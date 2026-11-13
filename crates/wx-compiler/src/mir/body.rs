//! A function's expressions, stored as an arena: every node is addressed by an
//! [`ExprId`] into its function's [`Body`]. Design: `notes/mir-arena.md`.
//!
//! The arena is split by access pattern, as TIR's `Body` is: `kinds` and
//! `types` are parallel, `lists` holds the runs of children a node has a
//! variable number of (statements, call arguments, a `Values`' values),
//! `cases` holds `Switch` arms, and `targets` the locals a `SetLocals` fills.
//!
//! Every node but the root is the child of exactly one node, and every node
//! is reachable from the root ([`verify`]). So a scan over the nodes in index
//! order visits exactly the tree; nothing promises children come before their
//! parent, since rewriting a node in place (inlining) breaks that.

use super::{
	FunctionId, GlobalId, Local, LocalIndex, MemoryId, StaticEntryId, ValueType,
};
use crate::index::index_newtype;

index_newtype!(
	/// A node of a function's [`Body`].
	ExprId
);
index_newtype!(
	/// What a `Break` or `Continue` names: the label of a `Block` or a `Loop`
	/// node. A label carries no data of its own (its kind is its owner's, its
	/// result type the owner's type); a function has `label_count` of them.
	LabelId
);

/// A run of `Body::lists`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub struct ExprList {
	start: u32,
	len: u32,
}

impl ExprList {
	pub const EMPTY: Self = Self { start: 0, len: 0 };

	pub fn len(self) -> usize {
		self.len as usize
	}

	pub fn is_empty(self) -> bool {
		self.len == 0
	}
}

/// A run of `Body::cases`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub struct CaseList {
	start: u32,
	len: u32,
}

/// A run of `Body::targets`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub struct TargetList {
	start: u32,
	len: u32,
}

impl TargetList {
	pub fn len(self) -> usize {
		self.len as usize
	}

	pub fn is_empty(self) -> bool {
		self.len == 0
	}
}

/// One arm of a `Switch`: the arm taken when the selector equals `value`.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub struct Case {
	/// A canonical `i64`: the raw value for an integer, 0/1 for a `Bool`,
	/// the code point for a `Char`, an enum variant's discriminant.
	pub value: i64,
	pub body: ExprId,
}

// Every opcode is one Wasm instruction, its signedness and its operand
// class its own: lowering, which knows the source types, picks it, and
// nothing after lowering reads a type to choose an instruction
// (`notes/mir-pipeline.md`, "MIR's vocabulary").

/// Which operand types an opcode takes.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Operands {
	Integer,
	Float,
	Any,
}

impl Operands {
	pub fn admit(self, ty: ValueType) -> bool {
		match self {
			Self::Integer => ty.is_integer(),
			Self::Float => ty.is_float(),
			Self::Any => ty.is_scalar(),
		}
	}
}

/// An operator on one operand, of the node's type; `Eqz` compares an
/// integer with zero and gives an `I32`. Wasm has no integer negation or
/// bitwise not: lowering writes `0 - x` and `x ^ -1`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum UnaryOp {
	Eqz,
	Neg,
	Abs,
	Sqrt,
	Floor,
	Ceil,
	Trunc,
	Nearest,
}

impl UnaryOp {
	pub fn operands(self) -> Operands {
		match self {
			Self::Eqz => Operands::Integer,
			_ => Operands::Float,
		}
	}
}

/// An operator on two operands of the node's type.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum BinaryOp {
	Add,
	Sub,
	Mul,
	And,
	Or,
	Xor,
	Shl,
	ShrS,
	ShrU,
	DivS,
	DivU,
	RemS,
	RemU,
	Div,
	Min,
	Max,
	Copysign,
}

impl BinaryOp {
	pub fn operands(self) -> Operands {
		match self {
			Self::Add | Self::Sub | Self::Mul => Operands::Any,
			Self::And
			| Self::Or
			| Self::Xor
			| Self::Shl
			| Self::ShrS
			| Self::ShrU
			| Self::DivS
			| Self::DivU
			| Self::RemS
			| Self::RemU => Operands::Integer,
			Self::Div | Self::Min | Self::Max | Self::Copysign => {
				Operands::Float
			}
		}
	}

	/// Traps on some operands: a zero divisor, or `MIN / -1`.
	pub fn can_trap(self) -> bool {
		matches!(self, Self::DivS | Self::DivU | Self::RemS | Self::RemU)
	}
}

/// A comparison of two operands of one type, giving an `I32` of 0 or 1.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum CompareOp {
	Eq,
	Ne,
	LtS,
	LtU,
	LeS,
	LeU,
	GtS,
	GtU,
	GeS,
	GeU,
	Lt,
	Le,
	Gt,
	Ge,
}

impl CompareOp {
	pub fn operands(self) -> Operands {
		match self {
			Self::Eq | Self::Ne => Operands::Any,
			Self::LtS
			| Self::LtU
			| Self::LeS
			| Self::LeU
			| Self::GtS
			| Self::GtU
			| Self::GeS
			| Self::GeU => Operands::Integer,
			Self::Lt | Self::Le | Self::Gt | Self::Ge => Operands::Float,
		}
	}
}

/// A conversion from the operand's type to the node's.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum ConvertOp {
	/// `I32` to `I64`, sign- or zero-extended.
	ExtendS,
	ExtendU,
	/// `I64` to `I32`, its low bits.
	Wrap,
	/// A float to an integer, rounded toward zero; traps when it does not
	/// fit.
	TruncS,
	TruncU,
	/// An integer to a float, read signed or unsigned.
	ConvertS,
	ConvertU,
	/// `F32` to `F64`, and back.
	Promote,
	Demote,
	/// The bits of an `F32`/`I32` or `F64`/`I64` read as the other.
	Reinterpret,
}

impl ConvertOp {
	/// Whether it converts `from` to `to`.
	pub fn converts(self, from: ValueType, to: ValueType) -> bool {
		use ValueType::*;
		match self {
			Self::ExtendS | Self::ExtendU => (from, to) == (I32, I64),
			Self::Wrap => (from, to) == (I64, I32),
			Self::TruncS | Self::TruncU => from.is_float() && to.is_integer(),
			Self::ConvertS | Self::ConvertU => {
				from.is_integer() && to.is_float()
			}
			Self::Promote => (from, to) == (F32, F64),
			Self::Demote => (from, to) == (F64, F32),
			Self::Reinterpret => matches!(
				(from, to),
				(I32, F32) | (F32, I32) | (I64, F64) | (F64, I64)
			),
		}
	}

	/// Traps on some operands: a float that no integer of the type holds.
	pub fn can_trap(self) -> bool {
		matches!(self, Self::TruncS | Self::TruncU)
	}
}

/// How a load reads memory: its width, and for a narrow one how it is
/// extended to an `I32`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum LoadAccess {
	I8S,
	I8U,
	I16S,
	I16U,
	I32,
	I64,
	F32,
	F64,
}

impl LoadAccess {
	/// Its natural alignment, as a power of two: its width in bytes.
	pub fn align_log2(self) -> u32 {
		match self {
			Self::I8S | Self::I8U => 0,
			Self::I16S | Self::I16U => 1,
			Self::I32 | Self::F32 => 2,
			Self::I64 | Self::F64 => 3,
		}
	}

	/// The type of the value it loads.
	pub fn value_type(self) -> ValueType {
		match self {
			Self::I8S | Self::I8U | Self::I16S | Self::I16U | Self::I32 => {
				ValueType::I32
			}
			Self::I64 => ValueType::I64,
			Self::F32 => ValueType::F32,
			Self::F64 => ValueType::F64,
		}
	}
}

/// How many bytes a store writes: a narrow one writes an `I32`'s low bits.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum StoreAccess {
	I8,
	I16,
	I32,
	I64,
	F32,
	F64,
}

impl StoreAccess {
	/// Its natural alignment, as a power of two: its width in bytes.
	pub fn align_log2(self) -> u32 {
		match self {
			Self::I8 => 0,
			Self::I16 => 1,
			Self::I32 | Self::F32 => 2,
			Self::I64 | Self::F64 => 3,
		}
	}

	/// The type of the value it stores.
	pub fn value_type(self) -> ValueType {
		match self {
			Self::I8 | Self::I16 | Self::I32 => ValueType::I32,
			Self::I64 => ValueType::I64,
			Self::F32 => ValueType::F32,
			Self::F64 => ValueType::F64,
		}
	}
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum ExprKind {
	/// Unit, with no effect.
	Noop,
	Unreachable,
	Int {
		value: i64,
	},
	Float {
		value: f64,
	},

	LocalGet {
		local: LocalIndex,
	},
	LocalSet {
		local: LocalIndex,
		value: ExprId,
	},
	/// Several values as one: each pushed in order, every one a scalar.
	/// Zero-sized initializer effects are sequenced outside it.
	Values {
		values: ExprList,
	},
	/// Pop `value`'s results into `targets`, one per result, in order;
	/// `None` drops that result. How a multi-result value is taken apart:
	/// nothing else takes one result out of several.
	SetLocals {
		targets: TargetList,
		value: ExprId,
	},
	Global {
		id: GlobalId,
	},
	GlobalSet {
		id: GlobalId,
		value: ExprId,
	},

	Unary {
		op: UnaryOp,
		value: ExprId,
	},
	Binary {
		op: BinaryOp,
		lhs: ExprId,
		rhs: ExprId,
	},
	Compare {
		op: CompareOp,
		lhs: ExprId,
		rhs: ExprId,
	},
	/// `value` converted from its type to the node's.
	Convert {
		op: ConvertOp,
		value: ExprId,
	},

	/// Statements in order; the value is the last one's (Unit when empty).
	/// It has no label, so nothing breaks to it.
	Sequence {
		statements: ExprList,
	},
	/// A break target: a labelled block, or an inlined function's wrapper.
	/// Its value is a `Break`'s, or the last statement's when control falls
	/// off its end.
	Block {
		label: LabelId,
		statements: ExprList,
	},
	Loop {
		label: LabelId,
		body: ExprId,
	},
	Break {
		label: LabelId,
		value: Option<ExprId>,
	},
	/// Restart a loop; `label` is a `Loop`'s.
	Continue {
		label: LabelId,
	},
	Return {
		value: Option<ExprId>,
	},
	IfElse {
		condition: ExprId,
		then: ExprId,
		otherwise: Option<ExprId>,
	},
	/// A genuine N-way branch, kept whole so the backend can choose a
	/// `br_table` for dense cases and a `br_if` chain for sparse ones.
	/// `default` is `None` only where the checker proved the cases
	/// exhaustive.
	Switch {
		selector: ExprId,
		cases: CaseList,
		default: Option<ExprId>,
	},

	/// A direct call. The call graph is read off these nodes.
	Call {
		function: FunctionId,
		args: ExprList,
	},
	/// Evaluate `value` and discard it.
	Drop {
		value: ExprId,
	},

	/// `Memory::DATA_END`: the address right after the memory's static
	/// data, known once codegen has laid it out.
	DataEnd {
		memory: MemoryId,
	},
	/// `i32.const <wasm_memory_index>`, resolved at codegen.
	MemoryIndex {
		memory: MemoryId,
	},
	/// `memory.size`, in pages.
	MemorySize {
		memory: MemoryId,
	},
	/// `memory.grow` by `delta` pages; the old size, or -1.
	MemoryGrow {
		memory: MemoryId,
		delta: ExprId,
	},
	/// `memory.fill`: `len` bytes from `dst` set to `value`.
	MemoryFill {
		memory: MemoryId,
		dst: ExprId,
		value: ExprId,
		len: ExprId,
	},
	/// `memory.copy` between two, possibly different, memories.
	MemoryCopy {
		dst_memory: MemoryId,
		src_memory: MemoryId,
		dst: ExprId,
		src: ExprId,
		len: ExprId,
	},
	/// Load the node's type from `pointer + offset`, as `access` reads it.
	PointerLoad {
		pointer: ExprId,
		offset: u32,
		memory: MemoryId,
		access: LoadAccess,
	},
	/// Store `value` to `pointer + offset`, as `access` writes it.
	PointerStore {
		pointer: ExprId,
		value: ExprId,
		offset: u32,
		memory: MemoryId,
		access: StoreAccess,
	},
	/// The address `offset` bytes into a static data entry
	/// (`MIR::static_entries`). The entries a function uses are read off
	/// these nodes.
	StaticPointer {
		entry: StaticEntryId,
		offset: u32,
	},
}

// A node is matched by value everywhere; keep it small.
const _: () = assert!(std::mem::size_of::<ExprKind>() <= 24);

/// A body-local index a node holds, as [`ExprKind::body_ids_mut`] hands it out.
pub enum BodyId<'a> {
	Expr(&'a mut ExprId),
	List(&'a mut ExprList),
	Cases(&'a mut CaseList),
	/// A run of target locals; its entries are in the body, as a list's.
	Targets(&'a mut TargetList),
	Local(&'a mut LocalIndex),
	Label(&'a mut LabelId),
}

impl ExprKind {
	/// Module references stored directly in this node, for discovery and
	/// remapping. This does not visit children or indices local to the body.
	/// Read-only callers visit a copy; no reference list is allocated.
	pub fn items_mut(
		&mut self,
		mut f: impl FnMut(super::references::ItemRef<'_>),
	) {
		use super::references::ItemRef;
		match self {
			Self::Call { function, .. } => f(ItemRef::Function(function)),
			Self::Global { id } | Self::GlobalSet { id, .. } => {
				f(ItemRef::Global(id));
			}
			Self::DataEnd { memory }
			| Self::MemoryIndex { memory }
			| Self::MemorySize { memory }
			| Self::MemoryGrow { memory, .. }
			| Self::MemoryFill { memory, .. }
			| Self::PointerLoad { memory, .. }
			| Self::PointerStore { memory, .. } => f(ItemRef::Memory(memory)),
			Self::MemoryCopy {
				dst_memory,
				src_memory,
				..
			} => {
				f(ItemRef::Memory(dst_memory));
				f(ItemRef::Memory(src_memory));
			}
			Self::StaticPointer { entry, .. } => f(ItemRef::Data(entry)),
			Self::Noop
			| Self::Unreachable
			| Self::Int { .. }
			| Self::Float { .. }
			| Self::LocalGet { .. }
			| Self::LocalSet { .. }
			| Self::Values { .. }
			| Self::SetLocals { .. }
			| Self::Unary { .. }
			| Self::Binary { .. }
			| Self::Compare { .. }
			| Self::Convert { .. }
			| Self::Sequence { .. }
			| Self::Block { .. }
			| Self::Loop { .. }
			| Self::Break { .. }
			| Self::Continue { .. }
			| Self::Return { .. }
			| Self::IfElse { .. }
			| Self::Switch { .. }
			| Self::Drop { .. } => {}
		}
	}

	/// Every body-local index this node holds, in evaluation order of its
	/// children. Body-local rewrites and checks share this per-variant walk;
	/// module references use [`Self::items_mut`]. A list's or a case list's
	/// entries are in the body, not in the node; the caller reads them there.
	pub fn body_ids_mut(&mut self, mut f: impl FnMut(BodyId<'_>)) {
		match self {
			Self::Noop
			| Self::Unreachable
			| Self::Int { .. }
			| Self::Float { .. }
			| Self::Global { .. }
			| Self::DataEnd { .. }
			| Self::MemoryIndex { .. }
			| Self::MemorySize { .. }
			| Self::StaticPointer { .. } => {}
			Self::LocalGet { local } => f(BodyId::Local(local)),
			Self::LocalSet { local, value } => {
				f(BodyId::Local(local));
				f(BodyId::Expr(value));
			}
			Self::SetLocals { targets, value } => {
				f(BodyId::Targets(targets));
				f(BodyId::Expr(value));
			}
			Self::Values { values: list }
			| Self::Sequence { statements: list }
			| Self::Call { args: list, .. } => f(BodyId::List(list)),
			Self::GlobalSet { value, .. }
			| Self::Unary { value, .. }
			| Self::Convert { value, .. }
			| Self::Drop { value }
			| Self::MemoryGrow { delta: value, .. } => f(BodyId::Expr(value)),
			Self::Binary { lhs, rhs, .. } | Self::Compare { lhs, rhs, .. } => {
				f(BodyId::Expr(lhs));
				f(BodyId::Expr(rhs));
			}
			Self::Block { label, statements } => {
				f(BodyId::Label(label));
				f(BodyId::List(statements));
			}
			Self::Loop { label, body } => {
				f(BodyId::Label(label));
				f(BodyId::Expr(body));
			}
			Self::Break { label, value } => {
				if let Some(value) = value {
					f(BodyId::Expr(value));
				}
				f(BodyId::Label(label));
			}
			Self::Continue { label } => f(BodyId::Label(label)),
			Self::Return { value } => {
				if let Some(value) = value {
					f(BodyId::Expr(value));
				}
			}
			Self::IfElse {
				condition,
				then,
				otherwise,
			} => {
				f(BodyId::Expr(condition));
				f(BodyId::Expr(then));
				if let Some(otherwise) = otherwise {
					f(BodyId::Expr(otherwise));
				}
			}
			Self::Switch {
				selector,
				cases,
				default,
			} => {
				f(BodyId::Expr(selector));
				f(BodyId::Cases(cases));
				if let Some(default) = default {
					f(BodyId::Expr(default));
				}
			}
			Self::MemoryFill {
				dst, value, len, ..
			} => {
				f(BodyId::Expr(dst));
				f(BodyId::Expr(value));
				f(BodyId::Expr(len));
			}
			Self::MemoryCopy { dst, src, len, .. } => {
				f(BodyId::Expr(dst));
				f(BodyId::Expr(src));
				f(BodyId::Expr(len));
			}
			Self::PointerLoad { pointer, .. } => f(BodyId::Expr(pointer)),
			Self::PointerStore { pointer, value, .. } => {
				f(BodyId::Expr(pointer));
				f(BodyId::Expr(value));
			}
		}
	}
}

impl ExprKind {
	/// About how many bytes the node's own instructions encode to, not
	/// counting its children: the inliner's measure of a function
	/// (`notes/mir-inlining.md`). A node that emits nothing (`Sequence`, a
	/// `Values`, whose values are its children) costs 0.
	/// An estimate: an opcode is a byte, an index or a small constant one
	/// more, a `memarg` two.
	pub fn cost(&self) -> u32 {
		match self {
			Self::Noop | Self::Sequence { .. } | Self::Values { .. } => 0,
			Self::Unreachable
			| Self::Unary { .. }
			| Self::Binary { .. }
			| Self::Compare { .. }
			| Self::Convert { .. }
			| Self::Drop { .. }
			| Self::Return { .. } => 1,
			// An opcode and `end`; an `if` with an `else` one more.
			Self::Block { .. } | Self::Loop { .. } => 2,
			Self::IfElse { otherwise, .. } => {
				2 + u32::from(otherwise.is_some())
			}
			Self::Int { .. }
			| Self::LocalGet { .. }
			| Self::LocalSet { .. }
			| Self::Global { .. }
			| Self::GlobalSet { .. }
			| Self::Break { .. }
			| Self::Continue { .. }
			| Self::Call { .. }
			| Self::DataEnd { .. }
			| Self::MemoryIndex { .. }
			| Self::MemorySize { .. }
			| Self::MemoryGrow { .. }
			| Self::StaticPointer { .. } => 2,
			// An `f32` or an `f64`: the node does not say which.
			Self::Float { .. } => 5,
			// A `local.set` or a `drop` per result.
			Self::SetLocals { targets, .. } => 2 * targets.len,
			// A table of depths, one per case.
			Self::Switch { cases, .. } => 2 + cases.len,
			Self::MemoryFill { .. }
			| Self::MemoryCopy { .. }
			| Self::PointerLoad { .. }
			| Self::PointerStore { .. } => 3,
		}
	}
}

/// One function's nodes.
#[derive(Clone, Default)]
pub struct Body {
	kinds: Vec<ExprKind>,
	types: Vec<ValueType>,
	lists: Vec<ExprId>,
	cases: Vec<Case>,
	targets: Vec<Option<LocalIndex>>,
}

impl Body {
	pub fn kind(&self, expr: ExprId) -> ExprKind {
		self.kinds[usize::from(expr)]
	}

	pub fn ty(&self, expr: ExprId) -> ValueType {
		self.types[usize::from(expr)]
	}

	pub fn list(&self, list: ExprList) -> &[ExprId] {
		&self.lists[list.start as usize..(list.start + list.len) as usize]
	}

	pub fn cases(&self, cases: CaseList) -> &[Case] {
		&self.cases[cases.start as usize..(cases.start + cases.len) as usize]
	}

	pub fn targets(&self, targets: TargetList) -> &[Option<LocalIndex>] {
		&self.targets
			[targets.start as usize..(targets.start + targets.len) as usize]
	}

	/// The entries of a target run, to rename the locals in place.
	pub fn targets_mut(
		&mut self,
		targets: TargetList,
	) -> &mut [Option<LocalIndex>] {
		&mut self.targets
			[targets.start as usize..(targets.start + targets.len) as usize]
	}

	/// How many nodes there are; every `ExprId` is below it.
	pub fn len(&self) -> usize {
		self.kinds.len()
	}

	pub fn is_empty(&self) -> bool {
		self.kinds.is_empty()
	}

	/// Every node, in index order. Each is in the tree exactly once, so this
	/// is a walk of the tree in no particular order.
	pub fn kinds(&self) -> &[ExprKind] {
		&self.kinds
	}

	pub fn push(&mut self, kind: ExprKind, ty: ValueType) -> ExprId {
		let id = ExprId::new(u32::try_from(self.kinds.len()).unwrap());
		self.kinds.push(kind);
		self.types.push(ty);
		id
	}

	pub fn push_list(
		&mut self,
		items: impl IntoIterator<Item = ExprId>,
	) -> ExprList {
		let start = u32::try_from(self.lists.len()).unwrap();
		self.lists.extend(items);
		let len = u32::try_from(self.lists.len()).unwrap() - start;
		if len == 0 {
			return ExprList::EMPTY;
		}
		ExprList { start, len }
	}

	pub fn push_cases(
		&mut self,
		cases: impl IntoIterator<Item = Case>,
	) -> CaseList {
		let start = u32::try_from(self.cases.len()).unwrap();
		self.cases.extend(cases);
		let len = u32::try_from(self.cases.len()).unwrap() - start;
		CaseList { start, len }
	}

	pub fn push_targets(
		&mut self,
		targets: impl IntoIterator<Item = Option<LocalIndex>>,
	) -> TargetList {
		let start = u32::try_from(self.targets.len()).unwrap();
		self.targets.extend(targets);
		let len = u32::try_from(self.targets.len()).unwrap() - start;
		TargetList { start, len }
	}

	/// Every node, mutably, in index order. Rewriting a node's indices must
	/// keep the arena's invariants ([`verify`]).
	pub fn kinds_mut(&mut self) -> &mut [ExprKind] {
		&mut self.kinds
	}

	/// The sum of every node's [`ExprKind::cost`].
	pub fn cost(&self) -> u32 {
		self.kinds.iter().map(ExprKind::cost).sum()
	}

	/// Append `other`'s nodes, lists and cases after this body's own, with
	/// every index they hold shifted to stay `other`'s: node, list and case
	/// indices past this body's, locals by `locals` and labels by `labels`.
	/// `rewrite` then sees each appended node. Returns how far node ids
	/// moved: `other`'s node `id` is `shift_expr(id, offset)` here.
	///
	/// The appended nodes are a second tree, reached from nothing until the
	/// caller links its root in.
	pub fn append(
		&mut self,
		other: &Body,
		locals: u32,
		labels: u32,
		mut rewrite: impl FnMut(&mut ExprKind),
	) -> u32 {
		let exprs = u32::try_from(self.kinds.len()).unwrap();
		let lists = u32::try_from(self.lists.len()).unwrap();
		let cases = u32::try_from(self.cases.len()).unwrap();
		let targets = u32::try_from(self.targets.len()).unwrap();
		self.targets.extend(other.targets.iter().map(|target| {
			target.map(|local| LocalIndex::new(u32::from(local) + locals))
		}));
		self.lists
			.extend(other.lists.iter().map(|&id| shift_expr(id, exprs)));
		self.cases.extend(other.cases.iter().map(|case| Case {
			value: case.value,
			body: shift_expr(case.body, exprs),
		}));
		self.types.extend_from_slice(&other.types);
		self.kinds.extend(other.kinds.iter().map(|&kind| {
			let mut kind = kind;
			kind.body_ids_mut(|id| match id {
				BodyId::Expr(expr) => *expr = shift_expr(*expr, exprs),
				BodyId::List(list) => {
					if list.len != 0 {
						list.start += lists;
					}
				}
				BodyId::Cases(list) => {
					if list.len != 0 {
						list.start += cases;
					}
				}
				BodyId::Targets(list) => list.start += targets,
				BodyId::Local(local) => {
					*local = LocalIndex::new(u32::from(*local) + locals)
				}
				BodyId::Label(label) => {
					*label = LabelId::new(u32::from(*label) + labels)
				}
			});
			rewrite(&mut kind);
			kind
		}));
		exprs
	}

	/// Rewrite a node in place, keeping its type.
	pub fn set_kind(&mut self, expr: ExprId, kind: ExprKind) {
		self.kinds[usize::from(expr)] = kind;
	}

	pub fn set_ty(&mut self, expr: ExprId, ty: ValueType) {
		self.types[usize::from(expr)] = ty;
	}
}

/// `expr` moved `offset` nodes along, as [`Body::append`] moves them.
pub fn shift_expr(expr: ExprId, offset: u32) -> ExprId {
	ExprId::new(u32::from(expr) + offset)
}

/// Why a function's body breaks the arena's invariants.
#[derive(Debug)]
pub enum VerifyError {
	/// An id past the end of its table.
	OutOfRange { expr: ExprId },
	/// A node reached twice: it has two parents, or is its own ancestor.
	Shared { expr: ExprId },
	/// A node the root does not reach.
	Orphan { expr: ExprId },
	/// A label owned by two nodes.
	LabelOwnedTwice { label: LabelId },
	/// A `Break` or `Continue` outside the node owning its label, or a
	/// `Continue` of a `Block`'s label.
	BadTarget { expr: ExprId },
	/// A local that is not one scalar: every local holds one Wasm value.
	NonScalarLocal { local: LocalIndex },
	/// An operation whose operand or result type its opcode or access does
	/// not take (`DivS` of an `F32`, an `I8U` load of an `I64`).
	OpcodeType { expr: ExprId },
}

/// Check `body`'s invariants from `root`: every local one scalar, every id in
/// range, every node in the tree exactly once, every label owned by one
/// `Block` or `Loop`, every `Break` and `Continue` inside the node owning
/// its label (a `Continue`'s a `Loop`), and every operation's types ones its
/// opcode takes.
pub fn verify(
	body: &Body,
	root: ExprId,
	locals: &[Local],
	label_count: u32,
) -> Result<(), VerifyError> {
	if let Some(local) = locals.iter().position(|local| !local.ty.is_scalar()) {
		return Err(VerifyError::NonScalarLocal {
			local: LocalIndex::new(local as u32),
		});
	}
	#[derive(Clone, Copy, PartialEq)]
	enum Owner {
		None,
		Block,
		Loop,
	}
	enum Step {
		Enter(ExprId),
		Leave(LabelId),
	}
	let mut seen = vec![false; body.len()];
	let mut owners = vec![Owner::None; label_count as usize];
	let mut open = vec![false; label_count as usize];
	let mut stack = vec![Step::Enter(root)];
	while let Some(step) = stack.pop() {
		let expr = match step {
			Step::Enter(expr) => expr,
			Step::Leave(label) => {
				open[usize::from(label)] = false;
				continue;
			}
		};
		let Some(visited) = seen.get_mut(usize::from(expr)) else {
			return Err(VerifyError::OutOfRange { expr });
		};
		if *visited {
			return Err(VerifyError::Shared { expr });
		}
		*visited = true;
		let mut kind = body.kind(expr);
		let mut in_range = true;
		let mut children = Vec::new();
		kind.body_ids_mut(|id| match id {
			BodyId::Expr(child) => children.push(*child),
			BodyId::List(list) => {
				if (list.start + list.len) as usize > body.lists.len() {
					in_range = false;
				} else {
					children.extend_from_slice(body.list(*list));
				}
			}
			BodyId::Cases(cases) => {
				if (cases.start + cases.len) as usize > body.cases.len() {
					in_range = false;
				} else {
					children.extend(body.cases(*cases).iter().map(|c| c.body));
				}
			}
			BodyId::Targets(targets) => {
				if (targets.start + targets.len) as usize > body.targets.len()
					|| body
						.targets(*targets)
						.iter()
						.flatten()
						.any(|local| usize::from(*local) >= locals.len())
				{
					in_range = false;
				}
			}
			BodyId::Local(local) => {
				if usize::from(*local) >= locals.len() {
					in_range = false;
				}
			}
			BodyId::Label(label) => {
				if u32::from(*label) >= label_count {
					in_range = false;
				}
			}
		});
		if !in_range {
			return Err(VerifyError::OutOfRange { expr });
		}
		if !operation_types_fit(body, expr) {
			return Err(VerifyError::OpcodeType { expr });
		}
		match kind {
			ExprKind::Block { label, .. } | ExprKind::Loop { label, .. } => {
				let index = usize::from(label);
				if owners[index] != Owner::None {
					return Err(VerifyError::LabelOwnedTwice { label });
				}
				owners[index] = if matches!(kind, ExprKind::Loop { .. }) {
					Owner::Loop
				} else {
					Owner::Block
				};
				open[index] = true;
				stack.push(Step::Leave(label));
			}
			ExprKind::Break { label, .. } => {
				if !open[usize::from(label)] {
					return Err(VerifyError::BadTarget { expr });
				}
			}
			ExprKind::Continue { label } => {
				let index = usize::from(label);
				if !open[index] || owners[index] != Owner::Loop {
					return Err(VerifyError::BadTarget { expr });
				}
			}
			_ => {}
		}
		// Pushed reversed, so children are entered in evaluation order and a
		// `Break` inside a child is checked while its owner is still open.
		stack.extend(children.into_iter().rev().map(Step::Enter));
	}
	match seen.iter().position(|&visited| !visited) {
		Some(orphan) => Err(VerifyError::Orphan {
			expr: ExprId::new(orphan as u32),
		}),
		None => Ok(()),
	}
}

/// Whether `expr`'s opcode or access takes its operands' types and its own.
/// A diverging operand never gives the operation a value, so it fits.
fn operation_types_fit(body: &Body, expr: ExprId) -> bool {
	let ty = body.ty(expr);
	let operand = |value: ExprId| body.ty(value);
	match body.kind(expr) {
		ExprKind::Unary { op, value } => {
			let from = operand(value);
			from == ValueType::Never
				|| op.operands().admit(from)
					&& ty
						== if op == UnaryOp::Eqz {
							ValueType::I32
						} else {
							from
						}
		}
		ExprKind::Binary { op, lhs, rhs } => {
			let (lhs, rhs) = (operand(lhs), operand(rhs));
			lhs == ValueType::Never
				|| rhs == ValueType::Never
				|| op.operands().admit(ty) && lhs == ty && rhs == ty
		}
		ExprKind::Compare { op, lhs, rhs } => {
			let (lhs, rhs) = (operand(lhs), operand(rhs));
			lhs == ValueType::Never
				|| rhs == ValueType::Never
				|| op.operands().admit(lhs)
					&& rhs == lhs && ty == ValueType::I32
		}
		ExprKind::Convert { op, value } => {
			let from = operand(value);
			from == ValueType::Never || op.converts(from, ty)
		}
		ExprKind::PointerLoad {
			pointer, access, ..
		} => operand(pointer) == ValueType::Never || ty == access.value_type(),
		ExprKind::PointerStore { value, access, .. } => {
			let value = operand(value);
			value == ValueType::Never || value == access.value_type()
		}
		_ => true,
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mir::Mutability;

	fn locals(count: usize) -> Vec<Local> {
		(0..count)
			.map(|_| Local {
				ty: ValueType::I32,
				mutability: Mutability::Mutable,
			})
			.collect()
	}

	fn int(body: &mut Body, value: i64) -> ExprId {
		body.push(ExprKind::Int { value }, ValueType::I32)
	}

	#[test]
	fn a_tree_reached_once_from_its_root_verifies() {
		let mut body = Body::default();
		let one = int(&mut body, 1);
		let two = int(&mut body, 2);
		let sum = body.push(
			ExprKind::Binary {
				op: BinaryOp::Add,
				lhs: one,
				rhs: two,
			},
			ValueType::I32,
		);
		let set = body.push(
			ExprKind::LocalSet {
				local: LocalIndex::new(0),
				value: sum,
			},
			ValueType::Unit,
		);
		let get = body.push(
			ExprKind::LocalGet {
				local: LocalIndex::new(0),
			},
			ValueType::I32,
		);
		let statements = body.push_list([set, get]);
		let root = body.push(ExprKind::Sequence { statements }, ValueType::I32);
		verify(&body, root, &locals(1), 0).unwrap();
	}

	#[test]
	fn a_node_with_two_parents_is_shared() {
		let mut body = Body::default();
		let one = int(&mut body, 1);
		let root = body.push(
			ExprKind::Binary {
				op: BinaryOp::Add,
				lhs: one,
				rhs: one,
			},
			ValueType::I32,
		);
		assert!(matches!(
			verify(&body, root, &[], 0),
			Err(VerifyError::Shared { .. })
		));
	}

	#[test]
	fn an_opcode_given_a_type_it_does_not_take_is_rejected() {
		let mut body = Body::default();
		let one = body.push(ExprKind::Float { value: 1.0 }, ValueType::F32);
		let two = body.push(ExprKind::Float { value: 2.0 }, ValueType::F32);
		let root = body.push(
			ExprKind::Binary {
				op: BinaryOp::DivS,
				lhs: one,
				rhs: two,
			},
			ValueType::F32,
		);
		assert!(matches!(
			verify(&body, root, &[], 0),
			Err(VerifyError::OpcodeType { .. })
		));
	}

	#[test]
	fn a_node_the_root_does_not_reach_is_an_orphan() {
		let mut body = Body::default();
		int(&mut body, 1);
		let root = int(&mut body, 2);
		assert!(matches!(
			verify(&body, root, &[], 0),
			Err(VerifyError::Orphan { .. })
		));
	}

	#[test]
	fn a_break_outside_its_labels_owner_has_a_bad_target() {
		let mut body = Body::default();
		let label = LabelId::new(0);
		let inner = body.push_list([]);
		let block = body.push(
			ExprKind::Block {
				label,
				statements: inner,
			},
			ValueType::Unit,
		);
		let escape =
			body.push(ExprKind::Break { label, value: None }, ValueType::Never);
		let statements = body.push_list([block, escape]);
		let root =
			body.push(ExprKind::Sequence { statements }, ValueType::Never);
		assert!(matches!(
			verify(&body, root, &[], 1),
			Err(VerifyError::BadTarget { .. })
		));
	}

	#[test]
	fn a_continue_of_a_blocks_label_has_a_bad_target() {
		let mut body = Body::default();
		let label = LabelId::new(0);
		let restart = body.push(ExprKind::Continue { label }, ValueType::Never);
		let statements = body.push_list([restart]);
		let root =
			body.push(ExprKind::Block { label, statements }, ValueType::Never);
		assert!(matches!(
			verify(&body, root, &[], 1),
			Err(VerifyError::BadTarget { .. })
		));
	}

	#[test]
	fn a_label_owned_twice_is_reported() {
		let mut body = Body::default();
		let label = LabelId::new(0);
		let empty = body.push_list([]);
		let inner = body.push(
			ExprKind::Block {
				label,
				statements: empty,
			},
			ValueType::Unit,
		);
		let root =
			body.push(ExprKind::Loop { label, body: inner }, ValueType::Never);
		assert!(matches!(
			verify(&body, root, &[], 1),
			Err(VerifyError::LabelOwnedTwice { .. })
		));
	}

	#[test]
	fn a_local_past_the_function_s_locals_is_out_of_range() {
		let mut body = Body::default();
		let root = body.push(
			ExprKind::LocalGet {
				local: LocalIndex::new(3),
			},
			ValueType::I32,
		);
		assert!(matches!(
			verify(&body, root, &locals(1), 0),
			Err(VerifyError::OutOfRange { .. })
		));
	}
}
