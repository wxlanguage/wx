//! A function's expressions, stored as an arena: every node is addressed by an
//! [`ExprId`] into its function's [`Body`]. Design: `notes/mir-arena.md`.
//!
//! The arena is split by access pattern, as TIR's `Body` is: `kinds` and
//! `types` are parallel, `lists` holds the runs of children a node has a
//! variable number of (statements, call arguments, aggregate values), and
//! `cases` holds `Switch` arms.
//!
//! Every node but the root is the child of exactly one node, and every node
//! is reachable from the root ([`verify`]). So a scan over the nodes in index
//! order visits exactly the tree; nothing promises children come before their
//! parent, since rewriting a node in place (inlining) breaks that.

use super::{
	FunctionId, GlobalId, Local, LocalIndex, MemoryId, ScalarRange, ValueType,
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
#[cfg_attr(debug_assertions, derive(Debug))]
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
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct CaseList {
	start: u32,
	len: u32,
}

/// One arm of a `Switch`: the arm taken when the selector equals `value`.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct Case {
	/// A canonical `i64`: the raw value for an integer, 0/1 for a `Bool`,
	/// the code point for a `Char`, an enum variant's discriminant.
	pub value: i64,
	pub body: ExprId,
}

/// An operator on one operand, of the node's type. `Eqz` is the exception:
/// it compares its operand with zero and gives a `Bool`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum UnaryOp {
	Neg,
	BitNot,
	Eqz,
	Sqrt,
	Abs,
	Floor,
	Ceil,
	Trunc,
	Nearest,
}

/// An operator on two operands of the node's type. Division, remainder and
/// right shift are unsigned for an unsigned type
/// ([`ValueType::is_unsigned`]).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum BinaryOp {
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	BitAnd,
	BitOr,
	BitXor,
	Shl,
	Shr,
	Min,
	Max,
	Copysign,
}

/// A comparison of two operands of one type, giving a `Bool`. Ordering is
/// unsigned for an unsigned operand type.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum CompareOp {
	Eq,
	Ne,
	Lt,
	Le,
	Gt,
	Ge,
}

#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
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
	/// A flat value pack: every value is one scalar, in declaration
	/// pre-order. Zero-sized initializer effects are sequenced outside it.
	Aggregate {
		values: ExprList,
	},
	/// A scalar or flat subpack of a local, selected by slot range.
	AggregateGet {
		local: LocalIndex,
		range: ScalarRange,
	},
	/// Replace a local's slots in `range` with `value`, evaluated once. An
	/// empty range still evaluates `value`.
	AggregateSet {
		local: LocalIndex,
		range: ScalarRange,
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
	/// A numeric conversion, chosen by the operand's type and the node's:
	/// extend, wrap, convert, truncate, promote or demote. An integer's
	/// signedness is the operand's for an extension or a conversion to a
	/// float, the node's for a truncation.
	Convert {
		value: ExprId,
	},
	/// The bits of an `f32`/`i32` or `f64`/`i64` read as the other.
	Reinterpret {
		value: ExprId,
	},
	/// `value`'s Wasm values read as the node's type (std's `transmute`):
	/// both flatten to the same scalars in the same order, so no instruction
	/// is emitted. A node of its own rather than a rewritten type, because a
	/// node's own type selects its instruction (`DivS` or `DivU`), while its
	/// consumers read the transmuted one.
	Transmute {
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

	/// `i32.const <data_section_end>`: the first byte past the static data.
	MemoryOffset {
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
	/// Load the node's type from `pointer + offset`.
	PointerLoad {
		pointer: ExprId,
		offset: u32,
		memory: MemoryId,
	},
	/// Store `value` to `pointer + offset`.
	PointerStore {
		pointer: ExprId,
		value: ExprId,
		offset: u32,
		memory: MemoryId,
	},
	/// The address of a static data entry (`MIR::static_entries`). The
	/// entries a function uses are read off these nodes.
	StaticPointer {
		data_index: u32,
	},
}

// A node is matched by value everywhere; keep it small.
const _: () = assert!(std::mem::size_of::<ExprKind>() <= 24);

/// An index a node holds, as [`ExprKind::ids_mut`] hands it out.
pub enum Id<'a> {
	Expr(&'a mut ExprId),
	List(&'a mut ExprList),
	Cases(&'a mut CaseList),
	Local(&'a mut LocalIndex),
	Label(&'a mut LabelId),
}

impl ExprKind {
	/// Every index this node holds, in evaluation order of its children.
	/// The one per-variant walk: every rewrite and check goes through it, so
	/// a new variant is one arm here. A list's or a case list's entries are
	/// in the body, not in the node; the caller reads them there.
	pub fn ids_mut(&mut self, mut f: impl FnMut(Id<'_>)) {
		match self {
			Self::Noop
			| Self::Unreachable
			| Self::Int { .. }
			| Self::Float { .. }
			| Self::Global { .. }
			| Self::MemoryOffset { .. }
			| Self::MemoryIndex { .. }
			| Self::MemorySize { .. }
			| Self::StaticPointer { .. } => {}
			Self::LocalGet { local } | Self::AggregateGet { local, .. } => {
				f(Id::Local(local))
			}
			Self::LocalSet { local, value }
			| Self::AggregateSet { local, value, .. } => {
				f(Id::Local(local));
				f(Id::Expr(value));
			}
			Self::Aggregate { values: list }
			| Self::Sequence { statements: list }
			| Self::Call { args: list, .. } => f(Id::List(list)),
			Self::GlobalSet { value, .. }
			| Self::Unary { value, .. }
			| Self::Convert { value }
			| Self::Reinterpret { value }
			| Self::Transmute { value }
			| Self::Drop { value }
			| Self::MemoryGrow { delta: value, .. } => f(Id::Expr(value)),
			Self::Binary { lhs, rhs, .. } | Self::Compare { lhs, rhs, .. } => {
				f(Id::Expr(lhs));
				f(Id::Expr(rhs));
			}
			Self::Block { label, statements } => {
				f(Id::Label(label));
				f(Id::List(statements));
			}
			Self::Loop { label, body } => {
				f(Id::Label(label));
				f(Id::Expr(body));
			}
			Self::Break { label, value } => {
				if let Some(value) = value {
					f(Id::Expr(value));
				}
				f(Id::Label(label));
			}
			Self::Continue { label } => f(Id::Label(label)),
			Self::Return { value } => {
				if let Some(value) = value {
					f(Id::Expr(value));
				}
			}
			Self::IfElse {
				condition,
				then,
				otherwise,
			} => {
				f(Id::Expr(condition));
				f(Id::Expr(then));
				if let Some(otherwise) = otherwise {
					f(Id::Expr(otherwise));
				}
			}
			Self::Switch {
				selector,
				cases,
				default,
			} => {
				f(Id::Expr(selector));
				f(Id::Cases(cases));
				if let Some(default) = default {
					f(Id::Expr(default));
				}
			}
			Self::MemoryFill {
				dst, value, len, ..
			} => {
				f(Id::Expr(dst));
				f(Id::Expr(value));
				f(Id::Expr(len));
			}
			Self::MemoryCopy { dst, src, len, .. } => {
				f(Id::Expr(dst));
				f(Id::Expr(src));
				f(Id::Expr(len));
			}
			Self::PointerLoad { pointer, .. } => f(Id::Expr(pointer)),
			Self::PointerStore { pointer, value, .. } => {
				f(Id::Expr(pointer));
				f(Id::Expr(value));
			}
		}
	}
}

impl ExprKind {
	/// About how many bytes the node's own instructions encode to, not
	/// counting its children: the inliner's measure of a function
	/// (`notes/mir-inlining.md`). A node that emits nothing (`Sequence`,
	/// `Transmute`, an `Aggregate`, whose values are its children) costs 0.
	/// An estimate: an opcode is a byte, an index or a small constant one
	/// more, a `memarg` two.
	pub fn cost(&self) -> u32 {
		match self {
			Self::Noop
			| Self::Sequence { .. }
			| Self::Transmute { .. }
			| Self::Aggregate { .. } => 0,
			Self::Unreachable
			| Self::Unary { .. }
			| Self::Binary { .. }
			| Self::Compare { .. }
			| Self::Convert { .. }
			| Self::Reinterpret { .. }
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
			| Self::MemoryOffset { .. }
			| Self::MemoryIndex { .. }
			| Self::MemorySize { .. }
			| Self::MemoryGrow { .. }
			| Self::StaticPointer { .. } => 2,
			// An `f32` or an `f64`: the node does not say which.
			Self::Float { .. } => 5,
			// One `local.get` or `local.set` per slot.
			Self::AggregateGet { range, .. }
			| Self::AggregateSet { range, .. } => 2 * range.len,
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
		self.lists
			.extend(other.lists.iter().map(|&id| shift_expr(id, exprs)));
		self.cases.extend(other.cases.iter().map(|case| Case {
			value: case.value,
			body: shift_expr(case.body, exprs),
		}));
		self.types.extend_from_slice(&other.types);
		self.kinds.extend(other.kinds.iter().map(|&kind| {
			let mut kind = kind;
			kind.ids_mut(|id| match id {
				Id::Expr(expr) => *expr = shift_expr(*expr, exprs),
				Id::List(list) => {
					if list.len != 0 {
						list.start += lists;
					}
				}
				Id::Cases(list) => {
					if list.len != 0 {
						list.start += cases;
					}
				}
				Id::Local(local) => {
					*local = LocalIndex::new(u32::from(*local) + locals)
				}
				Id::Label(label) => {
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
}

/// Check `body`'s invariants from `root`: every id in range, every node in the
/// tree exactly once, every label owned by one `Block` or `Loop`, and every
/// `Break` and `Continue` inside the node owning its label (a `Continue`'s a
/// `Loop`).
pub fn verify(
	body: &Body,
	root: ExprId,
	locals: &[Local],
	label_count: u32,
) -> Result<(), VerifyError> {
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
		kind.ids_mut(|id| match id {
			Id::Expr(child) => children.push(*child),
			Id::List(list) => {
				if (list.start + list.len) as usize > body.lists.len() {
					in_range = false;
				} else {
					children.extend_from_slice(body.list(*list));
				}
			}
			Id::Cases(cases) => {
				if (cases.start + cases.len) as usize > body.cases.len() {
					in_range = false;
				} else {
					children.extend(body.cases(*cases).iter().map(|c| c.body));
				}
			}
			Id::Local(local) => {
				if usize::from(*local) >= locals.len() {
					in_range = false;
				}
			}
			Id::Label(label) => {
				if u32::from(*label) >= label_count {
					in_range = false;
				}
			}
		});
		if !in_range {
			return Err(VerifyError::OutOfRange { expr });
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
