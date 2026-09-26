//! Sea-of-nodes SSA IR for per-function optimization.
//!
//! Pipeline position: `mir::Function` → [`builder`] → [`Function`] →
//! [`scheduler`] → codegen
//!
//! # Structure
//! - [`DataNode`] — a pure value computation (constants, arithmetic, phis,
//!   aggregates). Nodes with identical [`DataNodeKind`] are deduplicated (CSE)
//!   via `Builder::node`.
//! - [`ControlNode`] — a side-effecting operation or control-flow construct.
//!   Placed sequentially inside [`Block`]s.
//! - [`Block`] — a linear sequence of `ControlNode`s, one per MIR scope.
//! - [`Function`] — the complete graph for one MIR function.

use std::collections::HashMap;

pub mod builder;
mod liveness;
#[cfg(debug_assertions)]
mod local_dominance;
pub mod scheduler;

#[cfg(test)]
mod tests;

use crate::index::index_newtype;
pub use crate::wasm::ScalarType;
use crate::{ast, mir};

pub type DataNodeIndex = u32;
pub type BlockIndex = u32;

/// Sign only matters for narrow loads: `i32.load8_s` vs `i32.load8_u`.
/// Full-width loads and stores are always unsigned.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum MemAccess {
	I8S,
	I8U,
	I16S,
	I16U,
	I32,
	I64,
	F32,
	F64,
}

impl MemAccess {
	pub fn from_mir(ty: mir::ValueType) -> Self {
		match ty {
			mir::ValueType::I8 => Self::I8S,
			mir::ValueType::U8 => Self::I8U,
			mir::ValueType::I16 => Self::I16S,
			mir::ValueType::U16 => Self::I16U,
			mir::ValueType::I64 | mir::ValueType::U64 => Self::I64,
			mir::ValueType::F32 => Self::F32,
			mir::ValueType::F64 => Self::F64,
			mir::ValueType::Pointer { kind, .. } => match kind {
				mir::MemoryKind::Memory32 => Self::I32,
				mir::MemoryKind::Memory64 => Self::I64,
			},
			_ => Self::I32,
		}
	}

	pub fn scalar_type(self) -> ScalarType {
		match self {
			Self::I8S | Self::I8U | Self::I16S | Self::I16U | Self::I32 => {
				ScalarType::I32
			}
			Self::I64 => ScalarType::I64,
			Self::F32 => ScalarType::F32,
			Self::F64 => ScalarType::F64,
		}
	}

	/// Log2 of the natural alignment in bytes (WASM memarg encoding).
	pub fn align_log2(self) -> u32 {
		match self {
			Self::I8S | Self::I8U => 0,
			Self::I16S | Self::I16U => 1,
			Self::I32 | Self::F32 => 2,
			Self::I64 | Self::F64 => 3,
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NodeType {
	Scalar(ScalarType),
	Aggregate(mir::AggregateIndex),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackResult {
	Value(DataNodeIndex),
	Unit,
	Never,
}

impl StackResult {
	pub fn unwrap_value(self) -> DataNodeIndex {
		match self {
			StackResult::Value(idx) => idx,
			r => panic!("expected Value, got {:?}", r),
		}
	}
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum DataNodeKind {
	// ── Constants ──────────────────────────────────────────────────────────
	Int {
		value: i64,
		ty: ScalarType,
	},
	/// Float bits stored as u64 to allow hashing.
	Float {
		bits: u64,
		ty: ScalarType,
	},

	// ── Inputs ─────────────────────────────────────────────────────────────
	Param {
		index: u32,
		ty: ScalarType,
	},
	/// Read from a mutable module global. Excluded from CSE.
	GlobalGet {
		id: ast::DefId,
		ty: ScalarType,
	},
	/// Constant index into the WASM function table.
	FunctionRef {
		id: ast::DefId,
	},
	/// Pointer into the static data segment for a string or array constant.
	/// `ty` is the pointer width of the memory holding the static data.
	StaticDataRef {
		data_index: u32,
		ty: ScalarType,
	},
	/// Byte offset of the end of the data section (link-time constant).
	/// `ty` is the memory's pointer width.
	MemoryOffset {
		memory: ast::DefId,
		ty: ScalarType,
	},
	/// WASM linear-memory index as an integer constant, resolved at codegen.
	MemoryIndex {
		memory: ast::DefId,
	},
	/// Result of a `MemorySize` control node. Excluded from CSE; always
	/// spilled. `ty` is the memory's size type (I64 for Memory64).
	MemorySizeResult {
		memory: ast::DefId,
		ty: ScalarType,
	},

	// ── Arithmetic ─────────────────────────────────────────────────────────
	Add {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	Sub {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	Mul {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	DivS {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	DivU {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	RemS {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	RemU {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	Min {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	Max {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	Copysign {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},

	// ── Bitwise ────────────────────────────────────────────────────────────
	BitAnd {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	BitOr {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	BitXor {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	Shl {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	ShrS {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	ShrU {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},

	// ── Unary ──────────────────────────────────────────────────────────────
	Neg {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	Sqrt {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	Abs {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	Floor {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	Ceil {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	Trunc {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	Nearest {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	BitNot {
		operand: DataNodeIndex,
		ty: ScalarType,
	},
	/// `i32.eqz` — produces I32.
	Eqz {
		operand: DataNodeIndex,
	},
	/// `i64.extend_i32_s` — sign-extends I32 to I64.
	I64ExtendI32S {
		operand: DataNodeIndex,
	},
	/// `i64.extend_i32_u` — zero-extends I32 to I64.
	I64ExtendI32U {
		operand: DataNodeIndex,
	},
	/// `i32.wrap_i64` — truncates I64 to I32.
	I32WrapI64 {
		operand: DataNodeIndex,
	},
	F32ConvertI32 {
		operand: DataNodeIndex,
	},
	F32ConvertU32 {
		operand: DataNodeIndex,
	},
	F32ConvertI64 {
		operand: DataNodeIndex,
	},
	F32ConvertU64 {
		operand: DataNodeIndex,
	},
	F64ConvertI32 {
		operand: DataNodeIndex,
	},
	F64ConvertU32 {
		operand: DataNodeIndex,
	},
	F64ConvertI64 {
		operand: DataNodeIndex,
	},
	F64ConvertU64 {
		operand: DataNodeIndex,
	},
	I32TruncF32 {
		operand: DataNodeIndex,
	},
	U32TruncF32 {
		operand: DataNodeIndex,
	},
	I32TruncF64 {
		operand: DataNodeIndex,
	},
	U32TruncF64 {
		operand: DataNodeIndex,
	},
	I64TruncF32 {
		operand: DataNodeIndex,
	},
	U64TruncF32 {
		operand: DataNodeIndex,
	},
	I64TruncF64 {
		operand: DataNodeIndex,
	},
	U64TruncF64 {
		operand: DataNodeIndex,
	},
	F64PromoteF32 {
		operand: DataNodeIndex,
	},
	F32DemoteF64 {
		operand: DataNodeIndex,
	},
	I32ReinterpretF32 {
		operand: DataNodeIndex,
	},
	F32ReinterpretI32 {
		operand: DataNodeIndex,
	},
	I64ReinterpretF64 {
		operand: DataNodeIndex,
	},
	F64ReinterpretI64 {
		operand: DataNodeIndex,
	},

	// ── Comparisons (always produce I32 / WASM bool) ───────────────────────
	Eq {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	NotEq {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	LtS {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	LtU {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	LtEqS {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	LtEqU {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	GtS {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	GtU {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	GtEqS {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},
	GtEqU {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},

	// ── Aggregates (structs as SSA values) ─────────────────────────────────
	Aggregate {
		fields: Box<[DataNodeIndex]>,
		aggregate_index: mir::AggregateIndex,
	},
	/// Projects a single WASM value out of an aggregate.
	///
	/// Indexed by [`mir::ScalarIndex`], *not* by physical field: a nested
	/// field spans several scalars and a zero-sized field spans none, so a
	/// field index would not name a value at all. This is why `ty` can be a
	/// `ScalarType` — a scalar index always names exactly one WASM value.
	/// To project a whole nested field, build one of these per scalar in the
	/// field's range and rewrap them (see `Builder::get_aggregate_field`).
	///
	/// Folds immediately when `aggregate` is a known `Aggregate` node.
	AggregateGet {
		aggregate: DataNodeIndex,
		scalar: mir::ScalarIndex,
		ty: ScalarType,
	},

	// ── Control-flow joins ─────────────────────────────────────────────────
	/// Merge two scalar values at a branch join point.
	/// Aggregate phis are decomposed field-by-field by the builder.
	Phi {
		left: DataNodeIndex,
		right: DataNodeIndex,
		ty: ScalarType,
	},

	/// A scalar value that flows around a loop. `after` starts as `before` and
	/// is patched once the loop body is built (see
	/// `Function::patch_loop_param`).
	LoopParam {
		block_index: BlockIndex,
		before: DataNodeIndex,
		after: DataNodeIndex,
		ty: ScalarType,
	},

	/// A stable placeholder identity for a plain `{}` block's carried
	/// binding — the block-join analogue of `LoopParam`, but with no
	/// before/after split: a block has no back-edge, so there is no
	/// "current iteration's value" to represent, only a fixed target every
	/// exit (`break`, or the fallthrough) commits into. Never fed into the
	/// block's own live bindings during construction (unlike `LoopParam` —
	/// see `Builder::create_join_params`'s doc comment) — referenced only
	/// via `ControlNode::BlockJoin::outputs` and commit-pair lists.
	JoinParam {
		block_index: BlockIndex,
		ty: ScalarType,
	},

	// ── Call / memory results (excluded from CSE: side effects) ────────────
	CallResult {
		callee: DataNodeIndex,
		args: Box<[DataNodeIndex]>,
		ty: ScalarType,
	},
	/// Unlike `Aggregate`, has no concrete field sub-nodes — values come from
	/// the WASM multi-return stack. `AggregateGet` of this node does not fold.
	AggregateCallResult {
		aggregate_index: mir::AggregateIndex,
	},
	MemoryGrowResult {
		memory: ast::DefId,
		delta: DataNodeIndex,
		ty: ScalarType,
	},
	/// Value produced by a `ControlNode::PointerLoad`. Always spilled.
	PointerLoadResult {
		address: DataNodeIndex,
		access: MemAccess,
	},
}

impl DataNodeKind {
	pub fn node_type(&self) -> NodeType {
		match self {
			DataNodeKind::Int { ty, .. }
			| DataNodeKind::Param { ty, .. }
			| DataNodeKind::Add { ty, .. }
			| DataNodeKind::Sub { ty, .. }
			| DataNodeKind::Mul { ty, .. }
			| DataNodeKind::DivS { ty, .. }
			| DataNodeKind::DivU { ty, .. }
			| DataNodeKind::RemS { ty, .. }
			| DataNodeKind::RemU { ty, .. }
			| DataNodeKind::Min { ty, .. }
			| DataNodeKind::Max { ty, .. }
			| DataNodeKind::Copysign { ty, .. }
			| DataNodeKind::BitAnd { ty, .. }
			| DataNodeKind::BitOr { ty, .. }
			| DataNodeKind::BitXor { ty, .. }
			| DataNodeKind::Shl { ty, .. }
			| DataNodeKind::ShrS { ty, .. }
			| DataNodeKind::ShrU { ty, .. }
			| DataNodeKind::Neg { ty, .. }
			| DataNodeKind::Sqrt { ty, .. }
			| DataNodeKind::Abs { ty, .. }
			| DataNodeKind::Floor { ty, .. }
			| DataNodeKind::Ceil { ty, .. }
			| DataNodeKind::Trunc { ty, .. }
			| DataNodeKind::Nearest { ty, .. }
			| DataNodeKind::BitNot { ty, .. }
			| DataNodeKind::AggregateGet { ty, .. }
			| DataNodeKind::Phi { ty, .. }
			| DataNodeKind::LoopParam { ty, .. }
			| DataNodeKind::JoinParam { ty, .. }
			| DataNodeKind::CallResult { ty, .. }
			| DataNodeKind::Float { ty, .. } => NodeType::Scalar(*ty),

			DataNodeKind::Eqz { .. }
			| DataNodeKind::Eq { .. }
			| DataNodeKind::NotEq { .. }
			| DataNodeKind::LtS { .. }
			| DataNodeKind::LtU { .. }
			| DataNodeKind::LtEqS { .. }
			| DataNodeKind::LtEqU { .. }
			| DataNodeKind::GtS { .. }
			| DataNodeKind::GtU { .. }
			| DataNodeKind::GtEqS { .. }
			| DataNodeKind::GtEqU { .. }
			| DataNodeKind::FunctionRef { .. }
			| DataNodeKind::MemoryIndex { .. }
			| DataNodeKind::I32WrapI64 { .. }
			| DataNodeKind::I32TruncF32 { .. }
			| DataNodeKind::U32TruncF32 { .. }
			| DataNodeKind::I32TruncF64 { .. }
			| DataNodeKind::U32TruncF64 { .. }
			| DataNodeKind::I32ReinterpretF32 { .. } => {
				NodeType::Scalar(ScalarType::I32)
			}
			DataNodeKind::I64ExtendI32S { .. }
			| DataNodeKind::I64ExtendI32U { .. }
			| DataNodeKind::I64TruncF32 { .. }
			| DataNodeKind::U64TruncF32 { .. }
			| DataNodeKind::I64TruncF64 { .. }
			| DataNodeKind::U64TruncF64 { .. }
			| DataNodeKind::I64ReinterpretF64 { .. } => {
				NodeType::Scalar(ScalarType::I64)
			}
			DataNodeKind::F32ConvertI32 { .. }
			| DataNodeKind::F32ConvertU32 { .. }
			| DataNodeKind::F32ConvertI64 { .. }
			| DataNodeKind::F32ConvertU64 { .. }
			| DataNodeKind::F32DemoteF64 { .. }
			| DataNodeKind::F32ReinterpretI32 { .. } => {
				NodeType::Scalar(ScalarType::F32)
			}
			DataNodeKind::F64ConvertI32 { .. }
			| DataNodeKind::F64ConvertU32 { .. }
			| DataNodeKind::F64ConvertI64 { .. }
			| DataNodeKind::F64ConvertU64 { .. }
			| DataNodeKind::F64PromoteF32 { .. }
			| DataNodeKind::F64ReinterpretI64 { .. } => {
				NodeType::Scalar(ScalarType::F64)
			}
			DataNodeKind::GlobalGet { ty, .. }
			| DataNodeKind::StaticDataRef { ty, .. }
			| DataNodeKind::MemoryOffset { ty, .. }
			| DataNodeKind::MemorySizeResult { ty, .. }
			| DataNodeKind::MemoryGrowResult { ty, .. } => NodeType::Scalar(*ty),

			DataNodeKind::PointerLoadResult { access, .. } => {
				NodeType::Scalar(access.scalar_type())
			}

			DataNodeKind::Aggregate {
				aggregate_index, ..
			}
			| DataNodeKind::AggregateCallResult { aggregate_index } => {
				NodeType::Aggregate(*aggregate_index)
			}
		}
	}

	pub fn unwrap_scalar(&self) -> ScalarType {
		match self.node_type() {
			NodeType::Scalar(s) => s,
			NodeType::Aggregate(_) => {
				panic!("expected scalar node type, got aggregate")
			}
		}
	}

	/// Returns true when two nodes with the same inputs are guaranteed to
	/// produce the same value and can be deduplicated. Impure nodes (reads of
	/// mutable state, call results, memory ops) and LoopParams (mutated after
	/// creation) are not pure and each represent a distinct value. Phi is not
	/// pure either: its value is control-dependent on the specific join point
	/// that produced it (which predecessor branch is live), so two Phis with
	/// identical `(left, right, ty)` from *unrelated* branches are not
	/// interchangeable even though they look structurally equal — CSE-ing
	/// them would silently make one join's value leak into the other's. A
	/// `Phi{left, right}` with `left == right` is still simplified away, but
	/// that happens in `Builder::node` before nodes ever reach `intern_node`,
	/// so excluding `Phi` here only removes the unsound cross-join dedup.
	fn is_pure(&self) -> bool {
		match self {
			DataNodeKind::GlobalGet { .. }
			| DataNodeKind::MemorySizeResult { .. }
			| DataNodeKind::CallResult { .. }
			| DataNodeKind::AggregateCallResult { .. }
			| DataNodeKind::MemoryGrowResult { .. }
			| DataNodeKind::PointerLoadResult { .. }
			| DataNodeKind::LoopParam { .. }
			| DataNodeKind::JoinParam { .. }
			| DataNodeKind::Phi { .. } => false,
			_ => true,
		}
	}
}

pub struct DataNode {
	pub kind: DataNodeKind,
	pub uses: Vec<DataNodeIndex>,
}

pub enum ControlNode {
	Return {
		value: StackResult,
	},
	GlobalSet {
		id: ast::DefId,
		value: DataNodeIndex,
	},
	Call {
		callee: DataNodeIndex,
		args: Box<[DataNodeIndex]>,
		result: StackResult,
		/// MIR signature index for this call; used by the scheduler to emit
		/// `CallIndirectSym` when the callee is not a statically known
		/// `FunctionRef`.
		callee_sig: mir::SignatureIndex,
	},
	IfElse {
		condition: DataNodeIndex,
		then_block: BlockIndex,
		else_block: Option<BlockIndex>,
		/// Phi nodes produced at the join point (one per differing binding).
		/// An aggregate binding contributes one phi per differing *scalar*
		/// (`mir::ScalarTable`), not per field — a nested field spans several
		/// scalars and a zero-sized field spans none.
		outputs: Box<[DataNodeIndex]>,
		result: StackResult,
	},
	/// A `match`, kept as a genuine N-way branch rather than desugared to
	/// nested `IfElse` — the scheduler picks a WASM `br_table` (dense case
	/// values) or a `br_if` chain (sparse) based on the case set.
	Switch {
		selector: DataNodeIndex,
		cases: Box<[SwitchCase]>,
		/// The wildcard arm, if the source had one (absent only when TIR
		/// proved exhaustiveness by covering every enum variant).
		default: Option<SwitchCase>,
		/// Merged (Phi) nodes, one per divergent binding across arms, plus —
		/// if the arms' own result values differ — one more for the overall
		/// match result. Same role as `IfElse.outputs`, but folded N-way.
		outputs: Box<[DataNodeIndex]>,
		result: StackResult,
	},
	Loop {
		body: BlockIndex,
		/// LoopParam nodes for bindings that change across the loop.
		/// An aggregate binding contributes one loop-param per *scalar*
		/// (`mir::ScalarTable`), not per field — a nested field spans several
		/// scalars and a zero-sized field spans none. Reading this as
		/// "per field" is what made a nested aggregate crossing a loop
		/// unrepresentable.
		outputs: Box<[DataNodeIndex]>,
		result: StackResult,
	},
	/// A plain `{}` block that's an actual `break` target — the block-join
	/// analogue of `Loop`, minus everything that exists only to solve the
	/// loop back-edge problem. See `DataNodeKind::JoinParam`'s doc comment.
	BlockJoin {
		body: BlockIndex,
		/// Same role as `Loop::outputs`, but these are `JoinParam` nodes —
		/// no back-edge, so no before/after two-phase commit.
		outputs: Box<[DataNodeIndex]>,
		/// The fallthrough path's own commit pairs — same shape/role as
		/// `Break::carried_binding_updates`, but there is no `ControlNode`
		/// to attach it to (falling off the end of a block isn't itself a
		/// control node), so it lives here instead.
		fallthrough_updates: Box<[(DataNodeIndex, DataNodeIndex)]>,
		/// The fallthrough path's own *raw* tail value — distinct from
		/// `result` (the final merged value across every exit). When this
		/// block has more than one value-contributing exit (some `break
		/// <value>` plus the fallthrough), each exit's own raw value must be
		/// individually committed into the shared `break_result_outputs`
		/// phi locals at its own point — a `Break` already carries its own
		/// `value` for exactly this; falling off the end has no
		/// `ControlNode` of its own to carry it, so it lives here instead,
		/// mirroring `fallthrough_updates` just above.
		fallthrough_value: StackResult,
		result: StackResult,
	},
	Break {
		target: BlockIndex,
		value: StackResult,
		/// `(carried_node, current_value_node)` pairs, decomposed to
		/// scalars — the target's own carried bindings (a loop's
		/// `JoinData::entry_placeholders`) as of this exact break site.
		/// The target's normal "commit
		/// accumulated bindings, then branch back/fall through" tail code
		/// only runs on the ordinary path (a loop's back-edge, or a block's
		/// own fallthrough); an early exit bypasses it entirely, so every
		/// `break`/`continue` site must independently commit whatever its
		/// own current values are — mirroring how `break_result_outputs`
		/// already does this for the trailing *value* specifically.
		carried_binding_updates: Box<[(DataNodeIndex, DataNodeIndex)]>,
	},
	Continue {
		target: BlockIndex,
		/// See `Break::carried_binding_updates`. Always targets a loop — TIR
		/// guarantees a `continue` can never target a plain block (see
		/// `tir::builder::control::build_continue_expression`).
		carried_binding_updates: Box<[(DataNodeIndex, DataNodeIndex)]>,
	},
	Unreachable,
	MemorySize {
		memory: ast::DefId,
		result: DataNodeIndex,
	},
	MemoryGrow {
		memory: ast::DefId,
		delta: DataNodeIndex,
		result: DataNodeIndex,
	},
	MemoryFill {
		memory: ast::DefId,
		dst: DataNodeIndex,
		val: DataNodeIndex,
		len: DataNodeIndex,
	},
	MemoryCopy {
		dst_memory: ast::DefId,
		src_memory: ast::DefId,
		dst: DataNodeIndex,
		src: DataNodeIndex,
		len: DataNodeIndex,
	},
	PointerLoad {
		address: DataNodeIndex,
		/// Byte offset added to `address` at the WASM instruction level (memarg).
		offset: u32,
		result: DataNodeIndex,
		memory: ast::DefId,
		access: MemAccess,
	},
	PointerStore {
		address: DataNodeIndex,
		/// Byte offset added to `address` at the WASM instruction level (memarg).
		offset: u32,
		value: DataNodeIndex,
		memory: ast::DefId,
		access: MemAccess,
	},
}

index_newtype!(
	/// Index into `Function::joins`, not the block table.
	JoinIndex
);

/// A block's shape — mirrors the same `Block`/`Loop` distinction TIR and MIR
/// already carry per scope (`tir::BlockKind`, `mir::BlockScope::kind`), kept
/// as opt's own type rather than reused directly since opt's `kind` also
/// covers synthetic blocks with no MIR scope at all (see
/// `Builder::push_synthetic_block`). Every `Block` has one, independent of
/// whether it's an actual break target (`Block::join`) — an ordinary
/// if/else or switch-arm body is `Block`-shaped without ever being a join.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum BlockKind {
	Block,
	Loop,
}

pub struct Block {
	pub parent: Option<BlockIndex>,
	pub statements: Vec<ControlNode>,
	/// Exit value. Overwritten as the block is built; the final value is
	/// what callers (e.g. `IfElse`/`Switch` arm handling) read back. For
	/// loop blocks, overwritten with `body_fallthrough` after `build_loop`
	/// finishes building the body — the pre-overwrite value (accumulated
	/// from every `break <value>` inside) is saved into
	/// `ControlNode::Loop.result` before this happens.
	pub result: StackResult,
	pub kind: BlockKind,
	/// `Some` only for a block that's an actual break target — every loop
	/// body (see `build_loop`), or a plain `{}` block something breaks to
	/// (see `Builder::break_targets`) — indexing into `Function::joins`.
	/// Most blocks (ordinary if/else/switch arm bodies) are neither, hence
	/// `Option` rather than an always-present field. `kind == Loop` always
	/// implies `Some` (`build_loop` registers both together); `kind ==
	/// Block` may be either, depending on `Builder::break_targets`.
	pub join: Option<JoinIndex>,
}

impl Block {
	pub fn is_loop(&self) -> bool {
		matches!(self.kind, BlockKind::Loop)
	}

	pub fn is_block_join(&self) -> bool {
		self.join.is_some() && matches!(self.kind, BlockKind::Block)
	}
}

/// Per-join-target extra data for a block that's an actual `break` target —
/// shared storage shape for both a loop body and a plain `{}` block's
/// block-join, distinguished by `Block::kind`. Holds
/// exactly what both forms need identically; the one thing that isn't
/// identical (a loop's back-edge before/after split) lives on the
/// `LoopParam`/`JoinParam` `DataNodeKind` variants instead, not here — see
/// `DataNodeKind::JoinParam`'s doc comment.
pub struct JoinData {
	/// Phi nodes at the join point for the merged exit *value* — every
	/// `break <value>` targeting this block, plus (for a block-join only;
	/// a loop's own "fallthrough" is its back-edge, already covered by
	/// `entry_placeholders`) the block's own fallthrough tail value.
	/// Scheduler pre-allocates WASM locals for these; each exit stores into
	/// them before branching. Empty when every exit carries the same value.
	pub break_result_outputs: Vec<DataNodeIndex>,
	/// This target's own per-slot carried-binding placeholders — a loop's
	/// `LoopParam`s (`Builder::create_loop_params`) or a block-join's
	/// `JoinParam`s (`Builder::create_join_params`) — one entry per
	/// function-wide local, `Some` only where that local already had a
	/// value at entry (`None` means "not yet declared on this build path,"
	/// e.g. a temp only declared inside the body itself; see
	/// `Builder::read_binding`'s doc comment). Kept around so a nested
	/// `break`/`continue` — however deep inside the body — can look up
	/// which placeholder node corresponds to which binding slot; see
	/// `ControlNode::Break::carried_binding_updates`.
	pub entry_placeholders: Vec<Option<StackResult>>,
	/// Scalar-level placeholder nodes any exit (a `break`/`continue` inside
	/// the body, or — for a block-join — the fallthrough) has ever recorded
	/// a genuine commit for (see `Builder::carried_binding_updates`),
	/// independent of what the fallthrough/back-edge path alone would
	/// conclude. Unioned into `patch_loop_binding`'s/
	/// `finalize_block_join_binding`'s divergence decision so a binding
	/// some exit mutates — but the ordinary path never touches, or resets
	/// back to the same value — still gets a real output local. A plain
	/// `Vec` (not a `HashSet`): carried bindings are typically few enough
	/// that a linear `.contains()` check is cheaper than hashing.
	pub divergent_params: Vec<DataNodeIndex>,
}

/// One `match` arm, lowered. `own_values` is required because `DataNodeKind::Phi`
/// is strictly binary (`left`/`right`, positionally keyed by convention) — an
/// N-ary join can't recover "this specific arm's contribution" the way
/// `IfElse`'s `emit_phi_stores_for_branch` reads `left`/`right` structurally,
/// so each case carries its own per-slot values explicitly.
pub struct SwitchCase {
	/// `None` only for the default/wildcard arm.
	pub discriminant: Option<i64>,
	pub block: BlockIndex,
	/// This case's own value for each of `Switch.outputs`, same length/order
	/// as `outputs`. `StackResult::Never` means this arm's body diverges
	/// before reaching the join, so the scheduler emits no store for it.
	pub own_values: Box<[StackResult]>,
}

pub struct Function {
	pub id: ast::DefId,
	pub data_nodes: Vec<DataNode>,
	/// One slot per MIR scope (indexed by scope index). `None` until the scope
	/// is built.
	pub blocks: Vec<Option<Block>>,
	/// Per-join-target extra data, indexed by `Block::join`'s `JoinIndex` —
	/// shared by both loop bodies and block-joins; see `JoinData`'s doc
	/// comment.
	pub joins: Vec<JoinData>,
	/// CSE map: `DataNodeKind` → existing `DataNodeIndex`. Impure nodes excluded.
	data_lookup: HashMap<DataNodeKind, DataNodeIndex>,
}

impl Function {
	pub fn new(id: ast::DefId, scope_count: usize) -> Self {
		Function {
			id,
			data_nodes: Vec::new(),
			blocks: (0..scope_count).map(|_| None).collect(),
			joins: Vec::new(),
			data_lookup: HashMap::new(),
		}
	}

	/// Registers a new join target's `JoinData` and returns its `JoinIndex`.
	pub fn push_join_data(&mut self, data: JoinData) -> JoinIndex {
		let idx = JoinIndex::new(self.joins.len() as u32);
		self.joins.push(data);
		idx
	}

	/// The `JoinData` for a loop or block-join target. Panics if `block_idx`
	/// is neither.
	pub fn join_data(&self, block_idx: BlockIndex) -> &JoinData {
		let idx = self.blocks[block_idx as usize]
			.as_ref()
			.unwrap()
			.join
			.expect("join_data called on a block with no join entry");
		&self.joins[usize::from(idx)]
	}

	/// Mutable counterpart of `join_data`.
	pub fn join_data_mut(&mut self, block_idx: BlockIndex) -> &mut JoinData {
		let idx = self.blocks[block_idx as usize]
			.as_ref()
			.unwrap()
			.join
			.expect("join_data_mut called on a block with no join entry");
		&mut self.joins[usize::from(idx)]
	}

	/// Get or create a data node via CSE only. Does not apply any algebraic
	/// simplification — call `Builder::node` for that.
	pub fn intern_node(&mut self, kind: DataNodeKind) -> DataNodeIndex {
		if kind.is_pure() {
			if let Some(&id) = self.data_lookup.get(&kind) {
				return id;
			}
		}

		let id = self.data_nodes.len() as DataNodeIndex;
		self.register_uses(&kind, id);

		if kind.is_pure() {
			self.data_lookup.insert(kind.clone(), id);
		}
		self.data_nodes.push(DataNode {
			kind,
			uses: Vec::new(),
		});
		id
	}

	/// Create a loop-param placeholder for `before` with `after = before`.
	/// Call `patch_loop_param` once the loop body has been built.
	pub fn push_loop_param(
		&mut self,
		block_index: BlockIndex,
		before: DataNodeIndex,
		ty: ScalarType,
	) -> DataNodeIndex {
		let id = self.data_nodes.len() as DataNodeIndex;
		self.data_nodes.push(DataNode {
			kind: DataNodeKind::LoopParam {
				block_index,
				before,
				after: before,
				ty,
			},
			uses: Vec::new(),
		});
		id
	}

	/// Create a join-param placeholder for a plain `{}` block's carried
	/// binding. Unlike `push_loop_param`, there is no `before`/`after` split
	/// and no later "patch" step — a `JoinParam` is either divergent (found
	/// to differ by some exit, pushed into `ControlNode::BlockJoin::outputs`)
	/// or not (never referenced again, left as a dead, zero-use node); it is
	/// never mutated in place. See `DataNodeKind::JoinParam`'s doc comment.
	pub fn push_join_param(
		&mut self,
		block_index: BlockIndex,
		ty: ScalarType,
	) -> DataNodeIndex {
		let id = self.data_nodes.len() as DataNodeIndex;
		self.data_nodes.push(DataNode {
			kind: DataNodeKind::JoinParam { block_index, ty },
			uses: Vec::new(),
		});
		id
	}

	/// Finalize a loop-param once the loop body is fully built.
	/// If `after == before` (the binding was never mutated), the node is left
	/// as-is and no uses are registered — the scheduler will see zero uses and
	/// skip it.
	pub fn patch_loop_param(
		&mut self,
		id: DataNodeIndex,
		after: DataNodeIndex,
	) {
		let (block_index, before, ty) = match self.data_nodes[id as usize].kind
		{
			DataNodeKind::LoopParam {
				block_index,
				before,
				ty,
				..
			} => (block_index, before, ty),
			_ => panic!("patch_loop_param called on non-LoopParam node"),
		};
		if before == after {
			return;
		}
		self.data_nodes[id as usize].kind = DataNodeKind::LoopParam {
			block_index,
			before,
			after,
			ty,
		};
		self.data_nodes[before as usize].uses.push(id);
		self.data_nodes[after as usize].uses.push(id);
	}

	fn register_uses(&mut self, kind: &DataNodeKind, user_id: DataNodeIndex) {
		match kind {
            DataNodeKind::Add { left, right, .. }
            | DataNodeKind::Sub { left, right, .. }
            | DataNodeKind::Mul { left, right, .. }
            | DataNodeKind::DivS { left, right, .. }
            | DataNodeKind::DivU { left, right, .. }
            | DataNodeKind::RemS { left, right, .. }
            | DataNodeKind::RemU { left, right, .. }
            | DataNodeKind::Min { left, right, .. }
            | DataNodeKind::Max { left, right, .. }
            | DataNodeKind::Copysign { left, right, .. }
            | DataNodeKind::BitAnd { left, right, .. }
            | DataNodeKind::BitOr  { left, right, .. }
            | DataNodeKind::BitXor { left, right, .. }
            | DataNodeKind::Shl    { left, right, .. }
            | DataNodeKind::ShrS   { left, right, .. }
            | DataNodeKind::ShrU   { left, right, .. }
            | DataNodeKind::Eq     { left, right, .. }
            | DataNodeKind::NotEq  { left, right, .. }
            | DataNodeKind::LtS    { left, right, .. }
            | DataNodeKind::LtU    { left, right, .. }
            | DataNodeKind::LtEqS  { left, right, .. }
            | DataNodeKind::LtEqU  { left, right, .. }
            | DataNodeKind::GtS    { left, right, .. }
            | DataNodeKind::GtU    { left, right, .. }
            | DataNodeKind::GtEqS  { left, right, .. }
            | DataNodeKind::GtEqU  { left, right, .. }
            | DataNodeKind::Phi    { left, right, .. } => {
                self.data_nodes[*left as usize].uses.push(user_id);
                self.data_nodes[*right as usize].uses.push(user_id);
            }

            DataNodeKind::Neg    { operand, .. }
            | DataNodeKind::Sqrt { operand, .. }
            | DataNodeKind::Abs { operand, .. }
            | DataNodeKind::Floor { operand, .. }
            | DataNodeKind::Ceil { operand, .. }
            | DataNodeKind::Trunc { operand, .. }
            | DataNodeKind::Nearest { operand, .. }
            | DataNodeKind::BitNot { operand, .. }
            | DataNodeKind::Eqz    { operand }
            | DataNodeKind::I64ExtendI32S { operand }
            | DataNodeKind::I64ExtendI32U { operand }
            | DataNodeKind::I32WrapI64 { operand }
            | DataNodeKind::F32ConvertI32 { operand }
            | DataNodeKind::F32ConvertU32 { operand }
            | DataNodeKind::F32ConvertI64 { operand }
            | DataNodeKind::F32ConvertU64 { operand }
            | DataNodeKind::F64ConvertI32 { operand }
            | DataNodeKind::F64ConvertU32 { operand }
            | DataNodeKind::F64ConvertI64 { operand }
            | DataNodeKind::F64ConvertU64 { operand }
            | DataNodeKind::I32TruncF32 { operand }
            | DataNodeKind::U32TruncF32 { operand }
            | DataNodeKind::I32TruncF64 { operand }
            | DataNodeKind::U32TruncF64 { operand }
            | DataNodeKind::I64TruncF32 { operand }
            | DataNodeKind::U64TruncF32 { operand }
            | DataNodeKind::I64TruncF64 { operand }
            | DataNodeKind::U64TruncF64 { operand }
            | DataNodeKind::F64PromoteF32 { operand }
            | DataNodeKind::F32DemoteF64 { operand }
            | DataNodeKind::I32ReinterpretF32 { operand }
            | DataNodeKind::F32ReinterpretI32 { operand }
            | DataNodeKind::I64ReinterpretF64 { operand }
            | DataNodeKind::F64ReinterpretI64 { operand }
            | DataNodeKind::AggregateGet { aggregate: operand, .. } => {
                self.data_nodes[*operand as usize].uses.push(user_id);
            }

            DataNodeKind::Aggregate { fields, .. } => {
                for &f in fields.iter() {
                    self.data_nodes[f as usize].uses.push(user_id);
                }
            }

            DataNodeKind::CallResult { callee, args, .. } => {
                self.data_nodes[*callee as usize].uses.push(user_id);
                for &a in args.iter() {
                    self.data_nodes[a as usize].uses.push(user_id);
                }
            }

            DataNodeKind::MemoryGrowResult { delta, .. } => {
                self.data_nodes[*delta as usize].uses.push(user_id);
            }

            DataNodeKind::PointerLoadResult { address, .. } => {
                self.data_nodes[*address as usize].uses.push(user_id);
            }

            // Leaf nodes: no inputs to register.
            DataNodeKind::Int { .. }
            | DataNodeKind::Float { .. }
            | DataNodeKind::Param { .. }
            | DataNodeKind::GlobalGet { .. }
            | DataNodeKind::FunctionRef { .. }
            | DataNodeKind::StaticDataRef { .. }
            | DataNodeKind::MemoryOffset { .. }
            | DataNodeKind::MemoryIndex { .. }
            | DataNodeKind::MemorySizeResult { .. }
            | DataNodeKind::AggregateCallResult { .. }
            // LoopParam uses are registered by patch_loop_param after both
            // `before` and `after` are known.
            | DataNodeKind::LoopParam { .. }
            // JoinParam has no before/after (see its own doc comment) and
            // no operand fields of its own — nothing to register, ever.
            | DataNodeKind::JoinParam { .. } => {}
        }
	}
}
