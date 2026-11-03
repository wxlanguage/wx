/// the role of MIR is to desugar the syntax like x += 1 into x = x + 1 and
/// lower the concepts like enums into primitive constants, convert labels from
/// symbols in interner into numeric indices
use std::collections::HashSet;

use string_interner::symbol::SymbolU32;

use crate::index::index_newtype;

// Only the pieces MIR still owns are in the module graph. The pre-transition
// lowering pass (`legacy_lowering.rs`) and its helpers (`builder/`,
// `types.rs`, `mono.rs`, `inlining.rs`, `static_data.rs`, `tests.rs`) stay on
// disk as reference but are deliberately not compiled: they target the
// removed `tir::TIR` API.
#[allow(dead_code)]
pub(crate) mod layout;
#[allow(dead_code)]
mod signatures;

index_newtype!(
	/// Backend identity of one MIR function *instance*.
	///
	/// This is neither a source `FunctionIdx` nor a Wasm function index. A
	/// monomorphized generic gets its own `FunctionId`, and codegen assigns
	/// Wasm indices from scratch (imports first). Lowering owns the mapping
	/// from source identity to this ID.
	FunctionId
);
index_newtype!(
	/// Backend identity of one MIR global instance, independent of its source
	/// `GlobalIdx` and of its Wasm global index.
	GlobalId
);
index_newtype!(
	/// Backend identity of one linear memory. Pointers are typed by the memory
	/// they address, so this distinguishes a `u32` address in memory A from
	/// the same bits in memory B.
	MemoryId
);
index_newtype!(
	/// Flat, function-wide index into `Function::locals`, distinct from
	/// `tir::LocalIndex` (which is per-scope).
	LocalIndex
);
index_newtype!(
	/// Index into `Function::scopes`, distinct from `tir::ScopeIndex`.
	ScopeIndex
);
index_newtype!(
	/// Index into `MIR::signatures`.
	SignatureIndex
);
index_newtype!(
	/// Index into `MIR::aggregates`. Reach the aggregate itself with
	/// [`MIR::aggregate`] rather than indexing the table by hand.
	AggregateIndex
);

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub enum ExprKind {
	Noop,
	Bool {
		value: bool,
	},
	Function {
		id: FunctionId,
	},
	Int {
		value: i64,
	},
	Float {
		value: f64,
	},
	LocalGet {
		local_index: LocalIndex,
	},
	LocalSet {
		local_index: LocalIndex,
		value: Box<Expression>,
	},
	/// An aggregate literal.
	///
	/// `values` is in **declaration order** and has exactly
	/// `Aggregate::field_count()` entries — one per field, not one per Wasm
	/// scalar. A zero-sized field still has an entry here; its expression is
	/// `Unit` and it contributes no Wasm slot. The matching accessors
	/// ([`ExprKind::AggregateGet`]/[`ExprKind::AggregateSet`]) index the same
	/// declaration space.
	Aggregate {
		values: Box<[Expression]>,
	},
	AggregateGet {
		local_index: LocalIndex,
		/// Declaration field index — see [`FieldIndex`].
		value_index: FieldIndex,
	},
	AggregateSet {
		local_index: LocalIndex,
		/// Declaration field index — see [`FieldIndex`].
		value_index: FieldIndex,
		value: Box<Expression>,
	},
	Global {
		id: GlobalId,
	},
	GlobalSet {
		id: GlobalId,
		value: Box<Expression>,
	},
	Add {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Sub {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Mul {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Div {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Rem {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	And {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Or {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Return {
		value: Option<Box<Expression>>,
	},
	Drop {
		value: Box<Expression>,
	},
	Call {
		callee: Box<Expression>,
		arguments: Box<[Expression]>,
	},
	Eq {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Eqz {
		value: Box<Expression>,
	},
	NotEq {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Block {
		scope_index: ScopeIndex,
		expressions: Box<[Expression]>,
	},
	Break {
		scope_index: ScopeIndex,
		value: Option<Box<Expression>>,
	},
	Continue {
		scope_index: ScopeIndex,
	},
	Unreachable,
	IfElse {
		condition: Box<Expression>,
		then_block: Box<Expression>,
		else_block: Option<Box<Expression>>,
	},
	/// A `match`, kept as a genuine N-way construct rather than desugared to
	/// nested `IfElse` — Opt/codegen choose between a WASM `br_table` (dense
	/// case values) and a `br_if` chain (sparse) based on the case set, and
	/// both need the full case list rather than a binary tree of ifs.
	Switch {
		selector: Box<Expression>,
		/// `(case discriminant, case body)` pairs in source order. The
		/// discriminant is always a canonical `i64` by this stage: the raw
		/// value for ints, 0/1 for bool, the codepoint for char, or the
		/// enum variant's folded `const_value` (enum variants already fold
		/// to constants — see the `tir::ExprKind::EnumVariant` lowering
		/// below).
		cases: Box<[(i64, Expression)]>,
		/// The wildcard arm's body. `None` only when TIR proved
		/// exhaustiveness without an explicit `_` (every enum variant
		/// covered) — codegen synthesizes `unreachable` for that case.
		default: Option<Box<Expression>>,
	},
	BitAnd {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	BitOr {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	BitXor {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	BitNot {
		value: Box<Expression>,
	},
	LeftShift {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	RightShift {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Less {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	LessEq {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Greater {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	GreaterEq {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Loop {
		scope_index: ScopeIndex,
		block: Box<Expression>,
	},
	Neg {
		value: Box<Expression>,
	},
	Sqrt {
		value: Box<Expression>,
	},
	Abs {
		value: Box<Expression>,
	},
	Floor {
		value: Box<Expression>,
	},
	Ceil {
		value: Box<Expression>,
	},
	Trunc {
		value: Box<Expression>,
	},
	Nearest {
		value: Box<Expression>,
	},
	Min {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Max {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	Copysign {
		left: Box<Expression>,
		right: Box<Expression>,
	},
	I64ExtendI32S {
		value: Box<Expression>,
	},
	I64ExtendI32U {
		value: Box<Expression>,
	},
	I32WrapI64 {
		value: Box<Expression>,
	},
	F32ConvertI32 {
		value: Box<Expression>,
	},
	F32ConvertU32 {
		value: Box<Expression>,
	},
	F32ConvertI64 {
		value: Box<Expression>,
	},
	F32ConvertU64 {
		value: Box<Expression>,
	},
	F64ConvertI32 {
		value: Box<Expression>,
	},
	F64ConvertU32 {
		value: Box<Expression>,
	},
	F64ConvertI64 {
		value: Box<Expression>,
	},
	F64ConvertU64 {
		value: Box<Expression>,
	},
	I32TruncF32 {
		value: Box<Expression>,
	},
	U32TruncF32 {
		value: Box<Expression>,
	},
	I32TruncF64 {
		value: Box<Expression>,
	},
	U32TruncF64 {
		value: Box<Expression>,
	},
	I64TruncF32 {
		value: Box<Expression>,
	},
	U64TruncF32 {
		value: Box<Expression>,
	},
	I64TruncF64 {
		value: Box<Expression>,
	},
	U64TruncF64 {
		value: Box<Expression>,
	},
	F64PromoteF32 {
		value: Box<Expression>,
	},
	F32DemoteF64 {
		value: Box<Expression>,
	},
	I32ReinterpretF32 {
		value: Box<Expression>,
	},
	F32ReinterpretI32 {
		value: Box<Expression>,
	},
	I64ReinterpretF64 {
		value: Box<Expression>,
	},
	F64ReinterpretI64 {
		value: Box<Expression>,
	},
	/// `i32.const <data_section_end>` — byte offset of the first writable
	/// memory region.
	MemoryOffset {
		memory: MemoryId,
	},
	/// `i32.const <wasm_memory_index>` — the wasm linear-memory index of this
	/// memory, resolved at codegen time.
	MemoryIndex {
		memory: MemoryId,
	},
	/// `memory.size` — current size of a linear memory in pages.
	MemorySize {
		memory: MemoryId,
	},
	/// `memory.grow` — grow linear memory by N pages; pushes old size or -1.
	MemoryGrow {
		memory: MemoryId,
		delta: Box<Expression>,
	},
	/// `memory.fill` — fill a region of linear memory with a byte value.
	MemoryFill {
		memory: MemoryId,
		dst: Box<Expression>,
		val: Box<Expression>,
		len: Box<Expression>,
	},
	/// `memory.copy` — copy a region between (possibly different) linear memories.
	MemoryCopy {
		dst_memory: MemoryId,
		src_memory: MemoryId,
		dst: Box<Expression>,
		src: Box<Expression>,
		len: Box<Expression>,
	},
	/// Load a value from the address held in `pointer`.
	PointerLoad {
		pointer: Box<Expression>,
		/// Static byte offset added to the address (WASM memarg immediate).
		offset: u32,
		memory: MemoryId,
	},
	/// Store `value` to the address held in `pointer`.
	PointerStore {
		pointer: Box<Expression>,
		value: Box<Expression>,
		/// Static byte offset added to the address (WASM memarg immediate).
		offset: u32,
		memory: MemoryId,
	},
	/// Pointer to a static data entry (index into `MIR.static_data`).
	/// Resolves to an `i32.const <byte_offset>` at codegen time.
	StaticPointer {
		data_index: u32,
	},
}

// `Debug` is gated on `debug_assertions` rather than `test` so that panics in
// a debug build can name the offending type. It must *not* also appear in the
// `test` derive below: `cargo test` enables both cfgs, and two `derive(Debug)`
// would be conflicting impls.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum ValueType {
	I32,
	I64,
	F32,
	F64,
	U32,
	U64,
	U8,
	I8,
	U16,
	I16,
	Unit,
	Never,
	Bool,
	Pointer { memory: MemoryId, kind: MemoryKind },
	Aggregate { aggregate_index: AggregateIndex },
	Function { signature_index: SignatureIndex },
}

impl ValueType {
	/// Types whose division, remainder, right shift, and ordered comparisons
	/// must use the unsigned WASM instruction variants. Pointers are
	/// unsigned addresses.
	pub fn is_unsigned(self) -> bool {
		matches!(
			self,
			ValueType::U8
				| ValueType::U16
				| ValueType::U32
				| ValueType::U64
				| ValueType::Pointer { .. }
		)
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub struct Expression {
	pub kind: ExprKind,
	pub ty: ValueType,
}

index_newtype!(
	/// A field's position in its aggregate's **declaration** order.
	///
	/// This is the index a field access or a place projection carries: it is
	/// the index the source declaration gives, independent of the aggregate's
	/// memory layout. Byte offsets are a separate attribute ([`Field::offset`]);
	/// there is no "physical field order" in the MIR value model.
	FieldIndex
);

index_newtype!(
	/// Index into an aggregate's flattened scalar (Wasm-value) list, in
	/// **declaration pre-order**.
	///
	/// One scalar is one WebAssembly value: one signature slot, one local, one
	/// stack entry. Deliberately a different type from [`FieldIndex`], because
	/// one field contributes *many* scalars when it is itself an aggregate and
	/// *none* when it is zero-sized — the two index spaces coincide only for a
	/// flat, ZST-free aggregate, and confusing them silently emits wrong code.
	ScalarIndex
);

/// One field of an aggregate, in declaration order. Value type and byte offset
/// live in one struct because both are always reached by the same
/// [`FieldIndex`].
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Field {
	pub ty: ValueType,
	/// Byte offset from the aggregate's base, chosen by layout. This is the
	/// only place memory order appears; it never orders values.
	pub offset: u32,
}

/// One WebAssembly value inside an aggregate.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Scalar {
	/// Always convertible to a `wasm::ScalarType`, by construction.
	pub ty: ValueType,
	/// Byte offset from the *aggregate's* base, with every enclosing field's
	/// offset already folded in. Carrying it here is what lets an aggregate
	/// store or load walk the scalar list flat instead of recursing the field
	/// tree — it is the one place the memory view and the value view meet.
	pub offset: u32,
}

/// An aggregate seen as a flat run of WebAssembly values, in declaration
/// pre-order — the same order `wasm::flatten_type_to_scalars` produces and the
/// WASM signature uses. Each entry's [`Scalar::offset`] is its memory byte
/// offset, so the list order and the memory order are independent.
#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct ScalarTable {
	entries: Box<[Scalar]>,
	/// Declaration field `i` owns `entries[field_starts[i]..field_starts[i + 1]]`.
	/// Monotone, length is `fields + 1`, and the last entry is `entries.len()`.
	/// A zero-sized field owns an empty range.
	field_starts: Box<[u32]>,
}

impl ScalarTable {
	/// Total number of WebAssembly values this aggregate occupies.
	#[inline]
	pub fn len(&self) -> usize {
		self.entries.len()
	}

	#[inline]
	pub fn is_empty(&self) -> bool {
		self.entries.is_empty()
	}

	#[inline]
	pub fn get(&self, index: ScalarIndex) -> Scalar {
		self.entries[usize::from(index)]
	}

	#[inline]
	pub fn iter(&self) -> impl ExactSizeIterator<Item = &Scalar> {
		self.entries.iter()
	}

	/// The scalars declaration field `field` contributes — empty for a ZST
	/// field, more than one for a field that is itself an aggregate.
	#[inline]
	pub fn of_field(&self, field: FieldIndex) -> &[Scalar] {
		let i = usize::from(field);
		let (start, end) = (
			self.field_starts[i] as usize,
			self.field_starts[i + 1] as usize,
		);
		&self.entries[start..end]
	}

	/// Half-open scalar range owned by declaration field `field`.
	#[inline]
	pub fn field_range(&self, field: FieldIndex) -> std::ops::Range<u32> {
		let i = usize::from(field);
		self.field_starts[i]..self.field_starts[i + 1]
	}

	/// Which declaration field owns `scalar`. Used to fold an `AggregateGet` of
	/// a literal aggregate back down to the sub-node holding that scalar.
	pub fn owner(&self, scalar: ScalarIndex) -> FieldIndex {
		let raw = u32::from(scalar);
		// `field_starts` is monotone with a terminator, so the owning field is
		// the last start not exceeding `raw`.
		let field = self
			.field_starts
			.partition_point(|&start| start <= raw)
			.saturating_sub(1);
		FieldIndex::new(field as u32)
	}
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Aggregate {
	/// Fields in declaration order. A zero-sized field is present here and
	/// occupies no scalar.
	pub fields: Box<[Field]>,
	/// Size and alignment of the aggregate as a whole.
	pub layout: Layout,
	/// The same aggregate, seen as a flat run of WebAssembly values.
	pub scalars: ScalarTable,
}

impl Aggregate {
	#[inline]
	pub fn field(&self, index: FieldIndex) -> Field {
		self.fields[usize::from(index)]
	}

	/// Number of declaration fields. Note this is *not* the number of scalars —
	/// see [`ScalarTable::len`].
	#[inline]
	pub fn field_count(&self) -> usize {
		self.fields.len()
	}
}

/// Whether a memory is locally defined or provided by the WASM host.
/// `External < Internal` so a stable sort puts imported memories first,
/// matching the WASM binary format requirement.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum MemorySource {
	External,
	Internal,
}

/// A memory's index type, lowered from TIR's `TypeIndex::U32`/`U64` (see
/// `tir::Memory::kind`) once and for all here — MIR and codegen branch on
/// this constantly (instruction selection, pointer size), so it's kept as
/// an exhaustively-matchable enum instead of repeated `TypeIndex` equality
/// checks. TIR itself never needs the distinction as its own enum: it only
/// validates the `Size` binding is one of the two and passes the
/// `TypeIndex` straight through.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum MemoryKind {
	Memory32,
	Memory64,
}

impl MemoryKind {
	#[inline]
	pub fn pointer_size(self) -> u32 {
		match self {
			MemoryKind::Memory32 => 4,
			MemoryKind::Memory64 => 8,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct MemoryInfo {
	pub id: MemoryId,
	pub source: MemorySource,
	pub kind: MemoryKind,
	pub min_pages: Option<u32>,
	pub max_pages: Option<u32>,
}

/// One entry in the static data segment — either a string literal or an array
/// constant. Bytes are pre-encoded; the layout (byte offset) is computed by
/// codegen after DCE.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct StaticEntry {
	pub bytes: Box<[u8]>,
	pub align: u32,
	/// The memory whose data segment this entry is placed in.
	pub memory: MemoryId,
}

/// A checked program lowered to backend form.
///
/// Identity is backend-local: [`FunctionId`], [`GlobalId`] and [`MemoryId`] are
/// assigned by lowering and are neither source indices nor Wasm indices. The
/// maps from checked source identity (`FunctionIdx`, `GlobalIdx`, …) to these
/// IDs, and the monomorphization worklist that mints them, belong to the
/// lowerer — MIR only ever stores the result. Codegen re-derives Wasm indices
/// from these IDs, imports first.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct MIR {
	pub functions: Vec<Function>,
	#[cfg_attr(test, serde(skip))]
	pub inline_functions: HashSet<FunctionId>,
	pub signatures: Vec<FunctionSignature>,
	pub globals: Vec<Global>,
	pub exports: Vec<ExportItem>,
	pub imports: Vec<ImportModule>,
	pub memories: Vec<MemoryInfo>,
	pub aggregates: Box<[Aggregate]>,
	pub static_entries: Vec<StaticEntry>,
	/// Direct call edges collected during lowering: (caller_mir_id,
	/// callee_mir_id). Consumed by `run_inlining_pass` to build the call
	/// graph.
	#[cfg_attr(test, serde(skip))]
	pub call_edges: Vec<(FunctionId, FunctionId)>,
	/// The synthetic start function that assigns all user-defined globals at
	/// module instantiation time, if any globals are declared.
	pub start_function: Option<FunctionId>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct ImportModule {
	pub name: String,
	pub items: Vec<ImportModuleItem>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub enum ImportModuleItem {
	Function {
		name: SymbolU32,
		id: FunctionId,
		signature_index: SignatureIndex,
	},
	Global {
		name: SymbolU32,
		id: GlobalId,
	},
	Memory {
		name: SymbolU32,
		id: MemoryId,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
pub enum ExportItem {
	Function { id: FunctionId, name: SymbolU32 },
	Global { id: GlobalId, name: SymbolU32 },
	Memory { id: MemoryId, name: SymbolU32 },
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy)]
pub enum Mutability {
	Mutable,
	Immutable,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub struct Local {
	pub ty: ValueType,
	pub mutability: Mutability,
}

/// A scope's shape, mirroring the `Block`/`Loop` distinction the checker keeps
/// per scope.
///
/// MIR carries its own enum rather than reusing `opt::BlockKind`: opt's version
/// also describes synthetic blocks that have no MIR scope at all. The two are
/// intentionally separate index spaces with separate meanings.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum BlockKind {
	/// A plain block: `break` leaves it and gives it a value.
	Block,
	/// A loop: `continue` restarts it, `break` leaves it.
	Loop,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub struct BlockScope {
	pub kind: BlockKind,
	pub result: ValueType,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct FunctionSignature {
	pub items: Box<[ValueType]>,
	pub params_count: usize,
}

impl FunctionSignature {
	pub fn params(&self) -> &[ValueType] {
		&self.items[..self.params_count]
	}

	pub fn result(&self) -> ValueType {
		self.items[self.params_count]
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub struct Function {
	pub id: FunctionId,
	pub signature_index: SignatureIndex,
	pub scopes: Vec<BlockScope>,
	/// Every local the function owns, in one flat, function-wide space —
	/// scope 0's locals first, then each subsequent scope's own locals in
	/// scope order, including MIR-synthesized temporaries (which are just
	/// appended here directly, not routed through any particular scope).
	pub locals: Vec<Local>,
	pub block: Expression,
	/// Indices into `MIR.static_pool.entries` owned by this function.
	/// Codegen unions these across all live functions to determine which
	/// entries to include in the WASM data segment.
	pub static_data: Vec<u32>,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy)]
pub enum ConstInit {
	Int(i64),
	Float(f64),
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct Global {
	pub id: GlobalId,
	pub ty: ValueType,
	pub mutability: Mutability,
	/// WASM global section init expression. Mutable globals use zero here
	/// and are assigned at runtime by the start function. Immutable globals
	/// carry their literal value directly.
	pub const_init: ConstInit,
}

/// Memory layout of a type: size in bytes and required alignment in bytes.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Layout {
	pub size: u32,
	pub align: u32,
}

impl MIR {
	/// The aggregate `index` refers to.
	#[inline]
	pub fn aggregate(&self, index: AggregateIndex) -> &Aggregate {
		&self.aggregates[usize::from(index)]
	}
}
