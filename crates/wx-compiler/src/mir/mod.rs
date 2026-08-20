/// the role of MIR is to desugar the syntax like x += 1 into x = x + 1 and
/// lower the concepts like enums into primitive constants, convert labels from
/// symbols in interner into numeric indices
use std::collections::{HashMap, HashSet};

use string_interner::symbol::SymbolU32;

use crate::ast::{self, DefIdGenerator};
use crate::tir::{self, ItemAttribute};

mod inlining;
use inlining::{rebase_scope, run_inlining_pass};

#[cfg(test)]
mod tests;

pub type LocalIndex = u32;
pub type ScopeIndex = u32;
pub type GlobalIndex = u32;
pub type SignatureIndex = u32;
pub type FunctionIndex = u32;
pub type AggregateIndex = u32;

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub enum ExprKind {
	Noop,
	Bool {
		value: bool,
	},
	Function {
		id: ast::DefId,
	},
	Int {
		value: i64,
	},
	Float {
		value: f64,
	},
	LocalGet {
		scope_index: ScopeIndex,
		local_index: LocalIndex,
	},
	LocalSet {
		scope_index: ScopeIndex,
		local_index: LocalIndex,
		value: Box<Expression>,
	},
	Aggregate {
		values: Box<[Expression]>,
	},
	AggregateGet {
		scope_index: ScopeIndex,
		local_index: LocalIndex,
		value_index: u32,
	},
	AggregateSet {
		scope_index: ScopeIndex,
		local_index: LocalIndex,
		value_index: u32,
		value: Box<Expression>,
	},
	Global {
		id: ast::DefId,
	},
	GlobalSet {
		id: ast::DefId,
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
		memory: ast::DefId,
	},
	/// `i32.const <wasm_memory_index>` — the wasm linear-memory index of this
	/// memory, resolved at codegen time.
	MemoryIndex {
		memory: ast::DefId,
	},
	/// `memory.size` — current size of a linear memory in pages.
	MemorySize {
		memory: ast::DefId,
	},
	/// `memory.grow` — grow linear memory by N pages; pushes old size or -1.
	MemoryGrow {
		memory: ast::DefId,
		delta: Box<Expression>,
	},
	/// `memory.fill` — fill a region of linear memory with a byte value.
	MemoryFill {
		memory: ast::DefId,
		dst: Box<Expression>,
		val: Box<Expression>,
		len: Box<Expression>,
	},
	/// `memory.copy` — copy a region between (possibly different) linear memories.
	MemoryCopy {
		dst_memory: ast::DefId,
		src_memory: ast::DefId,
		dst: Box<Expression>,
		src: Box<Expression>,
		len: Box<Expression>,
	},
	/// Load a value from the address held in `pointer`.
	PointerLoad {
		pointer: Box<Expression>,
		/// Static byte offset added to the address (WASM memarg immediate).
		offset: u32,
		memory: ast::DefId,
	},
	/// Store `value` to the address held in `pointer`.
	PointerStore {
		pointer: Box<Expression>,
		value: Box<Expression>,
		/// Static byte offset added to the address (WASM memarg immediate).
		offset: u32,
		memory: ast::DefId,
	},
	/// Pointer to a static data entry (index into `MIR.static_data`).
	/// Resolves to an `i32.const <byte_offset>` at codegen time.
	StaticPointer {
		data_index: u32,
	},
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug, serde::Serialize))]
pub enum Type {
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
	Pointer {
		memory: ast::DefId,
		kind: MemoryKind,
	},
	Aggregate {
		aggregate_index: AggregateIndex,
	},
	Function {
		signature_index: SignatureIndex,
	},
}

impl Type {
	/// Types whose division, remainder, right shift, and ordered comparisons
	/// must use the unsigned WASM instruction variants. Pointers are
	/// unsigned addresses.
	pub fn is_unsigned(self) -> bool {
		matches!(
			self,
			Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Pointer { .. }
		)
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub struct Expression {
	pub kind: ExprKind,
	pub ty: Type,
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Aggregate {
	pub values: Box<[Type]>,
	/// Byte offset of each field, in physical (layout) order.
	pub offsets: Box<[u32]>,
	pub layout: Layout,
	/// `decl_to_phys[decl_index]` = physical slot index.
	decl_to_phys: Box<[u32]>,
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

	#[inline]
	fn from_type_index(ty: tir::TypeIndex) -> MemoryKind {
		if ty == tir::TypeIndex::U32 {
			MemoryKind::Memory32
		} else if ty == tir::TypeIndex::U64 {
			MemoryKind::Memory64
		} else {
			unreachable!("TIR only ever validates Size as u32 or u64")
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct MemoryInfo {
	pub id: ast::DefId,
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
	pub memory: ast::DefId,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct MIR {
	pub functions: Vec<Function>,
	#[cfg_attr(test, serde(skip))]
	pub inline_functions: HashSet<ast::DefId>,
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
	pub call_edges: Vec<(ast::DefId, ast::DefId)>,
	/// The synthetic start function that assigns all user-defined globals at
	/// module instantiation time, if any globals are declared.
	pub start_function: Option<ast::DefId>,
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
		id: ast::DefId,
		signature_index: SignatureIndex,
	},
	Global {
		name: SymbolU32,
		id: ast::DefId,
	},
	Memory {
		name: SymbolU32,
		id: ast::DefId,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
pub enum ExportItem {
	Function { id: ast::DefId, name: SymbolU32 },
	Global { id: ast::DefId, name: SymbolU32 },
	Memory { id: ast::DefId, name: SymbolU32 },
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
	pub ty: Type,
	pub mutability: Mutability,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub struct BlockScope {
	pub kind: tir::BlockKind,
	pub parent: Option<ScopeIndex>,
	pub locals: Vec<Local>,
	pub result: Type,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct FunctionSignature {
	pub items: Box<[Type]>,
	pub params_count: usize,
}

impl FunctionSignature {
	pub fn params(&self) -> &[Type] {
		&self.items[..self.params_count]
	}

	pub fn result(&self) -> Type {
		self.items[self.params_count]
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone)]
pub struct Function {
	pub id: ast::DefId,
	pub signature_index: SignatureIndex,
	pub scopes: Vec<BlockScope>,
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
	pub id: ast::DefId,
	pub ty: Type,
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

impl Layout {
	fn pad_to_align(self) -> Self {
		Layout {
			size: (self.size + self.align - 1) & !(self.align - 1),
			align: self.align,
		}
	}
}

/// How an aggregate's fields are physically ordered in memory.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum FieldOrder {
	/// Fields are sorted by alignment descending to minimize padding
	/// (the default for tuples, slices, and plain structs).
	Sorted,
	/// Fields keep declaration order — set by `#[fixed_order]`.
	Fixed,
}

impl MIR {
	pub fn build(
		tir: &tir::TIR,
		interner: &ast::StringInterner,
		id_generator: ast::DefIdGenerator,
	) -> MIR {
		let mut builder = Builder {
			tir,
			interner,
			aggregate_index_lookup: HashMap::new(),
			aggregates: Vec::new(),
			signature_pool: Vec::new(),
			signature_index_lookup: HashMap::new(),
			current_substitutions: Box::new([]),
			mono_registry: MonoRegistry::new(id_generator),
			current_function_id: None,
			call_edges: Vec::new(),
			static_entries: Vec::new(),
			symbol_to_entry_index: HashMap::new(),
		};

		// MIR functions: live defined (Internal) monomorphic functions only.
		// Generic functions (own or inherited type params) are lowered on demand by the
		// mono pass below. Wasm index ordering (imports first) is codegen's
		// responsibility.
		let mut functions: Vec<Function> = Vec::new();
		let mut inline_functions: HashSet<ast::DefId> = HashSet::new();
		for func in &tir.functions {
			if func.body.is_some()
				&& func.total_type_param_count() == 0
				&& !tir.is_import_namespace(func.namespace)
				&& !func.attributes.contains(&ItemAttribute::Intrinsic)
			{
				if func.attributes.contains(&tir::ItemAttribute::Inline) {
					inline_functions.insert(func.id);
				}
				builder.current_function_id = Some(func.id);
				functions.push(builder.lower_function(func));
			}
		}

		let globals: Vec<Global> = tir
			.globals
			.iter()
			.filter(|g| {
				!tir.is_import_namespace(g.namespace) && g.value.is_some()
			})
			.map(|g| builder.lower_global(g))
			.collect();

		// Build the start function before the mono loop so that any generic
		// functions called in global initializers (e.g. null<M, T>()) are added
		// to the worklist and processed together with the rest.
		let start_id = builder.mono_registry.id_generator.generate();
		let start_function = builder.build_start_function(tir, start_id);

		// Monomorphization: drain the registry worklist populated by lower_expression
		// when it encountered calls to generic functions. Each iteration may add new
		// entries (generic-calls-generic), so we loop until the worklist is exhausted.
		let mut work_cursor = 0;
		loop {
			let current_len = builder.mono_registry.worklist.len();
			if work_cursor >= current_len {
				break;
			}
			let pending = builder.mono_registry.worklist
				[work_cursor..current_len]
				.to_vec();
			work_cursor = current_len;

			for (orig_id, subst, mono_id) in pending {
				let tir_idx = tir.expect_function_index(orig_id);
				let tir_func = &tir.functions[tir_idx as usize];
				let is_inline =
					tir_func.attributes.contains(&tir::ItemAttribute::Inline);

				builder.current_substitutions = subst;
				builder.current_function_id = Some(mono_id);

				// lower_function interns the concrete signature (substitutions active).
				let mut mir_func = builder.lower_function(tir_func);
				mir_func.id = mono_id;

				builder.current_substitutions = Box::new([]);
				functions.push(mir_func);

				if is_inline {
					inline_functions.insert(mono_id);
				}
			}
		}

		let imports: Vec<ImportModule> = tir
			.import_decls
			.iter()
			.map(|module| ImportModule {
				name: interner
					.resolve(module.external_name.inner)
					.unwrap()
					.to_string(),
				items: module
					.lookup
					.iter()
					.map(|(symbol, value)| match value {
						tir::ImportValue::Function { id } => {
							let tir_idx = tir.expect_function_index(*id);
							let tir_func = &tir.functions[tir_idx as usize];
							let signature_index = builder
								.intern_tir_function_type(
									tir_func.signature_index,
								);
							ImportModuleItem::Function {
								name: *symbol,
								id: *id,
								signature_index,
							}
						}
						tir::ImportValue::Global { id } => {
							ImportModuleItem::Global {
								name: *symbol,
								id: *id,
							}
						}
						tir::ImportValue::Memory { id } => {
							ImportModuleItem::Memory {
								name: *symbol,
								id: *id,
							}
						}
					})
					.collect(),
			})
			.collect();

		let signatures = builder.signature_pool;

		if let Some(ref f) = start_function {
			functions.push(f.clone());
		}

		let mut mir = MIR {
			functions,
			inline_functions,
			globals,
			signatures,
			aggregates: builder.aggregates.into_boxed_slice(),
			imports,
			start_function: start_function.map(|_| start_id),
			memories: tir
				.memories
				.iter()
				.map(|mem| MemoryInfo {
					id: mem.id,
					source: MemorySource::Internal,
					kind: MemoryKind::from_type_index(mem.size.inner),
					min_pages: mem.min_pages,
					max_pages: mem.max_pages,
				})
				.collect(),
			exports: {
				let mut exports: Vec<ExportItem> = tir
					.exports
					.values()
					.map(|export| match export {
						tir::ExportItem::Function {
							id,
							external_name,
							internal_name,
						} => ExportItem::Function {
							id: *id,
							name: (*external_name)
								.map(|n| n.inner)
								.unwrap_or(internal_name.inner),
						},
						tir::ExportItem::Global {
							id,
							external_name,
							internal_name,
						} => ExportItem::Global {
							id: *id,
							name: (*external_name)
								.map(|n| n.inner)
								.unwrap_or(internal_name.inner),
						},
						tir::ExportItem::Memory {
							id,
							external_name,
							internal_name,
						} => ExportItem::Memory {
							id: *id,
							name: (*external_name)
								.map(|n| n.inner)
								.unwrap_or(internal_name.inner),
						},
					})
					.collect();
				exports.sort_by_key(|e| match e {
					ExportItem::Function { name, .. } => *name,
					ExportItem::Global { name, .. } => *name,
					ExportItem::Memory { name, .. } => *name,
				});
				exports
			},
			call_edges: builder.call_edges,
			static_entries: builder.static_entries,
		};

		run_inlining_pass(&mut mir);
		mir
	}
}

/// Tracks which generic function instantiations are needed, assigning each
/// unique `(original_def_id, type_args)` pair a fresh synthetic `DefId`.
struct MonoRegistry {
	map: HashMap<(ast::DefId, Box<[tir::TypeIndex]>), ast::DefId>,
	/// Stable insertion-order worklist; grows as generic-calls-generic paths
	/// are encountered during lowering.
	worklist: Vec<(ast::DefId, Box<[tir::TypeIndex]>, ast::DefId)>,
	id_generator: DefIdGenerator,
}

impl MonoRegistry {
	fn new(id_generator: DefIdGenerator) -> Self {
		Self {
			map: HashMap::new(),
			worklist: Vec::new(),
			id_generator,
		}
	}

	fn get_or_insert(
		&mut self,
		orig_id: ast::DefId,
		type_args: Box<[tir::TypeIndex]>,
	) -> ast::DefId {
		if let Some(&id) = self.map.get(&(orig_id, type_args.clone())) {
			return id;
		}
		let id = self.id_generator.generate();
		self.map.insert((orig_id, type_args.clone()), id);
		self.worklist.push((orig_id, type_args, id));
		id
	}
}

/// Result of [`Builder::lower_index_address`].
enum IndexAddress {
	/// Compile-time constant index: `byte_offset = value * elem_size` is
	/// folded directly into the WASM memarg immediate of the surrounding
	/// `PointerLoad`/`PointerStore` — no runtime Add/Mul is emitted.
	Constant { ptr: Expression, byte_offset: u32 },
	/// Variable index: the runtime `base + idx * elem_size` computation is
	/// already embedded inside `ptr`; callers use `offset: 0`.
	Dynamic(Expression),
}

struct Builder<'tir> {
	tir: &'tir tir::TIR,
	interner: &'tir ast::StringInterner,
	aggregate_index_lookup: HashMap<(FieldOrder, Box<[Type]>), AggregateIndex>,
	aggregates: Vec<Aggregate>,
	/// Concrete function signatures, interned on demand. The index into this
	/// Vec is the MIR `SignatureIndex` used throughout the rest of the IR.
	signature_pool: Vec<FunctionSignature>,
	signature_index_lookup: HashMap<FunctionSignature, SignatureIndex>,
	/// Concrete type substitution for the current generic instantiation.
	/// Indexed by `param_index`: `current_substitutions[i]` is the concrete
	/// `TypeIndex` for `TypeParam { param_index: i }`.
	current_substitutions: Box<[tir::TypeIndex]>,
	mono_registry: MonoRegistry,
	/// MIR id of the function currently being lowered. Set by `MIR::build`
	/// before each `lower_function` call (TIR id in Phase 1, synthetic mono id
	/// in Phase 2) so that call edges are recorded with accurate MIR ids.
	current_function_id: Option<ast::DefId>,
	/// Direct call edges collected during lowering: (caller_mir_id,
	/// callee_mir_id). Used after all functions are built to derive each
	/// function's `callers` list from actual MIR-level calls rather than
	/// TIR accesses.
	call_edges: Vec<(ast::DefId, ast::DefId)>,
	static_entries: Vec<StaticEntry>,
	/// String-literal dedup: the same literal may still appear once per
	/// memory, so the memory is part of the key.
	symbol_to_entry_index: HashMap<(SymbolU32, ast::DefId), u32>,
}

struct FunctionContext {
	frame: Vec<BlockScope>,
	current_scope_index: usize,
	/// Static pool indices referenced by expressions in this function.
	static_data: Vec<u32>,
}

impl<'tir> Builder<'tir> {
	/// Given an `AssocTypeProjection`'s already-known `trait_index`/
	/// `assoc_name` and a fully concrete `base`, finds the applicable impl
	/// and its stored associated-type value. That value lives in the
	/// *impl's own* type-param scheme (e.g. `TraitImpl(impl_idx)`'s param 0
	/// for `impl<T> Trait for Foo<T> { type Assoc = ...; }`), not the
	/// caller's — so it is only safe to further resolve/lower under
	/// `impl_type_args`, never under whatever `current_substitutions`
	/// happens to be active at the call site. Returns `impl_type_args`
	/// alongside so callers can install it before recursing.
	fn find_assoc_type_value(
		&self,
		base: tir::TypeIndex,
		trait_index: tir::TraitIndex,
		assoc_name: SymbolU32,
	) -> (tir::TraitImplIndex, Box<[tir::TypeIndex]>, tir::TypeIndex) {
		// `trait_index` is already known (part of the projection itself), so
		// go straight through `find_trait_impl` rather than
		// `resolve_impl_member`'s ambiguity-scanning candidate search — no
		// ambiguity is possible here.
		let (impl_idx, impl_type_args) =
			self.tir.find_trait_impl(base, trait_index).expect(
				"no impl found for associated type projection during MIR lowering",
			);
		let assoc_ty = match self.tir.trait_impls[impl_idx as usize]
			.members
			.get(&assoc_name)
			.unwrap()
		{
			tir::ImplEntry::AssocType(idx) => {
				self.tir.assoc_type_impls[*idx as usize].ty.unwrap().inner
			}
			_ => unreachable!(),
		};
		(impl_idx, impl_type_args, assoc_ty)
	}

	/// Resolve a TIR TypeIndex to a concrete TIR TypeIndex using `current_substitutions`.
	/// Handles chains of `AssocTypeProjection` by recursing through the base.
	///
	/// Only chases direct `TypeParam`/`AssocTypeProjection` leaves — it
	/// cannot represent a *composite* associated-type value (e.g.
	/// `type Assoc = Box<T>;`) as a single resolved `TypeIndex` without
	/// interning a new one, which this `&self` method has no way to do
	/// (`Builder::tir` is a frozen `&TIR`). Its only callers needing that —
	/// `resolve_memory_id` and its own recursion on `base` — never hit the
	/// composite case in practice (a memory type is never wrapped inside
	/// another type constructor). `lower_type_index`'s `AssocTypeProjection`
	/// arm handles the general/composite case itself instead of going
	/// through here, since it can install `impl_type_args` into
	/// `current_substitutions` before recursing.
	fn resolve_tir_type(&self, ty: tir::TypeIndex) -> tir::TypeIndex {
		match &self.tir.types[ty.as_usize()] {
			tir::Type::TypeParam { param_index, .. } => {
				self.current_substitutions[*param_index as usize]
			}
			tir::Type::AssocTypeProjection {
				base,
				assoc_name,
				trait_index,
			} => {
				let (base, assoc_name, trait_index) =
					(*base, *assoc_name, *trait_index);
				let concrete_base = self.resolve_tir_type(base);
				let (impl_idx, impl_type_args, assoc_ty) = self
					.find_assoc_type_value(
						concrete_base,
						trait_index,
						assoc_name,
					);
				let resolved = match &self.tir.types[assoc_ty.as_usize()] {
					tir::Type::TypeParam { param_index, owner }
						if *owner
							== tir::TypeParamOwner::TraitImpl(impl_idx) =>
					{
						impl_type_args[*param_index as usize]
					}
					_ => assoc_ty,
				};
				self.resolve_tir_type(resolved)
			}
			_ => ty,
		}
	}

	fn resolve_memory_id(&self, memory_ty: tir::TypeIndex) -> ast::DefId {
		let concrete = self.resolve_tir_type(memory_ty);
		match &self.tir.types[concrete.as_usize()] {
			tir::Type::Memory { id, .. } => *id,
			_ => unreachable!(
				"memory TypeIndex does not resolve to Type::Memory"
			),
		}
	}

	/// The MIR pointer type for a memory, with the memory's width baked in
	/// so later stages can pick value types and access widths from the type
	/// alone, without a memory-table lookup.
	fn pointer_type(&self, memory: ast::DefId) -> Type {
		let tir_idx = self.tir.expect_memory_index(memory) as usize;
		Type::Pointer {
			memory,
			kind: MemoryKind::from_type_index(
				self.tir.memories[tir_idx].size.inner,
			),
		}
	}

	/// Compute the memory layout of a type.
	///
	/// Fields of structs and tuples are sorted by alignment descending before
	/// computing padding, giving optimal (minimal) struct sizes.
	///
	/// Panics on `Error`, `Unknown`, `ImportModule`, `Enum`, or non-value
	/// types.
	pub fn compute_layout(&mut self, idx: tir::TypeIndex) -> Layout {
		if idx == tir::TypeIndex::F32
			|| idx == tir::TypeIndex::I32
			|| idx == tir::TypeIndex::U32
			|| idx == tir::TypeIndex::CHAR
		{
			return Layout { size: 4, align: 4 };
		}
		if idx == tir::TypeIndex::I64
			|| idx == tir::TypeIndex::U64
			|| idx == tir::TypeIndex::F64
		{
			return Layout { size: 8, align: 8 };
		}
		if idx == tir::TypeIndex::U8
			|| idx == tir::TypeIndex::I8
			|| idx == tir::TypeIndex::BOOL
		{
			return Layout { size: 1, align: 1 };
		}
		if idx == tir::TypeIndex::UNIT || idx == tir::TypeIndex::NEVER {
			return Layout { size: 0, align: 1 };
		}
		if idx == tir::TypeIndex::U16 || idx == tir::TypeIndex::I16 {
			return Layout { size: 2, align: 2 };
		}

		match &self.tir.types[idx.as_usize()] {
			tir::Type::Function { .. } | tir::Type::FunctionItem { .. } => {
				Layout { size: 4, align: 4 }
			}
			tir::Type::Pointer { memory, .. }
			| tir::Type::Array { memory, .. } => {
				let id = self.resolve_memory_id(*memory);
				let tir_idx = self.tir.expect_memory_index(id) as usize;
				let pointer_size = MemoryKind::from_type_index(
					self.tir.memories[tir_idx].size.inner,
				)
				.pointer_size();
				Layout {
					size: pointer_size,
					align: pointer_size,
				}
			}
			tir::Type::Slice { memory, .. } => {
				let id = self.resolve_memory_id(*memory);
				let tir_idx = self.tir.expect_memory_index(id) as usize;
				let pointer_size = MemoryKind::from_type_index(
					self.tir.memories[tir_idx].size.inner,
				)
				.pointer_size();
				Layout {
					size: pointer_size * 2,
					align: pointer_size,
				}
			}
			tir::Type::Tuple { elements } => {
				let mir_elems: Box<[Type]> = elements
					.iter()
					.map(|&e| self.lower_type_index(e))
					.collect();
				let aggregate_index =
					self.ensure_aggregate(mir_elems, FieldOrder::Sorted);
				self.aggregates[aggregate_index as usize].layout
			}
			tir::Type::Struct { struct_index, args } => {
				let si = *struct_index;
				let aggregate_index =
					self.ensure_aggregate_for_struct(si, args);
				self.aggregates[aggregate_index as usize].layout
			}
			_ => unreachable!(),
		}
	}

	fn ensure_aggregate(
		&mut self,
		mir_fields: Box<[Type]>,
		order: FieldOrder,
	) -> AggregateIndex {
		let key = (order, mir_fields);
		if let Some(&index) = self.aggregate_index_lookup.get(&key) {
			return index;
		}
		let (_, mir_fields) = key;

		// TODO: for `FieldOrder::Fixed` the decl-to-phys indirection below is
		// unnecessary (physical order always equals declaration order) — skip
		// the sort/lookup scaffolding entirely and build offsets directly for
		// a leaner fast path once this shows up in profiling.
		let mut sorted: Vec<(u32, Layout)> = mir_fields
			.iter()
			.copied()
			.enumerate()
			.map(|(decl, ty)| (decl as u32, self.mir_type_layout(ty)))
			.collect();
		if order == FieldOrder::Sorted {
			sorted.sort_by_key(|(_, b)| std::cmp::Reverse(b.align));
		}

		// Single pass: total layout, per-field byte offsets, and ordering maps.
		let mut layout = Layout { size: 0, align: 1 };
		let mut offsets = Vec::with_capacity(sorted.len());
		let mut decl_to_phys = vec![0u32; sorted.len()];
		for (phys, (decl, field_layout)) in sorted.iter().copied().enumerate() {
			layout.size = (layout.size + field_layout.align - 1)
				& !(field_layout.align - 1);
			offsets.push(layout.size);
			layout.size += field_layout.size;
			layout.align = layout.align.max(field_layout.align);
			decl_to_phys[decl as usize] = phys as u32;
		}
		layout = layout.pad_to_align();

		let values: Box<[Type]> = sorted
			.iter()
			.map(|&(decl, _)| mir_fields[decl as usize])
			.collect();

		let aggregate_index = self.aggregates.len() as AggregateIndex;
		self.aggregate_index_lookup
			.insert((order, mir_fields), aggregate_index);
		self.aggregates.push(Aggregate {
			decl_to_phys: decl_to_phys.into_boxed_slice(),
			layout,
			offsets: offsets.into_boxed_slice(),
			values,
		});
		aggregate_index
	}

	fn mir_type_layout(&self, ty: Type) -> Layout {
		match ty {
			Type::I32 | Type::U32 | Type::F32 => Layout { size: 4, align: 4 },
			Type::I64 | Type::U64 | Type::F64 => Layout { size: 8, align: 8 },
			Type::U8 | Type::I8 | Type::Bool => Layout { size: 1, align: 1 },
			Type::U16 | Type::I16 => Layout { size: 2, align: 2 },
			Type::Unit | Type::Never => Layout { size: 0, align: 1 },
			Type::Pointer { kind, .. } => {
				let ptr_size = kind.pointer_size();
				Layout {
					size: ptr_size,
					align: ptr_size,
				}
			}
			Type::Function { .. } => Layout { size: 4, align: 4 },
			Type::Aggregate { aggregate_index } => {
				self.aggregates[aggregate_index as usize].layout
			}
		}
	}

	/// Ensures an aggregate exists for a struct, handling generic structs by
	/// temporarily substituting the struct's own type params from `args`.
	fn ensure_aggregate_for_struct(
		&mut self,
		struct_index: u32,
		args: &[tir::TypeIndex],
	) -> AggregateIndex {
		// TODO: detect infinite-size cycles caused by generic struct instantiation
		// (e.g. `struct Node { inner: DirectIdentity<Node> }` where
		// `DirectIdentity<T> { value: T }`). TIR only catches concrete cycles;
		// generic ones require substitution, which only happens here during
		// monomorphization. When this is implemented, extend the DFS in
		// `tir::Builder::find_direct_struct_recursion` with a substitution map
		// and promote the error to TIR. For now, this will stack-overflow on
		// truly recursive generic instantiations.

		// For generic structs, resolve TypeParam/AssocTypeProjection entries
		// in args and temporarily install them as current_substitutions so
		// lower_type_index resolves fields. Must go through `resolve_tir_type`
		// (not just a shallow `TypeParam` match) so a struct instantiated with
		// a projection type arg (e.g. `Layout<Self::M>` inside a trait default
		// method body) resolves once `Self` is concrete, instead of installing
		// the unresolved projection itself as the new substitution scope.
		let saved = if !args.is_empty() {
			let concrete_args: Box<[tir::TypeIndex]> =
				args.iter().map(|&a| self.resolve_tir_type(a)).collect();
			Some(std::mem::replace(
				&mut self.current_substitutions,
				concrete_args,
			))
		} else {
			None
		};
		// fields: &'tir [StructField] — lifetime tied to TIR, not to Builder
		let tir_struct = &self.tir.structs[struct_index as usize];
		let order = if tir_struct
			.attributes
			.contains(&tir::ItemAttribute::FixedOrder)
		{
			FieldOrder::Fixed
		} else {
			FieldOrder::Sorted
		};
		let mir_fields: Box<[Type]> = tir_struct
			.fields
			.iter()
			.map(|f| self.lower_type_index(f.ty.inner))
			.collect();
		let aggregate_index = self.ensure_aggregate(mir_fields, order);
		if let Some(saved) = saved {
			self.current_substitutions = saved;
		}
		aggregate_index
	}

	fn lower_type_index(&mut self, type_idx: tir::TypeIndex) -> Type {
		match type_idx {
			idx if idx == tir::TypeIndex::ERROR => unreachable!(),
			idx if idx == tir::TypeIndex::INFER => unreachable!(),
			idx if idx == tir::TypeIndex::UNIT => return Type::Unit,
			idx if idx == tir::TypeIndex::NEVER => return Type::Never,
			idx if idx == tir::TypeIndex::INTEGER => unreachable!(),
			idx if idx == tir::TypeIndex::I8 => return Type::I8,
			idx if idx == tir::TypeIndex::U8 => return Type::U8,
			idx if idx == tir::TypeIndex::I16 => return Type::I16,
			idx if idx == tir::TypeIndex::U16 => return Type::U16,
			idx if idx == tir::TypeIndex::I32 => return Type::I32,
			idx if idx == tir::TypeIndex::U32 => return Type::U32,
			idx if idx == tir::TypeIndex::I64 => return Type::I64,
			idx if idx == tir::TypeIndex::U64 => return Type::U64,
			idx if idx == tir::TypeIndex::F32 => return Type::F32,
			idx if idx == tir::TypeIndex::F64 => return Type::F64,
			idx if idx == tir::TypeIndex::BOOL => return Type::Bool,
			idx if idx == tir::TypeIndex::CHAR => return Type::U32,
			_ => {}
		};

		match &self.tir.types[type_idx.as_usize()] {
			tir::Type::TypeParam { param_index, .. } => {
				let param_index = *param_index;
				let concrete = self.current_substitutions[param_index as usize];
				self.lower_type_index(concrete)
			}
			tir::Type::Function { .. } => Type::Function {
				signature_index: self.intern_tir_function_type(type_idx),
			},
			tir::Type::FunctionItem { id, type_args } => {
				let fi = self.tir.expect_function_index(*id) as usize;
				let sig_idx = self.tir.functions[fi].signature_index;
				if type_args.is_empty() {
					Type::Function {
						signature_index: self.intern_tir_function_type(sig_idx),
					}
				} else {
					// Resolve any TypeParam entries in type_args through current_substitutions.
					let concrete_args: Box<[tir::TypeIndex]> = type_args
						.iter()
						.map(|&ty| match &self.tir.types[ty.as_usize()] {
							tir::Type::TypeParam { param_index, .. } => self
								.current_substitutions
								.get(*param_index as usize)
								.copied()
								.unwrap_or(ty),
							_ => ty,
						})
						.collect();
					let saved = std::mem::replace(
						&mut self.current_substitutions,
						concrete_args,
					);
					let signature_index =
						self.intern_tir_function_type(sig_idx);
					self.current_substitutions = saved;
					Type::Function { signature_index }
				}
			}
			tir::Type::AssocTypeProjection {
				base,
				assoc_name,
				trait_index,
			} => {
				let concrete_base = self.resolve_tir_type(*base);
				let (_, impl_type_args, assoc_ty) = self.find_assoc_type_value(
					concrete_base,
					*trait_index,
					*assoc_name,
				);
				// Unlike `resolve_tir_type`, this is `&mut self`, so it can
				// install the impl's own substitutions before recursing —
				// which is what makes a *composite* associated-type value
				// (e.g. `type Assoc = Box<T>;`) work: `assoc_ty`'s `T`
				// belongs to the impl's own param scheme, not whatever
				// scheme `current_substitutions` holds for the caller right
				// now, so it must be swapped in before `lower_type_index`
				// recurses into `assoc_ty`'s structure (e.g. `Box<_>`'s
				// type arg) and resolves that `TypeParam` leaf.
				let saved = std::mem::replace(
					&mut self.current_substitutions,
					impl_type_args,
				);
				let result = self.lower_type_index(assoc_ty);
				self.current_substitutions = saved;
				result
			}
			tir::Type::Pointer { memory, .. }
			| tir::Type::Array { memory, .. } => {
				let memory = self.resolve_memory_id(*memory);
				self.pointer_type(memory)
			}
			tir::Type::Slice { memory, .. } => {
				let memory = self.resolve_memory_id(*memory);
				let tir_idx = self.tir.expect_memory_index(memory) as usize;
				let kind_ty = self.tir.memories[tir_idx].size;
				let len_ty = self.lower_type_index(kind_ty.inner);
				// Slice layout is a fixed `{ ptr, len }` ABI contract, not a
				// sorting outcome — see the pipeline notes on slice lowering.
				let aggregate_index = self.ensure_aggregate(
					Box::new([self.pointer_type(memory), len_ty]),
					FieldOrder::Fixed,
				);
				Type::Aggregate { aggregate_index }
			}
			tir::Type::Memory { .. } => Type::Unit,
			tir::Type::Struct { struct_index, args } => {
				let aggregate_index =
					self.ensure_aggregate_for_struct(*struct_index, args);
				Type::Aggregate { aggregate_index }
			}
			tir::Type::Tuple { elements } => {
				let mir_elems: Box<[Type]> = elements
					.iter()
					.map(|&e| self.lower_type_index(e))
					.collect();
				let aggregate_index =
					self.ensure_aggregate(mir_elems, FieldOrder::Sorted);
				Type::Aggregate { aggregate_index }
			}
			tir::Type::Enum { enum_index } => {
				let repr_ty = self.tir.enums[*enum_index as usize].repr_type;
				self.lower_type_index(repr_ty)
			}
			_ => unreachable!(),
		}
	}

	fn intern_signature(&mut self, sig: FunctionSignature) -> SignatureIndex {
		let next = self.signature_pool.len() as SignatureIndex;
		*self
			.signature_index_lookup
			.entry(sig.clone())
			.or_insert_with(|| {
				self.signature_pool.push(sig);
				next
			})
	}

	/// Converts a TIR function type (by its type-pool index) to a MIR
	/// `SignatureIndex`, interning the concrete signature on first use.
	fn intern_tir_function_type(
		&mut self,
		type_idx: tir::TypeIndex,
	) -> SignatureIndex {
		let sig = match &self.tir.types[type_idx.as_usize()] {
			tir::Type::Function { signature } => signature.clone(),
			_ => unreachable!("expected Function type"),
		};
		let concrete = FunctionSignature {
			items: sig
				.params()
				.iter()
				.chain(std::iter::once(&sig.result()))
				.map(|&ty| self.lower_type_index(ty))
				.collect(),
			params_count: sig.params().len(),
		};
		self.intern_signature(concrete)
	}

	fn record_call_edge(&mut self, callee_id: ast::DefId) {
		if let Some(caller_id) = self.current_function_id {
			self.call_edges.push((caller_id, callee_id));
		}
	}

	/// Whether `id` refers to an `#[intrinsic]` function. Intrinsic calls are
	/// eliminated entirely during lowering (substituted for a dedicated
	/// `ExprKind` variant) and never become a real `mir::Function`, so they
	/// must never be recorded as a call-graph edge — an intrinsic id showing
	/// up as someone's callee would leave `CallGraph`'s `callers` map without
	/// an entry for it (populated only from `mir.functions`), which the
	/// inlining pass's Kahn-queue loop assumes always exists.
	fn is_intrinsic(&self, id: ast::DefId) -> bool {
		let func_index = self.tir.expect_function_index(id);
		self.tir.functions[func_index as usize]
			.attributes
			.contains(&tir::ItemAttribute::Intrinsic)
	}

	fn lower_function(&mut self, func: &tir::Function) -> Function {
		let body = func
			.body
			.as_ref()
			.expect("lower_function called on bodyless function");
		let frame = body
			.stack
			.scopes
			.iter()
			.map(|scope| {
				let result_type_idx =
					scope.inferred_type.infer_or(tir::TypeIndex::UNIT);
				let locals = scope
					.locals
					.iter()
					.map(|tir_local| Local {
						ty: self.lower_type_index(tir_local.ty),
						mutability: if tir_local.mut_span.is_some() {
							Mutability::Mutable
						} else {
							Mutability::Immutable
						},
					})
					.collect();
				BlockScope {
					kind: scope.kind,
					parent: scope.parent,
					locals,
					result: self.lower_type_index(result_type_idx),
				}
			})
			.collect();

		let mut ctx = FunctionContext {
			current_scope_index: 0,
			frame,
			static_data: Vec::new(),
		};

		let mut top_sink = Vec::new();
		let block = self.lower_expression(&mut ctx, &body.block, &mut top_sink);

		Function {
			id: func.id,
			signature_index: self
				.intern_tir_function_type(func.signature_index),
			scopes: ctx.frame,
			block,
			static_data: ctx.static_data,
		}
	}

	fn lower_global(&mut self, global: &tir::Global) -> Global {
		let ty = self.lower_type_index(global.ty.inner);
		let zero = match ty {
			Type::F32 | Type::F64 => ConstInit::Float(0.0),
			_ => ConstInit::Int(0),
		};
		let const_init = global
			.value
			.as_ref()
			.and_then(|body| match body.block.kind {
				tir::ExprKind::Int { value } => {
					Some(ConstInit::Int(value as i64))
				}
				tir::ExprKind::Float { value } => Some(ConstInit::Float(value)),
				_ => None,
			})
			.unwrap_or(zero);
		Global {
			id: global.id,
			ty,
			mutability: if global.mut_span.is_some() {
				Mutability::Mutable
			} else {
				Mutability::Immutable
			},
			const_init,
		}
	}

	/// Builds the synthetic `__wx_start` function that initializes all user
	/// globals in declaration order. Returns `None` when there are no globals
	/// with initializers.
	fn build_start_function(
		&mut self,
		tir: &tir::TIR,
		start_id: ast::DefId,
	) -> Option<Function> {
		let globals_with_init: Vec<&tir::Global> = tir
			.globals
			.iter()
			.filter(|g| {
				g.mut_span.is_some()
					&& g.value.as_ref().is_some_and(|body| {
						!matches!(
							body.block.kind,
							tir::ExprKind::Int { .. }
								| tir::ExprKind::Float { .. }
						)
					})
			})
			.collect();

		if globals_with_init.is_empty() {
			return None;
		}

		self.current_function_id = Some(start_id);

		// Root scope for the start function body (no params, no locals).
		let root_scope = BlockScope {
			kind: tir::BlockKind::Block,
			parent: None,
			locals: vec![],
			result: Type::Unit,
		};
		let mut combined_frame: Vec<BlockScope> = vec![root_scope];
		let mut combined_body: Vec<Expression> = Vec::new();
		let mut combined_static_data: Vec<u32> = Vec::new();

		for g in globals_with_init {
			let body = g.value.as_ref().unwrap();

			let frame: Vec<BlockScope> = body
				.stack
				.scopes
				.iter()
				.map(|scope| {
					let result_ty =
						scope.inferred_type.infer_or(tir::TypeIndex::UNIT);
					let locals = scope
						.locals
						.iter()
						.map(|tir_local| Local {
							ty: self.lower_type_index(tir_local.ty),
							mutability: if tir_local.mut_span.is_some() {
								Mutability::Mutable
							} else {
								Mutability::Immutable
							},
						})
						.collect();
					BlockScope {
						kind: scope.kind,
						parent: scope.parent,
						locals,
						result: self.lower_type_index(result_ty),
					}
				})
				.collect();

			let mut ctx = FunctionContext {
				current_scope_index: 0,
				frame,
				static_data: Vec::new(),
			};

			let mut sink = Vec::new();
			let mut lowered =
				self.lower_expression(&mut ctx, &body.block, &mut sink);

			// Offset all scope indices so this global's scopes don't collide
			// with scopes from prior globals in the combined frame.
			let scope_offset = combined_frame.len() as ScopeIndex;
			rebase_scope(&mut lowered, scope_offset, 0);
			for e in sink.iter_mut() {
				rebase_scope(e, scope_offset, 0);
			}

			// Append this global's scopes to the combined frame, adjusting
			// parent pointers so roots become children of the start body scope.
			for mut scope in ctx.frame {
				scope.parent = match scope.parent {
					None => Some(0),
					Some(p) => Some(p + scope_offset),
				};
				combined_frame.push(scope);
			}

			combined_body.extend(sink);
			combined_body.push(Expression {
				kind: ExprKind::GlobalSet {
					id: g.id,
					value: Box::new(lowered),
				},
				ty: Type::Unit,
			});
			combined_static_data.extend(ctx.static_data);
		}

		let unit_sig = FunctionSignature {
			items: Box::new([Type::Unit]),
			params_count: 0,
		};
		let signature_index = self.intern_signature(unit_sig);

		Some(Function {
			id: start_id,
			signature_index,
			scopes: combined_frame,
			block: Expression {
				kind: ExprKind::Block {
					scope_index: 0,
					expressions: combined_body.into_boxed_slice(),
				},
				ty: Type::Unit,
			},
			static_data: combined_static_data,
		})
	}

	/// Encode one compile-time element (Int or Float ExprKind + its TIR type)
	/// as little-endian bytes appended to `buf`.
	fn encode_element(
		buf: &mut Vec<u8>,
		kind: &tir::ExprKind,
		ty: tir::TypeIndex,
	) {
		match kind {
			tir::ExprKind::Int { value } => {
				let v = *value;
				if ty == tir::TypeIndex::I8 || ty == tir::TypeIndex::U8 {
					buf.push(v as u8);
				} else if ty == tir::TypeIndex::I16 || ty == tir::TypeIndex::U16
				{
					buf.extend_from_slice(&(v as u16).to_le_bytes());
				} else if ty == tir::TypeIndex::I32 || ty == tir::TypeIndex::U32
				{
					buf.extend_from_slice(&(v as u32).to_le_bytes());
				} else if ty == tir::TypeIndex::I64 || ty == tir::TypeIndex::U64
				{
					buf.extend_from_slice(&v.to_le_bytes());
				} else {
					unreachable!("unexpected int element type");
				}
			}
			tir::ExprKind::Float { value } => {
				if ty == tir::TypeIndex::F32 {
					buf.extend_from_slice(
						&(*value as f32).to_bits().to_le_bytes(),
					);
				} else if ty == tir::TypeIndex::F64 {
					buf.extend_from_slice(&value.to_bits().to_le_bytes());
				} else {
					unreachable!("unexpected float element type");
				}
			}
			_ => unreachable!("array element must be a compile-time constant"),
		}
	}

	/// Add a static data entry (array constant); returns `(index, byte_size)`.
	fn push_static_data(
		&mut self,
		func_ctx: &mut FunctionContext,
		bytes: Vec<u8>,
		align: u32,
		memory: ast::DefId,
	) -> (u32, u32) {
		let size = bytes.len() as u32;
		let idx = self.static_entries.len() as u32;
		self.static_entries.push(StaticEntry {
			bytes: bytes.into_boxed_slice(),
			align,
			memory,
		});
		func_ctx.static_data.push(idx);
		(idx, size)
	}

	/// Add a string literal entry, deduplicating by (symbol, memory);
	/// returns `(index, byte_size)`.
	fn push_string_data(
		&mut self,
		func_ctx: &mut FunctionContext,
		symbol: SymbolU32,
		memory: ast::DefId,
	) -> (u32, u32) {
		if let Some(&idx) = self.symbol_to_entry_index.get(&(symbol, memory)) {
			let size = self.static_entries[idx as usize].bytes.len() as u32;
			func_ctx.static_data.push(idx);
			return (idx, size);
		}
		let s = self
			.interner
			.resolve(symbol)
			.expect("unresolved string symbol");
		let size = s.len() as u32;
		let idx = self.static_entries.len() as u32;
		self.static_entries.push(StaticEntry {
			bytes: s.as_bytes().to_vec().into_boxed_slice(),
			align: 1,
			memory,
		});
		self.symbol_to_entry_index.insert((symbol, memory), idx);
		func_ctx.static_data.push(idx);
		(idx, size)
	}

	fn lower_index_address(
		&mut self,
		func_ctx: &mut FunctionContext,
		object: &tir::Expression,
		index: &tir::Expression,
		elem_ty: tir::TypeIndex,
		sink: &mut Vec<Expression>,
	) -> IndexAddress {
		let elem_size = self.compute_layout(elem_ty).size;

		// For slices the lowered object is an aggregate {ptr, len}; extract
		// the pointer field (index 0) as the base address.
		let (base, ptr_ty) = if let tir::Type::Slice { memory, .. } =
			self.tir.types[object.ty.as_usize()]
		{
			let memory_id = self.resolve_memory_id(memory);
			let ptr_ty = self.pointer_type(memory_id);
			let (si, li) = match &object.kind {
				tir::ExprKind::Local {
					scope_index,
					local_index,
				} => (*scope_index, *local_index),
				_ => {
					let lowered = self.lower_expression(func_ctx, object, sink);
					let obj_ty = self.lower_type_index(object.ty);
					let temp = func_ctx.frame[0].locals.len() as u32;
					func_ctx.frame[0].locals.push(Local {
						ty: obj_ty,
						mutability: Mutability::Immutable,
					});
					sink.push(Expression {
						kind: ExprKind::LocalSet {
							scope_index: 0,
							local_index: temp,
							value: Box::new(lowered),
						},
						ty: Type::Unit,
					});
					(0, temp)
				}
			};
			let ptr = Expression {
				kind: ExprKind::AggregateGet {
					scope_index: si,
					local_index: li,
					value_index: 0,
				},
				ty: ptr_ty,
			};
			(ptr, ptr_ty)
		} else {
			let ptr_ty = self.lower_type_index(object.ty);
			let base = self.lower_expression(func_ctx, object, sink);
			(base, ptr_ty)
		};

		// Constant index: fold `value * elem_size` directly into the memarg immediate.
		if let tir::ExprKind::Int { value } = index.kind {
			return IndexAddress::Constant {
				ptr: base,
				byte_offset: (value as u32).wrapping_mul(elem_size),
			};
		}

		let idx_ty = self.lower_type_index(index.ty);
		let idx = self.lower_expression(func_ctx, index, sink);
		IndexAddress::Dynamic(Expression {
			kind: ExprKind::Add {
				left: Box::new(base),
				right: Box::new(Expression {
					kind: ExprKind::Mul {
						left: Box::new(idx),
						right: Box::new(Expression {
							kind: ExprKind::Int {
								value: elem_size as i64,
							},
							ty: idx_ty,
						}),
					},
					ty: idx_ty,
				}),
			},
			ty: ptr_ty,
		})
	}

	/// Lowers an already-folded compile-time constant value directly to a MIR
	/// scalar — shared by every place that reads a `ConstValue` cached on TIR
	/// (`Constant`, `EnumVariant`) so codegen never has to re-walk the original
	/// expression tree just to rediscover a value TIR already computed.
	fn lower_const_value(const_value: tir::ConstValue, ty: Type) -> Expression {
		match const_value {
			tir::ConstValue::Int(value) => Expression {
				kind: ExprKind::Int { value },
				ty,
			},
			tir::ConstValue::Float(value) => Expression {
				kind: ExprKind::Float { value },
				ty,
			},
			tir::ConstValue::Bool(value) => Expression {
				kind: ExprKind::Bool { value },
				ty,
			},
			tir::ConstValue::Char(value) => Expression {
				kind: ExprKind::Int {
					value: value as i64,
				},
				ty,
			},
		}
	}

	fn lower_expression(
		&mut self,
		func_ctx: &mut FunctionContext,
		expr: &tir::Expression,
		sink: &mut Vec<Expression>,
	) -> Expression {
		use crate::ast::UnaryOp;

		match &expr.kind {
			tir::ExprKind::Error
			| tir::ExprKind::Placeholder
			| tir::ExprKind::Memory { .. } => Expression {
				kind: ExprKind::Noop,
				ty: Type::Unit,
			},
			tir::ExprKind::Unreachable => Expression {
				kind: ExprKind::Unreachable,
				ty: Type::Never,
			},
			tir::ExprKind::Int { value } => Expression {
				kind: ExprKind::Int {
					value: *value as i64,
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Float { value } => Expression {
				kind: ExprKind::Float { value: *value },
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Bool { value } => Expression {
				kind: ExprKind::Bool { value: *value },
				ty: Type::Bool,
			},
			tir::ExprKind::Global { id } => Expression {
				kind: ExprKind::Global { id: *id },
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Local {
				scope_index,
				local_index,
			} => Expression {
				kind: ExprKind::LocalGet {
					scope_index: *scope_index,
					local_index: *local_index,
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Function { id } => {
				// If the FunctionItem carries non-empty type_args the reference is a
				// monomorphized generic function; register the mono instance.
				match &self.tir.types[expr.ty.as_usize()] {
					&tir::Type::FunctionItem {
						id: fn_id,
						ref type_args,
					} if !type_args.is_empty() => {
						let concrete_args: Box<[tir::TypeIndex]> = type_args
							.iter()
							.map(|&ty| match &self.tir.types[ty.as_usize()] {
								tir::Type::TypeParam {
									param_index, ..
								} => self
									.current_substitutions
									.get(*param_index as usize)
									.copied()
									.unwrap_or(ty),
								_ => ty,
							})
							.collect();
						let mono_id = self
							.mono_registry
							.get_or_insert(fn_id, concrete_args.clone());
						if !self.is_intrinsic(fn_id) {
							self.record_call_edge(mono_id);
						}
						let fi = self.tir.expect_function_index(fn_id) as usize;
						let sig_idx = self.tir.functions[fi].signature_index;
						let saved = std::mem::replace(
							&mut self.current_substitutions,
							concrete_args,
						);
						let signature_index =
							self.intern_tir_function_type(sig_idx);
						self.current_substitutions = saved;
						Expression {
							kind: ExprKind::Function { id: mono_id },
							ty: Type::Function { signature_index },
						}
					}
					_ => {
						if !self.is_intrinsic(*id) {
							self.record_call_edge(*id);
						}
						Expression {
							kind: ExprKind::Function { id: *id },
							ty: self.lower_type_index(expr.ty),
						}
					}
				}
			}
			tir::ExprKind::Char { value } => Expression {
				kind: ExprKind::Int {
					value: *value as i64,
				},
				ty: Type::U32,
			},
			tir::ExprKind::String { symbol } => {
				// The literal's slice type says which memory its bytes are
				// placed in.
				let memory_id = match &self.tir.types[expr.ty.as_usize()] {
					tir::Type::Slice { memory, .. } => {
						self.resolve_memory_id(*memory)
					}
					_ => unreachable!("string literal must have slice type"),
				};
				let (data_index, size) =
					self.push_string_data(func_ctx, *symbol, memory_id);
				let ty = self.lower_type_index(expr.ty);
				let mem_idx = self.tir.expect_memory_index(memory_id) as usize;
				Expression {
					kind: ExprKind::Aggregate {
						values: Box::new([
							Expression {
								kind: ExprKind::StaticPointer { data_index },
								ty: self.pointer_type(memory_id),
							},
							Expression {
								kind: ExprKind::Int { value: size as i64 },
								// Slice len has the memory's size type
								// (u64 for a 64-bit memory).
								ty: self.lower_type_index(
									self.tir.memories[mem_idx].size.inner,
								),
							},
						]),
					},
					ty,
				}
			}
			tir::ExprKind::Return { value } => Expression {
				kind: ExprKind::Return {
					value: value.as_ref().map(|v| {
						Box::new(self.lower_expression(func_ctx, v, sink))
					}),
				},
				ty: Type::Never,
			},
			tir::ExprKind::EnumVariant {
				enum_index,
				variant_index,
			} => {
				let enum_ = &self.tir.enums[*enum_index as usize];
				let variant = &enum_.variants[*variant_index as usize];
				match variant.const_value {
					Some(const_value) => Self::lower_const_value(
						const_value,
						self.lower_type_index(expr.ty),
					),
					// Error-free TIR guarantees every variant folds to a
					// constant — see the `NotConstEvaluatable`/range checks
					// in `Builder::build_enum`. MIR::build assumes TIR has
					// no errors (the CLI aborts beforehand otherwise).
					None => unreachable!(
						"enum variant without a folded compile-time value"
					),
				}
			}
			tir::ExprKind::GenericCall {
				id,
				type_args,
				arguments,
			} => {
				let func_index = self.tir.expect_function_index(*id);
				let func = &self.tir.functions[func_index as usize];
				if func.attributes.iter().any(|attr| match attr {
					tir::ItemAttribute::Intrinsic => true,
					_ => false,
				}) {
					return self.lower_intrinsic(
						func_ctx,
						func.name.inner,
						expr.ty,
						type_args,
						arguments,
						sink,
					);
				}

				// Substitute any TypeParam/AssocTypeProjection entries in
				// type_args through current_substitutions.  Without this, a
				// generic calling another generic (e.g. `call_wrap<T>` calling
				// `wrap<T>`) would register `wrap<TypeParam{0}>` instead of
				// `wrap<i32>`, causing `lower_type_index` to recurse
				// infinitely when it later tries to lower `TypeParam{0}` with
				// substitutions = [TypeParam{0}]. Must go through
				// `resolve_tir_type` (not just a shallow `TypeParam` match) so
				// a projection like `Self::M` — inferred as a type arg to a
				// nested generic call inside a trait default method body —
				// also resolves once `Self` is concrete, instead of being
				// passed through unresolved and later failing to find a trait
				// impl for a still-generic base.
				let concrete_type_args: Box<[tir::TypeIndex]> = type_args
					.iter()
					.map(|&ty| self.resolve_tir_type(ty))
					.collect();
				let mono_id = self
					.mono_registry
					.get_or_insert(*id, concrete_type_args.clone());
				self.record_call_edge(mono_id);

				// Intern the callee's concrete signature with the resolved
				// substitutions active, then restore previous substitutions.
				let tir_func_sig_idx = {
					let tir_idx = self.tir.expect_function_index(*id);
					self.tir.functions[tir_idx as usize].signature_index
				};
				let saved_subs = std::mem::replace(
					&mut self.current_substitutions,
					concrete_type_args,
				);
				let callee_sig_idx =
					self.intern_tir_function_type(tir_func_sig_idx);
				self.current_substitutions = saved_subs;

				let lowered_args: Box<[_]> = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call {
						callee: Box::new(Expression {
							kind: ExprKind::Function { id: mono_id },
							ty: Type::Function {
								signature_index: callee_sig_idx,
							},
						}),
						arguments: lowered_args,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::GenericMethodCall {
				id,
				type_args,
				arguments,
			} => {
				let tir_idx = self.tir.expect_function_index(*id);
				let tir_func = &self.tir.functions[tir_idx as usize];

				// Resolve any TypeParam/AssocTypeProjection entries in
				// type_args through active substitutions — see the matching
				// comment in the `GenericCall` arm above for why a shallow
				// `TypeParam`-only match isn't enough (e.g. `Self::M` used as
				// a nested generic call's type arg inside a trait default
				// method body).
				let resolved: Box<[tir::TypeIndex]> = type_args
					.iter()
					.map(|&ty| self.resolve_tir_type(ty))
					.collect();

				// Intern the callee's concrete signature before consuming `resolved`.
				let saved_subs = std::mem::replace(
					&mut self.current_substitutions,
					resolved.clone(),
				);
				let callee_sig_idx =
					self.intern_tir_function_type(tir_func.signature_index);
				self.current_substitutions = saved_subs;

				let target_id = if tir_func.body.is_some() {
					// Default impl: monomorphize with resolved type_args.
					self.mono_registry.get_or_insert(*id, resolved)
				} else {
					// Abstract method called inside a default body: the concrete Self
					// type is now known, so dispatch directly to the impl.
					let concrete_self = resolved[0];
					let method_name = tir_func.name.inner;
					let trait_index = match tir_func.parent {
						Some(tir::ItemParent::Trait(idx)) => idx,
						_ => unreachable!(
							"abstract trait method must be parented by its trait"
						),
					};
					let (trait_impl_idx, impl_type_args) = self
						.tir
						.find_trait_impl(concrete_self, trait_index)
						.expect("no impl found for abstract trait method");
					let impl_func_idx = self.tir.trait_impls
						[trait_impl_idx as usize]
						.members
						.get(&method_name)
						.map(|entry| match entry {
							tir::ImplEntry::Method(idx) => *idx,
							_ => unreachable!(),
						})
						.expect("no impl found for abstract trait method");
					let impl_func_id =
						self.tir.functions[impl_func_idx as usize].id;
					// `impl_type_args` alone only covers the impl block's own
					// params (e.g. `impl<T> Trait for Box<T>`'s `T`) — the
					// impl's copy of the method can *also* declare its own
					// extra params (e.g. `fn write<Mem: Memory>(...)` on an
					// otherwise-concrete `impl Hasher for DefaultHasher`),
					// which `impl_type_args` says nothing about. Reusing the
					// bare `impl_func_id` whenever `impl_type_args` alone is
					// empty is therefore wrong whenever the method has any
					// such params of its own: that instance was never
					// eagerly emitted by `MIR::build`'s main loop (which only
					// emits functions with zero *total* type params), so the
					// bare id has no MIR function/wasm index behind it.
					let impl_own_type_params =
						&self.tir.functions[impl_func_idx as usize].type_params;
					if impl_type_args.is_empty()
						&& impl_own_type_params.is_empty()
					{
						// Fully concrete: zero total type params, so it was
						// already eagerly emitted (with this bare id) — reuse
						// it directly rather than registering a redundant
						// duplicate through `mono_registry`.
						impl_func_id
					} else {
						// Needs monomorphizing on demand via the worklist.
						// Full arg list: the impl block's own args (its
						// inherited-param prefix) followed by the method's
						// own args — `resolved`'s tail after the leading
						// `Self` slot (index 0, already consumed above to
						// find the impl).
						let full_args: Box<[tir::TypeIndex]> = impl_type_args
							.iter()
							.copied()
							.chain(resolved[1..].iter().copied())
							.collect();
						self.mono_registry
							.get_or_insert(impl_func_id, full_args)
					}
				};
				self.record_call_edge(target_id);

				let lowered_args: Box<[_]> = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call {
						callee: Box::new(Expression {
							kind: ExprKind::Function { id: target_id },
							ty: Type::Function {
								signature_index: callee_sig_idx,
							},
						}),
						arguments: lowered_args,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Call { callee, arguments } => {
				let callee =
					Box::new(self.lower_expression(func_ctx, callee, sink));
				if let ExprKind::Function { id } = callee.kind {
					let func_index = self.tir.expect_function_index(id);
					let func = &self.tir.functions[func_index as usize];
					if func.attributes.iter().any(|attr| match attr {
						tir::ItemAttribute::Intrinsic => true,
						_ => false,
					}) {
						return self.lower_intrinsic(
							func_ctx,
							func.name.inner,
							expr.ty,
							&[],
							arguments,
							sink,
						);
					}
					self.record_call_edge(id);
				};
				let arguments = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call { callee, arguments },
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::MethodCall { arguments, id } => {
				self.record_call_edge(*id);
				let tir_idx = self.tir.expect_function_index(*id);
				let callee_sig_idx = self.intern_tir_function_type(
					self.tir.functions[tir_idx as usize].signature_index,
				);
				let callee = Box::new(Expression {
					kind: ExprKind::Function { id: *id },
					ty: Type::Function {
						signature_index: callee_sig_idx,
					},
				});
				let arguments: Box<_> = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call { callee, arguments },
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::NamespaceAccess { namespace, member } => {
				match &member.kind {
					tir::ExprKind::Const { id } => {
						let const_idx =
							self.tir.expect_const_index(*id) as usize;
						let result_ty = self.lower_type_index(expr.ty);
						// Only `DATA_END`/`INDEX` are compiler-synthesized —
						// every other `Memory`-trait const (e.g. `PAGE_SIZE`)
						// is an ordinary default value, already folded to a
						// `const_value` in TIR, and falls through to the
						// generic path below like any other const.
						if let tir::Type::Memory { id, .. } =
							&self.tir.types[namespace.inner.as_usize()]
						{
							let const_name_sym =
								self.tir.constants[const_idx].name.inner;
							let const_name =
								self.interner.resolve(const_name_sym).unwrap();
							match const_name {
								"DATA_END" => {
									return Expression {
										kind: ExprKind::MemoryOffset {
											memory: *id,
										},
										ty: result_ty,
									};
								}
								"INDEX" => {
									return Expression {
										kind: ExprKind::MemoryIndex {
											memory: *id,
										},
										ty: result_ty,
									};
								}
								_ => {}
							}
						};

						match self.tir.constants[const_idx].const_value {
							Some(const_value) => {
								Self::lower_const_value(const_value, result_ty)
							}
							None => unreachable!(),
						}
					}
					_ => self.lower_expression(func_ctx, member, sink),
				}
			}
			tir::ExprKind::Const { id } => {
				let const_idx = self.tir.expect_const_index(*id) as usize;
				let result_ty = self.lower_type_index(expr.ty);
				if let Some(const_value) =
					self.tir.constants[const_idx].const_value
				{
					Self::lower_const_value(const_value, result_ty)
				} else if self.tir.constants[const_idx].value.is_some() {
					todo!("complex const expression in MIR lowering")
				} else {
					unreachable!(
						"compiler-implemented constant referenced outside namespace access"
					)
				}
			}
			tir::ExprKind::FieldAccess {
				object,
				field: member,
			} => {
				let (struct_index, args) =
					match &self.tir.types[object.ty.as_usize()] {
						tir::Type::Struct { struct_index, args } => {
							(*struct_index, args)
						}
						_ => unreachable!("ObjectAccess on non-struct type"),
					};
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, args);
				let aggregate = &self.aggregates[aggregate_index as usize];
				let decl_index = self.tir.structs[struct_index as usize].lookup
					[&member.inner];
				let phys_index = aggregate.decl_to_phys[decl_index];
				let field_ty = aggregate.values[phys_index as usize];

				match &object.kind {
					tir::ExprKind::Local {
						scope_index,
						local_index,
					} => Expression {
						kind: ExprKind::AggregateGet {
							scope_index: *scope_index,
							local_index: *local_index,
							value_index: phys_index,
						},
						ty: field_ty,
					},
					_ => {
						let object_ty = self.lower_type_index(object.ty);
						let object_lowered =
							self.lower_expression(func_ctx, object, sink);

						let temp_idx = func_ctx.frame[0].locals.len() as u32;
						func_ctx.frame[0].locals.push(Local {
							ty: object_ty,
							mutability: Mutability::Immutable,
						});

						sink.push(Expression {
							kind: ExprKind::LocalSet {
								scope_index: 0,
								local_index: temp_idx,
								value: Box::new(object_lowered),
							},
							ty: Type::Unit,
						});

						Expression {
							kind: ExprKind::AggregateGet {
								scope_index: 0,
								local_index: temp_idx,
								value_index: phys_index,
							},
							ty: field_ty,
						}
					}
				}
			}
			tir::ExprKind::StructInit { fields, .. } => {
				let (struct_index, args) =
					match &self.tir.types[expr.ty.as_usize()] {
						tir::Type::Struct { struct_index, args } => {
							(*struct_index, args)
						}
						_ => unreachable!("StructInit type must be Struct"),
					};
				let lowered: Vec<Expression> = fields
					.iter()
					.map(|f| self.lower_expression(func_ctx, f, sink))
					.collect();
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, args);
				let decl_to_phys =
					&self.aggregates[aggregate_index as usize].decl_to_phys;
				let mut phys_slots: Vec<Option<Expression>> =
					(0..lowered.len()).map(|_| None).collect();
				for (decl, expr) in lowered.into_iter().enumerate() {
					phys_slots[decl_to_phys[decl] as usize] = Some(expr);
				}
				let values: Box<[Expression]> =
					phys_slots.into_iter().map(|e| e.unwrap()).collect();
				Expression {
					kind: ExprKind::Aggregate { values },
					ty: Type::Aggregate { aggregate_index },
				}
			}
			tir::ExprKind::TupleInit { elements } => {
				let types: Box<[Type]> =
					match &self.tir.types[expr.ty.as_usize()] {
						tir::Type::Tuple { elements } => {
							let elements: Box<[Type]> = elements
								.iter()
								.map(|&t| self.lower_type_index(t))
								.collect();
							elements
						}
						_ => unreachable!("TupleInit type must be Tuple"),
					};
				let lowered: Vec<Expression> = elements
					.iter()
					.map(|expr| self.lower_expression(func_ctx, expr, sink))
					.collect();
				let aggregate_index =
					self.ensure_aggregate(types, FieldOrder::Sorted);
				let decl_to_phys =
					&self.aggregates[aggregate_index as usize].decl_to_phys;
				let mut phys_slots: Vec<Option<Expression>> =
					(0..lowered.len()).map(|_| None).collect();
				for (decl, expr) in lowered.into_iter().enumerate() {
					phys_slots[decl_to_phys[decl] as usize] = Some(expr);
				}
				let values: Box<[Expression]> =
					phys_slots.into_iter().map(|e| e.unwrap()).collect();
				Expression {
					kind: ExprKind::Aggregate { values },
					ty: Type::Aggregate { aggregate_index },
				}
			}
			tir::ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				let condition =
					Box::new(self.lower_expression(func_ctx, condition, sink));
				let then_block =
					Box::new(self.lower_expression(func_ctx, then_block, sink));
				let else_block = else_block.as_ref().map(|e| {
					Box::new(self.lower_expression(func_ctx, e, sink))
				});
				Expression {
					kind: ExprKind::IfElse {
						condition,
						then_block,
						else_block,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Match { scrutinee, arms } => {
				let selector =
					Box::new(self.lower_expression(func_ctx, scrutinee, sink));
				let mut cases: Vec<(i64, Expression)> =
					Vec::with_capacity(arms.len());
				let mut default: Option<Box<Expression>> = None;
				for arm in arms.iter() {
					let body = self.lower_expression(func_ctx, &arm.body, sink);
					match arm.pattern {
						tir::Pattern::Wildcard => {
							default = Some(Box::new(body));
						}
						tir::Pattern::Int(v) => cases.push((v, body)),
						tir::Pattern::Bool(v) => cases.push((v as i64, body)),
						tir::Pattern::Char(v) => cases.push((v as i64, body)),
						tir::Pattern::EnumVariant {
							enum_index,
							variant_index,
						} => {
							let variant = &self.tir.enums[enum_index as usize]
								.variants[variant_index as usize];
							let discriminant = match variant.const_value {
								Some(tir::ConstValue::Int(v)) => v,
								// Error-free TIR guarantees an integer-repr
								// enum's variants fold to an int constant —
								// see the `EnumReprNotInteger` check in
								// `Builder::build_enum`.
								_ => unreachable!(
									"enum variant without a folded integer compile-time value"
								),
							};
							cases.push((discriminant, body));
						}
					}
				}
				Expression {
					kind: ExprKind::Switch {
						selector,
						cases: cases.into_boxed_slice(),
						default,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Break { scope_index, value } => Expression {
				kind: ExprKind::Break {
					scope_index: *scope_index,
					value: value.as_ref().map(|v| {
						Box::new(self.lower_expression(func_ctx, v, sink))
					}),
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Continue { scope_index } => Expression {
				kind: ExprKind::Continue {
					scope_index: *scope_index,
				},
				ty: Type::Never,
			},
			tir::ExprKind::Loop { scope_index, block } => Expression {
				kind: ExprKind::Loop {
					scope_index: *scope_index,
					block: Box::new(
						self.lower_expression(func_ctx, block, sink),
					),
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Block {
				scope_index,
				expressions,
				result,
			} => {
				func_ctx.current_scope_index = *scope_index as usize;
				let mut inner_sink: Vec<Expression> = Vec::new();

				for e in expressions.iter() {
					let lowered =
						self.lower_expression(func_ctx, e, &mut inner_sink);
					inner_sink.push(lowered);
				}
				if let Some(result) = result {
					let lowered = self.lower_expression(
						func_ctx,
						result,
						&mut inner_sink,
					);
					inner_sink.push(lowered);
				}

				Expression {
					kind: ExprKind::Block {
						scope_index: *scope_index,
						expressions: inner_sink.into_boxed_slice(),
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::LocalDeclaration {
				scope_index,
				local_index,
				value,
				..
			} => Expression {
				kind: ExprKind::LocalSet {
					scope_index: *scope_index,
					local_index: *local_index,
					value: Box::new(
						self.lower_expression(func_ctx, value, sink),
					),
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Unary { operator, operand } => {
				let operand =
					Box::new(self.lower_expression(func_ctx, operand, sink));
				Expression {
					kind: match operator.inner {
						UnaryOp::InvertSign => ExprKind::Neg { value: operand },
						UnaryOp::Not => ExprKind::Eqz { value: operand },
						UnaryOp::BitNot => ExprKind::BitNot { value: operand },
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Binary {
				operator,
				left,
				right,
			} => {
				use tir::BinaryOp::*;

				let kind = match operator.inner {
					Add => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Add { left, right }
					}
					Sub => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Sub { left, right }
					}
					Mul => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Mul { left, right }
					}
					Div => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Div { left, right }
					}
					Rem => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Rem { left, right }
					}
					Eq => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Eq { left, right }
					}
					NotEq => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::NotEq { left, right }
					}
					Less => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Less { left, right }
					}
					LessEq => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::LessEq { left, right }
					}
					Greater => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Greater { left, right }
					}
					GreaterEq => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::GreaterEq { left, right }
					}
					And => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::And { left, right }
					}
					Or => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::Or { left, right }
					}
					BitAnd => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::BitAnd { left, right }
					}
					BitOr => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::BitOr { left, right }
					}
					BitXor => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::BitXor { left, right }
					}
					LeftShift => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::LeftShift { left, right }
					}
					RightShift => {
						let left = Box::new(
							self.lower_expression(func_ctx, left, sink),
						);
						let right = Box::new(
							self.lower_expression(func_ctx, right, sink),
						);
						ExprKind::RightShift { left, right }
					}
				};

				Expression {
					kind,
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::ArrayLiteral { elements, memory } => {
				let elem_ty = match &self.tir.types[expr.ty.as_usize()] {
					tir::Type::Array { of, .. } => *of,
					_ => unreachable!(),
				};
				let memory_id = self.resolve_memory_id(*memory);
				let align = self.compute_layout(elem_ty).align;
				let mut bytes = Vec::new();
				for elem in elements.iter() {
					Self::encode_element(&mut bytes, &elem.kind, elem_ty);
				}
				if bytes.is_empty() {
					return Expression {
						kind: ExprKind::Int { value: 0 },
						ty: self.pointer_type(memory_id),
					};
				}
				let (data_index, _) =
					self.push_static_data(func_ctx, bytes, align, memory_id);
				Expression {
					kind: ExprKind::StaticPointer { data_index },
					ty: self.pointer_type(memory_id),
				}
			}
			tir::ExprKind::ArrayRepeat {
				value,
				count,
				memory,
			} => {
				let elem_ty = match &self.tir.types[expr.ty.as_usize()] {
					tir::Type::Array { of, .. } => *of,
					_ => unreachable!(),
				};
				let memory_id = self.resolve_memory_id(*memory);
				let align = self.compute_layout(elem_ty).align;
				let mut elem_bytes = Vec::new();
				Self::encode_element(&mut elem_bytes, &value.kind, elem_ty);
				let bytes = elem_bytes.repeat(*count as usize);
				if bytes.is_empty() {
					return Expression {
						kind: ExprKind::Int { value: 0 },
						ty: self.pointer_type(memory_id),
					};
				}
				let (data_index, _) =
					self.push_static_data(func_ctx, bytes, align, memory_id);
				Expression {
					kind: ExprKind::StaticPointer { data_index },
					ty: self.pointer_type(memory_id),
				}
			}
			tir::ExprKind::SliceRange { object, start, end } => {
				let (elem_tir_ty, mem_tir_ty, static_size) = match &self
					.tir
					.types[object.ty.as_usize()]
				{
					tir::Type::Array {
						of, memory, size, ..
					} => (*of, *memory, Some(*size)),
					tir::Type::Slice { of, memory, .. } => (*of, *memory, None),
					_ => unreachable!(),
				};

				let elem_size = self.compute_layout(elem_tir_ty).size;
				let memory_id = self.resolve_memory_id(mem_tir_ty);
				let ptr_ty = self.pointer_type(memory_id);
				let tir_mem_idx =
					self.tir.expect_memory_index(memory_id) as usize;
				let idx_ty = self.lower_type_index(
					self.tir.memories[tir_mem_idx].size.inner,
				);

				let lowered_obj = self.lower_expression(func_ctx, object, sink);

				// For slices: extract base pointer and length from the aggregate.
				// Spill to a temp when the object isn't already a local.
				let (base_ptr, opt_slice_len) = match static_size {
					Some(_) => (lowered_obj, None),
					None => {
						let (si, li) = match &object.kind {
							tir::ExprKind::Local {
								scope_index,
								local_index,
							} => (*scope_index, *local_index),
							_ => {
								let obj_ty = self.lower_type_index(object.ty);
								let temp =
									func_ctx.frame[0].locals.len() as u32;
								func_ctx.frame[0].locals.push(Local {
									ty: obj_ty,
									mutability: Mutability::Immutable,
								});
								sink.push(Expression {
									kind: ExprKind::LocalSet {
										scope_index: 0,
										local_index: temp,
										value: Box::new(lowered_obj),
									},
									ty: Type::Unit,
								});
								(0, temp)
							}
						};
						let ptr = Expression {
							kind: ExprKind::AggregateGet {
								scope_index: si,
								local_index: li,
								value_index: 0,
							},
							ty: ptr_ty,
						};
						let len = Expression {
							kind: ExprKind::AggregateGet {
								scope_index: si,
								local_index: li,
								value_index: 1,
							},
							ty: idx_ty,
						};
						(ptr, Some(len))
					}
				};

				// If start is Some, spill it to a temp so it can be used
				// for both the pointer offset and the length subtraction.
				let start_local: Option<u32> = if start.is_some() {
					let s_lowered = self.lower_expression(
						func_ctx,
						start.as_ref().unwrap(),
						sink,
					);
					let temp = func_ctx.frame[0].locals.len() as u32;
					func_ctx.frame[0].locals.push(Local {
						ty: idx_ty,
						mutability: Mutability::Immutable,
					});
					sink.push(Expression {
						kind: ExprKind::LocalSet {
							scope_index: 0,
							local_index: temp,
							value: Box::new(s_lowered),
						},
						ty: Type::Unit,
					});
					Some(temp)
				} else {
					None
				};

				// Compute the offset pointer: base + start * elem_size
				let offset_ptr = match start_local {
					None => base_ptr,
					Some(li) => {
						let start_val = Expression {
							kind: ExprKind::LocalGet {
								scope_index: 0,
								local_index: li,
							},
							ty: idx_ty,
						};
						let byte_offset = if elem_size == 1 {
							start_val
						} else {
							Expression {
								kind: ExprKind::Mul {
									left: Box::new(start_val),
									right: Box::new(Expression {
										kind: ExprKind::Int {
											value: elem_size as i64,
										},
										ty: idx_ty,
									}),
								},
								ty: idx_ty,
							}
						};
						Expression {
							kind: ExprKind::Add {
								left: Box::new(base_ptr),
								right: Box::new(byte_offset),
							},
							ty: ptr_ty,
						}
					}
				};

				// Compute end: use provided expr, or array size, or slice len.
				// When both explicit bounds are given, spill `end` to a local and
				// emit a trap guard for the `from > to` case.
				// TODO: once proper panic infrastructure exists, replace the
				// `unreachable` trap with a formatted panic message and also add
				// the `to <= slice_len` check that is currently skipped.
				let end_val = match end {
					Some(e) => {
						let e_lowered =
							self.lower_expression(func_ctx, e, sink);
						if let Some(s_li) = start_local {
							// Spill `to` so it can be read by both the bounds
							// check and the length subtraction below.
							let e_temp = func_ctx.frame[0].locals.len() as u32;
							func_ctx.frame[0].locals.push(Local {
								ty: idx_ty,
								mutability: Mutability::Immutable,
							});
							sink.push(Expression {
								kind: ExprKind::LocalSet {
									scope_index: 0,
									local_index: e_temp,
									value: Box::new(e_lowered),
								},
								ty: Type::Unit,
							});

							// Allocate a synthetic block scope for the trap branch.
							let trap_scope = func_ctx.frame.len() as u32;
							func_ctx.frame.push(BlockScope {
								kind: tir::BlockKind::Block,
								parent: Some(
									func_ctx.current_scope_index as u32,
								),
								locals: vec![],
								result: Type::Never,
							});

							// if from > to { unreachable }
							sink.push(Expression {
								kind: ExprKind::IfElse {
									condition: Box::new(Expression {
										kind: ExprKind::Greater {
											left: Box::new(Expression {
												kind: ExprKind::LocalGet {
													scope_index: 0,
													local_index: s_li,
												},
												ty: idx_ty,
											}),
											right: Box::new(Expression {
												kind: ExprKind::LocalGet {
													scope_index: 0,
													local_index: e_temp,
												},
												ty: idx_ty,
											}),
										},
										ty: Type::Bool,
									}),
									then_block: Box::new(Expression {
										kind: ExprKind::Block {
											scope_index: trap_scope,
											expressions: Box::new([
												Expression {
													kind: ExprKind::Unreachable,
													ty: Type::Never,
												},
											]),
										},
										ty: Type::Never,
									}),
									else_block: None,
								},
								ty: Type::Unit,
							});

							Expression {
								kind: ExprKind::LocalGet {
									scope_index: 0,
									local_index: e_temp,
								},
								ty: idx_ty,
							}
						} else {
							e_lowered
						}
					}
					None => match static_size {
						Some(sz) => Expression {
							kind: ExprKind::Int { value: sz as i64 },
							ty: idx_ty,
						},
						None => opt_slice_len.unwrap(),
					},
				};

				// new_len = end - start (start is 0 when absent, skip sub)
				let new_len = match start_local {
					None => end_val,
					Some(li) => Expression {
						kind: ExprKind::Sub {
							left: Box::new(end_val),
							right: Box::new(Expression {
								kind: ExprKind::LocalGet {
									scope_index: 0,
									local_index: li,
								},
								ty: idx_ty,
							}),
						},
						ty: idx_ty,
					},
				};

				let result_ty = self.lower_type_index(expr.ty);
				Expression {
					kind: ExprKind::Aggregate {
						values: Box::new([offset_ptr, new_len]),
					},
					ty: result_ty,
				}
			}
			tir::ExprKind::Load { place } => {
				let (ptr, offset, memory) =
					self.lower_place_address(func_ctx, place, sink);
				Expression {
					kind: ExprKind::PointerLoad {
						pointer: Box::new(ptr),
						offset,
						memory,
					},
					ty: self.lower_type_index(place.ty),
				}
			}
			tir::ExprKind::AddressOf { place, .. } => {
				let (ptr, offset, _memory) =
					self.lower_place_address(func_ctx, place, sink);
				let ptr_ty = self.lower_type_index(expr.ty);
				if offset == 0 {
					ptr
				} else {
					Expression {
						kind: ExprKind::Add {
							left: Box::new(ptr),
							right: Box::new(Expression {
								kind: ExprKind::Int {
									value: offset as i64,
								},
								ty: ptr_ty,
							}),
						},
						ty: ptr_ty,
					}
				}
			}
			tir::ExprKind::Store { target, value } => {
				let (ptr, offset, memory) =
					self.lower_place_address(func_ctx, target, sink);
				let lowered_value =
					self.lower_expression(func_ctx, value, sink);
				Expression {
					kind: ExprKind::PointerStore {
						pointer: Box::new(ptr),
						value: Box::new(lowered_value),
						offset,
						memory,
					},
					ty: Type::Unit,
				}
			}
			tir::ExprKind::Assign { left, right } => Expression {
				kind: self.lower_assignment(func_ctx, left, right, sink),
				ty: Type::Unit,
			},
			tir::ExprKind::CompoundAssign {
				target,
				rhs,
				method_id,
			} => self
				.lower_compound_assign(func_ctx, target, rhs, *method_id, sink),
			tir::ExprKind::GenericCompoundAssign {
				target,
				rhs,
				abstract_method_id,
				self_type,
			} => {
				let method_id = self.resolve_generic_compound_method(
					*abstract_method_id,
					*self_type,
				);
				self.lower_compound_assign(
					func_ctx, target, rhs, method_id, sink,
				)
			}
			tir::ExprKind::CompoundStore {
				target,
				rhs,
				method_id,
			} => self
				.lower_compound_store(func_ctx, target, rhs, *method_id, sink),
			tir::ExprKind::GenericCompoundStore {
				target,
				rhs,
				abstract_method_id,
				self_type,
			} => {
				let method_id = self.resolve_generic_compound_method(
					*abstract_method_id,
					*self_type,
				);
				self.lower_compound_store(
					func_ctx, target, rhs, method_id, sink,
				)
			}
		}
	}

	fn lower_intrinsic(
		&mut self,
		func_ctx: &mut FunctionContext,
		name: SymbolU32,
		expr_ty: tir::TypeIndex,
		type_args: &[tir::TypeIndex],
		arguments: &[tir::Expression],
		sink: &mut Vec<Expression>,
	) -> Expression {
		let name_str = self.interner.resolve(name).unwrap();
		match name_str {
			"memory_grow" => {
				let raw_ty = type_args[0];
				let mem_ty = match &self.tir.types[raw_ty.as_usize()] {
					tir::Type::TypeParam { param_index, .. } => self
						.current_substitutions
						.get(*param_index as usize)
						.copied()
						.unwrap_or(raw_ty),
					_ => raw_ty,
				};
				let memory = match &self.tir.types[mem_ty.as_usize()] {
					tir::Type::Memory { id, .. } => *id,
					_ => unreachable!(
						"memory_grow type arg must be a Memory type"
					),
				};
				let delta = Box::new(self.lower_expression(
					func_ctx,
					&arguments[1],
					sink,
				));
				Expression {
					kind: ExprKind::MemoryGrow { memory, delta },
					ty: self.lower_type_index(expr_ty),
				}
			}
			"memory_size" => {
				let raw_ty = type_args[0];
				let mem_ty = match &self.tir.types[raw_ty.as_usize()] {
					tir::Type::TypeParam { param_index, .. } => self
						.current_substitutions
						.get(*param_index as usize)
						.copied()
						.unwrap_or(raw_ty),
					_ => raw_ty,
				};
				let memory = match &self.tir.types[mem_ty.as_usize()] {
					tir::Type::Memory { id, .. } => *id,
					_ => unreachable!(
						"memory_size type arg must be a Memory type"
					),
				};
				Expression {
					kind: ExprKind::MemorySize { memory },
					ty: self.lower_type_index(expr_ty),
				}
			}
			"slice_len" => {
				let result_ty = self.lower_type_index(expr_ty);
				let slice_arg = &arguments[0];
				match &slice_arg.kind {
					tir::ExprKind::Local {
						scope_index,
						local_index,
					} => Expression {
						kind: ExprKind::AggregateGet {
							scope_index: *scope_index,
							local_index: *local_index,
							value_index: 1,
						},
						ty: result_ty,
					},
					_ => {
						let slice_ty = self.lower_type_index(slice_arg.ty);
						let lowered =
							self.lower_expression(func_ctx, slice_arg, sink);
						let temp_idx = func_ctx.frame[0].locals.len() as u32;
						func_ctx.frame[0].locals.push(Local {
							ty: slice_ty,
							mutability: Mutability::Immutable,
						});
						sink.push(Expression {
							kind: ExprKind::LocalSet {
								scope_index: 0,
								local_index: temp_idx,
								value: Box::new(lowered),
							},
							ty: Type::Unit,
						});
						Expression {
							kind: ExprKind::AggregateGet {
								scope_index: 0,
								local_index: temp_idx,
								value_index: 1,
							},
							ty: result_ty,
						}
					}
				}
			}
			"slice_ptr" => {
				let result_ty = self.lower_type_index(expr_ty);
				let slice_arg = &arguments[0];
				match &slice_arg.kind {
					tir::ExprKind::Local {
						scope_index,
						local_index,
					} => Expression {
						kind: ExprKind::AggregateGet {
							scope_index: *scope_index,
							local_index: *local_index,
							value_index: 0,
						},
						ty: result_ty,
					},
					_ => {
						let slice_ty = self.lower_type_index(slice_arg.ty);
						let lowered =
							self.lower_expression(func_ctx, slice_arg, sink);
						let temp_idx = func_ctx.frame[0].locals.len() as u32;
						func_ctx.frame[0].locals.push(Local {
							ty: slice_ty,
							mutability: Mutability::Immutable,
						});
						sink.push(Expression {
							kind: ExprKind::LocalSet {
								scope_index: 0,
								local_index: temp_idx,
								value: Box::new(lowered),
							},
							ty: Type::Unit,
						});
						Expression {
							kind: ExprKind::AggregateGet {
								scope_index: 0,
								local_index: temp_idx,
								value_index: 0,
							},
							ty: result_ty,
						}
					}
				}
			}
			"slice_from_parts" => {
				let data = self.lower_expression(func_ctx, &arguments[0], sink);
				let len = self.lower_expression(func_ctx, &arguments[1], sink);
				let result_ty = self.lower_type_index(expr_ty);
				Expression {
					kind: ExprKind::Aggregate {
						values: Box::new([data, len]),
					},
					ty: result_ty,
				}
			}
			"size_of" => {
				let raw_ty = type_args[0];
				let concrete_t = match &self.tir.types[raw_ty.as_usize()] {
					tir::Type::TypeParam { param_index, .. } => self
						.current_substitutions
						.get(*param_index as usize)
						.copied()
						.unwrap_or(raw_ty),
					_ => raw_ty,
				};
				let layout = self.compute_layout(concrete_t);
				Expression {
					kind: ExprKind::Int {
						value: layout.size as i64,
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"align_of" => {
				let raw_ty = type_args[0];
				let concrete_t = match &self.tir.types[raw_ty.as_usize()] {
					tir::Type::TypeParam { param_index, .. } => self
						.current_substitutions
						.get(*param_index as usize)
						.copied()
						.unwrap_or(raw_ty),
					_ => raw_ty,
				};
				let layout = self.compute_layout(concrete_t);
				Expression {
					kind: ExprKind::Int {
						value: layout.align as i64,
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"f32_sqrt" | "f64_sqrt" => Expression {
				kind: ExprKind::Sqrt {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_abs" | "f64_abs" => Expression {
				kind: ExprKind::Abs {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_floor" | "f64_floor" => Expression {
				kind: ExprKind::Floor {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_ceil" | "f64_ceil" => Expression {
				kind: ExprKind::Ceil {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_trunc" | "f64_trunc" => Expression {
				kind: ExprKind::Trunc {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_nearest" | "f64_nearest" => Expression {
				kind: ExprKind::Nearest {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_min" | "f64_min" => Expression {
				kind: ExprKind::Min {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_max" | "f64_max" => Expression {
				kind: ExprKind::Max {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_copysign" | "f64_copysign" => Expression {
				kind: ExprKind::Copysign {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_neg" | "i64_neg" | "f32_neg" | "f64_neg" => Expression {
				kind: ExprKind::Neg {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitnot" | "i64_bitnot" => Expression {
				kind: ExprKind::BitNot {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_add" | "i64_add" | "f32_add" | "f64_add" => Expression {
				kind: ExprKind::Add {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_sub" | "i64_sub" | "f32_sub" | "f64_sub" => Expression {
				kind: ExprKind::Sub {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_mul" | "i64_mul" | "f32_mul" | "f64_mul" => Expression {
				kind: ExprKind::Mul {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_div" | "u32_div" | "i64_div" | "u64_div" | "f32_div"
			| "f64_div" => Expression {
				kind: ExprKind::Div {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_rem" | "u32_rem" | "i64_rem" | "u64_rem" => Expression {
				kind: ExprKind::Rem {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitand" | "i64_bitand" => Expression {
				kind: ExprKind::BitAnd {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitor" | "i64_bitor" => Expression {
				kind: ExprKind::BitOr {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitxor" | "i64_bitxor" => Expression {
				kind: ExprKind::BitXor {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_shl" | "i64_shl" => Expression {
				kind: ExprKind::LeftShift {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_shr" | "u32_shr" | "i64_shr" | "u64_shr" => Expression {
				kind: ExprKind::RightShift {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_extend_i32" => Expression {
				kind: ExprKind::I64ExtendI32S {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u64_extend_u32" => Expression {
				kind: ExprKind::I64ExtendI32U {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_wrap_i64" => Expression {
				kind: ExprKind::I32WrapI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_i32" => Expression {
				kind: ExprKind::F32ConvertI32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_u32" => Expression {
				kind: ExprKind::F32ConvertU32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_i64" => Expression {
				kind: ExprKind::F32ConvertI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_u64" => Expression {
				kind: ExprKind::F32ConvertU64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_i32" => Expression {
				kind: ExprKind::F64ConvertI32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_u32" => Expression {
				kind: ExprKind::F64ConvertU32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_i64" => Expression {
				kind: ExprKind::F64ConvertI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_u64" => Expression {
				kind: ExprKind::F64ConvertU64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_trunc_f32" => Expression {
				kind: ExprKind::I32TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u32_trunc_f32" => Expression {
				kind: ExprKind::U32TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_trunc_f64" => Expression {
				kind: ExprKind::I32TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u32_trunc_f64" => Expression {
				kind: ExprKind::U32TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_trunc_f32" => Expression {
				kind: ExprKind::I64TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u64_trunc_f32" => Expression {
				kind: ExprKind::U64TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_trunc_f64" => Expression {
				kind: ExprKind::I64TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u64_trunc_f64" => Expression {
				kind: ExprKind::U64TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_promote_f32" => Expression {
				kind: ExprKind::F64PromoteF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_demote_f64" => Expression {
				kind: ExprKind::F32DemoteF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_reinterpret_f32" => Expression {
				kind: ExprKind::I32ReinterpretF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_reinterpret_i32" => Expression {
				kind: ExprKind::F32ReinterpretI32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_reinterpret_f64" => Expression {
				kind: ExprKind::I64ReinterpretF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_reinterpret_i64" => Expression {
				kind: ExprKind::F64ReinterpretI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"memory_fill" => {
				let raw_ty = type_args[0];
				let mem_ty = match &self.tir.types[raw_ty.as_usize()] {
					tir::Type::TypeParam { param_index, .. } => self
						.current_substitutions
						.get(*param_index as usize)
						.copied()
						.unwrap_or(raw_ty),
					_ => raw_ty,
				};
				let memory = match &self.tir.types[mem_ty.as_usize()] {
					tir::Type::Memory { id, .. } => *id,
					_ => unreachable!(
						"memory_fill type arg must be a Memory type"
					),
				};
				let dst = Box::new(self.lower_expression(
					func_ctx,
					&arguments[0],
					sink,
				));
				let val = Box::new(self.lower_expression(
					func_ctx,
					&arguments[1],
					sink,
				));
				let len = Box::new(self.lower_expression(
					func_ctx,
					&arguments[2],
					sink,
				));
				Expression {
					kind: ExprKind::MemoryFill {
						memory,
						dst,
						val,
						len,
					},
					ty: Type::Unit,
				}
			}
			"memory_copy" => {
				let resolve_memory = |raw_ty: tir::TypeIndex| {
					let mem_ty = match &self.tir.types[raw_ty.as_usize()] {
						tir::Type::TypeParam { param_index, .. } => self
							.current_substitutions
							.get(*param_index as usize)
							.copied()
							.unwrap_or(raw_ty),
						_ => raw_ty,
					};
					match &self.tir.types[mem_ty.as_usize()] {
						tir::Type::Memory { id, .. } => *id,
						_ => unreachable!(
							"memory_copy type arg must be a Memory type"
						),
					}
				};
				let src_memory = resolve_memory(type_args[1]);
				let dst_memory = resolve_memory(type_args[2]);
				let dst = Box::new(self.lower_expression(
					func_ctx,
					&arguments[0],
					sink,
				));
				let src = Box::new(self.lower_expression(
					func_ctx,
					&arguments[1],
					sink,
				));
				let len = Box::new(self.lower_expression(
					func_ctx,
					&arguments[2],
					sink,
				));
				Expression {
					kind: ExprKind::MemoryCopy {
						dst_memory,
						src_memory,
						dst,
						src,
						len,
					},
					ty: Type::Unit,
				}
			}
			name => unreachable!("cannot lower unknown intrinsic `{name}`"),
		}
	}

	/// Compute the address of a place, returning `(base_ptr, static_byte_offset, memory_id)`.
	///
	/// The caller emits a `PointerLoad`/`PointerStore` using the returned triple.
	///
	/// - `Deref { pointer }` — evaluate the pointer expression; offset = 0.
	/// - `Field { object, member }` — recurse on the parent place and add the
	///   field's static byte offset.
	/// - `Index { object, index }` — delegate to `lower_index_address`; the
	///   returned pointer already encodes runtime index arithmetic when needed.
	fn lower_place_address(
		&mut self,
		func_ctx: &mut FunctionContext,
		place: &tir::Place,
		sink: &mut Vec<Expression>,
	) -> (Expression, u32, ast::DefId) {
		let memory_id = self.resolve_memory_id(place.memory);
		match &place.kind {
			tir::PlaceKind::Deref { pointer } => {
				let ptr = self.lower_expression(func_ctx, pointer, sink);
				(ptr, 0, memory_id)
			}
			tir::PlaceKind::Field { object, member } => {
				let (base_ptr, base_offset, memory_id) =
					self.lower_place_address(func_ctx, object, sink);
				let (struct_index, args) =
					match &self.tir.types[object.ty.as_usize()] {
						tir::Type::Struct { struct_index, args } => {
							(*struct_index, &args[..])
						}
						_ => unreachable!(
							"PlaceKind::Field: parent place must be a struct"
						),
					};
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				let decl_index = self.tir.structs[struct_index as usize].lookup
					[&member.inner];
				let phys_index = self.aggregates[aggregate_index as usize]
					.decl_to_phys[decl_index] as usize;
				let field_offset = self.aggregates[aggregate_index as usize]
					.offsets[phys_index];
				(base_ptr, base_offset + field_offset, memory_id)
			}
			tir::PlaceKind::Index { object, index } => {
				let elem_ty = place.ty;
				match self
					.lower_index_address(func_ctx, object, index, elem_ty, sink)
				{
					IndexAddress::Constant { ptr, byte_offset } => {
						(ptr, byte_offset, memory_id)
					}
					IndexAddress::Dynamic(ptr) => (ptr, 0, memory_id),
				}
			}
		}
	}

	fn lower_assignment(
		&mut self,
		func_ctx: &mut FunctionContext,
		left: &tir::Expression,
		right: &tir::Expression,
		sink: &mut Vec<Expression>,
	) -> ExprKind {
		if let tir::ExprKind::Placeholder = &left.kind {
			// `_ = expr`: evaluate rhs for side effects, discard the value.
			return ExprKind::Drop {
				value: Box::new(self.lower_expression(func_ctx, right, sink)),
			};
		}
		let value = self.lower_expression(func_ctx, right, sink);
		self.lower_assign_target(left, value)
	}

	/// Builds the `LocalSet`/`GlobalSet`/`AggregateSet` that writes `value`
	/// to `target` (a `Local`/`Global`/`FieldAccess`). Shared by plain
	/// assignment (`lower_assignment`, `value` = the lowered rhs) and
	/// compound assignment (`lower_compound_assign`, `value` = the resolved
	/// operator method's `Call`) — `target`'s own indices/field-offset are
	/// pure metadata lookups, never requiring further lowering, so both
	/// callers can share this exactly.
	fn lower_assign_target(
		&mut self,
		target: &tir::Expression,
		value: Expression,
	) -> ExprKind {
		match &target.kind {
			tir::ExprKind::Local {
				scope_index,
				local_index,
			} => ExprKind::LocalSet {
				scope_index: *scope_index,
				local_index: *local_index,
				value: Box::new(value),
			},
			tir::ExprKind::Global { id } => ExprKind::GlobalSet {
				id: *id,
				value: Box::new(value),
			},
			tir::ExprKind::FieldAccess {
				object,
				field: member,
			} => {
				let (struct_index, args) =
					match &self.tir.types[object.ty.as_usize()] {
						tir::Type::Struct { struct_index, args } => {
							(*struct_index, args.clone())
						}
						_ => unreachable!("ObjectAccess on non-struct type"),
					};
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				let decl_index = self.tir.structs[struct_index as usize].lookup
					[&member.inner];
				let phys_index = self.aggregates[aggregate_index as usize]
					.decl_to_phys[decl_index] as usize;
				let tir::ExprKind::Local {
					scope_index,
					local_index,
				} = &object.kind
				else {
					unreachable!(
						"ObjectAccess assignment: object must be Local after place/value split"
					)
				};
				ExprKind::AggregateSet {
					scope_index: *scope_index,
					local_index: *local_index,
					value_index: phys_index as u32,
					value: Box::new(value),
				}
			}
			_ => unreachable!(
				"assignment target must be Local/Global/FieldAccess"
			),
		}
	}

	/// Builds the `Call` to `method_id` a compound-assignment operator
	/// resolves to — `current_value`/`rhs` are its two arguments (mirrors
	/// `MethodCall`'s lowering), and the call's own MIR type is
	/// `current_value`'s type, since every operator trait method returns
	/// `Self`. Records the call-graph edge so the inlining pass considers
	/// this call a candidate exactly like an ordinary `MethodCall` would —
	/// primitive impls (`impl Add for i32`, `#[inline]`) only collapse back
	/// to a native op if this edge exists.
	fn build_compound_operator_call(
		&mut self,
		method_id: ast::DefId,
		current_value: Expression,
		rhs: Expression,
	) -> Expression {
		self.record_call_edge(method_id);
		let ty = current_value.ty;
		let tir_idx = self.tir.expect_function_index(method_id);
		let callee_sig_idx = self.intern_tir_function_type(
			self.tir.functions[tir_idx as usize].signature_index,
		);
		Expression {
			kind: ExprKind::Call {
				callee: Box::new(Expression {
					kind: ExprKind::Function { id: method_id },
					ty: Type::Function {
						signature_index: callee_sig_idx,
					},
				}),
				arguments: Box::new([current_value, rhs]),
			},
			ty,
		}
	}

	/// Resolves `GenericCompoundAssign`/`GenericCompoundStore`'s abstract
	/// trait method to a concrete one now that `self_type` is guaranteed
	/// concrete (the surrounding function has already been monomorphized
	/// for this instantiation) — exactly `GenericMethodCall`'s
	/// abstract-method branch, just factored out since compound assignment
	/// has two `Place`/non-`Place` shapes that both need it.
	fn resolve_generic_compound_method(
		&mut self,
		abstract_method_id: ast::DefId,
		self_type: tir::TypeIndex,
	) -> ast::DefId {
		let concrete_self = self.resolve_tir_type(self_type);
		let tir_idx = self.tir.expect_function_index(abstract_method_id);
		let tir_func = &self.tir.functions[tir_idx as usize];
		let method_name = tir_func.name.inner;
		let trait_index = match tir_func.parent {
			Some(tir::ItemParent::Trait(idx)) => idx,
			_ => unreachable!(
				"abstract trait method must be parented by its trait"
			),
		};
		let (trait_impl_idx, impl_type_args) = self
			.tir
			.find_trait_impl(concrete_self, trait_index)
			.expect("no impl found for abstract trait method");
		let impl_func_idx = self.tir.trait_impls[trait_impl_idx as usize]
			.members
			.get(&method_name)
			.map(|entry| match entry {
				tir::ImplEntry::Method(idx) => *idx,
				_ => unreachable!(),
			})
			.expect("no impl found for abstract trait method");
		let impl_func_id = self.tir.functions[impl_func_idx as usize].id;
		if impl_type_args.is_empty() {
			impl_func_id
		} else {
			self.mono_registry
				.get_or_insert(impl_func_id, impl_type_args)
		}
	}

	/// `CompoundAssign`/`GenericCompoundAssign` (target is `Local`/`Global`/
	/// `FieldAccess`): read the current value, call the resolved operator
	/// method, write the result back — `target`'s indices are safe to
	/// reference twice (`Copy` metadata, not a computation), so no
	/// once-only-lowering concern here, unlike `lower_compound_store`.
	fn lower_compound_assign(
		&mut self,
		func_ctx: &mut FunctionContext,
		target: &tir::Expression,
		rhs: &tir::Expression,
		method_id: ast::DefId,
		sink: &mut Vec<Expression>,
	) -> Expression {
		let current_value = self.lower_expression(func_ctx, target, sink);
		let lowered_rhs = self.lower_expression(func_ctx, rhs, sink);
		let call = self.build_compound_operator_call(
			method_id,
			current_value,
			lowered_rhs,
		);
		Expression {
			kind: self.lower_assign_target(target, call),
			ty: Type::Unit,
		}
	}

	/// `CompoundStore`/`GenericCompoundStore` (target is a `Place`): the
	/// careful one. Computes `target`'s address exactly once and sinks it
	/// into a temp local, reused via `LocalGet` for both the old-value read
	/// and the final store — fixes the pre-existing double-evaluation bug
	/// where e.g. `arr[i()] += 1` called `i()` twice (once per
	/// `lower_place_address` call). Mirrors the temp-local idiom already
	/// used elsewhere in this file (e.g. `lower_intrinsic`'s `slice_len`/
	/// `slice_ptr` arms).
	fn lower_compound_store(
		&mut self,
		func_ctx: &mut FunctionContext,
		target: &tir::Place,
		rhs: &tir::Expression,
		method_id: ast::DefId,
		sink: &mut Vec<Expression>,
	) -> Expression {
		let (ptr, offset, memory) =
			self.lower_place_address(func_ctx, target, sink);
		let ptr_ty = ptr.ty;
		let temp_idx = func_ctx.frame[0].locals.len() as u32;
		func_ctx.frame[0].locals.push(Local {
			ty: ptr_ty,
			mutability: Mutability::Immutable,
		});
		sink.push(Expression {
			kind: ExprKind::LocalSet {
				scope_index: 0,
				local_index: temp_idx,
				value: Box::new(ptr),
			},
			ty: Type::Unit,
		});

		let current_value = Expression {
			kind: ExprKind::PointerLoad {
				pointer: Box::new(Expression {
					kind: ExprKind::LocalGet {
						scope_index: 0,
						local_index: temp_idx,
					},
					ty: ptr_ty,
				}),
				offset,
				memory,
			},
			ty: self.lower_type_index(target.ty),
		};
		let lowered_rhs = self.lower_expression(func_ctx, rhs, sink);
		let call = self.build_compound_operator_call(
			method_id,
			current_value,
			lowered_rhs,
		);
		Expression {
			kind: ExprKind::PointerStore {
				pointer: Box::new(Expression {
					kind: ExprKind::LocalGet {
						scope_index: 0,
						local_index: temp_idx,
					},
					ty: ptr_ty,
				}),
				value: Box::new(call),
				offset,
				memory,
			},
			ty: Type::Unit,
		}
	}
}
