//! Backend form of a checked program: monomorphic functions over Wasm-shaped
//! values, each function's expressions stored as an arena (`body.rs`,
//! `notes/mir-arena.md`).

use string_interner::symbol::SymbolU32;

use crate::index::index_newtype;

// Only the pieces MIR still owns are in the module graph. The pre-transition
// lowering pass (`legacy_lowering.rs`) and its helpers (`builder/`,
// `types.rs`, `mono.rs`, `static_data.rs`, `tests.rs`) stay on
// disk as reference but are deliberately not compiled: they target the
// removed `tir::TIR` API.
pub mod body;
pub mod inline;
#[allow(dead_code)]
pub(crate) mod layout;
#[allow(dead_code)]
mod signatures;

pub use body::{
	BinaryOp, Body, Case, CaseList, CompareOp, ExprId, ExprKind, ExprList,
	LabelId, UnaryOp,
};

index_newtype!(
	/// Backend identity of one MIR function *instance*: its index in
	/// [`MIR::functions`] and [`MIR::function_flags`].
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
	/// Index into [`MIR::static_entries`].
	StaticEntryId
);
index_newtype!(
	/// Flat, function-wide index into `Function::locals`, distinct from
	/// `tir::LocalIndex` (which is per-scope).
	LocalIndex
);
index_newtype!(
	/// Index into [`MIR::imports`].
	ImportIdx
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
	/// An address. Which memory it points into is checked in TIR and named
	/// by every node that reads or writes through it, so the type holds only
	/// the address width: no module item id lives in a type.
	Pointer {
		kind: MemoryKind,
	},
	Aggregate {
		aggregate_index: AggregateIndex,
	},
	Function {
		signature_index: SignatureIndex,
	},
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

index_newtype!(
	/// Index into an aggregate's flattened scalar (Wasm-value) list, in
	/// **declaration pre-order**.
	///
	/// One scalar is one WebAssembly value: one signature slot, one local, one
	/// stack entry. Source fields exist only in TIR; lowering translates
	/// their projections into scalar ranges.
	ScalarIndex
);

/// A contiguous selection in a flat value pack, including an empty selection.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct ScalarRange {
	pub start: ScalarIndex,
	pub len: u32,
}

impl ScalarRange {
	pub fn new(start: u32, len: u32) -> Self {
		Self {
			start: ScalarIndex::new(start),
			len,
		}
	}

	pub fn indices(self) -> std::ops::Range<usize> {
		let start = usize::from(self.start);
		start..start + self.len as usize
	}
}

/// An owned, nonempty flat value representation. No entry may be another
/// aggregate, `Unit`, or `Never`. Source structure belongs to TIR only.
#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Aggregate {
	pub scalars: Box<[ValueType]>,
	/// Some stack values have no linear-memory representation. This is
	/// copied from TIR when available, never inferred from the slot types.
	pub memory: Option<AggregateMemory>,
}

/// Memory attributes paired with a flat pack's slots, in the same order.
#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct AggregateMemory {
	pub layout: Layout,
	pub offsets: Box<[u32]>,
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
	pub kind: MemoryKind,
	/// Counts of 64 KiB pages, as `#[memory_limits]` writes them (checked);
	/// `None` for a bound left out, and both for an imported memory.
	/// Codegen raises the minimum to the pages the static data takes.
	pub min_pages: Option<u64>,
	pub max_pages: Option<u64>,
	/// An imported memory has nothing a defined one lacks: its kind and
	/// limits are both.
	pub origin: Origin<()>,
}

/// Read-only bytes placed in a memory's data segment: a literal's, or data
/// a constant or a global points into. Codegen lays out the entries
/// something reaches and gives each its address.
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(PartialEq, Eq, Hash)]
pub struct StaticEntry {
	pub bytes: Box<[u8]>,
	pub align: u32,
	/// The memory whose data segment this entry is placed in.
	pub memory: MemoryId,
	/// The addresses written in `bytes`, sorted by offset.
	pub relocations: Box<[Relocation]>,
}

/// An address inside a static entry's bytes. The bytes at `offset`, as
/// wide as the addresses of the memory `target` is in, hold an offset from
/// it; codegen adds `target`'s address to them.
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Relocation {
	pub offset: u32,
	pub target: AddressTarget,
}

/// What an address codegen resolves points at.
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum AddressTarget {
	/// A static entry, in its memory.
	Entry(StaticEntryId),
	/// The address right after a memory's static data (`Memory::DATA_END`).
	DataEnd(MemoryId),
}

/// A checked program lowered to backend form.
///
/// Identity is backend-local: [`FunctionId`], [`GlobalId`] and [`MemoryId`] are
/// assigned by lowering and are neither source indices nor Wasm indices. The
/// maps from checked source identity (`FunctionIdx`, `GlobalIdx`, …) to these
/// IDs, and the monomorphization worklist that mints them, belong to the
/// lowerer — MIR only ever stores the result. Codegen re-derives Wasm indices
/// from these IDs, imports first.
pub struct MIR {
	/// Indexed by [`FunctionId`].
	pub functions: Vec<Function>,
	/// What callers and the backend may do with each function, beside its
	/// body; indexed by [`FunctionId`], as `functions` is.
	pub function_flags: Vec<FunctionFlags>,
	pub signatures: Vec<FunctionSignature>,
	pub globals: Vec<Global>,
	pub exports: Vec<Export>,
	/// What the host provides, one entry per imported item; indexed by
	/// [`ImportIdx`].
	pub imports: Vec<Import>,
	pub memories: Vec<MemoryInfo>,
	pub aggregates: Box<[Aggregate]>,
	pub static_entries: Vec<StaticEntry>,
	/// The synthetic start function that assigns all user-defined globals at
	/// module instantiation time, if any globals are declared.
	pub start_function: Option<FunctionId>,
}

/// Attributes of a function that its callers and the backend read, a byte
/// per function in [`MIR::function_flags`].
#[derive(Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct FunctionFlags(u8);

impl FunctionFlags {
	/// `#[inline]`: callers take its body in place of a call.
	pub const INLINE: Self = Self(1 << 0);

	pub const fn empty() -> Self {
		Self(0)
	}

	pub const fn contains(self, other: Self) -> bool {
		self.0 & other.0 == other.0
	}

	pub fn insert(&mut self, other: Self) {
		self.0 |= other.0;
	}
}

/// A module-level item an import or an export names.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum Item {
	Function(FunctionId),
	Global(GlobalId),
	Memory(MemoryId),
}

/// One item the host provides, under `module`.`name`.
///
/// Wasm does not require import names to be unique, and neither does MIR:
/// two imports may share both names, and even their external type. Each is
/// its own item here; codegen gives entries with the same names and external
/// type one Wasm import.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Import {
	pub module: SymbolU32,
	pub name: SymbolU32,
	/// The item this entry provides, whose `origin` is `Imported` of this
	/// entry.
	pub item: Item,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct Export {
	pub name: SymbolU32,
	pub item: Item,
}

/// Whether an item is provided by the host or defined by the module, and what
/// a definition has that an import does not.
#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum Origin<D> {
	/// Its entry in [`MIR::imports`], which names the item back.
	Imported(ImportIdx),
	Defined(D),
}

impl<D> Origin<D> {
	pub fn import(&self) -> Option<ImportIdx> {
		match self {
			Self::Imported(import) => Some(*import),
			Self::Defined(_) => None,
		}
	}

	pub fn defined(&self) -> Option<&D> {
		match self {
			Self::Defined(definition) => Some(definition),
			Self::Imported(_) => None,
		}
	}
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

#[derive(Clone)]
pub struct Function {
	pub signature_index: SignatureIndex,
	pub origin: Origin<Code>,
}

impl Function {
	/// The function's code, if the module defines it.
	pub fn code(&self) -> Option<&Code> {
		self.origin.defined()
	}

	pub fn code_mut(&mut self) -> Option<&mut Code> {
		match &mut self.origin {
			Origin::Defined(code) => Some(code),
			Origin::Imported(_) => None,
		}
	}
}

/// What a defined function has that an imported one does not.
#[derive(Clone)]
pub struct Code {
	/// Every local the function owns, in one flat, function-wide space, its
	/// parameters first; temporaries are appended like any other local.
	pub locals: Vec<Local>,
	/// How many labels the body uses; every [`LabelId`] is below it.
	pub label_count: u32,
	pub body: Body,
	pub root: ExprId,
}

impl Code {
	/// The static data entries (`MIR::static_entries`) the body points at.
	pub fn static_data(&self) -> impl Iterator<Item = StaticEntryId> + '_ {
		self.body.kinds().iter().filter_map(|kind| match *kind {
			ExprKind::StaticPointer { entry, .. } => Some(entry),
			_ => None,
		})
	}

	/// The functions the body calls directly, once per call.
	pub fn callees(&self) -> impl Iterator<Item = FunctionId> + '_ {
		self.body.kinds().iter().filter_map(|kind| match *kind {
			ExprKind::Call { function, .. } => Some(function),
			_ => None,
		})
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy)]
pub enum ConstInit {
	Int(i64),
	Float(f64),
	/// The address `offset` bytes into a static entry.
	Static {
		entry: StaticEntryId,
		offset: u32,
	},
	/// The address right after a memory's static data.
	DataEnd {
		memory: MemoryId,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct Global {
	pub id: GlobalId,
	pub ty: ValueType,
	pub mutability: Mutability,
	/// A defined global's init expression. Mutable globals use zero here and
	/// are assigned at runtime by the start function. Immutable globals carry
	/// their literal value directly.
	pub origin: Origin<ConstInit>,
}

/// Memory layout of a type: size in bytes and required alignment in bytes.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Layout {
	pub size: u32,
	pub align: u32,
}

impl MIR {
	pub fn function(&self, id: FunctionId) -> &Function {
		&self.functions[usize::from(id)]
	}

	/// `id`'s code. Panics on an imported function: only a pass that already
	/// knows it reads a definition asks this way.
	pub fn code(&self, id: FunctionId) -> &Code {
		self.function(id)
			.code()
			.expect("an imported function has no code")
	}

	pub fn global(&self, id: GlobalId) -> &Global {
		let global = &self.globals[usize::from(id)];
		debug_assert!(global.id == id, "a global's id is its index");
		global
	}

	pub fn memory(&self, id: MemoryId) -> &MemoryInfo {
		let memory = &self.memories[usize::from(id)];
		debug_assert!(memory.id == id, "a memory's id is its index");
		memory
	}

	/// The import entry providing `item`, if the host provides it.
	pub fn import_of(&self, item: Item) -> Option<ImportIdx> {
		match item {
			Item::Function(id) => self.function(id).origin.import(),
			Item::Global(id) => self.global(id).origin.import(),
			Item::Memory(id) => self.memory(id).origin.import(),
		}
	}

	/// Check that the import table and the items agree: every entry's item
	/// is `Imported` of that entry, and every `Imported` item's entry names
	/// it. Returns the first entry that does not.
	pub fn verify_imports(&self) -> Result<(), ImportIdx> {
		for (index, import) in self.imports.iter().enumerate() {
			let index = ImportIdx::new(index as u32);
			if self.import_of(import.item) != Some(index) {
				return Err(index);
			}
		}
		let items = (self
			.functions_with_ids()
			.map(|(id, _)| Item::Function(id)))
		.chain(self.globals.iter().map(|global| Item::Global(global.id)))
		.chain(self.memories.iter().map(|memory| Item::Memory(memory.id)));
		for item in items {
			if let Some(import) = self.import_of(item)
				&& self
					.imports
					.get(usize::from(import))
					.is_none_or(|entry| entry.item != item)
			{
				return Err(import);
			}
		}
		Ok(())
	}

	pub fn flags(&self, id: FunctionId) -> FunctionFlags {
		self.function_flags[usize::from(id)]
	}

	/// The functions with their ids, in id order.
	pub fn functions_with_ids(
		&self,
	) -> impl Iterator<Item = (FunctionId, &Function)> {
		self.functions
			.iter()
			.enumerate()
			.map(|(index, function)| (FunctionId::new(index as u32), function))
	}

	/// The aggregate `index` refers to.
	#[inline]
	pub fn aggregate(&self, index: AggregateIndex) -> &Aggregate {
		&self.aggregates[usize::from(index)]
	}
}
