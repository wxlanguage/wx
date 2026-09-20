//! Type identity: the structurally hash-consed `Type` arena every resolved
//! signature and expression points into.
//!
//! Deliberately independent of `defs`/`signatures`' resolution machinery —
//! this module only answers "given a `Type`, what `TypeIndex` names it",
//! never "what type does this path/expression have". It depends on `defs`
//! for `TraitIndex` (an associated-type projection names the trait that
//! declares it) but nothing here calls into name resolution, and nothing in
//! `defs` depends back on this module — see `tir/defs.rs`'s own doc comment
//! for why that direction has to stay one-way.
//!
//! A type parameter's owner is a bare `ast::DefId` rather than a dedicated
//! `TypeParamOwner` enum (the old builder's shape, one variant per arena a
//! generic-bearing item could live in): every such item — function, struct,
//! type alias, trait, inherent impl, trait impl — already carries its own
//! `DefId`, so a separate enum would only be re-deriving a distinction the
//! id space already makes for free.

use std::collections::HashMap;

use crate::ast::DefId;
use crate::index::index_newtype;
use string_interner::symbol::SymbolU32;

use super::defs::TraitIndex;

index_newtype!(TypeIndex);
// Which arena `Type::Struct`/`Type::Enum` point into — declared here rather
// than in `signatures.rs`, so this module doesn't have to name anything
// signature-storage owns. `signatures::SignatureRegistry` indexes its own
// `structs`/`enums` vecs with these same types.
index_newtype!(StructIndex);
index_newtype!(EnumIndex);

/// A function type's parameters and result packed into one interned slice —
/// `items[..params_count]` are the parameters, `items[params_count]` is the
/// result. One `Vec` rather than two separate `Box<[TypeIndex]>` fields
/// halves the allocations a `Type::Function` needs and keeps `Type`'s
/// `Hash`/`Eq` (which drive interning) from having to combine two slices.
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct FunctionSignature {
	items: Box<[TypeIndex]>,
	params_count: u32,
}

impl FunctionSignature {
	pub fn new(params: &[TypeIndex], result: TypeIndex) -> Self {
		let mut items = Vec::with_capacity(params.len() + 1);
		items.extend_from_slice(params);
		items.push(result);
		Self {
			items: items.into_boxed_slice(),
			params_count: u32::try_from(params.len())
				.expect("a function signature exceeded u32 param capacity"),
		}
	}

	pub fn params(&self) -> &[TypeIndex] {
		&self.items[..self.params_count as usize]
	}

	pub fn result(&self) -> TypeIndex {
		self.items[self.params_count as usize]
	}
}

#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, PartialEq, Eq, Hash)]
// `TypeParam`/`AssociatedType`/`AssocTypeProjection` echo the enum's own
// name because "type" is the domain term (a type parameter, an associated
// type), not accidental repetition — renaming to `Param`/`Associated` would
// read worse at every call site (`Type::Param` loses the "type" a reader
// needs to parse `owner`/`param_index` at a glance).
#[allow(clippy::enum_variant_names)]
pub enum Type {
	Error,
	/// A type inference placeholder — written `_` in source, or injected
	/// internally when a generic type argument cannot yet be determined.
	/// Must never reach MIR or codegen; the TIR checker reports an error
	/// whenever `Infer` survives past the call site that created it.
	Infer,
	Unit,
	Never,
	Integer,
	Float,
	U8,
	I8,
	U16,
	I16,
	U32,
	I32,
	U64,
	I64,
	F32,
	F64,
	Bool,
	Char,
	Tuple {
		elements: Box<[TypeIndex]>,
	},
	Struct {
		struct_index: StructIndex,
		/// Encodes three states via length: non-generic struct (always
		/// empty), generic and not yet instantiated (empty), generic and
		/// instantiated (one entry per type param, e.g. `Vec<i32, u8>` →
		/// `[i32_idx, u8_idx]`).
		args: Box<[TypeIndex]>,
	},
	Function {
		signature: FunctionSignature,
	},
	/// Named function reference before coercion to a fn pointer. Encodes
	/// three states via length, same convention as `Struct::args`.
	FunctionItem {
		id: DefId,
		type_args: Box<[TypeIndex]>,
	},
	Pointer {
		to: TypeIndex,
		memory: TypeIndex,
		ownership: crate::ast::Ownership,
	},
	Array {
		of: TypeIndex,
		size: u32,
		memory: TypeIndex,
		ownership: crate::ast::Ownership,
	},
	Slice {
		of: TypeIndex,
		memory: TypeIndex,
		ownership: crate::ast::Ownership,
	},
	Enum {
		enum_index: EnumIndex,
	},
	Memory {
		id: DefId,
		/// `TypeIndex::U32` or `TypeIndex::U64` — the memory's index type.
		size: TypeIndex,
	},
	/// One occurrence of a generic parameter declared by `owner` — every use
	/// of the same parameter across `owner`'s signature/body shares one
	/// interned instance. `param_index` is absolute across `owner`'s full
	/// visible chain: a method's own parameters start counting only after
	/// its parent impl/trait block's, mirroring how `signatures::GenericParam`
	/// slices compose (see that module's doc comment).
	TypeParam {
		owner: DefId,
		param_index: u32,
	},
	/// `M::Size` — opaque until monomorphization substitutes `M`.
	AssociatedType {
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
	},
	/// `M::Size` or `A::M::Size` in a signature: a projection from a base
	/// type (a `TypeParam` or another `AssocTypeProjection`), resolved once
	/// the base is substituted with a concrete type.
	AssocTypeProjection {
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
		base: TypeIndex,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(test, serde(transparent))]
pub struct TypeInterner {
	entries: Vec<Type>,
	#[cfg_attr(test, serde(skip))]
	index_lookup: HashMap<Type, TypeIndex>,
}

impl TypeInterner {
	pub fn new() -> Self {
		let entries = vec![
			// Order must match the `TypeIndex` constants below — see
			// `tir/mod.rs`'s "Type system" table for the frozen layout.
			Type::Infer,
			Type::Error,
			Type::Unit,
			Type::Never,
			Type::Integer,
			Type::Float,
			Type::U8,
			Type::I8,
			Type::U16,
			Type::I16,
			Type::U32,
			Type::I32,
			Type::U64,
			Type::I64,
			Type::F32,
			Type::F64,
			Type::Bool,
			Type::Char,
		];
		let index_lookup = entries
			.iter()
			.cloned()
			.enumerate()
			.map(|(index, ty)| {
				let index = u32::try_from(index)
					.expect("type interner exceeded u32 index capacity");
				(ty, TypeIndex::new(index))
			})
			.collect();
		Self {
			entries,
			index_lookup,
		}
	}

	pub fn intern(&mut self, ty: Type) -> TypeIndex {
		if let Some(&index) = self.index_lookup.get(&ty) {
			return index;
		}

		let index = u32::try_from(self.entries.len())
			.expect("type interner exceeded u32 index capacity");
		let index = TypeIndex::new(index);
		self.entries.push(ty.clone());
		self.index_lookup.insert(ty, index);
		index
	}

	#[inline]
	pub fn resolve(&self, index: TypeIndex) -> &Type {
		&self.entries[usize::from(index)]
	}
}

impl Default for TypeInterner {
	fn default() -> Self {
		Self::new()
	}
}

impl TypeIndex {
	/// Use wherever `INFER` acts as an absent-type sentinel and a concrete
	/// fallback is needed.
	#[inline]
	pub fn infer_or(self, other: TypeIndex) -> TypeIndex {
		if self == TypeIndex::INFER { other } else { self }
	}

	#[inline]
	pub fn is_comptime_number(self) -> bool {
		self == TypeIndex::INTEGER || self == TypeIndex::FLOAT
	}

	#[inline]
	pub fn is_integer(self) -> bool {
		self == TypeIndex::U8
			|| self == TypeIndex::I8
			|| self == TypeIndex::U16
			|| self == TypeIndex::I16
			|| self == TypeIndex::U32
			|| self == TypeIndex::I32
			|| self == TypeIndex::U64
			|| self == TypeIndex::I64
	}

	#[inline]
	pub fn is_float(self) -> bool {
		self == TypeIndex::F32 || self == TypeIndex::F64
	}

	#[inline]
	pub fn is_numeric(self) -> bool {
		self.is_integer() || self.is_float()
	}

	// Pre-allocated indices for primitive types — see `tir/mod.rs`'s "Type
	// system" table. The `TypeInterner` reserves these slots at startup so
	// comparisons like `ty == TypeIndex::U32` work without a pool lookup.
	pub const INFER: TypeIndex = TypeIndex(0);
	pub const ERROR: TypeIndex = TypeIndex(1);
	pub const UNIT: TypeIndex = TypeIndex(2);
	pub const NEVER: TypeIndex = TypeIndex(3);
	pub const INTEGER: TypeIndex = TypeIndex(4);
	pub const FLOAT: TypeIndex = TypeIndex(5);
	pub const U8: TypeIndex = TypeIndex(6);
	pub const I8: TypeIndex = TypeIndex(7);
	pub const U16: TypeIndex = TypeIndex(8);
	pub const I16: TypeIndex = TypeIndex(9);
	pub const U32: TypeIndex = TypeIndex(10);
	pub const I32: TypeIndex = TypeIndex(11);
	pub const U64: TypeIndex = TypeIndex(12);
	pub const I64: TypeIndex = TypeIndex(13);
	pub const F32: TypeIndex = TypeIndex(14);
	pub const F64: TypeIndex = TypeIndex(15);
	pub const BOOL: TypeIndex = TypeIndex(16);
	pub const CHAR: TypeIndex = TypeIndex(17);
}
