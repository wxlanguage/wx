//! Type identity: the structurally hash-consed `Type` arena every resolved
//! signature and expression points into, plus `TypeEnvArena` — the
//! complementary arena answering "what does this *written name* currently
//! mean," rather than "what does this *shape* mean."
//!
//! Deliberately independent of `defs`/`signatures`' resolution machinery —
//! this module only answers identity questions, never "what type does this
//! path/expression have" or "what scope am I resolving in." It depends on
//! `defs` for `TraitIdx` (an associated-type projection names the trait
//! that declares it) and `StructIdx`/`EnumIdx`/`FunctionIdx`/`MemoryIdx`/
//! `GlobalIdx` (all pre-allocated in `defs.rs`'s Phase 1, for the same
//! reason as `TraitIdx`) but nothing
//! here calls into name resolution, and nothing in `defs` depends back on
//! this module — see `tir/defs.rs`'s own doc comment for why that direction
//! has to stay one-way. `TypeEnvArena` fits the same charter: given a name,
//! it hands back a `TypeIndex` already sitting in this module, with no
//! namespace lookup, no diagnostics, and no notion of `signatures.rs`'s
//! demand-driven queries at all.
//! Structural substitution likewise only replaces parameter identities in
//! an existing type; it never resolves or normalizes associated types.
//!
//! A generic-parameter frame's owner (`TypeEnvOwner`) is an enum of registry
//! indices, so it indexes straight into the right registry array
//! (`defs.structs`, `defs.functions`, ...) without a lookup.

use std::hash::BuildHasher;

use hashbrown::HashTable;
use rustc_hash::FxBuildHasher;

use crate::ast::Spanned;
use crate::index::index_newtype;
use crate::tir::defs::{
	DefinitionRegistry, FunctionIdx, IntrinsicDefs, TypeAliasIdx,
};
use crate::vfs::FileId;
use string_interner::symbol::SymbolU32;

use super::defs::{
	AssocTypeIdx, ConstIdx, EnumIdx, GlobalIdx, InherentImplIdx, MemoryIdx,
	StructIdx, TraitIdx, TraitImplIdx,
};

index_newtype!(TypeIndex);

impl TypeIndex {
	/// Use wherever `INFER` acts as an absent-type sentinel and a concrete
	/// fallback is needed.
	#[inline]
	pub fn infer_or(self, other: TypeIndex) -> TypeIndex {
		if self == TypeIndex::INFER {
			other
		} else {
			self
		}
	}

	pub fn is_literal(self) -> bool {
		self == TypeIndex::INTEGER_LITERAL
			|| self == TypeIndex::FLOAT_LITERAL
			|| self == TypeIndex::STRING_LITERAL
			|| self == TypeIndex::CHAR_LITERAL
			|| self == TypeIndex::ARRAY_LITERAL
	}

	#[inline]
	pub fn is_number_literal(self) -> bool {
		self == TypeIndex::INTEGER_LITERAL || self == TypeIndex::FLOAT_LITERAL
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

	// Pre-allocated indices for primitive types. The `TypeInterner` reserves
	// these slots at startup so comparisons like `ty == TypeIndex::U32` work
	// without a pool lookup.
	pub const INFER: TypeIndex = TypeIndex(0);
	pub const ERROR: TypeIndex = TypeIndex(1);
	pub const UNIT: TypeIndex = TypeIndex(2);
	pub const NEVER: TypeIndex = TypeIndex(3);
	pub const INTEGER_LITERAL: TypeIndex = TypeIndex(4);
	pub const FLOAT_LITERAL: TypeIndex = TypeIndex(5);
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
	/// std's `Bool`, an enum.
	pub const BOOL: TypeIndex = TypeIndex(16);
	/// std's `Char`, a struct.
	pub const CHAR: TypeIndex = TypeIndex(17);
	pub const STRING_LITERAL: TypeIndex = TypeIndex(18);
	pub const ARRAY_LITERAL: TypeIndex = TypeIndex(19);
	pub const FUNCREF: TypeIndex = TypeIndex(20);
	pub const CHAR_LITERAL: TypeIndex = TypeIndex(21);
}

/// A list of types inside a `Type`: a run of `TypeInterner::lists`. Not
/// interned on its own; the type holding it is, by the list's contents, so
/// equal types still share one `TypeIndex`. Built only by the interner.
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeList {
	start: u32,
	len: u32,
}

impl TypeList {
	pub(super) const EMPTY: TypeList = TypeList { start: 0, len: 0 };

	pub fn len(self) -> usize {
		self.len as usize
	}

	pub fn is_empty(self) -> bool {
		self.len == 0
	}

	/// The first `len` elements, sharing this list's storage: the arguments
	/// of a flat list's outer frames.
	pub(super) fn prefix(self, len: usize) -> TypeList {
		assert!(len <= self.len(), "a prefix longer than its list");
		TypeList {
			start: self.start,
			len: len as u32,
		}
	}

	/// The elements after the first `skip`, sharing this list's storage: a
	/// method's parameters after its receiver.
	pub(super) fn suffix(self, skip: usize) -> TypeList {
		assert!(skip <= self.len(), "a suffix past its list");
		TypeList {
			start: self.start + skip as u32,
			len: self.len - skip as u32,
		}
	}

	/// This list's elements, out of the interner's `lists`.
	fn slice(self, lists: &[TypeIndex]) -> &[TypeIndex] {
		&lists[self.start as usize..][..self.len as usize]
	}
}

#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
// `TypeParam`/`TypeProjection` echo the enum's own
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
	Never,
	IntegerLiteral,
	FloatLiteral,
	/// A character literal's type until its context gives it one: `Char`,
	/// or an integer type its code point fits (`coerce`).
	CharLiteral,
	/// A string literal's type until its context gives it one: a shared byte
	/// slice or a shared byte array of its length, in a memory the context
	/// names (`coerce`).
	StringLiteral,
	/// An array literal's type until its context gives it one: a shared array
	/// of its length or a shared slice of its elements' type, in a memory the
	/// context names (`coerce`).
	ArrayLiteral,
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
	/// A reference to a function of any signature, written `funcref`: the
	/// untyped counterpart of `TypedFuncref`.
	Funcref,
	/// `()` is the empty tuple, pre-interned as `TypeIndex::UNIT`.
	Tuple {
		elements: TypeList,
	},
	Struct {
		struct_index: StructIdx,
		/// One argument per type parameter of the struct.
		type_args: TypeList,
	},
	/// A reference to a function of a known signature, written
	/// `func(A) -> R`: Wasm's typed function reference. It takes exactly
	/// one parameter type; a written parameter list is sugar for it:
	/// `func()` takes `()`, `func(A)` takes `A`, `func(A, B)` takes
	/// `(A, B)`, so `func((A, B))` is the same type.
	TypedFuncref {
		param: TypeIndex,
		/// `TypeIndex::UNIT` when the written function type omits its result.
		result: TypeIndex,
	},
	/// A function's own zero-sized type, written with its name (`foo<i32>`).
	/// Always applied: one argument per type parameter of the function, so a
	/// generic function has no type until it is instantiated.
	///
	/// Nominal, like a struct: it equals only itself. A trait's function is
	/// its declaration applied to `Self` first (`<Point as Make>::make` is
	/// `make<Point>`), and stays that at every use, concrete `Self` included;
	/// which impl's body runs is decided where it is called, never by
	/// rewriting the type. The impl's own member appears only as the type of
	/// its definition.
	Function {
		func_index: FunctionIdx,
		type_args: TypeList,
	},
	Pointer {
		to: TypeIndex,
		memory: TypeIndex,
		ownership: crate::ast::Ownership,
	},
	/// `M::&[T; N]`. The length is a type-level constant: a `Value`, or
	/// `Infer` until its context gives one.
	Array {
		of: TypeIndex,
		length: TypeIndex,
		memory: TypeIndex,
		ownership: crate::ast::Ownership,
	},
	Slice {
		of: TypeIndex,
		memory: TypeIndex,
		ownership: crate::ast::Ownership,
	},
	Enum {
		enum_index: EnumIdx,
	},
	/// Every `memory` declaration is its own nominal type constructor. Its
	/// `Size` — and anything else `Memory`'s synthetic impl carries — is
	/// never duplicated here; query it through that impl instead (see
	/// `MemoryDef::size_assoc_type_index`), the same way a struct's own
	/// field types live on `StructDef`/`StructSignature`, not on
	/// `Type::Struct` itself.
	Memory {
		memory_index: MemoryIdx,
	},
	/// Every `global` declaration is its own nominal type constructor, same
	/// reasoning as `Memory` above — `Value` lives on the synthetic impl
	/// (`GlobalDef::value_assoc_type_index`), not here.
	Global {
		global_index: GlobalIdx,
	},
	/// One generic parameter, identified by its declaring frame and its
	/// index within that frame. Every use shares one interned instance.
	/// A method's own parameter zero and its parent impl's parameter zero
	/// have different `env`s; lookup and substitution must respect both
	/// parts of the identity. The frame itself records its declaration owner.
	TypeParam {
		env: TypeEnvIdx,
		param_index: u32,
	},
	/// A constant in a type, such as an array's length. It holds the bits
	/// alone: its type is the one where it appears (an array's length is its
	/// memory's `Size`), so the same number is the same type in every place,
	/// as rustc's `ty::Const` has no type of its own.
	Value {
		bits: u64,
	},
	/// A constant named in a type (`[u8; SIZE]`), with its flat type
	/// arguments as a `Function`'s: an impl's, then its own, or `[Self]`
	/// for a trait's declaration. Like a projection, it is replaced by what
	/// it means, its `Value`, once that is known: a free constant's once it
	/// is evaluated.
	Const {
		constant: ConstIdx,
		type_args: TypeList,
	},
	/// `<Base as Trait>::Item`, pending normalization. The base can be
	/// concrete or abstract. `assoc_type_index` always names the trait's
	/// declaration, never an impl's value provider; substitution preserves
	/// this identity and only transforms the base.
	TypeProjection {
		trait_index: TraitIdx,
		assoc_type_index: AssocTypeIdx,
		base: TypeIndex,
	},
}

/// What holds of a type or anything inside it, computed once when the type
/// is interned, from its own kind and its parts' flags (rustc's
/// `TypeFlags`). An interned type never changes, so neither do its flags.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct TypeFlags(u8);

impl TypeFlags {
	/// An `Infer` is in it: something about the type is not known yet.
	pub(super) const HAS_INFER: Self = Self(1 << 0);
	/// An `Error` is in it: something about the type was reported.
	pub(super) const HAS_ERROR: Self = Self(1 << 1);
	/// A literal's type (`IntegerLiteral`, `CharLiteral`, ..) is in it, which
	/// context has not replaced yet.
	pub(super) const HAS_LITERAL: Self = Self(1 << 2);
	/// A `TypeParam` is in it: substitution can change the type.
	pub(super) const HAS_PARAM: Self = Self(1 << 3);
	/// An `TypeProjection` or a `Const` is in it: normalization can
	/// change the type.
	pub(super) const HAS_PROJECTION: Self = Self(1 << 4);
	/// A `Const` is in it: its value can replace it, once evaluated.
	pub(super) const HAS_CONST: Self = Self(1 << 5);

	fn union(self, other: Self) -> Self {
		Self(self.0 | other.0)
	}

	fn contains(self, other: Self) -> bool {
		self.0 & other.0 == other.0
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(test, serde(transparent))]
pub struct TypeInterner {
	entries: Vec<Type>,
	/// Each entry's flags, by the entry's index.
	#[cfg_attr(test, serde(skip))]
	flags: Vec<TypeFlags>,
	/// Every `TypeList`'s elements, back to back.
	#[cfg_attr(test, serde(skip))]
	lists: Vec<TypeIndex>,
	/// The index of every entry, found by its contents: a type's fields
	/// and its list's elements, never where the list is stored.
	#[cfg_attr(test, serde(skip))]
	index_lookup: HashTable<TypeIndex>,
	#[cfg_attr(test, serde(skip))]
	hasher: FxBuildHasher,
}

impl Type {
	/// This type with its list blanked, and the list: hashing and comparing
	/// the first ignores where the list lives, so the list is compared by
	/// its elements.
	fn split_list(self) -> (Type, TypeList) {
		match self {
			Type::Tuple { elements } => (
				Type::Tuple {
					elements: TypeList::EMPTY,
				},
				elements,
			),
			Type::Struct {
				struct_index,
				type_args,
			} => (
				Type::Struct {
					struct_index,
					type_args: TypeList::EMPTY,
				},
				type_args,
			),
			Type::Function {
				func_index,
				type_args,
			} => (
				Type::Function {
					func_index,
					type_args: TypeList::EMPTY,
				},
				type_args,
			),
			Type::Const {
				constant,
				type_args,
			} => (
				Type::Const {
					constant,
					type_args: TypeList::EMPTY,
				},
				type_args,
			),
			ty => (ty, TypeList::EMPTY),
		}
	}
}

impl TypeInterner {
	/// Match a resolved impl target against one receiver. The parameters on
	/// `env`'s chain are holes, filled into the chain's flat argument list
	/// (see `Substitution`); parameters from every other frame are ordinary
	/// identities. All holes must be determined by the target.
	pub(super) fn match_impl_target(
		&self,
		pattern: TypeIndex,
		actual: TypeIndex,
		envs: &TypeEnvArena,
		env: TypeEnvIdx,
	) -> Option<Box<[TypeIndex]>> {
		let mut args = vec![None; envs.generic_count(env)];
		self.match_pattern(pattern, actual, envs, env, &mut args)?;
		args.into_iter().collect::<Option<Box<[TypeIndex]>>>()
	}

	fn match_pattern(
		&self,
		pattern: TypeIndex,
		actual: TypeIndex,
		envs: &TypeEnvArena,
		env: TypeEnvIdx,
		args: &mut [Option<TypeIndex>],
	) -> Option<()> {
		let (expected, found) = (self.resolve(pattern), self.resolve(actual));
		if matches!(expected, Type::Error | Type::Infer)
			|| matches!(found, Type::Error | Type::Infer)
		{
			return None;
		}
		match (expected, found) {
			(
				Type::TypeParam {
					env: owner,
					param_index,
				},
				_,
			) => match envs.flat_slot(env, *owner, *param_index) {
				Some(slot) => {
					let slot = args.get_mut(slot)?;
					match slot {
						Some(previous) if *previous != actual => None,
						Some(_) => Some(()),
						None => {
							*slot = Some(actual);
							Some(())
						}
					}
				}
				None => (pattern == actual).then_some(()),
			},
			(
				Type::Struct {
					struct_index: a,
					type_args: xs,
				},
				Type::Struct {
					struct_index: b,
					type_args: ys,
				},
			) if a == b => self.match_patterns(
				self.list(*xs),
				self.list(*ys),
				envs,
				env,
				args,
			),
			(Type::Tuple { elements: xs }, Type::Tuple { elements: ys }) => {
				self.match_patterns(
					self.list(*xs),
					self.list(*ys),
					envs,
					env,
					args,
				)
			}
			(
				Type::Function {
					func_index: a,
					type_args: xs,
				},
				Type::Function {
					func_index: b,
					type_args: ys,
				},
			) if a == b => self.match_patterns(
				self.list(*xs),
				self.list(*ys),
				envs,
				env,
				args,
			),
			(
				Type::Const {
					constant: a,
					type_args: xs,
				},
				Type::Const {
					constant: b,
					type_args: ys,
				},
			) if a == b => self.match_patterns(
				self.list(*xs),
				self.list(*ys),
				envs,
				env,
				args,
			),
			(
				Type::TypedFuncref {
					param: xp,
					result: xr,
				},
				Type::TypedFuncref {
					param: yp,
					result: yr,
				},
			) => {
				self.match_pattern(*xp, *yp, envs, env, args)?;
				self.match_pattern(*xr, *yr, envs, env, args)
			}
			(
				Type::Pointer {
					to: x,
					memory: xm,
					ownership: xo,
				},
				Type::Pointer {
					to: y,
					memory: ym,
					ownership: yo,
				},
			) if xo == yo => {
				self.match_pattern(*x, *y, envs, env, args)?;
				self.match_pattern(*xm, *ym, envs, env, args)
			}
			(
				Type::Array {
					of: x,
					length: xl,
					memory: xm,
					ownership: xo,
				},
				Type::Array {
					of: y,
					length: yl,
					memory: ym,
					ownership: yo,
				},
			) if xo == yo => {
				self.match_pattern(*x, *y, envs, env, args)?;
				self.match_pattern(*xl, *yl, envs, env, args)?;
				self.match_pattern(*xm, *ym, envs, env, args)
			}
			(
				Type::Slice {
					of: x,
					memory: xm,
					ownership: xo,
				},
				Type::Slice {
					of: y,
					memory: ym,
					ownership: yo,
				},
			) if xo == yo => {
				self.match_pattern(*x, *y, envs, env, args)?;
				self.match_pattern(*xm, *ym, envs, env, args)
			}
			(
				Type::TypeProjection {
					trait_index: at,
					assoc_type_index: aa,
					base: x,
				},
				Type::TypeProjection {
					trait_index: bt,
					assoc_type_index: ba,
					base: y,
				},
			) if at == bt && aa == ba => self.match_pattern(*x, *y, envs, env, args),
			_ if pattern == actual => Some(()),
			_ => None,
		}
	}

	fn match_patterns(
		&self,
		expected: &[TypeIndex],
		found: &[TypeIndex],
		envs: &TypeEnvArena,
		env: TypeEnvIdx,
		args: &mut [Option<TypeIndex>],
	) -> Option<()> {
		if expected.len() != found.len() {
			return None;
		}
		for (pattern, actual) in
			expected.iter().copied().zip(found.iter().copied())
		{
			self.match_pattern(pattern, actual, envs, env, args)?;
		}
		Some(())
	}

	/// `bool` and `char` are std's `Bool` and `Char`, which hold the
	/// `BOOL` and `CHAR` slots, so interning their types finds them.
	pub fn new(bool: EnumIdx, char: StructIdx) -> Self {
		let mut types = Self {
			entries: Vec::new(),
			flags: Vec::new(),
			lists: Vec::new(),
			index_lookup: HashTable::new(),
			hasher: FxBuildHasher,
		};
		// Order must match the `TypeIndex` constants below.
		for ty in [
			Type::Infer,
			Type::Error,
			// `()` is the empty tuple, not a type of its own, so interning
			// an empty tuple anywhere finds this slot.
			Type::Tuple {
				elements: TypeList::EMPTY,
			},
			Type::Never,
			Type::IntegerLiteral,
			Type::FloatLiteral,
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
			Type::Enum { enum_index: bool },
			Type::Struct {
				struct_index: char,
				type_args: TypeList::EMPTY,
			},
			Type::StringLiteral,
			Type::ArrayLiteral,
			Type::Funcref,
			Type::CharLiteral,
		] {
			types.intern(ty);
		}
		types
	}

	/// An interner whose `Bool` and `Char` are no declaration, for tests
	/// that have none.
	#[cfg(test)]
	pub(super) fn for_tests() -> Self {
		Self::new(EnumIdx::new(u32::MAX), StructIdx::new(u32::MAX))
	}

	/// Interns a type whose list, if it has one, is already stored.
	pub fn intern(&mut self, ty: Type) -> TypeIndex {
		// There is no tuple of one: it is its element.
		if let Type::Tuple { elements } = ty
			&& let [element] = *self.list(elements)
		{
			return element;
		}
		let (shape, list) = ty.split_list();
		let hash = self.hasher.hash_one((shape, list.slice(&self.lists)));
		match self.find(hash, shape, list.slice(&self.lists)) {
			Some(index) => index,
			None => self.insert(hash, ty),
		}
	}

	pub fn intern_tuple(&mut self, elements: &[TypeIndex]) -> TypeIndex {
		// There is no tuple of one: it is its element.
		if let [element] = *elements {
			return element;
		}
		let shape = Type::Tuple {
			elements: TypeList::EMPTY,
		};
		let hash = self.hasher.hash_one((shape, elements));
		if let Some(index) = self.find(hash, shape, elements) {
			return index;
		}
		// Stored only now, when no equal type exists yet.
		let list = self.push_list(elements);
		self.insert(hash, Type::Tuple { elements: list })
	}

	pub fn intern_struct(
		&mut self,
		struct_index: StructIdx,
		type_args: &[TypeIndex],
	) -> TypeIndex {
		let shape = Type::Struct {
			struct_index,
			type_args: TypeList::EMPTY,
		};
		let hash = self.hasher.hash_one((shape, type_args));
		if let Some(index) = self.find(hash, shape, type_args) {
			return index;
		}
		let list = self.push_list(type_args);
		self.insert(
			hash,
			Type::Struct {
				struct_index,
				type_args: list,
			},
		)
	}

	pub fn intern_function(
		&mut self,
		func_index: FunctionIdx,
		type_args: &[TypeIndex],
	) -> TypeIndex {
		let shape = Type::Function {
			func_index,
			type_args: TypeList::EMPTY,
		};
		let hash = self.hasher.hash_one((shape, type_args));
		if let Some(index) = self.find(hash, shape, type_args) {
			return index;
		}
		let list = self.push_list(type_args);
		self.insert(
			hash,
			Type::Function {
				func_index,
				type_args: list,
			},
		)
	}

	pub(super) fn intern_const(
		&mut self,
		constant: ConstIdx,
		type_args: &[TypeIndex],
	) -> TypeIndex {
		let shape = Type::Const {
			constant,
			type_args: TypeList::EMPTY,
		};
		let hash = self.hasher.hash_one((shape, type_args));
		if let Some(index) = self.find(hash, shape, type_args) {
			return index;
		}
		let list = self.push_list(type_args);
		self.insert(
			hash,
			Type::Const {
				constant,
				type_args: list,
			},
		)
	}

	/// Stores `elements` as a list of their own, not shared with an equal one:
	/// a type's list is shared through the type, which is interned.
	pub(super) fn push_list<'e>(
		&mut self,
		elements: impl IntoIterator<Item = &'e TypeIndex>,
	) -> TypeList {
		let start = self.lists.len();
		self.lists.extend(elements);
		TypeList {
			start: u32::try_from(start)
				.expect("type interner exceeded u32 list capacity"),
			len: u32::try_from(self.lists.len() - start).unwrap(),
		}
	}

	fn find(
		&self,
		hash: u64,
		shape: Type,
		elements: &[TypeIndex],
	) -> Option<TypeIndex> {
		self.index_lookup
			.find(hash, |&index| {
				let (candidate, list) = self.resolve(index).split_list();
				candidate == shape && list.slice(&self.lists) == elements
			})
			.copied()
	}

	fn insert(&mut self, hash: u64, ty: Type) -> TypeIndex {
		let index = TypeIndex::new(
			u32::try_from(self.entries.len())
				.expect("type interner exceeded u32 index capacity"),
		);
		let flags = self.flags_of(ty);
		self.entries.push(ty);
		self.flags.push(flags);
		let Self {
			entries,
			flags: _,
			lists,
			index_lookup,
			hasher,
		} = self;
		// Growing the table rehashes what it holds, from the same contents.
		index_lookup.insert_unique(hash, index, |&index| {
			let (shape, list) = entries[usize::from(index)].split_list();
			hasher.hash_one((shape, list.slice(lists)))
		});
		index
	}

	pub fn list(&self, list: TypeList) -> &[TypeIndex] {
		list.slice(&self.lists)
	}

	/// The flags of a type about to be interned: its own kind's, joined with
	/// those of its parts, which are interned already.
	fn flags_of(&self, ty: Type) -> TypeFlags {
		match ty {
			Type::Infer => TypeFlags::HAS_INFER,
			Type::Error => TypeFlags::HAS_ERROR,
			Type::IntegerLiteral
			| Type::FloatLiteral
			| Type::CharLiteral
			| Type::StringLiteral
			| Type::ArrayLiteral => TypeFlags::HAS_LITERAL,
			Type::Tuple { elements: list }
			| Type::Struct {
				type_args: list, ..
			}
			| Type::Function {
				type_args: list, ..
			} => {
				let mut flags = TypeFlags::default();
				for &part in list.slice(&self.lists) {
					flags = flags.union(self.flags[usize::from(part)]);
				}
				flags
			}
			Type::Pointer { to: of, memory, .. }
			| Type::Slice { of, memory, .. } => self.flags[usize::from(of)]
				.union(self.flags[usize::from(memory)]),
			Type::Array {
				of, length, memory, ..
			} => self.flags[usize::from(of)]
				.union(self.flags[usize::from(length)])
				.union(self.flags[usize::from(memory)]),
			Type::TypedFuncref { param, result } => self.flags
				[usize::from(param)]
			.union(self.flags[usize::from(result)]),
			Type::TypeProjection { base, .. } => {
				TypeFlags::HAS_PROJECTION.union(self.flags[usize::from(base)])
			}
			Type::Const { type_args, .. } => {
				let mut flags =
					TypeFlags::HAS_PROJECTION.union(TypeFlags::HAS_CONST);
				for &part in type_args.slice(&self.lists) {
					flags = flags.union(self.flags[usize::from(part)]);
				}
				flags
			}
			Type::TypeParam { .. } => TypeFlags::HAS_PARAM,
			Type::Never
			| Type::U8
			| Type::I8
			| Type::U16
			| Type::I16
			| Type::U32
			| Type::I32
			| Type::U64
			| Type::I64
			| Type::F32
			| Type::F64
			| Type::Funcref
			| Type::Enum { .. }
			| Type::Memory { .. }
			| Type::Global { .. }
			| Type::Value { .. } => TypeFlags::default(),
		}
	}

	/// Whether something in `ty` is not known yet (an `Infer` anywhere in it).
	pub(super) fn has_infer(&self, ty: TypeIndex) -> bool {
		self.flags[usize::from(ty)].contains(TypeFlags::HAS_INFER)
	}

	/// Whether something in `ty` was reported (an `Error` anywhere in it).
	pub(super) fn has_error(&self, ty: TypeIndex) -> bool {
		self.flags[usize::from(ty)].contains(TypeFlags::HAS_ERROR)
	}

	/// `ty`, collapsed to `ERROR` when an `Error` is anywhere in it: a type
	/// built of a reported part would only be reported again, as a mismatch
	/// against `Wrapper<{unknown}>`.
	pub(super) fn collapse_error(&self, ty: TypeIndex) -> TypeIndex {
		if self.has_error(ty) {
			TypeIndex::ERROR
		} else {
			ty
		}
	}

	/// Whether a literal's type is anywhere in `ty`.
	pub(super) fn has_literal(&self, ty: TypeIndex) -> bool {
		self.flags[usize::from(ty)].contains(TypeFlags::HAS_LITERAL)
	}

	/// Whether `ty`'s head is a parameter or a projection: the types with
	/// declarations of their own (a parameter's bounds, the bounds its trait
	/// declares on an associated type), which hold wherever `ty` is used.
	pub(super) fn is_param_or_projection(&self, ty: TypeIndex) -> bool {
		matches!(
			self.resolve(ty),
			Type::TypeParam { .. } | Type::TypeProjection { .. }
		)
	}

	/// Whether `ty` is a parameter or a projection out of one (`T::Item`,
	/// `T::Item::Size`): the only types that take traits and equalities from
	/// assumptions. Any other type has a trait exactly when an impl or a
	/// builtin says so: a tuple or a pointer, and a projection out of a
	/// concrete type too (`<P as Container>::Item` is whatever `P`'s impl
	/// says, unreduced or not).
	pub(super) fn is_abstract(&self, ty: TypeIndex) -> bool {
		match *self.resolve(ty) {
			Type::TypeParam { .. } => true,
			Type::TypeProjection { base, .. } => self.is_abstract(base),
			_ => false,
		}
	}

	/// Whether something in `ty` is a parameter: without one, no substitution
	/// changes it.
	pub(super) fn has_param(&self, ty: TypeIndex) -> bool {
		self.flags[usize::from(ty)].contains(TypeFlags::HAS_PARAM)
	}

	/// Whether something in `ty` is a projection: without one, it is already
	/// normal, in every assumption context.
	pub(super) fn has_projection(&self, ty: TypeIndex) -> bool {
		self.flags[usize::from(ty)].contains(TypeFlags::HAS_PROJECTION)
	}

	/// Whether something in `ty` is a constant named, not evaluated: without
	/// one, no value changes it.
	pub(super) fn has_const(&self, ty: TypeIndex) -> bool {
		self.flags[usize::from(ty)].contains(TypeFlags::HAS_CONST)
	}

	/// The type both `a` and `b` describe, where `Infer` is a part not known
	/// yet and gives way to the other side: `Pair<_, u8>` and `Pair<u16, _>`
	/// meet in `Pair<u16, u8>`. Parts meet where the constructors match. An
	/// `Error` absorbs the other side, since it was reported. `None` when the
	/// two disagree somewhere; `Integer` and `Float` are ordinary leaves.
	pub(super) fn meet(
		&mut self,
		a: TypeIndex,
		b: TypeIndex,
	) -> Option<TypeIndex> {
		if a == b || b == TypeIndex::INFER {
			return Some(a);
		}
		if a == TypeIndex::INFER {
			return Some(b);
		}
		if a == TypeIndex::ERROR || b == TypeIndex::ERROR {
			return Some(TypeIndex::ERROR);
		}
		// Two distinct types with nothing unknown or reported in them differ.
		if !self.has_infer(a) && !self.has_infer(b) {
			return None;
		}
		match (*self.resolve(a), *self.resolve(b)) {
			(Type::Tuple { elements: a }, Type::Tuple { elements: b }) => {
				let elements = self.meet_lists(a, b)?;
				Some(self.intern_tuple(&elements))
			}
			(
				Type::Struct {
					struct_index,
					type_args: a,
				},
				Type::Struct {
					struct_index: other,
					type_args: b,
				},
			) if struct_index == other => {
				let type_args = self.meet_lists(a, b)?;
				Some(self.intern_struct(struct_index, &type_args))
			}
			(
				Type::Function {
					func_index,
					type_args: a,
				},
				Type::Function {
					func_index: other,
					type_args: b,
				},
			) if func_index == other => {
				let type_args = self.meet_lists(a, b)?;
				Some(self.intern_function(func_index, &type_args))
			}
			(
				Type::Const {
					constant,
					type_args: a,
				},
				Type::Const {
					constant: other,
					type_args: b,
				},
			) if constant == other => {
				let type_args = self.meet_lists(a, b)?;
				Some(self.intern_const(constant, &type_args))
			}
			(
				Type::TypedFuncref { param, result },
				Type::TypedFuncref {
					param: other_param,
					result: other_result,
				},
			) => {
				let param = self.meet(param, other_param)?;
				let result = self.meet(result, other_result)?;
				Some(self.intern(Type::TypedFuncref { param, result }))
			}
			(
				Type::Pointer {
					to,
					memory,
					ownership,
				},
				Type::Pointer {
					to: other_to,
					memory: other_memory,
					ownership: other_ownership,
				},
			) if ownership == other_ownership => {
				let to = self.meet(to, other_to)?;
				let memory = self.meet(memory, other_memory)?;
				Some(self.intern(Type::Pointer {
					to,
					memory,
					ownership,
				}))
			}
			(
				Type::Array {
					of,
					length,
					memory,
					ownership,
				},
				Type::Array {
					of: other_of,
					length: other_length,
					memory: other_memory,
					ownership: other_ownership,
				},
			) if ownership == other_ownership => {
				let of = self.meet(of, other_of)?;
				let length = self.meet(length, other_length)?;
				let memory = self.meet(memory, other_memory)?;
				Some(self.intern(Type::Array {
					of,
					length,
					memory,
					ownership,
				}))
			}
			(
				Type::Slice {
					of,
					memory,
					ownership,
				},
				Type::Slice {
					of: other_of,
					memory: other_memory,
					ownership: other_ownership,
				},
			) if ownership == other_ownership => {
				let of = self.meet(of, other_of)?;
				let memory = self.meet(memory, other_memory)?;
				Some(self.intern(Type::Slice {
					of,
					memory,
					ownership,
				}))
			}
			(
				Type::TypeProjection {
					trait_index,
					assoc_type_index,
					base,
				},
				Type::TypeProjection {
					trait_index: other_trait,
					assoc_type_index: other_assoc_type,
					base: other_base,
				},
			) if trait_index == other_trait
				&& assoc_type_index == other_assoc_type =>
			{
				let base = self.meet(base, other_base)?;
				Some(self.intern(Type::TypeProjection {
					trait_index,
					assoc_type_index,
					base,
				}))
			}
			_ => None,
		}
	}

	/// Learns parameters of `env` from a value: walks `declared`, a type
	/// written in `env`, beside `actual`, the value's type, and meets each of
	/// `env`'s parameters' slot with the part of `actual` at its position.
	/// Parts that do not line up teach nothing; the value's own check against
	/// the declared type reports them. A value with an untyped literal in it
	/// is not known yet, so it teaches nothing either.
	pub(super) fn learn(
		&mut self,
		envs: &TypeEnvArena,
		env: TypeEnvIdx,
		slots: &mut [TypeIndex],
		declared: TypeIndex,
		actual: TypeIndex,
	) {
		if self.has_literal(actual) {
			return;
		}
		match (*self.resolve(declared), *self.resolve(actual)) {
			(
				Type::TypeParam {
					env: owner,
					param_index,
				},
				_,
			) => {
				let Some(slot) = envs.flat_slot(env, owner, param_index) else {
					return;
				};
				if let Some(met) = self.meet(slots[slot], actual) {
					slots[slot] = met;
				}
			}
			(
				Type::Tuple { elements: declared },
				Type::Tuple { elements: actual },
			) => self.learn_lists(envs, env, slots, declared, actual),
			(
				Type::Struct {
					struct_index,
					type_args: declared,
				},
				Type::Struct {
					struct_index: other,
					type_args: actual,
				},
			) if struct_index == other => {
				self.learn_lists(envs, env, slots, declared, actual)
			}
			(
				Type::Function {
					func_index,
					type_args: declared,
				},
				Type::Function {
					func_index: other,
					type_args: actual,
				},
			) if func_index == other => {
				self.learn_lists(envs, env, slots, declared, actual)
			}
			(
				Type::Const {
					constant,
					type_args: declared,
				},
				Type::Const {
					constant: other,
					type_args: actual,
				},
			) if constant == other => {
				self.learn_lists(envs, env, slots, declared, actual)
			}
			(
				Type::TypedFuncref { param, result },
				Type::TypedFuncref {
					param: other_param,
					result: other_result,
				},
			) => {
				self.learn(envs, env, slots, param, other_param);
				self.learn(envs, env, slots, result, other_result);
			}
			(
				Type::Pointer {
					to: of,
					memory,
					ownership,
				},
				Type::Pointer {
					to: other_of,
					memory: other_memory,
					ownership: other_ownership,
				},
			)
			| (
				Type::Slice {
					of,
					memory,
					ownership,
				},
				Type::Slice {
					of: other_of,
					memory: other_memory,
					ownership: other_ownership,
				},
			) if ownership == other_ownership => {
				self.learn(envs, env, slots, of, other_of);
				self.learn(envs, env, slots, memory, other_memory);
			}
			(
				Type::Array {
					of,
					length,
					memory,
					ownership,
				},
				Type::Array {
					of: other_of,
					length: other_length,
					memory: other_memory,
					ownership: other_ownership,
				},
			) if ownership == other_ownership => {
				self.learn(envs, env, slots, of, other_of);
				self.learn(envs, env, slots, length, other_length);
				self.learn(envs, env, slots, memory, other_memory);
			}
			// A projection's value is not its base: `<T as Tr>::X` being `u8`
			// says nothing of `T`.
			_ => {}
		}
	}

	/// `learn` over two lists, element by element, when their lengths agree.
	/// Each pair is read just before it is learned from, as in `meet_lists`.
	fn learn_lists(
		&mut self,
		envs: &TypeEnvArena,
		env: TypeEnvIdx,
		slots: &mut [TypeIndex],
		declared: TypeList,
		actual: TypeList,
	) {
		if declared.len() != actual.len() {
			return;
		}
		for at in 0..declared.len() {
			let (part, other) =
				(self.list(declared)[at], self.list(actual)[at]);
			self.learn(envs, env, slots, part, other);
		}
	}

	/// Two lists meeting element by element; `None` when their lengths or any
	/// pair of elements disagree. Each pair is read just before it meets: a
	/// meeting can intern, and so grow `lists`, but never change a list.
	fn meet_lists(
		&mut self,
		a: TypeList,
		b: TypeList,
	) -> Option<Box<[TypeIndex]>> {
		if a.len() != b.len() {
			return None;
		}
		let mut met = Vec::with_capacity(a.len());
		for at in 0..a.len() {
			let (left, right) = (self.list(a)[at], self.list(b)[at]);
			met.push(self.meet(left, right)?);
		}
		Some(met.into_boxed_slice())
	}

	#[inline]
	pub fn resolve(&self, index: TypeIndex) -> &Type {
		&self.entries[usize::from(index)]
	}

	/// Replaces parameters from one frame throughout `ty`. Parameters from
	/// other frames stay unchanged, and replacements are inserted as-is:
	/// this does not recursively substitute inside `substitution.args`.
	/// Projections keep their identity and only substitute their receiver;
	/// selecting an impl or normalizing its value is a separate operation.
	/// Unchanged types retain their indices without allocating. Child lists
	/// are copied only after a change requires a new owning type node.
	///
	/// Panics if an encountered parameter in the targeted frame has no
	/// corresponding argument. Argument arity is the caller's responsibility.
	pub(super) fn substitute(
		&mut self,
		ty: TypeIndex,
		substitution: Substitution<'_>,
	) -> TypeIndex {
		if !self.has_param(ty) {
			return ty;
		}
		match *self.resolve(ty) {
			Type::TypeParam { env, param_index } => match substitution
				.envs
				.flat_slot(substitution.env, env, param_index)
			{
				Some(slot) => *substitution.args.get(slot).expect(
					"substitution is missing an argument for its parameter chain",
				),
				None => ty,
			},
			Type::Tuple { elements } => {
				match self.substitute_list(elements, substitution) {
					Some(elements) => self.intern_tuple(&elements),
					None => ty,
				}
			}
			Type::Struct {
				struct_index,
				type_args,
			} => match self.substitute_list(type_args, substitution) {
				Some(type_args) => self.intern_struct(struct_index, &type_args),
				None => ty,
			},
			Type::Function {
				func_index,
				type_args,
			} => match self.substitute_list(type_args, substitution) {
				Some(type_args) => self.intern_function(func_index, &type_args),
				None => ty,
			},
			Type::Const {
				constant,
				type_args,
			} => match self.substitute_list(type_args, substitution) {
				Some(type_args) => self.intern_const(constant, &type_args),
				None => ty,
			},
			Type::TypedFuncref { param, result } => {
				let next_param = self.substitute(param, substitution);
				let next_result = self.substitute(result, substitution);
				if next_param == param && next_result == result {
					ty
				} else {
					self.intern(Type::TypedFuncref {
						param: next_param,
						result: next_result,
					})
				}
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => {
				let next_to = self.substitute(to, substitution);
				let next_memory = self.substitute(memory, substitution);
				if next_to == to && next_memory == memory {
					ty
				} else {
					self.intern(Type::Pointer {
						to: next_to,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Array {
				of,
				length,
				memory,
				ownership,
			} => {
				let next_of = self.substitute(of, substitution);
				let next_length = self.substitute(length, substitution);
				let next_memory = self.substitute(memory, substitution);
				if next_of == of
					&& next_length == length
					&& next_memory == memory
				{
					ty
				} else {
					self.intern(Type::Array {
						of: next_of,
						length: next_length,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Slice {
				of,
				memory,
				ownership,
			} => {
				let next_of = self.substitute(of, substitution);
				let next_memory = self.substitute(memory, substitution);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.intern(Type::Slice {
						of: next_of,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::TypeProjection {
				base,
				trait_index,
				assoc_type_index,
			} => {
				let next_base = self.substitute(base, substitution);
				if next_base == base {
					ty
				} else {
					self.intern(Type::TypeProjection {
						base: next_base,
						trait_index,
						assoc_type_index,
					})
				}
			}
			Type::Error
			| Type::Infer
			| Type::Never
			| Type::IntegerLiteral
			| Type::FloatLiteral
			| Type::CharLiteral
			| Type::StringLiteral
			| Type::ArrayLiteral
			| Type::U8
			| Type::I8
			| Type::U16
			| Type::I16
			| Type::U32
			| Type::I32
			| Type::U64
			| Type::I64
			| Type::F32
			| Type::F64
			| Type::Funcref
			| Type::Enum { .. }
			| Type::Memory { .. }
			| Type::Global { .. }
			| Type::Value { .. } => ty,
		}
	}

	/// The substituted elements, copied only after the first changed one.
	/// Each element is read by position: substituting may store more lists.
	fn substitute_list(
		&mut self,
		list: TypeList,
		substitution: Substitution<'_>,
	) -> Option<Vec<TypeIndex>> {
		let mut substituted: Option<Vec<TypeIndex>> = None;
		for index in 0..list.len as usize {
			let original = self.list(list)[index];
			let next = self.substitute(original, substitution);
			if next != original {
				substituted.get_or_insert_with(|| self.list(list).to_vec())
					[index] = next;
			}
		}
		substituted
	}
}

// A `Copy` handle into a `TypeEnvArena` — see that type's doc comment.
index_newtype!(TypeEnvIdx);

/// Replacements for every parameter on `env`'s chain: `args` is the chain's
/// flat argument list, outer frames first, so `TypeParam { env: e, i }` is
/// replaced by `args[parent_count(e) + i]` for each frame `e` on the chain
/// (`TypeEnvArena::flat_slot`). Parameters of any other frame, including a
/// frame nested inside `env`, are untouched, so instantiating an outer frame
/// alone is a partial substitution. This borrows an instantiation's arguments
/// without changing the original lexical environment. Replacement types may
/// themselves contain parameters.
#[derive(Clone, Copy)]
pub(super) struct Substitution<'a> {
	pub(super) envs: &'a TypeEnvArena,
	pub(super) env: TypeEnvIdx,
	pub(super) args: &'a [TypeIndex],
}

/// A generic reference site's target, identified the same way dispatch and
/// every other `defs.rs`-facing lookup is — by index into its own registry
/// array — so `name`/`file_id` can reach straight into `defs.structs[..]`. Constants and enums are also represented for
/// diagnostics, even though they currently have no type parameters.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeEnvOwner {
	Constant(ConstIdx),
	Enum(EnumIdx),
	Struct(StructIdx),
	Function(FunctionIdx),
	Trait(TraitIdx),
	TypeAlias(TypeAliasIdx),
	/// An impl block's own `<T>` frame — has no written name (see `name`).
	InherentImpl(InherentImplIdx),
	TraitImpl(TraitImplIdx),
}

/// The impl a frame chain is inside of: what `Self` there names.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ImplKind {
	Inherent(InherentImplIdx),
	Trait(TraitImplIdx),
}

impl TypeEnvOwner {
	pub(super) fn noun(self) -> &'static str {
		match self {
			Self::Constant(_) => "constant",
			Self::Enum(_) => "enum",
			Self::Struct(_) => "struct",
			Self::Trait(_) => "trait",
			Self::Function(_) => "function",
			Self::TypeAlias(_) => "type alias",
			Self::InherentImpl(_) | Self::TraitImpl(_) => "impl block",
		}
	}

	/// `None` for `InherentImpl`/`TraitImpl` — an impl block has no
	/// written name to report.
	pub(super) fn name(
		self,
		defs: &DefinitionRegistry,
	) -> Option<Spanned<SymbolU32>> {
		Some(match self {
			Self::Constant(index) => defs.constants[usize::from(index)].name,
			Self::Enum(index) => defs.enums[usize::from(index)].name,
			Self::Struct(struct_index) => {
				defs.structs[usize::from(struct_index)].name
			}
			Self::Function(func_index) => {
				defs.functions[usize::from(func_index)].name
			}
			Self::Trait(trait_index) => {
				defs.traits[usize::from(trait_index)].name
			}
			Self::TypeAlias(type_alias_index) => {
				defs.type_aliases[usize::from(type_alias_index)].name
			}
			Self::InherentImpl(_) | Self::TraitImpl(_) => return None,
		})
	}

	pub(super) fn file_id(self, defs: &DefinitionRegistry) -> FileId {
		match self {
			Self::Constant(index) => defs.constants[usize::from(index)].file_id,
			Self::Enum(index) => defs.enums[usize::from(index)].file_id,
			Self::Struct(struct_index) => {
				defs.structs[usize::from(struct_index)].file_id
			}
			Self::Function(func_index) => {
				defs.functions[usize::from(func_index)].file_id
			}
			Self::Trait(trait_index) => {
				defs.traits[usize::from(trait_index)].file_id
			}
			Self::TypeAlias(type_alias_index) => {
				defs.type_aliases[usize::from(type_alias_index)].file_id
			}
			Self::InherentImpl(index) => {
				defs.inherent_impls[usize::from(index)].file_id
			}
			Self::TraitImpl(index) => {
				defs.trait_impls[usize::from(index)].file_id
			}
		}
	}
}

/// One frame of the chain of generic-parameter names visible while resolving
/// one item's own signature — composed parent-first, the way lexical scopes
/// are: a trait's synthetic single-entry `Self` frame, or an impl's own
/// `<T>` frame (which every impl has, even an empty one); then the item's
/// own explicit `<T>`. Every frame declares parameters, and nothing else.
///
/// A parameter is a `T` from `<T: Bound>`, or a trait's or typeset's own
/// `Self`, interned as `Type::TypeParam { env, param_index }` the moment its
/// frame is built. An impl's `Self` is not a parameter: it names the impl's
/// target, found through the impl's frame (`TypeEnvArena::enclosing_impl`).
/// No bounds here: those are a resolved-signature fact (see `signatures.rs`'s
/// own doc comment), not an identity one.
///
/// `parent_count` is how many parameters the frames above this one declare
/// (rustc's `Generics::parent_count`): a parameter's position in its chain's
/// flat argument list is `parent_count + param_index`. A frame's parameters
/// live in the arena's tables: `len` names from `names_start`, and from
/// `types_start` its identity arguments, `parent_count + len` of them.
enum TypeEnv {
	Root,
	Frame {
		owner: TypeEnvOwner,
		parent: TypeEnvIdx,
		parent_count: u32,
		len: u32,
		names_start: u32,
		types_start: u32,
	},
}

/// Owns every [`TypeEnv`] frame ever pushed while resolving *any* item's
/// signature — one arena for the whole Phase 2 run, same lifetime and shape
/// as `TypeInterner` (append-only, addressed by a cheap `Copy` id, never
/// invalidated). A signature struct stores the `TypeEnvId` of its own frame
/// rather than an owned param list.
///
/// Generalizes `builder::type_compare::TypeEnv` (which answers "what does
/// this abstract variable mean, once an impl's own args are known," for
/// read-only structural comparison after signatures already exist) to also
/// answer "what does this written name refer to" while a signature is
/// being built in the first place; where it was written is recorded in
/// `NameResolutions`, which the frame's position identifies. Being append-only is what
/// makes that persistence safe under reentrancy: `ensure_signature` calling
/// back into itself for some *other* item (a field type naming another
/// struct, say) pushes that item's own frames on top without disturbing —
/// or invalidating the `TypeEnvId` of — anything the outer call already
/// holds, the exact same guarantee `TypeInterner::intern` already gives for
/// `TypeIndex`.
pub(super) struct TypeEnvArena {
	envs: Vec<TypeEnv>,
	/// Each frame's own parameter names.
	names: Vec<Spanned<SymbolU32>>,
	/// Each frame's identity arguments: the parameters of its whole chain,
	/// outer frames first, so an instantiation of a frame with its own
	/// parameters is a slice of this.
	types: Vec<TypeIndex>,
}

impl TypeEnvIdx {
	/// The always-present slot-0 frame — a [`TypeEnv::Root`]. A sentinel
	/// constant on the id type itself, same as `TypeIndex::INFER`/`ERROR`/…
	/// below rather than on the arena that produces the rest — built via the
	/// tuple constructor directly since `TypeEnvId::new` isn't `const fn`,
	/// the one place within this module that's allowed to reach past it.
	pub(super) const ROOT: TypeEnvIdx = TypeEnvIdx(0);
}

impl TypeEnvArena {
	pub(super) fn new() -> Self {
		Self {
			envs: vec![TypeEnv::Root],
			names: Vec::new(),
			types: Vec::new(),
		}
	}

	/// Builds a new frame out of `owner`'s own declared parameter names —
	/// the "insert the identities" step, and *only* that: no bounds (a
	/// bound can reference a sibling param, so it can only resolve once the
	/// frame this returns already exists — the caller's job, strictly
	/// afterward) and no duplicate-name checking (a diagnostic concern this
	/// module has no vocabulary for, and just as cheaply done over the
	/// caller's own name list before ever calling this). Covers both a
	/// fresh `<T, U>` list and a single-entry abstract `Self` frame (trait,
	/// typeset); it is the only way a frame is made.
	///
	/// Interns each name's own `Type::TypeParam` against the frame's id
	/// before the frame exists, predicted from the arena's length.
	#[inline]
	pub(super) fn push_param_frame(
		&mut self,
		types: &mut TypeInterner,
		owner: TypeEnvOwner,
		parent: TypeEnvIdx,
		names: impl IntoIterator<Item = Spanned<SymbolU32>>,
	) -> TypeEnvIdx {
		let frame = TypeEnvIdx::new(u32::try_from(self.envs.len()).unwrap());
		let parent_count = self.generic_count(parent);
		let names_start = self.names.len();
		self.names.extend(names);
		let len = self.names.len() - names_start;
		let types_start = self.types.len();
		self.types.extend_from_within(self.identity_range(parent));
		self.types.extend((0..len).map(|index| {
			types.intern(Type::TypeParam {
				env: frame,
				param_index: u32::try_from(index).unwrap(),
			})
		}));
		self.envs.push(TypeEnv::Frame {
			owner,
			parent,
			parent_count: u32::try_from(parent_count).unwrap(),
			len: u32::try_from(len).unwrap(),
			names_start: u32::try_from(names_start).unwrap(),
			types_start: u32::try_from(types_start).unwrap(),
		});
		frame
	}

	/// The names of `env`'s own parameters. A declaration without generics
	/// has no frame of its own and stores `ROOT`, which declares none.
	#[inline]
	pub(super) fn param_names(&self, env: TypeEnvIdx) -> &[Spanned<SymbolU32>] {
		match self.envs[usize::from(env)] {
			TypeEnv::Frame {
				len, names_start, ..
			} => &self.names[names_start as usize..][..len as usize],
			TypeEnv::Root => &[],
		}
	}

	/// The types of `env`'s own parameters.
	#[inline]
	pub(super) fn param_types(&self, env: TypeEnvIdx) -> &[TypeIndex] {
		&self.identity_args(env)[self.parent_count(env)..]
	}

	/// The arguments that instantiate `env`'s chain with its own parameters,
	/// each at its flat slot (`flat_slot`).
	#[inline]
	pub(super) fn identity_args(&self, env: TypeEnvIdx) -> &[TypeIndex] {
		&self.types[self.identity_range(env)]
	}

	fn identity_range(&self, env: TypeEnvIdx) -> std::ops::Range<usize> {
		match self.envs[usize::from(env)] {
			TypeEnv::Frame {
				parent_count,
				len,
				types_start,
				..
			} => {
				let start = types_start as usize;
				start..start + (parent_count + len) as usize
			}
			TypeEnv::Root => 0..0,
		}
	}

	#[inline]
	pub(super) fn owner(&self, env: TypeEnvIdx) -> TypeEnvOwner {
		match &self.envs[usize::from(env)] {
			TypeEnv::Frame { owner, .. } => *owner,
			_ => unreachable!(),
		}
	}

	/// The enclosing lexical frame; Root has no parent.
	pub(super) fn parent(&self, env: TypeEnvIdx) -> Option<TypeEnvIdx> {
		match &self.envs[usize::from(env)] {
			TypeEnv::Root => None,
			TypeEnv::Frame { parent, .. } => Some(*parent),
		}
	}

	/// How many parameters the frames above `env` declare.
	#[inline]
	pub(super) fn parent_count(&self, env: TypeEnvIdx) -> usize {
		match &self.envs[usize::from(env)] {
			TypeEnv::Root => 0,
			TypeEnv::Frame { parent_count, .. } => *parent_count as usize,
		}
	}

	/// How many arguments instantiating `env` takes: every parameter on its
	/// chain.
	#[inline]
	pub(super) fn generic_count(&self, env: TypeEnvIdx) -> usize {
		self.identity_args(env).len()
	}

	/// `env` and the frames above it, innermost first, without `Root`.
	pub(super) fn chain(
		&self,
		env: TypeEnvIdx,
	) -> impl Iterator<Item = TypeEnvIdx> + '_ {
		std::iter::successors(Some(env), |&frame| self.parent(frame))
			.take_while(|&frame| frame != TypeEnvIdx::ROOT)
	}

	/// The position of `TypeParam { env: owner, param_index }` in the flat
	/// argument list of `env`'s chain, or `None` when `owner` is not on it.
	pub(super) fn flat_slot(
		&self,
		env: TypeEnvIdx,
		owner: TypeEnvIdx,
		param_index: u32,
	) -> Option<usize> {
		self.chain(env)
			.any(|frame| frame == owner)
			.then(|| self.parent_count(owner) + param_index as usize)
	}

	/// The impl owning the nearest impl frame on `env`'s chain, if any.
	pub(super) fn enclosing_impl(
		&self,
		mut env: TypeEnvIdx,
	) -> Option<ImplKind> {
		while let TypeEnv::Frame { owner, parent, .. } =
			&self.envs[usize::from(env)]
		{
			match *owner {
				TypeEnvOwner::InherentImpl(index) => {
					return Some(ImplKind::Inherent(index));
				}
				TypeEnvOwner::TraitImpl(index) => {
					return Some(ImplKind::Trait(index));
				}
				_ => env = *parent,
			}
		}
		None
	}

	/// Where `name` is declared, walking from `env` towards `Root`: the
	/// frame and the parameter's position in it. `None` means no frame in
	/// the chain declares it.
	pub(super) fn resolve(
		&self,
		env: TypeEnvIdx,
		name: SymbolU32,
	) -> Option<(TypeEnvIdx, u32)> {
		let mut current = env;
		loop {
			match &self.envs[usize::from(current)] {
				TypeEnv::Root => return None,
				TypeEnv::Frame { parent, .. } => {
					if let Some(index) = self
						.param_names(current)
						.iter()
						.position(|param| param.inner == name)
					{
						return Some((current, u32::try_from(index).unwrap()));
					}
					current = *parent;
				}
			}
		}
	}
}

impl IntrinsicDefs {
	/// `idx`'s real identity as a primitive type, if it has one. `None` for
	/// the common case — an ordinary, non-primitive alias — and `Some` only
	/// for the handful of reserved names (`u8`, `funcref`, ...) that
	/// prescan recognized as one of std's own `#[intrinsic]` type aliases.
	/// Those are bodiless by design, so this pre-interned `TypeIndex` *is*
	/// their identity — nothing else names what they resolve to.
	pub(super) fn identity_of(&self, idx: TypeAliasIdx) -> Option<TypeIndex> {
		[
			(self.u8, TypeIndex::U8),
			(self.i8, TypeIndex::I8),
			(self.u16, TypeIndex::U16),
			(self.i16, TypeIndex::I16),
			(self.u32, TypeIndex::U32),
			(self.i32, TypeIndex::I32),
			(self.u64, TypeIndex::U64),
			(self.i64, TypeIndex::I64),
			(self.f32, TypeIndex::F32),
			(self.f64, TypeIndex::F64),
			(self.funcref, TypeIndex::FUNCREF),
			(self.integer_kind, TypeIndex::INTEGER_LITERAL),
			(self.char_kind, TypeIndex::CHAR_LITERAL),
		]
		.into_iter()
		.find_map(|(slot, ty)| (slot == Some(idx)).then_some(ty))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::ast::{Keyword, Ownership};
	use crate::diagnostics::TextSpan;

	#[test]
	fn types_meet_where_the_unknown_parts_give_way() {
		let mut types = TypeInterner::for_tests();
		let pair = |types: &mut TypeInterner, a, b| {
			types.intern_struct(StructIdx::new(0), &[a, b])
		};
		let left = pair(&mut types, TypeIndex::INFER, TypeIndex::U8);
		let right = pair(&mut types, TypeIndex::U16, TypeIndex::INFER);
		let both = pair(&mut types, TypeIndex::U16, TypeIndex::U8);
		assert_eq!(types.meet(left, right), Some(both));
		assert_eq!(types.meet(TypeIndex::INFER, both), Some(both));
		assert_eq!(types.meet(both, both), Some(both));
		// Nested: `(Pair<_, u8>, _)` and `(Pair<u16, _>, bool)`.
		let outer = types.intern_tuple(&[left, TypeIndex::INFER]);
		let other = types.intern_tuple(&[right, TypeIndex::BOOL]);
		let met = types.intern_tuple(&[both, TypeIndex::BOOL]);
		assert_eq!(types.meet(outer, other), Some(met));
		// A part known on both sides must agree, and so must the shapes.
		let wide = pair(&mut types, TypeIndex::INFER, TypeIndex::U32);
		assert_eq!(types.meet(left, wide), None);
		assert_eq!(types.meet(TypeIndex::U8, TypeIndex::U16), None);
		let long =
			types.intern_tuple(&[left, TypeIndex::BOOL, TypeIndex::BOOL]);
		assert_eq!(types.meet(outer, long), None);
		// A reported part takes the other side with it.
		assert_eq!(types.meet(TypeIndex::ERROR, both), Some(TypeIndex::ERROR));
	}

	#[test]
	fn a_type_has_infer_or_error_when_one_is_anywhere_in_it() {
		let mut types = TypeInterner::for_tests();
		let open = types.intern_tuple(&[TypeIndex::INFER, TypeIndex::U8]);
		let nested = types.intern_tuple(&[open, TypeIndex::U16]);
		let closed = types.intern_tuple(&[TypeIndex::U16, TypeIndex::U8]);
		let broken =
			types.intern_struct(StructIdx::new(0), &[closed, TypeIndex::ERROR]);
		assert!(types.has_infer(TypeIndex::INFER));
		assert!(types.has_infer(open));
		assert!(types.has_infer(nested));
		assert!(!types.has_infer(closed));
		assert!(!types.has_infer(TypeIndex::UNIT));
		assert!(types.has_error(broken));
		assert!(!types.has_infer(broken));
		assert!(!types.has_error(nested));
	}

	/// A parameter is what substitution replaces and a projection is what
	/// normalization reduces; a function type is nominal and has neither of
	/// its own, only what its arguments have.
	#[test]
	fn a_type_has_a_param_or_projection_when_one_is_anywhere_in_it() {
		let mut types = TypeInterner::for_tests();
		let t = parameter(&mut types, TypeEnvIdx::new(1), 0);
		let wrapped = types.intern_struct(StructIdx::new(0), &[t]);
		let projection = |types: &mut TypeInterner, base| {
			types.intern(Type::TypeProjection {
				trait_index: TraitIdx::new(0),
				assoc_type_index: AssocTypeIdx::new(0),
				base,
			})
		};
		let abstract_item = projection(&mut types, t);
		let concrete_item = projection(&mut types, TypeIndex::I32);
		let holds_item = types.intern_tuple(&[TypeIndex::U8, concrete_item]);
		let function = types.intern_function(FunctionIdx::new(0), &[t]);
		assert!(types.has_param(t));
		assert!(types.has_param(wrapped));
		assert!(!types.has_projection(wrapped));
		assert!(types.has_param(abstract_item));
		assert!(types.has_projection(abstract_item));
		assert!(!types.has_param(concrete_item));
		assert!(types.has_projection(holds_item));
		assert!(types.has_param(function));
		assert!(!types.has_projection(function));
		let point = types.intern_struct(StructIdx::new(1), &[]);
		let make_point = types.intern_function(FunctionIdx::new(0), &[point]);
		assert!(!types.has_param(make_point));
		assert!(!types.has_projection(make_point));
	}

	/// Two unrelated root frames: `TypeEnvIdx(1)` with two parameters and
	/// `TypeEnvIdx(2)` with one.
	fn root_frames(types: &mut TypeInterner) -> TypeEnvArena {
		let mut envs = TypeEnvArena::new();
		let name = Spanned {
			inner: Keyword::SelfPascal.symbol(),
			span: TextSpan::new(0, 0),
		};
		for count in [2, 1] {
			envs.push_param_frame(
				types,
				TypeEnvOwner::Function(FunctionIdx::new(0)),
				TypeEnvIdx::ROOT,
				vec![name.clone(); count],
			);
		}
		envs
	}

	fn parameter(
		types: &mut TypeInterner,
		env: TypeEnvIdx,
		param_index: u32,
	) -> TypeIndex {
		types.intern(Type::TypeParam { env, param_index })
	}

	#[test]
	fn substitution_replaces_only_the_targeted_frames_parameters() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let u = parameter(&mut types, env, 1);
		let other = parameter(&mut types, TypeEnvIdx::new(2), 0);
		let original = types.intern_tuple(&[t, u, other]);
		let expected =
			types.intern_tuple(&[TypeIndex::I32, TypeIndex::BOOL, other]);
		let count = types.entries.len();

		let actual = types.substitute(
			original,
			Substitution {
				envs: &envs,
				env,
				args: &[TypeIndex::I32, TypeIndex::BOOL],
			},
		);

		assert_eq!(actual, expected);
		assert_eq!(types.entries.len(), count, "reuse the interned result");
		assert_eq!(
			original,
			types.intern_tuple(&[t, u, other]),
			"the generic template must remain unchanged"
		);
	}

	/// A function containing every compound type shape. Both the element
	/// and memory are parameters, including beneath chained projections.
	fn nested_signature(
		types: &mut TypeInterner,
		element: TypeIndex,
		memory: TypeIndex,
	) -> TypeIndex {
		let wrapper = types.intern_struct(StructIdx::new(0), &[element]);
		let item = types.intern(Type::TypeProjection {
			trait_index: TraitIdx::new(0),
			assoc_type_index: AssocTypeIdx::new(0),
			base: wrapper,
		});
		let next = types.intern(Type::TypeProjection {
			trait_index: TraitIdx::new(1),
			assoc_type_index: AssocTypeIdx::new(1),
			base: item,
		});
		let pointer = types.intern(Type::Pointer {
			to: next,
			memory,
			ownership: Ownership::Shared,
		});
		let seven = types.intern(Type::Value { bits: 7 });
		let array = types.intern(Type::Array {
			of: pointer,
			length: seven,
			memory,
			ownership: Ownership::Exclusive,
		});
		let slice = types.intern(Type::Slice {
			of: element,
			memory,
			ownership: Ownership::Shared,
		});
		let function_item =
			types.intern_function(FunctionIdx::new(0), &[element, memory]);
		let tuple = types.intern_tuple(&[array, slice, function_item]);
		types.intern(Type::TypedFuncref {
			param: tuple,
			result: next,
		})
	}

	#[test]
	fn substitution_traverses_nested_types_without_normalizing_projections() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let m = parameter(&mut types, env, 1);
		let memory = types.intern(Type::Memory {
			memory_index: MemoryIdx::new(0),
		});
		let original = nested_signature(&mut types, t, m);

		let actual = types.substitute(
			original,
			Substitution {
				envs: &envs,
				env,
				args: &[TypeIndex::I32, memory],
			},
		);
		let expected = nested_signature(&mut types, TypeIndex::I32, memory);
		assert_eq!(actual, expected);
		assert_ne!(actual, original);
		assert_eq!(nested_signature(&mut types, t, m), original);
	}

	#[test]
	fn unchanged_substitution_preserves_indices_without_growing_the_interner() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let m = parameter(&mut types, env, 1);
		let original = nested_signature(&mut types, t, m);
		let count = types.entries.len();

		assert_eq!(
			types.substitute(
				original,
				Substitution {
					envs: &envs,
					env: TypeEnvIdx::new(2),
					args: &[]
				},
			),
			original
		);
		assert_eq!(
			types.substitute(
				original,
				Substitution {
					envs: &envs,
					env,
					args: &[t, m]
				}
			),
			original
		);
		assert_eq!(types.entries.len(), count);
	}

	#[test]
	fn substitution_preserves_unchanged_list_elements_around_late_changes() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let u = parameter(&mut types, env, 1);
		let substitution = Substitution {
			envs: &envs,
			env,
			args: &[TypeIndex::I32, TypeIndex::U8],
		};
		let cases = [
			(
				[TypeIndex::BOOL, TypeIndex::CHAR, t],
				[TypeIndex::BOOL, TypeIndex::CHAR, TypeIndex::I32],
			),
			(
				[TypeIndex::BOOL, t, TypeIndex::CHAR],
				[TypeIndex::BOOL, TypeIndex::I32, TypeIndex::CHAR],
			),
			(
				[t, TypeIndex::BOOL, u],
				[TypeIndex::I32, TypeIndex::BOOL, TypeIndex::U8],
			),
		];
		for (original, expected) in cases {
			let original = types.intern_tuple(&original);
			let actual = types.substitute(original, substitution);
			assert_eq!(actual, types.intern_tuple(&expected));
		}
	}

	#[test]
	fn substitution_handles_independent_function_parameter_and_result_changes()
	{
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let substitution = Substitution {
			envs: &envs,
			env,
			args: &[TypeIndex::I32],
		};
		let cases = [
			(
				Type::TypedFuncref {
					param: TypeIndex::BOOL,
					result: t,
				},
				Type::TypedFuncref {
					param: TypeIndex::BOOL,
					result: TypeIndex::I32,
				},
			),
			(
				Type::TypedFuncref {
					param: t,
					result: TypeIndex::CHAR,
				},
				Type::TypedFuncref {
					param: TypeIndex::I32,
					result: TypeIndex::CHAR,
				},
			),
			(
				Type::TypedFuncref {
					param: TypeIndex::UNIT,
					result: t,
				},
				Type::TypedFuncref {
					param: TypeIndex::UNIT,
					result: TypeIndex::I32,
				},
			),
		];
		for (original, expected) in cases {
			let original = types.intern(original);
			let actual = types.substitute(original, substitution);
			assert_eq!(types.resolve(actual), &expected);
		}
	}

	#[test]
	fn substitution_inserts_replacements_without_substituting_them_again() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let u = parameter(&mut types, env, 1);
		let original = types.intern_tuple(&[t, u]);
		let replacement = types.intern_tuple(&[t, t]);
		let expected = types.intern_tuple(&[u, replacement]);

		assert_eq!(
			types.substitute(
				original,
				Substitution {
					envs: &envs,
					env,
					args: &[u, replacement]
				}
			),
			expected,
			"T -> U and U -> (T, T) are simultaneous replacements"
		);
	}

	#[test]
	fn substitution_preserves_a_projection_with_an_error_receiver() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let subject = parameter(&mut types, env, 0);
		let projection = types.intern(Type::TypeProjection {
			base: subject,
			trait_index: TraitIdx::new(0),
			assoc_type_index: AssocTypeIdx::new(0),
		});
		let result = types.substitute(
			projection,
			Substitution {
				envs: &envs,
				env,
				args: &[TypeIndex::ERROR],
			},
		);
		assert_eq!(
			types.resolve(result),
			&Type::TypeProjection {
				base: TypeIndex::ERROR,
				trait_index: TraitIdx::new(0),
				assoc_type_index: AssocTypeIdx::new(0),
			}
		);
	}

	#[test]
	fn unit_is_the_empty_tuple() {
		let mut types = TypeInterner::for_tests();
		let unit = types.intern_tuple(&[]);
		assert_eq!(unit, TypeIndex::UNIT);
	}

	#[test]
	fn substitution_preserves_leaf_types() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let leaves = [
			Type::Error,
			Type::Infer,
			Type::Never,
			Type::IntegerLiteral,
			Type::FloatLiteral,
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
			Type::Funcref,
			Type::Enum {
				enum_index: EnumIdx::new(0),
			},
			Type::Memory {
				memory_index: MemoryIdx::new(0),
			},
			Type::Global {
				global_index: GlobalIdx::new(0),
			},
			Type::Struct {
				struct_index: StructIdx::new(0),
				type_args: TypeList::EMPTY,
			},
			Type::Function {
				func_index: FunctionIdx::new(0),
				type_args: TypeList::EMPTY,
			},
		];
		for leaf in leaves {
			let ty = types.intern(leaf);
			let count = types.entries.len();
			assert_eq!(
				types.substitute(
					ty,
					Substitution {
						envs: &envs,
						env: TypeEnvIdx::new(1),
						args: &[]
					}
				),
				ty
			);
			assert_eq!(types.entries.len(), count);
		}
	}

	#[test]
	fn substitution_keeps_error_and_inference_arguments_as_supplied() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		for replacement in [TypeIndex::ERROR, TypeIndex::INFER] {
			assert_eq!(
				types.substitute(
					t,
					Substitution {
						envs: &envs,
						env,
						args: &[replacement]
					}
				),
				replacement
			);
		}
	}

	#[test]
	#[should_panic(
		expected = "substitution is missing an argument for its parameter chain"
	)]
	fn substitution_rejects_missing_arguments_for_the_targeted_frame() {
		let mut types = TypeInterner::for_tests();
		let envs = root_frames(&mut types);
		let env = TypeEnvIdx::new(1);
		let u = parameter(&mut types, env, 1);
		types.substitute(
			u,
			Substitution {
				envs: &envs,
				env,
				args: &[TypeIndex::I32],
			},
		);
	}
}
