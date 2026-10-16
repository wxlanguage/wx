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

use std::hash::{BuildHasher, RandomState};

use hashbrown::HashTable;

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
	const EMPTY: TypeList = TypeList { start: 0, len: 0 };

	pub fn len(self) -> usize {
		self.len as usize
	}

	pub fn is_empty(self) -> bool {
		self.len == 0
	}

	/// This list's elements, out of the interner's `lists`.
	fn slice(self, lists: &[TypeIndex]) -> &[TypeIndex] {
		&lists[self.start as usize..][..self.len as usize]
	}
}

#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
	/// `()` is the empty tuple, pre-interned as `TypeIndex::UNIT`.
	Tuple {
		elements: TypeList,
	},
	Struct {
		struct_index: StructIdx,
		/// One argument per type parameter of the struct.
		type_args: TypeList,
	},
	/// A reference to a function, written `func(A) -> R`. It takes exactly
	/// one parameter type; a written parameter list is sugar for it:
	/// `func()` takes `()`, `func(A)` takes `A`, `func(A, B)` takes
	/// `(A, B)`, so `func((A, B))` is the same type.
	FunctionRef {
		param: TypeIndex,
		/// `TypeIndex::UNIT` when the written function type omits its result.
		result: TypeIndex,
	},
	/// A function's own zero-sized type, written with its name (`foo<i32>`).
	/// Always applied: one argument per type parameter of the function, so a
	/// generic function has no type until it is instantiated.
	Function {
		func_index: FunctionIdx,
		type_args: TypeList,
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
	/// `M::Size` — opaque until monomorphization substitutes `M`.
	AssociatedType {
		trait_index: TraitIdx,
		assoc_type_index: AssocTypeIdx,
	},
	/// `<Base as Trait>::Item`, pending normalization. The base can be
	/// concrete or abstract. `assoc_type_index` always names the trait's
	/// declaration, never an impl's value provider; substitution preserves
	/// this identity and only transforms the base.
	AssocTypeProjection {
		trait_index: TraitIdx,
		assoc_type_index: AssocTypeIdx,
		base: TypeIndex,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(test, serde(transparent))]
pub struct TypeInterner {
	entries: Vec<Type>,
	/// Every `TypeList`'s elements, back to back.
	#[cfg_attr(test, serde(skip))]
	lists: Vec<TypeIndex>,
	/// The index of every entry, found by its contents: a type's fields
	/// and its list's elements, never where the list is stored.
	#[cfg_attr(test, serde(skip))]
	index_lookup: HashTable<TypeIndex>,
	#[cfg_attr(test, serde(skip))]
	hasher: RandomState,
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
			ty => (ty, TypeList::EMPTY),
		}
	}
}

impl TypeInterner {
	/// Match a resolved impl target against one receiver. Only parameters
	/// declared by `env` are holes; parameters from every other frame are
	/// ordinary identities. All holes must be determined by the target.
	pub(super) fn match_impl_target(
		&self,
		pattern: TypeIndex,
		actual: TypeIndex,
		env: TypeEnvIdx,
		param_count: usize,
	) -> Option<Box<[TypeIndex]>> {
		let mut args = vec![None; param_count];
		self.match_pattern(pattern, actual, env, &mut args)?;
		args.into_iter().collect::<Option<Box<[TypeIndex]>>>()
	}

	fn match_pattern(
		&self,
		pattern: TypeIndex,
		actual: TypeIndex,
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
			) if *owner == env => {
				let slot = args.get_mut(*param_index as usize)?;
				match slot {
					Some(previous) if *previous != actual => None,
					Some(_) => Some(()),
					None => {
						*slot = Some(actual);
						Some(())
					}
				}
			}
			(
				Type::Struct {
					struct_index: a,
					type_args: xs,
				},
				Type::Struct {
					struct_index: b,
					type_args: ys,
				},
			) if a == b => {
				self.match_patterns(self.list(*xs), self.list(*ys), env, args)
			}
			(Type::Tuple { elements: xs }, Type::Tuple { elements: ys }) => {
				self.match_patterns(self.list(*xs), self.list(*ys), env, args)
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
			) if a == b => {
				self.match_patterns(self.list(*xs), self.list(*ys), env, args)
			}
			(
				Type::FunctionRef {
					param: xp,
					result: xr,
				},
				Type::FunctionRef {
					param: yp,
					result: yr,
				},
			) => {
				self.match_pattern(*xp, *yp, env, args)?;
				self.match_pattern(*xr, *yr, env, args)
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
				self.match_pattern(*x, *y, env, args)?;
				self.match_pattern(*xm, *ym, env, args)
			}
			(
				Type::Array {
					of: x,
					size: xs,
					memory: xm,
					ownership: xo,
				},
				Type::Array {
					of: y,
					size: ys,
					memory: ym,
					ownership: yo,
				},
			) if xs == ys && xo == yo => {
				self.match_pattern(*x, *y, env, args)?;
				self.match_pattern(*xm, *ym, env, args)
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
				self.match_pattern(*x, *y, env, args)?;
				self.match_pattern(*xm, *ym, env, args)
			}
			(
				Type::AssocTypeProjection {
					trait_index: at,
					assoc_type_index: aa,
					base: x,
				},
				Type::AssocTypeProjection {
					trait_index: bt,
					assoc_type_index: ba,
					base: y,
				},
			) if at == bt && aa == ba => self.match_pattern(*x, *y, env, args),
			_ if pattern == actual => Some(()),
			_ => None,
		}
	}

	fn match_patterns(
		&self,
		expected: &[TypeIndex],
		found: &[TypeIndex],
		env: TypeEnvIdx,
		args: &mut [Option<TypeIndex>],
	) -> Option<()> {
		if expected.len() != found.len() {
			return None;
		}
		for (pattern, actual) in
			expected.iter().copied().zip(found.iter().copied())
		{
			self.match_pattern(pattern, actual, env, args)?;
		}
		Some(())
	}

	pub fn new() -> Self {
		let mut types = Self {
			entries: Vec::new(),
			lists: Vec::new(),
			index_lookup: HashTable::new(),
			hasher: RandomState::new(),
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
		] {
			types.intern(ty);
		}
		types
	}

	/// Interns a type whose list, if it has one, is already stored.
	pub fn intern(&mut self, ty: Type) -> TypeIndex {
		let (shape, list) = ty.split_list();
		let hash = self.hasher.hash_one((shape, list.slice(&self.lists)));
		match self.find(hash, shape, list.slice(&self.lists)) {
			Some(index) => index,
			None => self.insert(hash, ty),
		}
	}

	pub fn intern_tuple(&mut self, elements: &[TypeIndex]) -> TypeIndex {
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

	fn push_list(&mut self, elements: &[TypeIndex]) -> TypeList {
		let list = TypeList {
			start: u32::try_from(self.lists.len())
				.expect("type interner exceeded u32 list capacity"),
			len: u32::try_from(elements.len()).unwrap(),
		};
		self.lists.extend_from_slice(elements);
		list
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
		self.entries.push(ty);
		let Self {
			entries,
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
		match *self.resolve(ty) {
			Type::TypeParam { env, param_index } if env == substitution.env => {
				*substitution.args.get(param_index as usize).expect(
					"substitution is missing an argument for its parameter frame",
				)
			}
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
			Type::FunctionRef { param, result } => {
				let next_param = self.substitute(param, substitution);
				let next_result = self.substitute(result, substitution);
				if next_param == param && next_result == result {
					ty
				} else {
					self.intern(Type::FunctionRef {
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
				size,
				memory,
				ownership,
			} => {
				let next_of = self.substitute(of, substitution);
				let next_memory = self.substitute(memory, substitution);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.intern(Type::Array {
						of: next_of,
						size,
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
			Type::AssocTypeProjection {
				base,
				trait_index,
				assoc_type_index,
			} => {
				let next_base = self.substitute(base, substitution);
				if next_base == base {
					ty
				} else {
					self.intern(Type::AssocTypeProjection {
						base: next_base,
						trait_index,
						assoc_type_index,
					})
				}
			}
			Type::Error
			| Type::Infer
			| Type::Never
			| Type::Integer
			| Type::Float
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
			| Type::Bool
			| Type::Char
			| Type::Enum { .. }
			| Type::Memory { .. }
			| Type::Global { .. }
			| Type::AssociatedType { .. }
			| Type::TypeParam { .. } => ty,
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

impl Default for TypeInterner {
	fn default() -> Self {
		Self::new()
	}
}

// A `Copy` handle into a `TypeEnvArena` — see that type's doc comment.
index_newtype!(TypeEnvIdx);

/// Replacements for all parameters in one declaring frame. `args[i]`
/// replaces `TypeParam { env, param_index: i }`; other frames are untouched.
/// Callers supply one argument per parameter in `env`, in declaration order.
/// This borrows an instantiation's arguments without changing the original
/// lexical environment. Replacement types may themselves contain parameters.
#[derive(Clone, Copy)]
pub(super) struct Substitution<'a> {
	pub(super) env: TypeEnvIdx,
	pub(super) args: &'a [TypeIndex],
}

/// One generic parameter of a [`TypeEnv`] frame — a `T` from `<T: Bound>`,
/// or a trait's or typeset's own `Self` — interned as
/// `Type::TypeParam { env, param_index }` the moment its frame is built. An
/// impl's `Self` is not a parameter: it names the impl's target, found
/// through the impl's frame (`TypeEnvArena::enclosing_impl`).
///
/// No bounds here — a frame is never asked for a param's bounds, and those
/// are a resolved-signature fact anyway (see `signatures.rs`'s own doc
/// comment), not an identity one.
pub(super) struct TypeParam {
	pub(super) name: Spanned<SymbolU32>,
	pub(super) ty: TypeIndex,
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
#[derive(Clone, Copy)]
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
enum TypeEnv {
	Root,
	Frame {
		owner: TypeEnvOwner,
		params: Box<[TypeParam]>,
		parent: TypeEnvIdx,
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
	/// before the frame exists, predicted via `next_id` — the id has to be
	/// knowable ahead of building the `params` that will fill it.
	#[inline]
	pub(super) fn push_param_frame(
		&mut self,
		types: &mut TypeInterner,
		owner: TypeEnvOwner,
		parent: TypeEnvIdx,
		names: impl IntoIterator<Item = Spanned<SymbolU32>>,
	) -> TypeEnvIdx {
		let frame = TypeEnvIdx::new(u32::try_from(self.envs.len()).unwrap());
		let params: Box<[TypeParam]> = names
			.into_iter()
			.enumerate()
			.map(|(index, name)| {
				let ty = types.intern(Type::TypeParam {
					env: frame,
					param_index: u32::try_from(index).unwrap(),
				});
				TypeParam { name, ty }
			})
			.collect();
		self.envs.push(TypeEnv::Frame {
			params,
			parent,
			owner,
		});
		frame
	}

	/// A declaration without generics has no frame of its own and stores
	/// `ROOT`, which declares no parameters.
	#[inline]
	pub(super) fn params(&self, env: TypeEnvIdx) -> &[TypeParam] {
		match &self.envs[usize::from(env)] {
			TypeEnv::Frame { params, .. } => params,
			TypeEnv::Root => &[],
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
				TypeEnv::Frame { params, parent, .. } => {
					if let Some(index) =
						params.iter().position(|p| p.name.inner == name)
					{
						return Some((current, u32::try_from(index).unwrap()));
					}
					current = *parent;
				}
			}
		}
	}
}

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

	// Pre-allocated indices for primitive types. The `TypeInterner` reserves
	// these slots at startup so comparisons like `ty == TypeIndex::U32` work
	// without a pool lookup.
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

impl IntrinsicDefs {
	/// `idx`'s real identity as a primitive type, if it has one. `None` for
	/// the common case — an ordinary, non-primitive alias — and `Some` only
	/// for the handful of reserved names (`u8`, `char`, `never`, ...) that
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
			(self.bool, TypeIndex::BOOL),
			(self.char, TypeIndex::CHAR),
		]
		.into_iter()
		.find_map(|(slot, ty)| (slot == Some(idx)).then_some(ty))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::ast::Ownership;

	fn parameter(
		types: &mut TypeInterner,
		env: TypeEnvIdx,
		param_index: u32,
	) -> TypeIndex {
		types.intern(Type::TypeParam { env, param_index })
	}

	#[test]
	fn substitution_replaces_only_the_targeted_frames_parameters() {
		let mut types = TypeInterner::new();
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
		let item = types.intern(Type::AssocTypeProjection {
			trait_index: TraitIdx::new(0),
			assoc_type_index: AssocTypeIdx::new(0),
			base: wrapper,
		});
		let next = types.intern(Type::AssocTypeProjection {
			trait_index: TraitIdx::new(1),
			assoc_type_index: AssocTypeIdx::new(1),
			base: item,
		});
		let pointer = types.intern(Type::Pointer {
			to: next,
			memory,
			ownership: Ownership::Shared,
		});
		let array = types.intern(Type::Array {
			of: pointer,
			size: 7,
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
		types.intern(Type::FunctionRef {
			param: tuple,
			result: next,
		})
	}

	#[test]
	fn substitution_traverses_nested_types_without_normalizing_projections() {
		let mut types = TypeInterner::new();
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
		let mut types = TypeInterner::new();
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let m = parameter(&mut types, env, 1);
		let original = nested_signature(&mut types, t, m);
		let count = types.entries.len();

		assert_eq!(
			types.substitute(
				original,
				Substitution {
					env: TypeEnvIdx::new(2),
					args: &[]
				},
			),
			original
		);
		assert_eq!(
			types.substitute(original, Substitution { env, args: &[t, m] }),
			original
		);
		assert_eq!(types.entries.len(), count);
	}

	#[test]
	fn substitution_preserves_unchanged_list_elements_around_late_changes() {
		let mut types = TypeInterner::new();
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let u = parameter(&mut types, env, 1);
		let substitution = Substitution {
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
		let mut types = TypeInterner::new();
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let substitution = Substitution {
			env,
			args: &[TypeIndex::I32],
		};
		let cases = [
			(
				Type::FunctionRef {
					param: TypeIndex::BOOL,
					result: t,
				},
				Type::FunctionRef {
					param: TypeIndex::BOOL,
					result: TypeIndex::I32,
				},
			),
			(
				Type::FunctionRef {
					param: t,
					result: TypeIndex::CHAR,
				},
				Type::FunctionRef {
					param: TypeIndex::I32,
					result: TypeIndex::CHAR,
				},
			),
			(
				Type::FunctionRef {
					param: TypeIndex::UNIT,
					result: t,
				},
				Type::FunctionRef {
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
		let mut types = TypeInterner::new();
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		let u = parameter(&mut types, env, 1);
		let original = types.intern_tuple(&[t, u]);
		let replacement = types.intern_tuple(&[t]);
		let expected = types.intern_tuple(&[u, replacement]);

		assert_eq!(
			types.substitute(
				original,
				Substitution {
					env,
					args: &[u, replacement]
				}
			),
			expected,
			"T -> U and U -> (T,) are simultaneous replacements"
		);
	}

	#[test]
	fn substitution_preserves_a_projection_with_an_error_receiver() {
		let mut types = TypeInterner::new();
		let env = TypeEnvIdx::new(1);
		let subject = parameter(&mut types, env, 0);
		let projection = types.intern(Type::AssocTypeProjection {
			base: subject,
			trait_index: TraitIdx::new(0),
			assoc_type_index: AssocTypeIdx::new(0),
		});
		let result = types.substitute(
			projection,
			Substitution {
				env,
				args: &[TypeIndex::ERROR],
			},
		);
		assert_eq!(
			types.resolve(result),
			&Type::AssocTypeProjection {
				base: TypeIndex::ERROR,
				trait_index: TraitIdx::new(0),
				assoc_type_index: AssocTypeIdx::new(0),
			}
		);
	}

	#[test]
	fn unit_is_the_empty_tuple() {
		let mut types = TypeInterner::new();
		let unit = types.intern_tuple(&[]);
		assert_eq!(unit, TypeIndex::UNIT);
	}

	#[test]
	fn substitution_preserves_leaf_types() {
		let mut types = TypeInterner::new();
		let leaves = [
			Type::Error,
			Type::Infer,
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
			Type::Enum {
				enum_index: EnumIdx::new(0),
			},
			Type::Memory {
				memory_index: MemoryIdx::new(0),
			},
			Type::Global {
				global_index: GlobalIdx::new(0),
			},
			Type::AssociatedType {
				trait_index: TraitIdx::new(0),
				assoc_type_index: AssocTypeIdx::new(0),
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
		let mut types = TypeInterner::new();
		let env = TypeEnvIdx::new(1);
		let t = parameter(&mut types, env, 0);
		for replacement in [TypeIndex::ERROR, TypeIndex::INFER] {
			assert_eq!(
				types.substitute(
					t,
					Substitution {
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
		expected = "substitution is missing an argument for its parameter frame"
	)]
	fn substitution_rejects_missing_arguments_for_the_targeted_frame() {
		let mut types = TypeInterner::new();
		let env = TypeEnvIdx::new(1);
		let u = parameter(&mut types, env, 1);
		types.substitute(
			u,
			Substitution {
				env,
				args: &[TypeIndex::I32],
			},
		);
	}
}
