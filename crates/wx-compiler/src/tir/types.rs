//! Type identity: the structurally hash-consed `Type` arena every resolved
//! signature and expression points into, plus `TypeEnvArena` — the
//! complementary arena answering "what does this *written name* currently
//! mean," rather than "what does this *shape* mean."
//!
//! Deliberately independent of `defs`/`signatures`' resolution machinery —
//! this module only answers identity questions, never "what type does this
//! path/expression have" or "what scope am I resolving in." It depends on
//! `defs` for `TraitIdx` (an associated-type projection names the trait
//! that declares it) and `StructIdx`/`EnumIdx`/`FunctionIdx`/`MemoryIdx`
//! (all pre-allocated in `defs.rs`'s Phase 1, for the same reason as
//! `TraitIdx`) but nothing
//! here calls into name resolution, and nothing in `defs` depends back on
//! this module — see `tir/defs.rs`'s own doc comment for why that direction
//! has to stay one-way. `TypeEnvArena` fits the same charter: given a name,
//! it hands back a `TypeIndex` already sitting in this module, with no
//! namespace lookup, no diagnostics, and no notion of `signatures.rs`'s
//! demand-driven queries at all.
//!
//! A generic-parameter frame's owner (`TypeEnvOwner`) is a dedicated enum
//! rather than a bare `ast::DefId`, so it indexes straight into the right
//! registry array (`defs.structs`, `defs.functions`, ...) without a lookup.

use std::collections::HashMap;

use crate::ast::Spanned;
use crate::diagnostics::SourceSpan;
use crate::index::index_newtype;
use crate::tir::defs::{
	DefinitionRegistry, FunctionIdx, IntrinsicDefs, TypeAliasIdx,
};
use crate::vfs::FileId;
use string_interner::symbol::SymbolU32;

use super::defs::{
	EnumIdx, InherentImplIdx, MemoryIdx, StructIdx, TraitIdx, TraitImplIdx,
};

index_newtype!(TypeIndex);

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
		struct_index: StructIdx,
		/// Encodes three states via length: non-generic struct (always
		/// empty), generic and not yet instantiated (empty), generic and
		/// instantiated (one entry per type param, e.g. `Vec<i32, u8>` →
		/// `[i32_idx, u8_idx]`).
		type_args: Box<[TypeIndex]>,
	},
	Function {
		params: Box<[TypeIndex]>,
		/// `TypeIndex::UNIT` when the written function type omits its result.
		/// A tuple result is one `TypeIndex`.
		result: TypeIndex,
	},
	/// Named function reference before coercion to a fn pointer. Encodes
	/// three states via length, same convention as `Struct::args`.
	FunctionItem {
		func_index: FunctionIdx,
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
		enum_index: EnumIdx,
	},
	Memory {
		memory_index: MemoryIdx,
		/// `TypeIndex::U32` or `TypeIndex::U64` — the memory's index type.
		size: TypeIndex,
	},
	/// One occurrence of a generic parameter declared by `owner` — every use
	/// of the same parameter across `owner`'s signature/body shares one
	/// interned instance. `param_index` is absolute across `owner`'s full
	/// visible chain: a method's own parameters start counting only after
	/// its parent impl/trait block's, mirroring how `signatures::GenericParam`
	/// slices compose (see that module's doc comment).
	///
	/// `env` is the `TypeEnvId` of the frame this param's own `EnvParam`
	/// lives in (predicted via `TypeEnvArena::next_id` before that frame
	/// exists — see its doc comment), with `param_index` local to that one
	/// frame. It's the lookup key `signatures.rs`'s bound resolution
	/// actually uses; `owner` stays alongside it for identity/diagnostics
	/// purposes (naming which item declared this param), not because
	/// anything here still needs it to find the frame.
	TypeParam {
		env: TypeEnvIdx,
		param_index: u32,
	},
	/// `M::Size` — opaque until monomorphization substitutes `M`.
	AssociatedType {
		trait_index: TraitIdx,
		assoc_name: SymbolU32,
	},
	/// `M::Size` or `A::M::Size` in a signature: a projection from a base
	/// type (a `TypeParam` or another `AssocTypeProjection`), resolved once
	/// the base is substituted with a concrete type.
	AssocTypeProjection {
		trait_index: TraitIdx,
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

// A `Copy` handle into a `TypeEnvArena` — see that type's doc comment.
index_newtype!(TypeEnvIdx);

/// One named binding inside a [`TypeEnv`] frame — a `T` from `<T: Bound>`,
/// interned as `Type::TypeParam { owner, param_index }` the moment its frame
/// is built, or `Self`, bound to whatever it means right here: a trait's own
/// abstract `TypeParam { owner: trait_id, param_index: 0 }`, or an impl's
/// already-concrete `target`. Both are just "this name resolves to this
/// `TypeIndex`" once interning is out of the way — one shape covers both, so
/// `resolve_name` never needs a separate concrete-vs-abstract case.
///
/// No bounds here — a frame is never asked for a param's bounds, and those
/// are a resolved-signature fact anyway (see `signatures.rs`'s own doc
/// comment), not an identity one.
pub(super) struct TypeParam {
	pub(super) name: Spanned<SymbolU32>,
	pub(super) ty: TypeIndex,
	pub(super) accesses: Vec<SourceSpan>,
}

/// A generic reference site's target, identified the same way dispatch and
/// every other `defs.rs`-facing lookup already is — by index into its own
/// registry array, not by `DefId` — so `name`/`file_id` can reach straight
/// into `defs.structs[..]` instead of re-deriving the index from a walk
/// through `ast_node` first. Grows one variant per item kind
/// `resolve_type_args` learns to instantiate (a type alias next).
#[derive(Clone, Copy)]
pub(super) enum TypeEnvOwner {
	Struct(StructIdx),
	Function(FunctionIdx),
	Trait(TraitIdx),
	TypeAlias(TypeAliasIdx),
	/// An impl block's own `<T>` frame — has no written name (see `name`).
	InherentImpl(InherentImplIdx),
	TraitImpl(TraitImplIdx),
}

impl TypeEnvOwner {
	pub(super) fn noun(self) -> &'static str {
		match self {
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
/// `<T>` frame; then, for an impl member, a `Self` frame rebinding it to a
/// concrete type; then the item's own explicit `<T>`.
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
/// answer "what does this written name refer to" — and, since this frame
/// persists for the rest of the compilation rather than being torn down
/// once its own item finishes, "where has it been referenced since" — while
/// a signature is being built in the first place. Being append-only is what
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

	pub(super) fn push_frame(
		&mut self,
		params: Box<[TypeParam]>,
		owner: TypeEnvOwner,
		parent: TypeEnvIdx,
	) -> TypeEnvIdx {
		let idx = TypeEnvIdx::new(u32::try_from(self.envs.len()).unwrap());
		self.envs.push(TypeEnv::Frame {
			params,
			parent,
			owner,
		});
		idx
	}

	/// Builds a new frame out of `owner`'s own declared parameter names —
	/// the "insert the identities" step, and *only* that: no bounds (a
	/// bound can reference a sibling param, so it can only resolve once the
	/// frame this returns already exists — the caller's job, strictly
	/// afterward) and no duplicate-name checking (a diagnostic concern this
	/// module has no vocabulary for, and just as cheaply done over the
	/// caller's own name list before ever calling this). Covers both a
	/// fresh `<T, U>` list and a single-entry abstract `Self` frame (trait,
	/// typeset) — anything that mints new `Type::TypeParam` identities
	/// rather than rebinding `Self` to an already-concrete type, which
	/// stays a direct `push_frame` call at its own two sites.
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
				TypeParam {
					name,
					ty,
					accesses: Vec::new(),
				}
			})
			.collect();
		self.envs.push(TypeEnv::Frame {
			params,
			parent,
			owner,
		});
		frame
	}

	#[inline]
	pub(super) fn frame(&self, env: TypeEnvIdx) -> &[TypeParam] {
		match &self.envs[usize::from(env)] {
			TypeEnv::Frame { params, .. } => params,
			_ => unreachable!(),
		}
	}

	#[inline]
	pub(super) fn frame_owner(&self, env: TypeEnvIdx) -> TypeEnvOwner {
		match &self.envs[usize::from(env)] {
			TypeEnv::Frame { owner, .. } => *owner,
			_ => unreachable!(),
		}
	}

	/// Resolves `name` (written at `span`), walking from `id` towards
	/// `Root`, recording the access against whichever entry matched. `None`
	/// means no frame in the chain declares it.
	pub(super) fn resolve(
		&mut self,
		env: TypeEnvIdx,
		name: SymbolU32,
		span: SourceSpan,
	) -> Option<TypeIndex> {
		let mut current = env;
		loop {
			match &mut self.envs[usize::from(current)] {
				TypeEnv::Root => return None,
				TypeEnv::Frame { params, parent, .. } => {
					if let Some(param) =
						params.iter_mut().find(|p| p.name.inner == name)
					{
						param.accesses.push(span);
						return Some(param.ty);
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
			(self.never, TypeIndex::NEVER),
		]
		.into_iter()
		.find_map(|(slot, ty)| (slot == Some(idx)).then_some(ty))
	}
}
