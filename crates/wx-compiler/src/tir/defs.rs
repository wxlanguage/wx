//! Phase 1 — the prescan. Walks every item in every file, allocates its TIR
//! entry and claims its name, and records it in `ast_nodes` for the
//! demand-driven signature pass to pick up. Import and export names are
//! decoded and interned here; no body checking happens in this phase.

// use super::*;

use std::collections::HashMap;
use std::ops::Range;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{self, Keyword, Spanned, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	index::index_newtype,
	small_vec::SmallVec,
	tir::{
		imports::ImportResolver, literals::unescape_string_literal,
		resolutions::NameResolutions,
	},
	vfs::{FileId, Files, Package, PackageId},
};

// `'ast` (borrowed by `ast_nodes`) is kept separate from `'ctx`
// (`diagnostics`/`strings`/`files`) so that building a registry doesn't pin
// down how long the caller's diagnostics list or string interner stay
// borrowed — only `packages` needs to outlive `ast_nodes`, which `build()`
// hands back separately from the (lifetime-free) `DefinitionRegistry`
// itself, for Phase 2's demand-driven signature pass to walk.
struct DefinitionRegistryBuilder<'ast, 'ctx> {
	diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
	strings: &'ctx mut StringInterner,
	files: &'ctx Files,
	/// The package a builtin name (`u8`, `Add`, ...) is only recognized in.
	/// Always present, from `CompilationUnit::stdlib_package`.
	stdlib_package: PackageId,
	root_package: PackageId,
	/// What a `crate "key" as alias;` item looks its key up in: each
	/// package's manifest-declared dependencies.
	packages: &'ast [Package],

	namespaces: Namespaces,
	modules: Vec<ModuleDef>,
	imports: Vec<ImportDef>,
	ast_nodes: Vec<AstEntry<'ast>>,
	exports: HashMap<SymbolU32, ExportEntrySource>,
	traits: Vec<TraitDef>,
	trait_impls: Vec<TraitImplDef>,
	inherent_impls: Vec<InherentImplDef>,
	structs: Vec<StructDef>,
	type_aliases: Vec<TypeAliasDef>,
	enums: Vec<EnumDef>,
	typesets: Vec<TypesetDef>,
	functions: Vec<FunctionDef>,
	memories: Vec<MemoryDef>,
	globals: Vec<GlobalDef>,
	constants: Vec<ConstDef>,
	assoc_types: Vec<AssocTypeDef>,
	use_items: Vec<UseItemDef>,
	use_paths: Vec<UsePathSegment>,
	intrinsics: IntrinsicDefs,
	// Keyed by local (alias-or-original) name, not the name as written at the `use` site.
	pending_named_imports: HashMap<(Scope, SymbolU32), SmallVec<UseItemIndex>>,
	/// Every glob `use` item — `pub` or not — grouped by the namespace it's
	/// *declared* in — no name dimension, unlike `pending_named_imports`,
	/// since a glob doesn't claim one. Lets glob resolution find "what does
	/// this namespace glob-import" without scanning every `use_items` entry.
	/// Covers private globs too (not just `pub` re-exports) because
	/// `imports::compute_glob_item` chases *every* glob a target declares
	/// before adding its own edge — the graph `indirect_lookup` walks at
	/// lookup time includes private edges just as much as `pub` ones, so
	/// cycle detection has to see the whole graph, not just its `pub`
	/// subset.
	pending_glob_targets: HashMap<Scope, SmallVec<UseItemIndex>>,
}

index_newtype!(UsePathIndex);
index_newtype!(UseItemIndex);
index_newtype!(CrateItemIdx);

/// One `crate "key" as alias;` item: an instantiation of a package.
///
/// Every item is its own instantiation site, so the same package named by
/// two items (`crate "math" as a; crate "math" as b;`) is instantiated
/// twice. Resolution does not yet tell the instances apart: both aliases
/// bind the package's one namespace. This list is what a stage that must
/// (emitting a separate copy of the package per item) walks instead.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct CrateItemDef {
	pub file_id: FileId,
	/// The scope the item was written in, where `alias` is bound.
	pub namespace: Scope,
	pub pub_span: Option<TextSpan>,
	/// The manifest key, decoded; the span covers the literal as written.
	pub package_name: Spanned<SymbolU32>,
	pub alias: Spanned<SymbolU32>,
	/// The package `package_name` names, or `None` when the manifest
	/// declares no such key (which is reported where the item is scanned).
	/// Until instances are told apart, what the alias leads into is this
	/// package's own namespace.
	pub package: Option<PackageId>,
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct UsePathSegment {
	pub(super) segment: Spanned<SymbolU32>,
	pub(super) parent: Option<UsePathIndex>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub enum UseItemKind {
	Name {
		name: Spanned<SymbolU32>,
		alias: Option<Spanned<SymbolU32>>,
		prefix: Option<UsePathIndex>,
	},
	Glob {
		path: UsePathIndex,
		/// The `x::*` span — the path through the star, never the `use`
		/// keyword — for diagnostics that need to blame this glob
		/// specifically. For a glob nested in a group (`use a::{b::*, c}`)
		/// this covers only `b::*`, since a span reaching back to `a`
		/// wouldn't be a contiguous range of source.
		span: TextSpan,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct UseItemDef {
	pub namespace: Scope,
	pub pub_span: Option<TextSpan>,
	pub kind: UseItemKind,
}

/// Which of a namespace's two sets of names a binding lives in: types or
/// values. One name can be bound once in each, as a struct is (its type and
/// its constructor).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum Tier {
	Type,
	Value,
}

impl Tier {
	pub(super) fn noun(self) -> &'static str {
		match self {
			Tier::Type => "type",
			Tier::Value => "value",
		}
	}
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct BindingKey {
	pub(super) tier: Tier,
	pub(super) symbol: SymbolU32,
}

impl BindingKey {
	pub(super) fn new(tier: Tier, symbol: SymbolU32) -> Self {
		Self { tier, symbol }
	}

	pub(super) fn ty(symbol: SymbolU32) -> Self {
		Self {
			tier: Tier::Type,
			symbol,
		}
	}

	pub(super) fn value(symbol: SymbolU32) -> Self {
		Self {
			tier: Tier::Value,
			symbol,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TraitDef {
	/// The typeset this trait was generated for, whose signature query builds
	/// it; `None` for a written trait.
	pub typeset: Option<TypesetIdx>,
	pub file_id: FileId,
	pub namespace: Scope,
	pub pub_span: Option<TextSpan>,
	pub name: Spanned<SymbolU32>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIdx>,
	pub members: Vec<TraitMemberDef>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TraitImplDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub members: Vec<TraitMemberDef>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIdx>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct InherentImplDef {
	pub file_id: FileId,
	pub namespace: Scope,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIdx>,
	pub members: Vec<InherentMemberDef>,
}

/// Field identity only (names, `pub_span`, lookup) — field *types* are
/// `signatures::StructSignature::field_types`, index-aligned with `fields`.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct StructDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
	pub fields: Box<[FieldDef]>,
	/// The named fields by name, each to its first occurrence.
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub lookup: HashMap<SymbolU32, FieldIdx>,
}

impl StructDef {
	/// Whether every field has a name: only then can the struct be
	/// constructed (`P({ x: 1, y: 2 })`) or destructured by name.
	pub fn is_fully_named(&self) -> bool {
		self.fields.iter().all(|field| field.name.is_some())
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct FieldDef {
	/// `None` for a positional field.
	pub name: Option<Spanned<SymbolU32>>,
	pub pub_span: Option<TextSpan>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct EnumDef {
	pub file_id: FileId,
	pub parent_namespace: Scope,
	pub name: Spanned<SymbolU32>,
	/// The enum's variants, in written order, a duplicate name included: a
	/// variant is a constant of the enum's type, and an enum's variants are
	/// one run of `constants`, so a variant's position is what its implicit
	/// value counts from.
	///
	/// Invariant: the run is contiguous. The enum's scan pushes all of its
	/// variants with one `extend` and nothing pushes a constant in between, so
	/// the variant before `c` is `c - 1` while that is still in the range. Any
	/// change to how variants are pushed must keep them together.
	pub variants: Range<ConstIdx>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TypeAliasDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
}

/// `typeset X: A + B { m1, m2 }` — `trait_index` is a generated trait with
/// no AST node of its own (`TraitDef::typeset` names this typeset). Its
/// data, the supertraits from `: A + B`, is written by this typeset's
/// signature query, so forcing the trait means forcing `DefId::Typeset`.
/// `member_impls` is index-aligned with the AST's own `members` list: one
/// generated `impl <trait_index> for <member>` per written member, filled in
/// with the member's resolved type by that same query.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct TypesetDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
	pub trait_index: TraitIdx,
	pub member_impls: Box<[TraitImplIdx]>,
}

/// Shared by a free function, a trait member, and an impl method — one
/// arena, the same reason `signatures::FunctionSignature` covers all
/// three. Field *types* stay in that struct, index-aligned with `params`
/// here, same split as `StructDef`/`StructSignature`.
///
/// Every function is its own type, so each has `function_impls`, its
/// synthetic `impl Call` and `impl Function`.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct FunctionDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub owner: FunctionOwner,
	pub name: Spanned<SymbolU32>,
	pub params: Box<[Spanned<SymbolU32>]>,
	pub function_impls: FunctionImpls,
}

/// Where a function is declared: directly in a scope (a free or imported
/// function), or as a member of a trait or impl. A trait's declaration is
/// the one whose type normalizes to an impl member's once `Self` is known.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum FunctionOwner {
	Free,
	Trait(TraitIdx),
	InherentImpl(InherentImplIdx),
	TraitImpl(TraitImplIdx),
}

/// A function's synthetic `impl Call for <function>`, which holds `Args` and
/// `Result`, and its `impl Function for <function>`, which declares nothing
/// (like a `global mut`'s `GlobalMut` impl). Pre-allocated for the same
/// reason as `MemoryDef`'s own fields.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct FunctionImpls {
	pub call_impl_index: TraitImplIdx,
	pub args_assoc_type_index: AssocTypeIdx,
	pub result_assoc_type_index: AssocTypeIdx,
	pub function_impl_index: TraitImplIdx,
}

/// Identity shared by local and imported memories. The written size
/// expression remains in the AST for later resolution.
///
/// `trait_impl_index`/`size_assoc_type_index` are this memory's synthetic
/// `impl Memory for <memory>` — pre-allocated unconditionally, here. Like a
/// typeset's generated impls (see `TypesetDef`), nothing forces these
/// through a query of their own: they're populated as a side effect of
/// resolving this memory's own signature. Allocating the slot never depends
/// on `IntrinsicDefs::memory` — it's just an index and a name, no reference
/// to the `Memory` trait itself. That trait is only needed later, to bucket
/// this impl for dispatch (`impls.rs`); if std never declared one, that's
/// where it's diagnosed as the broken-stdlib error it is, not something
/// every reader of this struct has to keep re-checking for.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct MemoryDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
	pub trait_impl_index: TraitImplIdx,
	pub size_assoc_type_index: AssocTypeIdx,
}

/// Identity shared by local and imported globals. The written value type
/// remains in the AST for later resolution (and may be entirely absent —
/// `global x = 0;` infers it from the value, which needs the body phase
/// this architecture doesn't have yet).
///
/// `trait_impl_index`/`value_assoc_type_index` are this global's synthetic
/// `impl Global for <global>`, unconditionally pre-allocated for the same
/// reason as `MemoryDef`'s own fields. `mut_trait_impl_index` is the
/// additional `impl GlobalMut for <global>` a `global mut` declaration also
/// gets (`GlobalMut` declares no members of its own — an empty impl is
/// enough to make it a dispatch candidate) — genuinely absent for a
/// non-`mut` global, unlike the other two fields.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct GlobalDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
	pub trait_impl_index: TraitImplIdx,
	pub value_assoc_type_index: AssocTypeIdx,
	pub mut_trait_impl_index: Option<TraitImplIdx>,
}

/// Identity of a free, trait, or impl constant. Its type and value are
/// resolved in later phases.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct ConstDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
}

/// Each trait declaration and each impl definition has its own identity.
/// Declared bounds and impl target types remain in the AST for resolution.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct AssocTypeDef {
	pub file_id: FileId,
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
}

index_newtype!(LocalDefIdx);
index_newtype!(MemberIdx);
index_newtype!(ModuleIdx);
index_newtype!(ImportIdx);
index_newtype!(TraitIdx);
index_newtype!(InherentImplIdx);
index_newtype!(TraitImplIdx);
index_newtype!(StructIdx);
index_newtype!(FieldIdx);
index_newtype!(EnumIdx);
index_newtype!(TypesetIdx);
index_newtype!(TypeAliasIdx);
index_newtype!(FunctionIdx);
index_newtype!(MemoryIdx);
index_newtype!(GlobalIdx);
index_newtype!(ConstIdx);
index_newtype!(AssocTypeIdx);

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TraitMemberDef {
	pub kind: MemberKind,
	pub span: TextSpan,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct InherentMemberDef {
	pub kind: MemberKind,
	pub visibility: Visibility,
	pub span: TextSpan,
}

impl LocalDefIdx {
	/// each module has a `self` binding which is the first binding in the list of it's bindings
	/// other modules can use it to reference it, for example `super`
	pub(super) const SELF: Self = LocalDefIdx(0);
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct AstEntry<'ast> {
	pub(super) file_id: FileId,
	/// The scope the item is written in, where its signature resolves. For
	/// an imported declaration that is the scope around its import block;
	/// the block itself is named by the entry (`AstNodeRef::Imported*`).
	pub(super) namespace: Scope,
	pub(super) node: AstNodeRef<'ast>,
}

#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum AstNodeRef<'ast> {
	Function {
		item: &'ast ast::Item,
		func_index: FunctionIdx,
	},
	Struct {
		struct_index: StructIdx,
		item: &'ast ast::Item,
	},
	Enum {
		enum_index: EnumIdx,
		item: &'ast ast::Item,
	},
	Global {
		global_index: GlobalIdx,
		item: &'ast ast::Item,
	},
	Memory {
		memory_index: MemoryIdx,
		item: &'ast ast::Item,
	},
	Constant {
		const_index: ConstIdx,
		item: &'ast ast::Item,
	},
	TypeSet {
		typeset_index: TypesetIdx,
		item: &'ast ast::Item,
	},
	TypeAlias {
		item: &'ast ast::Item,
		type_alias_index: TypeAliasIdx,
	},
	Trait {
		trait_index: TraitIdx,
		item: &'ast ast::Item,
	},
	TraitFunction {
		trait_index: TraitIdx,
		item: &'ast ast::TraitItem,
		function_index: FunctionIdx,
	},
	TraitConst {
		const_index: ConstIdx,
		trait_index: TraitIdx,
		item: &'ast ast::TraitItem,
	},
	EnumVariant {
		const_index: ConstIdx,
		enum_index: EnumIdx,
		item: &'ast ast::EnumVariant,
	},
	TraitAssocType {
		assoc_type_index: AssocTypeIdx,
		trait_index: TraitIdx,
		item: &'ast ast::TraitItem,
	},
	TraitImplBlock {
		item: &'ast ast::Item,
		block_index: TraitImplIdx,
	},
	TraitImplFunction {
		item: &'ast ast::ImplItem,
		block_index: TraitImplIdx,
		function_index: FunctionIdx,
	},
	TraitImplConstant {
		const_index: ConstIdx,
		item: &'ast ast::ImplItem,
		block_index: TraitImplIdx,
	},
	TraitImplAssocType {
		assoc_type_index: AssocTypeIdx,
		item: &'ast ast::ImplItem,
		block_index: TraitImplIdx,
	},
	InherentImplBlock {
		item: &'ast ast::Item,
		block_index: InherentImplIdx,
	},
	InherentImplFunction {
		item: &'ast ast::ImplItem,
		block_index: InherentImplIdx,
		function_index: FunctionIdx,
	},
	InherentImplConst {
		const_index: ConstIdx,
		item: &'ast ast::ImplItem,
		block_index: InherentImplIdx,
	},
	ImportedMemory {
		memory_index: MemoryIdx,
		import_index: ImportIdx,
		decl: &'ast ast::ImportDeclaration,
	},
	ImportedFunction {
		function_index: FunctionIdx,
		import_index: ImportIdx,
		decl: &'ast ast::ImportDeclaration,
	},
	ImportedGlobal {
		global_index: GlobalIdx,
		import_index: ImportIdx,
		decl: &'ast ast::ImportDeclaration,
	},
}

impl AstNodeRef<'_> {
	/// The declaration this entry writes.
	pub(super) fn def_id(&self) -> DefId {
		match *self {
			Self::Function { func_index, .. } => DefId::Function(func_index),
			Self::TraitFunction { function_index, .. }
			| Self::TraitImplFunction { function_index, .. }
			| Self::InherentImplFunction { function_index, .. }
			| Self::ImportedFunction { function_index, .. } => {
				DefId::Function(function_index)
			}
			Self::Struct { struct_index, .. } => DefId::Struct(struct_index),
			Self::Enum { enum_index, .. } => DefId::Enum(enum_index),
			Self::Global { global_index, .. }
			| Self::ImportedGlobal { global_index, .. } => DefId::Global(global_index),
			Self::Memory { memory_index, .. }
			| Self::ImportedMemory { memory_index, .. } => DefId::Memory(memory_index),
			Self::Constant { const_index, .. }
			| Self::TraitConst { const_index, .. }
			| Self::TraitImplConstant { const_index, .. }
			| Self::InherentImplConst { const_index, .. }
			| Self::EnumVariant { const_index, .. } => DefId::Const(const_index),
			Self::TypeSet { typeset_index, .. } => {
				DefId::Typeset(typeset_index)
			}
			Self::TypeAlias {
				type_alias_index, ..
			} => DefId::TypeAlias(type_alias_index),
			Self::Trait { trait_index, .. } => DefId::Trait(trait_index),
			Self::TraitAssocType {
				assoc_type_index, ..
			}
			| Self::TraitImplAssocType {
				assoc_type_index, ..
			} => DefId::AssocType(assoc_type_index),
			Self::TraitImplBlock { block_index, .. } => {
				DefId::TraitImpl(block_index)
			}
			Self::InherentImplBlock { block_index, .. } => {
				DefId::InherentImpl(block_index)
			}
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct ExportEntrySource {
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
	pub external_span: SourceSpan,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct DefinitionRegistry {
	pub stdlib_package: PackageId,
	pub root_package: PackageId,
	pub namespaces: Namespaces,
	/// The scope each file's top-level items live in, indexed by `FileId`.
	#[cfg_attr(test, serde(skip))]
	pub file_namespaces: Vec<Scope>,
	pub modules: Vec<ModuleDef>,
	pub imports: Vec<ImportDef>,
	/// Selected crate's compilation exports, keyed by decoded external name.
	pub exports: HashMap<SymbolU32, ExportEntrySource>,
	pub traits: Vec<TraitDef>,
	pub trait_impls: Vec<TraitImplDef>,
	pub inherent_impls: Vec<InherentImplDef>,
	pub structs: Vec<StructDef>,
	pub enums: Vec<EnumDef>,
	pub typesets: Vec<TypesetDef>,
	pub functions: Vec<FunctionDef>,
	pub memories: Vec<MemoryDef>,
	pub globals: Vec<GlobalDef>,
	pub constants: Vec<ConstDef>,
	pub assoc_types: Vec<AssocTypeDef>,
	pub type_aliases: Vec<TypeAliasDef>,
	pub use_items: Vec<UseItemDef>,
	pub use_paths: Vec<UsePathSegment>,
	/// The `DefKey` of every language builtin recognized by name in the
	/// stdlib package — primitive types (`u8`, `char`, ...) and
	/// operator traits (`Add`, `PartialEq`, ...) alike. `None` for any name
	/// prescan never found declared there. No `#[intrinsic]` marker is
	/// involved: recognition is implicit — a reserved name, of the right
	/// declaration kind, declared in the stdlib package *is* that builtin.
	/// This is std's own responsibility to get right, same as any other
	/// name collision within a single package. Same epistemic status as
	/// everything else on this registry: what was recorded, not a judgment
	/// about completeness.
	pub intrinsics: IntrinsicDefs,
}

/// One struct rather than one per kind — the recognized-name list only
/// needs to be written once — but [`IntrinsicDefs::type_slot_mut`] and
/// [`IntrinsicDefs::trait_slot_mut`] are kept as two separate lookups
/// (rather than one covering all fields) so a type alias and a trait can
/// never contend for the same slot just because they happen to share a
/// name — e.g. a stray `type Add;` in std can't clobber the `Add` trait's
/// entry, since only `trait_slot_mut` ever resolves `"Add"`.
#[derive(Default)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct IntrinsicDefs {
	pub u8: Option<TypeAliasIdx>,
	pub i8: Option<TypeAliasIdx>,
	pub u16: Option<TypeAliasIdx>,
	pub i16: Option<TypeAliasIdx>,
	pub u32: Option<TypeAliasIdx>,
	pub i32: Option<TypeAliasIdx>,
	pub u64: Option<TypeAliasIdx>,
	pub i64: Option<TypeAliasIdx>,
	pub f32: Option<TypeAliasIdx>,
	pub f64: Option<TypeAliasIdx>,
	pub bool: Option<TypeAliasIdx>,
	pub char: Option<TypeAliasIdx>,
	pub add: Option<TraitIdx>,
	pub sub: Option<TraitIdx>,
	pub mul: Option<TraitIdx>,
	pub div: Option<TraitIdx>,
	pub rem: Option<TraitIdx>,
	pub neg: Option<TraitIdx>,
	pub bitand: Option<TraitIdx>,
	pub bitor: Option<TraitIdx>,
	pub bitxor: Option<TraitIdx>,
	pub shl: Option<TraitIdx>,
	pub shr: Option<TraitIdx>,
	pub bitnot: Option<TraitIdx>,
	pub not: Option<TraitIdx>,
	pub partial_eq: Option<TraitIdx>,
	pub partial_ord: Option<TraitIdx>,
	pub memory: Option<TraitIdx>,
	pub global: Option<TraitIdx>,
	pub global_mut: Option<TraitIdx>,
	pub call: Option<TraitIdx>,
	pub function: Option<TraitIdx>,
	pub value_type: Option<TraitIdx>,
}

impl IntrinsicDefs {
	/// The mutable slot for `name` if it's one of the recognized primitive
	/// type names — the one place that list is written.
	fn type_slot_mut(
		&mut self,
		name: &str,
	) -> Option<&mut Option<TypeAliasIdx>> {
		Some(match name {
			"u8" => &mut self.u8,
			"i8" => &mut self.i8,
			"u16" => &mut self.u16,
			"i16" => &mut self.i16,
			"u32" => &mut self.u32,
			"i32" => &mut self.i32,
			"u64" => &mut self.u64,
			"i64" => &mut self.i64,
			"f32" => &mut self.f32,
			"f64" => &mut self.f64,
			"bool" => &mut self.bool,
			"char" => &mut self.char,
			_ => return None,
		})
	}

	/// The mutable slot for `name` if it's one of the recognized operator
	/// trait names — the one place that list is written.
	fn trait_slot_mut(&mut self, name: &str) -> Option<&mut Option<TraitIdx>> {
		Some(match name {
			"Add" => &mut self.add,
			"Sub" => &mut self.sub,
			"Mul" => &mut self.mul,
			"Div" => &mut self.div,
			"Rem" => &mut self.rem,
			"Neg" => &mut self.neg,
			"BitAnd" => &mut self.bitand,
			"BitOr" => &mut self.bitor,
			"BitXor" => &mut self.bitxor,
			"Shl" => &mut self.shl,
			"Shr" => &mut self.shr,
			"BitNot" => &mut self.bitnot,
			"Not" => &mut self.not,
			"PartialEq" => &mut self.partial_eq,
			"PartialOrd" => &mut self.partial_ord,
			"Memory" => &mut self.memory,
			"Global" => &mut self.global,
			"GlobalMut" => &mut self.global_mut,
			"Call" => &mut self.call,
			"Function" => &mut self.function,
			"ValueType" => &mut self.value_type,
			_ => return None,
		})
	}
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum Visibility {
	Public,
	Private,
}

impl From<Option<TextSpan>> for Visibility {
	fn from(value: Option<TextSpan>) -> Self {
		match value {
			Some(_) => Visibility::Public,
			None => Visibility::Private,
		}
	}
}

impl Visibility {
	/// The narrower of the two — a re-export can never be more visible than
	/// what it re-exports, so a `use`'s own visibility and the visibility of
	/// whatever it resolved to both cap the installed binding's visibility.
	pub(super) fn cap(self, other: Visibility) -> Visibility {
		match (self, other) {
			(Visibility::Public, Visibility::Public) => Visibility::Public,
			_ => Visibility::Private,
		}
	}
}

/// A declaration: the arena it lives in and its index there (an enum
/// variant is a constant). Assigned by the
/// prescan, which is what decides what a declaration is; a generated one (a
/// typeset's trait and impls, a memory's or global's impl) is built by the
/// signature query of the declaration that generates it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DefId {
	Struct(StructIdx),
	Enum(EnumIdx),
	Trait(TraitIdx),
	Typeset(TypesetIdx),
	TypeAlias(TypeAliasIdx),
	Function(FunctionIdx),
	Const(ConstIdx),
	Memory(MemoryIdx),
	Global(GlobalIdx),
	AssocType(AssocTypeIdx),
	TraitImpl(TraitImplIdx),
	InherentImpl(InherentImplIdx),
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum DefKind {
	Module(ModuleIdx),
	Import(ImportIdx),
	Package(PackageId),
	/// A `crate "key" as alias;` item, the name it binds. What a path
	/// continues into is the package it instantiates, which only
	/// [`Namespaces::entered_by`] can say.
	Crate(CrateItemIdx),
	Enum(EnumIdx),
	EnumVariant(ConstIdx),
	Struct(StructIdx),
	Memory(MemoryIdx),
	Trait(TraitIdx),
	TypeSet(TypesetIdx),
	Global(GlobalIdx),
	Function(FunctionIdx),
	Const(ConstIdx),
	TraitAssocType(AssocTypeIdx),
	TypeAlias(TypeAliasIdx),
}

impl DefKind {
	/// What kind of symbol this is, for diagnostics.
	pub fn noun(self) -> &'static str {
		match self {
			DefKind::Module(_) => "module",
			DefKind::Import(_) => "import block",
			DefKind::Package(_) => "package",
			DefKind::Crate(_) => "crate",
			DefKind::Enum(_) => "enum",
			DefKind::EnumVariant(_) => "enum variant",
			DefKind::Struct(_) => "struct",
			DefKind::Memory(_) => "memory",
			DefKind::Trait(_) => "trait",
			DefKind::TypeSet(_) => "typeset",
			DefKind::Global(_) => "global",
			DefKind::Function(_) => "function",
			DefKind::Const(_) => "constant",
			DefKind::TraitAssocType(_) => "associated type",
			DefKind::TypeAlias(_) => "type alias",
		}
	}

	/// Where the declaration's name is written, for diagnostics. A package,
	/// module or import block has no declaration of its own to point at.
	pub(super) fn declared_at(
		self,
		defs: &DefinitionRegistry,
	) -> Option<SourceSpan> {
		let (file_id, name) = match self {
			DefKind::Module(_) | DefKind::Import(_) | DefKind::Package(_) => {
				return None;
			}
			DefKind::Crate(index) => {
				let def = &defs.namespaces.crate_items()[usize::from(index)];
				(def.file_id, def.alias)
			}
			DefKind::Enum(index) => {
				let def = &defs.enums[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::EnumVariant(index) | DefKind::Const(index) => {
				let def = &defs.constants[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::Struct(index) => {
				let def = &defs.structs[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::Memory(index) => {
				let def = &defs.memories[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::Trait(index) => {
				let def = &defs.traits[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::TypeSet(index) => {
				let def = &defs.typesets[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::Global(index) => {
				let def = &defs.globals[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::Function(index) => {
				let def = &defs.functions[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::TraitAssocType(index) => {
				let def = &defs.assoc_types[usize::from(index)];
				(def.file_id, def.name)
			}
			DefKind::TypeAlias(index) => {
				let def = &defs.type_aliases[usize::from(index)];
				(def.file_id, def.name)
			}
		};
		Some(SourceSpan::new(file_id, name.span))
	}
}

/// Something a path can continue into: what `a::` names when `a` is a
/// package, a module, an enum or an import block. Each is addressed by its
/// owner's own index, so the handle and the owner are one thing.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum Namespace {
	Package(PackageId),
	Module(ModuleIdx),
	Enum(EnumIdx),
	Import(ImportIdx),
}

/// A namespace code is written in: where an unqualified lookup starts, and
/// the accessor of every privacy check. Only packages and modules are
/// scopes; an enum's variants and an import block's declarations are only
/// ever reached through a path.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum Scope {
	Package(PackageId),
	Module(ModuleIdx),
}

impl From<Scope> for Namespace {
	#[inline]
	fn from(scope: Scope) -> Self {
		match scope {
			Scope::Package(package) => Self::Package(package),
			Scope::Module(module) => Self::Module(module),
		}
	}
}

impl Namespace {
	pub(super) fn as_scope(self) -> Option<Scope> {
		match self {
			Self::Package(package) => Some(Scope::Package(package)),
			Self::Module(module) => Some(Scope::Module(module)),
			Self::Enum(_) | Self::Import(_) => None,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct ItemDef {
	pub(super) kind: DefKind,
	pub(super) span: TextSpan,
}

impl ItemDef {
	fn new(kind: DefKind, span: TextSpan) -> Self {
		Self { kind, span }
	}
}

/// What one namespace holds: the definitions declared in it (`items`, which
/// a `DefKey` addresses) and the names it binds. Every namespace is written in
/// one file.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct SymbolTable {
	pub file_id: FileId,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, Binding>,
	pub items: Vec<ItemDef>,
}

impl SymbolTable {
	fn new(file_id: FileId) -> Self {
		Self {
			file_id,
			bindings: HashMap::new(),
			items: Vec::new(),
		}
	}
}

/// A scope's symbols, plus what only a scope has: a place in the module tree
/// and the globs its `use path::*;` items brought in.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct ScopeTable {
	pub symbols: SymbolTable,
	pub parent: Option<Scope>,
	/// The package this scope belongs to — every scope is inside exactly
	/// one, so it's stored rather than recovered by walking parents.
	pub package_id: PackageId,
	/// Namespaces brought into scope via `use path::*;`. Checked during
	/// lookup after direct bindings.
	pub glob_imports: Vec<GlobImport>,
}

/// Every namespace's table, each list indexed by its owner's own index:
/// `packages` by `PackageId`, `modules` by `ModuleIdx`, `enums` by `EnumIdx`
/// and `imports` by `ImportIdx`. An owner and its table are pushed together,
/// which is what keeps the two aligned.
#[derive(Default)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Namespaces {
	packages: Vec<ScopeTable>,
	modules: Vec<ScopeTable>,
	enums: Vec<SymbolTable>,
	imports: Vec<SymbolTable>,
	/// Every `crate` item, indexed by `CrateItemIdx`. Held here because what
	/// a crate item's alias leads into is part of how a path walks, and the
	/// item says which package that is.
	crate_items: Vec<CrateItemDef>,
}

/// The result of [`Namespaces::lookup`]/[`Namespaces::indirect_lookup`].
/// `Found` pairs a target with its visibility — an accessibility check and
/// re-export capping both need both at once, and this holds regardless of
/// whether `accessor` can actually see it; that's left for the caller to
/// decide, same as a direct (non-glob) hit always has been.
///
/// `Ambiguous` carries every surviving candidate paired with the `pub use`
/// edge responsible for it — the diagnostic needs to name each one, same as
/// two colliding ordinary globs already do. The same `DefKey` reached through
/// two different edges is merged into one candidate before it ever becomes
/// an entry here, not after — see `indirect_lookup`. No visibility here: by
/// construction, every entry that survives into this variant was already
/// confirmed accessible to whichever `accessor` `indirect_lookup` was asked
/// on behalf of, so there's nothing left for it to say.
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum BindingLookup {
	NotFound,
	Found {
		target: BindingTarget,
		visibility: Visibility,
		/// The `use` item in the looked-up namespace that made the binding
		/// visible there, a named import or a glob; `None` for a declaration
		/// in that namespace.
		import: Option<UseItemIndex>,
	},
	Ambiguous(Box<[(BindingTarget, SourceSpan)]>),
}

/// `indirect_lookup`'s in-progress merge of the glob candidates it's walked
/// so far, for one `accessor`. Owns the whole merge policy so the walk
/// itself just has to `push` and, at the end, `finish`.
///
/// Two different kinds of "accessible" are in play here, at two different
/// times. `BindingTarget::Accessible`/`Inaccessible` records whether *the
/// edge that installed a binding* could see its def — baked in once. The
/// same `DefKey` reached through two `pub` edges (e.g. a diamond re-export)
/// isn't a conflict, and when the two edges disagree, `Accessible` wins
/// silently, same as `try_insert_binding` resolves the same disagreement
/// for a direct same-namespace collision.
///
/// Separately, `is_accessible_from(accessor, ..)` asks whether *this
/// query's* accessor can see a given def at all, checked fresh. A lone real
/// candidate is always kept as `One`, visibility included, regardless of
/// that check — deferred to the caller, same as a direct hit. It's only
/// consulted the moment a second, distinct `DefKey` would otherwise promote
/// this into a real ambiguity: a candidate `accessor` could never legally
/// choose is excluded right then, rather than surviving into a misleading
/// `Ambiguous`.
struct CandidateMerge<'a> {
	namespaces: &'a Namespaces,
	accessor: Scope,
	candidates: Candidates,
}

/// A binding a glob leads to, and the glob that leads there.
#[derive(Clone, Copy)]
struct GlobCandidate {
	target: BindingTarget,
	visibility: Visibility,
	/// The glob's span: what an ambiguity between candidates names.
	span: SourceSpan,
	/// The glob's `use` item.
	glob: UseItemIndex,
}

enum Candidates {
	Empty,
	// An already-diagnosed broken edge (its target is `Error`). Never
	// competes with a real candidate for ambiguity — kept only as a
	// fallback, and only the first one seen, so a later re-export sees
	// `Errored` instead of re-diagnosing `Absent`, mirroring how a broken
	// named `use` installs its own `Error` placeholder. The moment a real
	// candidate arrives, this becomes moot for good: `finish` never looks
	// at it again once `One`/`Many` is reached, so there's nothing to keep
	// it for.
	Error(GlobCandidate),
	// `finish` never reads the span — `Found` doesn't carry one. It's kept
	// for `push`: if a second, distinct `DefKey` arrives later and this
	// candidate turns out to still be a real competitor, its span is what
	// seeds the new `Many` entry.
	One(GlobCandidate),
	Many(Vec<(BindingTarget, SourceSpan)>),
}

impl<'a> CandidateMerge<'a> {
	fn new(namespaces: &'a Namespaces, accessor: Scope) -> Self {
		Self {
			namespaces,
			accessor,
			candidates: Candidates::Empty,
		}
	}

	fn push(&mut self, candidate: GlobCandidate) {
		let Some(def_key) = candidate.target.def_key() else {
			if matches!(self.candidates, Candidates::Empty) {
				self.candidates = Candidates::Error(candidate);
			}
			return;
		};

		match &mut self.candidates {
			Candidates::Empty | Candidates::Error(_) => {
				self.candidates = Candidates::One(candidate);
			}
			Candidates::One(first) => {
				let first_key = first
					.target
					.def_key()
					.expect("a real candidate always carries a DefKey");

				if first_key == def_key {
					if matches!(candidate.target, BindingTarget::Accessible(_))
						&& matches!(
							first.target,
							BindingTarget::Inaccessible(_)
						) {
						*first = candidate;
					}
					return;
				}

				let first_reachable = self.namespaces.is_accessible_from(
					self.accessor,
					first_key.namespace,
					first.visibility,
				);
				let this_reachable = self.namespaces.is_accessible_from(
					self.accessor,
					def_key.namespace,
					candidate.visibility,
				);

				match (first_reachable, this_reachable) {
					(true, true) => {
						self.candidates = Candidates::Many(vec![
							(first.target, first.span),
							(candidate.target, candidate.span),
						]);
					}
					// Only one side is a real option for `accessor` — that
					// one just replaces `first` outright (or stays, if it
					// already was `first`); neither case is an ambiguity.
					(true, false) => {}
					(false, true) => {
						self.candidates = Candidates::One(candidate);
					}
					(false, false) => {}
				}
			}
			Candidates::Many(items) => {
				if !self.namespaces.is_accessible_from(
					self.accessor,
					def_key.namespace,
					candidate.visibility,
				) {
					return;
				}
				let slot = items
					.iter_mut()
					.find(|(target, _)| target.def_key() == Some(def_key));
				match slot {
					Some(slot)
						if matches!(
							candidate.target,
							BindingTarget::Accessible(_)
						) && matches!(
							slot.0,
							BindingTarget::Inaccessible(_)
						) =>
					{
						*slot = (candidate.target, candidate.span);
					}
					Some(_) => {}
					None => items.push((candidate.target, candidate.span)),
				}
			}
		}
	}

	fn finish(self) -> BindingLookup {
		match self.candidates {
			Candidates::Empty => BindingLookup::NotFound,
			Candidates::Error(found) | Candidates::One(found) => {
				BindingLookup::Found {
					target: found.target,
					visibility: found.visibility,
					import: Some(found.glob),
				}
			}
			Candidates::Many(items) => {
				BindingLookup::Ambiguous(items.into_boxed_slice())
			}
		}
	}
}

impl Namespaces {
	pub(super) fn symbols(&self, namespace: Namespace) -> &SymbolTable {
		match namespace {
			Namespace::Package(package) => {
				&self.packages[package.as_usize()].symbols
			}
			Namespace::Module(module) => {
				&self.modules[usize::from(module)].symbols
			}
			Namespace::Enum(enum_index) => &self.enums[usize::from(enum_index)],
			Namespace::Import(import) => &self.imports[usize::from(import)],
		}
	}

	fn symbols_mut(&mut self, namespace: Namespace) -> &mut SymbolTable {
		match namespace {
			Namespace::Package(package) => {
				&mut self.packages[package.as_usize()].symbols
			}
			Namespace::Module(module) => {
				&mut self.modules[usize::from(module)].symbols
			}
			Namespace::Enum(enum_index) => {
				&mut self.enums[usize::from(enum_index)]
			}
			Namespace::Import(import) => &mut self.imports[usize::from(import)],
		}
	}

	pub(super) fn scope(&self, scope: Scope) -> &ScopeTable {
		match scope {
			Scope::Package(package) => &self.packages[package.as_usize()],
			Scope::Module(module) => &self.modules[usize::from(module)],
		}
	}

	pub(super) fn scope_mut(&mut self, scope: Scope) -> &mut ScopeTable {
		match scope {
			Scope::Package(package) => &mut self.packages[package.as_usize()],
			Scope::Module(module) => &mut self.modules[usize::from(module)],
		}
	}

	pub(super) fn file_id(&self, namespace: Namespace) -> FileId {
		self.symbols(namespace).file_id
	}

	/// What `def_key` names.
	pub(super) fn kind(&self, def_key: DefKey) -> DefKind {
		self.symbols(def_key.namespace).items[usize::from(def_key.def_idx)].kind
	}

	pub fn crate_items(&self) -> &[CrateItemDef] {
		&self.crate_items
	}

	/// The namespace a path continues into after `def_key`: what `a::` names
	/// when `a` is a package, a module, an enum, an import block or a crate
	/// item. `None` for anything a path cannot continue through.
	pub(super) fn entered_by(&self, def_key: DefKey) -> Option<Namespace> {
		Some(match self.kind(def_key) {
			DefKind::Package(package) => Namespace::Package(package),
			DefKind::Module(module) => Namespace::Module(module),
			DefKind::Enum(enum_index) => Namespace::Enum(enum_index),
			DefKind::Import(import) => Namespace::Import(import),
			// Until instances are told apart, a crate item leads into its
			// package's own namespace.
			DefKind::Crate(index) => Namespace::Package(
				self.crate_items[usize::from(index)].package?,
			),
			_ => return None,
		})
	}

	/// Whether `scope` is `ancestor` itself, or nested inside it.
	pub(super) fn contains(&self, ancestor: Scope, scope: Scope) -> bool {
		let mut current = Some(scope);
		while let Some(scope) = current {
			if scope == ancestor {
				return true;
			}
			current = self.scope(scope).parent;
		}
		false
	}

	/// An item declared `visibility` in `target` is reachable from
	/// `accessor` if it's `Public`, or if `target` is a scope that contains
	/// `accessor`.
	pub(super) fn is_accessible_from(
		&self,
		accessor: Scope,
		target: Namespace,
		visibility: Visibility,
	) -> bool {
		match visibility {
			Visibility::Public => true,
			// No code is written inside an enum or an import block, so no
			// accessor is ever inside one.
			Visibility::Private => target
				.as_scope()
				.is_some_and(|target| self.contains(target, accessor)),
		}
	}

	/// Inserts `binding` under `key` in `namespace`. `Err` carries the
	/// colliding `DefKey` when one was already there and both count as
	/// real occupants of the name — this is an error state, not merely an
	/// optional value, hence `Result` over `Option`. No diagnostics here —
	/// this only touches the namespace graph; a caller with
	/// `diagnostics`/`strings` on hand (see
	/// `DefinitionRegistryBuilder`/`ImportResolver`'s own `insert_binding`)
	/// is what turns a collision into a reported error.
	pub(super) fn try_insert_binding(
		&mut self,
		namespace: Namespace,
		key: BindingKey,
		binding: Binding,
	) -> Result<(), DefKey> {
		use std::collections::hash_map::Entry;

		match self.symbols_mut(namespace).bindings.entry(key) {
			Entry::Vacant(entry) => {
				entry.insert(binding);
				Ok(())
			}
			Entry::Occupied(mut entry) => {
				match (entry.get().target, binding.target) {
					// Two equally-legitimate bindings compete for the same
					// name.
					(
						BindingTarget::Accessible(collision),
						BindingTarget::Accessible(_),
					)
					| (
						BindingTarget::Inaccessible(collision),
						BindingTarget::Inaccessible(_),
					) => Err(collision),
					// An accessible binding always wins over an
					// inaccessible one, silently — an inaccessible claim
					// isn't a real competing declaration, so this isn't a
					// collision to report either way.
					(
						BindingTarget::Inaccessible(_),
						BindingTarget::Accessible(_),
					) => {
						entry.insert(binding);
						Ok(())
					}
					(
						BindingTarget::Accessible(_),
						BindingTarget::Inaccessible(_),
					) => Ok(()),
					// A real binding replaces previous recovery state.
					(
						BindingTarget::Error,
						BindingTarget::Accessible(_)
						| BindingTarget::Inaccessible(_),
					) => {
						entry.insert(binding);
						Ok(())
					}
					// Recovery state must never hide a real binding.
					(
						BindingTarget::Accessible(_)
						| BindingTarget::Inaccessible(_),
						BindingTarget::Error,
					) => Ok(()),
					// Nothing useful to diagnose here.
					(BindingTarget::Error, BindingTarget::Error) => Ok(()),
				}
			}
		}
	}

	/// `namespace`'s own binding for `key` — a direct declaration or a
	/// resolved named `use`. No glob involved, so no ambiguity is
	/// possible: a `HashMap` has at most one entry per key. Accessor-blind
	/// by design — filtering happens one level up, once multiple
	/// candidates are actually competing.
	pub(super) fn direct_lookup(
		&self,
		namespace: Namespace,
		key: BindingKey,
	) -> Option<&Binding> {
		self.symbols(namespace).bindings.get(&key)
	}

	/// What `target` exposes through its `use path::*;` edges, filtered to
	/// the ones `accessor` may actually see — a glob is just another
	/// binding with a visibility, so a `pub` one is visible to anyone and a
	/// private one only to `target` itself and its descendants, the same
	/// rule `is_accessible_from` applies everywhere else. Recurses via
	/// `lookup` at each hop, not into itself, so a re-export chain composes
	/// through direct declarations and further re-exports alike. Terminates
	/// because `compute_glob_item` already rejects a cycle in this exact
	/// edge set before it can be walked. Only a scope has globs.
	///
	/// `accessor` also matters once two *distinct* candidates compete: a
	/// candidate `accessor` could never legally choose is excluded right
	/// then, rather than surviving into a misleading `Ambiguous`. A lone
	/// candidate is always returned `Found`, visibility included,
	/// regardless of whether `accessor` can see *that candidate* — deferred
	/// to the caller, same as a direct (non-glob) hit already is.
	pub(super) fn indirect_lookup(
		&self,
		use_items: &[UseItemDef],
		accessor: Scope,
		target: Namespace,
		key: BindingKey,
	) -> BindingLookup {
		let Some(target) = target.as_scope() else {
			return BindingLookup::NotFound;
		};
		let mut candidates = CandidateMerge::new(self, accessor);

		for glob in self.scope(target).glob_imports.iter().copied() {
			let item = &use_items[usize::from(glob.use_item)];
			let glob_visibility = Visibility::from(item.pub_span);
			if !self.is_accessible_from(
				accessor,
				target.into(),
				glob_visibility,
			) {
				continue;
			}
			let UseItemKind::Glob { span, .. } = item.kind else {
				unreachable!("a glob edge is always produced by a glob item")
			};
			let edge_span =
				SourceSpan::new(self.scope(target).symbols.file_id, span);

			match self.lookup(use_items, accessor, glob.namespace, key) {
				BindingLookup::NotFound => {}
				BindingLookup::Found {
					target, visibility, ..
				} => {
					candidates.push(GlobCandidate {
						target,
						visibility,
						span: edge_span,
						glob: glob.use_item,
					});
				}
				BindingLookup::Ambiguous(nested) => {
					// Every nested entry was already confirmed accessible
					// to this same `accessor` one recursion level down
					// (that's what let it survive into `Ambiguous` at
					// all) — `Public` is just a stand-in that reproduces
					// that same "yes" when re-checked just below, not a
					// claim about its real declared visibility.
					for (target, span) in nested.iter().copied() {
						candidates.push(GlobCandidate {
							target,
							visibility: Visibility::Public,
							span,
							glob: glob.use_item,
						});
					}
				}
			}
		}

		candidates.finish()
	}

	/// What `target` exposes to `accessor` — `direct_lookup`, falling back
	/// to `indirect_lookup`. What a named `use a::b;` and a glob `use a::*;`
	/// should both find when asking `a` for the same name, whether
	/// `accessor` is `a` itself (or a descendant, consulting `a`'s own
	/// private globs) or is reaching in from elsewhere.
	pub(super) fn lookup(
		&self,
		use_items: &[UseItemDef],
		accessor: Scope,
		target: Namespace,
		key: BindingKey,
	) -> BindingLookup {
		match self.direct_lookup(target, key) {
			Some(binding) => BindingLookup::Found {
				target: binding.target,
				visibility: binding.visibility,
				import: match binding.source {
					BindingSource::Definition => None,
					BindingSource::Import(import) => Some(import),
				},
			},
			None => self.indirect_lookup(use_items, accessor, target, key),
		}
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum BindingTarget {
	Accessible(DefKey),
	/// Resolved to a real def, but the source wasn't visible from the
	/// writing namespace when a `use` resolved it. Not poisoned like
	/// `Error` — whatever already enforces privacy at reference sites for
	/// direct qualified paths should apply the same check here, reporting
	/// (or not) each time this binding is actually used, not just once.
	Inaccessible(DefKey),
	Error,
}

impl BindingTarget {
	/// The underlying definition this target names, if it names one at all
	/// — `Error` doesn't, since it's recovery state for an already-diagnosed
	/// failure rather than a reference to anything real.
	pub(super) fn def_key(self) -> Option<DefKey> {
		match self {
			Self::Accessible(key) | Self::Inaccessible(key) => Some(key),
			Self::Error => None,
		}
	}
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
enum BindingSource {
	Definition,
	Import(UseItemIndex),
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct Binding {
	pub(super) target: BindingTarget,
	pub(super) visibility: Visibility,
	source: BindingSource,
}

impl Binding {
	fn definition(key: DefKey, visibility: Visibility) -> Self {
		Self {
			target: BindingTarget::Accessible(key),
			visibility,
			source: BindingSource::Definition,
		}
	}

	/// A name declared by a definition that could not be resolved, such as
	/// a `crate` item whose key the manifest does not declare. It carries
	/// no `DefKey`, so a path through it ends silently on top of the error
	/// already reported at the declaration, instead of adding "undeclared"
	/// errors at every use.
	fn poisoned(visibility: Visibility) -> Self {
		Self {
			target: BindingTarget::Error,
			visibility,
			source: BindingSource::Definition,
		}
	}

	pub(super) fn import(
		target: BindingTarget,
		visibility: Visibility,
		index: UseItemIndex,
	) -> Self {
		Self {
			target,
			visibility,
			source: BindingSource::Import(index),
		}
	}

	/// Where this binding itself was declared. For an import this is the local
	/// name at the `use` site, not the definition its target eventually names.
	pub(super) fn declaration_span(
		&self,
		namespaces: &Namespaces,
		use_items: &[UseItemDef],
	) -> SourceSpan {
		match self.source {
			BindingSource::Definition => {
				let def_key = match self.target {
					BindingTarget::Accessible(key)
					| BindingTarget::Inaccessible(key) => key,
					// Only a binding that rejected an insertion is asked
					// for its declaration, and an `Error` one never does.
					BindingTarget::Error => {
						unreachable!(
							"a poisoned binding never collides, so nothing \
							 asks where it was declared"
						)
					}
				};
				def_key.source_span(namespaces)
			}

			BindingSource::Import(index) => {
				let item = &use_items[usize::from(index)];
				let span = match item.kind {
					UseItemKind::Name { name, alias, .. } => {
						alias.unwrap_or(name).span
					}
					UseItemKind::Glob { span, .. } => span,
				};
				SourceSpan::new(namespaces.file_id(item.namespace.into()), span)
			}
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct ModuleDef {
	/// The scope `mod foo;` was written in — where the name `foo` itself
	/// gets bound. The "outside" of the module.
	pub parent_namespace: Scope,
	/// The file containing the `mod foo;` (or `mod foo { .. }`) text
	/// itself — not necessarily where `foo`'s own items live.
	///
	/// For inline `mod foo { .. }`, the module's content lives in this
	/// same file, so `declaration_file == own_file`. For file-backed
	/// `mod foo;`, the declaration is one line in this file but `foo`'s
	/// actual content lives in `foo.wx`, so `own_file` points there
	/// instead and the two differ.
	pub declaration_file: FileId,
	/// The file that IS `foo`'s content: `foo.wx` for `mod foo;`, or the
	/// same file as `declaration_file` for inline `mod foo { .. }`.
	pub own_file: FileId,
	pub name: ast::Spanned<SymbolU32>,
	pub pub_span: Option<TextSpan>,
}

/// One `use path::*;` edge — the namespace it resolved to, plus which item
/// produced it.
///
/// `use_item` is a back-reference, not a copy: `pub_span`, the declaring
/// namespace, and (via `UseItemKind::Glob`) the `x::*` span all already live
/// on the `UseItemDef` — duplicating them here would just be two copies of
/// the same fact able to drift, the same reason `Binding::source` points at
/// a `UseItemIndex` instead of cloning what it needs out of it. `namespace`
/// is the one genuinely new fact this pass computes: the item only ever
/// stores its *unresolved* `path`, and resolving it to a namespace is this
/// whole pass's job.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct GlobImport {
	pub use_item: UseItemIndex,
	pub namespace: Namespace,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct ImportDef {
	pub parent_namespace: Scope,
	pub external_name: ast::Spanned<SymbolU32>,
	pub internal_name: ast::Spanned<SymbolU32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum MemberKind {
	Function(FunctionIdx),
	Method(FunctionIdx),
	Constant(ConstIdx),
	AssociatedType(AssocTypeIdx),
}

impl MemberKind {
	pub(super) fn def_id(self) -> DefId {
		match self {
			Self::Function(index) | Self::Method(index) => {
				DefId::Function(index)
			}
			Self::Constant(index) => DefId::Const(index),
			Self::AssociatedType(index) => DefId::AssocType(index),
		}
	}

	pub fn tier(self) -> Tier {
		match self {
			Self::AssociatedType(_) => Tier::Type,
			Self::Function(_) | Self::Method(_) | Self::Constant(_) => {
				Tier::Value
			}
		}
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct DefKey {
	pub(super) namespace: Namespace,
	pub(super) def_idx: LocalDefIdx,
}

impl DefKey {
	#[inline]
	pub fn new(namespace: Namespace, def_idx: LocalDefIdx) -> Self {
		Self { namespace, def_idx }
	}

	#[inline]
	pub fn source_span(self, namespaces: &Namespaces) -> SourceSpan {
		let symbols = namespaces.symbols(self.namespace);
		SourceSpan::new(
			symbols.file_id,
			symbols.items[usize::from(self.def_idx)].span,
		)
	}

	#[inline]
	pub fn symbol_kind(self, defs: &DefinitionRegistry) -> DefKind {
		defs.namespaces.kind(self)
	}
}

pub(super) struct DuplicateDefinitionDiagnostic<'strings> {
	pub(super) strings: &'strings ast::StringInterner,
	pub(super) key: BindingKey,
	pub(super) definitions: (SourceSpan, SourceSpan),
}

impl DuplicateDefinitionDiagnostic<'_> {
	pub(super) fn report(self) -> Diagnostic<FileId> {
		let name = self.strings.resolve(self.key.symbol).unwrap();

		let (a, b) = self.definitions;
		// Most declarations in one namespace share a file, but file modules and
		// imported bindings can make a collision span files. Preserve insertion
		// order across files; within one file, keep diagnostics source-ordered.
		let (first, second) =
			if a.file_id == b.file_id && a.span.start > b.span.start {
				(b, a)
			} else {
				(a, b)
			};

		Diagnostic::error()
			.with_code(DiagnosticCode::DuplicateDefinition.code())
			.with_message(format!(
				"the name `{name}` is defined multiple times"
			))
			.with_label(
				second
					.primary_label()
					.with_message(format!("`{name}` redefined here")),
			)
			.with_label(first.secondary_label().with_message(format!(
				"previous definition of the {} `{name}` here",
				self.key.tier.noun(),
			)))
	}
}

impl DefinitionRegistry {
	/// The written name of `def_id`'s declaration. A generated trait has its
	/// typeset's name.
	pub(super) fn name(&self, def_id: DefId) -> Spanned<SymbolU32> {
		match def_id {
			DefId::Struct(index) => self.structs[usize::from(index)].name,
			DefId::Enum(index) => self.enums[usize::from(index)].name,
			DefId::Trait(index) => self.traits[usize::from(index)].name,
			DefId::Typeset(index) => self.typesets[usize::from(index)].name,
			DefId::TypeAlias(index) => {
				self.type_aliases[usize::from(index)].name
			}
			DefId::Function(index) => self.functions[usize::from(index)].name,
			DefId::Const(index) => self.constants[usize::from(index)].name,
			DefId::Memory(index) => self.memories[usize::from(index)].name,
			DefId::Global(index) => self.globals[usize::from(index)].name,
			DefId::AssocType(index) => {
				self.assoc_types[usize::from(index)].name
			}
			DefId::TraitImpl(_) | DefId::InherentImpl(_) => {
				todo!(
					"an impl has no name; describing one isn't implemented yet"
				)
			}
		}
	}

	/// Returns the registry alongside `ast_nodes` — every top-level item in
	/// parse order, for Phase 2's demand-driven `ensure_signature` to walk.
	/// Kept separate rather than a field: the registry itself needs no
	/// lifetime, since nothing else in it borrows the AST, and callers who
	/// only need the registry (like tests exercising this phase alone) can
	/// drop `ast_nodes` immediately instead of carrying an AST borrow
	/// alongside it.
	pub(super) fn build<'ast>(
		packages: &'ast [Package],
		files: &Files,
		strings: &mut ast::StringInterner,
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		resolutions: &mut NameResolutions,
		stdlib_package: PackageId,
		root_package: PackageId,
	) -> (Self, Vec<AstEntry<'ast>>) {
		DefinitionRegistryBuilder::build(
			packages,
			files,
			strings,
			diagnostics,
			resolutions,
			stdlib_package,
			root_package,
		)
	}
}

impl<'ast, 'ctx> DefinitionRegistryBuilder<'ast, 'ctx> {
	fn build(
		packages: &'ast [Package],
		files: &'ctx Files,
		strings: &'ctx mut ast::StringInterner,
		diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
		resolutions: &mut NameResolutions,
		stdlib_package: PackageId,
		root_package: PackageId,
	) -> (DefinitionRegistry, Vec<AstEntry<'ast>>) {
		let mut namespaces = Namespaces::default();
		for package in packages {
			debug_assert_eq!(
				namespaces.packages.len(),
				package.id.as_usize(),
				"packages are listed in `PackageId` order"
			);
			let root =
				DefKey::new(Namespace::Package(package.id), LocalDefIdx::SELF);
			let mut symbols = SymbolTable::new(
				package.modules[package.root.as_usize()].file_id,
			);
			symbols.items.push(ItemDef::new(
				DefKind::Package(package.id),
				TextSpan::new(0, 0),
			));
			for symbol in [
				ast::Keyword::SelfLower.symbol(),
				ast::Keyword::Crate.symbol(),
			] {
				symbols.bindings.insert(
					BindingKey::ty(symbol),
					Binding::definition(root, Visibility::Public),
				);
			}

			// The stdlib is implicit in every package but its own provider.
			// Every other dependency is named by a `crate` item, bound when
			// that item is scanned.
			if package.id != stdlib_package {
				let std = strings.get_or_intern("std");
				symbols.bindings.insert(
					BindingKey::ty(std),
					Binding::definition(
						DefKey::new(
							Namespace::Package(stdlib_package),
							LocalDefIdx::SELF,
						),
						Visibility::Public,
					),
				);
			}

			namespaces.packages.push(ScopeTable {
				symbols,
				parent: None,
				package_id: package.id,
				glob_imports: Vec::new(),
			});
		}

		let mut builder = Self {
			diagnostics,
			namespaces,
			strings,
			files,
			stdlib_package,
			root_package,
			packages,
			imports: Vec::new(),
			modules: Vec::new(),
			traits: Vec::new(),
			trait_impls: Vec::new(),
			inherent_impls: Vec::new(),
			type_aliases: Vec::new(),
			structs: Vec::new(),
			enums: Vec::new(),
			typesets: Vec::new(),
			functions: Vec::new(),
			memories: Vec::new(),
			globals: Vec::new(),
			constants: Vec::new(),
			assoc_types: Vec::new(),
			use_items: Vec::new(),
			use_paths: Vec::new(),
			ast_nodes: Vec::new(),
			exports: HashMap::new(),
			intrinsics: IntrinsicDefs::default(),
			pending_named_imports: HashMap::new(),
			pending_glob_targets: HashMap::new(),
		};

		let file_namespaces = builder.compute_file_namespaces(packages);
		for source_module in packages
			.iter()
			.flat_map(|package_graph| package_graph.modules.iter())
		{
			let scope = file_namespaces[source_module.file_id.as_usize()];
			for item in source_module.ast.items.iter() {
				builder.scan_item(
					source_module.file_id,
					scope,
					&item.inner.inner,
				);
			}
		}

		ImportResolver::resolve_imports(
			builder.diagnostics,
			resolutions,
			builder.strings,
			&mut builder.namespaces,
			&builder.use_items,
			&builder.use_paths,
			&builder.pending_named_imports,
			&builder.pending_glob_targets,
		);

		let defs = DefinitionRegistry {
			stdlib_package,
			root_package,
			namespaces: builder.namespaces,
			file_namespaces,
			modules: builder.modules,
			imports: builder.imports,
			exports: builder.exports,
			traits: builder.traits,
			trait_impls: builder.trait_impls,
			inherent_impls: builder.inherent_impls,
			structs: builder.structs,
			enums: builder.enums,
			typesets: builder.typesets,
			functions: builder.functions,
			memories: builder.memories,
			globals: builder.globals,
			constants: builder.constants,
			assoc_types: builder.assoc_types,
			use_items: builder.use_items,
			use_paths: builder.use_paths,
			intrinsics: builder.intrinsics,
			type_aliases: builder.type_aliases,
		};

		(defs, builder.ast_nodes)
	}

	fn intern_string(
		&mut self,
		file_id: FileId,
		span: TextSpan,
	) -> Result<SymbolU32, ()> {
		let source = &self.files.get(file_id).unwrap().source;
		let decoded = unescape_string_literal(span.extract_str(source))
			.map_err(|error| {
				self.diagnostics
					.push(error.diagnostic(SourceSpan::new(file_id, span)))
			})?;
		Ok(self.strings.get_or_intern(decoded))
	}

	/// Phase 1a — one namespace per file. Runs before any item is scanned,
	/// so a `mod foo;` declaration (Phase 1b) always finds its content
	/// file's namespace already in place. Pushed in the same order vfs
	/// assigned `FileId`s (each package's whole module tree is loaded, in
	/// module-push order, before the next package starts — see
	/// `Loader::load_module` in `vfs/mod.rs`), so this traversal always has
	/// a parent's namespace ready before any of its children need it, and
	/// `push` alone keeps every entry aligned to its `FileId` without
	/// needing to index ahead of the vec's current length.
	fn compute_file_namespaces(&mut self, packages: &[Package]) -> Vec<Scope> {
		let mut file_namespaces = Vec::with_capacity(self.files.len());
		for source_module in packages
			.iter()
			.flat_map(|package_graph| package_graph.modules.iter())
		{
			debug_assert_eq!(
				file_namespaces.len(),
				source_module.file_id.as_usize(),
				"vfs must assign FileIds in package/module push order",
			);
			let package = &packages[source_module.package_id.as_usize()];
			let scope = match &source_module.declaration {
				None => Scope::Package(package.id),
				Some(declaration) => {
					let parent_module =
						&package.modules[declaration.parent.as_usize()];
					let parent_namespace =
						file_namespaces[parent_module.file_id.as_usize()];
					let module = self.push_module(
						ModuleDef {
							declaration_file: parent_module.file_id,
							own_file: source_module.file_id,
							parent_namespace,
							name: declaration.name,
							pub_span: declaration.pub_span,
						},
						TextSpan::new(0, u32::MAX),
					);
					if let Err(collision) = self.bind_child(
						parent_namespace,
						declaration.name.inner,
						Namespace::Module(module),
						Visibility::from(declaration.pub_span),
					) {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key: BindingKey::ty(declaration.name.inner),
								definitions: (
									self.definition_span(collision),
									SourceSpan::new(
										parent_module.file_id,
										declaration.name.span,
									),
								),
							}
							.report(),
						);
					}
					Scope::Module(module)
				}
			};
			file_namespaces.push(scope);
		}

		file_namespaces
	}

	#[inline]
	fn push_trait(&mut self, item: TraitDef) -> TraitIdx {
		let index = TraitIdx::new(u32::try_from(self.traits.len()).unwrap());
		self.traits.push(item);
		index
	}

	#[inline]
	fn push_trait_impl(&mut self, item: TraitImplDef) -> TraitImplIdx {
		let index =
			TraitImplIdx::new(u32::try_from(self.trait_impls.len()).unwrap());
		self.trait_impls.push(item);
		index
	}

	/// Pre-allocates a memory declaration's synthetic `impl Memory for
	/// <memory>` — see `MemoryDef`'s own doc comment for why this never
	/// needs `IntrinsicDefs::memory` to already be resolved.
	fn synthesize_memory_impl(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		name_span: TextSpan,
	) -> (TraitImplIdx, AssocTypeIdx) {
		let size_symbol = self.strings.get_or_intern("Size");
		let size_assoc_type_index =
			AssocTypeIdx::new(u32::try_from(self.assoc_types.len()).unwrap());
		self.assoc_types.push(AssocTypeDef {
			file_id,
			namespace,
			name: Spanned {
				inner: size_symbol,
				span: name_span,
			},
		});
		let trait_impl_index = self.push_trait_impl(TraitImplDef {
			file_id,
			namespace,
			members: vec![TraitMemberDef {
				kind: MemberKind::AssociatedType(size_assoc_type_index),
				span: name_span,
			}],
			bindings: HashMap::from([(
				BindingKey::ty(size_symbol),
				MemberIdx::new(0),
			)]),
		});
		(trait_impl_index, size_assoc_type_index)
	}

	/// Pre-allocates a global declaration's synthetic `impl Global for
	/// <global>` and, if `mutable`, the additional `impl GlobalMut for
	/// <global>` — see `GlobalDef`'s own doc comment.
	fn synthesize_global_impl(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		name_span: TextSpan,
		mutable: bool,
	) -> (TraitImplIdx, AssocTypeIdx, Option<TraitImplIdx>) {
		let value_symbol = self.strings.get_or_intern("Value");
		let value_assoc_type_index =
			AssocTypeIdx::new(u32::try_from(self.assoc_types.len()).unwrap());
		self.assoc_types.push(AssocTypeDef {
			file_id,
			namespace,
			name: Spanned {
				inner: value_symbol,
				span: name_span,
			},
		});
		let trait_impl_index = self.push_trait_impl(TraitImplDef {
			file_id,
			namespace,
			members: vec![TraitMemberDef {
				kind: MemberKind::AssociatedType(value_assoc_type_index),
				span: name_span,
			}],
			bindings: HashMap::from([(
				BindingKey::ty(value_symbol),
				MemberIdx::new(0),
			)]),
		});
		// `GlobalMut` declares no members of its own (`func set` has a
		// default body reusing `Global::Value`) — an empty impl is enough
		// to make it a dispatch candidate.
		let mut_trait_impl_index = mutable.then(|| {
			self.push_trait_impl(TraitImplDef {
				file_id,
				namespace,
				members: Vec::new(),
				bindings: HashMap::new(),
			})
		});
		(
			trait_impl_index,
			value_assoc_type_index,
			mut_trait_impl_index,
		)
	}

	/// Pre-allocates a function's synthetic `impl Call for <function>` and
	/// `impl Function for <function>` — see `FunctionImpls`.
	fn synthesize_function_impls(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		name_span: TextSpan,
	) -> FunctionImpls {
		let args_symbol = self.strings.get_or_intern("Args");
		let result_symbol = self.strings.get_or_intern("Result");
		let args_assoc_type_index =
			AssocTypeIdx::new(u32::try_from(self.assoc_types.len()).unwrap());
		self.assoc_types.push(AssocTypeDef {
			file_id,
			namespace,
			name: Spanned {
				inner: args_symbol,
				span: name_span,
			},
		});
		let result_assoc_type_index =
			AssocTypeIdx::new(u32::try_from(self.assoc_types.len()).unwrap());
		self.assoc_types.push(AssocTypeDef {
			file_id,
			namespace,
			name: Spanned {
				inner: result_symbol,
				span: name_span,
			},
		});
		let call_impl_index = self.push_trait_impl(TraitImplDef {
			file_id,
			namespace,
			members: vec![
				TraitMemberDef {
					kind: MemberKind::AssociatedType(args_assoc_type_index),
					span: name_span,
				},
				TraitMemberDef {
					kind: MemberKind::AssociatedType(result_assoc_type_index),
					span: name_span,
				},
			],
			bindings: HashMap::from([
				(BindingKey::ty(args_symbol), MemberIdx::new(0)),
				(BindingKey::ty(result_symbol), MemberIdx::new(1)),
			]),
		});
		let function_impl_index = self.push_trait_impl(TraitImplDef {
			file_id,
			namespace,
			members: Vec::new(),
			bindings: HashMap::new(),
		});
		FunctionImpls {
			call_impl_index,
			args_assoc_type_index,
			result_assoc_type_index,
			function_impl_index,
		}
	}

	#[inline]
	fn push_typeset(&mut self, item: TypesetDef) -> TypesetIdx {
		let index =
			TypesetIdx::new(u32::try_from(self.typesets.len()).unwrap());
		self.typesets.push(item);
		index
	}

	#[inline]
	fn push_function(&mut self, item: FunctionDef) -> FunctionIdx {
		let index =
			FunctionIdx::new(u32::try_from(self.functions.len()).unwrap());
		self.functions.push(item);
		index
	}

	#[inline]
	fn push_inherent_impl(&mut self, item: InherentImplDef) -> InherentImplIdx {
		let index = InherentImplIdx::new(
			u32::try_from(self.inherent_impls.len()).unwrap(),
		);
		self.inherent_impls.push(item);
		index
	}

	#[inline]
	fn push_use_path(&mut self, segment: UsePathSegment) -> UsePathIndex {
		let index =
			UsePathIndex::new(u32::try_from(self.use_paths.len()).unwrap());
		self.use_paths.push(segment);
		index
	}

	#[inline]
	fn push_use_item(&mut self, item: UseItemDef) -> UseItemIndex {
		let index =
			UseItemIndex::new(u32::try_from(self.use_items.len()).unwrap());
		self.use_items.push(item);
		index
	}

	fn push_def(
		&mut self,
		namespace: Namespace,
		definition: ItemDef,
	) -> DefKey {
		let items = &mut self.namespaces.symbols_mut(namespace).items;
		let def_idx = LocalDefIdx::new(u32::try_from(items.len()).unwrap());
		items.push(definition);
		DefKey::new(namespace, def_idx)
	}

	/// Namespace self entries describe their contents; collision labels need
	/// the declaration name, which may be written in a different file.
	fn definition_span(&self, key: DefKey) -> SourceSpan {
		match self.namespaces.kind(key) {
			DefKind::Module(index) => {
				let module = &self.modules[usize::from(index)];
				SourceSpan::new(module.declaration_file, module.name.span)
			}
			DefKind::Import(index) => SourceSpan::new(
				self.namespaces.file_id(Namespace::Import(index)),
				self.imports[usize::from(index)].internal_name.span,
			),
			_ => key.source_span(&self.namespaces),
		}
	}

	fn insert_binding(
		&mut self,
		namespace: Namespace,
		key: BindingKey,
		binding: Binding,
		span: TextSpan,
	) {
		if let Err(collision_key) =
			self.namespaces.try_insert_binding(namespace, key, binding)
		{
			self.report_duplicate(namespace, key, collision_key, span);
		}
	}

	/// Binds one declaration under its name in both tiers, as a struct,
	/// function or memory is. It is one definition, so a clash in either
	/// tier is reported once, the value's first.
	fn insert_type_and_value(
		&mut self,
		namespace: Namespace,
		symbol: SymbolU32,
		ty: Binding,
		value: Binding,
		span: TextSpan,
	) {
		let value_key = BindingKey::value(symbol);
		let type_key = BindingKey::ty(symbol);
		let value = self
			.namespaces
			.try_insert_binding(namespace, value_key, value);
		let ty = self.namespaces.try_insert_binding(namespace, type_key, ty);
		match (value, ty) {
			(Err(collision_key), _) => {
				self.report_duplicate(namespace, value_key, collision_key, span)
			}
			(Ok(()), Err(collision_key)) => {
				self.report_duplicate(namespace, type_key, collision_key, span)
			}
			(Ok(()), Ok(())) => {}
		}
	}

	fn report_duplicate(
		&mut self,
		namespace: Namespace,
		key: BindingKey,
		collision_key: DefKey,
		span: TextSpan,
	) {
		self.diagnostics.push(
			DuplicateDefinitionDiagnostic {
				strings: self.strings,
				key,
				definitions: (
					self.definition_span(collision_key),
					SourceSpan::new(self.namespaces.file_id(namespace), span),
				),
			}
			.report(),
		);
	}

	/// Records a `crate "key" as alias;` item and binds `alias` in its scope
	/// to the package the manifest declares under `key`. The binding is as
	/// visible as the item: private to the scope and everything inside it,
	/// or public with `pub`, which lets a downstream package name the
	/// dependency through this one.
	fn scan_crate_item(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		pub_span: Option<TextSpan>,
		package: TextSpan,
		alias: Spanned<SymbolU32>,
	) {
		// A key that cannot be decoded was reported by `intern_string`.
		let Ok(key) = self.intern_string(file_id, package) else {
			return;
		};
		let package_name = Spanned {
			inner: key,
			span: package,
		};
		let owner = self.namespaces.scope(namespace).package_id;
		let package = self.packages[owner.as_usize()]
			.dependencies
			.get(&package_name.inner)
			.copied();
		let index = CrateItemIdx::new(
			u32::try_from(self.namespaces.crate_items.len()).unwrap(),
		);
		self.namespaces.crate_items.push(CrateItemDef {
			file_id,
			namespace,
			pub_span,
			package_name,
			alias,
			package,
		});

		if package.is_none() {
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::UnknownCrate.code())
					.with_message(format!(
						"no dependency named `{}` is declared in `wx.json`",
						self.strings.resolve(package_name.inner).unwrap(),
					))
					.with_label(
						SourceSpan::new(file_id, package_name.span)
							.primary_label()
							.with_message("not a declared dependency"),
					),
			);
		}
		// The alias of a malformed item was already reported by the parser.
		if alias.inner == Keyword::Error.symbol() {
			return;
		}

		let visibility = Visibility::from(pub_span);
		let binding = if package.is_some() {
			let def_key = self.push_def(
				Namespace::from(namespace),
				ItemDef::new(DefKind::Crate(index), alias.span),
			);
			Binding::definition(def_key, visibility)
		} else {
			Binding::poisoned(visibility)
		};
		self.insert_binding(
			Namespace::from(namespace),
			BindingKey::ty(alias.inner),
			binding,
			alias.span,
		);
	}

	/// Pushes a module together with its scope, which binds the module's own
	/// name and `self` to the module, `crate` to its package's root and
	/// `super` to the scope it was declared in.
	fn push_module(
		&mut self,
		module: ModuleDef,
		content_span: TextSpan,
	) -> ModuleIdx {
		let index = ModuleIdx::new(u32::try_from(self.modules.len()).unwrap());
		let parent = module.parent_namespace;
		let package_id = self.namespaces.scope(parent).package_id;
		let this = DefKey::new(Namespace::Module(index), LocalDefIdx::SELF);
		let mut symbols = SymbolTable::new(module.own_file);
		symbols
			.items
			.push(ItemDef::new(DefKind::Module(index), content_span));
		for symbol in [module.name.inner, ast::Keyword::SelfLower.symbol()] {
			symbols.bindings.insert(
				BindingKey::ty(symbol),
				Binding::definition(this, Visibility::Public),
			);
		}
		symbols.bindings.insert(
			BindingKey::ty(ast::Keyword::Crate.symbol()),
			Binding::definition(
				DefKey::new(Namespace::Package(package_id), LocalDefIdx::SELF),
				Visibility::Public,
			),
		);
		symbols.bindings.insert(
			BindingKey::ty(ast::Keyword::Super.symbol()),
			Binding::definition(
				DefKey::new(parent.into(), LocalDefIdx::SELF),
				Visibility::Public,
			),
		);
		self.modules.push(module);
		self.namespaces.modules.push(ScopeTable {
			symbols,
			parent: Some(parent),
			package_id,
			glob_imports: Vec::new(),
		});
		index
	}

	/// Pushes an import block together with its table, which holds only the
	/// block's own declarations: an import block is entered through a path,
	/// never written in, so it binds no `self`, `crate` or `super`.
	fn push_import(
		&mut self,
		import: ImportDef,
		file_id: FileId,
		content_span: TextSpan,
	) -> ImportIdx {
		let index = ImportIdx::new(u32::try_from(self.imports.len()).unwrap());
		let mut symbols = SymbolTable::new(file_id);
		symbols
			.items
			.push(ItemDef::new(DefKind::Import(index), content_span));
		self.imports.push(import);
		self.namespaces.imports.push(symbols);
		index
	}

	/// Binds a child namespace's name in the scope it was declared in, to the
	/// child's own entry. `Err` carries the definition already holding it.
	fn bind_child(
		&mut self,
		parent: Scope,
		name: SymbolU32,
		child: Namespace,
		visibility: Visibility,
	) -> Result<(), DefKey> {
		self.namespaces.try_insert_binding(
			parent.into(),
			BindingKey::ty(name),
			Binding::definition(
				DefKey::new(child, LocalDefIdx::SELF),
				visibility,
			),
		)
	}
}

impl<'ast, 'ctx> DefinitionRegistryBuilder<'ast, 'ctx> {
	fn scan_export_entry(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		entry: &ast::ExportEntry,
	) {
		let package = self.namespaces.scope(namespace).package_id;
		if package != self.root_package {
			return;
		}
		let external = match entry.alias {
			Some(span) => {
				let Ok(symbol) = self.intern_string(file_id, span) else {
					return;
				};
				Spanned {
					inner: symbol,
					span,
				}
			}
			None => entry.name,
		};
		let reference = SourceSpan::new(file_id, external.span);
		match self.exports.entry(external.inner) {
			std::collections::hash_map::Entry::Occupied(first) => {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::DuplicateExport.code())
						.with_message(format!(
							"duplicate export name `{}`",
							self.strings.resolve(external.inner).unwrap()
						))
						.with_label(
							reference
								.primary_label()
								.with_message("exported again here"),
						)
						.with_label(
							first
								.get()
								.external_span
								.secondary_label()
								.with_message("first exported here"),
						),
				);
			}
			std::collections::hash_map::Entry::Vacant(slot) => {
				slot.insert(ExportEntrySource {
					namespace,
					name: entry.name,
					external_span: reference,
				});
			}
		}
	}

	pub(super) fn scan_item(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		item: &'ast ast::Item,
	) {
		match item {
			ast::Item::Function {
				signature,
				pub_span,
				..
			}
			| ast::Item::FunctionDeclaration {
				signature,
				pub_span,
				..
			} => {
				let func_index = FunctionIdx::new(
					u32::try_from(self.functions.len()).unwrap(),
				);
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(
						DefKind::Function(func_index),
						signature.name.span,
					),
				);
				// A function is a value and, like a struct, its own type: each
				// one is a zero-sized type of its own (`foo<i32>`).
				let binding =
					Binding::definition(def_key, Visibility::from(*pub_span));
				self.insert_type_and_value(
					Namespace::from(namespace),
					signature.name.inner,
					binding.clone(),
					binding,
					signature.name.span,
				);

				let params =
					self.scan_free_function_params(file_id, &signature.params);
				let function_impls = self.synthesize_function_impls(
					file_id,
					namespace,
					signature.name.span,
				);
				self.functions.push(FunctionDef {
					file_id,
					namespace,
					owner: FunctionOwner::Free,
					name: signature.name,
					params,
					function_impls,
				});
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Function { item, func_index },
				});
			}
			ast::Item::Global {
				pub_span,
				mut_span,
				name,
				..
			} => {
				let global_index =
					GlobalIdx::new(u32::try_from(self.globals.len()).unwrap());
				let (
					trait_impl_index,
					value_assoc_type_index,
					mut_trait_impl_index,
				) = self.synthesize_global_impl(
					file_id,
					namespace,
					name.span,
					mut_span.is_some(),
				);
				self.globals.push(GlobalDef {
					file_id,
					namespace,
					name: *name,
					trait_impl_index,
					value_assoc_type_index,
					mut_trait_impl_index,
				});
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(DefKind::Global(global_index), name.span),
				);
				// The name is the global's zero-sized value and its own
				// type, the one `Global` is implemented for.
				let binding =
					Binding::definition(def_key, Visibility::from(*pub_span));
				self.insert_type_and_value(
					Namespace::from(namespace),
					name.inner,
					binding.clone(),
					binding,
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Global { global_index, item },
				});
			}
			ast::Item::Struct {
				pub_span,
				name,
				fields,
				..
			} => {
				let struct_index =
					StructIdx::new(u32::try_from(self.structs.len()).unwrap());
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(DefKind::Struct(struct_index), name.span),
				);
				// The name is also the struct's constructor, called like a
				// function. Constructing it takes every field, so it is only
				// as visible as the struct and every one of its fields.
				let constructor_visibility = fields.iter().fold(
					Visibility::from(*pub_span),
					|visibility, f| {
						visibility.cap(Visibility::from(f.inner.inner.pub_span))
					},
				);
				self.insert_type_and_value(
					Namespace::from(namespace),
					name.inner,
					Binding::definition(def_key, Visibility::from(*pub_span)),
					Binding::definition(def_key, constructor_visibility),
					name.span,
				);

				let mut field_defs: Vec<FieldDef> =
					Vec::with_capacity(fields.len());
				let mut lookup: HashMap<SymbolU32, FieldIdx> = HashMap::new();
				for field in fields.iter().map(|f| &f.inner.inner) {
					let index =
						FieldIdx::new(u32::try_from(field_defs.len()).unwrap());
					// A duplicate name keeps its slot (positions still match
					// the declaration) but is unreachable by name.
					if let Some(name) = field.name {
						if let Some(&first_index) = lookup.get(&name.inner) {
							let first_name = field_defs
								[usize::from(first_index)]
							.name
							.expect("only named fields are looked up");
							self.diagnostics.push(
								report_duplicate_struct_field(
									self.strings,
									file_id,
									name,
									first_name,
								),
							);
						} else {
							lookup.insert(name.inner, index);
						}
					}
					field_defs.push(FieldDef {
						name: field.name,
						pub_span: field.pub_span,
					});
				}

				self.structs.push(StructDef {
					file_id,
					namespace,
					name: *name,
					fields: field_defs.into_boxed_slice(),
					lookup,
				});
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Struct { struct_index, item },
				});
			}
			ast::Item::Enum {
				pub_span,
				name,
				variants,
				..
			} => {
				let enum_index =
					EnumIdx::new(u32::try_from(self.enums.len()).unwrap());
				let own_namespace = Namespace::Enum(enum_index);
				// All of the enum's variants in one `extend`, which is what keeps
				// `EnumDef::variants` contiguous.
				let first_variant =
					ConstIdx::new(u32::try_from(self.constants.len()).unwrap());
				self.constants.extend(variants.iter().map(|variant| {
					ConstDef {
						file_id,
						namespace,
						name: variant.inner.inner.name,
					}
				}));
				let end_variant =
					ConstIdx::new(u32::try_from(self.constants.len()).unwrap());
				self.enums.push(EnumDef {
					file_id,
					parent_namespace: namespace,
					name: *name,
					variants: first_variant..end_variant,
				});
				self.namespaces.enums.push(SymbolTable::new(file_id));
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(DefKind::Enum(enum_index), name.span),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Enum { enum_index, item },
				});

				// A variant's written value is read in the scope around the
				// enum, like any constant's initializer.
				for (offset, variant) in variants.iter().enumerate() {
					let variant = &variant.inner.inner;
					let const_index = ConstIdx::new(
						u32::from(first_variant)
							+ u32::try_from(offset).unwrap(),
					);
					let variant_key = self.push_def(
						own_namespace,
						ItemDef::new(
							DefKind::EnumVariant(const_index),
							variant.name.span,
						),
					);
					self.insert_binding(
						own_namespace,
						BindingKey::value(variant.name.inner),
						Binding::definition(variant_key, Visibility::Public),
						variant.name.span,
					);
					self.ast_nodes.push(AstEntry {
						file_id,
						namespace,
						node: AstNodeRef::EnumVariant {
							const_index,
							enum_index,
							item: variant,
						},
					});
				}
			}
			ast::Item::TypeAlias {
				pub_span,
				name,
				body,
				..
			} => {
				let type_alias_index = TypeAliasIdx::new(
					u32::try_from(self.type_aliases.len()).unwrap(),
				);
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(
						DefKind::TypeAlias(type_alias_index),
						name.span,
					),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				if body.is_none()
					&& self.namespaces.scope(namespace).package_id
						== self.stdlib_package
				{
					if let Some(name_str) = self.strings.resolve(name.inner) {
						if let Some(slot) =
							self.intrinsics.type_slot_mut(name_str)
						{
							*slot = Some(type_alias_index);
						}
					}
				}
				self.type_aliases.push(TypeAliasDef {
					file_id,
					namespace,
					name: *name,
				});
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::TypeAlias {
						item,
						type_alias_index,
					},
				});
			}
			ast::Item::Memory { pub_span, name, .. } => {
				let memory_index =
					MemoryIdx::new(u32::try_from(self.memories.len()).unwrap());
				let (trait_impl_index, size_assoc_type_index) =
					self.synthesize_memory_impl(file_id, namespace, name.span);
				self.memories.push(MemoryDef {
					file_id,
					namespace,
					name: *name,
					trait_impl_index,
					size_assoc_type_index,
				});
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(DefKind::Memory(memory_index), name.span),
				);
				let binding =
					Binding::definition(def_key, Visibility::from(*pub_span));
				self.insert_type_and_value(
					Namespace::from(namespace),
					name.inner,
					binding.clone(),
					binding,
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Memory { memory_index, item },
				});
			}
			ast::Item::Const { pub_span, name, .. } => {
				let const_index =
					ConstIdx::new(u32::try_from(self.constants.len()).unwrap());
				self.constants.push(ConstDef {
					file_id,
					namespace,
					name: *name,
				});
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(DefKind::Const(const_index), name.span),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::value(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Constant { const_index, item },
				});
			}
			ast::Item::Module {
				name,
				items,
				pub_span,
			} => {
				let module = self.push_module(
					ModuleDef {
						parent_namespace: namespace,
						declaration_file: file_id,
						own_file: file_id,
						name: *name,
						pub_span: *pub_span,
					},
					items.span,
				);
				if let Err(collision) = self.bind_child(
					namespace,
					name.inner,
					Namespace::Module(module),
					Visibility::from(*pub_span),
				) {
					self.diagnostics.push(
						DuplicateDefinitionDiagnostic {
							strings: self.strings,
							key: BindingKey::ty(name.inner),
							definitions: (
								self.definition_span(collision),
								SourceSpan::new(file_id, name.span),
							),
						}
						.report(),
					);
				}

				for item in items.inner.iter() {
					self.scan_item(
						file_id,
						Scope::Module(module),
						&item.inner.inner,
					);
				}
			}
			// Nothing to do: Phase 1a already created this module's
			// namespace (and set its `pub_span`) directly from vfs's
			// `SourceModule` tree, before any file's items were scanned.
			ast::Item::ModuleDeclaration { .. } => {}
			ast::Item::Trait {
				name,
				items,
				pub_span,
				..
			} => {
				let trait_index =
					TraitIdx(u32::try_from(self.traits.len()).unwrap());
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(DefKind::Trait(trait_index), name.span),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				if self.namespaces.scope(namespace).package_id
					== self.stdlib_package
				{
					if let Some(slot) = self.intrinsics.trait_slot_mut(
						self.strings.resolve(name.inner).unwrap(),
					) {
						*slot = Some(trait_index);
					}
				}
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Trait { trait_index, item },
				});

				let mut members: Vec<TraitMemberDef> = Vec::new();
				let mut bindings: HashMap<BindingKey, MemberIdx> =
					HashMap::new();
				for item in items.iter() {
					let member_index =
						MemberIdx::new(u32::try_from(members.len()).unwrap());
					let (member, key) = match &item.inner.inner {
						ast::TraitItem::Function { signature, .. } => {
							let params = self.scan_impl_function_params(
								file_id,
								&signature.params,
							);
							let is_method = params.first().is_some_and(|p| {
								p.inner == Keyword::SelfLower.symbol()
							});
							let function_impls = self
								.synthesize_function_impls(
									file_id,
									namespace,
									signature.name.span,
								);
							let function_index =
								self.push_function(FunctionDef {
									file_id,
									namespace,
									owner: FunctionOwner::Trait(trait_index),
									name: signature.name,
									params,
									function_impls,
								});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::TraitFunction {
									trait_index,
									item: &item.inner.inner,
									function_index,
								},
							});
							(
								TraitMemberDef {
									kind: if is_method {
										MemberKind::Method(function_index)
									} else {
										MemberKind::Function(function_index)
									},
									span: signature.name.span,
								},
								BindingKey::value(signature.name.inner),
							)
						}
						ast::TraitItem::Const { name, .. } => {
							let const_index = ConstIdx::new(
								u32::try_from(self.constants.len()).unwrap(),
							);
							self.constants.push(ConstDef {
								file_id,
								namespace,
								name: *name,
							});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::TraitConst {
									const_index,
									trait_index,
									item: &item.inner.inner,
								},
							});
							(
								TraitMemberDef {
									kind: MemberKind::Constant(const_index),
									span: name.span,
								},
								BindingKey::value(name.inner),
							)
						}
						ast::TraitItem::AssociatedType { name, .. } => {
							let assoc_type_index = AssocTypeIdx::new(
								u32::try_from(self.assoc_types.len()).unwrap(),
							);
							self.assoc_types.push(AssocTypeDef {
								file_id,
								namespace,
								name: *name,
							});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::TraitAssocType {
									assoc_type_index,
									trait_index,
									item: &item.inner.inner,
								},
							});
							(
								TraitMemberDef {
									kind: MemberKind::AssociatedType(
										assoc_type_index,
									),
									span: name.span,
								},
								BindingKey::ty(name.inner),
							)
						}
					};
					// A function is also its own type, so it holds the name in both
					// tiers, and a clash in either is one duplicate definition.
					let type_key = matches!(
						member.kind,
						MemberKind::Function(_) | MemberKind::Method(_)
					)
					.then(|| BindingKey::ty(key.symbol));
					let collision =
						std::iter::once(key).chain(type_key).find_map(|key| {
							bindings
								.get(&key)
								.map(|&collision| (key, collision))
						});
					if let Some((key, collision)) = collision {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key,
								definitions: (
									SourceSpan::new(
										file_id,
										members[usize::from(collision)].span,
									),
									SourceSpan::new(file_id, member.span),
								),
							}
							.report(),
						);
					} else {
						bindings.insert(key, member_index);
						if let Some(type_key) = type_key {
							bindings.insert(type_key, member_index);
						}
					}
					members.push(member);
				}

				let actual_index = self.push_trait(TraitDef {
					typeset: None,
					file_id,
					namespace,
					pub_span: *pub_span,
					name: *name,
					bindings,
					members,
				});
				debug_assert_eq!(trait_index, actual_index);
			}
			ast::Item::InherentImpl { items, .. } => {
				let mut members: Vec<InherentMemberDef> = Vec::new();
				let mut bindings: HashMap<BindingKey, MemberIdx> =
					HashMap::new();
				let block_index = InherentImplIdx(
					u32::try_from(self.inherent_impls.len()).unwrap(),
				);
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::InherentImplBlock { item, block_index },
				});
				for impl_item in items.iter() {
					let member_index =
						MemberIdx::new(u32::try_from(members.len()).unwrap());
					let (member, key, binding) = match &impl_item.inner.inner {
						ast::ImplItem::Function {
							signature,
							pub_span,
							..
						} => {
							let params = self.scan_impl_function_params(
								file_id,
								&signature.params,
							);
							let is_method = params.first().is_some_and(|p| {
								p.inner == Keyword::SelfLower.symbol()
							});
							let function_impls = self
								.synthesize_function_impls(
									file_id,
									namespace,
									signature.name.span,
								);
							let function_index =
								self.push_function(FunctionDef {
									file_id,
									namespace,
									owner: FunctionOwner::InherentImpl(
										block_index,
									),
									name: signature.name,
									params,
									function_impls,
								});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::InherentImplFunction {
									item: &impl_item.inner.inner,
									block_index,
									function_index,
								},
							});
							(
								InherentMemberDef {
									kind: if is_method {
										MemberKind::Method(function_index)
									} else {
										MemberKind::Function(function_index)
									},
									visibility: Visibility::from(*pub_span),
									span: signature.name.span,
								},
								BindingKey::value(signature.name.inner),
								member_index,
							)
						}
						ast::ImplItem::Constant { name, pub_span, .. } => {
							let const_index = ConstIdx::new(
								u32::try_from(self.constants.len()).unwrap(),
							);
							self.constants.push(ConstDef {
								file_id,
								namespace,
								name: *name,
							});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::InherentImplConst {
									const_index,
									item: &impl_item.inner.inner,
									block_index,
								},
							});
							(
								InherentMemberDef {
									kind: MemberKind::Constant(const_index),
									visibility: Visibility::from(*pub_span),
									span: name.span,
								},
								BindingKey::value(name.inner),
								member_index,
							)
						}
						ast::ImplItem::AssocType { .. } => {
							unimplemented!(
								"associated types are not allowed in inherent impls"
							)
						}
					};
					// A function is also its own type, so it holds the name in both
					// tiers, and a clash in either is one duplicate definition.
					let type_key = matches!(
						member.kind,
						MemberKind::Function(_) | MemberKind::Method(_)
					)
					.then(|| BindingKey::ty(key.symbol));
					let collision =
						std::iter::once(key).chain(type_key).find_map(|key| {
							bindings
								.get(&key)
								.map(|&collision| (key, collision))
						});
					if let Some((key, collision)) = collision {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key,
								definitions: (
									SourceSpan::new(
										file_id,
										members[usize::from(collision)].span,
									),
									SourceSpan::new(file_id, member.span),
								),
							}
							.report(),
						);
					} else {
						bindings.insert(key, binding);
						if let Some(type_key) = type_key {
							bindings.insert(type_key, binding);
						}
					}
					members.push(member);
				}

				let actual_index = self.push_inherent_impl(InherentImplDef {
					file_id,
					namespace,
					members,
					bindings,
				});
				debug_assert_eq!(block_index, actual_index);
			}
			ast::Item::Import {
				internal_name,
				external_name,
				items,
			} => {
				let internal_name = *internal_name;
				let external_name = Spanned {
					inner: self
						.intern_string(file_id, *external_name)
						.unwrap_or(Keyword::Error.symbol()),
					span: *external_name,
				};

				let import = self.push_import(
					ImportDef {
						external_name,
						internal_name,
						parent_namespace: namespace,
					},
					file_id,
					items.span,
				);
				let own_namespace = Namespace::Import(import);
				if let Err(collision) = self.bind_child(
					namespace,
					internal_name.inner,
					own_namespace,
					Visibility::Public,
				) {
					self.diagnostics.push(
						DuplicateDefinitionDiagnostic {
							strings: self.strings,
							key: BindingKey::ty(internal_name.inner),
							definitions: (
								self.definition_span(collision),
								SourceSpan::new(file_id, internal_name.span),
							),
						}
						.report(),
					);
				}

				for item in items.inner.iter() {
					match &item.inner.inner.declaration {
						ast::ImportDeclaration::Memory { name, .. } => {
							let memory_index = MemoryIdx::new(
								u32::try_from(self.memories.len()).unwrap(),
							);
							let (trait_impl_index, size_assoc_type_index) =
								self.synthesize_memory_impl(
									file_id, namespace, name.span,
								);
							self.memories.push(MemoryDef {
								file_id,
								namespace,
								name: *name,
								trait_impl_index,
								size_assoc_type_index,
							});
							let def_key = self.push_def(
								own_namespace,
								ItemDef::new(
									DefKind::Memory(memory_index),
									name.span,
								),
							);
							let binding = Binding::definition(
								def_key,
								Visibility::Public,
							);
							self.insert_type_and_value(
								own_namespace,
								name.inner,
								binding.clone(),
								binding,
								name.span,
							);
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::ImportedMemory {
									memory_index,
									import_index: import,
									decl: &item.inner.inner.declaration,
								},
							});
						}
						ast::ImportDeclaration::Function {
							signature, ..
						} => {
							let params = self.scan_free_function_params(
								file_id,
								&signature.params,
							);
							let function_impls = self
								.synthesize_function_impls(
									file_id,
									namespace,
									signature.name.span,
								);
							let function_index =
								self.push_function(FunctionDef {
									file_id,
									namespace,
									owner: FunctionOwner::Free,
									name: signature.name,
									params,
									function_impls,
								});
							let def_key = self.push_def(
								own_namespace,
								ItemDef::new(
									DefKind::Function(function_index),
									signature.name.span,
								),
							);
							let binding = Binding::definition(
								def_key,
								Visibility::Public,
							);
							self.insert_type_and_value(
								own_namespace,
								signature.name.inner,
								binding.clone(),
								binding,
								signature.name.span,
							);
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::ImportedFunction {
									function_index,
									import_index: import,
									decl: &item.inner.inner.declaration,
								},
							});
						}
						ast::ImportDeclaration::Global {
							mut_span,
							name,
							..
						} => {
							let global_index = GlobalIdx::new(
								u32::try_from(self.globals.len()).unwrap(),
							);
							let (
								trait_impl_index,
								value_assoc_type_index,
								mut_trait_impl_index,
							) = self.synthesize_global_impl(
								file_id,
								namespace,
								name.span,
								mut_span.is_some(),
							);
							self.globals.push(GlobalDef {
								file_id,
								namespace,
								name: *name,
								trait_impl_index,
								value_assoc_type_index,
								mut_trait_impl_index,
							});
							let def_key = self.push_def(
								own_namespace,
								ItemDef::new(
									DefKind::Global(global_index),
									name.span,
								),
							);
							let binding = Binding::definition(
								def_key,
								Visibility::Public,
							);
							self.insert_type_and_value(
								own_namespace,
								name.inner,
								binding.clone(),
								binding,
								name.span,
							);
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::ImportedGlobal {
									global_index,
									import_index: import,
									decl: &item.inner.inner.declaration,
								},
							});
						}
					}
				}
			}
			ast::Item::Use { tree, pub_span } => {
				self.scan_use_tree(namespace, tree, None, *pub_span);
			}
			ast::Item::Crate {
				pub_span,
				package,
				alias,
			} => {
				self.scan_crate_item(
					file_id, namespace, *pub_span, *package, *alias,
				);
			}
			ast::Item::Export { entry } => {
				self.scan_export_entry(file_id, namespace, &entry.inner);
			}
			ast::Item::ExportBlock { entries, .. } => {
				for entry in entries {
					self.scan_export_entry(
						file_id,
						namespace,
						&entry.inner.inner,
					);
				}
			}
			ast::Item::TypeSet {
				name,
				pub_span,
				members,
				..
			} => {
				let typeset_index = TypesetIdx::new(
					u32::try_from(self.typesets.len()).unwrap(),
				);
				let def_key = self.push_def(
					Namespace::from(namespace),
					ItemDef::new(DefKind::TypeSet(typeset_index), name.span),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				let trait_index = self.push_trait(TraitDef {
					typeset: Some(typeset_index),
					file_id,
					namespace,
					pub_span: *pub_span,
					name: *name,
					bindings: HashMap::new(),
					members: Vec::new(),
				});
				let member_impls: Box<[TraitImplIdx]> = members
					.iter()
					.map(|_| {
						self.push_trait_impl(TraitImplDef {
							file_id,
							namespace,
							members: Vec::new(),
							bindings: HashMap::new(),
						})
					})
					.collect();
				self.typesets.push(TypesetDef {
					file_id,
					namespace,
					name: *name,
					trait_index,
					member_impls,
				});
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::TypeSet {
						typeset_index,
						item,
					},
				});
			}
			ast::Item::TraitImpl { items, .. } => {
				let mut members: Vec<TraitMemberDef> = Vec::new();
				let mut bindings: HashMap<BindingKey, MemberIdx> =
					HashMap::new();
				// Reserved before the members, whose synthetic impls (each
				// function's `Call` and `Function`) take slots after it.
				let block_index = self.push_trait_impl(TraitImplDef {
					file_id,
					namespace,
					members: Vec::new(),
					bindings: HashMap::new(),
				});
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::TraitImplBlock { item, block_index },
				});
				for item in items.iter() {
					let member_index =
						MemberIdx::new(u32::try_from(members.len()).unwrap());
					let (member, key) = match &item.inner.inner {
						ast::ImplItem::Function { signature, .. } => {
							let params = self.scan_impl_function_params(
								file_id,
								&signature.params,
							);
							let is_method = params.first().is_some_and(|p| {
								p.inner == Keyword::SelfLower.symbol()
							});
							let function_impls = self
								.synthesize_function_impls(
									file_id,
									namespace,
									signature.name.span,
								);
							let function_index =
								self.push_function(FunctionDef {
									file_id,
									namespace,
									owner: FunctionOwner::TraitImpl(
										block_index,
									),
									name: signature.name,
									params,
									function_impls,
								});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::TraitImplFunction {
									item: &item.inner.inner,
									block_index,
									function_index,
								},
							});
							(
								TraitMemberDef {
									kind: if is_method {
										MemberKind::Method(function_index)
									} else {
										MemberKind::Function(function_index)
									},
									span: signature.name.span,
								},
								BindingKey::value(signature.name.inner),
							)
						}
						ast::ImplItem::Constant { name, .. } => {
							let const_index = ConstIdx::new(
								u32::try_from(self.constants.len()).unwrap(),
							);
							self.constants.push(ConstDef {
								file_id,
								namespace,
								name: *name,
							});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::TraitImplConstant {
									const_index,
									item: &item.inner.inner,
									block_index,
								},
							});
							(
								TraitMemberDef {
									kind: MemberKind::Constant(const_index),
									span: name.span,
								},
								BindingKey::value(name.inner),
							)
						}
						ast::ImplItem::AssocType { name, .. } => {
							let assoc_type_index = AssocTypeIdx::new(
								u32::try_from(self.assoc_types.len()).unwrap(),
							);
							self.assoc_types.push(AssocTypeDef {
								file_id,
								namespace,
								name: *name,
							});
							self.ast_nodes.push(AstEntry {
								file_id,
								namespace,
								node: AstNodeRef::TraitImplAssocType {
									assoc_type_index,
									item: &item.inner.inner,
									block_index,
								},
							});
							(
								TraitMemberDef {
									kind: MemberKind::AssociatedType(
										assoc_type_index,
									),
									span: name.span,
								},
								BindingKey::ty(name.inner),
							)
						}
					};

					// A function is also its own type, so it holds the name in both
					// tiers, and a clash in either is one duplicate definition.
					let type_key = matches!(
						member.kind,
						MemberKind::Function(_) | MemberKind::Method(_)
					)
					.then(|| BindingKey::ty(key.symbol));
					let collision =
						std::iter::once(key).chain(type_key).find_map(|key| {
							bindings
								.get(&key)
								.map(|&collision| (key, collision))
						});
					if let Some((key, collision)) = collision {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key,
								definitions: (
									SourceSpan::new(
										file_id,
										members[usize::from(collision)].span,
									),
									SourceSpan::new(file_id, member.span),
								),
							}
							.report(),
						);
					} else {
						bindings.insert(key, member_index);
						if let Some(type_key) = type_key {
							bindings.insert(type_key, member_index);
						}
					}
					members.push(member);
				}

				self.trait_impls[usize::from(block_index)] = TraitImplDef {
					file_id,
					namespace,
					bindings,
					members,
				};
			}
		}
	}

	fn scan_use_tree(
		&mut self,
		namespace: Scope,
		tree: &ast::Spanned<ast::UseTree>,
		parent_segment: Option<UsePathIndex>,
		pub_span: Option<TextSpan>,
	) {
		match &tree.inner {
			ast::UseTree::Name { segment, alias } => {
				let local_name = (*alias).unwrap_or(*segment).inner;
				let item_index = self.push_use_item(UseItemDef {
					kind: UseItemKind::Name {
						name: *segment,
						alias: *alias,
						prefix: parent_segment,
					},
					namespace,
					pub_span,
				});
				self.pending_named_imports
					.entry((namespace, local_name))
					.and_modify(|items| items.push(item_index))
					.or_insert_with(|| SmallVec::new(item_index));
			}
			ast::UseTree::Glob { segment } => {
				let path = self.push_use_path(UsePathSegment {
					segment: *segment,
					parent: parent_segment,
				});
				let item_index = self.push_use_item(UseItemDef {
					kind: UseItemKind::Glob {
						path,
						span: tree.span,
					},
					namespace,
					pub_span,
				});
				self.pending_glob_targets
					.entry(namespace)
					.and_modify(|items| items.push(item_index))
					.or_insert_with(|| SmallVec::new(item_index));
			}
			ast::UseTree::Path { segment, rest } => {
				let path = self.push_use_path(UsePathSegment {
					segment: *segment,
					parent: parent_segment,
				});
				self.scan_use_tree(namespace, rest, Some(path), pub_span);
			}
			ast::UseTree::Group { segment, branches } => {
				let path = self.push_use_path(UsePathSegment {
					segment: *segment,
					parent: parent_segment,
				});
				for branch in branches.inner.iter() {
					self.scan_use_tree(
						namespace,
						&branch.inner,
						Some(path),
						pub_span,
					);
				}
			}
		}
	}

	/// Collects parameters for free definitions, declarations, and imports.
	/// Reports duplicate names, rejects `self`, and preserves every slot.
	fn scan_free_function_params(
		&mut self,
		file_id: FileId,
		params: &[ast::Separated<Spanned<ast::FunctionParam>>],
	) -> Box<[Spanned<SymbolU32>]> {
		let mut names: Vec<Spanned<SymbolU32>> =
			Vec::with_capacity(params.len());
		for param in params.iter().map(|param| &param.inner.inner) {
			if let Some(&first) =
				names.iter().find(|s| s.inner == param.name.inner)
			{
				self.diagnostics.push(report_duplicate_function_parameter(
					self.strings,
					file_id,
					param.name,
					first,
				));
			}

			if param.name.inner == Keyword::SelfLower.symbol() {
				self.diagnostics
					.push(report_self_param_position(file_id, param.name.span));
			}
			names.push(param.name);
		}
		names.into_boxed_slice()
	}

	/// Validates a trait/impl function's parameter list: every name unique,
	/// `self` (if present) only as the very first parameter. Whether `self`
	/// is actually present — i.e. whether this member is
	/// `MemberKind::Method` or `MemberKind::Function` — is for the caller
	/// to read straight off `params.first()` against
	/// `Keyword::SelfLower.symbol()`, same constant-time check this uses;
	/// nothing here needs to hand that fact back out. Whether every other
	/// parameter is explicitly typed is a signature-phase concern
	/// (`MissingParameterType`), not this prescan's.
	fn scan_impl_function_params(
		&mut self,
		file_id: FileId,
		params: &[ast::Separated<Spanned<ast::FunctionParam>>],
	) -> Box<[Spanned<SymbolU32>]> {
		let mut names: Vec<Spanned<SymbolU32>> =
			Vec::with_capacity(params.len());
		for (index, param) in params.iter().enumerate() {
			let p = &param.inner.inner;
			let name = p.name;

			if let Some(&first) = names.iter().find(|s| s.inner == name.inner) {
				self.diagnostics.push(report_duplicate_function_parameter(
					self.strings,
					file_id,
					name,
					first,
				));
			}

			let is_self = name.inner == Keyword::SelfLower.symbol();
			if is_self && index != 0 {
				self.diagnostics
					.push(report_self_param_position(file_id, name.span));
			}

			names.push(name);
		}
		names.into_boxed_slice()
	}
}

fn report_duplicate_struct_field(
	strings: &StringInterner,
	file_id: FileId,
	name: Spanned<SymbolU32>,
	first: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateStructField.code())
		.with_message(format!("field `{name_str}` is already declared"))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("already declared"),
		)
		.with_label(
			SourceSpan::new(file_id, first.span)
				.secondary_label()
				.with_message(format!("`{name_str}` first declared here")),
		)
}

fn report_duplicate_function_parameter(
	strings: &StringInterner,
	file_id: FileId,
	name: Spanned<SymbolU32>,
	first: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateFunctionParameter.code())
		.with_message(format!(
			"identifier `{name_str}` is bound more than once in this parameter list"
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("used as parameter more than once"),
		)
		.with_label(
			SourceSpan::new(file_id, first.span)
				.secondary_label()
				.with_message(format!(
					"first use of `{name_str}` as a parameter"
				)),
		)
}

fn report_self_param_position(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::SelfParamPosition.code())
		.with_message(
			"`self` parameter is only allowed as the first parameter of an associated function",
		)
		.with_label(SourceSpan::new(file_id, span).primary_label())
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

	use super::super::paths::PathResolver;
	use super::*;
	use crate::testing::DiagnosticView;
	use crate::vfs;

	struct TestCase {
		graph: vfs::CompilationUnit,
		defs: DefinitionRegistry,
		diagnostics: Vec<Diagnostic<FileId>>,
	}

	/// The written trait impl declaring `member`, among the synthetic impls
	/// every function brings.
	fn written_trait_impl<'a>(
		case: &'a TestCase,
		member: &str,
	) -> &'a TraitImplDef {
		let key = BindingKey::value(case.graph.strings.get(member).unwrap());
		case.defs
			.trait_impls
			.iter()
			.find(|owner| owner.bindings.contains_key(&key))
			.expect("a written trait impl declares the member")
	}

	#[must_use]
	struct ResolutionResult<'a> {
		case: &'a TestCase,
		target: BindingTarget,
		diagnostics: Vec<Diagnostic<FileId>>,
	}

	impl ResolutionResult<'_> {
		fn target(&self) -> BindingTarget {
			self.target
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"resolution",
				&self.diagnostics,
				&self.case.graph.files,
			)
		}

		/// The namespace the resolved definition leads into.
		fn expect_namespace(&self) -> Namespace {
			self.expect_success();
			let BindingTarget::Accessible(key) = self.target else {
				unreachable!("`expect_success` found an accessible definition")
			};
			self.case
				.defs
				.namespaces
				.entered_by(key)
				.expect("expected a namespace")
		}

		fn expect_success(&self) -> DefKind {
			self.diagnostics().assert_none();
			let BindingTarget::Accessible(key) = self.target else {
				panic!(
					"expected an accessible definition, got {:?}",
					self.target
				);
			};
			key.symbol_kind(&self.case.defs)
		}
	}

	impl TestCase {
		fn from_graph(mut graph: vfs::CompilationUnit) -> Self {
			let parser_diagnostics = graph.collect_parser_diagnostics();
			DiagnosticView::new("parse", &parser_diagnostics, &graph.files)
				.assert_no_errors();
			let linker_diagnostics = graph.collect_linker_diagnostics();
			DiagnosticView::new("link", &linker_diagnostics, &graph.files)
				.assert_no_errors();

			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				&mut resolutions,
				graph.stdlib_package,
				graph.root_package,
			);
			// Only Phase 1 (this file) is under test here — `ast_nodes` is
			// Phase 2's input, and dropping it now is what lets `defs` (and
			// `graph`, moved below) outlive this constructor with no
			// lingering borrow between them.
			drop(ast_nodes);

			TestCase {
				graph,
				defs,
				diagnostics,
			}
		}

		fn new(source: &str) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			builder.load_stdlib();
			let root_id = builder
				.load_binary(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)])),
				)
				.unwrap();
			Self::from_graph(builder.build(root_id))
		}

		fn new_workspace(
			entry_path: vfs::AbsolutePath,
			workspace: HashMap<vfs::AbsolutePath, String>,
		) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			builder.load_stdlib();
			let root_id = builder
				.load_binary(
					entry_path,
					&vfs::VirtualFileSource::new(workspace),
				)
				.unwrap();
			Self::from_graph(builder.build(root_id))
		}

		/// A `"type": "std"` root — no embedded stdlib loaded, so `source`
		/// is the *entire* package graph, and `stdlib_package == root_package`.
		/// For tests that need to control every `#[intrinsic]` declaration
		/// themselves rather than asserting against the real, separately
		/// evolving `std/main.wx`.
		fn new_stdlib(source: &str) -> Self {
			let workspace = vfs::VirtualFileSource::new(HashMap::from([
				(
					vfs::AbsolutePath::new("/std/wx.json"),
					r#"{ "type": "std", "entry": "main.wx" }"#.to_string(),
				),
				(vfs::AbsolutePath::new("/std/main.wx"), source.to_string()),
			]));
			let graph =
				vfs::open_manifest(vfs::AbsolutePath::new("/std"), &workspace)
					.unwrap();
			Self::from_graph(graph)
		}

		fn root_namespace(&self) -> Scope {
			Scope::Package(self.defs.root_package)
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new("prescan", &self.diagnostics, &self.graph.files)
		}

		/// String queries use synthetic spans. Use `resolve_segments` with
		/// source path segments when asserting diagnostic locations.
		fn resolve(&mut self, tier: Tier, path: &str) -> ResolutionResult<'_> {
			self.resolve_from(self.root_namespace(), tier, path)
		}

		fn resolve_from(
			&mut self,
			namespace: Scope,
			tier: Tier,
			path: &str,
		) -> ResolutionResult<'_> {
			let file_id = self.defs.namespaces.file_id(namespace.into());
			let segments: Box<[ast::PathSegment]> = path
				.split("::")
				.map(|segment| ast::PathSegment {
					ident: Spanned {
						inner: self.graph.strings.get_or_intern(segment),
						span: TextSpan::new(0, 0),
					},
					type_args: Box::new([]),
				})
				.collect();
			self.resolve_segments(file_id, namespace, tier, &segments)
		}

		fn resolve_segments(
			&self,
			file_id: FileId,
			namespace: Scope,
			tier: Tier,
			segments: &[ast::PathSegment],
		) -> ResolutionResult<'_> {
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let target = PathResolver::new(
				&mut diagnostics,
				&mut resolutions,
				&self.graph.strings,
				&self.defs,
			)
			.resolve_path(file_id, namespace, segments, tier);
			ResolutionResult {
				case: self,
				target,
				diagnostics,
			}
		}

		fn namespace(&mut self, path: &str) -> Namespace {
			self.resolve(Tier::Type, path).expect_namespace()
		}

		fn scope(&mut self, path: &str) -> Scope {
			self.namespace(path).as_scope().expect("expected a scope")
		}
	}

	#[test]
	fn resolution_diagnostics_are_kept_separate_from_other_queries_and_prescan()
	{
		let mut case = TestCase::new("func f(x: i32, x: i32) {}");
		case.diagnostics()
			.assert_error(DiagnosticCode::DuplicateFunctionParameter);

		let missing = case.resolve(Tier::Value, "missing");
		missing
			.diagnostics()
			.assert_error(DiagnosticCode::UndeclaredIdentifier);
		assert!(matches!(missing.target(), BindingTarget::Error));

		assert!(matches!(
			case.resolve(Tier::Value, "f").expect_success(),
			DefKind::Function(_)
		));
		assert_eq!(case.diagnostics().all().len(), 1);
	}

	#[test]
	fn resolution_preserves_privacy_diagnostics_and_source_spans_with_a_recovered_target()
	 {
		let case = TestCase::new(indoc! {"
			mod outer {
				mod hidden { pub struct Visible(); }
			}
			type Alias = outer::hidden::Visible;
		"});
		case.diagnostics().assert_none();
		let package = &case.graph.packages[case.defs.root_package.as_usize()];
		let module = &package.modules[package.root.as_usize()];
		let ast::Item::TypeAlias {
			body: Some(body), ..
		} = &module.ast.items.last().unwrap().inner.inner
		else {
			panic!("expected an alias");
		};
		let ast::TypeExpression::Path(segments) = &body.inner else {
			panic!("expected a type path");
		};
		let result = case.resolve_segments(
			module.file_id,
			case.root_namespace(),
			Tier::Type,
			segments,
		);
		result.diagnostics().assert_error_with(
			DiagnosticCode::PrivateItem,
			|diagnostic| {
				assert_eq!(diagnostic.labels[0].file_id, module.file_id);
				assert_eq!(
					diagnostic.labels[0].range,
					std::ops::Range::from(segments[1].ident.span)
				);
			},
		);
		let BindingTarget::Accessible(key) = result.target() else {
			panic!("expected the public terminal definition to be recovered");
		};
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Struct(_)));
	}

	#[test]
	#[should_panic(expected = "expected no resolution diagnostics")]
	fn resolution_success_rejects_privacy_errors_even_with_an_accessible_target()
	 {
		let mut case =
			TestCase::new("mod outer { mod hidden { pub struct Visible(); } }");
		case.resolve(Tier::Type, "outer::hidden::Visible")
			.expect_success();
	}

	#[test]
	fn stdlib_primitive_slots_reference_the_matching_aliases() {
		let case = TestCase::new_stdlib(indoc! {"
			type u8;
			type i8;
			type u16;
			type i16;
			type u32;
			type i32;
			type u64;
			type i64;
			type f32;
			type f64;
			type bool;
			type char;
		"});
		case.diagnostics().assert_none();

		let intrinsics = &case.defs.intrinsics;
		for (slot, expected_name) in [
			(intrinsics.u8, "u8"),
			(intrinsics.i8, "i8"),
			(intrinsics.u16, "u16"),
			(intrinsics.i16, "i16"),
			(intrinsics.u32, "u32"),
			(intrinsics.i32, "i32"),
			(intrinsics.u64, "u64"),
			(intrinsics.i64, "i64"),
			(intrinsics.f32, "f32"),
			(intrinsics.f64, "f64"),
			(intrinsics.bool, "bool"),
			(intrinsics.char, "char"),
		] {
			let index = slot.unwrap_or_else(|| {
				panic!("missing intrinsic `{expected_name}`")
			});
			let name = case.defs.type_aliases[usize::from(index)].name.inner;
			assert_eq!(case.graph.strings.resolve(name), Some(expected_name));
		}
	}

	#[test]
	fn stdlib_operator_slots_reference_the_matching_traits() {
		let case = TestCase::new_stdlib(indoc! {"
			trait Add {}
			trait Sub {}
			trait Mul {}
			trait Div {}
			trait Rem {}
			trait Neg {}
			trait BitAnd {}
			trait BitOr {}
			trait BitXor {}
			trait Shl {}
			trait Shr {}
			trait BitNot {}
			trait Not {}
			trait PartialEq {}
			trait PartialOrd {}
		"});
		case.diagnostics().assert_none();

		let intrinsics = &case.defs.intrinsics;
		for (slot, expected_name) in [
			(intrinsics.add, "Add"),
			(intrinsics.sub, "Sub"),
			(intrinsics.mul, "Mul"),
			(intrinsics.div, "Div"),
			(intrinsics.rem, "Rem"),
			(intrinsics.neg, "Neg"),
			(intrinsics.bitand, "BitAnd"),
			(intrinsics.bitor, "BitOr"),
			(intrinsics.bitxor, "BitXor"),
			(intrinsics.shl, "Shl"),
			(intrinsics.shr, "Shr"),
			(intrinsics.bitnot, "BitNot"),
			(intrinsics.not, "Not"),
			(intrinsics.partial_eq, "PartialEq"),
			(intrinsics.partial_ord, "PartialOrd"),
		] {
			let index = slot.unwrap_or_else(|| {
				panic!("missing intrinsic `{expected_name}`")
			});
			let name = case.defs.traits[usize::from(index)].name.inner;
			assert_eq!(case.graph.strings.resolve(name), Some(expected_name));
		}
	}

	#[test]
	fn stdlib_missing_an_intrinsic_leaves_its_slot_empty() {
		let case = TestCase::new_stdlib(indoc! {"
			type u8;
		"});
		case.diagnostics().assert_none();
		assert!(case.defs.intrinsics.u8.is_some());
		assert!(case.defs.intrinsics.char.is_none());
		assert!(case.defs.intrinsics.add.is_none());
	}

	#[test]
	fn reserved_name_outside_stdlib_is_not_recorded_as_intrinsic() {
		let case = TestCase::new(indoc! {"
			type u8;
		"});
		case.diagnostics().assert_none();

		// The real stdlib's own `u8` must still be the one on record — the
		// same-named declaration in the binary package must not clobber it,
		// and (since it isn't in the stdlib package) must not be recorded
		// as an intrinsic at all.
		let root_namespace = case.root_namespace();
		let stdlib_namespace = Scope::Package(case.graph.stdlib_package);
		assert_ne!(
			root_namespace, stdlib_namespace,
			"the binary package must not be the stdlib package"
		);
		let u8_index =
			case.defs.intrinsics.u8.expect("u8 should still resolve");
		assert_eq!(
			case.defs.type_aliases[usize::from(u8_index)].namespace,
			stdlib_namespace,
			"u8 must still point into the stdlib package, not the binary one"
		);
	}

	#[test]
	fn type_and_trait_intrinsics_cannot_clobber_each_other() {
		// A type alias and a trait sharing a reserved name must land in
		// distinct slots — `type_slot_mut`/`trait_slot_mut` are separate
		// lookups specifically so this can't happen.
		let case = TestCase::new_stdlib(indoc! {"
			type Add;
			trait u8 { func f(self) -> Self; }
		"});
		case.diagnostics().assert_none();
		assert!(
			case.defs.intrinsics.add.is_none(),
			"a type alias named `Add` must not populate the trait slot"
		);
		assert!(
			case.defs.intrinsics.u8.is_none(),
			"a trait named `u8` must not populate the type slot"
		);
	}

	#[test]
	fn memory_identity_is_registered_without_resolving_bounds() {
		let mut case = TestCase::new(indoc! {r#"
			memory heap: UnknownSize;
			import "env" as host {
				memory shared: UnknownSize;
				func log(value: UnknownType);
				global counter: UnknownType;
			}
			use host::shared as shared_alias;
		"#});
		case.diagnostics().assert_no_errors();

		// An import block's declarations are written in the scope around
		// the block, so that is their namespace too.
		let root = case.root_namespace();
		let mut indices = Vec::new();
		for (path, name) in [("heap", "heap"), ("host::shared", "shared")] {
			let kind = case.resolve(Tier::Type, path).expect_success();
			assert_eq!(kind, case.resolve(Tier::Value, path).expect_success());
			let DefKind::Memory(index) = kind else {
				panic!("expected `{path}` to be a memory");
			};
			let memory = &case.defs.memories[usize::from(index)];
			assert_eq!(
				case.graph.strings.resolve(memory.name.inner),
				Some(name)
			);
			assert_eq!(memory.namespace, root);
			assert_eq!(
				memory.file_id,
				case.defs.namespaces.file_id(root.into())
			);
			indices.push(index);
		}
		assert_ne!(indices[0], indices[1]);
		for tier in [Tier::Type, Tier::Value] {
			assert_eq!(
				case.resolve(tier, "shared_alias").expect_success(),
				DefKind::Memory(indices[1]),
			);
		}
		let DefKind::Function(index) =
			case.resolve(Tier::Value, "host::log").expect_success()
		else {
			panic!("expected an imported function");
		};
		let function = &case.defs.functions[usize::from(index)];
		assert_eq!(function.namespace, root);
		assert_eq!(
			case.graph.strings.resolve(function.name.inner),
			Some("log")
		);
		assert!(matches!(
			case.resolve(Tier::Value, "host::counter").expect_success(),
			DefKind::Global(_),
		));
	}

	#[test]
	fn an_import_block_is_entered_through_a_path_but_never_written_in() {
		let mut case = TestCase::new(indoc! {r#"
			import "env" as host { func log(); }
		"#});
		case.diagnostics().assert_none();
		assert!(matches!(
			case.resolve(Tier::Value, "host::log").expect_success(),
			DefKind::Function(_),
		));
		// The block holds only its own declarations: it is not a scope, so
		// it binds neither its own name nor `self`, `crate` or `super`.
		for path in ["host::host", "host::self", "host::crate", "host::super"] {
			case.resolve(Tier::Type, path)
				.diagnostics()
				.assert_error(DiagnosticCode::UndeclaredIdentifier);
		}
	}

	/// An import block is a namespace like an enum is: `use` can reach its
	/// declarations by name, by glob, or through a re-export, and all three
	/// name the same function.
	#[test]
	fn an_import_blocks_declarations_can_be_brought_in_by_use() {
		let block = r#"import "console" as console { func log(x: i32); }"#;
		for imports in [
			"use console::log;",
			"use console::*;",
			"mod m { pub use super::console::log; } use m::log;",
		] {
			let mut case = TestCase::new(&format!("{block} {imports}"));
			case.diagnostics().assert_none();
			let original =
				case.resolve(Tier::Value, "console::log").expect_success();
			assert!(matches!(original, DefKind::Function(_)), "{imports}");
			assert_eq!(
				case.resolve(Tier::Value, "log").expect_success(),
				original,
				"{imports}"
			);
		}
	}

	#[test]
	fn member_identities_and_function_kinds_are_preserved_without_resolving_types()
	 {
		let mut case = TestCase::new_stdlib(indoc! {"
			const VALUE: Unknown = missing;
			trait Api {
				func make() -> Unknown;
				func get(self, value: Unknown) -> Unknown;
				const VALUE: Unknown;
				type Item: Unknown;
			}
			struct Host();
			impl Host {
				func make() -> Unknown { missing }
				func get(self, value: Unknown) -> Unknown { missing }
				const VALUE: Unknown = missing;
			}
			impl Api for Host {
				func make() -> Unknown { missing }
				func get(self, value: Unknown) -> Unknown { missing }
				const VALUE: Unknown = missing;
				type Item = Unknown;
			}
		"});
		case.diagnostics().assert_no_errors();

		let DefKind::Const(free_constant) =
			case.resolve(Tier::Value, "VALUE").expect_success()
		else {
			panic!("expected a free constant");
		};
		let mut ids =
			std::collections::HashSet::from([DefId::Const(free_constant)]);
		let members = case.defs.traits[0]
			.members
			.iter()
			.map(|member| member.kind)
			.chain(
				case.defs.inherent_impls[0]
					.members
					.iter()
					.map(|member| member.kind),
			)
			.chain(
				written_trait_impl(&case, "make")
					.members
					.iter()
					.map(|member| member.kind),
			);
		for kind in members {
			assert!(
				ids.insert(kind.def_id()),
				"members must have distinct identities"
			);
			let (name, expected) = match kind {
				MemberKind::Function(index) => {
					(case.defs.functions[usize::from(index)].name, "make")
				}
				MemberKind::Method(index) => {
					(case.defs.functions[usize::from(index)].name, "get")
				}
				MemberKind::Constant(index) => {
					(case.defs.constants[usize::from(index)].name, "VALUE")
				}
				MemberKind::AssociatedType(index) => {
					(case.defs.assoc_types[usize::from(index)].name, "Item")
				}
			};
			assert_eq!(case.graph.strings.resolve(name.inner), Some(expected));
		}
		assert_eq!(ids.len(), 12);
		for def in &case.defs.constants {
			assert_eq!(def.namespace, case.root_namespace());
		}
		for def in &case.defs.assoc_types {
			assert_eq!(def.namespace, case.root_namespace());
		}
	}

	#[test]
	fn type_and_value_definitions_can_share_a_name() {
		let mut case = TestCase::new("trait Item {} const Item: i32 = 1;");
		case.diagnostics().assert_none();
		assert!(matches!(
			case.resolve(Tier::Type, "Item").expect_success(),
			DefKind::Trait(_)
		));
		assert!(matches!(
			case.resolve(Tier::Value, "Item").expect_success(),
			DefKind::Const(_)
		));
	}

	#[test]
	fn a_function_name_is_also_its_type() {
		// A function is its own zero-sized type, so its name is bound in
		// both tiers, and a clash in either is one duplicate definition.
		let mut case = TestCase::new("func f() {}");
		case.diagnostics().assert_none();
		for tier in [Tier::Type, Tier::Value] {
			assert!(matches!(
				case.resolve(tier, "f").expect_success(),
				DefKind::Function(_)
			));
		}
		for source in [
			"trait Item {} func Item() {}",
			"func Item() {} const Item: i32 = 1;",
			"func f() {} func f() {}",
		] {
			TestCase::new(source)
				.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		}
	}

	#[test]
	fn a_member_function_name_is_also_a_type_member() {
		// A member function is its own type too, so it holds its name in the
		// member table's type tier, where an associated type of the same
		// name is a duplicate definition.
		for source in [
			"trait T { type X; func X(); }",
			"trait T {} struct S(); impl T for S { type X = (); func X() {} }",
		] {
			TestCase::new_stdlib(source)
				.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		}
		let case = TestCase::new_stdlib("struct S(); impl S { func f() {} }");
		case.diagnostics().assert_none();
		let symbol = case.graph.strings.get("f").unwrap();
		let owner = &case.defs.inherent_impls[0];
		assert_eq!(
			owner.bindings[&BindingKey::ty(symbol)],
			owner.bindings[&BindingKey::value(symbol)]
		);
	}

	#[test]
	fn a_struct_name_is_also_its_constructor() {
		// A struct is constructed by calling its name, so the name is a value
		// as well as a type, and a function cannot share it. (The constructor
		// is accessible where every field is, so the field is `pub`.)
		let mut case = TestCase::new("struct Item(pub x: i32);");
		case.diagnostics().assert_none();
		for namespace in [Tier::Type, Tier::Value] {
			assert!(matches!(
				case.resolve(namespace, "Item").expect_success(),
				DefKind::Struct(_)
			));
		}
		let case = TestCase::new("struct Item(); func Item() {}");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
	}

	#[test]
	fn duplicate_function_keeps_the_original_binding_and_continues_collection()
	{
		let source = "func f(original: i32) {} func f(replacement: i32) {} func after() {}";
		let mut case = TestCase::new(source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		let file_id =
			case.defs.namespaces.file_id(case.root_namespace().into());
		case.diagnostics().assert_error_with(
			DiagnosticCode::DuplicateDefinition,
			|diagnostic| {
				let first = source.find("f(").unwrap();
				let second = source.rfind("f(").unwrap();
				assert_eq!(diagnostic.labels[0].file_id, file_id);
				assert_eq!(diagnostic.labels[0].range, second..second + 1);
				assert_eq!(diagnostic.labels[1].file_id, file_id);
				assert_eq!(diagnostic.labels[1].range, first..first + 1);
			},
		);
		let DefKind::Function(index) =
			case.resolve(Tier::Value, "f").expect_success()
		else {
			panic!("expected a function");
		};
		assert_eq!(
			case.graph.strings.resolve(
				case.defs.functions[usize::from(index)].params[0].inner
			),
			Some("original")
		);
		assert!(matches!(
			case.resolve(Tier::Value, "after").expect_success(),
			DefKind::Function(_)
		));
	}

	#[test]
	fn duplicate_module_labels_declarations_in_source_order_and_keeps_the_file_module()
	 {
		// File modules are registered before inline modules, independently of source order.
		let source = "mod clash { pub func inline_only() {} } mod clash; func after() {}";
		let mut case = TestCase::new_workspace(
			vfs::AbsolutePath::new("/main.wx"),
			HashMap::from([
				(vfs::AbsolutePath::new("/main.wx"), source.to_string()),
				(
					vfs::AbsolutePath::new("/clash.wx"),
					"pub func file_only() {}".to_string(),
				),
			]),
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		let file_id =
			case.defs.namespaces.file_id(case.root_namespace().into());
		case.diagnostics().assert_error_with(
			DiagnosticCode::DuplicateDefinition,
			|diagnostic| {
				let first = source.find("clash").unwrap();
				let second = source.rfind("clash").unwrap();
				assert_eq!(diagnostic.labels[0].file_id, file_id);
				assert_eq!(diagnostic.labels[0].range, second..second + 5);
				assert_eq!(diagnostic.labels[1].file_id, file_id);
				assert_eq!(diagnostic.labels[1].range, first..first + 5);
			},
		);
		assert!(matches!(
			case.resolve(Tier::Value, "clash::file_only")
				.expect_success(),
			DefKind::Function(_)
		));
		assert!(matches!(
			case.resolve(Tier::Value, "after").expect_success(),
			DefKind::Function(_)
		));
	}

	#[test]
	fn duplicate_enum_variant_keeps_the_original_binding_and_later_variants() {
		let source = "enum E { Same, Same, After }";
		let mut case = TestCase::new(source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		let result = case.resolve(Tier::Value, "E::Same");
		let DefKind::EnumVariant(same) = result.expect_success() else {
			panic!("`E::Same` is an enum variant");
		};
		let key = result.target().def_key().unwrap();
		let first = source.find("Same").unwrap();
		assert_eq!(
			std::ops::Range::from(key.source_span(&case.defs.namespaces).span),
			first..first + 4
		);
		let DefKind::EnumVariant(after) =
			case.resolve(Tier::Value, "E::After").expect_success()
		else {
			panic!("`E::After` is an enum variant");
		};
		// The duplicate keeps its slot, so the enum's run of constants
		// matches the written list.
		let DefKind::Enum(enum_index) =
			case.resolve(Tier::Type, "E").expect_success()
		else {
			panic!("`E` is an enum");
		};
		let run = &case.defs.enums[usize::from(enum_index)].variants;
		assert_eq!(
			(u32::from(run.start), u32::from(run.end)),
			(u32::from(same), u32::from(same) + 3)
		);
		assert_eq!(u32::from(after), u32::from(same) + 2);
		let names: Vec<_> = (u32::from(run.start)..u32::from(run.end))
			.map(|index| {
				let name = case.defs.constants[index as usize].name.inner;
				case.graph.strings.resolve(name).unwrap()
			})
			.collect();
		assert_eq!(names, ["Same", "Same", "After"]);
	}

	#[test]
	fn duplicate_members_keep_the_original_binding_and_later_members() {
		for source in [
			"trait T { func f(original: i32); func f(replacement: i32); func after(); }",
			"struct S(); impl S { func f(original: i32) {} func f(replacement: i32) {} func after() {} }",
			"trait T {} struct S(); impl T for S { func f(original: i32) {} func f(replacement: i32) {} func after() {} }",
		] {
			let case = TestCase::new_stdlib(source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
			let f = BindingKey::value(case.graph.strings.get("f").unwrap());
			let after =
				BindingKey::value(case.graph.strings.get("after").unwrap());
			let (original, later) =
				if let Some(owner) = case.defs.inherent_impls.first() {
					(
						owner.members[usize::from(owner.bindings[&f])].kind,
						owner.members[usize::from(owner.bindings[&after])].kind,
					)
				} else if let Some(owner) = case
					.defs
					.trait_impls
					.iter()
					.find(|owner| owner.bindings.contains_key(&after))
				{
					(
						owner.members[usize::from(owner.bindings[&f])].kind,
						owner.members[usize::from(owner.bindings[&after])].kind,
					)
				} else {
					let owner = &case.defs.traits[0];
					(
						owner.members[usize::from(owner.bindings[&f])].kind,
						owner.members[usize::from(owner.bindings[&after])].kind,
					)
				};
			let MemberKind::Function(index) = original else {
				panic!("expected an associated function");
			};
			assert_eq!(
				case.graph.strings.resolve(
					case.defs.functions[usize::from(index)].params[0].inner
				),
				Some("original")
			);
			let MemberKind::Function(index) = later else {
				panic!("expected a later associated function");
			};
			assert_eq!(
				case.graph.strings.resolve(
					case.defs.functions[usize::from(index)].name.inner
				),
				Some("after")
			);
		}
	}

	#[test]
	fn tuple_struct_with_all_pub_fields_has_a_public_constructor() {
		let mut case = TestCase::new(indoc! {"
			pub struct Point(pub i32, pub i32);
		"});
		case.diagnostics().assert_none();

		let point_symbol = case.graph.strings.get_or_intern("Point");
		let root_namespace = case.root_namespace();
		let bindings =
			&case.defs.namespaces.symbols(root_namespace.into()).bindings;

		let value_binding = bindings
			.get(&BindingKey::value(point_symbol))
			.expect("`Point` should be bound in the value namespace");
		assert!(matches!(value_binding.target, BindingTarget::Accessible(_)));
		assert_eq!(value_binding.visibility, Visibility::Public);
	}

	#[test]
	fn tuple_struct_with_a_private_field_has_a_private_constructor() {
		let mut case = TestCase::new(indoc! {"
			pub struct Point(pub i32, i32);
		"});
		case.diagnostics().assert_none();

		let point_symbol = case.graph.strings.get_or_intern("Point");
		let root_namespace = case.root_namespace();
		let bindings =
			&case.defs.namespaces.symbols(root_namespace.into()).bindings;

		// The type itself is public...
		let type_binding = bindings
			.get(&BindingKey::ty(point_symbol))
			.expect("`Point` should be bound in the type namespace");
		assert!(matches!(type_binding.target, BindingTarget::Accessible(_)));
		assert_eq!(type_binding.visibility, Visibility::Public);

		// ...but the constructor is private, as the field it initializes is:
		// usable where the field is visible, and nowhere else.
		let value_binding = bindings
			.get(&BindingKey::value(point_symbol))
			.expect("`Point` should be bound in the value namespace");
		assert!(matches!(value_binding.target, BindingTarget::Accessible(_)));
		assert_eq!(value_binding.visibility, Visibility::Private);
	}

	#[test]
	fn duplicate_record_field_is_reported_but_keeps_its_own_slot() {
		let mut case = TestCase::new(indoc! {"
			struct Point( x: i32, x: i32 );
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateStructField.code())
		);

		// `Point` isn't necessarily `defs.structs[0]` — the real stdlib
		// (loaded by `TestCase::new`) declares its own structs (`Layout`,
		// `RawPtr`), so look it up by name rather than assuming an index.
		let DefKind::Struct(point_struct_index) =
			case.resolve(Tier::Type, "Point").expect_success()
		else {
			panic!("expected `Point` to be a struct")
		};
		let struct_def = &case.defs.structs[usize::from(point_struct_index)];

		let (fields, lookup) = (&struct_def.fields, &struct_def.lookup);
		// Both occurrences keep a real field slot — duplicate name isn't
		// dropped, only unreachable by name — so a later field's index
		// still matches its declaration position.
		assert_eq!(fields.len(), 2);
		let name = fields[0].name.unwrap().inner;
		assert_eq!(fields[1].name.unwrap().inner, name);
		// `lookup` only ever points at the first occurrence.
		assert_eq!(lookup.get(&name), Some(&FieldIdx::new(0)));
	}

	#[test]
	fn duplicate_function_parameter_is_reported_but_keeps_its_own_slot() {
		for (source, path) in [
			("func f(x: i32, x: i32) {}", "f"),
			("func f(x: i32, x: i32);", "f"),
			(
				r#"import "env" as host { func f(x: i32, x: i32); }"#,
				"host::f",
			),
		] {
			let mut case = TestCase::new(source);
			case.diagnostics()
				.assert_error(DiagnosticCode::DuplicateFunctionParameter);

			// Duplicate names still keep their positional slots.
			let DefKind::Function(index) =
				case.resolve(Tier::Value, path).expect_success()
			else {
				panic!("expected `{path}` to be a function");
			};
			let params = &case.defs.functions[usize::from(index)].params;
			assert_eq!(params.len(), 2);
			assert_eq!(params[0].inner, params[1].inner);
			let labels = &case.diagnostics[0].labels;
			assert_eq!(labels[0].range, std::ops::Range::from(params[1].span));
			assert_eq!(labels[1].range, std::ops::Range::from(params[0].span));
		}
	}

	#[test]
	fn self_in_a_free_function_is_rejected() {
		for source in [
			"func f(self) {}",
			"func f(self);",
			r#"import "env" as host { func f(self); }"#,
			r#"import "env" as host { func f(x: i32, self); }"#,
		] {
			let case = TestCase::new(source);
			case.diagnostics()
				.assert_error(DiagnosticCode::SelfParamPosition);
		}
	}

	#[test]
	fn duplicate_associated_function_parameters_keep_their_slots() {
		for source in [
			"trait T { func f(x: i32, x: i32, tail: i32); }",
			"struct S(); impl S { func f(x: i32, x: i32, tail: i32) {} }",
			"trait T {} struct S(); impl T for S { func f(x: i32, x: i32, tail: i32) {} }",
		] {
			let case = TestCase::new_stdlib(source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateFunctionParameter]);
			let function = &case.defs.functions[0];
			let names: Vec<_> = function
				.params
				.iter()
				.map(|param| case.graph.strings.resolve(param.inner).unwrap())
				.collect();
			assert_eq!(names, ["x", "x", "tail"]);
			case.diagnostics().assert_error_with(
				DiagnosticCode::DuplicateFunctionParameter,
				|diagnostic| {
					let first = source.find("x:").unwrap();
					let second = source.rfind("x:").unwrap();
					assert_eq!(diagnostic.labels[0].range, second..second + 1);
					assert_eq!(diagnostic.labels[1].range, first..first + 1);
				},
			);
		}
	}

	#[test]
	fn self_not_first_in_an_associated_function_is_rejected() {
		for source in [
			"trait T { func f(x: i32, self); }",
			"struct S(); impl S { func f(x: i32, self) {} }",
			"trait T {} struct S(); impl T for S { func f(x: i32, self) {} }",
		] {
			let case = TestCase::new_stdlib(source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::SelfParamPosition]);
			case.diagnostics().assert_error_with(
				DiagnosticCode::SelfParamPosition,
				|diagnostic| {
					let start = source.find("self").unwrap();
					assert_eq!(diagnostic.labels[0].range, start..start + 4);
				},
			);
		}
	}

	#[test]
	fn repeated_self_reports_both_duplicate_name_and_invalid_position() {
		let source = "trait T { func f(self, self); }";
		let case = TestCase::new_stdlib(source);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::DuplicateFunctionParameter,
			DiagnosticCode::SelfParamPosition,
		]);
		let params = &case.defs.functions[0].params;
		assert_eq!(params.len(), 2);
		let first = source.find("self").unwrap();
		let second = source.rfind("self").unwrap();
		case.diagnostics().assert_error_with(
			DiagnosticCode::DuplicateFunctionParameter,
			|diagnostic| {
				assert_eq!(diagnostic.labels[0].range, second..second + 4);
				assert_eq!(diagnostic.labels[1].range, first..first + 4);
			},
		);
		case.diagnostics().assert_error_with(
			DiagnosticCode::SelfParamPosition,
			|diagnostic| {
				assert_eq!(diagnostic.labels[0].range, second..second + 4);
			},
		);
	}

	#[test]
	fn receiver_presence_classifies_trait_and_impl_functions() {
		let case = TestCase::new_stdlib(indoc! {"
			trait T {
				func method(self, x: i32);
				func associated(x: i32);
			}
			struct S();
			impl S {
				func method(self, x: i32) {}
				func associated(x: i32) {}
			}
			impl T for S {
				func method(self, x: i32) {}
				func associated(x: i32) {}
			}
		"});
		case.diagnostics().assert_none();
		let members = case.defs.traits[0]
			.members
			.iter()
			.map(|member| member.kind)
			.chain(
				case.defs.inherent_impls[0]
					.members
					.iter()
					.map(|member| member.kind),
			)
			.chain(
				written_trait_impl(&case, "method")
					.members
					.iter()
					.map(|member| member.kind),
			);
		for kind in members {
			let (index, expected_name) = match kind {
				MemberKind::Method(index) => (index, "method"),
				MemberKind::Function(index) => (index, "associated"),
				_ => panic!("expected a function member"),
			};
			assert_eq!(
				case.graph.strings.resolve(
					case.defs.functions[usize::from(index)].name.inner
				),
				Some(expected_name)
			);
		}
	}

	#[test]
	fn module_declared_in_another_file_gets_a_namespace() {
		let mut case = TestCase::new_workspace(
			vfs::AbsolutePath::new("/main.wx"),
			HashMap::from([
				(vfs::AbsolutePath::new("/main.wx"), "mod math;".to_string()),
				(
					vfs::AbsolutePath::new("/math.wx"),
					"pub func add() -> i32 { 1 }".to_string(),
				),
			]),
		);
		case.diagnostics().assert_none();

		assert!(matches!(
			case.resolve(Tier::Value, "math::add").expect_success(),
			DefKind::Function(_)
		));
	}

	#[test]
	fn direct_lookup_never_falls_back_to_a_glob() {
		// `direct_lookup` is a plain `HashMap` read with no notion of globs
		// at all — `lookup`'s indirect half is what chases those. Checking
		// this directly, rather than only through the bindings a `use`
		// installs, pins down that boundary explicitly.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub func helper() -> i32 { 1 }
			}
			use a::*;
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let helper = case.graph.strings.get_or_intern("helper");

		assert!(matches!(
			case.defs.namespaces.lookup(
				&case.defs.use_items,
				root,
				root.into(),
				BindingKey::value(helper),
			),
			BindingLookup::Found { .. }
		));
		assert!(
			case.defs
				.namespaces
				.direct_lookup(root.into(), BindingKey::value(helper))
				.is_none(),
			"a glob installs no binding of its own, so `direct_lookup` \
			 must not find `helper` even though `lookup` does"
		);
	}

	#[test]
	fn indirect_lookup_ignores_private_globs_from_outside_the_declaring_namespace()
	 {
		// `b`'s glob is private, and `root` is neither `b` itself nor a
		// descendant of it — so from `root`'s perspective this is exactly
		// like any other private item: not visible. (A descendant of `b`
		// asking the same question gets a different answer — see
		// `indirect_lookup_reaches_a_private_glob_from_a_descendant_namespace`.)
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub func helper() -> i32 { 1 }
			}
			mod b {
				use crate::a::*;
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let b = case.scope("b");
		let helper = case.graph.strings.get_or_intern("helper");

		assert!(matches!(
			case.defs.namespaces.indirect_lookup(
				&case.defs.use_items,
				root,
				b.into(),
				BindingKey::value(helper),
			),
			BindingLookup::NotFound
		));
	}

	#[test]
	fn indirect_lookup_reaches_a_private_glob_from_a_descendant_namespace() {
		// Same private glob as the test above, but queried from `m::inner`
		// — a genuine descendant of the declaring namespace `m`, which
		// (same as any other private item) must see it. A blanket "only
		// `pub` globs are ever visible" rule would get this wrong: `pub`
		// only governs visibility to namespaces *outside* `m`'s own
		// subtree, not to `m` and its descendants, which already have
		// access to everything `m` privately imports.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub func helper() -> i32 { 1 }
			}
			mod m {
				use crate::a::*;
				mod inner {}
			}
		"});
		case.diagnostics().assert_none();

		let m = case.scope("m");
		let inner = case
			.resolve_from(m, Tier::Type, "inner")
			.expect_namespace()
			.as_scope()
			.unwrap();
		let helper = case.graph.strings.get_or_intern("helper");

		match case.defs.namespaces.indirect_lookup(
			&case.defs.use_items,
			inner,
			m.into(),
			BindingKey::value(helper),
		) {
			BindingLookup::Found {
				target: BindingTarget::Accessible(_),
				import: Some(_),
				..
			} => {}
			other => panic!(
				"a descendant of `m` should see `m`'s own private glob, \
				 got {other:?}"
			),
		}
	}

	#[test]
	fn indirect_lookup_finds_a_single_pub_glob_candidate() {
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub func helper() -> i32 { 1 }
			}
			mod hub {
				pub use crate::a::*;
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let a = case.scope("a");
		let hub = case.scope("hub");
		let helper = case.graph.strings.get_or_intern("helper");

		let Some(Binding {
			target: BindingTarget::Accessible(original),
			..
		}) = case
			.defs
			.namespaces
			.direct_lookup(a.into(), BindingKey::value(helper))
		else {
			panic!("`a::helper` should resolve directly");
		};

		match case.defs.namespaces.indirect_lookup(
			&case.defs.use_items,
			root,
			hub.into(),
			BindingKey::value(helper),
		) {
			BindingLookup::Found {
				target: BindingTarget::Accessible(found),
				visibility,
				import: Some(_),
			} => {
				assert_eq!(found, *original);
				assert_eq!(visibility, Visibility::Public);
			}
			other => panic!("expected a single found candidate, got {other:?}"),
		}
	}

	#[test]
	fn indirect_lookup_reports_ambiguous_for_two_disagreeing_pub_globs() {
		// Same shape the end-to-end `imports.rs` ambiguity tests use, but
		// nothing here ever consults `hub::pick` through a `use` item — the
		// raw primitive can still see (and report) the disagreement on
		// demand; the pipeline just never happens to ask.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub func pick() -> i32 { 1 }
			}
			mod b {
				pub func pick() -> i32 { 2 }
			}
			mod hub {
				pub use crate::a::*;
				pub use crate::b::*;
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let hub = case.scope("hub");
		let pick = case.graph.strings.get_or_intern("pick");

		match case.defs.namespaces.indirect_lookup(
			&case.defs.use_items,
			root,
			hub.into(),
			BindingKey::value(pick),
		) {
			BindingLookup::Ambiguous(candidates) => {
				assert_eq!(candidates.len(), 2);
			}
			other => {
				panic!("expected two disagreeing candidates, got {other:?}")
			}
		}
	}

	#[test]
	fn lookup_prefers_a_direct_binding_over_a_colliding_pub_glob() {
		// `hub` has both its own (private) `pick` and a `pub use a::*;`
		// that would also supply a *different* `pick` through the glob.
		// `lookup`'s direct-then-indirect composition must return the
		// direct one without ever consulting the indirect half.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub func pick() -> i32 { 1 }
			}
			mod hub {
				pub use crate::a::*;
				func pick() -> i32 { 2 }
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let hub = case.scope("hub");
		let pick = case.graph.strings.get_or_intern("pick");

		let Some(Binding {
			target: BindingTarget::Accessible(direct),
			..
		}) = case
			.defs
			.namespaces
			.direct_lookup(hub.into(), BindingKey::value(pick))
		else {
			panic!("`hub::pick` should be bound directly");
		};

		match case.defs.namespaces.lookup(
			&case.defs.use_items,
			root,
			hub.into(),
			BindingKey::value(pick),
		) {
			BindingLookup::Found {
				target: BindingTarget::Accessible(found),
				import: None,
				..
			} => {
				assert_eq!(
					found, *direct,
					"lookup should return hub's own `pick`, not a::pick \
					 through the glob"
				);
			}
			other => {
				panic!("expected the direct binding to win, got {other:?}")
			}
		}
	}

	#[test]
	fn import_external_names_are_decoded_during_prescan() {
		let case = TestCase::new(indoc! {"
            import \"slash\\\\n\" as host {
                func f();
            }
        "});
		case.diagnostics().assert_none();
		let import = &case.defs.imports[0];
		assert_eq!(
			case.graph
				.strings
				.resolve(import.external_name.inner)
				.unwrap(),
			"slash\\n"
		);
		let source = &case
			.graph
			.files
			.get(case.defs.namespaces.file_id(import.parent_namespace.into()))
			.unwrap()
			.source;
		assert_eq!(
			import.external_name.span.extract_str(source),
			r#""slash\\n""#
		);
	}

	#[test]
	fn exports_merge_items_by_decoded_external_name() {
		let case = TestCase::new(indoc! {"
            export {
                f as \"run\",
            }

            export f as \"start\";

            func f() {
            }

            func g() {
            }

            export g
        "});
		case.diagnostics().assert_none();
		assert_eq!(case.defs.exports.len(), 3);
		let f = case.graph.strings.get("f").unwrap();
		for name in ["run", "start"] {
			let export =
				&case.defs.exports[&case.graph.strings.get(name).unwrap()];
			assert_eq!(export.name.inner, f);
			assert_eq!(
				export.external_span.span.extract_str(
					&case
						.graph
						.files
						.get(export.external_span.file_id)
						.unwrap()
						.source
				),
				format!("\"{name}\"")
			);
		}
		assert!(
			!case
				.defs
				.exports
				.contains_key(&case.graph.strings.get("f").unwrap())
		);
	}

	#[test]
	fn duplicate_exports_keep_the_first_target_across_forms() {
		let case = TestCase::new(indoc! {"
            func first() {}
            func second() {}

            export {
                first as \"run\",
            }

            export second as \"run\"
        "});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateExport]);
		assert_eq!(case.defs.exports.len(), 1);
		let export =
			&case.defs.exports[&case.graph.strings.get("run").unwrap()];
		assert_eq!(export.name.inner, case.graph.strings.get("first").unwrap());
	}

	#[test]
	fn duplicate_exports_share_one_map_across_namespaces() {
		let case = TestCase::new(indoc! {"
            func first() {}

            export {
                first as \"run\",
            }

            mod nested {
                func run() {}

                export run
            }
        "});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateExport]);
		assert_eq!(case.defs.exports.len(), 1);
		let export =
			&case.defs.exports[&case.graph.strings.get("run").unwrap()];
		assert_eq!(export.name.inner, case.graph.strings.get("first").unwrap());
		assert_eq!(export.namespace, Scope::Package(case.defs.root_package));
		let diagnostic = &case.diagnostics[0];
		assert_eq!(diagnostic.labels.len(), 2);
	}

	#[test]
	fn export_aliases_are_decoded_once_and_retain_literal_spans() {
		let source = indoc! {"
            func f() {}

            export {
                f as \"line\\n\",
                f as \"slash\\\\n\",
                f as \"quote\\\"\",
                f as \"\",
            }
        "};
		let case = TestCase::new(source);
		case.diagnostics().assert_none();
		assert_eq!(case.defs.exports.len(), 4);
		for expected in ["line\n", "slash\\n", "quote\"", ""] {
			let symbol = case.graph.strings.get(expected).unwrap();
			let export = &case.defs.exports[&symbol];
			let file =
				case.graph.files.get(export.external_span.file_id).unwrap();
			let written = export.external_span.span.extract_str(&file.source);
			assert!(written.starts_with('"') && written.ends_with('"'));
		}
		assert!(case.graph.strings.get(r#""line\n""#).is_none());
	}

	#[test]
	fn unknown_escapes_in_import_and_export_names_are_semantic_errors() {
		for source in [
			indoc! {"
            import \"\\o\" as host {
                func f();
            }

            func after() {}
        "},
			indoc! {"
            func f() {}

            export {
                f as \"\\o\",
                f as \"valid\",
            }
        "},
			indoc! {"
            func f() {
            }

            export f as \"\\o\"
            export f as \"valid\"
        "},
		] {
			let case = TestCase::new(source);
			assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
			let diagnostic = &case.diagnostics[0];
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(DiagnosticCode::UnknownCharacterEscape.code())
			);
			assert_eq!(diagnostic.message, "unknown character escape: `o`");
			assert_eq!(diagnostic.labels.len(), 1);
			let offset = source.find(r"\o").unwrap() + 1;
			assert_eq!(diagnostic.labels[0].range, offset..offset + 1);
			assert_eq!(
				diagnostic.labels[0].message,
				"unknown character escape"
			);
			assert!(case.graph.strings.get(r#""\o""#).is_none());
			assert!(case.graph.strings.get(r"\o").is_none());
			if source.starts_with("import") {
				assert_eq!(
					case.defs.imports[0].external_name.inner,
					Keyword::Error.symbol()
				);
				assert!(case.graph.strings.get("after").is_some());
			} else {
				assert_eq!(case.defs.exports.len(), 1);
				assert!(
					case.defs.exports.contains_key(
						&case.graph.strings.get("valid").unwrap()
					)
				);
			}
		}
	}

	#[test]
	fn unknown_escape_labels_use_utf8_byte_offsets() {
		let source = indoc! {"
            import \"λ\\💥\" as host {
                func f();
            }
        "};
		let case = TestCase::new(source);
		assert_eq!(case.diagnostics.len(), 1);
		let diagnostic = &case.diagnostics[0];
		assert_eq!(
			diagnostic.code.as_deref(),
			Some(DiagnosticCode::UnknownCharacterEscape.code())
		);
		assert_eq!(diagnostic.message, "unknown character escape: `💥`");
		assert_eq!(&source[diagnostic.labels[0].range.clone()], "💥");
	}

	#[test]
	fn discarded_attributes_do_not_produce_literal_diagnostics() {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					indoc! {"
            #[tag = \"\\o\"
        "}
					.to_string(),
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id);
		let parser_diagnostics = graph.collect_parser_diagnostics();
		assert_eq!(parser_diagnostics.len(), 1, "{parser_diagnostics:?}");
		assert_eq!(
			parser_diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::UnclosedDelimiter.code())
		);
		let mut diagnostics = Vec::new();
		let mut resolutions = NameResolutions::default();
		let _ = DefinitionRegistry::build(
			&graph.packages,
			&graph.files,
			&mut graph.strings,
			&mut diagnostics,
			&mut resolutions,
			graph.stdlib_package,
			graph.root_package,
		);
		assert!(diagnostics.is_empty(), "{diagnostics:?}");
	}

	// ── `crate` items ────────────────────────────────────────────────────

	/// A real project on virtual files: `/app` is the root, and every
	/// `wx.json` is read, so a `crate` item looks its key up in an actual
	/// manifest.
	fn manifest_case(files: &[(&str, &str)]) -> TestCase {
		let workspace = vfs::VirtualFileSource::new(
			files
				.iter()
				.map(|(path, source)| {
					(vfs::AbsolutePath::new(*path), source.to_string())
				})
				.collect(),
		);
		let graph =
			vfs::open_manifest(vfs::AbsolutePath::new("/app"), &workspace)
				.unwrap();
		TestCase::from_graph(graph)
	}

	const APP_WITH_MATH: &str = r#"{
		"type": "bin",
		"entry": "main.wx",
		"dependencies": { "math": { "type": "local", "path": "../math" } }
	}"#;
	const MATH_MANIFEST: &str = r#"{ "type": "lib", "entry": "main.wx" }"#;
	const MATH_SOURCE: &str = "pub func add() {}";

	#[test]
	fn a_crate_item_binds_its_alias_to_the_declared_package() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"crate "math" as m;"#),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		assert_eq!(case.defs.namespaces.crate_items().len(), 1);
		let item = &case.defs.namespaces.crate_items()[0];
		assert_eq!(
			case.graph.strings.resolve(item.package_name.inner),
			Some("math")
		);
		assert_eq!(case.graph.strings.resolve(item.alias.inner), Some("m"));
		assert!(item.package.is_some());

		assert!(matches!(
			case.resolve(Tier::Value, "m::add").expect_success(),
			DefKind::Function(_)
		));
	}

	/// The point of the item over the old implicit binding: one package can
	/// be instantiated several times, each under an alias of its own.
	#[test]
	fn one_package_can_be_instantiated_under_several_aliases() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			(
				"/app/main.wx",
				r#"crate "math" as math; pub crate "math" as math2;"#,
			),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		assert_eq!(case.defs.namespaces.crate_items().len(), 2);
		let items = case.defs.namespaces.crate_items();
		assert_eq!(items[0].package, items[1].package);
		for path in ["math::add", "math2::add"] {
			assert!(matches!(
				case.resolve(Tier::Value, path).expect_success(),
				DefKind::Function(_)
			));
		}
	}

	/// A manifest key only makes a package available. Without a `crate`
	/// item nothing names it, which is what the implicit binding used to
	/// do on every key.
	#[test]
	fn a_declared_dependency_is_not_nameable_without_a_crate_item() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", "func main() {}"),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		let result = case.resolve(Tier::Value, "math::add");
		assert!(matches!(result.target(), BindingTarget::Error));
		result
			.diagnostics()
			.assert_error(DiagnosticCode::UndeclaredIdentifier);
	}

	#[test]
	fn a_crate_item_may_be_declared_in_a_nested_module() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			(
				"/app/main.wx",
				r#"mod outer { pub mod inner { pub crate "math" as m; } }"#,
			),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		assert!(matches!(
			case.resolve(Tier::Value, "outer::inner::m::add")
				.expect_success(),
			DefKind::Function(_)
		));
		// Bound in `inner`, not at the root.
		let result = case.resolve(Tier::Value, "m::add");
		assert!(matches!(result.target(), BindingTarget::Error));
	}

	#[test]
	fn a_private_crate_item_is_not_visible_outside_its_module() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"pub mod inner { crate "math" as m; }"#),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		case.resolve(Tier::Value, "inner::m::add")
			.diagnostics()
			.assert_error(DiagnosticCode::PrivateItem);
	}

	/// `pub crate` hands the dependency on: whoever depends on this package
	/// can name it through the alias. Without `pub` they cannot.
	#[test]
	fn a_pub_crate_item_exposes_the_dependency_to_consumers() {
		let app = r#"{
			"type": "bin",
			"entry": "main.wx",
			"dependencies": { "mid": { "type": "local", "path": "../mid" } }
		}"#;
		let mid = r#"{
			"type": "lib",
			"entry": "main.wx",
			"dependencies": { "math": { "type": "local", "path": "../math" } }
		}"#;
		let files = |mid_source: &'static str| {
			vec![
				("/app/wx.json", app),
				("/app/main.wx", r#"crate "mid" as mid;"#),
				("/mid/wx.json", mid),
				("/mid/main.wx", mid_source),
				("/math/wx.json", MATH_MANIFEST),
				("/math/main.wx", MATH_SOURCE),
			]
		};

		let mut public = manifest_case(&files(r#"pub crate "math" as math;"#));
		public.diagnostics().assert_none();
		assert!(matches!(
			public
				.resolve(Tier::Value, "mid::math::add")
				.expect_success(),
			DefKind::Function(_)
		));

		let mut private = manifest_case(&files(r#"crate "math" as math;"#));
		private.diagnostics().assert_none();
		private
			.resolve(Tier::Value, "mid::math::add")
			.diagnostics()
			.assert_error(DiagnosticCode::PrivateItem);
	}

	#[test]
	fn a_crate_item_naming_an_undeclared_dependency_is_an_error() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"crate "nope" as nope;"#),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);

		case.diagnostics()
			.assert_error(DiagnosticCode::UnknownCrate);
		assert!(case.defs.namespaces.crate_items()[0].package.is_none());

		// The alias is still bound, to a poisoned binding: a path through it
		// ends in `Error` without a second diagnostic, since the one at the
		// item already says what is wrong.
		let result = case.resolve(Tier::Value, "nope::add");
		assert!(matches!(result.target(), BindingTarget::Error));
		result.diagnostics().assert_none();
	}

	#[test]
	fn a_crate_alias_colliding_with_another_name_is_a_duplicate() {
		// Whichever is written first, the diagnostic points at both sites.
		for source in [
			r#"crate "math" as m; struct m();"#,
			r#"struct m(); crate "math" as m;"#,
		] {
			let case = manifest_case(&[
				("/app/wx.json", APP_WITH_MATH),
				("/app/main.wx", source),
				("/math/wx.json", MATH_MANIFEST),
				("/math/main.wx", MATH_SOURCE),
			]);

			case.diagnostics()
				.assert_error(DiagnosticCode::DuplicateDefinition);
			let alias = case.defs.namespaces.crate_items()[0].alias.span;
			let ranges: Vec<_> = case.diagnostics[0]
				.labels
				.iter()
				.map(|label| label.range.clone())
				.collect();
			assert!(
				ranges.contains(&(alias.start as usize..alias.end as usize)),
				"{source}: no label on the crate alias, got {ranges:?}"
			);
		}
	}

	/// The alias is a definition of its own, so it has the declaration span
	/// of every other definition, and a `use` can lead through it.
	#[test]
	fn a_crate_alias_is_a_definition_a_use_can_lead_through() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"crate "math" as m; use m::add;"#),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		let DefKind::Crate(index) =
			case.resolve(Tier::Type, "m").expect_success()
		else {
			panic!("expected a crate item");
		};
		let item = &case.defs.namespaces.crate_items()[usize::from(index)];
		let declared = DefKind::Crate(index).declared_at(&case.defs).unwrap();
		assert_eq!(
			(declared.file_id, declared.span),
			(item.file_id, item.alias.span)
		);

		assert!(matches!(
			case.resolve(Tier::Value, "add").expect_success(),
			DefKind::Function(_)
		));
	}

	/// The stdlib stays implicit: `std` needs no `crate` item.
	#[test]
	fn std_is_bound_without_a_crate_item() {
		let mut case = manifest_case(&[
			("/app/wx.json", r#"{ "type": "bin", "entry": "main.wx" }"#),
			("/app/main.wx", "func main() {}"),
		]);
		case.diagnostics().assert_none();

		assert!(matches!(
			case.resolve(Tier::Type, "std::Memory").expect_success(),
			DefKind::Trait(_)
		));
	}
}
