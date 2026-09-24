//! Phase 1 — the prescan. Walks every item in every file, allocates its TIR
//! entry and claims its name, and records it in `ast_nodes` for the
//! demand-driven signature pass to pick up. No type checking happens here.

// use super::*;

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{self, DefId, Keyword, Spanned, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	index::index_newtype,
	small_vec::SmallVec,
	tir::{imports::ImportResolver, literals::unescape_string_literal},
	vfs::{FileId, Files, Package, PackageId},
};

use super::imports;

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

	namespaces: Vec<Namespace>,
	package_namespaces: Vec<NamespaceIndex>,
	module_decls: Vec<ModuleDeclaration>,
	import_decls: Vec<ImportDeclaration>,
	ast_nodes: Vec<AstEntry<'ast>>,
	traits: Vec<TraitDef>,
	trait_impls: Vec<TraitImplDef>,
	inherent_impls: Vec<InherentImplDef>,
	structs: Vec<StructDef>,
	enums: Vec<EnumDef>,
	typesets: Vec<TypeSetDef>,
	functions: Vec<FunctionDef>,
	use_items: Vec<UseItemDef>,
	use_paths: Vec<UsePathSegment>,
	intrinsics: IntrinsicDefs,
	// Keyed by local (alias-or-original) name, not the name as written at the `use` site.
	pending_named_imports:
		HashMap<(NamespaceIndex, SymbolU32), SmallVec<UseItemIndex>>,
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
	pending_glob_targets: HashMap<NamespaceIndex, SmallVec<UseItemIndex>>,
}

index_newtype!(UsePathIndex);
index_newtype!(UseItemIndex);

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
	pub namespace: NamespaceIndex,
	pub pub_span: Option<TextSpan>,
	pub kind: UseItemKind,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum BindingNamespace {
	Type,
	Value,
}

impl BindingNamespace {
	pub(super) fn noun(self) -> &'static str {
		match self {
			BindingNamespace::Type => "type",
			BindingNamespace::Value => "value",
		}
	}
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct BindingKey {
	pub(super) namespace: BindingNamespace,
	pub(super) symbol: SymbolU32,
}

impl BindingKey {
	pub(super) fn new(namespace: BindingNamespace, symbol: SymbolU32) -> Self {
		Self { namespace, symbol }
	}

	pub(super) fn ty(symbol: SymbolU32) -> Self {
		Self {
			namespace: BindingNamespace::Type,
			symbol,
		}
	}

	pub(super) fn value(symbol: SymbolU32) -> Self {
		Self {
			namespace: BindingNamespace::Value,
			symbol,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TraitDef {
	pub def_id: DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	pub pub_span: Option<TextSpan>,
	pub name: Spanned<SymbolU32>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIndex>,
	pub members: Vec<TraitMemberDef>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TraitImplDef {
	pub def_id: DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	pub members: Vec<TraitMemberDef>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIndex>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct InherentImplDef {
	pub def_id: ast::DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIndex>,
	pub members: Vec<InherentMemberDef>,
}

/// Field identity only (names, `pub_span`, dedup/lookup) — field *types*
/// are `signatures::StructSignature::field_types`, index-aligned with
/// whichever `StructFields` variant is used here.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct StructDef {
	pub def_id: DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	pub fields: StructFields,
}

/// `Tuple` carries no `lookup` — a tuple field has no name to look up by.
#[cfg_attr(test, derive(serde::Serialize))]
pub enum StructFields {
	Record {
		fields: Box<[RecordFieldDef]>,
		#[cfg_attr(
			test,
			serde(serialize_with = "crate::testing::serialize_sorted_map")
		)]
		lookup: HashMap<SymbolU32, FieldIndex>,
	},
	Tuple {
		fields: Box<[TupleFieldDef]>,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct RecordFieldDef {
	pub name: Spanned<SymbolU32>,
	pub pub_span: Option<TextSpan>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TupleFieldDef {
	pub pub_span: Option<TextSpan>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct EnumDef {
	pub def_id: DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	pub variants_namespace: NamespaceIndex,
}

/// `typeset X: A + B { m1, m2 }` — `trait_index` is a compiler-generated
/// trait with no AST node of its own, reusing this typeset's own `def_id`
/// rather than minting a fresh one (nothing ever names it independently,
/// and "force this trait's signature" has to mean the same query as
/// "force this typeset's signature" anyway, since the trait's data — its
/// supertraits, from the typeset's own `: A + B` clause — is written as a
/// direct side effect of the typeset's own Phase 2 resolution, not through
/// an independent `ensure_signature` call on the trait itself).
/// `member_impls` is index-aligned with the AST's own `members` list —
/// one pre-allocated synthetic `impl <trait_index> for <member>` slot per
/// written member, same `def_id`-reuse reasoning, filled in with each
/// member's resolved type during that same Phase 2 pass.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct TypeSetDef {
	pub def_id: DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	pub trait_index: TraitIndex,
	pub member_impls: Box<[TraitImplIndex]>,
}

/// Shared by a free function, a trait member, and an impl method — one
/// arena, the same reason `signatures::FunctionSignature` covers all
/// three. Field *types* stay in that struct, index-aligned with `params`
/// here, same split as `StructDef`/`StructSignature`.
#[cfg_attr(test, derive(serde::Serialize))]
pub struct FunctionDef {
	pub def_id: DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	pub name: Spanned<SymbolU32>,
	pub params: Box<[Spanned<SymbolU32>]>,
}

index_newtype!(LocalDefIndex);
index_newtype!(MemberIndex);
index_newtype!(ModuleDeclIndex);
index_newtype!(ImportDeclIndex);
index_newtype!(NamespaceIndex);
index_newtype!(TraitIndex);
index_newtype!(InherentImplIndex);
index_newtype!(TraitImplIndex);
// Pre-allocated here (like `TraitIndex`), not lazily in `signatures.rs`
// (like `TypeAlias`) — a struct's identity doesn't depend on its own
// fields being resolved, so a self-/mutually-referencing pointer field
// needs a stable index without waiting on `ensure_signature`.
index_newtype!(StructIndex);
// A field's declaration-order position within its struct.
index_newtype!(FieldIndex);
// Pre-allocated here (like `StructIndex`) — an enum's variant namespace is
// created in Phase 1, so `NamespaceKind::Enum` needs a stable index to point
// at before `signatures.rs` has any reason to resolve this enum.
index_newtype!(EnumIndex);
// Pre-allocated here — a typeset's backing trait and per-member impl slots
// are created in Phase 1 (see `TypeSetDef`), so bound resolution can force
// them via `ensure_signature` before `signatures.rs` would otherwise reach
// this typeset in the general sweep.
index_newtype!(TypeSetIndex);
// Pre-allocated here (like `StructIndex`) — shared by a free function, a
// trait member, and an impl method alike (see `FunctionDef`), so a
// self-/mutually-referencing signature (`fn f<T: HasSize>(x: T::Size)`)
// needs a stable index the same way a struct field does.
index_newtype!(FunctionIndex);

#[cfg_attr(test, derive(serde::Serialize))]
pub struct TraitMemberDef {
	pub kind: MemberKind,
	pub accesses: Vec<SourceSpan>,
	pub span: TextSpan,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct InherentMemberDef {
	pub kind: MemberKind,
	pub visibility: Visibility,
	pub accesses: Vec<SourceSpan>,
	pub span: TextSpan,
}

impl LocalDefIndex {
	/// each module has a `self` binding which is the first binding in the list of it's bindings
	/// other modules can use it to reference it, for example `super`
	pub(super) const SELF: Self = LocalDefIndex(0);
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct AstEntry<'ast> {
	pub(super) def_id: DefId,
	pub(super) file_id: FileId,
	pub(super) namespace: NamespaceIndex,
	pub(super) node: AstNodeRef<'ast>,
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum AstNodeRef<'ast> {
	Function {
		item: &'ast ast::Item,
		function_index: FunctionIndex,
	},
	RecordStruct {
		struct_index: StructIndex,
		item: &'ast ast::Item,
	},
	TupleStruct {
		struct_index: StructIndex,
		item: &'ast ast::Item,
	},
	Enum {
		enum_index: EnumIndex,
		item: &'ast ast::Item,
	},
	Global {
		item: &'ast ast::Item,
	},
	Memory {
		item: &'ast ast::Item,
	},
	Constant {
		item: &'ast ast::Item,
	},
	TypeSet {
		typeset_index: TypeSetIndex,
		item: &'ast ast::Item,
	},
	TypeAlias {
		item: &'ast ast::Item,
	},
	Trait {
		trait_index: TraitIndex,
		item: &'ast ast::Item,
	},
	TraitFunction {
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
		function_index: FunctionIndex,
	},
	TraitConst {
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	},
	TraitAssocType {
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	},
	TraitImplBlock {
		item: &'ast ast::Item,
		block_index: TraitImplIndex,
	},
	TraitImplFunction {
		item: &'ast ast::ImplItem,
		block_index: TraitImplIndex,
		function_index: FunctionIndex,
	},
	TraitImplConstant {
		item: &'ast ast::ImplItem,
		block_index: TraitImplIndex,
	},
	TraitImplAssocType {
		item: &'ast ast::ImplItem,
		block_index: TraitImplIndex,
	},
	InherentImplBlock {
		item: &'ast ast::Item,
		block_index: InherentImplIndex,
	},
	InherentImplFunction {
		item: &'ast ast::ImplItem,
		block_index: InherentImplIndex,
		function_index: FunctionIndex,
	},
	InherentImplConst {
		item: &'ast ast::ImplItem,
		block_index: InherentImplIndex,
	},
	ImportedMemory {
		import_module_index: ImportDeclIndex,
		decl: &'ast ast::ImportDeclaration,
	},
	ImportedFunction {
		import_module_index: ImportDeclIndex,
		decl: &'ast ast::ImportDeclaration,
	},
	ImportedGlobal {
		import_module_index: ImportDeclIndex,
		decl: &'ast ast::ImportDeclaration,
	},
	Export {
		item: &'ast ast::Item,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct DefinitionRegistry {
	pub namespaces: Vec<Namespace>,
	/// Each package's own root namespace.
	#[cfg_attr(test, serde(skip))]
	pub package_namespaces: Vec<NamespaceIndex>,
	/// The scope each file's top-level items live in, indexed by `FileId`.
	#[cfg_attr(test, serde(skip))]
	pub file_namespaces: Vec<NamespaceIndex>,
	pub module_decls: Vec<ModuleDeclaration>,
	pub import_decls: Vec<ImportDeclaration>,
	pub traits: Vec<TraitDef>,
	pub trait_impls: Vec<TraitImplDef>,
	pub inherent_impls: Vec<InherentImplDef>,
	pub structs: Vec<StructDef>,
	pub enums: Vec<EnumDef>,
	pub typesets: Vec<TypeSetDef>,
	pub functions: Vec<FunctionDef>,
	pub use_items: Vec<UseItemDef>,
	pub use_paths: Vec<UsePathSegment>,
	/// The `DefKey` of every language builtin recognized by name in the
	/// stdlib package — primitive types (`u8`, `char`, `never`, ...) and
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
	pub u8: Option<DefKey>,
	pub i8: Option<DefKey>,
	pub u16: Option<DefKey>,
	pub i16: Option<DefKey>,
	pub u32: Option<DefKey>,
	pub i32: Option<DefKey>,
	pub u64: Option<DefKey>,
	pub i64: Option<DefKey>,
	pub f32: Option<DefKey>,
	pub f64: Option<DefKey>,
	pub bool: Option<DefKey>,
	pub char: Option<DefKey>,
	pub never: Option<DefKey>,
	pub add: Option<DefKey>,
	pub sub: Option<DefKey>,
	pub mul: Option<DefKey>,
	pub div: Option<DefKey>,
	pub rem: Option<DefKey>,
	pub neg: Option<DefKey>,
	pub bitand: Option<DefKey>,
	pub bitor: Option<DefKey>,
	pub bitxor: Option<DefKey>,
	pub shl: Option<DefKey>,
	pub shr: Option<DefKey>,
	pub bitnot: Option<DefKey>,
	pub not: Option<DefKey>,
	pub partial_eq: Option<DefKey>,
	pub partial_ord: Option<DefKey>,
}

impl IntrinsicDefs {
	/// The mutable slot for `name` if it's one of the recognized primitive
	/// type names — the one place that list is written.
	fn type_slot_mut(&mut self, name: &str) -> Option<&mut Option<DefKey>> {
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
			"never" => &mut self.never,
			_ => return None,
		})
	}

	/// The mutable slot for `name` if it's one of the recognized operator
	/// trait names — the one place that list is written.
	fn trait_slot_mut(&mut self, name: &str) -> Option<&mut Option<DefKey>> {
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
			_ => return None,
		})
	}
}

/// Back-pointer to whichever declaration created this namespace.
#[cfg_attr(test, derive(serde::Serialize))]
pub enum NamespaceKind {
	/// Index into `TIR::module_decls`.
	Module(ModuleDeclIndex),
	/// Index into `TIR::import_decls`.
	Import(ImportDeclIndex),
	/// A package's own root namespace. Carries the entry module's `FileId`
	/// for diagnostic spans; which package it is lives on
	/// [`ModuleNamespace::package`], the same as for every other namespace.
	Package(FileId),
	/// An enum's own variant scope — lets `Enum::Variant` (and eventually
	/// `use Enum::*;`) resolve through the same segment-walking `PathResolver`
	/// already uses for `module::item`, rather than a bespoke lookup. Unlike
	/// a module, this namespace is never the binding installed for the
	/// enum's own name — that stays `DefKind::Enum` so the enum keeps its
	/// own identity (diagnostics, type resolution) rather than being
	/// mistaken for a plain module. See `EnumDef::variants_namespace`.
	Enum(EnumIndex),
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

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum DefKind {
	Module(NamespaceIndex),
	Import(NamespaceIndex),
	Package(NamespaceIndex),
	Enum(NamespaceIndex),
	EnumVariant(DefId),
	Struct(DefId),
	Memory(DefId),
	Trait(DefId),
	TypeSet(DefId),
	Global(DefId),
	Function(DefId),
	Const(DefId),
	TraitAssocType(DefId),
	TypeAlias(DefId),
}

impl DefKind {
	/// What kind of symbol this is, for diagnostics.
	pub fn noun(self) -> &'static str {
		match self {
			DefKind::Module(_) => "module",
			DefKind::Import(_) => "import block",
			DefKind::Package(_) => "package",
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

	/// The namespace a path can continue walking into through this def, if
	/// any — every kind whose own identity *is* owning a `NamespaceIndex`.
	/// `Struct`/`Trait`/... are excluded even though some will eventually
	/// gain their own member namespaces too (impl/trait members): those are
	/// resolved through dedicated member lookups, never through this
	/// module's segment walk, so they never belong here.
	pub(super) fn as_namespace(self) -> Option<NamespaceIndex> {
		match self {
			DefKind::Module(idx)
			| DefKind::Import(idx)
			| DefKind::Package(idx)
			| DefKind::Enum(idx) => Some(idx),
			DefKind::EnumVariant(_)
			| DefKind::Struct(_)
			| DefKind::Memory(_)
			| DefKind::Trait(_)
			| DefKind::TypeSet(_)
			| DefKind::Global(_)
			| DefKind::Function(_)
			| DefKind::Const(_)
			| DefKind::TraitAssocType(_)
			| DefKind::TypeAlias(_) => None,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct ItemDef {
	pub(super) kind: DefKind,
	span: TextSpan,
	accesses: Vec<SourceSpan>,
}

impl ItemDef {
	fn new(kind: DefKind, span: TextSpan) -> Self {
		Self {
			kind,
			span,
			accesses: Vec::new(),
		}
	}
}

/// The symbol table for a module namespace — shared concept for both local
/// modules (`mod foo;` / `mod foo { }`) and import blocks (`import "env" { }`).
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Namespace {
	pub parent: Option<NamespaceIndex>,
	pub file_id: FileId,
	/// The package this namespace belongs to — every namespace is inside
	/// exactly one, so it's stored rather than recovered by walking parents.
	pub package_id: PackageId,
	pub kind: NamespaceKind,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, Binding>,
	pub items: Vec<ItemDef>,
	/// Namespaces brought into scope via `use path::*;`.  Checked during lookup
	/// after direct symbols but before walking to the parent.
	pub glob_imports: Vec<GlobImport>,
}

/// Lookup helpers over a namespace graph. Implemented on `[Namespace]`
/// rather than a dedicated wrapper type so it applies uniformly to
/// `DefinitionRegistryBuilder`'s still-growing `Vec<Namespace>`,
/// `DefinitionRegistry`'s frozen storage, and `ImportResolver`'s borrowed
/// `&mut [Namespace]` — all of them deref to `[Namespace]`.
pub(super) trait NamespaceLookup {
	/// Whether `namespace` is `ancestor` itself, or nested inside it.
	fn namespace_contains(
		&self,
		ancestor: NamespaceIndex,
		namespace: NamespaceIndex,
	) -> bool;

	/// An item declared `visibility` in `target_namespace` is reachable
	/// from `accessor` if it's `Public`, or if `target_namespace`
	/// contains `accessor`.
	fn is_accessible_from(
		&self,
		accessor: NamespaceIndex,
		target_namespace: NamespaceIndex,
		visibility: Visibility,
	) -> bool;

	/// Inserts `binding` under `key` in `namespace_idx`. `Err` carries the
	/// colliding `DefKey` when one was already there and both count as
	/// real occupants of the name — this is an error state, not merely an
	/// optional value, hence `Result` over `Option`. No diagnostics here —
	/// this only touches the namespace graph; a caller with
	/// `diagnostics`/`strings` on hand (see
	/// `DefinitionRegistryBuilder`/`ImportResolver`'s own `insert_binding`)
	/// is what turns a collision into a reported error.
	fn try_insert_binding(
		&mut self,
		namespace_idx: NamespaceIndex,
		key: BindingKey,
		binding: Binding,
	) -> Result<(), DefKey>;

	/// Records that `def_key` was referenced at `span` — go-to-definition
	/// and find-references over the *definition itself*, regardless of
	/// which name/path was used to reach it (a re-export's own consult of
	/// the original item counts here too, same as a direct reference).
	fn record_access(&mut self, def_key: DefKey, span: SourceSpan);

	/// Records that the binding under `key` in `namespace_idx` was
	/// consulted at `span` — distinct from `record_access`: this tracks
	/// whether *this specific name slot* (a direct declaration or a `use`)
	/// was ever looked up, which is what unused-import/unused-declaration
	/// diagnostics need and `record_access` alone can't answer (a
	/// re-export's own binding can sit unused while the original
	/// definition it points to is still referenced elsewhere).
	fn record_binding_access(
		&mut self,
		namespace_idx: NamespaceIndex,
		key: BindingKey,
		span: SourceSpan,
	);

	/// `namespace`'s own binding for `key` — a direct declaration or a
	/// resolved named `use`. No glob involved, so no ambiguity is
	/// possible: a `HashMap` has at most one entry per key. Accessor-blind
	/// by design — filtering happens one level up, once multiple
	/// candidates are actually competing.
	fn direct_lookup(
		&self,
		target_namespace: NamespaceIndex,
		key: BindingKey,
	) -> Option<(BindingTarget, Visibility)>;

	/// What `target_namespace` exposes through its `use path::*;` edges,
	/// filtered to the ones `accessor` may actually see — a glob is just
	/// another binding with a visibility, so a `pub` one is visible to
	/// anyone and a private one only to `target_namespace` itself and its
	/// descendants, the same rule `is_accessible_from` applies everywhere
	/// else. Recurses via `lookup` at each hop, not into itself, so a
	/// re-export chain composes through direct declarations and further
	/// re-exports alike. Terminates because `compute_glob_item` already
	/// rejects a cycle in this exact edge set before it can be walked.
	///
	/// `accessor` also matters once two *distinct* candidates compete: a
	/// candidate `accessor` could never legally choose is excluded right
	/// then, rather than surviving into a misleading `Ambiguous`. A lone
	/// candidate is always returned `Found`, visibility included,
	/// regardless of whether `accessor` can see *that candidate* — deferred
	/// to the caller, same as a direct (non-glob) hit already is.
	fn indirect_lookup(
		&self,
		use_items: &[UseItemDef],
		accessor: NamespaceIndex,
		target_namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup;

	/// What `target_namespace` exposes to `accessor` — `direct_lookup`,
	/// falling back to `indirect_lookup`. What a named `use a::b;` and a
	/// glob `use a::*;` should both find when asking `a` for the same
	/// name, whether `accessor` is `a` itself (or a descendant, consulting
	/// `a`'s own private globs) or is reaching in from elsewhere.
	fn lookup(
		&self,
		use_items: &[UseItemDef],
		accessor: NamespaceIndex,
		target_namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup;
}

/// The result of [`NamespaceLookup::lookup`]/[`NamespaceLookup::indirect_lookup`].
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
	Found(BindingTarget, Visibility),
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
	namespaces: &'a [Namespace],
	accessor: NamespaceIndex,
	candidates: Candidates,
}

enum Candidates {
	Empty,
	// An already-diagnosed broken edge. Never competes with a real
	// candidate for ambiguity — kept only as a fallback, and only the
	// first one seen, so a later re-export sees `Errored` instead of
	// re-diagnosing `Absent`, mirroring how a broken named `use` installs
	// its own `Error` placeholder. The moment a real candidate arrives,
	// this becomes moot for good: `finish` never looks at it again once
	// `One`/`Many` is reached, so there's nothing to keep it for.
	Error(Visibility),
	// `finish` itself never reads this span — `Found` doesn't carry one.
	// It's kept for `push`: if a second, distinct `DefKey` arrives later
	// and this candidate turns out to still be a real competitor, its
	// span is what seeds the new `Many` entry.
	One(BindingTarget, Visibility, SourceSpan),
	Many(Vec<(BindingTarget, SourceSpan)>),
}

impl<'a> CandidateMerge<'a> {
	fn new(namespaces: &'a [Namespace], accessor: NamespaceIndex) -> Self {
		Self {
			namespaces,
			accessor,
			candidates: Candidates::Empty,
		}
	}

	fn push(
		&mut self,
		target: BindingTarget,
		visibility: Visibility,
		span: SourceSpan,
	) {
		let Some(def_key) = target.def_key() else {
			if matches!(self.candidates, Candidates::Empty) {
				self.candidates = Candidates::Error(visibility);
			}
			return;
		};

		match &mut self.candidates {
			Candidates::Empty | Candidates::Error(..) => {
				self.candidates = Candidates::One(target, visibility, span);
			}
			Candidates::One(first_target, first_visibility, first_span) => {
				let first_key = first_target
					.def_key()
					.expect("a real candidate always carries a DefKey");

				if first_key == def_key {
					if matches!(target, BindingTarget::Accessible(_))
						&& matches!(
							*first_target,
							BindingTarget::Inaccessible(_)
						) {
						*first_target = target;
						*first_visibility = visibility;
						*first_span = span;
					}
					return;
				}

				let first_reachable = self.namespaces.is_accessible_from(
					self.accessor,
					first_key.namespace_idx,
					*first_visibility,
				);
				let this_reachable = self.namespaces.is_accessible_from(
					self.accessor,
					def_key.namespace_idx,
					visibility,
				);

				match (first_reachable, this_reachable) {
					(true, true) => {
						self.candidates = Candidates::Many(vec![
							(*first_target, *first_span),
							(target, span),
						]);
					}
					// Only one side is a real option for `accessor` — that
					// one just replaces `first` outright (or stays, if it
					// already was `first`); neither case is an ambiguity.
					(true, false) => {}
					(false, true) => {
						self.candidates =
							Candidates::One(target, visibility, span);
					}
					(false, false) => {}
				}
			}
			Candidates::Many(items) => {
				if !self.namespaces.is_accessible_from(
					self.accessor,
					def_key.namespace_idx,
					visibility,
				) {
					return;
				}
				let slot = items
					.iter_mut()
					.find(|(t, _)| t.def_key() == Some(def_key));
				match slot {
					Some(slot)
						if matches!(target, BindingTarget::Accessible(_))
							&& matches!(
								slot.0,
								BindingTarget::Inaccessible(_)
							) =>
					{
						*slot = (target, span);
					}
					Some(_) => {}
					None => items.push((target, span)),
				}
			}
		}
	}

	fn finish(self) -> BindingLookup {
		match self.candidates {
			Candidates::Empty => BindingLookup::NotFound,
			Candidates::Error(visibility) => {
				BindingLookup::Found(BindingTarget::Error, visibility)
			}
			Candidates::One(target, visibility, _) => {
				BindingLookup::Found(target, visibility)
			}
			Candidates::Many(items) => {
				BindingLookup::Ambiguous(items.into_boxed_slice())
			}
		}
	}
}

impl NamespaceLookup for [Namespace] {
	fn namespace_contains(
		&self,
		ancestor: NamespaceIndex,
		current: NamespaceIndex,
	) -> bool {
		let mut current = Some(current);
		while let Some(ns) = current {
			if ns == ancestor {
				return true;
			}
			current = self[usize::from(ns)].parent;
		}
		false
	}

	fn is_accessible_from(
		&self,
		accessor: NamespaceIndex,
		target_namespace: NamespaceIndex,
		visibility: Visibility,
	) -> bool {
		match visibility {
			Visibility::Public => true,
			Visibility::Private => {
				self.namespace_contains(target_namespace, accessor)
			}
		}
	}

	fn try_insert_binding(
		&mut self,
		namespace_idx: NamespaceIndex,
		key: BindingKey,
		binding: Binding,
	) -> Result<(), DefKey> {
		use std::collections::hash_map::Entry;

		match self[usize::from(namespace_idx)].bindings.entry(key) {
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

	fn record_access(&mut self, def_key: DefKey, span: SourceSpan) {
		self[usize::from(def_key.namespace_idx)].items
			[usize::from(def_key.def_idx)]
		.accesses
		.push(span);
	}

	fn record_binding_access(
		&mut self,
		namespace_idx: NamespaceIndex,
		key: BindingKey,
		span: SourceSpan,
	) {
		if let Some(binding) =
			self[usize::from(namespace_idx)].bindings.get_mut(&key)
		{
			binding.accesses.push(span);
		}
	}

	fn direct_lookup(
		&self,
		target_namespace: NamespaceIndex,
		key: BindingKey,
	) -> Option<(BindingTarget, Visibility)> {
		self[usize::from(target_namespace)]
			.bindings
			.get(&key)
			.map(|binding| (binding.target, binding.visibility))
	}

	fn indirect_lookup(
		&self,
		use_items: &[UseItemDef],
		accessor: NamespaceIndex,
		target_namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup {
		let mut candidates = CandidateMerge::new(self, accessor);

		for glob in self[usize::from(target_namespace)]
			.glob_imports
			.iter()
			.copied()
		{
			let item = &use_items[usize::from(glob.use_item)];
			let glob_visibility = Visibility::from(item.pub_span);
			if !self.is_accessible_from(
				accessor,
				target_namespace,
				glob_visibility,
			) {
				continue;
			}
			let UseItemKind::Glob { span, .. } = item.kind else {
				unreachable!("a glob edge is always produced by a glob item")
			};
			let edge_span = SourceSpan::new(
				self[usize::from(target_namespace)].file_id,
				span,
			);

			match self.lookup(use_items, accessor, glob.namespace, key) {
				BindingLookup::NotFound => {}
				BindingLookup::Found(target, visibility) => {
					candidates.push(target, visibility, edge_span);
				}
				BindingLookup::Ambiguous(nested) => {
					// Every nested entry was already confirmed accessible
					// to this same `accessor` one recursion level down
					// (that's what let it survive into `Ambiguous` at
					// all) — `Public` is just a stand-in that reproduces
					// that same "yes" when re-checked just below, not a
					// claim about its real declared visibility.
					for (target, span) in nested.iter().copied() {
						candidates.push(target, Visibility::Public, span);
					}
				}
			}
		}

		candidates.finish()
	}

	fn lookup(
		&self,
		use_items: &[UseItemDef],
		accessor: NamespaceIndex,
		target_namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup {
		match self.direct_lookup(target_namespace, key) {
			Some((target, visibility)) => {
				BindingLookup::Found(target, visibility)
			}
			None => {
				self.indirect_lookup(use_items, accessor, target_namespace, key)
			}
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
	pub(super) accesses: Vec<SourceSpan>,
	source: BindingSource,
}

impl Binding {
	fn definition(key: DefKey, visibility: Visibility) -> Self {
		Self::definition_with_target(BindingTarget::Accessible(key), visibility)
	}

	/// Like `definition`, but for the rare case where a direct declaration
	/// doesn't bind `Accessible` outright — a tuple struct's own value-namespace
	/// binding (its constructor) is `Inaccessible` when any field is private,
	/// since the type itself is still fine to name, but nothing outside the
	/// declaring namespace can construct it.
	fn definition_with_target(
		target: BindingTarget,
		visibility: Visibility,
	) -> Self {
		Self {
			target,
			accesses: Vec::new(),
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
			accesses: Vec::new(),
			visibility,
			source: BindingSource::Import(index),
		}
	}

	/// Where this binding itself was declared. For an import this is the local
	/// name at the `use` site, not the definition its target eventually names.
	pub(super) fn declaration_span(
		&self,
		namespaces: &[Namespace],
		use_items: &[UseItemDef],
	) -> SourceSpan {
		match self.source {
			BindingSource::Definition => {
				let def_key = match self.target {
					BindingTarget::Accessible(key)
					| BindingTarget::Inaccessible(key) => key,
					BindingTarget::Error => {
						unreachable!(
							"a definition binding cannot target recovery state"
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
				SourceSpan::new(
					namespaces[usize::from(item.namespace)].file_id,
					span,
				)
			}
		}
	}
}

/// Declaration-site metadata for a locally-defined module (`mod foo;` / `mod foo { }`).
#[cfg_attr(test, derive(serde::Serialize))]
pub struct ModuleDeclaration {
	pub namespace_idx: NamespaceIndex,
	/// File containing the `mod foo;` or `mod foo { }` declaration.
	pub declaration_file_id: FileId,
	/// File that IS this module (`foo.wx`). `None` for inline modules.
	pub content_file_id: Option<FileId>,
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
	pub namespace: NamespaceIndex,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct ImportDeclaration {
	pub namespace_idx: NamespaceIndex,
	pub external_name: ast::Spanned<SymbolU32>,
	pub internal_name: ast::Spanned<SymbolU32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum MemberKind {
	Function(DefId),
	Method(DefId),
	Constant(DefId),
	AssociatedType(DefId),
}

impl MemberKind {
	pub fn def_id(self) -> DefId {
		match self {
			Self::Function(id) => id,
			Self::Method(id) => id,
			Self::Constant(id) => id,
			Self::AssociatedType(id) => id,
		}
	}

	pub fn binding_namespace(self) -> BindingNamespace {
		match self {
			Self::AssociatedType(_) => BindingNamespace::Type,
			Self::Function(_) | Self::Method(_) | Self::Constant(_) => {
				BindingNamespace::Value
			}
		}
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct DefKey {
	pub(super) namespace_idx: NamespaceIndex,
	pub(super) def_idx: LocalDefIndex,
}

impl DefKey {
	#[inline]
	pub fn new(namespace_idx: NamespaceIndex, def_idx: LocalDefIndex) -> Self {
		Self {
			namespace_idx,
			def_idx,
		}
	}

	#[inline]
	pub fn source_span(self, namespaces: &[Namespace]) -> SourceSpan {
		let namespace = &namespaces[usize::from(self.namespace_idx)];
		SourceSpan::new(
			namespace.file_id,
			namespace.items[usize::from(self.def_idx)].span,
		)
	}

	#[inline]
	pub fn symbol_kind(self, defs: &DefinitionRegistry) -> DefKind {
		let namespace = &defs.namespaces[usize::from(self.namespace_idx)];
		namespace.items[usize::from(self.def_idx)].kind
	}
}

#[must_use]
struct Declared<T: Copy> {
	value: T,
	collision: Option<DefKey>,
}

impl<T: Copy> Declared<T> {
	fn new(value: T) -> Self {
		Self {
			value,
			collision: None,
		}
	}

	fn with_collision(value: T, collision: DefKey) -> Self {
		Self {
			value,
			collision: Some(collision),
		}
	}

	fn report_with(self, f: impl FnOnce(DefKey)) -> T {
		if let Some(existing) = self.collision {
			f(existing);
		}
		self.value
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
				self.key.namespace.noun(),
			)))
	}
}

impl DefinitionRegistry {
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
		stdlib_package: PackageId,
	) -> (Self, Vec<AstEntry<'ast>>) {
		DefinitionRegistryBuilder::build(
			packages,
			files,
			strings,
			diagnostics,
			stdlib_package,
		)
	}
}

impl<'ast, 'ctx> DefinitionRegistryBuilder<'ast, 'ctx> {
	fn build(
		packages: &'ast [Package],
		files: &'ctx Files,
		strings: &'ctx mut ast::StringInterner,
		diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
		stdlib_package: PackageId,
	) -> (DefinitionRegistry, Vec<AstEntry<'ast>>) {
		let package_namespaces: Vec<NamespaceIndex> = (0..packages.len())
			.map(|i| NamespaceIndex(u32::try_from(i).unwrap()))
			.collect();

		let namespaces: Vec<Namespace> = packages
			.iter()
			.enumerate()
			.map(|(index, package)| {
				let namespace_idx =
					NamespaceIndex(u32::try_from(index).unwrap());
				let mut namespace = Namespace {
					parent: None,
					package_id: package.id,
					kind: NamespaceKind::Package(
						package.modules[package.root.as_usize()].file_id,
					),
					file_id: package.modules[package.root.as_usize()].file_id,
					bindings: HashMap::new(),
					items: vec![ItemDef::new(
						DefKind::Package(namespace_idx),
						TextSpan::new(0, 0),
					)],
					glob_imports: Vec::new(),
				};
				namespace.bindings.insert(
					BindingKey::ty(ast::Keyword::SelfLower.symbol()),
					Binding::definition(
						DefKey::new(namespace_idx, LocalDefIndex::SELF),
						Visibility::Public,
					),
				);
				namespace.bindings.insert(
					BindingKey::ty(ast::Keyword::Crate.symbol()),
					Binding::definition(
						DefKey::new(namespace_idx, LocalDefIndex::SELF),
						Visibility::Public,
					),
				);

				// TODO: I want to remove this later, the declaration should be defined in the crate itself
				// Here's an example:
				// crate foo;
				// pub crate bar;
				// We will use pub modifier here to set Visibility in that symbol
				// right now it's just private, but in the future we could walk downstream the dependency chain
				// this will be a neat way to expose peer dependencies
				for (&name, &dependency_id) in package.dependencies.iter() {
					namespace.bindings.insert(
						BindingKey::ty(name),
						Binding::definition(
							DefKey::new(
								package_namespaces[dependency_id.as_usize()],
								LocalDefIndex::SELF,
							),
							Visibility::Public,
						),
					);
				}

				namespace
			})
			.collect();

		let mut builder = Self {
			ast_nodes: Vec::new(),
			diagnostics,
			namespaces,
			package_namespaces,
			import_decls: Vec::new(),
			module_decls: Vec::new(),
			strings,
			files,
			stdlib_package,
			traits: Vec::new(),
			trait_impls: Vec::new(),
			inherent_impls: Vec::new(),
			structs: Vec::new(),
			enums: Vec::new(),
			typesets: Vec::new(),
			functions: Vec::new(),
			use_items: Vec::new(),
			use_paths: Vec::new(),
			intrinsics: IntrinsicDefs::default(),
			pending_named_imports: HashMap::new(),
			pending_glob_targets: HashMap::new(),
		};

		let file_namespaces = builder.compute_file_namespaces(packages);
		for source_module in packages
			.iter()
			.flat_map(|package_graph| package_graph.modules.iter())
		{
			let namespace_idx =
				file_namespaces[source_module.file_id.as_usize()];
			for item in source_module.ast.items.iter() {
				builder.scan_item(
					source_module.file_id,
					namespace_idx,
					&item.inner.inner,
				);
			}
		}

		ImportResolver::resolve_imports(
			builder.diagnostics,
			builder.strings,
			&mut builder.namespaces,
			&builder.use_items,
			&builder.use_paths,
			&builder.pending_named_imports,
			&builder.pending_glob_targets,
		);

		let registry = DefinitionRegistry {
			namespaces: builder.namespaces,
			package_namespaces: builder.package_namespaces,
			file_namespaces,
			module_decls: builder.module_decls,
			import_decls: builder.import_decls,
			traits: builder.traits,
			trait_impls: builder.trait_impls,
			inherent_impls: builder.inherent_impls,
			structs: builder.structs,
			enums: builder.enums,
			typesets: builder.typesets,
			functions: builder.functions,
			use_items: builder.use_items,
			use_paths: builder.use_paths,
			intrinsics: builder.intrinsics,
		};
		(registry, builder.ast_nodes)
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
	fn compute_file_namespaces(
		&mut self,
		packages: &[Package],
	) -> Vec<NamespaceIndex> {
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
			let namespace_idx = match &source_module.declaration {
				None => self.package_namespaces[package.id.as_usize()],
				Some(declaration) => {
					let parent_module =
						&package.modules[declaration.parent.as_usize()];
					let parent_namespace =
						file_namespaces[parent_module.file_id.as_usize()];
					let namespace_idx = NamespaceIndex(
						u32::try_from(self.namespaces.len()).unwrap(),
					);
					let module_declaration_idx =
						self.push_module_declaration(ModuleDeclaration {
							namespace_idx,
							declaration_file_id: parent_module.file_id,
							content_file_id: Some(source_module.file_id),
							name: declaration.name,
							pub_span: declaration.pub_span,
						});
					debug_assert_eq!(
						namespace_idx,
						self.declare_child_namespace(
							parent_namespace,
							source_module.file_id,
							declaration.name.inner,
							NamespaceKind::Module(module_declaration_idx),
							TextSpan::new(0, u32::MAX),
							Visibility::from(declaration.pub_span),
						)
						.report_with(|collision| {
							self.diagnostics.push(
								DuplicateDefinitionDiagnostic {
									strings: self.strings,
									key: BindingKey::ty(declaration.name.inner),
									definitions: (
										collision.source_span(&self.namespaces),
										SourceSpan::new(
											parent_module.file_id,
											declaration.name.span,
										),
									),
								}
								.report(),
							)
						})
					);
					namespace_idx
				}
			};
			file_namespaces.push(namespace_idx);
		}

		file_namespaces
	}

	#[inline]
	fn push_trait(&mut self, item: TraitDef) -> TraitIndex {
		let index = TraitIndex::new(u32::try_from(self.traits.len()).unwrap());
		self.traits.push(item);
		index
	}

	#[inline]
	fn push_trait_impl(&mut self, item: TraitImplDef) -> TraitImplIndex {
		let index =
			TraitImplIndex::new(u32::try_from(self.trait_impls.len()).unwrap());
		self.trait_impls.push(item);
		index
	}

	#[inline]
	fn push_typeset(&mut self, item: TypeSetDef) -> TypeSetIndex {
		let index =
			TypeSetIndex::new(u32::try_from(self.typesets.len()).unwrap());
		self.typesets.push(item);
		index
	}

	#[inline]
	fn push_function(&mut self, item: FunctionDef) -> FunctionIndex {
		let index =
			FunctionIndex::new(u32::try_from(self.functions.len()).unwrap());
		self.functions.push(item);
		index
	}

	#[inline]
	fn push_inherent_impl(
		&mut self,
		item: InherentImplDef,
	) -> InherentImplIndex {
		let index = InherentImplIndex::new(
			u32::try_from(self.inherent_impls.len()).unwrap(),
		);
		self.inherent_impls.push(item);
		index
	}

	fn push_use_path(&mut self, segment: UsePathSegment) -> UsePathIndex {
		let index =
			UsePathIndex::new(u32::try_from(self.use_paths.len()).unwrap());
		self.use_paths.push(segment);
		index
	}

	fn push_use_item(&mut self, item: UseItemDef) -> UseItemIndex {
		let index =
			UseItemIndex::new(u32::try_from(self.use_items.len()).unwrap());
		self.use_items.push(item);
		index
	}

	fn push_def(
		&mut self,
		namespace_idx: NamespaceIndex,
		definition: ItemDef,
	) -> DefKey {
		let symbol_idx = LocalDefIndex::new(
			u32::try_from(
				self.namespaces[usize::from(namespace_idx)].items.len(),
			)
			.unwrap(),
		);
		self.namespaces[usize::from(namespace_idx)]
			.items
			.push(definition);
		DefKey::new(namespace_idx, symbol_idx)
	}

	fn insert_binding(
		&mut self,
		namespace_idx: NamespaceIndex,
		key: BindingKey,
		binding: Binding,
		span: TextSpan,
	) {
		if let Err(collision_key) =
			self.namespaces
				.try_insert_binding(namespace_idx, key, binding)
		{
			self.diagnostics.push(
				DuplicateDefinitionDiagnostic {
					strings: self.strings,
					key,
					definitions: (
						collision_key.source_span(&self.namespaces),
						SourceSpan::new(
							self.namespaces[usize::from(namespace_idx)].file_id,
							span,
						),
					),
				}
				.report(),
			);
		}
	}

	fn declare_child_namespace(
		&mut self,
		parent_namespace: NamespaceIndex,
		file_id: FileId,
		name: SymbolU32,
		kind: NamespaceKind,
		content_span: TextSpan,
		visibility: Visibility,
	) -> Declared<NamespaceIndex> {
		let namespace_idx = NamespaceIndex::new(
			u32::try_from(self.namespaces.len())
				.expect("namespace graph exceeded u32 index capacity"),
		);
		let package_id =
			self.namespaces[usize::from(parent_namespace)].package_id;
		// Only `Module`/`Import` are ever declared through this helper —
		// `Package` roots are built directly (they have no parent to
		// declare them from) and `Enum`'s variant namespace is built by its
		// own prescan arm (it needs neither the `self`/`crate`/`super`
		// bindings below nor a name claimed in `parent_namespace`).
		let def_kind = match kind {
			NamespaceKind::Module(_) => DefKind::Module(namespace_idx),
			NamespaceKind::Import(_) => DefKind::Import(namespace_idx),
			NamespaceKind::Package(_) | NamespaceKind::Enum(_) => {
				unreachable!("only Module/Import namespaces are declared here")
			}
		};
		let mut namespace = Namespace {
			parent: Some(parent_namespace),
			file_id,
			package_id,
			kind,
			bindings: HashMap::new(),
			items: vec![ItemDef::new(def_kind, content_span)],
			glob_imports: Vec::new(),
		};
		namespace.bindings.insert(
			BindingKey::ty(name),
			Binding::definition(
				DefKey::new(namespace_idx, LocalDefIndex::SELF),
				Visibility::Public,
			),
		);
		namespace.bindings.insert(
			BindingKey::ty(ast::Keyword::SelfLower.symbol()),
			Binding::definition(
				DefKey::new(namespace_idx, LocalDefIndex::SELF),
				Visibility::Public,
			),
		);

		let crate_root_namespace =
			self.package_namespaces[package_id.as_usize()];
		namespace.bindings.insert(
			BindingKey::ty(ast::Keyword::Crate.symbol()),
			Binding::definition(
				DefKey::new(crate_root_namespace, LocalDefIndex::SELF),
				Visibility::Public,
			),
		);
		namespace.bindings.insert(
			BindingKey::ty(ast::Keyword::Super.symbol()),
			Binding::definition(
				DefKey::new(parent_namespace, LocalDefIndex::SELF),
				Visibility::Public,
			),
		);
		self.namespaces.push(namespace);
		match self.namespaces.try_insert_binding(
			parent_namespace,
			BindingKey::ty(name),
			Binding::definition(
				DefKey::new(namespace_idx, LocalDefIndex::SELF),
				visibility,
			),
		) {
			Err(collision) => {
				Declared::with_collision(namespace_idx, collision)
			}
			Ok(()) => Declared::new(namespace_idx),
		}
	}

	fn push_module_declaration(
		&mut self,
		decl: ModuleDeclaration,
	) -> ModuleDeclIndex {
		let index = ModuleDeclIndex::new(
			u32::try_from(self.module_decls.len()).unwrap(),
		);
		self.module_decls.push(decl);
		index
	}

	fn push_import_declaration(
		&mut self,
		decl: ImportDeclaration,
	) -> ImportDeclIndex {
		let index = ImportDeclIndex::new(
			u32::try_from(self.import_decls.len()).unwrap(),
		);
		self.import_decls.push(decl);
		index
	}
}

impl<'ast, 'ctx> DefinitionRegistryBuilder<'ast, 'ctx> {
	pub(super) fn scan_item(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		item: &'ast ast::Item,
	) {
		match item {
			ast::Item::Function {
				id,
				signature,
				pub_span,
				..
			}
			| ast::Item::FunctionDeclaration {
				id,
				signature,
				pub_span,
				..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Function(*id), signature.name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::value(signature.name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					signature.name.span,
				);

				// `self` has no meaning in a free function — no `Self` to
				// bind it to — so every occurrence is a position error,
				// same diagnostic as one in the wrong spot within a
				// method's own list (`validate_method_params`).
				let mut params: Vec<Spanned<SymbolU32>> =
					Vec::with_capacity(signature.params.len());
				for param in signature.params.iter() {
					let p = &param.inner.inner;
					let name = p.name;

					if let Some(&first) =
						params.iter().find(|s| s.inner == name.inner)
					{
						self.diagnostics.push(
							report_duplicate_function_parameter(
								self.strings,
								file_id,
								name,
								first,
							),
						);
					}

					if name.inner == Keyword::SelfLower.symbol() {
						self.diagnostics.push(report_self_param_position(
							file_id, name.span,
						));
					} else if p.ty.is_none() {
						self.diagnostics.push(report_missing_parameter_type(
							self.strings,
							file_id,
							name,
						));
					}

					params.push(name);
				}
				let function_index = self.push_function(FunctionDef {
					def_id: *id,
					file_id,
					namespace,
					name: signature.name,
					params: params.into_boxed_slice(),
				});

				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Function {
						item,
						function_index,
					},
				});
			}
			ast::Item::Global {
				id, pub_span, name, ..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Global(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::value(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Global { item },
				});
			}
			ast::Item::RecordStruct {
				id,
				pub_span,
				name,
				fields,
				..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Struct(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);

				// Every written field gets a real `FieldIndex` and keeps its
				// storage slot — including a duplicate name, which is only
				// unreachable by name (`lookup` keeps the first occurrence),
				// not dropped: dropping it would shift every later field's
				// index and hide its type from the recursion check below.
				let mut record_fields: Vec<RecordFieldDef> =
					Vec::with_capacity(fields.len());
				let mut lookup: HashMap<SymbolU32, FieldIndex> =
					HashMap::with_capacity(fields.len());
				for f in fields.iter() {
					let field = &f.inner.inner;
					let index = FieldIndex::new(
						u32::try_from(record_fields.len()).unwrap(),
					);
					if let Some(&first_index) = lookup.get(&field.name.inner) {
						let first_name =
							record_fields[usize::from(first_index)].name;
						self.diagnostics.push(report_duplicate_struct_field(
							self.strings,
							file_id,
							field.name,
							first_name,
						));
					} else {
						lookup.insert(field.name.inner, index);
					}
					record_fields.push(RecordFieldDef {
						name: field.name,
						pub_span: field.pub_span,
					});
				}
				let struct_index = StructIndex::new(
					u32::try_from(self.structs.len()).unwrap(),
				);
				self.structs.push(StructDef {
					def_id: *id,
					file_id,
					namespace,
					fields: StructFields::Record {
						fields: record_fields.into_boxed_slice(),
						lookup,
					},
				});

				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::RecordStruct { struct_index, item },
				});
			}
			ast::Item::TupleStruct {
				id,
				pub_span,
				name,
				fields,
				..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Struct(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				// The type itself is always nameable if `pub`, but a field
				// that isn't `pub` can't be initialized from outside this
				// namespace — so the constructor (the value binding) is
				// only ever `Accessible` when every field is. This is
				// purely syntactic (each field's own `pub_span`), so it's
				// known here in prescan without needing any type resolved.
				let all_fields_pub =
					fields.iter().all(|f| f.inner.inner.pub_span.is_some());
				let value_target = if all_fields_pub {
					BindingTarget::Accessible(def_key)
				} else {
					BindingTarget::Inaccessible(def_key)
				};
				self.insert_binding(
					namespace,
					BindingKey::value(name.inner),
					Binding::definition_with_target(
						value_target,
						Visibility::from(*pub_span),
					),
					name.span,
				);

				let struct_index = StructIndex::new(
					u32::try_from(self.structs.len()).unwrap(),
				);
				self.structs.push(StructDef {
					def_id: *id,
					file_id,
					namespace,
					fields: StructFields::Tuple {
						fields: fields
							.iter()
							.map(|f| TupleFieldDef {
								pub_span: f.inner.inner.pub_span,
							})
							.collect(),
					},
				});

				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::TupleStruct { struct_index, item },
				});
			}
			ast::Item::Enum {
				id,
				pub_span,
				name,
				variants,
				..
			} => {
				let enum_index =
					EnumIndex::new(u32::try_from(self.enums.len()).unwrap());
				let variants_namespace = NamespaceIndex::new(
					u32::try_from(self.namespaces.len()).unwrap(),
				);
				let package_id =
					self.namespaces[usize::from(namespace)].package_id;
				self.namespaces.push(Namespace {
					parent: Some(namespace),
					file_id,
					package_id,
					kind: NamespaceKind::Enum(enum_index),
					bindings: HashMap::new(),
					items: Vec::new(),
					glob_imports: Vec::new(),
				});
				self.enums.push(EnumDef {
					def_id: *id,
					file_id,
					namespace,
					variants_namespace,
				});

				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Enum(variants_namespace), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);

				for v in variants.iter() {
					let variant = &v.inner.inner;
					let variant_key = self.push_def(
						variants_namespace,
						ItemDef::new(
							DefKind::EnumVariant(variant.id),
							variant.name.span,
						),
					);
					self.insert_binding(
						variants_namespace,
						BindingKey::value(variant.name.inner),
						Binding::definition(variant_key, Visibility::Public),
						variant.name.span,
					);
				}

				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Enum { enum_index, item },
				});
			}
			ast::Item::TypeAlias {
				id,
				pub_span,
				name,
				body,
				..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::TypeAlias(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				if body.is_none()
					&& self.namespaces[usize::from(namespace)].package_id
						== self.stdlib_package
				{
					if let Some(name_str) = self.strings.resolve(name.inner) {
						if let Some(slot) =
							self.intrinsics.type_slot_mut(name_str)
						{
							*slot = Some(def_key);
						}
					}
				}
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::TypeAlias { item },
				});
			}
			ast::Item::Memory { id, name, .. } => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Memory(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::Private),
					name.span,
				);
				self.insert_binding(
					namespace,
					BindingKey::value(name.inner),
					Binding::definition(def_key, Visibility::Private),
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Memory { item },
				});
			}
			ast::Item::Const {
				id, pub_span, name, ..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Const(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::value(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Constant { item },
				});
			}
			ast::Item::Module {
				name,
				items,
				pub_span,
			} => {
				let namespace_idx = NamespaceIndex(
					u32::try_from(self.namespaces.len()).unwrap(),
				);
				let module_declaration_idx =
					self.push_module_declaration(ModuleDeclaration {
						namespace_idx,
						declaration_file_id: file_id,
						content_file_id: None,
						name: *name,
						pub_span: *pub_span,
					});
				debug_assert_eq!(
					namespace_idx,
					self.declare_child_namespace(
						namespace,
						file_id,
						name.inner,
						NamespaceKind::Module(module_declaration_idx),
						items.span,
						Visibility::from(*pub_span),
					)
					.report_with(|collision_key| {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key: BindingKey::ty(name.inner),
								definitions: (
									collision_key.source_span(&self.namespaces),
									SourceSpan::new(file_id, name.span),
								),
							}
							.report(),
						)
					})
				);

				for item in items.inner.iter() {
					self.scan_item(file_id, namespace_idx, &item.inner.inner);
				}
			}
			// Nothing to do: Phase 1a already created this module's
			// namespace (and set its `pub_span`) directly from vfs's
			// `SourceModule` tree, before any file's items were scanned.
			ast::Item::ModuleDeclaration { .. } => {}
			ast::Item::Trait {
				id,
				name,
				items,
				pub_span,
				..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Trait(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				if self.namespaces[usize::from(namespace)].package_id
					== self.stdlib_package
				{
					if let Some(name_str) = self.strings.resolve(name.inner) {
						if let Some(slot) =
							self.intrinsics.trait_slot_mut(name_str)
						{
							*slot = Some(def_key);
						}
					}
				}
				let trait_index =
					TraitIndex(u32::try_from(self.traits.len()).unwrap());
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Trait { trait_index, item },
				});

				let mut members: Vec<TraitMemberDef> = Vec::new();
				let mut bindings: HashMap<BindingKey, MemberIndex> =
					HashMap::new();
				for item in items.iter() {
					let member_index =
						MemberIndex::new(u32::try_from(members.len()).unwrap());
					let (member, key) = match &item.inner.inner {
						ast::TraitItem::Function { signature, id, .. } => {
							let params = self
								.scan_method_params(file_id, &signature.params);
							let is_method = params.first().is_some_and(|p| {
								p.inner == Keyword::SelfLower.symbol()
							});
							let function_index =
								self.push_function(FunctionDef {
									def_id: *id,
									file_id,
									namespace,
									name: signature.name,
									params,
								});
							self.ast_nodes.push(AstEntry {
								def_id: *id,
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
										MemberKind::Method(*id)
									} else {
										MemberKind::Function(*id)
									},
									accesses: Vec::new(),
									span: signature.name.span,
								},
								BindingKey::value(signature.name.inner),
							)
						}
						ast::TraitItem::Const { name, id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitConst {
									trait_index,
									item: &item.inner.inner,
								},
							});
							(
								TraitMemberDef {
									kind: MemberKind::Constant(*id),
									accesses: Vec::new(),
									span: name.span,
								},
								BindingKey::value(name.inner),
							)
						}
						ast::TraitItem::AssociatedType { name, id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitAssocType {
									trait_index,
									item: &item.inner.inner,
								},
							});
							(
								TraitMemberDef {
									kind: MemberKind::AssociatedType(*id),
									accesses: Vec::new(),
									span: name.span,
								},
								BindingKey::ty(name.inner),
							)
						}
					};
					if let Some(collision) = bindings.get(&key).copied() {
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
					}
					members.push(member);
				}

				debug_assert_eq!(
					trait_index,
					self.push_trait(TraitDef {
						def_id: *id,
						file_id,
						namespace,
						pub_span: *pub_span,
						name: *name,
						bindings,
						members,
					})
				);
			}
			ast::Item::InherentImpl {
				id: impl_id, items, ..
			} => {
				let mut members: Vec<InherentMemberDef> = Vec::new();
				let mut bindings: HashMap<BindingKey, MemberIndex> =
					HashMap::new();
				let block_index = InherentImplIndex(
					u32::try_from(self.inherent_impls.len()).unwrap(),
				);
				self.ast_nodes.push(AstEntry {
					def_id: *impl_id,
					file_id,
					namespace,
					node: AstNodeRef::InherentImplBlock { item, block_index },
				});
				for impl_item in items.iter() {
					let member_index =
						MemberIndex::new(u32::try_from(members.len()).unwrap());
					let (member, key, binding) = match &impl_item.inner.inner {
						ast::ImplItem::Function {
							id,
							signature,
							pub_span,
							..
						} => {
							let params = self
								.scan_method_params(file_id, &signature.params);
							let is_method = params.first().is_some_and(|p| {
								p.inner == Keyword::SelfLower.symbol()
							});
							let function_index =
								self.push_function(FunctionDef {
									def_id: *id,
									file_id,
									namespace,
									name: signature.name,
									params,
								});
							self.ast_nodes.push(AstEntry {
								def_id: *id,
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
									accesses: Vec::new(),
									kind: if is_method {
										MemberKind::Method(*id)
									} else {
										MemberKind::Function(*id)
									},
									visibility: Visibility::from(*pub_span),
									span: signature.name.span,
								},
								BindingKey::value(signature.name.inner),
								member_index,
							)
						}
						ast::ImplItem::Constant {
							id, name, pub_span, ..
						} => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::InherentImplConst {
									item: &impl_item.inner.inner,
									block_index,
								},
							});
							(
								InherentMemberDef {
									accesses: Vec::new(),
									kind: MemberKind::Constant(*id),
									visibility: Visibility::from(*pub_span),
									span: name.span,
								},
								BindingKey::value(name.inner),
								member_index,
							)
						}
						ast::ImplItem::AssocType { .. } => {
							todo!()
						}
					};
					if let Some(collision) = bindings.get(&key).copied() {
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
					}
					members.push(member);
				}

				debug_assert_eq!(
					block_index,
					self.push_inherent_impl(InherentImplDef {
						def_id: *impl_id,
						file_id,
						namespace,
						members,
						bindings,
					})
				);
			}
			ast::Item::Import {
				internal_name,
				external_name,
				items,
			} => {
				let external_name = {
					let unquoted =
						unescape_string_literal(external_name.extract_str(
							&self.files.get(file_id).unwrap().source,
						));
					Spanned {
						inner: self.strings.get_or_intern(&unquoted),
						span: *external_name,
					}
				};
				let internal_name = *internal_name;

				let namespace_idx = NamespaceIndex(
					u32::try_from(self.namespaces.len()).unwrap(),
				);
				let import_declaration_idx =
					self.push_import_declaration(ImportDeclaration {
						external_name,
						internal_name,
						namespace_idx,
					});
				debug_assert_eq!(
					namespace_idx,
					self.declare_child_namespace(
						namespace,
						file_id,
						internal_name.inner,
						NamespaceKind::Import(import_declaration_idx),
						items.span,
						Visibility::Public,
					)
					.report_with(|collision| {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key: BindingKey::ty(internal_name.inner),
								definitions: (
									collision.source_span(&self.namespaces),
									SourceSpan::new(
										file_id,
										internal_name.span,
									),
								),
							}
							.report(),
						)
					})
				);

				for item in items.inner.iter() {
					match &item.inner.inner.declaration {
						ast::ImportDeclaration::Memory { id, name, .. } => {
							let def_key = self.push_def(
								namespace_idx,
								ItemDef::new(DefKind::Memory(*id), name.span),
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::ty(name.inner),
								Binding::definition(
									def_key,
									Visibility::Public,
								),
								name.span,
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::value(name.inner),
								Binding::definition(
									def_key,
									Visibility::Public,
								),
								name.span,
							);
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::ImportedMemory {
									import_module_index: import_declaration_idx,
									decl: &item.inner.inner.declaration,
								},
							});
						}
						ast::ImportDeclaration::Function { id, signature } => {
							let def_key = self.push_def(
								namespace_idx,
								ItemDef::new(
									DefKind::Memory(*id),
									signature.name.span,
								),
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::value(signature.name.inner),
								Binding::definition(
									def_key,
									Visibility::Public,
								),
								signature.name.span,
							);
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::ImportedFunction {
									import_module_index: import_declaration_idx,
									decl: &item.inner.inner.declaration,
								},
							});
						}
						ast::ImportDeclaration::Global { id, name, .. } => {
							let def_key = self.push_def(
								namespace_idx,
								ItemDef::new(DefKind::Memory(*id), name.span),
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::value(name.inner),
								Binding::definition(
									def_key,
									Visibility::Public,
								),
								name.span,
							);
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::ImportedGlobal {
									import_module_index: import_declaration_idx,
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
			ast::Item::Export { id, .. } => {
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Export { item },
				});
			}
			ast::Item::TypeSet {
				id,
				name,
				pub_span,
				members,
				..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::TypeSet(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);

				// See `TypeSetDef`'s doc comment for why the backing trait
				// and every member impl below reuse this typeset's own
				// `def_id` rather than minting fresh ones.
				let trait_index = self.push_trait(TraitDef {
					def_id: *id,
					file_id,
					namespace,
					pub_span: None,
					name: *name,
					bindings: HashMap::new(),
					members: Vec::new(),
				});
				let member_impls: Box<[TraitImplIndex]> = members
					.iter()
					.map(|_| {
						self.push_trait_impl(TraitImplDef {
							def_id: *id,
							file_id,
							namespace,
							members: Vec::new(),
							bindings: HashMap::new(),
						})
					})
					.collect();
				let typeset_index = self.push_typeset(TypeSetDef {
					def_id: *id,
					file_id,
					namespace,
					trait_index,
					member_impls,
				});

				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::TypeSet {
						typeset_index,
						item,
					},
				});
			}
			ast::Item::TraitImpl {
				id: impl_id, items, ..
			} => {
				let mut members: Vec<TraitMemberDef> = Vec::new();
				let mut bindings: HashMap<BindingKey, MemberIndex> =
					HashMap::new();
				let block_index = TraitImplIndex(
					u32::try_from(self.trait_impls.len()).unwrap(),
				);
				self.ast_nodes.push(AstEntry {
					def_id: *impl_id,
					file_id,
					namespace,
					node: AstNodeRef::TraitImplBlock { item, block_index },
				});
				for item in items.iter() {
					let member_index =
						MemberIndex::new(u32::try_from(members.len()).unwrap());
					let (member, key) = match &item.inner.inner {
						ast::ImplItem::Function { id, signature, .. } => {
							let params = self
								.scan_method_params(file_id, &signature.params);
							let is_method = params.first().is_some_and(|p| {
								p.inner == Keyword::SelfLower.symbol()
							});
							let function_index =
								self.push_function(FunctionDef {
									def_id: *id,
									file_id,
									namespace,
									name: signature.name,
									params,
								});
							self.ast_nodes.push(AstEntry {
								def_id: *id,
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
									accesses: Vec::new(),
									kind: if is_method {
										MemberKind::Method(*id)
									} else {
										MemberKind::Function(*id)
									},
									span: signature.name.span,
								},
								BindingKey::value(signature.name.inner),
							)
						}
						ast::ImplItem::Constant { id, name, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitImplConstant {
									item: &item.inner.inner,
									block_index,
								},
							});
							(
								TraitMemberDef {
									accesses: Vec::new(),
									kind: MemberKind::Constant(*id),
									span: name.span,
								},
								BindingKey::value(name.inner),
							)
						}
						ast::ImplItem::AssocType { id, name, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitImplAssocType {
									item: &item.inner.inner,
									block_index,
								},
							});
							(
								TraitMemberDef {
									accesses: Vec::new(),
									kind: MemberKind::AssociatedType(*id),
									span: name.span,
								},
								BindingKey::ty(name.inner),
							)
						}
					};

					if let Some(collision) = bindings.get(&key).copied() {
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
					}
					members.push(member);
				}

				debug_assert_eq!(
					block_index,
					self.push_trait_impl(TraitImplDef {
						def_id: *impl_id,
						file_id,
						namespace,
						bindings,
						members,
					})
				);
			}
		}
	}

	fn scan_use_tree(
		&mut self,
		namespace: NamespaceIndex,
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

	/// Validates a trait/impl method's parameter list: every name unique,
	/// `self` (if present) only as the very first parameter, every other
	/// parameter explicitly typed. Whether `self` is actually present —
	/// i.e. whether this member is `MemberKind::Method` or
	/// `MemberKind::Function` — is for the caller to read straight off
	/// `params.first()` against `Keyword::SelfLower.symbol()`, same
	/// constant-time check this uses; nothing here needs to hand that
	/// fact back out.
	fn scan_method_params(
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
			if is_self {
				if index != 0 {
					self.diagnostics
						.push(report_self_param_position(file_id, name.span));
				}
			} else if p.ty.is_none() {
				self.diagnostics.push(report_missing_parameter_type(
					self.strings,
					file_id,
					name,
				));
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

fn report_missing_parameter_type(
	strings: &StringInterner,
	file_id: FileId,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingParameterType.code())
		.with_message(format!(
			"parameter `{name_str}` requires an explicit type"
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("expected `: Type` here"),
		)
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

	impl TestCase {
		fn from_graph(mut graph: vfs::CompilationUnit) -> Self {
			let mut diagnostics = Vec::new();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				graph.stdlib_package,
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

		fn root_namespace(&self) -> NamespaceIndex {
			self.defs.package_namespaces[self.graph.root_package.as_usize()]
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new("prescan", &self.diagnostics, &self.graph.files)
		}

		/// Resolves `path` (`::`-separated) from the root namespace in
		/// binding tier `ns`, via the real `PathResolver` — the same
		/// mechanism production code uses, so a test asking for `"a::Foo"`
		/// gets whatever namespacing/shadowing rules would actually pick,
		/// not just *an* item with that spelling somewhere. Mirrors
		/// `signatures.rs`'s own `TestCase::resolve`.
		fn resolve(&self, ns: BindingNamespace, path: &str) -> DefKind {
			let root = self.root_namespace();
			let file_id = self.defs.namespaces[usize::from(root)].file_id;
			let stdlib_root = self.defs.package_namespaces
				[self.graph.stdlib_package.as_usize()];

			let segments: Box<[ast::PathSegment]> = path
				.split("::")
				.map(|segment| ast::PathSegment {
					ident: Spanned {
						inner: self
							.graph
							.strings
							.get(segment)
							.expect("already interned from source"),
						span: TextSpan::new(0, 0),
					},
					type_args: Box::new([]),
				})
				.collect();
			let mut scratch = Vec::new();
			let target = PathResolver::new(
				&self.defs.namespaces,
				&self.defs.use_items,
				stdlib_root,
			)
			.resolve_path(
				&mut scratch,
				&self.graph.strings,
				file_id,
				root,
				&segments,
				ns,
			);
			let def_key = target.def_key().unwrap_or_else(|| {
				panic!("expected `{path}` to resolve: {scratch:?}")
			});
			def_key.symbol_kind(&self.defs)
		}

		fn lookup_type(
			&mut self,
			namespace: NamespaceIndex,
			name: &str,
		) -> Option<BindingTarget> {
			let symbol = self.graph.strings.get_or_intern(name);
			self.defs.namespaces[usize::from(namespace)]
				.bindings
				.get(&BindingKey::ty(symbol))
				.map(|binding| binding.target)
		}

		fn lookup_value(
			&mut self,
			namespace: NamespaceIndex,
			name: &str,
		) -> Option<BindingTarget> {
			let symbol = self.graph.strings.get_or_intern(name);
			self.defs.namespaces[usize::from(namespace)]
				.bindings
				.get(&BindingKey::value(symbol))
				.map(|binding| binding.target)
		}

		/// `resolve`'s `DefKind::Function` case, followed to its own
		/// `FunctionDef` entry.
		fn function_def(&self, name: &str) -> &FunctionDef {
			let DefKind::Function(def_id) =
				self.resolve(BindingNamespace::Value, name)
			else {
				panic!("expected `{name}` to be a function");
			};
			self.defs
				.functions
				.iter()
				.find(|f| f.def_id == def_id)
				.unwrap_or_else(|| {
					panic!("`{name}` should have its own FunctionDef entry")
				})
		}

		/// Follows a bound name to the namespace it names — e.g. the
		/// namespace a `mod inner { ... }` or `mod inner;` declares.
		fn child_namespace(
			&mut self,
			namespace: NamespaceIndex,
			name: &str,
		) -> NamespaceIndex {
			let target = self
				.lookup_type(namespace, name)
				.unwrap_or_else(|| panic!("`{name}` should be bound"));
			let BindingTarget::Accessible(def_key) = target else {
				panic!("`{name}` should be accessible here");
			};
			let kind = self.defs.namespaces[usize::from(def_key.namespace_idx)]
				.items[usize::from(def_key.def_idx)]
			.kind;
			kind.as_namespace().unwrap_or_else(|| {
				panic!("`{name}` is not a namespace: {kind:?}")
			})
		}
	}

	#[test]
	fn stdlib_declares_every_primitive() {
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
			type never;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let intrinsics = &case.defs.intrinsics;
		assert!(intrinsics.u8.is_some(), "u8 should be found");
		assert!(intrinsics.i8.is_some(), "i8 should be found");
		assert!(intrinsics.u16.is_some(), "u16 should be found");
		assert!(intrinsics.i16.is_some(), "i16 should be found");
		assert!(intrinsics.u32.is_some(), "u32 should be found");
		assert!(intrinsics.i32.is_some(), "i32 should be found");
		assert!(intrinsics.u64.is_some(), "u64 should be found");
		assert!(intrinsics.i64.is_some(), "i64 should be found");
		assert!(intrinsics.f32.is_some(), "f32 should be found");
		assert!(intrinsics.f64.is_some(), "f64 should be found");
		assert!(intrinsics.bool.is_some(), "bool should be found");
		assert!(intrinsics.char.is_some(), "char should be found");
		assert!(intrinsics.never.is_some(), "never should be found");
	}

	#[test]
	fn stdlib_declares_every_operator_trait() {
		let case = TestCase::new_stdlib(indoc! {"
			trait Add { fn add(self, rhs: Self) -> Self; }
			trait Sub { fn sub(self, rhs: Self) -> Self; }
			trait Mul { fn mul(self, rhs: Self) -> Self; }
			trait Div { fn div(self, rhs: Self) -> Self; }
			trait Rem { fn rem(self, rhs: Self) -> Self; }
			trait Neg { fn neg(self) -> Self; }
			trait BitAnd { fn bitand(self, rhs: Self) -> Self; }
			trait BitOr { fn bitor(self, rhs: Self) -> Self; }
			trait BitXor { fn bitxor(self, rhs: Self) -> Self; }
			trait Shl { fn shl(self, rhs: Self) -> Self; }
			trait Shr { fn shr(self, rhs: Self) -> Self; }
			trait BitNot { fn bitnot(self) -> Self; }
			trait Not { fn not(self) -> Self; }
			trait PartialEq { fn eq(self, other: Self) -> bool; }
			trait PartialOrd { fn lt(self, other: Self) -> bool; }
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let intrinsics = &case.defs.intrinsics;
		assert!(intrinsics.add.is_some(), "Add should be found");
		assert!(intrinsics.sub.is_some(), "Sub should be found");
		assert!(intrinsics.mul.is_some(), "Mul should be found");
		assert!(intrinsics.div.is_some(), "Div should be found");
		assert!(intrinsics.rem.is_some(), "Rem should be found");
		assert!(intrinsics.neg.is_some(), "Neg should be found");
		assert!(intrinsics.bitand.is_some(), "BitAnd should be found");
		assert!(intrinsics.bitor.is_some(), "BitOr should be found");
		assert!(intrinsics.bitxor.is_some(), "BitXor should be found");
		assert!(intrinsics.shl.is_some(), "Shl should be found");
		assert!(intrinsics.shr.is_some(), "Shr should be found");
		assert!(intrinsics.bitnot.is_some(), "BitNot should be found");
		assert!(intrinsics.not.is_some(), "Not should be found");
		assert!(intrinsics.partial_eq.is_some(), "PartialEq should be found");
		assert!(
			intrinsics.partial_ord.is_some(),
			"PartialOrd should be found"
		);
	}

	#[test]
	fn stdlib_missing_an_intrinsic_leaves_its_slot_empty() {
		let case = TestCase::new_stdlib(indoc! {"
			type u8;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert!(case.defs.intrinsics.u8.is_some());
		assert!(case.defs.intrinsics.char.is_none());
		assert!(case.defs.intrinsics.add.is_none());
	}

	#[test]
	fn reserved_name_outside_stdlib_is_not_recorded_as_intrinsic() {
		let case = TestCase::new(indoc! {"
			type u8;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		// The real stdlib's own `u8` must still be the one on record — the
		// same-named declaration in the binary package must not clobber it,
		// and (since it isn't in the stdlib package) must not be recorded
		// as an intrinsic at all.
		let root_namespace = case.root_namespace();
		let stdlib_namespace =
			case.defs.package_namespaces[case.graph.stdlib_package.as_usize()];
		assert_ne!(
			root_namespace, stdlib_namespace,
			"the binary package must not be the stdlib package"
		);
		let u8_key = case.defs.intrinsics.u8.expect("u8 should still resolve");
		assert_eq!(
			u8_key.namespace_idx, stdlib_namespace,
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
			trait u8 { fn f(self) -> Self; }
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
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
	fn function_and_struct_get_bindings() {
		let mut case = TestCase::new(indoc! {"
			pub fn add(a: i32, b: i32) -> i32 { a + b }
			struct Point { x: i32, y: i32 }
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let add_symbol = case.graph.strings.get_or_intern("add");
		let point_symbol = case.graph.strings.get_or_intern("Point");
		let root_namespace = case.root_namespace();
		let bindings =
			&case.defs.namespaces[usize::from(root_namespace)].bindings;

		let add_binding = bindings
			.get(&BindingKey::value(add_symbol))
			.expect("`add` should be bound in the value namespace");
		assert!(matches!(add_binding.target, BindingTarget::Accessible(_)));

		let point_binding = bindings
			.get(&BindingKey::ty(point_symbol))
			.expect("`Point` should be bound in the type namespace");
		assert!(matches!(point_binding.target, BindingTarget::Accessible(_)));
	}

	#[test]
	fn tuple_struct_with_all_pub_fields_has_an_accessible_constructor() {
		let mut case = TestCase::new(indoc! {"
			pub struct Point(pub i32, pub i32);
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let point_symbol = case.graph.strings.get_or_intern("Point");
		let root_namespace = case.root_namespace();
		let bindings =
			&case.defs.namespaces[usize::from(root_namespace)].bindings;

		let value_binding = bindings
			.get(&BindingKey::value(point_symbol))
			.expect("`Point` should be bound in the value namespace");
		assert!(matches!(value_binding.target, BindingTarget::Accessible(_)));
	}

	#[test]
	fn tuple_struct_with_a_private_field_has_an_inaccessible_constructor() {
		let mut case = TestCase::new(indoc! {"
			pub struct Point(pub i32, i32);
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let point_symbol = case.graph.strings.get_or_intern("Point");
		let root_namespace = case.root_namespace();
		let bindings =
			&case.defs.namespaces[usize::from(root_namespace)].bindings;

		// The type itself stays fully nameable...
		let type_binding = bindings
			.get(&BindingKey::ty(point_symbol))
			.expect("`Point` should be bound in the type namespace");
		assert!(matches!(type_binding.target, BindingTarget::Accessible(_)));

		// ...but the constructor can't be, since a private field can't be
		// initialized from outside this namespace.
		let value_binding = bindings
			.get(&BindingKey::value(point_symbol))
			.expect("`Point` should be bound in the value namespace");
		assert!(matches!(
			value_binding.target,
			BindingTarget::Inaccessible(_)
		));
	}

	#[test]
	fn duplicate_record_field_is_reported_but_keeps_its_own_slot() {
		let mut case = TestCase::new(indoc! {"
			struct Point { x: i32, x: i32 }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateStructField.code())
		);

		// `Point` isn't necessarily `defs.structs[0]` — the real stdlib
		// (loaded by `TestCase::new`) declares its own structs (`Layout`,
		// `RawPtr`), so look it up by name rather than assuming an index.
		let DefKind::Struct(point_def_id) =
			case.resolve(BindingNamespace::Type, "Point")
		else {
			panic!("expected `Point` to be a struct")
		};
		let struct_def = case
			.defs
			.structs
			.iter()
			.find(|s| s.def_id == point_def_id)
			.expect("Point should have its own StructDef entry");

		let StructFields::Record { fields, lookup } = &struct_def.fields else {
			panic!("expected a record struct");
		};
		// Both occurrences keep a real field slot — duplicate name isn't
		// dropped, only unreachable by name — so a later field's index
		// still matches its declaration position.
		assert_eq!(fields.len(), 2);
		assert_eq!(fields[0].name.inner, fields[1].name.inner);
		// `lookup` only ever points at the first occurrence.
		assert_eq!(
			lookup.get(&fields[1].name.inner),
			Some(&FieldIndex::new(0))
		);
	}

	#[test]
	fn duplicate_function_parameter_is_reported_but_keeps_its_own_slot() {
		let case = TestCase::new(indoc! {"
			fn f(x: i32, x: i32) {}
		"});

		case.diagnostics()
			.assert_error(DiagnosticCode::DuplicateFunctionParameter);

		// Positional, same as a duplicate struct field — the second `x`
		// still gets its own slot rather than being dropped.
		let params = &case.function_def("f").params;
		assert_eq!(params.len(), 2);
		assert_eq!(params[0].inner, params[1].inner);
	}

	#[test]
	fn self_in_a_free_function_is_rejected() {
		let case = TestCase::new(indoc! {"
			fn f(self) {}
		"});

		case.diagnostics().assert_error(DiagnosticCode::SelfParamPosition);
	}

	#[test]
	fn self_not_first_in_a_method_is_rejected() {
		let case = TestCase::new(indoc! {"
			trait T {
				fn f(x: i32, self);
			}
		"});

		case.diagnostics().assert_error(DiagnosticCode::SelfParamPosition);
	}

	#[test]
	fn missing_parameter_type_is_reported() {
		let case = TestCase::new(indoc! {"
			fn f(x) {}
		"});

		case.diagnostics().assert_error(DiagnosticCode::MissingParameterType);
	}

	#[test]
	fn self_as_the_first_method_parameter_is_accepted_and_classified() {
		let mut case = TestCase::new(indoc! {"
			trait T {
				fn f(self);
			}
		"});

		case.diagnostics().assert_no_errors();

		let DefKind::Trait(trait_def_id) =
			case.resolve(BindingNamespace::Type, "T")
		else {
			panic!("expected `T` to be a trait");
		};
		let trait_def = case
			.defs
			.traits
			.iter()
			.find(|t| t.def_id == trait_def_id)
			.expect("T should have its own TraitDef entry");
		let f_symbol = case.graph.strings.get_or_intern("f");
		let &member_index = trait_def
			.bindings
			.get(&BindingKey::value(f_symbol))
			.expect("expected `T` to have a function `f`");
		assert!(matches!(
			trait_def.members[usize::from(member_index)].kind,
			MemberKind::Method(_)
		));
	}

	#[test]
	fn module_declared_in_another_file_gets_a_namespace() {
		let mut case = TestCase::new_workspace(
			vfs::AbsolutePath::new("/main.wx"),
			HashMap::from([
				(vfs::AbsolutePath::new("/main.wx"), "mod math;".to_string()),
				(
					vfs::AbsolutePath::new("/math.wx"),
					"pub fn add() -> i32 { 1 }".to_string(),
				),
			]),
		);
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let math = case.child_namespace(root, "math");
		assert!(matches!(
			case.lookup_value(math, "add"),
			Some(BindingTarget::Accessible(_))
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
				pub fn helper() -> i32 { 1 }
			}
			use a::*;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let helper = case.graph.strings.get_or_intern("helper");

		assert!(matches!(
			case.defs.namespaces.lookup(
				&case.defs.use_items,
				root,
				root,
				BindingKey::value(helper),
			),
			BindingLookup::Found(..)
		));
		assert!(
			case.defs
				.namespaces
				.direct_lookup(root, BindingKey::value(helper))
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
				pub fn helper() -> i32 { 1 }
			}
			mod b {
				use crate::a::*;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let b = case.child_namespace(root, "b");
		let helper = case.graph.strings.get_or_intern("helper");

		assert!(matches!(
			case.defs.namespaces.indirect_lookup(
				&case.defs.use_items,
				root,
				b,
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
				pub fn helper() -> i32 { 1 }
			}
			mod m {
				use crate::a::*;
				mod inner {}
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let m = case.child_namespace(root, "m");
		let inner = case.child_namespace(m, "inner");
		let helper = case.graph.strings.get_or_intern("helper");

		match case.defs.namespaces.indirect_lookup(
			&case.defs.use_items,
			inner,
			m,
			BindingKey::value(helper),
		) {
			BindingLookup::Found(BindingTarget::Accessible(_), _) => {}
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
				pub fn helper() -> i32 { 1 }
			}
			mod hub {
				pub use crate::a::*;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let hub = case.child_namespace(root, "hub");
		let helper = case.graph.strings.get_or_intern("helper");

		let Some(BindingTarget::Accessible(original)) =
			case.lookup_value(a, "helper")
		else {
			panic!("`a::helper` should resolve directly");
		};

		match case.defs.namespaces.indirect_lookup(
			&case.defs.use_items,
			root,
			hub,
			BindingKey::value(helper),
		) {
			BindingLookup::Found(
				BindingTarget::Accessible(found),
				visibility,
			) => {
				assert_eq!(found, original);
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
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				pub fn pick() -> i32 { 2 }
			}
			mod hub {
				pub use crate::a::*;
				pub use crate::b::*;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let hub = case.child_namespace(root, "hub");
		let pick = case.graph.strings.get_or_intern("pick");

		match case.defs.namespaces.indirect_lookup(
			&case.defs.use_items,
			root,
			hub,
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
				pub fn pick() -> i32 { 1 }
			}
			mod hub {
				pub use crate::a::*;
				fn pick() -> i32 { 2 }
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let hub = case.child_namespace(root, "hub");
		let pick = case.graph.strings.get_or_intern("pick");

		let Some(BindingTarget::Accessible(direct)) =
			case.lookup_value(hub, "pick")
		else {
			panic!("`hub::pick` should be bound directly");
		};

		match case.defs.namespaces.lookup(
			&case.defs.use_items,
			root,
			hub,
			BindingKey::value(pick),
		) {
			BindingLookup::Found(BindingTarget::Accessible(found), _) => {
				assert_eq!(
					found, direct,
					"lookup should return hub's own `pick`, not a::pick \
					 through the glob"
				);
			}
			other => {
				panic!("expected the direct binding to win, got {other:?}")
			}
		}
	}
}
