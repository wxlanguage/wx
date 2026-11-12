//! Phase 1 — the prescan. Walks every item in every file, allocates its TIR
//! entry and claims its name, and records it in `ast_nodes` for the
//! demand-driven signature pass to pick up. Import and export names are
//! decoded and interned here; no body checking happens in this phase.

// use super::*;

use rustc_hash::FxHashMap;
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
// hands back separately from the (lifetime-free) `Declarations`
// itself, for Phase 2's demand-driven signature pass to walk.
struct DeclarationsBuilder<'ast, 'ctx> {
	diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
	strings: &'ctx mut StringInterner,
	files: &'ctx Files,
	/// The package a builtin name (`u8`, `Add`, ...) is only recognized in.
	/// Always present, from `CompilationUnit::core_package`.
	core_package: PackageId,
	root_package: PackageId,
	/// What a package instance looks its key up in: each
	/// package's manifest-declared dependencies.
	packages: &'ast [Package],

	namespaces: Namespaces,
	modules: Vec<ModuleDecl>,
	imports: Vec<ImportDecl>,
	ast_nodes: Vec<AstEntry<'ast>>,
	exports: FxHashMap<SymbolU32, ExportEntrySource>,
	import_entries: FxHashMap<ItemLoc, ImportEntry>,
	package_contracts: Vec<PackageContract>,
	traits: Vec<TraitDecl>,
	trait_impls: Vec<TraitImplDecl>,
	inherent_impls: Vec<InherentImplDecl>,
	structs: Vec<StructDecl>,
	type_aliases: Vec<TypeAliasDecl>,
	enums: Vec<EnumDecl>,
	typesets: Vec<TypesetDecl>,
	functions: Vec<FunctionDecl>,
	memories: Vec<MemoryDecl>,
	globals: Vec<GlobalDecl>,
	constants: Vec<ConstDecl>,
	assoc_types: Vec<AssocTypeDecl>,
	use_items: Vec<UseItemDecl>,
	use_paths: Vec<UsePathSegment>,
	intrinsics: IntrinsicDefs,
	// Keyed by local (alias-or-original) name, not the name as written at the `use` site.
	pending_named_imports:
		FxHashMap<(Scope, SymbolU32), SmallVec<UseItemIndex>>,
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
	pending_glob_targets: FxHashMap<Scope, SmallVec<UseItemIndex>>,
}

index_newtype!(UsePathIndex);
index_newtype!(UseItemIndex);
index_newtype!(PackageInstanceIdx);

/// One package instance, written `package "key" as alias;`: an instantiation of
/// a package.
///
/// Every instance is its own instantiation site, so the same package named by
/// two instances (`package "math" as a; package "math" as b;`) is instantiated
/// twice. Resolution does not yet tell the instances apart: both aliases
/// bind the package's one namespace. This list is what a stage that must
/// (emitting a separate copy of the package per instance) walks instead.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct PackageInstanceDecl {
	/// Its row, in the table of the scope it is written in.
	pub loc: ItemLoc,
	/// The manifest key, decoded; the span covers the literal as written.
	pub package_name: Spanned<SymbolU32>,
	/// The package `package_name` names, or `None` when the manifest
	/// declares no such key (which is reported where the item is scanned).
	/// Until instances are told apart, what the alias leads into is this
	/// package's own namespace.
	pub package: Option<PackageId>,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) struct UsePathSegment {
	pub(super) segment: Spanned<SymbolU32>,
	pub(super) parent: Option<UsePathIndex>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
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

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct UseItemDecl {
	pub namespace: Scope,
	pub pub_span: Option<TextSpan>,
	pub kind: UseItemKind,
}

/// Which of a namespace's two sets of names a binding lives in: types or
/// values. One name can be bound once in each, as a struct is (its type and
/// its constructor).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
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
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
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

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct TraitDecl {
	/// Its row, in the table of the scope it is written in; a typeset's
	/// trait is a generated row beside the typeset's.
	pub loc: ItemLoc,
	/// The typeset this trait was generated for, whose signature query builds
	/// it; `None` for a written trait.
	pub typeset: Option<TypesetIdx>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub(super) bindings: FxHashMap<BindingKey, MemberIdx>,
	pub members: Vec<TraitMemberDecl>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct TraitImplDecl {
	pub file_id: FileId,
	pub namespace: Scope,
	pub members: Vec<TraitMemberDecl>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub(super) bindings: FxHashMap<BindingKey, MemberIdx>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct InherentImplDecl {
	pub file_id: FileId,
	pub namespace: Scope,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub(super) bindings: FxHashMap<BindingKey, MemberIdx>,
	pub members: Vec<InherentMemberDecl>,
}

/// Field identity only (names, each field's `pub`, lookup) — field *types* are
/// `signatures::StructSignature::field_types`, index-aligned with `fields`.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct StructDecl {
	/// Its row, in the table of the scope it is written in.
	pub loc: ItemLoc,
	/// Each field's name, `None` for a positional field.
	pub field_names: Box<[Option<Spanned<SymbolU32>>]>,
	/// Each field's `pub`, index-aligned with `field_names`.
	pub field_pub_spans: Box<[Option<TextSpan>]>,
	/// The named fields by name, each to its first occurrence.
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub lookup: FxHashMap<SymbolU32, FieldIdx>,
	/// How the fields are placed in linear memory.
	pub order: FieldOrder,
}

/// How a struct's fields are placed in linear memory.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum FieldOrder {
	/// In declaration order, as `#[fixed_order]` asks: a layout the program
	/// shares with something outside it.
	Fixed,
	/// In descending alignment, which leaves the least padding.
	Optimal,
}

/// The attributes written on a declaration that the compiler acts on. The
/// prescan admits only those that apply to the item they are written on,
/// so a function's never holds `FIXED_ORDER`. An attribute is a hint to the
/// compiler: none of them changes a type or an identity.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Attributes(u8);

impl Attributes {
	/// `#[inline]`: every call of the function is to be replaced by its
	/// body.
	pub const INLINE: Self = Self(1 << 0);
	/// `#[fixed_order]`: a struct's fields keep declaration order.
	pub const FIXED_ORDER: Self = Self(1 << 1);

	pub const fn empty() -> Self {
		Self(0)
	}

	pub const fn contains(self, other: Self) -> bool {
		self.0 & other.0 == other.0
	}

	fn insert(&mut self, other: Self) {
		self.0 |= other.0;
	}
}

/// An attribute the compiler knows. `#[memory_limits]` has arguments and
/// is read where a memory is lowered, so it has no flag.
#[derive(Clone, Copy, PartialEq, Eq)]
enum KnownAttribute {
	Inline,
	FixedOrder,
	MemoryLimits,
}

impl KnownAttribute {
	const ALL: [Self; 3] = [Self::Inline, Self::FixedOrder, Self::MemoryLimits];

	fn from_name(name: &str) -> Option<Self> {
		Self::ALL.into_iter().find(|known| known.name() == name)
	}

	fn name(self) -> &'static str {
		match self {
			Self::Inline => "inline",
			Self::FixedOrder => "fixed_order",
			Self::MemoryLimits => "memory_limits",
		}
	}

	/// The one kind of item it can be written on.
	fn target(self) -> AttributeTarget {
		match self {
			Self::Inline => AttributeTarget::Function,
			Self::FixedOrder => AttributeTarget::Struct,
			Self::MemoryLimits => AttributeTarget::Memory,
		}
	}

	/// Whether it is written with a parenthesized argument list, rather
	/// than as its name alone.
	fn takes_arguments(self) -> bool {
		matches!(self, Self::MemoryLimits)
	}

	fn flag(self) -> Attributes {
		match self {
			Self::Inline => Attributes::INLINE,
			Self::FixedOrder => Attributes::FIXED_ORDER,
			Self::MemoryLimits => Attributes::empty(),
		}
	}
}

/// What an attribute is written on, as far as which attributes apply.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AttributeTarget {
	/// A function with a body: free, an impl's, or a trait's default.
	Function,
	/// A function declared without one: a trait's required function, a
	/// bodiless declaration, a package contract's.
	BodilessFunction,
	Struct,
	Memory,
	Enum,
	Constant,
	Global,
	TypeAlias,
	Trait,
	Typeset,
	AssociatedType,
}

impl AttributeTarget {
	fn description(self) -> &'static str {
		match self {
			Self::Function => "a function with a body",
			Self::BodilessFunction => "a function without a body",
			Self::Struct => "a struct",
			Self::Memory => "a memory",
			Self::Enum => "an enum",
			Self::Constant => "a constant",
			Self::Global => "a global",
			Self::TypeAlias => "a type alias",
			Self::Trait => "a trait",
			Self::Typeset => "a typeset",
			Self::AssociatedType => "an associated type",
		}
	}

	/// The attributes written on an item, and what they are written on.
	fn of_item(item: &ast::Item) -> Option<(Self, &[ast::Attribute])> {
		Some(match item {
			ast::Item::Function { attributes, .. } => {
				(Self::Function, attributes)
			}
			ast::Item::FunctionDeclaration { attributes, .. }
			| ast::Item::PackageFunction { attributes, .. } => {
				(Self::BodilessFunction, attributes)
			}
			ast::Item::Struct { attributes, .. } => (Self::Struct, attributes),
			ast::Item::Memory { attributes, .. } => (Self::Memory, attributes),
			ast::Item::Enum { attributes, .. } => (Self::Enum, attributes),
			ast::Item::Const { attributes, .. }
			| ast::Item::PackageConst { attributes, .. } => (Self::Constant, attributes),
			ast::Item::Global { attributes, .. } => (Self::Global, attributes),
			ast::Item::TypeAlias { attributes, .. }
			| ast::Item::PackageType { attributes, .. } => (Self::TypeAlias, attributes),
			ast::Item::Trait { attributes, .. } => (Self::Trait, attributes),
			ast::Item::TypeSet { attributes, .. } => {
				(Self::Typeset, attributes)
			}
			ast::Item::Export { .. }
			| ast::Item::ExportBlock { .. }
			| ast::Item::Import { .. }
			| ast::Item::InherentImpl { .. }
			| ast::Item::TraitImpl { .. }
			| ast::Item::Module { .. }
			| ast::Item::ModuleDeclaration { .. }
			| ast::Item::PackageInstance { .. }
			| ast::Item::Use { .. } => return None,
		})
	}

	fn of_trait_item(item: &ast::TraitItem) -> (Self, &[ast::Attribute]) {
		match item {
			ast::TraitItem::Function {
				attributes,
				body: Some(_),
				..
			} => (Self::Function, attributes),
			ast::TraitItem::Function {
				attributes,
				body: None,
				..
			} => (Self::BodilessFunction, attributes),
			ast::TraitItem::Const { attributes, .. } => {
				(Self::Constant, attributes)
			}
			ast::TraitItem::AssociatedType { attributes, .. } => {
				(Self::AssociatedType, attributes)
			}
		}
	}

	fn of_impl_item(item: &ast::ImplItem) -> (Self, &[ast::Attribute]) {
		match item {
			ast::ImplItem::Function { attributes, .. } => {
				(Self::Function, attributes)
			}
			ast::ImplItem::Constant { attributes, .. } => {
				(Self::Constant, attributes)
			}
			ast::ImplItem::AssocType { attributes, .. } => {
				(Self::AssociatedType, attributes)
			}
		}
	}
}

impl StructDecl {
	/// Whether every field has a name: only then can the struct be
	/// constructed (`P({ x: 1, y: 2 })`) or destructured by name.
	pub fn is_fully_named(&self) -> bool {
		self.field_names.iter().all(Option::is_some)
	}
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct EnumDecl {
	/// Its row, in the table of the scope it is written in.
	pub loc: ItemLoc,
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
	/// The first `..` in the body, if there is one: the variants name some of
	/// the enum's values and every value of its repr is valid. A `..` is not
	/// a variant and has no constant.
	pub open: Option<TextSpan>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct TypeAliasDecl {
	/// Its row, in the table of the scope it is written in.
	pub loc: ItemLoc,
}

/// `typeset X: A + B { m1, m2 }` — `trait_index` is a generated trait with
/// no AST node of its own (`TraitDecl::typeset` names this typeset). Its
/// data, the supertraits from `: A + B`, is written by this typeset's
/// signature query, so forcing the trait means forcing `SignatureQuery::Typeset`.
/// `member_impls` is index-aligned with the AST's own `members` list: one
/// generated `impl <trait_index> for <member>` per written member, filled in
/// with the member's resolved type by that same query.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct TypesetDecl {
	/// Its row, in the table of the scope it is written in.
	pub loc: ItemLoc,
	pub trait_index: TraitIdx,
	pub member_impls: Box<[TraitImplIdx]>,
}

/// Shared by a free function, a trait member, and an impl method — one
/// arena, the same reason `signatures::FunctionSignature` covers all
/// three. Field *types* stay in that struct, index-aligned with `params`
/// here, same split as `StructDecl`/`StructSignature`.
///
/// Every function is its own type, so each has `function_impls`, its
/// synthetic `impl Call` and `impl Function`.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct FunctionDecl {
	/// Its row, in the table of the scope it, or its trait or impl, is
	/// written in.
	pub loc: ItemLoc,
	pub owner: MemberOwner,
	/// Each parameter's name, `None` for an unnamed one.
	pub params: Box<[Option<Spanned<SymbolU32>>]>,
	pub function_impls: FunctionImpls,
	/// Only ever `INLINE`, and only on a function with a body.
	pub attributes: Attributes,
}

/// Where a function or a constant is declared: directly in a scope (a free
/// or imported one), or as a member of a trait or impl. A trait's
/// declaration is reached through the impl its `Self` selects.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub enum MemberOwner {
	Free,
	Trait(TraitIdx),
	InherentImpl(InherentImplIdx),
	TraitImpl(TraitImplIdx),
}

/// A function's synthetic `impl Call for <function>`, which holds `Args` and
/// `Result`, and its `impl Function for <function>`, which declares nothing
/// (like a `global mut`'s `GlobalMut` impl). Pre-allocated for the same
/// reason as `MemoryDecl`'s own fields.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
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
/// typeset's generated impls (see `TypesetDecl`), nothing forces these
/// through a query of their own: they're populated as a side effect of
/// resolving this memory's own signature. Allocating the slot never depends
/// on `IntrinsicDefs::memory` — it's just an index and a name, no reference
/// to the `Memory` trait itself. That trait is only needed later, to bucket
/// this impl for dispatch (`impls.rs`); if core never declared one, that's
/// where it's diagnosed as the broken-core error it is, not something
/// every reader of this struct has to keep re-checking for.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct MemoryDecl {
	/// Its row, in the table of the scope it is written in.
	pub loc: ItemLoc,
	pub trait_impl_index: TraitImplIdx,
	pub size_assoc_type_index: AssocTypeIdx,
	/// What its `#[memory_limits]` says; both bounds `None` without one, and
	/// for an imported memory, which takes the host's memory of any size.
	pub limits: MemoryLimits,
}

/// A memory's page limits, as `#[memory_limits({ min_pages: .., max_pages:
/// .. })]` writes them: counts of 64 KiB pages, `None` for a bound left out.
/// Recorded as written; whether a count fits the memory is the checker's
/// (`Semantics::check_memory_limits`), since it depends on the memory's
/// `Size`.
#[derive(Clone, Copy, Default)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct MemoryLimits {
	pub min_pages: Option<Spanned<u64>>,
	pub max_pages: Option<Spanned<u64>>,
}

/// Identity shared by local and imported globals. The written value type
/// remains in the AST for later resolution (and may be entirely absent —
/// `global x = 0;` infers it from the value, which needs the body phase
/// this architecture doesn't have yet).
///
/// `trait_impl_index`/`value_assoc_type_index` are this global's synthetic
/// `impl Global for <global>`, unconditionally pre-allocated for the same
/// reason as `MemoryDecl`'s own fields. `mut_trait_impl_index` is the
/// additional `impl GlobalMut for <global>` a `global mut` declaration also
/// gets (`GlobalMut` declares no members of its own — an empty impl is
/// enough to make it a dispatch candidate) — genuinely absent for a
/// non-`mut` global, unlike the other two fields.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct GlobalDecl {
	/// Its row, in the table of the scope it is written in.
	pub loc: ItemLoc,
	pub trait_impl_index: TraitImplIdx,
	pub value_assoc_type_index: AssocTypeIdx,
	pub mut_trait_impl_index: Option<TraitImplIdx>,
}

/// Identity of a free, trait, or impl constant. Its type and value are
/// resolved in later phases.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ConstDecl {
	/// Its row: a variant's in its enum's table, any other constant's in
	/// the table of the scope it, or its trait or impl, is written in.
	pub loc: ItemLoc,
	/// An enum's variant is free: it is no trait's or impl's member.
	pub owner: MemberOwner,
}

/// Each trait declaration and each impl definition has its own identity.
/// Declared bounds and impl target types remain in the AST for resolution.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct AssocTypeDecl {
	/// Its row, in the table of the scope its trait or impl is written
	/// in (or its generator, for a function's, memory's or global's impl).
	pub loc: ItemLoc,
}

index_newtype!(DeclIdx);
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

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct TraitMemberDecl {
	pub kind: MemberKind,
	pub span: TextSpan,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct InherentMemberDecl {
	pub kind: MemberKind,
	pub span: TextSpan,
}

impl DeclIdx {
	/// A package's own entry, the first in its table, which `self` and
	/// `package` at its root, and `super` in its top-level modules, name.
	pub(super) const SELF: Self = DeclIdx(0);
}

#[derive(Clone)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub(super) struct AstEntry<'ast> {
	pub(super) file_id: FileId,
	/// The scope the item is written in, where its signature resolves: for
	/// an imported declaration, its import block's own scope.
	pub(super) namespace: Scope,
	pub(super) node: AstNodeRef<'ast>,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
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
		import_block: &'ast ast::ImportDeclaration,
	},
	ImportedFunction {
		function_index: FunctionIdx,
		import_index: ImportIdx,
		import_block: &'ast ast::ImportDeclaration,
	},
	ImportedGlobal {
		global_index: GlobalIdx,
		import_index: ImportIdx,
		import_block: &'ast ast::ImportDeclaration,
	},
}

impl AstNodeRef<'_> {
	/// The declaration this entry writes.
	pub(super) fn query(&self) -> SignatureQuery {
		match *self {
			Self::Function { func_index, .. } => {
				SignatureQuery::Function(func_index)
			}
			Self::TraitFunction { function_index, .. }
			| Self::TraitImplFunction { function_index, .. }
			| Self::InherentImplFunction { function_index, .. }
			| Self::ImportedFunction { function_index, .. } => {
				SignatureQuery::Function(function_index)
			}
			Self::Struct { struct_index, .. } => {
				SignatureQuery::Struct(struct_index)
			}
			Self::Enum { enum_index, .. } => SignatureQuery::Enum(enum_index),
			Self::Global { global_index, .. }
			| Self::ImportedGlobal { global_index, .. } => {
				SignatureQuery::Global(global_index)
			}
			Self::Memory { memory_index, .. }
			| Self::ImportedMemory { memory_index, .. } => {
				SignatureQuery::Memory(memory_index)
			}
			Self::Constant { const_index, .. }
			| Self::TraitConst { const_index, .. }
			| Self::TraitImplConstant { const_index, .. }
			| Self::InherentImplConst { const_index, .. }
			| Self::EnumVariant { const_index, .. } => {
				SignatureQuery::Const(const_index)
			}
			Self::TypeSet { typeset_index, .. } => {
				SignatureQuery::Typeset(typeset_index)
			}
			Self::TypeAlias {
				type_alias_index, ..
			} => SignatureQuery::TypeAlias(type_alias_index),
			Self::Trait { trait_index, .. } => {
				SignatureQuery::Trait(trait_index)
			}
			Self::TraitAssocType {
				assoc_type_index, ..
			}
			| Self::TraitImplAssocType {
				assoc_type_index, ..
			} => SignatureQuery::AssocType(assoc_type_index),
			Self::TraitImplBlock { block_index, .. } => {
				SignatureQuery::TraitImpl(block_index)
			}
			Self::InherentImplBlock { block_index, .. } => {
				SignatureQuery::InherentImpl(block_index)
			}
		}
	}
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) struct ExportEntrySource {
	pub namespace: Scope,
	pub name: Spanned<SymbolU32>,
	pub external_span: SourceSpan,
}

/// One package's externally supplied declarations, independent of the
/// modules in which their names are visible. A free function claims both
/// tiers, as it does in its module's ordinary symbol table.
#[derive(Default)]
pub(super) struct PackageContract {
	pub(super) members: FxHashMap<BindingKey, PackageMember>,
}

#[derive(Clone, Copy)]
pub(super) struct PackageMember {
	pub(super) item: PackageMemberItem,
	pub(super) namespace: Scope,
	pub(super) source: SourceSpan,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PackageMemberItem {
	Function(FunctionIdx),
	Constant(ConstIdx),
	Type(TypeAliasIdx),
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct Declarations {
	pub core_package: PackageId,
	pub root_package: PackageId,
	pub namespaces: Namespaces,
	/// The scope each file's top-level items live in, indexed by `FileId`.
	#[cfg_attr(any(debug_assertions, test), serde(skip))]
	pub file_namespaces: Vec<Scope>,
	pub modules: Vec<ModuleDecl>,
	pub imports: Vec<ImportDecl>,
	/// Selected crate's compilation exports, keyed by decoded external name.
	pub(super) exports: FxHashMap<SymbolU32, ExportEntrySource>,
	/// The entry each host-imported declaration is written in, by its row.
	#[cfg_attr(any(debug_assertions, test), serde(skip))]
	pub(super) import_entries: FxHashMap<ItemLoc, ImportEntry>,
	/// Package-level contract keys, indexed by `PackageId`.
	#[cfg_attr(any(debug_assertions, test), serde(skip))]
	pub(super) package_contracts: Vec<PackageContract>,
	pub traits: Vec<TraitDecl>,
	pub trait_impls: Vec<TraitImplDecl>,
	pub inherent_impls: Vec<InherentImplDecl>,
	pub structs: Vec<StructDecl>,
	pub enums: Vec<EnumDecl>,
	pub typesets: Vec<TypesetDecl>,
	pub functions: Vec<FunctionDecl>,
	pub memories: Vec<MemoryDecl>,
	pub globals: Vec<GlobalDecl>,
	pub constants: Vec<ConstDecl>,
	pub assoc_types: Vec<AssocTypeDecl>,
	pub type_aliases: Vec<TypeAliasDecl>,
	pub use_items: Vec<UseItemDecl>,
	pub(super) use_paths: Vec<UsePathSegment>,
	/// The `ItemLoc` of every language builtin recognized by name in the
	/// core package — primitive types (`u8`, `funcref`, ...), `Bool`, `Char` and
	/// operator traits (`Add`, `PartialEq`, ...) alike. `None` for any name
	/// prescan never found declared there. No `#[intrinsic]` marker is
	/// involved: recognition is implicit — a reserved name, of the right
	/// declaration kind, declared in the core package *is* that builtin.
	/// This is core's own responsibility to get right, same as any other
	/// name collision within a single package. Same epistemic status as
	/// everything else on this registry: what was recorded, not a judgment
	/// about completeness.
	pub intrinsics: IntrinsicDefs,
}

/// One struct rather than one per kind — the recognized-name list only
/// needs to be written once — but [`IntrinsicDefs::type_slot_mut`],
/// [`IntrinsicDefs::trait_slot_mut`] and
/// [`IntrinsicDefs::typeset_slot_mut`] are kept as separate lookups (rather
/// than one covering all fields) so a type alias, a trait and a typeset can
/// never contend for the same slot just because they happen to share a
/// name — e.g. a stray `type Add;` in core can't clobber the `Add` trait's
/// entry, since only `trait_slot_mut` ever resolves `"Add"`.
#[derive(Default)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
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
	/// core's `Bool` and `Char`, which the compiler's conditions and literals
	/// are typed with.
	pub bool: Option<EnumIdx>,
	pub char: Option<StructIdx>,
	pub funcref: Option<TypeAliasIdx>,
	/// core's `Integer` typeset, whose members are the integer primitives.
	/// Enum representations are checked against it.
	pub integer: Option<TypesetIdx>,
	/// The literal kinds `integer` and `char`, written `{integer}` and
	/// `{char}`: the types of literals that have no type yet.
	pub integer_kind: Option<TypeAliasIdx>,
	pub char_kind: Option<TypeAliasIdx>,
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
	/// core's `Eq`, the total-equality marker used by pattern tests.
	pub eq: Option<TraitIdx>,
	pub memory: Option<TraitIdx>,
	/// `Memory`'s declaration of `Size`.
	pub memory_size: Option<AssocTypeIdx>,
	pub global: Option<TraitIdx>,
	pub global_mut: Option<TraitIdx>,
	pub call: Option<TraitIdx>,
	/// `Call`'s declarations of `Args` and `Result`, which a function
	/// reference's type answers by a compiler rule.
	pub call_args: Option<AssocTypeIdx>,
	pub call_result: Option<AssocTypeIdx>,
	pub function: Option<TraitIdx>,
	pub stack_value: Option<TraitIdx>,
	/// `StackValue`'s declaration of `Repr`, which every type answers by a
	/// compiler rule.
	pub stack_value_repr: Option<AssocTypeIdx>,
	/// `Slice` and `Array`, which the compiler implements for the slices and
	/// arrays `[T]` and `[T; N]`.
	pub slice: Option<TraitIdx>,
	pub array: Option<TraitIdx>,
	/// `Slice`'s declaration of `Value`: a slice's or an array's element.
	pub slice_value: Option<AssocTypeIdx>,
	/// `Slice`'s bodiless `len` and `as_ref`, which lowering supplies from
	/// the receiver's type. Its other functions, and `Array`'s, have bodies.
	pub slice_len: Option<FunctionIdx>,
	pub slice_as_ref: Option<FunctionIdx>,
	/// `Array`'s declaration of `LEN`: an array's length.
	pub array_len: Option<ConstIdx>,
	/// `Memory`'s declaration of `DATA_END`: where a memory's static data
	/// ends, known once the program's data is laid out.
	pub memory_data_end: Option<ConstIdx>,
	/// `Pointer`, which the compiler implements for every pointer type, and
	/// its declarations of `Memory`, `Pointee` and `Metadata`.
	pub pointer: Option<TraitIdx>,
	pub pointer_memory: Option<AssocTypeIdx>,
	pub pointer_pointee: Option<AssocTypeIdx>,
	pub pointer_metadata: Option<AssocTypeIdx>,
}

impl IntrinsicDefs {
	/// Whether the compiler supplies `function`, a member of `trait_index`
	/// for a type that trait is implemented for structurally: `Call` of a
	/// function reference, and `Slice`'s bodiless `len` and `as_ref`. Any
	/// other member of such a trait is its default body.
	pub fn supplies(
		&self,
		trait_index: TraitIdx,
		function: FunctionIdx,
	) -> bool {
		self.call == Some(trait_index)
			|| [self.slice_len, self.slice_as_ref].contains(&Some(function))
	}

	/// Whether `alias` is a type the compiler provides, a primitive or a
	/// literal kind: one of the bodiless types `type_slot_mut` recognizes.
	pub fn is_builtin_type(&self, alias: TypeAliasIdx) -> bool {
		[
			self.u8,
			self.i8,
			self.u16,
			self.i16,
			self.u32,
			self.i32,
			self.u64,
			self.i64,
			self.f32,
			self.f64,
			self.funcref,
			self.integer_kind,
			self.char_kind,
		]
		.contains(&Some(alias))
	}

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
			"funcref" => &mut self.funcref,
			"integer" => &mut self.integer_kind,
			"char" => &mut self.char_kind,
			_ => return None,
		})
	}

	/// The mutable slot for `name` if it's one of the recognized builtin
	/// typeset names — the one place that list is written.
	fn typeset_slot_mut(
		&mut self,
		name: &str,
	) -> Option<&mut Option<TypesetIdx>> {
		Some(match name {
			"Integer" => &mut self.integer,
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
			"Eq" => &mut self.eq,
			"Memory" => &mut self.memory,
			"Global" => &mut self.global,
			"GlobalMut" => &mut self.global_mut,
			"Call" => &mut self.call,
			"Function" => &mut self.function,
			"StackValue" => &mut self.stack_value,
			"Slice" => &mut self.slice,
			"Array" => &mut self.array,
			"Pointer" => &mut self.pointer,
			_ => return None,
		})
	}
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
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
pub enum SignatureQuery {
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
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum DeclKind {
	Module(ModuleIdx),
	Import(ImportIdx),
	Package(PackageId),
	/// A package instance, `package "key" as alias;`: the name it binds. What a path
	/// continues into is the package it instantiates, which only
	/// [`Namespaces::entered_by`] can say.
	PackageInstance(PackageInstanceIdx),
	Enum(EnumIdx),
	EnumVariant(ConstIdx),
	Struct(StructIdx),
	Memory(MemoryIdx),
	Trait(TraitIdx),
	TypeSet(TypesetIdx),
	Global(GlobalIdx),
	Function(FunctionIdx),
	Const(ConstIdx),
	AssocType(AssocTypeIdx),
	TypeAlias(TypeAliasIdx),
}

impl DeclKind {
	/// What kind of symbol this is, for diagnostics.
	pub fn noun(self) -> &'static str {
		match self {
			DeclKind::Module(_) => "module",
			DeclKind::Import(_) => "import block",
			DeclKind::Package(_) => "package",
			DeclKind::PackageInstance(_) => "package instance",
			DeclKind::Enum(_) => "enum",
			DeclKind::EnumVariant(_) => "enum variant",
			DeclKind::Struct(_) => "struct",
			DeclKind::Memory(_) => "memory",
			DeclKind::Trait(_) => "trait",
			DeclKind::TypeSet(_) => "typeset",
			DeclKind::Global(_) => "global",
			DeclKind::Function(_) => "function",
			DeclKind::Const(_) => "constant",
			DeclKind::AssocType(_) => "associated type",
			DeclKind::TypeAlias(_) => "type alias",
		}
	}

	/// Where the declaration's name is written, for diagnostics. A package,
	/// module or import block has no declaration of its own to point at.
	pub(super) fn declared_at(
		self,
		decls: &Declarations,
	) -> Option<SourceSpan> {
		let key = match self {
			DeclKind::Module(_)
			| DeclKind::Import(_)
			| DeclKind::Package(_) => {
				return None;
			}
			DeclKind::PackageInstance(index) => index.loc(decls),
			DeclKind::Enum(index) => index.loc(decls),
			DeclKind::EnumVariant(index) | DeclKind::Const(index) => {
				index.loc(decls)
			}
			DeclKind::Struct(index) => index.loc(decls),
			DeclKind::Memory(index) => index.loc(decls),
			DeclKind::Trait(index) => index.loc(decls),
			DeclKind::TypeSet(index) => index.loc(decls),
			DeclKind::Global(index) => index.loc(decls),
			DeclKind::Function(index) => index.loc(decls),
			DeclKind::AssocType(index) => index.loc(decls),
			DeclKind::TypeAlias(index) => index.loc(decls),
		};
		Some(decls.declaration_span(key))
	}
}

/// Something a path can continue into: what `a::` names when `a` is a
/// package, a module, an enum or an import block. Each is addressed by its
/// owner's own index, so the handle and the owner are one thing.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Namespace {
	Package(PackageId),
	Module(ModuleIdx),
	Enum(EnumIdx),
	Import(ImportIdx),
}

/// A namespace code is written in: where an unqualified lookup starts, and
/// the accessor of every privacy check. Import signatures also have a scope:
/// sibling declarations are local; `use` items can bring in other
/// names. Enums expose variants through paths and are not scopes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Scope {
	Package(PackageId),
	Module(ModuleIdx),
	Import(ImportIdx),
}

impl From<Scope> for Namespace {
	#[inline]
	fn from(scope: Scope) -> Self {
		match scope {
			Scope::Package(package) => Self::Package(package),
			Scope::Module(module) => Self::Module(module),
			Scope::Import(import) => Self::Import(import),
		}
	}
}

impl Namespace {
	pub(super) fn as_scope(self) -> Option<Scope> {
		match self {
			Self::Package(package) => Some(Scope::Package(package)),
			Self::Module(module) => Some(Scope::Module(module)),
			Self::Import(import) => Some(Scope::Import(import)),
			Self::Enum(_) => None,
		}
	}
}

/// A declaration made in a table's namespace, as written: a row of
/// `SymbolTable::items`, which a `ItemLoc` addresses.
///
/// A row is reachable by name only through a binding that points at it, so
/// a trait's or an impl's member is a row of the scope its trait or impl is
/// written in without being bound there. A generated declaration (a
/// typeset's trait, the associated types of a function's, memory's or
/// global's impl, a package's own entry) has a row whose name span is empty.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ItemDecl {
	/// Which arena holds what it means, and its index there.
	pub kind: DeclKind,
	pub name: Spanned<SymbolU32>,
	/// Whether `pub` is written on it. A rule that derives a visibility from
	/// another (a trait member is as visible as its trait, an import
	/// block's entries are visible in the block) is the code's that applies
	/// it; a generated declaration has what its generator writes (a
	/// typeset's trait the typeset's).
	pub visibility: Visibility,
}

impl ItemDecl {
	fn new(
		kind: DeclKind,
		name: Spanned<SymbolU32>,
		visibility: Visibility,
	) -> Self {
		Self {
			kind,
			name,
			visibility,
		}
	}
}

/// What one namespace holds: the definitions declared in it (`items`, which
/// a `ItemLoc` addresses) and the names it binds. Every namespace is written in
/// one file.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct SymbolTable {
	pub file_id: FileId,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: FxHashMap<BindingKey, Binding>,
	pub items: Vec<ItemDecl>,
}

impl SymbolTable {
	fn new(file_id: FileId) -> Self {
		Self {
			file_id,
			bindings: FxHashMap::default(),
			items: Vec::new(),
		}
	}
}

/// A scope's symbols, plus what only a scope has: a place in the lexical tree
/// and the globs its `use path::*;` items brought in.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
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

impl ScopeTable {
	/// A module or import block has the same explicit scope qualifiers:
	/// `self` names its own declaration `own`, `super` the one of the scope
	/// it is written in, `parent_key`, and `package` its package's root.
	fn child(
		mut symbols: SymbolTable,
		own: ItemLoc,
		parent: Scope,
		parent_key: ItemLoc,
		package_id: PackageId,
	) -> Self {
		for (name, target) in [
			(Keyword::SelfLower, own),
			(
				Keyword::Package,
				ItemLoc::new(Namespace::Package(package_id), DeclIdx::SELF),
			),
			(Keyword::Super, parent_key),
		] {
			symbols.bindings.insert(
				BindingKey::ty(name.symbol()),
				Binding::definition(target, Visibility::Public),
			);
		}
		Self {
			symbols,
			parent: Some(parent),
			package_id,
			glob_imports: Vec::new(),
		}
	}
}

/// Every namespace's table, each list indexed by its owner's own index:
/// `packages` by `PackageId`, `modules` by `ModuleIdx`, `enums` by `EnumIdx`
/// and `imports` by `ImportIdx`. An owner and its table are pushed together,
/// which is what keeps the two aligned.
#[derive(Default)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct Namespaces {
	packages: Vec<ScopeTable>,
	modules: Vec<ScopeTable>,
	enums: Vec<SymbolTable>,
	imports: Vec<ScopeTable>,
	/// Every package instance, indexed by `PackageInstanceIdx`. Held here because what
	/// a package instance's alias leads into is part of how a path walks, and the
	/// item says which package that is.
	package_instances: Vec<PackageInstanceDecl>,
}

/// The result of [`Namespaces::lookup`]/[`Namespaces::indirect_lookup`].
/// `Found` pairs a target with its visibility — an accessibility check and
/// re-export capping both need both at once, and this holds regardless of
/// whether `accessor` can actually see it; that's left for the caller to
/// decide, same as a direct (non-glob) hit always has been.
///
/// `Ambiguous` carries every surviving candidate paired with the `pub use`
/// edge responsible for it — the diagnostic needs to name each one, same as
/// two colliding ordinary globs already do. The same `ItemLoc` reached through
/// two different edges is merged into one candidate before it ever becomes
/// an entry here, not after — see `indirect_lookup`. No visibility here: by
/// construction, every entry that survives into this variant was already
/// confirmed accessible to whichever `accessor` `indirect_lookup` was asked
/// on behalf of, so there's nothing left for it to say.
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
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
/// same `ItemLoc` reached through two `pub` edges (e.g. a diamond re-export)
/// isn't a conflict, and when the two edges disagree, `Accessible` wins
/// silently, same as `try_insert_binding` resolves the same disagreement
/// for a direct same-namespace collision.
///
/// Separately, `is_accessible_from(accessor, ..)` asks whether *this
/// query's* accessor can see a given def at all, checked fresh. A lone real
/// candidate is always kept as `One`, visibility included, regardless of
/// that check — deferred to the caller, same as a direct hit. It's only
/// consulted the moment a second, distinct `ItemLoc` would otherwise promote
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
	// for `push`: if a second, distinct `ItemLoc` arrives later and this
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
		let Some(loc) = candidate.target.loc() else {
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
					.loc()
					.expect("a real candidate always carries a DefKey");

				if first_key == loc {
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
					loc.namespace,
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
					loc.namespace,
					candidate.visibility,
				) {
					return;
				}
				let slot = items
					.iter_mut()
					.find(|(target, _)| target.loc() == Some(loc));
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
			Namespace::Import(import) => {
				&self.imports[usize::from(import)].symbols
			}
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
			Namespace::Import(import) => {
				&mut self.imports[usize::from(import)].symbols
			}
		}
	}

	/// Every declaration of every namespace, in no particular order.
	pub fn keys(&self) -> impl Iterator<Item = ItemLoc> + '_ {
		let packages = self
			.packages
			.iter()
			.map(|table| Namespace::Package(table.package_id));
		let modules = (0..self.modules.len())
			.map(|index| Namespace::Module(ModuleIdx::new(index as u32)));
		let enums = (0..self.enums.len())
			.map(|index| Namespace::Enum(EnumIdx::new(index as u32)));
		let imports = (0..self.imports.len())
			.map(|index| Namespace::Import(ImportIdx::new(index as u32)));
		packages
			.chain(modules)
			.chain(enums)
			.chain(imports)
			.flat_map(move |namespace| {
				(0..self.symbols(namespace).items.len()).map(move |index| {
					ItemLoc::new(namespace, DeclIdx::new(index as u32))
				})
			})
	}

	pub(super) fn scope(&self, scope: Scope) -> &ScopeTable {
		match scope {
			Scope::Package(package) => &self.packages[package.as_usize()],
			Scope::Module(module) => &self.modules[usize::from(module)],
			Scope::Import(import) => &self.imports[usize::from(import)],
		}
	}

	pub(super) fn scope_mut(&mut self, scope: Scope) -> &mut ScopeTable {
		match scope {
			Scope::Package(package) => &mut self.packages[package.as_usize()],
			Scope::Module(module) => &mut self.modules[usize::from(module)],
			Scope::Import(import) => &mut self.imports[usize::from(import)],
		}
	}

	pub(super) fn file_id(&self, namespace: Namespace) -> FileId {
		self.symbols(namespace).file_id
	}

	/// The declaration `loc` addresses, its row.
	pub fn item(&self, loc: ItemLoc) -> &ItemDecl {
		&self.symbols(loc.namespace).items[usize::from(loc.decl_idx)]
	}

	/// What `loc` names.
	pub(super) fn kind(&self, loc: ItemLoc) -> DeclKind {
		self.item(loc).kind
	}

	pub fn package_instances(&self) -> &[PackageInstanceDecl] {
		&self.package_instances
	}

	/// The namespace a path continues into after `loc`: what `a::` names
	/// when `a` is a package, a module, an enum, an import block or a crate
	/// item. `None` for anything a path cannot continue through.
	pub(super) fn entered_by(&self, loc: ItemLoc) -> Option<Namespace> {
		Some(match self.kind(loc) {
			DeclKind::Package(package) => Namespace::Package(package),
			DeclKind::Module(module) => Namespace::Module(module),
			DeclKind::Enum(enum_index) => Namespace::Enum(enum_index),
			DeclKind::Import(import) => Namespace::Import(import),
			// Until instances are told apart, a package instance leads into its
			// package's own namespace.
			DeclKind::PackageInstance(index) => Namespace::Package(
				self.package_instances[usize::from(index)].package?,
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
			// An enum has no lexical scope; import signatures do, and inherit
			// access to private declarations in their enclosing module.
			Visibility::Private => target
				.as_scope()
				.is_some_and(|target| self.contains(target, accessor)),
		}
	}

	/// Inserts `binding` under `key` in `namespace`. `Err` carries the
	/// colliding `ItemLoc` when one was already there and both count as
	/// real occupants of the name — this is an error state, not merely an
	/// optional value, hence `Result` over `Option`. No diagnostics here —
	/// this only touches the namespace graph; a caller with
	/// `diagnostics`/`strings` on hand (see
	/// `DeclarationsBuilder`/`ImportResolver`'s own `insert_binding`)
	/// is what turns a collision into a reported error.
	pub(super) fn try_insert_binding(
		&mut self,
		namespace: Namespace,
		key: BindingKey,
		binding: Binding,
	) -> Result<(), ItemLoc> {
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
	/// because import resolution rejects any cycle that an accessor could
	/// actually traverse. Only a scope has globs.
	///
	/// `accessor` also matters once two *distinct* candidates compete: a
	/// candidate `accessor` could never legally choose is excluded right
	/// then, rather than surviving into a misleading `Ambiguous`. A lone
	/// candidate is always returned `Found`, visibility included,
	/// regardless of whether `accessor` can see *that candidate* — deferred
	/// to the caller, same as a direct (non-glob) hit already is.
	fn indirect_lookup(
		&self,
		use_items: &[UseItemDecl],
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
		use_items: &[UseItemDecl],
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
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub(super) enum BindingTarget {
	Accessible(ItemLoc),
	/// Resolved to a real def, but the source wasn't visible from the
	/// writing namespace when a `use` resolved it. Not poisoned like
	/// `Error` — whatever already enforces privacy at reference sites for
	/// direct qualified paths should apply the same check here, reporting
	/// (or not) each time this binding is actually used, not just once.
	Inaccessible(ItemLoc),
	Error,
}

impl BindingTarget {
	/// The underlying definition this target names, if it names one at all
	/// — `Error` doesn't, since it's recovery state for an already-diagnosed
	/// failure rather than a reference to anything real.
	pub(super) fn loc(self) -> Option<ItemLoc> {
		match self {
			Self::Accessible(key) | Self::Inaccessible(key) => Some(key),
			Self::Error => None,
		}
	}
}

#[derive(Clone)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
enum BindingSource {
	Definition,
	Import(UseItemIndex),
}

#[derive(Clone)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) struct Binding {
	pub(super) target: BindingTarget,
	pub(super) visibility: Visibility,
	source: BindingSource,
}

impl Binding {
	fn definition(loc: ItemLoc, visibility: Visibility) -> Self {
		Self {
			target: BindingTarget::Accessible(loc),
			visibility,
			source: BindingSource::Definition,
		}
	}

	/// A name declared by a definition that could not be resolved, such as
	/// a package instance whose key the manifest does not declare. It carries
	/// no `ItemLoc`, so a path through it ends silently on top of the error
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
		use_items: &[UseItemDecl],
	) -> SourceSpan {
		match self.source {
			BindingSource::Definition => {
				let loc = match self.target {
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
				loc.source_span(namespaces)
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

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ModuleDecl {
	/// Its row, in the table of the scope `mod foo` is written in, which is
	/// where its name is bound and what `super` names inside it.
	pub loc: ItemLoc,
	/// The file that IS `foo`'s content: `foo.wx` for `mod foo;`, or the
	/// file `mod foo { .. }` is written in, its row's
	/// (`Declarations::file_id(decl)`), for an inline module.
	pub own_file: FileId,
}

/// One `use path::*;` edge — the namespace it resolved to, plus which item
/// produced it.
///
/// `use_item` is a back-reference, not a copy: `pub_span`, the declaring
/// namespace, and (via `UseItemKind::Glob`) the `x::*` span all already live
/// on the `UseItemDecl` — duplicating them here would just be two copies of
/// the same fact able to drift, the same reason `Binding::source` points at
/// a `UseItemIndex` instead of cloning what it needs out of it. `namespace`
/// is the one genuinely new fact this pass computes: the item only ever
/// stores its *unresolved* `path`, and resolving it to a namespace is this
/// whole pass's job.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct GlobImport {
	pub use_item: UseItemIndex,
	pub namespace: Namespace,
}

/// An import block's entry: the field of the block's module the host
/// provides its item as. Wasm allows one `module.field` to be imported as
/// several items, so the field is not an identity: the entry is keyed by the
/// item it declares.
pub struct ImportEntry {
	/// The string written before the item, or else the item's name, which
	/// then names it both in wx and to the host (as
	/// `ExportEntrySource::external_span` does for `export { run }`).
	pub field: Spanned<SymbolU32>,
	/// The entry as written, `"field":` included, in the block's file.
	pub span: TextSpan,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ImportDecl {
	/// Its row, in the table of the scope the block is written in, where
	/// its alias is bound.
	pub loc: ItemLoc,
	pub external_name: ast::Spanned<SymbolU32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub enum MemberKind {
	Function(FunctionIdx),
	Method(FunctionIdx),
	Constant(ConstIdx),
	AssociatedType(AssocTypeIdx),
}

impl MemberKind {
	/// Whether `other` is a member of the same kind: a function provides a
	/// function or a method declaration alike, since what makes one a method
	/// is its first parameter, which conformance compares.
	pub(super) fn same_kind(self, other: Self) -> bool {
		matches!(
			(self, other),
			(
				Self::Function(_) | Self::Method(_),
				Self::Function(_) | Self::Method(_)
			) | (Self::Constant(_), Self::Constant(_))
				| (Self::AssociatedType(_), Self::AssociatedType(_))
		)
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

/// A typed index of a declaration: reaches its row through its arena entry's
/// `loc`. An impl is not one (it has no row), so a signature query is not.
pub trait Declared: Copy {
	fn loc(self, decls: &Declarations) -> ItemLoc;
}

macro_rules! declared {
	($($index:ty => $arena:ident),* $(,)?) => {
		$(impl Declared for $index {
			fn loc(self, decls: &Declarations) -> ItemLoc {
				decls.$arena[usize::from(self)].loc
			}
		})*
	};
}

declared! {
	StructIdx => structs,
	EnumIdx => enums,
	TraitIdx => traits,
	TypesetIdx => typesets,
	TypeAliasIdx => type_aliases,
	FunctionIdx => functions,
	ConstIdx => constants,
	MemoryIdx => memories,
	GlobalIdx => globals,
	AssocTypeIdx => assoc_types,
}

impl Declared for PackageInstanceIdx {
	fn loc(self, decls: &Declarations) -> ItemLoc {
		decls.namespaces.package_instances()[usize::from(self)].loc
	}
}

impl Declared for MemberKind {
	fn loc(self, decls: &Declarations) -> ItemLoc {
		match self {
			Self::Function(index) | Self::Method(index) => index.loc(decls),
			Self::Constant(index) => index.loc(decls),
			Self::AssociatedType(index) => index.loc(decls),
		}
	}
}

/// Where a declaration is made: slot `decl_idx` of `namespace`'s table, the
/// row (`ItemDecl`) it addresses. A location, as rust-analyzer's `ItemLoc`
/// is, not an id assigned to the declaration.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct ItemLoc {
	pub(super) namespace: Namespace,
	pub(super) decl_idx: DeclIdx,
}

impl ItemLoc {
	#[inline]
	pub fn new(namespace: Namespace, decl_idx: DeclIdx) -> Self {
		Self {
			namespace,
			decl_idx,
		}
	}

	#[inline]
	pub fn source_span(self, namespaces: &Namespaces) -> SourceSpan {
		let symbols = namespaces.symbols(self.namespace);
		SourceSpan::new(
			symbols.file_id,
			symbols.items[usize::from(self.decl_idx)].name.span,
		)
	}

	#[inline]
	pub(super) fn symbol_kind(self, decls: &Declarations) -> DeclKind {
		decls.namespaces.kind(self)
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

impl Declarations {
	/// The declaration `loc` addresses, its row.
	pub fn item(&self, loc: ItemLoc) -> &ItemDecl {
		self.namespaces.item(loc)
	}

	/// The import block entry `loc` is declared in, when it is imported from
	/// the host.
	pub fn import_entry(&self, loc: ItemLoc) -> Option<&ImportEntry> {
		self.import_entries.get(&loc)
	}

	/// The scope `loc` is declared in, where the names its signature writes
	/// are looked up: its table's, or for an enum's variant, the enum's.
	pub fn scope(&self, loc: ItemLoc) -> Scope {
		match loc.namespace {
			Namespace::Package(package) => Scope::Package(package),
			Namespace::Module(module) => Scope::Module(module),
			Namespace::Import(import) => Scope::Import(import),
			Namespace::Enum(index) => {
				self.scope(self.enums[usize::from(index)].loc)
			}
		}
	}

	/// The file `loc` is declared in: its table's, since every namespace is
	/// written in one file.
	pub fn file_id(&self, loc: ItemLoc) -> FileId {
		self.namespaces.file_id(loc.namespace)
	}

	/// The name `index`'s declaration is written with, from its row.
	pub(super) fn name(&self, index: impl Declared) -> Spanned<SymbolU32> {
		self.item(index.loc(self)).name
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
		core_package: PackageId,
		root_package: PackageId,
	) -> (Self, Vec<AstEntry<'ast>>) {
		DeclarationsBuilder::build(
			packages,
			files,
			strings,
			diagnostics,
			resolutions,
			core_package,
			root_package,
		)
	}
}

impl Declarations {
	/// Where `loc` is declared: the span of its name.
	pub fn declaration_span(&self, loc: ItemLoc) -> SourceSpan {
		loc.source_span(&self.namespaces)
	}
}

impl<'ast, 'ctx> DeclarationsBuilder<'ast, 'ctx> {
	fn build(
		packages: &'ast [Package],
		files: &'ctx Files,
		strings: &'ctx mut ast::StringInterner,
		diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
		resolutions: &mut NameResolutions,
		core_package: PackageId,
		root_package: PackageId,
	) -> (Declarations, Vec<AstEntry<'ast>>) {
		let mut namespaces = Namespaces::default();
		for package in packages {
			debug_assert_eq!(
				namespaces.packages.len(),
				package.id.as_usize(),
				"packages are listed in `PackageId` order"
			);
			let root =
				ItemLoc::new(Namespace::Package(package.id), DeclIdx::SELF);
			let mut symbols = SymbolTable::new(
				package.modules[package.root.as_usize()].file_id,
			);
			// Generated: nobody writes it, so its name is `package` and its
			// span empty.
			symbols.items.push(ItemDecl::new(
				DeclKind::Package(package.id),
				Spanned {
					inner: Keyword::Package.symbol(),
					span: TextSpan::new(0, 0),
				},
				Visibility::Private,
			));
			for symbol in [
				ast::Keyword::SelfLower.symbol(),
				ast::Keyword::Package.symbol(),
			] {
				symbols.bindings.insert(
					BindingKey::ty(symbol),
					Binding::definition(root, Visibility::Public),
				);
			}

			// The core is implicit in every package but its own provider.
			// Every other dependency is named by a package instance, bound when
			// that item is scanned.
			if package.id != core_package {
				let core = strings.get_or_intern("core");
				symbols.bindings.insert(
					BindingKey::ty(core),
					Binding::definition(
						ItemLoc::new(
							Namespace::Package(core_package),
							DeclIdx::SELF,
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
			core_package,
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
			exports: FxHashMap::default(),
			import_entries: FxHashMap::default(),
			package_contracts: packages
				.iter()
				.map(|_| PackageContract::default())
				.collect(),
			intrinsics: IntrinsicDefs::default(),
			pending_named_imports: FxHashMap::default(),
			pending_glob_targets: FxHashMap::default(),
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

		let decls = Declarations {
			core_package,
			root_package,
			namespaces: builder.namespaces,
			file_namespaces,
			modules: builder.modules,
			imports: builder.imports,
			exports: builder.exports,
			import_entries: builder.import_entries,
			package_contracts: builder.package_contracts,
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

		(decls, builder.ast_nodes)
	}

	/// Records the entry `loc` is declared in: `span`, as written, and the
	/// field it is provided as, the string `written` or else `name`. A
	/// string that does not decode (which is reported) keeps its span, with
	/// `name` as its value.
	fn push_import_entry(
		&mut self,
		file_id: FileId,
		loc: ItemLoc,
		written: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		span: TextSpan,
	) {
		let field = match written {
			Some(written) => Spanned {
				inner: self
					.intern_string(file_id, written)
					.unwrap_or(name.inner),
				span: written,
			},
			None => name,
		};
		self.import_entries.insert(loc, ImportEntry { field, span });
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
						parent_namespace,
						source_module.file_id,
						declaration.name,
						declaration.pub_span,
					);
					if let Err(collision) = self.bind_child(
						parent_namespace,
						declaration.name.inner,
						self.modules[usize::from(module)].loc,
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
	fn push_trait(&mut self, item: TraitDecl) -> TraitIdx {
		let index = TraitIdx::new(u32::try_from(self.traits.len()).unwrap());
		self.traits.push(item);
		index
	}

	#[inline]
	fn push_trait_impl(&mut self, item: TraitImplDecl) -> TraitImplIdx {
		let index =
			TraitImplIdx::new(u32::try_from(self.trait_impls.len()).unwrap());
		self.trait_impls.push(item);
		index
	}

	/// A generated impl's associated type, `name`, and its row in
	/// `namespace`'s table: a member of the impl that the declaration whose
	/// name is at `generator` generates. It has no written name; its empty
	/// span, at the generator's, keeps it out of the name-to-definition
	/// table.
	fn push_generated_assoc_type(
		&mut self,
		namespace: Scope,
		name: SymbolU32,
		generator: TextSpan,
	) -> AssocTypeIdx {
		let index =
			AssocTypeIdx::new(u32::try_from(self.assoc_types.len()).unwrap());
		let name = Spanned {
			inner: name,
			span: TextSpan::new(generator.start, generator.start),
		};
		let loc = self.push_decl(
			namespace.into(),
			ItemDecl::new(
				DeclKind::AssocType(index),
				name,
				Visibility::Private,
			),
		);
		self.assoc_types.push(AssocTypeDecl { loc });
		index
	}

	/// Pre-allocates a memory declaration's synthetic `impl Memory for
	/// <memory>` — see `MemoryDecl`'s own doc comment for why this never
	/// needs `IntrinsicDefs::memory` to already be resolved.
	fn synthesize_memory_impl(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		name_span: TextSpan,
	) -> (TraitImplIdx, AssocTypeIdx) {
		let size_symbol = self.strings.get_or_intern("Size");
		let size_assoc_type_index =
			self.push_generated_assoc_type(namespace, size_symbol, name_span);
		let trait_impl_index = self.push_trait_impl(TraitImplDecl {
			file_id,
			namespace,
			members: vec![TraitMemberDecl {
				kind: MemberKind::AssociatedType(size_assoc_type_index),
				span: name_span,
			}],
			bindings: FxHashMap::from_iter([(
				BindingKey::ty(size_symbol),
				MemberIdx::new(0),
			)]),
		});
		(trait_impl_index, size_assoc_type_index)
	}

	/// Pre-allocates a global declaration's synthetic `impl Global for
	/// <global>` and, if `mutable`, the additional `impl GlobalMut for
	/// <global>` — see `GlobalDecl`'s own doc comment.
	fn synthesize_global_impl(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		name_span: TextSpan,
		mutable: bool,
	) -> (TraitImplIdx, AssocTypeIdx, Option<TraitImplIdx>) {
		let value_symbol = self.strings.get_or_intern("Value");
		let value_assoc_type_index =
			self.push_generated_assoc_type(namespace, value_symbol, name_span);
		let trait_impl_index = self.push_trait_impl(TraitImplDecl {
			file_id,
			namespace,
			members: vec![TraitMemberDecl {
				kind: MemberKind::AssociatedType(value_assoc_type_index),
				span: name_span,
			}],
			bindings: FxHashMap::from_iter([(
				BindingKey::ty(value_symbol),
				MemberIdx::new(0),
			)]),
		});
		// `GlobalMut` declares no members of its own (`func set` has a
		// default body reusing `Global::Value`) — an empty impl is enough
		// to make it a dispatch candidate.
		let mut_trait_impl_index = mutable.then(|| {
			self.push_trait_impl(TraitImplDecl {
				file_id,
				namespace,
				members: Vec::new(),
				bindings: FxHashMap::default(),
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
			self.push_generated_assoc_type(namespace, args_symbol, name_span);
		let result_assoc_type_index =
			self.push_generated_assoc_type(namespace, result_symbol, name_span);
		let call_impl_index = self.push_trait_impl(TraitImplDecl {
			file_id,
			namespace,
			members: vec![
				TraitMemberDecl {
					kind: MemberKind::AssociatedType(args_assoc_type_index),
					span: name_span,
				},
				TraitMemberDecl {
					kind: MemberKind::AssociatedType(result_assoc_type_index),
					span: name_span,
				},
			],
			bindings: FxHashMap::from_iter([
				(BindingKey::ty(args_symbol), MemberIdx::new(0)),
				(BindingKey::ty(result_symbol), MemberIdx::new(1)),
			]),
		});
		let function_impl_index = self.push_trait_impl(TraitImplDecl {
			file_id,
			namespace,
			members: Vec::new(),
			bindings: FxHashMap::default(),
		});
		FunctionImpls {
			call_impl_index,
			args_assoc_type_index,
			result_assoc_type_index,
			function_impl_index,
		}
	}

	/// Reads the attributes written on one item. An unknown name is ignored
	/// with a warning, since no attribute changes what a program means; a
	/// known one on the wrong item, or in the wrong form, is an error.
	fn scan_attributes(
		&mut self,
		file_id: FileId,
		target: AttributeTarget,
		attributes: &[ast::Attribute],
	) -> Attributes {
		let mut flags = Attributes::empty();
		let mut first: [Option<TextSpan>; KnownAttribute::ALL.len()] =
			[None; KnownAttribute::ALL.len()];
		for attribute in attributes {
			let name = self.strings.resolve(attribute.name.inner).unwrap();
			let Some(known) = KnownAttribute::from_name(name) else {
				self.diagnostics.push(report_unknown_attribute(
					file_id,
					attribute.name,
					name,
				));
				continue;
			};
			if known.target() != target {
				self.diagnostics.push(report_misplaced_attribute(
					file_id,
					attribute.name.span,
					known,
					target,
				));
				continue;
			}
			let has_arguments =
				matches!(attribute.value, ast::AttributeValue::Named(_));
			if known.takes_arguments() != has_arguments {
				self.diagnostics.push(report_malformed_attribute(
					file_id,
					attribute.name.span,
					known,
				));
				continue;
			}
			let slot = &mut first[known as usize];
			if let Some(first_span) = *slot {
				self.diagnostics.push(report_duplicate_attribute(
					file_id,
					attribute.name.span,
					first_span,
					known,
				));
				continue;
			}
			*slot = Some(attribute.name.span);
			flags.insert(known.flag());
		}
		flags
	}

	/// What a memory's `#[memory_limits]` says: the first one with an
	/// argument list (`scan_attributes` reports any other). An argument
	/// that says nothing (an unknown name, a name written twice, a value
	/// that is not a number) is reported (E2130) and left out.
	fn resolve_memory_limits(
		&mut self,
		file_id: FileId,
		attributes: &[ast::Attribute],
	) -> MemoryLimits {
		let mut limits = MemoryLimits::default();
		let Some(arguments) =
			attributes
				.iter()
				.find_map(|attribute| match &attribute.value {
					ast::AttributeValue::Named(arguments)
						if KnownAttribute::from_name(
							self.strings.resolve(attribute.name.inner).unwrap(),
						) == Some(KnownAttribute::MemoryLimits) =>
					{
						Some(arguments)
					}
					_ => None,
				})
		else {
			return limits;
		};
		let mut written = [None::<TextSpan>; 2];
		for argument in arguments.iter() {
			let argument = &argument.inner.inner;
			let name = self.strings.resolve(argument.name.inner).unwrap();
			let (slot, bound) = match name {
				"min_pages" => (0, &mut limits.min_pages),
				"max_pages" => (1, &mut limits.max_pages),
				_ => {
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::InvalidMemoryLimits.code(),
							)
							.with_message(format!(
								"`#[memory_limits]` has no argument `{name}`"
							))
							.with_label(
								SourceSpan::new(file_id, argument.name.span)
									.primary_label(),
							)
							.with_note(
								"its arguments are `min_pages` and `max_pages`",
							),
					);
					continue;
				}
			};
			if let Some(first) = written[slot] {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::InvalidMemoryLimits.code())
						.with_message(format!("`{name}` is written twice"))
						.with_label(
							SourceSpan::new(file_id, argument.name.span)
								.primary_label(),
						)
						.with_label(
							SourceSpan::new(file_id, first)
								.secondary_label()
								.with_message("first written here"),
						),
				);
				continue;
			}
			written[slot] = Some(argument.name.span);
			// A count of pages is an integer literal; the shorthand
			// `{ min_pages }` names nothing an attribute can read.
			match argument.value.as_deref() {
				Some(&Spanned {
					inner: ast::Expression::Int { value },
					span,
				}) => *bound = Some(Spanned { inner: value, span }),
				value => {
					let span = value.map_or(argument.name.span, |v| v.span);
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::InvalidMemoryLimits.code(),
							)
							.with_message(format!(
								"`{name}` must be a number of pages"
							))
							.with_label(
								SourceSpan::new(file_id, span)
									.primary_label()
									.with_message(
										"expected an integer literal",
									),
							),
					);
				}
			}
		}
		limits
	}

	#[inline]
	fn push_inherent_impl(
		&mut self,
		item: InherentImplDecl,
	) -> InherentImplIdx {
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
	fn push_use_item(&mut self, item: UseItemDecl) -> UseItemIndex {
		let index =
			UseItemIndex::new(u32::try_from(self.use_items.len()).unwrap());
		self.use_items.push(item);
		index
	}

	fn push_decl(
		&mut self,
		namespace: Namespace,
		definition: ItemDecl,
	) -> ItemLoc {
		let items = &mut self.namespaces.symbols_mut(namespace).items;
		let decl_idx = DeclIdx::new(u32::try_from(items.len()).unwrap());
		items.push(definition);
		ItemLoc::new(namespace, decl_idx)
	}

	/// Where `loc`'s name is written, for a collision's label.
	fn definition_span(&self, loc: ItemLoc) -> SourceSpan {
		loc.source_span(&self.namespaces)
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
		collision_key: ItemLoc,
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

	fn record_crate_member(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		name: Spanned<SymbolU32>,
		item: PackageMemberItem,
		keys: &[BindingKey],
	) {
		let package = self.namespaces.scope(namespace).package_id;
		let source = SourceSpan::new(file_id, name.span);
		let member = PackageMember {
			item,
			namespace,
			source,
		};
		let mut reported = Vec::new();
		for &key in keys {
			let previous = self.package_contracts[package.as_usize()]
				.members
				.get(&key)
				.copied();
			if let Some(previous) = previous {
				// The ordinary namespace already reports same-module collisions.
				// A function claims two keys, but one conflicting declaration
				// should receive only one package-level diagnostic.
				if previous.namespace != namespace
					&& !reported.contains(&previous.source)
				{
					self.diagnostics.push(
						DuplicateDefinitionDiagnostic {
							strings: self.strings,
							key,
							definitions: (previous.source, source),
						}
						.report(),
					);
					reported.push(previous.source);
				}
			} else {
				self.package_contracts[package.as_usize()]
					.members
					.insert(key, member);
			}
		}
	}

	/// Records a package instance, `package "key" as alias;`, and binds `alias` in its scope
	/// to the package the manifest declares under `key`. The binding is as
	/// visible as the item: private to the scope and everything inside it,
	/// or public with `pub`, which lets a downstream package name the
	/// dependency through this one.
	fn scan_package_instance(
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
		if package.is_none() {
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::UnknownPackage.code())
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

		let index = PackageInstanceIdx::new(
			u32::try_from(self.namespaces.package_instances.len()).unwrap(),
		);
		let visibility = Visibility::from(pub_span);
		let loc = self.push_decl(
			Namespace::from(namespace),
			ItemDecl::new(DeclKind::PackageInstance(index), alias, visibility),
		);
		self.namespaces.package_instances.push(PackageInstanceDecl {
			loc,
			package_name,
			package,
		});
		// An unknown key's instance has its row, but the alias binds no
		// declaration, so a path through it ends silently.
		let binding = if package.is_some() {
			Binding::definition(loc, visibility)
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

	/// The declaration that names `scope`: a module's or an import block's
	/// row, or a package's own entry.
	fn scope_key(&self, scope: Scope) -> ItemLoc {
		match scope {
			Scope::Package(package) => {
				ItemLoc::new(Namespace::Package(package), DeclIdx::SELF)
			}
			Scope::Module(module) => self.modules[usize::from(module)].loc,
			Scope::Import(import) => self.imports[usize::from(import)].loc,
		}
	}

	/// Pushes a module, its row in `parent`'s table and its scope, which
	/// binds `self` to the module, `package` to its package's root and
	/// `super` to the scope it was declared in.
	fn push_module(
		&mut self,
		parent: Scope,
		own_file: FileId,
		name: Spanned<SymbolU32>,
		pub_span: Option<TextSpan>,
	) -> ModuleIdx {
		let index = ModuleIdx::new(u32::try_from(self.modules.len()).unwrap());
		let package_id = self.namespaces.scope(parent).package_id;
		let loc = self.push_decl(
			parent.into(),
			ItemDecl::new(
				DeclKind::Module(index),
				name,
				Visibility::from(pub_span),
			),
		);
		let parent_key = self.scope_key(parent);
		self.modules.push(ModuleDecl { loc, own_file });
		self.namespaces.modules.push(ScopeTable::child(
			SymbolTable::new(own_file),
			loc,
			parent,
			parent_key,
			package_id,
		));
		index
	}

	/// Pushes an import block, its row in `parent`'s table and its own
	/// signature scope, with the same `self`, `package` and `super`
	/// qualifiers as a module.
	fn push_import(
		&mut self,
		parent: Scope,
		file_id: FileId,
		external_name: Spanned<SymbolU32>,
		internal_name: Spanned<SymbolU32>,
	) -> ImportIdx {
		let index = ImportIdx::new(u32::try_from(self.imports.len()).unwrap());
		let package_id = self.namespaces.scope(parent).package_id;
		let loc = self.push_decl(
			parent.into(),
			ItemDecl::new(
				DeclKind::Import(index),
				internal_name,
				Visibility::Private,
			),
		);
		let parent_key = self.scope_key(parent);
		self.imports.push(ImportDecl { loc, external_name });
		self.namespaces.imports.push(ScopeTable::child(
			SymbolTable::new(file_id),
			loc,
			parent,
			parent_key,
			package_id,
		));
		index
	}

	/// Binds a child namespace's name in the scope it was declared in, to the
	/// child's own entry. `Err` carries the definition already holding it.
	fn bind_child(
		&mut self,
		parent: Scope,
		name: SymbolU32,
		child: ItemLoc,
		visibility: Visibility,
	) -> Result<(), ItemLoc> {
		self.namespaces.try_insert_binding(
			parent.into(),
			BindingKey::ty(name),
			Binding::definition(child, visibility),
		)
	}
}

impl<'ast, 'ctx> DeclarationsBuilder<'ast, 'ctx> {
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
		let attributes = match AttributeTarget::of_item(item) {
			Some((target, attributes)) => {
				self.scan_attributes(file_id, target, attributes)
			}
			None => Attributes::empty(),
		};
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
			}
			| ast::Item::PackageFunction {
				signature,
				pub_span,
				..
			} => {
				let func_index = FunctionIdx::new(
					u32::try_from(self.functions.len()).unwrap(),
				);
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Function(func_index),
						signature.name,
						Visibility::from(*pub_span),
					),
				);
				// A function is a value and, like a struct, its own type: each
				// one is a zero-sized type of its own (`foo<i32>`).
				let binding =
					Binding::definition(loc, Visibility::from(*pub_span));
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
				self.functions.push(FunctionDecl {
					loc,
					owner: MemberOwner::Free,
					params,
					function_impls,
					attributes,
				});
				if matches!(item, ast::Item::PackageFunction { .. }) {
					self.record_crate_member(
						file_id,
						namespace,
						signature.name,
						PackageMemberItem::Function(func_index),
						&[
							BindingKey::ty(signature.name.inner),
							BindingKey::value(signature.name.inner),
						],
					);
				}
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
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Global(global_index),
						*name,
						Visibility::from(*pub_span),
					),
				);
				self.globals.push(GlobalDecl {
					loc,
					trait_impl_index,
					value_assoc_type_index,
					mut_trait_impl_index,
				});
				// The name is the global's zero-sized value and its own
				// type, the one `Global` is implemented for.
				let binding =
					Binding::definition(loc, Visibility::from(*pub_span));
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
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Struct(struct_index),
						*name,
						Visibility::from(*pub_span),
					),
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
					Binding::definition(loc, Visibility::from(*pub_span)),
					Binding::definition(loc, constructor_visibility),
					name.span,
				);

				let mut field_names: Vec<Option<Spanned<SymbolU32>>> =
					Vec::with_capacity(fields.len());
				let mut field_pub_spans = Vec::with_capacity(fields.len());
				let mut lookup: FxHashMap<SymbolU32, FieldIdx> =
					FxHashMap::default();
				for field in fields.iter().map(|f| &f.inner.inner) {
					let index = FieldIdx::new(
						u32::try_from(field_names.len()).unwrap(),
					);
					// A duplicate name keeps its slot (positions still match
					// the declaration) but is unreachable by name.
					let name = field.binding.and_then(ast::Binding::name);
					if let Some(name) = name {
						if name.inner == Keyword::SelfLower.symbol() {
							self.diagnostics
								.push(report_self_field(file_id, name.span));
						}
						if let Some(&first_index) = lookup.get(&name.inner) {
							let first_name = field_names
								[usize::from(first_index)]
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
					field_names.push(name);
					field_pub_spans.push(field.pub_span);
				}

				if self.namespaces.scope(namespace).package_id
					== self.core_package
					&& self.strings.resolve(name.inner) == Some("Char")
				{
					self.intrinsics.char = Some(struct_index);
				}
				self.structs.push(StructDecl {
					loc,
					field_names: field_names.into_boxed_slice(),
					field_pub_spans: field_pub_spans.into_boxed_slice(),
					lookup,
					order: if attributes.contains(Attributes::FIXED_ORDER) {
						FieldOrder::Fixed
					} else {
						FieldOrder::Optimal
					},
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
				entries,
				..
			} => {
				// The variants among the entries, in written order, and the
				// first `..`.
				let variants: Vec<&ast::EnumVariant> = entries
					.iter()
					.filter_map(|entry| match &entry.inner.inner {
						ast::EnumEntry::Variant(variant) => Some(variant),
						ast::EnumEntry::Rest => None,
					})
					.collect();
				let open = entries.iter().find_map(|entry| {
					matches!(entry.inner.inner, ast::EnumEntry::Rest)
						.then_some(entry.inner.span)
				});
				let enum_index =
					EnumIdx::new(u32::try_from(self.enums.len()).unwrap());
				let own_namespace = Namespace::Enum(enum_index);
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Enum(enum_index),
						*name,
						Visibility::from(*pub_span),
					),
				);
				self.namespaces.enums.push(SymbolTable::new(file_id));
				// Each variant's row, in the enum's own table.
				let first_variant =
					ConstIdx::new(u32::try_from(self.constants.len()).unwrap());
				let mut variant_locs = Vec::with_capacity(variants.len());
				for (offset, variant) in variants.iter().enumerate() {
					let const_index = ConstIdx::new(
						u32::from(first_variant)
							+ u32::try_from(offset).unwrap(),
					);
					variant_locs.push(self.push_decl(
						own_namespace,
						ItemDecl::new(
							DeclKind::EnumVariant(const_index),
							variant.name,
							Visibility::Private,
						),
					));
				}
				// All of the enum's variants in one `extend`, which is what keeps
				// `EnumDecl::variants` contiguous.
				self.constants.extend(variant_locs.iter().map(|&loc| {
					ConstDecl {
						loc,
						owner: MemberOwner::Free,
					}
				}));
				let end_variant =
					ConstIdx::new(u32::try_from(self.constants.len()).unwrap());
				if self.namespaces.scope(namespace).package_id
					== self.core_package
					&& self.strings.resolve(name.inner) == Some("Bool")
				{
					self.intrinsics.bool = Some(enum_index);
				}
				self.enums.push(EnumDecl {
					loc,
					variants: first_variant..end_variant,
					open,
				});
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(loc, Visibility::from(*pub_span)),
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::Enum { enum_index, item },
				});

				// A variant's written value is read in the scope around the
				// enum, like any constant's initializer.
				for (offset, (&variant, variant_key)) in
					variants.iter().zip(variant_locs).enumerate()
				{
					let const_index = ConstIdx::new(
						u32::from(first_variant)
							+ u32::try_from(offset).unwrap(),
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
			ast::Item::TypeAlias { pub_span, name, .. }
			| ast::Item::PackageType { pub_span, name, .. } => {
				let bodyless = match item {
					ast::Item::TypeAlias { body, .. } => body.is_none(),
					ast::Item::PackageType { .. } => true,
					_ => unreachable!(),
				};
				let type_alias_index = TypeAliasIdx::new(
					u32::try_from(self.type_aliases.len()).unwrap(),
				);
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::TypeAlias(type_alias_index),
						*name,
						Visibility::from(*pub_span),
					),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(loc, Visibility::from(*pub_span)),
					name.span,
				);
				if bodyless
					&& self.namespaces.scope(namespace).package_id
						== self.core_package
				{
					if let Some(name_str) = self.strings.resolve(name.inner) {
						if let Some(slot) =
							self.intrinsics.type_slot_mut(name_str)
						{
							*slot = Some(type_alias_index);
						}
					}
				}
				self.type_aliases.push(TypeAliasDecl { loc });
				if matches!(item, ast::Item::PackageType { .. }) {
					self.record_crate_member(
						file_id,
						namespace,
						*name,
						PackageMemberItem::Type(type_alias_index),
						&[BindingKey::ty(name.inner)],
					);
				}
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::TypeAlias {
						item,
						type_alias_index,
					},
				});
			}
			ast::Item::Memory {
				pub_span,
				name,
				attributes: written,
				..
			} => {
				let memory_index =
					MemoryIdx::new(u32::try_from(self.memories.len()).unwrap());
				let (trait_impl_index, size_assoc_type_index) =
					self.synthesize_memory_impl(file_id, namespace, name.span);
				let limits = self.resolve_memory_limits(file_id, written);
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Memory(memory_index),
						*name,
						Visibility::from(*pub_span),
					),
				);
				self.memories.push(MemoryDecl {
					loc,
					trait_impl_index,
					size_assoc_type_index,
					limits,
				});
				let binding =
					Binding::definition(loc, Visibility::from(*pub_span));
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
			ast::Item::Const { pub_span, name, .. }
			| ast::Item::PackageConst { pub_span, name, .. } => {
				let const_index =
					ConstIdx::new(u32::try_from(self.constants.len()).unwrap());
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Const(const_index),
						*name,
						Visibility::from(*pub_span),
					),
				);
				self.constants.push(ConstDecl {
					loc,
					owner: MemberOwner::Free,
				});
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::value(name.inner),
					Binding::definition(loc, Visibility::from(*pub_span)),
					name.span,
				);
				if matches!(item, ast::Item::PackageConst { .. }) {
					self.record_crate_member(
						file_id,
						namespace,
						*name,
						PackageMemberItem::Constant(const_index),
						&[BindingKey::value(name.inner)],
					);
				}
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
				let module =
					self.push_module(namespace, file_id, *name, *pub_span);
				if let Err(collision) = self.bind_child(
					namespace,
					name.inner,
					self.modules[usize::from(module)].loc,
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
			// namespace (and its row) directly from vfs's
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
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Trait(trait_index),
						*name,
						Visibility::from(*pub_span),
					),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(loc, Visibility::from(*pub_span)),
					name.span,
				);
				if self.namespaces.scope(namespace).package_id
					== self.core_package
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

				let mut members: Vec<TraitMemberDecl> = Vec::new();
				let mut bindings: FxHashMap<BindingKey, MemberIdx> =
					FxHashMap::default();
				for item in items.iter() {
					let member_index =
						MemberIdx::new(u32::try_from(members.len()).unwrap());
					let (target, attributes) =
						AttributeTarget::of_trait_item(&item.inner.inner);
					let attributes =
						self.scan_attributes(file_id, target, attributes);
					let (member, key) = match &item.inner.inner {
						ast::TraitItem::Function { signature, .. } => {
							let params = self.scan_impl_function_params(
								file_id,
								&signature.params,
							);
							let is_method = params.first().is_some_and(|p| {
								p.is_some_and(|p| {
									p.inner == Keyword::SelfLower.symbol()
								})
							});
							let function_impls = self
								.synthesize_function_impls(
									file_id,
									namespace,
									signature.name.span,
								);
							let function_index = FunctionIdx::new(
								u32::try_from(self.functions.len()).unwrap(),
							);
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::Function(function_index),
									signature.name,
									Visibility::Private,
								),
							);
							self.functions.push(FunctionDecl {
								loc,
								owner: MemberOwner::Trait(trait_index),
								params,
								function_impls,
								attributes,
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
								TraitMemberDecl {
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
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::Const(const_index),
									*name,
									Visibility::Private,
								),
							);
							self.constants.push(ConstDecl {
								loc,
								owner: MemberOwner::Trait(trait_index),
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
								TraitMemberDecl {
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
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::AssocType(assoc_type_index),
									*name,
									Visibility::Private,
								),
							);
							self.assoc_types.push(AssocTypeDecl { loc });
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
								TraitMemberDecl {
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

				// A name never interned is no member's.
				let member = |key: fn(SymbolU32) -> BindingKey, name: &str| {
					let key = key(self.strings.get(name)?);
					Some(members[usize::from(*bindings.get(&key)?)].kind)
				};
				let declared = |name: &str| match member(BindingKey::ty, name) {
					Some(MemberKind::AssociatedType(assoc)) => Some(assoc),
					_ => None,
				};
				let this = Some(trait_index);
				if self.intrinsics.call == this {
					self.intrinsics.call_args = declared("Args");
					self.intrinsics.call_result = declared("Result");
				} else if self.intrinsics.stack_value == this {
					self.intrinsics.stack_value_repr = declared("Repr");
				} else if self.intrinsics.memory == this {
					self.intrinsics.memory_size = declared("Size");
					self.intrinsics.memory_data_end =
						match member(BindingKey::value, "DATA_END") {
							Some(MemberKind::Constant(constant)) => {
								Some(constant)
							}
							_ => None,
						};
				} else if self.intrinsics.slice == this {
					self.intrinsics.slice_value = declared("Value");
					let function =
						|name: &str| match member(BindingKey::value, name) {
							Some(
								MemberKind::Function(function)
								| MemberKind::Method(function),
							) => Some(function),
							_ => None,
						};
					self.intrinsics.slice_len = function("len");
					self.intrinsics.slice_as_ref = function("as_ref");
				} else if self.intrinsics.pointer == this {
					self.intrinsics.pointer_memory = declared("Memory");
					self.intrinsics.pointer_pointee = declared("Pointee");
					self.intrinsics.pointer_metadata = declared("Metadata");
				} else if self.intrinsics.array == this {
					self.intrinsics.array_len =
						match member(BindingKey::value, "LEN") {
							Some(MemberKind::Constant(constant)) => {
								Some(constant)
							}
							_ => None,
						};
				}
				let actual_index = self.push_trait(TraitDecl {
					loc,
					typeset: None,
					bindings,
					members,
				});
				debug_assert_eq!(trait_index, actual_index);
			}
			ast::Item::InherentImpl { items, .. } => {
				let mut members: Vec<InherentMemberDecl> = Vec::new();
				let mut bindings: FxHashMap<BindingKey, MemberIdx> =
					FxHashMap::default();
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
					let (target, attributes) =
						AttributeTarget::of_impl_item(&impl_item.inner.inner);
					let attributes =
						self.scan_attributes(file_id, target, attributes);
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
								p.is_some_and(|p| {
									p.inner == Keyword::SelfLower.symbol()
								})
							});
							let function_impls = self
								.synthesize_function_impls(
									file_id,
									namespace,
									signature.name.span,
								);
							let function_index = FunctionIdx::new(
								u32::try_from(self.functions.len()).unwrap(),
							);
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::Function(function_index),
									signature.name,
									Visibility::from(*pub_span),
								),
							);
							self.functions.push(FunctionDecl {
								loc,
								owner: MemberOwner::InherentImpl(block_index),
								params,
								function_impls,
								attributes,
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
								InherentMemberDecl {
									kind: if is_method {
										MemberKind::Method(function_index)
									} else {
										MemberKind::Function(function_index)
									},
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
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::Const(const_index),
									*name,
									Visibility::from(*pub_span),
								),
							);
							self.constants.push(ConstDecl {
								loc,
								owner: MemberOwner::InherentImpl(block_index),
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
								InherentMemberDecl {
									kind: MemberKind::Constant(const_index),
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

				let actual_index = self.push_inherent_impl(InherentImplDecl {
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
					namespace,
					file_id,
					external_name,
					internal_name,
				);
				let own_namespace = Namespace::Import(import);
				if let Err(collision) = self.bind_child(
					namespace,
					internal_name.inner,
					self.imports[usize::from(import)].loc,
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

				// Imported declarations are written inside the block: resolve
				// their signatures (and synthetic impls) in its sibling scope.
				let namespace = Scope::Import(import);
				for item in items.inner.iter() {
					let (import_block, external_name) = match &item.inner.inner
					{
						ast::ImportEntry::Use { tree, pub_span } => {
							self.scan_use_tree(
								namespace, tree, None, *pub_span,
							);
							continue;
						}
						ast::ImportEntry::Declaration {
							declaration,
							external_name,
						} => (declaration, *external_name),
					};
					match import_block {
						ast::ImportDeclaration::Memory { name, .. } => {
							let memory_index = MemoryIdx::new(
								u32::try_from(self.memories.len()).unwrap(),
							);
							let (trait_impl_index, size_assoc_type_index) =
								self.synthesize_memory_impl(
									file_id, namespace, name.span,
								);
							let loc = self.push_decl(
								own_namespace,
								ItemDecl::new(
									DeclKind::Memory(memory_index),
									*name,
									Visibility::Private,
								),
							);
							self.push_import_entry(
								file_id,
								loc,
								external_name,
								*name,
								item.inner.span,
							);
							self.memories.push(MemoryDecl {
								loc,
								trait_impl_index,
								size_assoc_type_index,
								limits: MemoryLimits::default(),
							});
							let binding =
								Binding::definition(loc, Visibility::Public);
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
									import_block,
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
							let function_index = FunctionIdx::new(
								u32::try_from(self.functions.len()).unwrap(),
							);
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::Function(function_index),
									signature.name,
									Visibility::Private,
								),
							);
							self.functions.push(FunctionDecl {
								loc,
								owner: MemberOwner::Free,
								params,
								function_impls,
								attributes: Attributes::empty(),
							});
							self.push_import_entry(
								file_id,
								loc,
								external_name,
								signature.name,
								item.inner.span,
							);
							let binding =
								Binding::definition(loc, Visibility::Public);
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
									import_block,
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
							let loc = self.push_decl(
								own_namespace,
								ItemDecl::new(
									DeclKind::Global(global_index),
									*name,
									Visibility::Private,
								),
							);
							self.globals.push(GlobalDecl {
								loc,
								trait_impl_index,
								value_assoc_type_index,
								mut_trait_impl_index,
							});
							self.push_import_entry(
								file_id,
								loc,
								external_name,
								*name,
								item.inner.span,
							);
							let binding =
								Binding::definition(loc, Visibility::Public);
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
									import_block,
								},
							});
						}
					}
				}
			}
			ast::Item::Use { tree, pub_span } => {
				self.scan_use_tree(namespace, tree, None, *pub_span);
			}
			ast::Item::PackageInstance {
				pub_span,
				package,
				alias,
			} => {
				self.scan_package_instance(
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
				if self.namespaces.scope(namespace).package_id
					== self.core_package
				{
					if let Some(name_str) = self.strings.resolve(name.inner) {
						if let Some(slot) =
							self.intrinsics.typeset_slot_mut(name_str)
						{
							*slot = Some(typeset_index);
						}
					}
				}
				let loc = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::TypeSet(typeset_index),
						*name,
						Visibility::from(*pub_span),
					),
				);
				self.insert_binding(
					Namespace::from(namespace),
					BindingKey::ty(name.inner),
					Binding::definition(loc, Visibility::from(*pub_span)),
					name.span,
				);
				// Its trait is generated: a row of its own, with the typeset's
				// name and visibility and an empty span at the typeset's name.
				let trait_index =
					TraitIdx(u32::try_from(self.traits.len()).unwrap());
				let trait_decl = self.push_decl(
					Namespace::from(namespace),
					ItemDecl::new(
						DeclKind::Trait(trait_index),
						Spanned {
							inner: name.inner,
							span: TextSpan::new(
								name.span.start,
								name.span.start,
							),
						},
						Visibility::from(*pub_span),
					),
				);
				let actual_index = self.push_trait(TraitDecl {
					loc: trait_decl,
					typeset: Some(typeset_index),
					bindings: FxHashMap::default(),
					members: Vec::new(),
				});
				let member_impls: Box<[TraitImplIdx]> = members
					.iter()
					.map(|_| {
						self.push_trait_impl(TraitImplDecl {
							file_id,
							namespace,
							members: Vec::new(),
							bindings: FxHashMap::default(),
						})
					})
					.collect();
				debug_assert_eq!(trait_index, actual_index);
				self.typesets.push(TypesetDecl {
					loc,
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
				let mut members: Vec<TraitMemberDecl> = Vec::new();
				let mut bindings: FxHashMap<BindingKey, MemberIdx> =
					FxHashMap::default();
				// Reserved before the members, whose synthetic impls (each
				// function's `Call` and `Function`) take slots after it.
				let block_index = self.push_trait_impl(TraitImplDecl {
					file_id,
					namespace,
					members: Vec::new(),
					bindings: FxHashMap::default(),
				});
				self.ast_nodes.push(AstEntry {
					file_id,
					namespace,
					node: AstNodeRef::TraitImplBlock { item, block_index },
				});
				for item in items.iter() {
					let member_index =
						MemberIdx::new(u32::try_from(members.len()).unwrap());
					let (target, attributes) =
						AttributeTarget::of_impl_item(&item.inner.inner);
					let attributes =
						self.scan_attributes(file_id, target, attributes);
					let (member, key) = match &item.inner.inner {
						ast::ImplItem::Function { signature, .. } => {
							let params = self.scan_impl_function_params(
								file_id,
								&signature.params,
							);
							let is_method = params.first().is_some_and(|p| {
								p.is_some_and(|p| {
									p.inner == Keyword::SelfLower.symbol()
								})
							});
							let function_impls = self
								.synthesize_function_impls(
									file_id,
									namespace,
									signature.name.span,
								);
							let function_index = FunctionIdx::new(
								u32::try_from(self.functions.len()).unwrap(),
							);
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::Function(function_index),
									signature.name,
									Visibility::Private,
								),
							);
							self.functions.push(FunctionDecl {
								loc,
								owner: MemberOwner::TraitImpl(block_index),
								params,
								function_impls,
								attributes,
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
								TraitMemberDecl {
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
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::Const(const_index),
									*name,
									Visibility::Private,
								),
							);
							self.constants.push(ConstDecl {
								loc,
								owner: MemberOwner::TraitImpl(block_index),
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
								TraitMemberDecl {
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
							let loc = self.push_decl(
								Namespace::from(namespace),
								ItemDecl::new(
									DeclKind::AssocType(assoc_type_index),
									*name,
									Visibility::Private,
								),
							);
							self.assoc_types.push(AssocTypeDecl { loc });
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
								TraitMemberDecl {
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

				self.trait_impls[usize::from(block_index)] = TraitImplDecl {
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
				let item_index = self.push_use_item(UseItemDecl {
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
				let item_index = self.push_use_item(UseItemDecl {
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
	) -> Box<[Option<Spanned<SymbolU32>>]> {
		let names = self.scan_param_names(file_id, params);
		for name in names.iter().flatten() {
			if name.inner == Keyword::SelfLower.symbol() {
				self.diagnostics
					.push(report_self_param_position(file_id, name.span));
			}
		}
		names
	}

	/// Validates a trait/impl function's parameter list: every name unique,
	/// `self` (if present) only as the very first parameter. Whether `self`
	/// is actually present — i.e. whether this member is
	/// `MemberKind::Method` or `MemberKind::Function` — is for the caller
	/// to read straight off `params.first()` against
	/// `Keyword::SelfLower.symbol()`, same constant-time check this uses;
	/// nothing here needs to hand that fact back out.
	fn scan_impl_function_params(
		&mut self,
		file_id: FileId,
		params: &[ast::Separated<Spanned<ast::FunctionParam>>],
	) -> Box<[Option<Spanned<SymbolU32>>]> {
		let names = self.scan_param_names(file_id, params);
		for (index, name) in names.iter().enumerate() {
			if let Some(name) = name
				&& name.inner == Keyword::SelfLower.symbol()
				&& index != 0
			{
				self.diagnostics
					.push(report_self_param_position(file_id, name.span));
			}
		}
		names
	}

	/// Each parameter's name, `None` for an unnamed one, reporting a name
	/// bound twice. Unnamed parameters never clash.
	fn scan_param_names(
		&mut self,
		file_id: FileId,
		params: &[ast::Separated<Spanned<ast::FunctionParam>>],
	) -> Box<[Option<Spanned<SymbolU32>>]> {
		let mut names: Vec<Option<Spanned<SymbolU32>>> =
			Vec::with_capacity(params.len());
		for param in params.iter().map(|param| &param.inner.inner) {
			let name = param.binding.and_then(ast::Binding::name);
			if let Some(name) = name
				&& let Some(&first) =
					names.iter().flatten().find(|s| s.inner == name.inner)
			{
				self.diagnostics.push(report_duplicate_function_parameter(
					self.strings,
					file_id,
					name,
					first,
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

fn report_unknown_attribute(
	file_id: FileId,
	name: Spanned<SymbolU32>,
	text: &str,
) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::UnknownAttribute.code())
		.with_message(format!("unknown attribute `{text}`"))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("ignored"),
		)
}

fn report_misplaced_attribute(
	file_id: FileId,
	span: TextSpan,
	attribute: KnownAttribute,
	target: AttributeTarget,
) -> Diagnostic<FileId> {
	let name = attribute.name();
	Diagnostic::error()
		.with_code(DiagnosticCode::MisplacedAttribute.code())
		.with_message(format!(
			"`#[{name}]` cannot be written on {}",
			target.description()
		))
		.with_label(SourceSpan::new(file_id, span).primary_label())
		.with_note(format!(
			"`#[{name}]` applies only to {}",
			attribute.target().description()
		))
}

fn report_malformed_attribute(
	file_id: FileId,
	span: TextSpan,
	attribute: KnownAttribute,
) -> Diagnostic<FileId> {
	let name = attribute.name();
	let (message, form) = if attribute.takes_arguments() {
		(
			format!("`#[{name}]` takes arguments"),
			format!("#[{name}({{ .. }})]"),
		)
	} else {
		(
			format!("`#[{name}]` takes no arguments"),
			format!("#[{name}]"),
		)
	};
	Diagnostic::error()
		.with_code(DiagnosticCode::MalformedAttribute.code())
		.with_message(message)
		.with_label(SourceSpan::new(file_id, span).primary_label())
		.with_note(format!("write it as `{form}`"))
}

fn report_duplicate_attribute(
	file_id: FileId,
	span: TextSpan,
	first: TextSpan,
	attribute: KnownAttribute,
) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::DuplicateAttribute.code())
		.with_message(format!("`#[{}]` is written twice", attribute.name()))
		.with_label(
			SourceSpan::new(file_id, span)
				.primary_label()
				.with_message("redundant"),
		)
		.with_label(
			SourceSpan::new(file_id, first)
				.secondary_label()
				.with_message("first written here"),
		)
}

fn report_self_field(file_id: FileId, span: TextSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ReservedIdentifier.code())
		.with_message("a field cannot be named `self`")
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

	#[test]
	fn crate_contract_records_binding_tiers_across_modules() {
		let case = TestCase::new(indoc! {"
			mod first {
				pub package type Shared;
				pub package func compute(x: i32) -> i32;
			}
			mod second {
				package const Shared: i32;
			}
		"});
		case.diagnostics().assert_none();
		let contract =
			&case.decls.package_contracts[case.graph.root_package.as_usize()];
		let shared = case.strings.get("Shared").unwrap();
		let compute = case.strings.get("compute").unwrap();
		assert!(matches!(
			contract.members[&BindingKey::ty(shared)].item,
			PackageMemberItem::Type(_)
		));
		assert!(matches!(
			contract.members[&BindingKey::value(shared)].item,
			PackageMemberItem::Constant(_)
		));
		let ty = contract.members[&BindingKey::ty(compute)];
		let value = contract.members[&BindingKey::value(compute)];
		assert!(matches!(ty.item, PackageMemberItem::Function(_)));
		assert_eq!(ty.source, value.source);
	}

	#[test]
	fn crate_contract_rejects_duplicate_keys_in_different_modules() {
		let case = TestCase::new(indoc! {"
			mod first { package type Shared; }
			mod second { package type Shared; }
		"});
		let duplicates: Vec<_> = case
			.diagnostics
			.iter()
			.filter(|diagnostic| {
				diagnostic.code.as_deref()
					== Some(DiagnosticCode::DuplicateDefinition.code())
			})
			.collect();
		assert_eq!(duplicates.len(), 1);
		assert_eq!(duplicates[0].labels.len(), 2);
	}

	struct TestCase {
		graph: vfs::CompilationUnit,
		strings: StringInterner,
		decls: Declarations,
		diagnostics: Vec<Diagnostic<FileId>>,
	}

	/// The written trait impl declaring `member`, among the synthetic impls
	/// every function brings.
	fn written_trait_impl<'a>(
		case: &'a TestCase,
		member: &str,
	) -> &'a TraitImplDecl {
		let key = BindingKey::value(case.strings.get(member).unwrap());
		case.decls
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
				.decls
				.namespaces
				.entered_by(key)
				.expect("expected a namespace")
		}

		fn expect_success(&self) -> DeclKind {
			self.diagnostics().assert_none();
			let BindingTarget::Accessible(key) = self.target else {
				panic!(
					"expected an accessible definition, got {:?}",
					self.target
				);
			};
			key.symbol_kind(&self.case.decls)
		}
	}

	impl TestCase {
		fn from_graph(
			graph: vfs::CompilationUnit,
			mut strings: StringInterner,
		) -> Self {
			let parser_diagnostics = graph.collect_parser_diagnostics();
			DiagnosticView::new("parse", &parser_diagnostics, &graph.files)
				.assert_no_errors();
			let linker_diagnostics = graph.collect_linker_diagnostics();
			DiagnosticView::new("link", &linker_diagnostics, &graph.files)
				.assert_no_errors();

			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (decls, ast_nodes) = Declarations::build(
				&graph.packages,
				&graph.files,
				&mut strings,
				&mut diagnostics,
				&mut resolutions,
				graph.core_package,
				graph.root_package,
			);
			// Only Phase 1 (this file) is under test here — `ast_nodes` is
			// Phase 2's input, and dropping it now is what lets `decls` (and
			// `graph`, moved below) outlive this constructor with no
			// lingering borrow between them.
			drop(ast_nodes);

			TestCase {
				graph,
				strings,
				decls,
				diagnostics,
			}
		}

		fn new(source: &str) -> Self {
			let mut strings = Keyword::create_interner();
			let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
			builder.load_core();
			let root_id = builder
				.load_package(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)])),
				)
				.unwrap();
			Self::from_graph(builder.build(root_id), strings)
		}

		fn new_workspace(
			entry_path: vfs::AbsolutePath,
			workspace: HashMap<vfs::AbsolutePath, String>,
		) -> Self {
			let mut strings = Keyword::create_interner();
			let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
			builder.load_core();
			let root_id = builder
				.load_package(
					entry_path,
					&vfs::VirtualFileSource::new(workspace),
				)
				.unwrap();
			Self::from_graph(builder.build(root_id), strings)
		}

		/// A `"type": "core"` root — no embedded core loaded, so `source`
		/// is the *entire* package graph, and `core_package == root_package`.
		/// For tests that need to control every `#[intrinsic]` declaration
		/// themselves rather than asserting against the real, separately
		/// evolving `core/main.wx`.
		fn new_core(source: &str) -> Self {
			let mut strings = Keyword::create_interner();
			let workspace = vfs::VirtualFileSource::new(HashMap::from([
				(
					vfs::AbsolutePath::new("/core/wx.json"),
					r#"{ "type": "core", "entry": "main.wx" }"#.to_string(),
				),
				(vfs::AbsolutePath::new("/core/main.wx"), source.to_string()),
			]));
			let graph = vfs::open_manifest(
				vfs::AbsolutePath::new("/core"),
				&workspace,
				&mut strings,
			)
			.unwrap();
			Self::from_graph(graph, strings)
		}

		fn root_namespace(&self) -> Scope {
			Scope::Package(self.decls.root_package)
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
			let file_id = self.decls.namespaces.file_id(namespace.into());
			let segments: Box<[ast::PathSegment]> = path
				.split("::")
				.map(|segment| ast::PathSegment {
					ident: Spanned {
						inner: self.strings.get_or_intern(segment),
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
				&self.strings,
				&self.decls,
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
			DeclKind::Function(_)
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
		let package = &case.graph.packages[case.decls.root_package.as_usize()];
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
		assert!(matches!(key.symbol_kind(&case.decls), DeclKind::Struct(_)));
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
	fn core_primitive_slots_reference_the_matching_aliases() {
		let case = TestCase::new_core(indoc! {"
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
			type funcref;
			enum Bool(u8) { False = 0, True = 1 }
			struct Char(value: u32);
		"});
		case.diagnostics().assert_none();

		let intrinsics = &case.decls.intrinsics;
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
			(intrinsics.funcref, "funcref"),
		] {
			let index = slot.unwrap_or_else(|| {
				panic!("missing intrinsic `{expected_name}`")
			});
			let name = case.decls.name(index).inner;
			assert_eq!(case.strings.resolve(name), Some(expected_name));
		}
		let bool = intrinsics.bool.expect("`Bool` is recorded");
		let name = case.decls.name(bool).inner;
		assert_eq!(case.strings.resolve(name), Some("Bool"));
		let char = intrinsics.char.expect("`Char` is recorded");
		let name = case.decls.name(char).inner;
		assert_eq!(case.strings.resolve(name), Some("Char"));
	}

	#[test]
	fn core_operator_slots_reference_the_matching_traits() {
		let case = TestCase::new_core(indoc! {"
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
			trait Eq {}
		"});
		case.diagnostics().assert_none();

		let intrinsics = &case.decls.intrinsics;
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
			(intrinsics.eq, "Eq"),
		] {
			let index = slot.unwrap_or_else(|| {
				panic!("missing intrinsic `{expected_name}`")
			});
			let name = case.decls.name(index).inner;
			assert_eq!(case.strings.resolve(name), Some(expected_name));
		}
	}

	#[test]
	fn core_integer_typeset_is_recorded() {
		let case = TestCase::new_core(indoc! {"
			type u8;
			typeset Integer { u8 }
		"});
		case.diagnostics().assert_none();
		let integer = case
			.decls
			.intrinsics
			.integer
			.expect("`Integer` is recorded");
		let name = case.decls.name(integer).inner;
		assert_eq!(case.strings.resolve(name), Some("Integer"));
	}

	#[test]
	fn core_missing_an_intrinsic_leaves_its_slot_empty() {
		let case = TestCase::new_core(indoc! {"
			type u8;
		"});
		case.diagnostics().assert_none();
		assert!(case.decls.intrinsics.u8.is_some());
		assert!(case.decls.intrinsics.char.is_none());
		assert!(case.decls.intrinsics.add.is_none());
		assert!(case.decls.intrinsics.eq.is_none());
		assert!(case.decls.intrinsics.integer.is_none());
	}

	#[test]
	fn reserved_name_outside_core_is_not_recorded_as_intrinsic() {
		let case = TestCase::new(indoc! {"
			type u8;
		"});
		case.diagnostics().assert_none();

		// The real core's own `u8` must still be the one on record — the
		// same-named declaration in the binary package must not clobber it,
		// and (since it isn't in the core package) must not be recorded
		// as an intrinsic at all.
		let root_namespace = case.root_namespace();
		let core_namespace = Scope::Package(case.graph.core_package);
		assert_ne!(
			root_namespace, core_namespace,
			"the binary package must not be the core package"
		);
		let u8_index =
			case.decls.intrinsics.u8.expect("u8 should still resolve");
		assert_eq!(
			case.decls
				.scope(case.decls.type_aliases[usize::from(u8_index)].loc),
			core_namespace,
			"u8 must still point into the core package, not the binary one"
		);
	}

	#[test]
	fn type_and_trait_intrinsics_cannot_clobber_each_other() {
		// A type alias and a trait sharing a reserved name must land in
		// distinct slots — `type_slot_mut`/`trait_slot_mut` are separate
		// lookups specifically so this can't happen.
		let case = TestCase::new_core(indoc! {"
			type Add;
			trait u8 { func f(self: Self) -> Self; }
		"});
		case.diagnostics().assert_none();
		assert!(
			case.decls.intrinsics.add.is_none(),
			"a type alias named `Add` must not populate the trait slot"
		);
		assert!(
			case.decls.intrinsics.u8.is_none(),
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

		// Imported declarations are written in their block's own scope.
		let root = case.root_namespace();
		let imported = Scope::Import(ImportIdx::new(0));
		let mut indices = Vec::new();
		for (path, name, namespace) in
			[("heap", "heap", root), ("host::shared", "shared", imported)]
		{
			let kind = case.resolve(Tier::Type, path).expect_success();
			assert_eq!(kind, case.resolve(Tier::Value, path).expect_success());
			let DeclKind::Memory(index) = kind else {
				panic!("expected `{path}` to be a memory");
			};
			let memory = &case.decls.memories[usize::from(index)];
			assert_eq!(
				case.strings.resolve(case.decls.item(memory.loc).name.inner),
				Some(name)
			);
			assert_eq!(case.decls.scope(memory.loc), namespace);
			assert_eq!(
				case.decls.file_id(memory.loc),
				case.decls.namespaces.file_id(root.into())
			);
			indices.push(index);
		}
		assert_ne!(indices[0], indices[1]);
		for tier in [Tier::Type, Tier::Value] {
			assert_eq!(
				case.resolve(tier, "shared_alias").expect_success(),
				DeclKind::Memory(indices[1]),
			);
		}
		let DeclKind::Function(index) =
			case.resolve(Tier::Value, "host::log").expect_success()
		else {
			panic!("expected an imported function");
		};
		let function = &case.decls.functions[usize::from(index)];
		assert_eq!(case.decls.scope(function.loc), imported);
		assert_eq!(
			case.strings
				.resolve(case.decls.item(function.loc).name.inner),
			Some("log")
		);
		assert!(matches!(
			case.resolve(Tier::Value, "host::counter").expect_success(),
			DeclKind::Global(_),
		));
	}

	/// A module does not bind its own name inside itself (`self` names it),
	/// so an item there may share the module's name, as `math::sin::sin`.
	#[test]
	fn a_module_item_may_share_the_modules_name() {
		let mut case = TestCase::new(indoc! {r#"
			mod sin { pub func sin() {} pub struct cos(); }
			mod cos { pub struct cos(); }
		"#});
		case.diagnostics().assert_none();
		assert!(matches!(
			case.resolve(Tier::Value, "sin::sin").expect_success(),
			DeclKind::Function(_),
		));
		assert!(matches!(
			case.resolve(Tier::Type, "cos::cos").expect_success(),
			DeclKind::Struct(_),
		));
	}

	#[test]
	fn an_import_block_has_the_same_scope_qualifiers_as_a_module() {
		let mut case = TestCase::new(indoc! {r#"
			import "env" as host { func log(); }
		"#});
		case.diagnostics().assert_none();
		assert!(matches!(
			case.resolve(Tier::Value, "host::log").expect_success(),
			DeclKind::Function(_),
		));
		let host = case.resolve(Tier::Type, "host").expect_success();
		assert_eq!(
			case.resolve(Tier::Type, "host::self").expect_success(),
			host
		);
		let root = DeclKind::Package(case.decls.root_package);
		assert_eq!(
			case.resolve(Tier::Type, "host::package").expect_success(),
			root
		);
		assert_eq!(
			case.resolve(Tier::Type, "host::super").expect_success(),
			root
		);
		case.resolve(Tier::Type, "host::host")
			.diagnostics()
			.assert_error(DiagnosticCode::UndeclaredIdentifier);
	}

	/// Each host import records the entry it is written in and the field it
	/// is imported as: the string written before it, or else its own name, at
	/// the name's span. A string that does not decode keeps its span, so the
	/// field is still the one written.
	#[test]
	fn a_host_import_records_its_entry_and_field() {
		let source = indoc! {r#"
			import "env" as host {
				func log(value: i32);
				"Tick": func tick();
				"b\q": global depth: i32;
			}
		"#};
		let mut case = TestCase::new(source);
		let at = |text: &str| {
			let start = u32::try_from(source.find(text).unwrap()).unwrap();
			TextSpan::new(start, start + u32::try_from(text.len()).unwrap())
		};
		let mut entry = |path: &str| {
			let loc = case.resolve(Tier::Value, path).target().loc().unwrap();
			let entry = case.decls.import_entry(loc).unwrap();
			let field = case.strings.resolve(entry.field.inner).unwrap();
			(field.to_owned(), entry.field.span, entry.span.start)
		};
		assert_eq!(
			entry("host::log"),
			("log".to_owned(), at("log"), at("func log").start),
		);
		assert_eq!(
			entry("host::tick"),
			("Tick".to_owned(), at(r#""Tick""#), at(r#""Tick""#).start),
		);
		assert_eq!(
			entry("host::depth"),
			("depth".to_owned(), at(r#""b\q""#), at(r#""b\q""#).start),
		);
	}

	/// A module and an import block are declared where their names are
	/// written: a row in the table of the scope around them, which `self`
	/// inside them and `super` inside their children name too.
	#[test]
	fn a_module_and_an_import_block_are_rows_where_their_names_are_written() {
		let source = indoc! {r#"
			mod geo {
				import "env" as host { func log(); }
			}
		"#};
		let mut case = TestCase::new(source);
		case.diagnostics().assert_none();
		let mut key =
			|path| case.resolve(Tier::Type, path).target().loc().unwrap();
		let (geo, host) = (key("geo"), key("geo::host"));
		assert_eq!(key("geo::self"), geo);
		assert_eq!(key("geo::host::self"), host);
		assert_eq!(key("geo::host::super"), geo);
		let root = case.decls.root_package;
		assert_eq!(geo.namespace, Namespace::Package(root));
		let DeclKind::Module(module) = case.decls.namespaces.kind(geo) else {
			panic!("`geo` is a module");
		};
		assert_eq!(host.namespace, Namespace::Module(module));
		for (key, name) in [(geo, "geo"), (host, "host")] {
			let span = key.source_span(&case.decls.namespaces).span;
			assert_eq!(span.extract_str(source), name);
		}
	}

	/// Every declaration is a row, and its arena entry points back at it:
	/// the row's kind leads back to the entry, and every row but a package's
	/// own entry is exactly one entry's. Run over the user's package and core,
	/// which between them declare every kind (and core every generated one).
	/// The rows hold what is written: members, generated declarations and
	/// import entries are rows of the scope they are written in, a generated
	/// one's name span is empty, and the visibility is whether `pub` is
	/// written.
	#[test]
	fn every_declaration_is_a_row_its_arena_entry_points_at() {
		let source = indoc! {r#"
			pub struct Point(x: u32, y: u32);
			enum Color(u8) { Red = 0, Green, .. }
			pub trait Shape {
				type Unit;
				const SIDES: u32;
				func area(self: Self) -> u32;
			}
			impl Shape for Point {
				type Unit = u32;
				const SIDES: u32 = 0;
				func area(self: Self) -> u32 { 0 }
			}
			impl Point {
				pub func origin() -> Point { Point(0, 0) }
				const ZERO: u32 = 0;
			}
			typeset Small: StackValue { u8, u16 }
			type Alias = u32;
			memory heap: u32;
			pub global mut counter: u32 = 0;
			const LIMIT: u32 = 4;
			func run() {}
			pub mod geo {
				import "env" as host {
					"Log": func log(value: u32);
					global base: u32;
					memory mem: u32;
				}
			}
		"#};
		let case = TestCase::new(source);
		case.diagnostics().assert_no_errors();
		let decls = &case.decls;
		let namespaces = &decls.namespaces;
		let mut rows = 0;
		let mut check = |decl: ItemLoc, kind: DeclKind| {
			assert_eq!(namespaces.kind(decl), kind);
			rows += 1;
		};
		for (index, decl) in decls.structs.iter().enumerate() {
			let kind = DeclKind::Struct(StructIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.enums.iter().enumerate() {
			let kind = DeclKind::Enum(EnumIdx::new(index as u32));
			check(decl.loc, kind);
		}
		let variants: Vec<ConstIdx> = decls
			.enums
			.iter()
			.flat_map(|decl| {
				(u32::from(decl.variants.start)..u32::from(decl.variants.end))
					.map(ConstIdx::new)
			})
			.collect();
		for (index, decl) in decls.constants.iter().enumerate() {
			let index = ConstIdx::new(index as u32);
			let kind = if variants.contains(&index) {
				DeclKind::EnumVariant(index)
			} else {
				DeclKind::Const(index)
			};
			check(decl.loc, kind);
		}
		for (index, decl) in decls.traits.iter().enumerate() {
			let kind = DeclKind::Trait(TraitIdx::new(index as u32));
			// A typeset's trait has the typeset's name, written nowhere.
			if decl.typeset.is_some() {
				let name = namespaces.item(decl.loc).name;
				assert_eq!(name.span.start, name.span.end);
			}
			check(decl.loc, kind);
		}
		for (index, decl) in decls.typesets.iter().enumerate() {
			let kind = DeclKind::TypeSet(TypesetIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.type_aliases.iter().enumerate() {
			let kind = DeclKind::TypeAlias(TypeAliasIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.functions.iter().enumerate() {
			let kind = DeclKind::Function(FunctionIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.memories.iter().enumerate() {
			let kind = DeclKind::Memory(MemoryIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.globals.iter().enumerate() {
			let kind = DeclKind::Global(GlobalIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.assoc_types.iter().enumerate() {
			let kind = DeclKind::AssocType(AssocTypeIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.modules.iter().enumerate() {
			let kind = DeclKind::Module(ModuleIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in decls.imports.iter().enumerate() {
			let kind = DeclKind::Import(ImportIdx::new(index as u32));
			check(decl.loc, kind);
		}
		for (index, decl) in namespaces.package_instances().iter().enumerate() {
			let kind = DeclKind::PackageInstance(PackageInstanceIdx::new(
				index as u32,
			));
			check(decl.loc, kind);
		}
		// Every other row is a package's own entry.
		let packages = namespaces.packages.len();
		assert_eq!(namespaces.keys().count(), rows + packages);
		for package in &namespaces.packages {
			let own = ItemLoc::new(
				Namespace::Package(package.package_id),
				DeclIdx::SELF,
			);
			let row = namespaces.item(own);
			assert_eq!(row.kind, DeclKind::Package(package.package_id));
			assert_eq!(row.name.inner, Keyword::Package.symbol());
			assert_eq!(row.name.span, TextSpan::new(0, 0));
		}
		// The user's members, generated rows and import entries are rows of
		// the scope they are written in, under their own names.
		let root = Namespace::Package(decls.root_package);
		let names_in = |namespace: Namespace| -> Vec<(&str, bool, Visibility)> {
			namespaces
				.symbols(namespace)
				.items
				.iter()
				.map(|row| {
					(
						case.strings.resolve(row.name.inner).unwrap(),
						row.name.span.start == row.name.span.end,
						row.visibility,
					)
				})
				.collect()
		};
		let root_rows = names_in(root);
		for (written, visibility) in [
			("Point", Visibility::Public),
			("Color", Visibility::Private),
			("Shape", Visibility::Public),
			("area", Visibility::Private),
			("SIDES", Visibility::Private),
			("Unit", Visibility::Private),
			("origin", Visibility::Public),
			("ZERO", Visibility::Private),
			("counter", Visibility::Public),
			("geo", Visibility::Public),
		] {
			assert!(
				root_rows.contains(&(written, false, visibility)),
				"{written}"
			);
		}
		// A typeset's trait is generated, with the typeset's visibility.
		for generated in ["Small", "Args", "Result", "Size", "Value"] {
			assert!(
				root_rows.contains(&(generated, true, Visibility::Private)),
				"{generated}"
			);
		}
		let DeclKind::Import(import) = namespaces
			.kind(case.decls.imports.last().expect("`host` is an import").loc)
		else {
			unreachable!()
		};
		let host_rows = names_in(Namespace::Import(import));
		for written in ["log", "base", "mem"] {
			assert!(
				host_rows.contains(&(written, false, Visibility::Private)),
				"{written}"
			);
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
			assert!(matches!(original, DeclKind::Function(_)), "{imports}");
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
		let mut case = TestCase::new_core(indoc! {"
			const VALUE: Unknown = missing;
			trait Api {
				func make() -> Unknown;
				func get(self: Self, value: Unknown) -> Unknown;
				const VALUE: Unknown;
				type Item: Unknown;
			}
			struct Host();
			impl Host {
				func make() -> Unknown { missing }
				func get(self: Self, value: Unknown) -> Unknown { missing }
				const VALUE: Unknown = missing;
			}
			impl Api for Host {
				func make() -> Unknown { missing }
				func get(self: Self, value: Unknown) -> Unknown { missing }
				const VALUE: Unknown = missing;
				type Item = Unknown;
			}
		"});
		case.diagnostics().assert_no_errors();

		let DeclKind::Const(free_constant) =
			case.resolve(Tier::Value, "VALUE").expect_success()
		else {
			panic!("expected a free constant");
		};
		let mut ids =
			std::collections::HashSet::from([free_constant.loc(&case.decls)]);
		let members = case.decls.traits[0]
			.members
			.iter()
			.map(|member| member.kind)
			.chain(
				case.decls.inherent_impls[0]
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
				ids.insert(kind.loc(&case.decls)),
				"members must have distinct identities"
			);
			let (name, expected) = match kind {
				MemberKind::Function(index) => (case.decls.name(index), "make"),
				MemberKind::Method(index) => (case.decls.name(index), "get"),
				MemberKind::Constant(index) => {
					(case.decls.name(index), "VALUE")
				}
				MemberKind::AssociatedType(index) => {
					(case.decls.name(index), "Item")
				}
			};
			assert_eq!(case.strings.resolve(name.inner), Some(expected));
		}
		assert_eq!(ids.len(), 12);
		for decl in &case.decls.constants {
			assert_eq!(case.decls.scope(decl.loc), case.root_namespace());
		}
		for decl in &case.decls.assoc_types {
			assert_eq!(case.decls.scope(decl.loc), case.root_namespace());
		}
	}

	#[test]
	fn type_and_value_definitions_can_share_a_name() {
		let mut case = TestCase::new("trait Item {} const Item: i32 = 1;");
		case.diagnostics().assert_none();
		assert!(matches!(
			case.resolve(Tier::Type, "Item").expect_success(),
			DeclKind::Trait(_)
		));
		assert!(matches!(
			case.resolve(Tier::Value, "Item").expect_success(),
			DeclKind::Const(_)
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
				DeclKind::Function(_)
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
			TestCase::new_core(source)
				.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		}
		let case = TestCase::new_core("struct S(); impl S { func f() {} }");
		case.diagnostics().assert_none();
		let symbol = case.strings.get("f").unwrap();
		let owner = &case.decls.inherent_impls[0];
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
				DeclKind::Struct(_)
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
			case.decls.namespaces.file_id(case.root_namespace().into());
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
		let DeclKind::Function(index) =
			case.resolve(Tier::Value, "f").expect_success()
		else {
			panic!("expected a function");
		};
		assert_eq!(
			case.strings.resolve(
				case.decls.functions[usize::from(index)].params[0]
					.unwrap()
					.inner
			),
			Some("original")
		);
		assert!(matches!(
			case.resolve(Tier::Value, "after").expect_success(),
			DeclKind::Function(_)
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
			case.decls.namespaces.file_id(case.root_namespace().into());
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
			DeclKind::Function(_)
		));
		assert!(matches!(
			case.resolve(Tier::Value, "after").expect_success(),
			DeclKind::Function(_)
		));
	}

	#[test]
	fn duplicate_enum_variant_keeps_the_original_binding_and_later_variants() {
		let source = "enum E { Same, Same, After }";
		let mut case = TestCase::new(source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		let result = case.resolve(Tier::Value, "E::Same");
		let DeclKind::EnumVariant(same) = result.expect_success() else {
			panic!("`E::Same` is an enum variant");
		};
		let key = result.target().loc().unwrap();
		let first = source.find("Same").unwrap();
		assert_eq!(
			std::ops::Range::from(key.source_span(&case.decls.namespaces).span),
			first..first + 4
		);
		let DeclKind::EnumVariant(after) =
			case.resolve(Tier::Value, "E::After").expect_success()
		else {
			panic!("`E::After` is an enum variant");
		};
		// The duplicate keeps its slot, so the enum's run of constants
		// matches the written list.
		let DeclKind::Enum(enum_index) =
			case.resolve(Tier::Type, "E").expect_success()
		else {
			panic!("`E` is an enum");
		};
		let run = &case.decls.enums[usize::from(enum_index)].variants;
		assert_eq!(
			(u32::from(run.start), u32::from(run.end)),
			(u32::from(same), u32::from(same) + 3)
		);
		assert_eq!(u32::from(after), u32::from(same) + 2);
		let names: Vec<_> = (u32::from(run.start)..u32::from(run.end))
			.map(|index| {
				let name = case.decls.name(ConstIdx::new(index)).inner;
				case.strings.resolve(name).unwrap()
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
			let case = TestCase::new_core(source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
			let f = BindingKey::value(case.strings.get("f").unwrap());
			let after = BindingKey::value(case.strings.get("after").unwrap());
			let (original, later) =
				if let Some(owner) = case.decls.inherent_impls.first() {
					(
						owner.members[usize::from(owner.bindings[&f])].kind,
						owner.members[usize::from(owner.bindings[&after])].kind,
					)
				} else if let Some(owner) = case
					.decls
					.trait_impls
					.iter()
					.find(|owner| owner.bindings.contains_key(&after))
				{
					(
						owner.members[usize::from(owner.bindings[&f])].kind,
						owner.members[usize::from(owner.bindings[&after])].kind,
					)
				} else {
					let owner = &case.decls.traits[0];
					(
						owner.members[usize::from(owner.bindings[&f])].kind,
						owner.members[usize::from(owner.bindings[&after])].kind,
					)
				};
			let MemberKind::Function(index) = original else {
				panic!("expected an associated function");
			};
			assert_eq!(
				case.strings.resolve(
					case.decls.functions[usize::from(index)].params[0]
						.unwrap()
						.inner
				),
				Some("original")
			);
			let MemberKind::Function(index) = later else {
				panic!("expected a later associated function");
			};
			assert_eq!(
				case.strings.resolve(case.decls.name(index).inner),
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

		let point_symbol = case.strings.get_or_intern("Point");
		let root_namespace = case.root_namespace();
		let bindings = &case
			.decls
			.namespaces
			.symbols(root_namespace.into())
			.bindings;

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

		let point_symbol = case.strings.get_or_intern("Point");
		let root_namespace = case.root_namespace();
		let bindings = &case
			.decls
			.namespaces
			.symbols(root_namespace.into())
			.bindings;

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

		// `Point` isn't necessarily `decls.structs[0]` — the real core
		// (loaded by `TestCase::new`) declares its own structs (`Layout`,
		// `RawPtr`), so look it up by name rather than assuming an index.
		let DeclKind::Struct(point_struct_index) =
			case.resolve(Tier::Type, "Point").expect_success()
		else {
			panic!("expected `Point` to be a struct")
		};
		let struct_decl = &case.decls.structs[usize::from(point_struct_index)];

		let (names, lookup) = (&struct_decl.field_names, &struct_decl.lookup);
		// Both occurrences keep a real field slot — duplicate name isn't
		// dropped, only unreachable by name — so a later field's index
		// still matches its declaration position.
		assert_eq!(names.len(), 2);
		let name = names[0].unwrap().inner;
		assert_eq!(names[1].unwrap().inner, name);
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
			let DeclKind::Function(index) =
				case.resolve(Tier::Value, path).expect_success()
			else {
				panic!("expected `{path}` to be a function");
			};
			let params: Vec<_> = case.decls.functions[usize::from(index)]
				.params
				.iter()
				.map(|param| param.unwrap())
				.collect();
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
			"func f(self: Self) {}",
			"func f(self: Self);",
			r#"import "env" as host { func f(self: Self); }"#,
			r#"import "env" as host { func f(x: i32, self: Self); }"#,
		] {
			let case = TestCase::new(source);
			case.diagnostics()
				.assert_error(DiagnosticCode::SelfParamPosition);
		}
	}

	#[test]
	fn a_field_cannot_be_named_self() {
		let case = TestCase::new("struct S(self: i32);");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ReservedIdentifier]);
	}

	#[test]
	fn duplicate_associated_function_parameters_keep_their_slots() {
		for source in [
			"trait T { func f(x: i32, x: i32, tail: i32); }",
			"struct S(); impl S { func f(x: i32, x: i32, tail: i32) {} }",
			"trait T {} struct S(); impl T for S { func f(x: i32, x: i32, tail: i32) {} }",
		] {
			let case = TestCase::new_core(source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateFunctionParameter]);
			let function = &case.decls.functions[0];
			let names: Vec<_> = function
				.params
				.iter()
				.map(|param| {
					case.strings.resolve(param.unwrap().inner).unwrap()
				})
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
			"trait T { func f(x: i32, self: Self); }",
			"struct S(); impl S { func f(x: i32, self: Self) {} }",
			"trait T {} struct S(); impl T for S { func f(x: i32, self: Self) {} }",
		] {
			let case = TestCase::new_core(source);
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
		let source = "trait T { func f(self: Self, self: Self); }";
		let case = TestCase::new_core(source);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::DuplicateFunctionParameter,
			DiagnosticCode::SelfParamPosition,
		]);
		let params = &case.decls.functions[0].params;
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
		let case = TestCase::new_core(indoc! {"
			trait T {
				func method(self: Self, x: i32);
				func associated(x: i32);
			}
			struct S();
			impl S {
				func method(self: Self, x: i32) {}
				func associated(x: i32) {}
			}
			impl T for S {
				func method(self: Self, x: i32) {}
				func associated(x: i32) {}
			}
		"});
		case.diagnostics().assert_none();
		let members = case.decls.traits[0]
			.members
			.iter()
			.map(|member| member.kind)
			.chain(
				case.decls.inherent_impls[0]
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
				case.strings.resolve(case.decls.name(index).inner),
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
			DeclKind::Function(_)
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
		let helper = case.strings.get_or_intern("helper");

		assert!(matches!(
			case.decls.namespaces.lookup(
				&case.decls.use_items,
				root,
				root.into(),
				BindingKey::value(helper),
			),
			BindingLookup::Found { .. }
		));
		assert!(
			case.decls
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
				use package::a::*;
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let b = case.scope("b");
		let helper = case.strings.get_or_intern("helper");

		assert!(matches!(
			case.decls.namespaces.lookup(
				&case.decls.use_items,
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
				use package::a::*;
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
		let helper = case.strings.get_or_intern("helper");

		match case.decls.namespaces.lookup(
			&case.decls.use_items,
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
				pub use package::a::*;
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let a = case.scope("a");
		let hub = case.scope("hub");
		let helper = case.strings.get_or_intern("helper");

		let Some(Binding {
			target: BindingTarget::Accessible(original),
			..
		}) = case
			.decls
			.namespaces
			.direct_lookup(a.into(), BindingKey::value(helper))
		else {
			panic!("`a::helper` should resolve directly");
		};

		match case.decls.namespaces.lookup(
			&case.decls.use_items,
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
				pub use package::a::*;
				pub use package::b::*;
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let hub = case.scope("hub");
		let pick = case.strings.get_or_intern("pick");

		match case.decls.namespaces.lookup(
			&case.decls.use_items,
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
				pub use package::a::*;
				func pick() -> i32 { 2 }
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let hub = case.scope("hub");
		let pick = case.strings.get_or_intern("pick");

		let Some(Binding {
			target: BindingTarget::Accessible(direct),
			..
		}) = case
			.decls
			.namespaces
			.direct_lookup(hub.into(), BindingKey::value(pick))
		else {
			panic!("`hub::pick` should be bound directly");
		};

		match case.decls.namespaces.lookup(
			&case.decls.use_items,
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
		let import = &case.decls.imports[0];
		assert_eq!(
			case.strings.resolve(import.external_name.inner).unwrap(),
			"slash\\n"
		);
		let source = &case
			.graph
			.files
			.get(
				case.decls
					.namespaces
					.file_id(case.decls.scope(import.loc).into()),
			)
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
		assert_eq!(case.decls.exports.len(), 3);
		let f = case.strings.get("f").unwrap();
		for name in ["run", "start"] {
			let export = &case.decls.exports[&case.strings.get(name).unwrap()];
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
				.decls
				.exports
				.contains_key(&case.strings.get("f").unwrap())
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
		assert_eq!(case.decls.exports.len(), 1);
		let export = &case.decls.exports[&case.strings.get("run").unwrap()];
		assert_eq!(export.name.inner, case.strings.get("first").unwrap());
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
		assert_eq!(case.decls.exports.len(), 1);
		let export = &case.decls.exports[&case.strings.get("run").unwrap()];
		assert_eq!(export.name.inner, case.strings.get("first").unwrap());
		assert_eq!(export.namespace, Scope::Package(case.decls.root_package));
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
		assert_eq!(case.decls.exports.len(), 4);
		for expected in ["line\n", "slash\\n", "quote\"", ""] {
			let symbol = case.strings.get(expected).unwrap();
			let export = &case.decls.exports[&symbol];
			let file =
				case.graph.files.get(export.external_span.file_id).unwrap();
			let written = export.external_span.span.extract_str(&file.source);
			assert!(written.starts_with('"') && written.ends_with('"'));
		}
		assert!(case.strings.get(r#""line\n""#).is_none());
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
			assert!(case.strings.get(r#""\o""#).is_none());
			assert!(case.strings.get(r"\o").is_none());
			if source.starts_with("import") {
				assert_eq!(
					case.decls.imports[0].external_name.inner,
					Keyword::Error.symbol()
				);
				assert!(case.strings.get("after").is_some());
			} else {
				assert_eq!(case.decls.exports.len(), 1);
				assert!(
					case.decls
						.exports
						.contains_key(&case.strings.get("valid").unwrap())
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
		let mut strings = Keyword::create_interner();
		let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
		builder.load_core();
		let root_id = builder
			.load_package(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					indoc! {"
            #[other({ value: \"\\o\" })
        "}
					.to_string(),
				)])),
			)
			.unwrap();
		let graph = builder.build(root_id);
		let parser_diagnostics = graph.collect_parser_diagnostics();
		assert_eq!(parser_diagnostics.len(), 1, "{parser_diagnostics:?}");
		assert_eq!(
			parser_diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::UnclosedDelimiter.code())
		);
		let mut diagnostics = Vec::new();
		let mut resolutions = NameResolutions::default();
		let _ = Declarations::build(
			&graph.packages,
			&graph.files,
			&mut strings,
			&mut diagnostics,
			&mut resolutions,
			graph.core_package,
			graph.root_package,
		);
		assert!(diagnostics.is_empty(), "{diagnostics:?}");
	}

	// ── package instances (`package "key" as alias;`) ─────────────────────────

	/// A real project on virtual files: `/app` is the root, and every
	/// `wx.json` is read, so a package instance looks its key up in an actual
	/// manifest.
	fn manifest_case(files: &[(&str, &str)]) -> TestCase {
		let mut strings = Keyword::create_interner();
		let workspace = vfs::VirtualFileSource::new(
			files
				.iter()
				.map(|(path, source)| {
					(vfs::AbsolutePath::new(*path), source.to_string())
				})
				.collect(),
		);
		let graph = vfs::open_manifest(
			vfs::AbsolutePath::new("/app"),
			&workspace,
			&mut strings,
		)
		.unwrap();
		TestCase::from_graph(graph, strings)
	}

	const APP_WITH_MATH: &str = r#"{
		"entry": "main.wx",
		"dependencies": { "math": { "type": "local", "path": "../math" } }
	}"#;
	const MATH_MANIFEST: &str = r#"{ "entry": "main.wx" }"#;
	const MATH_SOURCE: &str = "pub func add() {}";

	#[test]
	fn a_package_instance_binds_its_alias_to_the_declared_package() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"package "math" as m;"#),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		assert_eq!(case.decls.namespaces.package_instances().len(), 1);
		let item = &case.decls.namespaces.package_instances()[0];
		assert_eq!(case.strings.resolve(item.package_name.inner), Some("math"));
		assert_eq!(
			case.strings.resolve(case.decls.item(item.loc).name.inner),
			Some("m")
		);
		assert!(item.package.is_some());

		assert!(matches!(
			case.resolve(Tier::Value, "m::add").expect_success(),
			DeclKind::Function(_)
		));
	}

	#[test]
	fn package_instances_accept_dependency_keys_that_are_not_identifiers() {
		for key in [
			"SomeLib",
			"my-lib",
			"loop",
			"@org/math",
			"with spaces",
			"数学",
			"",
		] {
			let quoted = serde_json::to_string(key).unwrap();
			let manifest = APP_WITH_MATH.replace("\"math\"", &quoted);
			let source = format!("package {quoted} as math;");
			let mut case = manifest_case(&[
				("/app/wx.json", &manifest),
				("/app/main.wx", &source),
				("/math/wx.json", MATH_MANIFEST),
				("/math/main.wx", MATH_SOURCE),
			]);
			case.diagnostics().assert_none();
			let item = &case.decls.namespaces.package_instances()[0];
			assert_eq!(
				case.strings.resolve(item.package_name.inner),
				Some(key)
			);
			assert!(matches!(
				case.resolve(Tier::Value, "math::add").expect_success(),
				DeclKind::Function(_)
			));
		}
	}

	/// The point of the item over the old implicit binding: one package can
	/// be instantiated several times, each under an alias of its own.
	#[test]
	fn one_package_can_be_instantiated_under_several_aliases() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			(
				"/app/main.wx",
				r#"package "math" as math; pub package "math" as math2;"#,
			),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		assert_eq!(case.decls.namespaces.package_instances().len(), 2);
		let items = case.decls.namespaces.package_instances();
		assert_eq!(items[0].package, items[1].package);
		for path in ["math::add", "math2::add"] {
			assert!(matches!(
				case.resolve(Tier::Value, path).expect_success(),
				DeclKind::Function(_)
			));
		}
	}

	/// A manifest key only makes a package available. Without a `crate`
	/// item nothing names it, which is what the implicit binding used to
	/// do on every key.
	#[test]
	fn a_declared_dependency_is_not_nameable_without_a_package_instance() {
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
	fn a_package_instance_may_be_declared_in_a_nested_module() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			(
				"/app/main.wx",
				r#"mod outer { pub mod inner { pub package "math" as m; } }"#,
			),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		assert!(matches!(
			case.resolve(Tier::Value, "outer::inner::m::add")
				.expect_success(),
			DeclKind::Function(_)
		));
		// Bound in `inner`, not at the root.
		let result = case.resolve(Tier::Value, "m::add");
		assert!(matches!(result.target(), BindingTarget::Error));
	}

	#[test]
	fn a_private_package_instance_is_not_visible_outside_its_module() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"pub mod inner { package "math" as m; }"#),
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
	fn a_pub_package_instance_exposes_the_dependency_to_consumers() {
		let app = r#"{
			"entry": "main.wx",
			"dependencies": { "mid": { "type": "local", "path": "../mid" } }
		}"#;
		let mid = r#"{
			"entry": "main.wx",
			"dependencies": { "math": { "type": "local", "path": "../math" } }
		}"#;
		let files = |mid_source: &'static str| {
			vec![
				("/app/wx.json", app),
				("/app/main.wx", r#"package "mid" as mid;"#),
				("/mid/wx.json", mid),
				("/mid/main.wx", mid_source),
				("/math/wx.json", MATH_MANIFEST),
				("/math/main.wx", MATH_SOURCE),
			]
		};

		let mut public =
			manifest_case(&files(r#"pub package "math" as math;"#));
		public.diagnostics().assert_none();
		assert!(matches!(
			public
				.resolve(Tier::Value, "mid::math::add")
				.expect_success(),
			DeclKind::Function(_)
		));

		let mut private = manifest_case(&files(r#"package "math" as math;"#));
		private.diagnostics().assert_none();
		private
			.resolve(Tier::Value, "mid::math::add")
			.diagnostics()
			.assert_error(DiagnosticCode::PrivateItem);
	}

	#[test]
	fn a_package_instance_naming_an_undeclared_dependency_is_an_error() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"package "nope" as nope;"#),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);

		case.diagnostics()
			.assert_error(DiagnosticCode::UnknownPackage);
		assert!(
			case.decls.namespaces.package_instances()[0]
				.package
				.is_none()
		);

		// The alias is still bound, to a poisoned binding: a path through it
		// ends in `Error` without a second diagnostic, since the one at the
		// item already says what is wrong.
		let result = case.resolve(Tier::Value, "nope::add");
		assert!(matches!(result.target(), BindingTarget::Error));
		result.diagnostics().assert_none();
	}

	#[test]
	fn a_package_alias_colliding_with_another_name_is_a_duplicate() {
		// Whichever is written first, the diagnostic points at both sites.
		for source in [
			r#"package "math" as m; struct m();"#,
			r#"struct m(); package "math" as m;"#,
		] {
			let case = manifest_case(&[
				("/app/wx.json", APP_WITH_MATH),
				("/app/main.wx", source),
				("/math/wx.json", MATH_MANIFEST),
				("/math/main.wx", MATH_SOURCE),
			]);

			case.diagnostics()
				.assert_error(DiagnosticCode::DuplicateDefinition);
			let alias = case
				.decls
				.item(case.decls.namespaces.package_instances()[0].loc)
				.name
				.span;
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
	fn a_package_alias_is_a_definition_a_use_can_lead_through() {
		let mut case = manifest_case(&[
			("/app/wx.json", APP_WITH_MATH),
			("/app/main.wx", r#"package "math" as m; use m::add;"#),
			("/math/wx.json", MATH_MANIFEST),
			("/math/main.wx", MATH_SOURCE),
		]);
		case.diagnostics().assert_none();

		let DeclKind::PackageInstance(index) =
			case.resolve(Tier::Type, "m").expect_success()
		else {
			panic!("expected a package instance");
		};
		let item =
			&case.decls.namespaces.package_instances()[usize::from(index)];
		let declared = DeclKind::PackageInstance(index)
			.declared_at(&case.decls)
			.unwrap();
		assert_eq!(declared, case.decls.declaration_span(item.loc));
		assert_eq!(
			declared
				.span
				.extract_str(r#"package "math" as m; use m::add;"#),
			"m"
		);

		assert!(matches!(
			case.resolve(Tier::Value, "add").expect_success(),
			DeclKind::Function(_)
		));
	}

	/// The core stays implicit: `core` needs no package instance.
	#[test]
	fn core_is_bound_without_a_package_instance() {
		let mut case = manifest_case(&[
			("/app/wx.json", r#"{ "entry": "main.wx" }"#),
			("/app/main.wx", "func main() {}"),
		]);
		case.diagnostics().assert_none();

		assert!(matches!(
			case.resolve(Tier::Type, "core::Memory").expect_success(),
			DeclKind::Trait(_)
		));
	}

	/// The attributes prescan recorded on the function named `name`.
	fn function_attributes(case: &TestCase, name: &str) -> Attributes {
		let symbol = case.strings.get(name).unwrap();
		let mut found = case.decls.functions.iter().filter(|function| {
			case.decls.item(function.loc).name.inner == symbol
		});
		let function = found.next().expect("the function is declared");
		assert!(found.next().is_none(), "`{name}` names one function");
		function.attributes
	}

	#[test]
	fn inline_is_recorded_on_every_kind_of_function_with_a_body() {
		let case = TestCase::new(indoc! {"
			struct S();
			trait T {
				#[inline]
				func defaulted(self: Self) {}
				func required(self: Self);
			}
			impl S {
				#[inline]
				func inherent(self: Self) {}
			}
			impl T for S {
				#[inline]
				func required(self: Self) {}
			}
			#[inline]
			func free() {}
			func plain() {}
		"});
		case.diagnostics().assert_none();
		for name in ["defaulted", "inherent", "free"] {
			assert!(
				function_attributes(&case, name).contains(Attributes::INLINE),
				"`{name}` is inline"
			);
		}
		assert_eq!(function_attributes(&case, "plain"), Attributes::empty());
		// The trait's declaration and the impl's function are two functions
		// with the attribute only on the impl's.
		let required = case.strings.get("required").unwrap();
		let inline: Vec<bool> = case
			.decls
			.functions
			.iter()
			.filter(|function| {
				case.decls.item(function.loc).name.inner == required
			})
			.map(|function| function.attributes.contains(Attributes::INLINE))
			.collect();
		assert_eq!(inline, [false, true]);
	}

	/// What `name`'s `#[memory_limits]` records, as `(min, max)`.
	fn memory_limits(
		case: &TestCase,
		name: &str,
	) -> (Option<u64>, Option<u64>) {
		let symbol = case.strings.get(name).unwrap();
		let memory = case
			.decls
			.memories
			.iter()
			.find(|memory| case.decls.item(memory.loc).name.inner == symbol)
			.expect("the memory is declared");
		(
			memory.limits.min_pages.map(|pages| pages.inner),
			memory.limits.max_pages.map(|pages| pages.inner),
		)
	}

	#[test]
	fn memory_limits_are_recorded_as_written() {
		let case = TestCase::new(indoc! {"
			#[memory_limits({ min_pages: 2, max_pages: 9 })]
			memory both: u32;
			#[memory_limits({ max_pages: 4 })]
			memory capped: u32;
			memory free: u32;
			// Too many for a 32-bit memory: that is the checker's to say.
			#[memory_limits({ min_pages: 70000 })]
			memory big: u32;
			import \"env\" as env { memory host: u32; }
		"});
		case.diagnostics().assert_none();
		assert_eq!(memory_limits(&case, "both"), (Some(2), Some(9)));
		assert_eq!(memory_limits(&case, "capped"), (None, Some(4)));
		assert_eq!(memory_limits(&case, "free"), (None, None));
		assert_eq!(memory_limits(&case, "big"), (Some(70000), None));
		assert_eq!(memory_limits(&case, "host"), (None, None));
	}

	#[test]
	fn a_memory_limits_argument_that_says_nothing_is_reported_and_left_out() {
		for (source, message, recorded) in [
			(
				"#[memory_limits({ pages: 1 })] memory heap: u32;",
				"`#[memory_limits]` has no argument `pages`",
				(None, None),
			),
			(
				"#[memory_limits({ min_pages: 1, min_pages: 2 })] memory heap: u32;",
				"`min_pages` is written twice",
				(Some(1), None),
			),
			(
				"#[memory_limits({ max_pages: \"4\" })] memory heap: u32;",
				"`max_pages` must be a number of pages",
				(None, None),
			),
		] {
			let case = TestCase::new(source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::InvalidMemoryLimits]);
			case.diagnostics().assert_error_saying(message);
			assert_eq!(memory_limits(&case, "heap"), recorded, "{source}");
		}
	}

	#[test]
	fn an_unknown_attribute_is_ignored_with_a_warning() {
		let case = TestCase::new(indoc! {"
			#[inlin]
			func f() {}
			#[packed]
			struct S();
		"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnknownAttribute,
			DiagnosticCode::UnknownAttribute,
		]);
		case.diagnostics().assert_no_errors();
		assert_eq!(function_attributes(&case, "f"), Attributes::empty());
	}

	#[test]
	fn a_known_attribute_on_the_wrong_item_is_an_error() {
		let case = TestCase::new(indoc! {"
			#[inline]
			struct S();
			#[fixed_order]
			func f() {}
			trait T {
				#[inline]
				func required(self: Self);
			}
			#[inline]
			const C: u32 = 0;
		"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::MisplacedAttribute,
			DiagnosticCode::MisplacedAttribute,
			DiagnosticCode::MisplacedAttribute,
			DiagnosticCode::MisplacedAttribute,
		]);
		case.diagnostics().assert_error_saying(
			"`#[inline]` cannot be written on a function without a body",
		);
		case.diagnostics()
			.assert_error_saying("`#[fixed_order]` applies only to a struct");
		assert_eq!(function_attributes(&case, "f"), Attributes::empty());
		assert_eq!(function_attributes(&case, "required"), Attributes::empty());
	}

	#[test]
	fn a_known_attribute_in_the_wrong_form_is_an_error() {
		let case = TestCase::new(indoc! {"
			#[inline({ always: 1 })]
			func f() {}
			#[memory_limits]
			memory heap: u32;
		"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::MalformedAttribute,
			DiagnosticCode::MalformedAttribute,
		]);
		case.diagnostics()
			.assert_error_saying("`#[inline]` takes no arguments");
		case.diagnostics()
			.assert_error_saying("`#[memory_limits]` takes arguments");
		assert_eq!(function_attributes(&case, "f"), Attributes::empty());
	}

	#[test]
	fn a_repeated_attribute_is_a_warning_and_still_applies() {
		let case = TestCase::new(indoc! {"
			#[inline]
			#[inline]
			func f() {}
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateAttribute]);
		case.diagnostics().assert_no_errors();
		assert_eq!(function_attributes(&case, "f"), Attributes::INLINE);
	}
}
