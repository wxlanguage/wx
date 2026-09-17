//! Phase 1 — the prescan. Walks every item in every file, allocates its TIR
//! entry and claims its name, and records it in `ast_nodes` for the
//! demand-driven signature pass to pick up. No type checking happens here.

// use super::*;

use std::collections::HashMap;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{self, DefId, Spanned, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	index::index_newtype,
	small_vec::SmallVec,
	tir::literals::unescape_string_literal,
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

	namespaces: Vec<Namespace>,
	package_namespaces: Vec<NamespaceIndex>,
	module_decls: Vec<ModuleDeclaration>,
	import_decls: Vec<ImportDeclaration>,
	ast_nodes: Vec<AstEntry<'ast>>,
	traits: Vec<TraitDef>,
	trait_impls: Vec<TraitImplDef>,
	inherent_impls: Vec<InherentImplDef>,
	use_items: Vec<UseItemDef>,
	use_paths: Vec<UsePathSegment>,
	// Keyed by local (alias-or-original) name, not the name as written at the `use` site.
	pending_named_imports:
		HashMap<(NamespaceIndex, SymbolU32), SmallVec<UseItemIndex>>,
	/// Every `pub use path::*;` item, grouped by the namespace it's
	/// *declared* in — no name dimension, unlike `pending_named_imports`,
	/// since a glob doesn't claim one. Lets glob resolution find "what does
	/// this namespace re-export" without scanning every `use_items` entry.
	pending_pub_glob_reexports: HashMap<NamespaceIndex, SmallVec<UseItemIndex>>,
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
	fn noun(self) -> &'static str {
		match self {
			BindingNamespace::Type => "type",
			BindingNamespace::Value => "value",
		}
	}
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct BindingKey {
	namespace: BindingNamespace,
	pub(super) symbol: SymbolU32,
}

impl BindingKey {
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
	pub self_param: TypeParamDef,
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
	pub type_params: Box<[TypeParamDef]>,
	pub members: Vec<TraitMemberDef>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIndex>,
	pub self_accesses: Vec<SourceSpan>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct InherentImplDef {
	pub def_id: ast::DefId,
	pub file_id: FileId,
	pub namespace: NamespaceIndex,
	pub type_params: Box<[TypeParamDef]>,
	#[cfg_attr(
		test,
		serde(serialize_with = "crate::testing::serialize_sorted_map")
	)]
	pub bindings: HashMap<BindingKey, MemberIndex>,
	pub members: Vec<InherentMemberDef>,
	pub self_accesses: Vec<SourceSpan>,
}

index_newtype!(LocalDefIndex);
index_newtype!(MemberIndex);
index_newtype!(ModuleDeclIndex);
index_newtype!(ImportDeclIndex);
index_newtype!(NamespaceIndex);
index_newtype!(TraitIndex);
index_newtype!(InherentImplIndex);
index_newtype!(TraitImplIndex);

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
	const SELF: Self = LocalDefIndex(0);
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct AstEntry<'ast> {
	def_id: DefId,
	file_id: FileId,
	namespace: NamespaceIndex,
	node: AstNodeRef<'ast>,
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum AstNodeRef<'ast> {
	Function {
		item: &'ast ast::Item,
	},
	RecordStruct {
		item: &'ast ast::Item,
	},
	TupleStruct {
		item: &'ast ast::Item,
	},
	Enum {
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
	},
	TraitImplFunction {
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	},
	TraitImplConstant {
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	},
	TraitImplAssocType {
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	},
	InherentImplBlock {
		item: &'ast ast::Item,
		block_index: InherentImplIndex,
	},
	InherentImplFunction {
		block_id: ast::DefId,
		item: &'ast ast::ImplItem,
		block_index: InherentImplIndex,
	},
	InherentImplConst {
		block_id: ast::DefId,
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
	pub use_items: Vec<UseItemDef>,
	pub use_paths: Vec<UsePathSegment>,
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
	Namespace(NamespaceIndex),
	Enum(DefId),
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
			DefKind::Enum(_) => "enum",
			DefKind::Struct(_) => "struct",
			DefKind::Namespace(_) => "module",
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

	/// An item declared `visibility` in `declaring_namespace` is reachable
	/// from `accessor` if it's `Public`, or if `declaring_namespace`
	/// contains `accessor`.
	fn is_accessible_from(
		&self,
		accessor: NamespaceIndex,
		declaring_namespace: NamespaceIndex,
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
	/// possible: a `HashMap` has at most one entry per key.
	fn direct_lookup(
		&self,
		namespace: NamespaceIndex,
		key: BindingKey,
	) -> Option<BindingCandidate>;

	/// What `namespace` exposes *only* through its own `pub use path::*;`
	/// edges — never a private one, which stays local to that namespace's
	/// own body lookups (a separate, richer walk that isn't this: own
	/// bindings, then *every* glob regardless of visibility, then the
	/// parent, then the prelude). Recurses via `lookup` at each hop, not
	/// into itself, so a re-export chain composes through direct
	/// declarations and further re-exports alike. Terminates because
	/// `compute_glob_item` already rejects a cycle in this exact edge set
	/// before it can be walked.
	fn indirect_lookup(
		&self,
		use_items: &[UseItemDef],
		namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup;

	/// What `namespace` exposes to an outside consumer, full stop —
	/// `direct_lookup`, falling back to `indirect_lookup`. What a named
	/// `use a::b;` and a glob `use a::*;` should both find when asking `a`
	/// for the same name.
	fn lookup(
		&self,
		use_items: &[UseItemDef],
		namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup;
}

/// One thing a name could resolve to: what it targets, and how visible it
/// was declared where it was actually found. The two travel together
/// everywhere a lookup result is consumed — an accessibility check and
/// re-export capping both need both at once.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct BindingCandidate {
	pub(super) target: BindingTarget,
	pub(super) visibility: Visibility,
}

/// The result of [`NamespaceLookup::lookup`]/[`NamespaceLookup::indirect_lookup`].
/// `Ambiguous` carries every surviving candidate paired with the `pub use`
/// edge responsible for it — the diagnostic needs to name each one, same as
/// two colliding ordinary globs already do. The same target reached through
/// two different edges is deduplicated before it ever becomes a candidate,
/// not after.
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum BindingLookup {
	NotFound,
	Found(BindingCandidate),
	Ambiguous(Box<[(BindingCandidate, SourceSpan)]>),
}

impl NamespaceLookup for [Namespace] {
	fn namespace_contains(
		&self,
		ancestor: NamespaceIndex,
		namespace: NamespaceIndex,
	) -> bool {
		let mut current = Some(namespace);
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
		declaring_namespace: NamespaceIndex,
		visibility: Visibility,
	) -> bool {
		match visibility {
			Visibility::Public => true,
			Visibility::Private => {
				self.namespace_contains(declaring_namespace, accessor)
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
		namespace: NamespaceIndex,
		key: BindingKey,
	) -> Option<BindingCandidate> {
		self[usize::from(namespace)].bindings.get(&key).map(
			|binding| BindingCandidate {
				target: binding.target,
				visibility: binding.visibility,
			},
		)
	}

	fn indirect_lookup(
		&self,
		use_items: &[UseItemDef],
		namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup {
		let mut candidates: Vec<(BindingCandidate, SourceSpan)> = Vec::new();
		for glob in self[usize::from(namespace)].glob_imports.iter() {
			let item = &use_items[usize::from(glob.use_item)];
			if item.pub_span.is_none() {
				continue;
			}
			let UseItemKind::Glob { span, .. } = item.kind else {
				unreachable!("a glob edge is always produced by a glob item")
			};
			let edge_span =
				SourceSpan::new(self[usize::from(namespace)].file_id, span);

			match self.lookup(use_items, glob.namespace, key) {
				BindingLookup::NotFound => {}
				BindingLookup::Found(candidate) => {
					push_candidate(&mut candidates, candidate, edge_span);
				}
				BindingLookup::Ambiguous(nested) => {
					for (candidate, span) in nested.iter().copied() {
						push_candidate(&mut candidates, candidate, span);
					}
				}
			}
		}

		match candidates.len() {
			0 => BindingLookup::NotFound,
			1 => BindingLookup::Found(candidates[0].0),
			_ => BindingLookup::Ambiguous(candidates.into_boxed_slice()),
		}
	}

	fn lookup(
		&self,
		use_items: &[UseItemDef],
		namespace: NamespaceIndex,
		key: BindingKey,
	) -> BindingLookup {
		match self.direct_lookup(namespace, key) {
			Some(candidate) => BindingLookup::Found(candidate),
			None => self.indirect_lookup(use_items, namespace, key),
		}
	}
}

/// Adds `candidate` to an in-progress ambiguity scan, unless the same
/// target is already there — the same target reached through two `pub`
/// edges (e.g. a diamond re-export) isn't a conflict, so it must be
/// deduplicated before it ever becomes a candidate rather than after.
fn push_candidate(
	candidates: &mut Vec<(BindingCandidate, SourceSpan)>,
	candidate: BindingCandidate,
	span: SourceSpan,
) {
	if candidates
		.iter()
		.any(|(existing, _)| existing.target == candidate.target)
	{
		return;
	}
	candidates.push((candidate, span));
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
		Self {
			target: BindingTarget::Accessible(key),
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
	Constant(DefId),
	AssociatedType(DefId),
}

impl MemberKind {
	pub fn def_id(self) -> DefId {
		match self {
			Self::Function(id) => id,
			Self::Constant(id) => id,
			Self::AssociatedType(id) => id,
		}
	}

	pub fn binding_namespace(self) -> BindingNamespace {
		match self {
			Self::AssociatedType(_) => BindingNamespace::Type,
			Self::Function(_) | Self::Constant(_) => BindingNamespace::Value,
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

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct TypeParamDef {
	pub name: Spanned<SymbolU32>,
	pub accesses: Vec<SourceSpan>,
}

impl TypeParamDef {
	pub fn new(name: Spanned<SymbolU32>) -> Self {
		Self {
			name,
			accesses: Vec::new(),
		}
	}
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
	) -> (Self, Vec<AstEntry<'ast>>) {
		DefinitionRegistryBuilder::build(packages, files, strings, diagnostics)
	}
}

impl<'ast, 'ctx> DefinitionRegistryBuilder<'ast, 'ctx> {
	fn build(
		packages: &'ast [Package],
		files: &'ctx Files,
		strings: &'ctx mut ast::StringInterner,
		diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
	) -> (DefinitionRegistry, Vec<AstEntry<'ast>>) {
		let package_namespaces: Vec<NamespaceIndex> = (0..packages.len())
			.into_iter()
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
						DefKind::Namespace(namespace_idx),
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
			traits: Vec::new(),
			trait_impls: Vec::new(),
			inherent_impls: Vec::new(),
			use_items: Vec::new(),
			use_paths: Vec::new(),
			pending_named_imports: HashMap::new(),
			pending_pub_glob_reexports: HashMap::new(),
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

		builder.resolve_use_paths();

		let registry = DefinitionRegistry {
			namespaces: builder.namespaces,
			package_namespaces: builder.package_namespaces,
			file_namespaces,
			module_decls: builder.module_decls,
			import_decls: builder.import_decls,
			traits: builder.traits,
			trait_impls: builder.trait_impls,
			inherent_impls: builder.inherent_impls,
			use_items: builder.use_items,
			use_paths: builder.use_paths,
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
		let mut namespace = Namespace {
			parent: Some(parent_namespace),
			file_id,
			package_id,
			kind,
			bindings: HashMap::new(),
			items: vec![ItemDef::new(
				DefKind::Namespace(namespace_idx),
				content_span,
			)],
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
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Function { item },
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
				id, pub_span, name, ..
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
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::RecordStruct { item },
				});
			}
			ast::Item::TupleStruct {
				id, pub_span, name, ..
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
					node: AstNodeRef::TupleStruct { item },
				});
			}
			ast::Item::Enum {
				id, pub_span, name, ..
			} => {
				let def_key = self.push_def(
					namespace,
					ItemDef::new(DefKind::Enum(*id), name.span),
				);
				self.insert_binding(
					namespace,
					BindingKey::ty(name.inner),
					Binding::definition(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Enum { item },
				});
			}
			ast::Item::TypeAlias {
				id, pub_span, name, ..
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
					let (member, key) = match &item.inner.inner {
						ast::TraitItem::Function { signature, id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitFunction {
									trait_index,
									item: &item.inner.inner,
								},
							});
							(
								TraitMemberDef {
									kind: MemberKind::Function(*id),
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
					let member_index =
						MemberIndex::new(u32::try_from(members.len()).unwrap());
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
						self_param: TypeParamDef::new(Spanned {
							inner: ast::Keyword::SelfPascal.symbol(),
							span: name.span,
						}),
						bindings,
						members,
					})
				);
			}
			ast::Item::InherentImpl {
				id: impl_id,
				type_params,
				items,
				..
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
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::InherentImplFunction {
									block_id: *impl_id,
									item: &impl_item.inner.inner,
									block_index,
								},
							});
							(
								InherentMemberDef {
									accesses: Vec::new(),
									kind: MemberKind::Function(*id),
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
									block_id: *impl_id,
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
						type_params: type_params
							.iter()
							.map(|tp| TypeParamDef::new(tp.name))
							.collect(),
						members,
						bindings,
						self_accesses: Vec::new(),
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
				id, name, pub_span, ..
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
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::TypeSet { item },
				});
			}
			ast::Item::TraitImpl {
				id: impl_id,
				items,
				type_params,
				..
			} => {
				let mut members: Vec<TraitMemberDef> = Vec::new();
				let mut bindings: HashMap<BindingKey, MemberIndex> =
					HashMap::new();
				self.ast_nodes.push(AstEntry {
					def_id: *impl_id,
					file_id,
					namespace,
					node: AstNodeRef::TraitImplBlock { item },
				});
				for item in items.iter() {
					let (member, key) = match &item.inner.inner {
						ast::ImplItem::Function { id, signature, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitImplFunction {
									parent_id: *impl_id,
									item: &item.inner.inner,
								},
							});
							(
								TraitMemberDef {
									accesses: Vec::new(),
									kind: MemberKind::Function(*id),
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
									parent_id: *impl_id,
									item: &item.inner.inner,
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
									parent_id: *impl_id,
									item: &item.inner.inner,
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

					let member_index =
						MemberIndex::new(u32::try_from(members.len()).unwrap());
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

				let mut params = Vec::with_capacity(type_params.len());
				for param in type_params.iter() {
					params.push(TypeParamDef {
						accesses: Vec::new(),
						name: param.name,
					});
					if let Some(collision) =
						params.iter().find(|p| p.name.inner == param.name.inner)
					{
						let name =
							self.strings.resolve(collision.name.inner).unwrap();
						self.diagnostics.push(
								Diagnostic::error()
									.with_code(
										DiagnosticCode::DuplicateGenericParam,
									)
									.with_message(format!(
										"the name `{name}` is already used for a generic parameter in this item's generic parameters"
									))
									.with_label(
										Label::primary(
											file_id,
											param.name.span,
										)
										.with_message("already used"),
									)
									.with_label(
										Label::secondary(
											file_id,
											collision.name.span,
										)
										.with_message(format!(
											"first use of `{}`",
											name
										)),
									),
							);
					}
				}

				self.push_trait_impl(TraitImplDef {
					def_id: *impl_id,
					file_id,
					namespace,
					self_accesses: Vec::new(),
					bindings,
					members,
					type_params: params.into_boxed_slice(),
				});
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
				if pub_span.is_some() {
					self.pending_pub_glob_reexports
						.entry(namespace)
						.and_modify(|items| items.push(item_index))
						.or_insert_with(|| SmallVec::new(item_index));
				}
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
}

impl<'ast, 'ctx> DefinitionRegistryBuilder<'ast, 'ctx> {
	fn resolve_use_paths(&mut self) {
		imports::resolve_use_paths(
			self.diagnostics,
			self.strings,
			&mut self.namespaces,
			&self.use_items,
			&self.use_paths,
			&self.pending_named_imports,
			&self.pending_pub_glob_reexports,
		);
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

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
				&mut graph.interner,
				&mut diagnostics,
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

		fn new_multi_file(
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

		fn root_namespace(&self) -> NamespaceIndex {
			self.defs.package_namespaces[self.graph.root_package.as_usize()]
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new("prescan", &self.diagnostics, &self.graph.files)
		}

		fn lookup_type(
			&mut self,
			namespace: NamespaceIndex,
			name: &str,
		) -> Option<BindingTarget> {
			let symbol = self.graph.interner.get_or_intern(name);
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
			let symbol = self.graph.interner.get_or_intern(name);
			self.defs.namespaces[usize::from(namespace)]
				.bindings
				.get(&BindingKey::value(symbol))
				.map(|binding| binding.target)
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
			match self.defs.namespaces[usize::from(def_key.namespace_idx)].items
				[usize::from(def_key.def_idx)]
			.kind
			{
				DefKind::Namespace(namespace) => namespace,
				other => panic!("`{name}` is not a module: {other:?}"),
			}
		}
	}

	#[test]
	fn function_and_struct_get_bindings() {
		let mut case = TestCase::new(indoc! {"
			pub fn add(a: i32, b: i32) -> i32 { a + b }
			struct Point { x: i32, y: i32 }
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let add_symbol = case.graph.interner.get_or_intern("add");
		let point_symbol = case.graph.interner.get_or_intern("Point");
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
	fn module_declared_in_another_file_gets_a_namespace() {
		let mut case = TestCase::new_multi_file(
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
}
