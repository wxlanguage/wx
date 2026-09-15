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
	tir::builder::unescape_string,
	vfs::{FileId, Files, Package, PackageId},
};

struct DefinitionRegistryBuilder<'a> {
	diagnostics: &'a mut Vec<Diagnostic<FileId>>,
	strings: &'a mut StringInterner,
	files: &'a Files,

	namespaces: Vec<Namespace>,
	package_namespaces: Vec<NamespaceIndex>,
	module_decls: Vec<ModuleDeclaration>,
	import_decls: Vec<ImportDeclaration>,
	ast_nodes: Vec<AstEntry<'a>>,
	traits: Vec<TraitDef>,
	trait_impls: Vec<TraitImplDef>,
	inherent_impls: Vec<InherentImplDef>,
	use_items: Vec<UseItemDef>,
	use_paths: Vec<UsePathSegment>,
}

index_newtype!(UsePathIndex);
index_newtype!(UseItemIndex);

struct UsePathSegment {
	segment: Spanned<SymbolU32>,
	parent: Option<UsePathIndex>,
}

pub enum UseItemKind {
	Name { alias: Option<Spanned<SymbolU32>> },
	Glob,
}

pub struct UseItemDef {
	pub namespace: NamespaceIndex,
	pub pub_span: Option<TextSpan>,
	pub path: UsePathIndex,
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
struct BindingKey {
	namespace: BindingNamespace,
	symbol: SymbolU32,
}

impl BindingKey {
	fn Type(symbol: SymbolU32) -> Self {
		Self {
			namespace: BindingNamespace::Type,
			symbol,
		}
	}

	fn Value(symbol: SymbolU32) -> Self {
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
struct AstEntry<'ast> {
	def_id: DefId,
	file_id: FileId,
	namespace: NamespaceIndex,
	node: AstNodeRef<'ast>,
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
enum AstNodeRef<'ast> {
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
struct NamespaceDef {
	kind: DefKind,
	span: TextSpan,
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
	pub defs: Vec<NamespaceDef>,
	/// Namespaces brought into scope via `use path::*;`.  Checked during lookup
	/// after direct symbols but before walking to the parent.
	pub glob_imports: Vec<GlobImport>,
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(serde::Serialize))]
enum BindingTarget {
	Def(DefKey),
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
struct Binding {
	target: BindingTarget,
	visibility: Visibility,
	accesses: Vec<SourceSpan>,
	source: BindingSource,
}

impl Binding {
	fn PrivateDef(key: DefKey) -> Self {
		Self {
			target: BindingTarget::Def(key),
			accesses: Vec::new(),
			visibility: Visibility::Private,
			source: BindingSource::Definition,
		}
	}

	fn PublicDef(key: DefKey) -> Self {
		Self {
			target: BindingTarget::Def(key),
			accesses: Vec::new(),
			visibility: Visibility::Public,
			source: BindingSource::Definition,
		}
	}

	fn Def(key: DefKey, visibility: Visibility) -> Self {
		Self {
			target: BindingTarget::Def(key),
			accesses: Vec::new(),
			visibility,
			source: BindingSource::Definition,
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

/// One `use path::*;` edge — the namespace it opens, plus where it was
/// written.
///
/// The span is what makes a wildcard ambiguity reportable: when two globs
/// supply the same name, the thing to point at is the `use` statements, not
/// the definitions (which are each perfectly fine on their own). Covers the
/// path and the star, `x::*`, not the `use` keyword — and for a glob nested
/// in a group (`use a::{b::*, c}`) only `b::*`, since a span reaching back
/// to `a` wouldn't be a contiguous range of source.
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct GlobImport {
	pub namespace: NamespaceIndex,
	pub span: SourceSpan,
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
	namespace_idx: NamespaceIndex,
	def_idx: LocalDefIndex,
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
	pub fn source_span(self, namespaces: &Vec<Namespace>) -> SourceSpan {
		let namespace = &namespaces[usize::from(self.namespace_idx)];
		SourceSpan::new(
			namespace.file_id,
			namespace.defs[usize::from(self.def_idx)].span,
		)
	}

	#[inline]
	pub fn text_span(self, namespaces: &Vec<Namespace>) -> TextSpan {
		namespaces[usize::from(self.namespace_idx)].defs
			[usize::from(self.def_idx)]
		.span
	}

	#[inline]
	pub fn symbol_kind(self, defs: &DefinitionRegistry) -> DefKind {
		let namespace = &defs.namespaces[usize::from(self.namespace_idx)];
		namespace.defs[usize::from(self.def_idx)].kind
	}
}

impl DefinitionRegistry {
	pub(super) fn record_access(&mut self, def_key: DefKey, span: SourceSpan) {
		self.namespaces[usize::from(def_key.namespace_idx)].defs
			[usize::from(def_key.def_idx)]
		.accesses
		.push(span);
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

struct DuplicateDefinitionDiagnostic<'strings> {
	pub(super) strings: &'strings ast::StringInterner,
	pub(super) key: BindingKey,
	pub(super) file_id: FileId,
	pub(super) definitions: (TextSpan, TextSpan),
}

impl DuplicateDefinitionDiagnostic<'_> {
	fn report(self) -> Diagnostic<FileId> {
		let name = self.strings.resolve(self.key.symbol).unwrap();

		let (a, b) = self.definitions;
		let (first, second) = if a.start <= b.start { (a, b) } else { (b, a) };

		Diagnostic::error()
			.with_code(DiagnosticCode::DuplicateDefinition.code())
			.with_message(format!(
				"the name `{name}` is defined multiple times"
			))
			.with_label(
				Label::primary(self.file_id, second)
					.with_message(format!("`{name}` redefined here")),
			)
			.with_label(Label::secondary(self.file_id, first).with_message(
				format!(
					"previous definition of the {} `{name}` here",
					self.key.namespace.noun(),
				),
			))
	}
}

impl DefinitionRegistry {
	pub(super) fn build(
		packages: &[Package],
		files: &Files,
		strings: &mut ast::StringInterner,
		diagnostics: &mut Vec<Diagnostic<FileId>>,
	) -> Self {
		DefinitionRegistryBuilder::build(packages, files, strings, diagnostics)
	}
}

impl<'a> DefinitionRegistryBuilder<'a> {
	fn build(
		packages: &[Package],
		files: &Files,
		strings: &mut ast::StringInterner,
		diagnostics: &mut Vec<Diagnostic<FileId>>,
	) -> DefinitionRegistry {
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
					defs: vec![NamespaceDef {
						kind: DefKind::Namespace(namespace_idx),
						span: TextSpan::new(0, 0),
					}],
					glob_imports: Vec::new(),
				};
				namespace.bindings.insert(
					BindingKey::Type(ast::Keyword::SelfLower.symbol()),
					Binding::PublicDef(DefKey::new(
						namespace_idx,
						LocalDefIndex::SELF,
					)),
				);
				namespace.bindings.insert(
					BindingKey::Type(ast::Keyword::Crate.symbol()),
					Binding::PublicDef(DefKey::new(
						namespace_idx,
						LocalDefIndex::SELF,
					)),
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
						BindingKey::Type(name),
						Binding::PublicDef(DefKey::new(
							package_namespaces[dependency_id.as_usize()],
							LocalDefIndex::SELF,
						)),
					);
				}

				namespace
			})
			.collect();

		let builder = Self {
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
		};

		let file_namespaces = builder.compute_file_namespaces(packages);
		for source_module in packages
			.iter()
			.flat_map(|package_graph| package_graph.modules.iter())
		{
			let namespace_idx =
				file_namespaces[source_module.file_id.as_usize()];
		}

		todo!()
	}

	fn compute_file_namespaces(
		&mut self,
		packages: &[Package],
	) -> Vec<NamespaceIndex> {
		let file_namespaces = Vec::new();
		for source_module in packages
			.iter()
			.flat_map(|package_graph| package_graph.modules.iter())
		{
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
					self.declare_child_namespace(
						parent_namespace,
						source_module.file_id,
						declaration.name.inner,
						NamespaceKind::Module(module_declaration_idx),
						TextSpan::new(0, u32::MAX),
						Visibility::from(declaration.pub_span),
					)
					.report_with(|collision| todo!());
					namespace_idx
				}
			};
			file_namespaces[source_module.file_id.as_usize()] = namespace_idx;
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
			u32::try_from(self.trait_impls.len()).unwrap(),
		);
		self.inherent_impls.push(item);
		index
	}

	fn push_use_path(&mut self, segment: UsePathSegment) -> UsePathIndex {
		let index =
			UsePathIndex::new(u32::try_from(self.trait_impls.len()).unwrap());
		self.use_paths.push(segment);
		index
	}

	fn push_def(
		&mut self,
		namespace_idx: NamespaceIndex,
		definition: NamespaceDef,
	) -> DefKey {
		let symbol_idx = LocalDefIndex::new(
			u32::try_from(
				self.namespaces[usize::from(namespace_idx)].defs.len(),
			)
			.unwrap(),
		);
		self.namespaces[usize::from(namespace_idx)]
			.defs
			.push(definition);
		DefKey::new(namespace_idx, symbol_idx)
	}

	fn try_insert_binding(
		&mut self,
		namespace_idx: NamespaceIndex,
		key: BindingKey,
		binding: Binding,
	) -> Option<DefKey> {
		use std::collections::hash_map::Entry;

		match self.namespaces[usize::from(namespace_idx)]
			.bindings
			.entry(key)
		{
			Entry::Vacant(entry) => {
				entry.insert(binding);
				None
			}
			Entry::Occupied(mut entry) => {
				match (entry.get().target, binding.target) {
					// Two actual bindings compete for the same name.
					(BindingTarget::Def(collision), BindingTarget::Def(_)) => {
						Some(collision)
					}
					// A real binding replaces previous recovery state.
					(BindingTarget::Error, BindingTarget::Def(_)) => {
						entry.insert(binding);
						None
					}
					// Recovery state must never hide a real binding.
					(BindingTarget::Def(_), BindingTarget::Error) => None,
					// Nothing useful to diagnose here.
					(BindingTarget::Error, BindingTarget::Error) => None,
				}
			}
		}
	}

	fn insert_binding(
		&mut self,
		namespace_idx: NamespaceIndex,
		key: BindingKey,
		binding: Binding,
		span: TextSpan,
	) {
		if let Some(collision_key) =
			self.try_insert_binding(namespace_idx, key, binding)
		{
			self.diagnostics.push(
				DuplicateDefinitionDiagnostic {
					strings: self.strings,
					key,
					file_id: self.namespaces[usize::from(namespace_idx)]
						.file_id,
					definitions: (
						collision_key.text_span(&self.namespaces),
						span,
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
			defs: vec![NamespaceDef {
				kind: DefKind::Namespace(namespace_idx),
				span: content_span,
			}],
			glob_imports: Vec::new(),
		};
		namespace.bindings.insert(
			BindingKey::Type(name),
			Binding::PublicDef(DefKey::new(namespace_idx, LocalDefIndex::SELF)),
		);

		let crate_root_namespace =
			self.package_namespaces[package_id.as_usize()];
		namespace.bindings.insert(
			BindingKey::Type(ast::Keyword::Crate.symbol()),
			Binding::PublicDef(DefKey::new(
				crate_root_namespace,
				LocalDefIndex::SELF,
			)),
		);
		namespace.bindings.insert(
			BindingKey::Type(ast::Keyword::Super.symbol()),
			Binding::PublicDef(DefKey::new(
				parent_namespace,
				LocalDefIndex::SELF,
			)),
		);
		self.namespaces.push(namespace);
		match self.try_insert_binding(
			parent_namespace,
			BindingKey::Type(name),
			Binding::Def(
				DefKey::new(namespace_idx, LocalDefIndex::SELF),
				visibility,
			),
		) {
			Some(collision) => {
				Declared::with_collision(namespace_idx, collision)
			}
			None => Declared::new(namespace_idx),
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

impl<'a> DefinitionRegistryBuilder<'a> {
	pub(super) fn scan_item(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		item: &'a ast::Item,
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
					NamespaceDef {
						kind: DefKind::Function(*id),
						span: signature.name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Value(signature.name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
				id,
				pub_span,
				mut_span,
				name,
				..
			} => {
				let def_key = self.push_def(
					namespace,
					NamespaceDef {
						kind: DefKind::Global(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Value(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
					NamespaceDef {
						kind: DefKind::Struct(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Type(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
					NamespaceDef {
						kind: DefKind::Struct(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Type(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
					name.span,
				);
				self.insert_binding(
					namespace,
					BindingKey::Value(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
					NamespaceDef {
						kind: DefKind::Enum(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Type(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
					NamespaceDef {
						kind: DefKind::TypeAlias(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Type(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
					NamespaceDef {
						kind: DefKind::Memory(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Type(name.inner),
					Binding::Def(def_key, Visibility::Private),
					name.span,
				);
				self.insert_binding(
					namespace,
					BindingKey::Value(name.inner),
					Binding::Def(def_key, Visibility::Private),
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
					NamespaceDef {
						kind: DefKind::Const(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Value(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
								key: BindingKey::Type(name.inner),
								file_id,
								definitions: (
									collision_key.text_span(&self.namespaces),
									name.span,
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
					NamespaceDef {
						kind: DefKind::Trait(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Type(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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

				let members: Vec<TraitMemberDef> = Vec::new();
				let bindings: HashMap<BindingKey, MemberIndex> = HashMap::new();
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
								BindingKey::Value(signature.name.inner),
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
								BindingKey::Value(name.inner),
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
								BindingKey::Type(name.inner),
							)
						}
					};
					let member_index =
						MemberIndex::new(u32::try_from(members.len()).unwrap());
					members.push(member);
					if let Some(collision) = bindings.get(&key).copied() {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key,
								file_id,
								definitions: (
									members[usize::from(collision)].span,
									member.span,
								),
							}
							.report(),
						);
					} else {
						bindings.insert(key, member_index);
					}
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
				target,
				items,
			} => {
				let members: Vec<InherentMemberDef> = Vec::new();
				let bindings: HashMap<BindingKey, (MemberIndex, Visibility)> =
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
									span: signature.name.span,
								},
								BindingKey::Value(signature.name.inner),
								(member_index, Visibility::from(*pub_span)),
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
									span: name.span,
								},
								BindingKey::Value(name.inner),
								(member_index, Visibility::from(*pub_span)),
							)
						}
						ast::ImplItem::AssocType { .. } => {
							todo!()
						}
					};
					members.push(member);
					if let Some((collision, _)) = bindings.get(&key).copied() {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key,
								file_id,
								definitions: (
									members[usize::from(collision)].span,
									member.span,
								),
							}
							.report(),
						);
					} else {
						bindings.insert(key, binding);
					}
				}

				let block_index = self.push_inherent_impl(InherentImplDef {
					def_id: *impl_id,
					file_id,
					namespace,
					type_params: type_params
						.iter()
						.map(|tp| TypeParamDef::new(tp.name))
						.collect(),
					members: Vec::new(),
					bindings: HashMap::new(),
					self_accesses: Vec::new(),
				});
			}
			ast::Item::Import {
				internal_name,
				external_name,
				items,
				id,
			} => {
				let external_name = {
					let unquoted =
						unescape_string(external_name.extract_str(
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
								key: BindingKey::Type(internal_name.inner),
								file_id,
								definitions: (
									collision.text_span(&self.namespaces),
									internal_name.span,
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
								NamespaceDef {
									kind: DefKind::Memory(*id),
									span: name.span,
								},
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::Type(name.inner),
								Binding::Def(def_key, Visibility::Public),
								name.span,
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::Value(name.inner),
								Binding::Def(def_key, Visibility::Public),
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
								NamespaceDef {
									kind: DefKind::Memory(*id),
									span: signature.name.span,
								},
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::Value(signature.name.inner),
								Binding::Def(def_key, Visibility::Public),
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
								NamespaceDef {
									kind: DefKind::Memory(*id),
									span: name.span,
								},
							);
							self.insert_binding(
								namespace_idx,
								BindingKey::Value(name.inner),
								Binding::Def(def_key, Visibility::Public),
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
				self.scan_use_tree(namespace, &tree.inner, None, *pub_span);
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
					NamespaceDef {
						kind: DefKind::TypeSet(*id),
						span: name.span,
					},
				);
				self.insert_binding(
					namespace,
					BindingKey::Type(name.inner),
					Binding::Def(def_key, Visibility::from(*pub_span)),
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
				let members: Vec<TraitMemberDef> = Vec::new();
				let bindings: HashMap<BindingKey, MemberIndex> = HashMap::new();
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
								BindingKey::Value(signature.name.inner),
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
								BindingKey::Value(name.inner),
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
								BindingKey::Type(name.inner),
							)
						}
					};

					let member_index =
						MemberIndex::new(u32::try_from(members.len()).unwrap());
					members.push(member);
					if let Some(collision) = bindings.get(&key).copied() {
						self.diagnostics.push(
							DuplicateDefinitionDiagnostic {
								strings: self.strings,
								key,
								file_id,
								definitions: (
									members[usize::from(collision)].span,
									member.span,
								),
							}
							.report(),
						);
					} else {
						bindings.insert(key, member_index);
					}
				}

				let params = Vec::with_capacity(type_params.len());
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
		tree: &ast::UseTree,
		parent_segment: Option<UsePathIndex>,
		pub_span: Option<TextSpan>,
	) {
		match tree {
			ast::UseTree::Name { segment, alias } => {
				let path = self.push_use_path(UsePathSegment {
					segment: *segment,
					parent: parent_segment,
				});
				self.use_items.push(UseItemDef {
					kind: UseItemKind::Name { alias: *alias },
					namespace,
					pub_span,
					path,
				});
			}
			ast::UseTree::Glob { segment } => {
				let path = self.push_use_path(UsePathSegment {
					segment: *segment,
					parent: parent_segment,
				});
				self.use_items.push(UseItemDef {
					kind: UseItemKind::Glob,
					namespace,
					pub_span,
					path,
				});
			}
			ast::UseTree::Path { segment, rest } => {
				let path = self.push_use_path(UsePathSegment {
					segment: *segment,
					parent: parent_segment,
				});
				self.scan_use_tree(
					namespace,
					&rest.inner,
					Some(path),
					pub_span,
				);
			}
			ast::UseTree::Group { segment, branches } => {
				let path = self.push_use_path(UsePathSegment {
					segment: *segment,
					parent: parent_segment,
				});
				for branch in branches.inner.iter() {
					self.scan_use_tree(
						namespace,
						&branch.inner.inner,
						Some(path),
						pub_span,
					);
				}
			}
		}
	}
}

#[derive(Clone, Copy)]
enum ImportScope {
	Namespace(NamespaceIndex),
	// TODO: Enum, Variant etc..
}

impl ImportScope {
	fn resolve_member(
		self,
		defs: &DefinitionRegistryBuilder,
		segment: Spanned<SymbolU32>,
	) {
		match self {
			ImportScope::Namespace(namespace) => {
				// ...
			}
		}
	}
}

#[derive(Clone, Copy)]
enum UsePathStatus {
	Pending,
	Resolving,
	Resolved(ImportScope),
	Error,
}

impl<'a> DefinitionRegistryBuilder<'a> {
	fn resolve_use_paths(&mut self) {
		let state: Vec<UsePathStatus> =
			vec![UsePathStatus::Pending; self.use_paths.len()];
		for item in self.use_items.iter() {
			let import_scope = match self.ensure_import_scope(
				item.namespace,
				item.path,
				&mut state,
			) {
				Ok(scope) => scope,
				Err(_) => continue,
			};
			match item.kind {
				UseItemKind::Glob => {}
				UseItemKind::Name { alias } => {}
			}

			todo!()
		}
	}

	fn ensure_import_scope(
		&mut self,
		origin: NamespaceIndex,
		path: UsePathIndex,
		cache: &mut [UsePathStatus],
	) -> Result<ImportScope, ()> {
		match cache[usize::from(path)] {
			UsePathStatus::Resolved(scope) => return Ok(scope),
			UsePathStatus::Error => return Err(()),
			UsePathStatus::Resolving => {
				// cyclic explicit re-export / path dependency
				// self.report_use_cycle(path);
				cache[usize::from(path)] = UsePathStatus::Error;
				return Err(());
			}
			UsePathStatus::Pending => {}
		}

		cache[usize::from(path)] = UsePathStatus::Resolving;

		let segment = self.use_paths[usize::from(path)];
		let result = match segment.parent {
			None => {
				let Some(binding) = self.namespaces[usize::from(origin)]
					.bindings
					.get(&BindingKey::Type(segment.segment.inner))
				else {
					// self.report_unresolved_use_segment(origin, segment);
					// return Err(())
					todo!()
				};

				self.binding_to_import_scope(binding, segment.segment.span)
			}
			Some(parent) => {
				let parent_scope =
					self.ensure_import_scope(origin, parent, cache)?;
				self.resolve_import_scope_member(
					origin,
					parent_scope,
					segment.segment,
				)
			}
		};

		match result {
			Ok(scope) => {
				cache[usize::from(path)] = UsePathStatus::Resolved(scope);
				Ok(scope)
			}
			Err(()) => {
				cache[usize::from(path)] = UsePathStatus::Error;
				Err(())
			}
		}
	}

	fn binding_to_import_scope(
		&mut self,
		binding: &Binding,
		span: TextSpan,
	) -> Result<ImportScope, ()> {
		if binding.visibility == Visibility::Private {
			// self.report_private_import(span, binding);
			return Err(());
		}
		let BindingTarget::Def(def_key) = binding.target else {
			return Err(());
		};

		let def = &self.namespaces[usize::from(def_key.namespace_idx)].defs
			[usize::from(def_key.def_idx)];
		match def.kind {
			DefKind::Namespace(namespace) => {
				Ok(ImportScope::Namespace(namespace))
			}
			_ => {
				// self.report_expected_import_scope(span, def.kind);
				Err(())
			}
		}
	}
}
