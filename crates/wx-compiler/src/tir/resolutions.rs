//! Every written name the compiler resolved, in one table.
//!
//! The table is built next to the diagnostics: phase 1 and impl dispatch
//! are lent it `&mut`, and `Semantics` then owns it. Phase 1 records the
//! segments of `use` paths, the path walk records every segment it resolves,
//! and signature construction records generic parameters and selected
//! members. Only code that has committed to a meaning records it, so a
//! lookup that is tried and discarded leaves no trace.
//!
//! Entries are keyed by where the name is written, so resolving the same
//! site again overwrites it instead of adding a second entry. The order is
//! by file and then position, which turns "what does the name under the
//! cursor mean" into a range lookup. Who refers to a definition, or which
//! `use` items are never used, is the inverse of this table and is computed
//! from it when needed.
//!
//! This is a reference table, not a token index: declaration names live in
//! their owning definition/body tables, and unresolved names have no entry.
//! Identities are local to one compilation; locals and labels need their body
//! owner, and fields need their struct because their indices are owner-relative.
//!
//! A written name can mean two things at one span: a `use` leaf names a type
//! and a value, and a shorthand argument (`f({ x })`, `S({ x })`) is a label
//! and the value it supplies. A `Site` says which role an entry is for,
//! so each meaning has an entry of its own: `Type` and `Value` are the
//! namespace tiers a name is looked up in, `Label` is a name that is not
//! looked up at all.

use std::collections::BTreeMap;

use super::body::{BodyOwner, LabelIdx, LocalIdx, ParamIdx};
use super::decls::{
	ConstIdx, DeclKey, DeclKind, FieldIdx, FunctionIdx, GlobalIdx,
	InherentImplIdx, MemberKind, StructIdx, Tier, TraitImplIdx, UseItemIndex,
};
use super::signatures::Semantics;
use super::types::{GenericEnvIdx, GenericEnvOwner};
use crate::diagnostics::{SourceSpan, TextSpan};
use crate::vfs::FileId;

/// Where a name is written, and the role it plays there; see the module doc.
/// Entries order by position first, so what is written at one place is
/// adjacent.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Site {
	/// Looked up among types.
	Type(SourceSpan),
	/// Looked up among values.
	Value(SourceSpan),
	/// A name that picks out a declaration by where it is written: a named
	/// argument's parameter or field, a `break`'s label.
	Label(SourceSpan),
}

impl Site {
	/// The site of a name looked up in `tier`.
	pub(super) fn new(tier: Tier, span: SourceSpan) -> Self {
		match tier {
			Tier::Type => Site::Type(span),
			Tier::Value => Site::Value(span),
		}
	}

	pub(super) fn span(self) -> SourceSpan {
		match self {
			Site::Type(span) | Site::Value(span) | Site::Label(span) => span,
		}
	}

	/// Which of the entries at one name is the one it means where it is
	/// used; see `Semantics::symbol_at`.
	fn priority(self) -> u8 {
		match self {
			Site::Value(_) => 2,
			Site::Type(_) => 1,
			Site::Label(_) => 0,
		}
	}

	fn role(self) -> u8 {
		match self {
			Site::Type(_) => 0,
			Site::Value(_) => 1,
			Site::Label(_) => 2,
		}
	}
}

impl Ord for Site {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		(self.span(), self.role()).cmp(&(other.span(), other.role()))
	}
}

impl PartialOrd for Site {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

#[derive(Default)]
pub(super) struct NameResolutions {
	pub(super) by_site: BTreeMap<Site, Reference>,
}

impl NameResolutions {
	pub(super) fn record(&mut self, site: Site, reference: Reference) {
		self.by_site.insert(site, reference);
	}

	pub(super) fn get(&self, site: Site) -> Option<Reference> {
		self.by_site.get(&site).copied()
	}

	#[cfg(test)]
	pub(super) fn references(&self) -> impl Iterator<Item = Reference> + '_ {
		self.by_site.values().copied()
	}

	/// Sets the access of the local recorded at `site`.
	pub(super) fn set_local_access(&mut self, site: Site, access: AccessKind) {
		if let Some(Reference::Local {
			access: recorded, ..
		}) = self.by_site.get_mut(&site)
		{
			*recorded = access;
		}
	}

	/// Makes the local or field recorded at `site` a plain read, for a name
	/// first recorded as written that turned out to be only read through.
	pub(super) fn downgrade_to_read(&mut self, site: Site) {
		if let Some(
			Reference::Local { access, .. } | Reference::Field { access, .. },
		) = self.by_site.get_mut(&site)
		{
			*access = AccessKind::Read;
		}
	}
}

/// One written name: what it refers to and how it was reached. Parameters
/// used in bodies are locals; a named argument's parameter identifies the
/// callee's declaration, not a read of it.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Reference {
	/// A declaration in the namespace the name was looked up in: an item, a
	/// module, a package or an import block.
	Item { item: DeclKey, route: Route },
	/// A local, a parameter included, of the body `owner`.
	Local {
		owner: BodyOwner,
		local: LocalIdx,
		access: AccessKind,
	},
	/// A field selected, matched or named by an argument.
	Field {
		owner: StructIdx,
		field: FieldIdx,
		access: AccessKind,
	},
	/// A named argument's parameter, owned by the declaration whose names the
	/// call uses (the trait declaration for a trait implementation's method).
	/// This does not require the callee to have a body or a corresponding
	/// local.
	Parameter {
		function: FunctionIdx,
		parameter: ParamIdx,
	},
	/// A generic parameter, or a trait's own `Self`: its frame and position
	/// in it.
	TypeParam { env: GenericEnvIdx, index: u32 },
	/// A member selected through a type: `T::A`, `<X as Tr>::A`.
	Member(MemberKind),
	/// A label of the body `owner`, named by a `break` or `continue`.
	Label { owner: BodyOwner, label: LabelIdx },
	/// `Self` inside an inherent impl, which names the impl's target and is
	/// not a parameter of it.
	InherentImplSelf(InherentImplIdx),
	/// `Self` inside a trait impl; see `InherentImplSelf`.
	TraitImplSelf(TraitImplIdx),
}

/// How a name reached the declaration it names.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Route {
	/// The declaration is in the namespace the name was looked up in.
	Direct,
	/// The namespace made the declaration visible through this `use` item, a
	/// named import or a glob. Only that first `use` is recorded; one it
	/// leads through in another namespace can be found again by looking the
	/// name up from it.
	Import(UseItemIndex),
}

/// How a use reaches a local or a field.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum AccessKind {
	Read,
	Write,
	ReadWrite,
	/// A constructor's field label gives the field its value.
	Initialize,
}

/// A declared name: what a written name can be declared as. A reference
/// refers to one (`Reference::definition`), and the declaration is written
/// at `Semantics::definition_span`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Definition {
	Item(DeclKey),
	Local {
		owner: BodyOwner,
		local: LocalIdx,
	},
	Field {
		owner: StructIdx,
		field: FieldIdx,
	},
	Parameter {
		function: FunctionIdx,
		parameter: ParamIdx,
	},
	TypeParam {
		env: GenericEnvIdx,
		index: u32,
	},
	Member(MemberKind),
	Label {
		owner: BodyOwner,
		label: LabelIdx,
	},
	/// What `Self` names in an inherent impl: the target type written in its
	/// header.
	InherentImplTarget(InherentImplIdx),
	/// What `Self` names in a trait impl; see `InherentImplTarget`.
	TraitImplTarget(TraitImplIdx),
}

impl Reference {
	/// What a namespace lookup found: `import` is the `use` item it came
	/// through, as `BindingLookup::Found` reports it.
	pub(super) fn from_lookup(
		declaration: DeclKey,
		import: Option<UseItemIndex>,
	) -> Self {
		Self::Item {
			item: declaration,
			route: import.map_or(Route::Direct, Route::Import),
		}
	}

	/// The declaration this refers to, without how it was reached.
	pub fn definition(self) -> Definition {
		match self {
			Reference::Item { item, .. } => Definition::Item(item),
			Reference::Local { owner, local, .. } => {
				Definition::Local { owner, local }
			}
			Reference::Field { owner, field, .. } => {
				Definition::Field { owner, field }
			}
			Reference::Parameter {
				function,
				parameter,
			} => Definition::Parameter {
				function,
				parameter,
			},
			Reference::TypeParam { env, index } => {
				Definition::TypeParam { env, index }
			}
			Reference::Member(kind) => Definition::Member(kind),
			Reference::Label { owner, label } => {
				Definition::Label { owner, label }
			}
			Reference::InherentImplSelf(index) => {
				Definition::InherentImplTarget(index)
			}
			Reference::TraitImplSelf(index) => {
				Definition::TraitImplTarget(index)
			}
		}
	}
}

impl Semantics {
	/// What the name written at `offset` in `file` resolved to, with the span
	/// of the name. `None` when no resolved name is written there.
	///
	/// Names do not nest, so the entry is the last one starting at or before
	/// `offset`. One written name can hold up to three entries (the roles of
	/// one site: a `use` leaf is a type and a value, a shorthand argument is
	/// a label and a value); the value wins, then the type, then the label,
	/// which is what the name means where it is used.
	pub fn symbol_at(
		&self,
		file: FileId,
		offset: u32,
	) -> Option<(SourceSpan, Reference)> {
		let probe = Site::Label(SourceSpan::new(
			file,
			TextSpan {
				start: offset,
				end: u32::MAX,
			},
		));
		let mut found: Option<(SourceSpan, Site, Reference)> = None;
		for (site, reference) in self.resolutions.by_site.range(..=probe).rev()
		{
			let span = site.span();
			if span.file_id != file || span.span.end < offset {
				break;
			}
			if found.is_some_and(|(found, ..)| found != span) {
				break;
			}
			// A zero-width synthetic span never covers a cursor.
			if span.span.start == span.span.end {
				continue;
			}
			if found
				.is_none_or(|(_, kept, _)| site.priority() > kept.priority())
			{
				found = Some((span, *site, *reference));
			}
		}
		found.map(|(span, _, reference)| (span, reference))
	}

	/// Where the definition of the name written at `offset` in `file` is
	/// declared: the declaring name's span (a module's or an import block's
	/// content, for those). `None` when no resolved name is written there, or
	/// its target has no written name (`Self` in an impl, a package).
	pub fn definition_at(
		&self,
		file: FileId,
		offset: u32,
	) -> Option<SourceSpan> {
		let (_, reference) = self.symbol_at(file, offset)?;
		self.definition_target(reference.definition())
	}

	/// What kind of declaration `key` names.
	pub fn declaration_kind(&self, key: DeclKey) -> DeclKind {
		key.symbol_kind(&self.decls)
	}

	/// Where go-to-definition leads for `definition`: where it is declared,
	/// except a module in a file of its own, which leads to the start of that
	/// file, its contents.
	pub fn definition_target(
		&self,
		definition: Definition,
	) -> Option<SourceSpan> {
		if let Definition::Item(key) = definition
			&& let DeclKind::Module(index) = self.declaration_kind(key)
		{
			let module = &self.decls.modules[usize::from(index)];
			if module.own_file != module.declaration_file {
				return Some(SourceSpan::new(
					module.own_file,
					TextSpan { start: 0, end: 0 },
				));
			}
		}
		self.definition_span(definition)
	}

	/// Where `definition` is declared: the declaring name's span, or `None`
	/// when the target has no written name.
	pub fn definition_span(
		&self,
		definition: Definition,
	) -> Option<SourceSpan> {
		let decls = &self.decls;
		match definition {
			Definition::Item(key) => Some(decls.declaration_span(key)),
			Definition::TypeParam { env, index } => {
				let name =
					self.generic_envs.param_names(env).get(index as usize)?;
				let file = self.env_owner_file(self.generic_envs.owner(env));
				Some(SourceSpan::new(file, name.span))
			}
			Definition::Member(kind) => {
				let (file, name) = match kind {
					MemberKind::Function(function)
					| MemberKind::Method(function) => {
						let function = &decls.functions[usize::from(function)];
						(function.file_id, function.name)
					}
					MemberKind::Constant(constant) => {
						let constant = &decls.constants[usize::from(constant)];
						(constant.file_id, constant.name)
					}
					MemberKind::AssociatedType(assoc) => {
						let assoc = &decls.assoc_types[usize::from(assoc)];
						(assoc.file_id, assoc.name)
					}
				};
				Some(SourceSpan::new(file, name.span))
			}
			Definition::Label { owner, label } => {
				let body = self.owner_body(owner)?;
				Some(SourceSpan::new(
					self.owner_file(owner),
					body.label(label).name.span,
				))
			}
			Definition::Local { owner, local } => {
				let body = self.owner_body(owner)?;
				Some(SourceSpan::new(
					self.owner_file(owner),
					body.local(local).name.span,
				))
			}
			Definition::Field { owner, field } => {
				self.field_definition(owner, field)
			}
			Definition::InherentImplTarget(index) => {
				let header =
					self.inherent_impls[usize::from(index)].as_ref()?;
				let file = decls.inherent_impls[usize::from(index)].file_id;
				Some(SourceSpan::new(file, header.target.span))
			}
			Definition::TraitImplTarget(index) => {
				let header = self.trait_impls[usize::from(index)].as_ref()?;
				let file = decls.trait_impls[usize::from(index)].file_id;
				Some(SourceSpan::new(file, header.target.span))
			}
			Definition::Parameter {
				function,
				parameter,
			} => {
				let function = &decls.functions[usize::from(function)];
				let name =
					function.params.get(usize::from(parameter))?.as_ref()?;
				Some(SourceSpan::new(function.file_id, name.span))
			}
		}
	}

	/// Every declared name that has a written name, with where it is written.
	/// Where two share a span (a memory and the `Size` its synthetic impl
	/// declares at its name, a trait and its `Self`), the item wins.
	pub fn definitions(&self) -> BTreeMap<SourceSpan, Definition> {
		let decls = &self.decls;
		let mut found = BTreeMap::new();
		let mut add = |definition: Definition| {
			if let Some(span) = self.definition_span(definition)
				&& span.span.start != span.span.end
			{
				found.insert(span, definition);
			}
		};
		for member in decls.traits.iter().flat_map(|decl| &decl.members) {
			add(Definition::Member(member.kind));
		}
		for member in decls.trait_impls.iter().flat_map(|decl| &decl.members) {
			add(Definition::Member(member.kind));
		}
		for member in decls.inherent_impls.iter().flat_map(|decl| &decl.members)
		{
			add(Definition::Member(member.kind));
		}
		for (index, decl) in decls.structs.iter().enumerate() {
			let owner = StructIdx::new(index as u32);
			for field in 0..decl.field_names.len() {
				add(Definition::Field {
					owner,
					field: FieldIdx::new(field as u32),
				});
			}
		}
		for env in self.generic_envs.frames() {
			for index in 0..self.generic_envs.param_names(env).len() {
				add(Definition::TypeParam {
					env,
					index: index as u32,
				});
			}
		}
		for index in 0..decls.functions.len() {
			let function = FunctionIdx::new(index as u32);
			let owner = BodyOwner::Function(function);
			// A parameter of a function with a body is a local of it; the
			// others are known by the declaration alone.
			if self.owner_body(owner).is_none() {
				for parameter in 0..decls.functions[index].params.len() {
					add(Definition::Parameter {
						function,
						parameter: ParamIdx::new(parameter as u32),
					});
				}
			}
			self.add_body_definitions(owner, &mut add);
		}
		for index in 0..decls.constants.len() {
			let owner = BodyOwner::Const(ConstIdx::new(index as u32));
			self.add_body_definitions(owner, &mut add);
		}
		for index in 0..decls.globals.len() {
			let owner = BodyOwner::Global(GlobalIdx::new(index as u32));
			self.add_body_definitions(owner, &mut add);
		}
		for key in decls.namespaces.keys() {
			if !matches!(self.declaration_kind(key), DeclKind::Package(_)) {
				add(Definition::Item(key));
			}
		}
		found
	}

	fn add_body_definitions(
		&self,
		owner: BodyOwner,
		add: &mut impl FnMut(Definition),
	) {
		let Some(body) = self.owner_body(owner) else {
			return;
		};
		for index in 0..body.locals().len() {
			add(Definition::Local {
				owner,
				local: LocalIdx::new(index as u32),
			});
		}
		for index in 0..body.labels().len() {
			add(Definition::Label {
				owner,
				label: LabelIdx::new(index as u32),
			});
		}
	}

	fn field_definition(
		&self,
		owner: StructIdx,
		field: FieldIdx,
	) -> Option<SourceSpan> {
		let decl = &self.decls.structs[usize::from(owner)];
		let name = decl.field_names.get(usize::from(field))?.as_ref()?;
		Some(SourceSpan::new(decl.file_id, name.span))
	}

	/// The checked body of `owner`, if it has one.
	pub fn owner_body(&self, owner: BodyOwner) -> Option<&super::body::Body> {
		match owner {
			BodyOwner::Const(constant) => self.const_body(constant),
			BodyOwner::Function(function) => self.function_implementations
				[usize::from(function)]
			.body()
			.map(|body| self.body(body)),
			BodyOwner::Global(global) => self.global_bodies
				[usize::from(global)]
			.map(|body| self.body(body)),
		}
	}

	fn owner_file(&self, owner: BodyOwner) -> FileId {
		match owner {
			BodyOwner::Const(index) => {
				self.decls.constants[usize::from(index)].file_id
			}
			BodyOwner::Function(index) => {
				self.decls.functions[usize::from(index)].file_id
			}
			BodyOwner::Global(index) => {
				self.decls.globals[usize::from(index)].file_id
			}
		}
	}

	fn env_owner_file(&self, owner: GenericEnvOwner) -> FileId {
		let decls = &self.decls;
		match owner {
			GenericEnvOwner::Constant(index) => {
				decls.constants[usize::from(index)].file_id
			}
			GenericEnvOwner::Enum(index) => {
				decls.enums[usize::from(index)].file_id
			}
			GenericEnvOwner::Struct(index) => {
				decls.structs[usize::from(index)].file_id
			}
			GenericEnvOwner::Function(index) => {
				decls.functions[usize::from(index)].file_id
			}
			GenericEnvOwner::Trait(index) => {
				decls.traits[usize::from(index)].file_id
			}
			GenericEnvOwner::TypeAlias(index) => {
				decls.type_aliases[usize::from(index)].file_id
			}
			GenericEnvOwner::InherentImpl(index) => {
				decls.inherent_impls[usize::from(index)].file_id
			}
			GenericEnvOwner::TraitImpl(index) => {
				decls.trait_impls[usize::from(index)].file_id
			}
		}
	}
}

#[cfg(test)]
mod tests {
	#[derive(Debug, PartialEq, Eq)]
	struct Shorthand {
		label: Reference,
		value: Reference,
	}

	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::{Diagnostics, TextSpan};
	use crate::tir::body::Local;
	use crate::tir::decls::{BindingKey, DeclKind, Scope};
	use crate::tir::impls::ImplTarget;
	use crate::tir::paths::PathResolver;
	use crate::tir::signatures::Semantics;
	use crate::vfs::{self, FileId};

	struct Analysis<'s> {
		source: &'s str,
		file: FileId,
		strings: StringInterner,
		sema: Semantics,
	}

	impl<'s> Analysis<'s> {
		fn new(source: &'s str) -> Self {
			let mut strings = ast::Keyword::create_interner();
			let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
			builder.load_stdlib();
			let root = builder
				.load_binary(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(
						std::collections::HashMap::from([(
							"main.wx".to_string(),
							source.to_string(),
						)]),
					),
				)
				.unwrap();
			let compilation = builder.build(root);
			let parse_diagnostics = compilation.collect_diagnostics();
			assert!(!parse_diagnostics.has_errors(), "{parse_diagnostics:?}");
			let sema = crate::tir::check(&compilation, &mut strings);
			let file =
				sema.decls.namespaces.file_id(Scope::Package(root).into());
			Self {
				source,
				file,
				strings,
				sema,
			}
		}

		fn clean(source: &'s str) -> Self {
			let analysis = Self::new(source);
			assert!(
				!analysis.has_errors(),
				"{:?}",
				analysis.sema.diagnostics.errors().collect::<Vec<_>>()
			);
			analysis
		}

		fn has_errors(&self) -> bool {
			self.sema.diagnostics.has_errors()
		}

		/// The local `index` of the body of the function `function`.
		fn local(&self, function: FunctionIdx, index: usize) -> &Local {
			let body = self.sema.function_implementations
				[usize::from(function)]
			.body()
			.expect("a function with a block has a body");
			&self.sema.body(body).locals()[index]
		}

		fn at(
			&self,
			context: &str,
			name: &str,
			tier: Tier,
		) -> Option<Reference> {
			let span = self.span(context, name);
			self.sema
				.resolutions
				.get(Site::new(tier, SourceSpan::new(self.file, span)))
		}

		/// The label recorded at `name`: an argument's or a jump's.
		fn label(&self, context: &str, name: &str) -> Reference {
			let span = self.span(context, name);
			self.sema
				.resolutions
				.get(Site::Label(SourceSpan::new(self.file, span)))
				.unwrap_or_else(|| {
					panic!("label `{name}` in `{context}` was not recorded")
				})
		}

		/// A shorthand argument: its label and the value it supplies.
		fn shorthand(&self, context: &str, name: &str) -> Option<Shorthand> {
			Some(Shorthand {
				label: self.label(context, name),
				value: self.at(context, name, Tier::Value)?,
			})
		}

		fn span(&self, context: &str, name: &str) -> TextSpan {
			let start = self.source.find(context).unwrap()
				+ context.find(name).unwrap();
			TextSpan::new(start as u32, (start + name.len()) as u32)
		}

		fn value(&self, context: &str, name: &str) -> Reference {
			self.at(context, name, Tier::Value).unwrap_or_else(|| {
				panic!("`{name}` in `{context}` was not recorded")
			})
		}

		fn reference(&self, context: &str, name: &str) -> Reference {
			self.at(context, name, Tier::Value).unwrap_or_else(|| {
				panic!("expected a reference for `{name}` in `{context}`")
			})
		}

		fn resolve(&self, path: &str, tier: Tier) -> DeclKind {
			self.declaration(path, tier).symbol_kind(&self.sema.decls)
		}

		fn declaration(&self, path: &str, tier: Tier) -> DeclKey {
			let segments: Box<[ast::PathSegment]> = path
				.split("::")
				.map(|name| ast::PathSegment {
					ident: Spanned {
						inner: self.strings.get(name).unwrap(),
						span: TextSpan::new(0, 0),
					},
					type_args: Box::new([]),
				})
				.collect();
			// Keep synthetic lookup spans out of the table under test.
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let target = PathResolver::new(
				&mut diagnostics,
				&mut resolutions,
				&self.strings,
				&self.sema.decls,
			)
			.resolve_path(
				self.file,
				Scope::Package(self.sema.decls.root_package),
				&segments,
				tier,
			);
			assert!(diagnostics.is_empty(), "{diagnostics:?}");
			target
				.decl_key()
				.unwrap_or_else(|| panic!("expected `{path}` to resolve"))
		}

		fn struct_index(&self, path: &str) -> StructIdx {
			let DeclKind::Struct(index) = self.resolve(path, Tier::Type) else {
				panic!("expected `{path}` to name a struct");
			};
			index
		}

		fn function_index(&self, path: &str) -> FunctionIdx {
			let DeclKind::Function(index) = self.resolve(path, Tier::Value)
			else {
				panic!("expected `{path}` to name a function");
			};
			index
		}

		fn trait_member(
			&self,
			path: &str,
			name: &str,
			tier: Tier,
		) -> MemberKind {
			let DeclKind::Trait(index) = self.resolve(path, Tier::Type) else {
				panic!("expected `{path}` to name a trait");
			};
			self.sema
				.decls
				.declared_trait_member(
					index,
					BindingKey::new(tier, self.strings.get(name).unwrap()),
				)
				.unwrap()
		}
	}

	#[test]
	fn local_reads_writes_and_shadowing_keep_their_identity() {
		let a = Analysis::clean(indoc! {"
			func f(x: u32) -> u32 {
				local mut y = x;
				y = x + 1;
				y += 2;
				local _ = block {
					local y: u32 = 3;
					y
				};
				y
			}
		"});
		let x = a.value("= x;", "x");
		let y = a.value("y = x +", "y");
		assert!(matches!(x, Reference::Local { .. }));
		assert!(matches!(y, Reference::Local { .. }));
		assert_ne!(x, y);
		assert_eq!(x, a.value("= x +", "x"));
		let Reference::Local {
			owner,
			local,
			access: AccessKind::Write,
		} = y
		else {
			panic!()
		};
		assert_eq!(
			a.value("y +=", "y"),
			Reference::Local {
				owner,
				local,
				access: AccessKind::ReadWrite
			}
		);
		assert_eq!(
			a.value("\n\ty\n", "y"),
			Reference::Local {
				owner,
				local,
				access: AccessKind::Read
			}
		);
		assert_ne!(y, a.value("\n\t\ty\n", "y"));
		// Bindings are declarations, not references.
		assert_eq!(a.at("mut y =", "y", Tier::Value), None);
	}

	#[test]
	fn locals_in_different_bodies_do_not_alias() {
		let a = Analysis::clean(indoc! {"
			func f(x: u32) -> u32 { x }
			func g(x: u32) -> u32 { x + 1 }
		"});
		let Reference::Local {
			owner: f,
			local: x,
			access: AccessKind::Read,
		} = a.value("{ x }", "x")
		else {
			panic!()
		};
		let Reference::Local {
			owner: g,
			local: y,
			access: AccessKind::Read,
		} = a.value("{ x +", "x")
		else {
			panic!()
		};
		assert_eq!(x, y);
		assert_ne!(f, g);
	}

	#[test]
	fn destructured_bindings_are_recorded_when_read() {
		let a = Analysis::clean(indoc! {"
			func f(p: (u32, u32)) -> u32 {
				local (left, right) = p;
				left + right
			}
		"});
		let left = a.value("left +", "left");
		let right = a.value("+ right", "right");
		assert!(matches!(left, Reference::Local { .. }));
		assert!(matches!(right, Reference::Local { .. }));
		assert_ne!(left, right);
	}

	#[test]
	fn paths_record_each_segment_and_import_provenance() {
		let a = Analysis::clean(indoc! {"
			mod m {
				pub func run() {}
			}
			use m::run as alias;
			func f() {
				m::run();
				alias();
			}
		"});
		assert!(matches!(
			a.at("m::run();", "m", Tier::Type),
			Some(Reference::Item {
				item: _,
				route: Route::Direct
			})
		));
		let Reference::Item {
			item: direct,
			route: Route::Direct,
		} = a.value("m::run();", "run")
		else {
			panic!()
		};
		let Reference::Item {
			item: declaration,
			route: Route::Import(_),
		} = a.value("alias();", "alias")
		else {
			panic!()
		};
		assert_eq!(direct, declaration);
	}

	#[test]
	fn generic_type_references_and_method_names_are_recorded() {
		let a = Analysis::clean(indoc! {"
			struct S();
			impl S {
				func get(self: Self) -> u32 { 1 }
			}
			func f<T: StackValue>(x: T, s: S) -> T {
				local _ = s.get();
				x
			}
		"});
		assert!(matches!(
			a.at("x: T", "T", Tier::Type),
			Some(Reference::TypeParam { .. })
		));
		assert_eq!(
			a.at("x: T", "T", Tier::Type),
			a.at("-> T", "T", Tier::Type)
		);
		assert!(matches!(
			a.value("s.get()", "get"),
			Reference::Member(MemberKind::Method(_))
		));
	}

	#[test]
	fn field_reads_and_assignment_targets_record_owner_relative_identity() {
		let a = Analysis::clean(indoc! {"
			struct A(value: u32);
			struct B(value: u32);
			func f(mut a: A, b: B) -> u32 {
				a.value = b.value;
				a.value
			}
		"});
		let first = a.reference("a.value =", "value");
		assert_eq!(
			first,
			Reference::Field {
				owner: a.struct_index("A"),
				field: FieldIdx::new(0),
				access: AccessKind::Write,
			}
		);
		assert_eq!(
			a.reference("\n\ta.value\n", "value"),
			Reference::Field {
				owner: a.struct_index("A"),
				field: FieldIdx::new(0),
				access: AccessKind::Read
			}
		);
		let Reference::Field {
			owner: a_owner,
			field: a_field,
			access: AccessKind::Write,
		} = first
		else {
			panic!()
		};
		let Reference::Field {
			owner: b_owner,
			field: b_field,
			access: AccessKind::Read,
		} = a.reference("b.value;", "value")
		else {
			panic!()
		};
		assert_eq!(
			a.reference("b.value;", "value"),
			Reference::Field {
				owner: a.struct_index("B"),
				field: FieldIdx::new(0),
				access: AccessKind::Read,
			}
		);
		assert_eq!(a_field, b_field);
		assert_ne!(a_owner, b_owner);
	}

	#[test]
	fn unresolved_names_do_not_erase_resolved_neighbors() {
		let a = Analysis::new(indoc! {"
			func f(x: u32) {
				x;
				missing;
				x;
			}
		"});
		assert!(a.has_errors());
		assert_eq!(a.at("missing;", "missing", Tier::Value), None);
		assert_eq!(a.value("\n\tx;\n", "x"), a.value("missing;\n\tx;", "x"));
	}

	#[test]
	fn named_arguments_record_labels_and_both_shorthand_references() {
		let a = Analysis::clean(indoc! {"
			func take(x: u32) {}
			func f(x: u32) -> u32 {
				take({ x: 1 });
				take({ x });
				x
			}
		"});
		let selection = Reference::Parameter {
			function: a.function_index("take"),
			parameter: ParamIdx::new(0),
		};
		assert_eq!(a.label("{ x: 1", "x"), selection);
		assert_eq!(
			a.shorthand("{ x }", "x"),
			Some(Shorthand {
				label: selection,
				value: a.value("\n\tx\n", "x"),
			})
		);
	}

	#[test]
	fn constructor_arguments_record_fields_and_both_shorthand_references() {
		let a = Analysis::clean(indoc! {"
			struct S(other: u32, value: u32);
			func f(value: u32) -> u32 {
				local _ = S({ other: 0, value: 1 });
				local _ = S({ other: 0, value });
				value
			}
		"});
		let field = Reference::Field {
			owner: a.struct_index("S"),
			field: FieldIdx::new(1),
			access: AccessKind::Initialize,
		};
		assert_eq!(a.label("value: 1", "value"), field);
		assert_eq!(
			a.shorthand("value });", "value"),
			Some(Shorthand {
				label: field,
				value: a.value("\n\tvalue\n", "value"),
			})
		);
	}

	#[test]
	fn shorthand_can_supply_an_imported_constant_instead_of_a_local() {
		let a = Analysis::clean(indoc! {"
			mod m { pub const value: u32 = 7; }
			use m::value;
			func take(value: u32) {}
			func f() -> u32 {
				take({ value });
				value
			}
		"});
		let value = a.value("\n\tvalue\n", "value");
		assert!(matches!(
			value,
			Reference::Item {
				route: Route::Import(_),
				..
			}
		));
		assert_eq!(
			a.shorthand("{ value }", "value"),
			Some(Shorthand {
				label: Reference::Parameter {
					function: a.function_index("take"),
					parameter: ParamIdx::new(0),
				},
				value,
			})
		);
	}

	#[test]
	fn unresolved_shorthand_values_still_record_the_parameter() {
		let a = Analysis::new(indoc! {"
			func take(value: u32) {}
			func f() {
				take({ value });
			}
		"});
		assert!(a.has_errors());
		assert_eq!(
			a.label("{ value }", "value"),
			Reference::Parameter {
				function: a.function_index("take"),
				parameter: ParamIdx::new(0),
			}
		);
	}

	#[test]
	fn unknown_argument_labels_do_not_erase_shorthand_value_references() {
		let a = Analysis::new(indoc! {"
			func take(other: u32) {}
			func f(value: u32) -> u32 {
				take({ value });
				value
			}
		"});
		assert!(a.has_errors());
		assert_eq!(
			a.value("{ value }", "value"),
			a.value("\n\tvalue\n", "value")
		);
	}

	#[test]
	fn trait_argument_labels_refer_to_the_naming_declaration_without_a_body() {
		let a = Analysis::clean(indoc! {"
			trait Make: StackValue {
				func make(value: u32) -> Self;
			}
			struct S(value: u32);
			impl Make for S {
				func make(_: u32) -> Self { S(0) }
			}
			func concrete(value: u32) -> S {
				S::make({ value })
			}
			func generic<T: Make>(value: u32) -> T {
				T::make({ value })
			}
		"});
		let DeclKind::Trait(trait_index) = a.resolve("Make", Tier::Type) else {
			panic!("expected a trait");
		};
		let Some(MemberKind::Function(function)) =
			a.sema.decls.declared_trait_member(
				trait_index,
				crate::tir::decls::BindingKey::value(
					a.strings.get("make").unwrap(),
				),
			)
		else {
			panic!("expected the trait's function declaration");
		};
		for (call, caller) in [
			("S::make({ value })", "concrete"),
			("T::make({ value })", "generic"),
		] {
			assert_eq!(
				a.shorthand(call, "value"),
				Some(Shorthand {
					label: Reference::Parameter {
						function,
						parameter: ParamIdx::new(0),
					},
					value: Reference::Local {
						owner: BodyOwner::Function(a.function_index(caller)),
						local: LocalIdx::new(0),
						access: AccessKind::Read,
					},
				})
			);
		}
	}

	#[test]
	fn named_pattern_fields_refer_to_the_same_field_as_an_access() {
		let a = Analysis::clean(indoc! {"
			struct S(value: u32);
			func f(s: S) -> u32 {
				local _ = s.value;
				local S({ value: x }) = s;
				x
			}
		"});
		assert_eq!(
			a.reference("{ value: x", "value"),
			Reference::Field {
				owner: a.struct_index("S"),
				field: FieldIdx::new(0),
				access: AccessKind::Read,
			}
		);
		assert_eq!(
			a.reference("{ value: x", "value"),
			a.reference("s.value;", "value")
		);
		assert!(matches!(a.value("\n\tx\n", "x"), Reference::Local { .. }));
	}

	#[test]
	fn field_selection_through_a_pointer_uses_the_struct_identity() {
		let a = Analysis::clean(indoc! {"
			memory heap: u32;
			struct S(value: u32);
			func f(p: heap::*S, s: S) -> u32 {
				p.value = s.value;
				p.value
			}
		"});
		assert_eq!(
			a.reference("p.value =", "value"),
			Reference::Field {
				owner: a.struct_index("S"),
				field: FieldIdx::new(0),
				access: AccessKind::Write,
			}
		);
		assert_eq!(
			a.reference("\n\tp.value\n", "value"),
			a.reference("s.value;", "value")
		);
		assert_ne!(
			a.reference("p.value =", "value"),
			a.reference("\n\tp.value\n", "value")
		);
	}

	#[test]
	fn labelled_break_and_continue_refer_to_the_same_label() {
		let a = Analysis::clean(indoc! {"
			func f(c: Bool) {
				loop :outer {
					if c { continue :outer; }
					break :outer;
				}
			}
		"});
		let label = a.label("break :outer", "outer");
		assert!(matches!(label, Reference::Label { .. }));
		assert_eq!(label, a.label("continue :outer", "outer"));
		assert_eq!(a.at("loop :outer", "outer", Tier::Value), None);
	}

	#[test]
	fn a_failed_path_retains_only_its_resolved_prefix() {
		let a = Analysis::new(indoc! {"
			mod m {}
			func f() {
				m::missing();
			}
		"});
		assert!(a.has_errors());
		assert!(matches!(
			a.at("m::missing", "m", Tier::Type),
			Some(Reference::Item {
				item: _,
				route: Route::Direct
			})
		));
		assert_eq!(a.at("m::missing", "missing", Tier::Value), None);
	}

	#[test]
	fn private_fields_are_resolved_even_when_access_is_rejected() {
		let a = Analysis::new(indoc! {"
			mod m {
				pub struct S(other: u32, value: u32);
			}
			func f(s: m::S) -> u32 {
				s.value
			}
		"});
		assert!(a.has_errors());
		assert_eq!(
			a.reference("s.value", "value"),
			Reference::Field {
				owner: a.struct_index("m::S"),
				field: FieldIdx::new(1),
				access: AccessKind::Read,
			}
		);
	}

	#[test]
	fn pattern_shorthand_selects_a_field_and_keeps_the_local_declaration() {
		let a = Analysis::clean(indoc! {"
			struct S(value: u32);
			func f(s: S) -> u32 {
				local S({ value }) = s;
				value
			}
		"});
		let function = a.function_index("f");
		assert_eq!(
			a.reference("{ value }", "value"),
			Reference::Field {
				owner: a.struct_index("S"),
				field: FieldIdx::new(0),
				access: AccessKind::Read,
			}
		);
		assert_eq!(
			a.value("\n\tvalue\n", "value"),
			Reference::Local {
				owner: BodyOwner::Function(function),
				local: LocalIdx::new(1),
				access: AccessKind::Read,
			}
		);
		let declaration = a.local(function, 1);
		assert_eq!(declaration.name.span, a.span("{ value }", "value"));
		assert_eq!(a.strings.resolve(declaration.name.inner), Some("value"));
	}

	#[test]
	fn associated_types_constants_and_qualified_calls_record_exact_declarations()
	 {
		let a = Analysis::clean(indoc! {"
			trait Tr: StackValue {
				type Value: StackValue;
				const COUNT: u32;
				func make(value: Self::Value) -> Self::Value;
			}
			func f<T: Tr>(value: T::Value) -> <T as Tr>::Value {
				local _ = T::COUNT;
				local _ = <T as Tr>::COUNT;
				<T as Tr>::make(value)
			}
		"});
		let parameter = Reference::TypeParam {
			env: a.sema.functions[usize::from(a.function_index("f"))]
				.type_params,
			index: 0,
		};
		for context in [
			"value: T::Value",
			"-> <T as Tr>::Value",
			"T::COUNT",
			"<T as Tr>::COUNT",
			"<T as Tr>::make",
		] {
			assert_eq!(a.at(context, "T", Tier::Type), Some(parameter));
		}
		for context in ["value: T::Value", "-> <T as Tr>::Value"] {
			assert_eq!(
				a.at(context, "Value", Tier::Type),
				Some(Reference::Member(a.trait_member(
					"Tr",
					"Value",
					Tier::Type
				)))
			);
		}
		for context in ["T::COUNT", "<T as Tr>::COUNT"] {
			assert_eq!(
				a.value(context, "COUNT"),
				Reference::Member(a.trait_member("Tr", "COUNT", Tier::Value))
			);
		}
		assert_eq!(
			a.value("<T as Tr>::make", "make"),
			Reference::Member(a.trait_member("Tr", "make", Tier::Value))
		);
		assert_eq!(
			a.at("<T as Tr>::make", "Tr", Tier::Type),
			Some(Reference::Item {
				item: a.declaration("Tr", Tier::Type),
				route: Route::Direct
			})
		);
	}

	#[test]
	fn self_types_and_receiver_values_keep_their_distinct_identities() {
		let a = Analysis::clean(indoc! {"
			trait Tr: StackValue {
				func id(self: Self) -> Self { self }
			}
			struct S();
			impl S {
				func make() -> Self { Self() }
			}
			impl Tr for S {
				func id(self: Self) -> Self { self }
			}
		"});
		let DeclKind::Trait(trait_index) = a.resolve("Tr", Tier::Type) else {
			panic!()
		};
		assert_eq!(
			a.at("self: Self", "Self", Tier::Type),
			Some(Reference::TypeParam {
				env: a.sema.traits[usize::from(trait_index)].env,
				index: 0,
			})
		);
		let target = ImplTarget::Struct(a.struct_index("S"));
		let &[inherent] = a.sema.impl_dispatch.inherent_candidates(target)
		else {
			panic!("expected one inherent impl")
		};
		assert_eq!(
			a.at("make() -> Self", "Self", Tier::Type),
			Some(Reference::InherentImplSelf(inherent))
		);
		assert_eq!(
			a.at("{ Self()", "Self", Tier::Value),
			Some(Reference::InherentImplSelf(inherent))
		);
		let &[(actual_trait, implementation)] =
			a.sema.impl_dispatch.trait_candidates(target)
		else {
			panic!("expected one trait impl")
		};
		assert_eq!(actual_trait, trait_index);
		assert_eq!(
			a.at("impl Tr for S {\n\tfunc id(self: Self)", "Self", Tier::Type),
			Some(Reference::TraitImplSelf(implementation))
		);
		let MemberKind::Method(function) =
			a.trait_member("Tr", "id", Tier::Value)
		else {
			panic!()
		};
		assert_eq!(
			a.value("{ self }", "self"),
			Reference::Local {
				owner: BodyOwner::Function(function),
				local: LocalIdx::new(0),
				access: AccessKind::Read,
			}
		);
	}

	#[test]
	fn imports_and_exports_record_source_names_not_external_names() {
		let a = Analysis::clean(indoc! {"
			mod m {
				pub func run() {}
			}
			use m::run as alias;
			func f() { alias(); }
			export alias as \"external\"
		"});
		let declaration = a.declaration("m::run", Tier::Value);
		assert_eq!(
			a.value("use m::run", "run"),
			Reference::Item {
				item: declaration,
				route: Route::Direct
			}
		);
		let imported = a.value("alias();", "alias");
		let Reference::Item {
			item: actual,
			route: Route::Import(_),
		} = imported
		else {
			panic!("expected an import")
		};
		assert_eq!(actual, declaration);
		assert_eq!(a.value("export alias", "alias"), imported);
		assert_eq!(a.at("as \"external\"", "external", Tier::Value), None);
	}

	#[test]
	fn glob_imports_and_both_tiers_of_a_constructor_use_are_recorded() {
		let a = Analysis::clean(indoc! {"
			mod m {
				pub struct S();
				pub func run() {}
			}
			use m::S;
			use m::*;
			func f(s: S) -> S {
				run();
				S()
			}
		"});
		for tier in [Tier::Type, Tier::Value] {
			assert_eq!(
				a.at("use m::S", "S", tier),
				Some(Reference::Item {
					item: a.declaration("m::S", tier),
					route: Route::Direct
				})
			);
		}
		let imported = a.value("\n\tS()", "S");
		let Reference::Item {
			item: declaration,
			route: Route::Import(_),
		} = imported
		else {
			panic!("expected a named import")
		};
		assert_eq!(declaration, a.declaration("m::S", Tier::Value));
		let Reference::Item {
			item: declaration,
			route: Route::Import(_),
		} = a.value("run();", "run")
		else {
			panic!("expected a glob import")
		};
		assert_eq!(declaration, a.declaration("m::run", Tier::Value));
	}

	#[test]
	fn failed_members_keep_receivers_arguments_and_later_references() {
		let a = Analysis::new(indoc! {"
			struct S(value: u32);
			func f(s: S, x: u32) -> u32 {
				local _ = s.missing(x);
				local _ = s.missing({ value: x });
				local _ = s.absent;
				x
			}
		"});
		assert!(a.has_errors());
		let function = a.function_index("f");
		let receiver = Reference::Local {
			owner: BodyOwner::Function(function),
			local: LocalIdx::new(0),
			access: AccessKind::Read,
		};
		let argument = Reference::Local {
			owner: BodyOwner::Function(function),
			local: LocalIdx::new(1),
			access: AccessKind::Read,
		};
		assert_eq!(a.value("s.missing", "s"), receiver);
		assert_eq!(a.value("s.absent", "s"), receiver);
		assert_eq!(a.value("missing(x)", "x"), argument);
		assert_eq!(a.value("value: x", "x"), argument);
		assert_eq!(a.at("value: x", "value", Tier::Value), None);
		assert_eq!(a.value("\n\tx\n", "x"), argument);
		assert_eq!(a.at("s.missing", "missing", Tier::Value), None);
		assert_eq!(a.at("s.absent", "absent", Tier::Value), None);
	}

	#[test]
	fn invalid_arguments_preserve_successful_labels_and_value_references() {
		let a = Analysis::new(indoc! {"
			func take(x: u32, y: u32) {}
			func f(x: u32) -> u32 {
				take({ x, y: missing });
				x
			}
		"});
		assert!(a.has_errors());
		assert_eq!(
			a.shorthand("{ x,", "x"),
			Some(Shorthand {
				label: Reference::Parameter {
					function: a.function_index("take"),
					parameter: ParamIdx::new(0)
				},
				value: Reference::Local {
					owner: BodyOwner::Function(a.function_index("f")),
					local: LocalIdx::new(0),
					access: AccessKind::Read,
				},
			})
		);
		assert_eq!(
			a.label("y: missing", "y"),
			Reference::Parameter {
				function: a.function_index("take"),
				parameter: ParamIdx::new(1)
			}
		);
		assert_eq!(a.at("y: missing", "missing", Tier::Value), None);
		assert_eq!(
			a.value("\n\tx\n", "x"),
			Reference::Local {
				owner: BodyOwner::Function(a.function_index("f")),
				local: LocalIdx::new(0),
				access: AccessKind::Read,
			}
		);
	}

	#[test]
	fn unresolved_calls_still_record_positional_and_named_argument_values() {
		let a = Analysis::new(indoc! {"
			struct S();
			func f(x: u32) -> u32 {
				missing(x);
				S::absent({ x });
				<Missing>::absent({ value: x });
				x
			}
		"});
		assert!(a.has_errors());
		let expected = Reference::Local {
			owner: BodyOwner::Function(a.function_index("f")),
			local: LocalIdx::new(0),
			access: AccessKind::Read,
		};
		for context in ["missing(x)", "{ x }", "value: x", "\n\tx\n"] {
			assert_eq!(a.value(context, "x"), expected);
		}
		assert_eq!(a.at("value: x", "value", Tier::Value), None);
	}

	#[test]
	fn import_block_uses_and_imported_function_calls_record_each_name() {
		let a = Analysis::clean(indoc! {r#"
			mod types {
				pub struct S();
			}
			import "host" as host {
				use super::types::S;
				func run(value: S);
			}
			func f(value: types::S) {
				host::run(value);
			}
		"#});
		assert_eq!(
			a.at("super::types::S", "types", Tier::Type),
			Some(Reference::Item {
				item: a.declaration("types", Tier::Type),
				route: Route::Direct
			})
		);
		assert_eq!(
			a.at("super::types::S", "S", Tier::Type),
			Some(Reference::Item {
				item: a.declaration("types::S", Tier::Type),
				route: Route::Direct
			})
		);
		assert_eq!(
			a.at("host::run", "host", Tier::Type),
			Some(Reference::Item {
				item: a.declaration("host", Tier::Type),
				route: Route::Direct
			})
		);
		assert_eq!(
			a.value("host::run", "run"),
			Reference::Item {
				item: a.declaration("host::run", Tier::Value),
				route: Route::Direct
			}
		);
		assert_eq!(
			a.value("run(value)", "value"),
			Reference::Local {
				owner: BodyOwner::Function(a.function_index("f")),
				local: LocalIdx::new(0),
				access: AccessKind::Read,
			}
		);
	}

	#[test]
	fn constant_patterns_record_the_constant_and_enum_path_segments() {
		let a = Analysis::clean(indoc! {"
			const LIMIT: u32 = 1;
			enum E(u8) { A = 0, B = 1 }
			func f(x: u32) -> u32 {
				match x { const LIMIT => 1, _ => 0 }
			}
			func g(x: E) -> u32 {
				match x { E::A => 1, _ => 0 }
			}
		"});
		assert_eq!(
			a.value("const LIMIT =>", "LIMIT"),
			Reference::Item {
				item: a.declaration("LIMIT", Tier::Value),
				route: Route::Direct
			}
		);
		assert_eq!(
			a.at("E::A =>", "E", Tier::Type),
			Some(Reference::Item {
				item: a.declaration("E", Tier::Type),
				route: Route::Direct
			})
		);
		assert_eq!(
			a.value("E::A =>", "A"),
			Reference::Item {
				item: a.declaration("E::A", Tier::Value),
				route: Route::Direct
			}
		);
	}

	#[test]
	fn only_the_named_target_of_a_write_is_written() {
		let a = Analysis::clean(indoc! {"
			memory heap: u32;
			struct Inner(value: u32);
			struct Outer(inner: Inner, pointer: heap::*Inner);
			func f(mut s: Outer, p: heap::*Outer, n: u32) {
				s.inner.value = n;
				(s.inner.value) += n;
				p.inner.value = n;
				s.pointer.value += n;
				p.pointer.value += n;
				p.* = s;
				local _ = p.inner.value.&;
			}
		"});
		let local = |index, access| Reference::Local {
			owner: BodyOwner::Function(a.function_index("f")),
			local: LocalIdx::new(index),
			access,
		};
		assert_eq!(
			a.value("s.inner.value =", "s"),
			local(0, AccessKind::Write)
		);
		assert_eq!(
			a.value("(s.inner.value)", "s"),
			local(0, AccessKind::ReadWrite)
		);
		assert_eq!(a.value("p.inner.value =", "p"), local(1, AccessKind::Read));
		assert_eq!(
			a.value("s.pointer.value +=", "s"),
			local(0, AccessKind::Read)
		);
		assert_eq!(a.value("p.* =", "p"), local(1, AccessKind::Read));
		for (context, field, owner, access) in [
			("s.inner.value =", "inner", "Outer", AccessKind::Read),
			("s.inner.value =", "value", "Inner", AccessKind::Write),
			("(s.inner.value)", "inner", "Outer", AccessKind::Read),
			("(s.inner.value)", "value", "Inner", AccessKind::ReadWrite),
			("p.inner.value =", "inner", "Outer", AccessKind::Read),
			("p.inner.value =", "value", "Inner", AccessKind::Write),
			("s.pointer.value +=", "pointer", "Outer", AccessKind::Read),
			(
				"s.pointer.value +=",
				"value",
				"Inner",
				AccessKind::ReadWrite,
			),
			("p.pointer.value +=", "pointer", "Outer", AccessKind::Read),
			(
				"p.pointer.value +=",
				"value",
				"Inner",
				AccessKind::ReadWrite,
			),
			("p.inner.value.&", "inner", "Outer", AccessKind::Read),
			("p.inner.value.&", "value", "Inner", AccessKind::Read),
		] {
			let index = if field == "pointer" { 1 } else { 0 };
			assert_eq!(
				a.reference(context, field),
				Reference::Field {
					owner: a.struct_index(owner),
					field: FieldIdx::new(index),
					access,
				}
			);
		}
		assert_eq!(a.value("= n;", "n"), local(2, AccessKind::Read));
	}

	#[test]
	fn an_indexed_pointer_element_is_read_not_written() {
		let a = Analysis::clean(indoc! {"
			memory heap: u32;
			struct Rows(data: [heap::*[u32; 4]; 4]);
			func f(p: heap::*Rows, i: u32, j: u32) {
				p.data[i][j] = 1;
			}
		"});
		assert_eq!(
			a.reference("p.data[i][j] =", "data"),
			Reference::Field {
				owner: a.struct_index("Rows"),
				field: FieldIdx::new(0),
				access: AccessKind::Read,
			}
		);
	}

	#[test]
	fn only_a_value_chain_makes_its_root_local_written() {
		let a = Analysis::clean(indoc! {"
			memory heap: u32;
			struct Inner(value: u32);
			struct Outer(inner: Inner, pointer: heap::*Inner);
			func through_value(mut s: Outer, n: u32) { s.inner.value = n; }
			func through_pointer(s: Outer, n: u32) { s.pointer.value = n; }
		"});
		assert!(matches!(
			a.value("s.inner.value = n", "s"),
			Reference::Local {
				access: AccessKind::Write,
				..
			}
		));
		assert!(matches!(
			a.value("s.pointer.value = n", "s"),
			Reference::Local {
				access: AccessKind::Read,
				..
			}
		));
	}

	#[test]
	fn an_indexed_pointer_local_is_read_not_written() {
		let a = Analysis::clean(indoc! {"
			memory heap: u32;
			func f(a: heap::*[u32; 4], i: u32) {
				a[i] = 1;
			}
		"});
		assert!(matches!(
			a.value("a[i] =", "a"),
			Reference::Local {
				access: AccessKind::Read,
				..
			}
		));
	}

	#[test]
	fn indexed_writes_read_the_pointer_and_index() {
		let a = Analysis::clean(indoc! {"
			memory heap: u32;
			struct Buffer(data: [u32; 4], pointer: heap::*[u32; 4]);
			func f(p: heap::*Buffer, i: u32) {
				p.data[i] = 1;
				p.data[i] += 1;
				p.pointer[i] = 1;
				p.data[block { p.pointer[i] += 1; i }] = 2;
			}
		"});
		for (context, access) in [
			("p.data[i] =", AccessKind::Write),
			("p.data[i] +=", AccessKind::ReadWrite),
		] {
			assert!(matches!(
				a.value(context, "p"),
				Reference::Local {
					access: AccessKind::Read,
					..
				}
			));
			assert!(matches!(
				a.value(context, "i"),
				Reference::Local {
					access: AccessKind::Read,
					..
				}
			));
			assert_eq!(
				a.reference(context, "data"),
				Reference::Field {
					owner: a.struct_index("Buffer"),
					field: FieldIdx::new(0),
					access
				}
			);
		}
		for context in ["p.pointer[i] =", "p.pointer[i] +="] {
			assert_eq!(
				a.reference(context, "pointer"),
				Reference::Field {
					owner: a.struct_index("Buffer"),
					field: FieldIdx::new(1),
					access: AccessKind::Read
				}
			);
			assert!(matches!(
				a.value(context, "p"),
				Reference::Local {
					access: AccessKind::Read,
					..
				}
			));
		}
		assert_eq!(
			a.reference("p.data[block", "data"),
			Reference::Field {
				owner: a.struct_index("Buffer"),
				field: FieldIdx::new(0),
				access: AccessKind::Write
			}
		);
	}

	#[test]
	fn a_label_and_a_value_at_one_span_are_separate_entries() {
		let a = Analysis::clean("func f(x: u32) { _ = x; }");
		let span = SourceSpan::new(a.file, a.span("x;", "x"));
		let value = a.value("x;", "x");
		let label = Reference::Parameter {
			function: a.function_index("f"),
			parameter: ParamIdx::new(0),
		};
		let mut resolutions = NameResolutions::default();
		resolutions.record(Site::Value(span), value);
		resolutions.record(Site::Label(span), label);
		let updated = Reference::Item {
			item: a.declaration("f", Tier::Value),
			route: Route::Direct,
		};
		resolutions.record(Site::Value(span), updated);
		assert_eq!(resolutions.get(Site::Value(span)), Some(updated));
		assert_eq!(resolutions.get(Site::Label(span)), Some(label));
		assert_eq!(resolutions.get(Site::Type(span)), None);
	}

	/// A source with labelled positions. `$[label]` is written right before a
	/// name and is removed from the text the compiler sees; the label stands
	/// for that name's position.
	struct Marked {
		source: String,
		marks: Vec<(&'static str, u32)>,
	}

	impl Marked {
		fn new(marked: &'static str) -> Self {
			let mut source = String::new();
			let mut marks = Vec::new();
			let mut rest = marked;
			while let Some(open) = rest.find("$[") {
				source.push_str(&rest[..open]);
				let after = &rest[open + "$[".len()..];
				let close = after.find(']').expect("an unclosed marker");
				marks.push((&after[..close], source.len() as u32));
				rest = &after[close + "]".len()..];
			}
			source.push_str(rest);
			Self { source, marks }
		}

		/// The span of the name the mark `label` is written before.
		fn name(&self, label: &str) -> TextSpan {
			let (_, start) = *self
				.marks
				.iter()
				.find(|(mark, _)| *mark == label)
				.unwrap_or_else(|| panic!("no mark `{label}`"));
			let length = self.source[start as usize..]
				.find(|c: char| !c.is_alphanumeric() && c != '_')
				.unwrap_or(self.source.len() - start as usize);
			TextSpan::new(start, start + length as u32)
		}

		/// Asserts that the cursor on the name marked `used` (at its start,
		/// inside it and at its end) goes to the name marked `declared`.
		#[track_caller]
		fn assert_definition(
			&self,
			analysis: &Analysis<'_>,
			used: &str,
			declared: &str,
		) {
			let used_span = self.name(used);
			let declared_span =
				SourceSpan::new(analysis.file, self.name(declared));
			for offset in [used_span.start, used_span.start + 1, used_span.end]
			{
				assert_eq!(
					analysis.sema.definition_at(analysis.file, offset),
					Some(declared_span),
					"from `{used}` at offset {offset}"
				);
			}
		}
	}

	#[test]
	fn definition_at_reaches_items_locals_labels_parameters_and_fields() {
		let marked = Marked::new(indoc! {"
			struct $[Point]Point($[width]width: i32, height: i32);
			func $[make]make($[amount]amount: i32) -> i32 {
				local $[total]total = $[amount.read]amount;
				loop :$[done]done { break :$[done.break]done $[total.read]total }
			}
			func main() {
				local p = $[Point.call]Point({ $[width.label]width: 1, height: 2 });
				_ = $[make.call]make({ $[amount.label]amount: 3 });
				local q: $[Point.type]Point = p;
			}
		"});
		let analysis = Analysis::clean(&marked.source);
		for (used, declared) in [
			("Point.call", "Point"),
			("Point.type", "Point"),
			("make.call", "make"),
			("amount.read", "amount"),
			("amount.label", "amount"),
			("total.read", "total"),
			("done.break", "done"),
			("width.label", "width"),
		] {
			marked.assert_definition(&analysis, used, declared);
		}
	}

	#[test]
	fn definition_at_reaches_type_parameters_and_members() {
		let marked = Marked::new(indoc! {"
			struct $[Meters]Meters(value: u32);
			impl Meters { pub func $[zero]zero() -> Meters { Meters(0) } }
			func id<$[Elem]Elem: StackValue>(x: $[Elem.param]Elem) -> $[Elem.result]Elem { x }
			func main() { local m = $[Meters.path]Meters::$[zero.call]zero(); }
		"});
		let analysis = Analysis::clean(&marked.source);
		for (used, declared) in [
			("Elem.param", "Elem"),
			("Elem.result", "Elem"),
			("zero.call", "zero"),
			("Meters.path", "Meters"),
		] {
			marked.assert_definition(&analysis, used, declared);
		}
	}

	#[test]
	fn definition_at_is_none_away_from_a_resolved_name() {
		let source = "func f() { local x = 1; }";
		let analysis = Analysis::new(source);
		let keyword = source.find("local").unwrap() as u32;
		assert_eq!(analysis.sema.definition_at(analysis.file, keyword), None);
		assert_eq!(
			analysis
				.sema
				.definition_at(analysis.file, source.len() as u32 + 5),
			None
		);
	}

	#[test]
	fn symbol_at_returns_the_resolved_reference_and_the_names_span() {
		let marked = Marked::new(indoc! {"
			func $[make]make(amount: i32) -> i32 { amount }
			func main() {
				local amount: i32 = 1;
				_ = $[call]make({ $[label]amount: 3 });
				_ = make({ $[short]amount });
			}
		"});
		let analysis = Analysis::clean(&marked.source);
		let at = |label: &str| {
			let span = marked.name(label);
			let (found, reference) = analysis
				.sema
				.symbol_at(analysis.file, span.start + 1)
				.unwrap_or_else(|| panic!("nothing at `{label}`"));
			assert_eq!(found, SourceSpan::new(analysis.file, span));
			reference
		};

		// A call names the function, whose kind is read through the sema.
		let Reference::Item {
			item: key,
			route: Route::Direct,
		} = at("call")
		else {
			panic!("expected a declaration");
		};
		assert!(matches!(
			analysis.sema.declaration_kind(key),
			DeclKind::Function(_)
		));
		// A named argument's label is the parameter, not a read of it.
		assert!(matches!(at("label"), Reference::Parameter { .. }));
		// A shorthand argument is a label and the value it supplies: the
		// value is what the name means where it is used.
		assert!(matches!(at("short"), Reference::Local { .. }));
	}
}
