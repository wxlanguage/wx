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
use super::decls::Declared;
use super::decls::{
	BindingKey, BindingLookup, ConstIdx, DeclKind, FieldIdx, FunctionIdx,
	GlobalIdx, InherentImplIdx, ItemLoc, MemberKind, NameUse, Namespace,
	PackageMemberItem, Scope, StructIdx, Tier, TraitImplIdx, UseItemIndex,
};
use super::signatures::Semantics;
use super::types::{GenericEnvIdx, GenericEnvOwner, ImplKind};
use crate::ast::Keyword;
use crate::diagnostics::{SourceSpan, TextSpan};
use crate::vfs::FileId;
use string_interner::symbol::SymbolU32;

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
	Item { item: ItemLoc, route: Route },
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
	Item(ItemLoc),
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
		declaration: ItemLoc,
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
	/// Every resolved name referring to `definition`, in source order and
	/// without duplicate spans. Declarations are not references; callers may
	/// include `definition_span` separately. Like every definition identity,
	/// the argument and results belong to this compilation only.
	///
	/// This is the inverse of the existing resolution table, computed on
	/// demand rather than stored alongside it. All roles at a site participate:
	/// a shorthand can refer to both a parameter/field and its supplied value.
	pub fn references_to(&self, definition: Definition) -> Vec<SourceSpan> {
		let definition = self.reference_identity(definition);
		let mut found = Vec::new();
		for (site, reference) in &self.resolutions.by_site {
			let span = site.span();
			if span.span.start != span.span.end
				&& self.reference_identity(reference.definition()) == definition
				&& found.last() != Some(&span)
			{
				found.push(span);
			}
		}
		found
	}

	/// Every resolved meaning of the name written at exactly `span`: one per
	/// role it plays there (a shorthand argument is a label and a value).
	pub fn references_at(
		&self,
		span: SourceSpan,
	) -> impl Iterator<Item = Reference> + '_ {
		self.resolutions
			.by_site
			.range(Site::Type(span)..=Site::Label(span))
			.map(|(_, &reference)| reference)
	}

	/// Whether `a` and `b` name the same declaration, as `references_to`
	/// compares them: a parameter and the local it binds, a trait member
	/// reached as an item and through a type, are one.
	pub fn same_definition(&self, a: Definition, b: Definition) -> bool {
		self.reference_identity(a) == self.reference_identity(b)
	}

	/// Whether the name `name` written at `span` is an entry of the export
	/// block with no `as "..."`, so its Wasm export name is its own name.
	pub fn exported_under_own_name(
		&self,
		name: SymbolU32,
		span: SourceSpan,
	) -> bool {
		// An entry's external span is its name's own when it has no alias,
		// and the quoted string's when it has one.
		self.decls
			.exports
			.get(&name)
			.is_some_and(|entry| entry.external_span == span)
	}

	/// Different ways of naming the same declaration, not declarations that
	/// merely navigate to the same span (a trait and its `Self`, for example).
	fn reference_identity(&self, definition: Definition) -> Definition {
		match definition {
			Definition::Item(key) => match self.declaration_kind(key) {
				DeclKind::Function(index) => {
					Definition::Member(MemberKind::Function(index))
				}
				DeclKind::Const(index) | DeclKind::EnumVariant(index) => {
					Definition::Member(MemberKind::Constant(index))
				}
				DeclKind::AssocType(index) => {
					Definition::Member(MemberKind::AssociatedType(index))
				}
				_ => definition,
			},
			Definition::Member(MemberKind::Method(index)) => {
				Definition::Member(MemberKind::Function(index))
			}
			Definition::Parameter {
				function,
				parameter,
			} => {
				let owner = BodyOwner::Function(function);
				self.owner_body(owner)
					.and_then(|body| body.params().get(usize::from(parameter)))
					.copied()
					.flatten()
					.map_or(definition, |local| Definition::Local {
						owner,
						local,
					})
			}
			_ => definition,
		}
	}

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

	/// Every resolved name written in `file`, in source order, one per name:
	/// where a name holds several entries, the one `symbol_at` would answer
	/// (the value, then the type, then the label). Zero-width synthetic
	/// spans are skipped, since nothing is written there.
	pub fn resolutions_in(
		&self,
		file: FileId,
	) -> impl Iterator<Item = (SourceSpan, Reference)> + '_ {
		// The least site of `file`: the empty span at its start, first role.
		let start =
			Site::Type(SourceSpan::new(file, TextSpan { start: 0, end: 0 }));
		let mut entries = self
			.resolutions
			.by_site
			.range(start..)
			.take_while(move |(site, _)| site.span().file_id == file)
			.filter(|(site, _)| {
				let span = site.span().span;
				span.start != span.end
			})
			.peekable();
		std::iter::from_fn(move || {
			let (&site, &reference) = entries.next()?;
			let mut found = (site, reference);
			while let Some((&next, &reference)) =
				entries.next_if(|(next, _)| next.span() == site.span())
			{
				if next.priority() > found.0.priority() {
					found = (next, reference);
				}
			}
			Some((found.0.span(), found.1))
		})
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

	/// Whether the compiler provides `definition`, with no wx definition
	/// behind it: a function core leaves to the compiler (a package function
	/// of core's, as `transmute` or an intrinsic, and `Slice`'s bodiless
	/// `len` and `as_ref`), a primitive type or a literal kind. A function
	/// core writes a body for is an ordinary function, even when that body
	/// calls one of these.
	pub fn is_compiler_provided(&self, definition: Definition) -> bool {
		let decls = &self.decls;
		let function = match definition {
			Definition::Item(key) => match self.declaration_kind(key) {
				DeclKind::Function(function) => function,
				DeclKind::TypeAlias(alias) => {
					return decls.intrinsics.is_builtin_type(alias);
				}
				_ => return false,
			},
			Definition::Member(
				MemberKind::Function(function) | MemberKind::Method(function),
			) => function,
			_ => return false,
		};
		// Only a package function enters a contract, so core's entry under
		// this function's name being this function makes it one.
		let name = BindingKey::value(decls.name(function).inner);
		let package_function = decls.package_contracts
			[decls.core_package.as_usize()]
		.members
		.get(&name)
		.is_some_and(|member| {
			member.item == PackageMemberItem::Function(function)
		});
		package_function
			|| [decls.intrinsics.slice_len, decls.intrinsics.slice_as_ref]
				.contains(&Some(function))
	}

	/// What kind of declaration `loc` names.
	pub fn declaration_kind(&self, loc: ItemLoc) -> DeclKind {
		loc.symbol_kind(&self.decls)
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
			if module.own_file != self.decls.file_id(module.loc) {
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
				Some(decls.declaration_span(kind.loc(decls)))
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
				Some(SourceSpan::new(decls.file_id(function.loc), name.span))
			}
		}
	}

	/// Every declared name that has a written name, with where it is written.
	/// A declaration is its row, a member's included; a generated one's name
	/// span is empty (a package's own entry, a typeset's trait, a generated
	/// impl's associated types), so it is skipped. Where two still share a
	/// span (a trait and its `Self`), the item wins.
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
			add(Definition::Item(key));
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
		Some(SourceSpan::new(self.decls.file_id(decl.loc), name.span))
	}

	/// The body `declaration` owns: a function's block, a constant's or a
	/// global's initializer (an enum variant's value is a constant's).
	pub fn body_of(&self, declaration: Definition) -> Option<BodyOwner> {
		let Definition::Item(loc) = declaration else {
			return None;
		};
		let owner = match self.declaration_kind(loc) {
			DeclKind::Function(index) => BodyOwner::Function(index),
			DeclKind::Const(index) | DeclKind::EnumVariant(index) => {
				BodyOwner::Const(index)
			}
			DeclKind::Global(index) => BodyOwner::Global(index),
			_ => return None,
		};
		self.owner_body(owner).is_some().then_some(owner)
	}

	/// Every impl, by the span of its target's path (`ast::Path::span`, what
	/// `Self` there names), the one span an impl keeps; a generated impl (a
	/// function's `Call`) by its generator's. Nothing is kept: a caller that
	/// finds impls by where they are written (the language server) indexes
	/// them itself.
	pub fn impls(&self) -> impl Iterator<Item = (SourceSpan, Definition)> + '_ {
		let inherent = (0..self.inherent_impls.len()).map(|index| {
			Definition::InherentImplTarget(InherentImplIdx::new(index as u32))
		});
		let traits = (0..self.trait_impls.len()).map(|index| {
			Definition::TraitImplTarget(TraitImplIdx::new(index as u32))
		});
		inherent.chain(traits).filter_map(|definition| {
			Some((self.definition_span(definition)?, definition))
		})
	}

	/// Every name a bare identifier written at `offset` in `owner`'s body
	/// can mean, used as `used_as` says, with what it would refer to there:
	/// what an unqualified lookup of that name finds, so nothing it would
	/// reject (a name that is out of reach, private, ambiguous, or hidden by
	/// a nearer one) is listed, and only what can be written there
	/// (`NameUse::admits`). As a value, the locals the name can use; as a
	/// type, the type parameters in scope; then the items of the body's
	/// scope and the core prelude a nearer name does not hide.
	pub fn names_at(
		&self,
		owner: BodyOwner,
		offset: u32,
		used_as: NameUse,
	) -> Vec<(SymbolU32, Definition)> {
		let Some(body) = self.owner_body(owner) else {
			return Vec::new();
		};
		let scope = self.owner_scope(owner);
		let mut found = Vec::new();
		// A value is looked up among the locals first.
		if used_as == NameUse::Value {
			found.extend(body.locals_at(offset).into_iter().map(|local| {
				(
					body.local(local).name.inner,
					Definition::Local { owner, local },
				)
			}));
		}
		self.scope_names(
			scope.namespace,
			scope.generic_env,
			used_as,
			|name| body.local_named_at(offset, name).is_some(),
			&mut found,
		);
		found
	}

	/// Every name a bare identifier written in the signature of `owner` can
	/// mean, used as `used_as` says, as `names_at` lists them in a body,
	/// which a signature has none of the locals of. `owner` is an item, or an impl by its
	/// target (`InherentImplTarget`, `TraitImplTarget`); an associated
	/// type's signature is read in its trait's or impl's scope.
	pub fn names_in_signature(
		&self,
		owner: Definition,
		used_as: NameUse,
	) -> Vec<(SymbolU32, Definition)> {
		let Some((namespace, env)) = self.signature_scope(owner) else {
			return Vec::new();
		};
		let mut found = Vec::new();
		self.scope_names(namespace, env, used_as, |_| false, &mut found);
		found
	}

	/// Where `owner`'s signature is read: the scope its declaration is
	/// written in, and its generic env, which holds its own type parameters
	/// and those of its trait or impl (see `names_in_signature`).
	fn signature_scope(
		&self,
		owner: Definition,
	) -> Option<(Scope, GenericEnvIdx)> {
		match owner {
			Definition::Item(loc) => {
				let env = match self.declaration_kind(loc) {
					DeclKind::Function(index) => {
						self.functions[usize::from(index)].type_params
					}
					DeclKind::Struct(index) => {
						self.structs[usize::from(index)].type_params
					}
					DeclKind::TypeAlias(index) => {
						self.type_aliases[usize::from(index)].type_params
					}
					DeclKind::Trait(index) => {
						self.traits[usize::from(index)].env
					}
					DeclKind::Const(index) | DeclKind::EnumVariant(index) => {
						self.constants[usize::from(index)].env
					}
					// Declares no type parameters.
					_ => GenericEnvIdx::ROOT,
				};
				Some((self.decls.scope(loc), env))
			}
			Definition::InherentImplTarget(index) => Some((
				self.decls.inherent_impls[usize::from(index)].namespace,
				self.inherent_impls[usize::from(index)]
					.as_ref()?
					.type_params,
			)),
			Definition::TraitImplTarget(index) => Some((
				self.decls.trait_impls[usize::from(index)].namespace,
				self.trait_impls[usize::from(index)].as_ref()?.type_params,
			)),
			_ => None,
		}
	}

	/// What a bare name used as `used_as` can mean in `namespace` with the
	/// type parameters of `env`, after the locals a body lists itself: as a
	/// type, the parameters along `env`'s chain (each kept when no nearer one
	/// of its name hides it), then the items of `namespace` and of the core
	/// prelude an unqualified lookup finds (`lookup_unqualified`), accessible
	/// from `namespace`, that can be written there and that no parameter, or
	/// local (`is_local`), of their name takes first. A trait, in a bound or
	/// an impl, is looked up among the items alone, so no parameter is one
	/// or hides one.
	fn scope_names(
		&self,
		namespace: Scope,
		env: GenericEnvIdx,
		used_as: NameUse,
		is_local: impl Fn(SymbolU32) -> bool,
		found: &mut Vec<(SymbolU32, Definition)>,
	) {
		if used_as == NameUse::Type {
			let envs = std::iter::successors(Some(env), |&env| {
				self.generic_envs.parent(env)
			});
			for frame in envs {
				for (index, name) in
					self.generic_envs.param_names(frame).iter().enumerate()
				{
					let index = index as u32;
					if self.generic_envs.resolve(env, name.inner)
						== Some((frame, index))
					{
						found.push((
							name.inner,
							Definition::TypeParam { env: frame, index },
						));
					}
				}
			}
			// An impl's implicit `Self` is its target, rather than a type
			// parameter. A written parameter/refinement takes precedence,
			// just as it does in `resolve_type_path`.
			let self_name = Keyword::SelfPascal.symbol();
			if self.generic_envs.resolve(env, self_name).is_none()
				&& let Some((kind, _)) = self.resolve_impl_self(env)
			{
				let definition = match kind {
					ImplKind::Inherent(index) => {
						Definition::InherentImplTarget(index)
					}
					ImplKind::Trait(index) => {
						Definition::TraitImplTarget(index)
					}
				};
				found.push((self_name, definition));
			}
		}
		let hidden = |name: SymbolU32| match used_as {
			NameUse::Value => is_local(name),
			NameUse::Type => self.generic_envs.resolve(env, name).is_some(),
			NameUse::Bound | NameUse::Trait => false,
		};
		let tier = used_as.tier();
		let roots = [
			Namespace::from(namespace),
			Namespace::Package(self.decls.core_package),
		];
		for name in self.candidates(&roots, tier) {
			if hidden(name) {
				continue;
			}
			let key = BindingKey::new(tier, name);
			let (base, lookup) = self.decls.lookup_unqualified(namespace, key);
			if let BindingLookup::Found {
				target, visibility, ..
			} = lookup && let Some(loc) = target.loc()
				&& used_as.admits(self.declaration_kind(loc))
				&& self
					.decls
					.namespaces
					.is_accessible_from(namespace, base, visibility)
			{
				found.push((name, Definition::Item(loc)));
			}
		}
	}

	/// Every name a path written in `declaration` (its signature or its
	/// body; see `names_in_signature` for what it may be) can continue with,
	/// used as `used_as` says, after a prefix that means `prefix`, with what
	/// it would refer to: what the walk's lookup of the next segment finds in
	/// the namespace `prefix` enters (`Namespaces::lookup`), accessible from
	/// where the path is written, that can be written there. Empty when
	/// `prefix` enters no namespace: what follows a type is one of its
	/// members, which the member search finds.
	pub fn names_in(
		&self,
		declaration: Definition,
		prefix: ItemLoc,
		used_as: NameUse,
	) -> Vec<(SymbolU32, Definition)> {
		let tier = used_as.tier();
		let Some((accessor, _)) = self.signature_scope(declaration) else {
			return Vec::new();
		};
		let namespaces = &self.decls.namespaces;
		let Some(base) = namespaces.entered_by(prefix) else {
			return Vec::new();
		};
		let mut found = Vec::new();
		for name in self.candidates(&[base], tier) {
			let key = BindingKey::new(tier, name);
			if let BindingLookup::Found {
				target, visibility, ..
			} = namespaces.lookup(&self.decls.use_items, accessor, base, key)
				&& let Some(loc) = target.loc()
				&& used_as.admits(self.declaration_kind(loc))
				&& namespaces.is_accessible_from(accessor, base, visibility)
			{
				found.push((name, Definition::Item(loc)));
			}
		}
		found
	}

	/// Every name of `tier` a lookup in `roots` might find, each once: their
	/// own bindings and those their globs reach. A superset: the callers
	/// keep what the lookup itself finds.
	fn candidates(&self, roots: &[Namespace], tier: Tier) -> Vec<SymbolU32> {
		let namespaces = &self.decls.namespaces;
		let mut pending = roots.to_vec();
		let mut visited = Vec::new();
		let mut names = Vec::new();
		while let Some(namespace) = pending.pop() {
			if visited.contains(&namespace) {
				continue;
			}
			visited.push(namespace);
			for key in namespaces.symbols(namespace).bindings.keys() {
				if key.tier == tier && !names.contains(&key.symbol) {
					names.push(key.symbol);
				}
			}
			if let Some(scope) = namespace.as_scope() {
				pending.extend(
					namespaces
						.scope(scope)
						.glob_imports
						.iter()
						.map(|glob| glob.namespace),
				);
			}
		}
		names
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
			BodyOwner::Const(index) => self
				.decls
				.file_id(self.decls.constants[usize::from(index)].loc),
			BodyOwner::Function(index) => self
				.decls
				.file_id(self.decls.functions[usize::from(index)].loc),
			BodyOwner::Global(index) => self
				.decls
				.file_id(self.decls.globals[usize::from(index)].loc),
		}
	}

	fn env_owner_file(&self, owner: GenericEnvOwner) -> FileId {
		let decls = &self.decls;
		match owner {
			GenericEnvOwner::Constant(index) => {
				decls.file_id(decls.constants[usize::from(index)].loc)
			}
			GenericEnvOwner::Enum(index) => {
				decls.file_id(decls.enums[usize::from(index)].loc)
			}
			GenericEnvOwner::Struct(index) => {
				decls.file_id(decls.structs[usize::from(index)].loc)
			}
			GenericEnvOwner::Function(index) => {
				decls.file_id(decls.functions[usize::from(index)].loc)
			}
			GenericEnvOwner::Trait(index) => {
				decls.file_id(decls.traits[usize::from(index)].loc)
			}
			GenericEnvOwner::TypeAlias(index) => {
				decls.file_id(decls.type_aliases[usize::from(index)].loc)
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
	use crate::diagnostics::DiagnosticCode;
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
			builder.load_core();
			let root = builder
				.load_package(
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

		/// What `names_at` lists at the comment `// {mark}`, as `name` for an
		/// item, `name (local)` and `name (param)` for the others.
		fn names(&self, mark: &str, used_as: NameUse) -> Vec<String> {
			let offset =
				self.source.find(&format!("// {mark}")).unwrap() as u32;
			// Every test writes its mark in `f`.
			let f = Definition::Item(self.declaration("f", Tier::Value));
			let owner = self.sema.body_of(f).unwrap();
			self.sema
				.names_at(owner, offset, used_as)
				.into_iter()
				.map(|(name, definition)| {
					let name = self.strings.resolve(name).unwrap();
					match definition {
						Definition::Local { .. } => format!("{name} (local)"),
						Definition::TypeParam { .. } => {
							format!("{name} (param)")
						}
						_ => name.to_string(),
					}
				})
				.collect()
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

		fn declaration(&self, path: &str, tier: Tier) -> ItemLoc {
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
				.loc()
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
	fn references_join_parameter_labels_and_body_locals_and_deduplicate_roles()
	{
		let a = Analysis::clean(indoc! {"
			func take(value: u32) -> u32 {
				_ = take({ value: 1 });
				_ = take({ value });
				value
			}
		"});
		let local = a.value("\n\tvalue\n", "value").definition();
		let parameter = a.label("{ value: 1", "value").definition();
		let expected = [
			a.span("{ value: 1", "value"),
			a.span("{ value }", "value"),
			a.span("\n\tvalue\n", "value"),
		]
		.map(|span| SourceSpan::new(a.file, span));
		assert_ne!(local, parameter);
		assert_eq!(a.sema.references_to(local), expected);
		assert_eq!(a.sema.references_to(parameter), expected);
	}

	#[test]
	fn references_include_both_constructor_tiers_and_import_routes() {
		let a = Analysis::clean(indoc! {"
			mod m { pub struct S(); }
			use m::S as Alias;
			func f(s: Alias) -> m::S { Alias() }
		"});
		let ty = a.at("s: Alias", "Alias", Tier::Type).unwrap().definition();
		let value = a.value("{ Alias()", "Alias").definition();
		let expected = [
			a.span("use m::S", "S"),
			a.span("s: Alias", "Alias"),
			a.span("-> m::S", "S"),
			a.span("{ Alias()", "Alias"),
		]
		.map(|span| SourceSpan::new(a.file, span));
		assert_eq!(a.sema.references_to(ty), expected);
		assert_eq!(a.sema.references_to(value), expected);
	}

	#[test]
	fn references_preserve_owner_identity_and_ignore_access_kind() {
		let a = Analysis::clean(indoc! {"
			func f() -> u32 {
				local mut x: u32 = 0;
				x = 1;
				x += 2;
				local _ = block { local x: u32 = 3; x };
				x
			}
			func g(x: u32) -> u32 { x }
		"});
		let definition = a.value("x = 1", "x").definition();
		assert_eq!(
			a.sema.references_to(definition),
			[
				a.span("x = 1", "x"),
				a.span("x += 2", "x"),
				a.span("\n\tx\n", "x"),
			]
			.map(|span| SourceSpan::new(a.file, span))
		);
	}

	#[test]
	fn references_do_not_merge_a_trait_with_its_self_parameter() {
		let a = Analysis::clean(indoc! {"
			trait Tr: StackValue { func id(self: Self) -> Self { self } }
			func f<T: Tr>(x: T) -> T { x.id() }
		"});
		let tr = a.at("T: Tr", "Tr", Tier::Type).unwrap().definition();
		let self_ty =
			a.at("self: Self", "Self", Tier::Type).unwrap().definition();
		assert_eq!(a.sema.definition_span(tr), a.sema.definition_span(self_ty));
		assert_eq!(
			a.sema.references_to(tr),
			[SourceSpan::new(a.file, a.span("T: Tr", "Tr"))]
		);
		assert_eq!(a.sema.references_to(self_ty).len(), 2);
	}

	#[test]
	fn references_find_members_from_their_declarations() {
		let a = Analysis::clean(indoc! {"
			struct S();
			impl S {
				func id(self: Self) -> Self { self }
			}
			func f(s: S) -> S { S::id(s).id() }
		"});
		let definition = a.value("S::id", "id").definition();
		assert_eq!(
			a.sema.references_to(definition),
			[a.span("S::id", "id"), a.span(".id()", "id"),]
				.map(|span| SourceSpan::new(a.file, span))
		);
		let span = SourceSpan::new(a.file, a.span("func id", "id"));
		let declared = a.sema.definitions()[&span];
		assert_eq!(
			a.sema.references_to(declared),
			a.sema.references_to(definition)
		);
	}

	#[test]
	fn references_find_labels_type_parameters_and_bodyless_parameters() {
		let a = Analysis::clean(indoc! {r#"
			import "host" as host { func take(value: u32); }
			func f<T: StackValue>(x: T) -> T {
				host::take({ value: 1 });
				loop :done { break :done; }
				x
			}
		"#});
		for (reference, contexts, name) in [
			(a.label("value: 1", "value"), vec!["value: 1"], "value"),
			(a.label("break :done", "done"), vec!["break :done"], "done"),
			(
				a.at("x: T", "T", Tier::Type).unwrap(),
				vec!["x: T", "-> T"],
				"T",
			),
		] {
			let definition = reference.definition();
			let span = a.sema.definition_span(definition).unwrap();
			let declared = a.sema.definitions()[&span];
			let expected: Vec<_> = contexts
				.into_iter()
				.map(|context| SourceSpan::new(a.file, a.span(context, name)))
				.collect();
			assert_eq!(a.sema.references_to(definition), expected);
			assert_eq!(a.sema.references_to(declared), expected);
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
	fn references_at_lists_every_role_of_one_name() {
		let a = Analysis::clean(indoc! {"
			func take(x: u32) {}
			func f(x: u32) {
				take({ x });
			}
		"});
		let span = SourceSpan::new(a.file, a.span("{ x }", "x"));
		let found: Vec<_> = a.sema.references_at(span).collect();
		// The parameter it labels, and the local it supplies.
		assert_eq!(found.len(), 2, "{found:?}");
		assert!(found.contains(&a.label("{ x }", "x")));
		assert!(found.contains(&a.value("{ x }", "x")));
		// A parameter named by a label is the local it binds.
		assert!(
			a.sema.same_definition(
				a.label("{ x }", "x").definition(),
				Reference::Local {
					owner: BodyOwner::Function(a.function_index("take")),
					local: LocalIdx::new(0),
					access: AccessKind::Read,
				}
				.definition(),
			)
		);
	}

	#[test]
	fn an_export_entry_without_as_is_exported_under_its_own_name() {
		let a = Analysis::clean(indoc! {"
			func run() {}
			func tick() {}
			export { run, tick as \"step\" }
		"});
		let at = |context: &str, name: &str| {
			SourceSpan::new(a.file, a.span(context, name))
		};
		let symbol = |name: &str| a.strings.get(name).unwrap();
		assert!(
			a.sema
				.exported_under_own_name(symbol("run"), at("{ run,", "run"))
		);
		// Exported under the alias, so not under its own name.
		assert!(
			!a.sema
				.exported_under_own_name(symbol("tick"), at("tick as", "tick"))
		);
		// The declaration is no export entry.
		assert!(
			!a.sema
				.exported_under_own_name(symbol("run"), at("func run", "run"))
		);
	}

	#[test]
	fn only_what_core_leaves_to_the_compiler_is_compiler_provided() {
		let a = Analysis::clean("func f() {}");
		let item = |path| Definition::Item(a.declaration(path, Tier::Value));
		let ty = |path| Definition::Item(a.declaration(path, Tier::Type));
		// A package function of core's is supplied by the compiler; a core
		// function with a body, even one calling it, is an ordinary one.
		assert!(a.sema.is_compiler_provided(item("transmute")));
		assert!(!a.sema.is_compiler_provided(item("slice_from_parts")));
		// Primitives and literal kinds are bodiless; `Char` is a struct core
		// writes.
		assert!(a.sema.is_compiler_provided(ty("u32")));
		assert!(a.sema.is_compiler_provided(ty("const_int")));
		assert!(!a.sema.is_compiler_provided(ty("Char")));
		// `Slice::len` is a bodiless trait function lowering expands.
		let len = a.sema.decls.intrinsics.slice_len.unwrap();
		assert!(a.sema.is_compiler_provided(Definition::Member(
			MemberKind::Function(len)
		)));
		// The user's own function is not.
		assert!(!a.sema.is_compiler_provided(item("f")));
	}

	#[test]
	fn resolutions_in_lists_one_entry_per_name_in_source_order() {
		let a = Analysis::clean(indoc! {"
			func take(x: u32) {}
			func f(x: u32) {
				take({ x });
			}
		"});
		let found: Vec<_> = a.sema.resolutions_in(a.file).collect();
		let spans: Vec<_> = found.iter().map(|(span, _)| span.span).collect();
		let mut sorted = spans.clone();
		sorted.sort();
		sorted.dedup();
		assert_eq!(spans, sorted, "ordered, without a repeated name");
		// The shorthand is a label and a value at one name; the value wins.
		let shorthand = a.span("{ x }", "x");
		let at_shorthand: Vec<_> = found
			.iter()
			.filter(|(span, _)| span.span == shorthand)
			.map(|&(_, reference)| reference)
			.collect();
		assert_eq!(at_shorthand, [a.value("{ x }", "x")]);
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

	// ── Names in scope (`Semantics::names_at`) ──────────────────────────

	fn listed(names: &[String], name: &str) -> usize {
		names.iter().filter(|listed| *listed == name).count()
	}

	#[test]
	fn a_value_position_lists_locals_then_the_items_a_lookup_finds() {
		let analysis = Analysis::new(indoc! {"
			mod helpers {
			    pub func shared() {}
			}
			use helpers::*;
			const LIMIT: u32 = 3;
			func f(a: u32) {
			    local b: u32 = a;
			    // here
			}
		"});
		let names = analysis.names("here", NameUse::Value);
		assert_eq!(names[..2], ["b (local)", "a (local)"]);
		for item in ["LIMIT", "f", "shared", "True", "transmute"] {
			assert_eq!(listed(&names, item), 1, "`{item}` in {names:?}");
		}
		// A module is a type-tier name.
		assert_eq!(listed(&names, "helpers"), 0);
	}

	#[test]
	fn a_local_hides_an_item_of_its_name() {
		let analysis = Analysis::new(indoc! {"
			const x: u32 = 1;
			func f(x: u32) {
			    // here
			}
		"});
		let names = analysis.names("here", NameUse::Value);
		assert_eq!(listed(&names, "x (local)"), 1);
		assert_eq!(listed(&names, "x"), 0);
	}

	/// In a literal an outer local cannot be used, but it still takes its
	/// name there (E2140), so the item of that name is not offered either.
	#[test]
	fn in_static_data_an_outer_local_is_neither_usable_nor_an_item() {
		let analysis = Analysis::new(indoc! {"
			memory heap: u32;
			const x: u32 = 5;
			const y: u32 = 6;
			func f(x: u32) -> heap::&[u32] {
			    [
			        // here
			        1,
			    ]
			}
		"});
		let names = analysis.names("here", NameUse::Value);
		assert_eq!(listed(&names, "x (local)"), 0);
		assert_eq!(listed(&names, "x"), 0);
		assert_eq!(listed(&names, "y"), 1);
	}

	#[test]
	fn a_type_position_lists_parameters_then_type_items() {
		let analysis = Analysis::new(indoc! {"
			struct Point(x: u32);
			struct T();
			func f<T>(t: T) {
			    // here
			}
		"});
		let names = analysis.names("here", NameUse::Type);
		assert_eq!(names[0], "T (param)");
		// The parameter hides the struct of its name.
		assert_eq!(listed(&names, "T"), 0);
		for item in ["Point", "u32", "Ordering", "Bool"] {
			assert_eq!(listed(&names, item), 1, "`{item}` in {names:?}");
		}
		assert_eq!(listed(&names, "t (local)"), 0);
		// A function is a type too: its own item type (`local g: f = f;`).
		assert_eq!(listed(&names, "f"), 1);
	}

	/// A type position offers what `resolve_type_path` takes, and the
	/// namespaces a path goes on into; a bound what
	/// `resolve_trait_bound_path` takes, a trait or a typeset, and the same
	/// namespaces, with no parameter (a bound never reads them).
	#[test]
	fn a_type_and_a_bound_list_what_each_takes() {
		let analysis = Analysis::new(indoc! {"
			trait Show {}
			typeset Small { u8, u16 }
			mod shapes {}
			struct Point(x: u32);
			func f<T>(t: T) {
			    // here
			}
		"});
		let types = analysis.names("here", NameUse::Type);
		for name in ["T (param)", "Point", "u32", "f", "shapes"] {
			assert_eq!(listed(&types, name), 1, "`{name}` in {types:?}");
		}
		for name in ["Show", "Small", "Add", "PointerSize"] {
			assert_eq!(listed(&types, name), 0, "`{name}` in {types:?}");
		}
		let bounds = analysis.names("here", NameUse::Bound);
		for name in ["Show", "Small", "Add", "PointerSize", "shapes"] {
			assert_eq!(listed(&bounds, name), 1, "`{name}` in {bounds:?}");
		}
		for name in ["T (param)", "T", "Point", "u32", "f"] {
			assert_eq!(listed(&bounds, name), 0, "`{name}` in {bounds:?}");
		}
	}

	/// `NameUse::takes` is what the checker takes: a type position reports
	/// all but a type (`NotAType`), a bound all but a trait or a typeset, and
	/// an impl all but a trait (both `NotATraitBound`).
	#[test]
	fn each_use_takes_what_the_checker_takes() {
		const DECLARATIONS: &str = "
			mod m {}
			struct S();
			enum E(u8) { A = 0 }
			type Alias = u32;
			memory heap: u32;
			func g() {}
			global G: u32 = 0;
			trait Tr {}
			typeset Ts { u8 }
		";
		for name in [
			"m", "package", "S", "E", "Alias", "heap", "g", "G", "Tr", "Ts",
		] {
			for (used_as, written, code) in [
				(
					NameUse::Type,
					format!("func as_type(x: {name}) {{}}"),
					DiagnosticCode::NotAType,
				),
				(
					NameUse::Bound,
					format!("func as_bound<X: {name}>() {{}}"),
					DiagnosticCode::NotATraitBound,
				),
				(
					NameUse::Trait,
					format!("impl {name} for S {{}}"),
					DiagnosticCode::NotATraitBound,
				),
			] {
				let source = format!("{DECLARATIONS}\n{written}\n");
				let analysis = Analysis::new(&source);
				let kind = analysis
					.sema
					.declaration_kind(analysis.declaration(name, Tier::Type));
				let reported =
					(analysis.sema.diagnostics().iter()).any(|diagnostic| {
						diagnostic.code.as_deref() == Some(code.code())
					});
				assert_eq!(
					reported,
					!used_as.takes(kind),
					"`{name}` in `{written}`"
				);
			}
		}
	}

	/// What `names_in` lists in `tier` after the prefix written as `name`
	/// in `context`, in the function `f`, as the server asks: the prefix's
	/// meaning from `symbol_at`.
	fn names_after(
		analysis: &Analysis,
		context: &str,
		name: &str,
		used_as: NameUse,
	) -> Vec<String> {
		let span = analysis.span(context, name);
		let (_, reference) =
			analysis.sema.symbol_at(analysis.file, span.start).unwrap();
		let Definition::Item(prefix) = reference.definition() else {
			panic!("`{name}` is not an item");
		};
		// The function the path is written in.
		let declaration =
			Definition::Item(analysis.declaration("f", Tier::Value));
		let mut names: Vec<_> = analysis
			.sema
			.names_in(declaration, prefix, used_as)
			.into_iter()
			.map(|(name, _)| {
				analysis.strings.resolve(name).unwrap().to_string()
			})
			.collect();
		names.sort();
		names
	}

	#[test]
	fn after_a_prefix_its_namespace_lists_what_the_walk_finds() {
		let analysis = Analysis::new(indoc! {"
			mod shapes {
			    pub struct Square(pub side: u32);
			    pub func area() -> u32 { 1 }
			    func hidden() {}
			    pub enum Kind(u8) { A = 0, B }
			}
			func f() {
			    shapes::area();
			    shapes::Kind::A;
			}
		"});
		let prefix = "shapes::area";
		assert_eq!(
			names_after(&analysis, prefix, "shapes", NameUse::Value),
			["Square", "area"],
			"`hidden` is private to `shapes`"
		);
		// A constructor is a value only where every field is accessible.
		let private_field = Analysis::new(indoc! {"
			mod shapes { pub struct Square(side: u32); pub func area() {} }
			func f() { shapes::area(); }
		"});
		assert_eq!(
			names_after(
				&private_field,
				"shapes::area",
				"shapes",
				NameUse::Value
			),
			["area"]
		);
		assert_eq!(
			names_after(&analysis, prefix, "shapes", NameUse::Type),
			["Kind", "Square", "area", "package", "self", "super"],
			"a module's path keywords are bindings of its own"
		);
		assert_eq!(
			names_after(&analysis, "Kind::A", "Kind", NameUse::Value),
			["A", "B"]
		);
		// As a bound, a module's traits and its path keywords.
		let traits = Analysis::new(indoc! {"
			mod shapes { pub trait Show {} pub struct Square(); }
			func f() { shapes::Square(); }
		"});
		assert_eq!(
			names_after(&traits, "shapes::Square", "shapes", NameUse::Bound),
			["Show", "package", "self", "super"]
		);
	}

	#[test]
	fn after_a_type_nothing_is_listed() {
		let analysis = Analysis::new(indoc! {"
			struct P();
			impl P { pub func new() -> P { P() } }
			func f() { P::new(); }
		"});
		assert!(
			names_after(&analysis, "P::new", "P", NameUse::Value).is_empty()
		);
	}

	/// What `names_in_signature` lists for `owner`, as `name` for an item
	/// and `name (param)` for a type parameter.
	fn signature_names(
		analysis: &Analysis,
		owner: Definition,
		used_as: NameUse,
	) -> Vec<String> {
		analysis
			.sema
			.names_in_signature(owner, used_as)
			.into_iter()
			.map(|(name, definition)| {
				let name = analysis.strings.resolve(name).unwrap();
				match definition {
					Definition::TypeParam { .. } => format!("{name} (param)"),
					_ => name.to_string(),
				}
			})
			.collect()
	}

	#[test]
	fn a_signature_lists_its_parameters_and_its_impls_then_items() {
		let analysis = Analysis::new(indoc! {"
			struct Wrap<T>(value: T);
			trait Show { func show<U>(self: Self, u: U) -> u32; }
			impl<T> Show for Wrap<T> {
			    func show<U>(self: Self, u: U) -> u32 { 0 }
			}
			func free<A>(a: A) {}
		"});
		// The free function, found as the server finds it: by its name.
		let free = analysis
			.sema
			.definitions()
			.get(&SourceSpan::new(
				analysis.file,
				analysis.span("func free", "free"),
			))
			.copied()
			.unwrap();
		let names = signature_names(&analysis, free, NameUse::Type);
		assert_eq!(names[0], "A (param)");
		assert!(names.iter().any(|name| name == "Wrap"), "{names:?}");
		assert!(names.iter().any(|name| name == "u32"), "{names:?}");
		// The impl's method: its own parameter, then the impl's.
		let show = analysis
			.sema
			.definitions()
			.get(&SourceSpan::new(
				analysis.file,
				analysis.span("    func show", "show"),
			))
			.copied()
			.unwrap();
		let names = signature_names(&analysis, show, NameUse::Type);
		assert_eq!(names[..2], ["U (param)", "T (param)"]);
		// The impl's header, by its target as written.
		let target = SourceSpan::new(
			analysis.file,
			analysis.span("for Wrap<T>", "Wrap"),
		);
		let (_, header) = analysis
			.sema
			.impls()
			.find(|&(span, _)| span == target)
			.unwrap();
		let names = signature_names(&analysis, header, NameUse::Type);
		assert_eq!(names[0], "T (param)");
		assert!(!names.iter().any(|name| name == "U (param)"));
		// A signature has no locals: values are items only.
		let names = signature_names(&analysis, free, NameUse::Value);
		assert!(names.iter().any(|name| name == "free"), "{names:?}");
		assert!(!names.iter().any(|name| name == "a"), "{names:?}");
	}
}
