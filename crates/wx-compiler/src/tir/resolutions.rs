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

use super::body::{BodyOwner, LocalIdx, ParamIdx, TargetIdx};
use super::decls::Declared;
use super::decls::{
	BindingKey, BindingLookup, DeclKind, FieldIdx, FieldOwner, FunctionIdx,
	InherentImplIdx, ItemLoc, MemberKind, NameUse, Namespace, Scope, Tier,
	TraitIdx, TraitImplIdx, UseItemIndex,
};
use super::members::MemberLookup;
use super::signatures::Semantics;
use super::types::{GenericEnvIdx, GenericEnvOwner, ImplKind};
use crate::ast::Keyword;
use crate::diagnostics::{SourceSpan, TextOffset};
use crate::vfs::FileId;
use string_interner::symbol::SymbolU32;

/// Where a name is written, and the role it plays there; see the module doc.
/// Entries order by position first, so what is written at one place is
/// adjacent.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Site {
	/// Looked up among types.
	Type(SourceSpan),
	/// Looked up among values.
	Value(SourceSpan),
	/// What picks out a declaration by where it is written: a named
	/// argument's parameter or field, a `break`'s label, the `break` or
	/// `continue` keyword itself, or by what a manifest declares: a package
	/// instance's key, its package.
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

	pub fn span(self) -> SourceSpan {
		match self {
			Site::Type(span) | Site::Value(span) | Site::Label(span) => span,
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
pub struct NameResolutions {
	pub by_site: BTreeMap<Site, Reference>,
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
		owner: FieldOwner,
		field: FieldIdx,
		access: AccessKind,
	},
	/// A named argument's parameter, of the function the call selected (a
	/// trait's declaration, for a call through an abstract type). This does
	/// not require the callee to have a body or a corresponding local.
	Parameter {
		function: FunctionIdx,
		parameter: ParamIdx,
	},
	/// A generic parameter, or a trait's own `Self`: its frame and position
	/// in it.
	TypeParam { env: GenericEnvIdx, index: u32 },
	/// A member selected through a type: `T::A`, `<X as Tr>::A`.
	Member(MemberKind),
	/// The label of a jump target of the body `owner`, named by a `break`
	/// or `continue`.
	Label { owner: BodyOwner, target: TargetIdx },
	/// A `break` keyword: the jump target of the body `owner` it leaves,
	/// whether or not a label names it.
	Break { owner: BodyOwner, target: TargetIdx },
	/// A `continue` keyword: the loop of the body `owner` it restarts; see
	/// `Break`.
	Continue { owner: BodyOwner, target: TargetIdx },
	/// A `return` keyword: the function whose body it leaves.
	Return { function: FunctionIdx },
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
		owner: FieldOwner,
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
	/// A jump target's label.
	Label {
		owner: BodyOwner,
		target: TargetIdx,
	},
	/// A loop or a `block`, which a `break` or `continue` jumps to; declared
	/// by its keyword.
	JumpTarget {
		owner: BodyOwner,
		target: TargetIdx,
	},
	/// A function's body, which a `return` leaves; declared by its `func`
	/// keyword.
	FunctionBody(FunctionIdx),
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
			Reference::Label { owner, target } => {
				Definition::Label { owner, target }
			}
			Reference::Break { owner, target }
			| Reference::Continue { owner, target } => {
				Definition::JumpTarget { owner, target }
			}
			Reference::Return { function } => {
				Definition::FunctionBody(function)
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

/// A member an entry of a bound's `where { .. }` block can name
/// (`Semantics::binding_names`).
#[derive(Clone, Copy)]
pub struct BindingName {
	pub name: SymbolU32,
	pub member: MemberKind,
	/// The supertrait that declares it, for one the bound's trait inherits.
	pub inherited_from: Option<TraitIdx>,
}

impl Semantics {
	/// What kind of declaration `loc` names.
	pub fn declaration_kind(&self, loc: ItemLoc) -> DeclKind {
		loc.symbol_kind(&self.decls)
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
			Definition::Label { owner, target } => {
				let label = self.owner_body(owner)?.target(target).label?;
				Some(SourceSpan::new(self.owner_file(owner), label.span))
			}
			Definition::JumpTarget { owner, target } => {
				let body = self.owner_body(owner)?;
				Some(SourceSpan::new(
					self.owner_file(owner),
					body.target_keyword_span(target),
				))
			}
			Definition::FunctionBody(function) => {
				let decl = &decls.functions[usize::from(function)];
				Some(SourceSpan::new(
					decls.file_id(decl.loc),
					Keyword::Func.span_at(decl.func_at),
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
				let at = usize::from(parameter);
				if at >= function.params.len() {
					return None;
				}
				decls.params.name(function.params, at)?;
				let span = decls.params.name_span(function.params, at);
				Some(SourceSpan::new(decls.file_id(function.loc), span))
			}
		}
	}

	fn field_definition(
		&self,
		owner: FieldOwner,
		field: FieldIdx,
	) -> Option<SourceSpan> {
		let fields = owner.fields(&self.decls);
		if usize::from(field) >= fields.len() {
			return None;
		}
		self.decls.fields.name(fields, field)?;
		Some(SourceSpan::new(
			self.decls.file_id(owner.loc(&self.decls)),
			self.decls.fields.name_span(fields, field),
		))
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
		offset: TextOffset,
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
	pub(super) fn signature_scope(
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
	/// or hides one. A value also lists the namespaces a path can start
	/// with, from the type tier, where no local hides them.
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
		// A local hides a value, and a type parameter a type, a value path's
		// prefix included.
		let hidden = |tier: Tier, name: SymbolU32| match (used_as, tier) {
			(NameUse::Value, Tier::Value) => is_local(name),
			(NameUse::Value | NameUse::Type, Tier::Type) => {
				self.generic_envs.resolve(env, name).is_some()
			}
			_ => false,
		};
		let roots = [
			Namespace::from(namespace),
			Namespace::Package(self.decls.namespaces.core_package()),
		];
		for &tier in used_as.listed_tiers() {
			for name in self.candidates(&roots, tier) {
				if hidden(tier, name) {
					continue;
				}
				let key = BindingKey::new(tier, name);
				let lookup = self.decls.namespaces.lookup_unqualified(
					&self.decls.use_items,
					namespace,
					key,
				);
				if let BindingLookup::Found {
					target, reachable, ..
				} = lookup && let Some(loc) = target.loc()
					&& used_as.admits(tier, self.declaration_kind(loc))
					&& reachable
				{
					found.push((name, Definition::Item(loc)));
				}
			}
		}
	}

	/// Every name a path written in `accessor` can continue with, used as
	/// `used_as` says, after a prefix that means `prefix`, with what it would
	/// refer to: what the walk's lookup of the next segment finds in the
	/// namespace `prefix` enters (`Namespaces::lookup`), accessible from
	/// `accessor`, that can be written there. Empty when `prefix` enters no
	/// namespace: what follows a type is one of its members, which the member
	/// search finds. A `use` leaf (`NameUse::Import`) binds its name in both
	/// tiers, so each name is listed once, and never a path keyword: the
	/// scope binds its own already.
	pub fn names_in(
		&self,
		accessor: Scope,
		prefix: ItemLoc,
		used_as: NameUse,
	) -> Vec<(SymbolU32, Definition)> {
		let namespaces = &self.decls.namespaces;
		let Some(base) = namespaces.entered_by(prefix) else {
			return Vec::new();
		};
		let mut found: Vec<(SymbolU32, Definition)> = Vec::new();
		for &tier in used_as.listed_tiers() {
			for name in self.candidates(&[base], tier) {
				if used_as == NameUse::Import
					&& (is_path_keyword(name)
						|| found.iter().any(|&(listed, _)| listed == name))
				{
					continue;
				}
				let key = BindingKey::new(tier, name);
				if let BindingLookup::Found {
					target, reachable, ..
				} = namespaces.lookup(
					&self.decls.use_items,
					accessor,
					base,
					key,
				) && let Some(loc) = target.loc()
					&& used_as.admits(tier, self.declaration_kind(loc))
					&& reachable
				{
					found.push((name, Definition::Item(loc)));
				}
			}
		}
		found
	}

	/// Every name a bare identifier written directly in `scope`, outside any
	/// declaration, can mean, used as `used_as` says: a `use` path's first
	/// segment, looked up as any path's first segment is (the scope, then the
	/// core prelude), with no type parameters or locals in scope.
	pub fn names_in_scope(
		&self,
		scope: Scope,
		used_as: NameUse,
	) -> Vec<(SymbolU32, Definition)> {
		let mut found = Vec::new();
		self.scope_names(
			scope,
			GenericEnvIdx::ROOT,
			used_as,
			|_| false,
			&mut found,
		);
		found
	}

	/// Every member an entry of a `where { .. }` block in a bound of the
	/// trait declared at `bound` can name, in `tiers` (a type's entry, a
	/// `const` one's, or one not marked yet): the trait's own, or else the
	/// one its supertraits declare, where only one does, as the checker
	/// selects a binding's target (`binding_target`). Nearest first:
	/// the trait's own, then its supertraits' (`written_supertraits`), each
	/// in declaration order.
	pub fn binding_names(
		&self,
		bound: ItemLoc,
		tiers: &[Tier],
	) -> Vec<BindingName> {
		let DeclKind::Trait(trait_index) = self.declaration_kind(bound) else {
			return Vec::new();
		};
		let decls = &self.decls;
		// A function is no binding's target.
		let declared = |trait_index, key| {
			decls
				.declared_trait_member(trait_index, key)
				.filter(|kind| {
					matches!(
						kind,
						MemberKind::AssociatedType(_) | MemberKind::Constant(_)
					)
				})
		};
		let traits = self.written_supertraits(trait_index);
		let supertraits = &traits[1..];
		let mut found: Vec<BindingName> = Vec::new();
		for &owner in &traits {
			for member in &decls.traits[usize::from(owner)].members {
				let key = decls.member_key(member.kind);
				if !tiers.contains(&key.tier)
					|| found.iter().any(|found| {
						found.name == key.symbol
							&& found.member.tier() == key.tier
					}) {
					continue;
				}
				let selected = match declared(trait_index, key) {
					Some(member) => Some((member, None)),
					None => {
						let declaring = (supertraits.iter().copied()).filter(
							|&supertrait| declared(supertrait, key).is_some(),
						);
						match Semantics::select_declared_member(
							decls, declaring, key,
						) {
							MemberLookup::Found(member) => {
								Some((member.selected_kind(decls), Some(owner)))
							}
							_ => None,
						}
					}
				};
				let Some((member, inherited_from)) = selected else {
					continue;
				};
				found.push(BindingName {
					name: key.symbol,
					member,
					inherited_from,
				});
			}
		}
		found
	}

	/// Every member a path can name after a trait-qualified root,
	/// `<T as Tr>::`, `bound` being `Tr`'s declaration, used as `used_as`
	/// says (`NameUse::takes_member`): `Tr`'s own declarations, as its
	/// lookup searches them (`resolve_trait_member_declaration`), in
	/// declaration order. `T` does not choose them: whether it implements
	/// `Tr` is checked apart.
	pub fn trait_member_names(
		&self,
		bound: ItemLoc,
		used_as: NameUse,
	) -> Vec<(SymbolU32, Definition)> {
		let DeclKind::Trait(trait_index) = self.declaration_kind(bound) else {
			return Vec::new();
		};
		let decls = &self.decls;
		let trait_decl = &decls.traits[usize::from(trait_index)];
		let mut found = Vec::new();
		for (index, member) in trait_decl.members.iter().enumerate() {
			let key = decls.member_key(member.kind);
			if used_as.takes_member(member.kind)
				&& trait_decl
					.bindings
					.get(&key)
					.is_some_and(|&at| usize::from(at) == index)
			{
				found.push((key.symbol, Definition::Member(member.kind)));
			}
		}
		found
	}

	/// `trait_index` and every trait it inherits, nearest first: the ones
	/// it writes itself, then theirs, breadth-first. A trait's env holds
	/// every supertrait; the ones it writes itself are those brought in by
	/// their own bound.
	fn written_supertraits(&self, trait_index: TraitIdx) -> Vec<TraitIdx> {
		let mut traits = vec![trait_index];
		let mut next = 0;
		while let Some(&current) = traits.get(next) {
			next += 1;
			let env = self.traits[usize::from(current)].env;
			let own_self = self.generic_envs.param_types(env)[0];
			let range = self.assumption_envs.requirements(env).range();
			for clause in self.clauses.traits(range) {
				if clause.subject == own_self
					&& clause.source == clause.origin
					&& !traits.contains(&clause.trait_index)
				{
					traits.push(clause.trait_index);
				}
			}
		}
		traits
	}

	/// The scope `declaration` is written in, where a path in its signature
	/// or body is looked up (see `names_in_signature` for what it may be).
	pub fn declaration_scope(&self, declaration: Definition) -> Option<Scope> {
		Some(self.signature_scope(declaration)?.0)
	}

	/// The scope a module or an import block declared at `loc` opens, where
	/// the items written inside it are.
	pub fn scope_entered_by(&self, loc: ItemLoc) -> Option<Scope> {
		self.decls.namespaces.entered_by(loc)?.as_scope()
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

/// `self`, `super` or `package`, which every scope binds itself.
fn is_path_keyword(name: SymbolU32) -> bool {
	[Keyword::SelfLower, Keyword::Super, Keyword::Package]
		.iter()
		.any(|keyword| keyword.symbol() == name)
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
	use crate::tir::decls::{BindingKey, DeclKind, Scope, StructIdx};
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
			let offset = TextOffset::from(
				self.source.find(&format!("// {mark}")).unwrap() as u32,
			);
			// Every test writes its mark in `f`.
			let owner = BodyOwner::Function(self.function_index("f"));
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
			TextSpan::from(start as u32..(start + name.len()) as u32)
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
				.map(|name| {
					ast::PathSegment::new(Spanned {
						inner: self.strings.get(name).unwrap(),
						span: TextSpan::empty_at(TextOffset::ZERO),
					})
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
				&[],
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
				owner: FieldOwner::Struct(a.struct_index("A")),
				field: FieldIdx::new(0),
				access: AccessKind::Write,
			}
		);
		assert_eq!(
			a.reference("\n\ta.value\n", "value"),
			Reference::Field {
				owner: FieldOwner::Struct(a.struct_index("A")),
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
				owner: FieldOwner::Struct(a.struct_index("B")),
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
			owner: FieldOwner::Struct(a.struct_index("S")),
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
	fn argument_labels_refer_to_the_selected_functions_parameter() {
		let a = Analysis::clean(indoc! {"
			trait Make: StackValue {
				func make(value: u32) -> Self;
			}
			struct S(value: u32);
			impl Make for S {
				func make(value: u32) -> Self { S(0) }
			}
			func concrete(value: u32) -> S {
				S::make({ value })
			}
			func generic<T: Make>(value: u32) -> T {
				T::make({ value })
			}
		"});
		let make = a.strings.get("make").unwrap();
		let DeclKind::Trait(trait_index) = a.resolve("Make", Tier::Type) else {
			panic!("expected a trait");
		};
		let Some(MemberKind::Function(declaration)) = a
			.sema
			.decls
			.declared_trait_member(trait_index, BindingKey::value(make))
		else {
			panic!("expected the trait's function declaration");
		};
		let decls = &a.sema.decls;
		let implementation = (0..decls.functions.len())
			.map(|index| FunctionIdx::new(index as u32))
			.find(|&function| {
				let decl = &decls.functions[usize::from(function)];
				matches!(
					decl.owner,
					crate::tir::decls::MemberOwner::TraitImpl(_)
				) && decls.name(function).inner == make
					&& decls.file_id(decl.loc) == a.file
			})
			.unwrap();
		// A concrete call names the impl's parameter; a call through the
		// trait, the declaration's, which has no body.
		for (call, caller, function) in [
			("S::make({ value })", "concrete", implementation),
			("T::make({ value })", "generic", declaration),
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
				owner: FieldOwner::Struct(a.struct_index("S")),
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
				owner: FieldOwner::Struct(a.struct_index("S")),
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
				owner: FieldOwner::Struct(a.struct_index("m::S")),
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
				owner: FieldOwner::Struct(a.struct_index("S")),
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
			enum E(value: u8) { A = 0, B = 1 }
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
					owner: FieldOwner::Struct(a.struct_index(owner)),
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
				owner: FieldOwner::Struct(a.struct_index("Rows")),
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
					owner: FieldOwner::Struct(a.struct_index("Buffer")),
					field: FieldIdx::new(0),
					access
				}
			);
		}
		for context in ["p.pointer[i] =", "p.pointer[i] +="] {
			assert_eq!(
				a.reference(context, "pointer"),
				Reference::Field {
					owner: FieldOwner::Struct(a.struct_index("Buffer")),
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
				owner: FieldOwner::Struct(a.struct_index("Buffer")),
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
		// A module is a type-tier name, which a value path can start with.
		for namespace in ["helpers", "core", "package", "self"] {
			assert_eq!(
				listed(&names, namespace),
				1,
				"`{namespace}` in {names:?}"
			);
		}
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
			enum E(value: u8) { A = 0 }
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
	/// meaning, as a value or else as a type.
	fn names_after(
		analysis: &Analysis,
		context: &str,
		name: &str,
		used_as: NameUse,
	) -> Vec<String> {
		let reference = analysis
			.at(context, name, Tier::Value)
			.or_else(|| analysis.at(context, name, Tier::Type))
			.unwrap();
		let Definition::Item(prefix) = reference.definition() else {
			panic!("`{name}` is not an item");
		};
		// The function the path is written in.
		let declaration =
			Definition::Item(analysis.declaration("f", Tier::Value));
		let accessor = analysis.sema.declaration_scope(declaration).unwrap();
		sorted_names(
			analysis,
			analysis.sema.names_in(accessor, prefix, used_as),
		)
	}

	fn sorted_names(
		analysis: &Analysis,
		names: Vec<(SymbolU32, Definition)>,
	) -> Vec<String> {
		let mut names: Vec<_> = names
			.into_iter()
			.map(|(name, _)| {
				analysis.strings.resolve(name).unwrap().to_string()
			})
			.collect();
		names.sort();
		names
	}

	#[test]
	fn a_use_path_continues_into_namespaces_and_ends_in_anything() {
		let analysis = Analysis::new(indoc! {"
			mod shapes {
			    pub struct Square(pub side: u32);
			    pub func area() -> u32 { 1 }
			    pub const SIDES: u32 = 4;
			    func hidden() {}
			    pub mod inner {}
			    pub enum Kind(value: u8) { A = 0, B }
			}
			use shapes::area;
			func f() {}
		"});
		let root =
			analysis.sema.decls.file_namespaces[analysis.file.as_usize()];
		let shapes = analysis.declaration("shapes", Tier::Type);
		assert_eq!(
			sorted_names(
				&analysis,
				analysis.sema.names_in(root, shapes, NameUse::Namespace)
			),
			["Kind", "inner", "package", "self"]
		);
		// Each name once, though `Square` and `area` are in both tiers, and
		// no path keyword, which would bind the scope's own name again.
		assert_eq!(
			sorted_names(
				&analysis,
				analysis.sema.names_in(root, shapes, NameUse::Import)
			),
			["Kind", "SIDES", "Square", "area", "inner"],
			"`hidden` is private to `shapes`"
		);
	}

	#[test]
	fn a_use_path_starts_in_its_scope_and_the_prelude() {
		let analysis = Analysis::new(indoc! {"
			mod shapes {
			    pub mod inner {}
			    pub func area() -> u32 { 1 }
			}
			func f() {}
		"});
		let first = |scope| {
			sorted_names(
				&analysis,
				analysis.sema.names_in_scope(scope, NameUse::Namespace),
			)
		};
		let root = first(
			analysis.sema.decls.file_namespaces[analysis.file.as_usize()],
		);
		for name in ["shapes", "core", "package", "self", "Bool", "Ordering"] {
			assert!(root.contains(&name.to_string()), "{name}: {root:?}");
		}
		for name in ["f", "area", "i32", "super"] {
			assert!(!root.contains(&name.to_string()), "{name}: {root:?}");
		}
		let shapes = analysis.declaration("shapes", Tier::Type);
		let inside = first(analysis.sema.scope_entered_by(shapes).unwrap());
		for name in ["inner", "super", "self", "package", "Bool"] {
			assert!(inside.contains(&name.to_string()), "{name}: {inside:?}");
		}
		// `core` is bound in the package's root scope only.
		for name in ["shapes", "core", "area"] {
			assert!(!inside.contains(&name.to_string()), "{name}: {inside:?}");
		}
	}

	#[test]
	fn after_a_prefix_its_namespace_lists_what_the_walk_finds() {
		let analysis = Analysis::new(indoc! {"
			mod shapes {
			    pub struct Square(pub side: u32);
			    pub func area() -> u32 { 1 }
			    func hidden() {}
			    pub enum Kind(value: u8) { A = 0, B }
			}
			func f() {
			    shapes::area();
			    shapes::Kind::A;
			}
		"});
		let prefix = "shapes::area";
		assert_eq!(
			names_after(&analysis, prefix, "shapes", NameUse::Value),
			// An enum's name is a value path too (`Kind::A`, `Kind(n)`), and
			// the module's public path keywords continue it.
			["Kind", "Square", "area", "package", "self"],
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
			["area", "package", "self"]
		);
		assert_eq!(
			names_after(&analysis, prefix, "shapes", NameUse::Type),
			["Kind", "Square", "area", "package", "self"],
			"a module's public path keywords are bindings of its own"
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
			["Show", "package", "self"]
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
		let free = Definition::Item(analysis.declaration("free", Tier::Value));
		let names = signature_names(&analysis, free, NameUse::Type);
		assert_eq!(names[0], "A (param)");
		assert!(names.iter().any(|name| name == "Wrap"), "{names:?}");
		assert!(names.iter().any(|name| name == "u32"), "{names:?}");
		// The impl's method: its own parameter, then the impl's.
		let decls = &analysis.sema.decls;
		let show_span = SourceSpan::new(
			analysis.file,
			analysis.span("    func show", "show"),
		);
		let show = decls
			.namespaces
			.keys()
			.find(|&key| decls.declaration_span(key) == show_span)
			.map(Definition::Item)
			.unwrap();
		let names = signature_names(&analysis, show, NameUse::Type);
		assert_eq!(names[..2], ["U (param)", "T (param)"]);
		// The impl's header, by its target as written.
		let target = SourceSpan::new(
			analysis.file,
			analysis.span("for Wrap<T>", "Wrap"),
		);
		let header = (0..analysis.sema.trait_impls.len())
			.map(|index| {
				Definition::TraitImplTarget(TraitImplIdx::new(index as u32))
			})
			.find(|&header| {
				analysis.sema.definition_span(header) == Some(target)
			})
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
