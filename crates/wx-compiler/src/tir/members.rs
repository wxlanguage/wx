//! Type-relative member resolution: given an already-resolved type
//! (concrete or abstract), find a function/const/associated-type member by
//! name. The companion to `paths.rs`, which only ever resolves *names*
//! through the namespace graph — this module picks up exactly where that
//! one's own doc comment says it has to stop: once a segment names
//! something that doesn't own a namespace, continuing needs impl dispatch
//! (`impls.rs`) or bound projection instead, neither of which involves the
//! namespace graph, `use`, or `Visibility` at all.

use string_interner::symbol::SymbolU32;

use crate::ast::DefId;

use super::defs::{
	BindingKey, BindingNamespace, InherentImplIndex, MemberKind,
	TraitImplIndex, TraitIndex,
};
use super::impls::ImplTarget;
use super::signatures::{
	AssocBindingKind, ItemLocation, QueryInfo, SignatureBuilder, TraitBound,
};
use super::types::{Type, TypeIndex};

/// What a type-relative member lookup found.
pub(super) enum TypeMemberLookup {
	NotFound,
	Found(TypeMemberTarget),
	/// Two or more *unrelated* traits each provide this name for this
	/// receiver — inherent-vs-trait precedence never lands here (inherent
	/// always wins outright, checked before any trait candidate at all), so
	/// this only ever holds trait-sourced candidates.
	Ambiguous(Box<[TypeMemberTarget]>),
	/// The bound combination itself already disagrees about this
	/// associated type's value (`merge_trait_bound` found two different
	/// `where{}` bindings for it and poisoned the merged entry to `ERROR`)
	/// — there is no candidate to name here, since the conflict is on the
	/// *value*, not on which trait provides it. The diagnostic was already
	/// pushed during the merge, so the caller reports nothing further.
	Conflicted,
}

pub(super) struct TypeMemberTarget {
	/// Carries the member's own `DefId` already — no separate `id` field
	/// needed alongside it.
	pub(super) kind: MemberKind,
	pub(super) source: MemberSource,
}

pub(super) enum MemberSource {
	Inherent(InherentImplIndex),
	/// A concrete `impl Trait for Type` provides (or overrides) this member.
	TraitImpl(TraitIndex, TraitImplIndex),
	/// No impl overrides it for this concrete type — the trait's own
	/// declaration applies as-is. Whether that declaration has a body is
	/// not this lookup's concern: an impl missing a required override is an
	/// ill-formed program, caught later by trait-conformance checking (the
	/// last checking phase, run only once every body is resolved) — not
	/// something name resolution needs to gate on. Mirrors rustc, which
	/// never reports an error at an access site for an incorrectly
	/// implemented trait member, only at the `impl` block that's missing
	/// it.
	TraitDefault(TraitIndex),
	/// Receiver is abstract (`TypeParam`/`AssocTypeProjection`): resolved
	/// through one of its own bounds, not a concrete impl at all. Concrete
	/// dispatch is deferred to monomorphization (mirrors the existing
	/// `GenericMethodCall`/`AbstractConstAccess` shape).
	Bound(TraitIndex),
}

impl SignatureBuilder<'_, '_> {
	/// Resolves `name` (in binding tier `tier` — `Value` for a
	/// function/const, `Type` for an associated type) as a member of
	/// `receiver`.
	pub(super) fn resolve_type_member(
		&mut self,
		receiver: TypeIndex,
		tier: BindingNamespace,
		name: SymbolU32,
	) -> TypeMemberLookup {
		let key = BindingKey::new(tier, name);
		match ImplTarget::from_type(self.types.resolve(receiver)) {
			Some(target) => self.resolve_concrete_member(target, key),
			None => self.resolve_bound_member(receiver, key),
		}
	}

	fn resolve_concrete_member(
		&mut self,
		target: ImplTarget,
		key: BindingKey,
	) -> TypeMemberLookup {
		// No forcing needed here: `SignatureRegistry::build` resolves every
		// impl header, inherent and trait alike, in its own dedicated pass
		// before anything else runs, precisely so `inherent_impl_dispatch`/
		// `trait_impl_dispatch` are already complete by the time any other
		// item's resolution — this included — could possibly reach here.

		// Inherent always wins outright — no trait candidate is even
		// consulted once one matches.
		for &index in self
			.inherent_impl_dispatch
			.get(&target)
			.map(Vec::as_slice)
			.unwrap_or(&[])
		{
			let impl_def = &self.defs.inherent_impls[usize::from(index)];
			if let Some(&member_index) = impl_def.bindings.get(&key) {
				let kind = impl_def.members[usize::from(member_index)].kind;
				return TypeMemberLookup::Found(TypeMemberTarget {
					kind,
					source: MemberSource::Inherent(index),
				});
			}
		}

		let mut candidates = Vec::new();
		for &(trait_index, impl_index) in self
			.trait_impl_dispatch
			.get(&target)
			.map(Vec::as_slice)
			.unwrap_or(&[])
		{
			let impl_def = &self.defs.trait_impls[usize::from(impl_index)];
			if let Some(&member_index) = impl_def.bindings.get(&key) {
				let kind = impl_def.members[usize::from(member_index)].kind;
				candidates.push(TypeMemberTarget {
					kind,
					source: MemberSource::TraitImpl(trait_index, impl_index),
				});
				continue;
			}
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			if let Some(&member_index) = trait_def.bindings.get(&key) {
				let kind = trait_def.members[usize::from(member_index)].kind;
				candidates.push(TypeMemberTarget {
					kind,
					source: MemberSource::TraitDefault(trait_index),
				});
			}
			// Else: this trait doesn't declare `name` at all — not a
			// candidate, nothing to record.
		}
		Self::classify(candidates)
	}

	/// `declared`'s bounds are only ever validated in isolation, each
	/// against its *own* supertrait chain, at the point that trait's own
	/// header resolved (`TraitSignature::implied_bounds`) — never as a
	/// *combination*. A trait's own `Self: B + C` is the one place that
	/// combination *is* checked eagerly (right there, since `D`'s own
	/// closure is what every future `T: D` bound will reuse); a
	/// function/struct/impl's own `T: B + C` never is, because nothing
	/// else ever reuses that specific combination — so if `B` and `C`
	/// disagree about some associated type, nothing has caught it before
	/// now. This is where that combination is finally checked, lazily,
	/// via the same `merge_trait_bound` a trait's own header uses.
	fn resolve_bound_member(
		&mut self,
		receiver: TypeIndex,
		key: BindingKey,
	) -> TypeMemberLookup {
		let declared: Box<[TraitBound]> = match self.types.resolve(receiver) {
			Type::TypeParam { owner, param_index } => {
				self.type_param_bounds(*owner, *param_index).into()
			}
			Type::AssocTypeProjection {
				trait_index,
				assoc_name,
				..
			} => self.assoc_type_bounds(*trait_index, *assoc_name),
			// Error/Infer/anything else `ImplTarget` also can't bucket and
			// that isn't one of the two abstract shapes — nothing to look
			// a member up on.
			_ => return TypeMemberLookup::NotFound,
		};

		// The full reachable set: every declared bound (one hop — for a
		// trait's own `Self` this already includes the trait itself,
		// reflexively, at index 0), plus everything each one transitively
		// implies (precomputed per-trait, so this is just union over
		// already-finished data, not a walk). Merged, not just deduped by
		// identity: `declared` can combine multiple, mutually unrelated
		// bounds (`T: B + C`) whose own transitive sets were never checked
		// against *each other* before.
		let mut reachable: Vec<TraitBound> = Vec::new();
		for bound in declared.iter() {
			self.merge_trait_bound(&mut reachable, bound);
		}
		for bound in declared.iter() {
			let implied: Box<[TraitBound]> =
				self.traits[usize::from(bound.trait_index)]
					.implied_bounds
					.clone();
			for further in implied.iter() {
				self.merge_trait_bound(&mut reachable, further);
			}
		}

		let mut candidates = Vec::new();
		for bound in &reachable {
			let trait_def = &self.defs.traits[usize::from(bound.trait_index)];
			if let Some(&member_index) = trait_def.bindings.get(&key) {
				// A poisoned `where{}` binding for this exact name means the
				// combination already disagrees about its value — already
				// diagnosed by `merge_trait_bound`, so there's no candidate
				// to report here, poisoned or not.
				let poisoned = bound.bindings.iter().any(|binding| {
					binding.name == key.symbol
						&& matches!(
							binding.kind,
							AssocBindingKind::Conflicting
						)
				});
				if poisoned {
					return TypeMemberLookup::Conflicted;
				}
				let kind = trait_def.members[usize::from(member_index)].kind;
				candidates.push(TypeMemberTarget {
					kind,
					source: MemberSource::Bound(bound.trait_index),
				});
			}
		}
		Self::classify(candidates)
	}

	/// The one-hop declared bounds on generic parameter `param_index`,
	/// declared by whichever item `owner` names. Every kind that can ever
	/// appear as a `TypeParam`'s `owner` stores its params' bounds
	/// somewhere — this is the one place that knows where, for each of
	/// them. Transitive expansion (supertraits-of-supertraits) is the
	/// caller's job (`resolve_bound_member`), via each returned bound's own
	/// `TraitSignature::implied_bounds` — not this method's concern.
	fn type_param_bounds(
		&self,
		owner: DefId,
		param_index: u32,
	) -> &[TraitBound] {
		let index = param_index as usize;
		match self.item_lookup[&owner] {
			// A trait's own `Self` — always index 0, the trait having no
			// generic params of its own to share the space with.
			// `declared_bounds` already has the reflexive `Self: ThisTrait`
			// entry at its own index 0 (see `TraitSignature`'s doc
			// comment), so there's nothing extra to add here.
			ItemLocation::Trait(idx) => {
				&self.traits[usize::from(idx)].declared_bounds
			}
			ItemLocation::Function(idx) => {
				&self.functions[usize::from(idx)].type_param_bounds[index]
			}
			ItemLocation::Struct(idx) => {
				&self.structs[usize::from(idx)].type_param_bounds[index]
			}
			ItemLocation::InherentImpl(idx) => {
				&self.inherent_impls[usize::from(idx)]
					.as_ref()
					.expect(
						"a TypeParam can only reference an impl whose header \
						 already resolved — that's what minted the TypeParam",
					)
					.type_param_bounds[index]
			}
			ItemLocation::TraitImpl(idx) => {
				&self.trait_impls[usize::from(idx)]
					.as_ref()
					.expect(
						"a TypeParam can only reference an impl whose header \
						 already resolved — that's what minted the TypeParam",
					)
					.type_param_bounds[index]
			}
			ItemLocation::TypeAlias(_) => &[],
			ItemLocation::Enum(_)
			| ItemLocation::TypeSet(_)
			| ItemLocation::Constant(_)
			| ItemLocation::TraitAssocType(_) => unreachable!(
				"none of these ever declare a generic param, so no \
				 `Type::TypeParam` can name one as its owner"
			),
		}
	}

	/// The resolved bounds on trait `trait_index`'s own associated type
	/// named `assoc_name` — forces that one associated type's own signature
	/// first, same reasoning as forcing `Self` before reading it.
	fn assoc_type_bounds(
		&mut self,
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
	) -> Box<[TraitBound]> {
		let key = BindingKey::ty(assoc_name);
		let Some(&member_index) = self.defs.traits[usize::from(trait_index)]
			.bindings
			.get(&key)
		else {
			// Already diagnosed wherever this projection was built — a
			// projection is only ever constructed against a name the trait
			// really declares.
			return Box::new([]);
		};
		let MemberKind::AssociatedType(def_id) = self.defs.traits
			[usize::from(trait_index)]
		.members[usize::from(member_index)]
		.kind
		else {
			return Box::new([]);
		};
		let _ = self.ensure_signature(QueryInfo {
			def_id,
			requested_at: None,
		});
		let Some(&ItemLocation::TraitAssocType(index)) =
			self.item_lookup.get(&def_id)
		else {
			unreachable!()
		};
		self.assoc_types[usize::from(index)].bounds.clone()
	}

	fn classify(mut candidates: Vec<TypeMemberTarget>) -> TypeMemberLookup {
		match candidates.len() {
			0 => TypeMemberLookup::NotFound,
			1 => TypeMemberLookup::Found(candidates.pop().unwrap()),
			_ => TypeMemberLookup::Ambiguous(candidates.into_boxed_slice()),
		}
	}
}
