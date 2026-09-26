//! Type-relative member resolution: given an already-resolved type
//! (concrete or abstract), find a function/const/associated-type member by
//! name. The companion to `paths.rs`, which only ever resolves *names*
//! through the namespace graph — this module picks up exactly where that
//! one's own doc comment says it has to stop: once a segment names
//! something that doesn't own a namespace, continuing needs impl dispatch
//! (`impls.rs`) or bound projection instead, neither of which involves the
//! namespace graph, `use`, or `Visibility` at all.

use string_interner::symbol::SymbolU32;

use crate::diagnostics::SourceSpan;
use crate::tir::types::TypeEnvOwner;

use super::bounds::ImpliedTraitBound;
use super::defs::{
	AssocTypeIdx, BindingKey, BindingNamespace, InherentImplIdx, MemberKind,
	TraitIdx, TraitImplIdx,
};
use super::impls::ImplTarget;
use super::signatures::{
	QueryInfo, SignatureBuilder, SignatureLocation, SignatureStatus,
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
}

pub(super) struct TypeMemberTarget {
	/// Carries the index into the member's definition arena.
	pub(super) kind: MemberKind,
	pub(super) source: MemberSource,
}

pub(super) enum MemberSource {
	Inherent(InherentImplIdx),
	/// A concrete `impl Trait for Type` provides (or overrides) this member.
	TraitImpl(TraitIdx, TraitImplIdx),
	/// No impl overrides it for this concrete type — the trait's own
	/// declaration applies as-is. Whether that declaration has a body is
	/// not this lookup's concern: an impl missing a required override is an
	/// ill-formed program, caught later by trait-conformance checking (the
	/// last checking phase, run only once every body is resolved) — not
	/// something name resolution needs to gate on. Mirrors rustc, which
	/// never reports an error at an access site for an incorrectly
	/// implemented trait member, only at the `impl` block that's missing
	/// it.
	TraitDefault(TraitIdx),
	/// Receiver is abstract (`TypeParam`/`AssocTypeProjection`): resolved
	/// through one of its own bounds, not a concrete impl at all. Concrete
	/// dispatch is deferred to monomorphization (mirrors the existing
	/// `GenericMethodCall`/`AbstractConstAccess` shape).
	Bound(TraitIdx),
}

impl SignatureBuilder<'_, '_> {
	/// Resolves `name` (in binding tier `tier` — `Value` for a
	/// function/const, `Type` for an associated type) as a member of
	/// `receiver`. `reference` is the span of whatever named `receiver` in
	/// the first place — threaded through to `ensure_assoc_type_signature`,
	/// the one path below that can force another item's signature and so
	/// needs a real "why" to attach to a cycle diagnostic.
	pub(super) fn resolve_type_member(
		&mut self,
		receiver: TypeIndex,
		tier: BindingNamespace,
		name: SymbolU32,
		reference: SourceSpan,
	) -> TypeMemberLookup {
		let key = BindingKey::new(tier, name);
		match ImplTarget::from_type(self.types.resolve(receiver)) {
			Some(target) => self.resolve_concrete_member(target, key),
			None => self.resolve_bound_member(receiver, key, reference),
		}
	}

	fn resolve_concrete_member(
		&mut self,
		target: ImplTarget,
		key: BindingKey,
	) -> TypeMemberLookup {
		// No forcing needed here: ImplDispatch was built from declarations
		// before signature resolution began.

		// Inherent always wins outright — no trait candidate is even
		// consulted once one matches.
		for &index in self.impl_dispatch.inherent_candidates(target) {
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
		for &(trait_index, impl_index) in
			self.impl_dispatch.trait_candidates(target)
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

	fn resolve_bound_member(
		&mut self,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> TypeMemberLookup {
		match self.types.resolve(receiver) {
			Type::TypeParam { env, param_index } => self
				.candidates_from_implied(
					&self.param_bounds[usize::from(*env)]
						[*param_index as usize]
						.implied_bounds,
					key,
					match self.type_envs.frame_owner(*env) {
						TypeEnvOwner::Trait(trait_index) => Some(trait_index),
						_ => None,
					},
				),
			Type::AssocTypeProjection {
				trait_index,
				assoc_name,
				..
			} => {
				let Some(assoc_type_index) = self.ensure_assoc_type_signature(
					*trait_index,
					*assoc_name,
					reference,
				) else {
					return TypeMemberLookup::NotFound;
				};
				self.candidates_from_implied(
					&self.assoc_types[usize::from(assoc_type_index)]
						.as_ref()
						.expect("trait associated type signature is resolved")
						.implied_bounds,
					key,
					None,
				)
			}
			// Error/Infer/anything else `ImplTarget` also can't bucket and
			// that isn't one of the two abstract shapes — nothing to look
			// a member up on.
			_ => TypeMemberLookup::NotFound,
		}
	}

	/// Turns an already-merged implied set into a lookup result — shared
	/// between all three receiver shapes `resolve_bound_member` handles.
	/// Purely identity: which member definition this name names. Whether the
	/// combination's `where { .. }` bindings for it actually agree
	/// (`MergedBindingKind::Conflicting`, already diagnosed once by
	/// `union_trait_bound`) is a fact about this associated type's *value*,
	/// not about its identity — `A::X` is `A::X` regardless of whether `B`
	/// and `C` agree what it equals — so it's irrelevant here. It only
	/// matters to whatever eventually normalizes/substitutes this
	/// projection, which isn't this function's job.
	fn candidates_from_implied(
		&self,
		bounds: &[ImpliedTraitBound],
		key: BindingKey,
		reflexive: Option<TraitIdx>,
	) -> TypeMemberLookup {
		let mut candidates = Vec::new();
		for (trait_index, _bound) in reflexive
			.into_iter()
			.map(|index| (index, None))
			.chain(bounds.iter().map(|bound| (bound.trait_index, Some(bound))))
		{
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			if let Some(&member_index) = trait_def.bindings.get(&key) {
				let kind = trait_def.members[usize::from(member_index)].kind;
				candidates.push(TypeMemberTarget {
					kind,
					source: MemberSource::Bound(trait_index),
				});
			}
		}
		Self::classify(candidates)
	}

	/// Ensures trait `trait_index`'s associated type named `assoc_name` has
	/// a resolved signature, and returns its index — `type Size: PointerSize`
	/// doesn't get its own signature computed until something demands it,
	/// same reasoning as forcing `Self` before reading it.
	///
	/// `None` covers two situations a caller doesn't need to tell apart:
	/// `assoc_name` isn't actually one of `trait_index`'s associated types
	/// (already diagnosed wherever this projection/binding was built, since
	/// one is only ever constructed against a name the trait really
	/// declares), or the query closed a cycle — diagnosed here, once, by
	/// whichever call is the first to discover it (see `SignatureStatus`'s
	/// own `CycleReported` doc comment for why a second, independent
	/// rediscovery has to stay silent instead of reporting again).
	///
	/// `pub(super)`: also the entry point `bounds.rs` uses to find an
	/// associated-type binding's own declared bound (`type Size: Bound`)
	/// when checking a written `where { Size = T }` against it — see
	/// `satisfaction::type_satisfies_trait`.
	pub(super) fn ensure_assoc_type_signature(
		&mut self,
		trait_index: TraitIdx,
		assoc_name: SymbolU32,
		requested_at: SourceSpan,
	) -> Option<AssocTypeIdx> {
		let key = BindingKey::ty(assoc_name);
		let &member_index = self.defs.traits[usize::from(trait_index)]
			.bindings
			.get(&key)?;
		let MemberKind::AssociatedType(assoc_type_index) = self.defs.traits
			[usize::from(trait_index)]
		.members[usize::from(member_index)]
		.kind
		else {
			return None;
		};
		let def_id =
			self.defs.assoc_types[usize::from(assoc_type_index)].def_id;
		match self.ensure_signature(QueryInfo {
			def_id,
			requested_at: Some(requested_at),
		}) {
			SignatureStatus::Resolved(SignatureLocation::TraitAssocType(
				index,
			)) => Some(index),
			SignatureStatus::Resolved(_) => unreachable!(
				"an AssociatedType member's DefId always resolves to SignatureLocation::TraitAssocType"
			),
			SignatureStatus::Cycle => {
				let diagnostic =
					self.report_cyclic_assoc_type_bound(def_id, requested_at);
				self.diagnostics.push(diagnostic);
				None
			}
			SignatureStatus::CycleReported => None,
		}
	}

	fn classify(mut candidates: Vec<TypeMemberTarget>) -> TypeMemberLookup {
		match candidates.len() {
			0 => TypeMemberLookup::NotFound,
			1 => TypeMemberLookup::Found(candidates.pop().unwrap()),
			_ => TypeMemberLookup::Ambiguous(candidates.into_boxed_slice()),
		}
	}
}
