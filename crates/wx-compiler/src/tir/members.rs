//! Type-relative member resolution: given an already-resolved type
//! (concrete or abstract), find a function/const/associated-type member by
//! name. The companion to `paths.rs`, which only ever resolves *names*
//! through the namespace graph — this module picks up exactly where that
//! one's own doc comment says it has to stop: once a segment names
//! something that doesn't own a namespace, continuing needs impl dispatch
//! (`impls.rs`) or bound projection instead, neither of which involves the
//! namespace graph, `use`, or `Visibility` at all.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{self, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::small_vec::SmallVec;
use crate::vfs::FileId;

use super::assumptions::{
	AssumptionContext, AssumptionKind, QueryError, QueryResult,
};
use super::bounds::{Readiness, report_not_an_associated_type};
use super::defs::{
	AssocTypeIdx, AstNodeRef, BindingKey, BindingNamespace, DefinitionRegistry,
	InherentImplIdx, MemberKind, TraitIdx, TraitImplIdx,
};
use super::impls::ImplTarget;
use super::obligations::Obligation;
use super::signatures::{
	QueryInfo, SignatureBuilder, SignatureLocation, SignatureStatus,
};
use super::types::{Type, TypeIndex};

/// What a type-relative member lookup found.
pub(super) enum TypeMemberLookup {
	/// A dependency has already failed; the caller must not diagnose absence.
	Error,
	/// Selecting a declaration needs facts that are not ready yet.
	Pending,
	NotFound,
	Found(TypeMemberTarget),
	/// Two or more *unrelated* traits each provide this name for this
	/// receiver — inherent-vs-trait precedence never lands here (inherent
	/// always wins outright, checked before any trait candidate at all), so
	/// this only ever holds trait-sourced candidates.
	Ambiguous(Box<[TypeMemberTarget]>),
}

#[derive(Clone, Copy)]
pub(super) struct TypeMemberTarget {
	/// Trait-associated types always name the trait declaration, even when
	/// `source` selects an impl override. Value members name the selected
	/// definition as before. Provider values are accessed separately.
	pub(super) kind: MemberKind,
	pub(super) source: MemberSource,
}

#[derive(Clone, Copy)]
pub(super) enum MemberSource {
	Inherent(InherentImplIdx),
	/// A concrete `impl Trait for Type` provides (or overrides) this member.
	TraitImpl(TraitIdx, TraitImplIdx),
	/// No impl override: the trait declaration may supply a default.
	/// An absent required member needs error recovery; conformance checking
	/// owns the diagnostic.
	TraitDefault(TraitIdx, TraitImplIdx),
	/// Receiver is abstract (`TypeParam`/`AssocTypeProjection`): resolved
	/// through one of its own bounds, not a concrete impl at all. Concrete
	/// dispatch is deferred to monomorphization (mirrors the existing
	/// `GenericMethodCall`/`AbstractConstAccess` shape).
	Bound(TraitIdx),
}

/// An associated-type index known to refer to a value provided by an impl:
///
/// ```text
/// trait Trait { type Item; }          // declaration
/// impl Trait for T { type Item = U; } // value provider
/// ```
///
/// This wraps the impl's `Item` index. Its value may still need to be resolved,
/// but callers can rely on that value being present after resolution.
#[derive(Clone, Copy)]
pub(super) struct ImplAssocTypeIdx(AssocTypeIdx);

impl ImplAssocTypeIdx {
	pub(super) fn index(self) -> AssocTypeIdx {
		self.0
	}
}

impl DefinitionRegistry {
	pub(super) fn declared_trait_member(
		&self,
		trait_index: TraitIdx,
		key: BindingKey,
	) -> Option<MemberKind> {
		let definition = &self.traits[usize::from(trait_index)];
		definition
			.bindings
			.get(&key)
			.map(|&index| definition.members[usize::from(index)].kind)
	}

	/// Keeps type identity on the declaration while preserving value-member
	/// override selection. An undeclared impl-associated type is not a trait
	/// projection; full impl conformance checking will diagnose that member.
	pub(super) fn concrete_trait_member(
		&self,
		trait_index: TraitIdx,
		impl_index: TraitImplIdx,
		key: BindingKey,
	) -> Option<TypeMemberTarget> {
		let trait_def = &self.traits[usize::from(trait_index)];
		let declared = trait_def
			.bindings
			.get(&key)
			.map(|&index| trait_def.members[usize::from(index)].kind);
		let impl_def = &self.trait_impls[usize::from(impl_index)];
		if let Some(&index) = impl_def.bindings.get(&key) {
			let kind = match impl_def.members[usize::from(index)].kind {
				MemberKind::AssociatedType(_) => declared?,
				kind => kind,
			};
			Some(TypeMemberTarget {
				kind,
				source: MemberSource::TraitImpl(trait_index, impl_index),
			})
		} else {
			declared.map(|kind| TypeMemberTarget {
				kind,
				source: MemberSource::TraitDefault(trait_index, impl_index),
			})
		}
	}

	/// Returns the impl's value-providing associated type for this declaration.
	pub(super) fn impl_assoc_type_for(
		&self,
		impl_index: TraitImplIdx,
		declaration: AssocTypeIdx,
	) -> Option<ImplAssocTypeIdx> {
		let declaration = &self.assoc_types[usize::from(declaration)];
		let impl_def = &self.trait_impls[usize::from(impl_index)];
		let member_idx = impl_def
			.bindings
			.get(&BindingKey::ty(declaration.name.inner))
			.copied()?;
		let MemberKind::AssociatedType(provider) =
			impl_def.members[usize::from(member_idx)].kind
		else {
			unreachable!("a type-tier impl member is an associated type")
		};
		Some(ImplAssocTypeIdx(provider))
	}
}

/// How `required_trait` applies to a receiver, per `find_trait_impl`.
pub(super) enum TraitImplLookup {
	/// Concrete receiver, with a registered `impl required_trait for
	/// receiver` (`impls.rs`'s dispatch) — `TraitImplIdx` names it, in
	/// case it overrides the member being looked up.
	Concrete {
		impl_index: TraitImplIdx,
		args: Box<[TypeIndex]>,
	},
	/// Membership supplied by the caller's assumptions, including evidence
	/// on an equivalent subject. No concrete provider was selected; dispatch
	/// remains symbolic until instantiation.
	Abstract,
}

impl SignatureBuilder<'_, '_, '_> {
	/// Resolves `name` (in binding tier `tier` — `Value` for a
	/// function/const, `Type` for an associated type) as a member of
	/// `receiver`. `reference` is the span of whatever named `receiver` in
	/// the first place — threaded through to `ensure_assoc_type_bounds`,
	/// the one path below that can force another item's signature and so
	/// needs a real "why" to attach to a cycle diagnostic.
	pub(super) fn resolve_type_member(
		&mut self,
		cx: AssumptionContext,
		receiver: TypeIndex,
		tier: BindingNamespace,
		name: SymbolU32,
		reference: SourceSpan,
	) -> TypeMemberLookup {
		let key = BindingKey::new(tier, name);
		if matches!(
			self.types.resolve(receiver),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			match self.resolve_bound_member(cx, receiver, key, reference) {
				TypeMemberLookup::NotFound => {}
				found => return found,
			}
		}
		let receiver = match self.normalize_head_query(cx, receiver, reference)
		{
			Ok(receiver) => receiver,
			Err(QueryError::Pending) => return TypeMemberLookup::Pending,
			Err(QueryError::Failed) => return TypeMemberLookup::Error,
		};
		if receiver == TypeIndex::ERROR {
			return TypeMemberLookup::Error;
		}
		match ImplTarget::from_type(self.types.resolve(receiver)) {
			Some(target) => self
				.resolve_concrete_member(cx, receiver, target, key, reference),
			None => self.resolve_bound_member(cx, receiver, key, reference),
		}
	}

	/// Walks `segments` as member lookups off of `current` — a struct
	/// field, associated type, or method, resolved by name rather than
	/// through the namespace graph. Intermediate projections retain their
	/// nested facts. The caller decides whether to normalize the completed type.
	/// Shared by `resolve_type`'s own `Path`
	/// arm (for whatever's left once its namespace-tier prefix is
	/// consumed), its `Grouped` arm (`<T>::Item`, which has no namespace-
	/// tier prefix at all — `current` starts as `T` itself), and its
	/// `QualifiedPath` arm (for whatever's left after the first, trait-
	/// qualified segment).
	pub(super) fn resolve_type_member_path(
		&mut self,
		cx: AssumptionContext,
		file_id: FileId,
		mut current: TypeIndex,
		segments: &[ast::PathSegment],
	) -> TypeIndex {
		if current == TypeIndex::ERROR {
			return current;
		}
		for segment in segments {
			if !segment.type_args.is_empty() {
				todo!(
					"generic args on a type-relative path segment aren't implemented yet"
				)
			}
			match self.resolve_type_member(
				cx,
				current,
				BindingNamespace::Type,
				segment.ident.inner,
				SourceSpan::new(file_id, segment.ident.span),
			) {
				TypeMemberLookup::Pending => {
					let receiver = self.type_formatter().display_type(current);
					let name =
						self.strings.resolve(segment.ident.inner).unwrap();
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::TypeMemberNeedsQualification
									.code(),
							)
							.with_message(format!(
								"selecting associated type `{name}` depends on unfinished bounds"
							))
							.with_label(
								SourceSpan::new(file_id, segment.ident.span)
									.primary_label(),
							)
							.with_note(format!(
								"qualify the declaring trait with `<{receiver} as Trait>::{name}`"
							)),
					);
					return TypeIndex::ERROR;
				}
				TypeMemberLookup::Error => return TypeIndex::ERROR,
				TypeMemberLookup::Found(member) => {
					current = self.project_type_member(current, member);
				}
				TypeMemberLookup::NotFound => {
					self.diagnostics.push(report_no_such_type_member(
						file_id,
						self.strings,
						segment.ident,
					));
					return TypeIndex::ERROR;
				}
				TypeMemberLookup::Ambiguous(candidates) => {
					self.diagnostics.push(report_ambiguous_type_member(
						file_id,
						self.strings,
						self.defs,
						segment.ident,
						&candidates,
					));
					return TypeIndex::ERROR;
				}
			}
		}
		current
	}

	/// Turns a resolved member lookup into the next `current` type in a
	/// path walk — `base` is whatever `member` was looked up on. Shared by
	/// `resolve_type_member_path`'s per-segment loop and `QualifiedPath`'s
	/// one-off first segment, which resolves its member a different way
	/// (`resolve_trait_qualified_member`, not `resolve_type_member`) but
	/// turns the result into a type the same way.
	pub(super) fn project_type_member(
		&mut self,
		base: TypeIndex,
		member: TypeMemberTarget,
	) -> TypeIndex {
		match member.kind {
			MemberKind::AssociatedType(assoc_type_index) => {
				let trait_index = match member.source {
					MemberSource::Bound(trait_index)
					| MemberSource::TraitImpl(trait_index, _)
					| MemberSource::TraitDefault(trait_index, _) => trait_index,
					MemberSource::Inherent(_) => {
						todo!("inherent associated types")
					}
				};
				// Projection identity is independent of the selected provider.
				// Path consumers normalize the constructed projection.
				self.types.intern(Type::AssocTypeProjection {
					trait_index,
					assoc_type_index,
					base,
				})
			}
			// Every caller resolves in `BindingNamespace::Type` — a
			// Function/Method/Constant is Value-tier, so `bindings` (keyed
			// by tier) can never match one here.
			MemberKind::Function(_)
			| MemberKind::Method(_)
			| MemberKind::Constant(_) => unreachable!(
				"a Type-tier lookup cannot resolve to a Value-tier member"
			),
		}
	}

	/// Resolves `<receiver as required_trait>::name` — the first, trait-
	/// qualified segment of a `QualifiedPath`. The rest of a multi-segment
	/// qualified path (`<T as Trait>::Item::Next`) continues through the
	/// ordinary `resolve_type_member_path`, same as `Grouped`/`Path` — only
	/// the first segment is ever qualified, since a qualification pins down
	/// *which* trait provides that one name, and everything after it is
	/// projected off whatever that named.
	pub(super) fn resolve_trait_qualified_member(
		&mut self,
		cx: AssumptionContext,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		tier: BindingNamespace,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<TypeMemberTarget, ()> {
		if receiver == TypeIndex::ERROR {
			return Err(());
		}
		let key = BindingKey::new(tier, name.inner);
		let trait_def = &self.defs.traits[usize::from(required_trait)];
		let Some(&member_index) = trait_def.bindings.get(&key) else {
			self.diagnostics.push(report_not_an_associated_type(
				file_id,
				self.strings,
				name,
				trait_def.name.inner,
			));
			return Err(());
		};
		let declared_kind = trait_def.members[usize::from(member_index)].kind;

		let found = self.find_trait_impl(
			cx,
			receiver,
			required_trait,
			file_id,
			name.span,
		)?;
		Ok(match found {
			TraitImplLookup::Concrete { impl_index, .. } => self
				.defs
				.concrete_trait_member(required_trait, impl_index, key)
				.expect("the requested trait member was found above"),
			TraitImplLookup::Abstract => TypeMemberTarget {
				kind: declared_kind,
				source: MemberSource::Bound(required_trait),
			},
		})
	}

	/// Finds how `required_trait` applies to `receiver`, if at all — a
	/// concrete registered impl, or (for an abstract receiver) membership
	/// in its own implied bounds. Decoupled from looking up any particular
	/// member, so it's exactly as usable wherever else "does `receiver`
	/// have an impl/bound for `required_trait`" needs answering, not only
	/// for `resolve_trait_qualified_member`'s own use. Not a conformance
	/// check: it doesn't care whether that impl/bound actually provides
	/// everything the trait requires, only whether one exists at all —
	/// completeness is `check_trait_conformance`'s own, separate job.
	pub(super) fn find_trait_impl(
		&mut self,
		cx: AssumptionContext,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<TraitImplLookup, ()> {
		let reference = SourceSpan::new(file_id, span);
		match self.find_trait_impl_query(
			cx,
			receiver,
			required_trait,
			reference,
		) {
			Ok(Some(found)) => Ok(found),
			Ok(None) => {
				let diagnostic = self.report_type_does_not_implement_trait(
					file_id,
					span,
					receiver,
					required_trait,
				);
				self.diagnostics.push(diagnostic);
				Err(())
			}
			Err(QueryError::Failed) => Err(()),
			Err(QueryError::Pending) => {
				// A qualified member already has a declaration identity.
				// Membership is checked before the owning query completes.
				self.register_obligation(Obligation::CheckTraitMembership {
					context: cx,
					subject: receiver,
					required: required_trait,
					reference,
				});
				Ok(TraitImplLookup::Abstract)
			}
		}
	}

	pub(super) fn find_trait_impl_query(
		&mut self,
		cx: AssumptionContext,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		reference: SourceSpan,
	) -> QueryResult<Option<TraitImplLookup>> {
		if matches!(self.types.resolve(receiver), Type::Error | Type::Infer) {
			return Err(QueryError::Failed);
		}
		let mut assumed =
			self.check_assumed_trait(cx, receiver, required_trait, reference);
		if assumed == Err(QueryError::Failed) {
			return Err(QueryError::Failed);
		}
		if assumed == Ok(true)
			&& ImplTarget::from_type(self.types.resolve(receiver)).is_none()
		{
			return Ok(Some(TraitImplLookup::Abstract));
		}
		let normalized = self.normalize_head_query(cx, receiver, reference)?;
		if normalized == TypeIndex::ERROR {
			return Err(QueryError::Failed);
		}
		if normalized != receiver {
			match self.check_assumed_trait(
				cx,
				normalized,
				required_trait,
				reference,
			) {
				Ok(true) => assumed = Ok(true),
				Err(QueryError::Failed) => return Err(QueryError::Failed),
				Err(QueryError::Pending) if assumed != Ok(true) => {
					assumed = Err(QueryError::Pending)
				}
				_ => {}
			}
		}
		if let Some(target) =
			ImplTarget::from_type(self.types.resolve(normalized))
		{
			let candidate =
				self.impl_dispatch.trait_candidates(target).iter().find_map(
					|&(trait_index, impl_index)| {
						(trait_index == required_trait).then_some(impl_index)
					},
				);
			if let Some(impl_index) = candidate {
				if let Some(args) = self.match_trait_impl_candidate_query(
					cx, impl_index, normalized, reference,
				)? {
					return Ok(Some(TraitImplLookup::Concrete {
						impl_index,
						args,
					}));
				}
			}
		}
		assumed.map(|proven| proven.then_some(TraitImplLookup::Abstract))
	}

	/// Same code and wording as `check_assoc_type_value`'s own
	/// `report_trait_bound_violation` (mirroring rustc's `E0277` for this
	/// same case: `the trait bound `Foo: Bar` is not satisfied`) — this is
	/// that same condition, just reached with no declared bound clause to
	/// point a "required by a bound in `X`" secondary label at, since a
	/// qualified path's `as Trait` isn't one.
	pub(super) fn report_type_does_not_implement_trait(
		&self,
		file_id: FileId,
		span: TextSpan,
		receiver: TypeIndex,
		required_trait: TraitIdx,
	) -> Diagnostic<FileId> {
		let receiver_name = self.type_formatter().display_type(receiver);
		let trait_name = self
			.strings
			.resolve(self.defs.traits[usize::from(required_trait)].name.inner)
			.unwrap();
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitBoundViolation.code())
			.with_message(format!(
				"the trait bound `{receiver_name}: {trait_name}` is not satisfied"
			))
			.with_label(
				SourceSpan::new(file_id, span).primary_label().with_message(
					format!(
						"the trait `{trait_name}` is not implemented for `{receiver_name}`"
					),
				),
			)
	}

	fn resolve_concrete_member(
		&mut self,
		cx: AssumptionContext,
		receiver: TypeIndex,
		target: ImplTarget,
		key: BindingKey,
		reference: SourceSpan,
	) -> TypeMemberLookup {
		// Only a candidate that declares this name can affect precedence.
		for &index in self.impl_dispatch.inherent_candidates(target) {
			let impl_def = &self.defs.inherent_impls[usize::from(index)];
			let Some(&member_index) = impl_def.bindings.get(&key) else {
				continue;
			};
			let kind = impl_def.members[usize::from(member_index)].kind;
			match self.match_inherent_impl_candidate_query(
				cx, index, receiver, reference,
			) {
				Ok(true) => {
					return TypeMemberLookup::Found(TypeMemberTarget {
						kind,
						source: MemberSource::Inherent(index),
					});
				}
				Ok(false) => {}
				Err(QueryError::Pending) => return TypeMemberLookup::Pending,
				Err(QueryError::Failed) => return TypeMemberLookup::Error,
			}
		}
		let mut traits = Vec::new();
		for &(trait_index, _) in self.impl_dispatch.trait_candidates(target) {
			if self.defs.declared_trait_member(trait_index, key).is_some() {
				traits.push(trait_index);
			}
		}
		let (scoped, readiness) =
			match self.assumed_member_traits(cx, key, reference) {
				Ok(traits) => traits,
				Err(()) => return TypeMemberLookup::Error,
			};
		for trait_index in scoped {
			if !traits.contains(&trait_index) {
				traits.push(trait_index);
			}
		}
		self.resolve_trait_member_candidates(
			cx, receiver, key, reference, traits, readiness,
		)
	}

	/// Discover trait declarations from finite scoped evidence, rather than
	/// scanning every trait in the program. Applicability uses the shared proof.
	fn assumed_member_traits(
		&mut self,
		cx: AssumptionContext,
		key: BindingKey,
		reference: SourceSpan,
	) -> Result<(Vec<TraitIdx>, Readiness), ()> {
		let defs = self.defs;
		let mut traits = Vec::new();
		let mut equalities = Vec::new();
		let mut readiness;
		{
			let (reader, types) = self.assumptions();
			let mut facts = reader.scoped_facts(cx, types);
			readiness = facts.readiness;
			while let Some(fact) = facts.next(types) {
				match fact.kind {
					AssumptionKind::Trait { trait_index, .. }
						if defs.traits[usize::from(trait_index)]
							.bindings
							.contains_key(&key) =>
					{
						if !traits.contains(&trait_index) {
							traits.push(trait_index);
						}
					}
					AssumptionKind::Equality(
						super::bounds::ImpliedBindingKind::Equals(_),
					) => equalities.push(fact.subject),
					_ => {}
				}
			}
		}
		// An equality's projection path can carry associated declaration bounds.
		for subject in equalities {
			self.prepare_effective_bounds(subject, reference)?;
			let depth = self.normalization.remaining_depth();
			let (reader, types) = self.assumptions();
			let mut facts = reader.subject_facts(subject, types, depth);
			readiness = readiness.and(facts.readiness);
			while let Some(fact) = facts.next(types) {
				if let AssumptionKind::Trait { trait_index, .. } = fact.kind {
					if defs.traits[usize::from(trait_index)]
						.bindings
						.contains_key(&key)
						&& !traits.contains(&trait_index)
					{
						traits.push(trait_index);
					}
				}
			}
		}
		if readiness == Readiness::Overflowed {
			self.normalization_overflow(reference);
			return Err(());
		}
		Ok((traits, readiness))
	}

	fn resolve_trait_member_candidates(
		&mut self,
		cx: AssumptionContext,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
		traits: Vec<TraitIdx>,
		mut readiness: Readiness,
	) -> TypeMemberLookup {
		let mut candidates: Option<SmallVec<TypeMemberTarget>> = None;
		for trait_index in traits {
			match self.find_trait_impl_query(
				cx,
				receiver,
				trait_index,
				reference,
			) {
				Ok(Some(TraitImplLookup::Concrete { impl_index, .. })) => {
					if let Some(member) = self.defs.concrete_trait_member(
						trait_index,
						impl_index,
						key,
					) {
						Self::push_candidate(&mut candidates, member);
					}
				}
				Ok(Some(TraitImplLookup::Abstract)) => {
					if let Some(kind) =
						self.defs.declared_trait_member(trait_index, key)
					{
						Self::push_candidate(
							&mut candidates,
							TypeMemberTarget {
								kind,
								source: MemberSource::Bound(trait_index),
							},
						);
					}
				}
				Ok(None) => {}
				Err(QueryError::Pending) => {
					readiness = readiness.and(Readiness::Pending)
				}
				Err(QueryError::Failed) => return TypeMemberLookup::Error,
			}
		}
		// Two known declarations already establish ambiguity. Otherwise pending
		// discovery or applicability could change a unique or absent answer.
		if !matches!(candidates, Some(SmallVec::Many(_)))
			&& readiness == Readiness::Pending
		{
			TypeMemberLookup::Pending
		} else {
			Self::classify(candidates)
		}
	}

	fn resolve_bound_member(
		&mut self,
		cx: AssumptionContext,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> TypeMemberLookup {
		if !matches!(
			self.types.resolve(receiver),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			return TypeMemberLookup::NotFound;
		}
		if self.prepare_effective_bounds(receiver, reference).is_err() {
			return TypeMemberLookup::Error;
		}
		let mut candidates: Option<SmallVec<TypeMemberTarget>> = None;
		let bounds = self.effective_bounds(receiver);
		for trait_index in bounds
			.reflexive_trait
			.into_iter()
			.chain(bounds.map(|view| view.bound.trait_index))
		{
			// The same trait can be supplied by a declaration and a nested
			// receiver constraint; that does not make its member ambiguous.
			if candidates.as_ref().is_some_and(|items| {
				items.into_iter().any(|candidate| {
					matches!(candidate.source, MemberSource::Bound(index) if index == trait_index)
				})
			}) {
				continue;
			}
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			if let Some(&member_index) = trait_def.bindings.get(&key) {
				Self::push_candidate(
					&mut candidates,
					TypeMemberTarget {
						kind: trait_def.members[usize::from(member_index)].kind,
						source: MemberSource::Bound(trait_index),
					},
				);
			}
		}
		// Preserve direct declaration lookup, including known provisional
		// memberships. Equality-based discovery is a fallback when these bounds
		// do not identify the requested name.
		if candidates.is_some() {
			return Self::classify(candidates);
		}
		let (traits, readiness) =
			match self.assumed_member_traits(cx, key, reference) {
				Ok(traits) => traits,
				Err(_) => return TypeMemberLookup::Error,
			};
		self.resolve_trait_member_candidates(
			cx, receiver, key, reference, traits, readiness,
		)
	}

	/// Forces a trait declaration's bounds, never an impl provider's value.
	/// The only failure is a cycle, diagnosed here once — `CycleReported`
	/// means another call already did.
	pub(super) fn ensure_assoc_type_bounds(
		&mut self,
		assoc_type_index: AssocTypeIdx,
		requested_at: SourceSpan,
	) -> Result<(), ()> {
		let def_id =
			self.defs.assoc_types[usize::from(assoc_type_index)].def_id;
		assert!(
			matches!(self.ast_node(def_id), AstNodeRef::TraitAssocType { .. }),
			"bound access requires a trait declaration, not a provider"
		);
		match self.ensure_signature(QueryInfo {
			def_id,
			requested_at: Some(requested_at),
		}) {
			SignatureStatus::Available(SignatureLocation::AssocType(..)) => {
				Ok(())
			}
			SignatureStatus::Available(_) => unreachable!(
				"a trait associated-type declaration has its own signature query"
			),
			SignatureStatus::Cycle => {
				let diagnostic =
					self.report_cyclic_assoc_type_bound(def_id, requested_at);
				self.diagnostics.push(diagnostic);
				Err(())
			}
			SignatureStatus::CycleReported => Err(()),
		}
	}

	fn push_candidate(
		candidates: &mut Option<SmallVec<TypeMemberTarget>>,
		candidate: TypeMemberTarget,
	) {
		match candidates {
			Some(items) => items.push(candidate),
			None => *candidates = Some(SmallVec::new(candidate)),
		}
	}

	fn classify(
		candidates: Option<SmallVec<TypeMemberTarget>>,
	) -> TypeMemberLookup {
		match candidates {
			None => TypeMemberLookup::NotFound,
			Some(SmallVec::One(candidate)) => {
				TypeMemberLookup::Found(candidate)
			}
			Some(SmallVec::Many(candidates)) => {
				TypeMemberLookup::Ambiguous(candidates.into_boxed_slice())
			}
		}
	}
}

fn report_no_such_type_member(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitMember.code())
		.with_message(format!(
			"no associated type named `{name_str}` found for this type"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}

/// `candidates` never holds a `MemberSource::Inherent` entry — inherent
/// always wins outright in `resolve_concrete_member`, before any trait
/// candidate is even gathered, so nothing ever reaches `Ambiguous` through
/// it.
fn report_ambiguous_type_member(
	file_id: FileId,
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	name: Spanned<SymbolU32>,
	candidates: &[TypeMemberTarget],
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	let mut diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousTraitMember.code())
		.with_message(format!(
			"`{name_str}` is ambiguous between multiple traits"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label());
	for candidate in candidates {
		let trait_index = match candidate.source {
			MemberSource::TraitImpl(trait_index, _)
			| MemberSource::TraitDefault(trait_index, _)
			| MemberSource::Bound(trait_index) => trait_index,
			MemberSource::Inherent(_) => continue,
		};
		let trait_name = strings
			.resolve(defs.traits[usize::from(trait_index)].name.inner)
			.unwrap();
		diagnostic =
			diagnostic.with_note(format!("provided by trait `{trait_name}`"));
	}
	diagnostic
}
