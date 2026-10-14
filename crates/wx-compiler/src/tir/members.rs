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

use super::assumptions::AssumptionKind;
use super::assumptions::Readiness;
use super::bounds::report_not_an_associated_type;
use super::defs::{
	AssocTypeIdx, AstNodeRef, BindingKey, DefinitionRegistry, InherentImplIdx,
	MemberKind, Tier, TraitIdx, TraitImplIdx,
};
use super::impls::ImplTarget;
use super::obligations::Obligation;
use super::signatures::{
	QueryInfo, SignatureLocation, SignatureStatus, TypeContext,
};
use super::solver::Unsolved;
use super::types::{Type, TypeEnvIdx, TypeIndex};

/// What type-relative member applicability found.
pub(super) enum MemberLookup {
	/// A dependency has already failed; the caller must not diagnose absence.
	Error,
	/// The solver could not finish (`Unsolved::Overflow` or `Cycle`). Nothing
	/// was reported; the site that wrote the path does that.
	Stuck(Unsolved),
	/// Selecting a member needs facts that are not ready yet.
	Pending,
	NotFound,
	Found(ApplicableMember),
	/// Two or more *unrelated* traits each provide this name for this
	/// receiver — inherent-vs-trait precedence never lands here (inherent
	/// always wins outright, checked before any trait candidate at all), so
	/// this only ever holds trait-sourced candidates.
	Ambiguous(Box<[ApplicableMember]>),
}

impl From<Unsolved> for MemberLookup {
	fn from(error: Unsolved) -> Self {
		match error {
			Unsolved::Pending => Self::Pending,
			Unsolved::Failed => Self::Error,
			fatal @ (Unsolved::Overflow | Unsolved::Cycle(_)) => {
				Self::Stuck(fatal)
			}
		}
	}
}

/// A resolved trait-associated type, ready to form a projection on a base.
#[derive(Clone, Copy)]
pub(super) struct AssocTypeProjectionTarget {
	pub(super) trait_index: TraitIdx,
	pub(super) assoc_type_index: AssocTypeIdx,
}

/// A member found through impl dispatch or trait bounds. Trait candidates
/// retain the declaration; a concrete impl can provide a different definition.
#[derive(Clone, Copy)]
pub(super) enum ApplicableMember {
	Inherent {
		impl_index: InherentImplIdx,
		kind: MemberKind,
	},
	/// The receiver has trait membership through a bound or assumption.
	AbstractTraitMember {
		trait_index: TraitIdx,
		declaration: MemberKind,
	},
	/// A concrete trait impl applies; its member may use the trait declaration.
	TraitImplMember {
		trait_index: TraitIdx,
		impl_index: TraitImplIdx,
		declaration: MemberKind,
	},
}

impl ApplicableMember {
	/// Only a trait-associated type has a projection declaration.
	pub(super) fn assoc_type_declaration(
		self,
	) -> Option<AssocTypeProjectionTarget> {
		match self {
			Self::AbstractTraitMember {
				trait_index,
				declaration: MemberKind::AssociatedType(assoc_type_index),
			}
			| Self::TraitImplMember {
				trait_index,
				declaration: MemberKind::AssociatedType(assoc_type_index),
				..
			} => Some(AssocTypeProjectionTarget {
				trait_index,
				assoc_type_index,
			}),
			_ => None,
		}
	}

	/// Returns the definition used for a value member.
	pub(super) fn selected_kind(self, defs: &DefinitionRegistry) -> MemberKind {
		match self {
			Self::Inherent { kind, .. } => kind,
			Self::TraitImplMember {
				impl_index,
				declaration,
				..
			} => defs.select_trait_member(impl_index, declaration).kind(),
			Self::AbstractTraitMember { declaration, .. } => declaration,
		}
	}
}

/// Which definition supplies a member of a concrete trait impl.
#[derive(Clone, Copy)]
pub(super) enum TraitMemberSelection {
	Impl(MemberKind),
	/// The impl omits this member; the trait declaration may supply a default.
	/// A required declaration may still lack a body or value until conformance.
	TraitDeclaration(MemberKind),
}

impl TraitMemberSelection {
	pub(super) fn kind(self) -> MemberKind {
		match self {
			Self::Impl(kind) | Self::TraitDeclaration(kind) => kind,
		}
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

	fn member_key(&self, declaration: MemberKind) -> BindingKey {
		let name = match declaration {
			MemberKind::Function(index) | MemberKind::Method(index) => {
				self.functions[usize::from(index)].name.inner
			}
			MemberKind::Constant(index) => {
				self.constants[usize::from(index)].name.inner
			}
			MemberKind::AssociatedType(index) => {
				self.assoc_types[usize::from(index)].name.inner
			}
		};
		BindingKey::new(declaration.tier(), name)
	}

	/// Selects an impl member or its trait declaration. The caller must pass a
	/// declaration of the trait implemented by `impl_index`; member lookup and
	/// projection resolution establish that relationship before calling here.
	pub(super) fn select_trait_member(
		&self,
		impl_index: TraitImplIdx,
		declaration: MemberKind,
	) -> TraitMemberSelection {
		let key = self.member_key(declaration);
		let impl_def = &self.trait_impls[usize::from(impl_index)];
		if let Some(index) = impl_def.bindings.get(&key).copied() {
			TraitMemberSelection::Impl(
				impl_def.members[usize::from(index)].kind,
			)
		} else {
			TraitMemberSelection::TraitDeclaration(declaration)
		}
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

impl TypeContext<'_, '_, '_> {
	/// Selects the trait that supplies an associated type named by `key` off
	/// `receiver`, for a written type path. Selection reads declarations only:
	/// a parameter's bounds, the assumptions in scope, and the traits that have
	/// an impl for the receiver's type constructor (`ImplDispatch`). With one
	/// impl per trait per constructor that index names the provider exactly, so
	/// no impl header is read and nothing is matched. Whether the receiver
	/// really implements the selected trait is recorded as a membership check.
	pub(super) fn select_associated_type(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		match self.declared_bound_member(receiver, key, reference) {
			MemberLookup::NotFound => {}
			found => return found,
		}
		// Only assumed equalities may rewrite the receiver here, so a concrete
		// head can come from evidence in scope but never from selecting an impl.
		let receiver = match self
			.normalize_assumed_type_query(assumption_context, receiver)
		{
			Ok(receiver) => receiver,
			Err(error) => return error.into(),
		};
		if receiver == TypeIndex::ERROR {
			return MemberLookup::Error;
		}
		let mut traits = Vec::new();
		if let Some(target) =
			ImplTarget::from_type(self.types.resolve(receiver))
		{
			for &(trait_index, _) in self.impl_dispatch.trait_candidates(target)
			{
				if self.defs.declared_trait_member(trait_index, key).is_some() {
					traits.push(trait_index);
				}
			}
		}
		// Evidence in scope names traits regardless of receiver, so each must
		// be shown to apply by assumptions alone. No impl is consulted.
		let (scoped, mut readiness) = match self.assumed_member_traits(
			assumption_context,
			key,
			reference,
		) {
			Ok(traits) => traits,
			Err(lookup) => return lookup,
		};
		for trait_index in scoped {
			if traits.contains(&trait_index) {
				continue;
			}
			match self.check_assumed_trait(
				assumption_context,
				receiver,
				trait_index,
			) {
				Ok(true) => traits.push(trait_index),
				Ok(false) => {}
				Err(Unsolved::Pending) => {
					readiness = readiness.and(Readiness::Pending)
				}
				Err(error) => return error.into(),
			}
		}
		let mut candidates: Option<SmallVec<ApplicableMember>> = None;
		for trait_index in traits {
			let declaration = self
				.defs
				.declared_trait_member(trait_index, key)
				.expect("candidate traits declare the member");
			Self::push_candidate(
				&mut candidates,
				ApplicableMember::AbstractTraitMember {
					trait_index,
					declaration,
				},
			);
		}
		// Two known declarations already establish ambiguity. Otherwise unfinished
		// discovery could still change a unique or absent answer.
		if !matches!(candidates, Some(SmallVec::Many(_)))
			&& readiness == Readiness::Pending
		{
			MemberLookup::Pending
		} else {
			Self::classify(candidates)
		}
	}

	/// Shared applicability and ambiguity search. Declaration identity and
	/// implementation selection happen after this search completes.
	pub(super) fn resolve_applicable_member(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		if matches!(
			self.types.resolve(receiver),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			match self.resolve_bound_member(
				assumption_context,
				receiver,
				key,
				reference,
			) {
				MemberLookup::NotFound => {}
				found => return found,
			}
		}
		let receiver =
			match self.normalize_head_query(assumption_context, receiver) {
				Ok(receiver) => receiver,
				Err(error) => return error.into(),
			};
		if receiver == TypeIndex::ERROR {
			return MemberLookup::Error;
		}
		match ImplTarget::from_type(self.types.resolve(receiver)) {
			Some(target) => self.resolve_concrete_member(
				assumption_context,
				receiver,
				target,
				key,
				reference,
			),
			None => self.resolve_bound_member(
				assumption_context,
				receiver,
				key,
				reference,
			),
		}
	}

	/// Walks `segments` as member lookups off of `current` — a struct
	/// field, associated type, or method, resolved by name rather than
	/// through the namespace graph. Intermediate projections retain their
	/// nested facts. The caller decides whether to normalize the completed type.
	/// Shared by `resolve_type`'s own `Path`
	/// arm (for whatever's left once its namespace prefix is
	/// consumed), its `Grouped` arm (`<T>::Item`, which has no namespace
	/// prefix at all — `current` starts as `T` itself), and its
	/// `QualifiedPath` arm (for whatever's left after the first, trait-
	/// qualified segment).
	pub(super) fn resolve_type_member_path(
		&mut self,
		assumption_context: TypeEnvIdx,
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
			let key = BindingKey::ty(segment.ident.inner);
			match self.select_associated_type(
				assumption_context,
				current,
				key,
				SourceSpan::new(file_id, segment.ident.span),
			) {
				MemberLookup::Pending => {
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
				MemberLookup::Error => return TypeIndex::ERROR,
				MemberLookup::Stuck(unsolved) => {
					let _ = self.report_unsolved::<()>(
						Err(unsolved),
						SourceSpan::new(file_id, segment.ident.span),
					);
					return TypeIndex::ERROR;
				}
				MemberLookup::Found(member) => {
					let Some(declaration) = member.assoc_type_declaration()
					else {
						self.diagnostics.push(report_no_such_type_member(
							file_id,
							self.strings,
							segment.ident,
						));
						return TypeIndex::ERROR;
					};
					// Selection named the trait without matching an impl; that
					// the receiver implements it is the check pass's question.
					self.register_obligation(
						Obligation::CheckTraitMembership {
							assumption_context,
							subject: current,
							required: declaration.trait_index,
							reference: SourceSpan::new(
								file_id,
								segment.ident.span,
							),
						},
					);
					current = self.project_assoc_type(current, declaration);
				}
				MemberLookup::NotFound => {
					if matches!(
						self.types.resolve(current),
						Type::AssocTypeProjection { .. }
					) {
						// A projection's declared bounds are only half of what
						// it can have: its value may be a type that does. That
						// takes impls, so the check pass decides what to say.
						self.register_obligation(
							Obligation::CheckProjectionMember {
								assumption_context,
								projection: current,
								name: segment.ident.inner,
								reference: SourceSpan::new(
									file_id,
									segment.ident.span,
								),
							},
						);
					} else {
						self.diagnostics.push(report_no_such_type_member(
							file_id,
							self.strings,
							segment.ident,
						));
					}
					return TypeIndex::ERROR;
				}
				MemberLookup::Ambiguous(candidates) => {
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

	/// Build a symbolic projection. Ordinary signature types normalize it;
	/// bound expressions retain it until their assumptions are available.
	pub(super) fn project_assoc_type(
		&mut self,
		base: TypeIndex,
		member: AssocTypeProjectionTarget,
	) -> TypeIndex {
		self.types.intern(Type::AssocTypeProjection {
			trait_index: member.trait_index,
			assoc_type_index: member.assoc_type_index,
			base,
		})
	}

	/// Resolve the trait declaration named by the first segment of a
	/// qualified type path. Later segments use ordinary type-member lookup.
	pub(super) fn resolve_trait_qualified_assoc_type(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<AssocTypeProjectionTarget, ()> {
		if receiver == TypeIndex::ERROR {
			return Err(());
		}
		let kind = self.resolve_trait_member_declaration(
			required_trait,
			BindingKey::ty(name.inner),
			name,
			file_id,
		)?;
		let MemberKind::AssociatedType(assoc_type_index) = kind else {
			self.diagnostics.push(report_not_an_associated_type(
				file_id,
				self.strings,
				name,
				self.defs.traits[usize::from(required_trait)].name.inner,
			));
			return Err(());
		};
		// Naming the projection does not need an impl; whether `receiver`
		// implements the trait is the check pass's question.
		self.register_obligation(Obligation::CheckTraitMembership {
			assumption_context,
			subject: receiver,
			required: required_trait,
			reference: SourceSpan::new(file_id, name.span),
		});
		Ok(AssocTypeProjectionTarget {
			trait_index: required_trait,
			assoc_type_index,
		})
	}

	pub(super) fn resolve_trait_qualified_value(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<ApplicableMember, ()> {
		let key = BindingKey::value(name.inner);
		if receiver == TypeIndex::ERROR {
			return Err(());
		}
		let declaration = self.resolve_trait_member_declaration(
			required_trait,
			key,
			name,
			file_id,
		)?;
		let found = self.find_trait_impl(
			assumption_context,
			receiver,
			required_trait,
			file_id,
			name.span,
		)?;
		let member = match found {
			TraitImplLookup::Concrete { impl_index, .. } => {
				ApplicableMember::TraitImplMember {
					trait_index: required_trait,
					impl_index,
					declaration,
				}
			}
			TraitImplLookup::Abstract => {
				ApplicableMember::AbstractTraitMember {
					trait_index: required_trait,
					declaration,
				}
			}
		};
		Ok(member)
	}

	/// The trait's own declaration of `key`, with no impl involved. A missing
	/// member is a written-site error reported here.
	fn resolve_trait_member_declaration(
		&mut self,
		required_trait: TraitIdx,
		key: BindingKey,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<MemberKind, ()> {
		let trait_def = &self.defs.traits[usize::from(required_trait)];
		let Some(&member_index) = trait_def.bindings.get(&key) else {
			self.diagnostics.push(report_missing_trait_member(
				file_id,
				self.strings,
				name,
				trait_def.name.inner,
				key.tier,
			));
			return Err(());
		};
		Ok(trait_def.members[usize::from(member_index)].kind)
	}

	/// Finds how `required_trait` applies to `receiver`, if at all — a
	/// concrete registered impl, or (for an abstract receiver) membership
	/// in its own implied bounds. Decoupled from looking up any particular
	/// member, so it's exactly as usable wherever else "does `receiver`
	/// have an impl/bound for `required_trait`" needs answering, not only
	/// for qualified member resolution. Not a conformance
	/// check: it doesn't care whether that impl/bound actually provides
	/// everything the trait requires, only whether one exists at all —
	/// completeness is `check_trait_conformance`'s own, separate job.
	pub(super) fn find_trait_impl(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<TraitImplLookup, ()> {
		let reference = SourceSpan::new(file_id, span);
		match self.find_trait_impl_query(
			assumption_context,
			receiver,
			required_trait,
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
			Err(Unsolved::Failed) => Err(()),
			Err(fatal @ (Unsolved::Overflow | Unsolved::Cycle(_))) => {
				let _ = self.report_unsolved::<()>(Err(fatal), reference);
				Err(())
			}
			Err(Unsolved::Pending) => {
				// A qualified member already has a declaration identity.
				// Membership is checked before the owning query completes.
				self.register_obligation(Obligation::CheckTraitMembership {
					assumption_context,
					subject: receiver,
					required: required_trait,
					reference,
				});
				Ok(TraitImplLookup::Abstract)
			}
		}
	}

	/// Same code and wording as `report_trait_bound_violation`,
	/// reported for a recorded bounds check (mirroring rustc's `E0277` for this
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
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		target: ImplTarget,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		// Only a candidate that declares this name can affect precedence.
		for &index in self.impl_dispatch.inherent_candidates(target) {
			let impl_def = &self.defs.inherent_impls[usize::from(index)];
			let Some(&member_index) = impl_def.bindings.get(&key) else {
				continue;
			};
			let kind = impl_def.members[usize::from(member_index)].kind;
			match self.match_inherent_impl_candidate_query(
				assumption_context,
				index,
				receiver,
			) {
				Ok(true) => {
					return MemberLookup::Found(ApplicableMember::Inherent {
						kind,
						impl_index: index,
					});
				}
				Ok(false) => {}
				Err(error) => return error.into(),
			}
		}
		let mut traits = Vec::new();
		for &(trait_index, _) in self.impl_dispatch.trait_candidates(target) {
			if self.defs.declared_trait_member(trait_index, key).is_some() {
				traits.push(trait_index);
			}
		}
		let (scoped, readiness) = match self.assumed_member_traits(
			assumption_context,
			key,
			reference,
		) {
			Ok(traits) => traits,
			Err(lookup) => return lookup,
		};
		for trait_index in scoped {
			if !traits.contains(&trait_index) {
				traits.push(trait_index);
			}
		}
		self.resolve_trait_member_candidates(
			assumption_context,
			receiver,
			key,
			traits,
			readiness,
		)
	}

	/// Discover trait declarations from finite scoped evidence, rather than
	/// scanning every trait in the program. Applicability uses the shared proof.
	fn assumed_member_traits(
		&mut self,
		assumption_context: TypeEnvIdx,
		key: BindingKey,
		reference: SourceSpan,
	) -> Result<(Vec<TraitIdx>, Readiness), MemberLookup> {
		let defs = self.defs;
		let mut traits = Vec::new();
		let mut equalities = Vec::new();
		let mut readiness;
		{
			let (reader, types) = self.assumptions();
			let mut facts = reader.scoped_facts(assumption_context, types);
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
			self.prepare_effective_bounds(subject, reference)
				.map_err(|()| MemberLookup::Error)?;
			let depth = self.solver.remaining_depth();
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
			return Err(MemberLookup::Stuck(Unsolved::Overflow));
		}
		Ok((traits, readiness))
	}

	fn resolve_trait_member_candidates(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		traits: Vec<TraitIdx>,
		mut readiness: Readiness,
	) -> MemberLookup {
		let mut candidates: Option<SmallVec<ApplicableMember>> = None;
		for trait_index in traits {
			let Some(declaration) =
				self.defs.declared_trait_member(trait_index, key)
			else {
				continue;
			};
			match self.find_trait_impl_query(
				assumption_context,
				receiver,
				trait_index,
			) {
				Ok(Some(TraitImplLookup::Concrete { impl_index, .. })) => {
					Self::push_candidate(
						&mut candidates,
						ApplicableMember::TraitImplMember {
							trait_index,
							impl_index,
							declaration,
						},
					);
				}
				Ok(Some(TraitImplLookup::Abstract)) => {
					Self::push_candidate(
						&mut candidates,
						ApplicableMember::AbstractTraitMember {
							trait_index,
							declaration,
						},
					);
				}
				Ok(None) => {}
				Err(Unsolved::Pending) => {
					readiness = readiness.and(Readiness::Pending)
				}
				Err(error) => return error.into(),
			}
		}
		// Two known declarations already establish ambiguity. Otherwise pending
		// discovery or applicability could change a unique or absent answer.
		if !matches!(candidates, Some(SmallVec::Many(_)))
			&& readiness == Readiness::Pending
		{
			MemberLookup::Pending
		} else {
			Self::classify(candidates)
		}
	}

	/// Traits supplied by the receiver's own declared bounds, by name only.
	pub(super) fn declared_bound_member(
		&mut self,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		if !matches!(
			self.types.resolve(receiver),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			return MemberLookup::NotFound;
		}
		if self.prepare_effective_bounds(receiver, reference).is_err() {
			return MemberLookup::Error;
		}
		let mut candidates: Option<SmallVec<ApplicableMember>> = None;
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
					matches!(candidate, ApplicableMember::AbstractTraitMember { trait_index: index, .. } if index == trait_index)
				})
			}) {
				continue;
			}
			if let Some(declaration) =
				self.defs.declared_trait_member(trait_index, key)
			{
				Self::push_candidate(
					&mut candidates,
					ApplicableMember::AbstractTraitMember {
						trait_index,
						declaration,
					},
				);
			}
		}
		Self::classify(candidates)
	}

	fn resolve_bound_member(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		// Preserve direct declaration lookup, including known provisional
		// memberships. Equality-based discovery is a fallback when these bounds
		// do not identify the requested name.
		match self.declared_bound_member(receiver, key, reference) {
			MemberLookup::NotFound => {}
			found => return found,
		}
		let (traits, readiness) = match self.assumed_member_traits(
			assumption_context,
			key,
			reference,
		) {
			Ok(traits) => traits,
			Err(lookup) => return lookup,
		};
		self.resolve_trait_member_candidates(
			assumption_context,
			receiver,
			key,
			traits,
			readiness,
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
		candidates: &mut Option<SmallVec<ApplicableMember>>,
		candidate: ApplicableMember,
	) {
		match candidates {
			Some(items) => items.push(candidate),
			None => *candidates = Some(SmallVec::new(candidate)),
		}
	}

	fn classify(
		candidates: Option<SmallVec<ApplicableMember>>,
	) -> MemberLookup {
		match candidates {
			None => MemberLookup::NotFound,
			Some(SmallVec::One(candidate)) => MemberLookup::Found(candidate),
			Some(SmallVec::Many(candidates)) => {
				MemberLookup::Ambiguous(candidates.into_boxed_slice())
			}
		}
	}
}

fn report_missing_trait_member(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	trait_name: SymbolU32,
	tier: Tier,
) -> Diagnostic<FileId> {
	match tier {
		Tier::Type => {
			report_not_an_associated_type(file_id, strings, name, trait_name)
		}
		Tier::Value => {
			let name_str = strings.resolve(name.inner).unwrap();
			let trait_str = strings.resolve(trait_name).unwrap();
			Diagnostic::error()
				.with_code(DiagnosticCode::NotATraitMember.code())
				.with_message(format!(
					"`{name_str}` is not a value member of trait `{trait_str}`"
				))
				.with_label(SourceSpan::new(file_id, name.span).primary_label())
		}
	}
}

pub(super) fn report_no_such_type_member(
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

/// Inherent members win before trait candidates are gathered, so ambiguous
/// associated-type candidates always have trait declaration identities.
fn report_ambiguous_type_member(
	file_id: FileId,
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	name: Spanned<SymbolU32>,
	candidates: &[ApplicableMember],
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	let mut diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousTraitMember.code())
		.with_message(format!(
			"`{name_str}` is ambiguous between multiple traits"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label());
	for candidate in candidates {
		let trait_index = match candidate {
			ApplicableMember::AbstractTraitMember { trait_index, .. }
			| ApplicableMember::TraitImplMember { trait_index, .. } => trait_index,
			ApplicableMember::Inherent { .. } => {
				unreachable!("inherent members cannot be ambiguous")
			}
		};
		let trait_name = strings
			.resolve(defs.traits[usize::from(*trait_index)].name.inner)
			.unwrap();
		diagnostic =
			diagnostic.with_note(format!("provided by trait `{trait_name}`"));
	}
	diagnostic
}
