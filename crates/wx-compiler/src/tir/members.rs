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
use super::assumptions::EffectiveBounds;
use super::assumptions::Readiness;
use super::bounds::report_not_an_associated_type;
use super::defs::{
	AssocTypeIdx, AstNodeRef, BindingKey, DefId, DefinitionRegistry,
	InherentImplIdx, MemberKind, Scope, Tier, TraitIdx, TraitImplIdx,
};
use super::format::TypeFormatter;
use super::impls::ImplTarget;
use super::obligations::{BoundRequirements, Obligation};
use super::resolutions::Referent;
use super::signatures::{
	InferPolicy, QueryInfo, SignatureLocation, SignatureStatus, TypeContext,
};
use super::solver::{Assumption, SolverError};
use super::types::{Type, TypeEnvIdx, TypeEnvOwner, TypeIndex};

/// What type-relative member applicability found.
pub(super) enum MemberLookup {
	/// A dependency has already failed; the caller must not diagnose absence.
	Error,
	/// The solver could not finish (`SolverError::Overflow` or `Cycle`). Nothing
	/// was reported; the site that wrote the path does that.
	Stuck(SolverError),
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

impl From<SolverError> for MemberLookup {
	fn from(error: SolverError) -> Self {
		match error {
			SolverError::Pending => Self::Pending,
			SolverError::Poisoned => Self::Error,
			fatal @ (SolverError::Overflow | SolverError::Cycle(_)) => {
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
		let mut readiness = Readiness::Ready;
		if let Some(target) =
			ImplTarget::from_type(self.types.resolve(receiver))
		{
			// A type an impl can target takes its traits from impls only,
			// never from assumptions (`Solver::find_trait_impl_query`).
			for &(trait_index, _) in self.impl_dispatch.trait_candidates(target)
			{
				if self.defs.declared_trait_member(trait_index, key).is_some() {
					traits.push(trait_index);
				}
			}
		} else {
			// Evidence in scope names traits regardless of receiver, so each
			// must be shown to apply by assumptions alone. No impl is consulted.
			let scoped;
			(scoped, readiness) =
				match self.assumed_member_traits(assumption_context, key) {
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
					Ok(Assumption::Holds) => traits.push(trait_index),
					Ok(Assumption::Unproven) => {}
					Ok(Assumption::Pending) => {
						readiness = readiness.and(Readiness::Pending)
					}
					Err(error) => return error.into(),
				}
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
		namespace: Scope,
		mut current: TypeIndex,
		segments: &[ast::PathSegment],
		infer_policy: InferPolicy,
	) -> TypeIndex {
		if current == TypeIndex::ERROR {
			return current;
		}
		for segment in segments {
			// An inherent function comes first, as in value lookup.
			if let Some(function) = self.select_inherent_function(
				assumption_context,
				file_id,
				namespace,
				current,
				segment,
				infer_policy,
			) {
				current = function;
				continue;
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
				MemberLookup::Stuck(error) => {
					let _ = self.report_solver_error::<()>(
						Err(error),
						SourceSpan::new(file_id, segment.ident.span),
					);
					return TypeIndex::ERROR;
				}
				MemberLookup::Found(member) => {
					let ApplicableMember::AbstractTraitMember {
						trait_index,
						declaration,
					} = member
					else {
						unreachable!(
							"type-position selection reads trait declarations only"
						)
					};
					// Selection named the trait without matching an impl; that
					// the receiver implements it is the declaration check's question.
					self.register_obligation(
						Obligation::CheckTraitMembership {
							assumption_context,
							subject: current,
							required: trait_index,
							reference: SourceSpan::new(
								file_id,
								segment.ident.span,
							),
						},
					);
					self.resolutions.by_site.insert(
						(
							SourceSpan::new(file_id, segment.ident.span),
							Tier::Type,
						),
						Referent::Member(declaration),
					);
					current = match declaration {
						MemberKind::AssociatedType(assoc_type_index) => {
							if !segment.type_args.is_empty() {
								self.report_assoc_type_args(
									file_id,
									namespace,
									assumption_context,
									segment,
									assoc_type_index,
									infer_policy,
								);
								return TypeIndex::ERROR;
							}
							self.project_assoc_type(
								current,
								AssocTypeProjectionTarget {
									trait_index,
									assoc_type_index,
								},
							)
						}
						// `<current as Trait>::f`, which normalization takes to
						// the impl's member once `current` has an impl.
						MemberKind::Function(function)
						| MemberKind::Method(function) => {
							let own_args = self.member_function_type_args(
								assumption_context,
								file_id,
								namespace,
								function,
								&[current],
								segment,
								infer_policy,
							);
							let mut type_args = vec![current];
							type_args.extend_from_slice(&own_args);
							self.types.intern_function(function, &type_args)
						}
						MemberKind::Constant(_) => {
							unreachable!("a constant is a value member")
						}
					};
				}
				MemberLookup::NotFound => {
					if matches!(
						self.types.resolve(current),
						Type::AssocTypeProjection { .. }
					) {
						// A projection's declared bounds are only half of what
						// it can have: its value may be a type that does. That
						// takes impls, so the declaration check decides what to say.
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

	/// The inherent function `segment` names off a concrete `receiver`: the
	/// impl whose target matches it supplies the leading arguments, and its
	/// bounds on them are recorded as checks. `None` leaves the name to the
	/// trait members.
	fn select_inherent_function(
		&mut self,
		assumption_context: TypeEnvIdx,
		file_id: FileId,
		namespace: Scope,
		receiver: TypeIndex,
		segment: &ast::PathSegment,
		infer_policy: InferPolicy,
	) -> Option<TypeIndex> {
		let key = BindingKey::ty(segment.ident.inner);
		let reference = SourceSpan::new(file_id, segment.ident.span);
		// Only assumed equalities may rewrite the receiver here, as for an
		// associated type; a failure is the trait selection's to report.
		let receiver = self
			.normalize_assumed_type_query(assumption_context, receiver)
			.ok()?;
		let target = ImplTarget::from_type(self.types.resolve(receiver))?;
		let impl_dispatch = self.impl_dispatch;
		for &impl_index in impl_dispatch.inherent_candidates(target) {
			let impl_def = &self.defs.inherent_impls[usize::from(impl_index)];
			let Some(&member_index) = impl_def.bindings.get(&key) else {
				continue;
			};
			let kind = impl_def.members[usize::from(member_index)].kind;
			let (MemberKind::Function(function) | MemberKind::Method(function)) =
				kind
			else {
				continue;
			};
			let _ = self.ensure_signature(QueryInfo {
				def_id: DefId::InherentImpl(impl_index),
				requested_at: Some(reference),
			});
			let Some(header) = &self.inherent_impls[usize::from(impl_index)]
			else {
				continue;
			};
			let env = header.type_params;
			let Some(impl_args) = self.types.match_impl_target(
				header.target.inner,
				receiver,
				&self.type_envs,
				env,
			) else {
				continue;
			};
			let mut type_args = Vec::with_capacity(impl_args.len());
			let arguments = self.types.push_list(&impl_args);
			for (index, &argument) in impl_args.iter().enumerate() {
				type_args.push(self.record_bounds_check(
					assumption_context,
					BoundRequirements::Parameter {
						env,
						index,
						arguments,
					},
					Spanned {
						inner: argument,
						span: segment.ident.span,
					},
					reference,
					TypeEnvOwner::InherentImpl(impl_index),
				));
			}
			self.resolutions
				.by_site
				.insert((reference, Tier::Type), Referent::Member(kind));
			let own_args = self.member_function_type_args(
				assumption_context,
				file_id,
				namespace,
				function,
				&type_args,
				segment,
				infer_policy,
			);
			type_args.extend_from_slice(&own_args);
			return Some(self.types.intern_function(function, &type_args));
		}
		None
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
	/// qualified type path: an associated type or a function. Later segments
	/// use ordinary type-member lookup.
	pub(super) fn resolve_trait_qualified_type_member(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<MemberKind, ()> {
		if receiver == TypeIndex::ERROR {
			return Err(());
		}
		let kind = self.resolve_trait_member_declaration(
			required_trait,
			BindingKey::ty(name.inner),
			name,
			file_id,
		)?;
		self.resolutions.by_site.insert(
			(SourceSpan::new(file_id, name.span), Tier::Type),
			Referent::Member(kind),
		);
		// Naming the member does not need an impl; whether `receiver`
		// implements the trait is the declaration check's question.
		self.register_obligation(Obligation::CheckTraitMembership {
			assumption_context,
			subject: receiver,
			required: required_trait,
			reference: SourceSpan::new(file_id, name.span),
		});
		Ok(kind)
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
		self.resolutions.by_site.insert(
			(SourceSpan::new(file_id, name.span), Tier::Value),
			Referent::Member(member.selected_kind(self.defs)),
		);
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
				let diagnostic = report_type_does_not_implement_trait(
					&self.type_formatter(),
					file_id,
					span,
					receiver,
					required_trait,
				);
				self.diagnostics.push(diagnostic);
				Err(())
			}
			Err(SolverError::Poisoned) => Err(()),
			Err(fatal @ (SolverError::Overflow | SolverError::Cycle(_))) => {
				let _ = self.report_solver_error::<()>(Err(fatal), reference);
				Err(())
			}
			Err(SolverError::Pending) => {
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

	fn resolve_concrete_member(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		target: ImplTarget,
		key: BindingKey,
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
		// Only impls give a concrete receiver a trait, so no assumption in
		// scope can add a candidate (`Solver::find_trait_impl_query`).
		let mut traits = Vec::new();
		for &(trait_index, _) in self.impl_dispatch.trait_candidates(target) {
			if self.defs.declared_trait_member(trait_index, key).is_some() {
				traits.push(trait_index);
			}
		}
		self.resolve_trait_member_candidates(
			assumption_context,
			receiver,
			key,
			traits,
			Readiness::Ready,
		)
	}

	/// Discover trait declarations from finite scoped evidence, rather than
	/// scanning every trait in the program. Applicability uses the shared proof.
	fn assumed_member_traits(
		&mut self,
		assumption_context: TypeEnvIdx,
		key: BindingKey,
	) -> Result<(Vec<TraitIdx>, Readiness), MemberLookup> {
		let defs = self.defs;
		let mut traits = Vec::new();
		let (reader, types) = self.assumptions();
		let mut facts = reader.scoped_facts(assumption_context);
		let readiness = facts.readiness;
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
		if readiness == Readiness::Overflowed {
			return Err(MemberLookup::Stuck(SolverError::Overflow));
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
				Err(SolverError::Pending) => {
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
		Self::select_declared_member(
			self.defs,
			self.effective_bounds(receiver),
			key,
		)
	}

	/// The members named `key` among the traits `bounds` supply.
	pub(super) fn select_declared_member(
		defs: &DefinitionRegistry,
		bounds: EffectiveBounds<'_>,
		key: BindingKey,
	) -> MemberLookup {
		let mut candidates: Option<SmallVec<ApplicableMember>> = None;
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
				defs.declared_trait_member(trait_index, key)
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
		let (traits, readiness) =
			match self.assumed_member_traits(assumption_context, key) {
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
		let def_id = DefId::AssocType(assoc_type_index);
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

/// Same code and wording as `report_trait_bound_violation`,
/// reported for a recorded bounds check (mirroring rustc's `E0277` for this
/// same case: `the trait bound `Foo: Bar` is not satisfied`) — this is
/// that same condition, just reached with no declared bound clause to
/// point a "required by a bound in `X`" secondary label at, since a
/// qualified path's `as Trait` isn't one.
pub(super) fn report_type_does_not_implement_trait(
	formatter: &TypeFormatter<'_>,
	file_id: FileId,
	span: TextSpan,
	receiver: TypeIndex,
	required_trait: TraitIdx,
) -> Diagnostic<FileId> {
	let receiver_name = formatter.display_type(receiver);
	let trait_name = formatter
		.strings
		.resolve(
			formatter.defs.traits[usize::from(required_trait)]
				.name
				.inner,
		)
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
