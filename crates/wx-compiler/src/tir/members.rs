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

use super::bounds::{AssumptionEnvIdx, Readiness, report_not_a_binding_member};
use super::decls::{
	AssocTypeIdx, AstNodeRef, BindingKey, ConstIdx, Declarations, FunctionIdx,
	InherentImplIdx, MemberKind, MemberOwner, SignatureQuery, Tier, TraitIdx,
	TraitImplIdx,
};
use super::format::TypeFormatter;
use super::impls::ImplTarget;
use super::obligations::{BoundRequirements, TypeObligation};
use super::resolutions::{Reference, Site};
use super::signatures::{
	InferPolicy, LexicalScope, QueryInfo, Semantics, SemanticsBuilder,
	SignatureLocation, SignatureStatus,
};
use super::solver::{
	Assumption, NormalizationDepth, RewriteFlags, SolverError,
};
use super::types::{
	GenericEnvIdx, GenericEnvOwner, Type, TypeIndex, TypeInterner,
};

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

/// A resolved trait constant, the declaration a representability clause reads
/// over its subject (`<T as Array>::LEN`).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub(super) struct ConstantTarget {
	pub(super) trait_index: TraitIdx,
	pub(super) constant: ConstIdx,
}

/// A resolved trait-associated type, ready to form a projection on a base.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) struct TypeProjectionTarget {
	pub(super) trait_index: TraitIdx,
	pub(super) assoc_type_index: AssocTypeIdx,
}

impl TypeProjectionTarget {
	pub(super) fn project(
		self,
		types: &mut TypeInterner,
		base: TypeIndex,
	) -> TypeIndex {
		types.intern(Type::TypeProjection {
			trait_index: self.trait_index,
			assoc_type_index: self.assoc_type_index,
			base,
		})
	}
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
	/// The trait constant a representability clause can read, for a constant's
	/// member.
	pub(super) fn constant_declaration(self) -> Option<ConstantTarget> {
		match self {
			Self::AbstractTraitMember {
				trait_index,
				declaration: MemberKind::Constant(constant),
			}
			| Self::TraitImplMember {
				trait_index,
				declaration: MemberKind::Constant(constant),
				..
			} => Some(ConstantTarget {
				trait_index,
				constant,
			}),
			_ => None,
		}
	}

	/// Only a trait-associated type has a projection declaration.
	pub(super) fn type_declaration(self) -> Option<TypeProjectionTarget> {
		match self {
			Self::AbstractTraitMember {
				trait_index,
				declaration: MemberKind::AssociatedType(assoc_type_index),
			}
			| Self::TraitImplMember {
				trait_index,
				declaration: MemberKind::AssociatedType(assoc_type_index),
				..
			} => Some(TypeProjectionTarget {
				trait_index,
				assoc_type_index,
			}),
			_ => None,
		}
	}

	/// Returns the definition used for a value member.
	pub(super) fn selected_kind(self, decls: &Declarations) -> MemberKind {
		match self {
			Self::Inherent { kind, .. } => kind,
			Self::TraitImplMember {
				impl_index,
				declaration,
				..
			} => decls.select_trait_member(impl_index, declaration).kind(),
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

impl Declarations {
	pub(super) fn declared_trait_member(
		&self,
		trait_index: TraitIdx,
		key: BindingKey,
	) -> Option<MemberKind> {
		let definition = &self.traits[usize::from(trait_index)];
		definition.bindings.get(&key).copied().map(|member_index| {
			definition.members[usize::from(member_index)].kind
		})
	}

	fn member_key(&self, declaration: MemberKind) -> BindingKey {
		let name = match declaration {
			MemberKind::Function(index) | MemberKind::Method(index) => {
				self.name(index).inner
			}
			MemberKind::Constant(index) => self.name(index).inner,
			MemberKind::AssociatedType(index) => self.name(index).inner,
		};
		BindingKey::new(declaration.tier(), name)
	}

	/// Selects an impl member or its trait declaration. The caller must pass a
	/// declaration of the trait implemented by `impl_index`; member lookup and
	/// projection resolution establish that relationship before calling here.
	/// Only a member of the declaration's kind provides it: one of another
	/// kind under its name is conformance's to report, and the declaration
	/// is selected as if the impl had omitted it.
	pub(super) fn select_trait_member(
		&self,
		impl_index: TraitImplIdx,
		declaration: MemberKind,
	) -> TraitMemberSelection {
		let key = self.member_key(declaration);
		let impl_decl = &self.trait_impls[usize::from(impl_index)];
		match impl_decl.bindings.get(&key) {
			Some(&index)
				if impl_decl.members[usize::from(index)]
					.kind
					.same_kind(declaration) =>
			{
				TraitMemberSelection::Impl(
					impl_decl.members[usize::from(index)].kind,
				)
			}
			_ => TraitMemberSelection::TraitDeclaration(declaration),
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
	/// A trait the compiler answers from the receiver's structure: `StackValue`,
	/// and `Call` for a function reference, whose `Args` and `Result` are its
	/// parameter and result types. No impl provides it.
	Builtin,
}

/// What a call of a function with concrete arguments runs, per
/// `resolve_function`.
pub(super) enum ResolvedFunction {
	/// `function` with `args`, flat: the function itself; the member of the
	/// impl a trait declaration's `Self` selects, with the impl's arguments
	/// and then the call's own; or the trait's default the impl inherits,
	/// with `[Self, own...]`.
	Instance {
		function: FunctionIdx,
		args: Box<[TypeIndex]>,
	},
	/// `Call::call` of a function item: the item's function with its own
	/// arguments, called with the `Args` value as its parameters.
	Item {
		function: FunctionIdx,
		args: Box<[TypeIndex]>,
	},
	/// A function the compiler supplies for `Self` (`Call` of a function
	/// reference, a slice's or an array's `len` and `as_ref`;
	/// `IntrinsicDefs::supplies`). No function provides it.
	Builtin,
	/// A trait's declaration whose `Self` is not known here.
	Abstract,
}

impl Semantics {
	/// What `function` with `args` runs, as `resolve_constant` is for a
	/// constant: itself, or, for a trait's declaration (`args` is `[Self,
	/// own...]`), what the impl its `Self` selects provides.
	pub(super) fn resolve_function(
		&mut self,
		strings: &StringInterner,
		function: FunctionIdx,
		args: &[TypeIndex],
	) -> Result<ResolvedFunction, SolverError> {
		let MemberOwner::Trait(trait_index) =
			self.decls.functions[usize::from(function)].owner
		else {
			return Ok(ResolvedFunction::Instance {
				function,
				args: args.into(),
			});
		};
		let receiver = args[0];
		if self.types.has_param(receiver) {
			return Ok(ResolvedFunction::Abstract);
		}
		Ok(
			match self.find_trait_impl_query(
				strings,
				AssumptionEnvIdx::ROOT,
				receiver,
				trait_index,
			)? {
				Some(TraitImplLookup::Concrete {
					impl_index,
					args: impl_args,
				}) => {
					// A function item's `impl Call` is the compiler's: it
					// declares `Args` and `Result`, and the call runs the item.
					if let Type::Function {
						func_index: item,
						type_args,
					} = *self.types.resolve(receiver)
						&& Some(trait_index) == self.decls.intrinsics.call
					{
						return Ok(ResolvedFunction::Item {
							function: item,
							args: self.types.list(type_args).into(),
						});
					}
					match self.decls.select_trait_member(
						impl_index,
						MemberKind::Method(function),
					) {
						TraitMemberSelection::Impl(
							MemberKind::Function(own) | MemberKind::Method(own),
						) => ResolvedFunction::Instance {
							function: own,
							args: impl_args
								.iter()
								.chain(&args[1..])
								.copied()
								.collect(),
						},
						_ => ResolvedFunction::Instance {
							function,
							args: args.into(),
						},
					}
				}
				// What the compiler supplies has no function; a default is
				// instantiated with the structural `Self`, as an impl that
				// inherits it would.
				Some(TraitImplLookup::Builtin)
					if self
						.decls
						.intrinsics
						.supplies(trait_index, function) =>
				{
					ResolvedFunction::Builtin
				}
				Some(TraitImplLookup::Builtin) => ResolvedFunction::Instance {
					function,
					args: args.into(),
				},
				Some(TraitImplLookup::Abstract) => ResolvedFunction::Abstract,
				// The unmet bound was reported where the function is named.
				None => return Err(SolverError::Poisoned),
			},
		)
	}

	/// The traits some type of `target`'s may have: those its impls
	/// implement, and those the compiler implements for typed function
	/// references, slices and arrays.
	pub(super) fn trait_candidates(
		&self,
		target: ImplTarget,
	) -> impl Iterator<Item = TraitIdx> + use<'_> {
		let intrinsics = &self.decls.intrinsics;
		let callable =
			(target == ImplTarget::TypedFuncref).then_some(intrinsics.call);
		let sequence = matches!(target, ImplTarget::Slice | ImplTarget::Array)
			.then_some([intrinsics.slice, intrinsics.array]);
		self.impl_dispatch
			.trait_candidates(target)
			.iter()
			.map(|&(trait_index, _)| trait_index)
			.chain(callable.flatten())
			.chain(sequence.into_iter().flatten().flatten())
	}

	/// The member a type-position `lookup` of `segment` off `current` found,
	/// or `None` once its failure is reported: an associated type for a type
	/// tier `key`, a constant for a value one.
	pub(super) fn type_member_found(
		&mut self,
		strings: &StringInterner,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
		current: TypeIndex,
		segment: &ast::PathSegment,
		key: BindingKey,
		lookup: MemberLookup,
	) -> Option<ApplicableMember> {
		let reference = SourceSpan::new(scope.file_id, segment.ident.span);
		let noun = match key.tier {
			Tier::Type => "associated type",
			Tier::Value => "associated constant",
		};
		match lookup {
			MemberLookup::Found(member) => return Some(member),
			MemberLookup::Pending => {
				let receiver =
					self.type_formatter(strings).display_type(current);
				let name = strings.resolve(segment.ident.inner).unwrap();
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::TypeMemberNeedsQualification.code(),
						)
						.with_message(format!(
							"selecting {noun} `{name}` depends on unfinished bounds"
						))
						.with_label(reference.primary_label())
						.with_note(format!(
							"qualify the declaring trait with `<{receiver} as Trait>::{name}`"
						)),
				);
			}
			MemberLookup::Error => {}
			MemberLookup::Stuck(SolverError::Overflow) => {
				self.diagnostics.push(self.overflow_diagnostic(reference));
			}
			MemberLookup::Stuck(SolverError::Cycle(cycle)) => {
				self.diagnostics
					.push(self.cycle_diagnostic(strings, &cycle, reference));
			}
			MemberLookup::Stuck(_) => {}
			// No name is written (`T::` unfinished): the parser reported it.
			MemberLookup::NotFound if segment.is_missing() => {}
			// A projection's declared bounds are only half of what it can
			// have: its value may be a type that does. That takes impls, so
			// the declaration check decides what to say.
			MemberLookup::NotFound
				if key.tier == Tier::Type
					&& matches!(
						self.types.resolve(current),
						Type::TypeProjection { .. }
					) =>
			{
				obligations.push(TypeObligation::CheckProjectionMember {
					frame: scope.generic_env,
					projection: current,
					name: segment.ident.inner,
					reference,
				});
			}
			MemberLookup::NotFound => {
				self.diagnostics.push(report_no_such_type_member(
					scope.file_id,
					strings,
					segment.ident,
					noun,
				));
			}
			MemberLookup::Ambiguous(candidates) => {
				self.diagnostics.push(report_ambiguous_type_member(
					scope.file_id,
					strings,
					&self.decls,
					segment.ident,
					&candidates,
				));
			}
		}
		None
	}

	/// The constant `<receiver as required_trait>::segment` names in a type:
	/// the trait's declaration with the receiver as `Self`, as
	/// `select_type_constant` gives one.
	pub(super) fn select_qualified_constant(
		&mut self,
		strings: &StringInterner,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		segment: &ast::PathSegment,
	) -> Option<(ConstIdx, Vec<TypeIndex>)> {
		let kind = self
			.resolve_trait_qualified_type_member(
				strings,
				obligations,
				scope.generic_env,
				receiver,
				required_trait,
				BindingKey::value(segment.ident.inner),
				segment.ident,
				scope.file_id,
			)
			.ok()?;
		let MemberKind::Constant(constant) = kind else {
			self.report_length_not_constant(
				strings,
				"function",
				segment.ident.inner,
				SourceSpan::new(scope.file_id, segment.ident.span),
			);
			return None;
		};
		Some((constant, vec![receiver]))
	}

	/// Build a symbolic projection. Ordinary signature types normalize it;
	/// bound expressions retain it until their assumptions are available.
	pub(super) fn project_assoc_type(
		&mut self,
		base: TypeIndex,
		member: TypeProjectionTarget,
	) -> TypeIndex {
		member.project(&mut self.types, base)
	}

	/// Resolve the trait declaration named by the first segment of a
	/// qualified type path: an associated type or a function. Later segments
	/// use ordinary type-member lookup.
	#[allow(clippy::too_many_arguments)]
	pub(super) fn resolve_trait_qualified_type_member(
		&mut self,
		strings: &StringInterner,
		obligations: &mut Vec<TypeObligation>,
		frame: GenericEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		key: BindingKey,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<MemberKind, ()> {
		if receiver == TypeIndex::ERROR {
			return Err(());
		}
		let kind = self.resolve_trait_member_declaration(
			strings,
			required_trait,
			key,
			name,
			file_id,
		)?;
		self.resolutions.record(
			Site::new(key.tier, SourceSpan::new(file_id, name.span)),
			Reference::Member(kind),
		);
		// Naming the member does not need an impl; whether `receiver`
		// implements the trait is the declaration check's question.
		obligations.push(TypeObligation::CheckTraitMembership {
			frame,
			subject: receiver,
			required: required_trait,
			reference: SourceSpan::new(file_id, name.span),
		});
		Ok(kind)
	}

	pub(super) fn resolve_trait_qualified_value(
		&mut self,
		strings: &StringInterner,
		obligations: &mut Vec<TypeObligation>,
		frame: GenericEnvIdx,
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
			strings,
			required_trait,
			key,
			name,
			file_id,
		)?;
		let found = self.find_trait_impl(
			strings,
			obligations,
			frame,
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
			// A builtin impl has no members of its own: the declaration is
			// what it provides.
			TraitImplLookup::Abstract | TraitImplLookup::Builtin => {
				ApplicableMember::AbstractTraitMember {
					trait_index: required_trait,
					declaration,
				}
			}
		};
		self.resolutions.record(
			Site::Value(SourceSpan::new(file_id, name.span)),
			Reference::Member(member.selected_kind(&self.decls)),
		);
		Ok(member)
	}

	/// The trait's own declaration of `key`, with no impl involved. A missing
	/// member is a written-site error reported here.
	fn resolve_trait_member_declaration(
		&mut self,
		strings: &StringInterner,
		required_trait: TraitIdx,
		key: BindingKey,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<MemberKind, ()> {
		let trait_decl = &self.decls.traits[usize::from(required_trait)];
		let Some(&member_index) = trait_decl.bindings.get(&key) else {
			self.diagnostics.push(report_missing_trait_member(
				file_id,
				strings,
				name,
				self.decls.item(trait_decl.loc).name.inner,
				key.tier,
			));
			return Err(());
		};
		Ok(trait_decl.members[usize::from(member_index)].kind)
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
		strings: &StringInterner,
		obligations: &mut Vec<TypeObligation>,
		frame: GenericEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<TraitImplLookup, ()> {
		let reference = SourceSpan::new(file_id, span);
		match self.find_trait_impl_query(
			strings,
			self.assumption_envs.of_frame(frame),
			receiver,
			required_trait,
		) {
			Ok(Some(found)) => Ok(found),
			Ok(None) => {
				let diagnostic = report_type_does_not_implement_trait(
					&self.type_formatter(strings),
					file_id,
					span,
					receiver,
					required_trait,
				);
				self.diagnostics.push(diagnostic);
				Err(())
			}
			Err(SolverError::Poisoned) => Err(()),
			Err(SolverError::Overflow) => {
				self.diagnostics.push(self.overflow_diagnostic(reference));
				Err(())
			}
			Err(SolverError::Cycle(cycle)) => {
				self.diagnostics
					.push(self.cycle_diagnostic(strings, &cycle, reference));
				Err(())
			}
			Err(SolverError::Pending) => {
				// A qualified member already has a declaration identity.
				// Membership is checked before the owning query completes.
				obligations.push(TypeObligation::CheckTraitMembership {
					frame,
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
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		target: ImplTarget,
		key: BindingKey,
	) -> MemberLookup {
		// Only a candidate that declares this name can affect precedence.
		let declaring: Vec<_> = self
			.impl_dispatch
			.inherent_candidates(target)
			.iter()
			.filter_map(|&index| {
				let impl_decl = &self.decls.inherent_impls[usize::from(index)];
				let &member_index = impl_decl.bindings.get(&key)?;
				Some((index, impl_decl.members[usize::from(member_index)].kind))
			})
			.collect();
		for (index, kind) in declaring {
			match self.match_inherent_impl_candidate_query(
				strings,
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
		// Only impls and the compiler's rules give a concrete receiver a
		// trait, so no assumption in scope can add a candidate
		// (`Solver::find_trait_impl_query`).
		let mut traits = Vec::new();
		for trait_index in self.trait_candidates(target) {
			if self.decls.declared_trait_member(trait_index, key).is_some() {
				traits.push(trait_index);
			}
		}
		self.resolve_trait_member_candidates(
			strings,
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
		assumption_context: AssumptionEnvIdx,
		key: BindingKey,
	) -> Result<(Vec<TraitIdx>, Readiness), MemberLookup> {
		let tables = self.clause_tables();
		let readiness = tables.assumptions_readiness(assumption_context);
		let mut traits = Vec::new();
		for (_, trait_index) in tables.assumed_traits(assumption_context) {
			if self.decls.traits[usize::from(trait_index)]
				.bindings
				.contains_key(&key)
				&& !traits.contains(&trait_index)
			{
				traits.push(trait_index);
			}
		}
		if readiness == Readiness::Overflowed {
			return Err(MemberLookup::Stuck(SolverError::Overflow));
		}
		Ok((traits, readiness))
	}

	fn resolve_trait_member_candidates(
		&mut self,
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		traits: Vec<TraitIdx>,
		mut readiness: Readiness,
	) -> MemberLookup {
		let mut candidates: Option<SmallVec<ApplicableMember>> = None;
		for trait_index in traits {
			let Some(declaration) =
				self.decls.declared_trait_member(trait_index, key)
			else {
				continue;
			};
			match self.find_trait_impl_query(
				strings,
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
				Ok(Some(
					TraitImplLookup::Abstract | TraitImplLookup::Builtin,
				)) => {
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

	/// The members named `key` among the traits `bounds` supply.
	pub(super) fn select_declared_member(
		decls: &Declarations,
		traits: impl IntoIterator<Item = TraitIdx>,
		key: BindingKey,
	) -> MemberLookup {
		let mut candidates: Option<SmallVec<ApplicableMember>> = None;
		for trait_index in traits {
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
				decls.declared_trait_member(trait_index, key)
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
		Tier::Type => report_not_a_binding_member(
			file_id,
			strings,
			name,
			trait_name,
			"an associated type",
		),
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
	noun: &str,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitMember.code())
		.with_message(format!(
			"no {noun} named `{name_str}` found for this type"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}

/// Inherent members win before trait candidates are gathered, so ambiguous
/// associated-type candidates always have trait declaration identities.
pub(super) fn report_ambiguous_type_member(
	file_id: FileId,
	strings: &StringInterner,
	decls: &Declarations,
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
		let trait_name =
			strings.resolve(decls.name(*trait_index).inner).unwrap();
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
		.resolve(formatter.decls.name(required_trait).inner)
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

impl<'ast> SemanticsBuilder<'ast> {
	/// Selects the trait that supplies an associated type named by `key` off
	/// `receiver`, for a written type path. Selection reads declarations only:
	/// a parameter's bounds, the assumptions in scope, and the traits that have
	/// an impl for the receiver's type constructor (`ImplDispatch`). With one
	/// impl per trait per constructor that index names the provider exactly, so
	/// no impl header is read and nothing is matched. Whether the receiver
	/// really implements the selected trait is recorded as a membership check.
	pub(super) fn select_associated_type(
		&mut self,
		sema: &mut Semantics,
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		match self.declared_bound_member(
			sema,
			assumption_context,
			receiver,
			key,
			reference,
		) {
			MemberLookup::NotFound => {}
			found => return found,
		}
		// Only assumed equalities may rewrite the receiver here, so a concrete
		// head can come from evidence in scope but never from selecting an impl.
		let receiver = match sema.normalize(
			self.strings,
			assumption_context,
			receiver,
			NormalizationDepth::Deep,
			RewriteFlags::EQUALITIES,
		) {
			Ok(receiver) => receiver,
			Err(error) => return error.into(),
		};
		if receiver == TypeIndex::ERROR {
			return MemberLookup::Error;
		}
		let mut traits = Vec::new();
		let mut readiness = Readiness::Ready;
		if !sema.types.is_abstract(receiver) {
			// A concrete type takes its traits from impls and the compiler's
			// rules, never from assumptions (`Solver::find_trait_impl_query`);
			// one no impl can target has none.
			if let Some(target) =
				ImplTarget::from_type(sema.types.resolve(receiver))
			{
				for trait_index in sema.trait_candidates(target) {
					if sema
						.decls
						.declared_trait_member(trait_index, key)
						.is_some()
					{
						traits.push(trait_index);
					}
				}
			}
		} else {
			// Evidence in scope names traits regardless of receiver, so each
			// must be shown to apply by assumptions alone. No impl is consulted.
			let scoped;
			(scoped, readiness) =
				match sema.assumed_member_traits(assumption_context, key) {
					Ok(traits) => traits,
					Err(lookup) => return lookup,
				};
			for trait_index in scoped {
				match sema.check_assumed_trait(
					self.strings,
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
			let declaration = sema
				.decls
				.declared_trait_member(trait_index, key)
				.expect("candidate traits declare the member");
			Semantics::push_candidate(
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
			Semantics::classify(candidates)
		}
	}

	/// Shared applicability and ambiguity search. Declaration identity and
	/// implementation selection happen after this search completes.
	pub(super) fn resolve_applicable_member(
		&mut self,
		sema: &mut Semantics,
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		if matches!(
			sema.types.resolve(receiver),
			Type::TypeParam { .. } | Type::TypeProjection { .. }
		) {
			match self.resolve_bound_member(
				sema,
				assumption_context,
				receiver,
				key,
				reference,
			) {
				MemberLookup::NotFound => {}
				found => return found,
			}
		}
		let receiver = match sema.normalize(
			self.strings,
			assumption_context,
			receiver,
			NormalizationDepth::Shallow,
			RewriteFlags::ALL,
		) {
			Ok(receiver) => receiver,
			Err(error) => return error.into(),
		};
		if receiver == TypeIndex::ERROR {
			return MemberLookup::Error;
		}
		match ImplTarget::from_type(sema.types.resolve(receiver)) {
			Some(target) => sema.resolve_concrete_member(
				self.strings,
				assumption_context,
				receiver,
				target,
				key,
			),
			None => self.resolve_bound_member(
				sema,
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
		sema: &mut Semantics,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
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
				sema,
				obligations,
				scope,
				current,
				segment,
				infer_policy,
			) {
				current = function;
				continue;
			}
			let key = BindingKey::ty(segment.ident.inner);
			let lookup = self.select_associated_type(
				sema,
				scope.assumption_env,
				current,
				key,
				SourceSpan::new(scope.file_id, segment.ident.span),
			);
			let Some(member) = sema.type_member_found(
				self.strings,
				obligations,
				scope,
				current,
				segment,
				key,
				lookup,
			) else {
				return TypeIndex::ERROR;
			};
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
			obligations.push(TypeObligation::CheckTraitMembership {
				frame: scope.generic_env,
				subject: current,
				required: trait_index,
				reference: SourceSpan::new(scope.file_id, segment.ident.span),
			});
			sema.resolutions.record(
				Site::Type(SourceSpan::new(scope.file_id, segment.ident.span)),
				Reference::Member(declaration),
			);
			current = match declaration {
				MemberKind::AssociatedType(assoc_type_index) => {
					if !segment.type_args.is_empty() {
						self.report_assoc_type_args(
							sema,
							obligations,
							scope,
							segment,
							assoc_type_index,
							infer_policy,
						);
						return TypeIndex::ERROR;
					}
					sema.project_assoc_type(
						current,
						TypeProjectionTarget {
							trait_index,
							assoc_type_index,
						},
					)
				}
				// `<current as Trait>::f`: the declaration over
				// `current`, whatever impl `current` has.
				MemberKind::Function(function)
				| MemberKind::Method(function) => {
					let own_args = self.member_function_type_args(
						sema,
						obligations,
						scope,
						function,
						&[current],
						segment,
						infer_policy,
					);
					let mut type_args = vec![current];
					type_args.extend_from_slice(&own_args);
					sema.types.intern_function(function, &type_args)
				}
				MemberKind::Constant(_) => {
					unreachable!("a constant is a value member")
				}
			};
		}
		current
	}

	/// The constant `segment` names off `receiver` in a type (`T::SIZE`,
	/// `Self::SIZE`, `A::SIZE`), with its arguments: an inherent one with its
	/// impl's, or a trait's declaration with the receiver as `Self`, as
	/// `T::Item` is a projection, whose value is the impl's once `Self` is
	/// known. Whether the receiver implements the trait is recorded as a
	/// membership check. `None` once a failure is reported.
	pub(super) fn select_type_constant(
		&mut self,
		sema: &mut Semantics,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
		receiver: TypeIndex,
		segment: &ast::PathSegment,
	) -> Option<(ConstIdx, Vec<TypeIndex>)> {
		if receiver == TypeIndex::ERROR {
			return None;
		}
		let key = BindingKey::value(segment.ident.inner);
		if let Some((kind, impl_args)) = self.select_inherent_member(
			sema,
			obligations,
			scope,
			receiver,
			segment,
			key,
		) {
			let MemberKind::Constant(constant) = kind else {
				unreachable!("a value-tier inherent member here is a constant")
			};
			return Some((constant, impl_args));
		}
		let reference = SourceSpan::new(scope.file_id, segment.ident.span);
		let lookup = self.select_associated_type(
			sema,
			scope.assumption_env,
			receiver,
			key,
			reference,
		);
		let ApplicableMember::AbstractTraitMember {
			trait_index,
			declaration,
		} = sema.type_member_found(
			self.strings,
			obligations,
			scope,
			receiver,
			segment,
			key,
			lookup,
		)?
		else {
			unreachable!(
				"type-position selection reads trait declarations only"
			)
		};
		let MemberKind::Constant(constant) = declaration else {
			sema.report_length_not_constant(
				self.strings,
				"function",
				segment.ident.inner,
				reference,
			);
			return None;
		};
		obligations.push(TypeObligation::CheckTraitMembership {
			frame: scope.generic_env,
			subject: receiver,
			required: trait_index,
			reference,
		});
		sema.resolutions
			.record(Site::Value(reference), Reference::Member(declaration));
		Some((constant, vec![receiver]))
	}

	/// The inherent function `segment` names off a concrete `receiver`, as
	/// its function type with the impl's arguments. `None` leaves the name to
	/// the trait members.
	fn select_inherent_function(
		&mut self,
		sema: &mut Semantics,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
		receiver: TypeIndex,
		segment: &ast::PathSegment,
		infer_policy: InferPolicy,
	) -> Option<TypeIndex> {
		let (kind, mut type_args) = self.select_inherent_member(
			sema,
			obligations,
			scope,
			receiver,
			segment,
			BindingKey::ty(segment.ident.inner),
		)?;
		let (MemberKind::Function(function) | MemberKind::Method(function)) =
			kind
		else {
			unreachable!("a type-tier inherent member is a function")
		};
		let own_args = self.member_function_type_args(
			sema,
			obligations,
			scope,
			function,
			&type_args,
			segment,
			infer_policy,
		);
		type_args.extend_from_slice(&own_args);
		Some(sema.types.intern_function(function, &type_args))
	}

	/// The inherent member `key` names off a concrete `receiver`, a function
	/// for a type tier key and a constant for a value one, with the arguments
	/// of the impl whose target matches the receiver; its bounds on them are
	/// recorded as checks. `None` leaves the name to the trait members.
	pub(super) fn select_inherent_member(
		&mut self,
		sema: &mut Semantics,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
		receiver: TypeIndex,
		segment: &ast::PathSegment,
		key: BindingKey,
	) -> Option<(MemberKind, Vec<TypeIndex>)> {
		let reference = SourceSpan::new(scope.file_id, segment.ident.span);
		// Only assumed equalities may rewrite the receiver here, as for an
		// associated type; a failure is the trait selection's to report.
		let receiver = sema
			.normalize(
				self.strings,
				scope.assumption_env,
				receiver,
				NormalizationDepth::Deep,
				RewriteFlags::EQUALITIES,
			)
			.ok()?;
		let target = ImplTarget::from_type(sema.types.resolve(receiver))?;
		let wanted: Vec<_> = sema
			.impl_dispatch
			.inherent_candidates(target)
			.iter()
			.filter_map(|&impl_index| {
				let impl_decl =
					&sema.decls.inherent_impls[usize::from(impl_index)];
				let &member_index = impl_decl.bindings.get(&key)?;
				let kind = impl_decl.members[usize::from(member_index)].kind;
				let wanted = match key.tier {
					Tier::Type => matches!(
						kind,
						MemberKind::Function(_) | MemberKind::Method(_)
					),
					Tier::Value => matches!(kind, MemberKind::Constant(_)),
				};
				wanted.then_some((impl_index, kind))
			})
			.collect();
		for (impl_index, kind) in wanted {
			let _ = self.ensure_signature(
				sema,
				QueryInfo {
					query: SignatureQuery::InherentImpl(impl_index),
					requested_at: Some(reference),
				},
			);
			let Some(header) = &sema.inherent_impls[usize::from(impl_index)]
			else {
				continue;
			};
			let env = header.type_params;
			let Some(impl_args) = sema.types.match_impl_target(
				header.target.inner,
				receiver,
				&sema.generic_envs,
				env,
			) else {
				continue;
			};
			let args = sema
				.generic_args
				.push(impl_args.iter().map(|&ty| (ty, segment.ident.span)));
			sema.record_bounds_check(
				obligations,
				scope.generic_env,
				BoundRequirements::Frame { env, args },
				reference,
				GenericEnvOwner::InherentImpl(impl_index),
			);
			sema.resolutions.record(
				Site::new(key.tier, reference),
				Reference::Member(kind),
			);
			return Some((kind, impl_args.into_vec()));
		}
		None
	}

	/// Traits supplied by the receiver's own declared bounds, by name only.
	pub(super) fn declared_bound_member(
		&mut self,
		sema: &mut Semantics,
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		if !matches!(
			sema.types.resolve(receiver),
			Type::TypeParam { .. } | Type::TypeProjection { .. }
		) {
			return MemberLookup::NotFound;
		}
		if self
			.prepare_declarations_of(sema, receiver, reference)
			.is_err()
		{
			return MemberLookup::Error;
		}
		Semantics::select_declared_member(
			&sema.decls,
			sema.clause_tables().declared_traits(
				&sema.types,
				assumption_context,
				receiver,
				sema.solver.state.recursion_budget,
			),
			key,
		)
	}

	fn resolve_bound_member(
		&mut self,
		sema: &mut Semantics,
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> MemberLookup {
		// Preserve direct declaration lookup, including known provisional
		// memberships. Equality-based discovery is a fallback when these bounds
		// do not identify the requested name.
		match self.declared_bound_member(
			sema,
			assumption_context,
			receiver,
			key,
			reference,
		) {
			MemberLookup::NotFound => {}
			found => return found,
		}
		let (traits, readiness) =
			match sema.assumed_member_traits(assumption_context, key) {
				Ok(traits) => traits,
				Err(lookup) => return lookup,
			};
		sema.resolve_trait_member_candidates(
			self.strings,
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
		sema: &mut Semantics,
		assoc_type_index: AssocTypeIdx,
		requested_at: SourceSpan,
	) -> Result<(), ()> {
		let query = SignatureQuery::AssocType(assoc_type_index);
		assert!(
			matches!(
				self.ast_entry(query).node,
				AstNodeRef::TraitAssocType { .. }
			),
			"bound access requires a trait declaration, not a provider"
		);
		match self.ensure_signature(
			sema,
			QueryInfo {
				query,
				requested_at: Some(requested_at),
			},
		) {
			SignatureStatus::Available(SignatureLocation::AssocType(..)) => {
				Ok(())
			}
			SignatureStatus::Available(_) => unreachable!(
				"a trait associated-type declaration has its own signature query"
			),
			SignatureStatus::Cycle => {
				let diagnostic = self.report_cyclic_assoc_type_bound(
					sema,
					query,
					requested_at,
				);
				sema.diagnostics.push(diagnostic);
				Err(())
			}
			SignatureStatus::CycleReported => Err(()),
		}
	}
}
