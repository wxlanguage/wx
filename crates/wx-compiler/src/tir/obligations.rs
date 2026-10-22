//! Requirements a declaration's signature states, and the contexts that solve
//! them. Construction lowers written syntax and never checks a bound; a site
//! that needs one registers an `Obligation` with the signature being built,
//! and the declaration keeps them. Checking the declaration, once every
//! signature exists, checks them. A check never changes a stored signature: a
//! failure is diagnosed and nothing is rewritten.
//!
//! A check runs on an `ObligationChecker`, which borrows only what checking
//! may touch, through the module that owns its question (bound satisfaction,
//! the solver's judgements); this module records requirements, dispatches
//! checks, and reports what a solver could not finish.
//!
//! What is written inside a declaration (a constant's initializer, an enum's
//! discriminants) is not an obligation: it is a body, checked by the body
//! phase that follows this pass (`TypeContext::check_bodies`).

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use super::bounds::BoundArena;
use super::defs::{AssocTypeIdx, TraitIdx};
use super::format::TypeFormatter;
use super::members::report_type_does_not_implement_trait;
use super::signatures::TypeContext;
use super::solver::{
	Definition, ImplMember, Solver, SolverError, SolverView, Verdict,
};
use super::types::{ImplKind, TypeEnvIdx, TypeEnvOwner, TypeIndex, TypeList};
use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::vfs::FileId;

/// Requirements refer to their eventual bound table, so a provisional table
/// cannot lose inherited requirements that have not been published yet.
#[derive(Clone, Copy)]
pub(super) enum BoundRequirements {
	/// Parameter `index` of `env`. `arguments` is the use's flat argument list
	/// for `env`'s whole chain, outer frames first: a binding's value is
	/// written in the declaration, so it may name any of them.
	Parameter {
		env: TypeEnvIdx,
		index: usize,
		arguments: TypeList,
	},
	/// The declared bounds of `declaration`, a member of `trait_index`, whose
	/// `Self` is `receiver`.
	AssociatedType {
		declaration: AssocTypeIdx,
		trait_index: TraitIdx,
		receiver: TypeIndex,
	},
}

#[derive(Clone, Copy)]
pub(super) enum Obligation {
	CheckBounds {
		assumption_context: TypeEnvIdx,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	},
	CheckTraitMembership {
		assumption_context: TypeEnvIdx,
		subject: TypeIndex,
		required: TraitIdx,
		reference: SourceSpan,
	},
	/// A written type is normalized once, so a cycle or an exhausted budget
	/// inside it is found even if nothing ever reads the type. The result is
	/// discarded: the stored type stays as written.
	CheckWellFormed {
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		reference: SourceSpan,
	},
	/// An impl member's value (its own, or the trait default it inherits) has a
	/// meaning. Unlike `CheckWellFormed`, the judgement is the solver's, made
	/// once whoever asks first (`Verdict`); this check reports the failure
	/// the member owns, so a loop through definitions is reported once, where
	/// it is defined, and readers of a poisoned value stay silent. `reference`
	/// is the written value, or the impl's target for an inherited default.
	CheckAssocValue {
		member: ImplMember,
		reference: SourceSpan,
	},
	/// A generic impl's requirements have a meaning: proving them for its own
	/// parameters in its own scope does not need the impl itself. Like
	/// `CheckAssocValue`, the judgement is the solver's, made once whoever
	/// asks first; this check reports a loop the impl owns, once, at the bound
	/// it closed in, and every selection of the impl stays silent.
	/// `reference` is the impl's target, for a judgement that ran out of
	/// budget.
	CheckImplRequirements {
		impl_kind: ImplKind,
		reference: SourceSpan,
	},
	/// `Projection::name` was written, and the projection's declared bounds do
	/// not name `name`. Whether its *value* has such a member depends on impls,
	/// which construction cannot read, so the type was lowered to `ERROR` and
	/// this decides what to say: a plain "no such member", or, when the value
	/// does have one, that the trait must be named (with the spelling).
	CheckProjectionMember {
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		name: SymbolU32,
		reference: SourceSpan,
	},
}

impl TypeContext<'_, '_, '_> {
	/// The checker over this context's finished tables.
	fn obligation_checker(&mut self) -> ObligationChecker<'_> {
		ObligationChecker {
			solver: &mut self.solver,
			view: SolverView {
				types: &mut self.types,
				defs: self.defs,
				impl_dispatch: self.impl_dispatch,
				traits: &self.traits,
				trait_impls: &self.trait_impls,
				inherent_impls: &self.inherent_impls,
				assoc_types: &self.assoc_types,
				structs: &self.structs,
				enums: &self.enums,
				param_bounds: &self.param_bounds,
				clauses: &self.clauses,
				type_envs: &self.type_envs,
			},
			bounds: &self.bounds,
			strings: self.strings,
			diagnostics: self.diagnostics,
		}
	}

	/// Checks `obligations` once every signature exists: a declaration's
	/// own, or what a body recorded while lowering a written type. Every fact
	/// is final then, so nothing can be pending; a failure reports itself.
	pub(super) fn check_now(&mut self, obligations: &[Obligation]) {
		let mut checker = self.obligation_checker();
		for obligation in obligations {
			if let Err(SolverError::Pending) = checker.check(obligation) {
				debug_assert!(
					false,
					"a check cannot be pending once every signature is built"
				);
			}
		}
	}

	/// A solver that cannot finish (budget or cycle) reports nothing; the
	/// construct that wrote the requirement does, here, once, at its own span.
	/// Any other result passes through for the caller to recover from.
	pub(super) fn report_solver_error<T>(
		&mut self,
		result: Result<T, SolverError>,
		site: SourceSpan,
	) -> Result<T, SolverError> {
		let Err(error) = &result else {
			return result;
		};
		let Some(diagnostic) =
			solver_error_diagnostic(&self.type_formatter(), error, site)
		else {
			return result;
		};
		self.diagnostics.push(diagnostic);
		Err(SolverError::Poisoned)
	}
}

/// The diagnostic for a solver that could not finish, reported at `site`;
/// `None` for an answer that is not a divergence.
fn solver_error_diagnostic(
	formatter: &TypeFormatter<'_>,
	error: &SolverError,
	site: SourceSpan,
) -> Option<Diagnostic<FileId>> {
	Some(match error {
		SolverError::Overflow => Diagnostic::error()
			.with_code(DiagnosticCode::TypeNormalizationOverflow.code())
			.with_message("type normalization exceeded its recursion limit")
			.with_label(site.primary_label()),
		SolverError::Cycle(cycle) => {
			let mut diagnostic = Diagnostic::error()
				.with_code(DiagnosticCode::CyclicAssociatedType.code())
				.with_message(format!(
					"cycle detected when normalizing `{}`",
					formatter.display_type(cycle.projection)
				))
				.with_label(site.primary_label());
			for step in cycle.steps.iter().copied() {
				diagnostic = diagnostic.with_label(
					site.secondary_label().with_message(format!(
						"requires normalizing `{}`",
						formatter.display_type(step)
					)),
				);
			}
			diagnostic
		}
		SolverError::Pending | SolverError::Poisoned => return None,
	})
}

/// What checking an obligation may touch: the solver's memoized state, the
/// interner it interns into, and the diagnostics it reports to. Every table it
/// reads is final by then and shared. It holds no query state, so a check can
/// neither force a signature nor register another obligation.
pub(super) struct ObligationChecker<'a> {
	pub(super) solver: &'a mut Solver,
	pub(super) view: SolverView<'a>,
	pub(super) bounds: &'a BoundArena,
	pub(super) strings: &'a StringInterner,
	pub(super) diagnostics: &'a mut Vec<Diagnostic<FileId>>,
}

impl ObligationChecker<'_> {
	pub(super) fn type_formatter(&self) -> TypeFormatter<'_> {
		TypeFormatter {
			types: self.view.types,
			defs: self.view.defs,
			strings: self.strings,
			type_envs: self.view.type_envs,
		}
	}

	/// `Ok` means the obligation holds. A failure has been reported (or derives
	/// from one that was), so callers only need to know that it did not.
	pub(super) fn check(
		&mut self,
		obligation: &Obligation,
	) -> Result<(), SolverError> {
		let site = match *obligation {
			Obligation::CheckBounds { reference, .. }
			| Obligation::CheckTraitMembership { reference, .. }
			| Obligation::CheckWellFormed { reference, .. }
			| Obligation::CheckAssocValue { reference, .. }
			| Obligation::CheckImplRequirements { reference, .. }
			| Obligation::CheckProjectionMember { reference, .. } => reference,
		};
		// The obligation is the owning site: a normalization that diverged inside
		// it is reported here, once.
		let result = self.run(obligation);
		let Err(error) = &result else {
			return result;
		};
		let Some(diagnostic) =
			solver_error_diagnostic(&self.type_formatter(), error, site)
		else {
			return result;
		};
		self.diagnostics.push(diagnostic);
		Err(SolverError::Poisoned)
	}

	fn run(&mut self, obligation: &Obligation) -> Result<(), SolverError> {
		match *obligation {
			Obligation::CheckBounds {
				assumption_context,
				requirements,
				argument,
				reference,
				owner,
			} => self.check_requirements(
				assumption_context,
				requirements,
				argument,
				reference,
				owner,
			),
			Obligation::CheckTraitMembership {
				assumption_context,
				subject,
				required,
				reference,
			} => {
				if self
					.solver
					.find_trait_impl_query(
						&mut self.view,
						assumption_context,
						subject,
						required,
					)?
					.is_some()
				{
					return Ok(());
				}
				let diagnostic = report_type_does_not_implement_trait(
					&self.type_formatter(),
					reference.file_id,
					reference.span,
					subject,
					required,
				);
				self.diagnostics.push(diagnostic);
				Err(SolverError::Poisoned)
			}
			Obligation::CheckWellFormed {
				assumption_context,
				ty,
				..
			} => {
				self.solver.normalize_type_query(
					&mut self.view,
					assumption_context,
					ty,
				)?;
				Ok(())
			}
			// A judgement the definition owns: its verdict holds the failure,
			// whoever asked first.
			Obligation::CheckAssocValue { member, .. } => {
				if let Err(SolverError::Pending) =
					self.solver.assoc_value(&mut self.view, member, None)
				{
					return Err(SolverError::Pending);
				}
				match self.solver.verdict(Definition::Member(member)) {
					Verdict::Resolved => Ok(()),
					Verdict::Overflowed => Err(SolverError::Overflow),
					Verdict::Cyclic(cycle) => {
						Err(SolverError::Cycle(cycle.clone()))
					}
					Verdict::Poisoned => Err(SolverError::Poisoned),
					Verdict::Unchecked | Verdict::InProgress => {
						unreachable!("a finished judgement has a verdict")
					}
				}
			}
			Obligation::CheckImplRequirements { impl_kind, .. } => {
				if let Err(SolverError::Pending) =
					self.solver.requirements_verdict(&mut self.view, impl_kind)
				{
					return Err(SolverError::Pending);
				}
				let definition = Definition::Requirements(impl_kind);
				match self.solver.verdict(definition) {
					Verdict::Resolved => Ok(()),
					Verdict::Overflowed => Err(SolverError::Overflow),
					// Reported at the bound the loop closed in, not at the impl:
					// that is the requirement that names the impl again.
					Verdict::Cyclic(cycle) => {
						let bound = cycle.bound.expect(
							"an impl's requirements own a loop in a bound",
						);
						let error = SolverError::Cycle(cycle.clone());
						let diagnostic = solver_error_diagnostic(
							&self.type_formatter(),
							&error,
							self.bounds.span(bound),
						)
						.expect("a cycle has a report");
						self.diagnostics.push(diagnostic);
						Err(SolverError::Poisoned)
					}
					Verdict::Poisoned => Err(SolverError::Poisoned),
					Verdict::Unchecked | Verdict::InProgress => {
						unreachable!("a finished judgement has a verdict")
					}
				}
			}
			Obligation::CheckProjectionMember {
				assumption_context,
				projection,
				name,
				reference,
			} => self.check_projection_member(
				assumption_context,
				projection,
				name,
				reference,
			),
		}
	}
}
