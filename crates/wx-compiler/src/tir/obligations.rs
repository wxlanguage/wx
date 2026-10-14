//! Checks recorded while signatures are constructed and run by the check pass
//! that follows construction (see `notes/tir-check-pass.md`). Construction
//! lowers written syntax and never checks a bound; a site that needs one records
//! an `Obligation` against the declaration being built. A check never changes a
//! stored signature: a failure is diagnosed and nothing is rewritten.
//!
//! Each check runs through the module that owns its question (bound
//! satisfaction, the solver's judgements, constant evaluation); this module
//! records checks, runs the pass, and reports what a solver could not finish.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use super::defs::{AssocTypeIdx, ConstIdx, TraitIdx};
use super::signatures::TypeContext;
use super::solver::{ImplMember, Unsolved};
use super::types::{TypeEnvIdx, TypeEnvOwner, TypeIndex};
use crate::ast::Spanned;
use crate::diagnostics::{DiagnosticCode, SourceSpan};

/// Requirements refer to their eventual bound table, so a provisional table
/// cannot lose inherited requirements that have not been published yet.
#[derive(Clone, Copy)]
pub(super) enum BoundRequirements {
	Parameter { env: TypeEnvIdx, index: usize },
	AssociatedType(AssocTypeIdx),
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
	/// once whoever asks first (`AssocValue`); this check reports the failure
	/// the member owns, so a loop through definitions is reported once, where
	/// it is defined, and readers of a poisoned value stay silent. `reference`
	/// is the written value, or the impl's target for an inherited default.
	CheckAssocValue {
		member: ImplMember,
		reference: SourceSpan,
	},
	/// A constant's initializer is checked against its declared type, in the
	/// scope the constant is declared in, and evaluated when the type is a
	/// scalar. Runs once every signature exists, since the initializer may name
	/// any item.
	CheckConstant {
		const_index: ConstIdx,
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
	/// Records a check for the pass that follows construction. The owner is the
	/// signature query being constructed, so the pass can run in definition order.
	pub(super) fn register_obligation(&mut self, obligation: Obligation) {
		let owner = self
			.query_stack
			.last()
			.expect("recorded checks belong to a signature query")
			.def_id;
		self.checks.push((owner, obligation));
	}

	/// The check pass: every signature exists and every fact is `Ready`, so a
	/// check answering `Pending` is an internal invariant failure. A failed check
	/// has already reported itself; nothing is rewritten.
	pub(super) fn run_checks(&mut self) {
		let mut checks = std::mem::take(&mut self.checks);
		// Stable, so checks of one declaration keep their source order. Order
		// only arranges the output: a fact one check reads from another
		// definition is the solver's memoized judgement, not this pass's.
		checks.sort_by_key(|(owner, _)| self.ast_index(*owner));
		for (_, obligation) in &checks {
			self.run_check(obligation);
		}
		debug_assert!(
			self.checks.is_empty(),
			"running a check cannot record another"
		);
	}

	fn run_check(&mut self, obligation: &Obligation) {
		if let Err(Unsolved::Pending) = self.check_obligation(obligation) {
			debug_assert!(
				false,
				"a check cannot be pending once every signature is built"
			);
		}
	}

	/// A solver that cannot finish (budget or cycle) reports nothing; the
	/// construct that wrote the requirement does, here, once, at its own span.
	/// Any other result passes through for the caller to recover from.
	pub(super) fn report_unsolved<T>(
		&mut self,
		result: Result<T, Unsolved>,
		site: SourceSpan,
	) -> Result<T, Unsolved> {
		let diagnostic = match &result {
			Err(Unsolved::Overflow) => Diagnostic::error()
				.with_code(DiagnosticCode::TypeNormalizationOverflow.code())
				.with_message("type normalization exceeded its recursion limit")
				.with_label(site.primary_label()),
			Err(Unsolved::Cycle(cycle)) => {
				let mut diagnostic = Diagnostic::error()
					.with_code(DiagnosticCode::CyclicAssociatedType.code())
					.with_message(format!(
						"cycle detected when normalizing `{}`",
						self.type_formatter().display_type(cycle.projection)
					))
					.with_label(site.primary_label());
				for &step in cycle.steps.iter() {
					diagnostic = diagnostic.with_label(
						site.secondary_label().with_message(format!(
							"requires normalizing `{}`",
							self.type_formatter().display_type(step)
						)),
					);
				}
				diagnostic
			}
			_ => return result,
		};
		self.diagnostics.push(diagnostic);
		Err(Unsolved::Failed)
	}

	/// `Ok` means the obligation holds. A failure has been reported (or derives
	/// from one that was), so callers only need to know that it did not.
	pub(super) fn check_obligation(
		&mut self,
		obligation: &Obligation,
	) -> Result<(), Unsolved> {
		let site = match *obligation {
			Obligation::CheckBounds { reference, .. }
			| Obligation::CheckTraitMembership { reference, .. }
			| Obligation::CheckWellFormed { reference, .. }
			| Obligation::CheckAssocValue { reference, .. }
			| Obligation::CheckConstant { reference, .. }
			| Obligation::CheckProjectionMember { reference, .. } => reference,
		};
		// The obligation is the owning site: a normalization that diverged inside
		// it is reported here, once.
		let result = self.run_obligation(obligation);
		self.report_unsolved(result, site)
	}

	fn run_obligation(
		&mut self,
		obligation: &Obligation,
	) -> Result<(), Unsolved> {
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
					.find_trait_impl_query(
						assumption_context,
						subject,
						required,
					)?
					.is_some()
				{
					return Ok(());
				}
				let diagnostic = self.report_type_does_not_implement_trait(
					reference.file_id,
					reference.span,
					subject,
					required,
				);
				self.diagnostics.push(diagnostic);
				Err(Unsolved::Failed)
			}
			Obligation::CheckWellFormed {
				assumption_context,
				ty,
				..
			} => {
				self.normalize_type_query(assumption_context, ty)?;
				Ok(())
			}
			Obligation::CheckAssocValue { member, .. } => {
				self.judge_assoc_value(member)
			}
			Obligation::CheckConstant { const_index, .. } => {
				self.ensure_const_body(const_index);
				self.evaluate_constant(const_index);
				Ok(())
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
