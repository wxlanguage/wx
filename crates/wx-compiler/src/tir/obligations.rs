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

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::bounds::BoundArena;
use super::defs::{AssocTypeIdx, ConstIdx, TraitIdx};
use super::format::TypeFormatter;
use super::literals::Integer;
use super::members::report_type_does_not_implement_trait;
use super::signatures::{ConstantSignature, TypeContext, TypeSetSignature};
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
	/// A constant written in a type fits its type `ty`, as written: an
	/// array's length fits its memory's `Size`. An abstract type is any
	/// member of the typesets its bounds name, so the value must fit every
	/// one of them, and the type works with each.
	CheckConstantFits {
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		bits: u64,
		reference: SourceSpan,
	},
	/// A constant named in a type (an array's length) has exactly the type
	/// its position needs, `expected` as written: a constant of another type
	/// is a mismatch, even one whose value would fit. Checking it first
	/// evaluates the constant (`TypeContext::check_now`), so the type it is
	/// written in can be normalized to its value afterwards.
	CheckConstantType {
		assumption_context: TypeEnvIdx,
		constant: ConstIdx,
		expected: TypeIndex,
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
				constants: &self.constants,
				const_bodies: &self.const_bodies,
				strings: self.strings,
			},
			bounds: &self.bounds,
			typesets: &self.typesets,
			constants: &self.constants,
			strings: self.strings,
			diagnostics: self.diagnostics,
		}
	}

	/// Checks `obligations` once every signature exists: a declaration's
	/// own, or what a body recorded while lowering a written type. A failure
	/// reports itself. Returns the ones that are pending: they read a
	/// constant's value while constant bodies are still being built, which
	/// only a constant's body can, and it decides them once every body exists.
	#[must_use]
	pub(super) fn check_now(
		&mut self,
		obligations: &[Obligation],
	) -> Vec<Obligation> {
		let mut pending = Vec::new();
		for obligation in obligations {
			if let Err(SolverError::Pending) =
				self.obligation_checker().check(obligation)
			{
				pending.push(*obligation);
			}
		}
		pending
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
	pub(super) typesets: &'a [TypeSetSignature],
	pub(super) constants: &'a [ConstantSignature],
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
			| Obligation::CheckConstantFits { reference, .. }
			| Obligation::CheckConstantType { reference, .. }
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
			Obligation::CheckConstantFits {
				assumption_context,
				ty,
				bits,
				reference,
			} => self.check_constant_fits(
				assumption_context,
				ty,
				bits,
				reference,
			),
			Obligation::CheckConstantType {
				assumption_context,
				constant,
				expected,
				reference,
			} => self.check_constant_type(
				assumption_context,
				constant,
				expected,
				reference,
			),
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

impl ObligationChecker<'_> {
	/// `bits` fits `ty`: an integer type's range, or, for an abstract type,
	/// the range of every member of every typeset its bounds name.
	fn check_constant_fits(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		bits: u64,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		let ty = self.solver.normalize_type_query(
			&mut self.view,
			assumption_context,
			ty,
		)?;
		if let Some(integer) = Integer::from_type(ty) {
			if integer.in_range(bits, false) {
				return Ok(());
			}
			let message = format!(
				"`{bits}` is out of range for `{}`",
				self.type_formatter().display_type(ty)
			);
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::IntegerLiteralOutOfRange.code())
					.with_message(message)
					.with_label(reference.primary_label()),
			);
			return Err(SolverError::Poisoned);
		}
		let clause_tables = self.view.clause_tables();
		let typesets = clause_tables
			.declared_traits(
				self.view.types,
				ty,
				self.solver.state.recursion_budget,
			)
			.filter_map(|trait_index| {
				self.view.defs.traits[usize::from(trait_index)].typeset
			})
			.collect::<Vec<_>>();
		for typeset in typesets {
			let misfit = self.typesets[usize::from(typeset)]
				.members
				.iter()
				.find(|member| {
					!Integer::from_type(member.inner)
						.is_some_and(|integer| integer.in_range(bits, false))
				});
			let Some(member) = misfit else {
				continue;
			};
			let def = &self.view.defs.typesets[usize::from(typeset)];
			let typeset_name = self.strings.resolve(def.name.inner).unwrap();
			let member_name = self.type_formatter().display_type(member.inner);
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypesetBoundViolation.code())
					.with_message(format!(
						"`{bits}` is not representable by every member of \
						 typeset `{typeset_name}`"
					))
					.with_label(reference.primary_label().with_message(
						format!("cannot be represented by `{member_name}`"),
					))
					.with_label(
						Label::secondary(def.file_id, member.span)
							.with_message(format!(
								"`{member_name}` is a member here"
							)),
					),
			);
			return Err(SolverError::Poisoned);
		}
		Ok(())
	}

	/// The constant's type, in its own scope, is `expected`, in the scope
	/// the constant is named in.
	fn check_constant_type(
		&mut self,
		assumption_context: TypeEnvIdx,
		constant: ConstIdx,
		expected: TypeIndex,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		let signature = &self.constants[usize::from(constant)];
		let (ty, env) = (signature.ty, signature.env);
		let found =
			self.solver.normalize_type_query(&mut self.view, env, ty)?;
		let expected = self.solver.normalize_type_query(
			&mut self.view,
			assumption_context,
			expected,
		)?;
		if found == expected
			|| found == TypeIndex::ERROR
			|| expected == TypeIndex::ERROR
		{
			return Ok(());
		}
		let formatter = self.type_formatter();
		let (expected, found) = (
			formatter.display_type(expected),
			formatter.display_type(found),
		);
		let name = self.view.defs.constants[usize::from(constant)].name.inner;
		let name = self.strings.resolve(name).unwrap();
		self.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypeMistmatch.code())
				.with_message(format!(
					"an array's length is a `{expected}`, but `{name}` is a \
					 `{found}`"
				))
				.with_label(reference.primary_label().with_message(format!(
					"expected `{expected}`, found `{found}`"
				)))
				.with_note("an array's length is of its memory's `Size`"),
		);
		Err(SolverError::Poisoned)
	}
}
