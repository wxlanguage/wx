//! Requirements a declaration's signature states, and the contexts that solve
//! them. Construction lowers written syntax and never checks a bound; a site
//! that needs one registers an `TypeObligation` with the signature being built,
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
use super::defs::{AssocTypeIdx, ConstIdx, TraitIdx, TraitImplIdx};
use super::literals::Integer;
use super::members::report_type_does_not_implement_trait;
use super::signatures::{ConstantSignature, TypeContext, TypeSetSignature};
use super::solver::{
	Definition, ImplMember, NormalizationDepth, ProjectionCycle, RewriteFlags,
	Solver, SolverError, Verdict,
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
pub(super) enum TypeObligation {
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
	/// is a mismatch, even one whose value would fit. Both types are compared
	/// normalized with every fact, so a constant either names is read; a
	/// constant's body therefore records it for after the values exist.
	CheckConstantType {
		assumption_context: TypeEnvIdx,
		constant: ConstIdx,
		expected: TypeIndex,
		reference: SourceSpan,
	},
	/// A trait impl keeps its trait's contract (`conformance.rs`).
	CheckConformance { impl_index: TraitImplIdx },
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
	/// The diagnostic for a normalization that ran out of its recursion budget,
	/// reported at `site`, the construct that asked.
	pub(super) fn overflow_diagnostic(
		&self,
		site: SourceSpan,
	) -> Diagnostic<FileId> {
		Diagnostic::error()
			.with_code(DiagnosticCode::TypeNormalizationOverflow.code())
			.with_message("type normalization exceeded its recursion limit")
			.with_label(site.primary_label())
	}

	/// The diagnostic for a projection that requires itself, reported at
	/// `site`, the construct that asked.
	pub(super) fn cycle_diagnostic(
		&self,
		cycle: &ProjectionCycle,
		site: SourceSpan,
	) -> Diagnostic<FileId> {
		let formatter = self.type_formatter();
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
}

impl TypeContext<'_, '_, '_> {
	pub(super) fn check_obligation(
		&mut self,
		obligation: &TypeObligation,
	) -> Result<(), ()> {
		match *obligation {
			TypeObligation::CheckBounds {
				assumption_context,
				requirements,
				argument,
				reference,
				owner,
			} => match self.check_bound_requirements(
				assumption_context,
				requirements,
				argument,
				reference,
				owner,
			) {
				Ok(_) => Ok(()),
				Err(SolverError::Cycle(cycle)) => {
					let diagnostic = self.cycle_diagnostic(&cycle, reference);
					self.diagnostics.push(diagnostic);
					Ok(())
				}
				Err(SolverError::Overflow) => {
					self.diagnostics.push(self.overflow_diagnostic(reference));
					Ok(())
				}
				Err(SolverError::Poisoned) => Ok(()),
				Err(SolverError::Pending) => Err(()),
			},
			TypeObligation::CheckTraitMembership {
				assumption_context,
				subject,
				required,
				reference,
			} => {
				match self.find_trait_impl_query(
					assumption_context,
					subject,
					required,
				) {
					Ok(Some(_)) => Ok(()),
					Ok(None) => {
						let diagnostic = report_type_does_not_implement_trait(
							&self.type_formatter(),
							reference.file_id,
							reference.span,
							subject,
							required,
						);
						self.diagnostics.push(diagnostic);
						Ok(())
					}
					Err(SolverError::Cycle(cycle)) => {
						let diagnostic =
							self.cycle_diagnostic(&cycle, reference);
						self.diagnostics.push(diagnostic);
						Ok(())
					}
					Err(SolverError::Overflow) => {
						self.diagnostics
							.push(self.overflow_diagnostic(reference));
						Ok(())
					}
					Err(SolverError::Poisoned) => Ok(()),
					Err(SolverError::Pending) => Err(()),
				}
			}
			TypeObligation::CheckWellFormed {
				assumption_context,
				ty,
				reference,
			} => {
				match self.normalize(
					assumption_context,
					ty,
					NormalizationDepth::Deep,
					RewriteFlags::ALL,
				) {
					Ok(_) => Ok(()),
					Err(SolverError::Cycle(cycle)) => {
						let diagnostic =
							self.cycle_diagnostic(&cycle, reference);
						self.diagnostics.push(diagnostic);
						Ok(())
					}
					Err(SolverError::Overflow) => {
						self.diagnostics
							.push(self.overflow_diagnostic(reference));
						Ok(())
					}
					Err(SolverError::Poisoned) => Ok(()),
					Err(SolverError::Pending) => Err(()),
				}
			}
			// A judgement the definition owns: its verdict holds the failure,
			// whoever asked first.
			TypeObligation::CheckAssocValue { member, reference } => {
				// This check owns the judgement, so it asks once (which computes
				// and memoizes the verdict) and reports the failure the verdict
				// kept for it. A failure another definition owns was reported
				// there and stays silent here. Only "not decided yet" is
				// forwarded.
				match self.assoc_value(member, None) {
					Ok(_) => Ok(()),
					Err(SolverError::Pending) => Err(()),
					Err(_) => {
						match self.solver.verdict(Definition::Member(member)) {
							Verdict::Resolved => Ok(()),
							Verdict::Overflowed => {
								self.diagnostics
									.push(self.overflow_diagnostic(reference));
								Ok(())
							}
							Verdict::Cyclic(cycle) => {
								let diagnostic =
									self.cycle_diagnostic(cycle, reference);
								self.diagnostics.push(diagnostic);
								Ok(())
							}
							Verdict::Poisoned => Ok(()),
							Verdict::Unchecked | Verdict::InProgress => {
								unreachable!(
									"a finished judgement has a verdict"
								)
							}
						}
					}
				}
			}
			TypeObligation::CheckImplRequirements {
				impl_kind,
				reference,
			} => {
				// Like `CheckAssocValue`: ask once, then report the failure the
				// impl's own verdict holds. Every selection of a failed impl
				// stays silent.
				match self.requirements_verdict(impl_kind) {
					Ok(()) => Ok(()),
					Err(SolverError::Pending) => Err(()),
					Err(_) => {
						let definition = Definition::Requirements(impl_kind);
						match self.solver.verdict(definition) {
							Verdict::Resolved => Ok(()),
							Verdict::Overflowed => {
								self.diagnostics
									.push(self.overflow_diagnostic(reference));
								Ok(())
							}
							// Reported at the bound the loop closed in, not at the
							// impl: that is the requirement that names the impl
							// again.
							Verdict::Cyclic(cycle) => {
								let bound = cycle.bound.expect(
									"an impl's requirements own a loop in a bound",
								);
								let diagnostic = self.cycle_diagnostic(
									cycle,
									self.bounds.span(bound),
								);
								self.diagnostics.push(diagnostic);
								Ok(())
							}
							Verdict::Poisoned => Ok(()),
							Verdict::Unchecked | Verdict::InProgress => {
								unreachable!(
									"a finished judgement has a verdict"
								)
							}
						}
					}
				}
			}
			TypeObligation::CheckConstantFits {
				assumption_context,
				ty,
				bits,
				reference,
			} => match self.check_constant_fits(
				assumption_context,
				ty,
				bits,
				reference,
			) {
				Ok(_) => Ok(()),
				Err(SolverError::Cycle(cycle)) => {
					let diagnostic = self.cycle_diagnostic(&cycle, reference);
					self.diagnostics.push(diagnostic);
					Ok(())
				}
				Err(SolverError::Overflow) => {
					self.diagnostics.push(self.overflow_diagnostic(reference));
					Ok(())
				}
				Err(SolverError::Poisoned) => Ok(()),
				Err(SolverError::Pending) => Err(()),
			},
			TypeObligation::CheckConstantType {
				assumption_context,
				constant,
				expected,
				reference,
			} => match self.check_constant_type(
				assumption_context,
				constant,
				expected,
				reference,
			) {
				Ok(_) => Ok(()),
				Err(SolverError::Cycle(cycle)) => {
					let diagnostic = self.cycle_diagnostic(&cycle, reference);
					self.diagnostics.push(diagnostic);
					Ok(())
				}
				Err(SolverError::Overflow) => {
					self.diagnostics.push(self.overflow_diagnostic(reference));
					Ok(())
				}
				Err(SolverError::Poisoned) => Ok(()),
				Err(SolverError::Pending) => Err(()),
			},
			// Reports everything but "not decided yet" itself.
			TypeObligation::CheckConformance { impl_index } => {
				self.check_conformance(impl_index).map_err(|_| ())
			}
			TypeObligation::CheckProjectionMember {
				assumption_context,
				projection,
				name,
				reference,
			} => match self.check_projection_member(
				assumption_context,
				projection,
				name,
				reference,
			) {
				Ok(_) => Ok(()),
				Err(SolverError::Cycle(cycle)) => {
					let diagnostic = self.cycle_diagnostic(&cycle, reference);
					self.diagnostics.push(diagnostic);
					Ok(())
				}
				Err(SolverError::Overflow) => {
					self.diagnostics.push(self.overflow_diagnostic(reference));
					Ok(())
				}
				Err(SolverError::Poisoned) => Ok(()),
				Err(SolverError::Pending) => Err(()),
			},
		}
	}
}

impl TypeContext<'_, '_, '_> {
	/// `bits` fits `ty`: an integer type's range, or, for an abstract type,
	/// the range of every member of every typeset its bounds name.
	fn check_constant_fits(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		bits: u64,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		let ty = self.normalize(
			assumption_context,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
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
		let clause_tables = self.clause_tables();
		let typesets = clause_tables
			.declared_traits(
				&self.types,
				ty,
				self.solver.state.recursion_budget,
			)
			.filter_map(|trait_index| {
				self.defs.traits[usize::from(trait_index)].typeset
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
			let def = &self.defs.typesets[usize::from(typeset)];
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
		let found = self.normalize(
			env,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		)?;
		let expected = self.normalize(
			assumption_context,
			expected,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
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
		let name = self.defs.constants[usize::from(constant)].name.inner;
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
