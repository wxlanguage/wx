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

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use super::bounds::{AssumptionEnvIdx, BoundArena, BoundClauses};
use super::defs::{AssocTypeIdx, ConstIdx, TraitIdx, TraitImplIdx};
use super::literals::ConcreteType;
use super::members::report_type_does_not_implement_trait;
use super::signatures::{ConstantSignature, TypeContext, TypeSetSignature};
use super::solver::{
	Definition, ImplMember, NormalizationDepth, ProjectionCycle, RewriteFlags,
	Solver, SolverError, Verdict,
};
use super::types::{
	GenericArgs, GenericEnvIdx, GenericEnvOwner, ImplKind, Substitution, Type,
	TypeIndex,
};
use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::vfs::FileId;

/// Requirements refer to their eventual bound table, so a provisional table
/// cannot lose inherited requirements that have not been published yet.
#[derive(Clone, Copy)]
pub(super) enum BoundRequirements {
	/// What `env`'s item states in its own assumption env, for a use that
	/// gives `args`, flat over `env`'s whole chain: a binding's value is
	/// written in the declaration, so it may name any of them. A failure is
	/// reported where the argument its clause is about is given.
	Frame {
		env: GenericEnvIdx,
		args: GenericArgs,
	},
	/// The declared bounds of `declaration`, a member of `trait_index`, whose
	/// `Self` is `receiver`.
	AssociatedType {
		declaration: AssocTypeIdx,
		trait_index: TraitIdx,
		receiver: TypeIndex,
		/// The value checked against them.
		value: TypeIndex,
	},
}

#[derive(Clone, Copy)]
pub(super) enum TypeObligation {
	CheckBounds {
		frame: GenericEnvIdx,
		requirements: BoundRequirements,
		reference: SourceSpan,
		owner: GenericEnvOwner,
	},
	CheckTraitMembership {
		frame: GenericEnvIdx,
		subject: TypeIndex,
		required: TraitIdx,
		reference: SourceSpan,
	},
	/// A written type is normalized once, so a cycle or an exhausted budget
	/// inside it is found even if nothing ever reads the type. The result is
	/// discarded: the stored type stays as written.
	CheckWellFormed {
		frame: GenericEnvIdx,
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
	/// A constant written in a type is representable as its type `ty`, as
	/// written: an array's length as its memory's `Size`. An abstract type is
	/// any member of the typesets its bounds name, so the value must be
	/// representable as every one of them, and the type works with each.
	CheckConstantRepresentable {
		frame: GenericEnvIdx,
		ty: TypeIndex,
		bits: u64,
		reference: SourceSpan,
	},
	/// A constant named in a type (an array's length) has exactly the type its
	/// position needs, `expected` as written: a constant of another type is a
	/// mismatch, even one whose value would be representable. Both types are
	/// compared normalized with every fact, so a constant either names is read;
	/// a constant's body therefore records it for after the values exist.
	CheckConstantType {
		frame: GenericEnvIdx,
		/// The `Type::Const` the length names.
		length: TypeIndex,
		expected: TypeIndex,
		reference: SourceSpan,
	},
	/// A type held by value (a parameter's, a result's, a function type's
	/// part, a local's) is a `StackValue`. A field, a tuple's element and a
	/// type argument need nothing: their container states what it needs.
	CheckValueType {
		frame: GenericEnvIdx,
		ty: TypeIndex,
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
		frame: GenericEnvIdx,
		projection: TypeIndex,
		name: SymbolU32,
		reference: SourceSpan,
	},
	/// A trait impl function's `Self` entry, `clauses` about the impl's
	/// target, is normalized into what the function assumes
	/// (`normalize_self_entry`). First in the function's run, so its other
	/// checks read the completed env; `reference` is the entry's `Self`.
	NormalizeSelfEntry {
		frame: GenericEnvIdx,
		clauses: BoundClauses,
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
				frame,
				requirements,
				reference,
				owner,
			} => match self.check_bound_requirements(
				self.assumption_envs.of_frame(frame),
				requirements,
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
				frame,
				subject,
				required,
				reference,
			} => {
				match self.find_trait_impl_query(
					self.assumption_envs.of_frame(frame),
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
				frame,
				ty,
				reference,
			} => {
				match self.normalize(
					self.assumption_envs.of_frame(frame),
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
			TypeObligation::CheckConstantRepresentable {
				frame,
				ty,
				bits,
				reference,
			} => match self.check_constant_representable(
				self.assumption_envs.of_frame(frame),
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
				frame,
				length,
				expected,
				reference,
			} => match self.check_constant_type(
				self.assumption_envs.of_frame(frame),
				length,
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
			TypeObligation::CheckValueType {
				frame,
				ty,
				reference,
			} => {
				match self.check_value_type(
					self.assumption_envs.of_frame(frame),
					ty,
					reference,
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
			// Reports everything but "not decided yet" itself.
			TypeObligation::CheckConformance { impl_index } => {
				self.check_conformance(impl_index).map_err(|_| ())
			}
			TypeObligation::NormalizeSelfEntry {
				frame,
				clauses,
				reference,
			} => match self.normalize_self_entry(frame, clauses) {
				Ok(()) => Ok(()),
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
			TypeObligation::CheckProjectionMember {
				frame,
				projection,
				name,
				reference,
			} => match self.check_projection_member(
				self.assumption_envs.of_frame(frame),
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
	/// `bits` is representable as `ty`: an integer type, or every member of
	/// every typeset an abstract one is bounded by.
	fn check_constant_representable(
		&mut self,
		assumption_context: AssumptionEnvIdx,
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
		for concrete in self.concrete_types(assumption_context, ty) {
			if concrete.holds_integer(i128::from(bits)).is_ok() {
				continue;
			}
			// A length's type is a memory's `Size`: an integer type, or the
			// members of `PointerSize`.
			let diagnostic = match concrete {
				ConcreteType::Member(typeset, member) => self
					.report_typeset_member(
						format_args!("`{bits}`"),
						typeset,
						member,
						reference,
					),
				ConcreteType::Target(_) => self.report_out_of_range(
					format_args!("`{bits}`"),
					ty,
					reference,
				),
			};
			self.diagnostics.push(diagnostic);
			return Err(SolverError::Poisoned);
		}
		Ok(())
	}

	/// `ty` may be held by value: it is a `StackValue`.
	fn check_value_type(
		&mut self,
		assumption_context: AssumptionEnvIdx,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		let Some(part) = self.non_stack_part(assumption_context, ty)? else {
			return Ok(());
		};
		self.diagnostics
			.push(self.not_stack_value_diagnostic(ty, part, reference));
		Err(SolverError::Poisoned)
	}

	/// `ty`, held by value at `reference`, is no `StackValue` because of
	/// `part` (`non_stack_part`).
	pub(super) fn not_stack_value_diagnostic(
		&self,
		ty: TypeIndex,
		part: TypeIndex,
		reference: SourceSpan,
	) -> Diagnostic<FileId> {
		let formatter = self.type_formatter();
		let (found, part_name) =
			(formatter.display_type(ty), formatter.display_type(part));
		let (label, note) = match self.types.resolve(part) {
			Type::Slice { .. } => (
				"a slice",
				format!(
					"`{part_name}` is a slice, which only a pointer holds, as \
					 `M::&{part_name}`"
				),
			),
			Type::Array { .. } => (
				"an array",
				format!(
					"`{part_name}` is an array, which only a pointer holds, \
					 as `M::&{part_name}`"
				),
			),
			_ => (
				"not a `StackValue`",
				format!(
					"`{part_name}` is not known to be a `StackValue`: \
					 require `{part_name}: StackValue`"
				),
			),
		};
		let message = if part == ty {
			format!("`{found}` cannot be held by value")
		} else {
			format!(
				"`{found}` cannot be held by value, since it holds \
				 `{part_name}`"
			)
		};
		Diagnostic::error()
			.with_code(DiagnosticCode::NotStackValue.code())
			.with_message(message)
			.with_label(reference.primary_label().with_message(label))
			.with_note(note)
	}

	/// The constant's type, in its own scope, is `expected`, in the scope
	/// the constant is named in.
	fn check_constant_type(
		&mut self,
		assumption_context: AssumptionEnvIdx,
		length: TypeIndex,
		expected: TypeIndex,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		let Type::Const {
			constant,
			type_args,
		} = *self.types.resolve(length)
		else {
			unreachable!("a length checked for its type names a constant")
		};
		let signature = &self.constants[usize::from(constant)];
		let (mut ty, frame) = (signature.ty, signature.env);
		let mut env = self.assumption_envs.of_frame(frame);
		// With its arguments, the declared type is read where it is named.
		if !type_args.is_empty() {
			let args: Box<[TypeIndex]> = self.types.list(type_args).into();
			ty = self.types.substitute(
				ty,
				Substitution {
					envs: &self.generic_envs,
					env: frame,
					args: &args,
				},
			);
			env = assumption_context;
		}
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
		// An untyped integer constant is a count: its value is representable as
		// the length's type, as a literal length's does.
		if found == TypeIndex::INTEGER_LITERAL {
			let Ok(value) = self.exact_value(constant) else {
				return Ok(());
			};
			return match u64::try_from(value) {
				Ok(bits) => self.check_constant_representable(
					assumption_context,
					expected,
					bits,
					reference,
				),
				Err(_) => {
					let message = format!(
						"an array's length is a count, but `{}` is `{value}`",
						self.strings
							.resolve(
								self.defs.constants[usize::from(constant)]
									.name
									.inner
							)
							.unwrap()
					);
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::IntegerLiteralOutOfRange.code(),
							)
							.with_message(message)
							.with_label(reference.primary_label()),
					);
					Err(SolverError::Poisoned)
				}
			};
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
