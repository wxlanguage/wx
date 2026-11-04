//! Trait-bound satisfaction: does a resolved type actually satisfy a
//! required trait? The question everything else that checks a bound —
//! impl-target validation, call-site type-argument checking, `where`-clause
//! verification — will eventually go through, once any of those exist.
//!
//! Concrete membership uses dispatch candidate discovery followed by full
//! impl-target matching. Abstract membership reads the same clauses as
//! normalization and member lookup. A bound's bindings are proven too: an
//! equality by comparing the normalized projection with the written value, a
//! nested bound on the projection. That proof is `Solver::satisfies_clauses`,
//! shared with impl selection; this module reports its failures. Impl
//! conformance (`conformance.rs`) proves an impl's associated values and its
//! target's supertraits through the same check.

use codespan_reporting::diagnostic::Diagnostic;

use super::bounds::{
	AssumptionEnvIdx, BoundClauses, BoundId, Clause, EqualityClause,
	RepresentableClause, TraitClause,
};
use string_interner::symbol::SymbolU32;

use super::defs::{BindingKey, DefKind, DefinitionRegistry, TraitIdx};
use super::impls::ImplTarget;
use super::members::{MemberLookup, report_no_such_type_member};
use super::obligations::{BoundRequirements, TypeObligation};
use super::signatures::{LexicalScope, TypeContext};
use super::solver::{
	NormalizationDepth, RewriteFlags, SolverError, Subjects, UnsatisfiedClause,
};
use super::types::{GenericArgs, GenericEnvIdx, Type, TypeIndex};
use crate::ast::{self, Keyword, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::bounds::{BindingRef, BindingRequirement};
use crate::tir::types::GenericEnvOwner;
use crate::vfs::FileId;

impl TypeContext<'_, '_, '_> {
	/// Records the check of `requirements` in `obligations`, for whoever
	/// lowers it to check. Construction never decides a bound: the argument
	/// is kept as written, and a failure is diagnosed later without
	/// rewriting it.
	pub(super) fn record_bounds_check(
		&mut self,
		obligations: &mut Vec<TypeObligation>,
		frame: GenericEnvIdx,
		requirements: BoundRequirements,
		reference: SourceSpan,
		owner: GenericEnvOwner,
	) {
		obligations.push(TypeObligation::CheckBounds {
			frame,
			requirements,
			reference,
			owner,
		});
	}

	/// Resolves a written type-argument list against `params_env`, `owner`'s
	/// own frame (`ROOT` when it declares no parameters). Always returns as
	/// many arguments as the frame declares. A wrong count is reported and makes every one `ERROR`:
	/// there is no sensible pairing to salvage, and the caller still sees a
	/// `Wrapper`, not a second "not a struct" error. Otherwise the arguments
	/// are kept as written, and the frame's bounds are recorded, each failure
	/// reported at the argument it is about, so `T: A + B` is two reports
	/// when an argument satisfies neither. `parent_args` are the arguments of
	/// the frames around `params_env`, outer first, which a bound may name;
	/// a failure about one is reported at the segment.
	pub(super) fn resolve_type_args(
		&mut self,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
		segment: &ast::PathSegment,
		params_env: GenericEnvIdx,
		parent_args: &[TypeIndex],
		args: &[TypeIndex],
		owner: GenericEnvOwner,
	) -> Box<[TypeIndex]> {
		if !self.check_type_arg_count(scope, segment, params_env, owner) {
			let expected = self.generic_envs.param_names(params_env).len();
			return vec![TypeIndex::ERROR; expected].into_boxed_slice();
		}
		if params_env == GenericEnvIdx::ROOT {
			return Box::new([]);
		}
		debug_assert_eq!(
			parent_args.len(),
			self.generic_envs.parent_count(params_env),
			"a bound is substituted over the frame's whole chain"
		);
		let parents = parent_args.iter().map(|&ty| (ty, segment.ident.span));
		let written = segment.type_args.iter().map(|written| written.span());
		let generic_args = self
			.generic_args
			.push(parents.chain(args.iter().copied().zip(written)));
		self.record_bounds_check(
			obligations,
			scope.generic_env,
			BoundRequirements::Frame {
				env: params_env,
				args: generic_args,
			},
			SourceSpan::new(scope.file_id, segment.ident.span),
			owner,
		);
		args.into()
	}

	/// Whether `segment` writes as many type arguments as `params_env`
	/// declares; reports the mismatch when it does not.
	pub(super) fn check_type_arg_count(
		&mut self,
		scope: LexicalScope,
		segment: &ast::PathSegment,
		params_env: GenericEnvIdx,
		owner: GenericEnvOwner,
	) -> bool {
		let expected = self.generic_envs.param_names(params_env).len();
		if segment.type_args.len() == expected {
			return true;
		}
		self.diagnostics.push(report_type_arg_count_mismatch(
			self.strings,
			self.defs,
			scope.file_id,
			segment,
			owner,
			self.generic_envs.param_names(params_env),
		));
		false
	}
}

/// The checks bound satisfaction owns, run by the declaration check.
impl TypeContext<'_, '_, '_> {
	/// Completes `frame`'s env with what its `Self` entry, `clauses` about a
	/// trait impl's target, means (`normalize_clauses`). What is not about an
	/// abstract type is proved there and dropped. One that does not hold is
	/// reported at its bound: an error without a parameter (`Bytes: Show`
	/// never holds), and unsupported with one (`Wrap<T>: Show` would be an
	/// assumption about a type that is not abstract, which lookup never
	/// reads).
	pub(super) fn normalize_self_entry(
		&mut self,
		frame: GenericEnvIdx,
		clauses: BoundClauses,
	) -> Result<(), SolverError> {
		let env = self.assumption_envs.of_frame(frame);
		let (assumed, proved) = self.normalize_clauses(env, clauses)?;
		let arguments: Box<[TypeIndex]> =
			self.generic_envs.identity_args(frame).into();
		let mut failures = Vec::new();
		self.satisfies_clauses(
			env,
			proved,
			Subjects::All,
			(frame, &arguments),
			Some(&mut failures),
			None,
		)?;
		let owner = self.generic_envs.owner(frame);
		for failure in failures {
			let diagnostic = match failure {
				UnsatisfiedClause::Trait {
					subject,
					reduced,
					trait_index,
					source,
					..
				} => {
					let at = self.bounds.span(source);
					if self.types.has_param(reduced) {
						let trait_name = self.defs.traits
							[usize::from(trait_index)]
						.name
						.inner;
						let clause = format!(
							"{}: {}",
							self.type_formatter().display_type(reduced),
							self.strings.resolve(trait_name).unwrap()
						);
						report_unassumable_clause(at, &clause)
					} else {
						self.report_trait_bound_violation(
							at.file_id,
							Spanned {
								inner: (subject, reduced),
								span: at.span,
							},
							trait_index,
							source,
							owner,
						)
					}
				}
				UnsatisfiedClause::Equality {
					projection,
					required,
					found,
					expected,
					source,
					..
				} => {
					let at = self.binding_span(source);
					if self.types.has_param(found)
						|| self.types.has_param(expected)
					{
						self.report_unassumable_equality(
							at, projection, found, expected,
						)
					} else {
						self.report_equality_mismatch(
							at,
							(projection, required),
							found,
							expected,
							source,
							owner,
						)
					}
				}
				UnsatisfiedClause::Representable {
					subject,
					constant,
					ty,
					value,
					source,
					..
				} => {
					let at = self.binding_span(source);
					match value {
						Some(_) => self.report_unrepresentable_constant(
							at,
							(subject, constant),
							ty,
							value,
							None,
						),
						None => {
							let read =
								self.types.intern_const(constant, &[subject]);
							let formatter = self.type_formatter();
							let clause = format!(
								"{} is representable as {}",
								formatter.display_type(read),
								formatter.display_type(ty)
							);
							report_unassumable_clause(at, &clause)
						}
					}
				}
			};
			self.diagnostics.push(diagnostic);
		}

		if !assumed.is_empty() {
			let completed = self.assumption_envs.push(env, None);
			*self.assumption_envs.clauses_mut(completed) = assumed;
			self.assumption_envs.complete_frame(frame, completed);
		}
		Ok(())
	}

	/// An equality a `Self` entry states that holds only for some of the
	/// impl's arguments (`Item = u8` where `Item` is `T`): assuming it would
	/// make a parameter equal a type, which no assumption can state.
	fn report_unassumable_equality(
		&self,
		at: SourceSpan,
		projection: TypeIndex,
		found: TypeIndex,
		expected: TypeIndex,
	) -> Diagnostic<FileId> {
		let formatter = self.type_formatter();
		let (projection, found, expected) = (
			formatter.display_type(projection),
			formatter.display_type(found),
			formatter.display_type(expected),
		);
		Diagnostic::error()
			.with_code(DiagnosticCode::UnassumableEquality.code())
			.with_message(format!(
				"`{projection}` is `{found}`, which a bound cannot require to \
				 be `{expected}`"
			))
			.with_label(
				at.primary_label().with_message(format!(
					"would require `{found} == {expected}`"
				)),
			)
			.with_note(
				"an equality is assumed only about an associated type of a \
				 parameter (`T::Item = u8`), never about a parameter itself",
			)
	}

	/// Where the equality or representability clause `source` is written: from
	/// its name to its value or type (`Item = u8`, `LEN: u8`).
	pub(super) fn binding_span(&self, source: BindingRef) -> SourceSpan {
		let binding = self.bounds.binding(source);
		let (BindingRequirement::Equals(_, value)
		| BindingRequirement::Representable(_, value)) = &binding.kind
		else {
			unreachable!(
				"an equality's or a representability clause's binding states a type"
			)
		};
		SourceSpan::new(
			self.bounds.span(source.bound).file_id,
			TextSpan::new(binding.name.span.start, value.span.end),
		)
	}

	/// `clauses`, about types (a `Self` entry's, read in a trait impl),
	/// normalized in `env`: those that now read about an abstract type, as
	/// they read, which is what assuming them means; then the rest, as
	/// written, which holds or not of its own and assumes nothing.
	pub(super) fn normalize_clauses(
		&mut self,
		env: AssumptionEnvIdx,
		clauses: BoundClauses,
	) -> Result<(BoundClauses, BoundClauses), SolverError> {
		let Some(range) = clauses.final_range() else {
			unreachable!("normalized clauses are final")
		};
		let (mut assumed, mut other) = (Vec::new(), Vec::new());
		// Read one clause at a time: normalizing interns, and the arena only
		// grows, so the range stays valid.
		for at in 0..range.len() {
			let clause = self.clauses.get(range)[at];
			let normalized = match clause {
				Clause::Trait(clause) => {
					let subject = self.normalize(
						env,
						clause.subject,
						NormalizationDepth::Deep,
						RewriteFlags::ALL,
					)?;
					self.types.is_abstract(subject).then_some(Clause::Trait(
						TraitClause { subject, ..clause },
					))
				}
				Clause::Equality(clause) => {
					let projection = self.normalize(
						env,
						clause.projection,
						NormalizationDepth::Deep,
						RewriteFlags::ALL,
					)?;
					if matches!(
						self.types.resolve(projection),
						Type::TypeProjection { .. }
					) && self.types.is_abstract(projection)
					{
						let value = self.normalize(
							env,
							clause.value,
							NormalizationDepth::Deep,
							RewriteFlags::ALL,
						)?;
						Some(Clause::Equality(EqualityClause {
							projection,
							value,
							..clause
						}))
					} else {
						None
					}
				}
				Clause::Representable(clause) => {
					let subject = self.normalize(
						env,
						clause.subject,
						NormalizationDepth::Deep,
						RewriteFlags::ALL,
					)?;
					if self.types.is_abstract(subject) {
						let ty = self.normalize(
							env,
							clause.ty,
							NormalizationDepth::Deep,
							RewriteFlags::ALL,
						)?;
						Some(Clause::Representable(RepresentableClause {
							subject,
							ty,
							..clause
						}))
					} else {
						None
					}
				}
			};
			match normalized {
				Some(normalized) => assumed.push(normalized),
				None => other.push(clause),
			}
		}
		Ok((
			BoundClauses::Final(self.clauses.push(&assumed)),
			BoundClauses::Final(self.clauses.push(&other)),
		))
	}

	/// Gather violations before emitting them: another requirement can still
	/// be pending, and a retry must not duplicate a diagnostic.
	pub(super) fn check_bound_requirements(
		&mut self,
		assumption_context: AssumptionEnvIdx,
		requirements: BoundRequirements,
		reference: SourceSpan,
		owner: GenericEnvOwner,
	) -> Result<(), SolverError> {
		// The clauses are written in the declaration's frame, about its own
		// subject; the use supplies that frame's arguments and the subject.
		// The arguments are owned: the proof interns while it reads them.
		let (clauses, subjects, frame, arguments): (_, _, _, Box<[TypeIndex]>) =
			match requirements {
				BoundRequirements::Frame { env, args } => (
					self.assumption_envs.requirements(env),
					Subjects::All,
					env,
					self.generic_args.types(args).into(),
				),
				BoundRequirements::AssociatedType {
					declaration,
					trait_index,
					receiver,
					value,
				} => {
					let Some(signature) =
						&self.assoc_types[usize::from(declaration)]
					else {
						return Err(SolverError::Pending);
					};
					let env = self.traits[usize::from(trait_index)].env;
					let root = self.types.intern(Type::TypeProjection {
						base: self.generic_envs.param_types(env)[0],
						trait_index,
						assoc_type_index: declaration,
					});
					(
						signature.clauses,
						Subjects::Rooted {
							root,
							subject: value,
						},
						env,
						Box::new([receiver]),
					)
				}
			};
		let mut failures = Vec::new();
		if self.satisfies_clauses(
			assumption_context,
			clauses,
			subjects,
			(frame, &arguments),
			Some(&mut failures),
			None,
		)? {
			return Ok(());
		}
		for failure in failures {
			let at = match requirements {
				BoundRequirements::Frame { args, .. } => {
					self.argument_span(args, failure.written())
				}
				BoundRequirements::AssociatedType { .. } => None,
			}
			.unwrap_or(reference.span);
			let diagnostic = match failure {
				UnsatisfiedClause::Trait {
					subject,
					reduced,
					trait_index,
					source,
					..
				} => self.report_trait_bound_violation(
					reference.file_id,
					Spanned {
						inner: (subject, reduced),
						span: at,
					},
					trait_index,
					source,
					owner,
				),
				UnsatisfiedClause::Equality {
					projection,
					required,
					found,
					expected,
					source,
					..
				} => self.report_equality_mismatch(
					SourceSpan::new(reference.file_id, at),
					(projection, required),
					found,
					expected,
					source,
					owner,
				),
				UnsatisfiedClause::Representable {
					subject,
					constant,
					ty,
					value,
					source,
					..
				} => self.report_unrepresentable_constant(
					SourceSpan::new(reference.file_id, at),
					(subject, constant),
					ty,
					value,
					Some((source, owner)),
				),
			};
			self.diagnostics.push(diagnostic);
		}
		Err(SolverError::Poisoned)
	}

	/// Where `args` gives the parameter `written`, a clause's subject, is
	/// rooted at (`T` for `<T as Tr>::A`); `None` for a path out of a
	/// concrete type.
	fn argument_span(
		&self,
		args: GenericArgs,
		mut written: TypeIndex,
	) -> Option<TextSpan> {
		let (env, param_index) = loop {
			match *self.types.resolve(written) {
				Type::TypeParam { env, param_index } => {
					break (env, param_index);
				}
				Type::TypeProjection { base, .. } => written = base,
				_ => return None,
			}
		};
		let slot = self.generic_envs.parent_count(env) + param_index as usize;
		Some(self.generic_args.spans(args)[slot])
	}

	/// `projection::name` could not be selected from the projection's declared
	/// bounds. Resolve what the projection's value is and which traits could
	/// supply `name` on it, as rustc does to build its suggestion. Selecting
	/// through an impl unqualified is ambiguous by design, so a trait that
	/// *would* work is still an error, but one that says how to write it.
	/// Always fails: the lowered type was `ERROR`.
	pub(super) fn check_projection_member(
		&mut self,
		assumption_context: AssumptionEnvIdx,
		projection: TypeIndex,
		name: SymbolU32,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		let key = BindingKey::ty(name);
		let ident = Spanned {
			inner: name,
			span: reference.span,
		};
		let declared_anywhere = (0..self.defs.traits.len()).any(|index| {
			self.defs
				.declared_trait_member(TraitIdx::new(index as u32), key)
				.is_some()
		});
		let normalized = match self.normalize(
			assumption_context,
			projection,
			NormalizationDepth::Shallow,
			RewriteFlags::ALL,
		) {
			Ok(normalized) => normalized,
			// The projection has no value (an impl omits it, or its own
			// requirement failed); that is reported where it belongs. Only a
			// name no trait declares is certainly wrong.
			Err(SolverError::Poisoned) => {
				if !declared_anywhere {
					self.diagnostics.push(report_no_such_type_member(
						reference.file_id,
						self.strings,
						ident,
						"associated type",
					));
				}
				return Err(SolverError::Poisoned);
			}
			Err(error) => return Err(error),
		};
		// Each source names a trait at most once: the dispatch index holds one
		// impl per trait per type constructor, and `declared_bound_member` skips
		// a trait it has already collected.
		let mut traits: Vec<TraitIdx> = Vec::new();
		match ImplTarget::from_type(self.types.resolve(normalized)) {
			Some(target) => {
				for trait_index in self.trait_candidates(target) {
					if self
						.defs
						.declared_trait_member(trait_index, key)
						.is_some()
					{
						traits.push(trait_index);
					}
				}
			}
			// Every signature exists, so the bounds are ready to read.
			None if matches!(
				self.types.resolve(normalized),
				Type::TypeParam { .. } | Type::TypeProjection { .. }
			) =>
			{
				let declared = self.clause_tables().declared_traits(
					&self.types,
					assumption_context,
					normalized,
					self.solver.state.recursion_budget,
				);
				match TypeContext::select_declared_member(
					self.defs, declared, key,
				) {
					MemberLookup::Found(member) => {
						traits.extend(
							member.type_declaration().map(|d| d.trait_index),
						);
					}
					MemberLookup::Ambiguous(members) => {
						traits.extend(members.iter().filter_map(|member| {
							member.type_declaration().map(|d| d.trait_index)
						}));
					}
					_ => {}
				}
			}
			None => {}
		}
		if traits.is_empty() {
			self.diagnostics.push(report_no_such_type_member(
				reference.file_id,
				self.strings,
				ident,
				"associated type",
			));
			return Err(SolverError::Poisoned);
		}
		let name_str = self.strings.resolve(name).unwrap().to_string();
		let receiver = self.type_formatter().display_type(projection);
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::TypeMemberNeedsQualification.code())
			.with_message(format!("ambiguous associated type `{name_str}`"))
			.with_label(reference.primary_label().with_message(format!(
				"`{receiver}` is known only through an impl, so the trait must be named"
			)));
		for trait_index in traits {
			let trait_name = self
				.strings
				.resolve(self.defs.traits[usize::from(trait_index)].name.inner)
				.unwrap();
			diagnostic = diagnostic.with_note(format!(
				"qualify the trait: `<{receiver} as {trait_name}>::{name_str}`"
			));
		}
		self.diagnostics.push(diagnostic);
		Err(SolverError::Poisoned)
	}

	/// The message states the clause with the use's arguments; the label
	/// names the type it reduces to, which lacks the trait.
	fn report_trait_bound_violation(
		&self,
		file_id: FileId,
		argument: Spanned<(TypeIndex, TypeIndex)>,
		trait_index: TraitIdx,
		bound_id: BoundId,
		owner: GenericEnvOwner,
	) -> Diagnostic<FileId> {
		let formatter = self.type_formatter();
		let (subject, reduced) = argument.inner;
		let (subject, reduced) = (
			formatter.display_type(subject),
			formatter.display_type(reduced),
		);
		let trait_name = self
			.strings
			.resolve(self.defs.traits[usize::from(trait_index)].name.inner)
			.unwrap();
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitBoundViolation.code())
			.with_message(format!(
				"the trait bound `{subject}: {trait_name}` is not satisfied"
			))
			.with_label(
				SourceSpan::new(file_id, argument.span)
					.primary_label()
					.with_message(format!(
						"the trait `{trait_name}` is not implemented for `{reduced}`"
					)),
			)
			.with_label(
				self.bounds.span(bound_id).secondary_label().with_message(
					// An impl has no name to point at; its bound is shown.
					match owner.name(self.defs) {
						Some(name) => format!(
							"required by a bound in `{}`",
							self.strings.resolve(name.inner).unwrap()
						),
						None => "required by this bound".to_owned(),
					},
				),
			)
	}

	/// rustc's E0271: the projection a bound's equality names has another
	/// value. The message states the equality with the use's arguments, the
	/// label what its two sides reduce to, and the written equality is shown,
	/// since that is what the value failed.
	fn report_equality_mismatch(
		&self,
		reference: SourceSpan,
		(projection, required): (TypeIndex, TypeIndex),
		found: TypeIndex,
		expected: TypeIndex,
		source: BindingRef,
		owner: GenericEnvOwner,
	) -> Diagnostic<FileId> {
		let formatter = self.type_formatter();
		let (projection, required, found, expected) = (
			formatter.display_type(projection),
			formatter.display_type(required),
			formatter.display_type(found),
			formatter.display_type(expected),
		);
		let ast::Spanned { span, .. } = match self.bounds.binding(source).kind {
			BindingRequirement::Equals(_, value) => value,
			BindingRequirement::Bound(..)
			| BindingRequirement::Representable(..) => {
				unreachable!("an equality clause comes from a written equality")
			}
		};
		let written =
			SourceSpan::new(self.bounds.span(source.bound).file_id, span);
		Diagnostic::error()
			.with_code(DiagnosticCode::AssocTypeEqualityMismatch.code())
			.with_message(format!(
				"type mismatch resolving `{projection} == {required}`"
			))
			.with_label(reference.primary_label().with_message(format!(
				"expected `{expected}`, found `{found}`"
			)))
			.with_label(written.secondary_label().with_message(
				match owner.name(self.defs) {
					Some(name) => format!(
						"required by this equality in `{}`",
						self.strings.resolve(name.inner).unwrap()
					),
					None => "required by this equality".to_owned(),
				},
			))
	}
}

/// What a path segment written with type arguments names when it can
/// never declare parameters. An impl's `Self` has its own report, which
/// shows the target the impl names.
pub(super) enum TypeArgsNotAllowedOn<'a> {
	/// A namespace a path passes through, an enum, a global, a memory, an
	/// associated type or an intrinsic type alias.
	Declaration(DefKind),
	/// A generic parameter or a trait's `Self`, and the declaration whose
	/// frame declares it.
	TypeParam {
		owner: GenericEnvOwner,
		name: &'a Spanned<SymbolU32>,
	},
}

/// Type arguments on a name that never takes any, as opposed to a wrong
/// count for one that declares a parameter list.
pub(super) fn report_type_args_not_allowed(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	file_id: FileId,
	segment: &ast::PathSegment,
	target: TypeArgsNotAllowedOn<'_>,
) -> Diagnostic<FileId> {
	let (noun, declared_at) = match target {
		TypeArgsNotAllowedOn::Declaration(kind) => {
			(kind.noun(), kind.declared_at(defs))
		}
		TypeArgsNotAllowedOn::TypeParam { owner, name } => (
			if name.inner == Keyword::SelfPascal.symbol() {
				"self type"
			} else {
				"type parameter"
			},
			Some(SourceSpan::new(owner.file_id(defs), name.span)),
		),
	};
	let name = strings.resolve(segment.ident.inner).unwrap();
	let (first, last) = (
		segment.type_args.first().unwrap(),
		segment.type_args.last().unwrap(),
	);
	let mut labels = vec![
		SourceSpan::new(
			file_id,
			TextSpan::new(first.span().start, last.span().end),
		)
		.primary_label()
		.with_message(format!(
			"type argument{} not allowed",
			if segment.type_args.len() == 1 {
				""
			} else {
				"s"
			}
		)),
		SourceSpan::new(file_id, segment.ident.span)
			.secondary_label()
			.with_message(format!("not allowed on {noun} `{name}`")),
	];
	if let Some(declared_at) = declared_at {
		labels.push(
			declared_at
				.secondary_label()
				.with_message(format!("{noun} `{name}` defined here")),
		);
	}
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeArgumentsNotAllowed.code())
		.with_message(format!(
			"type arguments are not allowed on {noun} `{name}`"
		))
		.with_labels(labels)
		.with_note(format!(
			"{noun} `{name}` has no generic parameters; write `{name}` alone"
		))
}

/// A wrong number of type arguments for a declaration with its own
/// parameter list, possibly empty: a struct, a function or a type alias.
fn report_type_arg_count_mismatch(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	file_id: FileId,
	segment: &ast::PathSegment,
	owner: GenericEnvOwner,
	params: &[Spanned<SymbolU32>],
) -> Diagnostic<FileId> {
	let (noun, name) = (owner.noun(), segment.ident.inner);
	let declaration = owner.name(defs).map(|declared| {
		(SourceSpan::new(owner.file_id(defs), declared.span), params)
	});
	let args = &segment.type_args;
	let params = declaration.map_or(&[][..], |(_, params)| params);
	let expected = params.len();
	let found = args.len();
	let plural = |n: usize| if n == 1 { "" } else { "s" };

	let mut labels = vec![
		SourceSpan::new(file_id, segment.ident.span)
			.primary_label()
			.with_message(format!(
				"expected {expected} generic argument{}",
				plural(expected)
			)),
	];
	for (index, arg) in args.iter().enumerate() {
		let label = SourceSpan::new(file_id, arg.span()).secondary_label();
		labels.push(if index + 1 == args.len() {
			if expected == 0 {
				label.with_message("remove the unnecessary generics")
			} else {
				label.with_message(format!(
					"supplied {found} generic argument{}",
					plural(found)
				))
			}
		} else {
			label
		});
	}

	if let Some((declared_at, params)) = declaration {
		labels.push(declared_at.secondary_label().with_message(format!(
			"{noun} defined here, with {expected} generic parameter{}",
			plural(expected)
		)));
		for param in params {
			labels.push(
				SourceSpan::new(declared_at.file_id, param.span)
					.secondary_label(),
			);
		}
	}

	let name = strings.resolve(name).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeArgumentCountMismatch.code())
		.with_message(format!(
			"{noun} `{name}` takes {expected} generic argument{} but {found} generic argument{} {} supplied",
			plural(expected),
			plural(found),
			if found == 1 { "was" } else { "were" },
		))
		.with_labels(labels)
}

#[cfg(test)]
mod tests {

	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned};
	use crate::diagnostics::TextSpan;
	use crate::tir::defs::{DefKind, DefinitionRegistry, Scope, Tier};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::paths::PathResolver;
	use crate::tir::resolutions::NameResolutions;
	use crate::tir::signatures::tests::source_graph;
	use crate::tir::solver::Solver;
	use crate::tir::types::Type;

	/// Parses `source` over the embedded stdlib, sweeps every registered
	/// item's signature, then hands the live `TypeContext` to `f`. Nothing
	/// borrowed here (`graph`, `defs`, `ast_nodes`, `diagnostics`) may escape
	/// this call; only `f`'s own, owned return value does.
	fn with_resolved<R>(
		source: &str,
		f: impl FnOnce(&mut TypeContext) -> R,
	) -> R {
		let mut graph = source_graph(source);

		let mut diagnostics = Vec::new();
		let mut resolutions = NameResolutions::default();
		let (defs, ast_nodes) = DefinitionRegistry::build(
			&graph.packages,
			&graph.files,
			&mut graph.strings,
			&mut diagnostics,
			&mut resolutions,
			graph.stdlib_package,
			graph.root_package,
		);
		let impl_dispatch = ImplDispatch::build(
			&mut diagnostics,
			&mut resolutions,
			&graph.strings,
			&defs,
			&ast_nodes,
		);
		let mut solver = Solver::new(defs.constants.len());
		let mut builder = TypeContext::new(
			&mut diagnostics,
			&mut resolutions,
			&mut graph.strings,
			&mut solver,
			&graph.files,
			&defs,
			&ast_nodes,
			&impl_dispatch,
		);
		builder.sweep();
		assert!(builder.diagnostics.is_empty(), "{:?}", builder.diagnostics);

		f(&mut builder)
	}

	/// Resolves `path` (`::`-separated) as a `tier`-tier path from the root
	/// namespace — same mechanism a written bound or type actually uses,
	/// mirroring `signatures::tests::TestCase::resolve`.
	fn resolve(builder: &TypeContext, tier: Tier, path: &str) -> DefKind {
		let root = Scope::Package(builder.defs.root_package);
		let file_id = builder.defs.namespaces.file_id(root.into());

		let segments: Box<[ast::PathSegment]> = path
			.split("::")
			.map(|segment| ast::PathSegment {
				ident: Spanned {
					inner: builder
						.strings
						.get(segment)
						.expect("already interned from source"),
					span: TextSpan::new(0, 0),
				},
				type_args: Box::new([]),
			})
			.collect();
		let mut diagnostics = Vec::new();
		let mut resolutions = NameResolutions::default();
		let target = PathResolver::new(
			&mut diagnostics,
			&mut resolutions,
			builder.strings,
			builder.defs,
		)
		.resolve_path(file_id, root, &segments, tier);
		target
			.def_key()
			.unwrap_or_else(|| {
				panic!("expected `{path}` to resolve: {diagnostics:?}")
			})
			.symbol_kind(builder.defs)
	}

	fn trait_index(builder: &TypeContext, path: &str) -> TraitIdx {
		let DefKind::Trait(trait_index) = resolve(builder, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a trait");
		};
		trait_index
	}

	/// The `TraitIndex` of `path`'s compiler-generated backing trait — what
	/// a `T: <path>` bound naming this typeset actually resolves to. See
	/// `TypeSetSignature`'s own doc comment.
	fn typeset_trait_index(builder: &TypeContext, path: &str) -> TraitIdx {
		let DefKind::TypeSet(typeset_index) =
			resolve(builder, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a typeset");
		};
		builder.defs.typesets[usize::from(typeset_index)].trait_index
	}

	/// `path`'s own `TypeIndex` — a non-generic struct only(a generic
	/// struct's instantiated `TypeIndex` needs type-argument resolution,
	/// which isn't implemented yet — see `impls.rs::resolve_impl_target`).
	fn struct_type(builder: &mut TypeContext, path: &str) -> TypeIndex {
		let DefKind::Struct(struct_index) = resolve(builder, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a struct");
		};
		builder.types.intern_struct(struct_index, &[])
	}

	/// The `TypeIndex` of `function_path`'s `param_index`-th own declared
	/// generic parameter — e.g. the `T` in `func target<T: Bound>(x: T)`.
	/// Declaring the type under test as a generic function's own type
	/// parameter, rather than reading a resolved parameter type back out of
	/// `FunctionSignature` (private to `signatures.rs` — nothing outside it
	/// needs a function's own resolved types yet), is what lets this same
	/// harness reach a `TypeParam` receiver without a wider accessor.
	/// Where `param` is declared: the assumptions of its own declaration.
	fn param_scope(
		builder: &TypeContext,
		param: TypeIndex,
	) -> AssumptionEnvIdx {
		let Type::TypeParam { env, .. } = *builder.types.resolve(param) else {
			panic!("expected a type parameter");
		};
		builder.assumption_envs.of_frame(env)
	}

	fn generic_param_type(
		builder: &mut TypeContext,
		function_path: &str,
		param_index: u32,
	) -> TypeIndex {
		let DefKind::Function(function_index) =
			resolve(builder, Tier::Value, function_path)
		else {
			panic!("expected `{function_path}` to be a function");
		};
		let env = builder.functions[usize::from(function_index)].type_params;
		builder.types.intern(Type::TypeParam { env, param_index })
	}

	#[test]
	fn error_and_infer_are_recovery_not_proofs() {
		with_resolved(
			indoc! {"
			trait Foo {}
		"},
			|builder| {
				let foo = trait_index(builder, "Foo");
				assert!(
					(builder
						.find_trait_impl_query(
							AssumptionEnvIdx::ROOT,
							TypeIndex::ERROR,
							foo
						)
						.map(|found| found.is_some())
						== Err(SolverError::Poisoned))
				);
				assert!(
					(builder
						.find_trait_impl_query(
							AssumptionEnvIdx::ROOT,
							TypeIndex::INFER,
							foo
						)
						.map(|found| found.is_some())
						== Err(SolverError::Poisoned))
				);
			},
		);
	}

	#[test]
	fn a_struct_with_a_matching_impl_satisfies_the_trait() {
		with_resolved(
			indoc! {"
				trait Foo {}
				struct S();
				impl Foo for S {}
			"},
			|builder| {
				let foo = trait_index(builder, "Foo");
				let s = struct_type(builder, "S");
				assert!(
					(builder
						.find_trait_impl_query(AssumptionEnvIdx::ROOT, s, foo)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_struct_with_no_impl_does_not_satisfy_the_trait() {
		with_resolved(
			indoc! {"
				trait Foo {}
				trait Bar {}
				struct S();
				impl Foo for S {}
			"},
			|builder| {
				let bar = trait_index(builder, "Bar");
				let s = struct_type(builder, "S");
				assert!(
					!(builder
						.find_trait_impl_query(AssumptionEnvIdx::ROOT, s, bar)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_struct_listed_in_a_typeset_satisfies_its_backing_trait() {
		with_resolved(
			indoc! {"
				struct S();
				typeset Nums { S }
			"},
			|builder| {
				let nums = typeset_trait_index(builder, "Nums");
				let s = struct_type(builder, "S");
				assert!(
					(builder
						.find_trait_impl_query(AssumptionEnvIdx::ROOT, s, nums)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_with_a_matching_bound_satisfies_the_trait() {
		with_resolved(
			indoc! {"
				trait Bound {}
				func target<T: Bound + StackValue>(x: T) {}
			"},
			|builder| {
				let bound = trait_index(builder, "Bound");
				let t = generic_param_type(builder, "target", 0);
				assert!(
					(builder
						.find_trait_impl_query(
							param_scope(builder, t),
							t,
							bound
						)
						.map(|found| found.is_some())
						== Ok(true))
				);
				// Outside `target` its bounds are not assumed.
				assert_eq!(
					builder
						.find_trait_impl_query(AssumptionEnvIdx::ROOT, t, bound)
						.map(|found| found.is_some()),
					Ok(false)
				);
			},
		);
	}

	#[test]
	fn a_generic_param_without_the_bound_does_not_satisfy_the_trait() {
		with_resolved(
			indoc! {"
				trait Bound {}
				trait Other {}
				func target<T: Bound + StackValue>(x: T) {}
			"},
			|builder| {
				let other = trait_index(builder, "Other");
				let t = generic_param_type(builder, "target", 0);
				assert!(
					!(builder
						.find_trait_impl_query(
							param_scope(builder, t),
							t,
							other
						)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_satisfies_a_bounds_supertrait_transitively() {
		with_resolved(
			indoc! {"
				trait Super {}
				trait Sub: Super {}
				func target<T: Sub + StackValue>(x: T) {}
			"},
			|builder| {
				let super_trait = trait_index(builder, "Super");
				let t = generic_param_type(builder, "target", 0);
				assert!(
					(builder
						.find_trait_impl_query(
							param_scope(builder, t),
							t,
							super_trait
						)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}
}

/// A `Self` entry's clause that normalizes to a statement about a type with a
/// parameter that is not abstract, which no lookup would read.
fn report_unassumable_clause(
	at: SourceSpan,
	clause: &str,
) -> Diagnostic<FileId> {
	Diagnostic::bug()
		.with_code(DiagnosticCode::UnsupportedExpression.code())
		.with_message(format!("assuming `{clause}` is not supported yet"))
		.with_label(at.primary_label().with_message(
			"a bound on `Self` here is assumed only about a parameter or a \
			 projection out of one",
		))
}
