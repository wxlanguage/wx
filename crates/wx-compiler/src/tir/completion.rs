//! Each frame's completed env: its clauses, and the clauses in scope around
//! it, rewritten by the equalities in scope once every signature exists
//! (`notes/member-selection-and-equalities.md`, decision 2). Construction and
//! path selection read the written env; everything after construction reads
//! this one.

use super::bounds::{
	AssumptionEnvIdx, BoundClauses, Clause, ClauseRange, EqualityClause,
	FrameCompletion, RepresentableClause, TraitClause, push_trait_clause,
};
use super::signatures::Semantics;
use super::solver::{NormalizationDepth, RewriteFlags, SolverError};
use super::types::{GenericEnvIdx, Type, TypeIndex};
use crate::ast::StringInterner;
use crate::diagnostics::SourceSpan;

/// The clauses a completed env holds, and the written clauses it proves
/// instead of assuming.
#[derive(Default)]
struct Completed {
	traits: Vec<TraitClause>,
	values: Vec<Clause>,
	/// Written clauses not about an abstract type once rewritten: each holds
	/// or not of its own, and is proved at its bound.
	proved: Vec<Clause>,
	/// Whether any clause reads differently than written, so the written
	/// env no longer says what the frame assumes.
	rewritten: bool,
}

/// What a frame's clauses are rewritten against.
#[derive(Clone, Copy)]
struct Rewrite {
	frame: GenericEnvIdx,
	/// The frame's rules as written over its parent's completed env: every
	/// rule in scope.
	rules: AssumptionEnvIdx,
	/// The parent's completed env: what an equality of the frame's own is
	/// read in when it is about anything but the frame's own parameters, so
	/// a rule never rewrites itself.
	parent_env: AssumptionEnvIdx,
}

/// Where a clause comes from, which decides what rewrites it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Origin {
	/// Already completed in the parent: only the frame's rules rewrite it.
	Inherited,
	/// Written on the frame.
	Own,
	/// Lent by an associated type's declared bounds through an equality:
	/// read whole with every rule in scope.
	Lent,
}

impl Semantics {
	/// `frame`'s completed env: asks for its parent's first, then rewrites
	/// what `frame` states, once; a frame read again later gets the same env.
	/// Asked once every signature exists, so nothing it normalizes is
	/// `Pending`.
	pub(super) fn completed_env(
		&mut self,
		strings: &StringInterner,
		frame: GenericEnvIdx,
	) -> AssumptionEnvIdx {
		match self.assumption_envs.completion(frame) {
			FrameCompletion::Completed(env) => return env,
			FrameCompletion::Rewriting { rules } => return rules,
			FrameCompletion::Unasked => {}
		}
		let parent = self
			.generic_envs
			.parent(frame)
			.expect("the root frame is complete from the start");
		let parent_env = self.completed_env(strings, parent);
		let env = self.complete_frame(strings, frame, parent, parent_env);
		self.assumption_envs
			.set_completion(frame, FrameCompletion::Completed(env));
		env
	}

	/// Completes every frame not asked for yet, so readers that run after
	/// declarations are checked find each complete.
	pub(super) fn complete_every_frame(&mut self, strings: &StringInterner) {
		for frame in 0..self.assumption_envs.frame_count() {
			let frame = GenericEnvIdx::new(u32::try_from(frame).unwrap());
			self.completed_env(strings, frame);
		}
	}

	/// A frame that adds no facts reuses `parent_env`; one in whose scope
	/// nothing rewrites keeps its written env; any other gets a flat env
	/// holding every clause in scope, rewritten.
	fn complete_frame(
		&mut self,
		strings: &StringInterner,
		frame: GenericEnvIdx,
		parent: GenericEnvIdx,
		parent_env: AssumptionEnvIdx,
	) -> AssumptionEnvIdx {
		let written = self.assumption_envs.written(frame);
		let Some(own) = self.assumption_envs.requirements(frame).final_range()
		else {
			unreachable!("requirements are final once every signature exists")
		};
		if own.len() == 0 {
			return parent_env;
		}
		let parent_written = self.assumption_envs.written(parent);
		let parent_kept = parent_env == parent_written;
		if parent_kept && !self.may_rewrite(written, own) {
			return written;
		}
		let written_own = self.written_own(written, parent_written);
		// Under a kept parent the written env is the frame's rules over its
		// parent's completed env already; under a replaced one they are put
		// over the parent's completed env instead. A `Self` entry is in
		// neither: about a trait impl's target, lookup never matches it as
		// written.
		let rules = if parent_kept {
			written
		} else {
			let rules = self.assumption_envs.push(parent_env, None);
			*self.assumption_envs.clauses_mut(rules) =
				BoundClauses::Final(written_own);
			rules
		};
		self.assumption_envs
			.set_completion(frame, FrameCompletion::Rewriting { rules });
		let rewrite = Rewrite {
			frame,
			rules,
			parent_env,
		};
		let mut completed = Completed {
			// The written env lacks what is not in it: a `Self` entry, or the
			// whole run of a frame that shares its parent's env.
			rewritten: !parent_kept || written_own.len() != own.len(),
			..Completed::default()
		};
		let inherited: Vec<ClauseRange> = self
			.assumption_envs
			.chain(parent_env)
			.map(|env| {
				env.clauses.final_range().expect("a completed env is final")
			})
			.collect();
		for range in inherited {
			for at in 0..range.len() {
				let clause = self.clauses.get(range)[at];
				self.rewrite(
					strings,
					rewrite,
					clause,
					Origin::Inherited,
					&mut completed,
				);
			}
		}
		for at in 0..own.len() {
			let clause = self.clauses.get(own)[at];
			self.rewrite(strings, rewrite, clause, Origin::Own, &mut completed);
		}
		self.lend_declared_bounds(strings, rewrite, own, &mut completed);
		if !completed.proved.is_empty() {
			let at = self.clause_span(completed.proved[0]);
			let proved =
				BoundClauses::Final(self.clauses.push(&completed.proved));
			if let Err(error) = self
				.prove_clauses_at_their_bounds(strings, frame, rules, proved)
			{
				self.report_completion_failure(strings, error, at);
			}
		}
		if !completed.rewritten {
			return written;
		}
		let reflexive = self
			.assumption_envs
			.chain(written)
			.find_map(|env| env.reflexive);
		let run: Vec<Clause> = completed
			.traits
			.into_iter()
			.map(Clause::Trait)
			.chain(completed.values)
			.collect();
		let flat = self.assumption_envs.push(AssumptionEnvIdx::ROOT, reflexive);
		*self.assumption_envs.clauses_mut(flat) =
			BoundClauses::Final(self.clauses.push(&run));
		flat
	}

	/// Whether completing can change anything: an equality in scope, or a
	/// clause about a type not rooted at a parameter (a `Self` entry's),
	/// which reduces through definitions.
	fn may_rewrite(&self, written: AssumptionEnvIdx, own: ClauseRange) -> bool {
		let in_scope = self.assumption_envs.chain(written).any(|env| {
			self.clauses
				.get(env.clauses.range())
				.iter()
				.any(|clause| matches!(clause, Clause::Equality(_)))
		});
		in_scope
			|| self.clauses.get(own).iter().any(|clause| match *clause {
				Clause::Equality(_) => true,
				Clause::Trait(TraitClause { subject, .. })
				| Clause::Representable(RepresentableClause {
					subject, ..
				}) => self.root_frame(subject).is_none(),
			})
	}

	/// The frame whose parameter `ty`'s projection path starts at; `None`
	/// for a path that starts at no parameter.
	fn root_frame(&self, mut ty: TypeIndex) -> Option<GenericEnvIdx> {
		loop {
			match *self.types.resolve(ty) {
				Type::TypeParam { env, .. } => return Some(env),
				Type::TypeProjection { base, .. } => ty = base,
				_ => return None,
			}
		}
	}

	/// The frame's own clauses its written env holds: none when it shares
	/// its parent's.
	fn written_own(
		&self,
		written: AssumptionEnvIdx,
		parent_written: AssumptionEnvIdx,
	) -> ClauseRange {
		if written == parent_written {
			ClauseRange::EMPTY
		} else {
			self.assumption_envs.get(written).clauses.range()
		}
	}

	/// Rewrites `clause` into `completed`. A part whose normalization fails
	/// keeps its written form: its failure is reported where it belongs, and
	/// a completed env never loses a fact construction had.
	fn rewrite(
		&mut self,
		strings: &StringInterner,
		rewrite: Rewrite,
		clause: Clause,
		origin: Origin,
		completed: &mut Completed,
	) {
		let at = self.clause_span(clause);
		match clause {
			Clause::Trait(written) => {
				let subject = self.normalize_or_written(
					strings,
					rewrite.rules,
					written.subject,
					at,
				);
				if self.types.is_abstract(subject) {
					completed.rewritten |= subject != written.subject;
					push_trait_clause(
						&mut completed.traits,
						TraitClause { subject, ..written },
					);
				} else {
					completed.rewritten = true;
					completed.proved.push(clause);
				}
			}
			Clause::Representable(written) => {
				let subject = self.normalize_or_written(
					strings,
					rewrite.rules,
					written.subject,
					at,
				);
				let ty = self.normalize_or_written(
					strings,
					rewrite.rules,
					written.ty,
					at,
				);
				if self.types.is_abstract(subject) {
					completed.rewritten |=
						subject != written.subject || ty != written.ty;
					completed.values.push(Clause::Representable(
						RepresentableClause {
							subject,
							ty,
							..written
						},
					));
				} else {
					completed.rewritten = true;
					completed.proved.push(clause);
				}
			}
			Clause::Equality(written) => {
				let projection = match origin {
					Origin::Inherited => written.projection,
					// About the frame's own parameters, the parent knows
					// nothing and the frame's own rules must not apply.
					Origin::Own
						if self.root_frame(written.projection)
							== Some(rewrite.frame) =>
					{
						written.projection
					}
					// About a parent's parameter, whose rules may fix it, or
					// a trait impl's target, which reduces through definitions.
					Origin::Own => self.normalize_or_written(
						strings,
						rewrite.parent_env,
						written.projection,
						at,
					),
					Origin::Lent => self.normalize_or_written(
						strings,
						rewrite.rules,
						written.projection,
						at,
					),
				};
				let value = self.normalize_or_written(
					strings,
					rewrite.rules,
					written.value,
					at,
				);
				if matches!(
					self.types.resolve(projection),
					Type::TypeProjection { .. }
				) && self.types.is_abstract(projection)
				{
					completed.rewritten |= projection != written.projection
						|| value != written.value;
					let known = completed.values.iter().any(|existing| {
						matches!(
							existing,
							Clause::Equality(EqualityClause {
								projection: known,
								value: known_value,
								..
							}) if *known == projection && *known_value == value
						)
					});
					if !known {
						completed.values.push(Clause::Equality(
							EqualityClause {
								projection,
								value,
								..written
							},
						));
					}
				} else {
					completed.rewritten = true;
					completed.proved.push(clause);
				}
			}
		}
	}

	/// What an equality of the frame's own, with an abstract value as
	/// written, gives: the declared bounds of its associated type, held by
	/// the value. Sound, since every impl proves its associated types'
	/// declared bounds, so whatever the value is at a use satisfies them; a
	/// concrete value is checked against them where it is written instead.
	fn lend_declared_bounds(
		&mut self,
		strings: &StringInterner,
		rewrite: Rewrite,
		own: ClauseRange,
		completed: &mut Completed,
	) {
		for at in 0..own.len() {
			let Clause::Equality(equality) = self.clauses.get(own)[at] else {
				continue;
			};
			if !self.types.is_abstract(equality.value) {
				continue;
			}
			let Type::TypeProjection {
				base,
				trait_index,
				assoc_type_index,
			} = *self.types.resolve(equality.projection)
			else {
				continue;
			};
			let declared = self.assoc_types[usize::from(assoc_type_index)]
				.as_ref()
				.expect("every signature exists")
				.clauses;
			if declared.is_empty() {
				continue;
			}
			let trait_env = self.traits[usize::from(trait_index)].env;
			let lent = self.instantiate_clauses(declared, trait_env, &[base]);
			let range =
				lent.final_range().expect("instantiated clauses are final");
			for at in 0..range.len() {
				let clause = self.clauses.get(range)[at];
				completed.rewritten = true;
				self.rewrite(strings, rewrite, clause, Origin::Lent, completed);
			}
		}
	}

	/// `ty` normalized in `env`, or as written once its failure is reported
	/// at `at` (a cycle or an overflow) or owned elsewhere.
	fn normalize_or_written(
		&mut self,
		strings: &StringInterner,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
		at: SourceSpan,
	) -> TypeIndex {
		match self.normalize(
			strings,
			env,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		) {
			Ok(normalized) => normalized,
			Err(error) => {
				self.report_completion_failure(strings, error, at);
				ty
			}
		}
	}

	fn report_completion_failure(
		&mut self,
		strings: &StringInterner,
		error: SolverError,
		at: SourceSpan,
	) {
		match error {
			SolverError::Cycle(cycle) => {
				let diagnostic = self.cycle_diagnostic(strings, &cycle, at);
				self.diagnostics.push(diagnostic);
			}
			SolverError::Overflow => {
				self.diagnostics.push(self.overflow_diagnostic(at));
			}
			SolverError::Poisoned => {}
			SolverError::Pending => {
				unreachable!("every signature exists when envs are completed")
			}
		}
	}

	/// Where `clause` is written: its bound, or its binding.
	fn clause_span(&self, clause: Clause) -> SourceSpan {
		match clause {
			Clause::Trait(clause) => self.bounds.span(clause.source),
			Clause::Equality(EqualityClause { source, .. })
			| Clause::Representable(RepresentableClause { source, .. }) => {
				self.binding_span(source)
			}
		}
	}
}
