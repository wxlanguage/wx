//! Normalizing a frame's assumption env. Construction makes its written env,
//! the clauses in scope as written; once every signature exists, they are
//! rewritten by the equalities in scope into its normalized env
//! (`notes/member-selection-and-equalities.md`, decision 2). Path selection
//! reads the written env; everything after construction reads the normalized
//! one. Conformance rewrites a trait function's contract the same way.
use super::{
	AssumptionEnvIdx, Clause, ClauseRange, EnvNormalization, EqualityClause,
	PublishedClauses, RepresentableClause, TraitClause,
};
use crate::ast::StringInterner;
use crate::diagnostics::SourceSpan;
use crate::tir::signatures::Semantics;
use crate::tir::solver::{NormalizationDepth, RewriteFlags, SolverError};
use crate::tir::types::{GenericFrameIdx, Type, TypeIndex};

/// What one frame's clauses are rewritten against.
#[derive(Clone, Copy)]
pub(in crate::tir) struct RewriteScope {
	/// The frame whose own parameters the clauses state facts about, if it
	/// has any: an equality about them keeps its projection as written.
	pub(in crate::tir) own_frame: Option<GenericFrameIdx>,
	/// The frame's clauses as written over its parent's normalized env:
	/// every rule in scope.
	pub(in crate::tir) rewriting_env: AssumptionEnvIdx,
	/// The parent's normalized env: what an equality of the frame's own is
	/// read in when it is about anything but the frame's own parameters, so
	/// a rule never rewrites itself.
	pub(in crate::tir) parent_env: AssumptionEnvIdx,
}

/// What one clause becomes once rewritten.
enum Rewritten {
	/// Still about an abstract type: assumed as it now reads.
	Assumed(Clause),
	/// No longer about an abstract type: it holds or not of its own, and is
	/// proved at its bound.
	Proved,
}

/// Rewritten clauses, collected.
#[derive(Default)]
pub(in crate::tir) struct RewrittenClauses {
	/// What is assumed, each statement once; the first source of a statement
	/// is the one diagnostics name.
	pub(in crate::tir) assumed: Vec<Clause>,
	/// The clauses found to be proved, as written.
	pub(in crate::tir) proved: Vec<Clause>,
	/// Whether the clauses say anything other than as written: one reads
	/// differently, is proved instead, or was lent.
	pub(in crate::tir) changed: bool,
}

impl RewrittenClauses {
	fn push(
		&mut self,
		written: Clause,
		rewritten: Rewritten,
		provenance: Provenance,
	) {
		match rewritten {
			Rewritten::Proved => {
				self.changed = true;
				self.proved.push(written);
			}
			Rewritten::Assumed(clause) => {
				self.changed |=
					provenance == Provenance::Lent || clause != written;
				if !self.assumed.iter().any(|known| known.states_same(&clause))
				{
					self.assumed.push(clause);
				}
			}
		}
	}
}

/// Where a clause comes from, which decides what rewrites it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Provenance {
	/// Already normalized in the parent: only the frame's rules rewrite it.
	Inherited,
	/// Written on the frame.
	Own,
	/// Lent by an associated type's declared bounds through an equality:
	/// read whole with every rule in scope.
	Lent,
}

impl Semantics {
	/// `frame`'s normalized env: asks for its parent's first, then rewrites
	/// what `frame` states, once; a frame read again later gets the same env.
	/// Asked once every signature exists, so nothing it normalizes is
	/// `Pending`.
	pub(in crate::tir) fn normalize_env(
		&mut self,
		strings: &StringInterner,
		frame: GenericFrameIdx,
	) -> AssumptionEnvIdx {
		match self.assumption_envs.normalization(frame) {
			EnvNormalization::Normalized(env) => return env,
			EnvNormalization::Rewriting { rewriting_env } => {
				return rewriting_env;
			}
			EnvNormalization::Unasked => {}
		}
		let parent = self
			.generic_frames
			.parent(frame)
			.expect("the root frame is normalized from the start");
		let parent_env = self.normalize_env(strings, parent);
		let env = self.build_normalized_env(strings, frame, parent, parent_env);
		self.assumption_envs
			.set_normalization(frame, EnvNormalization::Normalized(env));
		env
	}

	/// Normalizes every frame's env not asked for yet, so readers that run
	/// after declarations are checked find each normalized.
	pub(in crate::tir) fn normalize_every_env(
		&mut self,
		strings: &StringInterner,
	) {
		for frame in 0..self.assumption_envs.frame_count() {
			let frame = GenericFrameIdx::new(u32::try_from(frame).unwrap());
			self.normalize_env(strings, frame);
		}
	}

	/// A frame that adds no facts reuses `parent_env`; one whose clauses
	/// read as written keeps its written env; any other gets a flat env
	/// holding every clause in scope, rewritten.
	fn build_normalized_env(
		&mut self,
		strings: &StringInterner,
		frame: GenericFrameIdx,
		parent: GenericFrameIdx,
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
		// Under a kept parent the written env is the frame's clauses over its
		// parent's normalized env already; under a replaced one they are put
		// over the parent's normalized env instead. A `Self` entry is in
		// neither: about a trait impl's target, lookup never matches it as
		// written.
		let rewriting_env = if parent_kept {
			written
		} else {
			self.assumption_envs
				.push_final(parent_env, None, written_own)
		};
		self.assumption_envs.set_normalization(
			frame,
			EnvNormalization::Rewriting { rewriting_env },
		);
		let scope = RewriteScope {
			own_frame: Some(frame),
			rewriting_env,
			parent_env,
		};
		let mut rewritten = RewrittenClauses::default();
		let inherited: Vec<ClauseRange> = self
			.assumption_envs
			.chain(parent_env)
			.map(|env| {
				env.clauses
					.final_range()
					.expect("a normalized env is final")
			})
			.collect();
		for range in inherited {
			self.rewrite_run(
				strings,
				scope,
				range,
				Provenance::Inherited,
				&mut rewritten,
			);
		}
		self.rewrite_own_clauses(strings, scope, own, &mut rewritten);
		self.lend_declared_bounds(strings, scope, own, &mut rewritten);
		self.prove_at_their_bounds(
			strings,
			frame,
			rewriting_env,
			&rewritten.proved,
		);
		// The written env says what the frame assumes when it holds every
		// clause (no `Self` entry is missing from it), reads its parent's
		// facts where they are (the parent's env was kept), and none of them
		// reads differently.
		if parent_kept && written_own.len() == own.len() && !rewritten.changed {
			return written;
		}
		let reflexive = self
			.assumption_envs
			.chain(written)
			.find_map(|env| env.reflexive);
		let run = self.clauses.push(&rewritten.assumed);
		self.assumption_envs
			.push_final(AssumptionEnvIdx::ROOT, reflexive, run)
	}

	/// Whether normalizing can change anything: an equality in scope, or a
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
	fn root_frame(&self, mut ty: TypeIndex) -> Option<GenericFrameIdx> {
		loop {
			match *self.types.resolve(ty) {
				Type::TypeParam { frame, .. } => return Some(frame),
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

	/// Proves `proved`, `frame`'s clauses no longer about an abstract type,
	/// in `env`, reporting each that does not hold at its bound.
	fn prove_at_their_bounds(
		&mut self,
		strings: &StringInterner,
		frame: GenericFrameIdx,
		env: AssumptionEnvIdx,
		proved: &[Clause],
	) {
		let Some(&first) = proved.first() else {
			return;
		};
		let proved = PublishedClauses::Final(self.clauses.push(proved));
		if let Err(error) =
			self.prove_clauses_at_their_bounds(strings, frame, env, proved)
		{
			let at = self.clause_span(first);
			self.report_normalization_failure(strings, error, at);
		}
	}

	/// `own`, a frame's own clauses, rewritten in `scope` into `out`.
	pub(in crate::tir) fn rewrite_own_clauses(
		&mut self,
		strings: &StringInterner,
		scope: RewriteScope,
		own: ClauseRange,
		out: &mut RewrittenClauses,
	) {
		self.rewrite_run(strings, scope, own, Provenance::Own, out);
	}

	fn rewrite_run(
		&mut self,
		strings: &StringInterner,
		scope: RewriteScope,
		range: ClauseRange,
		provenance: Provenance,
		out: &mut RewrittenClauses,
	) {
		// One clause at a time: normalizing interns and may push clauses,
		// and the arena only grows, so the range stays valid.
		for at in 0..range.len() {
			let clause = self.clauses.get(range)[at];
			let rewritten =
				self.rewrite_clause(strings, scope, clause, provenance);
			out.push(clause, rewritten, provenance);
		}
	}

	/// `clause` rewritten. A part whose normalization fails keeps its
	/// written form: its failure is reported where it belongs, and a
	/// normalized env never loses a fact construction had.
	fn rewrite_clause(
		&mut self,
		strings: &StringInterner,
		scope: RewriteScope,
		clause: Clause,
		provenance: Provenance,
	) -> Rewritten {
		let at = self.clause_span(clause);
		let normalize = |sema: &mut Self, env, ty| {
			sema.normalize_or_written(strings, env, ty, at)
		};
		match clause {
			Clause::Trait(written) => {
				let subject =
					normalize(self, scope.rewriting_env, written.subject);
				if !self.types.is_abstract(subject) {
					return Rewritten::Proved;
				}
				Rewritten::Assumed(Clause::Trait(TraitClause {
					subject,
					..written
				}))
			}
			Clause::Representable(written) => {
				let subject =
					normalize(self, scope.rewriting_env, written.subject);
				if !self.types.is_abstract(subject) {
					return Rewritten::Proved;
				}
				let ty = normalize(self, scope.rewriting_env, written.ty);
				Rewritten::Assumed(Clause::Representable(RepresentableClause {
					subject,
					ty,
					..written
				}))
			}
			Clause::Equality(written) => {
				let projection = match provenance {
					Provenance::Inherited => written.projection,
					// About the frame's own parameters, the parent knows
					// nothing and the frame's own rules must not apply.
					Provenance::Own
						if scope.own_frame.is_some()
							&& self.root_frame(written.projection)
								== scope.own_frame =>
					{
						written.projection
					}
					// About a parent's parameter, whose rules may fix it, or
					// a trait impl's target, which reduces through definitions.
					Provenance::Own => {
						normalize(self, scope.parent_env, written.projection)
					}
					Provenance::Lent => {
						normalize(self, scope.rewriting_env, written.projection)
					}
				};
				let still_projection = matches!(
					self.types.resolve(projection),
					Type::TypeProjection { .. }
				) && self.types.is_abstract(projection);
				if !still_projection {
					return Rewritten::Proved;
				}
				let value = normalize(self, scope.rewriting_env, written.value);
				Rewritten::Assumed(Clause::Equality(EqualityClause {
					projection,
					value,
					..written
				}))
			}
		}
	}

	/// What the equalities in `own` with an abstract value as written give:
	/// the declared bounds of their associated type, held by the value,
	/// rewritten into `out`. Sound, since every impl proves its associated
	/// types' declared bounds, so whatever the value is at a use satisfies
	/// them; a concrete value is checked against them where it is written
	/// instead.
	pub(in crate::tir) fn lend_declared_bounds(
		&mut self,
		strings: &StringInterner,
		scope: RewriteScope,
		own: ClauseRange,
		out: &mut RewrittenClauses,
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
			let trait_frame =
				self.traits[usize::from(trait_index)].generic_params;
			let lent = self.instantiate_clauses(declared, trait_frame, &[base]);
			let range =
				lent.final_range().expect("instantiated clauses are final");
			self.rewrite_run(strings, scope, range, Provenance::Lent, out);
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
				self.report_normalization_failure(strings, error, at);
				ty
			}
		}
	}

	fn report_normalization_failure(
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
				unreachable!("every signature exists when envs are normalized")
			}
		}
	}

	/// Where `clause` is written: its bound, or its binding.
	fn clause_span(&self, clause: Clause) -> SourceSpan {
		match clause {
			Clause::Trait(clause) => self.source_clauses.span(clause.source),
			Clause::Equality(EqualityClause { source, .. })
			| Clause::Representable(RepresentableClause { source, .. }) => {
				self.binding_span(source)
			}
		}
	}
}
