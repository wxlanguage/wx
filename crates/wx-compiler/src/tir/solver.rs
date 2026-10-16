//! The solver: associated-type normalization and impl selection, which recurse
//! into each other and so are one engine, `Solver`. It reads the world through
//! a `SolverView` lent by `TypeContext::solver_and_view`, which names every
//! table it may touch.
//!
//! Declaration identity stays in projections; abstract equalities come from
//! effective bounds; concrete values come from selected impl members, whose
//! values the solver judges once (`AssocValue`). Evidence comparison uses the
//! same traversal and budget, reducing assumed equalities without selecting
//! providers. Structural substitution remains independent in `types.rs`.

use std::collections::HashMap;

#[cfg(test)]
use crate::diagnostics::SourceSpan;

use super::assumptions::{
	AssumptionKind, AssumptionReader, EffectiveBounds, Readiness,
	SelfSubstitution,
};
use super::bounds::ImpliedBindingKind;
use super::defs::{
	AssocTypeIdx, DefinitionRegistry, MemberKind, TraitIdx, TraitImplIdx,
};
use super::impls::{ImplDispatch, ImplTarget};
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::signatures::{
	AssocTypeSignature, ParamBounds, TraitImplSignature, TraitSignature,
	TypeContext,
};
use super::types::{
	Substitution, Type, TypeEnvArena, TypeEnvIdx, TypeIndex, TypeInterner,
};

/// Why the solver (normalization and impl selection, which are one recursive
/// engine) has no answer. It only reports why; whoever wrote the type or the
/// requirement owns any diagnostic, so a query never emits one.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum SolverError {
	/// A fact the answer depends on is not final yet (declarations are still
	/// being built). It is not evidence of absence; ask again once construction
	/// has advanced.
	Pending,
	/// There is no answer because the input derives from an error another
	/// construct owns: an erroneous receiver, a poisoned value, a provider that
	/// supplies nothing, or a check that already reported its violation. The
	/// owner reports it; consumers recover silently.
	Poisoned,
	/// The recursion budget ran out. The asking site reports it.
	Overflow,
	/// A projection requires itself. The asking site reports it.
	Cycle(Box<ProjectionCycle>),
}

/// A projection that normalization reached again while normalizing it: the
/// loop, read from the projection that closed it.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct ProjectionCycle {
	/// The projection that was requested again.
	pub(super) projection: TypeIndex,
	/// The projections in flight when it came back, outermost first.
	pub(super) steps: Box<[TypeIndex]>,
	/// The impl member in the loop that owns it (`AssocValue`): the first
	/// defined, so the report does not depend on which member was asked for
	/// first. `None` for a loop found within one derivation.
	pub(super) owner: Option<ImplMember>,
}

/// One associated type of one trait impl: the value the impl supplies, or the
/// trait's default when it supplies none. The unit the solver judges, since a
/// default means something different in every impl that inherits it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct ImplMember {
	pub(super) impl_index: TraitImplIdx,
	pub(super) declaration: AssocTypeIdx,
}

impl ImplMember {
	/// Definition order, which picks a loop's owner.
	fn order(self) -> (usize, usize) {
		(usize::from(self.impl_index), usize::from(self.declaration))
	}
}

/// What the solver has concluded about an impl member's value, judged on first
/// use (`Solver::assoc_value`). The signatures keep the value as
/// written (`AssocTypeSignature::value`).
///
/// A loop through definitions has no root cause, so the definitions own it:
/// the first defined member keeps the failure for its own check to report,
/// and every other reader of a poisoned value fails silently, as it would for
/// a value that failed to lower. The verdict depends on the definitions alone,
/// so it does not matter who asks first.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum AssocValue {
	/// Not asked for yet.
	Unchecked,
	/// Being judged; reaching it again closes a loop through definitions.
	InProgress,
	/// The value normalizes in the impl's own scope. Readers still take the
	/// value as written and normalize it in their own context.
	Resolved,
	/// The value has no meaning because it derives from a failure another
	/// construct owns and reports.
	Poisoned,
	/// The judgement ran out of budget. The definition owns this, and its
	/// check reports it.
	Overflowed,
	/// The value requires itself through definitions only, and this member
	/// owns the loop. Its check reports it.
	Cyclic(Box<ProjectionCycle>),
}

/// What the facts in scope establish for a trait requirement, without impl
/// dispatch. Ordered by strength, so combining two readings keeps the
/// stronger (`max`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum Assumption {
	/// The facts are final and none proves it.
	Unproven,
	/// No fact read so far proves it; an unfinished table may still add one.
	Pending,
	/// A fact proves it.
	Holds,
}

/// One frame of the solver's stack: work started and not yet finished, the
/// solver's counterpart of a `query_stack` frame. The stack is the path a
/// cycle is read from.
///
/// A projection is rewritten by one of two facts, and a loop is judged by
/// which it passes through:
///
/// ```text
/// func f<T: Tr where { A = U::A }, U: Tr where { A = T::A }>() {}
/// // T::A -> U::A -> T::A through equalities: a tautology, T::A stays abstract
///
/// impl Tr for W { type A = <W as Tr>::A; }
/// // W::A -> W::A through a definition only: a cycle, reported by its member
/// ```
enum SolverFrame {
	/// A projection being normalized; its `ty` advances as the base reduces.
	/// Evidence comparison and provider reduction differ in `facts`, so they
	/// are distinct cycle keys.
	Projection(Normalization),
	/// The projection below was rewritten by an equality written in a bound
	/// (`T: Tr where { A = U }` rewrites `T::A` to `U`). It states what the
	/// caller may assume, not what a type is, so a loop through one is a
	/// tautology.
	Equality,
	/// A definition: an impl member's value being judged (`impl Tr for W
	/// { type A = u32; }` rewrites `W::A` to `u32`). Selected by
	/// `requested_by` (`None` when its own check asked). The member's verdict is
	/// `InProgress` while this frame is on the stack, as a signature's query state
	/// is while its frame is on `query_stack`. The judgement starts with a full
	/// recursion budget, so running out of it is a verdict on the definition
	/// alone; `outer_budget` is the budget to restore once it is done.
	Judgement {
		member: ImplMember,
		requested_by: Option<TypeIndex>,
		outer_budget: usize,
	},
}

/// The derivation currently being computed. Shared across re-entrant
/// signature queries and value judgements, not recreated per API call, so
/// cycle detection sees every frame of a loop, whichever judgement it crosses.
pub(super) struct SolverState {
	frames: Vec<SolverFrame>,
	/// How many more levels the innermost judgement (or the request, outside
	/// any judgement) may recurse. Equals `Solver::recursion_limit` when no frame is open.
	pub(super) recursion_budget: usize,
	/// Roll back an assumed equality chain that made no finite progress.
	blocked_at: Option<usize>,
	/// The outermost frame the innermost request's answer read so far (a
	/// cycle, a re-entered judgement or a rollback), `usize::MAX` when none.
	/// An answer that read no frame below its own request is a function of its
	/// `Normalization` alone.
	lowest_frame_read: usize,
}

/// The engine that normalizes types and selects impls, with everything it
/// keeps: the derivation in flight, the finished-answer cache and the rule for
/// when it may be used, and the verdicts on impl members' values.
pub(super) struct Solver {
	/// The recursion budget each request and each judgement starts with. Fixed
	/// configuration, not state; only tests change it.
	recursion_limit: usize,
	pub(super) state: SolverState,
	/// Only `Ok` answers are stored. `Pending` means a fact is not final yet,
	/// and `Poisoned` is not a permanent verdict (a budget overflow can be
	/// retried), so neither is remembered. Every
	/// stored answer was final when computed, so no "facts are final" switch is
	/// needed.
	pub(super) normalized: HashMap<Normalization, TypeIndex>,
	/// The verdict on each impl member asked about; absent is `Unchecked`.
	/// A member is `InProgress` exactly while its `SolverFrame::Judgement` is on
	/// the stack.
	pub(super) verdicts: HashMap<ImplMember, AssocValue>,
}

impl Solver {
	pub(super) fn new() -> Self {
		let recursion_limit = 128;
		Self {
			recursion_limit,
			state: SolverState {
				frames: Vec::new(),
				recursion_budget: recursion_limit,
				blocked_at: None,
				lowest_frame_read: usize::MAX,
			},
			normalized: HashMap::new(),
			verdicts: HashMap::new(),
		}
	}

	pub(super) fn verdict(&self, member: ImplMember) -> &AssocValue {
		self.verdicts.get(&member).unwrap_or(&AssocValue::Unchecked)
	}

	/// `member`'s value, judged once: normalized in its impl's `Self` scope with
	/// a budget of its own, so the verdict depends on the definitions alone and
	/// is memoized whoever asks first. `requested_by` is the projection that
	/// selected it, `None` when its own check asks.
	///
	/// Answers the value as written in the impl's environment; the caller
	/// instantiates it. The judgement is a frame on the same stack, so
	/// reaching the member again sees the whole loop: through definitions only,
	/// it is a cycle owned by its first defined member (see `AssocValue`);
	/// through an equality, it is a tautology the derivation itself blocks.
	pub(super) fn assoc_value(
		&mut self,
		view: &mut SolverView<'_>,
		member: ImplMember,
		requested_by: Option<TypeIndex>,
	) -> Result<TypeIndex, SolverError> {
		match self.verdict(member) {
			AssocValue::Unchecked => {}
			AssocValue::InProgress => {
				return self.reenter_judgement(view, member, requested_by);
			}
			AssocValue::Resolved => return view.impl_member_value(member),
			AssocValue::Poisoned
			| AssocValue::Overflowed
			| AssocValue::Cyclic(_) => return Err(SolverError::Poisoned),
		}
		let value = match view.impl_member_value(member) {
			Ok(value) => value,
			// No value (lowering failed and reported, or neither the impl nor the
			// trait supplies one, which conformance owns); nothing to judge.
			Err(SolverError::Poisoned) => {
				self.verdicts.insert(member, AssocValue::Poisoned);
				return Err(SolverError::Poisoned);
			}
			Err(error) => return Err(error),
		};
		let scope = view.trait_impls[usize::from(member.impl_index)]
			.as_ref()
			.expect("a member with a value has a resolved impl header")
			.self_scope;
		self.verdicts.insert(member, AssocValue::InProgress);
		let index = self.state.frames.len();
		self.state.frames.push(SolverFrame::Judgement {
			member,
			requested_by,
			outer_budget: std::mem::replace(
				&mut self.state.recursion_budget,
				self.recursion_limit,
			),
		});
		let result = self.normalize(
			view,
			scope,
			value,
			NormalizationDepth::Deep,
			RewriteFacts::EqualitiesAndDefinitions,
		);
		let Some(SolverFrame::Judgement { outer_budget, .. }) =
			self.state.frames.pop()
		else {
			unreachable!("the judgement is the innermost frame once it is done")
		};
		self.state.recursion_budget = outer_budget;
		// A tautology further out is unwinding through this judgement, which was
		// cut short: there is no verdict yet, so it is judged again when asked.
		if self.state.blocked_at.is_some_and(|blocked| blocked < index) {
			self.verdicts.remove(&member);
			return Ok(value);
		}
		let (verdict, answer) = match result {
			Ok(_) => (AssocValue::Resolved, Ok(value)),
			Err(SolverError::Pending) => {
				(AssocValue::Unchecked, Err(SolverError::Pending))
			}
			Err(SolverError::Poisoned) => {
				(AssocValue::Poisoned, Err(SolverError::Poisoned))
			}
			// Another member owns the loop. Its own judgement, further out,
			// answers `Poisoned` once it has kept the loop, so members past it
			// unwind as derived failures.
			Err(SolverError::Cycle(cycle))
				if cycle.owner.is_some_and(|owner| owner != member) =>
			{
				(AssocValue::Poisoned, Err(SolverError::Cycle(cycle)))
			}
			// The budget counts from this judgement, so running out is a verdict
			// on the definition, like a cycle.
			Err(SolverError::Overflow) => {
				(AssocValue::Overflowed, Err(SolverError::Poisoned))
			}
			Err(SolverError::Cycle(cycle)) => {
				(AssocValue::Cyclic(cycle), Err(SolverError::Poisoned))
			}
		};
		self.verdicts.insert(member, verdict);
		answer
	}

	/// `member` was reached again while its judgement is on the stack. An
	/// equality on the way back makes the loop a tautology, not an error: the
	/// value as written goes on, and the derivation blocks once its projections
	/// repeat (`projection_cycle`), as it does for any loop through an
	/// equality. Through definitions only, the loop is a cycle, read from the
	/// stack and owned by its first defined member.
	fn reenter_judgement(
		&mut self,
		view: &mut SolverView<'_>,
		member: ImplMember,
		requested_by: Option<TypeIndex>,
	) -> Result<TypeIndex, SolverError> {
		let start = self
			.state
			.frames
			.iter()
			.position(|frame| {
				matches!(frame, SolverFrame::Judgement { member: judged, .. } if *judged == member)
			})
			.expect("an in-progress judgement is on the stack");
		self.state.lowest_frame_read = self.state.lowest_frame_read.min(start);
		let loop_frames = &self.state.frames[start..];
		if loop_frames
			.iter()
			.any(|frame| matches!(frame, SolverFrame::Equality))
		{
			return view.impl_member_value(member);
		}
		let mut members = Vec::new();
		// Each judgement after the first was selected by the projection on its
		// frame;
		// this request selected `member` again and closes the loop.
		let mut steps = Vec::new();
		for frame in loop_frames {
			if let SolverFrame::Judgement {
				member,
				requested_by,
				..
			} = *frame
			{
				if !members.is_empty() {
					steps.push(
						requested_by
							.expect("only a projection re-enters a judgement"),
					);
				}
				members.push(member);
			}
		}
		steps.push(
			requested_by.expect("only a projection re-enters a judgement"),
		);
		let (at, owner) = members
			.iter()
			.copied()
			.enumerate()
			.min_by_key(|(_, member)| member.order())
			.expect("the loop has a member");
		// Read the loop from the owner: its value requires the first step.
		steps.rotate_left(at);
		Err(SolverError::Cycle(Box::new(ProjectionCycle {
			projection: steps[0],
			steps: steps.into_boxed_slice(),
			owner: Some(owner),
		})))
	}

	#[cfg(test)]
	pub(super) fn set_limit_for_test(&mut self, limit: usize) {
		debug_assert!(self.state.frames.is_empty());
		self.recursion_limit = limit;
		self.state.recursion_budget = limit;
	}
}

/// One normalization: `ty` under the assumptions of `env`, reduced to `depth`
/// by `facts`. Two are the same exactly when their answers must be, so it keys
/// both cycle detection and the cache.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Normalization {
	env: TypeEnvIdx,
	pub(super) ty: TypeIndex,
	depth: NormalizationDepth,
	facts: RewriteFacts,
}

/// How far into a type a normalization reduces.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum NormalizationDepth {
	/// Only the outermost type: enough to select an impl.
	Shallow,
	/// The type and every type nested in it.
	Deep,
}

/// The facts that may replace a projection with a value.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum RewriteFacts {
	/// Only equalities written in bounds. Comparing evidence for a trait must
	/// not select the impl being proved.
	Equalities,
	/// Equalities, and the impl's definition when no equality applies.
	EqualitiesAndDefinitions,
}

/// What the assumptions in scope say a projection equals. Unfinished facts are
/// not an answer (`SolverError::Pending`), and neither absence nor competing
/// equalities make an abstract projection invalid.
pub(super) enum EqualityLookup {
	Known(TypeIndex),
	Absent,
	Ambiguous,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct ContextualEquality {
	pub(super) value: TypeIndex,
	pub(super) context: Option<SelfSubstitution>,
}

/// What the solver may read, lent by `TypeContext::solver`. The interner is the
/// only thing it extends; every other table is read-only and already final
/// (an unfinished slot reads as `Pending`). Diagnostics, strings, the query
/// engine and the per-kind signature tables a body or a declaration owns are
/// deliberately not here: the solver can neither report nor construct.
pub(super) struct SolverView<'a> {
	pub(super) types: &'a mut TypeInterner,
	pub(super) defs: &'a DefinitionRegistry,
	pub(super) impl_dispatch: &'a ImplDispatch,
	pub(super) traits: &'a [TraitSignature],
	pub(super) trait_impls: &'a [Option<TraitImplSignature>],
	pub(super) assoc_types: &'a [Option<AssocTypeSignature>],
	pub(super) param_bounds: &'a [Box<[ParamBounds]>],
	pub(super) type_envs: &'a TypeEnvArena,
}

impl<'a> SolverView<'a> {
	fn reader(&self) -> AssumptionReader<'a> {
		AssumptionReader::new(
			self.type_envs,
			self.param_bounds,
			self.traits,
			self.assoc_types,
		)
	}

	/// Lend fact storage and the interner separately, so traversing facts can
	/// intern projected subjects without cloning or mutating their bound trees.
	fn assumptions(&mut self) -> (AssumptionReader<'a>, &mut TypeInterner) {
		(self.reader(), &mut *self.types)
	}

	pub(super) fn effective_bounds(
		&self,
		receiver: TypeIndex,
		recursion_budget: usize,
	) -> EffectiveBounds<'a> {
		self.reader()
			.effective_bounds(&*self.types, receiver, recursion_budget)
	}

	/// Only a parameter or a projection of one can carry assumed equalities.
	fn is_abstract(&self, ty: TypeIndex) -> bool {
		matches!(
			self.types.resolve(ty),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		)
	}

	/// The value an impl supplies for an associated type, as lowered in its own
	/// environment. Instantiation and any normalization made possible by
	/// substitution belong to the caller. Reads the finished slot: an unfilled
	/// one is an unfinished fact (`Pending`), never something to construct here.
	fn assoc_type_value(
		&self,
		provider: AssocTypeIdx,
	) -> Result<TypeIndex, SolverError> {
		let Some(signature) = self.assoc_types[usize::from(provider)].as_ref()
		else {
			return Err(SolverError::Pending);
		};
		match signature.value {
			Some(TypeIndex::ERROR) => Err(SolverError::Poisoned),
			Some(value) => Ok(value),
			None => unreachable!("an impl provider has a value"),
		}
	}

	/// `member`'s value in its impl's environment, as written: the impl's own,
	/// or the trait's default with `Self` the impl's target. Readers go through
	/// `Solver::assoc_value`, which judges it.
	fn impl_member_value(
		&mut self,
		member: ImplMember,
	) -> Result<TypeIndex, SolverError> {
		let Some(header) =
			self.trait_impls[usize::from(member.impl_index)].as_ref()
		else {
			return Err(SolverError::Pending);
		};
		let target = header.target.inner;
		match self.defs.select_trait_member(
			member.impl_index,
			MemberKind::AssociatedType(member.declaration),
		) {
			TraitMemberSelection::Impl(MemberKind::AssociatedType(
				provider,
			)) => self.assoc_type_value(provider),
			TraitMemberSelection::Impl(_) => Err(SolverError::Poisoned),
			TraitMemberSelection::TraitDeclaration(_) => {
				let default = self.assoc_type_default(member.declaration)?;
				let trait_index = self
					.impl_dispatch
					.trait_header(member.impl_index)
					.trait_def
					.expect("a selected impl names its trait")
					.inner;
				let env = self.traits[usize::from(trait_index)].env;
				Ok(self.types.substitute(
					default,
					&Substitution {
						env,
						args: &[target],
					},
				))
			}
		}
	}

	/// The default a trait declaration supplies when the selected impl omits
	/// the member, in the trait's `Self` scope. A declaration without a default
	/// has no value; the later conformance pass owns the missing-member report.
	fn assoc_type_default(
		&self,
		declaration: AssocTypeIdx,
	) -> Result<TypeIndex, SolverError> {
		let Some(signature) =
			self.assoc_types[usize::from(declaration)].as_ref()
		else {
			return Err(SolverError::Pending);
		};
		match signature.value {
			Some(TypeIndex::ERROR) | None => Err(SolverError::Poisoned),
			Some(value) => Ok(value),
		}
	}
}

impl Solver {
	/// A ready result can be an abstract projection. Pending is a dependency
	/// state, never evidence that a concrete impl does not match.
	pub(super) fn normalize_head_query(
		&mut self,
		view: &mut SolverView<'_>,
		env: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<TypeIndex, SolverError> {
		self.normalize(
			view,
			env,
			ty,
			NormalizationDepth::Shallow,
			RewriteFacts::EqualitiesAndDefinitions,
		)
	}

	pub(super) fn normalize_type_query(
		&mut self,
		view: &mut SolverView<'_>,
		env: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<TypeIndex, SolverError> {
		self.normalize(
			view,
			env,
			ty,
			NormalizationDepth::Deep,
			RewriteFacts::EqualitiesAndDefinitions,
		)
	}

	pub(super) fn normalize_assumed_type_query(
		&mut self,
		view: &mut SolverView<'_>,
		env: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<TypeIndex, SolverError> {
		self.normalize(
			view,
			env,
			ty,
			NormalizationDepth::Deep,
			RewriteFacts::Equalities,
		)
	}
}

impl Solver {
	/// The cache layer around `normalize_uncached`. An answer that read a frame
	/// below its own request (cycle and rollback state, an open judgement)
	/// holds only while that frame is open, so it is not stored. Only a request
	/// with no frame open reads the cache: a nested one could reuse an answer
	/// whose derivation passed through a frame open now, skipping the cycle it
	/// would have found.
	///
	/// TODO: let nested requests read the cache too, removing the repeated
	/// work inside one deep normalization. Each entry would also store what its
	/// derivation pushed (projection normalizations and judged members), and a
	/// nested read would use it only when none of those is on the stack now,
	/// as rustc's search graph does. Worth it once body checking makes
	/// normalization measurably hot; every frame-pushing path must then record
	/// itself, or reads silently become order-dependent.
	fn normalize(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		let normalization = Normalization {
			env: assumption_context,
			ty,
			depth,
			facts,
		};
		let frame = self.state.frames.len();
		if frame == 0
			&& let Some(&normalized) = self.normalized.get(&normalization)
		{
			return Ok(normalized);
		}
		let outer_read =
			std::mem::replace(&mut self.state.lowest_frame_read, usize::MAX);
		let result =
			self.normalize_uncached(view, assumption_context, ty, depth, facts);
		let lowest_read = self.state.lowest_frame_read;
		self.state.lowest_frame_read = outer_read.min(lowest_read);
		// A request that started with nothing in flight leaves nothing behind.
		debug_assert!(frame != 0 || self.state.frames.is_empty());
		debug_assert!(frame != 0 || self.state.blocked_at.is_none());
		if lowest_read >= frame
			&& let Ok(normalized) = result
		{
			self.normalized.insert(normalization, normalized);
		}
		result
	}

	fn normalize_uncached(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		if let Some(blocked) = self.state.blocked_at {
			// Unwinding to `blocked`: the answer is only a way out.
			self.state.lowest_frame_read =
				self.state.lowest_frame_read.min(blocked);
			return Ok(ty);
		}
		if self.state.recursion_budget == 0 {
			// Budget exhaustion is a failure the asking site reports, never an
			// unfinished fact; a top-level request can be retried with more.
			return Err(SolverError::Overflow);
		}
		self.state.recursion_budget -= 1;
		let result = if matches!(
			view.types.resolve(ty),
			Type::AssocTypeProjection { .. }
		) {
			self.normalize_projection(
				view,
				assumption_context,
				ty,
				depth,
				facts,
			)
		} else {
			match depth {
				NormalizationDepth::Shallow => Ok(ty),
				NormalizationDepth::Deep => self.normalize_children(
					view,
					assumption_context,
					ty,
					depth,
					facts,
				),
			}
		};
		self.state.recursion_budget += 1;
		result
	}

	fn normalize_projection(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		let normalization = Normalization {
			env: assumption_context,
			ty: projection,
			depth,
			facts,
		};
		if self.projection_cycle(normalization)? {
			return Ok(projection);
		}
		self.state
			.frames
			.push(SolverFrame::Projection(normalization));
		// Keep the frame active across receiver normalization, provider queries,
		// and traversal of the resulting type, including compound results.
		let result = self.reduce_projection(
			view,
			assumption_context,
			projection,
			depth,
			facts,
		);
		let index = self.state.frames.len() - 1;
		self.state.frames.pop();
		if let Some(blocked) = self.state.blocked_at {
			if index == blocked {
				self.state.blocked_at = None;
			}
			return Ok(projection);
		}
		result
	}

	fn reduce_projection(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		let Type::AssocTypeProjection {
			base,
			trait_index,
			assoc_type_index,
		} = *view.types.resolve(projection)
		else {
			unreachable!()
		};
		// Receiver-specific nested facts must be read before reducing the
		// receiver to a value that no longer carries their provenance.
		if view.is_abstract(base) {
			match self.projection_equality(
				view,
				assumption_context,
				base,
				trait_index,
				assoc_type_index,
			)? {
				EqualityLookup::Known(value) => {
					return self.reduce_by_equality(
						view,
						assumption_context,
						projection,
						value,
						depth,
						facts,
					);
				}
				EqualityLookup::Absent | EqualityLookup::Ambiguous => {}
			}
		}
		let next_base =
			self.normalize(view, assumption_context, base, depth, facts)?;
		if next_base == TypeIndex::ERROR {
			return Err(SolverError::Poisoned);
		}
		let projection = if next_base == base {
			projection
		} else {
			let next = view.types.intern(Type::AssocTypeProjection {
				base: next_base,
				trait_index,
				assoc_type_index,
			});
			if self.projection_cycle(Normalization {
				env: assumption_context,
				ty: next,
				depth,
				facts,
			})? {
				return Ok(projection);
			}
			let Some(SolverFrame::Projection(current)) =
				self.state.frames.last_mut()
			else {
				unreachable!("the reducing projection is the innermost frame")
			};
			current.ty = next;
			next
		};
		if view.is_abstract(next_base) {
			return match self.projection_equality(
				view,
				assumption_context,
				next_base,
				trait_index,
				assoc_type_index,
			)? {
				EqualityLookup::Known(value) => self.reduce_by_equality(
					view,
					assumption_context,
					projection,
					value,
					depth,
					facts,
				),
				EqualityLookup::Absent | EqualityLookup::Ambiguous => {
					Ok(projection)
				}
			};
		}
		if matches!(
			view.types.resolve(next_base),
			Type::Infer | Type::AssociatedType { .. }
		) {
			return Ok(projection);
		}
		if facts == RewriteFacts::Equalities {
			return Ok(projection);
		}
		// `None` is silent on purpose: normalization is a query and reports
		// nothing. The construct that wrote this projection owns the report,
		// either when it formed the projection or through the membership check
		// it recorded; a failure derived from it stays quiet.
		let Some(found) = self.find_trait_impl_query(
			view,
			assumption_context,
			next_base,
			trait_index,
		)?
		else {
			return Err(SolverError::Poisoned);
		};
		let TraitImplLookup::Concrete { impl_index, args } = found else {
			return Ok(projection);
		};
		let member = ImplMember {
			impl_index,
			declaration: assoc_type_index,
		};
		let value = self.assoc_value(view, member, Some(projection))?;
		let instantiated = if args.is_empty() {
			value
		} else {
			let env = view.trait_impls[usize::from(impl_index)]
				.as_ref()
				.expect("a generic selected impl has a resolved header")
				.type_params;
			debug_assert_ne!(env, TypeEnvIdx::ROOT);
			view.types
				.substitute(value, &Substitution { env, args: &args })
		};
		self.normalize(view, assumption_context, instantiated, depth, facts)
	}

	/// An equality in scope gives `projection` the value `value`. One that
	/// restates the projection (`A = T::A` for `T::A`) leaves it abstract.
	fn reduce_by_equality(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		value: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		if value == projection {
			return Ok(projection);
		}
		self.state.frames.push(SolverFrame::Equality);
		let result =
			self.normalize(view, assumption_context, value, depth, facts);
		self.state.frames.pop();
		result
	}

	fn projection_cycle(
		&mut self,
		normalization: Normalization,
	) -> Result<bool, SolverError> {
		let Some(start) = self.state.frames.iter().position(|frame| {
			matches!(frame, SolverFrame::Projection(step) if *step == normalization)
		}) else {
			return Ok(false);
		};
		self.state.lowest_frame_read = self.state.lowest_frame_read.min(start);
		let loop_frames = &self.state.frames[start..];
		if loop_frames
			.iter()
			.any(|frame| matches!(frame, SolverFrame::Equality))
		{
			self.state.blocked_at = Some(
				self.state
					.blocked_at
					.map_or(start, |previous| previous.min(start)),
			);
			return Ok(true);
		}
		// The loop goes through a value being judged. Repeating the projection
		// selects that member again one step later, where the judgement reads
		// the loop and its owner (`reenter_judgement`).
		if loop_frames
			.iter()
			.any(|frame| matches!(frame, SolverFrame::Judgement { .. }))
		{
			return Ok(false);
		}
		let steps = loop_frames
			.iter()
			.filter_map(|frame| match frame {
				SolverFrame::Projection(step) => Some(step.ty),
				SolverFrame::Equality | SolverFrame::Judgement { .. } => None,
			})
			.collect();
		Err(SolverError::Cycle(Box::new(ProjectionCycle {
			projection: normalization.ty,
			steps,
			owner: None,
		})))
	}

	/// Rebuild a structured type from its normalized children. Interning
	/// returns the original index when nothing changed.
	fn normalize_children(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		let rebuilt = match view.types.resolve(ty).clone() {
			Type::Tuple { mut elements } => {
				for element in elements.iter_mut() {
					*element = self.normalize(
						view,
						assumption_context,
						*element,
						depth,
						facts,
					)?;
				}
				Type::Tuple { elements }
			}
			Type::Struct {
				struct_index,
				mut type_args,
			} => {
				for arg in type_args.iter_mut() {
					*arg = self.normalize(
						view,
						assumption_context,
						*arg,
						depth,
						facts,
					)?;
				}
				Type::Struct {
					struct_index,
					type_args,
				}
			}
			Type::FunctionItem {
				func_index,
				mut type_args,
			} => {
				for arg in type_args.iter_mut() {
					*arg = self.normalize(
						view,
						assumption_context,
						*arg,
						depth,
						facts,
					)?;
				}
				Type::FunctionItem {
					func_index,
					type_args,
				}
			}
			Type::Function { mut params, result } => {
				for param in params.iter_mut() {
					*param = self.normalize(
						view,
						assumption_context,
						*param,
						depth,
						facts,
					)?;
				}
				Type::Function {
					params,
					result: self.normalize(
						view,
						assumption_context,
						result,
						depth,
						facts,
					)?,
				}
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => Type::Pointer {
				to: self.normalize(
					view,
					assumption_context,
					to,
					depth,
					facts,
				)?,
				memory: self.normalize(
					view,
					assumption_context,
					memory,
					depth,
					facts,
				)?,
				ownership,
			},
			Type::Array {
				of,
				size,
				memory,
				ownership,
			} => Type::Array {
				of: self.normalize(
					view,
					assumption_context,
					of,
					depth,
					facts,
				)?,
				size,
				memory: self.normalize(
					view,
					assumption_context,
					memory,
					depth,
					facts,
				)?,
				ownership,
			},
			Type::Slice {
				of,
				memory,
				ownership,
			} => Type::Slice {
				of: self.normalize(
					view,
					assumption_context,
					of,
					depth,
					facts,
				)?,
				memory: self.normalize(
					view,
					assumption_context,
					memory,
					depth,
					facts,
				)?,
				ownership,
			},
			Type::AssocTypeProjection { .. } => unreachable!(
				"projections are handled before structural traversal"
			),
			Type::Error
			| Type::Infer
			| Type::Never
			| Type::Integer
			| Type::Float
			| Type::U8
			| Type::I8
			| Type::U16
			| Type::I16
			| Type::U32
			| Type::I32
			| Type::U64
			| Type::I64
			| Type::F32
			| Type::F64
			| Type::Bool
			| Type::Char
			| Type::Enum { .. }
			| Type::Memory { .. }
			| Type::Global { .. }
			| Type::AssociatedType { .. }
			| Type::TypeParam { .. } => return Ok(ty),
		};
		Ok(view.types.intern(rebuilt))
	}

	pub(super) fn find_trait_impl_query(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
	) -> Result<Option<TraitImplLookup>, SolverError> {
		if matches!(view.types.resolve(receiver), Type::Error | Type::Infer) {
			return Err(SolverError::Poisoned);
		}
		let mut assumed = self.check_assumed_trait(
			view,
			assumption_context,
			receiver,
			required_trait,
		)?;
		if assumed == Assumption::Holds
			&& ImplTarget::from_type(view.types.resolve(receiver)).is_none()
		{
			return Ok(Some(TraitImplLookup::Abstract));
		}
		let normalized =
			self.normalize_head_query(view, assumption_context, receiver)?;
		if normalized == TypeIndex::ERROR {
			return Err(SolverError::Poisoned);
		}
		if normalized != receiver {
			assumed = assumed.max(self.check_assumed_trait(
				view,
				assumption_context,
				normalized,
				required_trait,
			)?);
		}
		if let Some(target) =
			ImplTarget::from_type(view.types.resolve(normalized))
		{
			let candidate =
				view.impl_dispatch.trait_candidates(target).iter().find_map(
					|&(trait_index, impl_index)| {
						(trait_index == required_trait).then_some(impl_index)
					},
				);
			if let Some(impl_index) = candidate {
				if let Some(args) = self.match_trait_impl_candidate_query(
					view,
					assumption_context,
					impl_index,
					normalized,
				)? {
					return Ok(Some(TraitImplLookup::Concrete {
						impl_index,
						args,
					}));
				}
			}
		}
		match assumed {
			Assumption::Holds => Ok(Some(TraitImplLookup::Abstract)),
			Assumption::Unproven => Ok(None),
			Assumption::Pending => Err(SolverError::Pending),
		}
	}

	/// Whether the facts in scope prove `ty: required`. Comparison reduces
	/// assumed equalities only, so it cannot depend on impl dispatch. It reads
	/// finished declaration bounds and never demands one: an unfinished table
	/// is `Assumption::Pending`, never an error.
	pub(super) fn check_assumed_trait(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		required: TraitIdx,
	) -> Result<Assumption, SolverError> {
		let recursion_budget = self.state.recursion_budget;
		// Subjects carrying `required`: the scope's facts, then declaration
		// bounds along `ty`'s path and along each path a written equality
		// names (Item: Marker). Paths found there are not followed: a
		// recursive trait describes infinitely many.
		let mut subjects = Vec::new();
		let mut paths = vec![ty];
		let mut readiness;
		{
			let (reader, types) = view.assumptions();
			let mut facts = reader.scoped_facts(assumption_context, types);
			readiness = facts.readiness;
			while let Some(fact) = facts.next(types) {
				match fact.kind {
					AssumptionKind::Trait { trait_index, .. }
						if trait_index == required =>
					{
						subjects.push(fact.subject)
					}
					AssumptionKind::Equality(ImpliedBindingKind::Equals(_)) => {
						paths.push(fact.subject)
					}
					_ => {}
				}
			}
			for path in paths {
				let mut facts =
					reader.subject_facts(path, types, recursion_budget);
				readiness = readiness.and(facts.readiness);
				while let Some(fact) = facts.next(types) {
					if matches!(fact.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == required)
					{
						subjects.push(fact.subject);
					}
				}
			}
		}
		if subjects.contains(&ty) {
			return Ok(Assumption::Holds);
		}
		if !subjects.is_empty() {
			let normalized = match self.normalize_assumed_type_query(
				view,
				assumption_context,
				ty,
			) {
				Ok(normalized) => normalized,
				Err(SolverError::Pending) => return Ok(Assumption::Pending),
				Err(error) => return Err(error),
			};
			for subject in subjects {
				match self.normalize_assumed_type_query(
					view,
					assumption_context,
					subject,
				) {
					Ok(candidate)
						if candidate == normalized
							&& candidate != TypeIndex::ERROR =>
					{
						return Ok(Assumption::Holds);
					}
					Ok(_) => {}
					Err(SolverError::Pending) => {
						readiness = readiness.and(Readiness::Pending)
					}
					Err(error) => return Err(error),
				}
			}
		}
		match readiness {
			Readiness::Ready => Ok(Assumption::Unproven),
			Readiness::Pending => Ok(Assumption::Pending),
			Readiness::Overflowed => Err(SolverError::Overflow),
		}
	}

	/// Match an impl header's complete target against `receiver`, then validate
	/// the arguments against the impl's own parameter bounds. The returned
	/// arguments belong only to this lookup; no declaration frame is changed.
	/// Reads the finished header: one still missing is `Pending`.
	pub(super) fn match_trait_impl_candidate_query(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		impl_index: TraitImplIdx,
		receiver: TypeIndex,
	) -> Result<Option<Box<[TypeIndex]>>, SolverError> {
		let Some(header) = view.trait_impls[usize::from(impl_index)].as_ref()
		else {
			return Err(SolverError::Pending);
		};
		self.match_impl_target_and_bounds(
			view,
			assumption_context,
			header.type_params,
			header.target.inner,
			receiver,
		)
	}

	/// `assumption_context` is the caller's; `impl_env` is the candidate impl's own
	/// parameter frame. The impl's requirements are proved in the caller's
	/// assumptions, never the candidate's.
	fn match_impl_target_and_bounds(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		impl_env: TypeEnvIdx,
		target: TypeIndex,
		receiver: TypeIndex,
	) -> Result<Option<Box<[TypeIndex]>>, SolverError> {
		// Structural matching below compares `receiver`'s nested children
		// against `target`'s pattern directly, with no normalization of its
		// own (`TypeInterner::match_pattern` is `&self`, with no access to
		// this builder's normalization machinery) — so a receiver whose
		// *nested* type argument is still an unreduced projection (e.g.
		// `Wrap<S::Item>`) would otherwise fail to match a concrete impl
		// (`impl Result for Wrap<i32>`) even when that projection reduces to
		// exactly what the impl requires. Every caller of this function
		// (`find_trait_impl`, `type_satisfies_trait`, generic-impl matching)
		// converges here, so normalizing once, here, closes the gap for all
		// of them instead of requiring each to remember it independently.
		let receiver =
			self.normalize_type_query(view, assumption_context, receiver)?;
		let count = if impl_env == TypeEnvIdx::ROOT {
			0
		} else {
			view.type_envs.params(impl_env).len()
		};
		let Some(args) = view
			.types
			.match_impl_target(target, receiver, impl_env, count)
		else {
			return Ok(None);
		};
		for (index, &arg) in args.iter().enumerate() {
			if !view.param_bounds[usize::from(impl_env)][index]
				.facts
				.is_ready()
			{
				return Err(SolverError::Pending);
			}
			let bound_count = view.param_bounds[usize::from(impl_env)][index]
				.facts
				.current()
				.len();
			for bound_index in 0..bound_count {
				let bound = &view.param_bounds[usize::from(impl_env)][index]
					.facts
					.current()[bound_index];
				// Associated equalities and nested requirements are not yet
				// proved. Trait membership alone cannot justify accepting them.
				if !bound.bindings.is_empty() {
					return Ok(None);
				}
				let trait_index = bound.trait_index;
				if self
					.find_trait_impl_query(
						view,
						assumption_context,
						arg,
						trait_index,
					)?
					.is_none()
				{
					return Ok(None);
				}
			}
		}
		Ok(Some(args))
	}

	pub(super) fn projection_equality(
		&mut self,
		view: &mut SolverView<'_>,
		_cx: TypeEnvIdx,
		receiver: TypeIndex,
		trait_index: TraitIdx,
		assoc_type_index: AssocTypeIdx,
	) -> Result<EqualityLookup, SolverError> {
		let mut first = None;
		// No allocation for the usual zero/one-equality lookup. Competing
		// contexts are rare, and only need scalar handles for substitution.
		let mut alternatives = Vec::new();
		let mut ambiguous = false;
		let effective =
			view.effective_bounds(receiver, self.state.recursion_budget);
		let readiness = effective.readiness;
		for entry in effective {
			let bound = entry.bound;
			if bound.trait_index != trait_index {
				continue;
			}
			for binding in &bound.bindings {
				if binding.assoc_type_index != assoc_type_index {
					continue;
				}
				match binding.kind {
					ImpliedBindingKind::Equals(fact) => {
						let candidate = ContextualEquality {
							value: fact.value,
							context: entry.context,
						};
						match first {
							None => first = Some(candidate),
							Some(previous) if previous == candidate => {}
							Some(_) => {
								if !alternatives.contains(&candidate) {
									alternatives.push(candidate);
								}
							}
						}
					}
					ImpliedBindingKind::Ambiguous(_)
					| ImpliedBindingKind::Conflicting => ambiguous = true,
					ImpliedBindingKind::Bound => {}
				}
			}
		}
		match readiness {
			Readiness::Ready => {}
			Readiness::Pending => return Err(SolverError::Pending),
			Readiness::Overflowed => return Err(SolverError::Overflow),
		}
		if ambiguous {
			return Ok(EqualityLookup::Ambiguous);
		}
		let Some(first) = first else {
			return Ok(EqualityLookup::Absent);
		};
		let value = self.instantiate_equality(view, first);
		for alternative in alternatives {
			if self.instantiate_equality(view, alternative) != value {
				return Ok(EqualityLookup::Ambiguous);
			}
		}
		Ok(EqualityLookup::Known(value))
	}

	fn instantiate_equality(
		&mut self,
		view: &mut SolverView<'_>,
		fact: ContextualEquality,
	) -> TypeIndex {
		match fact.context {
			Some(context) => view.types.substitute(
				fact.value,
				&Substitution {
					env: context.env,
					args: &[context.receiver],
				},
			),
			None => fact.value,
		}
	}
}

/// `TypeContext` keeps the entry points the rest of `tir` calls; each lends the
/// solver its view and forwards. Impl-based entry points also check that no
/// signature is being built: reducing by impl reads finished signatures, while
/// assumption-only reduction reads declared bounds and may run mid-construction.
impl TypeContext<'_, '_, '_> {
	fn solver_and_view(&mut self) -> (&mut Solver, SolverView<'_>) {
		(
			&mut self.solver,
			SolverView {
				types: &mut self.types,
				defs: self.defs,
				impl_dispatch: self.impl_dispatch,
				traits: &self.traits,
				trait_impls: &self.trait_impls,
				assoc_types: &self.assoc_types,
				param_bounds: &self.param_bounds,
				type_envs: &self.type_envs,
			},
		)
	}

	pub(super) fn normalize_head_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<TypeIndex, SolverError> {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		solver.normalize_head_query(&mut view, assumption_context, ty)
	}

	pub(super) fn normalize_type_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<TypeIndex, SolverError> {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		solver.normalize_type_query(&mut view, assumption_context, ty)
	}

	pub(super) fn normalize_assumed_type_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<TypeIndex, SolverError> {
		let (solver, mut view) = self.solver_and_view();
		solver.normalize_assumed_type_query(&mut view, assumption_context, ty)
	}

	pub(super) fn find_trait_impl_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
	) -> Result<Option<TraitImplLookup>, SolverError> {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		solver.find_trait_impl_query(
			&mut view,
			assumption_context,
			receiver,
			required_trait,
		)
	}

	pub(super) fn check_assumed_trait(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		required: TraitIdx,
	) -> Result<Assumption, SolverError> {
		let (solver, mut view) = self.solver_and_view();
		solver.check_assumed_trait(&mut view, assumption_context, ty, required)
	}

	pub(super) fn match_impl_target_and_bounds(
		&mut self,
		assumption_context: TypeEnvIdx,
		impl_env: TypeEnvIdx,
		target: TypeIndex,
		receiver: TypeIndex,
	) -> Result<Option<Box<[TypeIndex]>>, SolverError> {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		solver.match_impl_target_and_bounds(
			&mut view,
			assumption_context,
			impl_env,
			target,
			receiver,
		)
	}

	/// Test conveniences over the queries: an unfinished fact stays symbolic, a
	/// failure becomes `ERROR`, and a divergence is reported at `site`. No
	/// production path normalizes this way: lowering stores types as written.
	#[cfg(test)]
	pub(super) fn normalize_head(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		site: SourceSpan,
	) -> TypeIndex {
		let result = self.normalize_head_query(assumption_context, ty);
		self.settle(result, ty, site)
	}

	#[cfg(test)]
	pub(super) fn normalize_type(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		site: SourceSpan,
	) -> TypeIndex {
		let result = self.normalize_type_query(assumption_context, ty);
		self.settle(result, ty, site)
	}

	#[cfg(test)]
	fn settle(
		&mut self,
		result: Result<TypeIndex, SolverError>,
		ty: TypeIndex,
		site: SourceSpan,
	) -> TypeIndex {
		match self.report_solver_error(result, site) {
			Ok(result) => result,
			Err(SolverError::Pending) => ty,
			Err(_) => TypeIndex::ERROR,
		}
	}
}

const IMPL_WHILE_BUILDING: &str =
	"impl-based normalization cannot run while a signature is being built";
