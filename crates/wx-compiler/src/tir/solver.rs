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
pub(super) enum Unsolved {
	/// A fact the answer depends on is not final yet (declarations are still
	/// being built). It is not evidence of absence; ask again once construction
	/// has advanced.
	Pending,
	/// There is no answer, and the construct that wrote the input owns the
	/// report: an erroneous receiver, a trait the type does not implement, a
	/// provider that supplies nothing, or a check that already reported its
	/// violation. Consumers recover silently.
	Failed,
	/// The recursion budget ran out. The asking site reports it.
	Overflow,
	/// A projection requires itself. The asking site reports it.
	Cycle(Box<Cycle>),
}

/// The loop a normalization closed on itself.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Cycle {
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
	/// The value has no meaning: a cycle, an exhausted budget, or it derives
	/// from a value that has none. `Some` holds the failure (`Overflow` or
	/// `Cycle`) this definition owns and its check reports; `None` derives from
	/// a failure reported elsewhere.
	Poisoned(Option<Unsolved>),
}

/// A type reduced as far as its mode asks. The result can still be an abstract
/// projection; that is a valid answer, not an unfinished one.
pub(super) type Normalized = Result<TypeIndex, Unsolved>;

/// One frame of the solver's stack: work started and not yet finished, the
/// solver's counterpart of a `query_stack` frame. The stack is the path a
/// cycle is read from.
enum SolverFrame {
	/// A projection being reduced. Evidence comparison and provider reduction
	/// have distinct cycle keys.
	Projection {
		mode: Mode,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
	},
	/// The frame above it was justified by a hypothesis (an equality written in
	/// a bound), not by a definition. A loop through one is a tautology that
	/// leaves the projection abstract; a loop through definitions only is an
	/// error.
	Assumption,
	/// An impl member's value being judged (`Solver::assoc_value`), selected by
	/// `requested_by` (`None` when its own check asked). The member's verdict is
	/// `InProgress` while this frame is on the stack, as a signature's query state
	/// is while its frame is on `query_stack`. The judgement counts its depth
	/// from zero, so running out of budget is a verdict on the definition alone;
	/// `outer_depth` is the depth to restore once it is done.
	Judgement {
		member: ImplMember,
		requested_by: Option<TypeIndex>,
		outer_depth: usize,
	},
}

/// The derivation currently being computed. Shared across re-entrant
/// signature queries and value judgements, not recreated per API call, so
/// cycle detection sees every frame of a loop, whichever judgement it crosses.
struct SolverState {
	frames: Vec<SolverFrame>,
	/// How deeply the innermost judgement's derivation (or the request, outside
	/// any judgement) is nested; the budget is measured against it.
	depth: usize,
	/// Roll back an assumed equality chain that made no finite progress.
	blocked_at: Option<usize>,
}

impl Default for SolverState {
	fn default() -> Self {
		Self {
			frames: Vec::new(),
			depth: 0,
			blocked_at: None,
		}
	}
}

impl SolverState {
	/// No frame is open: no projection, assumption or judgement is in flight, so
	/// no rollback can be pending either. An answer asked for now cannot depend
	/// on anything above it.
	fn is_idle(&self) -> bool {
		self.frames.is_empty()
	}
}

/// The engine that normalizes types and selects impls, with everything it
/// keeps: the derivation in flight, the finished-answer cache and the rule for
/// when it may be used, and the verdicts on impl members' values.
pub(super) struct Solver {
	/// The recursion budget: how deeply one request may nest. Fixed
	/// configuration, not state; only tests change it.
	limit: usize,
	state: SolverState,
	/// Only `Ok` answers are stored. `Pending` means a fact is not final yet,
	/// and `Failed` is not a permanent verdict (a budget overflow can be
	/// retried), so neither is remembered. Every
	/// stored answer was final when computed, so no "facts are final" switch is
	/// needed.
	completed: HashMap<(TypeEnvIdx, TypeIndex, Mode), TypeIndex>,
	/// The verdict on each impl member asked about; absent is `Unchecked`.
	/// A member is `InProgress` exactly while its `SolverFrame::Judgement` is on
	/// the stack.
	pub(super) values: HashMap<ImplMember, AssocValue>,
}

impl Solver {
	pub(super) fn new() -> Self {
		Self {
			limit: 128,
			state: SolverState::default(),
			completed: HashMap::new(),
			values: HashMap::new(),
		}
	}

	pub(super) fn verdict(&self, member: ImplMember) -> &AssocValue {
		self.values.get(&member).unwrap_or(&AssocValue::Unchecked)
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
	/// through a hypothesis, it is a tautology the derivation itself blocks.
	fn assoc_value(
		&mut self,
		view: &mut SolverView<'_>,
		member: ImplMember,
		requested_by: Option<TypeIndex>,
	) -> Normalized {
		match self.verdict(member) {
			AssocValue::Unchecked => {}
			AssocValue::InProgress => {
				return self.reenter_judgement(view, member, requested_by);
			}
			AssocValue::Resolved => return view.impl_member_value(member),
			AssocValue::Poisoned(_) => return Err(Unsolved::Failed),
		}
		let value = match view.impl_member_value(member) {
			Ok(value) => value,
			// No value (lowering failed and reported, or neither the impl nor the
			// trait supplies one, which conformance owns); nothing to judge.
			Err(Unsolved::Failed) => {
				self.values.insert(member, AssocValue::Poisoned(None));
				return Err(Unsolved::Failed);
			}
			Err(error) => return Err(error),
		};
		let scope = view.trait_impls[usize::from(member.impl_index)]
			.as_ref()
			.expect("a member with a value has a resolved impl header")
			.self_scope;
		self.values.insert(member, AssocValue::InProgress);
		let index = self.state.frames.len();
		self.state.frames.push(SolverFrame::Judgement {
			member,
			requested_by,
			outer_depth: std::mem::take(&mut self.state.depth),
		});
		let result = self.normalize(view, scope, value, Mode::Deep);
		let Some(SolverFrame::Judgement { outer_depth, .. }) =
			self.state.frames.pop()
		else {
			unreachable!("the judgement is the innermost frame once it is done")
		};
		self.state.depth = outer_depth;
		// A tautology further out is unwinding through this judgement, which was
		// cut short: there is no verdict yet, so it is judged again when asked.
		if self.state.blocked_at.is_some_and(|blocked| blocked < index) {
			self.values.remove(&member);
			return Ok(value);
		}
		let (verdict, answer) = match result {
			Ok(_) => (AssocValue::Resolved, Ok(value)),
			Err(Unsolved::Pending) => {
				(AssocValue::Unchecked, Err(Unsolved::Pending))
			}
			Err(Unsolved::Failed) => {
				(AssocValue::Poisoned(None), Err(Unsolved::Failed))
			}
			// Another member owns the loop. Its own judgement, further out,
			// answers `Failed` once it has kept the loop, so members past it
			// unwind as derived failures.
			Err(Unsolved::Cycle(cycle))
				if cycle.owner.is_some_and(|owner| owner != member) =>
			{
				(AssocValue::Poisoned(None), Err(Unsolved::Cycle(cycle)))
			}
			// The budget counts from this judgement, so running out is a verdict
			// on the definition, like a cycle.
			Err(owned @ (Unsolved::Overflow | Unsolved::Cycle(_))) => {
				(AssocValue::Poisoned(Some(owned)), Err(Unsolved::Failed))
			}
		};
		self.values.insert(member, verdict);
		answer
	}

	/// `member` was reached again while its judgement is on the stack. A
	/// hypothesis on the way back makes the loop a tautology, not an error: the
	/// value as written goes on, and the derivation blocks once its projections
	/// repeat (`projection_cycle`), as it does for any loop through a
	/// hypothesis. Through definitions only, the loop is a cycle, read from the
	/// stack and owned by its first defined member.
	fn reenter_judgement(
		&mut self,
		view: &mut SolverView<'_>,
		member: ImplMember,
		requested_by: Option<TypeIndex>,
	) -> Normalized {
		let start = self
			.state
			.frames
			.iter()
			.position(|frame| {
				matches!(frame, SolverFrame::Judgement { member: judged, .. } if *judged == member)
			})
			.expect("an in-progress judgement is on the stack");
		let loop_frames = &self.state.frames[start..];
		if loop_frames
			.iter()
			.any(|frame| matches!(frame, SolverFrame::Assumption))
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
		Err(Unsolved::Cycle(Box::new(Cycle {
			projection: steps[0],
			steps: steps.into_boxed_slice(),
			owner: Some(owner),
		})))
	}

	/// Bound readers traverse receiver structure within the same work limit.
	pub(super) fn remaining_depth(&self) -> usize {
		self.limit - self.state.depth
	}

	/// A finished answer, if this request may be served from the cache. With a
	/// frame open the answer can depend on it (cycle and rollback state, an
	/// open judgement), so the cache is bypassed entirely; with none it is a
	/// function of the key alone.
	fn cached(
		&self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		mode: Mode,
	) -> Option<TypeIndex> {
		if !self.state.is_idle() {
			return None;
		}
		self.completed.get(&(assumption_context, ty, mode)).copied()
	}

	/// Remember an answer under the same rule. Called after the request has
	/// settled, so the state is idle exactly when no frame enclosed it.
	fn remember(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		mode: Mode,
		result: &Normalized,
	) {
		if self.state.is_idle()
			&& let Ok(normalized) = *result
		{
			self.completed
				.insert((assumption_context, ty, mode), normalized);
		}
	}

	#[cfg(test)]
	pub(super) fn set_limit_for_test(&mut self, limit: usize) {
		self.limit = limit;
	}
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Mode {
	Head,
	Deep,
	/// Reduce only assumed equalities, including nested type structure.
	/// Comparing evidence must not recursively select the impl being proved.
	Assumptions,
}

/// What the assumptions in scope say a projection equals. Unfinished facts are
/// not an answer (`Unsolved::Pending`), and neither absence nor competing
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

	fn effective_bounds(
		&self,
		receiver: TypeIndex,
		remaining_depth: usize,
	) -> EffectiveBounds<'a> {
		self.reader()
			.effective_bounds(&*self.types, receiver, remaining_depth)
	}

	fn has_effective_trait(
		&self,
		receiver: TypeIndex,
		trait_index: TraitIdx,
		remaining_depth: usize,
	) -> bool {
		let bounds = self.effective_bounds(receiver, remaining_depth);
		if bounds.reflexive_trait == Some(trait_index) {
			return true;
		}
		for entry in bounds {
			if entry.bound.trait_index == trait_index {
				return true;
			}
		}
		false
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
	fn assoc_type_value(&self, provider: AssocTypeIdx) -> Normalized {
		let Some(signature) = self.assoc_types[usize::from(provider)].as_ref()
		else {
			return Err(Unsolved::Pending);
		};
		match signature.value {
			Some(TypeIndex::ERROR) => Err(Unsolved::Failed),
			Some(value) => Ok(value),
			None => unreachable!("an impl provider has a value"),
		}
	}

	/// `member`'s value in its impl's environment, as written: the impl's own,
	/// or the trait's default with `Self` the impl's target. Readers go through
	/// `Solver::assoc_value`, which judges it.
	fn impl_member_value(&mut self, member: ImplMember) -> Normalized {
		let Some(header) =
			self.trait_impls[usize::from(member.impl_index)].as_ref()
		else {
			return Err(Unsolved::Pending);
		};
		let target = header.target.inner;
		match self.defs.select_trait_member(
			member.impl_index,
			MemberKind::AssociatedType(member.declaration),
		) {
			TraitMemberSelection::Impl(MemberKind::AssociatedType(
				provider,
			)) => self.assoc_type_value(provider),
			TraitMemberSelection::Impl(_) => Err(Unsolved::Failed),
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
	fn assoc_type_default(&self, declaration: AssocTypeIdx) -> Normalized {
		let Some(signature) =
			self.assoc_types[usize::from(declaration)].as_ref()
		else {
			return Err(Unsolved::Pending);
		};
		match signature.value {
			Some(TypeIndex::ERROR) | None => Err(Unsolved::Failed),
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
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Normalized {
		self.normalize(view, assumption_context, ty, Mode::Head)
	}

	pub(super) fn normalize_type_query(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Normalized {
		self.normalize(view, assumption_context, ty, Mode::Deep)
	}

	pub(super) fn normalize_assumed_type_query(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Normalized {
		self.normalize(view, assumption_context, ty, Mode::Assumptions)
	}
}

impl Solver {
	/// The cache layer around `normalize_uncached`; when the cache may be used
	/// is decided by `Solver`.
	fn normalize(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		mode: Mode,
	) -> Normalized {
		if let Some(hit) = self.cached(assumption_context, ty, mode) {
			return Ok(hit);
		}
		let enclosed = !self.state.is_idle();
		let result =
			self.normalize_uncached(view, assumption_context, ty, mode);
		// A request that started with nothing in flight leaves nothing behind.
		debug_assert!(enclosed || self.state.is_idle());
		debug_assert!(enclosed || self.state.blocked_at.is_none());
		self.remember(assumption_context, ty, mode, &result);
		result
	}

	fn normalize_uncached(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		mode: Mode,
	) -> Normalized {
		if self.state.blocked_at.is_some() {
			return Ok(ty);
		}
		if self.state.depth == self.limit {
			// Budget exhaustion is a failure the asking site reports, never an
			// unfinished fact; a top-level request can be retried with more.
			return Err(Unsolved::Overflow);
		}
		self.state.depth += 1;
		let result = if matches!(
			view.types.resolve(ty),
			Type::AssocTypeProjection { .. }
		) {
			self.normalize_projection(view, assumption_context, ty, mode)
		} else {
			match mode {
				Mode::Head => Ok(ty),
				Mode::Deep | Mode::Assumptions => {
					self.normalize_children(view, assumption_context, ty, mode)
				}
			}
		};
		self.state.depth -= 1;
		result
	}

	fn normalize_projection(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		mode: Mode,
	) -> Normalized {
		if self.projection_cycle(assumption_context, projection, mode)? {
			return Ok(projection);
		}
		self.state.frames.push(SolverFrame::Projection {
			mode,
			assumption_context,
			projection,
		});
		// Keep the frame active across receiver normalization, provider queries,
		// and traversal of the resulting type, including compound results.
		let result =
			self.reduce_projection(view, assumption_context, projection, mode);
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
		mode: Mode,
	) -> Normalized {
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
					return self.reduce_to_assumed(
						view,
						assumption_context,
						projection,
						value,
						mode,
					);
				}
				EqualityLookup::Absent | EqualityLookup::Ambiguous => {}
			}
		}
		let next_base = self.normalize(view, assumption_context, base, mode)?;
		if next_base == TypeIndex::ERROR {
			return Err(Unsolved::Failed);
		}
		let projection = if next_base == base {
			projection
		} else {
			let next = view.types.intern(Type::AssocTypeProjection {
				base: next_base,
				trait_index,
				assoc_type_index,
			});
			if self.projection_cycle(assumption_context, next, mode)? {
				return Ok(projection);
			}
			let Some(SolverFrame::Projection {
				projection: current,
				..
			}) = self.state.frames.last_mut()
			else {
				unreachable!("the reducing projection is the innermost frame")
			};
			*current = next;
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
				EqualityLookup::Known(value) => self.reduce_to_assumed(
					view,
					assumption_context,
					projection,
					value,
					mode,
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
		if mode == Mode::Assumptions {
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
			return Err(Unsolved::Failed);
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
		self.normalize(view, assumption_context, instantiated, mode)
	}

	/// The assumptions in scope give `projection` the value `value`. Evidence
	/// that restates the projection itself leaves it abstract.
	fn reduce_to_assumed(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		value: TypeIndex,
		mode: Mode,
	) -> Normalized {
		if value == projection {
			return Ok(projection);
		}
		self.state.frames.push(SolverFrame::Assumption);
		let result = self.normalize(view, assumption_context, value, mode);
		self.state.frames.pop();
		result
	}

	fn projection_cycle(
		&mut self,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		mode: Mode,
	) -> Result<bool, Unsolved> {
		let Some(start) = self.state.frames.iter().position(|frame| {
			matches!(frame, SolverFrame::Projection {
					mode: step_mode,
					assumption_context: step_context,
					projection: step_projection,
				} if *step_context == assumption_context
					&& *step_projection == projection
					&& *step_mode == mode)
		}) else {
			return Ok(false);
		};
		let loop_frames = &self.state.frames[start..];
		if loop_frames
			.iter()
			.any(|frame| matches!(frame, SolverFrame::Assumption))
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
				SolverFrame::Projection { projection, .. } => Some(*projection),
				SolverFrame::Assumption | SolverFrame::Judgement { .. } => None,
			})
			.collect();
		Err(Unsolved::Cycle(Box::new(Cycle {
			projection,
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
		mode: Mode,
	) -> Normalized {
		let rebuilt = match view.types.resolve(ty).clone() {
			Type::Tuple { mut elements } => {
				for element in elements.iter_mut() {
					*element = self.normalize(
						view,
						assumption_context,
						*element,
						mode,
					)?;
				}
				Type::Tuple { elements }
			}
			Type::Struct {
				struct_index,
				mut type_args,
			} => {
				for arg in type_args.iter_mut() {
					*arg =
						self.normalize(view, assumption_context, *arg, mode)?;
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
					*arg =
						self.normalize(view, assumption_context, *arg, mode)?;
				}
				Type::FunctionItem {
					func_index,
					type_args,
				}
			}
			Type::Function { mut params, result } => {
				for param in params.iter_mut() {
					*param =
						self.normalize(view, assumption_context, *param, mode)?;
				}
				Type::Function {
					params,
					result: self.normalize(
						view,
						assumption_context,
						result,
						mode,
					)?,
				}
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => Type::Pointer {
				to: self.normalize(view, assumption_context, to, mode)?,
				memory: self.normalize(
					view,
					assumption_context,
					memory,
					mode,
				)?,
				ownership,
			},
			Type::Array {
				of,
				size,
				memory,
				ownership,
			} => Type::Array {
				of: self.normalize(view, assumption_context, of, mode)?,
				size,
				memory: self.normalize(
					view,
					assumption_context,
					memory,
					mode,
				)?,
				ownership,
			},
			Type::Slice {
				of,
				memory,
				ownership,
			} => Type::Slice {
				of: self.normalize(view, assumption_context, of, mode)?,
				memory: self.normalize(
					view,
					assumption_context,
					memory,
					mode,
				)?,
				ownership,
			},
			Type::AssocTypeProjection { .. } => unreachable!(
				"projections are handled before structural traversal"
			),
			Type::Error
			| Type::Infer
			| Type::Unit
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
	) -> Result<Option<TraitImplLookup>, Unsolved> {
		if matches!(view.types.resolve(receiver), Type::Error | Type::Infer) {
			return Err(Unsolved::Failed);
		}
		let mut assumed = self.check_assumed_trait(
			view,
			assumption_context,
			receiver,
			required_trait,
		);
		if let Err(error) = &assumed
			&& *error != Unsolved::Pending
		{
			return Err(error.clone());
		}
		if assumed == Ok(true)
			&& ImplTarget::from_type(view.types.resolve(receiver)).is_none()
		{
			return Ok(Some(TraitImplLookup::Abstract));
		}
		let normalized =
			self.normalize_head_query(view, assumption_context, receiver)?;
		if normalized == TypeIndex::ERROR {
			return Err(Unsolved::Failed);
		}
		if normalized != receiver {
			match self.check_assumed_trait(
				view,
				assumption_context,
				normalized,
				required_trait,
			) {
				Ok(true) => assumed = Ok(true),
				Ok(false) => {}
				Err(Unsolved::Pending) => {
					if assumed != Ok(true) {
						assumed = Err(Unsolved::Pending)
					}
				}
				Err(error) => return Err(error),
			}
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
		assumed.map(|proven| proven.then_some(TraitImplLookup::Abstract))
	}

	/// Direct facts are the fast path. Otherwise compare the requested type
	/// with subjects that carry this trait in the active scope. Comparison
	/// reduces assumed equalities only, so it cannot depend on impl dispatch.
	/// It reads finished declaration bounds and never demands one: an unfinished
	/// table is `Pending`.
	pub(super) fn check_assumed_trait(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		required: TraitIdx,
	) -> Result<bool, Unsolved> {
		let mut readiness = Readiness::Ready;
		if matches!(
			view.types.resolve(ty),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			readiness =
				view.effective_bounds(ty, self.remaining_depth()).readiness;
			if view.has_effective_trait(ty, required, self.remaining_depth()) {
				return Ok(true);
			}
		}
		// Retain only scalar subjects of relevant memberships. The borrowed
		// cursor must be released before normalization can demand signatures.
		let mut subjects = Vec::new();
		let mut equality_subjects = Vec::new();
		{
			let (reader, types) = view.assumptions();
			let mut facts = reader.scoped_facts(assumption_context, types);
			readiness = readiness.and(facts.readiness);
			while let Some(fact) = facts.next(types) {
				if matches!(
					fact.kind,
					AssumptionKind::Equality(
						super::bounds::ImpliedBindingKind::Equals(_)
					)
				) {
					equality_subjects.push(fact.subject);
				}
				if matches!(fact.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == required)
				{
					if fact.subject == ty {
						return Ok(true);
					}
					if !subjects.contains(&fact.subject) {
						subjects.push(fact.subject);
					}
				}
			}
		}
		// A written equality also gives a finite projection path on which
		// associated declaration bounds may supply evidence (Item: Marker).
		// Read those paths without recursively expanding every declaration.
		for subject in equality_subjects {
			let remaining_depth = self.remaining_depth();
			let (reader, types) = view.assumptions();
			let mut facts =
				reader.subject_facts(subject, types, remaining_depth);
			readiness = readiness.and(facts.readiness);
			while let Some(fact) = facts.next(types) {
				if matches!(fact.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == required)
				{
					if fact.subject == ty {
						return Ok(true);
					}
					if !subjects.contains(&fact.subject) {
						subjects.push(fact.subject);
					}
				}
			}
		}
		if !subjects.is_empty() {
			let normalized = self.normalize_assumed_type_query(
				view,
				assumption_context,
				ty,
			)?;
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
						return Ok(true);
					}
					Ok(_) => {}
					Err(Unsolved::Pending) => {
						readiness = readiness.and(Readiness::Pending)
					}
					Err(error) => return Err(error.into()),
				}
			}
		}
		match readiness {
			Readiness::Ready => Ok(false),
			Readiness::Pending => Err(Unsolved::Pending),
			Readiness::Overflowed => Err(Unsolved::Overflow),
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
	) -> Result<Option<Box<[TypeIndex]>>, Unsolved> {
		let Some(header) = view.trait_impls[usize::from(impl_index)].as_ref()
		else {
			return Err(Unsolved::Pending);
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
	) -> Result<Option<Box<[TypeIndex]>>, Unsolved> {
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
			view.type_envs.frame(impl_env).len()
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
				return Err(Unsolved::Pending);
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
	) -> Result<EqualityLookup, Unsolved> {
		let mut first = None;
		// No allocation for the usual zero/one-equality lookup. Competing
		// contexts are rare, and only need scalar handles for substitution.
		let mut alternatives = Vec::new();
		let mut ambiguous = false;
		let effective = view.effective_bounds(receiver, self.remaining_depth());
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
			Readiness::Pending => return Err(Unsolved::Pending),
			Readiness::Overflowed => return Err(Unsolved::Overflow),
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

	/// Judges `member`'s value for the definition's own check. `Err` with
	/// `Overflow` or `Cycle` is a failure this definition owns and must report;
	/// any other failure is reported elsewhere.
	pub(super) fn judge_assoc_value(
		&mut self,
		member: ImplMember,
	) -> Result<(), Unsolved> {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		if let Err(Unsolved::Pending) =
			solver.assoc_value(&mut view, member, None)
		{
			return Err(Unsolved::Pending);
		}
		match solver.verdict(member) {
			AssocValue::Resolved => Ok(()),
			AssocValue::Poisoned(Some(owned)) => Err(owned.clone()),
			AssocValue::Poisoned(None) => Err(Unsolved::Failed),
			AssocValue::Unchecked | AssocValue::InProgress => {
				unreachable!("a finished judgement has a verdict")
			}
		}
	}

	pub(super) fn normalize_head_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Normalized {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		solver.normalize_head_query(&mut view, assumption_context, ty)
	}

	pub(super) fn normalize_type_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Normalized {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		solver.normalize_type_query(&mut view, assumption_context, ty)
	}

	pub(super) fn normalize_assumed_type_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Normalized {
		let (solver, mut view) = self.solver_and_view();
		solver.normalize_assumed_type_query(&mut view, assumption_context, ty)
	}

	pub(super) fn find_trait_impl_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		receiver: TypeIndex,
		required_trait: TraitIdx,
	) -> Result<Option<TraitImplLookup>, Unsolved> {
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
	) -> Result<bool, Unsolved> {
		let (solver, mut view) = self.solver_and_view();
		solver.check_assumed_trait(&mut view, assumption_context, ty, required)
	}

	pub(super) fn match_impl_target_and_bounds(
		&mut self,
		assumption_context: TypeEnvIdx,
		impl_env: TypeEnvIdx,
		target: TypeIndex,
		receiver: TypeIndex,
	) -> Result<Option<Box<[TypeIndex]>>, Unsolved> {
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
		result: Normalized,
		ty: TypeIndex,
		site: SourceSpan,
	) -> TypeIndex {
		match self.report_unsolved(result, site) {
			Ok(result) => result,
			Err(Unsolved::Pending) => ty,
			Err(_) => TypeIndex::ERROR,
		}
	}
}

const IMPL_WHILE_BUILDING: &str =
	"impl-based normalization cannot run while a signature is being built";
