//! The solver: associated-type normalization and impl selection, which recurse
//! into each other and so are one engine, `Solver`. It reads the world through
//! a `SolverView` lent by `TypeContext::solver_and_view`, which names every
//! table it may touch.
//!
//! Declaration identity stays in projections; abstract equalities come from
//! equality clauses; concrete values come from selected impl members, whose
//! values the solver judges once (`Verdict`). Evidence comparison uses the
//! same traversal and budget, reducing assumed equalities without selecting
//! providers. Structural substitution remains independent in `types.rs`.

use rustc_hash::FxHashMap;

use crate::ast::StringInterner;
#[cfg(test)]
use crate::diagnostics::SourceSpan;

use super::body::ConstBody;
use super::bounds::{
	BindingRef, BoundClauses, BoundId, ClauseArena, ClauseTables, Readiness,
	SelfSubstitution, known_distinct,
};
use super::defs::{
	AssocTypeIdx, ConstIdx, DefinitionRegistry, MemberKind, TraitIdx,
	TraitImplIdx,
};
use super::eval::{Allocation, ConstValueState, Unevaluable, value_bits};
use super::impls::{ImplDispatch, ImplTarget};
use super::layout::Layouts;
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::signatures::{
	AssocTypeSignature, ConstantSignature, EnumSignature,
	InherentImplSignature, ParamBounds, StructSignature, TraitImplSignature,
	TraitSignature, TypeContext,
};
use super::types::{
	ImplKind, Substitution, Type, TypeEnvArena, TypeEnvIdx, TypeIndex,
	TypeInterner, TypeList,
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

/// Why a bound does not hold, for the check that owns it to report.
pub(super) enum Unsatisfied {
	/// `subject` lacks `trait_index`, which the bound `source` requires.
	Trait {
		subject: TypeIndex,
		trait_index: TraitIdx,
		source: BoundId,
	},
	/// The projection the equality `source` names has another value.
	Equality {
		projection: TypeIndex,
		found: TypeIndex,
		expected: TypeIndex,
		source: BindingRef,
	},
}

/// One Wasm value type (`valtype`).
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ValType {
	I32,
	I64,
	F32,
	F64,
	V128,
	FuncRef,
	ExternRef,
}

/// One value in a type's layout (`Solver::value_layout`).
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum LayoutValue {
	Known(ValType),
	/// One value whose kind its instantiation decides: a type parameter or
	/// a projection that does not reduce, assumed `ValueType`, or an address
	/// into a memory not known yet.
	Abstract(TypeIndex),
}

/// The value of `assoc_type_index` for `receiver`, whose trait the compiler
/// answers from its structure: `func(A) -> R`'s `Call::Args` is `A` and its
/// `Call::Result` is `R`.
fn builtin_assoc_value(
	view: &SolverView<'_>,
	receiver: TypeIndex,
	assoc_type_index: AssocTypeIdx,
) -> Option<TypeIndex> {
	let Type::FunctionRef { param, result } = *view.types.resolve(receiver)
	else {
		return None;
	};
	let intrinsics = &view.defs.intrinsics;
	if Some(assoc_type_index) == intrinsics.call_args {
		Some(param)
	} else if Some(assoc_type_index) == intrinsics.call_result {
		Some(result)
	} else {
		None
	}
}

/// `ty`, a projection path over `root`, with `root` replaced by `onto`.
fn rebase(
	types: &mut TypeInterner,
	ty: TypeIndex,
	root: TypeIndex,
	onto: TypeIndex,
) -> TypeIndex {
	if ty == root {
		return onto;
	}
	let Type::AssocTypeProjection {
		base,
		trait_index,
		assoc_type_index,
	} = *types.resolve(ty)
	else {
		unreachable!("a clause's subject is a projection path over its root")
	};
	let base = rebase(types, base, root, onto);
	types.intern(Type::AssocTypeProjection {
		base,
		trait_index,
		assoc_type_index,
	})
}

/// Whether a step of `ty`'s projection path is a membership in `failed`.
fn through_failed(
	types: &TypeInterner,
	mut ty: TypeIndex,
	failed: &[(TypeIndex, TraitIdx)],
) -> bool {
	while let Type::AssocTypeProjection {
		base, trait_index, ..
	} = *types.resolve(ty)
	{
		if failed.contains(&(base, trait_index)) {
			return true;
		}
		ty = base;
	}
	false
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
	/// The definition in the loop that owns it: the first defined, so the
	/// report does not depend on which was asked for first. `None` for a loop
	/// found within one derivation.
	pub(super) owner: Option<Definition>,
	/// For a loop an impl's requirements own: the bound being proved when it
	/// closed, where the impl's check reports it.
	pub(super) bound: Option<BoundId>,
}

/// A definition the solver judges once, in its own scope, and which owns the
/// loops through it (`Verdict`). These are the definitions on the solver's own
/// path: a projection reduces through an impl member's value, and selecting
/// an impl proves its requirements. Another declaration's bounds are proved
/// only where it is used, by the obligation that uses it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Definition {
	/// An impl member's value.
	Member(ImplMember),
	/// An impl's requirements (the bounds on its parameters), proved for its
	/// own parameters in its own scope: the instantiation every other one is
	/// a substitution of.
	Requirements(ImplKind),
}

impl Definition {
	/// Definition order, which picks a loop's owner: an impl's requirements
	/// come before its members, as its header comes before its body.
	fn order(self) -> (u8, usize, u8, usize) {
		match self {
			Self::Requirements(ImplKind::Trait(index)) => {
				(0, usize::from(index), 0, 0)
			}
			Self::Member(member) => {
				let (impl_index, declaration) = member.order();
				(0, impl_index, 1, declaration)
			}
			Self::Requirements(ImplKind::Inherent(index)) => {
				(1, usize::from(index), 0, 0)
			}
		}
	}
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

/// What the solver has concluded about a `Definition`, judged on first use
/// (`Solver::assoc_value`, `Solver::requirements_verdict`). The signatures
/// keep what was written.
///
/// A loop through definitions has no root cause, so the definitions own it:
/// the first defined keeps the failure for its own check to report, and
/// every other reader of a poisoned definition fails silently, as it would
/// for a value that failed to lower. The verdict depends on the definitions
/// alone, so it does not matter who asks first.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Verdict {
	/// Not asked for yet.
	Unchecked,
	/// Being judged; reaching it again closes a loop through definitions.
	InProgress,
	/// A member's value normalizes, or an impl's requirements are decided, in
	/// the impl's own scope. Readers still take what is written and judge it
	/// in their own context.
	Resolved,
	/// The value has no meaning because it derives from a failure another
	/// construct owns and reports.
	Poisoned,
	/// The judgement ran out of budget. The definition owns this, and its
	/// check reports it.
	Overflowed,
	/// The definition requires itself through definitions only, and owns the
	/// loop. Its check reports it.
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
pub(super) enum SolverFrame {
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
	/// A definition: an impl's requirements being judged for its own
	/// parameters in its own scope (`impl<T: Tr where { A = W<T> }> ..`
	/// proves `T: Tr` and `T::A = W<T>`). Selecting the impl for those same
	/// parameters there again closes a loop; for other arguments it is
	/// ordinary recursion (`impl<T: Tr> Tr for Box<T>`). `bound` is the bound
	/// being proved, where a loop it owns is reported; the budget is the
	/// judgement's own, as for a member.
	Requirements {
		impl_kind: ImplKind,
		bound: Option<BoundId>,
		outer_budget: usize,
	},
	/// A constant being evaluated (`Solver::const_value`). Its state is
	/// `InProgress` while this frame is on the stack; reading it again closes
	/// a loop through constants. The budget is the evaluation's own, as for
	/// a judgement.
	Evaluation {
		constant: ConstIdx,
		outer_budget: usize,
	},
}

/// The projections in flight on `frames`, outermost first.
fn projection_steps(frames: &[SolverFrame]) -> Vec<TypeIndex> {
	frames
		.iter()
		.filter_map(|frame| match frame {
			SolverFrame::Projection(step) => Some(step.ty),
			SolverFrame::Equality
			| SolverFrame::Judgement { .. }
			| SolverFrame::Requirements { .. }
			| SolverFrame::Evaluation { .. } => None,
		})
		.collect()
}

/// The first defined definition on a loop's frames.
fn loop_owner(frames: &[SolverFrame]) -> Option<Definition> {
	frames
		.iter()
		.filter_map(|frame| match *frame {
			SolverFrame::Judgement { member, .. } => {
				Some(Definition::Member(member))
			}
			SolverFrame::Requirements { impl_kind, .. } => {
				Some(Definition::Requirements(impl_kind))
			}
			SolverFrame::Projection(_)
			| SolverFrame::Equality
			| SolverFrame::Evaluation { .. } => None,
		})
		.min_by_key(|definition| definition.order())
}

/// The derivation currently being computed. Shared across re-entrant
/// signature queries and value judgements, not recreated per API call, so
/// cycle detection sees every frame of a loop, whichever judgement it crosses.
pub(super) struct SolverState {
	pub(super) frames: Vec<SolverFrame>,
	/// How many more levels the innermost judgement (or the request, outside
	/// any judgement) may recurse. Equals `Solver::recursion_limit` when no frame is open.
	pub(super) recursion_budget: usize,
	/// Roll back an assumed equality chain that made no finite progress.
	blocked_at: Option<usize>,
	/// The outermost frame the innermost request's answer read so far (a
	/// cycle, a re-entered judgement or a rollback), `usize::MAX` when none.
	/// An answer that read no frame below its own request is a function of its
	/// `Normalization` alone.
	pub(super) lowest_frame_read: usize,
}

/// The engine that normalizes types and selects impls, with everything it
/// keeps: the derivation in flight, the finished-answer cache and the rule for
/// when it may be used, and the verdicts on the definitions it judges.
pub(super) struct Solver {
	/// The recursion budget each request and each judgement starts with. Fixed
	/// configuration, not state; only tests change it.
	pub(super) recursion_limit: usize,
	pub(super) state: SolverState,
	/// Only `Ok` answers are stored. `Pending` means a fact is not final yet,
	/// and `Poisoned` is not a permanent verdict (a budget overflow can be
	/// retried), so neither is remembered. Every
	/// stored answer was final when computed, so no "facts are final" switch is
	/// needed.
	pub(super) normalized: FxHashMap<Normalization, TypeIndex>,
	/// The verdict on each definition asked about; absent is `Unchecked`. A
	/// definition is `InProgress` exactly while its judgement's frame
	/// (`SolverFrame::Judgement`, `SolverFrame::Requirements`) is on the stack.
	pub(super) verdicts: FxHashMap<Definition, Verdict>,
	/// Every aggregate layout asked for, by its concrete type.
	pub(super) layouts: Layouts,
	/// Each constant's value query state, by `ConstIdx` (`eval.rs`).
	pub(super) const_values: Vec<ConstValueState>,
	/// The bytes constant values point into, by `AllocIdx` (`eval.rs`).
	pub(super) allocations: Vec<Allocation>,
}

impl Solver {
	pub(super) fn new(constant_count: usize) -> Self {
		let recursion_limit = 128;
		Self {
			recursion_limit,
			state: SolverState {
				frames: Vec::new(),
				recursion_budget: recursion_limit,
				blocked_at: None,
				lowest_frame_read: usize::MAX,
			},
			normalized: FxHashMap::default(),
			verdicts: FxHashMap::default(),
			layouts: Layouts::default(),
			const_values: vec![ConstValueState::Unevaluated; constant_count],
			allocations: Vec::new(),
		}
	}

	pub(super) fn verdict(&self, definition: Definition) -> &Verdict {
		self.verdicts
			.get(&definition)
			.unwrap_or(&Verdict::Unchecked)
	}

	/// `member`'s value, judged once: normalized in its impl's `Self` scope with
	/// a budget of its own, so the verdict depends on the definitions alone and
	/// is memoized whoever asks first. `requested_by` is the projection that
	/// selected it, `None` when its own check asks.
	///
	/// Answers the value as written in the impl's environment; the caller
	/// instantiates it. The judgement is a frame on the same stack, so
	/// reaching the member again sees the whole loop: through definitions only,
	/// it is a cycle owned by its first defined member (see `Verdict`);
	/// through an equality, it is a tautology the derivation itself blocks.
	pub(super) fn assoc_value(
		&mut self,
		view: &mut SolverView<'_>,
		member: ImplMember,
		requested_by: Option<TypeIndex>,
	) -> Result<TypeIndex, SolverError> {
		match self.verdict(Definition::Member(member)) {
			Verdict::Unchecked => {}
			Verdict::InProgress => {
				return self.reenter_judgement(view, member, requested_by);
			}
			Verdict::Resolved => return view.impl_member_value(member),
			Verdict::Poisoned | Verdict::Overflowed | Verdict::Cyclic(_) => {
				return Err(SolverError::Poisoned);
			}
		}
		let value = match view.impl_member_value(member) {
			Ok(value) => value,
			// No value (lowering failed and reported, or neither the impl nor the
			// trait supplies one, which conformance owns); nothing to judge.
			Err(SolverError::Poisoned) => {
				self.verdicts
					.insert(Definition::Member(member), Verdict::Poisoned);
				return Err(SolverError::Poisoned);
			}
			Err(error) => return Err(error),
		};
		let scope = view.trait_impls[usize::from(member.impl_index)]
			.as_ref()
			.expect("a member with a value has a resolved impl header")
			.type_params;
		self.verdicts
			.insert(Definition::Member(member), Verdict::InProgress);
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
			self.verdicts.remove(&Definition::Member(member));
			return Ok(value);
		}
		let (verdict, answer) = match result {
			Ok(_) => (Verdict::Resolved, Ok(value)),
			Err(SolverError::Pending) => {
				(Verdict::Unchecked, Err(SolverError::Pending))
			}
			Err(SolverError::Poisoned) => {
				(Verdict::Poisoned, Err(SolverError::Poisoned))
			}
			// Another member owns the loop. Its own judgement, further out,
			// answers `Poisoned` once it has kept the loop, so members past it
			// unwind as derived failures.
			Err(SolverError::Cycle(cycle))
				if cycle.owner.is_some_and(|owner| {
					owner != Definition::Member(member)
				}) =>
			{
				(Verdict::Poisoned, Err(SolverError::Cycle(cycle)))
			}
			// The budget counts from this judgement, so running out is a verdict
			// on the definition, like a cycle.
			Err(SolverError::Overflow) => {
				(Verdict::Overflowed, Err(SolverError::Poisoned))
			}
			Err(SolverError::Cycle(cycle)) => {
				(Verdict::Cyclic(cycle), Err(SolverError::Poisoned))
			}
		};
		self.verdicts.insert(Definition::Member(member), verdict);
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
		// Through an impl's requirements too: read from its projections, and
		// owned by the first defined definition on it.
		if loop_frames
			.iter()
			.any(|frame| matches!(frame, SolverFrame::Requirements { .. }))
		{
			let mut steps = projection_steps(loop_frames);
			steps.push(
				requested_by.expect("only a projection re-enters a judgement"),
			);
			return Err(SolverError::Cycle(Box::new(ProjectionCycle {
				projection: steps[0],
				steps: steps.into_boxed_slice(),
				owner: loop_owner(loop_frames),
				bound: None,
			})));
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
			owner: Some(Definition::Member(owner)),
			bound: None,
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

impl Normalization {
	/// `ty` under `env`'s assumptions. Only an abstract type reads them
	/// (`TypeInterner::is_abstract`), and every abstract type has a
	/// parameter in it, so a type with none means the same in every scope:
	/// its request is the root's, computed and cached once for all of them.
	fn new(
		types: &TypeInterner,
		env: TypeEnvIdx,
		ty: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Self {
		let env = if types.has_param(ty) {
			env
		} else {
			TypeEnvIdx::ROOT
		};
		Self {
			env,
			ty,
			depth,
			facts,
		}
	}
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
/// (an unfinished slot reads as `Pending`). Diagnostics, the query engine and
/// the tables a body or a declaration is built into are deliberately not here:
/// the solver can neither report nor construct. It reads built bodies to
/// evaluate constants, and strings for a string literal's contents.
pub(super) struct SolverView<'a> {
	pub(super) types: &'a mut TypeInterner,
	pub(super) defs: &'a DefinitionRegistry,
	pub(super) impl_dispatch: &'a ImplDispatch,
	pub(super) traits: &'a [TraitSignature],
	pub(super) trait_impls: &'a [Option<TraitImplSignature>],
	pub(super) inherent_impls: &'a [Option<InherentImplSignature>],
	pub(super) assoc_types: &'a [Option<AssocTypeSignature>],
	pub(super) structs: &'a [StructSignature],
	pub(super) enums: &'a [EnumSignature],
	pub(super) param_bounds: &'a [Box<[ParamBounds]>],
	pub(super) clauses: &'a ClauseArena,
	pub(super) type_envs: &'a TypeEnvArena,
	pub(super) constants: &'a [ConstantSignature],
	/// Read by constant evaluation, which never builds a body.
	pub(super) const_bodies: &'a [ConstBody],
	/// Read for a string literal's contents.
	pub(super) strings: &'a StringInterner,
}

impl<'a> SolverView<'a> {
	pub(super) fn clause_tables(&self) -> ClauseTables<'a> {
		ClauseTables::new(
			self.type_envs,
			self.param_bounds,
			self.traits,
			self.assoc_types,
			self.clauses,
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
					Substitution {
						envs: self.type_envs,
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
		// Nothing to reduce: no frame is opened or read, and no budget spent,
		// since a type without a projection cannot loop.
		if !view.types.has_projection(ty) {
			return Ok(ty);
		}
		let normalization = Normalization::new(
			view.types,
			assumption_context,
			ty,
			depth,
			facts,
		);
		let frame = self.state.frames.len();
		if frame == 0
			&& let Some(&normalized) = self.normalized.get(&normalization)
		{
			return Ok(normalized);
		}
		let outer_read =
			std::mem::replace(&mut self.state.lowest_frame_read, usize::MAX);
		let result =
			self.normalize_uncached(view, normalization.env, ty, depth, facts);
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
		let result = match *view.types.resolve(ty) {
			Type::AssocTypeProjection { .. } => self.normalize_projection(
				view,
				assumption_context,
				ty,
				depth,
				facts,
			),
			Type::Const {
				constant,
				type_args,
			} => self.normalize_const(
				view,
				assumption_context,
				constant,
				type_args,
				depth,
				facts,
			),
			_ => match depth {
				NormalizationDepth::Shallow => Ok(ty),
				NormalizationDepth::Deep => self.normalize_children(
					view,
					assumption_context,
					ty,
					depth,
					facts,
				),
			},
		};
		self.state.recursion_budget += 1;
		result
	}

	/// A constant in a type means its value, evaluated here on first use;
	/// one whose body is not built yet is `Pending`. A constant with type
	/// arguments is not evaluated yet, so it keeps its normalized arguments.
	fn normalize_const(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		constant: ConstIdx,
		type_args: TypeList,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		if !type_args.is_empty() {
			let mut type_args = view.types.list(type_args).to_vec();
			for item in type_args.iter_mut() {
				*item = self.normalize(
					view,
					assumption_context,
					*item,
					depth,
					facts,
				)?;
			}
			return Ok(view.types.intern_const(constant, &type_args));
		}
		match self.const_value(view, constant) {
			Ok(value) => match value_bits(value) {
				Some(bits) => Ok(view.types.intern(Type::Value { bits })),
				None => Err(SolverError::Poisoned),
			},
			Err(Unevaluable::Pending) => Err(SolverError::Pending),
			// Reported by the constant's own check, or where it is named.
			Err(_) => Err(SolverError::Poisoned),
		}
	}

	fn normalize_projection(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		depth: NormalizationDepth,
		facts: RewriteFacts,
	) -> Result<TypeIndex, SolverError> {
		let normalization = Normalization::new(
			view.types,
			assumption_context,
			projection,
			depth,
			facts,
		);
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
		if view.types.is_param_or_projection(base) {
			match self.projection_equality(
				view,
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
		// A base reduced to a type with no parameter (`T::A` to `i32`) leaves a
		// request that is the root's from here on.
		let (projection, assumption_context) = if next_base == base {
			(projection, assumption_context)
		} else {
			let next = view.types.intern(Type::AssocTypeProjection {
				base: next_base,
				trait_index,
				assoc_type_index,
			});
			let normalization = Normalization::new(
				view.types,
				assumption_context,
				next,
				depth,
				facts,
			);
			if self.projection_cycle(normalization)? {
				return Ok(projection);
			}
			let Some(SolverFrame::Projection(current)) =
				self.state.frames.last_mut()
			else {
				unreachable!("the reducing projection is the innermost frame")
			};
			*current = normalization;
			(next, normalization.env)
		};
		if view.types.is_param_or_projection(next_base) {
			return match self.projection_equality(
				view,
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
		if matches!(view.types.resolve(next_base), Type::Infer) {
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
		let (impl_index, args) = match found {
			TraitImplLookup::Concrete { impl_index, args } => {
				(impl_index, args)
			}
			TraitImplLookup::Builtin => {
				let Some(value) =
					builtin_assoc_value(view, next_base, assoc_type_index)
				else {
					return Ok(projection);
				};
				return self.normalize(
					view,
					assumption_context,
					value,
					depth,
					facts,
				);
			}
			TraitImplLookup::Abstract => return Ok(projection),
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
			view.types.substitute(
				value,
				Substitution {
					envs: view.type_envs,
					env,
					args: &args,
				},
			)
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
		// The loop goes through a definition: a value being judged or an impl's
		// requirements being proved. Repeating the projection reaches that
		// definition again one step later, where it reads the loop and its owner
		// (`reenter_judgement`, `reenter_requirements`).
		if loop_frames.iter().any(|frame| {
			matches!(
				frame,
				SolverFrame::Judgement { .. }
					| SolverFrame::Requirements { .. }
			)
		}) {
			return Ok(false);
		}
		Err(SolverError::Cycle(Box::new(ProjectionCycle {
			projection: normalization.ty,
			steps: projection_steps(loop_frames).into_boxed_slice(),
			owner: None,
			bound: None,
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
		let rebuilt = match *view.types.resolve(ty) {
			Type::Tuple { elements } => {
				let mut elements = view.types.list(elements).to_vec();
				for item in elements.iter_mut() {
					*item = self.normalize(
						view,
						assumption_context,
						*item,
						depth,
						facts,
					)?;
				}
				return Ok(view.types.intern_tuple(&elements));
			}
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let mut type_args = view.types.list(type_args).to_vec();
				for item in type_args.iter_mut() {
					*item = self.normalize(
						view,
						assumption_context,
						*item,
						depth,
						facts,
					)?;
				}
				return Ok(view.types.intern_struct(struct_index, &type_args));
			}
			Type::Function {
				func_index,
				type_args,
			} => {
				let mut type_args = view.types.list(type_args).to_vec();
				for item in type_args.iter_mut() {
					*item = self.normalize(
						view,
						assumption_context,
						*item,
						depth,
						facts,
					)?;
				}
				return Ok(view.types.intern_function(func_index, &type_args));
			}
			Type::FunctionRef { param, result } => Type::FunctionRef {
				param: self.normalize(
					view,
					assumption_context,
					param,
					depth,
					facts,
				)?,
				result: self.normalize(
					view,
					assumption_context,
					result,
					depth,
					facts,
				)?,
			},
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
				length,
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
				length: self.normalize(
					view,
					assumption_context,
					length,
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
			Type::AssocTypeProjection { .. } | Type::Const { .. } => {
				unreachable!(
					"projections are handled before structural traversal"
				)
			}
			Type::Error
			| Type::Infer
			| Type::Never
			| Type::Integer
			| Type::Float
			| Type::String
			| Type::ArrayLiteral
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
			| Type::TypeParam { .. }
			| Type::Value { .. } => return Ok(ty),
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
		// A value type is one Wasm value, whatever impls exist.
		if Some(required_trait) == view.defs.intrinsics.value_type {
			let layout =
				self.value_layout(view, assumption_context, receiver)?;
			return Ok(layout
				.is_some_and(|layout| layout.len() == 1)
				.then_some(TraitImplLookup::Builtin));
		}
		// Only an abstract type takes a trait from assumptions. Any other type
		// has the trait exactly when its impl says so: there is one impl per
		// trait and constructor, so a local assumption cannot make it hold, only
		// make the declaration that assumes it impossible to use. A type no impl
		// can target (a tuple, a pointer) is no exception: it has no impl.
		let mut assumed = Assumption::Unproven;
		if view.types.is_param_or_projection(receiver) {
			assumed = self.check_assumed_trait(
				view,
				assumption_context,
				receiver,
				required_trait,
			)?;
			if assumed == Assumption::Holds {
				return Ok(Some(TraitImplLookup::Abstract));
			}
		}
		let normalized =
			self.normalize_head_query(view, assumption_context, receiver)?;
		if normalized == TypeIndex::ERROR {
			return Err(SolverError::Poisoned);
		}
		// A function reference is called by a compiler rule.
		if Some(required_trait) == view.defs.intrinsics.call
			&& matches!(
				view.types.resolve(normalized),
				Type::FunctionRef { .. }
			) {
			return Ok(Some(TraitImplLookup::Builtin));
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
			let Some(impl_index) = candidate else {
				return Ok(None);
			};
			return Ok(self
				.match_trait_impl_candidate_query(
					view,
					assumption_context,
					impl_index,
					normalized,
				)?
				.map(|args| TraitImplLookup::Concrete { impl_index, args }));
		}
		if normalized != receiver
			&& view.types.is_param_or_projection(normalized)
		{
			assumed = assumed.max(self.check_assumed_trait(
				view,
				assumption_context,
				normalized,
				required_trait,
			)?);
		}
		match assumed {
			Assumption::Holds => Ok(Some(TraitImplLookup::Abstract)),
			Assumption::Unproven => Ok(None),
			Assumption::Pending => Err(SolverError::Pending),
		}
	}

	/// The Wasm values a value of `ty` occupies, as `ValueType` judges it:
	/// fields in declaration order. `None` when some part of it is abstract
	/// and not assumed `ValueType`, so its values are unknown.
	pub(super) fn value_layout(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<Box<[LayoutValue]>>, SolverError> {
		let mut layout = Vec::new();
		let known =
			self.push_layout(view, assumption_context, ty, &mut layout, 0)?;
		Ok(known.then(|| layout.into_boxed_slice()))
	}

	/// Appends `ty`'s values to `out`; `false` when some part of it is
	/// abstract and not assumed `ValueType`.
	fn push_layout(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		out: &mut Vec<LayoutValue>,
		depth: usize,
	) -> Result<bool, SolverError> {
		if depth > self.state.recursion_budget {
			return Err(SolverError::Overflow);
		}
		let ty = self.normalize_head_query(view, assumption_context, ty)?;
		let known = match *view.types.resolve(ty) {
			// A constant is no value's type; lowering puts one only where a
			// constant is expected.
			Type::Error
			| Type::Infer
			| Type::Integer
			| Type::Float
			| Type::String
			| Type::ArrayLiteral
			| Type::Value { .. }
			| Type::Const { .. } => {
				return Err(SolverError::Poisoned);
			}
			Type::Never
			| Type::Function { .. }
			| Type::Memory { .. }
			| Type::Global { .. } => true,
			Type::U8
			| Type::I8
			| Type::U16
			| Type::I16
			| Type::U32
			| Type::I32
			| Type::Bool
			| Type::Char => {
				out.push(LayoutValue::Known(ValType::I32));
				true
			}
			Type::U64 | Type::I64 => {
				out.push(LayoutValue::Known(ValType::I64));
				true
			}
			Type::F32 => {
				out.push(LayoutValue::Known(ValType::F32));
				true
			}
			Type::F64 => {
				out.push(LayoutValue::Known(ValType::F64));
				true
			}
			Type::FunctionRef { .. } => {
				out.push(LayoutValue::Known(ValType::FuncRef));
				true
			}
			Type::Enum { enum_index } => {
				let repr = view.enums[usize::from(enum_index)].repr;
				self.push_layout(
					view,
					assumption_context,
					repr,
					out,
					depth + 1,
				)?
			}
			// An address, as wide as its memory's `Size`.
			Type::Pointer { memory, .. } | Type::Array { memory, .. } => self
				.push_address(
				view,
				assumption_context,
				ty,
				memory,
				out,
				depth,
			)?,
			// An address and a length, both as wide as the memory's `Size`.
			Type::Slice { memory, .. } => {
				self.push_address(
					view,
					assumption_context,
					ty,
					memory,
					out,
					depth,
				)? && self.push_address(
					view,
					assumption_context,
					ty,
					memory,
					out,
					depth,
				)?
			}
			Type::Tuple { elements } => {
				let elements: Box<[TypeIndex]> =
					view.types.list(elements).into();
				let mut known = true;
				for element in elements {
					known &= self.push_layout(
						view,
						assumption_context,
						element,
						out,
						depth + 1,
					)?;
				}
				known
			}
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let signature = &view.structs[usize::from(struct_index)];
				let (env, fields) =
					(signature.type_params, signature.field_types);
				let args: Box<[TypeIndex]> = view.types.list(type_args).into();
				let mut known = true;
				// Read one field at a time: substituting may store more lists.
				for at in 0..fields.len() {
					let field = view.types.list(fields)[at];
					let field = view.types.substitute(
						field,
						Substitution {
							envs: view.type_envs,
							env,
							args: &args,
						},
					);
					known &= self.push_layout(
						view,
						assumption_context,
						field,
						out,
						depth + 1,
					)?;
				}
				known
			}
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. } => {
				let value_type = view
					.defs
					.intrinsics
					.value_type
					.expect("only `ValueType` asks for a layout");
				match self.check_assumed_trait(
					view,
					assumption_context,
					ty,
					value_type,
				)? {
					Assumption::Holds => {
						out.push(LayoutValue::Abstract(ty));
						true
					}
					Assumption::Unproven => false,
					Assumption::Pending => return Err(SolverError::Pending),
				}
			}
		};
		Ok(known)
	}

	/// Appends one address into `memory`, the layout of its `Size`. An
	/// address into a memory not known yet is still one value: `pointer`,
	/// abstract.
	fn push_address(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		pointer: TypeIndex,
		memory: TypeIndex,
		out: &mut Vec<LayoutValue>,
		depth: usize,
	) -> Result<bool, SolverError> {
		let memory =
			self.normalize_head_query(view, assumption_context, memory)?;
		let Type::Memory { memory_index } = *view.types.resolve(memory) else {
			out.push(LayoutValue::Abstract(pointer));
			return Ok(true);
		};
		let size =
			view.defs.memories[usize::from(memory_index)].size_assoc_type_index;
		let Some(size) = view.assoc_types[usize::from(size)]
			.as_ref()
			.and_then(|signature| signature.value)
		else {
			return Err(SolverError::Pending);
		};
		self.push_layout(view, assumption_context, size, out, depth + 1)
	}

	/// Whether the facts in scope prove `ty: required`, from three sources:
	///
	/// 1. a declaration on `ty`'s own path states it (`type Item: Marker`);
	/// 2. a clause in scope states it of `ty` as written;
	/// 3. a clause states it of another subject that means what `ty` means,
	///    by assumed equalities: `T::Item: Marker` with `T::Item = U` proves
	///    `U: Marker`.
	///
	/// The first holds wherever `ty` is used; the other two are the scope's
	/// own, and only an abstract `ty` with an abstract meaning takes them. A
	/// concrete one has its traits from impls alone, so a clause whose subject
	/// means `i32`, or `<P as Container>::Item`, proves nothing about it, and
	/// the answer for it never depends on `assumption_context`.
	///
	/// Declaration bounds are not lent through an equality: `Item = U` with
	/// `type Item: Marker` does not make `U: Marker`, which must be written.
	///
	/// Comparison reduces assumed equalities only, so it cannot depend on impl
	/// dispatch. It reads finished declaration bounds and never demands one:
	/// an unfinished table is `Assumption::Pending`, never an error.
	pub(super) fn check_assumed_trait(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		required: TraitIdx,
	) -> Result<Assumption, SolverError> {
		let tables = view.clause_tables();
		// 1. Declared on `ty`'s own path.
		let mut declared =
			tables.declared_traits(view.types, ty, self.state.recursion_budget);
		if declared.any(|trait_index| trait_index == required) {
			return Ok(Assumption::Holds);
		}
		let mut readiness = declared.readiness;
		if view.types.is_abstract(ty) {
			readiness =
				readiness.and(tables.assumptions_readiness(assumption_context));
			// 2. Stated of `ty` itself.
			if tables
				.assumed_subjects(assumption_context, required)
				.any(|subject| subject == ty)
			{
				return Ok(Assumption::Holds);
			}
			// 3. Stated of another subject with the same, abstract, meaning.
			let mut subjects = tables
				.assumed_subjects(assumption_context, required)
				.peekable();
			if subjects.peek().is_some() {
				let meaning = match self.normalize_assumed_type_query(
					view,
					assumption_context,
					ty,
				) {
					Ok(meaning) => meaning,
					Err(SolverError::Pending) => {
						return Ok(Assumption::Pending);
					}
					Err(error) => return Err(error),
				};
				if view.types.is_abstract(meaning) {
					for subject in subjects {
						match self.normalize_assumed_type_query(
							view,
							assumption_context,
							subject,
						) {
							Ok(candidate) if candidate == meaning => {
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
			ImplKind::Trait(impl_index),
			header.type_params,
			header.target.inner,
			receiver,
		)
	}

	/// `assumption_context` is the caller's; `impl_env` is the candidate impl's own
	/// parameter frame (for a synthetic impl, the frame it is generic over). The
	/// impl's requirements are proved in the caller's assumptions, never the
	/// candidate's.
	fn match_impl_target_and_bounds(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		impl_kind: ImplKind,
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
		let Some(args) = view.types.match_impl_target(
			target,
			receiver,
			view.type_envs,
			impl_env,
		) else {
			return Ok(None);
		};
		// The impl's requirements are a definition, judged once before any
		// selection relies on them. While they are judged, the impl's own
		// instantiation is that judgement; any other is proved as usual.
		if *self.verdict(Definition::Requirements(impl_kind))
			== Verdict::InProgress
		{
			if assumption_context == impl_env
				&& *args == *view.type_envs.identity_args(impl_env)
			{
				self.reenter_requirements(impl_kind)?;
				return Ok(Some(args));
			}
		} else {
			self.requirements_verdict(view, impl_kind)?;
		}
		if self.prove_requirements(
			view,
			assumption_context,
			impl_env,
			&args,
			None,
		)? {
			Ok(Some(args))
		} else {
			Ok(None)
		}
	}

	/// `impl_kind`'s requirements, judged once: proved for its own parameters
	/// in its own scope, with a budget of its own, so the verdict depends on
	/// the definitions alone and is memoized whoever asks first. A loop is a
	/// selection of the impl's own instantiation while this judgement runs
	/// (`reenter_requirements`); the verdict keeps a loop it owns, at the bound
	/// it closed in, for the impl's check to report (`CheckImplRequirements`),
	/// and every reader of a failed verdict fails silently.
	///
	/// Whether the requirements hold there is no part of the verdict: in its
	/// own scope they are assumptions, and a selection proves them for its own
	/// arguments.
	pub(super) fn requirements_verdict(
		&mut self,
		view: &mut SolverView<'_>,
		impl_kind: ImplKind,
	) -> Result<(), SolverError> {
		let definition = Definition::Requirements(impl_kind);
		match self.verdict(definition) {
			Verdict::Unchecked => {}
			Verdict::Resolved => return Ok(()),
			Verdict::InProgress => {
				unreachable!("a selection re-entering the judgement is a loop")
			}
			Verdict::Poisoned | Verdict::Overflowed | Verdict::Cyclic(_) => {
				return Err(SolverError::Poisoned);
			}
		}
		let impl_env = match impl_kind {
			ImplKind::Trait(index) => view.trait_impls[usize::from(index)]
				.as_ref()
				.map(|header| header.type_params),
			ImplKind::Inherent(index) => view.inherent_impls
				[usize::from(index)]
			.as_ref()
			.map(|header| header.type_params),
		}
		.ok_or(SolverError::Pending)?;
		let args = view.type_envs.identity_args(impl_env);
		self.verdicts.insert(definition, Verdict::InProgress);
		let index = self.state.frames.len();
		self.state.frames.push(SolverFrame::Requirements {
			impl_kind,
			bound: None,
			outer_budget: std::mem::replace(
				&mut self.state.recursion_budget,
				self.recursion_limit,
			),
		});
		let result = self.prove_requirements(
			view,
			impl_env,
			impl_env,
			args,
			Some(index),
		);
		let Some(SolverFrame::Requirements {
			bound,
			outer_budget,
			..
		}) = self.state.frames.pop()
		else {
			unreachable!("the judgement is the innermost frame once it is done")
		};
		self.state.recursion_budget = outer_budget;
		// A tautology further out is unwinding through this judgement, which was
		// cut short: there is no verdict yet, so it is judged again when asked.
		if self.state.blocked_at.is_some_and(|blocked| blocked < index) {
			self.verdicts.remove(&definition);
			return Ok(());
		}
		let (verdict, answer) = match result {
			Ok(_) => (Verdict::Resolved, Ok(())),
			Err(SolverError::Pending) => {
				self.verdicts.remove(&definition);
				return Err(SolverError::Pending);
			}
			Err(SolverError::Poisoned) => {
				(Verdict::Poisoned, Err(SolverError::Poisoned))
			}
			// Another definition owns the loop; this one derives from it.
			Err(SolverError::Cycle(cycle))
				if cycle.owner.is_some_and(|owner| owner != definition) =>
			{
				(Verdict::Poisoned, Err(SolverError::Cycle(cycle)))
			}
			Err(SolverError::Overflow) => {
				(Verdict::Overflowed, Err(SolverError::Poisoned))
			}
			// This impl owns the loop, or one found inside its requirements:
			// either way the requirement it closed in is where it is written.
			Err(SolverError::Cycle(mut cycle)) => {
				cycle.owner = Some(definition);
				cycle.bound = bound;
				(Verdict::Cyclic(cycle), Err(SolverError::Poisoned))
			}
		};
		self.verdicts.insert(definition, verdict);
		answer
	}

	/// The impl's own instantiation was selected again while its requirements
	/// are judged. Through an equality on the way back the loop is a
	/// tautology: the requirements are taken to hold, and nothing read through
	/// them is cached. Through definitions only, it is a cycle, owned by the
	/// first defined definition on it.
	fn reenter_requirements(
		&mut self,
		impl_kind: ImplKind,
	) -> Result<(), SolverError> {
		let start = self
			.state
			.frames
			.iter()
			.position(|frame| {
				matches!(frame, SolverFrame::Requirements { impl_kind: judged, .. } if *judged == impl_kind)
			})
			.expect("an in-progress judgement is on the stack");
		self.state.lowest_frame_read = self.state.lowest_frame_read.min(start);
		let loop_frames = &self.state.frames[start..];
		if loop_frames
			.iter()
			.any(|frame| matches!(frame, SolverFrame::Equality))
		{
			return Ok(());
		}
		let steps = projection_steps(loop_frames);
		Err(SolverError::Cycle(Box::new(ProjectionCycle {
			projection: *steps
				.first()
				.expect("a selection is reached again through a projection"),
			steps: steps.into_boxed_slice(),
			owner: loop_owner(loop_frames),
			bound: None,
		})))
	}

	/// Whether every bound on `impl_env`'s chain holds for `args` (its flat
	/// arguments) under `assumption_context`. A judgement passes its frame,
	/// which records the bound being proved.
	fn prove_requirements(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		impl_env: TypeEnvIdx,
		args: &[TypeIndex],
		judgement: Option<usize>,
	) -> Result<bool, SolverError> {
		// Every parameter on the impl's chain is an argument of the match,
		// at its flat slot; its bounds stay in its own frame.
		for frame in view.type_envs.chain(impl_env) {
			let start = view.type_envs.parent_count(frame);
			for (index, bounds) in
				view.param_bounds[usize::from(frame)].iter().enumerate()
			{
				if !self.satisfies_clauses(
					view,
					assumption_context,
					bounds.clauses,
					(
						view.type_envs.param_types(frame)[index],
						args[start + index],
					),
					(impl_env, args),
					None,
					judgement,
				)? {
					return Ok(false);
				}
			}
		}
		Ok(true)
	}

	/// Whether `subject` satisfies `clauses`, which a declaration states
	/// about `root`: each membership, then each equality, as Rust proves `T:
	/// Tr<A = X, A: Other>`. A clause's subject is a path over `root`, read
	/// over `subject` and named by its value; its other types are substituted
	/// over `substitution` (the frame the clauses are written in and the
	/// arguments for its whole chain). A clause reached through a membership
	/// that does not hold is not proved: that membership is the failure. With
	/// `failures`, every failure is collected for the caller to report;
	/// without, the first one answers. A judgement passes its frame, which
	/// records the bound being proved.
	pub(super) fn satisfies_clauses(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		clauses: BoundClauses,
		(root, subject): (TypeIndex, TypeIndex),
		(frame, arguments): (TypeEnvIdx, &[TypeIndex]),
		mut failures: Option<&mut Vec<Unsatisfied>>,
		judgement: Option<usize>,
	) -> Result<bool, SolverError> {
		let Some(equalities) = clauses.equalities else {
			return Err(SolverError::Pending);
		};
		let arena = view.clauses;
		let mut failed = Vec::new();
		let mut satisfied = true;
		for clause in arena.traits(clauses.traits) {
			if through_failed(view.types, clause.subject, &failed) {
				continue;
			}
			self.record_proving(judgement, clause.origin);
			let mut receiver =
				rebase(view.types, clause.subject, root, subject);
			if clause.subject != root {
				receiver = self.normalize_type_query(
					view,
					assumption_context,
					receiver,
				)?;
			}
			if self
				.find_trait_impl_query(
					view,
					assumption_context,
					receiver,
					clause.trait_index,
				)?
				.is_some()
			{
				continue;
			}
			failed.push((clause.subject, clause.trait_index));
			let Some(failures) = failures.as_deref_mut() else {
				return Ok(false);
			};
			failures.push(Unsatisfied::Trait {
				subject: receiver,
				trait_index: clause.trait_index,
				source: clause.source,
			});
			satisfied = false;
		}
		let equalities = arena.equalities(equalities);
		for clause in equalities {
			// A conflict is the declaration's own error.
			if equalities.iter().any(|other| {
				other.projection == clause.projection
					&& known_distinct(view.types, other.value, clause.value)
			}) || through_failed(view.types, clause.projection, &failed)
			{
				continue;
			}
			self.record_proving(judgement, clause.origin);
			let projection =
				rebase(view.types, clause.projection, root, subject);
			let expected = view.types.substitute(
				clause.value,
				Substitution {
					envs: view.type_envs,
					env: frame,
					args: arguments,
				},
			);
			let found = self.normalize_type_query(
				view,
				assumption_context,
				projection,
			)?;
			let expected =
				self.normalize_type_query(view, assumption_context, expected)?;
			if found == expected
				|| found == TypeIndex::ERROR
				|| expected == TypeIndex::ERROR
			{
				continue;
			}
			let Some(failures) = failures.as_deref_mut() else {
				return Ok(false);
			};
			failures.push(Unsatisfied::Equality {
				projection,
				found,
				expected,
				source: clause.source,
			});
			satisfied = false;
		}
		Ok(satisfied)
	}

	/// Records on a requirements judgement's frame the bound being proved,
	/// where a loop that closes in it is reported.
	fn record_proving(&mut self, judgement: Option<usize>, bound: BoundId) {
		let Some(judgement) = judgement else {
			return;
		};
		let SolverFrame::Requirements { bound: proving, .. } =
			&mut self.state.frames[judgement]
		else {
			unreachable!("the judgement's own frame")
		};
		*proving = Some(bound);
	}

	pub(super) fn projection_equality(
		&mut self,
		view: &mut SolverView<'_>,
		receiver: TypeIndex,
		trait_index: TraitIdx,
		assoc_type_index: AssocTypeIdx,
	) -> Result<EqualityLookup, SolverError> {
		let mut first = None;
		// No allocation for the usual zero/one-equality lookup. Competing
		// contexts are rare, and only need scalar handles for substitution.
		let mut alternatives = Vec::new();
		// The equalities on `<receiver as Tr>::A`, from each subject whose
		// clauses can describe `receiver`.
		let tables = view.clause_tables();
		let types = &*view.types;
		let sources = tables.declarations_of(
			types,
			receiver,
			self.state.recursion_budget,
		);
		let readiness = sources.readiness;
		for source in sources {
			let Some(equalities) = source.clauses.equalities else {
				continue;
			};
			for clause in tables.clauses.equalities(equalities) {
				let Type::AssocTypeProjection {
					base,
					trait_index: clause_trait,
					assoc_type_index: clause_assoc,
				} = *types.resolve(clause.projection)
				else {
					unreachable!("an equality is on a projection")
				};
				if clause_trait != trait_index
					|| clause_assoc != assoc_type_index
					|| !source.names(types, tables.type_envs, base, receiver)
				{
					continue;
				}
				let candidate = ContextualEquality {
					value: clause.value,
					context: source.context,
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
		}
		match readiness {
			Readiness::Ready => {}
			Readiness::Pending => return Err(SolverError::Pending),
			Readiness::Overflowed => return Err(SolverError::Overflow),
		}
		// Two values are ambiguous unless they agree once instantiated,
		// conflicting ones included (the declaration reports those).
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
				Substitution {
					envs: view.type_envs,
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
	pub(super) fn solver_and_view(&mut self) -> (&mut Solver, SolverView<'_>) {
		(
			&mut self.solver,
			SolverView {
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

	#[cfg(test)]
	pub(super) fn value_layout(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<Box<[LayoutValue]>>, SolverError> {
		let (solver, mut view) = self.solver_and_view();
		solver.value_layout(&mut view, assumption_context, ty)
	}

	pub(super) fn match_impl_target_and_bounds(
		&mut self,
		assumption_context: TypeEnvIdx,
		impl_kind: ImplKind,
		impl_env: TypeEnvIdx,
		target: TypeIndex,
		receiver: TypeIndex,
	) -> Result<Option<Box<[TypeIndex]>>, SolverError> {
		debug_assert!(self.query_stack.is_empty(), "{IMPL_WHILE_BUILDING}");
		let (solver, mut view) = self.solver_and_view();
		solver.match_impl_target_and_bounds(
			&mut view,
			assumption_context,
			impl_kind,
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
