//! Declaration-local assumptions, read from the existing bound tables.
//!
//! Scope traversal visits the finite parameter-bound trees. Declaration
//! bounds are read along a requested subject's projection path instead of
//! recursively expanding every associated type: a recursive trait can
//! describe infinitely many such paths.
//!
//! This is the one reader over the bound tables: scoped facts, subject facts, and
//! `effective_bounds` (the declaration bounds along a receiver's projection
//! path, with `Readiness` saying whether they are final). Both the solver
//! (`solver.rs`, through its `SolverView`) and member selection
//! (`members.rs`) read through it; it holds only references to the tables.
//!
//! A query's assumptions are named by a `TypeEnvIdx` called
//! `assumption_context`: the declaration whose bounds (and enclosing
//! declarations' bounds) apply. It is not the environment a parameter was
//! declared in; a query about an outer parameter can use extra facts from an
//! inner declaration's context. Where both meet (`match_impl_target_and_bounds`)
//! the `assumption_context` is the caller's and `impl_env` the candidate impl's:
//! requirements are proved in the caller's context.

use crate::small_vec::SmallVec;

use super::bounds::{
	BoundId, ImpliedAssocBinding, ImpliedBindingKind, ImpliedTraitBound,
};
use super::defs::{AssocTypeIdx, TraitIdx};
use super::signatures::{
	AssocTypeSignature, ParamBounds, TraitSignature, TypeContext,
};
use super::types::{
	Type, TypeEnvArena, TypeEnvIdx, TypeEnvOwner, TypeIndex, TypeInterner,
};

/// A borrowed view shared by signature construction and body checking.
/// It does not demand signatures, normalize types, or prove requirements.
pub(super) struct AssumptionReader<'a> {
	pub(super) type_envs: &'a TypeEnvArena,
	pub(super) param_bounds: &'a [Box<[ParamBounds]>],
	pub(super) traits: &'a [TraitSignature],
	pub(super) assoc_types: &'a [Option<AssocTypeSignature>],
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum TraitAssumptionSource {
	Bound(BoundId),
	/// The implicit `Self: ThisTrait` membership has no written bound.
	TraitSelf(TraitIdx),
}

pub(super) enum AssumptionKind<'a> {
	Trait {
		trait_index: TraitIdx,
		source: TraitAssumptionSource,
	},
	/// Includes known, ambiguous, and conflicting equality states. A plain
	/// `Bound` binding contributes nested memberships, not an equality.
	Equality(&'a ImpliedBindingKind),
}

/// The subject is already instantiated. An equality's RHS stays borrowed
/// from its source tree; `self_substitution` supplies its meaning of Self.
pub(super) struct Fact<'a> {
	pub(super) subject: TypeIndex,
	pub(super) kind: AssumptionKind<'a>,
	pub(super) self_substitution: Option<SelfSubstitution>,
}

impl<'a> AssumptionReader<'a> {
	pub(super) fn new(
		type_envs: &'a TypeEnvArena,
		param_bounds: &'a [Box<[ParamBounds]>],
		traits: &'a [TraitSignature],
		assoc_types: &'a [Option<AssocTypeSignature>],
	) -> Self {
		Self {
			type_envs,
			param_bounds,
			traits,
			assoc_types,
		}
	}

	/// Read memberships and equalities in this scope and its ancestors.
	/// Readiness describes these parameter trees; associated declaration
	/// dependencies are inspected separately by `subject_facts`.
	pub(super) fn scoped_facts(
		&self,
		assumption_context: TypeEnvIdx,
		types: &TypeInterner,
	) -> AssumptionFacts<'a> {
		let mut readiness = Readiness::Ready;
		let mut roots = ScopedRoots::new(self, assumption_context);
		while let Some(root) = roots.next(types) {
			readiness = readiness.and(root.readiness);
		}
		AssumptionFacts {
			sources: Sources::Scope(ScopedRoots::new(self, assumption_context)),
			current: None,
			parents: Vec::new(),
			readiness,
		}
	}

	/// Read facts applying to a particular subject, including associated
	/// declaration bounds with Self rebound to each projection's receiver.
	/// The caller supplies its remaining traversal budget. Missing or
	/// provisional declaration slots remain Pending; reading never forces them.
	pub(super) fn subject_facts(
		&self,
		subject: TypeIndex,
		types: &TypeInterner,
		recursion_budget: usize,
	) -> AssumptionFacts<'a> {
		let bounds = self.effective_bounds(types, subject, recursion_budget);
		let readiness = bounds.readiness;
		AssumptionFacts {
			sources: Sources::Subject { subject, bounds },
			current: None,
			parents: Vec::new(),
			readiness,
		}
	}
}

struct BoundSource<'a> {
	subject: TypeIndex,
	bounds: &'a [ImpliedTraitBound],
	context: Option<SelfSubstitution>,
	reflexive_trait: Option<TraitIdx>,
	readiness: Readiness,
}

struct ScopedRoots<'a> {
	type_envs: &'a TypeEnvArena,
	param_bounds: &'a [Box<[ParamBounds]>],
	scope: Option<TypeEnvIdx>,
	param_index: usize,
}

impl<'a> ScopedRoots<'a> {
	fn new(
		reader: &AssumptionReader<'a>,
		assumption_context: TypeEnvIdx,
	) -> Self {
		Self {
			type_envs: reader.type_envs,
			param_bounds: reader.param_bounds,
			scope: Some(assumption_context),
			param_index: 0,
		}
	}

	fn next(&mut self, types: &TypeInterner) -> Option<BoundSource<'a>> {
		while let Some(env) = self.scope {
			if env != TypeEnvIdx::ROOT {
				let params = self.type_envs.params(env);
				while let Some(param) = params.get(self.param_index) {
					let index = self.param_index;
					self.param_index += 1;
					// An impl's Self frame binds a name to an existing type.
					// Its placeholder row is not a new assumption source,
					// even when that type is an outer abstract parameter.
					if !matches!(types.resolve(param.ty),
						Type::TypeParam { env: owner, param_index }
						if *owner == env && *param_index as usize == index)
					{
						continue;
					}
					let facts =
						&self.param_bounds[usize::from(env)][index].facts;
					return Some(BoundSource {
						subject: param.ty,
						bounds: facts.current(),
						context: None,
						reflexive_trait: match self.type_envs.owner(env) {
							TypeEnvOwner::Trait(index) => Some(index),
							_ => None,
						},
						readiness: Readiness::from_ready(facts.is_ready()),
					});
				}
			}
			self.scope = self.type_envs.parent(env);
			self.param_index = 0;
		}
		None
	}
}

enum Sources<'a> {
	Scope(ScopedRoots<'a>),
	Subject {
		subject: TypeIndex,
		bounds: EffectiveBounds<'a>,
	},
}

impl<'a> Sources<'a> {
	fn next(&mut self, types: &TypeInterner) -> Option<BoundSource<'a>> {
		match self {
			Self::Scope(roots) => roots.next(types),
			Self::Subject { subject, bounds } => {
				if let Some(trait_index) = bounds.reflexive_trait.take() {
					return Some(BoundSource {
						subject: *subject,
						bounds: &[],
						context: None,
						reflexive_trait: Some(trait_index),
						readiness: bounds.readiness,
					});
				}
				bounds.next().map(|view| BoundSource {
					subject: *subject,
					bounds: std::slice::from_ref(view.bound),
					context: view.context,
					reflexive_trait: None,
					readiness: bounds.readiness,
				})
			}
		}
	}
}

enum Visit<'a> {
	Traits {
		subject: TypeIndex,
		bounds: &'a [ImpliedTraitBound],
		context: Option<SelfSubstitution>,
	},
	Bindings {
		subject: TypeIndex,
		trait_index: TraitIdx,
		bindings: &'a [ImpliedAssocBinding],
		context: Option<SelfSubstitution>,
	},
}

/// A cursor over borrowed trees, allocating traversal frames only when a
/// nested tree has siblings to return to. Facts are neither cloned nor cached.
pub(super) struct AssumptionFacts<'a> {
	sources: Sources<'a>,
	current: Option<Visit<'a>>,
	parents: Vec<Visit<'a>>,
	/// Computed before iteration, so early termination cannot hide Pending.
	/// Provisional memberships may be inspected, but equality reduction needs
	/// Ready facts. The cursor exposes data; it does not authorize a proof.
	pub(super) readiness: Readiness,
}

impl<'a> AssumptionFacts<'a> {
	/// The interner is supplied per step because nested subjects may need
	/// fresh projection identities. This is structural interning, not reduction.
	pub(super) fn next(
		&mut self,
		types: &mut TypeInterner,
	) -> Option<Fact<'a>> {
		loop {
			match self.current.take() {
				Some(Visit::Traits {
					subject,
					bounds,
					context,
				}) => {
					let Some((bound, remaining)) = bounds.split_first() else {
						self.current = self.parents.pop();
						continue;
					};
					let rest = Visit::Traits {
						subject,
						bounds: remaining,
						context,
					};
					if bound.bindings.is_empty() {
						self.current = Some(rest);
					} else {
						if !remaining.is_empty() {
							self.parents.push(rest);
						}
						self.current = Some(Visit::Bindings {
							subject,
							trait_index: bound.trait_index,
							bindings: &bound.bindings,
							context,
						});
					}
					return Some(Fact {
						subject,
						kind: AssumptionKind::Trait {
							trait_index: bound.trait_index,
							source: TraitAssumptionSource::Bound(bound.source),
						},
						self_substitution: context,
					});
				}
				Some(Visit::Bindings {
					subject,
					trait_index,
					bindings,
					context,
				}) => {
					let Some((binding, remaining)) = bindings.split_first()
					else {
						self.current = self.parents.pop();
						continue;
					};
					let projection = types.intern(Type::AssocTypeProjection {
						base: subject,
						trait_index,
						assoc_type_index: binding.assoc_type_index,
					});
					let rest = Visit::Bindings {
						subject,
						trait_index,
						bindings: remaining,
						context,
					};
					if binding.required_bounds.is_empty() {
						self.current = Some(rest);
					} else {
						if !remaining.is_empty() {
							self.parents.push(rest);
						}
						self.current = Some(Visit::Traits {
							subject: projection,
							bounds: &binding.required_bounds,
							context,
						});
					}
					if !matches!(binding.kind, ImpliedBindingKind::Bound) {
						return Some(Fact {
							subject: projection,
							kind: AssumptionKind::Equality(&binding.kind),
							self_substitution: context,
						});
					}
				}
				None => {
					let source = self.sources.next(types)?;
					self.current = Some(Visit::Traits {
						subject: source.subject,
						bounds: source.bounds,
						context: source.context,
					});
					if let Some(trait_index) = source.reflexive_trait {
						return Some(Fact {
							subject: source.subject,
							kind: AssumptionKind::Trait {
								trait_index,
								source: TraitAssumptionSource::TraitSelf(
									trait_index,
								),
							},
							self_substitution: source.context,
						});
					}
				}
			}
		}
	}
}

// ---- Effective bounds: the declaration bounds along a receiver's projection path

/// Interpretation of Self in one associated declaration's bound tree.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct SelfSubstitution {
	pub(super) env: TypeEnvIdx,
	pub(super) receiver: TypeIndex,
}

pub(super) struct BoundView<'a> {
	pub(super) bound: &'a ImpliedTraitBound,
	pub(super) context: Option<SelfSubstitution>,
}

/// Whether `effective_bounds`' traversal reached a state where its equality
/// facts are safe to read. Separate from `EqualityLookup` (the caller-facing
/// result of an actual lookup): `Pending` and `Overflowed` used to collapse
/// into the same `facts_ready: bool = false`, but they call for different
/// handling — `Pending` is a normal, temporary state a caller can retry once
/// the dependency it's waiting on resolves; `Overflowed` never resolves no
/// matter how many times it's retried, and needs its own diagnostic instead
/// of silently masquerading as "not resolved yet".
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Readiness {
	Ready,
	Pending,
	Overflowed,
}

impl Readiness {
	/// Keeps the more severe of two readiness observations gathered while
	/// walking a receiver path — order of collection shouldn't matter.
	pub(super) fn and(self, other: Readiness) -> Readiness {
		match (self, other) {
			(Readiness::Overflowed, _) | (_, Readiness::Overflowed) => {
				Readiness::Overflowed
			}
			(Readiness::Pending, _) | (_, Readiness::Pending) => {
				Readiness::Pending
			}
			(Readiness::Ready, Readiness::Ready) => Readiness::Ready,
		}
	}

	pub(super) fn from_ready(ready: bool) -> Readiness {
		if ready {
			Readiness::Ready
		} else {
			Readiness::Pending
		}
	}
}

/// Declaration bounds for one projection on the receiver path. Its identity
/// also selects the nested constraints contributed by each ancestor source.
#[derive(Clone, Copy)]
struct ProjectionBounds<'a> {
	trait_index: TraitIdx,
	assoc_type_index: AssocTypeIdx,
	bounds: &'a [ImpliedTraitBound],
	context: SelfSubstitution,
}

/// A cursor over borrowed bound sources, from the receiver's declaration
/// through its ancestors to the root parameter. Bounds are never flattened
/// or cloned. A parameter or a single projection needs no heap storage.
pub(super) struct EffectiveBounds<'a> {
	projections: Option<SmallVec<ProjectionBounds<'a>>>,
	root: &'a [ImpliedTraitBound],
	source_index: usize,
	current: std::slice::Iter<'a, ImpliedTraitBound>,
	context: Option<SelfSubstitution>,
	pub(super) readiness: Readiness,
	pub(super) reflexive_trait: Option<TraitIdx>,
}

impl<'a> EffectiveBounds<'a> {
	fn projections(&self) -> &[ProjectionBounds<'a>] {
		match &self.projections {
			None => &[],
			Some(SmallVec::One(source)) => std::slice::from_ref(source),
			Some(SmallVec::Many(sources)) => sources,
		}
	}
}

impl<'a> Iterator for EffectiveBounds<'a> {
	type Item = BoundView<'a>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if let Some(bound) = self.current.next() {
				return Some(BoundView {
					bound,
					context: self.context,
				});
			}
			let sources = self.projections();
			if self.source_index > sources.len() {
				return None;
			}
			let (mut bounds, context): (&'a [ImpliedTraitBound], _) =
				match sources.get(self.source_index) {
					Some(source) => (source.bounds, Some(source.context)),
					None => (self.root, None),
				};
			// Ancestor facts describe the ancestor's type. Follow the
			// intervening projections to select facts about this receiver.
			for projection in sources[..self.source_index].iter().rev() {
				let Some(bound) = bounds
					.iter()
					.find(|bound| bound.trait_index == projection.trait_index)
				else {
					bounds = &[];
					break;
				};
				let Some(binding) = bound.bindings.iter().find(|binding| {
					binding.assoc_type_index == projection.assoc_type_index
				}) else {
					bounds = &[];
					break;
				};
				bounds = &binding.required_bounds;
			}
			self.source_index += 1;
			self.current = bounds.iter();
			self.context = context;
		}
	}
}

impl<'a> AssumptionReader<'a> {
	/// The caller prepares declaration bounds first. Readiness is computed
	/// for the whole receiver path even if a consumer stops iteration early.
	pub(super) fn effective_bounds(
		&self,
		types: &TypeInterner,
		mut receiver: TypeIndex,
		recursion_budget: usize,
	) -> EffectiveBounds<'a> {
		let reflexive_trait = match *types.resolve(receiver) {
			Type::TypeParam { env, .. } => match self.type_envs.owner(env) {
				TypeEnvOwner::Trait(index) => Some(index),
				_ => None,
			},
			_ => None,
		};
		let mut projections = None;
		let mut root = &[][..];
		let mut readiness = Readiness::Ready;
		let mut remaining = recursion_budget;
		while remaining > 0 {
			match *types.resolve(receiver) {
				Type::TypeParam { env, param_index } => {
					let bounds = &self.param_bounds[usize::from(env)]
						[param_index as usize];
					root = bounds.facts.current();
					readiness = readiness
						.and(Readiness::from_ready(bounds.facts.is_ready()));
					break;
				}
				Type::AssocTypeProjection {
					base,
					trait_index,
					assoc_type_index,
				} => {
					let declaration = self.assoc_types
						[usize::from(assoc_type_index)]
					.as_ref();
					readiness = readiness.and(Readiness::from_ready(
						declaration.is_some_and(|value| value.facts.is_ready()),
					));
					let source = ProjectionBounds {
						trait_index,
						assoc_type_index,
						bounds: declaration
							.map(|value| value.facts.current())
							.unwrap_or_default(),
						context: SelfSubstitution {
							env: self.traits[usize::from(trait_index)].env,
							receiver: base,
						},
					};
					match &mut projections {
						None => projections = Some(SmallVec::new(source)),
						Some(sources) => sources.push(source),
					}
					receiver = base;
					remaining -= 1;
				}
				_ => break,
			}
		}
		if remaining == 0 {
			readiness = readiness.and(Readiness::Overflowed);
		}
		EffectiveBounds {
			projections,
			root,
			source_index: 0,
			current: [].iter(),
			context: None,
			readiness,
			reflexive_trait,
		}
	}
}

impl TypeContext<'_, '_, '_> {
	pub(super) fn reader(&self) -> AssumptionReader<'_> {
		AssumptionReader::new(
			&self.type_envs,
			&self.param_bounds,
			&self.traits,
			&self.assoc_types,
		)
	}

	/// Lend fact storage and the interner separately, so traversing facts can
	/// intern projected subjects without cloning or mutating their bound trees.
	pub(super) fn assumptions(
		&mut self,
	) -> (AssumptionReader<'_>, &mut TypeInterner) {
		(
			AssumptionReader::new(
				&self.type_envs,
				&self.param_bounds,
				&self.traits,
				&self.assoc_types,
			),
			&mut self.types,
		)
	}

	pub(super) fn effective_bounds(
		&self,
		receiver: TypeIndex,
	) -> EffectiveBounds<'_> {
		self.reader().effective_bounds(
			&self.types,
			receiver,
			self.solver.state.recursion_budget,
		)
	}
}
