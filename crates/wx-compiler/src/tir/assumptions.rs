//! Declaration-local assumptions, read from the existing bound tables.
//!
//! Scope traversal visits the finite parameter-bound trees. Declaration
//! bounds are read along a requested subject's projection path instead of
//! recursively expanding every associated type: a recursive trait can
//! describe infinitely many such paths.

use super::bounds::{
	BoundId, EffectiveBounds, ImpliedAssocBinding, ImpliedBindingKind,
	ImpliedTraitBound, Readiness, SelfSubstitution,
};
use super::defs::TraitIdx;
use super::signatures::{
	AssocTypeSignature, ParamBounds, SignatureBuilder, SignatureRegistry,
	TraitSignature,
};
use super::types::{
	Type, TypeEnvArena, TypeEnvIdx, TypeEnvOwner, TypeIndex, TypeInterner,
};

/// The assumptions available at a declaration, including enclosing scopes.
/// This is distinct from a type parameter's declaring environment: a query
/// about an outer parameter can use additional facts from an inner scope.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) struct AssumptionContext {
	scope: TypeEnvIdx,
}

impl AssumptionContext {
	pub(super) fn new(scope: TypeEnvIdx) -> Self {
		Self { scope }
	}
	pub(super) fn scope(self) -> TypeEnvIdx {
		self.scope
	}
}

/// An unfinished dependency is retryable; a failed query needs recovery.
/// `Ok` may still contain a valid abstract type or an unsatisfied requirement.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum QueryError {
	Pending,
	Failed,
}

pub(super) type QueryResult<T> = Result<T, QueryError>;

/// A borrowed view shared by signature construction and its finished output.
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
pub(super) struct Assumption<'a> {
	pub(super) subject: TypeIndex,
	pub(super) kind: AssumptionKind<'a>,
	pub(super) self_substitution: Option<SelfSubstitution>,
}

impl<'a> AssumptionReader<'a> {
	/// Read memberships and equalities in this scope and its ancestors.
	/// Readiness describes these parameter trees; associated declaration
	/// dependencies are inspected separately by `subject_facts`.
	pub(super) fn scoped_facts(
		&self,
		cx: AssumptionContext,
		types: &TypeInterner,
	) -> AssumptionFacts<'a> {
		let mut readiness = Readiness::Ready;
		let mut roots = ScopedRoots::new(self, cx);
		while let Some(root) = roots.next(types) {
			readiness = readiness.and(root.readiness);
		}
		AssumptionFacts {
			sources: Sources::Scope(ScopedRoots::new(self, cx)),
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
		remaining_depth: usize,
	) -> AssumptionFacts<'a> {
		let bounds = self.effective_bounds(types, subject, remaining_depth);
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
	fn new(reader: &AssumptionReader<'a>, cx: AssumptionContext) -> Self {
		Self {
			type_envs: reader.type_envs,
			param_bounds: reader.param_bounds,
			scope: Some(cx.scope),
			param_index: 0,
		}
	}

	fn next(&mut self, types: &TypeInterner) -> Option<BoundSource<'a>> {
		while let Some(env) = self.scope {
			if env != TypeEnvIdx::ROOT {
				let params = self.type_envs.frame(env);
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
						reflexive_trait: match self.type_envs.frame_owner(env) {
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
	) -> Option<Assumption<'a>> {
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
					return Some(Assumption {
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
						return Some(Assumption {
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
						return Some(Assumption {
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

impl SignatureBuilder<'_, '_> {
	/// Lend fact storage and the interner separately, so traversing facts can
	/// intern projected subjects without cloning or mutating their bound trees.
	pub(super) fn assumptions(
		&mut self,
	) -> (AssumptionReader<'_>, &mut TypeInterner) {
		(
			AssumptionReader {
				type_envs: &self.type_envs,
				param_bounds: &self.param_bounds,
				traits: &self.traits,
				assoc_types: &self.assoc_types,
			},
			&mut self.types,
		)
	}
}

impl SignatureRegistry {
	/// Body checking reads the same facts after construction has completed.
	/// The function's stored scope supplies its context; normalized type owners
	/// do not. Only the interner is mutable, to form projected subjects.
	pub(super) fn assumptions(
		&mut self,
	) -> (AssumptionReader<'_>, &mut TypeInterner) {
		(
			AssumptionReader {
				type_envs: &self.type_envs,
				param_bounds: &self.param_bounds,
				traits: &self.traits,
				assoc_types: &self.assoc_types,
			},
			&mut self.types,
		)
	}
}
