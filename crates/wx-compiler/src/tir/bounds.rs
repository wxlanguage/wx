//! Trait bounds: as written, as clauses, and as read.
//!
//! A clause is one statement a bound makes about types: `T: Tr` (a
//! `TraitClause`) or `<T as Tr>::A == X` (an `EqualityClause`). Its
//! declaration assumes it; a use of the declaration proves it. (rustc's term:
//! a predicate that can stand in a `where` clause, as opposed to one that is
//! only ever proved, such as well-formedness.)
//!
//! Each written bound is stored once in the `BoundArena`, with its spans. A
//! declaration's written bounds become its clauses (`BoundClauses`): flat runs
//! in the `ClauseArena`, nested bounds as clauses on projections and each
//! trait's own clauses (its supertraits) substituted for `Self`. They are
//! built in two passes: memberships before any equality's value is resolved,
//! so a sibling's value can name members they supply, then equalities.
//!
//! Proving a use's clauses reads the tables directly
//! (`Solver::satisfies_clauses`). `ClauseTables` answers the two questions
//! asked of them otherwise:
//!
//! - what a scope assumes (`assumed_traits`, `assumptions_readiness`): every
//!   clause of every parameter in the scope and the frames around it, rustc's
//!   `ParamEnv`;
//! - what a type's own declarations state about it (`declarations_of`,
//!   `declared_traits`): the parameter at its root and the associated
//!   declarations along its projection path, whatever the scope. An
//!   associated declaration's clauses are read there rather than expanded into
//!   a parameter's: a recursive trait describes infinitely many paths.
//!
//! A query's assumptions are named by a `TypeEnvIdx` called
//! `assumption_context`: the declaration whose bounds (and enclosing
//! declarations' bounds) apply. It is not the environment a parameter was
//! declared in; a query about an outer parameter can use extra facts from an
//! inner declaration's context. Where both meet (`match_impl_target_and_bounds`)
//! the `assumption_context` is the caller's and `impl_env` the candidate impl's:
//! requirements are proved in the caller's context.

use std::marker::PhantomData;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::index::index_newtype;
use crate::vfs::FileId;

use super::defs::{DefId, DefKind, DefinitionRegistry, TraitIdx};
use super::members::AssocTypeProjectionTarget;
use super::signatures::{
	AssocTypeSignature, ParamBounds, QueryInfo, SignatureStatus,
	TraitSignature, TypeContext,
};
use super::types::{
	Substitution, Type, TypeEnvArena, TypeEnvIdx, TypeEnvOwner, TypeIndex,
	TypeInterner,
};

index_newtype!(BoundId);

/// One binding within a source bound. The index is stable because an
/// occurrence's completed binding slice is immutable after publication.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct BindingRef {
	pub(super) bound: BoundId,
	pub(super) index: u32,
}

/// One resolved trait bound as written, including its source location.
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct SourceTraitBound {
	pub(super) trait_index: TraitIdx,
	pub(super) span: SourceSpan,
	pub(super) bindings: Box<[SourceAssocBinding]>,
}

/// One `Assoc = Type` or `Assoc: Bounds` clause inside a written bound.
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct SourceAssocBinding {
	/// The associated type it constrains, under the trait that declares it:
	/// the bound's own trait, or one of its supertraits.
	pub(super) target: AssocTypeProjectionTarget,
	pub(super) name: Spanned<SymbolU32>,
	pub(super) kind: BindingRequirement,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum BindingRequirement {
	Equals(Spanned<TypeIndex>),
	Bound(Box<[BoundId]>),
}

/// The clause `subject: trait_index`, stated by a bound.
/// `source` is the written bound that states it, which for a supertrait's
/// clause is the bound in the supertrait's declaration; `origin` is the bound
/// written on this declaration's subject whose expansion brought it in.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct TraitClause {
	pub(super) subject: TypeIndex,
	pub(super) trait_index: TraitIdx,
	pub(super) source: BoundId,
	pub(super) origin: BoundId,
}

/// The clause `projection == value`, stated by a bound.
/// `source` is the written equality; `origin` as for `TraitClause`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct EqualityClause {
	pub(super) projection: TypeIndex,
	pub(super) value: TypeIndex,
	pub(super) source: BindingRef,
	pub(super) origin: BoundId,
}

/// A run of clauses in the `ClauseArena`, owned by one subject.
pub(super) struct ClauseRange<T> {
	start: u32,
	len: u32,
	clauses: PhantomData<fn() -> T>,
}

impl<T> Clone for ClauseRange<T> {
	fn clone(&self) -> Self {
		*self
	}
}

impl<T> Copy for ClauseRange<T> {}

impl<T> ClauseRange<T> {
	pub(super) const EMPTY: Self = Self {
		start: 0,
		len: 0,
		clauses: PhantomData,
	};

	fn slice(self, clauses: &[T]) -> &[T] {
		&clauses[self.start as usize..][..self.len as usize]
	}
}

/// Whether a subject's equality pass has run: the second half of
/// `BoundClauses`, published once its memberships are.
#[derive(Clone, Copy)]
pub(super) enum Equalities {
	/// The memberships are published, the values are not resolved yet, so a
	/// read may conclude neither a proof nor a failure. Not an answer
	/// (`SolverError::Pending`); ask again once construction has advanced.
	Pending,
	/// The pass is done: every equality the bound states.
	Final(ClauseRange<EqualityClause>),
}

impl Equalities {
	/// The range once the pass has run; `None` while it is pending.
	pub(super) fn final_range(self) -> Option<ClauseRange<EqualityClause>> {
		match self {
			Self::Pending => None,
			Self::Final(range) => Some(range),
		}
	}

	/// The range, for tests that build final clauses by hand.
	#[cfg(test)]
	pub(super) fn resolved(self) -> ClauseRange<EqualityClause> {
		self.final_range().expect("the test's clauses are final")
	}
}

/// The clauses one subject's bounds state: a parameter's (`T: Tr where { A =
/// X, A: B }`), or an associated type declaration's (`type A: B`, about
/// `<Self as Tr>::A`).
/// Each written bound becomes a flat run of clauses, its nested bounds as
/// clauses on projections and each trait's own clauses (its supertraits, and
/// theirs) substituted for `Self`. The trait clauses are published before
/// any equality's value is resolved, so a sibling's value can name members
/// they supply; the equalities stay `Pending` until the values are resolved.
#[derive(Clone, Copy)]
pub(super) struct BoundClauses {
	pub(super) traits: ClauseRange<TraitClause>,
	pub(super) equalities: Equalities,
}

impl BoundClauses {
	/// A subject whose bounds are not published yet.
	pub(super) const PENDING: Self = Self {
		traits: ClauseRange::EMPTY,
		equalities: Equalities::Pending,
	};
	/// A subject that assumes nothing.
	pub(super) const NONE: Self = Self {
		traits: ClauseRange::EMPTY,
		equalities: Equalities::Final(ClauseRange::EMPTY),
	};
}

/// Every subject's clauses, append-only, addressed by `ClauseRange`.
#[derive(Default)]
pub(super) struct ClauseArena {
	traits: Vec<TraitClause>,
	equalities: Vec<EqualityClause>,
}

impl ClauseArena {
	pub(super) fn traits(
		&self,
		range: ClauseRange<TraitClause>,
	) -> &[TraitClause] {
		range.slice(&self.traits)
	}

	pub(super) fn equalities(
		&self,
		range: ClauseRange<EqualityClause>,
	) -> &[EqualityClause] {
		range.slice(&self.equalities)
	}

	pub(super) fn push_traits(
		&mut self,
		clauses: &[TraitClause],
	) -> ClauseRange<TraitClause> {
		push_range(&mut self.traits, clauses)
	}

	pub(super) fn push_equalities(
		&mut self,
		clauses: &[EqualityClause],
	) -> ClauseRange<EqualityClause> {
		push_range(&mut self.equalities, clauses)
	}
}

fn push_range<T: Copy>(arena: &mut Vec<T>, clauses: &[T]) -> ClauseRange<T> {
	let start = u32::try_from(arena.len())
		.expect("clause arena exceeded u32 index capacity");
	arena.extend_from_slice(clauses);
	ClauseRange {
		start,
		len: u32::try_from(clauses.len()).unwrap(),
		clauses: PhantomData,
	}
}

#[derive(Default)]
pub(super) struct BoundArena {
	bounds: Vec<BoundEntry>,
}

/// Construction state belongs to the arena, not to a written requirement.
/// A reservation carries only the identity and location needed by membership
/// lookup; the AST retains the unresolved binding expressions.
enum BoundEntry {
	Reserved {
		trait_index: TraitIdx,
		span: SourceSpan,
	},
	Resolved(SourceTraitBound),
}

impl BoundArena {
	fn next_id(&self) -> BoundId {
		BoundId::new(
			u32::try_from(self.bounds.len())
				.expect("bound arena exceeded u32 index capacity"),
		)
	}

	pub(super) fn reserve(
		&mut self,
		trait_index: TraitIdx,
		span: SourceSpan,
	) -> BoundId {
		let id = self.next_id();
		self.bounds.push(BoundEntry::Reserved { trait_index, span });
		id
	}

	pub(super) fn span(&self, id: BoundId) -> SourceSpan {
		match &self.bounds[usize::from(id)] {
			BoundEntry::Reserved { span, .. } => *span,
			BoundEntry::Resolved(bound) => bound.span,
		}
	}

	pub(super) fn trait_index(&self, id: BoundId) -> TraitIdx {
		match &self.bounds[usize::from(id)] {
			BoundEntry::Reserved { trait_index, .. } => *trait_index,
			BoundEntry::Resolved(bound) => bound.trait_index,
		}
	}

	pub(super) fn fill(&mut self, id: BoundId, bound: SourceTraitBound) {
		let slot = &mut self.bounds[usize::from(id)];
		let BoundEntry::Reserved { trait_index, span } = slot else {
			panic!("source bounds are immutable after publication")
		};
		assert_eq!(*trait_index, bound.trait_index);
		assert_eq!(*span, bound.span);
		*slot = BoundEntry::Resolved(bound);
	}

	pub(super) fn get(&self, id: BoundId) -> &SourceTraitBound {
		match &self.bounds[usize::from(id)] {
			BoundEntry::Resolved(bound) => bound,
			BoundEntry::Reserved { .. } => {
				panic!("source bound has not finished resolving")
			}
		}
	}

	pub(super) fn binding(&self, reference: BindingRef) -> &SourceAssocBinding {
		&self.get(reference.bound).bindings[reference.index as usize]
	}
}

impl TypeContext<'_, '_, '_> {
	/// The frame whose `Self` clauses are the trait `bound` names, once its
	/// signature is available. While it is being built the bound closes a
	/// cycle, reported here at `bound`, and expands to nothing.
	fn trait_clause_env(&mut self, bound: BoundId) -> Option<TypeEnvIdx> {
		let trait_index = self.bounds.trait_index(bound);
		self.trait_env(trait_index, self.bounds.span(bound))
	}

	/// The declaration whose signature holds `trait_index`'s: its typeset's
	/// for a trait a typeset generates.
	pub(super) fn trait_def_id(&self, trait_index: TraitIdx) -> DefId {
		match self.defs.traits[usize::from(trait_index)].typeset {
			Some(typeset_index) => DefId::Typeset(typeset_index),
			None => DefId::Trait(trait_index),
		}
	}

	/// The frame of `trait_index`, once its signature is available. While it
	/// is being built, `reference` closes a cycle, reported here once.
	pub(super) fn trait_env(
		&mut self,
		trait_index: TraitIdx,
		reference: SourceSpan,
	) -> Option<TypeEnvIdx> {
		let def_id = self.trait_def_id(trait_index);
		match self.ensure_signature(QueryInfo {
			def_id,
			requested_at: Some(reference),
		}) {
			SignatureStatus::Available(_) => {
				Some(self.traits[usize::from(trait_index)].env)
			}
			SignatureStatus::Cycle => {
				let diagnostic =
					self.report_cyclic_implied_trait_bounds(def_id, reference);
				self.diagnostics.push(diagnostic);
				None
			}
			SignatureStatus::CycleReported => None,
		}
	}

	/// Appends the trait clauses of the trait `bound` names, with `Self`
	/// replaced by `subject`, as brought in by `origin`.
	pub(super) fn inherit_trait_clauses(
		&mut self,
		out: &mut Vec<TraitClause>,
		subject: TypeIndex,
		bound: BoundId,
		origin: BoundId,
	) {
		let Some(env) = self.trait_clause_env(bound) else {
			return;
		};
		let range = self.param_bounds[usize::from(env)][0].clauses.traits;
		for clause in self.clauses.traits(range) {
			let subject = self.types.substitute(
				clause.subject,
				Substitution {
					envs: &self.type_envs,
					env,
					args: &[subject],
				},
			);
			push_trait_clause(
				out,
				TraitClause {
					subject,
					origin,
					..*clause
				},
			);
		}
	}

	/// The equality clauses the written bounds `ids` state about `subject`
	/// (named `name`), each trait's own equalities included. Two values an
	/// outer constructor tells apart are a conflict, reported here.
	pub(super) fn equality_clauses(
		&mut self,
		subject: TypeIndex,
		ids: &[BoundId],
		name: SymbolU32,
	) -> ClauseRange<EqualityClause> {
		let mut builder = EqualityClauseBuilder {
			bounds: &self.bounds,
			clauses: &self.clauses,
			param_bounds: &self.param_bounds,
			traits: &self.traits,
			type_envs: &self.type_envs,
			types: &mut self.types,
			out: Vec::new(),
			conflicts: Vec::new(),
		};
		for &id in ids {
			builder.collect(subject, id, id);
		}
		let EqualityClauseBuilder { out, conflicts, .. } = builder;
		for conflict in conflicts {
			self.diagnostics.push(report_conflicting_assoc_type_binding(
				self.strings,
				self.defs,
				&self.bounds,
				name,
				conflict,
			));
		}
		self.clauses.push_equalities(&out)
	}

	/// Demand the associated declarations along `receiver`'s projection path,
	/// whose clauses can describe it (`ClauseTables::declarations_of`). A
	/// declaration whose equalities are not resolved yet still supplies its
	/// memberships, but not an equality.
	pub(super) fn prepare_declarations_of(
		&mut self,
		mut receiver: TypeIndex,
		reference: SourceSpan,
	) -> Result<(), ()> {
		while let Type::AssocTypeProjection {
			base,
			assoc_type_index,
			..
		} = *self.types.resolve(receiver)
		{
			if self.assoc_types[usize::from(assoc_type_index)].is_none() {
				self.ensure_assoc_type_bounds(assoc_type_index, reference)?;
			}
			receiver = base;
		}
		Ok(())
	}
}

struct AssocBindingConflict {
	first: BindingRef,
	second: BindingRef,
	/// The written bound whose expansion brought the two values together.
	merge_point: BoundId,
}

/// The equality pass over written bounds. It walks the same bounds as the
/// membership pass, which already demanded every trait they name, so it
/// forces nothing: it reads finished tables and borrows what it walks. A
/// trait still being built has no `Self` equalities yet, and lends none.
struct EqualityClauseBuilder<'a> {
	bounds: &'a BoundArena,
	clauses: &'a ClauseArena,
	param_bounds: &'a [Box<[ParamBounds]>],
	traits: &'a [TraitSignature],
	type_envs: &'a TypeEnvArena,
	types: &'a mut TypeInterner,
	out: Vec<EqualityClause>,
	conflicts: Vec<AssocBindingConflict>,
}

impl EqualityClauseBuilder<'_> {
	/// The equalities the written bound `id` states about `subject`, its
	/// nested bounds' included, then its trait's own, as brought in by
	/// `origin`.
	fn collect(&mut self, subject: TypeIndex, id: BoundId, origin: BoundId) {
		let bound = self.bounds.get(id);
		for (index, binding) in bound.bindings.iter().enumerate() {
			let source = BindingRef {
				bound: id,
				index: u32::try_from(index)
					.expect("bound binding count exceeded u32 capacity"),
			};
			let projection = binding.target.project(self.types, subject);
			match &binding.kind {
				BindingRequirement::Equals(value) => {
					let written_since = self.out.len();
					push_equality_clause(
						self.types,
						&mut self.out,
						EqualityClause {
							projection,
							value: value.inner,
							source,
							origin,
						},
						written_since,
						&mut self.conflicts,
					);
				}
				BindingRequirement::Bound(nested) => {
					for &nested in nested {
						self.collect(projection, nested, origin);
					}
				}
			}
		}
		let env = self.traits[usize::from(bound.trait_index)].env;
		let Some(range) = self.param_bounds[usize::from(env)]
			.first()
			.and_then(|bounds| bounds.clauses.equalities.final_range())
		else {
			return;
		};
		let inherited_since = self.out.len();
		for clause in self.clauses.equalities(range) {
			let substitution = Substitution {
				envs: self.type_envs,
				env,
				args: &[subject],
			};
			let projection =
				self.types.substitute(clause.projection, substitution);
			let value = self.types.substitute(clause.value, substitution);
			push_equality_clause(
				self.types,
				&mut self.out,
				EqualityClause {
					projection,
					value,
					origin,
					..*clause
				},
				inherited_since,
				&mut self.conflicts,
			);
		}
	}
}

/// Adds `clause` unless the same membership is already there; the first
/// source of a membership is the one diagnostics name.
pub(super) fn push_trait_clause(
	out: &mut Vec<TraitClause>,
	clause: TraitClause,
) {
	if !out.iter().any(|existing| {
		existing.subject == clause.subject
			&& existing.trait_index == clause.trait_index
	}) {
		out.push(clause);
	}
}

/// Adds `clause` unless its value is already known for its projection. A
/// value an outer constructor tells apart from a known one is a conflict,
/// reported once for that value; both values stay, so the projection reads as
/// ambiguous. The clauses from `inherited_since` on came with `clause` from
/// one supertrait, whose own declaration reported their conflicts.
fn push_equality_clause(
	types: &TypeInterner,
	out: &mut Vec<EqualityClause>,
	clause: EqualityClause,
	inherited_since: usize,
	conflicts: &mut Vec<AssocBindingConflict>,
) {
	let mut conflict = None;
	for (index, existing) in out.iter().enumerate() {
		if existing.projection != clause.projection {
			continue;
		}
		if existing.value == clause.value {
			return;
		}
		if conflict.is_none()
			&& known_distinct(types, existing.value, clause.value)
		{
			conflict = Some((index, existing.source));
		}
	}
	if let Some((index, first)) = conflict
		&& index < inherited_since
	{
		conflicts.push(AssocBindingConflict {
			first,
			second: clause.source,
			merge_point: clause.origin,
		});
	}
	out.push(clause);
}

/// The clause tables, borrowed: what a scope assumes, and what a type's own
/// declarations state about it. Shared by signature construction and body
/// checking; it does not demand signatures, normalize types, or prove
/// requirements.
#[derive(Clone, Copy)]
pub(super) struct ClauseTables<'a> {
	pub(super) type_envs: &'a TypeEnvArena,
	pub(super) param_bounds: &'a [Box<[ParamBounds]>],
	pub(super) traits: &'a [TraitSignature],
	pub(super) assoc_types: &'a [Option<AssocTypeSignature>],
	pub(super) clauses: &'a ClauseArena,
}

impl<'a> ClauseTables<'a> {
	pub(super) fn new(
		type_envs: &'a TypeEnvArena,
		param_bounds: &'a [Box<[ParamBounds]>],
		traits: &'a [TraitSignature],
		assoc_types: &'a [Option<AssocTypeSignature>],
		clauses: &'a ClauseArena,
	) -> Self {
		Self {
			type_envs,
			param_bounds,
			traits,
			assoc_types,
			clauses,
		}
	}

	/// The memberships assumed in `assumption_context` and the frames around
	/// it, as `(subject, trait)`: every parameter's trait clauses, and a
	/// trait's own `Self: Trait`, which no clause states.
	pub(super) fn assumed_traits(
		&self,
		assumption_context: TypeEnvIdx,
	) -> impl Iterator<Item = (TypeIndex, TraitIdx)> + 'a {
		let Self {
			type_envs,
			param_bounds,
			clauses,
			..
		} = *self;
		type_envs.chain(assumption_context).flat_map(move |frame| {
			let reflexive = match type_envs.owner(frame) {
				TypeEnvOwner::Trait(index) => {
					Some((type_envs.param_types(frame)[0], index))
				}
				_ => None,
			};
			reflexive.into_iter().chain(
				param_bounds[usize::from(frame)].iter().flat_map(
					move |bounds| {
						clauses
							.traits(bounds.clauses.traits)
							.iter()
							.map(|clause| (clause.subject, clause.trait_index))
					},
				),
			)
		})
	}

	/// The subjects assumed in `assumption_context` to implement `trait_index`.
	pub(super) fn assumed_subjects(
		&self,
		assumption_context: TypeEnvIdx,
		trait_index: TraitIdx,
	) -> impl Iterator<Item = TypeIndex> + 'a {
		self.assumed_traits(assumption_context)
			.filter(move |&(_, assumed)| assumed == trait_index)
			.map(|(subject, _)| subject)
	}

	/// Whether every parameter in scope has its equalities: a membership read
	/// before that can still be one an equality's value has to confirm.
	pub(super) fn assumptions_readiness(
		&self,
		assumption_context: TypeEnvIdx,
	) -> Readiness {
		let mut readiness = Readiness::Ready;
		for frame in self.type_envs.chain(assumption_context) {
			for bounds in &self.param_bounds[usize::from(frame)] {
				readiness =
					readiness.and(Readiness::from(bounds.clauses.equalities));
			}
		}
		readiness
	}

	/// The subjects whose clauses can describe `receiver`: each associated
	/// declaration on its projection path, outermost first, then the
	/// parameter at its root. Missing or provisional declarations make the
	/// path `Pending`; reading never forces them.
	pub(super) fn declarations_of<'t>(
		&self,
		types: &'t TypeInterner,
		receiver: TypeIndex,
		recursion_budget: usize,
	) -> DeclarationSources<'a, 't> {
		let reflexive_trait = match *types.resolve(receiver) {
			Type::TypeParam { env, .. } => match self.type_envs.owner(env) {
				TypeEnvOwner::Trait(index) => Some(index),
				_ => None,
			},
			_ => None,
		};
		let mut sources = DeclarationSources {
			tables: *self,
			types,
			receiver,
			current: Some(receiver),
			remaining: recursion_budget,
			readiness: Readiness::Ready,
			reflexive_trait,
		};
		// Computed up front, so stopping early cannot hide `Pending`.
		let mut readiness = Readiness::Ready;
		let mut walk = DeclarationSources { ..sources };
		while let Some(source) = walk.next() {
			readiness =
				readiness.and(Readiness::from(source.clauses.equalities));
		}
		if walk.remaining == 0 {
			readiness = readiness.and(Readiness::Overflowed);
		}
		sources.readiness = readiness;
		sources
	}

	/// The traits clauses assume of `receiver` itself, its own `Self: Trait`
	/// first. Duplicates are not removed.
	pub(super) fn declared_traits<'t>(
		&self,
		types: &'t TypeInterner,
		receiver: TypeIndex,
		recursion_budget: usize,
	) -> DeclaredTraits<'a, 't> {
		let sources = self.declarations_of(types, receiver, recursion_budget);
		DeclaredTraits {
			readiness: sources.readiness,
			reflexive: sources.reflexive_trait,
			sources,
			current: None,
		}
	}
}

/// One subject whose clauses can describe a receiver (`declarations_of`).
#[derive(Clone, Copy)]
pub(super) struct DeclarationSource {
	pub(super) clauses: BoundClauses,
	/// For an associated declaration, its trait's `Self` read as the
	/// projection's base. `None` for the root parameter, whose clauses name
	/// the receiver in its own terms.
	pub(super) context: Option<SelfSubstitution>,
}

impl DeclarationSource {
	/// Whether `subject`, a subject of this source's clauses, is `receiver`:
	/// for a declaration, the same projections over its `Self` as over the
	/// base it is read with. Compared without interning.
	pub(super) fn names(
		self,
		types: &TypeInterner,
		type_envs: &TypeEnvArena,
		mut subject: TypeIndex,
		mut receiver: TypeIndex,
	) -> bool {
		let Some(context) = self.context else {
			return subject == receiver;
		};
		let self_type = type_envs.param_types(context.env)[0];
		loop {
			if subject == self_type {
				return receiver == context.receiver;
			}
			match (types.resolve(subject), types.resolve(receiver)) {
				(
					Type::AssocTypeProjection {
						base: subject_base,
						trait_index: subject_trait,
						assoc_type_index: subject_assoc,
					},
					Type::AssocTypeProjection {
						base: receiver_base,
						trait_index: receiver_trait,
						assoc_type_index: receiver_assoc,
					},
				) if subject_trait == receiver_trait
					&& subject_assoc == receiver_assoc =>
				{
					(subject, receiver) = (*subject_base, *receiver_base);
				}
				_ => return false,
			}
		}
	}
}

/// The sources along a receiver's projection path (`declarations_of`).
pub(super) struct DeclarationSources<'a, 't> {
	tables: ClauseTables<'a>,
	types: &'t TypeInterner,
	/// The receiver the sources describe.
	pub(super) receiver: TypeIndex,
	current: Option<TypeIndex>,
	remaining: usize,
	pub(super) readiness: Readiness,
	/// `Self: Trait` for a trait's own `Self`, which no clause states.
	pub(super) reflexive_trait: Option<TraitIdx>,
}

impl Iterator for DeclarationSources<'_, '_> {
	type Item = DeclarationSource;

	fn next(&mut self) -> Option<DeclarationSource> {
		let current = self.current.take()?;
		if self.remaining == 0 {
			return None;
		}
		match *self.types.resolve(current) {
			Type::TypeParam { env, param_index } => Some(DeclarationSource {
				clauses: self.tables.param_bounds[usize::from(env)]
					[param_index as usize]
					.clauses,
				context: None,
			}),
			Type::AssocTypeProjection {
				base,
				trait_index,
				assoc_type_index,
			} => {
				self.current = Some(base);
				self.remaining -= 1;
				Some(DeclarationSource {
					clauses: self.tables.assoc_types
						[usize::from(assoc_type_index)]
					.as_ref()
					.map_or(BoundClauses::PENDING, |signature| {
						signature.clauses
					}),
					context: Some(SelfSubstitution {
						env: self.tables.traits[usize::from(trait_index)].env,
						receiver: base,
					}),
				})
			}
			_ => None,
		}
	}
}

/// The traits assumed of a receiver itself (`declared_traits`).
pub(super) struct DeclaredTraits<'a, 't> {
	pub(super) readiness: Readiness,
	reflexive: Option<TraitIdx>,
	sources: DeclarationSources<'a, 't>,
	current: Option<(DeclarationSource, std::slice::Iter<'a, TraitClause>)>,
}

impl Iterator for DeclaredTraits<'_, '_> {
	type Item = TraitIdx;

	fn next(&mut self) -> Option<TraitIdx> {
		if let Some(trait_index) = self.reflexive.take() {
			return Some(trait_index);
		}
		loop {
			if let Some((source, clauses)) = &mut self.current {
				let (tables, types) = (self.sources.tables, self.sources.types);
				let receiver = self.sources.receiver;
				if let Some(clause) = clauses.find(|clause| {
					source.names(
						types,
						tables.type_envs,
						clause.subject,
						receiver,
					)
				}) {
					return Some(clause.trait_index);
				}
			}
			let source = self.sources.next()?;
			let clauses =
				self.sources.tables.clauses.traits(source.clauses.traits);
			self.current = Some((source, clauses.iter()));
		}
	}
}

/// How an associated declaration's clauses are read on a projection path:
/// its trait's `Self`, the frame `env` declares, is the projection's base.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct SelfSubstitution {
	pub(super) env: TypeEnvIdx,
	pub(super) receiver: TypeIndex,
}

/// Whether the clauses a read reached are final, so its equalities are safe
/// to read. Separate from `EqualityLookup` (the caller-facing
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
}

impl From<Equalities> for Readiness {
	fn from(equalities: Equalities) -> Self {
		match equalities {
			Equalities::Pending => Readiness::Pending,
			Equalities::Final(_) => Readiness::Ready,
		}
	}
}

impl TypeContext<'_, '_, '_> {
	pub(super) fn clause_tables(&self) -> ClauseTables<'_> {
		ClauseTables::new(
			&self.type_envs,
			&self.param_bounds,
			&self.traits,
			&self.assoc_types,
			&self.clauses,
		)
	}
}

/// Only incompatible outer constructors establish a conflict here. Symbolic
/// values and differing arguments remain unavailable for reduction; semantic
/// equality checking belongs to a later phase.
pub(super) fn known_distinct(
	types: &TypeInterner,
	a: TypeIndex,
	b: TypeIndex,
) -> bool {
	match (types.resolve(a), types.resolve(b)) {
		// A type without a fixed outer constructor could still become either.
		(
			Type::Error
			| Type::Infer
			| Type::Integer
			| Type::Float
			| Type::String
			| Type::ArrayLiteral
			| Type::TypeParam { .. }
			| Type::AssocTypeProjection { .. },
			_,
		)
		| (
			_,
			Type::Error
			| Type::Infer
			| Type::Integer
			| Type::Float
			| Type::String
			| Type::ArrayLiteral
			| Type::TypeParam { .. }
			| Type::AssocTypeProjection { .. },
		) => false,
		// A nominal type is its declaration: two declarations never meet,
		// whatever their arguments.
		(
			Type::Struct {
				struct_index: a, ..
			},
			Type::Struct {
				struct_index: b, ..
			},
		) => a != b,
		(Type::Enum { enum_index: a }, Type::Enum { enum_index: b }) => a != b,
		(
			Type::Memory { memory_index: a },
			Type::Memory { memory_index: b },
		) => a != b,
		(
			Type::Global { global_index: a },
			Type::Global { global_index: b },
		) => a != b,
		(
			Type::Function { func_index: a, .. },
			Type::Function { func_index: b, .. },
		) => a != b,
		(Type::Tuple { elements: a }, Type::Tuple { elements: b }) => {
			a.len() != b.len()
		}
		// Otherwise the constructor itself: a primitive, `!`, an array, a
		// slice, a pointer or a function reference, whose arguments may
		// still agree.
		(a, b) => std::mem::discriminant(a) != std::mem::discriminant(b),
	}
}

pub(super) fn report_not_a_trait_bound(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	kind: DefKind,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitBound.code())
		.with_message(format!(
			"expected trait, found {} `{name_str}`",
			kind.noun()
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("not a trait"),
		)
}

pub(super) fn report_duplicate_assoc_type_binding(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateAssocTypeBinding.code())
		.with_message(format!(
			"associated type `{name_str}` is bound more than once in this `where` clause"
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("duplicate binding"),
		)
}

/// Two paths reaching the same trait pin one associated type to
/// incompatible values. The references retain both original value spans.
fn report_conflicting_assoc_type_binding(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	arena: &BoundArena,
	subject: SymbolU32,
	conflict: AssocBindingConflict,
) -> Diagnostic<FileId> {
	let first = arena.binding(conflict.first);
	let second = arena.binding(conflict.second);
	let BindingRequirement::Equals(first_value) = &first.kind else {
		unreachable!("conflict points to a source equality")
	};
	let BindingRequirement::Equals(second_value) = &second.kind else {
		unreachable!("conflict points to a source equality")
	};
	let subject_str = strings.resolve(subject).unwrap();
	let trait_name = defs.traits[usize::from(first.target.trait_index)]
		.name
		.inner;
	let trait_str = strings.resolve(trait_name).unwrap();
	let assoc_str = strings.resolve(first.name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateAssocTypeBinding.code())
		.with_message(format!(
			"`{subject_str}` requires conflicting bindings for `{trait_str}::{assoc_str}`"
		))
		.with_label(
			SourceSpan::new(
				arena.get(conflict.second.bound).span.file_id,
				second_value.span,
			)
				.primary_label()
				.with_message("conflicting value bound here"),
		)
		.with_label(
			SourceSpan::new(
				arena.get(conflict.first.bound).span.file_id,
				first_value.span,
			)
				.secondary_label()
				.with_message("first bound to this value here"),
		)
		.with_label(
			arena
				.get(conflict.merge_point)
				.span
				.secondary_label()
				.with_message("bounds merged here"),
		)
}

pub(super) fn report_not_an_associated_type(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	trait_name: SymbolU32,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	let trait_str = strings.resolve(trait_name).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitMember.code())
		.with_message(format!(
			"`{name_str}` is not an associated type of trait `{trait_str}`"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tir::defs::EnumIdx;

	fn clause(index: u32, value: TypeIndex) -> EqualityClause {
		EqualityClause {
			projection: TypeIndex::UNIT,
			value,
			source: BindingRef {
				bound: BoundId::new(0),
				index,
			},
			origin: BoundId::new(0),
		}
	}

	/// Pushes each value as a clause on one projection, returning the values
	/// kept and the conflicts found.
	fn push(values: &[TypeIndex]) -> (Vec<EqualityClause>, usize) {
		let types = TypeInterner::new();
		let (mut out, mut conflicts) = (Vec::new(), Vec::new());
		for (index, &value) in values.iter().enumerate() {
			let written_since = out.len();
			push_equality_clause(
				&types,
				&mut out,
				clause(index as u32, value),
				written_since,
				&mut conflicts,
			);
		}
		(out, conflicts.len())
	}

	#[test]
	fn the_same_value_is_kept_once_with_its_first_source() {
		let (kept, conflicts) = push(&[TypeIndex::U32, TypeIndex::U32]);
		assert_eq!(conflicts, 0);
		assert_eq!(kept.len(), 1);
		assert_eq!(kept[0].source.index, 0);
	}

	#[test]
	fn a_distinct_concrete_value_conflicts_and_both_stay() {
		let (kept, conflicts) = push(&[TypeIndex::U32, TypeIndex::U64]);
		assert_eq!(conflicts, 1);
		assert_eq!(kept.len(), 2);
	}

	#[test]
	fn a_symbolic_value_stays_beside_a_concrete_one() {
		let (kept, conflicts) = push(&[TypeIndex::U32, TypeIndex::INFER]);
		assert_eq!(conflicts, 0);
		assert_eq!(kept.len(), 2);
	}

	/// A concrete conflict is found even when a symbolic value came between:
	/// each value is compared with every value already known.
	#[test]
	fn a_concrete_conflict_is_found_past_a_symbolic_value() {
		let (_, conflicts) =
			push(&[TypeIndex::U32, TypeIndex::INFER, TypeIndex::U64]);
		assert_eq!(conflicts, 1);
	}

	/// A supertrait's conflicting values come together, and its own
	/// declaration reported them: inheriting them reports nothing.
	#[test]
	fn a_conflict_within_one_supertraits_clauses_is_not_reported_again() {
		let types = TypeInterner::new();
		let (mut out, mut conflicts) = (Vec::new(), Vec::new());
		for (index, value) in
			[TypeIndex::U32, TypeIndex::U64].into_iter().enumerate()
		{
			push_equality_clause(
				&types,
				&mut out,
				clause(index as u32, value),
				0,
				&mut conflicts,
			);
		}
		assert!(conflicts.is_empty());
		assert_eq!(out.len(), 2);
	}

	#[test]
	fn distinct_declarations_of_one_kind_are_known_distinct() {
		let mut types = TypeInterner::new();
		let [a, b] = [0, 1].map(|index| {
			types.intern(Type::Enum {
				enum_index: EnumIdx::new(index),
			})
		});
		assert!(known_distinct(&types, a, b));
		assert!(!known_distinct(&types, a, a));
	}

	/// Each value that conflicts with an earlier one is its own report.
	#[test]
	fn each_conflicting_value_is_reported() {
		let (kept, conflicts) =
			push(&[TypeIndex::U32, TypeIndex::U64, TypeIndex::U16]);
		assert_eq!(conflicts, 2);
		assert_eq!(kept.len(), 3);
	}
}
