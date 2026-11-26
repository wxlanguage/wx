//! Clauses: as written, as statements about types, and as what each scope
//! assumes.
//!
//! A source clause is one clause as written, names resolved, spans kept:
//! `T: Container where { Item = U }` on a parameter, its trait with its
//! bindings (`Item = U`, `Item: Marker`, `const LEN: u8`, each a source
//! binding). It is what diagnostics point at, stored once in the
//! `SourceClauseArena`.
//!
//! A clause is one statement about types, a source clause flattened: `T: Tr`
//! (a `TraitClause`), `<T as Tr>::A == X` (an `EqualityClause`), or a
//! constant's value representable as a type (a `RepresentableClause`). It
//! carries no span; it points back at its source clause. A declaration's
//! source clauses become its clauses (`PublishedClauses`): flat runs in the
//! `ClauseArena`, nested bindings as clauses on projections and each trait's
//! own clauses (its supertraits) substituted for `Self`. They are built in two
//! passes: memberships before any equality's value is resolved, so a
//! sibling's value can name members they supply, then equalities. (rustc's
//! term: a predicate that can stand in a `where` clause, as opposed to one
//! that is only ever proved, such as well-formedness.)
//!
//! The same clauses play two roles. Inside their declaration they are
//! assumed: an assumption env holds them. At a use of it they are proved: a
//! frame's requirements.
//!
//! Proving a use's clauses reads the tables directly
//! (`Solver::satisfies_clauses`). `ClauseTables` answers the two questions
//! asked of them otherwise:
//!
//! - what a scope assumes (`assumed_traits`, `assumptions_readiness`): every
//!   clause of its assumption env and the envs around it;
//! - what states something about a type (`declarations_of`,
//!   `declared_traits`): the associated declarations along its projection
//!   path, whatever the scope, then the scope's assumption envs for the
//!   parameter at its root. An associated declaration's clauses are read
//!   there rather than expanded into a parameter's: a recursive trait
//!   describes infinitely many paths.
//!
//! An assumption env is the clauses a scope may assume: its own, then,
//! through `parent`, those of the scopes around it. Each frame (an item's
//! generic parameter list, `GenericEnvIdx`) is read in one: its own when the
//! item writes clauses, else its parent's. Construction makes the frame's
//! written env, its clauses as written, which path selection reads. Once
//! every signature exists, `normalization` rewrites it by the equalities in
//! scope into its normalized env, which everything after construction reads.
//! A frame's requirements are the same clauses in the other role: proved at
//! each use, as written, never rewritten.
//!
//! A query's assumptions are named by an `AssumptionEnvIdx` called
//! `assumption_context`: the assumption env of the declaration whose bounds
//! (and enclosing declarations' bounds) apply. It is not the environment a
//! parameter was declared in: a query about an outer parameter can use extra
//! facts from an inner declaration's context, and outside a parameter's
//! declaration its bounds are not assumed. Where both meet
//! (`match_impl_target_and_bounds`) the `assumption_context` is the caller's
//! and `impl_env` the candidate impl's generic env: requirements are proved
//! in the caller's context.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::index::index_newtype;
use crate::vfs::FileId;

use super::decls::{DeclKind, Declarations, SignatureQuery, TraitIdx};
use super::members::{ConstantTarget, TypeProjectionTarget};
use super::signatures::{
	AssocTypeSignature, QueryInfo, Semantics, SemanticsBuilder,
	SignatureStatus, TraitSignature,
};
use super::types::{
	GenericEnvArena, GenericEnvIdx, GenericEnvOwner, Substitution, Type,
	TypeIndex, TypeInterner,
};

mod normalization;

pub(super) use normalization::{RewriteScope, RewrittenClauses};

index_newtype!(SourceClauseId);
index_newtype!(AssumptionEnvIdx);

/// One binding within a source clause. The index is stable because an
/// occurrence's completed binding slice is immutable after publication.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) struct BindingRef {
	pub(super) bound: SourceClauseId,
	pub(super) index: u32,
}

/// One source clause: a trait as written about a subject, names resolved,
/// with its bindings and its source location.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) struct SourceClause {
	pub(super) trait_index: TraitIdx,
	pub(super) span: SourceSpan,
	pub(super) bindings: Box<[SourceBinding]>,
}

/// One source binding, an entry of a source clause's binding block: `Assoc =
/// Type`, `Assoc: Traits` or `const NAME: Type`.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) struct SourceBinding {
	pub(super) name: Spanned<SymbolU32>,
	pub(super) kind: BindingRequirement,
}

/// What an entry states, about the member it names under the trait that
/// declares it: the source clause's own trait, or one of its supertraits.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub(super) enum BindingRequirement {
	/// `Assoc = Type`.
	Equals(TypeProjectionTarget, Spanned<TypeIndex>),
	/// `Assoc: Bounds`.
	Bound(TypeProjectionTarget, Box<[SourceClauseId]>),
	/// `const NAME: Type`: the constant's value is representable as the type.
	Representable(ConstantTarget, Spanned<TypeIndex>),
}

/// The clause `subject: trait_index`, stated by a bound.
/// `source` is the written bound that states it, which for a supertrait's
/// clause is the bound in the supertrait's declaration; `origin` is the bound
/// written on this declaration's subject whose expansion brought it in.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct TraitClause {
	pub(super) subject: TypeIndex,
	pub(super) trait_index: TraitIdx,
	pub(super) source: SourceClauseId,
	pub(super) origin: SourceClauseId,
}

/// The clause that `subject`'s value of the trait constant `constant` is `ty`
/// (`const LEN: u8` on `T: Array` is `<T as Array>::LEN` representable as
/// `u8`), stated by a bound. `source` is the written entry; `origin` as for
/// `TraitClause`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct RepresentableClause {
	pub(super) subject: TypeIndex,
	pub(super) target: ConstantTarget,
	pub(super) ty: TypeIndex,
	pub(super) source: BindingRef,
	pub(super) origin: SourceClauseId,
}

/// The clause `projection == value`, stated by a bound.
/// `source` is the written equality; `origin` as for `TraitClause`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct EqualityClause {
	pub(super) projection: TypeIndex,
	pub(super) value: TypeIndex,
	pub(super) source: BindingRef,
	pub(super) origin: SourceClauseId,
}

/// One fact a bound states. Every kind lives in the one `ClauseArena`, and a
/// subject's clauses are one run of them; a reader of one kind filters
/// (`ClauseArena::traits`, `ClauseArena::equalities`).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Clause {
	Trait(TraitClause),
	Equality(EqualityClause),
	Representable(RepresentableClause),
}

impl Clause {
	/// Whether `self` and `other` state the same fact, whatever writes them.
	pub(super) fn states_same(&self, other: &Clause) -> bool {
		match (self, other) {
			(Clause::Trait(a), Clause::Trait(b)) => {
				a.subject == b.subject && a.trait_index == b.trait_index
			}
			(Clause::Equality(a), Clause::Equality(b)) => {
				a.projection == b.projection && a.value == b.value
			}
			(Clause::Representable(a), Clause::Representable(b)) => {
				a.subject == b.subject && a.target == b.target && a.ty == b.ty
			}
			_ => false,
		}
	}
}

/// A run of clauses in the `ClauseArena`, owned by one subject.
#[derive(Clone, Copy)]
pub(super) struct ClauseRange {
	start: u32,
	len: u32,
}

impl ClauseRange {
	pub(super) const EMPTY: Self = Self { start: 0, len: 0 };

	pub(super) fn len(self) -> usize {
		self.len as usize
	}

	/// The first `mid` clauses, then the rest.
	pub(super) fn split_at(self, mid: usize) -> (Self, Self) {
		let mid = u32::try_from(mid).unwrap();
		debug_assert!(mid <= self.len);
		(
			Self { len: mid, ..self },
			Self {
				start: self.start + mid,
				len: self.len - mid,
			},
		)
	}
}

/// The clauses one subject's source clauses state: a parameter's (`T: Tr
/// where { A = X, A: B }`), or an associated type declaration's (`type A: B`,
/// about `<Self as Tr>::A`).
/// Each source clause becomes a flat run of clauses, its nested bindings as
/// clauses on projections and each trait's own clauses (its supertraits, and
/// theirs) substituted for `Self`. They are published in two stages: the
/// memberships before any value is resolved, so a sibling's value can name
/// members they supply, then the whole run once the values are.
#[derive(Clone, Copy)]
pub(super) enum PublishedClauses {
	/// The memberships only: a read may conclude neither a proof nor a
	/// failure from what the values will decide. Not an answer
	/// (`SolverError::Pending`); ask again once construction has advanced.
	Provisional(ClauseRange),
	/// Every clause. A proof reads memberships before equalities whatever
	/// their order in the run.
	Final(ClauseRange),
}

impl PublishedClauses {
	/// A subject whose bounds are not published yet.
	pub(super) const PENDING: Self = Self::Provisional(ClauseRange::EMPTY);
	/// A subject that assumes nothing.
	pub(super) const NONE: Self = Self::Final(ClauseRange::EMPTY);

	/// What is published: the memberships, or the whole run.
	pub(super) fn range(self) -> ClauseRange {
		match self {
			Self::Provisional(range) | Self::Final(range) => range,
		}
	}

	/// The whole run once it is published; `None` while it is provisional.
	pub(super) fn final_range(self) -> Option<ClauseRange> {
		match self {
			Self::Provisional(_) => None,
			Self::Final(range) => Some(range),
		}
	}

	/// The whole run, for tests that read finished clauses.
	#[cfg(test)]
	pub(super) fn resolved(self) -> ClauseRange {
		self.final_range().expect("the test's clauses are final")
	}

	/// Whether the clauses are final and state nothing.
	pub(super) fn is_empty(self) -> bool {
		self.final_range().is_some_and(|range| range.len() == 0)
	}
}

/// Every subject's clauses, append-only, addressed by `ClauseRange`.
#[derive(Default)]
pub(super) struct ClauseArena {
	clauses: Vec<Clause>,
}

impl ClauseArena {
	pub(super) fn get(&self, range: ClauseRange) -> &[Clause] {
		&self.clauses[range.start as usize..][..range.len as usize]
	}

	/// The memberships in `range`.
	pub(super) fn traits(
		&self,
		range: ClauseRange,
	) -> impl Iterator<Item = &TraitClause> + '_ {
		self.get(range).iter().filter_map(|clause| match clause {
			Clause::Trait(clause) => Some(clause),
			_ => None,
		})
	}

	/// The equalities in `range`.
	pub(super) fn equalities(
		&self,
		range: ClauseRange,
	) -> impl Iterator<Item = &EqualityClause> + '_ {
		self.get(range).iter().filter_map(|clause| match clause {
			Clause::Equality(clause) => Some(clause),
			_ => None,
		})
	}

	/// The representability clauses in `range`.
	pub(super) fn representable(
		&self,
		range: ClauseRange,
	) -> impl Iterator<Item = &RepresentableClause> + '_ {
		self.get(range).iter().filter_map(|clause| match clause {
			Clause::Representable(clause) => Some(clause),
			_ => None,
		})
	}

	pub(super) fn push(&mut self, clauses: &[Clause]) -> ClauseRange {
		let start = u32::try_from(self.clauses.len())
			.expect("clause arena exceeded u32 index capacity");
		self.clauses.extend_from_slice(clauses);
		ClauseRange {
			start,
			len: u32::try_from(clauses.len()).unwrap(),
		}
	}

	/// The provisional run of `traits`.
	pub(super) fn push_traits(
		&mut self,
		traits: &[TraitClause],
	) -> ClauseRange {
		let start = u32::try_from(self.clauses.len())
			.expect("clause arena exceeded u32 index capacity");
		self.clauses
			.extend(traits.iter().copied().map(Clause::Trait));
		ClauseRange {
			start,
			len: u32::try_from(traits.len()).unwrap(),
		}
	}

	/// The final run of `traits`, then the clauses the values decide.
	pub(super) fn push_final(
		&mut self,
		traits: &[TraitClause],
		values: &[Clause],
	) -> ClauseRange {
		let range = self.push_traits(traits);
		self.clauses.extend_from_slice(values);
		ClauseRange {
			len: range.len + u32::try_from(values.len()).unwrap(),
			..range
		}
	}
}

/// The clauses in force in a scope (rustc's `ParamEnv`): its own, about any
/// subject in scope, then its parent's.
#[derive(Clone, Copy)]
pub(super) struct AssumptionEnv {
	pub(super) parent: Option<AssumptionEnvIdx>,
	pub(super) clauses: PublishedClauses,
	/// A trait's own `Self: Trait`, which no clause states.
	pub(super) reflexive: Option<(TypeIndex, TraitIdx)>,
}

/// What a frame's item states (rustc's `predicates_of` and `param_env`,
/// keyed by the item's frame): `requirements` are its own clauses as
/// written, which a use proves; `written` is the env construction made for
/// it, its clauses as written, which path selection reads; `normalization`
/// leads to its normalized env, which everything after construction reads,
/// its clauses rewritten by the equalities in scope
/// (`Semantics::normalize_env`). A trait impl function's `Self` entry is in
/// `requirements` only, never in `written`.
#[derive(Clone, Copy)]
struct FrameClauses {
	written: AssumptionEnvIdx,
	normalization: EnvNormalization,
	requirements: PublishedClauses,
}

/// How far a frame's normalized env is (`Semantics::normalize_env`).
#[derive(Clone, Copy)]
pub(super) enum EnvNormalization {
	/// Not asked yet: only the written env exists.
	Unasked,
	/// Its clauses are being rewritten in `rewriting_env`, its clauses as
	/// written over its parent's normalized env; a read of the frame
	/// meanwhile (a clause normalizing back through it) sees that env, and
	/// the judgement it reaches again owns that loop.
	Rewriting { rewriting_env: AssumptionEnvIdx },
	/// The written env itself, the parent's normalized env, or a new flat
	/// one.
	Normalized(AssumptionEnvIdx),
}

/// Every scope's clauses. An item that writes no bound has no env of its
/// own and shares its parent's; `AssumptionEnvIdx::ROOT` assumes nothing.
/// An env's clauses are published once final and never change after.
pub(super) struct AssumptionEnvArena {
	envs: Vec<AssumptionEnv>,
	frames: Vec<FrameClauses>,
}

impl AssumptionEnvIdx {
	pub(super) const ROOT: AssumptionEnvIdx = AssumptionEnvIdx(0);
}

impl AssumptionEnvArena {
	pub(super) fn new() -> Self {
		Self {
			envs: vec![AssumptionEnv {
				parent: None,
				clauses: PublishedClauses::NONE,
				reflexive: None,
			}],
			frames: vec![FrameClauses {
				written: AssumptionEnvIdx::ROOT,
				normalization: EnvNormalization::Normalized(
					AssumptionEnvIdx::ROOT,
				),
				requirements: PublishedClauses::NONE,
			}],
		}
	}

	fn push(
		&mut self,
		parent: AssumptionEnvIdx,
		reflexive: Option<(TypeIndex, TraitIdx)>,
		clauses: PublishedClauses,
	) -> AssumptionEnvIdx {
		let env = AssumptionEnvIdx::new(
			u32::try_from(self.envs.len())
				.expect("param env arena exceeded u32 index capacity"),
		);
		self.envs.push(AssumptionEnv {
			parent: Some(parent),
			clauses,
			reflexive,
		});
		env
	}

	/// A new env inside `parent` for construction, its clauses published
	/// later (`publish_env`).
	pub(super) fn push_pending(
		&mut self,
		parent: AssumptionEnvIdx,
		reflexive: Option<(TypeIndex, TraitIdx)>,
	) -> AssumptionEnvIdx {
		self.push(parent, reflexive, PublishedClauses::PENDING)
	}

	/// A new env inside `parent` holding `clauses`, final from the start.
	pub(super) fn push_final(
		&mut self,
		parent: AssumptionEnvIdx,
		reflexive: Option<(TypeIndex, TraitIdx)>,
		clauses: ClauseRange,
	) -> AssumptionEnvIdx {
		self.push(parent, reflexive, PublishedClauses::Final(clauses))
	}

	/// Records that `frame`, just pushed, is read in `env`: its own, whose
	/// clauses it publishes next (`publish`), or one it shares, which leaves
	/// it requiring nothing.
	pub(super) fn bind_frame(
		&mut self,
		frame: GenericEnvIdx,
		env: AssumptionEnvIdx,
		own: bool,
	) {
		debug_assert_eq!(usize::from(frame), self.frames.len());
		self.frames.push(FrameClauses {
			written: env,
			normalization: EnvNormalization::Unasked,
			requirements: if own {
				PublishedClauses::PENDING
			} else {
				PublishedClauses::NONE
			},
		});
	}

	/// The env construction made for `frame`'s item, its clauses as
	/// written: its own, or the one it shares. Construction and path
	/// selection read it.
	pub(super) fn written(&self, frame: GenericEnvIdx) -> AssumptionEnvIdx {
		self.frames[usize::from(frame)].written
	}

	/// `frame`'s normalized env, for a reader that runs once every frame is
	/// normalized (bodies, lowering); any other asks
	/// `Semantics::normalize_env`.
	pub(super) fn normalized(&self, frame: GenericEnvIdx) -> AssumptionEnvIdx {
		match self.frames[usize::from(frame)].normalization {
			EnvNormalization::Normalized(env) => env,
			EnvNormalization::Unasked | EnvNormalization::Rewriting { .. } => {
				unreachable!(
					"every frame is normalized once declarations are checked"
				)
			}
		}
	}

	pub(super) fn normalization(
		&self,
		frame: GenericEnvIdx,
	) -> EnvNormalization {
		self.frames[usize::from(frame)].normalization
	}

	pub(super) fn set_normalization(
		&mut self,
		frame: GenericEnvIdx,
		normalization: EnvNormalization,
	) {
		self.frames[usize::from(frame)].normalization = normalization;
	}

	/// The number of frames, for normalizing each one's env.
	pub(super) fn frame_count(&self) -> usize {
		self.frames.len()
	}

	/// The clauses `frame`'s item states, as written: what a use of it
	/// proves. `PublishedClauses::NONE` for an item that writes no bound.
	pub(super) fn requirements(
		&self,
		frame: GenericEnvIdx,
	) -> PublishedClauses {
		self.frames[usize::from(frame)].requirements
	}

	/// Publishes `clauses` as what `frame`'s item states and what its own
	/// env assumes.
	pub(super) fn publish(
		&mut self,
		frame: GenericEnvIdx,
		clauses: PublishedClauses,
	) {
		self.set_requirements(frame, clauses);
		let env = self.written(frame);
		self.publish_env(env, clauses);
	}

	/// Publishes `clauses` as what `frame`'s item states, apart from what
	/// its env assumes.
	pub(super) fn set_requirements(
		&mut self,
		frame: GenericEnvIdx,
		clauses: PublishedClauses,
	) {
		let entry = &mut self.frames[usize::from(frame)];
		debug_assert!(
			matches!(entry.requirements, PublishedClauses::Provisional(_)),
			"only an item with clauses of its own publishes them"
		);
		entry.requirements = clauses;
	}

	/// Publishes `clauses` as what `env`, made by construction, assumes:
	/// its memberships, then the whole run.
	pub(super) fn publish_env(
		&mut self,
		env: AssumptionEnvIdx,
		clauses: PublishedClauses,
	) {
		let published = &mut self.envs[usize::from(env)].clauses;
		debug_assert!(
			matches!(published, PublishedClauses::Provisional(_)),
			"an env's final clauses never change"
		);
		*published = clauses;
	}

	pub(super) fn get(&self, env: AssumptionEnvIdx) -> &AssumptionEnv {
		&self.envs[usize::from(env)]
	}

	/// `env`'s clauses, for tests that move an env back to an earlier
	/// stage of construction.
	#[cfg(test)]
	pub(super) fn clauses_mut(
		&mut self,
		env: AssumptionEnvIdx,
	) -> &mut PublishedClauses {
		&mut self.envs[usize::from(env)].clauses
	}

	/// `env`, then each env around it.
	pub(super) fn chain(
		&self,
		env: AssumptionEnvIdx,
	) -> impl Iterator<Item = &AssumptionEnv> + '_ {
		std::iter::successors(Some(self.get(env)), |env| {
			env.parent.map(|parent| self.get(parent))
		})
	}
}

/// Every source clause, by `SourceClauseId`.
#[derive(Default)]
pub(super) struct SourceClauseArena {
	entries: Vec<SourceClauseEntry>,
}

/// Construction state belongs to the arena, not to a written requirement.
/// A reservation carries only the identity and location needed by membership
/// lookup; the AST retains the unresolved binding expressions.
enum SourceClauseEntry {
	Reserved {
		trait_index: TraitIdx,
		span: SourceSpan,
	},
	Resolved(SourceClause),
}

impl SourceClauseArena {
	fn next_id(&self) -> SourceClauseId {
		SourceClauseId::new(
			u32::try_from(self.entries.len())
				.expect("bound arena exceeded u32 index capacity"),
		)
	}

	pub(super) fn reserve(
		&mut self,
		trait_index: TraitIdx,
		span: SourceSpan,
	) -> SourceClauseId {
		let id = self.next_id();
		self.entries
			.push(SourceClauseEntry::Reserved { trait_index, span });
		id
	}

	#[cfg(test)]
	pub(super) fn ids(&self) -> impl Iterator<Item = SourceClauseId> + '_ {
		(0..self.entries.len()).map(|index| SourceClauseId::new(index as u32))
	}

	pub(super) fn span(&self, id: SourceClauseId) -> SourceSpan {
		match &self.entries[usize::from(id)] {
			SourceClauseEntry::Reserved { span, .. } => *span,
			SourceClauseEntry::Resolved(bound) => bound.span,
		}
	}

	pub(super) fn trait_index(&self, id: SourceClauseId) -> TraitIdx {
		match &self.entries[usize::from(id)] {
			SourceClauseEntry::Reserved { trait_index, .. } => *trait_index,
			SourceClauseEntry::Resolved(bound) => bound.trait_index,
		}
	}

	pub(super) fn fill(&mut self, id: SourceClauseId, bound: SourceClause) {
		let slot = &mut self.entries[usize::from(id)];
		let SourceClauseEntry::Reserved { trait_index, span } = slot else {
			panic!("source bounds are immutable after publication")
		};
		debug_assert_eq!(*trait_index, bound.trait_index);
		debug_assert!(*span == bound.span);
		*slot = SourceClauseEntry::Resolved(bound);
	}

	pub(super) fn get(&self, id: SourceClauseId) -> &SourceClause {
		match &self.entries[usize::from(id)] {
			SourceClauseEntry::Resolved(bound) => bound,
			SourceClauseEntry::Reserved { .. } => {
				panic!("source bound has not finished resolving")
			}
		}
	}

	/// The bound at `id` if it finished resolving: a bound a signature
	/// cycle cut short stays reserved.
	pub(super) fn resolved(&self, id: SourceClauseId) -> Option<&SourceClause> {
		match &self.entries[usize::from(id)] {
			SourceClauseEntry::Resolved(bound) => Some(bound),
			SourceClauseEntry::Reserved { .. } => None,
		}
	}

	pub(super) fn binding(&self, reference: BindingRef) -> &SourceBinding {
		&self.get(reference.bound).bindings[reference.index as usize]
	}
}

impl Semantics {
	/// The declaration whose signature holds `trait_index`'s: its typeset's
	/// for a trait a typeset generates.
	pub(super) fn trait_query(&self, trait_index: TraitIdx) -> SignatureQuery {
		match self.decls.traits[usize::from(trait_index)].typeset {
			Some(typeset_index) => SignatureQuery::Typeset(typeset_index),
			None => SignatureQuery::Trait(trait_index),
		}
	}

	/// The clauses the values in the written bounds `ids` decide about
	/// `subject` (named `name`), equalities then representability, each trait's
	/// own included, appended to `out`, which may hold other subjects'. Two
	/// values an outer constructor tells apart are a conflict, reported here.
	pub(super) fn collect_value_clauses(
		&mut self,
		strings: &StringInterner,
		out: &mut Vec<Clause>,
		subject: TypeIndex,
		ids: &[SourceClauseId],
		name: SymbolU32,
	) {
		let mut builder = ValueClauseBuilder {
			source_clauses: &self.source_clauses,
			clauses: &self.clauses,
			assumption_envs: &self.assumption_envs,
			traits: &self.traits,
			generic_envs: &self.generic_envs,
			types: &mut self.types,
			equalities: Vec::new(),
			representable: Vec::new(),
			conflicts: Vec::new(),
		};
		for &id in ids {
			builder.collect(subject, id, id);
		}
		let ValueClauseBuilder {
			equalities,
			representable,
			conflicts,
			..
		} = builder;
		for conflict in conflicts {
			self.diagnostics.push(report_conflicting_assoc_type_binding(
				strings,
				&self.decls,
				&self.source_clauses,
				name,
				conflict,
			));
		}
		out.extend(equalities.into_iter().map(Clause::Equality));
		out.extend(representable.into_iter().map(Clause::Representable));
	}
}

struct AssocBindingConflict {
	first: BindingRef,
	second: BindingRef,
	/// The written bound whose expansion brought the two values together.
	merge_point: SourceClauseId,
}

/// The value pass over written bounds: the clauses resolved values decide,
/// equalities and representability. It walks the same bounds as the membership
/// pass, which already demanded every trait they name, so it forces nothing: it
/// reads finished tables and borrows what it walks. A trait still being built
/// has no final `Self` clauses yet, and lends none.
struct ValueClauseBuilder<'a> {
	source_clauses: &'a SourceClauseArena,
	clauses: &'a ClauseArena,
	assumption_envs: &'a AssumptionEnvArena,
	traits: &'a [TraitSignature],
	generic_envs: &'a GenericEnvArena,
	types: &'a mut TypeInterner,
	equalities: Vec<EqualityClause>,
	representable: Vec<RepresentableClause>,
	conflicts: Vec<AssocBindingConflict>,
}

impl ValueClauseBuilder<'_> {
	/// The equalities and representability clauses the written bound `id`
	/// states about `subject`, its nested bounds' included, then its trait's
	/// own, as brought in by `origin`.
	fn collect(
		&mut self,
		subject: TypeIndex,
		id: SourceClauseId,
		origin: SourceClauseId,
	) {
		let bound = self.source_clauses.get(id);
		for (index, binding) in bound.bindings.iter().enumerate() {
			let source = BindingRef {
				bound: id,
				index: u32::try_from(index)
					.expect("bound binding count exceeded u32 capacity"),
			};
			match &binding.kind {
				BindingRequirement::Equals(target, value) => {
					let written_since = self.equalities.len();
					let projection = target.project(self.types, subject);
					push_equality_clause(
						self.types,
						&mut self.equalities,
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
				BindingRequirement::Bound(target, nested) => {
					let projection = target.project(self.types, subject);
					for &nested in nested {
						self.collect(projection, nested, origin);
					}
				}
				BindingRequirement::Representable(target, ty) => {
					self.representable.push(RepresentableClause {
						subject,
						target: *target,
						ty: ty.inner,
						source,
						origin,
					});
				}
			}
		}
		let env = self.traits[usize::from(bound.trait_index)].env;
		let Some(range) = self.assumption_envs.requirements(env).final_range()
		else {
			return;
		};
		let inherited_since = self.equalities.len();
		let substitution = Substitution {
			envs: self.generic_envs,
			env,
			args: &[subject],
		};
		for clause in self.clauses.get(range) {
			match *clause {
				Clause::Trait(_) => {}
				Clause::Equality(clause) => {
					let projection =
						self.types.substitute(clause.projection, substitution);
					let value =
						self.types.substitute(clause.value, substitution);
					push_equality_clause(
						self.types,
						&mut self.equalities,
						EqualityClause {
							projection,
							value,
							origin,
							..clause
						},
						inherited_since,
						&mut self.conflicts,
					);
				}
				Clause::Representable(clause) => {
					self.representable.push(RepresentableClause {
						subject: self
							.types
							.substitute(clause.subject, substitution),
						ty: self.types.substitute(clause.ty, substitution),
						origin,
						..clause
					});
				}
			}
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
	pub(super) generic_envs: &'a GenericEnvArena,
	pub(super) assumption_envs: &'a AssumptionEnvArena,
	pub(super) traits: &'a [TraitSignature],
	pub(super) assoc_types: &'a [Option<AssocTypeSignature>],
	pub(super) clauses: &'a ClauseArena,
}

impl<'a> ClauseTables<'a> {
	pub(super) fn new(
		generic_envs: &'a GenericEnvArena,
		assumption_envs: &'a AssumptionEnvArena,
		traits: &'a [TraitSignature],
		assoc_types: &'a [Option<AssocTypeSignature>],
		clauses: &'a ClauseArena,
	) -> Self {
		Self {
			generic_envs,
			assumption_envs,
			traits,
			assoc_types,
			clauses,
		}
	}

	/// The memberships assumed in `assumption_context` and the frames around
	/// it, as `(subject, trait)`: every scope's trait clauses, and a
	/// trait's own `Self: Trait`, which no clause states.
	pub(super) fn assumed_traits(
		&self,
		assumption_context: AssumptionEnvIdx,
	) -> impl Iterator<Item = (TypeIndex, TraitIdx)> + 'a {
		let Self {
			assumption_envs,
			clauses,
			..
		} = *self;
		assumption_envs
			.chain(assumption_context)
			.flat_map(move |env| {
				env.reflexive.into_iter().chain(
					clauses
						.traits(env.clauses.range())
						.map(|clause| (clause.subject, clause.trait_index)),
				)
			})
	}

	/// The subjects assumed in `assumption_context` to implement `trait_index`.
	pub(super) fn assumed_subjects(
		&self,
		assumption_context: AssumptionEnvIdx,
		trait_index: TraitIdx,
	) -> impl Iterator<Item = TypeIndex> + 'a {
		self.assumed_traits(assumption_context)
			.filter(move |&(_, assumed)| assumed == trait_index)
			.map(|(subject, _)| subject)
	}

	/// Whether every scope has its equalities: a membership read
	/// before that can still be one an equality's value has to confirm.
	pub(super) fn assumptions_readiness(
		&self,
		assumption_context: AssumptionEnvIdx,
	) -> Readiness {
		self.assumption_envs
			.chain(assumption_context)
			.fold(Readiness::Ready, |readiness, env| {
				readiness.and(Readiness::from(env.clauses))
			})
	}

	/// The subjects whose clauses can describe `receiver` in
	/// `assumption_context`: each associated declaration on its projection
	/// path, outermost first, then, for a parameter at its root, each
	/// assumption env in scope. Missing or provisional declarations make the
	/// path `Pending`; reading never forces them.
	pub(super) fn declarations_of<'t>(
		&self,
		types: &'t TypeInterner,
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		recursion_budget: usize,
	) -> DeclarationSources<'a, 't> {
		let reflexive_trait = match *types.resolve(receiver) {
			Type::TypeParam { env, .. } => match self.generic_envs.owner(env) {
				GenericEnvOwner::Trait(index) => Some(index),
				_ => None,
			},
			_ => None,
		};
		let mut sources = DeclarationSources {
			tables: *self,
			types,
			receiver,
			current: Some(receiver),
			context: assumption_context,
			scope: None,
			remaining: recursion_budget,
			readiness: Readiness::Ready,
			reflexive_trait,
		};
		// Computed up front, so stopping early cannot hide `Pending`.
		let mut readiness = Readiness::Ready;
		let mut walk = DeclarationSources { ..sources };
		for source in walk.by_ref() {
			readiness = readiness.and(Readiness::from(source.clauses));
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
		assumption_context: AssumptionEnvIdx,
		receiver: TypeIndex,
		recursion_budget: usize,
	) -> DeclaredTraits<'a, 't> {
		let sources = self.declarations_of(
			types,
			assumption_context,
			receiver,
			recursion_budget,
		);
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
	pub(super) clauses: PublishedClauses,
	/// For an associated declaration, its trait's `Self` read as the
	/// projection's base. `None` for a scope's assumption env, whose clauses
	/// name the receiver in its own terms.
	pub(super) context: Option<SelfSubstitution>,
}

impl DeclarationSource {
	/// Whether `subject`, a subject of this source's clauses, is `receiver`:
	/// for a declaration, the same projections over its `Self` as over the
	/// base it is read with. Compared without interning.
	pub(super) fn names(
		self,
		types: &TypeInterner,
		generic_envs: &GenericEnvArena,
		mut subject: TypeIndex,
		mut receiver: TypeIndex,
	) -> bool {
		let Some(context) = self.context else {
			return subject == receiver;
		};
		let self_type = generic_envs.param_types(context.env)[0];
		loop {
			if subject == self_type {
				return receiver == context.receiver;
			}
			match (types.resolve(subject), types.resolve(receiver)) {
				(
					Type::TypeProjection {
						base: subject_base,
						trait_index: subject_trait,
						assoc_type_index: subject_assoc,
					},
					Type::TypeProjection {
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
	/// Where the receiver is read: whose assumption envs describe a
	/// parameter at its root.
	context: AssumptionEnvIdx,
	/// The next assumption env to read, once the walk reached the root.
	scope: Option<AssumptionEnvIdx>,
	remaining: usize,
	pub(super) readiness: Readiness,
	/// `Self: Trait` for a trait's own `Self`, which no clause states.
	pub(super) reflexive_trait: Option<TraitIdx>,
}

impl Iterator for DeclarationSources<'_, '_> {
	type Item = DeclarationSource;

	fn next(&mut self) -> Option<DeclarationSource> {
		// The root env assumes nothing.
		if let Some(env) =
			self.scope.filter(|&env| env != AssumptionEnvIdx::ROOT)
		{
			let env = self.tables.assumption_envs.get(env);
			self.scope = env.parent;
			return Some(DeclarationSource {
				clauses: env.clauses,
				context: None,
			});
		}
		let current = self.current.take()?;
		if self.remaining == 0 {
			return None;
		}
		match *self.types.resolve(current) {
			Type::TypeParam { .. } => {
				self.scope = Some(self.context);
				self.next()
			}
			Type::TypeProjection {
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
					.map_or(PublishedClauses::PENDING, |signature| {
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
	current: Option<(DeclarationSource, std::slice::Iter<'a, Clause>)>,
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
				if let Some(clause) = clauses.find_map(|clause| match clause {
					Clause::Trait(clause)
						if source.names(
							types,
							tables.generic_envs,
							clause.subject,
							receiver,
						) =>
					{
						Some(clause)
					}
					_ => None,
				}) {
					return Some(clause.trait_index);
				}
			}
			let source = self.sources.next()?;
			let clauses =
				self.sources.tables.clauses.get(source.clauses.range());
			self.current = Some((source, clauses.iter()));
		}
	}
}

/// How an associated declaration's clauses are read on a projection path:
/// its trait's `Self`, the frame `env` declares, is the projection's base.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct SelfSubstitution {
	pub(super) env: GenericEnvIdx,
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

impl From<PublishedClauses> for Readiness {
	fn from(clauses: PublishedClauses) -> Self {
		match clauses {
			PublishedClauses::Provisional(_) => Readiness::Pending,
			PublishedClauses::Final(_) => Readiness::Ready,
		}
	}
}

impl Semantics {
	pub(super) fn clause_tables(&self) -> ClauseTables<'_> {
		ClauseTables::new(
			&self.generic_envs,
			&self.assumption_envs,
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
			| Type::ConstInt
			| Type::ConstFloat
			| Type::ConstChar
			| Type::TypeParam { .. }
			| Type::TypeProjection { .. },
			_,
		)
		| (
			_,
			Type::Error
			| Type::Infer
			| Type::ConstInt
			| Type::ConstFloat
			| Type::ConstChar
			| Type::TypeParam { .. }
			| Type::TypeProjection { .. },
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
	kind: DeclKind,
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
	decls: &Declarations,
	arena: &SourceClauseArena,
	subject: SymbolU32,
	conflict: AssocBindingConflict,
) -> Diagnostic<FileId> {
	let first = arena.binding(conflict.first);
	let second = arena.binding(conflict.second);
	let BindingRequirement::Equals(target, first_value) = &first.kind else {
		unreachable!("conflict points to a source equality")
	};
	let BindingRequirement::Equals(_, second_value) = &second.kind else {
		unreachable!("conflict points to a source equality")
	};
	let subject_str = strings.resolve(subject).unwrap();
	let trait_name = decls.name(target.trait_index).inner;
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

/// A binding names no member of the kind its entry needs: `noun` is
/// "an associated type" for `Name = ..`/`Name: ..`, "a constant" for `const
/// NAME: ..`.
pub(super) fn report_not_a_binding_member(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	trait_name: SymbolU32,
	noun: &str,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	let trait_str = strings.resolve(trait_name).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitMember.code())
		.with_message(format!(
			"`{name_str}` is not {noun} of trait `{trait_str}`"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}

impl<'ast> SemanticsBuilder<'ast> {
	/// The frame whose `Self` clauses are the trait `bound` names, once its
	/// signature is available. While it is being built the bound closes a
	/// cycle, reported here at `bound`, and expands to nothing.
	fn trait_clause_env(
		&mut self,
		sema: &mut Semantics,
		bound: SourceClauseId,
	) -> Option<GenericEnvIdx> {
		let trait_index = sema.source_clauses.trait_index(bound);
		self.trait_env(sema, trait_index, sema.source_clauses.span(bound))
	}

	/// The frame of `trait_index`, once its signature is available. While it
	/// is being built, `reference` closes a cycle, reported here once.
	pub(super) fn trait_env(
		&mut self,
		sema: &mut Semantics,
		trait_index: TraitIdx,
		reference: SourceSpan,
	) -> Option<GenericEnvIdx> {
		let query = sema.trait_query(trait_index);
		match self.ensure_signature(
			sema,
			QueryInfo {
				query,
				requested_at: Some(reference),
			},
		) {
			SignatureStatus::Available(_) => {
				Some(sema.traits[usize::from(trait_index)].env)
			}
			SignatureStatus::Cycle => {
				let diagnostic = self
					.report_cyclic_implied_trait_bounds(sema, query, reference);
				sema.diagnostics.push(diagnostic);
				None
			}
			SignatureStatus::CycleReported => None,
		}
	}

	/// Appends the trait clauses of the trait `bound` names, with `Self`
	/// replaced by `subject`, as brought in by `origin`.
	pub(super) fn inherit_trait_clauses(
		&mut self,
		sema: &mut Semantics,
		out: &mut Vec<TraitClause>,
		subject: TypeIndex,
		bound: SourceClauseId,
		origin: SourceClauseId,
	) {
		let Some(env) = self.trait_clause_env(sema, bound) else {
			return;
		};
		let range = sema.assumption_envs.requirements(env).range();
		for clause in sema.clauses.traits(range) {
			let subject = sema.types.substitute(
				clause.subject,
				Substitution {
					envs: &sema.generic_envs,
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

	/// Demand the associated declarations along `receiver`'s projection path,
	/// whose clauses can describe it (`ClauseTables::declarations_of`). A
	/// declaration whose equalities are not resolved yet still supplies its
	/// memberships, but not an equality.
	pub(super) fn prepare_declarations_of(
		&mut self,
		sema: &mut Semantics,
		mut receiver: TypeIndex,
		reference: SourceSpan,
	) -> Result<(), ()> {
		while let Type::TypeProjection {
			base,
			assoc_type_index,
			..
		} = *sema.types.resolve(receiver)
		{
			if sema.assoc_types[usize::from(assoc_type_index)].is_none() {
				self.ensure_assoc_type_bounds(
					sema,
					assoc_type_index,
					reference,
				)?;
			}
			receiver = base;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tir::decls::EnumIdx;

	fn clause(index: u32, value: TypeIndex) -> EqualityClause {
		EqualityClause {
			projection: TypeIndex::UNIT,
			value,
			source: BindingRef {
				bound: SourceClauseId::new(0),
				index,
			},
			origin: SourceClauseId::new(0),
		}
	}

	/// Pushes each value as a clause on one projection, returning the values
	/// kept and the conflicts found.
	fn push(values: &[TypeIndex]) -> (Vec<EqualityClause>, usize) {
		let types = TypeInterner::for_tests();
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
		let types = TypeInterner::for_tests();
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
		let mut types = TypeInterner::for_tests();
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
