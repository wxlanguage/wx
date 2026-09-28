//! Phase 2, first slice — generic-parameter declarations and their trait
//! bounds: `<T: Add>` in `fn f<T: Add>(...)`, `struct S<T>`, `impl<T> ...`.
//!
//! Type parameters live here, not in `defs.rs`, on purpose: unlike a
//! struct/function/trait name, a type parameter is never reachable by a
//! path written anywhere outside its own declaration — nobody writes
//! `foo::T`. It's scoped to the item that declares it, exactly like a
//! function parameter name, which was never a `defs.rs` citizen either.
//!
//! A param's *identity* (name, resolved `TypeIndex`, and — once something
//! needs it — where it's been referenced) and its *bounds* are split the
//! same way the rest of this rewrite already splits identity from resolved
//! semantics: identity lives in `TypeEnvArena` (see that type's doc
//! comment), addressed by the `TypeEnvId` each signature struct carries;
//! bounds are a resolved-signature fact, index-aligned with that same
//! frame, and live on the signature struct itself. This mirrors
//! `defs.rs`/`signatures.rs` joined by a stable index, not the "two
//! redundant copies of one fact" shape this file used to warn against —
//! identity and bounds aren't copies of each other, they're different
//! facts about the same param.
//!
//! `defs.rs`'s own two previous exceptions — `TraitDef::self_param` and
//! `TraitImplDef`/`InherentImplDef::type_params` — were removed in favor of
//! this module for the same reason.

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{self, DefId, Keyword, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::defs::TypeAliasIdx;
use crate::tir::types::TypeEnvOwner;
use crate::vfs::FileId;

use super::bounds::{
	BindingRequirement, BoundArena, BoundFacts, BoundId, ImpliedAssocBinding,
	ImpliedBindingKind, ImpliedTraitBound, SourceAssocBinding,
	SourceTraitBound, report_duplicate_assoc_type_binding,
	report_not_a_trait_bound, report_not_an_associated_type,
};
use super::defs::{
	AssocTypeIdx, AstEntry, AstNodeRef, BindingKey, BindingNamespace, ConstIdx,
	DefKind, DefinitionRegistry, EnumIdx, FunctionIdx, GlobalIdx,
	InherentImplIdx, MemberKind, MemoryIdx, NamespaceIdx, StructIdx, TraitIdx,
	TraitImplIdx, TypesetIdx,
};
use super::impls::{ImplDispatch, ImplTarget};
use super::members::AssocTypeProvider;
use super::normalize::NormalizationState;
use super::paths::PathResolver;
use super::types::{
	Type, TypeEnvArena, TypeEnvIdx, TypeIndex, TypeInterner, TypeParam,
};

/// One generic parameter's bounds — everything about a `Type::TypeParam`
/// beyond its own identity (which lives in `TypeEnvArena`, addressed by the
/// same `(env, param_index)` pair; see that module's own doc comment for
/// why the two are split apart rather than living on `TypeParam` directly).
/// Stored in `SignatureBuilder::param_bounds`, index-aligned with
/// `TypeEnvArena`'s own frames — one `Box<[ParamBounds]>` per frame,
/// reserved for it by `reserve_param_bounds` right after, so the two arrays
/// can never drift out of length.
pub struct ParamBounds {
	/// One-hop, as written (`T: A + B`) — used for display and as the seed
	/// `compute_implied_bounds` merges from. Left empty for a frame whose one
	/// entry is never itself abstract (an impl's own `Self`, bound
	/// directly to a concrete type) — nothing ever queries bounds for one
	/// of those, so there's nothing to fill in.
	pub declared_bounds: Box<[BoundId]>,
	/// Includes inherited and nested facts. Memberships are published before
	/// equality RHS resolution — see `BoundFacts` — and the completed merge
	/// diagnoses only conflicts already established by incompatible outer
	/// constructors.
	pub(super) facts: BoundFacts,
}

impl ParamBounds {
	fn empty() -> Self {
		Self {
			declared_bounds: Box::new([]),
			facts: BoundFacts::empty(),
		}
	}
}

/// One accepted bound occurrence, decided once by
/// `SignatureBuilder::collect_bound_occurrences` and shared by both the
/// provisional-membership builder (`provisional_from_occurrences`) and the
/// source-bound resolver (`SignatureBuilder::resolve_source_bounds_from`),
/// so the two cannot disagree about which occurrences exist.
struct BoundOccurrence<'expr> {
	id: BoundId,
	trait_index: TraitIdx,
	span: SourceSpan,
	bindings: Vec<BindingOccurrence<'expr>>,
}

struct BindingOccurrence<'expr> {
	assoc_type_index: AssocTypeIdx,
	name: Spanned<SymbolU32>,
	kind: BindingOccurrenceKind<'expr>,
}

enum BindingOccurrenceKind<'expr> {
	/// RHS not resolved yet — `resolve_source_bounds_from` resolves it once
	/// every sibling param has provisional memberships published.
	Equals(&'expr Spanned<ast::TypeExpression>),
	Bound(Vec<BoundOccurrence<'expr>>),
}

/// Builds direct memberships from a decided occurrence tree, with
/// `ImpliedBindingKind::Bound` standing in for every equality binding until
/// `merge_implied_memberships` resolves its RHS. Whether any equality
/// binding exists at all — the fact that decides if that merge pass is
/// needed — is answered by `collect_bound_occurrences` itself, which
/// already visits every binding once; it isn't rediscovered here.
fn provisional_from_occurrences(
	occurrences: &[BoundOccurrence<'_>],
) -> Vec<ImpliedTraitBound> {
	occurrences
		.iter()
		.map(|occurrence| {
			let bindings = occurrence
				.bindings
				.iter()
				.map(|binding| {
					let required_bounds = match &binding.kind {
						BindingOccurrenceKind::Equals(_) => Vec::new(),
						BindingOccurrenceKind::Bound(nested) => {
							provisional_from_occurrences(nested)
						}
					};
					ImpliedAssocBinding {
						assoc_type_index: binding.assoc_type_index,
						kind: ImpliedBindingKind::Bound,
						required_bounds,
					}
				})
				.collect();
			ImpliedTraitBound {
				trait_index: occurrence.trait_index,
				source: occurrence.id,
				bindings,
			}
		})
		.collect()
}

pub struct TypeAliasSignature {
	type_params: TypeEnvIdx,
	target: TypeIndex,
}

/// A trait's own resolved header: `trait X: Y + Z { ... }`. Member
/// signatures (`TraitFunction`/`TraitConst`/`TraitAssocType`) are separate
/// queries, same as an impl's; identity already lives in `defs.rs`.
pub struct TraitSignature {
	pub env: TypeEnvIdx,
}

/// A resolved `fn name<...>(params) -> Result { ... }` — covers both
/// `Item::Function` and `Item::FunctionDeclaration` (an `import` block's
/// bodiless signature), which share one `FunctionSignature` shape in the
/// AST and so share one resolved shape here too. No name/identity fields:
/// unlike `TypeAliasSignature`, nothing needs to display a function's name
/// from just this struct — the one place that will (diagnostics, once
/// bodies exist) already has the `DefId` to look the name up from `defs`.
pub struct FunctionSignature {
	/// See `TypeAliasSignature::type_params` — bounds live in
	/// `SignatureBuilder::param_bounds`, not here.
	pub(super) type_params: TypeEnvIdx,
	param_types: Box<[TypeIndex]>,
	/// `TypeIndex::UNIT` when the source omits `-> Result`.
	return_type: TypeIndex,
}

/// Field *types* only — names/dedup/lookup already settled in
/// `defs::StructDef`, index-aligned with whichever `StructFields` variant
/// that struct has, so record vs. tuple doesn't need re-deriving here.
pub struct StructSignature {
	/// See `TypeAliasSignature::type_params`.
	pub(super) type_params: TypeEnvIdx,
	field_types: Box<[TypeIndex]>,
}

/// Just the repr type for now — variant identity/dedup already settled in
/// `defs::EnumDef`'s namespace; resolving each variant's value (explicit or
/// auto-incremented) needs constant-expression evaluation, which doesn't
/// exist yet, so it's deferred to the body phase rather than blocking this.
/// `TypeIndex::ERROR` if `repr` was missing or resolved to a non-integer
/// type — either way already diagnosed once, here, when that happened.
pub struct EnumSignature {
	repr: TypeIndex,
}

/// Resolved member types only — identity (the backing trait, the
/// pre-allocated synthetic impl slots) already lives in `defs::TypeSetDef`.
/// Index-aligned with the written member list; an invalid member (not a
/// legal `impl` target) still gets a slot here, carrying `TypeIndex::ERROR`,
/// same reasoning as a duplicate struct field still getting its own slot.
pub struct TypeSetSignature {
	members: Box<[Spanned<TypeIndex>]>,
}

/// A `const`'s resolved type — covers both a free top-level `const` and a
/// trait/impl associated const, which share one shape the same reason
/// `FunctionSignature` covers both a free function and a method. No default
/// value here yet: evaluating one needs constant-expression evaluation,
/// which doesn't exist in this architecture yet (see `EnumSignature::repr`,
/// deferred for the identical reason).
pub struct ConstantSignature {
	ty: TypeIndex,
}

/// One `AssocTypeIdx`'s resolved signature. `declared_bounds`/
/// `implied_bounds` (`type Name: Bound1 + Bound2;`, resolved against the
/// trait's own `self_scope` — forced first, same as `TraitFunction`/
/// `TraitConst` — so a bound may reference `Self`, e.g. `type Size: Memory
/// where { X = Self::Size }`) only ever come from a trait's own declaration.
/// `value` is the concrete type this slot is set to: `None` for a trait
/// declaration with no default (there's no syntax for one yet, but nothing
/// here assumes there won't be), `Some` for an `impl`'s own `type Name =
/// Ty;` (a separate query, `TraitImplAssocType`, and a separate `AssocTypeIdx`
/// from the trait's declaration even for "the same" name — it never sets
/// `declared_bounds`/`implied_bounds`, since an impl provides a value, it
/// doesn't declare a requirement).
pub struct AssocTypeSignature {
	pub(super) declared_bounds: Box<[BoundId]>,
	/// Effective facts from the declaration — see `BoundFacts`. A
	/// provisional membership table can be read while equality RHS types
	/// are still being resolved.
	pub(super) facts: BoundFacts,
	pub(super) value: Option<TypeIndex>,
}

/// The resolved header of `impl<...> Target { ... }`. Member signatures are
/// separate queries; names and identities already live in `defs.rs`.
pub struct InherentImplSignature {
	/// See `TypeAliasSignature::type_params`.
	pub type_params: TypeEnvIdx,
	pub target: Spanned<TypeIndex>,
	/// The frame binding `Self` to `target`, parented at `type_params` and
	/// pushed once, right here, rather than separately by each member —
	/// every member's own resolution parents *its* frame at this one
	/// instead of pushing a fresh `Self` binding of its own, so references
	/// to `Self` from anywhere in this impl accumulate in one place
	/// (`TypeEnvArena`'s own per-entry `accesses`) instead of scattering
	/// across a different frame per member. Moved here from
	/// `defs::InherentImplDef::self_accesses` (Phase 1 output, immutable
	/// once Phase 2 starts) for the same reason `type_params` isn't a
	/// `Box<[GenericParam]>` here either — see the module doc comment.
	pub self_scope: TypeEnvIdx,
}

/// The resolved header of `impl<...> Trait for Target { ... }`.
pub struct TraitImplSignature {
	/// See `TypeAliasSignature::type_params`.
	pub type_params: TypeEnvIdx,
	pub target: Spanned<TypeIndex>,
	/// See `InherentImplSignature::self_scope`.
	pub self_scope: TypeEnvIdx,
}

#[derive(Clone, Copy)]
enum InferSignatureKind {
	Function,
	ReturnType,
	Struct,
	TypeAlias,
	EnumRepr,
	AssocTypeBinding,
	Const,
}

impl InferSignatureKind {
	fn noun(self) -> &'static str {
		match self {
			Self::Function => "functions",
			Self::ReturnType => "return types",
			Self::Struct => "structs",
			Self::TypeAlias => "type aliases",
			Self::EnumRepr => "enum reprs",
			Self::AssocTypeBinding => "associated type bindings",
			Self::Const => "consts",
		}
	}
}

#[derive(Clone, Copy)]
enum InferPolicy {
	Reject(InferSignatureKind),
	/// Used by type-resolution contexts that can infer a written `_`.
	#[allow(dead_code)] // No such caller in the signature registry yet.
	Allow,
}

pub struct SignatureRegistry {
	pub type_aliases: Vec<TypeAliasSignature>,
	/// Indexed by the same `TraitIndex` `defs.traits` already uses — traits
	/// need no index space of their own here, unlike `type_aliases`, since
	/// Phase 1 already has one.
	pub traits: Vec<TraitSignature>,
	/// Indexed by the same `StructIndex` `defs.structs` already uses — see
	/// `traits`.
	pub structs: Vec<StructSignature>,
	/// Indexed by the same `EnumIndex` `defs.enums` already uses — see
	/// `traits`.
	pub enums: Vec<EnumSignature>,
	/// Indexed by the same `TypeSetIndex` `defs.typesets` already uses —
	/// see `traits`.
	pub typesets: Vec<TypeSetSignature>,
	/// Indexed by `defs::AssocTypeIdx`. Only resolved trait declarations
	/// have bounds signatures here; impl definitions have distinct identities
	/// and will need target-type resolution, which is not implemented yet.
	pub assoc_types: Vec<Option<AssocTypeSignature>>,
	pub functions: Vec<FunctionSignature>,
	/// Index-aligned with `defs.constants`. Only trait constant signatures
	/// are resolved so far; free and impl constants are not implemented yet.
	pub constants: Vec<ConstantSignature>,
	/// Index-aligned with the corresponding `defs.rs` impl arenas. A slot is
	/// `None` until its header query completes, even if that query later
	/// recovers with `TypeIndex::ERROR` or an unresolved trait path.
	pub inherent_impls: Vec<Option<InherentImplSignature>>,
	pub trait_impls: Vec<Option<TraitImplSignature>>,
	pub(super) impl_dispatch: ImplDispatch,
	pub types: TypeInterner,
	pub(super) bounds: BoundArena,
	/// See `SignatureBuilder::param_bounds`.
	pub(super) param_bounds: Vec<Box<[ParamBounds]>>,
	/// Derived once, here, from `SignatureBuilder::query_state` — every
	/// entry is `Resolved` by construction (`build`'s own sweep below
	/// forces every `ast_nodes` entry, and `ensure_signature` has no early
	/// `return` that could skip installing one), so this is a straight
	/// `DefId -> SignatureLocation` projection, not a filter. No production
	/// code needs a `DefId`-keyed reverse lookup once building is over
	/// (every real consumer already holds the index it wants by then) —
	/// this exists for tests, which only ever have a path they've resolved
	/// to a `DefId`, never the index.
	pub item_lookup: HashMap<DefId, SignatureLocation>,
}

impl SignatureRegistry {
	fn build<'ctx>(
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		defs: &DefinitionRegistry,
		ast_nodes: &[AstEntry<'ctx>],
	) -> Self {
		let impl_dispatch =
			ImplDispatch::build(diagnostics, strings, defs, ast_nodes);
		let mut builder = SignatureBuilder::new(
			diagnostics,
			strings,
			defs,
			ast_nodes,
			impl_dispatch,
		);
		// Dispatch is complete before any signature query can resolve a
		// concrete member. Impl parameter bounds are resolved here along
		// with all other signatures, without an earlier header query.
		for entry in ast_nodes {
			let _ = builder.ensure_signature(QueryInfo {
				def_id: entry.def_id,
				requested_at: None,
			});
		}

		Self {
			type_aliases: builder.type_aliases,
			traits: builder.traits,
			structs: builder.structs,
			enums: builder.enums,
			typesets: builder.typesets,
			assoc_types: builder.assoc_types,
			functions: builder.functions,
			constants: builder.constants,
			inherent_impls: builder.inherent_impls,
			trait_impls: builder.trait_impls,
			impl_dispatch: builder.impl_dispatch,
			types: builder.types,
			bounds: builder.bounds,
			param_bounds: builder.param_bounds,
			item_lookup: builder
				.query_state
				.into_iter()
				.map(|(def_id, entry)| {
					let QueryState::Resolved(location) = entry.state else {
						unreachable!(
							"build()'s own sweep visits every ast_nodes entry, so every query_state entry is Resolved by the time this runs"
						)
					};
					(def_id, location)
				})
				.collect(),
		}
	}
}

/// Where a `DefId`'s data actually lives — one arena per item kind
/// `ensure_signature` can be asked about. `Trait`/`TraitImpl`/`InherentImpl`/
/// `Struct` and the other item kinds use indices allocated in `defs.rs`
/// and keep resolved data in index-aligned slots here.
#[derive(Clone, Copy)]
pub enum SignatureLocation {
	Trait(TraitIdx),
	TraitImpl(TraitImplIdx),
	InherentImpl(InherentImplIdx),
	Struct(StructIdx),
	Enum(EnumIdx),
	TypeSet(TypesetIdx),
	TypeAlias(TypeAliasIdx),
	Function(FunctionIdx),
	Constant(ConstIdx),
	/// One `AssocTypeIdx`'s slot — a trait's own declaration or an impl's
	/// provided value; see `AssocTypeSignature`'s own doc comment for why
	/// the two don't need distinct variants here.
	AssocType(AssocTypeIdx),
	Memory(MemoryIdx),
	Global(GlobalIdx),
}

/// What `ensure_signature` found. `Cycle` is never stored anywhere — it's a
/// transient signal for whichever call is re-entering a query still
/// `InProgress` further down the stack; that caller reports the cycle once
/// (using `query_stack` to know what closed the loop) and substitutes
/// `TypeIndex::ERROR`, then keeps going. Every item in the cycle still
/// reaches its own `Done` normally.
///
/// `#[must_use]`: a bare `self.ensure_signature(..);` silently throwing away
/// the result is always a mistake — either the caller wants the resolved
/// `SignatureLocation` (and has to handle `Cycle`/`CycleReported` to get
/// one safely) or it only wants the forcing side effect and should say so
/// with an explicit `let _ = ..`, the way `TraitFunction`/`TraitConst`
/// already do (with a comment proving why `Cycle` can't actually happen for
/// that particular call).
#[must_use]
pub(super) enum SignatureStatus {
	/// Carries *where* — not just *that* — the query's target now lives, so
	/// a caller that only has a `DefId` (an associated type, a type alias,
	/// ...) doesn't need a second `item_lookup` lookup to find out: the one
	/// `ensure_signature` itself already did, right as it finished, is
	/// handed back here instead of being thrown away.
	Resolved(SignatureLocation),
	/// Still being computed; the first re-entry has already been reported.
	CycleReported,
	/// The first re-entry into this unfinished signature.
	Cycle,
}

/// Cycle detection state for one query's demand-driven resolution — mirrors
/// `imports.rs`'s `ResolveStatus`, including its `Error`-like third state
/// (`CycleReported` here): `ResolveStatus::poll` flips `Resolving` straight
/// to `Error` the instant it's re-entered, so a *second* independent path
/// re-discovering the same still-running item finds `Error` (silent, already
/// handled) rather than `Resolving` (which would mean "report a fresh
/// cycle"). `CycleReported` plays the identical role here — e.g. `trait A: B
/// + C {}` where both `B` and `C` separately supertrait back to `A`, or a
/// struct with two fields that each separately lead back to it, would
/// otherwise report the same finding twice, once per path, since nothing
/// would otherwise distinguish "the first path to notice" from "a second
/// path rediscovering what the first already reported." Unlike `Error`,
/// this is never a final state: it's overwritten to `Resolved` unconditionally
/// once the query's own execution actually finishes, same as `InProgress`
/// would be — a signature always has *some* value once resolution reaches
/// `Resolved` (a failed piece becomes `TypeIndex::ERROR`, the same
/// recovery-value pattern `BindingTarget::Error` already uses at the
/// identity layer), so there's never a case where reaching this state needs
/// a "no value" alternative.
///
/// `Resolved` carries the `SignatureLocation` itself — folding in what used
/// to be a separate `item_lookup: HashMap<DefId, SignatureLocation>` map.
/// Definition indices are already known from prescan; `Resolved` records
/// that the signature at that location is ready to read. Each resolver
/// installs this state only after writing its signature data.
#[derive(Clone, Copy)]
enum QueryState {
	Pending,
	InProgress,
	/// Still `InProgress` — this query's own execution hasn't actually
	/// finished — but a cycle closing back through it has already been
	/// reported once. See the enum's own doc comment.
	CycleReported,
	Resolved(SignatureLocation),
}

/// `ast_index` is this `DefId`'s position in `SignatureBuilder::ast_nodes`
/// — set once, at construction, from `defs.rs`'s parse-order record, so
/// `ensure_signature` never needs a second lookup to find the AST it's
/// supposed to resolve.
///
/// Keyed directly by `DefId` (`query_state: HashMap<DefId, QueryEntry>`
/// below) rather than through a `QueryKind`-tagged wrapper: signature
/// resolution is the only query this engine runs — a body doesn't get one
/// of its own, since (unlike a signature) it can't depend on anything that
/// could loop back through it, so it has nothing to force demand-driven or
/// detect a cycle in. Reintroduce the wrapper if a second kind that
/// genuinely needs this same state machine ever materializes; until then
/// it's speculative indirection with nothing to distinguish.
struct QueryEntry {
	ast_index: u32,
	state: QueryState,
}

/// What a caller passes to `ensure_signature` — also pushed as-is onto
/// `query_stack` as that in-progress query's own frame. `requested_at` is
/// the span of the reference that demanded `def_id`; `None` only for a
/// top-level, non-reference demand (the per-`DefId` driver loop) —
/// `resolve_type` always supplies `Some` when it recurses because of a
/// written reference.
#[derive(Clone, Copy)]
pub(super) struct QueryInfo {
	pub(super) def_id: DefId,
	pub(super) requested_at: Option<SourceSpan>,
}

#[derive(Clone, Copy)]
enum BoundSubject {
	Param { env: TypeEnvIdx, index: usize },
	Assoc(AssocTypeIdx),
}

/// The Phase 2 driver. Holds `defs` — Phase 1's finished output, read-only
/// from here on — plus whatever this phase needs on top of it.
pub(super) struct SignatureBuilder<'ast, 'ctx> {
	pub(super) diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
	pub(super) strings: &'ctx StringInterner,
	pub(super) defs: &'ctx DefinitionRegistry,
	ast_nodes: &'ast [AstEntry<'ast>],
	// The resolved data below is read across the sibling TIR modules.
	query_state: HashMap<DefId, QueryEntry>,
	/// In-progress queries, in call order.
	query_stack: Vec<QueryInfo>,
	pub(super) normalization: NormalizationState,
	pub(super) types: TypeInterner,
	pub(super) bounds: BoundArena,
	pub(super) type_envs: TypeEnvArena,
	/// Every generic-param-bearing frame's bounds, index-aligned with
	/// `type_envs`'s own frames (one `Box<[ParamBounds]>` per `TypeEnvId`,
	/// itself index-aligned with that frame's `params`) — kept as a
	/// sibling table here rather than inside `TypeEnvArena` itself, since
	/// `types.rs` is deliberately independent of this module's
	/// resolved-signature data (`BoundId`, diagnostics, ...; see that
	/// module's own doc comment). Grown only through
	/// `reserve_param_bounds`, called once per frame right after whichever
	/// of `push_frame`/`push_param_frame` created it, so the two arrays can
	/// never drift in length.
	pub(super) param_bounds: Vec<Box<[ParamBounds]>>,
	type_aliases: Vec<TypeAliasSignature>,
	pub(super) traits: Vec<TraitSignature>,
	pub(super) structs: Vec<StructSignature>,
	enums: Vec<EnumSignature>,
	typesets: Vec<TypeSetSignature>,
	pub(super) assoc_types: Vec<Option<AssocTypeSignature>>,
	pub(super) functions: Vec<FunctionSignature>,
	pub(super) constants: Vec<ConstantSignature>,
	pub(super) inherent_impls: Vec<Option<InherentImplSignature>>,
	pub(super) trait_impls: Vec<Option<TraitImplSignature>>,
	pub(super) impl_dispatch: ImplDispatch,
}

impl<'ast, 'ctx> SignatureBuilder<'ast, 'ctx> {
	pub(super) fn new(
		diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
		strings: &'ctx StringInterner,
		defs: &'ctx DefinitionRegistry,
		ast_nodes: &'ast [AstEntry<'ast>],
		impl_dispatch: ImplDispatch,
	) -> Self {
		// A pre-seeded kind's own `SignatureLocation` used to be seeded here
		// too, via a separate pass over `defs.traits`/`defs.structs`/... —
		// removed, since it duplicated a fact `ast_nodes` already carries
		// (`AstNodeRef::Trait { trait_index, .. }` etc.) and `ast_node`
		// reads directly. `query_state` itself only ever needs `Pending`
		// here; each item's own arm in `ensure_signature` sets its real
		// `Resolved(SignatureLocation)` once it actually finishes — for a
		// pre-seeded kind that's still worth doing (its *data*, not just its
		// identity, isn't ready before then), just not from this loop.
		let query_state: HashMap<DefId, QueryEntry> = ast_nodes
			.iter()
			.enumerate()
			.map(|(index, entry)| {
				(
					entry.def_id,
					QueryEntry {
						ast_index: u32::try_from(index).unwrap(),
						state: QueryState::Pending,
					},
				)
			})
			.collect();

		Self {
			diagnostics,
			strings,
			defs,
			ast_nodes,
			query_state,
			query_stack: Vec::new(),
			normalization: NormalizationState::default(),
			types: TypeInterner::new(),
			bounds: BoundArena::default(),
			type_envs: TypeEnvArena::new(),
			// `TypeEnvArena::new()` seeds one `Root` entry (`TypeEnvId::ROOT`)
			// before anything else is pushed — matched here with one empty
			// placeholder so the two arrays start, and stay, the same length.
			param_bounds: vec![Box::new([])],
			type_aliases: defs
				.type_aliases
				.iter()
				.map(|_| TypeAliasSignature {
					type_params: TypeEnvIdx::ROOT,
					target: TypeIndex::ERROR,
				})
				.collect(),
			traits: defs
				.traits
				.iter()
				.map(|_| TraitSignature {
					env: TypeEnvIdx::ROOT,
				})
				.collect(),
			structs: defs
				.structs
				.iter()
				.map(|_| StructSignature {
					type_params: TypeEnvIdx::ROOT,
					field_types: Box::default(),
				})
				.collect(),
			enums: defs
				.enums
				.iter()
				.map(|_| EnumSignature {
					repr: TypeIndex::ERROR,
				})
				.collect(),
			typesets: defs
				.typesets
				.iter()
				.map(|_| TypeSetSignature {
					members: Box::default(),
				})
				.collect(),
			assoc_types: defs.assoc_types.iter().map(|_| None).collect(),
			functions: defs
				.functions
				.iter()
				.map(|_| FunctionSignature {
					type_params: TypeEnvIdx::ROOT,
					param_types: Box::default(),
					return_type: TypeIndex::ERROR,
				})
				.collect(),
			constants: defs
				.constants
				.iter()
				.map(|_| ConstantSignature {
					ty: TypeIndex::ERROR,
				})
				.collect(),
			inherent_impls: defs.inherent_impls.iter().map(|_| None).collect(),
			trait_impls: defs.trait_impls.iter().map(|_| None).collect(),
			impl_dispatch,
		}
	}

	/// Resolves one item's whole `<...>` parameter list: the duplicate-name
	/// check moved here from `defs.rs`'s prescan (see the module doc
	/// comment), plus each parameter's own bounds — which may name a
	/// sibling declared *later* in the same list (`Src: Memory where { Size
	/// = S }, S: PointerSize`), hence resolved against the frame pushed for
	/// these params, once every name in it is already registered, rather
	/// than against `ast_params` directly.
	///
	/// Returns that frame — parented at `parent`, so a bound naming
	/// something from outer context (`Self`, an enclosing impl's own `<T>`)
	/// still resolves, and for the caller to go on using as the scope for
	/// the rest of this item's own signature. Each param's bounds are
	/// resolved here too, but no longer handed back — they're persisted
	/// directly into `self.param_bounds`, index-aligned with the returned
	/// frame, the same place every other item's bounds live (see that
	/// field's own doc comment for why this replaced a per-signature-struct
	/// `type_param_bounds` field).
	pub(super) fn resolve_generic_params(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		owner: TypeEnvOwner,
		parent: TypeEnvIdx,
		params: &[ast::TypeParam],
	) -> TypeEnvIdx {
		if params.is_empty() {
			return parent;
		}

		for (index, param) in params.iter().enumerate() {
			if let Some(colliding_param) = params[..index]
				.iter()
				.find(|p| p.name.inner == param.name.inner)
				.map(|p| p.name)
			{
				self.diagnostics.push(report_duplicate_generic_param(
					self.strings,
					file_id,
					param.name,
					colliding_param,
				));
			}
		}

		let type_env = self.type_envs.push_param_frame(
			&mut self.types,
			owner,
			parent,
			params.iter().map(|p| p.name),
		);
		self.param_bounds
			.push((0..params.len()).map(|_| ParamBounds::empty()).collect());

		// A single walk per param decides which bound occurrences exist;
		// both the provisional-membership pass below and the source-bound
		// pass after it consume that same decided tree, so they cannot
		// disagree about what they saw. See `collect_bound_occurrences`.
		let mut occurrences_per_param = Vec::with_capacity(params.len());
		let mut has_equalities = false;
		for ast_param in params {
			let mut occurrences = Vec::new();
			if let Some(bound) = &ast_param.bounds {
				has_equalities |= self.collect_bound_occurrences(
					file_id,
					namespace,
					bound,
					&mut occurrences,
				);
			}
			occurrences_per_param.push(occurrences);
		}

		// Publish direct memberships for every sibling first. No binding RHS
		// types or signature dependencies are resolved here.
		for (index, occurrences) in occurrences_per_param.iter().enumerate() {
			let memberships = provisional_from_occurrences(occurrences);
			self.param_bounds[usize::from(type_env)][index] = ParamBounds {
				declared_bounds: occurrences.iter().map(|o| o.id).collect(),
				facts: BoundFacts::Provisional(memberships.into_boxed_slice()),
			};
		}
		// Only equality expressions can need memberships during construction.
		if has_equalities {
			for index in 0..params.len() {
				let subject = self.type_envs.frame(type_env)[index].ty;
				let memberships = self.param_bounds[usize::from(type_env)]
					[index]
					.facts
					.take();
				self.param_bounds[usize::from(type_env)][index].facts =
					BoundFacts::Provisional(
						self.merge_implied_memberships(memberships, subject)
							.into_boxed_slice(),
					);
			}
		}

		// Resolve source bounds now that every sibling has provisional
		// memberships published, so an equality RHS can reference them.
		for (index, occurrences) in occurrences_per_param.iter().enumerate() {
			let ids = self.resolve_source_bounds_from(
				file_id,
				namespace,
				type_env,
				occurrences,
			);
			self.param_bounds[usize::from(type_env)][index].declared_bounds =
				ids.into_boxed_slice();
		}

		for (index, ast_param) in params.iter().enumerate() {
			let subject = self.type_envs.frame(type_env)[index].ty;
			let declared_bounds = std::mem::take(
				&mut self.param_bounds[usize::from(type_env)][index]
					.declared_bounds,
			);
			let implied_bounds = self
				.compute_implied_bounds(
					&declared_bounds,
					ast_param.name.inner,
					subject,
				)
				.into_boxed_slice();
			self.param_bounds[usize::from(type_env)][index] = ParamBounds {
				declared_bounds,
				facts: BoundFacts::Ready(implied_bounds),
			};
		}

		type_env
	}

	/// Reserves `frame`'s own `param_bounds` slot, initially empty —
	/// bookkeeping `TypeEnvArena` itself has no vocabulary for (`ParamBounds`
	/// is `BoundId`-shaped resolved-signature data, not an identity concern;
	/// see that module's own doc comment), so it's kept as a deliberately
	/// separate step from whatever just built the frame's identities rather
	/// than folded into one combining call. Must be called exactly once per
	/// frame, immediately after it's created — whichever of `push_frame` or
	/// `push_param_frame` did that — so the two arrays can never drift in
	/// length; this is the one place `param_bounds` is ever pushed to.
	///
	/// The placeholder is filled in by `resolve_generic_params`, right after
	/// it resolves the bounds that needed the frame to exist first (a bound
	/// can reference a sibling param). A `Self` frame (trait, typeset, or
	/// impl — none of them routed through `resolve_generic_params`) never
	/// gets filled in and keeps the empty placeholder — correct either way,
	/// since neither is ever queried through it: an impl's `Self` is never
	/// abstract at all, and a trait's/typeset's own `Self` is answered
	/// directly from `TraitSignature::implied_bounds` instead (see
	/// `resolve_bound_member`'s own doc comment).
	fn reserve_param_bounds(&mut self, frame: TypeEnvIdx) {
		debug_assert_eq!(usize::from(frame), self.param_bounds.len());
		let count = self.type_envs.frame(frame).len();
		self.param_bounds
			.push((0..count).map(|_| ParamBounds::empty()).collect());
	}

	/// Resolves a written impl target in the impl's own parameter frame. The
	/// dispatch head only identifies candidates; its arguments are checked and
	/// retained here so matching can use the full target later.
	fn resolve_impl_target(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		env: TypeEnvIdx,
		path: &ast::Path,
		head: Option<Spanned<ImplTarget>>,
	) -> TypeIndex {
		let Some(head) = head else {
			return TypeIndex::ERROR;
		};
		let Some(segment) = path.segments.last() else {
			unreachable!("an impl target path is nonempty")
		};
		let ImplTarget::Struct(struct_index) = head.inner else {
			if !segment.type_args.is_empty() {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::TypeArgumentCountMismatch.code(),
						)
						.with_message(
							"this impl target does not take type arguments",
						)
						.with_label(
							SourceSpan::new(file_id, segment.ident.span)
								.primary_label(),
						),
				);
				return TypeIndex::ERROR;
			}
			return self.impl_target_type(head.inner);
		};
		let def_id = self.defs.structs[usize::from(struct_index)].def_id;
		if matches!(self.query_state[&def_id].state, QueryState::Pending) {
			let _ = self.ensure_signature(QueryInfo {
				def_id,
				requested_at: Some(SourceSpan::new(
					file_id,
					segment.ident.span,
				)),
			});
		}
		let params_env = self.structs[usize::from(struct_index)].type_params;
		let resolved_args: Box<[Spanned<TypeIndex>]> = segment
			.type_args
			.iter()
			.map(|arg| Spanned {
				inner: self.resolve_type(
					file_id,
					namespace,
					env,
					arg,
					InferPolicy::Reject(InferSignatureKind::AssocTypeBinding),
				),
				span: arg.span,
			})
			.collect();
		let args = self.resolve_type_args(
			file_id,
			segment.ident.span,
			params_env,
			&resolved_args,
			TypeEnvOwner::Struct(struct_index),
		);
		self.types.intern(Type::Struct {
			struct_index,
			type_args: args,
		})
	}

	/// Demand an impl header, match its complete target, then validate the
	/// arguments against the impl's own parameter bounds. The returned
	/// arguments belong only to this lookup; no declaration frame is changed.
	pub(super) fn match_trait_impl_candidate(
		&mut self,
		impl_index: TraitImplIdx,
		receiver: TypeIndex,
		reference: SourceSpan,
	) -> Option<Box<[TypeIndex]>> {
		if self.trait_impls[usize::from(impl_index)].is_none() {
			let def_id = self.defs.trait_impls[usize::from(impl_index)].def_id;
			// Memory/global synthetic impls have a unique nominal target
			// already fixed by prescan. Keep their owner query lazy until an
			// associated value is actually demanded.
			if matches!(
				self.ast_node(def_id),
				AstNodeRef::Memory { .. }
					| AstNodeRef::ImportedMemory { .. }
					| AstNodeRef::Global { .. }
					| AstNodeRef::ImportedGlobal { .. }
			) {
				let head = self.impl_dispatch.trait_header(impl_index).target?;
				return (ImplTarget::from_type(self.types.resolve(receiver))
					== Some(head.inner))
				.then(Box::<[TypeIndex]>::default);
			}
			let _ = self.ensure_signature(QueryInfo {
				def_id,
				requested_at: Some(reference),
			});
		}
		let header = self.trait_impls[usize::from(impl_index)].as_ref()?;
		self.match_impl_target_and_bounds(
			header.type_params,
			header.target.inner,
			receiver,
			reference,
		)
	}

	pub(super) fn match_inherent_impl_candidate(
		&mut self,
		impl_index: InherentImplIdx,
		receiver: TypeIndex,
		reference: SourceSpan,
	) -> bool {
		if self.inherent_impls[usize::from(impl_index)].is_none() {
			let def_id =
				self.defs.inherent_impls[usize::from(impl_index)].def_id;
			let _ = self.ensure_signature(QueryInfo {
				def_id,
				requested_at: Some(reference),
			});
		}
		let Some(header) =
			self.inherent_impls[usize::from(impl_index)].as_ref()
		else {
			return false;
		};
		self.match_impl_target_and_bounds(
			header.type_params,
			header.target.inner,
			receiver,
			reference,
		)
		.is_some()
	}

	fn match_impl_target_and_bounds(
		&mut self,
		env: TypeEnvIdx,
		target: TypeIndex,
		receiver: TypeIndex,
		reference: SourceSpan,
	) -> Option<Box<[TypeIndex]>> {
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
		let receiver = self.normalize_type(receiver, reference);
		let count = if env == TypeEnvIdx::ROOT {
			0
		} else {
			self.type_envs.frame(env).len()
		};
		let args =
			self.types.match_impl_target(target, receiver, env, count)?;
		for (index, &arg) in args.iter().enumerate() {
			let bound_count = self.param_bounds[usize::from(env)][index]
				.facts
				.current()
				.len();
			for bound_index in 0..bound_count {
				let bound = &self.param_bounds[usize::from(env)][index]
					.facts
					.current()[bound_index];
				// Equality and nested associated-type requirements need the
				// assumption solver from checkpoint 4. Until then they must
				// not be accepted on trait membership alone.
				if !bound.bindings.is_empty() {
					return None;
				}
				let trait_index = bound.trait_index;
				let normalized = self.normalize_head(arg, reference);
				if normalized == TypeIndex::ERROR
					|| !self.type_satisfies_trait(
						normalized,
						trait_index,
						reference,
					) {
					return None;
				}
			}
		}
		Some(args)
	}

	pub(super) fn implied_bounds(
		&self,
		env: TypeEnvIdx,
		param_index: u32,
	) -> &[ImpliedTraitBound] {
		self.param_bounds[usize::from(env)][param_index as usize]
			.facts
			.current()
	}

	/// `def_id`'s own `AstNodeRef` — `defs.rs`'s output, so this is pure
	/// identity: reading it never forces `ensure_signature` and is valid
	/// the moment `SignatureBuilder` exists, before any query has run at
	/// all. This is how a pre-seeded kind's own index
	/// (`AstNodeRef::Trait { trait_index, .. }` and friends) is read
	/// without forcing that item's signature — the six pre-seeded kinds no
	/// longer get an early `SignatureLocation` seeded into `query_state`
	/// the way they briefly got one seeded into the old, separate
	/// `item_lookup` map; they get this instead, which was already sitting
	/// there.
	pub(super) fn ast_node(&self, def_id: DefId) -> &AstNodeRef<'ast> {
		&self.ast_nodes[self.query_state[&def_id].ast_index as usize].node
	}

	/// The demand-driven driver: computes `def_id`'s signature if it hasn't
	/// been already. The two checks below are safe to return early from —
	/// nothing has been pushed onto `query_stack` yet at that point. Past
	/// that, no early `return`: `query_stack`'s frame has to pop and
	/// `state` has to reach `Resolved` no matter which arm runs below, or
	/// this query is left `InProgress` forever.
	pub(super) fn ensure_signature(
		&mut self,
		query: QueryInfo,
	) -> SignatureStatus {
		match self.query_state[&query.def_id].state {
			QueryState::Resolved(location) => {
				return SignatureStatus::Resolved(location);
			}
			QueryState::CycleReported => {
				return SignatureStatus::CycleReported;
			}
			QueryState::InProgress => {
				self.query_state.get_mut(&query.def_id).unwrap().state =
					QueryState::CycleReported;
				return SignatureStatus::Cycle;
			}
			QueryState::Pending => {}
		}

		self.query_state.get_mut(&query.def_id).unwrap().state =
			QueryState::InProgress;
		self.query_stack.push(query);

		let entry =
			&self.ast_nodes[self.query_state[&query.def_id].ast_index as usize];
		let location =
			self.compute_signature(entry.file_id, entry.namespace, entry.node);

		self.query_stack.pop();
		self.query_state.get_mut(&query.def_id).unwrap().state =
			QueryState::Resolved(location);
		SignatureStatus::Resolved(location)
	}

	/// Demands the query that owns this provider's slot. Written impl members
	/// own a query; synthetic members reuse their memory/global owner's DefId.
	/// Read the associated-type slot, not the owner's query result kind.
	/// The value was normalized in its definition environment. Instantiation
	/// and any normalization made possible by substitution belong to the caller.
	pub(super) fn ensure_assoc_type_value(
		&mut self,
		provider: AssocTypeProvider,
		reference: SourceSpan,
	) -> TypeIndex {
		let index = provider.index();
		let def_id = self.defs.assoc_types[usize::from(index)].def_id;
		match self.ensure_signature(QueryInfo {
			def_id,
			requested_at: Some(reference),
		}) {
			SignatureStatus::Resolved(_) => self.assoc_types
				[usize::from(index)]
			.as_ref()
			.expect("the provider's owner populates its associated-type slot")
			.value
			.expect("an impl provider has a value, including error recovery"),
			SignatureStatus::Cycle => {
				self.diagnostics.push(self.report_cycle(
					def_id,
					reference,
					DiagnosticCode::CyclicAssociatedType,
					|name| {
						format!(
							"computing the associated-type value supplied by `{name}`"
						)
					},
				));
				TypeIndex::ERROR
			}
			SignatureStatus::CycleReported => TypeIndex::ERROR,
		}
	}

	/// Resolves a `fn`'s generic params, parameter types and return type.
	/// Shared by `AstNodeRef::Function` and `AstNodeRef::ImportedFunction` —
	/// both a plain/declared free function and an imported one carry the
	/// exact same `ast::FunctionSignature` shape, so there's nothing about
	/// resolution itself that differs once that signature is in hand.
	fn resolve_function_signature(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		function_index: FunctionIdx,
		signature: &ast::FunctionSignature,
	) -> SignatureLocation {
		let type_env = self.resolve_generic_params(
			file_id,
			namespace,
			TypeEnvOwner::Function(function_index),
			TypeEnvIdx::ROOT,
			&signature.type_params,
		);

		let param_types: Box<[TypeIndex]> = signature
			.params
			.iter()
			.map(|param| match &param.inner.inner.ty {
				Some(ty) => self.resolve_type(
					file_id,
					namespace,
					type_env,
					ty,
					InferPolicy::Reject(InferSignatureKind::Function),
				),
				None => {
					let name = param.inner.inner.name;
					if name.inner != Keyword::SelfLower.symbol() {
						self.diagnostics.push(report_missing_parameter_type(
							self.strings,
							file_id,
							name,
						));
					}
					TypeIndex::ERROR
				}
			})
			.collect();

		let return_type = match &signature.result {
			Some(result) => self.resolve_type(
				file_id,
				namespace,
				type_env,
				result,
				InferPolicy::Reject(InferSignatureKind::ReturnType),
			),
			None => TypeIndex::UNIT,
		};

		self.functions[usize::from(function_index)] = FunctionSignature {
			type_params: type_env,
			param_types,
			return_type,
		};
		SignatureLocation::Function(function_index)
	}

	/// Resolves and validates a `memory` declaration's `Size` and fills in
	/// its synthetic `Memory` impl. Shared by `AstNodeRef::Memory` and
	/// `AstNodeRef::ImportedMemory` — a declared memory and an imported one
	/// resolve identically once their `size` type expression is in hand.
	fn resolve_memory_signature(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		memory_index: MemoryIdx,
		name: Spanned<SymbolU32>,
		size: &Spanned<ast::TypeExpression>,
	) -> SignatureLocation {
		let memory_def = &self.defs.memories[usize::from(memory_index)];
		let trait_impl_index = memory_def.trait_impl_index;
		let size_assoc_type_index = memory_def.size_assoc_type_index;

		let resolved_size = self.resolve_type(
			file_id,
			namespace,
			TypeEnvIdx::ROOT,
			size,
			InferPolicy::Reject(InferSignatureKind::AssocTypeBinding),
		);

		let resolved_size = self
			.normalize_type(resolved_size, SourceSpan::new(file_id, size.span));

		// `Size`'s actual constraint (`PointerSize`) lives on `Memory`'s own
		// declaration, not hardcoded here — this looks it up and lets
		// `check_assoc_type_value` validate against it, the same bound-
		// satisfaction path any other associated-type binding goes through.
		let memory_trait = self.defs.intrinsics.memory.expect(
			"checked by impls.rs's dispatch pass before any signature is resolved",
		);
		let size_symbol = self
			.strings
			.get("Size")
			.expect("interned by synthesize_memory_impl during pre-scan");
		let declared_size_index = {
			let trait_def = &self.defs.traits[usize::from(memory_trait)];
			let &member_index = trait_def
				.bindings
				.get(&BindingKey::ty(size_symbol))
				.expect("the stdlib's `Memory` trait must declare `Size`");
			let MemberKind::AssociatedType(index) =
				trait_def.members[usize::from(member_index)].kind
			else {
				panic!("the stdlib's `Memory::Size` must be an associated type")
			};
			index
		};
		let checked_size = self.check_assoc_type_value(
			declared_size_index,
			Spanned {
				inner: resolved_size,
				span: size.span,
			},
			file_id,
			TypeEnvOwner::Trait(memory_trait),
		);

		let memory_type = self.types.intern(Type::Memory { memory_index });

		self.assoc_types[usize::from(size_assoc_type_index)] =
			Some(AssocTypeSignature {
				declared_bounds: Box::new([]),
				facts: BoundFacts::Ready(Box::new([])),
				value: Some(checked_size),
			});
		self.trait_impls[usize::from(trait_impl_index)] =
			Some(TraitImplSignature {
				type_params: TypeEnvIdx::ROOT,
				target: Spanned {
					inner: memory_type,
					span: name.span,
				},
				self_scope: TypeEnvIdx::ROOT,
			});
		SignatureLocation::Memory(memory_index)
	}

	/// Fills in a `global` declaration's synthetic `Global` impl (and, for
	/// `global mut`, its `GlobalMut` impl too) once its `Value` type is
	/// already resolved. Shared by `AstNodeRef::Global` and
	/// `AstNodeRef::ImportedGlobal`, which differ only in how they arrive at
	/// `resolved_value` — a written global may omit its type and gets
	/// diagnosed for it, an imported one's type is mandatory in the grammar.
	fn resolve_global_signature(
		&mut self,
		global_index: GlobalIdx,
		name: Spanned<SymbolU32>,
		mut_span: Option<TextSpan>,
		resolved_value: TypeIndex,
	) -> SignatureLocation {
		let global_def = &self.defs.globals[usize::from(global_index)];
		let trait_impl_index = global_def.trait_impl_index;
		let value_assoc_type_index = global_def.value_assoc_type_index;
		let mut_trait_impl_index = global_def.mut_trait_impl_index;

		let resolved_value = self.normalize_type(
			resolved_value,
			SourceSpan::new(global_def.file_id, name.span),
		);
		let global_type = self.types.intern(Type::Global { global_index });

		self.assoc_types[usize::from(value_assoc_type_index)] =
			Some(AssocTypeSignature {
				declared_bounds: Box::new([]),
				facts: BoundFacts::Ready(Box::new([])),
				value: Some(resolved_value),
			});

		self.trait_impls[usize::from(trait_impl_index)] =
			Some(TraitImplSignature {
				type_params: TypeEnvIdx::ROOT,
				target: Spanned {
					inner: global_type,
					span: name.span,
				},
				self_scope: TypeEnvIdx::ROOT,
			});
		if let Some(mut_trait_impl_index) = mut_trait_impl_index {
			debug_assert!(mut_span.is_some());
			self.trait_impls[usize::from(mut_trait_impl_index)] =
				Some(TraitImplSignature {
					type_params: TypeEnvIdx::ROOT,
					target: Spanned {
						inner: global_type,
						span: name.span,
					},
					self_scope: TypeEnvIdx::ROOT,
				});
		}
		SignatureLocation::Global(global_index)
	}

	fn compute_signature(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		ast_node: AstNodeRef<'_>,
	) -> SignatureLocation {
		match ast_node {
			AstNodeRef::TypeAlias {
				item,
				type_alias_index,
			} => {
				let ast::Item::TypeAlias {
					name,
					type_params,
					body,
					..
				} = item
				else {
					unreachable!()
				};

				// A `#[intrinsic]` primitive (`type u8;`) is bodiless by
				// design — its identity already comes from
				// `defs.intrinsics`, so there's nothing here to resolve.
				// Checked first so a real, non-intrinsic alias only needs
				// to handle a missing body as a diagnosed error below.
				let signature =
					match self.defs.intrinsics.identity_of(type_alias_index) {
						Some(target) => TypeAliasSignature {
							type_params: TypeEnvIdx::ROOT,
							target,
						},
						None => {
							let type_env = self.resolve_generic_params(
								file_id,
								namespace,
								TypeEnvOwner::TypeAlias(type_alias_index),
								TypeEnvIdx::ROOT,
								type_params,
							);
							let target = match body {
								Some(body) => self.resolve_type(
									file_id,
									namespace,
									type_env,
									body,
									InferPolicy::Reject(
										InferSignatureKind::TypeAlias,
									),
								),
								None => {
									self.diagnostics.push(
										report_missing_type_alias_body(
											file_id, name.span,
										),
									);
									TypeIndex::ERROR
								}
							};
							TypeAliasSignature {
								type_params: type_env,
								target,
							}
						}
					};

				self.type_aliases[usize::from(type_alias_index)] = signature;
				SignatureLocation::TypeAlias(type_alias_index)
			}
			AstNodeRef::Trait { trait_index, item } => {
				let ast::Item::Trait {
					name, supertraits, ..
				} = item
				else {
					unreachable!()
				};

				// `Self` is owned by the trait itself (`owner: def_id`,
				// `param_index: 0`) — pushed *before* the supertrait clause
				// is resolved (a bound may reference it, e.g. `trait X: Add
				// where { Rhs = Self } {}`) and once here, at the root, so
				// every member's own resolution (`TraitFunction`/
				// `TraitConst`) parents its own frame at this same one
				// rather than each minting its own `Self` binding.
				let self_scope = self.type_envs.push_param_frame(
					&mut self.types,
					TypeEnvOwner::Trait(trait_index),
					TypeEnvIdx::ROOT,
					[Spanned {
						inner: ast::Keyword::SelfPascal.symbol(),
						span: name.span,
					}],
				);
				self.reserve_param_bounds(self_scope);

				// The Self identity is available while its facts are collected;
				// the surrounding signature query remains in progress.
				self.traits[usize::from(trait_index)] =
					TraitSignature { env: self_scope };
				let subject = self.type_envs.frame(self_scope)[0].ty;
				let (declared_bounds, implied_bounds) = self
					.resolve_subject_bounds(
						file_id,
						namespace,
						self_scope,
						supertraits.as_ref(),
						BoundSubject::Param {
							env: self_scope,
							index: 0,
						},
						subject,
						name.inner,
					);
				self.param_bounds[usize::from(self_scope)][0] = ParamBounds {
					declared_bounds,
					facts: BoundFacts::Ready(implied_bounds.into_boxed_slice()),
				};
				self.traits[usize::from(trait_index)] =
					TraitSignature { env: self_scope };
				SignatureLocation::Trait(trait_index)
			}
			AstNodeRef::TraitFunction {
				trait_index,
				item,
				function_index,
			} => {
				let ast::TraitItem::Function { signature, .. } = item else {
					unreachable!()
				};

				// Forces the trait's own header — supertraits and, what
				// this member actually needs, its `Self` frame — before
				// resolving anything against it. Can never close a cycle
				// back through *this* member: a trait's own header only
				// ever depends on other traits' signatures (its supertrait
				// clause), never on one of its own members', so there's no
				// path from here back to an in-progress `def_id`.
				let trait_def_id =
					self.defs.traits[usize::from(trait_index)].def_id;
				let _ = self.ensure_signature(QueryInfo {
					def_id: trait_def_id,
					requested_at: None,
				});
				let self_scope = self.traits[usize::from(trait_index)].env;

				let scope = self.resolve_generic_params(
					file_id,
					namespace,
					TypeEnvOwner::Function(function_index),
					self_scope,
					&signature.type_params,
				);

				// `defs.rs` already validated this member's parameter list
				// (`validate_method_params`) — a `self` in any other
				// position is already diagnosed there (`SelfParamPosition`),
				// so a `self`-named parameter is never re-diagnosed here
				// regardless of where it sits. This only needs to answer
				// "does the first slot default to `Self`", the same
				// constant-time check that decided it there.
				let is_method = signature.params.first().is_some_and(|p| {
					p.inner.inner.name.inner == Keyword::SelfLower.symbol()
				});

				let mut param_types: Vec<TypeIndex> =
					Vec::with_capacity(signature.params.len());
				for (index, param) in signature.params.iter().enumerate() {
					let ty = match &param.inner.inner.ty {
						Some(ty) => self.resolve_type(
							file_id,
							namespace,
							scope,
							ty,
							InferPolicy::Reject(InferSignatureKind::Function),
						),
						// `self`'s type is this trait's own abstract `Self`.
						// Constructed directly (not looked up through
						// `self_scope`) since nothing was actually written
						// here for an access to attach to — the source
						// says `self`, never `Self`. Must intern with the
						// *same* `env` the trait's own header already used
						// for `Self` (`self_scope`) — otherwise `self` and
						// `Self` would dedup to two different `TypeIndex`es
						// instead of one.
						None if index == 0 && is_method => {
							self.types.intern(Type::TypeParam {
								env: self_scope,
								param_index: 0,
							})
						}
						None => {
							let name = param.inner.inner.name;
							if name.inner != Keyword::SelfLower.symbol() {
								self.diagnostics.push(
									report_missing_parameter_type(
										self.strings,
										file_id,
										name,
									),
								);
							}
							TypeIndex::ERROR
						}
					};
					param_types.push(ty);
				}

				let return_type = match &signature.result {
					Some(result) => self.resolve_type(
						file_id,
						namespace,
						scope,
						result,
						InferPolicy::Reject(InferSignatureKind::ReturnType),
					),
					None => TypeIndex::UNIT,
				};

				self.functions[usize::from(function_index)] =
					FunctionSignature {
						type_params: scope,
						param_types: param_types.into_boxed_slice(),
						return_type,
					};
				SignatureLocation::Function(function_index)
			}
			AstNodeRef::TraitConst {
				const_index,
				trait_index,
				item,
			} => {
				let ast::TraitItem::Const { ty, .. } = item else {
					unreachable!()
				};

				// See `TraitFunction`'s identical force — same reasoning.
				let trait_def_id =
					self.defs.traits[usize::from(trait_index)].def_id;
				let _ = self.ensure_signature(QueryInfo {
					def_id: trait_def_id,
					requested_at: None,
				});
				let self_scope = self.traits[usize::from(trait_index)].env;

				// No default-value evaluation yet — that needs constant-
				// expression evaluation, which doesn't exist in this
				// architecture yet (see `ConstantSignature`'s own doc
				// comment).
				let resolved_ty = self.resolve_type(
					file_id,
					namespace,
					self_scope,
					ty,
					InferPolicy::Reject(InferSignatureKind::Const),
				);

				self.constants[usize::from(const_index)] =
					ConstantSignature { ty: resolved_ty };
				SignatureLocation::Constant(const_index)
			}
			AstNodeRef::TraitAssocType {
				assoc_type_index,
				trait_index,
				item,
			} => {
				let ast::TraitItem::AssociatedType { name, bounds, .. } = item
				else {
					unreachable!()
				};

				// See `TraitFunction`'s identical force — same reasoning:
				// this member's own declared bound can reference the
				// trait's `Self` (`type Size: Memory where { X = Self::Y }`),
				// which needs `self_scope` in scope to resolve at all.
				let trait_def_id =
					self.defs.traits[usize::from(trait_index)].def_id;
				let _ = self.ensure_signature(QueryInfo {
					def_id: trait_def_id,
					requested_at: None,
				});
				let self_scope = self.traits[usize::from(trait_index)].env;

				let base = self.type_envs.frame(self_scope)[0].ty;
				let subject = self.types.intern(Type::AssocTypeProjection {
					base,
					trait_index,
					assoc_type_index,
				});
				let (resolved_bounds, implied_bounds) = self
					.resolve_subject_bounds(
						file_id,
						namespace,
						self_scope,
						bounds.as_ref(),
						BoundSubject::Assoc(assoc_type_index),
						subject,
						name.inner,
					);
				self.assoc_types[usize::from(assoc_type_index)] =
					Some(AssocTypeSignature {
						declared_bounds: resolved_bounds,
						facts: BoundFacts::Ready(
							implied_bounds.into_boxed_slice(),
						),
						value: None,
					});
				SignatureLocation::AssocType(assoc_type_index)
			}
			AstNodeRef::TraitImplAssocType {
				assoc_type_index,
				item,
				block_index,
			} => {
				let ast::ImplItem::AssocType { ty, .. } = item else {
					unreachable!()
				};

				// Forces the impl's own header — its generic params and,
				// what this member actually needs, its `Self` frame (bound
				// to the impl's target type) — before resolving anything
				// against it. Same reasoning as `TraitFunction`'s force of
				// its trait, and equally cycle-free: an impl's own header
				// only ever depends on other items' signatures, never on
				// one of its own members'.
				let impl_def_id =
					self.defs.trait_impls[usize::from(block_index)].def_id;
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let self_scope = self.trait_impls[usize::from(block_index)]
					.as_ref()
					.expect(
						"an impl's own header resolves before any of its members are forced",
					)
					.self_scope;

				let resolved_ty = self.resolve_type(
					file_id,
					namespace,
					self_scope,
					ty,
					InferPolicy::Reject(InferSignatureKind::AssocTypeBinding),
				);

				let resolved_ty = self.normalize_type(
					resolved_ty,
					SourceSpan::new(file_id, ty.span),
				);

				// An impl provides a value, it doesn't declare a
				// requirement — `declared_bounds`/`implied_bounds` stay
				// empty; only a trait's own declaration (the
				// `TraitAssocType` arm above) ever populates those.
				self.assoc_types[usize::from(assoc_type_index)] =
					Some(AssocTypeSignature {
						declared_bounds: Box::new([]),
						facts: BoundFacts::Ready(Box::new([])),
						value: Some(resolved_ty),
					});
				SignatureLocation::AssocType(assoc_type_index)
			}
			AstNodeRef::Memory { memory_index, item } => {
				let ast::Item::Memory { name, size, .. } = item else {
					unreachable!()
				};
				self.resolve_memory_signature(
					file_id,
					namespace,
					memory_index,
					*name,
					size,
				)
			}
			AstNodeRef::ImportedMemory { memory_index, decl } => {
				let ast::ImportDeclaration::Memory { name, size, .. } = decl
				else {
					unreachable!()
				};
				self.resolve_memory_signature(
					file_id,
					namespace,
					memory_index,
					*name,
					size,
				)
			}
			AstNodeRef::Global { global_index, item } => {
				let ast::Item::Global {
					name, ty, mut_span, ..
				} = item
				else {
					unreachable!()
				};

				// `global x = 0;` (no explicit type) would need the value
				// expression's own type to stand in for it, which needs the
				// body phase this architecture doesn't have yet — rather
				// than leave this global's `Value` silently unresolved,
				// require the annotation and fall back to `ERROR`.
				let resolved_value = match ty {
					Some(ty) => self.resolve_type(
						file_id,
						namespace,
						TypeEnvIdx::ROOT,
						ty,
						InferPolicy::Reject(
							InferSignatureKind::AssocTypeBinding,
						),
					),
					None => {
						self.diagnostics
							.push(report_missing_global_type(file_id, *name));
						TypeIndex::ERROR
					}
				};
				self.resolve_global_signature(
					global_index,
					*name,
					*mut_span,
					resolved_value,
				)
			}
			AstNodeRef::ImportedGlobal { global_index, decl } => {
				let ast::ImportDeclaration::Global {
					name, ty, mut_span, ..
				} = decl
				else {
					unreachable!()
				};
				// Unlike `Item::Global`, an imported global's type is
				// mandatory in the grammar itself — there's no initializer
				// expression to fall back to anyway, so there's nothing to
				// diagnose here.
				let resolved_value = self.resolve_type(
					file_id,
					namespace,
					TypeEnvIdx::ROOT,
					ty,
					InferPolicy::Reject(InferSignatureKind::AssocTypeBinding),
				);
				self.resolve_global_signature(
					global_index,
					*name,
					*mut_span,
					resolved_value,
				)
			}
			AstNodeRef::RecordStruct { struct_index, item } => {
				let ast::Item::RecordStruct {
					type_params: ast_type_params,
					fields,
					..
				} = item
				else {
					unreachable!()
				};

				let type_env = self.resolve_generic_params(
					file_id,
					namespace,
					TypeEnvOwner::Struct(struct_index),
					TypeEnvIdx::ROOT,
					ast_type_params,
				);
				// Written before fields are touched, not alongside
				// `field_types` below, so a self-/mutually-referencing
				// pointer field — `resolve_type` recursing back into this
				// same struct via `resolve_type_args`, to validate its own
				// written type arguments — reads this struct's real param
				// bounds instead of the placeholder `ROOT` frame it started
				// in. Same reasoning as `ast_node` already letting identity
				// be read before a query finishes, just for one more fact.
				self.structs[usize::from(struct_index)].type_params = type_env;

				// One-to-one with `defs.structs[..].fields` — a duplicate
				// name still gets its own slot resolved there, so it does
				// here too (name lookup, not type resolution, is where a
				// duplicate is unreachable).
				let mut field_types: Vec<TypeIndex> =
					Vec::with_capacity(fields.len());
				for f in fields.iter() {
					let ty_expr = &f.inner.inner.ty;
					let ty = self.resolve_type(
						file_id,
						namespace,
						type_env,
						ty_expr,
						InferPolicy::Reject(InferSignatureKind::Struct),
					);
					self.check_struct_direct_recursion(
						file_id,
						ty_expr.span,
						ty,
					);
					field_types.push(ty);
				}

				self.structs[usize::from(struct_index)].field_types =
					field_types.into_boxed_slice();
				SignatureLocation::Struct(struct_index)
			}
			AstNodeRef::TupleStruct { struct_index, item } => {
				let ast::Item::TupleStruct {
					type_params: ast_type_params,
					fields,
					..
				} = item
				else {
					unreachable!()
				};

				let scope = self.resolve_generic_params(
					file_id,
					namespace,
					TypeEnvOwner::Struct(struct_index),
					TypeEnvIdx::ROOT,
					ast_type_params,
				);
				// See the identical write in the `RecordStruct` arm above.
				self.structs[usize::from(struct_index)].type_params = scope;

				let mut field_types: Vec<TypeIndex> =
					Vec::with_capacity(fields.len());
				for f in fields.iter() {
					let ty_expr = &f.inner.inner.ty;
					let ty = self.resolve_type(
						file_id,
						namespace,
						scope,
						ty_expr,
						InferPolicy::Reject(InferSignatureKind::Struct),
					);
					self.check_struct_direct_recursion(
						file_id,
						ty_expr.span,
						ty,
					);
					field_types.push(ty);
				}

				self.structs[usize::from(struct_index)].field_types =
					field_types.into_boxed_slice();
				SignatureLocation::Struct(struct_index)
			}
			AstNodeRef::Function {
				item,
				func_index: function_index,
			} => {
				let (ast::Item::Function { signature, .. }
				| ast::Item::FunctionDeclaration { signature, .. }) = item
				else {
					unreachable!()
				};
				self.resolve_function_signature(
					file_id,
					namespace,
					function_index,
					signature,
				)
			}
			AstNodeRef::ImportedFunction {
				function_index,
				decl,
			} => {
				let ast::ImportDeclaration::Function { signature, .. } = decl
				else {
					unreachable!()
				};
				self.resolve_function_signature(
					file_id,
					namespace,
					function_index,
					signature,
				)
			}
			AstNodeRef::InherentImplBlock { item, block_index } => {
				let ast::Item::InherentImpl {
					type_params,
					target,
					..
				} = item
				else {
					unreachable!()
				};
				let scope = self.resolve_generic_params(
					file_id,
					namespace,
					TypeEnvOwner::InherentImpl(block_index),
					TypeEnvIdx::ROOT,
					type_params,
				);
				let target_type = self.resolve_impl_target(
					file_id,
					namespace,
					scope,
					target,
					self.impl_dispatch.inherent_target(block_index),
				);
				let target_span = target.span();
				let target_spanned = Spanned {
					inner: target_type,
					span: target_span,
				};
				let self_scope = self.type_envs.push_frame(
					Box::new([TypeParam {
						name: Spanned {
							inner: ast::Keyword::SelfPascal.symbol(),
							span: target_span,
						},
						ty: target_type,
						accesses: Vec::new(),
					}]),
					TypeEnvOwner::InherentImpl(block_index),
					scope,
				);
				self.reserve_param_bounds(self_scope);
				self.inherent_impls[usize::from(block_index)] =
					Some(InherentImplSignature {
						type_params: scope,
						target: target_spanned,
						self_scope,
					});
				SignatureLocation::InherentImpl(block_index)
			}
			AstNodeRef::InherentImplFunction {
				item,
				block_index,
				function_index,
			} => {
				let ast::ImplItem::Function { signature, .. } = item else {
					unreachable!()
				};

				// Forces the impl block's own header — its target type and
				// `self` frame — before resolving anything against it. Can
				// never close a cycle back through *this* member: the
				// block's own header only depends on its target path/
				// generic bounds, never on one of its members' signatures.
				let impl_def_id =
					self.defs.inherent_impls[usize::from(block_index)].def_id;
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let self_scope = self.inherent_impls[usize::from(block_index)]
					.as_ref()
					.expect("inherent impl header is resolved")
					.self_scope;
				let target_type = self.inherent_impls[usize::from(block_index)]
					.as_ref()
					.expect("inherent impl header is resolved")
					.target
					.inner;

				let scope = self.resolve_generic_params(
					file_id,
					namespace,
					TypeEnvOwner::Function(function_index),
					self_scope,
					&signature.type_params,
				);

				let is_method = signature.params.first().is_some_and(|p| {
					p.inner.inner.name.inner == Keyword::SelfLower.symbol()
				});

				let mut param_types: Vec<TypeIndex> =
					Vec::with_capacity(signature.params.len());
				for (index, param) in signature.params.iter().enumerate() {
					let ty = match &param.inner.inner.ty {
						Some(ty) => self.resolve_type(
							file_id,
							namespace,
							scope,
							ty,
							InferPolicy::Reject(InferSignatureKind::Function),
						),
						// `self`'s type is this impl's own concrete target —
						// unlike a trait's abstract `Self`, there's already a
						// real type to point at, so no `Type::TypeParam` is
						// interned for it.
						None if index == 0 && is_method => target_type,
						None => {
							let name = param.inner.inner.name;
							if name.inner != Keyword::SelfLower.symbol() {
								self.diagnostics.push(
									report_missing_parameter_type(
										self.strings,
										file_id,
										name,
									),
								);
							}
							TypeIndex::ERROR
						}
					};
					param_types.push(ty);
				}

				let return_type = match &signature.result {
					Some(result) => self.resolve_type(
						file_id,
						namespace,
						scope,
						result,
						InferPolicy::Reject(InferSignatureKind::ReturnType),
					),
					None => TypeIndex::UNIT,
				};

				self.functions[usize::from(function_index)] =
					FunctionSignature {
						type_params: scope,
						param_types: param_types.into_boxed_slice(),
						return_type,
					};
				SignatureLocation::Function(function_index)
			}
			AstNodeRef::InherentImplConst {
				const_index,
				item,
				block_index,
			} => {
				let ast::ImplItem::Constant { ty, .. } = item else {
					unreachable!()
				};

				// See `InherentImplFunction`'s identical force — same
				// reasoning.
				let impl_def_id =
					self.defs.inherent_impls[usize::from(block_index)].def_id;
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let self_scope = self.inherent_impls[usize::from(block_index)]
					.as_ref()
					.expect("inherent impl header is resolved")
					.self_scope;

				let resolved_ty = match ty {
					Some(ty) => self.resolve_type(
						file_id,
						namespace,
						self_scope,
						ty,
						InferPolicy::Reject(InferSignatureKind::Const),
					),
					// No default-value evaluation yet — inferring the
					// omitted type from `value` needs constant-expression
					// evaluation, which doesn't exist in this architecture
					// yet (see `ConstantSignature`'s own doc comment).
					None => todo!(
						"inferring an impl const's type from its initializer isn't implemented yet"
					),
				};

				self.constants[usize::from(const_index)] =
					ConstantSignature { ty: resolved_ty };
				SignatureLocation::Constant(const_index)
			}
			AstNodeRef::TraitImplBlock { item, block_index } => {
				let ast::Item::TraitImpl {
					type_params,
					target,
					..
				} = item
				else {
					unreachable!()
				};
				let scope = self.resolve_generic_params(
					file_id,
					namespace,
					TypeEnvOwner::TraitImpl(block_index),
					TypeEnvIdx::ROOT,
					type_params,
				);
				let header = self.impl_dispatch.trait_header(block_index);
				let target_type = self.resolve_impl_target(
					file_id,
					namespace,
					scope,
					target,
					header.target,
				);
				let target_span = target.span();
				let target_spanned = Spanned {
					inner: target_type,
					span: target_span,
				};
				let self_scope = self.type_envs.push_frame(
					Box::new([TypeParam {
						name: Spanned {
							inner: ast::Keyword::SelfPascal.symbol(),
							span: target_span,
						},
						ty: target_type,
						accesses: Vec::new(),
					}]),
					TypeEnvOwner::TraitImpl(block_index),
					scope,
				);
				self.reserve_param_bounds(self_scope);
				self.trait_impls[usize::from(block_index)] =
					Some(TraitImplSignature {
						type_params: scope,
						target: target_spanned,
						self_scope,
					});
				SignatureLocation::TraitImpl(block_index)
			}
			AstNodeRef::Enum { enum_index, item } => {
				let ast::Item::Enum { repr, name, .. } = item else {
					unreachable!()
				};

				let repr_type = match repr {
					Some(repr_expr) => {
						let resolved = self.resolve_type(
							file_id,
							namespace,
							TypeEnvIdx::ROOT,
							repr_expr,
							InferPolicy::Reject(InferSignatureKind::EnumRepr),
						);
						if resolved != TypeIndex::ERROR
							&& !resolved.is_integer()
						{
							self.diagnostics.push(
								report_enum_repr_not_integer(
									file_id,
									repr_expr.span,
								),
							);
							TypeIndex::ERROR
						} else {
							resolved
						}
					}
					None => {
						self.diagnostics
							.push(report_missing_enum_repr(file_id, name.span));
						TypeIndex::ERROR
					}
				};

				self.enums[usize::from(enum_index)] =
					EnumSignature { repr: repr_type };
				SignatureLocation::Enum(enum_index)
			}
			AstNodeRef::TypeSet {
				typeset_index,
				item,
			} => {
				let ast::Item::TypeSet {
					name,
					bounds,
					members,
					..
				} = item
				else {
					unreachable!()
				};
				let trait_index =
					self.defs.typesets[usize::from(typeset_index)].trait_index;
				let member_impls = self.defs.typesets
					[usize::from(typeset_index)]
				.member_impls
				.clone();

				// The typeset's own `: A + B` clause becomes its backing
				// trait's supertraits — same shape and cycle-forcing as a
				// hand-written `trait X: A + B {}`, `Self` included (e.g.
				// `typeset Int: Add where { Rhs = Self } { ... }`). Members
				// don't get this frame — see below, where they're resolved.
				let self_scope = self.type_envs.push_param_frame(
					&mut self.types,
					TypeEnvOwner::Trait(trait_index),
					TypeEnvIdx::ROOT,
					[Spanned {
						inner: ast::Keyword::SelfPascal.symbol(),
						span: name.span,
					}],
				);
				self.param_bounds.push(Box::new([ParamBounds::empty()]));

				// The Self identity is available while its facts are collected;
				// the surrounding signature query remains in progress.
				self.traits[usize::from(trait_index)] =
					TraitSignature { env: self_scope };
				let subject = self.type_envs.frame(self_scope)[0].ty;
				let (clause_bounds, implied_bounds) = self
					.resolve_subject_bounds(
						file_id,
						namespace,
						self_scope,
						bounds.as_ref(),
						BoundSubject::Param {
							env: self_scope,
							index: 0,
						},
						subject,
						name.inner,
					);
				self.param_bounds[usize::from(self_scope)][0] = ParamBounds {
					declared_bounds: clause_bounds,
					facts: BoundFacts::Ready(implied_bounds.into_boxed_slice()),
				};
				self.traits[usize::from(trait_index)] =
					TraitSignature { env: self_scope };

				// Dispatch already registered each member as a synthetic impl.
				// Resolve its complete type and fill the pre-allocated signature.
				let mut resolved_members = Vec::with_capacity(members.len());
				for (m, &impl_index) in members.iter().zip(member_impls.iter())
				{
					let member_ty = self.resolve_impl_target(
						file_id,
						namespace,
						TypeEnvIdx::ROOT,
						&m.inner.inner,
						self.impl_dispatch.trait_header(impl_index).target,
					);
					let target_spanned = Spanned {
						inner: member_ty,
						span: m.inner.span,
					};
					// No `Self` frame: a typeset member is a concrete type
					// by construction (it's the thing being implemented
					// for), never a context anything else resolves `Self`
					// against — the synthetic impl has no members of its
					// own to write a `Self` reference in either (see the
					// `TypeSetSignature` doc comment).
					self.trait_impls[usize::from(impl_index)] =
						Some(TraitImplSignature {
							type_params: TypeEnvIdx::ROOT,
							target: target_spanned,
							self_scope: TypeEnvIdx::ROOT,
						});
					resolved_members.push(target_spanned);
				}

				self.typesets[usize::from(typeset_index)] = TypeSetSignature {
					members: resolved_members.into_boxed_slice(),
				};
				SignatureLocation::TypeSet(typeset_index)
			}
			_ => todo!("this item kind's signature isn't implemented yet"),
		}
	}

	/// The memory an untagged pointer/slice/array type implicitly belongs
	/// to: the sole `memory` declaration visible to the whole compilation,
	/// if there's exactly one. Zero or several are both errors — there's no
	/// sense in which one memory could be "the" ambient one among several,
	/// and nothing to be ambient at all with none declared. A concrete
	/// memory needs none of its own signature forced to be interned here:
	/// `Type::Memory` carries only `memory_index`, so this is pure identity,
	/// unlike the legacy builder's version (which had to force the size).
	fn resolve_ambient_memory(
		&mut self,
		file_id: FileId,
		span: TextSpan,
	) -> Result<TypeIndex, ()> {
		match self.defs.memories.len() {
			0 => {
				self.diagnostics
					.push(report_no_memory_for_pointer(file_id, span));
				Err(())
			}
			1 => {
				let memory_index = MemoryIdx::new(0);
				Ok(self.types.intern(Type::Memory { memory_index }))
			}
			_ => {
				self.diagnostics
					.push(report_ambiguous_pointer_memory(file_id, span));
				Err(())
			}
		}
	}

	/// Resolves a memory tag's own path (`heap` in `heap::*u8`) to the
	/// concrete memory it names. This doesn't go through `resolve_type`'s
	/// own `Path` arm — that arm resolves a full `Spanned<TypeExpression>`,
	/// and a memory tag is a bare `&[ast::PathSegment]` with no such node
	/// to hand it (`TypeExpression` isn't `Clone`, so there's no cheap way
	/// to wrap it into one either) — so this walks the path directly. Only
	/// a concrete memory is accepted for now; tagging by a generic `M:
	/// Memory` type parameter is a separate, deferred feature.
	fn resolve_memory_tag(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		segments: &[ast::PathSegment],
	) -> Result<TypeIndex, ()> {
		let walk = PathResolver::new(self.defs).walk_path(
			self.diagnostics,
			self.strings,
			file_id,
			namespace,
			segments,
			BindingNamespace::Type,
		);
		let Some(def_key) = walk.target.def_key() else {
			return Err(());
		};
		match def_key.symbol_kind(self.defs) {
			DefKind::Memory(memory_index) => {
				Ok(self.types.intern(Type::Memory { memory_index }))
			}
			kind => {
				let stopped = &segments[walk.stopped_at as usize];
				self.diagnostics.push(report_not_a_memory(
					file_id,
					self.strings,
					stopped.ident,
					kind,
				));
				Err(())
			}
		}
	}

	/// The memory a pointer/slice/array type belongs to — an explicit
	/// `heap::` tag if it has one, the ambient one otherwise. Shared by
	/// `Pointer`/`Slice`/`Array`'s three arms in `resolve_type`, which
	/// otherwise differ only in which `Type` variant they intern.
	fn resolve_pointer_memory(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		memory: &Option<Box<[ast::PathSegment]>>,
		span: TextSpan,
	) -> Result<TypeIndex, ()> {
		match memory {
			Some(segments) => {
				self.resolve_memory_tag(file_id, namespace, segments)
			}
			None => self.resolve_ambient_memory(file_id, span),
		}
	}

	/// Resolve a written signature type and normalize the result. `_` follows
	/// the caller's inference policy; nominal types retain their structure.
	fn resolve_type(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		env: TypeEnvIdx,
		type_expr: &Spanned<ast::TypeExpression>,
		infer_policy: InferPolicy,
	) -> TypeIndex {
		let ty = self.resolve_type_expression(
			file_id,
			namespace,
			env,
			type_expr,
			infer_policy,
		);
		self.normalize_type(ty, SourceSpan::new(file_id, type_expr.span))
	}

	/// Resolve identities and structure without reducing the resulting type.
	/// Member lookup can still normalize a receiver when needed to discover a
	/// member, but stored equality expressions retain symbolic projections.
	fn resolve_type_expression(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		env: TypeEnvIdx,
		type_expr: &Spanned<ast::TypeExpression>,
		infer_policy: InferPolicy,
	) -> TypeIndex {
		match &type_expr.inner {
			ast::TypeExpression::Infer => match infer_policy {
				InferPolicy::Allow => TypeIndex::INFER,
				InferPolicy::Reject(kind) => {
					self.diagnostics.push(report_infer_in_signature(
						file_id,
						type_expr.span,
						kind,
					));
					TypeIndex::ERROR
				}
			},
			ast::TypeExpression::Path(segments) => {
				// The first segment tries `TypeEnv` regardless of how many
				// segments follow — `Self::Value`/`T::Size` never touch the
				// namespace graph at all for their own first hop, same as a
				// bare `T`/`Self` doesn't. Only once that fails does the
				// namespace graph get a turn. Either branch leaves `next`
				// at the first segment *not yet* consumed.
				let first = &segments[0];
				let (current, next) = if first.type_args.is_empty()
					&& let Some(ty) = self.type_envs.resolve(
						env,
						first.ident.inner,
						SourceSpan::new(file_id, first.ident.span),
					) {
					(ty, 1)
				} else {
					let walk = PathResolver::new(self.defs).walk_path(
						self.diagnostics,
						self.strings,
						file_id,
						namespace,
						segments,
						BindingNamespace::Type,
					);
					let Some(def_key) = walk.target.def_key() else {
						return TypeIndex::ERROR;
					};
					let stopped = &segments[walk.stopped_at as usize];

					let resolved = match def_key.symbol_kind(self.defs) {
						DefKind::TypeAlias(type_alias_index) => {
							let def_id = self.defs.type_aliases
								[usize::from(type_alias_index)]
							.def_id;
							let reference =
								SourceSpan::new(file_id, stopped.ident.span);
							let status = self.ensure_signature(QueryInfo {
								def_id,
								requested_at: Some(reference),
							});
							match status {
								SignatureStatus::Cycle => {
									let diagnostic = self
										.report_cyclic_type_alias(
											def_id, reference,
										);
									self.diagnostics.push(diagnostic);
									TypeIndex::ERROR
								}
								SignatureStatus::CycleReported => {
									TypeIndex::ERROR
								}
								SignatureStatus::Resolved(
									SignatureLocation::TypeAlias(index),
								) => {
									self.type_aliases[usize::from(index)].target
								}
								SignatureStatus::Resolved(_) => unreachable!(
									"a TypeAlias DefId always resolves to SignatureLocation::TypeAlias"
								),
							}
						}
						DefKind::Struct(struct_index) => {
							// Only forces resolution for a genuine forward
							// reference (`Pending`); an in-progress struct
							// is left alone so `check_struct_direct_recursion`
							// downstream still gets to observe `Cycle`
							// itself. Either way `type_params` (written
							// before fields, see `RecordStruct`/
							// `TupleStruct` above) is already valid to
							// read by the time we get here.
							let def_id = self.defs.structs
								[usize::from(struct_index)]
							.def_id;
							if matches!(
								self.query_state[&def_id].state,
								QueryState::Pending
							) {
								let _ = self.ensure_signature(QueryInfo {
									def_id,
									requested_at: Some(SourceSpan::new(
										file_id,
										stopped.ident.span,
									)),
								});
							}
							let params_env = self.structs
								[usize::from(struct_index)]
							.type_params;

							let resolved_args: Box<[Spanned<TypeIndex>]> =
								stopped
									.type_args
									.iter()
									.map(|arg| Spanned {
										inner: self.resolve_type_expression(
											file_id,
											namespace,
											env,
											arg,
											infer_policy,
										),
										span: arg.span,
									})
									.collect();
							let type_args = self.resolve_type_args(
								file_id,
								stopped.ident.span,
								params_env,
								&resolved_args,
								TypeEnvOwner::Struct(struct_index),
							);

							self.types.intern(Type::Struct {
								struct_index,
								type_args,
							})
						}
						DefKind::Enum(_) => todo!(
							"resolving a path to an enum isn't implemented yet"
						),
						// A bare memory name in type position — unusual (its
						// only real use is as a memory tag's prefix, e.g.
						// `heap::*u8`, which resolves through
						// `resolve_memory_tag` instead), but well-defined:
						// every `memory` declaration is its own nominal type
						// constructor, same as a struct or enum.
						DefKind::Memory(memory_index) => {
							self.types.intern(Type::Memory { memory_index })
						}
						kind @ (DefKind::Module(_)
						| DefKind::Package(_)
						| DefKind::Import(_)
						| DefKind::Trait(_)
						| DefKind::TypeSet(_)) => {
							self.diagnostics.push(report_not_a_type(
								file_id,
								self.strings,
								stopped.ident,
								kind,
							));
							TypeIndex::ERROR
						}
						// Value-tier only — a `BindingNamespace::Type` walk
						// can never stop on one of these.
						DefKind::EnumVariant(_)
						| DefKind::Global(_)
						| DefKind::Function(_)
						| DefKind::Const(_) => unreachable!(
							"value-tier DefKind from a type-namespace path walk"
						),
						// Never constructed anywhere — associated types are
						// only ever reached through `resolve_type_member`'s
						// own `MemberKind::AssociatedType`, never as a
						// top-level namespace symbol.
						DefKind::TraitAssocType(_) => unreachable!(
							"TraitAssocType is never registered as a namespace symbol"
						),
					};

					(resolved, walk.stopped_at as usize + 1)
				};

				// Whatever's left continues through impl dispatch or a
				// bound instead of the namespace graph — `members.rs`'s
				// job, not this module's.
				self.resolve_type_member_path(
					file_id,
					current,
					&segments[next..],
				)
			}
			ast::TypeExpression::Grouped { inner, segments } => {
				// `<T>::Item` — no namespace-tier prefix to consume first
				// (unlike `Path`'s `T::Item`, where `T` might itself be a
				// multi-segment namespace path): `inner` is already a full
				// type expression, so the member walk starts on it directly.
				let current = self.resolve_type_expression(
					file_id,
					namespace,
					env,
					inner,
					infer_policy,
				);
				self.resolve_type_member_path(file_id, current, segments)
			}
			ast::TypeExpression::QualifiedPath { root, segments } => {
				let base_ty = self.resolve_type_expression(
					file_id,
					namespace,
					env,
					&root.self_type,
					infer_policy,
				);
				if base_ty == TypeIndex::ERROR {
					return TypeIndex::ERROR;
				}
				let Some(required_trait) = self.resolve_trait_bound_path(
					file_id,
					namespace,
					&root.trait_path,
				) else {
					return TypeIndex::ERROR;
				};

				// Only the first segment is ever trait-qualified — it pins
				// down *which* trait provides that one name; everything
				// after it is projected off whatever that named, same as
				// `Grouped`/`Path`, through the ordinary
				// `resolve_type_member_path`.
				let first = &segments[0];
				if !first.type_args.is_empty() {
					todo!(
						"generic args on a type-relative path segment aren't implemented yet"
					)
				}
				let Ok(member) = self.resolve_trait_qualified_member(
					base_ty,
					required_trait,
					BindingNamespace::Type,
					first.ident,
					file_id,
				) else {
					return TypeIndex::ERROR;
				};
				let current = self.project_type_member(base_ty, member);

				self.resolve_type_member_path(file_id, current, &segments[1..])
			}
			ast::TypeExpression::Function { params, result } => {
				let mut param_types = Vec::with_capacity(params.len());
				for param in params.iter() {
					param_types.push(self.resolve_type_expression(
						file_id,
						namespace,
						env,
						&param.inner.inner.ty,
						infer_policy,
					));
				}
				let result_type = match result {
					Some(result) => self.resolve_type_expression(
						file_id,
						namespace,
						env,
						result,
						infer_policy,
					),
					None => TypeIndex::UNIT,
				};
				self.types.intern(Type::Function {
					params: param_types.into_boxed_slice(),
					result: result_type,
				})
			}
			ast::TypeExpression::Pointer {
				ownership,
				memory,
				inner,
			} => {
				let to = self.resolve_type_expression(
					file_id,
					namespace,
					env,
					inner,
					infer_policy,
				);
				let Ok(memory) = self.resolve_pointer_memory(
					file_id,
					namespace,
					memory,
					type_expr.span,
				) else {
					return TypeIndex::ERROR;
				};
				self.types.intern(Type::Pointer {
					to,
					memory,
					ownership: *ownership,
				})
			}
			ast::TypeExpression::Slice {
				ownership,
				memory,
				inner,
			} => {
				let of = self.resolve_type_expression(
					file_id,
					namespace,
					env,
					inner,
					infer_policy,
				);
				let Ok(memory) = self.resolve_pointer_memory(
					file_id,
					namespace,
					memory,
					type_expr.span,
				) else {
					return TypeIndex::ERROR;
				};
				self.types.intern(Type::Slice {
					of,
					memory,
					ownership: *ownership,
				})
			}
			ast::TypeExpression::Array {
				ownership,
				memory,
				inner,
				size,
			} => {
				let of = self.resolve_type_expression(
					file_id,
					namespace,
					env,
					inner,
					infer_policy,
				);
				let Ok(memory) = self.resolve_pointer_memory(
					file_id,
					namespace,
					memory,
					type_expr.span,
				) else {
					return TypeIndex::ERROR;
				};
				self.types.intern(Type::Array {
					of,
					size: size.inner as u32,
					memory,
					ownership: *ownership,
				})
			}
			ast::TypeExpression::Tuple { elements } => {
				if elements.is_empty() {
					return TypeIndex::UNIT;
				}
				let mut elems: Vec<TypeIndex> =
					Vec::with_capacity(elements.len());
				for element in elements.iter() {
					elems.push(self.resolve_type_expression(
						file_id,
						namespace,
						env,
						element,
						infer_policy,
					));
				}
				self.types.intern(Type::Tuple {
					elements: elems.into_boxed_slice(),
				})
			}
			_ => todo!("this type-expression form isn't implemented yet"),
		}
	}

	/// Builds the diagnostic for a cycle just detected while trying to
	/// re-enter `def_id` (found `InProgress` somewhere on `query_stack`).
	/// Mirrors rustc's E0391 structure: walks the stack from `def_id`'s own
	/// frame to the top, and for hop `i` shows the span of the *next*
	/// frame's `requested_at` — i.e. the reference inside hop `i`'s own body
	/// that demanded the next item, the same "attach the span to the query
	/// it justifies" shape `rustc_query_system::QueryInfo` uses. The one
	/// edge with no frame of its own is the closing one (re-entering
	/// `def_id`), since that call never got to push anything — the caller
	/// already has that span in hand at the point it detects `Cycle`, so it
	/// passes it in directly as `closing_reference`.
	///
	/// Shared by every cycle kind (`CyclicTypeAlias`, `CyclicTraitBounds`,
	/// `RecursiveTypeWithoutIndirection`, ...) — they differ only in which
	/// diagnostic code applies and how to phrase "why `name` was needed"
	/// (`describe`), e.g. `"expanding type alias \`A\`"` or `"computing the
	/// supertraits of \`A\`"`. Callers append their own closing notes on top
	/// of the returned diagnostic.
	fn report_cycle(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
		code: DiagnosticCode,
		describe: impl Fn(&str) -> String,
	) -> Diagnostic<FileId> {
		let position = self
			.query_stack
			.iter()
			.position(|frame| frame.def_id == def_id)
			.expect(
				"Cycle is only ever returned for a query currently in progress",
			);
		let chain = &self.query_stack[position..];

		let hop_span = |i: usize| -> SourceSpan {
			chain
				.get(i + 1)
				.map(|frame| {
					frame.requested_at.expect(
						"a non-root frame always records why it was required",
					)
				})
				.unwrap_or(closing_reference)
		};

		let root_name =
			item_name(self.ast_nodes, self.query_state[&def_id].ast_index);
		let root_name_str = self.strings.resolve(root_name.inner).unwrap();

		let mut diagnostic = Diagnostic::error()
			.with_code(code.code())
			.with_message(format!(
				"cycle detected when {}",
				describe(root_name_str)
			))
			.with_label(hop_span(0).primary_label());

		for (i, frame) in chain.iter().enumerate().skip(1) {
			let name = item_name(
				self.ast_nodes,
				self.query_state[&frame.def_id].ast_index,
			);
			let name_str = self.strings.resolve(name.inner).unwrap();
			diagnostic = diagnostic.with_label(
				hop_span(i).secondary_label().with_message(format!(
					"...which requires {}...",
					describe(name_str)
				)),
			);
		}

		diagnostic.with_note(format!(
			"...which again requires {}, completing the cycle",
			describe(root_name_str)
		))
	}

	fn report_cyclic_type_alias(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
	) -> Diagnostic<FileId> {
		self.report_cycle(
			def_id,
			closing_reference,
			DiagnosticCode::CyclicTypeAlias,
			|name| format!("expanding type alias `{name}`"),
		)
		.with_note("type aliases cannot be recursive")
		.with_note(
			"consider a struct or enum with a pointer field instead, to break the cycle",
		)
	}

	fn report_cyclic_supertrait(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
	) -> Diagnostic<FileId> {
		self.report_cycle(
			def_id,
			closing_reference,
			DiagnosticCode::CyclicTraitBounds,
			|name| format!("computing the supertraits of `{name}`"),
		)
		.with_note("a trait cannot require itself as a supertrait")
	}

	pub(super) fn report_cyclic_implied_trait_bounds(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
	) -> Diagnostic<FileId> {
		self.report_cycle(
			def_id,
			closing_reference,
			DiagnosticCode::CyclicTraitBounds,
			|name| format!("computing the implied bounds of `{name}`"),
		)
	}

	/// Same family as `report_cyclic_implied_trait_bounds` — a trait
	/// associated type's own declared bound (`type Size: PointerSize`)
	/// closed a cycle while being forced, e.g. by
	/// `members::ensure_assoc_type_bounds`.
	pub(super) fn report_cyclic_assoc_type_bound(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
	) -> Diagnostic<FileId> {
		self.report_cycle(
			def_id,
			closing_reference,
			DiagnosticCode::CyclicTraitBounds,
			|name| format!("computing the bound of associated type `{name}`"),
		)
	}

	/// Renders the rustc-E0072-style diagnostic: every struct in the cycle
	/// gets its own primary label (at its own declaration name) plus a
	/// secondary label at the specific field that continues the cycle,
	/// rather than the single-root "cycle detected when..." chain
	/// `report_cycle` renders for `CyclicTypeAlias`/`CyclicTraitBounds`. The
	/// full chain is already sitting in `query_stack[position..]` — built up
	/// by the ordinary recursive `ensure_signature` forcing that got us
	/// here — so there's nothing to separately collect first.
	fn report_recursive_struct_cycle(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
	) -> Diagnostic<FileId> {
		let position = self
			.query_stack
			.iter()
			.position(|frame| frame.def_id == def_id)
			.expect(
				"Cycle is only ever returned for a query currently in progress",
			);
		let chain = &self.query_stack[position..];

		let hop_span = |i: usize| -> SourceSpan {
			chain
				.get(i + 1)
				.map(|frame| {
					frame.requested_at.expect(
						"a non-root frame always records why it was required",
					)
				})
				.unwrap_or(closing_reference)
		};

		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::RecursiveTypeWithoutIndirection.code());
		let mut names = Vec::with_capacity(chain.len());
		for (i, frame) in chain.iter().enumerate() {
			let ast_index = self.query_state[&frame.def_id].ast_index;
			let file_id = self.ast_nodes[ast_index as usize].file_id;
			let name = item_name(self.ast_nodes, ast_index);
			names.push(self.strings.resolve(name.inner).unwrap());
			diagnostic = diagnostic
				.with_label(SourceSpan::new(file_id, name.span).primary_label())
				.with_label(
					hop_span(i)
						.secondary_label()
						.with_message("recursive without indirection"),
				);
		}

		let message = match names.as_slice() {
			[] => unreachable!("a cycle always has at least one participant"),
			[only] => format!("recursive type `{only}` has infinite size"),
			[rest @ .., last] => {
				let joined = rest
					.iter()
					.map(|n| format!("`{n}`"))
					.collect::<Vec<_>>()
					.join(", ");
				format!(
					"recursive types {joined} and `{last}` have infinite size"
				)
			}
		};

		diagnostic
			.with_message(message)
			.with_note("insert a pointer or slice field to break the cycle")
	}

	/// One element of a resolved `Type::Tuple`, re-resolving `ty` fresh
	/// rather than holding onto a borrowed slice — lets
	/// `check_struct_direct_recursion` iterate elements without cloning the
	/// whole `Box<[TypeIndex]>` just to sidestep borrowing `self.types`
	/// across its own recursive (`&mut self`) call.
	fn tuple_element(&self, ty: TypeIndex, index: usize) -> TypeIndex {
		let Type::Tuple { elements } = self.types.resolve(ty) else {
			unreachable!("only called when ty is already known to be a Tuple")
		};
		elements[index]
	}

	/// Walks `ty` for directly-embedded (non-indirected) struct references —
	/// `Type::Struct`/`Type::Tuple` embed inline and are followed;
	/// `Type::Pointer`/`Slice`/`Array` always carry their own memory +
	/// ownership sigil and live out-of-line, so the walk stops there. Each
	/// struct reference found is *forced* via `ensure_signature` — reusing
	/// the exact same demand-driven cycle detection every other kind in this
	/// file already has, rather than a separate visited-set walk: if that
	/// forcing call returns `Cycle`, this reports it via
	/// `report_recursive_struct_cycle`, which reads the full chain straight
	/// out of `query_stack`.
	///
	/// `args` is ignored entirely — a generic struct's own type arguments
	/// are never substituted into its fields here, so
	/// `struct Wrapper<T> { v: T } struct A { w: Wrapper<A> }` isn't
	/// caught. That's sound, not just incomplete: ignoring substitution can
	/// only remove edges from the graph being walked, never invent one, so
	/// this can under-detect but never falsely flag a cycle. Catching that
	/// case needs `params_in_repr`-style type-parameter substitution
	/// utilities that don't exist yet — deliberately deferred, not
	/// forgotten.
	fn check_struct_direct_recursion(
		&mut self,
		file_id: FileId,
		field_span: TextSpan,
		ty: TypeIndex,
	) {
		match self.types.resolve(ty) {
			Type::Struct { struct_index, .. } => {
				let embedded_def_id =
					self.defs.structs[usize::from(*struct_index)].def_id;
				let reference = SourceSpan::new(file_id, field_span);
				let status = self.ensure_signature(QueryInfo {
					def_id: embedded_def_id,
					requested_at: Some(reference),
				});
				if let SignatureStatus::Cycle = status {
					let diagnostic = self.report_recursive_struct_cycle(
						embedded_def_id,
						reference,
					);
					self.diagnostics.push(diagnostic);
				}
			}
			Type::Tuple { elements } => {
				let len = elements.len();
				for i in 0..len {
					let element = self.tuple_element(ty, i);
					self.check_struct_direct_recursion(
						file_id, field_span, element,
					);
				}
			}
			_ => {}
		}
	}

	fn resolve_subject_bounds(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		env: TypeEnvIdx,
		bound: Option<&Spanned<ast::BoundExpression>>,
		location: BoundSubject,
		subject: TypeIndex,
		name: SymbolU32,
	) -> (Box<[BoundId]>, Vec<ImpliedTraitBound>) {
		let mut occurrences = Vec::new();
		let has_equalities = bound.is_some_and(|bound| {
			self.collect_bound_occurrences(
				file_id,
				namespace,
				bound,
				&mut occurrences,
			)
		});
		let memberships = provisional_from_occurrences(&occurrences);
		if matches!(location, BoundSubject::Param { .. })
			&& matches!(self.type_envs.frame_owner(env), TypeEnvOwner::Trait(_))
		{
			for occurrence in &occurrences {
				let def_id = self.defs.traits
					[usize::from(occurrence.trait_index)]
				.def_id;
				let reference = occurrence.span;
				if let SignatureStatus::Cycle =
					self.ensure_signature(QueryInfo {
						def_id,
						requested_at: Some(reference),
					}) {
					let diagnostic =
						self.report_cyclic_supertrait(def_id, reference);
					self.diagnostics.push(diagnostic);
				}
			}
		}
		let memberships = if has_equalities {
			self.merge_implied_memberships(memberships, subject)
		} else {
			memberships
		}
		.into_boxed_slice();
		match location {
			BoundSubject::Param { env, index } => {
				self.param_bounds[usize::from(env)][index].facts =
					BoundFacts::Provisional(memberships)
			}
			BoundSubject::Assoc(index) => {
				self.assoc_types[usize::from(index)] =
					Some(AssocTypeSignature {
						declared_bounds: Box::new([]),
						facts: BoundFacts::Provisional(memberships),
						value: None,
					})
			}
		}
		let ids = self.resolve_source_bounds_from(
			file_id,
			namespace,
			env,
			&occurrences,
		);
		let implied = self.compute_implied_bounds(&ids, name, subject);
		(ids.into_boxed_slice(), implied)
	}

	/// Walks a bound expression exactly once, resolving trait paths,
	/// reserving a `BoundId` per accepted occurrence, and reporting the
	/// "not an associated type"/duplicate-binding diagnostics. The result is
	/// consumed twice — once by `provisional_from_occurrences` to publish
	/// direct memberships (no equality RHS types resolved), once by
	/// `resolve_source_bounds_from` to resolve those RHS types and fill in
	/// `self.bounds` — but which occurrences exist, and which bindings on
	/// them are accepted, is decided exactly once, here. The two former
	/// consumers used to re-walk the raw AST independently and could only be
	/// proven to agree by comparing how many `BoundId`s each had reserved;
	/// walking a shared `BoundOccurrence` tree instead makes that agreement
	/// structural rather than an invariant to maintain by hand.
	/// Returns whether any equality binding (nested ones included) was seen
	/// — the fact `resolve_generic_params`/`resolve_subject_bounds` need to
	/// decide whether `merge_implied_memberships` is worth running at all —
	/// since this walk already visits every binding once and would
	/// otherwise make a caller re-derive the same fact from its output.
	fn collect_bound_occurrences<'expr>(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		expr: &'expr Spanned<ast::BoundExpression>,
		out: &mut Vec<BoundOccurrence<'expr>>,
	) -> bool {
		let (segments, bindings) = match &expr.inner {
			ast::BoundExpression::BoundList(list) => {
				let mut has_equalities = false;
				for entry in list.iter() {
					has_equalities |= self.collect_bound_occurrences(
						file_id, namespace, entry, out,
					);
				}
				return has_equalities;
			}
			ast::BoundExpression::Path(segments) => {
				(segments.as_ref(), &[][..])
			}
			ast::BoundExpression::WithBindings { path, bindings } => {
				let ast::BoundExpression::Path(segments) = path.as_ref() else {
					unreachable!("WithBindings.path is always a plain Path")
				};
				(segments.as_ref(), bindings.as_ref())
			}
		};
		let Some(trait_index) =
			self.resolve_trait_bound_path(file_id, namespace, segments)
		else {
			return false;
		};
		let span = SourceSpan::new(file_id, expr.span);
		let id = self.bounds.reserve(trait_index, span);
		let mut occurrence_bindings = Vec::new();
		let mut has_equalities = false;
		for binding in bindings.iter() {
			let Some(assoc_type_index) =
				self.assoc_binding_index(trait_index, binding.name.inner)
			else {
				self.diagnostics.push(report_not_an_associated_type(
					file_id,
					self.strings,
					binding.name,
					self.defs.traits[usize::from(trait_index)].name.inner,
				));
				continue;
			};
			if occurrence_bindings
				.iter()
				.any(|b: &BindingOccurrence<'expr>| {
					b.assoc_type_index == assoc_type_index
				}) {
				self.diagnostics.push(report_duplicate_assoc_type_binding(
					file_id,
					self.strings,
					binding.name,
				));
				continue;
			}
			let kind = match &binding.kind {
				ast::AssocTypeBindingKind::Equals(ty) => {
					has_equalities = true;
					BindingOccurrenceKind::Equals(ty)
				}
				ast::AssocTypeBindingKind::Bound(rhs) => {
					let mut nested = Vec::new();
					has_equalities |= self.collect_bound_occurrences(
						file_id,
						namespace,
						rhs,
						&mut nested,
					);
					BindingOccurrenceKind::Bound(nested)
				}
			};
			occurrence_bindings.push(BindingOccurrence {
				assoc_type_index,
				name: binding.name,
				kind,
			});
		}
		out.push(BoundOccurrence {
			id,
			trait_index,
			span,
			bindings: occurrence_bindings,
		});
		has_equalities
	}

	/// Resolves every equality binding's RHS type and fills `self.bounds` at
	/// each occurrence's already-reserved `BoundId`. Run once every sibling
	/// param has provisional memberships published, so an equality RHS can
	/// reference a sibling's associated types.
	fn resolve_source_bounds_from(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		env: TypeEnvIdx,
		occurrences: &[BoundOccurrence<'_>],
	) -> Vec<BoundId> {
		occurrences
			.iter()
			.map(|occurrence| {
				let mut source_bindings =
					Vec::with_capacity(occurrence.bindings.len());
				for binding in &occurrence.bindings {
					let kind = match &binding.kind {
						BindingOccurrenceKind::Equals(ty) => {
							// Store the resolved expression without reducing
							// its final value. Member lookup may still need
							// to expose a receiver's constructor.
							let value = self.resolve_type_expression(
								file_id,
								namespace,
								env,
								ty,
								InferPolicy::Reject(
									InferSignatureKind::AssocTypeBinding,
								),
							);
							BindingRequirement::Equals(Spanned {
								inner: value,
								span: ty.span,
							})
						}
						BindingOccurrenceKind::Bound(nested) => {
							let nested_ids = self.resolve_source_bounds_from(
								file_id, namespace, env, nested,
							);
							BindingRequirement::Bound(
								nested_ids.into_boxed_slice(),
							)
						}
					};
					source_bindings.push(SourceAssocBinding {
						assoc_type_index: binding.assoc_type_index,
						name: binding.name,
						kind,
					});
				}
				self.bounds.fill(
					occurrence.id,
					SourceTraitBound {
						trait_index: occurrence.trait_index,
						span: occurrence.span,
						bindings: source_bindings.into_boxed_slice(),
					},
				);
				occurrence.id
			})
			.collect()
	}

	fn assoc_binding_index(
		&self,
		trait_index: TraitIdx,
		name: SymbolU32,
	) -> Option<AssocTypeIdx> {
		let trait_def = &self.defs.traits[usize::from(trait_index)];
		let &member_index = trait_def.bindings.get(&BindingKey::ty(name))?;
		match trait_def.members[usize::from(member_index)].kind {
			MemberKind::AssociatedType(index) => Some(index),
			_ => None,
		}
	}

	/// Resolves a bound's own path to the trait it names — shared between a
	/// bare `Trait` bound and `WithBindings`'s left-hand `Trait` part.
	/// `None` if the path failed to resolve to a real trait; already
	/// diagnosed either way, by `resolve_path` itself or by the "expected a
	/// trait" report below.
	fn resolve_trait_bound_path(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		segments: &[ast::PathSegment],
	) -> Option<TraitIdx> {
		let target = PathResolver::new(self.defs).resolve_path(
			self.diagnostics,
			self.strings,
			file_id,
			namespace,
			segments,
			BindingNamespace::Type,
		);
		let def_key = target.def_key()?;
		match def_key.symbol_kind(self.defs) {
			DefKind::Trait(trait_index) => Some(trait_index),
			// A `typeset` bound resolves to its own compiler-generated
			// trait — `typeset_index` (and, through it, `trait_index`) is
			// Phase 1 data, read straight off `defs.rs`'s own output. No
			// forcing needed here for the same reason the `Trait` arm just
			// above doesn't force anything either — see `ast_node`'s own
			// doc comment: this function only answers "which item does
			// this name refer to," not "is its data ready yet," and
			// forcing here would actively break supertrait-cycle
			// reporting (this runs *inside* `collect_bounds`, called
			// while the referencing item's own query is still
			// `InProgress` — forcing here could flip a genuine cycle
			// straight to `CycleReported` before the one call site that
			// can actually report it, `Trait`'s own supertrait-forcing
			// loop, ever gets a turn).
			DefKind::TypeSet(typeset_index) => {
				Some(self.defs.typesets[usize::from(typeset_index)].trait_index)
			}
			other => {
				let last = segments
					.last()
					.expect("a path always has at least one segment");
				self.diagnostics.push(report_not_a_trait_bound(
					file_id,
					self.strings,
					last.ident,
					other,
				));
				None
			}
		}
	}
}

/// The written name of `def_id`'s own declaration — reads Phase 1's prescan
/// record directly, since this needs to work even for an item that hasn't
/// finished resolving yet (a cycle's participants never do), or, in
/// `SignatureBuilder::new`'s primitive pre-pass, before a `SignatureBuilder`
/// exists at all to call a method on.
fn item_name(ast_nodes: &[AstEntry], ast_index: u32) -> Spanned<SymbolU32> {
	match ast_nodes[ast_index as usize].node.clone() {
		AstNodeRef::TypeAlias { item, .. } => {
			let ast::Item::TypeAlias { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::Trait { item, .. } => {
			let ast::Item::Trait { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::RecordStruct { item, .. } => {
			let ast::Item::RecordStruct { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::TupleStruct { item, .. } => {
			let ast::Item::TupleStruct { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::TypeSet { item, .. } => {
			let ast::Item::TypeSet { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::TraitAssocType { item, .. } => {
			let ast::TraitItem::AssociatedType { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::TraitImplAssocType { item, .. } => {
			let ast::ImplItem::AssocType { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::Memory { item, .. } | AstNodeRef::Global { item, .. } => {
			let (ast::Item::Memory { name, .. }
			| ast::Item::Global { name, .. }) = item
			else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::ImportedMemory { decl, .. }
		| AstNodeRef::ImportedGlobal { decl, .. } => {
			let (ast::ImportDeclaration::Memory { name, .. }
			| ast::ImportDeclaration::Global { name, .. }) = decl
			else {
				unreachable!()
			};
			*name
		}
		_ => todo!("naming this item kind isn't implemented yet"),
	}
}

fn report_infer_in_signature(
	file_id: FileId,
	span: TextSpan,
	kind: InferSignatureKind,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InferInSignature.code())
		.with_message(format!(
			"the placeholder `_` is not allowed within types on item signatures for {}",
			kind.noun(),
		))
		.with_label(
			SourceSpan::new(file_id, span)
				.primary_label()
				.with_message("not allowed in type signatures"),
		)
}

fn report_not_a_type(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	kind: DefKind,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotAType.code())
		.with_message(format!(
			"expected type, found {} `{name_str}`",
			kind.noun()
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("not a type"),
		)
}

fn report_not_a_memory(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	kind: DefKind,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotAMemory.code())
		.with_message(format!(
			"expected a memory, found {} `{name_str}`",
			kind.noun()
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("not a memory"),
		)
}

fn report_missing_enum_repr(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingEnumRepr.code())
		.with_message("enum requires a repr type")
		.with_label(
			SourceSpan::new(file_id, span)
				.primary_label()
				.with_message("add `: <type>` here"),
		)
}

fn report_missing_type_alias_body(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingTypeAliasBody.code())
		.with_message("free type alias without body")
		.with_label(
			SourceSpan::new(file_id, span)
				.primary_label()
				.with_message("provide a definition for the type: `= <type>;`"),
		)
}

fn report_enum_repr_not_integer(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::EnumReprNotInteger.code())
		.with_message("enum repr type must be an integer type")
		.with_label(
			SourceSpan::new(file_id, span)
				.primary_label()
				.with_message("not an integer type"),
		)
}

fn report_duplicate_generic_param(
	strings: &StringInterner,
	file_id: FileId,
	name: Spanned<SymbolU32>,
	first: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateGenericParam.code())
		.with_message(format!("the name `{name_str}` is already used for a generic parameter in this item's generic parameters"))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("already used"),
		)
		.with_label(
			SourceSpan::new(file_id, first.span)
				.secondary_label()
				.with_message(format!("first use of `{name_str}`")),
		)
}

fn report_duplicate_function_param(
	strings: &StringInterner,
	file_id: FileId,
	name: Spanned<SymbolU32>,
	first: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateDefinition.code())
		.with_message(format!(
			"identifier `{name_str}` is bound more than once in this parameter list"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
		.with_label(
			SourceSpan::new(file_id, first.span)
				.secondary_label()
				.with_message(format!(
					"first use of `{name_str}` as a parameter"
				)),
		)
}

fn report_missing_parameter_type(
	strings: &StringInterner,
	file_id: FileId,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingParameterType.code())
		.with_message(format!(
			"parameter `{name_str}` requires an explicit type"
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("expected `: Type` here"),
		)
}

/// Same wording as rustc's own `missing type for \`const\` item` message.
/// No suggested type yet, unlike rustc's `help:` — worth adding once this
/// architecture can infer one from the value expression.
fn report_missing_global_type(
	file_id: FileId,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingGlobalType.code())
		.with_message("missing type for `global` item")
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}

fn report_no_memory_for_pointer(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::NoMemoryForPointer.code())
		.with_message("a pointer type requires a linear memory")
		.with_label(SourceSpan::new(file_id, span).primary_label())
		.with_note("declare a memory in this module: `memory <name>: u32;`")
}

fn report_ambiguous_pointer_memory(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousPointerMemory.code())
		.with_message(
			"pointer type is ambiguous: multiple memories are declared",
		)
		.with_label(SourceSpan::new(file_id, span).primary_label())
		.with_note("specify which memory with `<memory_name>::*T` syntax")
}

#[cfg(test)]
pub(super) mod tests {
	use indoc::indoc;

	use super::*;
	use crate::testing::DiagnosticView;
	use crate::tir::defs::DefinitionRegistry;
	use crate::tir::impls::ImplTarget;
	use crate::vfs;

	/// Stops before the signature sweep so tests can exercise demand order.
	pub(in crate::tir) fn with_pending_signatures(
		source: &str,
		check: impl FnOnce(&mut SignatureBuilder<'_, '_>),
	) {
		let mut builder = vfs::CompilationUnitBuilder::new();
		let root = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					source.to_string(),
				)])),
			)
			.unwrap();
		builder.set_stdlib(root);
		let mut graph = builder.build(root);
		DiagnosticView::new(
			"parse",
			&graph.collect_parser_diagnostics(),
			&graph.files,
		)
		.assert_no_errors();
		DiagnosticView::new(
			"link",
			&graph.collect_linker_diagnostics(),
			&graph.files,
		)
		.assert_no_errors();
		let mut diagnostics = Vec::new();
		let (defs, ast_nodes) = DefinitionRegistry::build(
			&graph.packages,
			&graph.files,
			&mut graph.strings,
			&mut diagnostics,
			graph.stdlib_package,
			graph.root_package,
		);
		let dispatch = ImplDispatch::build(
			&mut diagnostics,
			&graph.strings,
			&defs,
			&ast_nodes,
		);
		DiagnosticView::new("prescan/dispatch", &diagnostics, &graph.files)
			.assert_none();
		check(&mut SignatureBuilder::new(
			&mut diagnostics,
			&graph.strings,
			&defs,
			&ast_nodes,
			dispatch,
		));
	}

	fn pending_provider(
		builder: &mut SignatureBuilder<'_, '_>,
		receiver: TypeIndex,
		name: &str,
	) -> (AssocTypeIdx, AssocTypeProvider, SourceSpan) {
		use crate::tir::members::{MemberSource, TypeMemberLookup};
		let file_id = builder.defs.namespaces
			[usize::from(builder.defs.root_package.root_namespace())]
		.file_id;
		let reference = SourceSpan::new(file_id, TextSpan::new(0, 1));
		let name = builder.strings.get(name).unwrap();
		let TypeMemberLookup::Found(member) = builder.resolve_type_member(
			receiver,
			BindingNamespace::Type,
			name,
			reference,
		) else {
			panic!("expected one associated type");
		};
		let MemberKind::AssociatedType(declaration) = member.kind else {
			panic!("expected an associated type")
		};
		let MemberSource::TraitImpl(trait_index, impl_index) = member.source
		else {
			panic!("expected an impl override")
		};
		let qualified = builder
			.resolve_trait_qualified_member(
				receiver,
				trait_index,
				BindingNamespace::Type,
				Spanned {
					inner: name,
					span: reference.span,
				},
				file_id,
			)
			.unwrap();
		assert!(
			matches!(qualified.kind, MemberKind::AssociatedType(index) if index == declaration)
		);
		let projection = builder.project_type_member(receiver, member);
		assert!(
			matches!(builder.types.resolve(projection), Type::AssocTypeProjection { assoc_type_index, .. } if *assoc_type_index == declaration)
		);
		let provider = builder
			.assoc_type_provider(impl_index, declaration)
			.unwrap();
		assert_ne!(declaration, provider.index());
		assert!(matches!(
			builder.ast_node(
				builder.defs.assoc_types[usize::from(declaration)].def_id
			),
			AstNodeRef::TraitAssocType { .. }
		));
		let provider_def_id =
			builder.defs.assoc_types[usize::from(provider.index())].def_id;
		assert!(matches!(
			builder.query_state[&provider_def_id].state,
			QueryState::Pending
		));
		assert!(builder.assoc_types[usize::from(provider.index())].is_none());
		(declaration, provider, reference)
	}

	/// Drives the real pipeline — parse, prescan, resolve — and keeps only
	/// what a test needs to check afterward. `defs` and `ast_nodes` are local
	/// to `new` itself: once `ensure_all_signatures` has run, `finish()`
	/// hands back an owned `SignatureRegistry` with no lifetime tied to the
	/// AST, which is the only thing worth carrying forward.
	struct TestCase {
		graph: vfs::CompilationUnit,
		defs: DefinitionRegistry,
		diagnostics: Vec<Diagnostic<FileId>>,
		signatures: SignatureRegistry,
	}

	impl TestCase {
		/// `source` plays the stdlib's own role (`set_stdlib`, the same
		/// mechanism a real `"type": "std"` package uses) instead of loading
		/// the real ~250-line embedded stdlib: `ensure_all_signatures` isn't
		/// selective about which item kinds it drives, so any real stdlib
		/// content — including item kinds and members whose signatures are
		/// not implemented yet — would panic before a test even runs. A test
		/// that needs a primitive declares its own bodiless `pub type i32;` — no
		/// `#[intrinsic]` marker required, recognition is implicit for a
		/// reserved name declared in whichever package is `stdlib_package`
		/// (see `defs.rs`'s own doc comment on `intrinsics`) — so this still
		/// works the same way it would for the real thing.
		fn new(source: &str) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			let root_id = builder
				.load_binary(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(
						std::collections::HashMap::from([(
							"main.wx".to_string(),
							source.to_string(),
						)]),
					),
				)
				.unwrap();
			builder.set_stdlib(root_id);
			let mut graph = builder.build(root_id);

			let mut diagnostics = Vec::new();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				graph.stdlib_package,
				graph.root_package,
			);

			let signatures = SignatureRegistry::build(
				&mut diagnostics,
				&graph.strings,
				&defs,
				&ast_nodes,
			);

			TestCase {
				graph,
				defs,
				diagnostics,
				signatures,
			}
		}

		/// Resolves `name` as a type-position path from the root namespace —
		/// the same mechanism a written bound or type actually uses to mean
		/// "this name" — `path` is `::`-separated, so a nested item (`mod
		/// inner; ... inner::Foo`) can be named too, not just a root-level
		/// one. A linear scan over `defs.traits`/`.type_aliases` would find
		/// *an* item with that spelling anywhere in the whole compilation,
		/// not necessarily the one this namespace's rules would actually
		/// pick, so path resolution is what decides the `DefKind` here, same
		/// as production code. Diagnostics from the lookup itself are
		/// discarded — a path a test asks for is always expected to resolve
		/// cleanly, so any diagnostic here would only ever be a bug in the
		/// test, not something worth asserting on.
		fn resolve(&self, ns: BindingNamespace, path: &str) -> DefKind {
			let root = self.defs.root_package.root_namespace();
			let file_id = self.defs.namespaces[usize::from(root)].file_id;

			let segments: Box<[ast::PathSegment]> = path
				.split("::")
				.map(|segment| ast::PathSegment {
					ident: Spanned {
						inner: self
							.graph
							.strings
							.get(segment)
							.expect("already interned from source"),
						span: TextSpan::new(0, 0),
					},
					type_args: Box::new([]),
				})
				.collect();
			let mut scratch = Vec::new();
			let target = PathResolver::new(&self.defs).resolve_path(
				&mut scratch,
				&self.graph.strings,
				file_id,
				root,
				&segments,
				ns,
			);
			let def_key = target.def_key().unwrap_or_else(|| {
				panic!("expected `{path}` to resolve: {scratch:?}")
			});
			def_key.symbol_kind(&self.defs)
		}

		fn trait_index(&self, path: &str) -> TraitIdx {
			let DefKind::Trait(trait_index) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a trait");
			};
			trait_index
		}

		/// The written clause excludes the implicit `Self: ThisTrait` bound.
		fn trait_supertraits(&self, path: &str) -> Vec<&SourceTraitBound> {
			let env =
				self.signatures.traits[usize::from(self.trait_index(path))].env;
			self.signatures.param_bounds[usize::from(env)][0]
				.declared_bounds
				.iter()
				.map(|&id| self.signatures.bounds.get(id))
				.collect()
		}

		fn typeset_index(&self, path: &str) -> TypesetIdx {
			let DefKind::TypeSet(typeset_index) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a typeset");
			};
			typeset_index
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"siganture",
				&self.diagnostics,
				&self.graph.files,
			)
		}

		fn typeset_signature(&self, path: &str) -> &TypeSetSignature {
			&self.signatures.typesets[usize::from(self.typeset_index(path))]
		}

		/// The `TraitIndex` of `path`'s compiler-generated backing trait —
		/// what a `T: <path>` bound actually resolves to.
		fn typeset_trait_index(&self, path: &str) -> TraitIdx {
			self.defs.typesets[usize::from(self.typeset_index(path))]
				.trait_index
		}

		/// See `trait_supertraits` — only the written clause.
		fn typeset_supertraits(&self, path: &str) -> Vec<&SourceTraitBound> {
			let env = self.signatures.traits
				[usize::from(self.typeset_trait_index(path))]
			.env;
			self.signatures.param_bounds[usize::from(env)][0]
				.declared_bounds
				.iter()
				.map(|&id| self.signatures.bounds.get(id))
				.collect()
		}

		/// `name` is looked up directly against the trait's own member
		/// bindings rather than through `resolve` — `Trait::Assoc` isn't a
		/// resolvable path yet.
		fn assoc_type_signature(
			&self,
			trait_path: &str,
			name: &str,
		) -> &AssocTypeSignature {
			let trait_index = self.trait_index(trait_path);
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("already interned from source");
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			let &member_index = trait_def
				.bindings
				.get(&BindingKey::ty(symbol))
				.unwrap_or_else(|| {
					panic!(
						"expected `{trait_path}` to have an associated type `{name}`"
					)
				});
			let member = &trait_def.members[usize::from(member_index)];
			let MemberKind::AssociatedType(index) = member.kind else {
				panic!("expected `{name}` to be an associated type");
			};
			self.signatures.assoc_types[usize::from(index)]
				.as_ref()
				.expect("trait associated type signature is resolved")
		}

		/// Same reasoning as `assoc_type_signature` — trait members aren't
		/// path-resolvable yet, so this looks the member up directly
		/// against the trait's own bindings.
		fn trait_function_signature(
			&self,
			trait_path: &str,
			name: &str,
		) -> &FunctionSignature {
			let trait_index = self.trait_index(trait_path);
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("already interned from source");
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			let &member_index = trait_def
				.bindings
				.get(&BindingKey::value(symbol))
				.unwrap_or_else(|| {
					panic!(
						"expected `{trait_path}` to have a function `{name}`"
					)
				});
			let member = &trait_def.members[usize::from(member_index)];
			let (MemberKind::Function(index) | MemberKind::Method(index)) =
				member.kind
			else {
				panic!("expected `{name}` to be a function");
			};
			&self.signatures.functions[usize::from(index)]
		}

		fn trait_const_signature(
			&self,
			trait_path: &str,
			name: &str,
		) -> &ConstantSignature {
			let trait_index = self.trait_index(trait_path);
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("already interned from source");
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			let &member_index = trait_def
				.bindings
				.get(&BindingKey::value(symbol))
				.unwrap_or_else(|| {
					panic!("expected `{trait_path}` to have a const `{name}`")
				});
			let member = &trait_def.members[usize::from(member_index)];
			let MemberKind::Constant(index) = member.kind else {
				panic!("expected `{name}` to be a const");
			};
			&self.signatures.constants[usize::from(index)]
		}

		/// The `InherentImplIdx` of `struct_path`'s own (single, in these
		/// tests) inherent `impl` block, found the same way dispatch itself
		/// would at a method call site.
		fn inherent_impl_index(&self, struct_path: &str) -> InherentImplIdx {
			let target = ImplTarget::Struct(self.struct_index(struct_path));
			self.signatures.impl_dispatch.inherent_candidates(target)[0]
		}

		fn inherent_function_signature(
			&self,
			struct_path: &str,
			name: &str,
		) -> &FunctionSignature {
			let impl_index = self.inherent_impl_index(struct_path);
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("already interned from source");
			let impl_def = &self.defs.inherent_impls[usize::from(impl_index)];
			let &member_index = impl_def
				.bindings
				.get(&BindingKey::value(symbol))
				.unwrap_or_else(|| {
					panic!(
						"expected `{struct_path}` to have a function `{name}`"
					)
				});
			let member = &impl_def.members[usize::from(member_index)];
			let (MemberKind::Function(index) | MemberKind::Method(index)) =
				member.kind
			else {
				panic!("expected `{name}` to be a function");
			};
			&self.signatures.functions[usize::from(index)]
		}

		fn inherent_const_signature(
			&self,
			struct_path: &str,
			name: &str,
		) -> &ConstantSignature {
			let impl_index = self.inherent_impl_index(struct_path);
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("already interned from source");
			let impl_def = &self.defs.inherent_impls[usize::from(impl_index)];
			let &member_index = impl_def
				.bindings
				.get(&BindingKey::value(symbol))
				.unwrap_or_else(|| {
					panic!("expected `{struct_path}` to have a const `{name}`")
				});
			let member = &impl_def.members[usize::from(member_index)];
			let MemberKind::Constant(index) = member.kind else {
				panic!("expected `{name}` to be a const");
			};
			&self.signatures.constants[usize::from(index)]
		}

		fn type_alias(&self, path: &str) -> &TypeAliasSignature {
			let DefKind::TypeAlias(index) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a type alias");
			};
			&self.signatures.type_aliases[usize::from(index)]
		}

		fn struct_signature(&self, path: &str) -> &StructSignature {
			&self.signatures.structs[usize::from(self.struct_index(path))]
		}

		fn struct_index(&self, path: &str) -> StructIdx {
			let DefKind::Struct(struct_index) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a struct");
			};
			struct_index
		}

		fn enum_signature(&self, path: &str) -> &EnumSignature {
			let DefKind::Enum(enum_index) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be an enum");
			};
			&self.signatures.enums[usize::from(enum_index)]
		}

		fn function_signature(&self, path: &str) -> &FunctionSignature {
			let DefKind::Function(index) =
				self.resolve(BindingNamespace::Value, path)
			else {
				panic!("expected `{path}` to be a function");
			};
			&self.signatures.functions[usize::from(index)]
		}

		/// The one-hop declared bounds on generic parameter `param_index` of
		/// whichever item owns `env` — bounds no longer live on the
		/// signature struct itself, see `SignatureBuilder::param_bounds`.
		fn declared_bounds(
			&self,
			env: TypeEnvIdx,
			param_index: u32,
		) -> Vec<&SourceTraitBound> {
			self.signatures.param_bounds[usize::from(env)][param_index as usize]
				.declared_bounds
				.iter()
				.map(|&id| self.signatures.bounds.get(id))
				.collect()
		}

		fn param_count(&self, env: TypeEnvIdx) -> usize {
			self.signatures.param_bounds[usize::from(env)].len()
		}
	}

	#[test]
	fn unbounded_params_resolve_with_no_diagnostics() {
		let case = TestCase::new("type A<T, U> = T;");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let env = case.type_alias("A").type_params;
		assert_eq!(case.param_count(env), 2);
		assert!((0..2).all(|i| case.declared_bounds(env, i).is_empty()));
	}

	#[test]
	fn written_infer_in_an_alias_is_reported_at_its_own_span_once() {
		let source = "type B = A; type A = _;";
		let case = TestCase::new(source);

		assert_eq!(case.type_alias("A").target, TypeIndex::ERROR);
		assert_eq!(case.type_alias("B").target, TypeIndex::ERROR);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		let diagnostic = &case.diagnostics[0];
		assert_eq!(
			diagnostic.code.as_deref(),
			Some(DiagnosticCode::InferInSignature.code())
		);
		assert_eq!(
			diagnostic.message,
			"the placeholder `_` is not allowed within types on item signatures for type aliases"
		);
		assert_eq!(diagnostic.labels.len(), 1);
		assert_eq!(&source[diagnostic.labels[0].range.clone()], "_");
		assert_eq!(
			diagnostic.labels[0].message,
			"not allowed in type signatures"
		);
	}

	#[test]
	fn function_type_ignores_parameter_names_for_identity() {
		let case = TestCase::new(indoc! {"
			type i32;
			type bool;
			type Named = fn(x: i32, y: bool) -> i32;
			type Unnamed = fn(i32, bool) -> i32;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let named = case.type_alias("Named").target;
		assert_eq!(named, case.type_alias("Unnamed").target);
		assert!(matches!(
			case.signatures.types.resolve(named),
			Type::Function { params, result }
				if params.as_ref() == [TypeIndex::I32, TypeIndex::BOOL]
					&& *result == TypeIndex::I32
		));
	}

	#[test]
	fn nested_function_type_uses_generic_scope_and_defaults_to_unit() {
		let case = TestCase::new("type Callback<T> = fn(T) -> fn();");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let alias = case.type_alias("Callback");
		let Type::Function { params, result } =
			case.signatures.types.resolve(alias.target)
		else {
			panic!("expected outer function type");
		};
		assert_eq!(params.len(), 1);
		assert_eq!(
			case.signatures.types.resolve(params[0]),
			&Type::TypeParam {
				env: alias.type_params,
				param_index: 0,
			}
		);
		assert!(matches!(
			case.signatures.types.resolve(*result),
			Type::Function { params, result }
				if params.is_empty() && *result == TypeIndex::UNIT
		));
	}

	#[test]
	fn function_type_placeholders_are_reported_in_source_order() {
		let source = "type Callback = fn((_, _)) -> _;";
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 3, "{:?}", case.diagnostics);
		let mut last_start = 0;
		for diagnostic in &case.diagnostics {
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(DiagnosticCode::InferInSignature.code())
			);
			assert_eq!(diagnostic.labels.len(), 1);
			let range = &diagnostic.labels[0].range;
			assert_eq!(&source[range.clone()], "_");
			assert!(range.start >= last_start);
			last_start = range.end;
		}
		let Type::Function { params, result } = case
			.signatures
			.types
			.resolve(case.type_alias("Callback").target)
		else {
			panic!("expected function type");
		};
		assert_eq!(params.len(), 1);
		assert_eq!(*result, TypeIndex::ERROR);
		assert!(matches!(
			case.signatures.types.resolve(params[0]),
			Type::Tuple { elements }
				if elements.as_ref() == [TypeIndex::ERROR, TypeIndex::ERROR]
		));
	}

	#[test]
	fn user_aliases_are_rejected_as_impl_targets_without_dispatch() {
		let case = TestCase::new(indoc! {"
			trait Tr {}
			impl Tr for Alias {}
			impl Alias {}
			type Alias = S;
			struct S {}
		"});

		assert_eq!(case.diagnostics.len(), 2, "{:?}", case.diagnostics);
		assert!(
			case.diagnostics.iter().all(|diagnostic| diagnostic
				.code
				.as_deref() == Some(
				DiagnosticCode::InvalidImplTarget.code()
			))
		);
		assert_eq!(
			case.signatures.trait_impls.len(),
			case.defs.trait_impls.len()
		);
		assert_eq!(
			case.signatures.inherent_impls.len(),
			case.defs.inherent_impls.len()
		);
		let trait_header = case.signatures.trait_impls[0].as_ref().unwrap();
		let inherent_header =
			case.signatures.inherent_impls[0].as_ref().unwrap();
		assert_eq!(
			case.signatures
				.impl_dispatch
				.trait_header(TraitImplIdx::new(0))
				.trait_def
				.unwrap()
				.inner,
			case.trait_index("Tr"),
		);
		assert_eq!(trait_header.target.inner, TypeIndex::ERROR);
		assert_eq!(inherent_header.target.inner, trait_header.target.inner);
		assert!(case.signatures.impl_dispatch_is_empty());
	}

	#[test]
	fn intrinsic_primitive_can_be_an_impl_target() {
		let case = TestCase::new(indoc! {"
			type u32;
			trait Tr {}
			impl Tr for u32 {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.signatures.trait_candidates(ImplTarget::U32),
			&[(case.trait_index("Tr"), TraitImplIdx::new(0))],
		);
	}

	#[test]
	fn intrinsic_never_is_invalid_impl_target() {
		let case = TestCase::new(indoc! {"
			type never;
			trait Tr {}
			impl Tr for never {}
		"});
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::InvalidImplTarget.code()),
		);
		assert_eq!(
			case.diagnostics[0].message,
			"cannot use type alias as an impl target"
		);
	}

	#[test]
	fn impl_type_parameter_does_not_resolve_to_a_same_named_struct() {
		let case = TestCase::new(indoc! {"
			struct T {}
			trait Tr {}
			impl<T> Tr for T {}
		"});
		assert!(case.signatures.impl_dispatch_is_empty());
		assert_eq!(
			case.diagnostics
				.iter()
				.filter(|diagnostic| diagnostic.code.as_deref()
					== Some(DiagnosticCode::InvalidImplTarget.code()))
				.count(),
			1,
			"{:?}",
			case.diagnostics,
		);
	}

	#[test]
	fn typeset_member_alias_is_rejected_without_a_synthetic_impl() {
		let case = TestCase::new(indoc! {"
			type u32;
			type Alias = u32;
			typeset Int { Alias }
		"});
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::InvalidImplTarget.code()),
		);
		assert!(case.signatures.impl_dispatch_is_empty());
	}

	#[test]
	fn impl_dispatch_rejects_duplicate_trait_for_same_constructor() {
		let case = TestCase::new(indoc! {"
			trait Tr {}
			struct S {}
			impl Tr for S {}
			impl Tr for S {}
		"});
		let target = ImplTarget::from_type(
			case.signatures.types.resolve(
				case.signatures.trait_impls[0]
					.as_ref()
					.unwrap()
					.target
					.inner,
			),
		)
		.unwrap();
		assert_eq!(case.signatures.trait_candidates(target).len(), 1);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateTraitImpl.code())
		);
	}

	#[test]
	fn impl_dispatch_does_not_index_invalid_targets() {
		let case = TestCase::new(indoc! {"
			impl<T> T {}
			impl Missing {}
		"});
		assert!(case.signatures.impl_dispatch_is_empty());
		assert_eq!(
			case.diagnostics
				.iter()
				.filter(|d| d.code.as_deref()
					== Some(DiagnosticCode::InvalidImplTarget.code()))
				.count(),
			1,
			"{:?}",
			case.diagnostics
		);
	}

	#[test]
	fn impl_header_resolves_generic_bounds() {
		let case = TestCase::new(indoc! {"
			trait Bound {}
			struct S {}
			impl<T: Bound> S {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let header = case.signatures.inherent_impls[0].as_ref().unwrap();
		assert_eq!(case.param_count(header.type_params), 1);
		let bounds = case.declared_bounds(header.type_params, 0);
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.trait_index("Bound"));
	}

	#[test]
	fn trait_impl_header_keeps_target_when_trait_path_is_not_a_trait() {
		let case = TestCase::new(indoc! {"
			struct S {}
			impl S for S {}
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitBound.code())
		);
		let header = case.signatures.trait_impls[0].as_ref().unwrap();
		assert!(
			case.signatures
				.impl_dispatch
				.trait_header(TraitImplIdx::new(0))
				.trait_def
				.is_none()
		);
		assert!(matches!(
			case.signatures.types.resolve(header.target.inner),
			Type::Struct { .. }
		));
	}

	#[test]
	fn function_parameter_placeholders_get_separate_diagnostics() {
		let source = "fn f(x: (_, _)) { }";
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 2, "{:?}", case.diagnostics);
		for diagnostic in &case.diagnostics {
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(DiagnosticCode::InferInSignature.code())
			);
			assert_eq!(
				diagnostic.message,
				"the placeholder `_` is not allowed within types on item signatures for functions"
			);
			assert_eq!(diagnostic.labels.len(), 1);
			assert_eq!(&source[diagnostic.labels[0].range.clone()], "_");
			assert_eq!(
				diagnostic.labels[0].message,
				"not allowed in type signatures"
			);
		}
		assert_ne!(
			case.diagnostics[0].labels[0].range,
			case.diagnostics[1].labels[0].range
		);
	}

	#[test]
	fn return_type_placeholders_get_separate_diagnostics() {
		let source = "fn f() -> (_, _) { }";
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 2, "{:?}", case.diagnostics);
		for diagnostic in &case.diagnostics {
			assert_eq!(
				diagnostic.message,
				"the placeholder `_` is not allowed within types on item signatures for return types"
			);
			assert_eq!(diagnostic.labels.len(), 1);
			assert_eq!(&source[diagnostic.labels[0].range.clone()], "_");
			assert_eq!(
				diagnostic.labels[0].message,
				"not allowed in type signatures"
			);
		}
		assert_ne!(
			case.diagnostics[0].labels[0].range,
			case.diagnostics[1].labels[0].range
		);
		let return_type = case.function_signature("f").return_type;
		assert!(matches!(
			case.signatures.types.resolve(return_type),
			Type::Tuple { elements }
				if elements.as_ref() == [TypeIndex::ERROR, TypeIndex::ERROR]
		));
	}

	#[test]
	fn tuple_struct_placeholders_get_separate_diagnostics() {
		let case = TestCase::new("struct Pair(_, _);");

		assert_eq!(case.diagnostics.len(), 2, "{:?}", case.diagnostics);
		for diagnostic in &case.diagnostics {
			assert_eq!(
				diagnostic.message,
				"the placeholder `_` is not allowed within types on item signatures for structs"
			);
		}
	}

	#[test]
	fn duplicate_param_name_is_reported_but_both_entries_survive() {
		let case = TestCase::new("type A<T, T> = T;");

		assert_eq!(
			case.param_count(case.type_alias("A").type_params),
			2,
			"a duplicate name isn't dropped"
		);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateGenericParam.code())
		);
	}

	#[test]
	fn three_unique_params_report_nothing() {
		// Regression test for the exact bug this slice's `resolve_generic_params`
		// was written to avoid: checking the *post-push* vec for a match
		// always finds the entry just pushed, spuriously flagging every
		// single param as its own "duplicate".
		let case = TestCase::new("type A<X, Y, Z> = X;");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
	}

	#[test]
	fn a_bound_naming_a_real_trait_resolves() {
		let case = TestCase::new(indoc! {"
			trait Addable { }
			type A<T: Addable> = T;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let env = case.type_alias("A").type_params;
		assert_eq!(case.declared_bounds(env, 0).len(), 1);
	}

	#[test]
	fn a_bound_naming_a_non_trait_is_rejected() {
		let case = TestCase::new(indoc! {"
			type i32;
			struct NotATrait { x: i32 }
			type A<T: NotATrait> = T;
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitBound.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"expected trait, found struct `NotATrait`"
		);
	}

	#[test]
	fn a_bound_naming_nothing_is_reported_by_path_resolution_itself() {
		let case = TestCase::new("type A<T: DoesNotExist> = T;");

		let env = case.type_alias("A").type_params;
		assert_eq!(case.declared_bounds(env, 0).len(), 0);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::UndeclaredIdentifier.code())
		);
	}

	#[test]
	fn type_aliases_to_primitives_resolve_to_the_primitive() {
		let case = TestCase::new(indoc! {"
			type i32;
			type bool;
			type char;

			type A = i32;
			type B = bool;
			type C = char;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.type_alias("A").target, TypeIndex::I32);
		assert_eq!(case.type_alias("B").target, TypeIndex::BOOL);
		assert_eq!(case.type_alias("C").target, TypeIndex::CHAR);
	}

	#[test]
	fn a_type_alias_cycle_is_reported_once_and_both_sides_become_error() {
		let case = TestCase::new(indoc! {"
			type A = B;
			type B = A;
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTypeAlias.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"cycle detected when expanding type alias `A`"
		);
		assert_eq!(
			case.type_alias("A").target,
			TypeIndex::ERROR,
			"A's own target degrades to Error since it's reached through the cycle"
		);
		assert_eq!(
			case.type_alias("B").target,
			TypeIndex::ERROR,
			"B must still finish, not get stuck, even though it's only reached transitively"
		);
	}

	#[test]
	fn a_real_supertrait_resolves() {
		let case = TestCase::new(indoc! {"
			trait Y { }
			trait X: Y { }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let bounds = case.trait_supertraits("X");
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.trait_index("Y"));
	}

	#[test]
	fn a_supertrait_cycle_is_reported_once_and_both_sides_still_finish() {
		let case = TestCase::new(indoc! {"
			trait A: B { }
			trait B: A { }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"cycle detected when computing the supertraits of `A`"
		);
		assert_eq!(
			case.trait_supertraits("A")[0].trait_index,
			case.trait_index("B"),
			"the direct bound is still recorded even though the deeper cycle was cut"
		);
		assert_eq!(
			case.trait_supertraits("B")[0].trait_index,
			case.trait_index("A"),
			"B must still finish, not get stuck, even though it's only reached transitively"
		);
	}

	#[test]
	fn a_supertrait_cycle_via_two_different_bounds_is_reported_once() {
		// Regression test for the double-report bug this session's
		// `ComputeState::CycleReported` fix closes: `A` stays `InProgress`
		// for its whole bound list, so both `B` and `C` independently
		// re-discover it — without the fix, each would report its own
		// cycle diagnostic for what's really one finding.
		let case = TestCase::new(indoc! {"
			trait A: B + C { }
			trait B: A { }
			trait C: A { }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
	}

	#[test]
	fn a_direct_self_supertrait_reports_a_supertrait_cycle() {
		let case = TestCase::new("trait D: D {}");

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
	}

	#[test]
	fn a_nested_self_bound_reports_an_implied_bounds_cycle_once() {
		let source = indoc! {"
			trait Outer { type Item; }
			trait D: Outer where { Item: D + D } {}
		"};
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"cycle detected when computing the implied bounds of `D`"
		);
		assert_eq!(&source[case.diagnostics[0].labels[0].range.clone()], "D");
	}

	#[test]
	fn a_struct_with_primitive_fields_resolves() {
		let case = TestCase::new(indoc! {"
			type i32;
			struct Point { x: i32, y: i32 }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let field_types = &case.struct_signature("Point").field_types;
		assert_eq!(field_types.len(), 2);
		assert_eq!(field_types[0], TypeIndex::I32);
		assert_eq!(field_types[1], TypeIndex::I32);
	}

	#[test]
	fn a_tuple_struct_resolves() {
		let case = TestCase::new(indoc! {"
			type i32;
			struct Pair(i32, i32);
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.struct_signature("Pair").field_types.len(), 2);
	}

	#[test]
	fn a_struct_referencing_another_struct_resolves() {
		let case = TestCase::new(indoc! {"
			struct Inner { }
			struct Outer { inner: Inner }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
	}

	#[test]
	fn a_directly_self_recursive_struct_is_rejected() {
		let case = TestCase::new("struct A { a: A }");

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"recursive type `A` has infinite size"
		);
	}

	#[test]
	fn a_tuple_field_embedding_the_struct_directly_is_rejected() {
		let case = TestCase::new("struct A { a: (A, A) }");

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
	}

	#[test]
	fn a_mutually_recursive_struct_pair_is_rejected_once() {
		let case = TestCase::new(indoc! {"
			struct A { b: B }
			struct B { a: A }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"recursive types `A` and `B` have infinite size"
		);
	}

	#[test]
	fn a_struct_reference_with_a_satisfying_type_argument_resolves() {
		let case = TestCase::new(indoc! {"
			struct Wrapper<T> { value: T }
			struct S {}
			struct Holder { w: Wrapper<S> }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			struct_index,
			type_args: args,
		} = case.signatures.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert_eq!(*struct_index, case.struct_index("Wrapper"));
		assert_eq!(args.len(), 1);
		let Type::Struct {
			struct_index: arg_struct_index,
			..
		} = case.signatures.types.resolve(args[0])
		else {
			panic!("expected the argument to resolve to `S`");
		};
		assert_eq!(*arg_struct_index, case.struct_index("S"));
	}

	#[test]
	fn a_forward_reference_to_a_generic_struct_resolves() {
		let case = TestCase::new(indoc! {"
			struct Holder { w: Wrapper<S> }
			struct Wrapper<T> { value: T }
			struct S {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			struct_index,
			type_args: args,
		} = case.signatures.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert_eq!(*struct_index, case.struct_index("Wrapper"));
		assert_eq!(args.len(), 1);
	}

	#[test]
	fn a_trait_used_as_a_type_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			trait Bound {}
			struct Holder { w: Bound }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotAType.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"expected type, found trait `Bound`"
		);
	}

	#[test]
	fn a_struct_reference_with_too_few_type_arguments_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			struct Wrapper<A, B> { a: A, b: B }
			struct S {}
			struct Holder { w: Wrapper<S> }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TypeArgumentCountMismatch.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"struct `Wrapper` takes 2 generic arguments but 1 generic argument was supplied"
		);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			type_args: args, ..
		} = case.signatures.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert_eq!(args.as_ref(), [TypeIndex::ERROR, TypeIndex::ERROR]);
	}

	#[test]
	fn a_struct_reference_with_too_many_type_arguments_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			struct Wrapper<T> { value: T }
			struct S {}
			struct Holder { w: Wrapper<S, S> }
		"});

		case.diagnostics().print();

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TypeArgumentCountMismatch.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"struct `Wrapper` takes 1 generic argument but 2 generic arguments were supplied"
		);
	}

	#[test]
	fn a_struct_reference_with_a_bound_violating_type_argument_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			trait Bound {}
			struct Wrapper<T: Bound> { value: T }
			struct S {}
			struct Holder { w: Wrapper<S> }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"the trait bound `S: Bound` is not satisfied"
		);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			type_args: args, ..
		} = case.signatures.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert_eq!(args.as_ref(), [TypeIndex::ERROR]);
	}

	#[test]
	fn a_struct_reference_with_a_bound_satisfying_type_argument_resolves() {
		let case = TestCase::new(indoc! {"
			trait Bound {}
			struct Wrapper<T: Bound> { value: T }
			struct S {}
			impl Bound for S {}
			struct Holder { w: Wrapper<S> }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			type_args: args, ..
		} = case.signatures.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		let Type::Struct {
			struct_index: arg_struct_index,
			..
		} = case.signatures.types.resolve(args[0])
		else {
			panic!("expected the argument to resolve to `S`");
		};
		assert_eq!(*arg_struct_index, case.struct_index("S"));
	}

	#[test]
	fn a_struct_cyclic_via_two_different_fields_is_reported_once() {
		// Same double-report shape as the supertrait regression test above,
		// but for structs: `A` has two fields (`b`, `c`) that each
		// independently lead back to `A`.
		let case = TestCase::new(indoc! {"
			struct A { b: B, c: C }
			struct B { a: A }
			struct C { a: A }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
	}

	#[test]
	fn a_function_with_primitive_params_and_return_resolves() {
		let case = TestCase::new(indoc! {"
			type i32;
			type bool;
			fn add(a: i32, b: i32) -> bool { true }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let signature = case.function_signature("add");
		assert_eq!(signature.param_types.len(), 2);
		assert_eq!(signature.param_types[0], TypeIndex::I32);
		assert_eq!(signature.param_types[1], TypeIndex::I32);
		assert_eq!(signature.return_type, TypeIndex::BOOL);
	}

	#[test]
	fn a_function_with_no_return_type_defaults_to_unit() {
		let case = TestCase::new("fn f() { }");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.function_signature("f").return_type, TypeIndex::UNIT);
	}

	#[test]
	fn a_generic_function_param_resolves_to_its_type_param() {
		let case = TestCase::new("fn identity<T>(x: T) -> T { x }");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let signature = case.function_signature("identity");
		assert_eq!(case.param_count(signature.type_params), 1);
		assert_eq!(signature.param_types[0], signature.return_type);
	}

	#[test]
	fn duplicate_function_param_name_is_reported_but_both_entries_survive() {
		let case = TestCase::new(indoc! {"
			type i32;
			fn f(x: i32, x: i32) { }
		"});

		assert_eq!(case.function_signature("f").param_types.len(), 2);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateFunctionParameter.code())
		);
	}

	#[test]
	fn a_bodiless_function_declaration_resolves_like_a_function() {
		let case = TestCase::new(indoc! {"
			type i32;
			fn imported(x: i32) -> i32;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let signature = case.function_signature("imported");
		assert_eq!(signature.param_types[0], TypeIndex::I32);
		assert_eq!(signature.return_type, TypeIndex::I32);
	}

	#[test]
	fn a_non_intrinsic_type_alias_without_a_body_is_diagnosed() {
		let case = TestCase::new("type X;");

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingTypeAliasBody.code())
		);
		assert_eq!(case.type_alias("X").target, TypeIndex::ERROR);
	}

	#[test]
	fn an_untyped_free_function_parameter_is_diagnosed_here_not_in_prescan() {
		for source in ["fn f(x) { }", "fn f(x);"] {
			let case = TestCase::new(source);

			assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
			assert_eq!(
				case.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::MissingParameterType.code())
			);
			assert_eq!(
				case.function_signature("f").param_types[0],
				TypeIndex::ERROR
			);
		}
	}

	#[test]
	fn an_untyped_non_self_trait_function_parameter_is_diagnosed() {
		let case = TestCase::new("trait Foo { fn get(self, x) -> Self; }");

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingParameterType.code())
		);
		let sig = case.trait_function_signature("Foo", "get");
		assert_eq!(sig.param_types[1], TypeIndex::ERROR);
	}

	#[test]
	fn an_enum_repr_resolves_to_the_named_integer_type() {
		let case = TestCase::new(indoc! {"
			type i32;
			enum Color: i32 { Red, Green, Blue }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.enum_signature("Color").repr, TypeIndex::I32);
	}

	#[test]
	fn an_enum_without_a_repr_is_diagnosed() {
		let case = TestCase::new("enum Color { Red, Green, Blue }");

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingEnumRepr.code())
		);
		assert_eq!(case.enum_signature("Color").repr, TypeIndex::ERROR);
	}

	#[test]
	fn an_enum_with_a_non_integer_repr_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			type bool;
			enum Color: bool { Red, Green, Blue }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::EnumReprNotInteger.code())
		);
		assert_eq!(case.enum_signature("Color").repr, TypeIndex::ERROR);
	}

	#[test]
	fn an_unbounded_trait_associated_type_resolves_with_no_bounds() {
		let case = TestCase::new("trait Container { type Item; }");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert!(
			case.assoc_type_signature("Container", "Item")
				.declared_bounds
				.is_empty()
		);
	}

	#[test]
	fn trait_impl_assoc_type_resolves_to_its_provided_value() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = i32; }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let container = case.trait_index("Container");
		let target = ImplTarget::Struct(case.struct_index("Wrapper"));
		let &(_, impl_index) = case
			.signatures
			.trait_candidates(target)
			.iter()
			.find(|&&(trait_index, _)| trait_index == container)
			.expect("Container is implemented for Wrapper");

		let impl_def = &case.defs.trait_impls[usize::from(impl_index)];
		let item_symbol = case
			.graph
			.strings
			.get("Item")
			.expect("already interned from source");
		let &member_index = impl_def
			.bindings
			.get(&BindingKey::ty(item_symbol))
			.expect("impl provides `Item`");
		let MemberKind::AssociatedType(assoc_type_index) =
			impl_def.members[usize::from(member_index)].kind
		else {
			panic!("expected `Item` to be an associated type");
		};

		let signature = case.signatures.assoc_types
			[usize::from(assoc_type_index)]
		.as_ref()
		.expect("impl's associated type value is resolved");
		assert_eq!(signature.value, Some(TypeIndex::I32));
		assert!(signature.declared_bounds.is_empty());
	}

	#[test]
	fn concrete_member_lookup_preserves_value_overrides_and_defaults() {
		use crate::tir::members::{MemberSource, TypeMemberLookup};
		with_pending_signatures(
			indoc! {"
			trait Container { fn overridden() {} fn inherited() {} }
			struct Wrapper {}
			impl Container for Wrapper { fn overridden() {} type Extra = (); }
		"},
			|builder| {
				let receiver = builder.types.intern(Type::Struct {
					struct_index: StructIdx::new(0),
					type_args: Box::new([]),
				});
				let trait_index = TraitIdx::new(0);
				let impl_index = TraitImplIdx::new(0);
				let reference = SourceSpan::new(
					builder.defs.traits[0].file_id,
					TextSpan::new(0, 1),
				);
				for (name, overridden) in
					[("overridden", true), ("inherited", false)]
				{
					let name = builder.strings.get(name).unwrap();
					let key = BindingKey::new(BindingNamespace::Value, name);
					let TypeMemberLookup::Found(member) = builder
						.resolve_type_member(
							receiver,
							BindingNamespace::Value,
							name,
							reference,
						)
					else {
						panic!("expected value member")
					};
					let MemberKind::Function(actual) = member.kind else {
						panic!("expected function")
					};
					let expected = if overridden {
						let def = &builder.defs.trait_impls[0];
						assert!(
							matches!(member.source, MemberSource::TraitImpl(t, i) if t == trait_index && i == impl_index)
						);
						def.members[usize::from(def.bindings[&key])].kind
					} else {
						let def = &builder.defs.traits[0];
						assert!(
							matches!(member.source, MemberSource::TraitDefault(t, i) if t == trait_index && i == impl_index)
						);
						def.members[usize::from(def.bindings[&key])].kind
					};
					assert!(
						matches!(expected, MemberKind::Function(index) if index == actual)
					);
					let qualified = builder
						.resolve_trait_qualified_member(
							receiver,
							trait_index,
							BindingNamespace::Value,
							Spanned {
								inner: name,
								span: reference.span,
							},
							reference.file_id,
						)
						.unwrap();
					assert!(
						matches!(qualified.kind, MemberKind::Function(index) if index == actual)
					);
				}
				// No declaration exists for this impl member, so it must not
				// become a projection with a provider index as its identity.
				assert!(matches!(
					builder.resolve_type_member(
						receiver,
						BindingNamespace::Type,
						builder.strings.get("Extra").unwrap(),
						reference
					),
					TypeMemberLookup::NotFound
				));
				assert!(builder.diagnostics.is_empty());
			},
		);
	}

	#[test]
	fn associated_value_access_demands_a_pending_written_provider() {
		with_pending_signatures(
			indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = Later; }
			type Later = i32;
		"},
			|builder| {
				let receiver = builder.types.intern(Type::Struct {
					struct_index: StructIdx::new(0),
					type_args: Box::new([]),
				});
				let (declaration, provider, reference) =
					pending_provider(builder, receiver, "Item");
				assert_eq!(
					builder.ensure_assoc_type_value(provider, reference),
					TypeIndex::I32
				);
				assert_eq!(
					builder.ensure_assoc_type_value(provider, reference),
					TypeIndex::I32
				);
				builder
					.ensure_assoc_type_bounds(declaration, reference)
					.unwrap();
				assert!(
					builder.assoc_types[usize::from(declaration)]
						.as_ref()
						.unwrap()
						.value
						.is_none()
				);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
			},
		);
	}

	#[test]
	fn associated_value_access_demands_pending_synthetic_owners() {
		for (source, memory) in [
			(
				"type u32; typeset PointerSize { u32 } trait Memory { type Size: PointerSize; } memory heap: u32;",
				true,
			),
			(
				"type u32; typeset PointerSize { u32 } trait Memory { type Size: PointerSize; } import \"env\" as host { memory heap: u32; }",
				true,
			),
			(
				"type u32; trait Global { type Value; } global counter: u32 = 0;",
				false,
			),
			(
				"type u32; trait Global { type Value; } import \"env\" as host { global counter: u32; }",
				false,
			),
		] {
			with_pending_signatures(source, |builder| {
				let receiver = builder.types.intern(if memory {
					Type::Memory {
						memory_index: MemoryIdx::new(0),
					}
				} else {
					Type::Global {
						global_index: GlobalIdx::new(0),
					}
				});
				let (_, provider, reference) = pending_provider(
					builder,
					receiver,
					if memory { "Size" } else { "Value" },
				);
				assert_eq!(
					builder.ensure_assoc_type_value(provider, reference),
					TypeIndex::U32
				);
				let def_id = builder.defs.assoc_types
					[usize::from(provider.index())]
				.def_id;
				assert!(
					matches!(builder.query_state[&def_id].state,
					QueryState::Resolved(SignatureLocation::Memory(_)) if memory)
						|| matches!(builder.query_state[&def_id].state,
					QueryState::Resolved(SignatureLocation::Global(_)) if !memory)
				);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
			});
		}
	}

	#[test]
	fn associated_value_query_cycle_is_reported_once() {
		with_pending_signatures(
			indoc! {r#"
			type i32;
			type u32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = i32; }
			trait Memory { type Size; }
			trait Global { type Value; }
			memory heap: u32;
			global counter: u32 = 0;
			import "env" as host { memory shared: u32; global counter: u32; }
		"#},
			|builder| {
				for (ty, name) in [
					(
						Type::Struct {
							struct_index: StructIdx::new(0),
							type_args: Box::new([]),
						},
						"Item",
					),
					(
						Type::Memory {
							memory_index: MemoryIdx::new(0),
						},
						"Size",
					),
					(
						Type::Global {
							global_index: GlobalIdx::new(0),
						},
						"Value",
					),
					(
						Type::Memory {
							memory_index: MemoryIdx::new(1),
						},
						"Size",
					),
					(
						Type::Global {
							global_index: GlobalIdx::new(1),
						},
						"Value",
					),
				] {
					let receiver = builder.types.intern(ty);
					let (_, provider, reference) =
						pending_provider(builder, receiver, name);
					let def_id = builder.defs.assoc_types
						[usize::from(provider.index())]
					.def_id;
					// Simulate re-entry while the provider's owner is computing.
					// End-to-end source cycles belong to the normalization checkpoint.
					builder.query_state.get_mut(&def_id).unwrap().state =
						QueryState::InProgress;
					builder.query_stack.push(QueryInfo {
						def_id,
						requested_at: None,
					});
					let before = builder.diagnostics.len();
					assert_eq!(
						builder.ensure_assoc_type_value(provider, reference),
						TypeIndex::ERROR
					);
					assert_eq!(
						builder.ensure_assoc_type_value(provider, reference),
						TypeIndex::ERROR
					);
					assert_eq!(builder.diagnostics.len(), before + 1);
					let diagnostic = &builder.diagnostics[before];
					assert_eq!(
						diagnostic.code.as_deref(),
						Some(DiagnosticCode::CyclicAssociatedType.code())
					);
					assert!(
						diagnostic.message.contains("associated-type value")
					);
					assert_eq!(
						diagnostic.labels[0].range,
						reference.span.into()
					);
					assert_eq!(builder.query_stack.len(), 1);
					builder.query_stack.pop();
				}
			},
		);
	}

	#[test]
	fn associated_value_access_preserves_an_already_diagnosed_error() {
		with_pending_signatures(
			indoc! {"
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = Missing; }
		"},
			|builder| {
				let receiver = builder.types.intern(Type::Struct {
					struct_index: StructIdx::new(0),
					type_args: Box::new([]),
				});
				let (_, provider, reference) =
					pending_provider(builder, receiver, "Item");
				assert_eq!(
					builder.ensure_assoc_type_value(provider, reference),
					TypeIndex::ERROR
				);
				assert_eq!(builder.diagnostics.len(), 1);
				assert_eq!(
					builder.ensure_assoc_type_value(provider, reference),
					TypeIndex::ERROR
				);
				assert_eq!(builder.diagnostics.len(), 1);
			},
		);
	}

	#[test]
	fn missing_associated_type_recovers_without_diagnostics() {
		for path in [
			"<Wrapper as Container>::Item",
			"Wrapper::Item",
			"<Wrapper>::Item::Next",
		] {
			let case = TestCase::new(&format!(
				"
				trait Container {{ type Item; }}
				struct Wrapper {{}}
				impl Container for Wrapper {{}}
				fn f(x: {path}) {{}}
				fn g(x: {path}) {{}}
			"
			));
			assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
			assert_eq!(
				case.function_signature("f").param_types[0],
				TypeIndex::ERROR
			);
			assert_eq!(
				case.function_signature("g").param_types[0],
				TypeIndex::ERROR
			);
		}
	}

	#[test]
	fn memory_declaration_registers_a_synthetic_impl_with_a_checked_size() {
		let case = TestCase::new(indoc! {"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let DefKind::Memory(memory_index) =
			case.resolve(BindingNamespace::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};

		let memory_trait = case.trait_index("Memory");
		let candidates = case
			.signatures
			.trait_candidates(ImplTarget::Memory(memory_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, memory_trait);

		let memory_def = &case.defs.memories[usize::from(memory_index)];
		let size_signature = case.signatures.assoc_types
			[usize::from(memory_def.size_assoc_type_index)]
		.as_ref()
		.expect("memory's Size value is resolved");
		assert_eq!(size_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn memory_size_violating_pointer_size_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			type u32;
			type bool;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: bool;
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);

		let DefKind::Memory(memory_index) =
			case.resolve(BindingNamespace::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};
		let memory_def = &case.defs.memories[usize::from(memory_index)];
		let size_signature = case.signatures.assoc_types
			[usize::from(memory_def.size_assoc_type_index)]
		.as_ref()
		.expect("memory's Size value is resolved, even poisoned");
		assert_eq!(size_signature.value, Some(TypeIndex::ERROR));
	}

	#[test]
	fn global_declaration_registers_a_synthetic_impl_with_its_value_type() {
		let case = TestCase::new(indoc! {"
			type u32;
			trait Global { type Value; }
			global counter: u32 = 0;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let DefKind::Global(global_index) =
			case.resolve(BindingNamespace::Value, "counter")
		else {
			panic!("expected `counter` to be a global");
		};

		let global_trait = case.trait_index("Global");
		let candidates = case
			.signatures
			.trait_candidates(ImplTarget::Global(global_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, global_trait);

		let global_def = &case.defs.globals[usize::from(global_index)];
		assert!(global_def.mut_trait_impl_index.is_none());
		let value_signature = case.signatures.assoc_types
			[usize::from(global_def.value_assoc_type_index)]
		.as_ref()
		.expect("global's Value is resolved");
		assert_eq!(value_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn mutable_global_also_registers_a_global_mut_impl() {
		let case = TestCase::new(indoc! {"
			type u32;
			trait Global { type Value; }
			trait GlobalMut: Global {}
			global mut counter: u32 = 0;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let DefKind::Global(global_index) =
			case.resolve(BindingNamespace::Value, "counter")
		else {
			panic!("expected `counter` to be a global");
		};
		let global_mut_trait = case.trait_index("GlobalMut");
		let candidates = case
			.signatures
			.trait_candidates(ImplTarget::Global(global_index));
		assert!(
			candidates.iter().any(|&(t, _)| t == global_mut_trait),
			"expected a `GlobalMut` impl to be registered too"
		);
	}

	#[test]
	fn global_without_a_type_annotation_is_diagnosed_and_falls_back_to_error() {
		let case = TestCase::new(indoc! {"
			trait Global { type Value; }
			global counter = 0;
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingGlobalType.code())
		);

		let DefKind::Global(global_index) =
			case.resolve(BindingNamespace::Value, "counter")
		else {
			panic!("expected `counter` to be a global");
		};
		let global_def = &case.defs.globals[usize::from(global_index)];
		let value_signature = case.signatures.assoc_types
			[usize::from(global_def.value_assoc_type_index)]
		.as_ref()
		.expect("global's Value is resolved, even poisoned");
		assert_eq!(value_signature.value, Some(TypeIndex::ERROR));
	}

	#[test]
	fn imported_memory_registers_a_synthetic_impl_with_a_checked_size() {
		let case = TestCase::new(indoc! {r#"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			import "env" as host {
				memory shared: u32;
			}
		"#});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let DefKind::Memory(memory_index) =
			case.resolve(BindingNamespace::Type, "host::shared")
		else {
			panic!("expected `host::shared` to be a memory");
		};
		let memory_trait = case.trait_index("Memory");
		let candidates = case
			.signatures
			.trait_candidates(ImplTarget::Memory(memory_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, memory_trait);
		let memory_def = &case.defs.memories[usize::from(memory_index)];
		let size_signature = case.signatures.assoc_types
			[usize::from(memory_def.size_assoc_type_index)]
		.as_ref()
		.expect("memory's Size value is resolved");
		assert_eq!(size_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn imported_global_registers_a_synthetic_impl_with_its_value_type() {
		let case = TestCase::new(indoc! {r#"
			type u32;
			trait Global { type Value; }
			import "env" as host {
				global counter: u32;
			}
		"#});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let DefKind::Global(global_index) =
			case.resolve(BindingNamespace::Value, "host::counter")
		else {
			panic!("expected `host::counter` to be a global");
		};
		let global_trait = case.trait_index("Global");
		let candidates = case
			.signatures
			.trait_candidates(ImplTarget::Global(global_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, global_trait);
		let global_def = &case.defs.globals[usize::from(global_index)];
		assert!(global_def.mut_trait_impl_index.is_none());
		let value_signature = case.signatures.assoc_types
			[usize::from(global_def.value_assoc_type_index)]
		.as_ref()
		.expect("global's Value is resolved");
		assert_eq!(value_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn imported_mutable_global_also_registers_a_global_mut_impl() {
		let case = TestCase::new(indoc! {r#"
			type u32;
			trait Global { type Value; }
			trait GlobalMut: Global {}
			import "env" as host {
				global mut counter: u32;
			}
		"#});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let DefKind::Global(global_index) =
			case.resolve(BindingNamespace::Value, "host::counter")
		else {
			panic!("expected `host::counter` to be a global");
		};
		let global_mut_trait = case.trait_index("GlobalMut");
		let candidates = case
			.signatures
			.trait_candidates(ImplTarget::Global(global_index));
		assert!(
			candidates.iter().any(|&(t, _)| t == global_mut_trait),
			"expected a `GlobalMut` impl to be registered too"
		);
	}

	#[test]
	fn imported_function_resolves_its_parameter_and_return_types() {
		let case = TestCase::new(indoc! {r#"
			type u32;
			import "env" as host {
				fn log(value: u32) -> u32;
			}
		"#});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let DefKind::Function(function_index) =
			case.resolve(BindingNamespace::Value, "host::log")
		else {
			panic!("expected `host::log` to be a function");
		};
		let signature = &case.signatures.functions[usize::from(function_index)];
		assert_eq!(signature.param_types.as_ref(), [TypeIndex::U32]);
		assert_eq!(signature.return_type, TypeIndex::U32);
	}

	#[test]
	fn pointer_type_resolves_through_the_sole_declared_memory() {
		let case = TestCase::new(indoc! {"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			fn f(x: *u32);
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let DefKind::Function(function_index) =
			case.resolve(BindingNamespace::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let DefKind::Memory(memory_index) =
			case.resolve(BindingNamespace::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};
		let signature = &case.signatures.functions[usize::from(function_index)];
		let &[param_type] = signature.param_types.as_ref() else {
			panic!("expected exactly one parameter");
		};
		let Type::Pointer {
			to,
			memory,
			ownership,
		} = case.signatures.types.resolve(param_type)
		else {
			panic!("expected `x` to resolve to a pointer type");
		};
		assert_eq!(*to, TypeIndex::U32);
		assert_eq!(*ownership, ast::Ownership::Exclusive);
		assert_eq!(
			case.signatures.types.resolve(*memory),
			&Type::Memory { memory_index }
		);
	}

	#[test]
	fn pointer_type_with_no_memory_declared_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			type u32;
			fn f(x: *u32);
		"});
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NoMemoryForPointer.code())
		);
		let DefKind::Function(function_index) =
			case.resolve(BindingNamespace::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let signature = &case.signatures.functions[usize::from(function_index)];
		assert_eq!(signature.param_types.as_ref(), [TypeIndex::ERROR]);
	}

	#[test]
	fn pointer_type_with_multiple_memories_is_diagnosed_as_ambiguous() {
		let case = TestCase::new(indoc! {"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			memory heap2: u32;
			fn f(x: *u32);
		"});
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::AmbiguousPointerMemory.code())
		);
		let DefKind::Function(function_index) =
			case.resolve(BindingNamespace::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let signature = &case.signatures.functions[usize::from(function_index)];
		assert_eq!(signature.param_types.as_ref(), [TypeIndex::ERROR]);
	}

	#[test]
	fn slice_and_array_types_resolve_through_the_sole_declared_memory() {
		let case = TestCase::new(indoc! {"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			fn f(s: &[u32], a: *[u32; 4]);
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let DefKind::Function(function_index) =
			case.resolve(BindingNamespace::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let DefKind::Memory(memory_index) =
			case.resolve(BindingNamespace::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};
		let signature = &case.signatures.functions[usize::from(function_index)];
		let &[slice_type, array_type] = signature.param_types.as_ref() else {
			panic!("expected exactly two parameters");
		};
		let Type::Slice {
			of,
			memory,
			ownership,
		} = case.signatures.types.resolve(slice_type)
		else {
			panic!("expected `s` to resolve to a slice type");
		};
		assert_eq!(*of, TypeIndex::U32);
		assert_eq!(*ownership, ast::Ownership::Shared);
		assert_eq!(
			case.signatures.types.resolve(*memory),
			&Type::Memory { memory_index }
		);
		let Type::Array {
			of,
			size,
			memory,
			ownership,
		} = case.signatures.types.resolve(array_type)
		else {
			panic!("expected `a` to resolve to an array type");
		};
		assert_eq!(*of, TypeIndex::U32);
		assert_eq!(*size, 4);
		assert_eq!(*ownership, ast::Ownership::Exclusive);
		assert_eq!(
			case.signatures.types.resolve(*memory),
			&Type::Memory { memory_index }
		);
	}

	#[test]
	fn memory_tagged_pointer_resolves_the_explicit_memory_despite_ambiguity() {
		let case = TestCase::new(indoc! {"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			memory heap2: u32;
			fn f(x: heap2::*u32);
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let DefKind::Function(function_index) =
			case.resolve(BindingNamespace::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let DefKind::Memory(heap2_index) =
			case.resolve(BindingNamespace::Type, "heap2")
		else {
			panic!("expected `heap2` to be a memory");
		};
		let signature = &case.signatures.functions[usize::from(function_index)];
		let &[param_type] = signature.param_types.as_ref() else {
			panic!("expected exactly one parameter");
		};
		let Type::Pointer { memory, .. } =
			case.signatures.types.resolve(param_type)
		else {
			panic!("expected `x` to resolve to a pointer type");
		};
		assert_eq!(
			case.signatures.types.resolve(*memory),
			&Type::Memory {
				memory_index: heap2_index
			}
		);
	}

	#[test]
	fn memory_tag_naming_a_non_memory_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			type u32;
			struct Foo {}
			fn f(x: Foo::*u32);
		"});
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotAMemory.code())
		);
		let DefKind::Function(function_index) =
			case.resolve(BindingNamespace::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let signature = &case.signatures.functions[usize::from(function_index)];
		assert_eq!(signature.param_types.as_ref(), [TypeIndex::ERROR]);
	}

	#[test]
	fn a_trait_associated_type_bound_resolves_to_the_named_traits() {
		let case = TestCase::new(indoc! {"
			trait Bound1 {}
			trait Bound2 {}
			trait Container { type Item: Bound1 + Bound2; }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let bounds = &case
			.assoc_type_signature("Container", "Item")
			.declared_bounds;
		assert_eq!(bounds.len(), 2);
		assert_eq!(
			case.signatures.bounds.get(bounds[0]).trait_index,
			case.trait_index("Bound1")
		);
		assert_eq!(
			case.signatures.bounds.get(bounds[1]).trait_index,
			case.trait_index("Bound2")
		);
	}

	#[test]
	fn an_untyped_self_param_resolves_to_the_traits_own_self() {
		let case = TestCase::new("trait Foo { fn get(self) -> Self; }");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.trait_function_signature("Foo", "get");
		assert_eq!(sig.param_types.len(), 1);
		assert_eq!(
			sig.param_types[0], sig.return_type,
			"`self`'s type and a written `Self` return type should be the \
			 exact same TypeParam"
		);
	}

	#[test]
	fn an_untyped_self_param_resolves_to_the_impls_own_concrete_target() {
		let case = TestCase::new(indoc! {"
			struct S {}
			impl S { fn get(self) -> Self { self } }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.inherent_function_signature("S", "get");
		assert_eq!(sig.param_types.len(), 1);
		assert_eq!(
			sig.param_types[0], sig.return_type,
			"`self` and a written `Self` return type should both resolve to \
			 the impl's own concrete target"
		);
		assert!(
			matches!(
				case.signatures.types.resolve(sig.param_types[0]),
				Type::Struct { .. }
			),
			"an inherent impl's `self` is a concrete type, not an abstract \
			 TypeParam"
		);
	}

	#[test]
	fn an_inherent_impl_const_resolves_its_declared_type() {
		let case = TestCase::new(indoc! {"
			type i32;
			struct S {}
			impl S { const X: i32 = 0; }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.inherent_const_signature("S", "X");
		assert_eq!(sig.ty, TypeIndex::I32);
	}

	#[test]
	fn a_non_self_untyped_inherent_impl_function_parameter_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			struct S {}
			impl S { fn get(self, x) -> Self { self } }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingParameterType.code())
		);
		let sig = case.inherent_function_signature("S", "get");
		assert_eq!(sig.param_types[1], TypeIndex::ERROR);
	}

	#[test]
	fn a_trait_functions_own_generic_param_is_distinct_from_self() {
		let case = TestCase::new("trait Foo { fn get<T>(self, x: T) -> T; }");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.trait_function_signature("Foo", "get");
		assert_eq!(sig.param_types.len(), 2);
		assert_eq!(
			sig.param_types[1], sig.return_type,
			"the param `x: T` and the `-> T` return type should share one TypeParam"
		);
		assert_ne!(
			sig.param_types[0], sig.param_types[1],
			"`self` (Self) and `x` (T) must resolve to different TypeParams"
		);
	}

	#[test]
	fn associated_type_signatures_keep_definition_indices_when_resolved_out_of_order()
	 {
		let case = TestCase::new(indoc! {"
			type i32;
			type bool;
			trait Result { type Value; const FLAG: bool; }
			trait Source { type Value; }
			trait Container {
				type First: Result where { Value = Self::Second::Value };
				type Second: Source;
				const COUNT: i32;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		// Resolving First's bound forces Second before First finishes.
		for (name, expected_trait) in
			[("First", "Result"), ("Second", "Source")]
		{
			let signature = case.assoc_type_signature("Container", name);
			assert_eq!(signature.declared_bounds.len(), 1);
			assert_eq!(
				case.signatures
					.bounds
					.get(signature.declared_bounds[0])
					.trait_index,
				case.trait_index(expected_trait),
			);
		}
		assert_eq!(
			case.signatures.assoc_types.len(),
			case.defs.assoc_types.len()
		);
		assert_eq!(case.signatures.constants.len(), case.defs.constants.len());
		assert_eq!(
			case.trait_const_signature("Result", "FLAG").ty,
			TypeIndex::BOOL
		);
		assert_eq!(
			case.trait_const_signature("Container", "COUNT").ty,
			TypeIndex::I32
		);
		for (index, def) in case.defs.assoc_types.iter().enumerate() {
			assert!(matches!(
				case.signatures.item_lookup[&def.def_id],
				SignatureLocation::AssocType(found) if usize::from(found) == index
			));
		}
		for (index, def) in case.defs.constants.iter().enumerate() {
			assert!(matches!(
				case.signatures.item_lookup[&def.def_id],
				SignatureLocation::Constant(found) if usize::from(found) == index
			));
		}
	}

	#[test]
	fn a_trait_const_resolves_its_declared_type() {
		let case = TestCase::new("type i32; trait Foo { const X: i32; }");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.trait_const_signature("Foo", "X").ty, TypeIndex::I32);
	}

	#[test]
	fn a_trait_consts_type_can_reference_self() {
		let case = TestCase::new(indoc! {"
			trait Foo {
				const X: Self;
				fn get(self) -> Self;
			}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.trait_const_signature("Foo", "X").ty,
			case.trait_function_signature("Foo", "get").return_type,
			"`const X: Self` and `fn get(self) -> Self` should resolve to \
			 the same TypeParam"
		);
	}

	#[test]
	fn a_trait_associated_type_bound_to_a_non_trait_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			struct S {}
			trait Container { type Item: S; }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitBound.code())
		);
		assert!(
			case.assoc_type_signature("Container", "Item")
				.declared_bounds
				.is_empty()
		);
	}

	#[test]
	fn a_where_binding_resolves_an_equals_assoc_type_to_a_concrete_type() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Memory { type Size; }
			fn f<Mem: Memory where { Size = i32 }>() {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.trait_index("Memory"));
		assert_eq!(bounds[0].bindings.len(), 1);
		assert!(matches!(
			bounds[0].bindings[0].kind,
			BindingRequirement::Equals(Spanned {
				inner: TypeIndex::I32,
				..
			})
		));
	}

	#[test]
	fn a_where_binding_resolves_a_bound_assoc_type_to_a_trait() {
		let case = TestCase::new(indoc! {"
			trait Unsigned {}
			trait Memory { type Size; }
			fn f<Mem: Memory where { Size: Unsigned }>() {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].bindings.len(), 1);
		let BindingRequirement::Bound(rhs_bounds) = &bounds[0].bindings[0].kind
		else {
			panic!("expected a `Bound` binding kind");
		};
		assert_eq!(rhs_bounds.len(), 1);
		assert_eq!(
			case.signatures.bounds.get(rhs_bounds[0]).trait_index,
			case.trait_index("Unsigned")
		);
	}

	#[test]
	fn a_duplicate_where_binding_is_diagnosed_and_only_the_first_is_kept() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Memory { type Size; }
			fn f<Mem: Memory where { Size = i32, Size = i32 }>() {}
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert_eq!(bounds[0].bindings.len(), 1);
	}

	#[test]
	fn a_where_binding_naming_an_unknown_associated_type_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Memory { type Size; }
			fn f<Mem: Memory where { Nope = i32 }>() {}
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitMember.code())
		);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert!(bounds[0].bindings.is_empty());
	}

	#[test]
	fn a_where_binding_may_reference_a_sibling_param_declared_later() {
		let case = TestCase::new(indoc! {"
			trait PointerSize {}
			trait Memory { type Size; }
			fn copy<Src: Memory where { Size = S }, S: PointerSize>() {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let env = case.function_signature("copy").type_params;
		let bounds = case.declared_bounds(env, 0);
		let BindingRequirement::Equals(ty) = &bounds[0].bindings[0].kind else {
			panic!("expected an `Equals` binding kind");
		};
		assert!(matches!(
			case.signatures.types.resolve(ty.inner),
			Type::TypeParam { param_index: 1, .. }
		));
	}

	#[test]
	fn a_typeset_bound_resolves_to_its_backing_trait() {
		let case = TestCase::new(indoc! {"
			type u32;
			type i32;
			typeset Int { u32, i32 }
			fn f<T: Int>() {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.typeset_trait_index("Int"));
	}

	#[test]
	fn a_typesets_own_clause_becomes_its_backing_traits_supertraits() {
		let case = TestCase::new(indoc! {"
			trait Bound {}
			typeset Int: Bound {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let supertraits = case.typeset_supertraits("Int");
		assert_eq!(supertraits.len(), 1);
		assert_eq!(supertraits[0].trait_index, case.trait_index("Bound"));
	}

	#[test]
	fn a_typeset_member_registers_a_synthetic_impl() {
		let case = TestCase::new(indoc! {"
			type u32;
			typeset Int { u32 }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.typeset_signature("Int").members[0].inner,
			TypeIndex::U32
		);
		let target = ImplTarget::from_type(
			case.signatures.types.resolve(TypeIndex::U32),
		)
		.unwrap();
		let candidates = case.signatures.trait_candidates(target);
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, case.typeset_trait_index("Int"));
	}

	#[test]
	fn a_typeset_used_before_its_own_declaration_still_sees_its_members() {
		let case = TestCase::new(indoc! {"
			fn f<T: Int>() {}
			type u32;
			typeset Int { u32 }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let target = ImplTarget::from_type(
			case.signatures.types.resolve(TypeIndex::U32),
		)
		.unwrap();
		assert_eq!(case.signatures.trait_candidates(target).len(), 1);
	}

	#[test]
	fn duplicate_typeset_members_are_diagnosed() {
		let case = TestCase::new(indoc! {"
			type u32;
			typeset Int { u32, u32 }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateTraitImpl.code())
		);
		let target = ImplTarget::from_type(
			case.signatures.types.resolve(TypeIndex::U32),
		)
		.unwrap();
		assert_eq!(case.signatures.trait_candidates(target).len(), 1);
	}

	#[test]
	fn self_assoc_type_projects_through_the_traits_own_self() {
		let case = TestCase::new(indoc! {"
			trait Global {
				type Value;
				fn get(self) -> Self::Value;
			}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.trait_function_signature("Global", "get");
		let trait_index = case.trait_index("Global");
		match case.signatures.types.resolve(sig.return_type) {
			Type::AssocTypeProjection {
				trait_index: found_trait,
				base,
				..
			} => {
				assert_eq!(*found_trait, trait_index);
				assert_eq!(
					*base, sig.param_types[0],
					"base should be `self`'s own type — the trait's Self"
				);
			}
			other => panic!("expected an AssocTypeProjection, got {other:?}"),
		}
	}

	#[test]
	fn grouped_bracketed_self_type_projects_the_same_as_a_bare_path() {
		let case = TestCase::new(indoc! {"
			trait Global {
				type Value;
				fn get(self) -> <Self>::Value;
			}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.trait_function_signature("Global", "get");
		let trait_index = case.trait_index("Global");
		match case.signatures.types.resolve(sig.return_type) {
			Type::AssocTypeProjection {
				trait_index: found_trait,
				base,
				..
			} => {
				assert_eq!(*found_trait, trait_index);
				assert_eq!(*base, sig.param_types[0]);
			}
			other => panic!("expected an AssocTypeProjection, got {other:?}"),
		}
	}

	#[test]
	fn qualified_path_disambiguates_between_two_bounds_with_the_same_associated_type()
	 {
		let case = TestCase::new(indoc! {"
			trait A { type X; }
			trait B { type X; }
			fn f<T: A + B>(x: <T as A>::X) { }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let trait_a = case.trait_index("A");
		match case
			.signatures
			.types
			.resolve(case.function_signature("f").param_types[0])
		{
			Type::AssocTypeProjection { trait_index, .. } => {
				assert_eq!(*trait_index, trait_a);
			}
			other => panic!("expected an AssocTypeProjection, got {other:?}"),
		}
	}

	#[test]
	fn qualified_path_continues_projecting_after_its_first_segment() {
		let case = TestCase::new(indoc! {"
			trait B { type Y; }
			trait A { type X: B; }
			fn f<T: A>(x: <T as A>::X::Y) { }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let trait_b = case.trait_index("B");
		match case
			.signatures
			.types
			.resolve(case.function_signature("f").param_types[0])
		{
			Type::AssocTypeProjection { trait_index, .. } => {
				assert_eq!(*trait_index, trait_b);
			}
			other => panic!("expected an AssocTypeProjection, got {other:?}"),
		}
	}

	#[test]
	fn qualified_path_naming_a_member_the_trait_does_not_declare_is_diagnosed()
	{
		let case = TestCase::new(indoc! {"
			trait A { type X; }
			fn f<T: A>(x: <T as A>::Y) { }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitMember.code())
		);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	#[test]
	fn qualified_path_naming_a_trait_the_type_param_does_not_have_is_diagnosed()
	{
		let case = TestCase::new(indoc! {"
			trait A { type X; }
			trait B {}
			fn f<T: B>(x: <T as A>::X) { }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	#[test]
	fn concrete_projection_paths_normalize_forward_references_and_chains() {
		let case = TestCase::new(indoc! {"
			type i32;
			fn f(a: Wrapper::Item::Value, b: <Wrapper>::Item::Value,
				c: <Wrapper as Container>::Item::Value) {}
			trait Container { type Item; }
			trait Element { type Value; }
			struct Wrapper {}
			struct Inner {}
			impl Container for Wrapper { type Item = Inner; }
			impl Element for Inner { type Value = i32; }
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.function_signature("f").param_types.as_ref(),
			[TypeIndex::I32; 3]
		);
	}

	#[test]
	fn concrete_projections_normalize_in_compound_signatures() {
		let case = TestCase::new(indoc! {"
			type i32;
			type u32;
			trait Memory { type Size; }
			memory heap: u32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = i32; }
			type Actual = fn((Wrapper::Item, Wrapper::Item), *Wrapper::Item) -> Wrapper::Item;
			type Expected = fn((i32, i32), *i32) -> i32;
			fn f(a: Actual, b: Expected) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.function_signature("f").param_types[0],
			case.function_signature("f").param_types[1]
		);
	}

	#[test]
	fn unused_associated_values_are_checked_for_direct_and_mutual_cycles() {
		for definitions in [
			"type First = Self::First; type Second = i32;",
			"type First = Self::Second; type Second = Self::First;",
			"type First = (Self::Second, Self::Second); type Second = Self::First;",
		] {
			let case = TestCase::new(&format!(
				"
				type i32;
				trait Pair {{ type First; type Second; }}
				struct Example {{}}
				impl Pair for Example {{ {definitions} }}
				fn independent(x: i32) {{}}
			"
			));
			assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
			assert_eq!(
				case.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::CyclicAssociatedType.code())
			);
			assert_eq!(
				case.function_signature("independent").param_types[0],
				TypeIndex::I32
			);
		}
	}

	#[test]
	fn synthetic_values_normalize_and_synthetic_cycles_recover() {
		let case = TestCase::new(indoc! {r#"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			trait Global { type Value; }
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = u32; }
			fn f(a: heap::Size, b: host::shared::Size) {}
			memory heap: Wrapper::Item;
			global counter: Wrapper::Item = 0;
			import "env" as host { memory shared: Wrapper::Item; global counter: Wrapper::Item; }
		"#});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.function_signature("f").param_types.as_ref(),
			[TypeIndex::U32; 2]
		);
		for def in &case.defs.globals {
			assert_eq!(
				case.signatures.assoc_types
					[usize::from(def.value_assoc_type_index)]
				.as_ref()
				.unwrap()
				.value,
				Some(TypeIndex::U32)
			);
		}
		for declaration in [
			"memory heap: heap::Size;",
			"import \"env\" as host { memory heap: host::heap::Size; }",
		] {
			let case = TestCase::new(&format!(
				"trait Memory {{ type Size; }} {declaration}"
			));
			assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
			assert_eq!(
				case.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::CyclicAssociatedType.code())
			);
		}
	}

	#[test]
	fn head_normalization_exposes_constructor_without_traversing_children() {
		with_pending_signatures(
			indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = i32; }
		"},
			|builder| {
				let receiver = builder.types.intern(Type::Struct {
					struct_index: StructIdx::new(0),
					type_args: Box::new([]),
				});
				let (declaration, provider, reference) =
					pending_provider(builder, receiver, "Item");
				let projection =
					builder.types.intern(Type::AssocTypeProjection {
						base: receiver,
						trait_index: TraitIdx::new(0),
						assoc_type_index: declaration,
					});
				let tuple = builder.types.intern(Type::Tuple {
					elements: Box::new([projection, TypeIndex::I32]),
				});
				let provider_def_id = builder.defs.assoc_types
					[usize::from(provider.index())]
				.def_id;
				// A completed stored value can still contain an abstract projection
				// that becomes reducible later. Here it models that result directly.
				builder.assoc_types[usize::from(provider.index())] =
					Some(AssocTypeSignature {
						declared_bounds: Box::new([]),
						facts: BoundFacts::Ready(Box::new([])),
						value: Some(tuple),
					});
				builder.query_state.get_mut(&provider_def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::AssocType(
						provider.index(),
					));
				assert_eq!(
					builder.normalize_head(projection, reference),
					tuple
				);
				assert_eq!(builder.normalize_head(tuple, reference), tuple);
				assert_eq!(
					builder.normalize_type(projection, reference),
					TypeIndex::ERROR
				);
				assert_eq!(builder.diagnostics.len(), 1);
				assert_eq!(
					builder.diagnostics[0].code.as_deref(),
					Some(DiagnosticCode::CyclicAssociatedType.code())
				);
				assert_eq!(
					builder.normalize_type(TypeIndex::I32, reference),
					TypeIndex::I32
				);
			},
		);
	}

	#[test]
	fn normalization_preserves_abstract_and_inference_projections() {
		with_pending_signatures(
			"trait Container { type Item; } fn f<T>() {}",
			|builder| {
				let def_id = builder.defs.functions[0].def_id;
				let _ = builder.ensure_signature(QueryInfo {
					def_id,
					requested_at: None,
				});
				let env = builder.functions[0].type_params;
				let reference = SourceSpan::new(
					builder.defs.traits[0].file_id,
					TextSpan::new(0, 1),
				);
				let declaration = match builder.defs.traits[0].members[0].kind {
					MemberKind::AssociatedType(index) => index,
					_ => unreachable!(),
				};
				for base in [
					builder.types.intern(Type::TypeParam {
						env,
						param_index: 0,
					}),
					TypeIndex::INFER,
				] {
					let projection =
						builder.types.intern(Type::AssocTypeProjection {
							base,
							trait_index: TraitIdx::new(0),
							assoc_type_index: declaration,
						});
					assert_eq!(
						builder.normalize_head(projection, reference),
						projection
					);
					assert_eq!(
						builder.normalize_type(projection, reference),
						projection
					);
				}
				let error = builder.types.intern(Type::AssocTypeProjection {
					base: TypeIndex::ERROR,
					trait_index: TraitIdx::new(0),
					assoc_type_index: declaration,
				});
				assert_eq!(
					builder.normalize_type(error, reference),
					TypeIndex::ERROR
				);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
			},
		);
	}

	#[test]
	fn deep_normalization_visits_all_supported_children_and_preserves_metadata()
	{
		with_pending_signatures(
			indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = i32; }
			fn marker() {}
		"},
			|builder| {
				use crate::ast::Ownership;
				let receiver = builder.types.intern(Type::Struct {
					struct_index: StructIdx::new(0),
					type_args: Box::new([]),
				});
				let (declaration, _, reference) =
					pending_provider(builder, receiver, "Item");
				let projection =
					builder.types.intern(Type::AssocTypeProjection {
						base: receiver,
						trait_index: TraitIdx::new(0),
						assoc_type_index: declaration,
					});
				let cases = [
					(
						Type::Tuple {
							elements: Box::new([projection, TypeIndex::I32]),
						},
						Type::Tuple {
							elements: Box::new([
								TypeIndex::I32,
								TypeIndex::I32,
							]),
						},
					),
					(
						Type::Struct {
							struct_index: StructIdx::new(0),
							type_args: Box::new([projection]),
						},
						Type::Struct {
							struct_index: StructIdx::new(0),
							type_args: Box::new([TypeIndex::I32]),
						},
					),
					(
						Type::FunctionItem {
							func_index: FunctionIdx::new(0),
							type_args: Box::new([projection]),
						},
						Type::FunctionItem {
							func_index: FunctionIdx::new(0),
							type_args: Box::new([TypeIndex::I32]),
						},
					),
					(
						Type::Function {
							params: Box::new([projection, TypeIndex::I32]),
							result: projection,
						},
						Type::Function {
							params: Box::new([TypeIndex::I32, TypeIndex::I32]),
							result: TypeIndex::I32,
						},
					),
					(
						Type::Pointer {
							to: projection,
							memory: projection,
							ownership: Ownership::Shared,
						},
						Type::Pointer {
							to: TypeIndex::I32,
							memory: TypeIndex::I32,
							ownership: Ownership::Shared,
						},
					),
					(
						Type::Array {
							of: projection,
							size: 7,
							memory: projection,
							ownership: Ownership::Exclusive,
						},
						Type::Array {
							of: TypeIndex::I32,
							size: 7,
							memory: TypeIndex::I32,
							ownership: Ownership::Exclusive,
						},
					),
					(
						Type::Slice {
							of: projection,
							memory: projection,
							ownership: Ownership::Shared,
						},
						Type::Slice {
							of: TypeIndex::I32,
							memory: TypeIndex::I32,
							ownership: Ownership::Shared,
						},
					),
				];
				for (before, after) in cases {
					let before = builder.types.intern(before);
					let after = builder.types.intern(after);
					assert_eq!(
						builder.normalize_head(before, reference),
						before
					);
					assert_eq!(
						builder.normalize_type(before, reference),
						after
					);
					assert_eq!(builder.normalize_type(after, reference), after);
				}
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
			},
		);
	}

	#[test]
	fn repeated_sibling_projections_are_not_a_cycle() {
		with_pending_signatures(
			"type i32; trait Container { type Item; } struct Wrapper {} impl Container for Wrapper { type Item = i32; }",
			|builder| {
				let receiver = builder.types.intern(Type::Struct {
					struct_index: StructIdx::new(0),
					type_args: Box::new([]),
				});
				let (declaration, _, reference) =
					pending_provider(builder, receiver, "Item");
				let projection =
					builder.types.intern(Type::AssocTypeProjection {
						base: receiver,
						trait_index: TraitIdx::new(0),
						assoc_type_index: declaration,
					});
				let pair = builder.types.intern(Type::Tuple {
					elements: Box::new([projection, projection]),
				});
				let expected = builder.types.intern(Type::Tuple {
					elements: Box::new([TypeIndex::I32, TypeIndex::I32]),
				});
				assert_eq!(builder.normalize_type(pair, reference), expected);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
			},
		);
	}

	#[test]
	fn normalization_depth_limit_reports_once_and_unwinds() {
		with_pending_signatures("trait Container { type Item; }", |builder| {
			let reference = SourceSpan::new(
				builder.defs.traits[0].file_id,
				TextSpan::new(0, 1),
			);
			builder.normalization.set_limit_for_test(4);
			let mut nested = TypeIndex::I32;
			for _ in 0..5 {
				nested = builder.types.intern(Type::Tuple {
					elements: Box::new([nested]),
				});
			}
			assert_eq!(
				builder.normalize_type(nested, reference),
				TypeIndex::ERROR
			);
			assert_eq!(builder.diagnostics.len(), 1);
			assert_eq!(
				builder.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TypeNormalizationOverflow.code())
			);
			assert_eq!(
				builder.normalize_type(TypeIndex::I32, reference),
				TypeIndex::I32
			);
		});
	}

	#[test]
	fn distinct_projection_chain_hits_depth_limit_without_exact_repetition() {
		with_pending_signatures(
			"trait Container { type Item; } fn f<T>() {}",
			|builder| {
				let def_id = builder.defs.functions[0].def_id;
				let _ = builder.ensure_signature(QueryInfo {
					def_id,
					requested_at: None,
				});
				let env = builder.functions[0].type_params;
				let reference = SourceSpan::new(
					builder.defs.traits[0].file_id,
					TextSpan::new(0, 1),
				);
				let declaration = match builder.defs.traits[0].members[0].kind {
					MemberKind::AssociatedType(index) => index,
					_ => unreachable!(),
				};
				builder.normalization.set_limit_for_test(6);
				let mut nested = builder.types.intern(Type::TypeParam {
					env,
					param_index: 0,
				});
				for _ in 0..8 {
					nested = builder.types.intern(Type::AssocTypeProjection {
						base: nested,
						trait_index: TraitIdx::new(0),
						assoc_type_index: declaration,
					});
				}
				assert_eq!(
					builder.normalize_type(nested, reference),
					TypeIndex::ERROR
				);
				assert_eq!(builder.diagnostics.len(), 1);
				assert_eq!(
					builder.diagnostics[0].code.as_deref(),
					Some(DiagnosticCode::TypeNormalizationOverflow.code())
				);
				builder.normalization.set_limit_for_test(128);
				assert_eq!(builder.normalize_type(nested, reference), nested);
				assert_eq!(builder.diagnostics.len(), 1);
			},
		);
	}

	#[test]
	fn failed_projection_receivers_do_not_report_missing_members() {
		for ty in [
			"Missing::Item",
			"<Missing>::Item",
			"<Missing as Container>::Item",
			"<Wrapper as Container>::Item::Next",
		] {
			let case = TestCase::new(&format!(
				"
				trait Container {{ type Item; }}
				struct Wrapper {{}}
				impl Container for Wrapper {{ type Item = Missing; }}
				fn f(x: {ty}) {{}}
			"
			));
			// The invalid impl RHS and (where present) the written Missing
			// receiver each own an error, with no member-lookup cascades.
			let expected = if ty.contains("Missing") { 2 } else { 1 };
			assert_eq!(
				case.diagnostics.len(),
				expected,
				"{:?}",
				case.diagnostics
			);
			assert_eq!(
				case.function_signature("f").param_types[0],
				TypeIndex::ERROR
			);
		}
	}

	#[test]
	fn qualified_path_resolves_a_concrete_impls_associated_type() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = i32; }
			fn f(x: <Wrapper as Container>::Item) { }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.function_signature("f").param_types[0], TypeIndex::I32);
	}

	#[test]
	fn generic_impl_projection_substitutes_its_own_target_arguments() {
		let case = TestCase::new(indoc! {"
			type i32;
			type u32;
			trait Container { type Item; }
			struct Wrapper<T> {}
			impl<T> Container for Wrapper<T> { type Item = T; }
			fn first(x: <Wrapper<i32> as Container>::Item) {}
			fn second(x: <Wrapper<u32> as Container>::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.function_signature("first").param_types[0],
			TypeIndex::I32
		);
		assert_eq!(
			case.function_signature("second").param_types[0],
			TypeIndex::U32
		);
	}

	#[test]
	fn generic_impl_target_matches_nested_and_repeated_arguments() {
		let case = TestCase::new(indoc! {"
			type i32;
			type u32;
			trait Container { type Item; }
			struct Inner<T> {}
			struct Pair<A, B> {}
			impl<T> Container for Pair<Inner<T>, Inner<T>> { type Item = T; }
			fn good(x: <Pair<Inner<i32>, Inner<i32>> as Container>::Item) {}
			fn bad(x: <Pair<Inner<i32>, Inner<u32>> as Container>::Item) {}
		"});
		assert_eq!(
			case.function_signature("good").param_types[0],
			TypeIndex::I32
		);
		assert_eq!(
			case.function_signature("bad").param_types[0],
			TypeIndex::ERROR
		);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
	}

	#[test]
	fn generic_impl_requires_its_inferred_arguments_bounds() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Good {}
			trait Container { type Item; }
			struct Yes {}
			struct No {}
			struct Wrapper<T> {}
			impl Good for Yes {}
			impl<T: Good> Container for Wrapper<T> { type Item = i32; }
			fn good(x: <Wrapper<Yes> as Container>::Item) {}
			fn bad(x: <Wrapper<No> as Container>::Item) {}
		"});
		assert_eq!(
			case.function_signature("good").param_types[0],
			TypeIndex::I32
		);
		assert_eq!(
			case.function_signature("bad").param_types[0],
			TypeIndex::ERROR
		);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
	}

	#[test]
	fn generic_impl_bound_checks_descend_through_nested_targets() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Mark {}
			trait Container { type Item; }
			struct Leaf {}
			struct Missing {}
			struct Wrap<T> {}
			impl Mark for Leaf {}
			impl<T: Mark> Mark for Wrap<T> {}
			impl<T: Mark> Container for Wrap<T> { type Item = i32; }
			fn good(x: <Wrap<Wrap<Leaf>> as Container>::Item) {}
			fn bad(x: <Wrap<Wrap<Missing>> as Container>::Item) {}
		"});
		assert_eq!(
			case.function_signature("good").param_types[0],
			TypeIndex::I32
		);
		assert_eq!(
			case.function_signature("bad").param_types[0],
			TypeIndex::ERROR
		);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
	}

	#[test]
	fn generic_impl_with_undetermined_parameter_does_not_match() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper<T> {}
			impl<T> Container for Wrapper<i32> { type Item = T; }
			fn f(x: <Wrapper<i32> as Container>::Item) {}
		"});
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
		assert!(
			case.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::TraitBoundViolation.code())),
			"{:?}",
			case.diagnostics
		);
	}

	#[test]
	fn generic_impl_bound_equalities_are_not_silently_assumed() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Source { type Item; }
			trait Container { type Item; }
			struct Value {}
			struct Wrapper<T> {}
			impl Source for Value { type Item = i32; }
			impl<T: Source where { Item = i32 }> Container for Wrapper<T> {
				type Item = i32;
			}
			fn f(x: <Wrapper<Value> as Container>::Item) {}
		"});
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
		assert!(
			case.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::TraitBoundViolation.code())),
			"{:?}",
			case.diagnostics
		);
	}

	#[test]
	fn generic_projection_cycle_appears_only_after_substitution() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Project { type Out; }
			struct Wrap<T> {}
			struct End {}
			struct Loop {}
			impl<T: Project> Project for Wrap<T> { type Out = T::Out; }
			impl Project for End { type Out = i32; }
			impl Project for Loop { type Out = Wrap<Loop>::Out; }
			fn finite(x: <Wrap<End> as Project>::Out) {}
			fn cyclic(x: <Wrap<Loop> as Project>::Out) {}
		"});
		assert_eq!(
			case.function_signature("finite").param_types[0],
			TypeIndex::I32
		);
		assert_eq!(
			case.function_signature("cyclic").param_types[0],
			TypeIndex::ERROR
		);
		assert!(
			case.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::CyclicAssociatedType.code())),
			"{:?}",
			case.diagnostics
		);
	}

	#[test]
	fn qualified_path_naming_a_trait_the_concrete_type_does_not_implement_is_diagnosed()
	 {
		let case = TestCase::new(indoc! {"
			trait Container { type Item; }
			struct Wrapper {}
			fn f(x: <Wrapper as Container>::Item) { }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	/// Regression test: `TraitAssocType`'s own arm used to resolve at
	/// `TypeEnvId::ROOT` instead of forcing the trait header and using its
	/// `self_scope`, the way `TraitFunction`/`TraitConst` already did — so
	/// `Self` silently failed to resolve inside a declared bound's own
	/// `where { .. }` clause (`type Item: Elem where { Assoc = Self::Item }`
	/// below). Fixed to mirror its sibling arms exactly.
	#[test]
	fn assoc_type_declared_bound_can_reference_the_traits_own_self() {
		let case = TestCase::new(indoc! {"
			trait Elem { type Assoc; }
			trait Container {
				type Item: Elem where { Assoc = Self::Item };
			}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.assoc_type_signature("Container", "Item");
		let bound = case.signatures.bounds.get(sig.declared_bounds[0]);
		let SourceAssocBinding {
			kind: BindingRequirement::Equals(value),
			..
		} = &bound.bindings[0]
		else {
			panic!("expected an `Assoc = ..` binding");
		};

		let container_index = case.trait_index("Container");
		match case.signatures.types.resolve(value.inner) {
			Type::AssocTypeProjection {
				trait_index, base, ..
			} => {
				assert_eq!(*trait_index, container_index);
				match case.signatures.types.resolve(*base) {
					Type::TypeParam { env, param_index } => {
						assert_eq!(
							*env,
							case.signatures.traits
								[usize::from(container_index)]
							.env
						);
						assert_eq!(
							*param_index, 0,
							"should resolve to the trait's own Self"
						);
					}
					other => {
						panic!(
							"expected base to be Self (a TypeParam), got {other:?}"
						)
					}
				}
			}
			other => panic!("expected an AssocTypeProjection, got {other:?}"),
		}
	}

	#[test]
	fn a_bound_generic_params_associated_type_projects_through_the_bound() {
		let case = TestCase::new(indoc! {"
			trait HasSize { type Size; }
			fn f<T: HasSize>(x: T::Size) -> T::Size { x }
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let sig = case.function_signature("f");
		assert_eq!(
			sig.param_types[0], sig.return_type,
			"`x: T::Size` and `-> T::Size` should resolve to the same projection"
		);
		assert!(matches!(
			case.signatures.types.resolve(sig.return_type),
			Type::AssocTypeProjection { .. }
		));
	}

	#[test]
	fn a_missing_associated_type_on_a_bound_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			trait Empty {}
			fn f<T: Empty>(x: T::Missing) { }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitMember.code())
		);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	#[test]
	fn two_bounds_both_declaring_the_same_associated_type_is_ambiguous() {
		let case = TestCase::new(indoc! {"
			trait A { type X; }
			trait B { type X; }
			fn f<T: A + B>(x: T::X) { }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::AmbiguousTraitMember.code())
		);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	/// Verified against real rustc (`trait B: A<X = u32> {}`, `trait C: A<X
	/// = u64> {}`, `fn f<T: B + C>() {}`): rejected immediately with
	/// `E0284`, zero uses of `T` anywhere past the bound list — bound
	/// well-formedness is checked once at declaration, not deferred to
	/// first use. wx matches that here (see `ParamBounds::implied_bounds`);
	/// `a_functions_unused_bound_combination_with_conflicting_assoc_type_bindings_is_still_diagnosed`
	/// below re-checks the fully-unused case, which the old
	/// lazy-on-first-projection design let compile silently.
	#[test]
	fn a_functions_own_bound_combination_with_conflicting_assoc_type_bindings_is_diagnosed_eagerly()
	 {
		let case = TestCase::new(indoc! {"
			type u32;
			type u64;
			trait A { type X; }
			trait B: A where { X = u32 } {}
			trait C: A where { X = u64 } {}
			fn f<T: B + C>(x: T::X) { }
		"});

		case.diagnostics().print();

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"`T` requires conflicting bindings for `A::X`"
		);
		// The conflict is a fact about `A::X`'s *value*, not its identity —
		// `T::X` still names a perfectly real item (`A::X`), so it still
		// resolves to a normal projection rather than `TypeIndex::ERROR`.
		// Normalization cannot select either conflicting value, so the
		// existing bound-conflict diagnostic remains the only error.
		let param_ty = case.function_signature("f").param_types[0];
		match case.signatures.types.resolve(param_ty) {
			Type::AssocTypeProjection { trait_index, .. } => {
				assert_eq!(*trait_index, case.trait_index("A"));
			}
			other => panic!("expected an AssocTypeProjection, got {other:?}"),
		}
	}

	/// Same source as the test above with the parameter dropped — `T` is
	/// never named anywhere past the bound list, so nothing would ever
	/// have demanded its merged closure under the old
	/// lazy-on-first-projection design, and this would have compiled
	/// clean. Verified this is still rejected (`E0284`) in real rustc too;
	/// eager computation in `resolve_generic_params` matches that.
	#[test]
	fn a_functions_unused_bound_combination_with_conflicting_assoc_type_bindings_is_still_diagnosed()
	 {
		let case = TestCase::new(indoc! {"
			type u32;
			type u64;
			trait A { type X; }
			trait B: A where { X = u32 } {}
			trait C: A where { X = u64 } {}
			fn f<T: B + C>() { }
		"});

		case.diagnostics().print();

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		assert_eq!(
			case.diagnostics[0].message,
			"`T` requires conflicting bindings for `A::X`"
		);
	}

	/// Verified against real rustc: `trait D: B + C {}` alone — no use of
	/// `Self::X` anywhere in `D`'s own body — still fails immediately
	/// (`E0284`), same as the function case above. `D`'s own closure is
	/// additionally what every future `T: D` bound would reuse, so it's
	/// computed once, right here, rather than re-merged per use site.
	#[test]
	fn a_traits_own_supertrait_combination_with_conflicting_assoc_type_bindings_is_diagnosed_eagerly()
	 {
		let source = indoc! {"
			type u32;
			type u64;
			trait A { type X; }
			trait B: A where { X = u32 } {}
			trait C: A where { X = u64 } {}
			trait D: B + C {}
		"};
		let case = TestCase::new(source);

		case.diagnostics().print();

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		let labels = &case.diagnostics[0].labels;
		assert_eq!(labels.len(), 3);
		assert_eq!(&source[labels[0].range.clone()], "u64");
		assert_eq!(&source[labels[1].range.clone()], "u32");
		assert_eq!(&source[labels[2].range.clone()], "C");
	}

	#[test]
	fn direct_supertrait_conflict_points_to_second_bound() {
		let source = indoc! {"
			type u32;
			type u64;
			trait A { type X; }
			trait D: A where { X = u32 } + A where { X = u64 } {}
		"};
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		let labels = &case.diagnostics[0].labels;
		assert_eq!(labels.len(), 3);
		assert_eq!(&source[labels[0].range.clone()], "u64");
		assert_eq!(&source[labels[1].range.clone()], "u32");
		assert_eq!(&source[labels[2].range.clone()], "A where { X = u64 }");
	}

	#[test]
	fn conflicting_binding_does_not_poison_another_associated_type() {
		let case = TestCase::new(indoc! {"
			type u32;
			type u64;
			trait A { type X; type Y; }
			trait B: A where { X = u32 } {}
			trait C: A where { X = u64 } {}
			fn f<T: B + C>(x: T::Y) {}
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_ne!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	#[test]
	fn nested_bound_conflict_is_still_diagnosed() {
		let source = indoc! {"
			type u32;
			type u64;
			trait Inner { type X; }
			trait Outer { type Item; }
			trait D: Outer where { Item: Inner where { X = u32 } } + Outer where { Item: Inner where { X = u64 } } + Outer where { Item: Inner where { X = u64 } } {}
		"};
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		let labels = &case.diagnostics[0].labels;
		assert_eq!(&source[labels[0].range.clone()], "u64");
		assert_eq!(&source[labels[1].range.clone()], "u32");
	}

	#[test]
	fn conflict_within_one_nested_bound_list_is_diagnosed() {
		let source = indoc! {"
			type u32;
			type u64;
			trait Inner { type X; }
			trait Outer { type Item; }
			trait D: Outer where { Item: Inner where { X = u32 } + Inner where { X = u64 } } {}
		"};
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		let labels = &case.diagnostics[0].labels;
		assert_eq!(&source[labels[0].range.clone()], "u64");
		assert_eq!(&source[labels[1].range.clone()], "u32");
	}

	#[test]
	fn nested_supertrait_conflict_is_diagnosed_with_forward_references() {
		let source = indoc! {"
			type u32;
			type u64;
			trait Inner { type X; }
			trait Outer { type Item; }
			trait D: Outer where { Item: B + C } {}
			trait B: Inner where { X = u32 } {}
			trait C: Inner where { X = u64 } {}
		"};
		let case = TestCase::new(source);

		case.diagnostics().print();

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].message,
			"`D` requires conflicting bindings for `Inner::X`"
		);
		let labels = &case.diagnostics[0].labels;
		assert_eq!(&source[labels[0].range.clone()], "u64");
		assert_eq!(&source[labels[1].range.clone()], "u32");
		let env =
			case.signatures.traits[usize::from(case.trait_index("D"))].env;
		let merged = case.signatures.param_bounds[usize::from(env)][0]
			.facts
			.current()
			.iter()
			.find(|bound| bound.trait_index == case.trait_index("Outer"))
			.unwrap();
		let inner = &merged.bindings[0].required_bounds;
		assert!(inner.iter().any(|bound| {
			bound.trait_index == case.trait_index("Inner")
				&& matches!(
					bound.bindings[0].kind,
					ImpliedBindingKind::Conflicting
				)
		}));
	}

	#[test]
	fn nested_conflict_survives_outer_equality_in_either_order() {
		let source = indoc! {"
			type u32;
			type u64;
			trait Inner { type X; }
			trait Outer { type Item; }
			trait D: Outer where { Item: Inner where { X = u32 } } + Outer where { Item: Inner where { X = u64 } } + Outer where { Item = u32 } {}
			trait E: Outer where { Item = u32 } + Outer where { Item: Inner where { X = u32 } } + Outer where { Item: Inner where { X = u64 } } {}
		"};
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 2, "{:?}", case.diagnostics);
		for trait_name in ["D", "E"] {
			let env = case.signatures.traits
				[usize::from(case.trait_index(trait_name))]
			.env;
			let merged = case.signatures.param_bounds[usize::from(env)][0]
				.facts
				.current()
				.iter()
				.find(|bound| bound.trait_index == case.trait_index("Outer"))
				.unwrap();
			assert!(matches!(
				merged.bindings[0].kind,
				ImpliedBindingKind::Equals(_)
			));
			let inner = &merged.bindings[0].required_bounds;
			assert_eq!(inner.len(), 1);
			assert!(matches!(
				inner[0].bindings[0].kind,
				ImpliedBindingKind::Conflicting
			));
		}
	}

	#[test]
	fn inherited_nested_conflict_is_not_reported_again() {
		let case = TestCase::new(indoc! {"
			type u32;
			type u64;
			trait Inner { type X; }
			trait Outer { type Item; }
			trait D: Outer where { Item: Inner where { X = u32 } + Inner where { X = u64 } } {}
			trait E: D {}
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
	}

	#[test]
	fn equality_wins_over_associated_type_bounds_in_either_order() {
		let case = TestCase::new(indoc! {"
			type u32;
			trait Mark {}
			trait A { type X; }
			trait D: A where { X: Mark } + A where { X = u32 } {}
			trait E: A where { X = u32 } + A where { X: Mark } {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for trait_name in ["D", "E"] {
			let env = case.signatures.traits
				[usize::from(case.trait_index(trait_name))]
			.env;
			let bounds = &case.signatures.param_bounds[usize::from(env)][0];
			let merged = bounds
				.facts
				.current()
				.iter()
				.find(|bound| bound.trait_index == case.trait_index("A"))
				.unwrap();
			assert_eq!(merged.source, bounds.declared_bounds[0]);
			let ImpliedBindingKind::Equals(reference) = merged.bindings[0].kind
			else {
				panic!("expected equality to win")
			};
			assert_eq!(reference.value, TypeIndex::U32);
		}
	}
	#[test]
	fn normalization_uses_direct_and_chained_equality_facts() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper {}
			impl Container for Wrapper { type Item = i32; }
			fn direct<T: Container where { Item = i32 }>(x: T::Item) {}
			fn chained<T: Container where { Item = <Wrapper as Container>::Item }>(x: T::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["direct", "chained"] {
			assert_eq!(
				case.function_signature(name).param_types[0],
				TypeIndex::I32
			);
		}
	}

	#[test]
	fn normalization_rebinds_self_through_multiple_supertraits() {
		let case = TestCase::new(indoc! {"
			trait Base { type Item; }
			trait Middle: Base where { Item = Self } {}
			trait Final: Middle {}
			fn f<T: Final>(x: T::Item) {}
			fn g<U: Final>(x: U::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["f", "g"] {
			let signature = case.function_signature(name);
			assert!(
				matches!(case.signatures.types.resolve(signature.param_types[0]), Type::TypeParam { env, param_index: 0 } if *env == signature.type_params)
			);
		}
	}

	#[test]
	fn normalization_reads_nested_constraints_and_deduplicates_memberships() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item: Inner; }
			fn f<T: Outer where { Item: Inner where { Value = i32 } }>(x: T::Item::Value) {}
			fn g<T: Outer where { Item: Inner where { Value = i32 } }>(x: <T::Item as Inner>::Value) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["f", "g"] {
			assert_eq!(
				case.function_signature(name).param_types[0],
				TypeIndex::I32
			);
		}
	}

	#[test]
	fn normalization_reads_nested_constraints_without_a_declared_trait_bound() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item; }
			fn f<T: Outer where { Item: Inner where { Value = i32 } }>(x: T::Item::Value) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.function_signature("f").param_types[0], TypeIndex::I32);
	}

	#[test]
	fn normalization_rebinds_self_in_inherited_nested_facts() {
		let case = TestCase::new(indoc! {"
			trait Inner { type Value; }
			trait Outer { type Item; }
			trait Middle: Outer where { Item: Inner where { Value = Self } } {}
			trait Final: Middle {}
			fn f<T: Final>(x: T::Item::Value) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let signature = case.function_signature("f");
		assert!(
			matches!(case.signatures.types.resolve(signature.param_types[0]), Type::TypeParam { env, param_index: 0 } if *env == signature.type_params)
		);
	}

	#[test]
	fn normalization_rebinds_self_in_associated_declaration_facts() {
		let case = TestCase::new(indoc! {"
			trait Inner { type Value; }
			trait Outer { type Item: Inner where { Value = Self }; }
			fn f<T: Outer>(x: T::Item::Value) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let signature = case.function_signature("f");
		assert!(
			matches!(case.signatures.types.resolve(signature.param_types[0]), Type::TypeParam { env, param_index: 0 } if *env == signature.type_params)
		);
	}

	#[test]
	fn normalization_preserves_nested_facts_when_an_outer_equality_supplies_a_value()
	 {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item; }
			fn f<T: Outer where { Item = U } + Outer where { Item: Inner where { Value = i32 } }, U>(x: T::Item::Value) {}
			fn g<T: Outer where { Item: Inner where { Value = i32 } } + Outer where { Item = U }, U>(x: <T::Item as Inner>::Value) {}
			fn h<T: Outer where { Item = U } + Outer where { Item: Inner where { Value = i32 } }, U>(x: <T::Item>::Value) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["f", "g", "h"] {
			assert_eq!(
				case.function_signature(name).param_types[0],
				TypeIndex::I32
			);
		}
	}

	#[test]
	fn normalization_resolves_sibling_projection_equalities_in_either_order() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Container { type Item; }
			fn f<T: Container where { Item = U::Item }, U: Container where { Item = i32 }>(x: T::Item) {}
			fn g<U: Container where { Item = i32 }, T: Container where { Item = U::Item }>(x: T::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["f", "g"] {
			assert_eq!(
				case.function_signature(name).param_types[0],
				TypeIndex::I32
			);
		}
	}

	#[test]
	fn normalization_handles_reciprocal_integer_facts_without_conformance_checks()
	 {
		let case = TestCase::new(indoc! {"
			type u8;
			type i8;
			trait UnsignedInt { type Signed: SignedInt where { Unsigned = Self }; }
			trait SignedInt { type Unsigned: UnsignedInt where { Signed = Self }; }
			impl UnsignedInt for u8 { type Signed = i8; }
			impl SignedInt for i8 { type Unsigned = u8; }
			fn f<T: UnsignedInt>(x: <T::Signed as SignedInt>::Unsigned) {}
			fn g<T: SignedInt>(x: <T::Unsigned as UnsignedInt>::Signed) {}
			fn concrete(x: <u8 as UnsignedInt>::Signed::Unsigned) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["f", "g"] {
			let signature = case.function_signature(name);
			assert!(
				matches!(case.signatures.types.resolve(signature.param_types[0]), Type::TypeParam { env, param_index: 0 } if *env == signature.type_params)
			);
		}
		assert_eq!(
			case.function_signature("concrete").param_types[0],
			TypeIndex::U8
		);
	}

	#[test]
	fn normalization_blocks_tautological_mutual_and_structural_abstract_equalities()
	 {
		let case = TestCase::new(indoc! {"
			trait Pair { type First; type Second; }
			fn tautology<T: Pair where { First = T::First }>(x: T::First) {}
			fn mutual<T: Pair where { First = T::Second, Second = T::First }>(x: T::First, y: T::Second) {}
			fn structural<T: Pair where { First = (T::First,) }>(x: T::First) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["tautology", "mutual", "structural"] {
			for &ty in &case.function_signature(name).param_types {
				assert!(matches!(
					case.signatures.types.resolve(ty),
					Type::AssocTypeProjection { .. }
				));
			}
		}
	}

	#[test]
	fn normalization_leaves_competing_symbolic_equalities_unresolved() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Container { type Item; }
			fn f<T: Container where { Item = U } + Container where { Item = V }, U, V>(x: T::Item) {}
			fn equivalent<T: Container where { Item = U::Item } + Container where { Item = i32 }, U: Container where { Item = i32 }>(x: T::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["f", "equivalent"] {
			assert!(matches!(
				case.signatures
					.types
					.resolve(case.function_signature(name).param_types[0]),
				Type::AssocTypeProjection { .. }
			));
		}
	}

	#[test]
	fn collecting_equality_facts_does_not_check_associated_value_conformance() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Mark {}
			trait Container { type Item: Mark; }
			fn f<T: Container where { Item = i32 }>(x: T::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.function_signature("f").param_types[0], TypeIndex::I32);
	}

	#[test]
	fn normalization_does_not_cache_an_unfinished_assumption_set() {
		with_pending_signatures(
			"type i32; trait Container { type Item; } fn f<T: Container where { Item = i32 }>() {}",
			|builder| {
				let def_id = builder.defs.functions[0].def_id;
				let _ = builder.ensure_signature(QueryInfo {
					def_id,
					requested_at: None,
				});
				let env = builder.functions[0].type_params;
				let base = builder.type_envs.frame(env)[0].ty;
				let assoc_type_index =
					match builder.defs.traits[0].members[0].kind {
						MemberKind::AssociatedType(index) => index,
						_ => unreachable!(),
					};
				let projection =
					builder.types.intern(Type::AssocTypeProjection {
						base,
						trait_index: TraitIdx::new(0),
						assoc_type_index,
					});
				let reference = SourceSpan::new(
					builder.defs.traits[0].file_id,
					TextSpan::new(0, 1),
				);
				let facts = builder.param_bounds[usize::from(env)][0]
					.facts
					.current()
					.to_vec()
					.into_boxed_slice();
				builder.param_bounds[usize::from(env)][0].facts =
					BoundFacts::Provisional(facts.clone());
				assert_eq!(
					builder.normalize_type(projection, reference),
					projection
				);
				builder.param_bounds[usize::from(env)][0].facts =
					BoundFacts::Ready(facts);
				assert_eq!(
					builder.normalize_type(projection, reference),
					TypeIndex::I32
				);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
			},
		);
	}
	#[test]
	fn contextual_equalities_agree_after_self_substitution() {
		let case = TestCase::new(indoc! {"
			trait Inner { type Value; }
			trait Outer { type Item: Inner where { Value = Self }; }
			fn f<T: Outer where { Item: Inner where { Value = T } }>(x: T::Item::Value) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let signature = case.function_signature("f");
		assert!(
			matches!(case.signatures.types.resolve(signature.param_types[0]), Type::TypeParam { env, param_index: 0 } if *env == signature.type_params)
		);
	}

	#[test]
	fn equality_rhs_can_read_a_later_siblings_nested_memberships() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item; }
			fn f<T: Outer where { Item = U::Item::Value }, U: Outer where { Item: Inner where { Value = i32 } }>(x: T::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(case.function_signature("f").param_types[0], TypeIndex::I32);
	}

	#[test]
	fn mutually_referencing_associated_bound_facts_do_not_require_conformance()
	{
		let case = TestCase::new(indoc! {"
			trait Value { type Item; }
			trait Pair {
				type First: Value where { Item = Self::Second::Item };
				type Second: Value where { Item = Self::First::Item };
			}
			fn f<T: Pair>(x: T::First::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert!(matches!(
			case.signatures
				.types
				.resolve(case.function_signature("f").param_types[0]),
			Type::AssocTypeProjection { .. }
		));
	}
	#[test]
	fn normalization_reads_facts_through_multiple_nested_projection_sources() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Leaf { type Value; }
			trait Branch { type Item; }
			trait Outer { type Branch; }
			fn f<T: Outer where { Branch: Branch where { Item: Leaf where { Value = i32 } } }>(x: T::Branch::Item::Value) {}
			fn g<T: Outer where { Branch: Branch where { Item: Leaf where { Value = i32 } } }>(x: <T::Branch::Item as Leaf>::Value) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for name in ["f", "g"] {
			assert_eq!(
				case.function_signature(name).param_types[0],
				TypeIndex::I32
			);
		}
	}

	#[test]
	fn nested_projection_sources_keep_the_declaring_self_context() {
		let case = TestCase::new(indoc! {"
			trait Leaf { type Value; }
			trait Branch { type Item; }
			trait Marked: Branch where { Item: Leaf where { Value = Self } } {}
			trait Outer { type Branch: Marked; }
			fn f<T: Outer>(x: T::Branch::Item::Value, y: T::Branch) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let signature = case.function_signature("f");
		assert_eq!(signature.param_types[0], signature.param_types[1]);
	}

	#[test]
	fn source_equalities_preserve_projections_inside_compound_types() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrap<X> {}
			fn f<U: Container where { Item = i32 }, T: Container where { Item = Wrap<(U::Item,)> }>(x: T::Item) {}
			fn g<T: Container where { Item = Wrap<(U::Item,)> }, U: Container where { Item = i32 }>(x: T::Item) {}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		for (name, t_index, u_index) in [("f", 1, 0), ("g", 0, 1)] {
			let signature = case.function_signature(name);
			let source = case.declared_bounds(signature.type_params, t_index);
			let BindingRequirement::Equals(value) = source[0].bindings[0].kind
			else {
				panic!("expected equality");
			};
			let types = &case.signatures.types;
			let Type::Struct { type_args, .. } = types.resolve(value.inner)
			else {
				panic!("expected Wrap");
			};
			let Type::Tuple { elements } = types.resolve(type_args[0]) else {
				panic!("expected tuple");
			};
			let Type::AssocTypeProjection { base, .. } =
				types.resolve(elements[0])
			else {
				panic!("source must retain U::Item");
			};
			assert!(
				matches!(types.resolve(*base), Type::TypeParam { env, param_index } if *env == signature.type_params && *param_index == u_index)
			);
			let Type::Struct { type_args, .. } =
				types.resolve(signature.param_types[0])
			else {
				panic!("expected normalized Wrap");
			};
			let Type::Tuple { elements } = types.resolve(type_args[0]) else {
				panic!("expected normalized tuple");
			};
			assert_eq!(elements.as_ref(), &[TypeIndex::I32]);
		}
	}

	#[test]
	fn bound_reservations_survive_invalid_occurrences_and_signature_demands() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Leaf { type Value; }
			trait Outer { type Item; }
			fn f<T: i32 + Outer where { Missing: Leaf, Item: i32 + Leaf where { Value = Later<U> }, Item: Leaf }, U: Outer>(x: T::Item::Value) {}
			struct Later<X: Outer> {}
		"});
		assert_eq!(case.diagnostics.len(), 4, "{:?}", case.diagnostics);
		for (code, count) in [
			(DiagnosticCode::NotATraitBound, 2),
			(DiagnosticCode::NotATraitMember, 1),
			(DiagnosticCode::DuplicateAssocTypeBinding, 1),
		] {
			assert_eq!(
				case.diagnostics
					.iter()
					.filter(|d| d.code.as_deref() == Some(code.code()))
					.count(),
				count
			);
		}
		let signature = case.function_signature("f");
		let Type::Struct {
			struct_index,
			type_args,
		} = case.signatures.types.resolve(signature.param_types[0])
		else {
			panic!("valid nested facts must remain usable");
		};
		assert_eq!(*struct_index, case.struct_index("Later"));
		assert!(
			matches!(case.signatures.types.resolve(type_args[0]), Type::TypeParam { env, param_index: 1 } if *env == signature.type_params)
		);
	}

	/// Regression test: `type_satisfies_trait` (satisfaction.rs) used to
	/// check only an abstract projection's effective trait memberships and
	/// never normalize it, so a projection that reduces to a concrete type
	/// satisfying the trait (here `U::Item` reduces to `i32`, and `i32:
	/// Marker`) was rejected outright. Fixed by falling back to
	/// `normalize_head` the same way `find_trait_impl` (members.rs) does.
	#[test]
	fn satisfaction_normalizes_an_abstract_projection_before_checking_trait_membership()
	 {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Marker {}
			impl Marker for i32 {}
			trait Value { type Item; }
			struct Need<X: Marker> {}

			fn f<U: Value where { Item = i32 }>(x: Need<U::Item>) {}
		"});
		assert_eq!(case.diagnostics, Vec::new(), "{:?}", case.diagnostics);
	}

	/// Regression test: structural impl matching used to normalize only the
	/// receiver's head (`normalize_head`), so a receiver whose *nested* type
	/// argument was an unreduced projection (`Wrap<S::Item>` where
	/// `S::Item` reduces to `i32`) failed to match a concrete impl (`impl
	/// Result for Wrap<i32>`) even though the reduced receiver would match.
	/// Fixed by deep-normalizing the receiver once in
	/// `match_impl_target_and_bounds`, the point every matching caller
	/// converges on.
	#[test]
	fn structural_match_normalizes_nested_receiver_type_arguments() {
		let case = TestCase::new(indoc! {"
			type i32;
			trait Value { type Item; }
			trait Result { type Out; }
			struct Wrap<T> {}
			impl Result for Wrap<i32> { type Out = i32; }

			fn f<S: Value where { Item = i32 }>(x: <Wrap<S::Item> as Result>::Out) {}
		"});
		assert_eq!(case.diagnostics, Vec::new(), "{:?}", case.diagnostics);
	}

	/// Regression test for a bug in `union_trait_bound`'s merge: a concrete
	/// conflict (`u32` vs `u64`) arriving with a symbolic fact (`V::Item`)
	/// merged in between used to go completely undiagnosed, because the
	/// `Ambiguous`-vs-`Equals` merge case only deduped by value equality
	/// instead of also checking `known_distinct` against every existing
	/// candidate. `add_equality_fact` now runs that check uniformly for
	/// every merge shape, so this and the reordered case below (where the
	/// two concrete facts merge before the symbolic one arrives) both
	/// diagnose the same way regardless of order.
	#[test]
	fn conflicting_equality_is_diagnosed_around_a_symbolic_middle_term() {
		let case = TestCase::new(indoc! {"
			type u32;
			type u64;
			trait A { type Item; }
			trait Value { type Item; }

			fn f<V: Value, T: A where { Item = u32 } + A where { Item = V::Item } + A where { Item = u64 }>() {}
		"});
		assert!(
			case.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::DuplicateAssocTypeBinding.code())),
			"expected u32/u64 to still be flagged as conflicting even with a symbolic term between them: {:?}",
			case.diagnostics
		);
	}

	#[test]
	fn conflicting_equality_is_diagnosed_with_symbolic_term_last() {
		let case = TestCase::new(indoc! {"
			type u32;
			type u64;
			trait A { type Item; }
			trait Value { type Item; }

			fn f<V: Value, T: A where { Item = u32 } + A where { Item = u64 } + A where { Item = V::Item }>() {}
		"});
		assert!(
			case.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::DuplicateAssocTypeBinding.code())),
			"{:?}",
			case.diagnostics
		);
	}
}
