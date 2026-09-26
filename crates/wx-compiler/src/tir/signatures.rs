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
	BindingRequirement, BoundArena, BoundId, ImpliedTraitBound,
	SourceAssocBinding, SourceTraitBound, report_duplicate_assoc_type_binding,
	report_expected_trait_bound, report_not_an_associated_type,
};
#[cfg(test)]
use super::bounds::{ImpliedBindingKind, equals_type};
use super::defs::{
	AssocTypeIdx, AstEntry, AstNodeRef, BindingKey, BindingNamespace, ConstIdx,
	DefKind, DefinitionRegistry, EnumIdx, FunctionIdx, InherentImplIdx,
	MemberKind, NamespaceIdx, StructIdx, TraitIdx, TraitImplIdx, TypesetIdx,
};
use super::impls::ImplDispatch;
use super::members::{MemberSource, TypeMemberLookup, TypeMemberTarget};
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
	/// The transitive, conflict-merged closure of `declared_bounds` —
	/// computed eagerly by `resolve_generic_params`, the same point
	/// `TraitSignature::implied_bounds` computes its own (see that field's
	/// doc comment): a conflicting bound combination has to be diagnosed
	/// whether or not any code ever ends up projecting a member through
	/// this param, so it can't wait for `resolve_bound_member` to demand it.
	pub implied_bounds: Box<[ImpliedTraitBound]>,
}

impl ParamBounds {
	fn empty() -> Self {
		Self {
			declared_bounds: Box::new([]),
			implied_bounds: Box::new([]),
		}
	}
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

/// A trait associated type's resolved bounds (`type Name: Bound1 +
/// Bound2;`). Resolved against its trait's own `self_scope` (forced first,
/// same as `TraitFunction`/`TraitConst`), so a bound may reference `Self`
/// (`type Size: Memory where { X = Self::Size }`). The concrete type each
/// `impl` provides is a separate query (`TraitImplAssocType`), not tracked
/// here.
pub struct AssocTypeSignature {
	pub(super) declared_bounds: Box<[BoundId]>,
	/// See `ParamBounds::implied_bounds` — same reasoning, computed eagerly
	/// right alongside `declared_bounds` rather than on first demand.
	pub(super) implied_bounds: Box<[ImpliedTraitBound]>,
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
	TraitAssocType(AssocTypeIdx),
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

/// One in-progress query frame — mirrors `rustc_query_system`'s own
/// `QueryInfo`. `requested_at` is the span of the reference that demanded
/// `def_id`, i.e. "the reason for which this was required"; `None` only for
/// a top-level, non-reference demand (the per-`DefId` driver loop) —
/// `resolve_type` always supplies `Some` when it recurses because of a
/// written reference.
#[derive(Clone, Copy)]
struct QueryFrame {
	def_id: DefId,
	requested_at: Option<SourceSpan>,
}

/// What a caller passes to `ensure_signature`.
#[derive(Clone, Copy)]
pub(super) struct QueryInfo {
	pub(super) def_id: DefId,
	pub(super) requested_at: Option<SourceSpan>,
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
	query_stack: Vec<QueryFrame>,
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
		let mut query_state: HashMap<DefId, QueryEntry> = ast_nodes
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

		let frame = self.type_envs.push_param_frame(
			&mut self.types,
			owner,
			parent,
			params.iter().map(|p| p.name),
		);
		self.param_bounds
			.push((0..params.len()).map(|_| ParamBounds::empty()).collect());

		// Resolved only now that `frame` exists (a bound can reference a
		// sibling param, e.g. `T: Trait<U>`), and merged into
		// `implied_bounds` right here, eagerly — see
		// `ParamBounds::implied_bounds`'s own doc comment for why that
		// can't wait for first demand.
		for (index, ast_param) in params.iter().enumerate() {
			let declared_bounds = match &ast_param.bounds {
				Some(bound) => {
					self.resolve_bounds(file_id, namespace, frame, bound)
				}
				None => Box::new([]),
			};
			let implied_bounds = self
				.compute_implied_bounds(&declared_bounds, ast_param.name.inner)
				.into_boxed_slice();
			self.param_bounds[usize::from(frame)][index] = ParamBounds {
				declared_bounds,
				implied_bounds,
			};
		}

		frame
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

	pub(super) fn implied_bounds(
		&self,
		env: TypeEnvIdx,
		param_index: u32,
	) -> &[ImpliedTraitBound] {
		&self.param_bounds[usize::from(env)][param_index as usize]
			.implied_bounds
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
		let def_id = query.def_id;
		match self.query_state[&def_id].state {
			// Already finished on an earlier call.
			QueryState::Resolved(location) => {
				return SignatureStatus::Resolved(location);
			}
			QueryState::CycleReported => {
				return SignatureStatus::CycleReported;
			}
			// First re-entrant discovery: flip to `CycleReported` right
			// here, atomically, before returning `Cycle` — mirrors
			// `ResolveStatus::poll`'s `Resolving -> Error` transition. This
			// is what makes a *second*, independent path that re-discovers
			// the same still-running query see `CycleReported` (silent)
			// instead of `InProgress` (which would mean "report again").
			QueryState::InProgress => {
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::CycleReported;
				return SignatureStatus::Cycle;
			}
			QueryState::Pending => {}
		}

		self.query_state.get_mut(&def_id).unwrap().state =
			QueryState::InProgress;
		self.query_stack.push(QueryFrame {
			def_id,
			requested_at: query.requested_at,
		});

		let ast_index = self.query_state[&def_id].ast_index;
		let ast_nodes = self.ast_nodes;
		let entry = &ast_nodes[ast_index as usize];
		let file_id = entry.file_id;
		let namespace = entry.namespace;
		let node = entry.node.clone();

		match node {
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
				// Checked first so a real, non-intrinsic alias can assume
				// its body is always present below.
				let signature =
					match self.defs.intrinsics.identity_of(type_alias_index) {
						Some(target) => TypeAliasSignature {
							type_params: TypeEnvIdx::ROOT,
							target,
						},
						None => {
							let body = body.as_ref().expect(
								"a non-intrinsic type alias always has a body",
							);
							let type_env = self.resolve_generic_params(
								file_id,
								namespace,
								TypeEnvOwner::TypeAlias(type_alias_index),
								TypeEnvIdx::ROOT,
								type_params,
							);
							let target = self.resolve_type(
								file_id,
								namespace,
								type_env,
								body,
								InferPolicy::Reject(
									InferSignatureKind::TypeAlias,
								),
							);
							TypeAliasSignature {
								type_params: type_env,
								target,
							}
						}
					};

				self.type_aliases[usize::from(type_alias_index)] = signature;
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::TypeAlias(
						type_alias_index,
					));
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

				let declared_bounds = match supertraits {
					Some(bound) => self
						.resolve_bounds(file_id, namespace, self_scope, bound),
					None => Box::new([]),
				};

				for bound in declared_bounds.iter().copied() {
					let bound = self.bounds.get(bound);
					let super_def_id =
						self.defs.traits[usize::from(bound.trait_index)].def_id;
					let reference = bound.span;
					let status = self.ensure_signature(QueryInfo {
						def_id: super_def_id,
						requested_at: Some(reference),
					});
					if let SignatureStatus::Cycle = status {
						let diagnostic = self
							.report_cyclic_supertrait(super_def_id, reference);
						self.diagnostics.push(diagnostic);
					}
				}

				let implied_bounds =
					self.compute_implied_bounds(&declared_bounds, name.inner);
				self.param_bounds[usize::from(self_scope)][0] = ParamBounds {
					declared_bounds,
					implied_bounds: implied_bounds.into_boxed_slice(),
				};
				self.traits[usize::from(trait_index)] =
					TraitSignature { env: self_scope };
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::Trait(trait_index));
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
				// position is already diagnosed there, so this only needs
				// to answer "does the first slot default to `Self`", the
				// same constant-time check that decided it there.
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
						// Already diagnosed by `defs.rs`
						// (`MissingParameterType`) — nothing left to do here
						// but recover.
						None => TypeIndex::ERROR,
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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::Function(
						function_index,
					));
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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::Constant(
						const_index,
					));
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

				let resolved_bounds = match bounds {
					Some(bound) => self
						.resolve_bounds(file_id, namespace, self_scope, bound),
					None => Box::new([]),
				};
				// Eager, same reasoning as `ParamBounds::implied_bounds`: a
				// conflicting bound combination must be diagnosed whether or
				// not any impl ever projects a member through this
				// associated type.
				let implied_bounds =
					self.compute_implied_bounds(&resolved_bounds, name.inner);

				self.assoc_types[usize::from(assoc_type_index)] =
					Some(AssocTypeSignature {
						declared_bounds: resolved_bounds,
						implied_bounds: implied_bounds.into_boxed_slice(),
					});
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::TraitAssocType(
						assoc_type_index,
					));
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

				let scope = self.resolve_generic_params(
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
				self.structs[usize::from(struct_index)].type_params = scope;

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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::Struct(
						struct_index,
					));
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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::Struct(
						struct_index,
					));
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

				let scope = self.resolve_generic_params(
					file_id,
					namespace,
					TypeEnvOwner::Function(function_index),
					TypeEnvIdx::ROOT,
					&signature.type_params,
				);

				// `defs.rs` already validated this parameter list (every
				// name unique, every parameter explicitly typed — `self`
				// has no meaning in a free function, so it's rejected
				// there too). An untyped parameter surviving here is
				// already a diagnosed `MissingParameterType`/
				// `SelfParamPosition` — nothing left to do but recover.
				let param_types: Vec<TypeIndex> = signature
					.params
					.iter()
					.map(|param| match &param.inner.inner.ty {
						Some(ty) => self.resolve_type(
							file_id,
							namespace,
							scope,
							ty,
							InferPolicy::Reject(InferSignatureKind::Function),
						),
						None => TypeIndex::ERROR,
					})
					.collect();

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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::Function(
						function_index,
					));
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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::InherentImpl(
						block_index,
					));
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
				let target_type =
					self.resolve_impl_target(target, header.target);
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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::TraitImpl(
						block_index,
					));
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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::Enum(enum_index));
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
				let trait_def_id =
					self.defs.traits[usize::from(trait_index)].def_id;
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

				let clause_bounds = match bounds {
					Some(bound) => self
						.resolve_bounds(file_id, namespace, self_scope, bound),
					None => Box::new([]),
				};
				for bound in &clause_bounds {
					let bound = self.bounds.get(*bound);
					let super_def_id =
						self.defs.traits[usize::from(bound.trait_index)].def_id;
					let reference = bound.span;
					let status = self.ensure_signature(QueryInfo {
						def_id: super_def_id,
						requested_at: Some(reference),
					});
					if let SignatureStatus::Cycle = status {
						let diagnostic = self
							.report_cyclic_supertrait(super_def_id, reference);
						self.diagnostics.push(diagnostic);
					}
				}

				let implied_bounds =
					self.compute_implied_bounds(&clause_bounds, name.inner);
				self.param_bounds[usize::from(self_scope)][0] = ParamBounds {
					declared_bounds: clause_bounds,
					implied_bounds: implied_bounds.into_boxed_slice(),
				};
				self.traits[usize::from(trait_index)] =
					TraitSignature { env: self_scope };

				// Dispatch already registered each member as a synthetic impl.
				// Resolve its complete type and fill the pre-allocated signature.
				let mut resolved_members = Vec::with_capacity(members.len());
				for (m, &impl_index) in members.iter().zip(member_impls.iter())
				{
					let member_ty = self.resolve_impl_target(
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
				self.query_state.get_mut(&def_id).unwrap().state =
					QueryState::Resolved(SignatureLocation::TypeSet(
						typeset_index,
					));
			}
			_ => todo!("this item kind's signature isn't implemented yet"),
		}

		self.query_stack.pop();
		// Every arm of the match above sets its own `Resolved(..)` state as
		// its last step, so this is never anything else here.
		let QueryState::Resolved(location) = self.query_state[&def_id].state
		else {
			unreachable!(
				"every arm above sets Resolved(..) before falling through to here"
			)
		};
		SignatureStatus::Resolved(location)
	}

	/// Resolves a written type. `Reject` diagnoses `_` at its own span and
	/// recovers as `TypeIndex::ERROR`; `Allow` preserves it as `INFER`.
	/// Nested types retain their shape. Other forms are still being implemented.
	fn resolve_type(
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
				let (mut current, mut next) = if first.type_args.is_empty()
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
							// Identity and param bounds only —
							// deliberately not `ensure_signature`: a
							// struct's fields don't need to be resolved to
							// name the struct itself or check its own type
							// arguments, which is what lets a self-/
							// mutually-referencing pointer field resolve
							// without falsely tripping the cycle machinery
							// `TypeAlias` needs. `type_params` is written
							// as soon as the struct's own generic
							// parameters are resolved (see the
							// `RecordStruct`/`TupleStruct` arms above),
							// specifically so this read is safe even
							// mid-resolution.
							let params_env = self.structs
								[usize::from(struct_index)]
							.type_params;

							let resolved_args: Box<[Spanned<TypeIndex>]> =
								stopped
									.type_args
									.iter()
									.map(|arg| Spanned {
										inner: self.resolve_type(
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
						_ => todo!(
							"resolving a path to this kind of item isn't implemented yet"
						),
					};

					(resolved, walk.stopped_at as usize + 1)
				};

				// Whatever's left continues through impl dispatch or a
				// bound instead of the namespace graph — `members.rs`'s
				// job, not this module's.
				while next < segments.len() {
					let segment = &segments[next];
					if !segment.type_args.is_empty() {
						todo!(
							"generic args on a type-relative path segment aren't implemented yet"
						)
					}
					match self.resolve_type_member(
						current,
						BindingNamespace::Type,
						segment.ident.inner,
						SourceSpan::new(file_id, segment.ident.span),
					) {
						TypeMemberLookup::Found(member) => {
							current = match member.kind {
								MemberKind::AssociatedType(_) => {
									match member.source {
										MemberSource::Bound(trait_index) => {
											self.types.intern(
												Type::AssocTypeProjection {
													trait_index,
													assoc_name: segment
														.ident
														.inner,
													base: current,
												},
											)
										}
										MemberSource::Inherent(_)
										| MemberSource::TraitImpl(..)
										| MemberSource::TraitDefault(_) => {
											todo!(
												"associated-type projection off a concrete receiver isn't implemented yet — needs TraitImplAssocType's own signature resolution"
											)
										}
									}
								}
								// `resolve_type_member` was called with
								// `BindingNamespace::Type` — a Function/
								// Method/Constant is Value-tier, so
								// `bindings` (keyed by tier) can never
								// match one here.
								MemberKind::Function(_)
								| MemberKind::Method(_)
								| MemberKind::Constant(_) => unreachable!(
									"a Type-tier lookup cannot resolve to a Value-tier member"
								),
							};
						}
						TypeMemberLookup::NotFound => {
							self.diagnostics.push(report_no_such_type_member(
								file_id,
								self.strings,
								segment.ident,
							));
							return TypeIndex::ERROR;
						}
						TypeMemberLookup::Ambiguous(candidates) => {
							self.diagnostics.push(
								report_ambiguous_type_member(
									file_id,
									self.strings,
									self.defs,
									segment.ident,
									&candidates,
								),
							);
							return TypeIndex::ERROR;
						}
					}
					next += 1;
				}

				current
			}
			ast::TypeExpression::Function { params, result } => {
				let mut param_types = Vec::with_capacity(params.len());
				for param in params.iter() {
					param_types.push(self.resolve_type(
						file_id,
						namespace,
						env,
						&param.inner.inner.ty,
						infer_policy,
					));
				}
				let result_type = match result {
					Some(result) => self.resolve_type(
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
			ast::TypeExpression::Tuple { elements } => {
				if elements.is_empty() {
					return TypeIndex::UNIT;
				}
				let mut elems: Vec<TypeIndex> =
					Vec::with_capacity(elements.len());
				for element in elements.iter() {
					elems.push(self.resolve_type(
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
	/// `members::ensure_assoc_type_signature`.
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

	fn resolve_bounds(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		env: TypeEnvIdx,
		bound: &Spanned<ast::BoundExpression>,
	) -> Box<[BoundId]> {
		let mut ids = Vec::new();
		self.collect_bounds(file_id, namespace, env, bound, &mut ids);
		ids.into_boxed_slice()
	}

	/// `+`-joined bounds flatten into one `Vec` — `T: Add + PartialEq`
	/// produces two `BoundId`s, not a nested structure mirroring
	/// `BoundList`.
	fn collect_bounds(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		env: TypeEnvIdx,
		expr: &Spanned<ast::BoundExpression>,
		bounds: &mut Vec<BoundId>,
	) {
		match &expr.inner {
			ast::BoundExpression::BoundList(list) => {
				for entry in list.iter() {
					self.collect_bounds(file_id, namespace, env, entry, bounds);
				}
			}
			ast::BoundExpression::Path(segments) => {
				if let Some(trait_index) =
					self.resolve_trait_bound_path(file_id, namespace, segments)
				{
					bounds.push(self.bounds.push(SourceTraitBound {
						trait_index,
						span: SourceSpan::new(file_id, expr.span),
						bindings: Box::new([]),
					}));
				}
			}
			ast::BoundExpression::WithBindings { path, bindings } => {
				// The parser only ever builds `WithBindings.path` as
				// `Box::new(BoundExpression::Path(..))` (`parse_bound` in
				// `ast/mod.rs`) — never a list or another `WithBindings`.
				let ast::BoundExpression::Path(segments) = path.as_ref() else {
					unreachable!("`WithBindings.path` is always a plain `Path`")
				};
				let Some(trait_index) =
					self.resolve_trait_bound_path(file_id, namespace, segments)
				else {
					return;
				};

				let mut source_bindings: Vec<SourceAssocBinding> =
					Vec::with_capacity(bindings.len());
				for binding in bindings.iter() {
					if source_bindings
						.iter()
						.any(|b| b.name.inner == binding.name.inner)
					{
						self.diagnostics.push(
							report_duplicate_assoc_type_binding(
								file_id,
								self.strings,
								binding.name,
							),
						);
						continue;
					}

					let trait_def = &self.defs.traits[usize::from(trait_index)];
					let assoc_type_index = trait_def
						.bindings
						.get(&BindingKey::ty(binding.name.inner))
						.map(|&member_index| {
							trait_def.members[usize::from(member_index)].kind
						})
						.and_then(|kind| match kind {
							MemberKind::AssociatedType(index) => Some(index),
							MemberKind::Function(_)
							| MemberKind::Method(_)
							| MemberKind::Constant(_) => None,
						});
					let Some(assoc_type_index) = assoc_type_index else {
						self.diagnostics.push(report_not_an_associated_type(
							file_id,
							self.strings,
							binding.name,
							trait_def.name.inner,
						));
						continue;
					};

					let kind = match &binding.kind {
						ast::AssocTypeBindingKind::Equals(ty) => {
							let resolved = self.resolve_type(
								file_id,
								namespace,
								env,
								ty,
								InferPolicy::Reject(
									InferSignatureKind::AssocTypeBinding,
								),
							);
							let value = Spanned {
								inner: resolved,
								span: ty.span,
							};
							BindingRequirement::Equals(value)
						}
						ast::AssocTypeBindingKind::Bound(rhs_bound) => {
							BindingRequirement::Bound(self.resolve_bounds(
								file_id, namespace, env, rhs_bound,
							))
						}
					};

					source_bindings.push(SourceAssocBinding {
						name: binding.name,
						assoc_type_index,
						kind,
					});
				}

				bounds.push(self.bounds.push(SourceTraitBound {
					trait_index,
					span: SourceSpan::new(file_id, expr.span),
					bindings: source_bindings.into_boxed_slice(),
				}));
			}
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
				self.diagnostics.push(report_expected_trait_bound(
					file_id,
					self.strings,
					last.ident,
					other.noun(),
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

fn report_no_such_type_member(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitMember.code())
		.with_message(format!(
			"no associated type named `{name_str}` found for this type"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}

/// `candidates` never holds a `MemberSource::Inherent` entry — inherent
/// always wins outright in `resolve_concrete_member`, before any trait
/// candidate is even gathered, so nothing ever reaches `Ambiguous` through
/// it.
fn report_ambiguous_type_member(
	file_id: FileId,
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	name: Spanned<SymbolU32>,
	candidates: &[TypeMemberTarget],
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	let mut diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousTraitMember.code())
		.with_message(format!(
			"`{name_str}` is ambiguous between multiple traits"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label());
	for candidate in candidates {
		let trait_index = match candidate.source {
			MemberSource::TraitImpl(trait_index, _)
			| MemberSource::TraitDefault(trait_index)
			| MemberSource::Bound(trait_index) => trait_index,
			MemberSource::Inherent(_) => continue,
		};
		let trait_name = strings
			.resolve(defs.traits[usize::from(trait_index)].name.inner)
			.unwrap();
		diagnostic =
			diagnostic.with_note(format!("provided by trait `{trait_name}`"));
	}
	diagnostic
}

#[cfg(test)]
mod tests {
	use indoc::indoc;

	use super::*;
	use crate::testing::DiagnosticView;
	use crate::tir::defs::DefinitionRegistry;
	use crate::tir::impls::ImplTarget;
	use crate::vfs;

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
			Some(DiagnosticCode::ExpectedTraitBound.code())
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
			Some(DiagnosticCode::ExpectedTraitBound.code())
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
				SignatureLocation::TraitAssocType(found) if usize::from(found) == index
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
			Some(DiagnosticCode::ExpectedTraitBound.code())
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
		// No substitution logic exists to ever normalize it (and none ever
		// will need to: no concrete type can satisfy `T: B + C` in the
		// first place, since `B` and `C` each require a different, already
		// conflicting `A::X` from any type implementing them), so the
		// diagnostic above is the only signal this program gets — same as
		// real rustc, which also reports only `E0284` here and nothing
		// further.
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
			.implied_bounds
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
				.implied_bounds
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
				.implied_bounds
				.iter()
				.find(|bound| bound.trait_index == case.trait_index("A"))
				.unwrap();
			assert_eq!(merged.source, bounds.declared_bounds[0]);
			let ImpliedBindingKind::Equals(reference) = merged.bindings[0].kind
			else {
				panic!("expected equality to win")
			};
			assert_eq!(
				equals_type(&case.signatures.bounds, reference),
				TypeIndex::U32
			);
		}
	}
}
