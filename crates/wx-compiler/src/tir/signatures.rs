//! Phase 2: declaration signatures, and the `TypeContext` that owns every
//! piece of semantic type state.
//!
//! `TypeContext` borrows Phase 1's output (`defs`, strings, `ast_nodes`, impl
//! dispatch) and owns the mutable state built on top of it: the type
//! interner, bounds, scope frames, per-kind signature tables, and the query
//! and obligation machinery behind `ensure_signature`. `sweep` forces every
//! registered declaration; the context then stays live and mutable for
//! later stages, which keep interning types into it rather than reading a
//! frozen copy.
//!
//! A type parameter's *identity* lives in `TypeEnvArena` (addressed by the
//! `TypeEnvIdx` each signature carries); its *bounds* are a resolved-signature
//! fact in `param_bounds`, index-aligned with that frame. Parameters are not
//! `defs.rs` citizens: nobody writes `foo::T`, so a parameter is only ever
//! reachable from the item that declares it.

use std::collections::HashMap;
use std::ops::Range;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{self, Keyword, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::defs::TypeAliasIdx;
use crate::tir::types::TypeEnvOwner;
use crate::vfs::{FileId, Files};

use super::body::Body;
use super::bounds::{
	BindingRequirement, BoundArena, BoundFacts, BoundId, ImpliedAssocBinding,
	ImpliedBindingKind, ImpliedTraitBound, SourceAssocBinding,
	SourceTraitBound, report_duplicate_assoc_type_binding,
	report_not_a_trait_bound, report_not_an_associated_type,
};
use super::defs::{
	AssocTypeIdx, AstEntry, AstNodeRef, BindingKey, BindingTarget, ConstIdx,
	DefId, DefKind, DefinitionRegistry, EnumIdx, FunctionIdx, GlobalIdx,
	InherentImplIdx, MemberKind, MemoryIdx, Scope, StructIdx, Tier, TraitIdx,
	TraitImplIdx, TypesetIdx,
};
use super::eval::ConstValueState;
use super::impls::{ImplDispatch, ImplTarget};
use super::imports::report_private_identifier;
use super::members::TraitMemberSelection;
use super::obligations::{BoundRequirements, Obligation, ObligationChecker};
use super::operators::OperatorTraits;
use super::paths::PathResolver;
use super::resolutions::{NameResolutions, Referent};
use super::satisfaction::{TypeArgsTarget, report_type_arg_count_mismatch};
use super::solver::{ImplMember, Solver, SolverError, SolverView};
use super::typecheck::BodyContext;
use super::types::{
	ImplKind, Substitution, Type, TypeEnvArena, TypeEnvIdx, TypeIndex,
	TypeInterner,
};

/// One generic parameter's bounds — everything about a `Type::TypeParam`
/// beyond its own identity (which lives in `TypeEnvArena`, addressed by the
/// same `(env, param_index)` pair; see that module's own doc comment for
/// why the two are split apart rather than living on `TypeParam` directly).
/// Stored in `TypeContext::param_bounds`, index-aligned with
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
/// `TypeContext::collect_bound_occurrences` and shared by both the
/// provisional-membership builder (`provisional_from_occurrences`) and the
/// source-bound resolver (`TypeContext::fill_source_bounds`),
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
	/// RHS not resolved yet — `fill_source_bounds` resolves it once
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

/// A resolved `func name<...>(params) -> Result { ... }` — covers both
/// `Item::Function` and `Item::FunctionDeclaration` (an `import` block's
/// bodiless signature), which share one `FunctionSignature` shape in the
/// AST and so share one resolved shape here too. No name/identity fields:
/// unlike `TypeAliasSignature`, nothing needs to display a function's name
/// from just this struct — the one place that will (diagnostics, once
/// bodies exist) already has the `DefId` to look the name up from `defs`.
pub struct FunctionSignature {
	/// The signature's lexical scope, including enclosing impl/trait frames.
	/// Without own parameters this is the parent's scope. Bounds remain in
	/// the registry's parameter table; body assumptions use this same scope.
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

/// The repr every variant's value is held in. A variant is a constant
/// (`defs::EnumDef::variants`), so its value is the constant query's, checked
/// after construction. `TypeIndex::ERROR` if `repr` was missing or resolved to
/// a non-integer type — either way already diagnosed once, here, when that
/// happened.
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
	/// The type scope the constant is declared in, where its type and
	/// initializer are read.
	scope: TypeEnvIdx,
}

/// One `AssocTypeIdx`'s resolved signature. `declared_bounds`/
/// `implied_bounds` (`type Name: Bound1 + Bound2;`, resolved against the
/// trait's own `self_scope` — forced first, same as `TraitFunction`/
/// `TraitConst` — so a bound may reference `Self`, e.g. `type Size: Memory
/// where { X = Self::Size }`) only ever come from a trait's own declaration.
/// `value` holds a trait default or an impl's provided type, when present.
/// Each impl definition has a separate `AssocTypeIdx` from its declaration;
/// only the declaration carries bounds and implied facts.
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
}

/// The resolved header of `impl<...> Trait for Target { ... }`.
pub struct TraitImplSignature {
	/// See `TypeAliasSignature::type_params`.
	pub type_params: TypeEnvIdx,
	pub target: Spanned<TypeIndex>,
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
	#[allow(dead_code)] // No such caller yet.
	Allow,
}

/// A resolved export target, indexed in the corresponding definition arena.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExportedItem {
	Function(FunctionIdx),
	Global(GlobalIdx),
	Memory(MemoryIdx),
}

impl TypeContext<'_, '_, '_> {
	/// Forces every registered declaration, then resolves the export block.
	/// Impl dispatch is complete before this runs, so no signature query can
	/// meet an unindexed member. Impl parameter bounds are resolved here with
	/// every other signature, without an earlier header query.
	///
	/// Construction comes first and checks nothing; each declaration is then
	/// checked against the requirements its signature recorded, and the body
	/// phase checks what is written inside declarations. Afterwards every
	/// query is `Resolved`; the context stays live and mutable.
	pub(super) fn sweep(&mut self) {
		let ast_nodes = self.ast_nodes;
		for entry in ast_nodes {
			let _ = self.ensure_signature(QueryInfo {
				def_id: entry.node.def_id(),
				requested_at: None,
			});
		}
		self.check_declarations();
		self.check_bodies();
		self.exports = self.resolve_exports();
		debug_assert!(
			self.query_state
				.values()
				.all(|entry| matches!(entry.state, QueryState::Resolved(_)))
		);
	}

	/// Checks every declaration, in definition order, which is the order
	/// their diagnostics come out in.
	pub(super) fn check_declarations(&mut self) {
		let mut checker = ObligationChecker {
			solver: &mut self.solver,
			view: SolverView {
				types: &mut self.types,
				defs: self.defs,
				impl_dispatch: self.impl_dispatch,
				traits: &self.traits,
				trait_impls: &self.trait_impls,
				assoc_types: &self.assoc_types,
				param_bounds: &self.param_bounds,
				type_envs: &self.type_envs,
			},
			bounds: &self.bounds,
			strings: self.strings,
			diagnostics: self.diagnostics,
		};
		for entry in self.ast_nodes {
			let range =
				self.query_state[&entry.node.def_id()].obligations.clone();
			for obligation in
				&self.obligations[range.start as usize..range.end as usize]
			{
				// Every signature exists and every fact is `Ready`, so nothing
				// can be pending; a failure has reported itself.
				if let Err(SolverError::Pending) = checker.check(obligation) {
					debug_assert!(
						false,
						"a check cannot be pending once every signature is built"
					);
				}
			}
		}
	}

	/// The body phase. Every signature exists and every fact is final, so a
	/// body may ask the type system anything; nothing it does is recorded for
	/// later. Constant initializers and enum discriminants so far, in
	/// definition order, which is the order their diagnostics come out in.
	fn check_bodies(&mut self) {
		let ast_nodes = self.ast_nodes;
		for entry in ast_nodes {
			match entry.node {
				AstNodeRef::Constant { const_index, .. }
				| AstNodeRef::TraitConst { const_index, .. }
				| AstNodeRef::TraitImplConstant { const_index, .. }
				| AstNodeRef::InherentImplConst { const_index, .. }
				| AstNodeRef::EnumVariant { const_index, .. } => {
					self.ensure_const_body(const_index);
					self.evaluate_constant(const_index);
				}
				AstNodeRef::Enum { enum_index, .. } => {
					self.check_discriminants(enum_index);
				}
				_ => {}
			}
		}
	}

	#[cfg(test)]
	pub(super) fn signature_location(
		&self,
		def_id: DefId,
	) -> SignatureLocation {
		let QueryState::Resolved(location) = self.query_state[&def_id].state
		else {
			unreachable!("`sweep` leaves every query resolved")
		};
		location
	}

	/// All declaration signatures are available; only the selected crate's entries remain.
	fn resolve_exports(&mut self) -> HashMap<SymbolU32, ExportedItem> {
		let mut exports = HashMap::with_capacity(self.defs.exports.len());
		for (&external_name, source) in &self.defs.exports {
			let file_id = source.external_span.file_id;
			let reference = SourceSpan::new(file_id, source.name.span);
			let segments = [ast::PathSegment {
				ident: source.name,
				type_args: Box::new([]),
			}];
			let Ok(key) = PathResolver::new(
				self.diagnostics,
				self.resolutions,
				self.strings,
				self.defs,
			)
			.resolve_definition(
				file_id,
				source.namespace,
				&segments,
				Tier::Value,
			) else {
				continue;
			};
			let kind = key.symbol_kind(self.defs);
			let item = match kind {
				DefKind::Function(index)
					if self.functions[usize::from(index)].type_params
						== TypeEnvIdx::ROOT =>
				{
					ExportedItem::Function(index)
				}
				DefKind::Global(index) => ExportedItem::Global(index),
				DefKind::Memory(index) => ExportedItem::Memory(index),
				_ => {
					let name = self.strings.resolve(source.name.inner).unwrap();
					let mut diagnostic = Diagnostic::error()
						.with_code(DiagnosticCode::CannotExportItem.code())
						.with_message(format!("cannot export `{name}`"))
						.with_label(reference.primary_label());
					if matches!(kind, DefKind::Function(_)) {
						diagnostic = diagnostic.with_note("generic functions require a concrete wrapper before they can be exported");
					} else {
						diagnostic = diagnostic.with_note(
							"only functions, globals, and memories can be exported",
						);
					}
					self.diagnostics.push(diagnostic);
					continue;
				}
			};
			exports.insert(external_name, item);
		}
		exports
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
	/// Structural signature data is available at this location. Deferred
	/// checks may still be awaiting facts; this is not a completed proof.
	Available(SignatureLocation),
	/// Still being computed; the first re-entry has already been reported.
	CycleReported,
	/// The first re-entry into this unfinished signature.
	Cycle,
}

/// The lifecycle of one declaration's signature construction. Reentry into
/// construction reports a cycle once. Checks are not part of this lifecycle:
/// requirements are recorded during construction and solved afterwards by
/// `check_declaration`.
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

/// `ast_index` is this `DefId`'s position in `TypeContext::ast_nodes`
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
	/// What the signature requires and construction could not decide: its run
	/// of `TypeContext::obligations`, checked once every signature exists.
	obligations: Range<u32>,
}

/// An in-progress signature query on `query_stack`: what was asked, and the
/// requirements its construction has registered so far.
pub(super) struct QueryFrame {
	pub(super) def_id: DefId,
	pub(super) requested_at: Option<SourceSpan>,
	pub(super) obligations: Vec<Obligation>,
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

/// The semantic type context: Phase 1's read-only output plus all mutable
/// type state. See the module doc; there is no separate finished form.
pub(super) struct TypeContext<'ast, 'ctx, 'dispatch> {
	pub(super) diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
	/// Every written name resolved so far; see `resolutions.rs`.
	pub(super) resolutions: &'ctx mut NameResolutions,
	pub(super) strings: &'ctx StringInterner,
	/// Source text, for literals whose value is read from their span.
	pub(super) files: &'ctx Files,
	pub(super) defs: &'ctx DefinitionRegistry,
	/// The trait and method each overloadable operator dispatches through.
	pub(super) operators: OperatorTraits,
	ast_nodes: &'ast [AstEntry<'ast>],
	// The resolved data below is read across the sibling TIR modules.
	query_state: HashMap<DefId, QueryEntry>,
	/// In-progress queries, in call order.
	pub(super) query_stack: Vec<QueryFrame>,
	pub(super) solver: Solver,
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
	/// `reserve_param_bounds` and `resolve_generic_params`, once per frame
	/// right after `push_param_frame` created it, so the two arrays can
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
	/// Each constant's checked initializer, by `ConstIdx`; filled on demand
	/// (`ensure_const_body`). `None` for a trait constant without a default.
	pub(super) const_bodies: Vec<Option<Body>>,
	/// Each constant's value query state, by `ConstIdx` (`eval.rs`).
	pub(super) const_values: Vec<ConstValueState>,
	/// The constants being evaluated, outermost first.
	pub(super) const_stack: Vec<ConstIdx>,
	pub(super) inherent_impls: Vec<Option<InherentImplSignature>>,
	pub(super) trait_impls: Vec<Option<TraitImplSignature>>,
	/// Resolved, exportable targets keyed by decoded external name; filled by `sweep`.
	pub exports: HashMap<SymbolU32, ExportedItem>,
	/// Built before the signature sweep and never mutated by its queries.
	pub(super) impl_dispatch: &'dispatch ImplDispatch,
	/// Every declaration's obligations, one contiguous run per declaration
	/// (`QueryEntry::obligations`).
	obligations: Vec<Obligation>,
}

impl<'ast, 'ctx, 'dispatch> TypeContext<'ast, 'ctx, 'dispatch> {
	pub(super) fn new(
		diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
		resolutions: &'ctx mut NameResolutions,
		strings: &'ctx StringInterner,
		files: &'ctx Files,
		defs: &'ctx DefinitionRegistry,
		ast_nodes: &'ast [AstEntry<'ast>],
		impl_dispatch: &'dispatch ImplDispatch,
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
					entry.node.def_id(),
					QueryEntry {
						ast_index: u32::try_from(index).unwrap(),
						state: QueryState::Pending,
						obligations: 0..0,
					},
				)
			})
			.collect();

		Self {
			diagnostics,
			resolutions,
			strings,
			files,
			defs,
			operators: OperatorTraits::new(defs, strings),
			ast_nodes,
			query_state,
			query_stack: Vec::new(),
			solver: Solver::new(),
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
					scope: TypeEnvIdx::ROOT,
				})
				.collect(),
			const_bodies: defs.constants.iter().map(|_| None).collect(),
			const_values: defs
				.constants
				.iter()
				.map(|_| ConstValueState::Unevaluated)
				.collect(),
			const_stack: Vec::new(),
			inherent_impls: defs.inherent_impls.iter().map(|_| None).collect(),
			trait_impls: defs.trait_impls.iter().map(|_| None).collect(),
			exports: HashMap::new(),
			impl_dispatch,
			obligations: Vec::new(),
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
		namespace: Scope,
		owner: TypeEnvOwner,
		parent: TypeEnvIdx,
		params: &[ast::TypeParam],
	) -> TypeEnvIdx {
		// An impl always owns a frame, even an empty one: it is where a `Self`
		// written inside the impl finds the impl it means (`resolve_impl_self`).
		let is_impl = matches!(
			owner,
			TypeEnvOwner::InherentImpl(_) | TypeEnvOwner::TraitImpl(_)
		);
		if params.is_empty() && !is_impl {
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
		match owner {
			TypeEnvOwner::Struct(index) => {
				self.structs[usize::from(index)].type_params = type_env
			}
			TypeEnvOwner::Function(index) => {
				self.functions[usize::from(index)].type_params = type_env
			}
			TypeEnvOwner::TypeAlias(index) => {
				self.type_aliases[usize::from(index)].type_params = type_env
			}
			_ => {}
		}

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
				let subject = self.type_envs.params(type_env)[index].ty;
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
		// Bound IDs were published above; filling their sources preserves them.
		for occurrences in &occurrences_per_param {
			self.fill_source_bounds(file_id, namespace, type_env, occurrences);
		}

		for (index, ast_param) in params.iter().enumerate() {
			let subject = self.type_envs.params(type_env)[index].ty;
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
	/// frame, immediately after `push_param_frame` creates it, so the two
	/// arrays can never drift in
	/// length; this is the one place `param_bounds` is ever pushed to.
	///
	/// The placeholder is filled in by `resolve_generic_params`, right after
	/// it resolves the bounds that needed the frame to exist first (a bound
	/// can reference a sibling param). A trait's or typeset's `Self` frame
	/// (not routed through `resolve_generic_params`) keeps the empty
	/// placeholder: its `Self` is answered directly from
	/// `TraitSignature::implied_bounds` instead (see `resolve_bound_member`'s
	/// own doc comment).
	fn reserve_param_bounds(&mut self, frame: TypeEnvIdx) {
		debug_assert_eq!(usize::from(frame), self.param_bounds.len());
		let count = self.type_envs.params(frame).len();
		self.param_bounds
			.push((0..count).map(|_| ParamBounds::empty()).collect());
	}

	/// What `Self` means inside an impl: the impl's target, found through the
	/// frame every impl owns. `None` outside an impl, and in the impl's own
	/// header, whose target is what `Self` would name.
	fn resolve_impl_self(
		&self,
		env: TypeEnvIdx,
	) -> Option<(Referent, TypeIndex)> {
		match self.type_envs.enclosing_impl(env)? {
			ImplKind::Inherent(index) => Some((
				Referent::InherentImplSelf(index),
				self.inherent_impls[usize::from(index)]
					.as_ref()?
					.target
					.inner,
			)),
			ImplKind::Trait(index) => Some((
				Referent::TraitImplSelf(index),
				self.trait_impls[usize::from(index)].as_ref()?.target.inner,
			)),
		}
	}

	/// Resolves a written impl target in the impl's own parameter frame. The
	/// dispatch head only identifies candidates; its arguments are checked and
	/// retained here so matching can use the full target later.
	fn resolve_impl_target(
		&mut self,
		file_id: FileId,
		namespace: Scope,
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
		let def_id = DefId::Struct(struct_index);
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
		let resolved_args: Box<[TypeIndex]> = segment
			.type_args
			.iter()
			.map(|arg| {
				self.resolve_type(
					file_id,
					namespace,
					env,
					arg,
					InferPolicy::Reject(InferSignatureKind::AssocTypeBinding),
				)
			})
			.collect();
		let args = self.resolve_type_args(
			env,
			file_id,
			segment,
			params_env,
			&resolved_args,
			TypeEnvOwner::Struct(struct_index),
		);
		self.types.intern_struct(struct_index, &args)
	}

	pub(super) fn match_inherent_impl_candidate_query(
		&mut self,
		assumption_context: TypeEnvIdx,
		impl_index: InherentImplIdx,
		receiver: TypeIndex,
	) -> Result<bool, SolverError> {
		let Some(header) =
			self.inherent_impls[usize::from(impl_index)].as_ref()
		else {
			return Err(SolverError::Pending);
		};
		self.match_impl_target_and_bounds(
			assumption_context,
			header.type_params,
			header.target.inner,
			receiver,
		)
		.map(|args| args.is_some())
	}

	/// A constant's declared type (`ERROR` when missing or unresolved), as
	/// written, and the scope it is written in.
	/// The integer type an enum's variant values are held in, or `ERROR`.
	pub(super) fn enum_repr(&self, enum_index: EnumIdx) -> TypeIndex {
		self.enums[usize::from(enum_index)].repr
	}

	pub(super) fn constant_type(
		&self,
		const_index: ConstIdx,
	) -> (TypeIndex, TypeEnvIdx) {
		let signature = &self.constants[usize::from(const_index)];
		(signature.ty, signature.scope)
	}

	/// A struct's field types as written, in declaration order.
	pub(super) fn struct_field_types(
		&self,
		struct_index: StructIdx,
	) -> &[TypeIndex] {
		&self.structs[usize::from(struct_index)].field_types
	}

	/// A typeset's member types.
	pub(super) fn typeset_members(
		&self,
		typeset_index: TypesetIdx,
	) -> &[Spanned<TypeIndex>] {
		&self.typesets[usize::from(typeset_index)].members
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
	/// the moment `TypeContext` exists, before any query has run at
	/// all. This is how a pre-seeded kind's own index
	/// (`AstNodeRef::Trait { trait_index, .. }` and friends) is read
	/// without forcing that item's signature — the six pre-seeded kinds no
	/// longer get an early `SignatureLocation` seeded into `query_state`;
	/// they get this instead, which was already sitting there.
	pub(super) fn ast_node(&self, def_id: DefId) -> &AstNodeRef<'ast> {
		&self.ast_nodes[self.ast_index(def_id) as usize].node
	}

	/// The declaration's position in parse order, which is definition order.
	pub(super) fn ast_index(&self, def_id: DefId) -> u32 {
		self.query_state[&def_id].ast_index
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
				return SignatureStatus::Available(location);
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
		self.query_stack.push(QueryFrame {
			def_id: query.def_id,
			requested_at: query.requested_at,
			obligations: Vec::new(),
		});

		let entry =
			&self.ast_nodes[self.query_state[&query.def_id].ast_index as usize];
		let location =
			self.compute_signature(entry.file_id, entry.namespace, entry.node);

		let frame = self.query_stack.pop().unwrap();
		// Nested queries register while this one is open, so its own
		// obligations join the shared list as one run only when it finishes.
		let start = u32::try_from(self.obligations.len()).unwrap();
		self.obligations.extend(frame.obligations);
		let end = u32::try_from(self.obligations.len()).unwrap();
		let entry = self.query_state.get_mut(&query.def_id).unwrap();
		entry.state = QueryState::Resolved(location);
		entry.obligations = start..end;
		SignatureStatus::Available(location)
	}

	/// Resolves a `func`'s generic params, parameter types and return type.
	/// Shared by `AstNodeRef::Function` and `AstNodeRef::ImportedFunction` —
	/// both a plain/declared free function and an imported one carry the
	/// exact same `ast::FunctionSignature` shape, so there's nothing about
	/// resolution itself that differs once that signature is in hand.
	fn resolve_function_signature(
		&mut self,
		file_id: FileId,
		namespace: Scope,
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

		// The synthetic `impl Call` and `impl Function` for <function>: generic
		// over the function's own parameters, with their bounds as their
		// assumptions. `Args` is the one parameter type (`func(..)`'s rule).
		let function_def = &self.defs.functions[usize::from(function_index)];
		let function_impls = function_def
			.function_impls
			.expect("a free or imported function has synthetic impls");
		let name_span = function_def.name.span;
		let args = if let [param] = &param_types[..] {
			*param
		} else {
			self.types.intern_tuple(&param_types)
		};
		let type_args: Vec<TypeIndex> = self
			.type_envs
			.params(type_env)
			.iter()
			.map(|param| param.ty)
			.collect();
		let function_type =
			self.types.intern_function(function_index, &type_args);
		// Each value is judged as the member's own (`CheckAssocValue`), so a
		// loop through it (`func f() -> f::Result`) is reported once, here.
		let call_trait = self.defs.intrinsics.call.expect(
			"checked by impls.rs's dispatch pass before any signature is resolved",
		);
		let args_span = match &signature.params[..] {
			[param] => param.inner.inner.ty.as_ref().map(|ty| ty.span),
			_ => None,
		};
		let result_span = signature.result.as_ref().map(|result| result.span);
		for (provider, value, span) in [
			(function_impls.args_assoc_type_index, args, args_span),
			(
				function_impls.result_assoc_type_index,
				return_type,
				result_span,
			),
		] {
			if value == TypeIndex::ERROR {
				continue;
			}
			let name = self.defs.assoc_types[usize::from(provider)].name.inner;
			let Some(MemberKind::AssociatedType(declaration)) = self
				.defs
				.declared_trait_member(call_trait, BindingKey::ty(name))
			else {
				continue;
			};
			self.register_obligation(Obligation::CheckAssocValue {
				member: ImplMember {
					impl_index: function_impls.call_impl_index,
					declaration,
				},
				reference: SourceSpan::new(file_id, span.unwrap_or(name_span)),
			});
		}
		self.assoc_types[usize::from(function_impls.args_assoc_type_index)] =
			Some(AssocTypeSignature {
				declared_bounds: Box::new([]),
				facts: BoundFacts::Ready(Box::new([])),
				value: Some(args),
			});
		self.assoc_types[usize::from(function_impls.result_assoc_type_index)] =
			Some(AssocTypeSignature {
				declared_bounds: Box::new([]),
				facts: BoundFacts::Ready(Box::new([])),
				value: Some(return_type),
			});
		for trait_impl_index in [
			function_impls.call_impl_index,
			function_impls.function_impl_index,
		] {
			self.trait_impls[usize::from(trait_impl_index)] =
				Some(TraitImplSignature {
					type_params: type_env,
					target: Spanned {
						inner: function_type,
						span: name_span,
					},
				});
		}

		self.functions[usize::from(function_index)] = FunctionSignature {
			type_params: type_env,
			param_types,
			return_type,
		};
		SignatureLocation::Function(function_index)
	}

	/// Resolve a member in its parent's scope (the trait's or the impl's),
	/// with a child frame for method generics; `self_type` is what `Self`
	/// means there. Definition collection already validates receiver position.
	fn resolve_member_function_signature(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		function_index: FunctionIdx,
		parent: TypeEnvIdx,
		self_type: TypeIndex,
		signature: &ast::FunctionSignature,
	) -> SignatureLocation {
		let scope = self.resolve_generic_params(
			file_id,
			namespace,
			TypeEnvOwner::Function(function_index),
			parent,
			&signature.type_params,
		);

		// Definition collection diagnoses misplaced receivers. Only an
		// untyped first `self` gets the enclosing Self type here.
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
				// The parent frame binds Self to the trait parameter or impl target.
				None if index == 0 && is_method => self_type,
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

		self.functions[usize::from(function_index)] = FunctionSignature {
			type_params: scope,
			param_types: param_types.into_boxed_slice(),
			return_type,
		};
		SignatureLocation::Function(function_index)
	}

	/// Resolve a constant's required annotation in its declaration scope.
	fn resolve_constant_signature(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		const_index: ConstIdx,
		scope: TypeEnvIdx,
		name: Spanned<SymbolU32>,
		ty: Option<&Spanned<ast::TypeExpression>>,
	) -> SignatureLocation {
		let ty = match ty {
			Some(ty) => self.resolve_type(
				file_id,
				namespace,
				scope,
				ty,
				InferPolicy::Reject(InferSignatureKind::Const),
			),
			None => {
				self.diagnostics
					.push(report_missing_constant_type(file_id, name));
				TypeIndex::ERROR
			}
		};
		self.constants[usize::from(const_index)] =
			ConstantSignature { ty, scope };
		SignatureLocation::Constant(const_index)
	}

	/// Checks a constant's initializer into its `Body` (`const_bodies`), once.
	/// On demand: evaluating one constant may need another's body first.
	pub(super) fn ensure_const_body(&mut self, const_index: ConstIdx) {
		if self.const_bodies[usize::from(const_index)].is_some() {
			return;
		}
		let def_id = DefId::Const(const_index);
		let entry =
			&self.ast_nodes[self.query_state[&def_id].ast_index as usize];
		let (file_id, namespace) = (entry.file_id, entry.namespace);
		let value = match entry.node {
			AstNodeRef::Constant { item, .. } => {
				let ast::Item::Const { value, .. } = item else {
					unreachable!()
				};
				value
			}
			AstNodeRef::TraitConst { item, .. } => {
				let ast::TraitItem::Const { value, .. } = item else {
					unreachable!()
				};
				// A required trait constant has no initializer.
				let Some(value) = value else {
					return;
				};
				value
			}
			AstNodeRef::TraitImplConstant { item, .. }
			| AstNodeRef::InherentImplConst { item, .. } => {
				let ast::ImplItem::Constant { value, .. } = item else {
					unreachable!()
				};
				value
			}
			AstNodeRef::EnumVariant {
				enum_index, item, ..
			} => {
				let repr = self.enum_repr(enum_index);
				// The run is contiguous (`EnumDef::variants`), so the variant
				// before this one is the constant before it.
				let first =
					self.defs.enums[usize::from(enum_index)].variants.start;
				let previous = (const_index != first)
					.then(|| ConstIdx::new(u32::from(const_index) - 1));
				let body = BodyContext::new(
					self,
					file_id,
					namespace,
					TypeEnvIdx::ROOT,
				)
				.check_variant_value(item, previous, repr);
				self.const_bodies[usize::from(const_index)] = Some(body);
				return;
			}
			_ => unreachable!("a constant's entry is a constant"),
		};
		let scope = self.constants[usize::from(const_index)].scope;
		let ty = self.constants[usize::from(const_index)].ty;
		let body = BodyContext::new(self, file_id, namespace, scope)
			.check_body(value, ty);
		self.const_bodies[usize::from(const_index)] = Some(body);
	}

	/// Resolves and validates a `memory` declaration's `Size` and fills in
	/// its synthetic `Memory` impl. Shared by `AstNodeRef::Memory` and
	/// `AstNodeRef::ImportedMemory` — a declared memory and an imported one
	/// resolve identically once their `size` type expression is in hand.
	fn resolve_memory_signature(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		memory_index: MemoryIdx,
		name: Spanned<SymbolU32>,
		size: &Spanned<ast::TypeExpression>,
	) -> SignatureLocation {
		let memory_def = &self.defs.memories[usize::from(memory_index)];
		let trait_impl_index = memory_def.trait_impl_index;
		let size_assoc_type_index = memory_def.size_assoc_type_index;

		let resolved_size = self.resolve_assoc_value(
			file_id,
			namespace,
			TypeEnvIdx::ROOT,
			trait_impl_index,
			size_assoc_type_index,
			size,
		);

		// `Size`'s actual constraint (`PointerSize`) lives on `Memory`'s own
		// declaration, not hardcoded here: the check recorded below validates
		// against it, the same path any other associated-type binding takes.
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
		let checked_size = self.record_bounds_check(
			TypeEnvIdx::ROOT,
			BoundRequirements::AssociatedType(declared_size_index),
			Spanned {
				inner: resolved_size,
				span: size.span,
			},
			SourceSpan::new(file_id, size.span),
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
				});
		}
		SignatureLocation::Global(global_index)
	}

	fn compute_signature(
		&mut self,
		file_id: FileId,
		namespace: Scope,
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
			AstNodeRef::Constant { const_index, item } => {
				let ast::Item::Const { name, ty, .. } = item else {
					unreachable!()
				};
				self.resolve_constant_signature(
					file_id,
					namespace,
					const_index,
					TypeEnvIdx::ROOT,
					*name,
					ty.as_deref(),
				)
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
				let subject = self.type_envs.params(self_scope)[0].ty;
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
				let trait_def_id = DefId::Trait(trait_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: trait_def_id,
					requested_at: None,
				});
				let self_scope = self.traits[usize::from(trait_index)].env;
				let self_type = self.type_envs.params(self_scope)[0].ty;

				self.resolve_member_function_signature(
					file_id,
					namespace,
					function_index,
					self_scope,
					self_type,
					signature,
				)
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
				let trait_def_id = DefId::Trait(trait_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: trait_def_id,
					requested_at: None,
				});
				let self_scope = self.traits[usize::from(trait_index)].env;

				let resolved_ty = self.resolve_type(
					file_id,
					namespace,
					self_scope,
					ty,
					InferPolicy::Reject(InferSignatureKind::Const),
				);

				self.constants[usize::from(const_index)] = ConstantSignature {
					ty: resolved_ty,
					scope: self_scope,
				};
				SignatureLocation::Constant(const_index)
			}
			AstNodeRef::TraitAssocType {
				assoc_type_index,
				trait_index,
				item,
			} => {
				let ast::TraitItem::AssociatedType {
					name,
					bounds,
					value,
					..
				} = item
				else {
					unreachable!()
				};

				// See `TraitFunction`'s identical force — same reasoning:
				// this member's own declared bound can reference the
				// trait's `Self` (`type Size: Memory where { X = Self::Y }`),
				// which needs `self_scope` in scope to resolve at all.
				let trait_def_id = DefId::Trait(trait_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: trait_def_id,
					requested_at: None,
				});
				let self_scope = self.traits[usize::from(trait_index)].env;

				let base = self.type_envs.params(self_scope)[0].ty;
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
				let resolved_value = value.as_ref().map(|value| {
					self.resolve_type(
						file_id,
						namespace,
						self_scope,
						value,
						InferPolicy::Reject(
							InferSignatureKind::AssocTypeBinding,
						),
					)
				});
				self.assoc_types[usize::from(assoc_type_index)] =
					Some(AssocTypeSignature {
						declared_bounds: resolved_bounds,
						facts: BoundFacts::Ready(
							implied_bounds.into_boxed_slice(),
						),
						value: resolved_value,
					});
				SignatureLocation::AssocType(assoc_type_index)
			}
			AstNodeRef::TraitImplFunction {
				item,
				block_index,
				function_index,
			} => {
				let ast::ImplItem::Function { signature, .. } = item else {
					unreachable!()
				};
				let impl_def_id = DefId::TraitImpl(block_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let header = self.trait_impls[usize::from(block_index)]
					.as_ref()
					.expect("trait impl header is resolved");
				let (scope, self_type) =
					(header.type_params, header.target.inner);
				self.resolve_member_function_signature(
					file_id,
					namespace,
					function_index,
					scope,
					self_type,
					signature,
				)
			}
			AstNodeRef::TraitImplConstant {
				item,
				block_index,
				const_index,
			} => {
				let ast::ImplItem::Constant { name, ty, .. } = item else {
					unreachable!()
				};
				let impl_def_id = DefId::TraitImpl(block_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let scope = self.trait_impls[usize::from(block_index)]
					.as_ref()
					.expect("trait impl header is resolved")
					.type_params;
				self.resolve_constant_signature(
					file_id,
					namespace,
					const_index,
					scope,
					*name,
					ty.as_deref(),
				)
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
				// what this member actually needs, the target type a `Self`
				// written here means — before resolving anything against
				// it. Same reasoning as `TraitFunction`'s force of
				// its trait, and equally cycle-free: an impl's own header
				// only ever depends on other items' signatures, never on
				// one of its own members'.
				let impl_def_id = DefId::TraitImpl(block_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let scope = self.trait_impls[usize::from(block_index)]
					.as_ref()
					.expect(
						"an impl's own header resolves before any of its members are forced",
					)
					.type_params;

				let resolved_ty = self.resolve_assoc_value(
					file_id,
					namespace,
					scope,
					block_index,
					assoc_type_index,
					ty,
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
			AstNodeRef::ImportedMemory {
				memory_index, decl, ..
			} => {
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
					Some(ty) => {
						let global_def =
							&self.defs.globals[usize::from(global_index)];
						self.resolve_assoc_value(
							file_id,
							namespace,
							TypeEnvIdx::ROOT,
							global_def.trait_impl_index,
							global_def.value_assoc_type_index,
							ty,
						)
					}
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
			AstNodeRef::ImportedGlobal {
				global_index, decl, ..
			} => {
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
				let global_def = &self.defs.globals[usize::from(global_index)];
				let resolved_value = self.resolve_assoc_value(
					file_id,
					namespace,
					TypeEnvIdx::ROOT,
					global_def.trait_impl_index,
					global_def.value_assoc_type_index,
					ty,
				);
				self.resolve_global_signature(
					global_index,
					*name,
					*mut_span,
					resolved_value,
				)
			}
			AstNodeRef::Struct { struct_index, item } => {
				let ast::Item::Struct {
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
				..
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
				self.inherent_impls[usize::from(block_index)] =
					Some(InherentImplSignature {
						type_params: scope,
						target: Spanned {
							inner: target_type,
							span: target.span(),
						},
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

				// Forces the impl block's own header — its generic params and
				// target type — before resolving anything against it. Can
				// never close a cycle back through *this* member: the
				// block's own header only depends on its target path/
				// generic bounds, never on one of its members' signatures.
				let impl_def_id = DefId::InherentImpl(block_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let header = self.inherent_impls[usize::from(block_index)]
					.as_ref()
					.expect("inherent impl header is resolved");
				let (scope, self_type) =
					(header.type_params, header.target.inner);
				self.resolve_member_function_signature(
					file_id,
					namespace,
					function_index,
					scope,
					self_type,
					signature,
				)
			}
			AstNodeRef::InherentImplConst {
				const_index,
				item,
				block_index,
			} => {
				let ast::ImplItem::Constant { name, ty, .. } = item else {
					unreachable!()
				};
				// See `InherentImplFunction`'s identical force — same
				// reasoning.
				let impl_def_id = DefId::InherentImpl(block_index);
				let _ = self.ensure_signature(QueryInfo {
					def_id: impl_def_id,
					requested_at: None,
				});
				let scope = self.inherent_impls[usize::from(block_index)]
					.as_ref()
					.expect("inherent impl header is resolved")
					.type_params;

				self.resolve_constant_signature(
					file_id,
					namespace,
					const_index,
					scope,
					*name,
					ty.as_deref(),
				)
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
				self.trait_impls[usize::from(block_index)] =
					Some(TraitImplSignature {
						type_params: scope,
						target: Spanned {
							inner: target_type,
							span: target.span(),
						},
					});
				// A default this impl inherits means something here that it
				// does not in the trait, so the impl owns its judgement; a
				// member the impl writes is checked where it is written.
				if let Some(trait_def) = header.trait_def {
					let trait_members =
						&self.defs.traits[usize::from(trait_def.inner)].members;
					for trait_member in trait_members {
						let declaration @ MemberKind::AssociatedType(index) =
							trait_member.kind
						else {
							continue;
						};
						if let TraitMemberSelection::TraitDeclaration(_) = self
							.defs
							.select_trait_member(block_index, declaration)
						{
							self.register_obligation(
								Obligation::CheckAssocValue {
									member: ImplMember {
										impl_index: block_index,
										declaration: index,
									},
									reference: SourceSpan::new(
										file_id,
										target.span(),
									),
								},
							);
						}
					}
				}
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
			// A variant is a constant of its enum's type; its value, written or
			// counted from the previous variant, is a value of the enum's repr.
			AstNodeRef::EnumVariant {
				const_index,
				enum_index,
				..
			} => {
				let ty = self.types.intern(Type::Enum { enum_index });
				self.constants[usize::from(const_index)] = ConstantSignature {
					ty,
					scope: TypeEnvIdx::ROOT,
				};
				SignatureLocation::Constant(const_index)
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
				let subject = self.type_envs.params(self_scope)[0].ty;
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
					// No frame: a typeset member is a concrete type by
					// construction (it's the thing being implemented for),
					// and the synthetic impl has no members of its own to
					// write a `Self` reference in (see the `TypeSetSignature`
					// doc comment).
					self.trait_impls[usize::from(impl_index)] =
						Some(TraitImplSignature {
							type_params: TypeEnvIdx::ROOT,
							target: target_spanned,
						});
					resolved_members.push(target_spanned);
				}

				self.typesets[usize::from(typeset_index)] = TypeSetSignature {
					members: resolved_members.into_boxed_slice(),
				};
				SignatureLocation::TypeSet(typeset_index)
			}
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

	/// A tag is an ordinary type with an additional Memory requirement.
	fn resolve_memory_tag(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		env: TypeEnvIdx,
		segments: &[ast::PathSegment],
		infer_policy: InferPolicy,
	) -> TypeIndex {
		let ty = self.resolve_type_path(
			file_id,
			namespace,
			env,
			segments,
			infer_policy,
		);
		if ty == TypeIndex::ERROR {
			return ty;
		}
		let required = self
			.defs
			.intrinsics
			.memory
			.expect("memory tags require the intrinsic Memory trait");
		let reference = SourceSpan::new(
			file_id,
			TextSpan::new(
				segments[0].ident.span.start,
				segments.last().unwrap().ident.span.end,
			),
		);
		let obligation = Obligation::CheckTraitMembership {
			assumption_context: env,
			subject: ty,
			required,
			reference,
		};
		self.register_obligation(obligation);
		ty
	}

	/// The memory a pointer/slice/array type belongs to — an explicit
	/// `heap::` tag if it has one, the ambient one otherwise. Shared by
	/// `Pointer`/`Slice`/`Array`'s three arms in `resolve_type`, which
	/// otherwise differ only in which `Type` variant they intern.
	fn resolve_pointer_memory(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		env: TypeEnvIdx,
		memory: &Option<Box<[ast::PathSegment]>>,
		span: TextSpan,
		infer_policy: InferPolicy,
	) -> Result<TypeIndex, ()> {
		match memory {
			Some(segments) => Ok(self.resolve_memory_tag(
				file_id,
				namespace,
				env,
				segments,
				infer_policy,
			)),
			None => self.resolve_ambient_memory(file_id, span),
		}
	}

	/// Resolve a written signature type. `_` follows the caller's inference
	/// policy; nominal types retain their structure. The type is stored as
	/// written, with projections unreduced; the declaration check normalizes it once
	/// to find cycles, and readers normalize under their own assumptions.
	fn resolve_type(
		&mut self,
		file_id: FileId,
		namespace: Scope,
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
		if ty != TypeIndex::ERROR {
			self.register_obligation(Obligation::CheckWellFormed {
				assumption_context: env,
				ty,
				reference: SourceSpan::new(file_id, type_expr.span),
			});
		}
		ty
	}

	/// Resolve the value an impl supplies for an associated type: a written
	/// member, or a memory's `Size` / a global's `Value`. Like `resolve_type`,
	/// but the generic well-formedness check is replaced by the member's own
	/// (`CheckAssocValue`), which reports the verdict the solver records for
	/// it; `scope` is the impl's `Self` scope. A value the trait does not
	/// declare is never selected, so it only gets the generic check.
	fn resolve_assoc_value(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		scope: TypeEnvIdx,
		impl_index: TraitImplIdx,
		provider: AssocTypeIdx,
		type_expr: &Spanned<ast::TypeExpression>,
	) -> TypeIndex {
		let infer_policy =
			InferPolicy::Reject(InferSignatureKind::AssocTypeBinding);
		let declaration = self
			.impl_dispatch
			.trait_header(impl_index)
			.trait_def
			.and_then(|trait_def| {
				let name = self.defs.assoc_types[usize::from(provider)].name;
				self.defs.declared_trait_member(
					trait_def.inner,
					BindingKey::ty(name.inner),
				)
			});
		let Some(MemberKind::AssociatedType(declaration)) = declaration else {
			return self.resolve_type(
				file_id,
				namespace,
				scope,
				type_expr,
				infer_policy,
			);
		};
		let ty = self.resolve_type_expression(
			file_id,
			namespace,
			scope,
			type_expr,
			infer_policy,
		);
		// Lowering that failed has already reported; nothing to judge.
		if ty != TypeIndex::ERROR {
			self.register_obligation(Obligation::CheckAssocValue {
				member: ImplMember {
					impl_index,
					declaration,
				},
				reference: SourceSpan::new(file_id, type_expr.span),
			});
		}
		ty
	}

	/// Resolve both ordinary type paths and explicit memory tags.
	fn resolve_type_path(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		env: TypeEnvIdx,
		segments: &[ast::PathSegment],
		infer_policy: InferPolicy,
	) -> TypeIndex {
		// The first segment tries `TypeEnv` regardless of how many
		// segments follow — `Self::Value`/`T::Size` never touch the
		// namespace graph at all for their own first hop, same as a
		// bare `T`/`Self` doesn't. Only once that fails does the
		// namespace graph get a turn. Either branch leaves `next`
		// at the first segment *not yet* consumed. Written arguments
		// don't change what the name means: a parameter shadows an
		// item of the same name with or without them, and takes none.
		let first = &segments[0];
		let parameter = self
			.type_envs
			.resolve(env, first.ident.inner)
			.map(|(frame, index)| {
				(
					Referent::TypeParam { env: frame, index },
					self.type_envs.params(frame)[index as usize].ty,
				)
			})
			.or_else(|| {
				(first.ident.inner == Keyword::SelfPascal.symbol())
					.then(|| self.resolve_impl_self(env))
					.flatten()
			});
		let (current, next) = if let Some((referent, ty)) = parameter {
			self.resolutions.by_site.insert(
				(SourceSpan::new(file_id, first.ident.span), Tier::Type),
				referent,
			);
			if !first.type_args.is_empty() {
				// Resolved only to report what is wrong inside them.
				for arg in &first.type_args {
					self.resolve_type_expression(
						file_id,
						namespace,
						env,
						arg,
						infer_policy,
					);
				}
				self.diagnostics.push(report_type_arg_count_mismatch(
					self.strings,
					self.defs,
					file_id,
					first,
					TypeArgsTarget::TypeParam,
				));
			}
			(ty, 1)
		} else {
			// TODO: this probably should be resolve_path instead of walk_path
			let walk = PathResolver::new(
				self.diagnostics,
				self.resolutions,
				self.strings,
				self.defs,
			)
			.walk_path(file_id, namespace, segments, Tier::Type);
			let Some(def_key) = walk.target.def_key() else {
				return TypeIndex::ERROR;
			};
			let stopped = &segments[walk.stopped_at as usize];
			if let BindingTarget::Inaccessible(_) = walk.target {
				self.diagnostics.push(report_private_identifier(
					&self.defs.namespaces,
					self.strings,
					stopped.ident.inner,
					SourceSpan::new(file_id, stopped.ident.span),
					Some(def_key),
				));
			}

			let resolved = match def_key.symbol_kind(self.defs) {
				DefKind::TypeAlias(type_alias_index) => {
					let def_id = DefId::TypeAlias(type_alias_index);
					let reference =
						SourceSpan::new(file_id, stopped.ident.span);
					let status = self.ensure_signature(QueryInfo {
						def_id,
						requested_at: Some(reference),
					});
					match status {
						SignatureStatus::Cycle => {
							let diagnostic = self
								.report_cyclic_type_alias(def_id, reference);
							self.diagnostics.push(diagnostic);
							TypeIndex::ERROR
						}
						SignatureStatus::CycleReported => TypeIndex::ERROR,
						SignatureStatus::Available(
							SignatureLocation::TypeAlias(index),
						) => {
							let TypeAliasSignature {
								type_params,
								target,
							} = self.type_aliases[usize::from(index)];
							let resolved_args: Box<[TypeIndex]> = stopped
								.type_args
								.iter()
								.map(|arg| {
									self.resolve_type_expression(
										file_id,
										namespace,
										env,
										arg,
										infer_policy,
									)
								})
								.collect();
							let type_args = self.resolve_type_args(
								env,
								file_id,
								stopped,
								type_params,
								&resolved_args,
								TypeEnvOwner::TypeAlias(index),
							);
							self.types.substitute(
								target,
								Substitution {
									env: type_params,
									args: &type_args,
								},
							)
						}
						SignatureStatus::Available(_) => unreachable!(
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
					let def_id = DefId::Struct(struct_index);
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
					let params_env =
						self.structs[usize::from(struct_index)].type_params;

					let resolved_args: Box<[TypeIndex]> = stopped
						.type_args
						.iter()
						.map(|arg| {
							self.resolve_type_expression(
								file_id,
								namespace,
								env,
								arg,
								infer_policy,
							)
						})
						.collect();
					let type_args = self.resolve_type_args(
						env,
						file_id,
						stopped,
						params_env,
						&resolved_args,
						TypeEnvOwner::Struct(struct_index),
					);
					self.types.intern_struct(struct_index, &type_args)
				}
				DefKind::Enum(enum_index) => {
					if !stopped.type_args.is_empty() {
						// Resolved only to report what is wrong inside them.
						for arg in &stopped.type_args {
							self.resolve_type_expression(
								file_id,
								namespace,
								env,
								arg,
								infer_policy,
							);
						}
						self.diagnostics.push(report_type_arg_count_mismatch(
							self.strings,
							self.defs,
							file_id,
							stopped,
							TypeArgsTarget::Item {
								owner: TypeEnvOwner::Enum(enum_index),
								params: &[],
							},
						));
						TypeIndex::ERROR
					} else {
						// Nominal identity is available from definition collection;
						// naming an enum does not depend on resolving its repr.
						self.types.intern(Type::Enum { enum_index })
					}
				}
				// Every memory declaration is its own nominal type,
				// including when referenced as a memory tag.
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
				// A free function is its own zero-sized type, applied
				// like a struct (`foo<i32>`). The type-param frame is
				// pushed before the parameters are lowered, so a
				// function naming itself reads a valid `type_params`.
				DefKind::Function(func_index) => {
					let def_id = DefId::Function(func_index);
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
					let params_env =
						self.functions[usize::from(func_index)].type_params;
					let resolved_args: Box<[TypeIndex]> = stopped
						.type_args
						.iter()
						.map(|arg| {
							self.resolve_type_expression(
								file_id,
								namespace,
								env,
								arg,
								infer_policy,
							)
						})
						.collect();
					let type_args = self.resolve_type_args(
						env,
						file_id,
						stopped,
						params_env,
						&resolved_args,
						TypeEnvOwner::Function(func_index),
					);
					self.types.intern_function(func_index, &type_args)
				}
				// Every global is its own nominal type, the one its
				// `Global` impl targets; it takes no arguments.
				kind @ DefKind::Global(global_index) => {
					if stopped.type_args.is_empty() {
						self.types.intern(Type::Global { global_index })
					} else {
						// Resolved only to report what is wrong inside them.
						for arg in &stopped.type_args {
							self.resolve_type_expression(
								file_id,
								namespace,
								env,
								arg,
								infer_policy,
							);
						}
						self.diagnostics.push(report_type_arg_count_mismatch(
							self.strings,
							self.defs,
							file_id,
							stopped,
							TypeArgsTarget::Namespace(kind),
						));
						TypeIndex::ERROR
					}
				}
				// Value-tier only — a `Tier::Type` walk
				// can never stop on one of these.
				DefKind::EnumVariant(_) | DefKind::Const(_) => unreachable!(
					"value-tier DefKind from a type-namespace path walk"
				),
				// Never constructed anywhere — associated types are
				// only ever reached through `resolve_type_member_path`'s
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
		self.resolve_type_member_path(env, file_id, current, &segments[next..])
	}

	/// Resolve identities and structure without reducing the resulting type.
	/// Member lookup can still normalize a receiver when needed to discover a
	/// member, but stored equality expressions retain symbolic projections.
	fn resolve_type_expression(
		&mut self,
		file_id: FileId,
		namespace: Scope,
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
			ast::TypeExpression::Never => TypeIndex::NEVER,
			ast::TypeExpression::Path(segments) => self.resolve_type_path(
				file_id,
				namespace,
				env,
				segments,
				infer_policy,
			),
			ast::TypeExpression::Grouped { inner, segments } => {
				// `<T>::Item` — no namespace prefix to consume first
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
				self.resolve_type_member_path(env, file_id, current, segments)
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
				let Ok(member) = self.resolve_trait_qualified_assoc_type(
					env,
					base_ty,
					required_trait,
					first.ident,
					file_id,
				) else {
					return TypeIndex::ERROR;
				};
				let current = self.project_assoc_type(base_ty, member);

				self.resolve_type_member_path(
					env,
					file_id,
					current,
					&segments[1..],
				)
			}
			ast::TypeExpression::Function { params, result } => {
				// One parameter type: a single one is itself, any other count
				// is its tuple (`()` for none).
				let param = if let [param] = &params[..] {
					self.resolve_type_expression(
						file_id,
						namespace,
						env,
						&param.inner.inner.ty,
						infer_policy,
					)
				} else {
					let mut elements = Vec::with_capacity(params.len());
					for param in params.iter() {
						elements.push(self.resolve_type_expression(
							file_id,
							namespace,
							env,
							&param.inner.inner.ty,
							infer_policy,
						));
					}
					self.types.intern_tuple(&elements)
				};
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
				self.types.intern(Type::FunctionRef {
					param,
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
					env,
					memory,
					type_expr.span,
					infer_policy,
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
					env,
					memory,
					type_expr.span,
					infer_policy,
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
					env,
					memory,
					type_expr.span,
					infer_policy,
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
				self.types.intern_tuple(&elems)
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

		let root_name = self.defs.name(def_id);
		let root_name_str = self.strings.resolve(root_name.inner).unwrap();

		let mut diagnostic = Diagnostic::error()
			.with_code(code.code())
			.with_message(format!(
				"cycle detected when {}",
				describe(root_name_str)
			))
			.with_label(hop_span(0).primary_label());

		for (i, frame) in chain.iter().enumerate().skip(1) {
			let name = self.defs.name(frame.def_id);
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
			let name = self.defs.name(frame.def_id);
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
		match *self.types.resolve(ty) {
			Type::Struct { struct_index, .. } => {
				let embedded_def_id = DefId::Struct(struct_index);
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
				for i in 0..elements.len() {
					let element = self.types.list(elements)[i];
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
		namespace: Scope,
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
			&& matches!(self.type_envs.owner(env), TypeEnvOwner::Trait(_))
		{
			for occurrence in &occurrences {
				let def_id = match self.defs.traits
					[usize::from(occurrence.trait_index)]
				.typeset
				{
					Some(typeset_index) => DefId::Typeset(typeset_index),
					None => DefId::Trait(occurrence.trait_index),
				};
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
		self.fill_source_bounds(file_id, namespace, env, &occurrences);
		let ids: Box<[BoundId]> = occurrences.iter().map(|o| o.id).collect();
		let implied = self.compute_implied_bounds(&ids, name, subject);
		(ids, implied)
	}

	/// Walks a bound expression exactly once, resolving trait paths,
	/// reserving a `BoundId` per accepted occurrence, and reporting the
	/// "not an associated type"/duplicate-binding diagnostics. The result is
	/// consumed twice — once by `provisional_from_occurrences` to publish
	/// direct memberships (no equality RHS types resolved), once by
	/// `fill_source_bounds` to resolve those RHS types and fill in
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
		namespace: Scope,
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
	fn fill_source_bounds(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		env: TypeEnvIdx,
		occurrences: &[BoundOccurrence<'_>],
	) {
		for occurrence in occurrences {
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
						self.fill_source_bounds(
							file_id, namespace, env, nested,
						);
						BindingRequirement::Bound(
							nested.iter().map(|o| o.id).collect(),
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
		}
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
		namespace: Scope,
		segments: &[ast::PathSegment],
	) -> Option<TraitIdx> {
		let def_key = PathResolver::new(
			self.diagnostics,
			self.resolutions,
			self.strings,
			self.defs,
		)
		.resolve_definition(file_id, namespace, segments, Tier::Type)
		.ok()?;
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

fn report_missing_constant_type(
	file_id: FileId,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingConstantType.code())
		.with_message("missing type for `const` item")
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("expected `: Type` here"),
		)
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
	use crate::tir::defs::{DefinitionRegistry, Namespace, Scope, UseItemKind};
	use crate::tir::impls::ImplTarget;
	use crate::tir::solver::AssocValue;
	use crate::vfs;

	/// `test_case!(case = "source")` / `test_case!(mut case = ..)` /
	/// `test_case!(case from graph)` declare the graph, inputs and swept
	/// `TestCase` borrowing them as three locals of the calling test.
	macro_rules! test_case {
		($case:ident = $source:expr $(,)?) => {
			test_case!($case from source_graph($source));
		};
		(mut $case:ident = $source:expr $(,)?) => {
			test_case!(mut $case from source_graph($source));
		};
		($case:ident from $graph:expr) => {
			let mut graph = $graph;
			let mut inputs = TestInputs::new(&mut graph);
			let $case = TestCase::new(&mut inputs);
		};
		(mut $case:ident from $graph:expr) => {
			let mut graph = $graph;
			let mut inputs = TestInputs::new(&mut graph);
			let mut $case = TestCase::new(&mut inputs);
		};
	}

	/// The shipped `std/main.wx` is the largest real input the sweep sees; it
	/// must stay free of diagnostics through every change to the solver.
	#[test]
	fn the_embedded_stdlib_sweeps_without_diagnostics() {
		test_case!(case = include_str!("../../std/main.wx"));
		case.diagnostics().assert_none();
	}

	/// Every written name lands in one table, whichever stage resolved it:
	/// `use` paths in phase 1, path segments in the walk, generic parameters
	/// and selected members during signature construction.
	#[test]
	fn every_resolved_name_is_recorded_where_it_is_written() {
		const SOURCE: &str = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			mod m { pub struct S(); pub trait Tr { type A; } }
			mod g { pub struct G(); }
			use m::S;
			use g::*;
			struct T();
			func f<T: m::Tr>(a: S, b: m::S, c: T, d: T::A, e: <T as m::Tr>::A, x: G) {}
		"};
		test_case!(case = SOURCE);
		case.diagnostics().assert_none();

		let root = Namespace::Package(case.defs.root_package);
		let file_id = case.defs.namespaces.file_id(root);
		// The span of `name` inside the first occurrence of `context`.
		let span_of = |context: &str, name: &str| {
			let start =
				SOURCE.find(context).unwrap() + context.find(name).unwrap();
			TextSpan::new(start as u32, (start + name.len()) as u32)
		};
		let at =
			|context: &str, name: &str| {
				let site = (
					SourceSpan::new(file_id, span_of(context, name)),
					Tier::Type,
				);
				*case.context.resolutions.by_site.get(&site).unwrap_or_else(
					|| panic!("`{name}` in `{context}` is not recorded"),
				)
			};
		let declared = |referent: Referent| {
			let Referent::Definition(def_key) = referent else {
				panic!("expected a declared definition, got {referent:?}");
			};
			def_key.symbol_kind(case.defs)
		};
		let imported = |referent: Referent| {
			let Referent::Import { definition, import } = referent else {
				panic!("expected an imported definition, got {referent:?}");
			};
			(
				definition.symbol_kind(case.defs),
				&case.defs.use_items[usize::from(import)].kind,
			)
		};
		let assoc_a = |referent: Referent| {
			let Referent::Member(MemberKind::AssociatedType(index)) = referent
			else {
				panic!("expected an associated type, got {referent:?}");
			};
			assert_eq!(
				case.graph.strings.resolve(
					case.defs.assoc_types[usize::from(index)].name.inner
				),
				Some("A")
			);
		};
		let struct_s = DefKind::Struct(case.struct_index("m::S"));
		let struct_g = DefKind::Struct(case.struct_index("g::G"));
		let tr = DefKind::Trait(case.trait_index("m::Tr"));
		let param_t = Referent::TypeParam {
			env: case.function_signature("f").type_params,
			index: 0,
		};

		// Phase 1: both segments of the `use` path, each declared in the
		// namespace it was looked up in.
		assert!(matches!(declared(at("use m::S", "m")), DefKind::Module(_)));
		assert_eq!(declared(at("use m::S", "S")), struct_s);

		// The walk: a name visible through a named `use` or a glob names that
		// `use` item next to the definition.
		let (definition, import) = imported(at("a: S", "S"));
		assert_eq!(definition, struct_s);
		assert!(matches!(
			import,
			UseItemKind::Name { name, .. } if name.span == span_of("use m::S", "S")
		));
		let (definition, import) = imported(at("x: G", "G"));
		assert_eq!(definition, struct_g);
		assert!(matches!(
			import,
			UseItemKind::Glob { span, .. } if *span == span_of("use g::*", "g::*")
		));
		assert!(matches!(declared(at("b: m::S", "m")), DefKind::Module(_)));
		assert_eq!(declared(at("b: m::S", "S")), struct_s);
		assert_eq!(declared(at("T: m::Tr", "Tr")), tr);

		// Generic parameters shadow the struct `T`, and members are selected.
		assert_eq!(at("c: T", "T"), param_t);
		assert_eq!(at("d: T::A", "T"), param_t);
		assoc_a(at("d: T::A", "A"));
		assert_eq!(at("<T as m::Tr>", "T"), param_t);
		assert_eq!(declared(at("<T as m::Tr>", "Tr")), tr);
		assoc_a(at("<T as m::Tr>::A", "A"));
	}

	#[test]
	fn a_name_that_does_not_resolve_is_not_recorded() {
		test_case!(
			case = "pub trait Call { type Args; type Result; } pub trait Function: Call {} func f(x: Missing) {}"
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
		// Only the supertrait `Call` resolves.
		assert_eq!(case.context.resolutions.by_site.len(), 1);
	}

	#[test]
	fn builtin_operators_match_the_stdlib_impls() {
		use crate::tir::operators::{
			Scalar, is_builtin_binary, is_builtin_unary,
		};
		// The compiler builds `Binary`/`Unary` exactly where the stdlib has a
		// primitive impl, so the two must name the same pairs.
		test_case!(case = include_str!("../../std/main.wx"));
		let implements = |trait_index: TraitIdx, scalar: Scalar| {
			let target =
				ImplTarget::from_type(case.context.types.resolve(scalar.ty()))
					.unwrap();
			case.context
				.impl_dispatch
				.trait_candidates(target)
				.iter()
				.any(|&(implemented, _)| implemented == trait_index)
		};
		for op in [
			ast::BinaryOp::Add,
			ast::BinaryOp::Sub,
			ast::BinaryOp::Mul,
			ast::BinaryOp::Div,
			ast::BinaryOp::Rem,
			ast::BinaryOp::BitAnd,
			ast::BinaryOp::BitOr,
			ast::BinaryOp::BitXor,
			ast::BinaryOp::LeftShift,
			ast::BinaryOp::RightShift,
			ast::BinaryOp::Eq,
			ast::BinaryOp::NotEq,
			ast::BinaryOp::Less,
			ast::BinaryOp::LessEq,
			ast::BinaryOp::Greater,
			ast::BinaryOp::GreaterEq,
		] {
			let method =
				case.context.operators.binary(op).unwrap_or_else(|| {
					panic!("`{}` has no method", op.as_str())
				});
			for scalar in Scalar::ALL {
				assert_eq!(
					implements(method.trait_index, scalar),
					is_builtin_binary(op, scalar),
					"`{}` on {scalar:?}",
					op.as_str()
				);
			}
		}
		for op in [
			ast::UnaryOp::InvertSign,
			ast::UnaryOp::BitNot,
			ast::UnaryOp::Not,
		] {
			let method = case.context.operators.unary(op).unwrap();
			for scalar in Scalar::ALL {
				assert_eq!(
					implements(method.trait_index, scalar),
					is_builtin_unary(op, scalar),
					"{op:?} on {scalar:?}"
				);
			}
		}
	}

	mod const_initializers {
		use super::*;
		use crate::tir::body::{ArgOrder, Body, ExprIdx, ExprKind};
		use crate::tir::eval::{ConstValue, ConstValueState};
		use crate::tir::operators::Scalar;

		/// Test items appended to the real stdlib, so operators are checked
		/// against its actual traits and impls.
		fn with_std(source: &str) -> String {
			format!("{}\n{source}", include_str!("../../std/main.wx"))
		}

		fn body<'c>(case: &'c TestCase<'_>, name: &str) -> &'c Body {
			let (DefKind::Const(index) | DefKind::EnumVariant(index)) =
				case.resolve(Tier::Value, name)
			else {
				panic!("expected `{name}` to be a constant");
			};
			case.context.const_bodies[usize::from(index)]
				.as_ref()
				.expect("a constant with an initializer has a body")
		}

		/// The checked tree as an S-expression, each node with its type:
		/// `(+ 1:u8 2:u8):u8`.
		fn shape(case: &TestCase<'_>, name: &str) -> String {
			fn render(
				case: &TestCase<'_>,
				body: &Body,
				expr: ExprIdx,
			) -> String {
				let node = match body.kind(expr) {
					ExprKind::Error => "error".to_string(),
					ExprKind::Unsupported => "unsupported".to_string(),
					ExprKind::Int(value) => value.to_string(),
					ExprKind::Float(value) => format!("{value:?}"),
					ExprKind::Bool(value) => value.to_string(),
					ExprKind::Char(value) => format!("{value:?}"),
					ExprKind::Const(index) => {
						let name =
							case.defs.constants[usize::from(index)].name.inner;
						case.graph.strings.resolve(name).unwrap().to_string()
					}
					ExprKind::NextDiscriminant(index) => {
						let name =
							case.defs.constants[usize::from(index)].name.inner;
						format!(
							"(next {})",
							case.graph.strings.resolve(name).unwrap()
						)
					}
					ExprKind::Unary { op, operand } => {
						format!(
							"({} {})",
							op.as_str(),
							render(case, body, operand)
						)
					}
					ExprKind::Binary { op, lhs, rhs } => format!(
						"({} {} {})",
						op.as_str(),
						render(case, body, lhs),
						render(case, body, rhs)
					),
					ExprKind::MethodCall { method, args }
					| ExprKind::GenericMethodCall { method, args } => {
						let generic = matches!(
							body.kind(expr),
							ExprKind::GenericMethodCall { .. }
						);
						let name =
							case.defs.functions[usize::from(method)].name.inner;
						let mut text = format!(
							"({}{}",
							if generic { "generic " } else { "call " },
							case.graph.strings.resolve(name).unwrap()
						);
						for &arg in body.args(args) {
							text.push(' ');
							text.push_str(&render(case, body, arg));
						}
						text + ")"
					}
					// A named argument shows the field it gives: `(P y=2:u8)`.
					ExprKind::Construct {
						struct_index,
						args,
						order,
					} => {
						let def = &case.defs.structs[usize::from(struct_index)];
						let strings = &case.graph.strings;
						let mut text = format!(
							"({}",
							strings.resolve(def.name.inner).unwrap()
						);
						for (at, &arg) in body.args(args).iter().enumerate() {
							text.push(' ');
							if let ArgOrder::Permuted { .. } = order {
								let field = &def.fields[usize::from(
									body.declared_index(order, at),
								)];
								let name = field.name.unwrap().inner;
								text.push_str(strings.resolve(name).unwrap());
								text.push('=');
							}
							text.push_str(&render(case, body, arg));
						}
						text + ")"
					}
				};
				let ty =
					case.context.type_formatter().display_type(body.ty(expr));
				format!("{node}:{ty}")
			}
			let body = body(case, name);
			render(case, body, body.root())
		}

		#[test]
		fn untyped_literals_take_the_declared_type() {
			test_case!(
				case = &with_std(
					"const A: u8 = 1 + 2 * 3;
					const B: i8 = -128;
					const C: f32 = 1.5;
					const D: f64 = 2;
					const E: char = 'a';
					const F: bool = true;"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(shape(&case, "A"), "(+ 1:u8 (* 2:u8 3:u8):u8):u8");
			assert_eq!(shape(&case, "B"), "(- 128:i8):i8");
			assert_eq!(shape(&case, "C"), "1.5:f32");
			assert_eq!(shape(&case, "D"), "2.0:f64");
			assert_eq!(shape(&case, "E"), "'a':char");
			assert_eq!(shape(&case, "F"), "true:bool");
		}

		#[test]
		fn a_typed_operand_types_an_untyped_one() {
			test_case!(
				case = &with_std(
					"const A: i64 = 1;
					const B: i64 = 2 * A;
					const C: bool = A < 10;
					const D: bool = A == 1 && true;"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(shape(&case, "B"), "(* 2:i64 A:i64):i64");
			assert_eq!(shape(&case, "C"), "(< A:i64 10:i64):bool");
			assert_eq!(
				shape(&case, "D"),
				"(&& (== A:i64 1:i64):bool true:bool):bool"
			);
		}

		#[test]
		fn literals_must_fit_their_type() {
			for (initializer, code) in [
				(
					"const A: u8 = 256;",
					DiagnosticCode::IntegerLiteralOutOfRange,
				),
				(
					"const A: i8 = -129;",
					DiagnosticCode::IntegerLiteralOutOfRange,
				),
				(
					"const A: i8 = 128;",
					DiagnosticCode::IntegerLiteralOutOfRange,
				),
				("const A: u32 = -1;", DiagnosticCode::UnableToCoerce),
				(
					"const A: u8 = 1 + 300;",
					DiagnosticCode::IntegerLiteralOutOfRange,
				),
				(
					"const A: f32 = 16777217;",
					DiagnosticCode::IntegerLiteralNotRepresentable,
				),
				("const A: f32 = 1e39;", DiagnosticCode::FloatLiteralOverflow),
				(
					"const A: f64 = 1e-400;",
					DiagnosticCode::FloatLiteralUnderflow,
				),
				("const A: bool = 1;", DiagnosticCode::UnableToCoerce),
				("const A: i32 = 1.5;", DiagnosticCode::UnableToCoerce),
				("const A: u8 = ^1.5;", DiagnosticCode::UnableToCoerce),
				(
					"const A: char = '';",
					DiagnosticCode::InvalidCharacterLiteral,
				),
			] {
				test_case!(case = &with_std(initializer));
				case.diagnostics().assert_codes(&[code]);
			}
		}

		#[test]
		fn operand_types_must_agree() {
			for (initializer, code) in [
				(
					"const A: i32 = 1; const B: i64 = A;",
					DiagnosticCode::TypeMistmatch,
				),
				(
					"const A: i32 = 1; const B: i32 = A + true;",
					DiagnosticCode::TypeMistmatch,
				),
				(
					"const A: bool = 1 < 2;",
					DiagnosticCode::ComparisonTypeAnnotationRequired,
				),
				(
					"const A: bool = true + false;",
					DiagnosticCode::BinaryOperatorCannotBeApplied,
				),
				(
					"const A: bool = -true;",
					DiagnosticCode::UnaryOperatorCannotBeApplied,
				),
				(
					"const A: u8 = 1; const B: u8 = -A;",
					DiagnosticCode::UnaryOperatorCannotBeApplied,
				),
				("const A: bool = true && 1;", DiagnosticCode::UnableToCoerce),
			] {
				test_case!(case = &with_std(initializer));
				case.diagnostics().assert_codes(&[code]);
			}
		}

		#[test]
		fn an_operator_on_a_user_type_calls_its_impl() {
			test_case!(
				case = &with_std(
					"struct V();
					impl Add for V { func add(self, rhs: Self) -> Self { self } }
					impl PartialEq for V { func eq(self, other: Self) -> bool { true } }
					const X: V = V();
					const Y: V = X + X;
					const Z: bool = X != X;"
				)
			);
			// `X` is a construction; `Y` and `Z` call methods, and a call is
			// not a constant.
			case.diagnostics().assert_codes(&[
				DiagnosticCode::NotConstEvaluatable,
				DiagnosticCode::NotConstEvaluatable,
			]);
			assert_eq!(shape(&case, "X"), "(V):V");
			assert_eq!(shape(&case, "Y"), "(call add X:V X:V):V");
			// `ne` is the trait's default: dispatched through the declaration.
			assert_eq!(shape(&case, "Z"), "(generic ne X:V X:V):bool");
		}

		#[test]
		fn a_literal_of_abstract_type_fits_every_typeset_member() {
			test_case!(
				case = &with_std(
					"typeset Small { u8, i8 }
					trait Holder {
						type S: Small;
						const FITS: Self::S = 100;
						const TOO_BIG: Self::S = 200;
					}"
				)
			);
			// `200` fits `u8` but not `i8`.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TypesetBoundViolation]);
		}

		#[test]
		fn a_declared_projection_type_is_normalized_first() {
			test_case!(
				case = &with_std(
					"trait Service { type Item; const VALUE: Self::Item; }
					struct S();
					impl Service for S { type Item = u16; const VALUE: Self::Item = 7; }"
				)
			);
			case.diagnostics().assert_none();
		}

		/// A constant's evaluation state; `name` may be an enum variant.
		fn state<'c>(
			case: &'c TestCase<'_>,
			name: &str,
		) -> &'c ConstValueState {
			let (DefKind::Const(index) | DefKind::EnumVariant(index)) =
				case.resolve(Tier::Value, name)
			else {
				panic!("expected `{name}` to be a constant");
			};
			&case.context.const_values[usize::from(index)]
		}

		fn value(case: &TestCase<'_>, name: &str) -> ConstValue {
			match state(case, name) {
				ConstValueState::Evaluated(value) => value.clone(),
				state => panic!("`{name}` has no value: {state:?}"),
			}
		}

		fn int(case: &TestCase<'_>, name: &str) -> i128 {
			match value(case, name) {
				ConstValue::Int { value, .. } => value,
				other => panic!("`{name}` is not an integer: {other:?}"),
			}
		}

		#[test]
		fn arithmetic_follows_the_operand_type() {
			test_case!(
				case = &with_std(
					"const A: u8 = 200 + 55;
					const B: i8 = -128;
					const C: i32 = 7 / -2;
					const D: i32 = -7 % 2;
					const E: u8 = ^1;
					const F: i8 = ^0;
					const G: u8 = 3 << 7;
					const H: i8 = -128 >> 1;
					const I: u64 = 18446744073709551615;
					const J: i64 = -9223372036854775808;
					const K: u32 = 6 & 3 | 8 ^ 1;"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(int(&case, "A"), 255);
			assert_eq!(int(&case, "B"), -128);
			// Truncating division; the remainder has the dividend's sign.
			assert_eq!(int(&case, "C"), -3);
			assert_eq!(int(&case, "D"), -1);
			assert_eq!(int(&case, "E"), 254);
			assert_eq!(int(&case, "F"), -1);
			// Bits shifted past the width are dropped, as at runtime.
			assert_eq!(int(&case, "G"), 128);
			// A right shift on a signed type is arithmetic.
			assert_eq!(int(&case, "H"), -64);
			assert_eq!(int(&case, "I"), i128::from(u64::MAX));
			assert_eq!(int(&case, "J"), i128::from(i64::MIN));
			assert_eq!(int(&case, "K"), (6 & 3) | (8 ^ 1));
		}

		#[test]
		fn floats_round_at_their_width_and_comparisons_answer_bool() {
			test_case!(
				case = &with_std(
					"const A: f32 = 0.1 + 0.2;
					const B: f64 = 0.1 + 0.2;
					const C: bool = A < 1.0;
					const D: bool = 'a' < 'b' && true != false;
					const E: f64 = 1.0 / 0.0;"
				)
			);
			case.diagnostics().assert_none();
			let ConstValue::Float { value: a, .. } = value(&case, "A") else {
				panic!()
			};
			assert_eq!(a, f64::from(0.1f32 + 0.2f32));
			let ConstValue::Float { value: b, .. } = value(&case, "B") else {
				panic!()
			};
			assert_eq!(b, 0.1 + 0.2);
			assert_eq!(value(&case, "C"), ConstValue::Bool(true));
			assert_eq!(value(&case, "D"), ConstValue::Bool(true));
			// IEEE results are values, not errors.
			let ConstValue::Float { value: e, .. } = value(&case, "E") else {
				panic!()
			};
			assert!(e.is_infinite());
		}

		#[test]
		fn constants_read_each_other_in_any_order() {
			test_case!(
				case = &with_std(
					"const A: i32 = B * 2;
					const B: i32 = C + 1;
					const C: i32 = 20;"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(int(&case, "A"), 42);
		}

		#[test]
		fn a_result_outside_the_type_is_an_error() {
			for initializer in [
				"const A: u8 = 255 + 1;",
				"const A: u8 = 0 - 1;",
				"const A: i8 = -128 - 1;",
				"const A: i8 = -(-128);",
				"const A: i16 = 200 * 200;",
				"const A: i32 = -2147483648 / -1;",
				"const A: i32 = 1 / 0;",
				"const A: i32 = 1 % 0;",
				"const A: u8 = 1 << 8;",
				"const A: i32 = 1 >> 32;",
			] {
				test_case!(case = &with_std(initializer));
				case.diagnostics()
					.assert_codes(&[DiagnosticCode::ConstEvaluationFailed]);
			}
		}

		#[test]
		fn a_constant_reading_a_failed_one_is_silent() {
			test_case!(
				case = &with_std(
					"const B: u8 = A;
					const A: u8 = 255 + 1;
					const C: bool = false && A == 1;"
				)
			);
			// `A` owns its overflow and `B` reads it silently. `C` names `A`
			// only in a branch it does not take, so it never reads it.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::ConstEvaluationFailed]);
			assert_eq!(state(&case, "B"), &ConstValueState::Poisoned);
			assert_eq!(value(&case, "C"), ConstValue::Bool(false));
		}

		#[test]
		fn a_branch_that_is_not_taken_is_not_a_dependency() {
			test_case!(
				case = &with_std(
					"const A: bool = false && B;
					const B: bool = A;"
				)
			);
			// `A` is `false` without reading `B`, so there is no loop.
			case.diagnostics().assert_none();
			assert_eq!(value(&case, "A"), ConstValue::Bool(false));
			assert_eq!(value(&case, "B"), ConstValue::Bool(false));
		}

		#[test]
		fn a_mismatched_initializer_has_no_value() {
			test_case!(
				case = &with_std(
					"enum E: i32 { A = 1 }
					const X: i32 = E::A;"
				)
			);
			// `E::A` is held as an `i32`, but it is an `E`: reported once, and
			// `X` gets no value from it.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TypeMistmatch]);
			assert_eq!(state(&case, "X"), &ConstValueState::Poisoned);
		}

		#[test]
		fn a_variant_value_naming_its_enum_reports_only_the_mismatch() {
			test_case!(case = &with_std("enum E: i32 { A = E::B, B }"));
			// `B` counts on from `A`, and `A` names `B`; the mismatch makes `A`
			// an error before any loop is evaluated.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TypeMistmatch]);
			assert_eq!(state(&case, "E::A"), &ConstValueState::Poisoned);
			assert_eq!(state(&case, "E::B"), &ConstValueState::Poisoned);
		}

		#[test]
		fn and_and_or_do_not_evaluate_a_side_they_do_not_need() {
			test_case!(
				case = &with_std(
					"const Z: i32 = 0;
					const A: bool = false && 1 / Z == 0;
					const B: bool = true || 1 / Z == 0;"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(value(&case, "A"), ConstValue::Bool(false));
			assert_eq!(value(&case, "B"), ConstValue::Bool(true));
		}

		#[test]
		fn a_loop_through_constants_is_reported_once_at_its_first_member() {
			for source in [
				"const A: i32 = B; const B: i32 = C + 1; const C: i32 = A;",
				"const C: i32 = A; const A: i32 = B; const B: i32 = C + 1;",
				"const B: i32 = C + 1; const C: i32 = A; const A: i32 = B;",
			] {
				test_case!(case = &with_std(source));
				case.diagnostics()
					.assert_codes(&[DiagnosticCode::CyclicConstant]);
				// Reported at the first-defined member, which starts the loop.
				let first = &source[6..7];
				assert_eq!(
					case.context.diagnostics[0].message,
					format!(
						"cycle detected when evaluating constant `{first}`"
					),
					"{source}"
				);
				assert_eq!(
					case.context.diagnostics[0].labels.len(),
					4,
					"{source}"
				);
			}
		}

		#[test]
		fn an_operator_call_is_not_a_constant() {
			test_case!(
				case = &with_std(
					"struct V();
					impl PartialEq for V { func eq(self, other: Self) -> bool { true } }
					const X: V = V();
					const Y: bool = X == X;"
				)
			);
			// `X` has a value; `Y` calls `eq`.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::NotConstEvaluatable]);
		}

		#[test]
		fn a_form_the_checker_does_not_cover_is_not_a_constant() {
			test_case!(
				case = &with_std(
					"func f() -> i32 { 1 }
					const A: i32 = f();"
				)
			);
			// The checker leaves the call unchecked; evaluation refuses it.
			assert_eq!(shape(&case, "A"), "unsupported:{unknown}");
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::NotConstEvaluatable]);
		}

		#[test]
		fn a_struct_is_constructed_by_calling_its_name() {
			test_case!(
				case = &with_std(
					"struct Meters(u32);
					struct Point(x: i32, y: i32);
					struct Line(from: Point, to: Point);
					const M: Meters = Meters(5);
					const P: Point = Point({ y: 2, x: 1 });
					const x: i32 = 3;
					const Q: Point = Point({ x, y: -x });
					const L: Line = Line(Point(0, 0), P);"
				)
			);
			case.diagnostics().assert_none();
			// Arguments keep their written order; the value is in declaration
			// order.
			assert_eq!(shape(&case, "P"), "(Point y=2:i32 x=1:i32):Point");
			assert_eq!(
				shape(&case, "Q"),
				"(Point x=x:i32 y=(- x:i32):i32):Point"
			);
			assert_eq!(
				shape(&case, "L"),
				"(Line (Point 0:i32 0:i32):Point P:Point):Line"
			);
			let int = |value, scalar| ConstValue::Int { value, scalar };
			let point = |x, y| {
				ConstValue::Struct(Box::new([
					int(x, Scalar::I32),
					int(y, Scalar::I32),
				]))
			};
			assert_eq!(
				value(&case, "M"),
				ConstValue::Struct(Box::new([int(5, Scalar::U32)]))
			);
			assert_eq!(value(&case, "P"), point(1, 2));
			assert_eq!(value(&case, "Q"), point(3, -3));
			assert_eq!(
				value(&case, "L"),
				ConstValue::Struct(Box::new([point(0, 0), point(1, 2)]))
			);
		}

		#[test]
		fn a_construction_gives_every_field_once() {
			use DiagnosticCode::*;
			for (initializer, code) in [
				("const P: Point = Point(1);", ArgumentCountMismatch),
				("const P: Point = Point(1, 2, 3);", ArgumentCountMismatch),
				("const P: Point = Point(1, true);", TypeMistmatch),
				("const P: Point = Point({ x: 1 });", MissingStructFields),
				(
					"const P: Point = Point({ x: 1, y: 2, z: 3 });",
					UnknownStructField,
				),
				(
					"const P: Point = Point({ x: 1, x: 2, y: 3 });",
					DuplicateStructFieldInit,
				),
				("const P: Pair = Pair({ a: 1 });", TupleStructBraceLiteral),
				(
					"const P: Point = Point::<u8>(1, 2);",
					TypeArgumentCountMismatch,
				),
				("const P: Point = Point;", StructUsedAsValue),
			] {
				test_case!(
					case = &with_std(&format!(
						"struct Point(x: i32, y: i32);
						struct Pair(i32, i32);
						{initializer}"
					))
				);
				// Reported once: the value is poisoned, not evaluated again.
				case.diagnostics().assert_codes(&[code]);
			}
		}

		#[test]
		fn a_struct_is_constructed_only_where_every_field_is_accessible() {
			test_case!(
				case = &with_std(
					"mod shapes {
						pub struct Pair(pub i32, i32);
						pub struct Point(pub x: i32, y: i32);
						pub struct Open(pub i32);
						const INSIDE: Pair = Pair(1, 2);
					}
					const A: shapes::Pair = shapes::Pair(1, 2);
					const B: shapes::Point = shapes::Point(1, 2);
					const C: shapes::Open = shapes::Open(1);"
				)
			);
			// Inside `shapes` every field is visible; outside, one report per
			// construction, whatever number of fields is private.
			case.diagnostics().assert_codes(&[
				DiagnosticCode::PrivateItem,
				DiagnosticCode::PrivateItem,
			]);
			let messages: Vec<_> = case
				.context
				.diagnostics
				.iter()
				.map(|diagnostic| diagnostic.message.as_str())
				.collect();
			assert_eq!(
				messages,
				[
					"the constructor of struct `Pair` is private",
					"the constructor of struct `Point` is private",
				]
			);
		}

		#[test]
		fn a_use_imports_a_struct_whose_constructor_it_cannot() {
			test_case!(
				case = &with_std(
					"mod shapes {
						pub struct Point(pub x: i32, y: i32);
					}
					use shapes::Point;
					pub use shapes::Point as Exported;
					const P: Point = Point(1, 2);"
				)
			);
			// The type is imported, the constructor installed inaccessible: the
			// `use`s are fine, the construction is not.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::PrivateItem]);
			assert_eq!(
				case.context.diagnostics[0].message,
				"the constructor of struct `Point` is private"
			);
		}

		#[test]
		fn a_use_of_nothing_accessible_is_reported_once() {
			test_case!(
				case = &with_std(
					"mod hidden {
						struct Secret();
					}
					use hidden::Secret;
					const S: hidden::Secret = hidden::Secret();"
				)
			);
			// Neither of `Secret`'s namespaces is visible: the `use` reports it
			// once. The constant's path reports the type and the constructor,
			// each where it is written.
			let messages: Vec<_> = case
				.context
				.diagnostics
				.iter()
				.map(|diagnostic| diagnostic.message.as_str())
				.collect();
			assert_eq!(
				messages,
				[
					"struct `Secret` is private",
					"struct `Secret` is private",
					"struct `Secret` is private",
				]
			);
		}

		#[test]
		fn a_constant_of_a_type_without_values_is_not_evaluated() {
			test_case!(
				case = &with_std(
					"struct Wrapper<T>(T);
					struct Callback(f: func(u32));
					struct Selfish(s: Selfish);
					func g(x: u32) {}
					const W: Wrapper<u32> = Wrapper(5);
					const F: Callback = Callback(g);
					const S: Selfish = Selfish(S);"
				)
			);
			// A generic struct is not constructed yet, and a function has no
			// compile-time value: neither is an error of the constant. A struct
			// containing itself is reported on the struct, and only there.
			case.diagnostics().assert_codes(&[
				DiagnosticCode::RecursiveTypeWithoutIndirection,
			]);
			assert_eq!(shape(&case, "W"), "unsupported:{unknown}");
			assert_eq!(state(&case, "W"), &ConstValueState::NoValue);
			assert_eq!(state(&case, "F"), &ConstValueState::NoValue);
			assert_eq!(state(&case, "S"), &ConstValueState::Poisoned);
		}

		#[test]
		fn a_variant_without_a_value_counts_on_from_the_one_before_it() {
			test_case!(
				case = &with_std(
					"const BASE: i16 = 10;
					enum E: i16 { A = BASE * 2, B, C = -2, D, F }
					const X: E = E::B;"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(int(&case, "E::A"), 20);
			assert_eq!(int(&case, "E::B"), 21);
			assert_eq!(int(&case, "E::C"), -2);
			assert_eq!(int(&case, "E::D"), -1);
			assert_eq!(int(&case, "E::F"), 0);
			// A value of an enum is held in its repr.
			assert_eq!(
				value(&case, "X"),
				ConstValue::Int {
					value: 21,
					scalar: Scalar::I16
				}
			);
			// A written value is checked against the repr; an implicit one is
			// the previous variant's, plus one.
			assert_eq!(shape(&case, "E::A"), "(* BASE:i16 2:i16):i16");
			assert_eq!(shape(&case, "E::B"), "(next A):i16");
		}

		#[test]
		fn the_stdlib_ordering_has_its_written_values() {
			test_case!(case = &with_std(""));
			case.diagnostics().assert_none();
			assert_eq!(int(&case, "Ordering::Less"), -1);
			assert_eq!(int(&case, "Ordering::Equal"), 0);
			assert_eq!(int(&case, "Ordering::Greater"), 1);
		}

		#[test]
		fn the_first_variant_needs_a_value_to_count_from() {
			test_case!(case = &with_std("enum E: u8 { A, B, C = 1, D }"));
			// Reported once, at `A`; `B` counts on from it and is silent.
			case.diagnostics().assert_codes(&[
				DiagnosticCode::EnumVariantRequiresExplicitValue,
			]);
			assert_eq!(state(&case, "E::A"), &ConstValueState::Poisoned);
			assert_eq!(state(&case, "E::B"), &ConstValueState::Poisoned);
			assert_eq!(int(&case, "E::D"), 2);
		}

		#[test]
		fn variants_of_an_enum_without_a_repr_are_not_checked_again() {
			test_case!(
				case = &with_std(
					"enum E { A, B = 1, C = 1 }
					const X: E = E::B;"
				)
			);
			// No repr: no anchor error, no duplicate, nothing on `X`.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::MissingEnumRepr]);
			assert_eq!(state(&case, "E::B"), &ConstValueState::Poisoned);
			assert_eq!(state(&case, "X"), &ConstValueState::Poisoned);
		}

		#[test]
		fn counting_past_the_repr_is_reported_once_at_the_variant() {
			test_case!(case = &with_std("enum E: u8 { A = 255, B, C }"));
			// `B` owns the overflow; `C` reads a failed value and is silent.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::ConstEvaluationFailed]);
			let diagnostic = &case.context.diagnostics[0];
			assert_eq!(diagnostic.message, "evaluation of constant `B` failed");
			let source = &with_std("enum E: u8 { A = 255, B, C }");
			assert_eq!(&source[diagnostic.labels[0].range.clone()], "B");
			assert_eq!(state(&case, "E::C"), &ConstValueState::Poisoned);
		}

		#[test]
		fn variants_sharing_a_value_are_reported_once_per_value() {
			let source = with_std(
				"enum E: i32 { F = 7, A = 1, B = 0, C, D = 1, G = 7, H = 2 }",
			);
			test_case!(case = &source);
			case.diagnostics().assert_codes(&[
				DiagnosticCode::EnumDuplicateValue,
				DiagnosticCode::EnumDuplicateValue,
			]);
			// In source order of each set's first variant: `F` before `A`.
			let labels = |at: usize| -> Vec<&str> {
				case.context.diagnostics[at].labels[1..]
					.iter()
					.map(|label| &source[label.range.clone()])
					.collect()
			};
			assert_eq!(
				case.context.diagnostics[0].message,
				"multiple variants of this enum have the same value `7`"
			);
			assert_eq!(labels(0), ["7", "7"]);
			// An implicit value is labelled at its variant's name.
			assert_eq!(
				case.context.diagnostics[1].message,
				"multiple variants of this enum have the same value `1`"
			);
			assert_eq!(labels(1), ["1", "C", "1"]);
		}
	}

	mod assumption_context {
		use super::*;
		use crate::tir::assumptions::{
			AssumptionKind, Readiness, TraitAssumptionSource,
		};
		use crate::tir::types::Substitution;

		fn memberships(
			signatures: &mut TypeContext<'_, '_, '_>,
			scope: TypeEnvIdx,
		) -> (Readiness, Vec<(TypeIndex, TraitIdx, TraitAssumptionSource)>) {
			let (reader, types) = signatures.assumptions();
			let mut facts = reader.scoped_facts(scope, types);
			let mut result = Vec::new();
			while let Some(fact) = facts.next(types) {
				if let AssumptionKind::Trait {
					trait_index,
					source,
				} = fact.kind
				{
					result.push((fact.subject, trait_index, source));
				}
			}
			(facts.readiness, result)
		}

		fn projection(
			case: &mut TestCase,
			base: TypeIndex,
			trait_name: &str,
			member_name: &str,
		) -> TypeIndex {
			let trait_index = case.trait_index(trait_name);
			let name = case.graph.strings.get(member_name).unwrap();
			let assoc_type_index = case.defs.traits[usize::from(trait_index)]
				.members
				.iter()
				.find_map(|member| match member.kind {
					MemberKind::AssociatedType(index)
						if case.defs.assoc_types[usize::from(index)]
							.name
							.inner == name =>
					{
						Some(index)
					}
					_ => None,
				})
				.unwrap();
			case.context.types.intern(Type::AssocTypeProjection {
				base,
				trait_index,
				assoc_type_index,
			})
		}

		#[test]
		fn scopes_preserve_outer_parameters_and_exclude_siblings() {
			test_case!(mut case = indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				trait Outer {}
				trait Local {}
				trait Other {}
				struct Host<T>();
				impl<T: Outer> Host<T> {
					func local<T: Local>() {}
					func sibling<U: Other>() {}
					func plain() {}
				}
				func unrelated<V: Other>() {}
			"});
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let outer = case.trait_index("Outer");
			let local = case.trait_index("Local");
			let other = case.trait_index("Other");
			let outer_scope =
				case.context.inherent_impls[0].as_ref().unwrap().type_params;
			let outer_param = case.context.type_envs.params(outer_scope)[0].ty;
			for (name, own_trait) in [
				("local", Some(local)),
				("sibling", Some(other)),
				("plain", None),
				("unrelated", Some(other)),
			] {
				let name_symbol = case.graph.strings.get(name).unwrap();
				let index = case
					.defs
					.functions
					.iter()
					.position(|function| function.name.inner == name_symbol)
					.unwrap();
				let scope = case.context.functions[index].type_params;
				let own_param = own_trait
					.map(|_| case.context.type_envs.params(scope)[0].ty);
				let (readiness, facts) = memberships(&mut case.context, scope);
				assert_eq!(readiness, Readiness::Ready);
				let actual: Vec<_> = facts
					.iter()
					.map(|&(subject, trait_index, _)| (subject, trait_index))
					.collect();
				let mut expected = Vec::new();
				if let (Some(subject), Some(trait_index)) =
					(own_param, own_trait)
				{
					expected.push((subject, trait_index));
				}
				if name != "unrelated" {
					expected.push((outer_param, outer));
				}
				assert_eq!(actual, expected, "{name}");
				if name == "local" {
					assert_ne!(own_param.unwrap(), outer_param);
				}
			}
			let (readiness, facts) =
				memberships(&mut case.context, TypeEnvIdx::ROOT);
			assert_eq!(readiness, Readiness::Ready);
			assert!(facts.is_empty());
		}

		#[test]
		fn inherited_and_nested_facts_keep_subjects_and_provenance() {
			test_case!(mut case = indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				type i32;
				trait Leaf {}
				trait Inner: Leaf { type Value; }
				trait Outer { type Item; type Other; }
				trait Base: Outer where { Item: Inner where { Value = i32 } } {}
				trait Final: Base {}
				func f<T: Final + Outer where { Other: Leaf }>() {}
			"});
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let scope = case.function_signature("f").type_params;
			let base = case.context.type_envs.params(scope)[0].ty;
			let item = projection(&mut case, base, "Outer", "Item");
			let value = projection(&mut case, item, "Inner", "Value");
			let other = projection(&mut case, base, "Outer", "Other");
			let expected = [
				(base, case.trait_index("Final")),
				(base, case.trait_index("Base")),
				(base, case.trait_index("Outer")),
				(item, case.trait_index("Inner")),
				(item, case.trait_index("Leaf")),
				(other, case.trait_index("Leaf")),
			];
			let (readiness, traits) = memberships(&mut case.context, scope);
			assert_eq!(readiness, Readiness::Ready);
			assert_eq!(traits.len(), expected.len());
			for &(subject, trait_index) in &expected {
				assert!(
					traits.iter().any(|&(actual, index, _)| actual == subject
						&& index == trait_index)
				);
			}
			for (_, trait_index, source) in traits {
				let TraitAssumptionSource::Bound(source) = source else {
					panic!("written/inherited bound expected");
				};
				assert_eq!(
					case.context.bounds.trait_index(source),
					trait_index
				);
			}
			let equalities = {
				let (reader, types) = case.context.assumptions();
				let mut cursor = reader.scoped_facts(scope, types);
				let mut equalities = Vec::new();
				while let Some(fact) = cursor.next(types) {
					if let AssumptionKind::Equality(
						ImpliedBindingKind::Equals(equality),
					) = fact.kind
					{
						assert!(fact.self_substitution.is_none());
						equalities.push((fact.subject, *equality));
					}
				}
				equalities
			};
			assert_eq!(equalities.len(), 1);
			let (subject, equality) = equalities[0];
			assert_eq!(subject, value);
			assert_eq!(equality.value, TypeIndex::I32);
			assert!(
				matches!(case.context.bounds.binding(equality.source).kind,
				BindingRequirement::Equals(value) if value.inner == TypeIndex::I32)
			);
		}

		#[test]
		fn associated_declaration_facts_preserve_self_through_nested_requirements()
		 {
			test_case!(mut case = indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				trait Deep { type Output; }
				trait Inner { type Value; }
				trait Outer { type Item: Inner where { Value: Deep where { Output = Self } }; }
				func f<T: Outer>() {}
			"});
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let scope = case.function_signature("f").type_params;
			let base = case.context.type_envs.params(scope)[0].ty;
			let item = projection(&mut case, base, "Outer", "Item");
			let value = projection(&mut case, item, "Inner", "Value");
			let output = projection(&mut case, value, "Deep", "Output");
			let inner = case.trait_index("Inner");
			let deep = case.trait_index("Deep");
			let outer_env =
				case.context.traits[usize::from(case.trait_index("Outer"))].env;
			let (reader, types) = case.context.assumptions();
			let mut facts = reader.subject_facts(item, types, 128);
			assert_eq!(facts.readiness, Readiness::Ready);
			let mut traits = Vec::new();
			let mut equalities = 0;
			while let Some(fact) = facts.next(types) {
				let context = fact.self_substitution.unwrap();
				assert_eq!(context.env, outer_env);
				assert_eq!(context.receiver, base);
				match fact.kind {
					AssumptionKind::Trait { trait_index, .. } => {
						traits.push((fact.subject, trait_index))
					}
					AssumptionKind::Equality(ImpliedBindingKind::Equals(
						equality,
					)) => {
						assert_eq!(fact.subject, output);
						assert_eq!(
							types.substitute(
								equality.value,
								Substitution {
									env: context.env,
									args: &[context.receiver],
								}
							),
							base
						);
						equalities += 1;
					}
					_ => panic!("expected a known equality"),
				}
			}
			assert_eq!(traits, [(item, inner), (value, deep)]);
			assert_eq!(equalities, 1);
		}

		#[test]
		fn implicit_trait_self_has_an_explicit_origin() {
			test_case!(mut case = "trait Parent {} trait Child: Parent {}");
			assert!(case.context.diagnostics.is_empty());
			let child = case.trait_index("Child");
			let parent = case.trait_index("Parent");
			let scope = case.context.traits[usize::from(child)].env;
			let subject = case.context.type_envs.params(scope)[0].ty;
			let (readiness, facts) = memberships(&mut case.context, scope);
			assert_eq!(readiness, Readiness::Ready);
			assert_eq!(facts.len(), 2);
			assert_eq!(
				facts[0],
				(subject, child, TraitAssumptionSource::TraitSelf(child))
			);
			assert!(
				matches!(facts[1], (ty, index, TraitAssumptionSource::Bound(_)) if ty == subject && index == parent)
			);
		}

		#[test]
		fn equality_alternatives_and_conflicts_remain_distinct() {
			test_case!(mut case = indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				type i32; type u32;
				trait Value { type Item; }
				func ambiguous<T: Value where { Item = U } + Value where { Item = V }, U, V>() {}
				func conflicting<T: Value where { Item = i32 } + Value where { Item = u32 }>() {}
			"});
			assert_eq!(case.context.diagnostics.len(), 1);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
			);
			for name in ["ambiguous", "conflicting"] {
				let scope = case.function_signature(name).type_params;
				let base = case.context.type_envs.params(scope)[0].ty;
				let expected_subject =
					projection(&mut case, base, "Value", "Item");
				let expected_values: Vec<_> = case
					.context
					.type_envs
					.params(scope)
					.iter()
					.skip(1)
					.map(|param| param.ty)
					.collect();
				let (reader, types) = case.context.assumptions();
				let mut facts = reader.scoped_facts(scope, types);
				assert_eq!(facts.readiness, Readiness::Ready);
				let mut equalities = 0;
				while let Some(fact) = facts.next(types) {
					if let AssumptionKind::Equality(kind) = fact.kind {
						assert_eq!(fact.subject, expected_subject);
						assert!(fact.self_substitution.is_none());
						match kind {
							ImpliedBindingKind::Ambiguous(candidates)
								if name == "ambiguous" =>
							{
								assert_eq!(
									candidates
										.iter()
										.map(|candidate| candidate.value)
										.collect::<Vec<_>>(),
									expected_values
								);
								assert_ne!(
									candidates[0].source,
									candidates[1].source
								);
								let original = &reader.param_bounds
									[usize::from(scope)][0]
									.facts
									.current()[0]
									.bindings[0]
									.kind;
								assert!(std::ptr::eq(kind, original));
							}
							ImpliedBindingKind::Conflicting
								if name == "conflicting" => {}
							_ => panic!("unexpected equality state"),
						}
						equalities += 1;
					}
				}
				assert_eq!(equalities, 1);
			}
		}

		#[test]
		fn readiness_includes_unvisited_siblings_and_updates_on_publication() {
			with_pending_signatures(
				"trait A {} trait B {} func f<T: A, U: B>() {} pub trait Call { type Args; type Result; } pub trait Function: Call {}",
				|builder| {
					let def_id = DefId::Function(FunctionIdx::new(0));
					let _ = builder.ensure_signature(QueryInfo {
						def_id,
						requested_at: None,
					});
					let scope = builder.functions[0].type_params;
					let facts = builder.param_bounds[usize::from(scope)][1]
						.facts
						.take()
						.into_boxed_slice();
					builder.param_bounds[usize::from(scope)][1].facts =
						BoundFacts::Provisional(facts);
					{
						let (reader, types) = builder.assumptions();
						let mut facts = reader.scoped_facts(scope, types);
						assert_eq!(facts.readiness, Readiness::Pending);
						let first = facts.next(types).unwrap();
						assert!(
							matches!(first.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == TraitIdx::new(0))
						);
					}
					let facts = builder.param_bounds[usize::from(scope)][1]
						.facts
						.take()
						.into_boxed_slice();
					builder.param_bounds[usize::from(scope)][1].facts =
						BoundFacts::Ready(facts);
					let (reader, types) = builder.assumptions();
					assert_eq!(
						reader.scoped_facts(scope, types).readiness,
						Readiness::Ready
					);
				},
			);
		}

		#[test]
		fn declaration_reading_preserves_pending_without_forcing_queries() {
			with_pending_signatures(
				"trait Inner {} trait Outer { type Item: Inner; } func f<T: Outer>() {} pub trait Call { type Args; type Result; } pub trait Function: Call {}",
				|builder| {
					let def_id = DefId::Function(FunctionIdx::new(0));
					let _ = builder.ensure_signature(QueryInfo {
						def_id,
						requested_at: None,
					});
					let scope = builder.functions[0].type_params;
					let base = builder.type_envs.params(scope)[0].ty;
					let declaration =
						match builder.defs.traits[1].members[0].kind {
							MemberKind::AssociatedType(index) => index,
							_ => unreachable!(),
						};
					let item =
						builder.types.intern(Type::AssocTypeProjection {
							base,
							trait_index: TraitIdx::new(1),
							assoc_type_index: declaration,
						});
					assert!(
						builder.assoc_types[usize::from(declaration)].is_none()
					);
					{
						let (reader, types) = builder.assumptions();
						let mut facts = reader.subject_facts(item, types, 128);
						assert_eq!(facts.readiness, Readiness::Pending);
						assert!(facts.next(types).is_none());
					}
					assert!(
						builder.assoc_types[usize::from(declaration)].is_none()
					);
					let reference = SourceSpan::new(
						builder.defs.traits[1].file_id,
						TextSpan::new(0, 1),
					);
					builder
						.ensure_assoc_type_bounds(declaration, reference)
						.unwrap();
					{
						let (reader, types) = builder.assumptions();
						assert_eq!(
							reader.subject_facts(item, types, 128).readiness,
							Readiness::Ready
						);
					}
					let facts = builder.assoc_types[usize::from(declaration)]
						.as_mut()
						.unwrap()
						.facts
						.take()
						.into_boxed_slice();
					builder.assoc_types[usize::from(declaration)]
						.as_mut()
						.unwrap()
						.facts = BoundFacts::Provisional(facts);
					let (reader, types) = builder.assumptions();
					let mut facts = reader.subject_facts(item, types, 128);
					assert_eq!(facts.readiness, Readiness::Pending);
					let membership = facts.next(types).unwrap();
					assert_eq!(membership.subject, item);
					assert!(
						matches!(membership.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == TraitIdx::new(0))
					);
					assert!(facts.next(types).is_none());
					assert_eq!(
						reader.subject_facts(item, types, 0).readiness,
						Readiness::Overflowed
					);
				},
			);
		}

		#[test]
		fn recursive_declarations_are_read_along_finite_subject_paths() {
			test_case!(mut case =
				"trait Node { type Next: Node; } func f<T: Node>() {} pub trait Call { type Args; type Result; } pub trait Function: Call {}",
			);
			assert!(case.context.diagnostics.is_empty());
			let scope = case.function_signature("f").type_params;
			let base = case.context.type_envs.params(scope)[0].ty;
			let next = projection(&mut case, base, "Node", "Next");
			let next_next = projection(&mut case, next, "Node", "Next");
			let (readiness, facts) = memberships(&mut case.context, scope);
			assert_eq!(readiness, Readiness::Ready);
			assert_eq!(facts.len(), 1);
			let (reader, types) = case.context.assumptions();
			for subject in [next, next_next] {
				let mut facts = reader.subject_facts(subject, types, 128);
				assert_eq!(facts.readiness, Readiness::Ready);
				let fact = facts.next(types).unwrap();
				assert_eq!(fact.subject, subject);
				assert!(
					matches!(fact.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == TraitIdx::new(0))
				);
				assert!(facts.next(types).is_none());
			}
			assert_eq!(
				reader.subject_facts(next_next, types, 1).readiness,
				Readiness::Overflowed
			);
		}
	}

	/// Stops before the signature sweep so tests can exercise demand order.
	pub(in crate::tir) fn with_pending_signatures(
		source: &str,
		check: impl FnOnce(&mut TypeContext<'_, '_, '_>),
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
		let mut resolutions = NameResolutions::default();
		let (defs, ast_nodes) = DefinitionRegistry::build(
			&graph.packages,
			&graph.files,
			&mut graph.strings,
			&mut diagnostics,
			&mut resolutions,
			graph.stdlib_package,
			graph.root_package,
		);
		let dispatch = ImplDispatch::build(
			&mut diagnostics,
			&mut resolutions,
			&graph.strings,
			&defs,
			&ast_nodes,
		);
		DiagnosticView::new("prescan/dispatch", &diagnostics, &graph.files)
			.assert_none();
		check(&mut TypeContext::new(
			&mut diagnostics,
			&mut resolutions,
			&graph.strings,
			&graph.files,
			&defs,
			&ast_nodes,
			&dispatch,
		));
	}

	/// Builds every signature, then selects the impl that supplies `name` for
	/// `receiver`: the trait's declaration, the impl's provider and a span.
	fn selected_provider(
		builder: &mut TypeContext<'_, '_, '_>,
		receiver: TypeIndex,
		name: &str,
	) -> (AssocTypeIdx, AssocTypeIdx, SourceSpan) {
		use crate::tir::members::{
			MemberLookup, TraitImplLookup, TraitMemberSelection,
		};
		builder.sweep();
		let file_id = builder
			.defs
			.namespaces
			.file_id(Namespace::Package(builder.defs.root_package));
		let reference = SourceSpan::new(file_id, TextSpan::new(0, 1));
		let name = builder.strings.get(name).unwrap();
		let key = BindingKey::ty(name);
		let MemberLookup::Found(member) = builder.resolve_applicable_member(
			TypeEnvIdx::ROOT,
			receiver,
			key,
			reference,
		) else {
			panic!("expected one associated type");
		};
		let member = member.assoc_type_declaration().unwrap();
		let declaration = member.assoc_type_index;
		let trait_index = member.trait_index;
		let Some(TraitImplLookup::Concrete { impl_index, .. }) = builder
			.find_trait_impl_query(TypeEnvIdx::ROOT, receiver, trait_index)
			.unwrap()
		else {
			panic!("expected an impl override")
		};
		let projection = builder.project_assoc_type(receiver, member);
		assert!(
			matches!(builder.types.resolve(projection), Type::AssocTypeProjection { assoc_type_index, .. } if *assoc_type_index == declaration)
		);
		let selection = builder.defs.select_trait_member(
			impl_index,
			MemberKind::AssociatedType(declaration),
		);
		let TraitMemberSelection::Impl(MemberKind::AssociatedType(provider)) =
			selection
		else {
			panic!("expected an impl associated-type value")
		};
		assert_ne!(declaration, provider);
		assert!(matches!(
			builder.ast_node(DefId::AssocType(declaration)),
			AstNodeRef::TraitAssocType { .. }
		));
		(declaration, provider, reference)
	}

	/// Parses `source` as a single-file binary playing the stdlib's own role
	/// (`set_stdlib`, the same mechanism a real `"type": "std"` package
	/// uses) instead of loading the real ~250-line embedded stdlib:
	/// `sweep` isn't selective about which item kinds it drives, so any real
	/// stdlib content — including item kinds and members whose signatures
	/// are not implemented yet — would panic before a test even runs. A test
	/// that needs a primitive declares its own bodiless `pub type i32;` — no
	/// `#[intrinsic]` marker required, recognition is implicit for a
	/// reserved name declared in whichever package is `stdlib_package`
	/// (see `defs.rs`'s own doc comment on `intrinsics`) — so this still
	/// works the same way it would for the real thing.
	fn source_graph(source: &str) -> vfs::CompilationUnit {
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
		builder.build(root_id)
	}

	/// Everything a `TypeContext` borrows. The context cannot own these —
	/// `ast_nodes` borrow the graph's packages — so a test keeps them on its
	/// own stack, declared before the `TestCase` that borrows them, which
	/// `test_case!` spells out in one line.
	struct TestInputs<'g> {
		graph: &'g vfs::CompilationUnit,
		defs: DefinitionRegistry,
		ast_nodes: Vec<AstEntry<'g>>,
		impl_dispatch: ImplDispatch,
		diagnostics: Vec<Diagnostic<FileId>>,
		resolutions: NameResolutions,
	}

	impl<'g> TestInputs<'g> {
		fn new(graph: &'g mut vfs::CompilationUnit) -> Self {
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				&mut resolutions,
				graph.stdlib_package,
				graph.root_package,
			);
			let graph = &*graph;
			let impl_dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				&graph.strings,
				&defs,
				&ast_nodes,
			);
			Self {
				graph,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			}
		}
	}

	/// A live, fully swept `TypeContext` over `TestInputs`, plus the graph
	/// and definitions tests read alongside it.
	struct TestCase<'a> {
		graph: &'a vfs::CompilationUnit,
		defs: &'a DefinitionRegistry,
		context: TypeContext<'a, 'a, 'a>,
	}

	impl<'a> TestCase<'a> {
		fn new(inputs: &'a mut TestInputs<'_>) -> Self {
			let TestInputs {
				graph,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			} = inputs;
			let mut context = TypeContext::new(
				diagnostics,
				resolutions,
				&graph.strings,
				&graph.files,
				defs,
				ast_nodes,
				impl_dispatch,
			);
			context.sweep();
			Self {
				graph,
				defs,
				context,
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
		fn resolve(&self, tier: Tier, path: &str) -> DefKind {
			let root = Scope::Package(self.defs.root_package);
			let file_id = self.defs.namespaces.file_id(root.into());

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
			let mut resolutions = NameResolutions::default();
			let target = PathResolver::new(
				&mut scratch,
				&mut resolutions,
				&self.graph.strings,
				self.defs,
			)
			.resolve_path(file_id, root, &segments, tier);
			let def_key = target.def_key().unwrap_or_else(|| {
				panic!("expected `{path}` to resolve: {scratch:?}")
			});
			def_key.symbol_kind(&self.defs)
		}

		fn trait_index(&self, path: &str) -> TraitIdx {
			let DefKind::Trait(trait_index) = self.resolve(Tier::Type, path)
			else {
				panic!("expected `{path}` to be a trait");
			};
			trait_index
		}

		/// The written clause excludes the implicit `Self: ThisTrait` bound.
		fn trait_supertraits(&self, path: &str) -> Vec<&SourceTraitBound> {
			let env =
				self.context.traits[usize::from(self.trait_index(path))].env;
			self.context.param_bounds[usize::from(env)][0]
				.declared_bounds
				.iter()
				.map(|&id| self.context.bounds.get(id))
				.collect()
		}

		fn typeset_index(&self, path: &str) -> TypesetIdx {
			let DefKind::TypeSet(typeset_index) =
				self.resolve(Tier::Type, path)
			else {
				panic!("expected `{path}` to be a typeset");
			};
			typeset_index
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"siganture",
				&self.context.diagnostics,
				&self.graph.files,
			)
		}

		fn typeset_signature(&self, path: &str) -> &TypeSetSignature {
			&self.context.typesets[usize::from(self.typeset_index(path))]
		}

		/// The `TraitIndex` of `path`'s compiler-generated backing trait —
		/// what a `T: <path>` bound actually resolves to.
		fn typeset_trait_index(&self, path: &str) -> TraitIdx {
			self.defs.typesets[usize::from(self.typeset_index(path))]
				.trait_index
		}

		/// See `trait_supertraits` — only the written clause.
		fn typeset_supertraits(&self, path: &str) -> Vec<&SourceTraitBound> {
			let env = self.context.traits
				[usize::from(self.typeset_trait_index(path))]
			.env;
			self.context.param_bounds[usize::from(env)][0]
				.declared_bounds
				.iter()
				.map(|&id| self.context.bounds.get(id))
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
			self.context.assoc_types[usize::from(index)]
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
			&self.context.functions[usize::from(index)]
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
			&self.context.constants[usize::from(index)]
		}

		fn trait_impl_index(
			&self,
			struct_path: &str,
			trait_path: &str,
		) -> TraitImplIdx {
			let trait_index = self.trait_index(trait_path);
			let target = ImplTarget::Struct(self.struct_index(struct_path));
			self.context
				.impl_dispatch
				.trait_candidates(target)
				.iter()
				.find(|&&(index, _)| index == trait_index)
				.expect("trait is implemented for the struct")
				.1
		}

		fn trait_impl_member(
			&self,
			struct_path: &str,
			trait_path: &str,
			name: &str,
		) -> MemberKind {
			let impl_index = self.trait_impl_index(struct_path, trait_path);
			let symbol = self.graph.strings.get(name).unwrap();
			let definition = &self.defs.trait_impls[usize::from(impl_index)];
			let &index =
				definition.bindings.get(&BindingKey::value(symbol)).unwrap();
			definition.members[usize::from(index)].kind
		}

		fn trait_impl_function_signature(
			&self,
			struct_path: &str,
			trait_path: &str,
			name: &str,
		) -> &FunctionSignature {
			let (MemberKind::Function(index) | MemberKind::Method(index)) =
				self.trait_impl_member(struct_path, trait_path, name)
			else {
				panic!("expected a function");
			};
			&self.context.functions[usize::from(index)]
		}

		fn trait_impl_const_signature(
			&self,
			struct_path: &str,
			trait_path: &str,
			name: &str,
		) -> &ConstantSignature {
			let MemberKind::Constant(index) =
				self.trait_impl_member(struct_path, trait_path, name)
			else {
				panic!("expected a constant");
			};
			&self.context.constants[usize::from(index)]
		}

		/// The `InherentImplIdx` of `struct_path`'s own (single, in these
		/// tests) inherent `impl` block, found the same way dispatch itself
		/// would at a method call site.
		fn inherent_impl_index(&self, struct_path: &str) -> InherentImplIdx {
			let target = ImplTarget::Struct(self.struct_index(struct_path));
			self.context.impl_dispatch.inherent_candidates(target)[0]
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
			&self.context.functions[usize::from(index)]
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
			&self.context.constants[usize::from(index)]
		}

		fn type_alias(&self, path: &str) -> &TypeAliasSignature {
			let DefKind::TypeAlias(index) = self.resolve(Tier::Type, path)
			else {
				panic!("expected `{path}` to be a type alias");
			};
			&self.context.type_aliases[usize::from(index)]
		}

		fn struct_signature(&self, path: &str) -> &StructSignature {
			&self.context.structs[usize::from(self.struct_index(path))]
		}

		fn struct_index(&self, path: &str) -> StructIdx {
			let DefKind::Struct(struct_index) = self.resolve(Tier::Type, path)
			else {
				panic!("expected `{path}` to be a struct");
			};
			struct_index
		}

		fn enum_signature(&self, path: &str) -> &EnumSignature {
			let DefKind::Enum(enum_index) = self.resolve(Tier::Type, path)
			else {
				panic!("expected `{path}` to be an enum");
			};
			&self.context.enums[usize::from(enum_index)]
		}

		fn constant_signature(&self, path: &str) -> &ConstantSignature {
			let DefKind::Const(index) = self.resolve(Tier::Value, path) else {
				panic!("expected `{path}` to be a constant");
			};
			&self.context.constants[usize::from(index)]
		}

		/// What `ty` means once normalized under `scope`'s assumptions.
		/// Signatures store types as written, so a test that asserts on the
		/// meaning of a projection normalizes it here instead of reading the
		/// stored index.
		fn normalized(
			&mut self,
			scope: TypeEnvIdx,
			ty: TypeIndex,
		) -> TypeIndex {
			self.context.normalize_type_query(scope, ty).unwrap_or_else(
				|error| panic!("expected {ty:?} to normalize, got {error:?}"),
			)
		}

		/// Parameter `index` of the function at `path`, normalized in that
		/// function's own scope.
		fn normalized_param(&mut self, path: &str, index: usize) -> TypeIndex {
			let signature = self.function_signature(path);
			let (scope, ty) =
				(signature.type_params, signature.param_types[index]);
			self.normalized(scope, ty)
		}

		/// Like `normalized_param`, but the answer itself: a parameter whose
		/// projection has no value is `Err(SolverError::Poisoned)`.
		fn try_normalized_param(
			&mut self,
			path: &str,
			index: usize,
		) -> Result<TypeIndex, SolverError> {
			let signature = self.function_signature(path);
			let (scope, ty) =
				(signature.type_params, signature.param_types[index]);
			self.context.normalize_type_query(scope, ty)
		}

		/// The parameter exactly as written, with its projections unreduced.
		fn is_projection_param(&self, path: &str, index: usize) -> bool {
			matches!(
				self.context
					.types
					.resolve(self.function_signature(path).param_types[index]),
				Type::AssocTypeProjection { .. }
			)
		}

		/// The return type of the function at `path`, normalized in its scope.
		fn normalized_return(&mut self, path: &str) -> TypeIndex {
			let signature = self.function_signature(path);
			let (scope, ty) = (signature.type_params, signature.return_type);
			self.normalized(scope, ty)
		}

		fn function_signature(&self, path: &str) -> &FunctionSignature {
			let DefKind::Function(index) = self.resolve(Tier::Value, path)
			else {
				panic!("expected `{path}` to be a function");
			};
			&self.context.functions[usize::from(index)]
		}

		/// The one-hop declared bounds on generic parameter `param_index` of
		/// whichever item owns `env` — bounds no longer live on the
		/// signature struct itself, see `TypeContext::param_bounds`.
		fn declared_bounds(
			&self,
			env: TypeEnvIdx,
			param_index: u32,
		) -> Vec<&SourceTraitBound> {
			self.context.param_bounds[usize::from(env)][param_index as usize]
				.declared_bounds
				.iter()
				.map(|&id| self.context.bounds.get(id))
				.collect()
		}

		fn param_count(&self, env: TypeEnvIdx) -> usize {
			self.context.param_bounds[usize::from(env)].len()
		}
	}

	#[test]
	fn unbounded_params_resolve_with_no_diagnostics() {
		test_case!(case = "type A<T, U> = T;");

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let env = case.type_alias("A").type_params;
		assert_eq!(case.param_count(env), 2);
		assert!((0..2).all(|i| case.declared_bounds(env, i).is_empty()));
	}

	#[test]
	fn written_infer_in_an_alias_is_reported_at_its_own_span_once() {
		let source = "type B = A; type A = _;";
		test_case!(case = source);

		assert_eq!(case.type_alias("A").target, TypeIndex::ERROR);
		assert_eq!(case.type_alias("B").target, TypeIndex::ERROR);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		let diagnostic = &case.context.diagnostics[0];
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
		test_case!(
			case = indoc! {"
			type i32;
			type bool;
			type Named = func(x: i32, y: bool) -> i32;
			type Unnamed = func(i32, bool) -> i32;
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let named = case.type_alias("Named").target;
		assert_eq!(named, case.type_alias("Unnamed").target);
		assert!(matches!(
			case.context.types.resolve(named),
			Type::FunctionRef { param, result }
				if *result == TypeIndex::I32
					&& matches!(
						case.context.types.resolve(*param),
						Type::Tuple { elements }
							if case.context.types.list(*elements) == [TypeIndex::I32, TypeIndex::BOOL]
					)
		));
	}

	#[test]
	fn a_function_type_takes_one_parameter_type() {
		test_case!(
			case = indoc! {"
			type i32;
			type bool;
			type List = func(i32, bool) -> i32;
			type Tupled = func((i32, bool)) -> i32;
			type Single = func(i32);
			type Grouped = func((i32));
			type OneTuple = func((i32,));
			type TrailingComma = func(i32,);
			type Empty = func();
		"}
		);
		case.diagnostics().assert_none();
		let target = |name| case.type_alias(name).target;
		assert_eq!(target("List"), target("Tupled"));
		assert_eq!(target("Single"), target("Grouped"));
		assert_eq!(target("Single"), target("TrailingComma"));
		assert_ne!(target("Single"), target("OneTuple"));

		let formatter = case.context.type_formatter();
		for (name, written) in [
			("List", "func(i32, bool) -> i32"),
			("Single", "func(i32) -> ()"),
			("OneTuple", "func((i32,)) -> ()"),
			("Empty", "func() -> ()"),
		] {
			assert_eq!(formatter.display_type(target(name)), written);
		}
	}

	#[test]
	fn nested_function_type_uses_generic_scope_and_defaults_to_unit() {
		test_case!(case = "type Callback<T> = func(T) -> func();");

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let alias = case.type_alias("Callback");
		let Type::FunctionRef { param, result } =
			case.context.types.resolve(alias.target)
		else {
			panic!("expected outer function type");
		};
		assert_eq!(
			case.context.types.resolve(*param),
			&Type::TypeParam {
				env: alias.type_params,
				param_index: 0,
			}
		);
		assert!(matches!(
			case.context.types.resolve(*result),
			Type::FunctionRef { param, result }
				if *param == TypeIndex::UNIT && *result == TypeIndex::UNIT
		));
	}

	#[test]
	fn function_type_placeholders_are_reported_in_source_order() {
		let source = "type Callback = func((_, _)) -> _;";
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			3,
			"{:?}",
			case.context.diagnostics
		);
		let mut last_start = 0;
		for diagnostic in &*case.context.diagnostics {
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
		let Type::FunctionRef { param, result } = case
			.context
			.types
			.resolve(case.type_alias("Callback").target)
		else {
			panic!("expected function type");
		};
		assert_eq!(*result, TypeIndex::ERROR);
		assert!(matches!(
			case.context.types.resolve(*param),
			Type::Tuple { elements }
				if case.context.types.list(*elements) == [TypeIndex::ERROR, TypeIndex::ERROR]
		));
	}

	#[test]
	fn user_aliases_are_rejected_as_impl_targets_without_dispatch() {
		test_case!(
			case = indoc! {"
			trait Tr {}
			impl Tr for Alias {}
			impl Alias {}
			type Alias = S;
			struct S();
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		assert!(
			case.context
				.diagnostics
				.iter()
				.all(|diagnostic| diagnostic.code.as_deref()
					== Some(DiagnosticCode::InvalidImplTarget.code()))
		);
		assert_eq!(case.context.trait_impls.len(), case.defs.trait_impls.len());
		assert_eq!(
			case.context.inherent_impls.len(),
			case.defs.inherent_impls.len()
		);
		let trait_header = case.context.trait_impls[0].as_ref().unwrap();
		let inherent_header = case.context.inherent_impls[0].as_ref().unwrap();
		assert_eq!(
			case.context
				.impl_dispatch
				.trait_header(TraitImplIdx::new(0))
				.trait_def
				.unwrap()
				.inner,
			case.trait_index("Tr"),
		);
		assert_eq!(trait_header.target.inner, TypeIndex::ERROR);
		assert_eq!(inherent_header.target.inner, trait_header.target.inner);
		assert!(case.context.impl_dispatch.is_empty());
	}

	#[test]
	fn intrinsic_primitive_can_be_an_impl_target() {
		test_case!(
			case = indoc! {"
			type u32;
			trait Tr {}
			impl Tr for u32 {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.impl_dispatch.trait_candidates(ImplTarget::U32),
			&[(case.trait_index("Tr"), TraitImplIdx::new(0))],
		);
	}

	#[test]
	fn never_and_unit_are_written_types() {
		test_case!(
			case = "pub trait Call { type Args; type Result; } pub trait Function: Call {} func f(a: !, b: ()) -> ! {}"
		);
		case.diagnostics().assert_none();
		let signature = case.function_signature("f");
		assert_eq!(
			&*signature.param_types,
			[TypeIndex::NEVER, TypeIndex::UNIT]
		);
		assert_eq!(signature.return_type, TypeIndex::NEVER);
	}

	#[test]
	fn impl_type_parameter_does_not_resolve_to_a_same_named_struct() {
		test_case!(
			case = indoc! {"
			struct T();
			trait Tr {}
			impl<T> Tr for T {}
		"}
		);
		assert!(case.context.impl_dispatch.is_empty());
		assert_eq!(
			case.context
				.diagnostics
				.iter()
				.filter(|diagnostic| diagnostic.code.as_deref()
					== Some(DiagnosticCode::InvalidImplTarget.code()))
				.count(),
			1,
			"{:?}",
			case.context.diagnostics,
		);
	}

	#[test]
	fn typeset_member_alias_is_rejected_without_a_synthetic_impl() {
		test_case!(
			case = indoc! {"
			type u32;
			type Alias = u32;
			typeset Int { Alias }
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::InvalidImplTarget.code()),
		);
		assert!(case.context.impl_dispatch.is_empty());
	}

	#[test]
	fn impl_dispatch_rejects_duplicate_trait_for_same_constructor() {
		test_case!(
			case = indoc! {"
			trait Tr {}
			struct S();
			impl Tr for S {}
			impl Tr for S {}
		"}
		);
		let target = ImplTarget::from_type(case.context.types.resolve(
			case.context.trait_impls[0].as_ref().unwrap().target.inner,
		))
		.unwrap();
		assert_eq!(
			case.context.impl_dispatch.trait_candidates(target).len(),
			1
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateTraitImpl.code())
		);
	}

	#[test]
	fn impl_dispatch_does_not_index_invalid_targets() {
		test_case!(
			case = indoc! {"
			impl<T> T {}
			impl Missing {}
		"}
		);
		assert!(case.context.impl_dispatch.is_empty());
		assert_eq!(
			case.context
				.diagnostics
				.iter()
				.filter(|d| d.code.as_deref()
					== Some(DiagnosticCode::InvalidImplTarget.code()))
				.count(),
			1,
			"{:?}",
			case.context.diagnostics
		);
	}

	#[test]
	fn impl_header_resolves_generic_bounds() {
		test_case!(
			case = indoc! {"
			trait Bound {}
			struct S();
			impl<T: Bound> S {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let header = case.context.inherent_impls[0].as_ref().unwrap();
		assert_eq!(case.param_count(header.type_params), 1);
		let bounds = case.declared_bounds(header.type_params, 0);
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.trait_index("Bound"));
	}

	#[test]
	fn trait_impl_header_keeps_target_when_trait_path_is_not_a_trait() {
		test_case!(
			case = indoc! {"
			struct S();
			impl S for S {}
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitBound.code())
		);
		let header = case.context.trait_impls[0].as_ref().unwrap();
		assert!(
			case.context
				.impl_dispatch
				.trait_header(TraitImplIdx::new(0))
				.trait_def
				.is_none()
		);
		assert!(matches!(
			case.context.types.resolve(header.target.inner),
			Type::Struct { .. }
		));
	}

	#[test]
	fn function_parameter_placeholders_get_separate_diagnostics() {
		let source = "pub trait Call { type Args; type Result; } pub trait Function: Call {} func f(x: (_, _)) { }";
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		for diagnostic in &*case.context.diagnostics {
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
			case.context.diagnostics[0].labels[0].range,
			case.context.diagnostics[1].labels[0].range
		);
	}

	#[test]
	fn return_type_placeholders_get_separate_diagnostics() {
		let source = "pub trait Call { type Args; type Result; } pub trait Function: Call {} func f() -> (_, _) { }";
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		for diagnostic in &*case.context.diagnostics {
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
			case.context.diagnostics[0].labels[0].range,
			case.context.diagnostics[1].labels[0].range
		);
		let return_type = case.function_signature("f").return_type;
		assert!(matches!(
			case.context.types.resolve(return_type),
			Type::Tuple { elements }
				if case.context.types.list(*elements) == [TypeIndex::ERROR, TypeIndex::ERROR]
		));
	}

	#[test]
	fn tuple_struct_placeholders_get_separate_diagnostics() {
		test_case!(case = "struct Pair(_, _);");

		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		for diagnostic in &*case.context.diagnostics {
			assert_eq!(
				diagnostic.message,
				"the placeholder `_` is not allowed within types on item signatures for structs"
			);
		}
	}

	#[test]
	fn duplicate_param_name_is_reported_but_both_entries_survive() {
		test_case!(case = "type A<T, T> = T;");

		assert_eq!(
			case.param_count(case.type_alias("A").type_params),
			2,
			"a duplicate name isn't dropped"
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateGenericParam.code())
		);
	}

	#[test]
	fn three_unique_params_report_nothing() {
		// Regression test for the exact bug this slice's `resolve_generic_params`
		// was written to avoid: checking the *post-push* vec for a match
		// always finds the entry just pushed, spuriously flagging every
		// single param as its own "duplicate".
		test_case!(case = "type A<X, Y, Z> = X;");

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
	}

	#[test]
	fn a_bound_naming_a_real_trait_resolves() {
		test_case!(
			case = indoc! {"
			trait Addable { }
			type A<T: Addable> = T;
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let env = case.type_alias("A").type_params;
		assert_eq!(case.declared_bounds(env, 0).len(), 1);
	}

	#[test]
	fn a_bound_naming_a_non_trait_is_rejected() {
		test_case!(
			case = indoc! {"
			type i32;
			struct NotATrait( x: i32 );
			type A<T: NotATrait> = T;
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitBound.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"expected trait, found struct `NotATrait`"
		);
	}

	#[test]
	fn a_bound_naming_nothing_is_reported_by_path_resolution_itself() {
		test_case!(case = "type A<T: DoesNotExist> = T;");

		let env = case.type_alias("A").type_params;
		assert_eq!(case.declared_bounds(env, 0).len(), 0);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::UndeclaredIdentifier.code())
		);
	}

	#[test]
	fn type_aliases_to_primitives_resolve_to_the_primitive() {
		test_case!(
			case = indoc! {"
			type i32;
			type bool;
			type char;

			type A = i32;
			type B = bool;
			type C = char;
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.type_alias("A").target, TypeIndex::I32);
		assert_eq!(case.type_alias("B").target, TypeIndex::BOOL);
		assert_eq!(case.type_alias("C").target, TypeIndex::CHAR);
	}

	#[test]
	fn a_type_alias_cycle_is_reported_once_and_both_sides_become_error() {
		test_case!(
			case = indoc! {"
			type A = B;
			type B = A;
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTypeAlias.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
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
		test_case!(
			case = indoc! {"
			trait Y { }
			trait X: Y { }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let bounds = case.trait_supertraits("X");
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.trait_index("Y"));
	}

	#[test]
	fn a_supertrait_cycle_is_reported_once_and_both_sides_still_finish() {
		test_case!(
			case = indoc! {"
			trait A: B { }
			trait B: A { }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
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
		test_case!(
			case = indoc! {"
			trait A: B + C { }
			trait B: A { }
			trait C: A { }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
	}

	#[test]
	fn a_direct_self_supertrait_reports_a_supertrait_cycle() {
		test_case!(case = "trait D: D {}");

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
	}

	#[test]
	fn a_nested_self_bound_reports_an_implied_bounds_cycle_once() {
		let source = indoc! {"
			trait Outer { type Item; }
			trait D: Outer where { Item: D + D } {}
		"};
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CyclicTraitBounds.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"cycle detected when computing the implied bounds of `D`"
		);
		assert_eq!(
			&source[case.context.diagnostics[0].labels[0].range.clone()],
			"D"
		);
	}

	#[test]
	fn a_struct_with_primitive_fields_resolves() {
		test_case!(
			case = indoc! {"
			type i32;
			struct Point( x: i32, y: i32 );
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let field_types = &case.struct_signature("Point").field_types;
		assert_eq!(field_types.len(), 2);
		assert_eq!(field_types[0], TypeIndex::I32);
		assert_eq!(field_types[1], TypeIndex::I32);
	}

	#[test]
	fn a_tuple_struct_resolves() {
		test_case!(
			case = indoc! {"
			type i32;
			struct Pair(i32, i32);
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.struct_signature("Pair").field_types.len(), 2);
	}

	#[test]
	fn a_struct_referencing_another_struct_resolves() {
		test_case!(
			case = indoc! {"
			struct Inner( );
			struct Outer( inner: Inner );
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
	}

	#[test]
	fn a_directly_self_recursive_struct_is_rejected() {
		test_case!(case = "struct A( a: A );");

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"recursive type `A` has infinite size"
		);
	}

	#[test]
	fn a_tuple_field_embedding_the_struct_directly_is_rejected() {
		test_case!(case = "struct A( a: (A, A) );");

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
	}

	#[test]
	fn a_mutually_recursive_struct_pair_is_rejected_once() {
		test_case!(
			case = indoc! {"
			struct A( b: B );
			struct B( a: A );
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"recursive types `A` and `B` have infinite size"
		);
	}

	#[test]
	fn a_struct_reference_with_a_satisfying_type_argument_resolves() {
		test_case!(
			case = indoc! {"
			struct Wrapper<T>( value: T );
			struct S();
			struct Holder( w: Wrapper<S> );
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			struct_index,
			type_args: args,
		} = case.context.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert_eq!(*struct_index, case.struct_index("Wrapper"));
		assert_eq!(args.len(), 1);
		let Type::Struct {
			struct_index: arg_struct_index,
			..
		} = case
			.context
			.types
			.resolve(case.context.types.list(*args)[0])
		else {
			panic!("expected the argument to resolve to `S`");
		};
		assert_eq!(*arg_struct_index, case.struct_index("S"));
	}

	#[test]
	fn a_forward_reference_to_a_generic_struct_resolves() {
		test_case!(
			case = indoc! {"
			struct Holder( w: Wrapper<S> );
			struct Wrapper<T>( value: T );
			struct S();
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			struct_index,
			type_args: args,
		} = case.context.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert_eq!(*struct_index, case.struct_index("Wrapper"));
		assert_eq!(args.len(), 1);
	}

	#[test]
	fn a_trait_used_as_a_type_is_diagnosed() {
		test_case!(
			case = indoc! {"
			trait Bound {}
			struct Holder( w: Bound );
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotAType.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"expected type, found trait `Bound`"
		);
	}

	#[test]
	fn a_struct_reference_with_too_few_type_arguments_is_diagnosed() {
		test_case!(
			case = indoc! {"
			struct Wrapper<A, B>( a: A, b: B );
			struct S();
			struct Holder( w: Wrapper<S> );
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TypeArgumentCountMismatch.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"struct `Wrapper` takes 2 generic arguments but 1 generic argument was supplied"
		);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			type_args: args, ..
		} = case.context.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert_eq!(
			case.context.types.list(*args),
			[TypeIndex::ERROR, TypeIndex::ERROR]
		);
	}

	#[test]
	fn a_struct_reference_with_too_many_type_arguments_is_diagnosed() {
		test_case!(
			case = indoc! {"
			struct Wrapper<T>( value: T );
			struct S();
			struct Holder( w: Wrapper<S, S> );
		"}
		);

		case.diagnostics().print();

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TypeArgumentCountMismatch.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"struct `Wrapper` takes 1 generic argument but 2 generic arguments were supplied"
		);
	}

	#[test]
	fn type_arguments_on_a_struct_without_generics_are_diagnosed() {
		// A struct without generics has no parameter frame of its own; the
		// report reads its (empty) parameter list from `ROOT`.
		test_case!(
			case = indoc! {"
			struct S();
			struct Holder( s: S<S> );
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentCountMismatch]);
		assert_eq!(
			case.context.diagnostics[0].message,
			"struct `S` takes 0 generic arguments but 1 generic argument was supplied"
		);
	}

	#[test]
	fn type_arguments_on_an_alias_are_counted() {
		// A primitive is a bodiless alias, so both go through the alias's
		// own parameter count; the written target is kept.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			type Byte = u8;
			type Pair<T> = (T, T);
			func f(a: Byte<u8>, b: u8<u8>, c: Pair) {}
		"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentCountMismatch,
		]);
		let params = &case.function_signature("f").param_types;
		assert_eq!(params[0], TypeIndex::U8);
		assert_eq!(params[1], TypeIndex::U8);
		let Type::Tuple { elements } = case.context.types.resolve(params[2])
		else {
			panic!("expected the alias's tuple");
		};
		assert_eq!(
			case.context.types.list(*elements),
			[TypeIndex::ERROR, TypeIndex::ERROR]
		);
	}

	#[test]
	fn a_generic_alias_substitutes_its_arguments() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			type Pair<T> = (T, T);
			func f(x: Pair<u8>) {}
		"}
		);
		case.diagnostics().assert_none();
		let param = case.function_signature("f").param_types[0];
		let Type::Tuple { elements } = case.context.types.resolve(param) else {
			panic!("expected the alias's tuple");
		};
		assert_eq!(
			case.context.types.list(*elements),
			[TypeIndex::U8, TypeIndex::U8]
		);
	}

	#[test]
	fn a_generic_alias_checks_its_parameter_bounds() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Tr {}
			type Same<T: Tr> = T;
			func f(x: Same<u8>) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
	}

	#[test]
	fn type_arguments_do_not_change_what_a_type_parameter_shadows() {
		// `T` names the parameter with or without arguments, never the
		// struct it shadows; the arguments are reported and dropped.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			struct T();
			func f<T>(x: T<u8>) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentCountMismatch]);
		assert_eq!(
			case.context.diagnostics[0].message,
			"type parameter `T` takes 0 generic arguments but 1 generic argument was supplied"
		);
		let param = case.function_signature("f").param_types[0];
		assert!(matches!(
			case.context.types.resolve(param),
			Type::TypeParam { .. }
		));
	}

	#[test]
	fn type_arguments_on_self_are_diagnosed() {
		test_case!(
			case = indoc! {"
			type u8;
			trait Tr { func g(x: Self<u8>); }
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentCountMismatch]);
		assert_eq!(
			case.context.diagnostics[0].message,
			"self type `Self` takes 0 generic arguments but 1 generic argument was supplied"
		);
	}

	#[test]
	fn a_type_parameter_with_arguments_still_selects_its_members() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Tr { type A; }
			func f<T: Tr>(x: T<u8>::A) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentCountMismatch]);
		assert!(case.is_projection_param("f", 0));
	}

	#[test]
	fn type_arguments_on_a_module_segment_are_diagnosed() {
		// The walker reports a namespace it passes through; the rest of the
		// path still resolves.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			mod m { pub struct S(); }
			func f(x: m<u8>::S) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentCountMismatch]);
		assert_eq!(
			case.context.diagnostics[0].message,
			"module `m` takes 0 generic arguments but 1 generic argument was supplied"
		);
		let param = case.function_signature("f").param_types[0];
		assert!(matches!(
			case.context.types.resolve(param),
			Type::Struct { struct_index, .. }
				if *struct_index == case.struct_index("m::S")
		));
	}

	#[test]
	fn a_struct_reference_with_a_bound_violating_type_argument_is_diagnosed() {
		test_case!(
			case = indoc! {"
			trait Bound {}
			struct Wrapper<T: Bound>( value: T );
			struct S();
			struct Holder( w: Wrapper<S> );
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"the trait bound `S: Bound` is not satisfied"
		);
		// The violation is diagnosed; the written type is kept, not rewritten.
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			type_args: args, ..
		} = case.context.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		assert!(matches!(
			case.context.types.resolve(case.context.types.list(*args)[0]),
			Type::Struct { struct_index, .. } if *struct_index == case.struct_index("S")
		));
	}

	#[test]
	fn a_struct_reference_with_a_bound_satisfying_type_argument_resolves() {
		test_case!(
			case = indoc! {"
			trait Bound {}
			struct Wrapper<T: Bound>( value: T );
			struct S();
			impl Bound for S {}
			struct Holder( w: Wrapper<S> );
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let field_ty = case.struct_signature("Holder").field_types[0];
		let Type::Struct {
			type_args: args, ..
		} = case.context.types.resolve(field_ty)
		else {
			panic!("expected a Struct type");
		};
		let Type::Struct {
			struct_index: arg_struct_index,
			..
		} = case
			.context
			.types
			.resolve(case.context.types.list(*args)[0])
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
		test_case!(
			case = indoc! {"
			struct A( b: B, c: C );
			struct B( a: A );
			struct C( a: A );
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
		);
	}

	#[test]
	fn a_function_with_primitive_params_and_return_resolves() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			type bool;
			func add(a: i32, b: i32) -> bool { true }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let signature = case.function_signature("add");
		assert_eq!(signature.param_types.len(), 2);
		assert_eq!(signature.param_types[0], TypeIndex::I32);
		assert_eq!(signature.param_types[1], TypeIndex::I32);
		assert_eq!(signature.return_type, TypeIndex::BOOL);
	}

	#[test]
	fn a_function_with_no_return_type_defaults_to_unit() {
		test_case!(
			case = "pub trait Call { type Args; type Result; } pub trait Function: Call {} func f() { }"
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.function_signature("f").return_type, TypeIndex::UNIT);
	}

	#[test]
	fn a_generic_function_param_resolves_to_its_type_param() {
		test_case!(
			case = "pub trait Call { type Args; type Result; } pub trait Function: Call {} func identity<T>(x: T) -> T { x }"
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let signature = case.function_signature("identity");
		assert_eq!(case.param_count(signature.type_params), 1);
		assert_eq!(signature.param_types[0], signature.return_type);
	}

	#[test]
	fn duplicate_function_param_name_is_reported_but_both_entries_survive() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func f(x: i32, x: i32) { }
		"}
		);

		assert_eq!(case.function_signature("f").param_types.len(), 2);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateFunctionParameter.code())
		);
	}

	#[test]
	fn a_bodiless_function_declaration_resolves_like_a_function() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func imported(x: i32) -> i32;
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let signature = case.function_signature("imported");
		assert_eq!(signature.param_types[0], TypeIndex::I32);
		assert_eq!(signature.return_type, TypeIndex::I32);
	}

	#[test]
	fn a_non_intrinsic_type_alias_without_a_body_is_diagnosed() {
		test_case!(case = "type X;");

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingTypeAliasBody.code())
		);
		assert_eq!(case.type_alias("X").target, TypeIndex::ERROR);
	}

	#[test]
	fn an_untyped_free_function_parameter_is_diagnosed_here_not_in_prescan() {
		for source in [
			"func f(x) { } pub trait Call { type Args; type Result; } pub trait Function: Call {}",
			"func f(x); pub trait Call { type Args; type Result; } pub trait Function: Call {}",
		] {
			test_case!(case = source);

			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
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
		test_case!(case = "trait Foo { func get(self, x) -> Self; }");

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingParameterType.code())
		);
		let sig = case.trait_function_signature("Foo", "get");
		assert_eq!(sig.param_types[1], TypeIndex::ERROR);
	}

	#[test]
	fn free_constants_resolve_forward_annotations_in_their_own_namespace() {
		test_case!(
			case = indoc! {"
			type i32;
			type bool;
			const VALUE: Local = 0;
			type Local = i32;
			mod nested {
				pub const VALUE: Local = false;
				type Local = bool;
			}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.constant_signature("VALUE").ty, TypeIndex::I32);
		assert_eq!(
			case.constant_signature("nested::VALUE").ty,
			TypeIndex::BOOL
		);
		for index in 0..case.defs.constants.len() {
			assert!(
				matches!(case.context.signature_location(DefId::Const(ConstIdx::new(index as u32))),
				SignatureLocation::Constant(found) if usize::from(found) == index)
			);
		}
	}

	#[test]
	fn free_constants_require_explicit_non_inferred_annotations() {
		test_case!(
			case = indoc! {"
			const MISSING = 0;
			const INFERRED: _ = 0;
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingConstantType.code())
		);
		assert_eq!(
			case.context.diagnostics[1].code.as_deref(),
			Some(DiagnosticCode::InferInSignature.code())
		);
		assert_eq!(case.constant_signature("MISSING").ty, TypeIndex::ERROR);
		assert_eq!(case.constant_signature("INFERRED").ty, TypeIndex::ERROR);
	}

	#[test]
	fn free_constant_annotations_normalize_projections_and_check_bounds() {
		test_case!(
			mut case = indoc! {"
			const VALUE: Need<S::Item> = Need();
			type i32;
			trait Marker {}
			impl Marker for i32 {}
			struct Need<T: Marker>();
			trait Container { type Item; }
			struct S();
			impl Container for S { type Item = i32; }
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		// Stored as written (`Need<S::Item>`), meaning `Need<i32>`.
		let written = case.constant_signature("VALUE").ty;
		let ty = case.normalized(TypeEnvIdx::ROOT, written);
		let Type::Struct {
			struct_index,
			type_args,
		} = case.context.types.resolve(ty)
		else {
			panic!("expected Need<i32>");
		};
		assert_eq!(*struct_index, case.struct_index("Need"));
		assert_eq!(case.context.types.list(*type_args), [TypeIndex::I32]);
	}

	#[test]
	fn free_constant_annotations_recover_from_failed_generic_requirements() {
		test_case!(
			case = indoc! {"
			type i32;
			trait Marker {}
			struct Need<T: Marker>();
			const VALUE: Need<i32> = Need();
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
		// The violation is diagnosed; the written `Need<i32>` is kept.
		let Type::Struct { type_args, .. } = case
			.context
			.types
			.resolve(case.constant_signature("VALUE").ty)
		else {
			panic!("expected Need<i32>");
		};
		assert_eq!(case.context.types.list(*type_args), [TypeIndex::I32]);
	}

	#[test]
	fn enum_types_resolve_forward_paths_in_all_signature_positions() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func f(x: colors::Color) -> Alias {}
			const FIRST: Alias = colors::Color::Red;
			struct Paint( color: Alias );
			type Alias = colors::Color;
			mod colors { pub enum Color: i32 { Red = 0, Green } }
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Enum(enum_index) =
			case.resolve(Tier::Type, "colors::Color")
		else {
			panic!("expected Color to be an enum");
		};
		let signature = case.function_signature("f");
		let ty = signature.param_types[0];
		assert!(
			matches!(case.context.types.resolve(ty), Type::Enum { enum_index: found } if *found == enum_index)
		);
		assert_ne!(ty, TypeIndex::I32);
		assert_eq!(signature.return_type, ty);
		assert_eq!(case.constant_signature("FIRST").ty, ty);
		assert_eq!(case.struct_signature("Paint").field_types.as_ref(), [ty]);
		assert_eq!(case.type_alias("Alias").target, ty);
		assert_eq!(case.enum_signature("colors::Color").repr, TypeIndex::I32);
	}

	#[test]
	fn enum_types_reject_generic_arguments() {
		let source = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func f(x: Color<i32>, y: nested::Color<i32, i32>) {}
			enum Color: i32 { Red = 0 }
			mod nested { pub enum Color: i32 { Red = 0 } }
		"};
		test_case!(case = source);
		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		for (diagnostic, path) in case
			.context
			.diagnostics
			.iter()
			.zip(["Color", "nested::Color"])
		{
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(DiagnosticCode::TypeArgumentCountMismatch.code())
			);
			assert_eq!(
				diagnostic.labels[0].message,
				"expected 0 generic arguments"
			);
			assert_eq!(&source[diagnostic.labels[0].range.clone()], "Color");
			let (argument_labels, declaration_labels) =
				diagnostic.labels[1..].split_at(diagnostic.labels.len() - 2);
			for label in argument_labels {
				assert_eq!(&source[label.range.clone()], "i32");
			}
			assert_eq!(
				argument_labels.last().unwrap().message,
				"remove the unnecessary generics"
			);
			let DefKind::Enum(index) = case.resolve(Tier::Type, path) else {
				panic!("expected an enum");
			};
			let definition = &case.defs.enums[usize::from(index)];
			let declaration = &declaration_labels[0];
			assert_eq!(declaration.file_id, definition.file_id);
			assert_eq!(
				declaration.range,
				definition.name.span.start as usize
					..definition.name.span.end as usize
			);
			assert_eq!(
				declaration.message,
				"enum defined here, with 0 generic parameters"
			);
		}
		assert_eq!(
			case.context.diagnostics[0].message,
			"enum `Color` takes 0 generic arguments but 1 generic argument was supplied"
		);
		assert_eq!(
			case.context.diagnostics[1].message,
			"enum `Color` takes 0 generic arguments but 2 generic arguments were supplied"
		);
		assert_eq!(
			case.function_signature("f").param_types.as_ref(),
			[TypeIndex::ERROR, TypeIndex::ERROR]
		);
	}

	#[test]
	fn enum_type_identity_does_not_force_its_representation_query() {
		with_pending_signatures(
			indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func f(x: Color) -> Color {}
			enum Color: i32 { Red }
		"},
			|builder| {
				let function = DefId::Function(FunctionIdx::new(0));
				let enumeration = DefId::Enum(EnumIdx::new(0));
				let _ = builder.ensure_signature(QueryInfo {
					def_id: function,
					requested_at: None,
				});
				assert!(matches!(
					builder.query_state[&enumeration].state,
					QueryState::Pending
				));
				assert!(matches!(
					builder.types.resolve(builder.functions[0].param_types[0]),
					Type::Enum { .. }
				));
				let _ = builder.ensure_signature(QueryInfo {
					def_id: enumeration,
					requested_at: None,
				});
				assert_eq!(builder.enums[0].repr, TypeIndex::I32);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
				builder.check_declarations();
			},
		);
	}

	#[test]
	fn enum_type_references_preserve_identity_when_the_representation_is_invalid()
	 {
		for (declaration, code) in [
			("enum Color { Red }", DiagnosticCode::MissingEnumRepr),
			(
				"enum Color: Color { Red }",
				DiagnosticCode::EnumReprNotInteger,
			),
			(
				"type Repr = Color; enum Color: Repr { Red }",
				DiagnosticCode::EnumReprNotInteger,
			),
		] {
			test_case!(
				case = &format!(
					"func f(x: Color) -> Color {{}} {declaration} pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}"
				)
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(code.code())
			);
			let signature = case.function_signature("f");
			assert!(matches!(
				case.context.types.resolve(signature.param_types[0]),
				Type::Enum { .. }
			));
			assert_eq!(signature.param_types[0], signature.return_type);
			assert_eq!(case.enum_signature("Color").repr, TypeIndex::ERROR);
		}
	}

	#[test]
	fn an_enum_repr_resolves_to_the_named_integer_type() {
		test_case!(
			case = indoc! {"
			type i32;
			enum Color: i32 { Red = 0, Green, Blue }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.enum_signature("Color").repr, TypeIndex::I32);
	}

	/// A variant is a constant whose type is its enum, declared at the root
	/// type scope like a free constant.
	#[test]
	fn an_enum_variant_is_a_constant_of_its_enum() {
		test_case!(
			mut case = indoc! {"
			type i32;
			enum Color: i32 { Red = 0, Green = 4 }
		"}
		);
		case.diagnostics().assert_none();
		let DefKind::Enum(enum_index) = case.resolve(Tier::Type, "Color")
		else {
			panic!("`Color` is an enum");
		};
		let color = case.context.types.intern(Type::Enum { enum_index });
		for path in ["Color::Red", "Color::Green"] {
			let DefKind::EnumVariant(const_index) =
				case.resolve(Tier::Value, path)
			else {
				panic!("`{path}` is an enum variant");
			};
			assert_eq!(
				case.context.constant_type(const_index),
				(color, TypeEnvIdx::ROOT),
				"{path}"
			);
		}
	}

	#[test]
	fn an_enum_without_a_repr_is_diagnosed() {
		test_case!(case = "enum Color { Red, Green, Blue }");

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingEnumRepr.code())
		);
		assert_eq!(case.enum_signature("Color").repr, TypeIndex::ERROR);
	}

	#[test]
	fn an_enum_with_a_non_integer_repr_is_diagnosed() {
		test_case!(
			case = indoc! {"
			type bool;
			enum Color: bool { Red, Green, Blue }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::EnumReprNotInteger.code())
		);
		assert_eq!(case.enum_signature("Color").repr, TypeIndex::ERROR);
	}

	#[test]
	fn an_unbounded_trait_associated_type_resolves_with_no_bounds() {
		test_case!(case = "trait Container { type Item; }");

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert!(
			case.assoc_type_signature("Container", "Item")
				.declared_bounds
				.is_empty()
		);
	}

	#[test]
	fn associated_type_defaults_apply_without_hiding_impl_overrides() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			type u32;
			trait Container { type Item = i32; }
			struct Defaulted();
			struct Overridden();
			impl Container for Defaulted {}
			impl Container for Overridden { type Item = u32; }
			func inherited(x: Defaulted::Item) {}
			func overridden(x: Overridden::Item) {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("inherited", 0), TypeIndex::I32);
		assert_eq!(case.normalized_param("overridden", 0), TypeIndex::U32);
	}

	#[test]
	fn associated_type_defaults_substitute_self_and_resolve_other_members() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container {
				type SelfType = Self;
				type Item = Self::Other;
				type Other;
			}
			struct Wrapper<T>();
			impl<T> Container for Wrapper<T> { type Other = T; }
			func self_type(x: <Wrapper<i32> as Container>::SelfType) {}
			func item(x: <Wrapper<i32> as Container>::Item) {}
			func abstract_item<T: Container>(x: T::Item) {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("item", 0), TypeIndex::I32);
		let self_type = case.normalized_param("self_type", 0);
		assert!(matches!(
			case.context.types.resolve(self_type),
			Type::Struct { type_args, .. } if case.context.types.list(*type_args) == [TypeIndex::I32]
		));
		// Under its own bounds `T::Item` has no concrete value: it stays abstract.
		let abstract_item = case.normalized_param("abstract_item", 0);
		assert!(matches!(
			case.context.types.resolve(abstract_item),
			Type::AssocTypeProjection { .. }
		));
	}

	#[test]
	fn bounded_associated_type_default_resolves_forward_type() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Marker {}
			trait Container { type Item: Marker = Later; }
			struct Later();
			struct Wrapper();
			impl Marker for Later {}
			impl Container for Wrapper {}
			func f(x: Wrapper::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let item = case.normalized_param("f", 0);
		assert!(matches!(
			case.context.types.resolve(item),
			Type::Struct { struct_index, .. }
				if *struct_index == case.struct_index("Later")
		));
	}

	#[test]
	fn associated_type_default_cycle_is_diagnosed() {
		// The default means something only in an impl that inherits it, so the
		// impl owns the loop: reported once, at the impl, whether or not any
		// use reaches it. The use's type is kept as written and fails silently.
		const IMPL: &str = "impl Container for Wrapper {} pub trait Call { type Args; type Result; } pub trait Function: Call {}";
		for uses in [
			"",
			"func f(x: Wrapper::Item) {}",
			"func f(x: Wrapper::Item, y: Wrapper::Item) {}",
		] {
			let source = format!(
				"
			trait Container {{ type Item = Self::Item; }}
			struct Wrapper();
			{uses}
			{IMPL}
		"
			);
			test_case!(mut case = &source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
			let target = {
				let start =
					source.find(IMPL).unwrap() + "impl Container for ".len();
				start..start + "Wrapper".len()
			};
			assert_eq!(
				case.context.diagnostics[0].labels[0].range, target,
				"{source}"
			);
			if uses.is_empty() {
				continue;
			}
			let signature = case.function_signature("f");
			let (scope, written) =
				(signature.type_params, signature.param_types[0]);
			assert!(matches!(
				case.context.types.resolve(written),
				Type::AssocTypeProjection { .. }
			));
			assert!(matches!(
				case.context.normalize_type_query(scope, written),
				Err(SolverError::Poisoned)
			));
		}
	}

	#[test]
	fn a_loop_through_an_equality_is_a_tautology_across_judgements() {
		// `V::B`'s value reaches `<W as Tr>::A as Tr2>::B`, which the declared
		// bound equates with `V::B` again. The loop passes through an equality,
		// so it restates itself and the projection stays abstract: no error,
		// although judging `V::B` reaches `V::B` again.
		const DECLS: &str = "
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Tr { type A: Tr2 where { B = <V as Tr2>::B }; }
			trait Tr2 { type B; }
			struct W();
			struct V();
		";
		const VALUE: &str =
			"impl Tr2 for V { type B = <<W as Tr>::A as Tr2>::B; }";
		const OTHER: &str = "impl Tr for W { type A = V; }";
		const USE: &str = "func f(x: <V as Tr2>::B) {}";
		for items in [
			[OTHER, VALUE, ""],
			[VALUE, OTHER, ""],
			[USE, VALUE, OTHER],
			[VALUE, OTHER, USE],
		] {
			let source = format!("{DECLS}{}", items.join("\n"));
			test_case!(case = &source);
			case.diagnostics().assert_none();
			assert!(
				case.context.solver.verdicts.values().all(|value| !matches!(
					value,
					AssocValue::Poisoned
						| AssocValue::Overflowed
						| AssocValue::Cyclic(_)
				)),
				"{source}"
			);
		}
	}

	#[test]
	fn an_answer_given_while_unwinding_a_loop_is_not_cached() {
		// `T::A`'s value restates `T::A`, so normalizing `x` rolls back to its
		// frame. `W::B` is reached while unwinding and answers unreduced: that
		// answer holds only while the loop is open. From the top it is `u32`.
		test_case!(
			mut case = "
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				pub type u32;
				trait Tr { type A; }
				trait Tr2 { type B; }
				struct W();
				impl Tr2 for W { type B = u32; }
				func f<T: Tr where { A = (<T as Tr>::A, <W as Tr2>::B) }>(
					x: <T as Tr>::A,
					y: <W as Tr2>::B,
				) {}
			"
		);
		case.diagnostics().assert_none();
		let written = case.function_signature("f").param_types[0];
		assert_eq!(case.normalized_param("f", 0), written);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::U32);
	}

	#[test]
	fn a_nested_answer_that_read_no_open_frame_is_cached() {
		// The base `T::A` is normalized inside the outer projection's frame and
		// reads none of it, so its answer is cached for later requests.
		test_case!(
			case = "
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				trait Tr { type A: Tr; }
				func f<T: Tr where { A = V }, V: Tr>(x: <<T as Tr>::A as Tr>::A) {}
			"
		);
		case.diagnostics().assert_none();
		let written = case.function_signature("f").param_types[0];
		let Type::AssocTypeProjection { base, .. } =
			*case.context.types.resolve(written)
		else {
			panic!("the parameter is a projection");
		};
		assert!(
			case.context
				.solver
				.normalized
				.keys()
				.any(|normalization| normalization.ty == base)
		);
	}

	#[test]
	fn a_loop_entered_in_the_impls_own_scope_is_owned_by_its_first_value() {
		// The method's parameter is normalized in the impl's own scope, the scope
		// the values are judged in, so the same projection repeats across
		// judgements. The loop is still read from its owner.
		for method in [
			"func by_first(x: Self::First) {}",
			"func by_second(x: Self::Second) {}",
		] {
			let source = format!(
				"
			trait Pair {{ type First; type Second; }}
			struct Example();
			impl Example {{ }}
			impl Pair for Example {{
			    {method}
			    type First = Self::Second;
			    type Second = Self::First;
			}}
		"
			);
			test_case!(case = &source);
			let first_value = {
				let from = source.find("type First =").unwrap();
				let start = from + source[from..].find("Self::Second").unwrap();
				start..start + "Self::Second".len()
			};
			let cycles: Vec<_> = case
				.context
				.diagnostics
				.iter()
				.filter(|diagnostic| {
					diagnostic.code.as_deref()
						== Some(DiagnosticCode::CyclicAssociatedType.code())
				})
				.collect();
			assert_eq!(
				cycles.len(),
				1,
				"{source}\n{:?}",
				case.context.diagnostics
			);
			assert_eq!(cycles[0].labels[0].range, first_value, "{source}");
		}
	}

	#[test]
	fn a_default_is_judged_per_impl() {
		// The same default loops in one impl and not in another: only the impl
		// that closes the loop reports it.
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Pair { type First = Self::Second; type Second; }
			struct Fine();
			struct Looping();
			impl Pair for Fine { type Second = i32; }
			impl Pair for Looping { type Second = Self::First; }
			func f(x: Fine::First) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
	}

	#[test]
	fn trait_impl_assoc_type_resolves_to_its_provided_value() {
		test_case!(
			case = indoc! {"
			type i32;
			trait Container { type Item; }
			struct Wrapper();
			impl Container for Wrapper { type Item = i32; }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);

		let container = case.trait_index("Container");
		let target = ImplTarget::Struct(case.struct_index("Wrapper"));
		let &(_, impl_index) = case
			.context
			.impl_dispatch
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

		let signature = case.context.assoc_types[usize::from(assoc_type_index)]
			.as_ref()
			.expect("impl's associated type value is resolved");
		assert_eq!(signature.value, Some(TypeIndex::I32));
		assert!(signature.declared_bounds.is_empty());
	}

	#[test]
	fn concrete_member_lookup_preserves_value_overrides_and_defaults() {
		use crate::tir::members::{
			ApplicableMember, MemberLookup, TraitMemberSelection,
		};
		with_pending_signatures(
			indoc! {"
			trait Container { func overridden() {} func inherited() {} }
			struct Wrapper();
			impl Container for Wrapper { func overridden() {} type Extra = (); }
		"},
			|builder| {
				builder.sweep();
				let receiver =
					builder.types.intern_struct(StructIdx::new(0), &[]);
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
					let key = BindingKey::new(Tier::Value, name);
					let MemberLookup::Found(member) = builder
						.resolve_applicable_member(
							TypeEnvIdx::ROOT,
							receiver,
							key,
							reference,
						)
					else {
						panic!("expected value member")
					};
					let ApplicableMember::TraitImplMember {
						trait_index: actual_trait,
						impl_index: actual_impl,
						declaration,
					} = member
					else {
						panic!("expected a concrete trait member")
					};
					assert_eq!(actual_trait, trait_index);
					assert_eq!(actual_impl, impl_index);
					let selection = builder
						.defs
						.select_trait_member(impl_index, declaration);
					let MemberKind::Function(actual) = selection.kind() else {
						panic!("expected function")
					};
					let expected = if overridden {
						let def = &builder.defs.trait_impls[0];
						assert!(matches!(
							selection,
							TraitMemberSelection::Impl(_)
						));
						def.members[usize::from(def.bindings[&key])].kind
					} else {
						let def = &builder.defs.traits[0];
						assert!(matches!(
							selection,
							TraitMemberSelection::TraitDeclaration(_)
						));
						def.members[usize::from(def.bindings[&key])].kind
					};
					assert!(
						matches!(expected, MemberKind::Function(index) if index == actual)
					);
					let qualified = builder
						.resolve_trait_qualified_value(
							TypeEnvIdx::ROOT,
							receiver,
							trait_index,
							Spanned {
								inner: name,
								span: reference.span,
							},
							reference.file_id,
						)
						.unwrap();
					assert!(
						matches!(qualified.selected_kind(builder.defs), MemberKind::Function(index) if index == actual)
					);
					// The selected definition is what the written name means.
					assert_eq!(
						builder.resolutions.by_site[&(reference, Tier::Value)],
						Referent::Member(MemberKind::Function(actual))
					);
				}
				// No declaration exists for this impl member, so it must not
				// become a projection with a provider index as its identity.
				assert!(matches!(
					builder.resolve_applicable_member(
						TypeEnvIdx::ROOT,
						receiver,
						BindingKey::ty(builder.strings.get("Extra").unwrap()),
						reference
					),
					MemberLookup::NotFound
				));
				assert!(builder.diagnostics.is_empty());
				let missing = builder.strings.get("Extra").unwrap();
				assert!(
					builder
						.resolve_trait_qualified_value(
							TypeEnvIdx::ROOT,
							receiver,
							trait_index,
							Spanned {
								inner: missing,
								span: reference.span
							},
							reference.file_id,
						)
						.is_err()
				);
				assert_eq!(
					builder.diagnostics.last().unwrap().message,
					"`Extra` is not a value member of trait `Container`"
				);
			},
		);
	}

	#[test]
	fn a_missing_impl_value_is_a_projection_without_a_value_and_no_diagnostic()
	{
		for path in ["<Wrapper as Container>::Item", "Wrapper::Item"] {
			test_case!(
				mut case = &format!(
					"
				pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}
				trait Container {{ type Item; }}
				struct Wrapper();
				impl Container for Wrapper {{}}
				func f(x: {path}) {{}}
				func g(x: {path}) {{}}
			"
				)
			);
			// The impl omits `Item`; reporting that belongs to impl conformance,
			// so neither the signatures nor the normalizer say anything.
			case.diagnostics().assert_none();
			for name in ["f", "g"] {
				let signature = case.function_signature(name);
				let (scope, written) =
					(signature.type_params, signature.param_types[0]);
				assert!(matches!(
					case.context.types.resolve(written),
					Type::AssocTypeProjection { .. }
				));
				assert_eq!(
					case.context.normalize_type_query(scope, written),
					Err(SolverError::Poisoned)
				);
			}
		}
	}

	#[test]
	fn a_member_of_a_projection_with_no_value_needs_its_own_declaration() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Container { type Item; }
			struct Wrapper();
			impl Container for Wrapper {}
			func f(x: <Wrapper>::Item::Next) {}
		"}
		);
		// Selecting `Next` off the projection reads `Item`'s declared bounds,
		// which name no `Next`; the projection is not reduced to find one.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::NotATraitMember]);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	#[test]
	fn memory_declaration_registers_a_synthetic_impl_with_a_checked_size() {
		test_case!(
			case = indoc! {"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);

		let DefKind::Memory(memory_index) = case.resolve(Tier::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};

		let memory_trait = case.trait_index("Memory");
		let candidates = case
			.context
			.impl_dispatch
			.trait_candidates(ImplTarget::Memory(memory_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, memory_trait);

		let memory_def = &case.defs.memories[usize::from(memory_index)];
		let size_signature = case.context.assoc_types
			[usize::from(memory_def.size_assoc_type_index)]
		.as_ref()
		.expect("memory's Size value is resolved");
		assert_eq!(size_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn memory_size_violating_pointer_size_is_diagnosed() {
		test_case!(
			case = indoc! {"
			type u32;
			type bool;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: bool;
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);

		let DefKind::Memory(memory_index) = case.resolve(Tier::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};
		let memory_def = &case.defs.memories[usize::from(memory_index)];
		let size_signature = case.context.assoc_types
			[usize::from(memory_def.size_assoc_type_index)]
		.as_ref()
		.expect("memory's Size value is resolved");
		// The violation is diagnosed; the written `bool` is kept.
		assert_eq!(size_signature.value, Some(TypeIndex::BOOL));
	}

	#[test]
	fn global_declaration_registers_a_synthetic_impl_with_its_value_type() {
		test_case!(
			case = indoc! {"
			type u32;
			trait Global { type Value; }
			global counter: u32 = 0;
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);

		let DefKind::Global(global_index) =
			case.resolve(Tier::Value, "counter")
		else {
			panic!("expected `counter` to be a global");
		};

		let global_trait = case.trait_index("Global");
		let candidates = case
			.context
			.impl_dispatch
			.trait_candidates(ImplTarget::Global(global_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, global_trait);

		let global_def = &case.defs.globals[usize::from(global_index)];
		assert!(global_def.mut_trait_impl_index.is_none());
		let value_signature = case.context.assoc_types
			[usize::from(global_def.value_assoc_type_index)]
		.as_ref()
		.expect("global's Value is resolved");
		assert_eq!(value_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn mutable_global_also_registers_a_global_mut_impl() {
		test_case!(
			case = indoc! {"
			type u32;
			trait Global { type Value; }
			trait GlobalMut: Global {}
			global mut counter: u32 = 0;
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);

		let DefKind::Global(global_index) =
			case.resolve(Tier::Value, "counter")
		else {
			panic!("expected `counter` to be a global");
		};
		let global_mut_trait = case.trait_index("GlobalMut");
		let candidates = case
			.context
			.impl_dispatch
			.trait_candidates(ImplTarget::Global(global_index));
		assert!(
			candidates.iter().any(|&(t, _)| t == global_mut_trait),
			"expected a `GlobalMut` impl to be registered too"
		);
	}

	#[test]
	fn global_without_a_type_annotation_is_diagnosed_and_falls_back_to_error() {
		test_case!(
			case = indoc! {"
			trait Global { type Value; }
			global counter = 0;
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingGlobalType.code())
		);

		let DefKind::Global(global_index) =
			case.resolve(Tier::Value, "counter")
		else {
			panic!("expected `counter` to be a global");
		};
		let global_def = &case.defs.globals[usize::from(global_index)];
		let value_signature = case.context.assoc_types
			[usize::from(global_def.value_assoc_type_index)]
		.as_ref()
		.expect("global's Value is resolved, even poisoned");
		assert_eq!(value_signature.value, Some(TypeIndex::ERROR));
	}

	#[test]
	fn imported_memory_registers_a_synthetic_impl_with_a_checked_size() {
		test_case!(
			case = indoc! {r#"
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			import "env" as host {
				memory shared: u32;
			}
		"#}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Memory(memory_index) =
			case.resolve(Tier::Type, "host::shared")
		else {
			panic!("expected `host::shared` to be a memory");
		};
		let memory_trait = case.trait_index("Memory");
		let candidates = case
			.context
			.impl_dispatch
			.trait_candidates(ImplTarget::Memory(memory_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, memory_trait);
		let memory_def = &case.defs.memories[usize::from(memory_index)];
		let size_signature = case.context.assoc_types
			[usize::from(memory_def.size_assoc_type_index)]
		.as_ref()
		.expect("memory's Size value is resolved");
		assert_eq!(size_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn imported_global_registers_a_synthetic_impl_with_its_value_type() {
		test_case!(
			case = indoc! {r#"
			type u32;
			trait Global { type Value; }
			import "env" as host {
				global counter: u32;
			}
		"#}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Global(global_index) =
			case.resolve(Tier::Value, "host::counter")
		else {
			panic!("expected `host::counter` to be a global");
		};
		let global_trait = case.trait_index("Global");
		let candidates = case
			.context
			.impl_dispatch
			.trait_candidates(ImplTarget::Global(global_index));
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, global_trait);
		let global_def = &case.defs.globals[usize::from(global_index)];
		assert!(global_def.mut_trait_impl_index.is_none());
		let value_signature = case.context.assoc_types
			[usize::from(global_def.value_assoc_type_index)]
		.as_ref()
		.expect("global's Value is resolved");
		assert_eq!(value_signature.value, Some(TypeIndex::U32));
	}

	#[test]
	fn imported_mutable_global_also_registers_a_global_mut_impl() {
		test_case!(
			case = indoc! {r#"
			type u32;
			trait Global { type Value; }
			trait GlobalMut: Global {}
			import "env" as host {
				global mut counter: u32;
			}
		"#}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Global(global_index) =
			case.resolve(Tier::Value, "host::counter")
		else {
			panic!("expected `host::counter` to be a global");
		};
		let global_mut_trait = case.trait_index("GlobalMut");
		let candidates = case
			.context
			.impl_dispatch
			.trait_candidates(ImplTarget::Global(global_index));
		assert!(
			candidates.iter().any(|&(t, _)| t == global_mut_trait),
			"expected a `GlobalMut` impl to be registered too"
		);
	}

	#[test]
	fn imported_function_resolves_its_parameter_and_return_types() {
		test_case!(
			case = indoc! {r#"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			import "env" as host {
				func log(value: u32) -> u32;
			}
		"#}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Function(function_index) =
			case.resolve(Tier::Value, "host::log")
		else {
			panic!("expected `host::log` to be a function");
		};
		let signature = &case.context.functions[usize::from(function_index)];
		assert_eq!(signature.param_types.as_ref(), [TypeIndex::U32]);
		assert_eq!(signature.return_type, TypeIndex::U32);
	}

	#[test]
	fn pointer_type_resolves_through_the_sole_declared_memory() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			func f(x: *u32);
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Function(function_index) = case.resolve(Tier::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let DefKind::Memory(memory_index) = case.resolve(Tier::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};
		let signature = &case.context.functions[usize::from(function_index)];
		let &[param_type] = signature.param_types.as_ref() else {
			panic!("expected exactly one parameter");
		};
		let Type::Pointer {
			to,
			memory,
			ownership,
		} = case.context.types.resolve(param_type)
		else {
			panic!("expected `x` to resolve to a pointer type");
		};
		assert_eq!(*to, TypeIndex::U32);
		assert_eq!(*ownership, ast::Ownership::Exclusive);
		assert_eq!(
			case.context.types.resolve(*memory),
			&Type::Memory { memory_index }
		);
	}

	#[test]
	fn pointer_type_with_no_memory_declared_is_diagnosed() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			func f(x: *u32);
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NoMemoryForPointer.code())
		);
		let DefKind::Function(function_index) = case.resolve(Tier::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let signature = &case.context.functions[usize::from(function_index)];
		assert_eq!(signature.param_types.as_ref(), [TypeIndex::ERROR]);
	}

	#[test]
	fn pointer_type_with_multiple_memories_is_diagnosed_as_ambiguous() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			memory heap2: u32;
			func f(x: *u32);
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::AmbiguousPointerMemory.code())
		);
		let DefKind::Function(function_index) = case.resolve(Tier::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let signature = &case.context.functions[usize::from(function_index)];
		assert_eq!(signature.param_types.as_ref(), [TypeIndex::ERROR]);
	}

	#[test]
	fn slice_and_array_types_resolve_through_the_sole_declared_memory() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			func f(s: &[u32], a: *[u32; 4]);
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Function(function_index) = case.resolve(Tier::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let DefKind::Memory(memory_index) = case.resolve(Tier::Type, "heap")
		else {
			panic!("expected `heap` to be a memory");
		};
		let signature = &case.context.functions[usize::from(function_index)];
		let &[slice_type, array_type] = signature.param_types.as_ref() else {
			panic!("expected exactly two parameters");
		};
		let Type::Slice {
			of,
			memory,
			ownership,
		} = case.context.types.resolve(slice_type)
		else {
			panic!("expected `s` to resolve to a slice type");
		};
		assert_eq!(*of, TypeIndex::U32);
		assert_eq!(*ownership, ast::Ownership::Shared);
		assert_eq!(
			case.context.types.resolve(*memory),
			&Type::Memory { memory_index }
		);
		let Type::Array {
			of,
			size,
			memory,
			ownership,
		} = case.context.types.resolve(array_type)
		else {
			panic!("expected `a` to resolve to an array type");
		};
		assert_eq!(*of, TypeIndex::U32);
		assert_eq!(*size, 4);
		assert_eq!(*ownership, ast::Ownership::Exclusive);
		assert_eq!(
			case.context.types.resolve(*memory),
			&Type::Memory { memory_index }
		);
	}

	#[test]
	fn memory_tagged_pointer_resolves_the_explicit_memory_despite_ambiguity() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			memory heap2: u32;
			func f(x: heap2::*u32);
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let DefKind::Function(function_index) = case.resolve(Tier::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let DefKind::Memory(heap2_index) = case.resolve(Tier::Type, "heap2")
		else {
			panic!("expected `heap2` to be a memory");
		};
		let signature = &case.context.functions[usize::from(function_index)];
		let &[param_type] = signature.param_types.as_ref() else {
			panic!("expected exactly one parameter");
		};
		let Type::Pointer { memory, .. } =
			case.context.types.resolve(param_type)
		else {
			panic!("expected `x` to resolve to a pointer type");
		};
		assert_eq!(
			case.context.types.resolve(*memory),
			&Type::Memory {
				memory_index: heap2_index
			}
		);
	}

	#[test]
	fn memory_tag_naming_a_non_memory_preserves_the_pointer() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u32;
            trait Memory {}
            struct Foo();

            func f(x: Foo::*u32) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		// The violation is diagnosed; the written pointer, tag included, is kept.
		let Type::Pointer { to, memory, .. } = case
			.context
			.types
			.resolve(case.function_signature("f").param_types[0])
		else {
			panic!("expected a pointer");
		};
		assert_eq!(*to, TypeIndex::U32);
		assert!(matches!(
			case.context.types.resolve(*memory),
			Type::Struct { struct_index, .. } if *struct_index == case.struct_index("Foo")
		));
	}

	#[test]
	fn memory_tag_accepts_generic_memory_for_pointers_slices_and_arrays() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}

            func test<M: Memory>(
                value: M,
                ptr: M::*u8,
                slice: M::&[u8],
                array: M::*[u8; 4],
            ) {}
        "}
		);
		case.diagnostics().assert_none();
		let params = &case.function_signature("test").param_types;
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
		assert_eq!(
			case.context.types.resolve(params[2]),
			&Type::Slice {
				of: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Shared
			}
		);
		assert_eq!(
			case.context.types.resolve(params[3]),
			&Type::Array {
				of: TypeIndex::U8,
				size: 4,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_requires_a_bound_and_accepts_a_memory_supertrait() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}
            trait SpecialMemory: Memory {}

            func unbounded<M>(value: M, ptr: M::*u8) {}

            func inherited<M: SpecialMemory>(value: M, ptr: M::*u8) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		let params = &case.function_signature("unbounded").param_types;
		assert!(matches!(
			case.context.types.resolve(params[0]),
			Type::TypeParam { .. }
		));
		// `M` is not a memory: diagnosed, and the written tag is kept.
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
		let params = &case.function_signature("inherited").param_types;
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_accepts_a_generic_associated_type_bounded_by_memory() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}

            trait Container {
                type Mem: Memory;
            }

            func test<T: Container>(value: T::Mem, ptr: T::Mem::*u8) {}
        "}
		);
		case.diagnostics().assert_none();
		let params = &case.function_signature("test").param_types;
		assert!(matches!(
			case.context.types.resolve(params[0]),
			Type::AssocTypeProjection { .. }
		));
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_accepts_self_with_a_memory_supertrait() {
		test_case!(
			case = indoc! {"
            type u8;
            trait Memory {}

            trait Tagged: Memory {
                func test(value: Self, ptr: Self::*u8);
            }
        "}
		);
		case.diagnostics().assert_none();
		let params =
			&case.trait_function_signature("Tagged", "test").param_types;
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_accepts_struct_impls_and_concrete_associated_types() {
		test_case!(
			mut case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}

            struct Heap();
            impl Memory for Heap {}

            trait Container {
                type Mem: Memory;
            }

            struct Holder();

            impl Container for Holder {
                type Mem = Heap;
            }

            func direct(ptr: Heap::*u8) {}

            func associated(value: Holder::Mem, ptr: Holder::Mem::*u8) {}
        "}
		);
		case.diagnostics().assert_none();
		let params = &case.function_signature("associated").param_types;
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
		// Written differently, the same memory once normalized.
		let associated = case.normalized_param("associated", 1);
		assert_eq!(case.normalized_param("direct", 0), associated);
	}

	#[test]
	fn memory_tag_resolves_generic_arguments_and_checks_impl_requirements() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}

            struct Heap<M>();
            impl<M: Memory> Memory for Heap<M> {}

            func bounded<M: Memory>(value: Heap<M>, ptr: Heap<M>::*u8) {}

            func unbounded<M>(ptr: Heap<M>::*u8) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		let params = &case.function_signature("bounded").param_types;
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
		// `Heap<M>` is not a memory without `M: Memory`: diagnosed, tag kept.
		let Type::Pointer { memory, .. } = case
			.context
			.types
			.resolve(case.function_signature("unbounded").param_types[0])
		else {
			panic!("expected a pointer");
		};
		assert!(matches!(
			case.context.types.resolve(*memory),
			Type::Struct { struct_index, type_args }
				if *struct_index == case.struct_index("Heap") && type_args.len() == 1
		));
	}

	#[test]
	fn memory_tag_accepts_an_alias_to_a_concrete_memory() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            type u32;

            typeset PointerSize {
                u32,
            }

            trait Memory {
                type Size: PointerSize;
            }

            memory heap: u32;
            type Alias = heap;

            func test(value: Alias, ptr: Alias::*u8) {}
        "}
		);
		case.diagnostics().assert_none();
		let params = &case.function_signature("test").param_types;
		assert!(matches!(
			case.context.types.resolve(params[0]),
			Type::Memory { .. }
		));
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_respects_generic_parameter_shadowing() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            type u32;

            typeset PointerSize {
                u32,
            }

            trait Memory {
                type Size: PointerSize;
            }

            memory M: u32;

            func test<M>(value: M, ptr: M::*u8) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		let params = &case.function_signature("test").param_types;
		assert!(matches!(
			case.context.types.resolve(params[0]),
			Type::TypeParam { .. }
		));
		// The parameter `M` shadows the memory `M`, so it must itself be a
		// memory: diagnosed, and the written tag (the parameter) is kept.
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_resolves_trailing_segments_after_a_concrete_memory() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            type u32;

            typeset PointerSize {
                u32,
            }

            trait Memory {
                type Size: PointerSize;
            }

            memory heap: u32;

            func test(ptr: heap::Missing::*u8) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::NotATraitMember]);
		assert_eq!(
			case.context
				.types
				.resolve(case.function_signature("test").param_types[0]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: TypeIndex::ERROR,
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_failure_preserves_a_valid_projection_in_other_positions() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}

            trait Container {
                type Mem;
            }

            func test<T: Container>(value: T::Mem, ptr: T::Mem::*u8) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		let params = &case.function_signature("test").param_types;
		assert!(matches!(
			case.context.types.resolve(params[0]),
			Type::AssocTypeProjection { .. }
		));
		// `T::Mem` is not a memory: diagnosed, and the written tag is kept.
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_membership_waits_for_associated_equalities() {
		test_case!(
			mut case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            type u32;
            trait Memory {}
            impl Memory for u32 {}

            trait Container {
                type Item;
            }

            func test<
                T: Container where { Item = U::Item::*u8 },
                U: Container where { Item = u32 },
            >(ptr: T::Item) {}
        "}
		);
		case.diagnostics().assert_none();
		// `T::Item` means a pointer tagged with `U::Item`, which `U`'s equality
		// makes `u32`, a memory.
		let ptr = case.normalized_param("test", 0);
		assert_eq!(
			case.context.types.resolve(ptr),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: TypeIndex::U32,
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_deferred_failure_preserves_the_pointer_and_ordinary_subject()
	{
		test_case!(
			mut case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            type u32;
            trait Memory {}

            trait Container {
                type Item;
            }

            func test<
                T: Container where { Item = U::Item::*u8 },
                U: Container where { Item = u32 },
            >(value: U::Item, ptr: T::Item) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		// `u32` is not a memory here: diagnosed once, at the written tag. The
		// ordinary subject and the pointer both keep their meaning.
		assert_eq!(case.normalized_param("test", 0), TypeIndex::U32);
		let ptr = case.normalized_param("test", 1);
		assert_eq!(
			case.context.types.resolve(ptr),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: TypeIndex::U32,
				ownership: ast::Ownership::Exclusive
			}
		);
	}

	#[test]
	fn memory_tag_with_a_failed_projection_preserves_the_pointer() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}

            trait Container {
                type Item;
            }

            trait Project {
                type Output: Memory;
            }

            func test<
                T: Container where { Item = <U as Project>::Output },
                U,
            >(value: U, ptr: T::Item::*u8) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		let params = &case.function_signature("test").param_types;
		assert!(matches!(
			case.context.types.resolve(params[0]),
			Type::TypeParam { .. }
		));
		// `<U as Project>::Output` needs `U: Project`, diagnosed at that path.
		// The tag is kept as written. Its own `Memory` membership holds through
		// `Project::Output: Memory`, so only the one requirement is reported.
		let Type::Pointer { memory, .. } =
			case.context.types.resolve(params[1])
		else {
			panic!("expected a pointer");
		};
		assert!(matches!(
			case.context.types.resolve(*memory),
			Type::AssocTypeProjection { .. }
		));
	}

	#[test]
	fn memory_tag_deferred_projection_failure_preserves_its_surrounding_pointer()
	 {
		test_case!(
			mut case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u8;
            trait Memory {}

            trait Container {
                type Item;
            }

            trait Project {
                type Output: Memory;
            }

            func test<
                T: Container where { Item = V::Item::*u8 },
                V: Container where { Item = <U as Project>::Output },
                U,
            >(value: U, ptr: T::Item) {}
        "}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		let params = &case.function_signature("test").param_types;
		assert!(matches!(
			case.context.types.resolve(params[0]),
			Type::TypeParam { .. }
		));
		// `ptr` is written as `T::Item`: a pointer tagged with `V::Item`, which
		// is `<U as Project>::Output`. `U: Project` is unsatisfied and reported
		// once, at that path, but the projection stays abstract, so the pointer
		// keeps its shape.
		assert!(matches!(
			case.context.types.resolve(params[1]),
			Type::AssocTypeProjection { .. }
		));
		let ptr = case.normalized_param("test", 1);
		let Type::Pointer { to, memory, .. } = case.context.types.resolve(ptr)
		else {
			panic!("expected a pointer");
		};
		assert_eq!(*to, TypeIndex::U8);
		assert!(matches!(
			case.context.types.resolve(*memory),
			Type::AssocTypeProjection { .. }
		));
	}

	#[test]
	fn a_trait_associated_type_bound_resolves_to_the_named_traits() {
		test_case!(
			case = indoc! {"
			trait Bound1 {}
			trait Bound2 {}
			trait Container { type Item: Bound1 + Bound2; }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let bounds = &case
			.assoc_type_signature("Container", "Item")
			.declared_bounds;
		assert_eq!(bounds.len(), 2);
		assert_eq!(
			case.context.bounds.get(bounds[0]).trait_index,
			case.trait_index("Bound1")
		);
		assert_eq!(
			case.context.bounds.get(bounds[1]).trait_index,
			case.trait_index("Bound2")
		);
	}

	#[test]
	fn an_untyped_self_param_resolves_to_the_traits_own_self() {
		test_case!(case = "trait Foo { func get(self) -> Self; }");

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
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
		test_case!(
			case = indoc! {"
			struct S();
			impl S { func get(self) -> Self { self } }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.inherent_function_signature("S", "get");
		assert_eq!(sig.param_types.len(), 1);
		assert_eq!(
			sig.param_types[0], sig.return_type,
			"`self` and a written `Self` return type should both resolve to \
			 the impl's own concrete target"
		);
		assert!(
			matches!(
				case.context.types.resolve(sig.param_types[0]),
				Type::Struct { .. }
			),
			"an inherent impl's `self` is a concrete type, not an abstract \
			 TypeParam"
		);
	}

	#[test]
	fn an_inherent_impl_const_resolves_its_declared_type() {
		test_case!(
			case = indoc! {"
			type i32;
			struct S();
			impl S { const X: i32 = 0; }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.inherent_const_signature("S", "X");
		assert_eq!(sig.ty, TypeIndex::I32);
	}

	#[test]
	fn a_non_self_untyped_inherent_impl_function_parameter_is_diagnosed() {
		test_case!(
			case = indoc! {"
			struct S();
			impl S { func get(self, x) -> Self { self } }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::MissingParameterType.code())
		);
		let sig = case.inherent_function_signature("S", "get");
		assert_eq!(sig.param_types[1], TypeIndex::ERROR);
	}

	#[test]
	fn trait_impl_methods_and_associated_functions_use_the_concrete_self_type()
	{
		test_case!(
			case = indoc! {"
			trait Service { func get(self) -> Self; func make(x: Self) -> Self; }
			struct S();
			impl Service for S {
				func get(self) -> Self { self }
				func make(x: Self) -> Self { x }
			}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let impl_index = case.trait_impl_index("S", "Service");
		let header = case.context.trait_impls[usize::from(impl_index)]
			.as_ref()
			.unwrap();
		for name in ["get", "make"] {
			let signature =
				case.trait_impl_function_signature("S", "Service", name);
			assert_eq!(signature.param_types.as_ref(), [header.target.inner]);
			assert_eq!(signature.return_type, header.target.inner);
			assert_eq!(signature.type_params, header.type_params);
		}
	}

	#[test]
	fn trait_impl_member_generics_inherit_the_impl_scope_and_allow_shadowing() {
		test_case!(
			case = indoc! {"
			type i32;
			typeset Number { i32 }
			trait Service {
				type Item;
				func get<U>(self, x: Self::Item, y: U) -> Self;
				func shadow<T>(self, x: T) -> Self;
				const VALUE: Self::Item;
			}
			struct Wrap<T>();
			impl<T: Number> Service for Wrap<T> {
				type Item = T;
				func get<U>(self, x: T, y: U) -> Self { self }
				func shadow<T>(self, x: T) -> Self { self }
				const VALUE: T = 0;
			}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let impl_index = case.trait_impl_index("Wrap", "Service");
		let header = case.context.trait_impls[usize::from(impl_index)]
			.as_ref()
			.unwrap();
		let outer = case.context.type_envs.params(header.type_params)[0].ty;
		let get = case.trait_impl_function_signature("Wrap", "Service", "get");
		assert_eq!(get.param_types[0], header.target.inner);
		assert_eq!(get.param_types[1], outer);
		assert_eq!(
			get.param_types[2],
			case.context.type_envs.params(get.type_params)[0].ty
		);
		assert_eq!(get.return_type, header.target.inner);
		assert_eq!(
			case.context.type_envs.parent(get.type_params),
			Some(header.type_params)
		);
		let shadow =
			case.trait_impl_function_signature("Wrap", "Service", "shadow");
		assert_ne!(shadow.param_types[1], outer);
		assert_eq!(shadow.param_types[0], header.target.inner);
		assert_eq!(shadow.return_type, header.target.inner);
		assert_eq!(
			case.trait_impl_const_signature("Wrap", "Service", "VALUE")
				.ty,
			outer
		);
	}

	#[test]
	fn trait_impl_member_checks_use_enclosing_and_local_assumptions() {
		test_case!(
			mut case = indoc! {"
			type i32;
			trait Marker {}
			impl Marker for i32 {}
			trait Container { type Item; }
			struct Need<T: Marker>();
			trait Service {
				type Item: Marker;
				func get<U: Container where { Item: Marker }>(self, x: Need<Self::Item>, y: Need<U::Item>);
			}
			struct Wrap<T>();
			impl<T: Marker> Service for Wrap<T> {
				type Item = T;
				func get<U: Container where { Item = i32 }>(self, x: Need<T>, y: Need<U::Item>) {}
			}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let signature =
			case.trait_impl_function_signature("Wrap", "Service", "get");
		let (scope, written, return_type) = (
			signature.type_params,
			signature.param_types[2],
			signature.return_type,
		);
		// Stored as `Need<U::Item>`; under the method's own `Item = i32` that
		// is `Need<i32>`.
		let ty = case.normalized(scope, written);
		let Type::Struct { type_args, .. } = case.context.types.resolve(ty)
		else {
			panic!("expected Need<i32>");
		};
		assert_eq!(case.context.types.list(*type_args), [TypeIndex::I32]);
		assert_eq!(return_type, TypeIndex::UNIT);
	}

	#[test]
	fn trait_impl_methods_complete_checks_from_forward_associated_equalities() {
		test_case!(
			mut case = indoc! {"
			type i32;
			trait Marker {}
			impl Marker for i32 {}
			struct Need<T: Marker>();
			trait Container { type A; type B; }
			trait Service {
				func get<U: Container where { A = Need<U::B>, B = i32 }>(self, x: U::A);
			}
			struct S();
			impl Service for S {
				func get<U: Container where { A = Need<U::B>, B = i32 }>(self, x: U::A) {}
			}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let signature =
			case.trait_impl_function_signature("S", "Service", "get");
		let (scope, written) =
			(signature.type_params, signature.param_types[1]);
		// `U::A` is `Need<U::B>` and `U::B` is `i32`, in either written order.
		let ty = case.normalized(scope, written);
		let Type::Struct { type_args, .. } = case.context.types.resolve(ty)
		else {
			panic!("expected Need<i32>");
		};
		assert_eq!(case.context.types.list(*type_args), [TypeIndex::I32]);
	}

	#[test]
	fn trait_impl_member_signatures_recover_from_failed_generic_requirements() {
		test_case!(
			case = indoc! {"
			type i32;
			trait Marker {}
			struct Need<T: Marker>();
			trait Service { func get(self, x: i32); const VALUE: i32; }
			struct S();
			impl Service for S {
				func get(self, x: Need<i32>) {}
				const VALUE: Need<i32> = Need();
			}
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		for diagnostic in &*case.context.diagnostics {
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(DiagnosticCode::TraitBoundViolation.code())
			);
		}
		let signature =
			case.trait_impl_function_signature("S", "Service", "get");
		let constant = case.trait_impl_const_signature("S", "Service", "VALUE");
		for ty in [signature.param_types[1], constant.ty] {
			let Type::Struct { type_args, .. } = case.context.types.resolve(ty)
			else {
				panic!("expected Need<i32>");
			};
			// Each written site reports its own violation; the type is kept.
			assert_eq!(case.context.types.list(*type_args), [TypeIndex::I32]);
		}
	}

	#[test]
	fn trait_impl_constants_normalize_associated_types_declared_after_them() {
		test_case!(
			mut case = indoc! {"
			type i32;
			trait Service { type Item; const VALUE: Self::Item; }
			struct S();
			impl Service for S {
				const VALUE: Self::Item = 0;
				type Item = i32;
			}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		// Stored as `Self::Item`, declared after the constant; it means `i32`.
		let written =
			case.trait_impl_const_signature("S", "Service", "VALUE").ty;
		assert_eq!(case.normalized(TypeEnvIdx::ROOT, written), TypeIndex::I32);
	}

	#[test]
	fn impl_constants_require_explicit_type_annotations() {
		test_case!(
			case = indoc! {"
			type i32;
			trait Service { const VALUE: i32; }
			struct S();
			impl Service for S { const VALUE = 0; }
			impl S { const OTHER = 0; }
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		for diagnostic in &*case.context.diagnostics {
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(DiagnosticCode::MissingConstantType.code())
			);
		}
		assert_eq!(
			case.trait_impl_const_signature("S", "Service", "VALUE").ty,
			TypeIndex::ERROR
		);
		assert_eq!(
			case.inherent_const_signature("S", "OTHER").ty,
			TypeIndex::ERROR
		);
	}

	#[test]
	fn invalid_trait_impl_member_annotations_are_diagnosed_without_panicking() {
		test_case!(
			case = indoc! {"
			type i32;
			trait Service { func get(self, x: i32, y: i32) -> i32; const VALUE: i32; }
			struct S();
			impl Service for S {
				func get(self, x, y: _) -> _ {}
				const VALUE: _ = 0;
			}
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			4,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context
				.diagnostics
				.iter()
				.filter(|d| d.code.as_deref()
					== Some(DiagnosticCode::MissingParameterType.code()))
				.count(),
			1
		);
		assert_eq!(
			case.context
				.diagnostics
				.iter()
				.filter(|d| d.code.as_deref()
					== Some(DiagnosticCode::InferInSignature.code()))
				.count(),
			3
		);
		let signature =
			case.trait_impl_function_signature("S", "Service", "get");
		assert_eq!(
			&signature.param_types[1..],
			[TypeIndex::ERROR, TypeIndex::ERROR]
		);
		assert_eq!(signature.return_type, TypeIndex::ERROR);
		assert_eq!(
			case.trait_impl_const_signature("S", "Service", "VALUE").ty,
			TypeIndex::ERROR
		);
	}

	#[test]
	fn trait_impl_member_requests_force_the_parent_header() {
		for method_first in [false, true] {
			with_pending_signatures(
				indoc! {"
				type i32;
				trait Service { func get(self) -> Self; const VALUE: i32; }
				struct S();
				impl Service for S { func get(self) -> Self { self } const VALUE: i32 = 0; }
			"},
				|builder| {
					let member = builder
						.ast_nodes
						.iter()
						.find(|entry| {
							if method_first {
								matches!(
									entry.node,
									AstNodeRef::TraitImplFunction { .. }
								)
							} else {
								matches!(
									entry.node,
									AstNodeRef::TraitImplConstant { .. }
								)
							}
						})
						.unwrap();
					let id = member.node.def_id();
					assert!(builder.trait_impls[0].is_none());
					assert!(matches!(
						builder.ensure_signature(QueryInfo {
							def_id: id,
							requested_at: None
						}),
						SignatureStatus::Available(_)
					));
					assert!(builder.trait_impls[0].is_some());
					for entry in builder.ast_nodes {
						let _ = builder.ensure_signature(QueryInfo {
							def_id: entry.node.def_id(),
							requested_at: None,
						});
					}
					assert!(
						builder.diagnostics.is_empty(),
						"{:?}",
						builder.diagnostics
					);
					builder.check_declarations();
				},
			);
		}
	}

	#[test]
	fn a_trait_functions_own_generic_param_is_distinct_from_self() {
		test_case!(case = "trait Foo { func get<T>(self, x: T) -> T; }");

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
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
		test_case!(
			case = indoc! {"
			type i32;
			type bool;
			trait Result { type Value; const FLAG: bool; }
			trait Source { type Value; }
			trait Container {
				type First: Result where { Value = Self::Second::Value };
				type Second: Source;
				const COUNT: i32;
			}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);

		// Resolving First's bound forces Second before First finishes.
		for (name, expected_trait) in
			[("First", "Result"), ("Second", "Source")]
		{
			let signature = case.assoc_type_signature("Container", name);
			assert_eq!(signature.declared_bounds.len(), 1);
			assert_eq!(
				case.context
					.bounds
					.get(signature.declared_bounds[0])
					.trait_index,
				case.trait_index(expected_trait),
			);
		}
		assert_eq!(case.context.assoc_types.len(), case.defs.assoc_types.len());
		assert_eq!(case.context.constants.len(), case.defs.constants.len());
		assert_eq!(
			case.trait_const_signature("Result", "FLAG").ty,
			TypeIndex::BOOL
		);
		assert_eq!(
			case.trait_const_signature("Container", "COUNT").ty,
			TypeIndex::I32
		);
		for index in 0..case.defs.assoc_types.len() {
			assert!(matches!(
				case.context.signature_location(DefId::AssocType(AssocTypeIdx::new(index as u32))),
				SignatureLocation::AssocType(found) if usize::from(found) == index
			));
		}
		for index in 0..case.defs.constants.len() {
			assert!(matches!(
				case.context.signature_location(DefId::Const(ConstIdx::new(index as u32))),
				SignatureLocation::Constant(found) if usize::from(found) == index
			));
		}
	}

	#[test]
	fn a_trait_const_resolves_its_declared_type() {
		test_case!(case = "type i32; trait Foo { const X: i32; }");

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.trait_const_signature("Foo", "X").ty, TypeIndex::I32);
	}

	#[test]
	fn a_trait_consts_type_can_reference_self() {
		test_case!(
			case = indoc! {"
			trait Foo {
				const X: Self;
				func get(self) -> Self;
			}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.trait_const_signature("Foo", "X").ty,
			case.trait_function_signature("Foo", "get").return_type,
			"`const X: Self` and `func get(self) -> Self` should resolve to \
			 the same TypeParam"
		);
	}

	#[test]
	fn a_trait_associated_type_bound_to_a_non_trait_is_diagnosed() {
		test_case!(
			case = indoc! {"
			struct S();
			trait Container { type Item: S; }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Memory { type Size; }
			func f<Mem: Memory where { Size = i32 }>() {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Unsigned {}
			trait Memory { type Size; }
			func f<Mem: Memory where { Size: Unsigned }>() {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
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
			case.context.bounds.get(rhs_bounds[0]).trait_index,
			case.trait_index("Unsigned")
		);
	}

	#[test]
	fn a_duplicate_where_binding_is_diagnosed_and_only_the_first_is_kept() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Memory { type Size; }
			func f<Mem: Memory where { Size = i32, Size = i32 }>() {}
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert_eq!(bounds[0].bindings.len(), 1);
	}

	#[test]
	fn a_where_binding_naming_an_unknown_associated_type_is_diagnosed() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Memory { type Size; }
			func f<Mem: Memory where { Nope = i32 }>() {}
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitMember.code())
		);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert!(bounds[0].bindings.is_empty());
	}

	#[test]
	fn a_where_binding_may_reference_a_sibling_param_declared_later() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait PointerSize {}
			trait Memory { type Size; }
			func copy<Src: Memory where { Size = S }, S: PointerSize>() {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let env = case.function_signature("copy").type_params;
		let bounds = case.declared_bounds(env, 0);
		let BindingRequirement::Equals(ty) = &bounds[0].bindings[0].kind else {
			panic!("expected an `Equals` binding kind");
		};
		assert!(matches!(
			case.context.types.resolve(ty.inner),
			Type::TypeParam { param_index: 1, .. }
		));
	}

	#[test]
	fn a_typeset_bound_resolves_to_its_backing_trait() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			type i32;
			typeset Int { u32, i32 }
			func f<T: Int>() {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let env = case.function_signature("f").type_params;
		let bounds = case.declared_bounds(env, 0);
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.typeset_trait_index("Int"));
	}

	#[test]
	fn a_typesets_own_clause_becomes_its_backing_traits_supertraits() {
		test_case!(
			case = indoc! {"
			trait Bound {}
			typeset Int: Bound {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let supertraits = case.typeset_supertraits("Int");
		assert_eq!(supertraits.len(), 1);
		assert_eq!(supertraits[0].trait_index, case.trait_index("Bound"));
	}

	#[test]
	fn a_typeset_member_registers_a_synthetic_impl() {
		test_case!(
			case = indoc! {"
			type u32;
			typeset Int { u32 }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.typeset_signature("Int").members[0].inner,
			TypeIndex::U32
		);
		let target =
			ImplTarget::from_type(case.context.types.resolve(TypeIndex::U32))
				.unwrap();
		let candidates = case.context.impl_dispatch.trait_candidates(target);
		assert_eq!(candidates.len(), 1);
		assert_eq!(candidates[0].0, case.typeset_trait_index("Int"));
	}

	#[test]
	fn a_typeset_used_before_its_own_declaration_still_sees_its_members() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			func f<T: Int>() {}
			type u32;
			typeset Int { u32 }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let target =
			ImplTarget::from_type(case.context.types.resolve(TypeIndex::U32))
				.unwrap();
		assert_eq!(
			case.context.impl_dispatch.trait_candidates(target).len(),
			1
		);
	}

	#[test]
	fn duplicate_typeset_members_are_diagnosed() {
		test_case!(
			case = indoc! {"
			type u32;
			typeset Int { u32, u32 }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateTraitImpl.code())
		);
		let target =
			ImplTarget::from_type(case.context.types.resolve(TypeIndex::U32))
				.unwrap();
		assert_eq!(
			case.context.impl_dispatch.trait_candidates(target).len(),
			1
		);
	}

	#[test]
	fn self_assoc_type_projects_through_the_traits_own_self() {
		test_case!(
			case = indoc! {"
			trait Global {
				type Value;
				func get(self) -> Self::Value;
			}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.trait_function_signature("Global", "get");
		let trait_index = case.trait_index("Global");
		match case.context.types.resolve(sig.return_type) {
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
		test_case!(
			case = indoc! {"
			trait Global {
				type Value;
				func get(self) -> <Self>::Value;
			}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.trait_function_signature("Global", "get");
		let trait_index = case.trait_index("Global");
		match case.context.types.resolve(sig.return_type) {
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait A { type X; }
			trait B { type X; }
			func f<T: A + B>(x: <T as A>::X) { }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let trait_a = case.trait_index("A");
		match case
			.context
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait B { type Y; }
			trait A { type X: B; }
			func f<T: A>(x: <T as A>::X::Y) { }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let trait_b = case.trait_index("B");
		match case
			.context
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait A { type X; }
			func f<T: A>(x: <T as A>::Y) { }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait A { type X; }
			trait B {}
			func f<T: B>(x: <T as A>::X) { }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
		// The unsatisfied requirement is diagnosed once, where it was written;
		// the type is kept as written.
		assert!(matches!(
			case.context
				.types
				.resolve(case.function_signature("f").param_types[0]),
			Type::AssocTypeProjection { .. }
		));
	}

	#[test]
	fn concrete_projection_paths_normalize_forward_references_and_chains() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func f(a: < <Wrapper as Container>::Item as Element>::Value,
				b: <Inner as Element>::Value) {}
			trait Container { type Item; }
			trait Element { type Value; }
			struct Wrapper();
			struct Inner();
			impl Container for Wrapper { type Item = Inner; }
			impl Element for Inner { type Value = i32; }
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		// Both paths name items declared after the function, and both mean `i32`.
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::I32);
	}

	/// The suggested spelling of a diagnostic: what its first note puts in
	/// backticks after "qualify the trait".
	fn suggested_spelling(diagnostic: &Diagnostic<FileId>) -> String {
		let note = diagnostic
			.notes
			.iter()
			.find(|note| note.starts_with("qualify the trait: `"))
			.expect("a suggestion note");
		let start = note.find('`').unwrap() + 1;
		let end = note.rfind('`').unwrap();
		note[start..end].to_string()
	}

	#[test]
	fn a_member_of_a_concrete_projection_needs_the_trait_qualified() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			trait Element { type Value; }
			struct Wrapper();
			struct Inner();
			impl Container for Wrapper { type Item = Inner; }
			impl Element for Inner { type Value = i32; }
			func unqualified(a: Wrapper::Item::Value) {}
			func partly(b: <Wrapper as Container>::Item::Value) {}
		"}
		);
		// `Wrapper::Item` is selected from the impl index, but its member
		// `Value` takes the impl's value (`Inner`) to find. The error says so,
		// and says how to write it, as rustc does.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMemberNeedsQualification,
			DiagnosticCode::TypeMemberNeedsQualification,
		]);
		for diagnostic in &*case.context.diagnostics {
			assert_eq!(diagnostic.message, "ambiguous associated type `Value`");
			assert_eq!(
				suggested_spelling(diagnostic),
				"<<Wrapper as Container>::Item as Element>::Value"
			);
		}
		// The unqualified type is lowered to `ERROR` in place.
		for name in ["unqualified", "partly"] {
			assert_eq!(
				case.function_signature(name).param_types[0],
				TypeIndex::ERROR
			);
		}
	}

	#[test]
	fn the_suggested_qualification_is_accepted_and_means_the_member() {
		let suggestion = {
			test_case!(
				case = indoc! {"
				type i32;
				trait Container { type Item; }
				trait Element { type Value; }
				struct Wrapper();
				struct Inner();
				impl Container for Wrapper { type Item = Inner; }
				impl Element for Inner { type Value = i32; }
				func f(a: Wrapper::Item::Value) {}
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
			"}
			);
			suggested_spelling(&case.context.diagnostics[0])
		};
		// Writing exactly what the compiler suggested is clean and means `i32`.
		test_case!(
			mut case = &format!(
				"
			type i32;
			trait Container {{ type Item; }}
			trait Element {{ type Value; }}
			struct Wrapper();
			struct Inner();
			impl Container for Wrapper {{ type Item = Inner; }}
			impl Element for Inner {{ type Value = i32; }}
			func f(a: {suggestion}) {{}}
			pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}
		"
			)
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
	}

	#[test]
	fn every_trait_that_could_supply_the_member_is_suggested() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			trait Element { type Value; }
			trait Measure { type Value; }
			struct Wrapper();
			struct Inner();
			impl Container for Wrapper { type Item = Inner; }
			impl Element for Inner { type Value = i32; }
			impl Measure for Inner { type Value = i32; }
			func f(a: Wrapper::Item::Value) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMemberNeedsQualification]);
		let notes = &case.context.diagnostics[0].notes;
		assert_eq!(notes.len(), 2, "{notes:?}");
		for trait_name in ["Element", "Measure"] {
			assert!(
				notes.iter().any(|note| note.contains(&format!(
					"<<Wrapper as Container>::Item as {trait_name}>::Value"
				))),
				"{notes:?}"
			);
		}
	}

	#[test]
	fn the_suggestion_also_resolves_through_an_abstract_value() {
		// The projection's value is a type parameter, only by way of the impl.
		const DECLARATIONS: &str = "
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			trait Element { type Value; }
			struct Wrap<X>();
			impl<X: Element> Container for Wrap<X> { type Item = X; }
		";
		let suggestion = {
			test_case!(
				case = &format!(
					"{DECLARATIONS} func f<Y: Element>(a: Wrap<Y>::Item::Value) {{}}"
				)
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TypeMemberNeedsQualification]);
			suggested_spelling(&case.context.diagnostics[0])
		};
		assert_eq!(
			suggestion,
			"<<Wrap<Y> as Container>::Item as Element>::Value"
		);
		test_case!(
			case = &format!(
				"{DECLARATIONS} func f<Y: Element>(a: {suggestion}) {{}}"
			)
		);
		case.diagnostics().assert_none();
	}
	#[test]
	fn a_name_no_trait_of_the_value_declares_is_not_suggested() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Container { type Item; }
			trait Other { type Value; }
			struct Wrapper();
			struct Inner();
			impl Container for Wrapper { type Item = Inner; }
			func f(a: Wrapper::Item::Value) {}
		"}
		);
		// `Other` declares `Value`, but `Inner` does not implement it: there is
		// nothing to qualify with, so it is a plain missing member.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::NotATraitMember]);
	}
	#[test]
	fn concrete_projections_normalize_in_compound_signatures() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			type u32;
			trait Memory { type Size; }
			memory heap: u32;
			trait Container { type Item; }
			struct Wrapper();
			impl Container for Wrapper { type Item = i32; }
			type Actual = func((Wrapper::Item, Wrapper::Item), *Wrapper::Item) -> Wrapper::Item;
			type Expected = func((i32, i32), *i32) -> i32;
			func f(a: Actual, b: Expected) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		// Written differently, the same function type once normalized.
		let actual = case.normalized_param("f", 0);
		assert_eq!(actual, case.normalized_param("f", 1));
		assert_ne!(actual, case.function_signature("f").param_types[0]);
	}

	/// A loop through two impl values has no single owner: each value is a
	/// written site, each site's well-formedness check walks the whole loop, and
	/// queries do not remember that the loop was already reported. So it is
	/// reported once at each value. This pins exactly that, so a future memo
	/// that reports a loop once shows up as a deliberate change here.
	#[test]
	fn a_loop_through_two_impl_values_is_reported_once_at_the_first() {
		const SOURCE: &str = indoc! {"
			trait Pair { type First; type Second; }
			struct Example();
			impl Pair for Example {
			    type First = Self::Second;
			    type Second = Self::First;
			}
		"};
		test_case!(case = SOURCE);
		// A loop has no root cause, so the definitions own it: the first value
		// checked finds it and reports; the other reads a poisoned value and is
		// silent.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
		let first_value = {
			let from = SOURCE.find("type First").unwrap();
			let start = from + SOURCE[from..].find("Self::Second").unwrap();
			start..start + "Self::Second".len()
		};
		let diagnostic = &case.context.diagnostics[0];
		// Checking `First`'s value starts the walk at `Second`:
		//   Second -> (its value) First -> (its value) Second, closed.
		assert_eq!(diagnostic.labels[0].range, first_value);
		assert_eq!(
			diagnostic.message,
			"cycle detected when normalizing `<Example as Pair>::Second`"
		);
		let steps: Vec<_> = diagnostic
			.labels
			.iter()
			.skip(1)
			.map(|label| label.message.as_str())
			.collect();
		assert_eq!(steps.len(), 2, "{steps:?}");
		for projection in ["First", "Second"] {
			assert!(
				steps.iter().any(|step| step
					.contains(&format!("`<Example as Pair>::{projection}`"))),
				"{steps:?}"
			);
		}
		// Both verdicts are recorded: the owner's and the derived one.
		let poisoned: Vec<_> = case
			.context
			.solver
			.verdicts
			.values()
			.filter_map(|value| match value {
				AssocValue::Overflowed | AssocValue::Cyclic(_) => Some(true),
				AssocValue::Poisoned => Some(false),
				_ => None,
			})
			.collect();
		assert_eq!(poisoned.len(), 2, "{poisoned:?}");
		assert_eq!(
			poisoned.iter().filter(|owned| **owned).count(),
			1,
			"{poisoned:?}"
		);
	}

	#[test]
	fn a_loop_through_definitions_is_reported_once_whatever_the_source_order() {
		// A use that comes first in the source, or that enters the loop at
		// another member, must change neither the count nor where it is
		// reported: the verdict is the solver's, owned by the first definition.
		for use_site in [
			"func use_it(x: <Example as Pair>::First) {}",
			"func use_it(x: <Example as Pair>::Second) {}",
		] {
			for (before, after) in [(use_site, ""), ("", use_site)] {
				let source = format!(
					"
				trait Pair {{ type First; type Second; }}
				struct Example();
				{before}
				impl Pair for Example {{
				    type First = Self::Second;
				    type Second = Self::First;
				}}
				{after}
				pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}
			"
				);
				test_case!(case = &source);
				case.diagnostics()
					.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
				let first_value = {
					let from = source.find("type First").unwrap();
					let start =
						from + source[from..].find("Self::Second").unwrap();
					start..start + "Self::Second".len()
				};
				let diagnostic = &case.context.diagnostics[0];
				assert_eq!(diagnostic.labels[0].range, first_value, "{source}");
				assert_eq!(
					diagnostic.message,
					"cycle detected when normalizing `<Example as Pair>::Second`",
					"{source}"
				);
			}
		}
	}

	#[test]
	fn an_overflowing_value_is_reported_once_and_poisoned() {
		// The value is checked with nothing in flight, so if it runs out of
		// budget there, every reader (which starts deeper) would too. It is a
		// verdict on the definition: reported at the definition, and the readers
		// stay silent.
		const SOURCE: &str = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Project { type Out; }
			struct Wrap<T>();
			impl<T: Project> Project for Wrap<T> { type Out = T::Out; }
			struct Leaf();
			impl Project for Leaf { type Out = i32; }
			impl Project for i32 { type Out = <Wrap<Wrap<Wrap<Wrap<Leaf>>>> as Project>::Out; }
			func first(x: <i32 as Project>::Out) {}
			func second(x: <i32 as Project>::Out) {}
		"};
		with_pending_signatures(SOURCE, |builder| {
			builder.solver.set_limit_for_test(3);
			builder.sweep();
			let readers = SOURCE.find("func first").unwrap();
			let value_start = SOURCE.find("<Wrap<Wrap<").unwrap();
			let value_end = value_start
				+ SOURCE[value_start..].find("::Out;").unwrap()
				+ "::Out".len();
			let overflows: Vec<_> = builder
				.diagnostics
				.iter()
				.filter(|diagnostic| {
					diagnostic.code.as_deref()
						== Some(
							DiagnosticCode::TypeNormalizationOverflow.code(),
						)
				})
				.collect();
			// The value itself reports once (its path's own membership check is
			// a separate site); no reader reports.
			assert_eq!(
				overflows
					.iter()
					.filter(|d| d.labels[0].range == (value_start..value_end))
					.count(),
				1,
				"{overflows:?}"
			);
			assert!(
				overflows.iter().all(|d| d.labels[0].range.end <= readers),
				"{overflows:?}"
			);
			assert!(builder.solver.verdicts.values().any(|value| matches!(
				value,
				AssocValue::Poisoned
					| AssocValue::Overflowed
					| AssocValue::Cyclic(_)
			)));
		});
	}

	#[test]
	fn unused_associated_values_are_checked_for_direct_and_mutual_cycles() {
		// A loop through definitions is one error, however many values close it:
		// the first value checked reports it and poisons itself, and the others
		// read a poisoned value (see `notes/tir-check-pass.md`).
		for (definitions, reports) in [
			("type First = Self::First; type Second = i32;", 1),
			("type First = Self::Second; type Second = Self::First;", 1),
			(
				"type First = (Self::Second, Self::Second); type Second = Self::First;",
				1,
			),
		] {
			test_case!(
				case = &format!(
					"
				type i32;
				trait Pair {{ type First; type Second; }}
				struct Example();
				impl Pair for Example {{ {definitions} }}
				func independent(x: i32) {{}}
				pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}
			"
				)
			);
			assert_eq!(
				case.context.diagnostics.len(),
				reports,
				"{:?}",
				case.context.diagnostics
			);
			for diagnostic in &*case.context.diagnostics {
				assert_eq!(
					diagnostic.code.as_deref(),
					Some(DiagnosticCode::CyclicAssociatedType.code())
				);
			}
			assert_eq!(
				case.function_signature("independent").param_types[0],
				TypeIndex::I32
			);
		}
	}

	#[test]
	fn synthetic_values_normalize_and_synthetic_cycles_recover() {
		test_case!(
			mut case = indoc! {r#"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			trait Global { type Value; }
			trait Container { type Item; }
			struct Wrapper();
			impl Container for Wrapper { type Item = u32; }
			func f(a: heap::Size, b: host::shared::Size) {}
			memory heap: Wrapper::Item;
			global counter: Wrapper::Item = 0;
			import "env" as host { memory shared: Wrapper::Item; global counter: Wrapper::Item; }
		"#}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::U32);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::U32);
		// Each global's value is stored as written (`Wrapper::Item`) and means
		// `u32`.
		let values: Vec<_> = case
			.defs
			.globals
			.iter()
			.map(|def| {
				case.context.assoc_types
					[usize::from(def.value_assoc_type_index)]
				.as_ref()
				.unwrap()
				.value
				.unwrap()
			})
			.collect();
		assert!(!values.is_empty());
		for written in values {
			assert_eq!(
				case.normalized(TypeEnvIdx::ROOT, written),
				TypeIndex::U32
			);
		}
		for declaration in [
			"memory heap: heap::Size;",
			"import \"env\" as host { memory heap: host::heap::Size; }",
		] {
			test_case!(
				mut case = &format!("trait Memory {{ type Size; }} {declaration}")
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
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
			struct Wrapper();
			impl Container for Wrapper { type Item = i32; }
		"},
			|builder| {
				let receiver =
					builder.types.intern_struct(StructIdx::new(0), &[]);
				let (declaration, provider, reference) =
					selected_provider(builder, receiver, "Item");
				let projection =
					builder.types.intern(Type::AssocTypeProjection {
						base: receiver,
						trait_index: TraitIdx::new(0),
						assoc_type_index: declaration,
					});
				let tuple =
					builder.types.intern_tuple(&[projection, TypeIndex::I32]);
				// A completed stored value can still contain an abstract projection
				// that becomes reducible later. Here it models that result directly.
				builder.assoc_types[usize::from(provider)] =
					Some(AssocTypeSignature {
						declared_bounds: Box::new([]),
						facts: BoundFacts::Ready(Box::new([])),
						value: Some(tuple),
					});
				assert_eq!(
					builder.normalize_head(
						TypeEnvIdx::ROOT,
						projection,
						reference
					),
					tuple
				);
				assert_eq!(
					builder.normalize_head(TypeEnvIdx::ROOT, tuple, reference),
					tuple
				);
				// The stored value contains the projection that reads it: a cycle.
				// Deep normalization returns it and reports nothing; the site that
				// asked owns the report.
				assert!(matches!(
					builder.normalize_type_query(TypeEnvIdx::ROOT, projection),
					Err(SolverError::Cycle(_))
				));
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
				assert_eq!(
					builder
						.normalize_type_query(TypeEnvIdx::ROOT, TypeIndex::I32),
					Ok(TypeIndex::I32)
				);
			},
		);
	}

	#[test]
	fn normalization_preserves_abstract_and_inference_projections() {
		with_pending_signatures(
			"pub trait Call { type Args; type Result; } pub trait Function: Call {} trait Container { type Item; } func f<T>() {}",
			|builder| {
				let def_id = DefId::Function(FunctionIdx::new(0));
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
						builder.normalize_head(
							TypeEnvIdx::ROOT,
							projection,
							reference
						),
						projection
					);
					assert_eq!(
						builder.normalize_type(
							TypeEnvIdx::ROOT,
							projection,
							reference
						),
						projection
					);
				}
				let error = builder.types.intern(Type::AssocTypeProjection {
					base: TypeIndex::ERROR,
					trait_index: TraitIdx::new(0),
					assoc_type_index: declaration,
				});
				assert_eq!(
					builder.normalize_type(TypeEnvIdx::ROOT, error, reference),
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
			struct Wrapper();
			impl Container for Wrapper { type Item = i32; }
			func marker() {}
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
		"},
			|builder| {
				use crate::ast::Ownership;
				let receiver =
					builder.types.intern_struct(StructIdx::new(0), &[]);
				let (declaration, _, reference) =
					selected_provider(builder, receiver, "Item");
				let projection =
					builder.types.intern(Type::AssocTypeProjection {
						base: receiver,
						trait_index: TraitIdx::new(0),
						assoc_type_index: declaration,
					});
				let cases = [
					(
						builder
							.types
							.intern_tuple(&[projection, TypeIndex::I32]),
						builder
							.types
							.intern_tuple(&[TypeIndex::I32, TypeIndex::I32]),
					),
					(
						builder
							.types
							.intern_struct(StructIdx::new(0), &[projection]),
						builder.types.intern_struct(
							StructIdx::new(0),
							&[TypeIndex::I32],
						),
					),
					(
						builder.types.intern_function(
							FunctionIdx::new(0),
							&[projection],
						),
						builder.types.intern_function(
							FunctionIdx::new(0),
							&[TypeIndex::I32],
						),
					),
					(
						builder.types.intern(Type::FunctionRef {
							param: projection,
							result: projection,
						}),
						builder.types.intern(Type::FunctionRef {
							param: TypeIndex::I32,
							result: TypeIndex::I32,
						}),
					),
					(
						builder.types.intern(Type::Pointer {
							to: projection,
							memory: projection,
							ownership: Ownership::Shared,
						}),
						builder.types.intern(Type::Pointer {
							to: TypeIndex::I32,
							memory: TypeIndex::I32,
							ownership: Ownership::Shared,
						}),
					),
					(
						builder.types.intern(Type::Array {
							of: projection,
							size: 7,
							memory: projection,
							ownership: Ownership::Exclusive,
						}),
						builder.types.intern(Type::Array {
							of: TypeIndex::I32,
							size: 7,
							memory: TypeIndex::I32,
							ownership: Ownership::Exclusive,
						}),
					),
					(
						builder.types.intern(Type::Slice {
							of: projection,
							memory: projection,
							ownership: Ownership::Shared,
						}),
						builder.types.intern(Type::Slice {
							of: TypeIndex::I32,
							memory: TypeIndex::I32,
							ownership: Ownership::Shared,
						}),
					),
				];
				for (before, after) in cases {
					assert_eq!(
						builder.normalize_head(
							TypeEnvIdx::ROOT,
							before,
							reference
						),
						before
					);
					assert_eq!(
						builder.normalize_type(
							TypeEnvIdx::ROOT,
							before,
							reference
						),
						after
					);
					assert_eq!(
						builder.normalize_type(
							TypeEnvIdx::ROOT,
							after,
							reference
						),
						after
					);
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
			"type i32; trait Container { type Item; } struct Wrapper(); impl Container for Wrapper { type Item = i32; }",
			|builder| {
				let receiver =
					builder.types.intern_struct(StructIdx::new(0), &[]);
				let (declaration, _, reference) =
					selected_provider(builder, receiver, "Item");
				let projection =
					builder.types.intern(Type::AssocTypeProjection {
						base: receiver,
						trait_index: TraitIdx::new(0),
						assoc_type_index: declaration,
					});
				let pair =
					builder.types.intern_tuple(&[projection, projection]);
				let expected = builder
					.types
					.intern_tuple(&[TypeIndex::I32, TypeIndex::I32]);
				assert_eq!(
					builder.normalize_type(TypeEnvIdx::ROOT, pair, reference),
					expected
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
	fn normalization_depth_limit_reports_once_and_unwinds() {
		with_pending_signatures("trait Container { type Item; }", |builder| {
			let reference = SourceSpan::new(
				builder.defs.traits[0].file_id,
				TextSpan::new(0, 1),
			);
			builder.solver.set_limit_for_test(4);
			let mut nested = TypeIndex::I32;
			for _ in 0..5 {
				nested = builder.types.intern_tuple(&[nested]);
			}
			assert_eq!(
				builder.normalize_type(TypeEnvIdx::ROOT, nested, reference),
				TypeIndex::ERROR
			);
			assert_eq!(builder.diagnostics.len(), 1);
			assert_eq!(
				builder.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TypeNormalizationOverflow.code())
			);
			assert_eq!(
				builder.normalize_type(
					TypeEnvIdx::ROOT,
					TypeIndex::I32,
					reference
				),
				TypeIndex::I32
			);
		});
	}

	#[test]
	fn distinct_projection_chain_hits_depth_limit_without_exact_repetition() {
		with_pending_signatures(
			"pub trait Call { type Args; type Result; } pub trait Function: Call {} trait Container { type Item; } func f<T>() {}",
			|builder| {
				let def_id = DefId::Function(FunctionIdx::new(0));
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
				builder.solver.set_limit_for_test(6);
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
					builder.normalize_type(TypeEnvIdx::ROOT, nested, reference),
					TypeIndex::ERROR
				);
				assert_eq!(builder.diagnostics.len(), 1);
				assert_eq!(
					builder.diagnostics[0].code.as_deref(),
					Some(DiagnosticCode::TypeNormalizationOverflow.code())
				);
				builder.solver.set_limit_for_test(128);
				assert_eq!(
					builder.normalize_type(TypeEnvIdx::ROOT, nested, reference),
					nested
				);
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
			test_case!(
				case = &format!(
					"
				pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}
				trait Container {{ type Item; }}
				struct Wrapper();
				impl Container for Wrapper {{ type Item = Missing; }}
				func f(x: {ty}) {{}}
			"
				)
			);
			// The invalid impl RHS and (where present) the written `Missing`
			// receiver each own an error, with no member-lookup cascades. The
			// last path selects `Next` off a valid projection whose `Item`
			// declares no such member: that is its own, independent error.
			let expected: &[DiagnosticCode] = if ty.ends_with("::Next") {
				&[
					DiagnosticCode::UndeclaredIdentifier,
					DiagnosticCode::NotATraitMember,
				]
			} else {
				&[
					DiagnosticCode::UndeclaredIdentifier,
					DiagnosticCode::UndeclaredIdentifier,
				]
			};
			case.diagnostics().assert_codes(expected);
			assert_eq!(
				case.function_signature("f").param_types[0],
				TypeIndex::ERROR
			);
		}
	}

	#[test]
	fn qualified_path_resolves_a_concrete_impls_associated_type() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			struct Wrapper();
			impl Container for Wrapper { type Item = i32; }
			func f(x: <Wrapper as Container>::Item) { }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
	}

	#[test]
	fn generic_impl_projection_substitutes_its_own_target_arguments() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			type u32;
			trait Container { type Item; }
			struct Wrapper<T>();
			impl<T> Container for Wrapper<T> { type Item = T; }
			func first(x: <Wrapper<i32> as Container>::Item) {}
			func second(x: <Wrapper<u32> as Container>::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("first", 0), TypeIndex::I32);
		assert_eq!(case.normalized_param("second", 0), TypeIndex::U32);
	}

	#[test]
	fn generic_impl_target_matches_nested_and_repeated_arguments() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			type u32;
			trait Container { type Item; }
			struct Inner<T>();
			struct Pair<A, B>();
			impl<T> Container for Pair<Inner<T>, Inner<T>> { type Item = T; }
			func good(x: <Pair<Inner<i32>, Inner<i32>> as Container>::Item) {}
			func bad(x: <Pair<Inner<i32>, Inner<u32>> as Container>::Item) {}
		"}
		);
		assert_eq!(case.normalized_param("good", 0), TypeIndex::I32);
		// Diagnosed below; the written projection is kept and has no value.
		assert!(case.is_projection_param("bad", 0));
		assert_eq!(
			case.try_normalized_param("bad", 0),
			Err(SolverError::Poisoned)
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
	}

	#[test]
	fn generic_impl_requires_its_inferred_arguments_bounds() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Good {}
			trait Container { type Item; }
			struct Yes();
			struct No();
			struct Wrapper<T>();
			impl Good for Yes {}
			impl<T: Good> Container for Wrapper<T> { type Item = i32; }
			func good(x: <Wrapper<Yes> as Container>::Item) {}
			func bad(x: <Wrapper<No> as Container>::Item) {}
		"}
		);
		assert_eq!(case.normalized_param("good", 0), TypeIndex::I32);
		// Diagnosed below; the written projection is kept and has no value.
		assert!(case.is_projection_param("bad", 0));
		assert_eq!(
			case.try_normalized_param("bad", 0),
			Err(SolverError::Poisoned)
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
	}

	#[test]
	fn generic_impl_bound_checks_descend_through_nested_targets() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Mark {}
			trait Container { type Item; }
			struct Leaf();
			struct Missing();
			struct Wrap<T>();
			impl Mark for Leaf {}
			impl<T: Mark> Mark for Wrap<T> {}
			impl<T: Mark> Container for Wrap<T> { type Item = i32; }
			func good(x: <Wrap<Wrap<Leaf>> as Container>::Item) {}
			func bad(x: <Wrap<Wrap<Missing>> as Container>::Item) {}
		"}
		);
		assert_eq!(case.normalized_param("good", 0), TypeIndex::I32);
		// Diagnosed below; the written projection is kept and has no value.
		assert!(case.is_projection_param("bad", 0));
		assert_eq!(
			case.try_normalized_param("bad", 0),
			Err(SolverError::Poisoned)
		);
		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
	}

	#[test]
	fn generic_impl_with_undetermined_parameter_does_not_match() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			struct Wrapper<T>();
			impl<T> Container for Wrapper<i32> { type Item = T; }
			func f(x: <Wrapper<i32> as Container>::Item) {}
		"}
		);
		// Diagnosed below; the written projection is kept and has no value.
		assert!(case.is_projection_param("f", 0));
		assert_eq!(
			case.try_normalized_param("f", 0),
			Err(SolverError::Poisoned)
		);
		assert!(
			case.context.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::TraitBoundViolation.code())),
			"{:?}",
			case.context.diagnostics
		);
	}

	#[test]
	fn generic_impl_bound_equalities_are_not_silently_assumed() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Source { type Item; }
			trait Container { type Item; }
			struct Value();
			struct Wrapper<T>();
			impl Source for Value { type Item = i32; }
			impl<T: Source where { Item = i32 }> Container for Wrapper<T> {
				type Item = i32;
			}
			func f(x: <Wrapper<Value> as Container>::Item) {}
		"}
		);
		// Diagnosed below; the written projection is kept and has no value.
		assert!(case.is_projection_param("f", 0));
		assert_eq!(
			case.try_normalized_param("f", 0),
			Err(SolverError::Poisoned)
		);
		assert!(
			case.context.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::TraitBoundViolation.code())),
			"{:?}",
			case.context.diagnostics
		);
	}

	#[test]
	fn generic_projection_cycle_appears_only_after_substitution() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Project { type Out; }
			struct Wrap<T>();
			struct End();
			struct Loop();
			impl<T: Project> Project for Wrap<T> { type Out = T::Out; }
			impl Project for End { type Out = i32; }
			impl Project for Loop { type Out = Wrap<Loop>::Out; }
			func finite(x: <Wrap<End> as Project>::Out) {}
			func cyclic(x: <Wrap<Loop> as Project>::Out) {}
		"}
		);
		assert_eq!(case.normalized_param("finite", 0), TypeIndex::I32);
		// The loop exists only once `T := Loop` is substituted, but it passes
		// through `Loop`'s own value, a definition. The definitions are judged
		// first, so `Loop`'s value reports it once and is poisoned; `cyclic`'s
		// parameter then reaches that poisoned value and stays silent.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
		let signature = case.function_signature("cyclic");
		let (scope, written) =
			(signature.type_params, signature.param_types[0]);
		assert!(matches!(
			case.context.normalize_type_query(scope, written),
			Err(SolverError::Poisoned)
		));
	}

	#[test]
	fn qualified_path_naming_a_trait_the_concrete_type_does_not_implement_is_diagnosed()
	 {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Container { type Item; }
			struct Wrapper();
			func f(x: <Wrapper as Container>::Item) { }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::TraitBoundViolation.code())
		);
		// The unsatisfied requirement is diagnosed once, where it was written;
		// the type is kept as written.
		assert!(matches!(
			case.context
				.types
				.resolve(case.function_signature("f").param_types[0]),
			Type::AssocTypeProjection { .. }
		));
	}

	/// Regression test: `TraitAssocType`'s own arm used to resolve at
	/// `TypeEnvId::ROOT` instead of forcing the trait header and using its
	/// `self_scope`, the way `TraitFunction`/`TraitConst` already did — so
	/// `Self` silently failed to resolve inside a declared bound's own
	/// `where { .. }` clause (`type Item: Elem where { Assoc = Self::Item }`
	/// below). Fixed to mirror its sibling arms exactly.
	#[test]
	fn assoc_type_declared_bound_can_reference_the_traits_own_self() {
		test_case!(
			case = indoc! {"
			trait Elem { type Assoc; }
			trait Container {
				type Item: Elem where { Assoc = Self::Item };
			}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.assoc_type_signature("Container", "Item");
		let bound = case.context.bounds.get(sig.declared_bounds[0]);
		let SourceAssocBinding {
			kind: BindingRequirement::Equals(value),
			..
		} = &bound.bindings[0]
		else {
			panic!("expected an `Assoc = ..` binding");
		};

		let container_index = case.trait_index("Container");
		match case.context.types.resolve(value.inner) {
			Type::AssocTypeProjection {
				trait_index, base, ..
			} => {
				assert_eq!(*trait_index, container_index);
				match case.context.types.resolve(*base) {
					Type::TypeParam { env, param_index } => {
						assert_eq!(
							*env,
							case.context.traits[usize::from(container_index)]
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait HasSize { type Size; }
			func f<T: HasSize>(x: T::Size) -> T::Size { x }
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.function_signature("f");
		assert_eq!(
			sig.param_types[0], sig.return_type,
			"`x: T::Size` and `-> T::Size` should resolve to the same projection"
		);
		assert!(matches!(
			case.context.types.resolve(sig.return_type),
			Type::AssocTypeProjection { .. }
		));
	}

	#[test]
	fn a_missing_associated_type_on_a_bound_is_diagnosed() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Empty {}
			func f<T: Empty>(x: T::Missing) { }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::NotATraitMember.code())
		);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	#[test]
	fn two_bounds_both_declaring_the_same_associated_type_is_ambiguous() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait A { type X; }
			trait B { type X; }
			func f<T: A + B>(x: T::X) { }
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::AmbiguousTraitMember.code())
		);
		assert_eq!(
			case.function_signature("f").param_types[0],
			TypeIndex::ERROR
		);
	}

	/// Verified against real rustc (`trait B: A<X = u32> {}`, `trait C: A<X
	/// = u64> {}`, `func f<T: B + C>() {}`): rejected immediately with
	/// `E0284`, zero uses of `T` anywhere past the bound list — bound
	/// well-formedness is checked once at declaration, not deferred to
	/// first use. wx matches that here (see `ParamBounds::implied_bounds`);
	/// `a_functions_unused_bound_combination_with_conflicting_assoc_type_bindings_is_still_diagnosed`
	/// below re-checks the fully-unused case, which the old
	/// lazy-on-first-projection design let compile silently.
	#[test]
	fn a_functions_own_bound_combination_with_conflicting_assoc_type_bindings_is_diagnosed_eagerly()
	 {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			type u64;
			trait A { type X; }
			trait B: A where { X = u32 } {}
			trait C: A where { X = u64 } {}
			func f<T: B + C>(x: T::X) { }
		"}
		);

		case.diagnostics().print();

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"`T` requires conflicting bindings for `A::X`"
		);
		// The conflict is a fact about `A::X`'s *value*, not its identity —
		// `T::X` still names a perfectly real item (`A::X`), so it still
		// resolves to a normal projection rather than `TypeIndex::ERROR`.
		// Normalization cannot select either conflicting value, so the
		// existing bound-conflict diagnostic remains the only error.
		let param_ty = case.function_signature("f").param_types[0];
		match case.context.types.resolve(param_ty) {
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			type u64;
			trait A { type X; }
			trait B: A where { X = u32 } {}
			trait C: A where { X = u64 } {}
			func f<T: B + C>() { }
		"}
		);

		case.diagnostics().print();

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		assert_eq!(
			case.context.diagnostics[0].message,
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
		test_case!(case = source);

		case.diagnostics().print();

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::DuplicateAssocTypeBinding.code())
		);
		let labels = &case.context.diagnostics[0].labels;
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
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		let labels = &case.context.diagnostics[0].labels;
		assert_eq!(labels.len(), 3);
		assert_eq!(&source[labels[0].range.clone()], "u64");
		assert_eq!(&source[labels[1].range.clone()], "u32");
		assert_eq!(&source[labels[2].range.clone()], "A where { X = u64 }");
	}

	#[test]
	fn conflicting_binding_does_not_poison_another_associated_type() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			type u64;
			trait A { type X; type Y; }
			trait B: A where { X = u32 } {}
			trait C: A where { X = u64 } {}
			func f<T: B + C>(x: T::Y) {}
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
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
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		let labels = &case.context.diagnostics[0].labels;
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
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		let labels = &case.context.diagnostics[0].labels;
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
		test_case!(case = source);

		case.diagnostics().print();

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(
			case.context.diagnostics[0].message,
			"`D` requires conflicting bindings for `Inner::X`"
		);
		let labels = &case.context.diagnostics[0].labels;
		assert_eq!(&source[labels[0].range.clone()], "u64");
		assert_eq!(&source[labels[1].range.clone()], "u32");
		let env = case.context.traits[usize::from(case.trait_index("D"))].env;
		let merged = case.context.param_bounds[usize::from(env)][0]
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
		test_case!(case = source);

		assert_eq!(
			case.context.diagnostics.len(),
			2,
			"{:?}",
			case.context.diagnostics
		);
		for trait_name in ["D", "E"] {
			let env = case.context.traits
				[usize::from(case.trait_index(trait_name))]
			.env;
			let merged = case.context.param_bounds[usize::from(env)][0]
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
		test_case!(
			case = indoc! {"
			type u32;
			type u64;
			trait Inner { type X; }
			trait Outer { type Item; }
			trait D: Outer where { Item: Inner where { X = u32 } + Inner where { X = u64 } } {}
			trait E: D {}
		"}
		);

		assert_eq!(
			case.context.diagnostics.len(),
			1,
			"{:?}",
			case.context.diagnostics
		);
	}

	#[test]
	fn equality_wins_over_associated_type_bounds_in_either_order() {
		test_case!(
			case = indoc! {"
			type u32;
			trait Mark {}
			trait A { type X; }
			trait D: A where { X: Mark } + A where { X = u32 } {}
			trait E: A where { X = u32 } + A where { X: Mark } {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for trait_name in ["D", "E"] {
			let env = case.context.traits
				[usize::from(case.trait_index(trait_name))]
			.env;
			let bounds = &case.context.param_bounds[usize::from(env)][0];
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
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			struct Wrapper();
			impl Container for Wrapper { type Item = i32; }
			func direct<T: Container where { Item = i32 }>(x: T::Item) {}
			func chained<T: Container where { Item = <Wrapper as Container>::Item }>(x: T::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["direct", "chained"] {
			assert_eq!(case.normalized_param(name, 0), TypeIndex::I32);
		}
	}

	#[test]
	fn normalization_rebinds_self_through_multiple_supertraits() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Base { type Item; }
			trait Middle: Base where { Item = Self } {}
			trait Final: Middle {}
			func f<T: Final>(x: T::Item) {}
			func g<U: Final>(x: U::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["f", "g"] {
			let scope = case.function_signature(name).type_params;
			let ty = case.normalized_param(name, 0);
			assert!(
				matches!(case.context.types.resolve(ty), Type::TypeParam { env, param_index: 0 } if *env == scope)
			);
		}
	}

	#[test]
	fn normalization_reads_nested_constraints_and_deduplicates_memberships() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item: Inner; }
			func f<T: Outer where { Item: Inner where { Value = i32 } }>(x: T::Item::Value) {}
			func g<T: Outer where { Item: Inner where { Value = i32 } }>(x: <T::Item as Inner>::Value) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["f", "g"] {
			assert_eq!(case.normalized_param(name, 0), TypeIndex::I32);
		}
	}

	#[test]
	fn normalization_reads_nested_constraints_without_a_declared_trait_bound() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item; }
			func f<T: Outer where { Item: Inner where { Value = i32 } }>(x: T::Item::Value) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
	}

	#[test]
	fn normalization_rebinds_self_in_inherited_nested_facts() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Inner { type Value; }
			trait Outer { type Item; }
			trait Middle: Outer where { Item: Inner where { Value = Self } } {}
			trait Final: Middle {}
			func f<T: Final>(x: T::Item::Value) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let scope = case.function_signature("f").type_params;
		let ty = case.normalized_param("f", 0);
		assert!(
			matches!(case.context.types.resolve(ty), Type::TypeParam { env, param_index: 0 } if *env == scope)
		);
	}

	#[test]
	fn normalization_rebinds_self_in_associated_declaration_facts() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Inner { type Value; }
			trait Outer { type Item: Inner where { Value = Self }; }
			func f<T: Outer>(x: T::Item::Value) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let scope = case.function_signature("f").type_params;
		let ty = case.normalized_param("f", 0);
		assert!(
			matches!(case.context.types.resolve(ty), Type::TypeParam { env, param_index: 0 } if *env == scope)
		);
	}

	#[test]
	fn normalization_preserves_nested_facts_when_an_outer_equality_supplies_a_value()
	 {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item; }
			func f<T: Outer where { Item = U } + Outer where { Item: Inner where { Value = i32 } }, U>(x: T::Item::Value) {}
			func g<T: Outer where { Item: Inner where { Value = i32 } } + Outer where { Item = U }, U>(x: <T::Item as Inner>::Value) {}
			func h<T: Outer where { Item = U } + Outer where { Item: Inner where { Value = i32 } }, U>(x: <T::Item>::Value) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["f", "g", "h"] {
			assert_eq!(case.normalized_param(name, 0), TypeIndex::I32);
		}
	}

	#[test]
	fn normalization_resolves_sibling_projection_equalities_in_either_order() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			func f<T: Container where { Item = U::Item }, U: Container where { Item = i32 }>(x: T::Item) {}
			func g<U: Container where { Item = i32 }, T: Container where { Item = U::Item }>(x: T::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["f", "g"] {
			assert_eq!(case.normalized_param(name, 0), TypeIndex::I32);
		}
	}

	#[test]
	fn normalization_handles_reciprocal_integer_facts_without_conformance_checks()
	 {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			type i8;
			trait UnsignedInt { type Signed: SignedInt where { Unsigned = Self }; }
			trait SignedInt { type Unsigned: UnsignedInt where { Signed = Self }; }
			impl UnsignedInt for u8 { type Signed = i8; }
			impl SignedInt for i8 { type Unsigned = u8; }
			func f<T: UnsignedInt>(x: <T::Signed as SignedInt>::Unsigned) {}
			func g<T: SignedInt>(x: <T::Unsigned as UnsignedInt>::Signed) {}
			func concrete(x: <u8 as UnsignedInt>::Signed::Unsigned) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["f", "g"] {
			let scope = case.function_signature(name).type_params;
			let ty = case.normalized_param(name, 0);
			assert!(
				matches!(case.context.types.resolve(ty), Type::TypeParam { env, param_index: 0 } if *env == scope)
			);
		}
		assert_eq!(case.normalized_param("concrete", 0), TypeIndex::U8);
	}

	#[test]
	fn normalization_blocks_tautological_mutual_and_structural_abstract_equalities()
	 {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Pair { type First; type Second; }
			func tautology<T: Pair where { First = T::First }>(x: T::First) {}
			func mutual<T: Pair where { First = T::Second, Second = T::First }>(x: T::First, y: T::Second) {}
			func structural<T: Pair where { First = (T::First,) }>(x: T::First) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["tautology", "mutual", "structural"] {
			for &ty in &case.function_signature(name).param_types {
				assert!(matches!(
					case.context.types.resolve(ty),
					Type::AssocTypeProjection { .. }
				));
			}
		}
	}

	#[test]
	fn normalization_leaves_competing_symbolic_equalities_unresolved() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			func f<T: Container where { Item = U } + Container where { Item = V }, U, V>(x: T::Item) {}
			func equivalent<T: Container where { Item = U::Item } + Container where { Item = i32 }, U: Container where { Item = i32 }>(x: T::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["f", "equivalent"] {
			assert!(matches!(
				case.context
					.types
					.resolve(case.function_signature(name).param_types[0]),
				Type::AssocTypeProjection { .. }
			));
		}
	}

	#[test]
	fn collecting_equality_facts_does_not_check_associated_value_conformance() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Mark {}
			trait Container { type Item: Mark; }
			func f<T: Container where { Item = i32 }>(x: T::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
	}

	#[test]
	fn normalization_does_not_cache_an_unfinished_assumption_set() {
		with_pending_signatures(
			"type i32; trait Container { type Item; } func f<T: Container where { Item = i32 }>() {} pub trait Call { type Args; type Result; } pub trait Function: Call {}",
			|builder| {
				let def_id = DefId::Function(FunctionIdx::new(0));
				let _ = builder.ensure_signature(QueryInfo {
					def_id,
					requested_at: None,
				});
				let env = builder.functions[0].type_params;
				let base = builder.type_envs.params(env)[0].ty;
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
				let facts = builder.param_bounds[usize::from(env)][0]
					.facts
					.current()
					.to_vec()
					.into_boxed_slice();
				builder.param_bounds[usize::from(env)][0].facts =
					BoundFacts::Provisional(facts.clone());
				assert_eq!(
					builder.normalize_type_query(env, projection),
					Err(SolverError::Pending)
				);
				builder.param_bounds[usize::from(env)][0].facts =
					BoundFacts::Ready(facts);
				assert_eq!(
					builder.normalize_type_query(env, projection),
					Ok(TypeIndex::I32)
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
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Inner { type Value; }
			trait Outer { type Item: Inner where { Value = Self }; }
			func f<T: Outer where { Item: Inner where { Value = T } }>(x: T::Item::Value) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let scope = case.function_signature("f").type_params;
		let ty = case.normalized_param("f", 0);
		assert!(
			matches!(case.context.types.resolve(ty), Type::TypeParam { env, param_index: 0 } if *env == scope)
		);
	}

	#[test]
	fn equality_rhs_can_read_a_later_siblings_nested_memberships() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Inner { type Value; }
			trait Outer { type Item; }
			func f<T: Outer where { Item = U::Item::Value }, U: Outer where { Item: Inner where { Value = i32 } }>(x: T::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
	}

	#[test]
	fn mutually_referencing_associated_bound_facts_do_not_require_conformance()
	{
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Value { type Item; }
			trait Pair {
				type First: Value where { Item = Self::Second::Item };
				type Second: Value where { Item = Self::First::Item };
			}
			func f<T: Pair>(x: T::First::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		assert!(matches!(
			case.context
				.types
				.resolve(case.function_signature("f").param_types[0]),
			Type::AssocTypeProjection { .. }
		));
	}
	#[test]
	fn normalization_reads_facts_through_multiple_nested_projection_sources() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Leaf { type Value; }
			trait Branch { type Item; }
			trait Outer { type Branch; }
			func f<T: Outer where { Branch: Branch where { Item: Leaf where { Value = i32 } } }>(x: T::Branch::Item::Value) {}
			func g<T: Outer where { Branch: Branch where { Item: Leaf where { Value = i32 } } }>(x: <T::Branch::Item as Leaf>::Value) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["f", "g"] {
			assert_eq!(case.normalized_param(name, 0), TypeIndex::I32);
		}
	}

	#[test]
	fn nested_projection_sources_keep_the_declaring_self_context() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Leaf { type Value; }
			trait Branch { type Item; }
			trait Marked: Branch where { Item: Leaf where { Value = Self } } {}
			trait Outer { type Branch: Marked; }
			func f<T: Outer>(x: T::Branch::Item::Value, y: T::Branch) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		// Written differently (`T::Branch::Item::Value` and `T::Branch`), the
		// same type once the nested `Value = Self` is read with `Self` rebound.
		let value = case.normalized_param("f", 0);
		assert_eq!(value, case.normalized_param("f", 1));
	}

	#[test]
	fn source_equalities_preserve_projections_inside_compound_types() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Container { type Item; }
			struct Wrap<X>();
			func f<U: Container where { Item = i32 }, T: Container where { Item = Wrap<(U::Item,)> }>(x: T::Item) {}
			func g<T: Container where { Item = Wrap<(U::Item,)> }, U: Container where { Item = i32 }>(x: T::Item) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for (name, t_index, u_index) in [("f", 1, 0), ("g", 0, 1)] {
			let signature = case.function_signature(name);
			let source = case.declared_bounds(signature.type_params, t_index);
			let BindingRequirement::Equals(value) = source[0].bindings[0].kind
			else {
				panic!("expected equality");
			};
			let types = &case.context.types;
			let Type::Struct { type_args, .. } = types.resolve(value.inner)
			else {
				panic!("expected Wrap");
			};
			let Type::Tuple { elements } =
				types.resolve(types.list(*type_args)[0])
			else {
				panic!("expected tuple");
			};
			let Type::AssocTypeProjection { base, .. } =
				types.resolve(types.list(*elements)[0])
			else {
				panic!("source must retain U::Item");
			};
			assert!(
				matches!(types.resolve(*base), Type::TypeParam { env, param_index } if *env == signature.type_params && *param_index == u_index)
			);
			let (scope, written) =
				(signature.type_params, signature.param_types[0]);
			let normalized = case.normalized(scope, written);
			let types = &case.context.types;
			let Type::Struct { type_args, .. } = types.resolve(normalized)
			else {
				panic!("expected normalized Wrap");
			};
			let Type::Tuple { elements } =
				types.resolve(types.list(*type_args)[0])
			else {
				panic!("expected normalized tuple");
			};
			assert_eq!(case.context.types.list(*elements), &[TypeIndex::I32]);
		}
	}

	#[test]
	fn bound_reservations_survive_invalid_occurrences_and_signature_demands() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Leaf { type Value; }
			trait Outer { type Item; }
			func f<T: i32 + Outer where { Missing: Leaf, Item: i32 + Leaf where { Value = Later<U> }, Item: Leaf }, U: Outer>(x: T::Item::Value) {}
			struct Later<X: Outer>();
		"}
		);
		assert_eq!(
			case.context.diagnostics.len(),
			4,
			"{:?}",
			case.context.diagnostics
		);
		for (code, count) in [
			(DiagnosticCode::NotATraitBound, 2),
			(DiagnosticCode::NotATraitMember, 1),
			(DiagnosticCode::DuplicateAssocTypeBinding, 1),
		] {
			assert_eq!(
				case.context
					.diagnostics
					.iter()
					.filter(|d| d.code.as_deref() == Some(code.code()))
					.count(),
				count
			);
		}
		// Stored as `T::Item::Value`; the valid nested facts it reads still
		// mean `Later<U>`.
		let scope = case.function_signature("f").type_params;
		let ty = case.normalized_param("f", 0);
		let Type::Struct {
			struct_index,
			type_args,
		} = case.context.types.resolve(ty)
		else {
			panic!("valid nested facts must remain usable");
		};
		assert_eq!(*struct_index, case.struct_index("Later"));
		assert!(
			matches!(case.context.types.resolve(case.context.types.list(*type_args)[0]), Type::TypeParam { env, param_index: 1 } if *env == scope)
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Marker {}
			impl Marker for i32 {}
			trait Value { type Item; }
			struct Need<X: Marker>();

			func f<U: Value where { Item = i32 }>(x: Need<U::Item>) {}
		"}
		);
		assert_eq!(
			*case.context.diagnostics,
			Vec::new(),
			"{:?}",
			case.context.diagnostics
		);
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Value { type Item; }
			trait Result { type Out; }
			struct Wrap<T>();
			impl Result for Wrap<i32> { type Out = i32; }

			func f<S: Value where { Item = i32 }>(x: <Wrap<S::Item> as Result>::Out) {}
		"}
		);
		assert_eq!(
			*case.context.diagnostics,
			Vec::new(),
			"{:?}",
			case.context.diagnostics
		);
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
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			type u64;
			trait A { type Item; }
			trait Value { type Item; }

			func f<V: Value, T: A where { Item = u32 } + A where { Item = V::Item } + A where { Item = u64 }>() {}
		"}
		);
		assert!(
			case.context.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::DuplicateAssocTypeBinding.code())),
			"expected u32/u64 to still be flagged as conflicting even with a symbolic term between them: {:?}",
			case.context.diagnostics
		);
	}

	#[test]
	fn conflicting_equality_is_diagnosed_with_symbolic_term_last() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			type u64;
			trait A { type Item; }
			trait Value { type Item; }

			func f<V: Value, T: A where { Item = u32 } + A where { Item = u64 } + A where { Item = V::Item }>() {}
		"}
		);
		assert!(
			case.context.diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::DuplicateAssocTypeBinding.code())),
			"{:?}",
			case.context.diagnostics
		);
	}

	mod sweep_complete {
		use super::*;
		use crate::tir::assumptions::{AssumptionKind, Readiness};
		use crate::tir::bounds::ImpliedBindingKind;

		fn assert_graph_clean(graph: &vfs::CompilationUnit) {
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
		}

		macro_rules! checked_case {
			($case:ident = $source:expr $(,)?) => {
				test_case!($case = $source);
				assert_graph_clean($case.graph);
			};
			(mut $case:ident = $source:expr $(,)?) => {
				test_case!(mut $case = $source);
				assert_graph_clean($case.graph);
			};
		}

		#[test]
		fn swept_context_preserves_evidence_for_a_normalized_parameter() {
			checked_case!(mut case = indoc! {"
                trait Marker {}
                trait Container { type Item; }
                func f<T: Container where { Item = U } + Container where { Item: Marker }, U>(x: T::Item) {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "});
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let signature = case.function_signature("f");
			let assumption_context = signature.type_params;
			let written = signature.param_types[0];
			let params = case.context.type_envs.params(assumption_context);
			let (t, u) = (params[0].ty, params[1].ty);
			// The parameter is stored as `T::Item` and means `U`; the evidence
			// about `T::Item` is kept as written.
			assert!(matches!(
				case.context.types.resolve(written),
				Type::AssocTypeProjection { .. }
			));
			assert_eq!(case.normalized(assumption_context, written), u);
			let stored = u;
			let projection =
				case.context.types.intern(Type::AssocTypeProjection {
					base: t,
					trait_index: TraitIdx::new(1),
					assoc_type_index: AssocTypeIdx::new(0),
				});
			let (reader, types) = case.context.assumptions();
			let mut facts = reader.scoped_facts(assumption_context, types);
			assert_eq!(facts.readiness, Readiness::Ready);
			let mut memberships = Vec::new();
			let mut equality = None;
			while let Some(fact) = facts.next(types) {
				match fact.kind {
					AssumptionKind::Trait { trait_index, .. } => {
						memberships.push((fact.subject, trait_index))
					}
					AssumptionKind::Equality(ImpliedBindingKind::Equals(
						value,
					)) => {
						assert_eq!(fact.subject, projection);
						assert_eq!(value.value, stored);
						assert!(fact.self_substitution.is_none());
						equality = Some(value.source);
					}
					_ => {}
				}
			}
			assert!(memberships.contains(&(projection, TraitIdx::new(0))));
			let BindingRequirement::Equals(source) =
				case.context.bounds.binding(equality.unwrap()).kind
			else {
				panic!()
			};
			assert_eq!(source.inner, stored);
		}

		#[test]
		fn successful_deferred_checks_keep_symbolic_source_evidence() {
			checked_case!(mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                struct Need<X: Marker>();
                impl Marker for i32 {}
                func f<T: Container where { Item = Need<U::Item> }, U: Container where { Item = i32 }>(x: T::Item) {}
            "});
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let signature = case.function_signature("f");
			let assumption_context = signature.type_params;
			let written = signature.param_types[0];
			// `T::Item` means `Need<i32>`...
			let stored = case.normalized(assumption_context, written);
			let Type::Struct { type_args, .. } =
				case.context.types.resolve(stored)
			else {
				panic!()
			};
			assert_eq!(case.context.types.list(*type_args), &[TypeIndex::I32]);
			// ...while the stored source fact keeps `U::Item` symbolic.
			let ImpliedBindingKind::Equals(value) = case.context.param_bounds
				[usize::from(assumption_context)][0]
				.facts
				.current()[0]
				.bindings[0]
				.kind
			else {
				panic!()
			};
			let raw = value.value;
			let source = value.source;
			let Type::Struct { type_args, .. } =
				case.context.types.resolve(raw)
			else {
				panic!()
			};
			assert!(matches!(
				case.context
					.types
					.resolve(case.context.types.list(*type_args)[0]),
				Type::AssocTypeProjection { .. }
			));
			let BindingRequirement::Equals(value) =
				case.context.bounds.binding(source).kind
			else {
				panic!()
			};
			assert_eq!(value.inner, raw);
			let (reader, types) = case.context.assumptions();
			let mut facts = reader.scoped_facts(assumption_context, types);
			assert_eq!(facts.readiness, Readiness::Ready);
			let mut retained = false;
			while let Some(fact) = facts.next(types) {
				if let AssumptionKind::Equality(ImpliedBindingKind::Equals(
					value,
				)) = fact.kind
				{
					retained |= value.source == source && value.value == raw;
				}
			}
			assert!(retained);
		}

		fn memberships(
			registry: &mut TypeContext<'_, '_, '_>,
			assumption_context: TypeEnvIdx,
		) -> Vec<(TypeIndex, TraitIdx)> {
			let (reader, types) = registry.assumptions();
			let mut facts = reader.scoped_facts(assumption_context, types);
			assert_eq!(facts.readiness, Readiness::Ready);
			let mut result = Vec::new();
			while let Some(fact) = facts.next(types) {
				if let AssumptionKind::Trait { trait_index, .. } = fact.kind {
					result.push((fact.subject, trait_index));
				}
			}
			result
		}

		#[test]
		fn method_context_keeps_local_evidence_about_an_outer_parameter() {
			checked_case!(mut case = indoc! {"
                trait Outer {}
                trait Marker {}
                trait Container { type Item; }
                struct Host<T>();
                impl<T: Outer> Host<T> {
                    func scoped<U: Container where { Item = T } + Container where { Item: Marker }>(self, x: U::Item) {}
                    func plain(self, x: T) {}
                }
                func free() {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "});
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let function = |name| {
				case.defs
					.functions
					.iter()
					.position(|def| {
						case.graph.strings.resolve(def.name.inner) == Some(name)
					})
					.unwrap()
			};
			let scoped = function("scoped");
			let plain = function("plain");
			let free = function("free");
			let outer_env =
				case.context.inherent_impls[0].as_ref().unwrap().type_params;
			let outer = case.context.type_envs.params(outer_env)[0].ty;
			let assumption_context = case.context.functions[scoped].type_params;
			assert_ne!(
				assumption_context, outer_env,
				"the normalized parameter's owner is not the body's context"
			);
			// `U::Item` is stored as written and means the outer parameter `T`.
			let written = case.context.functions[scoped].param_types[1];
			assert_eq!(case.normalized(assumption_context, written), outer);
			let plain_cx = case.context.functions[plain].type_params;
			assert_eq!(
				plain_cx,
				case.context.inherent_impls[0].as_ref().unwrap().type_params
			);
			let free_cx = case.context.functions[free].type_params;
			assert_eq!(free_cx, TypeEnvIdx::ROOT);
			let local = memberships(&mut case.context, assumption_context);
			assert!(local.contains(&(outer, TraitIdx::new(0))));
			assert!(local.iter().any(|&(_, index)| index == TraitIdx::new(1)));
			assert_eq!(
				memberships(&mut case.context, plain_cx),
				vec![(outer, TraitIdx::new(0))]
			);
			assert!(memberships(&mut case.context, free_cx).is_empty());
		}

		#[test]
		fn trait_body_context_and_instantiated_declaration_bounds_survive_the_sweep()
		 {
			use crate::tir::types::Substitution;
			checked_case!(mut case = indoc! {"
                trait Project { type Output; }
                trait Parent {}
                trait Child: Parent {
                    type Item: Project where { Output = Self };
                    func provided(self, x: Self::Item) {}
                }
                func user<T: Child>(x: T::Item) {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "});
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let index = case
				.defs
				.functions
				.iter()
				.position(|def| {
					case.graph.strings.resolve(def.name.inner)
						== Some("provided")
				})
				.unwrap();
			let assumption_context = case.context.functions[index].type_params;
			let self_env = case.context.traits[2].env;
			let trait_self = case.context.type_envs.params(self_env)[0].ty;
			assert_eq!(assumption_context, self_env);
			assert_eq!(
				case.context.functions[index].param_types[0],
				trait_self
			);
			let facts = memberships(&mut case.context, assumption_context);
			assert!(facts.contains(&(trait_self, TraitIdx::new(2))));
			assert!(facts.contains(&(trait_self, TraitIdx::new(1))));
			let signature = case.function_signature("user");
			let subject = signature.param_types[0];
			let receiver =
				case.context.type_envs.params(signature.type_params)[0].ty;
			let (reader, types) = case.context.assumptions();
			let mut facts = reader.subject_facts(subject, types, 128);
			assert_eq!(facts.readiness, Readiness::Ready);
			let mut equalities = 0;
			while let Some(fact) = facts.next(types) {
				if let AssumptionKind::Equality(ImpliedBindingKind::Equals(
					value,
				)) = fact.kind
				{
					let substitution = fact.self_substitution.unwrap();
					assert_eq!(substitution.receiver, receiver);
					let rhs = types.substitute(
						value.value,
						Substitution {
							env: substitution.env,
							args: &[substitution.receiver],
						},
					);
					assert_eq!(rhs, receiver);
					equalities += 1;
				}
			}
			assert_eq!(equalities, 1);
		}

		#[test]
		fn satisfaction_overflow_is_diagnosed_when_no_trait_subject_matches() {
			let nested = format!(
				"{}Next = U{}",
				"Next: Node where { ".repeat(16),
				" }".repeat(16)
			);
			let source = format!(
				"trait Node {{ type Next: Node; }} trait Marker {{}} func f<T: Node where {{ {nested} }}, U>() {{}} pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}"
			);
			with_pending_signatures(&source, |builder| {
				builder.sweep();
				let env = builder.functions[0].type_params;
				let ty = builder.type_envs.params(env)[1].ty;
				builder.solver.set_limit_for_test(8);
				// Overflow is returned as such, never folded into "not a member" or
				// an error type; the site that asked owns the report.
				assert_eq!(
					builder
						.find_trait_impl_query(env, ty, TraitIdx::new(1))
						.map(|found| found.is_some()),
					Err(SolverError::Overflow)
				);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
				builder.solver.set_limit_for_test(128);
				assert_eq!(
					builder
						.find_trait_impl_query(env, ty, TraitIdx::new(1))
						.map(|found| found.is_some()),
					Ok(false)
				);
				assert!(builder.diagnostics.is_empty());
			});
		}
	}

	mod contextual_members {
		use super::*;
		use crate::tir::members::{
			ApplicableMember, MemberLookup, TraitImplLookup,
			TraitMemberSelection,
		};

		fn assert_graph_clean(graph: &vfs::CompilationUnit) {
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
		}

		macro_rules! checked_case {
			($case:ident = $source:expr $(,)?) => {
				test_case!($case = $source);
				assert_graph_clean($case.graph);
			};
			(mut $case:ident = $source:expr $(,)?) => {
				test_case!(mut $case = $source);
				assert_graph_clean($case.graph);
			};
		}

		#[test]
		fn equivalent_subjects_support_unqualified_and_qualified_members() {
			checked_case!(
				case = indoc! {"
                trait Project { type Output; }
                trait Container { type Item; }
                func f<T: Container where { Item = U } + Container where { Item: Project }, U>(x: U::Output, y: <U as Project>::Output) {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let signature = case.function_signature("f");
			assert_eq!(signature.param_types[0], signature.param_types[1]);
			let Type::AssocTypeProjection {
				trait_index,
				assoc_type_index,
				base,
			} = case.context.types.resolve(signature.param_types[0])
			else {
				panic!("ordinary projection expected")
			};
			assert_eq!(*trait_index, TraitIdx::new(0));
			assert_eq!(*assoc_type_index, AssocTypeIdx::new(0));
			assert_eq!(
				*base,
				case.context.type_envs.params(signature.type_params)[1].ty
			);
		}

		#[test]
		fn associated_declaration_bounds_supply_members_through_equality() {
			checked_case!(
				case = indoc! {"
                trait Project { type Output; }
                trait Container { type Item: Project; }
                func f<T: Container where { Item = U }, U>(x: U::Output) {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			assert!(
				matches!(case.context.types.resolve(case.function_signature("f").param_types[0]), Type::AssocTypeProjection { trait_index, .. } if *trait_index == TraitIdx::new(0))
			);
		}

		#[test]
		fn equivalent_traits_are_deduplicated_but_distinct_traits_are_ambiguous()
		 {
			checked_case!(
				valid = indoc! {"
                trait Project { type Output; }
                trait Container { type Item: Project; }
                func f<T: Container where { Item = U } + Container where { Item: Project }, U>(x: U::Output) {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "}
			);
			assert!(
				valid.context.diagnostics.is_empty(),
				"{:?}",
				valid.context.diagnostics
			);
			checked_case!(
				ambiguous = indoc! {"
                trait Left { type Output; }
                trait Right { type Output; }
                trait Container { type Item; }
                func f<T: Container where { Item = U } + Container where { Item: Left + Right }, U>(x: U::Output) {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "}
			);
			assert_eq!(
				ambiguous.context.diagnostics.len(),
				1,
				"{:?}",
				ambiguous.context.diagnostics
			);
			assert_eq!(
				ambiguous.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::AmbiguousTraitMember.code())
			);
			assert_eq!(ambiguous.context.diagnostics[0].notes.len(), 2);
		}

		#[test]
		fn contextual_member_evidence_does_not_escape_to_a_sibling() {
			checked_case!(
				case = indoc! {"
                trait Project { type Output; }
                trait Container { type Item; }
                struct Host<T>();
                impl<T> Host<T> {
                    func scoped<U: Container where { Item = T } + Container where { Item: Project }>(x: T::Output) {}
                    func sibling(x: T::Output) {}
                }
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::NotATraitMember.code())
			);
			let signature = |name| {
				let name = case.graph.strings.get(name).unwrap();
				let index = case
					.defs
					.functions
					.iter()
					.position(|def| def.name.inner == name)
					.unwrap();
				&case.context.functions[index]
			};
			assert_ne!(signature("scoped").param_types[0], TypeIndex::ERROR);
			assert_eq!(signature("sibling").param_types[0], TypeIndex::ERROR);
		}

		#[test]
		fn qualified_bindings_can_depend_on_a_later_binding_of_the_same_parameter()
		 {
			checked_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type A; type B; }
                trait Project { type Output; }
                struct Need<X: Marker>();
                impl Marker for i32 {}
                impl Project for Need<i32> { type Output = i32; }
                func first<T: Container where { A = <Need< <T as Container>::B> as Project>::Output, B = i32 }>(x: T::A) {}
                func reversed<T: Container where { B = i32, A = <Need< <T as Container>::B> as Project>::Output }>(x: T::A) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			for name in ["first", "reversed"] {
				assert_eq!(case.normalized_param(name, 0), TypeIndex::I32);
			}
		}

		#[test]
		fn direct_member_identity_does_not_require_complete_binding_values() {
			checked_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type A; type B; }
                trait Project { type Output; }
                struct Need<X: Marker>();
                impl Marker for i32 {}
                impl Project for Need<i32> { type Output = i32; }
                func f<T: Container where { A = <Need<T::B> as Project>::Output, B = i32 }>(x: T::A) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		}

		#[test]
		fn pending_unqualified_selection_explains_how_to_qualify() {
			checked_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type A; type B; }
                trait Project { type Output; }
                struct Need<X: Marker>();
                impl Marker for i32 {}
                impl Project for Need<i32> { type Output = i32; }
                func first<T: Container where { A = Need<T::B>::Output, B = i32 }>(x: T::A) {}
                func reversed<T: Container where { B = i32, A = Need<T::B>::Output }>(x: T::A) {}
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				2,
				"{:?}",
				case.context.diagnostics
			);
			for diagnostic in &*case.context.diagnostics {
				assert_eq!(
					diagnostic.code.as_deref(),
					Some(DiagnosticCode::TypeMemberNeedsQualification.code())
				);
				assert!(diagnostic.notes[0].contains(" as Trait>::Output"));
				assert_eq!(diagnostic.labels.len(), 1);
			}
			for name in ["first", "reversed"] {
				assert_eq!(case.normalized_param(name, 0), TypeIndex::ERROR);
			}
		}

		#[test]
		fn pending_member_discovery_is_not_reported_as_a_missing_member() {
			checked_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Container { type A; type Item; }
                trait Project { type Output; }
                func f<T: Container where { A = U::Output, Item = U } + Container where { Item: Project }, U>(x: T::A) {}
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TypeMemberNeedsQualification.code())
			);
		}

		#[test]
		fn unqualified_selection_works_after_binding_facts_are_ready() {
			checked_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                trait Project { type Output; }
                struct Need<X: Marker>();
                impl Marker for i32 {}
                impl Project for Need<i32> { type Output = i32; }
                func f<T: Container where { Item = i32 }>(x: Need<T::Item>::Output) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		}

		#[test]
		fn sibling_dependent_unqualified_lookup_reports_the_same_limitation() {
			checked_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                trait Project { type Output; }
                struct Need<X: Marker>();
                impl Marker for i32 {}
                impl Project for Need<i32> { type Output = i32; }
                func f<T: Container where { Item = Need<U::Item>::Output }, U: Container where { Item = i32 }>(x: T::Item) {}
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TypeMemberNeedsQualification.code())
			);
			assert_eq!(case.normalized_param("f", 0), TypeIndex::ERROR);
		}

		#[test]
		fn a_failed_qualified_dependent_binding_reports_one_bound_error() {
			checked_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Container { type A; type B; }
                trait Project { type Output; }
                struct Need<X>();
                impl Project for Need<i32> { type Output = i32; }
                func f<T: Container where { A = <Need<T::B> as Project>::Output, B = () }>(x: T::A, y: i32) {}
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TraitBoundViolation.code())
			);
			// `T::A` is `<Need<T::B> as Project>::Output` with `T::B = ()`, and
			// `Need<()>` has no `Project` impl: the requirement is reported once,
			// at the qualified path; the type is kept and has no value.
			assert!(case.is_projection_param("f", 0));
			assert_eq!(
				case.try_normalized_param("f", 0),
				Err(SolverError::Poisoned)
			);
			assert_eq!(
				case.function_signature("f").param_types[1],
				TypeIndex::I32
			);
		}

		#[test]
		fn member_lookup_prefers_a_real_provider_for_a_concrete_equal_subject()
		{
			with_pending_signatures(
				indoc! {"
                type i32;
                trait Project { type Output; }
                trait Container { type Item; }
                impl Project for i32 { type Output = (); }
                func f<T: Container where { Item = i32 } + Container where { Item: Project }>() {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "},
				|builder| {
					builder.sweep();
					let assumption_context = builder.functions[0].type_params;
					let reference = SourceSpan::new(
						builder.defs.functions[0].file_id,
						TextSpan::new(0, 1),
					);
					let proof = builder
						.find_trait_impl_query(
							assumption_context,
							TypeIndex::I32,
							TraitIdx::new(0),
						)
						.unwrap()
						.unwrap();
					assert!(
						matches!(proof, TraitImplLookup::Concrete { impl_index, .. } if impl_index == TraitImplIdx::new(0))
					);
					let key =
						BindingKey::ty(builder.strings.get("Output").unwrap());
					let MemberLookup::Found(member) = builder
						.resolve_applicable_member(
							assumption_context,
							TypeIndex::I32,
							key,
							reference,
						)
					else {
						panic!("provider member expected")
					};
					let member = member.assoc_type_declaration().unwrap();
					assert_eq!(member.trait_index, TraitIdx::new(0));
					assert_eq!(member.assoc_type_index, AssocTypeIdx::new(0));
					let ty = builder.project_assoc_type(TypeIndex::I32, member);
					assert_eq!(
						builder.normalize_type_query(assumption_context, ty),
						Ok(TypeIndex::UNIT)
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
		fn concrete_equal_subjects_can_use_a_symbolic_assumed_member() {
			checked_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Project { type Output; }
                trait Container { type Item; }
                func f<T: Container where { Item = i32 } + Container where { Item: Project }>(x: i32::Output, y: <i32 as Project>::Output) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			let signature = case.function_signature("f");
			assert_eq!(signature.param_types[0], signature.param_types[1]);
			assert!(
				matches!(case.context.types.resolve(signature.param_types[0]), Type::AssocTypeProjection { base, .. } if *base == TypeIndex::I32)
			);
		}

		#[test]
		fn member_discovery_respects_the_shared_projection_budget() {
			let nested = format!(
				"{}Next = U{}",
				"Next: Node where { ".repeat(16),
				" }".repeat(16)
			);
			let source = format!(
				"pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}} trait Node {{ type Next: Node; }} trait Project {{ type Output; }} func f<T: Node where {{ {nested} }}, U>() {{}}"
			);
			with_pending_signatures(&source, |builder| {
				let id = DefId::Function(FunctionIdx::new(0));
				let _ = builder.ensure_signature(QueryInfo {
					def_id: id,
					requested_at: None,
				});
				let env = builder.functions[0].type_params;
				let ty = builder.type_envs.params(env)[1].ty;
				let reference = SourceSpan::new(
					builder.defs.functions[0].file_id,
					TextSpan::new(0, 1),
				);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
				builder.solver.set_limit_for_test(8);
				assert!(matches!(
					builder.resolve_applicable_member(
						env,
						ty,
						BindingKey::ty(builder.strings.get("Output").unwrap()),
						reference
					),
					MemberLookup::Stuck(
						crate::tir::solver::SolverError::Overflow
					)
				));
				// A query reports nothing; the site that asked owns the report.
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
				builder.solver.set_limit_for_test(128);
				assert!(matches!(
					builder.resolve_applicable_member(
						env,
						ty,
						BindingKey::ty(builder.strings.get("Output").unwrap()),
						reference
					),
					MemberLookup::NotFound
				));
				assert!(builder.diagnostics.is_empty());
			});
		}

		#[test]
		fn unrelated_inherent_requirements_do_not_hide_a_trait_member() {
			with_pending_signatures(
				indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Project { func selected() {} }
                struct Wrap<X>();
                impl<X: Marker> Wrap<X> { func unrelated() {} }
                impl<X> Project for Wrap<X> {}
                func f<U>(x: Wrap<U>) {}
            "},
				|builder| {
					let index = builder
						.defs
						.functions
						.iter()
						.position(|def| {
							builder.strings.resolve(def.name.inner) == Some("f")
						})
						.unwrap();
					builder.sweep();
					let signature = &builder.functions[index];
					let assumption_context = signature.type_params;
					let receiver = signature.param_types[0];
					let reference = SourceSpan::new(
						builder.defs.functions[index].file_id,
						TextSpan::new(0, 1),
					);
					let key = BindingKey::value(
						builder.strings.get("selected").unwrap(),
					);
					let MemberLookup::Found(member) = builder
						.resolve_applicable_member(
							assumption_context,
							receiver,
							key,
							reference,
						)
					else {
						panic!("trait member expected")
					};
					let ApplicableMember::TraitImplMember {
						impl_index,
						declaration,
						..
					} = member
					else {
						panic!("expected a concrete trait member")
					};
					let selection = builder
						.defs
						.select_trait_member(impl_index, declaration);
					assert!(matches!(
						selection,
						TraitMemberSelection::TraitDeclaration(_)
					));
					assert!(
						builder.diagnostics.is_empty(),
						"{:?}",
						builder.diagnostics
					);
				},
			);
		}
	}

	mod equality_satisfaction {
		use super::*;

		#[test]
		fn a_projection_reduced_to_a_bounded_parameter_satisfies_requirements()
		{
			test_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Container { type Item; }
                struct Need<T: Marker>();
                func f<T: Container where { Item = U }, U: Marker>(x: Need<T::Item>) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			// Stored as `Need<T::Item>`; `T::Item = U` and `U: Marker`, so it
			// means `Need<U>` and the bound holds.
			let scope = case.function_signature("f").type_params;
			let ty = case.normalized_param("f", 0);
			let Type::Struct { type_args, .. } = case.context.types.resolve(ty)
			else {
				panic!()
			};
			assert_eq!(
				case.context.types.list(*type_args),
				&[case.context.type_envs.params(scope)[1].ty]
			);
		}

		#[test]
		fn an_equal_subject_keeps_projection_evidence_after_normalization() {
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Container { type Item; }
                struct Need<T: Marker>();
                func f<T: Container where { Item = U } + Container where { Item: Marker }, U>(x: Need<U>) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
		}

		#[test]
		fn generic_impl_requirements_use_evidence_for_the_callers_equal_subject()
		 {
			test_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                trait Result { type Output; }
                struct Wrap<T>();
                impl<X: Marker> Result for Wrap<X> { type Output = i32; }
                func f<T: Container where { Item = U } + Container where { Item: Marker }, U>(x: <Wrap<T::Item> as Result>::Output) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		}

		#[test]
		fn a_stored_projection_is_checked_in_its_own_context() {
			with_pending_signatures(
				"trait Marker {} trait Container { type Item; } func f<T: Container where { Item = U } + Container where { Item: Marker }, U>(x: T::Item) {} pub trait Call { type Args; type Result; } pub trait Function: Call {}",
				|builder| {
					builder.sweep();
					let signature = &builder.functions[0];
					let env = signature.type_params;
					let written = signature.param_types[0];
					let u = builder.type_envs.params(env)[1].ty;
					// The parameter is stored as written, `T::Item`, and under its
					// own context means `U`...
					assert!(matches!(
						builder.types.resolve(written),
						Type::AssocTypeProjection { .. }
					));
					assert_eq!(
						builder.normalize_type_query(env, written),
						Ok(u)
					);
					// ...and either spelling satisfies `Marker` there.
					for ty in [written, u] {
						assert_eq!(
							builder
								.find_trait_impl_query(
									env,
									ty,
									TraitIdx::new(0)
								)
								.map(|found| found.is_some()),
							Ok(true)
						);
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
		fn associated_declaration_bounds_follow_a_written_equality() {
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Container { type Item: Marker; }
                struct Need<X: Marker>();
                func f<T: Container where { Item = U }, U>(x: Need<U>) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
		}

		#[test]
		fn local_evidence_about_an_outer_parameter_does_not_escape() {
			// Alone, `scoped` is fine: its own `Item = T` and `Item: Marker` make
			// `T: Marker` there.
			test_case!(
				case = indoc! {"
                trait Marker {}
                trait Container { type Item; }
                struct Need<X: Marker>();
                struct Host<T>();
                impl<T> Host<T> {
                    func scoped<U: Container where { Item = T } + Container where { Item: Marker }>(x: Need<T>) {}
                }
            "}
			);
			case.diagnostics().assert_none();
			// Next to a sibling that has no such evidence, the same source reports
			// exactly the sibling: the local evidence does not escape `scoped`.
			test_case!(
				case = indoc! {"
                trait Marker {}
                trait Container { type Item; }
                struct Need<X: Marker>();
                struct Host<T>();
                impl<T> Host<T> {
                    func scoped<U: Container where { Item = T } + Container where { Item: Marker }>(x: Need<T>) {}
                    func sibling(x: Need<T>) {}
                }
            "}
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
			let sibling = case.graph.strings.get("sibling").unwrap();
			let index = case
				.defs
				.functions
				.iter()
				.position(|definition| definition.name.inner == sibling)
				.unwrap();
			let diagnostic = &case.context.diagnostics[0];
			let label = &diagnostic.labels[0];
			let sibling_span = case.defs.functions[index].name.span;
			assert!(
				label.range.start >= sibling_span.start as usize,
				"the violation belongs to `sibling`: {diagnostic:?}"
			);
		}
		#[test]
		fn an_impl_requirement_cannot_supply_its_own_proof() {
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                struct Need<X: Marker>();
                struct Wrap<X>();
                impl<X: Marker> Marker for Wrap<X> {}
                func f<U>(x: Need<Wrap<U>>) {}
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TraitBoundViolation.code())
			);
		}

		#[test]
		fn ambiguous_equalities_do_not_transfer_membership() {
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Container { type Item; }
                struct Need<X: Marker>();
                func f<T: Container where { Item = U } + Container where { Item = V } + Container where { Item: Marker }, U, V>(x: Need<U>, y: Need<V>) {}
            "}
			);
			assert_eq!(
				case.context
					.diagnostics
					.iter()
					.filter(|d| d.code.as_deref()
						== Some(DiagnosticCode::TraitBoundViolation.code()))
					.count(),
				2,
				"{:?}",
				case.context.diagnostics
			);
		}

		#[test]
		fn an_assumed_cycle_does_not_invent_a_trait_or_recurse_through_dispatch()
		 {
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Container { type Item; }
                struct Need<X: Marker>();
                func f<T: Container where { Item = U::Item }, U: Container where { Item = T::Item }, V: Marker>(x: Need<T::Item>) {}
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TraitBoundViolation.code())
			);
		}

		#[test]
		fn equality_proofs_wait_for_facts_and_do_not_cache_a_pending_answer() {
			with_pending_signatures(
				"trait Marker {} trait Container { type Item; } func f<T: Container where { Item = U } + Container where { Item: Marker }, U>(x: T::Item) {} pub trait Call { type Args; type Result; } pub trait Function: Call {}",
				|builder| {
					let id = DefId::Function(FunctionIdx::new(0));
					let _ = builder.ensure_signature(QueryInfo {
						def_id: id,
						requested_at: None,
					});
					let env = builder.functions[0].type_params;
					// `U` is only provably a `Marker` through `T::Item = U`, an
					// equality fact: the proof must wait for the facts to be final.
					let ty = builder.type_envs.params(env)[1].ty;
					let facts = builder.param_bounds[usize::from(env)][0]
						.facts
						.current()
						.to_vec()
						.into_boxed_slice();
					builder.param_bounds[usize::from(env)][0].facts =
						BoundFacts::Provisional(facts.clone());
					assert_eq!(
						builder
							.find_trait_impl_query(env, ty, TraitIdx::new(0))
							.map(|found| found.is_some()),
						Err(SolverError::Pending)
					);
					builder.param_bounds[usize::from(env)][0].facts =
						BoundFacts::Ready(facts);
					assert_eq!(
						builder
							.find_trait_impl_query(env, ty, TraitIdx::new(0))
							.map(|found| found.is_some()),
						Ok(true)
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
		fn equality_comparison_uses_the_existing_budget_and_recovers_after_overflow()
		 {
			let nested = format!("{}U{}", "Wrap<".repeat(16), ">".repeat(16));
			let source = format!(
				"trait Marker {{}} trait Container {{ type Item; }} struct Wrap<X>(); func f<T: Container where {{ Item = {nested} }} + Container where {{ Item: Marker }}, U>() {{}} pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}"
			);
			with_pending_signatures(&source, |builder| {
				builder.sweep();
				let env = builder.functions[0].type_params;
				let ty = builder.type_envs.params(env)[1].ty;
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
				builder.solver.set_limit_for_test(8);
				// The budget is shared with the comparison. Running out is returned,
				// not reported: the site that asked owns the report.
				assert_eq!(
					builder
						.find_trait_impl_query(env, ty, TraitIdx::new(0))
						.map(|found| found.is_some()),
					Err(SolverError::Overflow)
				);
				assert!(
					builder.diagnostics.is_empty(),
					"{:?}",
					builder.diagnostics
				);
				builder.solver.set_limit_for_test(128);
				assert_eq!(
					builder
						.find_trait_impl_query(env, ty, TraitIdx::new(0))
						.map(|found| found.is_some()),
					Ok(false)
				);
				assert!(builder.diagnostics.is_empty());
			});
		}
	}

	mod deferred_checks {
		use super::*;

		#[test]
		fn bounded_equality_rhs_waits_for_all_sibling_facts() {
			test_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                struct Need<T: Marker>();
                impl Marker for i32 {}
                func first<T: Container where { Item = Need<U::Item> }, U: Container where { Item = i32 }>(x: T::Item) {}
                func reversed<U: Container where { Item = i32 }, T: Container where { Item = Need<U::Item> }>(x: T::Item) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			for name in ["first", "reversed"] {
				let ty = case.normalized_param(name, 0);
				let Type::Struct { type_args, .. } =
					case.context.types.resolve(ty)
				else {
					panic!("Need application expected");
				};
				assert_eq!(
					case.context.types.list(*type_args),
					&[TypeIndex::I32]
				);
			}
		}

		#[test]
		fn a_failed_check_keeps_the_written_argument_and_unrelated_types() {
			test_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                struct Need<T: Marker>();
                func bad<T: Container where { Item = Need<U::Item> }, U: Container where { Item = i32 }>(x: T::Item, y: i32) -> i32 {}
            "}
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
			let signature = case.function_signature("bad");
			assert_eq!(signature.param_types[1], TypeIndex::I32);
			assert_eq!(signature.return_type, TypeIndex::I32);
			// `x` is written as `T::Item`, which means `Need<i32>`.
			assert!(case.is_projection_param("bad", 0));
			let x = case.normalized_param("bad", 0);
			let Type::Struct { type_args, .. } = case.context.types.resolve(x)
			else {
				panic!("Need identity must survive the failed check");
			};
			assert_eq!(case.context.types.list(*type_args), &[TypeIndex::I32]);
			// The stored fact `Item = Need<U::Item>` is exactly as written; the
			// failed check does not rewrite it.
			let signature = case.function_signature("bad");
			let binding = &case.context.param_bounds
				[usize::from(signature.type_params)][0]
				.facts
				.current()[0]
				.bindings[0];
			let super::super::super::bounds::ImpliedBindingKind::Equals(fact) =
				binding.kind
			else {
				panic!()
			};
			let Type::Struct { type_args, .. } =
				case.context.types.resolve(fact.value)
			else {
				panic!()
			};
			assert!(matches!(
				case.context
					.types
					.resolve(case.context.types.list(*type_args)[0]),
				Type::AssocTypeProjection { .. }
			));
		}
		#[test]
		fn a_failed_check_keeps_nested_tuple_and_function_shapes() {
			test_case!(mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                struct Need<T: Marker>();
                func bad<T: Container where { Item = Need<U::Item> }, U: Container where { Item = i32 }>(x: (T::Item, i32), y: func(i32) -> T::Item) -> func(T::Item) -> i32 {}
            "});
			// `Need<i32>` needs `i32: Marker`: reported once, where it is written.
			// Nothing is rewritten, so every shape that mentions `T::Item` still
			// means what it says.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
			let signature = case.function_signature("bad");
			let (scope, written) = (
				signature.type_params,
				[
					signature.param_types[0],
					signature.param_types[1],
					signature.return_type,
				],
			);
			let actual = written.map(|ty| case.normalized(scope, ty));
			let struct_index = case.struct_index("Need");
			let types = &mut case.context.types;
			let need = types.intern_struct(struct_index, &[TypeIndex::I32]);
			let expected = [
				types.intern_tuple(&[need, TypeIndex::I32]),
				types.intern(Type::FunctionRef {
					param: TypeIndex::I32,
					result: need,
				}),
				types.intern(Type::FunctionRef {
					param: need,
					result: TypeIndex::I32,
				}),
			];
			assert_eq!(actual, expected);
		}
		#[test]
		fn a_recursive_application_reads_its_eventual_parameter_requirements() {
			test_case!(
				case = indoc! {"
                type i32;
                trait Marker {}
                trait Container { type Item; }
                impl Marker for i32 {}
                impl Container for i32 { type Item = i32; }
                struct Node<T: Marker + Container where { Item = Node<i32> }>();
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
		}

		#[test]
		fn eventual_requirements_cannot_be_accepted_from_an_incomplete_list() {
			test_case!(
				case = indoc! {"
                type i32;
                trait Marker {}
                trait Container { type Item; }
                impl Container for i32 { type Item = i32; }
                struct Node<T: Marker + Container where { Item = Node<i32> }>();
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TraitBoundViolation.code())
			);
			assert!(case.context.diagnostics[0].message.contains("Marker"));
		}

		#[test]
		fn qualified_projection_defers_membership_without_losing_identity() {
			test_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                trait Project { type Output; }
                struct Need<T: Marker>();
                impl Marker for i32 {}
                impl Project for Need<i32> { type Output = i32; }
                func f<T: Container where { Item = <Need<U::Item> as Project>::Output }, U: Container where { Item = i32 }>(x: T::Item) {}
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		}

		#[test]
		fn reentrant_queries_complete_in_their_own_contexts() {
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                struct Need<T: Marker>();
                impl Marker for i32 {}
                func outer<A: Container where { Item = Inner<A, A> }>(x: A::Item) {}
                struct Inner<T: Container where { Item = Need<U::Item> }, U: Container where { Item = i32 }>();
            "}
			);
			assert!(
				case.context.diagnostics.is_empty(),
				"{:?}",
				case.context.diagnostics
			);
		}

		#[test]
		fn an_unsatisfied_qualified_projection_is_reported_once_at_its_source()
		{
			test_case!(
				mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32; type bool;
                trait Container { type Item; }
                trait Project { type Output; }
                struct Plain<T>();
                impl Project for Plain<bool> { type Output = bool; }
                func f<T: Container where { Item = <Plain<U::Item> as Project>::Output }, U: Container where { Item = i32 }>(x: T::Item) {}
            "}
			);
			assert_eq!(
				case.context.diagnostics.len(),
				1,
				"{:?}",
				case.context.diagnostics
			);
			assert_eq!(
				case.context.diagnostics[0].code.as_deref(),
				Some(DiagnosticCode::TraitBoundViolation.code())
			);
			// `Plain<i32>` has no `Project` impl: reported once at the qualified
			// path. The parameter is kept as written and has no value.
			assert!(case.is_projection_param("f", 0));
			assert_eq!(
				case.try_normalized_param("f", 0),
				Err(SolverError::Poisoned)
			);
		}
	}

	#[test]
	fn nested_exports_resolve_names_in_the_declaring_namespace() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            func f<T>() {}

            mod left {
                func f() {}

                export f as \"left\"
            }

            mod right {
                func f() {}

                export {
                    f,
                }
            }
        "}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.context.exports.len(), 2);
		for (external, path) in [("left", "left::f"), ("f", "right::f")] {
			let export = case.context.exports
				[&case.graph.strings.get(external).unwrap()];
			let DefKind::Function(index) = case.resolve(Tier::Value, path)
			else {
				panic!("expected a function");
			};
			assert_eq!(export, ExportedItem::Function(index));
		}
	}

	#[test]
	fn exports_reject_ineligible_targets() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type i32;
            const C: i32 = 1;
            struct S();
            func generic<T>() {}

            mod nested {
                func f() {}

                export {
                    f,
                }
            }

            export {
                C,
                S,
            }

            export generic
            export missing
        "}
		);
		assert_eq!(
			case.context
				.diagnostics
				.iter()
				.filter(|d| d.code.as_deref()
					== Some(DiagnosticCode::CannotExportItem.code()))
				.count(),
			// `C`, `S` (a struct's constructor) and `generic`.
			3
		);
		assert_eq!(
			case.context
				.diagnostics
				.iter()
				.filter(|d| d.code.as_deref()
					== Some(DiagnosticCode::UndeclaredIdentifier.code()))
				.count(),
			// `missing`.
			1
		);
		assert_eq!(
			case.context.diagnostics.len(),
			4,
			"{:?}",
			case.context.diagnostics
		);
		assert_eq!(case.context.exports.len(), 1);
		let DefKind::Function(index) = case.resolve(Tier::Value, "nested::f")
		else {
			panic!("expected a function");
		};
		assert_eq!(
			case.context.exports[&case.graph.strings.get("f").unwrap()],
			ExportedItem::Function(index)
		);
	}

	#[test]
	fn exports_resolve_import_aliases_and_synthetic_values() {
		test_case!(
			case = indoc! {"
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            type u32;

            typeset PointerSize {
                u32,
            }

            trait Memory {
                type Size: PointerSize;
            }

            trait Global {
                type Value;
            }

            mod inner {
                pub func f() {}
            }

            use inner::f as imported;
            memory heap: u32;
            global counter: u32 = 0;

            export imported as \"run\"

            export {
                heap,
                counter,
            }
        "}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.context.exports.len(), 3);
		let DefKind::Function(function) = case.resolve(Tier::Value, "inner::f")
		else {
			panic!("expected a function");
		};
		let DefKind::Memory(memory) = case.resolve(Tier::Value, "heap") else {
			panic!("expected a memory");
		};
		let DefKind::Global(global) = case.resolve(Tier::Value, "counter")
		else {
			panic!("expected a global");
		};
		assert_eq!(
			case.context.exports[&case.graph.strings.get("run").unwrap()],
			ExportedItem::Function(function)
		);
		assert_eq!(
			case.context.exports[&case.graph.strings.get("heap").unwrap()],
			ExportedItem::Memory(memory)
		);
		assert_eq!(
			case.context.exports[&case.graph.strings.get("counter").unwrap()],
			ExportedItem::Global(global)
		);
	}

	#[test]
	fn dependency_exports_are_ignored_and_package_kind_does_not_gate_exports() {
		let mut builder = vfs::CompilationUnitBuilder::new();
		let workspace = vfs::VirtualFileSource::from_relative(HashMap::from([
			(
				"dep.wx".to_string(),
				r#"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                pub func f() {}
                export { missing as "run", f as "run" }
                mod nested { export { missing } }
            "#
				.to_string(),
			),
			(
				"main.wx".to_string(),
				r#"
                use std::f;
                export { f as "run" }
            "#
				.to_string(),
			),
		]));
		let dep = builder
			.load_package(
				vfs::PackageKind::Library,
				vfs::AbsolutePath::new("/dep.wx"),
				&workspace,
			)
			.unwrap();
		builder.set_stdlib(dep);
		let root = builder
			.load_package(
				vfs::PackageKind::Library,
				vfs::AbsolutePath::new("/main.wx"),
				&workspace,
			)
			.unwrap();
		test_case!(case from builder.build(root));
		case.diagnostics().assert_none();
		assert_eq!(case.defs.exports.len(), 1);
		let export =
			&case.defs.exports[&case.graph.strings.get("run").unwrap()];
		assert_eq!(export.name.inner, case.graph.strings.get("f").unwrap());
		assert!(
			case.defs
				.namespaces
				.symbols(Namespace::Package(dep))
				.bindings
				.get(&BindingKey::value(case.graph.strings.get("run").unwrap()))
				.is_none()
		);
	}

	/// An import block's declarations are written in the scope around the
	/// block, so their types resolve there. Test sources usually play the
	/// stdlib's role, where the prelude would find `S` anyway; here the
	/// stdlib is a separate package, so only the enclosing scope can.
	#[test]
	fn an_imported_declaration_resolves_its_types_in_the_enclosing_scope() {
		let mut builder = vfs::CompilationUnitBuilder::new();
		let workspace = vfs::VirtualFileSource::from_relative(HashMap::from([
			(
				"std.wx".to_string(),
				"pub trait Call { type Args; type Result; } pub trait Function: Call {} pub type u32;"
					.to_string(),
			),
			(
				"main.wx".to_string(),
				r#"struct S(); import "env" { func f(s: S); }"#.to_string(),
			),
		]));
		let std = builder
			.load_package(
				vfs::PackageKind::Library,
				vfs::AbsolutePath::new("/std.wx"),
				&workspace,
			)
			.unwrap();
		builder.set_stdlib(std);
		let root = builder
			.load_package(
				vfs::PackageKind::Library,
				vfs::AbsolutePath::new("/main.wx"),
				&workspace,
			)
			.unwrap();
		test_case!(case from builder.build(root));
		case.diagnostics().assert_none();
	}

	#[test]
	fn export_names_resolve_only_in_the_value_namespace() {
		test_case!(
			case = r#"
            type i32;
            struct S();
            trait T {}
            type Alias = S;
            enum E: i32 { A = 0 }
            mod inner {}
            export { T, Alias, E, i32, inner }
        "#,
		);
		// `S` is not here: a struct's name is also its constructor, a value.
		assert_eq!(
			case.context.diagnostics.len(),
			5,
			"{:?}",
			case.context.diagnostics
		);
		for diagnostic in &*case.context.diagnostics {
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(DiagnosticCode::UndeclaredIdentifier.code())
			);
			assert!(
				diagnostic.message.contains("value"),
				"{}",
				diagnostic.message
			);
		}
	}

	#[test]
	fn functions_and_globals_are_their_own_types() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Global { type Value; }
			global counter: i32 = 0;
			func id<T>(x: T) -> T {}
			func takes(g: counter, f: id<i32>, me: takes) {}
			func bare(f: id) {}
			func applied(g: counter<i32>) {}
		"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentCountMismatch,
		]);
		let DefKind::Global(counter) = case.resolve(Tier::Value, "counter")
		else {
			panic!("expected `counter` to be a global");
		};
		let function = |path| {
			let DefKind::Function(index) = case.resolve(Tier::Value, path)
			else {
				panic!("expected `{path}` to be a function");
			};
			index
		};
		let (id, takes) = (function("id"), function("takes"));
		let params = &case.function_signature("takes").param_types;
		assert_eq!(
			case.context.types.resolve(params[0]),
			&Type::Global {
				global_index: counter
			}
		);
		let types = &case.context.types;
		assert!(matches!(
			*types.resolve(params[1]),
			Type::Function { func_index, type_args }
				if func_index == id && types.list(type_args) == [TypeIndex::I32]
		));
		assert!(matches!(
			*types.resolve(params[2]),
			Type::Function { func_index, type_args }
				if func_index == takes && type_args.is_empty()
		));
	}

	/// A free function's type implements `Call` through its synthetic impl:
	/// `Args` is its one parameter type (`()` for none, a tuple for several,
	/// as in `func(..)`), `Result` its return type.
	#[test]
	fn a_function_type_implements_call() {
		test_case!(
			mut case = indoc! {r#"
			type i32;
			type bool;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			func none() {}
			func one(x: i32) -> bool {}
			func many(x: i32, y: bool) {}
			import "env" as host { func log(x: bool) -> i32; }
			func nullary(x: <none as Call>::Args, y: none::Result) {}
			func unary(x: <one as Call>::Args, y: one::Result) {}
			func tuple(x: many::Args) {}
			func imported(x: host::log::Args, y: host::log::Result) {}
		"#}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("nullary", 0), TypeIndex::UNIT);
		assert_eq!(case.normalized_param("nullary", 1), TypeIndex::UNIT);
		assert_eq!(case.normalized_param("unary", 0), TypeIndex::I32);
		assert_eq!(case.normalized_param("unary", 1), TypeIndex::BOOL);
		let pair = case
			.context
			.types
			.intern_tuple(&[TypeIndex::I32, TypeIndex::BOOL]);
		assert_eq!(case.normalized_param("tuple", 0), pair);
		assert_eq!(case.normalized_param("imported", 0), TypeIndex::BOOL);
		assert_eq!(case.normalized_param("imported", 1), TypeIndex::I32);
	}

	/// The impl is generic over the function's own parameters, so a
	/// projection off `id<i32>` substitutes them.
	#[test]
	fn a_generic_function_types_projections_substitute_its_arguments() {
		test_case!(
			mut case = indoc! {"
			type i32;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			func id<T>(x: T) -> T {}
			func f(x: id<i32>::Args, y: <id<i32> as Call>::Result) {}
		"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::I32);
	}

	/// `Function` is an ordinary bound: a function type satisfies it, any
	/// other type does not, nor its supertrait `Call`.
	#[test]
	fn only_function_types_satisfy_a_function_bound() {
		test_case!(
			case = indoc! {"
			type i32;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			struct Callback<F: Function>();
			func handler(x: i32) {}
			func good(c: Callback<handler>) {}
			func bad(c: Callback<i32>) {}
		"}
		);
		// `i32: Function` and, separately, its supertrait `i32: Call`.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
		]);
	}

	/// A return type that names the function's own `Result` is a value
	/// defined through itself: one cycle, owned by the synthetic member.
	#[test]
	fn a_function_whose_result_is_its_own_result_is_one_cycle() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			func f() -> f::Result {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
	}

	/// The synthetic impl is the only one: a function is not a path an impl
	/// can be written for.
	#[test]
	fn an_impl_cannot_be_written_for_a_function() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Marker {}
			func f() {}
			impl Marker for f {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::InvalidImplTarget]);
	}

	/// `Call` is an ordinary trait a struct can implement, like an operator
	/// trait; `Function` is only ever the synthetic impl of a function item.
	/// Both satisfy a `Call` bound, only the function a `Function` bound.
	#[test]
	fn a_struct_can_implement_call_but_only_functions_are_function() {
		test_case!(
			mut case = indoc! {"
			type i32;
			pub trait Call {
				type Args;
				type Result;
				func call(self, args: Self::Args) -> Self::Result;
			}
			pub trait Function: Call {}
			struct Adder(value: i32);
			impl Call for Adder {
				type Args = i32;
				type Result = i32;
				func call(self, args: Self::Args) -> Self::Result {}
			}
			func handler(x: i32) -> i32 {}
			struct Callable<F: Call>();
			struct Item<F: Function>();
			func callables(a: Callable<Adder>, b: Callable<handler>, c: Adder::Result) {}
			func items(a: Item<handler>, b: Item<Adder>) {}
			func generic<F: Function>(x: F::Args, y: F::Result) {}
		"}
		);
		// `Adder: Call` holds, so only `Adder: Function` fails.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `Adder: Function` is not satisfied",
		);
		assert_eq!(case.normalized_param("callables", 2), TypeIndex::I32);
	}

	/// `Self` in an impl is not a parameter: it names the impl's target and
	/// resolves through the frame every impl owns, even a non-generic one.
	/// A trait's `Self` stays its parameter 0.
	#[test]
	fn impl_self_names_the_target_through_the_impls_own_frame() {
		const SOURCE: &str = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Service { func make() -> Self; }
			struct Wrap<T>();
			struct Plain();
			impl<T> Wrap<T> { func get(self) -> Self {} }
			impl Plain { func get(self) -> Self {} }
			impl Service for Plain { func make() -> Self {} }
		"};
		test_case!(case = SOURCE);
		case.diagnostics().assert_none();
		for (path, impl_index) in [
			("Wrap", case.inherent_impl_index("Wrap")),
			("Plain", case.inherent_impl_index("Plain")),
		] {
			let header = case.context.inherent_impls[usize::from(impl_index)]
				.as_ref()
				.unwrap();
			assert_ne!(header.type_params, TypeEnvIdx::ROOT, "{path}");
			let get = case.inherent_function_signature(path, "get");
			assert_eq!(get.return_type, header.target.inner, "{path}");
			assert_eq!(get.type_params, header.type_params, "{path}");
		}
		let plain = case.context.inherent_impls
			[usize::from(case.inherent_impl_index("Plain"))]
		.as_ref()
		.unwrap();
		assert!(case.context.type_envs.params(plain.type_params).is_empty());
		let make =
			case.trait_impl_function_signature("Plain", "Service", "make");
		let header = case.context.trait_impls
			[usize::from(case.trait_impl_index("Plain", "Service"))]
		.as_ref()
		.unwrap();
		assert_eq!(make.return_type, header.target.inner);
		// Each written `Self`, in source order: the trait's is its parameter,
		// every impl's names that impl.
		let referents: Vec<_> = SOURCE
			.match_indices("Self")
			.map(|(at, _)| {
				let start = u32::try_from(at).unwrap();
				let span = TextSpan::new(start, start + 4);
				case.context
					.resolutions
					.by_site
					.iter()
					.find(|((site, tier), _)| {
						*tier == Tier::Type && site.span == span
					})
					.map(|(_, referent)| *referent)
			})
			.collect();
		assert!(matches!(referents[0], Some(Referent::TypeParam { .. })));
		assert_eq!(
			referents[1..],
			[
				Some(Referent::InherentImplSelf(
					case.inherent_impl_index("Wrap")
				)),
				Some(Referent::InherentImplSelf(
					case.inherent_impl_index("Plain")
				)),
				Some(Referent::TraitImplSelf(
					case.trait_impl_index("Plain", "Service")
				)),
			]
		);
	}

	/// An impl's header is where its target is written, so `Self` names
	/// nothing there yet.
	#[test]
	fn self_is_not_available_in_an_impl_header() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Marker {}
			struct Wrap<T>();
			impl Marker for Wrap<Self> {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
	}
}
