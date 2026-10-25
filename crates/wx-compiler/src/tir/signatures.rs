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

use rustc_hash::FxHashMap;
use std::ops::Range;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{self, Keyword, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::defs::TypeAliasIdx;
use crate::tir::types::TypeEnvOwner;
use crate::vfs::{FileId, Files};

use super::body::{Body, BodyOwner, ConstBody};
use super::bounds::{
	BindingRequirement, BoundArena, BoundClauses, BoundId, ClauseArena,
	ClauseRange, SourceAssocBinding, SourceTraitBound, TraitClause,
	push_trait_clause, report_duplicate_assoc_type_binding,
	report_not_a_trait_bound, report_not_an_associated_type,
};
use super::defs::{
	AssocTypeIdx, AstEntry, AstNodeRef, BindingKey, BindingTarget, ConstIdx,
	DefId, DefKey, DefKind, DefinitionRegistry, EnumIdx, FunctionIdx,
	GlobalIdx, InherentImplIdx, MemberKind, MemoryIdx, Scope, StructIdx, Tier,
	TraitIdx, TraitImplIdx, TypesetIdx,
};
use super::eval::{Allocation, ConstValueState};
use super::impls::{ImplDispatch, ImplTarget};
use super::imports::report_private_identifier;
use super::members::{
	ApplicableMember, AssocTypeProjectionTarget, MemberLookup,
	TraitMemberSelection, report_ambiguous_type_member,
};
use super::obligations::{BoundRequirements, Obligation};
use super::operators::OperatorTraits;
use super::paths::PathResolver;
use super::resolutions::{NameResolutions, Referent};
use super::satisfaction::{TypeArgsNotAllowedOn, report_type_args_not_allowed};
use super::solver::{ImplMember, Solver, SolverError};
use super::typecheck::BodyContext;
use super::types::{
	ImplKind, Substitution, Type, TypeEnvArena, TypeEnvIdx, TypeIndex,
	TypeInterner, TypeList,
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
	/// the clauses are built from. Left empty for a frame whose one
	/// entry is never itself abstract (an impl's own `Self`, bound
	/// directly to a concrete type) — nothing ever queries bounds for one
	/// of those, so there's nothing to fill in.
	pub declared_bounds: Box<[BoundId]>,
	/// What the parameter assumes, its inherited and nested bounds included
	/// (`BoundClauses`).
	pub(super) clauses: BoundClauses,
}

impl ParamBounds {
	fn empty() -> Self {
		Self {
			declared_bounds: Box::new([]),
			clauses: BoundClauses::PENDING,
		}
	}
}

/// One accepted bound occurrence, decided once by
/// `TypeContext::collect_bound_occurrences` and shared by both the
/// membership builder (`TypeContext::trait_clauses`) and the source-bound
/// resolver (`TypeContext::fill_source_bounds`), so the two cannot disagree
/// about which occurrences exist.
struct BoundOccurrence<'expr> {
	id: BoundId,
	trait_index: TraitIdx,
	span: SourceSpan,
	bindings: Vec<BindingOccurrence<'expr>>,
}

struct BindingOccurrence<'expr> {
	target: AssocTypeProjectionTarget,
	name: Spanned<SymbolU32>,
	kind: BindingOccurrenceKind<'expr>,
}

enum BindingOccurrenceKind<'expr> {
	/// RHS not resolved yet — `fill_source_bounds` resolves it once
	/// every sibling param has provisional memberships published.
	Equals(&'expr Spanned<ast::TypeExpression>),
	Bound(Vec<BoundOccurrence<'expr>>),
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
	/// The signature's scope scope, including enclosing impl/trait frames.
	/// Without own parameters this is the parent's scope. Bounds remain in
	/// the registry's parameter table; body assumptions use this same scope.
	pub(super) type_params: TypeEnvIdx,
	/// The parameter types as written, `self` included: a run of the
	/// interner's lists, which the function's `Call::Args` tuple is built
	/// from.
	pub(super) param_types: TypeList,
	/// `TypeIndex::UNIT` when the source omits `-> Result`.
	pub(super) return_type: TypeIndex,
}

/// Field *types* only — names/dedup/lookup already settled in
/// `defs::StructDef`, index-aligned with whichever `StructFields` variant
/// that struct has, so record vs. tuple doesn't need re-deriving here.
pub struct StructSignature {
	/// See `TypeAliasSignature::type_params`.
	pub(super) type_params: TypeEnvIdx,
	/// The field types as written, in declaration order: a run of the
	/// interner's lists, like a function's `param_types`.
	pub(super) field_types: TypeList,
}

/// The repr every variant's value is held in. A variant is a constant
/// (`defs::EnumDef::variants`), so its value is the constant query's, checked
/// after construction. `TypeIndex::ERROR` if `repr` was missing or resolved to
/// a non-integer type — either way already diagnosed once, here, when that
/// happened.
pub struct EnumSignature {
	pub(super) repr: TypeIndex,
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
	pub(super) ty: TypeIndex,
	/// The type scope the constant is declared in, where its type and
	/// initializer are read.
	pub(super) env: TypeEnvIdx,
}

/// One `AssocTypeIdx`'s resolved signature. `declared_bounds`/
/// `clauses` (`type Name: Bound1 + Bound2;`, resolved against the
/// trait's own `self_scope` — forced first, same as `TraitFunction`/
/// `TraitConst` — so a bound may reference `Self`, e.g. `type Size: Memory
/// where { X = Self::Size }`) only ever come from a trait's own declaration.
/// `value` holds a trait default or an impl's provided type, when present.
/// Each impl definition has a separate `AssocTypeIdx` from its declaration;
/// only the declaration carries bounds and clauses.
pub struct AssocTypeSignature {
	pub(super) declared_bounds: Box<[BoundId]>,
	/// What the declaration assumes about `<Self as Trait>::Name`
	/// (`BoundClauses`); its memberships can be read while equality values
	/// are still being resolved.
	pub(super) clauses: BoundClauses,
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
pub(super) enum InferSignatureKind {
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
pub(super) enum InferPolicy {
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
		// The checker borrows the whole context; the runs it reads are taken
		// out for the sweep and put back unchanged.
		let obligations = std::mem::take(&mut self.obligations);
		for entry in self.ast_nodes {
			let range =
				self.query_state[&entry.node.def_id()].obligations.clone();
			self.check_now(
				&obligations[range.start as usize..range.end as usize],
			);
		}
		self.obligations = obligations;
	}

	/// The body phase. Every signature exists and every fact is final, so a
	/// body may ask the type system anything; nothing it does is recorded for
	/// later. Constant initializers, enum discriminants, function blocks and
	/// global initializers, in definition order, which is the order their
	/// diagnostics come out in.
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
				AstNodeRef::Function { item, .. } => {
					if let ast::Item::Function {
						signature, block, ..
					} = item
					{
						self.check_function_body(entry, signature, block);
					}
				}
				AstNodeRef::TraitFunction { item, .. } => {
					// A required trait method has no block.
					if let ast::TraitItem::Function {
						signature,
						body: Some(block),
						..
					} = item
					{
						self.check_function_body(entry, signature, block);
					}
				}
				AstNodeRef::TraitImplFunction { item, .. }
				| AstNodeRef::InherentImplFunction { item, .. } => {
					if let ast::ImplItem::Function {
						signature, block, ..
					} = item
					{
						self.check_function_body(entry, signature, block);
					}
				}
				AstNodeRef::Global { global_index, item } => {
					let ast::Item::Global { value, .. } = item else {
						unreachable!("a global's entry is a global")
					};
					let scope = LexicalScope {
						file_id: entry.file_id,
						namespace: entry.namespace,
						env: TypeEnvIdx::ROOT,
					};
					let ty = self.global_value_type(global_index);
					let body = BodyContext::new(
						self,
						scope,
						BodyOwner::Global(global_index),
					)
					.check_body(value, ty);
					self.global_bodies[usize::from(global_index)] = Some(body);
				}
				_ => {}
			}
		}
	}

	/// Checks a function's block into its `Body` (`function_bodies`), in the
	/// function's own type scope: its parameters, and an enclosing impl's or
	/// trait's.
	fn check_function_body(
		&mut self,
		entry: &AstEntry<'_>,
		signature: &ast::FunctionSignature,
		block: &Spanned<ast::Expression>,
	) {
		let DefId::Function(function_index) = entry.node.def_id() else {
			unreachable!("a function's entry is a function")
		};
		let scope = LexicalScope {
			file_id: entry.file_id,
			namespace: entry.namespace,
			env: self.functions[usize::from(function_index)].type_params,
		};
		let body =
			BodyContext::new(self, scope, BodyOwner::Function(function_index))
				.check_function(function_index, signature, block);
		self.function_bodies[usize::from(function_index)] = Some(body);
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
	fn resolve_exports(&mut self) -> FxHashMap<SymbolU32, ExportedItem> {
		let mut exports = FxHashMap::with_capacity_and_hasher(
			self.defs.exports.len(),
			Default::default(),
		);
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
/// Keyed directly by `DefId` (`query_state: FxHashMap<DefId, QueryEntry>`
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

/// Where code is written: the file its spans are in, the namespace its
/// names resolve from, and the type scope its parameters and assumptions come
/// from. A lowering entering a new type scope narrows `env`.
#[derive(Clone, Copy)]
pub(super) struct LexicalScope {
	pub(super) file_id: FileId,
	pub(super) namespace: Scope,
	pub(super) env: TypeEnvIdx,
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
	pub(super) strings: &'ctx mut StringInterner,
	/// Source text, for literals whose value is read from their span.
	pub(super) files: &'ctx Files,
	pub(super) defs: &'ctx DefinitionRegistry,
	/// The trait and method each overloadable operator dispatches through.
	pub(super) operators: OperatorTraits,
	ast_nodes: &'ast [AstEntry<'ast>],
	// The resolved data below is read across the sibling TIR modules.
	query_state: FxHashMap<DefId, QueryEntry>,
	/// In-progress queries, in call order.
	pub(super) query_stack: Vec<QueryInfo>,
	pub(super) solver: Solver,
	pub(super) types: TypeInterner,
	pub(super) bounds: BoundArena,
	/// What each parameter and associated declaration assumes, flat
	/// (`BoundClauses`).
	pub(super) clauses: ClauseArena,
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
	pub(super) enums: Vec<EnumSignature>,
	typesets: Vec<TypeSetSignature>,
	pub(super) assoc_types: Vec<Option<AssocTypeSignature>>,
	pub(super) functions: Vec<FunctionSignature>,
	pub(super) constants: Vec<ConstantSignature>,
	/// Each constant's checked initializer, by `ConstIdx`; built on demand
	/// (`ensure_const_body`). A trait constant without a default has none.
	pub(super) const_bodies: Vec<ConstBody>,
	/// Each constant's value query state, by `ConstIdx` (`eval.rs`).
	pub(super) const_values: Vec<ConstValueState>,
	/// The constants being evaluated, outermost first.
	pub(super) const_stack: Vec<ConstIdx>,
	/// The bytes constant values point into, by `AllocIdx` (`eval.rs`).
	pub(super) allocations: Vec<Allocation>,
	/// Each function's checked block, by `FunctionIdx`; `None` for one
	/// without a block (a declaration, an import, a required trait method).
	pub(super) function_bodies: Vec<Option<Body>>,
	/// Each global's checked initializer, by `GlobalIdx`; `None` for an
	/// imported one.
	pub(super) global_bodies: Vec<Option<Body>>,
	pub(super) inherent_impls: Vec<Option<InherentImplSignature>>,
	pub(super) trait_impls: Vec<Option<TraitImplSignature>>,
	/// Resolved, exportable targets keyed by decoded external name; filled by `sweep`.
	pub exports: FxHashMap<SymbolU32, ExportedItem>,
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
		strings: &'ctx mut StringInterner,
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
		let query_state: FxHashMap<DefId, QueryEntry> = ast_nodes
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

		let operators = OperatorTraits::new(defs, strings);
		Self {
			diagnostics,
			resolutions,
			strings,
			files,
			defs,
			operators,
			ast_nodes,
			query_state,
			query_stack: Vec::new(),
			solver: Solver::new(),
			types: TypeInterner::new(),
			bounds: BoundArena::default(),
			clauses: ClauseArena::default(),
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
					field_types: TypeList::EMPTY,
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
					param_types: TypeList::EMPTY,
					return_type: TypeIndex::ERROR,
				})
				.collect(),
			constants: defs
				.constants
				.iter()
				.map(|_| ConstantSignature {
					ty: TypeIndex::ERROR,
					env: TypeEnvIdx::ROOT,
				})
				.collect(),
			const_bodies: defs
				.constants
				.iter()
				.map(|_| ConstBody::NotBuilt)
				.collect(),
			function_bodies: defs.functions.iter().map(|_| None).collect(),
			global_bodies: defs.globals.iter().map(|_| None).collect(),
			const_values: defs
				.constants
				.iter()
				.map(|_| ConstValueState::Unevaluated)
				.collect(),
			const_stack: Vec::new(),
			allocations: Vec::new(),
			inherent_impls: defs.inherent_impls.iter().map(|_| None).collect(),
			trait_impls: defs.trait_impls.iter().map(|_| None).collect(),
			exports: FxHashMap::default(),
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
		obligations: &mut Vec<Obligation>,
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
				.find(|p| p.name().inner == param.name().inner)
				.map(|p| p.name())
			{
				self.diagnostics.push(report_duplicate_generic_param(
					self.strings,
					file_id,
					param.name(),
					colliding_param,
				));
			}
		}

		let type_env = self.type_envs.push_param_frame(
			&mut self.types,
			owner,
			parent,
			params.iter().map(|p| p.name()),
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
		// both the membership pass below and the source-bound pass after it
		// consume that same decided tree, so they cannot disagree about what
		// they saw. See `collect_bound_occurrences`.
		let mut occurrences_per_param = Vec::with_capacity(params.len());
		for ast_param in params {
			let mut occurrences = Vec::new();
			match ast_param {
				ast::TypeParam::Type {
					bounds: Some(bound),
					..
				} => self.collect_bound_occurrences(
					file_id,
					namespace,
					bound,
					&mut occurrences,
				),
				ast::TypeParam::Type { bounds: None, .. } => {}
				// Kept as a type parameter with no bounds, so the arguments
				// still line up, until constants are checked.
				ast::TypeParam::Const {
					const_span, name, ..
				} => self.diagnostics.push(
					Diagnostic::bug()
						.with_code(DiagnosticCode::UnsupportedExpression.code())
						.with_message(
							"constant parameters are not supported yet",
						)
						.with_label(
							SourceSpan::new(
								file_id,
								TextSpan::new(const_span.start, name.span.end),
							)
							.primary_label(),
						),
				),
			}
			occurrences_per_param.push(occurrences);
		}

		// Publish every sibling's memberships first: an equality's value,
		// resolved next, can name the members they supply. No value is
		// resolved here.
		for (index, occurrences) in occurrences_per_param.iter().enumerate() {
			let subject = self.type_envs.param_types(type_env)[index];
			let traits = self.trait_clauses(subject, occurrences);
			self.param_bounds[usize::from(type_env)][index] = ParamBounds {
				declared_bounds: occurrences.iter().map(|o| o.id).collect(),
				clauses: BoundClauses {
					traits,
					equalities: None,
				},
			};
		}

		// Resolve source bounds now that every sibling has provisional
		// memberships published, so an equality RHS can reference them.
		// Bound IDs were published above; filling their sources preserves them.
		for (index, occurrences) in occurrences_per_param.iter().enumerate() {
			let subject = self.type_envs.param_types(type_env)[index];
			self.fill_source_bounds(
				obligations,
				LexicalScope {
					file_id,
					namespace,
					env: type_env,
				},
				subject,
				occurrences,
			);
		}

		for (index, ast_param) in params.iter().enumerate() {
			let subject = self.type_envs.param_types(type_env)[index];
			let ids = std::mem::take(
				&mut self.param_bounds[usize::from(type_env)][index]
					.declared_bounds,
			);
			let equalities =
				self.equality_clauses(subject, &ids, ast_param.name().inner);
			let bounds = &mut self.param_bounds[usize::from(type_env)][index];
			bounds.declared_bounds = ids;
			bounds.clauses.equalities = Some(equalities);
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
	/// (not routed through `resolve_generic_params`) is filled by the
	/// trait's own signature: its supertraits, as clauses on `Self`, which
	/// `inherit_trait_clauses` copies into every bound that names the trait.
	fn reserve_param_bounds(&mut self, frame: TypeEnvIdx) {
		debug_assert_eq!(usize::from(frame), self.param_bounds.len());
		let count = self.type_envs.param_types(frame).len();
		self.param_bounds
			.push((0..count).map(|_| ParamBounds::empty()).collect());
	}

	/// What `Self` means inside an impl: the impl's target, found through the
	/// frame every impl owns. `None` outside an impl, and in the impl's own
	/// header, whose target is what `Self` would name.
	pub(super) fn resolve_impl_self(
		&self,
		env: TypeEnvIdx,
	) -> Option<(ImplKind, TypeIndex)> {
		let impl_kind = self.type_envs.enclosing_impl(env)?;
		let target = match impl_kind {
			ImplKind::Inherent(index) => {
				self.inherent_impls[usize::from(index)].as_ref()?.target
			}
			ImplKind::Trait(index) => {
				self.trait_impls[usize::from(index)].as_ref()?.target
			}
		};
		Some((impl_kind, target.inner))
	}

	/// Type arguments written on an impl's `Self`, which already names the
	/// target with its arguments: the target is shown, and a struct's own
	/// name suggested for writing other arguments.
	pub(super) fn report_type_args_on_impl_self(
		&self,
		file_id: FileId,
		segment: &ast::PathSegment,
		impl_kind: ImplKind,
	) -> Diagnostic<FileId> {
		// `Self` resolves only past the impl's header.
		let (impl_file, target) = match impl_kind {
			ImplKind::Inherent(index) => (
				self.defs.inherent_impls[usize::from(index)].file_id,
				self.inherent_impls[usize::from(index)]
					.as_ref()
					.unwrap()
					.target,
			),
			ImplKind::Trait(index) => (
				self.defs.trait_impls[usize::from(index)].file_id,
				self.trait_impls[usize::from(index)]
					.as_ref()
					.unwrap()
					.target,
			),
		};
		let (first, last) = (
			segment.type_args.first().unwrap(),
			segment.type_args.last().unwrap(),
		);
		let target_name = self.type_formatter().display_type(target.inner);
		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::TypeArgumentsNotAllowed.code())
			.with_message("type arguments are not allowed on `Self`")
			.with_labels(vec![
				SourceSpan::new(
					file_id,
					TextSpan::new(first.span().start, last.span().end),
				)
				.primary_label()
				.with_message(format!(
					"type argument{} not allowed",
					if segment.type_args.len() == 1 {
						""
					} else {
						"s"
					}
				)),
				SourceSpan::new(file_id, segment.ident.span)
					.secondary_label()
					.with_message("not allowed on `Self`"),
				SourceSpan::new(impl_file, target.span)
					.secondary_label()
					.with_message(format!(
						"`Self` is `{target_name}` in this impl"
					)),
			]);
		match self.types.resolve(target.inner) {
			Type::Struct { struct_index, .. } => {
				let name = self.defs.structs[usize::from(*struct_index)].name;
				diagnostic.with_note(format!(
					"to write other type arguments, use the struct's name `{}` instead",
					self.strings.resolve(name.inner).unwrap()
				))
			}
			_ => diagnostic,
		}
	}

	/// Resolves a written impl target in the impl's own parameter frame. The
	/// dispatch head only identifies candidates; its arguments are checked and
	/// retained here so matching can use the full target later.
	fn resolve_impl_target(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
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
							SourceSpan::new(scope.file_id, segment.ident.span)
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
					scope.file_id,
					segment.ident.span,
				)),
			});
		}
		let params_env = self.structs[usize::from(struct_index)].type_params;
		let resolved_args: Box<[TypeIndex]> = segment
			.type_args
			.iter()
			.map(|arg| {
				self.resolve_type_argument(
					obligations,
					scope,
					arg,
					InferPolicy::Reject(InferSignatureKind::AssocTypeBinding),
				)
			})
			.collect();
		let args = self.resolve_type_args(
			obligations,
			scope,
			segment,
			params_env,
			&[],
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
			ImplKind::Inherent(impl_index),
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

	/// A global's value type, as written; `ERROR` when it is missing.
	pub(super) fn global_value_type(
		&self,
		global_index: GlobalIdx,
	) -> TypeIndex {
		let index =
			self.defs.globals[usize::from(global_index)].value_assoc_type_index;
		self.assoc_types[usize::from(index)]
			.as_ref()
			.and_then(|signature| signature.value)
			.unwrap_or(TypeIndex::ERROR)
	}

	/// A typeset's member types.
	pub(super) fn typeset_members(
		&self,
		typeset_index: TypesetIdx,
	) -> &[Spanned<TypeIndex>] {
		&self.typesets[usize::from(typeset_index)].members
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
		self.query_stack.push(query);

		let entry =
			&self.ast_nodes[self.query_state[&query.def_id].ast_index as usize];
		// A nested query keeps its own list, so this one's obligations join
		// the shared list as one run when it finishes.
		let mut obligations = Vec::new();
		let location = self.compute_signature(
			&mut obligations,
			entry.file_id,
			entry.namespace,
			entry.node,
		);

		self.query_stack.pop();
		let start = u32::try_from(self.obligations.len()).unwrap();
		self.obligations.extend(obligations);
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
		obligations: &mut Vec<Obligation>,
		file_id: FileId,
		namespace: Scope,
		function_index: FunctionIdx,
		signature: &ast::FunctionSignature,
	) -> SignatureLocation {
		let type_env = self.resolve_generic_params(
			obligations,
			file_id,
			namespace,
			TypeEnvOwner::Function(function_index),
			TypeEnvIdx::ROOT,
			&signature.type_params,
		);

		let param_types: Vec<TypeIndex> = signature
			.params
			.iter()
			.map(|param| {
				// A free function has no `Self`: its `self` was reported
				// where it is written.
				let receiver = param
					.inner
					.inner
					.binding
					.and_then(ast::Binding::name)
					.is_some_and(|name| {
						name.inner == Keyword::SelfLower.symbol()
					});
				if receiver {
					return TypeIndex::ERROR;
				}
				self.resolve_type(
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: type_env,
					},
					&param.inner.inner.ty,
					InferPolicy::Reject(InferSignatureKind::Function),
				)
			})
			.collect();

		let return_type = match &signature.result {
			Some(result) => self.resolve_type(
				obligations,
				LexicalScope {
					file_id,
					namespace,
					env: type_env,
				},
				result,
				InferPolicy::Reject(InferSignatureKind::ReturnType),
			),
			None => TypeIndex::UNIT,
		};

		let param_types = self.types.push_list(&param_types);
		self.resolve_function_impls(
			obligations,
			file_id,
			function_index,
			type_env,
			param_types,
			return_type,
			signature,
		);
		self.functions[usize::from(function_index)] = FunctionSignature {
			type_params: type_env,
			param_types,
			return_type,
		};
		SignatureLocation::Function(function_index)
	}

	/// Fills a function's synthetic `impl Call` and `impl Function`: generic
	/// over every parameter on the function's chain, with their bounds as
	/// their assumptions. `Args` is the one parameter type (`func(..)`'s
	/// rule), a method's `self` included.
	fn resolve_function_impls(
		&mut self,
		obligations: &mut Vec<Obligation>,
		file_id: FileId,
		function_index: FunctionIdx,
		type_env: TypeEnvIdx,
		param_types: TypeList,
		return_type: TypeIndex,
		signature: &ast::FunctionSignature,
	) {
		let function_def = &self.defs.functions[usize::from(function_index)];
		let function_impls = function_def.function_impls;
		let name_span = function_def.name.span;
		// The tuple is interned over the signature's own list, so nothing is
		// copied; none is the empty tuple, `()`.
		let args = match *self.types.list(param_types) {
			[param] => param,
			_ => self.types.intern(Type::Tuple {
				elements: param_types,
			}),
		};
		// Instantiating `type_env` takes an argument for every parameter on
		// its chain, outer first, so a member's type carries its parent's
		// parameters ahead of its own (`Wrap<T>::get<U>` is `get<T, U>`).
		let function_type = self.types.intern_function(
			function_index,
			self.type_envs.identity_args(type_env),
		);
		// Each value is judged as the member's own (`CheckAssocValue`), so a
		// loop through it (`func f() -> f::Result`) is reported once, here.
		let call_trait = self.defs.intrinsics.call.expect(
			"checked by impls.rs's dispatch pass before any signature is resolved",
		);
		let args_span = match &signature.params[..] {
			[param] => Some(param.inner.inner.ty.span),
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
			obligations.push(Obligation::CheckAssocValue {
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
				clauses: BoundClauses::NONE,
				value: Some(args),
			});
		self.assoc_types[usize::from(function_impls.result_assoc_type_index)] =
			Some(AssocTypeSignature {
				declared_bounds: Box::new([]),
				clauses: BoundClauses::NONE,
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
	}

	/// Resolve a member in its parent's scope (the trait's or the impl's),
	/// with a child frame for method generics. Definition collection already
	/// validates receiver position.
	fn resolve_member_function_signature(
		&mut self,
		obligations: &mut Vec<Obligation>,
		file_id: FileId,
		namespace: Scope,
		function_index: FunctionIdx,
		parent: TypeEnvIdx,
		signature: &ast::FunctionSignature,
	) -> SignatureLocation {
		let scope = self.resolve_generic_params(
			obligations,
			file_id,
			namespace,
			TypeEnvOwner::Function(function_index),
			parent,
			&signature.type_params,
		);

		// Definition collection diagnoses misplaced receivers.
		let param_types: Vec<TypeIndex> = signature
			.params
			.iter()
			.map(|param| {
				self.resolve_type(
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: scope,
					},
					&param.inner.inner.ty,
					InferPolicy::Reject(InferSignatureKind::Function),
				)
			})
			.collect();

		let return_type = match &signature.result {
			Some(result) => self.resolve_type(
				obligations,
				LexicalScope {
					file_id,
					namespace,
					env: scope,
				},
				result,
				InferPolicy::Reject(InferSignatureKind::ReturnType),
			),
			None => TypeIndex::UNIT,
		};

		let param_types = self.types.push_list(&param_types);
		self.resolve_function_impls(
			obligations,
			file_id,
			function_index,
			scope,
			param_types,
			return_type,
			signature,
		);
		self.functions[usize::from(function_index)] = FunctionSignature {
			type_params: scope,
			param_types,
			return_type,
		};
		SignatureLocation::Function(function_index)
	}

	/// Resolve a constant's required annotation in its declaration scope.
	fn resolve_constant_signature(
		&mut self,
		obligations: &mut Vec<Obligation>,
		file_id: FileId,
		namespace: Scope,
		const_index: ConstIdx,
		scope: TypeEnvIdx,
		name: Spanned<SymbolU32>,
		ty: Option<&Spanned<ast::TypeExpression>>,
	) -> SignatureLocation {
		let ty = match ty {
			Some(ty) => self.resolve_type(
				obligations,
				LexicalScope {
					file_id,
					namespace,
					env: scope,
				},
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
			ConstantSignature { ty, env: scope };
		SignatureLocation::Constant(const_index)
	}

	/// Checks a constant's initializer into its `Body` (`const_bodies`), once.
	/// On demand: evaluating one constant may need another's body first.
	pub(super) fn ensure_const_body(&mut self, const_index: ConstIdx) {
		match &self.const_bodies[usize::from(const_index)] {
			ConstBody::Built(_) | ConstBody::Building => return,
			ConstBody::NotBuilt => {}
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
				self.const_bodies[usize::from(const_index)] =
					ConstBody::Building;
				let body = BodyContext::new(
					self,
					LexicalScope {
						file_id,
						namespace,
						env: TypeEnvIdx::ROOT,
					},
					BodyOwner::Const(const_index),
				)
				.check_variant_value(item, previous, repr);
				self.const_bodies[usize::from(const_index)] =
					ConstBody::Built(body);
				return;
			}
			_ => unreachable!("a constant's entry is a constant"),
		};
		let env = self.constants[usize::from(const_index)].env;
		let ty = self.constants[usize::from(const_index)].ty;
		let scope = LexicalScope {
			file_id,
			namespace,
			env,
		};
		// Mark the body as being built before building it. Building it may
		// read this constant's value — a pattern in its initializer names
		// it — and a read of a constant whose body is being built must not
		// build that body again: the two builds would ask each other for a
		// value forever.
		self.const_bodies[usize::from(const_index)] = ConstBody::Building;
		let body = BodyContext::new(self, scope, BodyOwner::Const(const_index))
			.check_body(value, ty);
		self.const_bodies[usize::from(const_index)] = ConstBody::Built(body);
	}

	/// A constant's body, if it is built. `None` when it is not built yet,
	/// when it is being built, or when it has none (a required trait
	/// constant).
	pub(super) fn const_body(&self, const_index: ConstIdx) -> Option<&Body> {
		match &self.const_bodies[usize::from(const_index)] {
			ConstBody::Built(body) => Some(body),
			ConstBody::NotBuilt | ConstBody::Building => None,
		}
	}

	/// Resolves and validates a `memory` declaration's `Size` and fills in
	/// its synthetic `Memory` impl. Shared by `AstNodeRef::Memory` and
	/// `AstNodeRef::ImportedMemory` — a declared memory and an imported one
	/// resolve identically once their `size` type expression is in hand.
	fn resolve_memory_signature(
		&mut self,
		obligations: &mut Vec<Obligation>,
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
			obligations,
			LexicalScope {
				file_id,
				namespace,
				env: TypeEnvIdx::ROOT,
			},
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
		let memory_type = self.types.intern(Type::Memory { memory_index });
		let checked_size = self.record_bounds_check(
			obligations,
			TypeEnvIdx::ROOT,
			BoundRequirements::AssociatedType {
				declaration: declared_size_index,
				trait_index: memory_trait,
				receiver: memory_type,
			},
			Spanned {
				inner: resolved_size,
				span: size.span,
			},
			SourceSpan::new(file_id, size.span),
			TypeEnvOwner::Trait(memory_trait),
		);

		self.assoc_types[usize::from(size_assoc_type_index)] =
			Some(AssocTypeSignature {
				declared_bounds: Box::new([]),
				clauses: BoundClauses::NONE,
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
	/// `value` — a written global may omit its type and gets diagnosed for
	/// it, an imported one's type is mandatory in the grammar.
	fn resolve_global_signature(
		&mut self,
		obligations: &mut Vec<Obligation>,
		file_id: FileId,
		global_index: GlobalIdx,
		name: Spanned<SymbolU32>,
		mut_span: Option<TextSpan>,
		value: Spanned<TypeIndex>,
	) -> SignatureLocation {
		let global_def = &self.defs.globals[usize::from(global_index)];
		let trait_impl_index = global_def.trait_impl_index;
		let value_assoc_type_index = global_def.value_assoc_type_index;
		let mut_trait_impl_index = global_def.mut_trait_impl_index;

		let global_type = self.types.intern(Type::Global { global_index });

		// `Value`'s constraint lives on `Global`'s own declaration, checked
		// like `Memory::Size` (`resolve_memory_signature`).
		let global_trait = self.defs.intrinsics.global.expect(
			"checked by impls.rs's dispatch pass before any signature is resolved",
		);
		let value_symbol = self
			.strings
			.get("Value")
			.expect("interned by synthesize_global_impl during pre-scan");
		let Some(MemberKind::AssociatedType(declared_value_index)) = self
			.defs
			.declared_trait_member(global_trait, BindingKey::ty(value_symbol))
		else {
			panic!("the stdlib's `Global` trait must declare `type Value`")
		};
		let resolved_value = if value.inner == TypeIndex::ERROR {
			value.inner
		} else {
			self.record_bounds_check(
				obligations,
				TypeEnvIdx::ROOT,
				BoundRequirements::AssociatedType {
					declaration: declared_value_index,
					trait_index: global_trait,
					receiver: global_type,
				},
				value,
				SourceSpan::new(file_id, value.span),
				TypeEnvOwner::Trait(global_trait),
			)
		};

		self.assoc_types[usize::from(value_assoc_type_index)] =
			Some(AssocTypeSignature {
				declared_bounds: Box::new([]),
				clauses: BoundClauses::NONE,
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
		obligations: &mut Vec<Obligation>,
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
								obligations,
								file_id,
								namespace,
								TypeEnvOwner::TypeAlias(type_alias_index),
								TypeEnvIdx::ROOT,
								type_params,
							);
							let target = match body {
								Some(body) => self.resolve_type(
									obligations,
									LexicalScope {
										file_id,
										namespace,
										env: type_env,
									},
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
					obligations,
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
				let subject = self.type_envs.param_types(self_scope)[0];
				let (declared_bounds, clauses) = self.resolve_subject_bounds(
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: self_scope,
					},
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
					clauses,
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

				self.resolve_member_function_signature(
					obligations,
					file_id,
					namespace,
					function_index,
					self_scope,
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
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: self_scope,
					},
					ty,
					InferPolicy::Reject(InferSignatureKind::Const),
				);

				self.constants[usize::from(const_index)] = ConstantSignature {
					ty: resolved_ty,
					env: self_scope,
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

				let base = self.type_envs.param_types(self_scope)[0];
				let subject = self.types.intern(Type::AssocTypeProjection {
					base,
					trait_index,
					assoc_type_index,
				});
				let (resolved_bounds, clauses) = self.resolve_subject_bounds(
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: self_scope,
					},
					bounds.as_ref(),
					BoundSubject::Assoc(assoc_type_index),
					subject,
					name.inner,
				);
				let resolved_value = value.as_ref().map(|value| {
					self.resolve_type(
						obligations,
						LexicalScope {
							file_id,
							namespace,
							env: self_scope,
						},
						value,
						InferPolicy::Reject(
							InferSignatureKind::AssocTypeBinding,
						),
					)
				});
				self.assoc_types[usize::from(assoc_type_index)] =
					Some(AssocTypeSignature {
						declared_bounds: resolved_bounds,
						clauses,
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
				let scope = header.type_params;
				self.resolve_member_function_signature(
					obligations,
					file_id,
					namespace,
					function_index,
					scope,
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
					obligations,
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
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: scope,
					},
					block_index,
					assoc_type_index,
					ty,
				);

				// An impl provides a value, it doesn't declare a
				// requirement — `declared_bounds`/`clauses` stay
				// empty; only a trait's own declaration (the
				// `TraitAssocType` arm above) ever populates those.
				self.assoc_types[usize::from(assoc_type_index)] =
					Some(AssocTypeSignature {
						declared_bounds: Box::new([]),
						clauses: BoundClauses::NONE,
						value: Some(resolved_ty),
					});
				SignatureLocation::AssocType(assoc_type_index)
			}
			AstNodeRef::Memory { memory_index, item } => {
				let ast::Item::Memory { name, size, .. } = item else {
					unreachable!()
				};
				self.resolve_memory_signature(
					obligations,
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
					obligations,
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
				let value = match ty {
					Some(ty) => {
						let global_def =
							&self.defs.globals[usize::from(global_index)];
						Spanned {
							inner: self.resolve_assoc_value(
								obligations,
								LexicalScope {
									file_id,
									namespace,
									env: TypeEnvIdx::ROOT,
								},
								global_def.trait_impl_index,
								global_def.value_assoc_type_index,
								ty,
							),
							span: ty.span,
						}
					}
					None => {
						self.diagnostics
							.push(report_missing_global_type(file_id, *name));
						Spanned {
							inner: TypeIndex::ERROR,
							span: name.span,
						}
					}
				};
				self.resolve_global_signature(
					obligations,
					file_id,
					global_index,
					*name,
					*mut_span,
					value,
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
				let value = Spanned {
					inner: self.resolve_assoc_value(
						obligations,
						LexicalScope {
							file_id,
							namespace,
							env: TypeEnvIdx::ROOT,
						},
						global_def.trait_impl_index,
						global_def.value_assoc_type_index,
						ty,
					),
					span: ty.span,
				};
				self.resolve_global_signature(
					obligations,
					file_id,
					global_index,
					*name,
					*mut_span,
					value,
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
					obligations,
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
						obligations,
						LexicalScope {
							file_id,
							namespace,
							env: type_env,
						},
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
					self.types.push_list(&field_types);
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
					obligations,
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
					obligations,
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
					obligations,
					file_id,
					namespace,
					TypeEnvOwner::InherentImpl(block_index),
					TypeEnvIdx::ROOT,
					type_params,
				);
				let target_type = self.resolve_impl_target(
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: scope,
					},
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
				if !self.type_envs.param_types(scope).is_empty() {
					obligations.push(Obligation::CheckImplRequirements {
						impl_kind: ImplKind::Inherent(block_index),
						reference: SourceSpan::new(file_id, target.span()),
					});
				}
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
				let scope = header.type_params;
				self.resolve_member_function_signature(
					obligations,
					file_id,
					namespace,
					function_index,
					scope,
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
					obligations,
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
					obligations,
					file_id,
					namespace,
					TypeEnvOwner::TraitImpl(block_index),
					TypeEnvIdx::ROOT,
					type_params,
				);
				let header = self.impl_dispatch.trait_header(block_index);
				let target_type = self.resolve_impl_target(
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: scope,
					},
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
				if !self.type_envs.param_types(scope).is_empty() {
					obligations.push(Obligation::CheckImplRequirements {
						impl_kind: ImplKind::Trait(block_index),
						reference: SourceSpan::new(file_id, target.span()),
					});
				}
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
							obligations.push(Obligation::CheckAssocValue {
								member: ImplMember {
									impl_index: block_index,
									declaration: index,
								},
								reference: SourceSpan::new(
									file_id,
									target.span(),
								),
							});
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
							obligations,
							LexicalScope {
								file_id,
								namespace,
								env: TypeEnvIdx::ROOT,
							},
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
					env: TypeEnvIdx::ROOT,
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
				let subject = self.type_envs.param_types(self_scope)[0];
				let (clause_bounds, clauses) = self.resolve_subject_bounds(
					obligations,
					LexicalScope {
						file_id,
						namespace,
						env: self_scope,
					},
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
					clauses,
				};
				self.traits[usize::from(trait_index)] =
					TraitSignature { env: self_scope };

				// Dispatch already registered each member as a synthetic impl.
				// Resolve its complete type and fill the pre-allocated signature.
				let mut resolved_members = Vec::with_capacity(members.len());
				for (m, &impl_index) in members.iter().zip(member_impls.iter())
				{
					let member_ty = self.resolve_impl_target(
						obligations,
						LexicalScope {
							file_id,
							namespace,
							env: TypeEnvIdx::ROOT,
						},
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

	/// A tag is an ordinary type with an additional Memory requirement.
	fn resolve_memory_tag(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		segments: &[ast::PathSegment],
		infer_policy: InferPolicy,
	) -> TypeIndex {
		let ty =
			self.resolve_type_path(obligations, scope, segments, infer_policy);
		if ty == TypeIndex::ERROR {
			return ty;
		}
		let required = self
			.defs
			.intrinsics
			.memory
			.expect("memory tags require the intrinsic Memory trait");
		let reference = SourceSpan::new(
			scope.file_id,
			TextSpan::new(
				segments[0].ident.span.start,
				segments.last().unwrap().ident.span.end,
			),
		);
		let obligation = Obligation::CheckTraitMembership {
			assumption_context: scope.env,
			subject: ty,
			required,
			reference,
		};
		obligations.push(obligation);
		ty
	}

	/// The memory a pointer/slice/array type belongs to: its `heap::` tag.
	/// A type without one is an error; there is no default memory to guess
	/// from, however many are declared. Shared by `Pointer`/`Slice`/
	/// `Array`'s three arms in `resolve_type`, which otherwise differ only in
	/// which `Type` variant they intern.
	fn resolve_pointer_memory(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		memory: &Option<Box<[ast::PathSegment]>>,
		span: TextSpan,
		infer_policy: InferPolicy,
	) -> Result<TypeIndex, ()> {
		match memory {
			Some(segments) => Ok(self.resolve_memory_tag(
				obligations,
				scope,
				segments,
				infer_policy,
			)),
			None => {
				self.diagnostics
					.push(report_pointer_without_memory(scope.file_id, span));
				Err(())
			}
		}
	}

	/// Resolve a written signature type. `_` follows the caller's inference
	/// policy; nominal types retain their structure. The type is stored as
	/// written, with projections unreduced; the declaration check normalizes it once
	/// to find cycles, and readers normalize under their own assumptions.
	/// A written type argument as `resolve_type` lowers a type. A constant
	/// argument is not supported yet: it is reported, and is `ERROR`.
	pub(super) fn resolve_type_argument(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		arg: &ast::TypeArgument,
		infer_policy: InferPolicy,
	) -> TypeIndex {
		match arg {
			ast::TypeArgument::Type(ty) => {
				self.resolve_type(obligations, scope, ty, infer_policy)
			}
			ast::TypeArgument::Const(constant) => {
				self.report_const_argument(scope, constant.span)
			}
		}
	}

	/// A written type argument as `resolve_type_expression` lowers a type.
	fn resolve_type_argument_expression(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		arg: &ast::TypeArgument,
		infer_policy: InferPolicy,
	) -> TypeIndex {
		match arg {
			ast::TypeArgument::Type(ty) => self.resolve_type_expression(
				obligations,
				scope,
				ty,
				infer_policy,
			),
			ast::TypeArgument::Const(constant) => {
				self.report_const_argument(scope, constant.span)
			}
		}
	}

	/// The length an array type is written with. Only an integer literal
	/// that fits a `u32` is checked yet; a constant's value is a later step.
	fn array_length(
		&mut self,
		scope: LexicalScope,
		length: &Spanned<ast::ConstArgument>,
	) -> Option<u32> {
		let site = SourceSpan::new(scope.file_id, length.span);
		let diagnostic = match length.inner {
			ast::ConstArgument::Literal(ast::Literal::Int(value)) => {
				match u32::try_from(value) {
					Ok(size) => return Some(size),
					Err(_) => Diagnostic::bug()
						.with_code(DiagnosticCode::UnsupportedExpression.code())
						.with_message(
							"array lengths above `u32::MAX` are not supported \
							 yet",
						)
						.with_label(site.primary_label()),
				}
			}
			ast::ConstArgument::Literal(_) => Diagnostic::error()
				.with_code(DiagnosticCode::TypeMistmatch.code())
				.with_message("an array's length is an integer")
				.with_label(
					site.primary_label().with_message("not an integer"),
				),
			ast::ConstArgument::Path(_) => Diagnostic::bug()
				.with_code(DiagnosticCode::UnsupportedExpression.code())
				.with_message("constant array lengths are not supported yet")
				.with_label(site.primary_label()),
		};
		self.diagnostics.push(diagnostic);
		None
	}

	fn report_const_argument(
		&mut self,
		scope: LexicalScope,
		span: TextSpan,
	) -> TypeIndex {
		self.diagnostics.push(
			Diagnostic::bug()
				.with_code(DiagnosticCode::UnsupportedExpression.code())
				.with_message("constant arguments are not supported yet")
				.with_label(
					SourceSpan::new(scope.file_id, span).primary_label(),
				),
		);
		TypeIndex::ERROR
	}

	pub(super) fn resolve_type(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		type_expr: &Spanned<ast::TypeExpression>,
		infer_policy: InferPolicy,
	) -> TypeIndex {
		let ty = self.resolve_type_expression(
			obligations,
			scope,
			type_expr,
			infer_policy,
		);
		if ty != TypeIndex::ERROR {
			obligations.push(Obligation::CheckWellFormed {
				assumption_context: scope.env,
				ty,
				reference: SourceSpan::new(scope.file_id, type_expr.span),
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
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
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
				obligations,
				scope,
				type_expr,
				infer_policy,
			);
		};
		let ty = self.resolve_type_expression(
			obligations,
			scope,
			type_expr,
			infer_policy,
		);
		// Lowering that failed has already reported; nothing to judge.
		if ty != TypeIndex::ERROR {
			obligations.push(Obligation::CheckAssocValue {
				member: ImplMember {
					impl_index,
					declaration,
				},
				reference: SourceSpan::new(scope.file_id, type_expr.span),
			});
		}
		ty
	}

	/// Resolve both ordinary type paths and explicit memory tags.
	pub(super) fn resolve_type_path(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		segments: &[ast::PathSegment],
		infer_policy: InferPolicy,
	) -> TypeIndex {
		// The first segment tries `TypeEnv` regardless of how many
		// segments follow — `Self::Value`/`T::Size` never touch the
		// scope.namespace graph at all for their own first hop, same as a
		// bare `T`/`Self` doesn't. Only once that fails does the
		// scope.namespace graph get a turn. Either branch leaves `next`
		// at the first segment *not yet* consumed. Written arguments
		// don't change what the name means: a parameter shadows an
		// item of the same name with or without them, and takes none.
		let first = &segments[0];
		let site =
			(SourceSpan::new(scope.file_id, first.ident.span), Tier::Type);
		let (current, next) = if let Some((frame, index)) =
			self.type_envs.resolve(scope.env, first.ident.inner)
		{
			self.resolutions
				.by_site
				.insert(site, Referent::TypeParam { env: frame, index });
			if !first.type_args.is_empty() {
				// Resolved only to report what is wrong inside them.
				for arg in &first.type_args {
					self.resolve_type_argument_expression(
						obligations,
						scope,
						arg,
						infer_policy,
					);
				}
				self.diagnostics.push(report_type_args_not_allowed(
					self.strings,
					self.defs,
					scope.file_id,
					first,
					TypeArgsNotAllowedOn::TypeParam {
						owner: self.type_envs.owner(frame),
						name: &self.type_envs.param_names(frame)
							[index as usize],
					},
				));
			}
			(self.type_envs.param_types(frame)[index as usize], 1)
		} else if first.ident.inner == Keyword::SelfPascal.symbol()
			&& let Some((impl_kind, target)) = self.resolve_impl_self(scope.env)
		{
			self.resolutions.by_site.insert(
				site,
				match impl_kind {
					ImplKind::Inherent(index) => {
						Referent::InherentImplSelf(index)
					}
					ImplKind::Trait(index) => Referent::TraitImplSelf(index),
				},
			);
			if !first.type_args.is_empty() {
				// Resolved only to report what is wrong inside them.
				for arg in &first.type_args {
					self.resolve_type_argument_expression(
						obligations,
						scope,
						arg,
						infer_policy,
					);
				}
				let diagnostic = self.report_type_args_on_impl_self(
					scope.file_id,
					first,
					impl_kind,
				);
				self.diagnostics.push(diagnostic);
			}
			(target, 1)
		} else {
			// TODO: this probably should be resolve_path instead of walk_path
			let walk = PathResolver::new(
				self.diagnostics,
				self.resolutions,
				self.strings,
				self.defs,
			)
			.walk_path(scope.file_id, scope.namespace, segments, Tier::Type);
			let Some(def_key) = walk.target.def_key() else {
				return TypeIndex::ERROR;
			};
			let stopped = &segments[walk.stopped_at as usize];
			if let BindingTarget::Inaccessible(_) = walk.target {
				self.diagnostics.push(report_private_identifier(
					&self.defs.namespaces,
					self.strings,
					stopped.ident.inner,
					SourceSpan::new(scope.file_id, stopped.ident.span),
					Some(def_key),
				));
			}

			let resolved = self.resolve_named_type(
				obligations,
				scope,
				def_key,
				stopped,
				infer_policy,
			);

			(resolved, walk.stopped_at as usize + 1)
		};

		// Whatever's left continues through impl dispatch or a
		// bound instead of the scope.namespace graph — `members.rs`'s
		// job, not this module's.
		self.resolve_type_member_path(
			obligations,
			scope,
			current,
			&segments[next..],
			infer_policy,
		)
	}

	/// The type a definition a path stopped at names, with the arguments
	/// written on its segment (`stopped`): a struct, enum, alias, memory,
	/// global or function. Anything else is reported as not a type.
	pub(super) fn resolve_named_type(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		def_key: DefKey,
		stopped: &ast::PathSegment,
		infer_policy: InferPolicy,
	) -> TypeIndex {
		match def_key.symbol_kind(self.defs) {
			// An intrinsic alias takes no arguments: it is a primitive,
			// not an alias with an empty parameter list.
			kind @ DefKind::TypeAlias(type_alias_index)
				if !stopped.type_args.is_empty()
					&& self
						.defs
						.intrinsics
						.identity_of(type_alias_index)
						.is_some() =>
			{
				// Resolved only to report what is wrong inside them.
				for arg in &stopped.type_args {
					self.resolve_type_argument_expression(
						obligations,
						scope,
						arg,
						infer_policy,
					);
				}
				self.diagnostics.push(report_type_args_not_allowed(
					self.strings,
					self.defs,
					scope.file_id,
					stopped,
					TypeArgsNotAllowedOn::Declaration(kind),
				));
				// What it names is unambiguous, so the type is kept.
				self.defs.intrinsics.identity_of(type_alias_index).unwrap()
			}
			DefKind::TypeAlias(type_alias_index) => {
				let def_id = DefId::TypeAlias(type_alias_index);
				let reference =
					SourceSpan::new(scope.file_id, stopped.ident.span);
				let status = self.ensure_signature(QueryInfo {
					def_id,
					requested_at: Some(reference),
				});
				match status {
					SignatureStatus::Cycle => {
						let diagnostic =
							self.report_cyclic_type_alias(def_id, reference);
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
								self.resolve_type_argument_expression(
									obligations,
									scope,
									arg,
									infer_policy,
								)
							})
							.collect();
						let type_args = self.resolve_type_args(
							obligations,
							scope,
							stopped,
							type_params,
							&[],
							&resolved_args,
							TypeEnvOwner::TypeAlias(index),
						);
						self.types.substitute(
							target,
							Substitution {
								envs: &self.type_envs,
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
							scope.file_id,
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
						self.resolve_type_argument_expression(
							obligations,
							scope,
							arg,
							infer_policy,
						)
					})
					.collect();
				let type_args = self.resolve_type_args(
					obligations,
					scope,
					stopped,
					params_env,
					&[],
					&resolved_args,
					TypeEnvOwner::Struct(struct_index),
				);
				self.types.intern_struct(struct_index, &type_args)
			}
			DefKind::Enum(enum_index) => {
				if !stopped.type_args.is_empty() {
					// Resolved only to report what is wrong inside them.
					for arg in &stopped.type_args {
						self.resolve_type_argument_expression(
							obligations,
							scope,
							arg,
							infer_policy,
						);
					}
					self.diagnostics.push(report_type_args_not_allowed(
						self.strings,
						self.defs,
						scope.file_id,
						stopped,
						TypeArgsNotAllowedOn::Declaration(DefKind::Enum(
							enum_index,
						)),
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
			kind @ DefKind::Memory(memory_index) => {
				if stopped.type_args.is_empty() {
					self.types.intern(Type::Memory { memory_index })
				} else {
					// Resolved only to report what is wrong inside them.
					for arg in &stopped.type_args {
						self.resolve_type_argument_expression(
							obligations,
							scope,
							arg,
							infer_policy,
						);
					}
					self.diagnostics.push(report_type_args_not_allowed(
						self.strings,
						self.defs,
						scope.file_id,
						stopped,
						TypeArgsNotAllowedOn::Declaration(kind),
					));
					TypeIndex::ERROR
				}
			}
			kind @ (DefKind::Module(_)
			| DefKind::Package(_)
			| DefKind::PackageInstance(_)
			| DefKind::Import(_)
			| DefKind::Trait(_)
			| DefKind::TypeSet(_)) => {
				self.diagnostics.push(report_not_a_type(
					scope.file_id,
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
							scope.file_id,
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
						self.resolve_type_argument_expression(
							obligations,
							scope,
							arg,
							infer_policy,
						)
					})
					.collect();
				let type_args = self.resolve_type_args(
					obligations,
					scope,
					stopped,
					params_env,
					&[],
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
						self.resolve_type_argument_expression(
							obligations,
							scope,
							arg,
							infer_policy,
						);
					}
					self.diagnostics.push(report_type_args_not_allowed(
						self.strings,
						self.defs,
						scope.file_id,
						stopped,
						TypeArgsNotAllowedOn::Declaration(kind),
					));
					TypeIndex::ERROR
				}
			}
			// Value-tier only — a `Tier::Type` walk
			// can never stop on one of these.
			DefKind::EnumVariant(_) | DefKind::Const(_) => unreachable!(
				"value-tier DefKind from a type-scope.namespace path walk"
			),
			// Never constructed anywhere — associated types are
			// only ever reached through `resolve_type_member_path`'s
			// own `MemberKind::AssociatedType`, never as a
			// top-level scope.namespace symbol.
			DefKind::TraitAssocType(_) => unreachable!(
				"TraitAssocType is never registered as a scope.namespace symbol"
			),
		}
	}

	/// The written arguments for a member function's own parameters. Without
	/// generics of its own the function stores its parent's frame, so it then
	/// takes none.
	pub(super) fn member_function_type_args(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		function: FunctionIdx,
		parent_args: &[TypeIndex],
		segment: &ast::PathSegment,
		infer_policy: InferPolicy,
	) -> Box<[TypeIndex]> {
		let def_id = DefId::Function(function);
		if matches!(self.query_state[&def_id].state, QueryState::Pending) {
			let _ = self.ensure_signature(QueryInfo {
				def_id,
				requested_at: Some(SourceSpan::new(
					scope.file_id,
					segment.ident.span,
				)),
			});
		}
		let type_params = self.functions[usize::from(function)].type_params;
		let own = if type_params != TypeEnvIdx::ROOT
			&& matches!(
				self.type_envs.owner(type_params),
				TypeEnvOwner::Function(owner) if owner == function
			) {
			type_params
		} else {
			TypeEnvIdx::ROOT
		};
		let written: Box<[TypeIndex]> = segment
			.type_args
			.iter()
			.map(|arg| {
				self.resolve_type_argument_expression(
					obligations,
					scope,
					arg,
					infer_policy,
				)
			})
			.collect();
		self.resolve_type_args(
			obligations,
			scope,
			segment,
			own,
			parent_args,
			&written,
			TypeEnvOwner::Function(function),
		)
	}

	/// An associated type declares no generic parameters, so arguments
	/// written on one are reported; they are still lowered, to report what is
	/// wrong inside them too.
	pub(super) fn report_assoc_type_args(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		segment: &ast::PathSegment,
		assoc_type_index: AssocTypeIdx,
		infer_policy: InferPolicy,
	) {
		for arg in &segment.type_args {
			self.resolve_type_argument_expression(
				obligations,
				scope,
				arg,
				infer_policy,
			);
		}
		self.diagnostics.push(report_type_args_not_allowed(
			self.strings,
			self.defs,
			scope.file_id,
			segment,
			TypeArgsNotAllowedOn::Declaration(DefKind::TraitAssocType(
				assoc_type_index,
			)),
		));
	}

	/// Resolve identities and structure without reducing the resulting type.
	/// Member lookup can still normalize a receiver when needed to discover a
	/// member, but stored equality expressions retain symbolic projections.
	fn resolve_type_expression(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		type_expr: &Spanned<ast::TypeExpression>,
		infer_policy: InferPolicy,
	) -> TypeIndex {
		match &type_expr.inner {
			// Reported by the parser.
			ast::TypeExpression::Error => TypeIndex::ERROR,
			ast::TypeExpression::Infer => match infer_policy {
				InferPolicy::Allow => TypeIndex::INFER,
				InferPolicy::Reject(kind) => {
					self.diagnostics.push(report_infer_in_signature(
						scope.file_id,
						type_expr.span,
						kind,
					));
					TypeIndex::ERROR
				}
			},
			ast::TypeExpression::Never => TypeIndex::NEVER,
			ast::TypeExpression::Path(segments) => self.resolve_type_path(
				obligations,
				scope,
				segments,
				infer_policy,
			),
			ast::TypeExpression::Grouped { inner, segments } => {
				// `<T>::Item` — no scope.namespace prefix to consume first
				// (unlike `Path`'s `T::Item`, where `T` might itself be a
				// multi-segment scope.namespace path): `inner` is already a full
				// type expression, so the member walk starts on it directly.
				let current = self.resolve_type_expression(
					obligations,
					scope,
					inner,
					infer_policy,
				);
				self.resolve_type_member_path(
					obligations,
					scope,
					current,
					segments,
					infer_policy,
				)
			}
			ast::TypeExpression::QualifiedPath { root, segments } => {
				let base_ty = self.resolve_type_expression(
					obligations,
					scope,
					&root.self_type,
					infer_policy,
				);
				if base_ty == TypeIndex::ERROR {
					return TypeIndex::ERROR;
				}
				let Some(required_trait) = self.resolve_trait_bound_path(
					scope.file_id,
					scope.namespace,
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
				let Ok(declaration) = self.resolve_trait_qualified_type_member(
					obligations,
					scope.env,
					base_ty,
					required_trait,
					first.ident,
					scope.file_id,
				) else {
					return TypeIndex::ERROR;
				};
				let current = match declaration {
					MemberKind::AssociatedType(assoc_type_index) => {
						if !first.type_args.is_empty() {
							self.report_assoc_type_args(
								obligations,
								scope,
								first,
								assoc_type_index,
								infer_policy,
							);
							return TypeIndex::ERROR;
						}
						self.project_assoc_type(
							base_ty,
							AssocTypeProjectionTarget {
								trait_index: required_trait,
								assoc_type_index,
							},
						)
					}
					// The declaration's own type over `base_ty`, whatever
					// impl `base_ty` has.
					MemberKind::Function(function)
					| MemberKind::Method(function) => {
						let own_args = self.member_function_type_args(
							obligations,
							scope,
							function,
							&[base_ty],
							first,
							infer_policy,
						);
						let mut type_args = vec![base_ty];
						type_args.extend_from_slice(&own_args);
						self.types.intern_function(function, &type_args)
					}
					MemberKind::Constant(_) => {
						unreachable!("a constant is a value member")
					}
				};

				self.resolve_type_member_path(
					obligations,
					scope,
					current,
					&segments[1..],
					infer_policy,
				)
			}
			ast::TypeExpression::Function { params, result } => {
				// One parameter type: a single one is itself, any other count
				// is its tuple (`()` for none).
				let param = if let [param] = &params[..] {
					self.resolve_type_expression(
						obligations,
						scope,
						&param.inner.inner.ty,
						infer_policy,
					)
				} else {
					let mut elements = Vec::with_capacity(params.len());
					for param in params.iter() {
						elements.push(self.resolve_type_expression(
							obligations,
							scope,
							&param.inner.inner.ty,
							infer_policy,
						));
					}
					self.types.intern_tuple(&elements)
				};
				let result_type = match result {
					Some(result) => self.resolve_type_expression(
						obligations,
						scope,
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
					obligations,
					scope,
					inner,
					infer_policy,
				);
				let Ok(memory) = self.resolve_pointer_memory(
					obligations,
					scope,
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
					obligations,
					scope,
					inner,
					infer_policy,
				);
				let Ok(memory) = self.resolve_pointer_memory(
					obligations,
					scope,
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
				length,
			} => {
				let of = self.resolve_type_expression(
					obligations,
					scope,
					inner,
					infer_policy,
				);
				let Ok(memory) = self.resolve_pointer_memory(
					obligations,
					scope,
					memory,
					type_expr.span,
					infer_policy,
				) else {
					return TypeIndex::ERROR;
				};
				let Some(size) = self.array_length(scope, length) else {
					return TypeIndex::ERROR;
				};
				self.types.intern(Type::Array {
					of,
					size,
					memory,
					ownership: *ownership,
				})
			}
			ast::TypeExpression::Tuple { elements } => {
				let mut elems: Vec<TypeIndex> =
					Vec::with_capacity(elements.len());
				for element in elements.iter() {
					elems.push(self.resolve_type_expression(
						obligations,
						scope,
						&element.inner,
						infer_policy,
					));
				}
				// A tuple of one is its element, which interning unwraps.
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
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		bound: Option<&Spanned<ast::BoundExpression>>,
		location: BoundSubject,
		subject: TypeIndex,
		name: SymbolU32,
	) -> (Box<[BoundId]>, BoundClauses) {
		let mut occurrences = Vec::new();
		if let Some(bound) = bound {
			self.collect_bound_occurrences(
				scope.file_id,
				scope.namespace,
				bound,
				&mut occurrences,
			);
		}
		if matches!(location, BoundSubject::Param { .. })
			&& matches!(self.type_envs.owner(scope.env), TypeEnvOwner::Trait(_))
		{
			for occurrence in &occurrences {
				let def_id = self.trait_def_id(occurrence.trait_index);
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
		let traits = self.trait_clauses(subject, &occurrences);
		let provisional = BoundClauses {
			traits,
			equalities: None,
		};
		match location {
			BoundSubject::Param { env, index } => {
				self.param_bounds[usize::from(env)][index].clauses =
					provisional;
			}
			BoundSubject::Assoc(index) => {
				self.assoc_types[usize::from(index)] =
					Some(AssocTypeSignature {
						declared_bounds: Box::new([]),
						clauses: provisional,
						value: None,
					})
			}
		}
		self.fill_source_bounds(obligations, scope, subject, &occurrences);
		let ids: Box<[BoundId]> = occurrences.iter().map(|o| o.id).collect();
		let equalities = self.equality_clauses(subject, &ids, name);
		(
			ids,
			BoundClauses {
				traits,
				equalities: Some(equalities),
			},
		)
	}

	/// The memberships `occurrences` state about `subject`, published before
	/// any equality's value is resolved (`BoundClauses`).
	fn trait_clauses(
		&mut self,
		subject: TypeIndex,
		occurrences: &[BoundOccurrence<'_>],
	) -> ClauseRange<TraitClause> {
		let mut traits = Vec::new();
		for occurrence in occurrences {
			self.collect_trait_clauses(
				&mut traits,
				subject,
				occurrence,
				occurrence.id,
			);
		}
		self.clauses.push_traits(&traits)
	}

	/// The memberships `occurrence` states about `subject`: its trait, its
	/// nested bounds on projections, then the trait's own clauses.
	fn collect_trait_clauses(
		&mut self,
		out: &mut Vec<TraitClause>,
		subject: TypeIndex,
		occurrence: &BoundOccurrence<'_>,
		origin: BoundId,
	) {
		push_trait_clause(
			out,
			TraitClause {
				subject,
				trait_index: occurrence.trait_index,
				source: occurrence.id,
				origin,
			},
		);
		for binding in &occurrence.bindings {
			let BindingOccurrenceKind::Bound(nested) = &binding.kind else {
				continue;
			};
			let projection = binding.target.project(&mut self.types, subject);
			for nested in nested {
				self.collect_trait_clauses(out, projection, nested, origin);
			}
		}
		self.inherit_trait_clauses(out, subject, occurrence.id, origin);
	}

	/// Walks a bound expression exactly once, resolving trait paths,
	/// reserving a `BoundId` per accepted occurrence, and reporting the
	/// "not an associated type"/duplicate-binding diagnostics. The result is
	/// consumed twice — once by `trait_clauses` to publish memberships (no
	/// equality RHS types resolved), once by
	/// `fill_source_bounds` to resolve those RHS types and fill in
	/// `self.bounds` — but which occurrences exist, and which bindings on
	/// them are accepted, is decided exactly once, here. The two former
	/// consumers used to re-walk the raw AST independently and could only be
	/// proven to agree by comparing how many `BoundId`s each had reserved;
	/// walking a shared `BoundOccurrence` tree instead makes that agreement
	/// structural rather than an invariant to maintain by hand.
	fn collect_bound_occurrences<'expr>(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		expr: &'expr Spanned<ast::BoundExpression>,
		out: &mut Vec<BoundOccurrence<'expr>>,
	) {
		let (segments, bindings) = match &expr.inner {
			ast::BoundExpression::BoundList(list) => {
				for entry in list.iter() {
					self.collect_bound_occurrences(
						file_id, namespace, entry, out,
					);
				}
				return;
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
			return;
		};
		let span = SourceSpan::new(file_id, expr.span);
		let id = self.bounds.reserve(trait_index, span);
		let mut occurrence_bindings = Vec::new();
		for binding in bindings.iter() {
			let target = match self.binding_target(
				trait_index,
				binding.name.inner,
				span,
			) {
				MemberLookup::Found(member) => member.assoc_type_declaration(),
				MemberLookup::Ambiguous(candidates) => {
					let diagnostic = report_ambiguous_type_member(
						file_id,
						self.strings,
						self.defs,
						binding.name,
						&candidates,
					)
					.with_note(
						"name the trait that declares it in a bound of its own",
					);
					self.diagnostics.push(diagnostic);
					continue;
				}
				MemberLookup::Error => continue,
				_ => None,
			};
			let Some(target) = target else {
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
					b.target.assoc_type_index == target.assoc_type_index
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
					BindingOccurrenceKind::Equals(ty)
				}
				ast::AssocTypeBindingKind::Bound(rhs) => {
					let mut nested = Vec::new();
					self.collect_bound_occurrences(
						file_id,
						namespace,
						rhs,
						&mut nested,
					);
					BindingOccurrenceKind::Bound(nested)
				}
			};
			occurrence_bindings.push(BindingOccurrence {
				target,
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
	}

	/// Resolves every equality binding's RHS type and fills `self.bounds` at
	/// each occurrence's already-reserved `BoundId`. Run once every sibling
	/// param has provisional memberships published, so an equality RHS can
	/// reference a sibling's associated types.
	/// `subject` is the type the occurrences bound, the `Self` of each trait
	/// they name.
	fn fill_source_bounds(
		&mut self,
		obligations: &mut Vec<Obligation>,
		scope: LexicalScope,
		subject: TypeIndex,
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
							obligations,
							scope,
							ty,
							InferPolicy::Reject(
								InferSignatureKind::AssocTypeBinding,
							),
						);
						let value = Spanned {
							inner: value,
							span: ty.span,
						};
						// The value must be one the trait's associated type
						// can take: `Size = i32` against `type Size:
						// PointerSize` states a fact no impl can satisfy.
						if value.inner != TypeIndex::ERROR {
							self.record_bounds_check(
								obligations,
								scope.env,
								BoundRequirements::AssociatedType {
									declaration: binding
										.target
										.assoc_type_index,
									trait_index: binding.target.trait_index,
									receiver: subject,
								},
								value,
								SourceSpan::new(scope.file_id, ty.span),
								TypeEnvOwner::Trait(binding.target.trait_index),
							);
						}
						BindingRequirement::Equals(value)
					}
					BindingOccurrenceKind::Bound(nested) => {
						let projection =
							binding.target.project(&mut self.types, subject);
						self.fill_source_bounds(
							obligations,
							scope,
							projection,
							nested,
						);
						BindingRequirement::Bound(
							nested.iter().map(|o| o.id).collect(),
						)
					}
				};
				source_bindings.push(SourceAssocBinding {
					target: binding.target,
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

	/// The associated type a binding named `name` in a bound of
	/// `trait_index` constrains: the trait's own, or else the one its
	/// supertraits declare, as `T::Name` selects it (a trait reached twice is
	/// one candidate). Only an associated type is a binding's target, so a
	/// function of the same name is passed over.
	fn binding_target(
		&mut self,
		trait_index: TraitIdx,
		name: SymbolU32,
		reference: SourceSpan,
	) -> MemberLookup {
		let key = BindingKey::ty(name);
		let defs = self.defs;
		let declared = |trait_index| {
			defs.declared_trait_member(trait_index, key)
				.filter(|kind| matches!(kind, MemberKind::AssociatedType(_)))
		};
		if let Some(declaration) = declared(trait_index) {
			return MemberLookup::Found(
				ApplicableMember::AbstractTraitMember {
					trait_index,
					declaration,
				},
			);
		}
		// A trait still being built has no supertraits to read yet; the bound
		// that reached it again reports the cycle.
		let def_id = self.trait_def_id(trait_index);
		if matches!(self.query_state[&def_id].state, QueryState::InProgress) {
			return MemberLookup::Error;
		}
		let Some(env) = self.trait_env(trait_index, reference) else {
			return MemberLookup::Error;
		};
		let own_self = self.type_envs.param_types(env)[0];
		let range = self.param_bounds[usize::from(env)][0].clauses.traits;
		let supertraits = self
			.clauses
			.traits(range)
			.iter()
			.filter(|clause| clause.subject == own_self)
			.map(|clause| clause.trait_index)
			.filter(|&supertrait| declared(supertrait).is_some());
		Self::select_declared_member(self.defs, supertraits, key)
	}

	/// Resolves a bound's own path to the trait it names — shared between a
	/// bare `Trait` bound and `WithBindings`'s left-hand `Trait` part.
	/// `None` if the path failed to resolve to a real trait; already
	/// diagnosed either way, by `resolve_path` itself or by the "expected a
	/// trait" report below.
	pub(super) fn resolve_trait_bound_path(
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
				.with_message("add `(<type>)` here"),
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

fn report_pointer_without_memory(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::PointerWithoutMemory.code())
		.with_message("a pointer type must name its memory")
		.with_label(
			SourceSpan::new(file_id, span)
				.primary_label()
				.with_message("no memory written here"),
		)
		.with_note(
			"write the memory before the sigil: `heap::*T`, or a memory \
			 parameter `Mem::*T`",
		)
}

#[cfg(test)]
pub(super) mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

	use super::*;
	use crate::testing::DiagnosticView;
	use crate::tir::defs::{
		DefinitionRegistry, MemberOwner, Namespace, Scope, UseItemKind,
	};
	use crate::tir::impls::ImplTarget;
	use crate::tir::solver::Verdict;
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
				case.context.strings.resolve(
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
	fn primitive_operators_match_the_stdlib_impls() {
		use crate::tir::operators::{
			Scalar, is_primitive_binary, is_primitive_unary,
		};
		// The compiler builds `PrimitiveBinary`/`PrimitiveUnary` exactly where the stdlib has a
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
					is_primitive_binary(op, scalar.ty()),
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
					is_primitive_unary(op, scalar.ty()),
					"{op:?} on {scalar:?}"
				);
			}
		}
	}

	mod const_initializers {
		use super::*;
		use crate::tir::body::{Body, ElementOrder, ExprIdx, ExprKind};
		use crate::tir::eval::{ConstScalar, ConstValue, ConstValueState};

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
			case.context
				.const_body(index)
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
					ExprKind::Int(value) => value.to_string(),
					ExprKind::Float(value) => format!("{value:?}"),
					ExprKind::Bool(value) => value.to_string(),
					ExprKind::Char(value) => format!("{value:?}"),
					ExprKind::Const {
						constant: index, ..
					} => {
						let name =
							case.defs.constants[usize::from(index)].name.inner;
						case.context.strings.resolve(name).unwrap().to_string()
					}
					ExprKind::NextDiscriminant(index) => {
						let name =
							case.defs.constants[usize::from(index)].name.inner;
						format!(
							"(next {})",
							case.context.strings.resolve(name).unwrap()
						)
					}
					ExprKind::PrimitiveUnary { op, operand } => {
						format!(
							"({} {})",
							op.as_str(),
							render(case, body, operand)
						)
					}
					ExprKind::PrimitiveBinary { op, lhs, rhs } => format!(
						"({} {} {})",
						op.as_str(),
						render(case, body, lhs),
						render(case, body, rhs)
					),
					ExprKind::Call {
						function: method,
						args,
						..
					}
					| ExprKind::AbstractCall { method, args, .. }
					| ExprKind::MethodCall {
						function: method,
						args,
						..
					}
					| ExprKind::AbstractMethodCall { method, args, .. } => {
						let (abstract_call, receiver) = match body.kind(expr) {
							ExprKind::AbstractCall { .. } => (true, None),
							ExprKind::MethodCall { receiver, .. } => {
								(false, Some(receiver))
							}
							ExprKind::AbstractMethodCall {
								receiver, ..
							} => (true, Some(receiver)),
							_ => (false, None),
						};
						let name =
							case.defs.functions[usize::from(method)].name.inner;
						let mut text = format!(
							"({}{}",
							if abstract_call { "abstract " } else { "call " },
							case.context.strings.resolve(name).unwrap()
						);
						let count = case.context.functions[usize::from(method)]
							.param_types
							.len() - usize::from(receiver.is_some());
						for arg in receiver
							.into_iter()
							.chain(arguments(body, count, args))
						{
							text.push(' ');
							text.push_str(&render(case, body, arg));
						}
						text + ")"
					}
					ExprKind::Tuple { elements, .. } => {
						let mut text = "(".to_string();
						for (at, &element) in
							body.args(elements).iter().enumerate()
						{
							if at > 0 {
								text.push_str(", ");
							}
							text.push_str(&render(case, body, element));
						}
						if elements.len() == 1 {
							text.push(',');
						}
						text + ")"
					}
					// A named argument shows the field it gives: `(P y=2:u8)`.
					ExprKind::StructConstructor {
						struct_index,
						fields,
					} => {
						let def = &case.defs.structs[usize::from(struct_index)];
						let strings = &case.context.strings;
						let mut text = format!(
							"({}",
							strings.resolve(def.name.inner).unwrap()
						);
						let (args, order) = match body.kind(fields) {
							ExprKind::Tuple { elements, order }
								if def.field_names.len() != 1 =>
							{
								(body.args(elements).to_vec(), order)
							}
							_ => (vec![fields], ElementOrder::InOrder),
						};
						for (at, &arg) in args.iter().enumerate() {
							text.push(' ');
							if let ElementOrder::Permuted { .. } = order {
								let name = def.field_names[usize::from(
									body.declared_index(order, at),
								)]
								.unwrap()
								.inner;
								text.push_str(strings.resolve(name).unwrap());
								text.push('=');
							}
							text.push_str(&render(case, body, arg));
						}
						text + ")"
					}
					// Function bodies' forms; the typecheck suite renders them.
					kind => format!("{kind:?}"),
				};
				let ty =
					case.context.type_formatter().display_type(body.ty(expr));
				format!("{node}:{ty}")
			}
			/// A call's `args`, the value of `count` parameters, as written:
			/// a tuple of several as its elements, any other value itself.
			fn arguments(
				body: &Body,
				count: usize,
				args: ExprIdx,
			) -> Vec<ExprIdx> {
				match body.kind(args) {
					ExprKind::Tuple { elements, .. } if count != 1 => {
						body.args(elements).to_vec()
					}
					_ => vec![args],
				}
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
					DiagnosticCode::TraitBoundViolation,
				),
				(
					"const A: bool = -true;",
					DiagnosticCode::TraitBoundViolation,
				),
				(
					"const A: u8 = 1; const B: u8 = -A;",
					DiagnosticCode::TraitBoundViolation,
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
					impl Add for V { func add(self: Self, rhs: Self) -> Self { self } }
					impl PartialEq for V { func eq(self: Self, other: Self) -> bool { true } }
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
			assert_eq!(shape(&case, "Z"), "(abstract ne X:V X:V):bool");
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

		/// The one number of `name`'s value.
		fn scalar(case: &TestCase<'_>, name: &str) -> ConstScalar {
			match *value(case, name) {
				[scalar] => scalar,
				ref other => panic!("`{name}` is not one number: {other:?}"),
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
			assert_eq!(scalar(&case, "A"), ConstScalar::u8(255));
			assert_eq!(scalar(&case, "B"), ConstScalar::i8(-128));
			// Truncating division; the remainder has the dividend's sign.
			assert_eq!(scalar(&case, "C"), ConstScalar::i32(-3));
			assert_eq!(scalar(&case, "D"), ConstScalar::i32(-1));
			assert_eq!(scalar(&case, "E"), ConstScalar::u8(254));
			assert_eq!(scalar(&case, "F"), ConstScalar::i8(-1));
			// Bits shifted past the width are dropped, as at runtime.
			assert_eq!(scalar(&case, "G"), ConstScalar::u8(128));
			// A right shift on a signed type is arithmetic.
			assert_eq!(scalar(&case, "H"), ConstScalar::i8(-64));
			assert_eq!(scalar(&case, "I"), ConstScalar::u64(u64::MAX));
			assert_eq!(scalar(&case, "J"), ConstScalar::i64(i64::MIN));
			assert_eq!(scalar(&case, "K"), ConstScalar::u32((6 & 3) | (8 ^ 1)));
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
			assert_eq!(scalar(&case, "A"), ConstScalar::f32(0.1 + 0.2));
			assert_eq!(scalar(&case, "B"), ConstScalar::f64(0.1 + 0.2));
			assert_eq!(scalar(&case, "C"), ConstScalar::bool(true));
			assert_eq!(scalar(&case, "D"), ConstScalar::bool(true));
			// IEEE results are values, not errors.
			assert!(scalar(&case, "E").expect_f64().is_infinite());
		}

		#[test]
		fn a_value_is_held_as_wasm_numbers() {
			use crate::tir::eval::Val;
			test_case!(
				case = &with_std(
					"const A: u8 = 255;
					const B: i8 = -1;
					const C: i64 = -2;
					const D: f32 = 0.5;
					const E: bool = true;
					const F: char = 'a';"
				)
			);
			case.diagnostics().assert_none();
			// Narrow integers, `bool` and `char` are `I32`s; a signed one is
			// sign-extended; a float is its bits.
			for (name, val) in [
				("A", Val::I32(0xFF)),
				("B", Val::I32(u32::MAX)),
				("C", Val::I64(-2i64 as u64)),
				("D", Val::F32(0.5f32.to_bits())),
				("E", Val::I32(1)),
				("F", Val::I32(u32::from('a'))),
			] {
				assert_eq!(scalar(&case, name).val, val, "{name}");
			}
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
			assert_eq!(scalar(&case, "A"), ConstScalar::i32(42));
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
			assert_eq!(scalar(&case, "C"), ConstScalar::bool(false));
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
			assert_eq!(scalar(&case, "A"), ConstScalar::bool(false));
			assert_eq!(scalar(&case, "B"), ConstScalar::bool(false));
		}

		#[test]
		fn a_mismatched_initializer_has_no_value() {
			test_case!(
				case = &with_std(
					"enum E(i32) { A = 1 }
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
			test_case!(case = &with_std("enum E(i32) { A = E::B, B }"));
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
			assert_eq!(scalar(&case, "A"), ConstScalar::bool(false));
			assert_eq!(scalar(&case, "B"), ConstScalar::bool(true));
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
					impl PartialEq for V { func eq(self: Self, other: Self) -> bool { true } }
					const X: V = V();
					const Y: bool = X == X;"
				)
			);
			// `X` has a value; `Y` calls `eq`.
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
			assert_eq!(shape(&case, "Q"), "(Point x:i32 (- x:i32):i32):Point");
			assert_eq!(
				shape(&case, "L"),
				"(Line (Point 0:i32 0:i32):Point P:Point):Line"
			);
			// A struct is its fields' numbers, nested ones flattened.
			let i32s = |values: &[i32]| -> ConstValue {
				values
					.iter()
					.map(|&value| ConstScalar::i32(value))
					.collect()
			};
			assert_eq!(*value(&case, "M"), [ConstScalar::u32(5)]);
			assert_eq!(value(&case, "P"), i32s(&[1, 2]));
			assert_eq!(value(&case, "Q"), i32s(&[3, -3]));
			assert_eq!(value(&case, "L"), i32s(&[0, 0, 1, 2]));
		}

		#[test]
		fn a_construction_gives_every_field_once() {
			use DiagnosticCode::*;
			for (initializer, code) in [
				("const P: Point = Point(1);", ArgumentCountMismatch),
				("const P: Point = Point(1, 2, 3);", ArgumentCountMismatch),
				("const P: Point = Point(1, true);", TypeMistmatch),
				("const P: Point = Point({ x: 1 });", MissingArguments),
				(
					"const P: Point = Point({ x: 1, y: 2, z: 3 });",
					UnknownParameterName,
				),
				(
					"const P: Point = Point({ x: 1, x: 2, y: 3 });",
					DuplicateNamedArgument,
				),
				("const P: Pair = Pair({ a: 1 });", PositionalOnlyCall),
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
		fn a_generic_struct_takes_its_arguments_from_the_expected_type() {
			test_case!(
				case = &with_std(
					"struct Wrapper<T>(T);
					struct Pair<A, B>(first: A, second: B);
					const W: Wrapper<u32> = Wrapper(5);
					const P: Pair<u8, i64> = Pair({ second: -1, first: 2 });
					const N: Pair<Wrapper<u8>, u8> = Pair(Wrapper(1), 2);"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(shape(&case, "W"), "(Wrapper 5:u32):Wrapper<u32>");
			// A field's type is the declared one with the arguments in it.
			assert_eq!(
				shape(&case, "P"),
				"(Pair second=(- 1:i64):i64 first=2:u8):Pair<u8, i64>"
			);
			assert_eq!(
				shape(&case, "N"),
				"(Pair (Wrapper 1:u8):Wrapper<u8> 2:u8):Pair<Wrapper<u8>, u8>"
			);
			assert_eq!(*value(&case, "W"), [ConstScalar::u32(5)]);
			assert_eq!(
				*value(&case, "P"),
				[ConstScalar::u8(2), ConstScalar::i64(-1)]
			);
			assert_eq!(
				*value(&case, "N"),
				[ConstScalar::u8(1), ConstScalar::u8(2)]
			);
		}

		#[test]
		fn a_written_argument_is_used_and_a_written_placeholder_is_taken_from_the_expected_type()
		 {
			test_case!(
				case = &with_std(
					"struct Wrapper<T>(T);
					struct Pair<A, B>(first: A, second: B);
					const W: Wrapper<u32> = Wrapper::<u32>(5);
					const P: Pair<u8, u16> = Pair::<_, u16>(1, 2);
					const N: Wrapper<Pair<u16, u8>> = Wrapper::<Pair<_, u8>>(Pair(1, 2));
					const M: u8 = 7;
					const L: Pair<u8, u8> = Pair::<_, _>(M, 1);"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(shape(&case, "W"), "(Wrapper 5:u32):Wrapper<u32>");
			assert_eq!(shape(&case, "P"), "(Pair 1:u8 2:u16):Pair<u8, u16>");
			// A `_` inside a written argument is filled the same way.
			assert_eq!(
				shape(&case, "N"),
				"(Wrapper (Pair 1:u16 2:u8):Pair<u16, u8>):Wrapper<Pair<u16, u8>>"
			);
			assert_eq!(shape(&case, "L"), "(Pair M:u8 1:u8):Pair<u8, u8>");
			assert_eq!(
				*value(&case, "P"),
				[ConstScalar::u8(1), ConstScalar::u16(2)]
			);
		}

		#[test]
		fn a_generic_construction_is_checked_against_its_arguments() {
			use DiagnosticCode::*;
			for (initializer, codes) in [
				// A field is checked against its substituted type.
				(
					"const W: Wrapper<u8> = Wrapper(300);",
					&[IntegerLiteralOutOfRange][..],
				),
				// Written arguments make the type, which must be the expected.
				(
					"const W: Wrapper<u64> = Wrapper::<u32>(5);",
					&[TypeMistmatch],
				),
				// Nothing gives `T`: one report, not a mismatch as well.
				("const W: u32 = Wrapper(5);", &[TypeAnnotationRequired]),
				// A comparison's operands expect nothing, and a literal alone
				// has no type. The right side expects the left's, which is
				// reported already.
				(
					"const C: bool = Wrapper(1) == Wrapper(2);",
					&[TypeAnnotationRequired],
				),
				// The right side takes the left's type, so `1` is a `u8`.
				(
					"const M: u8 = 1; const C: bool = Wrapper(M) == Wrapper(1);",
					&[TraitBoundViolation],
				),
				// Learned from `M` on both sides: what fails is the operator,
				// which `Wrapper<u8>` does not implement, not the type.
				(
					"const M: u8 = 1; const C: bool = Wrapper(M) == Wrapper(M);",
					&[TraitBoundViolation],
				),
				(
					"const P: Pair<u8, u8> = Pair::<u8>(1, 2);",
					&[TypeArgumentCountMismatch],
				),
				// A written argument is held to its parameter's bounds.
				(
					"const B: u32 = Bounded::<Unit>(Unit());",
					&[TraitBoundViolation, TypeMistmatch],
				),
				// So is one taken from the expected type: the construction
				// proves its own instantiation, as the annotation does.
				(
					"const B: Bounded<Unit> = Bounded::<_>(Unit());",
					&[TraitBoundViolation, TraitBoundViolation],
				),
			] {
				test_case!(
					case = &with_std(&format!(
						"struct Wrapper<T>(T);
						struct Pair<A, B>(first: A, second: B);
						struct Bounded<T: Add>(T);
						struct Unit();
						{initializer}"
					))
				);
				case.diagnostics().assert_codes(codes);
			}
		}

		#[test]
		fn a_tuple_is_its_elements_in_order() {
			test_case!(
				case = &with_std(
					"struct Wrapper<T>(T);
					const T: (u8, u16) = (1, 2);
					const U: () = ();
					const O: (bool,) = (true,);
					const N: ((u8, bool), u8) = ((1, true), 2);
					const W: Wrapper<(u8, bool)> = Wrapper((1, true));"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(shape(&case, "T"), "(1:u8, 2:u16):(u8, u16)");
			assert_eq!(shape(&case, "U"), "():()");
			assert_eq!(shape(&case, "O"), "true:bool");
			assert_eq!(
				shape(&case, "W"),
				"(Wrapper (1:u8, true:bool):(u8, bool)):Wrapper<(u8, bool)>"
			);
			assert_eq!(
				*value(&case, "T"),
				[ConstScalar::u8(1), ConstScalar::u16(2)]
			);
			assert_eq!(*value(&case, "U"), []);
			assert_eq!(*value(&case, "O"), [ConstScalar::bool(true)]);
			// Nested tuples are flattened.
			assert_eq!(
				*value(&case, "N"),
				[
					ConstScalar::u8(1),
					ConstScalar::bool(true),
					ConstScalar::u8(2)
				]
			);
			assert_eq!(
				*value(&case, "W"),
				[ConstScalar::u8(1), ConstScalar::bool(true)]
			);
		}

		#[test]
		fn a_tuple_of_literals_takes_its_type_from_context() {
			use DiagnosticCode::*;
			for (initializer, codes) in [
				("const T: (u8, u16) = (1, 2, 3);", &[TypeMistmatch][..]),
				(
					"const T: (u8, u16) = (256, 2);",
					&[IntegerLiteralOutOfRange],
				),
				// Each element is held to its own position's type.
				("const T: (u8, bool) = (1, 2);", &[UnableToCoerce]),
				(
					"const C: bool = (1, 2) == (3, 4);",
					&[ComparisonTypeAnnotationRequired],
				),
				// `(1, 2)` waits for `(M, M)` to give `T`; what fails is the
				// operator, which `Same<(u8, u8)>` does not implement.
				(
					"const M: u8 = 1;
					const C: bool = Same((1, 2), (M, M)) == Same((M, M), (M, M));",
					&[TraitBoundViolation],
				),
			] {
				test_case!(
					case = &with_std(&format!(
						"struct Same<T>(a: T, b: T);
						{initializer}"
					))
				);
				case.diagnostics().assert_codes(codes);
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
		fn a_pub_memory_or_global_is_reachable_from_outside_its_module() {
			test_case!(
				case = &with_std(
					"mod inner {
						pub memory heap: u32;
						pub global G: u32 = 0;
						pub global mut M: u32 = 0;
					}
					use inner::heap;
					use inner::G;
					use inner::M;"
				)
			);
			case.diagnostics().assert_none();
		}

		#[test]
		fn a_private_memory_or_global_is_hidden_outside_its_module() {
			test_case!(
				case = &with_std(
					"mod inner {
						memory heap: u32;
						global G: u32 = 0;
					}
					use inner::heap;
					use inner::G;"
				)
			);
			let messages: Vec<_> = case
				.context
				.diagnostics
				.iter()
				.map(|diagnostic| diagnostic.message.as_str())
				.collect();
			assert_eq!(
				messages,
				["memory `heap` is private", "global `G` is private"]
			);
		}

		#[test]
		fn a_constant_of_a_struct_containing_itself_is_not_evaluated() {
			test_case!(
				case = &with_std(
					"struct Selfish(s: Selfish);
					const S: Selfish = Selfish(S);"
				)
			);
			// Reported on the struct, and only there.
			case.diagnostics().assert_codes(&[
				DiagnosticCode::RecursiveTypeWithoutIndirection,
			]);
			assert_eq!(state(&case, "S"), &ConstValueState::Poisoned);
		}

		#[test]
		fn a_variant_without_a_value_counts_on_from_the_one_before_it() {
			test_case!(
				case = &with_std(
					"const BASE: i16 = 10;
					enum E(i16) { A = BASE * 2, B, C = -2, D, F }
					const X: E = E::B;"
				)
			);
			case.diagnostics().assert_none();
			assert_eq!(scalar(&case, "E::A"), ConstScalar::i16(20));
			assert_eq!(scalar(&case, "E::B"), ConstScalar::i16(21));
			assert_eq!(scalar(&case, "E::C"), ConstScalar::i16(-2));
			assert_eq!(scalar(&case, "E::D"), ConstScalar::i16(-1));
			assert_eq!(scalar(&case, "E::F"), ConstScalar::i16(0));
			// A value of an enum is held in its repr.
			assert_eq!(scalar(&case, "X"), ConstScalar::i16(21));
			// A written value is checked against the repr; an implicit one is
			// the previous variant's, plus one.
			assert_eq!(shape(&case, "E::A"), "(* BASE:i16 2:i16):i16");
			assert_eq!(shape(&case, "E::B"), "(next A):i16");
		}

		#[test]
		fn the_stdlib_ordering_has_its_written_values() {
			test_case!(case = &with_std(""));
			case.diagnostics().assert_none();
			assert_eq!(scalar(&case, "Ordering::Less"), ConstScalar::i8(-1));
			assert_eq!(scalar(&case, "Ordering::Equal"), ConstScalar::i8(0));
			assert_eq!(scalar(&case, "Ordering::Greater"), ConstScalar::i8(1));
		}

		#[test]
		fn the_first_variant_needs_a_value_to_count_from() {
			test_case!(case = &with_std("enum E(u8) { A, B, C = 1, D }"));
			// Reported once, at `A`; `B` counts on from it and is silent.
			case.diagnostics().assert_codes(&[
				DiagnosticCode::EnumVariantRequiresExplicitValue,
			]);
			assert_eq!(state(&case, "E::A"), &ConstValueState::Poisoned);
			assert_eq!(state(&case, "E::B"), &ConstValueState::Poisoned);
			assert_eq!(scalar(&case, "E::D"), ConstScalar::u8(2));
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
			test_case!(case = &with_std("enum E(u8) { A = 255, B, C }"));
			// `B` owns the overflow; `C` reads a failed value and is silent.
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::ConstEvaluationFailed]);
			let diagnostic = &case.context.diagnostics[0];
			assert_eq!(diagnostic.message, "evaluation of constant `B` failed");
			let source = &with_std("enum E(u8) { A = 255, B, C }");
			assert_eq!(&source[diagnostic.labels[0].range.clone()], "B");
			assert_eq!(state(&case, "E::C"), &ConstValueState::Poisoned);
		}

		#[test]
		fn variants_sharing_a_value_are_reported_once_per_value() {
			let source = with_std(
				"enum E(i32) { F = 7, A = 1, B = 0, C, D = 1, G = 7, H = 2 }",
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
		use crate::tir::bounds::Readiness;
		use crate::tir::types::Substitution;

		fn memberships(
			signatures: &TypeContext<'_, '_, '_>,
			scope: TypeEnvIdx,
		) -> (Readiness, Vec<(TypeIndex, TraitIdx)>) {
			let tables = signatures.clause_tables();
			(
				tables.assumptions_readiness(scope),
				tables.assumed_traits(scope).collect(),
			)
		}

		fn projection(
			case: &mut TestCase,
			base: TypeIndex,
			trait_name: &str,
			member_name: &str,
		) -> TypeIndex {
			let trait_index = case.trait_index(trait_name);
			let name = case.context.strings.get(member_name).unwrap();
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
			let outer_param =
				case.context.type_envs.param_types(outer_scope)[0];
			for (name, own_trait) in [
				("local", Some(local)),
				("sibling", Some(other)),
				("plain", None),
				("unrelated", Some(other)),
			] {
				let name_symbol = case.context.strings.get(name).unwrap();
				let index = case
					.defs
					.functions
					.iter()
					.position(|function| function.name.inner == name_symbol)
					.unwrap();
				let scope = case.context.functions[index].type_params;
				let own_param = own_trait
					.map(|_| case.context.type_envs.param_types(scope)[0]);
				let (readiness, actual) = memberships(&case.context, scope);
				assert_eq!(readiness, Readiness::Ready);
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
				memberships(&case.context, TypeEnvIdx::ROOT);
			assert_eq!(readiness, Readiness::Ready);
			assert!(facts.is_empty());
		}

		#[test]
		fn inherited_and_nested_clauses_keep_subjects_and_provenance() {
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
			let base = case.context.type_envs.param_types(scope)[0];
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
			let (readiness, traits) = memberships(&case.context, scope);
			assert_eq!(readiness, Readiness::Ready);
			assert_eq!(traits.len(), expected.len());
			for membership in &expected {
				assert!(traits.contains(membership));
			}
			let clauses =
				case.context.param_bounds[usize::from(scope)][0].clauses;
			// Each clause names the written bound that states it, whether
			// written here or inherited from a supertrait's declaration.
			for clause in case.context.clauses.traits(clauses.traits) {
				assert_eq!(
					case.context.bounds.trait_index(clause.source),
					clause.trait_index
				);
			}
			let equalities =
				case.context.clauses.equalities(clauses.equalities.unwrap());
			assert_eq!(equalities.len(), 1);
			assert_eq!(equalities[0].projection, value);
			assert_eq!(equalities[0].value, TypeIndex::I32);
			assert!(
				matches!(case.context.bounds.binding(equalities[0].source).kind,
				BindingRequirement::Equals(value) if value.inner == TypeIndex::I32)
			);
		}

		#[test]
		fn associated_declaration_clauses_read_self_through_nested_requirements()
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
			let base = case.context.type_envs.param_types(scope)[0];
			let item = projection(&mut case, base, "Outer", "Item");
			let value = projection(&mut case, item, "Inner", "Value");
			let output = projection(&mut case, value, "Deep", "Output");
			let inner = case.trait_index("Inner");
			let deep = case.trait_index("Deep");
			let outer_env =
				case.context.traits[usize::from(case.trait_index("Outer"))].env;
			let tables = case.context.clause_tables();
			let types = &case.context.types;
			let mut sources = tables.declarations_of(types, item, 128);
			assert_eq!(sources.readiness, Readiness::Ready);
			// `Item`'s declaration first, read with `Self` as `T`.
			let source = sources.next().unwrap();
			let context = source.context.unwrap();
			assert_eq!(context.env, outer_env);
			assert_eq!(context.receiver, base);
			let traits = tables.clauses.traits(source.clauses.traits);
			assert_eq!(traits.len(), 2);
			assert!(
				source.names(types, tables.type_envs, traits[0].subject, item)
					&& traits[0].trait_index == inner
			);
			assert!(
				source.names(types, tables.type_envs, traits[1].subject, value)
					&& traits[1].trait_index == deep
			);
			let equalities = tables
				.clauses
				.equalities(source.clauses.equalities.unwrap());
			assert_eq!(equalities.len(), 1);
			assert!(source.names(
				types,
				tables.type_envs,
				equalities[0].projection,
				output
			));
			let written = equalities[0].value;
			// Then the parameter at the path's root.
			assert!(sources.next().unwrap().context.is_none());
			assert!(sources.next().is_none());
			let value = case.context.types.substitute(
				written,
				Substitution {
					envs: &case.context.type_envs,
					env: context.env,
					args: &[context.receiver],
				},
			);
			assert_eq!(value, base);
		}

		#[test]
		fn implicit_trait_self_comes_first_and_is_no_clause() {
			test_case!(case = "trait Parent {} trait Child: Parent {}");
			assert!(case.context.diagnostics.is_empty());
			let child = case.trait_index("Child");
			let parent = case.trait_index("Parent");
			let scope = case.context.traits[usize::from(child)].env;
			let subject = case.context.type_envs.param_types(scope)[0];
			let (readiness, facts) = memberships(&case.context, scope);
			assert_eq!(readiness, Readiness::Ready);
			assert_eq!(facts, [(subject, child), (subject, parent)]);
			let clauses =
				case.context.param_bounds[usize::from(scope)][0].clauses;
			let traits = case.context.clauses.traits(clauses.traits);
			assert_eq!(traits.len(), 1);
			assert_eq!(traits[0].trait_index, parent);
		}

		#[test]
		fn equality_alternatives_and_conflicts_both_keep_their_values() {
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
			for (name, values) in [
				("ambiguous", None),
				("conflicting", Some([TypeIndex::I32, TypeIndex::U32])),
			] {
				let scope = case.function_signature(name).type_params;
				let base = case.context.type_envs.param_types(scope)[0];
				let expected_subject =
					projection(&mut case, base, "Value", "Item");
				let expected_values = values.map_or_else(
					|| case.context.type_envs.param_types(scope)[1..].to_vec(),
					|values| values.to_vec(),
				);
				let clauses =
					case.context.param_bounds[usize::from(scope)][0].clauses;
				let equalities = case
					.context
					.clauses
					.equalities(clauses.equalities.unwrap());
				assert!(
					equalities
						.iter()
						.all(|clause| clause.projection == expected_subject)
				);
				assert_eq!(
					equalities
						.iter()
						.map(|clause| clause.value)
						.collect::<Vec<_>>(),
					expected_values,
					"{name}"
				);
				assert_ne!(equalities[0].source, equalities[1].source);
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
					let clauses =
						builder.param_bounds[usize::from(scope)][1].clauses;
					builder.param_bounds[usize::from(scope)][1]
						.clauses
						.equalities = None;
					let (readiness, facts) = memberships(builder, scope);
					assert_eq!(readiness, Readiness::Pending);
					assert_eq!(facts[0].1, TraitIdx::new(0));
					builder.param_bounds[usize::from(scope)][1].clauses =
						clauses;
					assert_eq!(
						builder.clause_tables().assumptions_readiness(scope),
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
					let base = builder.type_envs.param_types(scope)[0];
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
						let mut traits = builder
							.clause_tables()
							.declared_traits(&builder.types, item, 128);
						assert_eq!(traits.readiness, Readiness::Pending);
						assert!(traits.next().is_none());
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
					assert_eq!(
						builder
							.clause_tables()
							.declared_traits(&builder.types, item, 128)
							.readiness,
						Readiness::Ready
					);
					builder.assoc_types[usize::from(declaration)]
						.as_mut()
						.unwrap()
						.clauses
						.equalities = None;
					let tables = builder.clause_tables();
					let traits =
						tables.declared_traits(&builder.types, item, 128);
					assert_eq!(traits.readiness, Readiness::Pending);
					assert_eq!(traits.collect::<Vec<_>>(), [TraitIdx::new(0)]);
					assert_eq!(
						tables
							.declared_traits(&builder.types, item, 0)
							.readiness,
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
			let base = case.context.type_envs.param_types(scope)[0];
			let next = projection(&mut case, base, "Node", "Next");
			let next_next = projection(&mut case, next, "Node", "Next");
			let (readiness, facts) = memberships(&case.context, scope);
			assert_eq!(readiness, Readiness::Ready);
			assert_eq!(facts.len(), 1);
			let tables = case.context.clause_tables();
			for subject in [next, next_next] {
				let traits =
					tables.declared_traits(&case.context.types, subject, 128);
				assert_eq!(traits.readiness, Readiness::Ready);
				assert_eq!(traits.collect::<Vec<_>>(), [TraitIdx::new(0)]);
			}
			assert_eq!(
				tables
					.declared_traits(&case.context.types, next_next, 1)
					.readiness,
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
			&mut graph.strings,
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
		files: &'g Files,
		strings: &'g mut StringInterner,
		defs: DefinitionRegistry,
		ast_nodes: Vec<AstEntry<'g>>,
		impl_dispatch: ImplDispatch,
		diagnostics: Vec<Diagnostic<FileId>>,
		resolutions: NameResolutions,
	}

	impl<'g> TestInputs<'g> {
		fn new(graph: &'g mut vfs::CompilationUnit) -> Self {
			let vfs::CompilationUnit {
				files,
				packages,
				strings,
				stdlib_package,
				root_package,
			} = graph;
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				packages,
				files,
				strings,
				&mut diagnostics,
				&mut resolutions,
				*stdlib_package,
				*root_package,
			);
			let impl_dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				strings,
				&defs,
				&ast_nodes,
			);
			Self {
				files,
				strings,
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
		defs: &'a DefinitionRegistry,
		context: TypeContext<'a, 'a, 'a>,
	}

	impl<'a> TestCase<'a> {
		fn new(inputs: &'a mut TestInputs<'_>) -> Self {
			let TestInputs {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			} = inputs;
			let mut context = TypeContext::new(
				diagnostics,
				resolutions,
				strings,
				files,
				defs,
				ast_nodes,
				impl_dispatch,
			);
			context.sweep();
			// The body checker does not cover every form the stdlib's
			// function bodies use yet; what it does not cover is reported as
			// unsupported, which these tests do not concern.
			context.diagnostics.retain(|diagnostic| {
				diagnostic.code.as_deref()
					!= Some(DiagnosticCode::UnsupportedExpression.code())
			});
			Self { defs, context }
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
							.context
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
				self.context.strings,
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
				&self.context.files,
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
				.context
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
				.context
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
				.context
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
			let symbol = self.context.strings.get(name).unwrap();
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
				.context
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
				.context
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

		/// The field types of the struct at `path`, as written.
		fn field_types(&self, path: &str) -> &[TypeIndex] {
			self.context
				.types
				.list(self.struct_signature(path).field_types)
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
			let scope = self.function_signature(path).type_params;
			let ty = self.param_types(path)[index];
			self.normalized(scope, ty)
		}

		/// Like `normalized_param`, but the answer itself: a parameter whose
		/// projection has no value is `Err(SolverError::Poisoned)`.
		fn try_normalized_param(
			&mut self,
			path: &str,
			index: usize,
		) -> Result<TypeIndex, SolverError> {
			let scope = self.function_signature(path).type_params;
			let ty = self.param_types(path)[index];
			self.context.normalize_type_query(scope, ty)
		}

		/// The parameter exactly as written, with its projections unreduced.
		fn is_projection_param(&self, path: &str, index: usize) -> bool {
			matches!(
				self.context.types.resolve(self.param_types(path)[index]),
				Type::AssocTypeProjection { .. }
			)
		}

		/// The return type of the function at `path`, normalized in its scope.
		fn normalized_return(&mut self, path: &str) -> TypeIndex {
			let signature = self.function_signature(path);
			let (scope, ty) = (signature.type_params, signature.return_type);
			self.normalized(scope, ty)
		}

		/// The parameter types of the function at `path`, as written.
		fn param_types(&self, path: &str) -> &[TypeIndex] {
			self.context
				.types
				.list(self.function_signature(path).param_types)
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
		// There is no tuple of one.
		assert_eq!(target("Single"), target("OneTuple"));

		let formatter = case.context.type_formatter();
		for (name, written) in [
			("List", "func(i32, bool) -> i32"),
			("Single", "func(i32) -> ()"),
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
			case = "pub trait Call { type Args; type Result; } pub trait Function: Call {} func f(a: !, b: ()) -> ! { loop {} }"
		);
		case.diagnostics().assert_none();
		let signature = case.function_signature("f");
		assert_eq!(
			case.context.types.list(signature.param_types),
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
		let field_types = case.field_types("Point");
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
		assert_eq!(case.field_types("Pair").len(), 2);
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
		let field_ty = case.field_types("Holder")[0];
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
		let field_ty = case.field_types("Holder")[0];
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
		let field_ty = case.field_types("Holder")[0];
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
			DiagnosticCode::TypeArgumentsNotAllowed,
			DiagnosticCode::TypeArgumentCountMismatch,
		]);
		let params = &case.param_types("f");
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
		let param = case.param_types("f")[0];
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
			.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
		assert_eq!(
			case.context.diagnostics[0].message,
			"type arguments are not allowed on type parameter `T`"
		);
		let param = case.param_types("f")[0];
		assert!(matches!(
			case.context.types.resolve(param),
			Type::TypeParam { .. }
		));
	}

	/// An associated type declares no generic parameters, so arguments on
	/// one are reported in both spellings, and what is written inside them
	/// is still resolved.
	#[test]
	fn type_arguments_on_an_associated_type_are_diagnosed() {
		for path in ["T::Item<u8>", "<T as Iterable>::Item<u8>"] {
			test_case!(
				case = &format!(
					"type u8; trait Iterable {{ type Item; }} func f<T: Iterable>(x: {path}) {{}} pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}"
				)
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
			assert_eq!(
				case.context.diagnostics[0].message,
				"type arguments are not allowed on associated type `Item`"
			);
		}
		test_case!(
			case = "trait Iterable { type Item; } func f<T: Iterable>(x: T::Item<Missing>) {} pub trait Call { type Args; type Result; } pub trait Function: Call {}"
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UndeclaredIdentifier,
			DiagnosticCode::TypeArgumentsNotAllowed,
		]);
	}

	/// Type arguments on a parameter or a trait's `Self` point back at its
	/// declaration: the parameter's name, the trait's for its `Self`.
	#[test]
	fn type_arguments_on_a_parameter_point_at_its_declaration() {
		let call = "pub trait Call { type Args; type Result; } pub trait Function: Call {}";
		for (source, declared, name) in [
			("type u8; func f<T>(x: T<u8>) {}", "f<T", "T"),
			(
				"type u8; trait Tr { func g(x: Self<u8>); }",
				"trait Tr",
				"Tr",
			),
		] {
			let source = format!("{source} {call}");
			test_case!(case = &source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
			// `declared` ends with the declared name.
			let end = source.find(declared).unwrap() + declared.len();
			let label = case.context.diagnostics[0]
				.labels
				.iter()
				.find(|label| label.message.contains("defined here"))
				.expect("the report points at the declaration");
			assert_eq!(label.range, end - name.len()..end, "{source}");
		}
	}

	/// An impl's `Self` already names the target with its arguments, so
	/// arguments on it are their own error: it shows what `Self` is, and
	/// for a struct suggests writing the struct's name instead.
	#[test]
	fn type_arguments_on_an_impls_self_are_their_own_error() {
		let call = "pub trait Call { type Args; type Result; } pub trait Function: Call {}";
		for (source, target, shown, note) in [
			(
				"type u8; struct X<T>(); impl<T> X<T> { func f(x: Self<u8, T>) {} }",
				"X<T> {",
				"`Self` is `X<T>` in this impl",
				true,
			),
			(
				"type u8; trait Tr {} impl Tr for u8 { func f(x: Self<u8>) {} }",
				"u8 {",
				"`Self` is `u8` in this impl",
				false,
			),
		] {
			let source = format!("{source} {call}");
			test_case!(case = &source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
			let diagnostic = &case.context.diagnostics[0];
			let args = source.find("Self<").unwrap() + "Self<".len();
			assert_eq!(diagnostic.labels[0].range.start, args, "{source}");
			let label = diagnostic
				.labels
				.iter()
				.find(|label| label.message == shown)
				.expect("the report shows what `Self` is");
			assert_eq!(
				label.range.start,
				source.find(target).unwrap(),
				"{source}"
			);
			assert_eq!(
				diagnostic.notes.iter().any(|note| note.contains("`X`")),
				note,
				"{source}"
			);
		}
	}

	#[test]
	fn type_arguments_on_self_are_diagnosed() {
		test_case!(
			case = indoc! {"
			type u8;
			trait Tr { func g(x: Self<u8>); }
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
		assert_eq!(
			case.context.diagnostics[0].message,
			"type arguments are not allowed on self type `Self`"
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
			.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
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
			.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
		assert_eq!(
			case.context.diagnostics[0].message,
			"type arguments are not allowed on module `m`"
		);
		let param = case.param_types("f")[0];
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
		let field_ty = case.field_types("Holder")[0];
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
		let field_ty = case.field_types("Holder")[0];
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
		assert_eq!(case.context.types.list(signature.param_types).len(), 2);
		assert_eq!(
			case.context.types.list(signature.param_types)[0],
			TypeIndex::I32
		);
		assert_eq!(
			case.context.types.list(signature.param_types)[1],
			TypeIndex::I32
		);
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
		assert_eq!(
			case.context.types.list(signature.param_types)[0],
			signature.return_type
		);
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

		assert_eq!(case.param_types("f").len(), 2);
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
		assert_eq!(
			case.context.types.list(signature.param_types)[0],
			TypeIndex::I32
		);
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

	/// A free function has no `Self`, so its `self` is reported once, where
	/// it is written, and its type (`Self`, when written alone) is not
	/// resolved again.
	#[test]
	fn self_in_a_free_function_is_reported_once() {
		for source in [
			"func f(self: Self); pub trait Call { type Args; type Result; } pub trait Function: Call {}",
			"func f(mut self: Self); pub trait Call { type Args; type Result; } pub trait Function: Call {}",
		] {
			test_case!(case = source);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::SelfParamPosition]);
		}
	}

	/// A parameter is written like a struct field: a lone identifier is its
	/// type, never a name without one.
	#[test]
	fn a_lone_identifier_parameter_is_its_type() {
		for source in [
			"func f(x) { } pub trait Call { type Args; type Result; } pub trait Function: Call {}",
			"func f(x); pub trait Call { type Args; type Result; } pub trait Function: Call {}",
			"trait Foo { func get(self: Self, x) -> Self; } pub trait Call { type Args; type Result; } pub trait Function: Call {}",
			"struct S(); impl S { func get(self: Self, x) -> Self { self } } pub trait Call { type Args; type Result; } pub trait Function: Call {}",
		] {
			test_case!(case = source);
			let diagnostics = case.diagnostics();
			diagnostics.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
			diagnostics
				.assert_error_saying("cannot find type `x` in this scope");
		}
	}

	#[test]
	fn an_unnamed_parameter_has_its_written_type() {
		test_case!(
			case = indoc! {"
				pub type i32;
				pub type u8;
				func f(i32, _: u8, c: i32);
				pub trait Call { type Args; type Result; }
				pub trait Function: Call {}
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			&*case.param_types("f"),
			&[TypeIndex::I32, TypeIndex::U8, TypeIndex::I32]
		);
		let DefKind::Function(index) = case.resolve(Tier::Value, "f") else {
			panic!("expected a function");
		};
		let names: Vec<_> = case.defs.functions[usize::from(index)]
			.params
			.iter()
			.map(|param| {
				param.map(|name| {
					case.context.strings.resolve(name.inner).unwrap()
				})
			})
			.collect();
		assert_eq!(names, [None, None, Some("c")]);
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
		// Once at the annotation, and once at the construction, which proves
		// its own instantiation as every use does.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
		]);
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
			func f(x: colors::Color) -> Alias { loop {} }
			const FIRST: Alias = colors::Color::Red;
			struct Paint( color: Alias );
			type Alias = colors::Color;
			mod colors { pub enum Color(i32) { Red = 0, Green } }
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
		let ty = case.context.types.list(signature.param_types)[0];
		assert!(
			matches!(case.context.types.resolve(ty), Type::Enum { enum_index: found } if *found == enum_index)
		);
		assert_ne!(ty, TypeIndex::I32);
		assert_eq!(signature.return_type, ty);
		assert_eq!(case.constant_signature("FIRST").ty, ty);
		assert_eq!(case.field_types("Paint"), [ty]);
		assert_eq!(case.type_alias("Alias").target, ty);
		assert_eq!(case.enum_signature("colors::Color").repr, TypeIndex::I32);
	}

	/// An intrinsic type alias is a primitive, not an alias with an empty
	/// parameter list: its arguments are not allowed, and it keeps its type.
	/// A memory takes none either.
	#[test]
	fn builtin_and_memory_types_reject_type_arguments() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			func f(x: u8<u8>, y: heap<u8>) {}
		"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeArgumentsNotAllowed,
			DiagnosticCode::TypeArgumentsNotAllowed,
		]);
		let [builtin, memory] = &case.context.diagnostics[..] else {
			unreachable!()
		};
		assert_eq!(
			builtin.message,
			"type arguments are not allowed on type alias `u8`"
		);
		assert_eq!(
			memory.message,
			"type arguments are not allowed on memory `heap`"
		);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::U8);
	}

	/// An enum never declares parameters, so arguments on it are not
	/// allowed at all: the report marks the arguments, the name, and the
	/// enum's declaration.
	#[test]
	fn enum_types_reject_generic_arguments() {
		let source = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func f(x: Color<i32>, y: nested::Color<i32, i32>) {}
			enum Color(i32) { Red = 0 }
			mod nested { pub enum Color(i32) { Red = 0 } }
		"};
		test_case!(case = source);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeArgumentsNotAllowed,
			DiagnosticCode::TypeArgumentsNotAllowed,
		]);
		for (diagnostic, path, args, plural) in [
			(&case.context.diagnostics[0], "Color", "i32", ""),
			(
				&case.context.diagnostics[1],
				"nested::Color",
				"i32, i32",
				"s",
			),
		] {
			assert_eq!(
				diagnostic.message,
				"type arguments are not allowed on enum `Color`"
			);
			let [arguments, name, declaration] = &diagnostic.labels[..] else {
				panic!("expected three labels: {:?}", diagnostic.labels);
			};
			assert_eq!(&source[arguments.range.clone()], args);
			assert_eq!(
				arguments.message,
				format!("type argument{plural} not allowed")
			);
			assert_eq!(&source[name.range.clone()], "Color");
			assert_eq!(name.message, "not allowed on enum `Color`");
			let DefKind::Enum(index) = case.resolve(Tier::Type, path) else {
				panic!("expected an enum");
			};
			let definition = &case.defs.enums[usize::from(index)];
			assert_eq!(declaration.file_id, definition.file_id);
			assert_eq!(
				declaration.range,
				definition.name.span.start as usize
					..definition.name.span.end as usize
			);
			assert_eq!(declaration.message, "enum `Color` defined here");
		}
	}

	#[test]
	fn enum_type_identity_does_not_force_its_representation_query() {
		with_pending_signatures(
			indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			func f(x: Color) -> Color {}
			enum Color(i32) { Red }
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
					builder.types.resolve(
						builder.types.list(builder.functions[0].param_types)[0]
					),
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
				"enum Color(Color) { Red }",
				DiagnosticCode::EnumReprNotInteger,
			),
			(
				"type Repr = Color; enum Color(Repr) { Red }",
				DiagnosticCode::EnumReprNotInteger,
			),
		] {
			test_case!(
				case = &format!(
					"func f(x: Color) -> Color {{ loop {{}} }} {declaration} pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}"
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
				case.context
					.types
					.resolve(case.context.types.list(signature.param_types)[0]),
				Type::Enum { .. }
			));
			assert_eq!(
				case.context.types.list(signature.param_types)[0],
				signature.return_type
			);
			assert_eq!(case.enum_signature("Color").repr, TypeIndex::ERROR);
		}
	}

	#[test]
	fn an_enum_repr_resolves_to_the_named_integer_type() {
		test_case!(
			case = indoc! {"
			type i32;
			enum Color(i32) { Red = 0, Green, Blue }
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
			enum Color(i32) { Red = 0, Green = 4 }
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
			let signature = &case.context.constants[usize::from(const_index)];
			assert_eq!(
				(signature.ty, signature.env),
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
			enum Color(bool) { Red, Green, Blue }
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
			let (scope, written) = (
				signature.type_params,
				case.context.types.list(signature.param_types)[0],
			);
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
					Verdict::Poisoned
						| Verdict::Overflowed
						| Verdict::Cyclic(_)
				)),
				"{source}"
			);
		}
	}

	#[test]
	fn a_type_with_no_parameter_is_normalized_once_for_every_scope() {
		// `P::Item` means `Q` whatever `f` and `g` assume, so both scopes'
		// requests are one, under the root.
		test_case!(
			mut case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Container { type Item; }
                struct Q();
                struct P();
                impl Container for P { type Item = Q; }
                func f<T: Container>(x: P::Item) {}
                func g<U: Container where { Item = Q }>(x: P::Item) {}
            "}
		);
		case.diagnostics().assert_none();
		let q = case.normalized_param("f", 0);
		assert_eq!(case.normalized_param("g", 0), q);
		let projection = case.param_types("f")[0];
		assert_eq!(
			case.context
				.types
				.list(case.function_signature("g").param_types)[0],
			projection
		);
		let entries = case
			.context
			.solver
			.normalized
			.keys()
			.filter(|normalization| normalization.ty == projection)
			.count();
		assert_eq!(entries, 1);
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
		let written = case.param_types("f")[0];
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
		let written = case.param_types("f")[0];
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
			pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}
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
			.context
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
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
		"},
			|builder| {
				builder.sweep();
				let receiver =
					builder.types.intern_struct(StructIdx::new(0), &[]);
				let trait_index = TraitIdx::new(0);
				// The written impl, after its trait's members' synthetic ones.
				let impl_index = builder
					.ast_nodes
					.iter()
					.find_map(|entry| match entry.node {
						AstNodeRef::TraitImplBlock { block_index, .. } => {
							Some(block_index)
						}
						_ => None,
					})
					.unwrap();
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
						let def =
							&builder.defs.trait_impls[usize::from(impl_index)];
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
							&mut Vec::new(),
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
							&mut Vec::new(),
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
				let (scope, written) = (
					signature.type_params,
					case.context.types.list(signature.param_types)[0],
				);
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
		assert_eq!(case.param_types("f")[0], TypeIndex::ERROR);
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
		assert_eq!(
			case.context.types.list(signature.param_types),
			[TypeIndex::U32]
		);
		assert_eq!(signature.return_type, TypeIndex::U32);
	}

	#[test]
	fn pointer_type_resolves_through_its_memory_tag() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			func f(x: heap::*u32);
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
		let &[param_type] = case.context.types.list(signature.param_types)
		else {
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
	fn pointer_type_without_a_memory_is_diagnosed_with_no_memory_declared() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			func f(x: *u32);
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::PointerWithoutMemory]);
		let DefKind::Function(function_index) = case.resolve(Tier::Value, "f")
		else {
			panic!("expected `f` to be a function");
		};
		let signature = &case.context.functions[usize::from(function_index)];
		assert_eq!(
			case.context.types.list(signature.param_types),
			[TypeIndex::ERROR]
		);
	}

	#[test]
	fn pointer_type_without_a_memory_is_diagnosed_even_with_one_memory() {
		// A sole declared memory is not taken as the default: the memory is
		// always written.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			func f(x: *u32, y: &[u32], z: *[u32; 2]);
		"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::PointerWithoutMemory,
			DiagnosticCode::PointerWithoutMemory,
			DiagnosticCode::PointerWithoutMemory,
		]);
	}

	#[test]
	fn pointer_type_without_a_memory_is_diagnosed_with_several_memories() {
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
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::PointerWithoutMemory]);
	}

	#[test]
	fn slice_and_array_types_resolve_through_their_memory_tag() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			typeset PointerSize { u32 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			func f(s: heap::&[u32], a: heap::*[u32; 4]);
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
		let &[slice_type, array_type] =
			case.context.types.list(signature.param_types)
		else {
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
		let &[param_type] = case.context.types.list(signature.param_types)
		else {
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
		let Type::Pointer { to, memory, .. } =
			case.context.types.resolve(case.param_types("f")[0])
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
		let params = &case
			.context
			.types
			.list(case.function_signature("test").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("unbounded").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("inherited").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("test").param_types);
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
        pub trait Call { type Args; type Result; } pub trait Function: Call {}
        "}
		);
		case.diagnostics().assert_none();
		let params = &case
			.context
			.types
			.list(case.trait_function_signature("Tagged", "test").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("associated").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("bounded").param_types);
		assert_eq!(
			case.context.types.resolve(params[1]),
			&Type::Pointer {
				to: TypeIndex::U8,
				memory: params[0],
				ownership: ast::Ownership::Exclusive
			}
		);
		// `Heap<M>` is not a memory without `M: Memory`: diagnosed, tag kept.
		let Type::Pointer { memory, .. } = case.context.types.resolve(
			case.context
				.types
				.list(case.function_signature("unbounded").param_types)[0],
		) else {
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
		let params = &case
			.context
			.types
			.list(case.function_signature("test").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("test").param_types);
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
			case.context.types.resolve(
				case.context
					.types
					.list(case.function_signature("test").param_types)[0]
			),
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
		let params = &case
			.context
			.types
			.list(case.function_signature("test").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("test").param_types);
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
		let params = &case
			.context
			.types
			.list(case.function_signature("test").param_types);
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
		test_case!(
			case = "trait Foo { func get(self: Self) -> Self; } pub trait Call { type Args; type Result; } pub trait Function: Call {}"
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.trait_function_signature("Foo", "get");
		assert_eq!(case.context.types.list(sig.param_types).len(), 1);
		assert_eq!(
			case.context.types.list(sig.param_types)[0],
			sig.return_type,
			"`self`'s type and a written `Self` return type should be the \
			 exact same TypeParam"
		);
	}

	#[test]
	fn an_untyped_self_param_resolves_to_the_impls_own_concrete_target() {
		test_case!(
			case = indoc! {"
			struct S();
			impl S { func get(self: Self) -> Self { self } }
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
		"}
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.inherent_function_signature("S", "get");
		assert_eq!(case.context.types.list(sig.param_types).len(), 1);
		assert_eq!(
			case.context.types.list(sig.param_types)[0],
			sig.return_type,
			"`self` and a written `Self` return type should both resolve to \
			 the impl's own concrete target"
		);
		assert!(
			matches!(
				case.context
					.types
					.resolve(case.context.types.list(sig.param_types)[0]),
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
	fn trait_impl_methods_and_associated_functions_use_the_concrete_self_type()
	{
		test_case!(
			case = indoc! {"
			trait Service { func get(self: Self) -> Self; func make(x: Self) -> Self; }
			struct S();
			impl Service for S {
				func get(self: Self) -> Self { self }
				func make(x: Self) -> Self { x }
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
			assert_eq!(
				case.context.types.list(signature.param_types),
				[header.target.inner]
			);
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
				func get<U>(self: Self, x: Self::Item, y: U) -> Self;
				func shadow<T>(self: Self, x: T) -> Self;
				const VALUE: Self::Item;
			}
			struct Wrap<T>();
			impl<T: Number> Service for Wrap<T> {
				type Item = T;
				func get<U>(self: Self, x: T, y: U) -> Self { self }
				func shadow<T>(self: Self, x: T) -> Self { self }
				const VALUE: T = 0;
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
		let outer = case.context.type_envs.param_types(header.type_params)[0];
		let get = case.trait_impl_function_signature("Wrap", "Service", "get");
		assert_eq!(
			case.context.types.list(get.param_types)[0],
			header.target.inner
		);
		assert_eq!(case.context.types.list(get.param_types)[1], outer);
		assert_eq!(
			case.context.types.list(get.param_types)[2],
			case.context.type_envs.param_types(get.type_params)[0]
		);
		assert_eq!(get.return_type, header.target.inner);
		assert_eq!(
			case.context.type_envs.parent(get.type_params),
			Some(header.type_params)
		);
		let shadow =
			case.trait_impl_function_signature("Wrap", "Service", "shadow");
		assert_ne!(case.context.types.list(shadow.param_types)[1], outer);
		assert_eq!(
			case.context.types.list(shadow.param_types)[0],
			header.target.inner
		);
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
				func get<U: Container where { Item: Marker }>(self: Self, x: Need<Self::Item>, y: Need<U::Item>);
			}
			struct Wrap<T>();
			impl<T: Marker> Service for Wrap<T> {
				type Item = T;
				func get<U: Container where { Item = i32 }>(self: Self, x: Need<T>, y: Need<U::Item>) {}
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
			case.context.types.list(signature.param_types)[2],
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
				func get<U: Container where { A = Need<U::B>, B = i32 }>(self: Self, x: U::A);
			}
			struct S();
			impl Service for S {
				func get<U: Container where { A = Need<U::B>, B = i32 }>(self: Self, x: U::A) {}
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let signature =
			case.trait_impl_function_signature("S", "Service", "get");
		let (scope, written) = (
			signature.type_params,
			case.context.types.list(signature.param_types)[1],
		);
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
			trait Service { func get(self: Self, x: i32); const VALUE: i32; }
			struct S();
			impl Service for S {
				func get(self: Self, x: Need<i32>) {}
				const VALUE: Need<i32> = Need();
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
		"}
		);
		// Both annotations, and the construction, which proves its own
		// instantiation as every use does.
		assert_eq!(
			case.context.diagnostics.len(),
			3,
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
		for ty in [
			case.context.types.list(signature.param_types)[1],
			constant.ty,
		] {
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
			trait Service { func get(self: Self, x: i32, y: i32) -> i32; const VALUE: i32; }
			struct S();
			impl Service for S {
				func get(self: Self, x, y: _) -> _ {}
				const VALUE: _ = 0;
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
					== Some(DiagnosticCode::UndeclaredIdentifier.code()))
				.count(),
			1,
			"`x` alone is a type"
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
			&case.context.types.list(signature.param_types)[1..],
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
				trait Service { func get(self: Self) -> Self; const VALUE: i32; }
				struct S();
				impl Service for S { func get(self: Self) -> Self { self } const VALUE: i32 = 0; }
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
					let impl_index = usize::from(
						builder
							.ast_nodes
							.iter()
							.find_map(|entry| match entry.node {
								AstNodeRef::TraitImplBlock {
									block_index,
									..
								} => Some(block_index),
								_ => None,
							})
							.unwrap(),
					);
					assert!(builder.trait_impls[impl_index].is_none());
					assert!(matches!(
						builder.ensure_signature(QueryInfo {
							def_id: id,
							requested_at: None
						}),
						SignatureStatus::Available(_)
					));
					assert!(builder.trait_impls[impl_index].is_some());
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
		test_case!(
			case = "trait Foo { func get<T>(self: Self, x: T) -> T; } pub trait Call { type Args; type Result; } pub trait Function: Call {}"
		);

		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		let sig = case.trait_function_signature("Foo", "get");
		assert_eq!(case.context.types.list(sig.param_types).len(), 2);
		assert_eq!(
			case.context.types.list(sig.param_types)[1],
			sig.return_type,
			"the param `x: T` and the `-> T` return type should share one TypeParam"
		);
		assert_ne!(
			case.context.types.list(sig.param_types)[0],
			case.context.types.list(sig.param_types)[1],
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
				func get(self: Self) -> Self;
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
			"`const X: Self` and `func get(self: Self) -> Self` should resolve to \
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
	fn a_where_equality_satisfying_the_declared_bound_is_accepted() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Small {}
			impl Small for u8 {}
			trait Memory { type Size: Small; }
			func f<Mem: Memory where { Size = u8 }>() {}
		"}
		);

		case.diagnostics().assert_none();
	}

	#[test]
	fn a_where_equality_violating_the_declared_bound_is_reported() {
		// The equality cannot vouch for itself: `Mem::Size: Small` and
		// `Mem::Size = i32` do not make `i32: Small`, which only an impl can.
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Small {}
			trait Memory { type Size: Small; }
			func f<Mem: Memory where { Size = i32 }>(x: Mem::Size) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `i32: Small` is not satisfied",
		);
		// The equality is kept as written, and still normalizes.
		let env = case.function_signature("f").type_params;
		assert!(matches!(
			case.declared_bounds(env, 0)[0].bindings[0].kind,
			BindingRequirement::Equals(Spanned {
				inner: TypeIndex::I32,
				..
			})
		));
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
	}

	#[test]
	fn a_where_equality_to_a_parameter_needs_the_bound_written() {
		// An equality does not lend `U` the declared bound: `U: Small` is
		// written, as in Rust, or the equality is reported.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Small {}
			trait Memory { type Size: Small; }
			func bounded<U: Small, Mem: Memory where { Size = U }>() {}
			func unbounded<U, Mem: Memory where { Size = U }>() {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics()
			.assert_error_saying("the trait bound `U: Small` is not satisfied");
	}

	#[test]
	fn a_nested_where_equality_is_checked_against_its_declared_bound() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Small {}
			trait Memory { type Size: Small; }
			trait Owner { type Mem; }
			func f<O: Owner where { Mem: Memory where { Size = i32 } }>() {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `i32: Small` is not satisfied",
		);
	}

	/// As rustc reads `T: Sub<Item = u32>`: a binding names the bound's own
	/// member, or else the one its supertraits declare, as the projection
	/// under the trait that declares it.
	#[test]
	fn a_binding_constrains_a_supertraits_associated_type() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Base { type Item; }
			trait Derived: Base {}
			trait Further: Derived {}
			func direct<T: Derived where { Item = u32 }>(x: T::Item) {}
			func transitive<T: Further where { Item = u32 }>(x: <T as Base>::Item) {}
		"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("direct", 0), TypeIndex::U32);
		assert_eq!(case.normalized_param("transitive", 0), TypeIndex::U32);
	}

	#[test]
	fn a_binding_on_a_supertraits_associated_type_takes_a_nested_bound() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Small {}
			trait Base { type Item; }
			trait Derived: Base {}
			func f<T: Derived where { Item: Small }, U: Small>() {}
			func g<T: Derived where { Item: Small }>() { f::<T, T::Item>(); }
		"}
		);
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_traits_own_associated_type_wins_over_a_supertraits() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Base { type Item; }
			trait Derived: Base { type Item; }
			func f<T: Derived where { Item = u32 }>(
				own: <T as Derived>::Item,
				inherited: <T as Base>::Item,
			) {}
		"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("f", 0), TypeIndex::U32);
		assert!(case.is_projection_param("f", 1));
	}

	/// A function holds its name in the type namespace too, but only an
	/// associated type is a binding's target.
	#[test]
	fn a_binding_passes_over_a_function_of_the_same_name() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Base { type Item; }
			trait Derived: Base { func Item(); }
			func f<T: Derived where { Item = u32 }>(x: <T as Base>::Item) {}
		"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("f", 0), TypeIndex::U32);
	}

	#[test]
	fn a_supertrait_reached_twice_supplies_one_binding_target() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Base { type Item; }
			trait Left: Base {}
			trait Right: Base {}
			trait Both: Left + Right {}
			func f<T: Both where { Item = u32 }>(x: T::Item) {}
		"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("f", 0), TypeIndex::U32);
	}

	#[test]
	fn a_binding_two_supertraits_declare_is_ambiguous() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Left { type Item; }
			trait Right { type Item; }
			trait Both: Left + Right {}
			func f<T: Both where { Item = u32 }>() {}
			func spelled<T: Both + Left where { Item = u32 }>() {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AmbiguousTraitMember]);
		case.diagnostics()
			.assert_error_saying("`Item` is ambiguous between multiple traits");
	}

	/// Both bindings are the projection under `Base`, so they conflict.
	#[test]
	fn a_supertrait_binding_conflicts_with_one_on_the_supertrait() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			type u64;
			trait Base { type Item; }
			trait Derived: Base {}
			func f<T: Derived where { Item = u32 } + Base where { Item = u64 }>() {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateAssocTypeBinding]);
		case.diagnostics().assert_error_saying(
			"`T` requires conflicting bindings for `Base::Item`",
		);
	}

	#[test]
	fn a_binding_no_supertrait_declares_is_not_an_associated_type() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Base { type Item; }
			trait Derived: Base {}
			func f<T: Derived where { Missing = u32 }>() {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::NotATraitMember]);
	}

	/// The lookup does not read a trait still being built; the supertrait
	/// bound that closed the loop reports it, once.
	#[test]
	fn a_binding_in_a_supertrait_cycle_reports_the_cycle_once() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait A: A where { Item = u32 } {}
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
	fn an_associated_type_bound_equality_is_checked_against_its_declared_bound()
	{
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32;
			trait Small {}
			trait Memory { type Size: Small; }
			trait Owner { type Mem: Memory where { Size = i32 }; }
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `i32: Small` is not satisfied",
		);
	}

	#[test]
	fn a_where_equality_that_failed_to_resolve_is_not_checked() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Small {}
			trait Memory { type Size: Small; }
			func f<Mem: Memory where { Size = Missing }>() {}
		"}
		);

		case.diagnostics()
			.assert_absent(DiagnosticCode::TraitBoundViolation);
		assert_eq!(case.context.diagnostics.len(), 1);
	}

	#[test]
	fn a_use_proves_the_equalities_its_bound_states() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u64; type bool;
			trait HasItem { type Item; }
			impl HasItem for u64 { type Item = u8; }
			struct W<T: HasItem where { Item = bool }>();
			struct V<T: HasItem where { Item = u8 }>();
			func f(w: W<u64>, v: V<u64>) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
		case.diagnostics().assert_error_saying(
			"type mismatch resolving `<u64 as HasItem>::Item == bool`",
		);
	}

	#[test]
	fn an_equality_naming_a_sibling_parameter_takes_its_argument() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u64; type bool;
			trait HasItem { type Item; }
			impl HasItem for u64 { type Item = u8; }
			struct W<T: HasItem where { Item = U }, U>();
			func ok(w: W<u64, u8>) {}
			func bad(w: W<u64, bool>) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
		case.diagnostics().assert_error_saying(
			"type mismatch resolving `<u64 as HasItem>::Item == bool`",
		);
	}

	#[test]
	fn a_generic_use_proves_an_equality_from_its_own_assumptions() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type bool;
			trait HasItem { type Item; }
			struct W<T: HasItem where { Item = bool }>();
			func ok<T: HasItem where { Item = bool }>(w: W<T>) {}
			func bad<T: HasItem>(w: W<T>) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
		case.diagnostics().assert_error_saying(
			"type mismatch resolving `<T as HasItem>::Item == bool`",
		);
	}

	#[test]
	fn a_use_proves_a_nested_bound_on_the_projection() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u64; type bool;
			trait HasItem { type Item; }
			trait Outer { type Inner; }
			impl HasItem for u64 { type Item = u8; }
			impl Outer for u8 { type Inner = u64; }
			impl Outer for bool { type Inner = bool; }
			struct W<T: Outer where { Inner: HasItem where { Item = u8 } }>();
			func ok(w: W<u8>) {}
			func bad(w: W<bool>) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `bool: HasItem` is not satisfied",
		);
	}

	#[test]
	fn a_member_function_bound_takes_its_impl_arguments() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u64; type bool;
			trait HasItem { type Item; }
			impl HasItem for u64 { type Item = u8; }
			struct Host<T>();
			impl<T> Host<T> { func f<U: HasItem where { Item = T }>() {} }
			func ok(x: Host<u8>::f<u64>) {}
			func bad(x: Host<bool>::f<u64>) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
		case.diagnostics().assert_error_saying(
			"type mismatch resolving `<u64 as HasItem>::Item == bool`",
		);
	}

	#[test]
	fn a_declared_bound_equality_takes_the_bound_subject_as_self() {
		// `type A: HasItem where { Item = Self::B }`: checking `A = u64` reads
		// `Self` as `T`, so `Item` must be `T::B`.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u64; type bool;
			trait HasItem { type Item; }
			impl HasItem for u64 { type Item = u8; }
			trait Tr { type B; type A: HasItem where { Item = Self::B }; }
			func ok<T: Tr where { A = u64, B = u8 }>() {}
			func bad<T: Tr where { A = u64, B = bool }>() {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
		case.diagnostics().assert_error_saying(
			"type mismatch resolving `<u64 as HasItem>::Item == bool`",
		);
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
				func get(self: Self) -> Self::Value;
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
					*base,
					case.context.types.list(sig.param_types)[0],
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
				func get(self: Self) -> <Self>::Value;
			}
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
				assert_eq!(*base, case.context.types.list(sig.param_types)[0]);
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
		match case.context.types.resolve(case.param_types("f")[0]) {
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
		match case.context.types.resolve(case.param_types("f")[0]) {
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
		assert_eq!(case.param_types("f")[0], TypeIndex::ERROR);
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
			case.context.types.resolve(case.param_types("f")[0]),
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
				case.context
					.types
					.list(case.function_signature(name).param_types)[0],
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
			type Actual = func((Wrapper::Item, Wrapper::Item), heap::*Wrapper::Item) -> Wrapper::Item;
			type Expected = func((i32, i32), heap::*i32) -> i32;
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
		assert_ne!(actual, case.param_types("f")[0]);
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
				Verdict::Overflowed | Verdict::Cyclic(_) => Some(true),
				Verdict::Poisoned => Some(false),
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
				Verdict::Poisoned | Verdict::Overflowed | Verdict::Cyclic(_)
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
				case.context
					.types
					.list(case.function_signature("independent").param_types)[0],
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
						clauses: BoundClauses::NONE,
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
			// A projection at the bottom: a type without one is already normal
			// and spends no budget.
			let mut nested = builder.types.intern(Type::AssocTypeProjection {
				base: TypeIndex::I32,
				trait_index: TraitIdx::new(0),
				assoc_type_index: AssocTypeIdx::new(0),
			});
			for _ in 0..5 {
				nested = builder.types.intern_tuple(&[nested, TypeIndex::I32]);
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
			assert_eq!(case.param_types("f")[0], TypeIndex::ERROR);
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
	fn an_impl_with_an_equality_requirement_gives_its_trait_where_it_holds() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u16; type u64; type bool;
			trait HasItem { type Item; }
			impl HasItem for u64 { type Item = u8; }
			impl HasItem for u16 { type Item = bool; }
			trait Show {}
			struct W<T>();
			impl<T: HasItem where { Item = u8 }> Show for W<T> {}
			struct Need<X: Show>();
			func ok(x: Need<W<u64>>) {}
			func bad(x: Need<W<u16>>) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `W<u16>: Show` is not satisfied",
		);
	}

	#[test]
	fn an_inherent_impl_with_an_equality_requirement_applies_where_it_holds() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u16; type u64; type bool;
			trait HasItem { type Item; }
			impl HasItem for u64 { type Item = u8; }
			impl HasItem for u16 { type Item = bool; }
			struct W<T>();
			impl<T: HasItem where { Item = u8 }> W<T> { func m() {} }
			func ok(x: W<u64>::m) {}
			func bad(x: W<u16>::m) {}
		"}
		);

		// The member is selected by the impl's target; its requirement is
		// then proven at the use.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
		case.diagnostics().assert_error_saying(
			"type mismatch resolving `<u16 as HasItem>::Item == u8`",
		);
	}

	#[test]
	fn an_impl_requirement_proves_a_nested_bound() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u64; type bool;
			trait HasItem { type Item; }
			trait Outer { type Inner; }
			impl HasItem for u64 { type Item = u8; }
			impl Outer for u8 { type Inner = u64; }
			impl Outer for bool { type Inner = bool; }
			trait Show {}
			struct W<T>();
			impl<T: Outer where { Inner: HasItem where { Item = u8 } }> Show for W<T> {}
			struct Need<X: Show>();
			func ok(x: Need<W<u8>>) {}
			func bad(x: Need<W<bool>>) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `W<bool>: Show` is not satisfied",
		);
	}

	#[test]
	fn an_impl_requirement_that_normalizes_through_its_own_impl_terminates() {
		// Proving `S<u8>: Loop` normalizes `<S<u8> as Loop>::Out`, which
		// selects the same impl and asks the same question again.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Loop { type Out; }
			impl Loop for u8 { type Out = u8; }
			struct S<T>();
			impl<T: Loop where { Out = <S<T> as Loop>::Out }> Loop for S<T> {
				type Out = T;
			}
			func f(x: <S<u8> as Loop>::Out) {}
		"}
		);

		// Once, by the impl, at the requirement that names it again; the use
		// and the header's own `<S<T> as Loop>` stay silent.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
		case.diagnostics().assert_error_saying(
			"cycle detected when normalizing `<S<T> as Loop>::Out`",
		);
	}

	#[test]
	fn an_impl_requirement_loop_is_reported_once_whatever_the_source_order() {
		// The use is checked first; the impl's verdict still owns the loop.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			func f(x: <S<u8> as Loop>::Out) {}
			trait Loop { type Out; }
			impl Loop for u8 { type Out = u8; }
			struct S<T>();
			impl<T: Loop where { Out = <S<T> as Loop>::Out }> Loop for S<T> {
				type Out = T;
			}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
		case.diagnostics().assert_error_saying(
			"cycle detected when normalizing `<S<T> as Loop>::Out`",
		);
	}

	#[test]
	fn an_impl_requirement_naming_a_concrete_instantiation_is_owned_by_the_impl()
	 {
		// Only `S<u8>` loops, but judging the impl's own requirements reaches
		// it, so the impl reports it once.
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Loop { type Out; }
			impl Loop for u8 { type Out = u8; }
			struct S<T>();
			impl<T: Loop where { Out = <S<u8> as Loop>::Out }> Loop for S<T> {
				type Out = T;
			}
			func f(x: <S<u8> as Loop>::Out) {}
		"}
		);

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicAssociatedType]);
	}

	#[test]
	fn an_impl_selected_again_for_other_arguments_is_not_a_loop() {
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u64;
			trait Tr { type X; }
			impl Tr for u64 { type X = u8; }
			struct W<T>();
			impl<T: Tr where { X = u8 }> Tr for W<T> { type X = u8; }
			func f(x: <W<W<u64>> as Tr>::X) {}
		"}
		);

		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("f", 0), TypeIndex::U8);
	}

	#[test]
	fn generic_impl_bound_equalities_are_proven_not_assumed() {
		// The impl applies exactly where its equality holds: `Value::Item` is
		// `i32`, `Other::Item` is not.
		test_case!(
			mut case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type i32; type bool;
			trait Source { type Item; }
			trait Container { type Item; }
			struct Value();
			struct Other();
			struct Wrapper<T>();
			impl Source for Value { type Item = i32; }
			impl Source for Other { type Item = bool; }
			impl<T: Source where { Item = i32 }> Container for Wrapper<T> {
				type Item = i32;
			}
			func f(x: <Wrapper<Value> as Container>::Item) {}
			func g(x: <Wrapper<Other> as Container>::Item) {}
		"}
		);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		// Diagnosed; the written projection is kept and has no value.
		assert!(case.is_projection_param("g", 0));
		assert_eq!(
			case.try_normalized_param("g", 0),
			Err(SolverError::Poisoned)
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `Wrapper<Other>: Container` is not satisfied",
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
		let (scope, written) = (
			signature.type_params,
			case.context.types.list(signature.param_types)[0],
		);
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
			case.context.types.resolve(case.param_types("f")[0]),
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
			case.context.types.list(sig.param_types)[0],
			sig.return_type,
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
		assert_eq!(case.param_types("f")[0], TypeIndex::ERROR);
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
		assert_eq!(case.param_types("f")[0], TypeIndex::ERROR);
	}

	/// Verified against real rustc (`trait B: A<X = u32> {}`, `trait C: A<X
	/// = u64> {}`, `func f<T: B + C>() {}`): rejected immediately with
	/// `E0284`, zero uses of `T` anywhere past the bound list — bound
	/// well-formedness is checked once at declaration, not deferred to
	/// first use. wx matches that here (see `ParamBounds::clauses`);
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
		let param_ty = case.param_types("f")[0];
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
		assert_ne!(case.param_types("f")[0], TypeIndex::ERROR);
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
		// Both values stay, so the projection reads as ambiguous.
		assert_eq!(
			equality_values(&case, env),
			[vec![TypeIndex::U32, TypeIndex::U64]]
		);
	}

	/// The values each projection `env`'s first parameter assumes is equal
	/// to, one list per projection, in clause order.
	fn equality_values(
		case: &TestCase,
		env: TypeEnvIdx,
	) -> Vec<Vec<TypeIndex>> {
		let clauses = case.context.param_bounds[usize::from(env)][0].clauses;
		let mut groups: Vec<(TypeIndex, Vec<TypeIndex>)> = Vec::new();
		for clause in
			case.context.clauses.equalities(clauses.equalities.unwrap())
		{
			match groups
				.iter_mut()
				.find(|(projection, _)| *projection == clause.projection)
			{
				Some((_, values)) => values.push(clause.value),
				None => groups.push((clause.projection, vec![clause.value])),
			}
		}
		groups.into_iter().map(|(_, values)| values).collect()
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
			// `Item` keeps its one value; the nested `X` keeps both of its.
			let mut groups = equality_values(&case, env);
			groups.sort();
			assert_eq!(
				groups,
				[vec![TypeIndex::U32], vec![TypeIndex::U32, TypeIndex::U64]],
				"{trait_name}"
			);
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
			let membership = case
				.context
				.clauses
				.traits(bounds.clauses.traits)
				.iter()
				.find(|clause| clause.trait_index == case.trait_index("A"))
				.unwrap();
			assert_eq!(membership.source, bounds.declared_bounds[0]);
			assert_eq!(equality_values(&case, env), [vec![TypeIndex::U32]]);
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
			func structural<T: Pair where { First = (T::First, T::First) }>(x: T::First) {}
		"}
		);
		assert!(
			case.context.diagnostics.is_empty(),
			"{:?}",
			case.context.diagnostics
		);
		for name in ["tautology", "mutual", "structural"] {
			for &ty in case
				.context
				.types
				.list(case.function_signature(name).param_types)
			{
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
				case.context.types.resolve(
					case.context
						.types
						.list(case.function_signature(name).param_types)[0]
				),
				Type::AssocTypeProjection { .. }
			));
		}
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
				let base = builder.type_envs.param_types(env)[0];
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
				let clauses = builder.param_bounds[usize::from(env)][0].clauses;
				builder.param_bounds[usize::from(env)][0].clauses.equalities =
					None;
				assert_eq!(
					builder.normalize_type_query(env, projection),
					Err(SolverError::Pending)
				);
				builder.param_bounds[usize::from(env)][0].clauses = clauses;
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
			case.context.types.resolve(case.param_types("f")[0]),
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
			func f<U: Container where { Item = i32 }, T: Container where { Item = Wrap<(U::Item, i32)> }>(x: T::Item) {}
			func g<T: Container where { Item = Wrap<(U::Item, i32)> }, U: Container where { Item = i32 }>(x: T::Item) {}
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
			let (scope, written) = (
				signature.type_params,
				case.context.types.list(signature.param_types)[0],
			);
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
			assert_eq!(
				case.context.types.list(*elements),
				&[TypeIndex::I32, TypeIndex::I32]
			);
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
		use crate::tir::bounds::Readiness;

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
				let graph = source_graph($source);
				assert_graph_clean(&graph);
				test_case!($case from graph);
			};
			(mut $case:ident = $source:expr $(,)?) => {
				let graph = source_graph($source);
				assert_graph_clean(&graph);
				test_case!(mut $case from graph);
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
			let written = case.context.types.list(signature.param_types)[0];
			let params = case.context.type_envs.param_types(assumption_context);
			let (t, u) = (params[0], params[1]);
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
			assert!(
				memberships(&case.context, assumption_context)
					.contains(&(projection, TraitIdx::new(0)))
			);
			let clauses = case.context.param_bounds
				[usize::from(assumption_context)][0]
				.clauses;
			let equalities =
				case.context.clauses.equalities(clauses.equalities.unwrap());
			assert_eq!(equalities.len(), 1);
			assert_eq!(equalities[0].projection, projection);
			assert_eq!(equalities[0].value, stored);
			let BindingRequirement::Equals(source) =
				case.context.bounds.binding(equalities[0].source).kind
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
			let written = case.context.types.list(signature.param_types)[0];
			// `T::Item` means `Need<i32>`...
			let stored = case.normalized(assumption_context, written);
			let Type::Struct { type_args, .. } =
				case.context.types.resolve(stored)
			else {
				panic!()
			};
			assert_eq!(case.context.types.list(*type_args), &[TypeIndex::I32]);
			// ...while the stored clause keeps `U::Item` symbolic.
			let clauses = case.context.param_bounds
				[usize::from(assumption_context)][0]
				.clauses;
			let clause =
				case.context.clauses.equalities(clauses.equalities.unwrap())[0];
			let (raw, source) = (clause.value, clause.source);
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
		}

		fn memberships(
			registry: &TypeContext<'_, '_, '_>,
			assumption_context: TypeEnvIdx,
		) -> Vec<(TypeIndex, TraitIdx)> {
			let tables = registry.clause_tables();
			assert_eq!(
				tables.assumptions_readiness(assumption_context),
				Readiness::Ready
			);
			tables.assumed_traits(assumption_context).collect()
		}

		#[test]
		fn method_context_keeps_local_evidence_about_an_outer_parameter() {
			checked_case!(mut case = indoc! {"
                trait Outer {}
                trait Marker {}
                trait Container { type Item; }
                struct Host<T>();
                impl<T: Outer> Host<T> {
                    func scoped<U: Container where { Item = T } + Container where { Item: Marker }>(self: Self, x: U::Item) {}
                    func plain(self: Self, x: T) {}
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
						case.context.strings.resolve(def.name.inner)
							== Some(name)
					})
					.unwrap()
			};
			let scoped = function("scoped");
			let plain = function("plain");
			let free = function("free");
			let outer_env =
				case.context.inherent_impls[0].as_ref().unwrap().type_params;
			let outer = case.context.type_envs.param_types(outer_env)[0];
			let assumption_context = case.context.functions[scoped].type_params;
			assert_ne!(
				assumption_context, outer_env,
				"the normalized parameter's owner is not the body's context"
			);
			// `U::Item` is stored as written and means the outer parameter `T`.
			let written = case
				.context
				.types
				.list(case.context.functions[scoped].param_types)[1];
			assert_eq!(case.normalized(assumption_context, written), outer);
			let plain_cx = case.context.functions[plain].type_params;
			assert_eq!(
				plain_cx,
				case.context.inherent_impls[0].as_ref().unwrap().type_params
			);
			let free_cx = case.context.functions[free].type_params;
			assert_eq!(free_cx, TypeEnvIdx::ROOT);
			let local = memberships(&case.context, assumption_context);
			assert!(local.contains(&(outer, TraitIdx::new(0))));
			assert!(local.iter().any(|&(_, index)| index == TraitIdx::new(1)));
			assert_eq!(
				memberships(&case.context, plain_cx),
				vec![(outer, TraitIdx::new(0))]
			);
			assert!(memberships(&case.context, free_cx).is_empty());
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
                    func provided(self: Self, x: Self::Item) {}
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
					case.context.strings.resolve(def.name.inner)
						== Some("provided")
				})
				.unwrap();
			let assumption_context = case.context.functions[index].type_params;
			let self_env = case.context.traits[2].env;
			let trait_self = case.context.type_envs.param_types(self_env)[0];
			assert_eq!(assumption_context, self_env);
			assert_eq!(
				case.context
					.types
					.list(case.context.functions[index].param_types)[0],
				trait_self
			);
			let facts = memberships(&case.context, assumption_context);
			assert!(facts.contains(&(trait_self, TraitIdx::new(2))));
			assert!(facts.contains(&(trait_self, TraitIdx::new(1))));
			let signature = case.function_signature("user");
			let subject = case.context.types.list(signature.param_types)[0];
			let receiver =
				case.context.type_envs.param_types(signature.type_params)[0];
			// `Item`'s declaration states its equality with `Self` read as
			// the receiver.
			let tables = case.context.clause_tables();
			let sources =
				tables.declarations_of(&case.context.types, subject, 128);
			assert_eq!(sources.readiness, Readiness::Ready);
			let mut equalities = Vec::new();
			for source in sources {
				for clause in tables
					.clauses
					.equalities(source.clauses.equalities.unwrap())
				{
					equalities.push((clause.value, source.context.unwrap()));
				}
			}
			assert_eq!(equalities.len(), 1);
			let (value, context) = equalities[0];
			assert_eq!(context.receiver, receiver);
			let rhs = case.context.types.substitute(
				value,
				Substitution {
					envs: &case.context.type_envs,
					env: context.env,
					args: &[context.receiver],
				},
			);
			assert_eq!(rhs, receiver);
		}

		#[test]
		fn satisfaction_overflow_is_diagnosed_when_no_trait_subject_matches() {
			let nested = format!(
				"{}Next = U{}",
				"Next: Node where { ".repeat(16),
				" }".repeat(16)
			);
			let source = format!(
				"trait Node {{ type Next: Node; }} trait Marker {{}} func f<T: Node where {{ {nested} }}, U: Node>(x: T{path}) {{}} pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}",
				path = "::Next".repeat(16)
			);
			with_pending_signatures(&source, |builder| {
				builder.sweep();
				let env = builder.functions[0].type_params;
				let ty =
					builder.types.list(builder.functions[0].param_types)[0];
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
				let graph = source_graph($source);
				assert_graph_clean(&graph);
				test_case!($case from graph);
			};
			(mut $case:ident = $source:expr $(,)?) => {
				let graph = source_graph($source);
				assert_graph_clean(&graph);
				test_case!(mut $case from graph);
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
			assert_eq!(
				case.context.types.list(signature.param_types)[0],
				case.context.types.list(signature.param_types)[1]
			);
			let Type::AssocTypeProjection {
				trait_index,
				assoc_type_index,
				base,
			} = case
				.context
				.types
				.resolve(case.context.types.list(signature.param_types)[0])
			else {
				panic!("ordinary projection expected")
			};
			assert_eq!(*trait_index, TraitIdx::new(0));
			assert_eq!(*assoc_type_index, AssocTypeIdx::new(0));
			assert_eq!(
				*base,
				case.context.type_envs.param_types(signature.type_params)[1]
			);
		}

		#[test]
		fn associated_declaration_bounds_supply_no_members_through_equality() {
			// `Item: Project` belongs to `T::Item`; `Item = U` does not lend it
			// to `U`, so `U::Output` needs `U: Project` written.
			checked_case!(
				case = indoc! {"
                trait Project { type Output; }
                trait Container { type Item: Project; }
                func f<T: Container where { Item = U }, U>(x: U::Output) {}
                func g<T: Container where { Item = U }, U: Project>(x: U::Output) {}
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "}
			);
			case.diagnostics().assert_codes(&[
				DiagnosticCode::NotATraitMember,
				DiagnosticCode::TraitBoundViolation,
			]);
			assert!(
				matches!(case.context.types.resolve(case.context.types.list(case.function_signature("g").param_types)[0]), Type::AssocTypeProjection { trait_index, .. } if *trait_index == TraitIdx::new(0))
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
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
				let name = case.context.strings.get(name).unwrap();
				let index = case
					.defs
					.functions
					.iter()
					.position(|def| def.name.inner == name)
					.unwrap();
				&case.context.functions[index]
			};
			assert_ne!(
				case.context.types.list(signature("scoped").param_types)[0],
				TypeIndex::ERROR
			);
			assert_eq!(
				case.context.types.list(signature("sibling").param_types)[0],
				TypeIndex::ERROR
			);
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
			assert_eq!(case.param_types("f")[1], TypeIndex::I32);
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
		fn a_concrete_equal_subject_takes_no_assumed_trait() {
			// `T::Item = i32` and `T::Item: Project` say nothing about `i32`:
			// only an impl gives a concrete type a trait.
			checked_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Project { type Output; }
                trait Container { type Item; }
                func f<T: Container where { Item = i32 } + Container where { Item: Project }>(x: i32::Output, y: <i32 as Project>::Output) {}
            "}
			);
			case.diagnostics().assert_codes(&[
				DiagnosticCode::NotATraitMember,
				DiagnosticCode::TraitBoundViolation,
			]);
			case.diagnostics().assert_error_saying(
				"the trait bound `i32: Project` is not satisfied",
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
				"pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}} trait Node {{ type Next: Node; }} trait Project {{ type Output; }} func f<T: Node where {{ {nested} }}, U: Node>(x: T{path}) {{}}",
				path = "::Next".repeat(16)
			);
			with_pending_signatures(&source, |builder| {
				let id = DefId::Function(FunctionIdx::new(0));
				let _ = builder.ensure_signature(QueryInfo {
					def_id: id,
					requested_at: None,
				});
				let env = builder.functions[0].type_params;
				let ty =
					builder.types.list(builder.functions[0].param_types)[0];
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
					let receiver = builder.types.list(signature.param_types)[0];
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

	mod value_types {
		use super::*;
		use crate::tir::solver::{LayoutValue, ValType};

		/// The declarations a `ValueType` test builds on, as std writes them.
		fn with_value_type(source: &str) -> String {
			format!(
				"{}\n{source}",
				indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				type u8; type u32; type u64; type f32; type f64;
				typeset PointerSize { u32 }
				trait Memory { type Size: PointerSize; }
				trait ValueType {}
				trait Global { type Value: ValueType; }
				memory heap: u32;
			"}
			)
		}

		/// The layout of the global `name`'s value type.
		fn global_layout(
			case: &mut TestCase<'_>,
			name: &str,
		) -> Option<Box<[LayoutValue]>> {
			let DefKind::Global(global_index) = case.resolve(Tier::Value, name)
			else {
				panic!("expected `{name}` to be a global");
			};
			let declaration = case.defs.globals[usize::from(global_index)]
				.value_assoc_type_index;
			let value = case.context.assoc_types[usize::from(declaration)]
				.as_ref()
				.and_then(|signature| signature.value)
				.expect("a global's value type is resolved");
			case.context
				.value_layout(TypeEnvIdx::ROOT, value)
				.expect("a global's layout is final")
		}

		fn known(values: &[ValType]) -> Option<Box<[LayoutValue]>> {
			Some(
				values
					.iter()
					.map(|&value| LayoutValue::Known(value))
					.collect(),
			)
		}

		#[test]
		fn a_global_of_one_wasm_value_is_accepted() {
			let source = with_value_type(indoc! {"
				struct Meters(u32);
				struct Tagged(u64, ());
				struct Wrap<T>(T);
				enum Small(u8) { A = 0 }
				global int: u32 = 0;
				global float: f64 = 0;
				global newtype: Meters = Meters(0);
				global with_empty: Tagged = Tagged(0, ());
				global tuple: (f32, ()) = (0, ());
				global generic: Wrap<u64> = Wrap(0);
				global variant: Small = Small::A;
				global pointer: heap::&u32 = 0 as heap::&u32;
				global reference: func(u32) -> u32 = loop {};
				global size: <heap as Memory>::Size = 0;
			"});
			test_case!(mut case = &source);
			case.diagnostics().assert_none();
			for (name, layout) in [
				("int", [ValType::I32]),
				("float", [ValType::F64]),
				("newtype", [ValType::I32]),
				("with_empty", [ValType::I64]),
				("tuple", [ValType::F32]),
				("generic", [ValType::I64]),
				("variant", [ValType::I32]),
				("pointer", [ValType::I32]),
				("reference", [ValType::FuncRef]),
				("size", [ValType::I32]),
			] {
				assert_eq!(
					global_layout(&mut case, name),
					known(&layout),
					"{name}"
				);
			}
		}

		#[test]
		fn a_global_of_zero_or_several_wasm_values_is_rejected() {
			let source = with_value_type(indoc! {"
				struct Pair(u32, f64);
				struct Unit();
				global pair: Pair = Pair(0, 0);
				global unit: Unit = Unit();
				global empty: () = ();
				global slice: heap::&[u8] = loop {};
			"});
			test_case!(mut case = &source);
			case.diagnostics().assert_codes(&[
				DiagnosticCode::TraitBoundViolation,
				DiagnosticCode::TraitBoundViolation,
				DiagnosticCode::TraitBoundViolation,
				DiagnosticCode::TraitBoundViolation,
			]);
			assert_eq!(
				global_layout(&mut case, "pair"),
				known(&[ValType::I32, ValType::F64])
			);
			assert_eq!(global_layout(&mut case, "unit"), known(&[]));
			assert_eq!(
				global_layout(&mut case, "slice"),
				known(&[ValType::I32, ValType::I32])
			);
		}

		#[test]
		fn an_abstract_field_is_one_value_when_assumed_a_value_type() {
			let source = with_value_type(indoc! {"
				struct Wrap<T>(T);
				struct Pair<T>(T, T);
				struct Needs<U: ValueType>();
				func bounded<T: ValueType>(x: Needs<Wrap<T>>) {}
				func unbounded<T>(x: Needs<Wrap<T>>) {}
				func two<T: ValueType>(x: Needs<Pair<T>>) {}
			"});
			test_case!(mut case = &source);
			case.diagnostics().assert_codes(&[
				DiagnosticCode::TraitBoundViolation,
				DiagnosticCode::TraitBoundViolation,
			]);
			let scope = case.function_signature("bounded").type_params;
			let parameter = case.context.type_envs.param_types(scope)[0];
			let struct_index = case.struct_index("Wrap");
			let type_args = case.context.types.push_list([&parameter]);
			let wrap = case.context.types.intern(Type::Struct {
				struct_index,
				type_args,
			});
			assert_eq!(
				case.context.value_layout(scope, wrap),
				Ok(Some(Box::from([LayoutValue::Abstract(parameter)])))
			);
		}

		#[test]
		fn an_equality_on_a_global_value_must_be_a_value_type() {
			let source = with_value_type(indoc! {"
				func f<G: Global where { Value = (u32, u32) }>() {}
			"});
			test_case!(case = &source);
			case.diagnostics()
				.assert_error(DiagnosticCode::TraitBoundViolation);
		}
	}

	mod equality_satisfaction {
		use super::*;

		/// A tuple has no impl, so no trait: an assumption about a subject that
		/// means `(i32, i32)` does not make it one, exactly as for a struct.
		#[test]
		fn a_type_no_impl_can_target_takes_no_trait_from_assumptions() {
			for source in [
				"func f<T: Container where { Item = (i32, i32) } + Container where { Item: Marker }>(x: Need<(i32, i32)>) {}",
				"struct P(); func f<T: Container where { Item = P } + Container where { Item: Marker }>(x: Need<P>) {}",
			] {
				let source = format!(
					"pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}} type i32; trait Marker {{}} trait Container {{ type Item; }} struct Need<X: Marker>(); {source}"
				);
				test_case!(case = &source);
				case.diagnostics()
					.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
			}
		}

		/// `V::Item` means `i32`, as `T::Item` does, but `T::Item: Marker` lends
		/// it nothing: what both mean is concrete, and has traits from impls.
		#[test]
		fn an_equal_subject_that_means_a_concrete_type_lends_no_trait() {
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                type i32;
                trait Marker {}
                trait Container { type Item; }
                struct Need<X: Marker>();
                func f<
                    T: Container where { Item = i32 } + Container where { Item: Marker },
                    V: Container where { Item = i32 },
                >(x: Need<V::Item>) {}
            "}
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		}

		#[test]
		fn a_projection_out_of_a_concrete_type_takes_no_trait_from_assumptions()
		{
			// `<P as Container>::Item` is `Q`, whatever the scope assumes of a
			// subject equal to it; `Q` is not `Marker`.
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Container { type Item; }
                struct Q();
                struct P();
                impl Container for P { type Item = Q; }
                struct Need<X: Marker>();
                func f<
                    T: Container where { Item = P::Item } + Container where { Item: Marker },
                >(x: Need<P::Item>) {}
            "}
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		}

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
				&[case.context.type_envs.param_types(scope)[1]]
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
					let written = builder.types.list(signature.param_types)[0];
					let u = builder.type_envs.param_types(env)[1];
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
		fn associated_declaration_bounds_do_not_follow_a_written_equality() {
			// Both requirements on `U` fail: the equality's own, against
			// `Item`'s declared bound, and `Need`'s.
			test_case!(
				case = indoc! {"
                pub trait Call { type Args; type Result; } pub trait Function: Call {}
                trait Marker {}
                trait Container { type Item: Marker; }
                struct Need<X: Marker>();
                func f<T: Container where { Item = U }, U>(x: Need<U>) {}
                func g<T: Container where { Item = U }, U: Marker>(x: Need<U>) {}
            "}
			);
			case.diagnostics().assert_codes(&[
				DiagnosticCode::TraitBoundViolation,
				DiagnosticCode::TraitBoundViolation,
			]);
			case.diagnostics().assert_error_saying(
				"the trait bound `U: Marker` is not satisfied",
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
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
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
            pub trait Call { type Args; type Result; } pub trait Function: Call {}
            "}
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
			let sibling = case.context.strings.get("sibling").unwrap();
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
					let ty = builder.type_envs.param_types(env)[1];
					let clauses =
						builder.param_bounds[usize::from(env)][0].clauses;
					builder.param_bounds[usize::from(env)][0]
						.clauses
						.equalities = None;
					assert_eq!(
						builder
							.find_trait_impl_query(env, ty, TraitIdx::new(0))
							.map(|found| found.is_some()),
						Err(SolverError::Pending)
					);
					builder.param_bounds[usize::from(env)][0].clauses = clauses;
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
			// A projection at the bottom: a type without one is already normal
			// and spends no budget.
			let nested =
				format!("{}U::Item{}", "Wrap<".repeat(16), ">".repeat(16));
			let source = format!(
				"trait Marker {{}} trait Container {{ type Item; }} struct Wrap<X>(); func f<T: Container where {{ Item = {nested} }} + Container where {{ Item: Marker }}, U: Container>() {{}} pub trait Call {{ type Args; type Result; }} pub trait Function: Call {{}}"
			);
			with_pending_signatures(&source, |builder| {
				builder.sweep();
				let env = builder.functions[0].type_params;
				let ty = builder.type_envs.param_types(env)[1];
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
                func bad<T: Container where { Item = Need<U::Item> }, U: Container where { Item = i32 }>(x: T::Item, y: i32) -> i32 { loop {} }
            "}
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
			let signature = case.function_signature("bad");
			assert_eq!(
				case.context.types.list(signature.param_types)[1],
				TypeIndex::I32
			);
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
			let clauses = case.context.param_bounds
				[usize::from(signature.type_params)][0]
				.clauses;
			let clause =
				case.context.clauses.equalities(clauses.equalities.unwrap())[0];
			let Type::Struct { type_args, .. } =
				case.context.types.resolve(clause.value)
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
                func bad<T: Container where { Item = Need<U::Item> }, U: Container where { Item = i32 }>(x: (T::Item, i32), y: func(i32) -> T::Item) -> func(T::Item) -> i32 { loop {} }
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
					case.context.types.list(signature.param_types)[0],
					case.context.types.list(signature.param_types)[1],
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
                impl Container for i32 { type Item = Node<i32>; }
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
                impl Container for i32 { type Item = Node<i32>; }
                struct Node<T: Marker + Container where { Item = Node<i32> }>();
            "}
			);
			// Once per use of `Node<i32>`: the impl's value and the bound's own.
			case.diagnostics().assert_codes(&[
				DiagnosticCode::TraitBoundViolation,
				DiagnosticCode::TraitBoundViolation,
			]);
			case.diagnostics().assert_error_saying(
				"the trait bound `i32: Marker` is not satisfied",
			);
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
                func outer<A: Container where { Item = Inner<B, C> }, B: Container where { Item = Need<i32> }, C: Container where { Item = i32 }>(x: A::Item) {}
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
				[&case.context.strings.get(external).unwrap()];
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
			case.context.exports[&case.context.strings.get("f").unwrap()],
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
			case.context.exports[&case.context.strings.get("run").unwrap()],
			ExportedItem::Function(function)
		);
		assert_eq!(
			case.context.exports[&case.context.strings.get("heap").unwrap()],
			ExportedItem::Memory(memory)
		);
		assert_eq!(
			case.context.exports[&case.context.strings.get("counter").unwrap()],
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
			&case.defs.exports[&case.context.strings.get("run").unwrap()];
		assert_eq!(export.name.inner, case.context.strings.get("f").unwrap());
		assert!(
			case.defs
				.namespaces
				.symbols(Namespace::Package(dep))
				.bindings
				.get(&BindingKey::value(
					case.context.strings.get("run").unwrap()
				))
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
            enum E(i32) { A = 0 }
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
			func id<T>(x: T) -> T { loop {} }
			func takes(g: counter, f: id<i32>, me: takes) {}
			func bare(f: id) {}
			func applied(g: counter<i32>) {}
		"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentsNotAllowed,
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
		let params = &case
			.context
			.types
			.list(case.function_signature("takes").param_types);
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
			func one(x: i32) -> bool { loop {} }
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
			func id<T>(x: T) -> T { loop {} }
			func f(x: id<i32>::Args, y: <id<i32> as Call>::Result) {}
		"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::I32);
	}

	/// A method is its own type like a free function, and `self` is its
	/// first argument: `Point::at` takes `(Point, i32)`.
	#[test]
	fn a_member_function_type_implements_call_with_self_in_its_args() {
		test_case!(
			mut case = indoc! {"
			type i32;
			type bool;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			struct Point();
			impl Point {
				func at(self: Self, x: i32) -> bool { loop {} }
				func origin() -> Point { loop {} }
			}
			func f(a: Point::at::Args, b: Point::at::Result, c: Point::origin::Args) {}
		"}
		);
		case.diagnostics().assert_none();
		let point = case
			.context
			.types
			.intern_struct(case.struct_index("Point"), &[]);
		let args = case.context.types.intern_tuple(&[point, TypeIndex::I32]);
		assert_eq!(case.normalized_param("f", 0), args);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::BOOL);
		assert_eq!(case.normalized_param("f", 2), TypeIndex::UNIT);
	}

	/// A member's type takes its parent's parameters ahead of its own, so
	/// `Wrap<i32>::get<bool>` substitutes both.
	#[test]
	fn a_member_function_types_arguments_cover_its_parents_parameters() {
		test_case!(
			mut case = indoc! {"
			type i32;
			type bool;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			struct Wrap<T>();
			impl<T> Wrap<T> {
				func get<U>(self: Self, u: U) -> T { loop {} }
			}
			func f(a: Wrap<i32>::get<bool>::Args, b: Wrap<i32>::get<bool>::Result) {}
		"}
		);
		case.diagnostics().assert_none();
		let wrap = case
			.context
			.types
			.intern_struct(case.struct_index("Wrap"), &[TypeIndex::I32]);
		let args = case.context.types.intern_tuple(&[wrap, TypeIndex::BOOL]);
		assert_eq!(case.normalized_param("f", 0), args);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::I32);
	}

	/// A trait's function is its declaration over `Self`, concrete or not:
	/// `Point::make` and `<Point as Make>::make` are both `make<Point>`, and
	/// normalization never swaps in the impl's member. What it takes and
	/// returns is the declaration's signature with `Self` substituted.
	#[test]
	fn a_trait_function_stays_its_declaration_over_self() {
		test_case!(
			mut case = indoc! {"
			type i32;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Make {
				func make(x: i32) -> Self;
				func fresh() -> Self { loop {} }
			}
			struct Point();
			impl Make for Point { func make(x: i32) -> Point { loop {} } }
			func direct(x: Point::make, y: Point::fresh::Result) {}
			func qualified(
				x: <Point as Make>::make,
				y: <Point as Make>::fresh,
				z: <Point as Make>::make::Args,
			) {}
			func generic<T: Make>(x: T::make, y: T::make::Result) {}
		"}
		);
		case.diagnostics().assert_none();
		let declaration = |name| {
			let name = case.context.strings.get(name).unwrap();
			FunctionIdx::new(
				u32::try_from(
					case.defs
						.functions
						.iter()
						.position(|definition| {
							definition.name.inner == name
								&& matches!(
									definition.owner,
									MemberOwner::Trait(_)
								)
						})
						.unwrap(),
				)
				.unwrap(),
			)
		};
		let (make, fresh) = (declaration("make"), declaration("fresh"));
		let point = case
			.context
			.types
			.intern_struct(case.struct_index("Point"), &[]);
		let make_point = case.context.types.intern_function(make, &[point]);
		let fresh_point = case.context.types.intern_function(fresh, &[point]);
		assert_eq!(case.normalized_param("direct", 0), make_point);
		assert_eq!(case.normalized_param("direct", 1), point);
		assert_eq!(case.normalized_param("qualified", 0), make_point);
		assert_eq!(case.normalized_param("qualified", 1), fresh_point);
		assert_eq!(case.normalized_param("qualified", 2), TypeIndex::I32);
		assert_eq!(
			case.context.type_formatter().display_type(make_point),
			"<Point as Make>::make"
		);
		let env = case.function_signature("generic").type_params;
		let t = case.context.type_envs.param_types(env)[0];
		let make_t = case.context.types.intern_function(make, &[t]);
		assert_eq!(case.normalized_param("generic", 0), make_t);
		assert_eq!(case.normalized_param("generic", 1), t);
	}

	/// An associated function's own arguments follow its receiver's:
	/// `Foo<i32>::new<u8>` is `new<i32, u8>`. A trait member's follow `Self`:
	/// `Wrap<i32>::make<u8>` is `make<Wrap<i32>, u8>`.
	#[test]
	fn member_functions_take_their_own_type_arguments_after_the_receivers() {
		test_case!(
			mut case = indoc! {"
			type i32;
			type u8;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			struct Foo<T>();
			impl<T> Foo<T> { func new<U>(x: U) -> T { loop {} } }
			trait Make { func make<U>(x: U) -> Self; }
			struct Wrap<T>();
			impl<T> Make for Wrap<T> { func make<U>(x: U) -> Wrap<T> { loop {} } }
			func f(
				a: Foo<i32>::new<u8>::Args,
				b: Foo<i32>::new<u8>::Result,
				c: Wrap<i32>::make<u8>::Args,
				d: <Wrap<i32> as Make>::make<u8>::Result,
			) {}
		"}
		);
		case.diagnostics().assert_none();
		let wrap = case
			.context
			.types
			.intern_struct(case.struct_index("Wrap"), &[TypeIndex::I32]);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::U8);
		assert_eq!(case.normalized_param("f", 1), TypeIndex::I32);
		assert_eq!(case.normalized_param("f", 2), TypeIndex::U8);
		assert_eq!(case.normalized_param("f", 3), wrap);
	}

	/// As in value lookup, an inherent function wins over a trait's of the
	/// same name; the trait's stays reachable qualified.
	#[test]
	fn an_inherent_function_takes_precedence_over_a_traits_in_a_type() {
		test_case!(
			mut case = indoc! {"
			type i32;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Make { func make() -> Self; }
			struct Point();
			impl Point { func make() -> i32 { loop {} } }
			impl Make for Point { func make() -> Point { loop {} } }
			func f(x: Point::make::Result, y: <Point as Make>::make::Result) {}
		"}
		);
		case.diagnostics().assert_none();
		let point = case
			.context
			.types
			.intern_struct(case.struct_index("Point"), &[]);
		assert_eq!(case.normalized_param("f", 0), TypeIndex::I32);
		assert_eq!(case.normalized_param("f", 1), point);
	}

	/// Inherent impls of one type constructor are separate sources of
	/// members for it, whatever their targets' arguments, so a name two of
	/// them declare is one duplicate definition, however many tiers the
	/// member is bound in.
	#[test]
	fn a_member_two_inherent_impls_declare_is_one_duplicate() {
		for second in ["func get() {}", "const get: i32 = 0;"] {
			test_case!(
				case = &format!(
					"type i32; type u8; pub trait Call {{ type Args; type Result; }} \
					pub trait Function: Call {{}} struct Wrap<T>(); \
					impl Wrap<i32> {{ func get() {{}} }} impl Wrap<u8> {{ {second} }}"
				)
			);
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
		}
	}

	/// The inherent impl matched for a member's type supplies its leading
	/// arguments, so its bounds on them are checked where it is written.
	#[test]
	fn an_inherent_impls_bounds_apply_to_its_members_type() {
		test_case!(
			case = indoc! {"
			type i32;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Marker {}
			struct Wrap<T>();
			impl<T: Marker> Wrap<T> { func get() {} }
			func f(x: Wrap<i32>::get) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
	}

	/// A function and an associated type are both type members, so two
	/// bounds that each declare the name make it ambiguous.
	#[test]
	fn a_function_and_an_associated_type_of_one_name_are_ambiguous() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait A { func f(); }
			trait B { type f; }
			func g<T: A + B>(x: T::f) {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AmbiguousTraitMember]);
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
			func f() -> f::Result { loop {} }
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
				func call(self: Self, args: Self::Args) -> Self::Result;
			}
			pub trait Function: Call {}
			struct Adder(value: i32);
			impl Call for Adder {
				type Args = i32;
				type Result = i32;
				func call(self: Self, args: Self::Args) -> Self::Result { loop {} }
			}
			func handler(x: i32) -> i32 { loop {} }
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
			impl<T> Wrap<T> { func get(self: Self) -> Self { loop {} } }
			impl Plain { func get(self: Self) -> Self { loop {} } }
			impl Service for Plain { func make() -> Self { loop {} } }
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
		assert!(
			case.context
				.type_envs
				.param_types(plain.type_params)
				.is_empty()
		);
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
				// `self: Self` and `-> Self` in each inherent impl.
				Some(Referent::InherentImplSelf(
					case.inherent_impl_index("Wrap")
				)),
				Some(Referent::InherentImplSelf(
					case.inherent_impl_index("Wrap")
				)),
				Some(Referent::InherentImplSelf(
					case.inherent_impl_index("Plain")
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

	/// A method's chain is the impl's frame, then its own: one flat argument
	/// list `[T, U]` instantiates both, an outer frame alone instantiates
	/// only its own parameters, and another declaration's are never touched.
	#[test]
	fn substitution_and_matching_cover_a_methods_whole_chain() {
		test_case!(
			mut case = indoc! {"
			type i32;
			type bool;
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Number {}
			impl Number for i32 {}
			struct Wrap<T>();
			impl<T: Number> Wrap<T> { func get<U>(self: Self, x: T, y: U) -> (T, U) { loop {} } }
			func free<V>(v: V) {}
			trait Service { func make<W>(w: W) -> Self; }
		"}
		);
		case.diagnostics().assert_none();
		let get = case.inherent_function_signature("Wrap", "get");
		let (method, pair) = (get.type_params, get.return_type);
		let outer = case.context.inherent_impls
			[usize::from(case.inherent_impl_index("Wrap"))]
		.as_ref()
		.unwrap()
		.type_params;
		let free = case.function_signature("free").type_params;
		let make = case.trait_function_signature("Service", "make").type_params;
		let envs = &case.context.type_envs;
		let t = envs.param_types(outer)[0];
		let u = envs.param_types(method)[0];
		let v = envs.param_types(free)[0];

		// Counts: rustc's `parent_count`, and the whole chain's length.
		assert_eq!(envs.parent(method), Some(outer));
		for (env, parent_count, generic_count) in [
			(TypeEnvIdx::ROOT, 0, 0),
			(outer, 0, 1),
			(method, 1, 2),
			(free, 0, 1),
			(make, 1, 2),
		] {
			assert_eq!(envs.parent_count(env), parent_count);
			assert_eq!(envs.generic_count(env), generic_count);
		}

		let types = &mut case.context.types;
		let (i32_, bool_) = (TypeIndex::I32, TypeIndex::BOOL);
		let triple = types.intern_tuple(&[t, u, v]);
		let full = types.substitute(
			triple,
			Substitution {
				envs,
				env: method,
				args: &[i32_, bool_],
			},
		);
		assert_eq!(full, types.intern_tuple(&[i32_, bool_, v]));
		let partial = types.substitute(
			pair,
			Substitution {
				envs,
				env: outer,
				args: &[i32_],
			},
		);
		assert_eq!(partial, types.intern_tuple(&[i32_, u]));

		// Matching fills the same flat slots; a parameter outside the chain
		// is an ordinary identity.
		let concrete = types.intern_tuple(&[i32_, bool_]);
		assert_eq!(
			types
				.match_impl_target(pair, concrete, envs, method)
				.as_deref(),
			Some(&[i32_, bool_][..])
		);
		let repeated = types.intern_tuple(&[t, u, t]);
		let consistent = types.intern_tuple(&[i32_, bool_, i32_]);
		let inconsistent = types.intern_tuple(&[i32_, bool_, bool_]);
		assert!(
			types
				.match_impl_target(repeated, consistent, envs, method)
				.is_some()
		);
		assert!(
			types
				.match_impl_target(repeated, inconsistent, envs, method)
				.is_none()
		);
		assert!(
			types
				.match_impl_target(pair, concrete, envs, outer)
				.is_none()
		);
		let half = types.intern_tuple(&[i32_, u]);
		assert_eq!(
			types.match_impl_target(pair, half, envs, outer).as_deref(),
			Some(&[i32_][..])
		);

		// Bounds are checked in each parameter's own frame: `T: Number`
		// against the outer argument, nothing against `U`.
		let impl_kind = case
			.context
			.type_envs
			.enclosing_impl(method)
			.expect("the method is inside an impl");
		let swapped = case.context.types.intern_tuple(&[bool_, i32_]);
		assert_eq!(
			case.context
				.match_impl_target_and_bounds(
					TypeEnvIdx::ROOT,
					impl_kind,
					method,
					pair,
					concrete,
				)
				.unwrap()
				.as_deref(),
			Some(&[i32_, bool_][..])
		);
		assert_eq!(
			case.context.match_impl_target_and_bounds(
				TypeEnvIdx::ROOT,
				impl_kind,
				method,
				pair,
				swapped,
			),
			Ok(None)
		);
	}
}
