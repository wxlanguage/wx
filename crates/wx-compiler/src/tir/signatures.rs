//! Phase 2, first slice — generic-parameter declarations and their trait
//! bounds: `<T: Add>` in `fn f<T: Add>(...)`, `struct S<T>`, `impl<T> ...`.
//!
//! Type parameters live here, not in `defs.rs`, on purpose: unlike a
//! struct/function/trait name, a type parameter is never reachable by a
//! path written anywhere outside its own declaration — nobody writes
//! `foo::T`. It's scoped to the item that declares it, exactly like a
//! function parameter name, which was never a `defs.rs` citizen either.
//! Keeping the name, its uniqueness check, its accesses, and its resolved
//! bounds together in one struct here also avoids the alternative: two
//! parallel arrays (one in `defs.rs` for names, one here for bounds)
//! index-aligned across two files, which is exactly the kind of "two copies
//! of one fact able to drift" shape the rest of this codebase avoids.
//!
//! `defs.rs`'s own two previous exceptions — `TraitDef::self_param` and
//! `TraitImplDef`/`InherentImplDef::type_params` — were removed in favor of
//! this module for the same reason.

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{self, DefId, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::index::index_newtype;
use crate::vfs::{FileId, PackageId};

use super::defs::{
	AstEntry, AstNodeRef, BindingKey, BindingNamespace, DefKind,
	DefinitionRegistry, EnumIndex, InherentImplIndex, MemberKind,
	NamespaceIndex, NamespaceKind, StructIndex, TraitImplIndex, TraitIndex,
	TypeSetIndex,
};
use super::impls::ImplTarget;
use super::paths::PathResolver;
use super::types::{Type, TypeIndex, TypeInterner};

/// One `<T: Bound1 + Bound2>` declaration — name, resolved bounds, and
/// reference tracking all together (see the module doc comment for why).
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct GenericParam {
	pub(super) name: Spanned<SymbolU32>,
	pub(super) accesses: Vec<SourceSpan>,
	pub(super) bounds: Box<[TraitBound]>,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct TraitBound {
	pub(super) trait_index: TraitIndex,
	pub(super) span: TextSpan,
	/// `Trait where { Assoc = T, .. }` bindings — empty for a plain `Trait`
	/// bound with no `where` clause.
	pub(super) bindings: Box<[AssocBinding]>,
}

/// One `Assoc = T` or `Assoc: Bound` entry inside a `Trait where { .. }`
/// bound.
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct AssocBinding {
	pub(super) name: SymbolU32,
	/// Which of the trait's declared associated types this binds — found
	/// directly from `defs.rs`'s member bindings, no signature resolution
	/// needed to know *which* member a name means.
	pub(super) assoc_type_def_id: DefId,
	pub(super) kind: AssocBindingKind,
	pub(super) span: TextSpan,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum AssocBindingKind {
	/// `Size = u32` — the associated type must equal exactly this type.
	Equals(TypeIndex),
	/// `Size: UnsignedInt` — the associated type must satisfy this bound.
	Bound(Box<[TraitBound]>),
}

index_newtype!(TypeAliasIndex);
index_newtype!(FunctionIndex);
index_newtype!(AssocTypeIndex);

pub struct TypeAliasSignature {
	def_id: DefId,
	name: Spanned<SymbolU32>,
	type_params: Box<[GenericParam]>,
	/// What this alias transparently stands for. `TypeIndex::ERROR` if its
	/// body failed to resolve or closed a cycle.
	target: TypeIndex,
}

/// A resolved `fn name<...>(params) -> Result { ... }` — covers both
/// `Item::Function` and `Item::FunctionDeclaration` (an `import` block's
/// bodiless signature), which share one `FunctionSignature` shape in the
/// AST and so share one resolved shape here too. No name/identity fields:
/// unlike `TypeAliasSignature`, nothing needs to display a function's name
/// from just this struct — the one place that will (diagnostics, once
/// bodies exist) already has the `DefId` to look the name up from `defs`.
pub struct FunctionSignature {
	type_params: Box<[GenericParam]>,
	param_types: Box<[TypeIndex]>,
	/// `TypeIndex::UNIT` when the source omits `-> Result`.
	return_type: TypeIndex,
}

/// Field *types* only — names/dedup/lookup already settled in
/// `defs::StructDef`, index-aligned with whichever `StructFields` variant
/// that struct has, so record vs. tuple doesn't need re-deriving here.
pub struct StructSignature {
	type_params: Box<[GenericParam]>,
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

/// A trait associated type's resolved bounds (`type Name: Bound1 +
/// Bound2;`). `Self`-referencing bounds aren't resolvable yet — path
/// resolution has no notion of `Self` at all so far, same as every other
/// bound-resolution site in this phase. The concrete type each `impl`
/// provides is a separate query (`TraitImplAssocType`), not tracked here.
pub struct AssocTypeSignature {
	bounds: Box<[TraitBound]>,
}

/// The resolved header of `impl<...> Target { ... }`. Member signatures are
/// separate queries; names and identities already live in `defs.rs`.
pub struct InherentImplSignature {
	pub type_params: Box<[GenericParam]>,
	pub target: Spanned<TypeIndex>,
}

/// The resolved header of `impl<...> Trait for Target { ... }`.
pub struct TraitImplSignature {
	pub type_params: Box<[GenericParam]>,
	/// `None` if resolving the written trait path failed. Its span is kept
	/// for diagnostics when impl dispatch is built.
	pub trait_ref: Option<Spanned<TraitIndex>>,
	pub target: Spanned<TypeIndex>,
}

#[derive(Clone, Copy)]
enum InferSignatureKind {
	Function,
	ReturnType,
	Struct,
	TypeAlias,
	InherentImpl,
	TraitImpl,
	EnumRepr,
	AssocTypeBinding,
	TypeSetMember,
}

impl InferSignatureKind {
	fn noun(self) -> &'static str {
		match self {
			Self::Function => "functions",
			Self::ReturnType => "return types",
			Self::Struct => "structs",
			Self::TypeAlias => "type aliases",
			Self::InherentImpl => "inherent impls",
			Self::TraitImpl => "trait impls",
			Self::EnumRepr => "enum reprs",
			Self::AssocTypeBinding => "associated type bindings",
			Self::TypeSetMember => "typeset members",
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
	/// Each trait's resolved `trait X: Y + Z { ... }` bounds, indexed by the
	/// same `TraitIndex` `defs.traits` already uses — traits need no index
	/// space of their own here, unlike `type_aliases`, since Phase 1 already
	/// has one.
	pub trait_supertraits: Vec<Box<[TraitBound]>>,
	/// Indexed by the same `StructIndex` `defs.structs` already uses — see
	/// `trait_supertraits`.
	pub structs: Vec<StructSignature>,
	/// Indexed by the same `EnumIndex` `defs.enums` already uses — see
	/// `trait_supertraits`.
	pub enums: Vec<EnumSignature>,
	/// Indexed by the same `TypeSetIndex` `defs.typesets` already uses —
	/// see `trait_supertraits`.
	pub typesets: Vec<TypeSetSignature>,
	/// Indexed by `AssocTypeIndex`, allocated lazily as each associated
	/// type's signature resolves — see `type_aliases`.
	pub assoc_types: Vec<AssocTypeSignature>,
	pub functions: Vec<FunctionSignature>,
	/// Index-aligned with the corresponding `defs.rs` impl arenas. A slot is
	/// `None` until its header query completes, even if that query later
	/// recovers with `TypeIndex::ERROR` or an unresolved trait path.
	pub inherent_impls: Vec<Option<InherentImplSignature>>,
	pub trait_impls: Vec<Option<TraitImplSignature>>,
	pub(super) inherent_impl_dispatch:
		HashMap<ImplTarget, Vec<InherentImplIndex>>,
	pub(super) trait_impl_dispatch:
		HashMap<ImplTarget, Vec<(TraitIndex, TraitImplIndex)>>,
	pub item_lookup: HashMap<DefId, ItemLocation>,
	pub types: TypeInterner,
}

impl SignatureRegistry {
	fn build<'ctx>(
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		defs: &DefinitionRegistry,
		ast_nodes: &[AstEntry<'ctx>],
		stdlib_package: PackageId,
	) -> Self {
		let mut builder = SignatureBuilder::new(
			diagnostics,
			strings,
			defs,
			ast_nodes,
			stdlib_package,
		);

		// Impl headers (and, once typesets exist, their synthetic
		// per-member impls) register themselves into dispatch the moment
		// their own `ensure_signature` arm resolves them — see
		// `register_inherent_impl`/`register_trait_impl` in `impls.rs` —
		// so a single sweep over every registered item is enough; no
		// separate early pass or later dispatch-building step is needed.
		for entry in ast_nodes {
			builder.ensure_signature(QueryInfo {
				def_id: entry.def_id,
				requested_at: None,
			});
		}

		Self {
			type_aliases: builder.type_aliases,
			trait_supertraits: builder.trait_supertraits,
			structs: builder.structs,
			enums: builder.enums,
			typesets: builder.typesets,
			assoc_types: builder.assoc_types,
			functions: builder.functions,
			inherent_impls: builder.inherent_impls,
			trait_impls: builder.trait_impls,
			inherent_impl_dispatch: builder.inherent_impl_dispatch,
			trait_impl_dispatch: builder.trait_impl_dispatch,
			item_lookup: builder.item_lookup,
			types: builder.types,
		}
	}
}

/// Where a `DefId`'s data actually lives — one arena per item kind
/// `ensure_signature` can be asked about. `Trait`/`TraitImpl`/`InherentImpl`/
/// `Struct` use indices allocated in `defs.rs` and keep resolved data in
/// index-aligned slots here; aliases and functions get indices as their
/// signatures finish resolving.
#[derive(Clone, Copy)]
pub enum ItemLocation {
	Trait(TraitIndex),
	TraitImpl(TraitImplIndex),
	InherentImpl(InherentImplIndex),
	Struct(StructIndex),
	Enum(EnumIndex),
	TypeSet(TypeSetIndex),
	TypeAlias(TypeAliasIndex),
	Function(FunctionIndex),
	TraitAssocType(AssocTypeIndex),
}

/// What `ensure_signature` found. `Cycle` is never stored anywhere — it's a
/// transient signal for whichever call is re-entering a query still
/// `InProgress` further down the stack; that caller reports the cycle once
/// (using `query_stack` to know what closed the loop) and substitutes
/// `TypeIndex::ERROR`, then keeps going. Every item in the cycle still
/// reaches its own `Done` normally.
pub(super) enum SignatureStatus {
	Resolved,
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
/// this is never a final state: it's overwritten to `Done` unconditionally
/// once the query's own execution actually finishes, same as `InProgress`
/// would be — a signature always has *some* value once resolution reaches
/// `Done` (a failed piece becomes `TypeIndex::ERROR`, the same
/// recovery-value pattern `BindingTarget::Error` already uses at the
/// identity layer), so there's never a case where `Done` itself needs a "no
/// value" alternative the way `Resolved(T)` does for imports.
#[derive(Clone, Copy)]
enum QueryState {
	Pending,
	InProgress,
	/// Still `InProgress` — this query's own execution hasn't actually
	/// finished — but a cycle closing back through it has already been
	/// reported once. See the enum's own doc comment.
	CycleReported,
	Done,
}

/// Which question is being asked about a `DefId`. The state/stack this
/// keys into (`query_state`/`query_stack` below) is shared across every
/// kind — mirrors rustc's own query system: one active stack for cycle
/// detection across all query kinds, even though each kind's actual
/// *result* storage (`type_aliases`, `structs`, ...) stays completely
/// separate, untouched by this. Only one variant exists right now; this
/// exists so a later, genuinely separate question (e.g. a future body/const
/// -evaluation pass) has a home to plug into without re-deriving this same
/// state machine a second time.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum QueryKind {
	Signature,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct QueryKey {
	kind: QueryKind,
	def_id: DefId,
}

impl QueryKey {
	fn signature(def_id: DefId) -> Self {
		Self {
			kind: QueryKind::Signature,
			def_id,
		}
	}
}

/// `ast_index` is this key's position in `SignatureBuilder::ast_nodes` — set
/// once, at construction, from `defs.rs`'s parse-order record, so
/// `ensure_signature` never needs a second lookup to find the AST it's
/// supposed to resolve.
struct QueryEntry {
	ast_index: u32,
	state: QueryState,
}

/// One in-progress query frame — mirrors `rustc_query_system`'s own
/// `QueryInfo`. `requested_at` is the span of the reference that demanded
/// `key`, i.e. "the reason for which this was required"; `None` only for a
/// top-level, non-reference demand (the per-`DefId` driver loop) —
/// `resolve_type` always supplies `Some` when it recurses because of a
/// written reference.
#[derive(Clone, Copy)]
struct QueryFrame {
	key: QueryKey,
	requested_at: Option<SourceSpan>,
}

/// What a caller passes to `ensure_signature` — kept `DefId`-shaped (every
/// call site already constructs one of these) rather than exposing
/// `QueryKey` itself, since every current caller only ever means the
/// `Signature` kind; it's wrapped into a `QueryKey` internally.
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
	stdlib_root: NamespaceIndex,
	item_lookup: HashMap<DefId, ItemLocation>,
	query_state: HashMap<QueryKey, QueryEntry>,
	/// In-progress queries, in call order — shared across every `QueryKind`.
	query_stack: Vec<QueryFrame>,
	pub(super) types: TypeInterner,
	type_aliases: Vec<TypeAliasSignature>,
	trait_supertraits: Vec<Box<[TraitBound]>>,
	structs: Vec<StructSignature>,
	enums: Vec<EnumSignature>,
	typesets: Vec<TypeSetSignature>,
	assoc_types: Vec<AssocTypeSignature>,
	functions: Vec<FunctionSignature>,
	pub(super) inherent_impls: Vec<Option<InherentImplSignature>>,
	pub(super) trait_impls: Vec<Option<TraitImplSignature>>,
	pub(super) inherent_impl_dispatch:
		HashMap<ImplTarget, Vec<InherentImplIndex>>,
	pub(super) trait_impl_dispatch:
		HashMap<ImplTarget, Vec<(TraitIndex, TraitImplIndex)>>,
}

impl<'ast, 'ctx> SignatureBuilder<'ast, 'ctx> {
	pub(super) fn new(
		diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
		strings: &'ctx StringInterner,
		defs: &'ctx DefinitionRegistry,
		ast_nodes: &'ast [AstEntry<'ast>],
		stdlib_package: PackageId,
	) -> Self {
		let stdlib_root = defs.package_namespaces[stdlib_package.as_usize()];

		let mut item_lookup = HashMap::new();
		for (index, trait_def) in defs.traits.iter().enumerate() {
			item_lookup.insert(
				trait_def.def_id,
				ItemLocation::Trait(TraitIndex::new(
					u32::try_from(index).unwrap(),
				)),
			);
		}
		for (index, impl_def) in defs.trait_impls.iter().enumerate() {
			item_lookup.insert(
				impl_def.def_id,
				ItemLocation::TraitImpl(TraitImplIndex::new(
					u32::try_from(index).unwrap(),
				)),
			);
		}
		for (index, impl_def) in defs.inherent_impls.iter().enumerate() {
			item_lookup.insert(
				impl_def.def_id,
				ItemLocation::InherentImpl(InherentImplIndex::new(
					u32::try_from(index).unwrap(),
				)),
			);
		}
		for (index, struct_def) in defs.structs.iter().enumerate() {
			item_lookup.insert(
				struct_def.def_id,
				ItemLocation::Struct(StructIndex::new(
					u32::try_from(index).unwrap(),
				)),
			);
		}
		for (index, enum_def) in defs.enums.iter().enumerate() {
			item_lookup.insert(
				enum_def.def_id,
				ItemLocation::Enum(EnumIndex::new(
					u32::try_from(index).unwrap(),
				)),
			);
		}
		// Last, deliberately: a typeset's backing trait and synthetic
		// per-member impls (seeded just above, as ordinary `Trait`/
		// `TraitImpl` entries) reuse the typeset's own `def_id` — see
		// `defs::TypeSetDef`'s doc comment — so this insert intentionally
		// overwrites theirs. Nothing ever looks up that `def_id` expecting
		// `ItemLocation::Trait`/`TraitImpl` (a name bound to a typeset only
		// ever resolves to `DefKind::TypeSet`), so `ItemLocation::TypeSet`
		// is the only entry that's ever actually read back for it.
		for (index, typeset_def) in defs.typesets.iter().enumerate() {
			item_lookup.insert(
				typeset_def.def_id,
				ItemLocation::TypeSet(TypeSetIndex::new(
					u32::try_from(index).unwrap(),
				)),
			);
		}

		let mut query_state: HashMap<QueryKey, QueryEntry> = ast_nodes
			.iter()
			.enumerate()
			.map(|(index, entry)| {
				(
					QueryKey::signature(entry.def_id),
					QueryEntry {
						ast_index: u32::try_from(index).unwrap(),
						state: QueryState::Pending,
					},
				)
			})
			.collect();

		// Primitives (`#[intrinsic] pub type u8;`) are `DefKind::TypeAlias`
		// like any other alias, but bodiless — nothing to resolve, the
		// answer is already known from `defs.intrinsics`. Settling them here
		// (fully: location *and* value) keeps that fact out of
		// `ensure_signature`'s `TypeAlias` arm entirely, which can then
		// assume its body is always real.
		let mut type_aliases = Vec::new();
		for (key, type_index) in [
			(defs.intrinsics.u8, TypeIndex::U8),
			(defs.intrinsics.i8, TypeIndex::I8),
			(defs.intrinsics.u16, TypeIndex::U16),
			(defs.intrinsics.i16, TypeIndex::I16),
			(defs.intrinsics.u32, TypeIndex::U32),
			(defs.intrinsics.i32, TypeIndex::I32),
			(defs.intrinsics.u64, TypeIndex::U64),
			(defs.intrinsics.i64, TypeIndex::I64),
			(defs.intrinsics.f32, TypeIndex::F32),
			(defs.intrinsics.f64, TypeIndex::F64),
			(defs.intrinsics.bool, TypeIndex::BOOL),
			(defs.intrinsics.char, TypeIndex::CHAR),
			(defs.intrinsics.never, TypeIndex::NEVER),
		] {
			let Some(key) = key else { continue };
			let DefKind::TypeAlias(def_id) = key.symbol_kind(defs) else {
				unreachable!()
			};
			// Only ever absent when `ast_nodes` is deliberately partial (a
			// test convenience) — real callers always pass the full prescan
			// output, which covers every primitive by construction.
			let key = QueryKey::signature(def_id);
			let Some(entry) = query_state.get_mut(&key) else {
				continue;
			};
			let ast_index = entry.ast_index;
			entry.state = QueryState::Done;

			let index =
				TypeAliasIndex::new(u32::try_from(type_aliases.len()).unwrap());
			type_aliases.push(TypeAliasSignature {
				def_id,
				name: item_name(ast_nodes, ast_index),
				type_params: Box::new([]),
				target: type_index,
			});
			item_lookup.insert(def_id, ItemLocation::TypeAlias(index));
		}

		Self {
			diagnostics,
			strings,
			defs,
			ast_nodes,
			stdlib_root,
			item_lookup,
			query_state,
			query_stack: Vec::new(),
			types: TypeInterner::new(),
			type_aliases,
			trait_supertraits: defs
				.traits
				.iter()
				.map(|_| Box::default())
				.collect(),
			structs: defs
				.structs
				.iter()
				.map(|_| StructSignature {
					type_params: Box::default(),
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
			assoc_types: Vec::new(),
			functions: Vec::new(),
			inherent_impls: defs.inherent_impls.iter().map(|_| None).collect(),
			trait_impls: defs.trait_impls.iter().map(|_| None).collect(),
			inherent_impl_dispatch: HashMap::new(),
			trait_impl_dispatch: HashMap::new(),
		}
	}

	/// Resolves one item's whole `<...>` parameter list: the duplicate-name
	/// check moved here from `defs.rs`'s prescan (see the module doc
	/// comment), plus each parameter's own bounds.
	pub(super) fn resolve_generic_params(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		owner: DefId,
		ast_params: &[ast::TypeParam],
	) -> Box<[GenericParam]> {
		// Two passes: a bound can name a sibling param declared *later* in
		// the same list (`Src: Memory where { Size = S }, S: PointerSize`),
		// and `resolve_type`'s generic-scope lookup only ever finds a name
		// already present in the slice it's given. Registering every name
		// up front — bounds filled in as `Box::new([])` for now — gives
		// pass two a complete scope to resolve every param's bounds
		// against, sibling order no longer mattering.
		let mut params: Vec<GenericParam> =
			Vec::with_capacity(ast_params.len());
		for ast_param in ast_params {
			// Checked against what's already in `params`, *before* this one
			// is pushed — checking the post-push vec would always find this
			// same entry as its own "collision".
			if let Some(first) = params
				.iter()
				.find(|p| p.name.inner == ast_param.name.inner)
				.map(|p| p.name)
			{
				self.diagnostics.push(report_duplicate_generic_param(
					self.strings,
					file_id,
					ast_param.name,
					first,
				));
			}

			params.push(GenericParam {
				name: ast_param.name,
				accesses: Vec::new(),
				bounds: Box::new([]),
			});
		}

		for (index, ast_param) in ast_params.iter().enumerate() {
			let Some(bound) = &ast_param.bounds else {
				continue;
			};
			params[index].bounds =
				self.resolve_bounds(file_id, namespace, owner, &params, bound);
		}

		params.into_boxed_slice()
	}

	/// The demand-driven driver: computes `def_id`'s signature if it hasn't
	/// been already. The two checks below are safe to return early from —
	/// nothing has been pushed onto `query_stack` yet at that point. Past
	/// that, no early `return`: `query_stack`'s frame has to pop and
	/// `state` has to reach `Done` no matter which arm runs below, or this
	/// query is left `InProgress` forever.
	pub(super) fn ensure_signature(
		&mut self,
		query: QueryInfo,
	) -> SignatureStatus {
		let def_id = query.def_id;
		let key = QueryKey::signature(def_id);
		match self.query_state[&key].state {
			QueryState::Done | QueryState::CycleReported => {
				return SignatureStatus::Resolved;
			}
			// First re-entrant discovery: flip to `CycleReported` right
			// here, atomically, before returning `Cycle` — mirrors
			// `ResolveStatus::poll`'s `Resolving -> Error` transition. This
			// is what makes a *second*, independent path that re-discovers
			// the same still-running query see `CycleReported` (silent)
			// instead of `InProgress` (which would mean "report again").
			QueryState::InProgress => {
				self.query_state.get_mut(&key).unwrap().state =
					QueryState::CycleReported;
				return SignatureStatus::Cycle;
			}
			QueryState::Pending => {}
		}

		self.query_state.get_mut(&key).unwrap().state = QueryState::InProgress;
		self.query_stack.push(QueryFrame {
			key,
			requested_at: query.requested_at,
		});

		let ast_index = self.query_state[&key].ast_index;
		let ast_nodes = self.ast_nodes;
		let entry = &ast_nodes[ast_index as usize];
		let file_id = entry.file_id;
		let namespace = entry.namespace;
		let node = entry.node.clone();

		match node {
			AstNodeRef::TypeAlias { item } => {
				let ast::Item::TypeAlias {
					name,
					type_params,
					body,
					..
				} = item
				else {
					unreachable!()
				};
				let body = body.as_ref().expect(
					"bodiless type aliases are already Done before construction finishes",
				);

				let resolved_params = self.resolve_generic_params(
					file_id,
					namespace,
					def_id,
					type_params,
				);
				let target = self.resolve_type(
					file_id,
					namespace,
					def_id,
					&resolved_params,
					body,
					InferPolicy::Reject(InferSignatureKind::TypeAlias),
				);

				let index = TypeAliasIndex::new(
					u32::try_from(self.type_aliases.len()).unwrap(),
				);
				self.type_aliases.push(TypeAliasSignature {
					def_id,
					name: *name,
					type_params: resolved_params,
					target,
				});
				self.item_lookup
					.insert(def_id, ItemLocation::TypeAlias(index));
			}
			AstNodeRef::Trait { trait_index, item } => {
				let ast::Item::Trait { supertraits, .. } = item else {
					unreachable!()
				};

				let bounds = match supertraits {
					// Traits have no generic params of their own in this
					// language — `owner`/`generic_scope` only matter for a
					// `where`-bound's `Equals` right-hand side, which has
					// nothing to resolve against here.
					Some(bound) => self
						.resolve_bounds(file_id, namespace, def_id, &[], bound),
					None => Box::new([]),
				};

				for bound in &bounds {
					let super_def_id =
						self.defs.traits[usize::from(bound.trait_index)].def_id;
					let reference = SourceSpan::new(file_id, bound.span);
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

				self.trait_supertraits[usize::from(trait_index)] = bounds;
			}
			AstNodeRef::TraitAssocType { item, .. } => {
				let ast::TraitItem::AssociatedType { bounds, .. } = item
				else {
					unreachable!()
				};

				let resolved_bounds = match bounds {
					Some(bound) => self
						.resolve_bounds(file_id, namespace, def_id, &[], bound),
					None => Box::new([]),
				};

				let index = AssocTypeIndex::new(
					u32::try_from(self.assoc_types.len()).unwrap(),
				);
				self.assoc_types.push(AssocTypeSignature {
					bounds: resolved_bounds,
				});
				self.item_lookup
					.insert(def_id, ItemLocation::TraitAssocType(index));
			}
			AstNodeRef::RecordStruct { item } => {
				let ast::Item::RecordStruct {
					type_params: ast_type_params,
					fields,
					..
				} = item
				else {
					unreachable!()
				};
				let Some(&ItemLocation::Struct(struct_index)) =
					self.item_lookup.get(&def_id)
				else {
					unreachable!(
						"every struct's StructIndex is pre-seeded in SignatureBuilder::new"
					)
				};

				let resolved_params = self.resolve_generic_params(
					file_id,
					namespace,
					def_id,
					ast_type_params,
				);

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
						def_id,
						&resolved_params,
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

				self.structs[usize::from(struct_index)] = StructSignature {
					type_params: resolved_params,
					field_types: field_types.into_boxed_slice(),
				};
			}
			AstNodeRef::TupleStruct { item } => {
				let ast::Item::TupleStruct {
					type_params: ast_type_params,
					fields,
					..
				} = item
				else {
					unreachable!()
				};
				let Some(&ItemLocation::Struct(struct_index)) =
					self.item_lookup.get(&def_id)
				else {
					unreachable!(
						"every struct's StructIndex is pre-seeded in SignatureBuilder::new"
					)
				};

				let resolved_params = self.resolve_generic_params(
					file_id,
					namespace,
					def_id,
					ast_type_params,
				);

				let mut field_types: Vec<TypeIndex> =
					Vec::with_capacity(fields.len());
				for f in fields.iter() {
					let ty_expr = &f.inner.inner.ty;
					let ty = self.resolve_type(
						file_id,
						namespace,
						def_id,
						&resolved_params,
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

				self.structs[usize::from(struct_index)] = StructSignature {
					type_params: resolved_params,
					field_types: field_types.into_boxed_slice(),
				};
			}
			AstNodeRef::Function { item } => {
				let (ast::Item::Function { signature, .. }
				| ast::Item::FunctionDeclaration { signature, .. }) = item
				else {
					unreachable!()
				};

				let resolved_params = self.resolve_generic_params(
					file_id,
					namespace,
					def_id,
					&signature.type_params,
				);

				// Positional, so a duplicate name still gets its own
				// resolved slot in `param_types` — same reasoning as
				// struct fields (see `defs::StructFields`'s doc comment).
				// Names themselves aren't kept past this loop: nothing
				// downstream looks a parameter up by name yet, unlike a
				// struct field.
				let mut seen_params: Vec<Spanned<SymbolU32>> =
					Vec::with_capacity(signature.params.len());
				let mut param_types: Vec<TypeIndex> =
					Vec::with_capacity(signature.params.len());
				for param in signature.params.iter() {
					let name = param.inner.inner.name;
					if let Some(first) = seen_params
						.iter()
						.find(|p| p.inner == name.inner)
						.copied()
					{
						self.diagnostics.push(report_duplicate_function_param(
							self.strings,
							file_id,
							name,
							first,
						));
					}
					seen_params.push(name);

					let ty = match &param.inner.inner.ty {
						Some(ty) => self.resolve_type(
							file_id,
							namespace,
							def_id,
							&resolved_params,
							ty,
							InferPolicy::Reject(InferSignatureKind::Function),
						),
						// Only ever `None` when the source omits `: Type`
						// entirely — legal grammar (methods rely on it for
						// an untyped `self`), but `Item::Function`/
						// `FunctionDeclaration` are always free functions,
						// so there's no `Self` to default to here.
						None => TypeIndex::ERROR,
					};
					param_types.push(ty);
				}

				let return_type = match &signature.result {
					Some(result) => self.resolve_type(
						file_id,
						namespace,
						def_id,
						&resolved_params,
						result,
						InferPolicy::Reject(InferSignatureKind::ReturnType),
					),
					None => TypeIndex::UNIT,
				};

				let index = FunctionIndex::new(
					u32::try_from(self.functions.len()).unwrap(),
				);
				self.functions.push(FunctionSignature {
					type_params: resolved_params,
					param_types: param_types.into_boxed_slice(),
					return_type,
				});
				self.item_lookup
					.insert(def_id, ItemLocation::Function(index));
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
				let resolved_params = self.resolve_generic_params(
					file_id,
					namespace,
					def_id,
					type_params,
				);
				let target_type = self.resolve_type(
					file_id,
					namespace,
					def_id,
					&resolved_params,
					target,
					InferPolicy::Reject(InferSignatureKind::InherentImpl),
				);
				let target_spanned = Spanned {
					inner: target_type,
					span: target.span,
				};
				self.inherent_impls[usize::from(block_index)] =
					Some(InherentImplSignature {
						type_params: resolved_params,
						target: target_spanned,
					});
				self.register_inherent_impl(
					block_index,
					file_id,
					target_spanned,
				);
			}
			AstNodeRef::TraitImplBlock { item, block_index } => {
				let ast::Item::TraitImpl {
					type_params,
					trait_name,
					target,
					..
				} = item
				else {
					unreachable!()
				};
				let resolved_params = self.resolve_generic_params(
					file_id,
					namespace,
					def_id,
					type_params,
				);
				let trait_target = PathResolver::new(
					&self.defs.namespaces,
					&self.defs.use_items,
					self.stdlib_root,
				)
				.resolve_path(
					self.diagnostics,
					self.strings,
					file_id,
					namespace,
					trait_name,
					BindingNamespace::Type,
				);
				let trait_ref = trait_target.def_key().and_then(|key| {
					let trait_index = match key.symbol_kind(self.defs) {
						DefKind::Trait(trait_def_id) => {
							let Some(&ItemLocation::Trait(index)) =
								self.item_lookup.get(&trait_def_id)
							else {
								unreachable!()
							};
							index
						}
						other => {
							let last = trait_name.last().unwrap();
							self.diagnostics.push(report_expected_trait_bound(
								file_id,
								self.strings,
								last.ident,
								other.noun(),
							));
							return None;
						}
					};
					let span = TextSpan::new(
						trait_name.first().unwrap().ident.span.start,
						trait_name.last().unwrap().ident.span.end,
					);
					Some(Spanned {
						inner: trait_index,
						span,
					})
				});
				let target_type = self.resolve_type(
					file_id,
					namespace,
					def_id,
					&resolved_params,
					target,
					InferPolicy::Reject(InferSignatureKind::TraitImpl),
				);
				let target_spanned = Spanned {
					inner: target_type,
					span: target.span,
				};
				self.trait_impls[usize::from(block_index)] =
					Some(TraitImplSignature {
						type_params: resolved_params,
						trait_ref,
						target: target_spanned,
					});
				if let Some(trait_ref) = trait_ref {
					self.register_trait_impl(
						block_index,
						trait_ref.inner,
						file_id,
						target_spanned,
					);
				}
			}
			AstNodeRef::Enum { item } => {
				let ast::Item::Enum { repr, name, .. } = item else {
					unreachable!()
				};
				let Some(&ItemLocation::Enum(enum_index)) =
					self.item_lookup.get(&def_id)
				else {
					unreachable!(
						"every enum's EnumIndex is pre-seeded in SignatureBuilder::new"
					)
				};

				let repr_type = match repr {
					Some(repr_expr) => {
						let resolved = self.resolve_type(
							file_id,
							namespace,
							def_id,
							&[],
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
						self.diagnostics.push(report_missing_enum_repr(
							file_id, name.span,
						));
						TypeIndex::ERROR
					}
				};

				self.enums[usize::from(enum_index)] =
					EnumSignature { repr: repr_type };
			}
			AstNodeRef::TypeSet { typeset_index, item } => {
				let ast::Item::TypeSet { bounds, members, .. } = item else {
					unreachable!()
				};
				let trait_index =
					self.defs.typesets[usize::from(typeset_index)]
						.trait_index;
				let member_impls =
					self.defs.typesets[usize::from(typeset_index)]
						.member_impls
						.clone();

				// The typeset's own `: A + B` clause becomes its backing
				// trait's supertraits — same shape and cycle-forcing as a
				// hand-written `trait X: A + B {}`.
				let clause_bounds = match bounds {
					Some(bound) => self.resolve_bounds(
						file_id, namespace, def_id, &[], bound,
					),
					None => Box::new([]),
				};
				for bound in &clause_bounds {
					let super_def_id = self.defs.traits
						[usize::from(bound.trait_index)]
					.def_id;
					let reference = SourceSpan::new(file_id, bound.span);
					let status = self.ensure_signature(QueryInfo {
						def_id: super_def_id,
						requested_at: Some(reference),
					});
					if let SignatureStatus::Cycle = status {
						let diagnostic = self.report_cyclic_supertrait(
							super_def_id,
							reference,
						);
						self.diagnostics.push(diagnostic);
					}
				}
				self.trait_supertraits[usize::from(trait_index)] =
					clause_bounds;

				// Each written member becomes a synthetic `impl
				// <trait_index> for <member>`, fed through the same
				// dispatch registration real impls use — "does concrete
				// type T satisfy this typeset" later is just an ordinary
				// trait-impl lookup, no special-casing downstream.
				let mut resolved_members =
					Vec::with_capacity(members.len());
				for (m, &impl_index) in members.iter().zip(member_impls.iter())
				{
					let member_ty = self.resolve_type(
						file_id,
						namespace,
						def_id,
						&[],
						&m.inner,
						InferPolicy::Reject(InferSignatureKind::TypeSetMember),
					);
					// No separate "is this a legal typeset member" check —
					// `register_trait_impl` already reports
					// `InvalidImplTarget` for exactly this (a typeset
					// member *is* a synthetic impl target), and skips
					// bucketing it, so nothing further to do here.
					let target_spanned = Spanned {
						inner: member_ty,
						span: m.inner.span,
					};
					self.trait_impls[usize::from(impl_index)] =
						Some(TraitImplSignature {
							type_params: Box::new([]),
							trait_ref: Some(Spanned {
								inner: trait_index,
								span: m.inner.span,
							}),
							target: target_spanned,
						});
					self.register_trait_impl(
						impl_index,
						trait_index,
						file_id,
						target_spanned,
					);
					resolved_members.push(target_spanned);
				}

				self.typesets[usize::from(typeset_index)] =
					TypeSetSignature {
						members: resolved_members.into_boxed_slice(),
					};
			}
			_ => todo!("this item kind's signature isn't implemented yet"),
		}

		self.query_stack.pop();
		self.query_state.get_mut(&key).unwrap().state = QueryState::Done;
		SignatureStatus::Resolved
	}

	/// Resolves a written type. `Reject` diagnoses `_` at its own span and
	/// recovers as `TypeIndex::ERROR`; `Allow` preserves it as `INFER`.
	/// Nested types retain their shape. Other forms are still being implemented.
	fn resolve_type(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		owner: DefId,
		generic_scope: &[GenericParam],
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
				if let [segment] = &segments[..]
					&& segment.type_args.is_empty()
					&& let Some(param_index) =
						generic_scope.iter().position(|param| {
							param.name.inner == segment.ident.inner
						}) {
					return self.types.intern(Type::TypeParam {
						owner,
						param_index: u32::try_from(param_index).unwrap(),
					});
				}

				let target = PathResolver::new(
					&self.defs.namespaces,
					&self.defs.use_items,
					self.stdlib_root,
				)
				.resolve_path(
					self.diagnostics,
					self.strings,
					file_id,
					namespace,
					segments,
					BindingNamespace::Type,
				);
				let Some(def_key) = target.def_key() else {
					return TypeIndex::ERROR;
				};
				match def_key.symbol_kind(self.defs) {
					DefKind::TypeAlias(def_id) => {
						let last = segments
							.last()
							.expect("a path always has at least one segment");
						let reference =
							SourceSpan::new(file_id, last.ident.span);

						let status = self.ensure_signature(QueryInfo {
							def_id,
							requested_at: Some(reference),
						});
						match status {
							SignatureStatus::Cycle => {
								let diagnostic = self.report_cyclic_type_alias(
									def_id, reference,
								);
								self.diagnostics.push(diagnostic);
								TypeIndex::ERROR
							}
							SignatureStatus::Resolved => {
								let Some(&ItemLocation::TypeAlias(index)) =
									self.item_lookup.get(&def_id)
								else {
									unreachable!()
								};
								self.type_aliases[usize::from(index)].target
							}
						}
					}
					DefKind::Struct(struct_def_id) => {
						let Some(&ItemLocation::Struct(struct_index)) =
							self.item_lookup.get(&struct_def_id)
						else {
							unreachable!(
								"every struct's StructIndex is pre-seeded in SignatureBuilder::new"
							)
						};

						// Identity only — deliberately not `ensure_signature`:
						// a struct's fields don't need to be resolved to name
						// the struct itself, which is what lets a self-/
						// mutually-referencing pointer field resolve without
						// falsely tripping the cycle machinery `TypeAlias`
						// needs.
						let last = segments
							.last()
							.expect("a path always has at least one segment");
						if !last.type_args.is_empty() {
							todo!(
								"generic struct instantiation at a reference site isn't implemented yet"
							)
						}

						self.types.intern(Type::Struct {
							struct_index,
							args: Box::new([]),
						})
					}
					_ => todo!(
						"resolving a path to this kind of item isn't implemented yet"
					),
				}
			}
			ast::TypeExpression::Function { params, result } => {
				let mut param_types = Vec::with_capacity(params.len());
				for param in params.iter() {
					param_types.push(self.resolve_type(
						file_id,
						namespace,
						owner,
						generic_scope,
						&param.inner.inner.ty,
						infer_policy,
					));
				}
				let result_type = match result {
					Some(result) => self.resolve_type(
						file_id,
						namespace,
						owner,
						generic_scope,
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
						owner,
						generic_scope,
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
	/// Shared by every cycle kind (`CyclicTypeAlias`, `CyclicSupertrait`,
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
		let key = QueryKey::signature(def_id);
		let position = self
			.query_stack
			.iter()
			.position(|frame| frame.key == key)
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
			item_name(self.ast_nodes, self.query_state[&key].ast_index);
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
				self.query_state[&frame.key].ast_index,
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
			DiagnosticCode::CyclicSupertrait,
			|name| format!("computing the supertraits of `{name}`"),
		)
		.with_note("a trait cannot require itself as a supertrait")
	}

	/// Renders the rustc-E0072-style diagnostic: every struct in the cycle
	/// gets its own primary label (at its own declaration name) plus a
	/// secondary label at the specific field that continues the cycle,
	/// rather than the single-root "cycle detected when..." chain
	/// `report_cycle` renders for `CyclicTypeAlias`/`CyclicSupertrait`. The
	/// full chain is already sitting in `query_stack[position..]` — built up
	/// by the ordinary recursive `ensure_signature` forcing that got us
	/// here — so there's nothing to separately collect first.
	fn report_recursive_struct_cycle(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
	) -> Diagnostic<FileId> {
		let key = QueryKey::signature(def_id);
		let position = self
			.query_stack
			.iter()
			.position(|frame| frame.key == key)
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
			let ast_index = self.query_state[&frame.key].ast_index;
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
		namespace: NamespaceIndex,
		owner: DefId,
		generic_scope: &[GenericParam],
		bound: &Spanned<ast::BoundExpression>,
	) -> Box<[TraitBound]> {
		let mut traits = Vec::new();
		self.collect_bounds(
			file_id,
			namespace,
			owner,
			generic_scope,
			bound,
			&mut traits,
		);
		traits.into_boxed_slice()
	}

	/// `+`-joined bounds flatten into one `Vec` — `T: Add + PartialEq`
	/// produces two `TraitBound`s, not a nested structure mirroring
	/// `BoundList`.
	fn collect_bounds(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		owner: DefId,
		generic_scope: &[GenericParam],
		bound: &Spanned<ast::BoundExpression>,
		out: &mut Vec<TraitBound>,
	) {
		match &bound.inner {
			ast::BoundExpression::BoundList(list) => {
				for entry in list.iter() {
					self.collect_bounds(
						file_id,
						namespace,
						owner,
						generic_scope,
						entry,
						out,
					);
				}
			}
			ast::BoundExpression::Path(segments) => {
				if let Some(trait_index) =
					self.resolve_trait_bound_path(file_id, namespace, segments)
				{
					out.push(TraitBound {
						trait_index,
						span: bound.span,
						bindings: Box::new([]),
					});
				}
			}
			ast::BoundExpression::WithBindings { path, bindings } => {
				// The parser only ever builds `WithBindings.path` as
				// `Box::new(BoundExpression::Path(..))` (`parse_bound` in
				// `ast/mod.rs`) — never a list or another `WithBindings`.
				let ast::BoundExpression::Path(segments) = path.as_ref()
				else {
					unreachable!(
						"`WithBindings.path` is always a plain `Path`"
					)
				};
				let Some(trait_index) =
					self.resolve_trait_bound_path(file_id, namespace, segments)
				else {
					return;
				};

				let mut resolved_bindings: Vec<AssocBinding> =
					Vec::with_capacity(bindings.len());
				for binding in bindings.iter() {
					if resolved_bindings
						.iter()
						.any(|b| b.name == binding.name.inner)
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
					let assoc_type_def_id = trait_def
						.bindings
						.get(&BindingKey::ty(binding.name.inner))
						.map(|&member_index| {
							trait_def.members[usize::from(member_index)].kind
						})
						.and_then(|kind| match kind {
							MemberKind::AssociatedType(id) => Some(id),
							MemberKind::Function(_) | MemberKind::Constant(_) => {
								None
							}
						});
					let Some(assoc_type_def_id) = assoc_type_def_id else {
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
								owner,
								generic_scope,
								ty,
								InferPolicy::Reject(
									InferSignatureKind::AssocTypeBinding,
								),
							);
							AssocBindingKind::Equals(resolved)
						}
						ast::AssocTypeBindingKind::Bound(rhs_bound) => {
							let rhs_bounds = self.resolve_bounds(
								file_id,
								namespace,
								owner,
								generic_scope,
								rhs_bound,
							);
							AssocBindingKind::Bound(rhs_bounds)
						}
					};

					resolved_bindings.push(AssocBinding {
						name: binding.name.inner,
						assoc_type_def_id,
						kind,
						span: binding.name.span,
					});
				}

				out.push(TraitBound {
					trait_index,
					span: bound.span,
					bindings: resolved_bindings.into_boxed_slice(),
				});
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
		namespace: NamespaceIndex,
		segments: &[ast::PathSegment],
	) -> Option<TraitIndex> {
		let target = PathResolver::new(
			&self.defs.namespaces,
			&self.defs.use_items,
			self.stdlib_root,
		)
		.resolve_path(
			self.diagnostics,
			self.strings,
			file_id,
			namespace,
			segments,
			BindingNamespace::Type,
		);
		let def_key = target.def_key()?;
		match def_key.symbol_kind(self.defs) {
			DefKind::Trait(def_id) => {
				let Some(&ItemLocation::Trait(trait_index)) =
					self.item_lookup.get(&def_id)
				else {
					unreachable!()
				};
				Some(trait_index)
			}
			// A `typeset` bound resolves to its own compiler-generated
			// trait — `TypeSetIndex` (and, through it, `trait_index`) is
			// Phase 1 data, seeded into `item_lookup` before any Phase 2
			// resolution runs, exactly like `TraitIndex` above. No
			// forcing needed here for the same reason the `Trait` arm
			// doesn't force anything either: this function only answers
			// "which item does this name refer to," not "is its data
			// complete yet" — that's for whichever later consumer
			// actually reads `trait_supertraits`/dispatch to force, at
			// its own point of need.
			DefKind::TypeSet(def_id) => {
				let Some(&ItemLocation::TypeSet(typeset_index)) =
					self.item_lookup.get(&def_id)
				else {
					unreachable!(
						"every typeset's TypeSetIndex is pre-seeded in SignatureBuilder::new"
					)
				};
				Some(
					self.defs.typesets[usize::from(typeset_index)]
						.trait_index,
				)
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
		AstNodeRef::TypeAlias { item } => {
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
		AstNodeRef::RecordStruct { item } => {
			let ast::Item::RecordStruct { name, .. } = item else {
				unreachable!()
			};
			*name
		}
		AstNodeRef::TupleStruct { item } => {
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
		.with_message(format!("duplicate generic parameter `{name_str}`"))
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

fn report_expected_trait_bound(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	noun: &str,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::ExpectedTraitBound.code())
		.with_message(format!("expected trait, found {noun} `{name_str}`"))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("not a trait"),
		)
}

fn report_duplicate_assoc_type_binding(
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

fn report_not_an_associated_type(
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
	use indoc::indoc;

	use super::*;
	use crate::tir::defs::DefinitionRegistry;
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
			);

			let signatures = SignatureRegistry::build(
				&mut diagnostics,
				&graph.strings,
				&defs,
				&ast_nodes,
				graph.stdlib_package,
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
			let root = self.defs.package_namespaces
				[self.graph.root_package.as_usize()];
			let file_id = self.defs.namespaces[usize::from(root)].file_id;
			let stdlib_root = self.defs.package_namespaces
				[self.graph.stdlib_package.as_usize()];

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
			let target = PathResolver::new(
				&self.defs.namespaces,
				&self.defs.use_items,
				stdlib_root,
			)
			.resolve_path(
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

		fn trait_index(&self, path: &str) -> TraitIndex {
			let DefKind::Trait(def_id) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a trait");
			};
			let Some(&ItemLocation::Trait(index)) =
				self.signatures.item_lookup.get(&def_id)
			else {
				panic!("expected a Trait location for `{path}`");
			};
			index
		}

		fn trait_supertraits(&self, path: &str) -> &[TraitBound] {
			&self.signatures.trait_supertraits
				[usize::from(self.trait_index(path))]
		}

		fn typeset_index(&self, path: &str) -> TypeSetIndex {
			let DefKind::TypeSet(def_id) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a typeset");
			};
			let Some(&ItemLocation::TypeSet(index)) =
				self.signatures.item_lookup.get(&def_id)
			else {
				panic!("expected a TypeSet location for `{path}`");
			};
			index
		}

		fn typeset_signature(&self, path: &str) -> &TypeSetSignature {
			&self.signatures.typesets[usize::from(self.typeset_index(path))]
		}

		/// The `TraitIndex` of `path`'s compiler-generated backing trait —
		/// what a `T: <path>` bound actually resolves to.
		fn typeset_trait_index(&self, path: &str) -> TraitIndex {
			self.defs.typesets[usize::from(self.typeset_index(path))]
				.trait_index
		}

		fn typeset_supertraits(&self, path: &str) -> &[TraitBound] {
			&self.signatures.trait_supertraits
				[usize::from(self.typeset_trait_index(path))]
		}

		/// `name` is looked up directly against the trait's own member
		/// bindings rather than through `resolve` — trait members aren't
		/// namespace-path-continuable yet (see `DefKind::as_namespace`), so
		/// `Trait::Assoc` isn't a resolvable path in this rewrite so far.
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
			let &member_index =
				trait_def.bindings.get(&BindingKey::ty(symbol)).unwrap_or_else(
					|| {
						panic!(
							"expected `{trait_path}` to have an associated type `{name}`"
						)
					},
				);
			let member = &trait_def.members[usize::from(member_index)];
			let MemberKind::AssociatedType(def_id) = member.kind else {
				panic!("expected `{name}` to be an associated type");
			};
			let Some(&ItemLocation::TraitAssocType(index)) =
				self.signatures.item_lookup.get(&def_id)
			else {
				panic!("expected a TraitAssocType location for `{name}`");
			};
			&self.signatures.assoc_types[usize::from(index)]
		}

		fn type_alias(&self, path: &str) -> &TypeAliasSignature {
			let DefKind::TypeAlias(def_id) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a type alias");
			};
			let Some(&ItemLocation::TypeAlias(index)) =
				self.signatures.item_lookup.get(&def_id)
			else {
				panic!("expected a TypeAlias location for `{path}`");
			};
			&self.signatures.type_aliases[usize::from(index)]
		}

		fn struct_signature(&self, path: &str) -> &StructSignature {
			let DefKind::Struct(def_id) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be a struct");
			};
			let Some(&ItemLocation::Struct(index)) =
				self.signatures.item_lookup.get(&def_id)
			else {
				panic!("expected a Struct location for `{path}`");
			};
			&self.signatures.structs[usize::from(index)]
		}

		fn enum_signature(&self, path: &str) -> &EnumSignature {
			let DefKind::Enum(namespace_idx) =
				self.resolve(BindingNamespace::Type, path)
			else {
				panic!("expected `{path}` to be an enum");
			};
			let NamespaceKind::Enum(index) =
				self.defs.namespaces[usize::from(namespace_idx)].kind
			else {
				unreachable!("an enum's own binding always names its Enum namespace")
			};
			&self.signatures.enums[usize::from(index)]
		}

		fn function_signature(&self, path: &str) -> &FunctionSignature {
			let DefKind::Function(def_id) =
				self.resolve(BindingNamespace::Value, path)
			else {
				panic!("expected `{path}` to be a function");
			};
			let Some(&ItemLocation::Function(index)) =
				self.signatures.item_lookup.get(&def_id)
			else {
				panic!("expected a Function location for `{path}`");
			};
			&self.signatures.functions[usize::from(index)]
		}
	}

	#[test]
	fn unbounded_params_resolve_with_no_diagnostics() {
		let case = TestCase::new("type A<T, U> = T;");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let type_params = &case.type_alias("A").type_params;
		assert_eq!(type_params.len(), 2);
		assert!(type_params.iter().all(|p| p.bounds.is_empty()));
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
				owner: alias.def_id,
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
	fn impl_headers_use_defs_indices_and_resolve_targets_through_aliases() {
		let case = TestCase::new(indoc! {"
			trait Tr {}
			impl Tr for Alias {}
			impl Alias {}
			type Alias = S;
			struct S {}
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
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
			trait_header.trait_ref.unwrap().inner,
			case.trait_index("Tr")
		);
		assert_eq!(trait_header.target.inner, case.type_alias("Alias").target);
		assert_eq!(inherent_header.target.inner, trait_header.target.inner);
		assert!(matches!(
			case.signatures.types.resolve(trait_header.target.inner),
			Type::Struct { .. }
		));
		let target = ImplTarget::from_type(
			case.signatures.types.resolve(trait_header.target.inner),
		)
		.unwrap();
		assert_eq!(case.signatures.inherent_candidates(target).len(), 1);
		assert_eq!(case.signatures.trait_candidates(target).len(), 1);
		assert_eq!(
			case.signatures.trait_candidates(target)[0].0,
			case.trait_index("Tr")
		);
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
		assert_eq!(header.type_params.len(), 1);
		assert_eq!(header.type_params[0].bounds.len(), 1);
		assert_eq!(
			header.type_params[0].bounds[0].trait_index,
			case.trait_index("Bound")
		);
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
		assert!(header.trait_ref.is_none());
		assert!(matches!(
			case.signatures.types.resolve(header.target.inner),
			Type::Struct { .. }
		));
	}

	#[test]
	fn inherent_impl_header_recovers_an_infer_target() {
		let source = "impl _ {}";
		let case = TestCase::new(source);

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::InferInSignature.code())
		);
		assert_eq!(&source[case.diagnostics[0].labels[0].range.clone()], "_");
		assert_eq!(
			case.signatures.inherent_impls[0]
				.as_ref()
				.unwrap()
				.target
				.inner,
			TypeIndex::ERROR
		);
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

		let type_params = &case.type_alias("A").type_params;
		assert_eq!(type_params.len(), 2, "a duplicate name isn't dropped");
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
		assert_eq!(case.type_alias("A").type_params[0].bounds.len(), 1);
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

		assert_eq!(case.type_alias("A").type_params[0].bounds.len(), 0);
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
			Some(DiagnosticCode::CyclicSupertrait.code())
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
			Some(DiagnosticCode::CyclicSupertrait.code())
		);
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
		assert_eq!(signature.type_params.len(), 1);
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
			Some(DiagnosticCode::DuplicateDefinition.code())
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
			case.assoc_type_signature("Container", "Item").bounds.is_empty()
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
		let bounds = &case.assoc_type_signature("Container", "Item").bounds;
		assert_eq!(bounds.len(), 2);
		assert_eq!(bounds[0].trait_index, case.trait_index("Bound1"));
		assert_eq!(bounds[1].trait_index, case.trait_index("Bound2"));
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
			case.assoc_type_signature("Container", "Item").bounds.is_empty()
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
		let bounds = &case.function_signature("f").type_params[0].bounds;
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].trait_index, case.trait_index("Memory"));
		assert_eq!(bounds[0].bindings.len(), 1);
		assert!(matches!(
			bounds[0].bindings[0].kind,
			AssocBindingKind::Equals(TypeIndex::I32)
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
		let bounds = &case.function_signature("f").type_params[0].bounds;
		assert_eq!(bounds.len(), 1);
		assert_eq!(bounds[0].bindings.len(), 1);
		let AssocBindingKind::Bound(rhs_bounds) = &bounds[0].bindings[0].kind
		else {
			panic!("expected a `Bound` binding kind");
		};
		assert_eq!(rhs_bounds.len(), 1);
		assert_eq!(rhs_bounds[0].trait_index, case.trait_index("Unsigned"));
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
		let bounds = &case.function_signature("f").type_params[0].bounds;
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
		let bounds = &case.function_signature("f").type_params[0].bounds;
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
		let bounds = &case.function_signature("copy").type_params[0].bounds;
		let AssocBindingKind::Equals(ty) = bounds[0].bindings[0].kind else {
			panic!("expected an `Equals` binding kind");
		};
		assert!(matches!(
			case.signatures.types.resolve(ty),
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
		let bounds = &case.function_signature("f").type_params[0].bounds;
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
		let target =
			ImplTarget::from_type(case.signatures.types.resolve(TypeIndex::U32))
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
		let target =
			ImplTarget::from_type(case.signatures.types.resolve(TypeIndex::U32))
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
		let target =
			ImplTarget::from_type(case.signatures.types.resolve(TypeIndex::U32))
				.unwrap();
		assert_eq!(case.signatures.trait_candidates(target).len(), 1);
	}

	#[test]
	fn a_non_concrete_typeset_member_is_diagnosed() {
		let case = TestCase::new(indoc! {"
			type i32;
			typeset Bad { (i32, i32) }
		"});

		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::InvalidImplTarget.code())
		);
	}
}
