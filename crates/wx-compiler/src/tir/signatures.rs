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
	AstEntry, AstNodeRef, BindingNamespace, DefKind, DefinitionRegistry,
	InherentImplIndex, NamespaceIndex, TraitImplIndex, TraitIndex,
};
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
}

index_newtype!(TypeAliasIndex);

/// A resolved `type Name<...> = TypeExpr;` — including a primitive
/// (`#[intrinsic] pub type u8;`), which is just one with no type params and
/// a `target` that was already known rather than resolved from a body.
struct TypeAliasSignature {
	def_id: DefId,
	name: Spanned<SymbolU32>,
	type_params: Box<[GenericParam]>,
	/// What this alias transparently stands for. `TypeIndex::ERROR` if its
	/// body failed to resolve or closed a cycle.
	target: TypeIndex,
}

struct SignatureRegistry {
	type_aliases: Vec<TypeAliasSignature>,
	/// Each trait's resolved `trait X: Y + Z { ... }` bounds, indexed by the
	/// same `TraitIndex` `defs.traits` already uses — traits need no index
	/// space of their own here, unlike `type_aliases`, since Phase 1 already
	/// has one.
	trait_supertraits: Vec<Box<[TraitBound]>>,
	item_lookup: HashMap<DefId, ItemLocation>,
	types: TypeInterner,
}

/// Where a `DefId`'s data actually lives — one arena per item kind
/// `ensure_signature` can be asked about. `Trait`/`TraitImpl`/`InherentImpl`
/// point into `defs.rs`'s own arenas (Phase 1 already knows everything about
/// them); every other kind points into this module's own
/// `SignatureRegistry`, populated only once that kind's signature actually
/// finishes resolving.
#[derive(Clone, Copy)]
enum ItemLocation {
	Trait(TraitIndex),
	TraitImpl(TraitImplIndex),
	InherentImpl(InherentImplIndex),
	TypeAlias(TypeAliasIndex),
}

/// What `ensure_signature` found. `Cycle` is never stored anywhere — it's a
/// transient signal for whichever call is re-entering a `DefId` still
/// `InProgress` further down the stack; that caller reports the cycle once
/// (using `signature_stack` to know what closed the loop) and substitutes
/// `TypeIndex::ERROR`, then keeps going. Every item in the cycle still
/// reaches its own `Done` normally.
pub(super) enum SignatureStatus {
	Resolved,
	Cycle,
}

/// Cycle detection state for one `DefId`'s demand-driven resolution —
/// mirrors `imports.rs`'s `ResolveStatus`, but without its `Error` variant:
/// a signature always has *some* value once resolution reaches `Done` (a
/// failed piece becomes `TypeIndex::ERROR`, the same recovery-value pattern
/// `BindingTarget::Error` already uses at the identity layer), so there's
/// never a case where `Done` needs a "no value" alternative the way
/// `Resolved(T)` does for imports.
#[derive(Clone, Copy)]
enum ComputeState {
	Pending,
	InProgress,
	Done,
}

/// `ast_index` is this `DefId`'s position in `SignatureBuilder::ast_nodes` —
/// set once, at construction, from `defs.rs`'s parse-order record, so
/// `ensure_signature` never needs a second lookup to find the AST it's
/// supposed to resolve.
struct SignatureEntry {
	ast_index: u32,
	state: ComputeState,
}

/// One in-progress `ensure_signature` frame — mirrors `rustc_query_system`'s
/// `QueryInfo`. `requested_at` is the span of the reference that demanded
/// `def_id`, i.e. "the reason for which this [item] was required"; `None`
/// only for a top-level, non-reference demand (the eventual per-`DefId`
/// driver loop) — `resolve_type` always supplies `Some` when it recurses
/// because of a written reference.
#[derive(Clone, Copy)]
pub(super) struct QueryInfo {
	pub(super) def_id: DefId,
	pub(super) requested_at: Option<SourceSpan>,
}

/// The Phase 2 driver. Holds `defs` — Phase 1's finished output, read-only
/// from here on — plus whatever this phase needs on top of it.
pub(super) struct SignatureBuilder<'ast, 'ctx> {
	diagnostics: &'ctx mut Vec<Diagnostic<FileId>>,
	strings: &'ctx StringInterner,
	defs: &'ctx DefinitionRegistry,
	ast_nodes: &'ast [AstEntry<'ast>],
	stdlib_root: NamespaceIndex,
	item_lookup: HashMap<DefId, ItemLocation>,
	signature_state: HashMap<DefId, SignatureEntry>,
	/// In-progress items, in call order.
	signature_stack: Vec<QueryInfo>,
	types: TypeInterner,
	type_aliases: Vec<TypeAliasSignature>,
	trait_supertraits: Vec<Box<[TraitBound]>>,
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

		// Empty until each trait's own `ensure_signature` call fills its
		// slot in; a plain empty slice rather than `Option` since nothing
		// reads one before its owning trait reaches `Done`.
		let trait_supertraits: Vec<Box<[TraitBound]>> =
			defs.traits.iter().map(|_| Box::default()).collect();

		let mut item_lookup = HashMap::new();
		for (index, trait_def) in defs.traits.iter().enumerate() {
			item_lookup.insert(
				trait_def.def_id,
				ItemLocation::Trait(TraitIndex::new(u32::try_from(index).unwrap())),
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

		let mut signature_state: HashMap<DefId, SignatureEntry> = ast_nodes
			.iter()
			.enumerate()
			.map(|(index, entry)| {
				(
					entry.def_id,
					SignatureEntry {
						ast_index: u32::try_from(index).unwrap(),
						state: ComputeState::Pending,
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
			let Some(entry) = signature_state.get_mut(&def_id) else {
				continue;
			};
			entry.state = ComputeState::Done;

			let index = TypeAliasIndex::new(
				u32::try_from(type_aliases.len()).unwrap(),
			);
			type_aliases.push(TypeAliasSignature {
				def_id,
				name: item_name(ast_nodes, &signature_state, def_id),
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
			signature_state,
			signature_stack: Vec::new(),
			types: TypeInterner::new(),
			type_aliases,
			trait_supertraits,
		}
	}

	/// Resolves one item's whole `<...>` parameter list: the duplicate-name
	/// check moved here from `defs.rs`'s prescan (see the module doc
	/// comment), plus each parameter's own bounds.
	pub(super) fn resolve_generic_params(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		ast_params: &[ast::TypeParam],
	) -> Box<[GenericParam]> {
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

			let bounds = match &ast_param.bounds {
				Some(bound) => self.resolve_bounds(file_id, namespace, bound),
				None => Box::new([]),
			};

			params.push(GenericParam {
				name: ast_param.name,
				accesses: Vec::new(),
				bounds,
			});
		}
		params.into_boxed_slice()
	}

	/// The demand-driven driver: computes `def_id`'s signature if it hasn't
	/// been already. The two checks below are safe to return early from —
	/// nothing has been pushed onto `signature_stack` yet at that point.
	/// Past that, no early `return`: `signature_stack`'s frame has to pop
	/// and `state` has to reach `Done` no matter which arm runs below, or
	/// `def_id` is left `InProgress` forever.
	pub(super) fn ensure_signature(&mut self, query: QueryInfo) -> SignatureStatus {
		let def_id = query.def_id;
		match self.signature_state[&def_id].state {
			ComputeState::Done => return SignatureStatus::Resolved,
			ComputeState::InProgress => return SignatureStatus::Cycle,
			ComputeState::Pending => {}
		}

		self.signature_state.get_mut(&def_id).unwrap().state =
			ComputeState::InProgress;
		self.signature_stack.push(query);

		let ast_index = self.signature_state[&def_id].ast_index;
		let ast_nodes = self.ast_nodes;
		let entry = &ast_nodes[ast_index as usize];
		let file_id = entry.file_id;
		let namespace = entry.namespace;
		let node = entry.node.clone();

		match node {
			AstNodeRef::TypeAlias { item } => {
				let ast::Item::TypeAlias {
					name, type_params, body, ..
				} = item
				else {
					unreachable!()
				};
				let body = body.as_ref().expect(
					"bodiless type aliases are already Done before construction finishes",
				);

				let resolved_params =
					self.resolve_generic_params(file_id, namespace, type_params);
				let target =
					self.resolve_type(file_id, namespace, def_id, &resolved_params, body);

				let index = TypeAliasIndex::new(
					u32::try_from(self.type_aliases.len()).unwrap(),
				);
				self.type_aliases.push(TypeAliasSignature {
					def_id,
					name: *name,
					type_params: resolved_params,
					target,
				});
				self.item_lookup.insert(def_id, ItemLocation::TypeAlias(index));
			}
			AstNodeRef::Trait { trait_index, item } => {
				let ast::Item::Trait { supertraits, .. } = item else {
					unreachable!()
				};

				let bounds = match supertraits {
					Some(bound) => self.resolve_bounds(file_id, namespace, bound),
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
						let diagnostic =
							self.report_cyclic_supertrait(super_def_id, reference);
						self.diagnostics.push(diagnostic);
					}
				}

				self.trait_supertraits[usize::from(trait_index)] = bounds;
			}
			_ => todo!("this item kind's signature isn't implemented yet"),
		}

		self.signature_stack.pop();
		self.signature_state.get_mut(&def_id).unwrap().state = ComputeState::Done;
		SignatureStatus::Resolved
	}

	/// Drives `ensure_signature` for every registered item, in parse order —
	/// `ensure_signature`'s own recursion only ever reaches an item when
	/// something else's body references it, so this is the entry point that
	/// reaches everything else: every top-level declaration in the whole
	/// compilation, whether anything happens to reference it yet or not.
	pub(super) fn ensure_all_signatures(&mut self) {
		for entry in self.ast_nodes {
			self.ensure_signature(QueryInfo {
				def_id: entry.def_id,
				requested_at: None,
			});
		}
	}

	/// Freezes everything resolved so far into the dependency-free
	/// [`SignatureRegistry`] — mirrors `DefinitionRegistryBuilder::build`'s
	/// role, just consuming `self` instead of being the constructor itself,
	/// since a `SignatureBuilder` is also the demand-driven driver and stays
	/// alive across many `ensure_signature` calls rather than running once.
	pub(super) fn finish(self) -> SignatureRegistry {
		SignatureRegistry {
			type_aliases: self.type_aliases,
			trait_supertraits: self.trait_supertraits,
			item_lookup: self.item_lookup,
			types: self.types,
		}
	}

	/// Resolves a written type expression to a `TypeIndex`. Only
	/// `TypeExpression::Path` is implemented so far — everything else
	/// (`Pointer`, `Array`, `Function`, `GenericApplication`, ...) is a
	/// `todo!()` until the item kinds that actually need them exist.
	fn resolve_type(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		owner: DefId,
		generic_scope: &[GenericParam],
		type_expr: &Spanned<ast::TypeExpression>,
	) -> TypeIndex {
		match &type_expr.inner {
			ast::TypeExpression::Path(segments) => {
				if let [segment] = &segments[..]
					&& segment.type_args.is_empty()
					&& let Some(param_index) = generic_scope
						.iter()
						.position(|param| param.name.inner == segment.ident.inner)
				{
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
						let reference = SourceSpan::new(file_id, last.ident.span);

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
					_ => todo!(
						"resolving a path to this kind of item isn't implemented yet"
					),
				}
			}
			_ => todo!("this type-expression form isn't implemented yet"),
		}
	}

	/// Builds the diagnostic for a cycle just detected while trying to
	/// re-enter `def_id` (found `InProgress` somewhere on `signature_stack`).
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
	/// Shared by every cycle kind (`CyclicTypeAlias`, `CyclicSupertrait`, ...)
	/// — they differ only in which diagnostic code applies and how to phrase
	/// "why `name` was needed" (`describe`), e.g. `"expanding type alias
	/// \`A\`"` or `"computing the supertraits of \`A\`"`. Callers append their
	/// own closing notes on top of the returned diagnostic.
	fn report_cycle(
		&self,
		def_id: DefId,
		closing_reference: SourceSpan,
		code: DiagnosticCode,
		describe: impl Fn(&str) -> String,
	) -> Diagnostic<FileId> {
		let position = self
			.signature_stack
			.iter()
			.position(|query| query.def_id == def_id)
			.expect("Cycle is only ever returned for a DefId currently in progress");
		let chain = &self.signature_stack[position..];

		let hop_span = |i: usize| -> SourceSpan {
			chain
				.get(i + 1)
				.map(|query| {
					query.requested_at.expect(
						"a non-root frame always records why it was required",
					)
				})
				.unwrap_or(closing_reference)
		};

		let root_name = item_name(self.ast_nodes, &self.signature_state, def_id);
		let root_name_str = self.strings.resolve(root_name.inner).unwrap();

		let mut diagnostic = Diagnostic::error()
			.with_code(code.code())
			.with_message(format!(
				"cycle detected when {}",
				describe(root_name_str)
			))
			.with_label(hop_span(0).primary_label());

		for (i, query) in chain.iter().enumerate().skip(1) {
			let name = item_name(self.ast_nodes, &self.signature_state, query.def_id);
			let name_str = self.strings.resolve(name.inner).unwrap();
			diagnostic = diagnostic.with_label(
				hop_span(i)
					.secondary_label()
					.with_message(format!("...which requires {}...", describe(name_str))),
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

	fn resolve_bounds(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		bound: &Spanned<ast::BoundExpression>,
	) -> Box<[TraitBound]> {
		let mut traits = Vec::new();
		self.collect_bounds(file_id, namespace, bound, &mut traits);
		traits.into_boxed_slice()
	}

	/// `+`-joined bounds flatten into one `Vec` — `T: Add + PartialEq`
	/// produces two `TraitBound`s, not a nested structure mirroring
	/// `BoundList`.
	fn collect_bounds(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		bound: &Spanned<ast::BoundExpression>,
		out: &mut Vec<TraitBound>,
	) {
		match &bound.inner {
			ast::BoundExpression::BoundList(list) => {
				for entry in list.iter() {
					self.collect_bounds(file_id, namespace, entry, out);
				}
			}
			ast::BoundExpression::Path(segments) => {
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
					// Already diagnosed by `resolve_path` itself.
					return;
				};
				match def_key.symbol_kind(self.defs) {
					DefKind::Trait(def_id) => {
						let Some(&ItemLocation::Trait(trait_index)) =
							self.item_lookup.get(&def_id)
						else {
							unreachable!()
						};
						out.push(TraitBound {
							trait_index,
							span: bound.span,
						});
					}
					// A `typeset` bound resolves to its own compiler-generated
					// trait — not modeled here yet, so it falls into the
					// same "expected trait" diagnostic as any other
					// non-trait path for now.
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
					}
				}
			}
			ast::BoundExpression::WithBindings { .. } => {
				todo!(
					"associated-type bindings in bounds (`Trait where {{ Assoc = T }}`) — not yet implemented"
				)
			}
		}
	}
}

/// The written name of `def_id`'s own declaration — reads Phase 1's prescan
/// record directly, since this needs to work even for an item that hasn't
/// finished resolving yet (a cycle's participants never do), or, in
/// `SignatureBuilder::new`'s primitive pre-pass, before a `SignatureBuilder`
/// exists at all to call a method on.
fn item_name(
	ast_nodes: &[AstEntry],
	signature_state: &HashMap<DefId, SignatureEntry>,
	def_id: DefId,
) -> Spanned<SymbolU32> {
	let ast_index = signature_state[&def_id].ast_index;
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
		_ => todo!("naming this item kind isn't implemented yet"),
	}
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
		registry: SignatureRegistry,
	}

	impl TestCase {
		/// `source` plays the stdlib's own role (`set_stdlib`, the same
		/// mechanism a real `"type": "std"` package uses) instead of loading
		/// the real ~250-line embedded stdlib: `ensure_all_signatures` isn't
		/// selective about which item kinds it drives, so any real stdlib
		/// content — almost entirely `fn`/`trait`/`impl`, none of which
		/// `ensure_signature` dispatches yet — would panic on its first
		/// non-`TypeAlias` item before a test even runs. A test that needs a
		/// primitive declares its own bodiless `pub type i32;` — no
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

			let mut signature_builder = SignatureBuilder::new(
				&mut diagnostics,
				&graph.strings,
				&defs,
				&ast_nodes,
				graph.stdlib_package,
			);
			signature_builder.ensure_all_signatures();
			let registry = signature_builder.finish();

			TestCase {
				graph,
				defs,
				diagnostics,
				registry,
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
		fn resolve(&self, path: &str) -> DefKind {
			let root = self.defs.package_namespaces[self.graph.root_package.as_usize()];
			let file_id = self.defs.namespaces[usize::from(root)].file_id;
			let stdlib_root =
				self.defs.package_namespaces[self.graph.stdlib_package.as_usize()];

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
				BindingNamespace::Type,
			);
			let def_key = target
				.def_key()
				.unwrap_or_else(|| panic!("expected `{path}` to resolve: {scratch:?}"));
			def_key.symbol_kind(&self.defs)
		}

		fn trait_index(&self, path: &str) -> TraitIndex {
			let DefKind::Trait(def_id) = self.resolve(path) else {
				panic!("expected `{path}` to be a trait");
			};
			let Some(&ItemLocation::Trait(index)) = self.registry.item_lookup.get(&def_id)
			else {
				panic!("expected a Trait location for `{path}`");
			};
			index
		}

		fn trait_supertraits(&self, path: &str) -> &[TraitBound] {
			&self.registry.trait_supertraits[usize::from(self.trait_index(path))]
		}

		fn type_alias(&self, path: &str) -> &TypeAliasSignature {
			let DefKind::TypeAlias(def_id) = self.resolve(path) else {
				panic!("expected `{path}` to be a type alias");
			};
			let Some(&ItemLocation::TypeAlias(index)) =
				self.registry.item_lookup.get(&def_id)
			else {
				panic!("expected a TypeAlias location for `{path}`");
			};
			&self.registry.type_aliases[usize::from(index)]
		}
	}

	#[test]
	fn unbounded_params_resolve_with_no_diagnostics() {
		let case = TestCase::new("type A<T, U> = T;");

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		let type_params =
			&case.type_alias("A").type_params;
		assert_eq!(type_params.len(), 2);
		assert!(type_params.iter().all(|p| p.bounds.is_empty()));
	}

	#[test]
	fn duplicate_param_name_is_reported_but_both_entries_survive() {
		let case = TestCase::new("type A<T, T> = T;");

		let type_params =
			&case.type_alias("A").type_params;
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
		assert_eq!(
			case.type_alias("A").type_params[0]
				.bounds
				.len(),
			1
		);
	}

	#[test]
	#[ignore = "ensure_all_signatures panics on this source's own `struct` \
	            declaration — Struct isn't dispatched in ensure_signature yet. \
	            Re-enable once that arm lands."]
	fn a_bound_naming_a_non_trait_is_rejected() {
		let case = TestCase::new(indoc! {"
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

		assert_eq!(
			case.type_alias("A").type_params[0]
				.bounds
				.len(),
			0
		);
		assert_eq!(case.diagnostics.len(), 1, "{:?}", case.diagnostics);
		assert_eq!(
			case.diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::UndeclaredIdentifier.code())
		);
	}

	#[test]
	fn type_aliases_to_primitives_resolve_to_the_primitive() {
		let case = TestCase::new(indoc! {"
			pub type i32;
			pub type bool;
			pub type char;

			type A = i32;
			type B = bool;
			type C = char;
		"});

		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
		assert_eq!(
			case.type_alias("A").target,
			TypeIndex::I32
		);
		assert_eq!(
			case.type_alias("B").target,
			TypeIndex::BOOL
		);
		assert_eq!(
			case.type_alias("C").target,
			TypeIndex::CHAR
		);
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
}
