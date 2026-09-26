//! Resolves `use` imports demand-driven and memoized against cycles, once
//! `defs.rs`'s prescan has populated every namespace's bindings and every
//! `use` item/path segment.

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{Spanned, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	small_vec::SmallVec,
	tir::defs::{DefKind, EnumDef, ImportDef, ModuleDef},
	vfs::FileId,
};

use super::defs::{
	Binding, BindingKey, BindingLookup, BindingTarget, DefKey,
	DuplicateDefinitionDiagnostic, GlobImport, Namespace, NamespaceIdx,
	NamespaceLookup, UseItemDef, UseItemIndex, UseItemKind, UsePathIndex,
	UsePathSegment, Visibility,
};

/// Outcome of looking up one `BindingKey` slot for a `use` leaf's target
/// name. Kept distinct from a plain `Option<DefKey>` so the caller can
/// tell "nothing by this name here" apart from "something's here, but not
/// visible" — resolution proceeds either way (both carry the `DefKey`),
/// but only `Absent` means there's truly nothing to install.
#[derive(Clone, Copy)]
enum ImportSlot {
	Accessible(DefKey, Visibility),
	Inaccessible(DefKey, Visibility),
	/// No binding for this key at all — genuinely nothing by this name.
	Absent,
	/// A binding exists, but it's an `Error`-recovery placeholder from an
	/// earlier failure already diagnosed elsewhere. Kept distinct from
	/// `Absent` so a consulting `use` item knows not to report "not
	/// found" a second time for the same underlying problem — see its
	/// use in `compute_import_item`.
	Errored,
}

impl ImportSlot {
	/// The `BindingTarget` a local binding should install for this slot,
	/// paired with the consulted binding's own visibility — needed to cap
	/// the new binding's visibility (see [`Visibility::cap`]), so a `pub
	/// use` can't escalate a private item's reach. `None` when there's
	/// nothing to install at all.
	fn resolved(self) -> Option<(BindingTarget, Visibility)> {
		match self {
			Self::Accessible(key, visibility) => {
				Some((BindingTarget::Accessible(key), visibility))
			}
			Self::Inaccessible(key, visibility) => {
				Some((BindingTarget::Inaccessible(key), visibility))
			}
			Self::Absent | Self::Errored => None,
		}
	}
}

#[derive(Clone, Copy)]
enum ResolveStatus<T> {
	Pending,
	Resolving,
	Resolved(T),
	Error,
}

enum ResolveStep<T> {
	Ready(Result<T, ()>),
	/// This slot was still `Resolving` — a cycle just closed. Unlike
	/// `Ready(Err(()))`, nobody has reported this yet; the caller must.
	Cycle,
	Proceed,
}

impl<T: Copy> ResolveStatus<T> {
	/// `Ready`/`Cycle` short-circuit the caller. `Proceed` means the slot
	/// has been marked `Resolving` — a re-entrant `poll` on it now sees the
	/// cycle.
	fn poll(&mut self) -> ResolveStep<T> {
		match *self {
			Self::Resolved(v) => ResolveStep::Ready(Ok(v)),
			Self::Error => ResolveStep::Ready(Err(())),
			Self::Resolving => {
				*self = Self::Error;
				ResolveStep::Cycle
			}
			Self::Pending => {
				*self = Self::Resolving;
				ResolveStep::Proceed
			}
		}
	}

	/// Settles a slot that was `Proceed`d on, from the result of doing the
	/// actual work, and hands that same result back.
	fn finish(&mut self, result: Result<T, ()>) -> Result<T, ()> {
		*self = match result {
			Ok(v) => Self::Resolved(v),
			Err(()) => Self::Error,
		};
		result
	}
}

/// Everything import resolution needs, split out of
/// `DefinitionRegistryBuilder` along the line that actually matters here:
/// `namespaces` (bindings get inserted into it) and `diagnostics` are still
/// mutated; `use_items`/`use_paths`/`pending_named_imports` are frozen by
/// the time this phase runs. Storing the frozen parts as borrows (not the
/// owned `Vec`/`HashMap` fields `DefinitionRegistryBuilder` has) means
/// reading them never competes with the `&mut self` calls that touch
/// `namespaces`/`diagnostics`.
pub(super) struct ImportResolver<'r> {
	diagnostics: &'r mut Vec<Diagnostic<FileId>>,
	strings: &'r StringInterner,
	namespaces: &'r mut [Namespace],

	// these items necessary in order to get namespace by DefKind
	modules: &'r [ModuleDef],
	enums: &'r [EnumDef],
	imports: &'r [ImportDef],

	use_items: &'r [UseItemDef],
	use_paths: &'r [UsePathSegment],
	pending_named_imports:
		&'r HashMap<(NamespaceIdx, SymbolU32), SmallVec<UseItemIndex>>,
	pending_glob_targets: &'r HashMap<NamespaceIdx, SmallVec<UseItemIndex>>,

	path_state: &'r mut [ResolveStatus<NamespaceIdx>],
	item_state: &'r mut [ResolveStatus<()>],
	/// Every `use` item currently being resolved, innermost last — pushed
	/// and popped, generically, by `ensure_import_item` for both named leaves
	/// and globs, in lockstep with `item_state` flipping to/from
	/// `Resolving`. Unlike `item_state`'s flat per-item fact, this
	/// preserves the actual call chain, so `resolve_stack[pos..]` can name
	/// a whole loop, not just report that one exists.
	resolve_stack: Vec<UseItemIndex>,
}

impl<'r> ImportResolver<'r> {
	/// Entry point for `DefinitionRegistryBuilder::resolve_imports` — the
	/// only thing `defs.rs` needs to know about this module. Keeps every
	/// other field/method on `ImportResolver` private to this file.
	pub(super) fn resolve_imports(
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		namespaces: &mut [Namespace],
		modules: &[ModuleDef],
		enums: &[EnumDef],
		imports: &[ImportDef],
		use_items: &[UseItemDef],
		use_paths: &[UsePathSegment],
		pending_named_imports: &HashMap<
			(NamespaceIdx, SymbolU32),
			SmallVec<UseItemIndex>,
		>,
		pending_glob_targets: &HashMap<NamespaceIdx, SmallVec<UseItemIndex>>,
	) {
		let mut path_state = vec![ResolveStatus::Pending; use_paths.len()];
		let mut item_state = vec![ResolveStatus::Pending; use_items.len()];
		let mut resolver = ImportResolver {
			diagnostics,
			strings,
			namespaces,
			use_items,
			use_paths,
			enums,
			imports,
			modules,
			pending_named_imports,
			pending_glob_targets,
			path_state: &mut path_state,
			item_state: &mut item_state,
			resolve_stack: Vec::new(),
		};

		// A named leaf installs a real binding; a glob only ever records a
		// lookup-time fallback edge (`Namespace::glob_imports`) plus, if
		// `pub`, chases the target's own `pub` globs so cycles are caught
		// here rather than at some arbitrary later lookup.
		for index in 0..use_items.len() {
			resolver.ensure_import_item(UseItemIndex::new(
				u32::try_from(index).unwrap(),
			));
		}
	}

	fn insert_binding(
		&mut self,
		namespace_idx: NamespaceIdx,
		key: BindingKey,
		binding: Binding,
		span: TextSpan,
	) {
		if self
			.namespaces
			.try_insert_binding(namespace_idx, key, binding)
			.is_err()
		{
			let collision_span = self.namespaces[usize::from(namespace_idx)]
				.bindings
				.get(&key)
				.expect(
					"a rejected insertion must leave the existing binding in place",
				)
				.declaration_span(self.namespaces, self.use_items);
			self.diagnostics.push(
				DuplicateDefinitionDiagnostic {
					strings: self.strings,
					key,
					definitions: (
						collision_span,
						SourceSpan::new(
							self.namespaces[usize::from(namespace_idx)].file_id,
							span,
						),
					),
				}
				.report(),
			);
		}
	}

	fn ensure_import_item(&mut self, index: UseItemIndex) {
		match self.item_state[usize::from(index)].poll() {
			ResolveStep::Ready(_) => return,
			ResolveStep::Cycle => {
				let item = &self.use_items[usize::from(index)];
				let namespace = item.namespace;
				match item.kind {
					UseItemKind::Name { name, alias, .. } => {
						let local_name = alias.unwrap_or(name);
						let visibility = Visibility::from(item.pub_span);

						// `index`'s own (still-paused, outer) call already
						// pushed it here before ever reaching this
						// re-entrant one, so it's always found.
						let pos = self
							.resolve_stack
							.iter()
							.position(|&stacked| stacked == index)
							.expect(
								"an item whose poll() just found itself \
								 Resolving must already be on resolve_stack",
							);
						let diagnostic = self.report_cyclic_import(
							"cyclic import",
							"this import depends on itself",
							&self.resolve_stack[pos..],
						);
						self.diagnostics.push(diagnostic);

						self.insert_binding(
							namespace,
							BindingKey::ty(local_name.inner),
							Binding::import(
								BindingTarget::Error,
								visibility,
								index,
							),
							local_name.span,
						);
						self.insert_binding(
							namespace,
							BindingKey::value(local_name.inner),
							Binding::import(
								BindingTarget::Error,
								visibility,
								index,
							),
							local_name.span,
						);
					}
					// A glob item is never re-entered through this generic
					// path: `compute_glob_import` chases a target's globs
					// through `resolve_stack`, not `ensure_import_item`,
					// checking for re-entrancy itself *before* ever calling
					// back in — see `glob_cycle_is_unsafe`. So by the time
					// `ensure_import_item` would poll a glob item that's
					// already `Resolving`, something upstream failed to
					// guard against it.
					UseItemKind::Glob { .. } => unreachable!(
						"glob cycles are detected and reported via \
						 resolve_stack in compute_glob_import, not here"
					),
				}
				return;
			}
			ResolveStep::Proceed => {}
		}

		self.resolve_stack.push(index);
		self.compute_import_item(index);
		self.resolve_stack.pop();
		let _ = self.item_state[usize::from(index)].finish(Ok(()));
	}

	/// Dispatches to whichever kind `index` actually is — `ensure_import_item`
	/// is the only thing that touches `item_state` and marks the item
	/// resolved once this returns, so both `compute_*` functions below are
	/// free to `return` early on failure.
	fn compute_import_item(&mut self, index: UseItemIndex) {
		let item = &self.use_items[usize::from(index)];
		match item.kind {
			UseItemKind::Name {
				name,
				alias,
				prefix,
			} => self.compute_named_import(index, name, alias, prefix),
			UseItemKind::Glob { path, .. } => {
				self.compute_glob_import(index, path);
			}
		}
	}

	/// The actual named-import resolution logic.
	fn compute_named_import(
		&mut self,
		index: UseItemIndex,
		name: Spanned<SymbolU32>,
		alias: Option<Spanned<SymbolU32>>,
		prefix: Option<UsePathIndex>,
	) {
		let item = &self.use_items[usize::from(index)];
		let namespace = item.namespace;

		let scope = match prefix {
			Some(prefix) => {
				match self.ensure_import_path(namespace, prefix, index) {
					Ok(ns) => ns,
					Err(()) => return,
				}
			}
			// Bare `use foo;` — look up `foo` directly in the writing
			// namespace, same as the first segment of any `use` path.
			None => namespace,
		};

		// Force any not-yet-resolved `use` in `scope` first — it might be
		// a re-export chain that hasn't installed its binding yet:
		//
		//   use inner::helper;
		//   mod inner { pub use other::helper; }
		//
		// Skips its own index: a bare `use foo;` binds under the very
		// key "foo" it then searches for, so without the skip it would
		// always find itself `Resolving` and report a spurious cycle for
		// what's really just "nothing else defines this name" (a genuine
		// cycle still gets caught — that only ever comes from another
		// item's chain looping back, never from this one).
		if let Some(candidates) =
			self.pending_named_imports.get(&(scope, name.inner))
		{
			for candidate in candidates {
				if candidate == index {
					continue;
				}

				if matches!(
					self.item_state[usize::from(candidate)],
					ResolveStatus::Resolving
				) {
					// A concrete type or value already answers this lookup, so
					// re-entering a candidate would create a spurious cycle.
					let bindings =
						&self.namespaces[usize::from(scope)].bindings;
					let has_real_binding = bindings
						.get(&BindingKey::ty(name.inner))
						.is_some_and(|binding| {
							!matches!(binding.target, BindingTarget::Error)
						}) || bindings
						.get(&BindingKey::value(name.inner))
						.is_some_and(|binding| {
							!matches!(binding.target, BindingTarget::Error)
						});
					if has_real_binding {
						continue;
					}
				}

				self.ensure_import_item(candidate);
			}
		}

		let type_def = self.resolve_member_def(
			namespace,
			scope,
			BindingKey::ty(name.inner),
			name.span,
		);
		let value_def = self.resolve_member_def(
			namespace,
			scope,
			BindingKey::value(name.inner),
			name.span,
		);

		let local_name = alias.unwrap_or(name);
		let declared_visibility = Visibility::from(item.pub_span);

		// Nothing usable came out of either namespace — either genuinely
		// nothing by this name exists (`Absent`), or it does but is
		// itself an already-diagnosed `Errored` placeholder. Only the
		// former gets a fresh report, here, at the `use` site — but
		// either way, this item installs its *own* `Error` placeholder
		// under its local name, so a later `use` re-exporting it finds
		// `Errored` too and stays silent, however many hops deep the
		// chain goes, instead of hitting genuine `Absent` again and
		// reporting the same underlying problem a second time.
		if matches!(type_def, ImportSlot::Absent | ImportSlot::Errored)
			&& matches!(value_def, ImportSlot::Absent | ImportSlot::Errored)
		{
			if matches!(type_def, ImportSlot::Absent)
				&& matches!(value_def, ImportSlot::Absent)
			{
				let file_id = self.namespaces[usize::from(namespace)].file_id;
				let diagnostic = self.report_unresolved_import(
					prefix,
					name.inner,
					SourceSpan::new(file_id, name.span),
				);
				self.diagnostics.push(diagnostic);
			}
			self.insert_binding(
				namespace,
				BindingKey::ty(local_name.inner),
				Binding::import(
					BindingTarget::Error,
					declared_visibility,
					index,
				),
				local_name.span,
			);
			self.insert_binding(
				namespace,
				BindingKey::value(local_name.inner),
				Binding::import(
					BindingTarget::Error,
					declared_visibility,
					index,
				),
				local_name.span,
			);
			return;
		}

		if let Some((target, source_visibility)) = type_def.resolved() {
			if declared_visibility == Visibility::Public
				&& source_visibility == Visibility::Private
			{
				let file_id = self.namespaces[usize::from(namespace)].file_id;
				let diagnostic = self.report_private_reexport(
					name.inner,
					SourceSpan::new(file_id, name.span),
				);
				self.diagnostics.push(diagnostic);
			}
			self.insert_binding(
				namespace,
				BindingKey::ty(local_name.inner),
				Binding::import(
					target,
					declared_visibility.cap(source_visibility),
					index,
				),
				local_name.span,
			);
		}
		if let Some((target, source_visibility)) = value_def.resolved() {
			if declared_visibility == Visibility::Public
				&& source_visibility == Visibility::Private
			{
				let file_id = self.namespaces[usize::from(namespace)].file_id;
				let diagnostic = self.report_private_reexport(
					name.inner,
					SourceSpan::new(file_id, name.span),
				);
				self.diagnostics.push(diagnostic);
			}
			self.insert_binding(
				namespace,
				BindingKey::value(local_name.inner),
				Binding::import(
					target,
					declared_visibility.cap(source_visibility),
					index,
				),
				local_name.span,
			);
		}
	}

	/// The actual glob-import resolution logic. Resolves the glob's own
	/// path, then — `pub` or not — forces every glob `target` itself
	/// declares to resolve first, because `indirect_lookup` will walk
	/// straight through this edge into `target`'s own glob edges later,
	/// regardless of either one's visibility. That chase, via
	/// `resolve_stack` rather than `ensure_import_item`'s generic re-entrancy
	/// check, is where a cyclic glob graph is caught — and, unlike a cyclic
	/// named import, *not every* glob cycle is actually dangerous to leave
	/// standing (see `glob_cycle_is_unsafe`), so only the unsafe ones stop
	/// this edge from ever being recorded into `glob_imports` at all.
	/// That's what makes `indirect_lookup`'s own "terminates because a
	/// cycle can't reach here" assumption actually true, instead of merely
	/// hoped for.
	fn compute_glob_import(&mut self, index: UseItemIndex, path: UsePathIndex) {
		let item = &self.use_items[usize::from(index)];
		let namespace = item.namespace;

		let Ok(target) = self.ensure_import_path(namespace, path, index) else {
			return;
		};

		let mut unsafe_cycle = false;
		if let Some(candidates) = self.pending_glob_targets.get(&target) {
			for candidate in candidates {
				// O(1) first: `item_state[candidate] == Resolving` iff
				// `candidate` is on `resolve_stack` right now — the two are
				// pushed/popped in lockstep around the exact same
				// `poll()`/`finish()` window in `ensure_import_item` — so this
				// is exactly as accurate as searching the stack directly,
				// just without walking it for every candidate examined,
				// cyclic or not (the overwhelmingly common case).
				if matches!(
					self.item_state[usize::from(candidate)],
					ResolveStatus::Resolving
				) {
					let pos = self
						.resolve_stack
						.iter()
						.position(|&stacked| stacked == candidate)
						.expect(
							"item_state and resolve_stack are kept in \
							 lockstep, so a Resolving item is always found \
							 here",
						);
					if self.glob_cycle_is_unsafe(&self.resolve_stack[pos..]) {
						let diagnostic = self.report_cyclic_import(
							"cyclic glob import",
							"this glob import depends on itself",
							&self.resolve_stack[pos..],
						);
						self.diagnostics.push(diagnostic);
						unsafe_cycle = true;
					}
					// A safe cycle needs nothing further here: `candidate`
					// is already mid-resolution further up this very
					// stack, and that frame will record its own edge (or
					// not) once it gets back control.
					continue;
				}
				self.ensure_import_item(candidate);
			}
		}

		if unsafe_cycle {
			// Recording this edge would put the exact cycle just diagnosed
			// into `glob_imports` for `indirect_lookup` to walk into later.
			return;
		}
		self.namespaces[usize::from(namespace)]
			.glob_imports
			.push(GlobImport {
				use_item: index,
				namespace: target,
			});
	}

	/// Whether some accessor could actually walk `cycle` forever through
	/// `indirect_lookup` — if not, it's safe to leave the edge that closes
	/// it standing rather than reject it. A `pub` edge is crossable by
	/// any accessor; a `private` edge only by one already inside its
	/// declaring namespace. Two siblings privately glob-importing each
	/// other are safe — no accessor is ever inside both at once:
	///
	///   mod a { use crate::b::*; }
	///   mod b { use crate::a::*; }
	///
	/// Nest one inside the other and it's unsafe — an accessor inside
	/// `inner` is automatically inside `a` too, satisfying both edges:
	///
	///   mod a {
	///       use crate::a::inner::*;
	///       mod inner { use super::*; }
	///   }
	///
	/// Checked with a single running-`deepest` fold rather than a full
	/// pairwise comparison: on a tree, anything ancestor-or-descendant of
	/// a common `deepest` is automatically ancestor-or-descendant of
	/// everything else already folded in, so one incomparable pair
	/// against `deepest` is enough to prove the whole set isn't a chain.
	fn glob_cycle_is_unsafe(&self, cycle: &[UseItemIndex]) -> bool {
		let mut deepest: Option<NamespaceIdx> = None;
		for use_item in cycle.iter().copied() {
			let item = &self.use_items[usize::from(use_item)];
			if item.pub_span.is_some() {
				continue;
			}
			let candidate = item.namespace;
			deepest = Some(match deepest {
				None => candidate,
				Some(deepest)
					if self
						.namespaces
						.namespace_contains(candidate, deepest) =>
				{
					deepest
				}
				Some(deepest)
					if self
						.namespaces
						.namespace_contains(deepest, candidate) =>
				{
					candidate
				}
				// Two private edges on separate branches: no single
				// accessor can be inside both namespaces at once, so this
				// cycle can never actually be walked.
				Some(_) => return false,
			});
		}
		// Either no private edges at all (an all-`pub` cycle, walkable by
		// any accessor), or every private edge's namespace lies on one
		// straight ancestor chain (walkable by `deepest` itself).
		true
	}

	/// A single `BindingKey` slot lookup — deliberately simpler than
	/// `binding_to_import_scope`: the terminal leaf of a `use` can be any
	/// def kind (function, struct, const...), not just a namespace, so
	/// there's no `as_namespace` requirement here, just visibility and
	/// `Def`-ness.
	fn resolve_member_def(
		&mut self,
		accessor: NamespaceIdx,
		scope: NamespaceIdx,
		key: BindingKey,
		span: TextSpan,
	) -> ImportSlot {
		let source_span = SourceSpan::new(
			self.namespaces[usize::from(accessor)].file_id,
			span,
		);

		let (target, visibility) = match self.namespaces.lookup(
			self.use_items,
			accessor,
			scope,
			key,
		) {
			BindingLookup::NotFound => return ImportSlot::Absent,
			BindingLookup::Found(target, visibility) => (target, visibility),
			BindingLookup::Ambiguous(candidates) => {
				let diagnostic = report_ambiguous_identifier(
					self.namespaces,
					self.strings,
					key.symbol,
					source_span,
					&candidates,
				);
				self.diagnostics.push(diagnostic);
				// Every surviving candidate here was already confirmed
				// accessible to `accessor` by `indirect_lookup` — `Public`
				// is just a stand-in that reproduces that same "yes" below,
				// not a claim about its real declared visibility.
				(candidates[0].0, Visibility::Public)
			}
		};
		self.namespaces
			.record_binding_access(scope, key, source_span);

		let slot = match target {
			// Already flagged by an earlier link in a re-export chain —
			// can't become more accessible by being re-exported further.
			BindingTarget::Inaccessible(def_key) => {
				ImportSlot::Inaccessible(def_key, visibility)
			}
			BindingTarget::Accessible(def_key) => {
				if self
					.namespaces
					.is_accessible_from(accessor, scope, visibility)
				{
					ImportSlot::Accessible(def_key, visibility)
				} else {
					// `Inaccessible` exists to defer a check to wherever a
					// binding is next consulted — but this *is* that
					// consult, and we already have the accessor and the
					// def right here, so report it now rather than risk
					// nothing ever consulting this binding again and the
					// problem going unreported. Recover as `Accessible`:
					// having reported it, there's nothing left to defer.
					let diagnostic = report_private_identifier(
						self.namespaces,
						self.strings,
						key.symbol,
						source_span,
						Some(def_key),
					);
					self.diagnostics.push(diagnostic);
					ImportSlot::Accessible(def_key, visibility)
				}
			}
			// An `Error`-recovery placeholder — already diagnosed by
			// whoever caused that, nothing new to report here.
			BindingTarget::Error => ImportSlot::Errored,
		};

		if let ImportSlot::Accessible(def_key, _)
		| ImportSlot::Inaccessible(def_key, _) = slot
		{
			self.namespaces.record_access(def_key, source_span);
		}

		slot
	}

	fn ensure_import_path(
		&mut self,
		origin: NamespaceIdx,
		path: UsePathIndex,
		current_item: UseItemIndex,
	) -> Result<NamespaceIdx, ()> {
		match self.path_state[usize::from(path)].poll() {
			ResolveStep::Ready(result) => return result,
			ResolveStep::Cycle => {
				// A path-segment cycle, not an item cycle — `path_state` is
				// keyed by `UsePathIndex`, which a segment can share across
				// several items (`use a::{b, c};`), so there's no single
				// `resolve_stack` frame to build a full-chain report from.
				let segment = self.use_paths[usize::from(path)];
				let file_id = self.namespaces[usize::from(origin)].file_id;
				let diagnostic = Diagnostic::error()
					.with_code(DiagnosticCode::CyclicImport.code())
					.with_message("cyclic import")
					.with_label(
						SourceSpan::new(file_id, segment.segment.span)
							.primary_label()
							.with_message(
								"import resolution cycles back to itself here",
							),
					);
				self.diagnostics.push(diagnostic);
				return Err(());
			}
			ResolveStep::Proceed => {}
		}

		let result = self.compute_import_path(origin, path, current_item);
		self.path_state[usize::from(path)].finish(result)
	}

	/// The actual path-segment resolution logic, free to `match`/return
	/// however it likes — `ensure_import_path` above is the only thing that
	/// touches `path_state`, and it always feeds this function's result to
	/// `finish`, so nothing here can leave a slot stuck `Resolving`.
	fn compute_import_path(
		&mut self,
		origin: NamespaceIdx,
		path: UsePathIndex,
		current_item: UseItemIndex,
	) -> Result<NamespaceIdx, ()> {
		let segment = self.use_paths[usize::from(path)];
		match segment.parent {
			None => {
				self.binding_to_import_scope(origin, origin, path, current_item)
			}
			// Every segment after the first looks its own name up inside
			// the namespace the previous segment resolved to, rather than
			// `origin` — the first segment is the only one looked up
			// directly in `origin`'s own bindings (the `None` branch above),
			// since there's no prior scope yet to look inside of.
			Some(parent) => {
				let parent_scope =
					self.ensure_import_path(origin, parent, current_item)?;
				self.binding_to_import_scope(
					parent_scope,
					origin,
					path,
					current_item,
				)
			}
		}
	}

	/// Looks up `path`'s own segment in `target_namespace`'s bindings,
	/// records both kinds of access (the binding slot itself, and — if it
	/// points to a real def — the def), and validates it as a walkable
	/// scope. `accessor` is who's asking, for the visibility check and for
	/// `source_span`'s file (a `use` path is always written in one file,
	/// regardless of which namespace each segment resolves into).
	/// `current_item` is whichever `use` item's own resolution is driving
	/// this particular call — needed so the `pending_named_imports` forcing
	/// below can skip it: a path segment can be shared across a `use`
	/// group's branches (`use a::{b, c};`), but at any moment there's
	/// exactly one item whose resolution triggered computing it, and
	/// forcing *that one* would just be forcing itself mid-resolution.
	fn binding_to_import_scope(
		&mut self,
		target_namespace: NamespaceIdx,
		accessor: NamespaceIdx,
		path: UsePathIndex,
		current_item: UseItemIndex,
	) -> Result<NamespaceIdx, ()> {
		let segment = self.use_paths[usize::from(path)];
		let key = BindingKey::ty(segment.segment.inner);

		// Force any not-yet-resolved `use` that might install this exact
		// name first — a path prefix can be a `use`-created alias, not
		// just a direct `mod`, and the two must resolve in either order:
		//
		//   use alias::helper;
		//   use real as alias;
		//   mod real { pub fn helper() {} }
		//
		// Skips `current_item`: `use x::x;` registers itself as a
		// candidate for its own prefix segment "x", so forcing it here
		// would just be forcing this same resolution from inside itself.
		if let Some(candidates) = self
			.pending_named_imports
			.get(&(target_namespace, segment.segment.inner))
		{
			for candidate in candidates {
				if candidate != current_item {
					self.ensure_import_item(candidate);
				}
			}
		}

		let source_span = SourceSpan::new(
			self.namespaces[usize::from(accessor)].file_id,
			segment.segment.span,
		);

		let (target, visibility) = match self.namespaces.lookup(
			self.use_items,
			accessor,
			target_namespace,
			key,
		) {
			BindingLookup::NotFound => {
				let diagnostic = self.report_unresolved_import(
					segment.parent,
					segment.segment.inner,
					source_span,
				);
				self.diagnostics.push(diagnostic);
				return Err(());
			}
			BindingLookup::Found(target, visibility) => (target, visibility),
			BindingLookup::Ambiguous(candidates) => {
				let diagnostic = report_ambiguous_identifier(
					self.namespaces,
					self.strings,
					segment.segment.inner,
					source_span,
					&candidates,
				);
				self.diagnostics.push(diagnostic);
				// Every surviving candidate here was already confirmed
				// accessible to `accessor` by `indirect_lookup` — `Public`
				// is just a stand-in that reproduces that same "yes" below,
				// not a claim about its real declared visibility.
				(candidates[0].0, Visibility::Public)
			}
		};
		self.namespaces.record_binding_access(
			target_namespace,
			key,
			source_span,
		);

		if let BindingTarget::Accessible(def_key)
		| BindingTarget::Inaccessible(def_key) = target
		{
			self.namespaces.record_access(def_key, source_span);
		}

		if !self.namespaces.is_accessible_from(
			accessor,
			target_namespace,
			visibility,
		) {
			// Reported here and now, not deferred like a leaf's
			// `BindingTarget::Inaccessible` — this *is* the reference
			// site, so there's nothing to defer to. Walking continues
			// past it (rather than bailing) so a genuinely separate
			// problem further down the path — the next segment, or the
			// leaf, not existing — still gets its own diagnostic instead
			// of being silently swallowed by this one.
			let diagnostic = report_private_identifier(
				self.namespaces,
				self.strings,
				segment.segment.inner,
				source_span,
				target.def_key(),
			);
			self.diagnostics.push(diagnostic);
		}
		let BindingTarget::Accessible(def_key) = target else {
			return Err(());
		};

		let def = &self.namespaces[usize::from(def_key.namespace_idx)].items
			[usize::from(def_key.def_idx)];
		match def.kind {
			DefKind::Package(package) => {
				Ok(NamespaceIdx::new(package.as_u32()))
			}
			DefKind::Module(module_idx) => {
				Ok(self.modules[usize::from(module_idx)].own_namespace)
			}
			DefKind::Import(import_idx) => {
				Ok(self.imports[usize::from(import_idx)].own_namespace)
			}
			DefKind::Enum(enum_idx) => {
				Ok(self.enums[usize::from(enum_idx)].own_namespace)
			}
			_ => {
				let diagnostic = report_cannot_use_as_namespace(
					self.namespaces,
					self.strings,
					segment.segment.inner,
					source_span,
					def_key,
				);
				self.diagnostics.push(diagnostic);
				Err(())
			}
		}
	}

	/// Reconstructs the literal `::`-joined text of a `use` path prefix, as
	/// the user wrote it, from `path`'s root down to (but not including) the
	/// segment that failed — purely for naming what was searched in a
	/// diagnostic; nothing else needs this text. A bare leaf with no prefix
	/// at all has no `path` to pass here — callers handle that `None` case
	/// themselves, since an empty path has nothing for this to walk.
	fn format_import_path(&self, path: UsePathIndex) -> String {
		let mut segments = Vec::new();
		let mut current = Some(path);
		while let Some(index) = current {
			let segment = self.use_paths[usize::from(index)];
			segments.push(self.strings.resolve(segment.segment.inner).unwrap());
			current = segment.parent;
		}
		segments.reverse();
		segments.join("::")
	}

	fn report_unresolved_import(
		&self,
		prefix: Option<UsePathIndex>,
		name: SymbolU32,
		span: SourceSpan,
	) -> Diagnostic<FileId> {
		let name = self.strings.resolve(name).unwrap();
		let (full_path, label_message) = match prefix {
			Some(prefix) => {
				let prefix_text = self.format_import_path(prefix);
				(
					format!("{prefix_text}::{name}"),
					format!("no `{name}` in `{prefix_text}`"),
				)
			}
			None => (name.to_string(), "not found in this module".to_string()),
		};
		Diagnostic::error()
			.with_code(DiagnosticCode::UnresolvedImport.code())
			.with_message(format!("unresolved import `{full_path}`"))
			.with_label(span.primary_label().with_message(label_message))
	}

	/// The label for one frame of a reported cycle: the source path it's
	/// importing from, not the local name it binds:
	///
	///   mod a { pub use super::b::x; }
	///   mod b { pub use super::a::x; }
	///
	/// Both bind the local name `x`, so showing that would read as
	/// `x -> x -> x`; the source path (`super::b::x`, `super::a::x`) is
	/// what actually tells the two hops apart. A glob has no local name
	/// to fall back on anyway, so this keeps named leaves consistent.
	fn cycle_frame_label(&self, index: UseItemIndex) -> (String, SourceSpan) {
		let item = &self.use_items[usize::from(index)];
		let file_id = self.namespaces[usize::from(item.namespace)].file_id;
		match item.kind {
			UseItemKind::Name { name, prefix, .. } => {
				let leaf = self.strings.resolve(name.inner).unwrap();
				let text = match prefix {
					Some(prefix) => {
						format!("{}::{leaf}", self.format_import_path(prefix))
					}
					None => leaf.to_string(),
				};
				(text, SourceSpan::new(file_id, name.span))
			}
			UseItemKind::Glob { path, span } => {
				let text = format!("{}::*", self.format_import_path(path));
				(text, SourceSpan::new(file_id, span))
			}
		}
	}

	/// Reports a cyclic import, naming every item in the loop rather than
	/// only the edge that happened to close it (mirrors
	/// `report_cyclic_type_dependency`'s use of `sig_stack`, on signature
	/// cycles). Shared by named-leaf and glob cycles, which differ only in
	/// wording, not shape — callers pass `message`/`primary_label`
	/// directly rather than this function reconstructing them from a
	/// flag. `frames` is the cycle as `resolve_stack` recorded it.
	fn report_cyclic_import(
		&self,
		message: &str,
		primary_label: &str,
		frames: &[UseItemIndex],
	) -> Diagnostic<FileId> {
		let (first_text, first_span) = self.cycle_frame_label(frames[0]);
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::CyclicImport.code())
			.with_message(message)
			.with_label(first_span.primary_label().with_message(primary_label));

		let mut texts = Vec::with_capacity(frames.len());
		texts.push(first_text);
		for &frame in &frames[1..] {
			let (text, span) = self.cycle_frame_label(frame);
			diagnostic = diagnostic.with_label(
				span.secondary_label().with_message("through here"),
			);
			texts.push(text);
		}

		// A cycle closes back onto its first item, so that name repeats at
		// the end. Only worth spelling out once two items are involved — a
		// self-referential one is already clear from its single label.
		if texts.len() > 1 {
			diagnostic = diagnostic.with_note(format!(
				"cycle: `{}` -> `{}`",
				texts.join("` -> `"),
				texts[0],
			));
		}

		diagnostic
	}

	fn report_private_reexport(
		&self,
		name: SymbolU32,
		span: SourceSpan,
	) -> Diagnostic<FileId> {
		let name = self.strings.resolve(name).unwrap();
		Diagnostic::error()
			.with_code(DiagnosticCode::PrivateReexport.code())
			.with_message(format!(
				"`{name}` is private, and cannot be re-exported"
			))
			.with_label(span.primary_label())
			.with_note(format!(
				"consider marking `{name}` as `pub` in the imported module"
			))
	}
}

/// Modelled on rustc's E0659: several `pub use path::*;` re-exports supply
/// the same name, and nothing here picks one over another. The labels
/// point at the responsible `pub use` edges, not the ultimate definitions
/// — each definition is perfectly fine on its own, and it's exposing more
/// than one of them under the same name that isn't.
///
/// A free function, not an `ImportResolver` method — `paths.rs`'s general
/// path walker hits the exact same `BindingLookup::Ambiguous` case (rustc
/// reports the same E0659 regardless of whether the ambiguous name was
/// reached through a bare reference, a `use` import, or an arbitrary path
/// segment, verified empirically against all three), and pulls this in
/// from here rather than duplicating it, since ambiguity is fundamentally
/// a glob-import concept that belongs with the rest of import resolution.
pub(super) fn report_ambiguous_identifier(
	namespaces: &[Namespace],
	strings: &StringInterner,
	name: SymbolU32,
	span: SourceSpan,
	candidates: &[(BindingTarget, SourceSpan)],
) -> Diagnostic<FileId> {
	let resolved_name = strings.resolve(name).unwrap();
	let mut diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousIdentifier.code())
		.with_message(format!("`{resolved_name}` is ambiguous"))
		.with_label(span.primary_label().with_message("ambiguous name"));
	for (index, (target, candidate_span)) in candidates.iter().enumerate() {
		let def_key = target.def_key().expect(
			"an ambiguity candidate always carries a real DefKey — \
			 CandidateMerge::push never lets a BindingTarget::Error \
			 become one",
		);
		let noun = namespaces[usize::from(def_key.namespace_idx)].items
			[usize::from(def_key.def_idx)]
		.kind
		.noun();
		let also = if index == 0 { "" } else { "also " };
		diagnostic = diagnostic.with_label(
			candidate_span.secondary_label().with_message(format!(
				"could {also}refer to the {noun} imported here"
			)),
		);
	}
	diagnostic.with_note(format!(
		"consider adding an explicit import of `{resolved_name}` to disambiguate"
	))
}

/// A free function for the same reason `report_ambiguous_identifier` is:
/// `paths.rs` hits the same "resolved, but not visible" case and reuses
/// this rather than duplicating it.
///
/// `def_key` is `Option` so the message can name the item's kind when
/// known (matching rustc's `` struct `Priv` is private ``) — `None` only
/// for a `Found(BindingTarget::Error, _)` reached through an
/// already-errored glob candidate (see `CandidateMerge::push`), which has
/// a `Visibility` to fail the check with but no real item behind it.
pub(super) fn report_private_identifier(
	namespaces: &[Namespace],
	strings: &StringInterner,
	name: SymbolU32,
	span: SourceSpan,
	def_key: Option<DefKey>,
) -> Diagnostic<FileId> {
	let name = strings.resolve(name).unwrap();
	let noun = def_key.map(|def_key| {
		namespaces[usize::from(def_key.namespace_idx)].items
			[usize::from(def_key.def_idx)]
		.kind
		.noun()
	});
	let message = match noun {
		Some(noun) => format!("{noun} `{name}` is private"),
		None => format!("`{name}` is private"),
	};
	Diagnostic::error()
		.with_code(DiagnosticCode::PrivateItem.code())
		.with_message(message)
		.with_label(span.primary_label().with_message("this item is not `pub`"))
}

/// A free function for the same reason its siblings above are: `paths.rs`'s
/// general path walker hits this too (a segment resolved to something
/// real, but there are more segments after it and it isn't a namespace).
///
/// `imports.rs`'s call site is a permanent fact about `use` paths — they
/// can only ever traverse namespace-graph entries. `paths.rs`'s is only
/// provisional: it stops being automatically fatal once `impls.rs`'s
/// dispatch tables let a caller try member-lookup first. That's a
/// difference in whether a caller invokes this at all, not in what it says
/// once it does — hence one function, not two.
///
/// `def_key` is required, not `Option`, unlike `report_private_identifier`:
/// both call sites already know they have a real item in hand (a
/// `BindingTarget::Error` mid-path is handled — or skipped — before either
/// one gets here).
pub(super) fn report_cannot_use_as_namespace(
	namespaces: &[Namespace],
	strings: &StringInterner,
	name: SymbolU32,
	span: SourceSpan,
	def_key: DefKey,
) -> Diagnostic<FileId> {
	let name = strings.resolve(name).unwrap();
	let noun = namespaces[usize::from(def_key.namespace_idx)].items
		[usize::from(def_key.def_idx)]
	.kind
	.noun();
	Diagnostic::error()
		.with_code(DiagnosticCode::CannotUseAsNamespace.code())
		.with_message(format!("cannot use {noun} `{name}` as a namespace"))
		.with_label(span.primary_label())
}

#[cfg(test)]
mod tests {
	use indoc::indoc;

	use super::*;
	use crate::tir::defs::DefinitionRegistry;
	use crate::vfs;

	/// Small, `use`-resolution-only duplicate of `defs::tests::TestCase` —
	/// kept separate rather than shared across the two files so each test
	/// module stays self-contained; see the two files' own tests for the
	/// scanning-focused cases this one doesn't need to cover
	/// (`new_multi_file`, direct `.defs`/`.graph` access).
	struct TestCase {
		graph: vfs::CompilationUnit,
		defs: DefinitionRegistry,
		diagnostics: Vec<Diagnostic<FileId>>,
	}

	impl TestCase {
		fn from_graph(mut graph: vfs::CompilationUnit) -> Self {
			let mut diagnostics = Vec::new();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				graph.stdlib_package,
			);
			// Only Phase 1 (defs.rs + this module) is under test here —
			// `ast_nodes` is Phase 2's input, and dropping it now is what
			// lets `defs` (and `graph`, moved below) outlive this
			// constructor with no lingering borrow between them.
			drop(ast_nodes);

			TestCase {
				graph,
				defs,
				diagnostics,
			}
		}

		fn new(source: &str) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			builder.load_stdlib();
			let root_id = builder
				.load_binary(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)])),
				)
				.unwrap();
			Self::from_graph(builder.build(root_id))
		}

		fn new_workspace(
			entry_path: vfs::AbsolutePath,
			workspace: HashMap<vfs::AbsolutePath, String>,
		) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			builder.load_stdlib();
			let root_id = builder
				.load_binary(
					entry_path,
					&vfs::VirtualFileSource::new(workspace),
				)
				.unwrap();
			Self::from_graph(builder.build(root_id))
		}

		fn root_namespace(&self) -> NamespaceIdx {
			self.graph.root_package.root_namespace()
		}

		fn diagnostics(&self) -> crate::testing::DiagnosticView<'_> {
			crate::testing::DiagnosticView::new(
				"prescan",
				&self.diagnostics,
				&self.graph.files,
			)
		}

		fn lookup_type(
			&mut self,
			namespace: NamespaceIdx,
			name: &str,
		) -> Option<BindingTarget> {
			let symbol = self.graph.strings.get_or_intern(name);
			self.defs.namespaces[usize::from(namespace)]
				.bindings
				.get(&BindingKey::ty(symbol))
				.map(|binding| binding.target)
		}

		fn lookup_value(
			&mut self,
			namespace: NamespaceIdx,
			name: &str,
		) -> Option<BindingTarget> {
			let symbol = self.graph.strings.get_or_intern(name);
			self.defs.namespaces[usize::from(namespace)]
				.bindings
				.get(&BindingKey::value(symbol))
				.map(|binding| binding.target)
		}

		/// Follows a bound name to the namespace it names — e.g. the
		/// namespace a `mod inner { ... }` or `mod inner;` declares.
		fn child_namespace(
			&mut self,
			namespace: NamespaceIdx,
			name: &str,
		) -> NamespaceIdx {
			let target = self
				.lookup_type(namespace, name)
				.unwrap_or_else(|| panic!("`{name}` should be bound"));
			let BindingTarget::Accessible(def_key) = target else {
				panic!("`{name}` should be accessible here");
			};
			let kind = self.defs.namespaces[usize::from(def_key.namespace_idx)]
				.items[usize::from(def_key.def_idx)]
			.kind;
			self.defs.namespace_of(kind).unwrap_or_else(|| {
				panic!("`{name}` is not a namespace: {kind:?}")
			})
		}

		/// The namespaces `namespace` glob-imports, in declaration order.
		fn glob_targets(&self, namespace: NamespaceIdx) -> Vec<NamespaceIdx> {
			self.defs.namespaces[usize::from(namespace)]
				.glob_imports
				.iter()
				.map(|glob| glob.namespace)
				.collect()
		}
	}

	#[test]
	fn use_binds_to_the_same_def_as_the_original() {
		let mut case = TestCase::new(indoc! {"
			mod inner {
				pub fn helper() -> i32 { 1 }
			}
			use inner::helper;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let inner = case.child_namespace(root, "inner");
		let Some(BindingTarget::Accessible(original)) =
			case.lookup_value(inner, "helper")
		else {
			panic!("`inner::helper` should resolve directly");
		};
		let Some(BindingTarget::Accessible(imported)) =
			case.lookup_value(root, "helper")
		else {
			panic!("`use inner::helper;` should install a binding at the root");
		};
		assert_eq!(imported, original);
	}

	#[test]
	fn use_resolves_an_enum_variant() {
		let mut case = TestCase::new(indoc! {"
			enum Color { Red, Green, Blue }
			use Color::Red;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let color = case.child_namespace(root, "Color");
		let Some(BindingTarget::Accessible(original)) =
			case.lookup_value(color, "Red")
		else {
			panic!("`Color::Red` should resolve directly");
		};
		let Some(BindingTarget::Accessible(imported)) =
			case.lookup_value(root, "Red")
		else {
			panic!("`use Color::Red;` should install a binding at the root");
		};
		assert_eq!(imported, original);
	}

	/// Every other test in this module resolves within a single virtual
	/// file, same as `mod { ... }` blocks — this pins down that a `use`
	/// target behind a `mod math;` file declaration resolves exactly the
	/// same way across the file boundary.
	#[test]
	fn use_resolves_a_name_declared_in_another_file() {
		let mut case = TestCase::new_workspace(
			vfs::AbsolutePath::new("/main.wx"),
			HashMap::from([
				(
					vfs::AbsolutePath::new("/main.wx"),
					"mod math;\nuse math::add;".to_string(),
				),
				(
					vfs::AbsolutePath::new("/math.wx"),
					"pub fn add() -> i32 { 1 }".to_string(),
				),
			]),
		);
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let math = case.child_namespace(root, "math");
		let Some(BindingTarget::Accessible(original)) =
			case.lookup_value(math, "add")
		else {
			panic!("`math::add` should resolve directly");
		};
		let Some(BindingTarget::Accessible(imported)) =
			case.lookup_value(root, "add")
		else {
			panic!("`use math::add;` should resolve across the file boundary");
		};
		assert_eq!(imported, original);
	}

	#[test]
	fn use_with_alias_binds_under_the_alias_name() {
		let mut case = TestCase::new(indoc! {"
			fn add() -> i32 { 1 }
			use add as sub;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let Some(BindingTarget::Accessible(original)) =
			case.lookup_value(root, "add")
		else {
			panic!("`add` should resolve directly");
		};
		let Some(BindingTarget::Accessible(aliased)) =
			case.lookup_value(root, "sub")
		else {
			panic!("`use add as sub;` should install a binding under `sub`");
		};
		assert_eq!(aliased, original);
	}

	#[test]
	fn use_of_private_item_reports_immediately_and_recovers_as_accessible() {
		let mut case = TestCase::new(indoc! {"
			mod inner {
				fn secret() -> i32 { 1 }
			}
			use inner::secret;
		"});
		// A `use` is itself a reference site with everything needed to
		// check accessibility right now, so privacy is reported here
		// rather than deferred — deferring would risk the problem never
		// being reported at all if nothing else ever consults this
		// binding again.
		case.diagnostics().assert_error_with(
			DiagnosticCode::PrivateItem,
			|diagnostic| {
				assert_eq!(diagnostic.message, "function `secret` is private")
			},
		);

		let root = case.root_namespace();
		match case.lookup_value(root, "secret") {
			Some(BindingTarget::Accessible(_)) => {}
			other => panic!(
				"having already reported the privacy error, `secret` \
				 should recover as Accessible rather than deferring \
				 further, got {other:?}"
			),
		}
	}

	#[test]
	fn use_imports_both_namespaces_when_a_name_occupies_both() {
		let mut case = TestCase::new(indoc! {"
			mod x {
				pub type Y = u32;

				pub fn Y() -> u32 {
					42
				}
			}

			use x::Y;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(
			matches!(
				case.lookup_type(root, "Y"),
				Some(BindingTarget::Accessible(_))
			),
			"the type `Y` should also be imported"
		);
		assert!(
			matches!(
				case.lookup_value(root, "Y"),
				Some(BindingTarget::Accessible(_))
			),
			"the function `Y` should also be imported"
		);
	}

	#[test]
	fn unresolved_leaf_reports_unresolved_import() {
		let case = TestCase::new(indoc! {"
			mod math {
				pub mod inner {
					pub fn helper() -> i32 { 1 }
				}
			}

			use math::inner::add;
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::UnresolvedImport,
			|diagnostic| {
				assert_eq!(
					diagnostic.message,
					"unresolved import `math::inner::add`"
				);
				assert!(
					diagnostic
						.labels
						.iter()
						.any(|label| label.message
							== "no `add` in `math::inner`"),
					"{:#?}",
					diagnostic.labels
				);
			},
		);
	}

	#[test]
	fn reexporting_an_unresolved_import_does_not_report_again() {
		// `nonexistent` fails to resolve once, at its own `use` item —
		// `outer`'s re-export of that same (nonexistent) name should
		// propagate the already-diagnosed error state silently, not
		// produce a second, redundant "unresolved import" diagnostic.
		let case = TestCase::new(indoc! {"
			use nonexistent;

			mod outer {
				pub use super::nonexistent;
			}
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnresolvedImport]);
	}

	#[test]
	fn aliased_reimport_of_an_unresolved_name_does_not_report_again() {
		// Both items search for the same (nonexistent) `undefined` — the
		// alias only changes what *local* name the second one installs,
		// not what it searches for, so it must still find the first
		// item's `Errored` placeholder and stay silent.
		let case = TestCase::new(indoc! {"
			use undefined;
			use undefined as defined;
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnresolvedImport]);
	}

	#[test]
	fn private_segment_does_not_block_a_deeper_unresolved_error() {
		// `inner` is private *and* `add` doesn't exist inside it — walking
		// must not stop at the first problem, so both get reported.
		let case = TestCase::new(indoc! {"
			mod math {
				mod inner {
					pub fn helper() -> i32 { 1 }
				}
			}

			use math::inner::add;
		"});

		case.diagnostics().assert_codes(&[
			DiagnosticCode::PrivateItem,
			DiagnosticCode::UnresolvedImport,
		]);
	}

	#[test]
	fn private_path_segment_reports_private_item() {
		let case = TestCase::new(indoc! {"
			mod outer {
				mod inner {
					pub fn helper() -> i32 { 1 }
				}
			}

			use outer::inner::helper;
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::PrivateItem,
			|diagnostic| {
				assert_eq!(diagnostic.message, "module `inner` is private")
			},
		);
	}

	#[test]
	fn non_module_path_prefix_reports_not_a_namespace() {
		let case = TestCase::new(indoc! {"
			struct Helper { x: i32 }

			use Helper::something;
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::CannotUseAsNamespace,
			|diagnostic| {
				assert_eq!(
					diagnostic.message,
					"cannot use struct `Helper` as a namespace"
				)
			},
		);
	}

	/// Covers three properties of the same mutually-recursive re-export at
	/// once (previously three separate tests, each compiling this identical
	/// fixture on its own): the diagnostic's message, that a cycle does not
	/// also cascade into a spurious "unresolved import" for one of its own
	/// participants while the resolver unwinds it, and that the note names
	/// each hop by its source path (not the shared local name `x`, which
	/// would tell a reader nothing about which `x` is which).
	#[test]
	fn mutually_recursive_reexports_report_cyclic_import() {
		let case = TestCase::new(indoc! {"
			mod a {
				pub use super::b::x;
			}

			mod b {
				pub use super::a::x;
			}
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicImport]);
		case.diagnostics().assert_error_with(
			DiagnosticCode::CyclicImport,
			|diagnostic| {
				assert_eq!(diagnostic.message, "cyclic import");
				assert!(
					diagnostic.notes.iter().any(|note| note
						== "cycle: `super::b::x` -> `super::a::x` -> `super::b::x`"),
					"expected the full chain in a note, got: {:?}",
					diagnostic.notes
				);
			},
		);
	}

	#[test]
	fn direct_definition_anchors_an_apparent_import_cycle() {
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn x() -> i32 { 1 }
				pub use super::b::x;
			}

			mod b {
				pub use super::a::x;
			}
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::DuplicateDefinition]);
	}

	#[test]
	fn pending_import_still_fills_the_other_symbol_namespace() {
		let mut case = TestCase::new(indoc! {"
			use a::X;

			mod a {
				pub fn X() -> i32 { 1 }
				pub use super::source::X;
			}

			mod source {
				pub type X = u32;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(matches!(
			case.lookup_type(root, "X"),
			Some(BindingTarget::Accessible(_))
		));
		assert!(matches!(
			case.lookup_value(root, "X"),
			Some(BindingTarget::Accessible(_))
		));
	}

	/// Both definitions competing here are the local `use` declarations. The
	/// original function in `a` is merely the first import's target and should
	/// not be presented as the previous definition of the local binding.
	#[test]
	fn duplicate_named_import_labels_the_first_use() {
		let source = indoc! {"
			mod a {
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				pub fn pick() -> i32 { 2 }
			}

			use a::pick;
			use b::pick;
		"};
		let case = TestCase::new(source);
		let expected_start =
			source.find("use a::pick").unwrap() + "use a::".len();

		case.diagnostics().assert_error_with(
			DiagnosticCode::DuplicateDefinition,
			|diagnostic| {
				let secondary = diagnostic
					.labels
					.iter()
					.find(|label| {
						label.style
							== codespan_reporting::diagnostic::LabelStyle::Secondary
					})
					.expect(
						"duplicate definition should identify the first binding",
					);
				assert_eq!(secondary.range, expected_start..expected_start + 4);
			},
		);
	}

	#[test]
	fn reexport_chain_of_two_hops_resolves_to_the_original_def() {
		let mut case = TestCase::new(indoc! {"
			mod a {
				mod b {
					pub fn f() -> i32 { 1 }
				}
				pub use b::f;
			}
			use a::f;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let b = case.child_namespace(a, "b");
		let Some(BindingTarget::Accessible(original)) =
			case.lookup_value(b, "f")
		else {
			panic!("`b::f` should resolve directly");
		};
		let Some(BindingTarget::Accessible(reexported)) =
			case.lookup_value(root, "f")
		else {
			panic!("`use a::f;` should resolve through the re-export chain");
		};
		assert_eq!(reexported, original);
	}

	#[test]
	fn self_referential_single_hop_reports_unresolved_not_cyclic() {
		// `super::a` loops straight back to `a` itself, so naively this
		// looks the same as a genuine cycle — but nothing *other* than
		// this very item ever claims to define `x`, so there's no real
		// multi-step dependency loop, just a name that doesn't exist.
		// Matches rustc: this is E0433 ("unresolved import"), not E0391
		// ("cycle detected").
		let case = TestCase::new(indoc! {"
			mod a {
				pub use super::a::x;
			}
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::UnresolvedImport,
			|diagnostic| {
				assert_eq!(
					diagnostic.message,
					"unresolved import `super::a::x`"
				);
			},
		);
	}

	#[test]
	fn self_referential_path_prefix_reports_unresolved_not_cyclic() {
		// Same shape as the leaf-level self-reference above, but through
		// the prefix instead: `x`'s own use item registers itself as a
		// candidate for the prefix segment "x", so forcing it from
		// within `binding_to_import_scope` would force this exact
		// resolution from inside itself — a single unresolvable claim,
		// not a genuine multi-item cycle.
		let case = TestCase::new(indoc! {"
			use x::x;
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnresolvedImport]);
		case.diagnostics().assert_error_with(
			DiagnosticCode::UnresolvedImport,
			|diagnostic| {
				assert_eq!(diagnostic.message, "unresolved import `x`")
			},
		);
	}

	#[test]
	fn use_group_binds_every_name() {
		let mut case = TestCase::new(indoc! {"
			mod math {
				pub fn add() -> i32 { 1 }
				pub fn sub() -> i32 { 2 }
			}
			use math::{add, sub};
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(matches!(
			case.lookup_value(root, "add"),
			Some(BindingTarget::Accessible(_))
		));
		assert!(matches!(
			case.lookup_value(root, "sub"),
			Some(BindingTarget::Accessible(_))
		));
	}

	#[test]
	fn use_before_the_module_it_imports_from_still_resolves() {
		let mut case = TestCase::new(indoc! {"
			use inner::helper;
			mod inner {
				pub fn helper() -> i32 { 1 }
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(matches!(
			case.lookup_value(root, "helper"),
			Some(BindingTarget::Accessible(_))
		));
	}

	#[test]
	fn use_via_self_crate_and_super() {
		let mut case = TestCase::new(indoc! {"
			mod outer {
				pub fn helper() -> i32 { 1 }
				use self::helper as via_self;
				mod inner {
					use super::helper as via_super;
					use crate::outer::helper as via_crate;
				}
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let outer = case.child_namespace(root, "outer");
		let inner = case.child_namespace(outer, "inner");

		assert!(matches!(
			case.lookup_value(outer, "via_self"),
			Some(BindingTarget::Accessible(_))
		));
		assert!(matches!(
			case.lookup_value(inner, "via_super"),
			Some(BindingTarget::Accessible(_))
		));
		assert!(matches!(
			case.lookup_value(inner, "via_crate"),
			Some(BindingTarget::Accessible(_))
		));
	}

	#[test]
	fn import_only_claims_the_namespace_it_occupies() {
		let mut case = TestCase::new(indoc! {"
			fn Y() -> i32 { 1 }

			mod x {
				pub type Y = u32;
			}

			use x::Y;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(
			matches!(
				case.lookup_value(root, "Y"),
				Some(BindingTarget::Accessible(_))
			),
			"the directly-defined value `Y` should be untouched"
		);
		assert!(
			matches!(
				case.lookup_type(root, "Y"),
				Some(BindingTarget::Accessible(_))
			),
			"the imported type `Y` should occupy only the type namespace"
		);
	}

	#[test]
	fn reexport_of_a_public_item_stays_accessible() {
		// Control case — no capping needed here (pub -> pub), so this
		// should already pass and should keep passing once capping exists.
		let mut case = TestCase::new(indoc! {"
			mod inner {
				pub fn helper() -> i32 { 1 }
				pub use helper as public_helper;
			}
			use inner::public_helper;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(
			matches!(
				case.lookup_value(root, "public_helper"),
				Some(BindingTarget::Accessible(_))
			),
			"re-exporting an already-public item should stay accessible"
		);
	}

	#[test]
	fn reexport_cannot_escalate_a_private_items_visibility() {
		// Two independent problems, two diagnostics: `inner`'s own `pub
		// use` of a private item is reported where it's declared (E0364-
		// style), and root's plain `use` of the resulting (still capped
		// private) `public_secret` is *itself* a reference site with
		// everything needed to check accessibility, so it's reported
		// there too rather than silently deferred. Having reported both,
		// each recovers as `Accessible` rather than cascading further.
		let mut case = TestCase::new(indoc! {"
			mod inner {
				fn secret() -> i32 { 1 }
				pub use secret as public_secret;
			}
			use inner::public_secret;
		"});

		case.diagnostics().assert_codes(&[
			DiagnosticCode::PrivateReexport,
			DiagnosticCode::PrivateItem,
		]);

		let root = case.root_namespace();
		assert!(
			matches!(
				case.lookup_value(root, "public_secret"),
				Some(BindingTarget::Accessible(_))
			),
			"having already reported both problems, `public_secret` \
			 should recover as Accessible, found: {:?}",
			case.lookup_value(root, "public_secret")
		);
	}

	#[test]
	fn path_prefix_forward_reference_still_resolves() {
		// `alias` is a `use`-created module alias, not a direct `mod` —
		// unlike a direct declaration (already in place before any `use`
		// resolves, from Phase 1a), an alias only exists once its own
		// `use` item resolves. A path prefix depending on it must force
		// that resolution the same way a leaf name would, regardless of
		// which one appears first in the file.
		let mut case = TestCase::new(indoc! {"
			use alias::helper;
			use real as alias;
			mod real {
				pub fn helper() -> i32 { 1 }
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(matches!(
			case.lookup_value(root, "helper"),
			Some(BindingTarget::Accessible(_))
		));
	}

	#[test]
	fn repeated_unresolved_path_prefix_reports_independently() {
		// Unlike a leaf name, `nonexistent` here is never itself the
		// install target of any `use` item — `foo` and `bar` are — so
		// there's no shared binding slot for one to have already
		// diagnosed on the other's behalf. Each is an independent guess
		// at an unclaimed name, and rustc reports both; there's nothing
		// to propagate.
		let case = TestCase::new(indoc! {"
			use nonexistent::foo;
			use nonexistent::bar;
		"});

		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnresolvedImport,
			DiagnosticCode::UnresolvedImport,
		]);
	}

	#[test]
	fn plain_glob_records_a_fallback_edge_to_its_target() {
		let mut case = TestCase::new(indoc! {"
			mod math {
				pub fn add() -> i32 { 1 }
			}
			use math::*;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let math = case.child_namespace(root, "math");
		assert_eq!(case.glob_targets(root), vec![math]);
		// A plain glob never installs a binding — only the fallback edge.
		assert!(case.lookup_value(root, "add").is_none());
	}

	#[test]
	fn mutually_private_globs_are_not_a_cycle() {
		// Neither `use` is `pub`, so consulting one module's glob target
		// never chases that target's *own* globs — each edge is a leaf.
		// This is the case that would need real fixed-point iteration in
		// a Rust-style resolver; here it's just two independent, harmless
		// facts.
		let mut case = TestCase::new(indoc! {"
			mod a {
				use crate::b::*;
			}

			mod b {
				use crate::a::*;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let b = case.child_namespace(root, "b");
		assert_eq!(case.glob_targets(a), vec![b]);
		assert_eq!(case.glob_targets(b), vec![a]);
	}

	#[test]
	fn self_targeting_pub_glob_reports_cyclic_import() {
		let case = TestCase::new(indoc! {"
			pub use crate::*;
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicImport]);
	}

	#[test]
	fn acyclic_pub_glob_chain_resolves_without_diagnostics() {
		// `c -> b -> a`, a DAG rather than a cycle — resolving `a`'s
		// re-export surface (empty, no further `pub` globs of its own)
		// must not be mistaken for a cycle just because it's reached
		// twice, once via `b` and once via `c`'s recursion into `b`.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub fn helper() -> i32 { 1 }
			}
			mod b {
				pub use crate::a::*;
			}
			mod c {
				pub use crate::b::*;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let b = case.child_namespace(root, "b");
		let c = case.child_namespace(root, "c");
		assert_eq!(case.glob_targets(b), vec![a]);
		assert_eq!(case.glob_targets(c), vec![b]);
	}

	#[test]
	fn named_use_reaches_through_a_pub_glob_reexport() {
		// `b` doesn't define `helper` itself — it only sees it via its own
		// `pub use a::*;` — so `use b::helper;` has to fall through
		// `lookup`'s indirect half to find it at all.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub fn helper() -> i32 { 1 }
			}
			mod b {
				pub use crate::a::*;
			}
			use b::helper;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let Some(BindingTarget::Accessible(original)) =
			case.lookup_value(a, "helper")
		else {
			panic!("`a::helper` should resolve directly");
		};
		let Some(BindingTarget::Accessible(reexported)) =
			case.lookup_value(root, "helper")
		else {
			panic!(
				"`use b::helper;` should resolve through `b`'s own pub glob"
			);
		};
		assert_eq!(reexported, original);
	}

	#[test]
	fn private_glob_reexport_does_not_leak_to_named_use() {
		// Same shape as above, but `b`'s glob isn't `pub` — so `b` can use
		// `helper` in its own body, but nothing outside `b` can reach it
		// through `b`, named or otherwise.
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn helper() -> i32 { 1 }
			}
			mod b {
				use crate::a::*;
			}
			use b::helper;
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnresolvedImport]);
	}

	#[test]
	fn two_pub_globs_disagreeing_on_a_name_report_ambiguous_reexport() {
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				pub fn pick() -> i32 { 2 }
			}
			mod hub {
				pub use crate::a::*;
				pub use crate::b::*;
			}
			use hub::pick;
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AmbiguousIdentifier]);
	}

	#[test]
	fn ambiguous_reexport_names_each_candidates_def_kind() {
		// A function and a constant, not two functions, so the "function"
		// vs "constant" wording is actually exercised.
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				pub const pick: i32 = 2;
			}
			mod hub {
				pub use crate::a::*;
				pub use crate::b::*;
			}
			use hub::pick;
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::AmbiguousIdentifier,
			|diagnostic| {
				let secondary: Vec<_> = diagnostic
					.labels
					.iter()
					.filter(|label| {
						label.style
							== codespan_reporting::diagnostic::LabelStyle::Secondary
					})
					.map(|label| label.message.as_str())
					.collect();
				assert_eq!(
					secondary,
					vec![
						"could refer to the function imported here",
						"could also refer to the constant imported here",
					]
				);
			},
		);
	}

	#[test]
	fn diamond_reexport_through_two_pub_globs_is_not_ambiguous() {
		// `b` and `c` both re-export everything from `a`, and `d` globs
		// both `b` and `c` — the same `a::helper` is reached twice, once
		// via each edge. That's a diamond, not a conflict: both edges name
		// the exact same `DefKey`, so it must collapse into one candidate
		// rather than reading as two re-exports disagreeing on the name.
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn helper() -> i32 { 1 }
			}
			mod b {
				pub use crate::a::*;
			}
			mod c {
				pub use crate::a::*;
			}
			mod d {
				pub use crate::b::*;
				pub use crate::c::*;
			}
			use d::helper;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
	}

	#[test]
	fn broken_glob_edge_does_not_make_a_real_candidate_ambiguous() {
		// `broken` re-exports a name that doesn't exist under the alias
		// `helper`, which installs its own `Error`-recovery placeholder
		// under that key. `d` globs both `a` (the real `helper`) and
		// `broken` (the placeholder) — the placeholder must not read as a
		// second, competing candidate: that would both misreport a
		// perfectly fine `helper` as ambiguous and re-diagnose a problem
		// `broken`'s own `use` already reported.
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn helper() -> i32 { 1 }
			}
			mod broken {
				pub use crate::a::nonexistent_fn as helper;
			}
			mod d {
				pub use crate::a::*;
				pub use crate::broken::*;
			}
			use d::helper;
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnresolvedImport]);
	}

	#[test]
	fn all_glob_edges_broken_does_not_cascade() {
		// Unlike `broken_glob_edge_does_not_make_a_real_candidate_ambiguous`,
		// `hub` here has no real candidate at all — every edge it walks is
		// broken, so `Candidates::Error` has to survive all the way to
		// `finish` as the final result (`Found(Error, _)`, not `NotFound`).
		// If it didn't, `use hub::helper;` would fall through to a second,
		// redundant "unresolved import" diagnostic on top of the one
		// `broken`'s own `use` already reported.
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn something_else() -> i32 { 1 }
			}
			mod broken {
				pub use crate::a::nonexistent_fn as helper;
			}
			mod hub {
				pub use crate::broken::*;
			}
			use hub::helper;
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnresolvedImport]);
	}

	#[test]
	fn private_candidate_does_not_participate_in_ambiguity() {
		// `a::pick` is public, `b::pick` is private — `hub` re-exports both
		// under the same name. Only `a::pick` is a real option for an
		// accessor outside `b`'s own subtree, so this must resolve cleanly
		// to it rather than reporting a spurious ambiguity between a real
		// choice and one that was never actually reachable.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				fn pick() -> i32 { 2 }
			}
			mod hub {
				pub use crate::a::*;
				pub use crate::b::*;
			}
			use hub::pick;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let Some(BindingTarget::Accessible(a_pick)) =
			case.lookup_value(a, "pick")
		else {
			panic!("a::pick should resolve directly");
		};
		let Some(BindingTarget::Accessible(resolved)) =
			case.lookup_value(root, "pick")
		else {
			panic!("hub::pick should resolve to a::pick, not be swallowed");
		};
		assert_eq!(resolved, a_pick);
	}

	#[test]
	fn private_candidate_does_not_participate_in_ambiguity_regardless_of_glob_order()
	 {
		// Same shape as above with the two globs declared in the opposite
		// order — the outcome must not depend on which glob happened to be
		// written (and therefore walked) first. This ordering specifically
		// exercises the case where the unreachable `b::pick` is the first
		// real candidate seen (so it's provisionally kept, deferred, as
		// the sole candidate) and the later, reachable `a::pick` has to
		// *replace* it outright rather than merge into an ambiguity — as
		// opposed to the other test's ordering, where the reachable one
		// arrives first and the unreachable one is simply turned away.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				fn pick() -> i32 { 2 }
			}
			mod hub {
				pub use crate::b::*;
				pub use crate::a::*;
			}
			use hub::pick;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let Some(BindingTarget::Accessible(a_pick)) =
			case.lookup_value(a, "pick")
		else {
			panic!("a::pick should resolve directly");
		};
		let Some(BindingTarget::Accessible(resolved)) =
			case.lookup_value(root, "pick")
		else {
			panic!("hub::pick should resolve to a::pick, not be swallowed");
		};
		assert_eq!(resolved, a_pick);
	}

	#[test]
	fn local_definition_silently_wins_over_a_colliding_pub_glob() {
		// The exact shape from the design discussion: a local `X` must
		// never even trigger a duplicate-definition check against
		// something a glob happens to also offer under the same name.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub const X: i32 = 0;
			}
			pub use a::*;
			const X: i32 = 1;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(matches!(
			case.lookup_value(root, "X"),
			Some(BindingTarget::Accessible(_))
		));
	}

	#[test]
	fn glob_of_unresolved_path_reports_unresolved_import() {
		// A glob's own path is resolved eagerly, same as a named import's —
		// only *ambiguity between candidates* is on-demand, not the path
		// itself. `math` exists but `inner` doesn't, so this must report
		// exactly like the named-import equivalent
		// (`unresolved_leaf_reports_unresolved_import`) does.
		let case = TestCase::new(indoc! {"
			mod math {
				pub fn helper() -> i32 { 1 }
			}

			use math::inner::*;
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::UnresolvedImport,
			|diagnostic| {
				assert_eq!(
					diagnostic.message,
					"unresolved import `math::inner`"
				);
				assert!(
					diagnostic
						.labels
						.iter()
						.any(|label| label.message == "no `inner` in `math`"),
					"{:#?}",
					diagnostic.labels
				);
			},
		);
	}

	#[test]
	fn glob_of_non_module_path_reports_not_a_namespace() {
		// Mirrors `non_module_path_prefix_reports_not_a_namespace`, but for
		// a glob's own path rather than a named leaf's prefix.
		let case = TestCase::new(indoc! {"
			struct Helper { x: i32 }

			use Helper::*;
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::CannotUseAsNamespace,
			|diagnostic| {
				assert_eq!(
					diagnostic.message,
					"cannot use struct `Helper` as a namespace"
				)
			},
		);
	}

	#[test]
	fn named_use_silently_wins_over_a_colliding_pub_glob() {
		// Mirrors `local_definition_silently_wins_over_a_colliding_pub_glob`,
		// but the shadowing declaration is itself a `use` rather than a
		// direct definition. A named `use` and a direct item both install a
		// *direct* binding via `insert_binding`, and `lookup` only ever
		// falls back to a glob's fallback edge when no direct binding
		// exists — so this should resolve to `b::pick` without a
		// duplicate-definition or ambiguity diagnostic, the same way the
		// direct-definition case does.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				pub fn pick() -> i32 { 2 }
			}
			pub use a::*;
			use b::pick;
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let b = case.child_namespace(root, "b");
		let Some(BindingTarget::Accessible(b_pick)) =
			case.lookup_value(b, "pick")
		else {
			panic!("`b::pick` should resolve directly");
		};
		let Some(BindingTarget::Accessible(resolved)) =
			case.lookup_value(root, "pick")
		else {
			panic!(
				"`use b::pick;` should win over the colliding `pub use a::*;`"
			);
		};
		assert_eq!(resolved, b_pick);
	}

	#[test]
	fn unreferenced_ambiguous_glob_names_report_nothing() {
		// Same shape as `two_pub_globs_disagreeing_on_a_name_report_ambiguous_reexport`,
		// but nothing ever consults `hub::pick` — no `use hub::pick;`, no
		// other reference. Ambiguity between glob candidates is only ever
		// computed on demand (inside `resolve_member_def`/
		// `binding_to_import_scope`, both driven by an actual lookup), so
		// two globs merely *disagreeing* on a name, unreferenced, must
		// produce no diagnostic at all — matching rustc, where an ambiguous
		// glob import (E0659) is only ever reported at a use site.
		let case = TestCase::new(indoc! {"
			mod a {
				pub fn pick() -> i32 { 1 }
			}
			mod b {
				pub fn pick() -> i32 { 2 }
			}
			mod hub {
				pub use crate::a::*;
				pub use crate::b::*;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);
	}

	#[test]
	fn three_way_mutual_pub_globs_report_cyclic_import() {
		// Cycle detection is generic per-item `Resolving` state, not
		// pairwise special-cased — worth checking it still finds exactly
		// one cycle, not three (one per participant), once the loop has
		// three hops instead of two.
		let case = TestCase::new(indoc! {"
			mod a {
				pub use crate::b::*;
			}
			mod b {
				pub use crate::c::*;
			}
			mod c {
				pub use crate::a::*;
			}
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicImport]);
	}

	#[test]
	fn use_group_with_glob_branch_binds_every_name() {
		// `scan_use_tree`'s `Group` arm recurses into `Name`, `Path`,
		// `Group` and `Glob` branches alike — this exercises a glob branch
		// sitting alongside a named one in the same group.
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub mod b {
					pub fn helper() -> i32 { 1 }
				}
				pub fn c() -> i32 { 2 }
			}
			use a::{b::*, c};
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		assert!(
			matches!(
				case.lookup_value(root, "c"),
				Some(BindingTarget::Accessible(_))
			),
			"the named branch of the group should install a direct binding"
		);

		let a = case.child_namespace(root, "a");
		let b = case.child_namespace(a, "b");
		assert_eq!(
			case.glob_targets(root),
			vec![b],
			"the glob branch of the group should record its own fallback edge"
		);
	}

	#[test]
	fn nested_self_targeting_pub_glob_reports_cyclic_import() {
		// Extends `self_targeting_pub_glob_reports_cyclic_import` (root
		// only) to a non-root namespace, checking that `self` resolves to
		// the enclosing namespace itself in the general case, not just at
		// the package root.
		let case = TestCase::new(indoc! {"
			mod inner {
				pub use self::*;
			}
		"});

		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicImport]);
	}

	#[test]
	fn self_targeting_private_glob_reports_cyclic_import() {
		// The private counterpart of `self_targeting_pub_glob_reports_cyclic_import`.
		// A self-glob is always a genuine cycle regardless of visibility —
		// `namespace_contains(inner, inner)` trivially holds, so *any*
		// accessor already inside `inner` (including `inner` itself) can
		// walk this edge forever. This used to overflow the stack instead
		// of reaching this diagnostic, since nothing stopped the
		// self-referential edge from ever being recorded.
		let case = TestCase::new(indoc! {"
			mod inner {
				use self::*;
				use undefined_name;
			}
		"});

		case.diagnostics().assert_codes(&[
			DiagnosticCode::CyclicImport,
			DiagnosticCode::UnresolvedImport,
		]);
	}

	#[test]
	fn mutually_pub_globs_do_not_overflow_when_actually_looked_up() {
		// `mutually_pub_globs_report_cyclic_import` only checks that the
		// cycle itself is diagnosed; it never exercises a lookup that would
		// actually walk `glob_imports` through the pair. Doing so used to
		// overflow the stack, because the old pub-only cycle chase reported
		// a diagnostic without ever stopping the cyclic edge from being
		// recorded — `indirect_lookup` had nothing stopping it from walking
		// straight back and forth between `a` and `b` forever.
		let case = TestCase::new(indoc! {"
			mod a {
				pub use crate::b::*;
			}
			mod b {
				pub use crate::a::*;
			}
			use a::whatever;
		"});

		case.diagnostics().assert_codes(&[
			DiagnosticCode::CyclicImport,
			DiagnosticCode::UnresolvedImport,
		]);
	}

	#[test]
	fn nested_mutual_private_globs_report_cyclic_import() {
		// Unlike `mutually_private_globs_are_not_a_cycle`'s siblings, `a`
		// and `inner` here are nested (`inner` is a descendant of `a`) —
		// so an accessor inside `inner` satisfies *both* edges' private
		// containment check at once (`inner` is inside `a`'s subtree, and
		// trivially inside its own), and the walk can loop forever. This
		// is exactly the shape `mutually_private_globs_are_not_a_cycle`
		// deliberately avoids by keeping the two namespaces as siblings.
		let case = TestCase::new(indoc! {"
			mod a {
				use crate::a::inner::*;
				mod inner {
					use super::*;
					use undefined_name;
				}
			}
		"});

		case.diagnostics().assert_codes(&[
			DiagnosticCode::CyclicImport,
			DiagnosticCode::UnresolvedImport,
		]);
	}

	#[test]
	fn sibling_private_globs_still_resolve_a_name_without_overflow() {
		// Extends `mutually_private_globs_are_not_a_cycle` with an actual
		// lookup through the pair (a plain, still-legal case per the
		// language design: sibling private glob cycles are never walkable
		// by any single accessor, so they're deliberately left standing).
		let mut case = TestCase::new(indoc! {"
			mod a {
				use crate::b::*;
				pub fn only_in_a() -> i32 { 1 }
			}
			mod b {
				use crate::a::*;
			}
		"});
		assert!(case.diagnostics.is_empty(), "{:?}", case.diagnostics);

		let root = case.root_namespace();
		let a = case.child_namespace(root, "a");
		let b = case.child_namespace(root, "b");
		assert_eq!(case.glob_targets(a), vec![b]);
		assert_eq!(case.glob_targets(b), vec![a]);
	}

	#[test]
	fn cyclic_named_reexports_report_the_full_loop() {
		// Aliased in both directions — the label shows each frame's
		// *source* path (`super::b::y`, `super::a::x`), not the local
		// name it's renamed to on arrival, since the source is what
		// actually explains the dependency between the two hops.
		let case = TestCase::new(indoc! {"
			mod a {
				pub use super::b::y as x;
			}
			mod b {
				pub use super::a::x as y;
			}
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::CyclicImport,
			|diagnostic| {
				assert!(
					diagnostic.notes.iter().any(|note| note
						== "cycle: `super::b::y` -> `super::a::x` -> `super::b::y`"),
					"expected the full chain in a note, got: {:?}",
					diagnostic.notes
				);
				// One primary label for the item whose re-entrant lookup
				// closed the loop, plus one secondary label per other
				// item in it.
				assert_eq!(
					diagnostic.labels.len(),
					2,
					"expected one label per item in the two-item cycle"
				);
			},
		);
	}

	#[test]
	fn cyclic_glob_reexports_report_the_full_loop() {
		// Direct two-node case. Same shape as a named cycle's diagnostic —
		// one primary label plus one secondary per remaining hop, and a
		// `cycle: ...` note — but with glob-specific wording ("cyclic glob
		// import", "this glob import depends on itself").
		let case = TestCase::new(indoc! {"
			mod a {
				pub use crate::b::*;
			}
			mod b {
				pub use crate::a::*;
			}
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::CyclicImport,
			|diagnostic| {
				assert_eq!(diagnostic.message, "cyclic glob import");

				let primary = diagnostic
					.labels
					.iter()
					.find(|label| {
						label.style
							== codespan_reporting::diagnostic::LabelStyle::Primary
					})
					.expect("expected a primary label");
				assert_eq!(
					primary.message,
					"this glob import depends on itself"
				);

				let secondary: Vec<_> = diagnostic
					.labels
					.iter()
					.filter(|label| {
						label.style
							== codespan_reporting::diagnostic::LabelStyle::Secondary
					})
					.map(|label| label.message.as_str())
					.collect();
				assert_eq!(secondary, vec!["through here"]);

				assert!(
					diagnostic.notes.iter().any(|note| note
						== "cycle: `crate::b::*` -> `crate::a::*` -> `crate::b::*`"),
					"expected the full chain in a note, got: {:?}",
					diagnostic.notes
				);
			},
		);
	}

	#[test]
	fn three_way_cyclic_glob_reexports_report_every_hop() {
		// Extends the direct two-node case to three hops — matches the
		// exact shape requested for the diagnostic: primary label on the
		// glob where the cycle starts/closes, the remaining imports as
		// secondary labels in traversal order, and the starting glob's own
		// target path repeated at the end of the `cycle: ...` note.
		let case = TestCase::new(indoc! {"
			mod a {
				pub use crate::b::*;
			}
			mod b {
				pub use crate::c::*;
			}
			mod c {
				pub use crate::a::*;
			}
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::CyclicImport,
			|diagnostic| {
				assert_eq!(diagnostic.message, "cyclic glob import");

				let primary = diagnostic
					.labels
					.iter()
					.find(|label| {
						label.style
							== codespan_reporting::diagnostic::LabelStyle::Primary
					})
					.expect("expected a primary label");
				assert_eq!(
					primary.message,
					"this glob import depends on itself"
				);

				let secondary: Vec<_> = diagnostic
					.labels
					.iter()
					.filter(|label| {
						label.style
							== codespan_reporting::diagnostic::LabelStyle::Secondary
					})
					.map(|label| label.message.as_str())
					.collect();
				assert_eq!(secondary, vec!["through here", "through here"]);

				assert!(
					diagnostic.notes.iter().any(|note| {
						note == "cycle: `crate::b::*` -> `crate::c::*` -> \
						         `crate::a::*` -> `crate::b::*`"
					}),
					"expected the full chain in a note, got: {:?}",
					diagnostic.notes
				);
			},
		);
	}
}
