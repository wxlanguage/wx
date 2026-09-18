//! Resolves `use` imports demand-driven and memoized against cycles, once
//! `defs.rs`'s prescan has populated every namespace's bindings and every
//! `use` item/path segment.

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::StringInterner,
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	small_vec::SmallVec,
	vfs::FileId,
};

use super::defs::{
	Binding, BindingKey, BindingLookup, BindingTarget, DefKey, DefKind,
	DuplicateDefinitionDiagnostic, GlobImport, Namespace, NamespaceIndex,
	NamespaceLookup, UseItemDef, UseItemIndex, UseItemKind, UsePathIndex,
	UsePathSegment, Visibility,
};

#[derive(Clone, Copy)]
enum ImportScope {
	Namespace(NamespaceIndex),
	// TODO: Enum, Variant etc..
}

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
	/// use in `compute_use_item`.
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
struct ImportResolver<'r> {
	diagnostics: &'r mut Vec<Diagnostic<FileId>>,
	strings: &'r StringInterner,
	namespaces: &'r mut [Namespace],

	use_items: &'r [UseItemDef],
	use_paths: &'r [UsePathSegment],
	pending_named_imports:
		&'r HashMap<(NamespaceIndex, SymbolU32), SmallVec<UseItemIndex>>,
	pending_pub_glob_reexports:
		&'r HashMap<NamespaceIndex, SmallVec<UseItemIndex>>,

	path_state: &'r mut [ResolveStatus<ImportScope>],
	item_state: &'r mut [ResolveStatus<()>],
}

/// Entry point for `DefinitionRegistryBuilder::resolve_use_paths` — the only
/// thing `defs.rs` needs to know about this module. Keeps `ImportResolver`'s
/// fields private to this file rather than exposing the struct itself.
pub(super) fn resolve_use_paths(
	diagnostics: &mut Vec<Diagnostic<FileId>>,
	strings: &StringInterner,
	namespaces: &mut [Namespace],
	use_items: &[UseItemDef],
	use_paths: &[UsePathSegment],
	pending_named_imports: &HashMap<
		(NamespaceIndex, SymbolU32),
		SmallVec<UseItemIndex>,
	>,
	pending_pub_glob_reexports: &HashMap<
		NamespaceIndex,
		SmallVec<UseItemIndex>,
	>,
) {
	let mut path_state = vec![ResolveStatus::Pending; use_paths.len()];
	let mut item_state = vec![ResolveStatus::Pending; use_items.len()];
	ImportResolver {
		diagnostics,
		strings,
		namespaces,
		use_items,
		use_paths,
		pending_named_imports,
		pending_pub_glob_reexports,
		path_state: &mut path_state,
		item_state: &mut item_state,
	}
	.run();
}

impl<'r> ImportResolver<'r> {
	fn run(&mut self) {
		// A named leaf installs a real binding; a glob only ever records a
		// lookup-time fallback edge (`Namespace::glob_imports`) plus, if
		// `pub`, chases the target's own `pub` globs so cycles are caught
		// here rather than at some arbitrary later lookup.
		for (index, _) in self.use_items.iter().enumerate() {
			self.ensure_use_item(UseItemIndex::new(
				u32::try_from(index).unwrap(),
			));
		}
	}

	fn insert_binding(
		&mut self,
		namespace_idx: NamespaceIndex,
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

	fn ensure_use_item(&mut self, index: UseItemIndex) {
		match self.item_state[usize::from(index)].poll() {
			ResolveStep::Ready(_) => return,
			ResolveStep::Cycle => {
				let item = &self.use_items[usize::from(index)];
				let namespace = item.namespace;
				let file_id = self.namespaces[usize::from(namespace)].file_id;
				match item.kind {
					UseItemKind::Name { name, alias, .. } => {
						let local_name = alias.unwrap_or(name);
						let visibility = Visibility::from(item.pub_span);
						let diagnostic = self.report_use_cycle(
							SourceSpan::new(file_id, name.span),
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
					// No binding to poison — a glob never installs one. The
					// cyclic edge just stops contributing further; the
					// plain (non-`pub`) fallback registration, if it
					// already happened, is untouched.
					UseItemKind::Glob { span, .. } => {
						let diagnostic = self
							.report_use_cycle(SourceSpan::new(file_id, span));
						self.diagnostics.push(diagnostic);
					}
				}
				return;
			}
			ResolveStep::Proceed => {}
		}

		self.compute_use_item(index);
		let _ = self.item_state[usize::from(index)].finish(Ok(()));
	}

	/// The actual named-import resolution logic — free to `return` early on
	/// failure, since `ensure_use_item` above is the only thing that
	/// touches `item_state` and marks the item resolved after this returns.
	fn compute_use_item(&mut self, index: UseItemIndex) {
		let item = &self.use_items[usize::from(index)];
		let namespace = item.namespace;
		let (name, alias, prefix) = match item.kind {
			UseItemKind::Name {
				name,
				alias,
				prefix,
			} => (name, alias, prefix),
			UseItemKind::Glob { path, .. } => {
				return self.compute_glob_item(index, path);
			}
		};

		let scope = match prefix {
			Some(prefix) => {
				match self.ensure_use_path(namespace, prefix, index) {
					Ok(ImportScope::Namespace(ns)) => ns,
					Err(()) => return,
				}
			}
			// Bare `use foo;` — look up `foo` directly in the writing
			// namespace, same as the first segment of any `use` path.
			None => namespace,
		};

		// Force any not-yet-resolved `use` in `scope` that could produce
		// this name to resolve first — it might be a re-export chain that
		// hasn't installed its binding into `scope`'s bindings yet. Skips
		// its own index: a bare, unaliased `use foo;` registers itself
		// under the very key it then searches for, so without this it
		// would always find itself as a "candidate" and force itself
		// while still `Resolving`, reporting a spurious cycle for what is
		// really just "nothing else defines this name" (a genuine cycle
		// still gets caught — that self-match only ever comes from
		// another item's own chain looping back, never from this one).
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

				self.ensure_use_item(candidate);
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

	/// The actual glob-import resolution logic. A plain `use path::*;` just
	/// resolves its path and records a lookup-time fallback edge — nothing
	/// else here can fail or cycle, since nothing downstream of it depends
	/// on what it produces. A `pub use path::*;` additionally has to make
	/// the target's own `pub` globs resolve first, because *this*
	/// namespace's re-export surface now includes theirs — and that
	/// recursion, through `ensure_use_item`, is where a genuine re-export
	/// cycle gets caught, via the same cycle detection path resolution
	/// already relies on.
	fn compute_glob_item(&mut self, index: UseItemIndex, path: UsePathIndex) {
		let item = &self.use_items[usize::from(index)];
		let namespace = item.namespace;
		let is_pub = item.pub_span.is_some();

		let Ok(ImportScope::Namespace(target)) =
			self.ensure_use_path(namespace, path, index)
		else {
			return;
		};

		self.namespaces[usize::from(namespace)]
			.glob_imports
			.push(GlobImport {
				use_item: index,
				namespace: target,
			});

		if !is_pub {
			return;
		}
		let Some(candidates) = self.pending_pub_glob_reexports.get(&target)
		else {
			return;
		};
		for candidate in candidates {
			self.ensure_use_item(candidate);
		}
	}

	/// A single `BindingKey` slot lookup — deliberately simpler than
	/// `binding_to_import_scope`: the terminal leaf of a `use` can be any
	/// def kind (function, struct, const...), not just a namespace, so
	/// there's no `DefKind::Namespace` requirement here, just visibility
	/// and `Def`-ness.
	fn resolve_member_def(
		&mut self,
		accessor: NamespaceIndex,
		scope: NamespaceIndex,
		key: BindingKey,
		span: TextSpan,
	) -> ImportSlot {
		let source_span = SourceSpan::new(
			self.namespaces[usize::from(accessor)].file_id,
			span,
		);

		let (target, visibility) = match self.namespaces.lookup(
			self.use_items,
			scope,
			key,
			accessor,
		) {
			BindingLookup::NotFound => return ImportSlot::Absent,
			BindingLookup::Found(target, visibility) => (target, visibility),
			BindingLookup::Ambiguous(candidates) => {
				let diagnostic = self.report_ambiguous_reexport(
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
					let diagnostic =
						self.report_private_import(key.symbol, source_span);
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

	fn ensure_use_path(
		&mut self,
		origin: NamespaceIndex,
		path: UsePathIndex,
		current_item: UseItemIndex,
	) -> Result<ImportScope, ()> {
		match self.path_state[usize::from(path)].poll() {
			ResolveStep::Ready(result) => return result,
			ResolveStep::Cycle => {
				let segment = self.use_paths[usize::from(path)];
				let file_id = self.namespaces[usize::from(origin)].file_id;
				let diagnostic = self.report_use_cycle(SourceSpan::new(
					file_id,
					segment.segment.span,
				));
				self.diagnostics.push(diagnostic);
				return Err(());
			}
			ResolveStep::Proceed => {}
		}

		let result = self.compute_use_path(origin, path, current_item);
		self.path_state[usize::from(path)].finish(result)
	}

	/// The actual path-segment resolution logic, free to `match`/return
	/// however it likes — `ensure_use_path` above is the only thing that
	/// touches `path_state`, and it always feeds this function's result to
	/// `finish`, so nothing here can leave a slot stuck `Resolving`.
	fn compute_use_path(
		&mut self,
		origin: NamespaceIndex,
		path: UsePathIndex,
		current_item: UseItemIndex,
	) -> Result<ImportScope, ()> {
		let segment = self.use_paths[usize::from(path)];
		match segment.parent {
			None => {
				self.binding_to_import_scope(origin, origin, path, current_item)
			}
			Some(parent) => {
				let parent_scope =
					self.ensure_use_path(origin, parent, current_item)?;
				self.resolve_import_scope_member(
					origin,
					parent_scope,
					path,
					current_item,
				)
			}
		}
	}

	/// One step further down an already-resolved scope — looks up `path`'s
	/// own segment inside `scope` itself, rather than `origin`. Used for
	/// every path segment after the first; the first segment is looked up
	/// directly in `origin`'s own bindings by `compute_use_path`'s `None`
	/// branch, since there's no prior scope yet to look inside of.
	fn resolve_import_scope_member(
		&mut self,
		origin: NamespaceIndex,
		scope: ImportScope,
		path: UsePathIndex,
		current_item: UseItemIndex,
	) -> Result<ImportScope, ()> {
		match scope {
			ImportScope::Namespace(ns) => {
				self.binding_to_import_scope(ns, origin, path, current_item)
			}
		}
	}

	/// Looks up `path`'s own segment in `declaring_namespace`'s bindings,
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
		declaring_namespace: NamespaceIndex,
		accessor: NamespaceIndex,
		path: UsePathIndex,
		current_item: UseItemIndex,
	) -> Result<ImportScope, ()> {
		let segment = self.use_paths[usize::from(path)];
		let key = BindingKey::ty(segment.segment.inner);

		// Force any not-yet-resolved `use` that might install this exact
		// name in `declaring_namespace` first — same reasoning as leaf
		// resolution's own forcing in `compute_use_item`: a path prefix
		// can just as well be a `use`-created alias (not yet installed
		// only because its own item hasn't run yet) as a directly
		// declared `mod`, and the two must be equally order-independent.
		// Skips `current_item`: e.g. `use x::x;` registers itself as a
		// candidate for its own prefix segment "x", and forcing it here
		// would just be forcing this same resolution from inside itself —
		// a spurious cycle, not a real one, since nothing else claims "x"
		// either (same reasoning as the leaf-level self-skip).
		if let Some(candidates) = self
			.pending_named_imports
			.get(&(declaring_namespace, segment.segment.inner))
		{
			for candidate in candidates {
				if candidate != current_item {
					self.ensure_use_item(candidate);
				}
			}
		}

		let source_span = SourceSpan::new(
			self.namespaces[usize::from(accessor)].file_id,
			segment.segment.span,
		);

		let (target, visibility) = match self.namespaces.lookup(
			self.use_items,
			declaring_namespace,
			key,
			accessor,
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
				let diagnostic = self.report_ambiguous_reexport(
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
			declaring_namespace,
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
			declaring_namespace,
			visibility,
		) {
			// Reported here and now, not deferred like a leaf's
			// `BindingTarget::Inaccessible` — this *is* the reference
			// site, so there's nothing to defer to. Walking continues
			// past it (rather than bailing) so a genuinely separate
			// problem further down the path — the next segment, or the
			// leaf, not existing — still gets its own diagnostic instead
			// of being silently swallowed by this one.
			let diagnostic =
				self.report_private_import(segment.segment.inner, source_span);
			self.diagnostics.push(diagnostic);
		}
		let BindingTarget::Accessible(def_key) = target else {
			return Err(());
		};

		let def = &self.namespaces[usize::from(def_key.namespace_idx)].items
			[usize::from(def_key.def_idx)];
		match def.kind {
			DefKind::Namespace(namespace) => {
				Ok(ImportScope::Namespace(namespace))
			}
			_ => {
				let diagnostic = self.report_expected_import_scope(
					segment.segment.inner,
					source_span,
				);
				self.diagnostics.push(diagnostic);
				Err(())
			}
		}
	}

	/// Reconstructs the literal `::`-joined text of a `use` path prefix, as
	/// the user wrote it, from `path`'s root down to (but not including) the
	/// segment that failed — purely for naming what was searched in a
	/// diagnostic; nothing else needs this text.
	fn use_path_text(&self, path: Option<UsePathIndex>) -> String {
		let mut segments = Vec::new();
		let mut current = path;
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
		let prefix_text = self.use_path_text(prefix);
		let full_path = if prefix_text.is_empty() {
			name.to_string()
		} else {
			format!("{prefix_text}::{name}")
		};
		let label_message = if prefix_text.is_empty() {
			"not found in this module".to_string()
		} else {
			format!("no `{name}` in `{prefix_text}`")
		};
		Diagnostic::error()
			.with_code(DiagnosticCode::UnresolvedImport.code())
			.with_message(format!("unresolved import `{full_path}`"))
			.with_label(span.primary_label().with_message(label_message))
	}

	fn report_private_import(
		&self,
		name: SymbolU32,
		span: SourceSpan,
	) -> Diagnostic<FileId> {
		let name = self.strings.resolve(name).unwrap();
		Diagnostic::error()
			.with_code(DiagnosticCode::PrivateItem.code())
			.with_message(format!("`{name}` is private"))
			.with_label(
				span.primary_label().with_message("this item is not `pub`"),
			)
	}

	fn report_expected_import_scope(
		&self,
		name: SymbolU32,
		span: SourceSpan,
	) -> Diagnostic<FileId> {
		let name = self.strings.resolve(name).unwrap();
		Diagnostic::error()
			.with_code(DiagnosticCode::NotANamespace.code())
			.with_message(format!("`{name}` is not a module"))
			.with_label(
				span.primary_label()
					.with_message("only a module can be used as a path prefix"),
			)
	}

	fn report_use_cycle(&self, span: SourceSpan) -> Diagnostic<FileId> {
		Diagnostic::error()
			.with_code(DiagnosticCode::CyclicImport.code())
			.with_message("cyclic import")
			.with_label(
				span.primary_label().with_message(
					"import resolution cycles back to itself here",
				),
			)
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

	/// Modelled on rustc's E0659: several `pub use path::*;` re-exports
	/// supply the same name, and nothing here picks one over another. The
	/// labels point at the responsible `pub use` edges, not the ultimate
	/// definitions — each definition is perfectly fine on its own, and
	/// it's re-exporting more than one of them under the same name that
	/// isn't.
	fn report_ambiguous_reexport(
		&self,
		name: SymbolU32,
		span: SourceSpan,
		candidates: &[(BindingTarget, SourceSpan)],
	) -> Diagnostic<FileId> {
		let resolved_name = self.strings.resolve(name).unwrap();
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::AmbiguousReexport.code())
			.with_message(format!("`{resolved_name}` is ambiguous"))
			.with_label(span.primary_label().with_message("ambiguous name"));
		for (_, candidate_span) in candidates {
			diagnostic = diagnostic.with_label(
				candidate_span.secondary_label().with_message(format!(
					"`{resolved_name}` could refer to the item re-exported here"
				)),
			);
		}
		diagnostic.with_note(format!(
			"consider adding an explicit `use` of `{resolved_name}` to disambiguate"
		))
	}
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
			let mut graph = builder.build(root_id);

			let mut diagnostics = Vec::new();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.interner,
				&mut diagnostics,
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

		fn root_namespace(&self) -> NamespaceIndex {
			self.defs.package_namespaces[self.graph.root_package.as_usize()]
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
			namespace: NamespaceIndex,
			name: &str,
		) -> Option<BindingTarget> {
			let symbol = self.graph.interner.get_or_intern(name);
			self.defs.namespaces[usize::from(namespace)]
				.bindings
				.get(&BindingKey::ty(symbol))
				.map(|binding| binding.target)
		}

		fn lookup_value(
			&mut self,
			namespace: NamespaceIndex,
			name: &str,
		) -> Option<BindingTarget> {
			let symbol = self.graph.interner.get_or_intern(name);
			self.defs.namespaces[usize::from(namespace)]
				.bindings
				.get(&BindingKey::value(symbol))
				.map(|binding| binding.target)
		}

		/// Follows a bound name to the namespace it names — e.g. the
		/// namespace a `mod inner { ... }` or `mod inner;` declares.
		fn child_namespace(
			&mut self,
			namespace: NamespaceIndex,
			name: &str,
		) -> NamespaceIndex {
			let target = self
				.lookup_type(namespace, name)
				.unwrap_or_else(|| panic!("`{name}` should be bound"));
			let BindingTarget::Accessible(def_key) = target else {
				panic!("`{name}` should be accessible here");
			};
			match self.defs.namespaces[usize::from(def_key.namespace_idx)].items
				[usize::from(def_key.def_idx)]
			.kind
			{
				DefKind::Namespace(namespace) => namespace,
				other => panic!("`{name}` is not a module: {other:?}"),
			}
		}

		/// The namespaces `namespace` glob-imports, in declaration order.
		fn glob_targets(
			&self,
			namespace: NamespaceIndex,
		) -> Vec<NamespaceIndex> {
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
		case.diagnostics()
			.assert_error_with(DiagnosticCode::PrivateItem, |diagnostic| {
				assert_eq!(diagnostic.message, "`secret` is private")
			});

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

		case.diagnostics()
			.assert_error_with(DiagnosticCode::PrivateItem, |diagnostic| {
				assert_eq!(diagnostic.message, "`inner` is private")
			});
	}

	#[test]
	fn non_module_path_prefix_reports_not_a_namespace() {
		let case = TestCase::new(indoc! {"
			struct Helper { x: i32 }

			use Helper::something;
		"});

		case.diagnostics().assert_error_with(
			DiagnosticCode::NotANamespace,
			|diagnostic| {
				assert_eq!(diagnostic.message, "`Helper` is not a module")
			},
		);
	}

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
			.assert_error_with(DiagnosticCode::CyclicImport, |diagnostic| {
				assert_eq!(diagnostic.message, "cyclic import")
			});
	}

	/// A cycle is already the root cause. It should not also make one of its
	/// participants look like an independently missing name while the resolver
	/// unwinds the cycle.
	#[test]
	fn cyclic_reexports_do_not_cascade_into_unresolved_import() {
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
	fn mutually_pub_globs_report_cyclic_import() {
		let case = TestCase::new(indoc! {"
			mod a {
				pub use crate::b::*;
			}

			mod b {
				pub use crate::a::*;
			}
		"});

		case.diagnostics()
			.assert_error_with(DiagnosticCode::CyclicImport, |diagnostic| {
				assert_eq!(diagnostic.message, "cyclic import")
			});
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
			.assert_codes(&[DiagnosticCode::AmbiguousReexport]);
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
}
