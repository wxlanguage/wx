//! The module system: creating a namespace per module, claiming and looking up
//! names in it, Rust-style default visibility, and `use` trees — prefix walking,
//! wildcard imports and the ambiguity they can create.

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Pre-populates `namespace_idx`'s own symbol table with the two
	/// path-root keywords: `crate` (always, resolving to `package`'s own
	/// root namespace) and `super` (only when `parent` is `Some`, resolving
	/// there). Both are inserted as ordinary `SymbolKind::Module` entries —
	/// indistinguishable from a real module once inserted — so every
	/// existing path-walking function (`lookup_scope_chain`'s own-symbols
	/// check, and every multi-segment walker's direct-lookup-in-a-known-
	/// namespace step) already resolves them correctly with no changes of
	/// its own, including chained `super::super::x` (each namespace on the
	/// walk carries its own `super` entry).
	///
	/// Called once per namespace, right after it's pushed into
	/// `tir.namespaces`. For a package's own root namespace, call this
	/// *after* `tir.package_namespaces` already has that package's entry —
	/// that's what makes the root's own `crate` naturally resolve to
	/// itself, with `parent: None` (no `super` inserted there, matching
	/// every other place `parent: None` already means "package boundary").
	pub(super) fn seed_path_root_symbols(
		&mut self,
		namespace_idx: NamespaceIndex,
		package: PackageId,
		parent: Option<NamespaceIndex>,
	) {
		let crate_sym = self.interner.get_or_intern("crate");
		let crate_root = self.tir.package_namespaces[&package];
		self.tir.namespaces[namespace_idx as usize].symbols.insert(
			(SymbolNamespace::Type, crate_sym),
			SymbolEntry::Resolved {
				kind: SymbolKind::Module {
					namespace_idx: crate_root,
				},
				visibility: Visibility::Public,
			},
		);
		let Some(parent) = parent else { return };
		let super_sym = self.interner.get_or_intern("super");
		self.tir.namespaces[namespace_idx as usize].symbols.insert(
			(SymbolNamespace::Type, super_sym),
			SymbolEntry::Resolved {
				kind: SymbolKind::Module {
					namespace_idx: parent,
				},
				visibility: Visibility::Public,
			},
		);
	}

	/// Unconditionally creates a new module namespace as a child of
	/// `namespace`, with no lookup — every field is set exactly once, here,
	/// by whichever of the two callers actually has the real data:
	/// Phase 1a (file-based modules, `own_file_id: Some(..)`) or
	/// `ensure_module`'s not-found path (inline `mod foo { }` blocks,
	/// `own_file_id: None`).
	pub(super) fn create_module_namespace(
		&mut self,
		declaring_file_id: FileId,
		namespace: NamespaceIndex,
		name: ast::Spanned<SymbolU32>,
		pub_span: Option<ast::TextSpan>,
		own_file_id: Option<FileId>,
	) -> NamespaceIndex {
		let namespace_idx = self.tir.namespaces.len() as u32;
		let decl_idx = self.tir.module_decls.len() as u32;
		// A nested module belongs to whatever package encloses it.
		let package = self.tir.namespaces[namespace as usize].package;
		self.tir.namespaces.push(ModuleNamespace {
			parent: Some(namespace),
			package,
			declaration: ModuleDeclarationKind::Module(decl_idx),
			symbols: HashMap::new(),
			wildcard_imports: Vec::new(),
			accesses: Vec::new(),
		});
		self.seed_path_root_symbols(namespace_idx, package, Some(namespace));
		self.tir.module_decls.push(ModuleDecl {
			namespace_idx,
			declaring_file_id,
			own_file_id,
			name,
			pub_span,
		});
		self.insert_symbol(
			namespace,
			(SymbolNamespace::Type, name.inner),
			SymbolKind::Module { namespace_idx },
			pub_span,
		);
		namespace_idx
	}

	/// Checks `namespace`'s direct scope for an existing Type-namespace
	/// binding under `name` that's some `SymbolKind::Module` — a
	/// dependency (`wx.json`), an `import "..." { }` block, or another
	/// `mod`. Every legitimate case of two sites converging on one
	/// module namespace (a declaring file and its content file) is handled
	/// entirely by Phase 1a, before any of this module's three callers
	/// ever run — so by the time any of them see a hit here, it's always a
	/// genuine duplicate, never something safe to reuse. Diagnoses the
	/// collision and returns the existing namespace to recover into (the
	/// same tradeoff as any other diagnosed TIR: the compilation already
	/// has an error and `wx-cli` aborts before `MIR::build`, so what the
	/// colliding declaration's own contents end up merged into doesn't
	/// matter). `None` when the name is free to claim, or already claimed
	/// by some other, unrelated kind of symbol — not this helper's
	/// concern.
	pub(super) fn check_module_collision(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		name: ast::Spanned<SymbolU32>,
	) -> Option<NamespaceIndex> {
		let existing = self.direct_scope_lookup(
			namespace,
			(SymbolNamespace::Type, name.inner),
		)?;
		let SymbolEntry::Resolved {
			kind: SymbolKind::Module { namespace_idx },
			..
		} = existing
		else {
			return None;
		};
		let first_definition = self.get_symbol_location(existing);
		let name_str = self.interner.resolve(name.inner).unwrap();
		self.tir.diagnostics.push(report_duplicate_definition(
			DuplicateDefinitionDiagnostic {
				name: name_str,
				namespace: SymbolNamespace::Type,
				first_definition,
				second_definition: SourceSpan::new(file_id, name.span),
			},
		));
		Some(namespace_idx)
	}

	/// Resolves an *inline* `mod foo { }` block — the one case vfs never
	/// sees (it only discovers file-based `mod foo;` declarations, which
	/// Phase 1a already handles before any file's items are scanned).
	pub(super) fn ensure_module(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		name: ast::Spanned<SymbolU32>,
		pub_span: Option<ast::TextSpan>,
	) -> NamespaceIndex {
		if let Some(existing) =
			self.check_module_collision(file_id, namespace, name)
		{
			return existing;
		}
		self.create_module_namespace(file_id, namespace, name, pub_span, None)
	}

	/// Binds `kind` into `namespace`'s own symbol table under `key`, with
	/// `pub_span` as *this binding's own* visibility qualifier — the item's
	/// own `pub_span` for a direct declaration, or a `use` leaf's own for a
	/// re-export (independent of the re-exported item's — that's already
	/// been checked once, when the leaf's own prefix resolved). Ignored for
	/// a `kind` that `symbol_kind_is_gated` says isn't subject to privacy
	/// at all. Not for a still-unresolved claim — see `insert_pending`.
	pub(super) fn insert_symbol(
		&mut self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		kind: SymbolKind,
		pub_span: Option<TextSpan>,
	) {
		let visibility =
			if self.symbol_kind_is_gated(kind) && pub_span.is_none() {
				Visibility::Private
			} else {
				Visibility::Public
			};
		self.tir.namespaces[namespace as usize]
			.symbols
			.insert(key, SymbolEntry::Resolved { kind, visibility });
	}

	/// Registers a provisional, unresolved claim on `key` for `id` — what
	/// every item starts as during pre-scan, before its signature (and so
	/// its real `SymbolKind`/visibility) is known.
	pub(super) fn insert_pending(
		&mut self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		id: ast::DefId,
	) {
		self.tir.namespaces[namespace as usize]
			.symbols
			.insert(key, SymbolEntry::Pending(id));
	}

	/// Looks up `key` in `namespace`'s own symbol map only — no parent-scope
	/// or wildcard-import fallback. Used for Phase-1 duplicate-definition
	/// checks (locals must silently shadow wildcard imports, matching
	/// `Trait`'s existing pre-scan check) and for the Phase-2 "do I still
	/// hold my own `Pending` slot" check that decides whether an item wins
	/// its name binding.
	pub(super) fn direct_scope_lookup(
		&self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
	) -> Option<SymbolEntry> {
		self.tir.namespaces[namespace as usize]
			.symbols
			.get(&key)
			.copied()
	}

	/// `true` if `namespace`'s own symbol table still has `id`'s
	/// provisional claim sitting on `key`, untouched — the ubiquitous
	/// "do I still hold my own slot" check every item kind's Phase-2
	/// registration makes before binding its real `SymbolKind`.
	pub(super) fn still_pending(
		&self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		id: ast::DefId,
	) -> bool {
		matches!(
			self.direct_scope_lookup(namespace, key),
			Some(SymbolEntry::Pending(pending_id)) if pending_id == id
		)
	}

	/// Phase-1 registration for a name that may collide with an earlier
	/// item in the same direct scope. `pre_scan_item` never installs
	/// anything but `Pending`, so a collision here can only be a same-scope
	/// duplicate — never a wildcard import, which lives in a different
	/// scope's own map and is only ever consulted through the fallback
	/// chain, not this direct lookup.
	///
	/// Callers must unconditionally allocate the item's stub/index/
	/// `ast_nodes` entry regardless of the outcome — only the name binding
	/// is exclusive; every syntactic occurrence still gets fully resolved.
	pub(super) fn claim_name_binding(
		&mut self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		id: ast::DefId,
		definition_span: SourceSpan,
	) -> PendingClaim {
		if let Some(existing) = self.direct_scope_lookup(namespace, key) {
			// A real declaration always outranks an import's provisional
			// claim, and displaces it without a word — see
			// [`Self::claim_use_binding`] for why the import can't be judged
			// yet. The displaced import re-checks this slot in Phase 2 and
			// reports the collision only if it turns out to want the name.
			if matches!(existing, SymbolEntry::Pending(def_id)
			if matches!(
				self.tir.item_lookup.get(&def_id),
				Some(ItemIndex::Use(_))
			)) {
				self.insert_pending(namespace, key, id);
				return PendingClaim::Claimed;
			}
			let first_definition = self.get_symbol_location(existing);
			let name_str = self.interner.resolve(key.1).unwrap();
			self.tir.diagnostics.push(report_duplicate_definition(
				DuplicateDefinitionDiagnostic {
					name: name_str,
					namespace: key.0,
					first_definition,
					second_definition: definition_span,
				},
			));
			PendingClaim::Duplicate
		} else {
			self.insert_pending(namespace, key, id);
			PendingClaim::Claimed
		}
	}

	/// Claims a name for a `use` leaf — provisionally, and silently.
	///
	/// A leaf claims *both* symbol namespaces at prescan, because which one
	/// its target occupies isn't knowable until Phase 2, so one of the two
	/// claims is routinely spurious. That makes prescan the wrong place to
	/// judge any collision involving an import: `use math::add;` (a
	/// function, so value-only) alongside a local `struct add` is legal, and
	/// so is `use a::foo;` alongside `use b::foo;` when the two occupy
	/// different namespaces. Both would be reported as redefinitions on the
	/// strength of a claim that is about to be withdrawn.
	///
	/// So nothing is reported here. A real declaration keeps the slot; a
	/// rival import takes it (last one wins, provisionally). Either way the
	/// leaf that lost re-checks in Phase 2, once it knows which namespaces
	/// it actually wants, and reports the collision then.
	fn claim_use_binding(
		&mut self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		id: ast::DefId,
	) {
		match self.direct_scope_lookup(namespace, key) {
			None => self.insert_pending(namespace, key, id),
			// Another import's provisional claim — take it over.
			Some(SymbolEntry::Pending(def_id))
				if matches!(
					self.tir.item_lookup.get(&def_id),
					Some(ItemIndex::Use(_))
				) =>
			{
				self.insert_pending(namespace, key, id);
			}
			// A real declaration outranks an import. Leave it alone.
			Some(_) => {}
		}
	}

	/// `true` if `outer` encloses `inner` — `inner` is `outer` itself or one
	/// of its descendants. Implemented by walking *up* from `inner`, which is
	/// the cheap direction: a namespace has one parent but any number of
	/// children.
	///
	/// This is the containment half of Rust-style default visibility: an item
	/// declared in `outer` is visible without `pub` to `outer` and every
	/// module nested inside it. Callers phrase it as
	/// `namespace_contains(declaring, accessor)` — "does the declaring module
	/// contain the code doing the access".
	///
	/// A plain walk up `.parent` is enough now that every package has its own
	/// root namespace: a chain terminates inside the package it started in,
	/// so crossing into another package is impossible by construction. This
	/// used to need an explicit stop at `ModuleDeclarationKind::Package`,
	/// because `None` meant both "no ancestor" and "the root package's own
	/// scope", and the two chains dead-ended at the same value.
	fn namespace_contains(
		&self,
		outer: NamespaceIndex,
		inner: NamespaceIndex,
	) -> bool {
		let mut current = Some(inner);
		while let Some(idx) = current {
			if idx == outer {
				return true;
			}
			current = self.tir.namespaces[idx as usize].parent;
		}
		false
	}

	/// `true` if a binding of `kind` is subject to ordinary `pub`/private
	/// visibility at all — `false` for the kinds that stay unconditionally
	/// visible regardless of any `pub`: memories and import-block members
	/// (parser-rejects `pub` on both — `VisibilityNotPermitted`), and a
	/// `Module` reached via `crate`/a dependency name or an import block's
	/// own alias (never user-writable visibility; only a real `mod foo;`/
	/// `mod foo { }` is gated, using its own `ModuleDecl.pub_span`). Trait
	/// members (`TraitAssocType`) share their trait's own gating — `trait`
	/// bodies reject a `pub` qualifier on their items (see
	/// `VisibilityNotPermitted` in the parser), so there's no separate span
	/// to read for them.
	///
	/// `insert_symbol` calls this to decide whether the `pub_span` it was
	/// given actually matters — used both for a direct declaration's own
	/// visibility and, unchanged, for a `use` re-export's (the leaf's own
	/// `pub_span` in place of the original item's): an exempt kind must
	/// stay exempt either way, not become newly gated just for having gone
	/// through a `use`.
	fn symbol_kind_is_gated(&self, kind: SymbolKind) -> bool {
		let declaring = match kind {
			SymbolKind::Enum { enum_index } => {
				self.tir.enums[enum_index as usize].namespace
			}
			SymbolKind::Struct { struct_index } => {
				self.tir.structs[struct_index as usize].namespace
			}
			SymbolKind::Trait { trait_index }
			| SymbolKind::TraitAssocType { trait_index, .. } => {
				self.tir.traits[trait_index as usize].namespace
			}
			SymbolKind::TypeSet { typeset_index } => {
				self.tir.typesets[typeset_index as usize].namespace
			}
			SymbolKind::Global { global_index } => {
				self.tir.globals[global_index as usize].namespace
			}
			SymbolKind::Function { func_index } => {
				self.tir.functions[func_index as usize].namespace
			}
			SymbolKind::Const { const_index } => {
				self.tir.constants[const_index as usize].namespace
			}
			SymbolKind::TypeAlias { type_alias_index } => {
				self.tir.type_aliases[type_alias_index as usize].namespace
			}
			SymbolKind::Module { namespace_idx } => {
				return matches!(
					self.tir.namespaces[namespace_idx as usize].declaration,
					ModuleDeclarationKind::Module(_)
				);
			}
			SymbolKind::Memory { .. } => return false,
		};
		// `import "env" { fn log(...); }` declarations share the same
		// `ModuleNamespace` machinery as real modules, but there's no
		// visibility concept for them — they exist purely to be called, and
		// their functions/globals never carry a real `pub_span`. Without
		// this, every import would read as private-by-default and become
		// uncallable from outside the `import` block itself.
		!matches!(
			self.tir.namespaces[declaring as usize].declaration,
			ModuleDeclarationKind::Import(..)
		)
	}

	/// The one place the access rule lives: an item declared `visibility` in
	/// `declaring_namespace` is reachable from `accessor` if **either** it is
	/// `Public` **or** `declaring_namespace` contains `accessor`.
	///
	/// The `or` is what makes `pub` mean anything across a module boundary —
	/// a `pub` item is reachable from everywhere, containment or not — so
	/// this is deliberately not a conjunction of the two conditions.
	///
	/// `declaring_namespace` is whichever namespace's own `symbols` map the
	/// entry was found in — for a direct declaration that's the same
	/// namespace `symbol_kind_is_gated` read `pub_span` from; for a `use`
	/// re-export it's the namespace that wrote the `use`, not the original
	/// item's. A struct field has no `symbols` entry of its own, so its
	/// caller passes the struct's namespace (see [`Self::field_visibility`]).
	pub(super) fn is_accessible_from(
		&self,
		accessor: NamespaceIndex,
		declaring_namespace: NamespaceIndex,
		visibility: Visibility,
	) -> bool {
		match visibility {
			Visibility::Public => true,
			Visibility::Private => {
				self.namespace_contains(declaring_namespace, accessor)
			}
		}
	}

	/// The declared visibility of one struct field.
	///
	/// A field never gets a `SymbolEntry` — it is only ever reached by name
	/// on its owner — so there is no stored [`Visibility`] to read and the
	/// `pub` qualifier is interpreted here instead, by the same rule
	/// [`Self::insert_symbol`] applies to everything else.
	///
	/// Pair it with [`Self::is_accessible_from`] against the *struct's* namespace:
	/// a field has no scope of its own, so it is private to the module that
	/// declares the struct. That deliberately makes an inherent impl written
	/// in another module an outside accessor — `impl geom::Point { fn f(self)
	/// -> i32 { self.y } }` has no more claim on a private `y` than any other
	/// foreign code does.
	pub(super) fn field_visibility(
		&self,
		struct_index: u32,
		field_index: FieldIndex,
	) -> Visibility {
		if self.tir.structs[struct_index as usize].fields
			[field_index.as_usize()]
		.pub_span
		.is_some()
		{
			Visibility::Public
		} else {
			Visibility::Private
		}
	}

	/// Reports a struct field named from outside the module declaring it.
	///
	/// Its own code rather than [`report_private_item`]'s `PrivateItem`: that
	/// one names an item the caller could have brought into scope, and its
	/// "this item is not `pub`" wording points at a fix the caller can make.
	/// A field is reachable only through its owner, so the `pub` that has to
	/// be added is the one on the field declaration — a different fix, made
	/// by a different person, worth a code a reader can look up separately.
	pub(super) fn report_private_field(
		&mut self,
		struct_index: u32,
		field_index: FieldIndex,
		access: SourceSpan,
	) {
		let declaration = &self.tir.structs[struct_index as usize];
		let field = &declaration.fields[field_index.as_usize()];
		let declared_at = SourceSpan::new(declaration.file_id, field.name.span);
		let field_name = self.interner.resolve(field.name.inner).unwrap();
		let struct_name =
			self.interner.resolve(declaration.name.inner).unwrap();

		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::PrivateStructField.code())
			.with_message(format!(
				"field `{field_name}` of struct `{struct_name}` is private"
			))
			.with_label(access.primary_label().with_message("private field"))
			.with_label(
				declared_at
					.secondary_label()
					.with_message("declared without `pub` here"),
			);
		self.tir.diagnostics.push(diagnostic);
	}

	/// [`Self::is_accessible_from`], for a raw `SymbolEntry` straight out of a
	/// `symbols` map — used by the one caller that reads visibility off an
	/// entry that might still be `Pending` (`lookup_scope_chain`'s wildcard
	/// loop).
	///
	/// TODO: a still-`Pending` entry is always treated as visible here,
	/// without forcing its signature — there's no `Visibility` to read yet
	/// (see `SymbolEntry`). Safe only because the one caller that needs a
	/// *real* answer for a name that might be `Pending`
	/// (`resolve_pending_global_symbol`/`resolve_pending_namespace_symbol`)
	/// forces resolution via `ensure_signature` and re-fetches the
	/// now-resolved entry before trusting it — so this is never the value
	/// an actual gating decision runs on. But nothing enforces that in the
	/// type system: don't reuse this for a new caller without confirming it
	/// can't observe a still-`Pending` entry as final.
	fn is_entry_accessible_from(
		&self,
		accessor: NamespaceIndex,
		declaring_namespace: NamespaceIndex,
		entry: SymbolEntry,
	) -> bool {
		match entry {
			SymbolEntry::Pending(_) => true,
			SymbolEntry::Resolved { visibility, .. } => self
				.is_accessible_from(accessor, declaring_namespace, visibility),
		}
	}

	/// The symbol `key` resolves to, ignoring any ambiguity — see
	/// [`Self::lookup_scope_chain`], whose result this discards the evidence
	/// from. For sites that ask "is this still my own `Pending`" rather than
	/// "what does this name mean", which is a question ambiguity can't
	/// affect.
	pub(super) fn lookup_global_symbol(
		&self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
	) -> Option<SymbolEntry> {
		self.lookup_scope_chain(namespace, key).symbol()
	}

	/// Walks the scope chain for `key`: the namespace's own symbols, then
	/// its globs, then its parent, out to the package boundary — and finally
	/// the prelude.
	///
	/// Ambiguity is detected here, in the one walk every identifier already
	/// pays for, and the result carries the candidates that caused it — the
	/// evidence comes from the pass that found the problem rather than from
	/// a second traversal repeating the same visibility rules. Building the
	/// candidate list starts only once a second distinct item shows up, so
	/// the ordinary path allocates nothing.
	///
	/// Ambiguity is **per scope level**: two globs on one namespace
	/// supplying `foo` conflict, but a glob here and a glob on the parent is
	/// ordinary shadowing, which is why the walk stops at the first level
	/// that resolves.
	fn lookup_scope_chain(
		&self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
	) -> ScopeLookup {
		let mut current = Some(namespace);
		while let Some(idx) = current {
			let namespace_ref = &self.tir.namespaces[idx as usize];
			// A name declared or explicitly imported here always wins, and
			// wins unambiguously — which is what makes `use x::foo;` the
			// documented way out of a glob ambiguity.
			if let Some(entry) = namespace_ref.symbols.get(&key).copied() {
				return ScopeLookup::Found(entry);
			}

			let mut first: Option<(SymbolEntry, SourceSpan)> = None;
			let mut candidates: Vec<(SymbolEntry, SourceSpan)> = Vec::new();
			for import in namespace_ref.wildcard_imports.iter() {
				let Some(entry) = self.tir.namespaces
					[import.namespace as usize]
					.symbols
					.get(&key)
					.copied()
					.filter(|entry| {
						self.is_entry_accessible_from(
							namespace,
							import.namespace,
							*entry,
						)
					})
				else {
					continue;
				};
				match first {
					// The same item reached two ways is not a conflict.
					Some((seen, _)) if seen == entry => {}
					Some(seen) => {
						if candidates.is_empty() {
							candidates.push(seen);
						}
						candidates.push((entry, import.span));
					}
					None => first = Some((entry, import.span)),
				}
			}
			if !candidates.is_empty() {
				return ScopeLookup::Ambiguous(candidates.into_boxed_slice());
			}
			if let Some((entry, _)) = first {
				return ScopeLookup::Found(entry);
			}
			current = namespace_ref.parent;
		}
		// `parent: None` is only ever a package root now, so running out of
		// parents *is* the package boundary. There's no outer store left to
		// fall into, which is what keeps one package's items — and its
		// dependency names — invisible to every other package.
		//
		// The prelude is the one exception, and deliberately the last tier: a
		// name std happens to define never shadows anything the user wrote or
		// imported, so adding an item to the standard library can't break a
		// program that already compiled. That ordering is the whole reason
		// it's a tier of its own rather than a synthetic `use std::*;` seeded
		// into every namespace — a real glob sits at the same level as the
		// user's own globs, where colliding with one is an ambiguity error
		// instead of quiet shadowing, and it would need a `use` statement's
		// span to blame when it collided.
		//
		// Std's own namespaces are not excluded. At std's root the fallback
		// re-reads the same symbol map tier 1 just missed, which costs one
		// failed lookup and can't change an answer; one level down, in std's
		// own `mod ptr`, it's what lets that module see `Memory` and
		// `size_of` — the same service every other module gets.
		self.prelude_lookup(namespace, key)
	}

	/// The prelude tier of [`Self::lookup_scope_chain`]: `key` as found in the
	/// standard library's root namespace.
	///
	/// Visibility is checked against the looking-up namespace exactly as a
	/// glob's is, so a non-`pub` item at std's root stays internal to std —
	/// while staying visible to std's own descendants, which is what makes
	/// serving the prelude to std itself harmless.
	fn prelude_lookup(
		&self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
	) -> ScopeLookup {
		let Some(&prelude) =
			self.tir.package_namespaces.get(&self.stdlib_package)
		else {
			return ScopeLookup::NotFound;
		};
		match self.tir.namespaces[prelude as usize]
			.symbols
			.get(&key)
			.copied()
			.filter(|entry| {
				self.is_entry_accessible_from(namespace, prelude, *entry)
			}) {
			Some(entry) => ScopeLookup::Found(entry),
			None => ScopeLookup::NotFound,
		}
	}

	/// [`Self::lookup_scope_chain`], reporting an ambiguity before handing
	/// back the arbitrary winner so resolution carries on with something.
	///
	/// This — not [`Self::lookup_global_symbol`] — is what a *reference*
	/// site wants. The raw one is for sites asking "is this still my own
	/// `Pending`", a question no amount of glob ambiguity changes.
	pub(super) fn lookup_global_symbol_reporting(
		&mut self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		span: SourceSpan,
	) -> Option<SymbolEntry> {
		match self.lookup_scope_chain(namespace, key) {
			ScopeLookup::Ambiguous(candidates) => {
				self.report_wildcard_ambiguity(key.1, span, &candidates);
				Some(candidates[0].0)
			}
			other => other.symbol(),
		}
	}

	/// Reports a name that two or more globs supply. Modelled on rustc's
	/// E0659 but flattened: codespan-reporting has no nested
	/// sub-diagnostics, so rustc's per-candidate `note:` blocks become
	/// secondary labels on one diagnostic — the shape `AmbiguousTraitMember`
	/// already uses.
	///
	/// The labels point at the `use` statements, not the definitions: each
	/// definition is perfectly fine on its own, and it's importing both of
	/// them into one scope that isn't.
	fn report_wildcard_ambiguity(
		&mut self,
		name: SymbolU32,
		reference: SourceSpan,
		candidates: &[(SymbolEntry, SourceSpan)],
	) {
		let name = self.interner.resolve(name).unwrap();
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::AmbiguousWildcardImport.code())
			.with_message(format!("`{name}` is ambiguous"))
			.with_label(
				reference.primary_label().with_message("ambiguous name"),
			);
		for (index, (entry, span)) in candidates.iter().enumerate() {
			diagnostic = diagnostic.with_label(
				span.secondary_label().with_message(format!(
					"`{name}` could {}refer to the {} imported here",
					if index == 0 { "" } else { "also " },
					symbol_entry_noun(*entry),
				)),
			);
		}
		self.tir.diagnostics.push(
			diagnostic
				.with_note(
					"ambiguous because of multiple glob imports of a name in \
					 the same module",
				)
				.with_note(format!(
					"consider adding an explicit import of `{name}` to \
					 disambiguate"
				)),
		);
	}

	/// Looks up `key` via [`Self::lookup_global_symbol`], forcing a `Pending`
	/// result through `ensure_signature` and re-looking it up. Returns
	/// `Err(())` (with a cyclic-dependency diagnostic already pushed) if the
	/// pending item is still being computed on the current call stack.
	pub(super) fn resolve_pending_global_symbol(
		&mut self,
		namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		span: SourceSpan,
	) -> Result<Option<SymbolKind>, ()> {
		// Reported on the way in, not after forcing: forcing re-runs the
		// same lookup, and the ambiguity is a property of the imports rather
		// than of anything a signature could change.
		match self.lookup_global_symbol_reporting(namespace, key, span) {
			Some(SymbolEntry::Pending(def_id)) => {
				if matches!(
					self.sig_state.get(&def_id),
					Some(SigEntry {
						state: ComputeState::InProgress,
						..
					})
				) {
					self.tir
						.diagnostics
						.push(report_cyclic_type_dependency(span));
					return Err(());
				}
				self.ensure_signature(def_id);
				// Still pending after one force is not expected in
				// practice (see `SymbolEntry`'s docs), but rather than
				// propagate a phantom result, this folds it to `None` —
				// the same as a name that was never found.
				Ok(self
					.lookup_global_symbol(namespace, key)
					.and_then(SymbolEntry::resolved_kind))
			}
			other => Ok(other.and_then(SymbolEntry::resolved_kind)),
		}
	}

	/// Looks up `key` in `target_namespace`'s own symbol map — no
	/// parent-scope or wildcard-import fallback, for `module::Name`
	/// qualified lookups — forcing a `Pending` result through
	/// `ensure_signature` and re-looking it up. Same cyclic-dependency
	/// handling as [`Self::resolve_pending_global_symbol`].
	///
	/// `target_namespace` is *where* to search (the module named on the
	/// left of `::`); `accessor_namespace` is *who's asking* (the namespace
	/// the calling code lives in), needed to decide whether a non-`pub`
	/// result found in `target_namespace` is actually visible here. Unlike
	/// the ancestor-walk in `lookup_global_symbol` — where finding a symbol
	/// via a namespace's own `symbols` map already proves the accessor is
	/// that namespace or a descendant of it — naming `target_namespace`
	/// explicitly makes no such guarantee, so it has to be checked
	/// separately, the same way a wildcard import is.
	pub(super) fn resolve_pending_namespace_symbol(
		&mut self,
		accessor_namespace: NamespaceIndex,
		target_namespace: NamespaceIndex,
		key: (SymbolNamespace, SymbolU32),
		span: SourceSpan,
	) -> Result<Option<SymbolKind>, ()> {
		let resolved = match self.tir.namespaces[target_namespace as usize]
			.symbols
			.get(&key)
			.copied()
		{
			Some(SymbolEntry::Pending(def_id)) => {
				if matches!(
					self.sig_state.get(&def_id),
					Some(SigEntry {
						state: ComputeState::InProgress,
						..
					})
				) {
					self.tir
						.diagnostics
						.push(report_cyclic_type_dependency(span));
					return Err(());
				}
				self.ensure_signature(def_id);
				self.tir.namespaces[target_namespace as usize]
					.symbols
					.get(&key)
					.copied()
			}
			other => other,
		};
		match resolved {
			Some(SymbolEntry::Resolved { kind, visibility }) => {
				if !self.is_accessible_from(
					accessor_namespace,
					target_namespace,
					visibility,
				) {
					// Name resolution still succeeded — it's only the
					// accessibility check that failed — so this is a real
					// reference, same as Rust treats a private-item access
					// (E0603): resolved, then separately rejected. Recording
					// it here, before rejecting, is what lets hover/
					// go-to-definition work on it and keeps `report_unused_items`
					// from *also* calling it dead code on top of `PrivateItem`.
					// Every caller's own `record_symbol_access` call sits
					// on the success path only, so this doesn't double up.
					self.tir.record_symbol_access(
						span.file_id,
						kind,
						span.span,
					);
					let name = self.interner.resolve(key.1).unwrap();
					self.tir.diagnostics.push(report_private_item(name, span));
					return Err(());
				}
				Ok(Some(kind))
			}
			// Still pending after one force — not expected in practice
			// (see `SymbolEntry`'s docs) — folds to `None`, same as a name
			// that was never found, rather than fabricating a visibility
			// answer for it.
			Some(SymbolEntry::Pending(_)) | None => Ok(None),
		}
	}

	/// Resolves a single name in value position: local variables first,
	/// then the global scope chain, forcing a `Pending` signature through
	/// `ensure_signature` — the value-position twin of
	/// what [`Self::resolve_pending_global_symbol`] does for types.
	///
	/// Type position has always forced; value position never did, so any
	/// value reference resolved before its target's signature landed on the
	/// `Pending` arm of `resolve_symbol_kind_to_expression`, which is
	/// `unreachable!`. Two ways to get there: a const initializer naming a
	/// const declared later, and a name imported by a `use` written below
	/// the reference — both perfectly legal source.
	///
	/// `Err(())` means a cycle, already reported; the caller must not also
	/// report the name as undeclared.
	pub(super) fn resolve_symbol_forcing(
		&mut self,
		func_ctx: &ExprContext,
		symbol: ast::Spanned<SymbolU32>,
	) -> Result<Option<ResolvedSymbol>, ()> {
		// A local always shadows a global, so returning here means the scope
		// chain is never consulted for a local — no ambiguity report, no
		// signature forced, and none of it wasted.
		if let Some((scope_index, local_index)) =
			func_ctx.resolve_local(symbol.inner)
		{
			return Ok(Some(ResolvedSymbol::Local {
				scope_index,
				local_index,
			}));
		}

		// Past the local check this *is* the global case, so it delegates
		// rather than reimplementing: `resolve_pending_global_symbol` already
		// reports ambiguity, guards the cycle, forces, and re-looks-up. Doing
		// it here instead meant a second copy of the cycle guard — two places
		// to keep in step for one rule — and three scope-chain walks per
		// identifier where one does.
		let resolve_context = func_ctx.resolve_context;
		Ok(self
			.resolve_pending_global_symbol(
				resolve_context.namespace,
				(SymbolNamespace::Value, symbol.inner),
				SourceSpan::new(resolve_context.file_id, symbol.span),
			)?
			.map(ResolvedSymbol::Global))
	}

	pub(super) fn get_symbol_location(&self, entry: SymbolEntry) -> SourceSpan {
		let symbol = match entry {
			SymbolEntry::Resolved { kind, .. } => kind,
			// A `Pending` entry always has a stub already pushed by
			// `pre_scan_item` (every syntactic occurrence is unconditionally
			// registered there, duplicate or not), so its declaration span
			// is available via `item_lookup` even though its fields/value
			// haven't been resolved yet.
			SymbolEntry::Pending(def_id) => {
				return match self.tir.item_lookup[&def_id] {
					ItemIndex::Function(idx) => {
						let f = &self.tir.functions[idx as usize];
						SourceSpan::new(f.file_id, f.name.span)
					}
					// An import's "declaration" is the local name it binds,
					// which is the alias when it has one — that's the name
					// that actually collided.
					ItemIndex::Use(idx) => {
						let u = &self.tir.use_items[idx as usize];
						SourceSpan::new(u.file_id, u.local_name().span)
					}
					ItemIndex::Global(idx) => {
						let g = &self.tir.globals[idx as usize];
						SourceSpan::new(g.file_id, g.name.span)
					}
					ItemIndex::Memory(idx) => {
						let m = &self.tir.memories[idx as usize];
						SourceSpan::new(m.file_id, m.name.span)
					}
					ItemIndex::Struct(idx) => {
						let s = &self.tir.structs[idx as usize];
						SourceSpan::new(s.file_id, s.name.span)
					}
					ItemIndex::Const(idx) => {
						let c = &self.tir.constants[idx as usize];
						SourceSpan::new(c.file_id, c.name.span)
					}
					ItemIndex::Enum(idx) => {
						let e = &self.tir.enums[idx as usize];
						SourceSpan::new(e.file_id, e.name.span)
					}
					ItemIndex::TypeAlias(idx) => {
						let a = &self.tir.type_aliases[idx as usize];
						SourceSpan::new(a.file_id, a.name.span)
					}
					// TODO: chaugh panic when writing impl for trait, need to revisit this
					ItemIndex::TypeSet(_)
					| ItemIndex::Trait(_)
					| ItemIndex::TraitImpl(_) => unreachable!(
						"these kinds never install a Pending symbol"
					),
				};
			}
		};
		match symbol {
			SymbolKind::Function { func_index } => {
				let func = &self.tir.functions[func_index as usize];
				SourceSpan::new(func.file_id, func.name.span)
			}
			SymbolKind::Global { global_index } => {
				let global = &self.tir.globals[global_index as usize];
				SourceSpan::new(global.file_id, global.name.span)
			}
			SymbolKind::Const { const_index } => {
				let const_ = &self.tir.constants[const_index as usize];
				SourceSpan::new(const_.file_id, const_.name.span)
			}
			SymbolKind::Enum { enum_index } => {
				let enum_ = &self.tir.enums[enum_index as usize];
				SourceSpan::new(enum_.file_id, enum_.name.span)
			}
			SymbolKind::Struct { struct_index } => {
				let s = &self.tir.structs[struct_index as usize];
				SourceSpan::new(s.file_id, s.name.span)
			}
			SymbolKind::Module { namespace_idx } => {
				match self.tir.namespaces[namespace_idx as usize].declaration {
					ModuleDeclarationKind::Module(decl_idx) => {
						let decl = &self.tir.module_decls[decl_idx as usize];
						SourceSpan::new(decl.declaring_file_id, decl.name.span)
					}
					ModuleDeclarationKind::Import(import_idx) => {
						let decl = &self.tir.import_decls[import_idx as usize];
						SourceSpan::new(decl.file_id, decl.external_name.span)
					}
					ModuleDeclarationKind::Package(file_id) => {
						SourceSpan::new(file_id, ast::TextSpan::new(0, 0))
					}
				}
			}
			SymbolKind::Trait { trait_index } => {
				let trait_ = &self.tir.traits[trait_index as usize];
				SourceSpan::new(trait_.file_id, trait_.name.span)
			}
			SymbolKind::TypeSet { typeset_index } => {
				let ts = &self.tir.typesets[typeset_index as usize];
				SourceSpan::new(ts.file_id, ts.name.span)
			}
			SymbolKind::Memory { memory_index, .. } => {
				let memory = &self.tir.memories[memory_index as usize];
				SourceSpan::new(memory.file_id, memory.name.span)
			}
			SymbolKind::TraitAssocType { trait_index, .. } => {
				let trait_ = &self.tir.traits[trait_index as usize];
				SourceSpan::new(trait_.file_id, trait_.name.span)
			}
			SymbolKind::TypeAlias { type_alias_index } => {
				let alias = &self.tir.type_aliases[type_alias_index as usize];
				SourceSpan::new(alias.file_id, alias.name.span)
			}
		}
	}

	/// Phase 1: registers every named item into `ast_nodes` without resolving
	/// types.
	/// Walks a `use` tree at prescan, handling its two leaf kinds
	/// differently because they have opposite timing requirements.
	///
	/// A **glob** must be registered *now*: `lookup_global_symbol` consults
	/// `wildcard_imports` throughout Phase 2, so an edge added later would
	/// be invisible to every lookup that ran before it. Its prefix is
	/// resolved with plain non-forcing lookups, which is sound only because
	/// the only thing a prefix can name is a module, and module symbols are
	/// installed by Phase 1a — before any item is scanned.
	///
	/// A **named leaf** cannot be resolved now: files are prescanned in
	/// order, so `use math::add;` in `main.wx` runs before `math.wx`'s items
	/// are registered. It binds its local name to `Pending`, which is
	/// precisely the marker that makes any later reference force it through
	/// `ensure_signature` — so the deferral costs nothing.
	///
	/// `contiguous_start` tracks where the current path spelling began, for
	/// the glob's `x::*` span. It resets on entering a group element,
	/// because a span reaching back across a `{` wouldn't be a contiguous
	/// range of source.
	pub(super) fn pre_scan_use_tree(
		&mut self,
		resolve_context: ResolveContext,
		pub_span: Option<ast::TextSpan>,
		tree: &'ast ast::Spanned<ast::UseTree>,
		prefix: &mut Vec<ast::Spanned<SymbolU32>>,
		contiguous_start: u32,
		prefix_index: Option<u32>,
	) -> Option<u32> {
		match &tree.inner {
			ast::UseTree::Path { segment, rest } => {
				prefix.push(*segment);
				// A further segment is a *different* prefix, so leaves below
				// it share with each other and not with anything alongside —
				// hence `None` going down, and the caller's own index coming
				// back out untouched for whatever follows this subtree.
				self.pre_scan_use_tree(
					resolve_context,
					pub_span,
					rest,
					prefix,
					contiguous_start,
					None,
				);
				prefix.pop();
				prefix_index
			}
			ast::UseTree::Group(elements) => {
				// Threaded across siblings: the first leaf that needs these
				// tokens allocates them, and every later sibling is handed
				// the same index. This is the whole reason `{ .. }` needs
				// its own arm rather than folding into `Path`.
				let mut shared = prefix_index;
				for element in elements.iter() {
					shared = self.pre_scan_use_tree(
						resolve_context,
						pub_span,
						&element.inner,
						prefix,
						element.inner.span.start,
						shared,
					);
				}
				shared
			}
			ast::UseTree::Glob => {
				// Silent on every failure: this runs before other files have
				// been scanned, so "not found" here means "not yet", and a
				// bare `use *;` names nothing to import.
				let PrefixWalk::Resolved(source_ns) = self.walk_use_prefix(
					resolve_context.file_id,
					resolve_context.namespace,
					prefix,
				) else {
					return prefix_index;
				};
				self.tir.namespaces[resolve_context.namespace as usize]
					.wildcard_imports
					.push(WildcardImport {
						namespace: source_ns,
						span: SourceSpan::new(
							resolve_context.file_id,
							ast::TextSpan::new(contiguous_start, tree.span.end),
						),
					});
				// A glob binds no name, so it allocates no prefix of its
				// own — `use a::b::*;` stores nothing.
				prefix_index
			}
			ast::UseTree::Name { id, name, alias } => {
				let local = alias.unwrap_or(*name);
				let use_index = self.tir.use_items.len() as u32;

				// Both namespaces, because which one this import lands in
				// isn't knowable until its target resolves in Phase 2. The
				// one that turns out to be wrong is withdrawn there.
				for symbol_namespace in
					[SymbolNamespace::Type, SymbolNamespace::Value]
				{
					self.claim_use_binding(
						resolve_context.namespace,
						(symbol_namespace, local.inner),
						*id,
					);
				}

				// Unconditional, like every other item arm: the stub and the
				// `ast_nodes` entry exist whether or not the name was won,
				// so a losing duplicate still resolves fully and still has a
				// declaration span to point at.
				// First leaf under this prefix allocates it; siblings handed
				// the same index reuse it, so the segments are stored once
				// however many names the group imports.
				let prefix_index = prefix_index.unwrap_or_else(|| {
					let index = self.tir.use_prefixes.len() as u32;
					self.tir.use_prefixes.push(UsePrefix {
						path: prefix.clone().into_boxed_slice(),
						target: PrefixTarget::Unwalked,
					});
					index
				});

				// Unconditional, like every other item arm: the stub and the
				// `ast_nodes` entry exist whether or not the name was won,
				// so a losing duplicate still resolves fully and still has a
				// declaration span to point at.
				self.tir.item_lookup.insert(*id, ItemIndex::Use(use_index));
				self.tir.use_items.push(UseItem {
					id: *id,
					file_id: resolve_context.file_id,
					namespace: resolve_context.namespace,
					prefix: prefix_index,
					name: *name,
					alias: *alias,
					pub_span,
				});
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id: resolve_context.file_id,
					namespace: resolve_context.namespace,
					node: AstNodeRef::Use { use_index },
				});
				Some(prefix_index)
			}
		}
	}

	/// Resolves one named `use` leaf, in Phase 2: walks its prefix, looks
	/// the name up in the namespace that lands on, and binds whichever of
	/// the two symbol namespaces the target actually occupies.
	///
	/// Every path out of here has to leave the local name in a settled
	/// state — bound to a real symbol, or gone. A `Pending` left behind
	/// would outlive its own signature pass and hit the "signature resolved
	/// but symbol still pending" unreachable at the next reference to it.
	pub(super) fn resolve_use_item(&mut self, use_index: u32) {
		let item = &self.tir.use_items[use_index as usize];
		let (id, file_id, namespace, name, local, prefix, pub_span) = (
			item.id,
			item.file_id,
			item.namespace,
			item.name,
			item.local_name(),
			item.prefix,
			item.pub_span,
		);
		let name_span = SourceSpan::new(file_id, name.span);

		let target = match self.tir.use_prefixes[prefix as usize].target {
			// A sibling leaf already walked these very tokens — reuse its
			// answer rather than re-walking and re-reporting.
			walked @ (PrefixTarget::Resolved(_) | PrefixTarget::Failed) => {
				walked
			}
			PrefixTarget::Unwalked => {
				let path = self.tir.use_prefixes[prefix as usize].path.clone();
				// Unlike the glob path at prescan — which stays silent, since
				// it can legitimately run before its target file has been
				// scanned — a named leaf resolves late enough that everything
				// it could name already exists, so every failure is real.
				let walked = match self
					.walk_use_prefix(file_id, namespace, &path)
				{
					PrefixWalk::Resolved(target_ns) => {
						PrefixTarget::Resolved(target_ns)
					}
					// `use add;` — a bare name with nothing to import
					// it *from*.
					PrefixWalk::Empty => {
						let name = self.interner.resolve(name.inner).unwrap();
						self.tir.diagnostics.push(
							report_import_without_module(name, name_span),
						);
						PrefixTarget::Failed
					}
					PrefixWalk::NotAModule(segment, span) => {
						let name =
							self.interner.resolve(segment.inner).unwrap();
						self.tir
							.diagnostics
							.push(report_not_a_namespace(name, span));
						PrefixTarget::Failed
					}
					PrefixWalk::Unresolved(span) => {
						self.tir
							.diagnostics
							.push(report_undeclared_identifier(span));
						PrefixTarget::Failed
					}
				};
				self.tir.use_prefixes[prefix as usize].target = walked;
				walked
			}
		};

		let PrefixTarget::Resolved(target_ns) = target else {
			self.withdraw_use_claims(namespace, local.inner, id);
			return;
		};

		let mut bound_any = false;
		for symbol_namespace in [SymbolNamespace::Type, SymbolNamespace::Value]
		{
			let resolved = self.resolve_pending_namespace_symbol(
				namespace,
				target_ns,
				(symbol_namespace, name.inner),
				name_span,
			);
			match resolved {
				Ok(Some(kind)) => {
					let key = (symbol_namespace, local.inner);

					// A rival import may be sitting on this slot. Resolve it
					// first so the slot settles into either a real binding or
					// nothing — that's what distinguishes a genuine
					// collision from a claim that was about to be withdrawn
					// anyway. It cannot recurse back into this leaf: a rival
					// only ever displaced us, so we hold nothing it wants.
					if let Some(SymbolEntry::Pending(rival)) =
						self.direct_scope_lookup(namespace, key)
						&& rival != id && matches!(
						self.tir.item_lookup.get(&rival),
						Some(ItemIndex::Use(_))
					) {
						self.ensure_signature(rival);
					}

					match self.direct_scope_lookup(namespace, key) {
						// Ours, or vacated by a rival that didn't want it.
						Some(SymbolEntry::Pending(pending_id))
							if pending_id == id =>
						{
							self.insert_symbol(namespace, key, kind, pub_span);
						}
						None => {
							self.insert_symbol(namespace, key, kind, pub_span)
						}
						// Someone else really holds this name. Now that the
						// import is known to want it, the collision is real —
						// report it here, where prescan couldn't.
						Some(occupant) => {
							self.report_import_collision(
								occupant,
								symbol_namespace,
								local,
								SourceSpan::new(file_id, local.span),
							);
						}
					}
					// Only for the first namespace that binds. An item
					// occupying both — a `memory` does — would otherwise
					// record the identical span twice, and the LSP turns
					// every access into a reference, so a rename would
					// emit two overlapping edits at one range.
					if !bound_any {
						self.tir.record_symbol_access(file_id, kind, name.span);
					}
					bound_any = true;
				}
				Ok(None) => {
					self.withdraw_use_claim(
						namespace,
						local.inner,
						id,
						symbol_namespace,
					);
				}
				// Private or cyclic — already reported, and it disqualifies
				// the name in every symbol namespace at once. Returning
				// rather than breaking also skips the not-found report
				// below, which would otherwise pile a second diagnostic on
				// the same name.
				Err(()) => {
					self.withdraw_use_claims(namespace, local.inner, id);
					return;
				}
			}
		}

		if !bound_any {
			let name_str = self.interner.resolve(name.inner).unwrap();
			// A package has no name of its own — it's known by the key the
			// asking package declared it under, so this needs the *asking*
			// namespace's package, not the target's.
			let module_str = self.tir.namespace_name(
				target_ns,
				self.packages,
				self.tir.namespaces[namespace as usize].package,
				self.interner,
			);
			self.tir.diagnostics.push(report_unresolved_import(
				name_str, module_str, name_span,
			));
		}
	}

	/// Reports an import colliding with whatever already holds its local
	/// name. Ordered by source position rather than by which side is the
	/// import, so the labels read the same way as any other duplicate
	/// definition.
	fn report_import_collision(
		&mut self,
		occupant: SymbolEntry,
		symbol_namespace: SymbolNamespace,
		local: ast::Spanned<SymbolU32>,
		import: SourceSpan,
	) {
		let occupant = self.get_symbol_location(occupant);
		let name = self.interner.resolve(local.inner).unwrap();
		let swap = occupant.file_id == import.file_id
			&& occupant.span.start > import.span.start;
		let (first, second) = if swap {
			(import, occupant)
		} else {
			(occupant, import)
		};
		self.tir.diagnostics.push(report_duplicate_definition(
			DuplicateDefinitionDiagnostic {
				name,
				namespace: symbol_namespace,
				first_definition: first,
				second_definition: second,
			},
		));
	}

	/// Removes this leaf's provisional `Pending` claim from one symbol
	/// namespace — but only where the claim is still this leaf's own, since
	/// a real declaration may have displaced it.
	fn withdraw_use_claim(
		&mut self,
		namespace: NamespaceIndex,
		local: SymbolU32,
		id: ast::DefId,
		symbol_namespace: SymbolNamespace,
	) {
		let key = (symbol_namespace, local);
		if self.still_pending(namespace, key, id) {
			self.tir.namespaces[namespace as usize].symbols.remove(&key);
		}
	}

	/// [`Self::withdraw_use_claim`] for both symbol namespaces — what a leaf
	/// that resolved to nothing at all needs.
	fn withdraw_use_claims(
		&mut self,
		namespace: NamespaceIndex,
		local: SymbolU32,
		id: ast::DefId,
	) {
		for symbol_namespace in [SymbolNamespace::Type, SymbolNamespace::Value]
		{
			self.withdraw_use_claim(namespace, local, id, symbol_namespace);
		}
	}

	/// Walks a `use` prefix to the namespace it names, recording an access
	/// per resolved segment for IDE navigation.
	///
	/// Non-forcing on purpose: the only thing a prefix segment can legally
	/// name is a module, and module symbols are installed in Phase 1a —
	/// before any item is scanned — so a prefix is never `Pending`.
	///
	/// Reports nothing except an ambiguous first segment (which the lookup
	/// itself reports). Whether a failure deserves a diagnostic depends
	/// entirely on who is asking: prescan walks glob prefixes before other
	/// files exist and must stay silent, while a named leaf in Phase 2 is
	/// late enough that silence would just lose the error. Returning the
	/// outcome instead of reporting it is what lets one walker serve both
	/// without a "should I report" flag.
	fn walk_use_prefix(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		prefix: &[ast::Spanned<SymbolU32>],
	) -> PrefixWalk {
		let mut current_ns: Option<NamespaceIndex> = None;
		for segment in prefix.iter() {
			let key = (SymbolNamespace::Type, segment.inner);
			let span = SourceSpan::new(file_id, segment.span);
			let kind = match current_ns {
				// Later segments resolve only inside what we've already
				// walked into.
				Some(idx) => {
					self.tir.namespaces[idx as usize].symbols.get(&key).copied()
				}
				// The first segment is an ordinary scope-chain lookup from
				// wherever the `use` was written, so it reaches a sibling
				// module, or a dependency name held further up on the
				// package's own root namespace. It is also the only segment
				// that can be glob-ambiguous — the rest read one namespace's
				// own map directly.
				None => {
					self.lookup_global_symbol_reporting(namespace, key, span)
				}
			};
			match kind {
				Some(SymbolEntry::Resolved {
					kind: SymbolKind::Module { namespace_idx },
					..
				}) => {
					self.tir.namespaces[namespace_idx as usize]
						.accesses
						.push(span);
					current_ns = Some(namespace_idx);
				}
				Some(_) => return PrefixWalk::NotAModule(*segment, span),
				None => return PrefixWalk::Unresolved(span),
			}
		}
		match current_ns {
			Some(namespace_idx) => PrefixWalk::Resolved(namespace_idx),
			None => PrefixWalk::Empty,
		}
	}
}

/// The outcome of walking a `use` prefix — see
/// [`Builder::walk_use_prefix`], which reports none of these itself because
/// only its caller knows which deserve a diagnostic.
enum PrefixWalk {
	Resolved(NamespaceIndex),
	/// No segments at all: `use add;`. Distinct from `Unresolved` because
	/// there is no segment to point a label at, and distinct from
	/// `Resolved` because there is no namespace to look the leaf up in —
	/// conflating the three into an `Option` is what let this spelling
	/// through silently.
	Empty,
	/// A segment naming something that isn't a module.
	NotAModule(ast::Spanned<SymbolU32>, SourceSpan),
	/// A segment naming nothing at all.
	Unresolved(SourceSpan),
}

/// The outcome of a scope-chain lookup — see
/// [`Builder::lookup_scope_chain`].
enum ScopeLookup {
	NotFound,
	Found(SymbolEntry),
	/// Two or more globs at one scope level supply *distinct* items for this
	/// name, so which one wins is nothing but `use`-statement order.
	///
	/// Carries every candidate paired with the glob that supplied it,
	/// because the thing worth pointing a label at is the `use` statements —
	/// each definition is fine on its own; it's importing both that isn't.
	/// Always holds at least two entries.
	Ambiguous(Box<[(SymbolEntry, SourceSpan)]>),
}

impl ScopeLookup {
	/// What this name resolves to with ambiguity set aside: the first
	/// candidate in `use` order, which is exactly what resolution silently
	/// picked back when ambiguity wasn't detected at all.
	fn symbol(&self) -> Option<SymbolEntry> {
		match self {
			ScopeLookup::NotFound => None,
			ScopeLookup::Found(entry) => Some(*entry),
			ScopeLookup::Ambiguous(candidates) => Some(candidates[0].0),
		}
	}
}

/// Outcome of [`Builder::claim_name_binding`].
#[derive(Clone, Copy, PartialEq)]
pub(super) enum PendingClaim {
	/// No prior definition existed in this scope; `Pending(id)` was
	/// installed and this item owns the name.
	Claimed,
	/// The scope already had a binding; a duplicate-definition diagnostic
	/// was pushed against it and nothing was installed for this item.
	Duplicate,
}

/// What to call a `SymbolKind` in prose.
fn symbol_kind_noun(kind: SymbolKind) -> &'static str {
	match kind {
		SymbolKind::Enum { .. } => "enum",
		SymbolKind::Struct { .. } => "struct",
		SymbolKind::Module { .. } => "module",
		SymbolKind::Memory { .. } => "memory",
		SymbolKind::Trait { .. } => "trait",
		SymbolKind::TypeSet { .. } => "type set",
		SymbolKind::Global { .. } => "global",
		SymbolKind::Function { .. } => "function",
		SymbolKind::Const { .. } => "constant",
		SymbolKind::TraitAssocType { .. } => "associated type",
		SymbolKind::TypeAlias { .. } => "type alias",
	}
}

/// [`symbol_kind_noun`], but for a raw `SymbolEntry` — `Pending` stays vague
/// on purpose: its signature hasn't been computed, so the specific kind
/// isn't known yet and guessing would be worse than the generic word.
fn symbol_entry_noun(entry: SymbolEntry) -> &'static str {
	match entry {
		SymbolEntry::Pending(_) => "item",
		SymbolEntry::Resolved { kind, .. } => symbol_kind_noun(kind),
	}
}

fn report_not_a_namespace(name: &str, span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::NotANamespace.code())
		.with_message(format!("`{name}` is not a module"))
		.with_label(
			span.primary_label()
				.with_message("only a module can be used as a path prefix"),
		)
}

fn report_import_without_module(
	name: &str,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredIdentifier.code())
		.with_message(format!("unresolved import `{name}`"))
		.with_label(
			span.primary_label()
				.with_message("no module to import this from"),
		)
		.with_note(format!(
			"a `use` names where the item comes from, as in `use math::{name};`"
		))
}

fn report_unresolved_import(
	name: &str,
	module: &str,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredIdentifier.code())
		.with_message(format!("no `{name}` in `{module}`"))
		.with_label(
			span.primary_label()
				.with_message("not found in this module"),
		)
}

pub(super) fn report_private_item(
	name: &str,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::PrivateItem.code())
		.with_message(format!("`{name}` is private"))
		.with_label(span.primary_label().with_message("this item is not `pub`"))
}

pub(super) fn report_missing_import_alias(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingImportAlias.code())
		.with_message("import requires an `as` alias")
		.with_label(
			span.primary_label()
				.with_message("expected `as <name>` here"),
		)
}

fn report_cyclic_type_dependency(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
        .with_code(DiagnosticCode::CyclicTypeDependency.code())
        .with_message("cyclic type dependency")
        .with_label(span.primary_label())
        .with_note("types cannot have infinite size; consider using a pointer to break the cycle")
}

pub(super) struct DuplicateDefinitionDiagnostic<'a> {
	pub(super) name: &'a str,
	pub(super) namespace: SymbolNamespace,
	pub(super) first_definition: SourceSpan,
	pub(super) second_definition: SourceSpan,
}

pub(super) fn report_duplicate_definition(
	diagnostic: DuplicateDefinitionDiagnostic<'_>,
) -> Diagnostic<FileId> {
	let namespace = match diagnostic.namespace {
		SymbolNamespace::Type => "type",
		SymbolNamespace::Value => "value",
	};
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateDefinition.code())
		.with_message(format!(
			"the name `{}` is defined multiple times",
			diagnostic.name
		))
		.with_label(diagnostic.second_definition.primary_label())
		.with_label(diagnostic.first_definition.primary_label().with_message(
			format!(
				"previous definition of the {} `{}` here",
				diagnostic.name, namespace
			),
		))
}
