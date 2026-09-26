# Glob import / `pub use *;` reexport — implementation handoff

Status as of this note: mid-implementation, uncommitted, on branch `tir-refactor`.
All changes described below are **uncommitted working-tree edits** — if you're
reading this from a different checkout/machine, they won't be there unless
they were committed+pushed (or the filesystem is actually shared). Check
`git status`/`git diff --stat` first thing.

## What this task is

Finishing glob import resolution (`use path::*;` and `pub use path::*;`) in
the new Phase 1/1.5 rewrite of TIR's name resolution
(`crates/wx-compiler/src/tir/defs.rs` = prescan, `crates/wx-compiler/src/tir/imports.rs`
= demand-driven `use` resolution). Named imports were already fully working
before this session (see `imports.rs`'s existing, unchanged, well-tested
`ensure_use_item`/`compute_use_item`/`ensure_use_path` machinery). Globs were
scanned into `UseItemDef`/`UseItemKind::Glob` but never actually resolved —
`Namespace::glob_imports` existed as a field but nothing populated it.

This whole `defs.rs`/`imports.rs` pair is **not yet wired into the rest of
the compiler** — it's replacing an older system that still lives at
`crates/wx-compiler/src/tir/builder/modules.rs` (`lookup_scope_chain`,
`wildcard_imports`, `SymbolKind`, etc. — old naming, old data model). That's
why `cargo build`/`cargo clippy` show a huge pile of "never constructed /
never used" dead-code warnings on everything in `defs.rs`/`imports.rs` — this
is pre-existing, expected, mid-refactor state, **not a regression to chase**.
The user explicitly said to ignore clippy on this branch for now.

## Language-design decisions made (read this before changing behavior)

Established through a long back-and-forth (see conversation for full
reasoning) — the headline goal was: get most of what Rust's glob imports do,
**without** Rust's real fixed-point iteration over the whole module graph,
because that's exactly the complexity the user wants to avoid.

1. **A private glob (`use x::*;`) never installs a binding, ever, and is
   structurally incapable of creating a cycle.** It's just a pointer,
   recorded in `Namespace::glob_imports`, consulted later (Phase 3, body
   lookup — not built yet, see below) as a **one-hop, non-recursive**
   fallback: check the target's own binding, full stop. It never chases the
   target's *own* glob imports. Two modules privately glob-importing each
   other (`mod a { use crate::b::*; } mod b { use crate::a::*; }`) is
   completely harmless under this model — there is no shared traversal that
   could ever loop. Pinned by
   `tir::imports::tests::mutually_private_globs_are_not_a_cycle`.

2. **A `pub use x::*;` is real re-export** (not banned) — the namespace's own
   externally-visible surface now includes whatever `x` exposes. This is the
   "allow it, but ban cycles" option, chosen over "ban `pub`-glob re-export
   entirely" (the two options discussed early in the conversation — the user
   picked the former because the cycle-ban is cheap given the
   already-existing per-item cycle-detection machinery, whereas banning
   re-export entirely would also kill the legitimate "facade module"
   pattern).

3. **Cycles in the `pub`-glob re-export graph are rejected**, but via a
   single memoized DFS reusing the *exact same* per-item
   `ResolveStatus`/`Cycle`-detection shape that named-import cycle
   detection (`ensure_use_item`/`item_state`) already had — **not** a
   separate graph algorithm, and definitely not Rust's real fixed point.
   Concretely: resolving a `pub use path::*;` item recurses into the
   target's own pending `pub`-glob items via the same `ensure_use_item`
   entry point everything else uses, so re-entering an already-`Resolving`
   item is caught for free.

4. **`pub use *;` (bare, no path) doesn't exist as a case to worry about** —
   confirmed the parser already requires at least one identifier before
   `::*` (`ast::mod.rs`'s `parse_use_tree` always calls `parse_path_ident`
   first), so `use *;` is already a plain `UnexpectedToken` parse error.
   Pinned by `ast::tests::test_bare_glob_with_no_path_reports_unexpected_token`.

5. **`pub use foo::*;` (a real path) was already valid syntax** before this
   session — confirmed via the pre-existing, passing
   `ast::tests::test_pub_use_reexports_without_diagnostic`. Nothing to do at
   the parser level.

6. **A namespace's own direct/named binding always wins over anything
   glob-derived, silently, unconditionally** — no duplicate-definition check
   is ever run between a real declaration and a glob candidate, because
   globs never touch `bindings` at all (this was a real bug in an earlier
   draft of this session's work — caught by the user with a concrete Rust
   example — fixed by never installing glob-derived bindings anywhere).
   Pinned by `local_definition_silently_wins_over_a_colliding_pub_glob`.

## What's actually implemented now

### `crates/wx-compiler/src/tir/defs.rs`

- `UseItemKind::Glob` gained a `span: TextSpan` field (the `x::*` text,
  correctly narrowed even inside a `use a::{b::*, c}` group). This required
  changing `scan_use_tree`'s signature from `&ast::UseTree` to
  `&ast::Spanned<ast::UseTree>` so the parser's already-correct per-node span
  is available at every recursion depth instead of being stripped before the
  call.
- `GlobImport` reshaped from `{ namespace, span }` to
  `{ use_item: UseItemIndex, namespace: NamespaceIndex }` — `namespace` here
  is now the **resolved target**, and everything else (whether it's `pub`,
  the declaring namespace, its own span) is read back through `use_item`
  rather than duplicated. Mirrors the existing `Binding::source:
  BindingSource::Import(UseItemIndex)` pattern exactly (see
  `Binding::declaration_span`, which now has a real `Glob` arm instead of
  `unreachable!()`).
- `pending_pub_glob_reexports: HashMap<NamespaceIndex, SmallVec<UseItemIndex>>`
  added to `DefinitionRegistryBuilder`, populated in `scan_use_tree`'s `Glob`
  arm when `pub_span.is_some()`. Mirrors `pending_named_imports`'s shape,
  just keyed by declaring namespace alone (a glob has no name to key on).
  Threaded through into `imports::resolve_use_paths`.
- `BindingTarget` now derives `PartialEq, Eq` (needed to dedup "same def
  reached through two different `pub` edges" when merging ambiguity
  candidates).
- New on `NamespaceLookup` (the existing trait implemented on `[Namespace]`):
  - `direct_lookup(namespace, key) -> Option<BindingCandidate>` — the
    namespace's own binding only, no glob involvement, no ambiguity possible.
  - `indirect_lookup(use_items, namespace, key) -> BindingLookup` — walks
    only `namespace`'s **`pub`-marked** glob edges, recursing via `lookup`
    (not into itself) at each hop, so a chain composes through direct
    declarations and further re-exports alike. Never touches a private glob
    edge.
  - `lookup(use_items, namespace, key) -> BindingLookup` — `direct_lookup`,
    falling back to `indirect_lookup`. **This is the one both
    `resolve_member_def` and `binding_to_import_scope` call now**, and is
    designed to also be what Phase 3's eventual rewritten identifier lookup
    calls for each of a namespace's own glob targets (see "Not done" below).
  - New types: `BindingCandidate { target: BindingTarget, visibility:
    Visibility }` (the two travel together everywhere), and `BindingLookup {
    NotFound, Found(BindingCandidate), Ambiguous(Box<[(BindingCandidate,
    SourceSpan)]>) }` — `Ambiguous` carries **every** surviving candidate
    paired with the `pub use` edge responsible for it (an earlier draft only
    carried one candidate, which the user correctly called out as
    insufficient to even write the diagnostic message).
  - `push_candidate` free fn: dedups by `BindingTarget` identity before a
    candidate is added — "same target reached two ways" (a diamond
    re-export) is not a conflict.

### `crates/wx-compiler/src/tir/imports.rs`

- `run()` now drives **every** `use_items` entry through `ensure_use_item`
  (previously filtered to `UseItemKind::Name` only).
- `compute_use_item` dispatches: `Name` keeps its existing, unchanged body;
  `Glob { path, .. }` goes to a new `compute_glob_item`.
- `compute_glob_item(index, path)`: resolves `path` via the **existing**
  `ensure_use_path` (zero new code there — a glob's path prefix gets the
  same demand-driven resolution, alias support, and self-reference cycle
  detection a named import's prefix already had), pushes a `GlobImport` onto
  the declaring namespace's `glob_imports`, and — only if the item is
  `pub` — recurses into `pending_pub_glob_reexports[target]`, calling
  `ensure_use_item` on each. That recursion is the entire cycle check.
- `ensure_use_item`'s `Cycle` arm now branches on `item.kind`: `Name` keeps
  its existing binding-poisoning behavior; `Glob` just reports (reusing
  `report_use_cycle`) and stops — there's no binding to poison since a glob
  never installs one.
- `resolve_member_def` and `binding_to_import_scope` no longer do a raw
  `self.namespaces[scope].bindings.get_mut(&key)` — they call
  `self.namespaces.lookup(self.use_items, scope, key)` and match on
  `BindingLookup`. This is the actual payoff: a named `use m::Y;` can now
  find a `Y` that `m` only exposes via `m`'s own `pub use c::*;`.
- New `report_ambiguous_reexport` (modeled on rustc's E0659, one secondary
  label per contributing `pub use` edge) and new diagnostic code
  `DiagnosticCode::AmbiguousReexport` = `E2096`
  (`crates/wx-compiler/src/diagnostics.rs`).

### Tests added this session

`crates/wx-compiler/src/ast/tests.rs`:
- `test_bare_glob_with_no_path_reports_unexpected_token`

`crates/wx-compiler/src/tir/imports.rs` (`mod tests`), plus a `glob_targets`
helper on the test-local `TestCase`:
- `plain_glob_records_a_fallback_edge_to_its_target`
- `mutually_private_globs_are_not_a_cycle`
- `mutually_pub_globs_report_cyclic_import`
- `self_targeting_pub_glob_reports_cyclic_import`
- `acyclic_pub_glob_chain_resolves_without_diagnostics` (3-module DAG,
  `c -> b -> a`, reached twice, must not be mistaken for a cycle)
- `named_use_reaches_through_a_pub_glob_reexport`
- `private_glob_reexport_does_not_leak_to_named_use`
- `two_pub_globs_disagreeing_on_a_name_report_ambiguous_reexport`
- `local_definition_silently_wins_over_a_colliding_pub_glob`

All pass. Verify with:

```
cargo build -p wx-compiler --lib          # clean (only pre-existing dead-code warnings)
cargo test -p wx-compiler --lib "tir::"   # 35 in tir::imports, 2 in tir::defs
cargo test -p wx-compiler --lib "ast::tests::"
```

Do **not** run `cargo clippy -p wx-compiler --no-deps -- -D warnings` as a
gate right now — it fails on pre-existing dead code from this module not
being wired in yet, unrelated to this work. The user explicitly said to
ignore it for now.

## What's NOT done — pick up here

1. **Phase 3 (ordinary identifier/body lookup) hasn't been touched.** It
   still lives entirely in the old `tir/builder/modules.rs`
   (`lookup_scope_chain`, `wildcard_imports`, old `SymbolKind`/`DefKey`
   types — a completely separate, not-yet-migrated data model from
   `defs.rs`'s `Namespace`/`BindingTarget`/`DefKey`). None of this session's
   work is reachable from there yet. When that migration happens, its own
   per-namespace glob-consultation step should call the *same*
   `NamespaceLookup::lookup` added here for each of a namespace's own glob
   targets (unfiltered by pub/private, since "my own body can see all my
   own globs" — only the *recursion into a further glob's own edges* should
   stay pub-only, which `lookup`/`indirect_lookup` already enforce
   correctly regardless of who calls them).

2. **Known, accepted limitation, deliberately not fixed:**
   `indirect_lookup`'s recursion into a `pub`-glob target does **not** force
   that target's own not-yet-resolved named imports before reading its
   `bindings` — only the *immediate* queried scope gets forced (matching the
   pre-existing forcing pattern already in `binding_to_import_scope`/
   `compute_use_item`). In a contrived resolution order, a named import
   several `pub` hops away, not yet forced by anything else, could
   transiently read as absent. Discussed at length and deliberately not
   built — the fix (moving the recursion out of the trait into
   `ImportResolver` so it can force at every level) reintroduces real
   complexity for a narrow edge case. Revisit only if it actually bites.

3. **Enum/variant glob imports** (`use Color::*;` bringing in `Red, Green,
   Blue`) are explicitly out of scope. `ImportScope` in `imports.rs` still
   has `// TODO: Enum, Variant etc..`.

4. **Unused-import tracking** (`record_binding_access`) is a no-op for a
   binding reached only through `indirect_lookup` — there's no direct slot
   in the *querying* namespace to mark as consulted. Not a regression (no
   "unused import" diagnostic exists anywhere in this new system yet), just
   worth remembering if that feature gets built later.

5. Nothing has been reviewed with `cargo clippy` or `cargo fmt --check` on
   this branch — explicitly deferred per the user's instruction, but worth
   doing once the module is wired into the rest of the pipeline for real.

## Collaboration notes for whoever continues this

The user iterates on API shape before wanting code — expect multiple rounds
of "what should this be called / what should it return" before landing on
final types (e.g. `BindingCandidate`/`BindingLookup` went through several
shapes: a bare `unreachable!`-guarded tuple, then `ExternalLookup`/
`ExternalBinding` with a single-candidate `Ambiguous`, before landing on the
current shape). Prefer proposing 2-4 concrete named options with tradeoffs
over picking one silently. Reuse existing patterns rather than inventing new
ones — e.g. "index back into `use_items`, don't clone" was explicitly
established for `Binding`/`GlobImport` and should be the default instinct
for any new provenance-carrying type in this file.
