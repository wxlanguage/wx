# `wx build`/`wx format` finalized as manifest-required, and wx-lsp migrated off the `main.wx` convention

Follow-up session to the `wx.json` package-manifest work
([`2026-08-23-package-manifests-path-types-and-format-cli-design.md`](2026-08-23-package-manifests-path-types-and-format-cli-design.md),
[`2026-08-23-format-cli-and-stdlib-provider-design.md`](2026-08-23-format-cli-and-stdlib-provider-design.md)).
Those sessions designed the manifest schema and the `wx format` CLI shape but
explicitly deferred actually wiring the CLI to use it. This session did that,
then discovered wx-lsp needed the identical migration (it was still finding
projects by looking for a file literally named `main.wx`), which surfaced a
string of real, reproducible LSP bugs along the way.

## Summary

`wx.json` is now mandatory everywhere, with no anonymous/file-only fallback
left in the system:

- `wx compile` renamed to `wx build` (it builds whole projects now, not a
  single file) — both it and `wx check` always take a project directory
  (default `.`).
- `wx format` redesigned to exactly one project per invocation: a directory
  positional (always requiring `wx.json`), an optional `--files a.wx,b.wx`
  to restrict to specific named files instead of walking the whole module
  tree, and `--check`.
- `vfs::open_binary` (the old anonymous-file compilation entry point)
  deleted outright, along with its two unit tests — `open_manifest` is now
  the only public entry point that resolves dependencies.
- All 19 `examples/*` subdirectories got a `wx.json` (18 `"bin"`, `arena`
  `"lib"`) so they keep building under the new model.

wx-lsp's own project-root discovery was still on the old convention —
`discover_package_root` looked for a file named `main.wx`, unrelated to
whether a `wx.json` existed anywhere. Migrated to match: it now walks
ancestors for `wx.json` and returns the *directory*, and a file with no
`wx.json` ancestor gets a visible, rust-analyzer-style "unlinked file" hint
(`INFO` severity, whole-document range via the `u32::MAX`/`u32::MAX`
end-position trick, `UNNECESSARY` tag to fade it) instead of silently doing
nothing.

## Bugs found chasing the wx-lsp migration

Each of these was a real, user-reported, reproducible regression against the
new wx.json-based architecture, found and fixed one at a time rather than
guessed at:

1. **Stdlib URIs had a double slash.** `file_id_to_uri` built
   `format!("wx://std/{}", file.name)` where `file.name` already started
   with `/`, producing `wx://std//main.wx` — the client's URI handling
   treated that as a different, unresolvable virtual file, breaking
   go-to-definition into `std` and its own separate handler
   (`virtual_file_content`, which does a literal `strip_prefix("wx://std")`)
   with an "unknown stdlib file" error. Fixed to
   `format!("wx://std{}", file.name)`.

2. **`Package`-kind namespace accesses were never recorded.**
   `build_symbol_index`'s match on `ModuleDeclarationKind` had a `continue`
   for the `Package(file_id)` arm (dependency edges — `std`, or an explicit
   `wx.json` dependency like `pow`) that skipped the shared
   `for access in &ns.accesses { index.references.push(...) }` loop every
   other arm ran. Result: hover/goto-def/semantic-highlighting worked for a
   user's own `module x;` declarations but not for `std::` or a declared
   dependency's namespace token — confirmed by the user testing both shapes
   side by side. Fixed by moving the access-recording loop before the
   `continue`.

3. **A bare `todo!()` could kill the LSP's actor task permanently.**
   `resolve_path_segments_as_bound` (qualified bounds, `T: module::Trait`)
   had a `todo!()` on one resolution-failure branch. Since the whole LSP
   backend runs its state machine on one actor task, hitting it didn't just
   fail one request — it panicked the task and silently stopped *every*
   LSP feature until the client noticed and respawned the process. This is
   the actual explanation for "everything stops working, then fixes
   itself" reports. Replaced with a real diagnostic
   (`report_undeclared_type`).

4. **Fixing (2) introduced a duplicate access-recording bug.** Adding a
   bare `SymbolKind::Module` arm to `record_type_kind_access` (the fix for
   bug 2) caused two snapshot tests to start showing an exact duplicate
   `SourceSpan` for the same token. Traced to `build_namespace_member_expression`
   and `resolve_namespace_type_member`, which each had their own pre-existing,
   ad-hoc inline push recording "the namespace I'm about to dispatch
   through" — always redundant with the canonical recording point once (2)
   made that canonical point cover namespaces too. Proved safe to delete
   both unconditionally (not just for the traced cases) via `symbol_kind_to_type`
   being the *only* place `Type::Namespace` values are constructed, and both
   its call sites already invoking the canonical recording path first.

5. **Editing an open dependency package's file could wipe its dependent's
   entire cache.** `owning_root` reverse-scanned `published_by_root` —
   `HashMap<PathBuf, HashSet<PathBuf>>`, genuinely many-to-many (a `pow`
   dependency's files show up under every dependent root that reaches
   them) — with `.find_map(...).contains(file)`, which just returns
   whichever root happens to iterate first. So editing `pow`'s own file
   (correctly attributing it to `pow`'s own root when `pow` is open
   directly) could get attributed to `hashing`'s root instead depending on
   HashMap iteration order, and `compute_refresh` would then clear
   `hashing`'s cache for a file that isn't even part of a change to
   `hashing`. Fixed with a genuine 1:1 `own_root: HashMap<PathBuf, PathBuf>`,
   written only by `compute_refresh` for the exact file it's asked to
   refresh — `published_by_root` stays many-to-many and is used only for
   its original purpose (diffing what to clear), not repurposed as a
   reverse index it was never structured for.

A broader question came up mid-investigation: should wx-lsp move toward a
salsa/rust-analyzer-style incremental query architecture instead of
whole-project batch recompute per root? Answer, after walking through how
rust-analyzer/gopls/tsserver/clangd each handle this: interesting, but out
of scope — wx-compiler's own internals are a monolithic batch pipeline with
no query-level factoring, so adopting real incrementality at the LSP layer
would need compiler-level changes too. Deferred, not rejected.

## Debug-log redesign

Along the way, the LSP's debug logging (parse/typecheck/format timings)
went through several iterations, driven entirely by real VS Code Output
panel readability complaints rather than a spec:

- Started as independent flat log lines per phase (`parsing took...`,
  `typechecking took...`), which didn't show which package/root a line was
  about.
- First fix: embed the root path directly in each line.
- Redesigned into a `Trace` struct accumulating named timed steps
  (`step(label, || ...)`), rendered as one tree-branched (`├─`/`└─`) block
  per logical operation with a total on the heading — chosen over flatter
  alternatives specifically for showing dependency relationships (parse as
  a sub-step of typecheck, not a sibling log line).
- Then: VS Code's Output panel only timestamp-and-severity-prefixes a
  message's *first* line, so a heading padded with a long absolute path
  became disproportionately hard to read compared to its own body lines.
  Tried splitting `Trace` into separate `info`/`steps` lists — rejected for
  rendering both kinds of line identically (no visual way to tell "this is
  context" from "this is a measurement" apart). Tried unifying everything
  into one `Vec<(&'static str, String)>` — reconsidered again because it
  throws away real structure: every trace actually has exactly one
  required, typed fact (the file that caused it) plus zero or more timed
  steps, not an open bag of arbitrary key-value pairs.
- Settled shape: `Trace { path: PathBuf, steps: Vec<(&'static str, Duration)> }`,
  constructed as `Trace::new(path)` where `path` is the file that triggered
  the operation (its package root is recoverable from the shared path
  prefix, so storing both was redundant). `finish(operation)` renders a
  short heading (`typecheck`, `format`) with the steps' total, then every
  line after it — the `file: "..."` line and each tree-branch step —
  two-space indented so it visually groups under the heading instead of
  blending into the surrounding VS Code log list.
- The one-off `"typecheck {root:?} — cache hit, no recompute"` flat line
  and the ad-hoc `virtual_file_content uri=...` debug log were both
  reformatted through the same `Trace::finish` path instead of staying
  bespoke, so every LSP log line now has one consistent shape.

## Key findings

- `cargo build` does not compile `#[cfg(test)]` code — a signature change
  to `compile_root` passed `cargo build -p wx-lsp` cleanly while a stale
  4-argument call site in `tests.rs` silently went unchecked; only
  `cargo test -p wx-lsp` caught it. Worth remembering as a checklist item
  for any signature change touched only by tests.
- The root `wx.json` (a stray, unregistered manifest sketching a future
  `meta` section, not consumed by anything real — same file noted in
  [`2026-08-23-package-manifests-path-types-and-format-cli-design.md`](2026-08-23-package-manifests-path-types-and-format-cli-design.md))
  had drifted to a `"fmt"` key while `PackageManifest`'s field stayed
  `format` with no `#[serde(rename)]` — silently ignored rather than
  erroring, per the manifest's own "unknown keys are ignored" design.
  Reverted the key back to `"format"` rather than renaming the field:
  `format` is the CLI subcommand's real name (`fmt` is only a
  `visible_alias`), the struct is `FormatManifest` not `FmtManifest`, and
  every other `wx.json` key (`dependencies`, `entry`, `type`) is a full
  word, not an abbreviation.
- Found but not fixed: pre-existing bugs in `factorial`/`globals` (missing
  `use std::*;`), `raycaster` (unwired `std::math`), and `vec` (stale
  pointer-mutability-era type errors), surfaced purely by giving them
  `wx.json` manifests and trying to build them. Not part of this session's
  scope; reported for a future pass.

## Follow-ups

- Package-identity-based caching/dedup in `vfs::resolve.rs`, so a shared
  dependency (e.g. `pow`) open both directly and as another project's
  dependency isn't parsed and typechecked twice. Explicitly deferred by
  request — "a large rework which I can't afford now."
- `doom/` was deliberately left unmigrated to the manifest model —
  structurally ambiguous, not a quick `wx.json` addition like the other 19.
- The `factorial`/`globals`/`raycaster`/`vec` example bugs above.
