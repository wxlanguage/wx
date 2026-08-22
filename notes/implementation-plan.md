# Implementation plan: crate manifests (`wx.json`)

## Context

This implements the design settled in `notes/temp.md` after an extended design discussion.
The motivating bug: every frontend (CLI, LSP, wasm, tests) hardcodes `load_stdlib()` +
`load_binary()`, so pointing the compiler at its own `crates/wx-compiler/std/main.wx`
double-loads the stdlib (once embedded, once from disk), producing duplicate
inherent-impl-candidate errors — you currently cannot typecheck the standard library
directly. The root cause is that nothing in the compilation says what *kind* of crate is
being built. The design doc works this into a general mechanism (crate kind, a `wx.json`
manifest, general name-based dependency resolution) rather than a one-off fix, because real
library crates are an explicit near-term goal.

This plan breaks that design into independently shippable, independently testable steps.
Steps 1→4 are strictly sequential and get the motivating bug fixed by the end of step 4.
Step 5 only depends on step 1 and can be built in parallel with steps 2–4. Step 6 depends
on steps 2–3. Step 7 is optional polish, not blocking anything.

Line numbers below were re-verified against current `HEAD` (commit `ff7b5f8`) right before
writing this plan.

## Step 1 — `CrateKind`, pure refactor, zero behavior change

**Files:** `crates/wx-compiler/src/vfs/mod.rs`, `crates/wx-compiler/src/tir/builder.rs`

- Add `pub enum CrateKind { Binary, Library }` (derive `Clone, Copy, PartialEq, Eq`) to
  `vfs/mod.rs`.
- Add `pub kind: CrateKind` to `CrateGraph`, alongside the existing `name: Option<SymbolU32>`
  (unchanged for now — still `Some` only for named/library crates at this point).
- `CompilationUnitBuilder::load_crate` takes an explicit `kind: CrateKind` parameter instead
  of inferring library-ness from `name.is_some()`. `load_library`/`load_stdlib` pass
  `CrateKind::Library`; `load_binary` passes `CrateKind::Binary`. External signatures of
  `load_stdlib`/`load_binary`/`load_library` don't change, so none of the four existing call
  sites (`wx-cli/src/main.rs`, `wx-lsp/src/lib.rs`, `wx-compiler-wasm/src/lib.rs`,
  `TestCase`) need touching yet.
- `tir/builder.rs`'s crate-namespace-creation loop (`build()`, the
  `// Create a top-level namespace for each named (library) crate` block, currently gated
  `if let Some(crate_name) = crate_graph.name`) switches its guard to
  `if crate_graph.kind == CrateKind::Library`, then unwraps `name` inside
  (`.expect("library crate must have a name")` — safe, since step 1 doesn't change who sets
  `name`, only what's read to decide importability).

**Validation:** `cargo test -p wx-compiler` — expect zero snapshot diffs; this step changes
no observable behavior, only which field drives the namespace-creation decision.

## Step 2 — `CrateManifest` + `wx.json` parsing (data model only, not wired in yet)

**Files:** `crates/wx-compiler/src/vfs/mod.rs`

- Add `CrateManifest { name: String, r#type: CrateManifestType, dependencies: HashMap<String, DependencyEntry> }`
  with `CrateManifestType { Bin, Lib }` and `DependencyEntry { path: String }`, all deriving
  `serde::Deserialize`. `serde_json` is already a `wx-compiler` workspace dependency
  (confirmed in `Cargo.toml`) — no dependency changes needed anywhere for this step.
- Add a pure `pub fn parse_manifest(json: &str) -> Result<CrateManifest, serde_json::Error>`
  (or equivalent) so it's directly unit-testable without touching the loader.
- Validate `name` against the existing identifier grammar used elsewhere in the lexer at
  parse time (reject hyphens etc.) — reuse whatever validation function `ast`'s identifier
  lexing already exposes rather than re-deriving the grammar.

**Validation:** unit tests alongside this code (or in `vfs/tests.rs`, which already exists)
covering: valid bin/lib manifests, missing `name`, invalid `type`, an invalid identifier as
`name`, a `dependencies` entry with a relative path.

## Step 3 — general dependency resolution + implicit-`std` rule + duplicate-name diagnostic

**Files:** `crates/wx-compiler/src/vfs/mod.rs`

- New entry point, e.g. `pub fn open_crate(path: &str, source: &impl FileSource) -> Result<CompilationUnit, ()>`,
  replacing the two-line `load_stdlib()+load_binary()` dance frontends currently hardcode:
  - No `wx.json` found for `path`'s containing directory → today's behavior exactly:
    anonymous `Binary`, `name: None`, `load_binary` on `path` directly.
  - `wx.json` found → parse it (step 2), load the root crate as `<manifest_dir>/main.wx`
    with `name`/`kind` from the manifest.
  - Resolve each `dependencies` entry by its `path`, recursively, registering each crate
    into a name → `CrateId` map (reuse `interner.get_or_intern`, same lookup pattern
    `use module::*` already uses for path segments). A name already claimed when something
    else tries to claim it is a new diagnostic — add `DuplicateCrateName` to the existing
    `DiagnosticCode` macro-generated enum in this file (follows the same `E2xxx` numbering
    as `ModuleFileNotFound`/`AmbiguousModuleFile` already there).
  - After all explicit resolution finishes: if nothing has claimed the name `std` yet, call
    `load_stdlib()` and register it. This one check implements the design doc's implicit-std
    rule in full — it naturally no-ops when the root crate is itself named `std`, and is
    naturally overridden by an explicit `"std"` dependency entry, with no special-casing.
- This function does not yet get called from any frontend — that's step 4.

**Validation:** tests in `vfs/tests.rs` (pattern already established there) covering: a
plain binary with no manifest gets std exactly as today; a manifest'd binary with no deps
gets std; a root crate named `std` does not get a second std loaded; an explicit
`"dependencies": {"std": {"path": ...}}` entry is used instead of the embedded one; two
crates both claiming the same name in one graph produces `DuplicateCrateName`.

## Step 4 — wire the CLI, close the original bug

**Files:** `crates/wx-cli/src/main.rs`, new `crates/wx-compiler/std/wx.json`

- Replace `load_compilation`'s body with a call into step 3's `open_crate`.
- When a manifest was used, print the resolved identity (name, kind, entry file) to stderr
  alongside existing diagnostic output, per the design doc's transparency requirement.
- `cmd_compile`: hard error if the resolved root crate's `kind` is `Library`
  ("a library crate has no WASM output, use `wx check`").
- Add `crates/wx-compiler/std/wx.json`: `{"name": "std", "type": "lib"}`. No rename of the
  existing `main.wx` needed.

**Validation — this is the concrete milestone that closes the original bug:**
`cargo run -p wx-cli -- check crates/wx-compiler/std` should succeed cleanly with no
duplicate-candidate errors. Also re-run `cargo test -p wx-compiler` to confirm the existing
anonymous-file test suite is unaffected by the new resolution path.

## Step 5 — library-crate restrictions (can be built in parallel with steps 2–4; only needs step 1)

**Files:** `crates/wx-compiler/src/tir/builder.rs`

- Build a `FileId → CrateKind` lookup at the top of `build()`, alongside the existing
  crate × module walk that already builds `source_modules` — same traversal, one more map.
- Add four diagnostic codes to this file's `DiagnosticCode` enum (e.g.
  `ImportInLibraryCrate`, `ExportInLibraryCrate`, `MemoryInLibraryCrate`,
  `MutableGlobalInLibraryCrate`).
- Guard at the four confirmed sites (verified against current `HEAD`):
  - `ast::Item::Import` arm in `pre_scan_item`, line 5252 — bail before creating the import
    namespace.
  - The Phase 4 `ast::Item::Export` handling loop (not the no-op prescan arm at line 5394)
    — the crate is already in hand there.
  - `ast::Item::Memory` arm in `pre_scan_item`, line 4957.
  - `ast::Item::Global` arm in `pre_scan_item`, line 4800 — only when `mut_span.is_some()`.

**Validation:** TIR tests in `tir/tests.rs` using `TestCase::new_multi_file` with one file
loaded as a `Library`-kind crate (via `load_library` directly — doesn't need step 2/3's
manifest machinery at all, so this step is genuinely independent). Assert each of the four
constructs produces its diagnostic in a library and compiles clean in a binary. Also assert
`report_unused_items` still behaves correctly on a library root (it already skips
`pub_span.is_some()` items — confirm that continues to hold, don't just take it on faith).

## Step 6 — LSP integration

**Files:** `crates/wx-lsp/src/lib.rs`

- Extend manifest discovery: alongside the existing `discover_crate_root`'s upward walk for
  `main.wx`, also walk upward for `wx.json`, calling step 2's `parse_manifest` — `wx-lsp`
  already depends on `wx-compiler`, so no new Cargo dependency is needed to reach it.
- When a manifest is found, route through step 3's `open_crate` instead of `parse_root`'s
  current hardcoded two-line load. No manifest found → today's behavior, unchanged.

**Validation:** LSP tests in `wx-lsp/src/tests.rs` opening a `wx.json`-described workspace;
confirm diagnostics match the CLI path, and confirm go-to-definition into `std` now lands in
a real file (once std loads from disk with a real absolute path instead of the
`wx://std/...` virtual scheme).

## Step 7 — small polish (optional, independent, not blocking anything)

- `cmd_compile`'s default output filename derives from the manifest's `name` when present,
  instead of the entry file's stem. Small change in `wx-cli/src/main.rs`, can land any time
  after step 4.
- `resolve_operator_traits`'s current `panic!` on a missing `#[tag = "..."]` item (in
  `tir/builder.rs`) becomes a proper diagnostic — worth doing once step 4/5 make an
  incomplete standalone/replacement `std` crate a reachable end-user path for the first
  time, rather than only an internal compiler-team invariant.

## Explicitly out of scope for this plan

Per the design doc: `wx std vendor`, transitive dependency resolution, and Rust-style dual
`main.wx`+`lib.wx` coexistence are backlogged/rejected — not part of this implementation.
