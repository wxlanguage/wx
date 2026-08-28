# Implementation plan: package manifests (`wx.json`)

## Context

This implements the design settled in `notes/temp.md` after an extended design discussion.
The motivating bug: every frontend (CLI, LSP, wasm, tests) hardcodes `load_stdlib()` +
`load_binary()`, so pointing the compiler at its own `crates/wx-compiler/std/main.wx`
double-loads the stdlib (once embedded, once from disk), producing duplicate
inherent-impl-candidate errors — you currently cannot typecheck the standard library
directly. The root cause is that nothing in the compilation says what *kind* of package is
being built. The design doc works this into a general mechanism (package kind, a `wx.json`
manifest, general name-based dependency resolution) rather than a one-off fix, because real
library packages are an explicit near-term goal.

This plan breaks that design into independently shippable, independently testable steps.
Step 0 is a pure rename, prerequisite to everything else. Steps 1→4 are strictly sequential
and get the motivating bug fixed by the end of step 4. Step 5 only depends on step 1 and can
be built in parallel with steps 2–4. Step 6 depends on steps 2–3. Step 7 is optional polish,
not blocking anything.

Line numbers below were re-verified against current `HEAD` (commit `2462a88`) right before
writing this plan.

## Naming: "package", not "crate"

The compiler's internal vocabulary currently says "crate" (`CrateId`, `CrateGraph`, etc.) —
inherited from Rust by default, not for any reason specific to this codebase. WX targets the
WASM/web ecosystem, where the equivalent concept is universally called a "package" (npm,
`package.json`). There's no offsetting reason to keep the Rust-flavored term, so this plan
renames the concept wholesale (Step 0) before building the manifest feature on top of it, so
every new type introduced afterward (`PackageKind`, `PackageManifest`, ...) is named
consistently from the start rather than needing its own rename later.

## Why JSON, not TOML

Cargo's `Cargo.toml` is the obvious precedent, but `wx.json` deliberately picks JSON as the
shipped format instead:

- **Editor autocomplete.** JSON Schema is a de facto standard that every mainstream editor
  (VS Code, JetBrains, Zed) already supports out of the box via a `$schema` field or a
  registered schema association — get real autocomplete, inline validation, and hover docs
  for `wx.json` for free. TOML has no comparably standardized, comparably well-supported
  schema mechanism across editors.
- **Wider adoption in the web ecosystem.** WX targets WASM and its tooling story (the
  playground, editor extensions, npm distribution of `wx` itself) sits closer to the web
  ecosystem than to systems languages. `package.json` and `tsconfig.json` establish JSON as
  the expected manifest format for that audience — `wx.json` following the same convention
  is one less thing for users coming from that world to learn.
- **`serde_json` is already a dependency**, so this costs nothing extra in the dependency
  graph (see step 2).

This is not a claim that JSON is the only format `wx.json` will ever support. The manifest's
Rust data model (`PackageManifest`, step 2) is a plain `serde`-derived struct with no
JSON-specific shape decisions baked in — `serde_json::from_str` and `toml::from_str` were
both verified against the same struct during design and round-trip identically, including
the nested `[package]`/`"package"` grouping (TOML needs no special-casing: bare keys before
any `[header]` already belong to the root table, so `type`/`name` under `[package]` and a
`[dependencies]` table both fall out for free). So: JSON ships first for the reasons above,
but adding TOML later is "add a second `from_str` call gated on file extension," not a schema
redesign — the abstraction is inherent to using `serde`, not something this plan builds.

## Step 0 — rename `Crate*` → `Package*` (pure rename, zero behavior change)

**Files:** `crates/wx-compiler/src/vfs/mod.rs`, `crates/wx-compiler/src/tir/builder.rs`,
`crates/wx-compiler/src/tir/mod.rs`, `crates/wx-lsp/src/lib.rs`

Purely mechanical identifier rename, no logic changes. Confirmed occurrences as of `HEAD`:

- **`vfs/mod.rs`**: `CrateId` (struct, ~line 238) → `PackageId`; `CrateGraph` (struct, line
  265) → `PackageGraph`; `CompilationUnitBuilder.crates: Vec<CrateGraph>` (line 289) →
  `packages: Vec<PackageGraph>`; `CompilationUnit.root_crate: CrateId` (line 280) →
  `root_package: PackageId`; `CompilationUnitBuilder::load_crate` (line 380) →
  `load_package`; local variables `crate_id`/`crate_graph` throughout `load_crate`'s body and
  its helpers (lines 386–479, 541) → `package_id`/`package_graph`. `load_library`/
  `load_binary`/`load_stdlib` keep their names (they don't contain "crate") but their bodies
  call `load_package` instead of `load_crate`.
- **`tir/mod.rs`**: `ModuleDeclarationKind::Crate(CrateId, FileId)` (line 1188) →
  `::Package(PackageId, FileId)`; its doc comment ("named library crate") updated to
  "package"; the `is_import_namespace` match arm (line 3079) updated to the new variant name.
- **`tir/builder.rs`**: every `ModuleDeclarationKind::Crate` reference (lines 1752, 2768,
  2784, 4667) → `::Package`; local variables `crate_graph`/`crate_namespaces`/`crate_base`/
  `crate_name` in and around the namespace-creation loop (lines 1665–1774) →
  `package_graph`/`package_namespaces`/`package_base`/`package_name`; `graph.crates` (line
  1746) → `graph.packages`.
- **`wx-lsp/src/lib.rs`**: `discover_crate_root` (defined line 2405, called lines 548, 1266,
  referenced in doc comments at 1403 and 1456) → `discover_package_root`;
  `ModuleDeclarationKind::Crate(_, _)` match arm (line 1929) → `::Package(_, _)`. Note:
  `pub(crate)` on this same function is Rust's own visibility keyword, unrelated to this
  rename — leave every `pub(crate)` occurrence untouched; only rename the domain-specific
  `Crate`-prefixed identifiers.
- **`wx-cli/src/main.rs`, `wx-compiler-wasm/src/lib.rs`**: no `Crate*` identifiers (both only
  call `load_stdlib`/`load_binary`, whose names don't change) — no edits needed here.

**Validation:** `cargo test -p wx-compiler` and `cargo test -p wx-lsp`, then `cargo insta
accept`. `ModuleDeclarationKind::Crate` is serialized into ~93 TIR snapshot files as a literal
`Crate:` YAML tag, so the snapshot diff is expected and mechanical (`Crate:` → `Package:`) —
review the diff to confirm *only* that tag changed, nothing else. `cargo build --workspace`
to confirm the three dependent crates still compile with no further changes needed.

## Step 1 — `PackageKind`, pure refactor, zero behavior change

**Files:** `crates/wx-compiler/src/vfs/mod.rs`, `crates/wx-compiler/src/tir/builder.rs`

**Depends on step 0** (introduces new code using the renamed vocabulary directly, rather than
naming it `CrateKind` and renaming it later).

- Add `pub enum PackageKind { Binary, Library }` (derive `Clone, Copy, PartialEq, Eq`) to
  `vfs/mod.rs`.
- Add `pub kind: PackageKind` to `PackageGraph`, alongside the existing
  `name: Option<SymbolU32>` (unchanged for now — still `Some` only for named/library packages
  at this point).
- `CompilationUnitBuilder::load_package` takes an explicit `kind: PackageKind` parameter
  instead of inferring library-ness from `name.is_some()`. `load_library`/`load_stdlib` pass
  `PackageKind::Library`; `load_binary` passes `PackageKind::Binary`. External signatures of
  `load_stdlib`/`load_binary`/`load_library` don't change, so none of the four existing call
  sites (`wx-cli/src/main.rs`, `wx-lsp/src/lib.rs`, `wx-compiler-wasm/src/lib.rs`,
  `TestCase`) need touching yet.
- `tir/builder.rs`'s package-namespace-creation loop (`build()`, the
  `// Create a top-level namespace for each named (library) package` block, currently gated
  `if let Some(package_name) = package_graph.name`) switches its guard to
  `if package_graph.kind == PackageKind::Library`, then unwraps `name` inside
  (`.expect("library package must have a name")` — safe, since step 1 doesn't change who
  sets `name`, only what's read to decide importability).

**Validation:** `cargo test -p wx-compiler` — expect zero snapshot diffs; this step changes
no observable behavior, only which field drives the namespace-creation decision.

## Step 2 — `PackageManifest` + `wx.json` parsing (data model only, not wired in yet)

**Files:** `crates/wx-compiler/src/vfs/mod.rs`

- Data model — a struct wrapping a tagged enum, not the enum alone, so `dependencies` is
  declared once and shared by both kinds instead of duplicated per variant. Deliberately
  **not** `#[serde(flatten)]`: nesting under an explicit `"package"` key is the actual
  requirement (grouping identity fields separately from `dependencies`, and mirroring how
  `Cargo.toml`'s `[package]` table would map onto this shape if this ever moved to TOML), and
  flattening buys nothing here that a literal nested field doesn't already give for free —
  verified both shapes round-trip identically through `serde_json`/`toml`.
  ```rust
  #[derive(serde::Deserialize)]
  pub struct PackageManifest {
      pub package: PackageManifestKind,
      #[serde(default)]
      pub dependencies: HashMap<String, DependencySource>,
  }

  #[derive(serde::Deserialize)]
  #[serde(tag = "type", rename_all = "lowercase")]
  pub enum PackageManifestKind {
      Lib {
          #[serde(deserialize_with = "deserialize_package_name")]
          name: String,
      },
      Bin,
  }

  // Single variant today (`{"type": "local", "path": "../other"}`). Tagged from the
  // start — not a flat `{ path: String }` struct — so a future remote/registry source
  // (out of scope for this plan; see bottom) is an additive new variant, not a breaking
  // reshape of every existing `wx.json`'s `dependencies` entries.
  #[derive(serde::Deserialize)]
  #[serde(tag = "type", rename_all = "lowercase")]
  pub enum DependencySource {
      Local { path: String },
  }
  ```
  (`PackageManifestKind`, not `PackageKind`, to avoid colliding with step 1's `PackageKind`
  — that one is the resolved runtime kind on `PackageGraph`; this one is what the manifest's
  `"type"` field actually deserializes to, and additionally carries `name` for `Lib`. Step 3
  converts one into the other when it builds a `PackageGraph`.)
  `serde_json` is already a `wx-compiler` workspace dependency (confirmed in `Cargo.toml`) —
  no dependency changes needed anywhere for this step.
- **No `#[serde(deny_unknown_fields)]` anywhere.** Considered and dropped: (a) it doesn't
  actually work on internally-tagged enums in `serde` — verified empirically, a bare
  `#[serde(tag = "type", deny_unknown_fields)]` enum still silently accepts an unrecognized
  field regardless of flatten/nesting, so achieving it would mean either switching to an
  externally-tagged shape (`{"lib": {"name": ...}}`, worse editor-autocomplete ergonomics
  than a `"type"` discriminant field) or hand-rolling `Deserialize`; (b) it isn't actually
  load-bearing — a typo'd `dependencies` key just means that dependency never gets declared,
  which surfaces downstream as a normal unresolved-name diagnostic (not a silent miscompile),
  and a stray `name` on `Bin` is inert today (Step 1 only ever reads `name` for
  `PackageKind::Library`); (c) the JSON-Schema-autocomplete story from "Why JSON, not TOML"
  above already catches most typos at authoring time, in-editor, for free, before the file is
  even saved — a strictly better UX than a deserialize-time error. Not worth the complexity.
- Validate `name` (the `Lib` variant only) via a `deserialize_with` function so a bad name
  fails inside `parse_manifest` itself, with `parse_manifest`'s signature unchanged (a
  `deserialize_with` fn returns `Result<T, D::Error>`, and `serde::de::Error::custom(...)`
  produces a normal error in that same type). Package names must be valid snake_case
  identifiers, checked as two things: identifier shape, and not a reserved keyword.
  - **Identifier shape has no existing function to reuse** — `Lexer::consume_identifier`
    (`ast/mod.rs:707`) is inlined char-matching inside a private, non-`pub` `Lexer` struct,
    and its grammar (`[A-Za-z_][A-Za-z0-9_]*`) is looser than snake_case anyway (accepts
    uppercase). Write a small standalone predicate instead of trying to reuse it:
    ```rust
    fn is_valid_package_name(name: &str) -> bool {
        let mut chars = name.chars();
        let first_ok =
            matches!(chars.next(), Some(c) if c == '_' || c.is_ascii_lowercase());
        first_ok
            && chars.all(|c| c == '_' || c.is_ascii_lowercase() || c.is_ascii_digit())
            && ast::Keyword::try_from(name).is_err()
    }
    ```
    (empty string is naturally rejected — no leading char to satisfy `first_ok`.)
  - **The keyword check does have something real to reuse:** `ast::Keyword` and its
    `TryFrom<&str>` impl (`ast/mod.rs:1948`, `:1986`) are both `pub`. Worth checking: without
    it, a package named e.g. `loop` would load without error and then be permanently
    unreferenceable from any `.wx` file (`loop::Item` can't parse as a path — the parser sees
    the `loop` keyword token, not an identifier, at that position), a confusing silent dead
    end that this check closes off for nearly free.

**Validation:** unit tests alongside this code (or in `vfs/tests.rs`, which already exists)
covering: valid `lib`/`bin` manifests (nested `"package"` key, `dependencies` at the outer
level), missing `name` on `lib`, invalid `type` on `package`, an uppercase or hyphenated
`name`, a reserved-keyword `name` (e.g. `"loop"`), a `dependencies` entry with `type: "local"`
and a relative `path`, an unrecognized `type` on a dependency entry.

## Step 3 — general dependency resolution + implicit-`std` rule + duplicate-name diagnostic

**Files:** `crates/wx-compiler/src/vfs/mod.rs`

- New entry point, e.g. `pub fn open_package(path: &str, source: &impl FileSource) -> Result<CompilationUnit, ()>`,
  replacing the two-line `load_stdlib()+load_binary()` dance frontends currently hardcode:
  - No `wx.json` found for `path`'s containing directory → today's behavior exactly:
    anonymous `Binary`, `name: None`, `load_binary` on `path` directly.
  - `wx.json` found → parse it (step 2), load the root package as `<manifest_dir>/main.wx`
    with `name`/`kind` derived from `PackageManifestKind` (`Bin` → `PackageKind::Binary`,
    `name: None`; `Lib { name }` → `PackageKind::Library`, `name: Some(...)`).
  - Resolve each `dependencies` entry by its `DependencySource::Local { path }` (relative to
    the *depending* manifest's own directory, never the process's `cwd`), recursively,
    registering each package into a name → `PackageId` map (reuse `interner.get_or_intern`,
    same lookup pattern `use module::*` already uses for path segments). A name already
    claimed when something else tries to claim it is a new diagnostic — add
    `DuplicatePackageName` to the existing `DiagnosticCode` macro-generated enum in this file
    (follows the same `E2xxx` numbering as `ModuleFileNotFound`/`AmbiguousModuleFile` already
    there).
  - After all explicit resolution finishes: if nothing has claimed the name `std` yet, call
    `load_stdlib()` and register it. This one check implements the design doc's implicit-std
    rule in full — it naturally no-ops when the root package is itself named `std`, and is
    naturally overridden by an explicit `"std"` dependency entry, with no special-casing.
- This function does not yet get called from any frontend — that's step 4.

**Validation:** tests in `vfs/tests.rs` (pattern already established there) covering: a
plain binary with no manifest gets std exactly as today; a manifest'd binary with no deps
gets std; a root package named `std` does not get a second std loaded; an explicit
`"dependencies": {"std": {"type": "local", "path": ...}}` entry is used instead of the
embedded one; two packages both claiming the same name in one graph produces
`DuplicatePackageName`.

## Step 4 — wire the CLI, close the original bug

**Files:** `crates/wx-cli/src/main.rs`, new `crates/wx-compiler/std/wx.json`

- Replace `load_compilation`'s body with a call into step 3's `open_package`.
- When a manifest was used, print the resolved identity (name, kind, entry file) to stderr
  alongside existing diagnostic output, per the design doc's transparency requirement.
- `cmd_compile`: hard error if the resolved root package's `kind` is `Library`
  ("a library package has no WASM output, use `wx check`").
- Add `crates/wx-compiler/std/wx.json`:
  ```json
  { "package": { "type": "lib", "name": "std" } }
  ```
  No rename of the existing `main.wx` needed.

**Validation — this is the concrete milestone that closes the original bug:**
`cargo run -p wx-cli -- check crates/wx-compiler/std` should succeed cleanly with no
duplicate-candidate errors. Also re-run `cargo test -p wx-compiler` to confirm the existing
anonymous-file test suite is unaffected by the new resolution path.

## Step 5 — library-package restrictions (can be built in parallel with steps 2–4; only needs step 1)

**Files:** `crates/wx-compiler/src/tir/builder.rs`

- Build a `FileId → PackageKind` lookup at the top of `build()`, alongside the existing
  package × module walk that already builds `source_modules` — same traversal, one more map.
- Add four diagnostic codes to this file's `DiagnosticCode` enum (e.g.
  `ImportInLibraryPackage`, `ExportInLibraryPackage`, `MemoryInLibraryPackage`,
  `MutableGlobalInLibraryPackage`).
- Guard at the four confirmed sites (verified against current `HEAD`):
  - `ast::Item::Import` arm in `pre_scan_item`, line 5252 — bail before creating the import
    namespace.
  - The Phase 4 `ast::Item::Export` handling loop (not the no-op prescan arm at line 5394)
    — the package is already in hand there.
  - `ast::Item::Memory` arm in `pre_scan_item`, line 4957.
  - `ast::Item::Global` arm in `pre_scan_item`, line 4800 — only when `mut_span.is_some()`.

**Validation:** TIR tests in `tir/tests.rs` using `TestCase::new_multi_file` with one file
loaded as a `Library`-kind package (via `load_library` directly — doesn't need step 2/3's
manifest machinery at all, so this step is genuinely independent). Assert each of the four
constructs produces its diagnostic in a library and compiles clean in a binary. Also assert
`report_unused_items` still behaves correctly on a library root (it already skips
`pub_span.is_some()` items — confirm that continues to hold, don't just take it on faith).

## Step 6 — LSP integration

**Files:** `crates/wx-lsp/src/lib.rs`

- Extend manifest discovery: alongside the existing `discover_package_root`'s (step 0's
  renamed `discover_crate_root`) upward walk for `main.wx`, also walk upward for `wx.json`,
  calling step 2's `parse_manifest` — `wx-lsp` already depends on `wx-compiler`, so no new
  Cargo dependency is needed to reach it.
- When a manifest is found, route through step 3's `open_package` instead of `parse_root`'s
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
  incomplete standalone/replacement `std` package a reachable end-user path for the first
  time, rather than only an internal compiler-team invariant.

## Explicitly out of scope for this plan

Per the design doc: `wx std vendor`, transitive dependency resolution, and Rust-style dual
`main.wx`+`lib.wx` coexistence are backlogged/rejected — not part of this implementation.
Also out of scope, raised and deliberately deferred during planning: a `remote`/`registry`
`DependencySource` variant (would need fetch/cache/version-resolution machinery this plan
doesn't build, and transitive resolution besides — already out of scope above; `DependencySource`
is shaped as a tagged enum today specifically so this stays additive whenever it does happen),
package metadata (`description`/`version`/`repository`), and embedding formatter config in
`wx.json` (that's `wx-fmt`'s concern, not the compiler's package-loading path).
