# Package manifests (`wx.json`), the `AbsolutePath`/`RelativePath` rework, and `wx format`'s CLI design

## Summary

Implemented Steps 0–3 of `notes/implementation-plan.md` (itself implementing the design in
`notes/temp.md`): the `Crate*` → `Package*` rename, `PackageKind`, `PackageManifest`/`wx.json`
parsing, and general dependency resolution (implicit `std`, diamond dedup, cycle detection,
duplicate-name diagnostics) via a new `vfs::open_package`. Step 4 (wiring `wx-cli` to actually
call `open_package` instead of its hardcoded `load_stdlib()+load_binary()`, which is the
original motivating bug) was **explicitly deferred** by the user mid-session — see Open
questions.

While implementing this, the path-handling underneath the whole compiler turned out to be
ad-hoc string manipulation with no real invariants, which grew into a much bigger detour: a
full `AbsolutePath`/`RelativePath` type redesign threaded through every frontend. That in turn
surfaced a real regression in `wx-lsp` (fixed via a new `FileOrigin` concept) and a real
diagnostics-duplication bug (fixed by separating "linker" from "parse" diagnostics). The
session ended mid-design on `wx format`'s new CLI surface — several concrete shapes were
discussed but nothing is decided yet.

Everything below is implemented, tested, and **left uncommitted** in the working tree, per
explicit instruction ("don't commit, I'll review and commit myself").

## Changes

- **`crates/wx-compiler/src/vfs/path.rs`** (new) — `AbsolutePath`/`RelativePath` newtypes.
  Fully independent types, no shared "VirtualPath" wrapper (see Decisions). Only join
  operation is `AbsolutePath::join(&RelativePath) -> AbsolutePath`.
- **`crates/wx-compiler/src/vfs/manifest.rs`** (new) — `PackageManifest`/`PackageManifestKind`/
  `DependencySource`/`ResolvedDependency`, `is_valid_package_name`, own unit tests.
- **`crates/wx-compiler/src/vfs/resolve.rs`** (new) — `open_package`/`open_manifest_package`
  (dependency resolution, implicit-`std`, diamond/cycle handling via DFS), plus the new
  `package_kind` helper (see Decisions), own integration tests.
- **`crates/wx-compiler/src/vfs/mod.rs`** — `PackageKind::{Binary, Library{name}}` (name folded
  into the variant, no `Option`/`.expect()`), `FileOrigin{Local, Virtual}` + `FileSource::origin()`
  (no default impl — every source states it explicitly), `PackageGraph.linker_diagnostics`
  (renamed from `diagnostics`, see Decisions), `FileSource`/`VirtualFileSource`/`Files` all
  migrated to `AbsolutePath`.
- **`crates/wx-compiler/build.rs`** — `STDLIB_FILES` entries now `/`-prefixed at generation
  time, not patched afterward.
- **`crates/wx-cli/src/main.rs`** — `resolve_cli_path` (joins a CLI arg against `cwd` unless
  already absolute); `cmd_compile`/`cmd_check` updated for the diagnostics split (see below).
  `cmd_format` is **mid-rewrite, not finished** — see Open questions.
- **`crates/wx-lsp/src/lib.rs`** — `OverlayFileSource::origin() -> Local`; `file_id_to_uri`,
  `label_location`, `analysis_from_compiled_root` rewritten to dispatch on `FileOrigin` instead
  of the broken "starts with `/`" heuristic; `render_full_diagnostic`'s diagnostic-ordering walk
  updated to match the new linker/AST split so its indices still line up with what
  `analysis_from_compiled_root` published.
- **`crates/wx-compiler-wasm/src/lib.rs`** — same linker/AST diagnostics chain as the CLI.
- **`crates/wx-fmt/src/lib.rs`** — `RendererConfig` now derives `Clone, Copy` (needed once a
  single config value gets reused across multiple modules in whole-package formatting).
- All test harnesses (`ast/tests.rs`, `codegen/tests.rs`, `vfs/tests.rs`, `tir/tests.rs`,
  `wx-fmt/src/tests.rs`) updated for the `AbsolutePath`/`FileOrigin`/`linker_diagnostics` changes.
- 92 MIR snapshot files regenerated (`INSTA_UPDATE=always` + `cargo insta accept`) — purely the
  `Crate:` → `Package:` YAML tag from Step 0, verified as the only diff.

## Key findings

- **The `ast.diagnostics` → `PackageGraph.diagnostics` clone was real, load-bearing
  duplication.** `Loader::load_module` (`vfs/mod.rs`) copied every parse diagnostic into the
  package graph's own list — the *only* place that happened, confirmed by grep. Four separate
  consumers (`wx-cli`'s `cmd_compile`/`cmd_check`, `wx-lsp`'s `analysis_from_compiled_root`,
  `wx-compiler-wasm`'s `compile`) relied on that clone to see syntax errors at all. Removing it
  required an explicit loop over `module.ast.diagnostics` at each of the four call sites (user
  chose explicit inline chains over a shared convenience method — see Decisions) — a silent
  compile-time-invisible way to lose error reporting if any one of the four had been missed.
- **The `wx-lsp` "is this an absolute path" heuristic broke once stdlib paths also became
  `/`-prefixed.** `is_absolute_path`/`file_id_to_uri`/`label_location` all used to
  distinguish "real file" from "virtual stdlib" by checking for a leading `/` — this only
  worked because the embedded stdlib's paths used to be bare (`main.wx`, not `/main.wx`).
  Once the `AbsolutePath` migration made *everything* `/`-rooted by convention, this heuristic
  silently misclassified stdlib files as real ones. Caught via
  `resolve_uri_finds_virtual_stdlib_module`'s test assertion, but the actual fix (`FileOrigin`)
  needed a proper design pass, not just a patched assertion.
- **A stray, unregistered `wx.json` already exists at the repo root** (`git status` shows it
  `??`, i.e. untracked — not created this session). Its schema does **not** match what Step 2
  implemented: it has `"type"`/`meta.{name,description,version,repository}` at the top level
  (no nested `"package"` key) and an already-populated `"format": {max_line_width, indent_width,
  trailing_comma}` section. `notes/implementation-plan.md` explicitly lists package metadata and
  embedded formatter config as **out of scope** for this plan. This file looks like a forward-looking
  sketch of a *later* schema, not a bug — but it means a future session needs to explicitly
  reconcile "what `wx.json` looks like today" vs. "what this file already assumes it looks
  like." Left untouched; flagging so it isn't mistaken for stray test output.
- **Three pre-existing test failures, unrelated to this work**: `test_f32_sin_cos_agree_with_reference`,
  `test_f32_scale_pow2_wasmtime`, `test_f64_scale_pow2_wasmtime` (all in `codegen/tests.rs`) call
  `std::process::exit(1)` because `std/main.wx` doesn't actually define `sin`/`cos`/`scale_pow2`
  for `f32`/`f64` yet. Confirmed via `git diff` that my own edits to that file are just the
  `AbsolutePath` rename, and via `git log` that the test predates this session (commit `ff7b5f8`).
  Not fixed — out of scope, but worth knowing `cargo test -p wx-compiler` needs
  `--skip test_f32_sin_cos_agree_with_reference --skip test_f32_scale_pow2_wasmtime --skip test_f64_scale_pow2_wasmtime`
  until someone implements those stdlib methods (the test binary calls `process::exit(1)`
  directly on a diagnostic-carrying `TestCase`, which aborts the whole run rather than just
  failing that one test — so an unrelated failure here currently masks every test after it
  alphabetically/by-thread-schedule).

## Decisions

- **`AbsolutePath`/`RelativePath` as fully independent types, not one enum with a runtime tag.**
  Rejected an intermediate design where `VirtualPath` was the enum and `AbsolutePath`/
  `RelativePath` wrapped it ("that's backwards — I don't want to pay runtime overhead for this").
  Landed on: each is its own newtype; only `AbsolutePath` has `.join(&RelativePath)`/`.parent()`
  (joining two relatives, or two absolutes, was judged meaningless/wrong, respectively).
- **No `Deref<Target=str>` or `impl Into<AbsolutePath>` anywhere** — explicit `.as_str()` calls
  and concrete (non-generic) parameter types throughout, both by explicit request.
- **Dependency map key becomes the registered package's actual name**, not whatever its own
  `wx.json` declares — this single mechanism is what makes the implicit-`std`-override rule work
  by key alone, with no special-casing.
- **DFS + memoization for diamond/cycle detection**, not a topological sort — justified because
  TIR's own phased resolution (namespace creation → prescan → demand-driven signature
  resolution) doesn't depend on package load order at all.
- **`FileOrigin` has no default trait-method body.** Every `FileSource` impl must state its
  origin explicitly (`NativeFileSource`/`OverlayFileSource` → `Local`, `VirtualFileSource` →
  `Virtual`) — rejected a `fn origin(&self) -> FileOrigin { Local }` default specifically so a
  future `FileSource` can't silently inherit the wrong one.
- **`PackageGraph.diagnostics` renamed to `linker_diagnostics`**, not left generically named
  with a doc comment explaining the narrower scope — the field's own name should say what it
  holds. Considered `loader_diagnostics` (named after the private `Loader` type that produces
  them) but rejected in favor of `linker_diagnostics`, since the file's own pre-existing
  `DiagnosticCode` doc comment already frames this stage as "closer to a linker than a parser or
  type checker" — naming by what kind of diagnostic it is, not by which internal struct emits it.
- **The four diagnostics consumers use explicit inline `.chain(...)` at each call site**, not a
  shared `PackageGraph::diagnostics()` convenience iterator. I proposed the shared method
  (borrowing only, no clone) as the lower-boilerplate option; user picked inline explicitly
  ("inline over helpers" — consistent with `artem-code-review-style` memory).
- **`cmd_format` will not call `open_package` for whole-package formatting.** `open_package`
  resolves the *full* dependency graph, which formatting never needs (it only ever touches its
  own package's files) — reusing it wholesale would mean parsing every dependency just to throw
  that work away. Also explicitly rejected: a `follow_dependencies: bool` flag threaded through
  `open_package` itself to switch this off.
- **Directory-vs-file argument type-sniffing for `cmd_format` was rejected mid-design** in favor
  of an explicit `--manifest <path>` flag (see Open questions for the exact shape, still
  undecided) — the user specifically didn't want `wx format <dir>` to implicitly mean "look for
  `wx.json` here."
- **Extracted `vfs::package_kind`** (`PackageManifestKind` → runtime `PackageKind`, with an
  optional dependency-key name override) as a small, genuinely-reused helper — it now backs both
  `open_manifest_package`'s existing dependency-recursion step (pure extraction, zero behavior
  change, still requires each dependency to have its own manifest) and will back whole-package
  formatting once that lands. A fuller `resolve_package`/`ResolvedPackage` abstraction (bundling
  entry-path resolution + the raw manifest) was drafted and then **removed** once the CLI design
  pivoted away from directory-sniffing — it had no real caller left, so it was dead exported API,
  not "reuse for reuse's sake."
- **Formatting config discovery should be decoupled from which files get reformatted** (a
  question the user raised citing rustfmt/prettier/deno precedent): rustfmt and Prettier both
  resolve config *per file*, walking up from that file's own directory to the nearest
  `rustfmt.toml`/`.prettierrc`, entirely independent of whether you ran the tool on one file or
  a whole project — that's what makes Prettier's per-subtree monorepo configs work. deno fmt
  instead resolves one `deno.json` per invocation from cwd/`--config`, simpler but less
  flexible. Conclusion: don't hardcode "directory mode has config, single-file mode doesn't" —
  once `wx.json` gets a `format` section, config resolution should be its own concern, not
  coupled to file-selection. Not implemented yet (no `format` section in `PackageManifest`
  today) — just kept the door open.

## Context for future sessions

- `resolve_cli_path` (`wx-cli/src/main.rs`) is the one place a raw CLI string becomes an
  `AbsolutePath` — joins against `std::env::current_dir()` unless already `/`-prefixed. Known
  gap, not fixed: doesn't handle a Windows drive-letter absolute path (`C:\...`).
- The "synthetic root" convention: any `VirtualFileSource`-backed compilation (tests, wasm, LSP
  virtual buffers) treats `/` as its own synthetic root by convention only — every entry point
  into such a compilation must already be `/`-prefixed by whoever constructs it. `wasm`'s JS
  callers are responsible for this themselves now (no prepending happens in Rust).
- `crates/wx-compiler/std/wx.json` (which Step 4 of the plan calls for) does **not exist yet** —
  Step 4 wasn't started this session.
- Full validation before pausing: `cargo build --workspace` clean; `cargo test -p wx-compiler`
  818/818 (with the 3 pre-existing unrelated failures filtered — see Key findings); `cargo test
  -p wx-lsp` 53/53. Manually verified via the real `wx` binary that a genuine syntax error still
  aborts `wx check`/`wx compile` correctly after the diagnostics-separation refactor.

## Open questions

1. **`wx format`'s final CLI shape — not decided.** Three concrete options were on the table
   when the session paused:
   - **(A)** rustfmt-style: `wx format` only ever takes explicit `.wx` file arguments, full
     stop; no built-in "whole project" mode at all (mirrors that `rustfmt` itself never takes a
     directory — `cargo fmt` is a separate wrapper that expands a crate to a file list first).
     `--manifest <path>` only ever supplies config for the named files.
   - **(B)** `--manifest <path>` alone (no file args) means "format this whole package";
     `--manifest` *with* file args means "just these files, but sourced config from this
     manifest." (This is what was partway through being implemented when the user asked to stop
     and reconsider — overloads what `--manifest` means depending on whether files are also
     given.)
   - **(C)** an explicit `--all` flag, orthogonal to `--manifest`, so "whole package" is never
     inferred from "you didn't pass files": `--manifest wx.json --all` = whole package;
     `--manifest wx.json a.wx` = just `a.wx`, using that manifest's config.
   User's last words on this: "let's plan it tomorrow" — needs a fresh decision next session,
   not an assumption.
2. **`wx.json`'s eventual `format`/`meta` sections** — the stray root `wx.json` (see Key
   findings) already sketches a shape for these (`meta.{description,version,repository}`,
   `format.{max_line_width,indent_width,trailing_comma}`), but `notes/implementation-plan.md`
   explicitly scoped both out of the current plan. Worth explicitly deciding whether that stray
   file is the intended next-step schema or just a scratch example, and whether/how it should
   reconcile with the current nested-under-`"package"` shape.
3. **Step 4 (wiring `cmd_compile`/`cmd_check` to `open_package`, the plan's original motivating
   bug) was explicitly deferred** by the user this session ("No, keep this focused on
   cmd_format") — still open, not forgotten. `load_compilation` in `wx-cli/src/main.rs` still
   hardcodes `load_stdlib()+load_binary()`.
4. **Per-file, walk-up-based format-config discovery** (the rustfmt/Prettier model discussed
   under Decisions) is not implemented — there's no `format` section in `PackageManifest` yet
   to discover in the first place. Worth revisiting once (2) is resolved.
