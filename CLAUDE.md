# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

WX is a Rust-implemented compiler for a language that targets WebAssembly. Syntax is Rust-inspired. This is a bachelor's thesis project.

## Current state: TIR rewrite in progress (branch `tir-refactor`)

The type checker is being rewritten. Only the front half is live:

- **Compiled and tested:** `ast`, `vfs`, `diagnostics`, and `tir` phases 1–2 (`defs.rs`, `imports.rs`, `paths.rs`, `impls.rs`, `signatures.rs` and their support modules, see "TIR" below). The embedded stdlib sweeps with zero diagnostics.
- **Commented out** in `lib.rs`: `mir`, `opt`, `codegen`, `wasm`. In `tir/mod.rs`: the `TIR` struct, `TIR::build`, `mod builder` (the old body checker, ~22k lines under `tir/builder/`, kept only as the reference to port from) and `mod tests` (`tir/tests.rs` and `tir/snapshots/` are the old suite and are not compiled).
- **Not compiling:** `wx-fmt`, `wx-lsp`, `wx-cli` (and so `wx` itself) reference things that no longer exist. This is expected mid-refactor state; don't "fix" it as a side effect of unrelated work.
- **Not started:** function bodies (`BodyContext` in `typecheck.rs` checks constant initializers so far), impl conformance, wiring a new `TIR::build`.

Design and rationale: `notes/tir-type-context.md`. Everything below that mentions `tir/builder/`, the `TIR` struct, `TIR::build`, MIR/opt/codegen, or the CLI describes the **previous, still-reference-worthy design**, not what currently builds.

## Commands

```bash
# Build
cargo build -p wx-compiler       # core library
cargo build --release -p wx-cli  # CLI binary → target/release/wx

# Run the compiler on a project (every subcommand takes a *directory*
# containing a wx.json, never a bare .wx file)
wx build .                       # → <dir-name>.wasm; `-o -` writes to stdout
wx check .                       # type-check only, no output emitted
wx format .                      # in-place; --check for a diff-free exit code,
                                 # --files a.wx,b.wx to restrict the set
wx lsp                           # language server over stdio

# `build`/`check` accept --message-format human|short|json

# Inspect WASM output (WABT is installed)
wasm2wat output.wasm             # disassemble to WAT text format
wasm-objdump -d output.wasm      # annotated disassembly

# Test — most tests live in wx-compiler, but wx-fmt and wx-lsp have their own
cargo test --workspace
cargo test -p wx-compiler -- <test_name>  # single test by name

# Update snapshots when output changes legitimately
cargo test -p wx-compiler
cargo insta accept

# Lint (this exact form is what CI gates on)
cargo clippy --workspace --no-deps -- -D warnings

# Format Rust sources
cargo fmt
```

Current baseline (mid-refactor, see below): 673 `wx-compiler` tests pass; `wx-fmt`/`wx-lsp`/`wx-cli` do not compile and clippy is not clean (hundreds of dead-code warnings from the disabled stages). The earlier 1023 + 43 + 63 baseline predates the TIR rewrite.

## Crates & binaries

`wx` is a single native binary (from `wx-cli`) with `build`/`check`/`format` (alias `fmt`)/`lsp` subcommands — there is no separate `wx-lsp` binary anymore. `wx-lsp` is a library-only crate (no `main.rs`): it exposes `build_service()` (builds the `tower-lsp-server` `LspService`) and `run_stdio(stdin, stdout)` (serves it over a caller-supplied transport). `wx-cli`'s `lsp` subcommand (`cmd_lsp` in `wx-cli/src/main.rs`) is the only place that spins up a Tokio runtime — a current-thread one, scoped to just that subcommand, since everything else in the CLI is synchronous.

`run_stdio` is `#[cfg(not(target_arch = "wasm32"))]`: `tower_lsp_server::Server`'s `AsyncRead`/`AsyncWrite` bounds resolve to a different trait depending on which of its features is active (`tokio::io`'s under `runtime-tokio`, native; `futures::io`'s under `runtime-agnostic`, wasm32), so it can only compile for the target whose trait it's bounded by. `wx-lsp-wasm` (excluded from the main workspace — wasm32-only) only ever calls `build_service()` directly and bridges the transport over `postMessage` instead.

The two wasm crates (`wx-compiler-wasm`, `wx-lsp-wasm`) are built with `wasm-pack` **run from inside the crate directory** — `wx-lsp-wasm/.cargo/config.toml` pins `target = "wasm32-unknown-unknown"`, and Cargo's config discovery only picks that up when invoked from within that directory. Each produces a `pkg/` that `web-next/package.json` consumes as a `file:` dependency. There is no committed task or npm script wrapping this, and `pkg/` is not checked in.

Two web frontends are tracked: `web/` (the deployed playground — `.github/workflows/deploy.yml` builds it with Deno and pushes to Deno Deploy; depends on the published `@wx-lang/wasm-bindings`) and `web-next/` (its in-progress Monaco/LSP-backed replacement, wired to the local `wasm-pack` output above).

Distribution: `wx` (all subcommands, including `lsp`) ships via GitHub Releases and npm (`@wx-lang/cli`, per-platform optional deps) — see `.github/workflows/publish-cli.yml`. Release binaries are stripped (`[profile.release] strip = true` in the root `Cargo.toml` — cheap enough, no build-time cost, to apply everywhere including a plain local `cargo install`); `lto`/`codegen-units = 1` are enabled only in `publish-cli.yml`'s build step via env vars, not in `Cargo.toml`, since they meaningfully slow down builds and should only cost time on binaries actually being shipped.

CI (`.github/workflows/ci.yml`) runs only `cargo check`/`test`/`clippy` over the workspace. It does **not** build or check anything under `examples/`, so a broken example will not fail CI.

`thesis/` is gitignored — the bachelor's thesis lives in its own repo ([MellKam/bachelor-thesis](https://github.com/MellKam/bachelor-thesis)) and is merely cloned into this working directory for convenience. Its `thesis/CLAUDE.md` belongs to that repo, not this one.

## Editor integrations

`editors/` holds one git submodule per supported editor, each a fully self-contained repo under the `wxlanguage` org (own `package.json`/lockfile, own `.github/workflows/`, own `.vscode/` debug config) — nothing about them lives in the main repo beyond the submodule pointer and `.gitmodules`. `editors/vscode` ([wxlanguage/vscode](https://github.com/wxlanguage/vscode)) is functional; it doesn't bundle a `wx` binary, it resolves `wx` from the user's `PATH` (or an explicit `wx.path` setting) and spawns `wx lsp`, the same model as `deno.path`. `editors/zed` ([wxlanguage/zed](https://github.com/wxlanguage/zed)) is an MVP: a self-referential tree-sitter grammar (`[grammars.wx]` in `extension.toml` points `repository`/`rev` at this same repo, with the grammar source under `grammar/` via the `path` field — a real but undocumented `GrammarManifestEntry.path` field, confirmed from Zed's source rather than its docs) that gives real structure to top-level items but parses signatures/bodies as generic balanced-token groups rather than a full expression grammar; verified against every `.wx` file in this repo with zero parse errors. `src/lib.rs` resolves `wx` the same way as the VS Code extension (`Worktree::which("wx")`), with Zed's native `lsp.wx.binary.path`/`arguments` settings as an override — no custom setting needed. Not yet published to Zed's extension registry; install as a dev extension for local testing. Zed's own extension registry (a submodule tree itself) requires each listed extension to live in its own repo, which is why this follows the same one-repo-per-editor structure as `vscode` rather than living directly under `editors/`. Clone with `git clone --recurse-submodules`, or run `git submodule update --init` after a plain clone — a submodule directory is empty until explicitly initialized. To debug an editor integration, open its `editors/<name>` folder directly as its own VS Code window rather than from the `wx` root, since its `.vscode/launch.json` only applies there.

**Neither extension registers file watchers.** The server declares its own at `initialized` over `client/registerCapability` (`**/*.wx`, `**/wx.json`) and receives `workspace/didChangeWatchedFiles`; `didSave` is not used. Doing it server-side is what lets Zed — whose extensions can only supply a server command, with no file-watching API of their own — see manifest and off-buffer source edits at all. Don't reintroduce a per-editor watcher.

## Releasing

The compiler, CLI, and LSP are versioned in lockstep (see `CHANGELOG.md`'s preamble) rather than per-crate. For the full release process (version bump rules, changelog conventions, branch protection, tagging, and publish-workflow gotchas), use the `release-wx` skill.

## Project model — `wx.json`

Every compilation is rooted at a **package**, and every package needs a `wx.json` next to its sources. There is no anonymous single-file compilation path: `wx build`/`check`/`format` all take a directory, and `wx-lsp` finds a file's package by walking ancestors for a `wx.json` (a file with no such ancestor gets a rust-analyzer-style "unlinked file" hint rather than silent nothing).

```jsonc
{
  "type": "bin",             // "bin" | "lib" | "std"
  "entry": "main.wx",        // required, relative to this manifest — never guessed
  "dependencies": {
    "math": { "type": "local", "path": "../math" }
  },
  "format": {                // all optional; each falls back to RendererConfig::default
    "max_line_width": 80,
    "indent_width": 4,
    "trailing_comma": true
  }
}
```

Parsed by `vfs::manifest::PackageManifest`, resolved into `PackageGraph`s by `vfs::resolve::open_manifest`. Unknown top-level keys are ignored, so a manifest written for a newer wx still loads on an older one.

- **A package has no name of its own, and a `dependencies` key does not put one in scope.** The key only makes the package *available* to the declaring package (`Package.dependencies`, keyed by `PackageName`). Source names it with a package instance, `crate "key" as alias;` (see "Language features"), so the same package can be instantiated under several aliases, in any module. The stdlib is registered first in every package's `dependencies` as `std` (it is not reserved, just claimed first), so a manifest key `std` is a duplicate name (E0002); a `"type": "std"` dependency is E0004.
- **`"type": "std"`** means *this package provides the stdlib itself* (it defines the `#[tag = "..."]` items the language requires), so the embedded stdlib is not also loaded. It is not a freestanding mode — wx has none. Only `crates/wx-compiler/std/wx.json` uses it.
- `DependencySource` is `#[serde(tag = "type")]` from the start, so a future remote/registry source is an additive variant rather than a breaking reshape. Only `local` exists today, and its `path` is a `RelativePath` — always relative to the declaring manifest, never the process cwd, enforced as a type invariant.
- Formatting config is read from the manifest in exactly one place, `RendererConfig::from_manifest` in `wx-fmt`. `wx format` and the LSP's formatting request are the same operation and must agree byte for byte — don't add a second overlay. (Note: a doc comment on `cmd_format`'s config helper still describes a `--manifest <path>` flag that does not exist in the clap definition.)

## Compilation pipeline

```
wx.json + source text
    │  vfs::resolve::open_manifest() → package graph
    │  ast::Parser::parse() per file
    ▼
AST  (src/ast/)
    │  vfs::CompilationUnitBuilder — load_stdlib()/load_package()/load_binary()/build()
    │      → CompilationUnit
    │  tir::TIR::build(&mut compilation)
    ▼
TIR  (src/tir/) — type-checked, name-resolved IR
    │  MIR::build(&tir, &interner, compilation.id_generator)
    ▼
MIR  (src/mir/) — desugared, monomorphized, inlined IR
    │  opt::builder::Builder::build(&mir, func_mir) per function
    ▼
Opt  (src/opt/) — sea-of-nodes SSA per function
    │  opt::scheduler::Scheduler::schedule(&func, &mir) → wasm::Function
    ▼
codegen::Builder::build(&mir, &interner) → Result<WasmModule, ()>
    ▼
WASM bytecode (WasmModule::encode() → Vec<u8>)
```

Currently only the AST/vfs stages and TIR phases 1–2 are wired; `TIR::build` and everything after it are disabled (see "Current state").

`CompilationUnit` owns diagnostic gathering for the whole package graph — `collect_parser_diagnostics()`, `collect_linker_diagnostics()`, and `collect_diagnostics()` (both, interleaved per package). Don't walk `packages`/`modules` by hand to print or count diagnostics; and use the `Diagnostics` extension trait (`errors`/`error_count`/`has_errors`) rather than spelling out `Severity::Error | Severity::Bug`, since dropping `Bug` from any one such check is a silent hole.

The stdlib is embedded at build time by `crates/wx-compiler/build.rs`, which walks `std/**/*.wx` into `STDLIB_FILES: &[(&str, &str)]` (`/`-prefixed path relative to `std/`, source). `StdlibFileSource` serves it to the loader by reading that table directly. Adding a stdlib file means creating it and writing the `mod` declaration that references it — there is no third list to update. `std/main.wx` defines the fifteen operator traits, the `Memory` trait, `mod wasm` intrinsics, `impl` blocks for the primitives, and stdlib constants.

## Key modules (`crates/wx-compiler/src/`)

- **`ast/`** — lexer + parser → AST nodes
- **`tir/`** (live) — `defs.rs` (phase 1 prescan → `DefinitionRegistry`), `imports.rs` (`use`/glob resolution), `paths.rs` (shared path walking), `impls.rs` (`ImplDispatch`), `types.rs` (`TypeInterner`, `TypeEnvArena`), `signatures.rs` (`TypeContext`, `ensure_signature`, `sweep`), plus `bounds.rs`, `obligations.rs` (`Obligation`, `ObligationChecker`, `report_solver_error`), `solver.rs`, `satisfaction.rs`, `members.rs`, `literals.rs`, `format.rs`; bodies: `body.rs` (`Body` arena), `typecheck.rs` (`BodyContext`), `operators.rs`, `eval.rs`
- **`tir/builder/`** (disabled) — the old prescan + body checker; port source for body checking
- **`tir/mod.rs`** — module wiring; most of its remaining text is the commented-out old data model
- **`mir/mod.rs`** — desugaring (struct access → `AggregateGet`, `char` → `U32`), monomorphization, lowering
- **`mir/inlining.rs`** — `run_inlining_pass` (inlining + DCE) and the `Rebaser`
- **`opt/`** — sea-of-nodes SSA IR for per-function optimization (CSE via `Builder::node`, which delegates to `intern_node`; `liveness.rs`, `scheduler.rs`, and `local_dominance.rs` — a debug-only, deletable verifier for the definite-assignment invariant `coalesce_locals` depends on)
- **`wasm/`** — the shared wasm stack-machine representation (`Instruction`, `Function`, `Local`, `ScalarType`, `BlockType`). `opt::scheduler` **produces** it from the sea-of-nodes graph; `codegen` **consumes** it for encoding. It exists because those two used to hold near-identical private copies of the same shape.
- **`codegen/mod.rs`** — WASM bytecode emitter; `Builder::build` is the entry point
- **`vfs/`** — `mod.rs` (`CompilationUnit`, `PackageGraph`, `Files`, file sources), `manifest.rs` (`wx.json` schema), `resolve.rs` (manifest → package graph), `path.rs` (`AbsolutePath`/`RelativePath`)
- **`testing/`** — `#[cfg(test)]`-only shared test vocabulary; `DiagnosticView` (see Testing patterns)
- **`diagnostics.rs`** — the single `define_diagnostic_codes!` macro and the `Code` trait, shared by every stage
- **`../std/main.wx`** — standard library source (sibling to `src/`), embedded via `build.rs`

The pretty-printer used to live at `fmt/` in this crate; it's now its own crate, `wx-fmt` (`crates/wx-fmt/src/lib.rs`), used by both `wx-cli` (the `format` subcommand) and `wx-lsp` (the LSP formatting request).

## TIR (rewrite)

**Phase 1 — `DefinitionRegistry::build`** (`defs.rs`, with `imports.rs`/`paths.rs`): seeds one root scope per package (`crate`/`self` are real bindings, and `std` is bound in every package but the stdlib's own; other dependencies are bound by package instances as they are scanned), creates one scope per file, prescans every item into `ast_nodes: Vec<AstEntry>` (parse order) and per-kind arenas with stable indices (`FunctionIdx`, `StructIdx`, …), and resolves `use` imports and globs on demand. Output is read-only afterwards. `ImplDispatch::build` then indexes impl targets. Namespaces are addressed by their owner: a `Namespace` (`Package`/`Module`/`Enum`/`Import`) is what a path continues into, a `Scope` (`Package`/`Module`) is where code is written (an unqualified lookup's start, a privacy check's accessor, every item's `namespace`). Their tables live in `defs.namespaces: Namespaces`, one list per owner kind indexed by the owner's own index. Only a scope has a parent, globs and `self`/`crate`/`super`; an enum's or import block's table holds just its names, and an imported declaration's scope is the one around its block.

**Name resolutions** (`resolutions.rs`): every written name the compiler resolves is recorded in one `NameResolutions` table, keyed by `(SourceSpan, Tier)` and mapping to a `Referent` (`Definition`, `Import { definition, import }` for a name made visible by a named `use` or a glob, `TypeParam`, `Member`). The caller owns it next to `diagnostics` and lends it `&mut` to `DefinitionRegistry::build`, `ImplDispatch::build` and `TypeContext`; `PathResolver` holds it with the other things a walk writes. Only code that has committed to a meaning records it (the walk records each segment it resolves; `resolve_type_path` records a parameter once it chose it over the namespace walk; member selection records the member it picked). There are no per-definition `accesses` lists: who refers to a definition, or which `use` items are unused, is the inverse of this table.

**Phase 2 — `TypeContext`** (`signatures.rs`): the single owner of semantic type state (interner, bounds, scope frames, per-kind signature tables, query/obligation/normalization state). It *borrows* `defs`, strings, `ast_nodes`, `ImplDispatch` and the diagnostics sink; the caller owns those and creates the context inside that scope. `sweep()` forces `ensure_signature(DefId)` for every declaration, checks every declaration (`check_declarations`), then the body phase (`check_bodies`), resolves the export block, and debug-asserts everything is `Resolved`. Obligations are only requirements a signature recorded and could not decide during construction; what is written *inside* a declaration (a constant's initializer, an enum's discriminants, later function bodies) is a body, checked by `check_bodies` through a per-body `BodyContext` (`typecheck.rs`) after every check has run. A body records what its own lowering requires (a written type, a construction's bounds) in its own list and checks it on the spot (`TypeContext::check_now`), since every fact is final by then; nothing is kept for later. The context is **not frozen** afterwards: it stays live and mutable. Do not reintroduce a frozen `SignatureRegistry`, and don't reach for `Arc`/`Rc`/`unsafe` to make owner and borrower coexist; keep inputs on the caller's stack.

A declaration's identity is `defs::DefId`, the arena it lives in and its index there (`DefId::Struct(StructIdx)`, …; an enum variant is a `Const`). The prescan assigns it; the parser assigns none, so the AST is plain syntax. A trait a typeset generates is built by the typeset's query (`TraitDef::typeset`), and `DefinitionRegistry::name` reads any declaration's written name. `ensure_signature` is demand-driven and re-entrant. `query_state: HashMap<DefId, QueryEntry>` holds a `QueryState` (`Pending`, `InProgress`, `Resolved`, `CycleReported`); `query_stack` records in-progress frames in call order so a cycle diagnostic can name the whole loop. It returns `SignatureStatus { Available, CycleReported, Cycle }`, which is `#[must_use]`: handle `Cycle`, or write `let _ = …` with a reason. Once a frame is pushed, every path must reach the unwind that pops it; a leaked `InProgress` entry makes later cycles name items that finished long ago. Construction lowers written syntax and neither checks a bound nor normalizes: sites record an `Obligation` (bounds, trait membership, and well-formedness, which normalizes each written type once) in the list the lowering's caller passes (`obligations: &mut Vec<Obligation>`). `ensure_signature` owns one per query and keeps it with the declaration (`QueryEntry::obligations`); once every signature exists, `check_declarations` checks each declaration's obligations in place, in definition order. There is no global obligation list. A check never rewrites a stored signature; a failure is diagnosed and the type is kept as written, with projections unreduced. Unqualified `Type::Name` selection uses declared bounds, the `ImplDispatch` index and assumptions only; a member of a projection that those cannot find records `CheckProjectionMember`, and the declaration's check reports the ambiguity with the qualified spelling as the suggestion (E2104). Semantic queries (`normalize_*`, `find_trait_impl_query`) are pure: they read finished signatures, never force one, and never emit. They live on `Solver` (`solver.rs`) and take a `SolverView` that `TypeContext::solver_and_view()` lends: the interner plus the read-only tables the engine needs, so it can neither report nor construct; `TypeContext` keeps thin wrappers for the rest of `tir`. The solver's one error type is `SolverError` (`Pending`, `Poisoned`, `Overflow`, `Cycle`); a query that cannot finish (budget or cycle) returns it, and the construct that owns the requirement reports it once via `report_solver_error`. Lowering failures still become `TypeIndex::ERROR` in place. Two kinds of `solver::Definition` are on the solver's own path and own their loops: an impl member's value for an associated type (`Definition::Member`: its own, or the trait default it inherits, keyed by `ImplMember { impl_index, declaration }`), and an impl's requirements, the bounds on its parameters (`Definition::Requirements(ImplKind)`), proved for its own parameters in its own scope. The solver judges each once on first use and memoizes a `Verdict` in `Solver::verdicts` (`Unchecked`/`InProgress`/`Resolved`, or `Poisoned`/`Overflowed`/`Cyclic` when it has no meaning); impl selection consults the impl's verdict before proving its requirements for the arguments at hand. A judgement is a frame on the solver's own stack (`SolverState::frames`, the counterpart of `query_stack`: `SolverFrame::Judgement` for a member, `SolverFrame::Requirements` for an impl), with a budget counted from where it started. Reaching a definition again while it is judged is a loop (for requirements: selecting the impl's own instantiation again; other arguments are ordinary recursion): through an equality written in a bound (`SolverFrame::Equality`) it is a tautology and stays abstract; through definitions only it is a cycle owned by its first-defined definition (an impl's requirements before its members), whose check reports it (`CheckAssocValue`; `CheckImplRequirements`, at the bound the loop closed in), and every other reader of a failed verdict fails silently. Other declarations' bounds are proved only where they are used, so they are not definitions here. So a loop through any number of values is one diagnostic regardless of source order, and checks need no ordering among themselves. A successful normalization is memoized when its answer read no open frame below its own request (`SolverState::lowest_frame_read`: a cycle, a re-entered judgement or a rollback each record the frame they read); only a request with no frame open reads that cache. A request for a type with no parameter is keyed and computed under the root scope (`Normalization::new`): only an abstract type (`TypeInterner::is_abstract`: a parameter, or a projection out of one) takes assumptions, so such a type means the same in every scope. A projection out of a concrete type (`<P as Container>::Item`) is not abstract: it reads its trait's declarations (`is_param_or_projection`) but never the scope's assumptions. Any path that reads a non-final fact must return `Pending`, which is what keeps the cache valid. Design and open points: `notes/tir-check-pass.md`.

Semantic queries (`find_trait_impl_query`, `normalize_*`, `resolve_type_member`, `resolve_trait_qualified_member`) are methods on `TypeContext`; declaration-local assumptions are read through `ClauseTables` from an `assumption_context: TypeEnvIdx`. What a parameter or an associated declaration assumes is a flat run of clauses (`bounds::BoundClauses`, ranges into the `ClauseArena`): `TraitClause` (`subject: Trait`, nested bounds as clauses on projections) and `EqualityClause` (`projection == value`), with each trait's own clauses (its supertraits) copied in with `Self` substituted. Trait clauses are published before any equality value is resolved (`equalities: None` until then), so a sibling's value can name members they supply. An associated declaration's clauses are not expanded into a parameter's; they are read along a receiver's projection path (`declarations_of`), since a recursive trait describes infinitely many paths. A use proves a parameter's clauses with the use's arguments (`Solver::satisfies_clauses`). Ambiguity between equalities is decided where they are read; a conflict between values an outer constructor tells apart is reported once, when the clauses are built. `ValueType` (std) has no impls: the solver answers it from the receiver's structure (`Solver::value_layout`, the Wasm values a type occupies), and it holds for exactly one value; a parameter counts as one value when it is assumed `ValueType` (`TraitImplLookup::Builtin`). Trait-impl conformance is **not** implemented.

**Old body checker (`tir/builder/`, disabled):** feature-sliced (`operators`, `calls`, `control`, `paths`, `traits`, …), each slice owning its `report_*` diagnostics; `type_compare.rs` did trait-conformance signature comparison. When porting a slice, move it onto `BodyContext` rather than recreating a second declaration-query system.

## Type system

Every type is a `TypeIndex` (u32) into `tir.types` (a `TypeInterner`). The first 18 slots are pre-interned by the hardcoded `vec![Type::Infer, Type::Error, ..., Type::Char]` literal in **`TypeInterner::new()` (`tir/types.rs`)** — the reverse `index_lookup` is built by iterating over it — and MUST match the `TypeIndex` constants declared in the same file. Never reorder them; add new pre-interned types at the end only.

| Constant  | Index |
| --------- | ----- |
| `INFER`   | 0     |
| `ERROR`   | 1     |
| `UNIT`    | 2     |
| `NEVER`   | 3     |
| `INTEGER` | 4     |
| `FLOAT`   | 5     |
| `U8`      | 6     |
| `I8`      | 7     |
| `U16`     | 8     |
| `I16`     | 9     |
| `U32`     | 10    |
| `I32`     | 11    |
| `U64`     | 12    |
| `I64`     | 13    |
| `F32`     | 14    |
| `F64`     | 15    |
| `BOOL`    | 16    |
| `CHAR`    | 17    |

Each interned type carries `TypeFlags` (`HAS_INFER`, `HAS_ERROR`, `HAS_UNTYPED`, `HAS_PARAM`, `HAS_PROJECTION`), computed once in `TypeInterner::insert` from its own kind and its parts' flags, as rustc does: `has_infer`/`has_error`/`has_untyped`/`has_param`/`has_projection` answer "anywhere inside" without walking the type. `substitute` returns a type without `HAS_PARAM` unchanged and `Solver::normalize` one without `HAS_PROJECTION`, so a flag must never be missing where its variant occurs. Only `AssocTypeProjection` is a projection: a trait's function type (`<Point as Make>::make`, the declaration over `Self`) is nominal and never normalized into the impl's member; the impl is chosen where the call is resolved. A new compound `Type` variant must say in `flags_of` which parts it inherits from.

`INFER` (slot 0) is a type inference placeholder — used internally when a generic type argument cannot yet be determined, and will be the type of user-written `_` in type annotations. Must never reach MIR or codegen.

`UNIT` (slot 2) is the empty tuple, `Type::Tuple { elements: [] }`, not a variant of its own, so interning an empty tuple anywhere returns it. `NEVER` (slot 3) is written `!` (`TypeExpression::Never`), as in Rust; it is not a std item.

`char` is a primitive in TIR but lowers to `U32` in MIR and WASM.

## Language features (current state from tests)

- Primitives: `i32`, `i64`, `u32`, `u64`, `f32`, `f64`, `bool`, `char`, `u8`, `i8`, `u16`, `i16`. They are **real items** — `#[intrinsic] pub type X;` declarations in `std/main.wx`, bound by `ensure_signature` to the matching pre-interned `TypeIndex` — not a hardcoded string match, so they carry `DefId`s and LSP go-to-definition/hover/find-references work on them.
- Pointers, slices and arrays always carry an ownership sigil — `*T`/`&T`, `*[T]`/`&[T]`, `*[T; N]`/`&[T; N]` (`*` exclusive, `&` shared); there is no bare `[]T` and no `*mut T`. `.&` yields a shared reference (there is no `.&mut`). Each also belongs to a memory, resolved from the ambient one unless tagged explicitly (`heap::&[u8]`), and the type formatter always prints that memory prefix — so a slice surfaces in diagnostics as `heap::&[u8]`, never `&[u8]`
- String literals have type `&[u8]` (a shared byte slice); there is no separate `string` type
- `local` / `local mut` declarations; `global` / `global mut` for module-level state. A global's value type must be one Wasm value (`Global::Value: ValueType`): `u32`, `Meters(u32)`, a pointer or `func(A) -> R` are, `()`, a slice or `Pair(u32, u32)` are not
- **`local <pattern> = expr` destructuring** — tuples, struct patterns written exactly like construction (`Point(a, b)`, `Point({ x, y: py, .. })`, with a full path), `_` (a drop, binds nothing), arbitrary nesting, and `..` to opt out of exhaustiveness. This is not sugar: there is no `t.0`, so destructuring is the only way to take a tuple apart. Nesting flattens to projection paths, and indices are *declaration* indices mapped through `decl_to_phys` — tuples are alignment-sorted exactly like structs.
- `const` — compile-time evaluated, inlined at every reference site, never emitted as a WASM global
- Functions, declared with `func` (renamed from `fn` to follow WAT), and `func(T) -> U` type expressions (first-class function references). A call passes arguments by position, `f(a, b)`, or by name, `f({ x: a, y })` (shorthand allowed); the two never mix (E1018)
- Structs, one form only: `struct Point(x: i32, y: i32);`, `struct Pair(i32, pub u8);`, `struct Unit();` — field names are optional per field, like `pub`. A struct is constructed by calling its name (`Point(1, 2)`, or `Point({ x: 1, y: 2 })` when every field is named), so the name is a value as well as a type and a function cannot share it; the constructor is accessible only where every field is. Old brace forms (`struct P { .. }`, `P::{ .. }`) are reported (E1019/E1020) and parsed as the new ones
- `impl` blocks, `pub func` methods, `#[inline]` attribute
- Traits with default method bodies, associated types (`type Size: PointerSize`), associated consts, `impl Trait for Type`
- **Operator overloading via trait dispatch** — fifteen `#[tag]`ged traits in `std/main.wx`: `add`/`sub`/`mul`/`div`/`rem`/`neg`, `bitand`/`bitor`/`bitxor`/`shl`/`shr`/`bitnot`, `not` (unary `!`), `PartialEq` (`==`/`!=` → `eq`/`ne`) and `PartialOrd` (`<`/`<=`/`>`/`>=` → `lt`/`le`/`gt`/`ge`). Every overloadable operator desugars through `find_trait_impl` (`build_operator_dispatch`), falling back to a plain `Binary`/`Unary` node in `Comptime` contexts so const-folding is untouched. Primitive impls are `#[inline]` over intrinsics (ordering ones split signed/unsigned, e.g. `i32_lt`/`u32_lt`), so monomorphized codegen is still native `i32.add`/`i32.lt_s` etc. with no call overhead. Generic (`T: Add`) and typeset-bounded (`Mem::Size`) operands defer dispatch to monomorphization. `PartialEq`/`PartialOrd` methods return `bool` rather than `Self`, and `PartialEq::ne` is the first bodied default — a default an impl doesn't override is dispatched as a `GenericMethodCall` so monomorphization can resolve it. Comparison operators on primitives/`bool`/enums/pointers still lower to a native `Binary` node (no `MethodCall`), but the operator span is recorded as a go-to-definition access against the resolved `PartialEq`/`PartialOrd` method. Non-overloadable: `&&`/`||` and assignment.
- **Compound assignment** — `+= -= *= /= %=` and `&= |= ^= <<= >>=`, all sugar over the same resolved dispatch (`x = x.add(y)`), represented by a dedicated node family in TIR (`Assign`/`CompoundAssign`/`GenericCompoundAssign`/`CompoundStore`/`GenericCompoundStore`) split on resolved-now vs. generic and plain-target vs. `Place`-target
- Enums and `match` (lowered through `br_table`). **An enum variant requires an explicit anchor value before auto-increment is legal** (E2071) — this closes a silent collision where `Ordering { Less, Equal = 0, Greater = 1 }` gave `Less` and `Equal` both 0.
- Generics / monomorphization — `func f<T>(t: T) -> T`; `#[inline]` on generic functions is propagated to their mono instances (`mir/tests.rs`, `test_inline_attribute_on_generic_propagated_to_mono_instance`)
- `mod` declarations for multi-file compilation (the keyword is `mod`, not `module`). A module owns a directory per path segment: `a.wx` declaring `mod shared;` resolves `a/shared.wx`, exactly as Rust does, and `math.wx` / `math/mod.wx` are interchangeable for where `math`'s own children live.
- **Path keywords `crate` and `super`** — pre-populated as real `SymbolKind::Module` entries in every namespace's own `.symbols` map at creation time, rather than special-cased in each path-walking function. `lookup_scope_chain` checks own symbols first and every multi-segment walker resolves later segments by direct lookup, so chaining (`super::super::x`) falls out for free. `self` is deliberately not implemented.
- **`use` trees** — `UseTree::{Glob, Name, Path, Group}`, so nested groups and globs both work. Named leaves are real items (`tir.use_items` + `ItemIndex::Use`).
- **`std` is an implicit prelude** — `lookup_scope_chain` consults the stdlib's root namespace as a final tier, after own symbols, globs and the parent walk. `use std::*;` is never needed. Deliberately a tier of its own rather than a synthetic glob: as the last tier, a name std happens to define can never shadow anything the user wrote or imported, so adding a stdlib item cannot break a program that already compiles.
- Rust-style default visibility — an item without `pub` is visible to its declaring namespace and every descendant namespace, not to ancestors or unrelated modules. Enforced for name lookup (wildcard imports), explicit qualified paths (both type- and value-position), `mod` declarations themselves, `use` re-exports (a plain `use` no longer silently acts as `pub use`), and **struct fields** (E1076). Still **not** enforced for method calls — see Common pitfalls.
- **Inherent `impl` is restricted to the package that defines the type** (E1077) — no `impl f32 { }` in user code
- `memory` declarations — `memory heap: Memory32;` lowers to WASM linear memory; page limits via `#[memory_limits(min_pages = .., max_pages = ..)]`
- **Package instances, `crate "key" as alias;` / `pub crate "key" as alias;`** (the `crate` keyword is to be replaced by `package`) — instantiate the package the manifest declares under `key` and binds it as `alias` in the scope the item is written in. Allowed in any module; private by default (visible to the declaring module and its descendants), and `pub` lets a consumer name the dependency through this package. An undeclared key is E2113, a missing `as` E1021. Each instance is its own instantiation site, recorded in `Namespaces::package_instances`, and its alias is a definition of its own (`DefKind::PackageInstance(PackageInstanceIdx)`, with the alias as its declaration span). Resolution does not yet tell instances apart: a path through the alias continues into the package's one namespace (`Namespaces::entered_by`); a `Namespace::PackageInstance` per instance is the follow-up. An unknown key binds a poisoned alias (`BindingTarget::Error`), so a path through it ends silently instead of cascading. When codegen is revived, each instance must produce its own copy of the package's code. The stdlib is not instantiated this way; `std` stays implicit.
- `import "module" { func ... }` — WASM imports; `export { func, global }` — WASM exports (optionally renamed with `as "name"`). An export block must be unique per package, live at the binary root, and never appear in a library (E1072/E1073/E1074).
- `#[intrinsic]` — marks functions in `mod wasm { }` as WASM intrinsics (memory ops), and bodiless type aliases as primitives
- Untyped integer/float literals coerced by context or via `as T` cast. Literals are held as `u64`.
- `as` casts: validity is checked via `are_scalar_compatible`/`WasmScalar` equivalence (not a numeric-only allowlist) — integer↔integer and `char`↔`u8`/`u16`/`u32` all pass since `char` and `u32` share `WasmScalar::I32`. See Common pitfalls for what this does *not* check.
- `loop`, `break <value>`, `continue`, labeled blocks (`outer: block { break :outer }`)
- Block expressions (last expression without `;` is the value). A plain block is `block { ... }`: `{` alone never starts an expression, which keeps `f({ ... })` unambiguous; blocks owned by a construct (`if`/`else`, `loop`, match arms, function bodies) need no keyword. A bare `{` is reported (E1017) and parsed as a block

**Designed but not implemented:** the effect system (`does(...)` syntax — `notes/effect-system.md`, `notes/effect-tracking-plan.md`) and ownership/borrow checking (`notes/`, `devlog/2026-08-11-*`). Neither exists in the lexer, parser or stdlib. Don't describe them as features.

## MIR passes (in order)

1. **Lowering** — live defined monomorphic functions only; generics are lowered on demand by the mono pass. Wasm index ordering (imports first) is codegen's responsibility, not MIR's.
2. **Monomorphization** — generic functions instantiated per unique type-arg set via `MonoRegistry`, draining a worklist populated by `lower_expression` (each iteration may add more, so it loops until exhausted). The start function is built *before* this loop so generics called from global initializers join the same worklist.
3. **Inlining + DCE** (`run_inlining_pass` in `mir/inlining.rs`, called once from `MIR::build`) — one function doing both: Kahn topological sort of the `#[inline]` call graph (cycle-breaking via anchor selection for mutual recursion), then a reachability walk from `mir.exports` **and** `mir.start_function` that `retain`s only reachable functions in `mir.functions`.

Compound assignment is **not** desugared here — TIR already lowers `+=` to resolved trait dispatch; MIR just lowers the resulting node family.

Inlining appends an inlined call's parameters and locals directly to the caller's existing scope at the call site, rather than creating a sibling scope per call. `compute_locals_offsets` lets same-parent scopes share a flat local-offset range on the assumption that they're mutually exclusive at runtime (true for if/else/match arms); a per-call scope broke that and let two inlined calls at one site clobber each other. Appending means a second call simply gets index ranges past the first's — nothing to compare or protect against. The `Rebaser` that does this is shared with `build_start_function`'s globals-combining.

Struct layout uses alignment-sorted field ordering (fields sorted descending by alignment) to minimize padding; `#[fixed_order]` preserves declaration order instead.

String literals lower to a `&[u8]` slice aggregate `{ StaticPointer, len }`. Static data (string literals, array constants) is currently always placed in `memories[0]` (the first declared memory).

## Testing patterns

Tests live in `#[cfg(test)]` modules at the bottom of each source file.

**TIR (live):** the tests are inside `tir/signatures.rs` (and a few in `satisfaction.rs`). Signatures store types as written, so a test that asserts on what a projection *means* normalizes it first: `case.normalized_param("f", 0)`, `case.normalized(scope, ty)`, or `case.try_normalized_param(..)` for a type with no value (`Err(SolverError::Poisoned)`); `case.is_projection_param(..)` asserts the stored form. A test that looks impls up on a `with_pending_signatures` builder calls `builder.sweep()` first. `TypeContext` borrows its inputs, so a test keeps them on its own stack through a macro: `test_case!(case = "func f() {}")` (also `test_case!(mut case = …)` and `test_case!(case from <CompilationUnit>)`) declares the graph, `TestInputs` and a swept `TestCase` as three locals; `checked_case!` also asserts a clean parse and link. Read state through `case.context.<field>` (e.g. `case.context.functions`, `case.context.diagnostics`) and look items up with `case.resolve(..)`, which goes through real path resolution. The test source plays the stdlib's own role (`set_stdlib`), so a test that needs a primitive declares its own bodiless `pub type i32;`.

**Legacy (not compiled):** `tir/tests.rs`, `tir/snapshots/` and `mir/tests.rs` belong to the old pipeline and use `TestCase::new(..)` over a full `TIR`/`MIR`, with `insta` snapshots. They are the pattern to revive when those stages come back.

Test sources do **not** need `use std::*;` — the implicit prelude covers it.

`testing::DiagnosticView` is the shared vocabulary for diagnostic assertions: `assert_none`, `assert_no_errors`, `assert_error`, `assert_warning`, `assert_reported`, `assert_absent`, `assert_codes`, `assert_error_saying`. Prefer these over hand-rolled `matches!` or code-only checks — they render the offending source into the panic message and actually check severity, which a bare code comparison does not. `define_diagnostic_codes!` lives in `crate::diagnostics` and emits a `Code` trait impl, so one assertion accepts a code from any stage.

Adoption is uneven, so follow the suite you're in. `ast/tests.rs` and `vfs/tests.rs` are migrated: their `TestCase` exposes `diagnostics() -> DiagnosticView<'_>`, used as `case.diagnostics().assert_error(DiagnosticCode::…)`. The TIR suite's `TestCase::diagnostics()` also returns a `DiagnosticView`; the legacy `tir`/`mir` suites used a local free `assert_no_errors(&case)` helper. Write new assertions against `DiagnosticView` (construct one with `DiagnosticView::new(stage, diagnostics, files)`) rather than ad-hoc helpers.

Prefer assertions that state the claim over snapshots. The parser suite deliberately keeps only two snapshots (`top_level_items`, `use_tree_forms`) — genuinely structural cases — and expresses everything else directly; a `shape()` helper renders an expression as an S-expression (`a + b * c` → `(+ a (* b c))`) so precedence assertions name the tree they expect. Note that a snapshot of a *broken* parse still passes unless the test also asserts no diagnostics first.

Snapshot files live in `src/<stage>/snapshots/`. Never edit `.snap` files by hand. Any change to `std/main.wx` shifts byte offsets causing all snapshot tests to fail — regenerate with `cargo test -p wx-compiler` then `cargo insta accept`.

## Common pitfalls

- **Pre-interned `TypeIndex` ordering:** never insert in the middle of the pre-interned `vec![...]` literal in `TypeInterner::new()` (`tir/types.rs`) — every downstream type check silently gets wrong types. Add at the end only, and update the constants below it in the same file.
- **`ensure_signature` re-entrancy and early returns:** guarded by `query_state: HashMap<DefId, QueryEntry>` (`QueryState::{Pending, InProgress, Resolved, CycleReported}`); re-entering an `InProgress` query is a cycle. It returns `SignatureStatus` — handle `Cycle`, or say why you don't with `let _ = ... // reason`. The cached-state check returns before a frame is pushed; after that, add no early `return`, so the `query_stack` frame is always popped by the unwind at the bottom.
- **Don't freeze or copy `TypeContext`:** it is the one live owner of type state through body checking. A frozen registry, a second type interner, or `Arc`/`unsafe` to let the owner and its borrowed inputs coexist were all considered and rejected (`notes/tir-type-context.md`).

**The pitfalls below mostly describe the disabled `tir/builder/` and MIR and matter again when those are ported; the package-root-namespace invariant and `wx format` are the exceptions that still apply.**

- **Cast checking is looser than it looks:** `are_scalar_compatible`/`WasmScalar` equivalence is the gatekeeper for `as` casts, not a numeric-only allowlist. Two known gaps, both documented at `tir/builder/literal.rs:301`: lossy casts like `u32 as char` pass, and **pointer casts only compare `memory`, not ownership — so `&T as *T` passes, silently defeating "a `&T` is always read-only"**. Fixing the second needs a real rework of `as`-cast checking (likely alongside whatever borrow-checking wx eventually gets), not a local patch.
- **Privacy is enforced at namespace-lookup sites and struct fields, but not at method calls:** `is_accessible_from`/`is_entry_accessible_from`/`namespace_contains` (`tir/builder/modules.rs`) gate wildcard imports, qualified paths, `mod` declarations and `use` re-exports; `resolve_struct_field` (`tir/builder/aggregates.rs`) gates field access for all three sites that need it (object access, struct literal init, struct pattern destructuring). Method calls — `obj.method()` and `Type::method()`, both funnelling through `resolve_impl_member` (`tir/builder/calls.rs`) — are **not** gated, so a missing `pub` on an impl method does not block access. This is a missing call, not a missing mechanism: impl methods already carry a real `namespace`/`pub_span`. The one real gap is trait *default-body* methods (no impl override), which have no `pub_span` of their own and would need a fallback to the trait's own visibility, mirroring how `SymbolKind::TraitAssocType` already falls back to its trait.
  - Note the predicate renames: `is_ancestor_or_self` → `namespace_contains` (with the argument order the name implies), `visible_from` → `is_accessible_from`, `entry_visible_from` → `is_entry_accessible_from`.
- **Every package owns a root namespace, including the root package.** That is what makes `ScopeTable.parent: None` (a `Scope::Package`) mean "no ancestor" and nothing else, so a plain `.parent` walk terminates inside the package it started in and can never cross into another one. It used to mean *both* "no ancestor" and "the root package's own top-level scope" (backed by a global symbol table) — so a lookup walking past any package boundary fell through into the root's items. Don't reintroduce a global fallback in `lookup_global_symbol`: running out of parents *is* the package boundary. A package has no name of its own either — it's known by the `dependencies` key whoever declared it used, so use `TIR::namespace_name(ns, packages, from)` rather than looking for a name on the namespace.
- **`SymbolEntry` splits `Pending` from `Resolved`:** an unresolved claim is `SymbolEntry::Pending(DefId)` with no `visibility` field at all, rather than a `Resolved` carrying a defaulted fake `Public`. That split is what makes `use` re-export privacy expressible — a re-export's resolved entry is otherwise bit-for-bit identical to a direct declaration's (deliberately, so the same item reached via two paths collapses instead of raising a false ambiguity), so the `pub_span` must come from the `use` leaf itself. `insert_symbol` takes an explicit `pub_span` from its caller for this reason.
- **Field indices are declaration indices.** `FieldIndex(u32)` is the *declared* index and must go through `decl_to_phys`, because MIR reorders fields by alignment. This applies to tuples too — `(bool, i64, u32)` has physical slots `[2, 0, 1]`, so a naive `value_index: index` silently returns the wrong element.
- **`wx format` and the LSP formatting request must agree byte for byte.** Both go through `RendererConfig::from_manifest`. An already-formatted file must report *no* edits at all, or format-on-save dirties the buffer.
