# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

WX is a Rust-implemented compiler for a language that targets WebAssembly. Syntax is Rust-inspired. This is a bachelor's thesis project.

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

Current baseline: 1006 `wx-compiler` + 43 `wx-fmt` + 62 `wx-lsp` tests pass, clippy clean.

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

- **A package has no name of its own.** It is known by the key the *dependent* declared it under, which is why `PackageName` is a validated newtype on the `dependencies` key and `TIR::namespace_name(ns, packages, from)` needs a "from" context to name anything. Duplicate keys are E2005; declaring `std` as a dependency is E2004.
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

`CompilationUnit` owns diagnostic gathering for the whole package graph — `collect_parser_diagnostics()`, `collect_linker_diagnostics()`, and `collect_diagnostics()` (both, interleaved per package). Don't walk `packages`/`modules` by hand to print or count diagnostics; and use the `Diagnostics` extension trait (`errors`/`error_count`/`has_errors`) rather than spelling out `Severity::Error | Severity::Bug`, since dropping `Bug` from any one such check is a silent hole.

The stdlib is embedded at build time by `crates/wx-compiler/build.rs`, which walks `std/**/*.wx` into `STDLIB_FILES: &[(&str, &str)]` (`/`-prefixed path relative to `std/`, source). `StdlibFileSource` serves it to the loader by reading that table directly. Adding a stdlib file means creating it and writing the `mod` declaration that references it — there is no third list to update. `std/main.wx` defines the twelve operator traits, the `Memory` trait, `mod wasm` intrinsics, `impl` blocks for the primitives, and stdlib constants.

## Key modules (`crates/wx-compiler/src/`)

- **`ast/`** — lexer + parser → AST nodes
- **`tir/builder/`** — prescan + demand-driven type checker and name resolver; 16 modules, ~21k lines (see below)
- **`tir/mod.rs`** — the TIR data model: `TypeInterner`, `ItemRegistry`, `ModuleGraph`
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

### `tir/builder/` layout

Split by **feature slice**, not by kind — each module owns its own `report_*` diagnostics rather than sourcing them from a shared `diagnostics.rs` (of the 88 `report_*` functions, 78 had all their call sites inside one slice). `mod.rs` keeps only the `Builder` struct, the `build()` phase driver, the whole-program lint passes, the genuinely cross-cutting diagnostics, and the enums several slices share. Child modules reach `Builder` through `use super::*`; anything called across a slice boundary is `pub(super)`.

```
operators.rs 2078   calls.rs      1782   modules.rs      1636
types.rs     1585   paths.rs      1578   traits.rs       1568
signature.rs 1557   control.rs    1398   generics.rs     1337
body.rs      1123   type_compare.rs 1044   mod.rs        1023
literal.rs    988   aggregates.rs  976   memory.rs        732
prescan.rs    718
```

The module is still named `builder`, so `builder::build` and every existing import are unchanged.

## TIR data model

`TIR` is four fields, each its own arena-ish container:

- **`types: TypeInterner`** — `entries: Vec<Type>` plus a private `index_lookup` reverse map. Everything is a `TypeIndex` (u32) into it.
- **`items: ItemRegistry`** — `functions`, `globals`, `memories`, `enums`, `structs`, `use_items`, `use_prefixes`, `inherent_impls` + its `inherent_impl_dispatch` index, traits, and so on.
- **`modules: ModuleGraph`** — `namespaces: Vec<ModuleNamespace>`, `package_namespaces: HashMap<PackageId, NamespaceIndex>`, `file_namespaces: Vec<NamespaceIndex>` (indexed by `FileId`), `module_decls`, `import_decls`.
- **`export_block: Option<ExportBlock>`** — one `Option` answers both "is there a block" and "what does it export", so the two cannot drift.

## TIR resolution design

`tir::builder::build` uses a prescan + demand-driven approach. Before any phase runs it seeds the namespace graph:

- **Package root namespaces** — one per package, the root package included, walked in `graph.packages` order so `NamespaceIndex` values never depend on `HashMap` iteration order (they end up in snapshots). Each gets a `crate` symbol pointing at itself.
- **Dependency edges** — each `dependencies` key becomes an ordinary `SymbolKind::Module` entry in the *declaring* package's own namespace: a dependency is an implicit `mod <key>;` at the top of the entry file. Nothing global is involved, which is what keeps a package's dependencies invisible to its own dependents.

Then:

1. **Phase 1a** — one namespace per file, created directly from the `SourceModule` tree vfs already built, in `ModuleId` push order (vfs always pushes a parent before loading any child, so a child's parent namespace always already exists). Every `ModuleDecl` field is set exactly once, here; nothing downstream ever writes one afterward. `super` is seeded per namespace in `create_module_namespace`.
2. **Phase 1b — `pre_scan_item()`**: walks every top-level item and registers it into `builder.ast_nodes: Vec<AstEntry<'ast>>` (parse order; each entry holds `def_id`/`file_id`/`namespace`/`node`). A pure reader of `file_namespaces`. No type-checking. `sig_state` is then built from `ast_nodes` with exact capacity, all entries `Pending`.
3. **Phase 2 — `ensure_signature(def_id)`**: called for every registered `DefId` in parse order. Demand-driven and re-entrant safe (guarded by `sig_state: HashMap<DefId, SigEntry>`, where `SigEntry` holds the `ast_nodes` index plus a `ComputeState`), so resolving one signature can pull in another on demand. Returns `SignatureStatus { Resolved, Cycle }` — cycle detection lives here, not in callers. `sig_stack` records in-progress frames in call order so E1032 can name the whole loop (`A -> B -> C -> A`). `export { .. }` resolves here as an ordinary `ast_nodes` entry.
4. **`resolve_operator_traits()`** — resolves the twelve `#[tag]`ged operator traits into `builder.operator_traits`, between Phases 2 and 3.
5. **Phase 3 — `ensure_body(def_id)`**: evaluates function bodies for every registered `DefId`.
6. **Phase 3.5 — `check_trait_conformance()`**: verifies every trait impl provides all required items, comparing signatures through `type_compare.rs`.
7. **`report_unused_items()`**, then `finish()`.

There is no Phase 4 — the old post-hoc export loop is gone.

`ensure_signature` must have **no early `return` of its own**: every path out has to reach the unwind at the bottom, or the `DefId` is left `InProgress` forever and its `sig_stack` frame never pops, which would make every later cycle name items that finished resolving long ago. The `export` arm was extracted to `signature_export_block` for exactly this reason.

### Trait-conformance comparison (`type_compare.rs`)

Comparison runs against a `TypeEnvArena` addressed by a `Copy` `TypeEnvId`, so a resolver can build an environment and return a type still pointing into it. Both sides normalize through one `resolve_head`, then `project`. Two things this shape exists to prevent: an intermediate `Error`/`Infer` cascading a spurious signature mismatch on top of the diagnostic that already explains it, and the same interned `TypeIndex` reached under two different environments being taken as a fast-path match when it means different things on each side. `TypeDifferenceKind` is re-derived at render time via `classify`, not stored.

## Type system

Every type is a `TypeIndex` (u32) into `tir.types` (a `TypeInterner`). The first 18 slots are pre-interned by the hardcoded `vec![Type::Error, Type::Infer, ..., Type::Char]` literal in **`TypeInterner::new()` (`tir/mod.rs`)** — the reverse `index_lookup` is built by iterating over it — and MUST match the `TypeIndex` constants declared a little further down the same file. Never reorder them; add new pre-interned types at the end only.

| Constant  | Index |
| --------- | ----- |
| `ERROR`   | 0     |
| `INFER`   | 1     |
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

`INFER` is a type inference placeholder — used internally when a generic type argument cannot yet be determined, and will be the type of user-written `_` in type annotations. Must never reach MIR or codegen.

`char` is a primitive in TIR but lowers to `U32` in MIR and WASM.

## Language features (current state from tests)

- Primitives: `i32`, `i64`, `u32`, `u64`, `f32`, `f64`, `bool`, `char`, `u8`, `i8`, `u16`, `i16`. They are **real items** — `#[intrinsic] pub type X;` declarations in `std/main.wx`, bound by `ensure_signature` to the matching pre-interned `TypeIndex` — not a hardcoded string match, so they carry `DefId`s and LSP go-to-definition/hover/find-references work on them.
- Pointers, slices and arrays always carry an ownership sigil — `*T`/`&T`, `*[T]`/`&[T]`, `*[T; N]`/`&[T; N]` (`*` exclusive, `&` shared); there is no bare `[]T` and no `*mut T`. `.&` yields a shared reference (there is no `.&mut`). Each also belongs to a memory, resolved from the ambient one unless tagged explicitly (`heap::&[u8]`), and the type formatter always prints that memory prefix — so a slice surfaces in diagnostics as `heap::&[u8]`, never `&[u8]`
- String literals have type `&[u8]` (a shared byte slice); there is no separate `string` type
- `local` / `local mut` declarations; `global` / `global mut` for module-level state
- **`local <pattern> = expr` destructuring** — tuples, struct patterns (`Point::{ x, y }`, with a full path, matching wx's struct *literal* syntax rather than Rust's bare `Point { x, y }`), `_` (a drop, binds nothing), arbitrary nesting, and `..` to opt out of exhaustiveness. This is not sugar: there is no `t.0`, so destructuring is the only way to take a tuple apart. Nesting flattens to projection paths, and indices are *declaration* indices mapped through `decl_to_phys` — tuples are alignment-sorted exactly like structs.
- `const` — compile-time evaluated, inlined at every reference site, never emitted as a WASM global
- Functions, `fn(T) -> U` type expressions (first-class function references)
- Structs, `impl` blocks, `pub fn` methods, `#[inline]` attribute
- Traits with default method bodies, associated types (`type Size: PointerSize`), associated consts, `impl Trait for Type`
- **Operator overloading via trait dispatch** — twelve `#[tag]`ged traits in `std/main.wx`: `add`/`sub`/`mul`/`div`/`rem`/`neg` and `bitand`/`bitor`/`bitxor`/`shl`/`shr`/`bitnot`. Arithmetic, bitwise and unary `-`/`^` desugar through `find_trait_impl` (`build_operator_dispatch`), falling back to a plain `Binary`/`Unary` node in `Comptime` contexts so const-folding is untouched. Primitive impls are `#[inline]`, so monomorphized codegen is still native `i32.add` etc. with no call overhead. Generic (`T: Add`) and typeset-bounded (`Mem::Size`) operands defer dispatch to monomorphization. **Comparison operators are not overloadable yet.**
- **Compound assignment** — `+= -= *= /= %=` and `&= |= ^= <<= >>=`, all sugar over the same resolved dispatch (`x = x.add(y)`), represented by a dedicated node family in TIR (`Assign`/`CompoundAssign`/`GenericCompoundAssign`/`CompoundStore`/`GenericCompoundStore`) split on resolved-now vs. generic and plain-target vs. `Place`-target
- Enums and `match` (lowered through `br_table`). **An enum variant requires an explicit anchor value before auto-increment is legal** (E1071) — this closes a silent collision where `Ordering { Less, Equal = 0, Greater = 1 }` gave `Less` and `Equal` both 0.
- Generics / monomorphization — `fn f<T>(t: T) -> T`; `#[inline]` on generic functions is propagated to their mono instances (`mir/tests.rs`, `test_inline_attribute_on_generic_propagated_to_mono_instance`)
- `mod` declarations for multi-file compilation (the keyword is `mod`, not `module`). A module owns a directory per path segment: `a.wx` declaring `mod shared;` resolves `a/shared.wx`, exactly as Rust does, and `math.wx` / `math/mod.wx` are interchangeable for where `math`'s own children live.
- **Path keywords `crate` and `super`** — pre-populated as real `SymbolKind::Module` entries in every namespace's own `.symbols` map at creation time, rather than special-cased in each path-walking function. `lookup_scope_chain` checks own symbols first and every multi-segment walker resolves later segments by direct lookup, so chaining (`super::super::x`) falls out for free. `self` is deliberately not implemented.
- **`use` trees** — `UseTree::{Glob, Name, Path, Group}`, so nested groups and globs both work. The `DefId` lives on each `Name` leaf, not the item, since one `use` can bind several names. Named leaves are real items (`tir.use_items` + `ItemIndex::Use`).
- **`std` is an implicit prelude** — `lookup_scope_chain` consults the stdlib's root namespace as a final tier, after own symbols, globs and the parent walk. `use std::*;` is never needed. Deliberately a tier of its own rather than a synthetic glob: as the last tier, a name std happens to define can never shadow anything the user wrote or imported, so adding a stdlib item cannot break a program that already compiles.
- Rust-style default visibility — an item without `pub` is visible to its declaring namespace and every descendant namespace, not to ancestors or unrelated modules. Enforced for name lookup (wildcard imports), explicit qualified paths (both type- and value-position), `mod` declarations themselves, `use` re-exports (a plain `use` no longer silently acts as `pub use`), and **struct fields** (E1076). Still **not** enforced for method calls — see Common pitfalls.
- **Inherent `impl` is restricted to the package that defines the type** (E1077) — no `impl f32 { }` in user code
- `memory` declarations — `memory heap: Memory32;` lowers to WASM linear memory; page limits via `#[memory_limits(min_pages = .., max_pages = ..)]`
- `import "module" { fn ... }` — WASM imports; `export { fn, global }` — WASM exports (optionally renamed with `as "name"`). An export block must be unique per package, live at the binary root, and never appear in a library (E1072/E1073/E1074).
- `#[intrinsic]` — marks functions in `mod wasm { }` as WASM intrinsics (memory ops), and bodiless type aliases as primitives
- Untyped integer/float literals coerced by context or via `as T` cast. Literals are held as `u64`.
- `as` casts: validity is checked via `are_scalar_compatible`/`WasmScalar` equivalence (not a numeric-only allowlist) — integer↔integer and `char`↔`u8`/`u16`/`u32` all pass since `char` and `u32` share `WasmScalar::I32`. See Common pitfalls for what this does *not* check.
- `loop`, `break <value>`, `continue`, labeled blocks (`outer: { break :outer }`)
- Block expressions (last expression without `;` is the value)

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

Tests live in `#[cfg(test)]` modules at the bottom of each source file. The `TestCase` helper in `tir/tests.rs` and `mir/tests.rs` constructs a `CompilationUnit` (which automatically includes the embedded stdlib) and runs the pipeline:

```rust
// TIR test
let case = TestCase::new(indoc! { "fn add(a: i32, b: i32) -> i32 { a + b } export { add }" });
assert_no_errors(&case);
insta::assert_yaml_snapshot!(case.tir);

// MIR test
let case = TestCase::new(indoc! { "..." });
assert_eq!(case.mir.functions.len(), 2);
insta::assert_yaml_snapshot!(case.mir);

// Multi-file TIR test
let case = TestCase::new_multi_file("src/main.wx", "mod math;", &[("src/math.wx", "pub fn add() -> i32 { 1 }")]);
```

Test sources do **not** need `use std::*;` — the implicit prelude covers it.

`testing::DiagnosticView` is the shared vocabulary for diagnostic assertions: `assert_none`, `assert_no_errors`, `assert_error`, `assert_warning`, `assert_reported`, `assert_absent`, `assert_codes`, `assert_error_saying`. Prefer these over hand-rolled `matches!` or code-only checks — they render the offending source into the panic message and actually check severity, which a bare code comparison does not. `define_diagnostic_codes!` lives in `crate::diagnostics` and emits a `Code` trait impl, so one assertion accepts a code from any stage.

Adoption is uneven, so follow the suite you're in. `ast/tests.rs` and `vfs/tests.rs` are migrated: their `TestCase` exposes `diagnostics() -> DiagnosticView<'_>`, used as `case.diagnostics().assert_error(DiagnosticCode::…)`. `tir/tests.rs` and `mir/tests.rs` still use a local free `assert_no_errors(&case)` helper plus direct checks against `case.tir.diagnostics`. New assertions in those two suites are worth writing against `DiagnosticView` (construct one with `DiagnosticView::new(stage, diagnostics, files)`) rather than extending the ad-hoc helpers.

Prefer assertions that state the claim over snapshots. The parser suite deliberately keeps only two snapshots (`top_level_items`, `use_tree_forms`) — genuinely structural cases — and expresses everything else directly; a `shape()` helper renders an expression as an S-expression (`a + b * c` → `(+ a (* b c))`) so precedence assertions name the tree they expect. Note that a snapshot of a *broken* parse still passes unless the test also asserts no diagnostics first.

Snapshot files live in `src/<stage>/snapshots/`. Never edit `.snap` files by hand. Any change to `std/main.wx` shifts byte offsets causing all snapshot tests to fail — regenerate with `cargo test -p wx-compiler` then `cargo insta accept`.

## Common pitfalls

- **Pre-interned `TypeIndex` ordering:** never insert in the middle of the pre-interned `vec![...]` literal in `TypeInterner::new()` (`tir/mod.rs`) — every downstream type check silently gets wrong types. Add at the end only, and update the constants below it in the same file.
- **`ensure_signature` re-entrancy and early returns:** guarded by `sig_state: HashMap<DefId, SigEntry>` (each entry carries a `ComputeState`); an in-progress state means a cycle. It returns `SignatureStatus` — handle `Cycle`, or say why you don't with `let _ = ... // reason`. Never add an early `return` to it; the `sig_stack` frame must be popped by the unwind at the bottom.
- **Cast checking is looser than it looks:** `are_scalar_compatible`/`WasmScalar` equivalence is the gatekeeper for `as` casts, not a numeric-only allowlist. Two known gaps, both documented at `tir/builder/literal.rs:301`: lossy casts like `u32 as char` pass, and **pointer casts only compare `memory`, not ownership — so `&T as *T` passes, silently defeating "a `&T` is always read-only"**. Fixing the second needs a real rework of `as`-cast checking (likely alongside whatever borrow-checking wx eventually gets), not a local patch.
- **Privacy is enforced at namespace-lookup sites and struct fields, but not at method calls:** `is_accessible_from`/`is_entry_accessible_from`/`namespace_contains` (`tir/builder/modules.rs`) gate wildcard imports, qualified paths, `mod` declarations and `use` re-exports; `resolve_struct_field` (`tir/builder/aggregates.rs`) gates field access for all three sites that need it (object access, struct literal init, struct pattern destructuring). Method calls — `obj.method()` and `Type::method()`, both funnelling through `resolve_impl_member` (`tir/builder/calls.rs`) — are **not** gated, so a missing `pub` on an impl method does not block access. This is a missing call, not a missing mechanism: impl methods already carry a real `namespace`/`pub_span`. The one real gap is trait *default-body* methods (no impl override), which have no `pub_span` of their own and would need a fallback to the trait's own visibility, mirroring how `SymbolKind::TraitAssocType` already falls back to its trait.
  - Note the predicate renames: `is_ancestor_or_self` → `namespace_contains` (with the argument order the name implies), `visible_from` → `is_accessible_from`, `entry_visible_from` → `is_entry_accessible_from`.
- **Every package owns a root namespace, including the root package.** That is what makes `ModuleNamespace.parent: None` mean "no ancestor" and nothing else, so a plain `.parent` walk terminates inside the package it started in and can never cross into another one. It used to mean *both* "no ancestor" and "the root package's own top-level scope" (backed by a global symbol table) — so a lookup walking past any package boundary fell through into the root's items. Don't reintroduce a global fallback in `lookup_global_symbol`: running out of parents *is* the package boundary. A package has no name of its own either — it's known by the `dependencies` key whoever declared it used, so use `TIR::namespace_name(ns, packages, from)` rather than looking for a name on the namespace.
- **`SymbolEntry` splits `Pending` from `Resolved`:** an unresolved claim is `SymbolEntry::Pending(DefId)` with no `visibility` field at all, rather than a `Resolved` carrying a defaulted fake `Public`. That split is what makes `use` re-export privacy expressible — a re-export's resolved entry is otherwise bit-for-bit identical to a direct declaration's (deliberately, so the same item reached via two paths collapses instead of raising a false ambiguity), so the `pub_span` must come from the `use` leaf itself. `insert_symbol` takes an explicit `pub_span` from its caller for this reason.
- **Field indices are declaration indices.** `FieldIndex(u32)` is the *declared* index and must go through `decl_to_phys`, because MIR reorders fields by alignment. This applies to tuples too — `(bool, i64, u32)` has physical slots `[2, 0, 1]`, so a naive `value_index: index` silently returns the wrong element.
- **`wx format` and the LSP formatting request must agree byte for byte.** Both go through `RendererConfig::from_manifest`. An already-formatted file must report *no* edits at all, or format-on-save dirties the buffer.
