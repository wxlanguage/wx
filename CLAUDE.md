# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

WX is a Rust-implemented compiler for a language that targets WebAssembly. Syntax is Rust-inspired. This is a bachelor's thesis project.

## Commands

```bash
# Build
cargo build -p wx-compiler           # core library
cargo build --release -p wx-cli  # CLI binary → target/release/wx

# Inspect WASM output (WABT is installed)
wasm2wat output.wasm                 # disassemble to WAT text format
wasm-objdump -d output.wasm          # annotated disassembly

# Test (almost all tests live in wx-compiler)
cargo test -p wx-compiler
cargo test -p wx-compiler -- <test_name>  # single test by name

# Update snapshots when output changes legitimately
cargo test -p wx-compiler
cargo insta accept

# Format
cargo fmt

# Build the WASM playground package
deno task build:wasm
```

## Crates & binaries

`wx` is a single native binary (from `wx-cli`) with `compile`/`check`/`format`/`lsp` subcommands — there is no separate `wx-lsp` binary anymore. `wx-lsp` is a library-only crate (no `main.rs`): it exposes `build_service()` (builds the `tower-lsp-server` `LspService`) and `run_stdio(stdin, stdout)` (serves it over a caller-supplied transport). `wx-cli`'s `lsp` subcommand (`cmd_lsp` in `wx-cli/src/main.rs`) is the only place that spins up a Tokio runtime — a current-thread one, scoped to just that subcommand, since everything else in the CLI is synchronous.

`run_stdio` is `#[cfg(not(target_arch = "wasm32"))]`: `tower_lsp_server::Server`'s `AsyncRead`/`AsyncWrite` bounds resolve to a different trait depending on which of its features is active (`tokio::io`'s under `runtime-tokio`, native; `futures::io`'s under `runtime-agnostic`, wasm32), so it can only compile for the target whose trait it's bounded by. `wx-lsp-wasm` (excluded from the main workspace — wasm32-only, built via `wasm-pack`/`deno task build:wasm` for the browser playground in `web-next/`) only ever calls `build_service()` directly and bridges the transport over `postMessage` instead.

Distribution: `wx` (all subcommands, including `lsp`) ships via GitHub Releases and npm (`@wx-lang/cli`, per-platform optional deps) — see `.github/workflows/publish-cli.yml`. Release binaries are stripped (`[profile.release] strip = true` in the root `Cargo.toml` — cheap enough, no build-time cost, to apply everywhere including a plain local `cargo install`); `lto`/`codegen-units = 1` are enabled only in `publish-cli.yml`'s build step via env vars, not in `Cargo.toml`, since they meaningfully slow down builds and should only cost time on binaries actually being shipped.

## Editor integrations

`editors/` holds one git submodule per supported editor, each a fully self-contained repo under the `wxlanguage` org (own `package.json`/lockfile, own `.github/workflows/`, own `.vscode/` debug config) — nothing about them lives in the main repo beyond the submodule pointer and `.gitmodules`. `editors/vscode` ([wxlanguage/vscode](https://github.com/wxlanguage/vscode)) is functional; it doesn't bundle a `wx` binary, it resolves `wx` from the user's `PATH` (or an explicit `wx.path` setting) and spawns `wx lsp`, the same model as `deno.path`. `editors/zed` ([wxlanguage/zed](https://github.com/wxlanguage/zed)) is an MVP: a self-referential tree-sitter grammar (`[grammars.wx]` in `extension.toml` points `repository`/`rev` at this same repo, with the grammar source under `grammar/` via the `path` field — a real but undocumented `GrammarManifestEntry.path` field, confirmed from Zed's source rather than its docs) that gives real structure to top-level items but parses signatures/bodies as generic balanced-token groups rather than a full expression grammar; verified against every `.wx` file in this repo with zero parse errors. `src/lib.rs` resolves `wx` the same way as the VS Code extension (`Worktree::which("wx")`), with Zed's native `lsp.wx.binary.path`/`arguments` settings as an override — no custom setting needed. Not yet published to Zed's extension registry; install as a dev extension for local testing. Zed's own extension registry (a submodule tree itself) requires each listed extension to live in its own repo, which is why this follows the same one-repo-per-editor structure as `vscode` rather than living directly under `editors/`. Clone with `git clone --recurse-submodules`, or run `git submodule update --init` after a plain clone — a submodule directory is empty until explicitly initialized. To debug an editor integration, open its `editors/<name>` folder directly as its own VS Code window rather than from the `wx` root, since its `.vscode/launch.json` only applies there.

## Releasing

The compiler, CLI, and LSP are versioned in lockstep (see `CHANGELOG.md`'s preamble) rather than per-crate. For the full release process (version bump rules, changelog conventions, branch protection, tagging, and publish-workflow gotchas), use the `release-wx` skill.

## Compilation pipeline

```
source text
    │  ast::Parser::parse()
    ▼
AST  (src/ast/)
    │  vfs::CompilationGraphBuilder — load_stdlib()/load_binary()/build() → CompilationGraph
    │  tir::TIR::build(&mut compilation)
    ▼
TIR  (src/tir/) — type-checked, name-resolved IR
    │  MIR::build(&tir, &interner, graph.id_generator)
    ▼
MIR  (src/mir/) — desugared, monomorphized, inlined IR
    │  opt::builder::Builder::build(&mir, func_mir) per function
    ▼
Opt  (src/opt/) — sea-of-nodes SSA per function
    │  opt::scheduler::Scheduler::schedule(&opt, &mir)
    ▼
ScheduledFunction
    │  codegen::Builder::build(&mir, &interner) → Result<WasmModule, ()>
    ▼
WASM bytecode (WasmModule::encode() → Vec<u8>)
```

`std/lib.wx` is embedded via `include_str!("../../std/lib.wx")` in `vfs/mod.rs` as `STDLIB_SOURCE` and is always the first file in the `CompilationGraph` (loaded via `CompilationGraphBuilder::load_stdlib()`). It defines the `Memory` trait, `wasm` module intrinsics, `impl char` methods, and stdlib constants.

## Key modules (`crates/wx-compiler/src/`)

- **`ast/`** — lexer + parser → AST nodes
- **`tir/builder.rs`** — the largest file; prescan + demand-driven type checker and name resolver
- **`mir/mod.rs`** — desugaring: `+=` → explicit `=`, struct access → `AggregateGet`, `char` → `U32`, inlining, monomorphization, DCE
- **`opt/`** — sea-of-nodes SSA IR for per-function optimization (CSE via `Builder::node`, which delegates to `intern_node`; liveness, scheduling)
- **`codegen/mod.rs`** — WASM bytecode emitter; `Builder::build` is the entry point
- **`vfs/`** — `CompilationGraph` and file loading; `VirtualFileSource` for in-memory tests
- **`../std/lib.wx`** — standard library source (sibling to `src/`), embedded at compile time

The pretty-printer used to live at `fmt/` in this crate; it's now its own crate, `wx-fmt` (`crates/wx-fmt/src/lib.rs`), used by both `wx-cli` (the `format` subcommand) and `wx-lsp` (the LSP formatting request).

## TIR resolution design

`tir/builder.rs` uses a prescan + demand-driven approach across four phases:

1. **Phase 1 — `pre_scan_item()`**: walks every item in every file and registers it into `builder.ast_nodes: Vec<AstEntry<'ast>>` (parse order; each entry holds `def_id`/`file_id`/`namespace`/`node`). No type-checking; just populates the registry.
2. **Phase 2 — `ensure_signature(def_id)`**: called for every registered `DefId` in parse order (via `sig_state`, built from `ast_nodes` right after Phase 1 completes). Demand-driven — `ensure_signature` is re-entrant safe (guarded by `sig_state: HashMap<DefId, SigEntry>`, where `SigEntry` holds the `ast_nodes` index plus a `ComputeState`) so resolving one signature can pull in another on demand.
3. **Phase 3 — `ensure_body(def_id)`**: evaluates function bodies for every registered `DefId`.
4. **Phase 3.5 — `check_trait_conformance()`**: verifies every trait impl provides all required items.
5. **Phase 4 — exports**: processes `export { ... }` blocks after all signatures are resolved.

## Type system

Every type is a `TypeIndex` (u32) into `tir.type_pool`. The first 18 slots (`ERROR` through `CHAR` below) are pre-interned via a single hardcoded `vec![Type::Error, Type::Infer, ..., Type::Char]` literal at the top of `tir::builder::build` (`tir/builder.rs`, assigned directly to `tir.types`; the reverse lookup `type_index_lookup` is then built by iterating over it) and MUST match the constants in `tir/mod.rs`. Never reorder them; add new pre-interned types at the end only.

| Constant | Index |
|---|---|
| `ERROR` | 0 |
| `INFER` | 1 |
| `UNIT` | 2 |
| `NEVER` | 3 |
| `INTEGER` | 4 |
| `FLOAT` | 5 |
| `U8` | 6 |
| `I8` | 7 |
| `U16` | 8 |
| `I16` | 9 |
| `U32` | 10 |
| `I32` | 11 |
| `U64` | 12 |
| `I64` | 13 |
| `F32` | 14 |
| `F64` | 15 |
| `BOOL` | 16 |
| `CHAR` | 17 |

`INFER` is a type inference placeholder — used internally when a generic type argument cannot yet be determined, and will be the type of user-written `_` in type annotations. Must never reach MIR or codegen.

`char` is a primitive in TIR but lowers to `U32` in MIR and WASM.

## Language features (current state from tests)

- Primitives: `i32`, `i64`, `u32`, `u64`, `f32`, `f64`, `bool`, `char`, `u8`, `i8`, `u16`, `i16`
- String literals have type `[]u8` (byte slice); there is no separate `string` type
- `local` / `local mut` declarations; `global` / `global mut` for module-level state
- `const` — compile-time evaluated, inlined at every reference site, never emitted as a WASM global
- Functions, `fn(T) -> U` type expressions (first-class function references)
- Structs, `impl` blocks, `pub fn` methods, `#[inline]` attribute
- Traits with default method bodies, associated types (`type Size: PointerSize`), associated consts, `impl Trait for Type`
- Generics / monomorphization — `fn f<T>(t: T) -> T`; `#[inline]` on generic functions is propagated to their mono instances (`mir/tests.rs`, `test_inline_attribute_on_generic_propagated_to_mono_instance`)
- `module` declarations for multi-file compilation; `pub` visibility for cross-module access
- `memory` declarations — `memory heap: Memory32;` lowers to WASM linear memory
- `import "module" { fn ... }` — WASM imports; `export { fn, global }` — WASM exports (optionally renamed with `as "name"`)
- `#[intrinsic]` — marks functions in `module wasm { }` as WASM intrinsics (memory ops)
- Untyped integer/float literals coerced by context or via `as T` cast
- `as` casts: validity is checked via `are_scalar_compatible`/`WasmScalar` equivalence (not a numeric-only allowlist) — integer↔integer and `char`↔`u8`/`u16`/`u32` all pass since `char` and `u32` share `WasmScalar::I32`. Unsafe/lossy casts (e.g. `u32 as char`, which is *not* currently blocked) aren't yet checked — TODO at `tir/builder.rs:9579`
- `loop`, `break <value>`, `continue`, labeled blocks (`outer: { break :outer }`)
- Block expressions (last expression without `;` is the value)

## MIR passes (in order)

1. **Monomorphization** — generic functions instantiated per unique type-arg set via `MonoRegistry`
2. **Inlining + DCE** (`run_inlining_pass`, called once from `MIR::build`) — one function doing both: Kahn topological sort of the `#[inline]` call graph (cycle-breaking via anchor selection for mutual recursion), then a reachability walk from `mir.exports` **and** `mir.start_function` that `retain`s only reachable functions in `mir.functions`

Struct layout uses alignment-sorted field ordering (fields sorted descending by alignment) to minimize padding.

String literals lower to a `[]u8` slice aggregate `{ StaticPointer, len }`. Static data (string literals, array constants) is currently always placed in `memories[0]` (the first declared memory).

## Testing patterns

Tests live in `#[cfg(test)]` modules at the bottom of each source file. The `TestCase` helper in `tir/tests.rs` and `mir/tests.rs` constructs a `CompilationGraph` (which automatically includes `std/lib.wx`) and runs the pipeline:

```rust
// TIR test
let case = TestCase::new(indoc! { "fn add(a: i32, b: i32) -> i32 { a + b } export { add }" });
assert!(case.tir.diagnostics.is_empty());
insta::assert_yaml_snapshot!(case.tir);

// MIR test
let case = TestCase::new(indoc! { "..." });
assert_eq!(case.mir.functions.len(), 2);
insta::assert_yaml_snapshot!(case.mir);

// Multi-file TIR test
let case = TestCase::new_multi_file("src/main.wx", "module math;", &[("src/math.wx", "pub fn add() -> i32 { 1 }")]);
```

Snapshot files live in `src/tir/snapshots/` and `src/mir/snapshots/`. Never edit `.snap` files by hand. Any change to `std/lib.wx` shifts byte offsets causing all snapshot tests to fail — regenerate with `INSTA_UPDATE=always`.

## Common pitfalls

- **Pre-interned `TypeIndex` ordering:** never insert in the middle of the pre-interned `vec![...]` literal at the top of `tir::builder::build` — every downstream type check silently gets wrong types.
- **`ensure_signature` re-entrancy:** guarded by `sig_state: HashMap<DefId, SigEntry>` (each entry carries a `ComputeState`); an in-progress state means a cycle. Adding resolution code that calls `ensure_signature` recursively is safe only if cycles are handled.
- **Cast checking is looser than it looks:** `are_scalar_compatible`/`WasmScalar` equivalence is the gatekeeper for `as` casts, not a numeric-only allowlist — lossy casts like `u32 as char` currently pass (see `tir/builder.rs:9579` TODO). Don't assume the cast surface is fully validated.
- **`pub fn` only:** impl methods without `pub` are not visible to user code via `Type::method()` call syntax.
