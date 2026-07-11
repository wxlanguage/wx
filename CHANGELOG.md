# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning currently applies to the whole project at once (the compiler,
CLI, and tooling are released in lockstep) rather than per-crate.

## [0.1.1] - 2026-07-11

### Added

- Language: `#[fixed_layout]` struct attribute to opt out of automatic
  field reordering, for structs that need to match an external ABI (e.g.
  WASI's `iovec`); `slice_ptr`/`.ptr()` intrinsic to get a slice's
  address, alongside the existing `slice_len`/`.len()`.
- Casts/coercions: `[]mut T -> []T` and `[N]mut T -> [N]T` (dropping
  write permission) are now allowed, matching the existing pointer rules.
- CLI: `-o/--output` (supports `-` for stdout) and
  `--message-format json` (NDJSON) for `compile`; `wx lsp` now runs the
  language server directly from the same binary (previously a separate
  `wx-lsp` executable).
- Examples: a hand-verified WASI Preview 1 "hello world"
  (`examples/wasi_hello_world`).

### Changed

- The VS Code extension no longer bundles a platform-specific binary —
  see [vscode/CHANGELOG.md](vscode/CHANGELOG.md) for details.
- Release binaries are smaller (debug symbols stripped).
- A malformed `import "..."` alias now reports a normal diagnostic
  instead of aborting the parser outright.

### Fixed

- A real correctness bug where two trait impls providing the same
  method name for a type would silently overwrite each other with no
  warning; this now reports a clear "ambiguous trait member" error
  instead of picking one arbitrarily.
- Multi-file compilations no longer stop reporting diagnostics after
  the first file's errors — every file's errors are now shown.

## [0.1.0] - 2026-07-09

First tagged release. Previously unversioned (all crates sat at a
placeholder `0.0.1` that was never published anywhere) — this is the
project's first real snapshot, primarily to validate that the release
pipeline (CI, npm publish, VS Code Marketplace publish) works end to end.
Still early: expect rough edges and breaking changes before 1.0.

### Added

- Compiler pipeline: AST → TIR (type-checked, name-resolved) → MIR
  (desugared, monomorphized, inlined) → sea-of-nodes SSA optimizer →
  WASM bytecode.
- Language: Rust-inspired syntax — structs, traits with default methods
  and associated types/consts, generics with monomorphization, `impl`
  blocks, `#[inline]`, labeled blocks/loops, multi-file `module`
  declarations with `pub` visibility.
- WASM interop: `memory` declarations, `import`/`export` blocks,
  `#[intrinsic]` bindings for memory ops.
- `wx` CLI: `compile`, `check`, and `format` subcommands, distributed as
  prebuilt native binaries via `@wx-lang/cli` on npm (Linux, macOS
  x64/arm64, Windows).
- Language Server: diagnostics, completions, and formatting, packaged as
  the "WX - WebAssembly Expressive Language" VS Code extension (see
  [vscode/CHANGELOG.md](vscode/CHANGELOG.md) for extension-specific
  changes).
