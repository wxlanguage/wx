# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning currently applies to the whole project at once (the compiler,
CLI, and LSP are released in lockstep) rather than per-crate. Editor
integrations (e.g. [wxlanguage/vscode](https://github.com/wxlanguage/vscode))
live in their own repos with independent versioning.

## [0.2.0] - 2026-07-20

### Changed

- **Breaking:** a trait may now have at most one implementation per type
  constructor. `impl Trait for Box<i32>` and `impl Trait for Box<u8>` (or
  two differently-bounded generic impls of the same trait for the same
  struct) now conflict at declaration time, reported as `E1061`, even if
  the conflicting impls are never actually called. This replaces the
  previous behavior of allowing multiple same-trait impls to coexist and
  resolving/erroring on ambiguity lazily at the call site.

### Added

- Language: generic trait impls — `impl<T> Trait for Type<T>`, including
  bounded params (`impl<T: Foo> Bar for Vec<T>`), with full support for
  monomorphization and associated-type substitution through the impl.
- Language: `Allocator` trait in the standard library (`type M: Memory`,
  `reserve`, `alloc<T>`, `alloc_slice<T>`), giving custom allocators
  (e.g. bump allocators) a standard interface.
- Language: the unused-variable warning no longer fires for
  underscore-prefixed names (`_foo`) or an unused `self` receiver,
  matching Rust's convention.
- WASM: correct pointer-width handling for `Memory64`-declared memories —
  pointers, `memory.size`/`memory.grow`, and static data offsets now use
  64-bit addressing where required instead of always emitting 32-bit
  code (which produced invalid WASM). Static data placement is also now
  correctly per-memory in multi-memory modules, instead of always
  landing in memory 0.
- Language Server: go-to-implementation (`textDocument/implementation`);
  proper hover/goto-definition/highlighting for `self` and `Self`;
  `memory` declarations are now indexed (hover/goto-def previously did
  nothing for them); completions after `::` for enums, structs, traits,
  and namespaces.

### Fixed

- A real correctness bug where unsigned (`u32`/`u64`) comparisons,
  right-shifts, division, and remainder were compiled using signed WASM
  instructions, producing wrong results for values that differ under
  signed vs. unsigned interpretation.
- A parser panic (`unreachable!()`) on malformed label syntax reachable
  from ordinary mid-edit states (e.g. `std::io:` while typing
  `std::io::`) — now reports a normal diagnostic (`E0014`) instead of
  crashing.
- A type-checker bug where a pointer type referenced before its
  `memory` declaration's own signature had resolved (e.g. inside an
  earlier `import` block) could be interned as a distinct, identical-
  looking type, producing confusing "expected `heap::*mut u32`, found
  `heap::*mut u32`" diagnostics.
- A MIR lowering crash ("no impl found for associated type projection")
  when a trait's default generic method used an associated `Memory`
  type in its own signature (as the new `Allocator` trait does).
- A false-positive "unused function" warning for trait methods only
  ever reached through dynamic dispatch (a trait default calling an
  abstract method on `Self`).
- Formatter: attributes (e.g. `#[tag = "..."]`) on `typeset` items were
  silently dropped when formatting; generic params on a trait impl
  (`impl<T> Trait for Type<T>`) were also being dropped.
- Formatter: comments inside an otherwise-empty `{}` body, and
  leading/gap/trailing comments around import/export entries, were
  being dropped.
- Language Server: associated consts without a body (a trait's own
  abstract `const`, or a memory's synthesized consts) were invisible to
  hover/goto-def; type-annotation completions incorrectly offered
  functions and constants; bare enum variants leaked into plain-
  identifier completion.

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
  see [wxlanguage/vscode](https://github.com/wxlanguage/vscode/blob/main/CHANGELOG.md) for details.
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
  [wxlanguage/vscode](https://github.com/wxlanguage/vscode/blob/main/CHANGELOG.md) for extension-specific
  changes).
