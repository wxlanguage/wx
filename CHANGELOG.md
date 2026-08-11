# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning currently applies to the whole project at once (the compiler,
CLI, and LSP are released in lockstep) rather than per-crate. Editor
integrations (e.g. [wxlanguage/vscode](https://github.com/wxlanguage/vscode))
live in their own repos with independent versioning.

## [0.4.0] - 2026-08-11

### Changed

- **Breaking:** `memory` declarations no longer take a trailing config
  block — page limits are now set via a `#[memory_limits(...)]` attribute:
  ```
  // before
  memory heap: Memory where { Size = u32 } { min_pages: 1, max_pages: 10 };
  // after
  #[memory_limits(min_pages = 1, max_pages = 10)]
  memory heap: Memory where { Size = u32 };
  ```
  Old syntax is now a parse error.
- **Breaking:** `#[fixed_layout]` renamed to `#[fixed_order]`. Note this is
  currently a *silent* breakage: unrecognized attribute names are dropped
  without a diagnostic, so code still using `#[fixed_layout]` will not fail
  to compile — it will silently fall back to alignment-sorted field order
  instead of preserving declaration order. Search your code for
  `#[fixed_layout]` and rename it manually.

### Added

- Std: float math/conversion intrinsics — `sqrt`/`abs`/`floor`/`ceil` for
  `f32`/`f64`, all `i32`/`u32`/`i64`/`u64` ↔ `f32`/`f64` convert/trunc ops,
  `f64_promote_f32`/`f32_demote_f64`, and `f32::PI`/`f64::PI`.
- wx-lsp: go-to-definition, hover, semantic highlighting, and completion
  now work for type aliases (`type Id = u32;`) — previously silently
  unindexed.
- MIR: dead-code elimination now also prunes unreachable imported
  functions, dropping an import module entirely once none of its items
  are reachable.
- Examples: new WASI Preview 1 examples (`wasi_args`, `wasi_random`,
  `wasi_file_io`) and a near-complete port of the
  `wasi_snapshot_preview1` witx spec (`wasi_preview1_port`) exercising
  real host imports; a `raycaster` example dogfooding the new float
  intrinsics.

### Fixed

- Sea-of-nodes scheduler: a pure value read from more than one block
  (e.g. shared across `if`/`else` branches) could be computed in only one
  branch and read as WASM's zero-initialized default from any other
  reader. `compute_value_placement` now hoists such values to their
  lowest common ancestor block. Also fixes a related if-without-else phi
  bug and excludes `Phi` nodes from CSE so unrelated if/else joins that
  happen to merge the same constants no longer alias.
- Codegen: `coalesce_locals` computed local live ranges from flat textual
  position, so a local written before a `loop`'s back-edge and read after
  it could be coalesced with an unrelated local, silently aliasing values
  across iterations.
- MIR: a narrow-field read through a pointer (`p.*.field as u32`) could
  over-read adjacent bytes.
- MIR/optimizer: nested aggregates (a struct field that is itself a
  struct) could crash the compiler or emit invalid WASM.
- Parser: `/=` compound assignment failed to parse.
- Codegen: an explicit `#[memory_limits(max_pages = ...)]` below the
  memory's actual required initial page count could produce an invalid
  WASM module (`initial > max`); `max_pages` is now bumped up to match
  when needed.
- wx-lsp: `Position::character` was treated as a raw byte offset instead
  of a UTF-16 code unit count per the LSP spec, so any line with
  non-ASCII content before the cursor could panic (e.g. completion after
  a Cyrillic comment).
- A bad `if` condition previously suppressed every diagnostic inside both
  branches instead of still checking them.
- `pub const` inside an `impl` block was wrongly flagged as unused.
- wx-fmt: `if`/`else` branches decided flat/break formatting
  independently even when nested under the same outer group, and excess
  indentation was added to calls whose single argument is a (possibly
  deeply nested) struct literal.

## [0.3.0] - 2026-07-25

### Changed

- **Breaking:** non-`pub` items are now only visible within their
  declaring namespace and its descendants (Rust-style default-visibility
  privacy), enforced at wildcard-import and qualified-path resolution in
  both type and value position, reported as `E1065`. Previously nothing
  enforced visibility anywhere in the resolver, so code relying on
  reaching a non-`pub` item through `use module::*` or a qualified path
  from outside its declaring module — previously silently accepted —
  now fails to compile.

### Added

- Language: `match` expressions — literal (`int`/`char`/`bool`),
  `Enum::Variant`, and `_` wildcard patterns, with full exhaustiveness
  checking (`E1066` for a non-exhaustive match) and a warning for an
  unreachable arm shadowed by an earlier identical pattern (`W1010`).
  Codegen picks between a WASM `br_table` (dense patterns) and a
  right-nested if/else chain (sparse), decided once during optimizer
  construction. See
  `devlog/2026-07-21-match-expression-and-br-table.md` for the full
  pipeline walkthrough.
- Language: qualified-path syntax — `<Type as Trait>::item` and
  `<Type>::item`, in both expression and type position, to disambiguate
  a name across multiple bounds/impls (e.g. two traits in scope
  declaring the same method or associated type).
- Language: `where { Assoc: Bound }` clauses — a generic function can
  now require one of its type parameter's associated types to satisfy a
  trait or typeset that the type parameter's own bound doesn't declare,
  enforced both at the function's call sites and at `impl`-declaration
  time.
- Std: `size_of`, `memory_grow`, and other `wasm`-module intrinsics are
  now `pub`, since example code calls them directly and the new privacy
  enforcement would otherwise reject that.

### Fixed

- A `break`/`continue` exiting a loop could bypass that loop's own
  "commit loop-carried locals" tail code, silently losing a mutation
  made immediately before the early exit — found while testing `match`
  inside a loop, but not itself match-specific.
- Sea-of-nodes builder: a dense (`br_table`) match's per-slot arm-value
  merge left dead `Phi` nodes for every divergent slot but the last, and
  panicked outright if a divergent slot's value was a struct instead of
  a scalar. A sparse match lowered through the if/else-chain path also
  recursed one Rust call-stack frame per arm, bounding realistic arm
  counts far below what dense matches could already handle; that path is
  now iterative.

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
