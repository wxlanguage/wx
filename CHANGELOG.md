# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning currently applies to the whole project at once (the compiler,
CLI, and LSP are released in lockstep) rather than per-crate. Editor
integrations (e.g. [wxlanguage/vscode](https://github.com/wxlanguage/vscode))
live in their own repos with independent versioning.

## [0.5.0] - 2026-09-05

This release reshapes how a wx program is organized: every compilation is
now rooted at a `wx.json` package, privacy is genuinely enforced, and
pointers distinguish exclusive from shared access. Nearly every existing
program needs edits — see the Changed section, which is ordered roughly by
how much work each item is likely to cost you.

### Changed

- **Breaking:** `wx.json` is now required, and every subcommand operates on
  a project directory rather than a single file. `wx compile` is renamed
  `wx build`, and the anonymous single-file compilation path is gone.

  ```jsonc
  {
    "type": "bin",          // "bin" | "lib"
    "entry": "main.wx",     // required, relative to this manifest
    "dependencies": { "math": { "type": "local", "path": "../math" } },
    "format": { "max_line_width": 80, "indent_width": 4, "trailing_comma": true }
  }
  ```

  `wx format` is redesigned around the same model: a directory positional,
  `--files a.wx,b.wx` to restrict to named files, and `--check` for a
  diff-free exit-code check. Formatting settings now come from the
  package's own `wx.json`, so `wx format` and the editor's format-on-save
  produce identical bytes.
- **Breaking:** the `module` keyword is now `mod`. `module foo;` /
  `module foo { }` become `mod foo;` / `mod foo { }`.
- **Breaking:** pointer mutability is now a distinction between *exclusive*
  and *shared* access, replacing `*mut T`/bare `*T`:

  ```
  // before          after
  *mut T             *T      // exclusive
  *T                 &T      // shared, read-only
  []mut T            *[T]
  []T                &[T]
  [N]T               &[T; N] // or *[T; N]
  ```

  There is no bare `[]T` any more — slices and arrays always carry a
  sigil. `.&mut` is removed; `.&` always yields a shared reference.
- **Breaking:** a module's children now resolve under the module's *own*
  name, not its file's directory. `a.wx` declaring `mod shared;` resolves
  `a/shared.wx`, where it previously resolved `shared.wx` as a plain
  sibling of `a.wx`. This matches Rust, and makes it impossible for two
  files declaring the same child name to silently collide — previously
  only the first discoverer's declaration bound anything. `math.wx` and
  `math/mod.wx` are now fully interchangeable for where `math`'s children
  live.
- **Breaking:** an enum variant now requires an explicit anchor value
  before auto-increment is legal (`E1071`). This closes a silent
  collision: `enum Ordering { Less, Equal = 0, Greater = 1 }` previously
  gave `Less` and `Equal` both the value 0.
- **Breaking:** struct field privacy is now enforced (`E1076`). A field
  without `pub` is visible to its declaring module and that module's
  descendants, and nowhere else — matching the rule every other item
  already followed on paper.
- **Breaking:** a plain `use` no longer re-exports publicly. Previously
  every `use` behaved as `pub use`, because a re-export's symbol entry was
  indistinguishable from a direct declaration's. Relatedly, a private
  `mod foo;` is now actually inaccessible from outside its parent and
  descendants for the first time — its `pub` span was always parsed, just
  never read.
- **Breaking:** inherent `impl` blocks are restricted to the package that
  defines the type (`E1077`). `impl f32 { }` in user code is now an error;
  define a trait and implement that, or wrap the type in your own struct.
- **Breaking:** `export { .. }` blocks now enforce three invariants — one
  block per package (`E1072`), at the binary root (`E1073`), and never in
  a library (`E1074`).
- **Breaking:** every package now owns a root namespace, so a transitive
  dependency is no longer nameable from anywhere in the program — only the
  package that declared it can see it. Two related manifest errors: naming
  the same package under two keys (`E2005`), and declaring `std` as an
  explicit dependency (`E2004`). A package no longer has a name of its
  own; it is known by the key its dependent declared it under.
- Name collisions between a `wx.json` dependency, an `import "..." { }`
  block, and a `mod` declaration are now reported as `E1000` instead of
  one silently replacing another. The worst case was a file-declared
  `mod std;`, which replaced the real stdlib binding outright and
  surfaced as a cascade of unrelated type errors with nothing pointing at
  the cause.

### Added

- `std` is now an implicit prelude — `use std::*;` is no longer needed in
  any module. It resolves as a final tier, after your own symbols, globs
  and the parent walk, so a name std defines can never shadow one you
  wrote or imported, and adding an item to the standard library cannot
  break a program that already compiles.
- Operator overloading through trait dispatch: `Add`, `Sub`, `Mul`,
  `Div`, `Rem`, `Neg`, plus the bitwise `BitAnd`, `BitOr`, `BitXor`,
  `Shl`, `Shr` and `BitNot`. Primitive impls are `#[inline]`, so
  monomorphized code still emits native `i32.add` and friends with no call
  overhead. Generic (`T: Add`) and typeset-bounded (`Mem::Size`) operands
  defer dispatch to monomorphization. Comparison operators are not
  overloadable yet.
- Compound assignment for every overloadable operator: `+=`, `-=`, `*=`,
  `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`.
- `local` pattern destructuring — tuples, struct patterns, `_`, arbitrary
  nesting, and `..` to opt out of exhaustiveness:

  ```
  local (quotient, remainder) = divmod(a, b);
  local Point::{ x, y } = origin();
  local (a, (b, _)) = nested();
  ```

  This is not sugar: wx has no `t.0`, so destructuring is the only way to
  read a tuple element. The scrutinee is evaluated exactly once.
- `crate` and `super` path keywords, including chaining
  (`super::super::x`). `self` is not implemented.
- Nested `use` trees — groups, globs and aliases:

  ```
  use math::{trig::{sin, cos}, ops::*};
  use math::add as plus;
  ```
- Primitive types are now real items rather than a hardcoded name match,
  so go-to-definition, hover and find-references work on `i32`, `bool`,
  `char` and the rest.
- Language server: the server now registers its own file watchers, so
  edits to `wx.json` and to files you don't have open are picked up even
  in editors that have no file-watching API of their own. A `.wx` file
  with no `wx.json` ancestor gets a visible "unlinked file" hint instead
  of silently doing nothing. Completions trigger on `::`, and no longer
  fire on a lone `:`.
- Formatter: comments are now placed by source position. A comment that
  trails code stays on its line instead of migrating down and appearing to
  document the *next* item.
- Std: `ptr::align_up`, `f32::sqrt`/`f64::sqrt`, and integer/float
  conversion methods (`to_f32`, `to_i32`, `promote`, `demote`, and the
  rest).
- New diagnostics: `E0011`, `E0015`, `E1070`-`E1081`, and
  `E2002`-`E2006`.

### Fixed

- Two sequential `#[inline]` calls at the same site silently clobbered
  each other's staged values, because each inlined call got its own scope
  in a flat local-offset range that assumes sibling scopes are mutually
  exclusive at runtime. Confirmed against wasmtime: `a + (b - a) * t`
  trapped, and `calc(a, b, c, d) { (a + b) + (c + d) }` returned a wrong
  result.
- Scheduler: a pure value read inside a branch and again later in the same
  containing block could be placed after its first reader, aliasing an
  unrelated local once locals were coalesced. Separately,
  `compute_block_depths` assumed a block's parent always has a lower
  index, which `switch`'s synthetic wrapper blocks violate.
- Four trait-conformance bugs, including a spurious signature mismatch
  stacked on top of the error that already explained it, and a false match
  when the same type is reached under two different generic environments
  (`(T,)` where `T` means `i32` on one side and a free parameter on the
  other).
- Signature cycles are now reported with the whole chain
  (`` `A` -> `B` -> `C` -> `A` ``) rather than depending on which caller
  happened to notice. Cycles reached through value position — e.g.
  `const A = B; const B = A;` — previously panicked or produced a
  diagnostic with no labels at all.
- Integer literals are now held as `u64` rather than `i64`, fixing
  `i8::MIN`-class negation boundary checks against the wrong bound, and
  constant folding of `/` and `%` using signed semantics regardless of the
  operand type's actual signedness.
- An already-reported error no longer cascades: a failed pointer deref no
  longer reports "type `{unknown}` is not a pointer" on a binding that was
  already diagnosed, `p.* += x` no longer reports a spurious `E1013`, and
  a callee that fails to resolve no longer discards its argument list
  along with it.
- `E0001` (unknown token) was defined but never constructed, so a stray
  character like `@` surfaced as a misleading cascade of unrelated parse
  errors pointing at whatever followed it.
- `#[tag = ".."]` was silently ignored on `global`, `enum` and `memory`
  declarations.
- `local t = (1, 2);` — a plain binding with no destructuring — passed
  type checking with no diagnostics and then crashed the compiler. It now
  reports `E1002`.
- Formatter: comments were silently *deleted* in five places — between
  struct fields, between enum variants, between match arms, after the last
  top-level item, and before the first item in a `mod` body. Blank lines
  no longer carry the previous line's indentation, and an
  already-formatted file now reports no edits at all, so format-on-save
  stops dirtying the buffer.
- Formatter: `pub` and attributes were dropped entirely from constants in
  `impl` blocks, so formatting `impl f32 { pub const PI }` silently
  removed its `pub`.
- Language server: a path that isn't valid UTF-8 crashed the analysis task
  and left the server connected but permanently dead for the rest of the
  session. A `todo!()` reached through qualified-bound resolution could do
  the same.
- Language server: every keystroke republished every file's diagnostics,
  because the refresh cleared the state it diffs against before
  re-analysing.
- Language server: editing a file in an open dependency package could wipe
  its dependent's entire cache. Go-to-definition into `std` was broken by
  a malformed URI, and hover, go-to-definition and semantic highlighting
  did not work on tokens from a dependency package.
- Language server: renaming a symbol imported via `use` emitted two
  overlapping edits at a single range.

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
