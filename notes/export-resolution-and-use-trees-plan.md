# Export resolution + `use` trees

> Written 2026-08-26. **Parts 0-4 are implemented and green but uncommitted** —
> only Part 5 is unstarted. Line references are against the working tree as of Part 0 and are
> now badly stale; re-grep.
>
> Baseline is now **842** tests in `wx-compiler` plus 31 in `wx-fmt`
> (`cargo test --workspace -- --skip scale_pow2 --skip sin --skip cos`), up from 809.
> `examples/vec` and `examples/raycaster` fail `wx check` with 7 and 8 errors — verified
> identical at `c00d6db` in a clean worktree, so pre-existing and unrelated.

## Context

`export { .. }` was handled by a bespoke "Phase 4" loop in `tir::builder::build` that ran
after every other phase, reading namespace symbols raw. Investigating whether it needed its
own phase turned up three things:

1. It has **no dependency on Phase 3 (bodies) or 3.5** — only on Phase 2 having installed
   resolved `SymbolKind`s (prescan installs only `SymbolKind::Pending`).
2. It can ride the Phase 2 sweep as an ordinary `ast_nodes` entry, forcing the names it lists
   through `ensure_signature` like any other reference site. **This is implemented and green.**
3. It must *not* be hoisted ahead of the sweep. `trait_impl_dispatch` / `inherent_impl_dispatch`
   are populated as side effects of each impl block's own `ensure_signature`
   (`register_trait_impl` at `builder.rs:15549`, `builder.rs:6088`) and bound checks read them
   raw (`builder.rs:15688`, `builder.rs:16006`). An impl block has **no name to demand**, so
   nothing can force it on request. At its natural parse position the export block always sits
   after the stdlib, so the question is never asked too early.

Separately, the export block's design intent — *the unique exit point of a binary package* —
is not enforced, and its reach is broken: today **only top-level items of the entry file can be
exported at all**. `use` is wildcard-only (`ast/mod.rs:5691`), and `build_exports` does a direct
namespace lookup that skips `wildcard_imports`, so a submodule item is unexportable by any
spelling.

Outcome: exports resolve in Phase 2; the block's invariants are enforced; `use` gains Rust-style
named/nested imports; and a name that is in scope — by named import or by glob — can be exported.

---

## Part 0 — Done, uncommitted

Verified: 809 tests pass, workspace builds, no fmt drift in touched files.

- `ast::Item::Export` carries a `DefId` (`ast/mod.rs`)
- `AstNodeRef::Export { item }` variant (`tir/builder.rs:362`)
- `pre_scan_item` registers the node **without** `claim_name_binding` — an export block declares
  no name of its own (`builder.rs:5463`)
- `ensure_signature` gained an `Export` arm that derives the package namespace from
  `tir.namespaces[namespace].package` and calls `build_exports`
- `build_exports` resolves each entry via `resolve_pending_namespace_symbol`
  (`builder.rs:3030`) instead of a raw `symbols.get`
- The Phase 4 loop is deleted; `ensure_body`'s `_ => return` covers the new node
- New test: `test_export_block_preceding_the_items_it_names`
- `wx-fmt/src/lib.rs:492` pattern updated for the new field; 6 snapshots re-accepted (pure
  `DefId` shift)

Remaining work below builds on this.

---

## Part 1 — Done, uncommitted

All three invariants were unenforced; all three are now local checks in the
`AstNodeRef::Export` arm. Nothing in the repo violated them beforehand — every `.wx` file has
at most one top-level `export`, each is its manifest's declared entry, and the one library
that could have tripped the rule (`examples/pow`) has no block. `doom/` has three files with a
block each but no `wx.json`, so it isn't a package.

**The data model changed, and that's the substance of it.** `tir.exports:
HashMap<SymbolU32, ExportItem>` became `tir.export_block: Option<ExportBlock>`, with the
resolved items *inside* the block. A separate "have we seen a block?" marker beside a
`TIR`-level map would have been two things to keep in agreement; one `Option` answers both
questions, so the check that rejects a second block is a read of the very value that stores
the first block's exports. `build_exports` now returns its map instead of writing into `tir`,
and the arm installs the block.

Two consumers iterate the optional block directly
(`mir/mod.rs`, `wx-lsp/src/symbol_index.rs`) — no accessor, they're two call sites.

The three checks, in order, each returning **before** the slot is claimed:

| Check | Why this shape |
|---|---|
| Block's own package is a library → `LibraryCannotExport` (E1074) | Also catches every block in a dependency, since a dependency is only ever loaded as a library. "You can't export from here" is the useful thing to say — moving the block wouldn't help. |
| `namespace != tir.package_namespaces[root_package]` → `ExportBlockNotAtRoot` (E1073) | The entry file's top level is the only namespace equal to its package's root, so one comparison rejects both a submodule file and an inline `mod { .. }`. |
| `tir.export_block.is_some()` → `DuplicateExportBlock` (E1072) | Parse-order sweep makes "first" deterministic, because nothing can *demand* an export block — it claims no name, so `ensure_signature` only ever reaches it via the sweep. |

**Order matters, and rejections must not claim the slot.** If a misplaced block took the
`Option` on its way out, the entry file's legitimate block would be reported as a duplicate of
a block that was itself rejected, and the real ABI would silently lose its exports. Pinned by
`test_misplaced_export_block_does_not_claim_the_export_slot`.

Also added: `Builder.root_package` (`graph.root_package` wasn't reachable from the builder at
all); `keyword_span` on `ast::Item::Export`, since `pre_scan_item` receives the bare
`&ast::Item` with the `Spanned` wrapper stripped, and an empty `export { }` has no entry span
to point at; `TestCase::new_library`, because every existing helper goes through
`load_binary` and no rule depending on the root package's kind was otherwise reachable.

Five new tests; 10 TIR snapshots re-accepted for the `export_block` reshape.

---

## Part 2 — Done, uncommitted

`use` is now a full nested tree. `Item::Use { pub_span, tree: Spanned<UseTree> }`, with
`UseTree::{Glob, Name { id, name, alias }, Path { segment, rest }, Group(..)}`.

**The `DefId` lives on the `Name` leaf, not on the item.** A leaf is what binds a name, and
three separate mechanisms are keyed per-`DefId`: `claim_name_binding` claims one name,
`sig_state` tracks one compute state, `item_lookup` yields one declaration span. `use math::{sin,
cos};` binds two names, so it needs two of each — sharing one id would mean a duplicate on `cos`
underlining `sin`.

### Option C: `use` leaves are real items

`tir.use_items: Vec<UseItem>` + `ItemIndex::Use(u32)`, one entry per named leaf. This restores
the invariant that `SymbolKind::Pending(def_id)` *always* has a stub reachable through
`item_lookup`, rather than adding an exception to it — which is what makes
`get_symbol_location`'s `item_lookup[&def_id]` total again. `UseItem` carries the syntactic
prefix, because the prescan walk already builds it to resolve sibling globs; recovering it
later would mean a second walk per leaf.

### Resolution

- **Globs stay at prescan**, unchanged in timing, since `lookup_global_symbol` consults
  `wildcard_imports` throughout Phase 2.
- **Named leaves defer to Phase 2** (`resolve_use_item`), which walks the prefix with real
  diagnostics — `NotANamespace` (E1020, previously declared but unused) for a non-module
  prefix, `UndeclaredIdentifier` for a missing one or a name absent from the target.

### The provisional-claim problem, and how it's handled

A leaf claims *both* symbol namespaces at prescan, because which one its target occupies isn't
knowable yet — so one of the two claims is routinely spurious, and prescan is the wrong place to
judge any collision involving an import. `use math::add;` (value-only) next to a local `struct
add` is legal; so is `use a::foo;` next to `use b::foo;` when they occupy different namespaces.

So `claim_use_binding` reports **nothing**. A real declaration keeps the slot; a rival import
takes it (last one wins, provisionally); `claim_name_binding` silently displaces a provisional
claim rather than reporting it. The leaf that lost re-checks in Phase 2 — forcing any rival
import first, so the slot settles into either a real binding or nothing — and reports the
collision only once it knows it actually wants the name.

### Value-position `Pending` forcing (blocker 3)

Fixed, and it was a **pre-existing crash**, not something `use` introduced. Type position always
forced a `Pending` through `ensure_signature`; value position never did, so any value reference
resolved before its target's signature hit the `unreachable!` in
`resolve_symbol_kind_to_expression`. `resolve_symbol_forcing` is the value-position twin of
`resolve_pending_global_symbol`, cycle guard included. Two legal programs that used to panic now
compile: `const A: i32 = B; const B: i32 = 1;`, and a `use` written below a reference to what it
imports. A self-referential `const A: i32 = A;` reports `CyclicTypeDependency` instead of
crashing.

### Also landed here

`wildcard_imports: Vec<NamespaceIndex>` → `Vec<WildcardImport { namespace, span }>`, ahead of
Part 4 needing it — the push site is inside this same walk, and the prefix accumulator that
gives named leaves their `path` is what gives a glob its `x::*` span. For a glob nested in a
group the span covers only `b::*`, not `a::{b::*`, which wouldn't be contiguous source.

`wx-fmt` formats trees recursively, inline; groups don't break, since a `use`'s length tracks
the path being imported rather than anything in this file.

### Edge cases, verified by probe

`use a::{self, b}` → the parser's existing "cannot use keyword as identifier" plus an
unresolved-name error (rejected, no new code needed). Empty group, trailing comma, and `pub use`
all parse cleanly. `use math::{add, add};` → one duplicate-definition error. `use *;` is a
silent no-op, matching how an unresolvable glob has always behaved.

16 new tests in `tir/tests.rs`, one AST snapshot covering every `use` form, one `wx-fmt`
round-trip test.

---

## Part 3 — Done, uncommitted

`build_exports` now resolves each entry through `resolve_pending_global_symbol` (the scope
chain) instead of `resolve_pending_namespace_symbol` (the package root's own symbol map). The
plan's guess was right: that function already layered forcing over `lookup_global_symbol`, so
it was a two-call-site swap with no new helper.

**But the plan overstated what this fixes.** It claimed both spellings were broken:

```wx
use math::add;        export { add }   // already worked after Part 2
use math::*;          export { add }   // this is what Part 3 fixes
```

Verified by reverting the swap and re-running: `test_export_reaches_a_named_import` and
`..._an_aliased_import` **pass without it**. Part 2 fixed them as a side effect — a named `use`
leaf installs its resolved symbol directly into the namespace it was written in, which for an
entry-file `use` *is* the package root's `symbols` map, exactly where the old direct lookup was
already looking. Only globs live outside that map (in `wildcard_imports`), so the glob case is
Part 3's entire contribution.

Privacy still holds at the boundary: `lookup_global_symbol` visibility-checks wildcard hits, so
`use math::*; export { hidden }` on a non-`pub` item stays unexportable.

Four TIR tests plus an end-to-end `codegen/tests.rs` wasmtime case — a glob-imported function
exported under an alias, called through the real ABI, asserting the internal name does *not*
leak. That one needed a `new_multi_file` constructor on the codegen `TestCase`, which only had
a single-file one; `new` now delegates to it.

---

## Part 4 — Done, uncommitted

`lookup_global_symbol` returned the **first** wildcard match in `use`-statement order and never
looked for a second, so `use a::*; use b::*;` with a colliding `foo` silently bound `a::foo`.
Part 3 made that reachable from the export block, where it would have baked one of two `foo`s
into the module ABI.

### The result type, not a flag

Detection lives in `lookup_scope_chain`, which returns

```rust
enum ScopeLookup {
    NotFound,
    Found(SymbolKind),
    /// Always at least two entries.
    Ambiguous(Box<[(SymbolKind, SourceSpan)]>),
}
```

The ambiguous case **carries its own evidence** — every candidate paired with the glob that
supplied it. That was worth more than it first looks: a boolean flag would have said nothing at
the call site *and* forced a second traversal to recover the candidates for labelling, repeating
the visibility rules. As written, the pass that finds the problem produces the diagnostic data,
and the candidate list only starts allocating once a second distinct item appears, so the
ordinary path allocates nothing.

`lookup_global_symbol` survives as a thin `.symbol()` wrapper, so the sites that ask "is this
still my own `Pending`" — a question ambiguity cannot affect — are untouched.

`SymbolKind` gained `PartialEq`/`Eq`: every variant is an index into a `TIR` collection, so
equality is item identity, which is what makes "the same item through two globs is not
ambiguous" expressible. Mutation-tested — disabling that arm fails
`test_one_item_through_two_globs_is_not_ambiguous` and nothing else.

### Two semantics worth keeping straight

- **Ambiguity is per scope level.** Two globs on one namespace conflict; a glob here and a glob
  on the parent is ordinary shadowing, so the walk stops at the first level that resolves.
- **A namespace's own symbols win outright**, which is what makes the `help:` text true —
  `use x::foo;` really does disambiguate.

### Reporting sites

`lookup_global_symbol_reporting` is what a *reference* site calls. Wired into:
`resolve_pending_global_symbol` (type identifiers and bounds), value identifiers via
`resolve_symbol_forcing`, `GenericApplication`, the turbofish path, the function-reference path,
and `resolve_use_path`. Deliberately **not** wired into the `matches!(.. Pending(d) if d == *id)`
identity guard, nor into prescan's glob prefix walk, which is silent by design.

The plan's original placement — report only from the `&mut self` forcing wrappers — would have
covered type position and missed `foo()`, which is rustc's own E0659 example. Pinned by
`test_ambiguity_is_reported_in_value_position`.

### Rendering

As predicted, flattened: no nested sub-diagnostics, so rustc's per-candidate `note:` blocks
become secondary labels on one diagnostic.

```
error[E1075]: `FOO` is ambiguous
  ┌─ /src/main.wx:7:20
4 │ use x::*;
  │     ---- `FOO` could refer to the constant imported here
5 │ use y::*;
  │     ---- `FOO` could also refer to the constant imported here
7 │ fn main() -> i32 { FOO }
  │                    ^^^ ambiguous name
  = ambiguous because of multiple glob imports of a name in the same module
  = consider adding an explicit import of `FOO` to disambiguate
```

Seven new tests, including one asserting the secondary labels span `x::*` and `y::*` — the
`use` statements, not the definitions.

---

## Part 5 — Export entry grammar: parse, then reject

Both invalid forms are mangled today — **noisily, not silently** (the original table here was
wrong; corrected by probe 2026-08-26, which strengthens the case for parse-then-reject):

| Written | What actually happens today |
|---|---|
| `export { Point::len }` | Four parser diagnostics — `missing separator` and ``expected `identifier`, found `::` ``, twice — plus TIR's ``cannot export `Point` ``. `::len` is dropped. |
| `export { add::<i32> }` | Same parser noise; `::<i32>` dropped, and `add` **is still exported** under its own name. |

`ExportEntry.name` (`ast/mod.rs:1625`) becomes `Box<[PathSegment]>` — reusing the existing
`PathSegment { ident, type_args }` (`ast/mod.rs:1267`) so turbofish is captured rather than
dropped. `parse_export_block` (`ast/mod.rs:4744`) parses a full path; `build_exports` rejects:

- **len > 1** → *"paths are not allowed in export entries — bring `add` into scope with
  `use math::add;` and export it by name"*
- **any `type_args`** → *"type arguments are not allowed in export entries — a wasm export is a
  concrete function; define a wrapper `fn add_i32(a: i32, b: i32) -> i32 { add(a, b) }` and
  export that"*

Reject in TIR rather than the parser: TIR knows what is in scope so the message can name the
fix, the LSP can still resolve the segments for hover/go-to-definition in the error state, and
the grammar stays stable if paths or a world clause are allowed later.

The resulting rule is one sentence: **an export entry is a single bare identifier, optionally
aliased to a string.** Existing checks (generic function, non-exportable item, duplicate export)
are unchanged.

Order matters: Part 2 must land before this, since the path diagnostic recommends `use`.

---

## Not doing

- **Path exports** (`export { foo::bar::baz }`) and **turbofish exports** — rejected by design;
  parse-and-reject only. Both reintroduce a lossy internal-spelling→external-name projection
  that the `alias ?? identifier` rule avoids. No language exports a generic instantiation
  directly into a C-like ABI.
- **`Type::method` exports** — would need `resolve_impl_member` and inherits the impl-dispatch
  ordering hazard.
- **Fixing the impl-dispatch demand hole** — giving impl blocks a demandable name (a prescan map
  from the impl target's head symbol to its `DefId`s) is the real fix, but nothing here needs it.
  Worth recording as a known limitation.
- **World / WASI conformance checking** — the block is now the right place for it (a
  `check_world_conformance()` sibling to `check_trait_conformance()` in Phase 3.5), but out of
  scope.

---

## Verification

```bash
cargo test -p wx-compiler -- --skip scale_pow2 --skip sin --skip cos   # 809 baseline
cargo test --workspace -- --skip scale_pow2 --skip sin --skip cos
cargo insta accept        # snapshots only after reviewing the diff
cargo fmt --check         # vfs/tests.rs:208,289 drift is pre-existing
```

The three `scale_pow2` / `sin` / `cos` failures are pre-existing on this branch (wip stdlib math
port, commit `c00d6db`) and unrelated.

New tests, in `tir/tests.rs` unless noted:

- `use math::add; export { add }` resolves and exports (the reach fix)
- `use math::*; export { add }` resolves and exports (Part 3)
- `use math::add as add_i32; export { add_i32 }` — alias binds the local name
- `use math::{trig::{sin, cos}, ops::*};` — nested group, both leaf kinds in one item
- `use math::private_fn;` → `report_private_item` at the `use` site
- `use nonexistent::thing;` → real diagnostic (today the glob path is silently ignored)
- Two globs with a colliding name → `AmbiguousWildcardImport`, asserting one secondary label per
  glob and that each points at the `use` statement's `x::*` span, not at the definition (Part 4)
- Same item reachable through two globs → **no** ambiguity error
- Explicit `use x::foo;` alongside `use x::*; use y::*;` → no ambiguity (the named import wins,
  since a namespace's own `symbols` map is checked before its wildcards)
- Second export block → error; export block in a submodule → error; library package export →
  error (Part 1)
- `export { Point::len }` → path-not-allowed; `export { add::<i32> }` → type-args-not-allowed
  (Part 5)
- `ast/tests.rs`: parse snapshots for each new `use` form

End-to-end check that the ABI is actually emitted, not just resolved — a `codegen/tests.rs`
wasmtime case exporting an item reached via `use`, asserting the export is callable under its
external name.
