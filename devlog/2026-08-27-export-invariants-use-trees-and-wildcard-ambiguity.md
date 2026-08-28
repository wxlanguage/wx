# Export-block invariants, `use` trees, export reach, and wildcard ambiguity

Worked through Parts 0–4 of
[`notes/export-resolution-and-use-trees-plan.md`](../notes/export-resolution-and-use-trees-plan.md),
then a delegated code-quality review pass over the result. Part 5 is the only
part of that plan left unstarted.

The session began by reviewing the plan itself against the code rather than
taking it on faith, which turned up six things it got wrong — recorded inline
in the plan doc and summarised under "Where the plan was wrong" below.

809 → **846** `wx-compiler` tests, plus 31 `wx-fmt` and 52 `wx-lsp`.

## Part 1 — the export block's invariants

Three rules, none previously enforced: at most one block, at the binary
package's entry file, never in a library.

**The substance was a data-model change, not the checks.** `tir.exports:
HashMap<SymbolU32, ExportItem>` became `tir.export_block:
Option<ExportBlock>` with the resolved items *inside* the block. A separate
"have we seen a block?" marker beside a TIR-level map would have been two
things to keep in agreement; one `Option` answers both questions, so the
check that rejects a second block is a read of the very value that stores the
first block's exports. `build_exports` returns its map instead of writing into
`tir`, and the `AstNodeRef::Export` arm installs the block.

Two rules merged into one comparison. The plan listed "at the package root"
and "not in a library" as separate checks, but a block in a *dependency* is
caught by the position check too, since `namespace !=
package_namespaces[root_package]` covers a submodule file, an inline `mod
{ .. }`, and another package alike. What remains genuinely separate is the
root package itself being a library — different fix (delete the block, or
change the manifest), so a different code.

**Rejections must not claim the slot.** All three checks `return` before
assigning the `Option`. If a misplaced block took it on the way out, the entry
file's legitimate block would be reported as a duplicate of a block that was
itself rejected, and the real ABI would silently lose its exports. Pinned by
`test_misplaced_export_block_does_not_claim_the_export_slot`.

New: `E1072` `DuplicateExportBlock`, `E1073` `ExportBlockNotAtRoot`, `E1074`
`LibraryCannotExport`; `Builder.root_package` (`graph.root_package` wasn't
reachable from the builder at all); `keyword_span` on `ast::Item::Export`
(`pre_scan_item` gets the bare `&ast::Item` with the `Spanned` wrapper
stripped, and an empty `export { }` has no entry span to point at);
`TestCase::new_library`, since every existing helper went through
`load_binary` and no rule depending on the root package's kind was otherwise
reachable.

Verified beforehand that nothing in-tree violated any of the three: every
`.wx` file has at most one top-level `export`, each is its manifest's declared
entry, and `examples/pow` (the one `"type": "lib"` that could have tripped it)
has no block. `doom/` has three files with a block each but no `wx.json`, so
it isn't a package at all.

## Part 2 — `use` trees

`use` went from wildcard-only to a full nested tree: `UseTree::{Glob, Name {
id, name, alias }, Path { segment, rest }, Group}`, recursive-descent parser,
recursive formatter.

**The `DefId` lives on the `Name` leaf, not the `use` item.** Three mechanisms
are keyed per-`DefId` — `claim_name_binding` claims one name, `sig_state`
tracks one compute state, `item_lookup` yields one declaration span — so `use
math::{sin, cos};`, which binds two names, needs two of each. Sharing one id
(as the plan proposed) would mean a duplicate on `cos` underlining `sin`.

**`use` leaves are real items.** `tir.use_items: Vec<UseItem>` +
`ItemIndex::Use(u32)`. This exists to *restore* an invariant rather than
except it: `SymbolKind::Pending(def_id)` universally means "a stub for
`def_id` is already materialized, reachable through `item_lookup`", which is
what lets `get_symbol_location` produce a declaration span for a name whose
signature isn't computed yet. A leaf binding a name without a stub is a
`Pending` with nothing behind it — and `claim_name_binding` indexes
`item_lookup[&def_id]` directly, so `use a::foo;` alongside `fn foo` would
have *panicked* instead of reporting. Two rejected alternatives: a side map
(turns the invariant into "`item_lookup` *or* `use_spans`", enforced nowhere)
and a distinct `SymbolKind::PendingUse` (29 `Pending` sites to audit, of which
only 5 are compiler-checked `match` arms — 10 are `matches!` guards and 2 are
`filter` predicates that would fail silently).

**Provisional claims.** A leaf claims *both* symbol namespaces at prescan,
because which one its target occupies isn't knowable until Phase 2 — so one of
the two claims is routinely spurious, and prescan is the wrong place to judge
any collision involving an import. `use math::add;` (value-only) next to a
local `struct add` is legal, and so is `use a::foo;` next to `use b::foo;` when
they occupy different namespaces. So `claim_use_binding` reports **nothing**:
a real declaration keeps the slot, a rival import takes it (last wins,
provisionally), and `claim_name_binding` silently displaces a provisional
claim rather than reporting it. The leaf that lost re-checks in Phase 2 —
forcing any rival import first, so the slot settles into either a real binding
or nothing — and reports only once it knows it wants the name. All four
permutations and both source orderings verified to give exactly one diagnostic
or none.

**Value-position `Pending` forcing was missing entirely, and it was a
pre-existing crash.** Type position always forced a `Pending` through
`ensure_signature`; value position never did, so any value reference resolved
before its target's signature hit the `unreachable!` in
`resolve_symbol_kind_to_expression`. Two legal programs used to panic:
`const A: i32 = B; const B: i32 = 1;` (no `use` involved — this predates the
whole feature) and a `use` written below a reference to what it imports. A
self-referential `const A: i32 = A;` now reports `CyclicTypeDependency`
instead of crashing.

Also landed here, ahead of Part 4 needing it: `wildcard_imports:
Vec<NamespaceIndex>` → `Vec<WildcardImport { namespace, span }>`. The push
site is inside this same prescan walk, and the prefix accumulator that gives
named leaves their path is what gives a glob its `x::*` span. For a glob
nested in a group the span covers only `b::*`, never `a::{b::*`, which
wouldn't be a contiguous range of source.

## Part 3 — export reach

`build_exports` now resolves entries through `resolve_pending_global_symbol`
(the scope chain) instead of `resolve_pending_namespace_symbol` (the package
root's own map). Two call sites, no new helper — the plan's guess that
`resolve_pending_global_symbol` already did exactly this was right.

**But it fixes less than the plan claimed.** Verified by reverting the swap:
`use math::add; export { add }` and the aliased form **pass without it**. Part
2 already fixed them as a side effect, because a named `use` leaf installs its
resolved symbol into the namespace it was written in — which for an entry-file
`use` *is* the package root's `symbols` map, exactly where the old lookup was
already looking. Globs are the only imports living outside that map
(`wildcard_imports`), so glob reach is Part 3's entire contribution.

An end-to-end `codegen/tests.rs` wasmtime case compiles a glob-imported
function exported under an alias, calls it through the real ABI, and asserts
the internal name doesn't leak into the export section — resolving an export
is not the same as emitting one. Needed a `new_multi_file` constructor on the
codegen `TestCase`, which only had a single-file one.

## Part 4 — wildcard ambiguity

`lookup_global_symbol` returned the **first** wildcard match in
`use`-statement order and never looked for a second, so `use a::*; use b::*;`
with a colliding `foo` silently bound `a::foo`. Part 3 made that reachable
from the export block, where it would have baked one of two `foo`s into the
module ABI.

Detection lives in `lookup_scope_chain`, returning
`ScopeLookup::{NotFound, Found(SymbolKind), Ambiguous(Box<[(SymbolKind,
SourceSpan)]>)}`. The ambiguous case **carries its own evidence** — every
candidate paired with the glob that supplied it. The first draft returned
`(Option<SymbolKind>, bool)` and needed a second `wildcard_candidates` walk to
recover the labels, duplicating the visibility rules; making the result carry
the candidates collapsed both. The candidate list only starts allocating once
a second *distinct* item appears, so the ordinary path allocates nothing.
`lookup_global_symbol` survives as a thin `.symbol()` wrapper so the sites
asking "is this still my own `Pending`" — a question ambiguity can't affect —
are untouched.

`SymbolKind` gained `PartialEq`/`Eq`: every variant is an index into a TIR
collection, so equality is item identity, which is what makes "the same item
through two globs is not ambiguous" expressible. Reachable in practice — two
modules that each `pub use base::shared;` store the identical `Function {
func_index }`. Mutation-tested: disabling that arm fails exactly one test.

Two semantics worth keeping straight, both pinned by tests:

- **Ambiguity is per scope level.** Two globs on one namespace conflict; a
  glob here and a glob on the parent is ordinary shadowing, so the walk stops
  at the first level that resolves.
- **A namespace's own symbols win outright**, which is what makes the `help:`
  text honest — `use x::foo;` really does disambiguate.

Reported from six reference sites via `lookup_global_symbol_reporting`, and
deliberately *not* from the `Pending` identity guard or prescan's silent glob
walk. The plan's placement — report only from the `&mut self` forcing wrappers
— would have covered type position and missed `foo()`, which is rustc's own
E0659 example, because value identifiers go through `&self` code that can't
push diagnostics.

Rendering is flattened, as predicted: codespan-reporting has no nested
sub-diagnostics, so rustc's per-candidate `note:` blocks become secondary
labels on one diagnostic (the `AmbiguousTraitMember` shape).

```
error[E1075]: `FOO` is ambiguous
4 │ use x::*;
  │     ---- `FOO` could refer to the constant imported here
5 │ use y::*;
  │     ---- `FOO` could also refer to the constant imported here
7 │ fn main() -> i32 { FOO }
  │                    ^^^ ambiguous name
  = ambiguous because of multiple glob imports of a name in the same module
  = consider adding an explicit import of `FOO` to disambiguate
```

## Refactor pass

Delegated a code-quality review of the whole change to a subagent (research
only, no edits), then verified its load-bearing claims independently before
acting. Five findings landed:

1. **`resolve_symbol_forcing` walked the scope chain three times per
   identifier**, and the local stack three times — one
   `lookup_global_symbol_reporting` whose result was discarded, then
   `resolve_symbol` twice. It now early-returns for locals and delegates the
   rest to `resolve_pending_global_symbol`. The real defect wasn't the
   walks: the function had a **hand-copied cycle guard**, two independent
   copies of one correctness rule. `resolve_symbol` became dead and was
   deleted.
2. **Two prefix walkers merged into one** (`walk_use_prefix`) returning
   `PrefixWalk::{Resolved, Empty, NotAModule, Unresolved}`. They were the same
   walk differing only in reporting, and returning the outcome lets each
   caller decide — prescan stays silent, Phase 2 reports — with no "should I
   report" flag. This closed a real hole: `use add;` was **silently accepted**,
   because the old `Option` return conflated "resolved", "failed, already
   reported", and "no segments at all".
3. **Prefixes are stored and walked once.** `TIR::use_prefixes:
   Vec<UsePrefix>`, each with `PrefixTarget::{Unwalked, Resolved, Failed}` —
   three states rather than an `Option<NamespaceIndex>`, because "nobody
   walked this yet" and "walked, goes nowhere" need opposite responses.
   Previously every leaf of `use math::{add, sub};` re-walked `math` and
   pushed a byte-identical `SourceSpan` onto the namespace's `accesses`; since
   wx-lsp turns each access into a reference, that gave find-references
   repeats and made **rename emit two overlapping edits at one range**. The
   same restructure removed the duplicate `path` allocation per leaf.
   A rejected first draft used `prefix_owner: u32` + `target:
   Option<NamespaceIndex>` on `UseItem` — that encodes the owner/non-owner
   roles in *values*, so every reader branches and unwraps; giving the prefix
   its own identity removes the roles entirely.
4. **A second, unrelated double-record**: `record_type_kind_access` fired once
   per bound namespace, so an item occupying both (a `memory` does) recorded
   its access twice.
5. Small ones: `withdraw_use_claim`'s `only: Option<SymbolNamespace>` (a
   parameter driving a `continue` inside a two-element loop) split into
   singular/plural; a `reported` flag redundant with its own `break`; an
   `unreachable!()` created by testing a `SymbolKind` then re-destructuring
   it; the unread `ExportBlock.id`; and a doc comment of mine claiming the
   group's comma spans were needed by the formatter, which never reads them.

Measured and **not** changed: the Part 4 ambiguity scan. The glob loop is
reached on ~23 scope levels across an entire build and examines ~9 glob edges
total, because almost every lookup hits the namespace's own `symbols` map and
returns first.

## Where the plan was wrong

Worth recording, since the plan doc is the artifact a future session will read
first (all six are corrected in place there):

1. `get_symbol_location` panics on a `use`-leaf `Pending` — the two cases the
   plan called "free" (`use a::foo; use b::foo;` and `use a::foo;` + `fn foo`)
   would have crashed.
2. Claiming both namespaces at prescan invents duplicate-definition errors on
   legal code.
3. Value position had no `Pending` forcing at all, and landing on one is
   `unreachable!` — a pre-existing crash the plan didn't know about.
4. Part 4's reporting placement misses rustc's own example.
5. Part 5's table claims `export { Point::len }` is silently mangled; it
   actually emits four confusing parser diagnostics plus a TIR error, and
   `export { add::<i32> }` still exports `add`.
6. Part 3's reach fix only affects globs, not named imports.

## Not finished

- **Part 5** — export entry grammar. `ExportEntry.name` becomes
  `Box<[PathSegment]>` so paths and turbofish are *parsed and then rejected*
  in TIR with messages that name the fix. Unstarted; it's the smallest
  remaining piece, and the `use` recommendation its diagnostic makes is now
  true.
- **`pub use` is parsed and dropped.** `Item::Use.pub_span` is destructured as
  `pub_span: _`, and there's an AST test asserting it parses. Pre-existing, but
  newly load-bearing: now that named leaves install a real `SymbolKind`, `pub
  use` *looks* like it should re-export and silently doesn't.
- **`use *;`** (bare glob, no prefix) is a silent no-op. Deliberate, matching
  how an unresolvable glob has always behaved — but unlike `use add;`, which
  now reports, it's inconsistent.
- **Glob prefixes stay silent on an unresolvable prefix**, by necessity
  (prescan runs before other files are scanned). So `use nope::thing;` errors
  while `use nope::*;` doesn't.
- **Prescan glob resolution is order-dependent within a file** — `use
  math::*;` written above an inline `mod math { }` silently resolves nothing.
- **The impl-dispatch demand hole** (from the plan's "Not doing"): impl blocks
  have no demandable name, so `trait_impl_dispatch`/`inherent_impl_dispatch`
  are populated only as a side effect of the Phase 2 sweep reaching each impl
  block. Nothing here needed it; still worth recording as a limitation.
- **World / WASI conformance checking** — the export block is now the right
  place for it (a `check_world_conformance()` sibling to
  `check_trait_conformance()` in Phase 3.5), still out of scope.

## Pre-existing, unrelated, still broken

- `scale_pow2` / `sin` / `cos` tests fail from the wip stdlib math port
  (`c00d6db`) and **abort the test harness** if not skipped — every run in
  this session used `--skip scale_pow2 --skip sin --skip cos`.
- `examples/vec` and `examples/raycaster` fail `wx check` with 7 and 8 errors
  (generic pointer type mismatches, `A::M::*u8` vs `A::M::*T`). Verified
  identical at `c00d6db` in a clean worktree.
- `cargo fmt --check` reports drift at `vfs/tests.rs:208` and `:289`. Also
  pre-existing; deliberately left alone so it doesn't ride along in this diff.
- `crates/wx-compiler/std/ops.wx` is untracked and referenced by nothing —
  an orphan from the previous session, left unstaged.
