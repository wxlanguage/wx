# Module/dependency/import name collisions, and a Phase 1 redesign to fix them properly

Follow-up session to
[`2026-08-25-package-namespaces-and-typeformatter-analysis.md`](2026-08-25-package-namespaces-and-typeformatter-analysis.md),
picking up its first listed follow-up: `ensure_module`'s duplicate rule. What
started as a one-branch fix (diagnose instead of silently merge) turned into a
restructuring of how TIR builds namespaces from vfs's module tree, because the
narrow fix depended on a mutation pattern that turned out to be avoidable
entirely rather than just made safe.

## Summary

Three independent name-owning mechanisms — a `wx.json` dependency, an
`import "..." { }` block, and a user `module foo` — could each silently steal
another's binding with zero diagnostic. All three now report `E1000`
(`DuplicateDefinition`) instead. Getting there required splitting `TIR::build`'s
Phase 1 into two passes so every module namespace is created exactly once, with
every field set at construction — no more "create now, patch `pub_span` in
later if some other caller got there first." Also fixed: vfs's
`ModuleDeclaration` scan was flat, so a `module foo;` nested inside an inline
`module { }` block was invisible to it rather than diagnosed (`E2006`, new).

828 `wx-compiler` + 53 `wx-lsp` passing (up from 822 + 53 at the start of this
session — new regression tests, no regressions). The three
`sin`/`cos`/`scale_pow2` failures from the previous session are unrelated and
still failing (`std/math` submodule in progress).

## The bug

`ensure_module` treated *any* hit on an existing `SymbolKind::Module` the same
way: reuse silently, regardless of what created it. That's correct for the one
legitimate case — a module split across two files (its own content-file and
its `module foo;` declaration) converging on one namespace — but a hit on a
`Package` (dependency) or `Import` binding is a genuine collision, not
something to merge into.

Confirmed empirically before fixing: a package with `module std { pub fn
my_helper() {} }` compiled clean, with `my_helper` registered *inside the real
stdlib's own namespace* — every dependent package could now see it. Worse, the
file-declaration form (`module std;`, pointing at a separate file) didn't even
merge — it *replaced* the `std` binding outright, so `use std::*;` and every
other `std::x` reference in the file silently resolved against the user's file
instead of the real stdlib, surfacing as a cascade of unrelated `E1021
undeclared type` / `E1005 cannot coerce` errors with nothing pointing at the
actual cause.

## Why the fix couldn't stay inside `ensure_module`

The obvious fix — branch on `ModuleDeclarationKind` before reusing — worked,
but sitting right next to it was a pre-existing mutation:

```rust
if let ModuleDeclarationKind::Module(decl_idx) = ... {
    if decl.pub_span.is_none() { decl.pub_span = pub_span; }
}
```

This existed because two independent callers could both try to establish the
same file's namespace, in either order: the Phase-1 loop's `ensure_module_path`
(walking every file's full path from the package root, always passing
`pub_span: None` — it has no declaration to read) and `pre_scan_item`'s
`ModuleDeclaration` arm (which has the real `pub_span`, but might run before or
after the other). The `is_none()` check was pure defensive code against not
knowing which one got there first.

Root cause, traced further down: `Loader::load_module` (vfs) already reads the
real `pub_span` off `ast::Item::ModuleDeclaration` while scanning for children
— and throws it away, keeping only `name` (`vfs/mod.rs`'s old `child_decls: Box<[Spanned<SymbolU32>]>`). `ensure_module_path` wasn't choosing to pass
`None`; it structurally couldn't have anything else.

### The fix: one creator per namespace, not two racing to fill in the same struct

- **vfs**: new `ModuleDeclaration { parent: ModuleId, name: Spanned<SymbolU32>,
  pub_span: Option<TextSpan> }`, replacing `SourceModule`'s previous
  `parent: Option<ModuleId>` / `name: Option<SymbolU32>` (independent options
  that always existed or didn't *together* — now enforced by one type instead
  of a comment). Captured once, in `Loader::load_module`, at the only site that
  ever has the real data.
- **TIR**: `TIR::build`'s Phase 1 split into 1a and 1b. 1a walks
  `source_modules` and creates every file's namespace directly from its
  `SourceModule.declaration` — safe because `ModuleId`s are assigned in push
  order and vfs always pushes a parent before loading any child, so a child's
  parent namespace is always already in `file_namespaces` by the time the
  child is reached. Every `ModuleDecl` field is set exactly once, here. 1b is
  the unchanged `pre_scan_item` walk, now a pure reader of `file_namespaces`.
- `pre_scan_item`'s `ModuleDeclaration` arm — previously a call to
  `ensure_module` whose return value was discarded, existing purely for the
  `pub_span` side effect — is now a no-op. Phase 1a already did the job before
  any file's items are scanned.
- `ensure_module` is left with exactly one caller: inline `module foo { }`
  blocks, the one case vfs never sees (it only scans `ast::Item::ModuleDeclaration`, not inline `Module` blocks — see the `E2006` fix below). Its
  own "found" branch is now unconditionally a collision — Phase 1a owns the
  only legitimate convergence case, so nothing reaching `ensure_module` has a
  reason to already exist.

New shared helper, used by all three of `ensure_module`, Phase 1a, and (see
below) the `Import` arm:

```rust
fn check_module_collision(&mut self, file_id: FileId, namespace: NamespaceIndex,
                           name: Spanned<SymbolU32>) -> Option<NamespaceIndex>
```

Direct-scope lookup only (not `lookup_global_symbol`'s ancestor walk) — reuse
across files is only ever legitimate at the exact declaring level; an
ancestor's same-named module is unrelated. Diagnoses and returns the existing
namespace on a hit; both `ensure_module` and Phase 1a recover by handing that
back rather than creating something new (the compilation already has an error
and `wx-cli` aborts before `MIR::build`, so what the colliding declaration's
own contents end up merged into doesn't matter downstream).

## Two more collision sites, found by testing the fix rather than trusting it

Both pre-existed the `ensure_module` bug and are the same root pattern —
`insert_symbol` (unconditional `HashMap::insert`) used somewhere a real name
could already be claimed:

- **Phase 1a itself.** Its `create_module_namespace` call was deliberately
  unconditional (see above) — which also meant zero collision-checking for the
  file-declared `module std;` case. This is the one that actually corrupted
  compilation rather than just silently merging (see "The bug" above). Fixed
  by calling `check_module_collision` before creating.
- **`pre_scan_item`'s `Import` arm** (`import "..." as name { }`) — pre-existing,
  unrelated to this session's earlier work, but the identical shape:
  `insert_symbol` with no check. Fixed the same way, with one extra wrinkle:
  the fallback identifier used when an alias is missing (`external_name`, the
  unescaped *import-path string* — e.g. `"wasi_snapshot_preview1"`, not
  something the user ever wrote as an identifier) is **not** run through the
  collision check, and is no longer even bound into the `Type` namespace at
  all. Binding an unreachable, non-identifier string was pre-existing
  behavior, presumably to keep `namespace_idx`/`ImportDecl` non-optional for
  downstream code — that part is preserved (the namespace and decl are still
  created, `entries` still register normally), but the collision check and the
  `Type`-namespace binding both now happen only for a real, user-written alias.
  Missing alias and colliding alias recover identically: skip only the binding,
  register everything else.

## `E2006`: nested `module foo;` inside an inline block

Separate, smaller finding along the way: `Loader::load_module`'s scan for
child declarations only looks at a file's *top-level* `ast.items`, not
recursively. A `module extra;` written inside an inline `module utils { }`
block was invisible to vfs — never loaded, never diagnosed, just silently
absent, surfacing later as a generic "undeclared" error with no indication of
why.

Rust supports exactly this shape (`mod utils { mod extra; }` resolves via a
directory segment accumulated per inline nesting level, even though `utils`
itself has no file) — real precedent, not a made-up feature. Deliberately
**not** replicated here: where a `module foo;` file lives should be readable
from that one line, not require walking up through however many inline
wrappers enclose it. Chosen explicitly as a simpler, stricter alternative to
Rust's rule, not as a missing feature.

Also would have conflicted with the Phase 1a/1b split above in a real way, not
just a style preference: Phase 1a needs a file-backed declaration's *namespace*
parent to exist before any item is scanned, but an inline block's namespace
isn't created until `pre_scan_item` (Phase 1b) walks into it — so nesting a
file declaration inside one would need Phase 1a to depend on something Phase
1b hasn't produced yet.

Fixed as detection, not resolution: `Loader::diagnose_nested_module_declarations`
recurses into `Item::Module` blocks (the only item kind that nests further
`Item`s) purely to report `E2006` on anything found there — kept fully
separate from the existing flat `child_decls` scan rather than merged into one
dual-purpose function with a depth counter, so the common path stays exactly
as simple as it was.

## A module's children now resolve under its own name, not its file's directory

Found while trying to write a regression test for a "diamond" case (two
sibling files, `a.wx`/`b.wx`, both declaring `module shared;`) — the repro
itself turned out to be ill-formed, and fixing *that* is a better fix than
patching the dedup race it seemed to expose.

`resolve_child_module_path` used to search relative to
`self.modules[parent_module_id].file_path.parent()` — the declaring file's own
*physical* directory. For a plain-sibling file like `a.wx` (living directly in
`src/`, not `src/a/mod.wx`), that directory is `src/` — the same directory
`main.wx` itself lives in. So `a.wx` declaring `module shared;` never actually
nested `shared` under `a` at all; it resolved to `src/shared.wx`, a plain
sibling of `main.wx`, `a.wx`, and `b.wx` alike, with no more claim to that name
than any of them. Rust's actual rule (confirmed against its own diagnostic,
`E0583`, which suggests creating `.../a/shared.rs`) always grants a module its
own directory per path segment — `a.rs` included — regardless of whether `a`
itself is file-backed via a plain sibling or `a/mod.rs`.

Fixed by threading an accumulated `owned_dir: AbsolutePath` through
`Loader::load_module` and `resolve_child_module_path`, replacing the
file-path-derived lookup entirely. The root's `owned_dir` is its entry file's
own directory (unchanged); every child's `owned_dir` is
`<parent's owned_dir>/<child's own name>`, computed the same way regardless of
which form resolved the child's own file. This makes `math.wx` and
`math/mod.wx` fully interchangeable for what directory `math`'s own children
live in (`src/math/` either way) — matching Rust's `foo.rs`/`foo/mod.rs`
equivalence — and makes the "diamond" impossible by construction rather than
by restriction: `a`'s and `b`'s `shared` now resolve under `src/a/` and
`src/b/` respectively, genuinely different files, no collision to race. No new
diagnostic code needed — a `module shared;` that doesn't have a real file at
its now-correctly-scoped location is just an ordinary `ModuleFileNotFound`
(`E2000`).

`resolve_child_module_path` also lost its `parent_module_id` parameter (no
`self.modules[..]` lookup needed) and now just takes `owned_dir` directly. No
existing test exercised a non-root file declaring its own children, so nothing
depended on the old, non-accumulating behavior.

## Key findings

- `Spanned<T>` has a manual `impl<T: Copy> Copy for Spanned<T> {}`
  (`ast/mod.rs:1049`) alongside its `#[derive(Clone)]` — easy to miss by only
  checking the derive line. This is why `Spanned<SymbolU32>` values move
  freely by copy throughout this change with no explicit `.clone()` needed.
- `source_modules`' `(package_graph, source_module)` tuple pairing was
  redundant: `SourceModule.package_id` already indexes `builder.packages`/
  `TIR.package_namespaces` directly, same as `ModuleId` indexes
  `package_graph.modules`. Simplified to `Vec<&SourceModule>`.
- `SourceModule.id: ModuleId` was dead — its only reader was
  `module_symbol_path`, deleted along with it (that function is gone entirely;
  Phase 1a made it redundant).
- `ModuleId`s are assigned in strict push order, and a parent's `ModuleId` is
  therefore always numerically less than any of its children's — not just an
  incidental property of iteration order, a structural guarantee from how
  `Loader::load_module` recurses (parent pushed before any child is loaded).
  This is what makes Phase 1a's single ordered pass correct without needing an
  explicit tree walk.

## Follow-ups

- Everything else from the previous devlog's follow-up list is still open:
  tests for the per-package-namespace semantics, `display_type`/`display_bounds`
  infallibility, `pub interner` removal, the two disagreeing `TypeFormatter`
  constructors, `display_kind`'s placement, and the `wx-lsp` symbol-index/
  completion follow-ups.
