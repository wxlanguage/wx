# Unused-definition warnings in the new TIR

Status as of 2026-11-21, branch `tir-refactor`. Step 1 is implemented for
locals and labels (L3000, L3001, L3002; see "Done") as lints in
`crates/wx-lint`; the rest is a plan.
Companion to `tir-check-pass.md` and `tir-body-checking-plan.md`. Open
questions are at the end.

## Goal

Report, as warnings, what the old checker's end-of-check pass reported
(`tir/builder/mod.rs` in commit `05e2978`, `report_unused_items` and
`report_unused_enum_variants`; local and label warnings are in
`tir/builder/body.rs::report_stack_warnings`), on
the new `Semantics`, at check time (so `wx check` and the LSP get it without
lowering):

| Code | Subject |
| --- | --- |
| L3000 `UnusedVariable` | a local or parameter that is never read |
| L3001 `UnnecessaryMutability` | `mut` on a local that is never assigned |
| `UnusedItem` | a function, constant, global, struct, enum, trait, alias, memory, `use` item |
| `UnusedTypeParam` | a type parameter never used in its declaration |
| `UnusedStructField` | a private field that is never read |
| L3002 `UnusedLabel` | a loop or block label no `break`/`continue` names |
| `UnusedEnumVariant` | a variant never named |

Lints take codes in the L3xxx range. The three implemented ones have codes;
the others get the next free L3 code when they are implemented.

The disconnected legacy TIR source and tests have been removed; recover them
from commit `05e2978` when comparing behavior. In particular, the old field
warning required an initialization and no `Read` or `ReadWrite`, and was
suppressed when the struct itself was unused. The old local warning required
no accesses at all (writes counted as use), and exempted `self` and
underscore-prefixed names. Step 1 below proposes some policy changes rather
than exact parity; settle these explicitly when implementing the pass.

## Where we are

`resolutions.rs` records every written name the compiler resolves, keyed by a
`Site` (`Type`/`Value`/`Label` of a `SourceSpan`) and mapping to a `Reference`:

- a local or field selection carries an `AccessKind` (`Read`, `Write`,
  `ReadWrite`). The access belongs to the named node a use ends at, not to the
  names it is reached through; the root local of a value chain assigned to is
  recorded as written (`check_assignable`), so a local's `Write` means
  assigning needed `mut`. A field through a pointer is a place and does not
  reach it.
- a named argument's label is `Site::Label` with `Reference::Parameter` or a
  `Reference::Field` of `Initialize` (a constructor field label); a `break`'s
  or `continue`'s label is `Site::Label` with `Reference::Label { owner,
  target }`, and the jump keyword itself a `Reference::Break`/`Continue`.
- declarations are not entries: they live in their owning tables
  (`Body::locals`, `Body::targets` with their labels, the per-kind
  declaration arenas).

So "which `use` items are unused" and "which locals are never read" are
inverses of this table, as its module doc says. The table is **not enough for
reachability** (below): it has no owner for a reference, and it misses uses the
checker does not write as names (an operator calls an impl's method).

## Done

`crates/wx-lint/src/unused.rs`, run by `wx_lint::lint` over a finished
`Semantics`, with the package to report on as a parameter; the CLI (`build`,
`check`) and the LSP pass the root package. It runs only when neither the
compilation (parse, package loading) nor checking reported an error or bug
(`CompilationUnit::has_errors`). The compiler does not know the lints: their
codes and names (`unused_variable`, `unnecessary_mutability`, `unused_label`)
belong to `wx_lint::Lint`, and each one's level (`off`, `warn` (default),
`error`) is set in the `lint` section of `wx.json`:

```json
{ "entry": "main.wx", "lint": { "unused_variable": "error" } }
```

An unknown lint name or level makes the section invalid: `wx build`/`check`
stop with an error, and the LSP runs no lints for that package.

- **L3000:** a local or parameter with no `Read` reference. `Write` and
  `ReadWrite` are not reads, as in rustc: a local only assigned is reported as
  "assigned but never read", one only compound-assigned as unused. `_ = x;`
  records a `Read` (tested). No `_`-prefix exemption. Exempt: the receiver
  `self` (a keyword, so never an ordinary local), as rustc does and as the old
  pass did. Trait impl and trait default-method parameters are reported.
- **L3001:** `mut_span` set and no `Write`/`ReadWrite`. Assigning through a
  field (`s.x = ..`) writes the root local, so it counts.
- **L3002:** a labelled target with no `Reference::Label` for it. A jump
  keyword without a label (`break;`) does not use the label; a label named
  only by `continue :l` does.
- Not done: type parameters, fields, items, `use`, variants, reachability.

Over `examples/` and core, the only finding was a real unused local
(`examples/wasi_file_io`); no false positives.

## Two policies

**References-based.** An item is used if any reference names it, from anywhere,
even dead code or itself. This is what the old pass did (`accesses.is_empty()`).

**Reachability-based.** An item is live if it is reachable from the roots
through references. This is rustc's `dead_code`.

| | References | Reachability |
| --- | --- | --- |
| Dead chains (`helper` used only by an unused function) | missed until the caller is deleted | caught at once |
| Self- and mutual recursion | never warned | caught |
| Field read only in dead code | counted as read | not read |
| Needs roots and an owner for each edge | no | yes |
| Incomplete table | silent misses | wrong warnings on live code |
| Operators and trait dispatch | impls exempt wholesale | must model dispatch |

The failure modes are asymmetric: a missing edge makes references-based miss a
warning and reachability warn about working code. That decides the order below.

## Plan

### Step 1: references-based pass

A lint pass in `crates/wx-lint` over the finished `Semantics`. It reads
`Semantics` and returns diagnostics; it builds no bodies.

- **Gate:** run only when checking reported no error or bug. A failed path
  records only its resolved prefix, so an item used only through one would look
  unused, which is noise next to the real error (and the LSP is usually broken
  mid-edit). rustc's lints are gated the same way.
- **Locals and parameters:** for each `Body::locals()` entry, collect its
  references from the table (`Reference::Local { owner, local, access }`).
  L3000 when no reference is a `Read` (decide `ReadWrite`, below); L3001 when
  `mut_span` is set and no reference is `Write` or `ReadWrite`.
- **Labels:** for each `Body::targets` entry with a label, L3002 when no
  `Reference::Label` holds that `TargetIdx`.
- **Type parameters:** `UnusedTypeParam` when no `Reference::TypeParam { env, index }`
  names it. A trait's own `Self` is exempt.
- **Fields:** `UnusedStructField` for a non-`pub` field with no `Reference::Field` of `Read`
  or `ReadWrite` (see "Data gaps": positional patterns).
- **Items:** `UnusedItem`/`UnusedEnumVariant` when nothing references the declaration (a variant is a
  `Const`). `use` items: unused when no `Reference::Item` with
  `Route::Import(item)` names it; a glob is used if any such route points at
  it.
- **Exemptions:** the std package, items of dependency packages (report the
  user's packages only), wasm `import` declarations, anything named by the
  export block, `pub` items of a `lib` package, trait declarations' members,
  trait impls' members. Not `_`-prefixed names, and not trait impls'
  parameters: an unused parameter is dropped in the body, `_ = param;`
  (`notes/binders.md`).

### Step 2: a TIR dependency graph

The existing MIR DCE is the model: `opt/reachability.rs` plus
`mir/references.rs` are a worklist with `roots(f)`, `dependencies(node, f)`
and dense `Vec<bool>` columns per item arena. It cannot be reused (it runs
after lowering, in `wx build`; its nodes are functions, globals, memories and
data, not structs, traits, fields or imports; it never sees an uninstantiated
generic), but its shape transfers.

`tir/reachability.rs`:

```rust
pub(super) struct Reached { /* one Vec<bool> per DeclId arena */ }

pub(super) fn reach(sema: &Semantics) -> Reached {
    // roots, then pop a node and enqueue its dependencies; when the queue
    // drains, mark trait impls whose trait and target are both reached and
    // enqueue their members; repeat until nothing is added
}
```

**Nodes** are `DeclId` (`Struct`, `Enum`, `Trait`, `TypeAlias`, `Function`,
`Const`, `Memory`, `Global`, `AssocType`, and the two impl kinds).

**Roots:** the resolved export block (`Semantics::exports`), a bin's start
function, and in a lib every `pub` item of the root package.

**Edges from a body** are a linear scan of its arenas, as MIR's
`kind.items_mut(..)` scan is: `Body::dependencies(f)` over `kinds` and
`pat_kinds`.

- `ExprKind::{Call, MethodCall, Function}` name a function;
  `AbstractCall`, `AbstractMethodCall` and the four `*CompoundAssign`/
  `*CompoundStore` method nodes name a method (an impl's or a trait's);
  `Const`, `AbstractConst`, `NextDiscriminant` name a constant;
  `Global`, `Memory`, `StructConstructor` name theirs;
  `PatternKind::{Constant, AbstractConstant, Struct}` likewise.
- **The match must be exhaustive** (no `_ => {}`). A missed variant is a false
  "unused" on live code, so a new `ExprKind` must fail to compile here.
- Types are the other source: a struct can be live only through a local's type,
  a function's result or a type argument (`id::<Point>(..)`). `TypeInterner::
  dependencies(ty, f)` maps `Type::Struct`, `Function`, `Const`, the projection's
  trait and the rest to their `DeclId`s and recurses into parts; a shared
  `seen: Vec<bool>` over interned types makes each type be walked once for the
  whole pass. It is run over each body's expression and local types, its
  `GenericArgs`, and every signature's `TypeIndex`es.
- Operators need no special case: `a + b` is already a `MethodCall` of the
  selected impl's function in the body.

**Edges from a declaration** (`Semantics::dependencies(node, f)`, one match on
`DeclId`):

| Node | Edges |
| --- | --- |
| `Function` | signature types and bounds; its body, if it has one |
| `Const` | declared type and body; its parent enum when it is a variant |
| `Global` | its type and its initializer body |
| `Struct`, `Enum` | field types, the repr type |
| `TypeAlias` | its target |
| `Trait` | supertraits and its members' signatures |

**The one non-local rule:** a trait impl is live when its trait and its target
declaration are both reached; then its members are enqueued. This is why `reach`
loops. An inherent impl needs no rule: its members are ordinary function nodes,
reached by a `Call`/`MethodCall`.

**Table-only edges:** a `use` item is in no body, so it stays table-based, and
needs the owner of each reference (below).

### Step 3: switch items to reachability

Replace Step 1's "nothing references it" for items, fields and variants with
`!reached`, keeping locals, labels and type parameters reference-based (they are
local to one body, so a graph adds nothing).

## Data gaps to settle

- **Owner of a table reference.** Needed only for `use` items and for field
  reads counted from live code only. Two ways: containment (the innermost
  declaration whose full item span contains the reference span, which needs each
  declaration's full span, not only its name span, sorted per file), or record
  the current owner when the entry is written. Check what `Declarations` keeps.
- **Positional struct patterns record no field references.** `local P(a, b) = p`
  and `P((a, b))` read every field and write no field name; only the named form
  records `Reference::Field` (`typecheck/patterns.rs`). A body scan sees
  `PatternKind::Struct`, which fixes this under Step 2; under Step 1 it needs the
  pattern to record a read for each field, or the rule to exempt structs
  destructured positionally.
- **Whole-struct uses** (passing or copying a struct by value) read all fields
  but write no names. Follow Rust: they do not count as reading a field.
- **A uniform declaration accessor** from `DeclKey` to file, name span,
  visibility and package, for the diagnostic and for the exemptions.
- **`Body::kinds`, `places`, `pat_kinds`** are private; `Body::dependencies`
  lives in `body.rs`, so no accessor is needed.

## Decisions to settle

- ~~Does `ReadWrite` count as a read for L3000?~~ Decided 2026-11-20: no,
  `Read` only, as in rustc.
- ~~`_`-prefixed names exempt, or only the bare `_`?~~ Decided 2026-11-16
  (`notes/binders.md`): no exemption. `_` is no longer a binder, and a
  parameter's name is part of its function's interface (calls by name, trait
  conformance), so renaming it to silence L3000 would break callers. A local
  or parameter that is never read is warned; the fix is to read it or drop it,
  `_ = x;`, which counts as a read of `x` (`ExprKind::Drop`'s operand is an
  ordinary value read).
- Open enums name only some values; unused-variant warnings are probably wrong
  there.
- ~~Report only the root package, or every package the user owns?~~ Decided
  2026-11-20: the pass takes the one package to report on as a parameter;
  the CLI and LSP pass the root. Reporting on several would take a set
  indexed by `PackageId`, once that is decided.
- Whether a trait's default method body keeps edges when no impl inherits it.

## Tests

`DiagnosticView::assert_warning` / `assert_none`, in the new module. One case
per code, plus the shapes that distinguish the policies: a dead chain, a
self-recursive function, a field read only by an unused function, an operator
impl used only through `+`, a struct live only through a type argument, a use
item reached only through a glob, and a program with an error (no warnings).
