# Unused-definition warnings in the new TIR

Status as of 2026-11-11, branch `tir-refactor`. A plan, not a record: nothing
here is implemented beyond what "Where we are" describes. Companion to
`tir-check-pass.md` and `tir-body-checking-plan.md`. Open questions are at the
end.

## Goal

Report, as warnings, what the old checker's end-of-check pass reported
(`tir/builder/mod.rs` in commit `05e2978`, `report_unused_items` and
`report_unused_enum_variants`; local and label warnings are in
`tir/builder/body.rs::report_stack_warnings`), on
the new `Semantics`, at check time (so `wx check` and the LSP get it without
lowering):

| Code | Subject |
| --- | --- |
| W2001 `UnusedVariable` | a local or parameter that is never read |
| W2002 `UnnecessaryMutability` | `mut` on a local that is never assigned |
| W2004 `UnusedItem` | a function, constant, global, struct, enum, trait, alias, memory, `use` item |
| W2006 `UnusedTypeParam` | a type parameter never used in its declaration |
| W2007 `UnusedStructField` | a private field that is never read |
| W2008 `UnusedLabel` | a loop or block label no `break`/`continue` names |
| W2009 `UnusedEnumVariant` | a variant never named |

All seven codes already exist in `diagnostics.rs`.

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
- a named argument's label is `Site::Label` with `ArgumentLabel` (a constructor
  field label means initialization); a `break`'s label is `Site::Label` with
  `Referent::Label`.
- declarations are not entries: they live in their owning tables
  (`Body::locals`, `Body::labels`, the per-kind declaration arenas).

So "which `use` items are unused" and "which locals are never read" are
inverses of this table, as its module doc says. The table is **not enough for
reachability** (below): it has no owner for a reference, and it misses uses the
checker does not write as names (an operator calls an impl's method).

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

A new module, `tir/unused.rs`, one phase after `check_bodies` and the export
resolution in `SemanticsBuilder::build`. It reads `Semantics` and pushes
warnings; it builds no bodies.

- **Gate:** run only when checking reported no error or bug. A failed path
  records only its resolved prefix, so an item used only through one would look
  unused, which is noise next to the real error (and the LSP is usually broken
  mid-edit). rustc's lints are gated the same way.
- **Locals and parameters:** for each `Body::locals()` entry, collect its
  references from the table (`Reference::Local { owner, local, access }`).
  W2001 when no reference is a `Read` (decide `ReadWrite`, below); W2002 when
  `mut_span` is set and no reference is `Write` or `ReadWrite`.
- **Labels:** for each `Body::labels`, W2008 when no `Site::Label` entry holds
  that `LabelIdx`.
- **Type parameters:** W2006 when no `Referent::TypeParam { env, index }` names
  it. A trait's own `Self` is exempt.
- **Fields:** W2007 for a non-`pub` field with no `Reference::Field` of `Read`
  or `ReadWrite` (see "Data gaps": positional patterns).
- **Items:** W2004/W2009 when nothing references the declaration (a variant is a
  `Const`). `use` items: unused when no `Referent::Import { import }` names it;
  a glob is used if any import referent points at it.
- **Exemptions:** the std package, items of dependency packages (report the
  user's packages only), wasm `import` declarations, anything named by the
  export block, `pub` items of a `lib` package, trait declarations' members,
  trait impls' members, and `_`-prefixed names (decide).

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

- Does `ReadWrite` count as a read for W2001? rustc flags a variable that is only
  ever compound-assigned. Leaning: no, `Read` only.
- `_`-prefixed names exempt, or only the bare `_`?
- Open enums name only some values; unused-variant warnings are probably wrong
  there.
- Report only the root package, or every package the user owns?
- Whether a trait's default method body keeps edges when no impl inherits it.

## Tests

`DiagnosticView::assert_warning` / `assert_none`, in the new module. One case
per code, plus the shapes that distinguish the policies: a dead chain, a
self-recursive function, a field read only by an unused function, an operator
impl used only through `+`, a struct live only through a type argument, a use
item reached only through a glob, and a program with an error (no warnings).
