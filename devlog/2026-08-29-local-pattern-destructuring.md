# Pattern destructuring for `local` bindings

Finished a feature that was already half-built: the AST, parser, and formatter
handled all four pattern forms, with passing tests, but TIR rejected everything
except a plain name. The whole feature dead-ended at one `_ =>` arm in
`build_local_definition_statement`:

```rust
"pattern destructuring in locals is not yet supported"
```

(The AST half is the `Pattern::Struct` work destroyed and reconstructed in the
[formatter comment-placement session](2026-08-29-formatter-comment-placement.md)
earlier the same day.)

899 → 925 `wx-compiler`, 56 `wx-lsp`, 43 `wx-fmt`. No snapshots regenerated —
see "the shape that avoided snapshot churn" below.

## The motivating gap: tuples could be built but never taken apart

wx has tuple types (`Type::Tuple`), tuple literals (`ExprKind::TupleInit`), tuple
layout in MIR, and tuple type aliases. It has no way to *read* an element.
There is no `t.0`: `Expression::ObjectAccess.member` is a `SymbolU32`, so a
positional index cannot even be represented, and `build_object_access_expression`
only matches `Type::Struct`. Tuples could be constructed, typed, passed, and
returned — and then only ever consumed whole.

So destructuring is not sugar here. It is the only way to get a value out of a
tuple, which raised the stakes on getting the lowering right rather than
convenient.

## Design decisions

**`Point::{ x, y }`, not Rust's `Point { x, y }`.** The pattern grammar as
inherited used a bare identifier and Rust's brace form, while struct *literals*
in wx are `Point::{ x: 1 }` with a full `Box<[PathSegment]>`. Chose internal
consistency over Rust familiarity: a pattern and a literal for the same struct
now read the same way, and the path upgrade means a struct in another module can
be destructured at all (`geom::Point::{ x, y }`), which the bare identifier made
impossible without a `use` first. The parser mirrors `parse_path_expression`'s
`::` walk rather than reusing `parse_path_segments` — the latter consumes the
`::` and then `break`s, which makes `Point {` and `Point::{` indistinguishable.

**Exhaustive, with `..` as the escape hatch.** `Token::DotDot` already existed
(slice ranges). Requiring every field matches Rust, and `..` keeps wide structs
usable. Deliberately **no validation of `..` in the parser** — it records a
single `rest: Option<TextSpan>` and nothing inspects where `..` sat among the
fields or whether it appeared twice. Keeping the AST dumb here was a direct
call: position carries no meaning, so there is nothing for the parser to check.

**`t.0` is deliberately not a language feature.** The TIR needs a positional
projection to bind tuple elements, but it is compiler-internal, produced only by
`bind_pattern`, with no surface syntax — recorded in its doc comment so a future
reader does not "finish" it by wiring up `.0`.

**`_` is a drop, not a store.** My first draft gave a top-level `local _ = f();`
a nameless local slot. That was wrong, and the correction is the good kind of
obvious in hindsight: `_` means *don't bind*, and `_ = f();` already exists
end to end as `ExprKind::Assign { left: Placeholder }` lowering to MIR's `Drop`
with the comment "evaluate rhs for side effects, discard the value". `local _ =`
now lowers to exactly that node. A *nested* `_` emits nothing at all, since
projections are pure reads with nothing to evaluate for effect.

## The shape that avoided snapshot churn

With `_` handled, only one thing still needed a slot: the scrutinee.
`local (a, b) = f();` must evaluate `f()` once and project it twice, and MIR's
`FieldAccess` arm re-lowers its object per projection, so leaning on the
automatic spill would call `f()` twice.

Two candidates:

1. **Nameless TIR local** — `tir::Local.name` becomes `Option<...>`, TIR emits
   plain `LocalDeclaration`s, MIR needs only a projection arm.
2. **Fused TIR node** — `DestructureDeclaration { value, bindings }`, MIR spills
   once into a scope-0 temp and emits the stores.

Went with (2). The deciding argument is that **`mir::Local` has no name field at
all** — `{ ty, mutability }` — so MIR is already the layer where nameless temps
live, and `mir/mod.rs` open-codes exactly that spill in seven places. Option (1)
would have dragged a MIR concern into TIR, where every local is a user-written
binding, touched ~9 read sites across the compiler and LSP, and regenerated
every snapshot containing a local. Option (2) touched none of that: **`wx-lsp`
needed zero changes**, because destructured bindings are ordinary `tir::Local`s
in `scope.locals` with real name spans, and `symbol_index` already walks those —
go-to-definition, rename, and completion came for free.

### The arena question, and why it does not help

Asked directly whether storing expressions in an arena and referencing them by
index — instead of `Box<Expression>` — would remove the need for the temp.

It would not, and the reason is worth recording. TIR is a *tree* whose
evaluation order is structural: code is emitted at each occurrence of a node. If
`f()` lived in an arena and two declarations shared its `ExprId`, MIR would walk
that id twice and emit the call twice, exactly as `Box` does. Sharing a node
means "evaluate once" only if the IR's semantics say so, and a tree IR's do not.
Making it mean that requires memoization keyed on `ExprId` plus rules about when
re-evaluation is observable — which is value numbering, i.e. what `opt/` already
is (`Builder::node` → `intern_node`). **In a tree IR, a temp *is* the encoding of
"evaluate once."** The arena has real wins elsewhere (in-place subexpression
rewriting, one allocation instead of per-node, side tables keyed by `ExprId`,
`Place` becoming copyable) — but not this.

## Flattened projection paths

Nesting is flattened in TIR rather than kept nested: `local (x, (y, z)) = t;`
yields paths `[0]`, `[1,0]`, `[1,1]`. Each step is

```rust
pub struct PathStep { pub aggregate_ty: TypeIndex, pub index: u32 }
```

carrying the aggregate's TIR type **explicitly**, so MIR never re-derives the
type it is indexing into — `lower_type_index(aggregate_ty)` hands back the
interned `Aggregate` with generic substitution already applied. Without this,
MIR would have to walk the type alongside the path and re-apply struct type
arguments itself.

`index` is the *declaration* index. MIR maps it through `decl_to_phys`, which
matters: **tuples are alignment-sorted exactly like structs** (`ensure_aggregate`
with `FieldOrder::Sorted`, the same call `TupleInit` makes), so `(bool, i64, u32)`
has physical order `i64, u32, bool` and `decl_to_phys == [2, 0, 1]`. A naive
`value_index: index` silently returns the wrong element — covered by a test that
asserts the slots are `[2, 0, 1]` rather than `[0, 1, 2]`.

MIR gained a named `spill_to_temp` helper for this; the seven pre-existing
open-coded copies of the idiom were left alone rather than refactored during a
feature.

## Key finding: a pre-existing panic on untyped tuple literals

`local t = (1, 2);` — a **plain binding, no destructuring involved** — passed TIR
with zero diagnostics and panicked MIR:

```
TIR errors: []
panicked at mir/mod.rs:1259: internal error: entered unreachable code
```

`resolve_local_type` enforces wx's no-implicit-typing rule via
`value.ty.is_comptime_number()`, but that tests the type index itself, and
`(1, 2)` is a separately interned `Type::Tuple { elements: [INTEGER, INTEGER] }`,
not `INTEGER`. The local was created with a comptime-carrying type and
`lower_type_index` hit its `unreachable!()` on `INTEGER`.

Fixed with a `contains_comptime_number` traversal used in the same guard, so
`local (a, b) = (1, 2);` now correctly reports `E1002` ("type annotation
required") and `local (a, b): (i32, i32) = (1, 2);` is the way to write it.

**The traversal walks tuples only** — and that narrowing came from a challenge to
my first draft, which mirrored `contains_infer` across structs, pointers,
slices, arrays, and function signatures. The reasoning holds up and was
confirmed empirically rather than argued: there is no surface syntax for the
comptime types, so any type the user *wrote* is already concrete, and every
other route from literals to an aggregate is rejected before producing one —
`[1, 2]` already demands its own annotation (yields `Error` + `E1002`), and
`Box::{ v: 1 }` on a generic struct fails to coerce rather than inferring
`T = INTEGER`. A tuple is the single construction that silently keeps its
elements comptime, and it nests inside itself.

## Reused rather than added

Diagnostics needed no new codes. Struct patterns reuse `UnknownStructField`
(E1025), `DuplicateStructFieldInit` (E1026), and `MissingStructFields` (E1027,
inlined with a `..` note instead of the struct-init helper's "in initializer of"
wording); shape and arity mismatches reuse `TypeMistmatch` (E1001). Only the
parser gained one, `InvalidPattern` (E0015), for a path in binding position.
Field-type substitution and `FieldAccess { kind: Read }` recording follow
`build_object_access_expression`, so unused-field analysis and the LSP see
destructured reads like any other.

Note the replaced diagnostic had **no `DiagnosticCode` at all**, unlike the other
83 `report_*` helpers.

## Verified end to end

Not just types — the emitted WASM:

```wat
(func (;1;) (result i32)
  call 0          ;; make() — exactly once
  local.set 0
  local.set 1
  ...)
```

`..` correctly skips fields; a `Mixed { a: bool, b: i64, c: u32 }` parameter
flattens to alignment-sorted scalars and `local.get 2` picks `a`; `local _ =
make()` emits the call and discards it; a nested tuple of literals
constant-folds away entirely. `wx fmt` round-trips every pattern form
idempotently and the reformatted source rebuilds to a byte-identical module.

## Context for future sessions

- Two unrelated "pattern" concepts still coexist: `ast::Pattern` (locals only)
  and `match` arms, which parse as ordinary `Expression`s and build the separate,
  flat, `Copy` `tir::Pattern` (`Int`/`Bool`/`Char`/`EnumVariant`/`Wildcard`, "no
  bindings, no or-patterns, no guards"). Unifying them is the natural path to the
  `variant` item sketched in
  [2026-08-16-pointer-reference-split-design.md](2026-08-16-pointer-reference-split-design.md)
  — that design named the then-dormant `Pattern::Binding`/`Tuple`/`Struct`
  grammar as its reuse target, and it is no longer dormant.
- Function parameters are still names only (`ast::FunctionParam` is structurally
  `Pattern::Binding` plus a type), so `fn f((a, b): (i32, i32))` would be a
  mechanical extension now that `collect_pattern_bindings` exists.
- Two traps for anyone writing scratch `.wx` files by hand: primitives come from
  the stdlib, so a file needs `use std::*;` or `i32`/`bool` are undeclared types
  (the test harnesses prepend it automatically); and `as` between different WASM
  scalar widths is rejected (`i32 as i64` → `E1041`), since casts are gated on
  `WasmScalar` equivalence.

## Open questions

- **`report_unable_to_coerce` reads badly for an unresolved type parameter.**
  `Box::{ v: 1 }` reports "unable to coerce to type `T`", naming a parameter the
  user never wrote and describing a coercion failure when the real problem is
  that inference had nothing but an untyped literal to work from. Should report
  an inference failure with a turbofish suggestion. Five call sites, all
  `builder.rs:919`. Found while probing the comptime traversal; deliberately not
  folded into this change.
- **`local (a, a) = pair;` is accepted**, the second binding shadowing the first,
  with an unused-variable warning on the first. Rust rejects duplicate bindings
  in one pattern. wx's existing same-scope shadowing makes the current behaviour
  self-consistent, so this was left as a deliberate difference rather than an
  oversight — worth a decision if patterns grow.
- `Point::{ mut x }` does not parse; `Point::{ x: mut x }` is the workaround.
  `parse_pattern_field` reads an identifier then an optional `: pattern`, so
  `mut` in shorthand position would need its own handling. Rust allows it.
