# 2026-08-17 — Compound assignment (`+=`) as trait-dispatch sugar: design

## Context

Follow-on to the operator-overloading feature (`Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg` as
traits, tag-resolved via `#[tag = "add"]` etc., dispatched through
`EvalMode`/`OperatorTraits` — see the primitive-impl and `build_arithmetic_expr`
work already landed for plain `+`/`-`/`*`/`/`/`%` and unary `-`). This document
covers `+=`/`-=`/`*=`/`/=`/`%=` specifically: `x += y` is sugar for
`x = x.add(y)`, reusing the resolved trait method, not a separate `AddAssign`
trait.

This took a lot of iteration to land on the right shape. Recording the
rejected alternatives alongside the final design, because the reasons they
were rejected are exactly the constraints the final design has to satisfy —
without them the four-node split looks like overkill.

## The core problem

Computing the new value for `x op= y` needs `x`'s *current* value (read) and
also needs to write the result back to the same place (write) — but the
result has to come from *real trait dispatch* now, not a hardcoded native op,
to stay consistent with how plain `+` already works.

The naive fix — build `x = x.add(y)` as a literal TIR tree, i.e. reference the
`x` expression twice (once as the call's receiver, once as the assignment
target) — runs into two independent blockers:

1. **`Expression`/`Place` aren't `Clone`.** For `Local`/`Global` targets this
   wouldn't matter (their "receiver" is just `Copy` indices, trivially
   reconstructible without cloning anything). For a `Load { place }` target
   (`arr[i] += 1`, `ptr.* += 1`), `Place` can embed arbitrary sub-expressions
   (`PlaceKind::Index { object, index }`), which are not cheap to duplicate.
2. **Even if `Place` were `Clone`, that wouldn't fix evaluation order.**
   Verified directly: `lower_index_address`'s dynamic-index branch
   (`mir/mod.rs`, non-constant case) lowers `index` *inline* into the
   returned address expression — no temp-local sinking, unlike the adjacent
   slice branch. Today's `lower_compound_assignment` already calls
   `lower_place_address` **twice** for a `Load{place}` target (once inside
   `lower_expression(left)` for the old-value read, once directly for the
   store) — meaning **`arr[i()] += 1` already double-evaluates `i()` today**,
   a real pre-existing bug, independent of trait dispatch. Cloning the place
   wouldn't avoid this; the fix has to happen in MIR lowering regardless
   (materialize the address once, into a temp local, reuse for both the load
   and the store — the codebase already uses this exact idiom elsewhere,
   e.g. `mir/mod.rs` around the slice-object temp in `lower_index_address`).

So: whatever the final shape is, it must (a) never require duplicating a
`Place`, and (b) fix the address-computed-twice bug for the `Load` case while
it's being touched anyway (agreed explicitly — not silently perpetuating a
bug into new code written this session).

## Rejected shapes, and why

- **`Binary { operator: Assign, left: <place=place.add(rhs) desugar>, .. }`**
  — blocked by the `Clone` problem above; also, plain assignment's own
  `Load{place}` target *doesn't* go through `Binary{Assign}` at all — it
  already uses a dedicated `Store { target: Place, value }` node, precisely
  because a place can't be squeezed into a generic expression-shaped LHS.
  `lower_assignment` (MIR) has no `Load` arm at all for this reason.

- **One `CompoundAssign { operator, left, right, method_id: Option<DefId> }`
  node, used for all four target kinds**, with `None` meaning either
  "typeset-bounded, use the native op" or "genuinely unsupported, diagnostic
  already pushed." Rejected: the two `None` reasons are semantically
  different, and a caller building a node from a bare `Option` has no way to
  tell them apart short of re-deriving the check itself.

- **Split by target kind: `LocalSet`/`GlobalSet`/`FieldSet` (reusing
  `build_arithmetic_result` directly — `Some`/typeset-bounded/diagnostic all
  handled for free) + `CompoundStore` for `Load`.** Rejected on two grounds:
  `FieldSet`'s safety (object rebuildable without re-evaluating it) silently
  depends on an invariant enforced *elsewhere* (`build_arithmetic_assignment_expr`'s
  existing guard restricting field-assignment's `object` to `Local`/`Global`)
  that isn't visible in `FieldSet`'s own shape — fragile if that guard is
  ever loosened. And `CompoundStore` still needed the same `Option<DefId>`
  ambiguity as above, for the one target that actually mattered.

- **Moving resolution entirely into MIR** (`lower_compound_assignment` calls
  `find_trait_impl` itself, no TIR involvement) — rejected: TIR is where
  "does this type implement `Add`" has to be diagnosed (a real user-facing
  error), and where the go-to-definition access gets recorded
  (`resolve_operator_method` pushes `SourceSpan` onto the resolved method's
  `accesses` list at TIR-build time). Neither belongs in MIR.

- **Treating typeset-bounded (`Mem::Size`) as needing a distinct "native op
  fallback" shape, separate from the generic (`T: Add`) case.** This was the
  last wrong turn, worth recording because the fix is the key insight the
  whole design now rests on: **typeset-bounded and generic-not-yet-concrete
  are the same category.** `Mem::Size` is an `AssocTypeProjection` through an
  abstract `Mem: Memory` type parameter, and it resolves to a concrete type
  (e.g. `u32`) via the *same* substitution machinery
  (`resolve_tir_type`/`current_substitutions`) that resolves a bare
  `TypeParam` once the surrounding generic function is monomorphized —
  confirmed by how `GenericMethodCall`'s MIR lowering already resolves
  projections like `Self::M`, not just bare type params. So there is no need
  for a native-op fallback shape at all — deferring to monomorphization
  (`GenericCompoundAssign`/`GenericCompoundStore`, below) is the fallback,
  uniformly, for anything not concretely resolvable *yet*. This also means
  the "when do we build the generic node" decision does **not** need task
  #9's typeset/trait-bound checking machinery — it only needs "is `ty` a
  bare `Type::TypeParam` or `Type::AssocTypeProjection`," which is a much
  simpler, already-general question (the same kind of check that decides
  `MethodCall` vs. `GenericMethodCall` for ordinary calls, since
  `GenericMethodCall`'s `type_args[0] = Self` is populated whenever the
  receiver isn't already fully concrete).

## Precedent: how `t.method()` already works for `fn f<T: Trait>(t: T)`

Directly informed the final design. TIR builds `ExprKind::GenericMethodCall {
id, type_args, arguments }` — `id` is the **trait's abstract method
declaration** (no body), `type_args[0] = Self` (still abstract, e.g.
`TypeParam{0}`). TIR does not try to resolve which impl this is — it can't,
`T` isn't concrete yet.

Resolution happens in MIR, at lowering time (`mir/mod.rs`, `GenericMethodCall`
arm): `type_args` gets resolved through `current_substitutions` (concrete by
then, because the *surrounding* function has already been monomorphized for
this instantiation). If the trait method is abstract (no body — the normal
case), MIR calls `self.tir.find_trait_impl(concrete_self, trait_index)`
**right there** — the same public `find_trait_impl` API this whole feature
already uses — to find the concrete impl, then builds a `Call` to it. No
vtables, no runtime type tag — monomorphization plus a late static
resolution, reusing existing public TIR API from MIR.

`GenericCompoundAssign`/`GenericCompoundStore` (below) follow this exact
pattern: no new machinery, just the compound-assignment analogue of
`GenericMethodCall`.

## Final design

### New `tir::BinaryOp`

A TIR-only enum, `ast::BinaryOp` minus the six assignment variants (`Assign`,
`AddAssign`, `SubAssign`, `MulAssign`, `DivAssign`, `RemAssign`).
`ExprKind::Binary.operator` becomes `Spanned<tir::BinaryOp>`. Assignment is no
longer representable through `Binary` at all — it has its own dedicated
nodes, below. Touches every existing `Binary` construction site (~30, across
arithmetic/comparison/logical/bitwise) with a mechanical conversion where
`operator` is first extracted from the AST; the compiler enforces every site
is updated (exhaustive match).

### Plain assignment: `Assign`

```rust
Assign { left: Box<Expression>, right: Box<Expression> }
```
Replaces `Binary { operator: Assign, .. }` for `Local`/`Global`/`FieldAccess`
targets. `Load{place}` keeps using the existing `Store { target: Place, value
}` node, unchanged — this split already existed for plain assignment; `Assign`
just extends the same reasoning to the other three target kinds instead of
lumping them into the generic (soon-to-be-gone) `Binary{Assign}` shape.

### Compound assignment: four nodes, split two ways

Split 1 — **resolved now vs. deferred to monomorphization** (mirrors
`MethodCall` vs. `GenericMethodCall`):

```rust
// ty already concrete, find_trait_impl resolved a method now.
CompoundAssign {
    target: Box<Expression>,   // Local / Global / FieldAccess
    rhs: Box<Expression>,
    method_id: ast::DefId,     // non-optional — this node only exists when dispatch succeeded
}

// ty is still abstract (bare TypeParam, or an AssocTypeProjection like
// `Mem::Size` through an abstract type param) — resolved later, in MIR,
// exactly like GenericMethodCall's abstract-method branch.
GenericCompoundAssign {
    target: Box<Expression>,
    rhs: Box<Expression>,
    abstract_method_id: ast::DefId, // the trait's abstract method declaration
    self_type: TypeIndex,           // still abstract; = target's type
}
```

(`self_type` is stored bare rather than as a single-element `type_args: Box<[TypeIndex]>` — unlike `GenericMethodCall`, none of the operator traits' methods have any generics of their own beyond the implicit `Self`, so there's never a second slot to hold.)

Split 2 — **target is a plain `Expression` vs. a `Place`** (mirrors `Store`
vs. everything else): `Load{place}` needs address-computed-once semantics
that the other three target kinds don't, so it gets its own pair instead of
folding into the shapes above with a `Box<Expression>` that only sometimes
means "also gets read":

```rust
CompoundStore {
    target: Box<Place>,
    rhs: Box<Expression>,
    method_id: ast::DefId,
}

GenericCompoundStore {
    target: Box<Place>,
    rhs: Box<Expression>,
    abstract_method_id: ast::DefId,
    self_type: TypeIndex,
}
```

Four nodes, not two and not one — but each one is a single, uniform,
self-documenting shape; nothing needs a bare `Option` whose meaning depends
on which case you're in, and nothing needs to know its own field is
sometimes safe to duplicate and sometimes isn't.

### Resolution logic (`build_arithmetic_assignment_expr`)

For each of the four `left.kind` arms (`Local`/`Global`/`FieldAccess`/`Load`),
after building/coercing `rhs` exactly as today:

1. `ty` = the target's type.
2. If `self.tir.types[ty]` is `Type::TypeParam` or `Type::AssocTypeProjection`
   → look up the trait's *abstract* method (`self.tir.traits[trait_index]
   .entries.get(&method_symbol)` → `ImplEntry::Method(func_index)` → that
   function's `id`) → build `GenericCompoundAssign`/`GenericCompoundStore`
   with `self_type: ty`.
3. Otherwise, `ty` is concrete → call `resolve_operator_method` (the existing
   pure lookup from the plain-`+` work) → `Some(func_idx)` → build
   `CompoundAssign`/`CompoundStore` with that method's `id` (also where the
   go-to-definition access gets pushed, same as `build_operator_dispatch`) →
   `None` → push the existing "operator cannot be applied" diagnostic, return
   `Err(())` (node is never constructed; the compiler pipeline halts before
   MIR ever sees a real diagnostic, so there's nothing left to lower).

No node is ever built for "unsupported" — that path just fails the builder,
same as it does for `+` today.

### MIR lowering

`CompoundAssign`/`GenericCompoundAssign` (target is `Local`/`Global`/
`FieldAccess`): trivial — extract indices from `target.kind` (safe to
reference twice; they're `Copy` metadata, not computations), lower `target`
as a value for the old-value read, lower `rhs`, build a `Call` (direct to
`method_id`, or via `find_trait_impl` + `mono_registry` for the generic case,
exactly like `GenericMethodCall`'s abstract branch), then `LocalSet`/
`GlobalSet`/`AggregateSet` with that call as the value.

`CompoundStore`/`GenericCompoundStore` (target is a `Place`): the careful
one. Call `lower_place_address` **exactly once**, sink the resulting pointer
into a fresh temp local (`LocalSet` pushed to `sink`, matching the existing
temp-local idiom already used elsewhere in this file), then reference that
temp via `LocalGet` for both the `PointerLoad` (old value) and the
`PointerStore` (new value) — guaranteeing any side-effecting sub-expression
in the place (e.g. `i()` in `arr[i()] += 1`) runs exactly once. This is the
fix for the pre-existing bug identified above; it lands as part of this work
since `lower_compound_assignment`'s old `Load` arm is being replaced anyway.

### Scope boundary vs. task #9

Task #9 ("support `Type::TypeParam` bounded by `Add`/etc. in operator
checks") is about `build_arithmetic_expr`/`build_arithmetic_result` — plain
`+`/`-`/etc. — which today has no path for a bare `TypeParam` operand at all
(neither `is_typeset_bounded_assoc_type` nor `find_trait_impl` handle it).
Compound assignment's generic case doesn't block on that: the "is `ty`
abstract" check above is simpler and more general than what #9 will add
(#9 is specifically about checking a `TypeParam`'s *bound* actually includes
the relevant trait before allowing the operator — compound assignment's
`GenericCompoundAssign` doesn't need that check itself, since a `T: Add`
bound was already required by the function's own signature to even reach
this code meaningfully; resolution is fully deferred to MIR regardless).
