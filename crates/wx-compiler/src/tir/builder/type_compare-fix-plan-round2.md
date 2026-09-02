# Fix plan: `type_compare.rs`, round 2

Follow-up to `type_compare-fix-plan.md` (steps 1–4, all done/resolved).
That round fixed the two original regressions (nested trait-side
projections, asymmetric normalization for a simple equality-bound
projection) found by hand-construction. This round is a second review
pass that found four more real bugs — three of them symptoms of the same
underlying gap: `found`'s reduction was scoped too narrowly in round 1's
step 2, and the fast path's safety argument from round 1's step 3 turns
out to have a real hole.

Anchored on four new `#[ignore]`d regression tests in `tir/tests.rs`, all
verified by hand to fail exactly as described (`cargo test --lib
--include-ignored`), and confirmed not to disturb the rest of the suite
(999 passed, 0 failed, 14 ignored — up from 10 — `fmt` clean):

- `test_recursive_same_impl_nonidentity_binding_is_detected` — **false
  negative** (unsound): produces zero diagnostics for a genuine mismatch.
- `test_error_in_intermediate_resolution_does_not_cascade` — **false
  positive**: an undeclared-type error cascades into a spurious second
  diagnostic.
- `test_expected_typeparam_reduces_against_found_projection` — **false
  positive**: rejects a valid impl.
- `test_found_side_nested_projection_normalizes_via_find_trait_impl` —
  **false positive**: rejects a valid impl.

## Root cause

Three of the four (all but the `Error`/`Infer` one) trace back to the same
mistake in round 1: I scoped `found`'s reduction (`reduce_found`) to "only
ever needs a declared equality binding, never `find_trait_impl`, never a
new `Frame`" — true for the simple case, but incomplete in two ways that
compound:

1. **`reduce_found` isn't consulted early enough.** `compare_resolved`
   dispatches on `expected`'s shape first; if `expected` is a bare
   `TypeParam`, it goes straight to `compare_unresolved_type_param` and
   `reduce_found` never runs at all. (`test_expected_typeparam_reduces_
   against_found_projection`)

2. **`reduce_found` only tries an equality binding on a projection's raw,
   unreduced base.** If the base is itself a nested projection that only
   becomes concrete *through* a binding (not flattenable at Phase 2, since
   the binding is a fact local to this one method signature), `reduce_found`
   never gets far enough to discover that — and once the base *is*
   concrete, resolving the outer step genuinely needs `find_trait_impl`,
   contradicting round 1's "never `find_trait_impl`" premise.
   (`test_found_side_nested_projection_normalizes_via_find_trait_impl`)

Once (2) is fixed, `found` *can* end up carrying a `Frame::Bind` — which
directly reopens the fast-path safety argument from round 1's step 3. That
argument only covered `find_trait_impl` unifying an impl's pattern against
*its own original target* (always an identity binding); it didn't cover a
*later* projection step in the same chain dispatching to the same impl
again against an already-transformed receiver — which is exactly what
`test_recursive_same_impl_nonidentity_binding_is_detected` demonstrates,
and doesn't even need `found` to carry a frame at all (it's already
reachable purely through `expected`'s own resolution). So this needs
fixing regardless of how (1)/(2) land, and needs to land in a way that
still holds once (2) makes `found` frame-carrying too.

The `Error`/`Infer` cascade is unrelated and simpler: `compare_types`'s
check only examines the operands it's called with; `resolve_and_compare`/
`apply_pending` recurse into *themselves*, never back into `compare_types`,
so a value that resolves to `ERROR`/`INFER` partway through never gets
re-checked before reaching `compare_structural`.

## Step 1 — re-check `Error`/`Infer` after every resolution step

Simplest, most isolated, no interaction with the other three. Add the
same check `compare_types` already has to the entry of
`resolve_and_compare`:

```rust
fn resolve_and_compare(&self, expected: TypeRef<'_>, pending: &Pending<'_>, found: TypeRef<'_>, path: &mut Vec<TypePathElement>) -> TypeComparison {
    if matches!(self.types.resolve(expected.index), Type::Error | Type::Infer)
        || matches!(self.types.resolve(found.index), Type::Error | Type::Infer)
    {
        return TypeComparison::Indeterminate;
    }
    match self.types.resolve(expected.index) { ... }
}
```

`found` doesn't currently change across `resolve_and_compare` recursion
(round 1), but checking it here too costs nothing and stops being
redundant the moment step 3 below lands and `found` *does* change.
Verify: un-ignore `test_error_in_intermediate_resolution_does_not_cascade`,
confirm only `E1021` remains, no `E1080`.

## Step 2 — frame-aware fast path

The current fast path (`expected.index == found.index` alone) is unsound
for composite types that can embed a `TypeParam`. Fix: only trust a raw
index match unconditionally for a *frame-inert* leaf (a shape with no
substructure a frame could possibly reinterpret — primitives, `Enum`,
`Namespace`, `Memory`); for anything else, also require either identical
frame pointers, or — if the shared shape is a composite (`Tuple`,
`Struct`, `Pointer`, `Array`, `Slice`, `Function`, `FunctionItem`) — fall
through to structural recursion instead of trusting the index, so each
field gets compared under its *own* frame:

```rust
fn is_frame_inert(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Unit | Type::Never | Type::Integer | Type::Float
            | Type::U8 | Type::I8 | Type::U16 | Type::I16
            | Type::U32 | Type::I32 | Type::U64 | Type::I64
            | Type::F32 | Type::F64 | Type::Bool | Type::Char
            | Type::Enum { .. } | Type::Namespace { .. }
    )
}

/// `expected`/`found` share a raw `TypeIndex` — decide what that's worth.
/// `None` means "not decided by the index alone, proceed normally."
fn compare_equal_index(
    &self,
    expected: TypeRef<'_>,
    found: TypeRef<'_>,
    expected_ty: &Type,
    path: &mut Vec<TypePathElement>,
) -> Option<TypeComparison> {
    if std::ptr::eq(expected.frame, found.frame) || is_frame_inert(expected_ty) {
        return Some(TypeComparison::Equivalent);
    }
    if !matches!(expected_ty, Type::TypeParam { .. } | Type::AssocTypeProjection { .. }) {
        // Composite shape, same index, different frames that could still
        // make an embedded TypeParam mean different things on each side.
        return Some(self.compare_structural(expected, found, path));
    }
    // Same abstract node, different frames — resolve each side via its
    // own frame instead of trusting the raw index; fall through.
    None
}
```

Used identically at both `compare_types`'s and `compare_resolved`'s fast
paths (one shared helper, since round 1's step 3 comment already
established they need "the same safety argument" — worth actually sharing
the code now, not just the reasoning). Both call sites already resolve
`expected_ty` once for their own purposes; thread it into
`compare_equal_index` rather than re-resolving.

Verify: un-ignore `test_recursive_same_impl_nonidentity_binding_is_detected`,
confirm it now reports `TraitImplSignatureMismatch`. Also re-run the round
1 stdlib regression test (`test_trait_impl_method_self_type_projection_
matching_no_error`) — that one exists specifically because an earlier,
*more* naive fast path (checking frame identity unconditionally) broke it;
confirm this version doesn't regress it (it shouldn't: `u32`, the leaf
that test resolves to, is frame-inert).

## Step 3 — make `found`'s reduction earlier and genuinely complete

The larger piece, addressing both remaining tests together since they're
the same underlying gap at two different points.

**3a — try `reduce_found` before dispatching on `expected`'s shape**, not
only in `compare_resolved`'s non-`TypeParam` branch:

```rust
fn compare_resolved(&self, expected: TypeRef<'_>, found: TypeRef<'_>, path: &mut Vec<TypePathElement>) -> TypeComparison {
    let expected_ty = self.types.resolve(expected.index);
    if let Some(result) = self.compare_equal_index(expected, found, expected_ty, path) {
        return result;
    }
    let found = self.reduce_found(found); // moved up, tried unconditionally
    if expected.index == found.index { ... } // re-check after reduction
    match expected_ty {
        Type::TypeParam { .. } => compare_unresolved_type_param(...),
        _ => compare_structural(expected, found, path),
    }
}
```

This alone fixes `test_expected_typeparam_reduces_against_found_projection`
once `reduce_found` genuinely reduces `D::Out` to `C` (already works today
for a *non*-nested case — that part of round 1's step 2 was correct).

**3b — generalize `reduce_found` to resolve a nested projection base
first, and fall back to `find_trait_impl` once that base is concrete.**
This is the part that needs real design, not a quick patch: it means
`found` can now construct a `Frame::Bind` too, which is exactly the
capability round 1's step 2 deliberately avoided (for good reason at the
time — it kept `found`'s side allocation/lifetime-free). Two shapes worth
weighing before implementing:

- **Mirror `expected`'s machinery on `found`, called independently.**
  Build a `found`-side equivalent of `resolve_and_compare`/`apply_pending`
  that also tries `find_trait_impl`. Straightforward to reason about
  (same shape as code that already exists and works), but doubles the
  surface area — two near-identical recursive function pairs.
- **Generalize `resolve_and_compare` to reduce *either* side**, threading
  two `Pending` chains (`expected_pending`, `found_pending`) through one
  function: try reducing `expected` first (as today); once it's
  irreducible, try reducing `found` the same way; once both are
  irreducible, compare. More code reuse, but a more complex function
  signature and more states to reason through (four combinations of
  "which side, if either, just got reduced").

Lean toward the first shape unless the second turns out meaningfully
smaller in practice — round 1 already showed that "more symmetric" isn't
automatically "simpler" (that's exactly why `found` got a narrower path in
the first place). Whichever shape, this is where step 2's frame-aware
fast path earns its keep: once `found` can carry a `Frame::Bind`, the
`Recursive same-impl` failure mode from step 2 becomes reachable via
`found` too, not just `expected` — the fix from step 2 needs to already be
in place before this lands, not after.

Verify: un-ignore `test_found_side_nested_projection_normalizes_via_find_
trait_impl`, confirm it passes. Re-run all round 1 anchor tests plus this
round's other three to confirm no interaction regressions — this step
touches the most shared machinery, so it's the one most likely to disturb
something already fixed.

## Order of work

1. Step 1 (`Error`/`Infer` re-check) — isolated, do first, cheap
   confidence win.
2. Step 2 (frame-aware fast path) — needed standalone *and* as a
   prerequisite for step 3b being safe.
3. Step 3a (try `reduce_found` earlier) — small, mechanical once step 2 is
   in place.
4. Step 3b (`reduce_found` → nested + `find_trait_impl`-capable) — the
   real design work; decide between the two shapes above once actually
   writing it, the same way round 1's step 1 revised its own sketch after
   hitting a real lifetime constraint.
5. Un-ignore all four tests, full suite + `fmt` + `clippy`, same discipline
   as every step in round 1.

Not in scope for this round: claim 5 from the review (a cycle/progress
guard in `reduce_found`) — attempted to reproduce, couldn't get it to
trigger (fails earlier during bound resolution instead, same pattern as
the original "ProjectionCycle" concern from several rounds before round 1
that also turned out not to be live). Worth cheap defensive insurance
once step 3b's shape is settled, not before — no point guarding a
function whose recursive structure is about to change.
