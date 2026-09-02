# Fix plan: `type_compare.rs`

**Status: steps 1–3 done; step 4 mostly done, `IndeterminateReason` still
open.** Anchored on three new regression tests in
`tir/tests.rs` (alongside the existing
`test_trait_impl_method_self_type_projection_matching_no_error` and the two
conformance-cycle tests from earlier work):

- `test_nested_assoc_type_projection_mismatch_is_detected` — originally
  **failed** (produced zero diagnostics for a genuine mismatch). **Fixed by
  step 1**, now un-ignored and passing.
- `test_nested_assoc_type_projection_match_is_accepted` — originally
  **passed**, but for the wrong reason (`Indeterminate`, not a proven
  match). **Fixed by step 1**, now un-ignored and passing for the right
  reason.
- `test_impl_side_projection_normalizes_against_concrete_trait_return_type`
  — originally **failed** (false positive: rejected valid code). **Fixed by
  step 2**, now un-ignored and passing.

All three were verified by hand as each change landed — `cargo test --lib
--include-ignored` reproduced each described failure exactly before its
fix, and `cargo test --lib` after step 2 shows 999 passed (up from 996
before any of this), 10 ignored (down from 13), 0 failed, with `cargo fmt
--check` and `cargo clippy -p wx-compiler --no-deps -- -D warnings` both
clean throughout (modulo the pre-existing, unrelated `needless_borrow` at
`mod.rs:2464`).

## Root cause, and why it's one fix, not three

All three tests trace to the same two related gaps in `compare_types`/
`compare_projection`:

1. `peel_top` only unwraps a *bare* `TypeParam`. Its loop condition is
   `while let Type::TypeParam { .. } = types.resolve(r.index)` — when a
   projection's base is *another* `AssocTypeProjection` (`Self::Mid::Out`,
   base = `Self::Mid`), the loop never fires, and `find_trait_impl`
   immediately rejects the still-unresolved projection
   (`ImplTarget::from_type`'s `Type::AssocTypeProjection { .. } => Err(())`
   arm). Result: `Indeterminate`, silently.

2. `compare_types`'s dispatch only ever inspects `expected`'s shape:

   ```rust
   match self.types.resolve(expected.index) {
       Type::TypeParam { .. } => ...,
       &Type::AssocTypeProjection { .. } => ...,
       _ => self.compare_structural(expected, found, path),
   }
   ```

   If `expected` is already concrete but `found` is still an unresolved
   projection, we go straight to `compare_structural`, which has no case
   for "the other side is abstract" — it falls to the final shape-mismatch
   catch-all and reports `Different`. This is worse than gap 1: it's an
   active false positive against valid code, not a silent miss.

Both gaps are instances of the same missing capability: a *symmetric*,
*recursive* reduction step — resolve a `TypeRef` (whichever side needs it)
as far as it will go, through the same three-step pipeline
`compare_projection` already runs for one level (same-shape alpha-
equivalence → declared equality binding → `find_trait_impl`), repeated
until nothing more reduces. `compare_projection`'s existing body already
*is* most of this step; it just isn't applied recursively, and it's only
ever applied to one side.

## Step 1 — done, twice

**First pass:** the sketch above (a plain `fn normalize_head<'f>(&self, r:
TypeRef<'f>) -> TypeRef<'f>`, looping and returning) doesn't type-check,
and not for a superficial reason: resolving a projection via
`find_trait_impl` constructs a *new* `Frame::Bind`, and a function can
never return a `TypeRef` borrowing from a `Frame` it just built on its own
stack — that `Frame` is dropped the instant the function returns. The
original `compare_projection` never hit this because it built its one
`Frame::Bind` and *immediately* passed it into a nested `compare_types`
call rather than returning it; generalizing to arbitrary depth means that
discipline has to hold at every level. Landed this as continuation-passing
(`k: &mut dyn FnMut(&Self, TypeRef<'_>) -> TypeComparison`), which worked
and passed all tests, but reintroduced dynamic dispatch — against the
actual point of this whole redesign (avoid machinery, stay simple).

**Second pass, replacing the first:** dynamic dispatch turned out to be
avoidable by representing "what's still left to resolve" as *data* instead
of a closure — a second small borrowed chain, `Pending<'p>`, built with the
exact same discipline as `Frame` itself (each node constructed locally,
passed straight into a nested recursive call, never returned). Concretely:

- `Pending::{Done, Step { trait_index, assoc_name, rest }}` — a stack of
  queued projection steps, most-recently-queued first.
- `resolve_and_compare(r, pending, found, path)` — peels `r` through its
  frame (`TypeParam`) or queues another step and dives into the base
  (`AssocTypeProjection`), until `r` is neither; then hands off to
  `apply_pending`.
- `apply_pending(r, pending, found, path)` — `r` is confirmed already
  irreducible on its own. If `pending` has a queued step, apply it
  (equality binding, else `find_trait_impl`, building a new `Frame::Bind`
  if needed) and recurse back into `resolve_and_compare` with the result
  and the rest of the queue. Once `pending` is `Done`, hand off to
  `compare_resolved`.
- `compare_resolved(r, found, path)` — `r` is the final answer: the old
  fast path / `compare_unresolved_type_param` / `compare_structural`
  dispatch, unchanged in substance.
- `compare_types` itself keeps the `Error`/`Infer` check, the fast path,
  and now an explicit same-shape-projection pre-check (`T::Item` vs
  `U::Item`, moved out of the old `compare_projection` since there's no
  single "projection" function left to hold it), then delegates to
  `resolve_and_compare(expected, &Pending::Done, found, path)`.

No `dyn`, no closures, no `Rc` — `grep -n "dyn \|FnMut\|FnOnce"
type_compare.rs` returns nothing. Traced `Self::Mid::Out` through the new
structure by hand before trusting it (queues `Out`, resolves `Mid`, queues
nothing further, peels `Self` via `Frame::Root`, applies `Mid` via
`find_trait_impl` producing a new `Frame::Bind`, applies `Out` via another
`find_trait_impl` chained off it, lands on a concrete leaf) — matches what
the tests confirm.

Verified against the anchor tests, identically to the first pass:
`test_nested_assoc_type_projection_mismatch_is_detected` and
`test_nested_assoc_type_projection_match_is_accepted` both un-ignored and
passing — the first now correctly reports `TraitImplSignatureMismatch`,
the second passes for the right reason (a proven match through two levels
of projection) rather than the previous silent `Indeterminate`.
`test_impl_side_projection_normalizes_against_concrete_trait_return_type`
remains `#[ignore]`d and failing, as expected — that's step 2's fix, not
this one's (`compare_types` still only ever normalizes `expected`). Full
suite: 998 passed, 0 failed, 11 ignored, `cargo fmt --check` and `cargo
clippy -p wx-compiler --no-deps -- -D warnings` both clean (modulo the
pre-existing, unrelated `needless_borrow` at `mod.rs:2464`) — identical
numbers to the CPS version, confirming the rewrite is behaviorally
equivalent, not just differently shaped.

## Step 2 — give `found` its own, narrower reduction path — done

The speculation in the original version of this section (generalize
`resolve_and_compare`/`apply_pending` to walk *either* side symmetrically)
turned out to be more machinery than the problem needed. The key
realization: `found` (the impl's own written signature) structurally
cannot need the same resolution power `expected` does. Phase 2 signature
building already eagerly flattens any projection whose base is a concrete
or composite receiver (`resolve_namespace_type_member`'s catch-all), so the
only thing that can still be unresolved in an impl's own signature by
conformance-check time is a projection based on the impl's *own*
still-abstract generic — and that generic never gets bound to a concrete
receiver during signature comparison at all (there's no receiver; we're
comparing declarations). The *only* way such a thing can reduce is a
`where { Name = T }` binding its own base declared. Never `find_trait_impl`,
never a new `Frame`.

Because it never constructs anything, `found`'s reduction doesn't share
`expected`'s lifetime problem at all — no `Pending`, no recursion into a
continuation, just a plain function returning a `TypeRef` by value:

```rust
fn reduce_found<'f>(&self, found: TypeRef<'f>) -> TypeRef<'f> {
    let &Type::AssocTypeProjection { base, trait_index, assoc_name } =
        self.types.resolve(found.index)
    else {
        return found;
    };
    let base_ref = TypeRef { index: base, frame: found.frame };
    match self.resolve_projection_via_bound(base_ref, trait_index, assoc_name) {
        Some(resolved) => self.reduce_found(TypeRef { index: resolved, frame: found.frame }),
        None => found,
    }
}
```

Wired in as a **fallback inside `compare_resolved`**, not symmetrically
up front alongside `expected` — deliberately, per the "watch for" note
that carried over correctly from the original plan: reducing `found` up
front would risk short-circuiting `compare_types`'s same-shape
alpha-equivalence check (`T::Item` vs `U::Item`) on cases where that check,
not a bound reduction, is the right way to prove equivalence. Only reached
once `expected` has resolved to something concrete/irreducible and
structural comparison is about to fail:

```rust
_ => {
    let reduced_found = self.reduce_found(found);
    if reduced_found.index != found.index {
        self.compare_types(expected, reduced_found, path)
    } else {
        self.compare_structural(expected, found, path)
    }
}
```

Verified against the anchor test:
`test_impl_side_projection_normalizes_against_concrete_trait_return_type`
un-ignored and passing. Full suite: 999 passed, 0 failed, 10 ignored,
`fmt`/`clippy` clean (same pre-existing exception as always).

## Step 3 — fast-path comment — done

Originally framed as "re-verify the invariant, because `found` can now
route through a `Frame::Bind` the way `expected` does." That premise
didn't end up applying: `reduce_found` (step 2) never constructs a
`Frame::Bind` — `found`'s frame is always exactly whatever it was at the
top-level `compare_method_signature`/`compare_assoc_const_type` call
(`&root`), unchanged through every `reduce_found` recursion, since only
`index` ever changes. A declared equality binding is a closed, static type
expression (and if it references `Self`, that's already resolved to a
concrete target at Phase 2 signature-build time, same as everywhere else)
— so `found` never gains any new frame-dependence from step 2. The "does
symmetric normalization break the fast path" concern doesn't apply,
because the implementation that shipped isn't symmetric in that sense.

Turned out to be more than a wording tighten, though: checking the actual
file, the explanatory comment didn't survive step 1's rewrite of
`compare_types` at all — there was no comment next to either fast-path
check (`compare_types`'s own, or `compare_resolved`'s), not just an
imprecise one. Rewrote it from scratch, stating the real semantic
guarantee rather than the old "never compared directly here" ordering
framing: `expected`/`found` always trace back to the same `Frame::Root`
(one call is always scoped to one trait item vs. one impl item, for one
`TraitImpl`), and any `Frame::Bind` built along the way is derived from
that same root — so if resolution ever reaches the *same* impl again
(the self-referential `impl<X: Container> Container for Wrap<X> { type
Elem = X; }` case traced during the original design discussion), the args
bound to it are necessarily an identity mapping, since unifying an impl's
own pattern against its own target always binds each parameter to itself.
Two operands can only collide on the same raw `TypeIndex` when they denote
the literal same declaration — in which case they mean the same thing
regardless of which frame object is attached to each. Added a short
pointer comment at `compare_resolved`'s fast path rather than duplicating
the full argument twice.

Comment-only change — full suite still 999 passed, 0 failed, 10 ignored,
`fmt`/`clippy` clean (same pre-existing exception as always).

## Step 4 — cheap, uncontested fixes to fold in at the same time

Not blocking on steps 1–3, but touching the same file, so worth doing in
the same pass rather than a separate one:

- ~~**Reuse one `path` buffer** across `compare_method_signature`'s
  parameter loop instead of `&mut Vec::new()` per iteration.~~ **Done.**
  Verified safe: the `recurse!` macro's `push`/`pop` is unconditional
  (pop happens before the `match result { other => return other }` that
  might propagate a failure), so `path` is always back to empty by the
  time any top-level `compare_types` call returns, success or failure.
  `path.clear()` (implicit — the same `Vec` is just reused) +
  `debug_assert!(path.is_empty())` between iterations.
- ~~**Drop the four `.clone()`/`.to_vec()` calls** on argument slices in
  `compare_structural`.~~ **Done** — the hypothesis held: the borrow
  checker accepted removing all four with no changes needed elsewhere,
  confirming they were never required now that everything here is
  `&self`, unlike `substitute_type`'s `&mut self`.
- **Bring back a `#[cfg(test)]`-visible `IndeterminateReason`.** Still
  open — not yet decided. Removed two rounds ago for being genuinely dead
  code under `-D warnings` (nothing distinguished the variants), but steps
  1–2 are exactly the kind of change that could silently regress into
  "falls back to Indeterminate again" — and the two bugs this plan exists
  to fix were *found* by hand-constructing failing examples specifically
  because nothing surfaced them earlier. Gating it so tests can assert on
  it (e.g. a `#[cfg(test)]` accessor on `TypeComparison`) avoids
  reintroducing the dead-code warning, but every concrete shape considered
  so far adds real permanent surface area (a `Cell`-based side channel on
  `Builder`, or threading an extra return value through every internal
  function) for a benefit that's mostly "insurance," the same tradeoff
  the `Frame::Root`/`debug_assert!` hardening below got declined for.
- ~~**Cheap hardening:** `Frame::Root` checking the specific `TraitIndex`
  rather than any `TypeParamOwner::Trait(_)`; `debug_assert!` around
  `args[index as usize]` and the `expected_index - expected_offset`
  subtraction in `compare_unresolved_type_param`.~~ **Declined.** Neither
  is reachable as an actual bug (traced both — safe by construction, given
  the scoping invariants that already hold), and the fix would've added a
  permanent field to `Frame::Root` (threaded through every construction
  site) for a case that can't currently happen — not worth the added
  surface area on a type that's been trending smaller every round, not
  bigger.

## Explicitly not doing

- **Threading explicit `(trait_fn_id, impl_fn_id)` context** for the
  method-generic alpha-equivalence check. A function's signature can only
  ever reference its own generic scope or its parent's inherited one, so
  the two `Function`-owned owners `compare_unresolved_type_param` ever sees
  are structurally guaranteed to be the right pair already — nothing to
  recover, nothing steps 1–2 changes about that. Raised in the last review
  round and already declined once for the same reason.
- **Method-generic bound implication checking** (an impl method requiring a
  bound the trait didn't declare). Real gap, already documented as
  deliberately deferred (`SignatureDifference`'s doc comment) — a separate
  obligation-proving concern from type equivalence, not something this pass
  needs to pick up.
- **A general frame-aware `infer_type_args`** for the repeated-pattern-
  parameter case (`impl<X> T for Pair<X, X>` matched against a receiver
  where the two positions are frame-equal but not index-equal). Already
  degrades to `Indeterminate` rather than a wrong answer, which is the
  correct fallback until this shows up in practice.

## Order of work

1. ~~Implement recursive projection resolution (step 1).~~ **Done** —
   landed as `resolve_and_compare`/`apply_pending`/`compare_resolved` plus
   the `Pending` chain, plain recursive calls, no `dyn`/closures/`Rc`.
2. ~~Give `found` its own reduction path (step 2).~~ **Done** — landed as
   `reduce_found`, called as a fallback in `compare_resolved`, no `Frame`
   involved on `found`'s side at all.
3. ~~Fast-path comment (step 3).~~ **Done** — the comment had actually
   been lost entirely during step 1's rewrite, not just left imprecise;
   rewritten from scratch stating the real semantic guarantee, plus a
   short pointer comment at `compare_resolved`'s own fast path.
4. Step 4: path-buffer reuse and the clone-removal hypothesis **done**;
   `Frame::Root`/debug-assert hardening **declined** (not worth the
   permanent surface area for a case that can't currently happen); a
   test-visible `IndeterminateReason` still **open**, undecided. Plus a
   follow-up cleanup pass: fixed a stale test comment still describing the
   discarded CPS design, inconsistent `eo`/`fo` shorthand across
   `compare_structural`'s `Pointer`/`Array`/`Slice` arms (same two letters
   meant different fields depending on the arm), and merged two redundant
   `resolve()` calls in `compare_types`. Full suite + clippy + fmt clean
   throughout, same discipline as steps 1–3.
