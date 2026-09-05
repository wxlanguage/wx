# 2026-08-17 — Chained-inlining flat-offset collision: root cause, two fix candidates, both deferred

**Resolved same day — see
[2026-08-17-chained-inlining-offset-collision-fix.md](2026-08-17-chained-inlining-offset-collision-fix.md).**
Neither candidate below shipped as designed: 2b (`scope_offset`/`scope_end`
comparison) was implemented and verified first, then replaced with a
simpler fix after further discussion — inlining's `LocalSet`-populated
argument locals turned out not to need a new scope of their own at all, so
there was nothing left to protect against colliding with anything else's
new scope. Kept below as the historical record of the investigation that
found the root cause; the "for whoever picks this back up" section's
recommendation is superseded.

Follow-on to the "chained-inlining flat-offset collision" bug noted in
[2026-08-17-compound-assignment-implementation-and-deferred-bugs.md](2026-08-17-compound-assignment-implementation-and-deferred-bugs.md).
Went deep on root cause and two different fix designs; ultimately reverted
everything and left the bug in place, per explicit decision to stop and
document rather than land a fix today. `codegen::tests::test_lerp` and
`opt::tests::test_simple_add`'s "extra node" investigation (see the other
entry) both trace back to this same mechanism, though `test_simple_add`
itself was already fixed independently (that was the `extend_bindings`
dead-node issue, unrelated to the collision below).

## Precise root cause

`opt::builder::compute_locals_offsets` gives every scope with the same
`parent` the identical flat local-offset (`offsets[parent] +
scopes[parent].locals.len()`), on the assumption that same-parent siblings
are mutually exclusive (true for `if`/`else` branches — never simultaneously
live). This assumption is *never actually declared* anywhere in the data
model (`BlockScope` carries no "these are exclusive" marker) — it's just an
inference the optimizer makes from tree shape, and it happens to have always
held for the constructs that used to create sibling scopes.

`mir::inlining::inline_call` breaks it. For an inlined `#[inline]` call, it
builds `Block(wrapper)[LocalSet(body, 0, arg0), LocalSet(body, 1, arg1), ...,
Block(body)[...]]`, with `wrapper.parent = call_site_scope`. When a call
site's own arguments are themselves inlined calls (`(a + b) + (c + d)`), or
when an already-substituted `Block` from an *earlier, separate* inlining
sweep (a different `#[inline]` target) ends up nested inside a later one
(`a + (b - a) * t` — three different operator methods, three separate
sweeps), multiple such wrapper/body scope pairs end up as siblings under the
same `call_site_scope`, and hence get the identical offset.

The precise mechanism for why this is unsafe, traced by hand at the
`opt::builder::Builder` level (not just "same offset is bad" — the exact
reason it's bad here and not elsewhere):

- `build_block_expr`, whenever it processes *any* `Block{scope_index,...}`
  node, does `child = extend_bindings(bindings, scope_index)` — clones
  `bindings` fresh, does all its own work on that private clone, then writes
  back only `bindings[..parent_len]` (`parent_len` = `bindings.len()`
  *before* the clone) once done. Anything the nested block did beyond that
  boundary is discarded. This is why `Aggregate`, `MemoryFill`, native
  `Add`/`Sub` (which just call `build_expr` directly on each child against
  the *same*, unextended `bindings` reference) are all safe even when two of
  their children are independently-inlined calls sharing an offset: each
  child's own `Block` handling clones-and-discards, so nothing leaks between
  siblings — exactly the same mechanism that makes `if`/`else` branches safe.
- `LocalSet`'s handling is different: `ensure_bindings_capacity(bindings,
  idx+1); bindings[idx] = new_val;` — it writes *directly* into whatever
  `bindings` reference it was given, with no cloning and no bound. When a
  `LocalSet` is one of a `Block`'s own sequential statements (exactly what
  `inline_call` builds), it mutates that block's *shared* vector permanently,
  visible to every subsequent sibling statement in the same block — this is
  required for it to work at all (`local x = 1; x = x + 1;` needs the second
  statement to see the first's write).

So the collision is specific and narrow: it only happens when one inlined
call's `LocalSet`-staged argument slot shares an offset with *another*
inlined call's own internal scope, *and* both are reached through the same
shared, mutating vector rather than independent clones. That combination is
produced exclusively by `inline_call`'s own construction — nothing else in
the compiler builds a `LocalSet` targeting a scope that might share an
offset with something still needed.

## Fix candidate 1 — stop offset-sharing in the optimizer

`compute_locals_offsets` doesn't need to be this clever at all. Its output
(`locals_offsets`) has exactly one writer and one reader in the entire
codebase (`Builder::new` and `flat_index`) — fully encapsulated, confirmed
by grep. It exists solely to give `opt::builder::Builder`'s one internal
pass an O(1) flat-array lookup for "what data-flow node does this MIR local
currently hold," and is discarded the moment that pass returns. Final WASM
local count is decided entirely separately, later, by `Scheduler` — this
transient vector has zero bearing on emitted code. So:

```rust
fn compute_locals_offsets(scopes: &[mir::BlockScope]) -> Box<[u32]> {
    let mut offsets = Vec::with_capacity(scopes.len());
    let mut next = 0u32;
    for scope in scopes.iter() {
        offsets.push(next);
        next += scope.locals.len() as u32;
    }
    offsets.into_boxed_slice()
}
```

No parent-walking, no exclusivity assumption, no possible aliasing —
every scope gets a permanently disjoint range. Cost: `data_bindings` can be
modestly larger for `if`/`else`/`match`-heavy functions, purely at compile
time, with no observable effect on output.

**User's read**: this felt like patching around the real problem rather
than fixing it, and asked to reconsider at the architecture level instead —
specifically, whether the actual bug is that inlining produces a scope tree
that doesn't honestly represent what's happening (non-exclusive scopes
shaped like exclusive ones), which should be fixed at the source rather than
compensated for downstream.

## Fix candidate 2 — make inlining's own scope tree accurate

Two attempts here; the first is confirmed insufficient, the second is
hand-verified correct but unimplemented.

### 2a — thread scope through `Call`'s own arguments (insufficient)

Change `inline_expr` to return the "effective scope after processing this
expression" (unchanged unless inlining created new scopes), and have
`ExprKind::Call`'s argument loop thread that value between sibling
arguments — so a second argument's own inlining chains onto whatever the
first argument's inlining created, instead of both naively sharing
`current_scope`. Implemented (touching `inline_expr`'s signature and every
match arm to keep return types uniform, though only `Call` actually uses the
threaded value) and confirmed to fix the `(a + b) + (c + d)` case.

**But `codegen::tests::test_lerp` (`a + (b - a) * t`) still failed after this
fix.** Traced why by hand: `lerp` chains three *different* operator methods
(`f32::sub`, `f32::mul`, `f32::add`), each inlined in its own *separate*
sweep of `run_inlining_pass` (one sweep per distinct `#[inline]` target). By
the time `f32::mul`'s sweep runs, its first argument is no longer a `Call`
at all — `f32::sub`'s earlier sweep already replaced it with a resolved
`Block`. `inline_expr` processes that argument via the ordinary `Block`
match arm, not `Call`, so 2a's threading — which only updates the scope
value inside `Call`'s own handling — never sees it. `f32::mul`'s new wrapper
still naively chains onto `call_site_scope` (unaware `f32::sub`'s scope
exists), and — critically — even though the nested `Block(wrapper_sub)`'s
*own* processing individually self-corrects (its own `LocalSet` overwrite
gets superseded by the correct final assignment within its own evaluation),
`build_block_expr`'s write-back still propagates that intermediate,
already-self-corrected value back into the *enclosing* wrapper's vector at
an offset that enclosing wrapper's own earlier argument had already staked a
claim on — because that offset falls within the enclosing wrapper's
`parent_len`, i.e. inside the write-back boundary, not beyond it. Traced the
full three-level nesting by hand and confirmed this exact mechanism
reproduces `lerp`'s wrong result (computing `(b-a) + (b-a)*t` instead of
`a + (b-a)*t`). Reverted (see `git diff` on `mir/inlining.rs` — back to
exactly the pre-session state, only the pre-existing unrelated `Trunc` arms
remain).

### 2b — chain onto whichever of two candidates has the larger occupied range (verified correct, not implemented)

At the point `inline_call` is about to push a new wrapper scope, compare two
candidates and chain onto whichever already occupies more flat-index space:

```rust
fn scope_offset(scopes: &[BlockScope], mut scope: ScopeIndex) -> u32 {
    let mut offset = 0u32;
    while let Some(parent) = scopes[scope as usize].parent {
        offset += scopes[parent as usize].locals.len() as u32;
        scope = parent;
    }
    offset
}

fn scope_end(scopes: &[BlockScope], scope: ScopeIndex) -> u32 {
    scope_offset(scopes, scope) + scopes[scope as usize].locals.len() as u32
}

// in inline_call, before pushing the wrapper scope:
let last_scope = (caller_scopes.len() as ScopeIndex).saturating_sub(1);
let parent_scope = if scope_end(caller_scopes, last_scope)
    > scope_end(caller_scopes, call_site_scope)
{
    last_scope
} else {
    call_site_scope
};
```

Unlike 2a, this needs **no explicit threading at all** — `caller_scopes` is
one shared, monotonically-growing list across every sweep, so
`caller_scopes.len() - 1` at any point already reflects everything created
so far, from *any* sweep, at *any* nesting depth, automatically. Hand-traced
against both known failure cases:

- **`calc(a,b,c,d) { (a+b) + (c+d) }`**: wrapper1/body1 (for `a+b`) chain
  onto `scope0` (nothing created yet, ties, falls back correctly). Wrapper2/
  body2 (for `c+d`) compare `scope_end(scope0)=4` vs `scope_end(body1)=6` →
  chains onto `body1`, giving it range `[6,8)`, disjoint from body1's
  `[4,6)`. Wrapper3/body3 (outer `+`) compare `scope_end(scope0)=4` vs
  `scope_end(body2)=8` → chains onto `body2`, range `[8,10)` — all three
  fully disjoint.
- **`lerp(a,b,t) { a + (b-a)*t }`**: same pattern across all three separate
  sweeps — `body_sub` gets `[4,6)`, `body_mul` (chaining onto `body_sub`,
  found via the same global `caller_scopes.len()-1` comparison, correctly
  works even though `body_sub` was created in an *earlier, separate* sweep)
  gets `[6,8)`, `body_add` (chaining onto `body_mul`) gets `[8,10)` — again
  fully disjoint, no explicit propagation needed since `caller_scopes.len()`
  already captures it.

Also re-verified this doesn't regress the earlier-considered counterexample
(an inlined call inside an `if`-branch that already declared `local x`,
where the *other* branch — structurally later in the scope list but
numerically smaller — must not be chosen over the branch that actually holds
`x`): comparing `scope_end` of both candidates picks the true call-site
branch correctly there too, since its own `scope_end` (accounting for `x`)
exceeds the unrelated sibling's.

Not implemented — reverted along with 2a per explicit decision to stop and
just record findings.

## State as of this entry

`mir/inlining.rs` is back to exactly its pre-session diff (only the
pre-existing, unrelated `Trunc` unary-op arms remain — confirmed via `git
diff`). The separate `extend_bindings` dead-node fix (see the other entry)
is untouched and stays. Full suite: 715 passed / 2 failed
(`codegen::tests::test_lerp`, `tir::tests::test_stdlib_struct_field_access`
— the `char` gap), same as before this investigation started.

## For whoever picks this back up

Implement 2b (`scope_offset`/`scope_end` comparison in `inline_call`) — it's
verified correct against both known failure shapes, and it's *simpler* than
2a despite fixing more (touches only `inline_call`, not `inline_expr`'s
entire dispatch table). Add tests before or alongside the fix, since this
bug went unnoticed through all of this session's earlier operator-overloading
work:

- A white-box MIR-level test asserting no two scopes created by chained
  inlining ever occupy overlapping flat-index ranges (compute offsets the
  same way `compute_locals_offsets` does, on a `calc`-style chained-call
  case, and assert disjointness directly — would have caught this
  immediately without needing wasmtime execution at all).
- An execution-level test alongside `test_lerp`, e.g. `calc(a,b,c,d){(a+b)+(c+d)}`
  compiled and run through wasmtime with inputs chosen so a collision
  produces a detectably wrong result (as `-5,5,-5,5` did here) — covers the
  single-sweep sibling-argument case `test_lerp` alone doesn't exercise.
