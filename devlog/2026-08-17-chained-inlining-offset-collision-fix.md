# 2026-08-17 — Chained-inlining flat-offset collision: fixed

Follow-on to
[2026-08-17-chained-inlining-offset-collision-investigation.md](2026-08-17-chained-inlining-offset-collision-investigation.md),
which root-caused the bug and designed (but didn't implement) two fix
candidates. Landed a fix today — a *different, simpler* design than either
candidate in that entry, arrived at by pushing on "why does this need a new
scope at all" rather than "how do we protect a new scope from colliding."
`codegen::tests::test_lerp` passes again. Full suite: 732 passed / 0 failed.

## Recap of the bug

`opt::builder::compute_locals_offsets` lets same-`parent` scopes share a
flat local-offset range, on the assumption they're mutually exclusive at
runtime — true for `if`/`else`/`match` arms, the only shape ordinary
lowering ever produces. `mir::inlining::inline_call` broke that: for every
inlined `#[inline]` call it created a *new* sibling scope (a `wrapper`
holding nothing, plus a `body_scope_offset` holding the callee's
parameters), parented at the call site. Two calls inlined at or under the
same site — sibling arguments of one expression, or two separate,
independent sweeps substituting one after another — got two such sibling
scopes, which collided: one call's `LocalSet` into its param slot silently
overwrote the other's still-needed value. Confirmed via wasmtime
(`test_lerp`'s `a + (b-a)*t` and a hand-built `calc(a,b,c,d){(a+b)+(c+d)}`
both computed wrong results).

## Two candidates considered and rejected before landing on the real fix

**Candidate A — chain the new wrapper's `parent` onto whichever of (the true
call site) or (the most recently created scope anywhere in the function) has
already reserved more space**, compared via a `scope_offset`/`scope_end`
helper mirroring `compute_locals_offsets`'s own arithmetic. Implemented
first, verified correct (731/731, including `test_lerp`) — but the user
pushed back: it's "unnecessarily complex," comparing occupied ranges to work
around a problem that shouldn't exist if the construction were honest in the
first place. In retrospect the comparison-based approach was still a proxy
for "is anything else here" rather than a structural guarantee — correct,
but not the most direct statement of the actual requirement.

**Candidate B (first attempt) — skip creating any new scope when the callee
has no state of its own** (no extra locals beyond its params, no nested
scopes, no `return`), falling back to something like Candidate A otherwise.
Required a `contains_return` tree walk and a whole second rebaser
(`RootRebaser`) just for the "skip" path. Also rejected — the user was
explicit that the wrapper scope should stay unconditional (`return` is
already handled for free by the existing `Return`→`Break` rewrite,
regardless of whether a `return` is actually present), and that a
conditional "sometimes skip" branch was exactly the kind of complexity not
wanted.

## The actual fix: don't create a new scope for the callee's own locals

The root question, once separated from "how do we protect a new scope": *why
does inlining need a new scope to hold the callee's parameters at all?* An
`if`/`else` branch needs its own scope because it's a genuine alternative —
a callee's parameters aren't an alternative to anything; they're just more
data belonging to whatever scope the call already sits in, evaluated
unconditionally, once, in sequence. So: push them there directly.

`inline_call` (`mir/inlining.rs`) now:

1. Appends the callee's *entire* root-scope locals (its parameters, and any
   `local` it declares directly in its own body) onto
   `caller_scopes[call_site_scope].locals` — not a new scope. `Vec::push`
   can't collide with itself, so a second inlined call at the same site
   (another sibling argument, or a later, unrelated sweep) simply finds more
   locals already there and gets index ranges past them, the same way a
   second ordinary `local` declaration would. Nothing to compare, nothing to
   protect.
2. Still creates a `wrapper` scope, **unconditionally**, purely as the
   `break` target for the callee's own `Return`s (via the existing
   `Return`→`Break` rewrite) — but it never holds any locals itself
   (`locals: vec![]`), so it's always safe to parent at the call site
   directly, with no comparison needed. A scope with zero locals can never
   collide with anything, regardless of what shares its offset.
3. Copies the callee's *deeper* scopes (its own nested `if`/`else`, loops —
   anything beyond its root) as before, now parented under `wrapper_scope`
   directly (`k` in the callee's own numbering → `k + wrapper_scope`; a
   parent of `0`, the callee's own root, also lands on `wrapper_scope` by
   that same formula, since the root itself was never copied — it was
   dissolved into `call_site_scope` in step 1).

This is *smaller* than either rejected candidate: no `scope_end` comparison,
no `contains_return`, no conditional "sometimes skip the scope" branch. It's
also the more honest fix in the sense the investigation entry's own
retrospective was reaching for: the bug was never really about which parent
a wrapper scope should point at — it was that inlining manufactured a scope
that didn't need to exist, and the false "these are exclusive" assumption
only ever became relevant because that scope was created as a *sibling* in
the first place.

### Rebase logic

Splicing the callee's body in now needs two different kinds of reference
rewriting instead of one uniform shift: references to the callee's own root
scope (`scope_index == 0`, in the callee's own numbering) redirect to
`call_site_scope` with `local_index` biased by wherever its locals landed;
everything else (deeper scopes) shifts by a plain `scope_offset`
(`wrapper_scope`), same as before. Generalized the existing `Rebaser` to
carry both `root_scope`/`root_bias` (for the redirect) alongside
`scope_offset` (for the uniform case) — see "Rebaser unification" below for
why this didn't end up as two separate types.

## A real (accepted) regression: one dead SSA node per inlined call at the function root

`opt::tests::test_simple_add` (`fn add(a: i32, b: i32) -> i32 { a + b }`)
hard-asserts exactly 3 SSA data nodes after inlining: `Param(0)`, `Param(1)`,
`Add`. It now produces 4 — an extra dead `Int(0)`.

Cause: `opt::builder::Builder::build_function` seeds the function's root
scope specially — every local *past* the function's own declared parameters
gets a default value before the function body runs, on the assumption
anything there is a genuine `local x = ...;` that needs a starting value
before its own `LocalSet` overwrites it. That assumption held until now
because nothing but real source-level locals ever lived past `params_count`
in the root scope. Now, when an inlined call's site *is* the function root
(true for essentially all top-level arithmetic — the common case), the
locals pushed for it land in exactly that range, and get a wasted default
value seeded before `inline_call`'s own `LocalSet` immediately overwrites
it.

Explicitly decided not to fix: harmless (nothing reads the dead node; final
WASM output is unaffected — confirmed via `test_lerp` and the arithmetic
execution tests, all correct), and the same node gets reused via
`Builder::node`'s existing CSE for any other `0`-valued literal the function
happens to need elsewhere. `test_simple_add`'s assertion and comment updated
to expect 4 nodes and explain why, rather than changing `build_function`'s
seeding to special-case this.

## Checked (and ruled out) a second instance of the same bug shape

Before accepting the design, checked whether
`mir::MIR::build_start_function` — which also combines multiple *separate*
scope trees (one per global initializer) into one synthesized function,
using the same `rebase_scope`/`Rebaser` machinery — had the identical
collision risk: two globals' own root scopes are also true siblings (both
parented at the combined start function's shared root), and
`compute_locals_offsets` would give them the same offset too.

Verified empirically (not just on paper — this exact kind of reasoning
looked right for a rejected fix candidate earlier in the day, so it earned
a real wasmtime repro before being trusted either way) with two globals,
each declaring its own locals in its initializer block. It passed. Reason:
each global's *entire* initializer — locals included — is lowered as one
self-contained `Block` expression that becomes the *value* of a
`GlobalSet`, which routes through `opt::builder::build_block_expr`'s
clone-then-discard mechanism (the same thing that makes `if`/`else`
branches safe) rather than emitting bare `LocalSet` statements as direct,
uncloned siblings the way `inline_call`'s *old* design did. Sharing an
offset is only unsafe when a scope's locals get populated by `LocalSet`s
sitting as direct siblings in another scope's block, not wrapped in their
own `Block` boundary — `build_start_function` never does that.

Added `codegen::tests::test_global_init_multiple_globals_with_own_locals_executes`
to lock this in, since the shape (two-plus globals each with their own
locals) had never actually been exercised before.

## Rebaser unification

Once `inline_call` needed a rebaser with the root-redirect capability
(`root_scope`/`root_bias`), the pre-existing `Rebaser`/`rebase_scope` (used
by `build_start_function` to combine globals' scope trees — a plain uniform
`+= scope_offset` shift, no redirect) became a special case of it: redirect
scope `0` to exactly `scope_offset` (nowhere special) with `root_bias: 0`.
Removed the old, separately-maintained duplicate tree-walk; `rebase_scope`
is now a two-line wrapper around the generalized `Rebaser`. One walk, two
uses, instead of two near-identical ones.

## State

`mir/inlining.rs`: old `Rebaser` removed, `inline_call` rewritten per
above. `opt/tests.rs`: `test_simple_add`'s node-count assertion updated
(3 → 4) with an explanatory comment. `codegen/tests.rs`: new regression
test for multi-global own-locals safety. All MIR snapshots touching
inlined-call scope shape regenerated (`cargo insta accept`) — the only
diffs are `parent`/`scope_index`/`local_index` values reflecting the new,
flatter scope shape; no structural surprises. Full suite: 732 passed / 0
failed / 4 ignored.
