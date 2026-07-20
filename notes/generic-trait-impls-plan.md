# Generic Trait Impls — Implementation Plan

> **Status: DONE. AST, TIR, MIR, and monomorphization all working, 633
> tests passing** (no dedicated codegen/WASM test yet — see "What actually
> landed" for why that's a reasonable place to stop). The registry design
> actually implemented is simpler than originally planned below: a single
> unified `trait_impl_dispatch` map, not a two-tier exact/coarse split — see
> "What actually landed" after the Steps section before reading Steps 5-8,
> which describe the originally-planned (superseded) shape. The
> "Remaining: MIR/codegen stage" section that used to be here has been
> folded into "What actually landed" now that it's finished.

Goal: support `impl<T> Trait for Type<T> { .. }`, including bounded params
(`impl<T: Foo> Bar for Vec<T> { .. }`) and impls that introduce a param the
struct doesn't itself have. Generic *inherent* impls (`impl<T> Container<T> { .. }`)
already work end-to-end and are the template this plan mirrors — see "Current
state" below for exactly what exists today and what's missing.

Related: [trait-dispatch-followups.md](./trait-dispatch-followups.md) covers
open issues in the surrounding trait-dispatch machinery (ambiguity spans,
`AssociatedType::def_span` `todo!()`) that this work will brush up against
but doesn't need to fix.

---

## Current state (verified against the tree)

**Parser gap — the actual blocker.** `parse_impl_item` (`ast/mod.rs:4618`)
parses `<T>` into a local at line 4621 unconditionally, before it knows
whether `for` follows. The `InherentImpl` branch (return at `ast/mod.rs:4683`)
threads that local through as `type_params`. The `TraitImpl` branch (return
at `ast/mod.rs:4660`) never references it — silently discarded.
`Item::TraitImpl` (`ast/mod.rs:1596`) has no `type_params` field to put it in
even if it weren't discarded; `Item::InherentImpl` (`ast/mod.rs:1589`) does.

**TIR mirrors the gap.** `TraitImpl` (`tir/mod.rs:377`) has no `type_params`,
unlike `ImplBlock` (`tir/mod.rs:1121`), whose doc comment already frames
concrete impls as "the degenerate (zero-parameter) case" of one shape —
exactly the model to extend to trait impls.
`TypeParamOwner::TraitImpl(TraitImplIndex)` (`tir/mod.rs:65`) exists but its
own doc comment says outright it isn't yet a source of `own_params`; the
three sites that would look this up all return `&[]`
(`tir/builder.rs:2323`, `2492`, `3045`).

**Registries are the wrong shape for generic impls.** Inherent-impl dispatch
is two-tier: `impl_block_dispatch: HashMap<(ImplTarget, SymbolU32), Vec<u32>>`
(`tir/mod.rs:1933`) is a coarse bucket keyed on outer type constructor +
member name, and `Builder::match_impl_block` (`tir/builder.rs:8449`) unifies
each candidate block's `target` against the actual receiver to decide which
ones really apply and what the type-arg substitution is. Trait-impl dispatch
has no equivalent: `trait_impl_lookup: HashMap<(TypeIndex, TraitIndex),
TraitImplIndex>` and `type_trait_impls: HashMap<TypeIndex, Vec<TraitImplIndex>>`
(`tir/mod.rs:1940`, `1964`) are keyed by **exact** `TypeIndex` — `Foo<i32>`
and `Foo<bool>` are unrelated keys, with no unification step. The doc comment
on `type_trait_impls` (`tir/mod.rs:1941-1959`) already flags this as needing
reconsideration once generic trait impls are designed.

**Three call sites read those exact-keyed maps directly** and all three need
to change together:
1. `resolve_impl_member`'s trait branch (`tir/builder.rs:12295-12326`) — the
   main dispatch path for `.method()`/`Type::CONST` on a trait member. Always
   returns `type_args: Box::new([])` in `MemberLookup::Trait`
   (`tir/builder.rs:12336`) since there's currently never anything to
   substitute.
2. `check_assoc_type_bounds` (`tir/builder.rs:7628`) — checks
   `trait_impl_lookup.contains_key(&(concrete_ty, bound.trait_index))`
   (`tir/builder.rs:7649-7651`) to verify a `where { AssocType = RhsType }`
   binding's RHS actually implements a required bound.
3. **MIR's abstract-method dispatch**, `mir/mod.rs:1908-1937` — when a
   trait's default method body calls an abstract method on `Self`, MIR
   resolves the now-concrete `Self` type directly against
   `self.tir.trait_impl_lookup.get(&(concrete_self, trait_index))`
   (`mir/mod.rs:1922-1926`), `.expect()`-ing a hit. This is the one call site
   in a *different crate module* than the other two — important, see Step 6.

**Registration.** `AstNodeRef::TraitImplBlock` (`tir/builder.rs:5166-5236`)
resolves the trait name and target type in one single-phase step, with
`self.resolve_type(resolve_context, None, target)` (`tir/builder.rs:5202-5203`)
— note the `None` generic scope. This is why the existing (unasserted) probe
test, `test_generic_trait_impl_probe` (`tir/tests.rs:8510-8537`, writing
`impl<T> Getter for Box<T> { .. }`), produces `"undeclared type"` for `T`
today: there is no scope in which `T` is a declared type parameter at the
point the target is resolved. Compare with `ast::Item::InherentImpl`'s
pre-scan handling (`tir/builder.rs:3642-3677`), which is a proper two-phase
split: push an `ImplBlock` with `target: TypeIndex::ERROR` immediately, plus
a separate `AstNodeRef::InherentImplBlock` init node; then in Phase 2
(`tir/builder.rs:4454-4499`) resolve bounds via `resolve_type_param_bounds`
and the target via `resolve_signature_type` under
`GenericScope { owner: TypeParamOwner::ImplBlock(block_index), .. }` — so `T`
already exists as a declared param by the time the target expression is
resolved. `TraitImplBlock` needs the identical split.

**Member registration already assumes the split will happen.**
`AstNodeRef::TraitImplFunction`/`TraitImplConstant`/`TraitImplAssocType`
(`tir/builder.rs:5237-5482`) already build their `GenericScope` with
`owner: TypeParamOwner::TraitImpl(trait_impl_index)` — the plumbing for
`Self` resolution inside trait-impl bodies is already generic-shaped. What's
missing is exactly what `InherentImplFunction`'s phase-2 handling
(`tir/builder.rs:4305-4453`) does that `TraitImplFunction` doesn't yet:
reading `inherited_type_param_count` off the block
(`tir/builder.rs:4327-4330`), setting `type_param_parent`
(`tir/builder.rs:4350-4353`), and registering into a coarse dispatch bucket
(`tir/builder.rs:4444-4452`).

**Monomorphization needs no changes.** `MonoRegistry` (`mir/mod.rs:722-752`)
is keyed by `(ast::DefId, Box<[TypeIndex]>)` — fully agnostic to whether the
`DefId` is a free function, a generic inherent-impl method, or a generic
trait-impl method. `GenericMethodCall` lowering (`mir/mod.rs:1878-1937`)
already resolves `TypeParam` entries in `type_args` through
`current_substitutions` before calling `mono_registry.get_or_insert`. Once
TIR emits correct `type_args` at trait-impl-method call sites, this path
works unchanged — confirmed by reading the full lowering function, not
inferred.

**Associated types.** `ImplEntry::AssociatedType { ty: TypeIndex }`
(`tir/mod.rs:1104` region) stores an already-resolved concrete type. For
`impl<T> Trait for Type<T> { type Assoc = T; }`, `ty` just needs to be able
to hold a `Type::TypeParam` referencing the trait-impl's own param, then flow
through the same `substitute_type` machinery that already substitutes struct
fields and method signatures. No new representation needed.

---

## Design decision: mirror `ImplBlock`'s dispatch shape (not a parallel system)

Considered and rejected: keeping the exact-key registries as the primary
path and bolting a fallback scan onto them for generic impls. That still
needs unification and bound-checking to exist *somewhere*, so it isn't
actually less work — it just ends up as a second, differently-shaped dispatch
path to maintain alongside the inherent-impl one, which is exactly the kind
of thing that needs revisiting later (the `type_trait_impls` doc comment
already flags this risk). Instead: give `TraitImpl` real `type_params`,
build a coarse `(ImplTarget, TraitIndex)`-keyed bucket the same way
`impl_block_dispatch` is `(ImplTarget, SymbolU32)`-keyed, and write
`match_trait_impl` as `match_impl_block` plus a bound-check pass. One
dispatch shape, one mental model, for both impl kinds.

Scope decision, stated explicitly rather than left implicit: bound-checking
an inferred type arg against a trait-impl's declared bounds
(`impl<T: Foo> Bar for Vec<T>` — does the inferred `T` actually implement
`Foo`?) is checked by existence in the trait-impl registry (one level,
reusing whatever the concrete-or-generic lookup already resolves to). Full
recursive constraint propagation across chains of generic bounds (Rust's
trait solver) is out of scope — not because it's undesirable, but because
nothing in the current bound-checking machinery
(`check_typeset_bounds_on_type_args`, `tir/builder.rs:11582`) does that
either, and inventing it isn't required to make `impl<T: Foo> Bar for Vec<T>`
work correctly for the common case.

---

## Steps

### Step 1 — Parser (`ast/mod.rs`)
Add `type_params: Box<[TypeParam]>` to `Item::TraitImpl` (`ast/mod.rs:1596`).
In `parse_impl_item` (`ast/mod.rs:4618`), thread the already-parsed local
`type_params` (line 4621) into the `Item::TraitImpl` construction at line
4660 instead of dropping it — mechanical, mirrors what the `InherentImpl`
branch already does at line 4685.

### Step 2 — TIR data model (`tir/mod.rs`)
Add `type_params: Box<[TypeParamInfo]>` to `TraitImpl` (`tir/mod.rs:377`),
same shape as `ImplBlock::type_params`. Update the three `&[]` stubs at
`tir/builder.rs:2323`, `2492`, `3045` to read
`&self.tir.trait_impls[idx as usize].type_params` instead — same pattern
`ImplBlock`'s arm already uses alongside them.

### Step 3 — Two-phase registration (`tir/builder.rs`)
Split `AstNodeRef::TraitImplBlock`'s current single-phase handling
(`tir/builder.rs:5166-5236`) into pre-scan + Phase 2, mirroring
`ast::Item::InherentImpl` (`tir/builder.rs:3642-3677`) /
`AstNodeRef::InherentImplBlock` (`tir/builder.rs:4454-4499`) exactly:
- **Pre-scan**: push a `TraitImpl` with `target: TypeIndex::ERROR` and the
  parsed `type_params` immediately (trait name is still resolved eagerly
  here — the trait itself is never generic over the impl's own params, so
  there's no ordering hazard resolving it early). Push a new
  `AstNodeRef::TraitImplBlock` init node carrying `impl_type_params` +
  `impl_target`, same as `InherentImplBlock` carries them.
- **Phase 2**: `resolve_type_param_bounds` for the trait-impl's own params
  under `TypeParamOwner::TraitImpl(idx)`, then resolve the target via
  `resolve_signature_type` under
  `GenericScope { owner: TypeParamOwner::TraitImpl(idx), self_type: None }`
  — this is the one-line fix that makes `T` in `Box<T>` resolvable, since by
  this point `T` is a declared param under that owner.

### Step 4 — Member registration (`tir/builder.rs:5237-5482`)
In `AstNodeRef::TraitImplFunction`, add the two lines
`InherentImplFunction`'s phase-2 handling already has
(`tir/builder.rs:4327-4330`, `4350-4353`) that `TraitImplFunction` is
currently missing: read `inherited_type_param_count` off
`trait_impls[trait_impl_index].type_params.len()`, and set
`type_param_parent: Some(TypeParamOwner::TraitImpl(trait_impl_index))`
(already partially there — currently hardcodes `inherited_type_param_count: 0`
at `tir/builder.rs:5277`; needs to read the real count instead). Do the
analogous thing for `TraitImplConstant`/`TraitImplAssocType` where relevant
(associated types/consts don't have their own further type params, but their
resolution still needs the impl's params in scope via the existing
`GenericScope` — already correct there, no change needed beyond Step 3
making the scope's params real).

### Step 5 — Coarse dispatch registry (`tir/mod.rs` + `tir/builder.rs`)
Add `trait_impl_dispatch: HashMap<(ImplTarget, TraitIndex), Vec<TraitImplIndex>>`
next to `impl_block_dispatch` (`tir/mod.rs:1933`) — same coarse-bucket idea,
keyed by trait instead of member name (a trait impl's members are fixed by
the trait, so bucketing finer than "this outer shape implements this
trait" isn't needed the way `impl_block_dispatch` needs per-name buckets
across many separate inherent impl blocks). Populate it in
`AstNodeRef::TraitImplFunction`'s phase-2 handling (or once per trait-impl
block, whichever is simpler — the block-level target is known by Step 3),
mirroring `tir/builder.rs:4444-4452`. Leave `trait_impl_lookup`/
`type_trait_impls` untouched — they remain the exact-key fast path for
concrete impls; the new map only holds impls with non-empty `type_params`.

### Step 6 — Shared unification helper, exposed to MIR
`Builder::infer_type_args` (`tir/builder.rs:6517`) and the pattern in
`match_impl_block` (`tir/builder.rs:8449-8464`) only read `&self.tir` — no
other `Builder` state. Hoist the core into a function callable from outside
`tir::builder` (a free function taking `&TIR`, or an `impl TIR` method) —
this is necessary, not optional, because **Step 8's MIR call site is not in
`tir::builder` and cannot see `Builder`'s private methods**; `mir/mod.rs`
today only ever touches public `TIR` fields directly (e.g.
`self.tir.trait_impl_lookup.get(...)` at `mir/mod.rs:1922`), never
`tir::builder::Builder`. Write `match_trait_impl(tir: &TIR, impl_idx:
TraitImplIndex, receiver_ty: TypeIndex) -> Option<Box<[TypeIndex]>>` on top
of the hoisted unification core, plus the bound-check pass (Step 6b): for
each inferred type-arg slot with a trait bound, confirm it via the
concrete-or-generic trait-impl lookup (recursing into this same function for
nested generic receivers) — reject the candidate (return `None`) if any
bound fails, the same way `match_impl_block` reports "doesn't apply at all"
via `None`.

### Step 7 — Rewire `resolve_impl_member`'s trait branch
Replace the exact `type_trait_impls.get(&ty)` scan
(`tir/builder.rs:12295-12326`) with: exact-key concrete impls (unchanged,
still fast) **plus** a scan over `trait_impl_dispatch.get(&(kind, trait))`
for every trait reachable from the target (in practice: iterate
`trait_impl_dispatch` entries whose key's `ImplTarget` matches `ty`'s shape;
tightening this to avoid a full-map scan is a reasonable follow-up but
correctness-first is fine to start), running `match_trait_impl` per
candidate. On a match, thread the real type args into
`MemberLookup::Trait { type_args, .. }` instead of the hardcoded
`Box::new([])` (`tir/builder.rs:12336`).

### Step 8 — Fix the other two exact-key call sites
- `check_assoc_type_bounds` (`tir/builder.rs:7649-7651`): fall back to
  `match_trait_impl` over `trait_impl_dispatch` when the exact-key
  `contains_key` check misses.
- MIR's abstract-method dispatch (`mir/mod.rs:1922-1926`): same fallback,
  now reachable because Step 6 exposed the matcher outside `tir::builder`.
  This is the site most likely to be missed if this plan isn't followed
  literally — it's the only trait-impl-registry consumer outside the TIR
  module, and its current `.expect("no impl found for abstract trait
  method")` will start panicking on legitimate generic-impl programs the
  moment Step 3 makes them typecheck, unless this is fixed in the same pass.

### Step 9 — Associated types
No new representation. Confirm `ImplEntry::AssociatedType`'s stored `ty` can
already hold a `Type::TypeParam` under `TypeParamOwner::TraitImpl` (it can —
it's resolved through the same `resolve_type`/`GenericScope` path as
everything else once Step 3 lands), and that every consumer of that `ty`
(assoc-type projection resolution, `substitute_type` call sites) receives
the trait-impl's inferred `type_args` from Step 7 to substitute with.

### Step 10 — Verify monomorphization needs nothing
Expected to be a no-op per the "Current state" analysis above. Confirm with
a test (Step 11) rather than assuming.

### Step 11 — Tests
- Convert `test_generic_trait_impl_probe` (`tir/tests.rs:8510-8537`) from an
  `eprintln!`-only probe into a real assertion (empty diagnostics,
  snapshot).
- Add a bounded case: `impl<T: Foo> Bar for Vec<T>` where `T = ConcreteType`
  satisfies/fails `Foo`, asserting the bound is enforced.
- Add an MIR test exercising a generic trait-impl method call through to a
  monomorphized function, confirming `MonoRegistry` behaves as predicted.
- Add an ambiguity case: two applicable trait impls for the same receiver
  (e.g. a concrete `impl Show for Foo<i32>` coexisting with a generic
  `impl<T> Show for Foo<T>`) to confirm `AmbiguousTraitMember` still fires
  correctly rather than silently picking one.
- Add a codegen/WASM-level test for the abstract-dispatch-inside-default-body
  path specifically (Step 8's MIR fix) — this is the easiest piece to get
  right in TIR but wrong in MIR, since it's a different crate module maintained
  somewhat independently of the TIR registries.

### Step 12 — Snapshots
`INSTA_UPDATE=always cargo test -p wx-compiler` then `cargo insta review`.
Any existing trait-impl snapshot (TIR/MIR) is unaffected in shape (new
`type_params: []` field only appears non-empty for genuinely generic impls),
so this should be a small, reviewable diff — not a repo-wide snapshot reset
like the `std/lib.wx`-touching case.

---

## What actually landed (supersedes Steps 5-8 above)

Steps 1-4 and 9 landed close to as planned. Steps 5-8 changed shape midway
through implementation, in response to a fair question: with two registries
(`trait_impl_lookup`/`type_trait_impls` exact-keyed, plus a new
`trait_impl_dispatch` coarse-keyed for generics only), every one of the five
consumer call sites would need an "exact hit, else fall back to the coarse
scan" branch — real duplication, not less work than unifying. So the
two-tier design was dropped in favor of one:

- **`trait_impl_lookup` and `type_trait_impls` were deleted outright.** The
  only field left is `trait_impl_dispatch: HashMap<ImplTarget,
  Vec<TraitImplIndex>>` (`tir/mod.rs`) — every trait impl, concrete or
  generic alike, coarsely bucketed by outer type constructor only (**not**
  paired with `TraitIndex` in the key, unlike this doc's original Step 5: a
  type rarely has more than a handful of trait impls of any kind, so a cheap
  linear scan filtering by trait index is simpler than a second key
  component). Mirrors `impl_block_list`/`impl_block_dispatch`'s treatment of
  inherent impls exactly — concrete impls are just the zero-param case, no
  separate fast path needed because `match_trait_impl`'s zero-param branch
  already degenerates to exact `TypeIndex` equality.
- **`TIR::find_trait_impl(ty, trait_index) -> Option<(TraitImplIndex,
  Box<[TypeIndex]>)>`** is the single entry point every consumer calls
  instead of reading a map directly — used by `check_assoc_type_bounds`,
  the supertrait-conformance check in `check_trait_conformance`, the
  `AssocTypeProjection` substitution arm in `Builder::substitute_type`, and
  both MIR call sites.
- **`infer_type_args`, `type_param_typeset_bound`, and
  `concrete_type_in_typeset` were moved from `tir::builder::Builder` to
  `impl TIR`** (not just duplicated) — their bodies only ever read
  `&self.tir`/`&self` fields already, so this was a mechanical,
  behavior-preserving move. This is what let `mir::Builder` (which only ever
  holds `&TIR`, never `tir::builder::Builder`) call `find_trait_impl`
  directly without a second copy of the unification logic. Every original
  call site in `tir::builder::Builder` (11 for `infer_type_args`, 3 for the
  typeset helpers) was updated to `self.tir.foo(...)` instead of `self.foo(...)`.
- **Bound-checking** (`TIR::match_trait_impl`) came out simpler than
  Step 6 described: for each inferred type-arg slot, a trait bound is
  checked via `self.find_trait_impl(arg_ty, bound.trait_index).is_some()`
  (naturally recursive — this is what gives one-level-deep bound chains for
  free without extra code) and a typeset bound via
  `self.concrete_type_in_typeset(...)`. Any slot still `TypeIndex::INFER`
  after unification is treated as "doesn't apply" (`None`), since — unlike
  inherent-impl methods, which can receive extra type args from a turbofish
  or the call's own arguments — a trait impl's params have no other source
  to be filled from; letting `INFER` through would eventually reach
  MIR/codegen, which must never happen.
- **Associated-type substitution through a generic impl works in TIR**
  (verified by `test_generic_trait_impl_associated_type_substitutes`):
  `Builder::substitute_type`'s `AssocTypeProjection` arm now calls
  `find_trait_impl`, then substitutes the found impl's stored associated
  type through the returned `type_args` via a recursive
  `self.substitute_type(concrete, &impl_type_args)` call — this works
  because TIR-build time has full `&mut self`/interning access. **MIR's
  equivalent (`resolve_tir_type`'s `AssocTypeProjection` arm) is narrower —
  see "Remaining" below.**

---

## MIR stage — what it took (both earlier gaps fixed)

Both gaps flagged in the original version of this section are fixed, with
tests (`mir/tests.rs`): `test_generic_trait_impl_abstract_dispatch_monomorphizes`
and `test_generic_trait_impl_composite_associated_type_monomorphizes`.

1. **Abstract-method dispatch now monomorphizes generic impls.** The
   `GenericMethodCall` lowering's abstract-dispatch branch (`mir/mod.rs`,
   `tir_func.body.is_some() == false` case) used to call the impl method's
   bare TIR `id` directly, which is only valid for a concrete impl (whose
   method has zero *total* type params and was eagerly emitted by
   `MIR::build`'s main loop). A generic impl's method has
   `total_type_param_count() > 0` (once `inherited_type_param_count` was
   wired up correctly — see the AST/TIR section above) and so is *never*
   eagerly emitted; the fix branches on whether `find_trait_impl`'s returned
   `impl_type_args` is empty, and when it isn't, routes through
   `mono_registry.get_or_insert(impl_func_id, impl_type_args)` — the same
   mechanism the `body.is_some()` branch beside it already used.
2. **Composite associated-type values now substitute correctly.**
   `resolve_tir_type` (which returns a `tir::TypeIndex`) genuinely cannot
   represent a substituted composite (e.g. `type Assoc = Box<T>;`) without
   interning a new type, which is unavailable to MIR's frozen `&TIR`. The
   fix doesn't try to make `resolve_tir_type` do this — it keeps that
   function leaf-only (documented as such) and instead moves the general
   case into `lower_type_index`'s own `AssocTypeProjection` arm, which is
   `&mut self` and returns a `mir::Type` directly (never needing a new
   `tir::TypeIndex` at all): it looks up the impl and its stored assoc-type
   value via a new shared `find_assoc_type_value` helper, temporarily swaps
   `current_substitutions` to the impl's own `impl_type_args`, and recurses
   into `lower_type_index(assoc_ty)` — which already knows how to resolve a
   `TypeParam` leaf nested inside a `Struct`'s `args` (via
   `ensure_aggregate_for_struct`, which does the identical
   swap-and-recurse trick for ordinary generic structs). Same technique
   the codebase already used elsewhere, applied to a new spot.

**A real bug found and fixed along the way, unrelated to either gap
above:** `resolve_impl_member`'s trait-impl-scan loop was using the
*matched impl's* `type_args` (from `match_trait_impl`) for every candidate
regardless of where the candidate's `entry` actually came from. That's only
correct when `entry` is the impl's own override (whose method inherits the
impl's param scheme). When `entry` instead falls back to the trait's own
default body (`type_param_parent = Trait(trait_index)`, a *different*
owner with its own independently-indexed param scheme — just the receiver
type as `Self`), using the impl's `type_args` substituted the impl's own
`T` where `Self` belonged. Caught by
`test_generic_trait_impl_abstract_dispatch_monomorphizes`, which failed
with `"no impl found for abstract trait method"` until fixed — an
`i32`-vs-`Box<i32>` mismatch feeding into `find_trait_impl` downstream in
MIR. Fixed by tracking which owner produced `entry` and choosing `[ty]`
(just the receiver) instead of the impl's own args for the trait-default
case.

**A pre-existing false-positive "unused function" warning, also found and
fixed, also unrelated to generic impls specifically:** any method reached
*only* through abstract trait dispatch — a trait default calling an
abstract method on `Self`, or a bounded-generic function calling one on its
type param — was flagged `never used` by `report_unused_items`, even when
genuinely called, because TIR only ever recorded an access against the
*trait's* abstract declaration's `Function`, never against whichever
concrete/generic impl's method actually runs (decided dynamically, at MIR
monomorphization time). Confirmed pre-existing and unrelated to this
feature by running the already-in-the-suite concrete-impl test
`test_unused_trait_impl_eliminated_by_dce` with diagnostics printed: it
already silently emitted this exact false positive for `Num1::value`
(despite `Num1::value` being the entire point of that test) — nobody had
noticed because that test never asserted on diagnostics. Fixed with a new
`Builder::record_abstract_dispatch_access` (`tir/builder.rs`), called from
`resolve_impl_member`'s `Type::TypeParam` branch whenever the resolved
entry has no body anywhere (`entry_has_body(entry) == false` — the AST-based
check, not `Function.body.is_some()`, for the same phase-ordering-safety
reason `entry_has_body` itself already avoids the TIR-level field): it
walks every impl of that trait and records a conservative access on
whichever one provides the member, since dynamic dispatch means any of
them could be the real target. Over-conservative by design (DCE, a later
and far more precise MIR-level pass over actual call-graph edges, is what
determines genuine reachability) — this is only about not falsely warning
in the editor/CLI.

**Deliberately not done: a dedicated codegen/WASM-level test.** The two new
MIR tests confirm monomorphization produces the right *functions* and
*aggregates*; they don't run the result through `codegen::Builder::build`
and disassemble the WASM output. Given codegen consumes MIR's `Function`/
`Type`/`Aggregate` structures generically (nothing in `codegen/mod.rs` is
trait-dispatch-aware — by the time codegen runs, generic trait impls have
already been fully resolved into ordinary monomorphized `MIR::Function`s
indistinguishable from any other), this was judged low-value relative to
the MIR-level tests already in place. Worth adding if codegen-level
regressions in this area ever show up in practice.

---

## Explicitly out of scope / deferred

- **Coherence/orphan rules** — no checking today that two generic trait
  impls could never simultaneously apply (Rust's overlap checking). The
  ambiguity diagnostic (ad-hoc, at the point a member is actually looked up)
  covers the practical case; a static "these two impls could theoretically
  conflict" analysis is real work belonging to a separate design pass, not a
  necessary part of getting one generic impl to work correctly.
- **Specialization** (a concrete impl always beating an applicable generic
  one, resolved statically rather than via ambiguity error) — not evaluated
  here at all, would need its own decision.
- **Recursive multi-hop bound solving** — see the scope note under "Design
  decision" above.

---

## Risk areas

| Area | What to watch |
|---|---|
| MIR abstract-dispatch site (`mir/mod.rs:1922-1926`) | Easiest step to forget — it's the only trait-impl-registry consumer outside `tir::builder`, currently `.expect()`s and will panic (not silently misbehave) on any program this feature is meant to newly accept, if Step 8 is skipped. |
| `Builder::infer_type_args`/`match_impl_block` visibility | Confirm the hoisted Step 6 helper genuinely has no hidden `Builder`-only dependency before wiring MIR to call it — re-read the full recursive body, not just the top-level match arms already sampled here. |
| Bound-check false negatives on nested generics | `impl<T: Foo> Bar for Vec<T>` where the caller's own `T` is itself a still-unresolved type param (nested generic function calling into the impl) — `check_typeset_bounds_on_type_args` already special-cases `Type::TypeParam` actuals (`tir/builder.rs:11606-11610`) for the typeset case; `match_trait_impl`'s bound check needs the equivalent "forward the caller's own bound, don't fail outright" handling for trait bounds. |
| Ambiguity diagnostics spans | `trait-dispatch-followups.md`'s open `AssociatedType::def_span` `todo!()` (`tir/mod.rs:1104-1108`) becomes easier to hit once generic trait impls with associated types exist — worth fixing alongside, or at least confirming it isn't newly reachable by the added tests in Step 11. |
| `trait_impl_dispatch` scan cost in Step 7 | Starting with a full-map scan (rather than a tighter `ImplTarget`-first index) is fine for correctness but revisit if it shows up in compile-time profiling later — not a correctness risk, just a documented shortcut. |
