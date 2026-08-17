# 2026-08-16 — Pre-existing crash: `#[inline]` function calling an intrinsic

## Summary

Found while implementing the operator-overloading traits (`Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg` as pure syntax sugar over trait dispatch, `+=`-style compound assignment desugaring to `place = place.op(rhs)`, no separate `*Assign` traits). The primitive impls (`impl Add for i32 { #[inline] fn add(self, rhs) -> Self { i32_add(self, rhs) } }`, one per numeric type, backed by new `#[intrinsic]` wrappers around the raw wasm instructions) are the first code anywhere in the repo to call an `#[intrinsic]` function directly from inside an `#[inline]`-attributed function's body — and doing so panics the compiler:

```
thread 'main' panicked at crates/wx-compiler/src/mir/inlining.rs:702:26:
called `Option::unwrap()` on a `None` value
```

**Confirmed pre-existing, unrelated to the new work**: reproduced against a `git stash`-clean checkout (before any of this session's changes) using only `f32_sqrt`, an intrinsic that predates this session entirely:

```wx
use std::*;
#[inline]
fn wrapper(x: f32) -> f32 { f32_sqrt(x) }
fn my_sqrt(x: f32) -> f32 { wrapper(x) }
export { my_sqrt }
```

This alone crashes on unmodified `develop`. It was never triggered before simply because nothing in the existing codebase previously called an intrinsic from inside an `#[inline]` function's body.

## Root cause

`mir::MIR::build`'s expression lowering (`lower_expression` in `mir/mod.rs`) has four places that resolve a call target and decide whether to call `record_call_edge` (which feeds `mir.call_edges` → `CallGraph::build`'s `callees`/`callers` maps, consumed by `run_inlining_pass`'s Kahn-topological-sort inlining loop in `mir/inlining.rs`):

1. `tir::ExprKind::GenericCall` — checks `ItemAttribute::Intrinsic`, short-circuits to `lower_intrinsic` before ever reaching `record_call_edge`. Correct.
2. The "abstract trait method resolved inside a default body" arm — dispatches to the concrete impl, records an edge. Never targets an intrinsic in practice.
3. `tir::ExprKind::Call` — checks `Intrinsic`, short-circuits correctly for the intrinsic case, but **the plain non-intrinsic case never called `record_call_edge` at all** — a second, independent latent bug (ordinary non-method, non-generic calls to a `#[inline]` function would silently never actually get inlined, since no edge means the Kahn queue never learns who its callers are).
4. `tir::ExprKind::Function { id }` — resolves a bare function-value reference. This runs on the way to *every* call (lowering the `callee` sub-expression happens before the enclosing `Call`/`GenericCall` arm gets to check whether the target is an intrinsic), and **unconditionally called `record_call_edge` with no intrinsic check at all**, in both its generic/mono branch and its plain branch. This is the actual crash source.

Intrinsics are eliminated entirely during lowering — `lower_intrinsic` substitutes the whole call expression for the real MIR op (`ExprKind::Add`, `ExprKind::Trunc`, `ExprKind::MemoryGrow`, ...) directly at the call site. They never become a real `mir::Function`, by construction (they're bodiless declarations — `#[intrinsic] pub fn f32_trunc(value: f32) -> f32;` has no `{}`). `CallGraph::build` only pre-seeds `callees`/`callers` map entries for ids present in `mir.functions`, and silently no-ops (`if let Some(...)`) when an edge references a callee that never got a functions-map entry — so a spurious `caller → some_intrinsic` edge is normally harmless dead data. It only becomes fatal when the *caller* is itself `#[inline]`: the Kahn-queue loop iterates that caller's callee set unconditionally and does a bare `.unwrap()` on `graph.callers.get_mut(&callee_id)`, assuming every recorded callee has a real graph entry.

## Fix

Two-part, both in `mir/mod.rs`:

- Arm 3 (`tir::ExprKind::Call`, non-intrinsic branch): added the missing `self.record_call_edge(id);` — needed regardless, or `#[inline]` on an ordinary function called this way silently does nothing.
- Arm 4 (`tir::ExprKind::Function { id }`, both branches): added a new `is_intrinsic(&self, id: ast::DefId) -> bool` helper (checks `ItemAttribute::Intrinsic` on the resolved `tir::Function`) and guarded both `record_call_edge` calls behind `!self.is_intrinsic(...)`, matching what arms 1–2 already did.

Verified against all three repro cases (`f32_sqrt` wrapped in `#[inline]`, `f32_trunc` wrapped in `#[inline]`, and the real `impl Add for i32` calling `i32_add`) — all now compile and fully collapse through inlining to the bare wasm instruction (`i32.add`, `f32.sqrt`, `f32.trunc`), zero leftover call overhead.

## Alternative considered and rejected: make intrinsics real `#[inline]` `mir::Function`s

Instead of eager substitution during lowering, intrinsics could be materialized as ordinary `#[inline]` functions and go through the same call-graph/Kahn-inlining machinery as everything else, removing the need for arms 1–4 to special-case them individually. Rejected:

- **No performance win.** Both approaches produce identical final wasm. Eager substitution is already *stronger* than `#[inline]` — guaranteed 100% elimination during the first lowering pass, before any graph/cycle logic runs. `#[inline]` here only means "eligible for the Kahn-queue pass," which can lose a function to the mutual-recursion cycle-breaker's "evict one anchor" step (see `run_inlining_pass`'s outer loop) — an intrinsic evicted that way would survive as a literal `Call` node into codegen with no real function behind it. The current design makes that structurally impossible; the alternative would have to explicitly rule it out.
- **Real new machinery, not a deletion.** Several intrinsics are generic (`memory_grow<Mem: Memory>`, `slice_len<Mem, T>`, `size_of<T, Mem>`) and today get specialized per call site for free using whatever `current_substitutions` are already live in the calling context. Turning them into standalone functions means giving them their own `mono_registry`-style monomorphization identity — genuinely new code, not a simplification.
- Net: bigger diff, new correctness surface, no upside. Kept the narrow fix.

## Context for future sessions

- Relevant code: the four call-dispatch arms in `lower_expression` (`mir/mod.rs`, search `record_call_edge`), `is_intrinsic` (new, next to `record_call_edge`), `CallGraph::build`'s silent `if let Some(...)` drop (`mir/inlining.rs`), the Kahn-queue loop's `f_callees` iteration and cycle-breaker (`mir/inlining.rs`, `run_inlining_pass`).
- Motivating call site: `std/main.wx`'s new primitive `Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg` impls (one per numeric type, all `#[inline]`, all calling a raw `#[intrinsic]` wrapper directly) — part of the still-in-progress operator-overloading feature (traits as pure sugar, no `*Assign` traits, `+=` desugars to `place = place.add(rhs)` reusing the existing place-based compound-assignment machinery).
- If arm 2 (abstract trait method dispatch) is ever changed to allow resolving to an intrinsic, it needs the same `is_intrinsic` guard — not an issue today since trait default-body dispatch never targets one, but worth remembering if that assumption changes.
