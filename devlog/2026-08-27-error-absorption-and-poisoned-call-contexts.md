# Error absorption in deref, call arguments, and poisoned call contexts

A session of diagnostic-quality work, all of it one theme: an expression whose
type is already `TypeIndex::ERROR` marks a failure that has *already been
reported*, so everything downstream of it should absorb rather than re-report
— but absorbing must not mean skipping the parts of the tree that still have
something true to say.

Started from a single misreported diagnostic in `std/main.wx` and ended up
touching four distinct absorption failures, one 53-site cleanup, and a design
investigation into cascade suppression that overturned two of my own proposals.

879 `wx-compiler` tests (105 of them `codegen::`, green for the first time in
the session), 55 `wx-lsp`, 32 `wx-fmt`.

## 1 — `ptr.*` on an already-errored operand

`build_deref_expression` matched the operand's type against `Type::Pointer`
and sent *everything else* to the "not a pointer" arm, `Type::Error`
included. A binding that had already been diagnosed got a second, useless
`E1037` reading ``type `{unknown}` is not a pointer``.

Fixed with an explicit `Type::Error` arm ahead of the catch-all. The
interesting part is what it returns. `Err(())` silences the duplicate, which
is where I started — but it also propagates, and that turned out to matter.

## 2 — the right-hand side stopped being checked

With the deref returning `Err(())`, `build_assignment_expr`'s `?` on `left`
bailed before its own match ran, so in `ptr.* = value` the *value* was never
built at all. Any mistake in it went unreported.

`build_assignment_expr` already had an `ExprKind::Error` arm doing exactly the
right thing — building the RHS against `TypeIndex::ERROR` and absorbing
failures. **It was simply unreachable.** Returning an error *expression*
instead of `Err(())` made it reachable, and the RHS started being checked with
no new recovery code.

That exposed a latent cascade one level over: `build_compound_assignment_expr`
had no `ExprKind::Error` arm, so `p.* += x` fell through to the catch-all and
reported a spurious `E1013 invalid assignment target` on top of the original
error, *and* still skipped the RHS. Given its own arm now.

That arm collapses to `ExprKind::Error` rather than keeping the node shape,
which was considered and isn't possible: every compound variant carries a
resolved operator method — `CompoundAssign`/`CompoundStore` a
`method_id: ast::DefId`, the `Generic*` pair an `abstract_method_id` — and
with an errored target there is no method to resolve. `DefId(u32)`
(`ast/mod.rs:1704`) has a private field and no sentinel, so there is nothing
to put there. Plain `Assign` keeps its shape only because it has no such
field.

## 3 — why hover went blank

The reported symptom was that hovering the right-hand side showed nothing.
The cause is the same bug, one layer out: `SymbolIndex` is built from
`local.accesses`, and an access span is pushed *while an identifier expression
is being built*. An RHS that never gets built records no access, so there is
nothing at that position for `find_at_position` to return.

A/B on `fn bad(value: i32) { local p = nonexistent(); p.* = value; }`:

```
with the fix          without (Err(()))
  value accesses=1      value accesses=0
  p     accesses=1      p     accesses=1
```

Pinned by `test_poisoned_deref_store_records_rhs_access_for_hover`, kept in
`wx-compiler` rather than as a `wx-lsp` hover test: the index→hover mapping
already has three tests, the LSP harness costs ~90 lines per test, and the
precondition is better tested where it's produced.

**Standing gap, not fixed:** `SymbolKind` (`symbol_index.rs:13`) has 20
variants and every one is a *named* entity. There is no expression variant, so
hovering a call, a literal, a cast, or `a + b` shows nothing regardless of
errors. Giving those a type on hover needs a span→`TypeIndex` sidetable
populated during expression building, queried as a fallback when no symbol
matches — new machinery, deliberately deferred.

## 4 — arguments of an unresolved callee

Same shape again: `build_call_expression` and `build_method_call_expression`
both `?`'d on callee resolution, so `self.reserve(Layout::of::<T>())` reported
`E1049` and then never looked inside the argument list.

Three of four call kinds were affected. Plain calls to an undeclared function
already worked, because an unresolved bare identifier yields an error-*typed*
callee rather than `Err`, landing in a pre-existing `_` arm whose comment
already said *"still trying to check arguments, even though we don't have
information about the parameters"*. The failing paths just never reached it.

| case | before | after |
|---|---|---|
| `s.nope(missing_a(), missing_b())` | `E1049` only | `E1049` + 2× `E1007` |
| `s.x(missing_a())` — field, not method | `E1049` only | + `E1007` |
| `S::nope(missing_a())` — assoc fn | no-assoc-item only | + `E1007` |
| `nope(missing_a(), missing_b())` | already worked | unchanged |

## 5 — the `E1002` cascade, and two designs that were wrong

Checking arguments with no callee surfaced a *new* problem: an argument that
is itself a generic call, like `Layout::of::<T>()`, has nothing to infer its
type parameters from, so it reported `cannot infer type for type parameter
`M`` — asking the user to annotate their way out of a gap the missing callee
had opened.

Verified first that this was **pre-existing, not a regression**: the
undeclared-plain-function path produced the identical cascade before any of
this session's changes.

Three designs were tried and rejected, two of them mine:

**Pass `expected_type: ERROR` and let `infer_type_args` bind the slots.**
Doesn't work at all. `infer_type_args` skips `ERROR` actuals by an explicit
guard, and even with that guard removed, `Layout<M>` against `Error` matches
no structural arm, so nothing binds. Reverted.

**A `poisoned` flag on `ExprContext`.** Rejected on the grounds that
diagnostic policy shouldn't be threaded as state.

**Poison inside `infer_type_args` via a `(_, Type::Error)` arm.** Researched
in depth (subagent, claims verified independently). It *works* for the target
case but **silently loses a real error**:

```wx
fn same<T>(a: T, b: T) -> T { a }
fn f(s: S) { local p = s.missing(same(1 as i32, true)); }
```

Baseline reports `E1049` **and** `E1001` — `T` binds to `i32` from `a`, so
`b: bool` is a genuine mismatch. Poisoning inside `infer_type_args` binds
`T = ERROR` *from the result seed, before the argument-inference loop runs*,
so both arguments absorb and the real error vanishes. Initializing `type_args`
to `ERROR` has the identical flaw for the identical reason, and additionally
needs edits at four independent allocation sites (`builder.rs:3519`, `:12720`,
`:17013`/`:17017`, `mod.rs:3045`), three of which cannot see the call's
expected type.

**What landed: poison *after* argument inference**, gated on
`expected_result == TypeIndex::ERROR`, inside `build_generic_call_arguments`.
A slot still open at that point is open precisely because nothing at the call
site could constrain it — which is the exact condition `E1002` was trying to
describe.

The change is net-subtractive, because the block was already duplicating
itself. `had_unresolved` was set inside `if contains_infer(substituted_result)`
and read immediately after, so it could only ever be true when that condition
was — the flag, its second `if`, and a separate poison loop were all relaying
one condition down a scope. Collapsed into a single block where the only
difference between the poisoned and unpoisoned cases is whether the
diagnostic is emitted; the poison-and-return is shared:

```rust
if self.contains_infer(substituted_result) {
    if expected_result != TypeIndex::ERROR {
        for (i, &slot) in type_args.iter().enumerate() { /* report E1002 */ }
    }
    for slot in type_args.iter_mut() {
        if *slot == TypeIndex::INFER { *slot = TypeIndex::ERROR; }
    }
    return type_args;
}
```

Ordering is load-bearing and nothing in the type system enforces it, so
`test_poisoned_context_still_reports_mismatch_between_sibling_arguments` pins
it — it fails if poisoning ever drifts before the argument loop.

**No helper was added, twice deliberately.** The recovery loop I'd written
in `build_call_expression` was a hand-rolled copy of the `_` arm below it, so
a failed callee now becomes an error-typed expression and falls into that arm
on its own, deleting the duplicate outright. That left the method-call path as
the only site with its own loop — and a helper for one site isn't an
abstraction.

**Performance was measured, not guessed:** `infer_type_args` is called **145
times** to compile the whole stdlib, and under the rejected poisoning design
the new arm fired 0 times across 663 existing tests. No wall-clock delta above
noise. The block that landed does strictly less work than before.

## 6 — `unwrap_or` placeholder sweep

53 sites converted to bare `.unwrap()`, matching the 69 that already used it:
`tir/builder.rs` (22), `wx-lsp/src/lib.rs` (23), `completion.rs` (6),
`symbol_index.rs` (2). A symbol resolved against the interner it came from is
always `Some`; the fallbacks were papering over an impossible case with a
wrong answer.

Two flavours were doing real damage beyond cosmetics:

- **`unwrap_or("")` as a sort/lookup key.** `symbol_index.rs:149` sorts
  `global_definitions` by resolved name and `completion.rs` runs
  `partition_point`/`take_while` over that ordering — an empty fallback
  corrupts the sort and makes completions silently vanish.
- **`unwrap_or("")` as a match scrutinee.** `builder.rs:4870` matches a
  resolved attribute-arg name against `"min_pages"`/`"max_pages"`; an empty
  fallback falls to `_` and reports "invalid memory limits attribute",
  blaming the user's source for an interner bug.

Left alone: two `d.code.as_deref().unwrap_or("?")` in test helpers, where
`Diagnostic::code` is genuinely `Option<String>`.

## 7 — removed three std-math codegen tests

`f32`/`f64` math is moving out of the stdlib into a separately-installed
library, so `test_f32_scale_pow2_wasmtime`, `test_f64_scale_pow2_wasmtime`,
and `test_f32_sin_cos_agree_with_reference` no longer compile, along with the
`ulps_apart`/`monotonic` helper that existed solely for the last one.

There were **three**, not the two that were visible: the codegen harness
aborts the whole process on first failure, so the third was hidden behind the
others. Enumerated by running all 108 `codegen::` tests in separate processes.

The sin/cos test is worth moving rather than losing — a ~180-point sweep
straddling every branch of the argument reduction, checked to ≤1 ulp against
an `f64`-computed reference, plus signed-zero and NaN cases, and a comment
recording a real documented gap (`rem_pio2_large` isn't ported, so arguments
past 2^28·(π/2) return NaN by design, with an assertion pinning that).

Nothing else depends on std math: `test_f32_abs_floor_min_max_wasmtime` and
`test_float_boundary_consts_match_ieee754_exactly_wasmtime` use WASM-native
float ops and IEEE boundary consts, and still pass.

## Tests added

Six, all in `tir/tests.rs`:

- `test_deref_of_error_type_does_not_repeat_diagnostic`
- `test_deref_of_error_type_still_checks_the_assigned_value` — plain,
  compound, and field forms, plus no `E1013` cascade
- `test_unresolved_callee_still_checks_its_arguments` — method /
  field-not-method / assoc-fn
- `test_unresolved_callee_does_not_demand_a_type_annotation` — both method
  and plain-call paths
- `test_poisoned_context_still_reports_mismatch_between_sibling_arguments`
- `test_poisoned_deref_store_records_rhs_access_for_hover`

Worth noting that every design in §5, baseline included, passed the existing
suite unchanged — it had zero coverage discriminating them, which is why the
probe harness was necessary and why these tests exist.
