# Lowering correctness worklist

Status: in progress. Initial review: 2026-11-04, following `dc37bda`.

## Goal and working rules

Make checked WX programs produce correct observable results through the complete
TIR → MIR → opt → Wasm pipeline before extending the supported subset.

- Work through cases individually: reproduce, add a failing execution regression,
  implement a focused fix, and record validation here.
- Preserve evaluation order, number of evaluations, traps, and reads/writes of
  runtime state, including expressions whose values occupy no Wasm slots.
- Keep semantic decisions with their existing owner. Do not duplicate type/layout
  logic, introduce compensating side tables, or disable verifiers to hide a bug.
- Stop and ask the owner before substantial architectural changes or unresolved
  semantic/design choices. Prefer an explicit invariant to a local workaround.
- Test both lowered-only and inlined MIR where a transformation can change the
  outcome. The current CLI and the lowering test harness run different pipelines.
- General MIR DCE (`mir-dce.md`), memory support, and example migration are separate
  follow-ups, not prerequisites for fixing the cases below.

The review's baseline was 1,185 passing compiler tests, including 168 lowering
tests. Passing tests do not establish correctness for these additional cases.

## Cases

### C01 — Zero-sized tuple elements must still execute

Status: **fixed**.

With `mark()` incrementing a global and returning `()`:

```wx
local _ = (mark(), mark());
```

Expected: two increments in written order. Observed: no increments.

Cause identified in `tir/lower.rs`: tuple lowering immediately returns `Noop`
when the lowered representation is `Unit`, even for a nonempty tuple whose
elements all have zero-sized representations.

Regression coverage should include effects, written order, a trapping element,
and nested zero-sized values. Preserve the zero-slot ABI; do not invent runtime
storage for zero-sized values.

Implemented: removed the representation-based early return. All tuples now use
the existing element/aggregate lowering path, which already sequences effects
and erases only zero-sized values. No IR or layout changes were needed.

Three new execution regressions in `tir/lower.rs` all failed before the fix:

- `zero_sized_tuple_elements_execute_once_in_written_order`: observed `0` instead
  of `12`; also checks the zero-slot parameter/result ABI.
- `zero_sized_tuple_elements_preserve_nested_effects`: observed `0` instead of
  `123`; includes nested tuples and a zero-sized struct.
- `zero_sized_tuple_elements_preserve_traps_and_stop_later_effects`: failed to
  trap; also checks that only effects before the trap execute.

All three now pass both without inlining and with the default inliner. Added an
optional-policy test helper; existing tests still use their previous default.

Validation:

- Before: `cargo test -p wx-compiler zero_sized_tuple_elements` — 3 failed.
- After: `cargo test -p wx-compiler` — **1,188 passed, 2 ignored**.
- `cargo fmt --all -- --check` and `git diff --check` — passed.

### C02 — Trapping operations must not disappear or move past effects

Status: **fixed using the owner-approved control/result split**.

```wx
func discarded(x: i32) -> i32 {
    local _ = 1 / x;
    42
}
```

Expected with `x = 0`: trap. Observed: returns `42`.

```wx
local y = 1 / x;
counter.set(9);
y
```

Expected with `x = 0`: trap before the write. Observed: writes `9`, then traps.

Investigate `opt::DataNodeKind::is_pure`, discarded values in `opt/builder.rs`,
and scheduling. Cover integer division/remainder and trapping float-to-integer
conversions, including signed division overflow. Distinguish safe computation
from computation that must execute at its original control position.

Design checkpoint: agree on the representation of anchored trapping computations
before introducing a new effect/control mechanism or broader optimizer redesign.

Two approaches were considered:

1. A generic evaluation control statement naming a data node. Keep the operation
   in the data graph, but force evaluation/capture at that statement. Such
   computations must not be CSE'd across control positions without a dominance
   proof. A later global-read fix could use the same mechanism.
2. Explicit control operations with data-result nodes, following the existing
   call/memory-operation pattern. Give trapping arithmetic/conversions a fixed
   producer and let data consumers name its result. A later global read would
   likewise have a control producer and a data result.

The owner selected **explicit control producers and data results**. Implemented
`ControlNode::Trapping { op, result }`, with a typed `TrappingOp` for integer
division/remainder and the eight float-to-integer truncations. A
`DataNodeKind::TrappingResult` holds the produced value; operations no longer
also exist as movable data computations. Float division remains movable.

The builder folds integer operations only when they are proved not to trap
(including `x / 1`). Liveness retains operands even for a discarded result, and
the scheduler emits the operation at its control statement, capturing or dropping
only its result. Operand traversal is shared through `TrappingOp::operands`.
No TIR/MIR changes, effect system, or global optimization disablement were needed.

Five initial execution regressions all failed before the fix. Six tests now cover,
with inlining both off and on:

- discarded division/remainder at both integer widths and signednesses;
- trapping before a later write, including when the result is used;
- all eight truncations, NaN/infinity/out-of-range inputs, valid truncation, and
  unsigned negative inputs;
- trapping expressions under an absorbing `* 0` simplification;
- branch-local execution and repeated loop iterations;
- signed division overflow versus non-trapping `rem_s(INT_MIN, -1)`, plus safe
  constant folding (also checked structurally in opt).

Validation: `cargo test -p wx-compiler trapping_` — **6 passed**. The full suite
after C03 was **1,197 passed, 2 ignored**.

Future memory support must separately revisit dead pointer-load elimination:
unused loads may still have observable bounds traps. That is not changed by this
scalar-operation fix.

### C03 — Saved global reads must retain their original value after inlining

Status: **fixed using the owner-approved control/result split**.

```wx
counter.set(1);
local before = counter.get();
counter.set(2);
before * 10 + counter.get()
```

Expected: `12`. Observed: `12` without inlining, `22` with the default inliner.

An inlined `GlobalGet` can be materialized at its first consumer rather than at
the original read point. Excluding reads from CSE and spilling at first use is
insufficient. Investigate control anchoring in `opt/builder.rs` and scheduling;
cover intervening writes, calls, branches, and loop iterations.

Do not wire the inliner into the CLI before this case is resolved.

Implemented: `ControlNode::GlobalGet { id, result }` captures a value at the read
point; `DataNodeKind::GlobalGetResult { ty }` carries it to consumers. The global
identity is held only by the producer, and the result cannot be CSE'd/recomputed.
An unused global read can be omitted because the read itself cannot trap and has
no observable effect. No new scheduling side tables were introduced.

Added three execution regressions covering saved reads across writes, mutating
calls, aggregate element evaluation, branches, and loop iterations, with inlining
both off and on. The initial run reproduced the straight-line/call failures and
also exposed C07 in the loop test. After isolating C07, validation:
`cargo test -p wx-compiler saved_global_reads` — **3 passed**.

The first loop regression also exposed an independent computed-break-result bug
(C07 below). The C03 loop test uses a unit break and reads the accumulator after
the loop to isolate read timing from that separate defect; the failing computed
break source is retained under C07 rather than silently worked around.

### C04 — Pattern tests must respect user-defined equality effects

Status: **open**.

Use a struct implementing `PartialEq`/`Eq` whose `eq` increments a counter,
constants `ZERO` and `ONE`, and this pattern over `(P(0), 7)`:

```wx
match p {
    (const ZERO, x) | (const ONE, x) => x,
    _ => 99,
}
```

Expected: first alternative succeeds after one equality call; bind its `x`.
Observed: three equality calls, with and without inlining.

`tir/lower/patterns.rs` combines tests eagerly and repeats alternative tests for
binding selection. User-defined equality is not enforced pure and may mutate
state, call the host, or trap. Cover skipped alternatives, failed structural
prefixes, nested alternatives, and bindings selected by the original test.

Design checkpoint: do not silently impose a new purity rule on equality. Ask the
owner if fixing test/binding selection requires substantially reshaping pattern
lowering or settling unspecified pattern evaluation semantics.

### C05 — A short-circuit numerical loop trips the dominance verifier

Status: **fixed** (2026-11-04). Placement was wrong, not the verifier: a
miscompile without the verifier, too.

```wx
func escape(real: f64, imag: f64, limit: i32) -> i32 {
    local mut zr: f64 = 0;
    local mut zi: f64 = 0;
    local mut iterations: i32 = 0;
    loop {
        if iterations >= limit || zr * zr + zi * zi > 4 {
            break iterations;
        }
        local next_real = zr * zr - zi * zi + real;
        zi = 2 * zr * zi + imag;
        zr = next_real;
        iterations += 1;
    }
}
export { escape }
```

Observed in debug builds, with and without inlining: `opt/local_dominance.rs`
reports a local read without a dominating assignment. Investigate scheduler
placement and shared computations across short-circuit branches/loop bodies;
first determine whether placement or the verifier is incorrect.

Splitting the condition into two `if` statements compiles and matched a JavaScript
reference over 4,800 points. This is diagnostic evidence, not an accepted fix.
Keep the verifier enabled and retain the original expression in the regression.

**Cause.** `zr * zr` and `zi * zi` are each one interned node, read by the
`||` operand and by the loop's update. `compute_value_placement` hoists a
shared pure node to the common ancestor of its readers, but
`record_block_own_nodes` never recorded the back edge's reads: each
`LoopParam`'s `after` is emitted at the loop body's tail (`emit_control`,
`Loop`), and the `Loop` arm recorded only `outputs`. With one recorded reader
(the `else` arm), the node was emitted lazily inside that arm and the back
edge read its local on the path that skipped the operand. Here that path
always breaks, so only the verifier saw it. When the path continues, the
result is wrong. With the verifier off, this returned f(2) = 4 and f(3) = 16
instead of 16 and 256:

```wx
loop {
    if i >= n { break x; }
    if i == 1 || x * x > 1000 { hits += 1; }
    x = x * x;
    i += 1;
}
```

**Fix.** The `Loop` arm records each output's `after` as read at
`(body, block_tail(body))`, as `BlockJoin` records `fallthrough_updates`.
`x * x` now has two reading blocks and is computed in the loop body before
the `||`. Moving it ahead of the short circuit is sound because only pure,
non-trapping nodes are placed this way (trapping operations are control,
C02).

**Regressions** (`tir/lower.rs`, inlining off and on, both failing before the
fix): `a_back_edge_value_shared_with_a_skipped_operand_is_computed_every_iteration`
(the program above, n = 1..4) and
`an_escape_time_loop_with_a_short_circuit_condition_runs` (the original
expression, 725 points against a Rust reference). `cargo test -p wx-compiler`
— **1,216 passed, 0 failed, 4 ignored**. The CLI build of both programs ran
under Node with the expected results.

### C06 — CLI and execution tests must use the same backend pipeline

Status: **fixed** (2026-11-04). `backend::emit(mir, strings, inline)` is the
one sequence after `tir::build`: inlining under the given policy, then codegen.
`wx build` calls it with `Policy::DEFAULT`, and the execution harnesses call it
with the policy they test (`None` for lowering alone).
`backend::tests::a_build_inlines_an_inline_callee` covers it, and so does a
native CLI build that emitted one function and ran under Node.

The CLI calls `tir::build` and codegen directly; the lowering execution harness
also runs `mir::inline::run`. Consequently `#[inline]` has no effect on CLI
builds, and tests do not exercise the production sequence.

Establish a shared backend pipeline without rebuilding analysis or changing
`wx check` semantics. Preserve tests for lowering alone and inlining enabled.
Do not make general MIR DCE a requirement for this integration fix.

### C07 — A computed break result can be recomputed after carried-state commits

Status: **fixed with owner-approved uniform exit-result slots**, discovered
while extending C03 coverage.

```wx
func sum() -> i32 {
    local mut i: i32 = 1;
    local mut total: i32 = 0;
    loop {
        total += i;
        if i == 3 { break total; }
        i += 1;
    }
}
export { sum }
```

Expected: `6`. Observed: `9` (native CLI Wasm executed under Node). No globals are
needed to reproduce it.

The scheduler stores `total + i` into the carried `total` local on the break edge,
but emits the same expression again after the loop to obtain its result. At that
point `total` already holds `6`, so evaluating the expression again adds the last
`i` a second time. `merge_exit_value` only creates result outputs for differing
break values; a single expression can escape the loop as a movable data node.

Design checkpoint: give a breakable block/loop its own exit-result identity even
when there is only one break value, rather than letting a computation over
mutable carried locals escape as its result. The existing `JoinParam` and
`break_result_outputs` machinery may suffice, with each break/fallthrough writing
the target's result slots before committing carried bindings. This would replace
the special single-value path, not add a second result bookkeeping system.

The owner approved this result convention. Implemented by replacing
`merge_exit_value`'s raw-single-value/phi-chain paths with `record_exit_value`:
the first value-producing exit allocates one `JoinParam` per scalar in the
existing `break_result_outputs` table, and every exit writes those same slots.
The scheduler's existing exit stores now apply uniformly, before carried-binding
commits. There is no new result table or TIR/MIR representation.

Three new regressions all failed before the fix and now pass with inlining off
and on. They cover a computed single break, later consumers, identical values
from multiple exits, nested/zero-sized aggregate fields, and labelled-block
fallthrough. Failures before the fix included `9` instead of `6`, `2` instead of
`1`, and an aggregate result `(2, 2, 4)` instead of `(3, 2, 4)`.

Validation: `cargo test -p wx-compiler exit_results_` — **3 passed**;
`cargo test -p wx-compiler` — **1,200 passed, 2 ignored**.

### C08 — Folded 32-bit arithmetic disagrees with runtime equality

Status: **fixed**.

```wx
func folded() -> Bool { (4294967295: u32) + 1 == 0 }
func runtime(x: u32) -> Bool { x + 1 == 0 }
```

With `x = 4294967295`, expected agreement; observed `False` versus `True`.
Four probes cover signed addition/multiplication and unsigned addition/subtraction;
all four folded comparisons returned false instead of true, with inlining off/on.
`opt/builder.rs::try_fold_int` retains arithmetic results in i64 without
canonicalizing I32 values, while folded equality compares the full i64 values.
This is not a request to change overflow semantics: equivalent folded and runtime
operations already disagree.

Implemented: the opt builder's new `int(value, ty)` helper canonicalizes an
`I32` value to its sign-extended 32-bit pattern at the point the `Int` node is
constructed. Every `Int` construction site now goes through it: literals,
switch discriminants, default values, trapping-fold results, comparison and
arithmetic folds, conversion folds, and strength-reduction shift constants.
CSE/interning is unchanged and pays no per-node normalization cost. Emission
already truncates with `I32Const(value as i32)`, so the emitted bits are
unchanged; only value-inspecting folds see the fix.

The four-probe regression
`edge_wrapped_constants_agree_with_runtime_arithmetic` in `tir/lower.rs` is no
longer ignored. It checks both inlining policies.

Validation:

- Before: `cargo test -p wx-compiler edge_wrapped_constants_agree_with_runtime_arithmetic -- --ignored` — 1 failed; all four folded results were `0`.
- After: `cargo test -p wx-compiler` — **1,212 passed, 0 failed, 5 ignored** (C09/C10 reproducers remain ignored).
- `cargo fmt --all -- --check` and `git diff --check` — passed.

### C09 — Narrow runtime operations disagree with typed constants and patterns

Status: **fixed**.

```wx
const MAX: u8 = ^(0: u8);
func run(x: u8) -> (u8, Bool) { (^x, ^x == MAX) }
```

For zero, expected `(255, True)` from the constant evaluator's width-specific
bit-not. Observed `(-1, False)`; matching the result against literal `255` also
fails. The u16 equivalent produces `-1` instead of `65535`. This reproduction
does not depend on deciding overflow semantics. Initial overflow probes also
returned `(128, 32768, False, False)` for signed i8/i16 maxima plus one.

The runtime scalar path loses the subword width; std's narrow operator methods
also use representation-preserving `transmute` around i32 instructions. Review
the primitive/operator and canonical-value invariants before deciding where to
normalize; do not silently make all `transmute` operations narrowing conversions.

Implemented in two places, both preserving `transmute` as a pure
reinterpretation:

- Every narrow std operator impl restores the type's canonical form inline
  after its i32 operation — `& 0xFF` / `& 0xFFFF` for unsigned, or
  `(value << 24) >> 24` / `(value << 16) >> 16` for signed. This covers explicit
  calls such as `x.add(y)`/`x.bitnot()` and generic `T: Add` instantiations.
- `tir/lower.rs` applies the same mask/sign-extension to the results of
  `PrimitiveUnary`/`PrimitiveBinary`. Concrete `x + y`, `^x`, shifts, and the
  other primitive operators never execute the std bodies, so this is the path
  that fixes the reported case. Constant MIR nodes are created separately for
  the two shift directions because the MIR arena is a tree, not a DAG.

Constant evaluation remains checked: `tir/eval.rs::integer_binary` reports an
overflow error rather than wrapping, so `const X: u8 = 255 + 1` stays a
compile-time diagnostic. Runtime primitive operators wrap.

The lowering tests now cover the two paths directly:
`narrow_native_operators_restore_their_width` checks `+`, `<<`, `^`, and a
wrapped comparison for all four widths, and
`narrow_std_operator_methods_restore_their_width` checks explicit `.add()` /
`.bitnot()` and generic `T: Add`. Both run with inlining off and on.

Validation: `cargo test -p wx-compiler` — **1,215 passed, 0 failed, 4 ignored**;
`cargo fmt --all -- --check` and `git diff --check` — passed.

### C10 — Floating remainder panics; its trait implementation also disagrees

Status: **panic and incorrect stdlib implementation removed; general fmod is a
math-library follow-up**.

```wx
func run(x: f64, y: f64) -> f64 { x % y }
```

Checked source reaches `opt/builder.rs` and panics with `remainder has integer
operands`, including in the native CLI (exit 101), instead of producing Wasm or
an unsupported-feature diagnostic. Reproduced through the lowering-only path.

Explicit `x.rem(y)` does compile, but for finite `5.0` and infinite divisor it
returns NaN for both f32/f64, with inlining off/on. Constant evaluation of
`5.0 % (1.0 / 0.0)` returns `5.0`. The std methods use
`self - rhs * (self / rhs).trunc()`, which is not a general floating remainder
implementation. Merely routing `%` to that method will not resolve the semantic
mismatch.

Interim resolution: removed `impl Rem for f32` and `impl Rem for f64` from
`std/main.wx`; a general fmod belongs to a math library, not the core language.
`is_primitive_binary` now reports `Rem` as primitive only for integers, matching
the stdlib's impl set. Checked source therefore fails with a named diagnostic
instead of reaching the integer-only opt path:

- `x % y` on floats — E2063 (`TraitBoundViolation`): "the trait bound
  `f64: Rem` is not satisfied".
- `x.rem(y)` on floats — E2049 (`MethodNotFound`): "no function or constant
  named `rem` found for type `f64`".

No MIR is produced and the `opt/builder.rs` "remainder has integer operands"
unreachable is no longer reachable from checked source. Constant evaluation of
`5.0 % (1.0 / 0.0)` still uses the host `%` and remains the semantic reference
for a future implementation.

Added the unignored diagnostics regression
`float_remainder_is_unsupported_without_a_stdlib_impl`. The two execution tests
remain ignored as future fmod coverage:
`edge_float_remainder_agrees_with_constant_evaluation` and
`edge_float_remainder_methods_agree_with_constant_evaluation`.

Validation: `cargo test -p wx-compiler` — **1,215 passed, 0 failed, 4 ignored**;
`primitive_operators_match_the_stdlib_impls`, the C09 native/std-method
regressions, and the new C10 diagnostics regression pass. `cargo fmt --all --
--check` and `git diff --check` — passed.

## Validation and progress

Latest completed batch (C01–C03, C07):

- `cargo test -p wx-compiler` — **1,200 passed, 0 failed, 2 ignored**.
- `cargo build -p wx-cli` — passed.
- Native CLI output executed under Node: C01 effects, C02 discarded/ordered
  traps, C03 saved reads, and both C07 loop reproducers produced expected results.
- `cargo fmt --all -- --check` and `git diff --check` — passed.
- `cargo clippy -p wx-compiler --no-deps` — completed with existing warnings;
  it is not a warning-free baseline. No warnings name the modified opt files.
- C04–C06 remain open. Both design decisions used in this batch were approved
  before implementation.

### Post-fix design and cleanup review

Reviewed the changed lowering, builder, opt types, liveness, and scheduler code.
The control/result split and uniform exit slots are retained without changing
the IR or introducing new side tables.

- Borrow immutable exit-slot lists, aggregate operands, and scalar-type tables
  rather than cloning/collecting them solely to satisfy scheduler borrows.
- Use the same join-output allocation helper for branches, loops, and blocks;
  share break/fallthrough result stores, preserving result-before-carried-state
  ordering and reverse scalar stack order.
- Share scalar result capture without mixing it with evaluation, liveness, or
  trap-elimination decisions. Existing call/memory emission policies are unchanged.
- Remove redundant block-result liveness rooting: `JoinParam` has no input edges;
  the raw exit values are already rooted directly.
- Assert the scalar global-read invariant instead of silently defaulting to i32;
  update comments that still described the pre-C07 single-value/phi convention.
- Retain the builder's aggregate-result list copy: the aggregate node and join
  table independently own their lists. Avoiding it would require a representation
  change, not just removing a temporary allocation. `TrappingOp::operands` already
  uses a fixed-size stack array, not a heap allocation.

Added an aggregate labelled-block break/fallthrough execution regression with
saved global reads and nested/zero-sized fields, with inlining off and on.
Validation: `cargo test -p wx-compiler` — **1,201 passed, 0 failed, 2 ignored**;
formatting and diff checks passed. CLI build and compiler clippy passed (existing
warnings remain). Native CLI regressions also passed under Node; both existing
probe modules were byte-identical to their pre-cleanup outputs. C04–C06 remain
outside this cleanup's scope.

### Additional feature/edge-case execution review

Added 14 execution probes to the main lowering test module in
`crates/wx-compiler/src/tir/lower.rs`. Ten pass with inlining off and on,
covering:

- 1,024 deterministic input pairs each for signed i32 and unsigned u64 arithmetic,
  shifts, and remainder, compared with host reference operations;
- IEEE special values (NaN, infinities, signed zero, subnormals);
- aggregate rotations, nested labelled continues, dense/sparse match exits;
- recursive generic aggregates, zero-sized fields, early returns and inline joins;
- named construction/method evaluation order and traps in erased arguments;
- Euclid GCD, bitwise CRC, imported multivalue ABI and host-call counts.

Four additional probes reproduced C08–C10 above. Two (the C10 fmod probes)
remain explicitly ignored with case-specific reasons, not changed to assert
buggy behavior; they can be rerun with
`cargo test -p wx-compiler tir::lower::tests -- --ignored`. The C08 and C09
probes now run unignored after their fixes. No compiler behavior was changed in
this review.

Native CLI builds were also executed under Node: 12 modules ran, with **2,205
assertions** covering passing behavior and confirming C08/C09's recorded wrong
outputs; the floating `%` module instead failed to build with the C10 panic.
Projects, runner scripts, and build logs are in `/tmp/opencode/wx-edge-review`.
The explicit floating `rem` methods were separately executed under Wasmtime,
confirming NaN for both widths and both inlining policies.

Review-batch validation: `cargo test -p wx-compiler` — **1,211 passed, 0 failed,
6 ignored** (the previous two plus these four open-bug reproducers). Formatting
and diff checks passed. Logs: `/tmp/opencode/wx-edge-fourth.log`,
`/tmp/opencode/wx-edge-remainder-method.log`, and
`/tmp/opencode/wx-edge-final-tests.log`. C04–C06 remain open and unchanged.

After the C08 fix, C10 removal, and C09 completion: `cargo test -p
wx-compiler` — **1,215 passed, 0 failed, 4 ignored**; the C08 probe, both C09
lowering tests, and the C10 diagnostics regression run unignored. The C10 fmod
execution probes remain open.

Record each case's failing regression, implementation, commands, and outcome in
its section. Do not mark a case complete on checking or Wasm validation alone:
observable behavior needs an execution assertion.

The initial review also found unrelated integration debt: the browser compiler
adapter still calls removed APIs, the CLI LSP command is disabled, and the old
examples need source/API migration. These do not justify widening a correctness
fix or rewriting the IR.
