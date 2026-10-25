# TIR constant evaluation and type-level constants

Status as of 2026-10-25, branch `tir-refactor`. Companion to
`tir-check-pass.md` (obligations, the solver's verdicts) and
`tir-body-checking-plan.md`.

- Committed: `6ff4e9f` (array lengths as type-level constants, `Type::Value`),
  `6acc3be` (lengths named by free constants, `Type::Const`).
- Uncommitted: constant evaluation moved onto the solver (`impl Solver` in
  `eval.rs`), and on top of it the phase design below (sections 1, 2, 4, 5 and
  6 of the implementation map). The on-demand walk (`ensure_named_bodies`,
  `Body::named_constants`) is gone.

## Type-level constants

Constants live in the type space (as in GHC's DataKinds), not in a separate
`Const` space as in rustc. There is no `kind()` function: kinds are checked by
syntax where an argument meets its parameter, and are correct by construction
after that.

- `Type::Value { bits: u64 }`: a constant inside a type. It has **no type of
  its own**. Its type is the one of the position it is in (an array length's is
  `<memory as Memory>::Size`), as rustc's `ty::Const` dropped its `ty`. With a
  typed `Value`, `M::&[u8; 4]` would not match `heap::&[u8; 4]` once `Size`
  normalizes to `u32`.
- `Type::Array { of, length: TypeIndex, memory, ownership }`: the length is a
  `Value`, a `Const`, or `INFER` (a written `_`, filled by a literal).
- `Type::Const { constant, type_args }`: a constant named in a type. It is the
  constant counterpart of `AssocTypeProjection` (it carries `HAS_PROJECTION`):
  normalization replaces it with its `Value`. `type_args` follows
  `Type::Function`'s layout (an impl's arguments, then its own; `[Self]` for a
  trait's declaration), so one variant covers free, impl, trait and generic
  constants. Today only free constants are built, with no arguments.

| Kind of type | Concrete | Generic | Deferred |
| --- | --- | --- | --- |
| type | `u32`, `Struct { .. }` | `TypeParam` | `AssocTypeProjection` |
| constant | `Value` | `TypeParam` (const parameter, planned) | `Const` |

Alternatives rejected for the deferred form:

- **Evaluate during lowering** (`[u8; SIZE]` becomes `Value` at once): bodies
  would be checked in the middle of signature construction, which selects
  impls; that needs rustc-style queries everywhere, and still cannot handle
  `T::SIZE`.
- **Rewrite signatures after evaluation**: a fix-up pass, against "a check
  never rewrites a stored signature".
- **`Value(enum { Bits, Named })`**: the same two cases, wrapped.

### Checks on a length

- A literal length records `Obligation::CheckConstantFits`: the value fits the
  memory's `Size`, or, for an abstract memory, every member of the typesets
  `Size` is bounded by (`PointerSize`: `u32` and `u64`), so generic code works
  with every memory.
- A constant length records `Obligation::CheckConstantType`: the constant's type
  is **exactly** the length's type. A constant of another type is a mismatch even
  when its value fits; for an abstract memory, `const N: u32` is a mismatch with
  `<M as Memory>::Size`.

### Generic constants (planned)

Written with explicit parameters: `const N<S: PointerSize>: S = 0;`.
`const N: impl PointerSize` was considered and dropped: `impl` in a constant's
type reads as existential (one hidden type), which is useless in abstract code.

- `N` gets its own parameter frame, as a generic function does; its body is
  checked once, generically (the literal `0` must fit every member of
  `PointerSize`).
- A use instantiates `S` from the position: `M::&[u8; N]` gives
  `Const { N, [<M as Memory>::Size] }`, so `CheckConstantType` holds by
  construction and `S: PointerSize` is an ordinary bound obligation.
- Evaluation is memoized per instance, keyed by the interned `Type::Const`.

## Evaluation is the solver's

A constant's value is a judgement, like an impl member's value (`Verdict`):
judged once, memoized, owning its failures and loops. So it is a solver query
(`Solver::const_value`), in `eval.rs` as `impl Solver` blocks (as `layout.rs`
is).

- An evaluation is a frame on the solver's own stack,
  `SolverFrame::Evaluation { constant, outer_budget }`, with a budget of its own.
  The constant's memo slot (`Solver::const_values`) is `InProgress` exactly while
  its frame is on the stack.
- A dependency is a nested call: evaluating `N = M * 2` reaches the `Const{M}`
  node, which pushes `Evaluation(M)` on top, evaluates, pops, memoizes.
- A loop (`A = B; B = A`) is reading a constant that is `InProgress`: the loop
  is the frames from its first evaluation up, owned by its first-defined member.
  It is read from the same stack as a loop through projections.
- Normalizing a `Type::Const` evaluates it in place: no retry protocol between
  the solver and `TypeContext`.
- The solver reads built bodies and builds none. `SolverView` lends it constant
  signatures, constant bodies, and strings (a string literal's contents).
- Reporting stays in `TypeContext`: `evaluate_constant` reads the solver's
  state and reports what a constant owns.

Option (A), rejected: the solver returns `Unevaluated(instance)` and
`TypeContext` evaluates and retries. A protocol between two systems, and loops
through projections and constants would be split over two stacks.

## Bodies are built before anything evaluates

The solver cannot build a body, so every body an evaluation reads must exist
first. Discovering dependencies ahead of time (walking a body for the constants
it names, or recording them while building) cannot work: a body reached through
impl selection (`T::SIZE` with `T = Foo` selects `Foo`'s `SIZE`) is in no
expression tree. A retry protocol (`Pending(ConstIdx)`, build, retry) is lazy
but brings the protocol back and is quadratic along a chain.

Chosen: an invariant. **Every constant body is built before anything
evaluates.**

### Phases

| # | Phase | What happens | Reads values? |
|---|---|---|---|
| 1 | Construct signatures | Written types are lowered (`[u8; N]` is `Const{N}`); requirements are recorded as obligations | no |
| 2 | Build constant bodies | Every constant's initializer (variants included) is checked into its `Body`, in definition order; a check that needs a value is recorded beside the body | no (value-free) |
| 3 | Check declarations | Each declaration's obligations; a normalization meeting `Const{N}` evaluates `N` | yes |
| 4 | Check constant bodies | Per constant, in definition order: its recorded checks, its evaluation, the report of what it owns; enum discriminant checks | yes |
| 5 | Build and check function and global bodies | On the spot, as today | yes |

What this removes: `ConstBody::Building`, on-demand body building
(`ensure_const_body` recursion), the walk, `Pending` in evaluation, the forcing
in `check_now` before `CheckConstantType`, and the "constant named in a type
inside its own value" check at lowering (it becomes an ordinary loop on the
solver's stack).

### Value-free building

Phase 2 cannot compare two types when one contains an unevaluated `Const`
(`const A: heap::&[u8; N] = B;` with `B: heap::&[u8; 2]`). Such a comparison
is recorded as a requirement, "these are equal", and building continues as if
they were. This is rustc's `ConstEquate` obligation. Inside constant bodies:

- `expect` / `meet`: a mismatch involving a `Const` becomes a recorded equality.
- `coerce_static`: a literal's length against a `Const` length becomes a
  recorded check.
- A repeat `[0; N]` is typed `Array { length: Const{N} }` instead of reading
  `N`'s value.
- Exhaustiveness over constant patterns runs as a recorded check.
- A type written inside a constant body records its well-formedness instead of
  normalizing it on the spot (normalizing would evaluate).

The checking code is the same for every body; only what happens at the moment
of the check differs (decide now, or record for phase 4), one flag on
`BodyContext`. Function and global bodies keep checking on the spot.

This changes a stated rule: "a body checks what it requires on the spot"
becomes "a constant body records what needs values; it is checked once every
constant body exists".

### Worked example

```
memory heap: u32;
struct Buf(data: heap::&[u8; N]);
const N: u32 = M * 2;
const M: u32 = 4;
const TEXT: heap::&[u8; N] = "abcdefgh";
```

1. `Buf`'s field is `heap::&[u8; Const{N}]` (records `CheckConstantType`,
   `CheckWellFormed`); so is `TEXT`'s type.
2. `N`'s body types `M * 2` without a value; `M`'s is `4`; `TEXT`'s records
   "length 8 equals `Const{N}`".
3. `CheckWellFormed` normalizes `Const{N}`: `Evaluation(N)`, then
   `Evaluation(M)` on top, `4`, pop, `8`, pop: `Value{8}`.
4. `TEXT`'s recorded check reads the memoized `8`, and passes.

## Effects to keep in mind

- Diagnostic order: a constant body's diagnostics come before the declaration
  checks' (phase 2 before phase 3); today every body comes after every
  declaration.
- A recorded check reports in phase 4, after its constant's other diagnostics.
- A loop mixing projections and constants is found from either side (one
  stack), but its owner is not unified yet: constant loops are a list of
  `ConstIdx` owned by the lowest index, separate from `ProjectionCycle` and
  `Definition` order. Nothing builds such a loop yet (constants cannot read
  types).

## Next steps

1. List every place body building reads a value or compares a `Const`
   (`constant_bits` callers in `typecheck.rs` and `exhaustiveness.rs`,
   `coerce_static`, `expect`/`meet`, `check_now` in local annotations), to fix
   the scope of value-free building.
2. Implement the phases on top of the solver-side evaluation; drop the walk.
3. Substituted evaluation: lower `T::SIZE` / `Foo::SIZE`, normalize a trait's
   `Const` through impl selection, evaluate an instance with its arguments
   substituted, memoized per instance.
4. Generic constants, then const parameters (`TypeParam` with a declared type in
   its frame) and constant arguments.

## Implementation map

Line numbers are as of the uncommitted solver-side refactor; they will drift.

### 1. Reorder `sweep` (`signatures.rs:273`)

Today: signatures, `check_declarations`, `check_bodies` (everything, with
constant bodies built on demand). Target:

1. signatures;
2. `build_constant_bodies` (new): every constant and variant, value-free, in
   definition order;
3. `check_declarations`: may evaluate;
4. `check_constant_bodies` (new): recorded checks, `evaluate_constant`,
   `check_discriminants`;
5. `check_bodies`: function and global bodies only.

### 2. Delete the on-demand machinery

- `ensure_named_bodies` and its visited set (`eval.rs:257`),
  `Body::named_constants` (`body.rs:521`).
- `ConstBody::Building` and the comment that justifies it
  (`signatures.rs:1563`, `1592`); `ensure_const_body` (`signatures.rs:1515`)
  becomes a plain build, called once per constant.
- The cycle check at lowering, "named in a type inside its own value"
  (`signatures.rs:2940`).
- The forcing of `constant_bits` before `CheckConstantType` in `check_now`
  (`obligations.rs:170`).
- `Unevaluable::Pending` and `Halt::Pending` (`eval.rs:173`, `456`, `916`;
  `solver.rs:1015`): unreachable once evaluation starts in phase 3, so a
  `NotBuilt` body becomes a `debug_assert`.
- `TypeContext::const_value` shrinks to lending the view and calling the
  solver.

### 3. The solver before values exist (decided: option (a), variant 1)

Phase 2 normalizes types: `check_body` normalizes the declared type
(`typecheck.rs:125`), and local annotations, casts and calls go through
`check_now`. `normalize_const` on a `NotBuilt` body returns `Pending`, so the
whole normalization fails.

Decided: the solver keeps returning `Pending`. It stays phase-agnostic, and
`Pending` is never memoized, so the cache rule ("a path that reads a non-final
fact returns `Pending`") holds unchanged. A body built in phase 2 is `Built` in
phase 3, so an answer read in phase 2 is not final; this is why the solver must
not answer "rigid" there (option (b), rejected: its answers would depend on the
phase and would have to be kept out of the cache).

This is rustc's lazy normalization adapted to phases. rustc never meets an
unbuilt body (`const_eval_resolve` runs `typeck` on demand, and a loop is a
query cycle), but a constant it cannot evaluate yet (`TooGeneric`) is left as
an alias, and a comparison with it becomes a `ConstEquate` (old solver) or
`AliasRelate` (new solver) obligation decided later. rustc may memoize an
ambiguous answer because a query's inputs never change; ours do across phases.

On `Pending`, the body side keeps the **whole written type** (variant 1). A
comparison that then fails because one side is unreduced is recorded as a
`ConstEquate` and rechecked in phase 4 with full normalization, so the answers
are right; the cost is that some errors that would fail anyway come out in
phase 4 rather than phase 2, and a literal coerced against a projection left
unreduced beside a `Const` may misbehave (only in a type holding a `Const`).

Follow-up if that gets bad, variant 2: a body-side helper normalizes a type
part by part and keeps a `Const` part as written where its own normalization
is `Pending` (rustc replaces only the alias with a placeholder). A structural
walk over the type, never cached.

### 4. Value-free building

A flag on `BodyContext`; `BodyOwner::Const` already says which bodies it is.

- `expect` (`typecheck.rs:204`): `actual != expected` where either side holds a
  `Const` records `ConstEquate { expected, actual, expr }` instead of reporting.
  `meet` / `learn` must keep a `Const` rigid.
- `coerce_static` (`typecheck.rs:2101`): the count of `[v; N]` reads
  `constant_bits(N)` (`typecheck.rs:2163`); `[v; _]` against a `Const` length
  needs a `Value`. Idea: give the literal's length as a `TypeIndex` (a `Value`
  for a literal, `Const{N}` for a constant count), so the length comparison is
  a `ConstEquate`: one mechanism instead of three special cases.
- `check_now` inside a constant body pushes to the body's recorded list instead:
  `blocks.rs:265`, `casts.rs:40`, `members.rs:118`/`134`/`371`,
  `typecheck.rs:681`/`742`/`1032`/`1101`.
- Exhaustiveness reads constant pattern values (`exhaustiveness.rs:170`/`190`/
  `239`): record "check this match" for phase 4, which then runs usefulness
  over the built body outside `BodyContext`.

### 5. Recorded checks and phase 4

- Stored beside the body, e.g. `ConstBody::Built { body, deferred }`.
- Kinds: `Obligation` as it is (`CheckWellFormed`, `CheckConstantType`, ...),
  `ConstEquate { expected, actual, span }`, `MatchExhaustiveness { expr }`.
- Order per constant: recorded checks, then `evaluate_constant`, then (for an
  enum) its discriminants.

### 6. Loops and who reports them

- `const A: heap::&[u8; A] = [9; _];`: phase 3 normalizes `Const{A}`, which
  pushes `Evaluation(A)`; evaluation reads the type's length, `Const{A}` is
  `InProgress`, so it is a cycle.
- The constant owns it: `evaluate_constant` reports it in phase 4 (E2109).
- The obligation that met it (a phase-3 `CheckWellFormed`) stays silent:
  `report_solver_error` skips a cycle a constant owns.
- Evaluation normalizes body types through the solver, in place.

### 7. Watch items

- `layout.rs:305`: a `Const` is `Poisoned`, so an array's layout with a `Const`
  length needs normalizing first.
- Diagnostic order: constant bodies' diagnostics move before the declaration
  checks'.
- `check_variant_value(previous)` stays value-free (`NextDiscriminant` is
  evaluated later).

### 8. Tests and docs

- `a_constant_named_in_a_type_inside_its_own_value_is_a_cycle`: its expected
  codes change.
- New tests: a forward reference (the worked example), a `ConstEquate` that
  holds and one that fails, `[0; N]` against `[u8; 8]`, a match on constants
  inside a constant.
- Look for tests that assume the order between body and declaration
  diagnostics.
- `CLAUDE.md` (phase 2 and type system paragraphs) and this note's status.

### Order of work

1. Commit the solver-side refactor as it is (working, green).
2. Reorder the phases and delete the on-demand machinery (sections 1 and 2).
   Everything but `coerce_static` and exhaustiveness should keep passing,
   since no test has a forward reference inside a body.
3. Value-free building and recorded checks (sections 4 and 5).
4. Loop ownership (section 6), then tests and docs.

### Progress and deviations (2026-10-25)

Implemented: the five phases, the removal of the on-demand machinery and of
the lowering-time cycle check, `DeferredCheck` (stored on `Body`, decided by
`BodyContext::decide_deferred` over a resumed body), `ConstEquate` in
`expect`, `coerce_static` with the literal's length as a `TypeIndex`
(`check_static_length`), and deferred match usefulness. Tests: forward
references in types, lengths and repeat counts, mismatches found once the
value is known, a match on later constants and a later enum, the
`const A: heap::&[u8; A]` loop.

Where the code differs from the plan above:

- **No flag on `BodyContext`.** Deferral is driven by `Pending` itself: a check
  that meets `Pending` defers, and only a constant's body can meet it
  (`BodyContext::defer` debug-asserts the owner). So `Unevaluable::Pending` and
  `Halt::Pending` stay (the plan listed them for removal): they are how a
  phase-2 read says "not yet". An evaluation in phase 2 whose bodies all exist
  simply succeeds, and is final.
- **Phase 4 order per constant:** evaluate first (while its body is in place, a
  deferred check may read its own value), then the deferred checks, then the
  report. Caveat: a constant may be evaluated (in phase 3 or here) before its
  own deferred checks report a mismatch. The evaluator's scalar check against
  the declared type guards the value; rustc instead refuses to evaluate a body
  tainted by errors. Revisit if a wrong value shows up.
- **The evaluation frame opens before the declared type is read**
  (`constant_scalars` normalizes it), so a type naming its own constant is a
  loop on the stack instead of unbounded recursion.
- `const C: u32 = block { local a: heap::&[u8; C] = [0; _]; 1 }` is now only
  E2057: the block is not evaluated, so no loop is ever closed. It becomes
  E2109 once blocks with locals are evaluated.
- A loop is reported by the constant (E2109) alone; the obligation that met it
  sees `Poisoned` (`normalize_const` maps a cycle to it) and is silent, so
  `report_solver_error` needed no change.

Still open from the map: section 7's `layout.rs` handling of a `Const`
length, and option 2 of section 3 if keeping whole written types gets bad.

### Open: don't evaluate a body with errors (as rustc does)

rustc finishes `typeck(C)` (obligations included) before `eval(C)` reads the
body, and a body whose typeck reported an error is `tainted_by_errors`:
const-eval answers `ErrorHandled::Reported` without evaluating, and readers are
silent. The phase-4 caveat above is the gap. A sketch of closing it:

1. **Taint.** `Body::tainted_by_errors`, set by `BodyContext` when the error
   count rose while it built the body or decided its recorded checks (rustc's
   older count-based taint). The solver reads a tainted body as `Poisoned`.
2. **Ordering.** The taint only means something once the recorded checks are
   decided, and our solver cannot decide them on demand. So the solver also
   answers `Pending` for a body that still has recorded checks, and phase 4
   becomes a fixpoint over those bodies: decide what can be, re-record what is
   still `Pending`, repeat while there is progress (rustc's
   `select_where_possible`). Then evaluate and report every constant.
   `check_declarations` moves after the fixpoint, or it can meet a constant
   whose checks are undecided.
3. **What is left after the fixpoint is a loop**
   (`const C: u32 = block { local a: heap::&[u8; C] = .. }`: rustc's
   `typeck(C) -> eval(C) -> typeck(C)` cycle, E2109 instead of today's E2057).
   Reporting it once per loop needs to know what each stuck body waited on:
   (a) report every stuck constant (several reports per loop, and constants
   that only wait on a loop report too), or (b) record the awaited constant
   when an evaluation is `Pending` on an unfinished body (on the answer or on
   the solver's frames), build the waits-for graph, and let the first-defined
   constant of each loop own it, as impl-member loops are owned. (b) keeps the
   one-diagnostic-per-loop rule, but `SolverError::Pending` has many origins
   besides constants.
