# Placement and the first graph-to-MIR emitter

Status: structural indexes and value placement implemented, 2026-11-09. Follows
[use collection](opt-demands.md) and [the backend design](opt-design.md).
`opt/locations.rs` implements location indexes; `dominators.rs` and
`placement.rs` implement the placement plan below. `emit.rs` implements the
MIR emission with structured control and simultaneous join updates.
The default backend uses `opt::optimize_reachable` and selective codegen;
verifiers remain test-only. See [integration status](opt-integration.md).
The milestone updates below retain their original dates and describe historical
intermediate states. `WX_NO_OPT` and `WX_GRAPH_EMIT` have been removed; use the
direct-MIR execution oracle in tests for comparisons.

## First milestone

Emit a correct MIR body from the new graph and feed it to the existing
linearizer. Initially store computed values in locals; emit constants,
parameters and static pointers directly at their readers. Keep all stored
effects in their existing order, discarding unused results. In particular,
retain loads and trapping operations even when their results are unused.

This deliberately precedes expression nesting, safe dead-effect removal,
and using construct results to reduce locals. Those remain later milestones.
The first emitter is an intermediate implementation, not the final code-size
or local-count target.

## Locations

A location is a gap between effects in an executable region:

```rust
struct Location {
    region: RegionId,
    position: u32,
}
```

For a region with N effects, positions range from 0 through N. Position i
is before effect i; i + 1 is after it. Appending several generated statements
at one gap requires dependency order, not just assigning them equal locations.
There is no usable execution position after an unconditional branch, return
or unreachable effect.

An `Effect::Region` occupies one position in its enclosing sequence. An
if/switch condition is read before that effect, not inside one of its arms.
The current if/switch wrapper regions have empty effect sequences; their
arms are the executable child sequences. Do not assign computations to an
empty wrapper as though it were a shared sequence preceding the arms.

Useful derived information, built by one structured graph traversal:

- Each effect's containing region and position in that sequence.
- Each executable child region's enclosing construct location, from which
  ancestry can be recovered. An arm belongs to its if/switch construct;
  blocks and loops have their own executable sequences.
- Each join's owner and whether it is a loop header or a construct exit.
- Each incoming row's location: before its branch effect, or before the
  enclosing loop effect for the header's implicit entry row zero.

Use flat arrays indexed by existing IDs. Row information can use one flat
array and per-join starts, including zero-width joins. Choose exact storage
with the index implementation; do not copy these locations into use records.
These indexes are per-function planning data and expire after emission.
This traverses the graph's structure, not the original MIR input tree.

## Availability and read sites

A computation must execute before every reader, and all of its inputs must
already be available there. Numeric node order is not proof of availability.

| Value or use | Execution constraint |
| --- | --- |
| Constants, parameters, static pointers | Can be read directly where needed. |
| Effect result | Available after its producing effect, along paths reached after that effect. Capture used results at the effect; do not move or repeat the effect. |
| Construct-exit phi | Incoming rows write its local before transferring control; it can be read after the owning construct completes. |
| Loop-header phi | Entry initializes its local before the loop. The local is available at body entry; each back edge updates it for the next iteration. |
| Ordinary pure value | Available after its computation; all inputs must be available before that computation. |
| Effect operand use | Read immediately before that effect. |
| Phi incoming-row use | Read at that row's location, before its local updates and control transfer. |
| Pure-node operand use | Read at the consumer's planned computation location. |

For an ordinary pure node, choose the nearest common dominator of its
reader locations: the latest shared control point that every execution
reaching any reader must pass through. Validate that the candidate is also
within the availability of every input. Structured region ancestry alone
is insufficient for loops and nonlocal exits; see the concrete algorithm
below. Do not move an input's producer merely to hide an invalid candidate.

Do not move a value outside a loop when all its readers are inside that
loop. Broader loop-invariant hoisting is a separate optimization.

Loop phis are anchored local reads, rather than ordinary computations to
schedule recursively. This distinction breaks the loop dependency cycle
for placement: scheduling `next = p + 1` needs the header local `p`, not
completion of the future back-edge assignment to `p`.

Use collection order is not a placement or emission order. The placement
implementation must explicitly order ordinary pure dependencies and handle
fixed phi/effect-result availability. Do not introduce a recursive rule
that waits for every phi input to be computed before the phi can be read.

## Three examples

These are illustrative pseudocode, independent of WX surface syntax.

### Shared value in two branches

```text
shared = x + 1
if condition:
    consume(shared)
else:
    consume(shared)
```

The two calls are in different arms. Their common executable region is
the parent sequence. Compute `shared` immediately before the if effect,
then read its local in either arm. If only one arm reads it, computation
can stay in that arm, provided its inputs are available there.

### A call result

```text
result = call f()
shared = result + 1
if condition:
    consume(shared)
else:
    consume(shared)
```

Capture `result` when the call runs. Compute `shared` after that call and
before the if. A position before the call is invalid even if it encloses
all readers. If a result originates in only one arm and is needed after
the if, an exit phi must represent that merge; placement cannot manufacture
availability on the other path.

### Swapping loop-carried values

```text
entry:  a = initial_a; b = initial_b
loop:
    ...read a and b...
    next_a = b
    next_b = a
    continue with (next_a, next_b)
```

Assign both entry values before entering the loop. On the back edge, read
both old values before assigning either destination. Emit one MIR
`SetLocals(Values(...))`, whose semantics evaluate the values before writing
the targets. Sequential assignments `a = b; b = a` would be incorrect.
Use the same simultaneous-update rule for any row updating several live
columns, including an inner loop's entry inside an outer loop.

## Implementation order and remaining questions

1. Build the structural location indexes and test arm ownership, nested
   branch targets and implicit loop-entry rows.
2. Implement placement against those indexes and `Uses`, with explicit
   availability checks and dependency ordering. Turn the three examples
   above into tests; add a nested-loop case.
3. Emit MIR with locals, simultaneous row updates and preserved effects.
   Run the compiler execution suites through this path before switching the
   active optimizer. Compare optimized and `WX_NO_OPT=1` execution, including
   traps; record output-size differences without requiring this initial
   emitter to beat the existing optimizer.
4. Add expression nesting and construct results, then safe effect removal
   as separately tested changes.

The concrete algorithm and smaller implementation steps are below. An
unexpected availability conflict in a builder-produced graph should be
treated as an invariant or algorithm issue, not repaired by arbitrary
hoisting or duplicated effects.

## Structural index implementation

`Locations::build(&graph)` borrows the graph and records flat arrays for
effect locations, enclosing entries, join owners and incoming-row locations.
One iterative structural walk fills these arrays. A prefix array over join
edge counts addresses the row locations, independently of the row's value
width: even a zero-column row has a control-transfer location.

The queries are `before(effect)`, `entry(region)`, `is_executable(region)`,
`join(join)` and `row(join, row)`. `JoinLocation` distinguishes `Exit` from
`LoopHeader` and records the owner region. Wrapper regions have entries but
are not executable; their arms share the wrapper's entry in the parent
sequence. Following entries from an arm therefore skips the wrapper.

The structural indexes do not assign movable values to locations or certify
that control reaches a gap or a value is available there. The placement
implementation performs those checks. The builder requires the graph invariants; it
does not duplicate the test-only verifier or support orphan storage entries.

Construction takes O(regions + effects + joins + incoming rows) time and
uses proportional index storage plus a temporary region work stack. Queries
are constant time; following ancestry will cost the number of enclosing
regions visited. No ancestor cache, depth array or reachability table has
been added before the placement algorithm establishes its needs.

Tests cover if-arm ownership, switches with and without defaults, zero-width
rows, nested loop entry rows, back edges and branches to an enclosing loop's
exit. Codegen tests build these indexes for every new graph they verify.

Validation: `cargo test -p wx-compiler --lib` and the same command with
`WX_NO_OPT=1` each passed 1,359 tests, with two ignored and no failures.
All 15 focused graph tests passed. Formatting and whitespace checks passed.


## Concrete placement algorithm and checklist

### Why region ancestry is insufficient

Consider a pure node `next = i + 1`, where `i` is a loop-header phi. The node
can be shared by a body effect, the back-edge row and a return after the loop.
The builder can produce exactly this graph through node interning and an exit
column that resolves directly to the header phi. A common enclosing region
would suggest computing before the loop, capturing only the initial value.
That is incorrect. A point inside the loop, before the decision to exit, can
run on every path to those readers, including the path leaving the loop.

Use dominance instead. A control point A dominates B when every execution
path from function entry to B passes through A. Dominance follows explicit
breaks and continues, not just nesting. It can therefore place the example
inside the loop and still make the local available after the loop exits.

This replaces the earlier assumption that an input-availability conflict
with a common enclosing region must indicate an invalid builder graph.
Valid graphs can require a common execution point inside a nested region.

### A. Control dominance (first implementation step)

- Allocate a control point for each gap of every executable region. Wrappers
  have no points. Some gaps, such as after a return, are unreachable.
- Build temporary control edges from existing effects and join ownership:
  ordinary effects advance to the next gap; a region effect enters its body
  or selects an arm; branches reach a loop header or the owning construct's
  following gap. Returns and unreachable effects have no successor.
- A loop's initial control edge enters its body; continues enter the same
  header point. All exit branches target the parent's point after the loop.
- Compute reachable reverse postorder with an explicit stack. Compute
  immediate dominators by repeated predecessor intersections until stable.
  An immediate dominator is the nearest preceding control point that every
  path to a point passes through. Store that tree and its depths.
- Release edges, predecessor/successor runs, traversal order and iteration
  scratch after construction. Keep only the indexes needed for dominance
  and common-dominator queries. Borrow the graph for the analysis lifetime.
- Do not claim linear construction time: the initial iterative solver can
  revisit predecessor paths. Measure before replacing it with a more complex
  dominator algorithm. This traverses derived control edges, not MIR again.

Tests: straight-line before/after availability; separate if/switch arms;
merged exits; loop entry/back edges; a body point that dominates a loop exit;
a conditional body point that does not; nonlocal exits; terminal/unreachable
end gaps. Run the existing compiler suites with these indexes enabled.

### B. Dependency ordering and earliest availability

Classify each used canonical node:

- Direct values: constants, parameters, static pointers and other pure leaves.
- Fixed definitions: effect results and phis.
- Ordinary computations: unary, binary, compare and convert nodes.

A result is defined at its producer's following gap. An exit phi is defined
at the gap after its owning construct. A loop-header phi is defined at its
loop-body entry. Phis are fixed definitions regardless of incoming inputs;
those inputs are evaluated separately at their row-use locations.

Build a dependency-first order of ordinary computations with an explicit
stack and temporary visitation state, treating fixed definitions and direct
values as leaves. A cycle containing only ordinary computations is an
internal error, rather than an infinite scheduling loop. Do not assume node
IDs or use-discovery order already provide this ordering after replacements.

For each ordinary computation, its earliest legal point is the deepest
input-definition point in the dominator tree. All input definitions must be
comparable by dominance; otherwise their values cannot be read together at
one definition without a merge. A pure value with no constrained input can
start at function entry. This pass orders dependencies and establishes
availability; it does not yet commit to execution there.

### C. Latest placement from all readers

Process ordinary computations in reverse dependency order, so every ordinary
consumer's location is known. Fold a node's recorded use sites with the common-dominator
operation: effects map to their preceding gaps, rows to their row
locations, and ordinary node consumers to their chosen locations. Phi inputs
are already recorded as row uses, not as reads at a phi definition.

Choose that nearest common dominator as the computation's location. The
node's earliest point must dominate it; otherwise return an internal placement
error. Do not clone effectful operations or use arbitrary hoisting to repair
an error. A nontrapping pure computation may execute on a path that does not
ultimately use it when sharing requires that common placement.

Finally validate actual producer placements against every read site, not
only earliest bounds. At a shared gap, emit ordinary computations in
input-before-consumer order. Fixed result capture and already-completed join
updates precede computations scheduled at the same gap. Row reads occur
before their simultaneous destination updates and control transfer.

### D. Output, lifetime and acceptance

The initial plan should retain one placement classification per graph node
and an input-before-consumer order for ordinary computations. Exact per-gap
packing is chosen with the emitter; do not add persistent use counts or
per-node heap vectors. Temporary DFS state, earliest bounds and dominator
construction scratch expire once their consumers finish. Keep graph borrowing
consistent across Uses, Locations and the resulting plan.

Acceptance cases include the three examples above, a shared `i + 1` inside
and after a loop, multi-column loop updates, nested loops, forwarding aliases,
shared arithmetic, unused values, and calls whose results are used across
control flow. Test malformed dependencies explicitly to check that validation
rejects an unavailable producer. Do not switch the active optimizer until
MIR emission exists and execution/trap tests pass through it.

Progress:

- [x] Structural location indexes.
- [x] Control dominance and its regression tests.
- [x] Dependency ordering and earliest availability.
- [x] Latest placement, actual availability validation and plan tests.
- [x] Straight-line MIR emission with locals, effect capture and returns.
- [x] MIR emission with locals and simultaneous row updates.
- [x] Execution comparison through the new emitter before replacing the existing optimizer.
- [x] Production pipeline migration (completed 2026-11-09).


## Placement implementation and remaining work

`Placement::build(&uses, &locations)` implements steps A through C. It checks
that both analyses borrow the same graph, constructs dominance, orders only
required ordinary computations, calculates earliest bounds, places consumers
before their inputs in the reverse sweep, and validates actual definitions
against all recorded reads. It neither modifies the graph nor emits MIR.

`value(node)` accepts forwarding aliases and returns one of:

- `None`: no definition is needed for the canonical node.
- `Direct`: a pure leaf is read directly at each use.
- `Fixed(location)`: an effect result or phi has a fixed definition boundary.
- `Stored(location)`: emit this ordinary computation at the chosen gap.

`computations()` returns each required ordinary computation once, with inputs
before consumers. At one gap, this is the order the emitter must preserve.
Capturing effect results precedes scheduled computations at the following
gap. Incoming row reads and simultaneous assignments remain emitter work.
No node-local heap vectors or persistent use-count arrays were introduced.

Dominance, earliest bounds and dependency-visitation state are temporary.
The returned plan retains the per-node classifications, computation order
and a borrow of the graph. Dominator construction uses flat temporary control
edges and predecessor/successor arrays; these are analysis data, not a
replacement IR or a restructuring of the source's control flow.

The implementation rejects ordinary pure cycles, unreachable definitions or
uses, incomparable input definitions, and definitions that do not dominate
their readers. The structural verifier does not cover all of these semantic
constraints; deliberately malformed graph tests exercise the placement
errors. Canonical replacement chains themselves must still be acyclic.

With N allocated nodes, V required nodes, U required input occurrences and D
dominator-tree depth, the value sweeps cost O(N + V + U), plus O((V + U) * D)
for the current tree-climbing dominance/common-dominator queries. Add the
control-index and iterative dominator-construction costs separately; there
is no overall linear-time claim. Dominance intervals or a faster ancestor
query are possible follow-ups if measured costs justify their extra storage.
The sweeps operate on graph arrays and required dependencies, not MIR trees.

Structured MIR emission is now implemented; production integration remains.
The current codegen test hook checks placement for each graph but continues
to emit with the existing optimizer or direct linearizer. Without the test-only `WX_GRAPH_EMIT=1` option, suite execution checks
compatibility of placement with real graphs. With that option, the backend
emits fresh MIR and sends it directly to the linearizer. Effect removal, expression nesting,
construct results and dominator-query optimization remain separate changes.

Validation for placement: `cargo test -p wx-compiler --lib` and
`WX_NO_OPT=1 cargo test -p wx-compiler --lib` each passed 1,372 tests, with two
ignored and no failures. The suite includes 28 graph tests. Formatting and
whitespace checks passed. Tests exercise branch sharing, fixed call results,
loop-local values read after exit, loop swaps, aliases and unused values,
as well as rejection of unavailable results, incomparable inputs and pure
cycles introduced through replacements.

## Additional checks before MIR emission

The analysis tests now include an independent path-removal oracle in
`opt/dominators/reference_tests.rs`. It constructs control successors
directly from structured regions and branch targets, without the production
location/join indexes. A reachable position A dominates B exactly when
removing A makes B unreachable. This intentionally slow algorithm checks
reachability, every pairwise dominance/common-dominator query and each
immediate dominator on small fixtures. It uses neither the production solver
nor its tree depths. The resulting placement is also checked against these
reference dominance facts, locating effect and incoming-row reads directly
from region sequences.

Fixtures cover early returns, both arms terminating, nested conditions,
calls, trapping division, multiple loop back edges, infinite loops and
branches exiting multiple nested constructs. Generated nested-return cases
vary the depth deterministically; synthetic terminators exercise unreachable
gaps. This is a bounded corpus, not exhaustive control-flow generation.
Both implementations still interpret the same structured control semantics;
the oracle does not replace end-to-end execution tests.

Additional focused checks cover:

- Three-value rotations in both directions on distinct loop back edges,
  including exact incoming-row values, fixed header definitions and an
  unchanged value that needs no header column.
- Rejection of a loop header phi used in its own entry row. A header
  definition is available inside the loop, not before loop entry.
- Unused calls and divisions retained in order inside their own branch,
  with their operands demanded and their unused results unmaterialized.
  Use collection also covers an unused trapping float-to-integer conversion
  alongside calls, loads and division.
- Several outputs of one effect, including an unused output, followed by
  dependent computations at the same gap. Required results are fixed there;
  computation order puts inputs before consumers. Actual capture ordering
  remains an emitter responsibility.
- A 4,096-node dependency chain with repeated inputs and a separate unused
  4,096-node chain. Discovery and placement finish without recursive value
  traversal, keep each computation once and preserve duplicate reads.
- Generated loops with 4, 32 and 128 updated source values, checking every
  demanded header column and incoming-row use.

The wide-loop fixture exposed a storage distinction: MIR compound assignments
introduce temporary locals, and the write-set builder can include those in
stored join columns. Required header phis remain limited to source values
and the loop counter. Avoid assuming stored join width equals demanded phi
count. Compacting these columns is a possible later memory improvement,
not a prerequisite for the first emitter.

These are correctness and scale regression checks, not performance
benchmarks. Peak scratch memory, allocation counts and timings by stage
remain unmeasured. No linear-time or bounded-memory claim follows from the
stress fixtures.

Validation after these additions: all 36 graph tests pass. Both
`cargo test -p wx-compiler --lib` and its `WX_NO_OPT=1` variant pass
1,380 tests, with two ignored and no failures. Formatting and whitespace
checks pass. No production analysis behavior changed in this step.

### Checks that require the new emitter

Keep these as acceptance gates for graph-to-MIR construction:

- Execute swaps and rotations for zero, one and several iterations, on
  every back-edge path. Read all row sources before writing destinations.
- Execute nested loops with nonlocal exits and loop values read after exit;
  compare results with the direct MIR path and existing optimizer.
- Compare observable call/store order and trap behavior, including unused
  loads/divisions/conversions and effects in untaken branches.
- Execute multiple-result capture with partially unused outputs and
  dependent computations at the following gap.
- Validate emitted MIR/Wasm and run the full execution suite through the
  new emitter before switching the active optimizer.

The first implementation slice below covers straight-line arithmetic, fixed
effect-result capture and returns using explicit locals. The structured extension below adds branches/joins and simultaneous
loop-row updates.

## First graph-to-MIR slice

`opt::emit(&mut mir, function_id, &placement)` returns fresh `mir::Code`
without replacing the original function. The graph must have been built for
that function and its placement must be valid. The module is mutable because
emission can intern multi-result types in its signature table.

The original slice accepted a single executable region. The structured
extension below removes that restriction and the temporary `EmitError`
return type. Emission returns `mir::Code` for a valid placement; malformed
graphs/plans are invariant failures. There is no fallback to the old optimizer.

Parameters occupy the original leading local indexes and are only read.
Required ordinary computations and effect results receive fresh mutable
locals. Unused original source locals are not copied. Direct leaves get a
fresh MIR node at every read, as do reads of materialized locals: graph nodes
can be shared, but MIR's arena must be a tree with one owner per expression.

Computations are packed by root-region gap with count/prefix/fill arrays.
Filling in placement's dependency order preserves input-before-consumer
order within a gap. Each effect executes after the computations at its
preceding gap. Its results are captured as part of that statement, before
the following gap's computations.

Effect outputs are indexed in flat runs by effect and result index.
`SetLocals` captures each used output and uses `None` targets to discard
unused ones, preserving mixed output types and declaration order. A call
with entirely unused results still executes once. Stores, globals, memory
operations and trapping arithmetic/conversions retain their sequence.
Returns use `Values` for their scalars; Unit returns need no value expression.
A graph ending in a diverging call gets an explicit trailing `Unreachable`,
so its lack of fallthrough is also visible to Wasm validation.

### Execution reference and discovered issues

`backend_tests/graph_emission.rs` builds graphs from hand-written MIR,
emits new bodies, verifies their arena ownership/local/label invariants and
feeds them directly into the existing linearizer. A test-only codegen entry
point forces this path without environment-variable changes or another run
of the old optimizer. Wasmtime validates and executes the resulting modules.
The original MIR through the direct linearizer is the semantic reference.

The unused-load fixture exposed an existing optimizer discrepancy: given an
out-of-bounds unused load before an unused division by zero, the old optimizer
removes the load and allows a later global write before division traps. The
direct MIR path and new emitter preserve the earlier load trap. Do not use
the old optimizer as the sole trap/order oracle. This slice does not change
the old optimizer's effect-removal policy.

This is a discrepancy under the current trap-preserving MIR contract, not
proof that every language must preserve invalid-access behavior. The existing
design's "Dead loads" section and transition spec's "No dropped effects"
rule make that choice today. The subsequent explicit decision is to keep
observable raw-memory traps even inside `unsafe`; see the raw-pointer
contract in `opt-design.md`. Allocation/object validity and aliasing promises
remain separate questions. The current runtime checks linear-memory bounds,
not whether an integer-derived pointer names the intended live allocation.

Output typing currently relies on the graph builder retaining typed `Result`
nodes for every output, including unused outputs. This is particularly
important for trapping conversion destination types, which are not stored
on `TrappingOp::Convert`. The emitter checks dense/unique output indexes and
call result types against the callee signature. Before physically removing
unused result nodes, settle whether output types move onto effects or into
a separate output-signature table. Current use discovery does not remove
these nodes, so this is not a blocker for the current representation.

Expression nesting and local reuse remain later work. The normal production pipeline still
uses the existing optimizer; no active-path switch is included here.

Initial validation: eight backend emitter tests execute shared arithmetic,
mixed and partially unused call outputs, observable trap/global-write order,
trapping conversions, typed operations and multi-value returns, signed zero
and NaN bits, diverging calls, Unit/zero-initialized values and explicit
structured-control rejection. Both full compiler modes pass 1,388 tests,
with two ignored and no failures.


## Structured emission and simultaneous join updates

Implemented 2026-11-09. Every required canonical phi receives its own local,
just like a computed value or captured effect result. A flat array indexed
by stored join column maps to the required phi, leaving unused columns empty.
Forwarded/trivial phis receive no separate destination. This keeps assignments
limited to required values without compacting the original graph's rows.

Each owning construct receives one MIR label. A per-join target table maps
exit joins to `Break` and loop headers to `Continue`. Both joins of a loop
use that loop's label; the existing linearizer provides its outer break block.
If/switch owners become a labelled block around an `IfElse`/`Switch`, so
explicit exit rows from any arm can use the same branch representation as
block exits. These wrappers are a correctness-first representation; replacing
some exits with fallthrough or construct results is later work.

Before each branch, emit a single `SetLocals(Values(sources...))` for the live
columns, followed by the control transfer. All sources are evaluated before
any destination changes. A loop's implicit header row zero uses the same
assignment routine immediately before its loop construct, outside the body.
Back-edge assignments execute inside the body before continuing. Exit-row
assignments execute before breaking, so post-construct computations observe
the joined values. Zero-width or entirely unused rows emit only control.

Computations are packed across all executable-region gaps, excluding empty
if/switch wrappers. A postorder work stack builds children before their owners;
construction does not recurse through regions or rewalk the original MIR tree.
Temporary arrays hold gap offsets, schedules, completed body IDs, labels and
join destinations. They expire with the emitter. MIR reads remain distinct
arena nodes, and effects retain their original execution order. A terminating
sequence is typed `Never`; a diverging call with a Unit ABI gets an explicit
`Unreachable` boundary. Construct types are Unit when an exit row exists and
Never otherwise, because joined values travel through locals.

The test harness `opt::emit_for_tests` verifies each graph, builds its use
and placement analyses, emits a fresh body and verifies MIR arena/local/label
invariants before replacing it. `WX_GRAPH_EMIT=1 cargo test -p wx-compiler --lib`
opts the backend execution tests into this path after normal optional inlining,
then forces direct linearization. The option is test-only and does not change
production builds. Dedicated emitter fixtures independently compare with direct
original MIR; the old optimizer is not the trap-behavior reference.

New execution cases cover zero/one/many loop swaps, three-value rotations on
different back edges, nested loop entry and nonlocal continue/break, mixed scalar
construct results, dense/sparse/exhaustive switches, early returns, call results
and shared arithmetic across branches, untaken trapping branches and loop-local
computations shared by a back edge and a post-loop read. All memory effects
and potentially trapping operations remain ordered; no aliasing or validity
promises are inferred from raw pointers.

Remaining decisions before production migration: keep the module-level
optimization/inlining/DCE order explicit, compare emitted Wasm/local counts,
and decide where to own the temporary graph/analysis/emitter lifecycle in the
normal backend. Expression nesting, construct results, local reuse and compacting
unused join columns are improvements to measure separately. Typed effect-output
metadata still relies on retained Result nodes as described above.


Validation after structured emission: the normal full compiler suite,
`WX_NO_OPT=1 cargo test -p wx-compiler --lib`, and
`WX_GRAPH_EMIT=1 cargo test -p wx-compiler --lib` each pass 1,396 tests with
two ignored and no failures. The graph mode routes backend builds after
optional inlining through new emitted MIR and direct linearization; dedicated
backend emitter tests compare both emitted and original MIR explicitly.
There are 16 dedicated emitter tests. Non-test `cargo check -p wx-compiler`,
formatting and whitespace checks also pass (existing compiler warnings remain).


Pre-integration responsibility checks and the reproducible size/local baseline
are recorded in [opt-integration.md](opt-integration.md). The default backend
was not changed by those checks.


Default-backend migration, 2026-11-09: the new graph pipeline is now selected by
`backend::emit` after optional inlining. Reachability selects items for codegen
without moving MIR entries. The old optimizer and both environment selection
flags have been removed; commands above using those flags record historical
validation runs. Direct original-MIR execution remains a test-only reference.
See [integration status](opt-integration.md).


## Trivial control transfers removed during emission, 2026-11-10

The emitter now represents normal construct completion as fallthrough where it
can prove that the final branch reaches the same join. This refines the initial
uniform labeled-wrapper representation above; graph construction, uses,
locations, dominance and placement are unchanged.

The existing postorder work stack carries an optional natural-exit `JoinId`.
A block's executable sequence naturally finishes at its own exit; if/switch arms
finish at their owner's exit. Nested region effects do not inherit their parent's
exit: falling out of a nested construct must still execute the parent's remaining
computations and effects. Loop bodies have no fallthrough exit in this first
slice; their backedges and breaks stay explicit.

Only a sequence's final `Branch` to its natural exit loses its control transfer.
The emitter still visits all placement gaps and emits the branch row's existing
simultaneous `SetLocals` assignments. A region is never discarded based on its
graph effect count: movable computations may be scheduled in its gaps even if
its only stored effect is the final branch. Loads, stores, calls and trapping
operations retain their order.

The existing per-join target column now names owning regions instead of eager
MIR labels. The existing per-region label column allocates a dense label only
when a retained transfer requires one; loops always receive the label required
by MIR. The original label counter moves into the emitter. Once all descendants
have been emitted, an owner with no allocated label needs no block wrapper.
This needs no new analysis table, no additional tree pass and no persistent
analysis data. The extra exit context lives only on the current emission stack.

MIR sequence types follow their last expression; if/switch types reflect whether
an emitted arm can fall through. Non-returning calls still receive the explicit
`unreachable` boundary required by Wasm. Wrapper/transfer decisions happen before
allocating those MIR nodes, preserving arena ownership without orphan cleanup,
body compaction or label rewriting.

Three focused regressions check untargeted nested blocks, if and dense-switch
arms with required computations/phi updates, and a nonlocal exit that must skip
its parent's following global write. Existing execution tests cover simultaneous
loop updates, nested break/continue, sparse/exhaustive switches, non-returning
calls and observable trap ordering. All 1,414 compiler library tests pass, with
2 ignored. The example memory/WASI suite also passes.

The same 22-program comparison has new raw outputs under
[control-cleanup](backend-comparison/2026-11-10/control-cleanup/README.md).
The 15 repository examples fall from 10,483 to 7,983 bytes (23.8%); all 22 fall
from 11,129 to 8,589 bytes (22.8%). Local counts are unchanged. All 22 saved
modules validate and 197 arithmetic/hash/vector/control result assertions pass.

## Single-use expression nesting — 2026-11-10

Placement now distinguishes `Stored(location)` (a shared computation kept in a
local) from `Nested(location)` (a computation with exactly one recorded operand
occurrence). This decision is made while visiting readers in the existing latest
placement loop. Duplicate operands count separately, even when their `UseSite`
values are equal. A nested computation's location is its sole reader's location;
chains therefore remain at the same executable gap. The existing availability
and dominance validation applies to both forms.

No use-count column or additional input-tree walk is needed. `Uses` and locations
still expire after planning, before MIR emission. `computations()` retains its
complete dependency order, but only `Compute` entries receive locals and enter
the gap schedule. Fixed phi definitions and effect results remain in locals;
loads, calls and trapping operations remain ordered effects.

The emitter expands nested inputs on demand into fresh MIR expression nodes.
Two reusable scratch vectors hold pending construction tasks and completed input
expressions. They are empty between computations and retain capacity only until
the emitter expires. Construction is iterative, including deep chains, and shared
inputs produce local reads rather than duplicated computations. Incoming join
rows still evaluate every source before writing any destination.

The final linearizer's arithmetic walk is also iterative, using a reusable task
stack. Binary operands retain left-to-right evaluation, and a diverging left
operand suppresses the right operand and operation. Structured control handling
retains its existing recursion; this change removes recursion through arithmetic
chains, not all possible nesting in the backend. Reentrant expression walks stop
at their own stack boundary so structured children cannot consume an enclosing
expression's pending work.

Validation: 1,417 compiler library tests passed, 2 ignored. Dedicated checks cover
single-use nesting, repeated operands retaining a shared local, wrapping and
noncommutative arithmetic, and a flat input with 4,096 dependent assignments that
becomes one deep expression and executes successfully. Existing effect/trap,
conversion, mixed-type return, loop and simultaneous-update tests remain active.
The release CLI built; all 22 saved example modules validated and passed 197
result assertions, and the existing memory example execution suite passed.

Raw output versus the trivial-control cleanup baseline (`31aa121`): all 22
programs shrink from 8,589 to 7,256 bytes (15.5%), with non-parameter locals falling
from 593 to 273 (54.0%). The 15 repository examples shrink from 7,983 to 6,710 bytes
(15.9%). No external Wasm optimizer was applied. Compiler throughput and runtime
speed were not measured. Artifacts and the reproduction script are in
`notes/backend-comparison/2026-11-10/expression-nesting/`.

Follow-up (2026-11-10): the full linearizer now uses one iterative task stack,
including structured control and both switch lowerings. The earlier arithmetic
wrapper and recursive structured traversal have been replaced. See the
implemented traversal update in `notes/mir-pipeline.md` for the model and checks.
