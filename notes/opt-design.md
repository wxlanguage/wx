# `opt`: a sea of nodes for structured Wasm

Status, 2026-11-09, branch `tir-refactor`: graph construction, use collection,
locations and value placement are implemented in `opt/`.
The graph-to-MIR emitter handles structured control and simultaneous join
updates. The default backend uses the reachability worklist, new optimizer
and MIR linearizer; the old optimizer has been removed. `opt::optimize_function` exposes the new per-function
pipeline in normal builds; its verifiers remain test-only. See [opt-placement.md](opt-placement.md)
for the current implementation and remaining execution gates. This design
replaces `opt`'s builder, scheduler and liveness (`opt/builder.rs`,
`opt/scheduler.rs`, `opt/liveness.rs`) and is how step 2 of
`notes/mir-pipeline.md` ("`opt` outputs MIR") is done: steps 2.3–2.5
become "Order of work" below.

## Why

Measured on 2026-11-08 (`notes/mir-pipeline.md`, "Where 2.2 landed"):
lowering's MIR linearized straight to Wasm is about half the size of `opt`'s
output (25 KB against `opt`'s 51 KB over the 23 binary examples). `search` shows
why: every block a `break` targets, every inlined call's wrapper among
them, copies every live local into a fresh local at each exit and back,
nine values twice, whether or not the block changed them. Local
instructions: 403 under `opt`, 89 without it.

The size is a symptom, not the goal: it shows `opt` keeping values apart that
are the same. The cause is the data, not one comparison:

- **Joins are built for every local, then pruned.** A loop or a block that
  is a `break` target gets a placeholder per function-wide local
  (`create_loop_params`, `create_join_params`), each exit records its
  bindings against them (`carried_binding_updates`), a running union says
  which were real (`JoinData::divergent_params`), and
  `patch_loop_binding`/`finalize_block_join_binding` undo the rest. For a
  block the comparison is against the placeholder while the body starts
  from the parent's values, so every local looks changed: the bug above.
  Fixing it in place adds a third layer to the two that cause it.
- **Edges live in code, not in data.** A `JoinParam` has no edge to what is
  written into it, and a switch's `Phi` is a binary placeholder over two
  arms, so every pass that follows edges special-cases them: liveness
  roots the update lists and `own_values` instead (`liveness.rs`), and
  `should_spill` reads `node_to_local` for loop params. Inputs are spelled
  out per kind in three places (`liveness.rs`, `register_uses`, the
  scheduler's placement).
- **"Who uses this" has two answers.** Each node holds a `uses` vector, one
  allocation per node, filled at creation (it counts dead readers and
  misses control ones); `DataLiveness` is a second answer from the roots.
- **Aggregates and `Option<StackResult>`** everywhere, which scalar MIR no
  longer needs.

## The idea

Two facts about the input and the output decide the design:

1. **Control is structured on both sides.** MIR's `Block`/`Loop`/`IfElse`/
   `Switch` are Wasm's `block`/`loop`/`if`/`br_table`. So control stays a
   tree of regions mapping one to one onto them, and only data floats as a
   graph. No control-flow graph is built or reconstructed (no relooper).
2. **Which locals a merge needs is syntactic.** At a join, exactly the
   locals written inside the construct can differ. That is known before the
   construct is built, so a merge is sized once and never pruned: SSA for
   structured languages as in Brandis and Mössenböck, "Single-Pass
   Generation of Static Single-Assignment Form for Structured Languages"
   (TOPLAS, 1994).

So a join is a table: a column per thing merged, a row per incoming edge,
its width fixed before any row arrives. A merged value is a column; it is a
node only where its rows disagree, and its inputs are that column, so every
edge in the graph is data.

## The data

```rust
index_newtype!(NodeId);    // a value
index_newtype!(EffectId);  // a statement, pinned in program order
index_newtype!(RegionId);  // a block, a loop body, an arm, a case
index_newtype!(JoinId);    // a merge

pub struct Function {
    // Values: one scalar per node, as columns.
    kinds: Vec<NodeKind>,
    types: Vec<ScalarType>,
    operands: Vec<NodeId>,          // runs, for nodes with many inputs
    // Construction lookup for identical node kinds and types.
    interned_nodes: HashTable<NodeId>,

    // Control: the region tree, statements in program order.
    regions: Vec<Region>,
    effects: Vec<Effect>,           // each region's run is contiguous

    // Merges.
    joins: Vec<Join>,
    columns: Vec<Column>,           // each join's run
    rows: Vec<NodeId>,              // each join's rows, row-major
    // Each node points to itself or its replacement; chains are allowed.
    node_replacements: Vec<NodeId>,
}

pub enum NodeKind {
    Int(i64),
    Float(u64),                     // bits, so it hashes
    Param(u32),
    Unary(UnaryOp, NodeId),
    Binary(BinaryOp, NodeId, NodeId),
    Compare(CompareOp, NodeId, NodeId),
    Convert(ConvertOp, NodeId),
    DataEnd(MemoryId),
    MemoryIndex(MemoryId),
    StaticPointer { entry: StaticEntryId, offset: u32 },
    /// Column `column` of `join`: only where its rows disagree.
    Phi { join: JoinId, column: u32 },
    /// Result `index` of an effect. Never value-numbered.
    Result { effect: EffectId, index: u32 },
}

pub enum Effect {
    Call { function: FunctionId, args: Run },
    Load { address: NodeId, offset: u32, memory: MemoryId, access: LoadAccess },
    Store { address: NodeId, value: NodeId, offset: u32, memory: MemoryId,
            access: StoreAccess },
    /// An operation that can trap (`can_trap()`): it runs where it is
    /// written, even when its value is unused.
    Trapping(TrappingOp),
    GlobalGet(GlobalId),
    GlobalSet(GlobalId, NodeId),
    MemorySize(MemoryId),
    MemoryGrow(MemoryId, NodeId),
    MemoryFill { memory: MemoryId, dst: NodeId, value: NodeId, len: NodeId },
    MemoryCopy { dst_memory: MemoryId, src_memory: MemoryId,
                 dst: NodeId, src: NodeId, len: NodeId },
    /// A nested region: a block, a loop, an `if`, a switch.
    Region(RegionId),
    /// Leave toward `join`, contributing its row `row`.
    Branch { join: JoinId, row: u32 },
    Return { values: Run },
    Unreachable,
}

pub enum TrappingOp {
    Binary(BinaryOp, NodeId, NodeId),
    Convert(ConvertOp, NodeId),
}

pub struct Region {
    kind: RegionKind,
    effects: Run,                   // into `Function::effects`
}

pub enum RegionKind {
    /// A block; `exit` is the join its fallthrough and its breaks reach.
    Block { exit: JoinId },
    /// A loop: `header` merges entry and back edges, `exit` its breaks.
    Loop { header: JoinId, exit: JoinId },
    /// `then` and `otherwise` are regions; `exit` joins them.
    If { condition: NodeId, then: RegionId, otherwise: Option<RegionId>,
         exit: JoinId },
    /// Each case a region; `exit` joins them.
    Switch { selector: NodeId, cases: CaseRun, default: Option<RegionId>,
             exit: JoinId },
    /// The body of an arm or a case: no join of its own.
    Arm,
}

/// Values arriving from several edges.
pub struct Join {
    columns: Run,                   // into `Function::columns`
    rows: Run,                      // into `Function::rows`, `columns.len` wide
}

pub enum Column {
    /// A MIR local the construct writes.
    Local(LocalIndex),
    /// Scalar `i` of the construct's own value.
    Result(u32),
}
```

Every value is one scalar: MIR is scalar (`notes/mir-pipeline.md`, step 1),
so there are no aggregate nodes. A multi-result value (a call's, a
`Values`) is a run of nodes while building, and `Result { effect, index }`
for a call's results.

Effects are what runs in order: anything that can trap, touches memory or
globals, calls, or transfers control. A load is an effect because a store or
a call may change what it reads, and because it traps out of bounds; an
unused one is dropped only where that cannot remove a trap ("Dead loads").
Everything else is a node, placed where its readers need it.

## Building: MIR → graph

```rust
struct Builder<'a> {
    body: &'a mir::Body,
    function: Function,
    writes: WriteSets,
    bindings: Vec<NodeId>,          // per MIR local, its current value
    saved: Vec<NodeId>,             // write-set values saved around arms
    labels: Vec<Label>,             // per MIR label
    built: Vec<NodeId>,             // scratch: an expression's scalars
    open_effects: Vec<Effect>,      // scratch: regions being built
    open_rows: Vec<Vec<NodeId>>,    // scratch: rows of joins being built
}

/// Per MIR join construct, the locals it writes.
struct WriteSets {
    locals: Vec<LocalIndex>,
    of: Vec<Run>,                   // by the construct's `ExprId`
}

enum Label {
    Block { exit: JoinId },
    Loop { header: JoinId, exit: JoinId },
}
```

**Write sets** come first, in one bottom-up pass over the body: a `LocalSet`
or a `SetLocals` target writes its local, and a join construct (`Block`,
`Loop`, `IfElse`, `Switch`) writes the union of what its subtree writes,
deduplicated with a per-local stamp. `Sequence` is not a join and has no
entry. A local written inside and only read inside still gets a column; its
phi has no reader, so it is never emitted (see "Uses").

**Bindings** start as each parameter's `Param` and every other local's
`Int(0)`, Wasm's own initial value. `LocalGet` reads the binding,
`LocalSet` replaces it, `SetLocals` replaces several with a value's scalars
in order. An arm saves only the construct's write set before it runs and
restores it after, never the whole vector.

**An expression builds to its scalars**, pushed on `built`: none for `()`,
one, or several; or to nothing when it diverges, after which its parent
builds nothing more, as linearizing does.

Each construct, with `W` its write set and `R` its result scalars:

- **`Block`** with label `L`: a join `X` with columns `W ++ R`;
  `labels[L] = Block { exit: X }`. Its statements build into a new region.
  A `Break` of `L` appends the row `bindings[W] ++ value` and records
  `Branch { join: X, row }`; falling off the end appends a row too. When the
  block closes, each column resolves: one value if every row has it,
  otherwise a `Phi`. `bindings[W]` and the block's value are the resolved
  columns. No rows means the block diverges.
- **`IfElse`**: the condition, then each arm as a region, each that falls
  through appending a row; a missing `else` is a row of the entry bindings.
  Join `X` with columns `W ++ R`, resolved as a block's.
- **`Switch`**: the selector, then each case and the default likewise.
- **`Loop`** with label `L`: two joins.
  - The header `H`, columns `W`: its first row is the entry bindings. Its
    phis are needed while the body is built, before the back edges exist,
    so each column gets a placeholder `Phi { join: H, column }` up front and
    `bindings[W]` become those. A `Continue` of `L` appends a row, and so
    does falling off the body's end (the back edge).
  - The exit `X`, columns `W ++ R`, fed by `Break`s of `L`, resolved as a
    block's.
  - When the body closes, a header column whose rows are all the
    placeholder or one value `v` is trivial: `node_replacements[phi] = v`, read
    whenever a node's input is looked up. Users are not rewritten.
- **`Return`**: `Effect::Return` with the value's scalars.

**Value numbering**: a node is looked up in `interned_nodes` by its kind before
it is pushed, as `Builder::node` does today, and integer constants fold
there. `Phi` and `Result` nodes are unique by construction and not
numbered. A node numbered while its input was a loop placeholder that later
resolves misses a match against the resolved value; a renumbering pass can
recover those if it ever matters.

**Allocation**: a region's effects and a join's rows must end up contiguous,
but nested regions build in between, and a `break` deep inside adds rows to
an outer join. Both build on scratch stacks (`open_effects`, `open_rows`)
and move into the flat arenas when their construct closes, the pattern
lowering already uses for statement lists. The per-join row buffers are
reused across joins.

## Dead loads

### Raw-pointer and trap contract (decision, 2026-11-09)

Raw memory operations retain Wasm's observable trapping behavior, including
inside `unsafe`. An unsafe context permits operations the checker cannot
prove safe; it does not assert that those operations cannot trap, and does
not grant the optimizer undefined-behavior assumptions for invalid accesses.
Integer-to-pointer conversion alone is not evidence of a valid allocation,
alignment, lifetime or exclusive access.

Distinguish the selected linear memory's bounds from allocation/object
bounds. A scalar load/store whose full byte range is outside that memory
traps at its execution point. A numeric address inside memory can refer to
the wrong object or a freed allocation without trapping: the current runtime
does not enforce allocation bounds or pointer provenance. Preserving traps
does not add those checks. Address zero is not intrinsically trapping in
Wasm, and ordinary scalar accesses do not acquire an alignment precondition
from their pointer type.

Optimizer consequences:

- Preserve potentially trapping operations and their ordering relative to
  observable effects unless a proof establishes a legal transformation.
- Remove an unused ordinary load only after proving its accessed byte range
  cannot trap; preserve any effects of evaluating its address separately.
- Pointer type, integer origin and `unsafe` are not nontrapping proofs.
- Do not infer disjointness or immutable pointee contents merely from
  pointer types. Reusing or moving a read across a store/call requires a
  separate memory-dependence proof.
- Stronger allocation, aliasing or value-validity contracts would need an
  explicit language rule. They are not implicit consequences of this raw
  memory policy.

This decision concerns raw memory access. It does not promise stable trap
message text or establish a complete validity model for every transmuted
source type. A traps-never-happen mode is not part of the current plan.

### Removing proven nontrapping loads

A load traps when its bytes are out of bounds, so dropping an unused one can
remove a trap the program would have hit. Today's scheduler drops every
unused load. Here a dead load is dropped only when a rule proves it cannot
trap, and kept as `load; drop` otherwise. Which rules hold is to be
established by tests (step 3 of "Order of work"), not assumed. Candidates:

- **Covered by an earlier access.** Wasm memory never shrinks, so once an
  access to `address + offset` of a width succeeded, a later one to the
  same bytes, or fewer of them, of the same memory cannot trap. "Earlier"
  must mean on every path: in the same region before it, or in an
  enclosing region before the region holding it.
- **Inside static data.** A `StaticPointer` plus a constant offset whose
  bytes are within the memory's static data, which instantiation already
  required to fit.
- **Below a constant bound the memory has** (its minimum pages), for a
  constant address.

Anything else keeps its trap. The tests are programs whose unused load is
out of bounds (it must still trap), in bounds by each rule (it must
disappear), and the edge cases: a covering access only on one arm, a
`memory.grow` between (harmless: memory only grows), another memory.
Binaryen makes the same distinction, keeping a load that may trap unless
told traps never happen (`--traps-never-happen`). WX has chosen observable
traps as its current contract, including for unsafe raw memory access.

## Edges are data: `inputs`

```rust
impl Function {
    /// A node's inputs; a `Phi`'s are its column's rows.
    fn inputs(&self, node: NodeId) -> Inputs<'_>;
    /// An effect's operands.
    fn operands(&self, effect: EffectId) -> Inputs<'_>;
}
```

The one per-kind match, used by every pass, as MIR's `ExprKind::body_ids_mut` is.
`Inputs` iterates operands in the kind, a run of `operands`, or a column of
`rows`, and follows `node_replacements`. A new kind is one arm here.

## Uses

Revised 2026-11-09: [Demand-driven planning](opt-demands.md) is the
current direction and replaces the former mark/count/prefix-sum/fill plan.
Discover necessary values from retained effects and collect use sites in
the same dependency traversal. Store each value's uses as an index-linked
list in a flat record array; the requested-value vector also serves as the
work queue. There is no standalone boolean-only liveness phase.

Use sites distinguish node operands, effect operands and incoming join
rows, preserving duplicate operand occurrences. Placement consumes this
information after discovery finishes. Unrequested values have no emitted
computation; unused effect results still follow the trap-preservation rules
above. This replaces `liveness.rs`, per-node allocated `uses` vectors and
`register_uses`; exact placement and count-summary needs remain to be
established with the emitter.

## Emitting: graph → MIR

The initial implementation contract and worked placement examples are in
[opt-placement.md](opt-placement.md). The first emitter uses locals before
adding the expression nesting and construct-result optimizations below.
Value placement and structured MIR emission are implemented in tests;
production integration remains a separate milestone. Placement uses control
dominance rather than region ancestry alone, to handle loop values read
after a loop exits.

`opt` writes MIR, which linearizing turns into Wasm
(`notes/mir-pipeline.md`, "Codegen: MIR → wasm"). The output is a fresh MIR
body, built from the structured regions after packing computations by gap:

- **A region** keeps its control construct: `Block`, `Loop`, `IfElse` or
  `Switch`. If/switch wrappers get an enclosing labelled block to receive
  their explicit exit branches. Effects remain in their original order.
- **A computed node** is assigned to a gap by control dominance and input
  availability, then written to a fresh local. Its readers get `LocalGet`
  expressions. Constants, parameters and static pointers are emitted at
  each reader. Single-reader expression nesting is a later refinement.
- **A construct exit join** uses locals for its required canonical phis.
  Each exit assigns its row before breaking; following computations can
  read those locals. Using multi-value construct results instead is a
  later optimization, not part of the initial emitter.
- **A loop header join** also uses locals. The entry row is assigned before
  the loop; every back edge assigns its row before `Continue`. Any row with
  several live columns uses `SetLocals(Values(...))`, evaluating all sources
  before writing any target. This also handles cyclic swaps and rotations.
- **An unused effect result** is discarded through a `None` assignment
  target. The effect itself still runs, including calls, loads, trapping
  arithmetic, global reads and memory queries. Safe effect removal remains
  a separate change under the trap contract above.
- **`Switch`** stays a `Switch`; linearizing chooses `br_table` or an `if`
  chain (`codegen::uses_br_table`).

Expression nesting, construct results, local reuse and effect removal are
possible refinements after this baseline. They must preserve effect/trap
ordering and value availability; the current implementation assumes no
additional raw-pointer aliasing or validity guarantees.

## What goes away

`opt/builder.rs`'s join machinery (`JoinData`, `create_loop_params`,
`create_join_params`, `carried_binding_updates`, `patch_loop_binding`,
`finalize_block_join_binding`, `record_exit_value`), `StackResult`, the
aggregate nodes, `ControlNode::{Loop, BlockJoin}` with their update lists,
`opt/liveness.rs`, `DataNode::uses` and `register_uses`, and the
scheduler's Wasm emission. `opt`'s own `MemAccess` and `TrappingOp` take
MIR's enums. `opt/local_dominance.rs` checks the instruction list that
`coalesce_locals` reads; it stays with that pass, which runs on
linearizing's output.

## Order of work

Replaces steps 2.3–2.5 of `notes/mir-pipeline.md`. Each step leaves every
test passing, run both ways (`WX_NO_OPT=1`).

1. **The graph and its builder** (done; one difference from the text
   above: a `Branch` closes every edge, a region's fall-through end
   included, so each row has the effect that gives it, and an `if` without
   an `else` has an `otherwise` arm holding only its `Branch`): `Function`, `WriteSets`, `Builder`,
   `inputs`, beside today's `opt`. Tested by building every function of the
   wasmtime suites and checking the graph (every input below its user but a
   phi's, every row as wide as its join, every `Branch` inside its join's
   construct).
2. **Demand discovery and use collection**, following
   [opt-demands.md](opt-demands.md), tested on the same graphs: retained
   effects request their operands, each requested value expands once,
   and use records preserve operand occurrences and incoming row sites.
3. **Emission to MIR**, then linearizing. Codegen runs new builder →
   emission → linearize; the old builder, scheduler and liveness go. The
   goal is correctness and the simplifications (value numbering, folding,
   joins only where values differ, dead values), not a smaller binary:
   simplifying can make some output larger. Each example's size is
   measured against `WX_NO_OPT`'s and today's `opt`'s and a change in
   either direction is read case by case, with a test for what it shows.
   The dead-load rules are settled here, by their tests.
4. **Child of its user, or a local**, and control-flow values as results.

## Open points

1. **Write sets name dead locals.** A local only used inside a construct
   costs a column (a `NodeId` per row) and nothing in the output. Trimming
   columns by liveness on MIR is possible if memory ever matters.
2. **Numbering across a resolved placeholder** (see "Value numbering").
3. **Dead loads**: which rules hold (see "Dead loads"), and whether wx
   wants a "traps never happen" setting at all.
4. **Loop-invariant code**: placement never moves a node out of a loop
   whose body is its only reader. Hoisting is a later pass on the graph.
