# Demand-driven planning for `opt`

Status: initial discovery implemented, 2026-11-09, branch `tir-refactor`.
This refines the use analysis in [opt-design.md](opt-design.md#uses).
`opt/uses.rs` implements collection beside the new graph, callable in
normal builds through `opt::optimize_function`. Value placement and structured graph-to-MIR
emission with simultaneous join updates are implemented and used by the
default backend. The old separate liveness analysis has been removed.

## Goal

Discover the values required by observable execution and collect their use
sites together. Make that discovery the start of emission planning, rather
than a whole-graph liveness pass whose only output is a boolean per node.

The graph already answers “what inputs does this value need?” Planning also
needs “where is this value read?” Repeatedly scanning the graph for that
answer is expensive. Build the reverse information while following demand.

This follows the demand-driven direction of the TIR checker: request what
is needed, record that request, and expand its dependencies once. It does
not require adopting the checker's implementation or obligation machinery.

## Scope and phase boundaries

The intended per-function sequence is:

```text
MIR → graph construction
        → demand discovery and use collection
        → placement and MIR emission
        → linearization
```

Demand discovery reads the completed graph, not the original MIR tree.
It follows only requested value dependencies. Walking the structured effects
to seed requests is still necessary, as is traversing regions for emission.
This proposal does not eliminate every traversal or the builder's write-set
prepass. Removing that prepass would require a separate join-builder design.

Placement must wait until relevant demands have arrived. A value requested
once now may be requested again by a later effect or another branch. Discovery
alone cannot immediately decide that it is safe to inline that value at its
first reader.

## Data

Use flat arrays and indices. The initial representation is append-only
during discovery and read-only during placement and emission:

```rust
// Sketch: index types and accessors follow the graph's conventions.
struct Uses {
    first_use: Vec<Option<UseId>>, // indexed by canonical NodeId
    records: Vec<UseRecord>,
    used_nodes: Vec<NodeId>,       // each used node exactly once
}

struct UseRecord {
    site: UseSite,
    next: Option<UseId>,
}

enum UseSite {
    Node(NodeId),
    Effect(EffectId),
    Row { join: JoinId, row: u32 },
}
```

`first_use` was called `heads` in the discussion: it is the head of each
value's linked list of use records, not a root of the data-flow graph.
`UseId` indexes `records`. `None` means no use has been recorded; a record's
`next: None` ends its list. Index zero remains a valid record index.

```text
first_use[v0] → records[5] → records[2] → None
                  │            │
             Effect(e1)     Node(v3)
```

Records are linked by indices inside one vector. There is no allocation
per record or per value. Insertion prepends a record, so list order is not
execution order. Program order comes from regions and effects.

The initial design does not require a persistent count array. Counts can
be obtained by walking a value's list. If repeated count queries are needed,
collect a count, or a zero/one/many summary, during requests; avoid repeatedly
scanning lists for the same answer. Choose this from the emitter's actual
queries. Exact byte sizes and optional-index encodings should be measured
before introducing packing.

## Requesting a value

Every operand occurrence is a request. Resolve forwarding aliases to a
canonical value before recording it.

```text
record_use(value, site):
    value = resolve(value)
    previous = first_use[value]

    append UseRecord { site, next: previous } to records
    first_use[value] = the appended record's id

    if previous is None:
        append value to used_nodes
```

Install the first record before expanding dependencies. A nonempty list
then also means “already discovered”; no separate liveness bit is needed
for this algorithm.

Record occurrences, not just distinct consumers. In `Multiply(v0, v0)`,
`v0` has two use records pointing to the same consumer. Collapsing these
would incorrectly suggest one operand use. The consumer's own inputs are
expanded only once, however, regardless of how many readers it has.

## Processing pending values

Use `used_nodes` itself as a growing work queue with a local read cursor:

```text
cursor = 0
seed requests from the structured effects

while cursor < used_nodes.len:
    value = used_nodes[cursor]
    cursor += 1
    request each input occurrence of value with its use site
```

The processed prefix stays available for later placement. New requests
append to the same vector. A separate `Vec<NodeId>` stack is possible, but
unnecessary initially: dependency discovery does not need depth-first or
dependency-completion order. The queue is compiler scratch, not a runtime
stack in the generated program.

Requests may also be seeded and drained incrementally while traversing
effects, retaining the cursor. Placement still waits for discovery to finish.

## Roots, effects and joins

Seed discovery from operands of effects retained for execution: calls,
stores, returns, conditions/selectors, potentially trapping operations,
and other ordered operations under the current conservative effect policy.
An unused result does not imply that its producing effect can disappear.

Ordinary pure nodes request inputs at `UseSite::Node(consumer)`. Effects
request operands at `UseSite::Effect(effect)`. A requested phi requests
the value in its column of every incoming row, at `UseSite::Row { join,
row }`. Do not request every column of every branch row: unused columns
must not make their inputs needed.

Row identity matters for placement. An incoming value is consumed on its
incoming path, not at the merge's common location. A loop header's entry
row belongs before the loop; back-edge rows belong at their corresponding
continues or body end. Branch effects identify explicit row contributions;
loop-header entry is implicit in the current graph. Placement needs a
consistent way to locate both.

The current `inputs` callback yields values only. Filling use records also
needs phi row identity. Provide one consistent dependency enumeration that
supplies that context so the traversal and recorded edges cannot disagree.

Effect-removal policy must remain consistent with demand. For example, if
we later prove an unused load cannot trap and remove it, its address must
not remain required solely through that removed effect. Initially preserve
potentially trapping loads; settle safe removal rules with the emitter's
tests, as described in `opt-design.md`.

## Cycles and completion

```text
p = Phi(entry_value, next)
next = Add(p, 1)
```

The first request for `p` schedules it. Expanding it requests `next`;
expanding `next` requests `p` again. That second request records a use but
does not reschedule `p`, since its first-use entry already exists.

Each requested value expands once, so reachable loop cycles terminate.
Unrequested cycles are never expanded. Reference counting without this
rooted discovery would incorrectly retain such dead cycles.

The queue is a discovery order, not a topological emission order. A later
algorithm that requires completed input answers must explicitly handle
cycles; the request algorithm does not solve placement by itself.

## Layout and lifetime

Construction owns bindings, open joins, saved state, row-buffer pools and
value-numbering lookup tables. Release construction-only data before demand
analysis where possible. In particular, `Function` currently retains the
`interned_nodes` hash table; move or release it once no phase needs to create
numbered nodes.

The graph, demands and placement data live through MIR emission for one
function. Temporary discovery state is just the read cursor. Once emission
finishes, release the graph and analyses and retain the new MIR body.
Reusable buffer capacity across functions is an implementation option;
per-function contents and IDs must not escape their lifetime.

Keep the graph immutable while these demands are consumed. The analysis
describes one graph version. Changing dependencies or effect retention can
invalidate it. An analyzed-function wrapper borrowing the graph can make
this boundary explicit.

Use sites identify readers, not final locations for movable nodes. Store
placement separately: the location of a node reader is itself a planning
result. Avoid duplicating region/statement locations in every use record.

## Cost and tradeoffs

With constant-time canonical-ID lookup, discovery takes time proportional
to the effects visited, requested values, and their input occurrences.
Phi inputs include incoming row entries. It does not scan all nodes merely
to mark them, although initializing `first_use` is still proportional to
the number of allocated graph nodes.

Recording a use is amortized constant time. Reading a value's uses is
linear in its list length. Persistent demand storage is one optional head
per graph node, one record per demanded operand occurrence, and one ID per
requested value. The current forwarding lookup follows chains; its cost
must be counted unless canonicalization is made cheap.

The tradeoff against prefix-summed contiguous reader slices is locality:
insertion needs no count/prefix/fill passes, but readers of one value may
be scattered through `records`. If placement repeatedly walks long lists,
measure before deciding whether to group records later. Likewise, do not
discard reader lists in favor of placement summaries until the placement
algorithm proves those summaries sufficient, including movable consumers
and loop cycles.

## Implementation milestones

1. Add demand storage and context-aware dependency enumeration beside the
   graph. Seed requests from retained effects and drain the growing queue.
2. Test duplicate operand uses, shared subgraphs, unused pure chains,
   unused cycles, live loop cycles, phi row sites, forwarded aliases, and
   calls/trapping operations with unused results. Check that every requested
   node expands once and all recorded sites correspond to actual uses.
3. Design placement against these demand queries, then emit MIR. Finalize
   decisions only after all relevant requests are known; do not restore a
   standalone boolean-only liveness phase as an intermediate requirement.
4. Measure record layout and access patterns. Add count summaries, direct
   row-location indexes or other derived arrays only for demonstrated
   consumer needs. Advanced packing, incremental graph edits and removal
   of the write-set prepass are separate decisions.

## Initial implementation and issues found

The initial implementation provides `Uses::collect(&graph)`,
`used_nodes()` and `sites(value)`. The analysis borrows its graph, preventing
mutation while that analysis remains in use. Queries accept forwarding
aliases; stored readers and requested values use canonical node IDs.
`Function::inputs` supplies both input values and use sites, including phi
row identity, from one dependency enumeration.

Root discovery scans the flat effect table, rather than recursively walking
regions. The graph invariant guarantees that every stored effect occurs
exactly once in the structured program; all are retained for now. This scan
needs no execution order. If a later transformation leaves orphan effects
in storage, it must restore that invariant or change root enumeration.
Codegen tests now run discovery after building and verifying each graph.
Validation: `cargo test -p wx-compiler --lib` passed with 1,355 tests passed,
two ignored and no failures. Coverage includes duplicate operands, shared
dependencies, forwarding, unused effect results, live/dead loop cycles,
row sites and duplicate row suppliers.

An existing verifier gap allowed two branches to supply the same row while
another row was missing, provided the total branch count matched. Since row
identity matters to use sites, verification now tracks individual rows,
including the loop header's implicit entry, and rejects duplicate suppliers.

Open decisions for subsequent milestones:

- Resolved by `Locations`: row sites now have a direct location lookup,
  including implicit loop entry. `Placement` consumes these locations; see
  [opt-placement.md](opt-placement.md) for the implementation and remaining work.
- Keeping all effects roots is deliberately conservative. An effect-removal
  change must update demand rooting and emission together.
- Forwarding chains are still followed on lookup. No normalization pass or
  path-compression storage has been added without evidence it is needed.
- The builder's `interned_nodes` table still lives in `Function`. Releasing it or
  moving it into construction-only storage remains a graph ownership change.
- `Option<UseId>` follows the existing plain-u32 index convention. Its size
  and reader-list locality remain measurement questions; compact encoding
  and count summaries are deferred until placement establishes its queries.

Naming: the module and retained data are called `uses.rs` and `Uses`,
because they describe where values are read. Demand-driven discovery names
the algorithm, rather than the resulting data. `record_use` records one
operand occurrence and queues a node only on its first use.

The next milestone's location, availability and conservative emission
contracts are recorded in [opt-placement.md](opt-placement.md).
