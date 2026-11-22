# Graph backend integration plan and checks

Status: default backend migrated, 2026-11-09, branch `tir-refactor`.
Follows [placement and emission](opt-placement.md) and the target sequence in
[mir-pipeline.md](mir-pipeline.md).

`backend::emit` now runs optional inlining, `opt::optimize_reachable`, and
`codegen::Builder::build(&MIR, &StringInterner, &Reachability)`. The new graph
pipeline is the sole normal backend. The legacy optimizer, scheduler and
liveness sources and both backend-selection flags have been removed. Direct
original-MIR linearization remains a test-only execution reference.

The optimizer modules and graph types now live directly under `opt`; the
transitional `opt::graph` namespace was flattened after legacy removal.

## Decision: optimize functions when reachability discovers them

Accepted 2026-11-09. After optional inlining, start from the module's roots and
optimize each defined function when it is first reached. Discover dependencies
from its freshly emitted MIR, then pass MIR and reachability to codegen.

```text
lower → optional inline
      → module reachability worklist:
          reached defined function → optimize body → enumerate final references
          other reached item      → enumerate dependencies
      → codegen(MIR, reachability): assign output indices to reached items
      → linearize reached bodies → encode
```

This avoids optimizing bodies that are never reached. In particular, inlining
may leave an unreferenced original callee, and optimizing a caller can remove
unreachable calls before their callees enter the worklist. Matching the old
optimizer's output shape, local coalescing and linear-instruction peepholes are
not integration prerequisites. The measurements below are observations, not
behavior or performance requirements.

The worklist schedules work; function optimization, dependency enumeration and
output assembly remain separate operations. Do not introduce a persistent
dependency graph or maintain edges through every body transformation.

Algorithm and invariants:

1. Seed roots from exports of every item kind and the start function. Mark an
   item when enqueuing it, so duplicate references and recursive cycles process
   each item once.
2. For a reached defined function, build its graph, collect uses and locations,
   build placement, emit fresh MIR and replace its original body. Only then
   enumerate that function's module references. An imported function has no
   body to optimize.
3. For other reached items, enumerate their dependencies under the module's
   retention policy. The worklist covers functions, globals, memories and static
   entries; imports are metadata of retained items, not independent roots.
4. Keep all MIR item IDs stable throughout discovery, optimization and codegen. A
   reference may point to a function that has not yet been processed. Its
   signature remains available; its optimized body is not required by the
   current local optimizer.
5. Once discovery finishes, codegen uses the marks to select imports, function
   bodies, globals, memories and backing data. Its existing MIR-to-Wasm maps
   assign output indices only to retained items; references resolve through
   those maps without rewriting MIR IDs or moving MIR table entries.

Per-function graph and planning storage expires before the next function is
processed. `Placement` borrows the graph, not `Uses` or `Locations`, so those
analysis tables can expire after placement construction. Module marks and the
worklist live through discovery; marks survive through codegen, whose output
index maps live through assembly and encoding.
There is no requirement to retain per-function graphs or dependency lists.

### Scope and future scheduling

Inlining remains an earlier stage. Its root information can still guide inline
decisions, but final reachability belongs to the module driver and output
filtering belongs to codegen. Whether inlining is enabled does not change this
contract. Remove the inliner's physical dead-function cleanup during integration.

The initial driver processes each reached function once. This assumes local
optimization does not rewrite previously processed functions or require optimized
callee bodies. If future inlining, specialization or interprocedural summaries
invalidate those assumptions, add explicit scheduling/invalidation rules and
targeted revisits or a fresh reachability pass. There is no whole-pipeline
repeat-until-unchanged loop in the initial design.

This avoids work on items never discovered; it is not a promise that no processed
item can ever become dead under future cross-function transformations. An early
reachability scan followed by optimization and a final scan remains a reasonable
alternative if later scheduling constraints make that simpler.

Preserve initialization effects through the start root; unread global writes
are not removed by module reachability alone.

### Decision: retain MIR IDs and filter during codegen

Accepted 2026-11-09. Physical MIR compaction and ID rewriting are not required
for the initial pipeline. Codegen already assigns separate Wasm indices, with
imports first and equivalent imports merged. Make that mapping selective rather
than introducing an earlier MIR-to-MIR renumbering pass.

Pass optimized MIR plus `Reachability` into codegen. Filter imports by the item
they provide before assigning indices or merging import descriptors. Assign
indices and emit sections/bodies only for reached functions, globals and memories.
Lay out only marked backing-data entries, patching their relocations through the
retained-data layout; replace codegen's separate backing-data discovery walk.
Calls, exports and start resolve existing MIR IDs through the output maps.
`DATA_END` uses the retained-data layout, as already decided below.

Check that each reference in retained content targets another retained item;
a missing output mapping is an invariant failure, not a reason to emit a dead
item. Include import-before-definition ordering, merged imports and gaps in every
MIR item ID space in the output tests. Dead bodies must not be linearized.

Reachability decides retention; codegen consumes that decision without performing
another dependency analysis. No item tables, flags, import origins, initializers
or relocation targets need their MIR IDs rewritten. Unreachable storage remains
allocated until MIR is dropped. Earlier storage reclamation or physical compaction
can be added if measured memory use or a future consumer warrants it; neither is
an integration prerequisite. This supersedes the earlier compaction plan.

### Decision: constants do not require runtime backing storage

Accepted 2026-11-09. WX constants define compile-time values, not an obligation
to initialize bytes in the output module. MIR static entries are backend-owned
backing storage for values that need memory representation; they are not
independently retained source declarations.

Use reference-based reachability:

```text
exported pointer global → backing data → memory
reachable function     → backing data → memory
backing data           → relocation targets
exported memory        → memory only
```

Exporting or otherwise retaining a memory does not retain every backing entry
assigned to it. A constant string or array whose backing data has no reachable
reference can disappear, even when that memory is exported. To expose backing
data to a host, put its pointer in a global and export that global; its
initializer retains the data and the host obtains the compiler-chosen address
through the global. Reachable functions and relocation targets can also retain
backing entries.

The compiler may choose the layout of retained backing data. Incidental numeric
addresses are not roots and do not require unused constants to be materialized.
`DATA_END` describes the resulting retained-data layout; referring to it retains
the memory, not all candidate backing entries. Exported memory exposes the
resulting memory contents without imposing a reverse dependency on otherwise
unreferenced constants.

This supersedes the earlier recommendation to retain all static entries of a
retained memory. It does not relax preservation of executed memory operations,
their effects or their defined traps. Explicit fixed-address memory images,
should WX need them later, require a separate deliberate language contract.

Acceptance checks before switching the default:

- An unreachable or fully inlined callee is never passed to function optimization
  unless another root/reference reaches it.
- A removed call does not enqueue its callee; a retained call does.
- Duplicate calls, self-recursion and mutual recursion process each reached
  function once; unreachable cycles are absent from output.
- Exported items and the start function remain roots, including initialization
  effects and observable memory contents.
- Globals, memories, static relocation chains/cycles and mixed imported/defined
  items obey the chosen dependency and retention rules.
- Codegen emits only marked imports/items/data, handles gaps in stable MIR IDs,
  and resolves calls, exports, start, initializers and relocations consistently.
  Retained references target retained items; Wasm validates and executes.

## Current responsibilities

### Selective codegen implemented

`codegen::Builder::build(&MIR, &StringInterner, &Reachability)` now
consumes the marks and directly linearizes retained bodies. It filters imports
before descriptor registration, merging or index assignment, and emits only
retained function signatures/bodies, globals and memories. Dead bodies are never linearized. Graph verification belongs to function
optimization and its focused tests; codegen does not rebuild graph analyses. Output function buffers reserve for retained definitions,
not the whole MIR function table.

Static layout receives marked entry IDs directly, orders them deterministically
by alignment and ID, then patches relocations using the retained addresses.
`DATA_END` reflects this layout. Missing retained targets are invariant failures;
there is no fallback that emits an unmarked item. Codegen borrows MIR and marks
only during assembly, and neither is retained by the resulting Wasm module.

Five selective-output checks cover gaps in every ID space, import-first ordering
and merging for all import kinds, omitted dead import signatures, skipped invalid
dead bodies, calls and global/memory reads, static-pointer offsets, relocation
addends and DATA_END, exported-memory retention, start-only initialization and
rootless programs. They validate Wasm and execute observable results with
Wasmtime. The earlier removed-callee execution check now also asserts that only
the caller is emitted while both MIR function entries remain intact.

Validation before default integration: all 8 codegen migration checks passed;
the full compiler library suite had 1,416 passing tests and 2 ignored. Release compilation, formatting and
whitespace checks pass.

The normal backend now uses this path. The temporary all-items output path and
`legacy_static_entries` have been removed. Inlining no longer deletes functions,
compacts IDs or rewrites import entries. Its root columns remain useful for
one-call-site inlining policy. `None` in `backend::emit` skips only inlining;
optimization and output retention always run.

Integration tests run through the default backend with and without inlining.
They check that a removed call does not keep a host import, while MIR entries,
export IDs and import origins stay valid. The structured-emission execution
corpus now compares the default backend against direct original MIR, including
simultaneous join updates and trap ordering. The constant-integer test retains
runtime values and overflow traps; its legacy requirement that every safe
constant division disappear has been removed. Constant folding, local coalescing
and peepholes can be improved independently later.

Default integration validation: 1,411 compiler library tests pass, with 2 ignored.
Legacy dominance tests disappeared with the removed optimizer; structured-graph
placement and execution checks remain. Release checks pass for both compiler and
CLI. A real CLI build was validated and executed in Node: loop swaps, global
initialization and writes produce expected values, the dead host import is
absent, and the source still reports its unreachable-code warning. Formatting
and whitespace checks pass.

### Reachability worklist implemented

`opt::optimize_reachable(&mut MIR) -> Reachability` now discovers retained items
across the whole MIR program destined for one Wasm output. Here "module" means
that output unit, not a source file or namespace. It seeds exports and start,
marks on enqueue, and uses an iterative pending-item stack. Each reached defined
function runs through `optimize_function` before `MIR::dependencies` enumerates
its replacement body. Imported functions are marked but never optimized.

`Reachability` owns four dense `Vec<bool>` columns indexed by the existing
function, global, memory and backing-data IDs. Boolean vectors are the accepted
initial representation; no packed bitset is needed. Marking suppresses duplicate
work and terminates recursive calls and relocation cycles. The result contains
only membership, queried with `is_reachable(Reference)`, and does not retain
bodies, dependency lists or the pending stack. Further changes to roots or bodies
can invalidate it. Item tables remain intact with stable IDs; selective codegen
consumes these marks in the default backend.

Apart from function optimization, discovery costs table-sized mark initialization
plus root enumeration and one dependency scan per reached item. Each item enters
the pending stack at most once. This does not imply that the entire optimizer is
linear: graph construction and placement retain their own complexity.

Tests record exact optimization counts while invoking the real optimizer. They
cover removed and retained calls, duplicate roots/calls, self and mutual recursion,
unreachable cycles, imported items of every kind, pointer globals, relocation
cycles, memory and DATA_END retention policy, start initialization effects, an
empty root set and a 4,096-function call chain. A lowered execution check confirms
that a callee referenced only after return remains untouched and unmarked, both
with no inlining and with attribute-only inlining; the optimized caller executes
correctly through direct linearization.

Validation: all 9 reachability checks pass; the full compiler library suite has
1,411 passing tests and 2 ignored. Release compilation and formatting checks pass.

### Single-function optimizer implemented

`opt::optimize_function(&mut MIR, FunctionId)` now builds the graph, collects
uses and locations, builds placement, emits replacement MIR and replaces that
defined function's body. Passing an imported function is a caller error; the
module driver distinguishes imports before scheduling optimization.

Function IDs, signatures and other module item IDs remain stable. Other bodies
are untouched, and emission may append interned multi-result signatures. Uses
and locations expire after placement construction; graph and placement expire
before replacement of the original body. Graph and emitted-body verification
remain test-only. Placement failure is an internal compiler invariant failure,
not a reason to fall back to the old optimizer.

The all-functions test helper delegates to this entry point, so the existing
execution and trap-order corpus exercises the same function pipeline. An
additional execution check optimizes only a caller and verifies that its callee
body, function identities, flags, exported root and call dependency stay intact.
The optimized caller executes with the unoptimized callee.

Validation: 17 graph-emission tests pass; the full compiler library suite has
1,402 passing tests and 2 ignored. Normal and release compiler checks pass.
Promotion to normal builds also exposed an assertion requiring test/debug-only
`ValueType::Debug`; it now checks the same signature equality with a fixed
diagnostic, retaining the invariant check in release builds.

The reachability driver above now uses this entry point.

### Reference enumeration implemented

`mir::references` now provides `Reference::{Item, Data}`, borrowed `ItemRef`s,
`MIR::roots` and `MIR::dependencies`. `ExprKind::items_mut` exhaustively names
the module IDs stored in each expression, independently of its body-local
children. The same mutable visitor supports discovery on a copy and later ID
rewriting. Initializers, address targets, static entries and import/export
`Item`s also expose mutable reference visitors.

Enumeration streams direct references to a callback without allocating lists or
deduplicating. It scans a defined function's current arena once, visits a data
entry's relocations once, and does constant work for other dependency kinds.
The worklist owns transitive traversal and marking. Its caller must
replace a reached function's body before dependency enumeration; enumeration
does not itself determine which control-flow paths execute.

Tests cover every expression kind containing module references, both memories of
a copy (including equal IDs), imported items, roots, initializers, relocation
cycles, no reverse memory-to-data edge and mutable ID rewriting. Module discovery now consumes this API in place of the old cleanup scans.
Output filtering leaves MIR table entries intact. The mutable visitors remain available for
future transformations; the initial pipeline does not need a MIR remapping pass.

| Responsibility | Current owner |
| --- | --- |
| Optional inlining | `backend::emit` calls `mir::inline::run` before optimization; all MIR IDs and table entries remain intact. |
| Retention and function optimization | `opt::optimize_reachable` seeds all exports and start, optimizes reached bodies, then enumerates their final references. |
| Inlining roots | `mir::inline::roots` still supports the one-call-site policy; it does not decide final output. |
| Static-data selection and layout | The driver marks entries; `codegen::lay_out_static_data` places only those entries and patches relocations. |
| Wasm instruction emission | The MIR linearizer, followed by encoding with retained-item maps. |
| Local instruction cleanup | Independent helpers in `wasm`; optional, not connected to the default pipeline. |
| Backend orchestration | `backend::emit`, with no environment flags selecting alternative optimizers. |

## Reachability regression

`codegen::checks::graph_emission_removes_dead_calls_without_changing_item_ids`
checks that per-function graph emission removes calls after an unconditional
return while preserving MIR table entries. The full reachability/codegen check
then confirms that only the caller reaches the output and that the callee remains
untouched in MIR. The default backend also has a source-level regression proving
that such removed calls omit their host imports, with and without inlining.

## Size and local-count comparison

Current direct/new-graph measurements can be reproduced with:

```sh
cargo test -p wx-compiler --lib codegen::checks -- --nocapture
```

`compare_emitter_size_locals_and_execution` builds each source afresh, applies
the same default inlining policy, then explicitly selects direct MIR, the new graph, or the new graph with the
optional local-tee cleanup. The old optimizer has been removed; the table below
preserves the measurements collected before migration.
It bypasses environment-based backend selection. Every module is validated and
executed under Wasmtime; each path is compared with original MIR through the
direct linearizer on 18 input pairs per fixture.

Each cell below is **encoded module bytes / non-parameter Wasm locals**, summed
across defined functions. Bytes include module sections, not just instructions.
All cases have one defined function except `calls`, which retains two.

| Fixture | Direct MIR | Old optimizer | New graph | New graph + existing local cleanup |
| --- | ---: | ---: | ---: | ---: |
| Shared arithmetic | 53 / 0 | 54 / 1 | 69 / 4 | 63 / 4 |
| Conditional | 61 / 0 | 70 / 2 | 91 / 5 | 87 / 5 |
| Dense switch | 85 / 0 | 104 / 1 | 120 / 5 | 112 / 5 |
| Swapping loop | 104 / 5 | 95 / 3 | 124 / 8 | 118 / 8 |
| Nested loops | 123 / 6 | 182 / 9 | 156 / 10 | 152 / 10 |
| Retained calls | 65 / 0 | 75 / 2 | 95 / 6 | 89 / 6 |
| Total | 491 / 11 | 580 / 18 | 655 / 38 | 621 / 38 |

On this corpus the unrefined graph emitter is about 13% larger than the old
optimizer, or 7% larger with the existing local cleanup. The cleanup does not
remove local declarations. Graph output is smaller than old output for nested
loops, despite more locals; local count alone does not predict module size.

These six small synthetic fixtures establish a reproducible baseline, not a
claim about typical applications, compilation speed, runtime performance or
peak memory. Trap-order correctness uses the dedicated emitter tests and direct
MIR reference, not the old optimizer. No size budget is asserted: later changes
may legitimately alter these measurements, while execution equivalence remains
a test requirement. Expression nesting, construct results and local reuse stay
separate improvements.

## Implementation sequence

1. Done: establish authoritative module-reference enumeration and root discovery for
   the general item model, using the reference-based backing-data policy above.
2. Done: expose a single-function optimizer entry point with the lifetime described
   above, independently callable by the module driver.
3. Done: implement the reachability worklist: optimize a reached body before discovering
   its references. Keep IDs stable and test exactly which bodies are processed.
4. Done: make codegen consume reachability: filter imports and item sections, assign
   Wasm indices only to reached items, and lay out marked backing data without
   repeating discovery. Test ID gaps, output reference resolution and skipped dead
   bodies. Keep MIR IDs and tables unchanged.
5. Done: wire the orchestrator to normal MIR linearization and encoding. Validate the
   acceptance cases, then remove the inliner's physical dead-function cleanup,
   the old optimizer and backend-selection flags.
   Local cleanup and local coalescing can be connected later.

The broader dependency graph in `mir-pipeline.md` still applies. The accepted
stable-ID/output-filtering decision replaces its earlier MIR renumbering proposal.
