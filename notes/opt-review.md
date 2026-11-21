# Backend review and cleanup

Reviewed 2026-11-10 after the default-backend migration and namespace flattening.
This is a review of the current implementation, not a plan to reproduce the old
optimizer's output. [Integration status](opt-integration.md) records the pipeline.

## Completed in this pass

- Removed the codegen test hook that rebuilt a graph and repeated uses, location
  and placement analysis. The per-function optimizer already verifies its graph
  and emitted MIR. Direct-MIR execution comparisons now avoid graph placement.
- Named emitter tables by their indexed domain and payload, and documented the
  trailing offsets. Corrected the builder's misleading “one walk” description
  to explicitly include the write-set prepass.
- Replaced the switch density calculation with an exact integer comparison;
  selecting a branch table needs no floating-point arithmetic.
- Corrected stale current-status text in the placement notes and marked old
  backend flags as historical.

## Naming candidates for discussion

| Current name | Candidate | Reason / tradeoff |
| --- | --- | --- |
| `opt::Function` | `FunctionGraph` | Distinguishes the analysis representation from `mir::Function` and `wasm::Function`, especially after flattening. This is the most useful broader rename. |
| `Run` | `TableRange` or `IndexRange` | Describes a contiguous range in a flat table; `Run` is short but requires learning a local convention. Avoid `NodeRange`: it also indexes effects and columns. |
| `Function::edges(join)` / `Join::edges` | `row_count` | The count is specifically incoming join rows, not arbitrary graph edges. Use the join argument to keep its domain clear. |
| `Function::node` / `push` | `intern_node` / `push_unique_node` | Makes the difference between value interning and identity-bearing phi/result allocation explicit at call sites. |
| `Builder::built` | `value_stack` | Stores scalar results while recursively constructing MIR expressions; it is not a completed-node set. |
| `Builder::pool` | `row_buffers` | Owns reusable incoming-row buffers for open joins. |
| `WriteSets::of` field | `construct_writes` | Makes the ExprId-indexed range column clearer; keep the query method short if desired. |
| `UseSite::Row` | `JoinRow` | Clarifies that this is a phi input read on an incoming edge. Current documentation already explains it. |

Emitter internals already renamed in this pass: `result_starts` →
`effect_result_offsets`, `results` → `effect_results`, `gap_bases` →
`region_gap_offsets`, `starts` → `computation_offsets`, and `scheduled` →
`scheduled_computations`. No public naming changes were needed for those fields.

## Follow-up work, in priority order

The workspace audit also found a separate frontend migration gap: `wx-lsp`
still imports removed typechecker APIs (`TIR`, namespace/impl/type-parameter
representations and `ast::DefId`) and private `TextSpan` reexports. This prevents
`cargo check --workspace` from succeeding. The browser compiler wrapper also
still calls removed TIR/MIR constructors.
Both frontend migrations are explicitly outside this cleanup at the user's
request; no changes to either frontend are retained. The excluded `wx-lsp-wasm`
frontend was not audited.

1. **Retire disconnected source after checking test coverage.** `mir/mod.rs`
   explicitly lists the old lowering/helpers still on disk. `codegen/tests.rs`
   is also disconnected, and old optimizer snapshots remain. These are not
   alternative backends, but their presence makes searches misleading. Inventory
   source fixtures against current lowering/execution tests, port useful cases,
   then delete obsolete source and snapshots together. Do not reconnect removed
   APIs merely to keep the old tests alive.
2. **Clarify remaining historical notes.** Integration is authoritative. The
   earlier design and placement logs contain superseded commands and scheduling
   proposals. Preserve decision history, but label historical sections and keep
   runnable instructions current rather than treating old test counts as gates.
3. **Measure construction cost and stack depth.** The write-set prepass can
   collect the same locals at multiple nesting levels. `add_row` searches open
   joins. `close_header` repeatedly simplifies columns, and `resolve` follows
   replacement chains without compression. Dominator construction iterates and
   queries climb parent chains. Most analysis/emission walks use explicit stacks,
   but graph construction's `expr` and MIR linearization are recursive. Benchmark
   deep expressions,
   nested constructs, wide joins and long replacement chains before choosing
   new indexes, algorithms or stack conversion. There is no linear-time claim.
4. **Review construction-only storage lifetime.** `interned_nodes` and the node
   hasher live in the graph through placement/emission although interning is used
   during construction. Consider releasing the lookup after construction or
   moving it into the builder if peak-memory measurements justify the added
   API split. The graph's actual node/region/join tables remain necessary.
5. **Consider splitting emitter preparation into named operations.** `emit`
   currently allocates value locals, indexes effect outputs, assigns labels,
   buckets computations and builds region bodies in one function. Small private
   methods could improve readability without adding passes or generic table
   abstractions. Keep scratch cursors short-lived and dependency order explicit.

The dense optional columns are deliberate: absent placement means unused value;
absent region label means an unlabeled arm; absent region body means not yet
emitted. They should not be replaced wholesale merely to remove `Option`.
Likewise, the accepted reachability boolean columns and stable MIR IDs need no
representation change in this cleanup.

No new aliasing assumptions, memory optimizations, local coalescing, peepholes or
fixed-point scheduling are introduced by this review.

## Validation

The compiler library suite passed: 1,411 tests, 2 ignored. After the final switch
arithmetic cleanup, all 8 codegen checks passed again. Release checks passed for
`wx-compiler` and `wx-cli`; formatting and whitespace checks passed. Whole-workspace
validation remains blocked by the frontend migration gaps noted above.
