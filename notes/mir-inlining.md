# MIR inlining

Status as of 2026-11-04, branch `tir-translation`: implemented in
`mir/inline.rs` (steps 1 to 5 of "Order of work"); the corpus and the
tuning are next. Replaced `mir/inlining.rs` (the tree inliner, deleted) and
the "Inlining" section of `notes/mir-arena.md`, whose arena shape this
builds on.

## What the old pass got right and wrong

`run_inlining_pass` inlines every `#[inline]` function, callees first (Kahn
over the `#[inline]` subgraph), then drops what the exports and the start
function cannot reach.

Kept:

- **Callees first.** A body is flattened once, before it is copied, and a
  callee is never walked again after its splice.
- **A callee's locals are appended to the caller's.** A scope per call let
  two inlined calls at one site clobber each other's locals.
- **A cycle stays a call.** A function inside a cycle of inline functions
  is an ordinary call target.
- **Reachability from the exports and the start function** decides which
  functions are emitted.

Dropped:

1. **Nondeterminism.** The cycle breaker takes its anchor from
   `HashMap::iter().find(..)`, and levels come from `HashSet`s, so the same
   program can be inlined differently on two runs.
2. **Hash-keyed, incrementally edited call graph.** `callees`, `callers`,
   `func_idx` and the in-degree map are `HashMap<DefId, HashSet<DefId>>`,
   rewritten after every splice. With a dense `FunctionId` (its index) none
   of this is needed.
3. **Double copying.** Each target is cloned per level, then its tree is
   cloned again per call site, and each caller costs one recursive walk.
4. **Scope workarounds.** The callee's root scope is redirected onto the
   call site's, which `opt::Builder::build_block_expr` tolerates as
   aliasing; a whole level is inlined in one walk only so a later walk does
   not mistake a wrapper block for a caller scope. Fresh labels remove both.
5. **Hand-kept side tables.** `call_edges` and `static_data` are updated by
   hand (and a level's static data was once unioned into every caller).
   Both are now derived from the nodes.
6. **Two 75-arm walkers** (`Rebaser`, `inline_expr`). The arena has one
   child visitor, `ExprKind::ids_mut`.
7. **No policy.** Every call of an `#[inline]` function is inlined however
   large it is, and no other call is, however small the callee.
8. **`retain` breaks `FunctionId == index`**, which MIR now relies on.

## Shape

One pass, `mir::inline::run(mir: &mut MIR, policy: Policy)`, in four steps.
`tir::build` returns MIR as lowered, so lowering's tests see lowering's
output; whoever builds the module runs the pass before codegen (today the
wasmtime harness of `tir/lower.rs`, so every program those tests run is
inlined).

1. Build the call graph and the per-function columns.
2. Order the functions callees first.
3. For each function in that order, decide and splice its calls.
4. Drop unreachable functions and compact the ids.

Everything it keeps is a column indexed by `FunctionId`, owned by the pass
and dropped at its end. None of it is stored in `MIR`.

```rust
struct CallGraph {
    /// `callees[starts[f]..starts[f + 1]]` are the functions `f` calls,
    /// once per call node, in node order (CSR).
    starts: Vec<u32>,
    callees: Vec<FunctionId>,
}

struct Columns {
    /// Weighted size of the body as it is now: after its own inlining once
    /// the function is processed.
    cost: Vec<u32>,
    /// Call nodes naming the function, over the whole program, as lowered.
    /// Not updated by splices: a call is decided before any copy of it
    /// exists, so the count is never stale where it is read.
    call_sites: Vec<u32>,
    /// The strongly connected component the function belongs to.
    scc: Vec<u32>,
    /// Whether the component is recursive: more than one function, or one
    /// that calls itself.
    recursive: Vec<bool>, // per component
    /// Whether something outside the call graph refers to the function: an
    /// export, the start function, later a `funcref`.
    rooted: Vec<bool>,
}
```

An imported function (`Origin::Imported`) is a node with no callees and no
code: it is never inlined, its cost is a call's, and step 4 drops an import
nothing calls any more.

`FunctionFlags::INLINE` keeps its meaning, the user's request. The
decision itself is computed per call and not stored: only this pass reads it.

### 1. Call graph and columns

One linear scan over every function's `kinds` collects its `Call` nodes
into `CallGraph`, counts `call_sites`, and sums `cost`. `rooted` comes from
`mir.exports` and `mir.start_function`.

### 2. Order: Tarjan's SCCs

Tarjan's algorithm over the dense ids, started in id order, emits the
components callees first, in an order that depends only on the program.
That order replaces Kahn's levels, the in-degree counts and the
graph edits. The cycle rule falls out: a call whose callee is in the
caller's own component, and that component is recursive, is never inlined.
No anchor is chosen.

Recursion goes through an explicit stack, not the Rust call stack: a deep
chain of calls must not overflow the compiler.

### 3. Deciding and splicing

For each function `caller` in that order (so every callee it can inline is
already final):

```text
let end = caller.body.len()        // only the original nodes
for id in 0..end:
    if let Call { function: callee, args } = caller.body.kind(id)
       and should_inline(caller, callee):
        splice(caller, id, callee, args)
cost[caller] = recompute(caller)
```

Scanning only `0..end` is enough. The appended nodes are a callee that was
already processed, so every call left in it is one the policy refused, and
the decision does not depend on the call site (see "Policy").

`splice(caller, call, callee, args)`:

1. Take the offsets: `e = caller.body.len()` (expressions), `l` (lists),
   `c` (cases), `v = caller.locals.len()` (locals), and
   `b = caller.label_count` (labels). The wrapper label is
   `w = b + callee.label_count`, and `caller.label_count` grows by
   `callee.label_count + 1`.
2. Append `callee.locals` to `caller.locals`. Parameters come first, so
   parameter `i` is local `v + i`.
3. Append the callee's `kinds`, `types`, `lists` and `cases`. Shift each
   appended kind through `ids_mut`: `Expr` by `e`, `List` and `Cases` by
   `l` and `c` (their `start`), `Local` by `v`, `Label` by `b`. A
   `Return { value }` becomes `Break { label: w, value }`.
4. Push one `LocalSet { local: v + i, value: args[i] }` per argument, with
   the argument nodes reused as they are, and the list
   `[LocalSet..., callee.root + e]`.
5. Overwrite the call node with `Block { label: w, statements }`. Its type
   stays the call's (the callee's result type).
6. Debug builds run `verify` on the caller afterwards.

`static_data` and `callees()` need nothing: they are read off the nodes.

Appending a callee into its caller costs the callee's size and nothing
else: no clones of a tree, no second walk. A `Block` whose label nothing
breaks to (a callee without an early `return`) is left as it is; opt builds
it as a join with one entry.

### 4. Dead functions and compaction

Moving to its own pass over every kind of item: `notes/mir-dce.md`. What
follows is how `mir/inline.rs` does it today, for functions only.

1. Rebuild the call graph over the inlined bodies (one more scan), and walk
   it from the rooted functions.
2. Build `remap: Vec<Option<FunctionId>>`, old id to new, in id order over
   the live functions.
3. Move the live functions and their `function_flags` to their new indices,
   and rewrite every `Call::function`, every `ExportItem::Function` and
   `start_function` through `remap`.

That keeps `FunctionId == index` and the flags column aligned. Imports join
the same table when they are lowered (`notes/mir-arena.md`, decision 10),
so the same walk drops an unused import.

## Policy

```text
should_inline(caller, callee) =
       not (same component and recursive[scc[callee]])
   and (   INLINE in flags(callee)
        or cost[callee] <= call_cost(callee) + SLACK
        or (call_sites[callee] == 1 and not rooted[callee]))
```

- **`#[inline]` always inlines**, except in a recursive component. Rust's
  `#[inline]` mostly makes a body available to other crates and is only
  secondarily a hint. wx always compiles the whole program, so "always" is
  the meaning left. `#[inline(never)]` is the later opt-out.
- **A small callee is inlined.** Its weighted cost is at most what calling
  it costs, so the program does not grow. Arguments are evaluated either
  way, and the parameters' `LocalSet`s cost nothing once opt turns locals
  into SSA values, so the comparison is the body against the call itself.
  `SLACK` is `Policy::slack`, 4 to start with, to tune (see "Measuring").
  `Policy::ATTRIBUTE_ONLY` turns both automatic rules off.
- **A function with one call site is inlined** unless something outside
  the call graph refers to it. The copy replaces the only use, and the
  original is dropped in step 4, which saves its function entry, type and
  local declarations.

The decision depends only on the callee and the caller's component. A call
with constant arguments gains more, because opt can fold the body, but that
is per call site and left for later.

### Cost

`ExprKind::cost(&self) -> u32` is one match in `mir/body.rs`, next to
`ids_mut`, so a new variant gets a cost where it gets its children.
The weights estimate encoded bytes, since code size is what a Wasm program
pays for:

| Node | Cost |
| ---- | ---- |
| `Sequence`, `Transmute`, `Noop` | 0 |
| `Aggregate` (its values are its children) | 0 |
| `Block`, `Loop`, `IfElse` | 2 (the opcode and `end`), 3 for an `if` with an `else` |
| `LocalGet`, `LocalSet`, `Global`, `GlobalSet`, `Int` | 2 |
| `AggregateGet`, `AggregateSet` | 2 per slot |
| `Float` | 5 (the node does not say `f32` or `f64`) |
| `Unary`, `Binary`, `Compare`, `Convert`, `Reinterpret`, `Drop` | 1 |
| `Break`, `Continue` | 2 |
| `Return`, `Unreachable` | 1 |
| `Switch` | 2 + one per case |
| `Call` | 2 (the opcode and the index) |
| `MemoryOffset`, `MemoryIndex`, `MemorySize`, `MemoryGrow`, `StaticPointer` | 2 |
| `MemoryFill`, `MemoryCopy`, `PointerLoad`, `PointerStore` | 3 (an opcode and a `memarg`) |

`call_cost(callee)` is the `Call` weight. An aggregate value spans several
Wasm values, so a `LocalGet` of one can weigh its scalar count; to settle
once the corpus shows whether it matters.

The cost of a function is taken **after its own inlining**, which
callees-first order gives. That is what keeps the automatic rules from
growing the program: a function that absorbed ten copies of a callee has
the cost of ten copies, so it is no longer small. Only `#[inline]` can
copy a body into many callers regardless of size, as it does today.

A plain node count (`kinds.len()`) would be the wrong measure. std's `u8`
`add` is `transmute(i32_add(transmute(self), transmute(rhs)))`: five nodes,
but one instruction and two `local.get`s.

### Prior art

- **rustc's MIR inliner** weighs statements and terminators, adds a penalty
  for calls, and uses a higher threshold for an `#[inline]` callee. The
  real decisions are LLVM's.
- **LLVM** computes cost after simplifying the callee for the call site,
  gives a large bonus to the last call of a function with internal linkage
  (the single-caller rule) and bonuses for constant arguments.
- **Engines.** As far as I know, V8 inlines small direct Wasm calls itself.
  If so, the gain from inlining in wx is code size and what opt folds
  across the boundary, not call overhead, which is why the cost is in bytes.

## Measuring

1. **MIR tests** in `mir/inline.rs` (done):
   - a small function without `#[inline]` is inlined, and one over the
     threshold is not;
   - a function with one call site is inlined and removed, and an exported
     one is inlined but kept;
   - direct and mutual recursion stay calls, and an `#[inline]` function in
     a cycle is not expanded;
   - the output is the same across runs (the old pass fails this);
   - a chain of `#[inline]` calls gives the node count it should, and an
     unattributed chain stops growing;
   - `FunctionId == index` after compaction, with calls, exports and flags
     remapped;
   - each lowering test still runs under wasmtime with the same result.
2. **A corpus.** A script builds a few programs with the policy off,
   `#[inline]` only, and automatic at two or three `SLACK` values, and
   records the `.wasm` size and the run time under wasmtime. That tunes the
   weights, and it is the thesis's evidence for the policy. CI does not build
   `examples/`, so this is a script, not a test.
3. **A debug statistic.** Per function: call sites inlined and nodes before
   and after. Cheap, and it shows a weight that is badly off.

## Order of work

1. `cost` in `mir/body.rs`, with tests.
2. The pass skeleton: `CallGraph`, the columns, and Tarjan's order.
3. `splice`, with `#[inline]` as the only rule. This replaces the old pass;
   delete `mir/inlining.rs`. Wire it into `tir::build` between lowering and
   codegen.
4. Dead functions and compaction.
5. The two automatic rules.
6. The corpus and tuning `SLACK` and the weights.
7. Later: `#[inline(never)]`, a constant-argument bonus per call site, and
   `funcref` (a referenced function is rooted, and a `CallRef` is never
   inlined).
