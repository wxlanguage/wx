# MIR pipeline

Status as of 2026-11-07, branch `tir-refactor`: design, nothing
implemented. Replaces `notes/mir-dce.md`, whose pass is the "Dead-code
elimination" section below, corrected against the code.

## Today

```
lower → inline → codegen
                   └─ per function: MIR → opt::builder (sea of nodes)
                                        → opt::scheduler → wasm::Function → bytes
```

`backend::emit` runs it; `emit(.., None)` skips inlining.

What this shape costs:

1. **`opt` is not a pass.** It runs inside codegen and outputs wasm
   instructions, so nothing after it sees what it did: the inliner sizes
   callees before they are optimized, and nothing can remove an item whose
   last use `opt` deleted.
2. **Dead items have no general cleanup.** The inliner drops dead functions
   (`remove_dead_functions`) and their import entries; codegen skips static
   data nothing live points at (`lay_out_static_data`, its own reachability
   walk); globals and memories are never dropped. A memory named only by a
   pointer type is emitted (`func run(x: heap::&u32) -> heap::&u32 { .. }`
   gives `(memory 0)` with no instruction touching it).
3. **Aggregates are built, then taken apart by every later stage.** Lowering
   creates `Aggregate`/`AggregateGet`/`AggregateSet` and aggregate-typed
   loads, stores, parameters, results and blocks. The `opt` builder splits
   them again: one node per scalar, a merge per scalar at every join
   (`merge_switch_slot`, `merge_values`, `create_join_params`), a struct
   load or store as one access per scalar (`build_aggregate_load`,
   `emit_aggregate_store`, the only readers of `AggregateMemory::offsets`
   outside tests). The scheduler keeps each in one local per scalar
   (`ensure_aggregate_locals`). Codegen flattens them in signatures.
4. **A value made by control flow always goes through a local.** In `opt` an
   `if`, `match` or block is a statement (`ControlNode`) and its value a
   phi read later, so the scheduler sets a local in each arm
   (`pre_alloc_join_outputs`, `emit_phi_stores_for_branch`). Without phis it
   gives the `if` a stack type, then stores the result into a local right
   after `end` (`capture_branch_result`). `(if c > 0 { a } else { b }) + 3`
   compiles to

   ```wat
   if
     local.get 1
     local.set 3
   else
     local.get 2
     local.set 3
   end
   local.get 3
   i32.const 3
   i32.add
   ```

   where `if (result i32) local.get 1 else local.get 2 end i32.const 3
   i32.add` needs no local. A variable assigned in both arms is the same.

## Target

```
lower → inline → opt → dce → codegen
MIR      MIR→MIR  MIR→MIR  MIR→MIR  MIR→wasm→bytes
```

Each pass runs once, in this order, and takes and returns the same MIR.
Nothing repeats (see "Later").

- `opt` is a MIR → MIR pass: MIR → sea of nodes → MIR, per function.
- `dce` runs after `opt`, so it sees what `opt` deleted.
- Codegen turns MIR into wasm by one walk and encodes it; it decides no
  optimization.
- `backend::emit` runs the whole sequence, including `dce` when inlining is
  off: lowering alone already leaves dead items.

## What MIR represents

MIR is a monomorphic program as trees of expressions over Wasm values, and
the module's items. **It expresses what the Wasm stack can do**; what the
stack cannot do goes through a local.

- **Every value is a scalar.** A struct local is one local per scalar; a
  struct passed as an argument is its scalars, each an argument; a struct
  load or store is one `PointerLoad`/`PointerStore` per scalar at its
  layout offset, written by lowering, which has the layout. A signature is
  a flat list of parameters and of results.
- **A node may have several results**: a `Values`, a `Call`, a `Block`/
  `IfElse`/`Switch`, a `Break`'s value. They are taken whole and in order,
  as Wasm takes them off the stack: by a call's arguments (each result is
  one argument), a `Return`, an enclosing block's result, a `Transmute`, a
  `Drop`, or a `SetLocals`.
- **What the stack cannot do is a local:** taking one value out of several,
  or reading a value twice. No node takes one result out of several.

Removed: `ValueType::Aggregate`, `AggregateMemory`, and the `AggregateGet`
and `AggregateSet` nodes. A multi-result node's type is the list of its
scalars (where that list is kept: open point 2).

New:

```rust
/// Several values as one: each pushed in order. Its type is their types,
/// in order. Today's `Aggregate { values }`.
Values { values: ExprList },
/// Pop `value`'s results into `targets`, one per result, in order;
/// `None` drops that result.
SetLocals { targets: TargetList, value: ExprId },
```

and `Return` takes a list. `TargetList` is a run of a new body column,
`Body::targets: Vec<Option<LocalIndex>>`, as `ExprList` is of `lists` and
`CaseList` of `cases`; `ids_mut` hands it out as `Id::Targets`, so a pass
that renumbers locals rewrites its entries as it does every other local.
`verify` checks that a `SetLocals` has one target per result and that each
target local's type is its result's. The single `LocalSet { local, value }`
stays for one value.

A list rather than a run of consecutive locals (`SetLocals { first,
value }`): a run would hold only while every pass that renumbers locals
keeps runs whole, a rule nothing states locally, and would leave a result
nobody reads in a local nobody reads. The list costs one column and states
every target, a drop included.

So reading one field of a multi-result expression is two nodes. The middle
of `f() -> (i32, i64, f64)`:

```
Sequence [
    SetLocals { targets: [None, Some(t), None], value: Call f },
    LocalGet t,
]
```

which codegen emits as `call $f drop local.set $t drop local.get $t`. A
block, an `if` or a `match` with several results is read the same way, and
`local (_, b, _) = f()` is the `SetLocals` alone.

Lowering keeps one `ExprId` per expression (`Result<mir::ExprId, ()>`):
a struct-valued expression is one node, a `Values`, a call or a block.

- A struct local is one local per scalar. Writing it is a `SetLocals`;
  reading it is a `Values` of `LocalGet`s; a field of it is the `LocalGet`
  or `LocalSet` of its locals (today's `AggregateGet`/`AggregateSet` by
  range).
- A field of a struct that is in no local (`make(a)`'s) is read by storing
  the struct with a `SetLocals` first.

Lowering always writes it this way and `opt` decides what is left: in the
sea of nodes a local is a name for a value, so results nobody reads become
drops, a struct built in the same function is never pushed whole, and a
local is kept only where the stack cannot hold the value.

The alternative, keeping aggregates as lowering's output and scalarizing in
a first MIR pass, leaves two forms of MIR every pass has to tell apart.
Rejected.

## `opt`: MIR → MIR

The builder reads scalar MIR, so its aggregate code goes: the `Aggregate`,
`AggregateGet` and `AggregateCallResult` nodes, the per-scalar merging,
the load and store splitting. Several values at a join are several phis,
as several scalars of one aggregate already are.

The scheduler's emission (`emit_control`, `emit_value_inline`, about 1,000
lines) builds a MIR body instead of wasm instructions:

- Placement is unchanged (`compute_value_placement`,
  `record_block_own_nodes`, `lca_block`).
- Branches name labels, not depths (`break_depth` goes).
- A `match` stays a `Switch`; choosing `br_table` or a `br_if` chain
  (`emit_switch_br_table`) moves to codegen.
- Dead pointer-load elimination stays.

### Child of its user, or a local

Every value is placed one of two ways:

- **as the child of its user**, which in Wasm keeps it on the stack, when
  it has exactly one use and placing it there moves it past nothing with a
  side effect: its user is in the next statement (or is the block's tail),
  and what that statement evaluates before it is pure;
- **in a local** otherwise.

`should_spill` makes this decision for ordinary values today. It now also
applies to the values of control flow: when an `IfElse`/`Switch`/
`BlockJoin`'s join values are placed as a child, the construct itself
becomes that child, with each arm ending in its value. Several join values
become one multi-result construct when one user takes all of them, in
order; otherwise they are locals, as now. These are the rules LLVM's wasm
backend uses to remove locals (`WebAssemblyRegStackify`); Binaryen's
`SimplifyLocals` does the `if` case as a rewrite (an `if` whose arms each
set the same local becomes `local.set $x (if (result ..) ..)`).

Values carried around a loop stay in locals. Multi-value lets a loop take
parameters, but it is awkward to produce and engines gain nothing.

With these rules `func make(a: i32) -> P { P(a, a + 1) }` is `local.get 0
local.get 0 i32.const 1 i32.add` (today four locals' worth of sets and
gets), and `local P(x, y) = make(a); x + y` is `local.get 0 call 0
i32.add`, since `x` and `y` are each read once, in the order the call
returns them.

`opt` on its own output changes nothing; a debug test checks it, since a
round trip that adds locals would make code worse each time it runs.

## Dead-code elimination: `mir::dce::run(mir: &mut MIR)`

Mark and sweep over every kind of item, each knowing nothing of the
other's details. `remove_dead_functions` moves here and generalizes; the
inliner keeps its `rooted` column (the one-call-site rule reads it) and
removes nothing. Roots are one function both use.

What leaves items dead: lowering naming one through a type only (the memory
above), and code `opt` deletes. Inlining does not: a spliced callee's nodes
are copied into its callers, so whatever it named is still named. Lazy
lowering stays; it saves lowering work, but `dce` is what keeps the output
free of dead items.

### The graph

`Item` stays what an import or an export names (`Function`, `Global`,
`Memory`). Static data is never imported or exported, so the graph has its
own node type rather than an `Item::Data` that `Import::item` and
`Export::item` could hold:

```rust
pub enum Node {
    Item(Item),
    Data(StaticEntryId),
}

impl MIR {
    /// Every node `node` refers to.
    pub fn dependencies(&self, node: Node, f: impl FnMut(Node));
}
```

| Node | Depends on |
| ---- | ---------- |
| defined function | what its code's nodes name |
| imported function | nothing |
| global | data (`ConstInit::Static`), a memory (`ConstInit::DataEnd`) |
| static data | its memory; its relocations' targets: data (`AddressTarget::Entry`), memories (`AddressTarget::DataEnd`) |
| memory | nothing |

Which items a node names is one match in `mir/body.rs`, beside `ids_mut`
and `cost`:

```rust
pub enum ItemRef<'a> {
    Function(&'a mut FunctionId),
    Global(&'a mut GlobalId),
    Memory(&'a mut MemoryId),
    Data(&'a mut StaticEntryId),
}

impl ExprKind {
    pub fn items_mut(&mut self, f: impl FnMut(ItemRef<'_>));
}
```

`Call` names a function; `Global` and `GlobalSet` a global; `DataEnd`,
`MemoryIndex`, `MemorySize`, `MemoryGrow`, `MemoryFill`, `PointerLoad`,
`PointerStore` their memory, `MemoryCopy` two; `StaticPointer` its data. A
new variant that names an item says so in this one arm. `ids_mut` stays the
walk over indices inside one body; item ids are module-level and only
module-level passes read them. Marking calls `items_mut` on a copy
(`ExprKind` is `Copy`), so the list is written once.

### Mark

Roots: exports of every kind and `start_function`. A work list of `Node`
walks `dependencies` from them, with one `live` column per kind. A dead
function is never marked, so nothing it names is marked through it. This is
reachability, so cycles (data pointing at data) need nothing special.

### Sweep

For each kind, the live items get new ids in id order (`Vec<Option<_>>`,
old to new), and so do the import entries of live items. Then every stored
id is rewritten:

- every node, through `items_mut`;
- `exports`, `imports` (each entry's item), and `Origin::Imported` of each
  imported item;
- `start_function`;
- each global's `ConstInit::Static { entry }` and `ConstInit::DataEnd
  { memory }`;
- each static entry's `memory` and its relocations' targets.

Each table keeps only its live entries, at their new positions. Every table
is indexed by its own id, so `Global` and `MemoryInfo` drop their `id`
fields, as `Function` did. Debug builds run `verify_imports` afterwards.

Codegen then lays out every entry in `static_entries` and drops its own
walk.

### Decisions

1. **An unused import entry is dropped**, for every kind. Only an embedder
   filling imports by position notices; accepted already for functions
   (`notes/mir-arena.md`, decision 14).
2. **An unused defined memory is dropped**, unless exported.
3. **Static data is a node of the graph, not an `Item`**: it depends on its
   memory and its relocations' targets.

### Tests (`mir/dce.rs`)

- A memory named only by a pointer type is dropped.
- An imported global or function nothing live names loses its import
  entry; `verify_imports` holds afterwards.
- An exported item is kept with nothing naming it.
- A data entry and its memory go with the only function pointing at it,
  and stay while one live function, a global or another live entry does.
- After the sweep, every id a node, an export, an import entry, the start
  function, a global's initializer or a static entry holds is in range, and
  each table's index is its id.
- Every lowering test still runs under wasmtime with the same result.

## Codegen: MIR → wasm

One walk over each body, children before their parent:

- a label becomes a branch depth;
- a `Switch` becomes a `br_table` (dense cases) or a `br_if` chain;
- a block's type is its node's: none, one scalar, or several (a type-section
  entry; the signature table is already shared with multi-value block
  types, `codegen/mod.rs:330`);
- a `Call` leaves its results on the stack for its user; a `SetLocals`
  takes its targets in reverse, a `local.set` or a `drop` each.

Then the existing encoder (`encode_scheduled_instr`) runs unchanged;
`wasm::Function` stays the boundary. Reusing locals (`opt/liveness.rs`) is
an optional last step here: it only makes the binary smaller.

**Extensions are decided here only.** When multi-value is not allowed, a
multi-result block is lowered to locals mechanically: each arm sets them,
and they are read after `end`. MIR and `opt` never know which extensions
are on.

### Why locals are a size concern

Optimizing engines (V8's TurboFan, wasmtime's Cranelift, SpiderMonkey's
Ion) turn locals into SSA values and allocate registers themselves, so how
many locals a function uses, and in what order, does not change peak
speed. A `local.set`/`local.get` pair still costs bytes, and a little time
in baseline compilers (V8's Liftoff, wasmtime's Winch), which compile
without that analysis. So keeping values on the stack is worth doing, and
it belongs in the last steps, not in the optimizer's reasoning.

## Open points

1. **Multi-value is already emitted without an opt-in.** A function
   returning a struct or a slice gets `(result i32 i32)`, against the rule
   that output uses no extension unless the program uses it. Not part of
   this refactor; the direction is "Multi-value as an opt-in" below.
2. **Where a multi-result type's list is kept:** today's aggregate table
   without `memory`, or a `Results` table of its own. Minor: it is the list
   of a `Values`' types either way.
3. **Inlining thresholds.** Scalar MIR counts a struct-heavy callee as more
   nodes; the policy's numbers may need a look.

Closed:

- **`Transmute` between struct types.** It takes a multi-result value whole
  and gives the same values under the target's types (`U32` and `I32` stay
  apart, since a node's type picks its instruction), as it does today. A
  struct of one scalar (`Char`, `Meters(u32)`) is that scalar, so the `opt`
  builder's one-slot case (`opt/builder.rs:376`) goes, and so does the
  `Transmute` around a global's read or write
  (`tir/lower/intrinsics.rs:320`) wherever the two types are now equal.
- **A struct value as one node.** It stays one (`Values`, a call, a
  block); only reading one field needs it in locals.

## Later

Not part of this refactor:

- Interleaving inlining and `opt` per strongly connected component, callees
  first, so the inliner splices optimized callees (LLVM's CGSCC pipeline;
  the inliner already walks Tarjan's components callees first).
- Rewriting inside `opt` until nothing applies (constant folding, branches
  on constants, dead nodes); `dce` then drops what that orphans.
- Repeating the pipeline, with each pass reporting a change and a fixed cap.
- Multi-value as an opt-in (next section).

## Multi-value as an opt-in (future)

Direction, not planned for the near term.

Every extension should be adopted when the runtime supports it. Multi-value
is not, today: a function returning more than one Wasm value gets a
multi-value result whether or not the runtime supports it, and nothing says
whether it may. The other extensions codegen emits (several memories,
`Size = u64`, `memory_fill`/`memory_copy`) appear only when the program
asks for them; multi-value appears from returning a struct or a slice (an
address and a length), which does not read as asking for an extension.

**First: configuration.** The planned `extensions` list in `wx.json`, so
whether multi-value is allowed is a fact the compiler reads. Worth deciding
alongside: a list per extension, or a Wasm version as the baseline
(`"target": "wasm2"`, which has multi-value and bulk memory) plus extras.

**Where multi-value is needed.** Blocks with several results are lowered to
locals by codegen when it is off (see "Codegen"), and several parameters
are allowed without it. Only a function's results need it.

**Options considered for function results without it:**

- *Return through linear memory* (an out-pointer into a stack in memory, as
  C and Rust do): a hidden allocation, and a choice of memory where wx has
  no default. Rejected.
- *Return through globals* (the callee keeps its first result on the stack
  and sets the rest in compiler-made globals, one per scalar type and
  position; the caller reads them right after the call, as Emscripten's
  `tempRet0` did for `i64`): allocates nothing and is safe, but it is a
  calling convention the program does not write. Not chosen.
- *Forbid it.* Chosen, but only where a function with several results
  would otherwise have to exist in the output.

**The rule.** Without multi-value, a function whose result is more than one
Wasm value:

1. is not exported or imported (the host's calling convention);
2. is `#[inline]`, and `#[inline]` is a guarantee: inlined at every call,
   at every optimization level (the inliner always runs for `#[inline]`
   callees; turning optimization off turns off only its own choices);
3. is not recursive (a call inside its own strongly connected component
   cannot be inlined);
4. never becomes a `func(A) -> R` reference (a function type with several
   results needs multi-value itself); a value of its own item type is a
   direct call and is fine.

Each is a fact about the program, never about what the optimizer did, so a
program does not compile at one level and fail at another. Zig's `inline
fn` is the same kind of guarantee.

Where each is checked: 1, 4 and a non-generic 2 by the type checker, from
the signature; a generic 2 per instance by lowering, since `func id<T:
StackValue>(x: T) -> T` returns one value for `u32` and two for
`heap::&[u8]`; 3 by lowering, on the instances. Lowering already reports
diagnostics (E2114). The stricter alternative for generics, a bound
requiring one value, is too restrictive.

A large function returning a struct then has two explicit choices: enable
multi-value, or return through a pointer it is given.

**std** compiles under the rule once `Array::as_slice` and `as_slice_mut`
(`std/main.wx:265`) are `#[inline]`; `slice_from_parts` and
`slice_from_parts_mut` are already, and `Slice::len`/`as_ref` are expanded
by lowering.

**Open:** whether `#[inline]` on any recursive function becomes an error
(consistent), or only on one with several results (today a recursive
`#[inline]` callee quietly stays a call, `notes/mir-inlining.md`).

## Order of work

1. **Scalar MIR with multi-result nodes:** `Values`, `SetLocals` and the
   `targets` column; lowering's struct locals and field reads; the `opt`
   builder; `backend_tests.rs` (which builds aggregates by hand). The
   wasmtime tests check the results do not change.
2. **`opt` outputs MIR; codegen gets the MIR → wasm walk**, with the
   child-or-local rules for control-flow values.
3. **`mir::dce`**, taking `remove_dead_functions` from the inliner and the
   reachability walk from codegen.
4. **`backend::emit` runs the sequence**; every harness goes through it.

Steps 1 and 3 are independent of each other; step 2 is simplest after 1.
