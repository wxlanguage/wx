# MIR pipeline

Status as of 2026-11-07, branch `tir-refactor`, commit `5878b44`: step 1
of "Order of work" is done (scalar locals and signatures, `Values`,
`SetLocals`, per-scalar loads and stores), and so is step 2.1 (MIR's
vocabulary: Wasm types, flat opcodes, one signature table); next is 2.2,
the codegen walk ("Resuming at step 2.2", under "Order of work"); steps
3–4 are design. "Today" below describes the code before step 1. Replaces
`notes/mir-dce.md`, whose pass is the "Dead-code elimination" section
below, corrected against the code.

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
  one argument), a `Return`, an enclosing block's result, a `Drop`, or a
  `SetLocals`.
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

## MIR's vocabulary: Wasm's types, operations that say what they do

After step 1, MIR still types its values with source types (`U8`, `I16`,
`Bool`, `Pointer { kind }`) and leaves the instruction to them: a
`Binary { Div }` of type `U32` is `i32.div_u`. `opt` does not: its nodes
are instructions (`DivU`, `LtS`, `ShrU`) over Wasm's four types. So every
stage after lowering picks instructions from source types again: the `opt`
builder today, the codegen walk next, and `opt` writing MIR back would have
to make the types up again.

Step 2 moves MIR to `opt`'s level instead. Lowering, which has the TIR
types, decides everything a source type means, once.

### Types are Wasm's

A value is `I32`, `I64`, `F32`, `F64` or a reference (`funcref`, a
function reference by signature), plus `Unit`, `Never` and the
multi-result types. `U8`, `U16`, `I8`, `I16`, `U32`/`U64` as distinct
types, `Bool` and `Pointer` go:

- **Signedness is the operation's**, not the value's (below). A value used
  signed and unsigned is one value, with no cast between them.
- **A load's or a store's width and extension is the access's**
  (`LoadAccess`, `StoreAccess`, below), where today `opt`'s
  `MemAccess::from_mir` reads it off the type.
- **A narrow value is an `I32` with its masking written out.** Lowering
  already writes it (`canonical_narrow`: an `and` mask, or a shift pair,
  after each narrow operation); the type only repeated it.
- **An address is an `I32` or an `I64`.** Every access names its memory
  already.
- **One table of signatures, Wasm's function types.** An entry is a run
  of scalars in one column, its parameters then its results, with its
  parameter count; the table is interned by content. A function's type is
  one, and a multi-result type (`ValueType::Aggregate`) is one with no
  parameters, as a Wasm block yielding several values is typed by a
  function type `[] -> [t*]`. So equal scalars are one type, and a
  function's results are its scalars rather than a reference into another
  table. It replaces the aggregate table and the old signature list, whose
  results could be an aggregate. A function
  returning a pair repeats the pair's scalars in its own entry, as Wasm's
  type section does.
- **No function reference type yet** (open point 3).
- **`Transmute` goes.** Its two sides have the same scalars, which are now
  one MIR type, so lowering returns the operand (Closed, below).

**Facts come from operations, never from types.** A source type is no
guarantee about the bits in wx: std's narrow operators run the `i32`
instruction and `transmute` the result back, so `200 + 100` on `u8` is 300
under a `u8` type, and `transmute` makes any `i32`-represented value a
`u8`, a `Bool` (holding 5) or an open enum's value. "A `u8` is below 256"
would be an unsound rewrite. What an operation produces is always true:
`i32.load8_u` and `x & 0xff` are below 256, a comparison is 0 or 1. That
is what an optimizer reads (LLVM's known-bits analysis does), and if wx
later makes narrow types hold (overflow checks that trap, or masks),
lowering writes those checks as operations and the facts come from them.

### Opcodes are flat; nodes are grouped by shape

Two choices that are easy to conflate:

- **The opcode** (what an operation does) is one flat list, where every
  distinction is its own opcode: `DivS` and `DivU`, `LtS` and `LtU`,
  `ShrS` and `ShrU`; integer and float operations apart, as Wasm keeps
  them (`f32.div` has no signedness and does not trap; `i32.div_s` has one
  and does).
- **The node** (how many operands, of what kind) is grouped by shape:
  `Unary`, `Binary`, `Compare`, `Convert`, loads, stores. One node shape is
  one operand walk, one deduplication key and one folding table.

What an opcode is (whether it traps, whether it is commutative, which
signedness it uses) is a property of the opcode, defined once next to it:

```rust
pub enum BinaryOp {
    Add, Sub, Mul, And, Or, Xor, Shl, ShrS, ShrU, // integers
    DivS, DivU, RemS, RemU,                       // integers; trap
    Div, Min, Max, Copysign,                      // floats
}

impl BinaryOp {
    /// Traps on some operands: a zero divisor, or `MIN / -1`.
    pub fn can_trap(self) -> bool {
        matches!(self, Self::DivS | Self::DivU | Self::RemS | Self::RemU)
    }
}
```

and likewise `CompareOp { Eq, Ne, LtS, LtU, LeS, LeU, GtS, GtU, GeS, GeU,
Lt, Le, Gt, Ge }` (the last four for floats), `UnaryOp { Eqz, Neg, Abs,
Sqrt, Floor, Ceil, Trunc, Nearest }` (`Eqz` for integers, the rest for
floats) and the conversions as opcodes of their own, from the operand's
type to the node's: `ExtendS`, `ExtendU`, `Wrap`, `TruncS` and `TruncU`
(which trap), `ConvertS`, `ConvertU`, `Promote`, `Demote`, `Reinterpret`.
A node whose opcode does not fit its type (`DivS` of an `F32`) is a
`verify` error.

Every opcode is one Wasm instruction. Wasm has no integer negation or
bitwise not, so lowering writes them as `0 - x` and `x ^ -1`. A load's
access says its width and extension (`LoadAccess`: `I8S`, `I8U`, `I16S`,
`I16U`, `I32`, `I64`, `F32`, `F64`) and a store's its width only
(`StoreAccess`: `I8`, `I16`, `I32`, `I64`, `F32`, `F64`): a store has no
signedness.

This is Cranelift's design (a flat `Opcode`, `InstructionData` grouped by
format, `can_trap()` and the like as properties) and LLVM's
(`BinaryOperator` covers `sdiv` and `udiv`; `mayTrap()` is a property).
Every optimizing IR of the kind (LLVM IR, CLIF, MLIR's `arith`) keeps
integers signless and puts signedness in the operation, for the reason
above; Binaryen, Wasm to Wasm, has only Wasm's four types, as here. Rust's
MIR and GCC's GIMPLE pick instructions by source type, as wx's MIR does
today; they sit before an optimizing IR, not in place of one.

What it costs: today `ControlNode::Trapping` holds a `TrappingOp`, a type
that holds only trapping operations. With one opcode list, "the builder
puts an operation in program order when it can trap" is a check where the
node is built (`debug_assert!(op.can_trap())`), not a type.

### What each stage does with it

- **Lowering** picks the opcode and the access from the TIR type: the one
  place that knows a value was a `u8`.
- **`opt`** uses MIR's opcode enums for its data nodes, so writing MIR back
  is one node to one node, and the builder copies instead of translating
  (`build_binary`, `build_cmp`, `build_conversion` stop choosing). It puts
  an operation that can trap in program order (today's `ControlNode::
  Trapping`), by `can_trap()`.
- **Codegen** maps an opcode and its type to one Wasm instruction, choosing
  nothing.

## `opt`: MIR → MIR

The builder reads scalar MIR, so its aggregate code goes: the `Aggregate`,
`AggregateGet` and `AggregateCallResult` nodes, the per-scalar merging,
the load and store splitting. Several values at a join are several phis,
as several scalars of one aggregate already are. Its data nodes take MIR's
opcodes and types (see "MIR's vocabulary"), so a MIR node and its `opt`
node say the same thing.

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

One walk over each body, children before their parent. An opcode and its
type are one Wasm instruction (`DivU` of an `I32` is `i32.div_u`), and an
access is its load or store; codegen chooses no instruction.

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
2. **Inlining thresholds.** Scalar MIR counts a struct-heavy callee as more
   nodes; the policy's numbers may need a look.
3. **Function references.** Not lowered yet (`Funcref`, `TypedFuncref` and
   `CallRef` are reported unsupported), so MIR has no type for one; step 2
   removes the old pipeline's `ValueType::Function`, which nothing
   produces. For an optimizer the choice does not matter: devirtualizing
   (`call_ref` of a `ref.func` to `call`) reads the value's producer, not
   its type, as Binaryen does, and LLVM's opaque pointers and Cranelift's
   integer callees put the signature on the call. What decides it is Wasm:
   - **Table indices and `call_indirect $t`** (MVP, Cranelift's model, the
     old pipeline's): the value is an `i32`, the signature is the call's
     and checked at run time.
   - **Typed references and `call_ref $t`** (the function-references
     extension, opt-in): the operand must be `(ref null $t)`, so every
     local and block holding one is declared with its type, and MIR's value
     carries it. A bare `funcref` would need codegen to infer local types or
     a `ref.cast` (GC) at each call.
   TIR gives `func(A) -> R` the representation `funcref`, so `transmute`
   between two function types checks today; under typed references that is
   a cast, not a no-op, and the representation would have to name the
   signature.

Closed:

- **Where a multi-result type's list is kept:** in today's aggregate
  table, without the memory layout: `ValueType::Aggregate` names a list of
  two or more scalars, the type of a `Values`, a call or a block. A value
  of one scalar is that scalar (`Char`, `Meters(u32)`), so the table holds
  no list of one, and a constant pattern on a struct decides by the TIR
  type, not the MIR one, that it compares by `PartialEq`. Renaming the
  variant is left for when `opt` stops using it (step 2).

- **`Transmute`.** It goes (step 2.1). `transmute` requires the same
  `StackValue::Repr`, the same scalars in the same order, so with Wasm
  types both sides are one list, and its only job, retyping a value so that
  its users pick another instruction, is the opcode's now. Lowering returns
  the operand. Two struct types with the same scalars are one MIR type
  because the signature table is interned ("Types are Wasm's").
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

1. **Scalar MIR with multi-result nodes** (done): `Values`, `SetLocals`
   and the `targets` column; lowering's struct locals and field reads
   (`LocalRun`, `read_locals`/`write_locals` in `tir/lower.rs`); per-scalar
   loads and stores at TIR's offsets (`places.rs`); flat parameters, which
   the inliner binds with a `SetLocals` per struct argument; `verify`
   rejects a local that is not one scalar. The `opt` builder takes
   `SetLocals` apart into bindings; its struct machinery for bindings
   (aggregate loop and join params) is unreachable now and goes with
   step 2, which removes its aggregate nodes.

   Where the data lives after step 1:
   - **Memory layout is TIR's** (`tir/layout.rs`), as runs into two
     columns shared by every layout (`field_offsets`, `scalars`: each
     scalar's `Primitive` and byte offset); a load or a store reads an
     offset in place (`Layouts::scalar_offset`). Its unread per-field
     scalar ranges are gone.
   - **The stack shape is lowering's** (`tir/lower/shapes.rs`), its only
     reader: each type's MIR type and a run of `field_scalars`, each
     field's range among the scalars. The scalars' types are MIR's
     aggregate table; nothing is stored twice. A debug check in
     `place_value` keeps the two flattenings in one order. `StackValue`
     keeps its own walk, since it judges abstract types.
   - Nothing is cached that a lookup already answers: a call counts its
     callee's parameters from the checked signature.

   Still allocating, deliberately: `memory_values` copies its rows (the
   evaluator expands arrays from them); MIR's aggregate table keeps a box
   per entry; lowering collects node ids in a `Vec` before `state.list`.
2. **`opt` outputs MIR; codegen gets the MIR → wasm walk**, in five
   steps, each leaving every test passing:
   1. **MIR's vocabulary** (done; "MIR's vocabulary" above): Wasm types;
      flat opcodes with their properties; accesses with their width;
      lowering picks all of it from TIR types. The `opt` builder copies
      opcodes instead of choosing them.

      Where it landed:
      - **The opcodes** are `mir/body.rs`'s `UnaryOp`, `BinaryOp`,
        `CompareOp`, `ConvertOp`, `LoadAccess` and `StoreAccess`, each with
        what `verify` reads (`operands()`, `converts`, `value_type`) and
        `can_trap()`, which the builder asserts where it puts an operation
        in program order. `verify` rejects an operation whose types its
        opcode does not take (`VerifyError::OpcodeType`); a diverging
        operand fits anything.
      - **The signature table** is `mir/signatures.rs` (`Signatures`,
        `MIR::signatures`, interned by a `HashTable` over its column, as
        `tir/layout.rs` interns its aggregates);
        the aggregate table, the old `FunctionSignature` list and the dead
        `SignatureInterner` are gone. It keeps Wasm's name for a
        signature's index, `SignatureIndex`, though an entry with no
        parameters also types a multi-result value.
        Codegen still interns its own type section from it, by use.
      - **Lowering** reads an operator's opcode off its operand's source
        type through TIR's `Primitive` (`scalar_primitive`: an enum is its
        repr's, so `Bool` is a `u8`), a load's or a store's access off the
        layout's scalar (`Layouts::scalar` gives the primitive with the
        offset), an integer pattern's bits the same way, and an intrinsic
        is one opcode. A constant is its bits: a `Bool` constant is no
        longer forced to 0 or 1.
      - **`opt`** keeps its own node kinds; the builder maps an opcode to
        one without reading a type (`MemAccess::load`/`store`).
      - Output is byte-identical to step 1's on every example.

      The cleanup after it: `wasm::flatten_type_to_scalars` (no caller
      left) and lowering's `scalar_types` wrapper are gone;
      `operators::Scalar` and `layout::Primitive`, the same ten primitives,
      are one `tir::types::Primitive` (`of`, `is_integer`, `is_signed`,
      `is_float`, `size`); a compound assignment on a narrow local now
      wraps to its width as `x = x op v` and a compound store do (it left
      300 in a `u8`; `a_narrow_compound_assignment_restores_its_width`);
      `verify`'s opcode check has a test. Left on purpose, for the steps
      that remove them: `opt`'s own `MemAccess` and `TrappingOp` (step
      2.3, when `opt` takes MIR's enums), its aggregate nodes, whose
      fields are still named `aggregate_index` though they hold a
      `SignatureIndex` (step 2.5), and the unreachable `CallIndirectSym`
      path (open point 3).
   2. **The codegen walk**, MIR → `wasm::Function`, tested without `opt`: a
      test-only switch in `backend::emit` skips `opt`, so every wasmtime
      suite (lowering's, `backend_tests.rs`, the inliner's) also runs
      lowering's MIR straight through the walk. `coalesce_locals`,
      `peephole_local_tee` and the debug local check run on its output
      unchanged. The old path stays the default.
   3. **`opt` writes MIR.** Emission builds a MIR body: a value inlined at
      its user is a child expression, a value in a local a `LocalSet`
      statement and a `LocalGet`; a phi is a `LocalSet` in each arm; a
      carried binding's update a `LocalSet` before its `Break`; an `opt`
      block maps back to a label, a synthetic one gets a fresh label.
      Placement and `should_spill` stay. Codegen becomes builder →
      scheduler (MIR) → walk, and the scheduler's wasm emission goes. The
      target is parity: the same tests, about the same example sizes.
   4. **Control-flow values on the stack**: the child-or-local rule for an
      `IfElse`/`Switch`/`BlockJoin`'s join values ("Child of its user, or a
      local"), and the debug test that `opt` on its own output changes
      nothing. This is where the output improves.
   5. **Cleanup:** the builder's struct-binding code, unreachable since
      step 1; a loop carries every local its body sets, even one dead at
      the loop head; the `br_table`-or-`if`-chain choice moves from the
      builder (`should_use_br_table`, `build_switch_as_if_chain`) to
      codegen, so a `match` stays a `Switch` through `opt`. Kept out of
      step 3 so that parity there compares like with like.
   **Resuming at step 2.2.** Codegen runs `opt` per function in
   `codegen::Builder::build` (`codegen/mod.rs`, the loop over
   `mir.functions_with_ids()`: `opt::builder::Builder::build`, then
   `opt::scheduler::Scheduler::schedule`, then `encode_scheduled`). The
   walk is a third choice there: a MIR body straight to a
   `wasm::Function`, each node one instruction now that opcodes say
   everything, then `wasm::coalesce_locals` and `wasm::peephole_local_tee`
   (`wasm/mod.rs`) and, in debug, `opt::local_dominance::
   verify_local_dominance`, as the scheduler does after itself
   (`opt/scheduler.rs`). `backend::emit` takes the test-only switch.
   Settle first: where the walk lives (`codegen/walk.rs`?), how a value
   with several results reaches its user (on the stack in order; a
   `SetLocals` pops them), and what the switch looks like; then run every
   wasmtime suite both ways.
3. **`mir::dce`**, taking `remove_dead_functions` from the inliner and the
   reachability walk from codegen.
4. **`backend::emit` runs the sequence**; every harness goes through it.

Steps 1 and 3 are independent of each other; step 2 is simplest after 1.
