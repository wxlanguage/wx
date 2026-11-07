# MIR as an arena

Status as of 2026-11-04, branch `tir-translation`. Implemented (steps 1–5
below). Supersedes the tree-shaped `mir::Expression` and
`notes/inlining-pass-memory-plan.md` (written for the old `DefId`-keyed tree
inliner in `mir/inlining.rs`, which is not compiled).

## Why

MIR is built by one producer (`tir/lower.rs` and `tir/lower/*`) and read by
one consumer (`opt/builder.rs`), plus the hand-built fixtures in
`backend_tests.rs`. The tree form (`Box<Expression>` children) has cost us in
four ways:

- **Variant count.** `ExprKind` has about 75 variants, about 50 of them one-
  or two-operand operators that opt already treats as groups
  (`build_binary` matches `E::Add | E::Sub | …`). Every walker repeats the
  list (`collect_break_targets`, the pass-through lists, the old `Rebaser`
  and `inline_expr`), which is what adding `Transmute` cost. `And`/`Or`
  duplicate `BitAnd`/`BitOr`.
- **Side tables that duplicate the tree.** `MIR::call_edges` (lowering pushes
  an edge per call it builds), `MIR::inline_functions`, and
  `Function::static_data` (which the inliner had to union by hand) are all
  derivable from the nodes.
- **Scopes with dead data.** `BlockScope { kind, result }` is only ever read
  as `scopes.len()`. Lowering makes a synthetic scope just to sequence
  statements (`sequence`, `push_synthetic_scope`), so opt needs a
  `collect_break_targets` pre-walk to find the blocks something really breaks
  to.
- **Inlining.** A tree inliner deep-clones the callee and walks it per call
  site, and redirecting the callee's root scope onto the call site's aliased
  scope indices, which `opt::Builder::build_block_expr` works around.

## Shape

```rust
index_newtype!(ExprId);
index_newtype!(LabelId); // what `Break`/`Continue` name; replaces ScopeIndex

pub struct MIR {
    pub functions: Vec<Function>,          // indexed by FunctionId
    pub function_flags: Vec<FunctionFlags>, // one byte per function, same index
    pub imports: Vec<Import>,              // indexed by ImportIdx
    pub exports: Vec<Export>,
    // signatures, globals, memories, aggregates, static_entries,
    // start_function; no call_edges, no inline_functions
}

/// What an import or an export names.
pub enum Item { Function(FunctionId), Global(GlobalId), Memory(MemoryId) }
pub struct Import { pub module: SymbolU32, pub name: SymbolU32, pub item: Item }
pub struct Export { pub name: SymbolU32, pub item: Item }

/// Provided by the host, or defined with what only a definition has.
pub enum Origin<D> { Imported(ImportIdx), Defined(D) }

/// What a function's callers and the backend may do with it, beside its body.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct FunctionFlags(u8);
impl FunctionFlags {
    pub const INLINE: Self = Self(1 << 0);
    // later: NO_INLINE, COLD, START, ...
}

pub struct Function {
    pub signature: SignatureIndex,
    pub origin: Origin<Code>,
}

pub struct Code {
    pub locals: Vec<Local>,   // params' scalars first; each one scalar
    pub label_count: u32,     // LabelId is in 0..label_count
    pub body: Body,
    pub root: ExprId,
}
// Global { .., origin: Origin<ConstInit> }, MemoryInfo { .., origin: Origin<()> }

pub struct Body {
    kinds: Vec<ExprKind>,
    types: Vec<ValueType>,
    lists: Vec<ExprId>,       // statements, call arguments, `Values`' values
    cases: Vec<Case>,         // Switch arms
    targets: Vec<Option<LocalIndex>>, // `SetLocals` targets; None drops
}

pub struct ExprList { start: u32, len: u32 } // a run of `lists`
pub struct CaseList { start: u32, len: u32 } // a run of `cases`
pub struct TargetList { start: u32, len: u32 } // a run of `targets`
pub struct Case { pub value: i64, pub body: ExprId }

#[derive(Clone, Copy)]
pub enum ExprKind {
    Noop,
    Unreachable,
    Int { value: i64 },
    Float { value: f64 },

    LocalGet { local: LocalIndex },
    LocalSet { local: LocalIndex, value: ExprId },
    /// Several scalar values as one (`notes/mir-pipeline.md`).
    Values { values: ExprList },
    /// `value`'s results into `targets`, a run of `Body::targets`.
    SetLocals { targets: TargetList, value: ExprId },
    Global { id: GlobalId },
    GlobalSet { id: GlobalId, value: ExprId },

    // Every opcode is one Wasm instruction, its signedness its own
    // (`notes/mir-pipeline.md`, "MIR's vocabulary").
    /// Eqz (integers, giving `I32`); Neg, Abs, Sqrt, Floor, Ceil, Trunc,
    /// Nearest (floats).
    Unary { op: UnaryOp, value: ExprId },
    /// Add, Sub, Mul, And, Or, Xor, Shl, ShrS, ShrU, DivS, DivU, RemS, RemU,
    /// Div, Min, Max, Copysign.
    Binary { op: BinaryOp, lhs: ExprId, rhs: ExprId },
    /// Eq, Ne, LtS, LtU, …, Lt, Le, Gt, Ge, giving `I32`.
    Compare { op: CompareOp, lhs: ExprId, rhs: ExprId },
    /// ExtendS, ExtendU, Wrap, TruncS, TruncU, ConvertS, ConvertU, Promote,
    /// Demote, Reinterpret: from the operand's type to the node's.
    Convert { op: ConvertOp, value: ExprId },

    /// Statements in order; the value is the last one's. No label, never a
    /// break target.
    Sequence { statements: ExprList },
    /// A break target: a labelled block, or an inlined function's wrapper.
    Block { label: LabelId, statements: ExprList },
    Loop { label: LabelId, body: ExprId },
    Break { label: LabelId, value: Option<ExprId> },
    Continue { label: LabelId },
    Return { value: Option<ExprId> },
    IfElse { condition: ExprId, then: ExprId, otherwise: Option<ExprId> },
    Switch { selector: ExprId, cases: CaseList, default: Option<ExprId> },

    /// A direct call. Call edges are derived from these nodes.
    Call { function: FunctionId, args: ExprList },
    // CallRef { callee: ExprId, args: ExprList } with function references.
    Drop { value: ExprId },

    // Memory nodes keep their current fields, with `ExprId` operands:
    // MemoryOffset, MemoryIndex, MemorySize, MemoryGrow, MemoryFill,
    // MemoryCopy, StaticPointer, and PointerLoad/PointerStore, which also
    // carry their access (width, and a load's extension). `static_data` is
    // derived from the StaticPointer nodes.
}
```

## Decisions

1. **Struct of arrays, as TIR's `Body`.** `kinds` and `types` are parallel;
   opt reads both, the inliner copies both. `ExprKind` is `Copy` (every field
   is an index or a scalar, about 16 to 24 bytes), so a pass matches
   `body.kind(id)` by value with no borrow conflicts.
2. **One variant per shape of operation.** About 75 variants become about
   25. Signedness and conversions were read from types at first; since step
   2.1 of `notes/mir-pipeline.md` they are the opcode's (`DivS`/`DivU`,
   `ConvertOp`), and types are Wasm's. A future saturating truncation is
   two more `ConvertOp`s.
3. **`Sequence` and `Block { label }` are separate nodes.** A label exists
   only where something can break to it: a loop, a labelled block, an
   inlined function's wrapper. Synthetic sequencing, `if` branches (TIR
   allows no label on `if`) and unlabelled blocks are `Sequence`, which opt
   builds transparently. `collect_break_targets`, `push_synthetic_scope` and
   `BlockScope` go away.
4. **Labels carry no data.** A label's kind is its owner node's (`Block` or
   `Loop`), its result type that node's type. `Function::label_count` sizes
   opt's per-label table and is where the inliner takes fresh labels. A label
   is not the `ExprId` of its owner: children are pushed first, so a `Break`
   would need the id before its target exists, and opt's table would be
   indexed by a sparse id.
5. **`Call` holds a `FunctionId`.** A direct call never needed a callee
   expression. With this, `call_edges`, `inline_functions` and `static_data`
   are derived, not stored.
6. **Function flags are a column beside `functions`.** `FunctionFlags(u8)`,
   in the style of TIR's `TypeFlags`. Not a field in `Function`: whether a
   function is inline is an attribute that the inliner's decision reads, not
   part of the body. The inliner asks it at every call (a lookup by
   `FunctionId`) and once for its order (which are inline). One byte holds up
   to eight flags read together. Relies on `FunctionId` being dense and equal
   to the index into `functions`, which lowering gives (ids are assigned in
   queue order and every queued instance is lowered); debug-asserted.
7. **One parent per node, no orphans.** Every node but `root` is the child
   of exactly one node, and every node is reachable from `root`.
   Debug-verified. So a linear scan over `kinds` equals a walk of the tree:
   the call graph, the static data a function uses, and verifiers are flat
   loops. Children-before-parent is **not** promised: an in-place rewrite
   (inlining) breaks it, nothing needs it, and `root` is stored explicitly.
8. **One `Body` per function**, not one for the whole MIR. Inlining copies
   either way (each call site needs its own locals), and opt builds one
   function at a time.
9. **No spans.** Lowering reports everything before MIR exists. Debug info
   would be one more parallel `Vec`.

10. **A `FunctionId` is its function's index** in `MIR::functions` and
    `MIR::function_flags`; `Function` has no `id` field. Lowering gives ids
    in queue order and lowers every queued instance, so this holds by
    construction (debug-asserted). Imported functions are in the same table
    and the same queue, so only an import something calls is lowered.
13. **Imports are a table of their own, for every kind.** `MIR::imports`
    holds each entry's metadata (`module`, `name`) and the item it provides;
    the item says only that it is imported, `Origin::Imported(ImportIdx)`,
    and a defined item holds what an import lacks (a function's `Code`, a
    global's initializer, nothing for a memory). The two links agree
    (`MIR::verify_imports`, debug-checked after lowering). Exports have the
    same shape, `Export { name, item }`.
14. **Ids are not Wasm indices, and their order means nothing.** Codegen
    numbers each index space with the imports first: one pass over
    `imports` in order, then the defined items in id order. Wasm allows
    several imports under one `module`.`name`, even with different types
    (`host.log` as `i32` and as `i64`), and each wx import is its own item
    in MIR, never merged by name. Codegen gives entries with the same names
    and the same *external* type one Wasm import (`log(i32)` and `log(u32)`
    are both `(param i32)`): the host provides both from the same names, so
    the set of what it must provide is unchanged.
11. **Lowering gives a label lazily.** A TIR scope gets a `LabelId` the first
    time a `break` or `continue` names it, and a loop always gets one; when
    a block's node is pushed, a scope with a label is a `Block`, any other a
    `Sequence`. The per-scope table is a `Vec<Option<LabelId>>` indexed by
    the dense `ScopeIdx`. Opt's block `0` is the function body and label `l`
    is block `l + 1`; an `if` or `match` branch gets a synthetic opt block.
12. **Lowering builds no node it discards**, so nothing is orphaned: a
    match's `unreachable` base is pushed only when a refutable arm needs it,
    an `|` condition with an irrefutable alternative is never built, and a
    test that turns out to always hold becomes `true` rather than dropping
    what was built around it. `verify` runs on every lowered function in
    debug builds.

## Child visitor

`ExprKind::ids_mut(&mut self, f: impl FnMut(Id))` is the one per-variant
function, where `Id` is `Expr(&mut ExprId)`, `List(&mut ExprList)`,
`Cases(&mut CaseList)`, `Local(&mut LocalIndex)` or `Label(&mut LabelId)`. Every
rewrite (inlining, a verifier, a future pass) goes through it, so a new
variant is one arm in one place.

## Inlining

Planned in `notes/mir-inlining.md`: the order (callees first, by strongly
connected components), the splice (append with four offsets, `Return` to
`Break`, the call node overwritten in place), dead-function compaction and
the automatic policy.

## Migration order

1. Done: the types, the child visitor and the verifier (`mir/body.rs`).
2. Done: `backend_tests.rs`, rebuilt on a small `Fixture` builder.
3. Done: the opt builder reads the arena; `collect_break_targets` and the
   transparent-block path are gone.
4. Done: lowering pushes arena nodes; the tree `ExprKind`/`Expression`,
   `call_edges`, `inline_functions` and `static_data` are deleted. The
   prescan records `#[inline]` (`defs::Attributes` on `FunctionDef`, only on
   a function with a body), and lowering sets `INLINE` on every instance of
   such a function.
5. Done: the inliner, `mir/inline.rs`, replacing `mir/inlining.rs`
   (deleted): `notes/mir-inlining.md`.
6. Dead-code elimination over every kind of item, as its own pass after
   the inliner: "Dead-code elimination" in `notes/mir-pipeline.md`.
