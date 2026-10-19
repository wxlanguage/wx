# TIR body checking: from constant initializers to function bodies

Status as of 2026-10-19, branch `tir-refactor`. A plan, not a record: nothing
here is implemented yet beyond what "Where we are" describes. Companion to
`tir-type-context.md` and `tir-check-pass.md`. Open questions are collected at
the end; several sections depend on their answers.

## Where we are

`BodyContext` (`typecheck.rs`) checks one expression tree into a `Body`
(`body.rs`) for a constant initializer or an enum discriminant. It covers:
literals (with in-place coercion of untyped subtrees, typeset targets included),
grouping, unary/binary operators through their traits (builtin node on a
primitive scalar, `MethodCall`/`GenericMethodCall` otherwise), tuples, paths to
constants and variants, and struct construction by position or name with local
inference of the struct's type arguments (`meet`/`learn`) and bound checks at
the call (`check_now`). Every other form is a `todo!()`, so turning function
bodies on today panics on the stdlib.

The `Body` is a flat arena (`kinds`/`types`/`spans`, `extra` for argument runs,
`arg_order` for named calls), children pushed before parents, the root last.
This already answers "body output shape" from `tir-type-context.md`: a TIR tree
in arena form, not side tables over the AST.

## What the old checker (`tir/builder/`) did, and what to keep

Kept, because it was right:

- **One expected type flowing down** (`AccessContext::expected_type`, `INFER` =
  none, `Wrapper<_>` = partial). `BodyContext::build(expr, expected)` already is
  this.
- **Purely local inference.** Type arguments are inferred inside one call
  (result seed, then arguments, then leftovers are "annotation required"). There
  are no inference variables spanning statements: `local x = 5;` is an
  annotation error, not a deferred literal. This is what makes "every fact is
  final, check on the spot" (`check_now`) possible, and it should stay (see Q1).
- **Poisoned contexts.** An `ERROR` expectation silences "annotation required"
  and mismatches below it. Already the convention.
- **Divergence by type.** A statement of type `!` ends the block; the rest is
  reported unreachable, and the block's type is `!` unless a tail says otherwise.
- **Feature slices that own their `report_*` diagnostics.** Keep that: split
  `typecheck.rs` into submodules on `BodyContext` (`calls`, `control`, `places`,
  `patterns`, `paths`, `literals`) as it grows, rather than one 6k-line file.
- **Destructuring flattened to projection paths** for MIR (`PathStep` with the
  aggregate type and the *declared* index). Still the right lowering contract,
  but it can be derived from a typed pattern arena instead of being the stored
  form (below).

Changed, because the rest of TIR moved on:

| Old | New |
| --- | --- |
| Boxed `Expression` tree, `Result<Expression, ()>` (a failure drops the node) | Arena, failures are `ExprKind::Error` nodes typed `ERROR` |
| `accesses: Vec<..>` on locals, labels, items | `NameResolutions`; add `Referent::Local` |
| `lookup: HashMap<(ScopeIndex, Symbol), LocalIndex>` + `BlockScope` tree stored in the body | A shadowing stack in the checker only; locals flat in the body |
| `EvalMode::{Comptime, Runtime}` deciding whether operators dispatch | Gone already: scalars always get builtin nodes, the evaluator folds them |
| Generic call inference via `infer_type_args` + `substitute_expected_type` + `type_satisfies_annotation` | `meet`/`learn` (struct construction already uses them) |
| Bound checks via `check_bounds(BoundOrigin, ..)` | `record_bounds_check` + `check_now` |
| `Place` tree for memory only; `Assign`/`Store`, `CompoundAssign`/`CompoundStore`/two generic twins | One place arena including locals; one `Assign`, one `CompoundAssign` (below) |
| `ast::Expression::String(symbol)`, `StructInit` | AST changed: strings are span-only, structs are call-shaped |
| Method/assoc lookup in `builder/calls.rs` + `members.rs` | `TypeContext::resolve_applicable_member`, `resolve_trait_qualified_value`, `select_trait_member` exist and are pure enough to call from a body |
| Globals as plain lvalues | `Type::Global` is nominal with `impl Global`/`GlobalMut` (`get`/`set`); see Q2 |

## Data design

The aim is that every new form is "push a node of a kind that already has a
shape", and that the hard parts (control-flow typing, places, patterns) each get
one small side table rather than spreading state through the tree.

### Owners

```rust
enum BodyOwner { Const(ConstIdx), Function(FunctionIdx), Global(GlobalIdx) }
```

Storage next to `const_bodies`: `function_bodies: Vec<Option<Body>>`,
`global_bodies: Vec<Option<Body>>`. `check_bodies` gains the function arms
(free, inherent, trait impl, trait default) and the global arm. A function body
is checked in `LexicalScope { env: signature.type_params, .. }`, expected type
its return type; a trait default method's `Self` stays abstract.

### Locals

```rust
index_newtype!(LocalIdx);
struct LocalDecl { name: Spanned<SymbolU32>, ty: TypeIndex, mutable: Option<TextSpan> }
// Body gains: locals: Vec<LocalDecl>   (parameters are locals 0..n)
```

Name lookup is a stack in `BodyContext`: `Vec<(SymbolU32, LocalIdx)>` plus a
mark per block; entering a block saves `len()`, leaving truncates. Lookup scans
from the top, so shadowing is free. A single-segment value path tries locals
first, then the namespace walk. No scope tree is stored: MIR/opt compute
liveness and coalesce locals themselves (`opt/liveness.rs`), so the body does
not need to say which block owned a local. Each use records
`Referent::Local { owner: BodyOwner, local: LocalIdx }` for the LSP.

### Statements and blocks

```rust
ExprKind::Block { stmts: ExprRange, tail: Option<ExprIdx>, target: Option<TargetIdx> }
ExprKind::Let { pattern: PatIdx, value: ExprIdx }        // type `()`, or `!` if value is
```

A statement is just an expression; `Let` is the one statement-only kind.

### Control flow: targets

Children are pushed before parents, so a `break` cannot point at its loop's
`ExprIdx`. Give jump targets their own index, allocated on entry:

```rust
index_newtype!(TargetIdx);
struct Target { kind: TargetKind /* Loop | Block | Function */, label: Option<Spanned<SymbolU32>>,
                expected: TypeIndex, ty: TypeIndex /* INFER until a value arrives */ }
ExprKind::Loop { body: ExprIdx, target: TargetIdx }
ExprKind::Break { target: TargetIdx, value: Option<ExprIdx> }   // type `!`
ExprKind::Continue { target: TargetIdx }                        // type `!`
ExprKind::Return { value: Option<ExprIdx> }                     // target 0 is the function
```

Targets are kept in the `Body` (MIR needs them as branch depths). During
checking each target also collects the `break`s that gave it a value, so that
when its type is settled the untyped ones can be coerced (`loop { if c { break 1 }
break x }`). That list is checker state only. `return` is a break to the
function's target, so `if c { return 1 }` and `break` share one rule.

`IfElse { cond, then, else_: Option<ExprIdx> }` and
`Match { scrutinee, arms: ArmRange }` type their branches by the same "join"
rule: with an expectation, each branch is checked against it; without one, the
first typed branch sets the type and untyped siblings are coerced to it
(`coerce` learns to descend into `Block` tails, `IfElse` branches and `Match`
arms, which is a small extension of what it does for `Tuple` today). `!` joins
with anything.

`expect` needs one rule it lacks today: `!` is accepted wherever any type is
expected.

### Places

Reads, writes and `.&` all need to know what is a location. Keep the
place/value split from `tir-place-value-split.md`, in arena form, and let it
include locals so assignment is one node:

```rust
index_newtype!(PlaceIdx);
enum PlaceKind {
    Local(LocalIdx),
    Global(GlobalIdx),                                  // if Q2 says globals are places
    Deref { pointer: ExprIdx },                         // `p.*`, the only way into memory
    Field { base: PlaceIdx, field: FieldIdx },
    Index { base: PlaceIdx, index: ExprIdx },
    Temp(ExprIdx),                                      // `make().x`: an rvalue, not assignable
}
struct Place { kind: PlaceKind, ty: TypeIndex, memory: Option<TypeIndex>, mutable: bool }

ExprKind::Load(PlaceIdx)                                // reading `x`, `p.*.y`, `t.x`
ExprKind::AddressOf(PlaceIdx)                           // `.&`; requires `memory: Some(_)`
ExprKind::Assign { place: PlaceIdx, value: ExprIdx }
ExprKind::CompoundAssign { op: BinaryOp, place: PlaceIdx, value: ExprIdx, dispatch: OpDispatch }
ExprKind::Discard(ExprIdx)                              // `_ = e`
```

`memory`/`mutable` are computed once when the place is built (from the root
`Deref`'s pointer, a `local mut`, a `global mut`), so "cannot assign",
"cannot take address of a local" and "store through `&T`" are each a field read.
This collapses the old six assignment kinds into two, and lets MIR compute an
address once for both halves of `p.*.x += 1`.

### Operator dispatch as a value

Today the operator decision is spread over three kinds (`Binary`,
`MethodCall`, `GenericMethodCall`). Compound assignment needs the same decision
without being a call, so name it once:

```rust
enum OpDispatch { Builtin, Method(FunctionIdx), Generic(FunctionIdx) }
```

`select_binary`/`select_unary` return it; `Binary`/`Unary` keep their shape for
the builtin case (the evaluator and MIR like them), and `CompoundAssign` stores
it. Whether `Binary` itself should carry `dispatch` instead of turning into a
`MethodCall` is a taste call; the latter keeps the evaluator simpler.

### Calls

```rust
ExprKind::Call { callee: Callee, args: ExprRange, order: ArgOrder }
enum Callee {
    Function { func_index: FunctionIdx, type_args: TypeList },     // direct, `f::<T>(..)`
    Method { method: FunctionIdx, type_args: TypeList },           // selected impl member
    Generic { method: FunctionIdx, type_args: TypeList },          // trait declaration, abstract receiver
    Indirect(ExprIdx),                                             // a `func(A) -> R` value
}
```

`MethodCall`/`GenericMethodCall` from operators fold into this. Struct
construction stays its own kind (no callee). Inference for a function call is
struct construction generalised: the callee's parameter frame plays the struct's
role, the parameter types the fields', and the return type is met with the
expected type first. `struct_type_args`/`learn_field`/`field_type`/
`report_uninferred`/`check_struct_bounds` become one "instantiate a generic
frame at a call" helper used by both. Named arguments map through
`FunctionDef::params` exactly as fields do through `StructDef::lookup`.

`Type::Function` (a function item's zero-sized type) is what a bare path to a
function evaluates to; it coerces to `Type::FunctionRef` where one is expected.
Calling a value of a user type that implements `Call` would be
`Callee::Method` on `Call::call` (see Q3).

### Patterns

```rust
index_newtype!(PatIdx);
enum PatKind {
    Wildcard,
    Bind(LocalIdx),
    Tuple(PatRange),
    Struct { struct_index: StructIdx, fields: PatRange, order: ArgOrder, rest: bool },
    // match only:
    Literal(ExprIdx),            // an integer/bool/char literal node, already coerced
    Variant(ConstIdx),
}
// Body gains: pats: Vec<PatKind>, pat_types: Vec<TypeIndex>, pat_spans, pat_extra
```

`local` destructuring and `match` arms share it. `ArgOrder` already models
"which field does the n-th element give", so struct patterns reuse it. MIR's
flattened `PathStep` list is a walk over this. Match arms are still parsed as
expressions (`ast::MatchArm::pattern`), so the pattern lowerer reads expression
syntax; that is fine for literals, `_` and variant paths, and is where an
or-pattern or a binding pattern would need a parser change later.

## Order of work

Each step ends with tests in `signatures.rs`'s suite style and with no
`todo!()` reachable from the stdlib once function bodies are switched on.

### 0. Plumbing (small, do first)

- `BodyOwner`, `function_bodies`/`global_bodies`, function arms in
  `check_bodies`, parameters as locals.
- Replace the `todo!()`s in `build` with one `Severity::Bug` diagnostic
  ("not supported by the checker yet") and an `Error` node, so function bodies
  can be enabled immediately and the stdlib's diagnostic count is the progress
  meter. Add the missing committed test that the embedded stdlib sweeps clean,
  marked `#[ignore]` until it passes.
- `expect` accepts `!`.

### 1. Relatively simple (the existing machinery covers the hard part)

- **Locals and `local x: T = e` / `local x = e`** with the binding stack;
  `Referent::Local`; "annotation required" for an untyped initializer without
  a type, as before.
- **Blocks** with statements, tails, unreachable-code warning, unused-value
  warning.
- **`if`/`else`** (condition `bool`, join rule, missing `else` when the then
  branch is not `()`/`!`).
- **`return`** (target 0).
- **Direct calls** to free functions, generic included, by position and by
  name: the struct-construction inference generalised. Intrinsic functions are
  ordinary bodiless functions here.
- **`as` casts** between scalars, `char`, enums to their repr, and `as _`
  from the expected type. Write the validity table fresh rather than porting
  `are_scalar_compatible`, and close the `&T as *T` hole while at it.
- **Function items as values** and their coercion to `func(A) -> R`.

After step 1 most stdlib bodies type-check: they are intrinsic calls, `if`,
`self` and operators.

### 2. Moderate (needs a small design decision, listed in the section)

- **Method calls** `x.m(..)` and **type-relative paths** `T::f`, `Self::CONST`,
  `<T as Tr>::f`, `heap::DATA_END`: `resolve_applicable_member` with a value
  key, then `select_trait_member`. Decision: how the impl's own parameters are
  inferred from the receiver for `impl<T> Wrapper<T> { func m(self) }`. Proposal:
  `learn` the impl's frame from the impl target against the receiver type (the
  same walk `learn` does for a field), then the method's own frame from its
  arguments. A trait-owned constant on an abstract receiver needs a node of its
  own (`AbstractConst { receiver, const_index }`), as in the old checker.
- **`loop`/`break`/`continue`/labels**: the target table. Decision: whether a
  loop without any valued `break` is `!` (old behaviour; yes).
- **Assignment and compound assignment**: the place arena, mutability checks.
  Decision: Q2 (globals).
- **Field access** `x.y` on a value and through a place. Field privacy is
  enforced here (the old checker did, for all three sites).
- **`match`** on enums, `bool`, integers and `char`: patterns, exhaustiveness
  (enum variants and `bool` by set, integers need `_`), unreachable arms.
- **`local` destructuring**: the pattern arena; mostly a port of
  `collect_pattern_bindings`, minus the path bookkeeping.

### 3. Think first

- **Pointers and memory**: `.*`, `.&`, string literals (`&[u8]` in the ambient
  memory), array literals and repeats (static data), indexing, slice ranges.
  Each needs "which memory", which today lives only in the type resolver's
  ambient lookup; a literal also needs a static-data story that MIR used to
  own. Decide where ambient-memory resolution lives for expressions and what a
  string literal node carries (its decoded bytes, or a span decoded later).
- **Calls through `Call`** for non-function values (Q3), and whether
  `Callee::Indirect` is a separate path or `Call::call` on `FunctionRef`.
- **Method-call privacy**, which the old checker never enforced (CLAUDE.md
  pitfall). New code can do it from the start since impl members carry
  visibility; decide the rule for trait default methods (fall back to the
  trait's visibility).
- **Impl conformance** is not a body concern, but `GenericMethodCall` to a
  default the impl does not override assumes it. Keep it on the list.
- **Constant evaluation of richer bodies**: the evaluator returns `NotConst`
  for anything it does not know, so new kinds are safe by default. Whether
  `const` initializers may use `if`/blocks/calls to `const`-able functions is a
  separate feature.

## Open questions

- **Q1. Inference scope.** Keep inference local to one call/construction (no
  inference variables across statements; `local x = 5;` needs a type)? Everything
  above assumes yes; the alternative needs a fulfillment context and deferred
  obligations per body, which `check_now` deliberately avoids.
- **Q2. Globals.** A global's type is now nominal (`Type::Global`, with `impl
  Global { get }` and `impl GlobalMut { set }`), but the examples read and
  assign them as plain values (`bump = new_end; bump as u32`). Is the plan that
  the name `bump` in an expression means its value and is a place (implicit
  `get`/`set`), or that it means the handle and the user writes `bump.get()` /
  `bump.set(x)`? Same question, smaller, for a memory's name (`heap.grow(1)` is a
  handle; is it ever a value otherwise?).
- **Q3. Calls through `Call`.** Should `f(x)` on a value whose type implements
  `Call` (a user struct) be accepted now, or only function items and
  `func(..)` references, with `Call` left to bounds (`F: Call`) for the moment?
- **Q4. Operator nodes.** Keep `Binary`/`Unary` for builtins and a call node
  for overloaded operators (today's split), or one operator node carrying
  `OpDispatch`? The plan above keeps today's split and uses `OpDispatch` only
  for compound assignment.
- **Q5. Typeset-abstract literal arithmetic in bodies.** Coercion of literals
  to an abstract typeset-bounded `T` exists for constants; in a body, an operator
  on `T` gives a `GenericMethodCall`. Is anything beyond that expected (for
  example `as` casts between typeset members)?
