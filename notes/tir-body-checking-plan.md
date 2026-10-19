# TIR body checking: from constant initializers to function bodies

Status as of 2026-10-19, branch `tir-refactor`. A plan, not a record: nothing
here is implemented yet beyond what "Where we are" describes. Companion to
`tir-type-context.md` and `tir-check-pass.md`. Open questions are collected at
the end; several sections depend on their answers.

## Where we are

`BodyContext` (`typecheck.rs`) checks one expression tree into a `Body`
(`body.rs`) for a constant initializer or an enum discriminant. It covers:
literals (with in-place coercion of untyped subtrees, typeset targets included),
grouping, unary/binary operators through their traits (`PrimitiveBinary`/
`PrimitiveUnary` on a primitive scalar, `ConcreteMethodCall`/`AbstractMethodCall`
otherwise), tuples, paths to
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
| `BlockScope` holding its own `Vec<Local>`, locals addressed by `(ScopeIndex, LocalIndex)`, a separate `BlockLabel` arena | The scope tree is kept in the `Body`; a local is one `LocalIdx`; labels stay their own arena (`Body::labels`, a scope points at one); typing state per scope stays in the checker |
| `EvalMode::{Comptime, Runtime}` deciding whether operators dispatch | Gone already: scalars always get builtin nodes, the evaluator folds them |
| Generic call inference via `infer_type_args` + `substitute_expected_type` + `type_satisfies_annotation` | `meet`/`learn` (struct construction already uses them) |
| Bound checks via `check_bounds(BoundOrigin, ..)` | `record_bounds_check` + `check_now` |
| `Place` tree for memory only; `Assign`/`Store`, `CompoundAssign`/`CompoundStore`/two generic twins | Kept: memory-only places, `Assign`/`Store`, compound nodes on both targets, plus `Primitive*` variants (below) |
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

### Scopes and locals

A body's lexical structure is stored, not discarded. A block scope is
where locals are declared and what `break`, `continue` and `return` jump to,
so one tree serves both. The lifetime and ownership analyses designed in
`notes/` will read it later.

```rust
index_newtype!(ScopeIdx);
index_newtype!(LocalIdx);
index_newtype!(LabelIdx);

/// One lexical block. Scope 0 is the body's root: a function's parameters
/// live there and `return` jumps out of it. A constant's or global's
/// initializer has a root too, with no locals.
struct Scope {
    kind: ScopeKind,
    parent: Option<ScopeIdx>,
    /// `outer: loop { .. }`, `outer: block { .. }`, `outer: if .. { .. }`.
    label: Option<LabelIdx>,
    span: TextSpan,
}

enum ScopeKind {
    /// `block { .. }`, an `if`/`else` branch, a match arm's body, or the body
    /// itself (the root is the scope without a parent). Its type is its
    /// tail's, or a `break` value's when it is labelled.
    Block,
    /// `loop { .. }`: `continue` re-enters it, its type comes only from `break`.
    Loop,
}

/// A parameter or a name a `local` pattern binds.
struct Local {
    name: Spanned<SymbolU32>,
    ty: TypeIndex,
    mutable: Option<TextSpan>,
}

/// A written block label, as the old `BlockLabel`. One label can name two
/// scopes: both branches of a labelled `if`/`else` point at it.
struct Label {
    name: Spanned<SymbolU32>,
}

// Body gains: scopes: Vec<Scope>, locals: Vec<Local>, labels: Vec<Label>
```

**Two orders, one per arena.** A scope is allocated when the checker *enters*
the block (top-down), and an expression node when it *finishes* one (bottom-up,
children first). Each order fits its job: a scope must exist before its
contents, because a `break` inside names it, and a node must come after its
children. So a jump names the scope it leaves, and no extra index is needed for
jump targets:

```rust
ExprKind::Block { scope: ScopeIdx, stmts: ExprRange, tail: Option<ExprIdx> }
ExprKind::Loop  { scope: ScopeIdx, stmts: ExprRange }
ExprKind::Let   { pattern: PatIdx, value: ExprIdx }     // type `()`, or `!` if the value is
ExprKind::Break    { scope: ScopeIdx, value: Option<ExprIdx> }   // type `!`
ExprKind::Continue { scope: ScopeIdx }                           // a `Loop` scope; type `!`
ExprKind::Return   { value: Option<ExprIdx> }                    // leaves scope 0; type `!`
```

A statement is just an expression; `Let` is the one statement-only kind. A
labelled block or loop is an ordinary `Block`/`Loop` whose scope points at a
label. A labelled `if` pushes one label and gives both branch scopes that
`LabelIdx`, as `build_label_expression` did; a `break :outer` inside a branch
leaves that branch's scope, which ends the `if`.
`return` keeps its own kind, since MIR emits it differently, but is typed by
the same rule as a `break` out of scope 0.

**A local has one identity, `LocalIdx`.** The old model numbered locals per
scope and addressed one by `(ScopeIndex, LocalIndex)`. Here the scope is not
half of its name, so `Referent::Local { owner: BodyOwner, local: LocalIdx }`
and a pattern binding carry one index. Which block declares a local is not
stored on it: the checker only needs it while resolving names (the
`(scope, name)` map), and afterwards the tree holds it (a `LocalDeclaration`
sits among one block's statements; parameters are in the root). If a consumer
(MIR's slot sharing, the LSP) needs a direct "locals of scope S" lookup, it is
added then. Shadowing is explicit: `local x = 1; local x = x + 1;`
is two `Local`s with the same name in the same scope, and the second hides the
first from its own `Let` onwards. That is what rustc models with its
"remainder" scopes, and here it falls out of declaration order.

**Checking state lives beside the tree, not in it.** `BodyContext` holds:

```rust
current: ScopeIdx,
/// Scope-relative lookup, as in the old `ExprContext::lookup`.
lookup: HashMap<(ScopeIdx, SymbolU32), LocalIdx>,
/// Index-aligned with `Body::scopes`.
scope_types: Vec<ScopeType>,

struct ScopeType {
    expected: TypeIndex,     // INFER = unconstrained
    ty: TypeIndex,           // INFER until a result, `break` or `return` settles it
}
```

An untyped `break` or `return` value with nothing to hold it to needs an
annotation, as in the old checker; only a block's result may stay untyped, for
its context to coerce. (Collecting a scope's untyped `break`s to coerce them
later was considered and left out until a case needs it.)

To resolve a name, probe `(current, name)`, then `(parent, name)`, and so on up
to the root: one hash probe per enclosing block, so the cost grows with nesting
depth, not with the number of locals. rustc's resolver works the same way: a
stack of "ribs", one hash map per scope, walked outwards. A declaration inserts
`(current, name)` after its initializer is checked, so `local x = x + 1` reads
the outer `x`, and a later `local x` in the same block overwrites the entry.
Leaving a block needs no cleanup: lookups start from `current`, and a sibling
block has a different `ScopeIdx`. A name that is not a local falls through to
the namespace walk.

Labels resolve the same way, as the old `ExprContext::resolve_label` did: walk
up from `current` to the first scope whose label has that name (`break :outer`),
giving `(ScopeIdx, LabelIdx)`; the jump stores the scope and the use records
`Referent::Label { owner: BodyOwner, label: LabelIdx }`. An unlabelled `break`
or `continue` takes the nearest `Loop`, `return` the root. The label's old
`accesses: Vec<TextSpan>` is that resolution entry now, so the checker keeps
only a `used: Vec<bool>` beside `labels` for the unused-label warning
(`report_stack_warnings`'s check), rather than scanning the table.

For comparison, rustc keeps the same facts, spread over a few phases. Name
resolution uses ribs. HIR records each `break` target as the id of the
block or loop (`hir::Destination`). THIR blocks carry a `region_scope`, and
`Break`/`Continue` name a `region::Scope`. A separate `ScopeTree` built after
type checking maps every variable to its declaring scope (`var_map`) for
borrow checking. Here the checker builds the scope tree directly, since nothing
between parsing and checking produces one.

`IfElse { cond, then, else_: Option<ExprIdx> }` and
`Match { scrutinee, arms: ArmRange }` type their branches by the same "join"
rule: with an expectation, each branch is checked against it; without one, the
first typed branch sets the type and untyped siblings are coerced to it
(`coerce` learns to descend into `Block` tails, `IfElse` branches and `Match`
arms, which is a small extension of what it does for `Tuple` today). `!` joins
with anything.

`expect` needs one rule it lacks today: `!` is accepted wherever any type is
expected.

### Places and assignment

Implemented as the old checker had it, in arena form. A place is a location in
linear memory only, always reached through a pointer:

```rust
enum PlaceKind {
    Deref { pointer: ExprIdx },              // `p.*`, the only way into memory
    Field { object: PlaceIdx, field: FieldIdx },
}
struct Place { kind, ty, memory: TypeIndex, mutable: bool, span }

ExprKind::Load(PlaceIdx)                     // reading `p.*`, `p.*.x`
ExprKind::AddressOf(PlaceIdx)                // `.&`
ExprKind::FieldAccess { object, field }      // a field of a value (local, call result)
```

A local or a field of a value is not a place: it has no address, and whether
it is assignable is a property of the expression (`Local`, `FieldAccess`
rooted in one). A global's name is its handle (`Type::Global`),
not a location: it is read with `Global::get` and written with
`GlobalMut::set`, so `=` on it is an invalid target. There is no temporary root:
deciding where a call's result lives is MIR's job. `_ = value` is its own
`Drop`, not an assignment.

The assignment kinds stay separate, for the reasons they were split in the old
checker: a place is an address computed once and written through (`Store`,
`*CompoundStore`), the other targets are expressions (`Assign`,
`*CompoundAssign`); and an abstract target type keeps the trait's declaration
for monomorphization. Operator and compound nodes are named on two axes. The
prefix says what defines the operation: `Primitive` (the primitive scalar's
operator, holding `op`), `Concrete` (the method of the impl selected for a
concrete type) or `Abstract` (the trait's declaration, its impl selected at
monomorphization), both holding `method`. The rest says where the result goes:
`Assign` (a local or a field of one), `Store` (a place in linear memory), or
nowhere (a value):

| | value | into a local | into memory |
|---|---|---|---|
| `Primitive` | `PrimitiveBinary`, `PrimitiveUnary` | `PrimitiveCompoundAssign` | `PrimitiveCompoundStore` |
| `Concrete` | `ConcreteMethodCall` | `ConcreteCompoundAssign` | `ConcreteCompoundStore` |
| `Abstract` | `AbstractMethodCall` | `AbstractCompoundAssign` | `AbstractCompoundStore` |

Compared with the old checker, which had four compound nodes that always held a
method (primitives went through their `#[inline]` impls), the `Primitive`
variants are new: plain operators on primitives already build
`PrimitiveBinary`, so `op=` follows them.

A `Load` is pushed only where a place's value is used, so `.&` and the left of
`=` take the place itself and no node is orphaned.

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

`ConcreteMethodCall`/`AbstractMethodCall` from operators fold into this. Struct
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

- **Scopes, locals and `local x: T = e` / `local x = e`**, with scope-relative name lookup;
  `Referent::Local`; "annotation required" for an untyped initializer without
  a type, as before.
- **Blocks** with statements, tails, unreachable-code warning, unused-value
  warning.
- **`if`/`else`** (condition `bool`, join rule, missing `else` when the then
  branch is not `()`/`!`).
- **`return`** (leaves scope 0).
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
- **`loop`/`break`/`continue`/labels**: `Break`/`Continue` naming their scope. Decision: whether a
  loop without any valued `break` is `!` (old behaviour; yes).
- **Assignment and compound assignment**: the place arena, mutability checks.
  Globals are handles, written through `GlobalMut::set` (Q2).
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
- **Impl conformance** is not a body concern, but `AbstractMethodCall` to a
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
- **Q2. Globals.** Decided: a global's name means its handle, of its nominal
  type `Type::Global` (with `impl Global { get }` and, for `global mut`,
  `impl GlobalMut { set }`). Its value is `g.get()`, a write is `g.set(x)`;
  `g = x` and `g op= x` are invalid assignment targets. Until method calls are
  checked, both forms are reported as unsupported.
- **Q3. Calls through `Call`.** Should `f(x)` on a value whose type implements
  `Call` (a user struct) be accepted now, or only function items and
  `func(..)` references, with `Call` left to bounds (`F: Call`) for the moment?
- **Q4. Operator nodes.** Decided: one node per way an operation is defined
  (`Primitive`/`Concrete`/`Abstract`) and per destination (value, `Assign`, `Store`);
  see the table under places and assignment.
- **Q5. Typeset-abstract literal arithmetic in bodies.** Coercion of literals
  to an abstract typeset-bounded `T` exists for constants; in a body, an operator
  on `T` gives a `AbstractMethodCall`. Is anything beyond that expected (for
  example `as` casts between typeset members)?
