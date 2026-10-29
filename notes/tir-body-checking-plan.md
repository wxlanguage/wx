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
`PrimitiveUnary` on a primitive scalar, `Call`/`AbstractCall` of the operator's
method otherwise), tuples, paths to
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
    /// `loop :outer { .. }`, `block :outer { .. }`.
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
`accesses: Vec<TextSpan>` is that resolution entry now, and the checker keeps
nothing beside it. Unused labels (and later unused locals and imports) are not
reported while checking: they are the inverse of the resolutions table, and
will be reported together from it in one pass (for a body, a range query over
its span).

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
for monomorphization. Operator, call and compound nodes are sorted on two
axes. The first is what defines the operation: a primitive scalar's operator
(`Primitive*`, holding `op`); a known function (`Call`, `ConcreteCompound*`,
the selected impl's method for an operator); or a trait's declaration, its impl
selected at monomorphization (`AbstractCall`, `AbstractCompound*`). Every
function is held with its type arguments as one flat `TypeList`: an impl's
arguments, then the function's own (`[Self, own...]` for a trait's
declaration), the layout `substitute`/`learn` and signatures already use. The
second, for a compound assignment, is where the result goes: `Assign` (a local
or a field of one) or `Store` (a place in linear memory):

| | value | into a local | into memory |
|---|---|---|---|
| native op | `PrimitiveBinary`, `PrimitiveUnary` | `PrimitiveCompoundAssign` | `PrimitiveCompoundStore` |
| known function | `Call`, `MethodCall` | `ConcreteCompoundAssign` | `ConcreteCompoundStore` |
| trait declaration | `AbstractCall`, `AbstractMethodCall` | `AbstractCompoundAssign` | `AbstractCompoundStore` |

Compared with the old checker, which had four compound nodes that always held a
method (primitives went through their `#[inline]` impls), the `Primitive`
variants are new: plain operators on primitives already build
`PrimitiveBinary`, so `op=` follows them.

A `Load` is pushed only where a place's value is used, so `.&` and the left of
`=` take the place itself and no node is orphaned.

### Calls

```rust
/// Direct: a free function, `Type::f(..)`, `Type::m(x, ..)`.
ExprKind::Call { function: FunctionIdx, type_args: TypeList, args: ExprIdx }
/// A trait's declaration: an abstract receiver, or an impl inheriting a default.
ExprKind::AbstractCall { method: FunctionIdx, type_args: TypeList, args: ExprIdx }
/// `x.m(..)`, an operator's method, `Call::call` of a value; and its abstract twin.
ExprKind::MethodCall { function, type_args, receiver: ExprIdx, args: ExprIdx }
ExprKind::AbstractMethodCall { method, type_args, receiver: ExprIdx, args: ExprIdx }
/// A `func(A) -> R` value.
ExprKind::CallRef { callee: ExprIdx, args: ExprIdx }
```

`args` is one value of the parameters the call's list fills: `()` for none,
the argument itself for one, a `Tuple` of the arguments in written order with
an `ElementOrder` for several (permuted for a call by name), or one value
written for several (`f(p)`). A construction holds its fields the same way
(`StructConstructor { fields }`). A method call keeps its receiver beside
`args`: `x.m(a)` is a `MethodCall` and `T::m(x, a)` a `Call` whose `args`
hold `x` too. They mean the same call; the receiver is apart because what it
is given for differs from what an argument is (a `self: M::*Self` method is
called on the pointer itself, and any receiver adjustment belongs there), and
because `x.m(p)` for `m(self: Self, a: A, b: B)` has no value of
`(Self, A, B)` without taking `p` apart. Struct construction
stays its own kind. Inference for a function call is struct construction
generalised: the callee's parameter frame plays the struct's role, the
parameter types the fields', and the return type is met with the expected type
first. For a method, the frame's leading slots are the impl's, filled by impl
selection (`match_impl_target`, `find_trait_impl`); the written `::<..>` and
`learn` fill the method's own.

`Type::Function` (a function item's zero-sized type) is what a bare path to a
function evaluates to; it coerces to `Type::FunctionRef` where one is expected.
Calling a value of a user type that implements `Call` is a `Call` of
`Call::call`'s impl (Q3); a type itself is never called.

### Named calls and parameter names

Decided 2026-10-22; parts 1 and 3 implemented, part 2 left to conformance. A call may name its arguments,
`f({ b: 2, a })`, as a struct construction already can. Three pieces, in the
order they are built: a parameter may be unnamed, a trait impl's parameters
take their names from the trait, and a call by name binds each argument to the
parameter of its name. Supersedes `notes/wx-named-invocation-and-struct-constructors.md`
where the two differ (that note's record structs and named-only constructors
predate the one-form struct).

**1. Parameters and fields share one grammar** (done). Both are a binding
and a type, written the same way and parsed by one function
(`Parser::parse_binding_and_type`):

```
param, field ::= binding ":" Type   // both parts
               | Type               // the binding left out: `_: Type`
binding      ::= "_" | name | "mut" name
field        ::= ["pub"] (as above)
```

A binding is the same leaf a `local` pattern binds with, and it is always
followed by `:`. Anything without a `:` is a type, with no exception: `x`
alone is the type `x` (as it was already for a struct field), and `_` alone is
the type `_`, the inference placeholder, which a signature never accepts.
There is no parameter or field without a type, the receiver's included:
`self` is a name like any other and is written `self: Self` (or
`self: M::*Self`); its type is never implied.

| written | parameter | field |
|---|---|---|
| `i32`, `_: i32` | unnamed, binds nothing | unnamed: built and destructured by position only |
| `x: i32` | an immutable local `x` | a field `x` |
| `mut x: i32` | a mutable local `x` | a mutable field `x` (designed, not checked yet) |
| `self: Self` | the receiver, first in a trait or impl function | reported: a field cannot be named `self` (E1008) |
| `x` | the type `x`: "cannot find type `x`" | the same |
| `_` | the type `_`: rejected, signatures do not infer | the same |
| `self`, `mut x`, `mut i32` | E1023 "expected a type annotation" | the same |
| `mut _: i32`, `mut *u8`, `mut heap::*u8` | E1022 "`mut` needs a name" | the same |

`mut` always means that the named place may be reassigned; what differs is
whose it is. A parameter's belongs to the body, so its `mut` is invisible to
callers, absent from function types, and free in trait impls. A field's
belongs to the value, so its `mut` is part of the struct's type (below).
Without a name there is nothing to reach it by: an unnamed parameter binds no
local, and wx has no positional field access (`t.0` is never added, since
`t.0.1` would be ambiguous with the float `0.1`), so `mut` needs a name in
both.

An unnamed parameter is how a parameter is ignored: the body cannot read what
it cannot name, and it needs no unused-parameter exemption later. Function
types `func(A, B) -> R` stay unnamed; a declaration names its parameters.

- AST: `Binding` is `Wildcard(span)` (`_`) or `Name { mut_span, name }`, so
  `mut _` cannot be represented; `FunctionParam { binding: Option<Binding>,
  ty }` and `StructField { pub_span, binding: Option<Binding>, ty }`, `None`
  when the binding is left out. `_: T` and `T` mean the same; the AST keeps
  which was written. The type is always
  present: a binding written without one (`self`, `mut x`) keeps its name
  and is given `TypeExpression::Error`, which resolves to `ERROR` silently,
  so the parameter and those after it survive.
- Where a `self` may stand is not the parser's question: `defs` reports one
  that is not first in a trait or impl function (E2098, as before) and a
  field named `self`; a free function's `self` is reported once and its type
  not resolved.
- `defs`: `FunctionDef::params` holds `Option<Spanned<SymbolU32>>` per
  parameter; the duplicate-name check (E2097) skips unnamed ones.
- `signatures`: every parameter's type is resolved as written, the receiver's
  too; E2099 (`MissingParameterType`) and the receiver's implied `Self` are
  gone.
- Bodies: a named parameter is a local of the root scope; an unnamed one binds
  none. `Body::params` maps each parameter to its local (`None` when
  unnamed), so `Local::name` stays required. MIR gives every parameter a Wasm
  parameter and reads a named one through its local.
- wx-fmt prints parameters and fields as written, `_: T` included.
- The AST test harness now uses the keyword-seeded interner
  (`Keyword::create_interner`), as every compilation does.
- Later, maybe: `Pattern::Wildcard` and `Pattern::Binding { mut_span, name }`
  are `Binding`'s two cases, and the pattern leaf could hold one.

**Field mutability** (designed, not checked). Wasm GC declares each struct
field mutable or not, and the mutability is part of the type: `struct.set`
needs a mutable field, two struct types differing only in it are different
types, and only an immutable field may be refined in a subtype. wx makes it
explicit rather than inferring it, and gives it to every struct, GC or not.
Open: the checker rule for a linear-memory struct (a write through a place
needs an exclusive pointer *and* a `mut` field?), and that fields are then
immutable unless marked, which breaks the field writes in `examples/vec`,
`examples/arena`, `examples/hashing` and `examples/snake`.

**2. A trait impl's parameters are named by the trait** (left to impl
conformance, which is not implemented; calls by name do not depend on it,
since they read the trait's names). Where a trait's
declaration names a parameter, the impl's function either uses that name or
leaves the parameter unnamed (ignored); where the trait leaves it unnamed, the
impl may name it freely, since that name is only a local. `mut` is free (it
belongs to the local, not the interface); `self` matches by position.

- Why: a trait method has one spelling. `T::add({ rhs })` in generic code and
  `Point::add({ rhs })` in concrete code are the same call, and whether an impl
  overrides a default (`Call` or `AbstractCall`) never changes which names are
  valid. Parameter names are API, and the trait is their one owner.
- A different name inside the impl is a `local`: `local other = rhs;`. A trait
  name that hides an item the body needs is reached by a qualified path
  (`crate::size(..)`, `super::size(..)`), which never looks at locals.
- Checked in `check_declarations`, for each function of a trait impl: its
  declaration is `declared_trait_member(trait, value key of its name)`, and
  the names are compared position by position. A parameter count or receiver
  mismatch is conformance's, not this check's. New diagnostic: "parameter
  `other` is named `rhs` in trait `Add`", at the impl's name, with the trait's
  as a secondary label; help: use the trait's name, or leave it unnamed if
  unused.
- Costs, accepted: renaming a trait parameter breaks every impl that uses it
  (one that leaves it unnamed is unaffected).
- Inherent impls and free functions own their names; synthetic impls (`Call`
  for functions, `Memory`, `Global`) have no written parameters.
- Later, maybe: `_` or `a: _` taking the type from the trait. Left out:
  every signature stays readable on its own, and adding it breaks nothing.

**3. Calls by name** (done). `f({ a: 1, b })`, `T::f({ .. })`, `<T as Tr>::f({ .. })`
and `x.m({ .. })`, whose receiver gives `self`. Only a call whose function is
known statically can be named.

- The names are the selected function's declaration's; for a trait impl's
  function, its trait declaration's (by rule 2 they agree wherever the trait
  names one, and an impl's unnamed parameter must not make a concrete call
  positional only).
- A function with an unnamed parameter (past the receiver) is called by
  position only; naming it is an error (E2123), with the same code and
  wording as `X({ .. })` for `struct X(i32, b: i32)`.
- Decided: `self` is a name like any other, so a method called through its
  type names its receiver, `T::m({ self: x, rhs })`; method syntax gives it,
  and naming `self` there is an unknown name (E2120), as is any name the
  receiver already took.
- Checking: arguments in written order;
  each name finds its parameter (the first of that name); each value is built
  with the parameter's type as known so far and learned from; an unknown name,
  a name given twice and missing parameters are reported (new codes E2120
  `UnknownParameterName`, E2121 `DuplicateNamedArgument`, E2122
  `MissingArguments`, and E2123 `PositionalOnlyCall` for a target with an
  unnamed parameter), and dropped arguments are built with nothing expected.
  Then the same final `expect` and bound checks as a positional call.
- A struct construction is a call of its constructor and is checked by the
  same code: `CallTarget` (`typecheck/calls.rs`) is read once per call from
  a function or a struct, whose parameters are its fields (the type
  parameters' frame, the parameter types, the parameter names), and
  `build_arguments` checks either's arguments by position or by name. Only
  diagnostics and bound ownership ask which declaration it is
  (`CallTargetKind`); `StructDef` keeps its field names and `pub`s as two
  index-aligned lists, as `FunctionDef` keeps its parameter names. The
  diagnostics are shared too: E2016 and E2120–E2123, naming the target
  ("function `f`", "struct constructor `Point`") with a label at its
  declaration. E2086 is gone; struct patterns keep E2025–E2027 and E2088
  until they are looked at on their own, and field access keeps E2025.
- Body (since replaced: a call holds one `args` value, see "Calls"):
  `Call` and `AbstractCall` gain `order: ArgOrder`, as
  `StructConstructor` has. `args` stay in written order, which is the
  evaluation order; the permutation says which parameter each gives; a
  receiver is first and gives parameter 0. MIR evaluates in written order and
  passes in parameter order, through temporaries where the two differ.
- Implementation: `build_function_call` and `build_construction` share
  `build_arguments`, `expect_arguments` and `check_param_bounds`; a
  function's names are found through `naming_declaration`, a struct's
  through its field `lookup`. The call's type arguments are stored once and shared
  by the bound checks and the node (`TypeList::prefix` gives the impl's).
  `ArgOrder` grew `ExprKind` from 24 to 32 bytes; moving a call's fields
  into a side record would bring it back.
- Not yet: a call through a value (a local of `func(A) -> R` type, or a
  value whose type implements `Call`) is not checked in either form (E2114).
  It will be positional only, since `Call::Args` is a tuple; a named call
  there will report "a call through a value takes its arguments by position".
- Not yet: a named argument records no `Referent` (nor does a field name in
  a construction); go-to-definition and rename on `{ a: .. }` need a
  `Referent::Param` and a field counterpart, together.

### Patterns

Done. One pattern grammar serves `local` and `match` arms. Function parameters
are never patterns: a parameter is a binding (`_`, `name`, `mut name`) and a
type, see "Named calls and parameter names".

**What a term is follows from its own shape.** There is no mode to switch: a
name binds, a literal compares with that value, a qualified path compares with
that constant, and a destructure takes its children apart.

| written | what it is | why it cannot be anything else |
|---|---|---|
| `x` | a binding | a name *can* bind, so it does |
| `const x` | a constant | the one ambiguous case, marked |
| `0`, `-1`, `'a'`, `true` | a test | a literal cannot bind |
| `Ordering::Less` | a constant | a qualified path cannot bind |
| `mut x` | a mutable binding | |
| `_` | a wildcard | |
| `Point(x, 0)`, `Point({ x, .. })`, `(x, y)` | a destructure | each child is a pattern of its own |
| `A \| B` | an or-pattern | its alternatives bind the same names |

```
match point {
    Point(0, 0) -> origin(),
    Point(x, 0) -> on_x_axis(x),
    Point(const MAX, 0) -> at_the_limit(),
    Point(x, 5 | 10) -> { .. },
    (x, y) -> { .. },
    _ -> { .. },
}
```

`const` takes a path and nothing else: a literal is a comparison on its own, a
destructure has no name to mark, and a name of one segment is the only thing
the marker can mean. It binds tighter than `|`, so `const A | const B` is two
constants. Before a path that is a constant already (`const Ordering::Less`)
it is redundant, and is warned about (W1003) and dropped.

**Why a marker at all.** A single name in a pattern means one thing by syntax
alone: the marker, not name lookup, decides whether `MAX` binds or compares, so
renaming or removing a constant is an error ("cannot find value `MAX`") and
never a silent catch-all, as it is in Rust. A qualified path needs no marker
precisely because it cannot bind.

**A struct's list is one value of its fields,** as a construction gives
them, and as in Standard ML: `Point(x, y)` gives each field, `Point(p)` binds
them all as one tuple `(i32, i32)` (not the first field: that is
`Point(x, ..)`), `Point(_)` matches any point, and `Point((x, y))` is
`Point(x, y)`. A lone field whose type is a tuple takes several, so
`W(a, b)` and `W(a, ..)` match `W(x: (u8, u16))`. Nothing is regrouped:
`Outer(a, b, c)` does not match `Outer(x: (u8, u8), y: u8)`. A
`PatternKind::Struct` holds one child of the fields' tuple type, and
exhaustiveness splits a struct as that tuple (a lone field as one child). No
warning marks a lone name binding several fields; Python reads `Point(x)` as
the first field, Rust and OCaml (for an n-ary constructor) reject it.

**Refutability is syntactic.** wx enums carry no data, so destructuring a tuple
or a struct always matches, and a pattern can fail only where it holds a
literal or a constant. A `local` statement therefore takes a pattern that
holds neither: a test in one is E2115, at the test itself. A match arm takes
any pattern.

**Values are constants.** A value leaf is a literal, an enum variant, a
`const`, or an associated constant (`const u32::MAX`, `Self::LIMIT`), resolved
as a value path that never sees locals: `const y` for a local `y` is "cannot
find value `y`", with a note that a local cannot be compared in a pattern. An
untyped literal takes the type it is checked against. A struct is compared
structurally, field by field, never through `PartialEq`. An abstract constant
(`T::LIMIT`) is accepted and never counts towards exhaustiveness.

A float has no single value to compare with, and a string has no equality at
all, so neither can be matched: the parser reads them and the checker refuses
them (E2117).

**Checking flows down.** A pattern is checked against the type it is given:
the scrutinee's, or a `local`'s value (or annotation). A struct pattern names
its struct (`Point(..)`, `Self(..)`), checks field privacy as construction
does, and takes at most one `..`. Each match arm owns a scope for its bindings.

**AST** (done). One `Pattern` tree, with the leaves already resolved by the
parser: `Wildcard`, `Binding` (a name, with its `mut` span), `Constant` (a
constant, by path), `Literal` (an int — `Int` or `NegInt`, the sign being the
variant — a char, a bool, a float, a string), `Or`, `Destructure` (a tuple, a
struct, a named struct), and `Error` for a pattern the parser could not read. The leaves record what a term *is*, so no later
stage has to know a mode — `const MAX` and `MAX` are different leaves, and
`{ x }` in a named struct pattern is a binding, recorded as the field's own
name with no pattern of its own.

**TIR** (done). One pattern arena in `Body`, shared by `local` and `match`
(`PatKind`, with a type and a span per pattern, children in `pat_lists`). A
pattern is typed and resolved. The kinds group by what they do: structure
(`Wildcard`, `Bind(LocalIdx)`, `Tuple`, `Struct`) always matches; tests (`Int`,
`Bool`, `Char`, `Constant`, `AbstractConstant`, `Or`) match only some values,
so only a match arm holds them; `Error` is reported and counts as `_`.
Destructuring has one child per element or field of its type, in declaration
order: what `..` covers, and a field a named pattern leaves out, is a
`Wildcard`, so a struct's arity is its field count however it was written, and
no `ArgOrder` or rest flag survives. `Int` is the value's bits in the pattern's
type (`-1: i8` is `0xFF`), one spelling per value. `ExprKind::LocalDeclaration
{ pattern, value }` and `ExprKind::Match { scrutinee, arms }` with `Body::arms`
(`Arm { scope, pattern, body }`): each arm declares its bindings in a scope of
its own around its body. A test in a `local` is E2115, at the first test; every
test in the pattern then becomes `Error`, so the pattern takes the value apart
and binds without testing (its bindings are still declared), and only the
first test is reported. A name bound twice in the same pattern is E2116.

The alternatives of a `|` bind the same names, as in rustc. The same name in
two alternatives is *one* local, which both alternatives bind: the arm's body
reads that one local. A name one alternative binds and another does not is
E2118 (one report per name, a label on each alternative that lacks it); the
same name bound differently in two alternatives — one `mut`, one not — is
E2119; and the same name of a different type in two alternatives is E2001,
with the type it was first introduced with. Each `|` is checked on its own,
and an alternative's names are those bound anywhere inside it, so a nested `|`
counts towards the enclosing one.

A name bound twice in one alternative is E2116, and is still the local the
alternatives share: the two bindings are one variable, so they are of one
type (E2001 says so when they are not). A name bound in two *products* — two
sibling `|`s in one pattern, or a `|` and the pattern around it — is two
variables, and E2116 says so.

The two kinds of place a name can be bound are a **product** (one value taken
apart: a tuple, a struct, one alternative) and the **alternatives** of a `|`
(one value matched several ways). A name in a product names a different value
each time it is bound; a name in the alternatives names the same value, seen
two ways. That is the whole difference, and it is what decides whether a
second binding of a name is a mistake (E2116) or the same variable again
(shared). rustc splits it the same way (`PatBoundCtx::{Product, Or}` in
`rustc_resolve/src/late.rs`).

**Usefulness** (done). One pass, Maranget's "Warnings for pattern matching"
(rustc's `rustc_pattern_analysis`), in `tir/usefulness.rs` (pure: types are
asked of a `Shapes`), run by `BodyContext` once a match's arms are built
(`typecheck/exhaustiveness.rs`: lowering, `Shapes`, witnesses, reports). The question is whether a row `q`
is useful after rows `P`: does some value match `q` and no row of `P`. Arm *i*
is unreachable (W2010) when it is not useful after arms *0..i*; the match is
non-exhaustive (E2066) when `_` is still useful after every arm, with up to
three witnesses (the values no arm matches) in the report.

- Constructors: a tuple or struct is the single constructor of its type, with
  one sub-pattern per element or field; `Bool`, `Int`, `Char` and a variant (by
  its discriminant) are values; a `Constant` that `eval` reduces to a scalar or
  a variant is that value; any other constant, and `AbstractConstant`, is
  opaque; `Wildcard`, `Bind` and `Error` are wildcards; an `Or` is a row per
  alternative.
- A type's constructor set: `Single` (tuple, struct, `()`), `Bool`, an enum's
  `Variants`, `Integers { count }` (2^bits; `char`'s valid scalar values),
  `Empty` (`!`), `Unlisted` (floats, pointers, parameters: only `_` covers
  them).
- `useful(P, q)`: an empty `q` is useful when `P` has no rows. A constructor
  head `c` recurses on both specialised by `c` (rows headed by `c` replaced by
  its sub-patterns, wildcard heads by as many wildcards, others dropped, an
  opaque head dropped too). A wildcard head: when `P`'s first column covers the
  whole set, useful when it is for some `c`; else against the default rows
  (wildcard heads, removed), and a missing constructor heads the witness. An
  opaque head is useful against the default rows only.
- No range patterns yet, so a set of literals is complete only when it lists
  every value of its type (all 256 of a `u8`); the witness is the smallest
  value no arm lists.
- An opaque constant never makes a match exhaustive, nor is it unreachable
  unless a wildcard arm precedes it. `local` patterns hold no tests, so they
  always match and are not checked.
- Constants (and an enum's variants) are evaluated wherever a pattern may
  name them, a function's block or an initializer's alike. A constant whose
  value is not known — one that is still being built, one `eval` cannot
  reduce to a number — is opaque, and an enum whose variants have no value
  is unlisted; both need `_`.
- A match with an `Error` pattern, or a scrutinee whose type has an error, is
  not checked: what failed has said why.

### Pattern limitations (as of the usefulness pass)

What patterns, `match` and exhaustiveness do not do yet, or do on purpose in a
restricted way:

- **A constant's value is known wherever a pattern may name it.** A `match` in
  a constant's or global's initializer compares with the constants it names,
  as one in a function's block does. The rule was lifted once a constant's
  body could be built without looping: `const_value` calls
  `ensure_const_body` *before* it marks the constant `InProgress`, and
  `ensure_const_body` only checked whether the body exists, so two
  initializers whose patterns name each other rebuilt each other's bodies
  forever (reproduced: a stack overflow). Now a body is `NotBuilt`,
  `Building` or `Built`, and a body that is being built is not built again: a
  read of that constant's value finds none ("not known yet"), which is what
  the reader needs to know. A constant whose value is not known is opaque, and
  an enum whose variants have no value is unlisted; both need `_`.
- **`eval` folds no `match`.** `ExprKind::Match` (like `IfElse`) is not a
  constant expression, so a constant whose initializer is a `match` is E2057.
- **`|` alternatives bind the same names** (E2118, E2119, E2001); the same
  name in two alternatives is one local.
- **No range patterns.** An integer or `char` match is exhaustive only with
  `_` or every value listed; the witness is the smallest value no arm lists.
- **Opaque constants never count towards exhaustiveness:** a trait's
  constant (`T::MAX`), a constant with type arguments, a struct-valued
  constant, or one `eval` cannot reduce to one number. An enum one of whose
  variants has no value is unlisted (needs `_`).
- **A redundant alternative is not reported** (`case 1 | 1`); only whole arms
  are (W2010).
- **Non-exhaustive reports** name at most three witnesses ("and more"), one
  per missing variant; an integer gets one witness; `_` when no arm names a
  constructor of that column.
- **A match with a failed pattern** (`Error` anywhere) or an erroneous
  scrutinee type skips the usefulness pass entirely.
- **No patterns through pointers**, as there is no auto-deref: destructuring
  a `*T` is a type mismatch.
- **Struct pattern privacy** is construction's: the struct must be
  constructible here (every field visible), even with `..`.
- **Shorthand fields:** `{ mut x }` does not parse (write `{ x: mut x }`);
  `{ x }` under `case` names a constant `x`, as the mode rule says.
- **Untyped scrutinee or value:** `match 1 { .. }` and `local (a, b) = (1, 2)`
  need a type (annotation required).
- **Literals:** floats and strings are not pattern literals.
- **A test in a `local`** (E2115) turns each test into `Error`; the pattern
  still takes the value apart, and its bindings are still declared.
- **Parse recovery:** a `local` marker in a pattern is E1015, and the pattern
  is read as broken.
- **`!` scrutinee:** zero arms are exhaustive, and any arm there is reported
  unreachable.
- **Dead nodes:** a failed value path (`resolve_value_path` returning an error
  node) and the inner pattern of a reported `case` in a `local` leave nodes in
  the arenas that nothing references, as an extra call argument already does.
- **Not done elsewhere:** MIR lowering of patterns and `match` (MIR is
  disabled); the Zed grammar does not know `case`; wx-fmt's printing of a
  comment between a dropped redundant marker and its pattern is unverified.

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
  `are_scalar_compatible`, and close the `&T as *T` hole while at it. Done, then
  removed (2026-10-29): ascription gives a value its type and std's `transmute`
  reinterprets one.
- **Function items as values** and their coercion to `func(A) -> R`.

After step 1 most stdlib bodies type-check: they are intrinsic calls, `if`,
`self` and operators.

### 2. Moderate (needs a small design decision, listed in the section)

- **Type-relative paths** (functions done): `Ordering::of`, `Self::f`, `T::f`,
  `W::<u8>::new`, `<T>::f` and `<T as Tr>::f` (`typecheck/members.rs`). A value
  path starting at a type parameter or `Self` names a type from its first
  segment; any other walks the namespace graph and continues past the type it
  stops at (an enum is such a stop for a name it does not bind). The member is
  found by `resolve_applicable_member` (or the named trait alone), and becomes
  a `Callee`: the function, its leading type arguments (the impl's, from
  `match_impl_target` or `find_trait_impl`; `[Self]` for a trait's
  declaration) and whether it is reached directly or abstractly. The call then
  learns the function's own arguments as any call does. An inherent member is
  as visible as written, a trait's member as the trait.
  A generic struct named without its arguments (`Layout::of::<T>()`) is the
  receiver `Layout<_>`: the call's flat list is the impl's slots, `INFER`
  where the receiver does not say, then the method's own. The inherent impl is
  chosen by shape: its slots are learned from the receiver, and it is a
  candidate when its instantiated target still meets the receiver (a type's
  inherent impls declare a name once, so there is at most one). Its bounds
  wait for the call (`Callee::impl_bounds`), which proves them after learning
  from the expected type and the arguments, as it does the function's own.
  Trait members are not looked up on such a receiver yet.
- **Associated constants** (done): selected like functions, and read as the
  same pair the calls have: `Const { constant, type_args }` for a known
  constant (free, a variant, an inherent impl's or the one a concrete trait
  impl defines, with the impl's arguments) and `AbstractConst { constant,
  type_args: [Self] }` for a trait's declaration. Its type is the declared one
  with those arguments substituted. Constant evaluation reads only a `Const`
  without arguments; an impl's constant that depends on the impl's arguments,
  and an abstract one, are not evaluated yet.
- **`Self` as a value** (done): inside an impl whose target is a struct,
  `Self(..)` and `Self({ .. })` construct it with the target's arguments
  (`impl<Mem> Layout<Mem>` builds `Layout<Mem>`), checked where every field is
  visible like any construction. Bare `Self` is a struct used as a value
  (E2110). In a trait's default body, outside an impl, or for a target that is
  not a struct, `Self` names nothing to construct (E2009).
- **Method calls** `x.m(..)` (done): the same `Callee`, the checked receiver
  its first argument, learned from like any argument. Only a member taking
  `self` is a method. No auto-deref: a pointer receiver finds the pointee's
  methods that take `self` by pointer (`self: M::*Self`), and is itself
  `self`; a by-value method through a pointer is reported, pointing at `.*`.
  An untyped receiver (`(1).add(2)`) needs an annotation. Calls by name:
  see "Named calls and parameter names".
- **`loop`/`break`/`continue`/labels**: `Break`/`Continue` naming their scope. Decision: whether a
  loop without any valued `break` is `!` (old behaviour; yes).
- **Assignment and compound assignment**: the place arena, mutability checks.
  Globals are handles, written through `GlobalMut::set` (Q2).
- **Field access** `x.y` on a value and through a place. Field privacy is
  enforced here (the old checker did, for all three sites).
- **Patterns** (designed, see "Patterns"), in this order: the parser, the pattern
  arena, `local` destructuring, `match` and the usefulness pass (done).
- **Named calls** (done, see "Named calls and parameter names"): the
  parameter and field grammar, then calls by name. The check that a trait
  impl's parameters use the trait's names belongs to conformance.

### 3. Think first

- **Pointers and memory**: array literals and repeats (static data), indexing,
  slice ranges. There is no ambient memory: a pointer type always names its
  memory (`heap::*T`, `Mem::*T`; an untagged one is `PointerWithoutMemory`,
  E2038), and the compiler never picks one from how many are declared. A
  literal that becomes static data takes its type, and so its memory, from its
  context; without one it needs an annotation. A static-data story for MIR is
  still open.
- **String literals** (done): `ExprKind::String(SymbolU32)` holds the
  unescaped contents (`literals::unescape_string_literal`, interned through
  `TypeContext::strings`, which is `&mut`). Like a number, a string literal is
  untyped (`Type::String`, `HAS_UNTYPED`) until its context gives it a type,
  and `coerce` accepts a shared byte slice `M::&[u8]` or a shared byte array of
  exactly its length `M::&[u8; N]`, in any memory, abstract ones included. So
  it can wait for a generic call to learn its memory (`take("abc", p)`).
  Exclusive targets are rejected (the data is read-only), a wrong length is
  `ArraySizeMismatch`, operators on an untyped string are reported, and a cast
  accepts what coercion would. Constant evaluation gives `NotConst` until
  static data is designed. Open: `heap::&[u8; _]`, inferring the length.
- **Calls through `Call`** for non-function values (Q3), and whether
  `Callee::Indirect` is a separate path or `Call::call` on `FunctionRef`.
- **Method-call privacy**, which the old checker never enforced (CLAUDE.md
  pitfall). New code can do it from the start since impl members carry
  visibility; decide the rule for trait default methods (fall back to the
  trait's visibility).
- **Impl conformance** is not a body concern, but `AbstractCall` to a
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
  `g = x` and `g op= x` are invalid assignment targets. The global's impls
  declare no members, so `g.get()` is an `AbstractCall` of `Global::get` with
  the global as `Self`, which MIR lowers to `global.get`.
- **Q3. Calls through `Call`.** Done (`build_value_call`): a value is called by
  its type, as a call of `Call::call` with the value as `self` (`g(a, b)` is
  `g.call((a, b))`), so a computed callee (`make()(1)`) is evaluated like any
  receiver. A function item (zero-sized, `id<u8>`) selects the trait's
  declaration over itself (its impl is its own, whose requirements are its
  bounds, proven where it was named); its arguments are its function's, by
  position or by name, packed into `Args` by a `Tuple` with an `order`, which
  evaluates them as written and places them by parameter. There is no
  implicit conversion to `func(A) -> R`.
  A function reference `func(A) -> R` implements `Call` by a compiler rule
  (`TraitImplLookup::Builtin`; `Args` is `A`, `Result` is `R`) and its call is
  `ExprKind::CallRef`, which lowers to `call_ref`, not `call_indirect` (that
  is for table handles). Any other type is a `Call` of its impl's `call`, or
  an `AbstractCall` for an abstract `F: Call`, by position, with the
  arguments forming `Args` as a parameter list forms a function type. A type
  is never called as a value: a struct's name constructs it. Not yet:
  constant values of item type (`eval`).
  Every call follows one rule for its positional arguments
  (`positional_arguments`): the list is one value of the parameters it
  fills, and nothing is regrouped. When it fills one, the whole list is its
  value, `()` for none and a tuple for several (`whole_argument_list`); one
  value for several is their tuple (`one_value_for_all`, `f(p)`); otherwise
  each gives one parameter. So `g(a, b)` is `g((a, b))` for `g(p: (A, B))`, a
  lone generic parameter learns the tuple, a receiver fills its parameter
  first (`x.m(a, b)`, `x.m(p)`; `T::m(x, p)` is a wrong count), a lone
  value that is no tuple for several parameters is a wrong count (`f(a)`
  missing `b`), and so is a known lone parameter type that is no such tuple.
  `arguments_value` turns what was given into the node's one `args`. `Args`
  of a value is that one parameter, so the value calls agree.
- **Q4. Operator nodes.** Decided: one node per way an operation is defined
  (`Primitive`/`Concrete`/`Abstract`) and per destination (value, `Assign`, `Store`);
  see the table under places and assignment.
- **Q5. Typeset-abstract literal arithmetic in bodies.** Coercion of literals
  to an abstract typeset-bounded `T` exists for constants; in a body, an operator
  on `T` gives an `AbstractCall`. Is anything beyond that expected (for
  example `as` casts between typeset members)?
