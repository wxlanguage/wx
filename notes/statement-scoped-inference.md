# Statement-scoped inference: inference variables within one statement

Status: proposal, not implemented. Changes the answer to Q1 in
`tir-body-checking-plan.md` from "inference is local to one call" to
"inference is local to one statement". The rule that a body's inference ends
at each `;`, with no inference from later uses and no literal defaulting, is
kept: only the unit inside the statement grows.

## The problem

Type arguments are inferred inside one call today. `build_function_call`
holds them in a local `Vec<TypeIndex>`, `INFER` where unknown, learns from the
expected result and then from the arguments, and `settle_uninferred` turns
what is left into `ERROR` with E2002 before the call returns. Information
flows down (the expected type) and up from a call's own arguments, never back
into a call that has returned.

```wx
bump.set(RawPtr::from_addr(new_end).as_ptr());            // works (one level)
bump.set(RawPtr::from_addr(new_end).add(1).as_ptr());     // E2002 on `from_addr`
```

The first works only by a special case (`receiver_expectation`, `ReceiverOf`):
a path call's callee is known from syntax, so its shape `RawPtr<_, _>` exists
before it is built, and the method above it can turn its own expected type
into one for the receiver. The second cannot work in one pass. `add` is
selected by its receiver's type, so `from_addr` is built, and settled, before
`add` exists; what `as_ptr` learns from `heap::*u8` would have to go up the
chain and come back down into a node that is already finished:

```
from_addr shape -> select add -> add shape -> select as_ptr
    -> learn from heap::*u8 -> back into add -> back into from_addr
```

The same wall appears without methods, wherever two calls share an unknown
through a third:

```wx
func pair<T>(a: W<T>, b: W<T>) -> (W<T>, W<T>) { .. }
pair(W::empty(), W::new(5: u8));   // `W::empty()` settles before `b` is seen
```

## The model

A call no longer settles. An argument it cannot learn becomes an **inference
variable**, a type that is unknown now and may be decided later in the same
statement. Everything that later meets a type with a variable in it
**unifies**, binding the variable. At the end of the statement every variable
must be bound: what is left is E2002, reported where the variable was made,
with the same message as today ("cannot infer type for type parameter
`Mem`"). Then the statement's nodes are rewritten with the bound types
(*writeback*), so nothing after the `;` ever sees a variable.

**One pass, no fixpoint.** Variables are bound only where two types meet
structurally, on the spot, as the statement is built top-down. A check that
must wait for a variable (an equality through a projection over it, a literal
against such a projection, `StackValue`) is a **check, never a teacher**: it
is decided once, at the `;`, after every variable is bound or reported, and it
binds nothing. So the settle at the `;` is a fixed sequence (report, write
back, decide the queue in order) and never runs anything twice.

The price is one rule a user can see: **a projection over a variable teaches
nothing.** In `RawPtr::from_addr(make())` with `make<U>() -> U`, `?U` meets
`<?0 as Memory>::Size`, which is not a structural match, so `?U` is E2002
even if `?0` is bound later in the statement; `make::<u32>()` is the
spelling. This is the same direction as "no implied bounds through
equalities": `<?0 as Memory>::Size == u32` never binds `?0` either. Stated
for users: *inference learns from what lines up structurally, as it is
written; everything else is checked at the `;`.*

Under this model, the example above runs like this:

| step | node | what happens |
| ---- | ---- | ------------ |
| 1 | `RawPtr::from_addr(n)` | args `[?0, ?1]`; `n: u32` against `<?0 as Memory>::Size` cannot be normalized yet, a **queued check**; type `RawPtr<?0, ?1>` |
| 2 | `.add(1)` | `add` selected by shape on `RawPtr<_, _>`; impl args unify with the receiver, `?2 = ?0`, `?3 = ?1`; `1` against `<?0 as Memory>::Size`, a **pending literal**; type `RawPtr<?0, ?1>` |
| 3 | `.as_ptr()` | type `?0::*?1`; unified with the expected `heap::*u8`: `?0 = heap`, `?1 = u8` |
| 4 | `;` | every variable is bound, so nothing to report; writeback; the queue, in order: `u32 == <heap as Memory>::Size` holds, `1` becomes `u32`; the recorded bounds (`heap: Memory`, `u32: Add`, `u8: StackValue`) are decided at the body's end as today |

Nothing is checked twice, and no node is rebuilt: every check either happens
on the spot (no variable involved), or waits in the statement's queue for its
variables.

### Inference variables

- A new type variant, `Type::Var(VarIdx)`, with `HAS_INFER`. `INFER` (slot 0)
  stays what it is today: "nothing is expected" in an expectation. A variable
  is a specific unknown that two places can share; `INFER` never is.
- An `InferenceTable` on `BodyContext`: a union-find over `VarIdx`, each root
  holding `Unbound` or `Bound(TypeIndex)`, plus each variable's origin (the
  span and the parameter name that E2002 needs) and its level (below).
- `resolve(ty)` replaces each bound variable by its value, deeply, and is
  what every site that reads a type's structure calls first (rustc's
  `resolve_vars_if_possible` / `shallow_resolve`).
- `unify(a, b)` replaces `learn` for value positions: structural, binds a
  variable to the other side (occurs check: binding `?0` to `W<?0>` is a
  mismatch), and fails where the shapes differ. A failure is not reported by
  `unify` itself; `expect` reports it as a mismatch, exactly where
  `TypeEquality::Diff` reports it today.
- Variables are interned in the global `TypeInterner` like any type. The
  interner may keep `RawPtr<?0, ?1>` forever; that is harmless, since the
  invariant is about what the *body* holds, not what the interner holds.

### Where variables are made

Wherever an `INFER` is left today and settled:

- a call's type arguments (`build_function_call`, `build_function_value`)
  that are still unknown after learning from the expected type: a fresh
  variable per slot, not an `ERROR`;
- a construction's (`build_construction`);
- a written `_` in a type (`local x: W<_> = ..`, `id::<_>(x)`), which gets
  the same meaning for free: a variable the statement must decide;
- an array length `_` (`[v; _]`), today an `INFER` that a literal fills.

The order of learning stays: the expected result first, then the arguments.
With unification the result is the same either way, but the order decides
which side a mismatch is blamed on, and today's messages blame the argument.

### Where variables are decided: the end of a statement

A statement's variables are settled at its `;`, and also where a statement
ends without one: a block's tail, an arm's value, `return`'s and `break`'s
value, a `local`'s initializer. A local's type must be free of variables when
the `local` statement ends, so

```wx
local w = W::empty();   // E2002 here, as today
w.push(5: u8);          // does not teach `w`'s type: no inference from later uses
```

is unchanged. That is the rule from the statement-scoped inference decision,
and it is what keeps a body's inference local enough to report in place.

**Nested statements.** A block-like expression inside a statement holds
statements of its own:

```wx
local x: W<_> = block { f(); W::empty() };
```

`f();` ends before the outer `local` does. Settling at an inner `;` must not
report a variable that belongs to the outer statement (here, the `_`, which
`block`'s tail `W::empty()` unifies with). This is level-based, as in ML's
let-generalization (Rémy's levels):

- each variable is made at the current statement depth, its level;
- unifying two variables gives the root the lower level, and binding a
  variable to a type lowers the levels of the variables inside it;
- at a `;` at depth `d`, the unbound variables at level `d` are E2002; those
  at a lower level belong to an enclosing statement and stay open.

The variables made by the inner statement that were never connected to the
outer one are settled at the inner `;`, as they would be today.

### What waits, and what may not wait

Every place the checker reads a type and acts on it now has three choices:
resolve and continue (no variable left in the part it reads), **wait** (queue
it until the variables are bound), or **require** the type to be known enough
right now (rustc's `structurally_resolve_type`, E0282) and report E2002 if it
is not.

| site | today | with variables |
| ---- | ----- | -------------- |
| argument and value checks (`expect`, `equality`) | on the spot | unify where the two types line up structurally; an equality that must normalize a projection over a variable (`u32 == <?0 as Memory>::Size`) **waits** as a check that binds nothing, as `ExprObligation::Equal` already waits for values (`NeedsValues`) |
| untyped literal against a type with variables | `coerce` on the spot | **waits** (a pending coercion); decided once the target is known |
| bounds of a use (`check_use_bounds`) | recorded, decided at the body's end (`decide`) | unchanged: already deferred. Writeback rewrites their `GenericArgs` in place, so they never see a variable |
| `require_stack_value` | on the spot | **waits** when the type has variables |
| method call | selects on the receiver's type | selects on the receiver's **head**: an inherent impl by shape (`select_inherent_with_holes`, which already exists); a trait member by its head too (below). A receiver whose head is itself a variable (`id(x).m()` with `id`'s `T` unknown) is **required**: E2002 now |
| field access, `.*`, `.&`, indexing | reads the type | the head must be known (**required**); the parts may be variables (`make().field` is `W<?0>`'s field instantiated with `?0`) |
| operators | primitive or trait method by operand type | the head must be known (**required**); `?0 + 1` is E2002 |
| `match` scrutinee, patterns, exhaustiveness | reads the type | **required** at the `match`; usefulness is already decided at the end (`ExprObligation::Match`) |
| call of a value (`v(a)`) | `Call` by type | **required**: the callee's type must be known to pick `CallRef` or `Call::call` |

A **required** site that fails reports E2002 for the variable it met, the
same diagnostic it would get at the `;`, only earlier. The table is the real
cost of the change: every site in `typecheck/` that matches on
`self.cx.types.resolve(ty)` must say which of the three it is.

### Trait members on a receiver with variables

Today a member is looked up on a receiver with holes only among inherent
impls ("Trait members are not looked up on such a receiver yet"). With
variables, the **one impl per trait per type constructor** rule
(`single-trait-impl-per-constructor-plan.md`) makes a trait member selectable
by the head alone: `W<?0>` has at most one impl of `Tr`, whatever `?0` turns
out to be, so the impl is chosen now, its arguments unified with the
receiver's, and its requirements recorded like any other bound. This is a
consequence of that coherence rule that Rust cannot use, since Rust allows
`impl Tr for W<u8>` beside `impl Tr for W<u16>`, so it has to wait for `?0`.

### The solver never sees a variable

The solver's queries are pure and their answers are cached across bodies
(`Normalization`, `verdicts`, `instance_values`). A variable means something
only inside one statement of one body, so:

- a query over a type with `HAS_INFER` returns `SolverError::Pending`, the
  existing answer for "a fact here is not final", and is never cached; that
  is the existing rule ("any path that reads a non-final fact must return
  `Pending`, which is what keeps the cache valid");
- the caller queues what it was doing (the "waits" rows above) as a check,
  decided once at the `;`.

So the solver is not changed: it already has the answer this needs.

### Settling a statement

At the end of a statement, in this order, each step once:

1. **Report.** Each unbound variable at this level: E2002 at its origin, once
   per variable (union-find root), then bound to `ERROR`, which silences
   whatever was waiting on it. That keeps today's poisoning: one missing
   annotation is one diagnostic.
2. **Writeback.** Rewrite every type the statement produced with `resolve`.
   The body is push-only, so that is a range per column: the nodes
   `ExprIdx` from the statement's start (`Body::ty`), the `GenericArgs`
   pushed since (the call nodes' type arguments and the recorded bound
   checks'), the locals, places and patterns the statement declared, and the
   queued checks themselves. A debug assertion afterwards: nothing in those
   ranges has `HAS_INFER`.
3. **Decide the queue,** in the order it was recorded. Every entry is now
   free of variables, so each is one of today's on-the-spot checks (an
   equality, a coercion, a `StackValue` requirement), run late. None can
   bind a variable: there are none left.

Lowering already must never see `INFER`; it must never see a variable either,
and writeback is what guarantees it.

## What it replaces

- `receiver_expectation`, `ReceiverOf` and `Expected` (`typecheck/members.rs`):
  a receiver is built with no expectation again, comes back as
  `RawPtr<?0, ?1>`, and the method unifies. Chains of any depth fall out.
- `settle_uninferred` per call: replaced by the per-statement settle.
- `learn`, for value positions: replaced by `unify`. `learn` stays where it
  matches a pattern against a type that has no variables (impl targets in
  `select_inherent_with_holes`, `match_impl_target`).
- `INFER` as "a type argument not known yet": only "no expectation" is left.

## What it costs

Code where every call learns its arguments, which is most code, pays almost
nothing at run time: a flag check per stored type and per structural read.
The real cost is the engineering below.

### Time

There is **no additional walk over the expression tree.** `Body` is
struct-of-arrays and push-only, a node's children are pushed before it, and
no `ExprKind` holds a `TypeIndex` of its own. So everything one statement
produced is a contiguous range of a few flat columns, from their lengths at
the statement's start to their lengths at its `;`:

| column | holds |
| ------ | ----- |
| `Body::types` | each node's type |
| `Body::pat_types` | each pattern's type |
| `Body::locals[..].ty` | the locals the statement declared |
| `Body::places[..].ty`, `.memory` | the places it built |
| `cx.generic_args` (`GenericArgArena::types`) | call nodes' and recorded bound checks' type arguments; push-only as well |
| the statement's queue | the types its checks hold |

- **Writeback** is a loop over those slices. Each `TypeIndex` is tested for
  `HAS_INFER`, a flag `TypeInterner::insert` already computes, so one lookup
  and no walk; only a type with a variable in it is resolved, and that walks
  the *type* (as `substitute` does), never the expression. A statement with
  no variable rewrites nothing.
- **Nested statements** are rescanned: the outer `;` scans the range that
  holds the inner statements too, so a node is scanned once per enclosing
  statement, bounded by the nesting depth. A statement inside an expression
  inside a statement is rare. If it ever shows, a *dirty list* (each slot
  stored with a variable, recorded as it is stored) makes writeback
  proportional to the variables instead of the statement, for more
  bookkeeping; ranges come first.
- **Unify** replaces `learn`, which already walks the declared type beside
  the actual one: the same walk, plus a union-find lookup at a variable
  (near O(1) with path compression).
- **Resolving at a structural read** (method selection, fields, operators,
  `match`) is a `HAS_INFER` test, free when false, and a lookup of the head
  when true: those sites need only the head.
- **The solver** tests `HAS_INFER` once at entry and answers `Pending`
  without touching a cache.
- **Queued checks** are equalities, coercions and `StackValue` requirements
  that run today anyway, at the `;` instead of on the spot: moved, not added.
- **Settling** is three linear passes, each once: the variables made at this
  level, the writeback ranges, the queue.

It also removes work: today's receiver probe searches a receiver's inherent
impls twice (`inherent_candidates_with_holes` in `receiver_expectation`, then
again in `select_member`), and the model selects once.

### Memory

- **`Type::Var(VarIdx)`** has a `u32` payload; `Type` does not grow.
- **The inference table**, one per body, its `Vec`s cleared at each
  outermost `;` and their capacity reused, so nothing is allocated after the
  first few statements. Per variable, about 28 bytes:

  | field | bytes |
  | ----- | ----- |
  | union-find parent | 4 |
  | binding (`TypeIndex`, a reserved value for unbound) | 4 |
  | level | 4 |
  | origin: span | 8 |
  | origin: the parameter's frame and slot (E2002 names it) | 8 |

  A variable is made only for a type argument a call could not learn,
  typically none to four in a statement.
- **The queue**: one entry per check that met a variable, 12 to 16 bytes (a
  kind, an `ExprIdx`, one or two `TypeIndex`es), cleared per statement.
- **Statement marks**: per open statement, the start length of each column
  above, six `u32`s, on a stack as deep as the nesting.
- **The finished body stores nothing new.** After writeback no variable is
  left, so `Body` keeps its layout and size, and lowering, MIR and codegen see
  what they see today.
- **The interner grows a little.** Types with variables (`RawPtr<?0, ?1>`,
  `?0::*?1`) are interned and never freed. Variable numbering restarts at 0
  at each outermost statement, so the same shapes are the same entries for
  the whole compilation: growth is bounded by the distinct shapes, not by
  the number of statements.

### Engineering

- **Every type-reading site must be classified** (the table). This is the
  bulk of the work and the main source of bugs: a site that reads a variable
  as if it were a final type silently does the wrong thing. A debug assertion
  in the solver's entry points that the input has no unresolved variable
  catches the ones that reach it.
- **Diagnostic order.** E2002 and waited mismatches are reported at the `;`,
  after diagnostics from later in the statement. Sort a statement's
  diagnostics by span before pushing, or accept the order.
- **A second representation of "unknown".** Literal pseudo-types
  (`CONST_INT`, `CONST_FLOAT`, `CONST_CHAR`) already are
  variables in all but name: they wait for context and are rewritten in
  place. They could become variables with a kind (rustc's `IntVar`/`FloatVar`)
  so there is one mechanism. That is optional and can come later; the
  pending-coercion row covers the interaction meanwhile.
- **Constant bodies.** They are built value-free and defer what needs a value
  (`DeferredCheck`). The two deferrals are layered: a statement settles its
  variables first, and only then records what needs values, so a
  `DeferredCheck` never holds a variable.

## Migration

Each step leaves the suite passing:

1. `Type::Var`, `InferenceTable`, `unify`, `resolve`, writeback. Calls make
   variables instead of `INFER` but still settle at the call's end, so the
   behaviour is unchanged and the new machinery is exercised by every test.
2. The solver's `Pending` for `HAS_INFER` inputs, and the queue of checks for
   the "waits" sites. Still settled per call.
3. Move the settle point to the statement, with levels. `receiver_expectation`
   becomes dead; remove it. `pair(W::empty(), W::new(5: u8))` and the
   two-level chain start to check.
4. Classify the "required" sites, each with a test that the E2002 comes from
   the site and not from the `;`.
5. Trait members by head on a receiver with variables.
6. A written `_` in types.

## Tests that pin the model

- a chain of method calls learning from the expected type at its end;
- two arguments sharing a variable through the callee (`pair`);
- `local w = W::empty();` stays E2002; a later use teaches nothing;
- an inner statement in a `block` does not report an outer variable, and
  does report its own;
- `id(x).m()` with `T` unknown: E2002 at the method call, not a "no member";
- a projection equality over a variable waits (`from_addr(n)` with
  `n: u32`), and fails at the `;` when the bound memory's `Size` is not `u32`;
- a projection over a variable teaches nothing: `from_addr(make())` with
  `make<U>() -> U` is E2002 on `U`, even though `Mem` is bound later;
- a literal argument against a variable's projection (`add(1)`) gets its type
  at the `;` and is checked for representability then;
- one E2002 per variable, however many sites waited on it;
- no type with `HAS_INFER` in a finished body (debug assertion over every
  test).
