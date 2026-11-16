# Loops: the block/loop model and loop-scoped bindings

Status: 2026-11-16. Decided and implemented: the model (a `loop` is a fused
Wasm `block` + `loop`); the jump targets (an unlabelled `break` leaves the
nearest written `block` or loop, `continue` restarts the nearest loop); and a
loop's parameters (`loop (i: u32 = 0, total = n) { .. }`, each iteration
entered with the next state, given by the body's value or `continue`'s,
positionally or by name), lowered to Wasm loop parameters. Revised the same
day: each parameter takes its own initial value, in place of one initializer
for the whole state (`loop (i, total) = (0, n)`). Open: whether `while` takes
parameters.

## Problem

State a loop needs is declared outside it, and outlives it:

```wx
local mut next: u32 = 0;
local mut start: u32 = 0;
local mut at: u32 = 0;
loop {
    if at == text.len() { break };
    ..
    at += 1;
}
// `next`, `start` and `at` are still in scope here
```

Scoping it to the loop today takes a wrapper, `block { local ..; loop { .. } }`.
A `local` inside the loop body does not work: the body runs again on every
iteration, and the `local` with it.

A second, smaller oddity: `loop { break 0 }` compiles and `block { break 0 }`
does not (E2012), since an unlabelled `break` only leaves a loop
(`jump_target` in `tir/typecheck/blocks.rs`). "Decision: what a jump targets"
settles it.

## The model

Wasm has three label-opening constructs and one jump. `br` to a `block` (or an
`if`) jumps forward to its `end`, carrying the block's result; `br` to a `loop`
jumps back to its start. A Wasm `loop` does not repeat by itself: falling off
its end leaves it. Labels are depths, and every construct is one.

WX keeps two constructs and fuses the common shape:

- A **`block`** has one target, its exit: a Wasm `block`.
- A **`loop`** has two: its exit (an outer Wasm `block`, which `break` leaves
  with the loop's value) and its start (a Wasm `loop`, which `continue`
  restarts), and repeats at the end of its body (`br 0`).

```wx
func find(n: u32) -> u32 {
    local mut i: u32 = 0;
    loop {
        if i == n { break i * 2 };
        i += 1;
    }
}
```

```wat
block            ;; @1  `break` leaves this, with the loop's value
  loop           ;; @2  `continue` restarts this
    ...
    if
      br 2       ;; break
    end
    ...
    br 0         ;; the repeat
  end
  unreachable
end
```

That is what `wx build` emits today; MIR already holds the fused form (one
`mir::ExprKind::Loop { label }` that both `Break` and `Continue` name, built in
`tir/lower.rs`), and codegen expands it.

The model is transparent through a fixed expansion rather than one-to-one
syntax: each construct is one known Wasm shape, stated in a line. What it
costs: one WX label is two Wasm labels, so source nesting and `br` depths
differ; a loop that never breaks keeps an outer `block` that only the optimizer
could drop.

Every further loop kind is the same two targets with the exit test elsewhere:
`while c { body }` is `loop { if !c { break }; body }`, a `for` over a slice the
same with a hidden counter. `break` and `continue` mean the same in all of them.

## Decision: what a jump targets

`break` is a forward jump and `continue` a backward one, as `br` to a Wasm
`block` and `br` to a Wasm `loop` are:

- **An unlabelled `break` leaves the nearest written `block` or loop**, with its
  value. Both are forward targets: a `block` is a Wasm `block`, and a loop's
  exit is the outer Wasm `block` of its expansion.
- **An unlabelled `continue` restarts the nearest loop**, the only backward
  target.
- **A label names a target past a nearer one**: a `block`'s, to leave it from
  inside a loop; a loop's, to leave or restart it from inside a `block` or an
  inner loop. A `continue` naming a `block` stays E2012.

**Only a written `block { .. }` is a target.** The braces a construct owns are
not: an `if`'s and an `else`'s, a match arm's `{ .. }`, and a function's body.
In Wasm an `if` is a forward target too;
WX keeps it out, as it already refuses a label on an `if` (E1025), so
`loop { if c { break } }` leaves the loop. A `block` is something written to be
left (or to scope locals), never a side effect of another construct.

```wx
local x: u32 = block {
    if ready() { break 1 };   // leaves the block, with 1
    2
};

loop {
    if done() { break };      // leaves the loop: an `if` is not a target
    block {
        local t = next();
        if t == 0 { break };  // leaves the block, not the loop
        use(t);
    }
}
```

The second `break` is the cost of the rule: a `block` written only to scope a
temporary inside a loop body captures the unlabelled `break`s in it, silently.
Leaving the loop from there takes its label (`loop :l { block { .. break :l
.. } }`). The case is narrower than in Rust, where every `{}` is a block: in WX
a scoping `block` is the only way to get one, and a loop's state removes the
main reason to write one in a loop (state that outlives an iteration),
while a `local` in a loop body is already fresh each iteration.

Rejected: Rust's rule (an unlabelled `break` leaves only a loop, a `block` only
by name), which makes `block { break v }` an error for no reason Wasm has; and
requiring a name on a `block` inside a loop, a rule a sentence longer whose
only gain is the case above.

The AST says whether `block` was written. `Expression::Block` is only a
written `block`; an `else` and a match arm hold an `ast::Branch`, the
construct's own braces (`Branch::Block`) or an expression
(`Branch::Expression`: an arm's `=> x`, an `else if`, or a written
`A => block { .. }`). TIR gives a written `block` `ScopeKind::Block` and
every construct's braces `ScopeKind::Body`, and `jump_target` reads the kind.
Before this, all three were `Expression::Block` and wx-fmt printed an arm's
`block` without its keyword, dropping its label; it keeps both now.

## Decision: a loop has parameters, given each iteration

A loop may declare parameters after its label. Each iteration is entered with
a value for them, its state: the first from their initial values, every next
one from the body.

```wx
loop :label (a: A = x, b = y, mut c: C = z) { body }
```

- **The header is a parameter list**, in parentheses, written as a
  function's is, each parameter followed by `= value`. A parameter is `name`
  or `mut name` with an optional `: T` (`notes/binders.md`, "A slot's type may
  be left to inference"). No destructuring and no `_`: every part of the state
  has a name. `loop () { .. }` is a loop without parameters, as is
  `loop { .. }`, and wx-fmt prints it so. The label is optional.
- **Each initial value is checked as a `local`'s value is.** It is held to the
  parameter's written type, and a parameter without one takes the value's
  type, which must be known (E2002 for an untyped literal, as `local i = 0;`).
- **The initial values are evaluated once, before the first iteration**, left
  to right, outside the loop: they see neither the parameters nor the loop's
  label (`loop (i: u32 = i + 1)` reads an outer `i`).
- **The state's type** is the tuple of the parameters' types, one parameter's
  type for one parameter, `()` for none. It is fixed by the header.
- **The body's value is the next state.** Falling off the end of the body
  starts the next iteration with the body's result; `continue v` starts it
  with `v`. Either way the whole state is given.
- **The parameters hold the current state for one iteration.** They are
  immutable unless `mut`, which lets the body assign them within the
  iteration; the next iteration still takes its state from the body's value,
  never from what a parameter was left holding.
- **`break` leaves the loop**, with the loop's value, as without parameters.
  The state is not the loop's value; to hand it out, `break` it.
- **Their scope is the loop's body**, and nothing after it.

A loop without parameters is the case of the state `()`: its result is `()`,
and a bare `continue` is `continue ()`.

Each iteration is entered like a call of the body, with the header as its
parameters: the initial values are the arguments of the first call, and the
body's result and `continue`'s value those of each next one. Writing each
initial value beside its parameter keeps a name, its type and where it starts
together, as `local i: u32 = 0` does, instead of matching a header's
positions against a separate tuple.

### Giving the next state

The next state is a whole value, given in one of two forms, as a call's
arguments are:

- **Positionally**, as a value of the state's type: `(i + 1, total + x)`, or
  `i + 1` for one parameter (a one-element tuple is its element).
- **By name**, as a named list: `({ i: i + 1, total: total + x })`, with the
  shorthand `({ i: i + 1, total })` for a value handed on unchanged. Each name
  is a parameter of the loop.

The named form follows the rules of a call by name, with the same
diagnostics: every name is required (E2122 for a missing one), an unknown name
is E2120, a repeated one E2121, and the two forms do not mix in one list
(E1018). Leaving a name out does not keep its value: forgetting to advance a
counter is an error, not a silent infinite loop. A call by name and a named
state share their matching (`match_names` in `tir/typecheck/calls.rs`).

All of the next state is computed before any parameter takes it, so the
update is simultaneous: `(b, a + b)` reads the old `a` and `b`.

### `({ .. })`: parsed anywhere, meaningful only written directly

A parenthesized list that starts with `{` is a named list, and the parser
accepts it wherever an expression can start. It has no type of its own: tuple
types have no names, so no expected type can say what its names mean. The
checker gives its names a meaning only where it is written directly as a
loop's next state:

- the body's result, and
- `continue`'s value, naming that loop (or the nearest one).

Anywhere else it is E2144, with its values still checked. That includes a
named list in a branch of an `if` or `match` that is the body's result, and
one in parentheses (`(({ .. }))`, a one-element tuple). A branch gives the
state by name with `continue`:

```wx
match arr[mid].cmp(target) {
    Ordering::Less => continue ({ low: mid + 1, high }),
    Ordering::Greater => continue ({ low, high: mid }),
    Ordering::Equal => return (True, mid),
}
```

Letting the names flow through branches as the expected type does would take
a context carried beside every expected type, for this one use. If the type
system gains types that carry names, a named list could be checked against
them like any value, and this restriction would fall away.

### Parsing

The parser reads an optional label, then a parameter list if the next token
is not `{`, then the block. Each parameter is read with the parameter list's
own slot parser (`parse_binding_and_type`, the same recovery), then `=` and
its initial value; a missing one is reported (E1010) and kept as an error
node. `continue` takes an optional value after its optional label, as `break`
does.

The AST's `LoopHeader` holds two lists, the parameters (a
`List<FunctionParam>`) and their initial values (a `List<ExprId>`), in the
stores that already hold those kinds, one initial value per parameter. An
empty `()` is no header.

### Checking

The initial values are built in the scope around the loop, then the
parameters are declared, all together, as the loop scope's locals, with their
completed types. The first state is the initial values as one value (a tuple
of them, or the lone one), `ExprKind::Loop`'s `entry`. The state's type is
stored with the loop's scope while its body is checked, for the body's result
and each `continue`. A repeated parameter name is E2097, as in a function, and
the name finds the first.

### Wasm

A Wasm `loop` is a block whose type is a function type, `[params] -> []`, and
a `br` to it carries values for its parameters. A loop's state maps onto that:

- MIR's `Loop` carries its signature, its entry value, and the first of its
  parameter locals; `Continue` carries the next state. Each iteration starts
  by setting the Wasm parameters into those locals, which the body reads; a
  parameter, `mut` or not, is a local like any other.
- The optimizer treats them as locals the loop writes: they are its header's
  first columns. It emits every demanded header column, a parameter's or a
  local's the body assigns, as a parameter of the emitted loop, so the entry
  and each back edge give the values and set no local.
- The block type is the signature: `0x40` for `[] -> []`, a value type for
  `[] -> [t]`, and a type index otherwise (`BlockType::Signature`).

```wat
block
  i32.const 0
  local.get $n          ;; the first state
  loop (param i32 i32)
    local.set $high
    local.set $low
    ...                 ;; body
    br 0                ;; with the next state on the stack
  end
end
```

Where values sit between uses is the scheduler's choice, not the language's:
codegen takes a loop's parameters off the stack into locals at its top.
Keeping them on the stack where a value is consumed at once is an
optimization for later, as is carrying a block's exit values on its `br`s
rather than through locals.

## Examples

Assume `memory heap: u32;`, so `xs.len()` is a `u32`.

**Counting.** No `mut`: each iteration's `i` is the last one's result.

```wx
loop (i: u32 = 0) {
    if i == n { break };
    visit(i);
    i + 1
}
```

**Summing a slice**, by name; a `break` hands the result out.

```wx
func sum(xs: heap::&[u32]) -> u32 {
    loop (i: u32 = 0, total: u32 = 0) {
        if i == xs.len() { break total };
        ({ i: i + 1, total: total + xs[i] })
    }
}
```

**Several pieces of state, with an early `continue`** (`try_args` in
`examples/wasi/main.wx`).

```wx
loop (next: u32 = 0, start: u32 = 0, at: u32 = 0) {
    if at == text.len() { break };
    if text[at] == '\0' {
        arguments[next] = slices::slice_at(text, start, at - start);
        continue ({ next: next + 1, start: at + 1, at: at + 1 });
    }
    ({ next, start, at: at + 1 })
}
```

**The same, updated in place.** `mut` parameters are assigned within the
iteration and handed on by shorthand.

```wx
loop (mut next: u32 = 0, mut start: u32 = 0, mut at: u32 = 0) {
    if at == text.len() { break };
    if text[at] == '\0' {
        arguments[next] = slices::slice_at(text, start, at - start);
        next += 1;
        start = at + 1;
    }
    at += 1;
    ({ next, start, at })
}
```

**Fibonacci.** The update is simultaneous, so no temporary.

```wx
func fib(n: u32) -> u32 {
    loop (a: u32 = 0, b: u32 = 1, k = n) {
        if k == 0 { break a };
        (b, a + b, k - 1)
    }
}
```

**Nested loops.** The inner header is in the outer body, so `col` starts at 0
on every row. A labelled `continue` gives the state of the loop it names.

```wx
loop :rows (row: u32 = 0) {
    if row == height { break };
    loop (col: u32 = 0) {
        if col == width { break };
        if skip(row, col) { continue col + 1 };
        if done(row, col) { break :rows };
        if next_row(row, col) { continue :rows row + 1 };
        visit(row, col);
        col + 1
    }
    row + 1
}
```

## Edge cases

1. **The initial values are outside the parameters' scope.**
   `loop (i: u32 = i + 1)` reads an outer `i`; the parameter shadows it
   inside the body. An initial value does not see the parameters before it
   either.
2. **The initial values are outside the loop's targets.** An unlabelled
   `break` in one leaves an enclosing `block` or loop, not this one;
   `break :label` naming this loop is an undeclared label (E2011).
3. **A diverging initial value** (`loop (x = return)`) makes the loop
   unreachable: its type is `!`.
4. **A body that forgets the next state is a type error.** A body ending in a
   statement (`i += 1;`) is `()`, which is not the state's type (E2001, at the
   body's end). A body whose every path breaks, returns or continues is `!`,
   and fits.
5. **A bare `continue` in a loop with parameters is a mismatch**, as
   `continue ()` against the state's type. It never means "carry on
   unchanged".
6. **A labelled `continue` gives the named loop's state**
   (`continue :rows row + 1` from an inner loop), and a named list there takes
   that loop's names.
7. **The state is not the loop's value.** The loop's type is what its
   `break`s give, `!` without one.
8. **A value that does not change across iterations** belongs in a `local`
   before the loop, not in the state, where it would be handed on every time.
9. **Each outer iteration re-runs an inner header** (the nested example).
10. **A parameter's type ends at `,`, `)` or `=`.** No type contains `=`.

## Variants considered

**One initializer for the whole state**, `loop (i: u32, total) = (0, n)`, the
previous form of this decision, with one parameter allowed without
parentheses. A header's positions had to be matched against a separate tuple,
which gets error-prone past a few parameters, and the first state needed its
own named form (`= ({ i: 0, total: n })`) to stay readable. It could start
from one computed value (`= pair()`); with initial values per parameter that
is a `local` before the loop.

**Initial values as defaults.** `= x` here is not a default: a function
parameter's default would be evaluated per call when omitted, while an
initial value is evaluated once and every next state still gives every
parameter. An omitted name in a named next state is an error, not "keep it".

**The header as a `local` initialized once.** `loop P = e { body }` as
`block { local P = e; loop { body } }`: a mutation carries into the next
iteration because the binding is the same local, and the body's result stays
`()`. Replaced, because the next state is then implicit: forgetting `i += 1`
loops forever silently, and the data flow between iterations is spread over
assignments. Its one advantage, not restating the state, is what the named
form's shorthand gives back (`({ next, start, at })`).

**Leaving a name out keeps its value** (struct-update style). Shorter, and
forgetting the counter is a silent infinite loop again.

**The header as a pattern with a type on the whole**
(`loop (i, total): (u32, u32) = (0, 0)`). A pattern allows more than a state
needs (destructuring, `_`, literals, constants, alternatives), each of which
the checker would then refuse, and it puts the types away from the names they
belong to.

**Destructuring in the header** (`loop (Point(x, y) = p)`). A destructured
part has no name for the named form. Destructuring goes in the body, as in a
function.

**A named next state through branches**, by the expected type: see
"`({ .. })`: parsed anywhere, meaningful only written directly".

**Implicit carry of the parameters' current values** at the end of the body.
With immutable parameters, falling off the end repeats the same state forever.

**Wasm-literal constructs** (`loop` not repeating by itself; `break` and
`continue` as one jump whose direction is the target's). Every ordinary loop
would need a trailing `continue` and a `block` around it, the
`block { loop { ..; continue; } }` shape tried in `examples/wasi`.

**A C-style `for (init; cond; step)`.** Three clauses where the header needs
one, and the step is the body's value.

## Open

### `while` and parameters

After `while`, a condition may start where a parameter list would, and a
parameter list can look like an expression for arbitrarily long
(`while (a: T = x) ..` against `while (a) == b`), which would need
backtracking. Leaning: parameters on `loop` only. Decide with `while`.
