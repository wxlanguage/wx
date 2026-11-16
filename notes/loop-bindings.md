# Loops: the block/loop model and loop-scoped bindings

Status: 2026-11-16. Decided: the model (a `loop` is a fused Wasm `block` +
`loop`); the jump targets (an unlabelled `break` leaves the nearest written
`block` or loop, `continue` restarts the nearest loop), implemented; and a
loop's state (`loop P: T = e { .. }`, each iteration entered with the next
state, given by the body's value or `continue`'s, positionally or by name),
not implemented. Open: whether `while` takes a header.

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

## Decision: a loop has a state, given each iteration

A loop may declare a state in its header. Each iteration is entered with a
value of it: the first from the initializer, every next one from the body.

```wx
loop :label P: T = e { body }
```

- **`P` is a binder pattern**: one binder, or a tuple of binders, each `name` or
  `mut name` (`notes/binders.md`). No destructuring, and no `_`: every part of
  the state has a name.
- **`: T` is the state's type**, optional, on the whole pattern as on a
  `local`. The label is optional too.
- **`e` is the first state**, evaluated once, before the first iteration.
- **The body's value is the next state.** Falling off the end of the body
  starts the next iteration with the body's tail; `continue v` starts it with
  `v`. Either way the whole state is given.
- **The bindings hold the current state for one iteration.** They are
  immutable unless `mut`, which lets the body assign them within the iteration;
  the next iteration still takes its state from the body's value, never from
  what a binding was left holding.
- **`break` leaves the loop**, with the loop's value, as without a header. The
  state is not the loop's value; to hand it out, `break` it.
- **Its scope is the loop** (header and body), and nothing after it.

A loop without a header is the case of the state `()`: its tail is `()`, and a
bare `continue` is `continue ()`. Nothing changes for it.

Each iteration is entered like a call of the body, with the header's bindings
as its parameters: the tail and `continue`'s value are the arguments of the
next call. The analogy stops at the syntax: the header is a pattern, read as
patterns are (a lone identifier binds), not as a parameter list.

### Giving the next state

The next state is a whole value, given in one of two forms, as a call's
arguments are:

- **Positionally**, as a value of the state's type: `(i + 1, total + x)`, or
  `i + 1` for one binding (a one-element tuple is its element).
- **By name**, as a named list: `({ i: i + 1, total: total + x })`, with the
  shorthand `({ i: i + 1, total })` for a value handed on unchanged. Each name is
  a header binding.

The named form follows the rules of a call by name: every name is required
(E2122 for a missing one), an unknown name is E2120, a repeated one E2121, and
the two forms do not mix in one list (E1018). Leaving a name out does not keep
its value: forgetting to advance a counter is an error, not a silent infinite
loop.

All of the next state is computed before any binding takes it, so the update
is simultaneous: `(b, a + b)` reads the old `a` and `b`.

### `({ .. })`: parsed anywhere, checked where its names are known

A parenthesized list that starts with `{` is a named list. The parser accepts
it wherever an expression can start (today a `{` there is a block without its
keyword, E1017). It has no type of its own: tuple types have no names, so no
expected type can say what its names mean. The checker accepts it only where
the names are known:

- a header loop's body tail, and
- `continue`'s value, naming that loop (or the nearest one).

Anywhere else it is one error, saying that a named list needs a place whose
names are known. `break ({ .. })` is one such place: the loop's value has no
names.

### Typing the state

The state's type comes from the two sources a `local`'s does:

**An annotation on the whole pattern**, `P: T`. The initializer is checked
against `T`, so its literals take their types from it:

```wx
loop i: u32 = 0 { .. }
loop (i, total): (u32, u32) = (0, 0) { .. }
```

**Ascription in the initializer**, `(value: T)`:

```wx
loop i = (0: u32) { .. }
loop (next, start, at) = (0: u32, 0: u32, 0: u32) { .. }
```

**Neither, when the initializer is already typed** (`loop at = start {`, with
`start: u32`). **Both** may meet, and must agree
(`loop (a, b): (u32, u32) = (0: u32, 1) {`). **Neither, with a literal**, is
E2002, as `local i = 0;` is.

There is no type on a single binder inside the tuple
(`loop (i: u32, total: u32) = ..`): that is a parameter list's syntax, and the
header is a pattern.

### Why no `local` keyword

It carries nothing. After `loop`, only a label (`:name`) or the body (`{`) can
come today, so any other token starts a header, decided by its first token. A
binder without a keyword already has precedent where its position says what it
is: a function's parameters, a match arm's pattern, a planned `for x in xs`.

### Parsing

`loop P: T = e {` parses as `if c {` does: `{` never starts an expression in WX,
so the initializer ends at the body's `{`. The parser reads an optional label,
then a header if the next token is not `{`, then the block. `continue` takes an
optional value after its optional label, as `break` does.

### Wasm

Each binding is a Wasm local (function-wide; the scope is a WX naming rule).
The initializer is stored before the loop; at the back edge the next state is
computed onto the stack and stored, last value first, then `br` repeats:

```wat
i32.const 0
i32.const 0
local.set $total
local.set $i            ;; the first state
block
  loop
    ...                 ;; body
    local.get $i
    i32.const 1
    i32.add             ;; next i
    local.get $total
    ...                 ;; next total
    local.set $total
    local.set $i        ;; the next state, stored at once
    br 0
  end
end
```

A shorthand value handed on unchanged (`({ total, .. })`) is a store of a local
into itself, which the optimizer drops.

This is not WX's form of Wasm's loop parameters. A Wasm loop parameter is a
value on the operand stack, unnamed and not a place; a named binding read more
than once has to live in a local, so a WX loop's state is in locals either way.
Carrying it across the back edge on the stack instead is an encoding choice
codegen may make, and rarely saves anything. Wasm loop parameters stay without
WX syntax; WX has no syntax for stack values anywhere.

## Examples

Assume `memory heap: u32;`, so `xs.len()` is a `u32`.

**Counting.** No `mut`: each iteration's `i` is the last one's tail.

```wx
loop i: u32 = 0 {
    if i == n { break };
    visit(i);
    i + 1
}
```

**Summing a slice**, by name; a `break` hands the result out.

```wx
func sum(xs: heap::&[u32]) -> u32 {
    loop (i, total) = (0: u32, 0: u32) {
        if i == xs.len() { break total };
        ({ i: i + 1, total: total + xs[i] })
    }
}
```

**Finding an index.**

```wx
func index_of(xs: heap::&[u8], wanted: u8) -> u32 {
    loop i: u32 = 0 {
        if i == xs.len() || xs[i] == wanted { break i };
        i + 1
    }
}
```

**Several pieces of state, with an early `continue`** (`try_args` in
`examples/wasi/main.wx`).

```wx
loop (next, start, at) = (0: u32, 0: u32, 0: u32) {
    if at == text.len() { break };
    if text[at] == '\0' {
        arguments[next] = slices::slice_at(text, start, at - start);
        continue ({ next: next + 1, start: at + 1, at: at + 1 });
    }
    ({ next, start, at: at + 1 })
}
```

**The same, updated in place.** `mut` binders are assigned within the
iteration and handed on by shorthand.

```wx
loop (mut next, mut start, mut at) = (0: u32, 0: u32, 0: u32) {
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

**Two pointers, reversing in place.**

```wx
func reverse(xs: heap::*[u8]) {
    if xs.len() == 0 { return };
    loop (i, j): (u32, u32) = (0, xs.len() - 1) {
        if i >= j { break };
        local t = xs[i];
        xs[i] = xs[j];
        xs[j] = t;
        (i + 1, j - 1)
    }
}
```

**Fibonacci.** The update is simultaneous, so no temporary.

```wx
func fib(n: u32) -> u32 {
    loop (a, b, k) = (0: u32, 1: u32, n) {
        if k == 0 { break a };
        (b, a + b, k - 1)
    }
}
```

**Nested loops.** The inner header is in the outer body, so `col` starts at 0
on every row. A labelled `continue` gives the state of the loop it names.

```wx
loop :rows row: u32 = 0 {
    if row == height { break };
    loop col: u32 = 0 {
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

**No state.** A plain `loop` stays as it is.

```wx
loop {
    if try_read() { break };
}
```

## Edge cases

1. **The initializer is outside the bindings' scope.** `loop i: u32 = i + 1 {`
   reads an outer `i`; the header's `i` shadows it inside the loop.
2. **The initializer is outside the loop's targets.** An unlabelled `break` in
   it leaves an enclosing `block` or loop, not this one; `break :label` naming
   this loop is an undeclared label (E2011), since the initializer is not
   inside it.
3. **A diverging initializer** (`loop x = return {`) makes the loop
   unreachable, and it is warned as a statement after a `return` is.
4. **A body that forgets the next state is a type error.** A body ending in a
   statement (`i += 1;`) is `()`, which is not the state's type (E2001, at the
   body's end). A body whose every path breaks, returns or continues is `!`, and
   fits.
5. **A bare `continue` in a loop with a state is a mismatch**, as `continue ()`
   against the state's type. It never means "carry on unchanged".
6. **A labelled `continue` gives the named loop's state** (`continue :rows
   row + 1` from an inner loop), and a named list there takes that loop's names.
7. **The state is not the loop's value.** The loop's type is what its `break`s
   give, `!` without one.
8. **A value that does not change across iterations** belongs in a `local`
   before the loop, not in the state, where it would be handed on every time.
9. **Each outer iteration re-runs an inner header** (the nested example).
10. **Label placement.** The label stays right after the keyword, before the
    pattern, `loop :outer i: u32 = 0 {`.
11. **The annotation ends at `=`.** No type contains `=`; a label starts with `:`
    and a pattern never does, so `loop :i {` and `loop i: u32 = 0 {` are told
    apart by their first token.

## Variants considered

**The header as a `local` initialized once.** `loop P = e { body }` as
`block { local P = e; loop { body } }`: a mutation carries into the next
iteration because the binding is the same local, and the body's tail stays
`()`. This was the first decision. Replaced, because the next state is then
implicit: forgetting `i += 1` loops forever silently, and the data flow between
iterations is spread over assignments. Its one advantage, not restating the
state, is what the named form's shorthand gives back (`({ next, start, at })`).

**Leaving a name out keeps its value** (struct-update style). Shorter, and
forgetting the counter is a silent infinite loop again.

**Destructuring in the header** (`loop (Point(x, y), n) = ..`). The positional
form would still work, but a destructured part has no name for the named form,
and naming the leaves instead would need every part bound to rebuild the value
(a `_` or `..` throws parts away) and the constructor to be accessible.
Destructuring goes in the body, as in a function.

**A type on each binder** (`loop (i: u32, total: u32) = (0, 0)`). Parameter
syntax inside a pattern, the ambiguity `notes/binders.md` removes.

**Implicit carry of the bindings' current values** at the end of the body. With
immutable bindings, falling off the end repeats the same state forever.

**Wasm-literal constructs** (`loop` not repeating by itself; `break` and
`continue` as one jump whose direction is the target's). Every ordinary loop
would need a trailing `continue` and a `block` around it, the
`block { loop { ..; continue; } }` shape tried in `examples/wasi`.

**A C-style `for (init; cond; step)`.** Three clauses where the header needs
one, and the step is the body's value.

## Open

### `while` and a header

After `while`, a condition may start where a pattern would, and a pattern can
look like an expression for arbitrarily long (`while (a, b): T = ..` against
`while (a, b) == c`), which would need backtracking. Leaning: a header on
`loop` only. Decide with `while`.

## Implementation sketch

- **AST:** `Expression::Loop` gains an optional header (a binder pattern, an
  optional type, an initializer); `Expression::Continue` gains an optional
  value; a named list is a new expression holding a `List<NamedArgument>`, as a
  call by name does. The parser reads the header after the label when the next
  token is not `{`, and a named list when `(` is followed by `{`.
- **TIR:** the loop's scope records the state's type and its bindings, which
  are locals of the loop scope. The body's tail and each `continue`'s value are
  held to the state's type (`expect`, so its coercions apply), a named list
  arranged into the bindings' order by name, with the call-by-name diagnostics.
  A named list anywhere else is reported once. `_` as a header binder is
  reported (`notes/binders.md`).
- **Lowering:** the initializer is assigned to the bindings before MIR's
  `Loop`; at the end of the body and before each `Continue`, the next state is
  evaluated in full and then assigned. MIR and codegen keep their `Loop`.
- **wx-fmt:** print the header after the label, `continue`'s value, and named
  lists; wrapping a long header is a layout decision of its own.
- **LSP:** the bindings are ordinary locals, so hover, go-to-definition and
  rename work through the existing tables; completion inside a named list
  offers the header's names, as inside a call by name.
