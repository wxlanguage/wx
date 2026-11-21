# Binders: names in parameters, fields and patterns

Status: decided 2026-11-16. Implemented, except the loop header, which is built with `notes/loop-bindings.md`. "A slot's type may be left to inference" was revised the same day and is implemented. "As built" records where the implementation went another way than the plan.

## Problem

A lone identifier means two different things in lists that look alike:

```wx
func log(i32);          // a parameter of type `i32`, no name
local (total, i) = ..;  // two bindings, `total` and `i`
```

In a parameter or field list, a lone identifier is a type, and a name is
optional (`binding: Type` or `Type` alone, `parse_binding_and_type` in
`ast/parser.rs`). In a pattern it is a binding. The loop header
(`notes/loop-bindings.md`) made this visible: described as the loop's
parameter list, it is written as a pattern.

Other problems come from the same place:

- **`_` means more than one thing.** In a pattern it drops a value. In a
  parameter it is a binder that binds nothing and also takes the parameter's
  name away, so the function can only be called by position (E2094,
  `PositionalOnlyCall`), and conformance has a special rule for it (an impl may
  name a parameter the trait leaves unnamed).
- **An unnamed field can only be read with a pattern.** WX has no `t.0`, so
  `enum Errno(u16)` is read as `local Errno(code) = e;`, never `e.code`.
- **The parser has to guess.** Each slot looks ahead to decide whether an
  identifier is a binder (followed by `:`) or the start of a type.

## Decision

### Binder lists and type lists

- **A list of binders** names what it introduces. These are a function's
  parameters, a struct's fields, an enum's repr, a loop header and every
  pattern. In a binder list, a lone identifier is always a binder.
- **A list of types** describes a structural type. These are a tuple
  `(u8, u16)`, a function type `func(A) -> R`, and type arguments. In a type
  list, a lone identifier is always a type.

Nominal declarations name their parts; a structural shape is a tuple. A
nominal type that should wrap a positional shape holds a tuple:
`struct Pair(pair: (i32, u8))`, still constructed as `Pair(1, 2)`, since a
lone tuple field takes several arguments.

### A binder always has a name

A binder is `name` or `mut name`, wherever it binds:

| Where | Binder | `: Type` |
| --- | --- | --- |
| Parameter | `name`, `mut name` | written: nothing infers it |
| Struct field, enum repr | `name`, `mut name`, optional `pub` | written: nothing infers it |
| Loop header | `name`, `mut name` | optional: the initializer gives it |
| `local` and match patterns | `name`, `mut name`, or `_` | optional on `local` |

`_` stays only where a value really arrives and is thrown away: as a pattern
in a destructuring `local` or a match arm, and in `_ = expr;`. It is never a
binder.

**The type is needed where nothing else gives it** (a parameter, a field, a
repr) and optional where an initializer does (a `local`, a loop header). That
is the only difference between the rows, and it is the checker's, not the
grammar's (next section).

### A slot's type may be left to inference

Revised 2026-11-16, with the loop header. Every slot that binds a name has
one grammar, a parameter's, a field's, a repr's and a loop header's alike:

```
[pub] [mut] name (: Type)?
```

The type is optional in the syntax, and an omitted type means the same as a
written `_` (`x: _`, the placeholder any type position accepts): infer it.
Whether anything can is decided where the slot is checked:

- **A loop header** infers it from its initializer (`notes/loop-bindings.md`).
- **A signature** (a parameter, a field, a repr) has nothing to infer it
  from: no type is read from a body or a use. The slot is reported, E2036
  (`InferInSignature`, the code `_` in a signature already has), at the name
  for an omitted type and at the `_` for a written one, and keeps an `ERROR`
  type, so everything after it is silent. `func log(i32)` is such a slot: a
  parameter named `i32` whose type is missing. No hint guesses that `i32`
  was meant as a type.

So the parser records what is written (`ty: Option<TypeId>`) and reports
nothing for a missing type; E1023 (`MissingTypeAnnotation`) is retired, and
wx-fmt prints a slot without a type as `name`. The inference itself is the
same as a `local`'s: statement-scoped, from the initializer alone.

### Syntax stays shared; meaning is checked

The parser keeps one slot grammar for parameters, fields and reprs:
`[pub] [mut] binder (: Type)?`, where `binder` is an identifier or `_`. It
parses `_` there, so wx-fmt and the LSP see one tree whether or not the code
is valid, and the checker reports it:

- **A lone identifier is a binder with no type.** `func log(i32);` is a
  parameter named `i32` with an `ERROR` type, so its uses are silent; the
  missing type is reported (as revised: E2036 by the checker, "A slot's type
  may be left to inference").
- **A slot that starts with a type is a missing binder.** `func f(heap::&u8)`
  (an identifier followed by `::`, `<` or anything but `:`, `,` or `)`, or a
  slot starting with `(`, `[`, `*`, `&`, `!` or `func`) reports a missing name
  at the slot and keeps the type, with no binder.
- **`_` in a binder slot** (a parameter, a field, a repr, a loop header) is
  reported by the checker where it builds that slot: "a parameter needs a
  name", "a field needs a name". The slot is kept, as positional, so calls,
  constructions and patterns that use it do not cascade.

### What disappears

- **E2094** (`PositionalOnlyCall`): every function and every struct
  constructor has a name for each parameter, so every call may be by name.
- **Conformance's leniency** for unnamed parameters
  (`tir/conformance.rs`, "may name a parameter the trait leaves unnamed"): an
  impl's parameter names are the trait's, compared like any other part of the
  signature (E2058).
- **The binder-or-type lookahead** in `parse_binding_and_type`.

### What it gives

- Every field is readable by name, an enum's repr included (`e.code`,
  `b.value`), with no destructuring.
- Every call target can be called by name, and every signature prints with
  its names (hover, diagnostics, docs, imports).
- One meaning for `_`: drop a value.

## Unused parameters

A parameter that is not needed is still named, and dropped in the body:

```wx
impl Visit for Counter {
    func visit(self: Self, node: Node) -> Self {
        _ = node;
        ..
    }
}
```

`_ = param;` reads the parameter and drops the value. It changes nothing
outside the body, which matters because a parameter's name is part of its
function's interface: a call by name uses it, and a trait impl must keep the
trait's names (E2058). Renaming a parameter to silence a warning would break
calls; dropping it does not.

So the unused-variable warning (L3000, `notes/unused-definitions-plan.md`)
needs no exemption: not for `_`-prefixed names (no naming convention), and not
for trait impls' parameters. A local or parameter that is never read is
warned; the fix is to read it or drop it. `_ = x;` must count as a read of `x`
(its operand is an ordinary value read, `ExprKind::Drop`).

## Precedent

Rust made the parameter half of this move: its 2015 edition allowed anonymous
trait-method parameters (`fn f(i32);`), and RFC 1685 removed them in the 2018
edition, because a lone identifier in a parameter list was ambiguous between a
name and a type. Rust kept positional tuple-struct fields (`struct Meters(u32)`);
WX does not, since it has no `t.0` to read them by.

## Variants considered

**A lone identifier as a type in parameters, a binder in patterns** (the
current rule). Each list reads well alone, and the two look the same while
meaning different things.

**Parameters as binders, fields and reprs as type lists** (Rust's split). It
keeps `struct Meters(u32)`, and leaves two slot grammars and a field readable
only through a pattern. Core and the examples name 69 of their 89 fields and
reprs already; every unnamed one is an enum repr.

**`_` allowed as a field name.** No case needs it. Privacy is `pub`'s job;
positional construction works with named fields; a padding or reserved field
in a `#[fixed_order]` layout reads better named `reserved`. It would only take
away the by-name construction and `.name` access.

**`_` kept as a parameter binder.** It is what forces E2094 and the
conformance rule, and its one use, marking a parameter unused, is served by
`_ = param;` without touching the interface.

## As built

The plan below said `_` would be parsed in a binder slot and reported by the
checker. It went simpler, in the parser alone:

- **A binding is `name` or `mut name`** (`ast::Binding`, a struct; there is no
  `Wildcard`), and every `FunctionParam` and `StructField` has one.
- **`_: T` and a type alone** (`(u8, u16)`, `*u8`, `func(A) -> R`) are
  reported ("expected a name, found `_`", "expected a name before this type",
  E1001 `UnexpectedToken`, no code of its own) and kept with a missing name,
  the error symbol (`Binding::missing`), as `x.` keeps a missing
  `PathSegment`. The item keeps its arity, and checking treats the slot as
  unnamed and stays silent on it: no local, no name to call or match by, no
  duplicate, no conformance mismatch.
- **A lone identifier** with the slot ending after it (`func log(i32)`) is a
  binding with no type: E1023 and an error type. Revised: a slot's type is
  optional in the parser (`ty: Option<TypeId>` on `FunctionParam` and
  `StructField`), and signature building resolves a type left out as a
  written `_` (`resolve_infer` in `tir/signatures.rs`, the one place the
  infer policy is applied), so a signature reports it with the same E2036, at
  the name; silent for a slot whose name the parser reported missing. E1023
  is retired. See "A
  slot's type may be left to inference". An identifier followed by
  anything else (`heap::*u8`) is "expected `:`", and the slot is skipped:
  telling a name from a type there is the lookahead this removes.
- **Anything else** is "expected a name", and the list skips the slot.
  `skip_to_separator` now skips a group it opens whole (`(..)`, `[..]`,
  `{..}`), and stops at a keyword that only starts an item at any depth, so
  a group left open does not swallow the items after it.
- **E2094** stays, for a value called through `Call` by name; its
  unnamed-parameter case is gone. **E2088** (`TupleStructBracePattern`) is
  retired: no valid struct has an unnamed field. **E1022** (`mut` needs a
  name) is retired: `mut` before something that is no name is "expected a
  name".
- **Hover** prints an enum's repr with its name (`enum Color(value: u8)`).

## Plan

1. **Parser** (`parse_binding_and_type`, `ast/parser.rs`): an identifier, `mut
   name` or `_` starts a binder; with no `:` after it, E1023 and an `ERROR`
   type (the path `mut x` and `self` take today, for every name). A slot that
   starts with a type reports the missing name and keeps the type with no
   binder. Fields and reprs go through the same function. The test
   `parameters_and_fields_share_the_slot_grammar` (`ast/tests.rs`) changes to
   assert that `x` alone is a binder with a missing type.
2. **Checker:** report `_` as a parameter binder (signature construction,
   `tir/signatures.rs`), and as a field or repr binder (where the fields are
   built, `Declarations::fields`), one diagnostic per slot, with a new code.
   The loop header gets the same rule when it is built.
3. **Remove** E2094 (`typecheck/calls.rs`, its tests in `typecheck.rs`) and
   conformance's unnamed-parameter leniency (`tir/conformance.rs`).
4. **Migrate** the 20 unnamed reprs in core and the examples, naming each:
   `value` for most, `code` for an `Errno`. Core's are
   `pub enum Bool(pub u8)` and `pub enum Ordering(pub i8)`. The examples' are in
   `wasi_random`, `wasi_hello_world`, `wasi_file_io`, `snake`, `hello_wasi`,
   `wasi_preview1_port`, `two_memories` and `arena`. No `.wx` source in core or
   the examples has an unnamed or lone-type parameter. The test sources that
   write one, or a `_` field or repr, give each a name: `ast/tests.rs`
   (including the `top_level_items` snapshot's source, so that snapshot is
   regenerated), `tir/signatures.rs`, `tir/typecheck.rs`, `tir/body.rs`,
   `tir/conformance.rs` and `wx-fmt/src/tests.rs`.
5. **Printers:** every place that prints a signature or a field list back as
   source (`tir/format.rs`, hover in wx-lsp, wx-fmt) prints each binder's name.
6. **Docs:** CLAUDE.md's bullets on functions (parameter syntax, E2094, the
   impl naming rule), structs and enums, and "Trait-impl conformance";
   `notes/unused-definitions-plan.md` records the L3000 decision above.
