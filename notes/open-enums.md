# Open enums: a trailing `..` for values the enum does not name

Status: design, not implemented. Written 2026-11-05 for an implementer who has
not seen the discussion; everything needed is here or linked.

## Problem

A WX enum is a repr integer type plus named constants. It is erased to its
repr scalar: no tag, no layout of its own (`CLAUDE.md`, "Enums and `match`"). So
a value of an enum type can hold any number its repr holds, for example through
`transmute::<u16, Errno>(77)`, or by being a host function's result.

Today every enum is **closed**: its variants are taken to be all its values.
`match` over one is exhaustive when every variant is covered, and the compiled
code for the impossible case is `unreachable`. Checked on the current compiler:

```wx
enum E(u8) { A = 0, B = 1 }
func f(x: u8) -> u32 {
    match transmute::<u8, E>(x) { E::A => 10, E::B => 20 }
}
```

compiles to `if x == 0 { 10 } else if x == 1 { 20 } else { unreachable }`. So
`f(7)` traps. That is a sound choice for a closed enum, but it is the wrong
type for numbers that come from outside the module. The motivating case is
`examples/hello_wasi`: `fd_write` returns WASI's `errno`, a `u16` of which the
program names a handful of codes and the host may return any other. The program
should be able to say "these are the codes I know, and the type holds others",
and the compiler should make the program handle the others.

## Proposal

An enum body may end with `..`:

```wx
enum Errno(u16) {
    Success = 0,
    Badf = 8,
    Pipe = 64,
    ..
}
```

An enum written this way is **open**: its variants name some of its values, and
every value of the repr is a valid value of the enum. Concretely:

1. **Exhaustiveness.** A `match` on an open enum is exhaustive only if it covers
   every value of the repr, so in practice it needs a `_` arm (or a binding arm)
   even when every named variant has an arm. The `_` arm is never reported as
   unreachable for being redundant after the named variants (it is unreachable
   only if the named variants really cover the whole repr range, which the
   existing integer logic already decides).
2. **Validity.** `transmute` from the repr integer (or any type of the same
   `StackValue::Repr`) to an open enum is always meaningful: no value is out of
   range. Nothing else about `transmute`'s checking changes. A closed enum keeps
   today's behaviour (a value matching no variant is a hazard that traps in an
   exhaustive `match`).
3. **Everything else is unchanged.** Representation, layout, lowering, constant
   evaluation, `==`/`!=`/ordering, `Enum::Variant` paths, duplicate-name and
   duplicate-value checks, auto-increment. The `..` is not a variant: it has no
   name, no value and no `ConstIdx`.

The point of the design is that it changes only what the checker believes about
the set of values. Because the enum is already erased to its repr, there is no
new runtime or code-generation work.

### Syntax and what is judged where

Syntax and validation are separate. The parser takes `..` as an entry of the
body, like a variant, and reports nothing about it; the checker judges it.

- **AST** (`ast/mod.rs`): `Item::Enum { entries: Box<[Separated<Spanned<EnumEntry>>]>, .. }`
  with `enum EnumEntry { Variant(EnumVariant), Rest }`. `..` may be written
  anywhere and any number of times (`A, .., B` and `.., ..` parse). A trailing
  comma after it is read. `enum E(u8) { .. }` is allowed: an enum whose values
  are exactly its repr's, a distinct type with the meaning of `struct E(u8)`.
  Useless, but harmless.
- **Prescan** (`tir/defs.rs`): the variants are the `Variant` entries, in order,
  and only they get constants, so `EnumDef::variants` stays one contiguous run.
  `EnumDef::open` is the span of the first `Rest`, if any.
- **Enum signature** (`tir/signatures.rs`, `report_open_markers`), from the
  entries alone, as warnings, because any `..` opens the enum and so where it
  stands or how many there are does not change the meaning:
  - W2013 `MisplacedOpenMarker`: the first `..` has entries after it.
  - W2014 `RedundantOpenMarker`: a second or later `..`, which adds nothing.
- **`check_discriminants`** (`tir/eval.rs`), which has the variants' values:
  W2014 `RedundantOpenMarker` again when the distinct values already number
  every value of the repr (`u8` with 256 variants), so the `..` admits nothing.
  It needs values, which exist only after the constant bodies are built, so it
  cannot be decided in the signature.
- An enum with `..` still needs its repr, like any other (E2036,
  `MissingEnumRepr`, otherwise).
- **Formatter** (`wx-fmt`): `..` is an entry printed where it stands. Every entry
  but the last takes a comma; the last takes the break-only trailing comma
  unless it is a `..`, which takes none (as in a pattern), so a trailing comma
  after a last `..` is dropped. A body of only `..` with no comments prints as
  `{ .. }`.

### What `..` means elsewhere in WX (why this spelling)

In a destructuring `local` and in struct patterns, `..` already means "this
list is not claimed to be complete" (`Point({ x, .. })`; `..` opts out of
exhaustiveness). In an enum body it says the same about the list of variants.
The match arm that handles the rest stays `_`, which is "any value" in every
other position. The alternatives are in the next section.

## Alternatives considered

| Option | Verdict |
| --- | --- |
| Trailing `_`, as in Zig (`enum(u16) { a = 0, _ }`) | Same semantics; rejected only on spelling. `_` is "a value" everywhere in WX, so it would read as an unnamed variant. `..` matches WX's existing "list not complete" marker. If the spelling is reconsidered, nothing below changes except the token. |
| Attribute, `#[open]` or `#[non_exhaustive]` | Rejected. Rust's `#[non_exhaustive]` means "may gain variants later, every value is still a known variant", which is the opposite of this. Whether every number is valid is a property of the type that decides what `match` and `transmute` may do, so it belongs in the declaration's text, not in metadata. |
| Keyword, `open enum E(u16) { .. }` | Rejected: a new keyword for a modifier that changes the meaning of the body, and Rust-style syntax avoids new keywords. |
| Newtype plus constants (`struct Errno(code: u16)` with associated consts) | Already expressible (not verified here), which is why an enum is not strictly needed. Rejected as the answer: constant patterns on a struct need an `Eq` impl and path-qualified constants, and the type is not an enum for tooling (variant listing, exhaustiveness witnesses). |
| A catch-all variant that carries the number (`Unknown(u16)`) | Rejected. Enums are erased to their repr; a variant with a payload would need a layout and a tag. |

## Design details

### Exhaustiveness (`tir/typecheck/exhaustiveness.rs`, `tir/usefulness.rs`)

`..` means the rest: every value of the repr the variants do not name. `ctor_set`
gives an open enum `CtorSet::Open(values)`: the variants' values, listed, and
one more constructor for the rest, which no pattern covers but a wildcard.
(Only a variant can name an enum's value in a pattern: `transmute` is not
evaluated at compile time, so there is no constant of an unnamed value.) The
work is proportional to the number of variants, not to the width of the repr,
and the algorithm reads it as follows:

- `Open` is never complete, so a `match` needs a `_` or binding arm.
- Missing witnesses are the variants no row names, in order, then `_` for the
  rest. `match o { Open::A => .. }` reports ``patterns `Open::B`, `Open::C` and
  `_` ``; with every variant named it reports `_` alone.
- If the variants name every value of the repr (a `u8` with 256 variants) there
  is no rest: `ctor_set` returns `Listed` as for a closed enum, so naming them
  all is exhaustive and a `_` after them is unreachable. The `..` is then
  redundant and warned (W2014).

`Char` needs nothing special in `ctor_set`: it is std's `struct Char(value: u32)`,
so it has the struct's one constructor and a `u32` field. A char pattern lowers
as that struct with its code point, and `render_witness` prints a `Char`
witness as a char literal.

### Prescan and signatures

See "Syntax and what is judged where" above. `AstNodeRef::Enum` in
`signatures.rs` destructures `Item::Enum { repr, name, entries, .. }`; the
`EnumVariant` entries of `ast_nodes` are pushed only for real variants.

### Formatter

Described above. The "already formatted input reports no edits" rule applies
(`CLAUDE.md`, "`wx format` and the LSP formatting request must agree"), so the
tests format their own output, with comments around the `..` and with a `..`
in the middle of the body.

### Lowering and evaluation

No change is expected. A `match` over an enum lowers its patterns as integer
comparisons (and `br_table` for a dense set); the `_` arm is the default. The
only thing to confirm with a runtime test is that an out-of-range value reaches
the `_` arm instead of `unreachable`, which is the point of the feature.

### Documentation

- `CLAUDE.md`: one bullet under "Language features", next to the enum bullet
  ("Enums and `match`").
- `examples/hello_wasi/main.wx`: give `Errno` a trailing `..` and keep its
  `match` with `_ => trap()`; update the comment above the enum (it currently
  explains that the host may return codes not listed and that `_` is needed).
  Rebuild and run `node --no-warnings examples/test_memory_examples.mjs`.
- Thesis, `thesis/chapters/en/04-stack-values.typ` (`transmute`): optional
  follow-up for the author, not part of this task.

## Tests

Write new tests where the code under test is (`CLAUDE.md`, "Testing patterns").

- **Parser** (`ast/tests.rs`): `..` last parses and is recorded; `..` not last,
  a second `..`, and `..` with no repr each report a diagnostic (assert the
  specific code with `DiagnosticView`); `{ .. }` alone parses.
- **TIR** (`tir/typecheck.rs` or `exhaustiveness.rs` tests, with `TestCase::new`):
  closed enum, all variants covered: no error (unchanged). Open enum, all named
  variants covered, no `_`: `NonExhaustiveMatch` (E2066). Open enum with a `_`
  arm: no error and no `UnreachableMatchArm` warning. Open enum where the arms
  list every value of a small repr (`enum E(u8)` with all 256 would be long;
  use a typed 1-bit-wide-ish case through a macro-generated source, or skip if
  unwieldy and say so). A `local` destructuring or `==` use of an open enum
  compiles.
- **Lowering** (`tir/lower.rs` tests, run under wasmtime): the `f(7)` program
  above with `..` on `E` returns the `_` arm's value, where without `..` it
  traps.
- **Formatter** (`wx-fmt` tests): idempotence and comment placement, as above.
- **Examples**: `examples/hello_wasi` still prints and passes
  `node --no-warnings examples/test_memory_examples.mjs`.

## Out of scope

- Conversion functions or a `TryFrom`-style API between the repr and an enum.
- Changing what a *closed* enum does for an unlisted value (it traps in an
  exhaustive `match` today; a later change may make that checked at
  `transmute`).
- Any change to `wx-lsp`, which does not compile on this branch and must not be
  "fixed" as a side effect (`CLAUDE.md`, "Current state").
- Thesis text.

## Working notes for the implementer

- Baseline: 1317 `wx-compiler` and 73 `wx-fmt` tests pass; clippy is not clean
  (about 45 dead-code warnings, 8 `too_many_arguments`, one
  `large_enum_variant`): do not add warnings of your own, and do not try to
  clear the existing ones.
- Never edit `.snap` files by hand. A change to `std/main.wx` shifts byte
  offsets in snapshots; this task should not need one.
- Run `cargo fmt`, `cargo test -p wx-compiler`, `cargo test -p wx-fmt` and the
  clippy line from `CLAUDE.md` (`cargo clippy --workspace --no-deps -- -D
  warnings` fails on the existing warnings; compare against the baseline
  instead of expecting it clean).
- The user's tree has staged edits in `crates/wx-compiler/src/tir/signatures.rs`.
  Do not stash, reset or revert anything there; work in a git worktree if
  you can, and report if a change you need collides with theirs.
