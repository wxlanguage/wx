# Open sets of values: a struct with constants, not an open enum

Status: decided 2026-11-14. Change 2 (removing open enums) is done; Change 1
(an enum's repr as a field that may be read, revised the same day) is not
implemented. This replaces the 2026-11-05
design in this note (an enum body ending in `..`), which was implemented and is
to be removed. What it was, and why it was dropped, is in "The design this
replaces" below. What a constant pattern means, and so how `Errno`'s constants
are matched, is `notes/structural-eq.md`'s, decided the same day.

## Problem

A WX enum is a repr integer type plus named constants, erased to its repr
scalar: no tag, no layout of its own. Every enum is **closed**: its variants
are taken to be all its values, so a `match` that names every variant is
exhaustive, and the impossible case compiles to `unreachable`.

That is the wrong type for numbers that come from outside the module. The
motivating case is `examples/hello_wasi`: `fd_write` returns WASI's `errno`, a
`u16` of which the program names a handful of codes while the host may return
any other. The program has to be able to say "these are the codes I know, and
the type holds others", and the compiler has to make it handle the others.

## Decision

### `enum` is closed; a struct with constants is open

The two are different things, and the language spells them differently:

- An **enumeration** lists its values, and the list is the whole type. That is
  what `enum` means, and stays all it means.
- A **set of named values of a wider type** is a struct holding that type, with
  the names as constants in its inherent impl:

```wx
struct Errno(pub code: u16);

impl Errno {
    pub const SUCCESS: Self = Self(0);
    pub const BADF: Self = Self(8);
    pub const PIPE: Self = Self(64);
}

impl Eq for Errno {} // structural: `==` and the patterns compare `code`

func describe(e: Errno) -> u32 {
    match e {
        Errno::SUCCESS => 0,
        Errno::BADF => 1,
        Errno(code) => report(code), // every other code, with its number
    }
}
```

Being open is not a marker: it follows from what a struct already is. On the
current compiler this program needs `PartialEq` written out (`eq` comparing the
two `code`s) beside the empty `Eq` impl, and then checks and builds; the empty
impl alone is `notes/structural-eq.md`'s.

- **Exhaustiveness.** A struct has one constructor, and its constants do not
  cover it, so a `match` needs a catch-all, `Errno(code)` or `_`. Without one it
  is E2066 with the witness `Errno(_)`. Checked on the current compiler.
- **Construction.** `Errno(77)` builds any code, through the struct's ordinary
  constructor: no `transmute`.
- **Reading the number.** `local Errno(code) = e`, a struct pattern.
- **Who may do either** follows the struct rule: the constructor and the
  pattern are usable only where the field is visible, so `pub` on `code`
  decides whether other modules can make or read raw codes.
- **Representation.** A one-field struct is laid out as its field, so `Errno`
  is one `u16`, exactly what the enum was.

### Constant patterns need the type to be `Eq`

A constant pattern needs its type to be `Eq`, and `Eq` is structural equality,
implemented by the compiler and asked for with an empty impl
(`notes/structural-eq.md`). So `Errno::BADF` is matched as its value,
`Errno(8)`, and `==` on `Errno` is the same comparison. Whether a type has `Eq`
is still decided by an impl, never by the pattern that needs it: a struct
without the impl has no constant patterns, and a float field keeps a struct
from having one.

This first said the opposite: a constant pattern compared by a written `eq`,
and matching `Errno::BADF` as `Errno(8)` was rejected as equality synthesized
from the fields behind the user's back. That rejection stands for a
user-written `Eq`, which may compare anything; it does not apply once the type
asks for structural equality and `==` is that comparison.

What follows:

- The `match` compares values, with no `eq` call to inline.
- Exhaustiveness is unchanged: the struct's one constructor is not covered by
  its constants, so a `match` needs a catch-all.
- Usefulness compares constants by value: `Errno(8)` then `Errno::BADF` is
  unreachable.

**Opaque constants have an identity** (done 2026-11-14; once `Eq` is structural
it is needed only for constants with no value at check time, `T::MAX`).
`Ctor::Opaque(u32)`
(`tir/usefulness.rs`) is a position in a per-match table that
`check_match_usefulness` builds (`OpaqueKey` in
`tir/typecheck/exhaustiveness.rs`): the constant's evaluated value when there
is one, else the constant with its type arguments (which covers
`AbstractConstant`, `T::MAX`). An opaque constructor is covered by a wildcard
or the same identity, so `Errno::BADF` written twice, or `ALSO_BADF` of the
same value after it, is unreachable: it runs the same `eq` on the same
arguments, already false when control reached it. Constants with different
values say nothing either way (a written `eq` may equate them) and stay
possibly useful; they never complete a type. The usefulness pass only compares
identities and does not know what makes two constants the same.

This trusts `eq` to be deterministic, which WX does not enforce today: the
`Eq` contract is the guarantee, as reflexivity already is, until the effect
system can check it. Structural `Eq` removes the trust: the compiler owns the
comparison.

The derive this note first planned for (`struct Point: PartialEq + Eq (..)`,
generating the impls from the declaration) is replaced by the empty
`impl Eq for Point {}`, whose bounds are written like any impl's.

### Change 1: an enum's repr is a field, and may be read

Revised 2026-11-14: the repr is written and read as a struct field, with the
struct field grammar and `pub` deciding who may read it. This replaces the first
version of this change, under which the repr took no name and no `pub` and
could be read wherever the enum was visible.

```wx
pub enum Ordering(pub i8) { Less = -1, Equal = 0, Greater = 1 }
enum Signal(number: i32) { Hangup = 1, Interrupt = 2 }

local Ordering(n) = o;   // n: i8
local Signal({ number }) = s;
s.number
```

An enum is read as a struct over its repr whose values are a closed list known
at compile time. Reading the number is always safe: the value is one of its
variants, and the declaration writes every variant's number. It replaces
`transmute::<Ordering, i8>(o)`, which names the type and is only checked to
have the same representation; reading the field checks against the declared
repr.

**The repr is a struct field.** It is parsed as a `StructField` (a binding, a
`pub`, a type) where the enum's repr type is today, and each part means what it
means on a struct, restricted by the enum being closed:

| Part | Meaning | |
| --- | --- | --- |
| Type, `(i8)` | The repr. What a closed enum needs of it is `Repr: Eq + StackValue` (`notes/structural-eq.md`, "Enum reprs"); E2055 keeps it to integers until a wider repr is implemented | As today |
| Name, `(value: i8)` | The number is read by name, `o.value` and `Ordering({ value })`, as well as by position | Allowed |
| `_`, `(_: i8)` | No name, the same as `(i8)` (`Binding::name` is `None` for both), as on a struct field or a parameter | Allowed |
| `pub`, `(pub i8)` | Code outside the enum's module may read the number | Allowed; private by default |
| `mut`, `(mut value: i8)` | Writing the number in place | An error |

- **Construction from the repr is never allowed**, by position or by name,
  whatever the visibility: `Ordering(5)` and `Ordering({ value: 5 })` are an
  error of their own (a closed enum is not built from its repr: use a variant,
  or a struct if every number is valid). Building a value from a number is the
  one thing that could break "the variants are all its values"; reading one
  cannot.
- **`pub` decides who may read the number**, as it decides who may use a struct
  field. On a struct it grants construction and reading; on an enum it grants
  reading only, because being closed removes construction whatever the
  visibility, so `pub` grants what the type allows and keeps one meaning.
  Without `pub` the enum's module and its descendants may read it (the
  default visibility, `CLAUDE.md`), elsewhere it is the private-field error
  (E2076) for the pattern and the field access alike. Private by default
  because seeing the numbers in the declaration is not the same as their being
  API: if any module can read them, renumbering the variants breaks code, as
  `e as i32` makes every Rust enum's discriminants public whether the author
  meant it or not. An enum whose numbers are a contract says so: core's
  `pub enum Ordering(pub i8)` and `pub enum Bool(pub u8)`. `transmute` and a
  host import see the representation regardless, as for any type.
- **`mut` is an error**, with a hint to assign a variant. Writing the number in
  place can store a value no variant names, and restricting the write to
  variants' values is assigning the enum (`o = Ordering::Less`), which already
  works. Whatever `mut` comes to mean on a struct field (it is parsed and not
  checked yet), it has nothing to mean here.
- **What a pattern takes inside.** A binding or `_` only, to start with. A
  literal (`Ordering(-1)`) would work, since usefulness already reasons about
  integer values, but it is a second way to write `Ordering::Less`.
- **In a `match`,** `Ordering(n)` matches every value: after all the variants
  it is unreachable (correct for a closed enum), and before some of them it is
  a catch-all that binds the number.
- **Namespace.** Decided: the enum's name is in the value namespace too, as a
  struct's is (so it may not share its name with a function or a struct in the
  same scope). `E(n)` then resolves as a struct pattern does, `E(x)` reaches the
  construction error (E2142), and a bare `E` is "expected a value, found enum"
  (E2110).
- **Field access** `o.value` is a read of the one field, as on a struct; there
  is no positional access (`o.0`), as there is none on a struct or a tuple.
- **Several fields** are the deferred wider reprs below: written with this
  grammar, `enum Direction(dx: i8, dy: i8)` read as `d.dx` needs no syntax of
  its own when it comes.
- **Lowering** does nothing: the enum is already erased to that scalar, and the
  binding or the access is the same value. Core can use it
  (`local Bool(b) = x`); `Char` is a struct and has it already.
- **wx-fmt** prints the repr as it prints a struct field. The old
  `enum E: i8` form is removed (no longer read, and E1024 with it).

Step 1 (syntax) is done: the repr is parsed as a list of struct fields
(`List<StructField>`, empty when no parentheses are written), so several fields
need no new syntax when wider reprs come; until then the signature check reports
them unsupported (E2114). wx-fmt prints the list as a struct's, and `mut` is
reported by the signature check (E2141, `MutableEnumRepr`), since it is
well-formed syntax that means nothing here.

Step 2 (reading) is done. The repr's fields live in the same field arena as a
struct's (`Declarations::fields`, owned by a `FieldOwner`), and the struct
pattern and field access code reads either: `PatternKind::Fields { owner, .. }`
replaces `PatternKind::Struct`, and `ExprKind::FieldAccess` takes its owner
from the object's type. On an enum:

- a pattern of its fields holds no test (E2143, `TestInEnumRepr`, and the
  pattern is then the error pattern); usefulness counts it as `_`, so after
  every variant it is unreachable and before some a catch-all;
- a field access is always a value, never a place, so `=`, `op=` and `.&` on
  it are refused (E2013, "cannot assign to the repr of enum");
- reading needs every field read to be visible (E2076);
- lowering reuses the struct path: a pattern retypes the matched scalar as the
  repr, and a field read is the enum's value itself.

Step 3 (the construction error) came with it: `E(5)` and `E({ value: 5 })`
are E2142, `EnumConstructedFromRepr`.

Step 4 is done: core declares `pub enum Bool(pub u8)` and
`pub enum Ordering(pub i8)`. No `transmute` in core or the examples was
replaced: a read gives exactly the repr's type, and each of them converts to a
different one (core's `Bool` impls pass `self` to an `i32` intrinsic,
`Ordering::of` turns a `Bool` into an `i8` and builds an `Ordering` from a
number, which only `transmute` may, and the examples widen a `u8` or `u16`
repr to `u32`). Reading the repr replaces a `transmute::<E, Repr>`, which none
of them is.

### Change 2: remove open enums

The body `..` goes: `ast::EnumEntry::Rest` (the body is variants again),
`EnumDecl::open`, `CtorSet::Open` and its witness rendering, W2013
`MisplacedOpenMarker` and W2014 `RedundantOpenMarker` (and the
`check_discriminants` check that raises it), and wx-fmt's handling of `..`
(the normalization that moved it last and dropped repeats). A `..` in an enum
body becomes a parse error with a hint to use a struct with constants.

Done 2026-11-14: the body is a `List<EnumVariant>` again (`EnumVariantId`), and
a `..` is E1030 (`RestInEnumBody`), reported and skipped. `examples/hello_wasi`
and `examples/wasi` (`Errno`, `Fd`) are structs with constants; `Fd` is never
compared, so it has no `Eq`.
`examples/hello_wasi`'s `Errno` becomes the struct above, with its `Eq` impl
(and a written `PartialEq` until structural `Eq` is implemented) and its
`match` ending in `Errno(code) => ..` or `_ => trap()`.

## Why this, and not a marker on the enum

The previous design was semantically sound. What failed was the spelling: the
`..` sat after the variants, so on a long enum the reader had to scan to the
bottom to learn something that changes how every `match` on it is written. The
search for a better spelling ran into three constraints:

- **No new keywords.** That rules out `open enum`.
- **No attributes for meaning.** An attribute says how a declaration is
  compiled or laid out, never which programs are well typed. The test: delete
  it, and no program changes whether it checks or what it means. `#[inline]`
  passes; `#[fixed_order]` changes byte offsets, which matter to a host sharing
  memory, but no expression's type or meaning; `#[memory_limits]` configures
  the module. Openness fails the test both ways (an exhaustive `match` stops
  being one, `_` arms become reachable or unreachable, `Errno(5)` becomes
  valid), so `#[open]` is out.
- **Punctuation in the header** (`enum Errno(u16, ..)`, `enum Errno(..u16)`,
  OCaml's `[> ..]` delimiters as `{> .. }`) either reads as something else (more
  fields, a range, a token found nowhere else) or, written as a row-style tail
  (`{ A = 0, ..u16 }`), moves the repr back to the bottom.

Haskell's answer is the one that needs no marker: an open set of codes is a
newtype with pattern synonyms (`newtype Errno = Errno Word16`,
`pattern Success = Errno 0`). The type is the whole integer, and the names are
names for some of its values. WX can say the same with what it has, a struct,
its inherent impl's constants, and an `Eq` impl that lets them be patterns.

Under structural `Eq` the two forms are one idea, named values of an `Eq` type:
a struct with an `Eq` impl and constants is open, an enum over an `Eq` repr is
closed (`notes/structural-eq.md`, "Enum reprs").

What it costs: each name is longer to write (`pub const BADF: Self = Self(8)`
against `Badf = 8`), the type needs its `Eq` impl, and the enum's checks on its
values (duplicate values, the anchor auto-increment requires, E2071) do not
apply to constants. Both are acceptable for the few types whose values come
from outside the program, and a closed enum, the common case, is unchanged.

Also considered and rejected:

| Option | Why not |
| --- | --- |
| A struct with a body of named values, `struct Errno(pub code: u16) { SUCCESS = 0 }` | It is the inherent impl's constants written inside the declaration: a second way to declare them, for brevity only. |
| A catch-all variant carrying the number (`Unknown(u16)`) | Enums are erased to their repr; a payload needs a layout and a tag. |
| Trailing `_`, as in Zig (`enum(u16) { a = 0, _ }`) | The placement problem of `..`, and `_` reads as an unnamed variant. |
| `..` kept, placed first by the formatter | Visible, but against how `..` reads everywhere else in WX (last, "and the rest"), and still a marker for something a struct already is. |

## Deferred: enums over a wider repr

An enum whose repr is more than one integer, `enum Direction((i8, i8)) {
North = (0, -1), .. }` or `enum Color(Rgb) { Red = Rgb(255, 0, 0) }` (the
closed counterpart of a struct with constants), was first rejected here. Under
structural `Eq` it has a precise meaning: what a closed enum needs of its repr
is `Repr: Eq + StackValue`, not an integer (`notes/structural-eq.md`, "Enum
reprs"); variants are distinct when their values differ, a `match` compares
structurally, and `local Direction((dx, dy)) = d` reads the pair (Change 1). So
it is deferred, to be implemented later, not rejected.

What stays to weigh when it is: such an enum is several scalars wide, so it
cannot be a `global` and comparing it compares every field; lowering cannot
switch on it with `br_table` directly (a small tuple could be packed into one
integer key, `(i8, i8)` in 16 bits); usefulness needs a constructor per variant
where `Ctor::Value(u64)` holds one scalar; and data per case is often still
better served by a closed integer enum and a method matching on `self`. Until
then E2055 keeps reprs to integers.

## The design this replaces

From 2026-11-05: an enum body could end in `..`
(`enum Errno(u16) { Success = 0, Badf = 8, .. }`), making the enum **open**:
its variants named some of its values and every value of the repr was valid.
`ctor_set` gave it `CtorSet::Open`, the variants plus one constructor for the
rest that only a wildcard covered, so a `match` needed `_` even with every
variant named; witnesses named the uncovered variants and then `_`. The parser
took `..` as an entry anywhere, any number of times; the signature warned about
one not last (W2013) or repeated (W2014), and `check_discriminants` about one
made redundant by variants naming every value (W2014). Representation and
lowering were unchanged. Its weakness was the one described above, and
`transmute::<u16, Errno>(x)` was still how a host's number became an `Errno`.

## Tests

Write each where the code under test is (`CLAUDE.md`, "Testing patterns").

- **The struct form** (works today; pin it): the `describe` program checks;
  without the catch-all it is E2066 with witness `Errno(_)`; without the `Eq`
  impl it is E2063. Lowering (`tir/lower.rs`, under wasmtime):
  `describe(Errno(77))` takes the catch-all.
- **Change 1**: `local Ordering(n) = o`, `Signal({ number })` and `s.number`
  give the variant's number at runtime; `Ordering(5)` and
  `Ordering({ value: 5 })` as expressions are the new error; `Ordering(n)`
  after every variant is unreachable and before them a catch-all; a pattern
  other than a binding or `_` inside is refused; outside the module, reading a
  repr without `pub` is E2076 and with `pub` is fine; `(mut v: i8)` is the
  error; `(_: i8)` is `(i8)`; wx-fmt round-trips each form.
- **Change 2**: a `..` in an enum body is the parse error; the parser, TIR and
  wx-fmt tests for open enums are removed with the code.
- **Examples**: `examples/hello_wasi` checks, builds and prints.

## Documentation

- `CLAUDE.md`: the enums bullet under "Language features" gets the repr as a
  field (name, `pub`, reading it, no construction, no `mut`).
