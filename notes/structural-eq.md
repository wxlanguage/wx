# `Eq` is structural equality, implemented by the compiler

Status: decided 2026-11-14, not implemented. It changes what a constant
pattern means, so `notes/open-enums.md` builds on it.

## Problem

Today both equality traits are ordinary user traits (`core/main.wx`):
`PartialEq` has a written `eq`, and `Eq: PartialEq {}` is a marker that
promises that `eq` is an equivalence relation. A constant pattern compares by
that `eq` (`check_pattern_equality`, `tir/typecheck/patterns.rs`), so:

- The checker cannot know what a constant pattern matches. `Errno(8)` and
  `Errno::BADF` (whose value is `Errno(8)`) may or may not be the same pattern,
  depending on what `eq` compares (`a % 4 == b % 4` is a lawful `Eq`), so
  usefulness treats every such constant as opaque (`Ctor::Opaque`) and can only
  tell when the same constant is written twice. Even that trusts `eq` to be
  deterministic, which nothing checks until the effect system exists.
- A set of constants can never make a `match` exhaustive.
- A `match` lowers to a chain of `eq` calls, cheap only once inlined.
- `==` on any type with a written impl means whatever the impl says, and a
  pattern means the same, so nothing separates "these are the same value" from
  "these compare equal by some rule", the shallow address check of a pointer
  included.

## Decision

### Two traits, two meanings

- **`PartialEq` is the `==` operator**, an operator trait like `Add`. Users
  write it, and it promises nothing beyond its signature: it may be
  non-reflexive (floats, `NaN`), compare contents through a pointer, or ignore
  fields.
- **`Eq` is equality of the type's structure**: two values are equal exactly
  when their fields are, down to integers compared bit for bit. The compiler
  implements it. For a type that is `Eq`, the compiler also supplies its
  `PartialEq`, so `==` is the same comparison, and a type has one `==`, never
  two that could disagree.

`Eq: PartialEq` stays the supertrait relation, with a sharper meaning than
Rust's: `T: Eq` tells generic code that `==` is reflexive, symmetric,
transitive and deterministic, and more: equal values are indistinguishable, no
function can tell them apart. A hand-written equivalence (Rust's custom `Eq`)
never gives that last property: `Fraction(1, 2) == Fraction(2, 4)`, but
`numerator()` differs.

### Who is `Eq`

| Type | `Eq`? |
| --- | --- |
| Integers | By compiler rule |
| An enum | By compiler rule: it holds one of its variants' values, and its repr is `Eq` (see "Enum reprs") |
| A tuple | By compiler rule, when every element is `Eq` |
| A struct | When it has an `Eq` impl (below) |
| `f32`, `f64` | Never. They keep their written `PartialEq` (IEEE comparison) |
| A pointer, a slice, an array | Never (see "Three questions") |
| `funcref`, `func(A) -> R`, a function's item type | Never |

`Bool` is an enum, so it is `Eq` by rule. `Char` is a struct, so core writes
its impl. Core's written `PartialEq` and `Eq` impls for the integers and
`Bool` go away.

### A struct declares `Eq` with an empty impl

```wx
struct Errno(pub code: u16);
impl Eq for Errno {}

struct Pair<T>(a: T, b: T);
impl<T: Eq> Eq for Pair<T> {}
```

- **The impl has no body**: a member in it is an error. The compiler supplies
  `==` (comparing every field, in declaration order) and with it `PartialEq`.
- **Every field must be `Eq` under the impl's bounds.** The bounds are written,
  never implied from the fields: without `T: Eq` above, `a: T` is an error
  ("`T` is not known to be `Eq`: require `T: Eq`"), as `func test<T>(x:
  Foo<T>)` is E2098 asking for `T: StackValue`. A field of a type that is never
  `Eq` (`f32`, a pointer) is an error naming that field.
- **The condition belongs to the impl, not to the type.** `Pair<f32>` is a valid
  type; it is just not `Eq`. Writing the bound on the struct
  (`struct Pair<T: Eq>`) would make `Pair<f32>` ill-formed everywhere, and a
  generic wrapper (an option, a range) could then not be both `Eq` when its
  contents are and usable when they are not. Rust's `impl<T: Copy> Copy for
  W<T> {}` is the same shape: an empty impl of a trait whose meaning the
  compiler fixes and checks against the fields.
- **A written `impl PartialEq` for a type with an `Eq` impl is an error**: the
  compiler supplies it.
- **Without an `Eq` impl**, the author may write `impl PartialEq` (the type has
  `==`, but no constant patterns and no `T: Eq`) or nothing (the type has no
  `==`).

This keeps the coherence rule (one impl per trait per type constructor), and
the syntax is the one core already uses (`impl Eq for u8 {}`). What changes is
what the empty impl means: not a promise about a written `eq`, but a request for
the compiler's.

### Facts are derived, promises are declared

`StackValue` (with `Pointer`, `Slice`/`Array` and a future `Sized`) is also
implemented by the compiler, but needs no impl, and that is deliberate:

- `StackValue` is a fact about the representation, which Wasm values a type is.
  The fields decide it, two authors of the same struct could not choose
  differently, and opting out would only make a type that cannot be a
  parameter.
- `Eq` is a promise about meaning, when two values are the same. Authors of the
  same struct may well choose differently (`Fraction` with canonical fields
  wants it, a ring buffer whose head offset varies does not), and declaring it
  commits an API: patterns and `T: Eq` code are written against it, so removing
  it is a breaking change, and it shows the representation to every module
  that compares.

Rust draws the line in the same place: `Send`, `Sync` and `Sized` are derived,
`Copy` is declared. If ownership comes, "may be duplicated" is a promise of the
`Copy` kind and a trait of its own, not part of `StackValue`.

### Three questions, three spellings

A pointer has no `==`, so neither of the two things it could mean is asked by
accident:

```wx
e == Errno::BADF                         // the same value: Eq types only
address(p) == address(q)                 // the same place: compare integers
into_raw_parts(a) == into_raw_parts(b)   // the same slice: address and length
p.* == q.*                               // equal contents of one value
name.contents_eq(other)                  // equal contents of a slice
```

- **Identity** needs nothing new: core's `address`, `metadata` and
  `into_raw_parts` return a memory's `Size` and the metadata, integers and
  tuples of them, which are `Eq`. Spelling the conversion out is what makes a
  shallow check read as one.
- **Contents** of one value: load it, then compare (`T: PartialEq`, whatever
  `T`'s `==` means).
- **Contents** of a slice or an array, which cannot be loaded: a default method
  of `Slice`, requiring `Value: PartialEq` (so a slice of floats compares as
  `==` does on each element):

  ```wx
  func contents_eq<Self: Slice where { Value: PartialEq }, M: Memory>(
      self: M::&Self, other: M::&Self,
  ) -> Bool
  ```

  The name is a placeholder. Both slices are in one memory, since comparing
  lengths in two memories compares an `M::Size` with an `N::Size`.
- `==` on a pointer is the ordinary E2046 ("the trait bound `heap::&[u8]:
  PartialEq` is not satisfied"), with a help naming `address(..)` for identity
  and `.*`/`.contents_eq(..)` for contents. Users cannot write `PartialEq` for a
  pointer: an impl's target is a nominal type.
- A struct holding a pointer is never `Eq`; its author may write `PartialEq`
  and decide there whether it means identity or contents.

### Constant patterns

Only a constant of an `Eq` type may be a pattern. Any other is an error, with a
hint to compare with `==` in an `if` (WX has no match guards). The constant is
then compared by its value: `Errno::BADF` is the pattern `Errno(8)`. This is not
equality synthesized behind the user's back, the reason `notes/open-enums.md`
rejected it while `Eq` was user-written: the type asked for structural equality
with its impl, and `==` is the same comparison.

What follows:

- **Usefulness is exact** for constants with a value. `Errno(8)` then
  `Errno::BADF` is unreachable, and so is `Errno::BADF` written twice, now
  without trusting `eq` to be deterministic. Constants of an enum or integer
  type are `Ctor::Value`s already; a struct constant is its constructor applied
  to its fields' values.
- **A constant still opaque** is one with no value at check time: a trait's
  constant over an abstract type (`T::MAX` for `T: Eq`). `Ctor::Opaque` and its
  identity table (`OpaqueKey`, `tir/typecheck/exhaustiveness.rs`) stay for
  those only.
- **Lowering** compares the scrutinee's scalars with the constant's, with no
  call, and can switch on a single scalar with `br_table`.

### `Ord` agrees with structure

`Ord: PartialOrd + Eq` (`core/main.wx`) stays written by hand, since the order
is a choice (fields in any order, reversed, versions by major then minor). Its
contract, `cmp` is `Equal` exactly when `==` holds, now means exactly when the
structures are equal: ordering people by age through `Ord` violates it, as it
does in Rust. Ordering by a key is a comparator argument (`sort_by`), not an
`Ord` impl.

### Enum reprs

E2040 requires an enum's repr to be in core's integer typeset
(`report_enum_repr_not_integer`, `tir/signatures.rs`). What a closed enum needs
of its repr is `Eq`: its variants' values must be distinct, a `match` compares
the scrutinee with each, and the checker compares them as constants. A float
repr is wrong because `NaN` makes "distinct" and "matches its variant"
meaningless, not because it is not an integer. The stated rule becomes
`Repr: Eq + StackValue`, and the implementation keeps accepting integers only
until there is a use for wider reprs.

With it, an open and a closed set of values are the same idea: named values of
an `Eq` type. A struct with an `Eq` impl and constants is open (the names cover
some values, a `match` needs a catch-all); an enum over an `Eq` repr is closed
(the names are all the values). A repr wider than one integer,
`enum Direction((i8, i8)) { North = (0, -1), .. }` or
`enum Color(Rgb) { Red = Rgb(255, 0, 0) }`, is meaningful under this rule and
deferred, not rejected (`notes/open-enums.md`, "Deferred").

## What it costs

A type whose `==` is a lawful equivalence relation but not equality of its
structure cannot be `Eq`. That shows in generic code bounded by `Eq` (lookup,
deduplication, map keys), in `Ord` and in constant patterns.

- **Several encodings of one value** (a fraction, an angle modulo 360, unused
  bits): make the representation canonical, which private fields enforce.
  `Fraction::new` reduces by the gcd and nobody outside builds `Fraction(2,
  4)`; structural equality is then the right one. Normalizing costs work at
  construction instead of comparison; a type that cannot normalize cheaply (a
  ring buffer) offers a method or a written `PartialEq`, not `Eq`.
- **Fields that are not part of the value** (an entity's debug name, a cached
  hash): such a type usually holds a pointer and is not `Eq` anyway; code
  compares and keys by the field that is the identity (`a.id == b.id`).
- **Containers with keys that are not values.** A string is a slice, never
  `Eq`, so a map bounded by `K: Eq` cannot take string keys at all. A container
  whose keys need an equivalence takes it as a parameter, a zero-sized strategy
  type implementing a trait (C++'s `KeyEqual`):

  ```wx
  trait Equivalence {
      type Item;
      func same(a: Self::Item, b: Self::Item) -> Bool;
  }
  ```

  The custom equivalences Rust writes as an `impl Eq` (case-insensitive and the
  like) are these: named, chosen where the container is used, several per type.
  Not designed yet; it comes with the first container.
- **`transmute` can build a non-canonical value**
  (`transmute::<(i32, i32), Fraction>((2, 4))`), for which structural equality
  is then wrong. This is the class of unmarked raw pointers, out of scope until
  the effect system, not an oversight here.

The loss falls mostly on types holding pointers, which are not `Eq` once a
pointer has no `==`. Small value types, the ones matched and used as keys, can
nearly always be canonical.

## Implementation

1. **Core**: `Eq`'s doc comment says what it is; drop the written `PartialEq`
   and `Eq` impls for the integers and `Bool`; keep `f32`/`f64`'s `PartialEq`;
   `impl Eq for Char {}` stays and now means the structural one.
2. **Solver**: answer `T: Eq` and `T: PartialEq` structurally
   (`TraitImplLookup::Builtin`) for integers, enums and tuples of `Eq` types;
   for a struct, select its `Eq` impl as usual and answer `PartialEq` from it.
3. **Conformance** (`tir/conformance.rs`): an `Eq` impl with a member; a field
   not `Eq` under the impl's bounds; a written `PartialEq` for a type with an
   `Eq` impl. New diagnostics, each pointing at what to change.
4. **Patterns**: a constant of a type that is not `Eq` is an error; one of an
   `Eq` type with a value lowers in usefulness as its value's constructor
   pattern; `Ctor::Opaque` only without a value.
5. **Lowering**: the compiler's `eq` compares scalar by scalar; a constant
   pattern compares values; an enum `match` is unchanged.
6. **Diagnostics**: E2046's help for `==` on a pointer.
7. **`Slice::contents_eq`** in core.
8. **`examples/hello_wasi`**: when `notes/open-enums.md`'s Change 2 turns its
   `Errno` into a struct, it gets `impl Eq for Errno {}` (written `PartialEq`
   and `Eq` impls in between, if Change 2 lands first).

## Tests

Write each where the code under test is (`CLAUDE.md`, "Testing patterns").

- A struct with `impl Eq` gets `==` and constant patterns; `Errno(8)` then
  `Errno::BADF` is unreachable; a set of struct constants never completes the
  struct, but an enum's variants still do.
- `impl<T: Eq> Eq for Pair<T> {}`: `Pair<u32>` is `Eq`, `Pair<f32>` is a valid
  type without `==`; without the bound, the field error.
- Errors: a member in an `Eq` impl, a field of a type never `Eq`, a written
  `PartialEq` beside an `Eq` impl, a constant pattern of a type with only a
  written `PartialEq`, `==` on a pointer (E2046 and its help).
- `f32` keeps `==`, has no `Eq`, and its constants are not patterns.
- Lowering, under wasmtime: `==` on an `Eq` struct, a `match` on struct
  constants, `contents_eq` on two byte slices.
