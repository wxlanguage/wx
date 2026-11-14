# Reflection and derived traits

Status: exploration, 2026-11-14. Nothing is decided beyond the constraints
below, and nothing is implemented. Revisit once constant evaluation can call
functions and run loops (see "Prerequisite").

## Problem

Most programs need traits whose impl follows from a type's fields: `Debug`,
`Hash`, `Serialize`. Writing them by hand for every struct is the boilerplate
Rust's `#[derive]` removes. WX needs a way for library code to write such an
impl once, for any struct, without a macro system.

## Constraints settled so far

- **No new keyword.** `derive Eq for T;` was considered and rejected: it would
  be an `impl` under another name (same type parameters, bounds, target,
  coherence), and it would have to decide what `impl Eq for T {}` then means.
  What is special about `Eq` belongs to the trait's declaration, not the site.
- **No macros.** A token-level stage has no types, adds a separate compile
  step, and leaves the LSP to map generated code back to source.
- **A generic body is checked once, against its bounds.** No Zig- or
  C++-style checking of each expansion: an error must be found where the
  library code is written, not where some user's type first instantiates it.
  This is the rule every other part of WX follows, and the one that rules out
  the most designs here.
- **No type-level list recursion** (GHC.Generics: a type's fields as
  `Cons<F, Cons<G, Nil>>`, walked by a pair of impls). It works with today's
  bounds and solver, but code written that way is hard to read and reason
  about.
- **Iteration is a plain loop.** Library code walks a type's fields with an
  ordinary `for`/`loop` over ordinary values.
- **Structure is reached through a trait.** A struct exposes its fields
  through some compiler-supplied trait or query, read like any other
  interface.

## Why `Eq` is not a derive

`Eq` looks like code generation from fields (lowering emits a field-by-field
comparison), but the checker relies on what it means, not on any generated
body: constant patterns compare by value, usefulness is exact, and `T: Eq`
promises that equal values are indistinguishable. A hand-written `eq` that
compares every field would not give the checker that, so the declaration is
"this type has structural equality", not "generate this code".
`impl Eq for T {}` stays as `notes/structural-eq.md` describes it. `Eq`
declares no members, so the empty body is just ordinary conformance (E2078
for anything written in it).

Rust found the same split the hard way: `#[derive(PartialEq)]` expands to an
ordinary impl, so constant patterns needed a hidden marker trait,
`StructuralPartialEq`, which only the derive implements.

## The direction: metadata as constants

A type's structure is comptime data, read through a compiler-supplied query
and held in constants. Constants are data in no memory (as `[u8; 5]` is until
a context places it), so the metadata needs no memory parameter and no
pointers:

```wx
struct FieldInfo(name: [u8; const_int], offset: const_int, ty: TypeId);

const FIELDS = info::<Point>().fields;   // an array of FieldInfo
```

- **A nested type is named by an id, not held inside.** A field holds its
  type's id (`ty: TypeId`), and `info(ty)` is asked again to go deeper, so the
  metadata is never recursive. This is Rust's shape (below).
- **A length nothing gives is a count of unknown value**, written
  `[u8; const_int]`, not `_`: `_` infers from an initializer or a use, and a
  trait declaration or a per-field name has none. It reads as shorthand for a
  hidden associated constant (`const LEN: const_int; const NAME: [u8;
  Self::LEN];`), which today's `Type::Const` already handles, rigid over an
  abstract `Self`. Placing it in an abstract memory as a slice still needs a
  representability fact (the E2133 case): someone has to state that the
  length fits every `PointerSize`.
- **Enums are the easy case**: no payloads, so an enum's structure is its repr
  and a table of variant names, an ordinary constant array of `Self`.

Names, counts, offsets and kinds are then ordinary constant evaluation.

## The open problem: reading a field's value

The metadata has one type, but the values it describes do not:

```wx
for field in info::<Self>().fields {   // every element is a FieldInfo
    write_name(w, field.name);         // a constant, fine
    self.[field].fmt(w);               // i32 on one pass, heap::&[u8] on the next
}
```

These three cannot all hold:

1. the loop body is checked once;
2. each field is used through its own type's impl (a `Char` field prints as a
   character, a `Fraction` as `1/2`);
3. nothing new is added to the type system.

Checking once means the body sees the field's value as some abstract `V`, and
calling `V::fmt` needs `V: Debug` in scope. Every bound WX can write is about a
type that can be named, and this `V` ranges over a list whose length depends
on `Self`. Neither an associated type (one value per impl) nor a tuple of the
field types (`(A, B): Debug` cannot imply `A: Debug` without an implied bound,
and no trait holds for a tuple just because it holds for every element) can
supply it. The fact has to come from somewhere new, so one of the three
gives:

- **Give up 2 (type erasure).** Read a field's bytes at its `offset` by its
  kind's width. With nothing new, this gives a derived `Hash`, a layout dump,
  or a `Debug` that prints integers and recurses into structs, but it ignores
  every impl a field's type defines. This is a weaker derive than Rust's.
- **Give up 2 for now, add dispatch later.** From a value back to an impl is a
  vtable: a table of function references per type. WX's Wasm design is heading
  there anyway (tables, `funcref`, `call_indirect`,
  `notes/wx-tables-references-design.md`). With it, a field's metadata could
  carry its type's entry for a trait, and the plain loop could call it. Go's
  `fmt` bridges the same gap with a runtime interface check.
- **Give up 3 (a per-field requirement).** A signature states that every field
  satisfies some clauses. The body is checked once with the field abstract
  under them, and each use proves them for every field of the concrete type.
  This is not checking per expansion: only the stated requirement is proven
  per field, as any bound is proven, and a failure names the field ("field
  `name` of `Point`: `heap::&[u8]: Debug` is not satisfied"). The design
  already has this for one trait: an `Eq` impl requires every field to be `Eq`
  under the impl's bounds (`notes/structural-eq.md`), proven by the compiler.
  This option would let library code state such a requirement, where `Eq`'s is
  fixed by the compiler. How to spell it in a binding block is open
  (`each Value: Debug` was one placeholder, not a proposal).

Undecided. The per-field requirement keeps the strongest derive. Erasure and
dispatch add nothing to the type system now.

## Other open questions

- **Is exposing structure opt-in?** Generic code that reads a type's metadata
  reads its private fields too. serde avoids this because its generated code
  lives in the user's crate. Exposing structure is a promise (the `Eq` note's
  "facts are derived, promises are declared"): it shows the representation and
  makes changing it a breaking change. That argues for an empty impl
  (`impl Fields for Point {}`) over metadata every type has.
- **Value or place.** A field read by value works only for a `StackValue`. A
  struct holding an array needs its fields reached as places through
  `self: M::&Self`.
- **Construction.** A derived deserializer needs to build a value from its
  fields, which meets the constructor's rule (accessible only where every
  field is).
- **Per-field options** (serde's `#[serde(rename = "..")]`). Attributes carry
  no type-system meaning, but a library's meaning is a separate question. The
  alternative is no per-field knobs, with a hand-written impl as the escape
  hatch.
- **The opt-in spelling.** A trait's default method can require more of
  `Self` (`func as_slice<Self: Array where { .. }, M: Memory>`), so
  `impl Debug for Point {}` can use a default body that reads `Self`'s
  structure. A derive needs no syntax of its own. What the default body
  requires depends on the open problem above.

## Prerequisite

Constant evaluation (`tir/eval.rs`) handles literals, primitive operators,
references to other constants and struct construction. A call is not a
constant, and neither is a loop. Metadata held in constants is only useful
once comptime code can call functions, run loops and index arrays, so that
comes first (`notes/tir-constant-evaluation.md`).

## Rust, for comparison

- **Stable `TypeId`**: `TypeId::of::<T>()` is an opaque 128-bit hash of the
  type, used for `==` and hashing, and mainly by `dyn Any` downcasting (the
  vtable stores `type_id()`, and `downcast_ref::<T>()` compares it). It
  requires `T: 'static`, because lifetimes are erased and two types differing
  only in a lifetime would share an id. WX has no lifetimes, so it would not
  need that restriction, but without trait objects it has nothing to downcast.
- **Nightly reflection** (`#![feature(type_info)]`, oli-obk's "reflection and
  comptime" goal): `TypeId::info()` is a `const fn` returning a `Type` value
  (kind, fields), with each field's type again a `TypeId`. It is
  compile-time only, and it panics if called at runtime. It is value-level:
  from a `TypeId` there is no way back to a type to bound or call a trait on,
  which is the open problem above, and why Rust couples reflection with
  comptime and generic consts.
- Swift checks pack expansions once against a pack's bound (`each T:
  Equatable`, SE-0393; pack iteration, SE-0408), which is the per-field
  requirement in another form.

Sources: [Reflection MVP, rust-lang/rust#146923](https://github.com/rust-lang/rust/pull/146923),
[design meeting 2026-04-29](https://hackmd.io/@rust-lang-team/BJAklnkRbl),
[rust-lang/rust#152381](https://github.com/rust-lang/rust/pull/152381).
