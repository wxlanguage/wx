# `StackValue`: a type's representation on the Wasm stack

Status as of 2026-10-29, branch `tir-refactor`: implemented in TIR (std,
`defs.rs`'s intrinsic slots, `Solver::stack_elements`/`stack_repr` in
`solver.rs`, tests in `signatures.rs`'s `stack_values`). Replaced
`ValueType`. MIR's stack order (declaration, not physical) is still to do
when MIR is revived.

## The trait

```wx
pub trait StackValue {
    type Repr;
}

pub typeset StackScalar { i32, i64, f32, f64, funcref }
```

`StackValue` is answered by the compiler from a type's structure, as
`ValueType` and `Call` are today; no impl of it is written anywhere. `Repr` is
how a value of the type sits on the Wasm stack, spelled with wx's own
primitives: a flat tuple of scalars, the scalar itself when there is one (wx
has no tuple of one), or `()` when there is none.

`ValueType` only said "this is one Wasm value". It could not say whether two
types are held the same way, which `transmute` and `as` need:

```wx
// reinterprets a value on the stack; changing a scalar (i32 -> i64) is an
// intrinsic's job
package func transmute<
    T: StackValue,
    U: StackValue where { Repr = T::Repr },
>(value: T) [unsafe] -> U;

pub trait Global {
    type Value: StackValue where { Repr: StackScalar };
}
```

`Repr` is not injective, as no associated type is: a call names `U`
(`transmute::<_, Meters>(x)`).

`funcref` is a std primitive (`pub type funcref;`, `TypeIndex::FUNCREF`):
a function reference of any signature, the untyped counterpart of
`func(A) -> R`, which is the typed shape. It only names a Wasm value for now;
converting it to a typed reference before a call, `v128` and other reference
types are left for later.

## What implements it

Every type except `!` and any type that contains `!` (`(u32, !)`,
`struct S(x: !)`). An uninhabited type has no representation: with
`Repr = ()`, `transmute::<(), !>` would make a value of it.

| Type | `Repr` |
| --- | --- |
| `u8`, `i8`, `u16`, `i16`, `u32`, `i32`, `bool`, `char` | `i32` |
| `u64`, `i64` | `i64` |
| `f32`, `f64` | `f32`, `f64` |
| `funcref`, `func(A) -> R` | `funcref` |
| an enum | its repr's |
| `M::*T`, `M::&T`, `M::*[T; N]` | `M::Size`'s (an address; the pointee does not matter) |
| `M::&[T]` | `M::Size`'s, twice (address, length) |
| a tuple or struct | its parts', flattened |
| `()`, a zero-sized struct, a function item, a memory or global handle | `()` |

So `Point(x: u32, y: u32)` and `(u8, u8)` both have `Repr = (i32, i32)`, and
`Meters(u32)` has `Repr = i32`.

`transmute` is unsafe: a `bool` from 2, a `char` from a surrogate, an enum
from an invalid discriminant, or a narrow integer whose high bits break an
invariant MIR keeps are the caller's problem.

## Order: declaration, not memory layout

A value on the stack is its fields **in declaration order**, flattened
pre-order, with zero-sized parts dropped. Memory layout (alignment-sorted, or
declaration order under `#[fixed_order]`) is a separate question and never
affects the stack. `#[fixed_order]` changes nothing about `Repr`.

The old MIR flattened in physical order (`ScalarTable` reuses the sorted
field list in `mir/layout.rs`), while the new `push_stack_elements` walks declaration
order. When MIR is revived, its stack order must follow declaration order.
Each `Scalar` keeps its memory `offset`, so loads and stores still land on the
right bytes; `field_starts` becomes indexed by declaration.

Why not physical order:

- **Swaps.** Under physical order `(u8, u64)` and `(u64, u8)` are both
  `(i64, i32)`, so transmuting one into the other is accepted and silently
  swaps the fields by type. `(u32, f32)` to `(f32, u32)`, with equal
  alignments, is rejected. Declaration order rejects both.
- **`#[fixed_order]`.** It would change a struct's `Repr` and break a
  transmute between it and the matching tuple.
- **Pointer width.** `Header<M>(len: u32, data: M::*u8)` would sort `data`
  first only in a 64-bit memory, so one generic type would put its fields in
  a different order per instantiation.
- **Layout changes.** Changing the sort, or adding niches or packing later,
  would change `Repr`s and so the meaning of transmutes that still
  type-check.
- **ABI.** Multi-value parameters and results are visible in imported and
  exported signatures. The host should see `(u8, u64)` as `(i32, i64)`, as
  written, without knowing wx's layout rules.

The stack has no padding or alignment, so physical order gives nothing there.

## Generic code

wx checks a generic body once, before instantiation, so a transmute in one
must hold with its parameters abstract:

```wx
func unwrap<T: StackValue>(w: Wrap<T>) -> T {
    transmute(w) // Wrap<T>: StackValue, <Wrap<T> as StackValue>::Repr == T::Repr
}
```

Read as a user-written trait, this works by ordinary impl selection. With
`impl<T: Layout> Layout for Wrap<T> { type R = T::R; }`, `<Wrap<T> as
Layout>::R` reduces to `T::R` in `unwrap`, because the impl applies to any
`Wrap<_>` and its requirement is assumed. `StackValue` behaves as if the
compiler wrote that impl for every type constructor, with its value the
flattening of the parts' `Repr`s. The compiler does not build such impls. It
answers both questions directly:

- **`X: StackValue`** holds when every part of `X` does (an abstract part by
  its assumptions), and no part is `!`. `Wrap<T>` holds under `T: StackValue`.
- **`<X as StackValue>::Repr`** normalizes by canonicalizing its self type,
  described next.

### Canonical self type

A flattening can't be represented as a plain tuple once a part is abstract:
substituting `T = (u8, u8)` into `(T::Repr, i32)` gives `((i32, i32), i32)`,
which is not flat, and a tuple can't flatten itself because a written nested
tuple must stay nested. A new type former (a type-level concatenation) would
fix that at the cost of another variant to flag, substitute, normalize and
format. Instead, the normal form is an ordinary projection whose self type is
canonical.

`<X as StackValue>::Repr` depends only on the flattened sequence of `X`'s
parts, so normalization rewrites `X` into a self type that flattens the same:

1. Walk `X` with `push_stack_elements`, in declaration order: nested tuples, structs
   and enum reprs are flattened, and zero-sized parts dropped.
2. Each concrete scalar becomes its `Repr` (`u8`, `bool` → `i32`; `u64` →
   `i64`).
3. For each abstract part `P`, normalize `<P as StackValue>::Repr`. If its
   assumptions reduce it (`T: StackValue where { Repr = i32 }`), splice the
   result in; otherwise keep `P` as one element. A pointer into an abstract
   memory contributes `M::Size`.
4. Collapse:
   - no abstract element: the flat tuple of scalars, which is the `Repr`;
   - one element and it is abstract: `<P as StackValue>::Repr`;
   - otherwise: `<(e1, e2, ..) as StackValue>::Repr`.

| Written | Normal form |
| --- | --- |
| `<Wrap<T> as StackValue>::Repr` | `T::Repr` |
| `<Pair<T, u32> as StackValue>::Repr` | `<(T, i32) as StackValue>::Repr` |
| `<(T, u32) as StackValue>::Repr` | `<(T, i32) as StackValue>::Repr` |
| `<Header<M> as StackValue>::Repr` | `<(i32, M::Size) as StackValue>::Repr` |
| `<Point as StackValue>::Repr` | `(i32, i32)` |

Two `Repr`s are equal when their normal forms are, with the comparison used
everywhere else (substitute, normalize, compare interned), so there is no
special case in bound checking, conformance or coercion. `unwrap` checks, and
so does a transmute between `Pair<T, u32>` and `(T, u32)`. Once `T` is
known the leftover projection reduces as any other:
`<((u8, u8), i32) as StackValue>::Repr` is `(i32, i32, i32)`.

**Sound:** each step replaces a part with one that flattens the same (a
scalar with its `Repr`, an abstract part with itself, a nested tuple with its
elements, a zero-sized part with nothing), so equal normal forms flatten
equally under every instantiation. **Incomplete** only as a trait system is:
`(T, U)` and `(U, T)` are not equal generically even though they are when
`T = U`.

## Implementation

- `std/main.wx`: `StackValue`, `StackScalar` and `transmute` (bodiless, no
  `unsafe` yet); `Global::Value: StackValue where { Repr: StackScalar }`;
  `PointerSize: .. + StackValue`, so an abstract memory's `M::Size` is a
  `StackValue` by declaration (see "Idempotence").
- `defs.rs`: `IntrinsicDefs::stack_value` and `stack_value_repr`, the latter
  found as `Call`'s `Args`/`Result` are.
- `Solver::stack_elements` (was `value_layout`) yields `TypeIndex` elements: a
  scalar (`is_stack_scalar`: `i32`, `i64`, `f32`, `f64`, `funcref`) or an
  abstract part assumed `StackValue`, standing for its `Repr`. `!` makes it
  `None`. A pointer into an abstract memory contributes `<M as Memory>::Size`
  (`push_address`), so `M::*u8`, `M::*u64` and `M::Size` are held alike.
- `find_trait_impl_query`: `X: StackValue` holds when `stack_layout` is
  known, as `TraitImplLookup::Builtin`.
- `Solver::stack_repr`, called from `reduce_projection`'s `Builtin` branch
  for `StackValue::Repr`: steps 1 to 4 above. `splice_repr` reads a part's
  normalized `Repr` back into elements (scalars, tuples of them, and `Repr`
  projections over a tuple or an abstract part); anything else keeps the part
  as it is. The collapse to one abstract element is `intern_tuple`'s own rule.
- The branch returns the projection itself when `stack_repr` gives it back:
  a canonical form is its own answer.

### Idempotence

Normalizing a canonical form runs `stack_repr` on its tuple again, which must
give the same tuple. That holds only if every element is itself a
`StackValue` by its declarations. A parameter is (it was assumed one to
become an element); `M::Size` is only because `PointerSize` declares it.

### Caching

Only a canonical form of several elements has a tuple self type, and no bound
can be written on such a projection (equalities constrain projections out of
parameters). A one-element form is `<P as StackValue>::Repr`, abstract. The
parts' assumptions are read while canonicalizing, under the request's own
scope (the tuple has a parameter), so nothing is cached across scopes.

### Known limits

- `Point::Repr` (unqualified) does not resolve: selection reads impls and
  assumptions, and no impl exists. `<Point as StackValue>::Repr` does.
- An equality that restates a `Repr` through itself
  (`T: StackValue where { Repr = <Wrap<T> as StackValue>::Repr }`) leaves the
  two sides as different unreduced projections, so a transmute across it is
  rejected. A user-written trait with the matching impl behaves the same:
  it is the solver's handling of a looping equality, not `StackValue`'s; the
  planned fix is an open question in `tir-check-pass.md`.
- A `<X as StackValue>::Repr` written as a part of another type is not
  itself assumed a `StackValue`.
- An untyped literal gives `T` no type: `transmute(5)` is "cannot infer
  type for type parameter `T`" (E2002), `transmute::<i32, _>(5)` checks.

## Not covered

Reinterpreting bytes in memory (reading an `M::*S` as an `M::*T`) is a
question about memory layout, not the stack, and would need its own check.
