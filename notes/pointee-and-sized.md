# `Pointee` and `Sized`

Status as of 2026-11-25: **designed, nothing implemented**. A follow-up to
`slices-and-untyped-constants.md`, which settled most of the ground on
2026-10-30/31 and stays the reference for it: `Sized` with untyped `SIZE`
and `ALIGN` ("Sized"), rectangular nested slices and any number of unsized
fields ("Unsized fields"), layouts as expressions over the metadata
("Layouts are expressions"), and metadata named on the pointer ("The
`Pointer` trait"). This note records what a discussion on 2026-11-24/25
adds and where it revisits those decisions.

## What changes

1. **Metadata moves to the pointee**, as a generic associated type over the
   address width. The 2026-10-31 decision kept it on `Pointer` because the
   pointee does not know the memory; but the only thing a pointer
   contributes is its `Size`, so the metadata is a function of the pointee
   and a `PointerSize`, which is what a generic associated type expresses.
2. **`Sized` extends `Pointee`**: a pointee whose metadata is `()` and whose
   size is known at compile time.
3. **Infinite types** are named as a class: neither `Pointee` nor `Sized`,
   caught where one of them is proved, not by a declaration check.
4. **An unsized pointee's size is a trait function**, `Pointee::size`, the
   user-facing counterpart of the compiler's layout expressions.

## Classes of types

| Class | Examples | `Pointee` | `Sized` |
|---|---|---|---|
| compile-time sized | `u32`, `(i32, u8)`, `[u32; 4]`, `M::&[u8]` | yes | yes |
| runtime sized | `[T]`, `[[u8]]`, `[[u8]; 4]`, `Message(header: u32, payload: [u8], checksum: [u8])` | yes | no |
| infinite | `struct A(a: A)`, `struct A(w: W<A>)`, `struct A(a: [A; 2])` | no | no |
| not in linear memory | `funcref`, `func(A) -> R` | no | no |

A runtime-sized type's size is a function of its pointer's metadata. A slice
of slices is rectangular: every element shares one inner metadata, so
`[[u8]]` with `(rows, cols)` is a matrix with runtime dimensions. Jagged data
is `[M::&[u8]]`, a slice of pointers.

An infinite type is ill-formed rather than a kind of value. A pointer to one
may still be written (`heap::*A`); everything that needs its layout fails.

The last class is why the name matters (see "Naming"): such a type may
later be the pointee of a GC reference while never living in linear memory.

## The traits

```wx
/// A type that can live in linear memory behind a pointer. Its size is a
/// function of the metadata the pointer carries, its alignment a constant.
pub trait Pointee {
    type Metadata<Size: PointerSize>: StackValue;
    const ALIGN: const_int;
    func size<Size: PointerSize>(metadata: Self::Metadata<Size>) -> Size;
}

/// A pointee whose size is known at compile time; its metadata is `()`.
pub trait Sized: Pointee {
    const SIZE: const_int;
}

pub trait Pointer: StackValue where {
    Repr = <(Self::Memory::Size, <Self::Pointee as Pointee>::Metadata<Self::Memory::Size>) as StackValue>::Repr,
} {
    type Memory: Memory;
    type Pointee: Pointee;
}
```

- Both are answered by the compiler, as `StackValue` and `Pointer` are;
  users cannot implement them. Refusing a written impl is not enforced yet,
  as for the other built-in traits, and is not urgent.
- `[T]`'s rule, hard-coded today in `compute_pointer_metadata`, becomes
  ordinary core code once generic associated types exist:

  ```wx
  impl<T: Pointee> Pointee for [T] {
      type Metadata<Size: PointerSize> = (Size, T::Metadata<Size>);
      const ALIGN: const_int = T::ALIGN;
      func size<Size: PointerSize>(metadata: Self::Metadata<Size>) -> Size {
          metadata.0 * align_up(T::size(metadata.1), T::ALIGN)
      }
  }
  ```

  Structs and tuples stay compiler-answered from their fields: offsets of
  unsized fields and the order of the counts.
- `T: Sized` implies `T::Metadata<S> = ()` for every `S`. That is a built-in
  fact of the solver, not a written `where { Metadata<_> = () }`:
  `generic-associated-types.md` refuses equality bindings over a GAT's
  arguments (decision 5), and nothing else needs them.
- The metadata becomes one type per `Size` rather than per memory, which
  removes the cost noted in "The `Pointer` trait": `<heap1::&T as
  Pointer>::Metadata` and `<heap2::&T as Pointer>::Metadata` are equal when
  both memories' `Size` is `u32`.
- `SIZE` and `ALIGN` stay untyped; a use states its range with the existing
  representability clause, as `Array::LEN` does (`T: Sized where { const
  SIZE: Mem::Size }`).
- No implicit bounds. A generic pointer to `T` states `T: Sized` or
  `T: Pointee`; nothing is assumed. Revisit only if the verbosity hurts.

## Naming

Open. `Pointee` reads naturally (`type Pointee: Pointee;` on `Pointer`) and
matches Rust's pointer-metadata naming, but says nothing about linear
memory, and a GC reference's pointee may be a type that never lives there.
Candidates:

| Name | For | Against |
|---|---|---|
| `Pointee` | short, matches `Pointer::Pointee` | ambiguous once GC references exist |
| `MemoryPointee`, `LinearPointee` | says where the value lives | longer; "linear" is jargon |
| `MetaSized` | says what it means (sized through metadata), Rust's proposed hierarchy (`Sized: MetaSized`) | a coined word |
| `SizedPointee` | — | every `Sized` type is a pointee, and it reads as the narrower trait |

`Sized` keeps its name.

## The size of an unsized pointee

`Pointee::size` is what user code calls; the compiler's layout expressions
("Layouts are expressions") are how it answers it for structs and tuples,
and what MIR lowers field offsets with. Uses, none urgent:

- **Copying**, sized or not, across memories (`memory_copy` takes bytes):

  ```wx
  func copy<T: Pointee, Src: Memory, Dst: Memory>(dst: Dst::*T, src: Src::&T) {
      memory_copy(transmute(dst), transmute(src), T::size(metadata(src)));
  }
  ```

  Today a caller writes `len * size_of::<T, Mem>()` by hand.
- **Freeing.** A free-list allocator needs the size back; a generic `free`
  computes the layout from the pointer instead of trusting the caller.
  Core's `Allocator` has no `deallocate` yet, and nothing in the examples
  frees single allocations.
- **Allocating an unsized struct**: from counts to a layout, then a pointer
  built with `from_raw_parts`. User code cannot do this by hand, since it
  cannot know where unsized fields start.

Core will also need the building blocks to make such pointers: a matrix
view over a flat buffer (`from_raw_parts` with `(rows, cols)`), and the
conversions from arrays (`[[u8; 4]; 3]` to `[[u8; 4]]` or to `[[u8]]`),
including which of them are implicit.

## Infinite types

Decided: infinite types are caught where `Sized`, `Pointee` or `StackValue`
is proved, at the use, not by a check on the declaration.

### Where they can be caught

A **declaration check** finds a struct that reaches itself when walked from
its own parameters (`struct A(w: W<A>)`, `struct S<T>(x: W<S<T>>)`): infinite
for every argument, so the bug is the declaration's and is reported there,
used or not. It never rejects a generic type that is only infinite for some
arguments (`struct W<T>(v: T)` is fine). Without projections every infinite
concrete type comes from such a declaration, since a written type is a
finite term. With them, a cycle can exist for one instantiation only:

```wx
trait Id { type This; }
struct S<T: Id>(x: T::This);              // fine in general
impl Id for u32 { type This = S<u32>; }   // S<u32> is infinite
```

which only a check **at instantiation** sees, where the projection
normalizes.

Checking at instantiation through layout alone was rejected while layout is
computed only in lowering: `wx check` and the language server would never
report an infinite type, an unused declaration never, and the error would
point at the use. With `Sized` and `Pointee` proved during checking, the
first objection goes: every position that needs a layout states one of
them, so an infinite type is an unmet bound in `wx check`. What remains is
that unused declarations go unreported and the error sits at the use; the
diagnostic shows the chain (`A` holds `W<A>`, which holds `A`) to point back
at the declarations. Accepted.

The declaration check (`check_struct_direct_recursion`, during signature
resolution) can then be removed. It is cheap to bring back if unused
declarations should be reported.

### The judgement

- **A cycle is a failure** (inductive), never an assumed success.
- **One walk, one cycle check** for `Sized`, `Pointee` and `StackValue`.
  `StackValue` cannot be a subtrait of `Sized` (`funcref`), and today it is
  the one with no guard: `struct A(w: W<A>)` used as a parameter overflows
  the stack in `wx build`.
- **Everything stored inline is followed**: struct and tuple fields, array
  and slice elements, with type arguments substituted. Pointers stop it.
  `struct A(x: u32, tail: [A])` is infinite too: its metadata would contain
  its own metadata.
- **Projections are normalized** first, which the declaration check, running
  before signatures are complete, cannot do.

### Layout's walk as the judgement

"Sized" in `slices-and-untyped-constants.md` makes `layout.rs`'s walk the
judgement. As written today (`Semantics::piece`, `aggregate_piece`) it does
not fit yet:

- It answers `None` ("unknown") for type parameters, projections, slices,
  abstract array lengths and memories whose `Size` is not known, and
  returns at the first unknown field: `struct S<T>(t: T, s: S<T>)` would
  never reach `s`. Unknown is not finite: the judgement needs three answers
  (sized, not sized, or rigid until the type is known) and keeps walking
  past a rigid part.
- A cycle comes back as `SolverError::Poisoned`, the same error as an error
  type, with no path. The judgement needs a cycle verdict carrying the chain
  of fields, as the solver's `Verdict::Cyclic` does for projections.
- Its cache keeps only concrete aggregates, which is right for layouts but
  means a generic judgement is not cached there; the solver's own trait
  cache is the place.

Once checking guarantees finite types, reaching an aggregate already on
layout's `visiting` stack cannot happen in a checked program and becomes a
panic, instead of today's silent `Poisoned` that turns into a lowering panic
("lowering without an error diagnostic produces MIR").

### Finiteness as a proof the walks take

Decided 2026-11-25, planned. Interned types are finite terms; infinity only
appears when a type is expanded (fields substituted, projections
normalized). Every structural walk re-expands, so today every walk guards
itself (see "State of the code"). Instead, expansion and its guard are
separated from the computations over it:

1. **One judgement, in the solver.** `finite(ty)` answers `Finite`, `Rigid`
   (parameters or projections not resolvable in scope; asked again once
   known) or `Infinite(chain)`, the fields that close the loop. It is cached
   per interned type, as the solver's other queries are, and is the only
   code with a visiting stack and a depth budget. The budget covers
   projections whose arguments grow, where no exact repeat ever occurs.
   Its `Infinite` answer is the one cycle diagnostic `Sized`, `Pointee` and
   `StackValue` report.
2. **A proof token**, constructible only by the judgement:

   ```rust
   /// A type proven finite: expanding it terminates.
   #[derive(Clone, Copy)]
   pub(super) struct FiniteType(TypeIndex);
   ```

3. **One shared expansion step.** `shape(FiniteType)` normalizes one level
   and returns what a value is made of inline: fields with arguments
   substituted, array and slice elements, a pointer's pointee and memory, or
   a leaf. Its children are `FiniteType`s, since the parts of a finite type
   are finite; it is the one place a child gets the token without being
   judged again.
4. **Walks are plain recursion over `shape`.** The `StackValue`
   representation, layout, pointer metadata, `Pointee::size`, and any later
   walk take a `FiniteType`: no visiting stack, no budget, no cycle case,
   only their own answers (not sized, rigid). A walk that revisits a type is
   a compiler bug and panics.

The only place an infinite type can be noticed and reported is where a
`FiniteType` is obtained, and the type system enforces it: no walk runs on
an unproven type.

- A rigid type (`W<T>`, `T` abstract) is judged `Rigid`; the walks already
  keep rigid parts (a rigid `Repr`, metadata left a projection). The
  concrete type is judged when it appears, from the cache if seen before.
- Monomorphization forms types checking never saw. They go through the same
  judgement, so a projection-driven cycle surfaces there as a diagnostic
  (as rustc's "reached the recursion limit while instantiating"), not as a
  crash inside a walk.
- With projections, and later generic associated types, type-level
  computation is Turing-complete, so finiteness is not always decidable; the
  budget turns that into an error rather than a hang, in this one place.
- This is the cycle check of the `Sized`/`Pointee` judgement, not an extra
  stage, and can be done first: today's walks move onto `FiniteType` before
  `Sized` exists, which fixes the `W<A>` and `[A; 2]` crashes for all of them
  and replaces the interim declaration-check work.

### Cases

Rejected:

| Source | Through |
|---|---|
| `struct A(a: A)`; `struct A(b: B); struct B(a: A)` | fields |
| `struct W<T>(v: T); struct A(w: W<A>)`, in either order | a type argument |
| `W<W<A>>`, `(u32, W<A>)`, `P<u32, A>` | nesting |
| `struct G<T>(w: W<T>); struct A(g: G<A>)` | a generic chain |
| `struct S<T>(x: W<S<T>>)` | the struct's own parameters |
| `struct B(w: W<C>); struct C(w: W<B>)`, reported once | mutual, through arguments |
| `type WA = W<A>; struct A(w: WA)`, `type S = State; ...` | an alias |
| `struct A(x: u32, a: [A; 2])` | an array |
| `struct A(x: u32, tail: [A])` | a slice |
| `impl Id for u32 { type This = A; } struct A(x: <u32 as Id>::This)` | a projection |

Accepted:

| Source | Why |
|---|---|
| `struct W<T>(v: T); struct A(w: W<state::*A>)` | a pointer stops the walk |
| `struct Handler(s: state::*State); struct State(h: Handler)`, in either order | the same, through a struct |
| `struct G<T>(w: W<T>); struct A(g: G<u32>)` | the argument does not embed `A` |

Wrong argument counts (`W`, `W<A, A>`) report only the count.

### Interim

Until the trait judgement exists, the declaration check is what stands
between an infinite type and a lowering crash. Merged in #29: naming a struct
needs only its type parameters (`SignatureQuery::StructParams`), so a
pointer breaks a cycle in any declaration order. Written on 2026-11-24, not
merged: substituting a generic struct's type arguments into its fields
(the `W<A>` rows). Not written: arrays, slices and projections. The
finiteness judgement (step 0 of "Order of work") supersedes all of it.

## Decided

- Any number of unsized fields, as already decided; fields after an unsized
  one have runtime offsets, accepted as an explicit cost.
- The counts in the metadata are one per unsized field, in declaration
  order, whatever the layout.
- Field order follows the struct's `FieldOrder`. `Optimal` (the default)
  places every sized field first, alignment-sorted, so each keeps a constant
  offset, then the unsized fields in declaration order, as "Unsized fields"
  already decided. `#[fixed_order]` (`Fixed`) keeps declaration order for
  every field, so a sized field declared after an unsized one gets a runtime
  offset; the program asked for that layout.
- Overflow: `size` can wrap in `Size`. The invariant is that a valid
  pointer's value fits in its memory, so its size cannot exceed the memory's
  size; `from_raw_parts` with bogus metadata breaks it as a bogus address
  does. With overflow checks deferred, this is accepted and documented.

## Open

- The trait's name (see "Naming").
- Which array-to-slice conversions exist and which are implicit.

## State of the code (2026-11-25)

- `compute_pointer_metadata` (`solver.rs`) handles only `[T]`. Structs,
  tuples and arrays of unsized types fall into `_ => UNIT`, so
  `heap::&Message` is a thin pointer, unlike the table in "Unsized fields".
- `p[1][0]` on `heap::&[[u8]]` checks, and `wx build` reports E2085 "lowering
  a slice that is a field", which misnames the case. A struct field of
  slice type hits the same E2085.
- The declaration check misses arrays: `struct A(x: u32, a: [A; 2])` checks,
  and a function reading through a `heap::*A` makes `wx build` panic
  ("lowering without an error diagnostic produces MIR").
- `size_of` is replaced inline during lowering (`lower/intrinsics.rs`) and
  cannot be evaluated in a constant (E2042). Constant evaluation computes
  layouts only to place static data (`eval.rs`, `place_static`).
- Each structural walk guards against cycles on its own, and none tells an
  infinite type from an error type:

  | Walk | Guard | A cycle comes back as |
  |---|---|---|
  | `push_stack_elements` (`StackValue::Repr`, `solver.rs`) | a `visiting` stack and a depth against `recursion_budget` | `Overflow` or `Poisoned` |
  | `explain_non_stack_value` (its diagnostic) | its own `visiting` stack | `Poisoned` |
  | `piece` / `aggregate_piece` (`layout.rs`) | its own `visiting` stack and the budget | `Poisoned` |
  | `compute_pointer_metadata` | the solver's frames and budget, through projection normalization | the solver's verdicts |

  Even so, `struct W<T>(v: T); struct A(w: W<A>)` with `A` as an exported
  function's parameter passes `wx check` and overflows the native stack in
  `wx build`: some later walk has no guard, or the budget is deeper than the
  stack.
- Thinness of an abstract pointee is approximated by `StackValue` or `Array`
  (`compute_pointer_metadata`; core's `RawPtr<Mem, T: StackValue>`). Under
  this design the bound is `Sized`, and those signatures move to it.

## Order of work

0. The finiteness judgement and `FiniteType` ("Finiteness as a proof the
   walks take"), with today's `StackValue`, layout and metadata walks moved
   onto it and their own guards removed. Independent of the traits below,
   and the cases in "Cases" are its tests.
1. `Sized`, as in "Sized" of `slices-and-untyped-constants.md`: replaces
   `size_of`/`align_of`, gives array elements their stride, and is where
   infinite types are caught. Needs no generic associated types.
2. Generic associated types, as a language feature with its own tests
   (`generic-associated-types.md`, "Stages, if revived").
3. `Pointee` with `Metadata<Size>`; `Pointer`'s metadata derived from it;
   `[T]`'s rule moved to core.
4. Compiler-answered `Pointee` for structs and tuples with unsized fields,
   and arrays of unsized types; the gaps above.
5. Core: `copy`, `deallocate`/`free`, matrix views, array conversions, as
   their first users appear.
