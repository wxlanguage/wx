# Slices, untyped constants and representability clauses

Status as of 2026-11-01: steps 1–6 done (see "Order of work"), the rest
designed, not implemented. Settled in discussion on 2026-10-30; "Values are
`StackValue`s" (implemented 2026-11-01) replaced the `Slice`-bound rule.
Linked changes:

1. `[T]` and `[T; N]` become types of their own, a slice and an array: what a
   pointer points at, with no memory.
2. A length is a count: it has no machine type until it meets a memory.
3. A constant may be untyped, `const X: const_int = 4;`, used like a literal.
4. An abstract constant's representability is stated in a bound,
   `T: Array where { const LEN: u8 }`.
5. Array and string literals are arrays (`[const_int; 3]`, `[u8; 5]`),
   placed in a memory when coerced to a pointer; `{array}` and `{string}` go.
6. `Sized`, a compiler-answered trait with untyped `SIZE` and `ALIGN`: a
   type's layout in linear memory. It replaces `size_of`/`align_of`, and
   `Array::SIZE` becomes `Array::LEN`.

Generic constants (`const N<S: PointerSize>: S = 0`) stay planned as the
separate, bounded form; see the end.

## Naming

`[T]` is a slice and `[T; N]` an array, as Rust's reference names them; "a
slice" in the trait's sense is either (every array is a `Slice`, `Array:
Slice`), and the code says "slice or array" where it means both. `heap::&[u8]`
is "a pointer to a slice", never "a slice". The word *region* was used here at
first and dropped: in the literature (Tofte–Talpin, Cyclone, Rust's lifetimes)
a region is an area of memory, which is what wx calls a `memory`. Data not in
a memory yet (a literal, a constant holding one) is *placed* when its context
gives it a memory.

## Slices and arrays

Before the split, `Type::Slice { of, memory, ownership }` and
`Type::Array { of, length, memory, ownership }` were the pointer itself: a
slice value was the fat pointer, and `Slice`'s `Self` was `heap::&[u8]`.

After it:

- `[T]` is a run of values of `T` whose count is known only at runtime. It is
  unsized.
- `[T; N]` is exactly `N` values of `T`. It is sized (`N * size(T)` bytes),
  and its size does not depend on any memory.
- Neither is in a memory. Like `u32`, a slice is a shape; a memory comes in
  only with a pointer. `M::&[T]` is `Pointer { to: Slice { of: T }, memory: M,
  ownership: Shared }`, and `M::&[T; N]` is `Pointer { to: Array { of: T,
  length: N }, .. }`. The AST mirrors it: `&[T]` parses as a `Pointer` whose
  inner type is a `Slice`, and `[T]`/`[T; N]` parse anywhere a type does.
- A pointer is fat exactly when it points at `[T]`: the data pointer and a
  length of type `M::Size`. A pointer to `[T; N]` is thin; its length is in
  the type. `layout`, `Solver::stack_elements` and constant evaluation read
  this as `<P as Pointer>::Metadata` (see "The `Pointer` trait"); over an
  abstract pointee assumed `Slice` but not `Array` that stays rigid, a
  `StackValue` with no layout yet.
- A slice or an array is only ever behind a pointer, `[T; N]` included, and
  this is permanent: Wasm locals cannot be indexed at runtime (`local.get`
  takes an immediate), so an array in locals would be a tuple with constant
  indices or an O(N) dispatch per access. Native compilers keep "stack" arrays
  in a shadow stack in linear memory; wx has no ambient memory, so that is an
  `M::*[T; N]` from an allocator.
- A type held by value (a parameter, a result, a function type's parameter
  or result, a local, an ascription) is a `StackValue`, which no slice or
  array is, nor anything holding one: E2129 (`NotStackValue`), recorded as
  `TypeObligation::CheckValueType` where the type is lowered. A field, a
  tuple's element, a type argument, a constant's declared type, a type alias
  and a qualified path's root (`<[u8; 4] as Array>::LEN`) need nothing. See
  "Values are `StackValue`s".
- `[T]` and `[T; N]` will be well-formed only when `T: Sized` (see "Sized").
- One place rule covers fields and elements: each place step goes through at
  most one pointer, so `p.field` is `p.*.field` and `s[i]` is `s.*[i]`.

## Literals are arrays

An array or string literal is data not yet in a memory, so it has an array
type, and the literal pseudo-types `{array}` and `{string}` are gone:

```
[1, 2, 3]          : [const_int; 3]
[0; 16]            : [const_int; 16]
[0; N]             : [const_int; N]
[x; _]             : [T; _]          (the length is its context's)
"hello"            : [u8; 5]
```

- An array literal's element type is its first typed element's, or its first
  element's; placing checks every element against the target's.
- An expression whose type is a slice or an array (or a tuple holding one)
  waits for its context as an untyped literal does
  (`TypeInterner::needs_context`, from the `HAS_UNPLACED` flag, which only a
  tuple passes on): with an expected type it is coerced, and
  without one (`local x = "hi";`, a statement, a method's receiver) it is
  E2002, at the point an untyped literal is. Such data has no operators of its
  own (`"a" + "b"`).
- Coercing it to a pointer places it (`coerce_static`): it becomes static
  data in the pointer's memory, its elements take their type, and the pointer
  is thin (`M::&[u8; 5]`) or fat (`M::&[u8]`). Only shared targets, as before
  (the data is read-only). Placed, a repeat's count is checked against the
  memory's `Size`; evaluation reads it as a count.
- `M::&[u8; _]` learns its length from the literal's type.
- Only data in no memory is placed. A value that already has a type does not
  convert: `M::&[T; N]` to `M::&[T]` is `as_slice()`, as a function item does
  not become `func(A) -> R` by itself. An implicit unsizing coercion (only
  `M::&[T; N]` → `M::&[T]` and `M::*[T; N]` → `M::*[T]`, same memory, only
  where the expected type is known, never inside generic inference) is a
  possible later convenience.
- `Type::StringLiteral` and `Type::ArrayLiteral` are deleted, and the
  pre-interned slots after them (`FUNCREF`, `CONST_CHAR`) renumbered in
  the same edit: only the list and its constants must agree.
- A constant may hold an array: `const GREETING: [u8; 5] = "hello";` is data
  in no memory, and each use places a copy of it as a literal is placed
  (`heap::&[u8; 5]`, `stack::&[u8]`), so one constant serves every memory
  (`place_constant`, and `place_data` in evaluation, which reads the
  constant's body with the use's pointer type). The prior art is region
  polymorphism (Tofte–Talpin, Cyclone): the constant's type reads
  `∀M: Memory. M::&[u8; 5]`, and placing it instantiates `M`. Its own value is
  `NoValue`: its elements are evaluated at the definition, for what fails in
  them, and nothing is allocated until a use places it.
- Not done: an array of arrays placed in memory (`heap::&[[u8; 2]; 2]`)
  checks but does not evaluate, since `layout` gives an array no layout until
  `Sized`; and a literal kind inside a constant's array type
  (`const C: [const_int; 3]`) is still E2128.

## Runtime positions

Literal kinds and slices are two different properties: a literal kind has no
type yet (coercing gives it one), a slice or an array has no memory yet
(placing or a pointer gives it one). For a runtime position (a field, a
parameter, a local, a return type) they are one rule today:

> A runtime position needs a type with no literal kind in it and no slice or
> array held by value.

Checked where a written type is lowered and where a local takes its type. The
slice half is to become "a value position needs a `StackValue`", with fields
free (see "Values are `StackValue`s"); the literal half stays.
Inside a constant's declared type neither half applies: a constant may be
`const_int`, `[u8; 5]` or (later) `[const_int; 3]`.

## Values are `StackValue`s (implemented)

Decided on 2026-10-30, implemented on 2026-11-01. It replaced E2129's slice
check and E2130 (`SliceArgument`, removed), the `Slice`-bound rule below.

### What was weak in the `Slice`-bound rule

Only a parameter bounded by `Slice` stood for a slice or an array (E2130),
and a slice or an array held by value was E2129.

The `Slice` bound does two jobs: it says a type has elements, and it is the
only way a parameter may stand for something not held by value.

- No one generic type holds both a value and a slice: `Box<M, T>(p: M::*T)`
  refuses `Box<heap, [u8]>` (E2130), and `Box<M, T: Slice>` refuses
  `Box<heap, u32>`.
- `T: Slice` does not mean unsized: arrays are `Slice` and sized. It means
  "not held by value" only because everything that implements `Slice` happens
  to be held only by a pointer.
- A field may not hold an array (E2129), so a record laid out in memory with
  an inline buffer, `Header(len: u32, data: [u8; 16])`, cannot be written.
- (Fixed 2026-10-31 by the `Pointer` trait.) A pointer to an abstract
  pointee bounded by `Slice` was no `StackValue`; its metadata is now the
  rigid `<M::&S as Pointer>::Metadata`, so it can be passed and transmuted.
- `may_be_slice` and `pointer_metadata` match `Type::Slice`/`Type::Array` and
  the `Slice` bound by hand. A new kind of type held only by a pointer
  (`dyn Trait`, for dynamic dispatch) would need a case in each and another
  bound implying the same thing.

### Two properties, neither implying the other

wx has no stack in linear memory for aggregates, so everything held by value
ends up in Wasm locals: "held by value" and "flattens into Wasm values" are
one property, `StackValue`. Having bytes in linear memory is another,
`Sized` (see "Sized"). Each gap between them has one cause:

| A type that holds, by value, | `StackValue` | `Sized` |
|---|---|---|
| a reference (`funcref`, `func(A) -> R`, later `externref`) | yes | no |
| an array `[T; N]` | no | yes |
| `[T]` (later `dyn Tr`) | no | no |
| none of these | yes | yes |

- A reference never goes into linear memory: that is Wasm's rule. Storing a
  function means putting it in a table and storing the index, a different
  value (a handle) made by an explicit operation, so `funcref` is not `Sized`
  by quietly meaning its index.
- An array is never a value: that is wx's rule. Locals cannot be indexed at
  runtime, and arrays are not flattened into them.
- Where both hold, the two shapes still differ (a `u8` is an `i32` on the
  stack and one byte in memory; a struct's `Repr` is in declaration order, its
  layout alignment-sorted), so a load or a store converts between them.

Inhabitedness is a third question, a query asked where it matters
(exhaustiveness, dead code), with no flag: a `HAS_NEVER` flag would be the
wrong approximation (`func() -> !` has values, and with tagged unions so
would `Result<T, !>`), and flags cannot see a struct's fields anyway.

### The rule: a position states what it needs

Nothing carries an implicit bound: not a type parameter, not a struct. A
struct is well-formed whatever its fields are; whether it is a `StackValue`,
`Sized`, both or neither is answered from its structure when something asks.

| Position | Needs |
|---|---|
| a function's parameter or result, a `func(A) -> R`'s parts | `StackValue` (passed through the stack) |
| a local, an ascription | `StackValue` (held in Wasm locals) |
| a global | `Repr: StackScalar` (as now) |
| a load or a store through a pointer (`p.*`, `p.field = v`) | the pointee `Sized` (its layout), and the value read or written a `StackValue` |
| a struct's field, a tuple's element, a type argument | nothing |

```wx
struct Header(len: u32, data: [u8; 16]);  // Sized, no StackValue: in memory only
struct Callback(f: funcref);              // a StackValue, not Sized: on the stack only
struct Box<M: Memory, T>(p: M::*T);       // holds u32, [u8], later dyn alike
```

- A generic position states its bound: `func id<T: StackValue>(x: T) -> T`.
  Without it the position is an error that suggests adding the bound to the
  parameter. The solver already derives `Wrap<T>: StackValue` from
  `T: StackValue`, so the check is "every by-value position's type is a
  `StackValue` by the declared bounds". Implied bounds (the body assuming
  what its signature's positions need, callers proving it) were considered
  and left out: for `x: Wrap<T>` they need `T: StackValue` derived backwards
  from `Wrap<T>: StackValue`, which the solver does not do. Adding them later
  only relaxes the rule.
- E2129 is "this position needs a `StackValue`", answered by the solver;
  E2130 and `may_be_slice` are gone, `id::<[u8]>` being an unmet bound of
  `id`'s own. `Slice` means only "has elements".
- `dyn Tr` would be one more type that is neither, plus its pointer's shape.

### As implemented

- `TypeContext::stack_value_repr` asks for `<T as StackValue>::Repr` through
  ordinary normalization. Value checks and trait membership reuse its
  successful answers in the existing normalization cache; no separate cache
  or negative entries are needed. Projection rewriting handles equalities and
  receiver normalization, then `project_value` computes builtin associated
  values directly or falls back to `declared_projection_value` for impl selection.
  The StackValue computation owns both its bound check and representation.
  An abstract answer is accepted only with
  evidence of the bound, and remains keyed by the input's assumption env
  even when an equality makes its output concrete. A cold reduction collects
  the representation once, rather than first collecting it for membership.
  After a failed query, `explain_non_stack_value` locates an offending part
  separately from representation collection. E2129 names it: "`Header` cannot
  be held by value, since it holds `[u8; 16]`", with the suggestion
  `require T: StackValue` for an abstract part. The walk normalizes `Deep`, as
  a declaration's other checks do, so a
  loop through an equality (`First = (T::First, T::First)`) stays the rigid
  projection instead of unfolding a step at a time, and keeps the structs on
  its path, so a struct containing itself is poisoned (E2032 reports it)
  rather than overflowing.
- Signatures record `CheckValueType` for parameters, results, a function
  type's parts, and a local's or an ascription's written type. Two values
  are made with no written type, and are checked on the spot in the body
  (`require_stack_value`), the value typed `ERROR` when it fails, so nothing
  downstream reports again: a construction (its fields need nothing, the
  struct made of them does) and a load (`p.*`, `s[i]`, `p.field` read as a
  value).
- Thinness without `Sized`: an abstract pointee is thin when it is assumed a
  `StackValue` (nothing that is one holds a slice by value) or an `Array`;
  otherwise its metadata is the rigid `<M::&T as Pointer>::Metadata`. So an
  unbounded `T` gives a pointer of unknown shape, and generic code that
  treats `M::*T` as an address bounds `T: StackValue` until `Sized` comes
  (step 7), which will add "assumed `Sized`" to the same rule.
- std: a trait whose functions take `Self` by value has `StackValue` as a
  supertrait (the operator traits, `UnsignedInt`/`SignedInt`, `Global`,
  `Memory`, `Call`, whose `Args` and `Result` are bounded too); the address
  helpers (`slice_from_parts`, `array_from_ref`, `allocate_value`,
  `RawPtr::from_ref`, …) bound their element `T: StackValue`, `Array::as_slice`
  its `Value`. Those element bounds are `Sized`'s job and move to it.
- A typeset implies `StackValue` only when it says so
  (`typeset PointerSize: … + StackValue`): the solver does not derive a
  trait from every member of the set having it.

### `!` (implemented)

`!` and any type containing it are `StackValue`s held as `!`
(`stack_elements` collapses them to the one element `!`, `compute_stack_value_repr` gives
`Repr = !`). It must be one, since `func trap() -> !` and `local x: ! = trap();`
hold it by value; codegen holds no Wasm value for it (a function returning it
has the Wasm result `[]`, a local of it takes no Wasm local), since the code
that would is unreachable. Its `Repr` is `!` rather than `()`, so no other
type's equals it: `transmute` never makes one, and since `!` is no
`StackScalar`, no global is one. See `notes/stack-value.md`.

### A pointer's representation

A slice's length is `M::Size`, which belongs to the pointer, not to the
pointee: `[T]` knows no memory. So the length is not a type of `T`'s. A
pointer computes its representation from its memory and its pointee: an
address, then the pointee's metadata with each count held as `M::Size` (one
for `[T]`, none for a `Sized` pointee, see "Unsized fields"), a vtable index (probably `i32`, a table index, memory-free) for a later
`dyn`. Over a pointee of unknown shape the representation stays a rigid
projection, `<M::&T as StackValue>::Repr`, resolved after monomorphization,
as an abstract part's `Repr` is today, instead of "no `StackValue`"; so
`Box<M, T>` can be passed.

Rust's `Pointee` trait (`type Metadata`) names a pointer's extra part as a
type of the pointee's, which does not fit a length whose type is the
memory's. wx names it on the pointer instead (see "The `Pointer` trait"
below). Metadata is made of counts the pointer types with `M::Size`, as an
untyped constant is typed by its use, so the pointee never needs to know the
memory.

### Unsized fields

Decided on 2026-10-31. A struct may hold any number of unsized fields, in
any position, and a slice's element may itself be unsized. Nothing is
checked where the struct is declared: such a struct is neither a
`StackValue` nor `Sized`, so a construction (its result needs a
`StackValue`) or a load is refused at the use, and the diagnostic names the
field that makes it so.

```wx
struct Message(header: u32, payload: [u8], checksum: [u8]);
// metadata (count, count): payload's length, checksum's length

struct Image(pixels: [[u8]], palette: [u32]);
// metadata ((count, count), count)

struct Matrix(data: [[f32]]);
// metadata (count, count): 3 rows, 4 columns
```

**Metadata** is an ordinary type the compiler computes from the pointee and
the pointer's `Size`, so a count is typed by the pointer, never by the
pointee:

```rust
/// The lengths a pointer to `pointee` carries beside its address, each a
/// `size`: `Some(UNIT)` for a `Sized` pointee, `None` for one whose shape
/// is not known in this scope.
fn pointer_metadata(
    &mut self,
    assumption_context: AssumptionEnvIdx,
    pointee: TypeIndex,
    memory: TypeIndex,
) -> Result<Option<TypeIndex>, SolverError>
```

| Pointee | Metadata |
|---|---|
| a `Sized` type | `()` |
| `[T]` | `(size, metadata(T))` |
| a struct, a tuple | the tuple of its fields' metadata in declaration order, `()` skipped |
| an abstract type not assumed `Sized`, or a type holding one (`Wrap<T>`) | `None` |

Interning does the collapsing: an empty tuple is `UNIT` and a tuple of one
is its element, so `[u8]` gives `(Size, ())`, which is `Size`. Skipping `()`
fields inside a longer tuple is explicit. In `heap` (`Size = u32`):

| Pointee | Metadata |
|---|---|
| `u32`, `[u8; 4]` | `()` |
| `[u8]` | `u32` |
| `[[f32]]` | `(u32, u32)`: rows, columns |
| `Message(header: u32, payload: [u8], checksum: [u8])` | `(u32, u32)` |
| `Image(pixels: [[u8]], palette: [u32])` | `((u32, u32), u32)` |

and in an abstract memory each `u32` is `M::Size`. A slice of slices is
rectangular: every element shares the one inner metadata.

- A pointer's representation is its address, then
  `push_stack_elements(metadata)`, which already flattens nested tuples;
  `push_stack_elements`, `layout.rs`'s pointer piece and `eval.rs` read it
  (`pointer_metadata`; `is_fat_pointee` is gone).
- A layout's `Count(i)` (see "Layouts are expressions") is the i-th element
  of the flattened metadata, the order the representation uses.
- `None` is not `UNIT`: in `struct Box<M: Memory, T>(p: M::*T)`, `T` may be
  `u32`, `[u8]` or `[[u8]]`, so no type describes `M::*T`'s metadata, and
  answering `()` would commit to a thin pointer. `ERROR` would silence
  diagnostics wherever it spread, and a precondition on the caller would
  make each caller repeat the walk.
- `pointer_metadata`'s `None` is that projection, `<M::&T as
  Pointer>::Metadata`, rigid until `T` is known, as `T::Item` is (see "The
  `Pointer` trait"). `pointer_metadata_value` normalizes that projection,
  over the shared pointer, for the solver and the representation; a layout
  and an evaluation read `None` as unknown, never thin.

**Layouts are expressions** over that metadata (see "Sized"). A field's
offset is one too. Since wx orders fields itself, a struct places its sized
fields first, alignment-sorted as today, and its unsized fields after them
in declaration order: every sized field keeps a constant offset
(`p.header` through a `heap::&Message` is as cheap as through a sized
struct), and only an unsized field after the first one has a runtime offset.

### The `Pointer` trait

Decided and implemented on 2026-10-31. The metadata is named on the
pointer type, not on the pointee:

```wx
/// Every pointer type, `M::&T` and `M::*T`; the compiler answers it from the
/// pointer's structure.
pub trait Pointer: StackValue where {
    Repr = <(Self::Memory::Size, Self::Metadata) as StackValue>::Repr,
} {
    type Memory: Memory;
    type Pointee;
    type Metadata: StackValue;
}
```

- The solver answers it from the pointer's structure
  (`TraitImplLookup::Builtin`, as `StackValue`'s): `Memory` and `Pointee`
  read off the type, `Metadata` is `pointer_metadata(pointee, memory)`. Over
  a pointee of unknown shape `Metadata` stays the rigid projection
  `<M::&T as Pointer>::Metadata`; over a concrete pointee in an abstract
  memory it reduces (`<M::&[u8] as Pointer>::Metadata` is `M::Size`).
- Metadata requests use the ordinary projection-normalization pipeline:
  `pointer_metadata_value` forms `<M::&T as Pointer>::Metadata` and calls
  `normalize`; its builtin reduction calls `compute_pointer_metadata`.
  A slice's element metadata is another projection query, so the existing
  solver frames, recursion budget, equality rollback and cache cover the
  whole computation. The pointee is normalized deeply: a looping equality
  such as `T::Item = [T::Item]` stays rigid instead of unfolding afresh at
  each slice element. `Pointer::Metadata` must be present when this query runs.
- The metadata depends on the pointee and the memory, and a pointer type is
  exactly that pair, so this is a plain associated type: no generic trait,
  no generic associated type. It is the pattern the rigid
  `<M::&T as StackValue>::Repr` already follows.
- `M::&T` and `M::*T` have one metadata; the answer goes through the shared
  form, so the two are one cache entry (as `compute_stack_value_repr` canonicalizes).
- The supertrait equality states the representation: an address, then the
  metadata. So std writes `from_raw_parts<P: Pointer>(address:
  P::Memory::Size, metadata: P::Metadata) -> P`, `metadata(pointer: P) ->
  P::Metadata` and `address(pointer: P) -> P::Memory::Size` as plain
  `transmute`s, with no intrinsic. One function covers shared and exclusive
  pointers; `P` is learned from the expected result or the argument, never
  from a projection. Places through an abstract `P` would need rules of
  their own.
- Not done: refusing a written `impl Pointer` (or `StackValue`, `Slice`,
  `Array`, `Call`); impls are only for nominal types, so none can be written
  for a pointer today.
- Thinness is a derived fact: `T: Sized` gives `Metadata = ()` once
  `Sized` exists. No clause on a compound type is written.
- The cost: a rigid form names the memory, not only its `Size`. In a
  generic body with an abstract `T`, `<heap1::&T as Pointer>::Metadata` and
  `<heap2::&T as Pointer>::Metadata` are different types even when both
  memories' `Size` is `u32`, so a `transmute` between those two pointers is
  refused there (every instantiation would agree). Over a concrete pointee
  both reduce and the `transmute` is accepted. Accepted as rare.

Why not Rust's `Pointee`. Rust names metadata on the pointee because many
pointer types (`&`, `&mut`, `*const`, `*mut`, `NonNull`, `Box`, `Rc`, user
smart pointers) share it, its one address space makes every length a
`usize`, and unsizing (`CoerceUnsized`, `dyn`'s vtable) relates pointees.
In wx the metadata depends on the memory, which the pointee does not know,
so the pointee-side form needs a generic associated type
(`type Metadata<S: PointerSize>`), and wx has only two pointer forms, both
built in (a smart pointer holds one as a field and gets its representation
through it). A later `dyn` has memory-free metadata either way.

Generic associated types are deferred (`notes/generic-associated-types.md`):
they would serve one compiler-answered trait, at the cost of a change to
`Type::TypeProjection` that fails silently where a helper ignores its
arguments. If they come, `<M::&T as Pointer>::Metadata` can be redefined
inside the compiler as `<T as Pointee>::Metadata<M::Size>`, which also
makes the two rigid forms above one type; the `Pointer` API does not
change.

What the trait does not change yet:

- `len()` on a slice reads the first count, as it does now.
- `s[i]` on a `heap::&[[u8]]` is a place of `[u8]`, not loadable, and
  `s[i].&` is a `heap::&[u8]` carrying the inner count: one row. Its offset
  is `i` times the element's size, a runtime value.
- A pointer to an unsized struct is built only by `transmute` from its
  representation, which is fixed and does not change when the trait comes.
- A function over both `[u32]` and `[[u8]]` holds the pointer with its rigid
  metadata, but cannot index it until layouts are expressions.
- Turning a size or an offset that reads a count into instructions is
  MIR's. Until then a place step whose offset reads one is refused.

### Open

- `dyn`, and its metadata (a table index) through `Pointer`.
- Implied bounds instead of written ones (see above).

## Lengths are counts

A length (`Type::Value { bits }`) is a natural number. It has no type of its
own:

- `[T; N]` is well-formed for any `N`.
- `M::&[T; N]` is well-formed only when `N` fits `M::Size`: `CheckConstantRepresentable`
  is recorded by the pointer, not the array (`length_representable`), a concrete
  `Size`'s range (E2004), or every member of the typesets an abstract `Size`
  is bounded by (`PointerSize`, so `u32`; E2047). It may later tighten to
  `<[T; N] as Sized>::SIZE`, the real addressing limit. A pointer type made by
  substitution (`M::&S` with `S = [u8; N]`) is not checked again: see the
  open point under "Representability clauses".
- At runtime a count is only ever read through a pointer, where it has the
  type `M::Size`: `len<M>(self: M::&Self) -> M::Size` returns the fat
  pointer's length or `N`.
- A constant named as a length must have the pointer's `Size` as its type, or
  be an untyped `const_int` count that fits it (`CheckConstantType`, also
  recorded by the pointer). A bare array type's constant length is not
  checked for its type yet.

## The slice traits

The compiler implements them for every slice and array
(`implements_structurally`, matched on the pointee); no impl of them is
written anywhere, and source may `impl` only for nominal types (structs,
enums, the primitive items). A trait impl written for a slice, an array, a
function reference, a tuple or a pointer is an error (`InvalidImplTarget`: an
impl's target is a path). The methods are bodiless; MIR supplies them.

```wx
pub trait Slice {
    type Value;              // `: Sized` once `Sized` exists

    func len<M: Memory>(self: M::&Self) -> M::Size;
    func as_ref<M: Memory>(self: M::&Self) -> M::&Self::Value;

    #[inline]
    func first<M: Memory>(self: M::&Self) -> M::&Self::Value {
        if self.len() == 0 { trap() };
        self[0].&
    }

    #[inline]
    func last<M: Memory>(self: M::&Self) -> M::&Self::Value {
        if self.len() == 0 { trap() };
        self[self.len() - 1].&
    }
}

pub trait Array: Slice {
    const LEN: const_int;
    func as_slice<M: Memory>(self: M::&Self) -> M::&[Self::Value];
    func as_slice_mut<M: Memory>(self: M::*Self) -> M::*[Self::Value];
}
```

- The memory is each method's own parameter because a slice has none: the
  one `[u8]` is what `heap::&[u8]` and `stack::&[u8]` both point at, so a
  `Self::Mem` would have no single answer. A call learns `M` from its
  receiver. (`Allocator::Mem` is associated, correctly: an allocator belongs
  to one memory.)
- `SliceMut` and `ArrayMut` are gone: whether a slice may be written is the
  receiver's ownership, not `Self`'s. `as_slice_mut` stays a second method,
  since a method cannot be generic over ownership. `as_ptr<M>(self: M::*Self)
  -> M::*Self::Value` belongs in `Slice` when it is needed.
- `Array::LEN` is untyped (see below): its value does not depend on a memory,
  so `LEN<M: Memory>: M::Size` would only make every use name a memory that
  cannot be inferred (`Size` does not determine its memory).
- It was `SIZE`; renamed because `Sized::SIZE` is the size in bytes, and on
  `[u32; 4]` the two are 4 and 16. With `T: Array + Sized` one name would make
  `T::SIZE` ambiguous (E2059). `LEN` matches `len()`, and `SIZE` means bytes
  everywhere.
- `Value: Sized` (with `Sized`) because a slice is well-formed only over sized
  elements, so code bounded by `Slice` may index without a bound of its own.
- The receiver conversion: a method that takes `self: M::&Self` called on an
  exclusive `M::*[T]` takes `receiver.*.&` (only the receiver, only that
  direction). A shared receiver for a `self: M::*Self` method is a mismatch
  (E2001).

## Indexing is a place

`x[i]` is a built-in place, `PlaceKind::Element { object, index }` on a
`[T]` or `[T; N]` place, not a call: `s[i]` is `s.*[i]`, as `p.field` is
`p.*.field`, and the index is the pointer's memory's `Size`. The element is
the slice's or array's element type, or `<S as Slice>::Value` for an abstract
`S` assumed `Slice`. Read, it is a shared place; written (`s[i] = v`,
`s[i] += 1`), it needs an exclusive pointer. MIR lowers it to a bounds check
against the length and an offset from the data pointer. `index`, `index_mut`,
`first_mut` and `last_mut` are removed from std: `.&` is shared only, so
there is no exclusive pointer to an element until `.&mut` exists, and then
`first_mut` is `self[0].&mut`. Indexing anything else is E2125; a pointer to
a pointer to a slice is one step too far (`x.*[i]`).

## Untyped constants

A constant may have a literal kind as its type:

```wx
pub type const_int;      // core: binds the pre-interned CONST_INT slot
pub type const_float;    // CONST_FLOAT
pub type const_char;     // CONST_CHAR

const X: const_int = 4;
const PI: const_float = 3.14159265358979323846264338327950288;
const U: const_char = 'u';
// Planned, currently rejected:
// const P: (const_int, const_int) = (1, 2);
```

- Literal kinds are named by ordinary type paths (`const_int`, `const_float`, `const_char`,
  `core::const_int`). The checker recognizes the resolved type rather than a
  separate syntax form. Shadowing is ordinary: a user's own `const_int` is
  checked as that user's type.
- A literal kind is currently allowed only as the whole annotation of a free
  or trait constant. Runtime annotations (`func f(x: const_int)`, `local x:
  const_int`), type aliases and kinds nested in compound annotations remain
  E2128. Untyped impl constants and tuple/array annotations containing kinds
  remain unimplemented.
- The kind is written, never inferred from the initializer: inferring it
  would read another constant's body while building signatures
  (`const Y = X + 1`). `const X = 4;` stays E2002, suggesting `: const_int`.
- `const_int` checks nothing at the definition but the kind: the initializer
  is an integer literal, another `const_int` constant, or an operator over
  them (`const_char` is a char literal; `'a' + 1` is one too, so it is not an
  `const_int`). It is evaluated in an exact domain (`i128`) before it has a
  type, since one value serves every use; overflow there is the one error at
  the definition. `0 - 1` is `-1` and fails only where it meets an unsigned
  type.
- `const_float` preserves an exact decimal value without choosing `f32` or
  `f64`. `ExprKind::Float(DecimalFloat)` holds inline ranges into the single
  `Semantics::numbers` limb buffer: unsigned significand and exponent
  magnitudes in base 2^32, with separate signs. Temporary `num-bigint` values
  parse and normalize decimal input. `NumberStorage::to_f32`/`to_f64`
  format exact scientific notation and use Rust's parser at the requested
  width, preserving correct rounding and subnormals without custom conversion
  arithmetic. No expression owns a vector, no numeric text enters the name
  interner, and semantics retains no source files.
  Negation and references preserve the value and negative zero; binary
  untyped floating arithmetic is explicitly unsupported until an exact
  evaluator is implemented. Typed primitive operations continue to evaluate
  at their concrete widths; function and method calls remain unsupported.
  Overflow and underflow are checked at each typed use, including generic
  instances. Literal records and cached values never hold an f64 default.
- Each use checks the fit as a literal does: `coerce` gets an arm for a
  `Const` of literal type that reads its value and runs `coerce_int`'s check.
  In a function body the value is known; in a constant body (checked
  value-free) it is a `DeferredCheck`, as a literal's length already is. No
  defaulting: `local x = X;` is E2002, as `local x = 4;` is.
- A typed constant (`const X: u32 = 4`) keeps the exact-type rule; only an
  untyped one coerces. This is not the "any integer constant whose value
  fits" relaxation declined on 2026-10-25.
- A trait constant may be untyped. Done for the compiler's `Array::LEN`: over
  a concrete array its use reads the length (`untyped_value`, through
  `resolve_constant`); over an abstract one it needs a representability clause
  (E2133 without one). Not done: an impl's member of an
  untyped trait constant (conformance: it has the declaration's kind).

## Representability clauses (done)

Named after Go's spec ("a constant x is representable by a value of type
T"): an untyped constant is *representable as* a type when the type's range
holds its value, so a use can give it that type. This was called "fit" until
2026-11-01, literals' checks included (`CheckConstantRepresentable`,
`ExprObligation::Representable`).

An abstract constant (`<T as Array>::LEN` with `T` abstract) has no value in
a generic body. Checking it after monomorphization would be the first check
in the language deferred that far; instead the signature states it, next to
trait and equality clauses:

```wx
func f<T: Array>() -> u8 { T::LEN }                          // error
func f<T: Array where { const LEN: u8 }>() -> u8 { T::LEN }  // fine
```

- It is a bound, not a type: the clause states a fact about the value (its
  range), and each use still gives the constant its type, as a literal's
  context does. A failure is an unmet bound, not a type mismatch: E2133,
  "constant `<T as Array>::LEN` cannot be represented as `u8`", at the use in
  a body or at the argument of a call, with the clause to write as a note. A
  known value says it in the label ("its value `256` is out of range").
  Literals say the same ("literal `300` cannot be represented as `u8`",
  E2004).
- `Clause::Representable(RepresentableClause)`, beside `Trait` and
  `Equality`, published in the final stage (its type may name siblings,
  `const LEN: Mem::Size`), inherited from a supertrait's bound. A clause about
  a type the function does not declare (`Array::as_slice`'s `LEN` against
  `Mem::Size`) is written on `Self` as the function's first parameter.
  `Solver::satisfies_clauses` proves it at a use: a concrete argument by
  evaluating the constant, an abstract one from the caller's own clauses
  (`assumed_representable`).
- One implies another by range containment: `u8` gives `u16`, `i32`,
  `M::Size`, not `i8`; `M::Size` (every member of the typesets bounding it,
  `u32` and `u64`) gives `u32`, not `u16`. The solver's first judgement that
  is not an equality.
- Clauses are written, never implied by the types in a signature (the
  2026-10-17 rule: no implied bounds).
- A bound never states a constant's type. A constant's type is its
  declaration's (and the associated types it names); the one thing a bound
  says about a constant is representability, which means something only for
  an untyped one, the one kind whose type is open. A type fact about a
  constant is an equality on an associated type (`type F: Call; const FN:
  Self::F;` with `where { F = func() -> i32 }`). A generic constant (`const
  N<S: PointerSize>: S`) is typed per instance, and its value is checked
  against every member once, at the definition.
- A representability clause on a *typed* constant is E2134
  (`TypedConstantBound`), reported where the entry is lowered, pointing at
  the declared type; no clause is built.
- `const LEN = 4` (a value, rustc's `ConstEquate`) is parsed and reported
  unsupported (E2114).
- Open: a pointer to an abstract count, `M::&[u8; T::LEN]`, needs `T::LEN`
  representable as `M::Size` for well-formedness. Either the signature writes
  the clause, or the obligation is proved where the signature is
  instantiated, as `M::&S` with `S: Array` already has to work.

## Sized

A type's layout in linear memory, as a trait:

```wx
/// A type with a layout in linear memory: its bytes, and the alignment they
/// need. `SIZE` is a multiple of `ALIGN`, so it is also the stride between
/// the elements of an array.
pub trait Sized {
    const SIZE: const_int;
    const ALIGN: const_int;
}
```

- No impl of it is written anywhere, and writing one is an error. The solver
  answers it on demand from the type's structure, as it answers `StackValue`
  (`TraitImplLookup::Builtin`), and `resolve_constant` reads `SIZE` and
  `ALIGN` off the type, as it reads `Array::LEN`.
- The constants are untyped because a layout does not depend on the memory a
  value is stored in, only on the memories named inside the type. `SIZE`
  belongs to `T` alone; today's `size_of<T, Mem>() -> Mem::Size` takes `Mem`
  only to type its result, and each use of `T::SIZE` coerces instead.

| Type | `Sized` | `SIZE` / `ALIGN` |
|---|---|---|
| a primitive | yes | its width / its width |
| `!`, a function item, a memory's or a global's handle | yes | 0 / 1 |
| a struct, a tuple | iff every field is | `layout.rs`'s alignment-sorted placement |
| an enum | yes | its repr's |
| `M::&T`, `M::*T` | always | `M::Size`'s width |
| `M::&[T]`, `M::*[T]` | always | twice `M::Size`'s width |
| `[T; N]` | iff `T` is | `N * T::SIZE` / `T::ALIGN` |
| `[T]` | no | size `Count * T`'s size, at runtime / `T::ALIGN` |
| `funcref`, `func(A) -> R` | no | (a reference has no bytes in linear memory) |
| a type parameter, a projection | iff assumed | rigid |

- A pointer is always `Sized`: its address is `M::Size`, always a
  `PointerSize` member. Over an abstract memory its `SIZE` is rigid until the
  memory is known, as `Array::LEN` is over an abstract `Self`.
- The judgement is `layout.rs`'s walk, which answers a layout or `None` (the
  references, and parameters and projections not assumed `Sized`); see
  "Layouts are expressions" below.
- This is not the rule for by-value positions (see "Slices and arrays"):
  `[u8; 16]` is `Sized` and cannot be a local, a struct holding a `funcref` is
  not `Sized` and can. `Sized` says whether a type has bytes, and every
  question about memory layout goes through it.

Where it is required:

- A place step through a pointer into a pointee that is not a slice or an
  array (`p.*`, `p.field`) needs the pointee `Sized`: field offsets come from
  the whole pointee's layout, and a load or a store needs its bytes. So
  `func get<M: Memory, T>(p: M::&T) -> T { p.* }` needs `T: Sized`, which says
  that a `funcref` cannot be loaded from memory.
- An element of an array is `Sized` by its well-formedness; an element of a
  slice only needs a layout, so `[[u8]]` is well-formed. `Slice::Value`
  carries no bound (`[[u8]]`'s is `[u8]`); generic code that loads elements
  states `Value: Sized`.

### Layouts are expressions

`Sized` means a size known at compile time, unsized a size computed at
runtime. `layout.rs`'s walk returns, instead of a number, an expression
over the pointer's metadata, and an alignment, always a number (the largest
of the parts'; metadata never changes it):

```
Size = Const(n) | Count(i) | Add(Size, Size) | Mul(Size, Size) | AlignUp(Size, align)
```

`Count(i)` is the i-th element of the flattened metadata type.

| Type | Size | Align |
|---|---|---|
| `u32` | `4` | 4 |
| `[u32; 3]` | `12` | 4 |
| `[u32]` | `Count(0) * 4` | 4 |
| `[[u8]]` | `Count(0) * Count(1)` | 1 |
| `Image(pixels: [[u8]], palette: [u32])` | `AlignUp(Count(0) * Count(1), 4) + Count(2) * 4` | 4 |

A type is `Sized` when its expression reads no `Count`, and `SIZE` is that
expression folded. A leaf may also be a constant that is rigid in TIR (`N`
in `[T; N]` over an abstract type): it is still known at compile time,
resolved by monomorphization, so the type is `Sized`. The two kinds of leaf
are the line: constants are compile time, counts are runtime. Field offsets
are the same expressions (see "Unsized fields"), and MIR lowers the ones
that read a count to arithmetic on the metadata the pointer carries. A type
with no layout (a reference, an abstract type of unknown shape) is no
expression at all.
- Not on a pointer type: `M::&T` for a `T` not `Sized` is well-formed, as in
  Rust, or every trait with a `self: M::&Self` method (`Allocator`) would need
  `Sized` as a supertrait. If a useless `heap::&funcref` should be refused,
  well-formedness can refuse a concrete pointee known not to be `Sized`,
  leaving abstract ones alone.
- Not on fields, locals or parameters: a struct is `Sized` iff its fields
  are, so nothing is checked per position.

std's `size_of` and `align_of`, which give every type a size, go:

```wx
impl<Mem: Memory> Layout<Mem> {
    #[inline]
    pub func of<T: Sized where { const SIZE: Mem::Size, const ALIGN: Mem::Size }>() -> Self {
        Self({ size: T::SIZE, align: T::ALIGN })
    }

    #[inline]
    pub func array<T: Sized where { const SIZE: Mem::Size, const ALIGN: Mem::Size }>(
        count: Mem::Size,
    ) -> Self {
        Self({ size: T::SIZE * count, align: T::ALIGN })
    }
}
```

and `RawPtr<Mem, T>`'s arithmetic bounds `T: Sized where { const SIZE:
Mem::Size }`. At a call:

- `Layout::<heap>::of::<[u8; 16]>()` is fine: `SIZE` is 16, which fits `u32`.
- `Layout::<heap>::of::<[u8]>()` and `Layout::<heap>::of::<func(u32) ->
  u32>()` are an unmet bound (E2063).
- `Layout::<heap32>::of::<[u8; 1 << 33]>()` names a well-formed, `Sized` type
  whose `SIZE` does not fit `u32`: the representability clause fails at the call, where
  allocating it in a 32-bit memory is what is wrong.

## Generic constants (later, separate)

`const PAGE_SIZE<S: PointerSize>: S = 65536;` is the bounded form: `S` is a
bound, proved once for each member at the definition, and every instance is
typed. Use it when one definition must be safe at every type of a set without
per-use checks (`PAGE_SIZE` in abstract-memory code). `const_int` is not a
bound and checks nothing ahead of time; the two coexist. A literal kind is not a typeset or a bound.

## Order of work

Each step ends with tests green.

1. Done (2026-10-30). Reject impls written for structural types. Already the
   case: an impl's target is a path, resolved by
   `ImplDispatchBuilder::resolve_target` to a struct, an enum or a primitive
   item, and anything else (an alias of a slice included) is
   `InvalidImplTarget`. Pinned by a test.
2. Done (2026-10-30). Untyped constants, free constants: parse `{T}`, std's
   `pub type const_int;` and `pub type const_char;` bound to their slots, the
   bare-path error, the literal-kind half of the runtime-position rule,
   constant bodies checked against their kind, exact arithmetic in `eval.rs`,
   the `coerce` arm, untyped constants as lengths.
3. Done (2026-10-30). The split: `Pointer { to: Slice | Array }` across
   `tir/` and the AST, the fit check on the pointer, `layout`/
   `stack_elements`/evaluation reading the pointee, `implements_structurally`
   on the pointee, `SliceByValue` (E2129) and `SliceArgument` (E2130), the
   receiver conversion, std's traits as above (`Array::LEN`), literals as
   arrays, placement through `coerce_static`, constants holding arrays placed
   at each use, `M::&[u8; _]` learned from the literal, the literal
   pseudo-types deleted.
4. Done (2026-10-30), with step 3, which needed it: indexing as a built-in
   place, with std's `index`/`index_mut`/`first_mut`/`last_mut` removed.
5. Done (2026-11-01). Values are `StackValue`s: value positions
   (parameters, results, function types' parts, locals, ascriptions, and a
   construction's or a load's value) proved `StackValue` by declared bounds,
   with a suggestion to add the bound; fields, tuple elements and type
   arguments free (see "Unsized fields"); a pointer's representation from
   its pointee's metadata (done 2026-10-31: `pointer_metadata` replacing
   `is_fat_pointee`, std's `Pointer` trait answered structurally, its rigid
   `Metadata` making a pointer to an unknown shape a `StackValue`,
   `from_raw_parts`/`metadata`/`address` in std); E2130 and `may_be_slice`
   removed, E2129 reworded; an abstract pointee thin only when assumed a
   `StackValue` or an `Array`; std's traits and generic functions given
   `StackValue` bounds. Done ahead of it: `!` held as `!`.
6. Representability clauses (done): the `where { const NAME: ty }` syntax, `RepresentableClause`, the
   solver's case and implication between fits, coercion of abstract
   constants, untyped trait constants in impls. Done ahead of it: an untyped
   trait constant (`Array::LEN`) and its use over a concrete type.
7. `Sized`: the intrinsic trait, answered structurally by the solver on
   `layout.rs`'s walk; `SIZE`/`ALIGN` in `resolve_constant`; the requirement
   on place steps through a pointer; layouts as expressions over the
   metadata, with sized fields placed before unsized ones; the
   well-formedness of slices (an element with a layout) and arrays (a
   `Sized` element); arrays laid out in memory (so arrays
   of arrays and fields holding arrays evaluate); a load or a store needing
   the pointee `Sized` and the value a `StackValue`;
   `size_of`/`align_of` removed, `Layout` and `RawPtr` rewritten on it. Needs
   step 6 (untyped trait constants, fit clauses).
8. Generic constants.

MIR lowering can start now; it needs the final shape of pointers, which
step 3 gave. Steps 5 to 7 can go alongside it.
