# Slices, untyped constants and fit clauses

Status as of 2026-10-30, branch `tir-refactor`: steps 1–4 done, step 6 (fit
clauses) in part (see "Order of work"), the rest designed, not implemented.
Settled in discussion on 2026-10-30; "Values are `StackValue`s" replaces the
`Slice`-bound rule (planned, outline decided, its "Open" points not). Linked
changes:

1. `[T]` and `[T; N]` become types of their own, a slice and an array: what a
   pointer points at, with no memory.
2. A length is a count: it has no machine type until it meets a memory.
3. A constant may be untyped, `const X: {integer} = 4;`, used like a literal.
4. An abstract constant's fit is stated in a bound,
   `T: Array where { const LEN: u8 }`.
5. Array and string literals are arrays (`[{integer}; 3]`, `[u8; 5]`),
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
  this off the pointee (`is_fat_pointee`); an abstract pointee assumed `Slice`
  but not `Array` may be either, and has no known representation.
- A slice or an array is only ever behind a pointer, `[T; N]` included, and
  this is permanent: Wasm locals cannot be indexed at runtime (`local.get`
  takes an immediate), so an array in locals would be a tuple with constant
  indices or an O(N) dispatch per access. Native compilers keep "stack" arrays
  in a shadow stack in linear memory; wx has no ambient memory, so that is an
  `M::*[T; N]` from an allocator.
- A type held by value (a parameter, a result, a field, a local or an
  ascription, a tuple's element, a function type's parameter or result) is
  neither, nor a parameter that may stand for one: E2129 (`SliceByValue`),
  recorded as `TypeObligation::CheckValueType` where the type is lowered. A
  constant's declared type, a type alias, a qualified path's root
  (`<[u8; 4] as Array>::LEN`) and a type argument are not by-value positions.
- Only a parameter bounded by `Slice` stands for a slice or an array: an
  argument that is one, for any other parameter, is E2130 (`SliceArgument`),
  checked with the parameter's other bounds (`check_bound_requirements`). So
  `Box<[u8]>`, `id::<[u8]>` and `size_of::<[u8], heap>()` are refused where
  they are written, never after monomorphization. Since every slice and array
  is a `Slice` and nothing else is, `S: Slice` narrows `S` as any bound
  narrows: an unbounded `T` ranges over everything else, with no implicit
  bound and no relaxing `?Sized`. The cost: no one parameter ranges over both
  (`Box<M, T>` and a `SliceBox<M, S: Slice>` are two types). Rust needs
  `?Sized` mostly for `dyn Trait` and `str`, which wx does not have. When
  `Sized` exists, a parameter bounded by it may stand for an array too
  (`Layout::of::<[u8; 16]>()`). This rule is what is implemented; it is to
  be replaced, see "Values are `StackValue`s".
- `[T]` and `[T; N]` will be well-formed only when `T: Sized` (see "Sized").
- One place rule covers fields and elements: each place step goes through at
  most one pointer, so `p.field` is `p.*.field` and `s[i]` is `s.*[i]`.

## Literals are arrays

An array or string literal is data not yet in a memory, so it has an array
type, and the literal pseudo-types `{array}` and `{string}` are gone:

```
[1, 2, 3]          : [{integer}; 3]
[0; 16]            : [{integer}; 16]
[0; N]             : [{integer}; N]
[x; _]             : [T; _]          (the length is its context's)
"hello"            : [u8; 5]
```

- An array literal's element type is its first typed element's, or its first
  element's; placing checks every element against the target's.
- An expression whose type is a slice or an array (or a tuple holding one)
  waits for its context as an untyped literal does
  (`TypeInterner::needs_context`): with an expected type it is coerced, and
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
  pre-interned slots after them (`FUNCREF`, `CHAR_LITERAL`) renumbered in
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
  (`const C: [{integer}; 3]`) is still E2128.

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
`{integer}`, `[u8; 5]` or (later) `[{integer}; 3]`.

## Values are `StackValue`s (planned, replaces the `Slice`-bound rule)

Decided on 2026-10-30 in outline; not implemented, except `!` (below). It
replaces E2129's slice check and E2130, which are what the code does today.

### What is weak in the current rule

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
- A pointer to an abstract pointee bounded by `Slice` is thin for an array and
  fat for a slice, so `is_fat_pointee` answers `None` and the pointer is no
  `StackValue` (`push_stack_elements`'s `None => false`): it can be neither a
  global nor transmuted, though its representation is definite once the
  pointee is known.
- `may_be_slice` and `is_fat_pointee` match `Type::Slice`/`Type::Array` and
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
- E2129 becomes "this position needs a `StackValue`", answered by the
  solver; E2130 and `may_be_slice` go, `id::<[u8]>` being an unmet bound of
  `id`'s own. `Slice` means only "has elements".
- `dyn Tr` would be one more type that is neither, plus its pointer's shape.

### `!` (implemented)

`!` and any type containing it are `StackValue`s held as `!`
(`stack_elements` collapses them to the one element `!`, `stack_repr` gives
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
address, then a length of `M::Size` for `[T]`, nothing for a sized pointee,
a vtable index (probably `i32`, a table index, memory-free) for a later
`dyn`. Over a pointee of unknown shape the representation stays a rigid
projection, `<M::&T as StackValue>::Repr`, resolved after monomorphization,
as an abstract part's `Repr` is today, instead of "no `StackValue`"; so
`Box<M, T>` can be passed.

Rust's `Pointee` trait (`type Metadata`) names a pointer's extra part as a
type of the pointee's, which does not fit a length whose type is the
memory's. It is needed only if code must build or take apart fat pointers
generically (`from_raw_parts`); std intrinsics
(`from_raw_parts<M, T>(p, len: M::Size) -> M::&[T]`) cover that until then.
If it comes, the length could be a count the pointer types with `M::Size`,
as an untyped constant is typed by its use, or the trait could take the
memory as a parameter.

### Open

- **Unsized fields.** `struct S(n: u32, tail: [u8])` is neither `Sized` nor
  a `StackValue`, so the question is what a pointer to it is. Rust allows an
  unsized type only as the last field (and a tuple's last element), and a
  pointer's metadata is that tail's, recursively (`<S as Pointee>::Metadata`
  is `<[u8] as Pointee>::Metadata`, the tail's element count, not a size in
  bytes); a second unsized field is an error. Building one goes through an
  unsizing coercion from a sized version or `from_raw_parts`. In wx the tail
  would also have to be exempt from alignment-sorting. Undecided: Rust's
  rule, or refusing a concrete field type that is neither (a generic field
  stays unchecked), which can be relaxed later.
- Pointer metadata as a type (`Pointee`), and `dyn`.
- Implied bounds instead of written ones (see above).

## Lengths are counts

A length (`Type::Value { bits }`) is a natural number. It has no type of its
own:

- `[T; N]` is well-formed for any `N`.
- `M::&[T; N]` is well-formed only when `N` fits `M::Size`: `CheckConstantFits`
  is recorded by the pointer, not the array (`length_fits`), a concrete
  `Size`'s range (E2004), or every member of the typesets an abstract `Size`
  is bounded by (`PointerSize`, so `u32`; E2047). It may later tighten to
  `<[T; N] as Sized>::SIZE`, the real addressing limit. A pointer type made by
  substitution (`M::&S` with `S = [u8; N]`) is not checked again: see the
  open point under "Fit clauses".
- At runtime a count is only ever read through a pointer, where it has the
  type `M::Size`: `len<M>(self: M::&Self) -> M::Size` returns the fat
  pointer's length or `N`.
- A constant named as a length must have the pointer's `Size` as its type, or
  be an untyped `{integer}` count that fits it (`CheckConstantType`, also
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
    const LEN: {integer};
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
pub type integer;        // std: binds the pre-interned INTEGER_LITERAL slot
pub type char;           // CHAR_LITERAL; later float (strings are arrays)

const X: {integer} = 4;
const U: {char} = 'u';
const P: ({integer}, {integer}) = (1, 2);
```

- `{T}` is a new `TypeExpression::Literal`: the parser takes any type inside
  and knows no kind names. Lowering resolves `T` like any type path and checks
  that it is a literal kind (a pre-interned literal slot); otherwise "`Point`
  is not a literal kind". The braces construct nothing: `{integer}` is the
  type `integer` is bound to, and they say that it is meant.
- A path that resolves to a literal kind outside braces is an error:
  "`integer` is a literal kind; write `{integer}`" (for `char`: "did you mean
  `Char`?"). Shadowing is ordinary: a user's own `integer` makes `{integer}`
  "not a literal kind" in its scope.
- A literal kind, or a tuple or array containing one, may only be a
  constant's declared type (free, trait and impl constants):
  `func f(x: {integer})` and `local x: {integer}` are errors under the
  runtime-position rule, since an untyped value cannot exist at runtime.
- The kind is written, never inferred from the initializer: inferring it
  would read another constant's body while building signatures
  (`const Y = X + 1`). `const X = 4;` stays E2002, suggesting `: {integer}`.
- `{integer}` checks nothing at the definition but the kind: the initializer
  is an integer literal, another `{integer}` constant, or an operator over
  them (`{char}` is a char literal; `'a' + 1` is one too, so it is not an
  `{integer}`). It is evaluated in an exact domain (`i128`) before it has a
  type, since one value serves every use; overflow there is the one error at
  the definition. `0 - 1` is `-1` and fails only where it meets an unsigned
  type.
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
  `resolve_constant`); over an abstract one it needs a fit clause, reported as
  not supported yet (E2114) until step 6. Not done: an impl's member of an
  untyped trait constant (conformance: it has the declaration's kind).

## Fit clauses

An abstract constant (`<T as Array>::LEN` with `T` abstract) has no value in
a generic body, so its fit cannot be checked there. Checking it after
monomorphization would be the first check in the language deferred that far;
instead the fit is stated in the signature, next to trait and equality
clauses:

```wx
func f<T: Array>() -> u8 { T::LEN }                          // error
func f<T: Array where { const LEN: u8 }>() -> u8 { T::LEN }  // fine
```

- The first is reported in the body, at the coercion, as an unmet bound is
  ("`T::LEN` may not fit in `u8`", with the clause as the suggestion), like
  `x + x` on an unbounded `T` is E2063. The body checks against the
  signature, never against instantiations.
- The return type is `u8`. A constant is not a type: no singleton types.
- A third clause kind, `FitClause { constant, ty }`, in `BoundClauses` beside
  `TraitClause` and `EqualityClause`, published and read the same way.
  `Solver::satisfies_clauses` proves it at a use: a concrete argument by
  evaluating the constant and running the fit check; an abstract one from the
  caller's own fit clauses.
- One fit implies another: fitting `u8` gives `u16`, `u32`, `u64`, `i16`,
  `i32`, `i64`, but not `i8`. This is the solver's first judgement that is not
  an equality.
- `where { const LEN: M::Size }` means fitting every member of the typesets
  bounding `Size`, as `CheckConstantFits` reads an abstract memory.
- Clauses are written, never implied by the types in a signature (the
  2026-10-17 rule: no implied bounds).
- An abstract constant coerces to a type its fit clause covers and nowhere
  else, and it stays untyped under the clause: the clause does not decide the
  type of every use.
- The same grammar leaves room for constant equalities
  (`where { LEN = 4 }`, rustc's `ConstEquate`); not needed yet.
- Open: a pointer to an abstract count, `M::&[u8; T::LEN]`, needs
  `T::LEN` to fit `M::Size` for well-formedness. Either the signature writes
  the fit clause, or the obligation is proved where the signature is
  instantiated (the substituted pointer type must be well-formed at the
  call). The second is how `M::&S` with `S: Array` already has to work: a
  caller cannot name `heap::&[u8; 2^40]` because that type is ill-formed.

## Sized

A type's layout in linear memory, as a trait:

```wx
/// A type with a layout in linear memory: its bytes, and the alignment they
/// need. `SIZE` is a multiple of `ALIGN`, so it is also the stride between
/// the elements of an array.
pub trait Sized {
    const SIZE: {integer};
    const ALIGN: {integer};
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
| `[T]` | no | |
| `funcref`, `func(A) -> R` | no | (a reference has no bytes in linear memory) |
| a type parameter, a projection | iff assumed | rigid |

- A pointer is always `Sized`: its address is `M::Size`, always a
  `PointerSize` member. Over an abstract memory its `SIZE` is rigid until the
  memory is known, as `Array::LEN` is over an abstract `Self`.
- The judgement is the walk `layout.rs`'s `piece` already does: it answers
  `None` for exactly the references, parameters and projections, and the
  solver's walk takes an abstract part as `Sized` when it is assumed so.
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
- An element of a slice or array is `Sized` by its well-formedness, and
  `Slice::Value: Sized` gives it to code bounded by `Slice`.
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
  whose `SIZE` does not fit `u32`: the fit clause fails at the call, where
  allocating it in a 32-bit memory is what is wrong.

## Generic constants (later, separate)

`const PAGE_SIZE<S: PointerSize>: S = 65536;` is the bounded form: `S` is a
bound, proved once for each member at the definition, and every instance is
typed. Use it when one definition must be safe at every type of a set without
per-use checks (`PAGE_SIZE` in abstract-memory code). `{integer}` is not a
bound and checks nothing ahead of time; the two coexist. Typesets never go
inside the braces.

## Order of work

Each step ends with tests green.

1. Done (2026-10-30). Reject impls written for structural types. Already the
   case: an impl's target is a path, resolved by
   `ImplDispatchBuilder::resolve_target` to a struct, an enum or a primitive
   item, and anything else (an alias of a slice included) is
   `InvalidImplTarget`. Pinned by a test.
2. Done (2026-10-30). Untyped constants, free constants: parse `{T}`, std's
   `pub type integer;` and `pub type char;` bound to their slots, the
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
5. Values are `StackValue`s: value positions (parameters, results, function
   types' parts, locals, ascriptions) proved `StackValue` by declared bounds,
   with a suggestion to add the bound; fields, tuple elements and type
   arguments free; E2130 and `may_be_slice` removed, E2129 reworded; a
   pointer to a pointee of unknown shape held as a rigid `Repr`; std's
   generic functions given `T: StackValue`. Needs nothing new. Done ahead of
   it: `!` held as `!`.
6. Fit clauses: the `where { const NAME: ty }` syntax, `FitClause`, the
   solver's case and implication between fits, coercion of abstract
   constants, untyped trait constants in impls. Done ahead of it: an untyped
   trait constant (`Array::LEN`) and its use over a concrete type.
7. `Sized`: the intrinsic trait, answered structurally by the solver on
   `layout.rs`'s walk; `SIZE`/`ALIGN` in `resolve_constant`; the requirement
   on place steps through a pointer; `Slice::Value: Sized` and the
   well-formedness of slices and arrays; arrays laid out in memory (so arrays
   of arrays and fields holding arrays evaluate); a load or a store needing
   the pointee `Sized` and the value a `StackValue`;
   `size_of`/`align_of` removed, `Layout` and `RawPtr` rewritten on it. Needs
   step 6 (untyped trait constants, fit clauses).
8. Generic constants.

MIR lowering can start now; it needs the final shape of pointers, which
step 3 gave. Steps 5 to 7 can go alongside it.
