# Regions, untyped constants and fit clauses

Status as of 2026-10-30, branch `tir-refactor`: designed, not implemented.
Settled in discussion on 2026-10-30. Linked changes:

1. `[T]` and `[T; N]` become types of their own (regions): what a pointer
   points at, with no memory.
2. A length is a count: it has no machine type until it meets a memory.
3. A constant may be untyped, `const X: {integer} = 4;`, used like a literal.
4. An abstract constant's fit is stated in a bound,
   `T: Array where { const SIZE: u8 }`.
5. Array and string literals are regions (`[{integer}; 3]`, `[u8; 5]`),
   placed in a memory when coerced to a pointer; `{array}` and `{string}` go.

Generic constants (`const N<S: PointerSize>: S = 0`) stay planned as the
separate, bounded form; see the end.

## Regions

Today `Type::Slice { of, memory, ownership }` and
`Type::Array { of, length, memory, ownership }` are the pointer itself: a
slice value is the fat pointer, and `Slice`'s `Self` is `heap::&[u8]`.

After the split:

- `[T]` is a run of values of `T` whose count is known only at runtime. It is
  unsized.
- `[T; N]` is exactly `N` values of `T`. It is sized (`N * size(T)` bytes),
  and its size does not depend on any memory.
- Neither is in a memory. Like `u32`, a region is a shape; a memory comes in
  only with a pointer. `M::&[T]` is `Pointer { to: Slice { of: T }, memory: M,
  ownership: Shared }`, and `M::&[T; N]` is `Pointer { to: Array { of: T,
  length: N }, .. }`.
- A pointer is fat exactly when it points at `[T]`: the data pointer and a
  length of type `M::Size`. A pointer to `[T; N]` is thin; its length is in
  the type. `layout` and `Solver::stack_elements` read this off the pointee.
- The surface syntax does not change: users write `M::&[T]` and
  `M::&[T; N]`, and a bare `[T]` or `[T; N]` in a written type stays an error.
  A region still reaches code through inference: `func sum<M: Memory, S:
  Slice>(s: M::&S)` called with a `heap::&[u8]` gives `S = [u8]`.
- A region is only ever behind a pointer, `[T; N]` included, and this is
  permanent: Wasm locals cannot be indexed at runtime (`local.get` takes an
  immediate), so an array in locals would be a tuple with constant indices or
  an O(N) dispatch per access. Native compilers keep "stack" arrays in a
  shadow stack in linear memory; wx has no ambient memory, so that is an
  `M::*[T; N]` from an allocator.
- Proposed rule (not confirmed): only a parameter bounded by `Slice` may hold a
  region, and such a parameter may appear only behind a pointer; checked where
  a signature is lowered, beside `PointerWithoutMemory` (E2038), so a by-value
  `S` is rejected on the definition and never after monomorphization.
- One place rule covers fields and elements: each place step goes through at
  most one pointer, so `p.field` is `p.*.field` and `s[i]` is `s.*[i]`.

## Literals are regions

An array or string literal is a region not yet in a memory, so it has a region
type, and `ARRAY_LITERAL` (`{array}`) and `STRING_LITERAL` (`{string}`) go
away:

```
[1, 2, 3]          : [{integer}; 3]
[[1, 2], [3, 4]]   : [[{integer}; 2]; 2]
[0; 16]            : [{integer}; 16]
"hello"            : [u8; 5]
```

- Coercing a region literal to a pointer places it: it becomes static data in
  the pointer's memory, its elements take their type, and the pointer is thin
  (`M::&[u8; 5]`) or fat (`M::&[u8]`, the length from the literal's type).
  This is `coerce_static`, driven by the literal's type. Only shared targets,
  as today (the data is read-only).
- `M::&[u8; _]` learns its length from the literal's type by unification,
  which `{array}` could not give.
- Only a literal is placed. A value that already has a type does not convert:
  `M::&[T; N]` to `M::&[T]` is `as_slice()`, as a function item does not
  become `func(A) -> R` by itself. An implicit unsizing coercion (only
  `M::&[T; N]` → `M::&[T]` and `M::*[T; N]` → `M::*[T]`, same memory, only
  where the expected type is known, never inside generic inference) is a
  possible later convenience.
- The pre-interned slots 18 and 19 stay as unused placeholders, so nothing
  after them moves.

## Runtime positions

Literal kinds and regions are two different properties: a literal kind has no
type yet (coercing gives it one), a region has no memory yet (placing or a
pointer gives it one). For a runtime position (a field, a parameter, a local,
a return type) they are one rule:

> A runtime position needs a type with no literal kind in it and no region
> held by value.

Checked where a written type is lowered and where a local takes its type.
Inside a constant's declared type the literal-kind half does not apply.

## Lengths are counts

A length (`Type::Value { bits }`) is a natural number. It already has no type
of its own; it stops claiming one:

- `[T; N]` is well-formed for any `N`.
- `M::&[T; N]` is well-formed only when `N` fits `M::Size`. This is today's
  `CheckConstantFits`, moved from the array to the pointer: a concrete
  `Size`'s range (E2004), or every member of the typesets an abstract `Size`
  is bounded by (`PointerSize`, so `u32`; E2047). It may later tighten to
  `N * size(T)`, the real addressing limit.
- At runtime a count is only ever read through a pointer, where it has the
  type `M::Size`: `len<M>(self: M::&Self) -> M::Size` returns the fat
  pointer's length or `N`.
- In a type a length is a count again, so `CheckConstantType` (a length's
  constant must have exactly the length's type) changes: an untyped
  `{integer}` constant is a count; a typed constant must still be an integer
  constant, and its value must be a count that fits where the pointer puts it.

## The slice traits

The compiler implements them for every region (`implements_structurally`,
matched on the pointee); no impl of them is written anywhere, and source may
`impl` only for nominal types (structs, enums, the primitive items). A trait
impl written for a slice, an array, a function reference, a tuple or a pointer
is an error (`InvalidImplTarget`, already: an impl's target is a path). The
methods are bodiless; MIR supplies them.

```wx
pub trait Slice {
    type Value;

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
    const SIZE: {integer};
    func as_slice<M: Memory>(self: M::&Self) -> M::&[Self::Value];
    func as_slice_mut<M: Memory>(self: M::*Self) -> M::*[Self::Value];
}
```

- The memory is each method's own parameter because a region has none: the
  one `[u8]` is what `heap::&[u8]` and `stack::&[u8]` both point at, so a
  `Self::Mem` would have no single answer. A call learns `M` from its
  receiver. (`Allocator::Mem` is associated, correctly: an allocator belongs
  to one memory.)
- `SliceMut` and `ArrayMut` are gone: whether a region may be written is the
  receiver's ownership, not `Self`'s. `as_slice_mut` stays a second method,
  since a method cannot be generic over ownership. `as_ptr<M>(self: M::*Self)
  -> M::*Self::Value` belongs in `Slice` when it is needed.
- `Array::SIZE` is untyped (see below): its value does not depend on a memory,
  so `SIZE<M: Memory>: M::Size` would only make every use name a memory that
  cannot be inferred (`Size` does not determine its memory).
- Open: calling `len` (which takes `M::&Self`) on an exclusive `M::*[T]`
  needs `*` → `&` at a method call's receiver (only the receiver, only that
  direction). Without it the call is `s.*.&.len()`.

## Indexing is a place

`x[i]` is a built-in place, `PlaceKind::Element { object, index }` on a
`[T]` or `[T; N]` place, not a call: `s[i]` is `s.*[i]`, as `p.field` is
`p.*.field`. Read, it is a shared place; written (`s[i] = v`, `s[i] += 1`),
it needs an exclusive pointer. MIR lowers it to a bounds check against the
length and an offset from the data pointer. `index`, `index_mut`,
`first_mut` and `last_mut` are removed from std: `.&` is shared only, so
there is no exclusive pointer to an element until `.&mut` exists, and then
`first_mut` is `self[0].&mut`. Indexing anything else is E2125.

## Untyped constants

A constant may have a literal kind as its type:

```wx
pub type integer;        // std: binds the pre-interned INTEGER_LITERAL slot
pub type char;           // later, CHAR_LITERAL; then float (strings are regions)

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
- A literal kind, or a tuple or region containing one, may only be a
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
- A trait constant may be untyped (`ast::TraitItem::Const`'s `ty` is
  required today); conformance: an impl's member has the declaration's kind.

## Fit clauses

An abstract constant (`<T as Array>::SIZE` with `T` abstract) has no value in
a generic body, so its fit cannot be checked there. Checking it after
monomorphization would be the first check in the language deferred that far;
instead the fit is stated in the signature, next to trait and equality
clauses:

```wx
func f<T: Array>() -> u8 { T::SIZE }                          // error
func f<T: Array where { const SIZE: u8 }>() -> u8 { T::SIZE }  // fine
```

- The first is reported in the body, at the coercion, as an unmet bound is
  ("`T::SIZE` may not fit in `u8`", with the clause as the suggestion), like
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
- `where { const SIZE: M::Size }` means fitting every member of the typesets
  bounding `Size`, as `CheckConstantFits` reads an abstract memory.
- Clauses are written, never implied by the types in a signature (the
  2026-10-17 rule: no implied bounds).
- An abstract constant coerces to a type its fit clause covers and nowhere
  else, and it stays untyped under the clause: the clause does not decide the
  type of every use.
- The same grammar leaves room for constant equalities
  (`where { SIZE = 4 }`, rustc's `ConstEquate`); not needed yet.
- Open: a pointer to an abstract count, `M::&[u8; T::SIZE]`, needs
  `T::SIZE` to fit `M::Size` for well-formedness. Either the signature writes
  the fit clause, or the obligation is proved where the signature is
  instantiated (the substituted pointer type must be well-formed at the
  call). The second is how `M::&S` with `S: Array` already has to work: a
  caller cannot name `heap::&[u8; 2^40]` because that type is ill-formed.

## Generic constants (later, separate)

`const PAGE_SIZE<S: PointerSize>: S = 65536;` is the bounded form: `S` is a
bound, proved once for each member at the definition, and every instance is
typed. Use it when one definition must be safe at every type of a set without
per-use checks (`PAGE_SIZE` in abstract-memory code). `{integer}` is not a
bound and checks nothing ahead of time; the two coexist. Typesets never go
inside the braces.

## Order of work

Each step ends with tests green.

1. Reject impls written for structural types. Already the case: an impl's
   target is a path, resolved by `ImplDispatchBuilder::resolve_target` to a
   struct, an enum or a primitive item, and anything else (an alias of a
   slice included) is `InvalidImplTarget`. Pinned by a test (2026-10-30).
2. Done (2026-10-30). Untyped constants, free constants: parse `{T}`, std's `pub type integer;`
   and `pub type char;` bound to their slots, the bare-path error, the
   literal-kind half of the runtime-position rule, constant bodies checked
   against their kind, exact arithmetic in `eval.rs`, the `coerce` arm,
   untyped constants as lengths.
3. The region split: `Pointer { to: Slice | Array }` across `tir/` (about 80
   sites, a third of them in `types.rs`), the fit check on the pointer,
   `layout`/`stack_elements` reading the pointee, `implements_structurally` on
   the pointee, the rule for parameters holding regions, the receiver
   conversion, std's traits as above. With it, in the same commit or the next:
   array and string literals as regions (`[{integer}; 3]`, `[u8; 5]`),
   placement through `coerce_static`, `M::&[u8; _]` learned from the literal,
   slots 18/19 retired, and the region half of the runtime-position rule.
4. Indexing as a built-in place, with std's `index`/`index_mut`/`first_mut`/
   `last_mut` removed.
5. Fit clauses: the `where { const NAME: ty }` syntax, `FitClause`, the
   solver's case and implication between fits, coercion of abstract
   constants, untyped trait constants (`Array::SIZE`).
6. Generic constants.

MIR lowering can start after step 3; it needs the final shape of pointers.
Steps 4 and 5 can go alongside it.
