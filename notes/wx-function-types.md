# Function types, the `Function` trait and the one-parameter rule — design note

**Status: partly implemented.** The one-parameter rule (§2) is in:
`Type::FunctionRef` is the `func(A) -> R` type, and a declared function is
its own zero-sized type `Type::Function`, named like a struct (`foo<i32>`,
always fully applied). There is no `Function` trait yet, and calls are not
checked in bodies. Written 2026-10-16
on `tir-refactor`, from a design discussion that went through several
rejected alternatives (§7). The first version of this note used a
parameter-list slot with a `..` spelling; it was replaced the same day by the
one-parameter (ML) rule below (§7.6).

Related: `wx-tables-references-design.md` (handles vs references, `as_ref`,
tables), `wx-named-invocation-and-struct-constructors.md` (call syntax).

---

## 1. Goals

1. Let generic code describe a callable by its parts, an argument type and a
   result type, and **rebuild the exact function type** from those parts.
2. Do it without variadic generics, without any spread syntax, and without a
   marker trait such as `Tuple`.
3. Keep calling a compiler operation: a call is a builtin node, not a call to
   a library intrinsic.
4. Allow table handles to be allocated without the reference-types proposal
   (incremental feature adoption, `wasm-extensions-incremental`).

---

## 2. Every function takes one parameter

```
Type::FunctionRef { param: TypeIndex, result: TypeIndex }
```

A function type has exactly **one** parameter type. A written parameter list
is sugar for it:

| Written            | Parameter type |
| ------------------ | -------------- |
| `func() -> R`        | `()`           |
| `func(A) -> R`       | `A`            |
| `func(A, B) -> R`    | `(A, B)`       |
| `func((A, B)) -> R`  | `(A, B)`, the same type as `func(A, B) -> R` |
| `func((A,)) -> R`    | `(A,)`, distinct from `func(A) -> R` |

- **`(T)` is grouping, `(T,)` is the one-element tuple,** as in Rust. So
  `func(A)` and `func((A,))` are different types, and no one-element tuple appears
  unless written.
- **A declared function's parameter type follows the same table:**
  `func f(a: A, b: B)` has `(A, B)`, `func f(x: A)` has `A`, `func f()` has `()`.
  `func g(p: (A, B))` therefore has the same type as `func f(a: A, b: B)`.
- **Rebuilding** needs no new syntax: `func(F::Args) -> F::Result` is exactly
  the type of `F`.
- **Equality** is equality of the parameter types. The sugar is resolved when
  the type is lowered, so there is one canonical form.
- **No new normalization.** The parameter type normalizes like any other type.
- **Matching is plain unification.** `func(A) -> R` against `func(i32, u8) -> R`
  gives `A = (i32, u8)`: a one-parameter pattern matches a function of any
  arity. `func(A, B) -> R` is `func((A, B)) -> R` and matches only a two-element
  tuple.
- **The surprising part, accepted:** a tuple parameter and a parameter list
  are the same type, and a pattern written with one parameter matches several.
  Both only show up in generic code and in type errors.

### The flattening convention this needs

Identifying `func((A, B))` with `func(A, B)` is sound only if both lower to the
same wasm signature, in the same order. The convention:

- A function's wasm parameters are its parameter type **flattened in
  declaration order**.
- Every aggregate (tuple or struct) flattened into scalars (parameters,
  results, locals) uses declaration order. **Alignment sorting is a memory
  layout concern only**, and a value in wasm locals is not in memory.

`call_indirect` checks only the wasm signature, which erases most wx
distinctions, so it is not a safety backstop for handle types. A handle's type
holds as long as its slot is not refilled with another signature. That is the
same aliasing problem as reused linear memory, left to the future borrowing
rules.

---

## 3. Calls

Calling is the compiler's job, chosen by the callee's type:

| Callee                     | `f(..)` lowers to                                           |
| -------------------------- | ----------------------------------------------------------- |
| a function item (ZST)      | a builtin direct `call`                                     |
| a function reference       | `call_ref` (reference types, opt-in)                        |
| a table handle `T::func(..)` | `call_indirect` (MVP)                                       |
| an abstract `F: Function`  | `GenericMethodCall`-like, resolved at monomorphization      |

**Positional arguments form one value the same way a parameter list forms
one type:** no arguments give `()`, one argument gives itself, several give a
tuple. That value is checked against the callee's parameter type, for every
kind of callee.

```wx
func apply<Args, R>(f: func(Args) -> R, args: Args) -> R {
    f(args)
}

apply(add, (1, 2))      // func add(a: i32, b: i32): Args = (i32, i32)
apply(neg, 5)           // func neg(x: i32): Args = i32
```

- With a parameter type `(A, B)`, both `f(a, b)` and `f(pair)` are valid.
- With an abstract parameter type (`F::Args`, a type parameter), `f(args)`
  passes it whole.
- A generic body is checked once against its abstract parameter type, so
  monomorphization never re-decides a call.
- **Named arguments** (`f({ x: 1 })`) are checked against the callee's
  **declaration**, so only callees with one have them: items, constructors,
  and later closures of known type. References, handles and abstract `F`
  are positional only. Names belong to declarations, never to types.

---

---

## 4. The `Function` trait

```wx
pub trait Function {
    type Args;     // the parameter type (§2)
    type Result;
}
```

- **Impls are built into the solver,** not synthesized per function. A
  `Type::Function` answers `Args` and `Result` from its signature:
  - `Args` is the parameter type: `()`, `A`, `(A, B)`, ….
  - `Result` is the return type.
- **The exact type is rebuilt** by `func(F::Args) -> F::Result`.
- **`Function` means "a statically known wasm function":** a ZST, no
  environment, fit for `ref.func` and element segments. Function references
  and handles are values of their own types, which already describe their
  shape, and they do not need this trait to be called.
- **`as_ref` (`ref.func`)** belongs here once reference types are adopted, as
  the one intrinsic with a wasm cost (`wx-tables-references-design.md`).
  `call`/`call_ref` as std intrinsics are **not** needed: calling is §3.
- **Which functions get the impl:** every declared function. A method is an
  item like any other, with the receiver as its first parameter. A trait
  method is an item generic over `Self`: `<T as Trait>::method` normalizes to
  the impl's member once `T` is known, and while `T` is abstract its
  `Args`/`Result` come from the trait's signature with `Self = T`.

---

## 5. Table handles without funcref

Allocating a slot must not require the reference-types proposal. With bulk
memory's passive element segments, a slot is filled from an **item**:

```wx
#[intrinsic]
func table_init<T: FuncTable, F: Function>(
    table: T, at: T::Size, f: F,
) -> T::func(F::Args) -> F::Result;
```

- It lowers to `table.init` from a one-element passive segment for `F`, and
  the handle is called with `call_indirect`, which is MVP.
- The allocation policy (append via `table.grow`, a free list, an arena) is
  **library code** over the table intrinsics, and the compiler never picks a
  slot.
- With **reference types** adopted: `as_ref` and `table.set` with a reference
  are added on top, and nothing above changes.
- With **plain MVP** (no bulk memory), the only way to fill a table is active
  element segments at fixed indices. That needs a declaration, such as a slot
  attribute, not a runtime allocator. Not designed yet.

---

## 6. Closures (later)

- A closure is an anonymous struct holding its captured environment, with
  built-in call impls whose `call` takes the environment first.
- A function item is the degenerate case: a closure with an empty environment.
  That is why it alone implements `Function`.
- The future traits take the environment by value, by `M::*Self` and by
  `M::&Self` (once, mut, ref), generic over `M: Memory`. They reuse
  `Args`/`Result` unchanged.
- A method used as a value, `obj.method`, is a closure over `obj`.
  `Type::method` is an item.
- **Runtime representation:**
  - A closure that is statically known is monomorphized, with no table.
  - A type-erased one is (handle or reference, environment pointer).

---

## 7. Rejected alternatives

1. **Synthesized impls per function**, like `Global`'s. They cost arena
   entries for every function, and a solver rule covers items and every other
   callable uniformly.
2. **A general tuple spread** (`(..A, u8, ..B)`). It needs a flattening
   normalization, a "tuple" bound for operands, and a canonical form
   (`(..T)` ≡ `T`). Inference also becomes ambiguous: `(..A, ..B)` against
   `(u8, u16)` has several solutions. Spreading a non-tuple "as is" makes
   `T = i32` and `T = (i32,)` the same type.
3. **A `Tuple` marker trait, or `<..Args>` pack parameters.** Spread syntax is
   allowed only inside the type, never in a parameter declaration, and a
   marker trait needs implied bounds.
4. **A single `type Signature` / `type Ref` associated type** holding the
   whole `func(..)` type. A signature cannot be put back together from parts,
   and it ties the description to function references, which need reference
   types. Handles must be expressible without them (§5).
5. **Wrapping a non-tuple slot as `(X,)`** (in the slot design of 6). It is
   non-injective: `A = i32` and `A = (i32,)` give the same type.
6. **A parameter-list slot with a `..` spelling** (the first version of this
   note). `func(A)` had slot `(A,)`, and `func(..X)` put `X` into the slot as is,
   with `f(..x)` as the counterpart at calls. It mirrors Rust (`Fn(A)` is
   `Fn<(A,)>`, untupled by the internal `"rust-call"` ABI) and keeps
   `func((A, B))` distinct from `func(A, B)`. Replaced by the one-parameter rule
   because it needs `..` in two places, one-element tuples at every generic
   call (`apply(f, (5,))`), and `func(..u32)`, a type no item can have. Its one
   real objection to the one-parameter rule, that the ABI must flatten a tuple
   and a parameter list alike, is met by the flattening convention (§2).
7. **`func(i32,)` forcing a one-element tuple.** It is only another spelling of
   `func((i32,))`, and Rust readers expect it to mean `func(i32)`.

---

## 8. Open points

- **Methods of generic impls.** `Type::Function { func_index, type_args }`
  carries only the function's own type arguments. A method of
  `impl<T> Wrapper<T>` has no place for `T`, so it cannot be a value or
  implement `Function` until the item type also carries the parent impl's
  arguments.
- **Today's `func` pointer** is an index into a hidden implicit table. Under
  this design, `func(..)` written bare is a **reference** (`call_ref`, reference
  types) and `T::func(..)` is a **handle**. That is a breaking change in
  meaning, and it needs the gating decision from
  `wx-tables-references-design.md`.
- **The flattening convention** (§2) must be checked against MIR when it is
  revived: field access there goes through `decl_to_phys`, which is a memory
  layout concern, and flattening into parameters must not use it.
- **The plain-MVP slot declaration** (§5): spelling and semantics.
