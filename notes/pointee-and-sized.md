# `Pointee` and `Sized`

Status as of 2026-11-26: **designed; infinite types implemented** (see
"Infinite types"), the traits not yet. A follow-up to
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
   caught by a finiteness check in checking (see "Infinite types").
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

Decided 2026-11-25, planned. Infinite types are reported by checking, never
by monomorphization. Finiteness is its own judgement, separate from
well-formedness and from `Sized`:

| | Well-formedness | Finiteness |
|---|---|---|
| Asks | the type's requirements on its arguments hold: declared bounds, projections normalize, representability clauses (`N` fits `M::Size`) | expanding what the type holds directly terminates |
| Reach | local to each constructor, applied to every part | follows fields through definitions, type arguments substituted |
| Pointers | followed: `heap::*X` needs `X` well-formed | stop it: `struct A(next: heap::*A)` is finite |
| Code | `TypeObligation::CheckWellFormed`, pushed for every written type | queries on `Semantics`, cached in the solver: the struct pass and the projection walk (`finiteness.rs`) |

Finiteness does not wait for well-formedness: a query may run before the
struct's own obligations are checked (see "Where checking runs them"). A
field that fails to normalize is a leaf, silently; its well-formedness check
reports it. Rust calls it "representability" (E0072), but WX uses
"representable" for a constant fitting a type, so the name here is *finite*.

Neither implies `Sized`: `[u8]`, `[[u8]]`, `[[u8]; 4]` and a struct with a
slice field are well-formed, finite and unsized. Array and slice elements
need only be well-formed and finite. `Sized`, `Pointee` and `StackValue` are
separate obligations; their walks ask finiteness on entering a struct and
never meet a cycle themselves.

What is followed: struct and tuple fields, array and slice elements, with
type arguments substituted. Pointers, functions, `funcref` and enums stop
it. `struct A(x: u32, tail: [A])` is infinite: its metadata
would contain its own metadata. Array lengths are not read (see "Layout
cycles are not infinite types"). `[A; 0]` inside `A` is rejected too
(decided 2026-11-25): it takes zero bytes, but reading lengths would put
constant evaluation in the walk and make abstract lengths a per-instance
question; a struct nesting itself through an empty array has no use.

### Two checks

1. **The struct pass** judges each definition once, its type
   parameters unknown. It is exact for everything not passing through a
   projection, and it is what makes generic code safe: a finite struct is
   finite for every finite argument.
2. **The projection walk** follows what a struct stores through a projection
   (`struct S<T: Id>(x: T::This)`), whose value an impl chooses, so the
   definition cannot decide it.

### The struct pass

The question per struct: does walking its fields, with its own parameters
unknown, reach the struct again?

```wx
struct W<T>(v: T);          // stores T directly; never reaches W
struct P<T>(p: heap::*T);   // stores nothing directly that depends on T
struct A(w: W<A>);          // A → W<A>, W stores its T directly → A: a cycle
struct B(x: P<B>);          // B → P<B>, P does not store T directly: finite
struct S<T>(x: W<S<T>>);    // S → W<S<T>> → S: infinite for every T
```

Walking a field type:

| Found | Action |
|---|---|
| tuple, array, slice | walk the elements |
| pointer, function, `funcref`, primitive | nothing |
| the struct's own parameter or a projection over its parameters (`T`, `T::This`) | record it in the struct's `direct_deps` |
| a projection that resolves in the struct's own scope (`<u32 as Id>::This`) | normalize, walk the result |
| enum | nothing: its repr is one integer field |
| struct `D<args>` | judge `D`; if on the stack, a cycle; if `Finite`, substitute `args` into each of `D`'s `direct_deps`, normalize, walk the results |

A struct that finishes is `Finite` with its `direct_deps`: what it stores
directly that depends on its parameters. A parameter dependency substituted
is the argument itself; a projection dependency is normalized. So parameters
and projections need no separate cases.

An enum is a leaf: its repr is exactly one integer field (`EnumSignature`
makes anything else `ERROR`, reported). Decided 2026-11-26: enums get no
state column until a repr can be an aggregate; then an enum is judged as a
struct is (`struct S(tag: u8, e: E); enum E(s: S) { ... }` is an ordinary
cycle) and gets its column and a `StepOwner::Enum`.

Without projections the pass is exact and compositional: if no struct
reaches itself, structs can be ranked by depth, and expanding any finite
type terminates by induction on (rank, size). So `S<T>` in a generic body,
and every type monomorphization forms from finite arguments, is finite once
`S` is.

### The projection walk

A struct's projection dependency is followed at an instance: `S<u32>` substitutes
`T = u32` into `T::This`, normalizes `<u32 as Id>::This` and walks the result.
Implemented 2026-11-26:

- **When.** Where a struct with a projection dependency is met, the
  dependency is substituted and normalized in the current context. If it
  resolves, the instance is judged: its fields, with its arguments
  substituted, under its key. If it stays abstract, it is a dependency of
  the current owner when it has parameters.

- **Exact repeat.** Reaching the same instance again on the current path is
  a cycle (`impl Id for u32 { type This = S<u32>; }`). Reaching the same
  struct again is not:
  `impl Id for u32 { type This = S<u8>; } impl Id for u8 { type This = u8; }`
  makes `S<u32>` hold `S<u8>`, which holds a `u8`.
- **Budget.** A generic impl can make the instance grow without repeating
  (`impl<T: Id> Id for W<T> { type This = S<W<W<T>>>; }`). With projections,
  type-level computation is Turing-complete, so the instances in a
  request's segment are counted against `recursion_limit`. At the limit it
  is reported once, from the first instance in the segment, as E2025
  ("expanding `S<W<u8>>` exceeded the recursion limit", the first steps as
  labels, the limit in a note), and every owner from it up is `Infinite`.
  A finite type deeper than the limit is rejected; accepted.

Considered and rejected:

- **A shrink rule** (returning to an impl member needs strictly smaller
  arguments): needs no budget, but rejects finite types and its verdict
  depends on the path. This program checks and builds today, and the rule
  rejects `S<W<u8>>` while accepting `S<W<W<u16>>>`, which it contains:

  ```wx
  trait Id { type This; }
  struct W<T>(v: T);
  struct S<T: Id>(x: T::This);
  impl<T: Id> Id for W<T> { type This = S<T>; }
  impl Id for u8 { type This = S<W<W<u16>>>; }
  impl Id for u16 { type This = u32; }
  ```

- **Forbidding open projections in fields** (only typeset-bounded ones such
  as `Mem::Size`, or behind a pointer): the struct pass alone would then be
  exact, and a projection cycle would become a normalization cycle (E2073,
  as `impl Id for u32 { type This = S<u32, <u32 as Id>::This>; }` reports
  today). Rejected: storing `G::Value`, `P::Metadata` or a user trait's
  associated type by value is common enough.

### Where checking runs them

Decided 2026-11-26, revising "after signatures, a pass over every struct".
Finiteness is a query, computed by whoever asks first and cached, as a
constant's value is:

- **Who asks.** The walks over fields, on entering a struct:
  `push_stack_elements` (from `CheckValueType`, and from normalizing
  `<X as StackValue>::Repr`), layout (from constant evaluation and
  lowering), constant evaluation's own `push_scalars`, and lowering's
  assertion. And `check_declarations`, which asks
  for each `Struct` entry as it reaches it, so an unused
  definition is judged too, as `check_constant_bodies` evaluates the
  constants nothing read. It needs no `TypeObligation`: the index is all it
  takes.
- **Where it is reported.** When the cycle closes, inside whatever request
  closed it, as `close_const_loop` reports a constant cycle: the chain is
  read from the stack, rotated to its first-defined member, reported, and
  every member becomes `Infinite`. The chain is not stored. Its text does
  not depend on who asked first; its position among the diagnostics does:
  a cycle reached from an earlier use comes out there, an unused one at its
  definition.
- **What it says.** The message names the cycle's members ("recursive
  type `A` has infinite size"), each with a primary label. Every step of the
  chain is a secondary label on the field's name, saying which type it
  stores directly, the cause of the infinite size: for
  `struct W<T>(v: T); struct A(w: W<A>)`, on `w` "`W<A>` in field `w` of
  `A` is stored directly", on `v` "`A` in field `v` of `W<A>` is stored
  directly". The note: "hold one of them through a pointer to break the
  cycle". Field type spans are not kept (`FieldArena` has name spans only),
  and the message carries the type.
- **Readers.** `Infinite` gives every later reader (a place through
  `heap::*A`, layout, `StackValue`, lowering's assertion) `Poisoned`, and it
  stays silent. A struct holding a cycle without being in it
  (`struct Outer(a: A)`) becomes `Infinite` silently: the cycle was reported
  once, at its closure, so no one owns a second report.
- **Why not a pass before `check_declarations`.** The pass normalizes field
  types, and normalizing a `Repr` walks fields (`compute_stack_value_repr`),
  so it would meet structs it has not judged. A pass also prints every
  finiteness error before every other declaration error.
- **Why not an obligation per struct.** Obligations run entry by entry, so a
  function declared before `A` would reach `A` through `StackValue` before
  `A`'s obligation ran; the walks would keep their guards.

Considered: a `Cyclic` state beside `Infinite`, keeping the chain or marking
members, as `Verdict::Cyclic` does for an owner's check to report. Not
needed: the report happens at closure, and every reader treats a member and
a container alike.

This is exact, not a guess about unknown arguments: for a definition the
pass answers either "infinite for every argument" (`struct S<T>(x: W<S<T>>)`,
an error in the definition) or "finite whenever the arguments are"
(`struct W<T>(v: T)`, the conditional answer kept in `Finite { direct_deps }`).

The projection walk is per instance:

- **Impl values: the member owns the failure** (decided 2026-11-26). An
  impl member's judgement (`assoc_value`) judges its value's finiteness
  once it has normalized, in the impl's context, with the verdict already
  `Resolved`: the instance walk normalizes through the same member and must
  read its value, so the repeat is seen on the finiteness stack, not as the
  solver's `InProgress` loop. An infinite value makes the verdict
  `Verdict::Infinite`; finiteness reported it at closure, `CheckAssocValue`
  stays silent, and every reader of the member gets `Poisoned`. So an
  instance derived from it (`S<W<u32>>` from
  `impl<T> Id for W<T> { type This = S<W<T>>; }`, a generic impl walked
  with its parameters abstract) normalizes to `Poisoned`, a silent leaf:
  one report, at the impl, whichever is declared first. A `Poisoned`
  answer (an owner in progress in an outer request) leaves the member
  `Resolved`: that owner owns the loop. `CheckAssocValue` asks every
  member, so an unused value is judged too.
- **Uses**: the walks and lowering ask `type_is_finite(env, ty)` for what
  they enter, which judges an instance where its projection resolves.
  Cached, and nothing for a struct without a projection dependency.

A cycle is reported once, when it closes; its members, struct or instance,
become `Infinite` then.

### Checking and monomorphization

- Monomorphization substitutes judged types into judged types. Lowering
  asserts finiteness before `lower_aggregate_type` builds a shape (a cached
  read); a failure is a hole in checking and panics.
- Not proven: that every projection cycle closes at an impl value checking
  walks. A type formed only in monomorphization (`S<T>` in a generic body
  instantiated as `S<u32>`) is never walked as a concrete type in checking.
  Every example tried closes at an impl; the cases below are built through
  `wx build` to test it.
- Polymorphic recursion is not a type error: `grow<T>` calling
  `grow(Wrap(x))` forms only finite types, infinitely many. It stays with
  the instantiation limit in lowering (`RECURSION_LIMIT`, `tir/lower.rs`),
  the one diagnostic monomorphization reports. See "Open".

### Data

In `Solver`, next to `layouts`; the walks in `impl Semantics` in
`tir/finiteness.rs`, as `layout.rs` splits `Layouts` from its walk. Final
answers and work in progress are kept apart, as the solver keeps
`normalized` and `verdicts` apart from `SolverState::frames`.

```rust
pub(super) struct Finiteness {
	structs: Vec<Option<Expansion>>,               // None: not judged yet
	instances: FxHashMap<InstanceKey, Expansion>,  // absent: not judged yet
	direct_deps: Vec<TypeIndex>,
	stack: Vec<Step>,
}

enum Expansion {
	Finite { direct_deps: DirectDeps },
	Infinite,
}

/// What a finite owner stores directly that depends on the parameters in
/// scope, by kind, as runs of `Finiteness::direct_deps`.
struct DirectDeps {
	params: DepRun,       // `T`: substituted, the argument itself, walked
	projections: DepRun,  // `T::This`: resolves at an instance, or stays one
}

struct DepRun {
	start: u32,
	len: u32,
}

struct InstanceKey {
	env: AssumptionEnvIdx,
	ty: TypeIndex,
}

struct Step {
	owner: StepOwner,
	field: FieldIdx,
}

enum StepOwner {
	Definition(StructIdx),
	Instance(InstanceKey),
}

enum Progress {
	Idle,
	InRequest { at: usize },  // closes a cycle
	InOuterRequest,           // reached through normalization: `Poisoned`
}
```

- `Expansion` is the one answer for definitions and instances, cached in
  `structs` and `instances` and returned by the judgements; `Progress` is
  where an owner stands relative to the stack, a pure query the judgement
  acts on. The public queries answer a `bool`: `struct_is_finite(StructIdx)`
  for `check_declarations`, `type_is_finite(env, ty)` for everything else.
- A `Step` says that its owner holds its field's type directly. The stack
  holds definitions and instances being judged; a report's chain holds the
  members from the stack, and the `Instance` steps it finds again inside
  finished structs (`W<A>`'s `v`). One label is built from either: the
  owner is the struct's name or the instance, and the held type is the
  field as written or with the instance's arguments substituted.
- `direct_deps` is an arena of its own: each finite owner appends its two
  runs once, when it finishes, each dependency once. Not the type
  interner's lists: those are types' parts, and this is finiteness's own
  data. The kind is decided once, where the walk finds a dependency (a
  parameter, or a projection that stays abstract), so a use never re-derives
  it; after substitution it could not, since a parameter whose argument is
  a projection looks like one.
- `InstanceKey`: the facts in scope can change what an instance with
  parameters resolves to (a method's `where` clause adding an equality on
  its impl's parameter), so it is keyed with its environment; one with
  nothing abstract under the root environment, as `Normalization::new`
  does, so every use shares one answer.

- **The stack** is the only place work in progress lives. An owner already
  on it closes a cycle; the chain is the stack from that owner up, each step
  with its field, as the solver reads a projection cycle from `frames`
  (`projection_steps`), used for the report at once and dropped. The one
  link not on it, the field of a finished generic struct that holds the
  next step (`W`'s `v` holding `T`), is found again while the report is
  built, as `explain_non_stack_value` does. The depth is `stack.len()`
  against `Solver::recursion_limit`. `Pending` truncates the stack to where
  the request started; nothing was reported or written, so a retry starts
  clean.
- **Re-entry** (decided 2026-11-26): finiteness normalizes a field,
  normalizing a `Repr` walks fields, and that walk asks finiteness again.
  Each request starts its own segment of the stack, and only an owner in
  that segment closes a cycle, since only links the walk pushed itself are
  direct storage. An owner in progress below it was reached through
  normalization, so the answer is `Poisoned`: the loop is a definition
  cycle, which the solver reports (E2073), not infinite size, as a layout
  cycle is (see "Layout cycles are not infinite types"). In
  `struct A(y: <B as StackValue>::Repr); struct B(a: A)`, `B` holds `A`
  directly but `A` holds whatever `Repr(B)` is: `A`'s field must satisfy
  `X = Repr(X)`, undetermined rather than infinite. The nested request
  records nothing (the stack is truncated, as for `Pending`), so `B` is
  judged again at its own entry. The segment's start is a parameter of the
  walk.
- **Instances** exist because a struct with a projection dependency has a
  conditional answer: `Finite` with `T::This` means `S<X>` is finite when
  `<X as Id>::This` is, which depends on `X` (`S<u32>` infinite, `S<u8>`
  finite above). A struct with only parameter dependencies needs none: `W<X>` is
  finite when `X` is, so walking `W<S<u32>>` judges `S<u32>` and not
  `W<S<u32>>`. The map is not how cycles are found (the stack is); it
  caches a walk that may run to the budget, for later uses and lowering's
  assertion, and makes an infinite instance reported once. An instance has
  its own `direct_deps`: a generic definition holding an instance that
  resolves in its context (`struct G<T>(s: S<W<T>>)` with
  `impl<T> Id for W<T> { type This = (T, u32); }`) stores `T` through it.
  Without projections in fields the map stays empty.
- The struct column is sized in `Solver::new` from `decls`, as
  `const_values` is. Both walks are plain recursion. An owner's
  dependencies are collected by kind in a local `FoundDeps` and appended to
  the arena when it finishes.

### Relation to the solver

Reused: `normalize` and its cache (called from outside, with its own frames,
projection cycles and overflow), `recursion_limit`, `SolverError` and the
overflow diagnostic, the split of final answers from a stack of work in
progress (`verdicts` and `frames`), the
root-environment key rule, reporting a cycle where it closes and poisoning
its members (`close_const_loop`), and the existing "recursive type has
infinite size" diagnostic (`RecursiveTypeWithoutIndirection`).

Not reused: `SolverState::frames`. The shared stack exists for work that
calls into itself across kinds (normalization, judgements, evaluation).
Normalization does expand fields, through `StackValue::Repr`
(`compute_stack_value_repr` → `push_stack_elements`), but that walk asks
finiteness rather than following a cycle, and a request through it starts
its own segment (see "Re-entry" under "Data"), so a loop through both is
the solver's. Frames pushed by finiteness would only turn off the
normalization cache, which is read only with no frame open (the TODO above
`normalize` would lift that). If finiteness ever evaluates constants, it
moves onto `frames`.

### Layout cycles are not infinite types

```wx
struct A(x: [u8; <A as Sized>::SIZE]);
```

`A` stores only `u8`s; what loops is its size. Evaluating
`<A as Sized>::SIZE` opens an `Evaluation` frame; the layout it needs reads
the field's length, which evaluates the same instance, `InProgress`: the
constant cycle check on the shared stack catches it, with a diagnostic that
says the size of `A` depends on itself. `CheckWellFormed` normalizes the
written field type with every rewrite on, `VALUES` included, so this is
reported in checking, used or not. Requirements, for `Sized`:

- Layout runs inside the evaluation that asked for it, so the loop stays on
  one stack.
- Finiteness reads no array length and normalizes without `VALUES`
  (`RewriteFlags::EQUALITIES | DEFINITIONS`); otherwise it would reach
  `<A as Sized>::SIZE` while `A` is on its stack and report infinite size for
  a finite type.

### Cases

Rejected:

| Source | Through |
|---|---|
| `struct A(a: A)`; `struct A(b: B); struct B(a: A)` | fields |
| `struct W<T>(v: T); struct A(w: W<A>)`, in either order | a type argument |
| `W<W<A>>`, `(u32, W<A>)`, `P<u32, A>` | nesting |
| `struct G<T>(w: W<T>); struct A(g: G<A>)` | a generic chain |
| `struct S<T>(x: W<S<T>>)`, `struct S<T>(x: S<W<T>>)` | the struct's own definition |
| `struct B(w: W<C>); struct C(w: W<B>)`, reported once | mutual, through arguments |
| `type WA = W<A>; struct A(w: WA)` | an alias |
| `struct A(x: u32, a: [A; 2])` | an array |
| `struct A(x: u32, tail: [A])` | a slice |
| `impl Id for u32 { type This = A; } struct A(x: <u32 as Id>::This)` | a projection resolved in the definition |
| `struct S<T: Id>(x: T::This); impl Id for u32 { type This = S<u32>; }` | a projection, at the impl |
| `impl<T> Id for W<T> { type This = S<W<T>>; }` | a generic impl, exact repeat |
| `impl<T: Id> Id for W<T> { type This = S<W<W<T>>>; }` | a generic impl, growing: overflow |

Accepted:

| Source | Why |
|---|---|
| `struct W<T>(v: T); struct A(w: W<heap::*A>)` | a pointer stops the walk |
| `struct Handler(s: heap::*State); struct State(h: Handler)`, in either order | the same, through a struct |
| `struct G<T>(w: W<T>); struct A(g: G<u32>)` | the argument does not embed `A` |
| `struct Table<L: Level>(entries: [L::Child; 4])` with `u32 → Table<u16>`, `u16 → u8` | different impl members |
| `impl<T: Level> Level for W<T> { type Child = Table<T>; }`, `Table<W<W<u16>>>` | recursion that shrinks |
| the shrink-rule program above, `S<W<u8>>` | finite, reached through a larger argument |

Wrong argument counts (`W`, `W<A, A>`) report only the count. Every
rejected row that `wx check` accepts today and `wx build` crashes on is
also a build test.

### Implementation steps

Steps 1–5 are implemented (2026-11-26), with the cases above written first
as tests in `tir/finiteness.rs`; steps 1–4 fix the three crashes in "State
of the code".

1. **The struct query**: `Finiteness` with the state column, `direct_deps`
   and the stack; the report at closure, from the stack.
2. **The projection walk**: instances on the same stack, the instance
   map, the depth limit; an impl member's judgement judges its value.
3. **Checking calls**: `check_declarations` asks for each struct entry;
   `check_struct_direct_recursion` and its query-stack chain are removed.
4. **The walks rely on it**: `push_stack_elements`, its diagnostic
   (`explain_parts`), layout (`finite_form`/`aggregate_form`, which
   returned a `Piece`, now `MemoryForm`) and `push_scalars` (`eval.rs`)
   rely on finiteness (step 5 replaced how); lowering asserts finiteness
   before expanding a struct's fields.
5. **Structural**: `FiniteType { env, ty }`, a type whose direct contents
   expand finitely under `env`, which only finiteness constructs.
   `finite(env, ty)` judges a walk's root once (`Poisoned` when infinite);
   `normalize_finite` normalizes under the type's own facts, with every
   rewrite (constant values change only lengths and named constants, never
   what is stored directly); `parts` is one expansion step (a struct's
   fields substituted, a tuple's elements, an array's or slice's element,
   an enum's repr), each a `FiniteType`. A list rather than a `Shape` enum:
   the walks keep their own matches for leaves, pointers and lengths. The
   four walks take `FiniteType` and dropped their visiting stacks, depth
   budgets and per-struct questions; a pointer's address size and metadata
   are judged as roots of their own. The diagnostic walk's "root or part"
   test became two functions (`explain_parts`, `explain_part`). Lowering
   keeps `TypeIndex` and its one cached assertion: threading the token
   through it would change much for little.

### Interim

Merged in #29: naming a struct needs only its type parameters
(`SignatureQuery::StructParams`), so a pointer breaks a cycle in any
declaration order. Written on 2026-11-24, not merged: substituting a generic
struct's type arguments into its fields in the declaration check. Both are
superseded by the steps above.

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
- Polymorphic recursion in checking. Expanding cycles (a call in a cycle
  whose argument wraps a parameter, `T` to `Wrap<T>`) are detectable on a
  graph of generic calls, as .NET does; recursion through a projection
  argument (`T` to `T::Next`) is not, and would need the limit or a
  conservative rejection. Not now: checking has no call graph, and the
  instantiation limit in lowering covers it.

## State of the code (2026-11-25)

- `compute_pointer_metadata` (`solver.rs`) handles only `[T]`. Structs,
  tuples and arrays of unsized types fall into `_ => UNIT`, so
  `heap::&Message` is a thin pointer, unlike the table in "Unsized fields".
- `p[1][0]` on `heap::&[[u8]]` checks, and `wx build` reports E2085 "lowering
  a slice that is a field", which misnames the case. A struct field of
  slice type hits the same E2085.
- `size_of` is replaced inline during lowering (`lower/intrinsics.rs`) and
  cannot be evaluated in a constant (E2042). Constant evaluation computes
  layouts only to place static data (`eval.rs`, `place_static`).
- Infinite types passed `wx check` and crashed `wx build` (reproduced
  2026-11-25; fixed 2026-11-26, "Implementation steps" under "Infinite
  types"):

  | Program | `wx build` |
  |---|---|
  | `struct W<T>(v: T); struct A(w: W<A>)`, `A` a parameter | stack overflow |
  | `struct A(x: u32, a: [A; 2])`, read through `heap::*A` | panic "lowering without an error diagnostic produces MIR" |
  | `struct S<T: Id>(x: T::This)`, `impl Id for u32 { type This = S<u32>; }`, `S<u32>` a parameter | stack overflow |

  The checking walks see the cycle but answer `Poisoned`, as for an error
  type ("reported where it is declared"), and the declaration check
  (`check_struct_direct_recursion`, `signatures.rs`) neither substitutes
  type arguments nor follows arrays, so nothing reports it. Six walks
  guard themselves, or not:

  | Walk | Guard | A cycle comes back as |
  |---|---|---|
  | `push_stack_elements` (`StackValue::Repr`, `solver.rs`) | a `visiting` stack (structs) and a depth against `recursion_budget` | `Poisoned` or `Overflow` |
  | `explain_non_stack_value_inner` (its diagnostic) | its own `visiting` stack | `Poisoned` |
  | `piece` / `aggregate_piece` (`layout.rs`) | its own `visiting` stack and the budget | `Poisoned` |
  | `push_scalars` (constant evaluation, `eval.rs`) | its own `visiting` stack and the budget | `Poisoned` |
  | `compute_pointer_metadata` (`solver.rs`) | the solver's frames, through normalization; only slices recurse | the solver's verdicts |
  | `lower_aggregate_type` (`lower/shapes.rs`) | none: it recurses through `lower_type` and caches a shape only after its fields | native stack overflow |

- Thinness of an abstract pointee is approximated by `StackValue` or `Array`
  (`compute_pointer_metadata`; core's `RawPtr<Mem, T: StackValue>`). Under
  this design the bound is `Sized`, and those signatures move to it.

## Order of work

0. Finiteness, steps 1–5 of "Implementation steps" under "Infinite
   types": done 2026-11-26. Independent of the traits below.
1. `Sized`, as in "Sized" of `slices-and-untyped-constants.md`: replaces
   `size_of`/`align_of` and gives array elements their stride; its layout
   runs inside constant evaluation ("Layout cycles are not infinite
   types"). Needs no generic associated types.
2. Generic associated types, as a language feature with its own tests
   (`generic-associated-types.md`, "Stages, if revived").
3. `Pointee` with `Metadata<Size>`; `Pointer`'s metadata derived from it;
   `[T]`'s rule moved to core.
4. Compiler-answered `Pointee` for structs and tuples with unsized fields,
   and arrays of unsized types; the gaps above.
5. Core: `copy`, `deallocate`/`free`, matrix views, array conversions, as
   their first users appear.
