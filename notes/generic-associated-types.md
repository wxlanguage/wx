# Generic associated types

Status as of 2026-10-31: planned, nothing implemented. Motivated by
`Pointee` (see "Unsized fields" in `slices-and-untyped-constants.md`).

## Why

A pointer's metadata is a type of its pointee's, made of lengths whose type
is the pointer's memory's `Size`. The pointee does not know the memory, so
the size has to be an argument. Two places can take it:

```wx
trait Pointee<Size: PointerSize> { type Metadata: StackValue; }   // a generic trait
trait Pointee { type Metadata<Size: PointerSize>: StackValue; }   // a generic associated type
```

The size is a parameter of the metadata, not of the trait: every type has
one answer, generic over the size. So the second form fits, and it keeps
the model of `chatgpt-multiple-trait-implementations-per-target.md`: one
impl per trait and type constructor, selected by the target alone. A trait
reference never carries arguments, so bounds, `TraitClause`, supertraits,
impl headers and impl selection do not change; only a projection does.

With it, `pointer_metadata` returns a plain `TypeIndex` for every pointee,
and a pointee of unknown shape is the rigid projection
`<T as Pointee>::Metadata<M::Size>`, as `T::Item` is.

A generic trait is the more general feature (`Add<Rhs>`, conversions), and
the one that brings several impls per target. It is not needed here.

## Why Rust took six years

RFC 1598 was accepted in 2016, GATs stabilized in Rust 1.65 (November
2022). The time went into what wx does not have:

- Lifetime GATs (`type Item<'a> where Self: 'a`, the lending iterator): the
  required-bounds rule, implied bounds, region checking under binders.
- Higher-ranked bounds (`for<'a> I::Item<'a>: Debug`): normalizing under a
  binder in the old trait solver, partly still broken at stabilization.
- The old solver's eager normalization, which projections with arguments
  made worse; much of the delay was solver work (chalk, lazy
  normalization). wx's solver normalizes on request and memoizes by the
  interned type, so a projection with arguments is another key.
- `dyn` compatibility: a trait with a GAT cannot be a `dyn Trait`.
- Borrow-checker limits on lending iterators, after stabilization too.

wx has no lifetimes, no `for<..>` bounds and no `dyn`. What remains is type
parameters on an associated type, never the hard part of Rust's design.

## Stage 1: GATs in a compiler-answered trait

Enough for `Pointee`, whose impl is never written.

1. Parser and AST: parameters on an associated type declaration
   (`type Metadata<S: PointerSize>: StackValue;`), arguments on a
   projection in type position (`<T as Pointee>::Metadata<M::Size>`,
   `T::Metadata<u32>`).
2. `Type::TypeProjection { trait_index, assoc_type_index, base }` gains
   `args`, and every helper reads them: `flags_of` (a projection inherits
   its arguments' flags, `HAS_PARAM` among them), `substitute`,
   `match_pattern` (compares the arguments too), `is_abstract`, the
   formatter. A projection out of a concrete base with abstract arguments is
   not abstract: `<[u8] as Pointee>::Metadata<M::Size>` normalizes to
   `M::Size`.
3. Signatures: an associated type's own parameters are a scope of their
   own, and its declared bounds are read with the arguments substituted
   (`declarations_of`).
4. Well-formedness: a written projection proves its arguments meet their
   parameters' bounds (`M::Size: PointerSize`), recorded as an obligation as
   any type's arguments are.
5. `Pointee`'s structural answer (`TraitImplLookup::Builtin`), from
   `pointer_metadata`; its `Option` goes away.

A GAT in a written impl is refused until stage 2.

## Stage 2: GATs in written traits and impls

6. Conformance (`conformance.rs`): an impl's member has the declaration's
   parameters, by count and then bounds, and may require no more than the
   declaration, E2124's rule for functions, read in `contract_frame`.
7. Impl values: `Definition::Member` (keyed by `ImplMember`) is judged once
   with its own parameters abstract and instantiated per use, as a constant
   is per `eval::Instance`. Its verdict and cycle detection are unchanged:
   it is one definition whatever its arguments.
8. Defaults: a trait's default value for a GAT is inherited the same way.

## Edge cases

- **Equality bindings need a binder.** `T: Pointee where { Metadata<S> =
  (S, S) }` means "for every `S`", Rust's higher-ranked case. Refused at
  first. A binding with concrete arguments (`Metadata<u32> = u32`) is a
  plain `EqualityClause` and can come later. `Pointee` needs neither.
- **No quantified bounds written by users.** "`T::Metadata<S>` is `Copy`
  for every `S`" cannot be stated; only a GAT's declared bounds hold for
  every argument. Deliberate: it is what keeps the solver simple.
- **Recursion through the structural answer.** `[[T]]`'s metadata is
  `(S, <[T] as Pointee>::Metadata<S>)`, a projection inside the answer.
  Ordinary normalization depth; pin it with a test so nesting does not
  spend the budget unexpectedly.
- **Cache keys.** A request for a type with no parameter is keyed under the
  root scope; that must see the arguments' params, not only the base's.
  Falls out of `flags_of` if step 2 is right, and silently breaks
  memoization if not.
- **`HAS_PROJECTION` over a concrete base.** `Solver::normalize` skips a
  type without it, so a projection over a concrete base still carries it.
- **Bounds naming `Self` and the GAT's parameters**
  (`type Metadata<S>: Into<S>`). Substitution handles them; conformance
  instantiates both sides with the same placeholder for `S` before
  comparing, as for a function's own type parameters.

## Cost

Stage 1 is mostly mechanical: one variant change across the type helpers,
the parser, one structural answer. The risk is step 2, where a helper that
ignores `args` breaks matching or caching without an error. Stage 2 reuses
`contract_frame`, per-instance memoization and `Definition::Member`. The
edge cases that need design are the first two, both decided by refusing
them.
