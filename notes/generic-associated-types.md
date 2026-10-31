# Generic associated types

Status as of 2026-10-31: **deferred**, nothing implemented. They were
motivated by a pointee-side `Pointee` trait; pointer metadata is named on
the pointer instead (`<M::&T as Pointer>::Metadata`, "The `Pointer` trait"
in `slices-and-untyped-constants.md`), which needs no GAT. This note keeps
the design for when something else needs one: a trait whose impls are
written by users with a member that takes parameters (a collection family's
`type Of<T>`, say). Nothing planned does yet.

When to revisit: after generic constants (`const N<S: PointerSize>`), which
need the same pieces (a frame for a member's own parameters, flat
arguments `[Self, own…]`, per-instance values) and make GATs cheap. A GAT
would also let `<M::&T as Pointer>::Metadata` be redefined inside the
compiler as `<T as Pointee>::Metadata<M::Size>`, which makes the rigid
metadata of two memories with the same `Size` one type (the one cost of
the pointer-side form); the `Pointer` API would not change.

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

What carries over from rustc:

- A projection is `AliasTy { def_id, args }`: the trait's arguments
  (`Self` first), then the GAT's own. The GAT's `Generics` has the trait as
  parent, with `parent_count`, as wx's `TypeEnv` frames do.
- An impl's value is instantiated by rebasing: the trait's prefix of `args`
  is replaced by the impl's (`GenericArgs::rebase_onto`), so the value is
  read with `impl_args ++ own_args`.
- Conformance (`compare_impl_ty`): parameter count and kinds; the impl's
  bounds implied by the declaration's (E0276, wx's E2124); the value meets
  the declared bounds for every argument, with the parameters as
  placeholders (`check_type_bounds`).
- No `for<T>` bounds over types in stable Rust (`non_lifetime_binders` is
  unstable): only a GAT's declared bounds hold for every argument.

## Decisions

1. **Representation: flat arguments.** `TypeProjection { assoc_type_index,
   args }` with `args = [base, own…]`, as `Type::Const`'s `[Self]` and
   `Function`'s `[Self, own…]`, and rustc's `AliasTy`. Measured: `Type` is
   16 bytes today; an `args: TypeList` beside `base` makes it 24 (20 without
   `trait_index`), for every interned type and hash key; the flat form
   keeps 16. Costs: `base` is `list(args)[0]`, a projection without
   arguments stores a one-element list (deduplicated by content), and the
   trait comes from the declaration (`AssocTypeDef` gains its trait).
   `Type::Const` takes the same layout for generic constants.
2. **A frame per GAT** (`TypeEnvOwner::AssocType`). On the trait's
   declaration its parent is the trait's `Self` frame, so its flat slots
   are `[Self, own…]`, exactly the projection's `args`: reading the declared
   bounds along a projection path is `Substitution { env: gat_env, args }`,
   and `SelfSubstitution` (`bounds.rs`) becomes its special case. On an
   impl's member its parent is the impl's frame, slots `[impl params…,
   own…]`: `reduce_projection` substitutes `impl_args ++ args[1..]`,
   rustc's rebase with no new mechanism.
3. **Only the base selects.** Impl selection reads `base` alone, keeping
   one impl per trait and constructor. Arguments are not normalized before
   selection: they are substituted into the value and the result
   normalized, or, for a rigid projection, normalized as children under a
   `Deep` request only. The cache key needs nothing new
   (`Normalization::new` keys on `has_param`, so `flags_of` must collect
   from all of `args`).
4. **Not injective.** No type argument is learned through a projection
   (`learn` already ignores them): `func f<T, S>(m: T::Metadata<S>)` needs
   explicit arguments, as in Rust and GHC (without its injectivity
   annotations). `match_pattern`'s projection arm compares every argument.
   `_` in a GAT's arguments is refused. `learn` does learn through
   `Type::Const`'s `type_args`; harmless while no rigid constant can equal
   another, but the same question, to decide once for both.
5. **Equality bindings refused.** `Metadata<S> = (S, S)` needs a binder,
   which Rust does not have for types either. `Metadata<u32> = u32` is
   harder than it looks: `projection_equality` would match arguments modulo
   normalization, but clauses are published before equality values are
   resolved, and normalizing an argument may need those equalities.
6. **Parameter bounds only.** No `where` on the GAT itself (where Rust's
   required-bounds rules live); type parameters only. A GAT written
   without its arguments is an error, never defaulted (rustc's E0107).
7. **Well-formedness.** A written projection records its membership check
   and the GAT's parameter bounds instantiated with `args`, as a struct's
   arguments are checked. The hook is `report_assoc_type_args`
   (`signatures.rs`), which already lowers and reports arguments written on
   an associated type. A projection made by substitution is not checked
   again (the caller proved the bounds), the open point `M::&[u8; T::LEN]`
   has too.
8. **Judgement and cycles unchanged.** A member is judged once, in its own
   frame, its parameters abstract. Reaching it again with other arguments
   through definitions alone is still a real loop: with no specialization a
   definition cannot recurse on a smaller argument and stop. Legitimate
   recursion goes through a rigid argument (`<P as Nat>::Add<N>`), abstract
   during the judgement and unfolded per use outside its frame. Verdicts
   stay per definition. Recursion with growing arguments never repeats a
   `Normalization` and is stopped by the budget (type-level computation
   with GATs is Turing-complete, as in rustc).

## Efficiency

- The type's size: decision 1.
- Not GAT-specific, but GATs make it easier to reach: nested
  normalizations do not read the cache (the TODO above `normalize`), so a
  value like `(<P as Nat>::D<N>, <P as Nat>::D<N>)` normalizes identical
  children separately, exponential in depth although the interned result
  is small. Normalizing identical children of one node once is a cheap
  partial fix.

## Stages, if revived

1. Parser and AST: parameters on an associated type declaration;
   arguments on a projection already parse (`report_assoc_type_args`).
2. The flat `TypeProjection` across every helper that builds or reads one
   (`flags_of`, `substitute`, `match_pattern`, `meet`, `rebase`, the
   formatter), the GAT frame, declared bounds read through it,
   well-formedness. The risk: a helper that ignores `args` breaks caching
   or matching without an error.
3. Conformance in `contract_env`: count, bounds no stronger than the
   declaration's, the value meeting the declared bounds for every argument;
   impl values and trait defaults instantiated by rebasing.
