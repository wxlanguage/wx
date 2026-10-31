# TIR assumptions as their own arena (`ParamEnv`)

Status: plan, 2026-10-31, branch `slices-and-untyped-constants`. Nothing here
is implemented. Supersedes the 2026-10-28 proposal in this file
(`ClauseSource` over frames). Companions: `tir-assumption-context-plan.md`
(how the current assumption context came to be), `tir-type-context.md`,
`tir-check-pass.md`, and "Fit clauses" in `slices-and-untyped-constants.md`,
which builds on this.

## Problem

A type environment frame (`TypeEnvIdx`) does two jobs:

1. **Identity.** Which parameters exist, their names, their flat positions
   for substitution (`parent_count + param_index`), how they print.
2. **Assumptions.** `param_bounds: Vec<Box<[ParamBounds]>>` is indexed by
   frame and then by parameter, and an assumption context *is* a frame,
   read by walking its chain (`ClauseTables::assumed_traits`,
   `assumptions_readiness`).

A clause is owned by the parameter it is about. Everything below follows
from that:

- **A clause can only be about its own frame's parameter.** A method cannot
  state a fact about its trait's `Self` or its impl's `T`: `Self`'s run is
  shared by every method. `Array::as_slice` needs exactly that
  (`<Self as Array>::LEN` fits `M::Size`).
- **The same parameters cannot assume different things in different
  checks.** `conformance.rs::contract_frame` copies the impl function's
  parameter names into a second frame only so the copies can carry the
  trait declaration's clauses, and every comparison substitutes the impl's
  types onto them.
- **A parameter's own clauses are read without a context.**
  `declarations_of`'s root case reads `param_bounds[env][param_index]`
  whatever scope asks, so a narrower scope cannot add to them.
- **The cache key is the frame.** `Normalization` is keyed by the
  `TypeEnvIdx`, so every generic function is its own key: `<T as Tr>::A`
  over an impl's `T` is cached once per method, even for methods that
  assume nothing more than the impl.
- **Boxing.** One `Box<[ParamBounds]>` per frame, and one `Box<[BoundId]>`
  per parameter inside it.

## History

`tir-assumption-context-plan.md` introduced `AssumptionContext` as a handle
over the frame chain, keeping parameter identity and the frame
representation. It shrank to a newtype and was removed: queries take a
`TypeEnvIdx` named `assumption_context`. Its constraints still apply:

- impl requirements are proved in the caller's context and never become its
  assumptions;
- an inner declaration's facts about an outer parameter stay local to it;
- cycle detection accounts for context when it changes a query's meaning.

The 2026-10-28 version of this note kept clauses per parameter and added a
`ParamEnv` of sources over frames (`Frame(TypeEnvIdx)` read live, plus
`Clauses { subject, .. }` runs). It fixed where a context points, not how
clauses are owned. Attaching clause lists to frames instead was also
considered and rejected: an item with clauses but no parameters would need
an empty frame, and every empty frame would be another cache key to strip.

## rustc, for comparison

- A parameter is `ParamTy { index, name }`, a position in an item's flat
  generics (`generics_of`, with `parent` and `parent_count`).
- Written predicates are `predicates_of(def_id)`: `GenericPredicates {
  parent: Option<DefId>, predicates }`, the item's own, chained to its
  parent's and instantiated by walking the chain.
- What a query assumes is a `ParamEnv`: `param_env(def_id)` collects the
  chain, elaborates it (supertraits) and interns one flat `&List<Clause>`;
  the solver scans it linearly, and equal lists share caches.
- `compare_impl_method` builds a hybrid `ParamEnv` (the impl's predicates
  plus the trait method's, instantiated with `trait_to_impl_args`) and
  proves the impl method's predicates in it. It creates no parameters.

Identity and assumptions are separate tables in rustc, both keyed by the
item. wx keeps `TypeParam { env, param_index }` (owner-ful parameters, see
Non-goals) and separates the same two things.

## Design

Identity stays in `TypeEnvArena`, unchanged: frames only for items that
declare parameters. Assumptions get their own arena:

```rust
index_newtype!(ParamEnvIdx);

/// The clauses in force in a scope: its own, then its parent's.
#[derive(Clone, Copy)]
struct ParamEnv {
    parent: Option<ParamEnvIdx>,
    /// Any subject in scope: a parameter of any enclosing frame, or a
    /// projection out of one.
    traits: ClauseRange<TraitClause>,
    equalities: Equalities,
    // with fit clauses: fits: ClauseRange<FitClause>,
}

struct ParamEnvArena {
    /// Slot 0 is `ParamEnvIdx::EMPTY`: no clauses, no parent.
    envs: Vec<ParamEnv>,
}
```

- **Two fields per signature, set once.** Each signature keeps its
  `TypeEnvIdx` (identity) and gains a `param_env: ParamEnvIdx`. Neither is
  derived from the other, so there is nothing to keep in sync:
  - an item that states clauses gets a new env whose parent is the
    enclosing item's env;
  - an item that states none reuses its enclosing item's env (`EMPTY` at
    the top);
  - an item with clauses and no parameters (a `where` list on a non-generic
    method) gets an env and no frame;
  - a generic item with no bounds gets a frame and no env of its own.
- **A parent chain, not flattened copies.** Chains are at most two levels
  (an impl or trait, then a function), so a walk is short, and a parent's
  equalities are read live, so a child never holds a stale `Pending` copy.
  Flattening (rustc's interned list) can come later where a measurement
  shows it is better; it would need clause provenance (`source`, `origin`)
  moved beside the clause, so equal facts compare equal.
- **Flat storage.** `ParamEnv` is `Copy` in a `Vec`; clauses stay in the
  `ClauseArena`, each env's own contiguous; written bounds stay in the
  `BoundArena`. `param_bounds` and both boxes go away. A parameter's
  written bounds (`ParamBounds::declared_bounds`) are only read during
  construction (the equality pass takes them) and by tests, so they stay
  local to construction; tests read the clauses.
- **A clause's subject is any type in scope.** Inline bounds are the short
  form: `T: Iterator where { Item: Hash }` appends `T: Iterator` and
  `<T as Iterator>::Item: Hash` to the item's env, elaborated as today
  (supertraits with `Self` substituted, nested bounds as clauses on
  projections). A `where { .. }` list appends to the same env.
- **Associated type declarations keep their own clauses** (`type A: B`,
  about `<Self as Tr>::A`, on `AssocTypeSignature`): they describe a
  projection path, not a scope, and are read along it as today.
- **A trait's own clauses** (its supertraits, about `Self`) are its env's.
  `inherit_trait_clauses` reads `traits[i].param_env` instead of
  `param_bounds[env][0]`.
- **Construction order is unchanged.** Today a frame publishes every
  parameter's memberships, then resolves every value, then builds every
  equality (`signatures.rs`, the parameter-bounds pass). An env publishes
  its trait range with `Equalities::Pending`, then sets
  `Equalities::Final`: one readiness per env, the order construction
  already follows.

### Reading

- **What a scope assumes** (`assumed_traits(env)`,
  `assumed_subjects`, `assumptions_readiness(env)`): walk the env's parent
  chain instead of the frame chain. A trait's reflexive `Self: Trait` comes
  from the frame owner of the subject, which is identity, and is unchanged.
- **What states something about a receiver** (`declarations_of(env,
  receiver)`): the root case yields each env on the chain as a source with
  `context: None`. The filter every reader already applies
  (`DeclarationSource::names`: the clause's subject is the receiver) picks
  the clauses about it. A clause written on `as_slice` about `Self` is then
  seen inside `as_slice` and nowhere else. The associated-declaration case
  is unchanged.
- **Proving a use** (`satisfies_clauses`, `prove_requirements`): each env
  on the callee's chain is proved with the use's flat arguments,
  substituted through the callee's frame (the signature has both). The
  per-parameter `(param, arg)` pairing goes away; the substitution covers
  every parameter. `reads_failed` works on an env's clauses as on a run.
- **Body checking.** `LexicalScope` gains `param_env` beside `env`: `env`
  resolves names, `param_env` is what queries assume
  (`members.rs`'s `assumption_context: scope.env` and the like).

### Caching

`Normalization` is keyed by `ParamEnvIdx`. A type with no parameter is
keyed under `EMPTY`, as under `TypeEnvIdx::ROOT` today. Every item that
adds no clauses shares its parent's env and so its cache entries; no empty
frame or env is ever made, so nothing needs stripping from a key. A
normalization's answer depends only on the clauses and the definitions:
a type carries its own identity (`TypeParam { env, .. }`), so the frame is
not part of the key.

### Conformance

`contract_frame` becomes building one env:

```text
ParamEnv {
    parent: impl block's env,
    traits/equalities: the trait function's own clauses, instantiated with
                       [target, impl function's own parameters],
}
```

The impl function's signature and own clauses are checked in that env, with
its own parameters used directly. Gone: the second frame and its names, its
`param_bounds` slot, the `found` substitution in `compare_function`, and
`own_params`' need to recognize a check-only frame. The trait side is still
instantiated (`instantiate_clauses`), as in rustc. The env's index is new,
so its cache entries never alias a real declaration's.

### `where` lists

The written form of a clause, one entry per stored clause kind, qualified
paths only:

```wx
func as_slice<M: Memory>(self: M::&Self) -> M::&[Self::Value]
where { const <Self as Array>::LEN: M::Size } { .. }

func f<T: Iterator>(it: T)
where { <T as Iterator>::Item: Hash, <T as Iterator>::Item = u8 } { .. }
```

- `<T as Tr>::A: Bound` is a `TraitClause`; `<T as Tr>::A = X` is an
  `EqualityClause`, its left side always a projection, which keeps the
  orientation the solver relies on (a general `A = B` is refused, as Rust
  refuses equality in `where` clauses); `const <T as Tr>::C: Ty` is a
  `FitClause` (with fit clauses, see the slices note).
- No shorthand (`Self::LEN`, `T::Item`) yet; it would resolve as `T::Item`
  does, ambiguity included (E2059).
- A subject may be rooted at any enclosing frame's parameter; a qualified
  path requires its trait to hold already (`CheckTraitMembership`), and
  adds no bound.

## Steps

Each leaves the suite green.

1. **The arena, no behaviour change.** Add `ParamEnvArena`. Build one env
   per frame that has parameters' clauses today, its trait and equality
   ranges contiguous (one push per pass instead of one per parameter), and
   store `param_env` on each signature. Readers still take a `TypeEnvIdx`
   and map it to the frame's env. `param_bounds` goes away; written bounds
   stay local to construction; tests read clauses.
2. **Queries take `ParamEnvIdx`.** The `assumption_context: TypeEnvIdx`
   signatures (56 today: solver 23, obligations 10, members 9, layout 6,
   bounds and satisfaction 3 each, signatures 2), `Normalization`'s key,
   and `LexicalScope::param_env`. Items without clauses share their
   parent's env. Remove step 1's mapping.
3. **Scoped root lookup.** `declarations_of`/`declared_traits` take the
   env (16 call sites). The one semantic change; audit every caller (see
   below).
4. **Proving by env.** `prove_requirements`/`satisfies_clauses` prove each
   env on a chain with substituted arguments.
5. **Conformance by env.** Replace `contract_frame` with the hybrid env;
   delete the impl-side substitution.
6. **`where { .. }`.** Parser and AST (an optional list after a function's
   signature; other items later), lowering into the item's env (an item
   with a list gets an env even without parameters), wx-fmt.
7. **Fit clauses** (slices step 6): a third range in `ParamEnv`, the
   `const` entry in `where`, `satisfies_clauses`' arm, the body's lookup in
   `untyped_value`. Then `Array::as_slice`/`as_slice_mut` get bodies in std.

## To audit

- **Requirement re-entry** (`solver.rs`, `match_impl_target_and_bounds`):
  `assumption_context == impl_env` with identity arguments marks the impl's
  own judgement. Once envs are shared, an impl's env and a caller's (a
  method of the impl that adds no clauses) can be the same index. The check
  should name the judgement explicitly (its solver frame) rather than
  compare contexts.
- **`declarations_of` callers** (step 3) that read a parameter's bounds
  from a context outside its declaration. Outside its declaration a query
  should not see them, but that needs checking.
- **The conformance env's subjects** belong to a frame that is on no chain
  the env knows about. Substitution and `is_abstract` read identity from
  the types, so this should hold; check that nothing looks a subject's
  frame up from the context.
- **Lookup cost.** Lookup by subject scans an env's clauses instead of
  indexing a parameter's run. The lists are small; measure on the std
  sweep before adding an index.

## Open

- **Interning envs** (rustc's flat list): equal assumptions sharing caches
  across unrelated items. Needs provenance out of the clause; measure first.
- **Body-local facts** (a fact one branch learns): an env per branch fits,
  but nothing produces one.
- **`where` on other items** (structs, impls, traits): the same lowering;
  added when something needs it.

## Non-goals

- **Owner-free type parameters** (`TypeParam { index }` as in rustc). Every
  type would mean something only relative to an item: `T` from two
  unrelated functions would be one `TypeIndex`, display would need the item,
  and substitution would change shape. Independent of this plan.
- **A syntactic subset check for E2124** (E0276). Comparing clause lists
  rejects impls Rust accepts (a bound that follows from an equality, from
  the impl block's own assumptions, or after normalization). Conformance
  proves clauses, and keeps doing so.
