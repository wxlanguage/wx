# TIR assumptions as their own arena (`AssumptionEnv`)

Status: steps 1–5 done (2026-10-31, branch
`slices-and-untyped-constants`); the rest planned. Supersedes the 2026-10-28 proposal in this file
(`ClauseSource` over frames). Companions: `tir-assumption-context-plan.md`
(how the current assumption context came to be), `tir-type-context.md`,
`tir-check-pass.md`, and "Representability clauses" in `slices-and-untyped-constants.md`,
which builds on this.

## Problem

A type environment frame (`GenericEnvIdx`) does two jobs:

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
  (`<Self as Array>::LEN` representable as `M::Size`).
- **The same parameters cannot assume different things in different
  checks.** `conformance.rs::contract_frame` copies the impl function's
  parameter names into a second frame only so the copies can carry the
  trait declaration's clauses, and every comparison substitutes the impl's
  types onto them.
- **A parameter's own clauses are read without a context.**
  `declarations_of`'s root case reads `param_bounds[env][param_index]`
  whatever scope asks, so a narrower scope cannot add to them.
- **The cache key is the frame.** `Normalization` is keyed by the
  `GenericEnvIdx`, so every generic function is its own key: `<T as Tr>::A`
  over an impl's `T` is cached once per method, even for methods that
  assume nothing more than the impl.
- **Boxing.** One `Box<[ParamBounds]>` per frame, and one `Box<[BoundId]>`
  per parameter inside it.

## History

`tir-assumption-context-plan.md` introduced `AssumptionContext` as a handle
over the frame chain, keeping parameter identity and the frame
representation. It shrank to a newtype and was removed: queries take a
`GenericEnvIdx` named `assumption_context`. Its constraints still apply:

- impl requirements are proved in the caller's context and never become its
  assumptions;
- an inner declaration's facts about an outer parameter stay local to it;
- cycle detection accounts for context when it changes a query's meaning.

The 2026-10-28 version of this note kept clauses per parameter and added a
`AssumptionEnv` of sources over frames (`Frame(GenericEnvIdx)` read live, plus
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

Naming: a declaration's parameters live in a *generic env* (`GenericEnv`,
formerly `TypeEnv`), what it assumes in an *assumption env*
(`AssumptionEnv`). Both are environments rather than frames: inherited from
the parent unless the item adds something. Assumption envs are created
lazily (only an item that writes a bound gets one); generic envs are not
quite yet (every impl gets one, empty or not, because `Self` inside the
impl finds its impl through it), which can be revisited separately.

Identity stays in `GenericEnvArena`, unchanged: envs only for items that
declare parameters, and impls. Assumptions get their own arena:

```rust
index_newtype!(AssumptionEnvIdx);

/// The clauses in force in a scope: its own, then its parent's.
#[derive(Clone, Copy)]
struct AssumptionEnv {
    parent: Option<AssumptionEnvIdx>,
    /// Any subject in scope: a parameter of any enclosing frame, or a
    /// projection out of one. One run of `Clause`s (every kind) in the
    /// `ClauseArena`, `Provisional` (memberships only) until the values
    /// are resolved, then `Final`.
    clauses: BoundClauses,
}

struct AssumptionEnvArena {
    /// Slot 0 is `AssumptionEnvIdx::ROOT`: no clauses, no parent.
    envs: Vec<AssumptionEnv>,
}
```

- **Two fields per signature, set once.** Each signature keeps its
  `GenericEnvIdx` (identity) and gains a `assumption_env: AssumptionEnvIdx`. Neither is
  derived from the other, so there is nothing to keep in sync:
  - an item that states clauses gets a new env whose parent is the
    enclosing item's env;
  - an item that states none reuses its enclosing item's env (the root at
    the top);
  - an item with clauses and no own parameters (a function bounding only
    `Self`) gets an env and no frame of its own;
  - a generic item with no bounds gets a frame and no env of its own.
- **A parent chain, not flattened copies.** Chains are at most two levels
  (an impl or trait, then a function), so a walk is short, and a parent's
  equalities are read live, so a child never holds a stale `Pending` copy.
  Flattening (rustc's interned list) can come later where a measurement
  shows it is better; it would need clause provenance (`source`, `origin`)
  moved beside the clause, so equal facts compare equal.
- **Flat storage.** `AssumptionEnv` is `Copy` in a `Vec`; clauses stay in the
  `ClauseArena`, each env's own contiguous; written bounds stay in the
  `BoundArena`. `param_bounds` and both boxes go away. A parameter's
  written bounds (`ParamBounds::declared_bounds`) are only read during
  construction (the equality pass takes them) and by tests, so they stay
  local to construction; tests read the clauses.
- **A clause's subject is any type in scope.** Inline bounds are the short
  form: `T: Iterator where { Item: Hash }` appends `T: Iterator` and
  `<T as Iterator>::Item: Hash` to the item's env, elaborated as today
  (supertraits with `Self` substituted, nested bounds as clauses on
  projections). A trait function's `Self` entry appends to the same env.
- **Associated type declarations keep their own clauses** (`type A: B`,
  about `<Self as Tr>::A`, on `AssocTypeSignature`): they describe a
  projection path, not a scope, and are read along it as today.
- **A trait's own clauses** (its supertraits, about `Self`) are its env's.
  `inherit_trait_clauses` reads `traits[i].assumption_env` instead of
  `param_bounds[env][0]`.
- **Construction order is unchanged.** Today a frame publishes every
  parameter's memberships, then resolves every value, then builds every
  equality (`signatures.rs`, the parameter-bounds pass). An env publishes
  its memberships as `BoundClauses::Provisional`, then the whole run as
  `Final`: one readiness per env, the order construction already follows.

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
- **Body checking.** `LexicalScope` gains `assumption_env` beside `env`: `env`
  resolves names, `assumption_env` is what queries assume
  (`members.rs`'s `assumption_context: scope.env` and the like).

### Caching

`Normalization` is keyed by `AssumptionEnvIdx`. A type with no parameter is
keyed under `ROOT`, as under `GenericEnvIdx::ROOT` today. Every item that
adds no clauses shares its parent's env and so its cache entries; no empty
frame or env is ever made, so nothing needs stripping from a key. A
normalization's answer depends only on the clauses and the definitions:
a type carries its own identity (`TypeParam { env, .. }`), so the frame is
not part of the key.

### Conformance

`contract_frame` becomes building one env:

```text
AssumptionEnv {
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

### Clauses on `Self`: written as a trait function's first parameter

There is no `where` list. A trait function that needs more of `Self` than
the trait does names `Self` as its first type parameter, bounded as any
parameter is; `Self` is the trait frame's parameter, hidden by default:

```wx
pub trait Array: Slice {
    const LEN: const_int;
    func as_slice<
        Self: Array where { const LEN: M::Size },
        M: Memory,
    >(self: M::&Self) -> M::&[Self::Value];
}
```

- It lowers into the function's env: clauses about `Self` (an outer
  parameter) beside the function's own, exactly what a `where` list would
  have produced. Nested binding blocks reach any path from `Self`, and
  `Self: Other` requires another trait (Rust's `where Self: Sized`).
- It is not an argument: the turbofish starts at the next parameter
  (`x.as_slice::<heap>()`), and conformance's own-parameter count skips it.
- Only first, in a trait's functions and a trait impl's (below), where
  `Self` is the target.
- A binding block's entry for a constant starts with `const`, required, so
  the parser tells it from a type's entry by the keyword alone:
  `const N: u32` is a representability clause (step 8), `const N = 10` a constant
  equality (rustc's `ConstEquate`), parsed and formatted but reported
  unsupported (E2114) until something needs it. `Size: Sub` and
  `Size = u32` stay a type's.
- Why nothing more general: per-method clauses are needed only where a
  method cannot move. An inherent impl's method that needs more of `T` goes
  in another block bounded so (std's `RawPtr` blocks); a trait impl's may
  require no more than its declaration (E2124); a method's own parameters
  take bounds where they are declared. What is left is a trait's function
  about `Self`.
- A `where` list on a trait or impl header would collide with the bound's
  bindings (`trait Pointer: StackValue where { .. }`); nothing needs one.

### An impl function assumes what it writes (refinement)

An impl function's clauses are exactly the ones it writes, `Self` included,
as for its own parameters today (rustc's `#[refine]`, RFC 3245): a call
through the trait proves the declaration's clauses, a direct call proves
the impl's, and conformance proves the impl's follow from the
declaration's (E2124). Nothing is inherited from the declaration.

```wx
trait Container {
    type Item;
    func show<Self: Container where { Item: Display }>(self: Self);
}
struct Wrap<T>(inner: T);
impl<T> Container for Wrap<T> {
    type Item = T;
    func show<Self: Container where { Item: Display }>(self: Self) {
        display(self.inner)          // T: Display, as written
    }
}
```

- Without the `Self` entry, the body cannot use `T: Display` (an unmet
  bound), and `show` is callable for every `T`. `impl<T: Display>` would be
  wrong: `Wrap<NoDisplay>` is still a `Container`, only `show` needs it.
- In an impl `Self` is the target, so a `Self` entry's clauses are about a
  type (`<Wrap<T> as Container>::Item: Display`). The env normalizes them
  where it is built (`T: Display`), the form lookup by root parameter finds
  (rustc normalizes its param env for the same reason).
- A clause that normalizes to a concrete type (`type Item = Bytes`:
  `Bytes: Display`) assumes nothing abstract; it is proved where the env is
  built and reported if it never holds. A concrete target rarely needs a
  `Self` entry: its facts are decided directly.
- Allowed in trait functions and trait impl functions. An inherent impl
  splits into blocks instead (std's `RawPtr`); allowing it there too is a
  later uniformity question, nothing needs it.

## Steps

Each leaves the suite green.

1. Done. **The arena, no behaviour change.** `AssumptionEnvArena`; a
   generic env's clauses contiguous (one push per pass instead of one per
   parameter); `param_bounds` and `ParamBounds` gone; written bounds local
   to construction; tests read clauses (`written_bounds`), and the
   formatter's test reads bounds by span.
2. Done. **Queries take `AssumptionEnvIdx`.** Every `assumption_context`,
   `Normalization`'s key (`AssumptionEnvIdx::ROOT` for a type with no
   parameter), `LexicalScope::assumption_env` beside `generic_env`; an
   env's `parent` and `reflexive` (a trait's `Self: Trait`, which walking
   assumption envs no longer reads off the generic env's owner); items
   without a bound share their parent's env, decided from syntax when the
   generic env is pushed. Kept: the map from a generic env to the
   assumption env its item states clauses in (`AssumptionEnvArena::of_frame`),
   used to build a scope and to prove an item's own clauses. A signature
   field replaces it once an item can have an assumption env without a
   generic env (step 6).
3. Done. **Scoped root lookup.** `declarations_of`/`declared_traits` take
   the context; for a parameter at the root they read each assumption env
   on the context's chain (the root env, which assumes nothing, skipped),
   and `projection_equality`/`declared_bound_member` pass theirs. Audit:
   every production caller already asked from the declaration's own scope
   or one inside it; only two tests asked about a parameter's bounds from
   the root context, and now ask from its declaration (a third test pins
   that outside it the bounds are not assumed).
4. Done. **Proving by env.** `satisfies_clauses` takes `Subjects`: `All`
   (every clause, its subject substituted over the frame's chain like its
   other types) or `Rooted` (the clauses over one root, rebased onto the
   use's type). Impl selection (`prove_requirements`) proves each env on
   the impl's assumption chain whole, and conformance's `check_own_bounds`
   the impl function's own env whole (none when it shares the impl's).
   `Rooted` stays where a failure is reported at one argument
   (`check_bound_requirements`, per parameter) and for an associated
   declaration's clauses, whose root is a projection. Within an env,
   memberships are now proved before equalities across all parameters, not
   per parameter; the order is still the arena's, so deterministic.
5. Done. **Conformance by env.** `contract_env` pushes one assumption
   env, parented on the impl's and bound to no generic env, holding the
   declaration's own clauses instantiated with `[target, the function's
   own parameters]`; when the declaration writes no bound (it shares its
   trait's env) the impl's env is used as it is.
   The function's signature is compared and its own env proved there,
   with its own parameters used directly: the second generic env, the
   `found` substitution and `own_params`' check-only case are gone.
6. **Clauses on `Self`.** 6a done: the parser reads `Self` as an ordinary
   type parameter name (as `self` among a function's parameters); where it
   may stand is the signature's to check, and until 6b a leading `Self` is
   reported unsupported and declares no parameter. A binding block's
   `const N: Ty` (`AssocBindingKind::ConstRepresentable`) and `const N = value`
   (`ConstEquals`) entries parse, format, and are reported unsupported
   (`AssocTypeBinding` is now `AssocBinding`). 6b/6c done: a leading
   `Self` in a trait's function lowers as clauses about the trait's
   `Self` into the function's env (`self_entry`; such a function
   gets a frame even with no parameter of its own, so it has an env); a
   `Self` anywhere else is E2131 (`MisplacedSelfBound`), in a trait impl's
   function still unsupported (6d). A use proves its item's own env whole,
   one `BoundRequirements::Frame { env, args }` per frame on the chain
   (`Subjects::All`), so clauses about an enclosing frame's parameter (the
   trait's `Self`) need nothing apart. `args` is a run of the
   `GenericArgArena` on `TypeContext`: a use's flat arguments, each with
   the span it is given at (the written argument, the value it was learned
   from, a receiver for `Self`, or the name; `BodyContext::use_args`), so
   a failure is reported where the argument its clause is rooted at is
   given (`UnsatisfiedClause::written`, `argument_span`). Body nodes hold
   their arguments in the same arena (`GenericArgs`), not in the
   interner's lists, which back interned types only. A frame whose
   arguments selection proved (`check_use_bounds`' `proven`) is skipped.
   Requirements apart from assumptions (done, no behaviour change): what
   an item states as written is its *requirements*, kept per frame beside
   the env it is read in (`AssumptionEnvArena::requirements`, rustc's
   `predicates_of` beside `param_env`), published with its env's clauses
   (`publish`). A use, impl selection and conformance prove requirements;
   lookup reads the env. The two runs are the same range until 6d
   normalizes an env. `own()` and `frame_clauses` are gone; `of_frame`
   stays as the item's env (rustc's `param_env(def_id)`).
   Obligations name the item's frame, not an env (done, no behaviour
   change): each reads `of_frame` when it is checked, so an item's env can
   be completed after construction (`complete_frame`).
   6d-1/6d-2 done (`env-normalization.md`): a trait impl function's `Self`
   entry lowers about the impl's target into its requirements only;
   `NormalizeSelfEntry`, first in its run, normalizes it into a completed
   env (an abstract subject assumed, the rest proved and dropped or
   reported); conformance normalizes the contract env and compares only
   what the impl assumes. 6d-3 (a call's failure at the receiver) open.
   6d: a trait impl function's `Self` entry, its clauses normalized into
   its env (a concrete subject proved there), proved to follow from the
   declaration's by conformance like its own parameters' clauses, and
   proved at direct calls by the same `Frame`.
7. **Associated-type bounds by substitution** (rustc's
   `check_type_bounds`; whenever convenient, nothing waits on it). A value
   for `<R as Tr>::A` is checked against `type A: ..` by proving the
   declaration's clauses with `Self` substituted by `R`, normalized in an
   env that holds `<R as Tr>::A == value`, so the normalization never
   selects the definition being checked. Covers all four sites
   (conformance, a binding in a bound, a memory's `Size`, a global's
   `Value`), which today re-root the clauses onto the value
   (`Subjects::Rooted` over a projection root, `rebase`). `rebase` and
   `Subjects` go: every proof is then of a whole env.
   One clause arena (done, no behaviour change): every kind is a variant
   of `bounds::Clause` in one `ClauseArena`, and a subject's clauses are
   one `ClauseRange`. What was two runs per subject (traits, equalities)
   was publication order, not kind: `BoundClauses` is `Provisional`
   (memberships, published before any value is resolved, so a sibling's
   value can name what they supply) or `Final` (the whole run, pushed
   again as one range: nested queries push other items' clauses between
   the two stages, so the second cannot extend the first). A reader of
   one kind filters (`ClauseArena::traits`, `equalities`); a pass over all
   kinds is one loop with a `match`, and a new kind is a new variant
   (rustc's `ClauseKind`). A clause is about 24 bytes; runs are a few
   clauses, so filtering costs nothing measurable.
8. **Representability clauses** (slices step 6, done; "fit clauses" until
   the rename): a `Clause::Representable` variant, published in the final
   stage (its type names siblings, `const LEN: Mem::Size`), the `const N: Ty`
   entry in a binding block, `satisfies_clauses`' arm, the body's lookup
   (`assumed_representable`, `tir/representable.rs`); E2133 when unmet.
   `Array::as_slice`/`as_slice_mut` have bodies in std.

## To audit

- **Requirement re-entry** (`solver.rs`, `match_impl_target_and_bounds`):
  brittle, not wrong. While an impl's requirements are judged, selecting
  the impl with its identity arguments in its own env is the judgement
  re-entering. Since envs are shared, a method that writes no bound checks
  its body in the impl's env, so both conditions hold for a selection in
  that body too; it is safe only because a judgement runs to completion
  inside one `requirements_verdict` call and no body check interleaves
  with it (the identity arguments alone already name the impl). The check
  should name the judgement explicitly, the open `SolverFrame::Requirements`
  for the impl, rather than compare contexts.
- ~~**`declarations_of` callers** (step 3)~~: done, see step 3.
- ~~**Per-argument checks read one root**~~ (step 6): answered by proving
  each frame's env whole, see 6b/6c. A clause a trait function states
  about `Self` (an outer parameter) was rooted at none of the function's
  own parameters, so no per-argument check read it.
- ~~**The conformance env's subjects**~~ (step 5): they are the impl
  function's own parameters, whose frame is on no chain the env knows
  about. Nothing reads a subject's frame from the context: assumptions are
  matched by subject, substitution and `is_abstract` read identity from
  the types. The E2124 suite passes unchanged.
- **Lookup cost.** Lookup by subject scans an env's clauses instead of
  indexing a parameter's run. The lists are small; measure on the std
  sweep before adding an index.

## Open

- **Interning envs** (rustc's flat list): equal assumptions sharing caches
  across unrelated items. Needs provenance out of the clause; measure first.
- **Body-local facts** (a fact one branch learns): an env per branch fits,
  but nothing produces one.
- **Clauses on other items** (structs, impls, traits): no syntax; a header
  `where` list collides with bound bindings. Added when something needs it.

## Non-goals

- **Owner-free type parameters** (`TypeParam { index }` as in rustc). Every
  type would mean something only relative to an item: `T` from two
  unrelated functions would be one `TypeIndex`, display would need the item,
  and substitution would change shape. Independent of this plan.
- **A syntactic subset check for E2124** (E0276). Comparing clause lists
  rejects impls Rust accepts (a bound that follows from an equality, from
  the impl block's own assumptions, or after normalization). Conformance
  proves clauses, and keeps doing so.
