# Normalizing an assumption env

Status: implemented (6d-1, 6d-2); 6d-3 open. Step 6d of `tir-assumption-env-plan.md`
(a trait impl function's `Self` entry) needs it; type alias bounds
(`type X: Debug = u32`) would go through the same mechanism later.

## The problem

```wx
trait Show { func show(self: Self); }
trait Container {
    type Item;
    func show<Self: Container where { Item: Show }>(self: Self);
}
struct Wrap<T>(inner: T);
impl<T> Container for Wrap<T> {
    type Item = T;
    func show<Self: Container where { Item: Show }>(self: Self) {
        self.inner.show()        // asks: T: Show
    }
}
```

Lowering resolves names but keeps projections as written:

- `Self` in an impl is a name: lowering resolves it to the target
  (`resolve_impl_self`), as a type alias is resolved to its target. Neither
  exists as a type.
- `Self::Item` is a projection: it is stored as `<Wrap<T> as Container>::Item`,
  even inside the impl that writes `type Item = T`. Its value is a semantic
  fact, read by the solver.

So the impl function's entry lowers to two clauses:

```
Wrap<T>: Container
<Wrap<T> as Container>::Item: Show
```

Lookup reads assumptions by the parameter a type starts from (only an
abstract type takes assumptions). The body asks `T: Show`; neither clause
starts at a parameter, so it is never found. In the trait's own declaration
(6c) this never comes up, because `Self` is the trait's parameter there and
`<Self as Container>::Item: Show` is rooted at it.

Turning the second clause into `T: Show` means normalizing it, and lowering
does not normalize. It has to happen after every signature exists, in the
solver.

## What rustc does

- Lowering: `Self` in an impl lowers to the self type, and `Self::Item` to the
  projection `<Wrap<T> as Container>::Item`, as in wx.
- The `param_env` query (`rustc_ty_utils/src/ty.rs`) collects the item's
  where-clauses into an unnormalized env and ends with
  `traits::normalize_param_env_or_error`, which normalizes them "in case they
  contain any associated type projections". The env a body is checked in
  holds `T: Display`, not the projection.
- It normalizes the env inside an elaborated, unnormalized copy of itself
  (the source calls this a "HACK: we are trying to normalize the param-env
  inside *itself*"), so one clause may use the item's other clauses, and the
  outlives clauses get a second round.
- A where-clause about a type with parameters (`Wrap<T>: Show`) stays an
  assumption: trait selection matches param-env clauses against any type.
  A clause with no parameter at all (`u32: Debug`) that does not hold is an
  error where it is written, unless `trivial_bounds` is enabled.

## The design (decided 2026-10-31)

Only a trait impl function's `Self` entry produces clauses about a type, so
this is the mechanism for it; alias bounds would reuse it.

### Envs never change; the item's env is published

```
impl env              the impl's clauses
  └ signature env     the function's own parameters' clauses (the impl's
                      env when it writes none), final at construction
      └ completed env the Self entry's clauses, normalized
```

- **Every env is complete when it is made and never changes.** The entry's
  clauses are in no env during construction, only in the function's
  requirements (`AssumptionEnvArena::requirements`, the whole written run).
- **The item's env is what is published.** `of_frame(frame)` is the
  signature env until `NormalizeSelfEntry` makes the completed env and
  points the frame at it (`complete_frame`), once.
- **Lowering reads the signature env**, which is final, so a shorthand path
  in the function's own signature that needs the entry's meaning
  (`T::ShowMember` through `Item: Show`) is not found, and is written
  qualified; rustc resolves shorthand from written bounds too
  (`type_param_predicates`), not from the normalized `param_env`.
- **Obligations name the item's frame, not an env** (`TypeObligation`'s
  `frame`), and read `of_frame` when they are checked. `NormalizeSelfEntry`
  is first in the function's run, so the signature's checks (a
  `Shown<Self::Item>` that needs `Item: Show`, a deferred
  `CheckProjectionMember`) see the completed env. A reader outside the
  function that comes first (the impl's conformance) reads the signature
  env: final, with fewer facts.
- **Calls and conformance prove the requirements as written**; the
  substitution and the proof's normalization give `X: Show` at a call.

Rejected on the way: a flag on the env making it read as its parent until
normalized. One index meant two things over time, and every reader (the
chain walk, the declaration walk, the cache key) had to redirect.

### What a clause becomes

Each clause is normalized in the full env's parent:

- **An abstract subject** (`T`, `<T as Iterator>::Item`) is kept.
- **No parameter** (`type Item = Bytes`: `Bytes: Show`) is proved there:
  dropped if it holds, reported at its written bound if not (rustc's
  `check_false_global_bounds`).
- **A parameter, not abstract** (`Wrap2<T>: Show`): unsupported (E2114)
  for now. Later: replaced by the requirements of the one impl that
  matches, so every kept clause is abstract.
- An equality is kept when its projection is still abstract, compared when
  neither side has a parameter (E2112 at the equality), and otherwise an
  error (E2132, `UnassumableEquality`): `Item = u8` where `Item` is `T`
  would make a parameter equal a type, which no clause can state and
  normalization never reads (it rewrites projections only). rustc has no
  `T == u8` where-clauses either. Unlike `Wrap2<T>: Show`, this is not
  planned, so it is an error rather than unsupported.

### Which env a clause is normalized in

**The full env's parent** (the signature env, then the impl's). The entry's
own clauses do not take part in normalizing each other.

- It gives the same result as rustc's self-copy for every clause wx can
  produce about a type. Those come from names (`Self` in an impl, an alias
  later), and their projections reduce through definitions
  (`<Wrap<T> as Container>::Item` through the impl's `type Item = T`), not
  through the item's own clauses.
- The case rustc's self-copy exists for (`I: Iterator<Item = U>` with
  `<I as Iterator>::Item: Debug`) is about a parameter in wx, and wx resolves
  equalities where lookup reads them (`projection_equality`), so it needs no
  env normalization.
- A parent never reads its child, so normalizing cannot loop.

### Rejected

- **One env, `Pending` until normalized:** every unqualified `T::Name` in the
  function's signature would fail, the impl's own `T` included.
- **The solver finishes the env on first read:** the solver cannot publish
  (its queries do not publish into the signature tables), so every reader would need a prepare step or a
  solver-side table of normalized runs.
- **Normalizing during construction:** construction neither checks nor
  normalizes, and nothing bounds which signatures a normalization reaches.

## Conformance

The contract env (`contract_env`) holds what the declaration's own clauses
mean with `Self` as the target: instantiated, then normalized in the impl's
env (`normalize_clauses`), keeping what is about an abstract type. E2124
(`check_own_bounds`) compares only what the impl function assumes, its
requirements normalized in the impl's env the same way: a clause about a
type that is not abstract holds or not of its own and is reported where it
is written, never as stricter. Both read where the function is written, not
under the contract's assumptions, or a contract equality would rewrite the
clause being compared (`Item == u8` reading `Item == u16` as `u8 == u16`).
Whether a function has clauses of its own is whether it has a frame of its
own (`own_requirements`), not whether it has parameters.

## Open questions

- **Diagnostics at calls (6d-3).** A failure proved through the written run is
  rooted at the target, which is no argument, so it is reported at the
  method. Map it by `origin` to the normalized clause, rooted at the impl's
  parameter, to report it at the receiver.

## Already decided

- The written run is kept for good, as the item's requirements, per frame
  (`AssumptionEnvArena::requirements`), not on the env: an env is a scope
  (shared by items that write no bound, or an item's only, like the
  contract env), while requirements belong to an item. Uses prove
  requirements and lookup reads the env, so normalizing replaces only the
  env's clauses. Requirements could live on the signatures instead, but
  every reader names the item by its frame, and an impl's signature does
  not exist yet while its clauses are built.

- No simplification during lowering: aliases and `Self` are names resolved
  there, projections are kept as written.
- No separate pass after signatures, and no env rewritten by a phase that
  must run at the right moment.
- A trait impl function's `Self` entry lowers about the impl's target
  (`self_entry` in `signatures.rs`); its clauses are only usable once this
  exists.
