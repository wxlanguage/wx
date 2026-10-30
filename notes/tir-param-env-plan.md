# TIR assumptions as a value (`ParamEnv`)

Status: proposal, 2026-10-28, branch `tir-refactor`. Nothing here is
implemented. Companions: `tir-assumption-context-plan.md` (how the current
assumption context came to be), `tir-type-context.md`, `tir-check-pass.md`.

## Problem

A type environment frame (`TypeEnvIdx`) does two jobs at once:

1. **Identity and scoping.** Which parameters exist, their names, their flat
   positions for substitution (`flat_slot`), how they print.
2. **Assumptions.** What those parameters satisfy: `param_bounds` is indexed by
   frame, and an assumption context *is* a frame, read by walking its chain
   (`ClauseTables::assumed_traits`, `assumptions_readiness`).

Because assumptions hang off parameter identity, the same parameters cannot
assume different things in different checks. Two places show it today:

- **`declarations_of` reads a parameter's own bounds from its own frame,
  whatever the query's context is** (the root-parameter case reads
  `param_bounds[env][index]` of the parameter's frame; the function takes no
  context at all). Asking about `TypeParam { env: impl_fn_env, 0 }` from any
  context yields the impl's own bounds.
- **Trait-impl conformance has to invent parameters.** To prove an impl
  function's own bounds under the trait's (rustc's E0276),
  `conformance.rs::contract_frame` pushes a second frame with the same names,
  parented on the impl's frame, whose parameters carry the trait declaration's
  clauses instantiated for them (`instantiate_clauses`). The impl function's
  own types are then substituted onto those new parameters before every
  comparison. The real requirement was only "the same parameters, other
  assumptions".

Facts that hold in part of a declaration (a fact one branch learns, a
check-only context like conformance's) have no other home.

## History

`tir-assumption-context-plan.md` introduced `AssumptionContext` as "a handle
over the existing `TypeEnvIdx` parent chain", deliberately keeping parameter
identities and the frame representation. It later shrank to a one-field
newtype and was removed: queries take a `TypeEnvIdx` named
`assumption_context`. That plan's constraints still apply (impl requirements
are proved in the caller's context and never become its assumptions; an inner
declaration's facts about an outer parameter stay local to it; cycle detection
accounts for context when it changes a query's meaning). This proposal is the
step that plan left for later: give the context content of its own, so it is
no longer the same thing as a frame.

## rustc, for comparison

- A parameter is `ty::ParamTy { index, name }`: a position in the item's flat
  generics, with no owner. It means something only relative to an item.
- Assumptions are a `ParamEnv`: an interned list of predicates passed to every
  query, independent of parameter identity.
- `compare_impl_method` builds a hybrid `ParamEnv` (the impl's predicates plus
  the trait method's, instantiated with `trait_to_impl_args`) and proves the
  impl method's predicates in it. It still substitutes the trait's predicates;
  it creates no new parameters.

wx does not need rustc's owner-free parameters to get the second half of this.
Dropping `env` from `TypeParam` is a separate question (see Non-goals).

## Proposal

Split job 2 out of the frame. An assumption context becomes its own record,
referred to by index:

```rust
index_newtype!(ParamEnvIdx);

/// The clauses in force somewhere: rustc's `ParamEnv`.
struct ParamEnv {
    sources: Box<[ClauseSource]>,
}

enum ClauseSource {
    /// Every parameter of this frame and the frames around it, read live
    /// from `param_bounds`, so a declaration still being built is read with
    /// its current readiness (memberships published, equalities `Pending`).
    Frame(TypeEnvIdx),
    /// A fixed run stated about one parameter, outside its declaration: the
    /// trait's clauses for an impl function's own parameter, a fact one
    /// branch learns.
    Clauses { subject: TypeIndex, clauses: BoundClauses },
}
```

- **Every declaration gets one**, `[Frame(its env)]`, built once. Today's
  behaviour is exactly that environment, so the switch is mechanical for
  every existing caller.
- **Queries take a `ParamEnvIdx`** where they take `assumption_context:
  TypeEnvIdx` today (49 signatures at the time of writing), and
  `solver::Normalization` keys its cache by it. A type with no parameter is
  still computed once, under the empty environment.
- **Frames keep job 1** (names, identity, substitution, display) and stop
  being what a query receives.
- **`declarations_of` takes the context.** Its root-parameter case reads the
  clauses the context holds for that parameter (a `Clauses` source naming
  it, else the `Frame` source covering its frame). Its associated-declaration
  case does not change: an associated type's declared bounds belong to the
  declaration, not to a scope.

Why `ClauseSource::Frame` rather than snapshotting each frame's ranges: a
declaration's clauses are filled in place during construction (memberships,
then equalities from `Pending` to `Final`), and construction-time queries must
see that readiness. A snapshot taken early would keep `Pending` forever.

### Conformance afterwards

`contract_frame` becomes building one `ParamEnv`:

```rust
[Frame(impl block's env)] ++ for each own parameter `i` of the impl function:
    Clauses { subject: impl fn's own `T_i`,
              clauses: instantiate_clauses(trait fn's clauses for `i`,
                                           [target, impl fn's own params]) }
```

The impl function's own parameters are used directly. What goes away:

- the second frame and its `param_bounds` slot;
- substituting the impl's types onto that frame before comparing
  (`compare_function`'s `found` substitution);
- `own_params`' need to recognize a check-only frame.

The trait side is still substituted, as in rustc.

## Steps

Each step leaves the suite green.

1. **Representation, no behaviour change.** Add `ParamEnvArena` and
   `ParamEnvIdx`; give every declaration `[Frame(env)]`, built when its frame
   is. `ClauseTables` reads a `ParamEnv` by walking its sources; for a single
   `Frame` source that is today's walk.
2. **Queries take `ParamEnvIdx`.** Change the 49 signatures and the
   normalization key. Body checking passes the declaration's environment.
   Still no behaviour change.
3. **`declarations_of` reads the context for a root parameter.** This is the
   one semantic change: audit every caller that relies on reading a
   parameter's bounds from a context that does not contain its frame (outside
   a parameter's own declaration, a query should not see its bounds anyway,
   but this needs checking, not assuming).
4. **Conformance uses a hybrid `ParamEnv`.** Delete `contract_frame`'s frame
   and the impl-side substitution; keep `instantiate_clauses`.

## Open questions

- **Interning.** Deduplicating identical environments lets declarations with
  the same assumptions share normalization cache entries (rustc interns for
  this reason). An append-only arena is simpler; measure before interning.
- **Cycle detection.** A normalization on the solver's stack
  (`SolverFrame::Projection`) holds its `Normalization`, which includes the
  context, and so does the cache. A hybrid environment gets its own index and
  must never alias a real declaration's. (Verdicts are keyed by definition,
  not context, and are unaffected.)
- **Readiness of a `Clauses` source.** A fixed run is `Final` by construction
  (conformance runs after every signature exists). If a body-local fact is
  ever added during construction, it needs the same `Pending` discipline as
  a frame.
- **Where body-local facts would come from.** wx has no type tests or
  refinements that would produce them today; this is a capability, not a
  requirement.

## Non-goals

- **Owner-free type parameters** (`TypeParam { index }` as in rustc). It would
  make every type meaningful only relative to an item: `T` from two unrelated
  functions would become one `TypeIndex`, display would need the item to name a
  parameter, and `flat_slot` substitution would change shape. It is independent
  of this proposal, which keeps `TypeParam { env, param_index }`.
- **A syntactic subset check for E0276.** Comparing clause lists instead of
  proving them rejects impls Rust accepts (a bound that follows from an
  equality, from the impl block's own assumptions, or only after
  normalization). Conformance proves clauses, and keeps doing so.
