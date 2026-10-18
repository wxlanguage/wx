# TIR check pass

Status as of 2026-10-14, branch `tir-refactor`. Companion to
`tir-type-context.md`. Migration steps 1-4 and the follow-ups "Construction does
not normalize", "The solver is scoped by a view" and "Definitions own their
loops" are implemented, and the test suite has been rewritten to the new
contract (556 tests, all passing).

## Problem

Signature construction today does "check if possible, else defer":

- A bound check (`validate_or_defer`), a memory-tag check, a qualified trait
  membership and a normalization each try to finish immediately. If a fact they
  need is not `Ready` yet they return `Pending` and queue an `Obligation` on the
  declaration being built.
- A queued obligation is retried at three moments (facts publication,
  construction completion, a reader forcing the signature), and on completion it
  **rewrites the stored signature** (`TypeRepair`: `ReplaceType`,
  `RejectArgument`, `InvalidateTraitDependents`) so a failed argument becomes
  `ERROR` and nobody re-derives the same failure.

That couples three things: when a check may run, what state a signature is in
(`AwaitingChecks`, `Checking`), and a repair that must find every stored copy of
a type (`repair_signature`, `repair_source_bound`,
`repair_signature_assumptions`, ~300 lines). `Pending` exists only because
checks run while sibling facts are still being built.

## Design (D1, rustc-like)

rustc keeps construction and checking apart: `fn_sig`/`type_of` lower written
syntax without checking bounds, `check_well_formed` runs afterwards, and
normalization happens at the use site. Query results are never patched. wx
adopts the same split.

1. **Construction lowers, it does not check.** Lowering failures (unresolved
   path, wrong arity, missing associated type, cycle) still substitute
   `TypeIndex::ERROR` in place, at the failing site, exactly as now. Constraint
   failures (a bound is not satisfied) are only *recorded* as obligations and
   never change the type.
2. **A check pass runs after every signature is constructed**, before any body.
   All bound facts are `Ready` then, so a check returning `Pending` is an
   internal-invariant failure (a `debug_assert` in `run_checks`), not an expected
   state.
3. **Signatures are immutable after construction.** No repair. A stored type may
   contain an unnormalized projection; whoever reads it normalizes under its own
   assumption context. Construction never normalizes (see "Construction does
   not normalize").
4. **Queries are pure; sites own reports.** A semantic query (`normalize_*`,
   `find_trait_impl_query`) returns a verdict and never emits a
   diagnostic. The construct that introduced a requirement reports it, once: a
   written site that checks eagerly reports at that moment, and one that cannot
   decide records an obligation and the check pass reports it. A failure that is
   merely *derived* from an already-reported one (normalizing a projection whose
   bound failed at its site) returns `Failed` and stays silent, and consumers
   absorb `Failed` locally as `ERROR`. Duplicate reports are therefore ruled out
   by who is allowed to emit, not suppressed afterwards: no set of reported
   goals. The one piece of recorded state is a verdict on a *definition's* value
   (`AssocValue`, see "Definitions own their loops"), read like a failed lowering.

### Where the duplicates came from

`<Need<T::B> as Project>::Output` was checked by two independent mechanisms: the
qualified path recorded a `CheckTraitMembership` (site-owned), and
`reduce_projection` also reported "does not implement" from inside normalization.
Removing the emission from normalization alone fixed both double-report tests;
no dedup structure was needed.

### Construction does not normalize

Lowering used to end every written type with `normalize_type`, which made
construction depend on impl headers, associated-type values and `Ready` bound
facts. That eager normalization was the reason `Pending`, provisional facts and
demand-driven `ensure_*` calls existed inside the normalizer. It is gone:

- `resolve_type` (and the memory-size and global-value sites) store the type as
  written, projections unreduced. A reader normalizes under its own assumptions.
- A qualified path `<X as Trait>::Name` finds the trait's declared member and
  records `CheckTraitMembership`. It does not look for an impl.
- An unqualified `Type::Name` (`select_associated_type`, `members.rs`) reads
  declarations only: the receiver's declared bounds, the traits with an impl for
  the receiver's type constructor (`ImplDispatch`), and the assumptions in scope,
  each shown to apply by `check_assumed_trait`. Coherence (one impl per trait per
  constructor) makes the dispatch index name the provider exactly, so no header is
  read and no impl is matched. The membership is recorded like a qualified path's.
  The receiver may be rewritten by assumed equalities (`Mode::Assumptions`), never
  by selecting an impl. A member of a projection whose declared bounds do not
  name it (`Wrapper::Item::Value`) is the one case construction cannot decide, so
  it records `CheckProjectionMember` and lowers to `ERROR`. The check pass
  resolves what the projection's value is and which traits could supply the
  name, as rustc does to build its suggestion, and reports E2104 "ambiguous
  associated type" with one note per candidate:
  `qualify the trait: `<<Wrapper as Container>::Item as Element>::Value``. It is
  an error even when resolvable, because selecting through an impl unqualified is
  ambiguous by design. A projection with no value stays silent (the impl or the
  failed requirement is reported where it belongs) unless no trait declares the
  name at all; a name no candidate trait declares is the plain "no associated
  type". The suggested spelling parses (the parser splits `<<` at the start of a
  qualified type, as it splits `>>`), and a test feeds it back in.
- `Obligation::CheckWellFormed` is recorded for every written type and
  normalizes it once in the check pass, so a cycle or exhausted budget inside a
  type nobody reads is still found. The result is discarded; nothing is stored.

The normalizer then only reads finished tables. `assoc_type_value`,
`assoc_type_default` and the impl-header match are plain reads; an unfilled slot
is `Pending`, never something to construct. `prepare_declarations_of` (which
forces a declaration's bounds) is called by lowering's member selection only. A
`debug_assert` in `normalize_uncached` enforces that impl-based normalization
never runs while a signature is being built (`Mode::Assumptions` may).

### Queries return failures; sites report them

The solver (normalization and impl selection are one recursive engine) has one
flat error, `Unsolved`: `Pending` (a fact is not final yet), `Failed` (no answer,
and the construct that wrote the input already owns the report, so consumers
recover silently), `Overflow` (budget), and `Cycle(Box<Cycle>)` (the repeated
projection and the projections in flight, outermost first). Nothing in the engine
emits. The cycle's steps are copied into the error because the in-flight stack
has unwound by the time a site reports; the allocation happens only when a cycle
is detected. `report_unsolved(result, site)` (in `satisfaction.rs`, next to the
sites) is the one place that renders `Overflow` and `Cycle`, called by the
construct that owns the requirement: `check_obligation` for the three
obligations, the type-path walker for a failed selection, `find_trait_impl` for a
qualified value. `MemberLookup::Stuck` carries them out of member lookup. A fatal
failure travels as an ordinary `Err` through every frame above it; no stored
"failed" state is needed because nothing in the solver catches `Overflow` or
`Cycle`.

There is no generic result type. `Normalized` is `Result<TypeIndex, Unsolved>`;
the other solver queries spell out their own `Result<_, Unsolved>`. To get there
`normalize_children` clones the type once, normalizes its child lists in place and
re-interns (interning returns the original index when nothing changed);
`reduce_assumed_projection` is gone, replaced by `projection_equality` (whose
`Pending` is now `Err(Unsolved::Pending)`) plus `reduce_to_assumed`; and a trait
declaration with no default is `Failed` rather than `Ok(None)`.

A written type that is not a definition's value reports its own cycle: two
parameters that each walk into the same loop each report it. The values that
impl blocks supply for associated types are definitions, and they own their
loops (next section).

### Definitions own their loops

A loop has no root cause: `First = Self::Second` and `Second = Self::First` are
each wrong because of the other. Reporting it from every written type that walks
into it gave one report per mention. Detection was never the problem
(`SolverFrame::Projection` finds the loop); the missing piece was a place that records
"this definition's value has no meaning", so a reader that merely reaches it
fails silently, as it does for a value that failed to lower.

- `AssocValue` (`signatures.rs`), one per `AssocTypeIdx`, written only by the
  check pass: `Unchecked`, `Resolved(TypeIndex)` (the value normalized in the
  impl's own scope) or `Poisoned`. The signature itself stays as written.
- Lowering an impl's associated type value records `CheckAssocValue` instead of
  `CheckWellFormed`. It normalizes the value in the impl's scope and stores the
  verdict: `Ok` is `Resolved`; a cycle, an exhausted budget, or a failure
  derived from a poisoned value is `Poisoned`. Overflow is a verdict on the
  definition because the check starts with nothing in flight: a value that
  overflows from depth 0 overflows for every reader, which starts deeper. (Only
  a test that raises the budget between calls could tell the difference, and
  none involves an impl value.) A value that failed to lower is `Poisoned` from
  the start.
- `assoc_type_value` (solver) returns a silent `Failed` for a `Poisoned`
  provider. That is the only solver change: no new step kind, no new `Unsolved`
  variant, and the assumption-tautology rule (`blocked_at`) is untouched.
- `run_checks` runs every `CheckAssocValue` before any other check. The solver
  does not demand a verdict on the fly, so without this a use earlier in the
  source than the impl would meet an `Unchecked` value, walk the loop itself and
  report it again. It is a stable partition into two classes, not a topological
  sort: among definitions an `Unchecked` provider falls back to the written value,
  so whichever is first finds the loop and the rest read `Poisoned`.

Consequences, all pinned by tests: a loop through any number of values is one
diagnostic (`a_loop_through_two_impl_values_is_reported_once_at_the_first`,
`unused_associated_values_are_checked_for_direct_and_mutual_cycles`); the count
does not depend on source order
(`a_loop_through_definitions_is_reported_once_whatever_the_source_order`); and a
use that reaches a poisoned definition is silent even when the loop only exists
after substitution (`generic_projection_cycle_appears_only_after_substitution`:
`Loop`'s own value reports, `cyclic`'s parameter does not).

A loop that passes through no definition's value (for example a trait default
that only closes once `Self` is substituted, `associated_type_default_cycle_is_diagnosed`)
is still reported by the written type that closes it.

What this is not. It is not a set of reported loops or a bit on a goal: it is a
verdict on a definition, read exactly like the `ERROR` a failed lowering leaves.
This is the "targeted suppression" the rejected-alternatives list deferred, added
for the one place tests showed noise. rustc does not do this for projections (it
reports per site, partly deduplicated through the projection cache's cached
`Error` entry); it does for constants, where the query engine reports a cycle
once. We can because checks run after construction and we control their order.

Other options that were considered:

1. Report once at detection, inside the engine, and cache the error result
   (rustc's query engine does this for queries). Contradicts "queries never
   emit".
2. Remember a consumed loop in the normalization cache, keyed by scope: the same
   loop under another scope is reported again, and a query's answer depends on
   what was asked before.
3. Report per written site everywhere. Kept for everything that is not a
   definition's value.
4. Make the solver demand the verdict (`Unsolved::Pending` carrying the
   definition it needs, a driver in `TypeContext` running that check and
   retrying). Rejected: it adds a protocol to avoid a three-line ordering, and
   the solver's step stack is gone when the need is returned, so the driver
   could not tell a loop through a hypothesis (a tautology) from one through
   definitions.

### Cycles: definitions versus hypotheses

The in-flight stack is a stack of `SolverFrame`s: a `Projection` being reduced, or an
`Assumption` marker pushed around the normalization of a value that an equality
written in a bound supplied. A projection requested again while already on the
stack is a cycle. If an `Assumption` lies on the loop it is a tautology (circular
facts are consistent and give no value), so the projection stays abstract: the
detecting frame sets `blocked_at`, every frame above it unwinds to identity, and
the frame at that depth returns the projection unchanged. A loop through
definitions only (impl values, defaults) has no solution and is an
`Unsolved::Cycle`. `blocked_at` is a deliberate non-local exit: it has to cross
proof frames that know nothing about it. Treating equalities as an equivalence
relation instead of rewrite rules would remove it, at the cost of a congruence
closure per assumption context; not planned.

### Solver state and cache

Two structs in `solver.rs`, with `TypeContext` holding only the second:

- `SolverState`: what is being computed now (the stack of `SolverFrame`s, depth,
  rollback marker). Shared across re-entrant signature queries, deliberately, so
  cycle detection and the budget span them.
- `Solver`: wraps the state, the recursion limit (configuration, 128; only
  tests change it) and the finished-answer map, and owns the rule
  for when they meet (`cached`/`remember`), plus the two methods the rest of
  `tir` needs (`remaining_depth`, and `set_limit_for_test` in tests).

`Solver::normalize` is the cache layer and `normalize_uncached` the
computation, so the computation knows nothing about the cache.

### The solver is scoped by a view

Normalization and impl selection recurse into each other, so they are one
engine, and all of it lives on `Solver` in `solver.rs`:
`normalize*`, `find_trait_impl_query`, `check_assumed_trait`,
`match_trait_impl_candidate_query`, `match_impl_target_and_bounds`,
`projection_equality`. Every method takes a `SolverView<'_>`, a temporary struct
lent by `TypeContext::solver_and_view()` that holds exactly what the engine reads: the
interner (the one thing it extends) and read-only `defs`, `impl_dispatch`,
`traits`, `trait_impls`, `assoc_types`, `param_bounds`, `type_envs`. Diagnostics,
strings, the query engine, `query_state` and the other signature tables are
absent, so the solver can neither report nor construct, and the compiler
enforces it. `TypeContext` keeps thin wrappers (`normalize_*_query`,
`find_trait_impl_query`, `check_assumed_trait`, `match_impl_target_and_bounds`)
for the rest of `tir`; the impl-based ones also `debug_assert` that no signature
is being built. The cluster was measured, not guessed: it touched those eight
tables, its own state, and `query_stack` for that one assertion.

The cache is a pure performance cache with no diagnostic meaning, keyed by `(assumption_context: TypeEnvIdx, TypeIndex, Mode)`:

- It is bypassed whenever a normalization is in flight, for lookup and for
  insertion: an answer computed under active frames depends on cycle and rollback
  state, so only a request with nothing in flight is a function of the key.
- Only `Ok` is stored. `Pending` means a fact is not final yet; `Failed` is not a
  permanent verdict (a budget overflow can be retried, `normalization_overflow`).
  Caching `Failed` was tried and broke the two tests that raise the budget
  between calls.
- Validity rests on one invariant: **a non-`Pending` answer is final.** Any code
  path that reads a non-final fact (a subject whose `BoundClauses::equalities`
  is still `None`, an impl header
  still under construction) must return `Pending`. The suite is green without a
  "facts are final" switch, which is evidence for the invariant, not proof; a
  debug-only check that recomputes on a cache hit and asserts equality would
  turn it into a test.
- Goals containing `Type::Infer` must not be cached when inference arrives.
- Nothing is emitted inside normalization any more; overflow and cycles come
  back as `Unsolved::Overflow` / `Cycle` (see above).

No cache for `find_trait_impl_query` exists. Its answers inside active
normalization frames are not shown to be independent of that state, and nothing
consumes one yet.

### What disappears

`QueryState::{AwaitingChecks, Checking}`, `QueryEntry::deferred`,
`advance_signature`/`resume_obligations` and the mid-construction drain,
`Obligation::Normalize`, `complete_obligation`, `TypeRepair` and its three
folders, and the repair functions listed above. The signature query keeps only an
execution lifecycle (`Pending`, `InProgress`, `CycleReported`, `Resolved`), which
also makes the value-query kind (`tir-type-context.md`, constants) a clean second
query rather than a third state machine.

`Obligation`/`check_obligation` stay: body checking reuses them as the per-body
list (rustc's fulfillment context), where `Pending` means an unresolved
inference variable.

### Rejected alternatives

- **A general per-def taint set / `HAS_ERROR` type bit.** Not needed for
  correctness; only suppresses follow-on noise. The noise showed up in one place
  (a loop through impl values, reported once per mention), and the targeted
  suppression for it is `AssocValue`; nothing more general has been needed.
- **D2: keep substitution, rewrite once after the check pass.** Coherent (wx has
  mutable tables and no incremental compilation, so rustc's reason for immutable
  results does not bind). Rejected for D1 because it keeps a rewrite pass that
  must enumerate every type-holding table, plus pattern matching on interned
  types. Substitution is only trivial when the check is eager.
- **A set or per-entry bit recording "already diagnosed"
  (`reported`/`diagnosed_goals`/`Entry::diagnosed`).** Built once and removed: it
  only hid a duplicate that two emitting code paths created. Fix the emitters.

## Implementation status

Done (2026-10-17, "Impl requirements are definitions"): `AssocValue` became
`Verdict`, keyed by `solver::Definition` (`Member(ImplMember)` or
`Requirements(ImplKind)`). An impl's requirements are judged once for its own
parameters in its own scope (`Solver::requirements_verdict`,
`SolverFrame::Requirements`); impl selection consults that verdict before
proving them for its arguments (`satisfies_clauses`, shared with use-site
checks). A loop through them is reported once by `CheckImplRequirements`, at
the bound it closed in, whatever the source order; selections stay silent.
A loop that only some instantiation reaches and the impl's own judgement does
not stays an unowned (`owner: None`) loop, reported by each asker.

Done (latest, "Definitions own their loops"): `AssocValue` verdicts per
associated type, `Obligation::CheckAssocValue` in place of `CheckWellFormed` for
an impl's value, the solver's silent `Failed` for a `Poisoned` provider, and the
definitions-first partition in `run_checks`. Three tests changed their expected
count (two values: 2 to 1; `unused_associated_values_...`: 2 to 1 for the mutual
cases; `generic_projection_cycle_appears_only_after_substitution`: 2 to 1) and
two were added (source order; an overflowing value is reported once and
poisoned). Mutation checks: running uses before definitions, ignoring `Poisoned`
in the solver, and not poisoning on overflow are each caught. `run_checks`
asserts that no definition is `Unchecked` once the definitions pass ends.

Done (later, "Construction does not normalize"): `resolve_type` no longer
normalizes; qualified and unqualified type paths record membership instead of
searching impls; `CheckWellFormed` added; `ensure_assoc_type_value_query`,
`ensure_assoc_type_default_value_query` and the impl-header `ensure_signature`
calls are plain reads; `Unsolved::{Overflow, Cycle}` replace emission from inside
normalization; four tests of the demand-driven access path were deleted.

Done: construction records checks and never decides a bound; `run_checks` runs
them after construction in definition order; `Obligation::Normalize`,
`TypeRepair` and its folders, `ObligationArena`, `AwaitingChecks`/`Checking`,
`QueryEntry::deferred`, the repair functions and `BoundArena::recover_value` are
deleted; `reduce_projection` no longer emits; successful top-level
normalization is memoized.

Tests: the suite was rewritten against the new contract. Tests that asserted
the stored form of a projection now assert both the stored form
(`is_projection_param`) and its meaning (`normalized_param`); tests that asserted
`ERROR` substitution after a failed bound assert the one diagnostic and that the
written type and stored facts are unchanged; overflow and cycle tests assert the
returned `Unsolved` and an empty diagnostic list at the query level, and the
diagnostic at the site level. Mutation checks (dropping the `CheckWellFormed`
record; making `report_unsolved` swallow) are each caught by the cycle and
overflow tests. `the_embedded_stdlib_sweeps_without_diagnostics` pins the real
`std/main.wx`.

Assumptions as flat clauses (2026-10-17): the merged bound trees
(`ImpliedTraitBound` and its nested bindings, `BoundFacts`, the
`AssumptionFacts` cursor and `EffectiveBounds`) are replaced by
`bounds::BoundClauses`, ranges of `TraitClause`/`EqualityClause` in one
`ClauseArena`. Each written bound becomes clauses in one pass, a supertrait's
clauses copied in with `Self` substituted; trait clauses are published before
equality values are resolved. Readers scan a scope's clauses
(`assumed_traits`) or the declarations along a receiver's projection path
(`declarations_of`, matched without interning). A use substitutes and proves each
clause (`Solver::satisfies_clauses`); a clause reached through a membership
that fails is not proved. Ambiguity is decided where equalities are read; a
conflict is reported when the clauses are built, once, and not again by a
declaration that inherits both values. The migration ran with a debug-only
check that the clauses described what the trees did, then deleted the trees.

`ValueType` (2026-10-17): std's `trait ValueType {}` holds for a type whose
values are exactly one Wasm value, and `Global::Value` requires it, checked
like `Memory::Size` (`resolve_global_signature` records the bound). No impl
provides it: `find_trait_impl_query` answers it from `Solver::value_layout`,
the receiver's values in declaration order (`LayoutValue::Known(ValType)`),
as `TraitImplLookup::Builtin`. A parameter or a projection that does not
reduce is one `LayoutValue::Abstract` value when assumed `ValueType`, so
`Wrap<T>` holds under `T: ValueType`, and an instantiation is proved where it
is used; an address into a memory not known yet is one abstract value too.

Generic construction (2026-10-18): a body lowers a written type into its own
obligation list and checks it on the spot (`check_now`). A generic struct's
type arguments are learned within the call, as the old checker did and rustc's
inference does in its simplest case, without a table: slots start as the
written arguments (`_` anywhere is `INFER`) or `INFER`, meet the expected
type's (`TypeInterner::meet`), then learn from each field's value
(`TypeInterner::learn`, walking the declared field type to the struct's own
parameters). A slot still not known is E2002 "cannot infer type for type
parameter"; every final argument's bounds are proved at the call, as every use
proves its own instantiation (so an annotation's violation is reported there
too). `TypeFlags` on interned types (`HAS_INFER`, `HAS_ERROR`, `HAS_UNTYPED`)
answer "anywhere inside" without a walk. Tuples are expressions: a tuple of
untyped literals is untyped, and takes its type from context like a literal.
The layout is the type checker's alone; MIR lays types out itself. A
hand-written `impl ValueType` is not rejected yet; that comes with the other
builtin traits.

## Invariants

- Order: construction, then check pass, then bodies. Construction-time code does
  not emit trait-failure diagnostics for a requirement it left to the check pass.
- Queries never emit (except the normalization budget overflow). Every
  requirement has exactly one owning site.
- Two written sites that fail the same proposition each get a report
  (`trait_impl_member_signatures_recover_from_failed_generic_requirements`
  expects 2). Suppressing the second would need per-cause state, which this
  design deliberately does not have. The exception is a loop through an impl's
  associated type values: those are definitions and own the report.
- Definitions are judged before anything reads them: every `CheckAssocValue`
  runs before any other check. Breaking the order does not make the compiler
  unsound, it makes loops report more than once, and the source-order test
  catches it.

## Open questions

- Unqualified `Type::Name` selection no longer needs impl headers during
  construction (declared bounds, the `ImplDispatch` index and assumptions only),
  and the real stdlib plus the suite resolve. The visible consequence is the
  decision already taken: a member of a concrete projection
  (`Wrapper::Item::Value`) is an error that says which trait to write, as in rustc. In type
  position `<<` is split by the parser, so `<<A as B>::C as D>::E` is accepted.
- Derived errors that do *not* come through a silent query: a body that asks
  `S<u32>: Other` (impl bound `T: Trait`) after `u32: Trait` failed at a
  signature site reports its own error at its own site. Bodies assume their
  signature is well-formed and do not re-check it, which should remove the main
  source; watch for the rest once bodies exist.
- Every `Failed` out of normalization must have an owning site that reported or
  recorded it. Projections made by instantiating a declaration at a use site are
  owned by that site's bound check. Audit when bodies instantiate generics.
- `AssocValue::Resolved` is written but nothing reads it. Reading it in
  `assoc_type_value` was tried: one test moved
  (`head_normalization_exposes_constructor_without_traversing_children`). Part of
  that is the test overwriting the stored signature behind the verdict's back,
  which shows the cost, a second source of truth next to the signature. The rest
  is real: a `Resolved` value is the deep form, so a `Head` request would get
  its children reduced too. With no measured cost to save, either drop the
  payload (`Sound`) or read it behind a debug check that recomputes and compares.
- Trait defaults (`type Item = ...` in a trait). The definition here is the
  *impl that omits the member*: its value is the default with `Self` substituted,
  and it has no `AssocTypeIdx` of its own. Probed: an omitted default that loops
  (`type Item = Self::Item`) and is never mentioned reports **nothing**, a missed
  error; mentioned twice it reports twice. The loop only exists after the
  substitution, so a verdict on the trait's default cannot hold it. Candidate:
  one `CheckDefaultedValue { impl_index, declaration }` per omitted member that
  has a default (indices only, so construction needs nothing from the default),
  normalizing `<Target as Trait>::Member` in the impl's scope at check time, with
  the verdict kept per `(impl, declaration)` and read in the solver's
  `TraitDeclaration` branch. It joins the definitions class in `run_checks`.
- Constants, discriminants and array lengths cannot reuse the ordering trick if
  construction ever needs their value (a length in a signature): they need the
  demand-driven value query (`QueryKind`, migration step 5), which reports a
  cycle at detection and continues with `ERROR`, as `ensure_signature` does.
- Only the first loop found through a definition is reported; a second loop
  through the same definition appears once the first is fixed. By design: the
  check stops at the first `Err(Cycle)`, and the definition is then poisoned.
- Lowering records requirements in the list its caller passes
  (`obligations: &mut Vec<Obligation>`, rustc's fulfillment context): a
  signature's is kept and checked by `check_declarations`, a body's is checked
  right after lowering, once every fact is final. `find_trait_impl`'s `Pending`
  arm records into the same list.

- A trait's function type is nominal: `<Point as Make>::make` is the
  declaration over `Self` (`make<Point>`) and is never normalized into the
  impl's member. Normalization handles associated-type projections only, and
  the impl's body is chosen where a call is resolved (`method_call` in bodies,
  monomorphization later). The cost: a use sees the trait's declared signature,
  so an impl whose signature disagrees is accepted until trait-impl conformance
  checks signature agreement.

## Migration

Steps 1-4 are done (see "Implementation status"); each was meant to keep the
suite runnable, but steps 2-3 delete tests whose subject no longer exists and
leave 15 asserting the old `ERROR`-substitution policy.

1. **Defer every check to a post-construction pass.** A `defer_checks` flag is
   set during the sweep's construction loop: check sites only record, and
   `resume_obligations` is a no-op. After the loop the flag clears and every
   declaration is drained in definition order. The flag is scaffolding for the
   period where the old eager path still exists; it is deleted in step 3, when
   check sites record unconditionally and the drain functions are gone. Repair is
   still applied, so this step changes timing, not policy. Failures show where construction relied on an
   eager answer. Status: see below.
2. **Drop `Obligation::Normalize`.** Stop registering normalization work; keep
   projections symbolic.
3. **Replace repair with nothing.** Delete `TypeRepair`, `AwaitingChecks`,
   `Checking`, `deferred`, the mid-construction drain; rewrite the recovery tests.
4. **Make queries pure and memoize normalization.** Remove emission from
   `reduce_projection`; memoize top-level `normalize`. Done.
5. **Value queries** on the simplified engine (`QueryKind`, separate state).
