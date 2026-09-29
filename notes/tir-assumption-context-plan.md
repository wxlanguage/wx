# TIR assumption context implementation plan

Status: checkpoints 1–4 accepted; checkpoint 5 implemented and ready for review.
Updated 2026-09-28.

## Objective

Make signature checking preserve declaration-local assumptions across type
normalization, and delay definitive bound validation until its dependencies are
complete. The result should provide a usable assumption context for the future
body checker.

The four confirmed failing probes cover three causes:

1. A projection reduces to a bounded parameter, but satisfaction does not read
   that parameter's bounds.
2. A bounded type on an equality RHS is validated while sibling equalities are
   still provisional, producing a premature error.
3. Normalization changes a subject from a projection to a parameter, making an
   assumed trait unreachable during impl matching and through stored signatures.

## Review workflow

Implement one checkpoint at a time. Each checkpoint includes its relevant tests,
leaves the compiler library buildable, and ends with a review handoff. Wait for
the user's instruction before starting the next checkpoint.

A handoff reports:

- What behavior changed and which invariants now hold.
- The principal files and design decisions to review.
- The checks run and their results.
- Remaining limitations and any evidence requiring a change to this plan.

Use behavior and responsibility boundaries to size checkpoints. Closely connected
changes may span several modules. Avoid splitting an implementation merely to
meet a line-count target.

Keep intermediate checkpoints green. Record unresolved reproductions here or in
review notes; introduce their permanent regression tests with the implementation
that makes them pass. Do not add ignored tests or accept pending work as success
to obtain a green suite.

## Design constraints

- A TypeIndex identifies a type; an explicit AssumptionContext identifies the
  declaration-local assumptions available to a semantic query.
- Initially the context is a handle over the existing TypeEnvIdx parent chain.
  Parameter identities, lexical names, source bounds, and substitutions keep their
  existing representations.
- Existing bound trees remain the source of facts. Expose scoped facts with
  explicit subjects and preserve BoundId/BindingRef provenance and contextual
  Self substitution. Start with traversal; add an index only if justified.
- Ready abstract types are valid normalization results. Pending dependencies and
  diagnosed failures remain distinguishable from them and from failed proof.
- Impl requirements are instantiated obligations proved in the caller's context.
  They do not become caller assumptions.
- Reentrant declaration queries use their own explicit contexts. Cycle detection
  accounts for context when it affects the meaning of a query.
- Assumptions about an outer parameter introduced by an inner declaration stay
  local to the inner declaration.
- No global normalization cache while facts remain mutable.
- Preserve existing error recovery, source diagnostics, and allocation discipline.

## Checkpoint 1: Context identity, scoped facts, and ownership

Introduce AssumptionContext as a small handle over TypeEnvIdx. Provide traversal
of the active frame and its ancestors. Preserve TypeEnvArena in the finished
SignatureRegistry so stored environment handles remain usable.

Expose the semantic facts available through a context: trait memberships about
explicit subjects and projection equalities. Reuse existing implied bound trees,
including inherited and nested associated-type requirements. Account for
associated declaration bounds and their SelfSubstitution when interpreting them.
Keep readiness and source provenance visible to consumers.

Do not change trait satisfaction behavior in this checkpoint.

Primary areas: types.rs, bounds.rs, signatures.rs; a small assumptions.rs module
is appropriate if it gives the context and its reader a clear home.

Verification:

- Local and inherited scopes expose the expected facts.
- Sibling and unrelated declarations do not contribute assumptions.
- Nested subjects, inherited trait bounds, and Self substitution are correct.
- Provisional and completed facts retain their distinct lifecycle states.
- The finished registry retains the data required to read a context.

Review boundary: representation and ownership, without a new proof algorithm.

Checkpoint 1 handoff:

- Added assumptions.rs with AssumptionContext, a borrowed AssumptionReader,
  explicit-subject facts, and an iterative cursor over existing bound trees.
- Scope traversal excludes name-rebinding frames and visits enclosing parameter
  scopes without including siblings. Implicit trait Self membership has an
  explicit origin rather than an invented written BoundId.
- Scoped enumeration visits finite parameter trees. Associated declaration
  facts are read along a requested subject's projection path, preserving
  SelfSubstitution. This avoids expanding recursive declarations into infinitely
  many subjects. Their readiness is checked by that subject-specific read.
- Equality views retain known, ambiguous, and conflicting states and borrow their
  source data. Reading Pending facts does not authorize equality reduction.
- Moved the existing effective_bounds traversal onto the shared reader; the
  builder delegates with its existing normalization budget. Satisfaction rules
  and declaration validation order are unchanged.
- The finished SignatureRegistry now owns TypeEnvArena and uses the same reader
  as the builder. Storage and the interner are lent separately, allowing subject
  interning without cloning bound trees.
- Nine new tests cover scope isolation and shadowing, rebinding, inherited and
  nested subjects, provenance, contextual Self, equality states, readiness,
  non-forcing declaration reads, and finite recursive declaration paths.
- Validation: cargo test -p wx-compiler --lib: 453 passed, 0 failed, 0 ignored.
  Changed Rust files pass rustfmt --check; git diff --check passes.

The three confirmed semantic failure causes remain for checkpoints 2 and 3.

## Checkpoint 2: Symbolic construction and deferred validation

Separate forming a type from validating its well-formedness obligations. Keep
name, member identity, and argument-count checks immediate. Collect trait-bound
obligations with their context, subject, required trait, reference span, and bound
provenance when checking depends on unfinished facts.

Make pending dependencies explicit through the query paths needed by obligation
validation, including normalization and impl matching. Thread context explicitly
through those paths; retain the existing subject-directed lookup semantics until
checkpoint 3.

Own deferred obligations by the declaration query being built. Publish all
sibling bound facts before validating obligations created while resolving their
equality expressions. A pending dependency is retried after completion; it is
neither a bound violation nor a successful validation.

Define recovery for failed obligations before a signature is treated as
validated. Reentrant declarations must not drain each other's obligations or
inherit each other's contexts.

Primary areas: signatures.rs, satisfaction.rs, normalize.rs, impl-selection
callers.

Verification:

- Need<U::Item> on an equality RHS succeeds once U::Item = i32 and i32: Marker
  are available, in both sibling declaration orders.
- A corresponding unsatisfied argument still produces the bound diagnostic.
- Immediate arity and identity diagnostics retain their behavior.
- Reentrant queries, cycles, and overflow retain controlled recovery.
- Pending obligations cannot be silently left in a validated signature.

Review boundary: declaration lifecycle and the distinction between construction,
pending proof, completed proof, and diagnosed failure.


Checkpoint 2 handoff:

- Checking remains eager when facts are ready. Only `Pending` creates a deferred
  obligation; a negative answer and diagnosed recovery remain distinct results.
- `Bounds`, `Trait`, and `Normalize` retain their separate representations.
  Bounds refer to the eventual parameter or associated-type requirement table,
  rather than copying a provisional list of requirements.
- SignatureBuilder owns one ObligationArena. Each existing query entry has a
  four-byte optional chain head; links accommodate reentrant allocation without
  a per-query vector, a second query registry, or a final validity map.
  Retries reuse slots. Completed payloads are removed; the buffer lives until
  the builder is consumed. Measured arm64 layouts: Obligation 56 bytes, node
  64 bytes, optional head 4 bytes.
- The existing QueryState tracks construction, available data awaiting checks,
  active checking, and completion. `SignatureStatus::Available` permits reads
  of structural data without claiming validation has completed.
- Generic environments are published before resolving their source bounds.
  All sibling facts become ready before queued RHS checks resume and before
  field/parameter types are resolved. Recursive applications therefore read
  their eventual requirements rather than an empty provisional list.
- Retries run at fact publication, query completion, and subsequent requests
  for a signature awaiting checks. The existing declaration sweep visits every
  AST entry, including queries forced recursively while an outer declaration's
  facts were provisional. It completes their deferred work without a separate
  final retry pass. Pending work after that sweep is an internal invariant
  failure, not a speculative user diagnostic.
- Deferred normalization installs its result into the owning signature. Failed
  bounds recover the affected application argument and the owner's source and
  implied facts, preserving binding identity, spans, and unrelated types. These
  repairs traverse that declaration's stored roots only when deferred work
  completes; they are not another stored result table. Review this recovery
  code in signatures.rs and obligations.rs in particular.
- Explicit AssumptionContext is threaded through normalization, bound checking,
  impl matching, and the member paths required by qualified projection checks.
  Subject-directed proof rules remain until checkpoint 3.
- Ten new regressions cover both sibling orders, targeted failure recovery,
  recursive eventual requirements, qualified projection deferral and failure,
  reentrant ownership, normalization writeback, interleaved arena ownership,
  allocation-free eager checking, and slot reuse across pending retries.
- Validation: cargo test -p wx-compiler --lib: 463 passed, 0 failed, 0 ignored.

Remaining work at this boundary:

- Equality-aware membership and preservation of projection-subject evidence
  remain checkpoint 3 work (the first and third original failure causes).
- An audit probe confirmed an unqualified member-selection gap for checkpoint 4:
  with `impl Project for Need<i32>`, an equality RHS `Need<U::Item>::Output`
  before sibling `U::Item = i32` becomes ready returns an error type without a
  diagnostic. The qualified form `<Need<U::Item> as Project>::Output` now works.
  `resolve_concrete_member` still collapses a pending candidate match to
  TypeMemberLookup::Error. Deferring the membership of an already identified
  qualified member does not solve deferred name selection among competing
  inherent and trait candidates. This needs an explicit design in checkpoint 4,
  including ambiguity and precedence; do not treat this checkpoint as fixing
  every pending member-lookup path. The probe was temporary and restored; its
  passing regression belongs with that implementation.

## Checkpoint 3: Equality-aware satisfaction and impl selection

Use the scoped fact reader to prove trait membership for equivalent subjects.
First consult direct facts; then use equality reduction to compare the requested
subject with the subjects of assumptions. Reclassify normalized abstract results
and consult their bounds before concrete impl dispatch.

Keep assumption-subject comparison independent of the trait proof currently being
attempted, with bounded recursion and context-aware cycle handling. Build on the
existing projection equality rules; document unsupported ambiguous symbolic
equalities rather than inventing a general equality solver.

Integrate this query into generic argument checking and impl candidate validation.
Continue normalizing nested receiver types for structural matching. Prove the
candidate's instantiated requirements in the caller's context, so normalization
does not make its evidence unreachable.

Primary areas: bounds.rs/context reader, satisfaction.rs, signatures.rs,
normalize.rs.

Verification:

- T::Item = U with U: Marker permits Need<T::Item>.
- T::Item = U with T::Item: Marker permits checking U: Marker locally.
- The bounded generic impl for Wrap<X> matches Wrap<T::Item> after reduction to U.
- Stored normalized signature parameter types retain their assumed guarantees.
- Concrete specialized impl matching continues to work.
- An impl's own requirements cannot prove themselves in the caller.
- Inner assumptions about outer parameters do not escape their scope.

Review boundary: the proof rules and their semantic limits. All four original
probes should now be permanent passing regressions.


Checkpoint 3 handoff:

- `check_trait` first reads direct facts, then searches the caller's scoped
  assumptions for memberships on equal subjects. It rechecks a normalized
  abstract result before concrete dispatch. A completed impl match can still
  prove membership when unrelated scope facts remain pending.
- Evidence comparison uses a new Assumptions operation in the existing
  normalizer. It reduces known equalities through nested type structure but
  does not select impls or demand provider values. This prevents comparison
  from recursively invoking the trait requirement it is trying to prove.
  It reuses the existing depth budget and active projection frames; cycle keys
  include context and operation so provider reduction and evidence comparison
  do not falsely identify each other as recursive reentry.
- Scope lookup retains only temporary scalar subject handles while releasing
  borrowed readers before normalization. It introduces no persistent cache,
  index, declaration state, obligation kind, or additional pipeline pass.
  Direct proofs return before that fallback scan. Relevant-subject buffers and
  finite fact traversal are the cost of the uncached fallback.
- Written equality subjects supply finite paths for reading associated-type
  declaration bounds, with the reader's existing contextual Self substitution.
  This handles `Container::Item: Marker` with `T::Item = U` as well as explicit
  nested memberships, without recursively expanding every associated declaration.
- Generic impl matching still deeply normalizes receivers before structural
  matching. Each inferred argument's trait requirements use `check_trait` in
  the caller's context, never the candidate's assumption environment. Removed
  redundant head normalization immediately before that proof call.
- Eleven new tests cover the remaining original probes, stored normalized
  parameters, associated declaration evidence, local evidence about outer
  parameters, sibling isolation, impl requirement isolation, ambiguous and
  cyclic equalities, pending retries, and overflow recovery. The sibling-order
  regression from checkpoint 2 supplies the fourth original probe.
- Validation: cargo test -p wx-compiler --lib: 474 passed, 0 failed, 0 ignored.
  Changed Rust files pass rustfmt --check; git diff --check passes.

Limits retained at this boundary:

- Equality comparison follows the existing normalizer: competing equalities
  remain ambiguous, and assumed cycles remain symbolic. This is not a general
  equality solver or a proof of every mathematically equivalent cyclic term.
- Impl requirements containing associated equalities or nested constraints
  remain conservatively rejected, as before. This checkpoint proves their trait
  memberships; proving those additional requirement forms is separate work.
- Member discovery and qualified membership consumers still require checkpoint
  4's integration. In particular, the previously recorded unqualified pending
  lookup gap remains. This checkpoint changes the proof used by generic bounds
  and impl requirements, rather than claiming all member consumers are complete.

## Checkpoint 4: Member lookup and consistent semantic consumers

Bring type/member lookup onto the same contextual membership and impl-selection
rules. Keep diagnostic emission at the appropriate caller and preserve the
associated declaration/provider identity distinction.

Audit each normalization, satisfaction, and impl-selection call site for the
correct context: the declaration being constructed, the caller proving an
instantiated requirement, or the provider whose stored value is being resolved.
Ensure eager normalization and symbolic lookup follow compatible rules.

Primary areas: members.rs, normalize.rs, satisfaction.rs, signatures.rs.

Verification:

- A trait member available through an equivalent assumed subject is found.
- Qualified projection lookup and concrete providers retain correct identities.
- Missing and ambiguous members retain useful diagnostics without duplicates.
- Reentrant provider queries cannot leak their declaration's assumptions.
- Existing normalization recovery and allocation regressions pass.

Review boundary: consumer consistency and diagnostics, after the proof rules are
already independently reviewable.

Checkpoint 4 scope agreed after design review:

- Keep ordinary associated-type projections whenever the declaring trait is
  known. Qualified dependent bindings use the existing deferred checks.
- Do not introduce an intermediate unresolved-member type, deferred name
  construction, destination slots, or another query system.
- An unqualified name whose declaration cannot yet be selected is unsupported
  at this boundary. Diagnose it and suggest trait qualification; do not silently
  return an error type or pretend selection has completed.

Checkpoint 4 handoff:

- `check_trait` delegates to `find_trait_impl_query`, which combines the caller's
  equality-aware assumption proof with existing impl dispatch. Concrete receivers
  prefer a matching real provider; assumption-only evidence remains symbolic.
  Error and inference placeholders cannot prove membership.
- Direct abstract-bound member discovery retains its existing precedence and
  accepts known declaration identities while binding values are provisional.
  When those bounds do not identify the name, lookup discovers candidates from
  finite scoped memberships and associated declaration bounds along written
  equality paths, then proves applicability through the shared trait query.
- Concrete member discovery keeps inherent precedence, filters candidates by
  the requested name before checking their requirements, and combines dispatch
  candidates with scoped evidence. It does not scan every program trait or add
  a persistent index or cache. Temporary candidate buffers live only for lookup.
- `TypeMemberLookup::Pending` is a query outcome, not a stored type. Pending
  discovery and applicability remain distinct from absence and diagnosed failure.
  An unfinished competitor cannot be silently dropped from a unique selection.
  Two already established declarations still produce the ambiguity diagnostic.
- Type-path construction reports E2104 with a qualification hint when unqualified
  selection is pending. `<Receiver as Trait>::Member` continues to construct the
  existing projection and defer membership/normalization in the owning signature
  query's existing arena. No changes to obligation payloads or interner variants
  are needed. In particular, qualified bindings may depend on a later binding
  of the same parameter, in either source order.
- Fifteen new tests cover equivalent-subject member lookup, qualified lookup,
  associated declaration evidence, duplicate and ambiguous traits, sibling scope
  isolation, concrete provider identity, assumption-only concrete subjects,
  qualified dependent bindings and failure recovery, ready unqualified selection,
  pending selection and discovery diagnostics, irrelevant inherent requirements,
  and shared-budget overflow recovery. New source fixtures assert parser/linker
  success. Renamed one previous test's method from the reserved keyword `local`.
- Consumer audit: qualified lookup and projection normalization use the shared
  trait-selection query; generic requirements use its boolean adapter in the
  caller context. Provider values retain their definition context before
  substitution and their caller context afterward. Steps 1–3's obligation
  ownership, recovery, and normalization machinery remain unchanged.
- Validation: cargo test -p wx-compiler --lib: 489 passed, 0 failed, 0 ignored.
  Changed Rust files pass rustfmt --check; git diff --check passes.

The remaining limitation is deferred unqualified declaration selection. This
checkpoint deliberately requires qualification in that case and does not claim
Rust parser or language-feature parity. Finished-registry handoff and the final
pending-path audit remain checkpoint 5 work.

## Checkpoint 5: Finished-signature handoff and final audit

Verify that a function's stored environment identifies the context its body will
use and that the finished registry preserves the required scopes and fact arenas.
Demonstrate reading those assumptions after the signature builder is consumed.
Document the semantic operations the body checker will reuse; extract shared
readers where necessary, without adding an unused generic provider abstraction.

Audit validation completion and the remaining pending-result paths. Run the full
compiler library suite, formatting checks, and diff checks. Broaden checks only
where the changed scope justifies it.

Review boundary: acceptance of the complete signature-phase change and its body
handoff, before function body checking begins.

Checkpoint 5 handoff:

- Added `FunctionSignature::assumption_context()`, derived from its existing
  lexical scope. No context table, validity cache, or additional query state is
  retained. Tests read local, inherited, and trait Self facts from the finished
  registry after its builder has been consumed.
- Verified that normalized parameter types still have their original equality
  evidence and source provenance available. Method-local facts about an outer
  parameter stay local; a method without its own parameters retains its enclosing
  Self scope. Associated declaration equalities retain contextual Self substitution.
- Audit found and fixed two recovery gaps: failed deferred normalization did not
  repair owning assumptions, and assumption proof could return `Failed` on a
  traversal overflow without a diagnostic. The deferred-recovery regression
  explicitly reopens provisional facts to exercise the retry boundary. Successful
  reductions continue to preserve symbolic source terms.
- Consolidated overflow reporting across normalization, bound readers, member
  discovery, and satisfaction. It reports the existing diagnostic, poisons only
  an active normalization, and permits later independent queries to recover.
- The completed location projection now checks that each owner chain is empty;
  registry handoff also checks that all arena payloads were dropped. These
  debug checks add no release-build pass over terms or retained validation state.
  Eager checks do not allocate deferred slots.
- Seven regressions cover finished normalized evidence, successful symbolic source
  retention, inherited method contexts and sibling isolation, trait Self and
  instantiated associated declaration bounds, successful/failed queue completion,
  failed deferred normalization recovery, and overflow diagnostics/recovery.
- Added [body-checking handoff notes](tir-body-checking-handoff.md) with the data
  lifetime, context selection, pending-result audit, reusable operations, and
  explicit remaining limits. Proof methods still live on SignatureBuilder;
  adapting them to the completed registry belongs with body-checker implementation.
  The shared reader is already available to both stages.
- Validation: cargo test -p wx-compiler: 496 passed, 0 failed, 0 ignored; doc tests
  also pass (none present). Changed Rust files pass rustfmt --check and
  git diff --check passes.

## Scope boundary

This plan covers the confirmed assumption and readiness failures, contextual
semantic consumers, and preservation of their data for body checking. Implementing
function bodies, missing item-signature kinds, impl conformance, production entry
point wiring, and backend reconnection are separate work.

If a checkpoint reveals a dependency on one of those tasks, explain the concrete
dependency and revise the plan at that review boundary.
