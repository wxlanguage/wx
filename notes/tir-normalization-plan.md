# TIR normalization implementation plan

Status: checkpoints 1–4 implemented; checkpoint 4 ready for review.
Checkpoint 5 pending. Updated 2026-09-28.

Structural substitution is already implemented in `tir/types.rs`, including
single-frame parameter replacement and allocation-free traversal of unchanged
types. This plan builds on it. The latest full compiler library test result is 434 passed, 0 ignored,
including all active TIR tests.
The concrete qualified projection test was enabled in checkpoint 2.

This plan targets the active replacement TIR modules. Older planning notes and
`tir/builder/` contain useful prior work, but their completed features are not
necessarily wired into the current compiler.

## Review workflow

Work through the checkpoints below in order. Each checkpoint is a coherent
implementation and its tests, not a line-count limit. Finish the whole checkpoint,
verify it, and stop for review before starting the next one.

At each handoff, report:

- The behavior delivered and the important implementation choices.
- The files and entry points worth reviewing.
- Test results and any remaining limitations relevant to that checkpoint.
- Any evidence that changes a later part of this plan.

Keep the active compiler library buildable and its TIR suite passing at every
checkpoint. Do not create an intermediate commit that knowingly loops on a cyclic
input or mistakes an unfinished bound table for a complete one. A checkpoint may
span several development edits; review happens after the complete slice works.
Commits and PRs are separate from these review checkpoints and are not required.

## Agreed API and invariants

Implement the entry points in a new `tir/normalize.rs` as methods on
`TypeContext`, following the existing sibling-module pattern:

```rust
pub(super) fn normalize_head(
    &mut self,
    ty: TypeIndex,
    reference: SourceSpan,
) -> TypeIndex;

pub(super) fn normalize_type(
    &mut self,
    ty: TypeIndex,
    reference: SourceSpan,
) -> TypeIndex;
```

`normalize_head` reduces a projection far enough to expose its outer constructor,
or leaves a valid abstract projection. `normalize_type` also visits contained
types. Both use the same reduction rules. Neither expands nominal types into
their fields or performs layout analysis.

Successful normalization need not produce a concrete type. Preserve valid abstract
projections and unresolved inference rather than diagnosing a missing impl merely
because reduction cannot yet proceed. Invalid projections, cycles, and overflow
use diagnostics and `TypeIndex::ERROR` recovery; already-diagnosed dependencies
must not produce a diagnostic at every access while unwinding.

Normalization reads existing parameter and associated-type bounds. Parameter
identity already includes its declaring environment; do not introduce a redundant
caller environment argument initially. If a real consumer needs additional
assumptions not represented by these identities, revisit that contract explicitly.
Incomplete assumptions are not an empty final environment.

Keep structural substitution separate:

```rust
let instantiated = self.types.substitute(template, &substitution);
let normalized = self.normalize_type(instantiated, reference);
```

A projection always identifies the trait's associated-type declaration. A selected
impl member is the provider of its value. These identities must not be exchanged
depending on whether the receiver happens to be concrete.

Keep private normalization state on the builder: active instantiated projections,
source information, and recursion depth. Re-entrant normalization through a
signature demand must preserve the active chain. All exits unwind their own
frames; subsequent independent requests start with no leftover active entries.
Use an active stack, not a permanent visited set. Keep the existing signature
query stack for unfinished declaration dependencies. Start without a global
normalization cache or a replacement query engine.

Preserve the allocation discipline established by substitution: copy scalar fields
before recursion, re-read children through stable indices, and allocate child
lists only when constructing changed output requires them. Do not clone every
type or collect every list before knowing that it changes.

## Checkpoint 1 — Associated-type identity and provider access

Implemented and verified:

- Trait-associated lookup results and projections carry the declaration index.
  The selected impl remains in `MemberSource`; value-member selection is preserved.
- `assoc_type_provider(impl_index, declaration)` returns an optional
  `AssocTypeProvider` handle with a private constructor. The value accessor accepts
  this handle, preventing a required declaration from being used as a provider.
- `ensure_assoc_type_value` demands the existing query identified by the provider's
  `def_id`, then reads the associated-type slot. No extra ownership table is needed
  for synthetic memory/global providers, including imported ones.
- Declaration-bound demands are explicitly named `ensure_assoc_type_bounds`.
  Missing required values recover with `TypeIndex::ERROR` without a diagnostic;
  the later conformance pass owns missing-member reporting. Value query cycles
  recover with `CyclicAssociatedType`, with names for written and synthetic owners.
- Concrete projection construction is now available, but does not reduce the
  projection. The original concrete-result test stays ignored until checkpoint 2.
- Six regression tests cover declaration/provider identity, forward demand,
  synthetic owners, query-cycle recovery, existing errors, missing required members,
  and preservation of value-member overrides/defaults. Query cycles are exercised
  at the accessor boundary; end-to-end normalization cycle tests remain in step 2.
- `cargo test -p wx-compiler --lib tir::`: 244 passed, 1 ignored.

**Deliverable:** member lookup preserves declaration/provider identity explicitly,
and callers can demand a provided associated-type value through one operation.

Primary files: `defs.rs`, `members.rs`, `signatures.rs`; adjust `types.rs` only if
needed to document or enforce projection invariants.

Work:

- Refine the type-member result so the trait declaration remains identifiable
  when lookup selects an impl override. Choose the smallest representation that
  avoids storing redundant facts and leaves value-member lookup intact.
- Centralize creation of trait-associated projections using the declaration's
  `AssocTypeIdx`; audit existing producers and bound consumers.
- Add an internal `ensure_assoc_type_value(provider, reference) -> TypeIndex`
  accessor. Its input is an actual provider, not a bare required declaration.
- Support written impl members and synthetic memory/global members. The latter
  are populated by their owner's signature query, which does not return
  `SignatureLocation::AssocType`.
- Make provider provenance explicit wherever needed to demand the correct query.
  Reuse existing identities and ownership facts before adding another table.
- Keep declaration-bound forcing distinct from provided-value forcing, including
  diagnostic wording. Handle query cycles and already-reported failures.
- Define controlled recovery for a concrete impl that omits the requested required
  member. Provider lookup returns `None`; callers recover with `TypeIndex::ERROR`
  without emitting a missing-member diagnostic. Conformance checking, after full
  signature resolution, owns that diagnostic. Until that pass is implemented,
  missing-member validation remains an acknowledged gap in the refactor.

Verification:

- A concrete member result retains the declaration and the correct override.
- Provider access forces a later written definition and returns its value.
- Synthetic values can be demanded before their owner has otherwise been visited.
- Trait declarations with no value cannot be mistaken for providers.
- Existing abstract lookup, ambiguity, and missing-trait diagnostics still pass.

**Review boundary:** inspect the identity model and the demand/accessor contract.
The concrete qualified-path test may remain ignored here: traversal and reduction
arrive together in checkpoint 2.

## Checkpoint 2 — Concrete normalization, eager integration, and cycles

Implemented and verified:

- New `tir/normalize.rs` provides `normalize_head` and `normalize_type` on
  `TypeContext`. Concrete projections select a provider using the trait
  declaration index and reduce its stored value. Abstract and inference
  projections remain intact. Substitution stays structurally separate.
- Deep traversal handles tuples, function types, struct/function-item arguments,
  pointer/slice/array element and memory types. Head traversal stops at the
  exposed constructor; neither traversal expands nominal definitions.
- A builder-owned active projection stack survives re-entrant signature queries.
  Exact cycles receive `CyclicAssociatedType`; a depth cap receives
  `TypeNormalizationOverflow`. Both unwind and recover with `TypeIndex::ERROR`.
- Written impl RHS values and synthetic memory/global values normalize before
  their signature queries finish. Qualified, grouped, and ordinary type-member
  paths normalize concrete projections and avoid dependent missing-member errors.
- Missing impl members still recover without diagnostics; the future conformance
  pass owns reporting. No global associated-type validation sweep was added.
- Regression coverage includes forward references, chains, compound types,
  synthetic owners, unused direct/mutual cycles, completed stored-value cycles,
  abstract/inference projections, sibling reuse, and error/depth recovery.
- `cargo test -p wx-compiler --lib tir::`: 256 passed, 0 ignored.

**Deliverable:** concrete associated-type projections work throughout the supported
type forms, with both signature and normalization cycle handling.

Primary files: new `normalize.rs`, `mod.rs`, `signatures.rs`, `members.rs`, and
diagnostics as needed.

Work:

- Add both public entry points and one shared projection-reduction routine.
- Reduce concrete receivers using existing dispatch and checkpoint 1's provider
  accessor. Retain valid abstract projections for which no equality is available.
- Implement deep traversal across tuples, function parameters/results, struct and
  function-item arguments, pointer/slice/array element and memory types, and
  projection receivers. Preserve nominal identity, sizes, and ownership flags.
- Add the active-projection stack and a recursion limit. Keep the original
  projection active until normalization of its resulting type finishes. Handle
  both exact repetition and expansion that grows without repeating a key.
- Normalize impl-associated RHS types before their signature query leaves
  `InProgress`. Apply the same value contract to synthetic providers.
- Route qualified and ordinary type-member accesses through normalization;
  normalize a receiver sufficiently before looking up the next path segment.
- Preserve existing diagnostic ownership. Do not turn an error receiver into a
  second misleading "member not found" error.
- Enable `qualified_path_resolves_a_concrete_impls_associated_type` by reducing
  the declaration-based projection constructed in step 1.

Verification:

- Qualified, ordinary, and grouped concrete accesses, including forward references.
- Concrete chains and projections nested in compound types.
- Head normalization stops at the exposed constructor; deep normalization visits
  its contents. Neither follows a struct's fields.
- Direct and mutual RHS cycles, including unused associated-type definitions.
- Cycles involving completed stored projection values, tested at the normalization
  layer without relying on generic source support that has not returned yet.
- Repeated sibling projections are accepted; errors leave the stack clean.
- Synthetic memory/global values, abstract projections, error recovery, and depth
  overflow. Use a small internal test limit where practical instead of a huge test.

**Review boundary:** inspect the complete concrete slice, its diagnostics, and the
two entry-point contracts. No global associated-type validation sweep is added.

## Checkpoint 3 — Generic impl matching and normalization after substitution

Implemented and verified:

- Written impl target arguments resolve in the impl's own parameter frame.
  Dispatch still discovers candidates by outer constructor, then full
  structural matching infers every impl argument and checks repeated uses.
- Matching checks inferred arguments against trait bounds and rejects
  undetermined arguments. Associated-type equality and nested binding
  requirements are not assumed satisfied; those await checkpoint 4.
- Provider values are instantiated with `types.rs` substitution and normalized
  again. Active projection frames catch cycles that arise only after a concrete
  instantiation. Synthetic memory/global impls retain lazy owner queries.
- Generic inherent targets are also matched before unqualified member lookup
  can let an unrelated inherent member shadow a trait member.
- Bound checking uses the resolved dispatch candidate and inferred target
  arguments without a separate trait-obligation stack. Bare-parameter impl
  targets and blanket impls remain outside the language design.
- `cargo test -p wx-compiler --lib`: 414 passed, 0 ignored (including 263
  active TIR tests).

**Deliverable:** normalization selects and instantiates generic impl providers;
cycles that appear only for particular arguments are diagnosed.

Primary files: `impls.rs`, `signatures.rs`, `normalize.rs`, `satisfaction.rs` and
the member-selection plumbing. Reuse substitution from `types.rs`.

Work:

- Resolve written generic impl target arguments against the impl's own parameter
  frame, replacing the current `resolve_impl_target` TODO for the supported forms.
- Keep dispatch buckets as candidate discovery. Match the full target structure
  against the receiver and return the selected impl with its inferred arguments.
- Respect parameter ownership, repeated target parameters, and the distinction
  between impl parameters and parameters from other frames. Reject invalid or
  undetermined matches rather than inventing arguments.
- Enforce the applicable declared bounds using the current satisfaction machinery;
  use normalized types where required. Candidate discovery alone does not
  establish that a generic impl's own bounds hold; check its inferred arguments
  without introducing a separate trait-obligation stack.
  Equality-specific applicability checking remains deferred; unsupported cases
  must remain explicit rather than being silently treated as satisfied.
- Keep the current one-trait-impl-per-outer-constructor restriction. This work does
  not introduce specialization, overlap selection, or arbitrary inference.
- Instantiate a provider's generic value and normalize it again. Track the full
  instantiated projection, not just the associated definition's identity.
- Keep bounds used while resolving a generic provider separate from the caller's
  concrete substitutions; constructing an instantiation does not mutate its
  declaration environment.

Verification:

- `impl<T> Container for Wrapper<T> { type Item = T; }` projects correctly for
  different arguments, and nested target arguments are matched structurally.
- Mismatching targets, repeated-parameter mismatches, and unsatisfied bounds are
  rejected. An impl's parameter zero does not replace another frame's parameter.
- Port the discussed `Project`/`Source` example to supported wx syntax: the same
  generic definition terminates through `Wrap<Finite>` and cycles through
  `Wrap<Cycle>`. The unused abstract definition itself is accepted.
- Forward references and finite nested generic reductions continue to work.

**Review boundary:** inspect selection and the substitution boundary together.
This is one substantial chunk because implementing matching without integrating
its results would leave the core correctness questions untested.

## Checkpoint 4 — Normalization from available bound facts

Implemented and verified. Scope was narrowed by agreement: consume assumed
facts for normalization; do not add trait conformance, equality satisfaction,
a semantic comparison pass, or deferred trait obligations.

Delivered:

- Bounds use two AST walks within signature resolution. The first publishes
  direct memberships for all sibling parameters in the existing effective-bound
  representation. Inherited memberships are expanded before RHS resolution only
  when a valid equality expression needs them. The second builds completed,
  immutable source bounds. There is no separate collected-bound tree or merger
  input abstraction.
- The source arena reserves only a trait identity and source span before completing
  an occurrence. Both AST walks use the same accepted preorder; span matching
  skips invalid occurrences without repeating diagnostics, and an assertion checks
  that the reserved range is consumed. Signature demands may append other source
  bounds without changing these identities. Construction state stays in the arena;
  source requirements have only Equals and Bound variants.
- Equality collection records the symbolic resolved RHS without reducing its final
  value or checking it against associated declaration bounds. Compound children
  also retain projections. resolve_type_expression resolves structure; resolve_type
  explicitly normalizes its result for signature consumers. Member lookup may
  normalize a receiver when needed to discover a member. Future conformance
  checking owns associated-value validation. The existing specialized memory-size
  check remains in place.
- Merged equality facts retain source provenance separately from their interpreted
  type value. Inherited values substitute the declaring trait's Self using the
  structural substitution already implemented in types.rs.
- A concrete EffectiveBounds cursor reads parameter facts, associated declaration
  facts, and nested constraints on a projected receiver. BoundView exposes the
  borrowed bound and an optional named SelfSubstitution context. Consumers use
  ordinary loops; there are no visitor callbacks or dynamic dispatch. Bound trees
  are neither flattened nor cloned. Parameter and single-projection traversal
  needs no heap storage; deeper paths use the existing SmallVec for descriptors.
  Readiness is computed for the whole path before iteration. Declaration facts
  substitute Self for the receiver; normalization and abstract member/membership
  readers share these facts.
- Direct, inherited, nested, and reciprocal equalities reduce abstract projections.
  Relative-path receivers retain their original projection until subsequent
  member lookup has consumed receiver-specific facts.
- Tautological and circular abstract equality expansions preserve the projection.
  The existing active normalization stack rolls back a blocked assumed-equality
  chain; concrete definition cycles and the accepted work limit remain enforced.
- Competing symbolic equalities remain unavailable for reduction. Existing bound
  conflict diagnostics apply only when incompatible outer constructors establish
  a conflict. General semantic equality/conflict validation remains deferred.
- Generic impl equality/nested-bound applicability checks remain unsupported and
  fail closed as in checkpoint 3. This checkpoint does not turn assumptions into
  a new proof mechanism.

Verification:

- 20 new tests cover direct/chained reductions, inherited and nested Self
  substitution, contextual agreement, declaration facts, retained nested facts,
  sibling forward references, reciprocal integer bounds, abstract cycles,
  ambiguous equalities, deferred conformance, readiness without stale caching,
  multiple nested projection sources retaining their declaring Self context,
  symbolic source equalities in compound types, and reservation stability across
  invalid occurrences and re-entrant signature demands.
- All 434 compiler library tests pass, including the existing concrete cycle,
  depth-limit, missing-provider recovery, and bound-conflict regressions.
- rustfmt checks for the six edited Rust files and git diff --check pass.

Review entry points: bounds.rs (EqualityFact, effective-bound traversal,
projection_equality), signatures.rs (two AST walks, symbolic type-expression
resolution, and relative-path receiver resolution), normalize.rs (assumed reduction
and blocked-chain recovery).
Member lookup and existing abstract membership checks use the shared reader.

## Checkpoint 5 — Consumer audit, allocation verification, and completion

**Deliverable:** the agreed normalization scope is integrated consistently, with
combined regression coverage and measured allocation behavior.

Work:

- Audit active consumers that inspect a type constructor, perform impl dispatch,
  or compare types. Route applicable operations through head/deep normalization;
  preserve structural interner equality for genuinely structural questions.
- Verify that symbolic types remain legal in stored signatures. No consumer may
  assume all `TypeIndex` values are concrete because eager normalization ran once.
- Exercise normalization while signatures are pending and after dependencies are
  resolved, including re-entrant signature/provider demands and mixed cycles.
- Recheck diagnostic spans, one-error recovery behavior, declaration ordering,
  and state cleanup across independent requests.
- Measure unchanged traversal, fixed-field types, changed child lists, and reuse
  of already-interned results. Distinguish necessary output storage and stack
  capacity growth from avoidable temporary allocations. Interner length alone is
  not an allocation measurement.
- Reuse stack capacity, avoid eager slice clones, and make any further optimization
  only where the measurements justify its complexity.
- Update affected API comments and this plan with delivered behavior and remaining
  unsupported language features. Do not describe disabled legacy code as active.

**Review boundary:** a final bounded integration/performance review. Earlier
checkpoints already contain their own correctness tests; this is not where cycle
handling, provider errors, or basic safety are first added.

## Verification and scope boundaries

For each implementation checkpoint, run focused tests followed by the active
surface `cargo test -p wx-compiler --lib tir::`, formatting checks for edited Rust
files, and `git diff --check`. Record actual counts at each handoff. Do not chase
disabled pipeline/workspace failures or unrelated clippy warnings during this
refactor. Preserve unrelated working-tree edits.

The plan does not restore the old builder, MIR, codegen, or body checker. It does
not add associated-type defaults, inherent associated types, generic associated
types, specialization, or a general inference/constraint solver. Existing ordinary
alias expansion remains where it is unless a demonstrated dependency requires a
targeted change. Layout validation stays separate from type normalization.

If a later active phase needs normalization over completed registries, extract the
necessary context at that point while retaining these entry-point semantics. Do
not build an unused provider trait or refactor the whole builder merely to prepare
for that hypothetical caller.

## Progress

- [x] Structural substitution prerequisite in `types.rs`.
- [x] 1. Associated-type identity and provider access.
- [x] 2. Concrete normalization, eager integration, and cycles.
- [x] 3. Generic impl matching and normalization after substitution.
- [x] 4. Normalization from available bound facts (narrowed scope).
- [ ] 5. Consumer audit, allocation verification, and completion.
