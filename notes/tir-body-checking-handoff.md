# Assumptions at the body-checking boundary

Checkpoint 5 verifies the data handoff from signature construction. Function
bodies, impl conformance, and production compiler
wiring remain separate work. Trait-impl method and constant signatures are now
resolved by the existing declaration queries. Free constants also resolve their
required annotations. Enum paths construct nominal types from definition
identities without forcing representation queries; enum declarations still
validate their representation during the sweep. Export blocks are collected only
for the selected crate, regardless of package kind, and validated after the sweep.
Multiple root blocks share one map keyed by decoded external symbols. Duplicate
names retain the first source entry; dependency export blocks are ignored and do
not create namespace bindings. The definition registry owns this single export map alongside imports.
Signature construction borrows it to validate export eligibility using only
the value namespace. Type-only names report a missing value; memories and other
items in both namespaces resolve through their value binding. Validation reports
ineligible targets without allocating another map or filtering out entries.

String expressions carry decoded `SymbolU32` values (`ast::Expression::String`),
and import external names and attribute strings carry decoded spanned symbols.
The parser owns decoding, diagnostics, and interning for every string context.
Consumers use those symbols directly; original source spans retain literal spelling.

## Entering a body

Use the function's stored lexical scope, through
`FunctionSignature::assumption_context()`. This derives a small handle from the
existing `type_params` field; it stores no second context or validity state.
A method without its own parameters retains its enclosing Self scope. A free
function without parameters uses the root scope. Trait and inherent methods share
this scope construction: method generics inherit the impl's Self frame and then
its generic parameters. An implicit receiver uses that frame's existing Self type.

Free and impl constants require an explicit type annotation; a missing annotation
reports E2105 and stores `TypeIndex::ERROR`. Free constants resolve in the root type scope
and their own namespace; impl constants resolve in the enclosing impl's
`self_scope`. Both use associated-type normalization and bound checks. Use the
same declaration scope when checking their initializers. Signature construction
does not evaluate initializers or verify that impl members match trait declarations.

A normalized parameter's owner is not necessarily the body's context. For example:

```text
impl<T: Outer> Host<T> {
    fn scoped<U: Container where { Item = T }
        + Container where { Item: Marker }>(self, x: U::Item) {}
}
```

The stored type of `x` is the outer `T`, but the method's context also contains the
local `U::Item = T` and `U::Item: Marker` facts. Starting at `T`'s declaring frame
would lose those local guarantees. The sibling method cannot use them.

The finished registry lends its facts and interner independently:

```rust
let cx = signatures.functions[usize::from(function_index)].assumption_context();
let (reader, types) = signatures.assumptions();
let mut facts = reader.scoped_facts(cx, types);
while let Some(fact) = facts.next(types) {
    // Memberships have explicit subjects. Equalities retain source provenance.
}
```

This uses the same borrowed reader as signature construction. It does not clone
bound trees or retain a query cache. Forming projected subject identities may
intern types, so the reader accepts the mutable interner separately.

## What survives construction

`SignatureRegistry` owns `TypeEnvArena`, parameter bounds, associated declaration
and provider signatures, `BoundArena`, `TypeInterner`, and impl dispatch. Context
handles, lexical parents, original parameter identities, `BoundId`/`BindingRef`
provenance, and source spans remain usable after the builder is consumed.

`scoped_facts(cx, types)` visits finite written parameter trees and lexical
parents. It skips Self frames that only bind a name to an existing type. A trait's
own abstract Self instead contributes implicit membership in that trait, plus its
written supertraits. Siblings never become assumption sources.

`subject_facts(subject, types, remaining_depth)` adds associated declaration
bounds along a requested projection path. Supply the semantic operation's
remaining budget. These facts can carry `SelfSubstitution`: instantiate their
borrowed equality RHS with its recorded environment and receiver before comparing
it. Do not treat the declaration's literal Self as the caller's receiver, or
recursively expand every associated declaration into new subjects.

Successful normalization changes signature types but preserves symbolic source
terms. A stored `Need<i32>` may correspond to the source equality
`T::Item = Need<U::Item>`. Both identities matter when finding equivalent subjects.
Ambiguous or conflicting equalities retain their distinct representations.
Failed deferred checks repair affected types and the owning declaration's
assumptions; they do not modify enclosing declarations' facts.

## Completion and query results

During construction, `SignatureStatus::Available` exposes structural data and may
still own deferred checks. It does not mean those checks have completed.
The declaration sweep requests every AST entry and resumes deferred checks on
queries previously forced during recursive construction. No final retry pass is
needed. The finished registry's query-to-location projection requires `Resolved`
entries; debug checks verify empty owner chains and that no live obligation
payload is discarded.
The obligation arena and query states do not survive the builder.

Reachable semantic fact tables are ready at this boundary, including recovery
after diagnosed errors. Unused name-rebinding placeholder rows are ignored by the
reader. Completion is not a claim that a declaration was valid: diagnostics and
`TypeIndex::ERROR` represent failure. A ready abstract projection is a usable
symbolic type; it does not indicate unfinished work.

During construction, every genuine `Pending` semantic result either propagates
through its query caller or is handled by the current signature owner:

| Consumer | Pending handling |
| --- | --- |
| Generic or associated-value bound validation | Queue `Obligation::Bounds` against the eventual requirement table |
| Qualified member applicability | Form the known projection and queue `Obligation::Trait` |
| Signature normalization | Retain the symbolic term and queue `Obligation::Normalize` |
| Unqualified declaration selection | Report E2104 and suggest trait qualification |
| Assumption proof and impl matching | Propagate `Pending`; do not turn it into a negative proof |

Retries reuse arena slots. A stalled queue after all construction dependencies
complete is an internal invariant failure. A recursion-budget overflow is instead
a diagnosed `Failed` result; it must not queue another retry or silently return an
error type. Overflow reporting poisons an active normalization only, so later
independent semantic queries can proceed.

## Semantic operations for the body checker

Reuse the existing rules for:

- `check_trait` / `find_trait_impl_query`: contextual membership and provider
  selection. Candidate requirements use the caller's assumptions.
- `normalize_head_query` / `normalize_type_query`: projection reduction and
  normalization through compound types. A provider value is resolved in its
  definition context, substituted, then reduced in the caller context.
- `normalize_assumed_type_query`: comparing evidence through known equalities
  without recursive impl dispatch.
- `resolve_type_member` / `resolve_trait_qualified_member`: member declaration
  identity, direct-bound lookup, inherent precedence, and ambiguity. Associated
  projections name trait declarations; provider slots supply their values.

These proof and normalization methods currently belong to `SignatureBuilder`.
They are not callable on the finished registry yet. When implementing body
checking, adapt these operations to the body checker using the completed registry
and the shared reader. Do not recreate the signature builder, its deferred work,
or another declaration query system. This checkpoint establishes the retained
data and scope contract; it does not introduce a speculative provider abstraction.

The retained limits are deferred unqualified name selection, a general symbolic
equality solver, proof of impl associated equalities/nested requirements, and impl
conformance. Tests in `finished_signature_handoff` demonstrate the completed
registry reads, local scope isolation, contextual Self, symbolic source retention,
and failure/completion boundaries.

A full real-stdlib signature sweep now completes without unimplemented-item
panics, but still reports unresolved generic/Self memory tags (`Mem`, `DstMem`,
`SrcMem`, `Self`). `resolve_memory_tag` currently uses namespace-only path lookup
rather than the annotation's lexical type scope. This is separate from free
constant annotations and nominal enum type resolution and remains pending.
