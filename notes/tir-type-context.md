# TIR `TypeContext`: ownership model and body-checking entry

Status as of 2026-10-11, branch `tir-refactor`. Replaces
`tir-phase2-signatures-handoff.md` and `tir-body-checking-handoff.md`, both
written for a model (build a `SignatureBuilder`, freeze it into a
`SignatureRegistry`) that no longer exists.

## Ownership model

- **`TypeContext<'ast, 'ctx, 'dispatch>`** (`tir/signatures.rs`) is the one
  object that owns semantic type state: `types`, `bounds`, `type_envs`,
  `param_bounds`, the per-kind signature tables, `query_state`, `query_stack`,
  `obligations`, `normalization`, and `exports`. It is never frozen or
  converted into a second type. Later stages keep interning into it.
- **Inputs are borrowed**, not owned: `defs`, `strings`, `ast_nodes`,
  `impl_dispatch` (built before the sweep, never mutated by it) and the
  diagnostics sink. The driver owns them and creates the context inside that
  scope. No `Arc`/`Rc`, no `unsafe`, no leaking.
- **`sweep()`** forces `ensure_signature` for every registered declaration,
  resolves the export block, and debug-asserts that every query is `Resolved`
  and every obligation drained. It is a checkpoint, not a freeze: the context
  stays live and mutable afterwards.
- **Body checking** will use a per-function `FunctionContext` holding
  `&mut TypeContext` plus per-body state (locals, scopes, labels, expected
  types, inference). It does not exist yet. A body's own obligations should
  live in the `FunctionContext`, so one failing body cannot poison another.
- The proof and normalization methods (`check_trait`, `find_trait_impl_query`,
  `normalize_*`, `resolve_type_member`, `resolve_trait_qualified_member`)
  already live on `TypeContext`; nothing needs porting to use them from a body.
- Per-item state is keyed by `DefId`, so selective invalidation could be added
  later. Incremental compilation is deliberately not a goal yet.

### Tests

`signatures.rs` tests keep the inputs on their own stack:
`test_case!(case = "source")` (also `mut case`, and `case from <graph>`)
declares the graph, `TestInputs`, and a swept `TestCase` as three locals.
`checked_case!` additionally asserts a clean parse and link. Read state through
`case.context.<field>`. `satisfaction.rs` uses a closure (`with_resolved`)
that hands out the live `&mut TypeContext`.

The embedded stdlib sweeps with zero diagnostics (checked 2026-10-11; no
committed test covers it yet).

## Entering a body

- A function's scope comes from `FunctionSignature::assumption_context()`, a
  handle derived from its `type_params`. A method without its own parameters
  keeps its enclosing Self scope; a parameterless free function uses the root.
  Method generics inherit the impl's Self frame, then its generic parameters.
- A normalized parameter's *owner* is not necessarily the body's context:
  `fn scoped<U: Container where { Item = T } + Container where { Item: Marker }>(self, x: U::Item)`
  stores `x: T`, but the body also has the local facts `U::Item = T` and
  `U::Item: Marker`. Always start from the function's context, not from the
  type's declaring frame. Sibling methods never see each other's facts.
- Facts are read with the borrowed reader, which lends fact storage and the
  interner separately (forming projected subjects may intern):

  ```rust
  let cx = tcx.functions[usize::from(function_index)].assumption_context();
  let (reader, types) = tcx.assumptions();
  let mut facts = reader.scoped_facts(cx, types);
  while let Some(fact) = facts.next(types) { /* trait memberships, equalities */ }
  ```

  `scoped_facts` walks finite written parameter trees and lexical parents, skips
  Self frames that merely name an existing type, and gives a trait's abstract
  Self an implicit membership in that trait plus its written supertraits.
  `subject_facts(subject, types, remaining_depth)` adds associated-declaration
  bounds along a projection path; pass the operation's remaining budget. Such
  facts may carry a `SelfSubstitution`: instantiate the borrowed equality RHS
  with its recorded environment and the receiver before comparing, never with the
  declaration's literal Self.
- Normalization keeps symbolic source terms: a stored `Need<i32>` may stem from
  `T::Item = Need<U::Item>`. Both identities matter when matching subjects.
  Ambiguous or conflicting equalities keep their distinct representations.
- Constants require an explicit annotation (E2105 otherwise, stored as
  `TypeIndex::ERROR`). Free constants resolve in the root type scope and their
  own namespace; impl constants in the impl's `self_scope`. Initializers should
  be checked in the same scope. Signature construction does not evaluate them.
- Exports: collected only for the selected crate regardless of package kind,
  validated after the sweep against the value namespace only. Dependency export
  blocks are ignored; duplicate names keep the first entry.

## Pending results

| Consumer | `Pending` handling |
| --- | --- |
| Generic or associated-value bound validation | Queue `Obligation::Bounds` |
| Qualified member applicability | Form the known projection, queue `Obligation::Trait` |
| Signature normalization | Keep the symbolic term, queue `Obligation::Normalize` |
| Unqualified declaration selection | Report E2104, suggest trait qualification |
| Assumption proof and impl matching | Propagate `Pending`; never treat it as a negative proof |

A recursion-budget overflow is a diagnosed `Failed` result: it must not queue a
retry or silently produce an error type, and it poisons only the active
normalization. After the sweep a stalled queue is an internal invariant failure;
an obligation raised later by a body is that body's own concern.

## Known gaps

- Impl conformance (`check_trait_conformance`): not implemented.
- Deferred unqualified name selection (reports E2104 instead), a general
  symbolic equality solver, and proof of impl associated equalities and nested
  requirements.
- Remaining `todo!()`s: generic args on a type-relative path segment (two
  sites), the fallback arm of type-expression resolution, and naming some item
  kinds in diagnostics.
- Body checking, `FunctionContext`, the `TIR` struct and `TIR::build`, and
  everything downstream (`mir`, `opt`, `codegen`, `wasm`, plus `wx-fmt`,
  `wx-lsp`, `wx-cli`) are disabled or not compiling; see `CLAUDE.md`.

## Open design decisions

1. **Arena AST with ids** in place of the boxed tree. It would remove
   `AstEntry`/`AstNodeRef` (a duplicate of `DefKind` plus a reference) and
   let defs records hold item/expression ids directly. It does not by itself
   remove the borrow `TypeContext` has on its inputs.
2. **Body output shape**: does the checker keep producing a TIR tree (as the
   old `tir/builder/*` did, which MIR was written against), or side tables
   keyed by expression id over the AST arena? Decide before writing the body
   checker, and before the arena refactor.
3. If sweep order is ever changed to iterate per-kind vectors, keep a single
   definition-order list: that order drives diagnostic order and `TypeIndex`
   numbering in snapshots.

## Conventions worth keeping

- **Recovery values over `Option`/`Result` plumbing**: a failed piece becomes
  `TypeIndex::ERROR`, not a hole every consumer must handle.
- **Cycle spans are attached at call time** (`QueryInfo::requested_at`), never
  mutated onto a frame afterwards. A query that already reported its cycle needs
  its own state, not a side table of "reported" ids.
- **Add generality only with a second real consumer**; don't add a speculative
  variant ahead of demand.
- **Test lookups go through real path resolution** (`TestCase::resolve`), never a
  scan by name over an arena, and never assume index 0 is the first item you
  declared: stdlib items can occupy earlier indices.
- **Check diagnostic codes against existing ones, and against what rustc does**,
  before minting a new code.
