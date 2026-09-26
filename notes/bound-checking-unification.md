# Bound-checking unification

Consolidates every "does this type satisfy these bounds?" check in the TIR
builder into one operation, `Builder::check_bounds` (`tir/builder/bounds.rs`).

## The problem

Bound checking — trait membership, typeset membership, and the
`where { Assoc = T }` / `where { Assoc: Bound }` refinements — was spread
across four code paths that had drifted apart:

| Path | Location | What it checked |
| --- | --- | --- |
| Call sites | `build_generic_call_arguments` (`calls.rs`) | trait + typeset membership; `: Bound` refinements in a deferred second pass; **not** `= Type` refinements, **not** nested `where` |
| Declaration validation | `check_bound_bindings` + `check_binding_typeset` (`validation.rs`) | the written refinements, recursively through `Bound` |
| Trait conformance | `check_assoc_type_bounds` (`generics.rs`) | an impl's associated-type *values* against the trait's declared bounds |
| Impl selection | `type_args_satisfy_bounds` (`tir/mod.rs`) | trait + typeset membership only; **ignored** every associated binding |

Consequences: `f<T: Has where { Item = u32 }>(x)` called with a `T` whose
`Item` is `bool` was not rejected. A generic impl
`impl<T: Has where { Item = u32 }> W<T>` was considered applicable to `W<u8>`
even when `u8::Item` was `bool`. Nested `where` on a `: Bound` at a call site
was silently skipped. Three regression tests (`tir/tests.rs`,
`test_*_binding_mismatch_*`) were added `#[ignore]`d to pin these before any
refactor.

## Design decisions

Reached by discussion before writing code:

- **Return `Vec<Diagnostic>`, not a structured `BoundFailure` enum.** The only
  consumer of a failure is the diagnostic renderer; a structured type would
  just be the diagnostic re-encoded. Callers that want a yes/no (impl
  selection) check `.is_empty()`.
- **No `Proof` / three-valued result.** "Can't prove / can't disprove" cases
  (poisoned input, too-abstract subject) simply emit nothing — same as
  "satisfied" — because every diagnostic caller wants silence there anyway.
  A poisoned input is handled by an early `subject == ERROR` return, and a
  bound whose parent trait membership fails short-circuits past its
  refinements.
- **Borrow only what's needed, not `&mut Builder`.** `check_bounds` mutates
  exactly one thing: the type interner (to materialise substituted types).
  A `&mut Builder` would make the borrow checker assume it can touch
  everything, forcing callers to clone `Bounds` and drop `self.items`
  borrows. So the work lives on two small structs:
  - **`TypeCtx<'a>`** (`type_ctx.rs`) — `{ &mut TypeInterner, &ItemRegistry,
    &mut StringInterner }`. `substitute_type` and `materialize_assoc_value`
    were relocated here; `Builder` keeps one-line delegating wrappers so the
    ~27 existing `substitute_type` callers are untouched.
  - **`BoundChecker<'a>`** (`bounds.rs`) — `{ TypeCtx, &ModuleGraph,
    &[PackageGraph] }`. This is the same disjoint-field reasoning the
    `Builder` struct's own doc comment already relies on. It's the trait-
    solver pattern in miniature: a read-only view of what's declared, plus
    owned mutable interning state.
- **`check_bounds` signature**: `(namespace, subject: Subject,
  required: &Bounds, origin: BoundOrigin, type_args: &[TypeIndex])`. Four axes
  that look alike but differ (`namespace`, `origin` and `type_args` — the
  three that are fixed for a whole traversal — travel together as a `Copy`
  `BoundSite`):
  - `origin` — *who* imposed the obligation (a `where` clause, a struct type
    param, a trait's `type Assoc: Bound` declaration). Names the "required by
    a bound in `X`" note. **Constant** through recursion.
  - `required` — the constraint set *at this level*. **Shrinks** as recursion
    descends into a nested `where`; those are borrowed sub-trees of the parent
    `Bounds` that no index names, which is why it's a parameter.
  - `subject` — the type that must satisfy `required` here. Its *type*
    **changes** each level (`T` → `T::Assoc` → …); its *place* does not, and
    it carries that place itself as a `SourceSpan` rather than pairing a span
    with a file id from somewhere else. A nested level's spans belong to the
    **callee's** `where` clause, so pairing one with the caller's file put the
    primary label at an offset past the end of the caller's source — a blank
    line, silently, since codespan clamps rather than fails. The primary label
    stays on the code whose author can act on it (the call); which nested
    constraint failed is what the "required by a bound in `X`" secondary says,
    in the file that holds it.
  - `type_args` — what *this site* pinned the declaring item's type
    parameters to. A `where { Assoc = U }` RHS is written in the callee's
    scope, so at a call site it has to be read through the call's inferred
    arguments before it means anything; checking it as written rejects a
    valid `f(0 as u8, true)` against
    `fn f<T: Has where { Item = U }, U>` with "`Item` is `bool`, expected
    `U`". Empty at a declaration site (the parameters are still abstract
    there, and the RHS *is* checked as written). **Constant** through
    recursion — every nested `where` was written in that same scope.
    A plain positional `substitute_type` suffices because `param_index` is
    absolute across the inherited-then-own chain, the same order
    `function_type_params_iter` yields, so an inherited impl parameter
    (`impl<T> W<T> { fn go<U: Has where { Item = T }>(..) }`) substitutes
    from the receiver with no extra machinery.
  `Self` in a `required` RHS resolves to the enclosing frame's subject —
  derived from `origin` at the top (`BoundOrigin` → `origin_self_ty`), then
  the parent subject deeper down. Never a caller parameter. It only applies
  to a `Self` that `type_args` did not already cover, so at a call site the
  substituted receiver wins over the declaration's abstract `Self`.
- **An abstract subject answers from its declared bounds.** A concrete
  subject's associated value comes from its impl; a type parameter has no
  impl, but its own bounds are the whole truth about it — `fn g<U: Has where
  { Item = bool }>` fixes `U::Item` for the whole of `g`. `check_inner` falls
  back to `ItemRegistry::declared_assoc_value` when
  `materialize_assoc_value` finds no impl, which is what lets a violation
  forwarded through a generic caller (`g` calling `f<T: Has where { Item =
  u32 }>`) be caught rather than silently accepted. Membership checks
  (`type_implements_trait`) already consulted that side; only the binding
  comparison did not.
- **An `expected` that is still abstract after substitution is not a
  violation.** A phantom type parameter (`U` named in the RHS but nowhere in
  the signature) can never be pinned down; that is already reported as
  un-inferrable, and comparing the unsubstituted `U` against a concrete
  actual would stack a bogus mismatch on top of it.
- **A written bound's own well-formedness is not a satisfaction question.**
  E1048 ("`where { A: <typeset> }` may not add a typeset the trait already
  declared for `A`") needs no subject and no substitution, so it lives in
  `validation.rs`'s `check_written_bounds`, walking written `where` clauses at
  each declaration. Inside `check_bounds` it fired again at every call site
  that passed through the bound — each copy pointing back at the same
  declaration, so they rendered as literal duplicates (one declaration + two
  calls gave three).
- **The `Equals` mismatch is not a "trait bound not satisfied".** The trait
  *is* implemented — `check_inner` reports and skips when it isn't — and only
  the binding disagrees, so it reads "the associated type binding
  `Item = u32` is not satisfied" with "`u8::Item` is `bool`, not `u32`" on the
  label. The code stays `E1063`.
- **Written nesting recurses; declaration edges are followed once.** Two
  kinds of step were tangled in one traversal: descending a written
  `where { .. where { .. } }` (finite — it is source text) and opening
  *another declaration's* bounds (unbounded — declarations can refer to each
  other). `check_declared_bounds` now follows the declaration edge exactly
  once and hands the rest to `check_written_bounds`, which structurally
  cannot open a declaration, so it terminates on a strict subterm every call.
  That removes the need for the `visited` set the "D cleanup" step backed
  away from, and it closes the gap where an obligation written *inside* a
  declared associated-type bound (`type A: Mid where { B: Deep where { C:
  Marker } }`) was checked nowhere. Not following the edge twice is also
  correct rather than merely convenient: a value written inside a declared
  bound is in trait scope, so whether it satisfies its own associated type's
  declaration belongs to that declaration, where `validate_declarations`
  already checks it.
- **Impl selection stays a separate, silent predicate.** It runs during
  dispatch (`&self` on `ItemRegistry`, no interner to mutate, no diagnostics),
  and it can be tried against several candidates. Sharing a traversal with the
  diagnostic path was deferred — no proven need.

## Implementation steps

- **A — extract `TypeCtx`.** Move `substitute_type` /
  `materialize_assoc_value` off `Builder`. Tests unchanged.
- **B — write `bounds.rs`.** `BoundChecker` + `check_bounds`, not wired to
  callers yet.
- **C — wire call sites.** `build_generic_call_arguments`'s ~250-line
  two-pass bound block replaced by a per-type-param `check_bounds` call.
  Un-ignored the two call-site regression tests.
- **D — migrate declaration validation + conformance.** `validate_declarations`
  walks each declaration site and calls `check_bounds`; conformance
  synthesises a `Bounds` from each impl's own associated-type values
  (`type Item = X` → one `Equals` binding) and checks the impl target against
  it, with `Self` = the target. Deleted `check_bound_bindings`,
  `check_binding_typeset`, `check_assoc_type_bounds`.
- **D cleanup — flatten the `Equals` arm.** The first cut of `check_bounds`
  had the `Equals` arm *recurse* into the associated type's declared bounds.
  That both duplicated conformance's work and could cycle on mutually-
  recursive trait declarations (`type X: B where { Y = Self }` /
  `type Y: A where { X = Self }`), which forced a `visited` set. Reverted to
  the old behaviour: a flat one-level `check_declared_bounds`. See "Recursion"
  below for why one level is correct, not a compromise.
- **E — impl selection.** `type_args_satisfy_bounds` now also checks each
  trait bound's `bindings` via `assoc_bindings_hold`, which reads the value
  **without interning** — a
  concrete impl's value directly, or a generic impl's bare-type-param value
  resolved from the inferred args; a composite generic value returns `None`
  and the binding is left unchecked here (`check_bounds` covers those where
  diagnostics are reported). Un-ignored the last regression test.

## Recursion: `Equals` flat, `Bound` recursive — both correct

These two arms of `check_inner` treat nesting differently on purpose.

- **`Equals` (`where { A = SomeType }`) is checked one level and stops.**
  `SomeType` is a concrete type; its own `impl`s already went through
  `check_trait_conformance`, which verified `SomeType`'s associated types
  against their bounds. At a *use* site we only need "does `SomeType`
  satisfy `A`'s declared bounds" plus the declared bounds' direct
  refinements — deeper obligations are checked at the definition site, by
  construction. Recursing here would re-do conformance's work (and cycle).

- **`Bound` (`where { A: X where { B: Y where { … } } }`) recurses per
  written nesting level.** Here `A` is not bound to a type — it's a chain of
  *projections* (`T::A`, `T::A::B`, …), none of which has a concrete impl
  that conformance checked. Each nested level is a fresh obligation on a
  fresh projection that only exists in this `where` clause. Flattening would
  silently drop the innermost check. The recursion only ever walks *written*
  `where` clauses (finite source), so it terminates and can't cycle.

## Final shape

```
Builder::check_bounds (bounds.rs)
  └─ BoundChecker { TypeCtx, &ModuleGraph, &[PackageGraph] }
       ├─ check_inner              — per trait bound: membership, then per binding
       │    ├─ Equals  → check_declared_bounds   (flat, one level)
       │    └─ Bound   → E1048 check + recurse check_inner over written nesting
       └─ report_missing_trait / report_equals_mismatch /
          report_missing_typeset / report_redundant_typeset_binding

ItemRegistry::type_args_satisfy_bounds (tir/mod.rs)   — impl selection, silent
  └─ assoc_bindings_hold                              — no interning
```

Callers: `calls.rs` (generic calls, free and method), `validation.rs`
(declaration sites + trait `type Assoc` declarations), `traits.rs`
(conformance).

Net: roughly **−1000 lines** of duplicated / interleaved checking in the TIR
builder, replaced by `bounds.rs` + `type_ctx.rs`. Diagnostic wording is close
enough to the old code that no snapshots changed; the only deliberate change
is "a `where` clause on `X`" → "a bound in `X`".

## Known limitations / follow-ups

Re-verified against the compiler after the bound-checking, conformance and
memory-seeding work; each one below reproduces today.

**Diagnostics**

- **A rejected impl candidate explains nothing.** `W<u8>.go()` against
  `impl<T: Has where { Item: Marker }> W<T>` reports `E1049: no method 'go'
  found for type 'W<u8>'` — correct, but never mentions that `u8::Item` is
  `bool` and `bool` is not `Marker`. When *every* candidate is rejected, the
  best one could be re-run through `check_bounds` to say why. This is the
  proven need that "impl selection stays a separate, silent predicate"
  deferred.
- **`Self` does not resolve in a trait impl's `where` clause.** It resolves in
  the trait *declaration* (`type Elem: X where { Y = Self }` works, and is
  tested), but the same clause on the impl's method gives `E1021: undeclared
  type`. An inconsistency in name resolution, not in bound checking.

**By design, for now**

- **Not a trait solver.** `check_bounds` verifies a fixed, shallow set. It
  does not chase associated-type obligations transitively to a fixpoint. This
  is correct for `Equals` (see above) and bounded for `Bound` (syntactic
  nesting only).
- **`Equals` comparison is `TypeIndex` equality**, not semantic equality
  through projection normalisation. A projection that *normalises* to the
  written type but has a different `TypeIndex` would read as a mismatch.
  Fixing this means integrating `type_compare`'s `TypeEnvArena` (a new env
  variant for function/alias type params) — deferred.
- **Impl selection treats a composite generic value as satisfied.**
  `impl<T> Has for Box<T> { type Item = Wrapper<T> }` under a
  `where { Item = … }` binding cannot be read during dispatch without
  building `Wrapper<u8>`, and a query must not grow the type arena — that
  would make dispatch depend on what happened to be interned already. The
  violation is still reported, by `check_bounds` at the call site; what is
  affected is only *which candidate is selected* when more than one could
  apply.

**Smaller leftovers**

- `check_inner` builds a `Bounds { traits: inner.traits.clone(), .. }` per
  nested `where` level, purely to satisfy a `&Bounds` parameter. A `Copy`
  `BoundsRef { traits: &[TraitBound], typeset: Option<TypesetBound> }` view
  removes the allocation and names the "a nested level carries no typeset"
  rule.
- `check_declared_bounds` still calls `substitute_type(rhs, &[self_ty])` — a
  positional substitution used as a `Self` substitution. It is owner-blind:
  any `TypeParam` at index 0 is replaced, whatever owns it. Safe today
  because a declared bound's RHS is written in trait scope, but the type does
  not say so.
- `Builder::type_ctx()` has one caller (`substitute_type`'s wrapper) and a
  doc describing a use that is not possible — it takes `&mut self`, so the
  callers that build a `TypeCtx` from fields cannot use it.
- `specialize_memory_member` assigns the memory's size to *every* associated
  type of the trait, regardless of name. Harmless while the trait has exactly
  one, and it is why "associated types depend on nothing" holds
  unconditionally during seeding — but it is not what the name promises.

## Tests

Three `#[ignore]`d regression tests (`tir/tests.rs`, "bound-consistency
matrix") for the original gaps, un-ignored as each step landed:
`test_assoc_equality_binding_mismatch_caught_at_free_call`,
`test_nested_assoc_binding_mismatch_caught_at_free_call`,
`test_assoc_binding_mismatch_caught_during_impl_selection`.

Plus five added for genuine coverage holes:
`test_deeply_nested_bound_binding_violation_caught_at_free_call` (guards the
`Bound` recursion — verified it fails if the recursion is removed),
`test_conformance_declared_self_binding_{violation,satisfied}` (the
`substitute_type(Self, …)` branch in `check_declared_bounds`),
`test_bound_kind_assoc_binding_at_impl_selection_{rejects,accepts}`.

Plus five for the `type_args` axis, after step C was found to reject valid
code (a call that satisfies `where { Item = U }` was compared against the
literal `U`): `test_assoc_equality_binding_rhs_reads_the_calls_type_args` and
`test_assoc_equality_binding_rhs_type_param_still_catches_mismatch` (the
accept/reject pair for a callee's own parameter),
`test_assoc_equality_binding_rhs_reads_an_inherited_type_param` and
`test_assoc_equality_binding_rhs_inherited_type_param_catches_mismatch` (the
same pair for one inherited from the impl block, which is what pins the
absolute-index claim), and
`test_uninferrable_binding_rhs_reports_only_the_inference_error`.

Plus two more, one per remaining diagnostic defect found in review:
`test_conflicting_typeset_bound_is_reported_once_not_per_call_site` (E1048
belongs to the declaration) and
`test_nested_bound_violation_labels_the_call_not_the_callees_span` (a
multi-file case that asserts every label's range lies inside its own file —
verified it fails against the old caller-file/callee-span pairing).

Baseline after: 1086 `wx-compiler` + 43 `wx-fmt` + 63 `wx-lsp`, clippy clean,
no snapshot changes.
