# Rule: one trait impl per type constructor

**Status:** DONE. 636 tests passing (634 pre-existing + 2 new; one existing test rewritten).

## What actually landed

- `trait_impl_dispatch` changed to `HashMap<ImplTarget, Vec<(TraitIndex, TraitImplIndex)>>`
  as planned. `find_trait_impl` (`tir/mod.rs`) now does a direct `.find()` on the tuple slice
  instead of a `.find_map()` that re-derived `trait_index` via `trait_impls[idx].trait_index`.
- New `DuplicateTraitImpl` diagnostic, `E1061` (next free code after `NotAField` E1060).
- New `Builder::register_trait_impl` helper (`tir/builder.rs`, right after
  `record_abstract_dispatch_access`) — the single place that inserts into
  `trait_impl_dispatch`, used by both call sites (user-written `AstNodeRef::TraitImplBlock`
  and the synthetic per-`memory`-declaration `Memory`-trait impl). Confirmed via full-suite
  pass that the synthetic path has no collision risk in practice — no test anywhere writes an
  explicit `impl Memory for ...`, and each `memory` declaration gets a structurally unique
  `ImplTarget::Memory(DefId)` regardless.
- `resolve_impl_member`'s trait-scan loop simplified: iterates `&[(TraitIndex,
  TraitImplIndex)]` directly instead of re-deriving `trait_index` per candidate from
  `trait_impls[impl_index].trait_index` inside the loop body.
- One existing test rewritten: `test_generic_trait_impl_and_concrete_impl_ambiguous` (concrete
  `impl Getter for Box<i32>` + generic `impl<T> Getter for Box<T>`) now asserts
  `DuplicateTraitImpl` at declaration instead of `AmbiguousTraitMember` at the call site — its
  premise is exactly what the new rule bans outright.
- Two new tests added: `test_two_concrete_trait_impls_for_same_struct_is_duplicate` (two
  non-overlapping concrete impls, e.g. `Box<i32>`/`Box<u8>`, still conflict — proves the rule
  doesn't care whether receivers actually overlap) and
  `test_two_generic_trait_impls_for_same_struct_is_duplicate` (two impls with independently
  disjoint bounds, `impl<T: Foo>`/`impl<T: Bar>`, still conflict — proves the rule doesn't
  reason about bound overlap either).
- Confirmed via the full-suite run (no new failures beyond the one known case) that the
  regression scenarios in "New tests to add" below were already covered by existing tests:
  `test_two_trait_impls_with_colliding_method_name_is_ambiguous` (two different traits, same
  struct, same member name → still `AmbiguousTraitMember`, untouched) and
  `test_unused_trait_impl_eliminated_by_dce` (same trait, two different structs → still fine).

**Design discussion:** `notes/chatgpt-multiple-trait-implementations-per-target.md`.
**Related, explicitly out of scope here:** `notes/trait-dispatch-followups.md`'s
"cross-block inherent duplicates that are never called go undetected" item — the same
lazy-vs-eager gap exists for *inherent* impls today, and this plan does not touch it (see
Scope below).

## The rule

> A trait has at most one implementation per type constructor. Generic arguments do not
> participate in implementation selection — `impl Trait for Box<i32>` and
> `impl Trait for Box<u8>` both target the same constructor `Box` and therefore conflict,
> unconditionally, regardless of whether their receivers could ever actually overlap, and
> regardless of whether their bounds are disjoint (`impl<T: Foo> X for Box<T>` +
> `impl<T: Bar> X for Box<T>` are also illegal together).

This replaces the current model, where `trait_impl_dispatch` lets a bucket hold several impls
of the *same* trait, disambiguated per-call-site by `match_trait_impl`'s structural
unification (a concrete impl and a bounded generic impl for the same struct currently coexist
unless a specific receiver makes both apply, at which point `resolve_impl_member` reports
`AmbiguousTraitMember`, E1059).

## Why: honest cost/benefit (from the design discussion)

- **Logic simplification (the real motivator):** same-trait ambiguity between impls stops
  being a runtime question (unify against every candidate, compare, error on >1 matches) and
  becomes a structural impossibility, caught once at declaration instead of lazily at whatever
  call site happens to trigger it. This removes actual candidate-loop code, not just line
  count — `find_trait_impl`/`resolve_impl_member`'s trait scan go from "try N candidates" to
  "look up the one entry for this trait, if any."
- **Performance: real but minor, not the point.** Fewer candidates to probe shrinks
  `match_trait_impl` calls (and their per-candidate allocations) in the case where a
  constructor previously had multiple same-trait impls — but bucket sizes were already small,
  so this shaves an already-cheap constant. It does not touch the unrelated hot-path findings
  from the earlier perf review (`resolve_impl_member`'s `Vec` allocations for cross-trait
  ambiguity, etc.) — those are unaffected by this rule and stay open separately.
- **Cost:** genuine loss of per-instantiation specialization (e.g. a `Buffer<u8>` fast path
  vs `Buffer<T>`'s generic one) with no compile-time `match type(T)` escape hatch yet — the
  only escape hatch is distinct nominal wrapper types, which (per the SIMD API discussion) is
  often the *more* WASM-faithful design anyway, not just a workaround.

## Scope

**Trait impls only.** Inherent impl blocks keep their existing model — multiple inherent impl
blocks per type coexist fine as long as they don't define the same method name
(`inherent_impl_dispatch: HashMap<(ImplTarget, SymbolU32), Vec<InherentImplIndex>>`,
unaffected). That model was never in question in the design discussion.

**Detection timing: eager, at declaration.** A duplicate is rejected the moment the second
impl block is registered (Phase 2), independent of whether anything ever calls into either
one — a deliberate improvement over the *existing* lazy-detection pattern used for
inherent-impl collisions and the old trait-impl ambiguity check (both only fire when
`resolve_impl_member` is reached from a real call site). Inherent impls' lazy gap
(`trait-dispatch-followups.md`) is not fixed here.

## Data structure change

`trait_impl_dispatch` changes from:
```rust
pub trait_impl_dispatch: HashMap<ImplTarget, Vec<TraitImplIndex>>,
```
to:
```rust
pub trait_impl_dispatch: HashMap<ImplTarget, Vec<(TraitIndex, TraitImplIndex)>>,
```

Considered and rejected `HashMap<(ImplTarget, TraitIndex), TraitImplIndex>` (a flat tuple key,
single value): it would make `find_trait_impl`'s point lookup O(1) and the "at most one per
pair" invariant type-evident, but it can't serve `resolve_impl_member`'s trait-impl scan,
which enumerates *every* trait impl'd for a constructor without knowing the trait up front
(needed for the still-live, unrelated "two different traits, same member name" ambiguity
check, E1059). Introducing a second map to cover that would recreate the exact
two-maps-for-overlapping-purposes duplication rejected earlier in the original generic-trait-
impls work. Also considered a nested `HashMap<ImplTarget, HashMap<TraitIndex,
TraitImplIndex>>` — rejected as overkill for the actual bucket sizes involved (a handful of
traits per constructor at most), consistent with `trait-dispatch-followups.md`'s noted (not
yet acted on) observation that this codebase's small per-block member tables are already
`HashMap`s more by default than by necessity.

## Where enforcement goes

New helper `fn register_trait_impl(&mut self, target_type: TypeIndex, trait_index: TraitIndex, trait_impl_index: TraitImplIndex)`
in `tir/builder.rs`, replacing the three current call sites that push into
`trait_impl_dispatch` unconditionally:
1. `AstNodeRef::TraitImplBlock` handler (user-written trait impls).
2. The synthetic `Memory`-trait impl construction (`AstNodeRef::Memory` handling).

The helper: resolve `ImplTarget::from_type(target_type)`; look up the bucket; scan its
`Vec<(TraitIndex, TraitImplIndex)>` for an existing entry with this `trait_index`. If found,
emit `DuplicateTraitImpl` (new diagnostic code, next free after `NotAField` E1060 → **E1061**)
labeling both impls, and leave the new one unregistered (unreachable via dispatch, but its
`DefId` still exists and Phase 3 still type-checks its body normally — internal errors inside
a rejected duplicate are still reported). Otherwise push `(trait_index, trait_impl_index)`.

Message style, following the project's existing duplicate-definition wording (compare
inherent impl collisions: `"the name `{name}` is defined multiple times"`) and the
constructor-not-instantiation framing from the design discussion — deliberately does not
mention either impl's concrete type args:
```
error[E1061]: `{trait_name}` is already implemented for this type constructor
  --> second impl's trait-name span (primary): "duplicate implementation of `{trait_name}`"
  --> first impl's trait-name span (secondary): "first implementation here"
```

## What stays unaffected

- `match_trait_impl`'s bound/typeset checking — still essential per call site, since the sole
  impl for a constructor can still be a bounded generic, and a specific receiver's `T` might
  not satisfy the bound.
- `resolve_impl_member`'s candidate-collection loop and `AmbiguousTraitMember` (E1059) — still
  required, unchanged, for two *different* traits both providing a same-named member.
- `find_trait_impl`, `entry_has_body`, `record_abstract_dispatch_access` — orthogonal to how
  many impls exist per constructor; unaffected beyond the tuple-shape update.
- The `(entry, type_args)` owner-scheme branching (impl's own override vs. trait's bodied
  default) in `resolve_impl_member` — unchanged.

## Migration

1. Implement the data structure change, helper, and diagnostic.
2. Run `cargo test -p wx-compiler`; every test constructing two impls of the *same* trait for
   the *same* constructor (to exercise the old overlap-based ambiguity resolution) will fail
   and needs rewriting.
3. **Known certain case:** `test_generic_trait_impl_and_concrete_impl_ambiguous`
   (`tir/tests.rs`) — currently asserts `AmbiguousTraitMember` at the call site. Rewrite to
   assert `DuplicateTraitImpl` at the second `impl` declaration; its premise (concrete
   `impl Getter for Box<i32>` alongside generic `impl<T> Getter for Box<T>`) is exactly what
   this rule bans outright.
4. `tir/tests.rs` also has direct reads of `trait_impl_dispatch` (e.g. around the
   `test_generic_impl_block_registers_and_dispatches` area) that need updating for the new
   tuple element shape.
5. Full-suite run is the audit mechanism for everything else — don't pre-enumerate every
   affected test by grepping; let failures surface them.

## New tests to add

- Two concrete impls of the same trait for the same struct → `DuplicateTraitImpl` at the
  second declaration.
- Two generic impls of the same trait for the same struct → same error.
- Concrete + generic mix (the old ambiguous-overlap case) → `DuplicateTraitImpl`, not a
  call-site ambiguity.
- Regression: two *different* traits, same struct, same member name → still
  `AmbiguousTraitMember` at the call site.
- Regression: same trait, two *different* structs (existing
  `test_unused_trait_impl_eliminated_by_dce` shape) → still fine, different constructors.

## Explicitly not part of this change

- Inherent impl blocks keep their current per-method-name collision model.
- The lazy-detection gap for inherent-impl collisions is not fixed here.
- No compile-time `match type(T)` construct is introduced as a replacement for the
  specialization power being removed.
