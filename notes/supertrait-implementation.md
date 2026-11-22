Implementation update: piece D now uses shared member lookup through the transitive trait graph. Methods, constants, and associated types retain the declaring trait; diamonds are deduplicated and distinct declarations are ambiguous. Qualified paths use transitive bound satisfaction while remaining restricted to the explicitly named trait. The implementation uses a shared traversal, not a stored closure. See `notes/item-resolution-granularity-plan.md` for the member-demand and memory-synthesis changes. The original design discussion follows.

Not a hard block — but it's the right thing to do first, for three reasons.

## Why supertraits first

**1. It's a shared primitive.** The whole thing funnels through one function, `type_implements_trait` (`mod.rs:3747`), whose both branches say *"No supertrait transitivity."* That function is the choke point for:
- `check_assoc_type_bounds` (`Elem: Display` satisfied by `impl Debug for X` where `Debug: Display`)
- method-generic bound-compat (impl loosening `A: Ord` to `C: PartialOrd`)
- call-site / impl-target bound checks (`type_args_satisfy_bounds`)
- the two `#[ignore]`d `test_supertrait_*_satisfies_bound` tests

Build `supertrait_closure` once and all of those improve. Build the bound checks first and each either grows a throwaway partial walk or ships with a documented supertrait gap.

**2. It fixes accept-good-code, not just reject-bad-code.** "Can't call a parent-trait method from a child trait" is a language hole users hit now. Bound-checking is about rejecting more bad code — lower urgency.

**3. Compiler robustness.** `trait A: B {} trait B: A {}` isn't cycle-checked anywhere — per the code comments, the `ensure_signature` re-entrancy guard never even sees supertrait resolution.

## Current state

**Updated 2026-09-07: A, B and C have landed. Only D is left.**

Supertraits are stored as bounds on the trait's own `Self` type param — there is no
`Trait::bounds` field any more — and `Trait::supertraits(self_index)` reads them back by
filtering the reflexive `Self: ThisTrait` entry. `ensure_trait_supertraits` resolves the
clause and nothing else, recursing up the parent chain, so reading any trait's `Self` bounds
guarantees its ancestors' are resolved too. `ItemRegistry::trait_implies` walks that graph
transitively (visited-guarded) and `type_implements_trait` asks it, so `T: B` satisfies `A`
when `B: A` — B and C, in one function each rather than a stored closure.

Cycles are reported as E1082 (`CyclicSupertrait`), naming the whole loop. Not through
`sig_state` as piece A sketched: a trait resolving only its clause is deliberately never
`InProgress`, so the walk carries its own path instead — see `resolve_supertrait_clause`.

Missing: **name resolution through the chain** (piece D). `self.grandparent_method()`,
`T::parent_method()` and `T::ParentAssoc` still fail two levels up.

## What "supertrait resolution" is — 4 mostly-independent pieces

|       | Piece                                                                                                                                                                                  | Size                                   | Unblocks                                                                                      |
| ----- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------- | --------------------------------------------------------------------------------------------- |
| **A** | Cycle detection — `ensure_signature`'s `Trait` arm force-resolves each supertrait's signature so `sig_state`'s `InProgress` catches `A: B: A` → E0391 (fix sketch in `tests.rs:11695`) | small                                  | correctness; prereq for B                                                                     |
| **B** | `supertrait_closure(TraitIndex) -> [TraitBound]` — transitive set (carrying `where`-bindings), walk+visited or stored at signature time                                                | small                                  | everything below                                                                              |
| **C** | `type_implements_trait` transitivity — if the direct check fails, check whether an applicable trait's closure covers the needed one                                                    | small (one fn)                         | assoc-type bounds, method-bound-compat, call-site bounds; un-ignores the 2 transitivity tests |
| **D** | Name resolution through supertraits — `self.parent_method()` / `Self::PARENT_CONST` / `T::parent_method()` fall through to the closure; ambiguity on duplicate names is an error       | medium (touches `resolve_impl_member`) | the "can't call parent method" bug                                                            |

## Recommendation

Do **A → B → C** first — small, and it's the exact chain that (a) makes both comparator bound-checks *correct* instead of approximate, (b) un-ignores the two transitivity tests, (c) closes the cycle hole. Then **D** as the standalone user-facing fix. Then return to the comparator for assoc-type bound checking + method-generic bound-compat with `supertrait_closure` already in hand.

**A → C are done.** Sequence D together with step 2 of
`notes/item-resolution-granularity-plan.md`: D has to edit all six member-lookup sites
anyway, and routing them through one helper while it does turns that plan's step 4 from a
six-site change into a one-function change. The decision D forces: a name declared by both a
trait and its supertrait must report **ambiguous**, not silently pick one.