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

Supertraits are *parsed and stored* (`trait_def.bounds.traits`, direct only), and the direct-supertrait impl obligation works (`impl Drawable for Point` needs `impl Sized for Point` → E1034). Missing: transitivity, name resolution through them, cycle detection.

## What "supertrait resolution" is — 4 mostly-independent pieces

|       | Piece                                                                                                                                                                                  | Size                                   | Unblocks                                                                                      |
| ----- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------- | --------------------------------------------------------------------------------------------- |
| **A** | Cycle detection — `ensure_signature`'s `Trait` arm force-resolves each supertrait's signature so `sig_state`'s `InProgress` catches `A: B: A` → E0391 (fix sketch in `tests.rs:11695`) | small                                  | correctness; prereq for B                                                                     |
| **B** | `supertrait_closure(TraitIndex) -> [TraitBound]` — transitive set (carrying `where`-bindings), walk+visited or stored at signature time                                                | small                                  | everything below                                                                              |
| **C** | `type_implements_trait` transitivity — if the direct check fails, check whether an applicable trait's closure covers the needed one                                                    | small (one fn)                         | assoc-type bounds, method-bound-compat, call-site bounds; un-ignores the 2 transitivity tests |
| **D** | Name resolution through supertraits — `self.parent_method()` / `Self::PARENT_CONST` / `T::parent_method()` fall through to the closure; ambiguity on duplicate names is an error       | medium (touches `resolve_impl_member`) | the "can't call parent method" bug                                                            |

## Recommendation

Do **A → B → C** first — small, and it's the exact chain that (a) makes both comparator bound-checks *correct* instead of approximate, (b) un-ignores the two transitivity tests, (c) closes the cycle hole. Then **D** as the standalone user-facing fix. Then return to the comparator for assoc-type bound checking + method-generic bound-compat with `supertrait_closure` already in hand.