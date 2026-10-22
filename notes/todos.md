# TODOs

## ~~Flatten supertrait bounds in `TypeParamInfo`~~ — done, differently

**Closed 2026-09-07.** The gap was real: `T: C` recorded only `[C]`, so a
transitive `C: B: A` never satisfied a bound on `A`.

It was closed by walking rather than flattening. `ItemRegistry::trait_implies`
does a visited-guarded walk up the supertrait graph, and `type_implements_trait`
asks it when the direct check fails. Flattening at bound-resolution time would
have needed every trait's supertrait clause resolved before any bound naming it
could be resolved — an ordering constraint the demand-driven builder does not
have, and would have had to grow one for. Walking on demand needs only that the
clause is resolved by the time someone asks, which `ensure_trait_supertraits`
guarantees.

The note's other claim — that call-site bound checks were being skipped
vacuously — no longer holds either: `test_type_param_multiple_bounds_missing_impl_is_error`
was un-ignored in the same pass and now reports E1063 as written.
