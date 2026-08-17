# 2026-08-17 — Compound assignment implementation, dead-code-lint fix, and two deferred bugs

## Compound assignment (task #8) implemented

Followed the design in
[2026-08-17-compound-assignment-trait-dispatch-design.md](2026-08-17-compound-assignment-trait-dispatch-design.md).
`tir::BinaryOp` (18 non-assignment variants) now replaces `ast::BinaryOp` on
`ExprKind::Binary.operator`; a new `Assign` node covers plain `x = y` for
`Local`/`Global`/`FieldAccess`/`Placeholder` targets; `CompoundAssign`/
`GenericCompoundAssign`/`CompoundStore`/`GenericCompoundStore` cover `+=` and
friends, with `self_type: TypeIndex` (not a `type_args` slice — none of the
operator traits' methods have generics beyond the implicit `Self`) and
`abstract_method_id` naming per review. `resolve_compound_operator` replaces
the old ambiguous-`Option` resolver, returning `Result<CompoundOperatorDispatch, ()>`.
MIR lowering shares one `build_compound_operator_call` helper between the
`Expression`-target and `Place`-target pairs, calling `record_call_edge`
(the step flagged as required, not optional, by an earlier efficiency
review — see the design doc) and fixes the pre-existing
`arr[i()] += 1` double-eval bug via the temp-local-sink idiom already used
elsewhere in `mir/mod.rs`. Verified directly against the accepted MIR
snapshot for a struct-field-through-pointer compound assignment: address
computed once, call collapsed to a native `Add`, both load and store reusing
the same temp local.

## Dead-code lint fired on trait impl methods (fixed)

`report_unused_items` (`tir/builder.rs`) was flagging every primitive
`impl Add for i32`-style method as "never used" whenever a given test/program
didn't happen to invoke that specific operator on that specific type — since
each test compiles a small isolated snippet but the full stdlib (all ~60
primitive operator impls across 10 numeric types) is always loaded. This
alone accounted for most of the "584 passed / 129 failed" baseline noted in
the previous devlog entry's implementation. Fixed by extending the existing
`type_param_parent` check: `TypeParamOwner::TraitImpl(_)` is set only by
`AstNodeRef::TraitImplFunction`'s registration path (`tir/builder.rs:6730`),
never by the inherent-impl path (`TypeParamOwner::ImplBlock(_)`), so it's a
free, zero-cost signal already sitting on `Function` — no precomputed
`HashSet`/`Vec<bool>` needed. Matches Rust: implementing a trait is itself
the "use." Test suite: 609 passed/104 failed → 710/3.

## `opt::tests::TestCase::get_first_func` fixed, revealing a different bug

`get_first_func` assumed `mir.functions.first()` was always the test's own
function — reasonable before stdlib had much content, wrong now that
primitive operator impls exist (though DCE turned out to still strip them
correctly in practice). Added `get_tagged_func(tag)` (`#[tag = "..."]` on the
test's function + `tir.tagged_items` lookup, mirroring
`resolve_operator_trait`'s own pattern) as the robust alternative. Using it
on `test_simple_add` proved the "wrong function" theory wrong — `add` was
already being selected correctly — and surfaced the real bug underneath: a
genuinely extra `Int(0)` node in `add`'s own output.

Root cause: `mir::inlining::inline_call` structures an inlined `#[inline]`
call as a wrapper block containing one `LocalSet` per parameter (writing
into the callee's rebased scope via its global `flat_index`) *before* the
callee's own body block is spliced in as a sibling statement. `LocalSet`
uses `ensure_bindings_capacity` (grows with `StackResult::Unit`, no node
allocated) so the forwarding itself is free — but `extend_bindings`/
`extend_bindings_in_place` (`opt/builder.rs`), run when that body block is
later entered, unconditionally `.push()`ed a fresh `default_value` for every
one of its locals, landing past the slots the `LocalSet`s had already
populated and producing nodes no `flat_index()` call ever references (CSE
dedupes multiple identical defaults into one, which is why only one orphan
showed up despite two parameters). Fixed by having both functions check
each local's real `flat_index` against the current bindings length first,
skipping the default when the slot's already populated. Test suite:
710/3 → 711/2 (no new failures elsewhere — verified no other inlining-heavy
test depended on the old behavior).

An independent review (fork, instructed to be adversarial rather than
confirm) verified this fix's safety by tracing every `extend_bindings`
caller (`build_if_else`, `build_switch_as_if_chain`, `build_switch_arm`,
`build_loop`): each sibling scope always starts from an untouched parent
snapshot (per `build_block_expr`'s write-back, `bindings[..parent_len]
.copy_from_slice(&child[..parent_len])`), so `idx == child.len()` holds by
construction outside the inlining case — confirmed via
`debug_assert_eq!(idx, child.len())` on the fallthrough branch, never
tripped across the full suite.

## Two bugs found, deferred (user: "keep them noted, we will tackle them later")

**Chained-inlining flat-offset collision (value-correctness bug).** While
stress-testing the fix above, the same review fork constructed
`fn calc(a,b,c,d: i32) -> i32 { (a + b) + (c + d) }` and ran it through
wasmtime: `calc(-5,5,-5,5)` returns `-5`, not `0`. Confirmed pre-existing
(not caused by the `extend_bindings` fix above) by temporarily reverting
that fix and reproducing the identical wrong value at the identical spot.
Root cause: `compute_locals_offsets` gives sibling scopes the same flat
offset on the assumption they're "never simultaneously active" — true for
ordinary lexical siblings, false for *chained* inlining, where an outer
inlined call's `LocalSet` stages a value at a shared offset and a second,
also-offset-sharing inlined sibling's own `LocalSet` overwrites that slot
before the staged value is ever consumed. `(a+b)`'s inlined scope, `(c+d)`'s,
and the outer `+`'s all land at the same offset in the failing case; `c`
silently clobbers the staged `(a+b)` result.
**Likely the same root cause as `codegen::tests::test_lerp`'s wasmtime trap**
(`a + (b-a)*t` — also three chained inline-dispatched ops) — check this
first before treating `test_lerp` as its own investigation. Fix most likely
belongs in `compute_locals_offsets` or `inline_call`: offset-sharing needs
to account for staged-but-not-yet-consumed values from simultaneously-live
inlined siblings, not just non-overlapping lexical scope.

**`char` missing `impl Sub`/`impl Add` — resolved, intentionally, as "no impl."**
`c - 32` for `c: char` reports "operator `-` cannot be applied to type
`char`" — this was flagged as a possible gap, but the design decision
(explicitly made, not a default): `char` deliberately gets no `impl Add`/
`impl Sub` at all. Not just a Rust-parity choice — arithmetic directly on
`char` isn't safe: `char` carries a validity invariant (a legal Unicode
scalar value), and an `Add`/`Sub` impl would let any in-range-looking
expression silently produce an out-of-range or surrogate bit pattern with no
checkpoint to reject it. Requiring an explicit cast to an integer type first
(`(c as u8 - 32) as char`, the same idiom `std/main.wx`'s own
`to_ascii_uppercase`/`to_ascii_lowercase` already use) puts the unsafe part
where it's already visible and already the user's responsibility — the `as
char` cast back — rather than hiding it inside an innocuous-looking `+`.
So there is no compiler fix here — the diagnostic was already correct. Only
the *test* was stale: `test_stdlib_struct_field_access` (a pre-existing
misnomer — its body never touched a struct) asserted `c - 32` should compile
with no diagnostics, which was true before trait-dispatch made arithmetic
require a real impl. Renamed to `test_char_arithmetic_requires_explicit_cast`
and rewritten to use the cast-based form; added a sibling
`test_char_arithmetic_without_cast_is_error` to lock in the rejection as
intentional, not incidental. 717 passed / 1 failed (only `test_lerp`, the
still-deferred chained-inlining bug, remains).
