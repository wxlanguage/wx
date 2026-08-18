# 2026-08-18 — Bitwise operator traits, enum explicit-anchor values, two generic-trait-dispatch bugs, and a found-but-deferred memory-tag bound gap

Long session covering several mostly-independent pieces of work, tied
together by a running theme: every feature addition immediately got
stress-tested against real `.wx` example code, which is what surfaced three
of the four bugs fixed today. Full suite: 762 passed / 0 failed / 4 ignored.

## 1. Bitwise operator overloading (`BitAnd`/`BitOr`/`BitXor`/`Shl`/`Shr`/`BitNot`)

Extended the existing arithmetic-operator-trait machinery
(`Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg`) to bitwise operators, same shape:
`#[tag = "..."]`-marked stdlib traits, `OperatorTraits::for_op`/`for_unary_op`
lookup tables, native fast-path codegen preserved for primitives/`bool`
(`build_bitwise_result` mirrors `build_arithmetic_result`), real
`MethodCall`/`GenericMethodCall` dispatch only for structs and
typeset/generic-bound cases. `#[inline]` on every primitive impl collapses
calls back to bare intrinsics — verified via `wasm2wat`, zero call overhead.

Comparison operators (`==`/`<`/etc.) were explicitly scoped out for a later
session — deferred, not designed yet (open question: 6 flat traits vs.
Rust-style `PartialEq`/`PartialOrd` split).

## 2. Integer literal width: `i64` → `u64`

Found while testing bitwise ops on negative enum values: `parse_integer_literal`
stored literals as `i64`, capping representable magnitude at `i64::MAX` —
`u64::MAX` and `i64::MIN` literals couldn't even be written. Root-cause fixed
by widening `ExprKind::Int`/`ast::Expression::Int` to `u64`, representing the
raw non-negative magnitude as written; negation is always a separate
`Unary{InvertSign}` node, never folded into the literal itself outside
`eval_const_expr`. `ConstValue::Int` stays `i64` (bit-reinterpreted,
`u64::MAX as i64 == -1`, same convention `IntegerRange` already used) — it
represents an already-typed, resolved constant, a different concern from the
literal's pre-coercion magnitude.

Two boundary bugs fixed alongside:
- `coerce_untyped_unary_expr` range-checked negation against the
  *positive*-max bound, wrongly rejecting `i8::MIN`/`i16::MIN`/etc. (the
  most-negative value of each width has no positive counterpart in two's
  complement). Fixed with a dedicated `TYPE::MIN.unsigned_abs()` magnitude
  check.
- `eval_const_expr`'s Div/Rem folded with signed semantics unconditionally
  (`u64::MAX / 2` gave `0` instead of the correct unsigned answer) — fixed by
  checking `expr.ty`'s signedness and routing through `u64` wrapping ops when
  unsigned. `Add`/`Sub`/`Mul` didn't need this (representation-agnostic in
  two's complement).

## 3. Enum variants now require an explicit anchor value

Old behavior: `enum E: repr { A, B = 5, C }` silently defaulted `A` to `0`
with zero required values anywhere — `examples/compare/main.wx`'s `Ordering`
enum was actually `{ Less, Equal = 0, Greater = 1 }`, so `Less` silently
collided with `Equal` at `0`. New rule: an implicit (auto-incrementing)
variant is only legal once *some earlier* variant in the same enum wrote an
explicit value — `{ A = 0, B, C }` still auto-increments `B`/`C` from `A`
fine, but `{ A, B }` is now `E1071` on `A`. New diagnostic
`EnumVariantRequiresExplicitValue`; implementation is
`next_auto_value: Option<i64>` in `build_enum` (`None` = no anchor yet) — a
plain bool flag was tried first, then replaced with the `Option` per review
feedback, which also simplified "does a broken-but-present value still
anchor" to "no" for free (unified state, not two separately-tracked things).

Blast radius was bigger than the initial `.wx`-file grep found: ~15
Rust-embedded test fixtures across `mir`/`opt`/`codegen`/`tir` tests relied on
an implicit first variant. One of them
(`codegen::tests::test_match_enum_dispatch_runs_correctly`) hard-aborted the
*entire* test binary via `TestCase::new`'s deliberate
`std::process::exit(1)` on TIR errors — worth remembering next time a
`codegen::tests` run reports zero clean failures instead of a normal
per-test `FAILED`.

## 4. Generic-bound dispatch for unary operators (`Neg`/`BitNot`)

`build_operator_dispatch` (binary) already had a `Type::TypeParam` branch —
`build_unary_operator_dispatch` didn't, so `fn f<T: Neg>(x: T) -> T { -x }`
silently failed to dispatch (documented as a known gap while adding `BitNot`,
fixed today). Added the missing branch, mirroring the binary case exactly:
routes through `resolve_bounded_operator_method` into a `GenericMethodCall`,
resolved at MIR monomorphization time. Verified against both the native
fast-path case (`mir::tests::test_generic_bitnot_bound_resolves_to_primitive_impl`,
snapshot-checked) and a struct-impl case (`Vec2` with real `Neg`/`BitNot`
impls, chained through both generic functions, checked via `wasmtime` against
a hand-computed result).

## 5. Two bugs in "method has its own type params" handling

Found via a real example (`examples/hashing/main.wx`, a `Hasher`/`Hash`
pair modeled on Rust's `std::hash`) that a `fn write<Mem: Memory>(...)`
method declared *inside a trait impl* — as opposed to the impl block itself
being generic — hit two independent, previously-untested bugs:

**5a. TIR: `TraitImplFunction` dropped the method's own type params entirely.**
`AstNodeRef::TraitImplFunction` (methods inside `impl Trait for Type { }`)
hardcoded the new `Function`'s `type_params: Box::new([])` and never called
`resolve_type_param_bounds` for them — unlike the exactly analogous
`InherentImplFunction` and `TraitFunction` arms, which both do this
correctly. Result: `Mem` inside `fn write<Mem: Memory>(self: Mem::&Self, ...)`
resolved fine when written directly on the *trait*, but "cannot find type
`Mem` in this scope" the moment an *impl* provided it — invisible until now
because `resolve_type_param_bounds` early-returns on an empty param list, so
every trait-impl method without its own generics (the common case) never hit
the gap. Fixed by mirroring `InherentImplFunction`'s pattern.

**5b. MIR: abstract dispatch conflated "impl block is generic" with "impl's
copy of the method is generic."** Once 5a was fixed, the same example crashed
*codegen* instead (`self.func_wasm_index[&id]`, "no entry found for key") —
`GenericMethodCall`'s abstract-method-dispatch branch decided whether to
reuse a bare, already-emitted function id vs. monomorphize on demand purely
by checking `impl_type_args.is_empty()` (the impl *block's* own generic args)
— which says nothing about whether the impl's *method* itself declares
additional params (`Mem` on `write`, independent of the impl block, which
here isn't generic at all: `impl Hasher for DefaultHasher`). Reused the bare
id, which was never actually emitted (`MIR::build`'s eager-emission loop
skips anything with nonzero *total* type params), producing a `Call` to
nothing. Fixed by also checking the impl method's own `type_params`, and
building the full monomorphization arg list from impl-block args + the
method's own args (`resolved[1..]`, skipping the leading `Self` slot).
`resolve_generic_compound_method` has the identical shape/comment
("exactly `GenericMethodCall`'s abstract-method branch") but is *not*
affected — compound-assignment only ever dispatches through the fixed
`OperatorTraits` set, none of which declare their own extra params, so
there's no live bug there, just a structurally similar but currently-inert
code path. Confirmed via `git diff`/side-by-side re-reading, not fixed
speculatively.

Both got minimal regression tests: 5a as a TIR-only resolution check
(`test_trait_impl_method_with_own_generic_type_param_resolves`), 5b as a
from-scratch `Writer`/`Consumer` shape with null pointers and no hashing
logic (`test_trait_method_with_own_type_param_called_through_generic_bound`)
— deliberately stripped of the original FNV-1a repro's incidental complexity,
verified to still reproduce the exact panic when reverted.

## 6. Dead-code cleanup (found while reviewing the above)

- `coerce_untyped_binary_expression`'s bitwise-operator arm was provably
  unreachable — confirmed by temporarily instrumenting it with `eprintln!`
  and running the full suite plus a manual CLI check with `--nocapture`
  (zero hits), then explaining *why*: `build_bitwise_binary_expr`, unlike
  `build_arithmetic_expr`, always resolves its own type inline against
  `access_ctx`'s expected type (or reports "type annotation required"
  itself), so a bitwise `Binary` node is never left in the untyped state
  this function exists to coerce. It was also stale even hypothetically —
  its allowlist only covered `i32`/`i64`/`u32`/`u64`, missing the
  `u8`/`i8`/`u16`/`i16` impls added this session. Replaced with a
  `debug_assert!`.
- That removal made `tir::BinaryOp::is_bitwise` fully unused — removed.
- Same sweep found `ast::BinaryOp::is_assignment`/`is_comparison`/
  `is_logical`/`is_arithmetic`/`is_bitwise` (a *different*, unrelated
  `BinaryOp` type from the `ast` module) were *all* already unused
  workspace-wide, predating this session — removed all five.
- `coerce_untyped_int_expr`'s 9 near-identical per-primitive-type branches
  (each: one upper-bound check, one diagnostic, one `expr.ty = X`) collapsed
  into a single `match target_idx { .. } -> Option<u64>` lookup + one shared
  check, once the u64-widening refactor made every branch structurally
  identical (single-sided upper-bound only, `ty: target_idx` throughout).

## 7. Found, discussed, deferred: memory-tag positions don't check the `Memory` bound

`type Ptr<T> = T::&u8;` — and more generally any `Mem::&T`/`Mem::*T`/`Mem::[T]`
syntax where the base is a bare, *unbounded* type param — type-checks with
zero errors. Pinned to `resolve_type`'s `ast::TypeExpression::MemoryTagged`
arm (`tir/builder.rs`, the block handling `Mem::&T`-shaped syntax): once the
memory-position expression resolves to a `Type::TypeParam` or
`Type::AssocTypeProjection`, the code accepts it unconditionally —

```rust
match &self.tir.types[memory_ty.as_usize()] {
    Type::Memory { .. }
    | Type::TypeParam { .. }
    | Type::AssocTypeProjection { .. } => {}
    _ => { /* "not a memory declaration" */ }
};
```

— with no check that the type param/projection is actually bounded by
`Memory`. Confirmed the *narrower*, explicitly-bounded case (`fn f<Mem:
Memory>(x: Mem::&u8)`) is *also* unchecked, not just the type-alias framing —
this is a general gap, not alias-specific.

### Design work, not yet implemented

First two attempts both tried to answer "how do we cheaply get `Memory`'s
`TraitIndex` inside this one check" and both were correctly pushed back on:

1. Reuse the existing `#[tag = "..."]` / `tagged_items` mechanism
   (`resolve_operator_trait`'s pattern). Rejected: that mechanism is only
   safe because `resolve_operator_traits()` runs *once*, strictly after the
   entire Phase 2 `ensure_signature` sweep completes — `tagged_items` is
   populated as a side effect of `resolve_attributes`, itself only called
   from inside `ensure_signature`. `resolve_type`'s `MemoryTagged` arm runs
   *during* Phase 2, demand-driven, at unpredictable points — nothing
   guarantees `Memory`'s own `ensure_signature` (and thus its tag) has run
   yet when this check fires.
2. Resolve `"Memory"` by name at the check site itself, on every call,
   caller-relative (`resolve_identifier_as_bound`, same mechanism a written
   `T: Memory` bound would use). Correct, but reopened as "why does this
   need to be a fallible per-call lookup at all" — pushed toward the actual
   root cause instead of patching around it.

**Landed on (design only — not implemented)**: `Memory`'s `TraitIndex` is a
well-known constant, exactly like the pre-interned `TypeIndex` table
(`TypeIndex::I32` etc.) already is — it should be resolved *once*, right
after Phase 1 pre-scan completes (traits get their `TraitIndex` slot
immediately in pre-scan, independent of `ensure_signature` — only their
*contents*, not their identity, need Phase 2), and cached as a plain
`Builder` field, not re-resolved per call site. `std`'s crate is
unambiguously identifiable (`load_stdlib()` always names it literally
`"std"`, `vfs/mod.rs:316`), and `build()` already builds a
`crate_namespaces: HashMap<CrateId, NamespaceIndex>` during pre-scan — find
the `"std"`-named crate's namespace, look up `"Memory"` directly in *that*
namespace's own `symbols` map (no wildcard-import walk needed, it's declared
right there), store the resulting `TraitIndex` unconditionally (no `Option`
— a missing `Memory` trait in std at that point is a stdlib/compiler bug,
same invariant class `resolve_operator_trait` already leans on, just checked
one phase earlier). Every call site becomes a plain field read.

A `#[tag = "memory"]` was added to `std/main.wx`'s `Memory` trait and a
`report_memory_tag_not_bounded` diagnostic function was drafted during the
false starts above — both **reverted** before committing, since neither is
needed for the landed design and leaving them in would just be inert,
half-wired dead code. `resolve_type`'s `MemoryTagged` handling is back to
byte-identical with pre-session `HEAD`.

## Example: `examples/hashing/main.wx`

New example modeled on Rust's `std::hash::{Hash, Hasher}` — `Hasher`
trait with a default `#[inline] fn hash<Mem: Memory, T: Hash>` dispatcher,
`DefaultHasher` (real FNV-1a, not a stub), `Hash for i32`. This is what
surfaced bug 5 above; also deliberately keeps the unused
`type Ptr<T> = T::&u8;` alias in place as a live, still-reproducing example
of the bug in §7. Verified end-to-end via `wasmtime` — `hash_i32(42)` /
`hash_i32(43)` / `hash_i32(0)` all match an independently-computed reference
FNV-1a (cross-checked in Python). Was originally added onto
`examples/compare/main.wx` (which had an unrelated `Ordering`/`Ord` sketch);
moved to its own file and the unrelated content dropped, since by the end it
had nothing to do with comparison.

## State

762 passed / 0 failed / 4 ignored. `cargo fmt --check` clean. `wx-cli`/`wx-fmt`
build clean. Snapshot diffs from the `u64` literal-width change are
offset/representation-only, verified before accepting.

## Open questions / next up

- Comparison operators (`==`/`<`/etc.) as overload traits — trait shape not
  yet decided.
- §7 (memory-tag `Memory`-bound check) — design is settled, not implemented.
- `resolve_generic_compound_method`'s structurally-identical-but-currently-safe
  gap (§5b) — no action needed unless an operator trait ever grows a method
  with its own type params, which none currently do.
