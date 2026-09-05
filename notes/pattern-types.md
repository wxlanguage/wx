# Pattern types — value-restricted primitive types

Status: **parked idea, not scheduled.** Written up for later reference after a
detour while designing `Alignment32`/`Alignment64` in `std/main.wx`.

## Where this came from

While adding an `Align` associated type to `Memory` (bound to a per-pointer-width
`Alignment32`/`Alignment64` enum enumerating every valid power-of-two alignment),
we ended up hand-writing 32 and 64 explicit enum variants respectively — one
`AlignNShlM = 1 << M` per bit position — purely so the type checker could reject
non-power-of-two values at the impl site.

Rust's `core::ptr::alignment.rs` does the exact same thing internally: a private
`AlignmentEnum` with one variant per power of two, used only to give the public
`Alignment` newtype a validity invariant the compiler can reason about (and get
niche-optimization — `Option<Alignment>` costs nothing extra — for free). The
source has a comment on the `_inner_repr_trick` field:

> Hopefully it'll eventually be a pattern type instead.

"Pattern type" refers to an unstable Rust feature (tracking issue
[rust-lang/rust#123646](https://github.com/rust-lang/rust/issues/123646)) that
lets a type be declared as "this base type, restricted to values matching this
pattern" directly in the type system — e.g. `pattern_type!(u32 is 1..)` for a
nonzero `u32` — instead of faking the restriction with an enum whose only job is
listing legal discriminants.

## The idea for wx

wx already has two-thirds of the machinery this would need:

- **`typeset`** already validates that a literal's value fits inside a
  compile-time-known range (`IntegerRange` intersection, used by
  `report_integer_literal_out_of_typeset_range` in `tir/builder.rs`) — but only
  to pick *which primitive type* a generic parameter may be, not to restrict
  *which values* of one single type are legal.
- **`eval_const_expr`** (`tir/builder.rs`) folds literal const expressions —
  recently extended to cover `&`, `|`, `^`, `<<`, `>>` alongside the existing
  `+ - * / %` — so `1 << 5` already reduces to a checkable `ConstValue::Int` at
  exactly the point a discriminant or const gets validated today.

A `pattern` declaration would be the natural next step: reuse that same
fold-then-check pipeline, but check set/range membership against a single base
type instead of enumerating named variants:

```
// Range form — mirrors Rust's NonZeroU32 use case, reuses the IntegerRange
// machinery typeset intersection already has.
pattern Positive: u32 = 1..;

// Value-list form — what Alignment32/64 actually need, since "power of two"
// isn't a contiguous range. Same values the enum lists today, just without
// needing 32/64 named variants to hang them on.
pattern Alignment32: u32 { 1 << 0, 1 << 1, 1 << 2, /* ... */, 1 << 31 }
```

Type-checking a value against a `pattern`-typed position would be: fold it via
`eval_const_expr` (already happens for enum discriminants and consts), then
check range-containment or set-membership — literally the same validation
`Alignment32`'s enum-discriminant checking does today, minus the requirement to
name every value.

## Where it's hard / out of scope

- **Predicate patterns** (`pattern Alignment32: u32 where is_power_of_two(v)`)
  are a much bigger lift — `eval_const_expr` only folds literal expressions, not
  arbitrary function calls, so this would need real const-fn evaluation
  infrastructure wx doesn't have. The value-list form sidesteps this by writing
  out all 32/64 alternatives explicitly instead of evaluating a predicate — the
  same limitation Rust's *shipped* pattern-type subset has today (it's mostly
  range patterns; arbitrary predicates aren't part of the accepted design
  either).
- **Runtime narrowing.** A `u32` value not known at compile time (user input, a
  computed field) still needs a real fallible check —
  `fn Alignment32::try_from(v: u32) -> Option<Self>` actually testing the
  power-of-two property at runtime. wx has no `unsafe` keyword (confirmed: no
  `Unsafe` token/variant anywhere in `ast/mod.rs`), so unlike Rust's
  `Alignment::new_unchecked`, there would be no shortcut around that check —
  arguably a simpler, more honest story than Rust needs, at the cost of no
  escape hatch for a caller who's already proven the value's validity some
  other way.

## Payoff if built

`Alignment32`/`Alignment64` collapse from 32 + 64 hand-enumerated enum variants
to two one-line `pattern` declarations, with identical compile-time enforcement.
More generally, it's a reusable primitive for any "restricted-value" API —
non-zero integers, bounded percentages, valid enum-discriminant ranges — without
each one needing its own hand-rolled enum-of-legal-values trick.
