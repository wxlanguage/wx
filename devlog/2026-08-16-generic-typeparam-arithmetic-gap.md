# 2026-08-16 — Operator support for typeset-bounded assoc types: one gap fixed, one deferred

## Summary

While adding a `ptr::align_up` helper to `std/main.wx` (rounds an address up to an alignment — extracted from the hand-rolled `(bump + align - 1) / align * align` / bitmask formula duplicated across `doom/`, `examples/bump_allocator`, `examples/raycaster`, `examples/vec`, and every `examples/wasi_*` allocator), a first attempt bounded the function directly by a typeset:

```wx
pub fn align_up<Size: PointerSize>(addr: Size, align: Size) -> Size {
    local mask = align - 1;
    local result = (addr + mask) & ^mask;
    if result < addr { unreachable }
    result
}
```

This surfaced two separate, real type-checker gaps around operators on typeset-bounded types. One is fixed as of today; the other is deferred.

## Gap 1 (deferred): bare typeset-bounded type params don't support operators at all

`local mask = align - 1;` reported `cannot add `Size` to `Size`` even though both operands are the same type. The arithmetic-binary-expr matching arm only accepted two shapes for an operand: a concrete primitive (`ty.is_primitive()`), or an `AssocTypeProjection` (e.g. `Mem::Size`) whose owning trait declares that associated type with a typeset bound. A bare generic type parameter bounded by a typeset directly (`Size: PointerSize`) is `Type::TypeParam`, not `Type::AssocTypeProjection` — it matches neither shape and falls through to a type error, regardless of which typeset bounds it. Confirmed by elimination: adding more trait bounds to the param (`Size: PointerSize + UnsignedInt`) doesn't help, because the check never inspects a `TypeParam`'s bounds at all — no combination of bounds on a bare type param does anything.

This is why `Layout::array<T>(count: Mem::Size) -> Self { size: size_of::<T>() * count }` already worked before today: `Mem::Size` is an assoc-type projection off the `Memory` trait (`type Size: PointerSize + UnsignedInt;`), not a bare type param.

**Not fixed today.** `align_up` shipped bounded by `Mem: Memory` operating on `Mem::Size` instead, matching the convention every other function in the `ptr` module already uses (`add`/`sub`/`add_mut`/`sub_mut` are all `<Mem: Memory, T>`). Works today with zero compiler changes. The real fix, when picked up, is a third case alongside the primitive/assoc-type-projection ones already handled: for `Type::TypeParam { owner, index }`, check `self.tir.type_param_info(owner, index).bounds.typeset.is_some()` — the same accessor already used elsewhere for typeset-bound lookups on type params (e.g. comptime-literal-range checking).

## Gap 2 (fixed): unary and bitwise-binary operators never checked the assoc-type-projection case at all

Shipping the `Mem::Size` version hit two more bugs immediately:

- `^mask` (unary bitwise-not) on a `Mem::Size` value **crashed the compiler process** — `build_unary_expression`'s `InvertSign | BitNot` arm only checked `operand.ty.is_primitive() || operand.ty.is_comptime_number()`, and its `else` branch was a raw `panic!("can't apply unary operator to this type")` rather than a diagnostic. Any user-writable expression applying `^`/unary `-` to an assoc-type projection (or any other non-primitive type) took the whole compiler down instead of reporting an error.
- `(addr + mask) & ^mask` (binary bitwise-and) between two `Mem::Size` values failed to type-check — `build_bitwise_binary_expr`'s fallback arm gated on `left_type.is_integer() || left_type == TypeIndex::BOOL`, missing the assoc-type-projection case entirely (deliberately narrower than arithmetic's gate, since bitwise ops shouldn't apply to floats/`char` — so it couldn't just reuse the arithmetic check as-is).

Fixed by extracting the one truly shared piece — "is this an `AssocTypeProjection` bounded by a typeset" — into a single composable primitive, `is_typeset_bounded_assoc_type`, and inlining `ty.is_primitive() || self.is_typeset_bounded_assoc_type(ty)` (arithmetic/comparison/unary) or `ty.is_integer() || ty == TypeIndex::BOOL || self.is_typeset_bounded_assoc_type(ty)` (bitwise) at each of the four call sites, rather than layering named `is_arithmetic_type`/`is_bitwise_type` wrapper functions on top (tried first, deliberately reverted — the wrappers didn't pull their weight over the one real composable check). The unary arm's `panic!` was also replaced with the same `UnaryOperatorCannotBeApplied` diagnostic the sibling `Not` arm already emits, so a genuinely invalid unary application now reports an error instead of aborting the process.

All four operator-checking sites (`build_unary_expression`, `build_arithmetic_expr`, `build_comparison_binary_expr`, `build_bitwise_binary_expr`) now agree on what counts as an operand-capable type modulo their own category's extra rules (bitwise stays narrower than arithmetic on purpose).

## Context for future sessions

- Relevant code: `is_typeset_bounded_assoc_type` (`tir/builder.rs`, next to `build_arithmetic_expr`), the four call sites listed above, `type_param_info` (the accessor Gap 1's fix would reuse).
- The motivating call site: `ptr::align_up` in `std/main.wx` (in the `ptr` module, alongside `add`/`sub`/`null`) — verified end-to-end (both `u32` and `u64` memories, plus an overflow case that correctly traps via `unreachable`) and the full workspace test suite (snapshots regenerated for the `std/main.wx` growth).
- Once Gap 1 is fixed, whether to revisit `align_up`'s signature (back to a bare `<Size: PointerSize>` bound) is a separate, low-stakes follow-up — the `Mem::Size` version works fine indefinitely and arguably reads better anyway (ties the alignment arithmetic to the memory it addresses).
