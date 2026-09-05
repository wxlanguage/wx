# 2026-08-16 — Pointer/reference split design (exclusive vs. shared)

## Summary

Design-only discussion (no code changes) on replacing the current `mutable: bool` flag on `Type::Pointer`/`Slice`/`Array` with a two-kind split — `*T` = exclusive pointer, `&T` = shared read-only reference — and moving slice/array syntax to Rust-style `&[T]`/`*[T]`, `&[T; N]`/`*[T; N]`. Deliberately narrower than the 2026-08-11 ownership design: **no move-checking, no `Drop`, no lifetime/escape checking, no allocator identity**. The property "only one exclusive pointer exists at a time" is a naming/convention, not a compiler-enforced guarantee, in this pass. Landed on a concrete AST/TIR shape, resolved the sized/unsized-array exposure question, worked out address-of down to one real trade-off case, and surfaced a much bigger adjacent feature (`variant`/tagged unions) that this design leans on but explicitly defers.

## Current state (as of this session)

- `Type::Pointer { to, memory, mutable: bool }`, `Type::Slice { of, memory, mutable: bool }`, `Type::Array { of, size, memory, mutable: bool }` (`tir/mod.rs:148-163`) — same shape, same field, replicated three times.
- AST mirrors this: `TypeExpression::Pointer/Slice/Array` (`ast/mod.rs:1319-1377`) all carry `mutability: Option<TextSpan>` (a span marking presence of trailing `mut`, not a bool). Parsed via `Token::Star` (`*T`/`*mut T`) and `Token::LBracket` (`[]T`/`[]mut T`, `[N]T`/`[N]mut T`) as two independent dispatch arms in `parse_type_expression`, each with its own `parse_mut_span()` call.
- `coercible_to` (`builder.rs:1711-1770`) implements the same one-way "drop write permission" coercion three times: `*mut T → *T`, `[]mut T → []T`, `[N]mut T → [N]T`.
- Impl blocks already exist for `Slice`/`Array` (structurally, erasing element type *and* mutability — one `impl []T` covers every slice) but are explicitly excluded for `Pointer` (`ImplTarget::from_type`, `resolve_method_call` unwraps `Pointer::to` before impl lookup). `std/main.wx`'s `impl<Mem, T> Mem::[]T { fn len(...); fn ptr(...); }` (main.wx:311-321) is the only place slices get methods, and it's ordinary user-space code.
- **Arrays and slices already never live as bare stack/inline values** — both always carry a `memory: TypeIndex` tag, and MIR lowers `Type::Array` straight to `mir::Type::Pointer` (dropping the `u32` size from the MIR type entirely) and `Type::Slice` to a fixed `{ptr, len}` aggregate. No array→slice decay exists. Zero `.wx` files anywhere in the repo declare an explicit `[N]T` array-type annotation today (only inferred array literals).
- Mutability is **not represented in MIR at all** — by the time TIR→MIR lowering runs, all write-permission checks are already done; MIR only tracks `MemoryKind` (32/64-bit) per pointer. Confirms this change is TIR-local; MIR/codegen are insulated.
- Address-of/deref are postfix, method-call-style: `expr.&` / `expr.&mut` (`Expression::AddressOf`, `ast/mod.rs:1080`) and `expr.*` (`Expression::Deref`, `ast/mod.rs:1076`).
- `are_scalar_compatible`/`type_scalar` (`tir/builder.rs:11873-11961`, gates `as` casts) check `memory` equality for Pointer/Slice/Array casts but **do not check the mutable flag** — a pre-existing gap (CLAUDE.md's "cast checking is looser than it looks" pitfall) that becomes load-bearing under this design: left as-is, `shared_ref as *T` would silently defeat "a `&T` is always read-only."
- Real-code usage (repo-wide grep, `.wx` files only): 123 `*mut` sites, 10 `[]mut` sites, 0 explicit `[N]mut`/`[N]T` sites — concentrated in `std/main.wx`'s `ptr` module/`Allocator`/`Memory` traits and the WASI-facing examples (`wasi_preview1_port`, `doom/*`). Test-snapshot surface: ~240 matching lines across `tir/tests.rs`/`codegen/tests.rs`/`mir/tests.rs`, all `.snap` files needing `cargo insta accept` regeneration. `wx-fmt` has 17 dedicated match arms that must move in lockstep with the parser.

## Proposed model

| Current | Proposed | Notes |
|---|---|---|
| `*T` = immutable pointer | `&T` = shared reference, always read-only | coercion target — old `*T` was already write-incapable, so this rename is sound by construction at every existing call site |
| `*mut T` = mutable pointer | `*T` = exclusive pointer | |
| `[]T` = immutable slice | `&[T]` = shared slice | |
| `[]mut T` = mutable slice | `*[T]` = exclusive slice (can also mean "owned," informally — see below) | |
| `[N]T` = immutable array | `&[T; N]` = shared fixed array | |
| `[N]mut T` = mutable array | `*[T; N]` = exclusive fixed array | |

- **AST/TIR shape stays flat**, matching today's three-sibling-variant design — `Pointer`/`Slice`/`Array` remain distinct variants, just with `mutable: bool` replaced by an `Ownership::Exclusive | Shared` kind:
  ```rust
  Pointer { kind: Ownership, inner }
  Slice   { kind: Ownership, inner }
  Array   { kind: Ownership, size, inner }
  ```
  This resolves the "should `[T]`/`[T; N]` be exposed as standalone types" question by construction: there is no grammar production for a bare `[T]`/`[T; N]` — a `Slice`/`Array` node can't exist without an `Ownership` kind attached, same as today. No DST machinery, no by-value sized-array semantics, no new stack-allocation story. Parser-side this means restructuring dispatch so `&`/`*` is consumed *first*, then the target (bare type → `Pointer`, `[...]` → `Slice`/`Array`) is parsed — bigger than a pure rename, but still fully mechanical.
- **`*[T]` "owning" a slice costs nothing extra.** There's no move-checking to distinguish "exclusive access to an existing slice" from "freshly allocated slice" anyway — `*[T]` already covers both today (as `[]mut T` does), so this is stated behavior, not new work.
- **Coercion direction**: `*T -coerces-> &T`, one-way, same as today's three `coercible_to` cases with the boolean flipped. Migration is mechanically safe in this exact direction: every existing bare `*T` site was already read-only, so `*T → &T` and `*mut T → *T` are both sound blanket renames. The non-mechanical part is `[]T`/`[N]T` → `&[T]`/`&[T; N]` (element and size *reorder* around the brackets) — real but narrow, since zero sites use explicit `[N]T` today and only 58 slice sites total need the reorder.
- **Required, in-scope fix**: close the `as`-cast gap above — casts between `Pointer`/`Slice`/`Array` kinds must respect the same one-way direction as implicit coercion (never `&T as *T`), or the "shared is always safe to alias" property is cosmetic only.
- **Deferred, not in this pass**: `&[T; N] → &[T]` array-to-slice decay. Nothing in the codebase depends on it (zero explicit array-type usage today); adding it is new coercion logic beyond a mechanical rename.

## Address-of/deref: kept postfix, collapsed to one form

There is no `&mut` in this model at all. Exclusive pointers are only ever obtained by move through control flow (conceptually — not enforced this pass), never by borrowing an existing place. **Decision: keep the existing postfix syntax as-is** (`expr.&`, `expr.*`) rather than moving to prefix `&expr`/`*expr` — smaller diff, and the sigil position was never actually in tension with anything else discussed. The only real change is that `.&mut` disappears: address-of collapses to the single existing `.&` form, which always produces `&T`. `.*` (deref) is unchanged and continues to work through both `*T` and `&T` uniformly.

Grepping every `.wx` file for `.&mut` found exactly **one real (non-commented) call site** in the whole repo relying on the old "take a mutable pointer to a place" operator — everything else (`doom/main.wx`, `doom/m.wx`) was scratch syntax notes in a comment block:

```wx
// examples/wasi_preview1_port/main.wx:349-350
fn subscription_u_as_fd_readwrite(u: *mut SubscriptionU) -> *mut SubscriptionFdReadwrite {
  (u.*.clock.&mut) as _
}
```

This simulates a witx `union` (documented as limitation #2 in the file's own header, main.wx:18-27: wx `enum` has no payload, so the workaround is tag + largest-variant struct, reinterpreting the payload field's address as each smaller variant's type). Verified against the call site (line 677, `subscription_u_as_fd_readwrite(scratch).*.file_descriptor`) that this genuinely needs **aliasing** — the returned pointer must point at the same bytes as `scratch`'s `clock` field, not a copy, since the whole struct later goes to a WASI host expecting the union bytes at one fixed address. "Allocate a fresh pointer and return that instead" was considered and rejected for this reason.

Resolution: this was never actually in tension with dropping `.&mut` in the first place. `u: *SubscriptionU` is already the sole exclusive pointer (a parameter, not derived from an untracked place) — computing a sub-address *within memory already exclusively held* and reinterpreting its type isn't creating a second independently-tracked exclusive pointer, it's arithmetic on one you already have.

Two escape-hatch designs were tried and rejected before landing on the final one:

- **A `.&`-on-an-exclusive-place elaborates to `*T` via expected-type context** (single operator, no `.&mut`, but context-sensitive). Rejected on future-compatibility grounds: this is exactly Rust's **reborrow**, and reborrowing is the specific problem the owned/borrowed (no `&mut`) ownership model from 2026-08-11 was designed to avoid needing. If `u.*.clock.&` can produce a fresh `*T` while `u` itself is still an independently-owned `*T`, a future move-checker sees two values it thinks are independently responsible for cleanup over overlapping memory — either both get double-drop-checked (unsound), or the checker needs real region/lifetime reasoning to know the derived pointer's validity is tied to `u`'s and `u` is frozen meanwhile (Rust's actual `&mut` reborrow machinery — the hard problem `&T`-is-always-shared was specifically meant to sidestep). Reopening it one level down for `*T` undoes that.
- **A dedicated `offset_of::<T>("field")` intrinsic**, string-argument-based. Rejected for being stringly-typed (no compile-time field-existence guarantee tied to identifier syntax, no LSP go-to-def, typo-prone) — and, once the alternative below was found, unnecessary.

**Final resolution: `.&` never produces anything but `&T` — no exceptions, ever.** This is fully forward-compatible by construction, since a `&T` never enters ownership tracking at all under the 2026-08-11 model (unlimited simultaneous `&T`s are always sound). The key realization: `subscription_u_as_fd_readwrite` never actually needed a *pointer* out of the field-address computation — only the field's address *as an integer*, to compute a byte offset. Converting any pointer or reference to its raw numeric address is ownership-neutral (grants no write access, claims no exclusivity) regardless of which kind produced it — the same way Rust allows `&T as *const T as usize` freely in safe code. So a classic C `offsetof`-via-null-pointer computation, built entirely from existing pieces (`.&`, `.*`, `as` casts, the existing `ptr::null_mut` intrinsic, `std/main.wx:276`), solves it with zero new grammar and zero new intrinsics:

```wx
fn subscription_u_as_fd_readwrite(u: *SubscriptionU) -> *SubscriptionFdReadwrite {
  local base: *SubscriptionU = ptr::null_mut::<SubscriptionU, WasiMem>();
  local offset = (base.*.clock.& as WasiMem::Size) - (base as WasiMem::Size);
  (u as WasiMem::Size + offset) as *SubscriptionFdReadwrite
}
```

`base` is never actually dereferenced for a real load — field-address-of behind a pointer already lowers to pure offset arithmetic in MIR (`lower_place_address`, no `AggregateGet` involved), so a null base is safe here exactly as in C's `&((T*)0)->field` idiom. `base.*.clock.&` yields `&SubscriptionClock` (never `*SubscriptionClock` — no exception needed, since only its address-as-integer is used). The actual "produce an exclusive pointer into memory I already exclusively hold" step happens at the final `as *SubscriptionFdReadwrite` cast on `u`'s own address, which is legitimate because `u` was already exclusive. No reusable generic `offset_of` utility is needed this pass either — there's exactly one real call site, so it's solved inline rather than adding a stdlib primitive for a need that doesn't yet generalize. Net effect: address-of/deref grammar gets *smaller* than today (`.&`/`.&mut`/`.*` → `.&`/`.*`), and nothing new is added to the language to make this work.

One item worth a one-line flag for the *future* ownership design session, not a blocker now: does a scratch `null_mut()` placeholder need `Drop` bookkeeping once move-checking lands? Almost certainly not (null represents no allocation, nothing to free) — but worth confirming when that session happens.

## Bigger finding: the real fix for the union-simulation problem is a new item, not a workaround

Pushing on "why does this need pointer tricks at all" surfaced that the actual root cause is wx `enum` having no payload — confirmed by re-reading the `wasi_preview1_port` header comment, which already names this as an unsolved limitation. Two designs were compared:

- **Keep `enum` exactly as-is.** User was explicit: don't touch it. Fixed repr, required explicit `= N` value per constant, no payload — this is deliberately kept because WASI-style ABI-exact numeric enums depend on exact user-chosen discriminant values.
- **Add a new, separate item: `variant`** (name borrowed from WIT). Cases may carry an optional payload type; unlike `enum`, the compiler chooses the tag encoding — the user gets no say over the numeric value, which is the intended trade-off for gaining payload data per case. This is a real, separate feature: `match`/`enum` today (`tir/mod.rs`'s own `Pattern` doc comment: "no bindings, no or-patterns, no guards") is a pure C-style switch over an integer discriminant, and the existing `Pattern` AST type used for `local <pattern> = expr` destructuring is completely disconnected from `match` — never touched by it. Concretely, `variant` + real destructuring would need: new case syntax in item parsing, a TIR payload representation (reusing `Struct`/`StructField`-style layout per case, since `Enum`/`Struct` are fully disjoint today), and a genuinely new per-arm payload-extraction step in MIR/codegen (today `Expression::Match` lowers straight to a flat `Switch`/`br_table`, with nothing that extracts data — confirmed via `mir/mod.rs:2377-2420` and `codegen/mod.rs:915-928`). Comparable in size to, arguably larger than, the whole pointer/reference change in this document.

**Decision: deferred.** Not designed further this session. The null-pointer offset trick above stands as the pointer/reference pass's answer to the one real call site that needs it; `variant` is recorded here as the actual intended fix, motivated by a concrete existing pain point (`wasi_preview1_port`'s `SubscriptionU` hand-rolled union simulation, which `variant` would let get deleted entirely), for its own future design session.

## Open questions

- `variant` item design entirely open: case syntax, TIR payload layout reusing `Struct`, match-arm destructuring/binding syntax (the dormant `Pattern::Binding`/`Tuple`/`Struct` variants from `local`-destructuring are the natural reuse target), exhaustiveness rules once arms can bind sub-values.
- Whether a generic, reusable offset-computation helper (built the same way, from `.&`/`null_mut`/casts — no new intrinsic) is ever worth adding to `std/main.wx`, or whether `wasi_preview1_port` stays the only consumer until it's rewritten to use real tagged unions.
- Does a `null_mut()`-derived placeholder pointer need `Drop` bookkeeping once real move-checking lands? (Expected answer: no — flagged for the future ownership session to confirm.)
- Array-to-slice decay (`&[T; N] → &[T]`) — explicitly deferred, not designed.

## Context for future sessions

- Relevant existing code to read first: `Type::Pointer`/`Slice`/`Array` (`tir/mod.rs:148-163`), `TypeExpression::Pointer`/`Slice`/`Array`/`MemoryTagged` (`ast/mod.rs:1319-1377`), `coercible_to`'s three mut-drop cases (`tir/builder.rs:1711-1770`), `ImplTarget::from_type` and `resolve_method_call`'s pointer-unwrap (`tir/builder.rs`, ~15005-15109), `are_scalar_compatible`/`type_scalar` (`tir/builder.rs:11873-11961`).
- For the deferred `variant` work: `Expression::Match`/`MatchArm` (`ast/mod.rs:1109`, `1205-1225`), TIR `Pattern` (`tir/mod.rs:893-912`, note its own "v1" doc comment), `build_match_expression`/`build_pattern`/`check_match_exhaustiveness` (`tir/builder.rs:11523-11769+`), MIR `Switch` lowering (`mir/mod.rs:2377-2420`), `codegen/mod.rs:915-928` (`BrTable`), and the dormant `Pattern::Binding`/`Tuple`/`Struct` destructuring grammar (`ast/mod.rs:1389-1413`, currently only reachable from `local <pattern> = expr`).
- The one real motivating call site for both the null-pointer-offset stopgap and the eventual `variant` fix: `examples/wasi_preview1_port/main.wx:337-357` (`SubscriptionU`/`subscription_u_as_fd_readwrite`) and its use at line 677.
- No prototype code, grammar changes, or TIR changes exist yet for any of this — whiteboard stage only.
