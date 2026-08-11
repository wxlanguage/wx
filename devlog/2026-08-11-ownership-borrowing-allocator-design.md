# 2026-08-11 — Ownership, borrowing, and allocator design discussion

## Summary

Design-only discussion (no code changes) on introducing ownership and borrowing to wx, deliberately simpler than Rust: exactly two states, **owned** and **borrowed** — no `&mut T`, no shared/exclusive split. Landed on a two-state model that repurposes the existing `*T`/`*mut T`/`[]T`/`[N]T` syntax, worked out what automatic vs. manual cleanup requires without a `Drop` trait (and concluded it actually wants a minimal one), and traced why cleanup can't be a single global function once allocator identity is considered — ending on an unresolved allocator-identity question. This log exists to seed the next session; nothing here has been implemented.

## Current state (as of this session)

- `Type::Pointer { to, memory, mutable }`, `Type::Slice { of, memory, mutable }`, `Type::Array { of, size, memory, mutable }` (`tir/mod.rs`) already exist. All three carry `memory: TypeIndex` (which linear memory the data lives in) and `mutable: bool` (write access) — but **no ownership tracking, no move-checking, no cleanup** of any kind. They're raw, C-style pointers today.
- Surface syntax already covers memory-tagging and mutability for all three (`ast/mod.rs`, `TypeExpression`): `*u8` / `*mut u8`, `[]u8` / `[]mut u8`, `[5]u8` / `[5]mut u8`, and `heap::*mut u8` / `heap::[]i32` (`TypeExpression::MemoryTagged`).
- `*mut T` already implicitly coerces to `*T`, one-way, immutable direction only (see `2026-06-19-null-pointers-mut-coercion-sized-design.md`).
- None of this has any relationship to allocation: a `memory` is just an address space (bytes), there's no allocator abstraction, and no `Box`/`Drop`/move-checking exists yet.
- `std/main.wx` already has a `Memory` trait (`type Size`, `const MEMORY_INDEX`, `const DATA_END`, `grow`/`size` via `memory_grow`/`memory_size` intrinsics) — this is the substrate `memory heap: Memory32;` declarations implement. It is about the address space, not an allocator.

## Proposed ownership model

Two states only, no `&mut`. Syntax reuses existing sigils but **reassigns their meaning** — this is a breaking rename of currently-working syntax, not an additive feature (see Open questions):

| Current meaning | Proposed meaning | Notes |
|---|---|---|
| `*T` = immutable raw pointer | `&T` = borrowed, read-only, non-owning | |
| `*mut T` = mutable raw pointer | `*T` = owned pointer, requires cleanup | unique owner ⇒ mutation is always safe, no aliasing possible |
| `[]T` = immutable slice | `&[T]` = borrowed slice | |
| `[]mut T` = mutable slice | `*[T]` = owned (heap) slice | |
| `[N]T` = immutable array | `&[T; N]` = borrowed fixed array | |
| `[N]mut T` = mutable array | `*[T; N]` = owned fixed array | |

- Bare `T` (no sigil) = owned inline value (stack/struct-embedded), unchanged.
- Conversion is **one-way only**: `*T -> &T`. Never `&T -> *T` — a borrow can never become an owner (no `Rc`-style reclaiming).
- `&T` is **always read-only**. This is the load-bearing simplification that lets `&mut T` be dropped entirely: since a borrow can never mutate, unlimited simultaneous `&T`s are always sound — no aliasing-vs-mutation tracking (Rust's actual hard problem) is needed. The only remaining safety property for `&T` is a lifetime/escape check (below).
- Net effect: the `mut` qualifier disappears from slice/array/pointer surface syntax entirely, replaced by which sigil (`&` vs `*`) is used. Mutability is no longer a type qualifier — it's implied by ownership.

## Lifetime/escape checking (no `'a` syntax for MVP)

Named lifetimes (`&'a T`) are the stated eventual goal, but the session settled on **inferring, not annotating**, for the MVP, using a deliberately non-general inference:

- Rule: a `&T`'s last use must fall before scope-end of the `*T`/`T` it was borrowed from — a lexical/scope check, not Polonius-style region inference.
- To keep this decidable with zero lifetime params: **a `&T` may not be stored in a struct field, or returned in a way not obviously tied to an input parameter.** Compile error for now. These are exactly the cases that structurally require named lifetimes (a struct's own signature has to encode how long its borrowed field lives) — i.e. provably not inferable, not just hard to infer.
- This mirrors Rust's own historical path: elision rules handle the common case for free; explicit `'a` is reserved for the genuinely ambiguous cases. Named-lifetime syntax is the natural Phase 2 — added only where inference is provably insufficient (struct fields holding borrows; multi-ref-param functions with ambiguous output lifetime) — not a big-bang addition alongside the base feature.

## Cleanup: manual vs. automatic, via a minimal Drop trait

- The same move/liveness dataflow needed for use-after-move checking already tells you, at every scope-exit edge (fall-through, early `return`, `break`/`continue` out of labeled blocks — best done at MIR-build time, since control flow is already desugared there), whether an owned binding is still live.
- Key realization: **manual and automatic cleanup are the same mechanism**, not two features. If the user explicitly calls something that consumes the pointer by value (e.g. `dealloc(ptr)`), that call *is* a move — nothing left for auto-insertion to do at scope-exit. If nothing consumed it, scope-exit is reached with it still live. The only variable is what happens at that point: error, or auto-insert a call.
- Explicit requirement from this session: this must be **visible and opt-in per type, not ambient for every `*T`.** Resolution: a minimal **Drop trait**, gated purely on `impl Drop` presence — correcting a common misconception along the way: Rust's `Box<T>` isn't compiler-privileged, it's an ordinary struct implementing ordinary `Drop`.
  - No `Drop` impl (default for bare `*T`) → strict/manual mode: must be explicitly consumed (moved out, or passed to an explicit free) on every control-flow path, or compile error ("possibly leaked"). **This is the desired default.**
  - `Drop` impl present (e.g. a `Box<T>` wrapping `*T`) → compiler auto-inserts the `drop` call at scope-exit for still-live bindings of that type.
  - `drop` should take `self` **by full value** (`fn drop(self: Self)`), not `&mut self` like Rust — there's no exclusive-borrow mechanism here to reach in and take fields otherwise. `drop`'s body is checked by the same move/scope-exit machinery recursively (leftover fields not explicitly consumed inside `drop` are themselves auto-dropped if their type impls `Drop`, or required to be explicit otherwise) — this composes for free, no new mechanism needed.
- Avoiding runtime drop flags for MVP: **require a linear-owned binding to be moved on all control-flow paths uniformly, or none** (reject moving inside one `if` branch but not the other). Keeps insertion purely static — one point per exit edge, no runtime "was this actually moved" flag. Rust-style drop flags for partial/conditional moves are a later relaxation, not MVP scope.

## Allocator identity — open problem, partially resolved

- **Initial framing was wrong**, corrected mid-session: assumed tagging a pointer with its `memory` (e.g. `heap::*T`) was enough to know which `dealloc` to call, i.e. that a `memory` implies one canonical global allocator over it. It doesn't — `memory` is only an address space; nothing stops multiple independent allocators (a bump arena and a general-purpose allocator) from carving up regions of the same `memory`. Memory-tagging (needed for codegen — which linear memory to address) and allocator identity are orthogonal facts.
- Considered and rejected: "one allocator per memory" — would resolve the ambiguity, but forecloses the useful/common pattern of a scoped arena drawing from the same `memory` a general allocator also manages.
- **Current tentative direction**: don't encode allocator identity in `*T`'s type at all. Keep `*T` allocator-agnostic (just "uniquely owned, move-checked"); push "always allocate and free through the same allocator" onto wrapper types (`Box<T>` etc.), which hardcode a specific allocator call internally. Pairing correctness (never `dealloc`-ing through a different allocator than the one that `alloc`'d) is **not compiler-enforced** under this plan — accepted as a deliberate MVP trade-off, roughly analogous to C's malloc/free discipline, but still backed by real move/use-after-free/double-free checking within a binding's own lifetime (which C doesn't have).
- If/when stronger guarantees are wanted later: the generalization is Rust's `Box<T, A: Allocator>` — allocator as a type parameter, stored inline in the wrapper only when the allocator type is non-zero-sized (stateful). Explicitly deferred, not MVP.
- **Bump/arena/stack allocators need a fundamentally different mechanism than `Box` + `Drop`.** The point of a bump allocator is no per-object bookkeeping — individual objects are never freed; the arena is bulk-reset/freed when the arena itself goes out of scope. So:
  - The arena is one owned value with its own scope; its teardown is a single bulk operation, not a per-object `Drop`.
  - Every `*T`/`&T` allocated *from* the arena must be checked to not escape the arena's own lifetime — reusing the exact same escape-check machinery already needed for `&T` above, with the arena playing "owner" instead of a single value.
  - Concretely: bump-allocated pointers should **not** go through `Box`/`Drop` in the common case.

## Open questions

- Should there eventually be *any* compiler-enforced allocator-pairing check short of full `Box<T, A>` (e.g. a cheap syntactic check catching the most obvious `alloc`/`dealloc` mismatches)? Unresolved.
- Escape-checking for arena-allocated pointers needs its own design pass — only sketched as "reuse the `&T` lifetime mechanism," not worked out.
- **Naming collision**: the *existing* compiler already assigns `*T` = immutable raw pointer, `*mut T` = mutable raw pointer, with no ownership semantics, and this syntax is used in real code today (e.g. `examples/bump_allocator`). The proposed scheme reuses `*T` for a materially different meaning (owned, requires cleanup). This needs a deliberate migration decision before implementation starts — e.g. rename the current raw/unowned-pointer meaning to something else (so raw pointers and owned pointers can coexist), or treat the ownership feature as fully replacing today's raw-pointer semantics.
- Exact `Drop`/`Allocator` trait shapes are undecided, including whether `Allocator` should be its own trait separate from the existing `Memory` trait in `std/main.wx`.

## Context for future sessions

- Relevant existing code to read first: `Type::Pointer`/`Slice`/`Array` in `tir/mod.rs` (~line 148), `TypeExpression::Pointer`/`Slice`/`Array`/`MemoryTagged` in `ast/mod.rs` (~line 1319), the `Memory` trait in `std/main.wx` (~line 174), and the `*mut T -> *T` coercion rule referenced above (`tir/builder.rs`, `coercible_to`).
- No prototype code, trait definitions, or parser changes exist yet for any of this — the whole thread above is still at the whiteboard stage.
