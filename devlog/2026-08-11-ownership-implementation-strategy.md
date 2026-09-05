# 2026-08-11 — Ownership implementation strategy: where to check, move/copy semantics

## Summary

Follow-up to [`2026-08-11-ownership-borrowing-allocator-design.md`](2026-08-11-ownership-borrowing-allocator-design.md) (same day, later session). That log settled the *model* (owned `*T` / borrowed `&T`, no `&mut`); this session worked out *where in the pipeline* the checking should live and *what counts as move vs. Copy*. Still design-only, no code changes.

## Where to run the analysis: TIR, not MIR

The prior session tentatively assumed MIR-build time, reasoning that control flow needed to already be desugared (labeled `break`/`continue` resolved, etc.). That assumption was wrong and is now corrected: **TIR already has everything that reasoning required.**

Confirmed by reading `tir/mod.rs` and `mir/mod.rs` directly:

- **TIR's control flow is already fully desugared to the same tree shape MIR has.** `ExprKind::Block { scope_index, .. }`, `IfElse`, `Loop { scope_index, block }`, `Break { scope_index, value }`, `Continue { scope_index }` — labeled blocks already resolve to `scope_index`, not names, at the TIR level. MIR's equivalent variants are structurally identical. So "needs desugared control flow" is not an argument for MIR at all.
- **TIR already has a `Place`/`PlaceKind` lvalue abstraction** (`tir/mod.rs:519`): `Deref { pointer }`, `Field { object, member }`, `Index { object, index }`, each carrying `ty`, `memory`, `mutable`, `span`. `AddressOf { place, mutable }` (today's `.&`/`.&mut` postfix operators) already operates over this — borrowed-reference creation would plug directly into the existing `AddressOf` mechanism rather than needing a new one.
- **TIR already tracks per-binding use-lists**: `Local { name, ty, mut_span, accesses: Vec<LocalAccess> }`, where `LocalAccess { span, kind: AccessKind::{Read,Write,ReadWrite} }` is an ordered record of every access to that binding. Move-checking's core need — "enumerate every use of this binding, in order" — is already there for other purposes.
- **TIR's `BlockScope { kind, label, parent, locals, .. }`** has explicit `parent: Option<ScopeIndex>` chains — the scope-nesting stack the borrow-escape check needs is real data already, not something to derive.
- MIR only exists to run *after* monomorphization + inlining. Checking there means checking every monomorphized instance of a generic function separately — duplicated work and duplicated/misattributed diagnostics (would need span-based dedup) for a property that has nothing to do with which concrete type was substituted.

Net conclusion: ownership/borrow checking is a **TIR-phase, diagnostic-producing pass** — architecturally the same category as today's type checking, not a backend concern. Everything from MIR onward stays pure lowering with no new diagnostics, preserving the existing frontend/backend split (frontend = vfs/ast/tir, backend = mir/opt/codegen). Natural hook point: alongside `ensure_body(def_id)` (Phase 3) or as a pass similar to `check_trait_conformance()` (Phase 3.5), both in `tir/builder.rs`.

## What's missing at the TIR level

1. **Ownership tag on `Type::Pointer`/`Slice`/`Array`.** Currently just `memory: TypeIndex` + `mutable: bool`. Needs an `Ownership::{Owned, Borrowed}`-style field, kept distinct from `mutable` rather than conflated with it.
2. **No new fields needed on `Local`/`LocalAccess`.** Move-state should *not* be stored as data — whether a given use is "consuming" is a function of syntactic context (by-value call argument, `Store` source, `return`, etc.), computed by the checking pass as it walks the existing `accesses` list. Keep `Local` as a read-only input to the pass, same way type-checking doesn't mutate the AST.
3. **Scope-of-origin for a `Place`'s root — not actually missing.** A `Place::Deref`'s root is an `Expression`; if it's `ExprKind::Local { scope_index, .. }`, the scope is already right there. Just needs a small helper walking a `Place` down to its root and reading `scope_index` off it.
4. **`Drop` trait / lang-item plumbing — genuinely absent.** No hookup yet for TIR to answer "does type `T` have a `Drop` impl." Would presumably follow the existing `#[lang = "key"]` lang-items map pattern (referenced in `2026-06-16-lang-items-and-codegen-fixes.md`).
5. **Move-vs-Copy classification for aggregates — the real semantic gap.** See below; this is the one piece that isn't just "add a field."

## Move vs. Copy semantics

Initial framing floated: "`*T` moves, everything else (stack values) is Copy," with `&T` left as an open question. Refined during this session:

- **The `*T` → move rule must be transitive through structs, not "stack values are Copy" wholesale.** A struct holding an owned pointer field (e.g. `struct Node { next: *Node, val: i32 }`) must itself become move-only — otherwise copying the struct silently duplicates `next`, giving two owners of the same allocation, exactly the bug the whole system exists to prevent.
- **Unified rule**: a type is **move-only (affine)** iff it (a) *is* an owned pointer/slice/array itself, or (b) transitively contains one as an **inline** (by-value) field, or (c) has an explicit `impl Drop`. Everything else is Copy. Arm (c) is independent of (a)/(b) — a type can need cleanup (an external resource handle, an index into some other table) without embedding a `*T` at all; `impl Drop`'s presence is itself the authoritative signal, matching the original "gated purely on `impl Drop` presence" decision from the prior session.
- **Computing this is cheap**: recurse only through inline-by-value fields, never through indirection (`*T`/`&T` fields stop the recursion — whatever they point to is a separate allocation with its own drop responsibility, irrelevant to the containing struct's own copy-ability). Inline fields can't form cycles (a struct can't contain itself by value), so this is a plain memoized recursive property per `TypeIndex` — no fixpoint iteration needed.
- **`&T` should be Copy** — same reasoning as Rust's shared references: it owns nothing, so unlimited aliasing of a read-only view is always sound. This was the right instinct.
- **Caveat**: Copy-ness only answers the *move-checking* question ("can this binding be used more than once"); it says nothing about the separate *scope-escape* question ("how long is this reference allowed to live"). Every copy of a `&T` still individually has to pass the scope-nesting check — Copy just permits making copies, it doesn't exempt any of them from the check.
- **Consequence for the "move-while-borrowed" problem** (flagged as the hardest interaction in the prior session): since `&T` is Copy, an owned `*T` can have arbitrarily many live borrow-copies outstanding at once, not just one — so the real question is "is *any* copy derived from this borrow still live," not "what's this one binding's last use." The conservative MVP fallback already proposed (freeze the owner for the rest of the lexical block in which it was ever borrowed, regardless of copy count) absorbs this for free since it never tracks individual bindings. Only matters once/if real last-use tracking replaces that fallback later — at that point it'd need per-*place* "any live loan" tracking rather than per-binding last-use.

## Open questions carried forward

- Exact hook point in `tir/builder.rs`'s phase sequence (`ensure_body` itself vs. a separate `Phase 3.5`-style pass) — not yet decided; needs reading `ensure_body`/`check_trait_conformance` in detail before committing.
- `Drop` lang-item shape and how it's registered/queried — not designed yet, just noted as needed.
- All open questions from the prior session (allocator-pairing enforcement, arena escape-checking, the `*T` naming-collision migration) remain unresolved and are unaffected by this session's conclusions.

## Context for future sessions

- Key TIR types to read first: `Place`/`PlaceKind` (`tir/mod.rs:519`), `ExprKind::{Load,AddressOf,Store}` (`tir/mod.rs:689-702`), `Local`/`LocalAccess`/`AccessKind` (`tir/mod.rs:751-763`), `BlockScope` (`tir/mod.rs:783`).
- `mir::ExprKind::Drop { value }` (`mir/mod.rs:101`, used in `opt/builder.rs:620`) is an **unrelated pre-existing node** — "evaluate expression, discard its value" for statement-position expressions, not the ownership `Drop` trait's destructor call. Don't collide the naming when the real `Drop` mechanism is implemented.
