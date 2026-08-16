# Effect tracking — implementation plan

Companion to [`effect-system.md`](./effect-system.md), which specifies the
design (syntax, semantics, resolution rules). This doc is the implementation
side: what to build, in what order, and the decisions made getting here.
Branch: `effect-tracking` (off `develop`).

Thesis framing: this is the practical, implemented centerpiece backing the
type-system/typechecker/stdlib deep-dive. The MVP below is deliberately
narrow — a single effect atom (`trap`) — chosen so there's a complete,
defensible, working feature to write about rather than a partial general
mechanism.

## MVP scope

**In:**
- `does(...)` / `does(*)` / `does()` syntax — parser + AST.
- A single effect atom: `trap`.
- Resolution folded into existing TIR phases (no new phase — see below).
- `wx-fmt` printing of `does(...)` clauses.
- LSP signature display (hover / wherever signatures render) showing `does(...)`.

**Out (explicitly deferred, not accidentally missing):**
- Arithmetic operators (`+ - * / %`) carry no effect information, even
  though div/rem-by-zero traps. wx has no `Add`/`Sub`/`Mul`/`Div` traits —
  arithmetic is the primitive `ast::BinaryOp` node, not trait-dispatched
  (confirmed: no such traits exist in `std/main.wx` or `mir/mod.rs`). Wiring
  operator effects would mean inventing a hardcoded op → effect table ahead
  of any real operator-overloading mechanism existing. Known consequence:
  `does()` can currently be claimed by a function that actually traps via
  division. Documented gap, not a bug — matches the design doc's own §9
  distinction between `does()` and `does(trap)`, just not enforced yet.
- MIR/Opt changes of any kind. No CSE/DCE/dead-call-elimination payoff at
  this stage — effect data sits in TIR and stops there.
- Memory-parameterized effects (`read<M>`/`write<M>`/`grow<M>`, §8).
- Trait method effects (§6) — unreachable anyway with no operator traits.
- Effect-generic callbacks (`effect E` generic param, §11).
- `std/main.wx` annotation: done last, as one deliberate isolated pass (see
  Snapshot discipline below), not incrementally alongside the mechanism.

## Key decisions

### Representation: `EffectSet`

```rust
pub enum EffectSet {
    Top,
    Bounded(Box<[DefId]>),
}
```

- Not `BTreeSet<DefId>` — sets are 0–3 elements in practice; a tree is pure
  overhead at that size.
- **Not sorted.** Subset-checking (`does(a) ⊆ does(a, b)`) on a handful of
  elements is a linear "every element of A present in B" scan either way;
  sorting buys nothing here. Order is whatever the source text wrote (or
  whatever a checking pass accumulates), and that's already deterministic
  for snapshot purposes — re-parsing the same source always yields the same
  order, so there's no canonicalization to do.
- General (`Box<[DefId]>`, not a hardcoded `TrapEffect` marker), even though
  the MVP only ever populates it with one atom — so a second atom later is
  additive, not a rewrite.

### Storage: on `Function` directly, not a parallel map

`tir::Function` (`tir/mod.rs:1332`) gets a new field, sitting next to
`result: Option<Spanned<TypeIndex>>`:

```rust
pub effects: Option<EffectSet>,
```

`None` = unannotated (§4 resolution rule: unannotated ⇒ `Top`, always —
`None` and `Some(Top)` are the same meaning; keeping `None` for "nothing
written" vs `Some(Top)` for "explicitly wrote `does(*)`" is worth keeping
distinct for the formatter/LSP display, so it round-trips what the user
wrote instead of collapsing to a single top representation).

No separate `SigEntry`-parallel structure. `sig_state: HashMap<DefId,
SigEntry>` exists for re-entrancy tracking during resolution (see
`ensure_signature`'s cycle guard) — it's not where finished data belongs.
Resolved effect data lives on `Function` the same way resolved param/return
types do.

### Phasing: no new phase

Two distinct cases, both fit into phases that already exist:

- **Bodyless leaf resolution** (a `does(atom, ...)` on a body-less function
  mints or references atoms) is signature-shaped work — it belongs in
  `ensure_signature(def_id)`, alongside where param/return types resolve
  today. No new pass needed for this half.
- **Bodied-function checking** (declared effects must be a superset of
  every direct callee's declared effects — one-hop only, per §4, never
  descending into callee bodies) needs the body, so it folds into the
  *existing* `ensure_body(def_id)` phase rather than a new post-`ensure_body`
  pass.

### `trap` is an `#[intrinsic]`, and it already has plumbing

`#[intrinsic]` is the sole existing mechanism in wx for declaring a
body-less function the compiler knows how to lower directly (`memory_grow`,
`slice_len`, `size_of`, etc. — all in `std/main.wx`, dispatched by name
string in `mir::lower_intrinsic`, `mir/mod.rs:3050`, a big `match name_str`
block ending in `_ => unreachable!("cannot lower unknown intrinsic...")`
at `mir/mod.rs:3577`). Since "an effect is just a body-less function that
self-annotates" (§5), `trap`'s ground-truth atom has to be minted by an
actual body-less function, and body-less functions in wx are only ever
`#[intrinsic]` — so:

```
#[intrinsic]
fn trap() does(trap) -> never;
```

**Finding: most of the runtime plumbing for this already exists**, just not
exposed as a callable. wx already has `unreachable` as a first-class keyword
expression (`Keyword::Unreachable`, `ast/lexer.rs:1942`; parsed at
`ast/mod.rs:3271`; `ast::Expression::Unreachable`), which already lowers
end-to-end: `tir::ExprKind::Unreachable` (`tir/builder.rs:9605`) →
`mir::ExprKind::Unreachable` (`mir/mod.rs:1814`) →
`opt::ControlNode::Unreachable` (`opt/builder.rs:624`) →
`Instruction::Unreachable` / WASM opcode `0x00`
(`codegen/mod.rs:97,931,1167`). So `trap`'s intrinsic body is just: lower to
the same `Unreachable` node the `unreachable` keyword already produces. No
new codegen instruction needed — one new arm in `lower_intrinsic`'s match.

**Open question worth resolving early:** the bare `unreachable` keyword
already exists independently of any function call. If someone writes
`unreachable` directly inside a function body (not via `trap()`), does that
also count as invoking the `trap` effect for checking purposes? If not,
`does()` becomes trivially and silently violable by writing `unreachable`
directly instead of calling `trap()` — which defeats the point. Leaning
toward: yes, the body-checking walk should treat a bare
`ExprKind::Unreachable` node the same as a call to the `trap` intrinsic's
`DefId` (both "reference the atom"), not just literal calls to `trap()`.
Needs to be nailed down before checking is implemented, since it changes
what the `ensure_body` walk has to look for (not just call sites).

## Modules to touch

| Module | What |
|---|---|
| `ast/lexer.rs` | `does` keyword |
| `ast/mod.rs` (parser) | parse `does(...)` / `does(*)` / `does()` clause between params and return type; AST node for it |
| `tir/mod.rs` | `EffectSet` type; `effects: Option<EffectSet>` field on `Function` |
| `tir/builder.rs` | resolve `does(...)` clause in `ensure_signature`; mint/reference atoms for bodyless leaves; check declared ⊇ callees' declared (incl. bare `unreachable`) in `ensure_body`; new diagnostics |
| `std/main.wx` | `#[intrinsic] fn trap() does(trap) -> never;` — added once the mechanism works, annotation of the rest of the stdlib done last as its own pass |
| `mir/mod.rs` | new `"trap"` arm in `lower_intrinsic` (`mir/mod.rs:3050`), lowering to `ExprKind::Unreachable` — the only MIR-side change, and it's just plumbing a new intrinsic name, not effect-aware logic |
| `wx-fmt` | print `does(...)` clauses in function signatures |
| `wx-lsp` | show `does(...)` wherever a function signature is rendered (hover, etc.) |
| tests | inline `TestCase` fixtures in `tir/tests.rs` for resolution + checking, before touching `std/main.wx` |

## Diagnostics (new)

- Unresolved effect name in a `does(...)` clause (referenced atom doesn't
  resolve to a body-less self-annotating function).
- Declared effects not a superset of a callee's declared effects (the `⊆`
  violation, i.e. a bodied function under-declares relative to what it
  calls).

## Suggested order

1. Syntax: lexer + parser for `does(...)`/`does(*)`/`does()`, AST node. No
   semantic meaning yet — just parses and round-trips.
2. `EffectSet` + `Function::effects` field; bodyless-leaf resolution in
   `ensure_signature`. Add `trap` intrinsic (`mir::lower_intrinsic` arm +
   `std/main.wx` declaration) at this point, so there's a real atom to
   resolve against in tests.
3. Bodied-function checking folded into `ensure_body`, including the bare
   `unreachable`-counts-as-`trap` decision above. Diagnostics.
4. `wx-fmt` printing.
5. LSP signature display.
6. `std/main.wx` annotation pass — narrow, deliberate, last. One
   `INSTA_UPDATE=always` snapshot regen at the end (per CLAUDE.md: any
   `std/main.wx` change shifts byte offsets and breaks every snapshot test,
   so this must be its own isolated commit, not interleaved with mechanism
   work).

## Snapshot discipline

Steps 1–5 should be validated against small inline `TestCase` fixtures only
— touching `std/main.wx` before the mechanism is fully working and tested
means repeatedly eating full-suite snapshot churn for no reason. Step 6 is
the one point where `std/main.wx` changes, and it should be a single
isolated pass followed by one `cargo insta accept`.
