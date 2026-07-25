# `match` expressions, end to end (with `br_table`)

## Summary

Added `match` as a first-class expression to wx, carried through every compiler
stage as a genuine N-way construct rather than desugared to nested
`if`/`else`. Scope: integer/char/bool literal patterns, `Enum::Variant`
patterns, `_` wildcard; full exhaustiveness checking; codegen chooses between
a WASM `br_table` (dense case values) and a right-nested `if`/`else` chain
(sparse), decided once during Opt construction. Two unrelated bugs surfaced
and were fixed along the way — see [Bug hunts](#bug-hunts).

15 files changed, +2459/−67 lines. 668 tests passing.

## Pipeline

```
source text
    │  ast::Parser::parse()
    ▼
AST        Expression::Match { scrutinee, arms }
    ▼
TIR        ExprKind::Match { scrutinee, arms: [MatchArm { pattern: Pattern, body }] }
    │      (type-checked, name-resolved, exhaustiveness-proven)
    ▼
MIR        ExprKind::Switch { selector, cases: [(i64, Expression)], default }
    │      (generic N-way branch — not yet dense/sparse-decided)
    ▼
Opt        ControlNode::Switch { .. }   OR   ControlNode::IfElse chain
    │      (should_use_br_table decides here, once)
    ▼
Scheduler  Instruction::BrTable(..)   OR   If/Else/Eq instructions
    ▼
Codegen    WASM bytecode (opcode 0x0E, already reserved but unused before this)
```

## Stage 1 — AST & parser

`crates/wx-compiler/src/ast/mod.rs`, `crates/wx-fmt/src/lib.rs`

```rust
Expression::Match {
    scrutinee: Box<Spanned<Expression>>,
    arms: Box<[Separated<Spanned<MatchArm>>]>,
}
struct MatchArm {
    pattern: Box<Spanned<Expression>>,
    body: Box<Spanned<Expression>>,
}
```

Patterns are **not** a separate grammar — they're parsed as ordinary
`Expression`s (`Path` for `Enum::Variant`, `Placeholder` for `_`, literals
as-is), the same way `EnumVariant.value` already defers legality checking to
TIR instead of inventing a parallel syntax. Arms parse via the existing
`SeparatedGroup` machinery (same as enum bodies).

**No new token.** Match arms reuse `Token::MinusRightArrow` (`->`) instead of
adding `=>`. Verified safe: `->` is only ever consumed at fixed grammar
positions (after a parameter list, before a return type) and has no
`led_lookup` entry, so the Pratt expression parser simply stops there — same
as it would for any other unrecognized token. No lexer change needed.

`wx-fmt` got a `build_match_expression` printer (modeled on the enum-body
printer), verified by formatting a file and recompiling the formatted output
to confirm identical WASM.

## Stage 2 — TIR (types, resolution, exhaustiveness)

`crates/wx-compiler/src/tir/mod.rs`, `tir/builder.rs`

```rust
enum Pattern {
    Int(i64),
    Bool(bool),
    Char(char),
    EnumVariant { enum_index: u32, variant_index: EnumVariantIndex },
    Wildcard,
}
struct MatchArm { pattern: Pattern, pattern_span: ast::TextSpan, body: Box<Expression> }
```

No bindings, no or-patterns, no guards in v1 — deliberate scope, not a
shortcut.

**`build_pattern` reuses the ordinary expression builder** instead of writing
a parallel resolver: it runs the arm's syntax through `build_expression`
(including `build_path_expression`'s existing `Type::Enum ->
ResolvedMember::EnumVariant` arm), then matches the resulting `ExprKind`
(`Int`/`Bool`/`Char`/`EnumVariant`) into a `Pattern`. Anything else is
`E1065 InvalidPattern`. This reuse buys two things for free: untyped literal
coercion (`coerce_untyped_expr` handles range/type diagnostics identically to
any other literal), and enum-variant "used" tracking (resolving
`Color::Green` in a pattern pushes to `variants[..].accesses` exactly like
resolving it anywhere else).

**Exhaustiveness** (`check_match_exhaustiveness`): a wildcard arm makes it
trivial. Otherwise, for an enum scrutinee, builds a `Vec<bool>` coverage
bitset over `tir.enums[idx].variants`, reports missing names via `E1063
NonExhaustiveMatch` (reusing `report_unused_enum_variants`'s 1/2/3–5/many
phrasing). For non-enum scrutinees (int/char/bool), a missing `_` is always
an error — the domain isn't enumerable. The same coverage bitset also catches
exact-duplicate patterns for free: `W1010 UnreachableMatchArm`.

Diagnostic codes: `E1063` non-exhaustive, `E1064` invalid scrutinee type,
`E1065` invalid pattern shape, `W1010` unreachable arm. Arm type mismatches
need **no new diagnostic** — they unify pairwise against the running result
through the existing `self.unify`/`report_type_mistmatch`, the same
mechanism `if`/`else` already uses for two branches, folded across N arms.

## Stage 3 — MIR (`Switch`, not nested ifs)

`crates/wx-compiler/src/mir/mod.rs`

```rust
Switch {
    selector: Box<Expression>,
    cases: Box<[(i64, Expression)]>,   // (discriminant, body), source order
    default: Option<Box<Expression>>,  // None only when TIR proved exhaustiveness
}
```

The one decision that shapes everything downstream: `match` is **not**
desugared to nested `if`/`else` here, because collapsing to binary ifs this
early would throw away the case list a later stage needs to decide
`br_table` vs. comparison chain. Every discriminant is a canonical `i64` by
this point (raw int value, 0/1 for bool, codepoint for char, or the enum
variant's already-folded `const_value`), so arm bodies — always `{ }` blocks
per the grammar — lower through the existing `Block` path unmodified.

The two other MIR passes that exhaustively walk every `ExprKind` (the
inlining-time deep-clone/scope-offset rewriter, and the post-order call-site
inliner) each got one parallel `Switch` arm.

## Stage 4 — Opt (sea-of-nodes, and where dispatch strategy is decided)

`crates/wx-compiler/src/opt/mod.rs`, `opt/builder.rs`, `opt/liveness.rs`

MIR's `Switch` is uniform — every match becomes one. Opt splits it in two,
**once**, at the `mir::ExprKind::Switch` dispatch site in `build_expr`:

```rust
fn should_use_br_table(selector_ty: mir::Type, cases: &[(i64, mir::Expression)]) -> bool {
    if ScalarType::try_from(selector_ty) != Ok(ScalarType::I32) { return false; }
    if cases.len() < 3 { return false; }
    let range = max - min + 1;   // i128 math, dodges overflow
    if range > 512 { return false; }
    (cases.len() as f64) / (range as f64) >= 0.5
}
```

- **`>= 3` cases** — below that, a jump table's fixed setup (shift + implicit
  bounds check) doesn't beat two direct comparisons.
- **density `>= 0.5` over range `<= 512`** — a table costs bytes proportional
  to the value *range*, not the arm count; a sparse-but-3-arm match spread
  over a wide range would waste most of the table on default-pointing gaps.
- **I32 selector only** — the dispatch shifts by `-min` and truncates to i32
  (`br_table`'s index is always i32 regardless of scrutinee width). For an
  I64 selector, a genuinely out-of-range value could truncate into an
  in-range index and get misrouted to the wrong case instead of falling to
  default. Rather than add a separate range-check-before-truncate path,
  I32-only sidesteps the issue — and covers the overwhelming majority of real
  matches (enums, `bool`, `char`, ordinary `i32`/`u32`) anyway.

### Why the decision lives in Opt, not the scheduler

The original plan put this in the scheduler ("codegen stays mechanical,
strategy is a late decision"). That turned out to be wrong: `break`/
`continue` depths are computed by walking `Block::parent`, and that chain is
built during Opt construction, *before* the scheduler runs. If the scheduler
could independently re-decide the dispatch shape, the parent chain built at
Opt time and the instructions the scheduler actually emits could disagree
about how many WASM blocks wrap a case. Deciding once, storing nothing extra
on `ControlNode::Switch`, and having each path build its own matching parent
chain removes that whole class of desync — at the cost of
`ControlNode::Switch` now meaning something more specific: it's exclusively
the `br_table` shape.

### Sparse path — `build_switch_as_if_chain`

Below the threshold, nothing new is invented at the instruction level.
`build_if_chain_arm` builds one comparison — `if selector == discriminant {
case } else { <rest> }` — and recurses on the else side, producing genuine
`ControlNode::IfElse` nodes indistinguishable from a hand-written `if x == 0
{} else if x == 1 {} else {}`. It reuses `extend_bindings` and
`merge_branches` — the exact primitives `build_if_else` already uses for a
single then/else pair. The one thing that couldn't be reused directly:
`build_if_else` re-evaluates its condition via `build_expr` on every call,
but the match scrutinee must be evaluated *exactly once* (it can have side
effects) — so the selector is computed once as a `DataNodeIndex`, and each
comparison synthesizes its own `Eq` node directly against that index.

A `_ -> body`-only match lowers to `Switch { cases: [], default: Some(body)
}` in MIR — nothing to compare, so it's inlined directly with no branch at
all, a free byproduct of this structure.

### Dense path — `build_switch`

Above the threshold, `build_switch` is now exclusively the `br_table`
builder (it used to also emulate the nested-if shape, back when the strategy
was undecided at this stage). New types:

```rust
ControlNode::Switch { selector, cases: Box<[SwitchCase]>, default: Option<SwitchCase>, outputs, result }
SwitchCase { discriminant: Option<i64>, block: BlockIndex, own_values: Box<[StackResult]> }
```

`own_values` exists because `DataNodeKind::Phi` is strictly binary
(`left`/`right`, positionally keyed) — `IfElse` can recover "which branch
contributed which value" structurally since there are only two branches; an
N-ary join can't. So each `SwitchCase` carries its own per-slot values
explicitly, and the scheduler reads from there instead of decomposing a Phi.

## Stage 5 — Scheduler (the actual `br_table`)

`crates/wx-compiler/src/opt/scheduler.rs`

`emit_switch_br_table` emits a fixed stack of WASM `block`s around the
dispatch — one per case, plus `$default`, plus `$after` as the join point.
**Every wrapper closes before the content that "belongs" to it runs** — a
case's body sits one level further out than its own wrapper, not inside it.
That's the exact detail that caused both bugs below.

```
block $after                       // join point; result type lives here
  block $default
    block $case[N-1]
      ...
        block $case[0]
          <selector - min>  br_table
        end                        // case 0 body starts here — still inside $case[1]
        <case 0 body>  br $after
      end                          // case 1 body starts here
      ...
    end                            // case N-1 body starts here — still inside $default
    <case N-1 body>  br $after
  end                              // default body starts here — still inside $after
  <default body>                   // (or unreachable, if TIR proved exhaustiveness)
end
```

`br_table` case *i* → depth *i*, default → depth *N*. Every case's own
trailing `br` skips past whatever's left to reach `$after`. The table covers
every index in `[min, max]`, not just the ones a case claims — gaps (density
can be as low as 0.5, not 1.0) point at the default depth, same as anything
genuinely out of range:

```rust
let mut depths = vec![case_count as u32; range + 1];   // last slot = default depth
for (i, case) in cases.iter().enumerate() {
    depths[(case.discriminant.unwrap() - min) as usize] = i as u32;   // array position, not value
}
```

`depths[shifted]` stores each case's *array position* (declaration order),
not its discriminant value — cases aren't guaranteed sorted, so the mapping
goes through the case's index. `Instruction::BrTable(Box<[u32]>)` carries
both the table and the trailing default as one field, rather than a separate
`default_depth` field — the encoder needs the exact same split either way.

## Stage 6 — Codegen

`crates/wx-compiler/src/codegen/mod.rs`

The `0x0E` `BrTable` opcode constant had been sitting unused in the encoder
since the module was first sketched out. Encoding just splits the
scheduler's `Box<[u32]>` back into what the WASM binary format wants — a
length-prefixed vector, then the default as a separate trailing `u32`:

```rust
SI::BrTable(depths) => {
    sink.push(Instruction::BrTable as u8);
    let (default_depth, table) = depths.split_last().expect("never empty");
    (table.len() as u32).encode(sink);
    for depth in table { depth.encode(sink); }
    default_depth.encode(sink);
}
```

## Bug hunts

### The wrapper-chain off-by-one (twice)

`break_depth`/`continue_depth` resolve a `break`/`continue` by walking
`Block::parent`, adding one hop per ancestor — that walk has to land on
exactly the number the scheduler's real nesting produces. Getting it right
took two failed attempts, both caught by actually *executing* the compiled
module rather than just inspecting instruction counts.

- **Attempt 1 — one hop too many.** Every case's `Block::parent` was set to
  a synthetic wrapper representing *its own* numbered `$case[i]` — plausible,
  wrong. A case's body is emitted *after* `$case[i]` already closed, so it's
  never nested inside its own wrapper — it's nested inside `$case[i+1]`, one
  level further out. Result: every `continue` branched one block too far,
  landing on the loop's outer break-target instead of the loop itself.
  Confirmed by disassembling with `wasm2wat` and reading which label each
  `br` actually resolved to.
- **Attempt 2 — the default arm, same mistake in a different spot.** Fixing
  the case chain surfaced the identical error one level out: `$default` also
  closes before its own body runs (mirroring every `$case` wrapper), so the
  default arm's body actually lives directly inside `$after` — not inside
  `$default`'s own nesting, which the parent chain had assumed. A `break` in
  the default arm branched one level too far, escaping past the function's
  own implicit return scope and failing WASM validation outright (`"type
  mismatch: expected i32 but nothing on stack"`) rather than silently
  misbehaving.

Neither bug showed up in instruction-shape tests — both compiled a
reasonable-looking `br_table`. What caught them: a dense match nested inside
a loop, with `break`/`continue` from several different case positions, run
through wasmtime end to end. That test —
`test_match_inside_loop_break_and_continue_dense_br_table` — now exercises
this path permanently.

### A second, unrelated bug found along the way

Testing `match` inside a loop surfaced a bug with nothing to do with `match`
— it reproduces identically with plain `if`/`else`, and predates this
feature entirely.

A loop commits its loop-carried locals to their WASM locals only in its own
"normal fallthrough" tail code. `break` and `continue` bypass that tail
entirely, so a mutation made immediately before an early exit (`acc += 1; if
acc == 5 { break; }`) was silently lost — the loop reported the value from
*before* the mutation that triggered the exit.

Fixed by having every `break`/`continue` site commit its own current values
before branching (`loop_param_updates`, threaded through `opt/builder.rs`
and emitted two-phase — compute every new value first, then store all of
them — in `Scheduler::emit_loop_param_updates`, to avoid one update's store
clobbering a local a later update still needs to read). This also reshaped
`Block`'s loop-only fields out into a separate `Function.loops:
Vec<LoopData>` table, indexed by `Block::loop_index`, so every `Block` stays
the same small shape whether or not it's a loop.

## Testing strategy

Coverage follows the pipeline, plus the one layer the pipeline stages can't
verify themselves:

- **AST** — snapshot tests for literal/enum patterns, plus one asserting the
  exact diagnostic cascade a malformed arm produces.
- **TIR** — exhaustive-with-wildcard, exhaustive-by-coverage,
  missing-variant, non-enum-without-wildcard, invalid-pattern-shape,
  arm-type-mismatch, variant-marked-used, duplicate-pattern-warns.
- **MIR** — int match lowers to `Switch`, enum discriminants fold to repr
  values, exhaustive-enum-no-wildcard has `default: None`.
- **Opt** — no-divergent-bindings (unanimous fast path),
  phi-per-divergent-binding, result-value-join, exhaustive-enum-has-no-default
  — each bumped to `>= 3` dense cases so it actually exercises `build_switch`
  after the sparse/dense split landed.
- **Scheduler** — a sub-threshold match schedules `If`/`Else` with no
  `BrTable`; a dense match schedules exactly one `BrTable` with the expected
  depths and no `If` at all.
- **Codegen (wasmtime execution)** — the layer nothing above it can verify:
  actually running the compiled module. Int match, enum dispatch, a sparse
  match inside a loop with break/continue, and the dense `br_table` match
  inside a loop with break/continue from multiple case positions (the test
  that caught both depth bugs above).

## Files touched

| File | Δ |
|---|---|
| `ast/mod.rs` | +65 |
| `ast/tests.rs` | +54 |
| `wx-fmt/lib.rs` | +44 |
| `tir/mod.rs` | +31 |
| `tir/builder.rs` | +382 |
| `tir/tests.rs` | +185 |
| `mir/mod.rs` | +106 |
| `mir/tests.rs` | +80 |
| `opt/mod.rs` | +108 |
| `opt/builder.rs` | +616 |
| `opt/liveness.rs` | +44 |
| `opt/scheduler.rs` | +285 |
| `opt/tests.rs` | +295 |
| `codegen/mod.rs` | +15 |
| `codegen/tests.rs` | +214 |

+2459/−67 across 15 files (excludes an unrelated `editors/vscode` submodule
pointer bump). 668 tests passing; full workspace build clean.

## Open questions

- Codegen `BrTable` support was the last piece of the original `match` plan;
  nothing else from that plan is outstanding.
- The I32-only restriction on `br_table` eligibility means I64 matches never
  get the dense path — worth revisiting if that ever shows up as a real
  perf concern, but no evidence of that yet.
