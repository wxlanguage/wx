# Trailing comments, and the three ways `wx fmt` lost them

Started as a port of `libm`'s `sinf.rs` into `examples/math/sinf.wx`. Running
`wx fmt` over the result mangled the constants' hex comments, and chasing that
one symptom turned up three separate defects in `wx-fmt` — one of which was
silently *deleting* comments in five places. 925 `wx-compiler` tests, 56
`wx-lsp`, 32 → **43** `wx-fmt`.

## The port that surfaced it

`sinf.wx` is a line-for-line port of `compiler-builtins`'
`libm/src/math/sinf.rs` (itself FreeBSD `s_sinf.c`). Same bit-pattern cutoffs,
same early-return ladder, same `match n & 3` dispatch. Three deviations forced
by the language:

- **`force_eval!` dropped.** The `|x| < 2**-12` branch computes `x / 0x1p120f`
  and discards it purely to raise the inexact/underflow FP status flags. wasm
  has no FP status flags, so there is nothing to raise; `x1p120` went with it.
- **`x as f64` → `x.promote()`.** `as` is gated on `WasmScalar` equivalence,
  which f32↔f64 fails, so the width changes go through the
  `promote`/`demote` methods the kernels already use.
- **`if`-as-statement needs a trailing `;`**, same as `rem_pio2f.wx` — without
  it the `if` is parsed as the block's tail value.

`match` needed nothing special: `pattern -> { body }` with `_` as wildcard,
exhaustiveness accepted as-is.

Verified against `Math.fround(Math.sin(x))` under Deno over ~500k inputs —
dense sweeps through every branch (subnormals, `<2^-12`, each pi/4 band,
general reduction, up to `2^28*(pi/2)`), both signs, plus the exact bit
patterns either side of every cutoff. **Worst error 1 ULP**, zero results past
2 ULP; `sinf(±inf)`/`sinf(NaN)` → NaN, `sinf(-0)` → `-0`. Beyond
`2^28*(pi/2)` it returns NaN, inheriting `rem_pio2f`'s documented lack of
Payne–Hanek reduction.

To test it I built the example as a `bin` in a scratch copy with an added
`export`; `examples/math` is a `lib`, so it has no exports and nothing to
instantiate. That trick is worth remembering for any future numeric port.

## What was actually broken

Three defects, each confirmed by running the formatter, not by reading it.

**1. Trailing comments moved down a line and reattached to the next item.**

```
const A: u32 = 1; // note   →   const A: u32 = 1;
const B: u32 = 2;                // note
                                 const B: u32 = 2;
```

`build_item_list` treated every comment in the gap between two items as a
*leading* comment of the next one. There was no same-line concept anywhere in
the builder. This is the one that mangled `sinf.wx`: each `// 0x3FF921FB, …`
ended up documenting the *following* constant, and `S4`'s landed above the
function's doc comment.

**2. Comments silently deleted in five places.** `build_struct_declaration`,
`build_enum_definition` and the match-arm builder only consulted comments via
`build_empty_braced_comments` — i.e. *only when the body was empty*. Anything
between two fields, variants or arms was dropped on the floor. Likewise
comments after the last top-level item (nothing read
`between(last_item_end, EOF)`) and comments before the first item inside a
`mod` body (the leading scan was gated on `toplevel`).

**3. Blank lines carried the previous line's indent.** `Node::HardLine` wrote
`'\n'` then indent spaces, and a blank line is two consecutive hard lines — so
the first left `    ` on an otherwise-empty line. This is where the `+    `
noise in `scalbn.wx`'s diff came from.

## The rule — what rustfmt and Prettier actually do

Both decide comment placement **purely by source position, never by width**.

Prettier is the explicit version: `attachComments` classifies every comment
three ways — newline *before* it → `ownLine`, attached as a **leading**
comment of the following node; no newline before but one after → `endOfLine`,
attached as a **trailing** comment of the preceding node; neither →
`remaining`, handler-specific (`foo(/* a */ b)`). `printWidth` never enters,
and it is documented as a soft guide that trailing comments may exceed.

rustfmt's contract is the same: position relative to code is preserved. Its
width knobs (`comment_width`, default 80) only wrap a comment's *text* across
several `//` lines, and only when `wrap_comments = true`, which is off by
default. They never move a comment relative to code.

So the rule adopted here is one predicate — a comment trails iff nothing but
horizontal space separates it from the end of the code before it — plus two
refinements:

- **`///` is never trailing.** A doc comment documents what follows; letting
  one land after code would reattach it to the wrong item, which is defect 1
  in the other direction.
- **At most one comment per gap can trail**, because `//` runs to end of line,
  so every later comment necessarily has that newline in front of it. The
  split only ever inspects the first comment in the gap.

A third condition fell out of the top-of-file case: a comment with nothing but
whitespace before it *in the whole file* can't trail either — a line-1 header
has no code to trail, however little separates it from the search start.

### Why not the width-gated version

The obvious-sounding rule — "hoist a comment onto the previous line if it
fits" — was considered and rejected. It changes meaning: `// 0x3FF921FB`
written above `const S1_PIO2` documents S1, and hoisting it makes it read as
documenting S4. It is also unstable, since renaming a constant could push a
line past 80 and make a comment silently hop lines, producing diff noise
unrelated to the edit. That is why no mainstream formatter does it. The
behaviour actually wanted falls out of preservation for free: comments written
trailing stay trailing.

When a trailing comment overflows `max_line_width` it is left to overflow.
Moving it changes attribution, wrapping it changes its text; overflow is the
least-bad outcome and matches both reference formatters.

## The implementation

`split_trailing_comment` holds the entire rule. Everything else routes through
one function:

```rust
push_between(out, from: Before, to: After)
```

Every gap in every list is a combination of its two ends, and the division of
labour between them is that **what precedes the gap decides the blank line,
what follows decides whether a line is opened.**

`Before::{Opener, Entry, SpacedEntry}` names the first. Nothing trails an
opener — a comment written after `{` documents the body, not the line it sits
on — and no blank line sits directly under one, since there is nothing above
for it to separate the body from. An ordinary `Entry` keeps the blank line the
author left; `SpacedEntry` puts one in regardless, covering the lists that
always space their entries out (block-like items, impl members). The three
resolve to a `Blank::{Suppress, Preserve, Force}` that `push_line_break`
consumes, and it applies to the first break in the gap, wherever that lands —
if a comment took it, the breaks after it are ordinary.

`After::{Entry, End}` names the second. `Entry` ends by opening the following
entry's line, so an **empty gap is just the line break** — which is why every
list can route its separator through this one call instead of special-casing
"no comments". `End` bounds which comments belong to the gap and nothing more,
because nothing follows for a line to be opened for.

A list's head gap, the gaps between its entries, the one before its closing
brace, and the whole body of an empty `{ }` are then that one operation with
different ends, rather than the separate code paths that had drifted apart —
which is what defect 2 was.

The key structural change at each call site: **the line break moved from the
end of iteration N to the start of iteration N+1**, so iteration N can close
its line with `;`/`,` and let the gap append whatever trails it.

Defect 3 was fixed a level down, in the renderer: `newline()` trims trailing
spaces before writing `'\n'`, and `newline_indented()` is the only other way
to break a line. No line can end in whitespace now, which fixes blank-line
indent and anything else of the same shape at once.

Sites converted: item lists (plus `mod` bodies and end-of-file), block
statements, import entries, export entries, impl members, struct fields, enum
variants, match arms. The last three had no comment handling at all before.

### API shape — three drafts rejected in review

Worth recording, since the final shape is much smaller than the first attempt:

1. A `push_trailing_comment` helper wrapping two `out.push` calls behind an
   `if let` — dropped as pure indirection; inlined at each site instead.
2. `push_own_line_comments` with a mutable `force_blank` flag reset after the
   first iteration and `.max(usize::from(bool))` arithmetic — the loop-over-a-
   count was noise, since `count_blank_lines` already clamps to 0 or 1. Became
   a plain `if` inside `push_line_break`.
3. A separate `push_tail_comments` alongside `push_gap` — they differed *only*
   in whether a final line break gets emitted, so the terminator became a
   parameter (`After`) and the second function disappeared.

`BlockComments` was also deleted. Once `push_between` computes its own
ranges, the struct only survived to answer "does this block hold comments?",
which is now a one-line `block_has_comments` doing a single
`CommentMap::between`. `build_block_content` takes the block span directly and
is self-contained, the same shape as `build_item_list`. The old doc claimed the
struct existed so the shape wasn't computed twice — with binary-search lookup
that was a micro-optimisation costing an abstraction.

One compiler-crate change: `CommentKind` now derives `PartialEq, Eq`.

## Verification

A file exercising every construct — items, struct fields, enum variants, impl
members, match arms, export entries, block statements, each with a trailing
comment, an own-line comment and a comment after the last entry — round-trips
byte-identically and is idempotent on a second pass. `wx fmt` over
`examples/math` now moves **no comment at all**; the only remaining diffs are
stripped blank-line whitespace and `scalbn.wx`'s single-statement `if`
collapsing, which is pre-existing and unrelated.

Three regression tests added, one per defect. The round-trip test is written
as `assert_eq!(fmt(source), source)` over a source already in normal form,
so it fails loudly if any comment moves *or* disappears. Eight more followed
as each construct got routed through `push_between` — a comment straight after
a list opener, one after a non-block item, trait bodies, a comment-only file,
blank lines between leading comments, an empty body matching a non-empty one,
and no blank line under an opener — for **eleven** in total, 32 → 43.

## The regression the above missed: attributes

Shipped, installed, and immediately caught in `std/main.wx` — a blank line
appearing between a doc comment and the `#[intrinsic]` under it. None of the
tests above covered a doc comment followed by an *attributed* item.

The cause is a modelling detail worth remembering: **an item's attributes sit
outside its span.** `Item::span` starts at `pub`/`fn`, not at `#[`. The old
code never noticed because it measured blank lines from the *previous item's
end to the first comment's start* — a region that can't contain an attribute.
Routing every gap through one function meant now also measuring from the *last
comment to the item's start*, which crosses the `#[...]` line, and
`count_blank_lines` — which just counted newlines and subtracted one — read
the attribute's own line-ending newline as a blank line.

Three fixes were considered: give `Attribute` a real span in the AST (cleanest
modelling, but a compiler-crate + parser change with snapshot churn, for a
formatter-only benefit); reconstruct the item's true start in `wx-fmt` by
matching every variant for `attributes` and searching backwards for `#`
(~25 lines, duplicated for `ImplItem`, and `Attribute` only stores
`name: Spanned<SymbolU32>` so the backward search is a heuristic); or fix the
measurement, which is what landed.

`count_blank_lines` was misnamed — it computed "newlines in the region minus
one", which only equals "blank lines" when the region is pure whitespace. It
is now `has_blank_line`, returning the `bool` its single caller actually
wanted. The subtlety that cost a first attempt: **neither bound is a line
edge.** `from` is the end of an entry's *content*, and the separator the
formatter emits itself (`;`, `,`) still follows it — so a naive "scan the
whitespace run from `from`" stops dead on the `;` and reports no blank line,
which broke three existing tests. The shape that works skips the rest of
`from`'s line first, then asks whether what remains is whitespace up to a
second newline.

Whether the formatter should instead *remove* blank lines between a doc
comment and its item was considered and rejected. Checked against rustfmt
rather than assumed — it preserves all four shapes (doc→blank→item,
attr→blank→item, doc→blank→attr, doc→attr→blank→item) and only collapses runs
of two or more blanks to one, which `has_blank_line` already matches by
capping at one. Worth knowing the contrast: in Go a blank line genuinely
*detaches* a doc comment, so gofmt encodes a different model; in Rust and wx
`///` is sugar for `#[doc]` and whitespace before the item is insignificant,
so normalizing would have been safe but was declined in favour of matching
rustfmt and keeping "the author's vertical whitespace is theirs" as one rule
with no exceptions.

Consequence worth noting: because author blank lines are preserved, the five
already burned into `std/main.wx` by the broken binary were indistinguishable
from intentional ones and had to be deleted by hand — four above `#[intrinsic]`
memory functions, one above `ptr::align_up`'s `#[inline]`. Removing five
newlines shifted every byte offset in the stdlib, so all 46 affected snapshots
needed `cargo insta accept`.

## Process failure worth recording

`git checkout -- crates/wx-fmt/src/lib.rs`, run to undo a half-applied edit of
my own, also discarded uncommitted work already in that file — it was listed as
modified at session start. The lost change was the `Pattern::Struct` arm
rewritten for the new `Path::{ … }` syntax; it was reconstructed from the
already-modified `tests.rs`, whose expectations (`Point::{ x, y: renamed }`,
`geom::Point::{ x, .. }`, `Point::{ .. }`) pin the output exactly, and
`test_format_local_patterns` passes against it. Anything those tests don't pin
is gone.

The lesson generalises: in a tree with many modified files, `git checkout --`
is never a safe undo for "my" edit, because file-level granularity doesn't
match edit-level intent. Revert by re-editing, or stash first.

## Context for future sessions

- **The whole same-line rule lives in `split_trailing_comment`.** Anything
  that needs to change about comment placement — new constructs, `/* */`
  block comments if they ever land — should change that predicate or route
  through `push_between`, not add a parallel path.
- **An item's attributes are outside its span**, and its trailing `;`/`,` is
  outside it too. Any future code that reasons about the source region
  between two entries has to account for both ends holding code — that is the
  one assumption that broke here, and it broke *after* the tests were green.
- **`build_empty_braced_comments` was folded in too**, in the end: an empty
  `{ }` body is `Before::Opener` to `After::End`, so it is one
  `push_between` call and preserves blank lines like any other gap. It stays a
  named function only because nine call sites want the indent-and-break
  wrapper around it. A test pins an empty body against a non-empty one.
- **Comments inside expressions are still unhandled** — call arguments, `use`
  trees, type parameter lists. Nothing deletes them today only because the
  parser attaches them at statement granularity; worth checking before adding
  any expression-level comment support.
- **`measure_flat` returns early at the first `HardLine`**, reporting a short
  width, so a group containing one always measures as "fits". Import/export
  lists are unaffected because neither is wrapped in a `Group` at all — they
  always render in `Break` mode, which is why routing them through
  `push_between`'s `hard_line` was behaviour-preserving. Any future
  change that *does* group them needs to revisit this.
- **The `bench` target doesn't build under plain `--all-targets`** —
  `bench_lex_to_eof` is behind the `bench` feature, so clippy needs
  `--features wx-compiler/bench`. Pre-existing, trips up every full-workspace
  lint run.
- **`examples/math/sinf.wx`'s workaround for defect 1 is gone**: the hex
  comments had been moved *above* each `const` to dodge the bug, and now trail
  their constant again, matching `sinf.rs` exactly. Same in `cosf.wx` and
  `k_sinf.wx`.
