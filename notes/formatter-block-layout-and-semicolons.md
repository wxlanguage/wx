# Formatter rules for blocks, tail expressions, and semicolons

## Purpose

This note defines the intended formatting policy for executable blocks in
`wx-fmt`. It is an implementation guide, not a proposal to change the WX
grammar or type system.

The policy has three goals:

1. Preserve the semantic distinction between a statement and a block's result
   expression.
2. Use compact blocks only when they remain easy to read.
3. Give optional semicolons after block-like expressions one canonical visual
   role without requiring type information in the formatter.

The formatter must remain syntax-directed. `wx-fmt` receives the AST and source
text, but not TIR or resolved expression types.

## Relevant compiler behavior

### Separators are represented explicitly

Statements in an AST block are stored as
`Separated<Spanned<Statement>>`. `Separated::separator` records whether the
source contained the trailing `;`.

See:

- `crates/wx-compiler/src/ast/mod.rs`: `Separated<T>`
- `crates/wx-compiler/src/ast/mod.rs`: `Expression::Block`
- `crates/wx-compiler/src/ast/mod.rs`: `Statement`

### The final unterminated expression is the block result

TIR construction classifies the final entry as the block result only when:

- it is the final entry,
- it is an expression statement, and
- `separator.is_none()`.

Every other expression is built in statement position. See
`Builder::build_block_expression` in
`crates/wx-compiler/src/tir/builder/body.rs`.

Consequently, a formatter must not generally change this:

```wx
{
    calculate();
}
```

into this:

```wx
{
    calculate()
}
```

If `calculate()` produces a value, the first form reports `UnusedValue` while
the second propagates the value as the block result. WX has no implicit value
discarding. Explicit discard is written as assignment to `_`:

```wx
{
    _ = calculate()
}
```

Assignment to `_`, like other assignments, has `Unit` type.

### Block-like expressions have an optional separator in statement position

`Expression::is_block_like()` currently includes:

- bare blocks,
- `if`/`else`,
- loops,
- labeled blocks,
- matches,
- struct initializers.

The parser does not report a missing separator after these expressions. Their
closing brace makes them syntactically self-delimiting, allowing the parser to
continue with the next statement.

This syntactic exception does not by itself say whether a block-like expression
is a statement or a result. Its position in the containing block still decides
that.

## Terminology

This note uses the following terms:

- **Entry**: one `Separated<Spanned<Statement>>` in a block.
- **Tail result**: the last entry when it is an expression and has no
  separator.
- **Statement position**: every entry other than a tail result.
- **Terminated expression**: an expression whose AST entry has a separator.
- **Block-like expression**: an expression for which
  `Expression::is_block_like()` returns true.
- **Flat** or **inline**: braces and contents render on one line, such as
  `{ break 5 }`.
- **Broken** or **multiline**: the contents render on lines between the braces.

These terms describe two independent levels. In this example, `foo()` is the
tail result of an `if` branch, while the complete `if` is a statement in the
function body:

```wx
fn f(condition: bool) -> i32 {
    if condition { foo() } else { bar() };
    calculate()
}
```

## Rule 1: classify semantic role before formatting

For each entry in a block, classify it as follows:

```text
tail result =
    entry is the last entry
    && entry is Statement::Expression
    && entry.separator.is_none()

statement position = anything else
```

This classification must be based on the AST and entry position, not on the
eventual line layout.

The formatter must never add or remove the separator of a final entry in a way
that changes this classification.

In particular:

```wx
fn value() -> i32 { calculate() }
```

must not acquire a semicolon, and:

```wx
fn effect() {
    calculate();
}
```

must not lose its semicolon merely because `calculate()` might return `Unit`.
The AST-only formatter cannot prove its type, and the explicit separator also
preserves useful diagnostics in an invalid program.

## Rule 2: eligibility for a flat block

A non-empty executable block may render flat only when all of the following
are true:

1. It contains exactly one entry.
2. That entry is `Statement::Expression`.
3. The entry has no separator; it is a tail result, not a terminated statement.
4. The expression is not block-like according to
   `Expression::is_block_like()`.
5. The block contains no comments.
6. The expression does not introduce a mandatory hard line.
7. The whole containing group fits within `max_line_width`.

If any condition fails, the block must render multiline.

An empty block remains `{}` unless it contains comments.

### Function signatures and bodies share the flat decision

For a function body, condition 7 applies to the complete function declaration,
not to the body starting at the position after an already-broken signature.

If any part of the function signature breaks, the body must also use multiline
layout:

```wx
fn function_with_many_parameters(
    first: i32,
    second: i32,
) -> i32 {
    foo()
}
```

Do not produce a broken signature followed by a newly flattened body:

```wx
fn function_with_many_parameters(
    first: i32,
    second: i32,
) -> i32 { foo() }
```

The dependency is intentionally one-way:

```text
signature breaks -> body breaks
body breaks       -> parameter list may remain compact
```

A body may be forced multiline by comments, multiple entries, a terminated
entry, or a block-like tail even when the signature itself fits. That must not
needlessly explode a short parameter list:

```wx
fn f(condition: bool) -> i32 {
    if condition { foo() } else { bar() }
}
```

Requiring the reverse dependency would instead produce an undesirable form:

```wx
fn f(
    condition: bool,
) -> i32 {
    if condition { foo() } else { bar() }
}
```

Therefore an inline function body is allowed only when both conditions hold:

1. The body is structurally eligible under Rule 2.
2. The complete signature plus flat body fits without any signature group
   breaking.

### Consequences

A simple result may be inline:

```wx
fn f(condition: bool) -> i32 { foo() + bar() }
```

A terminated expression records statement intent and forces a multiline block:

```wx
fn log_result() {
    console::log("done");
}
```

The formatter must not rewrite it as either of these:

```wx
fn log_result() { console::log("done"); }
fn log_result() { console::log("done") }
```

Two entries always force multiline layout, even when both would fit:

```wx
fn run() {
    initialize();
    execute()
}
```

Do not produce:

```wx
fn run() { initialize(); execute() }
```

A block-like tail also forces its containing block to break. This avoids
excessive brace density:

```wx
fn f(condition: bool) -> i32 {
    if condition { foo() } else { bar() }
}
```

Do not produce:

```wx
fn f(condition: bool) -> i32 { if condition { foo() } else { bar() } }
```

The rule applies to every variant currently reported by
`Expression::is_block_like()`, including struct initializers:

```wx
fn make() -> Point {
    Point::{ x: 1, y: 2 }
}
```

This is intentional: nested braces inside an inline containing block have the
same readability problem even when the expression is not control flow.

### Branches are checked independently but break together

An `if` and its `else` branch should share one break decision. If either branch
is ineligible for flat layout, both branches render multiline:

```wx
if condition {
    foo()
} else {
    prepare();
    bar()
}
```

The semicolon on `prepare()` remains because it separates two expressions.
The tail expressions `foo()` and `bar()` remain unterminated.

The same applies if either branch contains a comment or a mandatory hard line.

## Rule 3: ordinary expression separators

For an ordinary, non-block-like expression:

- A non-final entry must render with `;` because another entry follows it.
- A final entry preserves its AST separator.
- A final unterminated expression remains the block result.
- A final terminated expression remains in statement position and forces the
  containing block to be multiline under Rule 2.

Examples:

```wx
fn calculate(n: i32) -> i32 {
    validate(n);
    perform_calculation(n)
}
```

```wx
fn explicit_drop() { _ = calculate() }
```

```wx
fn explicit_drop_after_setup() {
    setup();
    _ = calculate()
}
```

The last assignment may be unterminated because it is the block's explicit
`Unit` result. The formatter does not need type information to preserve that
source intent.

## Rule 4: optional separators after block-like expressions

A block-like expression can omit `;` in statement position because it is
self-delimiting. Use that optional punctuation to distinguish compact and
multiline forms.

### Non-final block-like expression

When another entry follows, the block-like expression is already in statement
position regardless of whether its AST separator is present. In this case the
formatter may normalize the optional separator without changing which
expression is the containing block's result:

- If the block-like expression renders flat, emit `;`.
- If it renders multiline, omit `;`.

Flat form:

```wx
fn f(condition: bool) -> i32 {
    if condition { foo() } else { bar() };
    calculate()
}
```

The semicolon gives the dense one-line expression a visible boundary.

Multiline form:

```wx
fn f(condition: bool) -> i32 {
    if condition {
        foo();
    } else {
        bar();
    }
    calculate()
}
```

The closing brace already provides a strong visual boundary, so the optional
outer semicolon is omitted.

This normalization is safe only because another entry follows. TIR will build
the block-like expression in statement position either way.

### Final block-like expression

When the block-like expression is the final entry, preserve its AST separator
regardless of whether it renders flat or multiline:

| Final entry in source | Meaning | Formatter action |
| --- | --- | --- |
| no `;` | containing block result | keep no `;` |
| has `;` | explicit statement position | keep `;` |

For example, this `if` is the function result:

```wx
fn choose(condition: bool) -> i32 {
    if condition { foo() } else { bar() }
}
```

No semicolon may be added after the `if`.

In this example the user explicitly terminated the final `if`, so that intent
must survive formatting:

```wx
fn perform(condition: bool) {
    if condition { foo() } else { bar() };
}
```

The function body is multiline because its only entry is terminated.

### Decision table

| Position in parent block | Block-like layout | Output separator |
| --- | --- | --- |
| Non-final | Flat | Emit `;` |
| Non-final | Multiline | Omit optional `;` |
| Final, separator absent | Either | Keep absent |
| Final, separator present | Either | Keep `;` |

## Worked examples

### Fibonacci-style guards

Input spellings such as these currently coexist:

```wx
if n <= 1 { return n }
if n == 0 { break a; }
if n == 1 { break b };
```

When each `if` is followed by another expression, the canonical output is:

```wx
if n <= 1 { return n };
if n == 0 {
    break a;
}
if n == 1 { break b };
```

The second branch stays multiline because `break a;` was explicitly
terminated. The formatter preserves that inner intent rather than silently
turning it into a tail result. The outer separator is omitted for that
multiline `if` and emitted for the flat `if` expressions.

If all three inner `break`/`return` expressions are unterminated, all three
guards may remain compact when they fit:

```wx
if n <= 1 { return n };
if n == 0 { break a };
if n == 1 { break b };
```

### Result-valued `if`

```wx
fn choose(condition: bool) -> i32 {
    if condition { foo() } else { bar() }
}
```

The branch blocks are compact. The function body is not, because its sole tail
expression is block-like. The final `if` receives no semicolon because it is
the function result.

### Statement-valued multiline `if`

```wx
fn run(condition: bool) -> i32 {
    if condition {
        log_a();
    } else {
        log_b();
    }
    calculate()
}
```

The branches are multiline because their sole expressions are terminated. The
outer `if` is non-final and multiline, so it omits its optional separator.

### A match as the result

Matches with arms are inherently multiline in the current formatter:

```wx
fn classify(n: i32) -> i32 {
    match n {
        0 -> { 10 },
        1 -> { 20 },
        _ -> { 30 },
    }
}
```

The match is block-like and therefore prevents the function body from being
flattened. It is also the function result, so it has no trailing semicolon.

### A match used before another result

```wx
fn prepare(n: i32) -> i32 {
    match n {
        0 -> { initialize_a() },
        _ -> { initialize_b() },
    }
    calculate()
}
```

The match is non-final and multiline, so its optional separator is omitted.

### Comments always prevent flattening

```wx
fn answer() -> i32 {
    // Keep this explanation attached to the result.
    calculate()
}
```

Likewise, a trailing comment keeps the block multiline:

```wx
fn answer() -> i32 {
    calculate()
    // Explanation of the result above.
}
```

Separators must continue to render before trailing comments:

```wx
fn run() {
    initialize(); // Required before execution.
    execute()
}
```

### Width-dependent layout

An unterminated, non-block-like tail is merely eligible for flat layout. It
still breaks when the complete group exceeds `max_line_width`:

```wx
fn calculate() -> i32 {
    perform_calculation_with_a_very_long_argument(argument)
}
```

Breaking for width must not add a semicolon to the tail expression.

## Edge cases and explicit decisions

### Empty blocks

- A truly empty block is `{}`.
- An otherwise empty block containing comments is multiline.
- Empty branch blocks do not by themselves force an `if` to break.

### Local definitions

`Statement::LocalDefinition` is never a tail result and is never eligible for
a flat executable block. This note does not require changing the parser's
acceptance of a final local definition without `;`.

For canonical output, the recommended follow-up decision is to always terminate
local definitions with `;`, including when they are last. That is consistent
with their statement-only role, but it should be tested and implemented as an
explicit part of this change rather than falling out accidentally from the
expression rules.

### Direct control transfer

`return`, `break`, `continue`, and `unreachable` are not block-like. When one is
the sole unterminated expression in a block, that block may be flat:

```wx
if failed { return error };
loop { continue }
```

When the user explicitly terminates one, the block remains multiline and the
semicolon is preserved:

```wx
if failed {
    return error;
}
```

The formatter must not special-case their `Never` type. Preserving the AST
separator is sufficient and avoids requiring semantic analysis.

### Grouped or wrapped block-like expressions

The initial rule uses the top-level `Expression::is_block_like()` result. A
grouped expression or a `return` whose operand is an `if` is not necessarily
classified as block-like at its outermost AST node:

```wx
fn f(condition: bool) -> i32 { return if condition { foo() } else { bar() } }
```

This may still be visually dense. Do not broaden the first implementation with
an informal "contains braces" text check. Either accept the top-level rule or
later introduce a separate recursive predicate such as
`ends_with_block_like_expression`, with dedicated examples and tests.

### Struct initializers

`StructInit` is currently block-like. It therefore:

- prevents a containing block from flattening when it is that block's tail,
- can omit its separator in non-final statement position, and
- participates in the flat-versus-multiline outer separator rule.

This behavior should be covered explicitly because it is easy to accidentally
implement the policy only for `if`, `loop`, and `match`.

### Invalid or incomplete programs

The CLI refuses to format AST syntax errors before overwriting a file, but it
does not reject all TIR/type errors. The LSP also needs useful formatting while
a document is semantically incomplete.

For that reason, final-entry separators must be preserved even when removing
one would make a currently invalid program valid. The only separator
normalization in this guide is for non-final block-like expressions, whose
statement role is already fixed by the following entry.

### Configuration changes

Changing `max_line_width` may change a non-final block-like expression from
flat-with-`;` to multiline-without-`;`, or the reverse. This is intentional and
semantics-preserving because the expression remains non-final.

Formatting must still be idempotent for any fixed configuration.

## Recommended formatter architecture: one document tree

The formatter should continue building one document tree and let the renderer
choose its layout from `max_line_width`. It should not build complete flat and
expanded trees for every construct.

The current architecture already has the right basic philosophy. Its gaps are
more specific:

1. Some constructs that should share one decision are currently represented as
   nested independent groups.
2. `measure_flat` treats a `HardLine` as a short prefix instead of declaring
   flat rendering impossible.
3. Conditional punctuation is represented by a syntax-specific
   `IfBreakComma` node rather than a general document operation.

These should be repaired without replacing the single-tree model.

### Keep one tree and give every coordinated layout one owning group

No group policy is necessary if group boundaries express dependencies
directly:

- Content that must flatten and break together is left ungrouped inside one
  owning `Group`.
- Content that may make an independent fit decision receives its own nested
  `Group`.

This is already the reason `build_block_content` exists: `if` uses the
ungrouped branch contents so both branches participate in the complete `if`
group's decision. The same pattern should be applied consistently instead of
adding metadata to `Group`.

The useful invariant is:

> A layout dependency is represented by document-tree ownership, not by a
> flag. A nested `Group` always means an intentionally independent opportunity
> to become flat inside a broken parent.

### Express function dependency through group ownership

The complete function owns one outer group. The function body's brace lines
are ungrouped contents of that function group. The parameter list retains its
own nested group because it is allowed to make an independent decision after
the function as a whole breaks:

```text
Function group
├── Parameter group (nested and independent)
└── Body contents (ungrouped; owned by Function group)
```

This yields all desired cases:

- If the complete signature and body fit, the function group is flat, so the
  body is flat.
- If the complete function exceeds the width, the function group breaks, so
  its ungrouped body contents break with it.
- The nested parameter group then performs its own fit check. It expands only
  when the signature itself needs it.
- If the body contains structural hard lines, the function group cannot be
  flat, while a short nested parameter group can remain compact.

Thus:

```wx
fn function_with_many_parameters(
    first: i32,
    second: i32,
) -> i32 {
    foo()
}
```

and:

```wx
fn f(condition: bool) -> i32 {
    if condition { foo() } else { bar() }
}
```

both arise from ordinary tree structure rather than function-specific renderer
logic.

### Express coordinated `if` branches through the same ownership rule

The complete `if` owns one group. Its branch block contents are deliberately
left ungrouped inside it:

```text
If group
├── Then-block contents (ungrouped)
└── Else-block contents (ungrouped)
```

If the complete inline `if` does not fit, both branches break. If either branch
contains a structural hard line, the `if` cannot flatten and both branches
break. No separate `force_break` calculation needs to duplicate block
eligibility rules.

When a compact `if` is the tail of a containing function, the function group
breaks due to the brace-density rule, but the `if` retains its own nested group.
It may therefore stay compact inside the multiline function body.

### Make flat measurement reject hard lines

Change flat measurement to distinguish a real one-line width from a document
that cannot be flattened:

```rust
fn measure_flat(&self, id: NodeId) -> Option<usize>
```

- `Some(width)` means every node can render on the current physical line.
- `None` means the document contains `HardLine` or `BlankLine`.

A group selects flat mode only when measurement returns a width that fits.
This fixes the existing behavior where measurement stops at the first hard
line and returns the misleadingly short prefix.

### Generalize conditional fragments, not whole layouts

Some output genuinely depends on the mode already selected by the surrounding
group:

- trailing comma in a broken argument list,
- semicolon after a flat non-final block-like expression,
- no semicolon after that expression when its group breaks.

The document tree must represent this dependency somewhere. The minimal
generic operation is a mode-dependent fragment:

```rust
enum Node {
    // ...
    IfMode {
        flat: Option<NodeId>,
        broken: Option<NodeId>,
    },
}
```

The name is illustrative. It could instead be two nodes, `IfFlat(NodeId)` and
`IfBreak(NodeId)`.

`IfMode` does **not** decide whether anything is flat. It reads the mode already
chosen by its surrounding group and renders one small fragment. For the new
semicolon rule:

```text
IfMode {
    flat: ";",
    broken: nothing,
}
```

For the existing trailing-comma behavior:

```text
IfMode {
    flat: nothing,
    broken: ",",
}
```

This remains one tree. It replaces the syntax-specific `IfBreakComma` with a
general pretty-printing primitive rather than adding `IfFlatSemi`.

During `measure_flat`, only the flat fragment contributes width. Therefore the
flat-only semicolon is included in the line-width decision automatically.

### The conditional fragment must be inside the governing group

For a non-final block-like statement, the builder must form one group whose
contents include both the expression and its mode-dependent suffix:

```text
Group(
    block-like expression contents
    + IfMode(flat: ";", broken: nothing)
)
```

Do not append `IfMode` outside an already completed expression group. It would
observe a different mode.

This suggests a builder-level cleanup: formatting functions for group-owning
expressions should construct their ungrouped contents first and apply `Group`
only at the boundary where the caller has supplied any suffix policy. Possible
APIs include:

```rust
struct GroupContents(NodeId);

fn build_block_like_contents(...) -> GroupContents;
fn finish_group(contents: GroupContents, suffix: Option<NodeId>) -> NodeId;
```

The exact types are not important. The invariant is: a construct has one
clearly owned governing group, and layout-dependent fragments live inside it.

### Structural block rules still belong in the builder

The builder decides whether a block uses `SoftLine` or `HardLine` at its brace
boundaries:

- eligible one-expression tail: `SoftLine`, allowing the group to flatten;
- terminated expression, multiple entries, comments, or block-like tail:
  `HardLine`, making flat measurement return `None`;
- empty block: `{}` unless comments force lines.

This encodes formatting possibilities, not the final width decision. Width
remains entirely the renderer's responsibility.

### What can remain

Retain:

- the arena and `NodeId` representation,
- one document tree,
- `Text`, symbols, source spans, concatenation, and indentation,
- `SoftLine`, `Line`, `HardLine`, and `BlankLine`,
- AST-specific builders,
- comment ownership and gap handling,
- configuration and item-spacing behavior.

### What should change or disappear

- Coordinated constructs must expose ungrouped contents to their owning group
  instead of introducing accidental nested groups.
- `measure_flat` returns `None` for unconditional newlines.
- `IfBreakComma` becomes generic `IfMode`/`IfFlat`/`IfBreak` fragments.
- Cross-component `force_break` calculations are replaced by group ownership
  plus structural hard lines.
- Group-owning expression builders expose a clean point for adding
  mode-dependent suffixes inside the governing group.
- `is_huggable` should be reassessed after hard-line measurement is fixed;
  retain its intended style, but remove behavior that only compensates for the
  current measurement bug.

This is an architectural correction rather than a ground-up rewrite of the AST
formatter. It keeps the original philosophy: build one tree describing legal
break opportunities and dependencies, then let the renderer choose from the
configuration.

### Implementation sequence for the single-tree design

1. Make flat measurement return `None` for `HardLine` and `BlankLine`, then
   update group selection and snapshots affected by the bug fix.
2. Establish the group-ownership invariant and make function bodies expose
   ungrouped content to the complete function group, as `if` branches already
   do.
3. Replace `IfBreakComma` with the generic mode-dependent fragment and prove
   existing trailing-comma behavior remains unchanged.
4. Centralize statement-role and block-eligibility classification.
5. Refactor group-owning block-like builders so optional suffixes are placed
   inside their governing groups.
6. Apply the shared owning-group structure to functions and paired `if`
   branches, then implement the new block and semicolon policies.
7. Re-run comment, width-boundary, idempotence, parser, and TIR-preservation
   tests before removing obsolete `force_break` paths.

## Rejected alternative: explicit flat and expanded document trees

The following alternative was considered before settling on the single-tree
design above. It is retained here only to explain the tradeoff; it should not
be implemented for this change. Although explicit alternatives are a valid
pretty-printing model, building a separate flat and expanded document for most
constructs duplicates representation and moves too much layout policy into the
builder.

The rules are implementable with the existing AST. The AST provides:

- entry index and block length,
- `separator.is_some()`,
- `Statement::Expression` versus `Statement::LocalDefinition`,
- `Expression::is_block_like()`,
- block spans and the comment map.

No TIR or type lookup is required. The difficulty is that the current document
model represents layout dependencies indirectly. A clean implementation should
replace that part of the model instead of adding increasingly specific
conditional tokens such as `IfFlatSemi`.

### Core idea: every breakable construct has two explicit layouts

Represent a layout-capable construct as two alternatives:

```rust
struct Layout {
    /// A document guaranteed to contain no physical newline.
    flat: Option<DocId>,
    /// The construct expanded at its own level. It may still contain nested
    /// choices that are free to remain compact.
    expanded: DocId,
}
```

`DocId` is only a proposed clearer name for the current `NodeId`: a small
integer index into the document-node arena. It is not an AST node ID and does
not require a new allocation model.

`flat: None` means the construct is structurally unable or forbidden to render
on one line. Reasons include comments, a terminated sole expression, multiple
entries, or a block-like tail in a containing block.

The arena can continue sharing nodes, so the two alternatives need not
duplicate every subtree. `DocId`s form a DAG just as current `NodeId`s do.

A `Layout` becomes a document through one general choice operation:

```text
choose(layout):
    if flat exists and its full width fits:
        render flat
    else:
        render expanded
```

When a flat alternative contains a nested choice, that nested choice must use
its flat alternative. This makes the flat-width calculation transitive and
guarantees that a selected flat document cannot unexpectedly emit a newline.

### Suggested low-level document nodes

The low-level arena only needs unconditional composition primitives plus one
general layout choice:

```rust
enum Node {
    Text(Text),
    SourceText(TextSpan),
    Symbol { symbol: SymbolU32, width: u32 },
    Concat { start: u32, len: u32 },
    Indent(DocId),
    Newline,
    BlankLine,
    Choice {
        flat: Option<DocId>,
        expanded: DocId,
    },
}
```

There is no need for a separate `LayoutId` or layout arena. `Layout` can be a
temporary builder-level value, and allocating a choice places its two `DocId`s
directly in the ordinary node arena:

```rust
fn choice(&mut self, layout: Layout) -> DocId {
    self.alloc(Node::Choice {
        flat: layout.flat,
        expanded: layout.expanded,
    })
}
```

Names are illustrative. The important distinction is architectural:

- `Newline` is unconditional.
- A flat alternative cannot contain `Newline` or `BlankLine`.
- `Choice` is the only place that asks whether something fits.
- Punctuation belongs directly to the alternative in which it appears.

This can replace the current combination of `Group`, `SoftLine`, `Line`, and
`IfBreakComma`. A trailing comma is no longer conditional punctuation:

```text
flat arguments    = "(" + join(arguments, ", ") + ")"
expanded arguments = "(" + newline
                     + indent(each argument + "," + newline)
                     + ")"
```

The same mechanism handles semicolons without an `IfFlatSemi` node.

### Width calculation should be total and newline-aware

Each flat document should have a computable width. This may be cached on arena
nodes or calculated on demand:

```rust
fn flat_width(doc: DocId) -> Option<usize>
```

- `Some(width)` means the document is physically one line.
- `None` means it contains an unconditional newline and cannot be selected as
  a flat alternative.

This replaces the current behavior where `measure_flat` stops at `HardLine`
and returns the short prefix width. Returning a prefix makes a document appear
to fit even though it will emit a newline, which is incompatible with any rule
that depends on actual flatness.

The flat width must include all punctuation present only in the flat
alternative. In particular, a flat-only outer `;` participates in the fit
decision. An expression that fits without the semicolon but exceeds the limit
with it must select the expanded, semicolon-free alternative.

### Layout composition, not renderer flags, expresses dependencies

The builder should create semantic layouts directly. Important compositions
are described below.

#### Executable block

For one eligible tail expression:

```text
flat     = "{ " + expression.flat + " }"
expanded = "{" + newline
           + indent(expression-as-normal-choice) + newline
           + "}"
```

For an ineligible block, `flat` is `None` and only `expanded` exists. Empty
blocks have a separate flat document `{}`; commented empty blocks have no flat
alternative.

The expanded body uses the expression as a normal nested choice. Expanding the
containing block should not unnecessarily expand an expression that reads well
on one line inside it.

#### Non-final block-like statement

Build the required separator directly into each alternative:

```text
flat     = expression.flat + ";"
expanded = expression.expanded
```

There is no conditional punctuation. The semicolon exists in one complete
layout and not in the other. Its width is naturally included when choosing.

#### Final block-like expression

Do not create the normalization above. Convert the expression layout to its
normal choice and append the source separator, if any, to the result of both
possible layouts. This preserves the statement/result boundary regardless of
which layout wins.

#### `if`/`else`

The flat alternative exists only when the condition and every branch have flat
alternatives:

```text
flat = "if " + condition.flat + " " + then_block.flat
       + " else " + else_block.flat
```

The expanded alternative uses every branch's expanded block. This makes the
branches break together. If the complete flat `if` exceeds the remaining
width, the one choice selects the expanded alternative for all branches.

When an `if` is a block-like tail inside a function, the function body has no
flat alternative, but its expanded body embeds the `if` as a normal choice.
That produces the desired form:

```wx
fn f(condition: bool) -> i32 {
    if condition { foo() } else { bar() }
}
```

The function is expanded while the nested `if` remains compact.

#### Function signature and body

Build the function itself as a layout:

```text
flat = signature.flat + " " + body.flat

expanded = signature-as-normal-choice + " " + body.expanded
```

The flat function exists only when both the signature and body have flat
alternatives and their combined width fits. If it fails, the function selects
`expanded`, which forces the body to expand. Inside that expanded alternative,
the signature remains a normal nested choice:

- if the signature fits by itself, its parameter list stays compact;
- if the signature does not fit, its parameter list expands;
- either way, the body is multiline.

This expresses the desired one-way dependency structurally:

```text
broken signature -> broken function -> expanded body
expanded body    -> signature may still choose its compact layout
```

No parent-mode inspection or special `force_break` flag is needed.

### Separate semantic classification from document construction

Before constructing documents for a block, classify its entries into an
explicit formatting role:

```rust
enum EntryRole {
    TailResult,
    Statement,
}
```

The classification uses only entry position, statement kind, and separator
presence as specified by Rule 1. Document construction then receives the role
instead of rediscovering it through several unrelated conditions.

Likewise, one shared function should classify block structure:

```rust
enum BlockShape {
    Empty,
    FlatTailCandidate,
    Expanded,
}
```

Names may differ, but semantic classification should happen once. Avoid
repeating partial versions of the rule in function bodies, `if` branches, and
bare block expressions.

### What this alternative would retain from the current formatter

The change does not require rewriting the entire AST formatter. Retain:

- the arena/DAG allocation strategy,
- `Text` and operator-to-token mappings,
- symbol and source-span rendering,
- expression-specific AST traversal,
- comment collection and the `push_between` ownership rules,
- configuration handling,
- indentation width and trailing-comma policy,
- item spacing and blank-line policy.

The current comment machinery should construct only expanded alternatives.
Any block containing comments has `flat: None`, so comments do not need a
second compact representation.

### What this alternative would replace

### Replace `Group` plus mode-sensitive line nodes

The current `Group`/`SoftLine`/`Line` model derives an expanded layout by
changing how individual nodes behave. That works for ordinary wrapping, but it
makes dependencies between separate constructs difficult to express and lets
nested groups override parent decisions.

Replace it with explicit `Layout { flat, expanded }` alternatives and a single
general `Choice` operation.

### Replace `IfBreakComma`

Trailing commas should be ordinary text in the expanded list alternative and
absent from the flat alternative. This validates the new architecture on an
existing conditional-punctuation case before using it for block-like
semicolons.

### Remove `force_break` as a cross-component coordination mechanism

A boolean passed into `build_block_content` does not explain why a construct
must break or which related constructs share the decision. Structural absence
of a flat alternative expresses this directly. Shared choices, such as a whole
`if` or function, express coordinated decisions.

### Re-evaluate `is_huggable`

Part of `is_huggable` exists to work around current flat measurement stopping
at a hard line and accumulating indentation through nested groups. The new
newline-aware flat width removes that failure mode.

The aesthetic policy of hugging a single block-like call argument may still be
desirable, but it should be rebuilt explicitly as call layout alternatives,
not retained as a workaround for renderer behavior.

### Do not add syntax-specific renderer nodes

Avoid `IfFlatSemi`, `IfBreakComma`, `FunctionBodyGroup`, or similar nodes. The
renderer should understand documents, widths, indentation, and alternatives;
it should not know what a semicolon, function body, or block-like expression
means. Those are builder-level decisions represented by complete alternatives.

### Hypothetical migration cost

A ground-up dual-document model could still reuse most formatting logic, but
would require a broad migration:

1. Introduce the new document arena and renderer behind tests, retaining the
   existing public `format` API.
2. Port primitive concatenation, indentation, fixed text, symbols, source text,
   and newline handling.
3. Port delimited lists using explicit flat and expanded alternatives. This
   replaces `IfBreakComma` and exercises width selection.
4. Port ordinary expressions and calls.
5. Port executable blocks with entry-role and block-shape classification.
6. Port `if`/`else` as one coordinated layout choice.
7. Port functions as one outer choice with a normal nested signature choice and
   a forced expanded body in the function's expanded alternative.
8. Port remaining block-like expressions and statement separator policy.
9. Port comments into expanded alternatives using the existing ownership
   logic.
10. Remove the old `Group`, mode-sensitive line nodes, `IfBreakComma`, and
    `force_break` paths once all builders use the new model.

During migration, avoid running old and new layout decisions on the same
construct. Each converted construct should have one owner for its alternatives;
otherwise nested independent choices can recreate the dependency bugs this
architecture is meant to remove.

## Required tests

Add formatter tests covering both source variants and idempotence. At minimum:

### Flat-block eligibility

- empty block,
- one unterminated call,
- one unterminated binary expression,
- one terminated call,
- one local definition,
- two short expressions,
- one expression that exceeds `max_line_width`,
- leading, trailing, and inline comments.

### Function signature/body coordination

- short signature plus eligible short body: both flat,
- signature that exceeds width plus otherwise eligible body: both broken,
- signature with parameters forced to break for another reason: body broken,
- short signature plus block-like tail: signature stays compact and body
  breaks,
- short signature plus body containing multiple entries: signature stays
  compact and body breaks,
- width boundaries that differ only by the inline body's contribution.

### Block-like tail prevention

- function body whose result is `if`/`else`,
- function body whose result is `match`,
- function body whose result is `loop`,
- function body whose result is a bare block,
- function body whose result is a labeled block,
- function body whose result is a struct initializer.

### Branch coordination

- two eligible one-expression branches,
- one terminated branch and one unterminated branch,
- one branch with two entries,
- comment in either branch,
- one branch that exceeds the width while the other fits.

### Outer block-like separators

- flat non-final block-like expression, originally with `;`,
- flat non-final block-like expression, originally without `;`,
- multiline non-final block-like expression, originally with `;`,
- multiline non-final block-like expression, originally without `;`,
- final block-like result without `;`,
- final terminated block-like expression with `;`,
- the same matrix for a struct initializer where grammar permits it.

### Semantic preservation

Reparse formatted output and assert:

- every final entry retains its separator presence,
- non-block-like expression roles are unchanged,
- only non-final block-like separator presence may differ,
- diagnostics for final `calculate();`-style unused values are preserved.

Where practical, build TIR before and after formatting for representative
well-typed examples and confirm that separator normalization on non-final
block-like expressions does not change diagnostics or types.

### Configuration and stability

- boundary cases one character below, at, and above `max_line_width`, including
  the flat-only semicolon's width,
- formatting the output a second time produces byte-identical output,
- changing width produces the expected flat/semicolon versus
  multiline/no-semicolon forms,
- custom indentation continues to work.

## Acceptance summary

The change is complete when all of the following hold:

- `{ expression }` is compact only for one unterminated, non-block-like result
  expression that fits and has no comments.
- `{ expression; }` is multiline and retains the semicolon.
- blocks with two or more entries are multiline.
- a block-like tail prevents its containing block from flattening.
- a broken function signature always forces a multiline body, while a
  multiline body does not automatically force a short parameter list to
  expand.
- `if` and `else` branches break together.
- flat, non-final block-like statements end in `;`.
- multiline, non-final block-like statements omit the optional `;`.
- final separators are never normalized across the statement/result boundary.
- formatting is idempotent and does not require type information.
