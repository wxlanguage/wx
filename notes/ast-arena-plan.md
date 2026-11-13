# The AST as an arena

Status as of 2026-11-13, branch `tir-refactor`. Steps 1 and 2 are done; the
rest is the plan. The decisions under "Design" were taken with the
recommendations below and can be revisited as the port shows what they cost.

## Why

The AST is the last tree-shaped IR: `Box<Spanned<Expression>>` children,
`Box<[Separated<Spanned<T>>]>` lists, a `Vec` per path. TIR's `Body` and MIR
are arenas already (columns of `Copy` kinds with typed `u32` ids, lists as
ranges into a side vector, children before their parent), and the AST should
read the same way to its consumers: the checker (`tir/decls.rs`,
`tir/signatures.rs`, `tir/typecheck*`), wx-fmt and the LSP.

Measured with `benches/parser.rs` (release, best of 300) over the core,
`examples/` and `doom/`: 44 files, 186 KB, 33.9k tokens.

| | |
|---|---|
| lex | 0.64 ms (19 ns/token, 290 MB/s) |
| lex + parse | 2.90 ms (86 ns/token, 64 MB/s) |
| dropping the tree | 0.48 ms (14 ns/token) |
| allocations | 21.4k + 7.8k reallocations (0.86/token), 3.6 MB requested |
| retained tree | 1.67 MB (49 B/token, 9x the source) |
| node sizes | `Spanned<Expression>` 80 B, `TypeExpression` 72 B, `Statement` 64 B, `Item` 104 B, `PathSegment` 32 B |

Where the parser's time goes (measured on a scratch copy, not kept in the
bench):

- **Allocation, about a third.** With a bump allocator swapped in for the
  parse, lex + parse went from 3.50 to 2.38 ms and dropping the tree from
  0.50 to 0.17 ms. The most frequent allocations are the 80 B boxes of
  `Spanned<Expression>` (9.4k), and then, for every one-segment path such as
  `foo`, a `Vec<PathSegment>` grown to capacity 4 (128 B) and shrunk back to
  one segment (32 B): two allocator calls and a copy for the most common
  expression there is. A quarter of all allocator calls are a `Vec` growing
  or shrinking.
- **Moving large values.** An 80 B `Spanned<Expression>` or 104 B `Item` is
  copied through every `Result` return and again into `Box::new`; the parse
  functions carry 100–300 16-byte vector moves each.
- **Drop glue.** Every `?` has to drop the half-built boxes above it: 283
  `panic_in_cleanup` and 142 `_Unwind_Resume` call sites in the parser.
- **Keyword lookup, about a tenth.** `Keyword::try_from(&str)` costs about
  10 ns and runs 0.72 times per token, since the same identifier is
  classified again by `nud_lookup`, `peek_keyword`, `is_keyword` and
  `intern_identifier`. `nud_lookup` is called as a predicate ("can this token
  start an expression?") at 9 sites, each of which runs the keyword match on
  an identifier for nothing.
- Interning is about 16 ns per identifier with foldhash, already a good
  hasher; keep it.

What is **not** a cost: the function pointers. The parser has 17 indirect
call sites in all, two in `parse_expression` (the nud and led handlers),
reached about 0.4 times per token; a `match` on a dense enum compiles to a
jump table, an indirect branch too, and oxc dispatches every byte through a
256-entry table of function pointers on purpose. `SeparatedGroup` has 5
instantiations (2.4k instructions), since its handler is a pointer and not a
generic closure.

## What oxc does

Read from source (`oxc_parser`, `oxc_ast`, `oxc_allocator`, November 2026):

- The lexer classifies keywords once (its `Kind` has a variant per keyword);
  the parser never compares strings. **Adopted.**
- AST types have no `Drop`; generated layout assertions pin their sizes
  (`size_of::<Expression>() == 16`). **Adopted**, as TIR's `ExprKind <= 24`
  assertion already does.
- A list records its trailing separator only, not one per element.
  **Adopted** (see "Separators").
- A list is allocated once at its final size: `collect_list` buffers the
  first elements on the stack before it allocates. **Adopted in Zig's
  form** instead, a scratch stack (see "Lists").
- Parse functions return a node, never a `Result`, with a fatal-error flag.
  **Deferred** (step 6).
- Not adopted: a pointer tree in a bump arena (`Box<'a, T>`, which puts a
  lifetime on every node and every consumer; wx's own IRs use index
  columns), the packed `u128` token, the perfect-hash keyword table and the
  unsafe SIMD byte search. They buy speed wx does not need at the price of
  the readability it does.

## Design

One `Ast` per file, as now (the LSP reparses a file at a time).

**Columns where the volume is.** Expressions, types, patterns and path
segments each live in a column pair, `kinds: Vec<XKind>` and
`spans: Vec<TextSpan>`, addressed by an `index_newtype!` id (`ExprId`,
`TypeId`, `PatId`, `SegmentId`). A kind is `Copy`, has no `Drop`, holds
children by id and lists by range, and is pinned by a size assertion (24 B
at most, as TIR's; 16 B where it fits). A child is pushed before its parent,
as in TIR. A binary node keeps its operator's start only
(`Binary { op, op_start: u32, left, right }`): the operator's length follows
from the operator.

**Plain structs where it is not.** Items, impl and trait members, function
parameters, struct fields, enum variants, attributes and `use` trees number
a few hundred per file; they stay ordinary structs in a `Vec` each, holding
ids into the columns. Splitting them into columns would cost readability and
save nothing measurable.

**Lists.** A list is a `Range { start, len }` into a typed side vector
(`expr_lists: Vec<ExprId>`, `type_lists`, `pat_lists`, `segment_lists`, …).
Lists nest while they are parsed (a call's arguments contain calls), so the
ids of the list being parsed go onto one `scratch: Vec<u32>` shared by every
list; at the closing delimiter `scratch[mark..]` is copied once into the
side vector and truncated. Every id is a `u32`, so the delimited-list parser
is one non-generic function,
`separated(&mut self, Delims, fn(&mut Parser) -> Result<u32, ()>)`, where
`Delims` is a constant (`PARENS_COMMA`, `BRACES_SEMI`, …) holding the open,
close and separator tokens and the separator rule (always required, or not
after a block-like statement or item, read off the node's kind). This
replaces the five-field `SeparatedGroup` literal written at about 30 sites.

**Separators.** `Spanned<T>` and `Separated<T>` go: the span is in the
column. Nothing outside the parser reads a separator's span (wx-fmt and
`tir/typecheck/blocks.rs` only ask `separator.is_some()`), so a statement
keeps a `has_semicolon` bit and a list a trailing-separator bit. A tool that
needs the `,` itself (a "remove trailing comma" fix) finds it after the last
element's span.

**Spans, not token indices.** Zig's AST stores a 4-byte token index instead
of an 8-byte span over a pre-lexed token array. Keep spans: they match TIR's
columns and every diagnostic, and the streaming lexer with its `>>`/`<<`
splitting stays as it is.

**Errors.** Parse functions keep returning `Result<Id, ()>` ("`Err` means it
has already reported"), so `separated`'s skip-to-separator recovery and the
`PathSegment::missing` convention carry over unchanged. Error nodes in place
of `Err` are step 6.

**Keywords in the lexer.** `Token::Keyword(Keyword)` beside
`Token::Identifier`, classified once per token. It still fits in one byte
(the keyword's unused values are the niche for the other variants), which a
size assertion pins. `self`, `Self`, `super` and `_` are keywords that also
name things, as now.

**The Pratt loop.** The two tables of function pointers become a `match` for
the prefix, `infix_power(token) -> Option<BindingPower>` for the loop, and
`starts_expression(token) -> bool` for the 9 sites that only ask.

**Modules.** `ast/mod.rs` holds the tree (and, after step 4, the arena and
its accessors), `ast/lexer.rs` the tokens and the lexer, `ast/parser.rs` the
parser and its `report_*` diagnostics; `ast/tests.rs` stays as it is.

## Consumers

- **TIR.** `AstEntry<'ast>` holds `&'ast ast::Item` and friends; it holds
  item ids instead (with the file's `Ast` reached through the package), and
  body building reads `ast.expr(id)`. Whether `SemanticsBuilder<'ast>` keeps
  its lifetime (it still borrows the `Ast`s) is decided when it is ported.
- **wx-fmt.** Walks the tree through the same accessors. `CommentMap` does
  not change.
- **LSP.** `completion.rs` walks the tree; `hover.rs` touches it once.
- **Parser tests.** The two snapshots (`top_level_items`, `use_tree_forms`)
  serialize the tree; they need a printer that resolves ids into a nested
  tree, so a snapshot still reads as one. `shape()` is rewritten over ids.

## Steps

Each step is one commit with every test passing and `wx-cli`/`wx-lsp`
building.

1. **Done.** `benches/parser.rs`: timing of lexing, parsing and dropping,
   allocation counts and node sizes over the repository's sources
   (`cargo bench -p wx-compiler --features bench --bench parser`).
2. **Done.** `ast/mod.rs` split into `mod.rs`, `lexer.rs` and `parser.rs`;
   a move only, with `pub(super)` where the parser and the tests reach into
   the lexer. `BracketedRoot` and the operators' `TryFrom<Token>` impls moved
   to the parser, their only user.
3. Keywords classified in the lexer; the Pratt tables replaced by matches.
   Measured on its own.
4. The arena, bottom-up, each with its consumers ported:
   1. types (`TypeExpression`, path segments, bounds, type arguments);
   2. patterns;
   3. expressions and statements, with `separated` and the scratch stack;
   4. items, members and the remaining lists; `Spanned` and `Separated`
      removed; TIR's `AstEntry` by id.

   The old and new forms coexist inside `Ast` while a step is in flight.
5. The snapshot printer (with 4.3 at the latest, when the snapshots' trees
   change).
6. Revisit: error nodes instead of `Err`; a byte-based lexer instead of
   `Chars` (the lexer is a fifth of the time) if the numbers still call for
   it.

## Results

| | before | after step 3 | after step 4 |
|---|---|---|---|
| lex + parse | 2.90 ms | | |
| drop tree | 0.48 ms | | |
| allocations/token | 0.86 | | |
| retained bytes/token | 49.2 | | |

The expected outcome, an estimate to be checked against this table: parsing
about 1.6–1.9 ms, dropping near zero, the retained tree about a third of its
size, and a markedly smaller parser once the drop glue is gone.
