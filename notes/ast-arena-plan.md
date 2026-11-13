# The AST as an arena

Status as of 2026-11-13, branch `tir-refactor`. Steps 1–3 and 4.1 are done;
the rest is the plan. The decisions under "Design" were taken with the
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
  print the tree through `ast/printer.rs`, which resolves ids into a nested
  S-expression (step 5); `shape()` is that printer.

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
3. **Done.** Keywords classified in the lexer (`Token::Keyword`, one byte);
   the parser reads a name through `expect_name(allowed)`, which accepts an
   identifier or one of the keywords that name something where it is read
   and reports any other as reserved, replacing the `next_expect(Identifier)`
   + `intern_identifier` pairs and four hand-written variants of it. The
   Pratt tables became `starts_expression`, `parse_prefix` and
   `infix_power`; the postfix handlers lost their unused power parameter
   and `BindingPower::Primary` went. Speed-neutral, as measured: the lexer
   pays for the classification (0.64 → 0.80 ms) what the parser saves
   (lex + parse 2.90 → 2.87 ms); the gain is the code (−180 lines). It also
   fixed an inconsistency in the grammar: a function's name could be a
   keyword (`func memory(..)`), read silently where every other item's name
   reports it as reserved; it is now a name like the others.
4. The arena, bottom-up, each with its consumers ported:
   1. **Done.** Types (`TypeExpression`, bounds, constant arguments, type
      arguments). `TypeExpression`, `BoundExpression` and `ConstArgument`
      keep their names and become `Copy` kinds in columns (`TypeId`,
      `BoundId`, `ConstId`, read with `ast.ty(id)`/`type_span(id)` and
      their siblings, at most 24 B each by assertion); a qualified root is
      a `QualifiedRootId`; every list is a `List<T>` read with
      `ast.list(..)`. `PathSegment` is `Copy`, its arguments a
      `List<TypeArgument>` (their extent was its own `args_span` until
      4.4d). A path inside a type, a bound or a constant argument lives in
      the segment column; paths in expressions, patterns and items are
      still `Box<[PathSegment]>` (both read as `&[PathSegment]`). Lists are
      still collected in a `Vec` and written whole (`push_list`); the
      scratch stack comes with `separated` in 4.3. Every file's tree lives
      in one table on `CompilationUnit`, `asts: Vec<AST>` indexed by
      `FileId` and filled as the loader parses each file
      (`compilation.ast(file)`); a `SourceModule` holds only its `file_id`.
      A consumer reaches a tree through the file a type is written in:
      `SemanticsBuilder::ast(file)` over the borrowed table,
      `BodyBuilder::ast()`, `type_site(file, ty)` for a diagnostic's site.
      `Semantics` holds no syntax, so its few methods that read a written
      type's spans (`resolve_type_args`, the argument-count check,
      conformance's `report_type_mismatch`) take the table as a parameter
      and read each span by the file id they already carry, only when they
      need it. wx-fmt's `Builder` and the LSP's completion `Cursor` hold
      the file's tree. Every example builds to
      byte-identical Wasm with identical messages; the two parser snapshots
      now show ids and the columns (step 5 makes them readable again).
   2. **Done.** Patterns. `Pattern` is a `Copy` kind in a column (`PatId`,
      `ast.pattern(id)`/`pattern_span(id)`, 24 B by assertion); `|`'s
      alternatives are a `List<PatId>`, a positional list a
      `List<PatternElement>` and a named one a `List<PatternFieldItem>`,
      where `..` carries its own span. A pattern's path is in the segment
      column. The separators' spans are gone, since no consumer read them
      (wx-fmt prints its own). A binding keeps `mutable: bool` rather than
      the `mut`'s span: the pattern starts at its `mut`, so
      `ast.pattern_mut_span(id)` gives it back, and the kind fits in 24 B.
      TIR's `check_pattern` takes a `PatId` and reads the column. Every
      example builds to byte-identical Wasm, messages and formatting.
   3. **Done.** Expressions, statements and blocks. Each is a `Copy` kind
      in a column (`ExprId`, `StmtId`, `BlockId`; `Expression` at most 24 B
      by assertion, `Statement` 16 B). A block is its statements and its
      `tail`, the last expression written without `;`, which is the only
      thing a statement's `;` ever told a consumer: TIR's block result and
      wx-fmt's `;` read it, and no `;` is stored. `if`, `loop` and function
      bodies hold a `BlockId`; an `else` branch and a match arm's body are
      expressions (an `Expression::Block` with no label, or an `if`). A
      method call is a `Call` (or `NamedCall`) whose callee is an
      `ObjectAccess`, as `x.m::<T>` already was before its call; this
      removed `MethodCall`/`NamedMethodCall` and their boxes, and
      `(x.f)(a)`, whose callee is a tuple, stays a call of the field. A
      member's name is a `SegmentId` into the segment column, since a
      `PathSegment` (28 B) does not fit a kind. A binary node keeps its
      operator's start (`ast.operator_span`); a positional call the `(`'s
      (`ast.arguments_span`), a named call its braces. No separator is
      stored anywhere in these lists: nothing read one but statements'.
      `separated` replaces `SeparatedGroup` for every list that ends as a
      `List` (expressions, named arguments, arms, statements, patterns,
      tuple types, function-type parameters): delimiters are constants
      (`PARENS`, `BRACES`, `BLOCK`), it is generic over the item, and it
      collects into a local `Vec`, so the scratch stack is not built; the
      item-level lists keep `SeparatedGroup` until 4.4. Lists of items that
      are not ids made the plan's single `u32` scratch impossible without
      giving every arm, argument and field pattern an id of its own, which
      nothing needs. Every example and core build to byte-identical Wasm,
      messages and formatting. The retained tree is 27.3 B/token of data;
      the 37.1 measured includes the columns' growth slack (shrinking them
      to fit, tried and not kept, gives the 27.3).
   4. **Done (4.4a).** Items, impl and trait members, `use` trees, type and
      function parameters, struct fields, enum and import entries are
      columns, each kept with its span; attributes, export entries and
      typeset members plain vectors. A list's items are contiguous, so a
      node's id is its position (`ast.ids(list)`, `ast.item(id)`) and no id
      list is stored; `ast.spanned(list)` reads items with their spans. Every
      item is `Copy`: a `Box` became a `List` or an id (a `use` tree's rest
      is a `UseTreeId`), so the tree has no drop glue left. The file's items
      are `ast.root`. `Separated` and `SeparatedGroup` are gone: every
      delimited list goes through `separated`, an item that ends in a block
      needing no separator (`ListItem::ends_in_block`). No separator is
      stored; wx-fmt writes `;` after every import entry, the last one too.
      `Spanned<SymbolU32>` stays for names. TIR still held `&'ast` item
      references in `AstEntry`, taken from the lists, until 4.4b.

      **4.4c, done.** The finished tree and its builder are two types:
      `AST` holds boxed slices fitted to their contents and only reads;
      `AstBuilder`, private to the parser, holds the vectors and every
      `push_*`, and `finish` turns one into the other. The parser keeps
      `file_id` and its diagnostics beside the builder, so reading what it
      built and reporting are separate borrows, and reads the builder's
      vectors directly. `Parser::parse` returns `Parsed { ast, comments,
      diagnostics }`, and `CompilationUnit` keeps the three in separate
      tables by file (`ast`, `comments`, `parse_diagnostics`): the checker
      reads only trees, the formatter and the editor also the comments.
      The tree header is 792 B (was 1232), and the retained tree loses the
      vectors' growth slack (36.4 to 25.0 B/token) for about 900 shrinking
      reallocations.

      **4.4d, done.** `PathSegment` drops `args_span` (28 to 20 B; the
      segment column is the tree's second largest, after expressions): where
      a segment's type arguments are written is read from the tree,
      `ast.type_args_span(segment)`. Only the "type arguments not allowed"
      reports and editor completion read it, so `PathResolver` and those
      reports are given the trees. Retained 25.0 to 23.2 B/token. Storing a
      block's statements in place of `stmt_lists` was measured too and left
      out: that list is under 1% of the tree.

      **4.4b, done.** TIR's `AstEntry` names its node by id (`ItemId`,
      `TraitItemId`, `ImplItemId`, and the new `EnumEntryId` and
      `ImportEntryId`) and has no lifetime; a reader takes the node from the
      entry's file (`ast.item(id)`), and `SemanticsBuilder::ast_entry`
      replaces `ast_node`, since a node alone no longer says which tree it is
      in. `SemanticsBuilder` keeps `'ast`: it still borrows the trees.

   The old and new forms coexist inside `Ast` while a step is in flight.
5. **Done.** The snapshot printer, `ast/printer.rs` (test-only): a `Sexp`
   (an atom or a list) printed flat, for one-line assertions, or wrapped at
   a width, for snapshots; and a `Printer` that builds one from the tree.
   Items, statements, expressions and patterns are S-expressions, the type
   level (types, bounds, constant arguments, paths) canonical source text,
   literals as written, no spans. `shape()` and the pattern renderer are
   the printer now, and the two snapshots print the tree instead of
   serializing its columns; `top_level_items` covers every item form and
   statement kind.
6. Revisit: error nodes instead of `Err`; a byte-based lexer instead of
   `Chars` (the lexer is a fifth of the time) if the numbers still call for
   it.

## Results

| | before | after step 3 | after 4.1 | after 4.2 | after 4.3 | after 4.4a | after 4.4c | after 4.4d |
|---|---|---|---|---|---|---|---|---|
| lex | 0.64 ms | 0.80 ms | 0.81 ms | 0.80 ms | 0.82 ms | 0.82 ms | 0.81 ms | 0.80 ms |
| lex + parse | 2.90 ms | 2.87 ms | 2.69 ms | 2.68 ms | 2.44 ms | 2.36 ms | 2.39 ms | 2.34 ms |
| drop tree | 0.48 ms | 0.49 ms | 0.35 ms | 0.34 ms | 0.07 ms | 0.03 ms | 0.03 ms | 0.03 ms |
| allocations/token | 0.86 | 0.86 | 0.72 | 0.72 | 0.49 | 0.45 | 0.48 | 0.48 |
| retained bytes/token | 49.2 | 49.2 | 38.2 | 37.1 | 37.1 (27.3 data) | 36.4 | 25.0 | 23.2 |
| expression node | 80 B | 80 B | 48 B | 48 B | 24 B + 8 B span | 24 B + 8 B span | 24 B + 8 B span | 24 B + 8 B span |
| item | 104 B | 104 B | 104 B | 104 B | 104 B | 64 B + 8 B span | 64 B + 8 B span | 64 B + 8 B span |

The expected outcome, an estimate to be checked against this table: parsing
about 1.6–1.9 ms, dropping near zero, the retained tree about a third of its
size, and a markedly smaller parser once the drop glue is gone.
