# `<<` opening a generic argument list

Status as of 2026-10-29, branch `tir-refactor`: open bug, not fixed. Pinned
by two `#[ignore]`d tests in `crates/wx-compiler/src/ast/tests.rs`
(`a_type_argument_list_may_open_with_a_qualified_type`,
`every_generic_argument_site_may_open_with_a_qualified_type`); run them with
`cargo test -p wx-compiler -- --ignored`.

## The bug

A generic argument list whose first argument is a qualified type lexes its
two `<` as one `<<` token (a shift). Every site that opens an argument list
checks for `<` only, so the list is left unparsed:

| Source | Parser reports |
| --- | --- |
| `x: Is<<A as B>::C, D>` | missing separator, unclosed delimiter |
| `x: m::Is<<A as B>::C>` | same |
| `local p: Is<<A as B>::C> = 0` | missing initial value |
| `g::<<A as B>::C>()` | invalid namespace |
| `x.m::<<A as B>::C>()` | invalid namespace |
| `P::<<A as B>::C>(..)` | invalid namespace, invalid item |

A type that itself starts with `<<` already works
(`<<A as B>::C as D>::E`): the type parser splits the token
(`Lexer::split_double_left_arrow`, the `Token::DoubleLeftArrow` arm of the
type expression parser). Writing a space (`Is< <A as B>::C>`) or parentheses
(`Is<(<A as B>::C)>`, a one-element tuple being its element) works around it.

Found while writing `StackValue` tests: TIR's harness reported only the
follow-on "struct `Is` takes 2 generic arguments but 0 generic arguments were
supplied", because `test_case!` does not assert a clean parse
(`checked_case!` does).

## The fix

- `parse_type_args` accepts an opening `<<`: split it, the first `<` opens
  the list, the second (left in `peeked`) starts the first argument.
- The sites that open an argument list on `<` also open it on `<<`
  (`ast/mod.rs`, at the time of writing): the type path walks
  (`parse_type_path`, `parse_type_path_from`) and the turbofish sites (value
  paths, expression paths, `x.m::<..>` / `f::<..>` type application, pattern
  paths).

The turbofish sites are unambiguous: nothing but an argument list follows
`::`, so `::<<` can only open one.

## The catch, gone

The catch was a cast followed by a shift: after `x as u32`, `<<` had to stay
a shift (`(g as u32 << 8)` in `examples/raycaster`), so the type path parser
could not open arguments on it unconditionally. Casts were removed
(2026-10-29), and no other position puts an expression's `<<` right after a
type: an ascription's type ends at its element's `,` or `)`. So the fix above
applies everywhere, with no exception.
