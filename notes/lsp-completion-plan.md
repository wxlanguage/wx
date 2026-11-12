# LSP completion

Status: steps 1 to 3 done (2026-11-12, branch `tir-refactor`); the rest
planned.
Supersedes `lsp-completions.md`, a session log from the removed `wx-lsp-next`
crate, kept for history.

## Principle

**Completion never decides anything the checker doesn't.** It reads what
checking recorded, asks the checker's own lookups whether a candidate
resolves, and offers nothing where the checker would require more from the
user. Every rule below follows from this one: there is no second copy of
visibility, shadowing, ambiguity, the prelude or the method-call rules in
the LSP.

## What the old server did, and what carries over

The completion in `crates/wx-lsp/src/completion.rs` (removed in `34f9397`;
read it with `git show 34f9397^:crates/wx-lsp/src/completion.rs`):

- classified the cursor from raw text (`classify_context`: identifier,
  after `.`, after `::`, after `:`, or nothing against a lone `:`);
- listed locals from the innermost body scope containing the cursor up;
- prefix-searched a name-sorted `SymbolIndex::global_definitions`, with
  visibility approximated by `visible_namespaces` (own module, its globs,
  every ancestor);
- completed `X::` for a one-segment `X` only, resolving it again
  (`resolve_bare_name`, "first visible match");
- never implemented `x.` (`DotAccess => vec![] // TODO`).

Kept: locals ranked before items (`sort_text` prefixes), a snippet
`name($1)` for a function with parameters, nothing offered against a lone
`:` (as rust-analyzer does), one item-to-`CompletionItemKind` mapping.

Dropped: the text classifier (comments, strings, `a.b::c` and generics
defeat it), the symbol index, and every re-implemented lookup.
`visible_namespaces` would be wrong today anyway: lookup does not climb to
enclosing modules, and core is a prelude tier.

## What the checker already has

| Need | Where |
|---|---|
| What `a::b` before a `::` means | `NameResolutions`: every resolved segment is recorded, so `Semantics::symbol_at` on the prefix's last segment answers it, at any depth |
| The names of a scope | `ScopeTable.symbols.bindings` (by `BindingKey`, whose tier is the type/value split), `glob_imports`, the core prelude |
| The members of a type | inherent impls (`ImplDispatch::inherent_candidates` + each impl's `bindings`), traits (`Semantics::trait_candidates`), bounds (`ClauseTables::declared_traits`), struct `field_names`, an enum's namespace |
| Body scopes | `Body::scopes`: span, parent, label, kind (`Static` cuts locals off) |
| Type parameters | `GenericEnvArena::param_names` along the env chain |
| `break :` labels | `Scope::label` on the ancestor scopes |
| Named arguments, `f({ \| })` | the callee's resolution, then the function's parameter or struct's field names |

## Decisions

### 1. An unfinished name is the error symbol (done)

`x.` and `a::` with no name after them parse as the access or the path with
`PathSegment::missing` in place of the name: `Keyword::Error.symbol()` at
the empty span right after the `.` or `::`. The parser reports it once and
leaves the next token alone, so a `}` still closes its block and the next
statement still parses. It follows the precedent of a package instance
without `as` (`ast/mod.rs`, `decls.rs`'s early return on the error alias).

- A keyword is never a member, and after a `::` only `super` is
  (`Parser::is_later_segment`): keywords lex as identifiers, so `p.` on a
  line of its own would otherwise read the next statement's `local` as its
  member and lose that statement.
- Covered: member access (field, method), expression paths, pattern paths,
  type paths. Not yet: a bound's path (`parse_type_path`), `<T as Tr>::`,
  `expr::` after a non-path (`parse_type_application_expression`), use
  trees.
- The checker selects nothing for a missing name and reports nothing more:
  `PathSegment::is_missing` is checked where a lookup's failure is reported
  (`PathResolver`'s walk, `type_member_found`, `select_member`,
  `select_field`). The expression is `ExprKind::Error`, which is silent
  downstream; `symbol_at` skips the empty span.
- Rejected: splicing a placeholder identifier into the buffer and checking
  it again for each request (rust-analyzer, IntelliJ, and the old note's
  proposal). It costs a second check per request and leaves diagnostics
  wrong while typing; recovery fixes both. A dedicated AST variant was not
  needed: no binding table can hold `<error>`, so every lookup of it already
  finds nothing, and wx-fmt never prints it (formatting refuses a file with
  parse errors).
- A `local` missing its type or its value (`local x: `, `local x: T`,
  `local x = `) keeps the statement, with `TypeExpression::Error` or
  `Expression::Error` in place of the missing part, as a parameter written
  without its type already did. The error node spans the gap where the part
  belongs, up to the next token (left alone), so a cursor in that
  whitespace is in it. `parse_type_expression`'s fallback no longer
  consumes the token it reports; a list's recovery skips it.
- A parameter or a struct field with nothing after its `:` (`y: )`,
  `y: ,`) keeps its binding with a `TypeExpression::Error` spanning the
  gap, so its uses find it and its error type is silent. A type written
  wrong (`x: =`) is still an `Err` the list's recovery skips. A named
  argument's `a:` with no value is kept the same way.
- A missing bound after `:` keeps its owner with `BoundExpression::Error`
  spanning the gap to the next delimiter. The parser reports it once;
  checking adds no diagnostic. Parser and checker tests cover supertraits,
  type parameters, typesets and associated types/bindings.
- Literal kinds now use ordinary type paths (`const_int`, `const_float`, `const_char`);
  braces no longer start a type expression. A missing function result (`-> | {}`)
  keeps a `TypeExpression::Error` spanning the gap, preserving the body for
  checking and offering types in completion. This covers free functions,
  impl methods and trait methods/declarations. Impl type positions also
  offer their implicit `Self`, using the checker's `resolve_impl_self`.
- Known: a name on the next line is still read as the member
  (`p.` then `foo(1);` is `p.foo(1)`); the newline is not significant. The
  server treats a cursor before the member's span as an empty prefix.

### 2. Locals visible at an offset: a scope for the rest of a block (done)

A `local` statement opens the rest of its block, from the statement's end to
the block's, as a scope of its own (`ScopeKind::Remainder`, rustc's
`ScopeData::Remainder`), and declares what it binds there. Every scope then
declares one run of locals (`Scope::locals`: the parameters in the root,
one arm's bindings, one statement's bindings, or none), and a local is in
scope wherever its scope's span covers the offset. `Body::locals_at(offset)`
walks from the innermost scope covering the offset outwards, keeps the first
local of each name, and stops after a `Static` scope: what `lookup_local`
finds, from the scope tree alone.

- The statement's own value is built before its remainder opens, so
  `local x = x + 1` reads the old `x`, which the structure now states.
- Shadowing is nesting: no scope declares a name twice (a pattern binding
  one twice is already an error), so the builder's `(scope, name)` map no
  longer overwrites.
- Branches need nothing: each `if`/`else` block, match arm and loop body is
  a scope, so a remainder inside it ends at its `}`, and siblings never
  overlap.
- An arm's scope spans from the end of its pattern, where its bindings come
  into scope. A scope covers the offsets after its start: a cursor at the
  end of `local a = p.` is still in the statement, not after it.
- A remainder is not a jump target (no label, not a loop), and leaving a
  block's scope closes the remainders opened in it, since `leave_scope`
  returns to the left scope's parent.
- Rejected: an offset per local (`visible_after`), chosen differently at
  each kind of declaration and checked against nothing, with shadowing left
  to declaration order; and deriving that offset from the declaring
  statement, the same offsets through a reverse map.
- Inside a literal's elements (a `Static` scope) `locals_at` stops at the
  boundary: an outer local is out of reach there. The checker's lookup
  still finds it (and reports E2140, `build_path`), so it hides an item of
  its name, and the language keeps that rule (`notes/static-data.md`: the
  name must not silently mean an item). Completion follows the checker's
  order one candidate at a time: an item candidate is dropped when
  `Body::local_named_at(offset, name)`, the local a name written there
  refers to, crossing static data, finds one; only otherwise does the
  scope lookup decide. Both queries share one walk of the scope chain.

### 3. Names in scope: `Semantics::names_at` (compiler side done)

The compiler answers "what can a bare identifier written here mean", in
the terms `symbol_at` answers "what does this one mean": `names_at(owner,
offset, tier) -> Vec<(SymbolU32, Definition)>`. The server only renders
(kind, detail, snippet) and filters by the typed prefix.

- Finding the declaration at the cursor is the server's, from the AST it
  walks anyway: the walker names it by the one span of it the checker
  keeps, an item's name (a member's included) or an impl's target path,
  and the server looks that up exactly (`Snapshot::declared_at` in
  `definitions`; `impl_with_target` in an index of `Semantics::impls()`,
  built once per build). `Semantics::body_of(declaration)` gives its body.
  The compiler keeps no item spans and no index by offset; an earlier
  `BTreeMap` of bodies by span ("the last body starting before the
  offset") was dropped for this: exact, and no edge rule for an
  initializer.
- `Semantics::owner_scope(owner)`: the `LexicalScope` a body is checked in,
  now also what checking itself uses for functions, constants and globals
  (it replaced three hand-built copies and `const_scope`).
- The order is the checker's, one candidate at a time. Value tier: the
  usable locals (`locals_at`), then items a local does not take
  (`local_named_at`). Type tier: the type parameters along the env chain
  (each kept when `GenericEnvArena::resolve` finds that one, so a nearer
  one hides it), then items no parameter takes. A function is listed in
  both tiers: it is a type of its own too.
- Items: candidate names from the scope's bindings, the namespaces its
  globs reach, and the core prelude (a superset), each kept when
  `Declarations::lookup_unqualified` finds it, unambiguously, and it is
  accessible from the scope. `lookup_unqualified` is the first segment of
  every path (own scope, then the prelude), extracted from
  `PathResolver::try_resolve_path`, which now calls it, so the prelude rule
  is written once.
- In a signature, `names_in_signature(declaration, tier)` lists the same
  minus locals, in the scope the signature is read in (`signature_scope`:
  the declaration's namespace and its generic env, a function's, struct's,
  alias's, trait's, constant's or impl's; the root's for the rest). An
  associated type is read in its trait's or impl's scope, which the walker
  passes. `names_at` and it share `scope_names`.
- Found while testing: a glob brings in a private item of the module it
  names (`mod helpers { func private() {} } use helpers::*;` lets the
  parent call `private()`; Rust rejects it). That is the checker's
  lookup, which `names_at` follows; to be fixed there, not here.

### 4. The receiver of `x.|`: from the AST and the body, by span

The server walks the module's AST to the `ObjectAccess`/`MethodCall` at the
cursor (the same walk gives the context: expression, type, pattern, label,
named argument) and asks the body for the operand written at the object's
span: `Body::operand_with_span`, an expression if one has exactly that span,
else a place. A place-only receiver exists (`p.inner.|` through a pointer),
and `build_field`'s synthetic `Deref` place reuses the pointer's span, which
is why expressions are preferred; tests pin both cases.

Rejected: the checker recording every member site (a second table next to
`NameResolutions`, filled for every access for one consumer); recording
failed sites in `NameResolutions` (every reader would skip the new
variant); keeping the receiver in the error node (covers only the failed
case, and `p.fo|` resolves when `fo` exists).

### 5. Members: list, then validate through the real lookup

List candidate names cheaply (inherent impls' bindings, `trait_candidates`,
the traits of declared bounds, fields), then keep each one the checker's
by-name search resolves, uniquely and accessibly, and the method-call rules
allow (no auto-deref; through a pointer only a pointer `self`; an exclusive
pointer may call a `self: M::&Self` method; fields through one pointer).
The same rule serves item names: candidates from the scope's bindings, its
globs' targets and the prelude, each kept when `Namespaces::lookup` from
that scope finds it.

What it takes: the bound-member search (`resolve_bound_member`,
`declared_bound_member`) is on `SemanticsBuilder` only because it forces
signatures (`prepare_declarations_of`); split that out so the search is a
`Semantics` method the builder calls after forcing and the server calls
after the sweep, when every signature is resolved. Access checking
(`check_member_access`) likewise reports as it decides; split the decision
out. Queries normalize, so the server lends `&mut Semantics`; they never
emit, so only caches change. Rejected: a second, listing search (two
searches to keep in agreement), and keeping the builder alive (it borrows
the AST entries; `Semantics` owning everything is the design).

### 6. Receivers without a type yet

A receiver whose type `needs_context` (`(5).`, `'a'.`, `"hi".`, `[1, 2].`)
offers nothing, as the checker requires an annotation there (E2002). A
receiver with holes (`Layout<_>`) offers inherent members only, which is all
`select_inherent_with_holes` would select. Later: a code action on E2002
that inserts the ascription.

## Steps

1. **Done.** Parser recovery with `PathSegment::missing`, the checker's
   silence on it. Tests: `ast/tests.rs` ("Unfinished member accesses and
   paths"), `tir/typecheck.rs` (`a_missing_member_is_reported_once`,
   `a_missing_path_segment_is_reported_once`,
   `checking_goes_on_after_a_missing_name`).
2. **Done.** Remainder scopes and `Body::locals_at`. Tests in
   `tir/body.rs`: `locals_at_agrees_with_the_checker` (at every local use
   the checker resolved, `locals_at` offers that local for its name), and
   statement order, branches, arms, literals, outside the body.
3. **Done.** Compiler:
   `names_at`, `names_in_signature`, `names_in`, `body_of`, `impls`,
   `owner_scope`, `lookup_unqualified`, `local_named_at`, `labels_at`
   (tests in `tir/resolutions.rs`, `tir/body.rs`). Server
   (`wx-lsp/src/completion.rs`): a walker written for completion alone (no
   general AST visitor until the AST is an arena) that descends to the node
   at the cursor, finding each level's child by a binary search of its
   siblings (in source order, not overlapping; every list element carries
   its own span, a type parameter's and a `where` binding's included, and
   a path segment's covers its type arguments), and answers what can be
   written there and in which declaration's signature or body, or nothing
   (a comment, a declaration's own name, a literal, a member, a segment
   after a type, a `use`, an `export`); a
   name written, an error node the parser kept, the room between a block's
   statements and between a list's elements are positions; the first
   segment of a longer path is a type, as `try_resolve_path` reads it.
   Items: label, kind (as semantic tokens colour it), detail from
   `hover::signature`, locals and type parameters sorted first. Tests in
   `wx-lsp/src/tests.rs` ("Completion").
   Paths after `::`: the segment before the cursor's is read with
   `symbol_at` (as checking resolved it), and `Semantics::names_in(
   declaration, prefix, tier)` lists what the walk's lookup finds in the
   namespace it enters (a module, a package, an enum's variants),
   accessible from where the path is written; a prefix that is a type gives nothing, its members being step 5's.
   A module's `self`, `super` and `package` are listed: they are bindings
   of its own, and `shapes::super::x` resolves. Labels: `break :` and
   `continue :` with no name keep the jump, the error symbol in place of
   the label (`Parser::parse_label`, now shared by all four), which the
   checker neither declares nor looks up; `Body::labels_at` gives the
   nearest label of each name with its `LabelKind`, and a `continue` is
   offered loops only. Signature positions: every type in a declaration's
   header (parameters, results, fields, bounds and their bindings' types,
   an alias's body, a typeset's members, an impl's trait and target, an
   associated type). `NameUse` filters the type tier by context: types for
   annotations and associated type defaults; traits or typesets for bounds
   and `<T as X>`; declared traits only for `impl X for T`. Namespaces are
   also offered to start or continue a path. Missing supertraits
   (`trait X: | {}`) offer bounds; an associated type default (`type Item = |`)
   offers types, including `Self`, and excludes traits. LSP tests cover both.
   Named arguments: inside a call's braces (a call's
   arguments are spanned by their delimiters, so a list not closed yet
   offers nothing), the name at the cursor or one not written yet is one of
   `Semantics::argument_names` (`typecheck/calls.rs`, read off
   `CallTarget::param_names`, as the checker matches them: a trait impl's
   function by its declaration's names, a struct by its fields, nothing for
   a target with an unnamed parameter), for the callee as checking resolved
   its last name, minus the names written already and, in `x.m({ .. })`,
   the receiver; after a name's `:` is a value (`a:` with no value is an
   error node, as `local x =` is). A function or a constructor in a value
   position inserts its call (`name($1)`, `name()` with nothing to give)
   when the client takes snippets (`ClientConfig`, from `initialize`) and
   no `(` follows. Open: the type
   tier lists every function, core's intrinsics included, since a function
   is a type of its own; correct, and noisy. Open: a value position offers values only, so `Ord|` does not
   offer the enum `Ordering` that a path could start with. A block's
   statements carry the span of their braces, so the room inside a
   keyword block starts at its `{`, not at `block`.
4. `Body::operand_with_span`, with the `Deref` and place-only tests.
5. The member search split; `x.|` completion.
6. Later: ranking by the expected type (the checker has `Expected` but does
   not keep it), `completionItem/resolve` through `hover::signature`, the
   E2002 code action.

Validation (2026-11-12): 1546 compiler tests pass (2 ignored), 80 formatter
tests and 63 LSP tests pass. `wx check` passes for 28/29 examples; `arena`
remains the documented unfinished experiment. Strict workspace Clippy fails
on existing compiler lints (dead code, argument counts and needless borrows).
`cargo check --workspace` still fails on the legacy `wx-compiler-wasm` API.
