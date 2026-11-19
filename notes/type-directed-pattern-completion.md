# Type-directed pattern completion

Status: partially implemented, 2026-11-19. Remaining proposals below are not
claims that all completion and parser changes are implemented.

Design revision: reuse checked pattern types through exact span lookup, as
other LSP requests already do. An error pattern may retain its known subject
type: `PatternKind::Error`, not an erased type, records failure. Do not add
source-ID mappings, expected-type tables, restriction tables, or a separate
recording mode. The initial root-to-target type walk has been replaced with
checked-pattern lookup. Cursor interpretation stays in
`wx-lsp`; compiler recovery and shared language rules stay in `wx-compiler`.

## Goals and completion policy

Completion should suggest patterns for the value the current position matches,
not enumerate every name that could appear somewhere in a pattern.

| Position | Initial suggestions |
| --- | --- |
| Ordinary pattern expecting enum `E` | All accessible variants of `E`, in declaration order; `_` |
| Ordinary pattern expecting struct `S` | Destructuring of `S`, where accessible; `_` |
| Ordinary pattern expecting a tuple | Tuple destructuring; `_` |
| Ordinary scalar pattern | `_`; no arbitrary constants or invented literal values |
| After an explicit `const` | Compatible constants and paths leading to them |
| Named destructure's field-name position | Its unwritten fields, with instantiated field types |
| Named field's subpattern | Patterns for that field's instantiated type |
| Binding-only context | Binding/destructuring forms; no tests against variants or constants |
| Unknown expected type | Structural suggestions only; no fallback to all in-scope values |

An explicit qualifier still matters. Do not offer a variant of `Other` after
`Other::` when the known expected type is `E`. With no known expected type,
normal completion of an explicitly resolved namespace can remain useful, but
must not invent a type expectation or ignore the pattern category.

Enum variants are a distinct candidate category even though the compiler
represents them as constants. Do not suggest ordinary constants without
`const`, and do not automatically insert that marker in an unmarked pattern.
This includes ordinary associated constants after an unmarked qualifier:
`Point::LIMIT` remains legal source, but it is not proactively suggested by
this policy. An explicitly marked qualified constant pattern is accepted
without a warning; formatting may omit the optional marker.

Display entity names separately from insertion syntax:

- Show `True`; insert `Bool::True` in an unqualified pattern position.
- After `Bool::`, show and insert `True`.
- After `const`, show `True`; insert only the constant name or accessible path.
- Show `Point` as the entity, with destructuring information in its details;
  accepting it inserts the selected destructuring form.

Bare `True` remains a binding under the existing grammar. This plan does not
change the language to make an unqualified variant name a test.

The first implementation should not hide already-covered variants. Coverage
ranking and richer snippets are independent later improvements.

## Current implementation and limitations

The working tree already has an initial implementation of pattern-prefix
completion, recovery for a missing match arm arrow/body, and field completion
immediately before a closing named-pattern brace. Those changes are the
starting point, not tasks to repeat.

`Body::pattern_type_of` now performs exact-span lookup, unwrapping transparent
tuple patterns and selecting the last checked node at a shared span. The LSP
reads existing child types directly, including correctly checked written generic
arguments. Cursor discovery carries destructure ancestors for representation
restrictions; it no longer reconstructs types through them.

The completion provider, checked-type queries, and insertion calculation live
together in `wx-lsp/src/completion/patterns.rs`. Written targets carry only a
pattern ID; only a match-arm gap carries its match expression. Restrictions
are handled separately from the optional expected type, without an expectation
wrapper or a scan through the match's arms.

Empty arm-list gaps still read the checked scrutinee. Prospective positional
insertions still calculate their changed list layout from the checked parent's
type. Their narrow owner/field helper remains conservative about explicit
generic arguments. Invalid arities yield no child expectation when checking
assigned `ERROR`; completion no longer guesses these child types independently.

Relevant ownership boundaries:

- `ast` records written syntax and parser recovery.
- `tir/typecheck/patterns.rs` gives each pattern its expected type and
  determines bindings, field types, alternatives, and restrictions.
- `tir::Body` stores normalized checked patterns for evaluation and lowering.
- `wx-lsp/src/completion.rs` currently walks syntax, queries candidates, and
  formats completion items in one module.

Specific limitations verified against the current code:

1. `parse_pattern_field_item` can discard a field when the pattern after `:`
   is missing. `parse_pattern` can discard an alternative after a trailing `|`.
2. The AST distinguishes bindings and constant paths, but does not explicitly
   retain the written `const` token. Completion infers it by comparing spans.
3. Error recovery previously stored `PatternKind::Error` with
   `TypeIndex::ERROR` even when the subject type was known. Preserve that type
   in the existing checked node; the error kind continues to mark failure.
4. Normalization removes some written wrappers and reorders/expands children.
   A source pattern is not always one checked pattern with the same shape.
5. `check_elements` checks every child against `ERROR` on an arity mismatch,
   even where part of the structural mapping may remain unambiguous.
6. The new `NameUse::Pattern` query is scope-directed, not expected-type-directed.
7. `Body::operand_of` currently joins syntax to checked operands using spans.
   This is an existing limitation, but replacing every expression query is not
   a prerequisite for this plan.

## Proposed parser and AST changes

### Required: retain missing subpatterns

Use the existing `Pattern::Error` representation where a required child is
missing, with a span covering the gap where it belongs. Keep the parent and
leave enclosing punctuation for the owning parser.

Examples:

```text
Packet{ state: <cursor> }
Packet{ state: <cursor>, position }
Status::Ready | <cursor> => ()
Pair(, second)
```

`<cursor>` is an editor position, not WX syntax.

Required behavior:

- A field after a written `:` remains a field with `Some(error_pattern)`;
  `None` continues to mean an actual shorthand binding.
- After a written `|`, retain a missing alternative instead of dropping the
  whole pattern.
- An explicit missing positional entry before a comma retains its position;
  recovery must not shift later children into earlier slots.
- Preserve following arms, siblings, declarations, and enclosing delimiters.
- Report the missing syntax once. An error pattern is not a successfully
  compiled hole or a new language feature.

Do not synthesize a child merely because the cursor could be in an empty
list. `()` and an empty list of fields retain their existing meaning, and a
trailing comma remains a trailing comma. Completion of a vacant insertion
position is a separate query, described below.

Prefer focused pattern recovery over a new boolean mode on the generic
separated-list parser. Every successful recovery must either consume input or
return control to a parser that will consume or close the group; test this at
`,` / `}` / `)` / `=>` / EOF to avoid loops.

### Reassessed: reuse existing syntax for the constant marker

Do not initially extend `Pattern::Constant` with another token field.
Completion already distinguishes an explicit marker by comparing the pattern's
start with the first path segment's start. Verify that parser span invariants
make this reliable, including whitespace/comments and unfinished paths.
Centralize the interpretation rather than duplicating span tests.

Also retain an unfinished `const` path using the existing missing path-segment
representation, so completion can distinguish `const <cursor>` from an
ordinary missing pattern.

If recovery cannot preserve that distinction with the existing representation,
document the failing case and reassess a minimal syntax change. An optional
token offset remains an option, not a prerequisite or an approved layout
increase.

Constraints:

- Preserve the absence of warnings for optional `const` on qualified constant
  patterns and the formatter's canonical omission of that marker. Warnings
  for redundant `const` in other contexts, such as generic constant arguments,
  are outside this change.
- Keep existing AST layouts and the `size_of::<Pattern>() <= 24` invariant.
- Update AST consumers together only if a demonstrated recovery requirement
  actually needs a representation change.
- No new keyword, successful grammar form, or interpretation of bare names.

No further delimiter fields are currently proposed. The existing
`Expression::Match::open_brace` already identifies the empty arm-list region.

## Proposed typechecker and semantic-query changes

### Required: reuse checked patterns by span

The existing syntax cursor walk identifies the written pattern. Look up its
checked counterpart by exact span in its owning body, using a query analogous
to `Body::operand_of`, then read its existing `pat_types` entry.

Define and test normalization rules rather than introducing a source map:

- Transparent single-element tuple patterns unwrap to their child, as
  expression lookup already does.
- Field-packing tuples can share the whole destructure's span. The enclosing
  written pattern is pushed afterward, so prefer the last match for that span.
- Synthetic wildcards may share a rest/enclosing span; they are not independent
  written patterns. Verify that enclosing source nodes win exact-span lookup.
- Never substitute a nearby span or use a pattern from a different body.

For failed source patterns, keep the known subject type on the existing
`PatternKind::Error` node. Test permission/equality checks return success or
failure separately from the subject type. Each checking path constructs its
typed result directly; do not overwrite the type afterward or use a temporary
`ERROR` type merely to suppress compatibility diagnostics.
For unresolved/incompatible constructors, retain the outer expectation but do
not invent expected field types for their children.

Preserve the error kind: exhaustiveness and lowering must not interpret a
concrete type as evidence that checking succeeded. Review those consumers and
test diagnostics as well as retained types. No table or additional checked node
is needed merely to retain a known error-pattern type.

Empty match-arm gaps have no source pattern: use the existing checked match's
scrutinee. Vacant positional insertions use the checked parent's layout and
the prospective list shape, not a whole root-to-target type reconstruction.

Locals should read the checked pattern type, not blindly use an initializer's
type: `build_local` receives a separate `local_ty` from `build_initial`.
Unknown cases return no answer without rechecking annotations or adding tables.

Lookup does not rerun checking, declare bindings, or emit diagnostics.

An outer type can be known while some generic arguments are not. Preserve
that partial knowledge: a known struct owner may still support destructuring
and field-name completion even if one field's expected type remains unknown.

### Required: expose restrictions without changing language rules

Expected type alone is insufficient. A local's pattern cannot test values, and
destructuring an enum's representation permits bindings rather than tests,
even inside a match arm.

Represent the query's context explicitly, for example as match-arm,
local-binding, and enum-representation modes. Keep it distinct from the
checker's binding/alternative tracking and diagnostic suppression state.

Derive restrictions from the ancestors already visited by cursor discovery:
start with match-arm versus local context, then restrict descendants inside
an enum representation identified through existing checked data.
The nearest enclosing `match` alone is not sufficient.
Do not retain per-pattern restriction rows or replay binding/alternative
tracking just to answer completion.

Keep any shared restriction representation focused. Changing `PatternContext`
and its diagnostic state is not required merely to expose a query; refactor
checker state only where it genuinely shares a rule with the query.

Preserve the existing diagnostic distinction between a refutable local
pattern and a test in an enum representation. This is not permission to
replace one diagnostic with the other or change accepted programs.

### Required: share structural mapping, not typechecking

`positional_pattern_gap` lives beside `check_elements` in
`tir/typecheck/patterns.rs` and is re-exported as a narrow TIR operation.
It validates the written count and rest position and returns the element range
covered by `..`. Both checking and prospective insertion use it. Without a rest,
the count must match exactly; it does not provide partial arity-error recovery.

Field-tuple versus individual-field interpretation is expressed directly in
`check_field_list` and the insertion query. No public layout enum or positional
shape object is needed. The LSP's private `PositionalInsertion` represents only
the prospective list and inserted child.

Diagnostics, local declaration, pattern construction, and evaluation stay with
their current owners. Invalid checked children remain typed as `ERROR`; broader
arity-error recovery is a separate change.

Do not type children of an unresolved or incompatible written constructor as
though the user had written the expected constructor instead.

### Small semantic queries used by providers

Use existing normalization and visibility/lookup mechanisms to answer:

- the normalized expected type under the body's assumptions;
- accessible variants of that enum;
- whether that struct is accessible for destructuring and which form it has;
- instantiated field information;
- compatible constants when the syntax explicitly requests a constant;
- an accessible spelling of a candidate definition.

Query names are provisional. These are language/semantic questions, not an API
returning LSP completion items. Queries must not emit new diagnostics or run a
speculative full check for every candidate.

Keep work demand-driven: inspect the target's ancestry and needed fields, not
every pattern or recursively every field type. Reuse existing resolutions,
signatures, substitution, and normalization APIs. Normalization/substitution
may intern types or use existing solver caches; these are completion-time
costs, not evidence that queries are allocation-free. Do not add a completion
cache, eagerly instantiate every field, or evaluate every candidate constant.

Constant compatibility must use WX's rules, including untyped constants and
representability where applicable, rather than equality of display strings or
an ad hoc `TypeIndex` comparison. First audit the existing non-diagnostic
compatibility and constant-value APIs. Do not evaluate constants or run a full
solver/check per candidate merely to filter suggestions. If those APIs cannot
answer cheaply and reliably, describe the unsupported cases and reassess the
filtering policy before implementing new evaluation machinery.

Where vacant-slot layout needs constructor validation, `pattern_owner` currently
combines resolution, type-argument checking, diagnostics, and field
instantiation. It is not directly reusable as a completion query. Extract
only the needed semantic rules, reuse checked resolutions where available,
and report unknown where validation cannot be established without rechecking.

Keep the initial path-spelling implementation bounded: respect an explicit
qualifier and reuse visible names/aliases and existing namespace lookup. Do
not introduce auto-import edits or a project-wide path-search engine as a
prerequisite.

Prefer named destructuring when the struct is fully named; otherwise offer a
positional form. Preserve a form the user has already started. Do not assume
every struct can use the current `Point{ .. }` template.

## Nested patterns and vacant slots

Examples of distinct targets:

```text
match (packet) { <cursor> }       -> the match scrutinee's type
Packet{ state: <cursor> }         -> the field's instantiated type
Packet{ position: Poi<cursor> }   -> the existing subpattern's expectation
Packet{ <cursor> }               -> field names, not value patterns
Pair(first, <cursor>)            -> a prospective positional child slot
```

For nested generic fields such as `Holder<T>{ value: ... }` matched against
`Holder<Status>`, the expectation is `Status`. Substitution and normalization
must use compiler mechanisms, on demand.

An unmarked prefix like `Poi` remains a binding in the AST. Offering to replace
it with a destructuring pattern does not reinterpret it or change what the
compiler accepts.

Vacant positional slots are the important special case:

- With two fields of types `A` and `B`, `Pair(p)` gives `p` the whole field
  tuple `(A, B)`.
- `Pair(_, p)` gives `p` the second field type `B`.
- Consequently, completing the first insertion in `Pair(<cursor>)` is not
  automatically completion for `A`.
- Inserting a second child in `Pair(first, <cursor>)` must use the prospective
  two-child shape, not the type assigned to the previously single child.

A vacant-slot query uses the checked parent's validated structure and applies
the same mapping rules to the prospective insertion shape. It
does not need a fake identifier, a reparsed program, or a second typecheck.
If that shape is ambiguous, avoid a type-specific claim.

Use a small target enum for written patterns, empty match-arm positions, and
vacant child slots. Do not create a general-purpose string-based projection
language. The LSP owns traversal, but must use shared compiler rules rather
than duplicate WX's structural semantics or implement another typechecker.

## Completion responsibilities

Refactor within `wx-lsp`, without requiring a new crate:

```text
completion/
    mod.rs       request setup, provider dispatch, protocol integration
    site.rs      AST cursor walk, syntax context, semantic anchors, edit ranges
    items.rs     labels, details, documentation, insertion forms and text edits
    patterns.rs  type-directed pattern provider
```

The request flow is:

```text
syntax site -> checked-pattern span lookup -> candidates -> edits
```

In particular:

- A pattern site carries its source target and explicit syntax, not just
  `Site::Name(NameUse::Pattern)`.
- Replace the broad unmarked-pattern scope scan. Reassess/removal of
  `NameUse::Pattern` is expected; do not preserve it through compatibility
  flags merely because the first implementation added it.
- Ordinary expression completion retains its behavior in this change.
- Existing name, member, argument, and field queries remain shared compiler
  mechanisms.
- Renderers do not select eligibility or infer context from labels.
- Entity labels, filtering text, replacement ranges, and inserted syntax are
  separate decisions. Do not duplicate existing qualifiers or delimiters.
- No framework of dynamically registered providers or a file per minor case.

## Impact on other compiler consumers

| Area | Expected change | What must remain unchanged |
| --- | --- | --- |
| AST/parser | Focused recovery using existing pattern/path nodes; validate marker span invariants | Existing layouts, valid grammar and binding/constant interpretation |
| TIR checking | Share structural rules, without adding fact-recording work | Types, bindings, diagnostics, safety rules, evaluation order, acceptance of valid programs |
| `tir::Body` / `Semantics` | Focused semantic accessors over existing data; no cursor walk or additional per-pattern/match metadata | Existing normalized pattern arena and backend invariants |
| Formatter | Validate unchanged successful formatting; adapt only if recovery requires it | CLI/LSP agreement and refusal to format parse-invalid input |
| AST printer/tests | Regressions for retained error children | Snapshots regenerated with tests/insta, never edited by hand |
| LSP | Checked-pattern span lookup, cursor/insertion targets, type-directed candidates and edits | Other completion categories and navigation behavior |
| MIR, optimizer, Wasm emission | No planned representation or algorithm change | Generated behavior for valid programs |
| Core/examples/editor submodules | No syntax migration planned | Existing programs and separate editor repositories |

Internal Rust APIs may change where shared helpers require it. No threading of
match source IDs through expression checking is planned. Update all affected
in-repository consumers together, including browser wrappers if they directly
consume an affected API.

Invalid-input diagnostics and retained AST shape can improve, so some existing
recovery assertions may change. List and review those deliberately rather than
preserving diagnostic cascades.

The initial work adds on-demand pattern queries, not source-fact tables.
A complete `ast::ExprId -> Operand` map, replacement of `Body::operand_of`,
and migration of hover/signature-help to it remain a separate follow-up.
Do not hide that larger expression refactor inside pattern completion.

Concrete compiler touch points:

| File | Planned change |
| --- | --- |
| `crates/wx-compiler/src/ast/mod.rs` | No planned representation change; retain layout assertions |
| `crates/wx-compiler/src/ast/parser.rs` | Focused pattern/path recovery; verify marker spans |
| `crates/wx-compiler/src/ast/printer.rs`, `src/ast/tests.rs` | Recovery regressions and consumer adaptation only as needed |
| `crates/wx-compiler/src/tir/body.rs` | Reuse existing operand/declaration queries; expose focused access only if needed, without new tables |
| `crates/wx-compiler/src/tir/typecheck.rs`, `typecheck/blocks.rs` | No planned source-ID plumbing or match/local fact recording |
| `crates/wx-compiler/src/tir/typecheck/patterns.rs` | Own positional validation and expose the narrow rest-gap operation, without source/cursor traversal |
| `crates/wx-lsp/src/completion/patterns.rs` | Read checked types by span; calculate prospective insertion layouts; own restrictions and typed provider |
| `crates/wx-compiler/src/tir/decls.rs`, `resolutions.rs`, `members.rs` | Remove or narrow the first-pass pattern-name category when its broad enumeration is replaced; reuse existing lookup/accessibility |
| `crates/wx-fmt/src/lib.rs`, `src/tests.rs` | Validate unchanged successful formatting; no marker-field adaptation planned |

No change to `tir::lower`, MIR, optimization, or code generation is expected
for these additions. A need to modify their semantics is a reason to revisit
the plan, not an assumed part of implementation.

## Implementation sequence and validation

1. **Query feasibility and cost audit**
   - Establish root-type lookup using existing data, including empty matches
     and annotated locals with bad initializers.
   - Check existing resolution, substitution/normalization, constructor
     validation, and explicit-constant compatibility APIs.
   - Document unknown cases and any missing API before expanding scope.
2. **Parser boundary**
   - Add focused recovery with existing nodes; verify explicit-marker spans.
   - Cover missing named subpatterns, alternatives, explicit positional holes,
     unfinished constant paths, following siblings/arms, and EOF.
   - Verify empty/trailing-comma lists do not acquire phantom children.
3. **Shared structural and expectation queries**
   - Implement checked-pattern span lookup and concrete error-type recovery.
   - Reuse shared compiler positional rules for vacant slots; carry restrictions
     through existing cursor discovery rather than a second type walk.
   - Test queries directly without completion or LSP rendering.
   - Verify a bad target can have a derived expectation without turning its
     checked result into a valid pattern; reject incompatible parent paths.
   - Cover field tuples, tuple-valued fields, `..`, generic substitution,
     replacements versus insertions, and ambiguous/error cases.
4. **Completion boundaries and provider**
   - Separate syntax and rendering without changing unrelated completions.
   - Replace broad pattern enumeration with expected-type-driven candidates.
   - Check enum variants, struct destructuring, explicit constants, field
     positions, qualifiers, visibility, and unknown types.
5. **Integration**
   - Apply completion edits to fixtures and check the resulting programs.
   - Preserve hover/definition queries on unfinished input.
   - Run workspace tests, formatting, Clippy, and a CLI build.
   - Run a release build to validate layout/configuration assumptions.
   - Review compiler storage and hot-path changes: no new source-fact tables,
     checking pass, or AST growth is planned. Compare native check/build time
     and peak memory on representative input if a shared-helper change could
     add meaningful cost; do not claim zero compiler overhead without evidence.
   - Check completion latency on large bodies/deep patterns and repeated
     requests, especially substitution, root span lookup, and constant filtering.
   - For the structural helper refactor, run generated-code execution tests;
     explicitly check/build affected examples if successful behavior or syntax
     changes unexpectedly.

Stop after each compiler-facing step for review if the change requires a
language-rule alteration, additional runtime policy, or a larger IR redesign.
Those are not authorized implicitly by this plan.

## Reassessment summary

| Earlier proposal | Revised decision |
| --- | --- |
| Store expected types/restrictions per written pattern | Reuse checked types by span; carry restrictions during cursor discovery |
| Store validated destructure descriptors | Reuse existing checked destructure structure |
| Record match scrutinee types with source-ID plumbing | Reuse checked scrutinee lookup, including empty matches |
| Add a constant-marker AST field upfront | Verify existing spans/recovery first; defer representation changes |
| Improve child checking on every arity error | Keep checker diagnostics stable; derive unambiguous completion expectations independently |
| Filter constants using unspecified compatibility machinery | Audit cheap existing APIs first; discuss gaps rather than adding eager evaluation |

Remaining feasibility risks are root lookup for erroneous annotated locals,
validation of written generic arguments on incomplete constructors, and
constant representability filtering. These are audit/test targets, not claims
that every necessary non-diagnostic query already exists. Unknown answers are
acceptable initially; any loss in useful completion should be demonstrated
with a fixture before proposing additional retained compiler data.

## Deferred work

- A full expression source map and broader expected-expression completion.
- Retained per-pattern expectations/restrictions/layouts or a match-type table.
  Reconsider only for a demonstrated gap and with explicit cost discussion.
- An extra constant-marker AST field unless existing syntax proves insufficient.
- Broader arity-error recovery changes beyond preserving known error-node types;
  reassess independently with diagnostics and checking tests.
- Another HIR, moving all normalization into a new stage, or replacing the AST.
- A lossless syntax tree, speculative completion parsing, Salsa, or new shared
  ownership/interior-mutability mechanisms.
- Changing WX's positional destructuring semantics to simplify completion.
- Automatic imports, project-wide spelling search, exhaustiveness filtering,
  advanced ranking, or recursive expansion of every nested destructure.
- General completion of newly declared binding names.

The on-demand semantic query boundary should permit later expression-query
improvements, but no unused general-purpose infrastructure is required now.

## References

- [WX compiler architecture](../crates/wx-compiler/README.md).
- [Existing completion rationale](lsp-completion-plan.md); historical syntax and
  implementation claims there must be checked against the current code.
- rust-analyzer revision
  [`b3c8f61b5036e12388787eaacd4775590fd3a036`](https://github.com/rust-lang/rust-analyzer/tree/b3c8f61b5036e12388787eaacd4775590fd3a036),
  reviewed 2026-11-18:
  [completion context](https://github.com/rust-lang/rust-analyzer/blob/b3c8f61b5036e12388787eaacd4775590fd3a036/crates/ide-completion/src/context.rs),
  [pattern provider](https://github.com/rust-lang/rust-analyzer/blob/b3c8f61b5036e12388787eaacd4775590fd3a036/crates/ide-completion/src/completions/pattern.rs),
  [source analyzer](https://github.com/rust-lang/rust-analyzer/blob/b3c8f61b5036e12388787eaacd4775590fd3a036/crates/hir/src/source_analyzer.rs).
- [rust-analyzer architecture](https://rust-analyzer.github.io/book/contributing/architecture.html).
  Adopt useful boundaries, not Rust-specific matching or inference semantics.
