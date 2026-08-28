# `crate`/`super` path keywords, and `use` re-export privacy

Two features, one continuous session. `crate`/`super` came first as a
prerequisite (the module-resolution test catalog needed them to even write
valid syntax); `use` re-export privacy was the deliberate pick of the three
gaps that catalog surfaced (privacy, wildcard transitivity, wildcard-cycle
detection) — self-contained, and a real soundness gap today, versus the other
two needing new resolver machinery. 896 → **899** `wx-compiler` tests, 56
`wx-lsp`, 32 `wx-fmt`.

## `crate`/`super` path-root keywords

Started from research: could the existing demand-driven signature resolution
power full module resolution (globs, cycles, privacy), or does that need a
separate system? Wrote a test-case catalog before implementing anything, which
caught its own wrong assumption — the catalog had `a.wx` reachable as bare
`a::*` from a sibling `b.wx`, which isn't how `use` resolves anywhere: a bare
name only resolves via whatever's already in the *writing* namespace's own
scope. wx had no `crate`/`super` keywords at all, so there was no correct way
to spell "the sibling module" — hence this feature, with `self` explicitly
out of scope (no use case, and `self` already means the method receiver).

**Design settled after a rejected first draft.** The first plan special-cased
`crate`/`super` at each of the resolver's path-walking entry points. Rejected
in favor of the user's own proposal, which turned out strictly simpler:
**pre-populate every namespace's own `.symbols` map, at creation time**, with
real `SymbolKind::Module` entries for `crate` (→ the package root, computed
once `tir.package_namespaces` has that package's entry) and `super` (→ the
parent, `None` only at a package root, matching every other place `parent:
None` already means "package boundary"). This works because
`lookup_scope_chain` already checks a namespace's own symbols first, and every
multi-segment path walker resolves segment 2+ via a **direct** lookup in an
already-known namespace's own map — the exact same query a pre-populated
entry satisfies. Chaining (`super::super::x`) falls out for free: each
namespace on the walk carries its own `super` pointing at its own parent, so
hopping through it is indistinguishable from walking through any other nested
module. **Net result: zero changes to any of the actual path-walking
functions** — the whole resolver-side change is `Builder::seed_path_root_symbols`,
called at each of the three sites that construct a `ModuleNamespace`.

**Accepted consequence, not a bug:** since `crate`/`super` are now ordinary
per-namespace symbols rather than parser-enforced "must be leading" tokens, a
non-leading `super` (`foo::super::bar`) is well-defined and resolves —
`super` inside `foo`'s own namespace always means `foo`'s parent, wherever
written. Rust forbids this by fiat; costs nothing here to allow it.

Parser side: no separate keyword token exists for anything in this lexer —
every bare word lexes as `Identifier`, and "keyword-ness" is decided by
matching source text at each parse call site (the `self`/`Self` precedent).
Four independent "parse a path segment" call sites each needed the
`Crate`/`Super` exception added, at both the first-segment and in-loop
positions (chaining being legal removed any first-vs-rest asymmetry). New
`intern_path_segment` mirrors `intern_identifier` but excepts `Crate`/`Super`
from the reserved-identifier diagnostic.

**Two real, independent panics found and fixed**, both via manually hovering
`crate` in the LSP:

1. `namespace_name(target, packages, from)` indexed
   `packages[from].dependency_names[&target]` unconditionally — for a
   self-referencing `crate` (`target == from`, a package root naming itself)
   there's no such dependency entry, since a package never depends on itself.
   Fixed by special-casing `target == from` to return the literal `"crate"`
   first. Discovered a **third** reachable panic site the same way while
   fixing the first two — `TypeFormatter`'s `Type::Namespace` `Display` arm
   called the same function the same unsafe way.
2. Separately, `wx-lsp`'s `Hover` and `SignatureHelp` handlers were passing
   `compiled.graph.root_package` as the "asking package" context to
   `namespace_name`, when it must be the namespace actually being hovered
   over's *own* package (relevant the moment you're looking at a dependency,
   not just the root). Wrong regardless of the crate/super work, just never
   observable until a self-referencing `crate` lookup made the distinction
   visible.

Along the way, `namespace_name`'s signature changed from returning a cached
`SymbolU32` to `<'a>(..., interner: &'a StringInterner) -> &'a str` — every
call site was immediately resolving the symbol anyway, and the one case with
no real dependency-name to look up (`crate`/`super` naming a package's own
root) can answer with the literal keyword text directly instead of needing
one interned. Two design detours rejected on the way to this: `Option<SymbolU32>`
(disliked — turns every caller into an `Option`-juggling exercise for what's
always either "here's a name" or "here's the literal string `crate`"), and a
richer `SymbolKind`/`keyword_accesses`-tracking design for the semantic-token
problem below (rejected specifically for adding a new tracked field to every
namespace's own struct just to solve a problem a stateless check already
solves).

**Semantic-token highlighting**: `crate`/`super` share the generic
`SymbolKind::Module` variant with an ordinary module once resolved, so
excluding them from *semantic* highlighting (in favor of plain keyword
highlighting) can't be done by dispatching on kind — landed on a hardcoded
span-text comparison (`matches!(span_text, Some("crate" | "super"))`) right
next to the existing operator-filter check in `SemanticTokensFull`, flagged
with a TODO. Mirrored in both editor grammars: VS Code's TextMate
`keyword.other.wx` pattern gained `crate|super`; Zed's tree-sitter grammar
needed no `grammar.js` change at all (verified by tracing it) since
`crate`/`super` inside expression bodies fall into the same
text-matched-against-generic-`identifier` bucket as `if`/`self`/`unreachable`
— only `highlights.scm`'s `#any-of?` list needed the two names added. Zed's
`parser.c` regenerated from the (unchanged) grammar since `highlights.scm`
alone needed no rebuild but the earlier grammar exploration did touch the
generated file.

8 new tests (`test_crate_path_reaches_package_root_from_submodule` through
`test_non_leading_super_segment_resolves`), one LSP regression test
(`hover_over_crate_keyword_does_not_panic`) pinning fix #1 above.

## Characterizing the remaining gaps

Before picking what to build next, re-ran the module-resolution test stubs
left `#[ignore]`d from the catalog phase, empirically rather than by
inspection — confirmed no accidental regressions or fixes from the
`crate`/`super` work, and precisely characterized what each gap actually does:

- **Wildcard transitivity** (`pub use crate::a::*;` inside `b`, reached via
  `use b::*;` elsewhere): fails with `undeclared identifier` — no recursion
  into a glob source's own globs at all.
- **Wildcard cycles** (`a` globbing `b`, `b` globbing `a`; a module globbing
  itself): **zero diagnostics** — confirmed via a temporary debug probe
  (immediately reverted), not silently hanging or crashing, just genuinely
  invisible to the compiler, since there's no recursion to even loop on.
- **`use` re-export privacy**: every `use`, public or not, acted as `pub use`.

Picked privacy: self-contained (no new cycle-detection machinery needed,
unlike the other two, which are coupled — making glob lookup recursive
without a cycle guard turns today's harmless cycles into real infinite
loops), and a real bug today rather than a missing feature.

## `use` re-export privacy — design arc

The core problem: a `use` leaf's binding into its own namespace's `.symbols`
map is stored as the *exact same* `SymbolKind` a direct declaration would
produce (`Function { func_index }`, etc.) — necessarily, since that's what
lets the same item reached through two different re-export paths collapse
into "not an ambiguity" instead of a false conflict. But it means the
original item's own `pub_span` is the only visibility anyone can find,
answering the wrong question: whether the *importing* namespace could see
the item (already checked once, when the `use` itself resolved) — not
whether *this rebinding* is itself public.

**Design landed after several rejected shapes**, in roughly this order:

1. A side map on `ModuleNamespace` (`reexport_visibility: HashMap<key,
   Option<TextSpan>>`) — rejected: "why do we need an additional map,"
   correctly identifying that the fact already lives on `UseItem.pub_span`
   and the only real gap was no way to get from `(namespace, key)` back to
   *which* `UseItem` bound it, once the `Pending(DefId)` placeholder — which
   did carry that link — gets overwritten by the real resolved kind.
2. `Visibility::{Public, Private}` plus `SymbolEntry { kind, visibility }`
   (a struct, `SymbolKind` unchanged) — the immediate fix, but `Visibility`
   briefly grew a third `Unrestricted` state for kinds that aren't gated at
   all (modules, memories). Challenged directly ("give an example where it's
   used") — no real answer existed since nothing distinguished `Unrestricted`
   from `Public` behaviorally; **collapsed back to two states**, YAGNI'd.
3. **The actual instruction that shaped everything downstream**: "let's
   rewrite it with `SymbolEntry::{Pending(DefId), Resolved{kind, visibility}}`
   ... so that we don't patch later over it." This is the pivot from
   "patch around the placeholder-visibility problem" to "make the invalid
   state unrepresentable" — a still-unresolved claim now has no `visibility`
   field to misread in the first place, rather than a silently-defaulted
   `Public` value nobody could tell was fake.

That last decision cascaded into pulling `Pending(DefId)` out of `SymbolKind`
itself (previously a member of the same enum as every resolved kind) — sized
by grep before committing to it: `SymbolKind::Pending` had ~40 match sites
beyond the two directly relevant to visibility, mostly the "do I still hold
my own claim" check every item kind's Phase-2 binding repeats. Justified
because `SymbolKind` becomes strictly cleaner as a result — "always a real,
resolved item," never a placeholder a downstream consumer (codegen, type
conversion) has to defensively handle.

## The mechanical migration

`SymbolEntry::resolved_kind(self) -> Option<SymbolKind>` bridges the ~15
lookup-only call sites that never cared about `Pending` in the first place
(unchanged in shape, just `.and_then(SymbolEntry::resolved_kind)` where they
used to get a bare `SymbolKind` back). `still_pending(namespace, key, id)`
replaced **9 copies** of the identical `matches!(direct_scope_lookup(...),
Some(Pending(id)) if id == *id)` guard spread across every item kind's own
Phase-2 registration (function, struct, enum, trait, const, global, typeset,
type alias, memory) — a real dedup, not just a rename, surfaced by having to
touch every one of those sites anyway.

`symbol_kind_is_gated(kind) -> bool` replaces the old `symbol_visibility`
(which used to read the span *and* the exemption in one pass) — now purely
"is this kind subject to `pub`/private at all," since `insert_symbol` gets
the span explicitly from its caller (`pub_span: Option<TextSpan>` — the
item's own for a direct declaration, the `use` leaf's own for a re-export,
identical call shape for both, no separate `insert_reexport_symbol` needed).
Unifying those two call shapes into one function was itself a mid-session
redesign ("these two functions seem really similar, can't we unify them") —
the earlier draft had `insert_symbol`/`insert_reexport_symbol` as separate
functions because the span source seemed to need different retrieval logic;
turned out both just needed the caller to hand over a span, at which point
they're identical.

**A real, unplanned bug fix rode along**: `symbol_kind_is_gated`'s `Module`
arm had to decide whether a module is gated at all, and — challenged
directly on treating it the same as `Memory`/import-block members ("module
have the same pub span and must be used the same way as any other pub
span") — the answer was that `Memory`/import-block members are *structurally*
exempt (parser-rejects `pub` on both, confirmed via `VisibilityNotPermitted`;
`Memory` doesn't even have a `pub_span` field), but `Module` was never
structurally exempt — `pub mod foo;` was always parsed and stored
(`ModuleDecl.pub_span`), just never *read* for gating. So `Module` now reads
its real span; a private `mod foo;` is genuinely inaccessible from outside
its parent+descendants for the first time — previously "not gated yet," an
accepted CLAUDE.md-documented gap. Flagged explicitly as a bonus behavior
change riding along, not requested; nothing in the suite broke.

`ScopeLookup`/`lookup_scope_chain`/`lookup_global_symbol[_reporting]` now
carry `SymbolEntry` instead of `SymbolKind` throughout — needed because the
wildcard-import filter has to read `visibility` off entries that might still
be `Pending`. `entry_visible_from` treats a still-`Pending` entry as always
visible without forcing it (a real, TODO-flagged narrowing: nothing enforces
in the type system that this is safe) — verified safe by tracing that the
one caller needing a *real* answer for a possibly-`Pending` name
(`resolve_pending_global_symbol`/`resolve_pending_namespace_symbol`) always
forces `ensure_signature` and re-fetches before trusting the result, so the
placeholder is never the value an actual gating decision runs on.
`resolve_pending_global_symbol`/`resolve_pending_namespace_symbol` keep their
external `Result<Option<SymbolKind>, ()>` shape unchanged — `SymbolEntry`
stays entirely internal to the resolver, invisible to their ~15 combined
callers elsewhere in the file.

Both originally-targeted tests pass for real now:
`test_private_use_is_not_visible_via_qualified_path_from_outside` (which also
needed its own expected diagnostic fixed — it asserted `UndeclaredIdentifier`,
written speculatively before the fix existed; the actual, correct diagnostic
is `PrivateItem`, matching how a direct private declaration is already
reported) and `test_private_use_is_not_reachable_through_an_external_glob`.
9 TIR snapshot files updated (`cargo insta accept`) for the `SymbolEntry`
shape change — explicitly **not** accepted: an unrelated pre-existing
`.snap.new` for `mir::tests::test_generic_compound_assign_through_ptr_deref`,
left as a pending baseline failure rather than folded in.

## `record_symbol_access`, and the access-recording gap it closed

Found via manual testing, not planning: making `pow` private and calling it
via `crate::pow::pow(1, 2)` correctly reported `PrivateItem` but **broke
hover** on the reference. Traced to `resolve_pending_namespace_symbol`
returning `Err(())` via `?` the moment it rejects a private item — every one
of its 4 callers records the access *after* that point, on their own success
path, so the early return skips it entirely.

Whether that's actually correct to fix (recording an access for a rejected
reference) was checked against what the access list itself gates, not
assumed: `report_unused_items` flags a function `never used` exactly when
`accesses.is_empty() && pub_span.is_none()` — so the bug was compounding,
not just cosmetic. A private, referenced-but-rejected item was *also*
getting flagged dead code, stacking two diagnostics on the same line for the
same obvious fact (someone visibly tried to call it). Matches how
rustc/rust-analyzer split name resolution from the accessibility check as
two separate phases — a private-item reference (E0603) still resolved, so
hover/go-to-definition/"find references" still work on it there too.

Fixing the call site alone surfaced a **second, broader, pre-existing gap**:
`record_type_kind_access` (its name before this session — renamed
`record_symbol_access`, since it's not type-position-specific) had no arm
for `Function` or `Global` at all, silently swallowed by a `_ => {}`
catch-all — meaning a `use`-imported function's own mention already had this
same problem, just never surfaced because the function later gets called
successfully elsewhere and records its access there instead. Added
`Function`/`Global` arms (verified no double-recording risk by checking all
6 call sites — the `export { }` block's own success path already
special-cases those two kinds before ever reaching the catch-all). Then
asked directly about the one variant still left uncovered,
`TraitAssocType` — added too (a `HashMap`-keyed lookup into
`Trait.assoc_types`, trusted safe by the same "only exists after
`ensure_signature` already inserted it" invariant the type's own doc comment
establishes), and the `_ => {}` **removed entirely** — the match is now
exhaustive over all 11 `SymbolKind` variants, so the compiler itself forces
a decision on the next new variant instead of silently dropping it a third
time (this exact class of bug had already bitten once before, on `Module` —
see `test_qualified_bound_namespace_segment_records_access`, a pre-existing
regression test for that one).

**Moved to `impl TIR` in `mod.rs`**, kept private (no `pub`) — a deliberate
mid-session architecture question ("can we implement it on the TIR instead
of builder? would you recommend to do so?"), decided yes: the function
touches nothing but `self.tir.*` arenas, no `Builder`-specific state
(interner, `sig_state`, `ast_nodes`), matching the existing precedent of
`function_index`/`expect_function_index`/`namespace_name` already living as
plain `impl TIR` methods rather than `Builder` methods. `builder.rs` is a
descendant module of `tir`, so a private method defined in `tir/mod.rs` is
already visible there with no `pub`/`pub(crate)` needed.

New regression test:
`test_private_item_reference_records_access_and_is_not_flagged_unused`,
modeled directly on the closest existing precedent for "error path must
still record an access,"
`test_export_reports_cannot_export_and_records_access`.

## Context for future sessions

- **Wildcard transitivity and cycle detection are the two gaps still left**
  from the original three-item catalog, deliberately deferred as one unit —
  making glob lookup recursive without a cycle guard turns today's harmless
  cycles into real infinite loops, so they have to land together.
- **Glob-of-glob re-export privacy is a known, real gap in what just
  shipped**: `WildcardImport` itself carries no visibility of its own, so
  `pub use a::*;` inside `b`, reached transitively via `use b::*;` elsewhere,
  isn't gated — moot until wildcard transitivity exists at all (nothing to
  gate yet), but will need `WildcardImport` to gain its own `pub_span` when
  it does. Unlike the named-`use` case, this one doesn't need the
  `SymbolEntry` restructuring at all — `WildcardImport` already gets one
  real struct instance per glob statement (never collapsed/shared the way
  `SymbolKind` values are), so its own `pub_span` can live directly on the
  struct with no index/map problem.
- **Method-call and struct-field privacy remain unenforced** — pre-existing,
  documented gap, unrelated to this session; `resolve_impl_member` and
  struct-field access still don't call `symbol_kind_is_gated`'s conceptual
  equivalent anywhere.
