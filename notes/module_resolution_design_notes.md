# Module Resolution & Cycle Detection — Design Notes

Summary of a design discussion comparing Rust's `use`/module resolution
model against what we want for `wx`. Goal: keep glob imports and a
Rust-like module system, but resolve everything in **one deterministic
pass with no fixed-point iteration**, and get precise, chain-aware cycle
diagnostics instead of Rust's occasionally-misleading errors.

---

## 1. Background reading (Rust internals studied)

Not directly actionable, but this is what informed the design below:

- `core::ops` vs `core::cmp` — operator traits are split by *return-value
  shape* (`Output`-producing vs fixed `bool`/`Ordering`), not by "is this
  spelled with a symbol." Confirms module boundaries should track
  semantic category, not surface syntax.
- `Drop::drop(&mut self)` — takes `&mut self`, not owned `self`, because
  drop glue must still walk the fields *after* the user's destructor
  runs; ownership would let a destructor smuggle the value back to life.
- `Allocator` trait (`core::alloc`, nightly, `allocator_api`) — allocator
  instance is stored as a field on `Box<T, A>`/`Vec<T, A>`; their own
  `Drop` impls call `.deallocate()` on that stored instance. No special
  "destructor #2" — it's the same drop-glue recursion, just business
  logic living in a library `Drop` impl.
- `NonNull<T>` — a non-null *proof only* (enables niche-optimized
  `Option<NonNull<T>>`); says nothing about validity/alignment/liveness.
- `super`/`self`/`crate` — real keywords, not bindings, specifically
  because they're resolved structurally (syntax-tree walk) *before* and
  independent of name/import resolution — an implicit binding would
  reintroduce the bootstrapping problem the 2018 edition's path-clarity
  RFC was written to remove.
- Known Rust wart: `self::super::X` is accepted even though `super` is
  documented as start-position-only (`internals` thread — a core dev
  called this "ancient" and possibly unintentional).
- Known Rust bug (rust-lang/rust#79309): `super` inside a block-scoped
  `mod { }` skips the block instead of seeing its siblings — "theoretically
  pure, practically surprising."

---

## 2. Rust's `use`-resolution bugs that motivated this design

- **Glob-vs-glob ambiguity under-detection** (`ambiguous_glob_imports`,
  `ambiguous_glob_imported_traits` lints) — nested globs (`pub use
  mod1::*; pub use mod2::*;` re-globbed again) historically failed to
  report genuine name collisions. Being tightened via future-incompatible
  lints as of 2025 PRs (#149058 etc.).
- **Pattern-position ambiguity fallback** (issue #46079) — `let v = V;`
  correctly errors on an ambiguous glob-sourced `V`; `match v { V => {} }`
  silently reinterprets the same ambiguous `V` as a **fresh binding**
  instead of erroring, because pattern-position resolution has a
  "not found → treat as binding" fallback that expression position
  doesn't have.
- **Named-import cycles** ("self-confirming import resolutions",
  rust-lang/rust#70236) — mutual `use X as Y` / `use Y as X` aliasing
  across modules can cycle. Rust's import resolver is an iterative
  fixed-point sweep (mark imports "indeterminate," retry every pass until
  stable); a genuine cycle just never stabilizes and falls through to a
  plain **"unresolved import"** diagnostic (E0432) that names only the
  last hop — not a cycle-aware diagnostic, because the fixed-point
  algorithm never explicitly notices *why* nothing converged.
- **Diagnostic-quality bugs** — e.g. false-positive `unused_imports` on
  glob re-exports (visibility model bug, not a resolution bug).

**Core takeaway:** Rust's resolver is correct-ish but structurally
iterative (retry-until-stable), and every sharp edge we found traces back
to that: no single pass ever "owns" the moment a cycle or ambiguity is
introduced, so diagnostics end up reporting a *symptom* instead of the
*cause*.

---

## 3. Design constraints we're adding on top of Rust's model

These are the deliberate simplifications, each chosen to eliminate one
specific failure mode above, in exchange for a small amount of
expressiveness:

1. **No glob-import of enum variants.** Variants always accessed
   qualified (`Enum::Variant`). Removes the single most common source of
   local match-arm ambiguity outright, and keeps renames/greps
   unambiguous. (Even Rust tutorials that show `use Enum::*;` immediately
   demonstrate scoping it tightly — informal evidence it's a contained
   feature, not an unconditionally loved one.)

2. **Pattern-position identifiers must not have a silent resolution
   fallback.** A bare lowercase identifier in a pattern is *always* a
   binding — never a lookup, never "try to resolve, fall back to
   binding on failure." Constructor/constant patterns must be
   grammatically distinct (qualified path, or a required marker) so the
   parser — not the resolver — decides which category applies, before
   any name resolution runs. This is what Haskell/OCaml/Elm/F# do via
   case-as-grammar. Necessary precondition for constraint #6 below to be
   *safe* (an ambiguous glob name must never silently reinterpret as "new
   binding" in pattern position).

3. **Wildcard (`use path::*;`) edges must form a DAG at the
   namespace level**, checked once, up front — no cycles allowed. A
   namespace importing itself transitively via globs is a hard compile
   error with the full cycle chain reported (not Rust's single-span
   E0432).

4. **Resolve wildcard-importing namespaces in topological order**, not
   iteratively. Because sources are fully finalized before their
   dependents are processed, glob-of-glob / transitive `pub use x::*;`
   chains **still work** — transitivity is *not* forbidden, only cycles
   are. This directly replaces Rust's retry-until-stable sweep with a
   single deterministic pass.

5. **Named imports get their own, finer-grained cycle check** —
   `(namespace, name)` as the graph node, not whole namespaces. A
   named-import cycle (`use b::Foo as Bar;` / `use a::Bar as Foo;` with
   neither side ever bottoming out at a real definition) is a distinct
   bug class from wildcard-namespace cycles and needs its own detector:
   a recursion stack over the *currently being resolved* symbols, not a
   static upfront graph (the alias graph isn't known until you start
   walking it). Fine-grained nodes also avoid false positives — two
   modules each importing *one concrete, already-defined* item from the
   other is legal and not cyclic, even though it looks superficially
   symmetric.

6. **Ambiguity stays deferred ("error on actual reference"), not eager
   at the `use` site** — explicitly rejected the "error immediately on
   any glob collision" design, since that defeats the point of the
   feature. Implemented as a sentinel resolution result (`Ambiguous`,
   similar in spirit to Rust's internal `Def::Err`) computed once during
   the topological pass, which only produces a diagnostic when something
   actually performs a reference lookup against that name — safe *only*
   because of constraint #2 (no silent pattern-position fallback that
   could dodge the sentinel).

7. **Poison / terminal state after a cycle or unresolvable error**, so a
   later, independent reference to the same broken symbol gets a quiet
   "already broken" answer instead of either a false "you're in a cycle"
   accusation or a duplicate re-derivation and re-report.

8. **The same fine-grained `(namespace, name)` graph doubles as the
   incremental-compilation dependency graph** (rustc's own red-green
   query system does exactly this: query DAG = dependency DAG =
   invalidation DAG). Two follow-on rules:
   - Fingerprint a symbol's **public signature**, not its source text or
     full body — an unrelated edit inside a function body shouldn't
     invalidate anyone who only depends on that function's signature.
   - Wildcard edges are **inherently coarser**: a glob edge must depend
     on the *entire public name-set* of its source (that's what "import
     everything" means), so adding/removing/renaming any public item in
     a globbed module invalidates every importer of that glob — an
     unavoidable structural cost of the feature, and one more argument
     (beyond readability) for keeping globs narrowly scoped rather than
     encouraged for broad API aggregation.

---

## 4. Codebase follow-ups — verify / implement

### Wildcard imports (`WildcardImport { namespace, source: NamespaceIndex, span }`)

- [ ] **Confirm today's actual resolution strategy for globs.** The
  existing comment on the `ast::UseTree::Glob` arm — *"Silent on every
  failure: this runs before other files have been scanned, so 'not
  found' here means 'not yet'"* — strongly suggests glob targets are
  currently resolved via silent-skip-and-presumably-retry, i.e. an
  implicit iterate-until-stable model. Verify whether/where the retry
  actually happens (a later pass? re-invocation of `walk_use_prefix`?).
  If so, this is exactly the fixed-point behavior we want to eliminate.
- [ ] **Build an explicit graph from `WildcardImport` entries**: edge
  `namespace → source` for every entry in
  `tir.namespaces[namespace].wildcard_imports`. This graph already has
  the right shape for what we need (your existing struct is namespace-
  level, matching constraint #3/#4 above).
- [ ] **Add a cycle check over this graph specifically** (DFS with a
  recursion-stack / on-path marker), before any namespace's glob set is
  resolved. On cycle, walk the path and report every hop's
  `WildcardImport.span`, not just one.
- [ ] **Replace retry-based resolution with topological-order
  resolution**: sort the DAG, process namespaces source-before-dependent,
  and when resolving namespace `N`'s glob set, treat every `source_ns`'s
  item table as already-finalized (no re-entry, no "not yet").
- [ ] **Implement the deferred-ambiguity sentinel** (constraint #6) as
  part of that same pass: when two *distinct* wildcard-sourced
  definitions land on the same name in `N`'s finalized table with no
  local/explicit override, store an `Ambiguous { candidates, spans }`
  entry; only raise a diagnostic when something later resolves a
  reference against that name.

### Named-import / signature cycle detection (`SigEntry`, `ComputeState`, `SymbolKind::Pending`)

- [ ] **`ComputeState` is currently `Pending | InProgress | Done` — add a
  fourth, terminal `Failed`/poisoned state** (constraint #7). Right now,
  after a cycle is detected and `report_cyclic_type_dependency` fires,
  verify what `sig_state[def_id]` is left as. If it stays `InProgress`
  forever, later *unrelated* references to that `def_id` will be
  wrongly told they're "cyclic." If it's reset to `Pending`, later
  references will silently re-walk into the same cycle and re-report.
  Neither is correct — needs a distinct memoized failure state, checked
  the same way `InProgress` is checked today.
- [ ] **Thread the resolution path through recursive `ensure_signature`
  calls** so the cycle diagnostic can report the full chain
  (`A → B → C → A`, one span per hop) instead of just the current call's
  `span`. The call stack already has this information at the point of
  detection — currently discarded. Either pass an explicit
  `Vec<(DefId, Span)>` down through the recursive calls, or reconstruct
  it by walking `InProgress` entries if there's enough info stored per
  entry to do so.
- [ ] **Clarify the relationship between `SymbolKind::Pending(DefId)` and
  `ComputeState::Pending`.** These look like two parallel "not resolved
  yet" trackers (one on the resolved-symbol-kind enum, one on the
  signature-computation state machine) — confirm whether they're
  tracking the same thing at different layers (kind vs. computation
  progress) deliberately, or whether there's redundant/driftable state
  here worth consolidating.
- [ ] **Decide whether wildcard-cycle detection (namespace-level) and
  named-import-cycle detection (`(namespace, name)`-level via
  `SigEntry`) should be unified into a single graph/detector, or
  deliberately kept separate** (different granularity, different timing
  — one is a static upfront DAG check, one is a live recursion-stack
  check during signature resolution). Current lean: keep them separate,
  since they run at different phases and catch structurally different
  bugs — but confirm this doesn't leave a gap where a cycle spans *both*
  a wildcard edge and a named-alias edge and falls through both checks.

### Pattern-position resolution (constraint #2)

- [ ] **Audit match/pattern lowering for any implicit "try resolve as
  constructor, fall back to binding" behavior**, and remove it if
  present. Confirm bare lowercase identifiers in pattern position never
  consult the symbol table at all — only qualified paths (or an
  explicitly marked constant-pattern form, if we add one) do.
- [ ] **Decide the const-pattern story**: either require constants to be
  matched via qualified path / explicit marker (grammatically distinct
  from a binding), or drop bare-constant patterns in favor of match
  guards (`x if x == SOME_CONST`) — this is the remaining gap after
  banning enum-variant globbing; it's the same ambiguity class applied
  to `const` instead of variants.

### Incremental-compilation groundwork (lower priority — future work)

- [ ] **Verify arena index stability.** `SymbolKind` variants store raw
  `u32`/`FooIndex` arena positions (`struct_index`, `enum_index`, etc.).
  Confirm these are derived from a stable identity (e.g. keyed off
  `DefId` or content hash) rather than push/allocation order — if
  they're pure insertion-order positions, adding an unrelated earlier
  item would renumber later ones and spuriously invalidate every future
  fingerprint comparison. Not urgent today, but worth confirming before
  any fingerprinting/caching work is built on top of these indices.
- [ ] **Not yet designed**: the actual fingerprint mechanism (what gets
  hashed as a symbol's "public signature" vs. what's considered
  body/implementation detail that's safe to change without invalidating
  dependents). Flagged for later — the graph/state work above should be
  built so this can slot in without a redesign, per constraint #8.

---

## 5. Open questions (not resolved in this session)

- Exact syntax for a constant-pattern marker, if we keep bare-constant
  matching at all (vs. dropping it for guard clauses only).
- Whether to special-case `use crate;`-style self-reference the way
  Rust's "blacklisted bindings" fix does, or whether our
  `(namespace, name)` recursion-stack check already subsumes that case
  for free (likely does, but worth a dedicated test).
- Whether wildcard-edge fingerprinting should hash the full public
  name-set of the source namespace, or something coarser/cheaper — full
  set is correct but worth checking cost on large re-export modules.