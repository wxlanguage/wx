# Native LSP migration to the new TIR

Status: compiler prerequisites done; server not yet reconnected.
Last updated: 2026-11-11.

Current compiler prerequisite design:
[TypeContext ownership and explicit borrowing refactor](type-context-ownership-refactor.md).
That plan supersedes the earlier extraction/borrowing-view proposals below: use
owned semantic and solver objects, explicit input/output arguments, and short
mutual reborrows, without another context view or a CompilerSession wrapper.
Latest refinement: distinguish computed products, solver, and signature query
system conceptually, but decide grouping from actual borrowing/parameter use.
Products may stay directly on TypeContext; no Products wrapper is required.
Computed signature tables are distinct from query scheduling/readiness state.

Interner prerequisite implemented: CompilationUnit no longer owns strings;
CompilationUnitBuilder borrows a caller-owned, keyword-seeded interner until it is
consumed. Manifest loading takes the interner explicitly, and checking/lowering
take immutable compilation inputs plus mutable strings. Native consumers are
migrated; LSP/Wasm wrappers remain untouched. The old diagnostics-returning TIR
entry points are transitional until the owned context refactor. Validation:
1,450 compiler tests passed (2 ignored), 75 formatter tests passed, native CLI
tests/build passed. See the companion plan's Current status for the sharing test.

This is the living reference for the migration. Add important discoveries,
decisions, and changes of direction here as work proceeds. Distinguish observed
behavior from proposals; the type and module names below are illustrative unless
explicitly identified as existing code.

## Scope and priorities

- Start with simple, non-incremental analysis: fully rebuild active roots.
- Preserve clear ownership and query boundaries so workers, selective root
  rebuilds, or compiler incrementality do not require rewriting request handlers.
- First native milestone: live diagnostics, formatting, and go-to-definition.
- Defer richer semantic features, completion, rename, and Wasm migration.
- Leave `wx-compiler-wasm` untouched; do not migrate Wasm wrappers as part of the
  first native milestone.
- Favor flat tables, typed indices, explicit owners, and small `Copy` identities.
  Avoid recursive boxed editor referents and a second LSP-owned semantic model.

## Prerequisite work completed

Commit `4bde6f6` (`refactor(tir): model name resolutions and audit reference
coverage`) establishes the resolution model and its coverage audit.

- (Updated 2026-11-11.) `NameResolutions::by_site` is a
  `BTreeMap<Site, Reference>`; `Site` is `Type`/`Value`/`Label(SourceSpan)`,
  ordered by position then role. `Reference` is `Name(Referent)`, `Local`,
  `Field` or `ArgumentLabel`; all flat and `Copy`, and all `pub(super)` to
  `tir`, so navigation needs a public `Semantics` query.
- A shorthand argument is two entries at one span (its label and its value).
- Named argument labels target the naming declaration, including trait
  declarations whose implementations use unnamed parameters.
- Pattern shorthand records a field selection; its local declaration remains in
  the body tables, not a second reference.
- Failed ordinary, qualified, associated, and method-call lookup now checks
  arguments through the existing `build_unchecked_arguments` recovery path.
- All 28 resolution tests live directly in `tir/resolutions.rs`, using multiline
  WX samples and exact identities, including owners and field indices. Expected
  definition targets use the existing `PathResolver`, not another path walker.
- Last validation: `cargo test -p wx-compiler --quiet`: 1,448 passed, 2 ignored;
  Rust formatting and `git diff --check` passed.

Whole-workspace validation is still blocked by disconnected frontend consumers
of the removed compiler APIs.

## Existing server: observed structure

Most implementation is in `crates/wx-lsp/src/lib.rs` (roughly 3,000 lines).

```text
notification
  -> FIFO command queue / single state-owning actor
  -> update open-document overlay and project state
  -> rediscover active roots
  -> load and parse each root and its dependencies
  -> build old TIR
  -> reconstruct SymbolIndex
  -> replace cached root
  -> publish diagnostics

request
  -> same queue
  -> locate a cached root containing the file
  -> query old TIR / SymbolIndex
  -> convert to LSP response
```

### State and execution

- `ServerState` owns open documents, workspace folders, cached `CompiledRoot`s,
  project manifests/publication tracking, and `own_root` file ownership.
- `CompiledRoot` contains `CompilationUnit`, the removed `TIR`, and `SymbolIndex`.
- `OpenDocument` currently contains text only; incoming versions are discarded.
- `OverlayFileSource` makes open editor text authoritative over disk, including
  existence checks. Disk events for open files are ignored.
- `StateHandle`, `Command`, and `run_actor` serialize state changes and reads.
- `task.rs` provides native/Wasm spawning shims. The native host can use a
  single-thread runtime; synchronous checking blocks responsiveness there.
- `compute_active_refresh` already rebuilds every active root on each refresh.
  Dependency-only manifest entries do not automatically become active roots.
- Project manifests are retained separately and refreshed on manifest events;
  source refreshes reuse them. Invalid manifests remain project boundaries.
- Root discovery walks up to `wx.json`, respecting workspace folders and open
  manifest buffers. Manifest creation/deletion can reparent open files.
- Publication tracking clears diagnostics for files no longer reached and merges
  shared-file diagnostics across roots.

### Semantic features

- `symbol_index.rs` reconstructs declarations and references by walking the old
  TIR's per-declaration access lists. It defines another `SymbolKind` enum and
  indexes globals, synthetic `Self` navigation targets, and implementations.
- `completion.rs` mixes textual context classification with old-TIR visibility,
  locals, namespaces, types, and member queries.
- Hover, definition, implementations, references, rename, signature help, semantic
  tokens, and completion all depend on obsolete semantic APIs.
- Initialization currently advertises all those features. Advertise only restored
  features during migration.
- Formatting reparses the latest overlay independently of cached semantics and
  uses manifest formatting configuration. Retain that independence.
- Custom requests expose virtual stdlib content and full rendered diagnostics.
  Preserve transport/extension compatibility deliberately, rather than silently
  dropping these while replacing handlers.

### Keep / reshape / replace

| Area | Direction |
| --- | --- |
| Transport, Backend, command queue, task shim | Keep |
| Overlay and watcher behavior | Keep; retain document versions |
| Package discovery and manifests | Preserve behavior; separate from semantic storage |
| Diagnostic conversion and UTF-16 helpers | Reuse and test |
| Formatting | Keep syntax-only and independent of semantic success |
| CompiledRoot | Replace with an owned analysis snapshot |
| SymbolIndex and old SymbolKind | Replace using compiler resolutions/declarations |
| Rich semantic handlers | Restore individually against compiler queries |
| Completion | Defer semantic rewrite; textual classification may be reusable |
| Tests | Preserve behavior scenarios; replace obsolete fixtures/assertions |

## Ownership and lifetimes

Settled by the ownership refactor ([record](type-context-ownership-refactor.md),
2026-11-11): `tir::check` returns an owned, lifetime-free `Semantics`, and the
AST borrow lives only in the `SemanticsBuilder` for the length of the build. The
old advice "do not store `TypeContext` in the server" and the separate
`SemanticData` are superseded; there is no second semantic model.

```text
server lifetime
  documents: authoritative open text + versions
  workspace/project configuration
  current snapshots
  diagnostic publication bookkeeping

snapshot lifetime (one per package root)
  AnalysisSnapshot { revision, compilation: CompilationUnit,
                     strings: StringInterner, sema: Semantics }
  built by tir::check; diagnostics = compilation.collect_diagnostics()
  + sema.diagnostics()

request lifetime
  borrowed snapshot view
  owned response
```

The compiler owns semantic queries (`Semantics` methods); the LSP owns
scheduling, versions, publication and protocol conversion. Interner scope:
see the decision recorded under step B.

### Snapshot invariants

- File IDs, declaration IDs, body-local IDs, type indices, symbols, and spans are
  scoped to one snapshot. Do not persist bare IDs in unrelated server state.
- Rebuilding constructs a replacement; retiring a snapshot retires its identities
  together. Never compare or merge semantic IDs across root snapshots.
- Source position conversion and semantic lookup use the same snapshot text.
- Erroneous source still produces partial semantic data and diagnostics; no
  success-only `Result<SemanticData, Diagnostics>` boundary.
- Requests read data; they should not need to restart mutable checking queries.
- Single ownership is sufficient initially. Add `Arc` only when concurrent users
  actually need to retain snapshots; immutability does not require cloning them.

## Query boundary and derived indexes

Request handlers should ask semantic questions rather than directly walk compiler
internals. Initial questions:

- What meanings occur at this file/byte position?
- What declaration/navigation targets correspond to those meanings?

Later questions include expression types, references, implementations, visible
names, and signatures. Return compiler spans and structured identities rather
than LSP locations, Markdown, or completion items.

Position lookup must cover declaration sites as well as reference sites. Keep
multiple tiers and shorthand meanings intact; do not force every position into a
single target. Navigation may return multiple destinations. Rename needs a
separate policy: navigation equivalence is not automatically rename equivalence.

Derived indexes accelerate access but are not another source of semantic truth:

- per-file occurrence lookup;
- declaration-position lookup;
- later, target-to-occurrences lookup.

Prefer compact span/ID records pointing into authoritative tables. Build indexes
once per snapshot. Scanning small tables is fine initially; do not prebuild every
possible index before a consumer needs it.

## Correctness findings to address

These are code-inspection findings, not yet new regression tests or fixes.

### Edit coalescing can cross request boundaries

`handle_command` considers an edit superseded if *any* pending command edits the
same file, not just an adjacent edit. With `edit A -> query -> edit B`, it can
store A but skip its rebuild, then answer the query from older semantics.

Initial recommendation: remove coalescing. Later batch only adjacent mutations,
without crossing a request boundary. Do not add query-time freshness polling to
compensate for inconsistent event processing.

### Root selection is nondeterministic for shared files

`resolve_uri` scans cached hash-map values and accepts the first root containing
the file. Dependencies can appear in multiple analyses.

Proposed policy: prefer the file's own active project; otherwise choose a
deterministic containing root. Keep that root context for the entire request.
Virtual stdlib files also need a deterministic fallback context.

### Live and semantic source can diverge

`resolve_source_and_offset` can prefer current buffer text while consumers use
older compiled semantics. Semantic requests must use one coherent snapshot;
formatting can independently parse current text.

### Document versions are discarded

Keep versions from didOpen/didChange and use versioned diagnostic publication
where applicable. Versions are also the foundation for rejecting obsolete worker
results if background analysis is introduced later.

### Full-diagnostic identity is fragile

The custom full-diagnostic request identifies a diagnostic by its displayed index,
then reconstructs that order from a selected root. Refreshes and merged-root
diagnostics can make the index refer to another diagnostic.

Use a root/revision/diagnostic identity when this feature is migrated. An expired
identity should report expiration, not render an unrelated current diagnostic.
Coordinate any protocol change with its extension consumer.

## Initial execution strategy and future scaling

1. Apply an event to authoritative input state.
2. Rediscover roots when needed.
3. Fully reload and analyze every active root.
4. Install the replacement snapshot set.
5. Aggregate and publish diagnostics, including clears.
6. Answer subsequent requests from installed snapshots.

Keep this serialized initially. Separate synchronous checking from async
transport, but accept its initial responsiveness cost. No shared mutable semantic
database, fine-grained invalidation, or background completion races are needed.

Possible later extensions preserve these boundaries:

- Workers take captured inputs and return owned snapshots. Install results only
  if their input revision is still current.
- Selective root rebuilds track filesystem reads and existence probes, including
  misses. Loaded-file lists alone miss dependencies such as a previously absent
  `foo.wx` referenced by `mod foo;`. Root-discovery changes from manifest
  creation/deletion still require broader reconsideration.
- Incremental compiler work changes how semantic data is produced, not how LSP
  handlers consume it. Do not promise stable cross-revision IDs prematurely.

## Implementation sequence

### A. Compiler analysis ownership

Done (2026-11-11): owned `Semantics`, ownership audit, resolution table and its
coverage tests. Remaining: the navigation query (`definition_at`).

- Audit persistent versus temporary `TypeContext` fields and arena dependencies.
- Design owned semantic storage and a small borrowed query view.
- Preserve useful output for erroneous programs.
- Add occurrence and navigation queries, including declarations and shorthand.
- Preserve CLI checking/lowering behavior; avoid a separate editor checker.

### B. Server state and consistency

- Separate document inputs, project discovery, snapshots, and publications.
- Retain document versions.
- Remove unsafe coalescing; make root selection deterministic.
- Ensure requests use snapshot-local source and identities.
- Split the monolithic module along ownership/responsibility boundaries as useful,
  without creating an elaborate framework or one cache per feature.

### C. Minimal native LSP

- Reconnect live diagnostics, formatting, and go-to-definition.
- Advertise only restored capabilities.
- Reconnect the native CLI entry point.
- Leave Wasm wrappers untouched.

### D. Richer features

Restore hover, semantic tokens, references, implementations, signature help,
completion, and rename individually, with explicit query/data requirements.

## Validation targets

Preserve existing behavior tests for overlays, dependency changes, manifest
creation/deletion, diagnostic clearing/merging, formatting, virtual stdlib files,
and Unicode conversions. Port fixtures away from the removed TIR.

Add focused regressions for:

- edit -> query -> edit ordering;
- navigation after edits shift source offsets;
- valid references inside erroneous programs;
- declaration clicks, named labels, and dual-target shorthand;
- deterministic shared-dependency root selection;
- removed files and stale diagnostic clearing;
- document versions and expired diagnostic identities;
- formatting independent of semantic success;
- Unicode position conversion using the queried snapshot's source.

## Code map

- `crates/wx-lsp/src/lib.rs`: state/actor, protocol handlers, project loading,
  analysis refresh, publication, formatting, custom requests, URI/position helpers.
- `crates/wx-lsp/src/symbol_index.rs`: obsolete semantic reconstruction to replace.
- `crates/wx-lsp/src/completion.rs`: textual classification plus obsolete queries.
- `crates/wx-lsp/src/task.rs`: runtime spawning shim.
- `crates/wx-lsp/src/tests.rs`: behavior tests and obsolete semantic fixtures.
- `crates/wx-compiler/src/tir/mod.rs`: checking/lowering entry points.
- `crates/wx-compiler/src/tir/signatures.rs`: TypeContext ownership and tables.
- `crates/wx-compiler/src/tir/defs.rs`: owned declaration identities and borrowed
  AST entries.
- `crates/wx-compiler/src/tir/resolutions.rs`: occurrence meanings and tests.
- `crates/wx-compiler/src/tir/body.rs`: body-local declarations and flat typed data.
- `crates/wx-compiler/src/vfs/mod.rs`: compilation ownership, files, packages,
  interner, and parser/package diagnostics.
- `crates/wx-cli/src/main.rs`: disconnected native LSP entry point to reconnect.
- `notes/lsp-full-diagnostic-view-plan.md`: existing custom diagnostic-view context.
- `notes/lsp-completions.md`: previous completion context; not the new-TIR API plan.

## Storage audit (historical)

The 2026-11-10 audit of what to retain from `TypeContext`, and the proposals to
consume it into a reduced result, are obsolete: the user's direction (keep the
live mutable semantic state, no extraction, no storage wrapper) was implemented
as the owned `Semantics`. See
[type-context-ownership-refactor.md](type-context-ownership-refactor.md). One
fact from it stays true: evaluated values refer into the solver's allocation
arena, so never retain `global_values` apart from the solver.
