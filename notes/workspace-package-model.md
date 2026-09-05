# Workspace / package model: what's wrong and what to do about it

Analysis notes, 2026-09-05. Line references are from that day's tree and will drift.

Nothing here is implemented. This is the reasoning behind a refactor we decided to
scope but not start, written down so it doesn't have to be re-derived.

## The root problem

`CompilationUnit` is modelled on the CLI's job — *produce one wasm module from one
root* — and `wx-lsp` reuses it as if it were a workspace model. There is no type in
the system meaning "the set of packages I know about". Almost everything odd in
`ServerState` is compensation for that missing concept.

The CLI's shape is genuinely single-rooted: it emits one module, and MIR/codegen
assume a root. The LSP's is not: it holds many packages, most of them shared, and
never runs MIR or codegen at all. Both are served by the same type today.

## Data flow as it stands

```
wx-cli check        → open_manifest(dir, NativeFileSource) → CompilationUnit → TIR → MIR → wasm
wx-cli format       → reads and parses wx.json itself, separately (wx-cli/src/format.rs:40)
wx-lsp analyze_root → parse_root → open_manifest_with_manifests(root, overlay, &retained)
                                     ↑ retained manifests smuggled back in from
                                       state.projects, parsed at wx-lsp/src/lib.rs:1556 and :1828
wx-lsp root lookup  → discover_package_root walks up with raw Path::exists(),
                      outside FileSource and outside the manifest store entirely
```

Four production sites parse `PackageManifest`. Three independent mechanisms answer
"what packages exist".

## Symptoms, all from the one cause

### 1. Manifests are deliberately homeless

`open_manifest_with_manifests`' own doc says it: *"The data is only an input to
resolution; no manifest is stored on the resulting CompilationUnit."* So every
consumer that needs a manifest afterwards keeps a private copy — `ProjectState::manifest`
in the LSP, a fresh read in `wx format`.

The `manifests: &HashMap<AbsolutePath, &PackageManifest>` parameter exists solely to
smuggle a caller's copy back *into* the function that discarded it.

The duplicated `let loaded; let manifest = if let Some(m) = …` block at
`vfs/resolve.rs:90` and `:168` is downstream of this. That deferred-init dance is what
you write when a value's owner is ambiguous — sometimes the map owns it, sometimes the
stack frame does. Give it one owner and the dance disappears without needing `Cow`, an
out-param slot, or a closure. (A shared `read_manifest` helper *did* exist and was
deleted when retention was added, because its owned return type couldn't express the
borrowed case.)

### 2. Every root recompiles the world, stdlib included

Each `CompilationUnit` carries its own `files`, `interner`, and `id_generator`
(`vfs/mod.rs:659`), and each build starts with `load_stdlib()` parsing the embedded
stdlib from scratch (`vfs/mod.rs:508`). Three open packages means the stdlib parsed and
typechecked three times, plus every shared local dependency.

The code visibly pays for this:

- `ServerState::cached`'s doc concedes that "a dependency file legitimately appears here
  under every root whose compiled graph reaches it"
- `resolve_uri` linear-scans every cached unit × every package × every module to resolve
  a single URI
- `compute_active_refresh` merges per-file diagnostics across roots with an O(n²)
  `!merged.contains(&diagnostic)` — deduplicating *the same file compiled twice*

### 3. Four hand-synchronised maps

`cached`, `projects`, `own_root`, and `published_files` inside `projects`, with long
comments explaining which is derived from which and how they can drift. One concept
wearing four hats.

## The numbering constraint (the part that decides the design)

Package-scoped incremental parsing — reusing a dependency's ASTs when its files haven't
changed — is blocked by *identifier allocation*, not by any of the above.

**`DefId`s are minted at parse time** (`parser.id_generator.generate()`, e.g.
`ast/mod.rs:2894`, `:4850`) from a counter shared across the whole unit —
`DefIdGenerator { next_id: u32 }` (`ast/mod.rs:1680`). TIR then mints *more* from the
same counter during its pass (`tir/builder/memory.rs:170`, `:463`, `:487`, via
`&mut graph.id_generator` at `tir/builder/mod.rs:517`).

So: parse A → ids 0..100; parse B → 100..150; TIR → 150..160.

A package's ids therefore depend on how many items were parsed *before* it. Add one item
to A and every id in B shifts, so a cached parse of B is worthless. This is the actual
blocker.

The three numbering spaces have to move in **different directions**:

| Space | Direction | Why |
|---|---|---|
| `interner` | **up** to the workspace | `string_interner` is append-only; a symbol never changes once assigned. Reparsing a package gets the same symbols back for unchanged text, so cached ASTs stay valid indefinitely. |
| `files` | **up**, plus a new op | Keep `FileId` dense and workspace-global, but reparsing must **replace in place** at the existing `FileId`, not `add`. Otherwise spans in other cached ASTs go stale and the `Vec` grows unbounded across a session. Needs `Files::replace`. |
| `id_generator` | **down**, into the package | Hoisting it makes things *worse* — it globalises exactly the ordering dependency that breaks caching. Wants `DefId { package: PackageId, index: u32 }` or a per-package generator, so a package's ids depend only on its own content. |

Cost check on the `DefId` change: it's used almost entirely as a **HashMap key**
(`item_lookup` `tir/mod.rs:2546`, `sig_state` `tir/builder/mod.rs:168`,
`func_wasm_index`/`global_wasm_index`/`memories` in `codegen/mod.rs`, the MIR inlining
maps), not as a dense `Vec` index. Widening it therefore doesn't force a data-structure
rewrite. Contrast `FileId`, whose doc explicitly leans on density: *"File ids are dense
within a compilation, so anything keyed by file can be a Vec rather than a map"* — which
is why that one stays dense and global.

## Monolithic TIR is fine, with one caveat

TIR stays non-incremental: one pass over every package, every time. That removes the
hardest part of incrementality from scope and is the right call for now.

The caveat: TIR currently *advances the parse-time counter* when it mints synthetic ids.
With a persistent workspace, running TIR twice over unchanged input yields different
synthetic ids each run, and `next_id` climbs for the whole session. Synthetic ids need
their own space — a generator reset per run, or a dedicated variant.

That's the difference between "TIR is a pure function of the parsed workspace" and "TIR
mutates the thing it reads". Only the first makes a parse cache trustworthy.

## Remote package sources

Materialising to the local filesystem before compiling is the right call — compilation
itself doesn't need to know. The consequences all land in resolution, and they reinforce
splitting resolution from compilation:

- Resolution gains network IO, checksums, and version solving, with failure modes parsing
  has never had. That phase must fully complete before any parsing starts.
- `vfs/resolve.rs:55` already names the mechanical blocker: a remote source *"would need
  its own `FileSource` … which can't be threaded through `&impl FileSource` here without
  widening it to `&dyn FileSource` first."*
- `DependencySource` has exactly one variant (`manifest.rs:139`) and `resolve_dependencies`
  destructures it irrefutably (`let ResolvedDependency::Local(dir) = &identity;`). That
  line marks where a second variant lands. `ResolvedDependency`'s doc already explains why
  it's tagged rather than a bare path, so the identity model is ready.

A materialised remote package is **immutable** — content-addressed by version and
checksum — so its parse artifact never needs invalidation:

```rust
enum Freshness {
    Local { fingerprint: u64 },  // reparse when the content hash changes
    Immutable,                   // fetched and checksummed; never reparse
}
```

## Target shape

```rust
pub struct Workspace {
    // Numbering that must outlive any single compilation.
    interner: StringInterner,
    files: Files,                                     // dense, replace-in-place

    manifests: HashMap<AbsolutePath, ManifestEntry>,  // parsed once, invalidated by event
    packages: HashMap<AbsolutePath, ParsedPackage>,   // ASTs + Freshness
}

// 1. Manifests and edges only. Materialises remote deps; no module parsing.
fn resolve(&mut self, root: &AbsolutePath, source: &dyn FileSource) -> Result<PackageSpec, ()>;

// 2. Parse, reusing every package whose Freshness allows it.
fn parse(&mut self, spec: &PackageSpec, source: &dyn FileSource) -> Result<(), ()>;

// 3. Typecheck everything, monolithically, as today.
fn check(&mut self, roots: &[PackageId]) -> TIR;
```

CLI: `resolve` → `parse` → `check(&[root])` → MIR → codegen; behaviour unchanged.
LSP: one workspace per session; `resolve` only on manifest events, `parse` only for
changed packages, `check` over everything.

On multi-root: `CompilationUnitBuilder` already accumulates N packages with edges, and
`build(root_package)` merely nominates one. Single-rootedness is a thin veneer —
`root_package` has just two consumers inside TIR (`tir/builder/signature.rs:725`,
`tir/builder/traits.rs:749`) and `stdlib_package` two more (`modules.rs:649`,
`traits.rs:763`). All four ask "which package owns this item?", which is answerable from
the item itself — *more* correct than assuming the root, not less.

## What the refactor deletes

- `open_manifest_with_manifests` and its borrow-of-borrows map
- `ManifestState` and both LSP manifest parse sites
- the CLI's third manifest read in `format.rs`
- the `let loaded;` duplication in `resolve.rs`
- `state.cached` as a map — becomes one workspace, so `resolve_uri` is a lookup
- the O(n²) cross-root diagnostic dedup in `compute_active_refresh`
- stdlib parsed once per session instead of once per root
- `Command::Formatting` parsing an entire package (and its dependencies) to format one file

It's also the substrate the deferred per-root invalidation work needs — see the doc
comment on `compute_active_refresh`.

## Staging

1. **Scope `DefId` per package**, and give TIR's synthetic ids their own space. First,
   because it's the precondition for any parse caching, and doing it after the hoist means
   touching the same code twice.
2. **Hoist `interner` and `files` into a `Workspace`**; add `Files::replace`. Mechanical,
   no behaviour change.
3. **`Workspace` owns manifests; split `resolve` from `parse`.** Where most of the
   deletions above land.
4. **Per-package parse cache** keyed on `Freshness`. The incremental win lands here and
   only here.
5. **Multi-root**: the four `root_package`/`stdlib_package` sites derive the package from
   the item.
6. **Remote**: `DependencySource::Remote`, `&dyn FileSource`, materialisation in `resolve`.

Steps 1–3 stand on their own merits. 4 is what the incremental goal actually needs. 5 and
6 are independent of both.

## Further out

Salvaged from `notes/incremental-lsp.md`, deleted 2026-09-05 as stale — it described
`parse_cache`, `compiled_versions` and `lsp_version`, none of which still exist. These
points outlived it.

**The TIR-mutation question is now answered.** That note flagged, as needing verification
before any parse cache could be finalised: *"`TIR::build` takes `&mut CompilationGraph`.
It reads from AST nodes but may also annotate them. If it writes into AST nodes, cached
ASTs from before a TIR build may be stale after."* It does mutate — not the AST nodes
themselves, but the shared `id_generator`, minting synthetic `DefId`s at
`tir/builder/memory.rs:170`, `:463`, `:487`. Hence the caveat above about giving synthetic
ids their own space.

**`FileId` stability has a second option.** This note proposes replace-in-place at the
existing id. The alternative that note raised is *path-keyed allocation* — the same path
always gets the same id, from a registry persisting across rebuilds. Equivalent in effect;
replace-in-place is the smaller change to `Files`, path-keying is more robust if the file
set is ever rebuilt from scratch mid-session.

**Interner growth.** Confirmed additive, which is exactly what makes cached ASTs stay
valid. The flip side is that a long session accumulates symbols from identifiers that no
longer exist anywhere. Not a correctness problem, only memory; a generational interner
(GC old generations after a full rebuild) would address it if it ever matters.

**Early cutoff, if TIR ever becomes incremental.** The property that makes salsa-style
systems feel instant: if reparsing a file yields a structurally identical result, the
change does not propagate and downstream work is skipped, making comment and whitespace
edits nearly free end-to-end. wx AST nodes carry byte-offset spans, so *any* edit produces
a different AST — so this needs either span-insensitive structural comparison, or a
semantic fingerprint per item (a hash of the token stream excluding trivia). The latter is
the tractable one. Out of scope while TIR stays monolithic, but it is the reason a
fingerprint is worth computing per package rather than a bare mtime check.

### References

- rust-analyzer architecture: https://rust-analyzer.github.io/book/arch/
- salsa incremental computation: https://github.com/salsa-rs/salsa
- "Responsive compilers" (Niko Matsakis) — the design goals behind salsa

## Scope and risk

`.interner` / `.files` / `.id_generator` appear **477 times** across the crates, 223 of
them in tests — so roughly 254 production sites plus a large test-churn tail. Steps 1–2
are mostly mechanical but wide, and they touch the typechecked core of a compiler that
currently works.

Against that, the measured pain is currently small: a full `wx check` of the largest
example (678 lines, including process start, stdlib parse, and codegen) is **~10ms**, so
one root is single-digit milliseconds. The redundant stdlib work and duplicate parsing
cost memory and time nobody has felt yet.

If the thesis deadline binds, the defensible minimum is **step 3 alone**: it removes the
manifest smuggling and the duplication without touching numbering, and forecloses
nothing — 1, 2, and 4 remain available afterwards, in that order.
