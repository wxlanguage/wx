# Crate manifests: making library/binary compilation explicit

## The problem

Every frontend (`wx-cli`, `wx-lsp`, `wx-compiler-wasm`, every `TestCase`) hardcodes the same
two-line dance:

```rust
builder.load_stdlib();               // embedded `std` crate
builder.load_binary(path, &source);  // whatever the user pointed at
```

When `path` *is* `crates/wx-compiler/std/main.wx`, this loads the stdlib twice — once
embedded, once from disk. The `std::` namespace prefix hides most of the fallout, but
inherent/trait impls aren't namespaced (`impl f64 { pub fn trunc }` registers into
`inherent_impl_dispatch` keyed by type, globally), so you get duplicate-candidate errors.

Root cause: **nothing in the compilation says what kind of crate is being built.**
`CrateGraph.name: Option<SymbolU32>` incidentally encodes lib-vs-bin (`Some` = library,
`None` = binary) and is read in exactly one place (crate-namespace creation in
`tir::builder::build`). `CompilationUnit.root_crate` exists but is essentially dead —
only `codegen/tests.rs` reads it.

The fix isn't a one-off patch to stop double-loading `std` — it's making crate kind and
identity a real, explicit part of the compilation, so it scales to actual library crates,
not just to unblocking one command.

## Design stance

A few principles this design leans on throughout, stated up front because they're what
killed several earlier drafts of this same idea:

- **One source of truth per fact.** Two independently-writable things that must agree
  (a flag and a manifest, a filename and a declared type) are a standing edge case, not
  a convenience — every disagreement is a bug someone has to reason about.
- **Generalize only when a second real use case already exists.** Dependency resolution
  generalizes past `std` because real library crates are the actual near-term goal.
  A `std`-only opt-out flag was rejected because no second foundational crate is actually
  in scope — that's designing for a hypothetical, not a plan.
- **Silent fallback vs. loud error.** Every ambiguous or missing state should be a clear,
  immediate error. Nothing guesses.
- **Don't build structure for a problem that doesn't exist yet** (a `target/`-style output
  directory, for instance) — add it when a second concrete need shows up, not preemptively.

## Crate identity

```rust
pub enum CrateKind { Binary, Library }   // no payload
```

`name: Option<SymbolU32>` lives on the crate graph directly, **independent of kind** —
not nested inside `CrateKind::Library { name }`. Reasons:

- Manifest ergonomics: `wx.json` always has a top-level `name` regardless of `type`, same
  as `package.json`/`Cargo.toml`.
- Output-artifact naming (`<name>.wasm` instead of the entry file's stem).
- Diagnostic/tooling attribution, and headroom for a future multi-binary workspace.

Migration note: code that currently gates crate-namespace creation on `name.is_some()`
must switch to gating on `kind == Library` explicitly — those stop being the same fact
once binaries can have names too.

`CrateId` is unaffected — it stays a pure internal dense-array handle (`crates[id.as_usize()]`),
never written by a developer, same relationship `DefId` has to a function name. The
developer-facing name is a plain string, interned through the *existing* `ast::StringInterner`
into a `SymbolU32` — reusing exactly the mechanism `use module::*` already resolves path
segments through. No new identifier concept needed.

**One naming namespace, not Rust's package-name/crate-name split.** `name` must lex as an
ordinary wx identifier — no hyphens. Rust needs two namespaces only because Cargo's registry
convention (kebab-case) sits on top of a language grammar that can't contain hyphens; wx has
no registry yet, so there's nothing to split. If a registry with its own naming convention
shows up later, that's an additive second field then, not a redesign now.

## The manifest: `wx.json`

**JSON, not TOML.** `serde_json` is already a workspace dependency, pulled into `wx-cli`,
`wx-compiler`, and — critically — already shipping on `wasm32-unknown-unknown` in
`wx-lsp-wasm` today. `toml` isn't a dependency anywhere in the workspace and would need new
wasm32 verification for a format whose only real advantage (comments) isn't load-bearing.
wx's actual distribution audience (npm-published CLI, browser playground, VS Code/Zed
extensions) also fits JSON conventions (`package.json`, `tsconfig.json`, `deno.json`) at
least as well as it fits Cargo's TOML.

The in-memory type is named **`CrateManifest`** — matching both the vocabulary used
throughout this design and Cargo's own internal term (`cargo_toml::Manifest`) for the same
concept.

### Schema

```json
// crates/wx-compiler/std/wx.json
{
  "name": "std",
  "type": "lib"
}
```

```json
// myapp/wx.json
{
  "name": "myapp",
  "type": "bin",
  "dependencies": {
    "somelib": { "path": "../somelib" }
  }
}
```

| Field | Required | Notes |
|---|---|---|
| `name` | yes, whenever a manifest exists | Must lex as a wx identifier (no hyphens). Used both as the dependency-resolution key and the in-language `name::Item` path segment. |
| `type` | yes | `"bin"` \| `"lib"`. A single enum field makes "can't be both" true by construction — no separate validation needed. |
| `dependencies` | no, defaults to none | Object keyed by name, not an array — values are typed objects (`{"path": "..."}`) rather than bare strings, so a future `{"version": "..."}` sibling key can be added per-entry without ever creating ambiguity between "this is a path" and "this is a version" (mirrors Cargo, which never accepts a bare string for a path dependency for the same reason). Value is a **directory** path (containing that dependency's own `wx.json`), not a path to the manifest file itself. |

**Deliberately absent:**
- No `version` field — no registry to publish to yet; the `dependencies` shape above is
  where it slots in later.
- No `entry`/`main` path override — see below, the entry filename is a fixed constant, not
  a per-crate value.
- No `out_dir` — see "Output artifacts" below.

### Entry point: always `main.wx`, regardless of kind

This took several iterations to land on. Earlier attempts all reintroduced the
"two facts that must agree" problem:

- **`main.wx` for binaries / `lib.wx` for libraries`** (Rust's convention) — filename
  implies kind, which is a second, independent way of stating the same fact `type` states,
  and the two can disagree (rename the file, silently change what's being compiled).
- **Explicit `entry` field, drop the convention** — solves the location question but not
  kind, so `type` comes right back as a second required field alongside it. No net
  simplification.
- **`bin`/`lib` as the manifest key itself, value is the path** (mirroring Cargo's
  `[lib]`/`[[bin]]` sections) — works, but the two-possible-keys shape exists only to avoid
  a redundant path value next to a redundant kind value.

**Settled: the entry filename is a fixed constant — always `main.wx`, whether `type` is
`"bin"` or `"lib"`.** Location no longer varies with kind at all, so there is nothing left
for the two facts to disagree about. `type` becomes the *only* fact stated, once, in the
manifest.

Concrete payoff: `crates/wx-compiler/std/main.wx` never needs to be renamed. Drop a
`wx.json` with `{"name": "std", "type": "lib"}` next to the file that's already there, and
`wx check crates/wx-compiler/std` works.

## Dependency resolution

General mechanism, not `std`-special-cased — this is the part meant to scale to real
library crates:

- `open_crate` resolves each declared dependency name against a graph-wide
  name → `CrateId` map, deduped as crates load — the same pattern `use module::*` already
  uses to resolve a path segment to a `NamespaceIndex`.
- A dependency's manifest is loaded from the directory named in its `path` value.
- Transitive dependency resolution (does a binary see its dependencies' dependencies
  automatically?) is an open question, deliberately deferred until a second real library
  crate exists to test it against.

### Implicit `std` — final rule

Three rejected designs before this one, worth recording so they don't get re-proposed:

1. ~~Gate on `crate.name == "std"` in isolation~~ — fragile; doesn't generalize to any
   other crate that might need the same treatment.
2. ~~`implicitStd: false` opt-out field~~ — solves it, but is speculative generality for a
   hypothetical second foundational crate that isn't actually in wx's scope. A field like
   this is cheap to add later, additively, if that need ever materializes.
3. ~~Globally reserve the name `"std"`~~ — directly breaks the motivating workflow: name
   comparison alone can't distinguish "the real stdlib, checked standalone" from "an
   impostor," so a blanket reservation rejects both.

**Settled rule**, evaluated once, graph-wide, *after* all explicit dependency resolution
completes: load the embedded stdlib under the name `std` **iff nothing in the graph
already claims that name.** Otherwise leave whatever's already there alone.

This single rule:
- **Subsumes the self-skip case for free** — when `std` itself is the root crate, it
  already occupies the name `std` before the fallback check ever runs.
- **Enables deliberate override for free** — any crate can declare
  `"dependencies": {"std": {"path": "../alternate-std"}}` and it wins automatically, purely
  by claiming the name first. No separate override mechanism needed.
- **Needs no reserved-name validation at all.** The general duplicate-crate-name-in-one-
  compilation diagnostic (already required for dependency resolution generally, independent
  of `std`) catches genuine collisions, and it's correctly scoped — a `std`-named crate
  checked completely standalone never collides with anything, matching how Cargo itself only
  enforces name uniqueness where names actually combine, not as a blanket global prohibition.

**Emergent, low-priority feature this unlocks:** local `std` patching/vendoring — declare
`"dependencies": {"std": {"path": "../my-patched-std"}}` in a scratch project to test a
stdlib fix before upstreaming it, without touching the compiler. This is whole-crate
substitution, not a partial patch — fixing one function means forking the entire stdlib
source. Backlogged (see below); cloning the repo is good enough for now.

**Follow-on this surfaces, not solved here:** `resolve_operator_traits`
(`tir/builder.rs`) currently `panic!`s if any of the twelve `#[tag = "..."]` operator-trait
items are missing. That was fine while only a broken compiler-team stdlib could trigger it.
This design makes "a standalone or replacement `std` crate that's missing some of them" a
genuinely reachable *end-user* path for the first time, so it should become a proper
diagnostic instead of a panic — worth doing alongside this work, not a pre-existing bug
only now discovered.

## Resolving kind/name — CLI and LSP

Collapsed from an earlier 4-source fallback chain (CLI flags, manifest, filename inference,
directory-name inference) down to one rule: **the manifest is the only source of truth.**
Explicitly cut, not deferred:

- **CLI flags** (`--crate-type`/`--crate-name`) — a redundant second way to state the same
  fact a manifest states.
- **Directory-name-as-default library name** — silent; a directory rename is a routine,
  often-unintentional action whose consequence (breaking every `use std::*` elsewhere)
  would be distant and confusing.

What's left:

- **No manifest** → today's anonymous single-file behavior, unchanged. Filename is
  irrelevant — could be anything.
- **Manifest present** → fully explicit, `name` + `type` read directly, nothing guessed.
- **CLI discovery**: bounded to exactly the immediate directory of whatever path is passed
  (file or directory) — *not* an open-ended upward walk. An open-ended walk is itself a
  surprise source ("which ancestor did it find"); a CLI invocation is already an explicit
  statement of intent, so it doesn't need to search further. Found → project mode, and the
  resolved identity (name/kind/entry file) is always printed, so convention-driven
  resolution (the fixed `main.wx`) is never silently surprising. Not found → anonymous
  single-file mode. Bare directory with no manifest inside → hard error.
- **LSP discovery**: deliberately kept as an open-ended upward walk from the open buffer —
  a genuinely different problem than the CLI's (an arbitrary open file can be nested
  arbitrarily deep inside a project, with no explicit statement of intent to anchor the
  search). Only the leaf-level "parse and validate a `wx.json`" logic should be shared
  between CLI and LSP, not the surrounding search strategy.
- Every ambiguous/missing state is a hard, explicit error — never a silent fallback.

## Output artifacts

**No `target/`-style directory, and not user-configurable.** Today there is exactly one
generated artifact (`<name>.wasm`), no on-disk build cache (the only "cache" anywhere is
the LSP's in-memory, per-session `state.cached`), and no build-profile concept. Library
crates emit nothing at all (`compile` on a lib root is a hard error; `check` only reports
diagnostics), which narrows this further to "one file, for binaries only." A directory
convention whose only job is to hold one file is structure for a problem that doesn't exist.

Keep today's behavior — output next to the source, `-o` override unchanged. One small,
free improvement: in project mode, default the output filename from the manifest's `name`
rather than the entry file's stem (`myapp.wasm`, not `main.wasm`).

Revisit only when a second real generated artifact appears (a persistent incremental
cache, split debug info, a source map) — and even then, keep the location fixed by
convention (maybe an env-var override for shared-cache/CI infra, à la
`CARGO_TARGET_DIR`), never a manifest field.

## Library-crate restrictions

Libraries may not declare `import`, `export`, `memory`, or `global mut` — all four banned
from the start (broader than the original plan of import/export only, deliberately chosen
over deferring `memory`/`global mut`).

Implementation:
- Checks belong in TIR's prescan, not the VFS loader — the loader only scans top-level
  items, while `pre_scan_item` also recurses into inline `module foo { }` blocks, so it's
  the only place that won't miss a nested `export { }`.
- `pre_scan_item`'s `ast::Item::Import` arm (`builder.rs` ~5252) — bail before creating the
  import namespace.
- Phase 4's `ast::Item::Export` loop (`builder.rs` ~1814) — the crate is already in hand
  there.
- Equivalent checks needed for `ast::Item::Memory` (~4957) and `ast::Item::Global` with
  `mut_span.is_some()` (~4800).
- New `E1xxx` diagnostic codes, e.g. `ImportInLibraryCrate` / `ExportInLibraryCrate` /
  `MemoryInLibraryCrate` / `MutableGlobalInLibraryCrate`.
- Confirmed no knock-on noise: `report_unused_items` already skips anything with
  `pub_span.is_some()`, so checking a library root won't drown in unused-item warnings.

## Implementation notes

- **`FileId → CrateKind` lookup**: build fresh as a `Vec`/`HashMap` at the top of
  `tir::builder::build` (the crate × module walk that builds `source_modules` already does
  this traversal), hung on `Builder`. *Not* stored on `vfs::File`/`Files` — `cmd_format`
  uses `Files` with zero crate concept and shouldn't be touched.
- **LSP go-to-definition into `std` improves for free** once it's loaded from disk with
  real absolute paths for a `wx.json`-described project, instead of always falling back to
  the virtual `wx://std/...` scheme.

## Backlog (explicitly deprioritized)

- `wx std vendor <dir>` — dump the embedded stdlib to disk so a user without a repo
  checkout can fork/patch it locally. Cheap to build later (`STDLIB_FILES` already has
  everything needed), but not important now — cloning the repo is good enough.
- `resolve_operator_traits`'s panic → proper diagnostic (see above).
- Transitive dependency resolution semantics.
- Rust-style dual `main.wx` + `lib.wx` coexistence in one directory — explicitly rejected
  in favor of single-target-only, to keep this simple.

## Suggested implementation order

1. `CrateKind` + unified `name` on `CrateGraph`, `CrateManifest` struct (unused so far) —
   pure internal refactor, no behavior change, snapshots unaffected.
2. `wx.json` parsing via `serde_json` (already a workspace dependency), general
   name-based dependency resolution, the implicit-`std` rule, CLI's bounded manifest
   discovery. This alone unblocks `wx check crates/wx-compiler/std`.
3. Library-crate restrictions (import/export/memory/global mut) using the
   `FileId → CrateKind` lookup.
4. LSP: open-ended `wx.json` discovery, sharing the manifest-parsing subroutine with the
   CLI; output filename derived from manifest `name`.
5. `resolve_operator_traits` panic → diagnostic, riding along since this work is what
   makes it reachable by ordinary use for the first time.
