# 2026-08-23 — `wx format` CLI shape, and the stdlib-provider model (`type: "std"`)

## Summary

Design-only, no code written. Two threads, both resolving open questions left by
[2026-08-23-package-manifests-path-types-and-format-cli-design.md](2026-08-23-package-manifests-path-types-and-format-cli-design.md):

1. **`wx format`'s CLI surface** — settled (that devlog's Open question 1). None of the three
   shapes on the table there (A/B/C) was chosen; the problem was re-decomposed into two
   orthogonal axes first, which dissolved the tension that made the original three feel
   unsatisfying.
2. **The `wx.json` package `name` field, and how a compilation decides who provides the
   stdlib** — started from "do we still need `name` now that dependency keys are aliases?" and
   ended at a `PackageManifestKind::Std` third package type plus a non-optional
   `CompilationUnit.stdlib_package`.

Implementation details may still shift; what's recorded here is the shape and the reasoning,
not a line-by-line plan.

---

# Part 1 — `wx format`

## The observation that reframed it

`CompilationUnitBuilder::load_package` (`vfs/mod.rs:481`) already walks `module` declarations
from an entry file and returns `modules` + `path_to_module` — the exact file list, with no
dependency resolution and no manifest involved. And `open_package` already only ever looks for
`wx.json` in the entry's *own* directory (`resolve.rs:76-77`), never walking up.

So "format a whole package" and "format a module tree with no manifest" are **not two
features** — they're the same call. The manifest contributes nothing to file selection beyond
the trivial fact that the entry is `main.wx` next to it, which is computable without reading
it. That leaves the manifest as *purely* a config source, and the design splits into two
independent axes.

## Axis 1 — selection (decided)

- `wx format [PATH]...`, default `.` when no path is given.
- **Directory argument** → `<dir>/main.wx` plus its module tree, via `load_package`. Works
  with or without a `wx.json` present; the manifest is optional and only supplies config.
- **`.wx` file argument** → that file only. **Shallow.**
- A directory argument that isn't a package (no `main.wx`) is an **error**, not a silent skip —
  "formatted nothing and said so" beats "formatted nothing quietly."

Rationale for shallow file arguments, against rustfmt's precedent (rustfmt follows `mod`
declarations by default and has `--skip-children` to undo it):

- Formatting is a *write*. Naming one file and having 40 rewritten is alarming in a way a
  read-only command's over-reach isn't.
- `wx format $(git diff --name-only '*.wx')` must mean exactly those files, or it's unusable
  in pre-commit hooks and CI.
- The deep case already has a spelling: `wx format .`.
- rustfmt's follow-children behavior is arguably an artifact of rustfmt having no directory
  mode at all (`cargo fmt` is a separate wrapper that expands a crate to a file list).

No `--deep`/`--recurse` flag for now. If "this subtree's module graph but not the whole
package" ever comes up, spell it `--follow-modules` — **not** `-r`/`--recursive`, which implies
directory recursion, which is not what it would do.

Rejected: a filesystem walk (`**/*.wx`) for directory arguments. It's the more obvious mental
model and it catches orphan files unreachable from `main.wx`, but it drags in an ignore-rules
subsystem (`target/`, vendored deps, generated code, nested packages) that wx has no concept
of today. Module-graph walking needs none of that and reuses `Loader` verbatim.

## Axis 2 — config (decided)

Resolution order for a given file:

1. `--manifest <PATH>` if given.
2. If the file came from a **directory argument** that contains a `wx.json`, that manifest.
3. `./wx.json` (cwd).
4. `RendererConfig::default()`.

Deliberately **no ancestor walk**. Rule 2 is what makes a monorepo correct in a single
invocation without one — a directory target carries its own config for everything under it,
while loose file arguments use the invocation-level config.

The important structural property: `resolve_config(file: &AbsolutePath, ...) -> RendererConfig`
takes a *file* and returns a config, so the policy is swappable. Upgrading later to
rustfmt/Prettier-style nearest-ancestor lookup changes only that function's body — no flag, no
argument, no CLI surface change. Note it *does* change behavior (some file resolves to a
different config); it's surface-compatible, not behavior-compatible.

`wx-lsp` should call the same `resolve_config`. That shared call is the only thing that keeps
the editor and the CLI from disagreeing about formatting, which is the whole point of a
formatter.

## Monorepos

Not a formatter problem — a workspace problem, and deferred. Multi-package formatting needs
**per-target config resolution**, which Axis 2 rule 2 already provides; it does not need a
workspace concept. Today's answer is a shell glob:

```
wx format ./packages/*
```

Each directory becomes its own target with its own config. When a workspace manifest
(`{"workspace": {"members": [...]}}`) eventually lands, `wx format` at a workspace root becomes
"resolve members → `Vec<FormatTarget::Package>`" — a new arm in the argument→target parse.
`expand` and `resolve_config` don't change. So deferring costs nothing, *provided* config is
never invocation-global.

Also weighed: per-package format config in a monorepo is rarer than it sounds. Prettier and
rustfmt both permit per-subtree configs and most real monorepos still use one root style,
because divergent formatting across packages in one repo is usually a bug rather than an
intent. And formatting is the weakest possible motivation for designing workspaces — the
features that justify that concept are shared dependency resolution, a lockfile, one output
directory, `wx build` at the root. Workspaces designed to serve `wx format` would be designed
wrong.

## Internal shape

```rust
enum FormatTarget {
    Package { entry: AbsolutePath },   // dir arg -> <dir>/main.wx
    File    { path:  AbsolutePath },   // .wx arg
}

fn expand(target: &FormatTarget, src: &impl FileSource) -> Vec<AbsolutePath>;
fn resolve_config(file: &AbsolutePath, ctx: &ConfigCtx) -> RendererConfig;
```

`expand` for `Package` is `load_package` + collect `path_to_module` keys; for `File` it's a
one-element vec. The CLI becomes a thin `Vec<String> -> Vec<FormatTarget>` parse. Whole-package
formatting stops before `build()`, so it never needs a `CompilationUnit` (relevant to Part 2 —
it isn't dragged into needing a stdlib id).

## Smaller decisions

- **`--check` lands in the same change** as whole-package formatting. `wx format` with no
  arguments rewriting an entire package in place is a destructive default with no dry run.
- **Add `fmt` as a subcommand alias** (cargo/deno/go all use it).
- **Keep the flag named `--manifest`, not `--config`** — it points at `wx.json`, which is a
  manifest that happens to carry format settings, not a formatter config file.
- **This reverses the prior session's rejection of directory-vs-file argument sniffing.** That
  rejection was specifically about `wx format <dir>` implicitly meaning "look for `wx.json`
  here." Under this design a directory argument means "`<dir>/main.wx`'s module tree," and
  manifest lookup is a separate axis that no longer keys off the argument being a directory —
  so the original objection is satisfied rather than overridden.

## Sequencing

The selection axis can ship now against `RendererConfig::default()`. The config axis is blocked
on `PackageManifest` having a `format` section at all, which is the prior devlog's Open
question 2 (and the stray root `wx.json`'s schema reconciliation). Config is purely additive on
top of selection.

---

# Part 2 — package `name`, and who provides the stdlib

## `name` comes off `lib` manifests

Audit of where a manifest's declared `name` actually goes:

- It has exactly one consumer: `package_kind`'s `name_override.unwrap_or(name)`
  (`resolve.rs:29`), and the fallback only fires when `name_override` is `None` — which is
  **only** the root package. Every dependency passes `Some(key)`, so a dependency's own
  declared name is already ignored today.
- `PackageKind::Library { name }` is read at exactly two sites: `vfs/mod.rs:507` (registers
  into `package_by_name` + duplicate diagnostic) and `tir/builder.rs:1748` (creates the
  package's top-level namespace).
- `package_by_name` has exactly **one** non-test consumer in the whole workspace:
  `resolve.rs:95`, the implicit-std check. It's `pub` on `CompilationUnit` but nothing outside
  `vfs` reads it — TIR builds its own `symbol_lookup` in the namespace loop instead.

So the name is load-bearing for exactly one thing, and that thing is a mechanism (suppressing
std injection via a name collision), not an intrinsic need for packages to have names.

**Names belong to edges, not nodes.** A package's name in a compilation is its dependency key;
registry identity is a separate future `meta.name` and should not be merged with it (a registry
could plausibly host a package named `std` that isn't *the* std).

Consequence: `PackageManifestKind::Lib` becomes fieldless, `deserialize_package_name` goes away
(`is_valid_package_name` stays — it still validates dependency keys at `resolve.rs:155`), and a
root library has no name, so its items land in the root namespace rather than under `name::`.

An argument for keeping `name` was raised and then dropped: that a root library checked
standalone would compile under a different namespace layout than when consumed as a dependency,
so self-qualified paths (`std::math::sin` written *inside* std) would resolve in one
configuration and not the other. It's real mechanically but not observable — wx has no idiom
for self-qualification, `crates/wx-compiler/std` never writes `std::` anywhere (grepped), and
the proper fix is a keyword, not a name.

## `package::` (future, not now)

A `package::`-style path resolving to the current package's root namespace is the right way to
self-qualify, and it removes the last reason a package would need to know its own name.

Cheap when wanted: `tir/builder.rs:1745` already builds
`package_namespaces: HashMap<PackageId, NamespaceIndex>`, and every `ModuleNamespace` already
carries `ModuleDeclarationKind::Package(PackageId, FileId)`. Resolution is "find the current
file's package, look up its namespace"; the root, having no entry, falls through to the root
namespace, which is correct.

Spell it **`package`**, not `crate` — the `Crate*` → `Package*` rename just landed, and
reintroducing `crate` as user-facing vocabulary would put back the word that was just removed.

## Implicit std becomes a merged default

The root manifest's dependency map is merged over `{"std": Builtin}`:

```rust
// root manifest only
if !matches!(manifest.package, PackageManifestKind::Std) {
    dependencies.entry("std".into()).or_insert(DependencySource::Builtin);
}
```

`DependencySource` gains a `Builtin` variant (the tagged enum was designed for additive
variants — see `manifest.rs:44`). Three user-visible states, one mechanism:

| manifest | result |
|---|---|
| no `std` entry | embedded stdlib |
| `"std": {"type":"local","path":"../my-std"}` | that package, under the name `std` |
| `"package": {"type": "std"}` | the root *is* the stdlib |

This **deletes** `resolve.rs:94-97` (the `package_by_name.contains_key(&std_name)` probe),
taking with it the last consumer of `package_by_name` outside `vfs`. Default and override stop
being separate cases — both are just "whatever the `std` key resolved to."

It also fixes an implicitness complaint about the current rule: the override behavior lives in
one line of `resolve.rs` and depends on a name matching. Merged defaults are a documentable
sentence — *your dependency map is merged over `{"std": builtin}`* — and override and opt-out
become the same gesture.

The default applies to the **root manifest only**; a dependency's own std preference is ignored
and the root decides for the whole unit. Matches today's behavior (one `load_stdlib()` at the
top of `open_package`), matches Rust (a `no_std` lib works inside a std binary), and stays
consistent with the existing punt on transitive-dependency semantics.

## `PackageManifestKind::Std`

Three fieldless, symmetric variants:

```json
{ "package": { "type": "bin" } }
{ "package": { "type": "lib" } }
{ "package": { "type": "std" } }
```

Chosen because it's honest about what's being declared — not "my std slot is empty" but "I am a
stdlib, I provide the tagged items." Single-valued, so it cannot contradict anything else in
the document.

Known limit, explicitly accepted: a no-std *binary* is inexpressible. Not a real case — every
compilation always wants some stdlib, whether default or overridden. That invariant is exactly
what this encodes: **every compilation has exactly one stdlib provider.**

`crates/wx-compiler/std/wx.json` becomes `{"package": {"type": "std"}}` and nothing else. No
name, no dependencies, no flags.

## `CompilationUnit.stdlib_package: PackageId` — not `Option`

Exhaustive by construction, in two branches (the merged-defaults model collapses "default" and
"override" into one):

```rust
let stdlib_package = match manifest.package {
    PackageManifestKind::Std => root_id,
    _ => /* the PackageId the "std" key resolved to */,
};
```

The guarantee must be **enforced at the constructor**, not documented:

```rust
pub fn build(self, root_package: PackageId, stdlib_package: PackageId) -> CompilationUnit
```

12 call sites (`wx-compiler-wasm:88`, `wx-lsp:1434`, `wx-cli:210`, `resolve.rs:82`/`99`, and six
test harnesses). Every one already calls `load_stdlib()` first and **discards its returned
`PackageId`** — it's been returning an id nobody binds. So each site becomes
`let std_id = builder.load_stdlib(); ... builder.build(root_id, std_id)`.

When the root is the stdlib, `root_package == stdlib_package`. That's fine and meaningful.

**Hazard the non-optional type will surface:** `resolve.rs:163-168`'s `CircularDependency` arm
records a diagnostic and `continue`s **without loading the package**, so a dependency key can be
present in the manifest and yield no `PackageId`. Probably not reachable for the root's own
`std` key (the root is never inserted into `in_progress`, and sibling entries pop between
recursions) — but not traced all the way. Making the field non-optional forces an explicit
answer (fail resolution outright, or fall back to `load_stdlib()`) instead of letting a `None`
flow into TIR and resurface as the panic below.

## `#[tag]` is currently ungated — this is the tool to fix it

`tir/builder.rs:4378-4384` accepts `#[tag = "..."]` on any item in any package and does a bare
`tagged_items.insert(key, id)`. Last writer wins, and the order depends on prescan order across
packages. **So today any user package can write `#[tag = "add"]` and silently take over `+` for
the whole compilation.** Pre-existing, unrelated to this work.

With a guaranteed `stdlib_package`, gating is a comparison with no `Option` handling:

```rust
if package_id != graph.stdlib_package { /* diagnostic: #[tag] outside the stdlib */ }
```

## The panic must become a diagnostic in the same change

`resolve_operator_trait` (`tir/builder.rs:1838-1847`) `panic!`s on a missing tag, and
`builder.rs:1806` calls it unconditionally on every compilation. That panic is *legitimately*
unreachable today — its doc comment says so, because std is always loaded, so a miss is a
compiler bug.

Introducing any user-facing way to say "I provide the stdlib myself" makes it reachable from a
two-line `wx.json`, i.e. a compiler crash on valid user input. With `stdlib_package` guaranteed,
the replacement diagnostic can name a specific package rather than report an absence:

> error: the `std` package does not define `#[tag = "add"]`

Twelve tags are mandatory: `add`, `sub`, `mul`, `div`, `rem`, `neg`, `bitand`, `bitor`,
`bitxor`, `shl`, `shr`, `bitnot` (`std/main.wx:41-96`). This is also why no freestanding mode is
expressible in wx at all — `type: "std"` means "I provide the stdlib myself", never "no
stdlib".

Note the tags are found via `tagged_items` **by tag**, independent of namespaces, package names
and visibility. So "define them yourself" means declaring twelve tagged traits *anywhere* in the
root — not in a module named `std`, not necessarily `pub`, not reachable by any writable path.
The `std` *identifier* and the tag side-channel are fully orthogonal: with no std package
loaded, `std` is simply a free name, and a root package could declare its own `module std;` and
have `std::foo` resolve to it.

## Also write the Rust-level stdlib check

Independent of all the above, and complementary to `wx check crates/wx-compiler/std`:

```rust
let mut builder = vfs::CompilationUnitBuilder::new();
let std_id = builder.load_stdlib();   // std, loaded as the root
let mut graph = builder.build(std_id);
let tir = TIR::build(&mut graph);
// assert no Severity::Error diagnostics
```

No second copy, since nothing else calls `load_stdlib`. This checks the **embedded** stdlib —
the artifact actually shipped — rather than an on-disk copy that could drift, and it runs in
`cargo test -p wx-compiler` on every commit instead of being a command someone remembers to
type. Not executed this session; the pieces line up but treat it as unverified. Expect
`report_unused_items` noise (nothing imports std here) — filter to `Severity::Error`.

## Rejected alternatives (Part 2)

- **`"no_std": true` boolean.** Creates a 2×2 where one cell is undefined (`no_std: true` *and*
  a `"std"` dependency entry), needing a validation rule and a precedence decision — a flag in
  one part of the document contradicting another part of the same document. Also promises a
  freestanding capability wx cannot deliver.
- **`DependencySource::None`.** Coherent and nearly free, and it keeps everything about std in
  one place. Lost to `type: "std"` because it describes an empty slot rather than the actual
  claim ("I provide the stdlib"), and it puts a user-facing knob in the schema whose only
  correct use is inside this repo.
- **CLI flag `--no-std`.** Zero schema change, but it's a property of the package rather than
  the invocation, so it's forgettable and invisible in the repo.
- **Flip the default: std must be opted into.** Sounds principled, but `open_package`'s
  manifest-less path (`resolve.rs:79-83`) must inject std or nothing compiles — so you'd end up
  with two rules (implicit for manifest-less, explicit for manifest-having), worse than the one
  rule that exists now.
- **Derive it: "root defines the tagged traits ⇒ don't inject std."** The only other knob-free
  option, but it inverts phase order (package loading is in `vfs`, tags are discovered during
  TIR prescan), and it's spooky — adding a tagged trait would silently drop the stdlib.
- **`"std": {"type":"local","path":"."}` self-reference.** Caught by `in_progress` at
  `resolve.rs:163` and turned into a `CircularDependency` diagnostic.

---

## Open questions

1. **Does `ensure_module` merge or diagnose when a package declares `module std;` while the
   builtin std is loaded?** Both want `symbol_lookup[(Type, "std")]` — the package-namespace
   loop inserts first (`builder.rs:1745-1770`, before Phase 1), then `ensure_module_path` runs
   for the user's module. Whether that's a duplicate-symbol diagnostic, a silent shadow, or a
   merge into the std package namespace depends on `ensure_module`'s reuse-by-name behavior,
   which wasn't read closely. Pre-existing, but it's the same collision surface, so worth
   knowing before leaning on "the root can just declare `module std;`" as a supported way to
   provide your own stdlib.
2. **Duplicate `#[tag]` across packages** is silently last-wins today (see above). Worth a
   diagnostic independent of the gating work.
3. **The prior devlog's Open question 2 is still open** — the stray root `wx.json`'s
   `meta`/`format` schema vs. the implemented nested-under-`"package"` shape. This session
   decided `meta.name` is a *separate concept* from the dependency-key name, but didn't settle
   the schema. The `format` section is a hard prerequisite for Part 1's config axis.
