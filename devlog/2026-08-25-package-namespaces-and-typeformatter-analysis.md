# Per-package namespaces, dependency edges, and a `TypeFormatter` post-mortem

Implementation session following the design recorded in
[`2026-08-23-format-cli-and-stdlib-provider-design.md`](2026-08-23-format-cli-and-stdlib-provider-design.md).
Two stages of the package-model refactor landed; a third planned refactor was
investigated and found to be impossible for reasons worth writing down.

## Summary

The overloaded `None` namespace is gone. Every package — the root included —
now owns a root namespace, dependency edges are materialized as ordinary module
symbols, and `Option<NamespaceIndex>` has been removed from the codebase.

The session ended on an analysis of `TypeFormatter`'s API. One dead field was
removed; the planned "pass `&CompilationUnit` instead of loose references"
cleanup was proven unimplementable and is documented below so nobody retries
it.

## Stage A1 — a package's name is a property of the edge, not the node

`PackageGraph.name` is deleted. `PackageKind` and `PackageManifestKind` are now
fieldless enums.

A package has no name of its own. It is known by the key under which a
dependent declared it, so the name lives on the `(declaring package, key)`
edge:

```rust
pub dependencies: HashMap<SymbolU32, PackageId>,
/// Inverse of `dependencies`. Well-defined only because
/// `add_dependency` keeps the mapping injective.
pub dependency_names: HashMap<PackageId, SymbolU32>,
```

`add_dependency` enforces injectivity in both directions and pushes its own
diagnostics rather than returning a status for the caller to interpret. Two
codes were added: `E2004` (`StdPackageAsDependency`) and `E2005`
(`PackageDeclaredTwice`).

The manifest key is a **declaration**, not an alias — duplicates are an error.
That keeps a future `use x as y` orthogonal to it instead of in conflict with
it, and it is what makes `dependency_names` a function rather than a
multimap.

`CompilationUnit.package_by_name` is deleted; `stdlib_package: PackageId`
replaces it. It is not an `Option`: the root package decides the stdlib for the
whole compilation, and `CompilationUnitBuilder.stdlib` is `None` only while the
stdlib itself is loading — which is exactly what stops it depending on itself,
with no check needed.

## Stage B — every package gets its own root namespace

### The bug this fixes

`None` as a namespace meant two different things: "the root package's own
top-level scope" (backed by a global `symbol_lookup` table) and "no parent".
Three bugs fell out of that single conflation:

1. A transitive dependency was nameable from anywhere in the compilation.
2. `std` could see the root package's private items.
3. `module std;` in the root silently *merged into* the stdlib's namespace.

Confirmed empirically before the fix: a root package called
`shared::from_shared()` with zero diagnostics despite never declaring `shared`.

The pre-existing `is_ancestor_or_self` guard — which had to stop the parent
walk on a crate root because "both chains dead-end at the same `None`" — was a
workaround for exactly this. It is now deleted along with the cause.

### What replaced it

`TIR.root_symbols` / `root_wildcard_imports` are gone. Two lookups replace
them:

```rust
pub package_namespaces: HashMap<PackageId, NamespaceIndex>,
pub file_namespaces: Vec<NamespaceIndex>,   // indexed by FileId
```

`ModuleNamespace` gained `package: PackageId` (every namespace is inside
exactly one, so it is stored rather than recovered by walking parents) and lost
`name`. `ModuleDeclarationKind::Package` carries only a `FileId` — the
`PackageId` would have been redundant with `ModuleNamespace.package`.

The net effect is subtractive. `lookup_global_symbol` no longer falls back to a
global store: running out of parents *is* the package boundary, which is the
whole point.

Dependency edges are materialized in `TIR::build` as plain `Module` symbols in
the declaring package's own namespace — a dependency is an implicit
`module <key>;` at the top of the entry file. Nothing global is involved, which
is what keeps a package's dependencies invisible to its own dependents, who
never declared them.

### Naming a namespace without an `Option`

Since a package has no name, "what is this namespace called?" has no
context-free answer. Rather than return `Option<SymbolU32>` — which would have
silently dropped names from diagnostics — the question was made contextual and
total:

```rust
pub fn namespace_name(&self, namespace: NamespaceIndex,
                      packages: &[PackageGraph], from: PackageId) -> SymbolU32
```

`Module`/`Import` namespaces answer from their declaration; a `Package`
namespace answers via `packages[from].dependency_names[&target]`. This is why
`TypeFormatter` carries `packages` and `from` at all — see below.

Storing the name on `Type::Namespace` was considered and rejected: a name is
not a property of a type.

## `Option<NamespaceIndex>` removal

Removed from `ResolveContext`, `AstEntry`, every item struct, and ~40 helper
signatures (`insert_symbol`, `direct_scope_lookup`, `claim_name_binding`,
`symbol_is_visible`, `pre_scan_item`, `ensure_module`, `ensure_module_path`,
…). `AssocTypeImpl` gained a real `namespace` field rather than having one
threaded to it. Several helpers that took a bare `file_id: FileId` now take
`resolve_context: ResolveContext`, which carries both halves.

## `TypeFormatter` analysis

### `type_params` was dead

The field was written by `with_type_params` and **never read**. `self.type_params`
appeared exactly twice in `tir/mod.rs`: the `&[]` initializer and the
assignment. The `Type::TypeParam` arm resolves names entirely from `owner` +
`tir` across all six `TypeParamOwner` variants, and the
`abs_index - inherited_type_param_count` arithmetic is sound (inherited params
are constructed with the *parent's* owner, and `abs_index = inherited +
own_idx`, so the subtraction always lands in range).

Removed, along with its three no-op call sites in `wx-lsp/src/lib.rs`.

### The `&mut CompilationUnit` collapse is impossible

`builder.rs` carried a TODO to collapse `interner`/`id_generator`/`files`/
`packages` into a single `&'graph mut CompilationUnit`, with a note claiming
feasibility because `'graph` appeared nowhere else. **That check looked at the
wrong lifetime.**

`Builder` holds `ast_nodes: Vec<AstEntry<'ast>>`, and `AstNodeRef<'ast>` is
`&'ast ast::Item` — pointing *into* `graph.packages[..].modules[..].ast`, i.e.
into the very `CompilationUnit`. Today that is legal only because `packages`
(shared) and `interner` (mutable) are **disjoint fields** borrowed separately
from `graph`. Merge them and the AST references must be reborrowed out of the
`&mut`, which poisons the builder for every later `&mut self` phase.

Reduced to a standalone repro of the same shape:

```rust
struct Builder<'ast, 'graph> {
    unit: &'graph mut Unit,
    nodes: Vec<&'ast Item>,
}
// for p in b.unit.packages.iter() { b.nodes.push(...) }
// b.phase2();   // &mut self
```
```
error[E0502]: cannot borrow `b` as mutable because it is also borrowed as immutable
   |     for p in b.unit.packages.iter() {   -- immutable borrow occurs here
   |     b.phase2();                         ^^ mutable borrow occurs here
```

Phases 2, 3, 3.5 and 4 are all `&mut self` calls made while `ast_nodes` is
live, so this is not a corner case. The TODO comment has been corrected in
place.

The consequence for `TypeFormatter`: it needs *shared* `interner` + *shared*
`packages`, while `Builder` holds *mutable* `interner` + shared `packages` —
two things, with no single owner the builder can name. A wider reference cannot
fix it. The achievable form is a narrower one (not yet implemented):

```rust
pub struct NameContext<'a> {
    interner: &'a ast::StringInterner,
    packages: &'a [PackageGraph],
    from: PackageId,
}
```

built on the fly from `&*self.interner` + `self.packages`, with a
`CompilationUnit::names(from)` helper for the LSP and tests. Its payoff is at
the ~10 external call sites and the LSP helper signatures, not inside the
builder — all 89 `Builder::formatter(namespace)` sites are unaffected either
way.

## Key findings

- `packages` + `from` on `TypeFormatter` serve exactly **one** match arm,
  `Type::Namespace` (`tir/mod.rs:1942`). 89 call sites thread a namespace
  through for one rare rendering path ("expected `i32`, found module `math`").
- Two stdlibs in one compilation are architecturally impossible, not merely
  disallowed: `tagged_items` is a single compilation-global map and the stdlib
  defines the shared vocabulary types (two `Memory` traits would be distinct
  `TypeIndex`es). This is what forces "the root package decides the stdlib".
- `File.package` was considered for making file→namespace lookup O(1) and
  rejected: it only narrows the search, since the specific module within the
  package still has to be found. `TIR.file_namespaces` (a `Vec` indexed by
  `FileId`) answers the actual question directly.

## Follow-ups

- **`ensure_module`'s duplicate rule** — the last behavioral piece of Stage B.
  It currently reuses *any* `Module` symbol it finds. Reuse is correct for
  `ModuleDeclarationKind::Module(..)` (two files both under `math::`); a hit on
  `Package(..)` or `Import(..)` should be a duplicate-definition diagnostic.
  This is what kills the silent `module std;` merge.
- **Tests for the new semantics** — transitive dependency not nameable from the
  root; a dependency can name its own dependencies; `module std;` is a
  duplicate definition; a package cannot see the root's items.
- **`display_type`/`display_bounds` should be infallible.** 30 call sites
  `.unwrap()` them and 6 use `.unwrap_or_default()`, which renders an *empty
  type name* into hover text. The only failure source is an interner miss — a
  compiler bug, so it wants `.expect()`. Both writers are private and every
  caller writes into a `String`, so the change is contained to one impl block.
- **`pub interner` on `TypeFormatter`** exists only to serve four sites
  (`builder.rs:916, 932, 15823, 15831`), two of which are
  `.resolve(x).unwrap_or("?")`. A `TypeFormatter::resolve` returning `&str`
  makes the field private and removes the placeholders together.
- **The two constructors disagree** — `Builder::formatter(namespace)` derives
  the package while `TIR::formatter(interner, packages, from)` takes it raw,
  and four of its five external callers write `tir.namespaces[x].package` by
  hand.
- **`display_kind` reads only `self.tir`** and belongs on `TIR`.
- `wx-lsp/src/symbol_index.rs` no longer emits a named `GlobalDefinition` for
  package namespaces (they have no name), so `std` is not completable by name.
  It should emit one per incoming edge instead — strictly better, since a
  package would be listed under whatever each dependent calls it.
- `wx-lsp/src/completion.rs::file_namespace` still does two linear scans;
  `tir.file_namespaces` now answers it directly.

## Note on test state

`test_f32_scale_pow2_wasmtime`, `test_f64_scale_pow2_wasmtime` and
`test_f32_sin_cos_agree_with_reference` fail — the `std/math` submodule is
in progress and unrelated to this work. The rest of the suite is green
(822 `wx-compiler` + 53 `wx-lsp`).
