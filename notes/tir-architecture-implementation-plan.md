# TIR Architecture Refactor: Implementation Plan

This note records the agreed implementation plan for splitting TIR storage and
introducing typed indexes. It complements `tir-architecture-plan.md` and takes
precedence where the older document describes read-only/frozen registries,
atomic dispatch registration, or a direct TIR-to-MIR index conversion.

## Agreed design

The refactor separates storage by mutation responsibility:

```rust
pub struct TIR {
	pub diagnostics: Vec<Diagnostic<FileId>>,
	pub types: TypeInterner,
	pub items: ItemRegistry,
	pub modules: ModuleGraph,
	pub export_block: Option<ExportBlock>,
}
```

These containers are not phase-state or read-only abstractions. Code receives
`&Container` or `&mut Container` according to what it needs. In particular,
`ItemRegistry` remains directly mutable during TIR construction, and its
dispatch maps may be incomplete while targets and members are still being
resolved.

Small `push_*` methods are used to allocate arena entries and return the correct
typed index. They do not hide later mutation or attempt to perform phase-specific
work such as resolving targets, claiming namespace names, reporting diagnostics,
or registering dispatch entries.

During construction, `Builder` owns the output pieces directly:

```rust
struct Builder<'ast, 'graph> {
	items: ItemRegistry,
	modules: ModuleGraph,
	types: TypeInterner,
	diagnostics: Vec<Diagnostic<FileId>>,
	export_block: Option<ExportBlock>,
	// compiler inputs and temporary phase state
}
```

This keeps hot builder paths short (`self.items.functions`, `self.types.resolve(..)`)
and exposes the disjoint borrows where checking actually happens. `Builder::finish`
assembles those fields into the final `TIR`.

## 1. Introduce typed TIR indexes

- Replace TIR `u32` index aliases and raw arena positions with distinct newtypes.
- Give each newtype a non-public `new(u32)` method.
- Keep the tuple field private so external crates cannot construct arbitrary
  indexes.
- Implement outward conversions only:

  ```rust
  usize::from(index)
  u32::from(index)
  ```

- Remove `as_u32()`, `as_usize()`, public raw constructors, and implicit casts.
- Update embedded index fields in `Type`, `ItemIndex`, `ImplTarget`,
  `SymbolKind`, and related records.
- Keep MIR indexes raw and independent. A TIR `FunctionIndex` is not a MIR
  function index because MIR filters, reorders, and monomorphizes functions.

Checkpoint: `cargo test -p wx-compiler` passes without behavior changes.

## 2. Extract `TypeInterner`

```rust
pub struct TypeInterner {
	entries: Vec<Type>,
	index_lookup: HashMap<Type, TypeIndex>,
}
```

- Move the type vector and `Builder::type_index_lookup` into this container.
- Make `TypeInterner::new()` seed the built-in types and build the reverse map.
- Make `intern(Type) -> TypeIndex` the normal insertion path so the vector and
  reverse map are updated together.
- Construct `TypeIndex` inside the interner from the next arena position.
- Use checked conversion when turning an arena length into `u32`.

Checkpoint: primitive index, type interning, TIR, and MIR tests pass.

## 3. Extract `ItemRegistry` and give it directly to `Builder`

Move these fields from `TIR` into `ItemRegistry`:

- functions, globals, constants, and memories
- structs, enums, traits, type sets, and type aliases
- inherent impls, trait impls, and associated-type impls
- use items and use prefixes
- `item_lookup`
- inherent-impl and trait-impl dispatch maps
- `tagged_items`

Keep the fields directly accessible within the crate so existing code can read
and mutate records without façade methods.

Add allocation helpers such as:

```rust
push_function(...) -> FunctionIndex
push_struct(...) -> StructIndex
push_trait_impl(...) -> TraitImplIndex
push_inherent_impl(...) -> InherentImplIndex
```

Each helper:

1. Reads the arena length.
2. Constructs the typed index with its private `new` method.
3. Pushes the value.
4. Updates `item_lookup` when that relationship applies to every value of the
   given kind.
5. Returns the index.

Trait impl registration remains staged:

```rust
let index = items.push_trait_impl(placeholder);
items.trait_impls[usize::from(index)].target.inner = target;
register_trait_impl(..., index);
```

`push_trait_impl` does not update dispatch. Invalid or duplicate impls remain in
storage and `item_lookup` but may intentionally be absent from dispatch.
Inherent-impl dispatch likewise remains member-driven and is updated separately.

Checkpoint: all arena allocation uses the appropriate `push_*` helper while
dispatch behavior and diagnostics remain unchanged.

## 4. Extract `ModuleGraph` and give it directly to `Builder`

```rust
pub struct ModuleGraph {
	pub namespaces: Vec<ModuleNamespace>,
	pub package_namespaces: HashMap<PackageId, NamespaceIndex>,
	pub file_namespaces: Vec<NamespaceIndex>,
	pub module_decls: Vec<ModuleDecl>,
	pub import_decls: Vec<ImportDecl>,
}
```

- Add `push_namespace`, `push_module_decl`, and `push_import_decl` helpers that
  return their typed indexes.
- Keep namespace symbol tables and other graph state directly mutable during
  resolution.
- Preserve deterministic namespace allocation order.

Checkpoint: multi-file, package, import, visibility, and LSP tests pass.

## 5. Assemble the new TIR layout

Add `Builder::finish(self) -> TIR`; do not store an intermediate nested `TIR`
inside `Builder`. This avoids migrating builder accesses first to
`self.tir.items.*` and then again to `self.items.*`.

Mechanically update field access:

```rust
tir.functions       -> tir.items.functions
tir.namespaces      -> tir.modules.namespaces
tir.types[index]    -> tir.types.entries[index]
```

Move item-local queries to `ItemRegistry`, module-local queries to `ModuleGraph`,
and pass `&TypeInterner` explicitly to item queries that inspect types. Keep only
small final-`TIR` delegates that are useful to downstream consumers.

Checkpoint: TIR snapshots and the full compiler test suite pass.

## 6. Narrow conformance-checking borrows

Refactor conformance and the substitution helpers it calls to accept the actual
resources they need, for example:

```rust
fn check_trait_conformance(
	items: &ItemRegistry,
	modules: &ModuleGraph,
	types: &mut TypeInterner,
	diagnostics: &mut Vec<Diagnostic<FileId>>,
	interner: &mut StringInterner,
	packages: &[PackageGraph],
)
```

If conformance later needs to mutate items, change the first parameter to
`&mut ItemRegistry`. Do not introduce a frozen registry, phase-state type, or
read-only façade.

Once these resources are borrowed separately, replace the current numeric
trait-impl iteration workaround with ordinary iteration where possible.

Checkpoint: trait conformance, generic impl, associated-type, and MIR tests pass.

## 7. Update consumers and documentation

- Update MIR to read through the new TIR storage fields without treating TIR
  indexes as MIR indexes.
- Update LSP symbol indexing and completion.
- Update test helpers and snapshots only where the serialized storage layout
  legitimately changes.
- Revise `tir-architecture-plan.md` to remove the read-only/freeze language,
  atomic dispatch-registration promise, and direct TIR-to-MIR index example.

## Final verification

```text
cargo fmt --check
cargo test -p wx-compiler
cargo test --workspace
```

## Non-goals

- No `ItemRegistryBuilder` or frozen-registry transition.
- No façade around every item read or mutation.
- No attempt to make dispatch complete before the existing compiler phases can
  resolve it.
- No direct identity conversion between TIR and MIR arena indexes.
- No redesign of the type checker beyond the borrow and storage changes needed
  for this refactor.
