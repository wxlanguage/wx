# TIR Phase 2 (signature/type resolution) — handoff

Status as of this note: committed on branch `tir-refactor`, 2026-09-21.

## What this task is

Phase 2 of the TIR rewrite — demand-driven signature and type resolution,
built on top of Phase 1 (`defs.rs` = prescan, `imports.rs` = `use` resolution,
`paths.rs` = shared path-walking), which was already committed before this
task started. This task's own code lives in two new files:

- `crates/wx-compiler/src/tir/types.rs` — the structurally hash-consed `Type`/
  `TypeIndex`/`TypeInterner`, ported from the old dead builder code. Pure data:
  answers "given a `Type`, what `TypeIndex` names it", never "what type does
  this path/expression have".
- `crates/wx-compiler/src/tir/signatures.rs` — everything else: generic
  params + bounds, the demand-driven `ensure_signature` driver, and one
  vertical slice per item kind on top of it.

## Important context before touching anything here

`tir/mod.rs` currently only wires in `defs`/`imports`/`literals`/`paths`/
`signatures`/`types`. The *old* TIR (`tir::builder`, the `TIR` struct itself)
is commented out, and so are `mir`/`opt`/`codegen`/`wasm` at the crate root
(`lib.rs`). This means:

- `cargo build --workspace` currently fails — `wx-fmt` and `wx-compiler-wasm`
  (and presumably `wx-cli`/`wx-lsp`) reference things that no longer exist.
  This is **pre-existing, expected, mid-refactor state**, not something this
  task broke or should fix.
- The only meaningful verification surface right now is
  `cargo test -p wx-compiler --lib tir::` (96 passed, 1 ignored as of this
  commit). `cargo test -p wx-compiler --lib` (the whole crate) also currently
  fails 3 unrelated, pre-existing `ast::tests` snapshot tests — untouched by
  anything in this task's diff, not investigated further.
- The user has said explicitly: ignore clippy on this branch for now, and
  don't chase build/test failures outside of what a given task actually
  touches.

## What's implemented and tested in `signatures.rs`

- **Generic params + bounds**: `resolve_generic_params`/`resolve_bounds`/
  `collect_bounds`. Diagnostics: `DuplicateGenericParam` (E2092),
  `ExpectedTraitBound` (E2031, rustc E0404-style).
- **The demand-driven driver**: `ensure_signature(&mut self, query: QueryInfo)`,
  guarded by `signature_state: HashMap<DefId, SignatureEntry>` holding
  `ComputeState::{Pending,InProgress,Done}`. `signature_stack: Vec<QueryInfo>`
  records in-progress frames in call order, mirroring
  `rustc_query_system::QueryInfo`/`CycleError` — `QueryInfo.requested_at` is
  the span of the reference that demanded an item, attached at the call site,
  never mutated after the fact.
- **`ItemLocation`**: `Trait`/`TraitImpl`/`InherentImpl` point into `defs.rs`'s
  own Phase-1 arenas (already fully known); every other kind points into this
  module's own `SignatureRegistry`, populated only once that kind's signature
  actually finishes resolving.
- **`TypeAlias` vertical slice**: `resolve_type` (only `TypeExpression::Path`
  implemented so far). Primitives (`#[intrinsic] pub type u8;`, or in the
  stdlib package generally — no attribute actually required, see
  `defs.rs`'s own doc comment on `intrinsics`) are resolved *eagerly* once at
  `SignatureBuilder::new()`, fully bypassing `ensure_signature`'s dispatch —
  the shared `TypeAlias` arm can then assume its body is always real.
  Cyclic-type-alias diagnostic: `CyclicTypeAlias` (E2096, rustc E0391-style,
  full per-hop chain with real spans).
- **`Trait` vertical slice**: resolves `trait X: Y + Z { ... }` via the same
  `resolve_bounds` generic-param bounds already use, then recurses
  `ensure_signature` into each supertrait to catch `trait A: B; trait B: A;`
  — same cycle machinery as type aliases, reported as `CyclicSupertrait`
  (E2082). Both cycle diagnostics now share one `report_cycle` helper
  (factored out once this became the second real consumer — see "Design
  conventions" below). Resolved bounds land in a new
  `trait_supertraits: Vec<Box<[TraitBound]>>`, indexed by the same
  `TraitIndex` `defs.traits` already assigns (no new index space needed,
  unlike `TypeAlias` which had none in Phase 1).
- **`ensure_all_signatures(&mut self)`**: the real outer Phase 2 driver —
  iterates every registered item in parse order and calls `ensure_signature`.
  Not selective by item kind, so it cannot yet run over a real program (see
  gap below).
- **`SignatureBuilder::finish(self) -> SignatureRegistry`**: assembles the
  frozen output (`type_aliases`, `trait_supertraits`, `item_lookup`, `types`)
  — mirrors `DefinitionRegistryBuilder::build`'s shape, just consuming `self`
  instead of being the constructor, since a `SignatureBuilder` stays alive
  across many `ensure_signature` calls rather than running once.
- **Tests**: one `TestCase::new(source)` drives the real pipeline end to end
  (parse → prescan → `ensure_all_signatures` → `finish()`), then looks things
  up via real path resolution (`TestCase::resolve`, `::`-separated paths —
  not a linear scan over an internal arena by name, which wouldn't respect
  namespacing/shadowing the way a real reference does).

## The one known gap: `Struct` isn't implemented yet

`a_bound_naming_a_non_trait_is_rejected` is `#[ignore]`d — its source
declares `struct NotATrait { x: i32 }` purely as a bound target, and
`ensure_all_signatures` isn't selective: it calls `ensure_signature` on
*every* registered item, including that struct, and panics on the `_ =>
todo!()` fallback since `Struct` has no arm yet. This is also why tests
build their own minimal `set_stdlib`-based source instead of loading the
real embedded stdlib (`builder.load_stdlib()`) — the real stdlib is almost
entirely `fn`/`trait`/`impl`, and `ensure_all_signatures` would panic on the
very first one.

Everything other than `TypeAlias`/`Trait` is still `_ => todo!()` in
`ensure_signature`: `Function`, `RecordStruct`/`TupleStruct`, `Enum`,
`Global`, `Memory`, `Constant`, `TypeSet`, `TraitImpl`, `InherentImpl`.
`resolve_type` likewise only handles `TypeExpression::Path` — `Pointer`,
`Array`, `Slice`, `Function`, `GenericApplication`, `Tuple`, `MemoryTagged`,
`QualifiedPath`, `Grouped` are all `todo!()`.

## What's next

1. **`Struct` (`RecordStruct`/`TupleStruct`)** — the natural next slice, and
   the one that unblocks the last ignored test. Needs a
   `StructSignature`/`structs: Vec<StructSignature>` arena in
   `SignatureRegistry` (the `StructIndex` type already exists, unused, in
   `types.rs`), `resolve_generic_params` for the struct's own type params,
   and a `resolve_type` call per field — which will also force `resolve_type`
   to grow past bare `Path`, since struct fields commonly need `Pointer`/
   `Array`/`Slice`.
2. **`Function`** next — params + return type, similar shape to a struct's
   fields.
3. **`InherentImpl`/`TraitImpl`** after that — will eventually need real
   trait-conformance checking, not just signature resolution.
4. Once enough kinds exist to walk a real program (stdlib included) without
   hitting `todo!()`, wire `ensure_all_signatures` into `tir::mod.rs`'s
   top-level `build()` as the actual Phase 2 entry point, and revisit
   whether it needs to become selective (skip dependency packages' items
   unless referenced) rather than walking every package's `ast_nodes`
   unconditionally — not yet a real question since nothing calls it outside
   tests today.

## Design conventions established this session, worth keeping consistent

- **Builder/Registry split**: a builder (`SignatureBuilder`) keeps flat,
  mutable fields during construction; a frozen, dependency-free struct
  (`SignatureRegistry`) is assembled only once, via `finish()`/`build()`, at
  the very end. Never store the frozen struct as a field on the builder
  itself mid-construction.
- **Recovery values over `Option`/`Result` plumbing**: a failed piece becomes
  `TypeIndex::ERROR` (or similar), not a hole that propagates optionality
  everywhere downstream — same pattern `BindingTarget::Error` already uses
  at the identity layer.
- **Cycle diagnostics attach the span to the destination at call time**
  (`QueryInfo.requested_at`, a required field set when `ensure_signature` is
  called), never mutated onto a stack frame after the fact — mirrors
  rustc's actual `QueryInfo` shape, confirmed by reading its source rather
  than guessing.
- **Add generality only once a second real consumer exists** — `report_cycle`
  was factored out of `report_cyclic_type_alias` only once `Trait` needed the
  same shape for `CyclicSupertrait`, not speculatively ahead of that.
- **Test lookups go through real path resolution**, never a linear scan over
  an internal arena by name — a scan would find *an* item with that spelling
  anywhere in the whole compilation, not necessarily the one namespace rules
  would actually pick, so it can silently grab the wrong item in a way real
  resolution can't.
- **Verify diagnostic codes against existing ones before adding new codes,
  and check what Rust does for the equivalent situation** — e.g.
  `CyclicTypeAlias`/`CyclicSupertrait` were confirmed as genuinely distinct
  from each other (and from `RecursiveTypeWithoutIndirection`) via rustc's
  own E0391/E0072 distinction before adding codes, not assumed.
