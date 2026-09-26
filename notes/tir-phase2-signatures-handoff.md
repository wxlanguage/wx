# TIR Phase 2 (signature/type resolution) — handoff

Status as of this note: committed on branch `tir-refactor`, 2026-09-22.

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

A struct's field *identity* (names, `pub_span`, dedup) lives in `defs.rs`'s
own Phase 1 prescan instead — see `defs::StructDef`/`StructFields`. Only
field *types* are resolved here, in `signatures.rs`'s `StructSignature`.

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
  `cargo test -p wx-compiler --lib tir::` (111 passed, 0 ignored as of this
  commit). `cargo test -p wx-compiler --lib` (the whole crate) also currently
  fails 3 unrelated, pre-existing `ast::tests` snapshot tests — untouched by
  anything in this task's diff, not investigated further. `cargo clippy` is
  currently noisy on this branch too (dead-code warnings from `types.rs`/
  `signatures.rs` not being reachable from any wired-in root yet) — the user
  has said explicitly: ignore clippy on this branch for now, and don't chase
  build/test failures outside of what a given task actually touches.

## What's implemented and tested in `signatures.rs`

- **Generic params + bounds**: `resolve_generic_params`/`resolve_bounds`/
  `collect_bounds`. Diagnostics: `DuplicateGenericParam` (E2092),
  `ExpectedTraitBound` (E2031, rustc E0404-style).
- **The demand-driven driver**: `ensure_signature(&mut self, query: QueryInfo)`,
  guarded by `query_state: HashMap<QueryKey, QueryEntry>` holding
  `ComputeState::{Pending,InProgress,CycleReported,Done}`. `QueryKey` wraps a
  `QueryKind` (one variant, `Signature`, today — deliberately kept as an enum
  so a later, genuinely separate query, e.g. body-checking, has a home to
  plug into without re-deriving this state machine) plus a `DefId`.
  `query_stack: Vec<QueryFrame>` records in-progress frames in call order,
  mirroring `rustc_query_system::QueryInfo`/`CycleError` —
  `QueryFrame.requested_at` is the span of the reference that demanded an
  item, attached at the call site, never mutated after the fact.
  `ComputeState::CycleReported` mirrors `imports.rs`'s `ResolveStatus::Error`:
  the *first* re-entrant discovery of a still-`InProgress` query flips it to
  `CycleReported` atomically (inside `ensure_signature`'s own entry check)
  and returns `Cycle`; every *later* independent path that re-discovers the
  same query sees `CycleReported` and returns `Resolved` silently. This is
  what makes a struct/trait with two fields/bounds that both lead back to the
  same cycle report it once, not twice — confirmed as a real, previously
  untested latent bug in the trait-supertrait cycle check too (regression
  test: `a_supertrait_cycle_via_two_different_bounds_is_reported_once`).
- **`ItemLocation`**: `Trait`/`TraitImpl`/`InherentImpl`/`Struct` point into
  `defs.rs`'s own Phase-1 arenas (already fully known — a struct's identity
  doesn't need its own fields resolved, so `StructIndex` is pre-seeded here
  just like `TraitIndex`, not lazily assigned); every other kind
  (`TypeAlias`, `Function`) points into this module's own
  `SignatureRegistry`, populated only once that kind's signature actually
  finishes resolving.
- **`TypeAlias` vertical slice**: primitives (`#[intrinsic] pub type u8;`, or
  in the stdlib package generally — no attribute actually required, see
  `defs.rs`'s own doc comment on `intrinsics`) are resolved *eagerly* once at
  `SignatureBuilder::new()`, fully bypassing `ensure_signature`'s dispatch —
  the shared `TypeAlias` arm can then assume its body is always real.
  Cyclic-type-alias diagnostic: `CyclicTypeAlias` (E2096, rustc E0391-style,
  full per-hop chain with real spans).
- **`Trait` vertical slice**: resolves `trait X: Y + Z { ... }` via the same
  `resolve_bounds` generic-param bounds already use, then recurses
  `ensure_signature` into each supertrait to catch `trait A: B; trait B: A;`
  — same cycle machinery as type aliases, reported as `CyclicSupertrait`
  (E2082). Both cycle diagnostics share one `report_cycle` helper (factored
  out once this became the second real consumer). Resolved bounds land in
  `trait_supertraits: Vec<Box<[TraitBound]>>`, indexed by the same
  `TraitIndex` `defs.traits` already assigns.
- **`Struct` (`RecordStruct`/`TupleStruct`) vertical slice**: resolves each
  field's type via `resolve_type`, one-to-one with `defs.structs[..].fields`
  (a duplicate field name still gets its own resolved slot — name dedup
  already happened in `defs.rs`). Direct-recursion ("infinite size without
  indirection") detection is folded into the existing cycle machinery rather
  than a separate pass: `check_struct_direct_recursion` calls
  `ensure_signature` on any directly-embedded struct type (following into
  `Type::Tuple` elements, since a tuple embeds inline the same way a struct
  does; stopping at `Type::Pointer`/`Slice`/`Array`, since those always carry
  an indirection sigil in wx), and reports `RecursiveTypeWithoutIndirection`
  via a rustc-E0072-style diagnostic (`report_recursive_struct_cycle`) if a
  cycle closes. **Deliberately out of scope**: generic-instantiation-aware
  substitution — `struct Wrapper<T>{v:T} struct A{w:Wrapper<A>}` is not
  detected (rustc's own `params_in_repr`-style check needs the type-param
  substitution utilities the old builder had; that machinery hasn't been
  reintroduced yet). Also out of scope: bound-checking on a struct's own
  type arguments at a reference site (`resolve_type`'s `DefKind::Struct` arm
  resolves identity only, `todo!()`s on any non-empty `type_args`) — a
  struct's bounds require the struct's own signature to be `Done`, which
  would reintroduce the exact cycle risk `Struct` identity resolution is
  built to avoid.
- **`Function` (`Item::Function`/`Item::FunctionDeclaration`) vertical
  slice**: both AST variants share one `ast::FunctionSignature` shape (the
  only difference is whether a body block follows), so both funnel through
  one `AstNodeRef::Function` arm. Resolves the function's own generic params,
  then each param's type (`TypeIndex::ERROR` for an untyped param — legal
  grammar for a method's bare `self`, but `Item::Function`/
  `FunctionDeclaration` are always free functions, so there's no `Self` to
  default to), then the return type (`TypeIndex::UNIT` when `-> Result` is
  omitted). Duplicate param names are reported (`DuplicateDefinition`,
  E2000, reusing the code the old builder used for the same check) but every
  param still gets its own resolved slot, same reasoning as struct fields.
  Lands in a new `functions: Vec<FunctionSignature>`, indexed by a lazily-
  assigned `FunctionIndex` (same lazy-allocation pattern as `TypeAlias` — a
  function's identity is never referenced from inside its own signature the
  way a struct's can be, so no pre-seeding is needed).
- **`resolve_type`**: handles `TypeExpression::Path` (including a generic
  scope's own type params, and both `TypeAlias`/`Struct` path targets) and
  `TypeExpression::Tuple`. Everything else (`Pointer`, `Array`, `Slice`,
  `Function`, `GenericApplication`, `MemoryTagged`, `QualifiedPath`,
  `Grouped`) is still `todo!()`.
- **`ensure_all_signatures(&mut self)`**: the real outer Phase 2 driver —
  iterates every registered item in parse order and calls `ensure_signature`.
  Not selective by item kind, so it still cannot run over a real program
  (`Enum`/`Global`/`Memory`/`Constant`/`TypeSet`/`TraitImpl`/`InherentImpl`
  are all still `_ => todo!()`; the real stdlib uses several of these).
- **`SignatureBuilder::finish(self) -> SignatureRegistry`**: assembles the
  frozen output (`type_aliases`, `trait_supertraits`, `structs`, `functions`,
  `item_lookup`, `types`) — mirrors `DefinitionRegistryBuilder::build`'s
  shape, just consuming `self` instead of being the constructor, since a
  `SignatureBuilder` stays alive across many `ensure_signature` calls rather
  than running once.
- **Tests**: one `TestCase::new(source)` drives the real pipeline end to end
  (parse → prescan → `ensure_all_signatures` → `finish()`), then looks things
  up via real path resolution (`TestCase::resolve(namespace, path)` —
  `BindingNamespace::Type` for types/traits/structs, `::Value` for functions
  — `::`-separated paths, not a linear scan over an internal arena by name,
  which wouldn't respect namespacing/shadowing the way a real reference
  does). `defs.rs`'s own test module grew the identical `resolve` helper
  (`BindingNamespace::Type` only, so far — no `defs.rs` test has needed a
  value-namespace lookup yet), reusing the same `PathResolver` production
  machinery rather than hand-rolled lookup boilerplate.

## What's next

1. **`InherentImpl`/`TraitImpl`** — the next natural slice. Will eventually
   need real trait-conformance checking (comparing a trait's required items
   against what an impl provides), not just signature resolution for the
   impl block itself.
2. **`Enum`** — no `EnumIndex` pre-allocation exists in `defs.rs` yet (unlike
   `StructIndex`); needs the same "identity before signature" treatment if
   an enum can self-reference (it likely can't need to, since variants don't
   embed the enum type directly the way a struct field can — worth
   confirming before assuming `Enum` needs pre-seeding at all).
3. **`resolve_type` growing past `Path`/`Tuple`** — `Pointer`/`Array`/
   `Slice` are the highest-value next forms (needed for `Global`/`Memory`
   declarations and for any realistic function signature — e.g. `&[u8]`
   params), which also means ambient-memory resolution needs to exist
   first (ownership sigil + explicit-or-ambient memory, per the language's
   `heap::&[u8]` syntax).
4. **Generic struct/function instantiation** — both `resolve_type`'s
   `DefKind::Struct` arm and any call/reference site that supplies
   `type_args` currently `todo!()` on a non-empty argument list. Needs the
   type-parameter substitution utilities the old builder had before either
   bound-checking or the deferred `params_in_repr`-style recursion check
   (point 4 in the previous version of this note) can be reintroduced.
5. Once enough kinds exist to walk a real program (stdlib included) without
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
  (`QueryFrame.requested_at`, set when `ensure_signature` pushes a frame),
  never mutated onto a stack frame after the fact — mirrors rustc's actual
  `QueryInfo` shape, confirmed by reading its source rather than guessing.
- **A query that's still running but already reported its own cycle needs a
  third state, not a side table.** Adding a `HashSet<DefId>`/`Vec<bool>`
  "already reported" tracker alongside `query_state` was tried and rejected
  — it duplicates information `ComputeState` should just represent directly.
  `CycleReported` (an `InProgress`-equivalent state that stays silent for
  everyone else) is the general fix; it isn't struct-specific, so it also
  silently fixed the same latent bug in `CyclicSupertrait`.
- **Add generality only once a second real consumer exists** — `report_cycle`
  was factored out of `report_cyclic_type_alias` only once `Trait` needed the
  same shape for `CyclicSupertrait`, not speculatively ahead of that. Same
  reasoning kept `QueryKind` to one variant (`Signature`) rather than adding
  a speculative `Body` variant before anything demands one.
- **Test lookups go through real path resolution**, never a linear scan over
  an internal arena by name — a scan would find *an* item with that spelling
  anywhere in the whole compilation, not necessarily the one namespace rules
  would actually pick, so it can silently grab the wrong item in a way real
  resolution can't. Don't assume arena index 0 is "the first thing you
  declared", either — the real stdlib (loaded by `defs.rs`'s own tests, via
  `load_stdlib()`) declares its own items (e.g. `Layout`, `RawPtr` structs)
  that can occupy earlier indices than anything in the test's own source.
- **Verify diagnostic codes against existing ones before adding new codes,
  and check what Rust does for the equivalent situation** — e.g.
  `CyclicTypeAlias`/`CyclicSupertrait`/`RecursiveTypeWithoutIndirection` were
  confirmed as genuinely distinct from each other via rustc's own
  E0391/E0072 distinction before adding codes, not assumed; the duplicate
  function-param diagnostic reuses `DuplicateDefinition` (E2000) rather than
  minting a new code, matching what the old (now-dead) builder did for the
  identical check.
