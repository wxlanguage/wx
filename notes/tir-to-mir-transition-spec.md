# New TIR to MIR transition specification

Status: **design specification; syntax and contract collection implemented;
scalar and aggregate TIR→MIR checkpoints and typed std function binding implemented**.
Std's provided functions now use `crate func`; primitive aliases retain their
existing type-context resolution. General package fulfillment remains deferred.
Decisions below are settled for the current compiler transition.
This describes the active `tir-refactor` implementation, not the commented-out
TIR or the older architecture notes. Source inspection: 2026-11-03.

## Goal and boundary

Produce a WebAssembly module from the checked TIR without changing the language
rules established by the new checker. Lowering consumes the checked definition
registry, signatures, body arenas, type solver, and constant evaluator; it
produces an owned MIR module. The optimizer, scheduler, and binary encoder then
consume that MIR. `wx check` and `wx build` must use the same analysis and
diagnostics path, and a failed check must never emit a module.

The first executable checkpoint may support fewer forms than the type checker,
but the unsupported boundary must be explicit. A supported, well-typed source
form must either lower correctly or produce a compiler diagnostic identifying
the missing backend feature. `ExprKind::Error` must not become a successful
`Noop`, and no form may silently disappear from the output.

## Design decisions

| Decision | Contract | Status |
| --- | --- | --- |
| MIR destination | Adapt the existing tree-shaped MIR and `opt`/`wasm`/`codegen` pipeline. Review each necessary contract change before implementation; a larger redesign needs a separate decision. | Decided |
| Scoped MIR reshaping | Separate backend IDs, declaration-order aggregate slots, TIR-owned type normalization, static relocations, and real function references. | Decided |
| First executable checkpoint | Exported scalar functions, direct calls, locals, blocks, and returns. Add aggregates and memory as later checkpoints. | Decided |
| Second executable checkpoint | Tuples and structs (including generics and zero-sized fields) lower as declaration-order aggregates; TIR owns byte offsets and size. Arrays, slices, pointers, and function references stay diagnostic-only until the memory checkpoint. | Implemented |
| Compiler-provided std items | Use `crate func ...;`, `crate const ...;`, and `crate type ...;` declarations collected in a package-wide contract map. The compiler fulfills std's contract; general package instantiation/fulfillment is deferred. | Decided |
| Std/compiler agreement | Std is maintained with the compiler. Its provided signatures and semantic types are compiler invariants, not a user-facing validation subsystem. Unknown std function parameters assert. | Decided; latest owner clarification |
| Function implementations | One `FunctionImplementation` per source function: checked body, typed compiler intrinsic, host import, or declaration without an attached implementation. Calls retain source IDs until lowering selects the implementation. | Implemented |
| Global initialization | Every global, mutable or immutable, requires a compile-time constant initializer. Emit no dynamic initializer/start function. | Decided |
| Contract-name collisions | One package-wide map keyed by `BindingKey { tier, symbol }`; duplicate keys are errors across modules. Preserve ordinary module-scoped collision rules. | Decided |
| `crate` and `pub` | Provider status and module visibility are independent. Use `pub crate func` / `pub crate const` / `pub crate type` when downstream code must see the item. | Decided; latest owner clarification |
| Constant global boundary | Require a compiler-evaluated value or symbolic data address. Runtime calls and reads of imported globals do not qualify. | Decided |

The existing MIR already has control-flow expressions, aggregate values,
places, and consumers in `opt` and codegen. Keep those strengths, but make the
small structural changes listed under "Required MIR reshaping". Propose any
further redesign with a concrete failing contract and migration cost before
changing the IR.

The scalar checkpoint proves the complete driver and emission path
while leaving the hard ABI questions visible in the next gates. Requiring
aggregates or memory in the first checkpoint would test more thesis-specific
behavior, but would also couple the first success to layout, data placement,
and memory instructions. The eventual spec requires those features either
way.

The `crate` declaration says that a package requires a member supplied by
its instantiation. In this compiler version only std is fulfilled, automatically
by the compiler. This differs from `import`, which names a Wasm host import,
and from a trait method declaration, which is an abstract member implemented
through trait dispatch. A compiler-provided function has a source signature
and a known operation; a compiler-provided type has a source name and a known
semantic type. Std/compiler agreement is an invariant maintained by compiler
authors; no separate signature-validation pass is required.

Wasm globals have a restricted initializer expression. The chosen rule is
stricter and simpler: every WX global must be evaluated to a compile-time
constant, with late-bound data addresses resolved during placement. The
constant evaluator currently handles *constant* bodies, not global bodies,
so it needs a reusable body-evaluation entry point and diagnostics for
nonconstant forms.

The previous
[`tir-architecture-implementation-plan.md`](tir-architecture-implementation-plan.md)
was written for an earlier TIR and is not a contract for direct conversion of
source item indices into MIR or Wasm indices.

## Existing inputs and outputs

### Checked input

- [`tir::check`](../crates/wx-compiler/src/tir/mod.rs) currently constructs
  `DefinitionRegistry`, `ImplDispatch`, `Solver`, and `TypeContext`, calls
  `sweep`, then drops the context and returns diagnostics. Build needs those
  objects to remain alive while lowering. `TypeContext` is mutable after the
  sweep because normalization, layout, and constant queries may intern data.
- [`DefinitionRegistry`](../crates/wx-compiler/src/tir/defs.rs) owns typed
  source identities (`FunctionIdx`, `GlobalIdx`, `MemoryIdx`, etc.) and
  `AstNodeRef` entries. `AstNodeRef` distinguishes defined functions,
  imported declarations, traits, impl members, and imported entities. Import
  module/name information is in `ImportDef` and the corresponding AST entry.
- The current `IntrinsicDefs` recognizes a fixed list of type and trait names
  in std, including bodiless primitive aliases, without a package contract
  marker. Std's compiler-provided free functions, such as `trap` and raw
  numeric operations, now use `crate func` and bind through its package
  contract. Ordinary `FunctionDeclaration` and bodiless `TypeAlias` nodes
  remain distinct from the explicit `crate func`, `crate const`, and
  `crate type` declarations collected by the parser and registry.
- [`TypeContext`](../crates/wx-compiler/src/tir/signatures.rs) owns resolved
  function signatures, `function_implementations`, `global_bodies`, constant
  bodies, export targets, type environments, and queries. A `FunctionSignature` has
  declared parameter types and a return type; it is not a Wasm signature.
- [`Body`](../crates/wx-compiler/src/tir/body.rs) is an indexed arena per
  function or initializer. Expression children precede their parent, but
  lowering must follow semantic evaluation order, not iterate the arena as a
  flat instruction list. Locals are function-wide `LocalIdx` values; `params`
  maps parameter positions to optional local bindings. Scopes, places,
  patterns, and match arms have their own indexes.
- [`TypeContext::normalize`](../crates/wx-compiler/src/tir/solver.rs),
  `TypeInterner::substitute`, `stack_elements`, `memory_layout`, and
  `aggregate_layout` are the semantic operations available to lowering.
  Do not copy the old MIR type solver into the new path.

### Current target and migration obstacles

- [`mir::MIR::build`](../crates/wx-compiler/src/mir/mod.rs) reads the removed
  owned `tir::TIR` and tree-shaped `tir::Expression`. Its builder and
  [`mir/types.rs`](../crates/wx-compiler/src/mir/types.rs) are a rewrite, not
  an API rename. `mir/builder/places.rs`, `mir/builder/intrinsics.rs`, and
  `mir/mono.rs` contain useful algorithms but also depend on the old shape.
- [`mir/layout.rs`](../crates/wx-compiler/src/mir/layout.rs) is now only a
  table builder. It accepts declaration-ordered field types, their TIR-decided
  byte offsets, and the aggregate's size/alignment, then derives the scalar
  table. It computes no size or offset itself, so `tir::AggregateLayout`
  remains the one memory-layout authority.
- The dormant backend still keys functions, globals, and memories by
  `ast::DefId`, which the active AST no longer provides. New TIR definition
  indices are source identities, while MIR needs extra identities for
  monomorphized functions. Re-enabling the modules before
  changing these contracts will yield mechanical compile failures.
- [`codegen::Builder`](../crates/wx-compiler/src/codegen/mod.rs) consumes MIR
  and calls `opt::builder`, `opt::scheduler`, and the Wasm encoder. It currently
  treats function references as integer table indices and emits indirect
  calls with `call_indirect`. Its imported globals are hardcoded as immutable
  `i32`, and imported memory limits are hardcoded. These are backend gaps,
  separate from TIR-to-MIR translation.
- [`wx build`](../crates/wx-cli/src/main.rs) currently exits before codegen.
  The separate `wx-compiler-wasm` entry point also calls the removed
  `tir::TIR::build`. Connect both only after one shared compilation API works.

## Required invariants

1. **One analysis run.** Parse/package diagnostics and checker diagnostics are
   reported before lowering. Build borrows the swept semantic context; it does
   not call `tir::check` and then rebuild TIR. Do not create a self-referential
   owned wrapper around `TypeContext` and its borrowed definitions.
2. **Source identity is not backend position.** Source `FunctionIdx`,
   `GlobalIdx`, and `MemoryIdx` identify declarations. MIR IDs identify
   emitted entities; Wasm section indices are assigned still later. Imports
   occupy Wasm index prefixes by entity kind. Generic instances need distinct
   MIR function identities.
3. **Three orders stay distinct.** Written evaluation order is observable for
   side effects; declaration order identifies parameters/fields and defines
   `StackValue::Repr`; physical memory order determines byte offsets. A named
   argument tuple records written order and a permutation to parameter order.
4. **One memory-layout authority.** Use TIR's `AggregateLayout` and
   `memory_values`: fields and flattened values are indexed by declaration,
   each with its physical byte offset. MIR must not sort fields again.
5. **Concrete MIR types.** A MIR function instance contains no unresolved
   `TypeParam`, `TypeProjection`, `Infer`, literal pseudo-type, or failed
   type. Normalize and instantiate through TIR before producing MIR types or
   Wasm signatures. `!` is divergence, not an empty ordinary value.
6. **No dropped effects.** Every source expression that may trap, call, read
   mutable state, or write state executes in the correct order and number of
   times. Compound assignment and memory stores compute their target once.
7. **Errors are explicit.** An unresolved trait call, unsupported pattern,
   unfulfilled `crate` function, bodiless ordinary call, or unavailable backend
   feature cannot compile
   as a zero-sized value or `Noop`. Backend limitations use diagnostics with
   source spans; assertions are reserved for broken compiler invariants.
8. **Deterministic output.** Function-instance worklist order, import/export
   ordering, data placement, and backend IDs must be stable for equal input.

## Proposed phase interface

The compiler driver should own the source compilation unit and stage the
registry, dispatch index, solver, diagnostics, and `TypeContext` in one scope.
After `sweep`, it checks for blocking diagnostics. Then it passes a borrowed,
crate-internal checked view to MIR lowering while the context is still alive.
`wx check` follows the same driver through analysis but does not call MIR.
The precise Rust API may be a scoped callback or a driver function with
separate stack locals; the important contract is the borrow lifetime and
single analysis run. TIR does not need to own MIR, and MIR does not need to
clone the AST, registry, bodies, or type interner.

Only a narrow crate-internal surface needs visibility beyond `tir`: source
definition/body lookup, resolved signatures and exports, type substitution and
normalization, layout, constant values, and source spans. Prefer methods on a
checked view to exposing all mutable `TypeContext` fields. Lowering may query
the context mutably, but it must not modify checked bodies or source item
identity.

## Standard-library package contract

The declaration forms are `crate func name(...) -> T;`,
`crate const NAME: T;`, and `crate type Name;`. They are the three member
kinds that can be declared inside an impl. A crate constant requires an
explicit type and has no initializer in its declaring package.
The `crate` modifier means compiler/provider-supplied; `pub` keeps its usual
module visibility meaning, so std exposes these as `pub crate func trap() -> !;`
and `pub crate type u8;`. The parser can distinguish
these from the existing package-instance item `crate "key" as alias;` by the
token after `crate`. A `crate` declaration has no body and still binds its name
in its module's ordinary type/value namespace. A bodiless ordinary free
function or type alias does not become compiler-provided merely by lacking a
body. Trait signatures remain trait requirements, not package parameters.
Generic `crate func` declarations are allowed because std already declares
generic compiler operations such as `transmute` and memory functions. Ordinary
type checking checks their uses; the correctness of std's own signatures and
constraints is a compiler invariant.
The parser records generic `crate type` parameters, but this transition needs
only non-generic provided types for std's primitives. A generic provided type
needs a separately specified provider mapping before it can be fulfilled.

The definition prescan collects contract declarations into a per-`PackageId`
record, for example
`CrateContract { members: HashMap<BindingKey, CrateMember> }`, alongside ordinary
namespace binding. `BindingKey` is the existing `(Tier, SymbolU32)` key.
`crate type` claims the type-tier key; `crate const` claims the value-tier key.
A free `crate func` claims both type and
value tiers, matching the current rule that each free function is also its
own zero-sized type. Both keys may point to the same function member. A
duplicate occupied key is diagnosed with both source spans even when the
declarations live in different modules; different tiers remain distinct.
Each `CrateMember` records its kind, typed source index, source span, and declaring
module. Ordinary items continue to collide according to their module's
existing namespace rules. This record is analogous to
package export metadata: it describes what the package declares, while the
currently selected compilation decides what actually gets emitted.

At compilation setup, the compiler binds function members of the automatically
available std package's contract. It interprets names once, attaching
`FunctionImplementation::Intrinsic(Intrinsic)` to each source `FunctionIdx`.
There is no second authoritative function-to-intrinsic table. Unknown provided
std function names assert: std is compiler-maintained, and its signatures are
assumed correct rather than compared against a separate schema. Ordinary
bodiless functions, host imports, and other packages' parameters are not
eligible merely because their names match. Prelude lookup, qualified paths,
and aliases all reach the same source identity and implementation.

`FunctionImplementation::Defined(Body)` owns a checked source block;
`Imported(ImportIdx)` names a host import; `Declaration` has no attached
implementation. This classification is not signature-query readiness. Calls
remain ordinary checked TIR calls; the lowerer expands typed intrinsics into
MIR operations without giving them function bodies or direct-call edges.
Direct scalar intrinsics are implemented; generic memory/global/layout and
transmute operations remain explicit backend limitations. Exporting an
intrinsic requires a callable wrapper and is currently diagnosed.

Primitive identities are already preinterned. The existing `IntrinsicDefs`
and type-alias signature path supply their semantic targets; they need no
function-implementation representation. Contract-gating and migrating the
remaining provided type declarations is separate work. Recognition of
std-defined `Bool`, `Char`, and language traits is also separate: those are
ordinary definitions rather than provider-filled holes. Trait method
declarations remain trait requirements. The old `#[intrinsic]` spelling must
not bypass the package contract rule.

Other packages may parse and collect the same declarations. This phase does
not implement general contract fulfillment, instance-specific values, or
separate copies of a package's namespace. If a non-std contract member is
needed by type checking or emission, report an unsupported/unfulfilled
contract with its source span. The existing registry says repeated
`crate "key" as alias` instances are distinct sites but currently resolve
through one package
namespace; full fulfillment needs to address that distinction later.

## Owned MIR contract to establish first

### Required MIR reshaping

Keep the tree expression/block structure and optimizer pipeline, with these
specific changes reviewed as one contract patch each:

1. Replace obsolete `ast::DefId` identity with backend entity IDs plus maps
   from checked source IDs. Monomorphized instances receive distinct IDs.
2. Store aggregates in declaration order on the stack and carry memory byte
   offsets as a per-slot attribute (see "Ordering model"). Remove the old
   `PhysIndex`/`decl_to_phys` semantics; update the optimizer and encoder
   consumers together.
3. Remove the old MIR type solver as an authority. Convert only normalized,
   instantiated TIR types through a narrow type-lowering interface.
4. Extend static data with relocations and late-bound memory values before
   accepting data-backed constants and globals.
5. Represent typed function references as reference values and use the Wasm
   reference-call instructions before claiming `funcref` support.

Each change is forced by a current TIR contract or a backend mismatch. Keep
the old representation for a checkpoint only when its unsupported boundary is
explicit and it cannot silently miscompile a checked program.

### Entity identities and selection

- Define separate backend IDs for functions, globals, and memories. A function
  instance key is `(source FunctionIdx, normalized concrete flat type args)`;
  a map assigns each key one MIR function ID and queues it once. An imported
  function has an external declaration and no body. Do not use a source index
  as a Wasm index or assume all instances of one source function share a MIR
  identity.
- Begin from the module's exported functions and globals' constant values;
  direct calls and function references add their targets to the worklist.
  This avoids lowering every unused standard-library body. Preserve the
  current backend behavior of emitting declared imports even if no reachable
  function calls them; imported entities remain part of the module ABI.
- Reject exporting an uninstantiated generic function unless the language
  defines a concrete export instance. A direct call to a generic import needs
  its own defined ABI rule before it can be emitted.
- Preserve source names separately from IDs. The backend must be able to map
  every emitted function/import/export to its source declaration and diagnostic
  span; generic instances keep their source origin.

### Ordering model

Three orders exist; only one of them orders values.

| Order | Owner | Rule |
| --- | --- | --- |
| Evaluation order | TIR | The order effects happen in source: left to right, receiver first. Never changed by layout or by a call's parameter permutation. |
| Slot order | MIR / Wasm ABI | Declaration pre-order: fields as declared, nested aggregates expanded depth-first. This is the only order a value has on the stack. |
| Memory order | Layout | Chosen by the compiler to minimize padding, or fixed by `#[fixed_order]`. Expressed only as a byte offset on each slot. |

The invariant: **memory order is never a value order.** Every flattened slot
carries its own byte offset, so a load or store zips the declaration-order
slot list with the same list's offsets. Nothing reorders values, neither on
the stack nor when materializing to memory; the layout permutation exists
only inside `mir::layout` while offsets are assigned.

Consequences, all mandatory:

- MIR aggregate fields and flattened slots are stored in declaration order.
  There is no `PhysIndex` and no `decl_to_phys`. A field is named by its
  declaration index (`FieldIndex`); a Wasm value is named by its declaration
  pre-order slot index (`ScalarIndex`). The two index spaces are distinct.
- Function signatures flatten parameters in declared order, then the result
  type in declared order. `func(A, B)` and `func((A, B))` therefore have the
  same Wasm type, and an exported function's external ABI is declaration
  order even when its in-memory layout is not.
- A call passes parameter values in parameter order, each value flattened in
  declaration pre-order. Named-argument permutation only changes which
  parameter slot an evaluated value lands in; it never changes evaluation
  order. When written order differs from parameter order and an argument may
  have effects, the lowerer spills to temporaries in written order first.
- Aggregate load and store walk the declaration-order slot list paired with
  each slot's byte offset. Field projection uses the declaration field index.
- A zero-sized field keeps its declaration position but contributes no slot
  and no Wasm value; its value is `Unit`. Field index stays equal to
  declaration index, so no elision map is needed.

### Types, stack slots, and aggregate layout

- Convert a fully instantiated TIR type to a MIR value type. Scalars map to
  `i32`, `i64`, `f32`, or `f64` slots with signed/narrow load semantics kept
  in MIR. `Bool`/`Char` and enums use their established stack and memory
  representations. Pointers use their memory's `Size` (`u32` or `u64`).
  Function, memory, and global *item types* are zero-sized handles; a typed
  function reference is a `funcref` value, not the item type.
- A tuple or struct MIR aggregate stores its fields in declaration order,
  size/alignment, and a flattened slot list in declaration pre-order. Each
  slot carries its memory byte offset; the layout permutation is internal to
  `mir::layout` and never appears in a value order. A zero-sized field has a
  field position and a `Unit` value but no slot. See "Ordering model".
- `func(A, B)` and `func((A, B))` have the same Wasm parameter sequence.
  Flatten parameter types in declared order, then result types in declared
  order. A single aggregate parameter can occupy multiple Wasm slots.
- Map every declared source parameter to a MIR parameter position, including
  unnamed and wildcard parameters. `Body::params` has `None` for those
  positions, while `opt::builder` currently expects the first
  `params_count` MIR locals to represent *all* parameters. Create discard
  bindings for unbound parameters or change that optimizer contract, then
  explicitly map each bound `LocalIdx` to its MIR local. Do not equate the
  source local index with the MIR local index.
- The first executable checkpoint may accept only numeric scalar signatures,
  but the MIR aggregate and ID contracts should be decided before coding it.
  Add an ABI test with fields whose memory offsets differ from declaration
  order before claiming aggregate support.

### Body and expression lowering

Use `Body::root()` and recursively lower `ExprIdx`. A per-function lowering
context holds the source body, concrete substitution, MIR locals, scope map,
temporary locals, worklist handle, and static-data references. An expression
may emit preceding statements into a sink when evaluation order or spilling
requires it; every helper must document that order.

| New TIR form | MIR obligation |
| --- | --- |
| `Int`, `Float`, `Char`, `Const`, `NextDiscriminant` | Lower using the checked concrete type and constant-value query. Preserve exact bits and narrow/signed rules. `Bool` is an enum/constant, not a separate TIR literal node. |
| `AbstractConst` | Resolve the concrete trait implementation using substituted `Self` and its flat type arguments, then evaluate or materialize the selected constant. Report an unresolved selection before MIR construction. |
| `Local`, `Global`, `Function` | Local is a flat body index. Global and function nodes are nominal zero-sized handles; materialize a Wasm global read/function ref only through the appropriate operation. |
| `PrimitiveUnary`, `PrimitiveBinary` | Select signed/unsigned/float instruction from concrete operand type. Preserve short-circuit behavior for logical operators and never evaluate the right operand early. |
| `Call`, `MethodCall`, `AbstractCall`, `AbstractMethodCall` | Instantiate flat type arguments; resolve abstract trait dispatch for the concrete instance; select intrinsic/import/defined target; record direct-call edges. Receiver executes before remaining arguments. |
| `CallRef` | Requires real `funcref` and `call_ref` support in MIR, optimizer, scheduler, and encoder; old integer table-index lowering does not implement the stated TIR representation. |
| `Tuple`, `StructConstructor`, `FieldAccess` | Evaluate elements in written order, spill when necessary, then assemble declaration-order slots. Named argument permutations change slot destinations, never evaluation order. Field projection uses the declared field index. |
| `Block`, `IfElse`, `Loop`, `Break`, `Continue`, `Return`, `Drop` | Map TIR scope IDs to MIR scopes; obtain result types from typed expressions (new `Scope` does not store the old inferred result). Preserve break values and divergence. |
| `LocalDeclaration`, `Assign`, compound assign | Destructure checked patterns; bind only after evaluating the initializer. Compute an assignment target once, including nested field updates, and preserve RHS timing. |
| `Load`, `AddressOf`, `Store`, compound store | Lower `PlaceIdx` to `(base address, static offset, memory ID, value type)`. `Deref` evaluates its pointer once; `Field` adds TIR's declaration-indexed byte offset. Emit the correct memory index and access width. |
| `Match` | The new checked pattern arena supports nested products and `Or`, while old MIR `Switch` handles a narrower scalar-case shape. First lower eligible scalar cases to `Switch`; design a general ordered decision tree with bindings and fallthrough for the rest. Do not silently treat all patterns as switch discriminants. Pattern tests require `Eq`: a scalar constant compares natively, while an aggregate constant calls the concrete `PartialEq::eq` impl selected by its `Eq` bound, so the type's own equality wins over structural comparison. Floats remain unsupported (they have no total equality) but can still be bound. |
| `String`, `Array`, `ArrayRepeat` | Materialize static allocations and their relocations in the selected memory. Use TIR's layout and constant-evaluation semantics; do not reimplement layout or silently drop unreachable-but-observable initializer effects. |
| `Error` | Reachable only after a failed analysis; compilation stops before lowering. |

The expression list is exhaustive for the current `body::ExprKind` families.
New variants must update the lowering coverage table and use an exhaustive
match in implementation; avoid a catch-all that turns future syntax into
`Noop`.

### Places and memory

`Place` already carries its value type, memory type, mutability, and span.
Resolve its concrete memory once, then lower recursive `Deref`/`Field`
steps. Field offsets come from TIR's `AggregateLayout.fields[decl_index]`;
the name can become `field_offsets` without changing semantics. Whole
aggregate loads/stores walk declaration-order slots paired with physical
offsets. Multiple memories and 32/64-bit address widths require runtime
validation; a successful single-memory test is insufficient.

Memory declaration metadata must be extracted from the current AST/registry:
defined versus imported, size type, external module/name, page limits, and
exports. New `MemoryDef` does not yet store page limits; the old backend's
`MemoryInfo` did. Avoid falling back to default limits without stating a
language rule. Memory indices are assigned by codegen after imports are
ordered, and typed memory handles never become integer indices in WX code.

### Constants, globals, data, and intrinsics

- The new constant evaluator stores declaration-order `ConstValue` scalars
  and `Allocation`s with byte relocations. MIR/static-data output must carry
  enough relocation information to resolve allocation addresses after final
  per-memory data placement. The old `StaticEntry` contains only bytes and
  alignment, so it cannot represent every new evaluator allocation.
- `Memory::INDEX` and `Memory::DATA_END` are trait associated constants, not
  free `crate` parameters. Their values depend on final Wasm memory numbering
  and static-data placement. They need explicit late-bound MIR constants or
  relocations. The current checker test for `DATA_END` establishes resolution
  and typing, not a finalized emitted value. This must be specified before
  the static-data/global-initializer slice.
- `global_bodies` are checked expression bodies, including general
  expressions. Evaluate every defined global initializer at compile time,
  whether the global is mutable or immutable. Reuse the constant evaluator's
  expression semantics for global bodies, including failure spans and symbolic
  data addresses; its current entry point evaluates constants only. This is a
  new checker rule: `wx check` must reject a nonconstant initializer, not defer
  the error to `wx build`. Existing checker tests show general calls, local
  blocks, and cross-global reads currently type-check; those tests must be
  revised to distinguish typing from constant validity. Reject
  calls, reads of runtime globals, and other nonconstant forms before codegen
  under this boundary. Emit the resulting value as a Wasm initializer;
  no start function performs global initialization. The existing backend's
  imported-global `i32` placeholder must be replaced with the resolved stack
  scalar and mutability. Std's `Global::Value` currently requires
  `StackScalar`, so a defined global holds one Wasm scalar; preserve this
  check. An imported immutable global read is still a runtime input and
  cannot appear in a defined global's initializer.
- The package contract identifies compiler-provided std functions by their
  recorded `FunctionIdx`. Bind each to a typed intrinsic implementation,
  expand it to a MIR operation, and keep it out of emitted function bodies
  and direct-call edges. `trap`, `transmute`, arithmetic/conversion, memory,
  and global operations each need an explicit entry or an
  explicit unsupported status. The current reserved-name `IntrinsicDefs`
  recognition can serve as the implementation table after it is gated by
  std's contract declarations.
- Imported functions are Wasm imports, not compiler-provided std operations.
  Bodiless ordinary functions may not be emitted as Wasm imports merely
  because they lack a body. Diagnose them before MIR emission.

## Implementation sequence and exit conditions

1. **Freeze contracts.** Record MIR IDs, aggregate slot order, the `funcref`
   target, package contract recognition, and global constant boundary in the
   implementation API. Add an exhaustive TIR-form
   coverage checklist.
   Exit: no ambiguous identity, order, or unsupported-form behavior remains
   for the first checkpoint.
2. **Fulfill std's package contract.** The parser and registry already collect
   `crate func`, `crate const`, and `crate type` declarations and diagnose
   duplicate package keys. Convert the relevant std declarations and resolve
   the compiler's implementations against them. Function binding is implemented;
   primitive aliases retain their existing resolution. Exit: source IDs for
   provided std types, constants, and functions come from the contract. Std's
   agreement with the compiler is an invariant, not a signature-validation pass.
3. **Re-enable backend types without the legacy TIR builder.** Separate MIR
   data structures from old lowering; migrate obsolete AST IDs through MIR,
   optimizer, scheduler, Wasm instruction types, and codegen. Keep backend
   fixture tests independent of the old TIR builder. Exit: the compiler crate
   builds with the backend modules enabled and an in-memory scalar MIR fixture
   emits valid Wasm.
4. **Share analysis with build.** Add the scoped checked-view driver, preserve
   parser/package/checker diagnostics, and stop on blocking errors. Exit:
   `wx check` behavior remains intact, and an internal build test can borrow
   checked signatures and a body without rebuilding analysis.
5. **Scalar vertical slice.** Lower an exported scalar function, a second
   direct callee, parameters, locals, literals, primitive arithmetic, blocks,
   returns, and exports. Wire `wx build`. Exit: a fresh program written for
   the new language rules emits Wasm that executes with expected results;
   a type error emits no module.
6. **Value ABI.** Implement tuple/struct values, named-argument permutation,
   zero-sized fields, field projection, nested aggregate parameter/result
   flattening, and storage offsets. Exit: exported Wasm signatures and
   runtime results match declaration order even when memory order differs.
7. **Control flow and data.** Add loops, branches, patterns/match, imports,
   constant-evaluated globals, static data and relocations, and std operations in
   small complete slices. Each slice includes a runtime or Wasm-structure
   assertion appropriate to its contract. No feature is marked complete on
   a checker-only test.
8. **Generic dispatch and remaining ABI features.** Drain a keyed
   monomorphization worklist, resolve abstract trait methods and constants,
   and add true `funcref`/`call_ref` support if that is not part of an earlier
   slice. Test recursion, defaults, imported calls, and multi-value returns.
   Connect `wx-compiler-wasm` and other clients after the shared driver API
   has proved stable.

## Required validation cases

- A scalar exported `add` and a second exported function that calls it;
  execute both from a Wasm host.
- An exported function with an unnamed parameter followed by a named one;
  verify the named binding reads the correct Wasm argument.
- A named call with effectful arguments written out of parameter order;
  prove effects happen in written order and parameters receive the right
  values.
- A nested struct with unequal field alignments, a zero-sized field, and
  `#[fixed_order]` counterpart; inspect signature order and memory bytes.
- A tuple passed as one value to a function declared with multiple params,
  and the reverse; verify the same Wasm type and results.
- An aggregate load and store in each of two memories; verify memory index,
  byte offsets, and 32/64-bit pointer size.
- A generic function called at two concrete types, and an abstract trait
  call selecting an impl or default; verify instance dedup and target IDs.
- An imported function, global, and memory, plus exports; verify section
  order, names, types, mutability, and limits.
- A constant array of aggregates with addresses to other allocations;
  verify bytes, relocations, alignment, and data-end values.
- A typed function reference passed/returned and called; verify a Wasm
  `funcref` value and the intended indirect-call instruction.
- `crate func`, `crate const`, and `crate type` declarations in different std modules;
  verify one package-wide `BindingKey` registry, both type/value keys for a
  function, source identity, compiler fulfillment, and a duplicate-key
  diagnostic with both spans.
- Mutable and immutable globals initialized by folded arithmetic and a
  symbolic static-data address; verify fixed Wasm initializers and no
  initializer start function. A runtime call in either initializer fails.
- Failure cases: unsupported checked form, unresolved concrete type,
  unfulfilled `crate` member, ordinary bodiless function, nonconstant global
  initializer, and invalid export; each produces a diagnostic instead of a
  panic or a partially emitted module.

Use the existing TIR tests as semantic evidence and add focused backend
fixtures only for contracts that change. End-to-end Wasm execution and binary
inspection are required for ABI claims. Existing examples written for 0.5.0
are not reliable acceptance programs without porting to the new global,
function, and package-contract semantics.
