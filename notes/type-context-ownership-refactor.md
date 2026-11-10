# TypeContext ownership and explicit borrowing refactor

Status: proposed design and implementation plan, not an implemented API.
Date: 2026-11-10.
Companion: [native LSP migration plan](lsp-refactor-plan.md).

## Current status

The interner ownership prerequisite is implemented in the current worktree:

```rust
let mut strings = Keyword::create_interner();
let mut builder = CompilationUnitBuilder::new(&mut strings);
builder.load_stdlib();
let root = builder.load_binary(path, source)?;
let compilation = builder.build(root); // No interner borrow remains.
tir::check(&compilation, &mut strings);
```

`CompilationUnit` no longer contains an interner. The temporary builder borrows
one for all package/module loading; this was chosen with the user over passing
an interner to each loading method because it enforces one interner per builder.
Manifest entry points accept it explicitly. Native CLI, formatter and compiler
tests have been migrated. No wrappers, new interner ownership layer, or LSP/Wasm
migration were introduced.

Checking/lowering now borrow compilation inputs immutably and strings separately.
Their old diagnostics-returning entry points remain transitional until the owned
TypeContext refactor; no diagnostics ownership changes were made in this step.

Validation: 1,450 compiler tests passed (2 ignored), 75 formatter tests passed,
native CLI tests/build passed. A new regression keeps two compilation units alive
with one interner, checks both, drops the second, then lowers and emits the first.
`cargo fmt --all -- --check` and `git diff --check HEAD` passed. CLI smoke tests
also passed for checking and building `examples/factorial`, with Wasm output
written under `/tmp/opencode` rather than the repository.

Latest design clarification: the three conceptual parts do not require exactly
three struct fields. Products may remain directly on TypeContext. Grouping is
open and should follow real parameter forwarding and disjoint borrowing needs,
not be fixed before the re-entrant compiler-path prototype.

## Conceptual ownership split: three disjoint parts

Earlier sketch: TypeContext owns computed products, solver, and signature
query system as three sibling fields. Grouping products is optional, as clarified
in Current status above. Signature rows belong to computed products;
signature query scheduling/readiness belongs to the signature engine. The earlier
combined semantic/signature-store sketch later in this document is superseded by
this split; reconcile implementation sketches against this section.

```rust
pub struct TypeContext {
    products: Products,
    solver: Solver,
    signatures: SignatureQueries,
}

struct Products {
    defs: DefinitionRegistry,
    impl_dispatch: ImplDispatch,
    types: TypeInterner,
    // Bound/generic arenas, computed signature tables, checked bodies,
    // owner-to-body mappings, exports, resolutions and diagnostics.
    diagnostics: Vec<Diagnostic<FileId>>,
    resolutions: NameResolutions,
}

struct SignatureQueries {
    ast_locations: AstLocations,
    query_state: FxHashMap<DefId, QueryEntry>,
    query_stack: Vec<QueryInfo>,
    // Signature construction/checking obligations and scheduling metadata.
}

struct Solver {
    // Derivation stack/budget, normalization cache, verdicts, layouts,
    // evaluation state/values and allocation storage initially unchanged.
}
```

Operations on either engine accept `&mut Products` and a short reborrow of the
other engine where needed. No engine stores a reference to another sibling.
Compilation inputs remain external and immutable; strings remain external and
explicitly mutable. The top-level driver destructures all three fields directly.

This separates mutable references, not the lifetime of the owned objects: all
three owned parts persist together. Nested reborrows temporarily suspend outer
access. References into product tables must end before a nested operation mutates
those tables. Operations needing only a subset of Products should borrow its
fields explicitly rather than taking `&mut Products` unnecessarily.

Solver caches/evaluated values are computed data too; retaining their existing
internal ownership initially avoids a gratuitous value-store migration. Whether
published values/allocations should move into Products is still a concrete
boundary to audit, not permission to split allocations from values that use them.

## Goal and agreed constraints

Make the compiler's semantic state owned and reusable after initial checking,
without requiring the LSP to solve compiler lifetimes. Keep mutation and field
borrows explicit. A substantial compiler refactor is acceptable to establish this
boundary; do not preserve the old architecture through opaque wrapper views.

- `CompilationUnit` is immutable after construction. Its interner moves out.
- Pass `StringInterner` explicitly; no CompilerSession or interner wrapper.
- `symbols.rs` holds keywords, the interner alias, and seeded construction.
- Keep semantic state, solver state, diagnostics, and resolutions alive for later
  queries. Do not extract a reduced frozen representation after checking.
- Checking appends diagnostics to owned context storage and returns unit.
- Lowering returns `Result<MIR, ()>` (or an equally small failure marker), with
  diagnostics retained by the context, rather than returning another diagnostics
  collection. Fix the exact public API during implementation.
- Prefer direct disjoint field borrows and explicit operation dependencies.
  Do not add `Deref`, interior mutability, unsafe pointers, or state-removal tricks
  just to preserve old method syntax.
- Start non-incrementally: replace analysis state when source changes. Keeping
  mutable state is not a promise that caches survive arbitrary input edits.
- Leave Wasm wrapper migration out of scope.

## Findings in the current compiler

### Ownership

`tir/signatures.rs::TypeContext<'ast, 'ctx, 'dispatch>` currently owns type/bound/
generic arenas, signature tables, bodies, query metadata, and obligations. It
borrows definitions, dispatch, files, AST entries, strings, resolutions,
diagnostics, and the solver. Most solver/evaluator algorithms are methods on
`TypeContext`, not on the `Solver` object itself.

Moving the borrowed fields into the current struct without changing operations
creates calls equivalent to `self.solver.operation(self)`: two mutable borrows of
overlapping storage. The ownership change therefore requires operation-boundary
changes, not just removing lifetime parameters.

### Existing phase separation must remain

`TypeContext::sweep` currently:

1. Forces declaration signatures.
2. Builds all constant bodies.
3. Checks declarations.
4. Checks/evaluates constants and decides their obligations.
5. Checks other bodies.
6. Resolves exports.

Signature construction recursively forces other signatures, publishing some
generic memberships before resolving equality values. Checking is distinct from
construction. `QueryState` records `Pending`, `InProgress`, `CycleReported`, and
`Resolved(SignatureLocation)`; obligation runs are stored per declaration.

`Solver::normalize` is currently a context method and explicitly asserts that
definition-based rewriting is not run while the signature query stack is open.
Assumption-only reduction may run during construction. Do not infer that every
solver operation should be allowed to force arbitrary signatures just because
the new borrowing shape would permit it.

### Re-entry is real, but not a generic callback framework

One important existing path is:

```text
normalize a type-level constant
  -> resolve its constant instance
  -> instance_value
  -> check_constant, if Unchecked
  -> decide_obligations
  -> body obligation checking
  -> normalization / evaluation again
```

`check_constant` pushes an evaluation frame before deciding obligations.
Normalization, equality reasoning, member judgement, impl requirements, and
constant evaluation cooperate on the same solver derivation stack and budgets.

The direct implementation should pass/reborrow concrete state objects, not
introduce a generic callback trait or an engine that suspends every query.

### Solver owns persistent values too

The existing `Solver` owns normalization cache, verdicts, recursion state, layouts,
constant/instance/static values, and allocation bytes/relocations. Values can
contain `AllocIdx`; `TypeContext::global_values` can also contain those values.
Retain all of these coherently. Do not drop allocations or reset the solver when
checking calls back into another operation.

### Borrowed AST entry list is the other ownership obstacle

`AstEntry<'ast>` carries file/namespace and an `AstNodeRef<'ast>`. The latter
borrows ordinary items, trait/impl members, enum variants, and import declarations.
`QueryEntry::ast_index` indexes this list and also establishes definition order.
The context cannot own the compilation and retain these references into it.

### Body checking currently borrows everything

`BodyContext` stores `&mut TypeContext` plus its own in-progress body, lexical
lookup, scopes, and obligations. Its local scratch state is useful, but the
whole-context reference hides the actual shared dependencies. It must be audited
alongside the solver split, not left as a back door to the old ownership problem.

## Recommended storage shape

The three conceptual pieces are:

1. Semantic tables and signature/body construction state.
2. Solver/evaluation state.
3. Read-only source/definition inputs and separately mutable side channels.

Strings are a mutable shared resource, not program-local owned state. Diagnostics
and resolutions are program-local outputs, not immutable inputs. Keep those
distinctions explicit even if operations need all three.

Illustrative owned shapes (names remain open):

```rust
pub struct TypeContext {
    defs: DefinitionRegistry,
    impl_dispatch: ImplDispatch,
    ast_locations: AstLocations,

    signatures: SignatureState,
    solver: Solver,

    diagnostics: Vec<Diagnostic<FileId>>,
    resolutions: NameResolutions,
}

struct SignatureState {
    types: TypeInterner,
    bounds: BoundArena,
    clauses: ClauseArena,
    generic_envs: GenericEnvArena,
    assumption_envs: AssumptionEnvArena,
    generic_args: GenericArgArena,

    functions: Vec<FunctionSignature>,
    structs: Vec<StructSignature>,
    // Other existing signature tables, unchanged in meaning.

    bodies: Vec<Body>,
    function_implementations: Vec<FunctionImplementation>,
    const_bodies: Vec<ConstBody>,
    global_bodies: Vec<Option<BodyIdx>>,
    global_values: Vec<Option<ConstValue>>,

    query_state: FxHashMap<DefId, QueryEntry>,
    query_stack: Vec<QueryInfo>,
    obligations: Vec<TypeObligation>,
    const_obligations: FxHashMap<ConstIdx, Obligations>,
    exports: FxHashMap<SymbolU32, ExportedItem>,
    operators: OperatorTraits,
}

struct Solver {
    // Existing owned state: derivation stack/budgets, cache, verdicts,
    // layouts, constant values/instances/statics, allocations.
}
```

`SignatureState` here includes checked bodies and type arenas, not just signature
rows. `SemanticState` may be the more accurate final name. Avoid further splitting
these arenas until real borrowing conflicts justify it. The grouping has a
purpose: it is disjoint from Solver, so operations can reborrow both independently.
It is not a view wrapping TypeContext.

Leave `global_values` in semantic state initially if moving it would add churn;
its cross-store allocation dependency is legal because both stores belong to the
same TypeContext and have the same revision. Reconsider consolidating value
storage only if there is a concrete simplification, not as a prerequisite.

## Operation signatures and mutual reborrowing

Public orchestration remains simple:

```rust
impl TypeContext {
    pub fn new(
        compilation: &CompilationUnit,
        strings: &mut StringInterner,
    ) -> Self;

    pub fn check(
        &mut self,
        compilation: &CompilationUnit,
        strings: &mut StringInterner,
    );

    pub fn lower(
        &mut self,
        compilation: &CompilationUnit,
        strings: &mut StringInterner,
    ) -> Result<MIR, ()>;

    pub fn diagnostics(&self) -> &[Diagnostic<FileId>];
}
```

Internally, operations use explicit parameters. Representative full dependencies,
not a requirement that every helper receive this whole list:

```rust
impl SignatureState {
    fn ensure_signature(
        &mut self,
        solver: &mut Solver,
        compilation: &CompilationUnit,
        defs: &DefinitionRegistry,
        dispatch: &ImplDispatch,
        ast_locations: &AstLocations,
        strings: &mut StringInterner,
        resolutions: &mut NameResolutions,
        diagnostics: &mut Vec<Diagnostic<FileId>>,
        query: QueryInfo,
    ) -> SignatureStatus;
}

impl Solver {
    fn normalize(
        &mut self,
        signatures: &mut SignatureState,
        // Explicit input/output parameters actually needed by this path.
        // The re-entrant evaluation path may need more than simple reduction.
        assumption_env: AssumptionEnvIdx,
        ty: TypeIndex,
        depth: NormalizationDepth,
        facts: RewriteFlags,
    ) -> Result<TypeIndex, SolverError>;
}
```

At the public orchestration boundary, destructure the context:

```rust
let TypeContext {
    signatures,
    solver,
    diagnostics,
    resolutions,
    defs,
    impl_dispatch,
    ast_locations,
} = self;
```

Pass those fields directly. Narrow helpers can take only `&TypeInterner`, a
specific table, or a diagnostic sink, instead of either whole mutable engine.
Long parameter lists at broad recursive boundaries are an explicit tradeoff;
do not hide them in a replacement context/reference bundle without user agreement.

### What Rust permits

Two owned objects do not store references to one another. A call temporarily
reborrows them, and can pass both through a nested call:

```rust
impl Signatures {
    fn check(&mut self, solver: &mut Solver, depth: usize) {
        if depth > 0 {
            solver.normalize(self, depth - 1);
        }
        // Both objects can be used again after the nested call returns.
    }
}

impl Solver {
    fn normalize(&mut self, signatures: &mut Signatures, depth: usize) {
        self.frames.push(depth);
        signatures.check(self, depth);
        self.frames.pop();
    }
}
```

The outer call frames remain alive; their exclusive access is suspended during
the shorter reborrow. We do not need disjoint outer execution lifetimes or a
different solver per level. References into either engine must not remain live
across a recursive call that mutates that engine.

A standalone Rust test of this pattern, including shared diagnostics and repeated
top-level queries, compiled and passed:
`/tmp/opencode/wx-semantic-borrow-probe.rs`. This proves the language-level shape,
not that all existing compiler paths have been ported successfully.

## Borrowing hazards and handling rules

### Query entries / tables across recursive calls

Do not keep `get_mut()` results or signature slices alive across recursive
checking/normalization. Copy the small status/ID/range, release the borrow, recurse,
and look up the row again. The current `ensure_signature` already releases its
query entry before `compute_signature` and reacquires it afterwards.

AST references should borrow the immutable CompilationUnit, not a mutable semantic
engine. They can then remain live while semantic state changes.

### Type-list slices while interning

Types contain `TypeList` ranges into TypeInterner. A slice borrowed from a list
cannot stay live while recursive normalization interns into the same interner.
The existing code sometimes copies lists to temporary vectors for exactly this
reason (`normalize_const` is an example). Preserve necessary existing copies.
Prefer copying small Type/ID records, indexed iteration that reacquires elements,
or local work buffers where equivalent. Do not promise zero allocation or remove
copies indiscriminately; measure and optimize after correctness is established.

### Diagnostics while reading semantic state

Reading one field while mutating the separate diagnostics field is legal. Keep
formatters scoped to the immutable fields they need. Build an owned diagnostic,
end its formatting/data borrows, then push. Do not clone entire tables to report
an error or make every diagnostic constructor borrow the whole context mutably.

### Returned evaluated-value slices

`const_value`/`instance_value` return borrowed slices after possibly mutating solver
state. A caller cannot retain such a slice while re-entering the solver. Preserve
short-lived consumption where possible; copy scalar values when that is all the
caller needs. If a real caller needs persistent aggregate access, consider a value
ID plus separate lookup rather than cloning the aggregate. Do not introduce new
value IDs without auditing the actual call sites first.

### Re-entry and one shared stack

Never `take` the solver out of the context and substitute a default for a nested
call. That loses active frames, budget, verdicts and allocation identity. Likewise,
do not borrow an individual frame across a callback that may grow the stack.
Record its index/copy metadata and reacquire afterwards.

Preserve `blocked_at`, `lowest_frame_read`, outer budgets and frame cleanup on
all Result branches. Cycle ownership and diagnostic order are observable behavior.
Only eligible successful normalization results are cached; do not memoize Pending
or assume nested calls may use the same cache policy as top-level calls.

### Existing ownership transfers are not all workarounds

The current checker takes obligation lists and in-progress bodies out of storage
for processing. Some are deliberate ownership transfers needed to mutate a body
while checking its dependencies. Audit them individually; avoid adding new
whole-engine `mem::take` operations, but do not ban local work-list moves.

## Owned AST locations

Replace persistent borrowed AST references with owned locations addressed from
immutable CompilationUnit inputs. Keep AstNodeRef as a short-lived typed result.

```rust
struct AstLocations {
    // Definition-order entries plus compact addressing data.
    // No references into CompilationUnit.
}

struct QueryEntry {
    ast_index: u32, // Still indexes definition-order entries if useful.
    state: QueryState,
    obligations: Range<u32>,
}

impl AstLocations {
    fn node<'input>(
        &self,
        compilation: &'input CompilationUnit,
        ast_index: u32,
    ) -> AstNodeRef<'input>;
}
```

Concrete representation is an implementation decision still requiring an AST
layout audit. Candidate: module address + parent-linked item locations + child
index/kind for trait/impl/import/enum members. A shared flat parent/path table
avoids one boxed path per nested definition. Do not assume all items are in a
single flat source array; nested modules and all AstNodeRef variants must work.

Requirements:

- Preserve definition/diagnostic order and exact DefId association.
- Cover nested modules, traits, impls, imports, enum variants, and synthesized
  declarations. Generated definitions without direct source nodes need explicit
  treatment matching the current scanner, not fabricated source indices.
- Resolve via indices, not repeated source-span searches or name lookup.
- No raw pointers, unsafe self-reference, AST cloning, or fresh definition scan
  per query.
- Locations are local to unchanged compilation inputs, not stable edit identities.
- Keep AST lookup independent of mutable query state where practical, so fetching
  syntax does not hold a semantic-state borrow during recursive checking.

## Alternatives considered

| Approach | Assessment |
| --- | --- |
| Owned semantic/signature engine + owned solver, explicit mutual reborrows | Recommended; preserves one recursive computation and exposes dependencies |
| Same owned storage, free functions taking separate fields | Useful for narrow helpers; potentially clearer than methods where dependencies span engines |
| Flat owned TypeContext with all algorithms still taking `&mut TypeContext` | Owns data but leaves overlapping solver/self borrows and hidden dependencies unresolved |
| Persistent solver/signature objects borrowing each other | Reject; cyclic/self-referential ownership and overlapping mutable references |
| Temporary all-fields context/reference bundle or Deref wrapper | Conflicts with requested explicit access; do not use as a mechanical migration shortcut |
| RefCell/locks/unsafe pointers | Reject as borrow-checker escape hatches; add runtime failure or synchronization without solving data flow |
| Extract a finished reduced semantic result | Superseded by user direction; loses the desired live query foundation |
| Need/Resume results, explicit work queue, or callback traits | Possible later if genuine algorithmic need; too disruptive now and changes recursive scheduling/cycle reasoning |
| Move shared arenas into yet another separately owned database immediately | Defer unless concrete borrow constraints justify it; do not preemptively fragment state |

## Body checking and lowering

Keep BodyContext's local body/lexical scratch, but remove its whole-TypeContext
dependency. Prefer a local body-builder state with operations receiving explicit
semantic/solver/input/output dependencies. This may require substantial signature
threading across `typecheck/*`; do not replace one hidden world reference with
another and call the split complete. Prototype a re-entrant body-obligation path
before committing to the final body-builder API.

Lowering still needs mutable semantic tables and solver state for normalization,
evaluation and layout; immutable inputs do not imply read-only lowering. Its
driver should borrow the relevant owned fields explicitly. Retained context data
remains usable afterwards, and all emitted spans still refer to the original
compilation. Audit `lower/*`, evaluation and layout together, including static
allocation identity and exports.

## Implementation phases and gates

### 1. Explicit interner ownership and immutable compilation

- Remove interner ownership from CompilationUnit and its builder. The temporary
  builder borrows the interner in its constructor; manifest loading and later
  compiler consumers receive it explicitly.
- Preserve keyword seeding, package symbol identity, diagnostic ordering, and
  formatting inputs. Test two compilation units using the same seeded interner.
- Make compiler compilation arguments immutable where only strings required
  mutation. Temporary legacy entry-point adapters may keep builds green, but
  remove diagnostics-returning adapters when the owned context API lands.

### 2. Owned declaration-source locations

- Audit every AST-entry creation and consumer.
- Choose the smallest owned locator representation; confirm nontrivial AST layout
  changes with the user.
- Replace borrowed entry persistence, validate identical definition order and
  source identity, and keep typed short-lived AST access.

### 3. Real compiler-path borrowing prototype

- Prototype an owned signature/semantic store and solver boundary in a bounded
  path, not just the standalone language test.
- Exercise assumption reduction during construction and normalization -> constant
  check -> obligations -> normalization after construction.
- Verify disjoint diagnostic/resolution writes without table/body cloning.
- Inspect actual parameter lists and required arena sub-borrows with the user.
  If the split requires excessive forwarding or duplicated operations, revise the
  operation boundaries before sweeping all modules.

### 4. Migrate storage and execution together

- Move existing semantic tables/query state into the chosen owned store and move
  algorithm entry points to the store/solver or explicit-field helpers.
- Make defs, dispatch, solver, diagnostics and resolutions owned context fields.
- Thread immutable CompilationUnit and mutable strings explicitly.
- Migrate BodyContext, declaration checking, solver, evaluation, layout and
  lowering. Preserve phase sequencing and one solver stack throughout.
- Remove context lifetimes, stale field-access helpers and transitional adapters.
- Keep check returning unit; lower reports diagnostics in the context and returns
  MIR or a small failure marker. Define repeated check semantics explicitly:
  should not silently duplicate diagnostics or append duplicate declarations.

### 5. Persistence and regression validation

- Construct context in a helper, return it after all temporary borrows end, and
  query it later with its immutable inputs and original interner.
- Test queries after initial checking and after lowering without resetting caches.
- Check erroneous programs retain useful declarations, references and body data.
- Keep resolution tests in `tir/resolutions.rs`; add ownership/engine tests where
  they naturally belong, with formatted multiline WX and exact target identities.
- Run full compiler and formatter suites, formatting and whitespace checks;
  validate native consumers as they are migrated. Report existing disconnected
  frontend/Wasm blockers separately.
- Update this plan and the LSP migration note as decisions become concrete.

## Regression checklist

- Signature cycles, CycleReported suppression, recursive aliases and generic
  environments; provisional memberships before equality resolution.
- Definition rewrite prohibition during construction; Pending versus Poisoned,
  depth overflow, equality rollback/tautology and cycle ownership.
- Type/constant mutual recursion, constant obligations, failed constant bodies,
  repeated queries, and a shared derivation budget/stack.
- Concrete and abstract associated types/constants, trait implementation selection,
  generic constant instances, type-level counts and array lengths.
- Static/global evaluated values, allocation bytes/relocations and lowering.
- Named labels, shorthand, locals/labels and error-recovery references.
- Diagnostic order, no duplicated diagnostics on query reuse, and no lost reports
  through changed early returns.
- Multiple packages/roots with one interner; IDs remain context-local except shared
  string symbols. No attempt to reuse program caches against changed inputs.

## Decisions still to confirm

1. Naming/scope of the state that owns types, signatures, bodies and query metadata:
   `SignatureState` versus a broader `SemanticState` (recommended broad meaning).
2. Concrete owned AST locator layout after inspecting scanner/AST nesting.
3. Final body-builder and lowering dependency signatures after real-path prototype.
4. Repeated check API: idempotent orchestration versus explicit construction/check
   lifecycle, without speculative incremental invalidation machinery.

Do not require decisions on every helper in advance. Bring concrete tradeoffs to
the user when they affect ownership, substantial forwarding, data duplication,
memory use, or correctness.
