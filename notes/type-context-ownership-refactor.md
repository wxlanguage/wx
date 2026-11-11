# TypeContext ownership and explicit borrowing refactor

Status: implemented (2026-11-11); see "Done: step 3". The sections after it
are the design as it was planned, kept for its reasoning.
Date: 2026-11-10; direction revised 2026-11-11 (see "Revised direction").
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

## Revised direction (2026-11-11): construction owns the AST borrow

The owned-AST-locator approach (phase 2 below, as first written) is dropped.
Auditing what TIR reads from the AST, and when, showed the borrow belongs to
checking, not to the semantic state:

| Reader | When | Needs |
| --- | --- | --- |
| `ensure_signature` (written types, params, bounds, attributes) | sweep | syntax |
| `BodyContext` (blocks, constant initializers) | sweep | syntax |
| `conformance.rs` (pointing at a written mismatch) | sweep | syntax |
| `ImplDispatch::build` (impl targets, trait paths) | before sweep | syntax |
| solver, eval, layout, member queries | any time | finished signatures and bodies only; they never force a signature |
| lowering | after checking | nothing, since 2026-11-11 (below) |

`query_state`/`query_stack` are construction bookkeeping too: outside the
signature code they are read only by three `debug_assert!`s in `solver.rs`.

So `TypeContext` today fuses two things: the semantic state the LSP keeps
(defs, dispatch, types, signatures, bodies, values, resolutions, diagnostics,
the solver) and the construction machinery that only lives while checking
(`ast_nodes`, query state and stack, per-query obligations, and the
signature/body/conformance entry points). The `'ast` lifetime belongs wholly
to the second. The target shape:

```rust
pub fn check(compilation: &CompilationUnit, strings: &mut StringInterner) -> TypeContext {
    let (defs, entries) = DefinitionRegistry::build(..); // entries keep &'ast refs
    let mut cx = TypeContext::new(defs, ..);              // owned, no lifetime
    Construction::new(compilation, entries, &mut cx).sweep();
    cx                                                    // AST borrow ends here
}
```

`Construction<'ast>` holds `entries: Vec<AstEntry<'ast>>` unchanged,
`query_state`, `query_stack` and the obligation lists, and lends `&mut
TypeContext`; signature building, body checking and conformance are its
methods. It is dropped when the sweep ends. The AST representation does not
change: no owned locator, no mirror enum, no parent table. This is the three-way
split below with one refinement: the signature-query part is the construction
phase and need not outlive it.

Open point for the prototype: the re-entry path (normalization -> `check_constant`
-> `decide_obligations`) runs during the sweep. It works on built bodies, not on
syntax, so it should live with the semantic state; confirm on real code that no
solver path needs `Construction`. If on-demand checking of a single body is ever
wanted after the sweep, a new `Construction` is built from the AST (its entries
are a deterministic walk); an arena AST or an `ItemTree` with stable item IDs is
only worth it once checking stops re-running whole-program per edit.

### Settled shapes (2026-11-11)

Measured before settling:

- After phase 1 of the sweep, no signature is ever computed and no cycle is
  hit: a temporary probe panicking on either passed the whole suite and every
  example. Every later `ensure_signature` is a read of a final status.
- What may force a signature (a call graph over `tir/`, collisions checked):
  ~45 `TypeContext` methods that turn written syntax into types (the
  `resolve_*` family, `resolve_*_signature`, name-based member selection,
  `trait_env`, `prepare_declarations_of`, the sweep) and body building. The
  solver, evaluation, `check_obligation`, `check_constant`,
  `decide_obligations`, lowering and `format.rs` cannot reach it.
- Body building calls those syntax methods at 10 sites (`typecheck.rs`,
  `typecheck/blocks.rs`, `typecheck/members.rs`).
- Deciding reaches 25 of `BodyContext`'s 199 methods, which read only `cx`,
  `body` and `scope`; building calls into them 64 times (`normalized` 23,
  `source_span` 11).

**`Construction`, a sibling of `TypeContext`, not a wrapper.** It holds the
syntax-reading scheduler and lends nothing; its operations take the context as
a parameter:

```rust
pub(super) struct Construction<'ast> {
    entries: Vec<AstEntry<'ast>>,               // ast_nodes, borrowed refs kept
    query_state: FxHashMap<DefId, QueryEntry>,
    query_stack: Vec<QueryInfo>,
    obligations: Vec<TypeObligation>,           // per-declaration runs
}
impl<'ast> Construction<'ast> {
    fn sweep(&mut self, cx: &mut TypeContext);
    fn ensure_signature(&mut self, cx: &mut TypeContext, query: QueryInfo) -> SignatureStatus;
    fn resolve_type(&mut self, cx: &mut TypeContext, obligations: &mut Vec<TypeObligation>,
                    scope: LexicalScope, type_expr: &Spanned<ast::TypeExpression>,
                    infer: InferPolicy) -> TypeIndex;
    // … the other syntax methods, same pattern
}
```

`TypeContext` keeps the products and the solver, with no lifetime; the solver,
evaluation and obligation checking stay its methods. Being a sibling is what
lets `BodyBuilder` hold `cx` and `construction` as two disjoint `&mut`s.

**`BodyContext` / `BodyBuilder`.** Deciding is its own entity, a body in its
scope and what is valid on it regardless of syntax; building uses it, and it
knows nothing of building. Rejected: an `Option<&mut Construction>` field
(runtime `expect`), a mode type parameter (typestate), and nesting a core
struct inside the builder (`self.core.cx` everywhere).

```rust
/// A body in the scope it is written in: normalize, compare, report, check
/// usefulness, decide what building left open. Knows nothing about syntax.
pub(super) struct BodyContext<'a> {
    cx: &'a mut TypeContext,
    body: &'a mut Body,
    scope: LexicalScope,
    owner: BodyOwner,
}
impl<'a> BodyContext<'a> {
    pub(super) fn new(cx: &'a mut TypeContext, body: &'a mut Body,
                      scope: LexicalScope, owner: BodyOwner) -> Self;
    pub(super) fn decide(&mut self, obligations: Obligations);
    // + the other deciding-reachable methods: decide_*, equality, normalize_at,
    // normalized, static_target, untyped_value, field_type, report_*,
    // mismatch_at, reject, push_error, source_span, exhaustiveness (`Shapes`)
}

/// Builds a body from written syntax, during construction.
pub(super) struct BodyBuilder<'a, 'ast> {
    cx: &'a mut TypeContext,
    construction: &'a mut Construction<'ast>,
    body: Body,
    scope: LexicalScope,
    owner: BodyOwner,
    obligations: Obligations,
    current: ScopeIdx,
    lookup: FxHashMap<(ScopeIdx, SymbolU32), LocalIdx>,
    scope_types: Vec<ScopeType>,
}
impl<'a, 'ast> BodyBuilder<'a, 'ast> {
    pub(super) fn new(cx: &'a mut TypeContext, construction: &'a mut Construction<'ast>,
                      scope: LexicalScope, owner: BodyOwner) -> Self;
    pub(super) fn check_body(self, expr: &Spanned<ast::Expression>,
                             expected: TypeIndex) -> (Body, Obligations);
    fn context(&mut self) -> BodyContext<'_> {
        BodyContext::new(self.cx, &mut self.body, self.scope, self.owner)
    }
}
```

Call sites: building keeps flat fields (`self.cx`, `self.body`); the 64 shared
calls become `self.context().f(..)`, with arguments that read `self` computed
first; the 10 syntax calls become
`self.construction.resolve_type(self.cx, &mut self.obligations.types, ..)`.
The solver's re-entry has no builder and no `Construction`:

```rust
fn decide_obligations(&mut self, const_index: ConstIdx) {   // on TypeContext
    let Some(obligations) = self.const_obligations.remove(&const_index) else { return };
    let mut body = std::mem::take(&mut self.bodies[index]);
    BodyContext::new(self, &mut body, scope, BodyOwner::Const(const_index)).decide(obligations);
    self.bodies[index] = body;
}
```

`const_scope` reads the constant's file and namespace from `ConstDef`, not
from the entries. The `decide_*` may move to their own `typecheck/decide.rs`.

**Order.** (1) Split `BodyContext` into `BodyContext` and `BodyBuilder`; it
does not depend on `Construction` (the builder holds only `cx` at first) and
lands and tests on its own. (2) Introduce `Construction` with the entries,
query state and stack and declaration obligations; move `ensure_signature`,
`compute_signature`, the ~45 syntax methods, the sweep, conformance and
`ImplDispatch::build`'s entry reading onto it, and give `BodyBuilder` its
`construction` field. (3) Drop `TypeContext`'s lifetimes and make `check`
return the owned context.

### Done: step 3, owned `Semantics` (2026-11-11)

`Semantics` has no lifetime. It owns `decls`, `impl_dispatch`, the solver
(built by `Semantics::new` from the constant count), the diagnostics and the
name resolutions; `Declarations::build` and `ImplDispatch::build` still write
into local diagnostics and resolutions, which then move in. The API:

```rust
pub fn check(compilation: &CompilationUnit, strings: &mut StringInterner) -> Semantics;
pub fn lower(sema: &mut Semantics, strings: &StringInterner) -> Result<MIR, ()>;
impl Semantics { pub fn diagnostics(&self) -> &[Diagnostic<FileId>]; }
```

`tir::build` is gone. `lower` refuses a `Semantics` whose checking reported an
error or a bug, so lowering never runs on a failed check, which is what
`build` guaranteed.

- **Strings are passed explicitly** (option (a), chosen with the user):
  `Semantics` interns nothing (the one interning, a string literal's
  contents, is the builder's), so its methods that read a name take
  `strings: &StringInterner` as their first parameter (125 of them, the
  solver chain included: `normalize` re-enters body deciding, which reports).
  The short-lived structs over `sema` hold it as a field instead:
  `BodyContext<'a>` and `Lowerer<'a>` (`&'a StringInterner`) and
  `SemanticsBuilder<'ast>` (`&'ast mut`); `BodyBuilder` reads its builder's.
  Clippy's `too_many_arguments` went from 12 to 18.
- **`files` moved to `SemanticsBuilder`**: only syntax readers use it (literal
  text, one diagnostic).
- **Borrows that owning broke**: four loops read `decls`/`impl_dispatch` while
  calling a `&mut` method. Each now collects the candidates that declare the
  name first (a pure read) and then queries them, as the trait-candidate loop
  beside them already did. `CallTarget` no longer borrows its parameter names
  for the whole call; it records the naming declaration and reads them on
  demand (`param_names(decls)`).
- **Tests**: the conformance, eval, layout, typecheck and satisfaction
  harnesses build through `tir::check`, so they need no `TestInputs`; the
  signatures suite keeps `TestInputs` (what its builder borrows, kept past the
  sweep) and reads the interner as `case.builder.strings`. The lowering and
  backend tests call `check` and then `lower`.
- **Tests, afterwards**: since nothing borrows anymore, every suite's
  `TestCase` owns its files, interner and `Semantics` and is built by a plain
  constructor (`TestCase::new(source)`, `checked`, `std`, `from_graph`); the
  `test_case!`/`checked_case!` macros, `TestInputs` and satisfaction's
  `with_resolved` closure are gone, and the resolutions and format harnesses
  hold `sema` whole instead of copying fields out of it. Only
  `with_pending_signatures` keeps its closure: its builder borrows the syntax.
  Phase 5's persistence tests are in `lower.rs`:
  `semantics_answers_queries_after_checking_and_after_lowering` and
  `an_erroneous_program_keeps_its_declarations_references_and_bodies`.

Validation: 1450 compiler tests pass (2 ignored), 75 formatter tests pass;
build warnings unchanged; every example checks and every binary example
builds; `cargo fmt` clean.

### Renamed (2026-11-11)

`TypeContext` is `Semantics` (variable `sema`): what the declarations mean,
not only types. `Construction` is `SemanticsBuilder` (variable `builder`),
and its `sweep` is `build`. A plain plural for the contents and `…Builder`
for what produces them, as `Body`/`BodyBuilder`; the sections below keep the
names they were written with.

The prescan's output followed: `DefinitionRegistry` is `Declarations`
(`decls`, `decls.rs`), with `DeclId`, `DeclKind`, `DeclKey` and
`FunctionDecl`, `StructDecl`, … for `DefId`, `DefKind`, `DefKey` and the
`*Def` records, and `Referent::Declaration` for `Referent::Definition`. It
records what is declared and where; what a declaration means is
`Semantics`'s. Unchanged: `solver::Definition` (an impl member's value or
requirements, a different notion), the `DuplicateDefinition` diagnostic and
`FunctionImplementation::Declaration` (a function with no body).

### Done: step 2, `Construction` (2026-11-11)

`Construction<'ast>` holds `entries: &'ast [AstEntry<'ast>]` (borrowed: the
caller keeps the prescan's `Vec`, which `ImplDispatch::build` reads first, and
construction iterates it while calling `&mut self` methods), the query state
and stack, and the declaration obligations. 66 methods moved onto it, each
taking `cx: &mut TypeContext` (or `&TypeContext`) when it needs the context:
the measured 65 plus `check_function_body`, which builds a body. A context
method may still take syntax as an argument (`resolve_type_args`,
`self_entry`, conformance's `written_part`); what moved is what reads
construction state, so `Construction` has no method that ignores `self`.
`BodyBuilder` holds `construction` beside `cx` and calls through it at the 10
measured sites. Three cuts first:

- `const_scope` reads `ConstDef`'s file and namespace and the signature's env
  (a variant's is `ROOT`).
- Conformance is not a `TypeObligation`: `check_declarations` checks it after
  a trait impl's own obligations, so `TypeObligation` is purely semantic.
- The solver's three `query_stack.is_empty()` debug asserts are dropped:
  nothing builds a signature after phase 1, and phase 1 is now visibly
  construction code.

`TypeContext` lost `'ast` (`TypeContext<'ctx, 'dispatch>`), and so did
`BodyContext` and `Lowerer`. Four methods crossed clippy's argument limit by
taking `cx` (12 `too_many_arguments`, from 8); most pass `(obligations,
file_id, namespace, ..)`, a candidate for grouping.

### Done: step 1, `BodyContext` / `BodyBuilder` (2026-11-11)

As settled, with two differences found while doing it. `BodyContext` has no
`owner`: nothing deciding reads it. And `normalized(ty)` normalizes in the
body's own scope, which 21 of its 23 building callers passed explicitly (the
argument read `self` while `context()` held it); `normalized_in(ty, env)` is
the other two, a constant's type in its own frame. `decide` and the `decide_*`
are in `typecheck/decide.rs`, exhaustiveness stays in `exhaustiveness.rs`, and
the other shared methods are one `impl BodyContext` block at the top of
`typecheck.rs`. Building reaches them through `self.context()` (61 sites).

### Done: lowering reads no AST (2026-11-11)

- `FunctionImplementation::Intrinsic` is replaced by `Parameter` (a package
  function parameter: whoever instantiates its package supplies it). Checking
  never read the intrinsic, and calls are not constant expressions, so TIR does
  not map intrinsics. `Declaration` no longer covers both a bodiless function
  and an unfulfilled parameter. No `PackageId` payload: the package is the
  declaring scope's, and per-instance fulfilment will need its own structure,
  keyed by instance and parameter, not by `FunctionIdx`.
- Lowering fulfils std's parameters: the compiler is std's instantiator.
  `std_intrinsics` builds an `FxHashMap<FunctionIdx, Intrinsic>` from std's
  package contract (sized by std's interface, not the program), resolving each
  name once and panicking on an unknown one on every build.
- An imported global or memory is recognized by its namespace,
  `Scope::Import(import)`; nothing new is stored.

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

(Resolved by the revised direction: the entry list stays borrowed and moves to
`Construction`, which does not outlive the sweep.)

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

**Superseded 2026-11-11** by "Revised direction": nothing after the sweep
needs the AST, so the entries stay borrowed inside `Construction`. Kept for
the record.

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
| Owned AST locators (`AstNode` mirror enum + item addresses) | Dropped 2026-11-11: makes construction-only data persistent; borrow it inside `Construction` instead |

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

### 2. Nothing after the sweep reads the AST

- Done 2026-11-11 for lowering (see "Revised direction"). Remaining after-sweep
  readers: none known; `members.rs:1384`'s `ast_node` assertion runs inside the
  sweep.

### 3. Real compiler-path borrowing prototype

- Prototype `Construction<'ast>` beside an owned `TypeContext` on one path
  (constant body building is a good first one), and check the re-entry path
  above against it.

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
   Query metadata now belongs to `Construction`, not to that state.
2. ~~Concrete owned AST locator layout~~: resolved 2026-11-11, no locator; the
   AST borrow lives in `Construction`.
3. Final body-builder and lowering dependency signatures after real-path prototype.
4. Repeated check API: idempotent orchestration versus explicit construction/check
   lifecycle, without speculative incremental invalidation machinery.

Do not require decisions on every helper in advance. Bring concrete tradeoffs to
the user when they affect ownership, substantial forwarding, data duplication,
memory use, or correctness.
