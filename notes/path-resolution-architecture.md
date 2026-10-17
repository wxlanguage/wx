# Path Resolution Architecture for WX

## Executive conclusion

The tuple-struct bug is a symptom of a missing intermediate representation, not
a special problem with constructors.

WX currently asks syntax-specific builders to do three jobs at once:

1. resolve a written path to a declaration or associated member;
2. interpret that declaration in a context such as type, value, bound, or
   callee position;
3. materialize TIR and commit observable effects such as diagnostics and
   access/reference records.

Because those jobs are fused, `build_call_expression` cannot inspect what a
path means without partially performing the same work that
`build_path_expression` will perform later. `resolve_symbol_and_type_args` is
therefore a speculative first resolver followed by the old authoritative
resolver. The first walk is not observationally pure: qualifier resolution and
type-argument resolution record accesses, force signatures, intern types, and
can report diagnostics. Replaying it is consequently incorrect even when its
caches are idempotent.

The durable design is:

```text
AST path
   │
   ▼
resolve once ──► ResolvedPath { target, generic arguments, trace }
   │
   ├── value use ──► materialize value expression
   ├── call use  ──► classify as runtime callable / tuple constructor / error
   ├── type use  ──► materialize TypeIndex
   └── bound use ──► materialize TraitBound
```

The critical rule is that a source path occurrence has exactly one resolution
driver. Call handling must consume the already-resolved target; it must never
probe and then call the ordinary expression builder as a fallback.

`Type::Namespace` was correctly removed. `PathQualifier::{Namespace, Type}` is
the right shape for an intermediate prefix state, but it is only half of the
needed abstraction. WX also needs a first-class *terminal* result that can
represent a local, a module binding, or a type-associated member without
immediately converting it to an `Expression` or `TypeIndex`.

## What the current machinery actually does

WX has two symbol namespaces, `Type` and `Value`, and a module symbol table
keyed by `(SymbolNamespace, SymbolU32)`. A `SymbolEntry` is either a prescan
`Pending(DefId)` claim or a `Resolved { kind, visibility }` binding. This is a
sound distinction: an unresolved claim cannot accidentally expose fake
visibility, and visibility belongs to the binding rather than solely to the
underlying item. [`tir/mod.rs`](../crates/wx-compiler/src/tir/mod.rs#L1425-L1589)
and [`modules.rs`](../crates/wx-compiler/src/tir/builder/modules.rs#L158-L228)
should remain the foundation.

The difficulty begins above that foundation.

### Lexical and module lookup

`lookup_scope_chain` performs direct-scope, glob, parent, and prelude lookup,
including wildcard ambiguity. `resolve_pending_global_symbol` adds signature
forcing and cycle handling. `resolve_pending_namespace_symbol` performs a
direct lookup in an already-known module, forces pending signatures, and checks
privacy. These are useful primitives, although their error and result types
discard too much information. See [`modules.rs`, lexical lookup](../crates/wx-compiler/src/tir/builder/modules.rs#L544-L695)
and [`modules.rs`, forcing and privacy](../crates/wx-compiler/src/tir/builder/modules.rs#L853-L1000).

### Qualifier resolution

`resolve_type_identifier` resolves a first segment into
`PathQualifier::Namespace` or `PathQualifier::Type`. It also searches generic
parameters, handles `Self`, forces global bindings, diagnoses invalid type
uses, applies omitted generic arguments to structs and aliases, interns types,
and records accesses. [`types.rs`](../crates/wx-compiler/src/tir/builder/types.rs#L180-L416)

`advance_path_qualifier` advances a module prefix by direct symbol lookup or a
type prefix by associated-type/member lookup. It likewise applies generic
arguments, reports errors, and records accesses. [`paths.rs`](../crates/wx-compiler/src/tir/builder/paths.rs#L742-L835)

These functions are called “resolution” helpers, but their contract is really
“resolve, validate for one particular use, lower part of the result, report,
and record.” That contract makes them unsuitable as composable query
primitives.

### Terminal resolution and materialization

Expression paths currently have three independent top-level branches:

- a bare identifier uses `resolve_symbol_forcing` and then
  `resolved_symbol_to_expression`;
- a bare identifier with turbofish directly looks up only a global function,
  performs its own arity and argument logic, and constructs a function item;
- a multi-segment path walks a qualifier and passes the last segment to
  `build_namespace_member_expression`.

[`build_path_expression`](../crates/wx-compiler/src/tir/builder/paths.rs#L299-L534)
therefore dispatches first on the *syntactic shape* of the path, even though all
three forms ask the same semantic question: “what does this value path denote,
with these written generic arguments?” The bare-turbofish branch accepting only
`SymbolKind::Function` is the immediate reason `Pair::<i32>(...)` does not fit.

The multi-segment terminal has two genuinely different lookup mechanisms:

- a module qualifier yields a `SymbolKind` from the module's value namespace;
- a type qualifier yields a `ResolvedMember` from inherent/trait member
  resolution.

That distinction is real and should be preserved, but it should be represented
inside one terminal-result enum. Today it is hidden inside
`build_namespace_member_expression`, which immediately turns either result
into an `Expression`. [`paths.rs`](../crates/wx-compiler/src/tir/builder/paths.rs#L982-L1187)

### The tuple-constructor probe

`build_call_expression` now calls `resolve_symbol_and_type_args` before building
the callee. If it finds a tuple struct, it builds a tuple initializer. Otherwise
it asks `build_expression` to build the same path again. [`calls.rs`](../crates/wx-compiler/src/tir/builder/calls.rs#L10-L119)

The helper itself repeats the qualifier walk and returns
`Result<Option<(SymbolKind, Box<[TypeIndex]>)>, ()>`. Its `Ok(None)` combines at
least four different states:

- the terminal is a local;
- no binding was found;
- the prefix resolved to a type rather than a module;
- a binding was found but this helper deliberately does not handle its shape.

The caller interprets all of them as permission to replay ordinary resolution.
[`modules.rs`](../crates/wx-compiler/src/tir/builder/modules.rs#L1002-L1101)

This is the central design failure. “Not applicable” is not a semantic answer
to path resolution. It is evidence that the result type cannot express the
answer the caller already discovered.

## Why the repeated walk is semantically wrong

The current comments justify replay by saying forcing and interning are
idempotent. That is true but incomplete. A path walk also performs non-idempotent
work.

### Accesses are appended, not interned

`record_symbol_access` appends directly to per-item vectors. Type-parameter,
associated-type, member, and abstract-dispatch accesses are appended at other
sites as well. [`builder/mod.rs`](../crates/wx-compiler/src/tir/builder/mod.rs#L742-L810)

Consequences of replay include:

- duplicated LSP references;
- overlapping edits during rename;
- incorrect exact access counts in tests and future analyses;
- repeated conservative “used” edges for abstract dispatch;
- duplicated accesses inside turbofish type arguments even when the callee
  itself is a bare function.

For a qualified ordinary call such as `module::f::<T>()`, the tuple probe may
record `module` and `T`, then the ordinary path builder records them again. For
a type-associated call, the probe may resolve and record the type prefix before
returning `Ok(None)`, after which member resolution repeats the prefix.

The repository has already encountered the same class of bug in `use` trees:
walking one written prefix once per imported leaf created duplicate LSP
references, so `UsePrefix` now caches the walk and shares it between siblings.
[`tir/mod.rs`](../crates/wx-compiler/src/tir/mod.rs#L1234-L1280) This is strong
local evidence that “the work is cheap” is the wrong criterion; a resolution
walk represents a source occurrence and must have occurrence cardinality.

### Diagnostics have unclear ownership

Low-level helpers sometimes report and return `Err(())`, sometimes return
`None` for the caller to report, and sometimes recover with an arbitrary
candidate after reporting ambiguity. This forces every caller to know whether
an error was already emitted. The tuple probe added an `Err` poison branch
solely to avoid reporting the same qualifier error twice.

`Result<Option<T>, ()>` does not encode enough information to enforce that
discipline. It says neither what failed nor which path segments resolved before
failure. Adding more callers will multiply conventions such as “fall through on
`None`, but never on `Err`.”

### Access spans are already drifting

On successful tuple construction, the struct access is currently pushed with
the entire call span in `build_tuple_struct_call_expression`, while ordinary
path references record the identifier segment span. [`aggregates.rs`](../crates/wx-compiler/src/tir/builder/aggregates.rs#L398-L400)
An LSP rename/reference range should identify `Point`, not `Point(1, 2)`.

This happened because access recording is owned by the lowering branch rather
than by the resolved path segment. It is another manifestation of the same
layering problem.

## What was done right

Several recent changes point in the correct direction and should not be
reversed.

1. **Removing `Type::Namespace` was correct.** A module namespace is not a WX
   type and should never occupy the type interner. `PathQualifier` makes the
   intermediate sum type explicit.

2. **`SymbolEntry::Pending` versus `Resolved` is correct.** It makes resolution
   state and binding visibility explicit rather than smuggling pending state
   through `SymbolKind`.

3. **Tuple constructors should not become `Type::FunctionItem`.** Under the
   chosen WX semantics they are not first-class function values. Adding a
   transient fake function type would move a path-resolution distinction into
   the type system and require every downstream type consumer to understand an
   entity that must never reach it.

4. **Tuple structs may reserve the value namespace without being runtime
   values.** Collision behavior and expression semantics are separate. The
   value-namespace binding can prevent a same-name function while the value
   interpreter rejects bare `Point` and the call interpreter accepts
   `Point(...)`.

5. **Module and type qualifiers are genuinely distinct.** Module terminals use
   symbol-table lookup; type terminals use impl/trait resolution. A good design
   unifies their *result protocol*, not their lookup algorithms.

## Recommended semantic model

### 1. Keep `SymbolKind` as item identity

`SymbolKind` is useful as the stable identity of a declared item. Do not add
`Namespace`, `Pending`, or a synthetic runtime constructor to it.

Do stop erasing the binding around it too early. A successful lookup should
return a small `ResolvedBinding`, not only `SymbolKind`:

```rust
#[derive(Clone, Copy)]
struct ResolvedBinding {
    kind: SymbolKind,
    namespace: SymbolNamespace,
    found_in: NamespaceIndex,
    visibility: Visibility,
}
```

`found_in` is the namespace whose binding was selected, which may be a direct
declaration or re-export. This preserves the distinction already documented by
`SymbolEntry`: binding visibility and item identity are different facts. If
origin information for glob/prelude lookup is useful, add it as a separate
`BindingOrigin` rather than overloading `SymbolKind`.

The value-namespace binding for a tuple struct may continue to contain
`SymbolKind::Struct`. Its meaning becomes explicit when the terminal is
interpreted in callee position. If WX later gains several kinds of call-only
declarations, introduce a `BindingRole::TupleConstructor` (or a general
`CallOnlyItem`) on `ResolvedBinding`; do not model them as function types.

### 2. Represent the complete terminal result

Introduce one builder-internal result for an ordinary path:

```rust
struct ResolvedPath {
    target: PathTarget,
    accesses: SmallVec<[ResolvedAccess; 4]>,
}

enum PathTarget {
    Local {
        scope_index: ScopeIndex,
        local_index: LocalIndex,
    },
    Item {
        binding: ResolvedBinding,
        generic_args: GenericApplication,
    },
    Associated {
        receiver: TypeIndex,
        member: ResolvedMember,
        generic_args: GenericApplication,
    },
}

struct GenericApplication {
    /// Slots inherited from an impl/receiver plus slots owned by the item.
    slots: Box<[TypeIndex]>,
    /// The range in `slots` to which a written terminal turbofish applies.
    own: std::ops::Range<usize>,
}
```

The exact names are unimportant; the distinctions are not.

- `Local` prevents a bare path from being flattened to a global symbol.
- `Item` represents a module-table terminal, including a tuple struct found in
  the value namespace.
- `Associated` represents `Type::member`, retaining the receiver required for
  abstract constants and associated lookup.
- `GenericApplication` gives free functions, impl functions, and tuple
  constructors one invariant for inherited, explicit, and inferred slots.

`ResolvedMember` can initially remain unchanged. Over time its function and
const variants should carry the normalized `GenericApplication` rather than a
bare box whose padding convention is documented only in comments.

### 3. Split prefix walking from terminal interpretation

Avoid one enormous `resolve_path(path, PathPurpose)` function full of mode
switches. Share the mechanical walk and keep thin semantic entry points.

```rust
enum PathParent {
    Lexical,
    Qualifier(Spanned<PathQualifier>),
}

fn resolve_path_parent(
    &mut self,
    context: PathContext,
    prefix: &[ast::PathSegment],
) -> Result<PathParent, PathError>;

fn resolve_value_path(
    &mut self,
    context: PathContext,
    path: &[ast::PathSegment],
) -> Result<ResolvedPath, PathError>;
```

`resolve_path_parent` receives every segment except the terminal:

- no prefix returns `Lexical`;
- otherwise the first segment resolves to `PathQualifier` and the rest advance
  it exactly once.

`resolve_value_path` resolves the terminal according to the parent:

- `Lexical`: local first, then value-namespace scope lookup;
- `Namespace`: direct value-namespace lookup in that module;
- `Type`: `resolve_impl_member`, producing `Associated`.

The same parent walker can serve `resolve_type_path` and `resolve_bound_path`.
Their terminal adapters request the type namespace or require a trait/typeset.
The `use` prefix driver should remain separate because it intentionally runs in
different phases and is non-forcing during prescan; it may share low-level
lookup/error/trace types, but forcing it into the ordinary semantic path API
would erase an important timing distinction.

Qualified paths such as `<T as Trait>::item` also deserve their own root
resolver because they name a required trait explicitly. After resolving that
root, however, they can produce the same `PathTarget::Associated` and reuse the
same materializers as unqualified paths.

### 4. Separate resolution from materialization

Turn the current conversion functions into consumers of `PathTarget`:

```rust
fn materialize_value_path(
    &mut self,
    ctx: &mut ExprContext,
    access_ctx: AccessContext,
    resolved: ResolvedPath,
    span: TextSpan,
) -> Result<Expression, PathUseError>;

enum ResolvedCallTarget {
    Runtime(Expression),
    TupleConstructor {
        struct_index: StructIndex,
        type_args: Box<[TypeIndex]>,
    },
}

fn classify_call_target(
    &mut self,
    ctx: &mut ExprContext,
    resolved: ResolvedPath,
) -> Result<ResolvedCallTarget, PathUseError>;
```

`materialize_value_path` is the successor to
`resolved_symbol_to_expression`, `global_symbol_to_expression`, and
`build_resolved_member_expression`. It may delegate to those functions during
migration, but lookup must not occur inside the materializer.

`classify_call_target` implements the WX-specific rule:

- an `Item` containing a tuple-kind `SymbolKind::Struct` becomes
  `TupleConstructor`;
- every ordinary value target is materialized once and checked for a function
  type by the existing call logic;
- a record struct or other non-value item gets a contextual diagnostic;
- a bare tuple-constructor use passed to `materialize_value_path` reports that
  the constructor is call-only.

This expresses “a type declaration that is constructible with call syntax”
without pretending it is a function value.

### 5. Make errors data until one reporting boundary

Replace `Result<Option<T>, ()>` in path-facing APIs with a structured failure:

```rust
struct PathError {
    kind: PathErrorKind,
    resolved_prefix: SmallVec<[ResolvedAccess; 4]>,
}

enum PathErrorKind {
    NotFound { segment: Spanned<SymbolU32> },
    Ambiguous { segment: Spanned<SymbolU32>, candidates: Box<[Candidate]> },
    Private { binding: ResolvedBinding, segment: Spanned<SymbolU32> },
    Cycle { def_id: DefId, segment: Spanned<SymbolU32> },
    NotAQualifier { qualifier: PathQualifier, segment: Spanned<SymbolU32> },
    TypeArgsNotAllowed { segment: ast::PathSegment },
    TypeArgCountMismatch { expected: usize, actual: usize, span: TextSpan },
}
```

One public builder boundary commits the prefix trace and reports the error.
Consumers no longer need folklore about whether `Err(())` was already
diagnosed. Error recovery can still choose an error expression, but reporting
ownership becomes explicit.

It is reasonable to migrate gradually: first keep existing low-level
diagnostics but eliminate replay; then lift errors into `PathError` one family
at a time. The key is not to preserve `Ok(None)` as “please run another
resolver.”

### 6. Give access recording occurrence semantics

At minimum, `ResolvedPath` should carry one `ResolvedAccess` per successfully
resolved source segment, and a single `commit_path_accesses` call should append
them to the existing per-item vectors. This fixes the current ownership and
span problems without requiring a wholesale LSP rewrite.

Longer term, accesses are better represented as edges keyed by source
occurrence:

```rust
struct ReferenceEdge {
    source: SourceSpan,
    target: ReferenceTarget,
    kind: ReferenceKind,
}
```

An index can expose both `source -> target` for hover/definition and
`target -> sources` for references and unused-item analysis, deduplicating the
pair as an invariant. This is safer than storing independently appended
reverse lists on every item. It is not a substitute for a single walk—duplicate
diagnostics and work would remain—but it is a useful second line of defense.

## The resulting call pipeline

With the proposed split, a path callee follows one flow:

```rust
fn build_call_expression(...) -> Result<Expression, ()> {
    let resolved_callee = match &ast_callee.inner {
        ast::Expression::Path(path) => {
            let resolved = self.resolve_value_path(path_context(ctx), path);
            Some(self.finish_path_resolution(resolved)?)
        }
        _ => None,
    };

    if let Some(resolved) = resolved_callee {
        match self.classify_call_target(ctx, resolved)? {
            ResolvedCallTarget::TupleConstructor { struct_index, type_args } => {
                return self.build_tuple_struct_call_expression(
                    ctx,
                    struct_index,
                    type_args,
                    arguments,
                    access_ctx.expected_type,
                    expr.span,
                );
            }
            ResolvedCallTarget::Runtime(callee) => {
                return self.build_runtime_call_from_callee(
                    ctx, access_ctx, callee, arguments, expr.span,
                );
            }
        }
    }

    let callee = self.build_expression(...); // only non-path callees
    self.build_runtime_call_from_callee(...)
}
```

`build_path_expression` uses the same `resolve_value_path` once and then
`materialize_value_path`. There is no tuple-specific resolver and no fallback
walk.

This also makes future call-syntax-only items straightforward. A future tagged
variant constructor can become another `ResolvedCallTarget` classification
without gaining a fake runtime type or a second resolver.

## Generic arguments need one owner

Generic argument handling is currently divided among:

- bare turbofish functions in `build_path_expression`;
- struct/alias application in `resolve_generic_type_application`;
- first-segment application in multi-segment expression paths;
- inherited impl arguments in `ResolvedMember`;
- tuple-constructor padding in `build_call_expression`;
- final inference in ordinary and tuple calls.

This is why the new helper returns “type args as written”: it cannot promise
more because no layer owns the complete substitution.

Normalize arguments immediately after terminal resolution:

1. identify the generic owner and total slot count;
2. seed inherited receiver/impl slots;
3. apply written turbofish arguments to the owner's own slot range;
4. pad omitted inferable slots with `INFER` according to an explicit arity
   policy;
5. leave call-argument/result inference to the call builder;
6. validate bounds after inference using the existing mechanisms.

One helper can implement steps 1–4 for functions, associated functions,
struct constructors, and type applications. This eliminates the current
bare-versus-qualified drift while preserving the real difference between
`RequireExact` type position and `AllowInfer` call/initializer position.

## Designs not recommended

### Keep the tuple probe and deduplicate accesses

This masks only one symptom. Diagnostics, type-argument resolution, signature
forcing, and future side effects are still replayed. It also leaves the
bare-turbofish semantic gap and three-branch path builder intact.

### Add a “silent” or “record accesses” flag to low-level resolvers

Flags create two behavioral modes whose equivalence every helper must preserve.
They make speculative resolution easier to add, not harder. A resolver that
returns a complete result is the stronger contract.

### Add `Type::StructConstructor`

That puts a call-context affordance into the runtime/type representation.
Under WX semantics it cannot be stored, passed, or reach MIR, so downstream
type matches would be defending against an impossible value. The resolved-path
layer is the proper home for it.

### Synthesize a real function

This would be coherent only if WX chose Rust's first-class constructor
semantics. It would make `array.map(Point)` meaningful and require real
function identity, parameters, generics, visibility, and lowering. That is a
different language design from the one chosen here.

### Unify every path consumer behind one large mode enum

Type paths, bounds, imports, and value paths share mechanics but have different
terminal rules and, in the case of imports, different phase/forcing rules. A
shared prefix engine plus typed terminal adapters is easier to reason about
than a single function parameterized by many booleans or a growing
`PathPurpose` switch.

## Migration plan

### Phase 0: lock down behavior

Add characterization tests before moving code:

- bare, turbofish, and module-qualified ordinary function calls;
- type-associated function calls;
- local function-pointer calls;
- tuple constructors in bare, turbofish, and module-qualified forms;
- bare tuple-constructor use and `array.map(Point)` rejection;
- collision between a tuple struct and function in the value namespace;
- unknown/private/cyclic prefixes producing exactly one diagnostic;
- exact access counts for every qualifier, terminal, and type-argument span;
- LSP rename/reference ranges covering only the identifier segment;
- tuple-constructor visibility with private fields and through re-exports.

The exact-count tests are important. Tests that only assert an access exists
will not catch this regression.

### Phase 1: introduce the terminal IR

Add `ResolvedBinding`, `PathTarget`, `ResolvedPath`, and `PathError` in
`paths.rs` or a new `path_resolution.rs`. Do not change behavior yet. Wrap the
existing bare and multi-segment primitives to populate the new result.

Move `resolve_symbol_and_type_args` out of `modules.rs` and delete it once the
new value-path resolver is active. `modules.rs` should own module/scope lookup,
forcing, and privacy—not expression-oriented path orchestration.

### Phase 2: make ordinary value paths single-pass

Rewrite `build_path_expression` as:

```text
resolve_value_path -> commit accesses/report once -> materialize_value_path
```

The syntax-shape branches disappear. Keep the existing conversion functions as
temporary materialization helpers so this phase stays reviewable.

### Phase 3: make path callees consume the same result

Extract the post-callee portion of `build_call_expression` into
`build_runtime_call_from_callee`. For a path callee, resolve once and classify
the result. For a non-path callee, keep the ordinary recursive expression
build. Delete the probe/fallback block.

This phase fixes the repeated walk and the bare-turbofish tuple gap together.

### Phase 4: normalize generic application

Introduce the `GenericApplication`/substitution invariant and migrate free
functions, associated functions, then tuple constructors. Consolidate count
checking and padding. Keep argument inference separate because it consumes
expression types rather than path syntax.

### Phase 5: converge other semantic paths

Migrate `resolve_path_type`, bound paths, memory tags, grouped paths, and
qualified paths to the shared parent walker where their timing and semantics
match. Keep `use` prefix walking as a distinct phase-aware driver.

### Phase 6: centralize reference edges if desired

Once all path occurrences have a single commit point, replacing per-item
access vectors with a bidirectional reference index becomes mechanical rather
than speculative.

Each phase can compile and test independently. The tuple feature does not need
to wait for Phases 4–6; Phases 1–3 are the architectural fix required to land
it safely.

## External compiler precedent

Rust's language semantics are intentionally different: a tuple-struct
declaration defines a constructor in the value namespace, and that constructor
is a first-class function value. The [Rust Reference on structs](https://doc.rust-lang.org/reference/items/structs.html)
and [struct expressions](https://doc.rust-lang.org/reference/expressions/struct-expr.html)
make that explicit. WX should not copy this semantic choice after deciding that
`Point` is call-only.

Rust's *representation boundary* is still instructive. rustc resolves names to
a `Res` describing what definition was found rather than immediately turning
the result into a type or expression. Its `PartialRes` explicitly represents a
resolved module/type base plus the number of segments that remain
type-dependent. The official rustc source describes this as resolving module
segments while deferring associated-item segments to type checking:
[rustc `PartialRes`](https://doc.rust-lang.org/beta/nightly-rustc/src/rustc_hir/def.rs.html#622-655).
The [`rustc_resolve` crate documentation](https://doc.rust-lang.org/stable/nightly-rustc/rustc_resolve/index.html)
also states that type-relative method/field/associated-item resolution is
handled outside ordinary name resolution.

The lesson for WX is not to reproduce rustc's multi-pass compiler. It is to
preserve a semantic resolution result between lookup and context-specific
lowering. WX can fully resolve associated members in TIR because type
information is already available; it should still represent whether the
terminal came from a module binding or a type member rather than immediately
lowering both.

Rust's namespace model also confirms that namespace occupancy and item identity
are separate axes. The [Rust Reference on namespaces](https://doc.rust-lang.org/reference/names/namespaces.html)
lists constructors in the value namespace and types in the type namespace.
WX can use the same collision model while assigning a different capability to
the value binding: call-only construction instead of a first-class function.

## Invariants the refactor should establish

The finished design should make these statements true and testable:

1. One AST path occurrence invokes one semantic path driver.
2. Lookup/forcing may mutate caches, but it never commits the same source
   reference twice.
3. Every successful path has one exhaustive terminal kind; “not applicable” is
   not a success state.
4. A module namespace never appears in `Type` or `TypeIndex`.
5. A tuple constructor never appears as a runtime function type or expression.
6. Bare and turbofish paths differ only in generic application, not in name
   lookup.
7. Module-qualified and bare items share terminal interpretation.
8. Module terminals and type-associated terminals keep their distinct lookup
   algorithms but converge on one result protocol.
9. Diagnostics are reported at one defined boundary; an error result says what
   happened rather than merely whether somebody probably reported it.
10. Every access/reference range is the exact source segment that resolved.

## Final recommendation

Land the tuple constructor only after replacing the probe/fallback pattern with
a resolved-path terminal consumed by both path expressions and path callees.
The minimal mature slice is not large:

- one shared “resolve parent/prefix” function;
- one exhaustive `ResolvedPath`/`PathTarget` result;
- one value materializer;
- one call-target classifier;
- one access commit point;
- structured enough errors to prohibit fallback replay.

That slice removes the fourth walk, collapses the three expression-path
branches semantically, fixes `Pair::<i32>(...)`, and provides the right
extension point for future call-syntax-only declarations. It also completes
the architectural move begun by removing `Type::Namespace`: namespaces,
resolved declarations, types, and runtime values become four related but
distinct concepts instead of being converted into one another merely to fit an
existing function signature.

## Sources

1. WX compiler source: [`tir/builder/paths.rs`](../crates/wx-compiler/src/tir/builder/paths.rs),
   [`tir/builder/modules.rs`](../crates/wx-compiler/src/tir/builder/modules.rs),
   [`tir/builder/types.rs`](../crates/wx-compiler/src/tir/builder/types.rs),
   [`tir/builder/calls.rs`](../crates/wx-compiler/src/tir/builder/calls.rs),
   [`tir/builder/aggregates.rs`](../crates/wx-compiler/src/tir/builder/aggregates.rs),
   and [`tir/mod.rs`](../crates/wx-compiler/src/tir/mod.rs).
2. The Rust Project. [“Structs.” *The Rust Reference*](https://doc.rust-lang.org/reference/items/structs.html).
3. The Rust Project. [“Struct expressions.” *The Rust Reference*](https://doc.rust-lang.org/reference/expressions/struct-expr.html).
4. The Rust Project. [“Namespaces.” *The Rust Reference*](https://doc.rust-lang.org/reference/names/namespaces.html).
5. The Rust Project. [`PartialRes` source documentation](https://doc.rust-lang.org/beta/nightly-rustc/src/rustc_hir/def.rs.html#622-655).
6. The Rust Project. [`rustc_resolve` crate documentation](https://doc.rust-lang.org/stable/nightly-rustc/rustc_resolve/index.html).
