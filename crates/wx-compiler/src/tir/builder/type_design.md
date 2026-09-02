This separation is the right long-term direction, with one important refinement:

> These are not three different storage formats. They are different semantic states built around the same interned type-term graph.

The central mistake today is treating `TypeIndex` as if it always identifies a self-contained type. Sometimes it does; often it identifies a template whose meaning depends on substitutions, binders, and associated-type assumptions.

A good architecture would look like:

```text
                    read-only semantic operations
 TypeTermId + ParamEnv ──────────────────────────────┐
          │                                          │
          ├── whnf / relate / project / prove ───────┤
          │                                          │
          └── materialize ──> ClosedTypeId ──> MIR/codegen
                    mutates interner
```

## Refine the terminology

I would eventually rename the three concepts approximately as follows.

### 1. Interned type term

```rust
TypeTermId
```

This is what `TypeIndex` really is today: an index into an interned DAG of type terms.

A term may contain:

- `TypeParam`;
- `AssocTypeProjection`;
- `Infer`;
- generic struct arguments;
- function-owned variables;
- impl-owned variables;
- completely concrete types.

It is structurally canonical because the interner deduplicates equal `Type` values, but it is not necessarily semantically closed or normalized.

“Raw type syntax” is close, but “interned type term” is more accurate because aliases and parsed syntax have already been resolved by this stage.

### 2. Semantic type occurrence

```rust
Ty {
    term: TypeTermId,
    env: ParamEnvId,
}
```

This means:

> Interpret this particular interned term under this particular parameter environment.

Two occurrences with the same term can mean different things:

```text
(T,) under T = i32
(T,) under T = bool
```

Conversely, two occurrences with different terms can be equivalent:

```text
trait method generic A
impl method generic C

A ≡ C because both are binder position 0
```

All semantic operations should operate on `Ty`, not bare `TypeIndex`.

### 3. Closed/materialized type

```rust
ClosedTypeId
```

This is a proof-carrying wrapper around an interned term that no longer depends on an environment.

It should contain no:

- `TypeParam`;
- `AssocTypeProjection`;
- `Infer`;
- unresolved equality assumptions.

This is the output of applying an environment and fully resolving projections.

Not every closed type is necessarily ready for codegen. For example, `{integer}`, `Namespace`, or an error-recovery type may be environment-independent but still invalid in MIR. It may eventually be useful to distinguish:

```rust
ClosedTypeId   // no environment dependence
RuntimeTypeId  // valid for MIR/codegen
```

Do not overload “closed” to mean every downstream invariant.

## The foundational type model

A type term is roughly:

```text
τ ::=
    i32
  | bool
  | Tuple(τ...)
  | Struct(S, τ...)
  | Pointer(τ, memory, ownership)
  | Param(owner, index)
  | Projection(τ, trait, associated_name)
  | ...
```

`TypeTermId` identifies one such term.

The meaning of a term is a judgment:

```text
ParamEnv ⊢ TypeTermId ⇓ semantic type
```

A raw-index comparison answers only:

```text
Are these the same stored term?
```

It does not answer:

```text
Do these terms mean the same type in their respective environments?
```

That distinction should become explicit throughout the API.

## `ParamEnv` design

The environment should be owner-aware. A flat `&[TypeIndex]` is not sufficient because multiple owners can use parameter index zero.

Use a query-local arena:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ParamEnvId(u32);

struct ParamEnvArena {
    frames: Vec<ParamEnvFrame>,
}

enum ParamEnvFrame {
    Empty,

    Bind {
        owner: TypeParamOwner,

        // Function-owned parameter indices currently start after inherited
        // parameters, so a binding may cover a nonzero index range.
        first_index: u32,

        args: Box<[Ty]>,

        parent: ParamEnvId,
    },
}
```

Then:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Ty {
    term: TypeTermId,
    env: ParamEnvId,
}
```

There is no need for a special `Root` frame. Trait `Self` is just a normal owner binding:

```rust
env.bind(
    TypeParamOwner::Trait(trait_index),
    0,
    [self_ty],
)
```

A generic trait impl is another binding:

```rust
env.bind(
    TypeParamOwner::TraitImpl(impl_index),
    0,
    inferred_args,
)
```

A function’s own generics can be bound starting at its inherited offset:

```rust
env.bind(
    TypeParamOwner::Function(function_id),
    function.inherited_type_param_count as u32,
    own_args,
)
```

This immediately makes substitution owner-correct. The current positional substitution APIs often inspect `param_index` while ignoring `owner`, which only works because call sites carefully construct flattened argument arrays.

## Query-local rigid variables

Method signature comparison needs alpha-equivalence, but rigid variables should not be interned globally merely for comparison.

Extend the semantic type representation:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Ty {
    Interned {
        term: TypeTermId,
        env: ParamEnvId,
    },

    Rigid(RigidTy),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct RigidTy {
    binder: BinderId,
    index: u32,
}
```

For conformance comparison, corresponding method parameters can map to a shared canonical binder:

```text
trait function A -> Rigid(comparison_binder, 0)
impl function C  -> Rigid(comparison_binder, 0)
```

Then alpha-equivalence is ordinary semantic equality.

Alternatively, retain distinct binders and let the relation know the binder correspondence. Shared canonical variables are generally simpler for a one-off comparison context.

Rigid variables cannot be materialized into a `ClosedTypeId`; that correctly reports that a declaration-level type is still open.

## The semantic evaluator

Introduce a central context:

```rust
struct TypeEvalCx<'a> {
    types: &'a TypeInterner,
    items: &'a ItemRegistry,
    envs: ParamEnvArena,

    active_projections: Vec<ProjectionKey>,

    // Optional, query-local caches.
    whnf_cache: HashMap<Ty, NormalizeResult>,
}
```

Its core operations should be small and composable.

### Weak-head normalization

```rust
fn whnf(&mut self, ty: Ty) -> Result<Ty, NormalizeError>;
```

`whnf` only resolves enough to discover the outer constructor.

It repeatedly handles:

- environment-bound `TypeParam`;
- query-local rigid variables;
- associated projections;
- `Error` and `Infer`.

It does not recursively rebuild every tuple/struct child.

For a tuple, it returns the tuple term under its environment:

```text
Tuple<T> under T=i32
```

The relation will interpret each child under that same environment when it reaches it.

This preserves lazy traversal and early mismatch exit.

### Projection resolution

```rust
fn project(
    &mut self,
    base: Ty,
    trait_index: TraitIndex,
    assoc_name: SymbolU32,
) -> Result<Ty, ProjectionError>;
```

The steps should be centralized:

1. Normalize the base to weak-head form.
2. If the base remains abstract, inspect declared equality assumptions.
3. Otherwise locate the applicable trait impl.
4. Infer the impl’s semantic arguments.
5. Add an owner binding for that impl.
6. Return the raw associated-type value under the new environment.

Conceptually:

```rust
let impl_args: Box<[Ty]> =
    self.infer_impl_args(impl_index, base)?;

let impl_env = self.envs.bind(
    TypeParamOwner::TraitImpl(impl_index),
    0,
    impl_args,
    base.env(),
);

Ok(Ty::Interned {
    term: raw_assoc_type_value,
    env: impl_env,
})
```

This is the operation currently duplicated across `substitute_type`, the comparator, path resolution, bound checking, and MIR lowering.

### Type relation

```rust
fn relate(
    &mut self,
    expected: Ty,
    found: Ty,
    relation: RelationKind,
    path: &mut TypePath,
) -> RelationResult;
```

Possible relation kinds:

```rust
enum RelationKind {
    Equal,
    Coercible,
    PatternMatches,
}
```

Initially, implement only equality for conformance. The common normalization machinery can later support other relations without conflating their semantics.

The equality algorithm becomes:

```rust
let expected = self.whnf(expected)?;
let found = self.whnf(found)?;

if expected == found {
    return Equivalent;
}

match (self.head(expected), self.head(found)) {
    (Rigid(a), Rigid(b)) if a == b => Equivalent,

    (Tuple(a), Tuple(b)) => relate children,

    (Struct(sa, aa), Struct(sb, ab))
        if sa == sb => relate arguments,

    ...

    _ => Different,
}
```

Both sides are treated symmetrically. There is no `expected` normalizer versus `found` reducer.

## Environment-aware impl matching

This is essential for completing the architecture.

Today [`find_trait_impl`](/home/melkam/wx/crates/wx-compiler/src/tir/mod.rs:3930) accepts a raw `TypeIndex`, and `infer_type_args` compares raw child indexes. It cannot correctly understand:

```text
Wrapper<T> under T=i32
```

as equivalent to:

```text
Wrapper<i32>
```

The semantic version should accept `Ty`:

```rust
fn find_trait_impl(
    &mut self,
    receiver: Ty,
    trait_index: TraitIndex,
) -> Result<TraitImplMatch, TraitSelectionError>;

struct TraitImplMatch {
    impl_index: TraitImplIndex,
    args: Box<[Ty]>,
}
```

The outer dispatch lookup remains cheap:

1. Normalize the receiver’s head.
2. Read its outer constructor from the interned term.
3. Use the existing dispatch table.
4. Semantically unify the candidate pattern with the receiver.

Semantic unification should operate on two `Ty` values:

```rust
fn infer_type_args(
    &mut self,
    inferred: &mut [Option<Ty>],
    pattern: Ty,
    actual: Ty,
) -> Result<(), TypeMismatch>;
```

Every recursive child carries its own environment.

This removes the existing raw-index repeated-binding limitation and makes trait lookup usable consistently by:

- projection normalization;
- generic dispatch;
- bound checking;
- conformance comparison;
- MIR monomorphization.

## Declared bounds and assumptions

Bounds should also become semantic occurrences.

A stored equality binding currently contains a raw `TypeIndex`:

```text
T: Container where { Item = U }
```

The stored `U` term belongs to some owner/binder. When used under an environment, the semantic equality value is:

```rust
Ty {
    term: stored_u_term,
    env: current_env,
}
```

A future API could return:

```rust
struct InstantiatedTraitBound {
    trait_index: TraitIndex,
    self_ty: Ty,
    bindings: Box<[(SymbolU32, InstantiatedBinding)]>,
}

enum InstantiatedBinding {
    Equals(Ty),
    Bound(InstantiatedBounds),
}
```

It need not allocate eagerly. An iterator/view is sufficient.

This is important because bounds are not metadata independent of substitution. A bound’s RHS may itself reference:

- another parameter;
- `Self`;
- another associated projection;
- an impl-owned parameter.

## Materialization

Materialization is the explicit boundary where mutation is allowed:

```rust
fn materialize(
    &mut self,
    ty: Ty,
    interner: &mut TypeInterner,
) -> Result<ClosedTypeId, MaterializeError>;
```

It should:

1. Normalize the head.
2. Reject unresolved rigid variables.
3. Reject missing/ambiguous projections.
4. Recursively materialize child types.
5. Intern changed composite nodes.
6. Return a proof wrapper.

Conceptually:

```rust
match self.head(self.whnf(ty)?) {
    Primitive(id) => ClosedTypeId::new_checked(id),

    Tuple(elements, env) => {
        let elements = elements
            .iter()
            .map(|term| {
                self.materialize(
                    Ty::interned(*term, env),
                    interner,
                )
            })
            .collect::<Result<Box<_>, _>>()?;

        let id = interner.intern(Type::Tuple {
            elements: elements
                .iter()
                .map(|ty| ty.raw())
                .collect(),
        });

        Ok(ClosedTypeId(id))
    }

    Rigid(_) => Err(MaterializeError::OpenType),

    ...
}
```

This becomes the principled replacement for `substitute_type`.

The crucial API difference is that materialization takes an explicit environment rather than a positional slice:

```rust
// Current
substitute_type(template, args)

// Future
materialize(Ty::new(template, env))
```

## What “closed” should guarantee

Add cached flags to each interned type term.

```rust
bitflags! {
    struct TypeFlags: u16 {
        const HAS_TYPE_PARAM  = 1 << 0;
        const HAS_PROJECTION  = 1 << 1;
        const HAS_INFER       = 1 << 2;
        const HAS_ERROR       = 1 << 3;
        const HAS_COMPTIME    = 1 << 4;
        const HAS_NAMESPACE   = 1 << 5;
        const HAS_ABSTRACT_ASSOC = 1 << 6;
    }
}
```

For a composite term, flags are the union of its children plus its own kind.

The interner can store:

```rust
struct InternedType {
    kind: Type,
    flags: TypeFlags,
}
```

Or maintain a parallel flags vector if changing `entries: Vec<Type>` would be disruptive.

Then:

```rust
impl TypeInterner {
    fn flags(&self, id: TypeTermId) -> TypeFlags;

    fn depends_on_env(&self, id: TypeTermId) -> bool {
        self.flags(id).intersects(
            TypeFlags::HAS_TYPE_PARAM
                | TypeFlags::HAS_PROJECTION
        )
    }

    fn is_closed(&self, id: TypeTermId) -> bool {
        !self.flags(id).intersects(
            TypeFlags::HAS_TYPE_PARAM
                | TypeFlags::HAS_PROJECTION
                | TypeFlags::HAS_INFER
                | TypeFlags::HAS_ERROR
        )
    }
}
```

This is better than a hand-maintained `is_frame_inert` match. It answers the recursive property that actually matters:

> Can anything anywhere in this term be reinterpreted by an environment?

It also allows a safe fast path:

```rust
if expected.term == found.term
    && (expected.env == found.env
        || !types.depends_on_env(expected.term))
{
    return Equivalent;
}
```

## Proof-carrying wrappers

Introduce wrappers gradually:

```rust
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ClosedTypeId(TypeIndex);

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct RuntimeTypeId(ClosedTypeId);
```

Construction should be private:

```rust
impl ClosedTypeId {
    fn try_new(
        types: &TypeInterner,
        id: TypeIndex,
    ) -> Result<Self, NotClosed> {
        types.is_closed(id).then_some(Self(id)).ok_or(NotClosed)
    }

    fn raw(self) -> TypeIndex {
        self.0
    }
}
```

`RuntimeTypeId` can enforce additional MIR requirements:

- not `Error`;
- not `Infer`;
- not `{integer}` or `{float}`;
- not `Namespace`;
- not an abstract associated-type placeholder;
- whatever else `lower_type_index` currently treats as unreachable.

This turns existing MIR `unreachable!()` assumptions into checked boundary conditions.

## Query-local values must not escape

`ParamEnvId` only has meaning inside its `TypeEvalCx`. A `Ty` must therefore never be stored in TIR or MIR.

Good boundaries:

- TIR declarations store `TypeTermId`.
- Semantic queries create `Ty`.
- Successful materialization returns `ClosedTypeId`.
- Diagnostics render semantic types before destroying the evaluator.

The last point affects the comparator. `TypeDifference` currently stores raw indexes and formats them afterward. A semantic mismatch may involve environment-dependent values that cannot escape with query-local `ParamEnvId`s.

On the error path, format them immediately:

```rust
struct TypeDifference {
    path: Vec<TypePathElement>,
    expected: String,
    found: String,
    kind: TypeDifferenceKind,
}
```

String allocation is fine when already producing a diagnostic.

Alternatively, have comparison and reporting occur within the same evaluator lifetime. Storing rendered strings is simpler.

## Formatting semantic types

Add:

```rust
fn display_semantic_type(
    &mut self,
    ty: Ty,
    formatter: &TypeFormatter,
) -> Result<String, fmt::Error>;
```

It should normalize lazily while formatting, without materializing into the interner.

That gives correct diagnostics for:

```text
(T,) under T=i32
```

which should print `(i32,)`, not `(T,)`.

This semantic formatter would also benefit hover/type-display features in generic contexts.

## How this applies to MIR

MIR currently has its own implicit environment:

```rust
current_substitutions: Box<[TypeIndex]>
```

and repeatedly swaps that slice when descending into another owner’s scheme. It also commonly indexes by `param_index` without checking `TypeParamOwner`.

That is the same missing abstraction as the comparator.

Long term, MIR lowering should use:

```rust
struct MirTypeContext {
    eval: TypeEvalCx,
    current_env: ParamEnvId,
}
```

When monomorphizing a function:

```rust
let function_env = envs.bind(
    TypeParamOwner::Function(function_id),
    function.inherited_type_param_count as u32,
    own_args,
    parent_env,
);
```

When resolving an associated type from a generic impl, projection resolution creates the impl-owned child environment automatically. No save/replace/restore of one global positional substitution slice is needed.

MIR lowering can then require:

```rust
fn lower_type(&mut self, ty: Ty) -> mir::Type;
```

or, more strictly:

```rust
fn lower_type(&mut self, ty: RuntimeTypeId) -> mir::Type;
```

A useful intermediate step is:

```rust
let closed = evaluator.materialize(ty, interner)?;
let runtime = RuntimeTypeId::try_from(closed)?;
lower_runtime_type(runtime)
```

## Persistent generic arguments should name their owner

Current TIR nodes often store:

```rust
type_args: Box<[TypeIndex]>
```

The implied target owner lives only in comments and surrounding control flow.

Make it explicit:

```rust
struct GenericArgs {
    owner: TypeParamOwner,
    first_index: u32,
    args: Box<[TypeTermId]>,
}
```

For a generic call inside another generic function, those arguments are still raw terms under the caller’s binder. At evaluation time:

1. Interpret each stored argument under the caller environment.
2. Bind the resulting `Ty` values to the callee owner.
3. Evaluate the callee signature/body under the resulting environment.

This makes substitution composition explicit and owner-safe.

## Recommended module layout

A reasonable eventual split:

```text
tir/
    types/
        term.rs          Type, TypeTermId, TypeInterner, TypeFlags
        env.rs           ParamEnvArena, ParamEnvId, Ty, rigid variables
        normalize.rs     whnf, projection resolution, cycle handling
        relate.rs        equality, coercion, pattern matching
        materialize.rs   Ty -> ClosedTypeId
        traits.rs        semantic trait selection / impl inference
        format.rs        raw and semantic formatting
```

It does not need to start this granular. Initially:

```text
tir/type_eval.rs
```

can contain the evaluator used only by the comparator. Split it once a second real consumer arrives.

## Staged migration

### Phase 1: establish terminology and flags

- Document `TypeIndex` as an interned type term, not necessarily a closed type.
- Add recursive `TypeFlags`.
- Replace `is_frame_inert` logic with `depends_on_env`.
- Add debug assertions around boundaries expected to receive closed types.

This is low-risk and immediately useful.

### Phase 2: introduce query-local `Ty + ParamEnv`

Use it only inside the comparator:

- owned environment arena;
- symmetric weak-head normalization;
- semantic equality;
- typed normalization failures;
- immediate semantic formatting of mismatches.

Delete the borrowed `Frame`, `Pending`, and asymmetric reducers.

This proves the abstraction against the hardest current test cases.

### Phase 3: semantic impl selection

Add environment-aware variants of:

- `infer_type_args`;
- `find_trait_impl`;
- `type_args_satisfy_bounds`;
- projection resolution.

Run the old and new lookup implementations in debug/test builds and assert identical results for closed receivers.

### Phase 4: explicit materialization

Implement:

```rust
materialize(Ty) -> Result<ClosedTypeId, _>
```

Keep `substitute_type` temporarily as a wrapper that constructs an environment and calls materialization.

Change call sites incrementally to supply an explicit owner.

Differential-test the new materializer against `substitute_type` for fully concrete inputs.

### Phase 5: move associated-type bound checking

Rewrite `check_assoc_type_bounds` using semantic projections and instantiated assumptions. This should also solve the currently ignored abstract-projection bound test.

At this point, the evaluator has proven itself with at least two independent consumers.

### Phase 6: migrate MIR monomorphization

Replace `current_substitutions` with `current_env`.

Require closed/runtime wrappers at the TIR-to-MIR boundary.

Turn `lower_type_index`’s impossible arms into a single checked conversion failure before lowering.

### Phase 7: clean up the representation

Only after the APIs have migrated:

- rename `TypeIndex` to `TypeTermId` or `InternedTypeId`;
- rename `substitute_type` to `materialize`/`instantiate`;
- remove positional substitution helpers;
- consolidate projection resolution;
- consider canonical binder/de Bruijn representation if still valuable.

Renaming first would create a large mechanical diff without improving semantics.

## Important invariants

Write these down as module-level documentation and debug assertions:

1. `TypeTermId` equality means structural term identity only.
2. `Ty` equality means term identity plus environment identity.
3. Semantic type equality is decided only by `relate`.
4. A `ParamEnvId` never outlives its evaluator.
5. Environment bindings are keyed by exact owner and index range.
6. Projection resolution always returns a `Ty`, never a naked associated-type term.
7. `materialize` is the only operation that converts an environment-dependent `Ty` into a global interned closed type.
8. Relation/proving operations never mutate the global type interner.
9. `ClosedTypeId` contains no environment-dependent or unresolved terms.
10. MIR/codegen accepts only types validated for runtime lowering.

## Tests and properties

Beyond individual regression tests, add properties:

- Materialization is idempotent:

```text
materialize(closed under empty env) = closed
```

- Semantic equality agrees with materialization for closed results:

```text
relate(a, b) = Equivalent
⇒ materialize(a) == materialize(b)
```

- Owner isolation:

```text
FunctionA::param0 and FunctionB::param0 do not substitute each other
unless explicitly canonicalized for alpha-equivalence.
```

- Substitution composition:

```text
materialize(term under env A extended with env B)
=
materialize(materialize-under-A term under B)
```

where both sides are defined.

- Relation does not grow the interner.
- Every `ClosedTypeId` passes a recursive closedness scan.
- Cached `TypeFlags` agree with a slow recursive test implementation.
- Semantic impl lookup agrees with existing lookup for environment-free receivers.
- Recursive same-impl projection resolution respects the nearest owner binding.
- Normalization cycles return `Cycle`, never recurse indefinitely.
- A successful conformance comparison never returns `Indeterminate`.

## The main architectural payoff

This is bigger than cleaning up `type_compare.rs`.

The same abstraction removes or consolidates:

- borrowed comparison frames;
- positional `substitute_type` assumptions;
- MIR’s `current_substitutions` swapping;
- duplicated associated-projection resolution;
- raw-index impl unification;
- several abstract-type bound false positives;
- unsafe equality fast paths;
- many “this associated type belongs to a different parameter scheme” comments.

The durable model is:

```text
TypeTermId
    is persistent syntax/template identity.

Ty = TypeTermId + ParamEnv
    is what semantic algorithms consume.

ClosedTypeId
    is what materialization produces and downstream phases may store.
```

That separation gives each layer one honest meaning and makes accidental raw-index equality much harder to write.