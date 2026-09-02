# Performance review: `type_compare.rs`

Scope: the trait-conformance signature/const-type comparator added in
`crates/wx-compiler/src/tir/builder/type_compare.rs` and its wiring into
`check_trait_conformance` (`traits.rs`). Review only — nothing here has been
fixed yet.

## Where this runs, and how often

`check_trait_conformance` iterates *every* `TraitImpl` in the whole
compilation graph — every package, including the embedded stdlib
(`std/main.wx`), on every single compile. There is no incremental/caching
layer yet (consistent with the rest of the compiler), so stdlib's own trait
impls (`Memory`, and whatever else grows to implement a trait) go through the
full comparator every run even though they never change. This isn't a
`type_compare.rs`-specific problem, but it's the multiplier on top of
everything below, and it's the first thing that would stop being true once
crate-scoped incremental compilation exists — conformance checking is exactly
the kind of pure, input-only-dependent pass that becomes trivially skippable
once there's somewhere to cache the result.

For each `TraitImpl`, for each trait item with a matching impl entry
(`Method`/`AssocFunction`/`AssocConstant` pair), one `compare_method_signature`
or `compare_assoc_const_type` call runs. Cost per call is dominated by how
deep/generic the compared types are, not by anything fixed.

## Allocations

### The one worth fixing first: cloning argument slices in `compare_structural`

Every structural arm that recurses into multiple children first clones the
`Box<[TypeIndex]>` (or copies a `Vec` from `&[TypeIndex]`) it's about to
iterate, *before* the loop:

- `Type::Tuple` (line 654): `let (e, f) = (e.clone(), f.clone());`
- `Type::Struct` (line 768): `let (ea, fa) = (ea.clone(), fa.clone());`
- `Type::Function` (line 788): `let (eparams, fparams) = (es.params().to_vec(), fs.params().to_vec());`
- `Type::FunctionItem` (line 816): `let (ea, fa) = (ea.clone(), fa.clone());`

Each of these is a heap allocation, and it happens on *every* structural
comparison of a tuple/generic-struct/function-pointer/function-item type —
regardless of whether the two sides turn out equal or different, since the
loop has to run either way to find out.

This mirrors a pattern already present in `substitute_type` (`generics.rs`),
which clones the same way before recursing — but `substitute_type` is
`&mut self` (it interns), so it genuinely has to drop the borrow on
`self.types` before making a mutating recursive call. `compare_types` is
`&self`-only throughout. Multiple shared (`&self`) borrows are allowed to
coexist in Rust, so as far as I can tell these clones aren't forced by the
borrow checker here the way they are in `substitute_type` — they look like
they were carried over by habit/pattern-matching the existing code shape
rather than by necessity. I haven't actually tried removing them and
rebuilding to confirm the borrow checker accepts it, so this is a hypothesis
to verify, not a confirmed diagnosis — but if it holds, this is a set of
avoidable heap allocations on exactly the kind of comparison this whole
feature was built to keep allocation-free (the stated goal from the start of
this work was "don't let comparison intern/allocate as a byproduct," and
these clones are a smaller instance of the same category of problem, even
though they don't touch `TypeInterner`).

Scale: at wx's current size this is very unlikely to be *measurable* — the
number of trait impls with tuple/struct/fn-pointer-shaped signatures is
small. It's flagged because it's cheap to fix and because it's the one place
this module doesn't fully live up to its own stated design principle, not
because it's an observed hot path.

### Everything else allocation-wise is either bounded-and-small or cold-path

- `path: &mut Vec<TypePathElement>` — `Vec::new()` doesn't allocate until the
  first `push`, and the common case (`i32` vs `i32`, or any pair of types
  that are flatly equal) hits the `expected.index == found.index` fast path
  before ever touching `path`. So the per-parameter `&mut Vec::new()` in
  `compare_method_signature`'s loop is free in the case that matters most.
- `path.to_vec()` inside `different()`/the `mismatch()` closure — only
  happens once per comparison that actually finds a difference (the
  `recurse!` macro returns immediately on the first non-`Equivalent` result),
  and is bounded by nesting depth. Not a concern.
- `describe_path`/`describe_type_difference`/`TypeFormatter::display_type`
  (String-building, `Vec<String>` + `.join`) — only ever run when building a
  diagnostic to report, i.e. strictly on the path where compilation is
  already failing. Not worth optimizing.
- `Frame`/`TypeRef` themselves — stack-allocated, borrowed, no heap
  allocation at all. This part of the design does what it set out to do.

## `find_trait_impl` cost (pre-existing, but newly invoked from here)

Every associated-type projection the comparator has to resolve
(`compare_projection`'s step 3) calls the existing `ItemRegistry::find_trait_impl`,
which — for a generic impl — allocates a `Vec<TypeIndex>` sized to the impl's
own type-param count (`vec![TypeIndex::INFER; type_params_len]` inside
`unify_impl_target`), fills it via `infer_type_args`, then converts it to a
`Box<[TypeIndex]>`. That's one or two small heap allocations per resolved
projection. This machinery isn't new — it's reused as-is — but this feature
is a genuinely new, additional call site for it: previously `find_trait_impl`
only ran during Phase 2/3 resolution and a handful of bound checks; now it
also runs once per associated-type projection appearing in *any* compared
trait-item signature, every conformance check, every compile. Bound checking
inside `unify_trait_impl_target` (`type_args_satisfy_bounds`) can itself
recurse into further `find_trait_impl`/`concrete_type_in_typeset` calls for
each of the impl's own bounded type params, so cost scales with how generic
the impl being checked is, not just with signature size.

`resolve_projection_via_bound` (the "check a declared equality binding
first" step, step 2) is cheap when it doesn't apply — `abstract_type_bounds`
short-circuits to `None` in one match arm for any concrete receiver (`_ =>
None`), which is the common case once a projection's base has already been
resolved down to something concrete. It's only expensive (and, per its own
existing doc comment in `paths.rs`, a "real recursive scan, not a cheap field
read") when the base is still abstract with its own chain of bounds to walk
— and in that case there's some overlap with the bound-walking
`find_trait_impl`'s own bound check does if step 2 fails and step 3 runs
next. Not unbounded, just not perfectly non-redundant across the two
fallback layers.

## Redundant `self.types.resolve()` calls

`compare_types`'s entry checks `Type::Error | Type::Infer` by calling
`self.types.resolve()` on both operands, then the main `match` immediately
calls `self.types.resolve(expected.index)` again. `resolve` is an O(1) `Vec`
index (no allocation, no hashing), so this is a handful of redundant array
reads per node visited — negligible on its own, just noted for completeness
since it's an easy, free cleanup if the function is being touched anyway.

## Recursion depth

`compare_types`/`compare_projection`/`peel_top`/`Frame::resolve` all recurse
with call-stack depth proportional to how deeply the compared types (and any
chained associated-type projections) are nested. For realistic wx code this
is single digits. There's no cycle risk (established separately — see the
ignored `CyclicTypeDependency` regression test), but there's also no depth
guard: a deliberately, pathologically deep generic nesting in a single
signature (`Wrap<Wrap<Wrap<...>>>` some large number of levels) has nothing
stopping it from recursing until the stack overflows. This is a robustness
edge case, not a normal-case performance concern, and matches the same
"finite but unbounded" character of `substitute_type`'s own existing
recursion — not a new risk this module introduces, just one it inherits.

`Frame::resolve` additionally walks its `parent` chain linearly per lookup;
for a projection chain of depth *N* (N nested nested generic impls), a
lookup near the bottom of the chain is O(N). Since a `TypeParam`/projection
node is resolved once per visit, a single comparison with N levels of
chained substitution is O(N²) in the pathological case. Same caveat as
above: N is realistically small for wx code today, so this is a
completeness note, not an observed problem.

## Overall

Ranked by where cycles are most likely actually going: (1) `find_trait_impl`'s
own allocations, multiplied by how many projections appear across every
checked signature, every compile — inherited cost, newly exercised more
often; (2) the `compare_structural` argument-slice clones — small per call,
possibly unnecessary outright, cheapest to fix; (3) re-checking the entire
graph including stdlib on every compile with no caching — a roadmap-level
concern, not a bug in this file; (4) everything else (redundant `resolve()`
calls, diagnostic-building allocations, frame-chain walks) is either
negligible at realistic scale or strictly on the cold/error path.

Nothing here reads as an actual regression against the pre-conformance-check
baseline — the comparator was correctly built read-only with respect to
`TypeInterner`, which was the goal that mattered most. The findings above are
about tightening allocation behavior further and about where the *next*
architectural lever (incremental compilation) would pay off, not about
anything currently broken.
