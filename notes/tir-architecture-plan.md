# TIR Architecture Redesign: Splitting Storage by Mutation Profile

## The problem

`check_trait_conformance` needs to do two things at once for each trait impl:

1. **Read** `traits`/`trait_impls`/`functions`/... to compare the impl against its trait.
2. **Write** into the type pool (`substitute_type` may intern a brand-new `Type`) and push diagnostics.

Both of these currently live behind `&mut self.tir` (or `&mut self`). Rust's borrow
checker won't let you hold a read-only iterator over part of a struct while calling a
method that needs `&mut` on the *same* struct — even if the two halves never actually
touch the same field. That's the E0502 you're hitting, and no amount of `unsafe`-free
cleverness at the call site fixes it, because the *types* don't say the two halves are
independent.

The fix is to make that independence a fact about the types, not a fact you have to
re-prove (or hack around with index-range loops) every time you write a new pass.

## The core idea: group fields by how they're mutated, not by what they mean

Right now `TIR` groups fields by *topic* (all compiler output in one struct). Instead,
group them by **mutation profile** — how and when each piece of data grows:

| Profile                              | Examples                                        | Behavior                                                               |
| ------------------------------------ | ----------------------------------------------- | ---------------------------------------------------------------------- |
| **Frozen by check-time**             | `traits`, `trait_impls`, `functions`, `structs` | Fully built by earlier phases; only *read* during conformance checking |
| **Actively growing during checking** | `types` (via `substitute_type`)                 | New entries minted *while* you're reading the frozen data above        |
| **Write-only, read at the end**      | `diagnostics`                                   | Never read back mid-pass; no aliasing hazard at all                    |

Once these are separate types, a checking pass can hold `&TraitData` and `&mut
TypeInterner` at the same time — the borrow checker sees two distinct types, not two
fields of one struct it has to reason about specially.

## A second, related problem: storage split from its own index

Separately, some data has a **derived index** — a `HashMap` that exists purely to
answer "given a key, which slot in this `Vec` holds it." Example: `TIR::types: Vec<Type>`
paired with `Builder::type_index_lookup: HashMap<Type, TypeIndex>`. Inserting a type is
really *two* writes (push to the `Vec`, insert into the map) that must never go out of
sync — but today they live in different structs, so anything that wants to insert a type
needs `&mut` access to both places at once. Same pattern shows up for:

- `item_lookup: HashMap<DefId, ItemIndex>` — shared index over every item `Vec`
- `inherent_impl_dispatch` — derived from `inherent_impls`
- `trait_impl_dispatch` — derived from `trait_impls`

**Fix:** bundle each `Vec` with everything derived from it into one type, with typed
`push_*` methods as the *only* way to insert. From outside, it behaves as one
indivisible resource instead of two-or-three fields that happen to need updating
together by convention.

```rust
impl ItemRegistry {
    pub fn push_trait_impl(&mut self, def_id: DefId, target: ImplTarget,
                            trait_index: TraitIndex, imp: TraitImpl) -> TraitImplIndex {
        let idx = TraitImplIndex::from(self.trait_impls.len());
        self.trait_impls.push(imp);
        self.item_lookup.insert(def_id, ItemIndex::TraitImpl(idx));
        self.trait_impl_dispatch.entry(target).or_default().push((trait_index, idx));
        idx
    }
}
```

Now inserting a trait impl is *atomically* one call — it's impossible to update the
`Vec` without also updating its indexes, because there's no other way in.

## The resulting shape

```rust
/// Everything read during conformance checking (and most other passes):
/// item data plus every index derived from it. Frozen by the time checking runs.
pub struct ItemRegistry {
    pub functions: Vec<Function>,
    pub structs: Vec<Struct>,
    pub traits: Vec<Trait>,
    pub trait_impls: Vec<TraitImpl>,
    // ... every other item Vec

    item_lookup: HashMap<DefId, ItemIndex>,               // derived
    inherent_impl_dispatch: HashMap<(ImplTarget, SymbolU32), Vec<InherentImplIndex>>, // derived
    trait_impl_dispatch: HashMap<ImplTarget, Vec<(TraitIndex, TraitImplIndex)>>,      // derived
}

/// Owns type storage AND its lookup map — no more splitting these across
/// Builder and TIR. Grows during checking, so it's kept separate from
/// ItemRegistry on purpose.
pub struct TypeInterner {
    types: Vec<Type>,
    index_lookup: HashMap<Type, TypeIndex>,
}

/// Scope/namespace data — a different question ("where is X visible") than
/// item storage ("what is X"), so kept as its own type.
pub struct ModuleGraph {
    pub namespaces: Vec<ModuleNamespace>,
    pub package_namespaces: HashMap<PackageId, NamespaceIndex>,
    pub file_namespaces: Vec<NamespaceIndex>,
}

pub struct TIR {
    pub diagnostics: Vec<Diagnostic<FileId>>,   // write-only, no hazard, stays a plain Vec
    pub items: ItemRegistry,
    pub modules: ModuleGraph,
    pub export_block: Option<ExportBlock>,
    pub tagged_items: HashMap<SymbolU32, DefId>,
}
```

## What this buys you at the call site

A checking pass now only needs to borrow the pieces it actually uses — and those
pieces are guaranteed disjoint *by type*, not by careful field-by-field reasoning:

```rust
struct ConformanceCx<'a> {
    items: &'a ItemRegistry,          // one shared borrow covers traits,
                                       // trait_impls, functions, constants, ...
    types: &'a mut TypeInterner,      // free to grow via substitute_type
    diagnostics: &'a mut Vec<Diagnostic<FileId>>,
}
```

Inside `ConformanceCx`, you can freely do:

```rust
for trait_impl in self.items.trait_impls.iter() {
    // ... compare against trait_def ...
    let substituted = self.types.intern(new_ty);   // grows TypeInterner
    self.diagnostics.push(diagnostic);              // grows diagnostics
}
```

No `RefCell`, no runtime borrow checks, no index-range workaround — the compiler
proves this is safe once, at the point `ConformanceCx` is constructed, because
`ItemRegistry`, `TypeInterner`, and `Vec<Diagnostic>` are separate types with no
overlapping fields.

## Why not other fixes

- **`RefCell<Vec<_>>` around `types`/`diagnostics`** — works, but turns a static
  guarantee into a runtime one (panics if ever misused), and doesn't fix the deeper
  "storage split from its index" problem.
- **Clone the `Vec` before iterating** — avoids the borrow conflict but pays a real
  allocation/copy cost every check run, and doesn't scale as a general pattern.
- **One `DispatchIndex<T>` type per dispatch map, separate from item storage** —
  tempting, but re-creates the exact problem being solved: a single logical insert
  (e.g. "add a trait impl") would need two separate `&mut` calls to two separate
  types, which is the two-writes-that-must-stay-in-sync hazard all over again, just
  moved one level down.

## Summary

1. **Group by mutation profile**, not by topic: frozen item data, actively-growing
   type pool, and write-only diagnostics become three separate types.
2. **Bundle every `Vec` with everything derived from it** (lookup maps, dispatch
   indexes) behind typed `push_*` methods, so partial/out-of-sync updates are
   impossible by construction.
3. The payoff: any future pass that needs to read frozen data while writing to the
   type pool or diagnostics just borrows the relevant pieces — the fix generalizes
   to every pass you write from here on, not just this one function.

## What actually changed from the initial plan

The broad split-by-mutation-profile idea stayed the same, but the concrete safety
mechanism evolved in a more important way: we ended up making the index types
strong, not just the storage layout.

The original write-up focused on `ItemRegistry`, `TypeInterner`, and
`ModuleGraph` as the primary separation. That was correct, but we later tightened
it with a stricter rule:

- every TIR index is a distinct newtype (`FunctionIndex`, `TraitIndex`,
  `ConstIndex`, `NamespaceIndex`, ...)
- only `ItemRegistry`/the registry layer is allowed to create these indexes
- there is no public arbitrary constructor for an index from a raw `u32`
- conversion is explicit at the boundary, never hidden behind convenience helpers

That makes the intended invariant concrete:

```rust
index_newtype!(FunctionIndex);
index_newtype!(TraitIndex);
index_newtype!(NamespaceIndex);

// generated shape (conceptually)
struct FunctionIndex(u32);

impl From<FunctionIndex> for usize {
    fn from(value: FunctionIndex) -> Self { value.0 as usize }
}

impl From<FunctionIndex> for u32 {
    fn from(value: FunctionIndex) -> Self { value.0 }
}
```

The important rule we agreed on is: no `as_u32()`, no `as_usize()`, and no
helper functions that hide the conversion. Call sites must say exactly what they
mean:

```rust
let func = &self.tir.functions[usize::from(func_index)];
let scope = u32::from(scope_index);
```

This is the actual decision that differs from the earlier, more abstract plan. The
storage split solves aliasing; the strong index types make accidental mixing
impossible.

## The concrete design we settled on

The plan is now:

1. keep the mutation-profile split (`ItemRegistry` / `TypeInterner` /
   `ModuleGraph` / write-only diagnostics)
2. keep the atomic `push_*` pattern so lookups and dispatch maps are updated in
   the same operation
3. enforce safety with type-safe index wrappers and explicit conversion sites
4. do not carry the conversion logic in helper methods or implicit casts
5. keep MIR intentionally simple and raw-`u32`-based at its own boundary, while
   TIR remains strongly typed with those newtypes

The practical example is the TIR→MIR boundary:

```rust
// TIR side: strong index
let func_index = self.tir.expect_function_index(id);
let func = &self.tir.functions[usize::from(func_index)];

// MIR side: raw u32 index is fine here
let fn_idx: u32 = u32::from(func_index);
```

This is a deliberate boundary rule: the lower layer is allowed to flatten to a
primitive index, but the higher layer must not silently lose type safety by
writing `as usize`/`as u32` everywhere.

## Why this is better than the original sketch

The original design prevented borrow conflicts; the refined design prevents the
more subtle bug class of mixing different kinds of indexes even when the storage is
split correctly. In other words, the architecture is now not just about aliasing,
but about making the compiler's invariants visible in the type system itself.

The rejected alternatives were the same ones we discussed throughout the refactor:

- `RefCell` around `types` or `diagnostics`
- cloning a `Vec` just to avoid a borrow issue
- one-off conversion helpers like `as_u32()` / `as_usize()`
- ad hoc raw casts in every builder module

We deliberately rejected all of them. The plan remains the same in spirit but the
actual enforcement model is stricter and more explicit than the initial draft.