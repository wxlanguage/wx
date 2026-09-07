# Item resolution granularity — plan

**Status:** in progress (2026-09-07). The trait-header split and the whole impl side have
landed — see "What already landed"; the trait side of the member index and the
`ensure_signature` split have not. Written out of the supertrait work, because the
supertrait bug turned out to be one symptom of something more general.

The impl side landed in a different shape than steps 2–4 below described, and better: the
`members` map does not need a parallel `member_ids` index beside it, because a *declaration*
map (name → kind + `DefId`, read straight off the AST when the block header resolves) is
enough for a lookup to both recognise a candidate and force the one member it needs. Steps
2–4 are kept as written for the trait side, where the same substitution applies — read
`member_decls` for what they call the index.

## The problem in one sentence

Phase 2's unit of work is *an item's whole signature*, which is coarser than the dependency
graph it serves — so a caller that needs one fact about an item either forces far more than
it asked for (traits) or forces nothing at all and reads a half-built table (impls).

## Two bugs, one cause

### 1. Traits over-force

`ensure_signature` on a trait means "resolve the header **and** force every member"
(`signature_trait`'s member loop, `tir/builder/traits.rs`). But a member needs only the
*header* from its parent — the supertrait clause, which is what puts inherited items in
`Self`'s bounds.

Making a member force its parent's full signature is the obvious fix and it breaks the
stdlib. Prescan registers a trait's members *before* the trait itself
(`prescan.rs`: member `ast_nodes` first, the trait's own node after), so in parse order a
member is usually reached first:

```
ensure_signature(type Mem)              // Allocator's first member
│  state[Mem] = InProgress
└─ ensure_signature(Allocator)          // "parent before member"
   ├─ resolve supertrait clause ✓
   └─ member loop:
      ├─ ensure_signature(Mem)          → InProgress → Cycle → SKIPPED
      │                                   ↑ never registers its entry
      ├─ ensure_signature(allocate)
      │  └─ `Self::Mem` → Allocator.entries["Mem"] → MISSING → E1021 ✗
      └─ ...
```

The member loop ran while the caller was `InProgress`, so the one member that got skipped is
exactly the one its siblings needed. Forcing the full signature at a *use* site is safe for
the mirror-image reason: the only member skipped there is the one asking, and nothing needs
itself.

**Landed fix:** `ensure_trait_supertraits` — resolves the clause and nothing else, so a
member can demand the header without triggering the member loop.

### 2. Impls under-force

Same family, opposite failure, still open. Verified against HEAD (i.e. it predates the
supertrait work):

```wx
trait Tr { type X; }
struct S { a: i32 }
fn f(v: S::X) -> i32 { v }        // impl AFTER  → error[E1021]
impl Tr for S { type X = i32; }   // move it above `f` and it compiles
```

Two independent gaps on that path:

- **Dispatch is signature-time.** `trait_impl_dispatch` is populated by `register_trait_impl`
  (`traits.rs:1284`) inside `signature_trait_impl_block`. Until that block's node is reached
  in parse order the impl is invisible and `resolve_impl_member` finds no candidate at all.
- **No lookup ever forces a member.** `trait_member_via_impl` (`calls.rs:1451`) and
  `resolve_inherent_member` (`calls.rs:1354`) take `&self` and read
  `trait_impls[i].members` / `inherent_impls[i].members` as-is.

Nobody noticed because prescan pushes an impl block's node *before* its members
(`prescan.rs:665` then `:671`) — the opposite of traits — so impl members normally resolve
right after their block, and only a use site earlier in parse order exposes it.

**Gap 1 cannot be fixed demand-driven.** A trait is reached by name, so a lookup can force
it. An impl has no name — it is keyed by a *type* — so nothing can demand it. Impl headers
have to be collected.

## What rustc does

1. **Granularity is per-fact, not per-item.** `predicates_of` (bounds/where-clauses — our
   "header"), `associated_items` (our member index), `fn_sig`/`type_of` (a member's
   signature), `impl_trait_ref`, `trait_def` are separate queries. Asking a trait for its
   predicates *cannot* force its members' signatures.
2. **Existence facts come from resolution, before type checking.** `associated_items` is
   derived from HIR — names and DefIds — so "does this trait have an item called `X`" never
   touches a type.
3. **Cycle detection is generic**, owned by the query engine's stack rather than written per
   feature.
4. **Impls are collected in bulk, explicitly.** `rustc_hir_analysis::check_crate` runs staged
   `tcx.ensure()` sweeps — collect item types, coherence over all impls, then typeck bodies.
   The impl index (`trait_impls_of`, `crate_inherent_impls`) is a whole-crate query, and
   candidates are keyed by a cheap `fast_reject::SimplifiedType` rather than a resolved type.

An ordered sweep over impls is therefore *not* a workaround — it is the mature shape. What
makes a hand-rolled version look like one is filtering `ast_nodes` inline instead of naming
the step and letting prescan record what it iterates.

## End state

- **Prescan owns existence:** item shells (including `TraitImpl`), member name → `DefId`, and
  the list of impl-block `DefId`s.
- **`ensure_signature` splits into named demands** — header/predicates vs. member signature —
  so no caller forces more than it needs, and `ensure_trait_supertraits` stops being a
  special case and becomes "the header demand".
- **Type-keyed lookups force one member by name** through the index; name-keyed lookups are
  unchanged.
- **The impl index is collected eagerly** from the prescan list, and becomes a demanded query
  once impl targets have a cheap simplified form (see step 6).
- **Cycle reporting lives in the one guard the demands share.**

## Staging

Each step leaves the tree compiling and the suite green. Ordered so that the cheap,
user-visible fixes come first and each later step is made smaller by the one before it.

### 1. Collect impl-block headers — **done**

Landed as `Builder::resolve_impl_dispatch`, which filters `ast_nodes` for the two block
variants rather than keeping a second list: a `Vec<DefId>` built in prescan would be a
duplicate of what `ast_nodes` already holds, free to drift when a node kind is added. The
original sketch was:

```rust
// Impls are keyed by type, not by name, so nothing can demand them — the
// dispatch index has to exist before any type-keyed lookup is answered.
for id in &builder.impl_blocks {
    let _ = builder.ensure_signature(*id);
}
```

No filtering, no new phase, no new state. Fixes gap 1 (the `S::X` repro above). Reorders
diagnostics as a side effect, which is fine — see "Independent" below.

### 2. One helper per member lookup (rides along with supertrait piece D)

**Partly done** — the impl half now goes through `ensure_trait_impl_members`
(`calls.rs`), which forces a member by name off `member_decls`. What is left is the trait
half, where the sites below still force the whole parent.

Today these sites open-code "force the parent, then read `entries`/`members` by name":

- `types.rs:1113`, `types.rs:1291` — projection resolution
- `paths.rs:710` — `resolve_assoc_type_via_bounds`
- `calls.rs:1196` — `resolve_impl_member`'s `TypeParam` branch
- `calls.rs:1354` — `resolve_inherent_member`
- `calls.rs:1451` — `trait_member_via_impl`

Supertrait name resolution (piece D in `notes/supertrait-implementation.md`) has to edit all
of them anyway, to consult the supertrait chain rather than only the directly named trait. Do
that edit *through a single helper* — `trait_member(trait_index, name)` /
`impl_member(impl_index, name)` — so the parent-forcing lives in one place.

This is the highest-leverage step in the plan: it costs nothing extra while piece D is in
those files, and it turns step 4 from a six-site change into a one-function change.

### 3. Prescan member index, and a `TraitImpl` shell

Prescan already creates `Struct` (`prescan.rs:117`), `Trait` (`:341`) and inherent impl
blocks (`:426`). `TraitImpl` is the odd one out, created at `traits.rs:1247` during signature
resolution. Create its shell in prescan too — `signature_trait_impl_block` then fills
`trait_index`/`target` — and the index is a plain field on `Trait`, `TraitImpl` and
`ImplBlock`:

```rust
member_ids: HashMap<SymbolU32, ast::DefId>,
```

filled in the same prescan loop that already pushes each member's `ast_nodes` entry and
already holds both the name and the `DefId` (`prescan.rs:673`, `:685`, `:696`).

This is *not* a scope, so module-level name collisions never reach it: the key is
(parent, member name) and the parent is already resolved before anyone asks. It is the same
shape as today's `Trait::entries` / `TraitImpl::members`, differing only in *when* it is
filled and in holding a `DefId` rather than a resolved `ImplEntry`.

Alternative shape, if the `TraitImpl` shell turns out to be disruptive: one flat
`ItemRegistry::member_index: HashMap<(DefId, SymbolU32), DefId>`, mirroring the existing
`item_lookup: HashMap<DefId, ItemIndex>` (`tir/mod.rs:2588`). Less code, less discoverable,
and it leaves the shell inconsistency in place.

### 4. Flip the helper to force one member by name

Inside the step-2 helper, replace "force the parent" with "look the name up in the index,
force that member". One function, both for traits and impls. The remaining ~9 readers of
`entries` run in Phase 3/3.5, where everything is `Done`, and need no change.

### 5. Delete the trait member loop, and `ensure_trait_supertraits` with it

`signature_trait`'s member loop is no longer load-bearing once step 4 is in:
`ensure_signature(trait)` becomes header-only, exactly like `signature_trait_impl_block`, and
members force their parent through the ordinary mechanism with no sibling hole. The narrow
helper disappears into the header demand. This is the step that makes the trait and impl
paths the same shape.

### 6. (Later) Split "name" from "fields", then name-only `ImplTarget`

`ImplTarget` (`tir/mod.rs:1759`) already *is* rustc's `SimplifiedType`: a constructor head
with arguments dropped. What is missing is the ability to compute it without resolving a
type:

| target form | name-only? |
| --- | --- |
| `&[T]`, `[T; N]` | yes — syntactic, → `Slice`/`Array` |
| pointer | n/a, not a legal target (E1062) |
| path → struct/enum | yes — `SymbolKind::Struct { struct_index }` (`tir/mod.rs:1364`) already carries exactly what `ImplTarget::Struct` wants |
| primitive (`i32`) | needs that `#[intrinsic]` type alias's signature — cheap, but a demand |
| type alias | **no** — `impl Tr for Alias` is legal; needs normalization |

The blocker is that struct and enum *names* are not resolvable without forcing their
signatures: they go through `claim_name_binding` (`prescan.rs:109`) as `Pending` and only
become `SymbolKind::Struct { struct_index }` inside their own signature (`signature.rs:66`).
Traits are already inserted *resolved* at prescan (`prescan.rs:409`), and `struct_index` is
known at prescan anyway (`push_struct`, `prescan.rs:117`).

**That forcing is load-bearing, though.** `check_struct_fields_for_direct_recursion`
(`types.rs:1507`) walks `structs[i].fields` of *other* structs to find `struct A { b: B }` /
`struct B { a: A }` (E1032), and those fields are only populated because naming `B` forced its
signature. Removing the forcing without an explicit "ensure fields" demand at that point makes
the check silently incomplete and pushes an infinite layout into MIR. So the order is: split
"name → index" from "fields/layout" into separate demands *first*, then prescan-resolved
struct/enum symbols, then name-only `ImplTarget`.

For an alias-headed target, do what fast-reject does: give up on simplification and resolve
that impl fully.

With all of that, step 1's eager collection can become `ensure_impl_index()` — one memo bit,
demanded by the first type-keyed lookup. **Worth doing only when there is something to gain**:
laziness pays in a per-file incremental / LSP model, and in a batch compile Phase 2 sweeps
everything regardless, so eager collection costs nothing. Do not write
`ImplTarget::from_symbol` until it has a caller.

**Do not** change `StructIndex`/`EnumIndex` to `DefId` for this. Both producers of an
`ImplTarget` already speak indices — name resolution yields `struct_index`, and `Type::Struct`
carries `struct_index` — so `DefId` would add a `structs[i].id` hop on both paths and buy
nothing. The genuine outlier is `ImplTarget::Memory(DefId)`, DefId only because `Type::Memory`
carries one; normalizing it to `MemoryIndex` is a small separate cleanup.

## Independent, unscheduled

**Sort diagnostics by span at render time.** There is no sort anywhere on the diagnostic path
— not in `vfs`, not `diagnostics.rs`, not the CLI — so emission order *is* resolution order,
and every step above reshuffles it. That is not a reason to block on this: the order is
arbitrary either way, and no step depends on it. Worth doing on its own merits, whenever, for
deterministic CLI and LSP output.

## Behavioural decisions this forces

1. **Duplicate arbitration for structs/enums** (step 6). `Pending` exists so that whoever
   resolves first wins the name binding (`still_pending`). Prescan-resolved symbols change
   that to *first in parse order wins*, which is more deterministic — but it is a change in
   which duplicate is reported and which is kept.
2. **Diagnostic order** (unscheduled). Step 1 reorders diagnostics as a side effect. Accepted:
   the order is arbitrary today either way. Sorting by span is worth doing on its own, later.
3. **Alias-headed impl targets** (step 6). Fall back to full resolution rather than
   attempting a syntactic answer; do not silently drop such impls from the index.
4. **Duplicate members inside one parent** (step 3). Prescan reports them, first wins —
   matching what it already does for traits (`prescan.rs:317`) and moving the check earlier
   than `register_trait_impl_member` (`traits.rs:1299`) does it today.

## What already landed

**The impl side, in full** (commit "Resolve impls by demand rather than by parse order"):

- `Builder::resolve_impl_dispatch` resolves every `impl` block *header* before the Phase 2
  sweep. Headers only — a block's signature never touched its members, so this stays a
  collection step rather than a resolution phase.
- `TraitImpl`/`InherentImpl` carry `member_decls: HashMap<SymbolU32, MemberDecl>`, filled
  when the block's header resolves. "Does this impl declare this name, and is it a
  fn/const/type" comes off the AST, so it needs nothing resolved, and the `DefId` it carries
  is what lets a lookup force one member.
- `resolve_impl_member` calls `ensure_trait_impl_members` first, forcing exactly the members
  named `member_symbol` in the impls that could apply. Nothing else moves.
- Typesets are forced where a bound names them (`resolve_identifier_as_bound`,
  `resolve_path_segments_as_bound`). Their symbols are registered *resolved* at prescan, so
  naming one never forced it, and `members` could be read empty — E1047 against a legal type,
  decided by declaration order alone.

Two findings worth keeping:

- **Eager resolution of impl *members* was tried and rejected.** Pulling every impl member
  ahead of everything else is the obvious way to make `S::X` resolve, and it surfaced the
  typeset bug above — unrelated code that trusts parse order rather than forcing what it
  reads. Forcing by name at the lookup site moves nothing and provokes nothing.
- **Inherent impls still need their own pass at this.** `inherent_impl_dispatch` is keyed by
  `(ImplTarget, name)` and filled by `register_inherent_member` at *member* signature time,
  so a block's header alone does not register it. Pre-filling that index from `member_decls`
  is the fix, but it interacts with the duplicate-detection logic that reads the same bucket
  (`conflicting_inherent_block`), so it wants deciding rather than patching.

**The trait-header split**, out of the supertrait work, which fits here as "the header
demand" (step 5 absorbs it):

- Supertraits are stored as bounds on the trait's own `Self` — there is no separate field —
  and `Trait::supertraits(self_index)` reads them back by filtering the reflexive
  `Self: ThisTrait` entry. `Trait::bounds` is gone.
- `ensure_trait_supertraits` resolves only the clause, recursing up the parent chain. It has
  no state of its own: the write happens before the recursion, so non-empty `Self` bounds
  mean done-or-in-progress, which is also how a supertrait cycle terminates.
- `ItemRegistry::trait_implies` walks a declared bound's supertraits transitively (visited-
  guarded), and `type_implements_trait` asks it — so `T: B` satisfies `A` when `B: A`.

## Not in scope here

- **Supertrait name resolution through the chain** (piece D in
  `notes/supertrait-implementation.md`): `self.grandparent_method()` still fails. It is a
  separate change, but it edits exactly the sites step 2 consolidates, so the two are
  deliberately sequenced together — piece D pays for the helper, the helper pays for step 4.
- **Supertrait cycle diagnostics.** `trait A: B {} trait B: A {}` is still accepted silently.
  Telling in-progress from done needs a stack of the traits the walk is inside, which is also
  what naming the loop in the diagnostic needs; both arrive together.
- **Visibility of supertrait members** — the trait default-body `pub_span` gap already
  recorded in `CLAUDE.md`.
