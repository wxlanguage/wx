# MIR dead-code elimination

Status as of 2026-11-04, branch `tir-translation`: planned, not
implemented. Takes over step 4 of `notes/mir-inlining.md` (dead functions
and compaction), which today lives in `mir/inline.rs` and removes
functions only.

## The problem

Removing only dead functions leaves behind what a dead function was the
last user of. Lowering is lazy, so a global is lowered the first time
something names it; if the only function naming it is later inlined away
and dropped, the global stays in the module. The same will hold for a
memory, and for static data, once they are lowered.

So dead-code elimination is over every kind of item, not over functions.

## Items and their dependencies

An item is anything the module holds and an import or an export can name,
plus static data:

```rust
index_newtype!(DataId); // index into MIR::static_entries

pub enum Item {
    Function(FunctionId),
    Global(GlobalId),
    Memory(MemoryId),
    Data(DataId),
}
```

A static data entry is an identity of its own that depends on a memory:
its bytes are placed in that memory's data segment. `StaticPointer
{ data_index: u32 }` becomes `StaticPointer { data: DataId }`, and
`StaticEntry::memory` is the entry's dependency.

What each kind depends on is stated in one place, read-only:

```rust
impl MIR {
    /// Every item `item` refers to.
    pub fn dependencies(&self, item: Item, f: impl FnMut(Item));
}
```

| Item | Depends on |
| ---- | ---------- |
| defined function | what its code's nodes name |
| imported function | nothing |
| static data | its memory |
| global | nothing (later: a function, for a `ref.func` initializer) |
| memory | nothing |

Which items a node names is one match in `mir/body.rs`, beside `ids_mut`
and `cost` and separate from both:

```rust
/// An item a node names, as `ExprKind::items_mut` hands it out.
pub enum ItemRef<'a> {
    Function(&'a mut FunctionId),
    Global(&'a mut GlobalId),
    Memory(&'a mut MemoryId),
    Data(&'a mut DataId),
}

impl ExprKind {
    pub fn items_mut(&mut self, f: impl FnMut(ItemRef<'_>));
}
```

`Call` names a function, `Global` and `GlobalSet` a global, the memory
nodes their memories (`MemoryCopy` two), `StaticPointer` its data. A new
variant that names an item says so in this one arm.

`ids_mut` stays what it is: the structure inside one body (expressions,
lists, cases, locals, labels), indices that mean something only in that
function. Item ids are module-level identities, read and rewritten only by
module-level passes. Two walks, two kinds of index.

There is one `items_mut`, not a read-only twin beside it: marking calls it
on a copy (`ExprKind` is `Copy`, as `verify` uses `ids_mut`), so the list
of which nodes name items is written once.

## The pass: `mir::dce::run(mir: &mut MIR)`

Mark and sweep, in that order, each knowing nothing of the other's
details.

### Mark

The roots are what the outside refers to: exports of every kind and the
start function (later, a table's element segment). A work list of `Item`
walks `dependencies` from them, with one `live` column per kind
(`Vec<bool>` indexed by that kind's id). Nothing is rewritten.

A dead function is never marked, so nothing it names is marked through
it: a global, a data entry or a memory whose only user was a dead function
is never reached. The cascade needs no fixed point, because this is
reachability from the roots, not reference counting.

### Sweep

For each kind, the live items get new ids in id order (`Vec<Option<_>>`,
old id to new), and so do the import entries that provide a live item.
Then every place an id is stored is rewritten through them:

- every node, through `items_mut`;
- `exports` and `imports` (each entry's item), and `Origin::Imported` of
  each imported item (its entry's new index);
- `start_function`;
- each static entry's `memory`.

and each table keeps only its live entries, at their new positions. Every
table is indexed by its own id, so `Global` and `MemoryInfo` drop their
`id` fields, as `Function` did (`MIR::global`/`MIR::memory` read by
index). Debug builds run `verify_imports` afterwards.

## Pipeline

lower → inline → dce → codegen. `tir::build` returns MIR as lowered; the
wasmtime harness of `tir/lower.rs` and the inliner's tests run inline and
then dce. A later MIR pass that can orphan items runs before dce.

The inliner keeps its `rooted` column, which the one-call-site rule reads
(an export or the start function is never inlined away), and removes
nothing itself: `remove_dead_functions` moves here and generalizes.

Lazy lowering stays: it saves lowering work (std items nothing uses), but
it is no longer what keeps the output free of dead items; dce is.

Codegen already gathers static data only from the live code; after dce
that is every entry left, so it can emit `static_entries` as they are.

## Decisions

1. **An unused import entry is dropped**, for every kind. It changes the
   module's import list, which only an embedder filling imports by
   position notices; accepted already for functions (`notes/mir-arena.md`,
   decision 14).
2. **An unused defined memory is dropped**, unless it is exported, which
   makes it a root.
3. **Static data is an item**, with a dependency on its memory, not an
   anonymous payload of the function that points at it.

## Tests (`mir/dce.rs`)

- A global named only by a function the inliner removed is dropped, and
  one named by a live function is kept.
- An imported global or function nothing live names loses its import
  entry; `verify_imports` holds afterwards.
- An exported item is kept with nothing naming it.
- On hand-built MIR (memories are not lowered yet): a data entry and its
  memory are dropped with the only function pointing at the entry, and
  kept while one live function does; a memory only data depends on is
  kept with that data.
- After the sweep, every id a node, an export, an import entry, the start
  function or a static entry holds is in range, and each table's index is
  its id.
- Every lowering test still runs under wasmtime with the same result.

## Order of work

1. `DataId`, `Item::Data`, `StaticPointer { data }`; drop the `id` fields
   of `Global` and `MemoryInfo`.
2. `ItemRef` and `ExprKind::items_mut`; `MIR::dependencies`.
3. `mir/dce.rs`: mark and sweep, moving `remove_dead_functions` out of the
   inliner.
4. Wire it after the inliner in the test harnesses; the tests above.
