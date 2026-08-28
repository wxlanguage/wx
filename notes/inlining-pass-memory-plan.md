# Inlining pass — memory & data-design plan

**Date:** 2026-08-19
**Target:** `crates/wx-compiler/src/mir/inlining.rs` (`run_inlining_pass`, `CallGraph`, `inline_expr`)
**Status:** not applied — plan only. See "Already applied" for what *is* in the tree.

---

## Why

`run_inlining_pass` deep-clones whole `Function` bodies to satisfy the borrow
checker, keys its call graph by `DefId` through two `HashMap<DefId, HashSet<DefId>>`,
and runs DCE only *after* the pass — so every unreachable function is walked,
cloned, and graph-tracked for a full pass before being discarded.

Measured on `examples/wasi_preview1_port/main.wx` (678 lines), instrumenting the
level loop:

```
[inline] level=149  with_callers=38   fns_total=179
[inline] level=15   with_callers=11   fns_total=179
[inline] level=2    with_callers=2    fns_total=179
```

149 full function-body clones in round one, 38 of which are ever read. The rest
are uncalled `#[inline]` stdlib functions still waiting for the sweep at the end
of the pass.

---

## Already applied (in the working tree, not committed)

These landed while investigating; the plan below builds on them.

1. **Narrowed the level clone.** Hoisted `caller_ids` above `targets` and
   filtered the level to members with a non-empty caller set (`inlined`) before
   paying for any per-member work. 149 clones → 38.
2. **Scoped the static-data union.** It ran as `for body in targets.values()`,
   so every caller absorbed the *whole level's* `static_data` including members
   it never calls. Since codegen unions `static_data` across live functions to
   pick data-segment entries, that kept bytes alive for functions the caller
   doesn't call — dead bytes in the output — on top of growing each caller's
   `Vec` by the whole level every round. Now inside the guarded
   `if graph.callees[&caller_id].contains(&f_id)` loop.
3. **Removed a phantom borrow-conflict.** The cycle-breaker had
   `graph.callers[&anchor].iter().copied().collect::<Vec<_>>()`. `graph` and
   `inline_callee_count` are separate locals — there was never a conflict.

Peak RSS on that example: 4.96 MB → 4.70 MB. 790 tests pass; all examples still
emit valid WASM.

---

## Plan

### 1. `CallGraph` → index-based

Two `HashMap<DefId, HashSet<DefId>>` means two hash allocations per function.
Call degrees are small enough that a linear scan over a sorted `Vec<u32>` beats
hashing.

Node space: `mir.functions` at `0..n`, then imported function `DefId`s at
`n..n+m`. Imports need nodes because DCE has to reach them — that's what the
`mir.imports` retain at the end consumes. Node index `< n` doubles as the
`mir.functions` index, so the separate `func_idx` map disappears.

```rust
/// Directed call graph over MIR functions, indexed rather than hashed: node
/// `i < functions.len()` is `functions[i]`, and the nodes past that are
/// imported functions — no body of their own, but still call targets, and so
/// still needing DCE reachability. Adjacency is `Vec<u32>` rather than
/// `HashSet`: call degrees are small enough that a linear scan beats hashing,
/// and this drops two hash allocations per function.
struct CallGraph {
	/// DefId → node. Below `functions.len()` this *is* the `MIR::functions` index.
	node_of: HashMap<ast::DefId, u32>,
	/// `callees[a]` = nodes `a` calls. Sorted and deduplicated on construction.
	callees: Vec<Vec<u32>>,
	/// `callers[a]` = nodes that call `a`. Sorted and deduplicated on construction.
	callers: Vec<Vec<u32>>,
}

impl CallGraph {
	fn build(
		functions: &[Function],
		imports: &[ImportModule],
		call_edges: &[(ast::DefId, ast::DefId)],
	) -> Self {
		let import_fns =
			imports.iter().flat_map(|m| m.items.iter()).filter_map(|item| {
				match item {
					ImportModuleItem::Function { id, .. } => Some(*id),
					_ => None,
				}
			});
		let node_of: HashMap<ast::DefId, u32> = functions
			.iter()
			.map(|f| f.id)
			.chain(import_fns)
			.enumerate()
			.map(|(i, id)| (id, i as u32))
			.collect();

		let mut callees = vec![Vec::new(); node_of.len()];
		let mut callers = vec![Vec::new(); node_of.len()];
		for &(caller_id, callee_id) in call_edges {
			let (Some(&caller), Some(&callee)) =
				(node_of.get(&caller_id), node_of.get(&callee_id))
			else {
				continue;
			};
			callees[caller as usize].push(callee);
			callers[callee as usize].push(caller);
		}
		for adjacency in callees.iter_mut().chain(callers.iter_mut()) {
			adjacency.sort_unstable();
			adjacency.dedup();
		}

		CallGraph { node_of, callees, callers }
	}

	/// Nodes reachable from the export roots and the start function.
	fn reachable(&self, mir: &MIR) -> NodeSet {
		let mut live = NodeSet::with_capacity(self.callees.len());
		let mut queue: VecDeque<u32> = VecDeque::new();

		let roots = mir
			.exports
			.iter()
			.filter_map(|e| match e {
				ExportItem::Function { id, .. } => Some(*id),
				_ => None,
			})
			.chain(mir.start_function);
		for id in roots {
			if let Some(&n) = self.node_of.get(&id) {
				if live.insert(n) {
					queue.push_back(n);
				}
			}
		}
		while let Some(n) = queue.pop_front() {
			for &callee in &self.callees[n as usize] {
				if live.insert(callee) {
					queue.push_back(callee);
				}
			}
		}
		live
	}
}
```

In-loop edge updates become `retain` / `contains`-guarded `push` on the
`Vec<u32>`s instead of `HashSet` `remove` / `insert`.

Note the edge filter tightens: today an edge is recorded on the callee side only
if the caller is a known function, and on the caller side regardless — so
function→import edges land in `callees` but never in `callers`. With import
nodes present, both directions are recorded.

### 2. `Targets` — stop cloning bodies, lift the caller instead

The clone exists purely because `inline_expr` needs `&mut` on the caller while
holding `&` on the target bodies, and both live in `mir.functions`.

Search the *small* thing (the level) rather than indexing the big one (the node
table). This also drops the `node_of` hash probe out of the walk's hot path.

```rust
/// The functions being substituted this round: `(DefId, node)` sorted by id,
/// with bodies read straight out of `MIR::functions`. No body is cloned merely
/// to be readable here — the only copy made is the one `inline_call` splices in
/// at each call site. A level is a handful of functions, so this search costs
/// less than a hash probe, and unlike a node-indexed side table it owns no
/// storage and needs no reset between rounds.
struct Targets<'a> {
	by_id: &'a [(ast::DefId, u32)],
	functions: &'a [Function],
}

impl Targets<'_> {
	fn get(&self, id: ast::DefId) -> Option<&Function> {
		let i = self
			.by_id
			.binary_search_by_key(&id.as_u32(), |(id, _)| id.as_u32())
			.ok()?;
		Some(&self.functions[self.by_id[i].1 as usize])
	}
}
```

`ast::DefId` derives `Hash, PartialEq, Eq` but **not** `Ord`, hence the
`as_u32()` key.

`inline_expr`'s parameter changes from `&HashMap<ast::DefId, Function>` to
`&Targets<'_>`, and its one lookup from `targets.get(&id)` to `targets.get(id)`.
Nothing else in that ~300-line walk changes.

The caller loop then lifts the caller out of the slice for the duration of its
walk:

```rust
for &caller in &caller_nodes {
	let ci = caller as usize;
	// Lift the caller out of `mir.functions` for the duration of its walk:
	// `inline_expr` needs `&mut` on this one function while every target body
	// it splices in is read straight out of that same slice. Kahn's algorithm
	// keeps the two disjoint — a level member has in-degree 0 in the inline
	// subgraph, so it calls no other member and therefore can't be a caller
	// this round, and a self-recursive function never reaches in-degree 0 at
	// all — so the vacated slot is never one a target is read from.
	let mut caller_func = std::mem::replace(
		&mut mir.functions[ci],
		vacated(&mir.functions[ci]),
	);

	inline_expr(
		&mut caller_func.block,
		&mut caller_func.scopes,
		&Targets { by_id: &targets_by_id, functions: &mir.functions },
		0,
	);

	for (i, &f) in inlined.iter().enumerate() {
		if !graph.callees[ci].contains(&f) {
			continue;
		}
		caller_func
			.static_data
			.extend_from_slice(&mir.functions[f as usize].static_data);

		graph.callees[ci].retain(|&c| c != f);
		graph.callers[f as usize].retain(|&c| c != caller);
		for &callee in &level_callees[i] {
			if !graph.callees[ci].contains(&callee) {
				graph.callees[ci].push(callee);
			}
			if !graph.callers[callee as usize].contains(&caller) {
				graph.callers[callee as usize].push(caller);
			}
		}

		if let Some(count) = &mut inline_callee_count[ci] {
			*count -= 1;
			if *count == 0 {
				queue.push_back(caller);
			}
		}
	}

	mir.functions[ci] = caller_func;
}
```

```rust
/// A body-less stand-in left in `mir.functions` while a caller is lifted out
/// for its inlining walk. Never read — see the lift site.
fn vacated(f: &Function) -> Function {
	Function {
		id: f.id,
		signature_index: f.signature_index,
		scopes: Vec::new(),
		block: Expression { ty: Type::Unit, kind: ExprKind::Noop },
		static_data: Vec::new(),
	}
}
```

**Open question.** The correctness of the lift rests on
`caller_nodes ∩ inlined = ∅`, which Kahn's algorithm guarantees but which
nothing in the types enforces. The plan states it as a `debug_assert!` at the
level-construction site:

```rust
debug_assert!(
	caller_nodes.iter().all(|c| inlined.binary_search(c).is_err()),
	"a level member is never one of its own level's callers"
);
```

That is a documented invariant with a debug-only guard, **not** a structural
fix — a redesign that makes the aliasing impossible would mean moving function
bodies into an arena separate from `Function`, which is a much larger change and
touches everything downstream of `mir.functions`. Decide which we want before
writing this.

### 3. Round setup — no side tables

Every `Vec<bool>` in the first draft of this plan shadowed information that
already existed. The replacements:

```rust
// Sorting the level makes `inlined` sorted (so the disjointness check is a
// binary search) and makes the whole pass deterministic — see below.
let mut level: Vec<u32> = queue.drain(..).collect();
level.sort_unstable();

// Every caller of *any* level member gets exactly one combined inline_expr
// walk, regardless of how many level members it calls. Each `callers` row is
// already sorted and deduplicated, so the union is a concatenate-and-dedup —
// no marker array, nothing to reset.
let mut caller_nodes: Vec<u32> = Vec::new();
for &f in &level {
	caller_nodes.extend_from_slice(&graph.callers[f as usize]);
}
caller_nodes.sort_unstable();
caller_nodes.dedup();

// A level member with no caller left is never substituted anywhere this round,
// so nothing below ever reads its body.
let inlined: Vec<u32> = level
	.iter()
	.copied()
	.filter(|&f| !graph.callers[f as usize].is_empty())
	.collect();

// The same set, keyed for lookup by the walk.
let mut targets_by_id: Vec<(ast::DefId, u32)> = inlined
	.iter()
	.map(|&f| (mir.functions[f as usize].id, f))
	.collect();
targets_by_id.sort_unstable_by_key(|(id, _)| id.as_u32());

// A level member's own callee set doesn't change while callers are processed
// (only caller/member edges are touched), so snapshot it once. Positionally
// paired with `inlined`.
let level_callees: Vec<Vec<u32>> =
	inlined.iter().map(|&f| graph.callees[f as usize].clone()).collect();
```

Kahn's in-degree table carries its own membership — no parallel `is_inline`
predicate:

```rust
// Kahn's algorithm on the inline subgraph: the number of inline callees not
// yet processed, absent for a node outside the subgraph — or one evicted as a
// cycle anchor.
let mut inline_callee_count: Vec<Option<u32>> = vec![None; node_count];
for id in &mir.inline_functions {
	if let Some(&n) = graph.node_of.get(id) {
		inline_callee_count[n as usize] = Some(0);
	}
}
for n in 0..node_count {
	if inline_callee_count[n].is_none() {
		continue;
	}
	let pending = graph.callees[n]
		.iter()
		.filter(|&&c| inline_callee_count[c as usize].is_some())
		.count() as u32;
	inline_callee_count[n] = Some(pending);
}
```

### 4. `NodeSet` — the one visited set that can't be dissolved

Reachability genuinely needs a visited set. It should be a set, one bit per
node, with `insert` reporting novelty so a BFS never test-then-sets.

```rust
/// A fixed-capacity set of call-graph nodes, one bit each.
struct NodeSet(Box<[u64]>);

impl NodeSet {
	fn with_capacity(nodes: usize) -> Self {
		NodeSet(vec![0; nodes.div_ceil(64)].into_boxed_slice())
	}

	/// Adds `node`, reporting whether it wasn't already present — the shape a
	/// worklist wants.
	fn insert(&mut self, node: u32) -> bool {
		let (word, bit) = (node as usize / 64, 1u64 << (node % 64));
		let absent = self.0[word] & bit == 0;
		self.0[word] |= bit;
		absent
	}

	fn contains(&self, node: u32) -> bool {
		self.0[node as usize / 64] & (1u64 << (node % 64)) != 0
	}
}
```

Both DCE sweeps and both retains read the same type. 8× smaller than
`Vec<bool>`, and it says what it is.

### 5. DCE before the pass, not only after

```rust
pub fn run_inlining_pass(mir: &mut MIR) {
	// Drop everything unreachable from the export roots *before* any inlining
	// work. Inlining only ever removes call edges — a caller absorbs its
	// callee's own edges — and never adds a function, so nothing dropped here
	// could have become reachable later on. Anything left out of this set would
	// otherwise be walked, its callers' bodies rewritten, and its edges tracked
	// for a whole pass before the sweep at the end discarded it.
	{
		let full =
			CallGraph::build(&mir.functions, &mir.imports, &mir.call_edges);
		let live = full.reachable(mir);
		// `retain` visits in order, and function nodes are the leading
		// `mir.functions.len()` entries of the node space.
		let mut nodes = 0u32..;
		mir.functions.retain(|_| live.contains(nodes.next().unwrap()));
	}

	let mut graph =
		CallGraph::build(&mir.functions, &mir.imports, &mir.call_edges);
	// ... Kahn's, as above ...
}
```

The final sweep still has to run: a function whose only callers all inlined it
away becomes unreachable *during* the pass, and only the second sweep catches
that. Both use the same `reachable`.

Two `CallGraph::build` calls: pre-DCE needs adjacency before the working graph
can be built over the survivors. Each is `O(V+E)` into `Vec<Vec<u32>>`, so both
together still allocate far less than today's single
`HashMap<DefId, HashSet<DefId>>` pair.

**The final function set is unchanged** — pre-DCE's removals are a subset of
post-DCE's — so snapshots shouldn't move.

Depends on: every function reference recording a call edge, including
function-*pointer* references (`ExprKind::Function { id }` used as a value, not
called). Verified — `mir/mod.rs` calls `record_call_edge` on that path, and
`examples/func_pointers` compiles and validates. Post-DCE already relies on this
today, so pre-DCE is no weaker.

### 6. `mir/mod.rs` — the start-function clone

`MIR::build` deep-clones the whole start function and then throws the original
away:

```rust
// before
if let Some(ref f) = start_function {
	functions.push(f.clone());
}
// ...
start_function: start_function.map(|_| start_id),

// after
let has_start = start_function.is_some();
if let Some(f) = start_function {
	functions.push(f);
}
// ...
start_function: has_start.then_some(start_id),
```

---

## Falls out of this: the pass becomes deterministic

Not a goal, but worth having. Three places currently iterate a `HashMap` /
`HashSet` and let hash order decide real outcomes:

- `caller_ids: HashSet<DefId>` — the order callers get walked.
- `inline_callee_count.iter().filter(|n| **n == 0)` — the order the initial
  queue is seeded, which decides level *composition* on later rounds.
- `inline_callee_count.iter().find(|n| **n > 0)` — **which function gets evicted
  as the mutual-recursion anchor**, i.e. which one is left un-inlined.

Going index-based makes all three deterministic: `sort_unstable` on
`caller_nodes`, `0..node_count` for seeding, `position()` for the anchor (lowest
node index wins). If a snapshot ever flakes around mutually-recursive
`#[inline]`, this is the cause.

---

## Verification checklist

- `cargo test -p wx-compiler` — 790 tests, no snapshot movement expected.
- `cargo build --release -p wx-cli`, then compile every `examples/*/main.wx` and
  `wasm-validate` each output. Byte sizes should be unchanged or smaller (the
  static-data scoping in "already applied" can only shrink the data segment).
- Re-run the level instrumentation to confirm clone count drops to zero and
  `fns_total` drops after pre-DCE.
- Peak RSS via `/usr/bin/time -l` on `examples/wasi_preview1_port/main.wx`
  (baseline before any of this work: 4,964,352 bytes).

---

## Appendix — adjacent findings, not part of this plan

Found while surveying, outside `inlining.rs`:

- **`TIR::type_index_lookup` (`HashMap<Type, TypeIndex>`)** and
  **`opt::Function::data_lookup` (`HashMap<DataNodeKind, DataNodeIndex>`)** each
  store a full second copy of every interned key, boxed slices included — the
  type pool and the node-kind pool are each held twice. Both are index-keyed-set
  candidates (`hashbrown::HashTable`, already in the build graph via
  `string-interner`), where the key is the index and hashing/equality goes
  through the pool.
- **`opt::DataNode.uses: Vec<DataNodeIndex>`** is one heap allocation per node,
  but it's write-only during building and read in exactly two places
  (`opt/local_dominance.rs:74`, `opt/scheduler.rs:1960`). A CSR side table built
  once after the function is complete would take N allocations to 2.
- **`opt::DataNodeKind` is 24 bytes**, of which the 16 come from the
  `Box<[DataNodeIndex]>` in exactly 2 of ~120 variants (`Aggregate { fields }`,
  `CallResult { args }`). Moving those into a shared arg pool as a `(u32, u32)`
  range would shrink the node array by a third and make the kind `Copy` — which
  would in turn remove the `self.func.data_nodes[n].kind.clone()` in
  `opt/scheduler.rs::emit_value_inline`, the innermost loop of codegen.
- **`cmd_compile` in `wx-cli`** holds `tir` and the whole `CompilationGraph`
  (all ASTs and source text) alive across codegen. `MIR` is fully owned, and
  codegen only needs `&mir` and `&compilation.interner`, so both could be
  dropped right after `MIR::build`.
