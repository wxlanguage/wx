//! Lower a sea-of-nodes [`Function`] to a flat sequence of WASM stack-machine
//! instructions.
//!
//! # Algorithm
//!
//! 1. **Spill decision** — `should_spill` decides whether a node must be
//!    materialised into a WASM local or can be inlined at its single use site.
//!    Constants and params are always inlined. Multi-use nodes and call results
//!    are always spilled.
//!
//! 2. **Dead pointer-load elimination** — before emission we compute the set of
//!    data nodes reachable backwards from control-node data sinks. Pure
//!    `PointerLoad` control nodes whose result is not live are skipped.
//!
//! 3. **Scheduling order** — we walk the block tree recursively and emit
//!    instructions in a post-order traversal of data dependencies: each node's
//!    inputs are emitted (or loaded from their local) before the node itself.
//!
//! # Output
//!
//! The scheduler produces a [`wasm::Function`] containing
//! - the extra WASM locals needed for spilled nodes (appended after params)
//! - a flat `Vec<Instruction>` for the function body
//!
//! `wasm::Function`/`Instruction` and everything else describing that
//! output shape live in `crate::wasm` — not here, since `codegen` (the sole
//! consumer, which does the actual byte encoding) needs them independent
//! of this module's own sea-of-nodes-specific types.

use std::collections::HashMap;

use crate::mir;
use crate::opt::liveness::DataLiveness;
use crate::opt::{
	BlockIndex, ControlNode, DataNode, DataNodeIndex, DataNodeKind, Function,
	MemAccess, ScalarType, StackResult, SwitchCase,
};
use crate::wasm::{self, BlockType, Instruction, Local, MemArg};

// ── Scheduler
// ─────────────────────────────────────────────────────────────────

pub struct Scheduler<'f> {
	func: &'f Function,
	mir: &'f mir::MIR,
	/// Data nodes reachable from control-node sinks under the scheduler's
	/// current emission semantics.
	live_data: DataLiveness,
	/// WASM locals: params (already allocated) + spill slots added by
	/// `ensure_local`.
	locals: Vec<Local>,
	/// Maps a scalar data-node index to its WASM local index.
	node_to_local: HashMap<DataNodeIndex, u32>,
	/// Maps an aggregate data-node index to its per-field WASM local indices.
	node_to_aggregate_locals: HashMap<DataNodeIndex, Box<[u32]>>,
	/// Output instruction stream.
	body: Vec<Instruction>,
	/// Flat arena backing every emitted `Instruction::BrTable` — see
	/// `wasm::Function::br_table_depths`.
	br_table_depths: Vec<u32>,
	/// Placement decisions for pure values read from more than one block —
	/// computed once by `compute_value_placement` before emission starts,
	/// consulted (and drained, one block at a time) by `emit_block`. Indexed
	/// directly by `BlockIndex` rather than a `HashMap` — both index types
	/// here are dense `u32`s, the same convention `DataLiveness` uses for
	/// `DataNodeIndex`. See `compute_value_placement`'s doc comment.
	placement_by_block: Vec<Vec<DataNodeIndex>>,
}

impl<'f> Scheduler<'f> {
	pub fn schedule(func: &'f Function, mir: &'f mir::MIR) -> wasm::Function {
		let sig = &mir.signatures[{
			// Find the function's signature via its DefId.
			mir.functions
				.iter()
				.find(|f| f.id == func.id)
				.expect("function not found")
				.signature_index as usize
		}];

		// Aggregate params are flattened to one local per field.
		let locals: Vec<Local> = sig
			.params()
			.iter()
			.copied()
			.flat_map(|ty| wasm::flatten_type_to_scalars(ty, &mir.aggregates))
			.map(|ty| Local { ty })
			.collect();
		let params_count = locals.len();

		let mut sched = Scheduler {
			func,
			mir,
			live_data: DataLiveness::compute(func),
			locals,
			node_to_local: HashMap::new(),
			node_to_aggregate_locals: HashMap::new(),
			body: Vec::new(),
			br_table_depths: Vec::new(),
			placement_by_block: Vec::new(),
		};
		sched.placement_by_block = sched.compute_value_placement();

		sched.emit_block(0);

		if matches!(sched.body.last(), Some(Instruction::Return)) {
			sched.body.pop();
		}

		wasm::coalesce_locals(&mut sched.body, &mut sched.locals, params_count);
		wasm::peephole_local_tee(&mut sched.body);

		wasm::Function {
			locals: sched.locals,
			body: sched.body,
			br_table_depths: sched.br_table_depths,
		}
	}

	// ── Control emission ──────────────────────────────────────────────────────

	fn emit_control(&mut self, block_idx: BlockIndex, stmt: &ControlNode) {
		match stmt {
			ControlNode::Return { value } => {
				if let StackResult::Value(node) = value {
					self.emit_value(*node);
				}
				self.body.push(Instruction::Return);
			}

			ControlNode::GlobalSet { id, value } => {
				self.emit_value(*value);
				self.body.push(Instruction::GlobalSet(*id));
			}

			ControlNode::Call {
				callee,
				args,
				result,
				callee_sig,
			} => {
				for &arg in args.iter() {
					self.emit_value(arg);
				}
				self.emit_call(*callee, *callee_sig);
				if let StackResult::Value(result_node) = result {
					match self.func.data_nodes[*result_node as usize].kind {
						DataNodeKind::AggregateCallResult {
							aggregate_index,
						} => {
							// Multi-value return: fields arrive deepest-first; pop in
							// reverse so each local.set captures the correct field.
							//
							// Always spill: result may be referenced via control-node
							// args (return, call) not tracked in DataNode::uses.
							let mut locals = Vec::with_capacity(
								self.mir.aggregates[aggregate_index as usize]
									.values
									.len(),
							);
							for &t in self.mir.aggregates
								[aggregate_index as usize]
								.values
								.iter()
								.rev()
							{
								let ty = ScalarType::try_from(t)
									.expect("field must be scalar");
								let local = self.alloc_local(ty);
								self.body.push(Instruction::LocalSet(local));
								locals.push(local);
							}
							locals.reverse();
							self.node_to_aggregate_locals.insert(
								*result_node,
								locals.into_boxed_slice(),
							);
						}
						_ => {
							// Scalar result: spill to a local if used, drop otherwise.
							if self.should_spill(
								&self.func.data_nodes[*result_node as usize],
							) {
								let ty = self.func.data_nodes
									[*result_node as usize]
									.kind
									.unwrap_scalar();
								let local = self.alloc_local(ty);
								self.node_to_local.insert(*result_node, local);
								self.body.push(Instruction::LocalSet(local));
							} else {
								self.body.push(Instruction::Drop);
							}
						}
					}
				}
			}

			ControlNode::IfElse {
				condition,
				then_block,
				else_block,
				outputs,
				result,
			} => {
				// Pre-allocate WASM locals for phi outputs.
				self.pre_alloc_phi_outputs(outputs);

				// A phi's "else" (unchanged) input is normally stored by the
				// `emit_phi_stores_for_branch(.., false)` call below, but that
				// runs inside the WASM `else` block — which doesn't exist
				// here. Without it, a false condition would skip straight to
				// `end`, leaving each phi's freshly allocated (zero-valued)
				// local instead of the source's implied "stays unchanged"
				// value. So that store is emitted once, unconditionally,
				// right here before the `if`. This never conflicts with the
				// `then`-branch store below: when the condition is true, the
				// `then` block's own store (inside the `if`) runs afterward
				// and overwrites the same local — WASM's `if` semantics
				// guarantee the `then` block's code, store included, simply
				// doesn't execute at all when the condition is false, so
				// exactly one store's result is ever actually observed.
				if else_block.is_none() {
					self.emit_phi_stores_for_branch(
						*then_block,
						outputs,
						false,
					);
				}

				self.emit_value(*condition);

				// When phis are stored via LocalSet inside branches, the if block
				// must have an empty result type — the branches consume the value.
				let result_block_ty = if outputs.is_empty() {
					self.stack_result_block_type(*result)
				} else {
					BlockType::Empty
				};
				self.body.push(Instruction::If {
					ty: result_block_ty,
				});

				self.emit_block(*then_block);
				// When there are no phi outputs, the if block has a value result
				// type; each branch must leave its result on the stack.
				if outputs.is_empty() {
					let then_block_result = self.func.blocks
						[*then_block as usize]
						.as_ref()
						.unwrap()
						.result;
					if let StackResult::Value(n) = then_block_result {
						self.emit_value(n);
					}
				}
				self.emit_phi_stores_for_branch(*then_block, outputs, true);
				if let Some(eb) = else_block {
					self.body.push(Instruction::Else);
					self.emit_block(*eb);
					if outputs.is_empty() {
						let else_block_result = self.func.blocks[*eb as usize]
							.as_ref()
							.unwrap()
							.result;
						if let StackResult::Value(n) = else_block_result {
							self.emit_value(n);
						}
					}
					self.emit_phi_stores_for_branch(*eb, outputs, false);
				}
				self.body.push(Instruction::End);

				// Value-type block: the if-End leaves the result on the WASM stack.
				// Capture it into a local so the parent's emit_value(result_node) can
				// read from the local rather than pushing a second copy.
				if outputs.is_empty() {
					if let StackResult::Value(result_node) = *result {
						let local = if let Some(&l) =
							self.node_to_local.get(&result_node)
						{
							l
						} else {
							let ty = self.func.data_nodes[result_node as usize]
								.kind
								.unwrap_scalar();
							let l = self.alloc_local(ty);
							self.node_to_local.insert(result_node, l);
							l
						};
						self.body.push(Instruction::LocalSet(local));
					}
				}
			}

			ControlNode::Switch {
				selector,
				cases,
				default,
				outputs,
				result,
			} => {
				self.pre_alloc_phi_outputs(outputs);

				// Compared against every case constant below — always spill to
				// its own local (regardless of the generic multi-use spill
				// heuristic, which only tracks DataNode-to-DataNode uses, not
				// ControlNode references) so each comparison rereads the same
				// computed value instead of re-emitting a (possibly impure)
				// computation once per case.
				self.emit_value(*selector);
				let selector_ty = self.func.data_nodes[*selector as usize]
					.kind
					.unwrap_scalar();
				let selector_local = self.alloc_local(selector_ty);
				self.body.push(Instruction::LocalSet(selector_local));

				let result_block_ty = if outputs.is_empty() {
					self.stack_result_block_type(*result)
				} else {
					BlockType::Empty
				};

				self.emit_switch_br_table(
					selector_local,
					selector_ty,
					cases,
					default.as_ref(),
					outputs,
					result_block_ty,
				);

				// Same "capture the fallthrough value into a local" step
				// `IfElse` does — lets the parent's `emit_value(result_node)`
				// read from a local uniformly rather than assuming a value is
				// still sitting on the WASM stack.
				if outputs.is_empty() {
					if let StackResult::Value(result_node) = *result {
						let local = if let Some(&l) =
							self.node_to_local.get(&result_node)
						{
							l
						} else {
							let ty = self.func.data_nodes[result_node as usize]
								.kind
								.unwrap_scalar();
							let l = self.alloc_local(ty);
							self.node_to_local.insert(result_node, l);
							l
						};
						self.body.push(Instruction::LocalSet(local));
					}
				}
			}

			ControlNode::Loop {
				body,
				outputs,
				result: _,
			} => {
				// Allocate a fresh local for each loop param and initialise it
				// with the `before` value.  Each param gets its own local so that
				// two params with the same `before` node (e.g. both init to 1)
				// don't share a slot and overwrite each other.
				for &lp in outputs.iter() {
					if let DataNodeKind::LoopParam { before, ty, .. } =
						self.func.data_nodes[lp as usize].kind
					{
						let local = self.alloc_local(ty);
						self.emit_value(before);
						self.body.push(Instruction::LocalSet(local));
						self.node_to_local.insert(lp, local);
					}
				}

				// Pre-allocate WASM locals for break-result phi nodes so that
				// Break handlers inside the body can write to them before `br`.
				for phi in self
					.func
					.loop_data(*body)
					.break_result_outputs
					.iter()
					.copied()
				{
					if self.node_to_local.contains_key(&phi) {
						continue;
					}
					let ty =
						self.func.data_nodes[phi as usize].kind.unwrap_scalar();
					let local = self.alloc_local(ty);
					self.node_to_local.insert(phi, local);
				}

				// The outer block has an empty result type: break values are held
				// in phi locals, not passed via WASM block result.
				self.body.push(Instruction::Block {
					ty: BlockType::Empty,
				});
				self.body.push(Instruction::Loop {
					ty: BlockType::Empty,
				});

				self.emit_block(*body);

				// Push all after-values first, then pop in reverse — avoids
				// swap-corruption when two params share an input node.
				for &lp in outputs.iter() {
					if let DataNodeKind::LoopParam { after, .. } =
						self.func.data_nodes[lp as usize].kind
					{
						self.emit_value(after);
					}
				}
				for &lp in outputs.iter().rev() {
					if let DataNodeKind::LoopParam { .. } =
						self.func.data_nodes[lp as usize].kind
					{
						let lp_local = *self.node_to_local.get(&lp).unwrap();
						self.body.push(Instruction::LocalSet(lp_local));
					}
				}

				// Back-edge; unreachable if the body always breaks or returns.
				self.body.push(Instruction::Br(0));

				self.body.push(Instruction::End); // Loop
				self.body.push(Instruction::End); // Block
			}

			ControlNode::Break {
				target,
				value,
				loop_param_updates,
			} => {
				if let StackResult::Value(v) = value {
					// Store break value into phi locals; LocalSet in reverse
					// because emit_value pushes fields lowest-first.
					let n_phis =
						self.func.loop_data(*target).break_result_outputs.len();
					if n_phis > 0 {
						self.emit_value(*v);
						for phi in self
							.func
							.loop_data(*target)
							.break_result_outputs
							.iter()
							.copied()
							.rev()
						{
							let phi_local =
								*self.node_to_local.get(&phi).expect(
									"break result phi local must be pre-allocated by Loop handler",
								);
							self.body.push(Instruction::LocalSet(phi_local));
						}
					}
				}
				// This break's own current values for the target loop's
				// carried bindings — committed here because the loop's normal
				// "commit, then branch back" tail code only runs on ordinary
				// fallthrough, which this `br` bypasses entirely. See
				// `Builder::loop_param_updates`.
				self.emit_loop_param_updates(loop_param_updates);
				let depth = self.break_depth(block_idx, *target);
				self.body.push(Instruction::Br(depth));
			}

			ControlNode::Continue {
				target,
				loop_param_updates,
			} => {
				self.emit_loop_param_updates(loop_param_updates);
				let depth = self.continue_depth(block_idx, *target);
				self.body.push(Instruction::Br(depth));
			}

			ControlNode::Unreachable => {
				self.body.push(Instruction::Unreachable);
			}

			ControlNode::MemorySize { memory, result } => {
				self.body.push(Instruction::MemorySize(*memory));
				let ty =
					self.func.data_nodes[*result as usize].kind.unwrap_scalar();
				let local = self.alloc_local(ty);
				self.node_to_local.insert(*result, local);
				self.body.push(Instruction::LocalSet(local));
			}

			ControlNode::MemoryGrow {
				memory,
				delta,
				result,
			} => {
				self.emit_value(*delta);
				self.body.push(Instruction::MemoryGrow(*memory));
				if self.should_spill(&self.func.data_nodes[*result as usize]) {
					let ty = self.func.data_nodes[*result as usize]
						.kind
						.unwrap_scalar();
					let local = self.alloc_local(ty);
					self.node_to_local.insert(*result, local);
					self.body.push(Instruction::LocalSet(local));
				}
			}

			ControlNode::PointerLoad {
				address,
				offset,
				result,
				memory,
				access,
			} => {
				if !self.live_data.is_live(*result) {
					return;
				}
				self.emit_value(*address);
				let m = MemArg {
					align: access.align_log2(),
					offset: *offset,
					memory: *memory,
				};
				let load_instr = match access {
					MemAccess::I8S => Instruction::I32Load8S(m),
					MemAccess::I8U => Instruction::I32Load8U(m),
					MemAccess::I16S => Instruction::I32Load16S(m),
					MemAccess::I16U => Instruction::I32Load16U(m),
					MemAccess::I32 => Instruction::I32Load(m),
					MemAccess::I64 => Instruction::I64Load(m),
					MemAccess::F32 => Instruction::F32Load(m),
					MemAccess::F64 => Instruction::F64Load(m),
				};
				self.body.push(load_instr);
				// PointerLoadResult always spills (no_cse + always_spill).
				let scalar_ty = access.scalar_type();
				let local = self.alloc_local(scalar_ty);
				self.node_to_local.insert(*result, local);
				self.body.push(Instruction::LocalSet(local));
			}

			ControlNode::MemoryFill {
				memory,
				dst,
				val,
				len,
			} => {
				self.emit_value(*dst);
				self.emit_value(*val);
				self.emit_value(*len);
				self.body.push(Instruction::MemoryFill(*memory));
			}

			ControlNode::MemoryCopy {
				dst_memory,
				src_memory,
				dst,
				src,
				len,
			} => {
				self.emit_value(*dst);
				self.emit_value(*src);
				self.emit_value(*len);
				self.body.push(Instruction::MemoryCopy {
					dst: *dst_memory,
					src: *src_memory,
				});
			}

			ControlNode::PointerStore {
				address,
				offset,
				value,
				memory,
				access,
			} => {
				self.emit_value(*address);
				self.emit_value(*value);
				let m = MemArg {
					align: access.align_log2(),
					offset: *offset,
					memory: *memory,
				};
				let store_instr = match access {
					MemAccess::I8S | MemAccess::I8U => {
						Instruction::I32Store8(m)
					}
					MemAccess::I16S | MemAccess::I16U => {
						Instruction::I32Store16(m)
					}
					MemAccess::I32 => Instruction::I32Store(m),
					MemAccess::I64 => Instruction::I64Store(m),
					MemAccess::F32 => Instruction::F32Store(m),
					MemAccess::F64 => Instruction::F64Store(m),
				};
				self.body.push(store_instr);
			}
		}
	}

	fn emit_block(&mut self, block_idx: BlockIndex) {
		// Materialize any pure values placed here by `compute_value_placement`
		// before this block's own statements — they may be read by more than
		// one of this block's (mutually exclusive) descendant branches, so
		// they must exist in a local before any of those branches run, not
		// lazily on whichever one the scheduler happens to reach first.
		let nodes = self.placement_by_block[block_idx as usize].clone();
		for node in nodes {
			self.ensure_local(node);
		}
		for stmt in &self.func.blocks[block_idx as usize]
			.as_ref()
			.expect("block scope should be built")
			.statements
		{
			self.emit_control(block_idx, stmt);
		}
	}

	// ── Cross-branch value placement ────────────────────────────────────────

	/// Decides, for every pure `DataNode` read from more than one block, the
	/// single block where it must be materialized: the lowest block that is
	/// an ancestor of (i.e. always runs before) every block that reads it.
	///
	/// `should_spill`/`ensure_local` alone are only sound when a spilled
	/// node's uses all live in the same block — they materialize a value
	/// lazily, the first time `emit_value` reaches it. That's unsound
	/// whenever the reading blocks are siblings under an `if`/`else` or
	/// `match` (only one of them actually runs at a time, so whichever
	/// branch the scheduler's single-pass walk happens to visit first
	/// "claims" the store, and any other branch reading the same node just
	/// gets a local that branch never actually populated) — or even when one
	/// reader is inside a branch and another is in the block that contains
	/// it, since the containing block isn't guaranteed the branch that
	/// computed the value actually ran.
	///
	/// `Block::parent` already gives this IR a tree over blocks (nesting via
	/// `if`/`switch`/`loop`, not a general CFG), so "the block guaranteed to
	/// run before a set of others" is just their lowest common ancestor in
	/// that tree — no dominator-tree algorithm needed.
	///
	/// Both `DataNodeIndex` and `BlockIndex` are dense `u32`s (see
	/// `DataLiveness` for the same convention), so every set below is a
	/// plain `Vec` indexed directly by one of them rather than a hashmap.
	/// Finding which blocks read which nodes is a single forward pass
	/// (`record_block_own_nodes`, direct operands only, no recursion)
	/// followed by a single backward pass propagating each node's readers
	/// down to its own operands (`for_each_operand`). That backward pass is
	/// valid in one sweep because a node's operands always have a lower
	/// `DataNodeIndex` than the node itself — a node can only reference an
	/// operand that was already interned (`Builder::intern_node` assigns
	/// indices in creation order) — so by the time the sweep reaches a
	/// node, every one of its own readers (all at higher indices) has
	/// already propagated its blocks into it. This replaces re-deriving each
	/// node's full transitive closure from scratch at every site that reads
	/// it, which repeats work across shared sub-expressions.
	fn compute_value_placement(&self) -> Vec<Vec<DataNodeIndex>> {
		let mut consuming_blocks: Vec<Vec<BlockIndex>> =
			vec![Vec::new(); self.func.data_nodes.len()];
		for block_idx in 0..self.func.blocks.len() as BlockIndex {
			if self.func.blocks[block_idx as usize].is_none() {
				continue;
			}
			self.record_block_own_nodes(block_idx, &mut consuming_blocks);
		}

		// Propagate downward: a pure node's readers are also, transitively,
		// readers of its own operands. Impure nodes (CallResult, GlobalGet,
		// LoopParam, Phi, ...) never propagate past themselves — their own
		// operands (a call's args, a phi's per-branch inputs, ...) are
		// always consumed at the single fixed control-node site that
		// produces the impure value (e.g. a call's args are pushed and
		// consumed exactly once, right where the call executes), which
		// `record_block_own_nodes` already recorded directly. Re-deriving
		// that from wherever the impure *result* is later read would be
		// redundant at best and wrong at worst, since the result's readers
		// don't run where the impure computation itself ran.
		for node in (0..self.func.data_nodes.len() as DataNodeIndex).rev() {
			if consuming_blocks[node as usize].is_empty() {
				continue;
			}
			if !self.func.data_nodes[node as usize].kind.is_pure() {
				continue;
			}
			let blocks = consuming_blocks[node as usize].clone();
			self.for_each_operand(node, |operand| {
				for &b in &blocks {
					push_unique_block(
						&mut consuming_blocks[operand as usize],
						b,
					);
				}
			});
		}

		let block_depths = self.compute_block_depths();
		let mut placement_by_block: Vec<Vec<DataNodeIndex>> =
			vec![Vec::new(); self.func.blocks.len()];
		for node in 0..self.func.data_nodes.len() as DataNodeIndex {
			let blocks = &consuming_blocks[node as usize];
			if blocks.len() < 2 {
				continue;
			}
			if !self.func.data_nodes[node as usize].kind.is_pure() {
				continue;
			}
			if !self.should_spill(&self.func.data_nodes[node as usize]) {
				continue;
			}
			let mut blocks_iter = blocks.iter().copied();
			let first = blocks_iter.next().unwrap();
			let lca = blocks_iter
				.fold(first, |acc, b| self.lca_block(&block_depths, acc, b));
			// If the LCA is itself one of the consuming blocks, this node is
			// already naturally computed there in program order — e.g.
			// `local cur_end = heap.size() * PAGE_SIZE; if new_end > cur_end
			// { ... cur_end ... }`: `cur_end` is read both by the condition
			// (in the block that declares it) and from inside the nested
			// `then` branch, so its LCA is that same declaring block. That
			// block's own existing lazy-on-first-use `ensure_local` call
			// (triggered while emitting the condition, strictly before the
			// nested branch is even entered) is already correct and
			// sufficient — forcing materialization at the very *start* of
			// that block instead would run it before whatever it itself
			// depends on (here, the `heap.size()` call) has executed.
			// Hoisting only the cases where the LCA is a strict ancestor —
			// never a member of `blocks` itself — is exactly what keeps this
			// pass from ever reordering a value ahead of its own inputs.
			if !blocks.contains(&lca) {
				placement_by_block[lca as usize].push(node);
			}
		}
		placement_by_block
	}

	/// Records every `DataNode` that `block_idx`'s own statements read.
	///
	/// A phi's `left`/`right` (`IfElse.outputs`) or a switch arm's own
	/// contribution (`SwitchCase.own_values`) is recorded against the
	/// specific branch block that actually produced it — `then_block`/
	/// `else_block`/`case.block` — never against `block_idx` itself.
	/// `block_idx` (the block containing the `if`/`switch`) only ever reads
	/// the phi's *merged* result, a value in its own right that's already
	/// correctly materialized by the existing `pre_alloc_phi_outputs`/
	/// `emit_phi_stores_for_branch` machinery — not the branch-local values
	/// feeding into it. Recording those against `block_idx` instead of their
	/// true origin block is exactly the bug this function exists to avoid:
	/// it would misidentify a value that's only ever computed inside one
	/// specific branch as something already available beforehand.
	///
	/// Only records the *direct* operand named by each control node —
	/// transitive propagation to that operand's own operands happens once,
	/// globally, in `compute_value_placement`'s backward sweep. Every case
	/// below reduces to the same one-line insertion into `consuming_blocks`
	/// (`push_unique_block`, shared with that backward sweep) — the size of
	/// this function is `ControlNode`'s own variant count, not new logic.
	fn record_block_own_nodes(
		&self,
		block_idx: BlockIndex,
		consuming_blocks: &mut [Vec<BlockIndex>],
	) {
		let block = self.func.blocks[block_idx as usize]
			.as_ref()
			.expect("block scope should be built");
		// `Block::result` is the block's own exit value (e.g. an if-branch's
		// tail expression) — separate from `statements`, and where a value
		// like `map_y_f` in the doc example gets read when a branch's whole
		// body is just `(oy - map_y_f) * delta_dist_y` with no other
		// statement.
		if let StackResult::Value(n) = block.result {
			push_unique_block(&mut consuming_blocks[n as usize], block_idx);
		}
		for stmt in &block.statements {
			match stmt {
				ControlNode::Return { value } => {
					if let StackResult::Value(n) = value {
						push_unique_block(
							&mut consuming_blocks[*n as usize],
							block_idx,
						);
					}
				}
				ControlNode::GlobalSet { value, .. } => {
					push_unique_block(
						&mut consuming_blocks[*value as usize],
						block_idx,
					);
				}
				ControlNode::Call { callee, args, .. } => {
					push_unique_block(
						&mut consuming_blocks[*callee as usize],
						block_idx,
					);
					for &a in args.iter() {
						push_unique_block(
							&mut consuming_blocks[a as usize],
							block_idx,
						);
					}
				}
				ControlNode::IfElse {
					condition,
					then_block,
					else_block,
					outputs,
					..
				} => {
					push_unique_block(
						&mut consuming_blocks[*condition as usize],
						block_idx,
					);
					for &phi in outputs.iter() {
						// The phi's own merged value is read by block_idx.
						push_unique_block(
							&mut consuming_blocks[phi as usize],
							block_idx,
						);
						let DataNodeKind::Phi { left, right, .. } =
							&self.func.data_nodes[phi as usize].kind
						else {
							continue;
						};
						let (l, r) = (*left, *right);
						push_unique_block(
							&mut consuming_blocks[l as usize],
							*then_block,
						);
						// No `else`: per `Builder::merge_branches`, `right`
						// is just whatever `bindings[i]` already held going
						// into the `if` — i.e. the parent's own pre-existing
						// value, not anything computed inside a branch — so
						// it belongs to block_idx.
						let r_block = else_block.unwrap_or(block_idx);
						push_unique_block(
							&mut consuming_blocks[r as usize],
							r_block,
						);
					}
				}
				ControlNode::Switch {
					selector,
					cases,
					default,
					outputs,
					..
				} => {
					push_unique_block(
						&mut consuming_blocks[*selector as usize],
						block_idx,
					);
					for &phi in outputs.iter() {
						push_unique_block(
							&mut consuming_blocks[phi as usize],
							block_idx,
						);
					}
					for case in cases.iter().chain(default.iter()) {
						for &own in case.own_values.iter() {
							if let StackResult::Value(n) = own {
								push_unique_block(
									&mut consuming_blocks[n as usize],
									case.block,
								);
							}
						}
					}
				}
				ControlNode::Loop { outputs, .. } => {
					// LoopParam nodes themselves are impure (excluded from
					// placement entirely); nothing pure to record here.
					for &o in outputs.iter() {
						push_unique_block(
							&mut consuming_blocks[o as usize],
							block_idx,
						);
					}
				}
				ControlNode::Break {
					value,
					loop_param_updates,
					..
				} => {
					if let StackResult::Value(n) = value {
						push_unique_block(
							&mut consuming_blocks[*n as usize],
							block_idx,
						);
					}
					for &(_, current) in loop_param_updates.iter() {
						push_unique_block(
							&mut consuming_blocks[current as usize],
							block_idx,
						);
					}
				}
				ControlNode::Continue {
					loop_param_updates, ..
				} => {
					for &(_, current) in loop_param_updates.iter() {
						push_unique_block(
							&mut consuming_blocks[current as usize],
							block_idx,
						);
					}
				}
				ControlNode::Unreachable => {}
				// `result`/`delta` etc. that *produce* a value (rather than
				// read one) are deliberately not recorded here — see the
				// impure-node skip in `compute_value_placement`.
				ControlNode::MemorySize { .. } => {}
				ControlNode::MemoryGrow { delta, .. } => {
					push_unique_block(
						&mut consuming_blocks[*delta as usize],
						block_idx,
					);
				}
				ControlNode::MemoryFill { dst, val, len, .. } => {
					for &n in [dst, val, len] {
						push_unique_block(
							&mut consuming_blocks[n as usize],
							block_idx,
						);
					}
				}
				ControlNode::MemoryCopy { dst, src, len, .. } => {
					for &n in [dst, src, len] {
						push_unique_block(
							&mut consuming_blocks[n as usize],
							block_idx,
						);
					}
				}
				ControlNode::PointerLoad { address, .. } => {
					push_unique_block(
						&mut consuming_blocks[*address as usize],
						block_idx,
					);
				}
				ControlNode::PointerStore { address, value, .. } => {
					for &n in [address, value] {
						push_unique_block(
							&mut consuming_blocks[n as usize],
							block_idx,
						);
					}
				}
			}
		}
	}

	/// Invokes `f` once for each `DataNode` operand `node` directly reads —
	/// one hop, not transitive. `compute_value_placement`'s backward sweep
	/// supplies the transitivity by visiting every node in the function
	/// exactly once, in decreasing index order.
	///
	/// `node` is always pure here (the sweep skips impure nodes before
	/// calling this), so the impure arms below — `CallResult`,
	/// `MemoryGrowResult`, `PointerLoadResult`, `Phi`, `LoopParam` — are
	/// unreachable in practice. They're listed anyway (as no-ops) so the
	/// match stays exhaustive against `DataNodeKind` and reads uniformly:
	/// an impure node's own operands are consumed at the single
	/// control-node site that produces it, already recorded directly by
	/// `record_block_own_nodes`, not wherever the impure result is later
	/// read.
	fn for_each_operand(
		&self,
		node: DataNodeIndex,
		mut f: impl FnMut(DataNodeIndex),
	) {
		match &self.func.data_nodes[node as usize].kind {
			DataNodeKind::Add { left, right, .. }
			| DataNodeKind::Sub { left, right, .. }
			| DataNodeKind::Mul { left, right, .. }
			| DataNodeKind::DivS { left, right, .. }
			| DataNodeKind::DivU { left, right, .. }
			| DataNodeKind::RemS { left, right, .. }
			| DataNodeKind::RemU { left, right, .. }
			| DataNodeKind::BitAnd { left, right, .. }
			| DataNodeKind::BitOr { left, right, .. }
			| DataNodeKind::BitXor { left, right, .. }
			| DataNodeKind::Shl { left, right, .. }
			| DataNodeKind::ShrS { left, right, .. }
			| DataNodeKind::ShrU { left, right, .. }
			| DataNodeKind::Eq { left, right, .. }
			| DataNodeKind::NotEq { left, right, .. }
			| DataNodeKind::LtS { left, right, .. }
			| DataNodeKind::LtU { left, right, .. }
			| DataNodeKind::LtEqS { left, right, .. }
			| DataNodeKind::LtEqU { left, right, .. }
			| DataNodeKind::GtS { left, right, .. }
			| DataNodeKind::GtU { left, right, .. }
			| DataNodeKind::GtEqS { left, right, .. }
			| DataNodeKind::GtEqU { left, right, .. } => {
				f(*left);
				f(*right);
			}
			DataNodeKind::Neg { operand, .. }
			| DataNodeKind::Sqrt { operand, .. }
			| DataNodeKind::Abs { operand, .. }
			| DataNodeKind::Floor { operand, .. }
			| DataNodeKind::Ceil { operand, .. }
			| DataNodeKind::Trunc { operand, .. }
			| DataNodeKind::BitNot { operand, .. }
			| DataNodeKind::Eqz { operand }
			| DataNodeKind::I64ExtendI32S { operand }
			| DataNodeKind::I64ExtendI32U { operand }
			| DataNodeKind::I32WrapI64 { operand }
			| DataNodeKind::F32ConvertI32 { operand }
			| DataNodeKind::F32ConvertU32 { operand }
			| DataNodeKind::F32ConvertI64 { operand }
			| DataNodeKind::F32ConvertU64 { operand }
			| DataNodeKind::F64ConvertI32 { operand }
			| DataNodeKind::F64ConvertU32 { operand }
			| DataNodeKind::F64ConvertI64 { operand }
			| DataNodeKind::F64ConvertU64 { operand }
			| DataNodeKind::I32TruncF32 { operand }
			| DataNodeKind::U32TruncF32 { operand }
			| DataNodeKind::I32TruncF64 { operand }
			| DataNodeKind::U32TruncF64 { operand }
			| DataNodeKind::I64TruncF32 { operand }
			| DataNodeKind::U64TruncF32 { operand }
			| DataNodeKind::I64TruncF64 { operand }
			| DataNodeKind::U64TruncF64 { operand }
			| DataNodeKind::F64PromoteF32 { operand }
			| DataNodeKind::F32DemoteF64 { operand }
			| DataNodeKind::AggregateGet {
				aggregate: operand, ..
			} => {
				f(*operand);
			}
			DataNodeKind::Aggregate { fields, .. } => {
				for &field in fields.iter() {
					f(field);
				}
			}
			// Impure — unreachable here; see this function's doc comment.
			DataNodeKind::Phi { .. }
			| DataNodeKind::CallResult { .. }
			| DataNodeKind::MemoryGrowResult { .. }
			| DataNodeKind::PointerLoadResult { .. } => {}
			// Leaf nodes, plus impure result kinds with no operand of
			// interest here.
			DataNodeKind::Int { .. }
			| DataNodeKind::Float { .. }
			| DataNodeKind::Param { .. }
			| DataNodeKind::GlobalGet { .. }
			| DataNodeKind::FunctionRef { .. }
			| DataNodeKind::StaticDataRef { .. }
			| DataNodeKind::MemoryOffset { .. }
			| DataNodeKind::MemoryIndex { .. }
			| DataNodeKind::MemorySizeResult { .. }
			| DataNodeKind::AggregateCallResult { .. }
			| DataNodeKind::LoopParam { .. } => {}
		}
	}

	/// Depth of each block in the `Block::parent` tree (root = 0), computed
	/// in one forward pass over `self.func.blocks`. Valid in one pass for
	/// the same reason `for_each_operand`'s backward sweep is: a block's
	/// parent always has a lower `BlockIndex` than the block itself (a
	/// nested scope's index is only minted once its enclosing scope
	/// already exists), so a block's parent's depth is always already
	/// final by the time the block itself is visited.
	fn compute_block_depths(&self) -> Vec<u32> {
		let mut depths = vec![0u32; self.func.blocks.len()];
		for (i, block) in self.func.blocks.iter().enumerate() {
			if let Some(parent) = block.as_ref().and_then(|b| b.parent) {
				depths[i] = depths[parent as usize] + 1;
			}
		}
		depths
	}

	/// Lowest common ancestor of two blocks in the `Block::parent` tree —
	/// the block guaranteed to run before both, as late as possible.
	/// `depths` (from `compute_block_depths`, computed once per function)
	/// lets this walk both parent chains in lockstep instead of building an
	/// ancestor set for one side.
	fn lca_block(
		&self,
		depths: &[u32],
		mut a: BlockIndex,
		mut b: BlockIndex,
	) -> BlockIndex {
		let parent_of = |b: BlockIndex| {
			self.func.blocks[b as usize]
				.as_ref()
				.unwrap()
				.parent
				.unwrap()
		};
		while depths[a as usize] > depths[b as usize] {
			a = parent_of(a);
		}
		while depths[b as usize] > depths[a as usize] {
			b = parent_of(b);
		}
		while a != b {
			a = parent_of(a);
			b = parent_of(b);
		}
		a
	}

	// ── Value emission ────────────────────────────────────────────────────────

	/// Emit instructions that push `node`'s value onto the WASM stack.
	/// If the node is spilled to a local, emits `local.get`; otherwise inlines.
	/// Aggregate nodes push all their field locals in field order.
	fn emit_value(&mut self, node: DataNodeIndex) {
		if matches!(
			self.func.data_nodes[node as usize].kind,
			DataNodeKind::Aggregate { .. }
				| DataNodeKind::AggregateCallResult { .. }
		) {
			self.ensure_aggregate_locals(node);
			for i in 0..self.node_to_aggregate_locals[&node].len() {
				let local = self.node_to_aggregate_locals[&node][i];
				self.body.push(Instruction::LocalGet(local));
			}
			return;
		}
		if self.should_spill(&self.func.data_nodes[node as usize]) {
			let local = self.ensure_local(node);
			self.body.push(Instruction::LocalGet(local));
			return;
		}
		self.emit_value_inline(node);
	}

	/// Compute and push the value without checking / writing a local.
	fn emit_value_inline(&mut self, node: DataNodeIndex) {
		match self.func.data_nodes[node as usize].kind.clone() {
			DataNodeKind::Int { value, ty } => match ty {
				ScalarType::I32 => {
					self.body.push(Instruction::I32Const(value as i32))
				}
				ScalarType::I64 => self.body.push(Instruction::I64Const(value)),
				_ => unreachable!("Int node with float type"),
			},
			DataNodeKind::Float { bits, ty } => match ty {
				ScalarType::F32 => self
					.body
					.push(Instruction::F32Const(f32::from_bits(bits as u32))),
				ScalarType::F64 => {
					self.body.push(Instruction::F64Const(f64::from_bits(bits)))
				}
				_ => unreachable!("Float node with int type"),
			},
			DataNodeKind::Param { index, .. } => {
				self.body.push(Instruction::LocalGet(index));
			}
			DataNodeKind::GlobalGet { id, .. } => {
				self.body.push(Instruction::GlobalGet(id));
			}
			DataNodeKind::FunctionRef { id } => {
				self.body.push(Instruction::FunctionPointer(id));
			}
			DataNodeKind::StaticDataRef { data_index, ty } => {
				self.body
					.push(Instruction::StaticDataPointer { data_index, ty });
			}
			DataNodeKind::MemoryOffset { memory, .. } => {
				self.body.push(Instruction::DataSectionEnd { memory });
			}
			DataNodeKind::MemoryIndex { memory } => {
				self.body.push(Instruction::MemoryIndex { memory });
			}
			DataNodeKind::MemorySizeResult { .. } => {
				unreachable!(
					"MemorySizeResult must be read from a local, not emitted inline"
				)
			}

			// Arithmetic / bitwise — push left, push right, emit opcode.
			DataNodeKind::Add { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Add,
					ScalarType::I64 => Instruction::I64Add,
					ScalarType::F32 => Instruction::F32Add,
					ScalarType::F64 => Instruction::F64Add,
				});
			}
			DataNodeKind::Sub { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Sub,
					ScalarType::I64 => Instruction::I64Sub,
					ScalarType::F32 => Instruction::F32Sub,
					ScalarType::F64 => Instruction::F64Sub,
				});
			}
			DataNodeKind::Mul { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Mul,
					ScalarType::I64 => Instruction::I64Mul,
					ScalarType::F32 => Instruction::F32Mul,
					ScalarType::F64 => Instruction::F64Mul,
				});
			}
			DataNodeKind::DivS { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32DivS,
					ScalarType::I64 => Instruction::I64DivS,
					ScalarType::F32 => Instruction::F32Div,
					ScalarType::F64 => Instruction::F64Div,
				});
			}
			DataNodeKind::DivU { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32DivU,
					ScalarType::I64 => Instruction::I64DivU,
					_ => unreachable!("float division is always DivS"),
				});
			}
			DataNodeKind::RemS { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32RemS,
					ScalarType::I64 => Instruction::I64RemS,
					_ => unimplemented!("float remainder"),
				});
			}
			DataNodeKind::RemU { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32RemU,
					ScalarType::I64 => Instruction::I64RemU,
					_ => unimplemented!("float remainder"),
				});
			}
			DataNodeKind::BitAnd { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32And,
					ScalarType::I64 => Instruction::I64And,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::BitOr { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Or,
					ScalarType::I64 => Instruction::I64Or,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::BitXor { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Xor,
					ScalarType::I64 => Instruction::I64Xor,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::Shl { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Shl,
					ScalarType::I64 => Instruction::I64Shl,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::ShrS { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32ShrS,
					ScalarType::I64 => Instruction::I64ShrS,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::ShrU { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32ShrU,
					ScalarType::I64 => Instruction::I64ShrU,
					_ => unimplemented!(),
				});
			}

			DataNodeKind::Neg { operand, ty } => match ty {
				ScalarType::F32 => {
					self.emit_value(operand);
					self.body.push(Instruction::F32Neg);
				}
				ScalarType::F64 => {
					self.emit_value(operand);
					self.body.push(Instruction::F64Neg);
				}
				ScalarType::I32 => {
					self.body.push(Instruction::I32Const(0));
					self.emit_value(operand);
					self.body.push(Instruction::I32Sub);
				}
				ScalarType::I64 => {
					self.body.push(Instruction::I64Const(0));
					self.emit_value(operand);
					self.body.push(Instruction::I64Sub);
				}
			},
			DataNodeKind::Sqrt { operand, ty } => {
				self.emit_value(operand);
				self.body.push(match ty {
					ScalarType::F32 => Instruction::F32Sqrt,
					ScalarType::F64 => Instruction::F64Sqrt,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::Abs { operand, ty } => {
				self.emit_value(operand);
				self.body.push(match ty {
					ScalarType::F32 => Instruction::F32Abs,
					ScalarType::F64 => Instruction::F64Abs,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::Floor { operand, ty } => {
				self.emit_value(operand);
				self.body.push(match ty {
					ScalarType::F32 => Instruction::F32Floor,
					ScalarType::F64 => Instruction::F64Floor,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::Ceil { operand, ty } => {
				self.emit_value(operand);
				self.body.push(match ty {
					ScalarType::F32 => Instruction::F32Ceil,
					ScalarType::F64 => Instruction::F64Ceil,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::Trunc { operand, ty } => {
				self.emit_value(operand);
				self.body.push(match ty {
					ScalarType::F32 => Instruction::F32Trunc,
					ScalarType::F64 => Instruction::F64Trunc,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::BitNot { operand, ty } => {
				// WASM has no bitwise-not; emit `x ^ -1`.
				self.emit_value(operand);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Const(-1),
					ScalarType::I64 => Instruction::I64Const(-1),
					_ => unimplemented!(),
				});
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Xor,
					ScalarType::I64 => Instruction::I64Xor,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::Eqz { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I32Eqz);
			}
			DataNodeKind::I64ExtendI32S { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I64ExtendI32S);
			}
			DataNodeKind::I64ExtendI32U { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I64ExtendI32U);
			}
			DataNodeKind::I32WrapI64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I32WrapI64);
			}
			DataNodeKind::F32ConvertI32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F32ConvertI32S);
			}
			DataNodeKind::F32ConvertU32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F32ConvertI32U);
			}
			DataNodeKind::F32ConvertI64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F32ConvertI64S);
			}
			DataNodeKind::F32ConvertU64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F32ConvertI64U);
			}
			DataNodeKind::F64ConvertI32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F64ConvertI32S);
			}
			DataNodeKind::F64ConvertU32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F64ConvertI32U);
			}
			DataNodeKind::F64ConvertI64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F64ConvertI64S);
			}
			DataNodeKind::F64ConvertU64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F64ConvertI64U);
			}
			DataNodeKind::I32TruncF32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I32TruncF32S);
			}
			DataNodeKind::U32TruncF32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I32TruncF32U);
			}
			DataNodeKind::I32TruncF64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I32TruncF64S);
			}
			DataNodeKind::U32TruncF64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I32TruncF64U);
			}
			DataNodeKind::I64TruncF32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I64TruncF32S);
			}
			DataNodeKind::U64TruncF32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I64TruncF32U);
			}
			DataNodeKind::I64TruncF64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I64TruncF64S);
			}
			DataNodeKind::U64TruncF64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::I64TruncF64U);
			}
			DataNodeKind::F64PromoteF32 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F64PromoteF32);
			}
			DataNodeKind::F32DemoteF64 { operand } => {
				self.emit_value(operand);
				self.body.push(Instruction::F32DemoteF64);
			}

			DataNodeKind::Eq { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Eq,
					ScalarType::I64 => Instruction::I64Eq,
					ScalarType::F32 => Instruction::F32Eq,
					ScalarType::F64 => Instruction::F64Eq,
				});
			}
			DataNodeKind::NotEq { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32Ne,
					ScalarType::I64 => Instruction::I64Ne,
					ScalarType::F32 => Instruction::F32Ne,
					ScalarType::F64 => Instruction::F64Ne,
				});
			}
			DataNodeKind::LtS { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32LtS,
					ScalarType::I64 => Instruction::I64LtS,
					ScalarType::F32 => Instruction::F32Lt,
					ScalarType::F64 => Instruction::F64Lt,
				});
			}
			DataNodeKind::LtU { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32LtU,
					ScalarType::I64 => Instruction::I64LtU,
					_ => unimplemented!("float unsigned cmp"),
				});
			}
			DataNodeKind::LtEqS { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32LeS,
					ScalarType::I64 => Instruction::I64LeS,
					ScalarType::F32 => Instruction::F32Le,
					ScalarType::F64 => Instruction::F64Le,
				});
			}
			DataNodeKind::LtEqU { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32LeU,
					ScalarType::I64 => Instruction::I64LeU,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::GtS { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32GtS,
					ScalarType::I64 => Instruction::I64GtS,
					ScalarType::F32 => Instruction::F32Gt,
					ScalarType::F64 => Instruction::F64Gt,
				});
			}
			DataNodeKind::GtU { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32GtU,
					ScalarType::I64 => Instruction::I64GtU,
					_ => unimplemented!(),
				});
			}
			DataNodeKind::GtEqS { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32GeS,
					ScalarType::I64 => Instruction::I64GeS,
					ScalarType::F32 => Instruction::F32Ge,
					ScalarType::F64 => Instruction::F64Ge,
				});
			}
			DataNodeKind::GtEqU { left, right, ty } => {
				self.emit_value(left);
				self.emit_value(right);
				self.body.push(match ty {
					ScalarType::I32 => Instruction::I32GeU,
					ScalarType::I64 => Instruction::I64GeU,
					_ => unimplemented!(),
				});
			}

			DataNodeKind::AggregateGet {
				aggregate,
				field_index,
				..
			} => {
				// Ensure the aggregate's per-*leaf* locals are populated (see
				// `ensure_aggregate_locals`), then find the one belonging to
				// this (always-scalar, per `get_aggregate_field`) top-level
				// field: `node_to_aggregate_locals` is flattened, so a field
				// preceded by a nested-aggregate sibling doesn't sit at
				// `field_index` directly — skip past every leaf contributed
				// by earlier sibling fields first.
				self.ensure_aggregate_locals(aggregate);
				let aggregate_index =
					match &self.func.data_nodes[aggregate as usize].kind {
						DataNodeKind::Aggregate {
							aggregate_index, ..
						}
						| DataNodeKind::AggregateCallResult {
							aggregate_index,
						} => *aggregate_index,
						_ => unreachable!(
							"AggregateGet::aggregate must itself be an aggregate node"
						),
					};
				let leaf_offset: usize = self.mir.aggregates
					[aggregate_index as usize]
					.values[..field_index as usize]
					.iter()
					.map(|&t| {
						wasm::flatten_type_to_scalars(t, &self.mir.aggregates)
							.len()
					})
					.sum();
				let field_local =
					self.node_to_aggregate_locals[&aggregate][leaf_offset];
				self.body.push(Instruction::LocalGet(field_local));
			}

			DataNodeKind::Phi { .. } => {
				// A phi's local was pre-allocated by `pre_alloc_phi_outputs`.
				// The scheduler reads it here; the branches write it via LocalSet.
				let local = self.node_to_local[&node];
				self.body.push(Instruction::LocalGet(local));
			}

			DataNodeKind::LoopParam { before, .. } => {
				// Unmodified loop param (before == after, should_spill = false):
				// the value never changes, so just re-emit the `before` value directly.
				self.emit_value(before);
			}

			DataNodeKind::CallResult { .. }
			| DataNodeKind::MemoryGrowResult { .. }
			| DataNodeKind::PointerLoadResult { .. } => {
				// Always spilled; should have been caught by `should_spill` above.
				let local = self.node_to_local[&node];
				self.body.push(Instruction::LocalGet(local));
			}

			// Aggregates are intercepted in `emit_value` before reaching here.
			DataNodeKind::Aggregate { .. }
			| DataNodeKind::AggregateCallResult { .. } => {
				unreachable!(
					"aggregate nodes are handled by emit_value, not emit_value_inline"
				)
			}
		}
	}

	/// Returns true if this node must be computed into a WASM local rather than
	/// inlined at each use site.
	fn should_spill(&self, node: &DataNode) -> bool {
		match &node.kind {
			// Constants and params are always cheaper to re-emit than to spill.
			DataNodeKind::Int { .. }
			| DataNodeKind::Float { .. }
			| DataNodeKind::Param { .. }
			| DataNodeKind::FunctionRef { .. }
			| DataNodeKind::StaticDataRef { .. }
			| DataNodeKind::MemoryOffset { .. } => false,

			// Loop params whose before == after were never modified; skip.
			DataNodeKind::LoopParam { before, after, .. } => before != after,

			// Phi nodes that folded away (left == right) don't need a local.
			DataNodeKind::Phi { left, right, .. } => left != right,

			// Control-node results always produce a result that must be captured.
			DataNodeKind::CallResult { .. }
			| DataNodeKind::AggregateCallResult { .. }
			| DataNodeKind::MemorySizeResult { .. }
			| DataNodeKind::MemoryGrowResult { .. }
			| DataNodeKind::PointerLoadResult { .. } => true,

			// GlobalGet reads mutable state. Control nodes (Return, Break,
			// GlobalSet) use data-node values but never call register_uses, so
			// a GlobalGet whose only non-control use is a single data node still
			// has uses.len()==1 and would not be spilled by the catch-all below.
			// If a GlobalSet to the same global is emitted between the read and
			// a late emit_value_inline call, the inline re-read returns the
			// post-write value instead of the original. Always spilling ensures
			// the value is captured in a local on the first use (which is always
			// scheduled before any write to the same global that depends on the
			// read's descendants), and subsequent uses read the saved local.
			DataNodeKind::GlobalGet { .. } => true,

			// Aggregates live in per-field locals, not on the stack.
			DataNodeKind::Aggregate { .. } => true,

			// For all other ops: spill only if the result is consumed more than once.
			_ => node.uses.len() > 1,
		}
	}

	/// Ensure per-*leaf* WASM locals exist for an `Aggregate` node.
	/// Emits each scalar field expression and spills it to a fresh local; a
	/// field that is itself an aggregate has no local of its own — it's
	/// walked into recursively, and its own (already- or newly-computed)
	/// leaf locals are spliced in directly, so `node_to_aggregate_locals`
	/// always ends up holding one entry per *leaf* scalar, flattened in the
	/// same pre-order as `wasm::flatten_type_to_scalars`. Records the mapping in
	/// `node_to_aggregate_locals`.
	///
	/// For `AggregateCallResult` nodes this must never be called — their locals
	/// are populated by `emit_control` when the call instruction is emitted.
	fn ensure_aggregate_locals(&mut self, node: DataNodeIndex) {
		if self.node_to_aggregate_locals.contains_key(&node) {
			return;
		}
		let (fields, aggregate_index) =
			match self.func.data_nodes[node as usize].kind.clone() {
				DataNodeKind::Aggregate {
					fields,
					aggregate_index,
				} => (fields, aggregate_index),
				DataNodeKind::AggregateCallResult { .. } => {
					unreachable!(
						"AggregateCallResult locals must be populated by emit_control before use"
					)
				}
				_ => panic!(
					"ensure_aggregate_locals called on non-aggregate node"
				),
			};
		let mut locals = Vec::with_capacity(fields.len());
		for (i, &field_node) in fields.iter().enumerate() {
			let field_ty =
				self.mir.aggregates[aggregate_index as usize].values[i];
			match field_ty {
				mir::Type::Aggregate { .. } => {
					self.ensure_aggregate_locals(field_node);
					locals.extend_from_slice(
						&self.node_to_aggregate_locals[&field_node],
					);
				}
				_ => {
					let scalar_ty = ScalarType::try_from(field_ty)
						.expect("non-aggregate field must be scalar");
					self.emit_value(field_node);
					let local = self.alloc_local(scalar_ty);
					self.body.push(Instruction::LocalSet(local));
					locals.push(local);
				}
			}
		}
		self.node_to_aggregate_locals
			.insert(node, locals.into_boxed_slice());
	}

	/// Ensure a WASM local exists for a scalar node. Computes and stores the
	/// value if not yet materialised.
	fn ensure_local(&mut self, node: DataNodeIndex) -> u32 {
		if let Some(&l) = self.node_to_local.get(&node) {
			return l;
		}
		self.emit_value_inline(node);
		let ty = self.func.data_nodes[node as usize].kind.unwrap_scalar();
		let local = self.alloc_local(ty);
		self.body.push(Instruction::LocalSet(local));
		self.node_to_local.insert(node, local);
		local
	}

	fn alloc_local(&mut self, ty: ScalarType) -> u32 {
		let idx = self.locals.len() as u32;
		self.locals.push(Local { ty });
		idx
	}

	/// Pre-allocate WASM locals for phi nodes produced by an if-else join.
	/// Both branches will write to these locals; the code after the if-else
	/// reads them.
	fn pre_alloc_phi_outputs(&mut self, outputs: &[DataNodeIndex]) {
		for &phi in outputs {
			if self.node_to_local.contains_key(&phi) {
				continue;
			}
			let ty = self.func.data_nodes[phi as usize].kind.unwrap_scalar();
			let local = self.alloc_local(ty);
			self.node_to_local.insert(phi, local);
		}
	}

	/// Emit `local.set` instructions at the end of a branch for each phi
	/// output.
	fn emit_phi_stores_for_branch(
		&mut self,
		_branch_block: BlockIndex,
		outputs: &[DataNodeIndex],
		is_then: bool,
	) {
		for &phi in outputs {
			let (input, local) = match &self.func.data_nodes[phi as usize].kind
			{
				DataNodeKind::Phi { left, right, .. } => {
					let input = if is_then { *left } else { *right };
					let local = *self.node_to_local.get(&phi).unwrap();
					(input, local)
				}
				_ => continue,
			};
			self.emit_value(input);
			self.body.push(Instruction::LocalSet(local));
		}
	}

	/// Commits a `break`/`continue` site's own current values for its target
	/// loop's carried bindings, immediately before the `br` that leaves the
	/// current block. See `Builder::loop_param_updates` for why every such
	/// site must do this independently rather than relying on the loop's own
	/// (fallthrough-only) tail code.
	fn emit_loop_param_updates(
		&mut self,
		updates: &[(DataNodeIndex, DataNodeIndex)],
	) {
		// Two-phase, matching `ControlNode::Loop`'s own tail code: push every
		// current value first, *then* pop into locals in reverse. A single
		// interleaved emit+store pass would be wrong here — a later update's
		// `current` can itself be an expression that reads an *earlier*
		// update's `param` local (e.g. `acc += i; i += 1;`: acc's new value
		// reads `i`'s old value out of the very local `i`'s own update is
		// about to overwrite), so every read must happen before any write.
		for &(_, current) in updates {
			self.emit_value(current);
		}
		for &(param, _) in updates.iter().rev() {
			let local = *self.node_to_local.get(&param).expect(
				"loop param local must be pre-allocated by the Loop handler",
			);
			self.body.push(Instruction::LocalSet(local));
		}
	}

	/// Emits `cases` (guaranteed non-empty, `selector_ty == I32` — see
	/// `Builder::should_use_br_table`) as a WASM `br_table` jump table,
	/// nested in a fixed stack of `block`s so every case — and the trailing
	/// `default`, or `unreachable` if TIR proved exhaustiveness without one
	/// — gets its own branch depth:
	///
	/// ```text
	/// block $after                       (result_block_ty)
	///   block $default
	///     block $case[N-1]
	///       ...
	///         block $case[0]
	///           <selector - min>  br_table
	///         end                        ; case 0 body starts here
	///         <case 0 body>  br $after
	///       end                          ; case 1 body starts here
	///       ...
	///     end                            ; case N-1 body starts here
	///     <case N-1 body>  br $after
	///   end                              ; default body starts here
	///   <default body>                   ; (or `unreachable`)
	/// end
	/// ```
	///
	/// `Builder::build_switch` allocates a matching chain of synthetic
	/// depth-bookkeeping blocks (`Builder::push_synthetic_block`) so a
	/// `break`/`continue` written inside an arm still resolves through the
	/// ordinary `break_depth`/`continue_depth` ancestor walk with no
	/// scheduler-side depth bookkeeping — this function must keep emitting
	/// exactly that many real `block`s (`case_count + 2`) for the two to
	/// stay in sync.
	fn emit_switch_br_table(
		&mut self,
		selector_local: u32,
		selector_ty: ScalarType,
		cases: &[SwitchCase],
		default: Option<&SwitchCase>,
		outputs: &[DataNodeIndex],
		result_block_ty: BlockType,
	) {
		debug_assert_eq!(
			selector_ty,
			ScalarType::I32,
			"should_use_br_table restricts br_table to an I32 selector"
		);
		let case_count = cases.len();

		self.body.push(Instruction::Block {
			ty: result_block_ty,
		}); // $after
		self.body.push(Instruction::Block {
			ty: BlockType::Empty,
		}); // $default
		for _ in 0..case_count {
			self.body.push(Instruction::Block {
				ty: BlockType::Empty,
			}); // $case[N-1] .. $case[0], innermost last
		}

		let min = cases
			.iter()
			.filter_map(|c| c.discriminant)
			.min()
			.expect("should_use_br_table guarantees at least one case");
		let max = cases
			.iter()
			.filter_map(|c| c.discriminant)
			.max()
			.expect("should_use_br_table guarantees at least one case");
		let range = (max - min) as usize + 1;

		// `depths[i]` for `i < range` is the branch depth for shifted-selector
		// value `i` — the *array position* of the case whose discriminant is
		// `min + i` (cases aren't necessarily discriminant-sorted, so this
		// can't be computed positionally from the value alone). The trailing
		// entry is the default depth; every slot starts there, covering both
		// "gap within the range" (density < 1.0 is allowed) and the
		// out-of-range/default case uniformly.
		let mut depths = vec![case_count as u32; range + 1];
		for (i, case) in cases.iter().enumerate() {
			let d = case.discriminant.expect("non-default switch case");
			depths[(d - min) as usize] = i as u32;
		}

		self.body.push(Instruction::LocalGet(selector_local));
		self.body.push(Instruction::I32Const(min as i32));
		self.body.push(Instruction::I32Sub);
		let start = self.br_table_depths.len() as u32;
		self.br_table_depths.extend_from_slice(&depths);
		self.body.push(Instruction::BrTable {
			start,
			len: depths.len() as u32,
		});

		for (i, case) in cases.iter().enumerate() {
			self.body.push(Instruction::End); // end $case[i]
			self.emit_switch_case_body(case, outputs);
			self.body.push(Instruction::Br((case_count - i) as u32));
		}
		self.body.push(Instruction::End); // end $default
		match default {
			Some(case) => self.emit_switch_case_body(case, outputs),
			// TIR proved every case is covered (exhaustive enum match with
			// no explicit `_`) — nothing left to fall through to.
			None => self.body.push(Instruction::Unreachable),
		}
		self.body.push(Instruction::End); // end $after
	}

	fn emit_switch_case_body(
		&mut self,
		case: &SwitchCase,
		outputs: &[DataNodeIndex],
	) {
		self.emit_block(case.block);
		if outputs.is_empty() {
			// Value-type block: like `IfElse`, the arm's own tail value (its
			// `Block::result`, not one of its `statements`) must be pushed
			// explicitly so it flows out through the `if`/`else`'s result type.
			let block_result = self.func.blocks[case.block as usize]
				.as_ref()
				.unwrap()
				.result;
			if let StackResult::Value(n) = block_result {
				self.emit_value(n);
			}
		} else {
			// Two-phase, same reasoning as `emit_loop_param_updates`: push
			// every own-value first, *then* pop into locals in reverse. A
			// later slot's value can be an expression that reads an earlier
			// slot's own pre-update local (e.g. `acc += i; i += 1;`), so
			// every read must happen before any write.
			for (&value, _) in case.own_values.iter().zip(outputs) {
				if let StackResult::Value(v) = value {
					self.emit_value(v);
				}
			}
			for (&value, &phi) in case.own_values.iter().zip(outputs).rev() {
				// `StackResult::Never`: this arm's body diverges before
				// reaching the join (e.g. ends in `return`/`unreachable`) —
				// nothing was pushed above, so nothing to store.
				if matches!(value, StackResult::Value(_)) {
					let local = *self.node_to_local.get(&phi).unwrap();
					self.body.push(Instruction::LocalSet(local));
				}
			}
		}
	}

	// ── Depth computation ──────────────────────────────────────────────────────

	/// WASM `br` depth for a `break` targeting `target_block` from
	/// `current_block`.
	fn break_depth(&self, current: BlockIndex, target: BlockIndex) -> u32 {
		// Walk up the block tree. is_loop blocks cost 2 WASM levels (block + loop);
		// others cost 1. Add +1 when the target is_loop so we exit via the outer
		// `block` (break) rather than the inner `loop` (continue).
		let mut depth = 0u32;
		let mut idx = current;
		loop {
			let block = self.func.blocks[idx as usize].as_ref().unwrap();
			if idx == target {
				if block.is_loop() {
					depth += 1;
				}
				return depth;
			}
			depth += if block.is_loop() { 2 } else { 1 };
			idx = block.parent.unwrap();
		}
	}

	/// WASM `br` depth for a `continue` (branch to loop header) from
	/// `current_block`.
	fn continue_depth(&self, current: BlockIndex, target: BlockIndex) -> u32 {
		// break_depth targets the outer block; subtract 1 to reach the inner loop.
		self.break_depth(current, target) - 1
	}

	// ── Index resolution ───────────────────────────────────────────────────────

	fn emit_call(&mut self, callee_node: DataNodeIndex, callee_sig: u32) {
		match &self.func.data_nodes[callee_node as usize].kind {
			DataNodeKind::FunctionRef { id } => {
				self.body.push(Instruction::Call(*id));
			}
			_ => {
				self.emit_value(callee_node);
				self.body.push(Instruction::CallIndirectSym {
					mir_sig_index: callee_sig,
				});
			}
		}
	}

	fn stack_result_block_type(&self, result: StackResult) -> BlockType {
		match result {
			StackResult::Value(node) => {
				let ty =
					self.func.data_nodes[node as usize].kind.unwrap_scalar();
				BlockType::Value(ty)
			}
			_ => BlockType::Empty,
		}
	}
}

/// Appends `block` to `blocks` unless it's already present. Each node is
/// read from only a handful of blocks at most, so a linear scan beats a
/// `HashSet` here — no hashing, and no allocation at all until a node is
/// actually read from a second block.
fn push_unique_block(blocks: &mut Vec<BlockIndex>, block: BlockIndex) {
	if !blocks.contains(&block) {
		blocks.push(block);
	}
}
