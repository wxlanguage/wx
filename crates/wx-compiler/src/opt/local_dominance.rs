//! Debug-only "definite assignment" check over the scheduler's just-emitted,
//! pre-coalescing instruction stream: every `LocalGet` of a spill slot must
//! be reachable only via control-flow paths that already passed through a
//! `LocalSet`/`LocalTee` of that same slot.
//!
//! Pre-coalescing, `alloc_local` (`opt::scheduler::Scheduler`) never reuses
//! an index — every slot `>= params_count` is allocated exactly once and,
//! for its entire lifetime, represents a single logical value (one
//! `DataNode`, phi, or loop param), even though a phi/loop-param slot may
//! legitimately be written from more than one site (once per incoming
//! branch). So this is exactly the "definitely assigned" property, and it
//! is exactly what `wasm::coalesce_locals` assumes when it later reuses
//! slots by textual live range: two slots' `[first_write, last_read]`
//! windows not overlapping is only a valid reason to share a physical local
//! if `first_write` really is reached before every read it claims to
//! dominate. Checking that here, before coalescing, matters because
//! coalescing can otherwise mask a violation behind slot aliasing — turning
//! what would be a silently wrong float into an immediate panic naming the
//! offending slot and position.
//!
//! This module exists purely as a debug safety net for the
//! `compute_value_placement`/`emit_block` hoisting logic in
//! `opt::scheduler` (see that module for the actual bug this is guarding
//! against). It is deliberately kept separate and self-contained so it can
//! be deleted wholesale without touching `scheduler.rs` if it's ever judged
//! not worth its keep.

use crate::opt::{DataNodeIndex, Function};
use crate::wasm::Instruction;

/// Debug-only check that every *pure* `DataNode`'s operands have a strictly
/// lower `DataNodeIndex` than the node itself. Two things in
/// `opt::scheduler::Scheduler::compute_value_placement` rest on this: the
/// backward propagation sweep is only a complete single pass if every
/// operand is still ahead of it (not yet visited) when its consumer is
/// processed, and the pending-queue tie-breaking in `emit_block` only
/// preserves operand-before-consumer ordering at equal statement indices
/// because of this same fact. Both only ever traverse from a *pure* node to
/// its operands (`for_each_operand`'s doc comment: the sweep skips impure
/// nodes entirely before ever calling it) — so that's the exact scope this
/// checks, not "every edge in the graph."
///
/// That scoping isn't cosmetic: restricted to pure consumers only, the
/// invariant holds today by construction of `Builder::node`'s single-pass,
/// bottom-up interning (every operand must already exist, by handle, before
/// it can be referenced) — every substitution path there either returns an
/// already-existing operand of the node being built or a freshly-interned
/// node (always the new maximum index), and both keep it intact. Checked
/// against *every* edge instead, it's simply false: `LoopParam`'s `after`
/// field necessarily has a *higher* index than the `LoopParam` node itself
/// (the placeholder has to exist before the loop body that computes its
/// updated value can reference it — patched in later by
/// `Function::patch_loop_param`), which is exactly why `LoopParam` is
/// impure and excluded from the sweep in the first place, not a bug to flag
/// here.
///
/// `DataNode::uses` is already exactly the reverse of "operand of" — every
/// node that reads a given node — populated as each node is constructed
/// (`Function::register_uses`), so this reduces to one assertion per
/// existing edge whose *consumer* is pure, no separate operand walk needed:
/// O(edges), not a new traversal shape to keep in sync with
/// `DataNodeKind`'s variants.
///
/// This exists as insurance against a future optimization pass (constant
/// folding beyond integers, GVN, index-reusing DCE) quietly breaking the
/// invariant, the same way `compute_block_depths`'s now-removed
/// monotonic-parent-index assumption turned out to be violated by
/// `Switch`'s synthetic wrapper blocks — a structurally identical kind of
/// unverified cross-cutting ordering assumption, just for `BlockIndex`
/// rather than `DataNodeIndex`.
pub fn verify_operand_index_ordering(func: &Function) {
	for (n, node) in func.data_nodes.iter().enumerate() {
		let n = n as DataNodeIndex;
		for &user in &node.uses {
			if !func.data_nodes[user as usize].kind.is_pure() {
				continue;
			}
			assert!(
				n < user,
				"scheduler: pure DataNode {user} uses DataNode {n}, which \
				 does not have a strictly lower index — \
				 compute_value_placement's backward sweep and emit_block's \
				 tie-breaking both assume every operand of a pure node has \
				 a lower DataNodeIndex than that node"
			);
		}
	}
}

/// Which structured-control-flow construct opened a [`Frame`] — determines
/// how [`Frame::exits`]/[`Frame::then_fallthrough`] get merged at its
/// matching `End` in [`verify_local_dominance`].
#[derive(PartialEq)]
enum FrameKind {
	Block,
	Loop,
	If,
}

/// One currently-open `Block`/`Loop`/`If` while walking the flat instruction
/// stream in [`verify_local_dominance`].
struct Frame {
	kind: FrameKind,
	/// `set`/reachability *before* this frame's first instruction — the
	/// implicit "condition false, skip the body" path for an `If` with no
	/// `Else`, and the state `Else` restores to before walking the `else`
	/// arm.
	entry_set: Vec<bool>,
	entry_reachable: bool,
	/// Snapshot of `set`/reachability at each `Br`/`BrIf`/`BrTable` edge
	/// that exits *this* frame (i.e. targets it while it is a `Block` or
	/// `If`). Never populated for a `Loop` frame — per WASM semantics a
	/// branch targeting a `loop` jumps to its top (a backedge), not past
	/// its `End`, so it is not a merge input for whatever follows.
	exits: Vec<Vec<bool>>,
	/// Set at `Else`: the `then` arm's state on falling through to `Else`.
	/// `None` until (or unless) `Else` is seen.
	then_fallthrough: Option<(Vec<bool>, bool)>,
}

/// Elementwise AND — "definitely set" only if set on every merged path.
fn intersect(a: &[bool], b: &[bool]) -> Vec<bool> {
	a.iter().zip(b).map(|(&x, &y)| x && y).collect()
}

/// Records that reaching a `Br`/`BrIf`/`BrTable` at depth `depth` (from the
/// innermost currently-open frame) carries `set` out through whichever
/// frame that depth resolves to — unless that frame is a `Loop` (a branch
/// to a loop frame is a backedge, not an exit; see [`Frame::exits`]), or
/// `depth` resolves past every open frame (a branch to the function's own
/// implicit outermost block, which exits the function like `Return` and is
/// not a merge input for any tracked frame).
fn record_exit(
	frames: &mut [Frame],
	depth: u32,
	set: &[bool],
	reachable: bool,
) {
	if !reachable {
		return;
	}
	let depth = depth as usize;
	if depth >= frames.len() {
		return;
	}
	let idx = frames.len() - 1 - depth;
	if frames[idx].kind != FrameKind::Loop {
		frames[idx].exits.push(set.to_vec());
	}
}

/// Merges `fallthrough` (this frame's own state at `End`, if reachable) with
/// every recorded jump-exit, intersecting wherever more than one path is
/// live. Returns `None` if nothing reaches past this frame at all (pure
/// dead code following it).
fn merge_exits(
	fallthrough: Option<Vec<bool>>,
	exits: &[Vec<bool>],
) -> Option<Vec<bool>> {
	let mut merged = fallthrough;
	for exit in exits {
		merged = Some(match merged {
			None => exit.clone(),
			Some(m) => intersect(&m, exit),
		});
	}
	merged
}

/// Entry point — see the module doc comment for what this checks and why.
/// `body`/`br_table_depths` are the scheduler's output *before*
/// `wasm::coalesce_locals` runs; `n_locals` is `sched.locals.len()`.
pub fn verify_local_dominance(
	body: &[Instruction],
	n_locals: usize,
	params_count: usize,
	br_table_depths: &[u32],
) {
	let mut set = vec![false; n_locals];
	set[..params_count].fill(true);
	let mut reachable = true;
	let mut frames: Vec<Frame> = Vec::new();

	for (i, instr) in body.iter().enumerate() {
		match instr {
			Instruction::LocalGet(s) => {
				if reachable {
					assert!(
						set[*s as usize],
						"scheduler: local {s} read at body[{i}] without a \
						 dominating set on every reaching path — \
						 coalesce_locals assumes this holds and would \
						 silently alias this slot with an unrelated value"
					);
				}
			}
			// `local.tee` writes the slot and pushes the value back onto
			// the WASM operand stack — it never reads the slot's *prior*
			// contents, so (unlike LocalGet above) it is purely a
			// definition site, exactly like LocalSet.
			Instruction::LocalSet(s) | Instruction::LocalTee(s) => {
				if reachable {
					set[*s as usize] = true;
				}
			}
			Instruction::Block { .. } | Instruction::Loop { .. } => {
				frames.push(Frame {
					kind: if matches!(instr, Instruction::Loop { .. }) {
						FrameKind::Loop
					} else {
						FrameKind::Block
					},
					entry_set: set.clone(),
					entry_reachable: reachable,
					exits: Vec::new(),
					then_fallthrough: None,
				});
			}
			Instruction::If { .. } => {
				frames.push(Frame {
					kind: FrameKind::If,
					entry_set: set.clone(),
					entry_reachable: reachable,
					exits: Vec::new(),
					then_fallthrough: None,
				});
			}
			Instruction::Else => {
				let frame = frames.last_mut().unwrap();
				frame.then_fallthrough = Some((set.clone(), reachable));
				set.clone_from(&frame.entry_set);
				reachable = frame.entry_reachable;
			}
			Instruction::Br(depth) => {
				record_exit(&mut frames, *depth, &set, reachable);
				reachable = false;
			}
			// Unlike `Br`, execution continues past a `br_if` when the
			// condition is false — `reachable` (and `set`) carry on
			// unchanged for the fallthrough path, in addition to the
			// exit snapshot recorded for the taken-branch path.
			Instruction::BrIf(depth) => {
				record_exit(&mut frames, *depth, &set, reachable);
			}
			Instruction::BrTable { start, len } => {
				let depths =
					&br_table_depths[*start as usize..(*start + *len) as usize];
				for &d in depths {
					record_exit(&mut frames, d, &set, reachable);
				}
				reachable = false;
			}
			Instruction::Return | Instruction::Unreachable => {
				reachable = false;
			}
			Instruction::End => {
				let frame = frames.pop().expect(
					"End with no matching Block/Loop/If — body is malformed",
				);
				match frame.kind {
					// A branch targeting a Loop frame is a backedge (jumps
					// to the loop's own top), never an exit past this End —
					// `frame.exits` is always empty. Whatever `set`/
					// `reachable` accumulated by falling through the body
					// is exactly the state after End; nothing to merge.
					FrameKind::Loop => {}
					FrameKind::Block => {
						let fallthrough = reachable.then(|| set.clone());
						match merge_exits(fallthrough, &frame.exits) {
							Some(m) => {
								set = m;
								reachable = true;
							}
							None => reachable = false,
						}
					}
					FrameKind::If => {
						// The `then` arm's fallthrough is either what
						// `Else` snapshotted, or (no `Else`) the frame's
						// own entry state carried at the frame's own
						// entry reachability — the implicit "condition
						// false" path per `emit_control`'s own no-else
						// handling, which is only actually reachable if
						// the `If` itself was.
						let (then_set, then_reachable) =
							frame.then_fallthrough.clone().unwrap_or((
								frame.entry_set.clone(),
								frame.entry_reachable,
							));
						let mut merged = then_reachable.then_some(then_set);
						if reachable {
							merged = Some(match merged {
								None => set.clone(),
								Some(m) => intersect(&m, &set),
							});
						}
						match merge_exits(merged, &frame.exits) {
							Some(m) => {
								set = m;
								reachable = true;
							}
							None => reachable = false,
						}
					}
				}
			}
			// Every remaining instruction neither reads nor writes a local
			// and does not affect structured control flow — deliberately
			// listed exhaustively (no wildcard) so a future addition to
			// `Instruction` (e.g. `br_on_cast` if/when WasmGC support
			// lands) fails to compile here instead of silently becoming a
			// no-op that this verifier can no longer see through.
			#[rustfmt::skip]
			Instruction::I32Const(_) | Instruction::I64Const(_)
			| Instruction::F32Const(_) | Instruction::F64Const(_)
			| Instruction::GlobalGet(_) | Instruction::GlobalSet(_)
			| Instruction::I32Add | Instruction::I32Sub | Instruction::I32Mul
			| Instruction::I32DivS | Instruction::I32DivU
			| Instruction::I32RemS | Instruction::I32RemU
			| Instruction::I32And | Instruction::I32Or | Instruction::I32Xor
			| Instruction::I32Shl | Instruction::I32ShrS | Instruction::I32ShrU
			| Instruction::I32Eqz | Instruction::I32Eq | Instruction::I32Ne
			| Instruction::I32LtS | Instruction::I32LtU
			| Instruction::I32LeS | Instruction::I32LeU
			| Instruction::I32GtS | Instruction::I32GtU
			| Instruction::I32GeS | Instruction::I32GeU
			| Instruction::I32Clz | Instruction::I32Ctz
			| Instruction::I64Add | Instruction::I64Sub | Instruction::I64Mul
			| Instruction::I64DivS | Instruction::I64DivU
			| Instruction::I64RemS | Instruction::I64RemU
			| Instruction::I64And | Instruction::I64Or | Instruction::I64Xor
			| Instruction::I64Shl | Instruction::I64ShrS | Instruction::I64ShrU
			| Instruction::I64Eqz | Instruction::I64Eq | Instruction::I64Ne
			| Instruction::I64LtS | Instruction::I64LtU
			| Instruction::I64LeS | Instruction::I64LeU
			| Instruction::I64GtS | Instruction::I64GtU
			| Instruction::I64GeS | Instruction::I64GeU
			| Instruction::F32Add | Instruction::F32Sub | Instruction::F32Mul
			| Instruction::F32Div | Instruction::F32Neg | Instruction::F32Sqrt
			| Instruction::F32Abs | Instruction::F32Floor
			| Instruction::F32Ceil | Instruction::F32Trunc
			| Instruction::F32Nearest | Instruction::F32Min
			| Instruction::F32Max | Instruction::F32Copysign
			| Instruction::F64Add | Instruction::F64Sub | Instruction::F64Mul
			| Instruction::F64Div | Instruction::F64Neg | Instruction::F64Sqrt
			| Instruction::F64Abs | Instruction::F64Floor
			| Instruction::F64Ceil | Instruction::F64Trunc
			| Instruction::F64Nearest | Instruction::F64Min
			| Instruction::F64Max | Instruction::F64Copysign
			| Instruction::F32Eq | Instruction::F32Ne | Instruction::F32Lt
			| Instruction::F32Le | Instruction::F32Gt | Instruction::F32Ge
			| Instruction::F64Eq | Instruction::F64Ne | Instruction::F64Lt
			| Instruction::F64Le | Instruction::F64Gt | Instruction::F64Ge
			| Instruction::Drop
			| Instruction::Call(_) | Instruction::CallIndirectSym { .. }
			| Instruction::MemorySize(_) | Instruction::MemoryGrow(_)
			| Instruction::MemoryFill(_) | Instruction::MemoryCopy { .. }
			| Instruction::MemoryIndex { .. }
			| Instruction::I32Load8S(_) | Instruction::I32Load8U(_)
			| Instruction::I32Load16S(_) | Instruction::I32Load16U(_)
			| Instruction::I32Load(_) | Instruction::I64Load(_)
			| Instruction::F32Load(_) | Instruction::F64Load(_)
			| Instruction::I32Store8(_) | Instruction::I32Store16(_)
			| Instruction::I32Store(_) | Instruction::I64Store(_)
			| Instruction::F32Store(_) | Instruction::F64Store(_)
			| Instruction::I64ExtendI32S | Instruction::I64ExtendI32U
			| Instruction::I32WrapI64
			| Instruction::F32ConvertI32S | Instruction::F32ConvertI32U
			| Instruction::F32ConvertI64S | Instruction::F32ConvertI64U
			| Instruction::F64ConvertI32S | Instruction::F64ConvertI32U
			| Instruction::F64ConvertI64S | Instruction::F64ConvertI64U
			| Instruction::I32TruncF32S | Instruction::I32TruncF32U
			| Instruction::I32TruncF64S | Instruction::I32TruncF64U
			| Instruction::I64TruncF32S | Instruction::I64TruncF32U
			| Instruction::I64TruncF64S | Instruction::I64TruncF64U
			| Instruction::F64PromoteF32 | Instruction::F32DemoteF64
			| Instruction::I32ReinterpretF32 | Instruction::F32ReinterpretI32
			| Instruction::I64ReinterpretF64 | Instruction::F64ReinterpretI64
			| Instruction::Nop
			| Instruction::FunctionPointer(_)
			| Instruction::DataSectionEnd { .. }
			| Instruction::StaticDataPointer { .. } => {}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn test_func(uses: Vec<Vec<DataNodeIndex>>) -> Function {
		let mut func =
			Function::new(crate::ast::DefIdGenerator::new().generate(), 0);
		func.data_nodes = uses
			.into_iter()
			.map(|uses| crate::opt::DataNode {
				// The concrete kind doesn't matter for this check — only
				// `uses` (the reverse operand edges) is inspected.
				kind: crate::opt::DataNodeKind::Int {
					value: 0,
					ty: crate::wasm::ScalarType::I32,
				},
				uses,
			})
			.collect();
		func
	}

	/// Every operand strictly precedes its consumer — the ordinary,
	/// well-formed case.
	#[test]
	fn well_ordered_does_not_panic() {
		// node 0 used by node 1; node 1 used by node 2; node 2 unused.
		let func = test_func(vec![vec![1], vec![2], vec![]]);
		verify_operand_index_ordering(&func);
	}

	/// Node 1 is recorded as a "use" of node 2 — a consumer with a *lower*
	/// index than its own operand, which the backward propagation sweep in
	/// `compute_value_placement` cannot handle correctly.
	#[test]
	#[should_panic(expected = "does not have a strictly lower index")]
	fn operand_after_consumer_panics() {
		let func = test_func(vec![vec![], vec![], vec![1]]);
		verify_operand_index_ordering(&func);
	}

	/// A `LoopParam`'s `after` field legitimately has a *higher* index than
	/// the `LoopParam` node itself — the placeholder must exist before the
	/// loop body that computes its updated value can reference it. Since
	/// `LoopParam` is impure, this must not be flagged (this is the exact
	/// false positive `test_sched_loop_two_vars_writebacks` and friends hit
	/// before the consumer-purity filter was added).
	#[test]
	fn loop_param_after_edge_does_not_panic() {
		let mut func =
			Function::new(crate::ast::DefIdGenerator::new().generate(), 0);
		// node 0: LoopParam, before=constant (unused here), after=node 1.
		// node 1: some pure expression computed inside the loop body,
		// created *after* node 0's placeholder — records "node 0 is used
		// by node 1" via `patch_loop_param`, i.e. an operand (0) with a
		// *higher* index than what it feeds into via `after`.
		func.data_nodes = vec![
			crate::opt::DataNode {
				kind: crate::opt::DataNodeKind::LoopParam {
					block_index: 0,
					before: 0,
					after: 1,
					ty: crate::wasm::ScalarType::I32,
				},
				uses: vec![1],
			},
			crate::opt::DataNode {
				kind: crate::opt::DataNodeKind::Int {
					value: 1,
					ty: crate::wasm::ScalarType::I32,
				},
				uses: vec![0],
			},
		];
		verify_operand_index_ordering(&func);
	}

	fn run(body: &[Instruction], n_locals: usize, params_count: usize) {
		verify_local_dominance(body, n_locals, params_count, &[]);
	}

	fn panics(
		body: &[Instruction],
		n_locals: usize,
		params_count: usize,
	) -> bool {
		std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			run(body, n_locals, params_count)
		}))
		.is_err()
	}

	/// Both arms set the shared slot; reading it after the merge is sound.
	#[test]
	fn set_in_both_arms_does_not_panic() {
		let body = [
			Instruction::If {
				ty: crate::wasm::BlockType::Empty,
			},
			Instruction::LocalSet(1),
			Instruction::Else,
			Instruction::LocalSet(1),
			Instruction::End,
			Instruction::LocalGet(1),
		];
		assert!(!panics(&body, 2, 1));
	}

	/// No `Else`: the implicit skip-the-body path never sets the slot, so
	/// reading it afterward is unsound on that path.
	#[test]
	fn no_else_panics() {
		let body = [
			Instruction::If {
				ty: crate::wasm::BlockType::Empty,
			},
			Instruction::LocalSet(1),
			Instruction::End,
			Instruction::LocalGet(1),
		];
		assert!(panics(&body, 2, 1));
	}

	/// `br_if` breaks out of the loop *before* the set — the break path
	/// never runs the `LocalSet`, so reading the slot after the loop is
	/// unsound. This is the case the pre-fix `_ => {}` wildcard silently
	/// let through, since `BrIf` never recorded an exit snapshot at all.
	#[test]
	fn br_if_before_set_panics() {
		let body = [
			Instruction::Block {
				ty: crate::wasm::BlockType::Empty,
			},
			Instruction::Loop {
				ty: crate::wasm::BlockType::Empty,
			},
			Instruction::BrIf(1), // break, before the set
			Instruction::LocalSet(1),
			Instruction::Br(0), // continue
			Instruction::End,   // Loop
			Instruction::End,   // Block
			Instruction::LocalGet(1),
		];
		assert!(panics(&body, 2, 1));
	}

	/// Same shape, but the set happens *before* the conditional break — the
	/// only way out of the loop already carries the set with it, so reading
	/// the slot after the loop is sound.
	#[test]
	fn br_if_after_set_does_not_panic() {
		let body = [
			Instruction::Block {
				ty: crate::wasm::BlockType::Empty,
			},
			Instruction::Loop {
				ty: crate::wasm::BlockType::Empty,
			},
			Instruction::LocalSet(1),
			Instruction::BrIf(1), // break, after the set
			Instruction::Br(0),   // continue
			Instruction::End,     // Loop
			Instruction::End,     // Block
			Instruction::LocalGet(1),
		];
		assert!(!panics(&body, 2, 1));
	}

	/// An `If` with no `Else` nested inside dead code (after `Return`) must
	/// not resurrect reachability at its `End` — the implicit skip-path is
	/// only as reachable as the `If` itself was.
	#[test]
	fn dead_code_if_stays_dead() {
		let body = [
			Instruction::Return,
			Instruction::If {
				ty: crate::wasm::BlockType::Empty,
			},
			Instruction::LocalSet(1),
			Instruction::End,
			// Still dead code — must not panic even though `set[1]` is
			// false here, because this whole span is unreachable.
			Instruction::LocalGet(1),
		];
		assert!(!panics(&body, 2, 1));
	}
}
