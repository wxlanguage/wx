//! Data liveness for scheduler result capture and dead-pointer-load elimination.
//!
//! Computes the set of data nodes reachable from control-node sinks.

use crate::opt::{
	BlockIndex, ControlNode, DataNodeIndex, DataNodeKind, Function, StackResult,
};

pub struct DataLiveness {
	pub live: Vec<bool>,
}

impl DataLiveness {
	pub fn compute(func: &Function) -> Self {
		let mut live = vec![false; func.data_nodes.len()];
		let mut worklist = Vec::new();
		mark_block_roots(func, 0, &mut live, &mut worklist);
		while let Some(node) = worklist.pop() {
			mark_node_inputs_live(func, node, &mut live, &mut worklist);
		}
		DataLiveness { live }
	}

	pub fn is_live(&self, node: DataNodeIndex) -> bool {
		self.live[node as usize]
	}
}

fn mark_block_roots(
	func: &Function,
	block_idx: BlockIndex,
	live: &mut [bool],
	worklist: &mut Vec<DataNodeIndex>,
) {
	let block = func.blocks[block_idx as usize]
		.as_ref()
		.expect("block must exist");
	for stmt in &block.statements {
		match stmt {
			ControlNode::Trapping { op, .. } => {
				// Its operands are live even when its result is discarded: the
				// operation still executes and may trap.
				for operand in op.operands() {
					mark_node_live(operand, live, worklist);
				}
			}
			ControlNode::Return { value } => {
				mark_stack_result_live(*value, live, worklist);
			}
			ControlNode::GlobalSet { value, .. } => {
				mark_node_live(*value, live, worklist);
			}
			ControlNode::Call { callee, args, .. } => {
				mark_node_live(*callee, live, worklist);
				for &arg in args.iter() {
					mark_node_live(arg, live, worklist);
				}
			}
			ControlNode::IfElse {
				condition,
				then_block,
				else_block,
				outputs,
				result,
			} => {
				mark_node_live(*condition, live, worklist);
				for &output in outputs.iter() {
					mark_node_live(output, live, worklist);
				}
				if outputs.is_empty() {
					mark_stack_result_live(*result, live, worklist);
				}
				mark_block_roots(func, *then_block, live, worklist);
				if let Some(else_block) = else_block {
					mark_block_roots(func, *else_block, live, worklist);
				}
			}
			ControlNode::Switch {
				selector,
				cases,
				default,
				outputs,
				result,
			} => {
				mark_node_live(*selector, live, worklist);
				for &output in outputs.iter() {
					mark_node_live(output, live, worklist);
				}
				if outputs.is_empty() {
					mark_stack_result_live(*result, live, worklist);
				}
				// `own_values` need no separate marking here: each arm's raw
				// contribution to a divergent slot is either the slot's sole
				// `outputs` node directly, or was folded into it through a
				// chain of intermediate Phi nodes (`Phi::left`/`right`) that
				// `mark_node_inputs_live` already walks — so marking the
				// slot's one `outputs` entry live transitively covers every
				// arm's own value for that slot.
				for case in cases.iter().chain(default.iter()) {
					mark_block_roots(func, case.block, live, worklist);
				}
			}
			ControlNode::Loop { body, outputs, .. } => {
				for &output in outputs.iter() {
					mark_node_live(output, live, worklist);
				}
				mark_block_roots(func, *body, live, worklist);
			}
			ControlNode::BlockJoin {
				body,
				outputs,
				fallthrough_updates,
				fallthrough_value,
				..
			} => {
				for &output in outputs.iter() {
					mark_node_live(output, live, worklist);
				}
				// JoinParam results have no input edges. Root the raw value
				// written by this exit, just as for Break below, rather than
				// trying to find it through the joined result.
				mark_stack_result_live(*fallthrough_value, live, worklist);
				// fallthrough_updates' `current` values have no other path
				// to liveness: a JoinParam carries no back-reference to
				// what was committed into it (unlike Phi/LoopParam).
				for &(_, current) in fallthrough_updates.iter() {
					mark_node_live(current, live, worklist);
				}
				mark_block_roots(func, *body, live, worklist);
			}
			ControlNode::Break {
				value,
				carried_binding_updates,
				..
			} => {
				mark_stack_result_live(*value, live, worklist);
				for &(_, current) in carried_binding_updates.iter() {
					mark_node_live(current, live, worklist);
				}
			}
			ControlNode::Continue {
				carried_binding_updates,
				..
			} => {
				for &(_, current) in carried_binding_updates.iter() {
					mark_node_live(current, live, worklist);
				}
			}
			ControlNode::Unreachable => {}
			ControlNode::MemoryGrow { delta, .. } => {
				mark_node_live(*delta, live, worklist);
			}
			ControlNode::MemorySize { .. } | ControlNode::GlobalGet { .. } => {}
			ControlNode::PointerLoad { .. } => {}
			ControlNode::PointerStore { address, value, .. } => {
				mark_node_live(*address, live, worklist);
				mark_node_live(*value, live, worklist);
			}
			ControlNode::MemoryFill { dst, val, len, .. } => {
				mark_node_live(*dst, live, worklist);
				mark_node_live(*val, live, worklist);
				mark_node_live(*len, live, worklist);
			}
			ControlNode::MemoryCopy { dst, src, len, .. } => {
				mark_node_live(*dst, live, worklist);
				mark_node_live(*src, live, worklist);
				mark_node_live(*len, live, worklist);
			}
		}
	}
}

fn mark_stack_result_live(
	result: StackResult,
	live: &mut [bool],
	worklist: &mut Vec<DataNodeIndex>,
) {
	if let StackResult::Value(node) = result {
		mark_node_live(node, live, worklist);
	}
}

fn mark_node_live(
	node: DataNodeIndex,
	live: &mut [bool],
	worklist: &mut Vec<DataNodeIndex>,
) {
	let idx = node as usize;
	if live[idx] {
		return;
	}
	live[idx] = true;
	worklist.push(node);
}

fn mark_node_inputs_live(
	func: &Function,
	node: DataNodeIndex,
	live: &mut [bool],
	worklist: &mut Vec<DataNodeIndex>,
) {
	match &func.data_nodes[node as usize].kind {
		DataNodeKind::Add { left, right, .. }
		| DataNodeKind::Sub { left, right, .. }
		| DataNodeKind::Mul { left, right, .. }
		| DataNodeKind::Div { left, right, .. }
		| DataNodeKind::Min { left, right, .. }
		| DataNodeKind::Max { left, right, .. }
		| DataNodeKind::Copysign { left, right, .. }
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
		| DataNodeKind::GtEqU { left, right, .. }
		| DataNodeKind::Phi { left, right, .. } => {
			mark_node_live(*left, live, worklist);
			mark_node_live(*right, live, worklist);
		}
		DataNodeKind::Neg { operand, .. }
		| DataNodeKind::Sqrt { operand, .. }
		| DataNodeKind::Abs { operand, .. }
		| DataNodeKind::Floor { operand, .. }
		| DataNodeKind::Ceil { operand, .. }
		| DataNodeKind::Trunc { operand, .. }
		| DataNodeKind::Nearest { operand, .. }
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
		| DataNodeKind::F64PromoteF32 { operand }
		| DataNodeKind::F32DemoteF64 { operand }
		| DataNodeKind::I32ReinterpretF32 { operand }
		| DataNodeKind::F32ReinterpretI32 { operand }
		| DataNodeKind::I64ReinterpretF64 { operand }
		| DataNodeKind::F64ReinterpretI64 { operand }
		| DataNodeKind::AggregateGet {
			aggregate: operand, ..
		} => {
			mark_node_live(*operand, live, worklist);
		}
		DataNodeKind::Aggregate { values, .. } => {
			for &value in values.iter() {
				mark_node_live(value, live, worklist);
			}
		}
		DataNodeKind::LoopParam { before, after, .. } => {
			mark_node_live(*before, live, worklist);
			mark_node_live(*after, live, worklist);
		}
		DataNodeKind::CallResult { callee, args, .. } => {
			mark_node_live(*callee, live, worklist);
			for &arg in args.iter() {
				mark_node_live(arg, live, worklist);
			}
		}
		DataNodeKind::MemoryGrowResult { delta, .. } => {
			mark_node_live(*delta, live, worklist);
		}
		DataNodeKind::PointerLoadResult { address, .. } => {
			mark_node_live(*address, live, worklist);
		}
		DataNodeKind::Int { .. }
		| DataNodeKind::Float { .. }
		| DataNodeKind::Param { .. }
		| DataNodeKind::GlobalGetResult { .. }
		| DataNodeKind::TrappingResult { .. }
		| DataNodeKind::FunctionRef { .. }
		| DataNodeKind::StaticDataRef { .. }
		| DataNodeKind::DataEnd { .. }
		| DataNodeKind::MemoryIndex { .. }
		| DataNodeKind::MemorySizeResult { .. }
		| DataNodeKind::AggregateCallResult { .. }
		// JoinParam has no before/after (unlike LoopParam, above) and no
		// operand fields of its own.
		| DataNodeKind::JoinParam { .. } => {}
	}
}
