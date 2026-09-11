use crate::mir::{self, ExprKind};
use crate::opt::{
	Block, BlockIndex, BlockJoinData, ControlNode, DataNodeIndex, DataNodeKind,
	Function, LoopData, MemAccess, NodeType, ScalarType, StackResult,
	SwitchCase,
};

pub struct Builder<'mir> {
	mir: &'mir mir::MIR,
	/// The specific MIR function being lowered (stored to avoid indexing into
	/// `mir.functions` by index, which would be wrong for non-first functions).
	mir_func: &'mir mir::Function,
	func: Function,
	/// For each MIR scope index, whether some `Break` anywhere in the
	/// function targets it — computed once, up front, by
	/// `collect_break_targets`. Lets `build_block_expr` skip registering a
	/// real `Block`/`BlockJoinData` for the overwhelming majority of plain
	/// `{}` blocks that are never a break target, keeping that case exactly
	/// as cheap as it is today. A loop scope is always its own real `Block`
	/// regardless of this (see `build_loop`), so this only matters for
	/// plain blocks.
	break_targets: Box<[bool]>,
}

/// One `match` arm as built so far: its own scope/bindings plus what it
/// contributed to (parent-binding index, or the arm's own result if
/// `slot == parent_len` — see `Builder::build_switch`).
struct SwitchArmBuild {
	discriminant: Option<i64>,
	scope: BlockIndex,
	result: StackResult,
	bindings: Vec<Option<StackResult>>,
}

/// One arm's contribution to an aggregate-typed `Switch` join slot, as
/// decomposed by `Builder::merge_switch_slot` — either the arm's own
/// per-field values (reusing the `Box<[DataNodeIndex]>` `Builder::fields_of`
/// already returned, no re-wrapping), or a `Never`/`Unit` marker to
/// propagate to every field without materializing `field_count` copies of it.
enum PerArmSlot {
	Fields(Box<[DataNodeIndex]>),
	NoValue(StackResult),
}

impl<'mir> Builder<'mir> {
	/// Lower one MIR function into a sea-of-nodes `Function`.
	pub fn build(
		mir: &'mir mir::MIR,
		mir_func: &'mir mir::Function,
	) -> Function {
		let mut break_targets = vec![false; mir_func.scopes.len()];
		collect_break_targets(&mir_func.block, &mut break_targets);
		let mut b = Builder {
			mir,
			mir_func,
			func: Function::new(mir_func.id, mir_func.scopes.len()),
			break_targets: break_targets.into_boxed_slice(),
		};
		b.build_function();
		b.func
	}

	fn build_function(&mut self) {
		let mir_func = self.mir_func;
		let sig = &self.mir.signatures[usize::from(mir_func.signature_index)];

		// Seed data_bindings for the whole function at once — locals are
		// flat and function-wide (`mir::Function::locals`), so every local's
		// index is already its final position here. Params are genuinely
		// available from function entry, so they're seeded `Some`; every
		// other local starts `None` ("not yet declared on this build path")
		// and only becomes `Some` when its own `LocalSet` is actually built
		// — see `read_binding`'s doc comment for why this matters.
		let mut data_bindings: Vec<Option<StackResult>> =
			vec![None; mir_func.locals.len()];

		let params_count = sig.params_count;
		// `wasm_idx` tracks the flattened WASM local index: an aggregate param
		// occupies one slot per *scalar* it contains (see `mir::ScalarTable`,
		// which counts through nested aggregates and skips zero-sized fields),
		// a scalar param one slot each. Params are always the first
		// `params_count` entries of `mir_func.locals` — scope 0 (the root) is
		// always flattened first by construction, and TIR itself lists a
		// scope's params before its other locals.
		let mut wasm_idx = 0u32;
		for (i, local) in mir_func.locals[..params_count].iter().enumerate() {
			// A zero-sized param (e.g. a `Memory`-typed handle) occupies no
			// WASM param slot — see the matching case in `build_call`.
			data_bindings[i] = Some(match local.ty {
				mir::ValueType::Unit | mir::ValueType::Never => {
					StackResult::Unit
				}
				ty => StackResult::Value(
					self.build_param_value(ty, &mut wasm_idx),
				),
			});
		}

		self.func.blocks[0] = Some(Block {
			parent: None,
			statements: Vec::new(),
			result: StackResult::Never,
			loop_index: None,
			block_join_index: None,
		});

		let body_exprs = match &mir_func.block.kind {
			ExprKind::Block { expressions, .. } => expressions,
			_ => unreachable!("function body must be a Block"),
		};

		// MIR uses an implicit return: the last expression's value is returned
		// without an explicit `return` keyword. Capture it and emit a Return node.
		let mut last = StackResult::Unit;
		for expr in body_exprs.iter() {
			last = self.build_expr(0, &mut data_bindings, expr);
			if last == StackResult::Never {
				break;
			}
		}

		if last != StackResult::Never {
			let fn_result = self.func.blocks[0].as_ref().unwrap().result;
			let merged = self.merge_stack_results(fn_result, last);
			self.func.blocks[0].as_mut().unwrap().result = merged;
			self.push_stmt(0, ControlNode::Return { value: last });
		}
	}

	/// Build the data node for a function parameter of type `ty`, consuming
	/// one flattened WASM param slot per *scalar* it contains (`*wasm_idx`
	/// tracks the next free slot across the whole call). A scalar parameter is
	/// just one `Param` node; an aggregate parameter — possibly nested — is
	/// passed as a flattened run of scalar WASM params (mirroring how
	/// `wasm::flatten_type_to_scalars`/signature flattening lays out a call
	/// site's arguments), so this recurses to rebuild the matching (possibly
	/// nested) `Aggregate` literal from them, in the same pre-order
	/// `mir::ScalarTable` uses.
	fn build_param_value(
		&mut self,
		ty: mir::ValueType,
		wasm_idx: &mut u32,
	) -> DataNodeIndex {
		match ty {
			mir::ValueType::Aggregate { aggregate_index } => {
				let mir = self.mir;
				let agg = &mir.aggregate(aggregate_index);
				let fields: Box<[_]> = agg
					.fields
					.iter()
					.map(|field| self.build_param_value(field.ty, wasm_idx))
					.collect();
				self.node(DataNodeKind::Aggregate {
					fields,
					aggregate_index,
				})
			}
			_ => {
				let scalar_ty =
					ScalarType::try_from(ty).expect("param must be scalar");
				let node = self.node(DataNodeKind::Param {
					index: *wasm_idx,
					ty: scalar_ty,
				});
				*wasm_idx += 1;
				node
			}
		}
	}

	// ── Expression builder ────────────────────────────────────────────────────

	fn build_expr(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		expr: &mir::Expression,
	) -> StackResult {
		match &expr.kind {
			// ── Literals ──────────────────────────────────────────────────
			ExprKind::Int { value } => {
				let ty =
					ScalarType::try_from(expr.ty).expect("Int must be scalar");
				StackResult::Value(
					self.node(DataNodeKind::Int { value: *value, ty }),
				)
			}
			ExprKind::Float { value } => {
				let ty = ScalarType::try_from(expr.ty)
					.expect("Float must be scalar");
				let bits = match ty {
					ScalarType::F32 => (*value as f32).to_bits() as u64,
					_ => value.to_bits(),
				};
				StackResult::Value(self.node(DataNodeKind::Float { bits, ty }))
			}
			ExprKind::Bool { value } => {
				let node = self.node(DataNodeKind::Int {
					value: if *value { 1 } else { 0 },
					ty: ScalarType::I32,
				});
				StackResult::Value(node)
			}
			ExprKind::Noop => StackResult::Unit,

			// ── Locals ───────────────────────────────────────────────────
			ExprKind::LocalGet { local_index } => {
				self.read_binding(bindings, usize::from(*local_index))
			}
			ExprKind::LocalSet { local_index, value } => {
				let new_val = self.build_expr(block_idx, bindings, value);
				bindings[usize::from(*local_index)] = Some(new_val);
				StackResult::Unit
			}

			// ── Module-level state ────────────────────────────────────────
			ExprKind::Global { id } => {
				let ty =
					ScalarType::try_from(expr.ty).unwrap_or(ScalarType::I32);
				let node = self.node(DataNodeKind::GlobalGet { id: *id, ty });
				StackResult::Value(node)
			}
			ExprKind::GlobalSet { id, value } => {
				let val =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				self.push_stmt(
					block_idx,
					ControlNode::GlobalSet {
						id: *id,
						value: val,
					},
				);
				StackResult::Unit
			}

			// ── Constants / refs ─────────────────────────────────────────
			ExprKind::Function { id } => {
				let node = self.node(DataNodeKind::FunctionRef { id: *id });
				StackResult::Value(node)
			}
			ExprKind::StaticPointer { data_index } => {
				let node = self.node(DataNodeKind::StaticDataRef {
					data_index: *data_index,
					ty: ScalarType::try_from(expr.ty)
						.expect("static pointer must be scalar"),
				});
				StackResult::Value(node)
			}
			ExprKind::MemoryOffset { memory } => {
				let node = self.node(DataNodeKind::MemoryOffset {
					memory: *memory,
					ty: ScalarType::try_from(expr.ty)
						.expect("memory offset must be scalar"),
				});
				StackResult::Value(node)
			}
			ExprKind::MemoryIndex { memory } => {
				let node =
					self.node(DataNodeKind::MemoryIndex { memory: *memory });
				StackResult::Value(node)
			}
			ExprKind::MemorySize { memory } => {
				let result_node = self.node(DataNodeKind::MemorySizeResult {
					memory: *memory,
					ty: ScalarType::try_from(expr.ty)
						.expect("memory.size result must be scalar"),
				});
				self.push_stmt(
					block_idx,
					ControlNode::MemorySize {
						memory: *memory,
						result: result_node,
					},
				);
				StackResult::Value(result_node)
			}

			// ── Binary operators ──────────────────────────────────────────
			ExprKind::Add { left, right }
			| ExprKind::Sub { left, right }
			| ExprKind::Mul { left, right }
			| ExprKind::Div { left, right }
			| ExprKind::Rem { left, right }
			| ExprKind::And { left, right }
			| ExprKind::Or { left, right }
			| ExprKind::BitAnd { left, right }
			| ExprKind::BitOr { left, right }
			| ExprKind::BitXor { left, right }
			| ExprKind::LeftShift { left, right }
			| ExprKind::RightShift { left, right }
			| ExprKind::Min { left, right }
			| ExprKind::Max { left, right }
			| ExprKind::Copysign { left, right } => {
				self.build_binary(block_idx, bindings, expr, left, right)
			}

			// ── Comparisons ───────────────────────────────────────────────
			ExprKind::Eq { left, right }
			| ExprKind::NotEq { left, right }
			| ExprKind::Less { left, right }
			| ExprKind::LessEq { left, right }
			| ExprKind::Greater { left, right }
			| ExprKind::GreaterEq { left, right } => {
				self.build_cmp(block_idx, bindings, expr, left, right)
			}

			// ── Unary ─────────────────────────────────────────────────────
			ExprKind::Neg { value } => {
				let ty =
					ScalarType::try_from(expr.ty).expect("Neg must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(self.node(DataNodeKind::Neg { operand, ty }))
			}
			ExprKind::Sqrt { value } => {
				let ty =
					ScalarType::try_from(expr.ty).expect("Sqrt must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::Sqrt { operand, ty }),
				)
			}
			ExprKind::Abs { value } => {
				let ty =
					ScalarType::try_from(expr.ty).expect("Abs must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(self.node(DataNodeKind::Abs { operand, ty }))
			}
			ExprKind::Floor { value } => {
				let ty = ScalarType::try_from(expr.ty)
					.expect("Floor must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::Floor { operand, ty }),
				)
			}
			ExprKind::Ceil { value } => {
				let ty =
					ScalarType::try_from(expr.ty).expect("Ceil must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::Ceil { operand, ty }),
				)
			}
			ExprKind::Trunc { value } => {
				let ty = ScalarType::try_from(expr.ty)
					.expect("Trunc must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::Trunc { operand, ty }),
				)
			}
			ExprKind::Nearest { value } => {
				let ty = ScalarType::try_from(expr.ty)
					.expect("Nearest must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::Nearest { operand, ty }),
				)
			}
			ExprKind::BitNot { value } => {
				let ty = ScalarType::try_from(expr.ty)
					.expect("BitNot must be scalar");
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::BitNot { operand, ty }),
				)
			}
			ExprKind::Eqz { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(self.node(DataNodeKind::Eqz { operand }))
			}
			ExprKind::I64ExtendI32S { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I64ExtendI32S { operand }),
				)
			}
			ExprKind::I64ExtendI32U { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I64ExtendI32U { operand }),
				)
			}
			ExprKind::I32WrapI64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I32WrapI64 { operand }),
				)
			}
			ExprKind::F32ConvertI32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F32ConvertI32 { operand }),
				)
			}
			ExprKind::F32ConvertU32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F32ConvertU32 { operand }),
				)
			}
			ExprKind::F32ConvertI64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F32ConvertI64 { operand }),
				)
			}
			ExprKind::F32ConvertU64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F32ConvertU64 { operand }),
				)
			}
			ExprKind::F64ConvertI32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F64ConvertI32 { operand }),
				)
			}
			ExprKind::F64ConvertU32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F64ConvertU32 { operand }),
				)
			}
			ExprKind::F64ConvertI64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F64ConvertI64 { operand }),
				)
			}
			ExprKind::F64ConvertU64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F64ConvertU64 { operand }),
				)
			}
			ExprKind::I32TruncF32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I32TruncF32 { operand }),
				)
			}
			ExprKind::U32TruncF32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::U32TruncF32 { operand }),
				)
			}
			ExprKind::I32TruncF64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I32TruncF64 { operand }),
				)
			}
			ExprKind::U32TruncF64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::U32TruncF64 { operand }),
				)
			}
			ExprKind::I64TruncF32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I64TruncF32 { operand }),
				)
			}
			ExprKind::U64TruncF32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::U64TruncF32 { operand }),
				)
			}
			ExprKind::I64TruncF64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I64TruncF64 { operand }),
				)
			}
			ExprKind::U64TruncF64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::U64TruncF64 { operand }),
				)
			}
			ExprKind::F64PromoteF32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F64PromoteF32 { operand }),
				)
			}
			ExprKind::F32DemoteF64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F32DemoteF64 { operand }),
				)
			}
			ExprKind::I32ReinterpretF32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I32ReinterpretF32 { operand }),
				)
			}
			ExprKind::F32ReinterpretI32 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F32ReinterpretI32 { operand }),
				)
			}
			ExprKind::I64ReinterpretF64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::I64ReinterpretF64 { operand }),
				)
			}
			ExprKind::F64ReinterpretI64 { value } => {
				let operand =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				StackResult::Value(
					self.node(DataNodeKind::F64ReinterpretI64 { operand }),
				)
			}

			// ── Aggregates ────────────────────────────────────────────────
			ExprKind::Aggregate { values } => {
				let aggregate_index = match expr.ty {
					mir::ValueType::Aggregate { aggregate_index } => {
						aggregate_index
					}
					_ => {
						panic!("Aggregate expression must have Aggregate type")
					}
				};
				let fields: Box<[_]> = values
					.iter()
					.map(|v| {
						self.build_expr(block_idx, bindings, v).unwrap_value()
					})
					.collect();
				let node = self.node(DataNodeKind::Aggregate {
					fields,
					aggregate_index,
				});
				StackResult::Value(node)
			}
			ExprKind::AggregateGet {
				local_index,
				value_index,
			} => {
				let idx = usize::from(*local_index);
				let aggregate = self.read_binding(bindings, idx).unwrap_value();
				let aggregate_index = match self.func.data_nodes
					[aggregate as usize]
					.kind
					.node_type()
				{
					NodeType::Aggregate(i) => i,
					_ => panic!("AggregateGet on non-aggregate binding"),
				};
				let node = self.get_aggregate_field(
					aggregate,
					aggregate_index,
					*value_index,
				);
				StackResult::Value(node)
			}

			ExprKind::AggregateSet {
				local_index,
				value_index,
				value,
			} => {
				let new_val =
					self.build_expr(block_idx, bindings, value).unwrap_value();
				let idx = usize::from(*local_index);
				let old_aggregate =
					self.read_binding(bindings, idx).unwrap_value();
				let aggregate_index = match self.func.data_nodes
					[old_aggregate as usize]
					.kind
					.node_type()
				{
					NodeType::Aggregate(i) => i,
					_ => panic!("AggregateSet on non-aggregate binding"),
				};
				let n = self.mir.aggregate(aggregate_index).field_count();
				let fields: Box<[DataNodeIndex]> = (0..n as u32)
					.map(mir::PhysIndex::new)
					.map(|phys| {
						if phys == *value_index {
							new_val
						} else {
							self.get_aggregate_field(
								old_aggregate,
								aggregate_index,
								phys,
							)
						}
					})
					.collect();
				bindings[idx] = Some(StackResult::Value(self.node(
					DataNodeKind::Aggregate {
						fields,
						aggregate_index,
					},
				)));
				StackResult::Unit
			}

			// ── Control flow ──────────────────────────────────────────────
			ExprKind::Return { value } => {
				let result = match value {
					Some(v) => self.build_expr(block_idx, bindings, v),
					None => StackResult::Unit,
				};
				// Merge return value into function block result.
				let fn_result = self.func.blocks[0].as_ref().unwrap().result;
				let merged = self.merge_stack_results(fn_result, result);
				self.func.blocks[0].as_mut().unwrap().result = merged;
				self.push_stmt(
					block_idx,
					ControlNode::Return { value: result },
				);
				StackResult::Never
			}
			ExprKind::Drop { value } => {
				self.build_expr(block_idx, bindings, value);
				StackResult::Unit
			}
			ExprKind::Unreachable => {
				self.push_stmt(block_idx, ControlNode::Unreachable);
				StackResult::Never
			}

			ExprKind::Block {
				scope_index,
				expressions,
			} => self.build_block_expr(
				block_idx,
				bindings,
				*scope_index,
				expressions,
			),
			ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => self.build_if_else(
				block_idx,
				bindings,
				condition,
				then_block,
				else_block.as_deref(),
			),
			ExprKind::Switch {
				selector,
				cases,
				default,
			} => {
				if Self::should_use_br_table(selector.ty, cases) {
					self.build_switch(
						block_idx,
						bindings,
						selector,
						cases,
						default.as_deref(),
					)
				} else {
					self.build_switch_as_if_chain(
						block_idx,
						bindings,
						selector,
						cases,
						default.as_deref(),
					)
				}
			}
			ExprKind::Loop { scope_index, block } => {
				self.build_loop(block_idx, bindings, *scope_index, block)
			}
			ExprKind::Break { scope_index, value } => {
				let val = match value {
					Some(v) => self.build_expr(block_idx, bindings, v),
					None => StackResult::Unit,
				};
				let target = u32::from(*scope_index);
				// Captured *before* the merge below (which only concerns the
				// target's own trailing value) — this break's own current
				// contribution to the target's carried bindings, independent
				// of its break value. See `carried_binding_updates`.
				let carried_binding_updates =
					self.carried_binding_updates(target, bindings);
				// Return value unused here — merge_exit_value's only job at
				// a break site is its side effect (updating the target's
				// accumulated result and break_result_outputs); nothing
				// downstream of a Break needs its own merged value back.
				self.merge_exit_value(target, val);
				self.push_stmt(
					block_idx,
					ControlNode::Break {
						target,
						value: val,
						carried_binding_updates,
					},
				);
				StackResult::Never
			}
			ExprKind::Continue { scope_index } => {
				let target = u32::from(*scope_index);
				let carried_binding_updates =
					self.carried_binding_updates(target, bindings);
				self.push_stmt(
					block_idx,
					ControlNode::Continue {
						target,
						carried_binding_updates,
					},
				);
				StackResult::Never
			}

			// ── Calls ─────────────────────────────────────────────────────
			ExprKind::Call { callee, arguments } => {
				self.build_call(block_idx, bindings, callee, arguments, expr.ty)
			}

			// ── Memory ────────────────────────────────────────────────────
			ExprKind::PointerLoad {
				pointer,
				offset: base_offset,
				memory,
			} => {
				let address = self
					.build_expr(block_idx, bindings, pointer)
					.unwrap_value();
				match expr.ty {
					mir::ValueType::Aggregate { aggregate_index } => {
						StackResult::Value(self.build_aggregate_load(
							block_idx,
							address,
							*base_offset,
							aggregate_index,
							*memory,
						))
					}
					_ => {
						let access = MemAccess::from_mir(expr.ty);
						let result =
							self.node(DataNodeKind::PointerLoadResult {
								address,
								access,
							});
						self.push_stmt(
							block_idx,
							ControlNode::PointerLoad {
								address,
								offset: *base_offset,
								result,
								memory: *memory,
								access,
							},
						);
						StackResult::Value(result)
					}
				}
			}

			ExprKind::PointerStore {
				pointer,
				value,
				offset: base_offset,
				memory,
			} => {
				let address = self
					.build_expr(block_idx, bindings, pointer)
					.unwrap_value();
				match value.ty {
					mir::ValueType::Aggregate { aggregate_index } => {
						let value_node = self
							.build_expr(block_idx, bindings, value)
							.unwrap_value();
						self.emit_aggregate_store(
							block_idx,
							address,
							*base_offset,
							value_node,
							aggregate_index,
							*memory,
						);
					}
					_ => {
						let value_node = self
							.build_expr(block_idx, bindings, value)
							.unwrap_value();
						let access = MemAccess::from_mir(value.ty);
						self.push_stmt(
							block_idx,
							ControlNode::PointerStore {
								address,
								offset: *base_offset,
								value: value_node,
								memory: *memory,
								access,
							},
						);
					}
				}
				StackResult::Unit
			}

			ExprKind::MemoryGrow { memory, delta } => {
				let delta_node =
					self.build_expr(block_idx, bindings, delta).unwrap_value();
				let result_node = self.node(DataNodeKind::MemoryGrowResult {
					memory: *memory,
					delta: delta_node,
					ty: ScalarType::try_from(expr.ty)
						.expect("memory.grow result must be scalar"),
				});
				self.push_stmt(
					block_idx,
					ControlNode::MemoryGrow {
						memory: *memory,
						delta: delta_node,
						result: result_node,
					},
				);
				StackResult::Value(result_node)
			}
			ExprKind::MemoryFill {
				memory,
				dst,
				val,
				len,
			} => {
				let dst =
					self.build_expr(block_idx, bindings, dst).unwrap_value();
				let val =
					self.build_expr(block_idx, bindings, val).unwrap_value();
				let len =
					self.build_expr(block_idx, bindings, len).unwrap_value();
				self.push_stmt(
					block_idx,
					ControlNode::MemoryFill {
						memory: *memory,
						dst,
						val,
						len,
					},
				);
				StackResult::Unit
			}
			ExprKind::MemoryCopy {
				dst_memory,
				src_memory,
				dst,
				src,
				len,
			} => {
				let dst =
					self.build_expr(block_idx, bindings, dst).unwrap_value();
				let src =
					self.build_expr(block_idx, bindings, src).unwrap_value();
				let len =
					self.build_expr(block_idx, bindings, len).unwrap_value();
				self.push_stmt(
					block_idx,
					ControlNode::MemoryCopy {
						dst_memory: *dst_memory,
						src_memory: *src_memory,
						dst,
						src,
						len,
					},
				);
				StackResult::Unit
			}
		}
	}

	// ── Control-flow builders ─────────────────────────────────────────────────

	fn build_block_expr(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut [Option<StackResult>],
		scope_index: mir::ScopeIndex,
		expressions: &[mir::Expression],
	) -> StackResult {
		let scope_u32 = u32::from(scope_index);

		// Two reasons to take the transparent fast path, checked together:
		//
		// 1. No `break` anywhere in the function ever targets this scope, so
		//    registering a real `Block`/`BlockJoinData` for it would be pure
		//    overhead — the overwhelming majority of plain `{}` blocks.
		//
		// 2. `scope_u32` is already registered as *something else*. This
		//    happens because `mir::inlining::Rebaser` redirects an inlined
		//    callee's own root scope to the call site's scope (see its doc
		//    comment: a reference to the callee's scope `0` is rewritten to
		//    `root_scope`, i.e. wherever the call itself lived) — so an
		//    inlined call's dissolved wrapper can carry the *same*
		//    `scope_index` as an already-built ancestor (e.g. an enclosing
		//    loop's own body scope, if the call happens directly in a loop
		//    body). That's not a genuine second occurrence of a nested
		//    scope needing its own registration; it's fully dissolved into
		//    whatever it aliases, so it must be built exactly like an
		//    ordinary untargeted block — spliced into the *current*
		//    enclosing block (`block_idx`), never re-registered at
		//    `scope_u32`, which would silently clobber the real owner's
		//    entry (confirmed via `test_loop_param`: an inlined `i + 1`
		//    dissolving into the loop's own body scope otherwise overwrote
		//    the loop's `Block` with a fresh, non-loop one).
		if self.func.blocks[scope_u32 as usize].is_some()
			|| !self.break_targets[usize::from(scope_index)]
		{
			let mut child = bindings.to_vec();
			let result =
				self.build_block_exprs(block_idx, &mut child, expressions);
			// Write back mutations to parent locals.
			let parent_len = bindings.len();
			bindings[..parent_len].copy_from_slice(&child[..parent_len]);
			return result;
		}

		// Genuine break target — register a real Block + BlockJoinData
		// before building the body, mirroring build_loop's own setup: any
		// break discovered while building the body needs somewhere to
		// commit against immediately (see create_join_params's doc comment).
		let entry_placeholders = self.create_join_params(bindings, scope_u32);
		let join_index = self.func.push_block_join_data(BlockJoinData {
			break_result_outputs: Vec::new(),
			entry_placeholders: entry_placeholders.clone(),
			divergent_params: Vec::new(),
		});
		self.func.blocks[scope_u32 as usize] = Some(Block {
			parent: Some(block_idx),
			statements: Vec::new(),
			result: StackResult::Never,
			loop_index: None,
			block_join_index: Some(join_index),
		});

		let mut child = bindings.to_vec();
		let fallthrough_result =
			self.build_block_exprs(scope_u32, &mut child, expressions);

		// "Once more, for the fallthrough" — the same fold every break
		// already goes through (via merge_exit_value, inside the
		// ExprKind::Break arm), applied one final time for falling off the
		// end of the body.
		let merged_result =
			self.merge_exit_value(scope_u32, fallthrough_result);

		let parent_len = bindings.len();
		// Order matters: this call is what folds the fallthrough's own
		// contribution into divergent_params in the first place — must run
		// before the clone below, so the finalize loop sees the *complete*
		// union of every exit (every break already folded in as it was
		// built, plus this one). Same "union of all exits, not just one"
		// principle Phase 1 fixed for loops, applied natively here.
		let fallthrough_updates =
			self.carried_binding_updates(scope_u32, &child[..parent_len]);
		let divergent_params: Vec<DataNodeIndex> = self
			.func
			.block_join_data(scope_u32)
			.divergent_params
			.clone();
		let mut outputs = Vec::new();
		for i in 0..parent_len {
			self.finalize_block_join_binding(
				i,
				&entry_placeholders,
				&child,
				bindings,
				&mut outputs,
				&divergent_params,
			);
		}

		self.push_stmt(
			block_idx,
			ControlNode::BlockJoin {
				body: scope_u32,
				outputs: outputs.into_boxed_slice(),
				fallthrough_updates,
				fallthrough_value: fallthrough_result,
				result: merged_result,
			},
		);
		merged_result
	}

	fn build_if_else(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		condition_expr: &mir::Expression,
		then_expr: &mir::Expression,
		else_expr: Option<&mir::Expression>,
	) -> StackResult {
		let condition = self
			.build_expr(block_idx, bindings, condition_expr)
			.unwrap_value();

		let (then_scope, then_exprs) = Self::unwrap_block(then_expr);
		let mut then_bindings = bindings.clone();
		self.func.blocks[usize::from(then_scope)] = Some(Block {
			parent: Some(block_idx),
			statements: Vec::new(),
			result: StackResult::Never,
			loop_index: None,
			block_join_index: None,
		});
		let then_result = self.build_block_exprs(
			u32::from(then_scope),
			&mut then_bindings,
			then_exprs,
		);
		self.func.blocks[usize::from(then_scope)]
			.as_mut()
			.unwrap()
			.result = then_result;

		let (else_result, else_bindings, else_scope) = match else_expr {
			Some(e) => {
				let (scope, exprs) = Self::unwrap_block(e);
				let mut eb = bindings.clone();
				self.func.blocks[usize::from(scope)] = Some(Block {
					parent: Some(block_idx),
					statements: Vec::new(),
					result: StackResult::Never,
					loop_index: None,
					block_join_index: None,
				});
				let r =
					self.build_block_exprs(u32::from(scope), &mut eb, exprs);
				self.func.blocks[usize::from(scope)]
					.as_mut()
					.unwrap()
					.result = r;
				(r, eb, Some(u32::from(scope)))
			}
			None => (StackResult::Unit, bindings.clone(), None),
		};

		let parent_len = bindings.len();
		let mut outputs = Vec::new();
		let result = self.merge_branches(
			then_result,
			else_result,
			&then_bindings,
			&else_bindings,
			parent_len,
			bindings,
			&mut outputs,
		);

		self.push_stmt(
			block_idx,
			ControlNode::IfElse {
				condition,
				then_block: u32::from(then_scope),
				else_block: else_scope,
				outputs: outputs.into_boxed_slice(),
				result,
			},
		);
		result
	}

	/// Whether `cases` is dense enough to justify a WASM `br_table` jump
	/// table over a right-nested `br_if` comparison chain. `br_table`'s cost
	/// (both code size and, for a sparse range, wasted table entries that
	/// all point at the default) is proportional to the index range
	/// regardless of how many cases are actually populated, so a small case
	/// count or a wide/sparse range isn't worth it — those are built as a
	/// plain `IfElse` chain instead (`build_switch_as_if_chain`), which
	/// reuses `IfElse`'s existing depth/scheduling machinery unmodified.
	///
	/// Restricted to an `I32` selector: the dispatch shifts the selector by
	/// `-min` and truncates to `br_table`'s mandatory i32 index. For an I64
	/// selector, a genuinely out-of-range runtime value could truncate
	/// (wrap) into an in-range index and be misrouted to the wrong case
	/// instead of falling through to the default — I32 selectors can't
	/// overflow the shift, so this sidesteps the issue rather than adding a
	/// separate range-check-before-truncate path. This covers the
	/// overwhelming majority of real matches anyway (enums, `bool`, `char`,
	/// and ordinary `i32`/`u32` literals); I64 matches still compile
	/// correctly, just always via the if-chain.
	fn should_use_br_table(
		selector_ty: mir::ValueType,
		cases: &[(i64, mir::Expression)],
	) -> bool {
		if ScalarType::try_from(selector_ty) != Ok(ScalarType::I32) {
			return false;
		}
		if cases.len() < 3 {
			return false;
		}
		let min = cases.iter().map(|(d, _)| *d).min().unwrap();
		let max = cases.iter().map(|(d, _)| *d).max().unwrap();
		let range = max as i128 - min as i128 + 1;
		if range > 512 {
			return false;
		}
		(cases.len() as f64) / (range as f64) >= 0.5
	}

	/// Allocates a new `Block` beyond those pre-sized for MIR scopes — used
	/// for synthetic WASM-nesting-only blocks that don't correspond to a
	/// MIR scope, such as the "else if" containers
	/// `build_switch_as_if_chain` invents for cases beyond the first, or the
	/// depth-bookkeeping wrapper blocks `build_switch`'s `br_table` shape
	/// needs. A `Block` here is purely a scheduling container — it costs
	/// nothing at the WASM level by itself; only the `ControlNode`s that
	/// target it as a `then_block`/`else_block`/etc. produce real
	/// instructions — so allocating extra ones freely is cheap.
	fn push_synthetic_block(&mut self, parent: BlockIndex) -> BlockIndex {
		let idx = self.func.blocks.len() as BlockIndex;
		self.func.blocks.push(Some(Block {
			parent: Some(parent),
			statements: Vec::new(),
			result: StackResult::Never,
			loop_index: None,
			block_join_index: None,
		}));
		idx
	}

	/// Lowers a `match` that didn't qualify for `br_table` (see
	/// `should_use_br_table`) into a right-nested `IfElse` chain — the exact
	/// shape a hand-written `if x == 0 { .. } else if x == 1 { .. } else {
	/// .. }` would produce. The scrutinee is evaluated exactly once (it may
	/// have side effects) and its resulting `DataNodeIndex` is compared
	/// against each case's discriminant directly — no MIR round-trip needed
	/// since Opt values are referenced by index, not re-evaluated per use.
	///
	/// Built iteratively, case-by-case from the *last* case back to the
	/// first, rather than by recursing through the case list: a naive
	/// recursive descent would grow the Rust call stack (and clone the
	/// bindings vector) once per case, with nothing bounding that beyond the
	/// arm count itself — exactly the shape this sparse path is chosen for
	/// (a wide-but-sparse match can have many cases). Every case's `then`
	/// branch is a mutually exclusive alternative from the *same* starting
	/// point, so every one of them is built from the caller's original,
	/// still-unmodified `bindings` — only the final (case 0) merge writes
	/// into it; every earlier merge writes into a throwaway scratch buffer
	/// that becomes the next case's `else_bindings` going outward, mirroring
	/// how only the outermost frame's merge touched the real `bindings` in
	/// the old recursive version.
	fn build_switch_as_if_chain(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		selector_expr: &mir::Expression,
		cases: &[(i64, mir::Expression)],
		default_expr: Option<&mir::Expression>,
	) -> StackResult {
		// A match that's just `_ -> body` lowers to `Switch { cases: [],
		// default: Some(body) }` in MIR — there's no comparison to make at
		// all, so just build `body` directly with no branch. The scrutinee
		// is still evaluated once for its side effects, matching `Switch`'s
		// semantics elsewhere.
		if cases.is_empty() {
			self.build_expr(block_idx, bindings, selector_expr);
			return match default_expr {
				Some(body) => self.build_expr(block_idx, bindings, body),
				None => {
					self.push_stmt(block_idx, ControlNode::Unreachable);
					StackResult::Never
				}
			};
		}

		let selector = self
			.build_expr(block_idx, bindings, selector_expr)
			.unwrap_value();
		let selector_ty =
			self.func.data_nodes[selector as usize].kind.unwrap_scalar();

		// One container block per case: case `i`'s `IfElse` is pushed into
		// `containers[i]` (`containers[0]` is `block_idx` itself); case
		// `i`'s "else" side is `containers[i + 1]` (or, for the last case,
		// the default/unreachable base built below) — a plain forward loop,
		// no recursion needed just to allocate these.
		let mut containers: Vec<BlockIndex> = Vec::with_capacity(cases.len());
		containers.push(block_idx);
		for _ in 1..cases.len() {
			let parent = *containers.last().unwrap();
			containers.push(self.push_synthetic_block(parent));
		}
		let last_container = *containers.last().unwrap();

		// The base of the chain: the default arm's own scope (genuine
		// source content, no synthetic wrapping needed), or a synthetic
		// block holding a single `Unreachable` if there's no default (TIR
		// proved exhaustiveness without one).
		let (mut else_block, mut else_result, mut else_bindings) =
			match default_expr {
				Some(body) => {
					let (scope, exprs) = Self::unwrap_block(body);
					let mut scope_bindings = bindings.clone();
					self.func.blocks[usize::from(scope)] = Some(Block {
						parent: Some(last_container),
						statements: Vec::new(),
						result: StackResult::Never,
						loop_index: None,
						block_join_index: None,
					});
					let result = self.build_block_exprs(
						u32::from(scope),
						&mut scope_bindings,
						exprs,
					);
					self.func.blocks[usize::from(scope)]
						.as_mut()
						.unwrap()
						.result = result;
					(u32::from(scope), result, scope_bindings)
				}
				None => {
					let unreachable_block =
						self.push_synthetic_block(last_container);
					self.push_stmt(unreachable_block, ControlNode::Unreachable);
					(unreachable_block, StackResult::Never, bindings.clone())
				}
			};

		let parent_len = bindings.len();
		for i in (0..cases.len()).rev() {
			let (discriminant, case_body) = &cases[i];
			let container = containers[i];
			let (condition, then_scope, then_result, then_bindings) = self
				.build_if_chain_then_branch(
					container,
					bindings,
					selector,
					selector_ty,
					*discriminant,
					case_body,
				);

			let mut outputs = Vec::new();
			let result;
			if i == 0 {
				// The outermost level: merge directly into the caller's own
				// `bindings`, matching the old recursive version's single
				// depth-0 merge.
				result = self.merge_branches(
					then_result,
					else_result,
					&then_bindings,
					&else_bindings,
					parent_len,
					bindings,
					&mut outputs,
				);
			} else {
				let mut scratch: Vec<Option<StackResult>> =
					vec![None; parent_len];
				result = self.merge_branches(
					then_result,
					else_result,
					&then_bindings,
					&else_bindings,
					parent_len,
					&mut scratch,
					&mut outputs,
				);
				else_bindings = scratch;
			}

			self.push_stmt(
				container,
				ControlNode::IfElse {
					condition,
					then_block: then_scope,
					else_block: Some(else_block),
					outputs: outputs.into_boxed_slice(),
					result,
				},
			);

			else_block = container;
			else_result = result;
		}

		else_result
	}

	/// Builds one case's `if selector == discriminant { case_body }` — the
	/// "then" half of one if-chain level, shared by every iteration of
	/// `build_switch_as_if_chain`'s fold regardless of which buffer that
	/// iteration merges into.
	fn build_if_chain_then_branch(
		&mut self,
		container: BlockIndex,
		bindings: &[Option<StackResult>],
		selector: DataNodeIndex,
		selector_ty: ScalarType,
		discriminant: i64,
		case_body: &mir::Expression,
	) -> (
		DataNodeIndex,
		BlockIndex,
		StackResult,
		Vec<Option<StackResult>>,
	) {
		let const_node = self.node(DataNodeKind::Int {
			value: discriminant,
			ty: selector_ty,
		});
		let condition = self.node(DataNodeKind::Eq {
			left: selector,
			right: const_node,
			ty: selector_ty,
		});

		let (then_scope, then_exprs) = Self::unwrap_block(case_body);
		let mut then_bindings = bindings.to_vec();
		self.func.blocks[usize::from(then_scope)] = Some(Block {
			parent: Some(container),
			statements: Vec::new(),
			result: StackResult::Never,
			loop_index: None,
			block_join_index: None,
		});
		let then_result = self.build_block_exprs(
			u32::from(then_scope),
			&mut then_bindings,
			then_exprs,
		);
		self.func.blocks[usize::from(then_scope)]
			.as_mut()
			.unwrap()
			.result = then_result;

		(condition, u32::from(then_scope), then_result, then_bindings)
	}

	fn build_switch(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		selector_expr: &mir::Expression,
		mir_cases: &[(i64, mir::Expression)],
		default_expr: Option<&mir::Expression>,
	) -> StackResult {
		let selector = self
			.build_expr(block_idx, bindings, selector_expr)
			.unwrap_value();

		// `should_use_br_table` guarantees a real `br_table` shape here, not
		// a nested if/else emulation — so this builds `Block::parent` chains
		// that mirror the *actual* WASM nesting `emit_switch_br_table`
		// produces:
		//   block $after
		//     block $default
		//       block $case[N-1] ... block $case[0]
		//         <dispatch>
		//       end          <- case 0 body runs here, still inside $case[1]
		//       ...
		//     end            <- case N-1 body runs here, still inside $default
		//   end              <- default body runs here, still inside $after
		// Every wrapper closes *before* the content that logically "belongs"
		// to it runs, so nothing ever sits directly inside its own
		// same-numbered wrapper: case i's body sits one level further out,
		// inside `$case[i+1]` (or `$default` for the last case), and the
		// default arm's body sits inside `$after` directly (`$default`
		// itself, like every `$case`, only wraps the dispatch/cases below
		// it — got this backwards once already, see the default-arm branch
		// below). `push_synthetic_block` costs nothing at the WASM level
		// itself (see its doc comment) — this chain is purely bookkeeping
		// for `break_depth`/`continue_depth`'s ancestor walk, not a
		// reflection of anything actually emitted here. `default_block` is
		// always allocated (even with no `_` arm) since it's still a real
		// WASM block wrapping the dispatch + every case.
		let case_count = mir_cases.len();
		debug_assert!(
			case_count >= 3,
			"should_use_br_table guarantees at least 3 cases"
		);
		let after_block = self.push_synthetic_block(block_idx);
		let default_block = self.push_synthetic_block(after_block);
		let mut case_wasm_parent = vec![default_block; case_count];
		case_wasm_parent[case_count - 1] = after_block;
		// case_wasm_parent[case_count - 2] is already `default_block` — the
		// vec's fill value — since case `N-2` sits directly inside
		// `$case[N-1]`, whose own real parent *is* `$default` with no
		// synthetic hop needed in between.
		let mut wrapper_parent = default_block;
		for i in (0..case_count - 2).rev() {
			let wrapper = self.push_synthetic_block(wrapper_parent);
			case_wasm_parent[i] = wrapper;
			wrapper_parent = wrapper;
		}

		let mut arms: Vec<SwitchArmBuild> =
			Vec::with_capacity(case_count + default_expr.is_some() as usize);
		for (i, (discriminant, body)) in mir_cases.iter().enumerate() {
			arms.push(self.build_switch_arm(
				case_wasm_parent[i],
				bindings,
				Some(*discriminant),
				body,
			));
		}
		if let Some(body) = default_expr {
			// Unlike a real case, `emit_switch_br_table` closes `$default`
			// itself *before* emitting the default body (mirroring how
			// every `$case[i]` wrapper closes before case i's body runs) —
			// so the default body lands directly inside `$after`, one hop
			// further out than `after_block` itself represents. Its parent
			// is `block_idx` directly, not `after_block`.
			arms.push(self.build_switch_arm(block_idx, bindings, None, body));
		}
		debug_assert!(
			!arms.is_empty(),
			"TIR guarantees at least one match arm"
		);

		let parent_len = bindings.len();
		// One slot per parent binding, plus one more for each arm's own result.
		let total_slots = parent_len + 1;

		// The result slot is always populated — an arm's trailing value is
		// never "not yet declared" the way a binding slot can be.
		let slot_value =
			|arm: &SwitchArmBuild, slot: usize| -> Option<StackResult> {
				if slot < parent_len {
					arm.bindings[slot]
				} else {
					Some(arm.result)
				}
			};

		// Merge each slot across all arms via `merge_switch_slot`. A slot
		// contributes at most one real `Switch` output per divergent
		// *scalar*: nothing downstream inspects a Phi's `left`/`right`
		// for a Switch (the scheduler reads each arm's raw contribution
		// from `SwitchCase::own_values` instead), so aggregate-typed slots
		// are decomposed field-by-field rather than merged as one opaque
		// unit, and a slot with no real value (only `Never`/`Unit` across
		// arms) contributes no scalar at all — `outputs` and every arm's row
		// in `own_values` grow together, one entry per scalar, so the two
		// stay index-aligned regardless of how many scalars a slot expands
		// into.
		let mut outputs: Vec<DataNodeIndex> = Vec::new();
		let mut merged_per_slot: Vec<Option<StackResult>> =
			Vec::with_capacity(total_slots);
		let mut own_values: Vec<Vec<StackResult>> =
			vec![Vec::new(); arms.len()];

		for slot in 0..total_slots {
			let values: Vec<Option<StackResult>> =
				arms.iter().map(|arm| slot_value(arm, slot)).collect();
			let merged =
				self.merge_switch_slot(&values, &mut outputs, &mut own_values);
			merged_per_slot.push(merged);
		}

		bindings[..parent_len].copy_from_slice(&merged_per_slot[..parent_len]);
		let result = merged_per_slot[parent_len]
			.expect("the switch's own result slot is always populated");

		let mut switch_cases: Vec<SwitchCase> = arms
			.into_iter()
			.zip(own_values)
			.map(|(arm, own_values)| SwitchCase {
				discriminant: arm.discriminant,
				block: arm.scope,
				own_values: own_values.into_boxed_slice(),
			})
			.collect();

		// The default arm, if present, was pushed last — pop it back off so
		// `ControlNode::Switch.cases` holds only the real discriminant cases.
		let default = if default_expr.is_some() {
			switch_cases.pop()
		} else {
			None
		};

		self.push_stmt(
			block_idx,
			ControlNode::Switch {
				selector,
				cases: switch_cases.into_boxed_slice(),
				default,
				outputs: outputs.into_boxed_slice(),
				result,
			},
		);
		result
	}

	/// Merges one `Switch` join slot (an outer binding, or the arms' own
	/// result) across every arm's `values` (one `StackResult` per arm, same
	/// order as `arms`). A `Switch` output only ever needs a validly-typed
	/// placeholder node per genuinely divergent *scalar* — the
	/// scheduler reads each arm's real contribution from
	/// `SwitchCase::own_values`, never a Phi's `left`/`right` — so this
	/// decomposes an aggregate-typed slot field-by-field (recursively, for
	/// nested aggregates) instead of merging it as one opaque unit, and
	/// treats a slot whose arms differ only in `Never` vs `Unit` (no arm
	/// disagrees on a real value) as contributing no scalar at all. Every
	/// `outputs.push` here is paired with exactly one push into each arm's
	/// row of `own_values`, so the two always stay index-aligned no matter
	/// how many scalars a slot expands into or how many slots contribute
	/// none.
	fn merge_switch_slot(
		&mut self,
		values: &[Option<StackResult>],
		outputs: &mut Vec<DataNodeIndex>,
		own_values: &mut [Vec<StackResult>],
	) -> Option<StackResult> {
		// A slot that isn't `Some` in every arm is private to whichever
		// arm(s) actually declared it — since every local gets a distinct
		// flat index (no sharing between arms), a `None` here can only mean
		// "this arm never touches that local," not "unrelated arms
		// disagree." Nothing outside any arm could ever reference it, so it
		// never gets merged or output — it just stays `None`.
		if values.iter().any(|v| v.is_none()) {
			return None;
		}
		let values: Vec<StackResult> =
			values.iter().map(|v| v.unwrap()).collect();

		let first = values[0];
		if values[1..].iter().copied().all(|v| v == first) {
			return Some(first);
		}

		let Some(sample) = values.iter().copied().find_map(|v| match v {
			StackResult::Value(n) => Some(n),
			_ => None,
		}) else {
			// Every arm is `Never` or `Unit` (a mix of the two — a uniform
			// value would have taken the fast path above): no real value to
			// carry, so this slot contributes no scalar.
			return Some(StackResult::Unit);
		};

		match self.func.data_nodes[sample as usize].kind.node_type() {
			NodeType::Scalar(ty) => {
				let merged =
					match values.iter().copied().find_map(|v| match v {
						StackResult::Value(n) if n != sample => Some(n),
						_ => None,
					}) {
						Some(other) => self.node(DataNodeKind::Phi {
							left: sample,
							right: other,
							ty,
						}),
						// Every value-bearing arm agrees; only `Never`/`Unit`
						// arms vary, so there's no genuine value divergence.
						None => sample,
					};
				outputs.push(merged);
				for (arm_values, v) in
					own_values.iter_mut().zip(values.iter().copied())
				{
					arm_values.push(v);
				}
				Some(StackResult::Value(merged))
			}
			NodeType::Aggregate(aggregate_index) => {
				let field_count =
					self.mir.aggregate(aggregate_index).field_count();
				// Extract each value-bearing arm's fields exactly once (not
				// once per field below). A `Never`/`Unit` arm propagates
				// unchanged to every field — its body diverges before
				// producing this slot at all, so it has nothing to
				// contribute at any field either — without allocating
				// `field_count` copies of that marker to represent it.
				let per_arm: Vec<PerArmSlot> = values
					.iter()
					.copied()
					.map(|v| match v {
						StackResult::Value(n) => {
							PerArmSlot::Fields(self.fields_of(n))
						}
						other => PerArmSlot::NoValue(other),
					})
					.collect();

				let merged_fields: Box<[DataNodeIndex]> = (0..field_count)
					.map(|field| {
						// Every arm structurally owns this field (it's part
						// of the same aggregate type on every arm), so this
						// is always `Some` — never subject to the "private
						// to one arm" exclusion above.
						let field_values: Vec<Option<StackResult>> = per_arm
							.iter()
							.map(|slot| {
								Some(match slot {
									PerArmSlot::Fields(fields) => {
										StackResult::Value(fields[field])
									}
									PerArmSlot::NoValue(v) => *v,
								})
							})
							.collect();
						self.merge_switch_slot(
							&field_values,
							outputs,
							own_values,
						)
						.expect(
							"every arm structurally owns this field, so it's always Some",
						)
						.unwrap_value()
					})
					.collect();
				let agg = self.node(DataNodeKind::Aggregate {
					fields: merged_fields,
					aggregate_index,
				});
				Some(StackResult::Value(agg))
			}
		}
	}

	fn build_switch_arm(
		&mut self,
		parent_block: BlockIndex,
		parent_bindings: &[Option<StackResult>],
		discriminant: Option<i64>,
		body: &mir::Expression,
	) -> SwitchArmBuild {
		let (scope, exprs) = Self::unwrap_block(body);
		let mut arm_bindings = parent_bindings.to_vec();
		self.func.blocks[usize::from(scope)] = Some(Block {
			parent: Some(parent_block),
			statements: Vec::new(),
			result: StackResult::Never,
			loop_index: None,
			block_join_index: None,
		});
		let result =
			self.build_block_exprs(u32::from(scope), &mut arm_bindings, exprs);
		self.func.blocks[usize::from(scope)]
			.as_mut()
			.unwrap()
			.result = result;
		SwitchArmBuild {
			discriminant,
			scope: u32::from(scope),
			result,
			bindings: arm_bindings,
		}
	}

	fn build_loop(
		&mut self,
		parent_block: BlockIndex,
		bindings: &mut [Option<StackResult>],
		_scope_index: mir::ScopeIndex,
		body_expr: &mir::Expression,
	) -> StackResult {
		let (body_scope, body_exprs) = Self::unwrap_block(body_expr);
		let body_block = u32::from(body_scope);

		// Create loop-param placeholders for all parent bindings — one per
		// entry, so this is already the full function-wide length; no
		// further growth needed for the body scope's own locals (every
		// local, function-wide, already has a slot from function-build
		// start).
		let entry_placeholders = self.create_loop_params(bindings, body_block);
		let mut loop_bindings = entry_placeholders.clone();

		let loop_index = self.func.push_loop_data(LoopData {
			break_result_outputs: Vec::new(),
			entry_placeholders: entry_placeholders.clone(),
			divergent_params: Vec::new(),
		});
		self.func.blocks[body_block as usize] = Some(Block {
			parent: Some(parent_block),
			statements: Vec::new(),
			result: StackResult::Never,
			loop_index: Some(loop_index),
			block_join_index: None,
		});
		let body_fallthrough =
			self.build_block_exprs(body_block, &mut loop_bindings, body_exprs);
		// blocks[body_block].result accumulates the result type from all `break`
		// statements. Save it before overwriting with the body's fallthrough
		// result (which is always Unit/Never since loops exit via break, not
		// fallthrough).
		let break_result = self.func.blocks[body_block as usize]
			.as_ref()
			.unwrap()
			.result;
		self.func.blocks[body_block as usize]
			.as_mut()
			.unwrap()
			.result = body_fallthrough;

		// Patch loop params and collect outputs. `divergent_params` is
		// cloned up front (mirrors `entry_placeholders` itself, above) so it
		// can be passed down without re-borrowing `self.func` inside the loop.
		let mut outputs = Vec::new();
		let parent_len = bindings.len();
		let divergent_params: Vec<DataNodeIndex> =
			self.func.loop_data(body_block).divergent_params.clone();
		for i in 0..parent_len {
			self.patch_loop_binding(
				i,
				&entry_placeholders,
				&loop_bindings,
				bindings,
				&mut outputs,
				&divergent_params,
			);
		}

		self.push_stmt(
			parent_block,
			ControlNode::Loop {
				body: body_block,
				outputs: outputs.into_boxed_slice(),
				result: break_result,
			},
		);
		break_result
	}

	fn build_call(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		callee_expr: &mir::Expression,
		arguments: &[mir::Expression],
		result_ty: mir::ValueType,
	) -> StackResult {
		let callee_sig = match callee_expr.ty {
			mir::ValueType::Function { signature_index } => signature_index,
			_ => unreachable!(),
		};
		let callee = self
			.build_expr(block_idx, bindings, callee_expr)
			.unwrap_value();
		// Zero-sized arguments (e.g. a `Memory`-typed handle) carry no
		// runtime bits and occupy no WASM param slot (see
		// `wasm::flatten_type_to_scalars`'s `Unit`/`Never` case) — drop them
		// here to match, rather than materializing a nonexistent `Value`.
		let args: Box<[_]> = arguments
			.iter()
			.filter_map(|a| match self.build_expr(block_idx, bindings, a) {
				StackResult::Value(idx) => Some(idx),
				StackResult::Unit => None,
				StackResult::Never => panic!("expected Value, got Never"),
			})
			.collect();

		let result = match result_ty {
			mir::ValueType::Unit | mir::ValueType::Never => StackResult::Unit,
			mir::ValueType::Aggregate { aggregate_index } => {
				StackResult::Value(self.node(
					DataNodeKind::AggregateCallResult { aggregate_index },
				))
			}
			_ => {
				let ty = ScalarType::try_from(result_ty)
					.expect("scalar call result type");
				StackResult::Value(self.node(DataNodeKind::CallResult {
					callee,
					args: args.clone(),
					ty,
				}))
			}
		};

		self.push_stmt(
			block_idx,
			ControlNode::Call {
				callee,
				args,
				result,
				callee_sig,
			},
		);
		result
	}

	// ── Binding helpers ───────────────────────────────────────────────────────

	/// Create loop-param placeholders for every scalar / aggregate binding in
	/// `parent`. A `None` entry — this local hasn't actually been declared
	/// yet on this build path, e.g. a temp local only declared inside the
	/// loop body itself — passes straight through as `None`: no placeholder
	/// is minted for it, so it can never be mistaken for a genuinely
	/// loop-carried binding (see `read_binding`'s doc comment for why `None`
	/// must never be papered over here).
	fn create_loop_params(
		&mut self,
		parent: &[Option<StackResult>],
		block_index: BlockIndex,
	) -> Vec<Option<StackResult>> {
		let mut params = Vec::with_capacity(parent.len());
		for &binding in parent {
			let param = match binding {
				Some(StackResult::Value(node_id)) => {
					Some(
						match self.func.data_nodes[node_id as usize]
							.kind
							.node_type()
						{
							NodeType::Scalar(ty) => {
								let lp = self.func.push_loop_param(
									block_index,
									node_id,
									ty,
								);
								StackResult::Value(lp)
							}
							NodeType::Aggregate(aggregate_index) => {
								// One loop-param per WASM *value*, not per field —
								// a nested field spans several and a zero-sized
								// one spans none — then reassemble the shape.
								let scalars = self.scalars_of(node_id);
								let params: Vec<DataNodeIndex> = scalars
									.into_iter()
									.map(|value| {
										let ty = match self.func.data_nodes
											[value as usize]
											.kind
											.node_type()
										{
											NodeType::Scalar(ty) => ty,
											NodeType::Aggregate(_) => {
												unreachable!(
													"scalars_of yields only scalars"
												)
											}
										};
										self.func.push_loop_param(
											block_index,
											value,
											ty,
										)
									})
									.collect();
								let new_agg = self.aggregate_from_scalars(
									aggregate_index,
									&params,
								);
								StackResult::Value(new_agg)
							}
						},
					)
				}
				other => other,
			};
			params.push(param);
		}
		params
	}

	/// The block-join analogue of `create_loop_params`. Mints a stable
	/// `JoinParam` placeholder for every parent binding *before* the block's
	/// body is built, so any `break` targeting it — however deeply nested,
	/// discovered at an arbitrary point in the single top-to-bottom build —
	/// has something fixed to commit its own current value against
	/// immediately, without waiting to know the final divergent set.
	///
	/// Unlike `create_loop_params`, these placeholders are *not* fed into
	/// the block's own live bindings afterward (there is no back-edge, so no
	/// "current iteration's value" ambiguity to paper over — see
	/// `DataNodeKind::JoinParam`'s doc comment) — the caller
	/// (`build_block_expr`) builds the body against the ordinary
	/// `extend_bindings`-produced bindings, completely unrelated to this
	/// return value, which exists purely for commit-diffing and the final
	/// `outputs`/local identity.
	fn create_join_params(
		&mut self,
		parent: &[Option<StackResult>],
		block_index: BlockIndex,
	) -> Vec<Option<StackResult>> {
		let mut params = Vec::with_capacity(parent.len());
		for &binding in parent {
			let param = match binding {
				Some(StackResult::Value(node_id)) => {
					Some(
						match self.func.data_nodes[node_id as usize]
							.kind
							.node_type()
						{
							NodeType::Scalar(ty) => {
								let jp =
									self.func.push_join_param(block_index, ty);
								StackResult::Value(jp)
							}
							NodeType::Aggregate(aggregate_index) => {
								// One join-param per WASM *value*, not per field —
								// mirrors create_loop_params exactly.
								let scalars = self.scalars_of(node_id);
								let params: Vec<DataNodeIndex> = scalars
									.into_iter()
									.map(|value| {
										let ty = match self.func.data_nodes
											[value as usize]
											.kind
											.node_type()
										{
											NodeType::Scalar(ty) => ty,
											NodeType::Aggregate(_) => {
												unreachable!(
													"scalars_of yields only scalars"
												)
											}
										};
										self.func
											.push_join_param(block_index, ty)
									})
									.collect();
								let new_agg = self.aggregate_from_scalars(
									aggregate_index,
									&params,
								);
								StackResult::Value(new_agg)
							}
						},
					)
				}
				other => other,
			};
			params.push(param);
		}
		params
	}

	/// Patch loop params for binding `i` once the loop body is built.
	///
	/// `divergent_params` is the loop's running list (see
	/// `LoopData::divergent_params`) of scalar `LoopParam` nodes some
	/// `break`/`continue` inside the body already found to differ from the
	/// placeholder at its own point — independent of, and unioned with, what
	/// the fallthrough path alone concludes below. Without this union, a
	/// binding mutated only along a path that ends in an early exit (while
	/// the fallthrough happens to leave it unchanged, or never touches it at
	/// all) would be wrongly treated as never loop-carried, and the early
	/// exit's already-recorded commit would reference a WASM local that was
	/// never allocated.
	fn patch_loop_binding(
		&mut self,
		i: usize,
		entry_placeholders: &[Option<StackResult>],
		loop_final: &[Option<StackResult>],
		parent_bindings: &mut [Option<StackResult>],
		outputs: &mut Vec<DataNodeIndex>,
		divergent_params: &[DataNodeIndex],
	) {
		// `None` at `entry_placeholders[i]` means this local was never
		// declared before the loop began — e.g. a temp only declared inside
		// the loop body itself, never genuinely loop-carried — so there's
		// nothing to patch or track divergence for.
		let param = match entry_placeholders[i] {
			Some(StackResult::Value(n)) => n,
			_ => return,
		};
		let after = match loop_final[i] {
			Some(StackResult::Value(n)) => n,
			_ => return,
		};

		// If loop_final still holds the LoopParam (or the same aggregate wrapper)
		// that was installed at loop entry, the binding was never written on the
		// fallthrough path. That alone doesn't mean it's not loop-carried — some
		// break/continue inside may have recorded a genuinely different value at
		// its own point (see `divergent_params`'s doc comment) — so only take the
		// early-out (restore to the pre-loop value, skip patching, no output) when
		// nothing has flagged this param as divergent either.
		if param == after {
			let any_divergent =
				match self.func.data_nodes[param as usize].kind.node_type() {
					NodeType::Scalar(_) => divergent_params.contains(&param),
					NodeType::Aggregate(_) => self
						.scalars_of(param)
						.iter()
						.any(|s| divergent_params.contains(s)),
				};
			if !any_divergent {
				let before = match self.func.data_nodes[param as usize].kind {
					DataNodeKind::LoopParam { before, .. } => before,
					// Aggregate wrapper whose fields were all unmodified.
					_ => {
						// Restore the parent binding to whatever it was before the loop.
						// The original value was `entry_placeholders[i]`'s `before` field, but
						// for aggregates we just leave the binding as-is (it's already correct
						// since the aggregate node CSE-deduplicates to the pre-loop one).
						return;
					}
				};
				parent_bindings[i] = Some(StackResult::Value(before));
				return;
			}
			// Else fall through into the match below: `patch_loop_param(param,
			// after)` there is a no-op (before == after already), but the
			// `divergent_params` check in each arm still forces the right
			// scalars into `outputs`.
		}

		match self.func.data_nodes[param as usize].kind.node_type() {
			NodeType::Scalar(_) => {
				self.func.patch_loop_param(param, after);
				// Expose as output if the binding was actually mutated on the
				// fallthrough path, *or* some break/continue already found it
				// to diverge independently of the fallthrough.
				let mutated = matches!(self.func.data_nodes[param as usize].kind, DataNodeKind::LoopParam { before, after, .. } if before != after);
				if mutated || divergent_params.contains(&param) {
					parent_bindings[i] = Some(StackResult::Value(param));
					outputs.push(param);
				}
			}
			NodeType::Aggregate(_) => {
				// One loop-param per WASM value, matching `create_loop_params`.
				// Reassembling afterwards would be a no-op: every slot already
				// holds its own loop param, so the rebuilt aggregate is `param`
				// itself — only the parent binding and the output list change.
				let lp_scalars = self.scalars_of(param);
				let after_scalars = self.scalars_of(after);
				let mut any_changed = false;
				for (&lp_scalar, &after_scalar) in
					lp_scalars.iter().zip(after_scalars.iter())
				{
					self.func.patch_loop_param(lp_scalar, after_scalar);
					let mutated = matches!(self.func.data_nodes[lp_scalar as usize].kind, DataNodeKind::LoopParam { before, after, .. } if before != after);
					if mutated || divergent_params.contains(&lp_scalar) {
						outputs.push(lp_scalar);
						any_changed = true;
					}
				}
				if any_changed {
					parent_bindings[i] = Some(StackResult::Value(param));
				}
			}
		}
	}

	/// The block-join analogue of `patch_loop_binding` — finalizes binding
	/// `i` once a block-join's body has been fully built (fallthrough
	/// reached). Unlike a loop, there is no "patch a placeholder in place"
	/// step at all: a `JoinParam` is either divergent (some exit — a break,
	/// or the fallthrough — found a genuinely different value for it, per
	/// `divergent_params`) or it isn't, decided purely from that
	/// already-accumulated union, with no `before`/`after` two-phase commit
	/// to run.
	///
	/// For a scalar slot, a non-divergent binding resolves directly to
	/// `current` (the fallthrough's own raw value) — never to the
	/// placeholder, which (unlike `LoopParam`) has no fallback value of its
	/// own to read if referenced (see `DataNodeKind::JoinParam`'s doc
	/// comment). For an aggregate slot that's only *partially* divergent
	/// (some scalar fields differ across exits, others don't), the
	/// reassembled result mixes: each divergent scalar uses its own
	/// `JoinParam` (so every exit's commit for it lands in the same local),
	/// each non-divergent scalar uses `current`'s own value for that field
	/// directly — so every scalar actually referenced downstream is
	/// self-sufficient, never routing through a placeholder with nothing
	/// backing it.
	fn finalize_block_join_binding(
		&mut self,
		i: usize,
		entry_placeholders: &[Option<StackResult>],
		fallthrough_bindings: &[Option<StackResult>],
		parent_bindings: &mut [Option<StackResult>],
		outputs: &mut Vec<DataNodeIndex>,
		divergent_params: &[DataNodeIndex],
	) {
		// `None` at `entry_placeholders[i]` means this local was never
		// declared before the block began — a block-inner temp, never
		// genuinely outer-visible — so there's nothing to finalize for it.
		let param = match entry_placeholders[i] {
			Some(StackResult::Value(n)) => n,
			_ => return,
		};
		let current = match fallthrough_bindings[i] {
			Some(StackResult::Value(n)) => n,
			_ => return,
		};

		match self.func.data_nodes[param as usize].kind.node_type() {
			NodeType::Scalar(_) => {
				if divergent_params.contains(&param) {
					outputs.push(param);
					parent_bindings[i] = Some(StackResult::Value(param));
				} else {
					parent_bindings[i] = Some(StackResult::Value(current));
				}
			}
			NodeType::Aggregate(aggregate_index) => {
				let param_scalars = self.scalars_of(param);
				let current_scalars = self.scalars_of(current);
				let mut any_changed = false;
				let mut result_scalars =
					Vec::with_capacity(param_scalars.len());
				for (&p_scalar, &c_scalar) in
					param_scalars.iter().zip(current_scalars.iter())
				{
					if divergent_params.contains(&p_scalar) {
						outputs.push(p_scalar);
						any_changed = true;
						result_scalars.push(p_scalar);
					} else {
						result_scalars.push(c_scalar);
					}
				}
				parent_bindings[i] = Some(if any_changed {
					StackResult::Value(self.aggregate_from_scalars(
						aggregate_index,
						&result_scalars,
					))
				} else {
					StackResult::Value(current)
				});
			}
		}
	}

	/// `(carried_node, current_value_node)` pairs, decomposed to scalars —
	/// the target's own carried bindings (a loop's
	/// `LoopData::entry_placeholders`, or a block-join's
	/// `BlockJoinData::entry_placeholders`) as of this exact
	/// point, wherever they differ from what the carried node itself
	/// currently holds. `Break`/`Continue` use this to commit their own
	/// current values before jumping: the target's normal "commit
	/// accumulated bindings, then branch back/fall through" tail code
	/// (`ControlNode::Loop`/`ControlNode::BlockJoin`'s own scheduling) only
	/// runs on the ordinary path (a loop's back-edge, or a block's own
	/// fallthrough), so an early exit must commit independently or the next
	/// iteration (for `continue`, always a loop) — or code after the target
	/// (for `break`) — would see stale values.
	fn carried_binding_updates(
		&mut self,
		target: BlockIndex,
		bindings: &[Option<StackResult>],
	) -> Box<[(DataNodeIndex, DataNodeIndex)]> {
		let is_loop = self.func.blocks[target as usize]
			.as_ref()
			.unwrap()
			.is_loop();
		// Cloned out up front rather than indexed per-iteration: `self.func`
		// would otherwise need re-borrowing on every loop, and
		// `collect_scalar_loop_param_updates` below already needs `&mut self`.
		let carried: Vec<Option<StackResult>> = if is_loop {
			self.func.loop_data(target).entry_placeholders.clone()
		} else {
			self.func.block_join_data(target).entry_placeholders.clone()
		};
		let mut updates = Vec::new();
		// A `None` on either side means this local isn't genuinely carried
		// by `target` (never declared before it began) — nothing to commit.
		for (param, current) in
			carried.iter().copied().zip(bindings.iter().copied())
		{
			if let (Some(StackResult::Value(p)), Some(StackResult::Value(c))) =
				(param, current)
			{
				self.collect_scalar_loop_param_updates(p, c, &mut updates);
			}
		}
		// Fold every genuine divergence this call found into the target's
		// running record — see `LoopData`/`BlockJoinData::divergent_params`'s
		// doc comment. `updates` is typically tiny, so a linear dedup check
		// stays cheap.
		let divergent = if is_loop {
			&mut self.func.loop_data_mut(target).divergent_params
		} else {
			&mut self.func.block_join_data_mut(target).divergent_params
		};
		for &(param, _) in &updates {
			if !divergent.contains(&param) {
				divergent.push(param);
			}
		}
		updates.into_boxed_slice()
	}

	fn collect_scalar_loop_param_updates(
		&mut self,
		param: DataNodeIndex,
		current: DataNodeIndex,
		updates: &mut Vec<(DataNodeIndex, DataNodeIndex)>,
	) {
		if param == current {
			return;
		}
		match (
			self.func.data_nodes[param as usize].kind.node_type(),
			self.func.data_nodes[current as usize].kind.node_type(),
		) {
			(NodeType::Scalar(_), NodeType::Scalar(_)) => {
				updates.push((param, current));
			}
			(NodeType::Aggregate(_), NodeType::Aggregate(_)) => {
				let param_scalars = self.scalars_of(param);
				let current_scalars = self.scalars_of(current);
				updates.extend(
					param_scalars
						.into_iter()
						.zip(current_scalars)
						.filter(|(p, c)| p != c),
				);
			}
			_ => {}
		}
	}

	/// Merges a `break`'s own value (or, for a block-join, the fallthrough's
	/// own tail value) into whatever `target`'s accumulated trailing value is
	/// so far, exactly like `Loop`'s own trailing-value merge — this is the
	/// loop-vs-block-join-agnostic core the `ExprKind::Break` arm and
	/// `build_block_expr`'s fallthrough step both call into. When two
	/// distinct values are merged, phi nodes are created and stored in
	/// `break_result_outputs` (on whichever side table `target` actually
	/// has) so the scheduler can pre-allocate WASM locals for them — the
	/// outputs vec is replaced (not appended) each call so it always
	/// reflects the current phi set: every exit writes directly to the
	/// final phi's local at runtime.
	fn merge_exit_value(
		&mut self,
		target: BlockIndex,
		val: StackResult,
	) -> StackResult {
		let existing =
			self.func.blocks[target as usize].as_ref().unwrap().result;
		let merged = match (existing, val) {
			(StackResult::Never, other) | (other, StackResult::Never) => other,
			(StackResult::Unit, StackResult::Unit) => StackResult::Unit,
			(StackResult::Value(l), StackResult::Value(r)) => {
				let mut outputs = Vec::new();
				let node = self.merge_values(l, r, &mut outputs);
				let is_loop = self.func.blocks[target as usize]
					.as_ref()
					.unwrap()
					.is_loop();
				if is_loop {
					self.func.loop_data_mut(target).break_result_outputs =
						outputs;
				} else {
					self.func
						.block_join_data_mut(target)
						.break_result_outputs = outputs;
				}
				StackResult::Value(node)
			}
			_ => {
				panic!("cannot merge exit results {:?} and {:?}", existing, val)
			}
		};
		self.func.blocks[target as usize].as_mut().unwrap().result = merged;
		merged
	}

	/// Merge bindings from two branches, creating Phi nodes for values that
	/// differ. Updates `parent_bindings` with the merged results and
	/// appends phi indices to `outputs`.
	#[allow(clippy::too_many_arguments)]
	fn merge_branches(
		&mut self,
		then_result: StackResult,
		else_result: StackResult,
		then_bindings: &[Option<StackResult>],
		else_bindings: &[Option<StackResult>],
		parent_len: usize,
		parent_bindings: &mut [Option<StackResult>],
		outputs: &mut Vec<DataNodeIndex>,
	) -> StackResult {
		for i in 0..parent_len {
			let (t, e) = match (then_bindings[i], else_bindings[i]) {
				(Some(t), Some(e)) => (t, e),
				// Not declared in at least one branch — private to
				// whichever branch (if either) actually declared it, since
				// every local gets a distinct flat index (no sharing
				// between branches). Nothing outside either branch could
				// ever reference it, so it never gets merged/output; stays
				// `None`.
				_ => {
					parent_bindings[i] = None;
					continue;
				}
			};
			if t == e {
				parent_bindings[i] = Some(t);
				continue;
			}
			match (t, e) {
				(StackResult::Value(l), StackResult::Value(r)) => {
					let merged = self.merge_values(l, r, outputs);
					parent_bindings[i] = Some(StackResult::Value(merged));
				}
				(StackResult::Never, other) | (other, StackResult::Never) => {
					parent_bindings[i] = Some(other);
				}
				_ => {}
			}
		}
		// Merge the branch expression results. Any phi created here must also
		// go into `outputs` so the scheduler can pre-allocate its local.
		match (then_result, else_result) {
			(StackResult::Never, other) | (other, StackResult::Never) => other,
			(StackResult::Unit, StackResult::Unit) => StackResult::Unit,
			(StackResult::Value(l), StackResult::Value(r)) => {
				StackResult::Value(self.merge_values(l, r, outputs))
			}
			_ => panic!(
				"cannot merge branch results {:?} and {:?}",
				then_result, else_result
			),
		}
	}

	/// Merge two scalar-or-aggregate value nodes, creating Phi(s) as needed.
	fn merge_values(
		&mut self,
		l: DataNodeIndex,
		r: DataNodeIndex,
		outputs: &mut Vec<DataNodeIndex>,
	) -> DataNodeIndex {
		match (
			self.func.data_nodes[l as usize].kind.node_type(),
			self.func.data_nodes[r as usize].kind.node_type(),
		) {
			(NodeType::Scalar(ty), NodeType::Scalar(_)) => {
				let phi = self.node(DataNodeKind::Phi {
					left: l,
					right: r,
					ty,
				});
				if phi != l && phi != r {
					outputs.push(phi);
				}
				phi
			}
			(NodeType::Aggregate(aggregate_index), NodeType::Aggregate(_)) => {
				// One phi per differing WASM value, then reassemble the shape.
				let l_scalars = self.scalars_of(l);
				let r_scalars = self.scalars_of(r);
				let merged: Vec<DataNodeIndex> = l_scalars
					.into_iter()
					.zip(r_scalars)
					.map(|(lf, rf)| {
						if lf == rf {
							return lf;
						}
						let ty = match self.func.data_nodes[lf as usize]
							.kind
							.node_type()
						{
							NodeType::Scalar(ty) => ty,
							NodeType::Aggregate(_) => {
								unreachable!("scalars_of yields only scalars")
							}
						};
						let phi = self.node(DataNodeKind::Phi {
							left: lf,
							right: rf,
							ty,
						});
						if phi != lf && phi != rf {
							outputs.push(phi);
						}
						phi
					})
					.collect();
				self.aggregate_from_scalars(aggregate_index, &merged)
			}
			_ => panic!("type mismatch when merging branch values"),
		}
	}

	/// Return the data node for aggregate field `phys_index` (physical order),
	/// whether that field is scalar or itself a nested aggregate.
	///
	/// When `aggregate` is a known `Aggregate` literal its `fields` are
	/// already-built nodes with whatever `NodeType` each field actually has,
	/// so returning `fields[phys_index]` directly sidesteps `AggregateGet`
	/// entirely (the same identity `node()` applies when folding).
	///
	/// Otherwise — a `Phi`, `LoopParam` or `AggregateCallResult` — the field
	/// is rebuilt out of per-scalar projections. A scalar field is one
	/// `AggregateGet`; a nested field is one per scalar in its range, rewrapped
	/// into an `Aggregate` node of the nested shape. This is why
	/// `AggregateGet` is indexed by `ScalarIndex`: it never has to name
	/// something that is not a single WASM value.
	fn get_aggregate_field(
		&mut self,
		aggregate: DataNodeIndex,
		aggregate_index: mir::AggregateIndex,
		phys_index: mir::PhysIndex,
	) -> DataNodeIndex {
		if let DataNodeKind::Aggregate { fields, .. } =
			&self.func.data_nodes[aggregate as usize].kind
		{
			return fields[usize::from(phys_index)];
		}
		// Copied out of `self` so it keeps its own `'mir` lifetime — reborrowing
		// through `self` would collide with the `&mut self` calls below.
		let mir = self.mir;
		let agg = &mir.aggregate(aggregate_index);
		let range = agg.scalars.field_range(phys_index);
		match agg.field(phys_index).ty {
			mir::ValueType::Aggregate {
				aggregate_index: nested,
			} => {
				let values: Vec<DataNodeIndex> = range
					.map(|i| {
						self.project_scalar(aggregate, mir::ScalarIndex::new(i))
					})
					.collect();
				self.aggregate_from_scalars(nested, &values)
			}
			_ => self
				.project_scalar(aggregate, mir::ScalarIndex::new(range.start)),
		}
	}

	/// Build the `AggregateGet` naming a single WASM value of `aggregate`.
	fn project_scalar(
		&mut self,
		aggregate: DataNodeIndex,
		scalar: mir::ScalarIndex,
	) -> DataNodeIndex {
		let aggregate_index = self.aggregate_index_of(aggregate);
		let ty = ScalarType::try_from(
			self.mir.aggregate(aggregate_index).scalars.get(scalar).ty,
		)
		.expect("a ScalarTable entry is scalar by construction");
		self.node(DataNodeKind::AggregateGet {
			aggregate,
			scalar,
			ty,
		})
	}

	/// The aggregate shape carried by any aggregate-typed node.
	fn aggregate_index_of(&self, node: DataNodeIndex) -> mir::AggregateIndex {
		match self.func.data_nodes[node as usize].kind.node_type() {
			NodeType::Aggregate(index) => index,
			NodeType::Scalar(_) => panic!("expected an aggregate-typed node"),
		}
	}

	/// One node per *physical field* of an aggregate node — a nested field
	/// comes back as an `Aggregate` node, not as its constituent values.
	///
	/// For consumers that recurse structurally, field by field (`merge_switch_slot`).
	/// Anything that needs one slot per WASM value — loop params, phis, call
	/// results, signatures — wants [`Builder::scalars_of`] instead; a field is
	/// not a value.
	fn fields_of(&mut self, node: DataNodeIndex) -> Box<[DataNodeIndex]> {
		let aggregate_index = self.aggregate_index_of(node);
		let count = self.mir.aggregate(aggregate_index).field_count();
		(0..count as u32)
			.map(mir::PhysIndex::new)
			.map(|phys| self.get_aggregate_field(node, aggregate_index, phys))
			.collect()
	}

	/// Decompose an aggregate node into one node per WASM value, in
	/// `mir::ScalarTable` order.
	///
	/// The only supported way to take an aggregate apart. Consumers needing
	/// one slot per value — loop params, phis, call results — come through
	/// here rather than walking `Aggregate::fields`, because a field is not a
	/// value: a nested field is several, a zero-sized field is none.
	fn scalars_of(&mut self, node: DataNodeIndex) -> Vec<DataNodeIndex> {
		let mut out = Vec::new();
		self.collect_scalars(node, &mut out);
		out
	}

	fn collect_scalars(
		&mut self,
		node: DataNodeIndex,
		out: &mut Vec<DataNodeIndex>,
	) {
		let mir = self.mir;
		match self.func.data_nodes[node as usize].kind.clone() {
			DataNodeKind::Aggregate {
				fields,
				aggregate_index,
			} => {
				let agg = &mir.aggregate(aggregate_index);
				for (field, &field_node) in agg.fields.iter().zip(fields.iter())
				{
					match field.ty {
						mir::ValueType::Unit | mir::ValueType::Never => {}
						mir::ValueType::Aggregate { .. } => {
							self.collect_scalars(field_node, out)
						}
						_ => out.push(field_node),
					}
				}
			}
			// No field sub-nodes — the values live on the multi-return stack,
			// so each one has to be named by an explicit projection.
			DataNodeKind::AggregateCallResult { aggregate_index } => {
				let count = mir.aggregate(aggregate_index).scalars.len();
				out.extend((0..count as u32).map(|i| {
					self.project_scalar(node, mir::ScalarIndex::new(i))
				}));
			}
			_ => panic!("expected aggregate node"),
		}
	}

	/// Rebuild an aggregate of shape `aggregate_index` from one node per WASM
	/// value, inverting `scalars_of`.
	///
	/// `values` holds exactly this shape's scalars. Each field owns a
	/// *contiguous* run of them, so a nested field recurses on its own
	/// subslice — there is no cursor to keep in sync between siblings. Built
	/// bottom-up, so a pure node's operands always have lower indices than the
	/// node itself, which is what
	/// `local_dominance::verify_operand_index_ordering` checks. Goes through
	/// `node()` so CSE still applies, which is what lets `patch_loop_binding`
	/// compare a rebuilt aggregate against the original by identity.
	fn aggregate_from_scalars(
		&mut self,
		aggregate_index: mir::AggregateIndex,
		values: &[DataNodeIndex],
	) -> DataNodeIndex {
		let mir = self.mir;
		let agg = &mir.aggregate(aggregate_index);
		debug_assert_eq!(
			values.len(),
			agg.scalars.len(),
			"value count must match the aggregate's scalar count"
		);
		let mut fields = Vec::with_capacity(agg.field_count());
		for (i, field) in agg.fields.iter().enumerate() {
			let range = agg.scalars.field_range(mir::PhysIndex::new(i as u32));
			let owned = &values[range.start as usize..range.end as usize];
			fields.push(match field.ty {
				mir::ValueType::Aggregate {
					aggregate_index: nested,
				} => self.aggregate_from_scalars(nested, owned),
				mir::ValueType::Unit | mir::ValueType::Never => unreachable!(
					"a zero-sized aggregate field owns no value to rebuild \
					 from; `DataNodeKind::Aggregate::fields` cannot represent \
					 one yet"
				),
				_ => owned[0],
			});
		}
		self.node(DataNodeKind::Aggregate {
			fields: fields.into_boxed_slice(),
			aggregate_index,
		})
	}

	/// Store an aggregate value through a pointer, one memory access per WASM
	/// value.
	///
	/// `MemAccess` has no notion of "store a whole nested struct", so this has
	/// to reach the individual scalars. It used to recurse the field tree
	/// accumulating offsets; the `ScalarTable` already holds each scalar's
	/// offset relative to the aggregate base, so it is now a flat zip.
	fn emit_aggregate_store(
		&mut self,
		block_idx: BlockIndex,
		address: DataNodeIndex,
		base_offset: u32,
		value_node: DataNodeIndex,
		aggregate_index: mir::AggregateIndex,
		memory: crate::ast::DefId,
	) {
		let values = self.scalars_of(value_node);
		let mir = self.mir;
		let scalars = &mir.aggregate(aggregate_index).scalars;
		debug_assert_eq!(values.len(), scalars.len());
		for (&value, scalar) in values.iter().zip(scalars.iter()) {
			self.push_stmt(
				block_idx,
				ControlNode::PointerStore {
					address,
					offset: base_offset + scalar.offset,
					value,
					memory,
					access: MemAccess::from_mir(scalar.ty),
				},
			);
		}
	}

	/// Load an aggregate through a pointer, one memory access per WASM value,
	/// then reassemble the shape. Mirrors `emit_aggregate_store`.
	fn build_aggregate_load(
		&mut self,
		block_idx: BlockIndex,
		address: DataNodeIndex,
		base_offset: u32,
		aggregate_index: mir::AggregateIndex,
		memory: crate::ast::DefId,
	) -> DataNodeIndex {
		let mir = self.mir;
		let scalars = &mir.aggregate(aggregate_index).scalars;
		let values: Vec<DataNodeIndex> = scalars
			.iter()
			.map(|scalar| {
				let access = MemAccess::from_mir(scalar.ty);
				let result = self
					.node(DataNodeKind::PointerLoadResult { address, access });
				self.push_stmt(
					block_idx,
					ControlNode::PointerLoad {
						address,
						offset: base_offset + scalar.offset,
						result,
						memory,
						access,
					},
				);
				result
			})
			.collect();
		self.aggregate_from_scalars(aggregate_index, &values)
	}

	/// Merge two `StackResult`s at a control-flow join. `Never` defers to the
	/// other side.
	fn merge_stack_results(
		&mut self,
		a: StackResult,
		b: StackResult,
	) -> StackResult {
		match (a, b) {
			(StackResult::Never, other) | (other, StackResult::Never) => other,
			(StackResult::Unit, StackResult::Unit) => StackResult::Unit,
			(StackResult::Value(l), StackResult::Value(r)) => {
				let mut dummy = Vec::new();
				StackResult::Value(self.merge_values(l, r, &mut dummy))
			}
			_ => panic!("cannot merge {:?} and {:?}", a, b),
		}
	}

	// ── Small helpers ─────────────────────────────────────────────────────────

	fn build_block_exprs(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		expressions: &[mir::Expression],
	) -> StackResult {
		let mut result = StackResult::Unit;
		for expr in expressions {
			result = self.build_expr(block_idx, bindings, expr);
			if result == StackResult::Never {
				break;
			}
		}
		result
	}

	/// Arithmetic, bitwise, and shift operators. WASM has separate signed
	/// and unsigned instructions for division, remainder, and right shift;
	/// `ScalarType` can't tell them apart (`u32` and `i32` are both `I32`
	/// there), so the node kind is chosen from the MIR type. Unsigned
	/// integers and pointers take the `_u` variants; floats keep the `S`
	/// kinds, which the scheduler maps to the sign-free float instructions.
	fn build_binary(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		expr: &mir::Expression,
		lhs: &mir::Expression,
		rhs: &mir::Expression,
	) -> StackResult {
		use DataNodeKind as N;
		use mir::ExprKind as E;

		let ty =
			ScalarType::try_from(expr.ty).expect("binary op must be scalar");
		let unsigned = expr.ty.is_unsigned();
		let left = self.build_expr(block_idx, bindings, lhs).unwrap_value();
		let right = self.build_expr(block_idx, bindings, rhs).unwrap_value();

		let kind = match &expr.kind {
			E::Add { .. } => N::Add { left, right, ty },
			E::Sub { .. } => N::Sub { left, right, ty },
			E::Mul { .. } => N::Mul { left, right, ty },
			E::Div { .. } if unsigned => N::DivU { left, right, ty },
			E::Div { .. } => N::DivS { left, right, ty },
			E::Rem { .. } if unsigned => N::RemU { left, right, ty },
			E::Rem { .. } => N::RemS { left, right, ty },
			E::And { .. } | E::BitAnd { .. } => N::BitAnd { left, right, ty },
			E::Or { .. } | E::BitOr { .. } => N::BitOr { left, right, ty },
			E::BitXor { .. } => N::BitXor { left, right, ty },
			E::LeftShift { .. } => N::Shl { left, right, ty },
			E::RightShift { .. } if unsigned => N::ShrU { left, right, ty },
			E::RightShift { .. } => N::ShrS { left, right, ty },
			E::Min { .. } => N::Min { left, right, ty },
			E::Max { .. } => N::Max { left, right, ty },
			E::Copysign { .. } => N::Copysign { left, right, ty },
			_ => unreachable!("build_binary called on a non-binary ExprKind"),
		};
		StackResult::Value(self.node(kind))
	}

	/// Comparison operators. Like `build_binary`, the signed/unsigned
	/// choice comes from the MIR type — but from the *operands*, since the
	/// result is always Bool. The `ScalarType` likewise comes from the
	/// built operand node.
	fn build_cmp(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		expr: &mir::Expression,
		lhs: &mir::Expression,
		rhs: &mir::Expression,
	) -> StackResult {
		use DataNodeKind as N;
		use mir::ExprKind as E;

		let unsigned = lhs.ty.is_unsigned();
		let left = self.build_expr(block_idx, bindings, lhs).unwrap_value();
		let right = self.build_expr(block_idx, bindings, rhs).unwrap_value();
		let ty = self.func.data_nodes[left as usize].kind.unwrap_scalar();

		let kind = match &expr.kind {
			E::Eq { .. } => N::Eq { left, right, ty },
			E::NotEq { .. } => N::NotEq { left, right, ty },
			E::Less { .. } if unsigned => N::LtU { left, right, ty },
			E::Less { .. } => N::LtS { left, right, ty },
			E::LessEq { .. } if unsigned => N::LtEqU { left, right, ty },
			E::LessEq { .. } => N::LtEqS { left, right, ty },
			E::Greater { .. } if unsigned => N::GtU { left, right, ty },
			E::Greater { .. } => N::GtS { left, right, ty },
			E::GreaterEq { .. } if unsigned => N::GtEqU { left, right, ty },
			E::GreaterEq { .. } => N::GtEqS { left, right, ty },
			_ => unreachable!("build_cmp called on a non-comparison ExprKind"),
		};
		StackResult::Value(self.node(kind))
	}

	/// Reads binding slot `idx`, falling back to a fresh type default —
	/// never memoized back into `bindings` — if this local was never
	/// actually written on this particular build path (e.g. code reachable
	/// only through a branch that traps/never executes at runtime, but
	/// still gets built). `None` must keep meaning "not yet declared" for
	/// every other consumer (divergence-merge, `create_loop_params`/
	/// `create_join_params`): writing the default back here would make a
	/// scope-private local look outer-visible just because one path
	/// happened to read it before writing it.
	fn read_binding(
		&mut self,
		bindings: &[Option<StackResult>],
		idx: usize,
	) -> StackResult {
		match bindings[idx] {
			Some(v) => v,
			None => self.default_value(self.mir_func.locals[idx].ty),
		}
	}

	fn default_value(&mut self, ty: mir::ValueType) -> StackResult {
		match ty {
			mir::ValueType::Unit | mir::ValueType::Never => StackResult::Unit,
			mir::ValueType::Aggregate { aggregate_index } => {
				let mir = self.mir;
				let agg = &mir.aggregate(aggregate_index);
				let fields: Box<[_]> = agg
					.fields
					.iter()
					.map(|field| self.default_value(field.ty).unwrap_value())
					.collect();
				StackResult::Value(self.node(DataNodeKind::Aggregate {
					fields,
					aggregate_index,
				}))
			}
			_ => {
				let scalar_ty =
					ScalarType::try_from(ty).expect("unexpected local type");
				let node = match scalar_ty {
					ScalarType::F32 => self.node(DataNodeKind::Float {
						bits: 0,
						ty: ScalarType::F32,
					}),
					ScalarType::F64 => self.node(DataNodeKind::Float {
						bits: 0,
						ty: ScalarType::F64,
					}),
					_ => self.node(DataNodeKind::Int {
						value: 0,
						ty: scalar_ty,
					}),
				};
				StackResult::Value(node)
			}
		}
	}

	/// If `aggregate` is a literal `Aggregate`, the node already holding the
	/// value at `scalar`. Descends through nested aggregates, rebasing the
	/// scalar index to each level, so a projection never survives as a node
	/// when the value it names is already in hand.
	fn fold_scalar_projection(
		&self,
		aggregate: DataNodeIndex,
		scalar: mir::ScalarIndex,
	) -> Option<DataNodeIndex> {
		let DataNodeKind::Aggregate {
			fields,
			aggregate_index,
		} = &self.func.data_nodes[aggregate as usize].kind
		else {
			return None;
		};
		let agg = self.mir.aggregate(*aggregate_index);
		let owner = agg.scalars.owner(scalar);
		let field_node = fields[usize::from(owner)];
		match agg.field(owner).ty {
			mir::ValueType::Aggregate { .. } => {
				let start = agg.scalars.field_range(owner).start;
				let relative = mir::ScalarIndex::new(u32::from(scalar) - start);
				self.fold_scalar_projection(field_node, relative)
			}
			_ => Some(field_node),
		}
	}

	// ── Node construction ─────────────────────────────────────────────────────

	/// The primary way to create a node. Applies algebraic simplifications
	/// then interns via CSE. Call `func.intern_node` directly only when the
	/// kind is already canonical (e.g. a freshly computed `Int` constant).
	fn node(&mut self, kind: DataNodeKind) -> DataNodeIndex {
		// AggregateGet of a known Aggregate returns the holding node directly.
		if let DataNodeKind::AggregateGet {
			aggregate, scalar, ..
		} = &kind
		{
			if let Some(folded) =
				self.fold_scalar_projection(*aggregate, *scalar)
			{
				return folded;
			}
		}

		// Phi with equal operands is a no-op.
		if let DataNodeKind::Phi { left, right, .. } = &kind {
			if left == right {
				return *left;
			}
		}

		// Identity / absorbing element rules.
		if let Some(s) = self.try_simplify_identity(&kind) {
			return s;
		}

		// Integer constant folding.
		if let Some(f) = self.try_fold_int(&kind) {
			return f;
		}

		// Strength reduction (fires after folding so two-constant mul is already
		// handled above).
		if let Some(r) = self.try_strength_reduce(&kind) {
			return r;
		}

		self.func.intern_node(kind)
	}

	fn unwrap_int(&self, node: DataNodeIndex) -> Option<i64> {
		match self.func.data_nodes[node as usize].kind {
			DataNodeKind::Int { value, .. } => Some(value),
			_ => None,
		}
	}

	fn try_fold_int(&mut self, kind: &DataNodeKind) -> Option<DataNodeIndex> {
		match kind {
			DataNodeKind::Neg { operand, ty } => {
				let v = self.unwrap_int(*operand)?;
				let result = match ty {
					ScalarType::I32 => (v as i32).wrapping_neg() as i64,
					ScalarType::I64 => v.wrapping_neg(),
					_ => return None,
				};
				return Some(self.func.intern_node(DataNodeKind::Int {
					value: result,
					ty: *ty,
				}));
			}
			DataNodeKind::BitNot { operand, ty } => {
				let v = self.unwrap_int(*operand)?;
				let result = match ty {
					ScalarType::I32 => !(v as i32) as i64,
					ScalarType::I64 => !v,
					_ => return None,
				};
				return Some(self.func.intern_node(DataNodeKind::Int {
					value: result,
					ty: *ty,
				}));
			}
			DataNodeKind::Eqz { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.func.intern_node(DataNodeKind::Int {
					value: (v == 0) as i64,
					ty: ScalarType::I32,
				}));
			}
			DataNodeKind::I32WrapI64 { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.func.intern_node(DataNodeKind::Int {
					value: v as i32 as i64,
					ty: ScalarType::I32,
				}));
			}
			DataNodeKind::I64ExtendI32S { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.func.intern_node(DataNodeKind::Int {
					value: v as i32 as i64,
					ty: ScalarType::I64,
				}));
			}
			DataNodeKind::I64ExtendI32U { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.func.intern_node(DataNodeKind::Int {
					value: v as u32 as i64,
					ty: ScalarType::I64,
				}));
			}
			DataNodeKind::Eq { left, right, ty }
			| DataNodeKind::NotEq { left, right, ty }
			| DataNodeKind::LtS { left, right, ty }
			| DataNodeKind::LtEqS { left, right, ty }
			| DataNodeKind::GtS { left, right, ty }
			| DataNodeKind::GtEqS { left, right, ty }
			| DataNodeKind::LtU { left, right, ty }
			| DataNodeKind::LtEqU { left, right, ty }
			| DataNodeKind::GtU { left, right, ty }
			| DataNodeKind::GtEqU { left, right, ty } => {
				let l = self.unwrap_int(*left)?;
				let r = self.unwrap_int(*right)?;
				// Signed I32 comparisons must compare as i32 (sign bit matters).
				// Unsigned comparisons must compare as u32/u64.
				let result = match kind {
					DataNodeKind::Eq { .. } => (l == r) as i64,
					DataNodeKind::NotEq { .. } => (l != r) as i64,
					DataNodeKind::LtS { .. } => match ty {
						ScalarType::I32 => ((l as i32) < (r as i32)) as i64,
						_ => (l < r) as i64,
					},
					DataNodeKind::LtEqS { .. } => match ty {
						ScalarType::I32 => ((l as i32) <= (r as i32)) as i64,
						_ => (l <= r) as i64,
					},
					DataNodeKind::GtS { .. } => match ty {
						ScalarType::I32 => ((l as i32) > (r as i32)) as i64,
						_ => (l > r) as i64,
					},
					DataNodeKind::GtEqS { .. } => match ty {
						ScalarType::I32 => ((l as i32) >= (r as i32)) as i64,
						_ => (l >= r) as i64,
					},
					DataNodeKind::LtU { .. } => match ty {
						ScalarType::I32 => ((l as u32) < (r as u32)) as i64,
						_ => ((l as u64) < (r as u64)) as i64,
					},
					DataNodeKind::LtEqU { .. } => match ty {
						ScalarType::I32 => ((l as u32) <= (r as u32)) as i64,
						_ => ((l as u64) <= (r as u64)) as i64,
					},
					DataNodeKind::GtU { .. } => match ty {
						ScalarType::I32 => ((l as u32) > (r as u32)) as i64,
						_ => ((l as u64) > (r as u64)) as i64,
					},
					DataNodeKind::GtEqU { .. } => match ty {
						ScalarType::I32 => ((l as u32) >= (r as u32)) as i64,
						_ => ((l as u64) >= (r as u64)) as i64,
					},
					_ => unreachable!(),
				};
				return Some(self.func.intern_node(DataNodeKind::Int {
					value: result,
					ty: ScalarType::I32,
				}));
			}
			_ => {}
		}

		// ── Binary arithmetic on two Int constants ────────────────────────
		let (left, right, ty) = match *kind {
			DataNodeKind::Add { left, right, ty } => (left, right, ty),
			DataNodeKind::Sub { left, right, ty } => (left, right, ty),
			DataNodeKind::Mul { left, right, ty } => (left, right, ty),
			DataNodeKind::DivS { left, right, ty } => (left, right, ty),
			DataNodeKind::DivU { left, right, ty } => (left, right, ty),
			DataNodeKind::RemS { left, right, ty } => (left, right, ty),
			DataNodeKind::RemU { left, right, ty } => (left, right, ty),
			DataNodeKind::BitAnd { left, right, ty } => (left, right, ty),
			DataNodeKind::BitOr { left, right, ty } => (left, right, ty),
			DataNodeKind::BitXor { left, right, ty } => (left, right, ty),
			DataNodeKind::Shl { left, right, ty } => (left, right, ty),
			DataNodeKind::ShrS { left, right, ty } => (left, right, ty),
			DataNodeKind::ShrU { left, right, ty } => (left, right, ty),
			_ => return None,
		};

		let l = self.unwrap_int(left)?;
		let r = self.unwrap_int(right)?;

		let result = match kind {
			DataNodeKind::Add { .. } => l.wrapping_add(r),
			DataNodeKind::Sub { .. } => l.wrapping_sub(r),
			DataNodeKind::Mul { .. } => l.wrapping_mul(r),
			DataNodeKind::DivS { .. } | DataNodeKind::RemS { .. } if r == 0 => {
				return None;
			}
			DataNodeKind::DivU { .. } | DataNodeKind::RemU { .. } if r == 0 => {
				return None;
			}
			// Signed div can trap (INT_MIN / -1); leave that to runtime.
			DataNodeKind::DivS { .. } => match ty {
				ScalarType::I32 => (l as i32).checked_div(r as i32)? as i64,
				ScalarType::I64 => l.checked_div(r)?,
				_ => return None,
			},
			DataNodeKind::DivU { .. } => match ty {
				ScalarType::I32 => ((l as u32) / (r as u32)) as i32 as i64,
				ScalarType::I64 => ((l as u64) / (r as u64)) as i64,
				_ => return None,
			},
			// WASM rem_s(INT_MIN, -1) is defined as 0, matching wrapping_rem.
			DataNodeKind::RemS { .. } => match ty {
				ScalarType::I32 => (l as i32).wrapping_rem(r as i32) as i64,
				ScalarType::I64 => l.wrapping_rem(r),
				_ => return None,
			},
			DataNodeKind::RemU { .. } => match ty {
				ScalarType::I32 => ((l as u32) % (r as u32)) as i32 as i64,
				ScalarType::I64 => ((l as u64) % (r as u64)) as i64,
				_ => return None,
			},
			DataNodeKind::BitAnd { .. } => l & r,
			DataNodeKind::BitOr { .. } => l | r,
			DataNodeKind::BitXor { .. } => l ^ r,
			// Shifts: WASM masks the shift amount by the bit-width, so cast to
			// the correct integer size first (mask is 31 for I32, 63 for I64).
			DataNodeKind::Shl { .. } => match ty {
				ScalarType::I32 => (l as i32).wrapping_shl(r as u32) as i64,
				ScalarType::I64 => l.wrapping_shl(r as u32),
				_ => return None,
			},
			DataNodeKind::ShrS { .. } => match ty {
				ScalarType::I32 => (l as i32).wrapping_shr(r as u32) as i64,
				ScalarType::I64 => l.wrapping_shr(r as u32),
				_ => return None,
			},
			DataNodeKind::ShrU { .. } => match ty {
				ScalarType::I32 => {
					(l as u32).wrapping_shr(r as u32) as i32 as i64
				}
				ScalarType::I64 => (l as u64).wrapping_shr(r as u32) as i64,
				_ => return None,
			},
			_ => unreachable!(),
		};

		Some(
			self.func
				.intern_node(DataNodeKind::Int { value: result, ty }),
		)
	}

	fn try_simplify_identity(
		&self,
		kind: &DataNodeKind,
	) -> Option<DataNodeIndex> {
		let zero = |n: DataNodeIndex| self.unwrap_int(n) == Some(0);
		let one = |n: DataNodeIndex| self.unwrap_int(n) == Some(1);

		match *kind {
			DataNodeKind::Add { left, right, .. } => {
				if zero(right) {
					return Some(left);
				}
				if zero(left) {
					return Some(right);
				}
			}
			DataNodeKind::Sub { left, right, .. } if zero(right) => {
				return Some(left);
			}
			DataNodeKind::Mul { left, right, .. } => {
				if zero(right) {
					return Some(right);
				}
				if zero(left) {
					return Some(left);
				}
				if one(right) {
					return Some(left);
				}
				if one(left) {
					return Some(right);
				}
			}
			DataNodeKind::DivS { left, right, .. }
			| DataNodeKind::DivU { left, right, .. }
				if one(right) =>
			{
				return Some(left);
			}
			DataNodeKind::BitAnd { left, right, .. } => {
				if zero(right) {
					return Some(right);
				}
				if zero(left) {
					return Some(left);
				}
			}
			DataNodeKind::BitOr { left, right, .. } => {
				if zero(right) {
					return Some(left);
				}
				if zero(left) {
					return Some(right);
				}
			}
			DataNodeKind::BitXor { left, right, .. } => {
				if zero(right) {
					return Some(left);
				}
				if zero(left) {
					return Some(right);
				}
			}
			DataNodeKind::Shl { left, right, .. }
			| DataNodeKind::ShrS { left, right, .. }
			| DataNodeKind::ShrU { left, right, .. }
				if zero(right) =>
			{
				return Some(left);
			}
			_ => {}
		}
		None
	}

	/// Replace `x * 2^n` with `x << n`. Only fires when `x` is not a constant
	/// (the constant case is already handled by `try_fold_int`).
	fn try_strength_reduce(
		&mut self,
		kind: &DataNodeKind,
	) -> Option<DataNodeIndex> {
		if let DataNodeKind::Mul { left, right, ty } = *kind {
			let (x, c) = if let Some(c) = self.unwrap_int(right) {
				(left, c)
			} else {
				let c = self.unwrap_int(left)?;
				(right, c)
			};
			// c > 1: c == 1 is already handled by identity rules.
			if c > 1 && c & (c - 1) == 0 {
				let shift = c.trailing_zeros() as i64;
				let shift_node = self
					.func
					.intern_node(DataNodeKind::Int { value: shift, ty });
				return Some(self.func.intern_node(DataNodeKind::Shl {
					left: x,
					right: shift_node,
					ty,
				}));
			}
		}
		None
	}

	fn push_stmt(&mut self, block_idx: BlockIndex, stmt: ControlNode) {
		self.func.blocks[block_idx as usize]
			.as_mut()
			.unwrap()
			.statements
			.push(stmt);
	}

	/// Expect a `Block` expression and return its scope index + expressions.
	fn unwrap_block(
		expr: &mir::Expression,
	) -> (mir::ScopeIndex, &[mir::Expression]) {
		match &expr.kind {
			ExprKind::Block {
				scope_index,
				expressions,
			} => (*scope_index, expressions),
			_ => panic!("expected Block expression"),
		}
	}
}

/// Marks `out[scope_index] = true` for every `ExprKind::Break { scope_index,
/// .. }` reachable from `expr`. Walked exhaustively over every `ExprKind`
/// variant that can hold a nested `Expression` — mirrors
/// `mir::inlining::Rebaser::rebase`'s identical full recursive-descent shape
/// (same file's `inline_expr` is the same shape again), just read-only and
/// recording instead of rewriting.
///
/// `Continue` is deliberately not collected here: TIR guarantees every
/// `Continue` always targets a loop scope (see
/// `tir::builder::control::build_continue_expression`), so its target is
/// never a block-join candidate — only `Break` can reach a plain block.
fn collect_break_targets(expr: &mir::Expression, out: &mut [bool]) {
	match &expr.kind {
		ExprKind::Break { scope_index, value } => {
			out[usize::from(*scope_index)] = true;
			if let Some(v) = value {
				collect_break_targets(v, out);
			}
		}
		ExprKind::LocalSet { value, .. }
		| ExprKind::AggregateSet { value, .. }
		| ExprKind::Drop { value }
		| ExprKind::GlobalSet { value, .. }
		| ExprKind::Neg { value }
		| ExprKind::Sqrt { value }
		| ExprKind::Abs { value }
		| ExprKind::Floor { value }
		| ExprKind::Ceil { value }
		| ExprKind::Trunc { value }
		| ExprKind::Nearest { value }
		| ExprKind::BitNot { value }
		| ExprKind::Eqz { value }
		| ExprKind::I64ExtendI32S { value }
		| ExprKind::I64ExtendI32U { value }
		| ExprKind::I32WrapI64 { value }
		| ExprKind::F32ConvertI32 { value }
		| ExprKind::F32ConvertU32 { value }
		| ExprKind::F32ConvertI64 { value }
		| ExprKind::F32ConvertU64 { value }
		| ExprKind::F64ConvertI32 { value }
		| ExprKind::F64ConvertU32 { value }
		| ExprKind::F64ConvertI64 { value }
		| ExprKind::F64ConvertU64 { value }
		| ExprKind::I32TruncF32 { value }
		| ExprKind::U32TruncF32 { value }
		| ExprKind::I32TruncF64 { value }
		| ExprKind::U32TruncF64 { value }
		| ExprKind::I64TruncF32 { value }
		| ExprKind::U64TruncF32 { value }
		| ExprKind::I64TruncF64 { value }
		| ExprKind::U64TruncF64 { value }
		| ExprKind::F64PromoteF32 { value }
		| ExprKind::F32DemoteF64 { value }
		| ExprKind::I32ReinterpretF32 { value }
		| ExprKind::F32ReinterpretI32 { value }
		| ExprKind::I64ReinterpretF64 { value }
		| ExprKind::F64ReinterpretI64 { value }
		| ExprKind::PointerLoad { pointer: value, .. }
		| ExprKind::MemoryGrow { delta: value, .. } => {
			collect_break_targets(value, out)
		}
		ExprKind::Loop { block: value, .. } => {
			collect_break_targets(value, out)
		}
		ExprKind::Block { expressions, .. } => {
			for e in expressions.iter() {
				collect_break_targets(e, out);
			}
		}
		ExprKind::Return { value } => {
			if let Some(v) = value {
				collect_break_targets(v, out);
			}
		}
		ExprKind::Add { left, right }
		| ExprKind::Sub { left, right }
		| ExprKind::Mul { left, right }
		| ExprKind::Div { left, right }
		| ExprKind::Rem { left, right }
		| ExprKind::And { left, right }
		| ExprKind::Or { left, right }
		| ExprKind::Eq { left, right }
		| ExprKind::NotEq { left, right }
		| ExprKind::Less { left, right }
		| ExprKind::LessEq { left, right }
		| ExprKind::Greater { left, right }
		| ExprKind::GreaterEq { left, right }
		| ExprKind::BitAnd { left, right }
		| ExprKind::BitOr { left, right }
		| ExprKind::BitXor { left, right }
		| ExprKind::LeftShift { left, right }
		| ExprKind::RightShift { left, right }
		| ExprKind::Min { left, right }
		| ExprKind::Max { left, right }
		| ExprKind::Copysign { left, right }
		| ExprKind::PointerStore {
			pointer: left,
			value: right,
			..
		} => {
			collect_break_targets(left, out);
			collect_break_targets(right, out);
		}
		ExprKind::MemoryFill { dst, val, len, .. } => {
			collect_break_targets(dst, out);
			collect_break_targets(val, out);
			collect_break_targets(len, out);
		}
		ExprKind::MemoryCopy { dst, src, len, .. } => {
			collect_break_targets(dst, out);
			collect_break_targets(src, out);
			collect_break_targets(len, out);
		}
		ExprKind::Aggregate { values } => {
			for e in values.iter() {
				collect_break_targets(e, out);
			}
		}
		ExprKind::Call { callee, arguments } => {
			collect_break_targets(callee, out);
			for a in arguments.iter() {
				collect_break_targets(a, out);
			}
		}
		ExprKind::IfElse {
			condition,
			then_block,
			else_block,
		} => {
			collect_break_targets(condition, out);
			collect_break_targets(then_block, out);
			if let Some(e) = else_block {
				collect_break_targets(e, out);
			}
		}
		ExprKind::Switch {
			selector,
			cases,
			default,
		} => {
			collect_break_targets(selector, out);
			for (_, body) in cases.iter() {
				collect_break_targets(body, out);
			}
			if let Some(d) = default {
				collect_break_targets(d, out);
			}
		}
		ExprKind::Noop
		| ExprKind::Bool { .. }
		| ExprKind::Function { .. }
		| ExprKind::Int { .. }
		| ExprKind::Float { .. }
		| ExprKind::Global { .. }
		| ExprKind::Unreachable
		| ExprKind::MemoryOffset { .. }
		| ExprKind::MemoryIndex { .. }
		| ExprKind::MemorySize { .. }
		| ExprKind::StaticPointer { .. }
		| ExprKind::LocalGet { .. }
		| ExprKind::AggregateGet { .. }
		| ExprKind::Continue { .. } => {}
	}
}
