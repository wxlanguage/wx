use crate::mir::{
	self, BinaryOp, CompareOp, ExprId, ExprKind, ExprList, UnaryOp,
};
use crate::opt::{
	Block, BlockIndex, BlockKind, ControlNode, DataNodeIndex, DataNodeKind,
	Function, JoinData, MemAccess, NodeType, ScalarType, StackResult,
	SwitchCase, TrappingOp,
};

/// The opt block of the function's own body. A MIR label `l` is block
/// `l + 1`; blocks past the labels are synthetic.
const BODY_BLOCK: BlockIndex = 0;

pub struct Builder<'mir> {
	mir: &'mir mir::MIR,
	/// The MIR function being lowered, and its code.
	id: mir::FunctionId,
	mir_func: &'mir mir::Code,
	func: Function,
}

/// One `match` arm as built so far: its own block/bindings plus what it
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
/// scalar nodes, or a `Never`/`Unit` marker propagated to all slots.
enum PerArmSlot {
	Scalars(Vec<DataNodeIndex>),
	NoValue(StackResult),
}

/// The opt block a MIR label names.
fn label_block(label: mir::LabelId) -> BlockIndex {
	u32::from(label) + 1
}

impl<'mir> Builder<'mir> {
	/// Lower MIR function `id` into a sea-of-nodes `Function`.
	pub fn build(mir: &'mir mir::MIR, id: mir::FunctionId) -> Function {
		let mir_func = mir.code(id);
		let mut b = Builder {
			mir,
			id,
			mir_func,
			func: Function::new(id, mir_func.label_count as usize + 1),
		};
		b.build_function();
		b.func
	}

	fn body(&self) -> &'mir mir::Body {
		&self.mir_func.body
	}

	fn kind(&self, expr: ExprId) -> ExprKind {
		self.mir_func.body.kind(expr)
	}

	fn ty(&self, expr: ExprId) -> mir::ValueType {
		self.mir_func.body.ty(expr)
	}

	fn build_function(&mut self) {
		let mir_func = self.mir_func;
		let params = self
			.mir
			.signatures
			.params(self.mir.function(self.id).signature)
			.len();

		// Seed data_bindings for the whole function at once — locals are
		// flat and function-wide (`mir::Code::locals`), so every local's
		// index is already its final position here. Params are genuinely
		// available from function entry, so they're seeded `Some`; every
		// other local starts `None` ("not yet declared on this build path")
		// and only becomes `Some` when its own `LocalSet` is actually built
		// — see `read_binding`'s doc comment for why this matters.
		let mut data_bindings: Vec<Option<StackResult>> =
			vec![None; mir_func.locals.len()];

		// Each parameter is one scalar local, so its local index is its Wasm
		// parameter index.
		for (i, local) in mir_func.locals[..params].iter().enumerate() {
			let ty = ScalarType::try_from(local.ty)
				.expect("a parameter is one scalar");
			data_bindings[i] =
				Some(StackResult::Value(self.node(DataNodeKind::Param {
					index: i as u32,
					ty,
				})));
		}

		self.func.blocks[BODY_BLOCK as usize] = Some(Block {
			parent: None,
			statements: Vec::new(),
			result: StackResult::Never,
			kind: BlockKind::Block,
			join: None,
		});

		// The body's value is returned implicitly.
		let last = self.build_in(BODY_BLOCK, &mut data_bindings, mir_func.root);
		if last != StackResult::Never {
			let fn_result = self.func.blocks[BODY_BLOCK as usize]
				.as_ref()
				.unwrap()
				.result;
			let merged = self.merge_stack_results(fn_result, last);
			self.func.blocks[BODY_BLOCK as usize]
				.as_mut()
				.unwrap()
				.result = merged;
			self.push_stmt(BODY_BLOCK, ControlNode::Return { value: last });
		} else {
			// The body never falls through, but Wasm does not treat the end
			// of a nested `if` or a call to a `!` function as terminating the
			// enclosing function. Close the body with an explicit
			// `unreachable`; it is dead code when the last statement already
			// returned or branched.
			self.push_stmt(BODY_BLOCK, ControlNode::Unreachable);
		}
	}

	// ── Expression builder ────────────────────────────────────────────────────

	fn build_expr(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		expr: ExprId,
	) -> StackResult {
		let ty = self.ty(expr);
		match self.kind(expr) {
			// ── Literals ──────────────────────────────────────────────────
			ExprKind::Int { value } => {
				let scalar =
					ScalarType::try_from(ty).expect("Int must be scalar");
				StackResult::Value(self.int(value, scalar))
			}
			ExprKind::Float { value } => {
				let scalar =
					ScalarType::try_from(ty).expect("Float must be scalar");
				let bits = match scalar {
					ScalarType::F32 => (value as f32).to_bits() as u64,
					_ => value.to_bits(),
				};
				StackResult::Value(
					self.node(DataNodeKind::Float { bits, ty: scalar }),
				)
			}
			ExprKind::Noop => StackResult::Unit,
			ExprKind::Unreachable => {
				self.push_stmt(block_idx, ControlNode::Unreachable);
				StackResult::Never
			}

			// ── Locals ───────────────────────────────────────────────────
			ExprKind::LocalGet { local } => {
				self.read_binding(bindings, usize::from(local))
			}
			ExprKind::LocalSet { local, value } => {
				let new_val = self.build_expr(block_idx, bindings, value);
				if new_val == StackResult::Never {
					return StackResult::Never;
				}
				bindings[usize::from(local)] = Some(new_val);
				StackResult::Unit
			}
			// In the sea of nodes a local is a name for a value: each target
			// is bound to its result, and a dropped one is never read.
			ExprKind::SetLocals { targets, value } => {
				let results = match self.build_expr(block_idx, bindings, value)
				{
					StackResult::Never => return StackResult::Never,
					StackResult::Unit => Vec::new(),
					StackResult::Value(node) => match self.ty(value) {
						mir::ValueType::Aggregate { .. } => {
							self.scalars_of(node)
						}
						_ => vec![node],
					},
				};
				let targets = self.body().targets(targets);
				assert_eq!(
					targets.len(),
					results.len(),
					"a `SetLocals` has one target per result"
				);
				for (&target, result) in targets.iter().zip(results) {
					if let Some(local) = target {
						bindings[usize::from(local)] =
							Some(StackResult::Value(result));
					}
				}
				StackResult::Unit
			}

			// ── Module-level state ────────────────────────────────────────
			ExprKind::Global { id } => {
				let scalar =
					ScalarType::try_from(ty).expect("a global read is scalar");
				let result =
					self.node(DataNodeKind::GlobalGetResult { ty: scalar });
				self.push_stmt(
					block_idx,
					ControlNode::GlobalGet { id, result },
				);
				StackResult::Value(result)
			}
			ExprKind::GlobalSet { id, value } => {
				let Some(value) = self.build_value(block_idx, bindings, value)
				else {
					return StackResult::Never;
				};
				self.push_stmt(block_idx, ControlNode::GlobalSet { id, value });
				StackResult::Unit
			}

			// ── Constants / refs ─────────────────────────────────────────
			ExprKind::StaticPointer { entry, offset } => {
				let node = self.node(DataNodeKind::StaticDataRef {
					entry,
					offset,
					ty: ScalarType::try_from(ty)
						.expect("static pointer must be scalar"),
				});
				StackResult::Value(node)
			}
			ExprKind::DataEnd { memory } => {
				let node = self.node(DataNodeKind::DataEnd {
					memory,
					ty: ScalarType::try_from(ty)
						.expect("memory offset must be scalar"),
				});
				StackResult::Value(node)
			}
			ExprKind::MemoryIndex { memory } => {
				let node = self.node(DataNodeKind::MemoryIndex { memory });
				StackResult::Value(node)
			}
			ExprKind::MemorySize { memory } => {
				let result_node = self.node(DataNodeKind::MemorySizeResult {
					memory,
					ty: ScalarType::try_from(ty)
						.expect("memory.size result must be scalar"),
				});
				self.push_stmt(
					block_idx,
					ControlNode::MemorySize {
						memory,
						result: result_node,
					},
				);
				StackResult::Value(result_node)
			}

			// ── Operators ─────────────────────────────────────────────────
			ExprKind::Unary { op, value } => {
				let Some(operand) =
					self.build_value(block_idx, bindings, value)
				else {
					return StackResult::Never;
				};
				let scalar = ScalarType::try_from(ty)
					.expect("a unary operator's type is scalar");
				let kind = match op {
					UnaryOp::Neg => DataNodeKind::Neg {
						operand,
						ty: scalar,
					},
					UnaryOp::Eqz => DataNodeKind::Eqz { operand },
					UnaryOp::Sqrt => DataNodeKind::Sqrt {
						operand,
						ty: scalar,
					},
					UnaryOp::Abs => DataNodeKind::Abs {
						operand,
						ty: scalar,
					},
					UnaryOp::Floor => DataNodeKind::Floor {
						operand,
						ty: scalar,
					},
					UnaryOp::Ceil => DataNodeKind::Ceil {
						operand,
						ty: scalar,
					},
					UnaryOp::Trunc => DataNodeKind::Trunc {
						operand,
						ty: scalar,
					},
					UnaryOp::Nearest => DataNodeKind::Nearest {
						operand,
						ty: scalar,
					},
				};
				StackResult::Value(self.node(kind))
			}
			ExprKind::Binary { op, lhs, rhs } => {
				self.build_binary(block_idx, bindings, ty, op, lhs, rhs)
			}
			ExprKind::Compare { op, lhs, rhs } => {
				self.build_cmp(block_idx, bindings, op, lhs, rhs)
			}
			ExprKind::Convert { op, value } => {
				let from = self.ty(value);
				let Some(operand) =
					self.build_value(block_idx, bindings, value)
				else {
					return StackResult::Never;
				};
				StackResult::Value(
					self.build_conversion(block_idx, op, from, ty, operand),
				)
			}
			// ── Aggregates ────────────────────────────────────────────────
			ExprKind::Values { values } => {
				let mir::ValueType::Aggregate {
					signature: aggregate_index,
				} = ty
				else {
					panic!("Aggregate expression must have Aggregate type")
				};
				let mut slots = Vec::with_capacity(values.len());
				for &value in self.body().list(values) {
					match self.build_expr(block_idx, bindings, value) {
						StackResult::Value(node) => slots.push(node),
						StackResult::Never => return StackResult::Never,
						StackResult::Unit => {
							panic!("a flat pack operand must be scalar")
						}
					}
				}
				assert_eq!(
					slots.len(),
					self.mir.signatures.results(aggregate_index).len()
				);
				let node = self.node(DataNodeKind::Aggregate {
					values: slots.into_boxed_slice(),
					aggregate_index,
				});
				StackResult::Value(node)
			}
			// ── Control flow ──────────────────────────────────────────────
			ExprKind::Return { value } => {
				let result = match value {
					Some(value) => self.build_expr(block_idx, bindings, value),
					None => StackResult::Unit,
				};
				// A diverging return value means this `return` never runs.
				if result == StackResult::Never {
					return StackResult::Never;
				}
				let fn_result = self.func.blocks[BODY_BLOCK as usize]
					.as_ref()
					.unwrap()
					.result;
				let merged = self.merge_stack_results(fn_result, result);
				self.func.blocks[BODY_BLOCK as usize]
					.as_mut()
					.unwrap()
					.result = merged;
				self.push_stmt(
					block_idx,
					ControlNode::Return { value: result },
				);
				StackResult::Never
			}
			ExprKind::Drop { value } => {
				match self.build_expr(block_idx, bindings, value) {
					StackResult::Never => StackResult::Never,
					_ => StackResult::Unit,
				}
			}
			ExprKind::Sequence { statements } => {
				self.build_statements(block_idx, bindings, statements)
			}
			ExprKind::Block { label, statements } => self.build_block_expr(
				block_idx,
				bindings,
				label_block(label),
				statements,
			),
			ExprKind::IfElse {
				condition,
				then,
				otherwise,
			} => self
				.build_if_else(block_idx, bindings, condition, then, otherwise),
			ExprKind::Switch {
				selector,
				cases,
				default,
			} => {
				let cases = self.body().cases(cases);
				if Self::should_use_br_table(self.ty(selector), cases) {
					self.build_switch(
						block_idx, bindings, selector, cases, default,
					)
				} else {
					self.build_switch_as_if_chain(
						block_idx, bindings, selector, cases, default,
					)
				}
			}
			ExprKind::Loop { label, body } => {
				self.build_loop(block_idx, bindings, label_block(label), body)
			}
			ExprKind::Break { label, value } => {
				let val = match value {
					Some(value) => self.build_expr(block_idx, bindings, value),
					None => StackResult::Unit,
				};
				// `break trap()` evaluates the value, which diverges, so the
				// break itself never runs and contributes nothing to the
				// target's result.
				if val == StackResult::Never {
					return StackResult::Never;
				}
				let target = label_block(label);
				// Captured *before* the merge below (which only concerns the
				// target's own trailing value) — this break's own current
				// contribution to the target's carried bindings, independent
				// of its break value. See `carried_binding_updates`.
				let carried_binding_updates =
					self.carried_binding_updates(target, bindings);
				// Establish the target's result identities; this exit keeps its
				// own raw value for the stores before committing carried locals.
				self.record_exit_value(target, val);
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
			ExprKind::Continue { label } => {
				let target = label_block(label);
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
			ExprKind::Call { function, args } => {
				self.build_call(block_idx, bindings, function, args, ty)
			}

			// ── Memory ────────────────────────────────────────────────────
			ExprKind::PointerLoad {
				pointer,
				offset,
				memory,
				access,
			} => {
				let Some(address) =
					self.build_value(block_idx, bindings, pointer)
				else {
					return StackResult::Never;
				};
				let access = MemAccess::load(access);
				let result = self
					.node(DataNodeKind::PointerLoadResult { address, access });
				self.push_stmt(
					block_idx,
					ControlNode::PointerLoad {
						address,
						offset,
						result,
						memory,
						access,
					},
				);
				StackResult::Value(result)
			}
			ExprKind::PointerStore {
				pointer,
				value,
				offset,
				memory,
				access,
			} => {
				let Some(address) =
					self.build_value(block_idx, bindings, pointer)
				else {
					return StackResult::Never;
				};
				let Some(value_node) =
					self.build_value(block_idx, bindings, value)
				else {
					return StackResult::Never;
				};
				let access = MemAccess::store(access);
				self.push_stmt(
					block_idx,
					ControlNode::PointerStore {
						address,
						offset,
						value: value_node,
						memory,
						access,
					},
				);
				StackResult::Unit
			}
			ExprKind::MemoryGrow { memory, delta } => {
				let Some(delta) = self.build_value(block_idx, bindings, delta)
				else {
					return StackResult::Never;
				};
				let result = self.node(DataNodeKind::MemoryGrowResult {
					memory,
					delta,
					ty: ScalarType::try_from(ty)
						.expect("memory.grow result must be scalar"),
				});
				self.push_stmt(
					block_idx,
					ControlNode::MemoryGrow {
						memory,
						delta,
						result,
					},
				);
				StackResult::Value(result)
			}
			ExprKind::MemoryFill {
				memory,
				dst,
				value,
				len,
			} => {
				let Some(dst) = self.build_value(block_idx, bindings, dst)
				else {
					return StackResult::Never;
				};
				let Some(val) = self.build_value(block_idx, bindings, value)
				else {
					return StackResult::Never;
				};
				let Some(len) = self.build_value(block_idx, bindings, len)
				else {
					return StackResult::Never;
				};
				self.push_stmt(
					block_idx,
					ControlNode::MemoryFill {
						memory,
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
				let Some(dst) = self.build_value(block_idx, bindings, dst)
				else {
					return StackResult::Never;
				};
				let Some(src) = self.build_value(block_idx, bindings, src)
				else {
					return StackResult::Never;
				};
				let Some(len) = self.build_value(block_idx, bindings, len)
				else {
					return StackResult::Never;
				};
				self.push_stmt(
					block_idx,
					ControlNode::MemoryCopy {
						dst_memory,
						src_memory,
						dst,
						src,
						len,
					},
				);
				StackResult::Unit
			}
		}
	}

	/// Build `expr` where a value is required. `Never` means the
	/// subexpression already left this block through a jump or `unreachable`
	/// and produced no value, so the enclosing operation cannot happen; its
	/// caller returns `Never` without emitting the operation. A `Unit` here
	/// is still a broken compiler invariant: zero-sized values are not
	/// operands.
	fn build_value(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		expr: ExprId,
	) -> Option<DataNodeIndex> {
		match self.build_expr(block_idx, bindings, expr) {
			StackResult::Value(value) => Some(value),
			StackResult::Never => None,
			StackResult::Unit => panic!("expected a value, got Unit"),
		}
	}

	/// Build `expr` as the content of `block_idx`: a `Sequence`'s statements
	/// directly, anything else as the block's one expression.
	fn build_in(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		expr: ExprId,
	) -> StackResult {
		match self.kind(expr) {
			ExprKind::Sequence { statements } => {
				self.build_statements(block_idx, bindings, statements)
			}
			_ => self.build_expr(block_idx, bindings, expr),
		}
	}

	/// Build a run of statements in order; the value is the last one's.
	fn build_statements(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		statements: ExprList,
	) -> StackResult {
		let mut result = StackResult::Unit;
		for &statement in self.body().list(statements) {
			result = self.build_expr(block_idx, bindings, statement);
			if result == StackResult::Never {
				break;
			}
		}
		result
	}

	// ── Control-flow builders ─────────────────────────────────────────────────

	/// A labelled block: a break target with a join, whose value is a
	/// `break`'s or the fallthrough's.
	fn build_block_expr(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut [Option<StackResult>],
		scope_u32: BlockIndex,
		statements: ExprList,
	) -> StackResult {
		// Genuine break target — register a real Block + JoinData before
		// building the body, mirroring build_loop's own setup: any break
		// discovered while building the body needs somewhere to commit
		// against immediately (see create_join_params's doc comment).
		let entry_placeholders = self.create_join_params(bindings, scope_u32);
		let join_index = self.func.push_join_data(JoinData {
			break_result_outputs: Vec::new(),
			entry_placeholders: entry_placeholders.clone(),
			divergent_params: Vec::new(),
		});
		self.func.blocks[scope_u32 as usize] = Some(Block {
			parent: Some(block_idx),
			statements: Vec::new(),
			result: StackResult::Never,
			kind: BlockKind::Block,
			join: Some(join_index),
		});

		let mut child = bindings.to_vec();
		let fallthrough_result =
			self.build_statements(scope_u32, &mut child, statements);

		// Falling through contributes to the same result slots as a break.
		let merged_result =
			self.record_exit_value(scope_u32, fallthrough_result);

		// `record_exit_value` stored the joined result on the block itself.
		// That is the *join's* value (carried by `BlockJoin::result` below),
		// not a value the body reads at its tail: the body's own tail is
		// just its ordinary fallthrough value. Restore it, mirroring
		// `build_loop`, which likewise saves the break result before
		// overwriting the body's result with `body_fallthrough`. Leaving the
		// merged value there makes `compute_value_placement` treat it as a
		// cross-block read and hoist it ahead of the `BlockJoin` that
		// pre-allocates its phi locals.
		self.func.blocks[scope_u32 as usize]
			.as_mut()
			.unwrap()
			.result = fallthrough_result;

		let parent_len = bindings.len();
		// Order matters: this call is what folds the fallthrough's own
		// contribution into divergent_params in the first place — must run
		// before the clone below, so the finalize loop sees the *complete*
		// union of every exit (every break already folded in as it was
		// built, plus this one). Same "union of all exits, not just one"
		// principle Phase 1 fixed for loops, applied natively here.
		let fallthrough_updates =
			self.carried_binding_updates(scope_u32, &child[..parent_len]);
		let divergent_params: Vec<DataNodeIndex> =
			self.func.join_data(scope_u32).divergent_params.clone();
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
		condition_expr: ExprId,
		then_expr: ExprId,
		else_expr: Option<ExprId>,
	) -> StackResult {
		// A diverging condition means neither branch is ever entered.
		let Some(condition) =
			self.build_value(block_idx, bindings, condition_expr)
		else {
			return StackResult::Never;
		};

		let (then_scope, then_result, then_bindings) =
			self.build_branch(block_idx, bindings, then_expr);
		let (else_result, else_bindings, else_scope) = match else_expr {
			Some(else_expr) => {
				let (scope, result, else_bindings) =
					self.build_branch(block_idx, bindings, else_expr);
				(result, else_bindings, Some(scope))
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
				then_block: then_scope,
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
		cases: &[mir::Case],
	) -> bool {
		if ScalarType::try_from(selector_ty) != Ok(ScalarType::I32) {
			return false;
		}
		if cases.len() < 3 {
			return false;
		}
		let min = cases.iter().map(|case| case.value).min().unwrap();
		let max = cases.iter().map(|case| case.value).max().unwrap();
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
			kind: BlockKind::Block,
			join: None,
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
		selector_expr: ExprId,
		cases: &[mir::Case],
		default_expr: Option<ExprId>,
	) -> StackResult {
		// A match that's just `_ => body` lowers to `Switch { cases: [],
		// default: Some(body) }` in MIR — there's no comparison to make at
		// all, so just build `body` directly with no branch. The scrutinee
		// is still evaluated once for its side effects, matching `Switch`'s
		// semantics elsewhere.
		if cases.is_empty() {
			if self.build_expr(block_idx, bindings, selector_expr)
				== StackResult::Never
			{
				return StackResult::Never;
			}
			return match default_expr {
				Some(body) => self.build_expr(block_idx, bindings, body),
				None => {
					self.push_stmt(block_idx, ControlNode::Unreachable);
					StackResult::Never
				}
			};
		}

		let Some(selector) =
			self.build_value(block_idx, bindings, selector_expr)
		else {
			return StackResult::Never;
		};
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
					let (scope, result, scope_bindings) =
						self.build_branch(last_container, bindings, body);
					(scope, result, scope_bindings)
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
			let mir::Case {
				value: discriminant,
				body: case_body,
			} = cases[i];
			let container = containers[i];
			let (condition, then_scope, then_result, then_bindings) = self
				.build_if_chain_then_branch(
					container,
					bindings,
					selector,
					selector_ty,
					discriminant,
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

			// A container beyond the outermost one contains the next case's
			// `if`/`else` and falls through with its merged result. It was
			// created as an empty synthetic block (`Never`); leaving that
			// result in place makes the scheduler append an unconditional
			// `unreachable` after the inner chain.
			if i > 0 {
				self.func.blocks[container as usize]
					.as_mut()
					.unwrap()
					.result = result;
			}

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
		case_body: ExprId,
	) -> (
		DataNodeIndex,
		BlockIndex,
		StackResult,
		Vec<Option<StackResult>>,
	) {
		let const_node = self.int(discriminant, selector_ty);
		let condition = self.node(DataNodeKind::Eq {
			left: selector,
			right: const_node,
			ty: selector_ty,
		});

		let (then_scope, then_result, then_bindings) =
			self.build_branch(container, bindings, case_body);
		(condition, then_scope, then_result, then_bindings)
	}

	fn build_switch(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		selector_expr: ExprId,
		mir_cases: &[mir::Case],
		default_expr: Option<ExprId>,
	) -> StackResult {
		let Some(selector) =
			self.build_value(block_idx, bindings, selector_expr)
		else {
			return StackResult::Never;
		};

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
		for (i, case) in mir_cases.iter().enumerate() {
			arms.push(self.build_switch_arm(
				case_wasm_parent[i],
				bindings,
				Some(case.value),
				case.body,
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
				let scalar_count =
					self.mir.signatures.results(aggregate_index).len();
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
							PerArmSlot::Scalars(self.scalars_of(n))
						}
						other => PerArmSlot::NoValue(other),
					})
					.collect();

				let merged_values: Box<[DataNodeIndex]> = (0..scalar_count)
					.map(|field| {
						// Every arm structurally owns this field (it's part
						// of the same aggregate type on every arm), so this
						// is always `Some` — never subject to the "private
						// to one arm" exclusion above.
						let field_values: Vec<Option<StackResult>> = per_arm
							.iter()
							.map(|slot| {
								Some(match slot {
									PerArmSlot::Scalars(values) => {
										StackResult::Value(values[field])
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
					values: merged_values,
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
		body: ExprId,
	) -> SwitchArmBuild {
		let (scope, result, bindings) =
			self.build_branch(parent_block, parent_bindings, body);
		SwitchArmBuild {
			discriminant,
			scope,
			result,
			bindings,
		}
	}

	/// A branch of an `if` or a `match`: `body` built in a block of its own
	/// under `parent`, from a copy of `bindings`. Returns the block, the
	/// branch's value and its bindings at its end.
	fn build_branch(
		&mut self,
		parent: BlockIndex,
		bindings: &[Option<StackResult>],
		body: ExprId,
	) -> (BlockIndex, StackResult, Vec<Option<StackResult>>) {
		let block = self.push_synthetic_block(parent);
		let mut branch_bindings = bindings.to_vec();
		let result = self.build_in(block, &mut branch_bindings, body);
		self.func.blocks[block as usize].as_mut().unwrap().result = result;
		(block, result, branch_bindings)
	}

	fn build_loop(
		&mut self,
		parent_block: BlockIndex,
		bindings: &mut [Option<StackResult>],
		body_block: BlockIndex,
		body_expr: ExprId,
	) -> StackResult {
		// Create loop-param placeholders for all parent bindings — one per
		// entry, so this is already the full function-wide length; no
		// further growth needed for the body scope's own locals (every
		// local, function-wide, already has a slot from function-build
		// start).
		let entry_placeholders = self.create_loop_params(bindings, body_block);
		let mut loop_bindings = entry_placeholders.clone();

		let join_index = self.func.push_join_data(JoinData {
			break_result_outputs: Vec::new(),
			entry_placeholders: entry_placeholders.clone(),
			divergent_params: Vec::new(),
		});
		self.func.blocks[body_block as usize] = Some(Block {
			parent: Some(parent_block),
			statements: Vec::new(),
			result: StackResult::Never,
			kind: BlockKind::Loop,
			join: Some(join_index),
		});
		let body_fallthrough =
			self.build_in(body_block, &mut loop_bindings, body_expr);
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
			self.func.join_data(body_block).divergent_params.clone();
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
		function: mir::FunctionId,
		arguments: ExprList,
		result_ty: mir::ValueType,
	) -> StackResult {
		let callee_sig = self.mir.function(function).signature;
		let callee = self.node(DataNodeKind::FunctionRef { id: function });
		// Zero-sized arguments (e.g. a `Memory`-typed handle) carry no
		// runtime bits and occupy no WASM param slot (`Signatures::scalars`
		// gives them none) — drop them here to match, rather than
		// materializing a nonexistent `Value`.
		// A diverging argument stops the call: it never reaches the callee,
		// so later arguments are not evaluated either.
		let mut args = Vec::with_capacity(arguments.len());
		for &argument in self.body().list(arguments) {
			match self.build_expr(block_idx, bindings, argument) {
				StackResult::Value(idx) => args.push(idx),
				StackResult::Unit => {}
				StackResult::Never => return StackResult::Never,
			}
		}
		let args = args.into_boxed_slice();

		let result =
			match result_ty {
				// A call whose declared result is `!` still runs for its effects,
				// but it never hands control back to this block.
				mir::ValueType::Never => StackResult::Never,
				mir::ValueType::Unit => StackResult::Unit,
				mir::ValueType::Aggregate {
					signature: aggregate_index,
				} => StackResult::Value(self.node(
					DataNodeKind::AggregateCallResult { aggregate_index },
				)),
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
									params,
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
									params,
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
	/// `JoinData::divergent_params`) of scalar `LoopParam` nodes some
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
						result_scalars,
					))
				} else {
					StackResult::Value(current)
				});
			}
		}
	}

	/// `(carried_node, current_value_node)` pairs, decomposed to scalars —
	/// the target's own carried bindings (`JoinData::entry_placeholders`,
	/// shared shape for a loop or a block-join) as of this exact point,
	/// wherever they differ from what the carried node itself currently
	/// holds. `Break`/`Continue` use this to commit their own current
	/// values before jumping: the target's normal "commit accumulated
	/// bindings, then branch back/fall through" tail code
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
		// Cloned out up front rather than indexed per-iteration: `self.func`
		// would otherwise need re-borrowing on every loop, and
		// `collect_scalar_loop_param_updates` below already needs `&mut self`.
		let carried: Vec<Option<StackResult>> =
			self.func.join_data(target).entry_placeholders.clone();
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
		// running record — see `JoinData::divergent_params`'s doc comment.
		// `updates` is typically tiny, so a linear dedup check stays cheap.
		let divergent = &mut self.func.join_data_mut(target).divergent_params;
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

	/// The first value-producing exit gives the target stable result slots;
	/// every break/fallthrough writes its own value into those same slots.
	/// Even a single exit cannot return its raw expression: committing carried
	/// locals can change the operands before an outside consumer evaluates it.
	fn record_exit_value(
		&mut self,
		target: BlockIndex,
		val: StackResult,
	) -> StackResult {
		let existing =
			self.func.blocks[target as usize].as_ref().unwrap().result;
		let merged = match (existing, val) {
			(StackResult::Never, StackResult::Value(value)) => {
				let node_type =
					self.func.data_nodes[value as usize].kind.node_type();
				let outputs = match node_type {
					NodeType::Scalar(ty) => {
						vec![self.func.push_join_param(target, ty)]
					}
					NodeType::Aggregate(aggregate_index) => self
						.mir
						.signatures
						.results(aggregate_index)
						.iter()
						.map(|&ty| {
							let ty = ScalarType::try_from(ty)
								.expect("a pack slot is scalar");
							self.func.push_join_param(target, ty)
						})
						.collect(),
				};
				let result = match node_type {
					NodeType::Scalar(_) => outputs[0],
					NodeType::Aggregate(aggregate_index) => {
						// The pack and join table each own their scalar list.
						self.aggregate_from_scalars(
							aggregate_index,
							outputs.clone(),
						)
					}
				};
				self.func.join_data_mut(target).break_result_outputs = outputs;
				StackResult::Value(result)
			}
			(StackResult::Never, other) | (other, StackResult::Never) => other,
			(StackResult::Unit, StackResult::Unit) => StackResult::Unit,
			(StackResult::Value(l), StackResult::Value(r)) => {
				debug_assert_eq!(
					self.func.data_nodes[l as usize].kind.node_type(),
					self.func.data_nodes[r as usize].kind.node_type(),
					"all exits have the target's checked result type"
				);
				StackResult::Value(l)
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
				self.aggregate_from_scalars(aggregate_index, merged)
			}
			_ => panic!("type mismatch when merging branch values"),
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
			self.mir.signatures.results(aggregate_index)[usize::from(scalar)],
		)
		.expect("a ScalarTable entry is scalar by construction");
		self.node(DataNodeKind::AggregateGet {
			aggregate,
			scalar,
			ty,
		})
	}

	/// The aggregate shape carried by any aggregate-typed node.
	fn aggregate_index_of(&self, node: DataNodeIndex) -> mir::SignatureIndex {
		match self.func.data_nodes[node as usize].kind.node_type() {
			NodeType::Aggregate(index) => index,
			NodeType::Scalar(_) => panic!("expected an aggregate-typed node"),
		}
	}

	/// Read a flat pack's scalar nodes. Call results need explicit scalar
	/// projections; materialized packs already contain the exact flat list.
	fn scalars_of(&mut self, node: DataNodeIndex) -> Vec<DataNodeIndex> {
		let mir = self.mir;
		match self.func.data_nodes[node as usize].kind.clone() {
			DataNodeKind::Aggregate { values, .. } => values.into_vec(),
			// No field sub-nodes — the values live on the multi-return stack,
			// so each one has to be named by an explicit projection.
			DataNodeKind::AggregateCallResult { aggregate_index } => {
				let count = mir.signatures.results(aggregate_index).len();
				(0..count as u32)
					.map(|i| {
						self.project_scalar(node, mir::ScalarIndex::new(i))
					})
					.collect()
			}
			_ => panic!("expected aggregate node"),
		}
	}

	/// Group scalar nodes into a flat pack. No source field tree is rebuilt.
	fn aggregate_from_scalars(
		&mut self,
		aggregate_index: mir::SignatureIndex,
		values: Vec<DataNodeIndex>,
	) -> DataNodeIndex {
		let mir = self.mir;
		let scalars = mir.signatures.results(aggregate_index);
		debug_assert_eq!(
			values.len(),
			scalars.len(),
			"value count must match the aggregate's scalar count"
		);
		debug_assert!(values.iter().all(|&node| matches!(
			self.func.data_nodes[node as usize].kind.node_type(),
			NodeType::Scalar(_)
		)));
		self.node(DataNodeKind::Aggregate {
			values: values.into_boxed_slice(),
			aggregate_index,
		})
	}

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

	/// Arithmetic, bitwise, and shift operators: the node for the opcode.
	/// Potentially trapping integer division/remainder are control
	/// operations; float division stays in the freely movable data graph.
	fn build_binary(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		node_ty: mir::ValueType,
		op: BinaryOp,
		lhs: ExprId,
		rhs: ExprId,
	) -> StackResult {
		use DataNodeKind as N;

		let ty =
			ScalarType::try_from(node_ty).expect("binary op must be scalar");
		let Some(left) = self.build_value(block_idx, bindings, lhs) else {
			return StackResult::Never;
		};
		let Some(right) = self.build_value(block_idx, bindings, rhs) else {
			return StackResult::Never;
		};

		let trapping = match op {
			BinaryOp::DivS => Some(TrappingOp::DivS { left, right, ty }),
			BinaryOp::DivU => Some(TrappingOp::DivU { left, right, ty }),
			BinaryOp::RemS => Some(TrappingOp::RemS { left, right, ty }),
			BinaryOp::RemU => Some(TrappingOp::RemU { left, right, ty }),
			_ => None,
		};
		if let Some(trapping) = trapping {
			debug_assert!(op.can_trap());
			return StackResult::Value(
				self.build_trapping(block_idx, trapping),
			);
		}

		let kind = match op {
			BinaryOp::Add => N::Add { left, right, ty },
			BinaryOp::Sub => N::Sub { left, right, ty },
			BinaryOp::Mul => N::Mul { left, right, ty },
			BinaryOp::Div => N::Div { left, right, ty },
			BinaryOp::And => N::BitAnd { left, right, ty },
			BinaryOp::Or => N::BitOr { left, right, ty },
			BinaryOp::Xor => N::BitXor { left, right, ty },
			BinaryOp::Shl => N::Shl { left, right, ty },
			BinaryOp::ShrS => N::ShrS { left, right, ty },
			BinaryOp::ShrU => N::ShrU { left, right, ty },
			BinaryOp::Min => N::Min { left, right, ty },
			BinaryOp::Max => N::Max { left, right, ty },
			BinaryOp::Copysign => N::Copysign { left, right, ty },
			BinaryOp::DivS
			| BinaryOp::DivU
			| BinaryOp::RemS
			| BinaryOp::RemU => {
				unreachable!("built as a trapping operation")
			}
		};
		StackResult::Value(self.node(kind))
	}

	/// Constant-fold only when the operation is proved not to trap. Otherwise
	/// its control producer survives even if every consumer discards the value.
	fn build_trapping(
		&mut self,
		block_idx: BlockIndex,
		op: TrappingOp,
	) -> DataNodeIndex {
		if let TrappingOp::DivS { left, right, .. }
		| TrappingOp::DivU { left, right, .. } = op
			&& self.unwrap_int(right) == Some(1)
		{
			return left;
		}
		if let Some(value) = self.fold_trapping_int(op) {
			return self.int(value, op.result_type());
		}
		let result = self.node(DataNodeKind::TrappingResult {
			ty: op.result_type(),
		});
		self.push_stmt(block_idx, ControlNode::Trapping { op, result });
		result
	}

	fn fold_trapping_int(&self, op: TrappingOp) -> Option<i64> {
		let (left, right, ty) = match op {
			TrappingOp::DivS { left, right, ty }
			| TrappingOp::DivU { left, right, ty }
			| TrappingOp::RemS { left, right, ty }
			| TrappingOp::RemU { left, right, ty } => (left, right, ty),
			_ => return None,
		};
		let l = self.unwrap_int(left)?;
		let r = self.unwrap_int(right)?;
		use ScalarType::{I32, I64};
		Some(match (op, ty) {
			(TrappingOp::DivS { .. }, I32) => {
				(l as i32).checked_div(r as i32)? as i64
			}
			(TrappingOp::DivS { .. }, I64) => l.checked_div(r)?,
			(TrappingOp::DivU { .. }, I32) => {
				(l as u32).checked_div(r as u32)? as i32 as i64
			}
			(TrappingOp::DivU { .. }, I64) => {
				(l as u64).checked_div(r as u64)? as i64
			}
			// Wasm rem_s(INT_MIN, -1) is zero, not an overflow trap.
			(TrappingOp::RemS { .. }, I32) if r as i32 != 0 => {
				(l as i32).wrapping_rem(r as i32) as i64
			}
			(TrappingOp::RemS { .. }, I64) if r != 0 => l.wrapping_rem(r),
			(TrappingOp::RemU { .. }, I32) => {
				(l as u32).checked_rem(r as u32)? as i32 as i64
			}
			(TrappingOp::RemU { .. }, I64) => {
				(l as u64).checked_rem(r as u64)? as i64
			}
			_ => return None,
		})
	}

	/// The node for `op` from `from` to `to`; a truncation, which can trap,
	/// in program order.
	fn build_conversion(
		&mut self,
		block_idx: BlockIndex,
		op: mir::ConvertOp,
		from: mir::ValueType,
		to: mir::ValueType,
		operand: DataNodeIndex,
	) -> DataNodeIndex {
		use DataNodeKind as N;
		use ScalarType::{F32, F64, I32, I64};
		use TrappingOp as T;
		use mir::ConvertOp as C;
		let source =
			ScalarType::try_from(from).expect("a conversion is scalar");
		let target = ScalarType::try_from(to).expect("a conversion is scalar");
		let trapping = match (op, source, target) {
			(C::TruncU, F32, I32) => Some(T::U32TruncF32 { operand }),
			(C::TruncS, F32, I32) => Some(T::I32TruncF32 { operand }),
			(C::TruncU, F64, I32) => Some(T::U32TruncF64 { operand }),
			(C::TruncS, F64, I32) => Some(T::I32TruncF64 { operand }),
			(C::TruncU, F32, I64) => Some(T::U64TruncF32 { operand }),
			(C::TruncS, F32, I64) => Some(T::I64TruncF32 { operand }),
			(C::TruncU, F64, I64) => Some(T::U64TruncF64 { operand }),
			(C::TruncS, F64, I64) => Some(T::I64TruncF64 { operand }),
			_ => None,
		};
		if let Some(trapping) = trapping {
			debug_assert!(op.can_trap());
			return self.build_trapping(block_idx, trapping);
		}
		let kind = match (op, source, target) {
			(C::ExtendU, I32, I64) => N::I64ExtendI32U { operand },
			(C::ExtendS, I32, I64) => N::I64ExtendI32S { operand },
			(C::Wrap, I64, I32) => N::I32WrapI64 { operand },
			(C::ConvertU, I32, F32) => N::F32ConvertU32 { operand },
			(C::ConvertS, I32, F32) => N::F32ConvertI32 { operand },
			(C::ConvertU, I64, F32) => N::F32ConvertU64 { operand },
			(C::ConvertS, I64, F32) => N::F32ConvertI64 { operand },
			(C::ConvertU, I32, F64) => N::F64ConvertU32 { operand },
			(C::ConvertS, I32, F64) => N::F64ConvertI32 { operand },
			(C::ConvertU, I64, F64) => N::F64ConvertU64 { operand },
			(C::ConvertS, I64, F64) => N::F64ConvertI64 { operand },
			(C::Promote, F32, F64) => N::F64PromoteF32 { operand },
			(C::Demote, F64, F32) => N::F32DemoteF64 { operand },
			(C::Reinterpret, F32, I32) => N::I32ReinterpretF32 { operand },
			(C::Reinterpret, I32, F32) => N::F32ReinterpretI32 { operand },
			(C::Reinterpret, F64, I64) => N::I64ReinterpretF64 { operand },
			(C::Reinterpret, I64, F64) => N::F64ReinterpretI64 { operand },
			_ => unreachable!("`verify` checks a conversion's types"),
		};
		self.node(kind)
	}

	/// Comparison operators. The `ScalarType` comes from the built operand
	/// node; a float comparison is the signed node of a float type.
	fn build_cmp(
		&mut self,
		block_idx: BlockIndex,
		bindings: &mut Vec<Option<StackResult>>,
		op: CompareOp,
		lhs: ExprId,
		rhs: ExprId,
	) -> StackResult {
		use DataNodeKind as N;

		let Some(left) = self.build_value(block_idx, bindings, lhs) else {
			return StackResult::Never;
		};
		let Some(right) = self.build_value(block_idx, bindings, rhs) else {
			return StackResult::Never;
		};
		let ty = self.func.data_nodes[left as usize].kind.unwrap_scalar();

		let kind = match op {
			CompareOp::Eq => N::Eq { left, right, ty },
			CompareOp::Ne => N::NotEq { left, right, ty },
			CompareOp::LtU => N::LtU { left, right, ty },
			CompareOp::LtS | CompareOp::Lt => N::LtS { left, right, ty },
			CompareOp::LeU => N::LtEqU { left, right, ty },
			CompareOp::LeS | CompareOp::Le => N::LtEqS { left, right, ty },
			CompareOp::GtU => N::GtU { left, right, ty },
			CompareOp::GtS | CompareOp::Gt => N::GtS { left, right, ty },
			CompareOp::GeU => N::GtEqU { left, right, ty },
			CompareOp::GeS | CompareOp::Ge => N::GtEqS { left, right, ty },
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
			mir::ValueType::Aggregate {
				signature: aggregate_index,
			} => {
				let mir = self.mir;
				let values: Box<[_]> = mir
					.signatures
					.results(aggregate_index)
					.iter()
					.map(|&ty| self.default_value(ty).unwrap_value())
					.collect();
				StackResult::Value(self.node(DataNodeKind::Aggregate {
					values,
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
					_ => self.int(0, scalar_ty),
				};
				StackResult::Value(node)
			}
		}
	}

	/// If `aggregate` is a literal `Aggregate`, the node already holding the
	/// value at `scalar`. A single lookup replaces recursive field traversal.
	fn fold_scalar_projection(
		&self,
		aggregate: DataNodeIndex,
		scalar: mir::ScalarIndex,
	) -> Option<DataNodeIndex> {
		let DataNodeKind::Aggregate { values, .. } =
			&self.func.data_nodes[aggregate as usize].kind
		else {
			return None;
		};
		Some(values[usize::from(scalar)])
	}

	// ── Node construction ─────────────────────────────────────────────────────

	/// The primary way to create a node. Applies algebraic simplifications
	/// then interns via CSE. Call `func.intern_node` directly only when the
	/// kind is already canonical (e.g. through `int` for a freshly computed
	/// integer constant).
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

	/// Create an integer constant in the canonical form its Wasm width stores:
	/// an `I32` value is sign-extended to its 32-bit pattern, while an `I64`
	/// value is already full-width. Every `Int` node is built through this, so
	/// folds may compare the stored value directly; emission truncates it back
	/// with `I32Const(value as i32)`.
	fn int(&mut self, value: i64, ty: ScalarType) -> DataNodeIndex {
		let value = match ty {
			ScalarType::I32 => value as i32 as i64,
			ScalarType::I64 => value,
			_ => unreachable!("Int node with float type"),
		};
		self.func.intern_node(DataNodeKind::Int { value, ty })
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
				return Some(self.int(result, *ty));
			}
			DataNodeKind::BitNot { operand, ty } => {
				let v = self.unwrap_int(*operand)?;
				let result = match ty {
					ScalarType::I32 => !(v as i32) as i64,
					ScalarType::I64 => !v,
					_ => return None,
				};
				return Some(self.int(result, *ty));
			}
			DataNodeKind::Eqz { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.int((v == 0) as i64, ScalarType::I32));
			}
			DataNodeKind::I32WrapI64 { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.int(v as i32 as i64, ScalarType::I32));
			}
			DataNodeKind::I64ExtendI32S { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.int(v as i32 as i64, ScalarType::I64));
			}
			DataNodeKind::I64ExtendI32U { operand } => {
				let v = self.unwrap_int(*operand)?;
				return Some(self.int(v as u32 as i64, ScalarType::I64));
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
				return Some(self.int(result, ScalarType::I32));
			}
			_ => {}
		}

		// ── Binary arithmetic on two Int constants ────────────────────────
		let (left, right, ty) = match *kind {
			DataNodeKind::Add { left, right, ty } => (left, right, ty),
			DataNodeKind::Sub { left, right, ty } => (left, right, ty),
			DataNodeKind::Mul { left, right, ty } => (left, right, ty),
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

		Some(self.int(result, ty))
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
				let shift_node = self.int(shift, ty);
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
}
