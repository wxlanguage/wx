//! A MIR body as a [`wasm::Function`]: each node after its children, one
//! instruction per node, choosing nothing (`notes/mir-pipeline.md`, "Codegen:
//! MIR → wasm"). The forms a node has no single instruction for are fixed:
//!
//! - a `Loop` that something leaves is a `block` around a `loop`, its label
//!   both: a `Break` exits the `block`, a `Continue` restarts the `loop`, and
//!   a body that falls off its end restarts it (`br 0`);
//! - a `Switch` is a `br_table` over nested blocks when [`uses_br_table`],
//!   else a chain of `if`s comparing the selector, kept in its own local
//!   when more than one comparison reads it;
//! - a structured node of type `Never` is followed by `unreachable`, since
//!   Wasm types what follows its `end` by its block type, not by whether
//!   control reaches it;
//! - once a child diverges, the rest of its parent is not emitted: the
//!   stack is polymorphic there, and a value pushed by dead code would still
//!   be checked against the enclosing block's type.

use crate::mir::{self, Code, ExprId, ExprKind, MIR, ValueType};
use crate::wasm::{self, BlockType, Instruction, Local, MemArg, ScalarType};

/// Whether a `Switch` on `selector` is a `br_table`: at least three cases,
/// dense enough that the table is at most twice as long as the cases and at
/// most 512 entries, on an `I32` selector (the table's index is one; an
/// `I64` one shifted and wrapped to it could land on a case). Otherwise it
/// is a chain of comparisons.
pub fn uses_br_table(selector: ValueType, cases: &[mir::Case]) -> bool {
	if selector != ValueType::I32 || cases.len() < 3 {
		return false;
	}
	let min = cases.iter().map(|case| case.value).min().unwrap();
	let max = cases.iter().map(|case| case.value).max().unwrap();
	let range = max as i128 - min as i128 + 1;
	range <= 512 && range <= 2 * cases.len() as i128
}

/// Linearize with one work stack. Lists advance one child at a time, so wide
/// argument/statement lists do not become equally wide pending-task lists.
pub fn linearize(mir: &MIR, code: &Code) -> wasm::Function {
	let locals = code
		.locals
		.iter()
		.map(|local| Local {
			ty: ScalarType::try_from(local.ty).expect("a local is a scalar"),
		})
		.collect();
	let mut linearizer = Linearizer {
		mir,
		body: &code.body,
		function: wasm::Function {
			locals,
			body: Vec::with_capacity(code.body.len()),
			br_table_depths: Vec::new(),
		},
		depth: 0,
		labels: vec![Label::Block(0); code.label_count as usize],
		tasks: Vec::new(),
	};
	linearizer.run(code.root);
	linearizer.function
}

struct Linearizer<'a> {
	mir: &'a MIR,
	body: &'a mir::Body,
	function: wasm::Function,
	/// Number of open structured instructions; labels store absolute frames.
	depth: u32,
	labels: Vec<Label>,
	/// Pending expressions and the work to resume after their children.
	tasks: Vec<Task>,
}

/// Operand/statement cursors can stop at divergence. Closing tasks remain on
/// the stack independently, so even a non-returning body closes its constructs.
enum Task {
	Expr(ExprId),
	AfterOperands(ExprId),
	Operands {
		expression: ExprId,
		next: u32,
	},
	Statements {
		expression: ExprId,
		next: u32,
	},
	Drop(ValueType),
	Else,
	Close {
		expression: ExprId,
		count: u32,
	},
	FinishLoop(ExprId),
	Branch {
		body: ExprId,
		frame: u32,
	},
	TableDispatch {
		expression: ExprId,
		after: u32,
	},
	TableCases {
		expression: ExprId,
		next: u32,
		after: u32,
	},
	IfCases {
		expression: ExprId,
		next: u32,
		/// This switch's saved selector; unnecessary for zero or one case.
		selector_local: Option<u32>,
	},
}

/// A loop's continue target is its loop frame; its break target is the
/// surrounding block, one frame earlier.
#[derive(Clone, Copy)]
enum Label {
	Block(u32),
	Loop(u32),
}

impl<'a> Linearizer<'a> {
	fn push(&mut self, instruction: Instruction) {
		self.function.body.push(instruction);
	}

	fn ty(&self, expr: ExprId) -> ValueType {
		self.body.ty(expr)
	}

	fn diverges(&self, expr: ExprId) -> bool {
		self.ty(expr) == ValueType::Never
	}

	/// How many Wasm values a value of `ty` is.
	fn arity(&self, ty: ValueType) -> usize {
		match ty {
			ValueType::Unit | ValueType::Never => 0,
			ValueType::Aggregate { signature } => {
				self.mir.signatures.results(signature).len()
			}
			_ => 1,
		}
	}

	fn block_type(&self, ty: ValueType) -> BlockType {
		match ty {
			ValueType::Unit | ValueType::Never => BlockType::Empty,
			ValueType::Aggregate { signature } => BlockType::Results(signature),
			ty => BlockType::Value(scalar(ty)),
		}
	}

	/// Open a structured instruction; returns its frame.
	fn open(&mut self, instruction: Instruction) -> u32 {
		self.push(instruction);
		self.depth += 1;
		self.depth - 1
	}

	fn close(&mut self) {
		self.push(Instruction::End);
		self.depth -= 1;
	}

	fn branch_depth(&self, frame: u32) -> u32 {
		self.depth - 1 - frame
	}

	fn run(&mut self, root: ExprId) {
		self.tasks.push(Task::Expr(root));
		while let Some(task) = self.tasks.pop() {
			match task {
				Task::Expr(expr) => self.schedule(expr),
				Task::AfterOperands(expr) => self.after_operands(expr),
				Task::Operands { expression, next } => {
					let (ExprKind::Values { values }
					| ExprKind::Call { args: values, .. }) = self.body.kind(expression)
					else {
						unreachable!("only values and calls have operand lists")
					};
					if let Some(&operand) =
						self.body.list(values).get(next as usize)
					{
						if !self.diverges(operand) {
							self.tasks.push(Task::Operands {
								expression,
								next: next + 1,
							});
						}
						self.tasks.push(Task::Expr(operand));
					} else {
						self.tasks.push(Task::AfterOperands(expression));
					}
				}
				Task::Statements { expression, next } => {
					let (statements, keep_last) = match self
						.body
						.kind(expression)
					{
						ExprKind::Sequence { statements } => (statements, true),
						ExprKind::Block { statements, .. } => {
							(statements, self.ty(expression) != ValueType::Unit)
						}
						_ => unreachable!(
							"only sequences and blocks have statement lists"
						),
					};
					let statements = self.body.list(statements);
					if let Some(&statement) = statements.get(next as usize) {
						if !self.diverges(statement) {
							self.tasks.push(Task::Statements {
								expression,
								next: next + 1,
							});
							if !(keep_last
								&& next as usize + 1 == statements.len())
							{
								self.tasks.push(Task::Drop(self.ty(statement)));
							}
						}
						self.tasks.push(Task::Expr(statement));
					}
				}
				Task::Drop(ty) => self.drop_values(ty),
				Task::Else => self.push(Instruction::Else),
				Task::Close { expression, count } => {
					for _ in 0..count {
						self.close();
					}
					self.after_structured(self.ty(expression));
				}
				Task::FinishLoop(expression) => {
					let ExprKind::Loop { body, .. } =
						self.body.kind(expression)
					else {
						unreachable!("a loop continuation requires a loop")
					};
					let ty = self.ty(expression);
					if !self.diverges(body) {
						self.drop_values(self.ty(body));
						self.push(Instruction::Br(0));
					}
					self.close();
					if ty != ValueType::Never {
						self.push(Instruction::Unreachable);
						self.close();
					}
					self.after_structured(ty);
				}
				Task::Branch { body, frame } => {
					if !self.diverges(body) {
						self.push(Instruction::Br(self.branch_depth(frame)));
					}
				}
				Task::TableDispatch { expression, after } => {
					self.table_dispatch(expression, after)
				}
				Task::TableCases {
					expression,
					next,
					after,
				} => {
					let ExprKind::Switch { cases, default, .. } =
						self.body.kind(expression)
					else {
						unreachable!("a case continuation requires a switch")
					};
					self.close();
					if let Some(case) =
						self.body.cases(cases).get(next as usize)
					{
						self.tasks.push(Task::TableCases {
							expression,
							next: next + 1,
							after,
						});
						self.tasks.push(Task::Branch {
							body: case.body,
							frame: after,
						});
						self.tasks.push(Task::Expr(case.body));
					} else if let Some(default) = default {
						self.tasks.push(Task::Expr(default));
					} else {
						self.push(Instruction::Unreachable);
					}
				}
				Task::IfCases {
					expression,
					next,
					selector_local,
				} => {
					let ExprKind::Switch {
						selector,
						cases,
						default,
					} = self.body.kind(expression)
					else {
						unreachable!("a case continuation requires a switch")
					};
					let selector = scalar(self.ty(selector));
					let cases = self.body.cases(cases);
					if let Some(case) = cases.get(next as usize) {
						if let Some(local) = selector_local {
							self.push(Instruction::LocalGet(local));
						}
						self.push(match selector {
							ScalarType::I32 => {
								Instruction::I32Const(case.value as i32)
							}
							ScalarType::I64 => {
								Instruction::I64Const(case.value)
							}
							_ => unreachable!("a switch on a float"),
						});
						self.push(Instruction::Compare(
							mir::CompareOp::Eq,
							selector,
						));
						self.open(Instruction::If {
							ty: self.block_type(self.ty(expression)),
						});
						self.tasks.push(Task::IfCases {
							expression,
							next: next + 1,
							selector_local,
						});
						self.tasks.push(Task::Else);
						self.tasks.push(Task::Expr(case.body));
					} else if let Some(default) = default {
						self.tasks.push(Task::Expr(default));
					} else {
						self.push(Instruction::Unreachable);
					}
				}
			}
		}
		debug_assert_eq!(self.depth, 0);
	}

	/// Fixed-arity operands have at most three entries. Schedule only through
	/// the first diverging operand; the parent's instruction then cannot run.
	fn schedule_operands<const N: usize>(
		&mut self,
		operands: [ExprId; N],
		parent: ExprId,
	) {
		let end =
			match operands.iter().position(|&operand| self.diverges(operand)) {
				Some(index) => index + 1,
				None => {
					self.tasks.push(Task::AfterOperands(parent));
					N
				}
			};
		self.tasks
			.extend(operands[..end].iter().rev().copied().map(Task::Expr));
	}

	fn schedule(&mut self, expr: ExprId) {
		let ty = self.ty(expr);
		match self.body.kind(expr) {
			ExprKind::Unary { value, .. }
			| ExprKind::Convert { value, .. }
			| ExprKind::LocalSet { value, .. }
			| ExprKind::SetLocals { value, .. }
			| ExprKind::GlobalSet { value, .. }
			| ExprKind::Drop { value }
			| ExprKind::MemoryGrow { delta: value, .. }
			| ExprKind::PointerLoad { pointer: value, .. } => {
				self.schedule_operands([value], expr)
			}
			ExprKind::Binary { lhs, rhs, .. }
			| ExprKind::Compare { lhs, rhs, .. } => {
				self.schedule_operands([lhs, rhs], expr)
			}
			ExprKind::PointerStore { pointer, value, .. } => {
				self.schedule_operands([pointer, value], expr)
			}
			ExprKind::MemoryFill {
				dst, value, len, ..
			} => self.schedule_operands([dst, value, len], expr),
			ExprKind::MemoryCopy { dst, src, len, .. } => {
				self.schedule_operands([dst, src, len], expr)
			}
			ExprKind::Values { .. } | ExprKind::Call { .. } => {
				self.tasks.push(Task::Operands {
					expression: expr,
					next: 0,
				});
			}
			ExprKind::Break { value, .. } | ExprKind::Return { value } => {
				match value {
					Some(value) => self.schedule_operands([value], expr),
					None => self.tasks.push(Task::AfterOperands(expr)),
				}
			}
			ExprKind::Sequence { .. } => {
				self.tasks.push(Task::Statements {
					expression: expr,
					next: 0,
				});
			}
			ExprKind::Block { label, .. } => {
				let frame = self.open(Instruction::Block {
					ty: self.block_type(ty),
				});
				self.labels[usize::from(label)] = Label::Block(frame);
				self.tasks.push(Task::Close {
					expression: expr,
					count: 1,
				});
				self.tasks.push(Task::Statements {
					expression: expr,
					next: 0,
				});
			}
			ExprKind::Loop { label, body } => {
				if ty != ValueType::Never {
					self.open(Instruction::Block {
						ty: self.block_type(ty),
					});
				}
				let frame = self.open(Instruction::Loop {
					ty: BlockType::Empty,
				});
				self.labels[usize::from(label)] = Label::Loop(frame);
				self.tasks.push(Task::FinishLoop(expr));
				self.tasks.push(Task::Expr(body));
			}
			ExprKind::IfElse { condition, .. } => {
				self.schedule_operands([condition], expr)
			}
			ExprKind::Switch {
				selector, cases, ..
			} => {
				if self.diverges(selector) {
					self.tasks.push(Task::Expr(selector));
				} else if uses_br_table(
					self.ty(selector),
					self.body.cases(cases),
				) {
					let after = self.open(Instruction::Block {
						ty: self.block_type(ty),
					});
					self.open(Instruction::Block {
						ty: BlockType::Empty,
					});
					for _ in self.body.cases(cases) {
						self.open(Instruction::Block {
							ty: BlockType::Empty,
						});
					}
					self.tasks.push(Task::TableDispatch {
						expression: expr,
						after,
					});
					self.tasks.push(Task::Expr(selector));
				} else {
					self.schedule_operands([selector], expr);
				}
			}
			// Leaves have no children to schedule.
			ExprKind::Noop
			| ExprKind::Unreachable
			| ExprKind::Int { .. }
			| ExprKind::Float { .. }
			| ExprKind::LocalGet { .. }
			| ExprKind::Global { .. }
			| ExprKind::Continue { .. }
			| ExprKind::DataEnd { .. }
			| ExprKind::MemoryIndex { .. }
			| ExprKind::MemorySize { .. }
			| ExprKind::StaticPointer { .. } => self.after_operands(expr),
		}
	}

	/// Emit a node after its operands. All expression kinds use the same
	/// scheduling rules; effects and arithmetic differ only in instructions.
	fn after_operands(&mut self, expr: ExprId) {
		let ty = self.ty(expr);
		match self.body.kind(expr) {
			ExprKind::Noop | ExprKind::Values { .. } => {}
			ExprKind::Unreachable => self.push(Instruction::Unreachable),
			ExprKind::Int { value } => self.push(match scalar(ty) {
				ScalarType::I32 => Instruction::I32Const(value as i32),
				ScalarType::I64 => Instruction::I64Const(value),
				_ => unreachable!("an integer constant of a float type"),
			}),
			ExprKind::Float { value } => self.push(match scalar(ty) {
				ScalarType::F32 => Instruction::F32Const(value as f32),
				ScalarType::F64 => Instruction::F64Const(value),
				_ => unreachable!("a float constant of an integer type"),
			}),
			ExprKind::LocalGet { local } => {
				self.push(Instruction::LocalGet(u32::from(local)))
			}
			ExprKind::LocalSet { local, .. } => {
				self.push(Instruction::LocalSet(u32::from(local)))
			}
			ExprKind::SetLocals { targets, .. } => {
				for &target in self.body.targets(targets).iter().rev() {
					self.push(match target {
						Some(local) => Instruction::LocalSet(u32::from(local)),
						None => Instruction::Drop,
					});
				}
			}
			ExprKind::Global { id } => self.push(Instruction::GlobalGet(id)),
			ExprKind::GlobalSet { id, .. } => {
				self.push(Instruction::GlobalSet(id))
			}
			ExprKind::Unary { op, value } => {
				self.push(Instruction::Unary(op, scalar(self.ty(value))))
			}
			ExprKind::Binary { op, .. } => {
				self.push(Instruction::Binary(op, scalar(ty)))
			}
			ExprKind::Compare { op, lhs, .. } => {
				self.push(Instruction::Compare(op, scalar(self.ty(lhs))))
			}
			ExprKind::Convert { op, value } => {
				self.push(Instruction::Convert {
					op,
					from: scalar(self.ty(value)),
					to: scalar(ty),
				})
			}
			ExprKind::Break { label, .. } => {
				let frame = match self.labels[usize::from(label)] {
					Label::Block(frame) => frame,
					Label::Loop(frame) => frame - 1,
				};
				self.push(Instruction::Br(self.branch_depth(frame)));
			}
			ExprKind::Continue { label } => {
				let Label::Loop(frame) = self.labels[usize::from(label)] else {
					unreachable!("a Continue of a Block's label")
				};
				self.push(Instruction::Br(self.branch_depth(frame)));
			}
			ExprKind::Return { .. } => self.push(Instruction::Return),
			ExprKind::IfElse {
				then, otherwise, ..
			} => {
				self.open(Instruction::If {
					ty: self.block_type(ty),
				});
				self.tasks.push(Task::Close {
					expression: expr,
					count: 1,
				});
				if let Some(otherwise) = otherwise {
					self.tasks.push(Task::Expr(otherwise));
					self.tasks.push(Task::Else);
				}
				self.tasks.push(Task::Expr(then));
			}
			ExprKind::Switch {
				selector, cases, ..
			} => {
				let selector = scalar(self.ty(selector));
				let cases = self.body.cases(cases);
				let selector_local = match cases.len() {
					0 => {
						self.push(Instruction::Drop);
						None
					}
					1 => None,
					_ => {
						let local = self.function.locals.len() as u32;
						self.function.locals.push(Local { ty: selector });
						self.push(Instruction::LocalSet(local));
						Some(local)
					}
				};
				self.tasks.push(Task::Close {
					expression: expr,
					count: cases.len() as u32,
				});
				self.tasks.push(Task::IfCases {
					expression: expr,
					next: 0,
					selector_local,
				});
			}
			ExprKind::Call { function, .. } => {
				self.push(Instruction::Call(function))
			}
			ExprKind::Drop { value } => self.drop_values(self.ty(value)),
			ExprKind::DataEnd { memory } => {
				self.push(Instruction::DataEnd { memory })
			}
			ExprKind::MemoryIndex { memory } => {
				self.push(Instruction::MemoryIndex { memory })
			}
			ExprKind::MemorySize { memory } => {
				self.push(Instruction::MemorySize(memory))
			}
			ExprKind::MemoryGrow { memory, .. } => {
				self.push(Instruction::MemoryGrow(memory))
			}
			ExprKind::MemoryFill { memory, .. } => {
				self.push(Instruction::MemoryFill(memory))
			}
			ExprKind::MemoryCopy {
				dst_memory,
				src_memory,
				..
			} => self.push(Instruction::MemoryCopy {
				dst: dst_memory,
				src: src_memory,
			}),
			ExprKind::PointerLoad {
				offset,
				memory,
				access,
				..
			} => {
				let memarg = MemArg {
					align: access.align_log2(),
					offset,
					memory,
				};
				self.push(Instruction::Load(access, memarg));
			}
			ExprKind::PointerStore {
				offset,
				memory,
				access,
				..
			} => {
				let memarg = MemArg {
					align: access.align_log2(),
					offset,
					memory,
				};
				self.push(Instruction::Store(access, memarg));
			}
			ExprKind::StaticPointer { entry, offset } => {
				self.push(Instruction::StaticDataPointer {
					entry,
					offset,
					ty: scalar(ty),
				})
			}
			ExprKind::Sequence { .. }
			| ExprKind::Block { .. }
			| ExprKind::Loop { .. } => {
				unreachable!("structured bodies have explicit closing tasks")
			}
		}
	}

	fn drop_values(&mut self, ty: ValueType) {
		for _ in 0..self.arity(ty) {
			self.push(Instruction::Drop);
		}
	}

	/// Wasm types what follows an end by its block type, even when the
	/// construct can never return. Preserve that fact with unreachable.
	fn after_structured(&mut self, ty: ValueType) {
		if ty == ValueType::Never {
			self.push(Instruction::Unreachable);
		}
	}

	/// Dispatch inside the case wrappers, then advance one case at a time.
	/// The table's default depth exits all case wrappers to the default body.
	fn table_dispatch(&mut self, expression: ExprId, after: u32) {
		let ExprKind::Switch { cases, .. } = self.body.kind(expression) else {
			unreachable!()
		};
		let cases = self.body.cases(cases);
		let min = cases.iter().map(|case| case.value).min().unwrap();
		let max = cases.iter().map(|case| case.value).max().unwrap();
		if min != 0 {
			self.push(Instruction::I32Const(min as i32));
			self.push(Instruction::Binary(mir::BinaryOp::Sub, ScalarType::I32));
		}
		let start = self.function.br_table_depths.len();
		self.function
			.br_table_depths
			.resize(start + (max - min) as usize + 2, cases.len() as u32);
		for (i, case) in cases.iter().enumerate() {
			self.function.br_table_depths
				[start + (case.value - min) as usize] = i as u32;
		}
		self.push(Instruction::BrTable {
			start: start as u32,
			len: (self.function.br_table_depths.len() - start) as u32,
		});
		self.tasks.push(Task::Close {
			expression,
			count: 1,
		});
		self.tasks.push(Task::TableCases {
			expression,
			next: 0,
			after,
		});
	}
}

fn scalar(ty: ValueType) -> ScalarType {
	ScalarType::try_from(ty).expect("a value of one scalar")
}
