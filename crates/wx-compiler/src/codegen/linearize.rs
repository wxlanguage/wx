//! A MIR body as a [`wasm::Function`]: each node after its children, one
//! instruction per node, choosing nothing (`notes/mir-pipeline.md`, "Codegen:
//! MIR → wasm"). The forms a node has no single instruction for are fixed:
//!
//! - a `Loop` that something leaves is a `block` around a `loop`, its label
//!   both: a `Break` exits the `block`, a `Continue` restarts the `loop`, and
//!   a body that falls off its end restarts it (`br 0`);
//! - a `Switch` is a `br_table` over nested blocks when [`uses_br_table`],
//!   else a chain of `if`s comparing the selector, kept in a scratch local
//!   when more than one comparison reads it;
//! - a structured node of type `Never` is followed by `unreachable`, since
//!   Wasm types what follows its `end` by its block type, not by whether
//!   control reaches it;
//! - once a child diverges, the rest of its parent is not emitted: the
//!   stack is polymorphic there, and a value pushed by dead code would still
//!   be checked against the enclosing block's type.

use crate::mir::{self, Code, ExprId, ExprKind, LabelId, MIR, ValueType};
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
		scratch: [None; 2],
	};
	linearizer.expr(code.root);
	linearizer.function
}

struct Linearizer<'a> {
	mir: &'a MIR,
	body: &'a mir::Body,
	function: wasm::Function,
	/// How many structured instructions are open: a branch's depth is
	/// counted down from here to its target's frame.
	depth: u32,
	/// Per label, the frame its owner opened.
	labels: Vec<Label>,
	/// The local an `if` chain keeps its `I32` or `I64` selector in. One per
	/// type serves every chain: a chain reads its selector only in its
	/// comparisons, which all run before any of its arms.
	scratch: [Option<u32>; 2],
}

/// The frame a label's owner opened. A `Break` of a `Block`'s label exits
/// it; a `Loop`'s is the `loop`, which a `Continue` restarts, and a `Break`
/// exits the `block` around it, the frame before.
#[derive(Clone, Copy)]
enum Label {
	Block(u32),
	Loop(u32),
}

impl Linearizer<'_> {
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

	/// Emit each of `exprs` in order, stopping after one that diverges;
	/// false if one did.
	fn exprs(&mut self, exprs: &[ExprId]) -> bool {
		for &expr in exprs {
			self.expr(expr);
			if self.diverges(expr) {
				return false;
			}
		}
		true
	}

	/// Emit `statements`, dropping each one's values but the last's when
	/// `keep_last`; false if one diverged.
	fn statements(&mut self, statements: &[ExprId], keep_last: bool) -> bool {
		for (i, &statement) in statements.iter().enumerate() {
			self.expr(statement);
			if self.diverges(statement) {
				return false;
			}
			if !(keep_last && i + 1 == statements.len()) {
				self.drop_values(self.ty(statement));
			}
		}
		true
	}

	fn drop_values(&mut self, ty: ValueType) {
		for _ in 0..self.arity(ty) {
			self.push(Instruction::Drop);
		}
	}

	fn expr(&mut self, expr: ExprId) {
		let ty = self.ty(expr);
		match self.body.kind(expr) {
			ExprKind::Noop => {}
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
			ExprKind::LocalSet { local, value } => {
				if self.exprs(&[value]) {
					self.push(Instruction::LocalSet(u32::from(local)));
				}
			}
			ExprKind::Values { values } => {
				self.exprs(self.body.list(values));
			}
			ExprKind::SetLocals { targets, value } => {
				if self.exprs(&[value]) {
					for &target in self.body.targets(targets).iter().rev() {
						self.push(match target {
							Some(local) => {
								Instruction::LocalSet(u32::from(local))
							}
							None => Instruction::Drop,
						});
					}
				}
			}
			ExprKind::Global { id } => self.push(Instruction::GlobalGet(id)),
			ExprKind::GlobalSet { id, value } => {
				if self.exprs(&[value]) {
					self.push(Instruction::GlobalSet(id));
				}
			}

			ExprKind::Unary { op, value } => {
				if self.exprs(&[value]) {
					let operand = scalar(self.ty(value));
					self.push(Instruction::Unary(op, operand));
				}
			}
			ExprKind::Binary { op, lhs, rhs } => {
				if self.exprs(&[lhs, rhs]) {
					self.push(Instruction::Binary(op, scalar(ty)));
				}
			}
			ExprKind::Compare { op, lhs, rhs } => {
				if self.exprs(&[lhs, rhs]) {
					let operand = scalar(self.ty(lhs));
					self.push(Instruction::Compare(op, operand));
				}
			}
			ExprKind::Convert { op, value } => {
				if self.exprs(&[value]) {
					self.push(Instruction::Convert {
						op,
						from: scalar(self.ty(value)),
						to: scalar(ty),
					});
				}
			}

			ExprKind::Sequence { statements } => {
				self.statements(self.body.list(statements), true);
			}
			ExprKind::Block { label, statements } => {
				let frame = self.open(Instruction::Block {
					ty: self.block_type(ty),
				});
				self.labels[usize::from(label)] = Label::Block(frame);
				let keep_last = ty != ValueType::Unit;
				self.statements(self.body.list(statements), keep_last);
				self.close();
				self.after_structured(ty);
			}
			ExprKind::Loop { label, body } => self.lp(label, body, ty),
			ExprKind::Break { label, value } => {
				if value.is_none_or(|value| self.exprs(&[value])) {
					let frame = match self.labels[usize::from(label)] {
						Label::Block(frame) => frame,
						Label::Loop(frame) => frame - 1,
					};
					self.push(Instruction::Br(self.branch_depth(frame)));
				}
			}
			ExprKind::Continue { label } => {
				let Label::Loop(frame) = self.labels[usize::from(label)] else {
					unreachable!("a `Continue` of a `Block`'s label")
				};
				self.push(Instruction::Br(self.branch_depth(frame)));
			}
			ExprKind::Return { value } => {
				if value.is_none_or(|value| self.exprs(&[value])) {
					self.push(Instruction::Return);
				}
			}
			ExprKind::IfElse {
				condition,
				then,
				otherwise,
			} => {
				if !self.exprs(&[condition]) {
					return;
				}
				self.open(Instruction::If {
					ty: self.block_type(ty),
				});
				self.expr(then);
				if let Some(otherwise) = otherwise {
					self.push(Instruction::Else);
					self.expr(otherwise);
				}
				self.close();
				self.after_structured(ty);
			}
			ExprKind::Switch {
				selector,
				cases,
				default,
			} => {
				if self.diverges(selector) {
					self.expr(selector);
					return;
				}
				let cases = self.body.cases(cases);
				if uses_br_table(self.ty(selector), cases) {
					self.br_table(selector, cases, default, ty);
				} else {
					self.expr(selector);
					self.if_chain(
						scalar(self.ty(selector)),
						cases,
						default,
						ty,
					);
				}
				self.after_structured(ty);
			}

			ExprKind::Call { function, args } => {
				if self.exprs(self.body.list(args)) {
					self.push(Instruction::Call(function));
				}
			}
			ExprKind::Drop { value } => {
				if self.exprs(&[value]) {
					self.drop_values(self.ty(value));
				}
			}

			ExprKind::DataEnd { memory } => {
				self.push(Instruction::DataEnd { memory })
			}
			ExprKind::MemoryIndex { memory } => {
				self.push(Instruction::MemoryIndex { memory })
			}
			ExprKind::MemorySize { memory } => {
				self.push(Instruction::MemorySize(memory))
			}
			ExprKind::MemoryGrow { memory, delta } => {
				if self.exprs(&[delta]) {
					self.push(Instruction::MemoryGrow(memory));
				}
			}
			ExprKind::MemoryFill {
				memory,
				dst,
				value,
				len,
			} => {
				if self.exprs(&[dst, value, len]) {
					self.push(Instruction::MemoryFill(memory));
				}
			}
			ExprKind::MemoryCopy {
				dst_memory,
				src_memory,
				dst,
				src,
				len,
			} => {
				if self.exprs(&[dst, src, len]) {
					self.push(Instruction::MemoryCopy {
						dst: dst_memory,
						src: src_memory,
					});
				}
			}
			ExprKind::PointerLoad {
				pointer,
				offset,
				memory,
				access,
			} => {
				if self.exprs(&[pointer]) {
					let memarg = MemArg {
						align: access.align_log2(),
						offset,
						memory,
					};
					self.push(Instruction::Load(access, memarg));
				}
			}
			ExprKind::PointerStore {
				pointer,
				value,
				offset,
				memory,
				access,
			} => {
				if self.exprs(&[pointer, value]) {
					let memarg = MemArg {
						align: access.align_log2(),
						offset,
						memory,
					};
					self.push(Instruction::Store(access, memarg));
				}
			}
			ExprKind::StaticPointer { entry, offset } => {
				self.push(Instruction::StaticDataPointer {
					entry,
					offset,
					ty: scalar(ty),
				})
			}
		}
	}

	/// After the `end` of a structured instruction of type `Never`, control
	/// never arrives, but Wasm reads the stack as the block type left it.
	fn after_structured(&mut self, ty: ValueType) {
		if ty == ValueType::Never {
			self.push(Instruction::Unreachable);
		}
	}

	/// A `Loop`: a `loop` that a body falling off its end restarts, inside a
	/// `block` a `Break` exits when anything can (its type is not `Never`).
	fn lp(&mut self, label: LabelId, body: ExprId, ty: ValueType) {
		let exits = ty != ValueType::Never;
		if exits {
			self.open(Instruction::Block {
				ty: self.block_type(ty),
			});
		}
		let frame = self.open(Instruction::Loop {
			ty: BlockType::Empty,
		});
		self.labels[usize::from(label)] = Label::Loop(frame);
		self.expr(body);
		if !self.diverges(body) {
			self.drop_values(self.ty(body));
			self.push(Instruction::Br(0));
		}
		self.close();
		if exits {
			// Control never leaves the `loop` by its `end`.
			self.push(Instruction::Unreachable);
			self.close();
		}
		self.after_structured(ty);
	}

	/// Case `i` is the `i`-th block from the inside, and the table, inside
	/// them all with the selector (a block does not see the stack outside
	/// it), maps each value in `min..=max` to its case's block or else past
	/// them all, to the default:
	///
	/// ```text
	/// block $after (ty)
	///   block $default
	///     block $case[n-1] … block $case[0]
	///       selector - min; br_table
	///     end  case 0; br $after
	///     …
	///   end    case n-1; br $after
	/// end      default, or unreachable
	/// ```
	fn br_table(
		&mut self,
		selector: ExprId,
		cases: &[mir::Case],
		default: Option<ExprId>,
		ty: ValueType,
	) {
		let after = self.open(Instruction::Block {
			ty: self.block_type(ty),
		});
		self.open(Instruction::Block {
			ty: BlockType::Empty,
		});
		for _ in cases {
			self.open(Instruction::Block {
				ty: BlockType::Empty,
			});
		}

		self.expr(selector);
		let min = cases.iter().map(|case| case.value).min().unwrap();
		let max = cases.iter().map(|case| case.value).max().unwrap();
		if min != 0 {
			self.push(Instruction::I32Const(min as i32));
			self.push(Instruction::Binary(mir::BinaryOp::Sub, ScalarType::I32));
		}
		let start = self.function.br_table_depths.len();
		// One entry per value in the range, then the default's.
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

		for case in cases {
			self.close();
			self.expr(case.body);
			if !self.diverges(case.body) {
				self.push(Instruction::Br(self.branch_depth(after)));
			}
		}
		self.close();
		match default {
			Some(default) => self.expr(default),
			None => self.push(Instruction::Unreachable),
		}
		self.close();
	}

	/// The selector, of type `selector`, is on the stack. Each case is an
	/// `if` on the selector being its value, the next case in its `else`,
	/// the default (or `unreachable`) in the last one's.
	fn if_chain(
		&mut self,
		selector: ScalarType,
		cases: &[mir::Case],
		default: Option<ExprId>,
		ty: ValueType,
	) {
		let local = match cases.len() {
			0 => {
				self.push(Instruction::Drop);
				None
			}
			1 => None,
			_ => {
				let local = self.scratch(selector);
				self.push(Instruction::LocalSet(local));
				Some(local)
			}
		};
		for case in cases {
			if let Some(local) = local {
				self.push(Instruction::LocalGet(local));
			}
			self.push(match selector {
				ScalarType::I32 => Instruction::I32Const(case.value as i32),
				ScalarType::I64 => Instruction::I64Const(case.value),
				_ => unreachable!("a switch on a float"),
			});
			self.push(Instruction::Compare(mir::CompareOp::Eq, selector));
			self.open(Instruction::If {
				ty: self.block_type(ty),
			});
			self.expr(case.body);
			self.push(Instruction::Else);
		}
		match default {
			Some(default) => self.expr(default),
			None => self.push(Instruction::Unreachable),
		}
		for _ in cases {
			self.close();
		}
	}

	fn scratch(&mut self, ty: ScalarType) -> u32 {
		let slot = match ty {
			ScalarType::I32 => 0,
			ScalarType::I64 => 1,
			_ => unreachable!("a switch on a float"),
		};
		let locals = &mut self.function.locals;
		*self.scratch[slot].get_or_insert_with(|| {
			locals.push(Local { ty });
			(locals.len() - 1) as u32
		})
	}
}

fn scalar(ty: ValueType) -> ScalarType {
	ScalarType::try_from(ty).expect("a value of one scalar")
}
