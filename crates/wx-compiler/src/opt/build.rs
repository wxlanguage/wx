//! MIR → graph after a local write-set prepass (see `notes/opt-design.md`).
//! The main construction walks the input once. Each MIR
//! local's current value is a binding; a join's columns are the locals its
//! construct writes, known before the construct is built, so every edge
//! gives a row of fixed width and nothing is pruned afterwards.

use super::{
	Case, Column, Effect, Function, JoinId, NodeId, NodeKind, Region, RegionId,
	RegionKind, Run, TrappingOp,
};
use crate::mir::{
	self, ExprId, ExprKind, ExprList, FunctionId, LabelId, LocalIndex, MIR,
	ValueType,
};
use crate::wasm::ScalarType;

/// The graph of a defined function.
pub fn build(mir: &MIR, id: FunctionId) -> Function {
	let function = mir.function(id);
	let code = function.code().expect("a defined function");
	let params = mir.signatures.params(function.signature).len();
	let mut builder = Builder {
		mir,
		body: &code.body,
		function: Function::new(),
		writes: WriteSets::compute(&code.body, code.root, code.locals.len()),
		bindings: Vec::with_capacity(code.locals.len()),
		saved: Vec::new(),
		labels: vec![None; code.label_count as usize],
		built: Vec::new(),
		sequence: Vec::new(),
		cases: Vec::new(),
		open: Vec::new(),
		pool: Vec::new(),
	};
	for (index, local) in code.locals.iter().enumerate() {
		let ty = scalar(local.ty);
		let kind = if index < params {
			NodeKind::Param(index as u32)
		} else if ty.is_float() {
			NodeKind::Float(0)
		} else {
			NodeKind::Int(0)
		};
		let node = builder.function.node(kind, ty);
		builder.bindings.push(node);
	}
	if builder.expr(code.root) {
		let values = builder.function.push_operands(&builder.built);
		builder.effect(Effect::Return { values });
	}
	builder.built.clear();
	builder.function.root = builder.close_region(RegionKind::Arm, 0);
	builder.function
}

struct Builder<'a> {
	mir: &'a MIR,
	body: &'a mir::Body,
	function: Function,
	writes: WriteSets,
	/// Per MIR local, its current value.
	bindings: Vec<NodeId>,
	/// The write sets' values at the start of the constructs whose arms are
	/// being built, restored before each arm.
	saved: Vec<NodeId>,
	labels: Vec<Option<Label>>,
	/// The scalars of the expressions being built.
	built: Vec<NodeId>,
	/// The statements of the regions being built, innermost last.
	sequence: Vec<super::EffectId>,
	/// The cases of the switches being built.
	cases: Vec<Case>,
	/// The joins being built, innermost last; they close in that order.
	open: Vec<OpenJoin>,
	/// Row buffers of closed joins, for the next ones.
	pool: Vec<Vec<NodeId>>,
}

#[derive(Clone, Copy)]
enum Label {
	Block {
		exit: JoinId,
		writes: Run,
	},
	Loop {
		header: JoinId,
		exit: JoinId,
		writes: Run,
	},
}

struct OpenJoin {
	join: JoinId,
	rows: Vec<NodeId>,
	edges: u32,
}

impl Builder<'_> {
	fn effect(&mut self, effect: Effect) -> super::EffectId {
		let id = super::EffectId::new(
			u32::try_from(self.function.effects.len()).unwrap(),
		);
		self.function.effects.push(effect);
		self.sequence.push(id);
		id
	}

	/// Push result `index` of `effect`.
	fn result(&mut self, effect: super::EffectId, index: u32, ty: ScalarType) {
		let node = self.function.push(NodeKind::Result { effect, index }, ty);
		self.built.push(node);
	}

	fn value(&mut self, kind: NodeKind, ty: ValueType) {
		let node = self.function.node(kind, scalar(ty));
		self.built.push(node);
	}

	/// The statements pushed since `start` as a region.
	fn close_region(&mut self, kind: RegionKind, start: usize) -> RegionId {
		let first = self.function.sequence.len();
		self.function.sequence.extend(self.sequence.drain(start..));
		self.push_region(kind, Run::of(first, self.function.sequence.len()))
	}

	fn push_region(&mut self, kind: RegionKind, effects: Run) -> RegionId {
		let id =
			RegionId::new(u32::try_from(self.function.regions.len()).unwrap());
		self.function.regions.push(Region { kind, effects });
		id
	}

	fn pop(&mut self) -> NodeId {
		self.built.pop().expect("a built value")
	}

	/// Build each of `exprs`, keeping their scalars; false once one
	/// diverges, after which nothing more is built.
	fn exprs(&mut self, exprs: &[ExprId]) -> bool {
		exprs.iter().all(|&expr| self.expr(expr))
	}

	fn list(&mut self, list: ExprList) -> bool {
		let body = self.body;
		self.exprs(body.list(list))
	}

	/// Build `statements`, keeping only the last one's scalars.
	fn statements(&mut self, statements: ExprList) -> bool {
		let statements = self.body.list(statements);
		for (index, &statement) in statements.iter().enumerate() {
			let base = self.built.len();
			if !self.expr(statement) {
				return false;
			}
			if index + 1 < statements.len() {
				self.built.truncate(base);
			}
		}
		true
	}

	/// Build `expr`, pushing its scalars onto `built`; false if it diverges.
	fn expr(&mut self, expr: ExprId) -> bool {
		let ty = self.body.ty(expr);
		match self.body.kind(expr) {
			ExprKind::Noop => true,
			ExprKind::Unreachable => {
				self.effect(Effect::Unreachable);
				false
			}
			ExprKind::Int { value } => {
				// One value per bit pattern, so an `I32`'s numbers equal.
				let value = match scalar(ty) {
					ScalarType::I32 => i64::from(value as i32),
					_ => value,
				};
				self.value(NodeKind::Int(value), ty);
				true
			}
			ExprKind::Float { value } => {
				let bits = match scalar(ty) {
					ScalarType::F32 => u64::from((value as f32).to_bits()),
					_ => value.to_bits(),
				};
				self.value(NodeKind::Float(bits), ty);
				true
			}

			ExprKind::LocalGet { local } => {
				self.built.push(self.bindings[usize::from(local)]);
				true
			}
			ExprKind::LocalSet { local, value } => {
				if !self.expr(value) {
					return false;
				}
				self.bindings[usize::from(local)] = self.pop();
				true
			}
			ExprKind::Values { values } => self.list(values),
			ExprKind::SetLocals { targets, value } => {
				let base = self.built.len();
				if !self.expr(value) {
					return false;
				}
				let targets = self.body.targets(targets);
				for (&target, &value) in targets.iter().zip(&self.built[base..])
				{
					if let Some(local) = target {
						self.bindings[usize::from(local)] = value;
					}
				}
				self.built.truncate(base);
				true
			}
			ExprKind::Global { id } => {
				let effect = self.effect(Effect::GlobalGet(id));
				self.result(effect, 0, scalar(ty));
				true
			}
			ExprKind::GlobalSet { id, value } => {
				if !self.expr(value) {
					return false;
				}
				let value = self.pop();
				self.effect(Effect::GlobalSet(id, value));
				true
			}

			ExprKind::Unary { op, value } => {
				if !self.expr(value) {
					return false;
				}
				let value = self.pop();
				self.value(NodeKind::Unary(op, value), ty);
				true
			}
			ExprKind::Binary { op, lhs, rhs } => {
				if !self.exprs(&[lhs, rhs]) {
					return false;
				}
				let rhs = self.pop();
				let lhs = self.pop();
				if op.can_trap() {
					let op = TrappingOp::Binary(op, lhs, rhs);
					let effect = self.effect(Effect::Trapping(op));
					self.result(effect, 0, scalar(ty));
				} else {
					self.value(NodeKind::Binary(op, lhs, rhs), ty);
				}
				true
			}
			ExprKind::Compare { op, lhs, rhs } => {
				if !self.exprs(&[lhs, rhs]) {
					return false;
				}
				let rhs = self.pop();
				let lhs = self.pop();
				self.value(NodeKind::Compare(op, lhs, rhs), ty);
				true
			}
			ExprKind::Convert { op, value } => {
				if !self.expr(value) {
					return false;
				}
				let value = self.pop();
				if op.can_trap() {
					let op = TrappingOp::Convert(op, value);
					let effect = self.effect(Effect::Trapping(op));
					self.result(effect, 0, scalar(ty));
				} else {
					self.value(NodeKind::Convert(op, value), ty);
				}
				true
			}

			ExprKind::Sequence { statements } => self.statements(statements),
			ExprKind::Block { label, statements } => {
				self.block(expr, label, statements, ty)
			}
			ExprKind::Loop { label, body } => self.lp(expr, label, body, ty),
			ExprKind::Break { label, value } => {
				let base = self.built.len();
				if let Some(value) = value
					&& !self.expr(value)
				{
					return false;
				}
				let (join, writes) = match self.labels[usize::from(label)] {
					Some(Label::Block { exit, writes })
					| Some(Label::Loop { exit, writes, .. }) => (exit, writes),
					None => unreachable!("a break outside its label's owner"),
				};
				let row = self.add_row(join, writes, base);
				self.built.truncate(base);
				self.effect(Effect::Branch { join, row });
				false
			}
			ExprKind::Continue { label } => {
				let Some(Label::Loop { header, writes, .. }) =
					self.labels[usize::from(label)]
				else {
					unreachable!("a continue of a block's label")
				};
				let row = self.add_row(header, writes, self.built.len());
				self.effect(Effect::Branch { join: header, row });
				false
			}
			ExprKind::Return { value } => {
				let base = self.built.len();
				if let Some(value) = value
					&& !self.expr(value)
				{
					return false;
				}
				let values = self.function.push_operands(&self.built[base..]);
				self.built.truncate(base);
				self.effect(Effect::Return { values });
				false
			}
			ExprKind::IfElse {
				condition,
				then,
				otherwise,
			} => self.if_else(expr, condition, then, otherwise, ty),
			ExprKind::Switch {
				selector,
				cases,
				default,
			} => self.switch(expr, selector, cases, default, ty),

			ExprKind::Call { function, args } => {
				let base = self.built.len();
				if !self.list(args) {
					return false;
				}
				let args = self.function.push_operands(&self.built[base..]);
				self.built.truncate(base);
				let effect = self.effect(Effect::Call { function, args });
				let mir = self.mir;
				for (index, &result) in scalars(mir, ty).iter().enumerate() {
					self.result(effect, index as u32, scalar(result));
				}
				ty != ValueType::Never
			}
			ExprKind::Drop { value } => {
				let base = self.built.len();
				let completes = self.expr(value);
				self.built.truncate(base);
				completes
			}

			ExprKind::DataEnd { memory } => {
				self.value(NodeKind::DataEnd(memory), ty);
				true
			}
			ExprKind::MemoryIndex { memory } => {
				self.value(NodeKind::MemoryIndex(memory), ty);
				true
			}
			ExprKind::MemorySize { memory } => {
				let effect = self.effect(Effect::MemorySize(memory));
				self.result(effect, 0, scalar(ty));
				true
			}
			ExprKind::MemoryGrow { memory, delta } => {
				if !self.expr(delta) {
					return false;
				}
				let delta = self.pop();
				let effect = self.effect(Effect::MemoryGrow(memory, delta));
				self.result(effect, 0, scalar(ty));
				true
			}
			ExprKind::MemoryFill {
				memory,
				dst,
				value,
				len,
			} => {
				if !self.exprs(&[dst, value, len]) {
					return false;
				}
				let len = self.pop();
				let value = self.pop();
				let dst = self.pop();
				self.effect(Effect::MemoryFill {
					memory,
					dst,
					value,
					len,
				});
				true
			}
			ExprKind::MemoryCopy {
				dst_memory,
				src_memory,
				dst,
				src,
				len,
			} => {
				if !self.exprs(&[dst, src, len]) {
					return false;
				}
				let len = self.pop();
				let src = self.pop();
				let dst = self.pop();
				self.effect(Effect::MemoryCopy {
					dst_memory,
					src_memory,
					dst,
					src,
					len,
				});
				true
			}
			ExprKind::PointerLoad {
				pointer,
				offset,
				memory,
				access,
			} => {
				if !self.expr(pointer) {
					return false;
				}
				let address = self.pop();
				let effect = self.effect(Effect::Load {
					address,
					offset,
					memory,
					access,
				});
				self.result(effect, 0, scalar(ty));
				true
			}
			ExprKind::PointerStore {
				pointer,
				value,
				offset,
				memory,
				access,
			} => {
				if !self.exprs(&[pointer, value]) {
					return false;
				}
				let value = self.pop();
				let address = self.pop();
				self.effect(Effect::Store {
					address,
					value,
					offset,
					memory,
					access,
				});
				true
			}
			ExprKind::StaticPointer { entry, offset } => {
				self.value(NodeKind::StaticPointer { entry, offset }, ty);
				true
			}
		}
	}

	fn block(
		&mut self,
		expr: ExprId,
		label: LabelId,
		statements: ExprList,
		ty: ValueType,
	) -> bool {
		let writes = self.writes.of(expr);
		let exit = self.open_join(writes, scalars(self.mir, ty).len());
		self.labels[usize::from(label)] = Some(Label::Block { exit, writes });
		let start = self.sequence.len();
		let base = self.built.len();
		if self.statements(statements) {
			let row = self.add_row(exit, writes, base);
			self.effect(Effect::Branch { join: exit, row });
		}
		self.built.truncate(base);
		let region = self.close_region(RegionKind::Block { exit }, start);
		self.effect(Effect::Region(region));
		self.close_join(exit, writes)
	}

	/// A loop's header gets a placeholder phi per column before its body
	/// is built, since the body reads them before the back edges exist;
	/// once they do, a placeholder whose rows are itself or one value is
	/// that value.
	fn lp(
		&mut self,
		expr: ExprId,
		label: LabelId,
		body: ExprId,
		ty: ValueType,
	) -> bool {
		let writes = self.writes.of(expr);
		let exit = self.open_join(writes, scalars(self.mir, ty).len());
		let header = self.open_join(writes, 0);
		self.add_row(header, writes, self.built.len());
		let placeholders = self.function.kinds.len();
		for (column, &local) in
			self.writes.locals[writes.range()].iter().enumerate()
		{
			let ty = self.function.ty(self.bindings[usize::from(local)]);
			let phi = NodeKind::Phi {
				join: header,
				column: column as u32,
			};
			self.bindings[usize::from(local)] = self.function.push(phi, ty);
		}
		self.labels[usize::from(label)] = Some(Label::Loop {
			header,
			exit,
			writes,
		});
		let start = self.sequence.len();
		let base = self.built.len();
		if self.expr(body) {
			self.built.truncate(base);
			let row = self.add_row(header, writes, base);
			self.effect(Effect::Branch { join: header, row });
		}
		self.built.truncate(base);
		let region =
			self.close_region(RegionKind::Loop { header, exit }, start);
		self.effect(Effect::Region(region));
		self.close_header(header, placeholders);
		self.close_join(exit, writes)
	}

	fn if_else(
		&mut self,
		expr: ExprId,
		condition: ExprId,
		then: ExprId,
		otherwise: Option<ExprId>,
		ty: ValueType,
	) -> bool {
		if !self.expr(condition) {
			return false;
		}
		let condition = self.pop();
		let writes = self.writes.of(expr);
		let exit = self.open_join(writes, scalars(self.mir, ty).len());
		let saved = self.save(writes);
		let then = self.arm(Some(then), exit, writes);
		self.restore(writes, saved);
		let otherwise = self.arm(otherwise, exit, writes);
		self.saved.truncate(saved);
		let region = self.push_region(
			RegionKind::If {
				condition,
				then,
				otherwise,
				exit,
			},
			Run::EMPTY,
		);
		self.effect(Effect::Region(region));
		self.close_join(exit, writes)
	}

	fn switch(
		&mut self,
		expr: ExprId,
		selector: ExprId,
		cases: mir::CaseList,
		default: Option<ExprId>,
		ty: ValueType,
	) -> bool {
		if !self.expr(selector) {
			return false;
		}
		let selector = self.pop();
		let writes = self.writes.of(expr);
		let exit = self.open_join(writes, scalars(self.mir, ty).len());
		let saved = self.save(writes);
		let first = self.cases.len();
		for case in self.body.cases(cases) {
			self.restore(writes, saved);
			let region = self.arm(Some(case.body), exit, writes);
			self.cases.push(Case {
				value: case.value,
				region,
			});
		}
		let default = default.map(|default| {
			self.restore(writes, saved);
			self.arm(Some(default), exit, writes)
		});
		self.saved.truncate(saved);
		let start = self.function.cases.len();
		self.function.cases.extend(self.cases.drain(first..));
		let cases = Run::of(start, self.function.cases.len());
		let region = self.push_region(
			RegionKind::Switch {
				selector,
				cases,
				default,
				exit,
			},
			Run::EMPTY,
		);
		self.effect(Effect::Region(region));
		self.close_join(exit, writes)
	}

	/// An arm of an `if` or a switch: `expr`, or nothing, then its row of
	/// `exit` if it falls through.
	fn arm(
		&mut self,
		expr: Option<ExprId>,
		exit: JoinId,
		writes: Run,
	) -> RegionId {
		let start = self.sequence.len();
		let base = self.built.len();
		if expr.is_none_or(|expr| self.expr(expr)) {
			let row = self.add_row(exit, writes, base);
			self.effect(Effect::Branch { join: exit, row });
		}
		self.built.truncate(base);
		self.close_region(RegionKind::Arm, start)
	}

	fn save(&mut self, writes: Run) -> usize {
		let base = self.saved.len();
		let Self {
			saved,
			writes: sets,
			bindings,
			..
		} = self;
		saved.extend(
			sets.locals[writes.range()]
				.iter()
				.map(|&local| bindings[usize::from(local)]),
		);
		base
	}

	fn restore(&mut self, writes: Run, base: usize) {
		for (index, &local) in
			self.writes.locals[writes.range()].iter().enumerate()
		{
			self.bindings[usize::from(local)] = self.saved[base + index];
		}
	}

	/// A join over the locals `writes` and `results` scalars of value.
	fn open_join(&mut self, writes: Run, results: usize) -> JoinId {
		let join =
			JoinId::new(u32::try_from(self.function.joins.len()).unwrap());
		let start = self.function.columns.len();
		let locals = &self.writes.locals[writes.range()];
		self.function
			.columns
			.extend(locals.iter().map(|&local| Column::Local(local)));
		self.function
			.columns
			.extend((0..results as u32).map(Column::Result));
		self.function.joins.push(super::Join {
			columns: Run::of(start, self.function.columns.len()),
			rows: 0,
			edges: 0,
		});
		let rows = self.pool.pop().unwrap_or_default();
		self.open.push(OpenJoin {
			join,
			rows,
			edges: 0,
		});
		join
	}

	/// Give `join` a row: the bindings of `writes`, then the scalars built
	/// since `base`. Returns its index.
	fn add_row(&mut self, join: JoinId, writes: Run, base: usize) -> u32 {
		let Self {
			open,
			writes: sets,
			bindings,
			built,
			..
		} = self;
		let open = open
			.iter_mut()
			.rev()
			.find(|open| open.join == join)
			.expect("a branch inside its join's construct");
		open.rows.extend(
			sets.locals[writes.range()]
				.iter()
				.map(|&local| bindings[usize::from(local)]),
		);
		open.rows.extend_from_slice(&built[base..]);
		open.edges += 1;
		open.edges - 1
	}

	/// Move the innermost open join's rows into the function.
	fn commit(&mut self, join: JoinId) {
		let mut open = self.open.pop().expect("an open join");
		debug_assert!(open.join == join, "joins close innermost first");
		let start = u32::try_from(self.function.rows.len()).unwrap();
		self.function.rows.extend_from_slice(&open.rows);
		let entry = &mut self.function.joins[usize::from(join)];
		entry.rows = start;
		entry.edges = open.edges;
		open.rows.clear();
		self.pool.push(open.rows);
	}

	/// Close `join`: each column is one value if every row has it, else a
	/// phi. The locals of `writes` take their columns' values, and the
	/// result columns' are pushed. False if no edge reaches it.
	fn close_join(&mut self, join: JoinId, writes: Run) -> bool {
		self.commit(join);
		let edges = self.function.edges(join);
		if edges == 0 {
			return false;
		}
		let width = self.function.width(join);
		for column in 0..width {
			let first =
				self.function.resolve(self.function.row(join, 0)[column]);
			let same = (1..edges).all(|row| {
				self.function.resolve(self.function.row(join, row)[column])
					== first
			});
			let value = if same {
				first
			} else {
				let ty = self.function.ty(first);
				let phi = NodeKind::Phi {
					join,
					column: column as u32,
				};
				self.function.push(phi, ty)
			};
			if column < writes.len() {
				let local = self.writes.locals[writes.start as usize + column];
				self.bindings[usize::from(local)] = value;
			} else {
				self.built.push(value);
			}
		}
		true
	}

	/// Close a loop's header, whose placeholders are the nodes from
	/// `placeholders`, one per column: forward each whose rows are itself
	/// or one value to that value, until none changes.
	fn close_header(&mut self, header: JoinId, placeholders: usize) {
		self.commit(header);
		let edges = self.function.edges(header);
		let width = self.function.width(header);
		loop {
			let mut changed = false;
			for column in 0..width {
				let phi = NodeId::new((placeholders + column) as u32);
				if self.function.resolve(phi) != phi {
					continue;
				}
				let mut value = None;
				let trivial = (0..edges).all(|row| {
					let input = self
						.function
						.resolve(self.function.row(header, row)[column]);
					if input == phi {
						return true;
					}
					match value {
						None => {
							value = Some(input);
							true
						}
						Some(value) => value == input,
					}
				});
				if trivial && let Some(value) = value {
					self.function.node_replacements[usize::from(phi)] = value;
					changed = true;
				}
			}
			if !changed {
				break;
			}
		}
	}
}

/// Per MIR join construct (`Block`, `Loop`, `IfElse`, `Switch`), the locals
/// its subtree writes, each once.
struct WriteSets {
	locals: Vec<LocalIndex>,
	/// By `ExprId`; empty for anything but a join construct.
	of: Vec<Run>,
}

impl WriteSets {
	fn compute(body: &mir::Body, root: ExprId, locals: usize) -> Self {
		enum Step {
			Enter(ExprId),
			/// Close a join construct whose writes start at `start` in
			/// `found`.
			Leave(ExprId, usize),
		}
		let mut sets = Self {
			locals: Vec::new(),
			of: vec![Run::EMPTY; body.len()],
		};
		// Every write found inside the constructs being walked; a
		// construct's own are deduplicated in place when it closes, so its
		// parent sees each once.
		let mut found: Vec<LocalIndex> = Vec::new();
		// Per local, the construct that last recorded it, plus one.
		let mut stamps = vec![0u32; locals];
		let mut stack = vec![Step::Enter(root)];
		while let Some(step) = stack.pop() {
			match step {
				Step::Enter(expr) => {
					let mut kind = body.kind(expr);
					match kind {
						ExprKind::LocalSet { local, .. } => found.push(local),
						ExprKind::SetLocals { targets, .. } => {
							found.extend(body.targets(targets).iter().flatten())
						}
						_ => {}
					}
					if matches!(
						kind,
						ExprKind::Block { .. }
							| ExprKind::Loop { .. }
							| ExprKind::IfElse { .. }
							| ExprKind::Switch { .. }
					) {
						stack.push(Step::Leave(expr, found.len()));
					}
					kind.body_ids_mut(|id| match id {
						mir::body::BodyId::Expr(child) => {
							stack.push(Step::Enter(*child))
						}
						mir::body::BodyId::List(list) => stack.extend(
							body.list(*list).iter().map(|&e| Step::Enter(e)),
						),
						mir::body::BodyId::Cases(cases) => stack.extend(
							body.cases(*cases)
								.iter()
								.map(|case| Step::Enter(case.body)),
						),
						_ => {}
					});
				}
				Step::Leave(expr, start) => {
					let stamp = u32::from(expr) + 1;
					let mut kept = start;
					for index in start..found.len() {
						let local = found[index];
						let seen = &mut stamps[usize::from(local)];
						if *seen != stamp {
							*seen = stamp;
							found[kept] = local;
							kept += 1;
						}
					}
					found.truncate(kept);
					let first = sets.locals.len();
					sets.locals.extend_from_slice(&found[start..]);
					sets.of[usize::from(expr)] =
						Run::of(first, sets.locals.len());
				}
			}
		}
		sets
	}

	fn of(&self, expr: ExprId) -> Run {
		self.of[usize::from(expr)]
	}
}

fn scalar(ty: ValueType) -> ScalarType {
	ScalarType::try_from(ty).expect("a value of one scalar")
}

/// The scalars a value of `ty` is.
fn scalars(mir: &MIR, ty: ValueType) -> &[ValueType] {
	match ty {
		ValueType::Unit | ValueType::Never => &[],
		ValueType::I32 => &[ValueType::I32],
		ValueType::I64 => &[ValueType::I64],
		ValueType::F32 => &[ValueType::F32],
		ValueType::F64 => &[ValueType::F64],
		ValueType::Aggregate { signature } => mir.signatures.results(signature),
	}
}
