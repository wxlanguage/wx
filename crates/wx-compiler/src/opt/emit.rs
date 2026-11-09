//! Graph-to-MIR construction with explicit value locals, structured control
//! and simultaneous incoming-row assignments. Effects retain graph order.

use super::{
	Effect, EffectId, Function, JoinId, NodeId, NodeKind, Placement, RegionId,
	RegionKind, TrappingOp, ValuePlacement,
};
use crate::mir::{
	self, ExprId, ExprKind, FunctionId, LabelId, LocalIndex, MIR, ValueType,
};
use crate::wasm::ScalarType;

/// Emit a fresh body; the caller decides when to replace the original code.
/// May intern multi-result types in the module's signature table.
pub fn emit(
	mir: &mut MIR,
	id: FunctionId,
	placement: &Placement<'_>,
) -> mir::Code {
	let graph = placement.function();
	let params = mir.signatures.params(mir.function(id).signature);
	let mut emitter = Emitter {
		graph,
		placement,
		body: mir::Body::default(),
		locals: params
			.iter()
			.map(|&ty| mir::Local {
				ty,
				mutability: mir::Mutability::Immutable,
			})
			.collect(),
		value_locals: vec![None; graph.kinds.len()],
		effect_result_offsets: vec![0; graph.effects.len() + 1],
		effect_results: Vec::new(),
		join_targets: vec![None; graph.joins.len()],
		phi_targets: vec![None; graph.columns.len()],
		region_labels: vec![None; graph.regions.len()],
		region_bodies: vec![None; graph.regions.len()],
		region_gap_offsets: Vec::with_capacity(graph.regions.len() + 1),
		computation_offsets: Vec::new(),
		scheduled_computations: Vec::new(),
	};
	for index in 0..graph.kinds.len() {
		let node = NodeId::new(index as u32);
		if graph.resolve(node) != node {
			continue;
		}
		if matches!(
			placement.value(node),
			Some(ValuePlacement::Compute(_) | ValuePlacement::Fixed(_))
		) {
			let local = LocalIndex::new(emitter.locals.len() as u32);
			emitter.locals.push(mir::Local {
				ty: value_type(graph.ty(node)),
				mutability: mir::Mutability::Mutable,
			});
			emitter.value_locals[index] = Some(local);
		}
		if let NodeKind::Phi { join, column } = graph.kind(node) {
			if emitter.value_locals[index].is_some() {
				let slot = graph.joins[usize::from(join)].columns.start
					as usize + column as usize;
				assert!(emitter.phi_targets[slot].replace(node).is_none());
			}
		}
		if let NodeKind::Result { effect, .. } = graph.kind(node) {
			emitter.effect_result_offsets[usize::from(effect) + 1] += 1;
		}
	}
	for index in 1..emitter.effect_result_offsets.len() {
		emitter.effect_result_offsets[index] +=
			emitter.effect_result_offsets[index - 1];
	}
	// Keep even unused outputs: they carry result types and must be dropped.
	let mut results =
		vec![None; *emitter.effect_result_offsets.last().unwrap()];
	for (node, kind) in graph.kinds.iter().enumerate() {
		if let NodeKind::Result { effect, index } = *kind {
			let start = emitter.effect_result_offsets[usize::from(effect)];
			let end = emitter.effect_result_offsets[usize::from(effect) + 1];
			let slot = start + index as usize;
			assert!(slot < end, "effect output outside its result run");
			assert!(
				results[slot].replace(NodeId::new(node as u32)).is_none(),
				"duplicate effect output"
			);
		}
	}
	emitter.effect_results = results
		.into_iter()
		.map(|node| node.expect("missing effect output"))
		.collect();

	// Labels belong to constructs, not individual edges. Both joins of a
	// loop use its label: exit rows break, header rows continue.
	let mut label_count = 0;
	emitter.region_gap_offsets.push(0);
	for (index, region) in graph.regions.iter().enumerate() {
		let executable = !matches!(
			region.kind,
			RegionKind::If { .. } | RegionKind::Switch { .. }
		);
		let base = *emitter.region_gap_offsets.last().unwrap();
		emitter.region_gap_offsets.push(
			base + if executable {
				region.effects.len() + 1
			} else {
				0
			},
		);
		let exit = match region.kind {
			RegionKind::Block { exit }
			| RegionKind::Loop { exit, .. }
			| RegionKind::If { exit, .. }
			| RegionKind::Switch { exit, .. } => exit,
			RegionKind::Arm => continue,
		};
		let label = LabelId::new(label_count);
		label_count += 1;
		emitter.region_labels[index] = Some(label);
		emitter.join_targets[usize::from(exit)] = Some(JoinTarget::Exit(label));
		if let RegionKind::Loop { header, .. } = region.kind {
			emitter.join_targets[usize::from(header)] =
				Some(JoinTarget::LoopHeader(label));
		}
	}
	// Count/prefix/fill across executable gaps, preserving dependency order.
	emitter.computation_offsets =
		vec![0; emitter.region_gap_offsets.last().unwrap() + 1];
	for &node in placement.computations() {
		let Some(ValuePlacement::Compute(location)) = placement.value(node)
		else {
			unreachable!()
		};
		let gap = emitter.region_gap_offsets[usize::from(location.region)]
			+ location.position as usize;
		emitter.computation_offsets[gap + 1] += 1;
	}
	for index in 1..emitter.computation_offsets.len() {
		emitter.computation_offsets[index] +=
			emitter.computation_offsets[index - 1];
	}
	let mut cursors = emitter.computation_offsets
		[..emitter.computation_offsets.len() - 1]
		.to_vec();
	emitter.scheduled_computations =
		vec![NodeId::new(0); placement.computations().len()];
	for &node in placement.computations() {
		let Some(ValuePlacement::Compute(location)) = placement.value(node)
		else {
			unreachable!()
		};
		let gap = emitter.region_gap_offsets[usize::from(location.region)]
			+ location.position as usize;
		emitter.scheduled_computations[cursors[gap]] = node;
		cursors[gap] += 1;
	}
	drop(cursors);

	// Build child bodies before owners using an explicit work stack. Region
	// nesting does not consume the Rust call stack, and no MIR input is walked.
	let mut pending = vec![(graph.root, false)];
	while let Some((id, ready)) = pending.pop() {
		if ready {
			let body = emitter.region(mir, id);
			emitter.region_bodies[usize::from(id)] = Some(body);
			continue;
		}
		pending.push((id, true));
		let region = &graph.regions[usize::from(id)];
		match region.kind {
			RegionKind::If {
				then, otherwise, ..
			} => pending.extend([(otherwise, false), (then, false)]),
			RegionKind::Switch { cases, default, .. } => {
				pending.extend(default.map(|id| (id, false)));
				pending.extend(
					graph.cases[cases.range()]
						.iter()
						.map(|case| (case.region, false)),
				);
			}
			_ => {}
		}
		for &effect in &graph.sequence[region.effects.range()] {
			if let Effect::Region(child) = graph.effects[usize::from(effect)] {
				pending.push((child, false));
			}
		}
	}
	mir::Code {
		locals: emitter.locals,
		label_count,
		root: emitter.region_bodies[usize::from(graph.root)].unwrap(),
		body: emitter.body,
	}
}

/// Test harness: optimize all defined bodies, including unreached ones.
/// Production scheduling belongs to `optimize_reachable`.
#[cfg(test)]
pub(crate) fn emit_for_tests(mir: &mut MIR) {
	for index in 0..mir.functions.len() {
		let id = FunctionId::new(index as u32);
		if mir.function(id).code().is_none() {
			continue;
		}
		crate::opt::optimize_function(mir, id);
	}
}

#[derive(Clone, Copy)]
enum JoinTarget {
	Exit(LabelId),
	LoopHeader(LabelId),
}

struct Emitter<'a> {
	graph: &'a Function,
	placement: &'a Placement<'a>,
	body: mir::Body,
	locals: Vec<mir::Local>,
	value_locals: Vec<Option<LocalIndex>>,
	/// Effect ID to a run in `effect_results`, with a trailing end offset.
	effect_result_offsets: Vec<usize>,
	effect_results: Vec<NodeId>,
	/// Per join: the owner's label and the control transfer it requires.
	join_targets: Vec<Option<JoinTarget>>,
	/// Required canonical phi per stored join column; dead columns stay empty.
	phi_targets: Vec<Option<NodeId>>,
	region_labels: Vec<Option<LabelId>>,
	region_bodies: Vec<Option<ExprId>>,
	/// Region ID to its first executable gap; wrappers contribute no gaps.
	region_gap_offsets: Vec<usize>,
	/// Gap index to a run in `scheduled_computations`, with an end offset.
	computation_offsets: Vec<usize>,
	scheduled_computations: Vec<NodeId>,
}

impl Emitter<'_> {
	/// Assign only demanded phi columns. Values evaluates every source before
	/// SetLocals writes any target, including cyclic swaps and self reads.
	fn row(&mut self, mir: &mut MIR, join: JoinId, row: u32) -> Option<ExprId> {
		let mut values = Vec::new();
		let mut targets = Vec::new();
		let mut types = Vec::new();
		let columns = self.graph.joins[usize::from(join)].columns;
		for (column, slot) in columns.range().enumerate() {
			let Some(phi) = self.phi_targets[slot] else {
				continue;
			};
			values.push(self.read(self.graph.row(join, row)[column]));
			targets.push(self.value_locals[usize::from(phi)]);
			types.push(value_type(self.graph.ty(phi)));
		}
		if values.is_empty() {
			return None;
		}
		let ty = mir.signatures.value_of(&types);
		let values = self.body.push_list(values);
		let value = self.body.push(ExprKind::Values { values }, ty);
		let targets = self.body.push_targets(targets);
		Some(
			self.body
				.push(ExprKind::SetLocals { targets, value }, ValueType::Unit),
		)
	}

	fn sequence(&mut self, statements: Vec<ExprId>) -> ExprId {
		let statements = self.body.push_list(statements);
		self.body
			.push(ExprKind::Sequence { statements }, ValueType::Never)
	}

	fn region(&mut self, mir: &mut MIR, id: RegionId) -> ExprId {
		let region = &self.graph.regions[usize::from(id)];
		let kind = region.kind;
		let label = self.region_labels[usize::from(id)];
		let (inner, exit) = match kind {
			RegionKind::If {
				condition,
				then,
				otherwise,
				exit,
			} => {
				let condition = self.read(condition);
				let inner = self.body.push(
					ExprKind::IfElse {
						condition,
						then: self.region_bodies[usize::from(then)].unwrap(),
						otherwise: self.region_bodies[usize::from(otherwise)],
					},
					ValueType::Never,
				);
				(inner, Some(exit))
			}
			RegionKind::Switch {
				selector,
				cases,
				default,
				exit,
			} => {
				let selector = self.read(selector);
				let cases = self.body.push_cases(
					self.graph.cases[cases.range()].iter().map(|case| {
						mir::Case {
							value: case.value,
							body: self.region_bodies[usize::from(case.region)]
								.unwrap(),
						}
					}),
				);
				let inner = self.body.push(
					ExprKind::Switch {
						selector,
						cases,
						default: default.map(|id| {
							self.region_bodies[usize::from(id)].unwrap()
						}),
					},
					ValueType::Never,
				);
				(inner, Some(exit))
			}
			_ => {
				let mut statements = Vec::new();
				let sequence = &self.graph.sequence[region.effects.range()];
				for position in 0..=sequence.len() {
					let gap =
						self.region_gap_offsets[usize::from(id)] + position;
					for index in self.computation_offsets[gap]
						..self.computation_offsets[gap + 1]
					{
						let node = self.scheduled_computations[index];
						let value = self.computation(node);
						let local =
							self.value_locals[usize::from(node)].unwrap();
						statements.push(self.body.push(
							ExprKind::LocalSet { local, value },
							ValueType::Unit,
						));
					}
					if let Some(&effect) = sequence.get(position) {
						statements.push(self.effect(mir, effect));
					}
				}
				// Every executable graph sequence transfers control explicitly.
				// This also encodes a diverging call's lack of fallthrough.
				if statements.last().is_none_or(|&statement| {
					self.body.ty(statement) != ValueType::Never
				}) {
					statements.push(
						self.body.push(ExprKind::Unreachable, ValueType::Never),
					);
				}
				let inner = self.sequence(statements);
				let exit = match kind {
					RegionKind::Block { exit }
					| RegionKind::Loop { exit, .. } => Some(exit),
					RegionKind::Arm => None,
					_ => unreachable!(),
				};
				(inner, exit)
			}
		};
		let Some(exit) = exit else { return inner };
		let ty = if self.graph.edges(exit) == 0 {
			ValueType::Never
		} else {
			ValueType::Unit
		};
		let label = label.unwrap();
		if matches!(kind, RegionKind::Loop { .. }) {
			self.body.push(ExprKind::Loop { label, body: inner }, ty)
		} else {
			let statements = self.body.push_list([inner]);
			self.body.push(ExprKind::Block { label, statements }, ty)
		}
	}

	/// Every read owns a fresh MIR node: the output arena is a tree.
	fn read(&mut self, node: NodeId) -> ExprId {
		let node = self.graph.resolve(node);
		let kind = match self
			.placement
			.value(node)
			.expect("a read requires a value")
		{
			ValuePlacement::Fixed(_) | ValuePlacement::Compute(_) => {
				ExprKind::LocalGet {
					local: self.value_locals[usize::from(node)].unwrap(),
				}
			}
			ValuePlacement::Direct => match self.graph.kind(node) {
				NodeKind::Int(value) => ExprKind::Int { value },
				NodeKind::Float(bits) => ExprKind::Float {
					value: match self.graph.ty(node) {
						ScalarType::F32 => f32::from_bits(bits as u32) as f64,
						ScalarType::F64 => f64::from_bits(bits),
						_ => unreachable!("a float leaf has a float type"),
					},
				},
				NodeKind::Param(index) => ExprKind::LocalGet {
					local: LocalIndex::new(index),
				},
				NodeKind::DataEnd(memory) => ExprKind::DataEnd { memory },
				NodeKind::MemoryIndex(memory) => {
					ExprKind::MemoryIndex { memory }
				}
				NodeKind::StaticPointer { entry, offset } => {
					ExprKind::StaticPointer { entry, offset }
				}
				_ => unreachable!("only pure leaves are direct"),
			},
		};
		self.body.push(kind, value_type(self.graph.ty(node)))
	}

	fn computation(&mut self, node: NodeId) -> ExprId {
		let kind = match self.graph.kind(node) {
			NodeKind::Unary(op, input) => ExprKind::Unary {
				op,
				value: self.read(input),
			},
			NodeKind::Binary(op, lhs, rhs) => ExprKind::Binary {
				op,
				lhs: self.read(lhs),
				rhs: self.read(rhs),
			},
			NodeKind::Compare(op, lhs, rhs) => ExprKind::Compare {
				op,
				lhs: self.read(lhs),
				rhs: self.read(rhs),
			},
			NodeKind::Convert(op, input) => ExprKind::Convert {
				op,
				value: self.read(input),
			},
			_ => unreachable!("only ordinary computations are scheduled"),
		};
		self.body.push(kind, value_type(self.graph.ty(node)))
	}

	fn values(&mut self, run: super::Run) -> mir::ExprList {
		let mut values = Vec::with_capacity(run.len());
		for &node in &self.graph.operands[run.range()] {
			values.push(self.read(node));
		}
		self.body.push_list(values)
	}

	fn effect(&mut self, mir: &mut MIR, effect: EffectId) -> ExprId {
		let outputs = self.effect_result_offsets[usize::from(effect)]
			..self.effect_result_offsets[usize::from(effect) + 1];
		let types: Vec<_> = self.effect_results[outputs.clone()]
			.iter()
			.map(|&node| value_type(self.graph.ty(node)))
			.collect();
		let ty = mir.signatures.value_of(&types);
		let kind = match self.graph.effects[usize::from(effect)] {
			Effect::Call { function, args } => {
				assert!(
					mir.signatures.results(mir.function(function).signature)
						== types,
					"graph call outputs must match the callee signature"
				);
				ExprKind::Call {
					function,
					args: self.values(args),
				}
			}
			Effect::Load {
				address,
				offset,
				memory,
				access,
			} => ExprKind::PointerLoad {
				pointer: self.read(address),
				offset,
				memory,
				access,
			},
			Effect::Store {
				address,
				value,
				offset,
				memory,
				access,
			} => ExprKind::PointerStore {
				pointer: self.read(address),
				value: self.read(value),
				offset,
				memory,
				access,
			},
			Effect::Trapping(TrappingOp::Binary(op, lhs, rhs)) => {
				ExprKind::Binary {
					op,
					lhs: self.read(lhs),
					rhs: self.read(rhs),
				}
			}
			Effect::Trapping(TrappingOp::Convert(op, input)) => {
				ExprKind::Convert {
					op,
					value: self.read(input),
				}
			}
			Effect::GlobalGet(id) => ExprKind::Global { id },
			Effect::GlobalSet(id, value) => ExprKind::GlobalSet {
				id,
				value: self.read(value),
			},
			Effect::MemorySize(memory) => ExprKind::MemorySize { memory },
			Effect::MemoryGrow(memory, input) => ExprKind::MemoryGrow {
				memory,
				delta: self.read(input),
			},
			Effect::MemoryFill {
				memory,
				dst,
				value,
				len,
			} => ExprKind::MemoryFill {
				memory,
				dst: self.read(dst),
				value: self.read(value),
				len: self.read(len),
			},
			Effect::MemoryCopy {
				dst_memory,
				src_memory,
				dst,
				src,
				len,
			} => ExprKind::MemoryCopy {
				dst_memory,
				src_memory,
				dst: self.read(dst),
				src: self.read(src),
				len: self.read(len),
			},
			Effect::Return { values } => {
				let value = if values.is_empty() {
					None
				} else {
					let types: Vec<_> = self.graph.operands[values.range()]
						.iter()
						.map(|&node| {
							value_type(self.graph.ty(self.graph.resolve(node)))
						})
						.collect();
					let ty = mir.signatures.value_of(&types);
					let values = self.values(values);
					Some(self.body.push(ExprKind::Values { values }, ty))
				};
				return self
					.body
					.push(ExprKind::Return { value }, ValueType::Never);
			}
			Effect::Unreachable => {
				return self.body.push(ExprKind::Unreachable, ValueType::Never);
			}
			Effect::Region(region) => {
				let body = self.region_bodies[usize::from(region)].unwrap();
				if let RegionKind::Loop { header, .. } =
					self.graph.regions[usize::from(region)].kind
				{
					if let Some(entry) = self.row(mir, header, 0) {
						let statements = self.body.push_list([entry, body]);
						let ty = self.body.ty(body);
						return self
							.body
							.push(ExprKind::Sequence { statements }, ty);
					}
				}
				return body;
			}
			Effect::Branch { join, row } => {
				let update = self.row(mir, join, row);
				let transfer =
					match self.join_targets[usize::from(join)].unwrap() {
						JoinTarget::LoopHeader(label) => {
							ExprKind::Continue { label }
						}
						JoinTarget::Exit(label) => {
							ExprKind::Break { label, value: None }
						}
					};
				let transfer = self.body.push(transfer, ValueType::Never);
				return match update {
					Some(update) => self.sequence(vec![update, transfer]),
					None => transfer,
				};
			}
		};
		let value = self.body.push(kind, ty);
		if outputs.is_empty() {
			return value;
		}
		let targets = self.body.push_targets(
			self.effect_results[outputs]
				.iter()
				.map(|&node| self.value_locals[usize::from(node)]),
		);
		self.body
			.push(ExprKind::SetLocals { targets, value }, ValueType::Unit)
	}
}

fn value_type(ty: ScalarType) -> ValueType {
	match ty {
		ScalarType::I32 => ValueType::I32,
		ScalarType::I64 => ValueType::I64,
		ScalarType::F32 => ValueType::F32,
		ScalarType::F64 => ValueType::F64,
	}
}
