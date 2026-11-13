//! Plan definitions without emitting MIR. Fixed phi/result definitions break
//! loop cycles; ordinary computations are ordered explicitly.
//! See `notes/opt-placement.md` for the algorithm and constraints.

use super::{
	Dominators, Function, JoinLocation, Location, Locations, NodeId, NodeKind,
	UseSite, Uses,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValuePlacement {
	/// Emit a leaf at each use without introducing a temporary local.
	/// For example, `x + 2` directly reads parameter `x` and emits constant `2`.
	Direct,
	/// Read a local established by an effect or incoming join row. The location
	/// marks availability; for example, `t = call f()` captures the call result,
	/// while `t = if c { a } else { b }` receives the selected arm's value.
	Fixed(Location),
	/// Compute at the planned location and store the result in a local.
	/// For example, `t = x + y; t * t` computes the shared addition once.
	Stored(Location),
	/// Build a computation inside its sole consumer at the planned location.
	/// For example, `(x + y) * 2` nests the addition in the multiplication,
	/// passing its result directly without a temporary local.
	Nested(Location),
}

#[derive(Debug, PartialEq, Eq)]
pub enum PlacementError {
	PureCycle {
		node: NodeId,
	},
	UnreachableDefinition {
		node: NodeId,
		location: Location,
	},
	UnreachableUse {
		node: NodeId,
		site: UseSite,
	},
	IncomparableInputs {
		node: NodeId,
	},
	Unavailable {
		node: NodeId,
		definition: Location,
		reader: Location,
	},
}

/// One immutable graph's definition plan. No MIR locals are allocated yet.
pub struct Placement<'a> {
	function: &'a Function,
	values: Vec<Option<ValuePlacement>>,
	/// Ordinary computations in dependency-first order, including at equal gaps.
	computations: Vec<NodeId>,
}

impl<'a> Placement<'a> {
	pub(super) fn function(&self) -> &'a Function {
		self.function
	}

	pub fn build(
		uses: &Uses<'a>,
		locations: &Locations<'a>,
	) -> Result<Self, PlacementError> {
		let function = uses.function();
		assert!(
			std::ptr::eq(function, locations.function()),
			"analyses must describe the same graph"
		);
		let dominators = Dominators::build(locations);
		let root = Location {
			region: function.root,
			position: 0,
		};
		let mut plan = Self {
			function,
			values: vec![None; function.kinds.len()],
			computations: Vec::new(),
		};
		let mut earliest = vec![None; function.kinds.len()];
		for &node in uses.used_nodes() {
			let placement = match function.kind(node) {
				NodeKind::Result { effect, .. } => {
					let before = locations.before(effect);
					ValuePlacement::Fixed(Location {
						position: before.position + 1,
						..before
					})
				}
				NodeKind::Phi { join, .. } => {
					ValuePlacement::Fixed(match locations.join(join) {
						JoinLocation::LoopHeader { owner } => Location {
							region: owner,
							position: 0,
						},
						JoinLocation::Exit { owner } => {
							let entry = locations
								.entry(owner)
								.expect("an exit has an owner");
							Location {
								position: entry.position + 1,
								..entry
							}
						}
					})
				}
				NodeKind::Unary(..)
				| NodeKind::Binary(..)
				| NodeKind::Compare(..)
				| NodeKind::Convert(..) => continue,
				NodeKind::Int(_)
				| NodeKind::Float(_)
				| NodeKind::Param(_)
				| NodeKind::DataEnd(_)
				| NodeKind::MemoryIndex(_)
				| NodeKind::StaticPointer { .. } => ValuePlacement::Direct,
			};
			let definition = match placement {
				ValuePlacement::Fixed(location) => location,
				_ => root,
			};
			if !dominators.is_reachable(definition) {
				return Err(PlacementError::UnreachableDefinition {
					node,
					location: definition,
				});
			}
			plan.values[usize::from(node)] = Some(placement);
			earliest[usize::from(node)] = Some(definition);
		}

		// Treat fixed phi/result definitions as leaves. Check ordinary cycles
		// rather than relying on allocation or discovery order.
		let mut states = vec![0u8; function.kinds.len()];
		let mut pending = Vec::new();
		for &start in uses.used_nodes() {
			if !is_computation(function.kind(start)) {
				continue;
			}
			pending.push((start, false));
			while let Some((node, leaving)) = pending.pop() {
				let state = &mut states[usize::from(node)];
				if leaving {
					*state = 2;
					plan.computations.push(node);
					continue;
				}
				match *state {
					2 => continue,
					1 => return Err(PlacementError::PureCycle { node }),
					_ => *state = 1,
				}
				pending.push((node, true));
				function.inputs(node, |input, _| {
					if is_computation(function.kind(input)) {
						pending.push((input, false));
					}
				});
			}
		}
		drop(states);
		drop(pending);

		for &node in &plan.computations {
			let mut bound = root;
			let mut incompatible = false;
			function.inputs(node, |input, _| {
				let definition = earliest[usize::from(input)]
					.expect("inputs precede consumers");
				if dominators.dominates(bound, definition) {
					bound = definition;
				} else if !dominators.dominates(definition, bound) {
					incompatible = true;
				}
			});
			if incompatible {
				return Err(PlacementError::IncomparableInputs { node });
			}
			earliest[usize::from(node)] = Some(bound);
		}

		for &node in plan.computations.iter().rev() {
			let mut candidate = None;
			let mut has_multiple_uses = false;
			for site in uses.sites(node) {
				let reader = plan.reader(site, locations);
				if !dominators.is_reachable(reader) {
					return Err(PlacementError::UnreachableUse { node, site });
				}
				candidate = Some(match candidate {
					None => reader,
					Some(previous) => {
						has_multiple_uses = true;
						dominators.common_dominator(previous, reader).unwrap()
					}
				});
			}
			let location = candidate.expect("a used computation has readers");
			let definition = earliest[usize::from(node)].unwrap();
			if !dominators.dominates(definition, location) {
				return Err(PlacementError::Unavailable {
					node,
					definition,
					reader: location,
				});
			}
			plan.values[usize::from(node)] = Some(if has_multiple_uses {
				ValuePlacement::Stored(location)
			} else {
				ValuePlacement::Nested(location)
			});
		}
		drop(earliest);

		// Validate actual placements, not only earliest bounds. Row reads are
		// checked separately from fixed phi definitions, including loop entries.
		for &node in uses.used_nodes() {
			let definition = match plan.values[usize::from(node)].unwrap() {
				ValuePlacement::Direct => None,
				ValuePlacement::Fixed(location)
				| ValuePlacement::Stored(location)
				| ValuePlacement::Nested(location) => Some(location),
			};
			for site in uses.sites(node) {
				let reader = plan.reader(site, locations);
				if !dominators.is_reachable(reader) {
					return Err(PlacementError::UnreachableUse { node, site });
				}
				if let Some(definition) = definition
					&& !dominators.dominates(definition, reader)
				{
					return Err(PlacementError::Unavailable {
						node,
						definition,
						reader,
					});
				}
			}
		}
		Ok(plan)
	}

	fn reader(&self, site: UseSite, locations: &Locations<'_>) -> Location {
		match site {
			UseSite::Effect(effect) => locations.before(effect),
			UseSite::Row { join, row } => locations.row(join, row),
			UseSite::Node(node) => match self.values[usize::from(node)] {
				Some(
					ValuePlacement::Stored(location)
					| ValuePlacement::Nested(location),
				) => location,
				_ => unreachable!(
					"an ordinary reader is placed before its inputs"
				),
			},
		}
	}

	/// None for unused values. Forwarding aliases query their canonical value.
	pub fn value(&self, node: NodeId) -> Option<ValuePlacement> {
		self.values[usize::from(self.function.resolve(node))]
	}

	/// Input-before-consumer order for computations scheduled at shared gaps.
	pub fn computations(&self) -> &[NodeId] {
		&self.computations
	}
}

fn is_computation(kind: NodeKind) -> bool {
	matches!(
		kind,
		NodeKind::Unary(..)
			| NodeKind::Binary(..)
			| NodeKind::Compare(..)
			| NodeKind::Convert(..)
	)
}

#[cfg(test)]
mod tests {
	use super::super::{
		Effect, EffectId, Region, RegionKind, Run, tests::graph_of,
	};
	use super::*;
	use crate::mir::{BinaryOp, GlobalId};
	use crate::wasm::ScalarType;

	fn plan(graph: &Function) -> Placement<'_> {
		Placement::build(&Uses::collect(graph), &Locations::build(graph))
			.unwrap()
	}

	fn computed(plan: &Placement<'_>, node: NodeId) -> Location {
		let Some(
			ValuePlacement::Stored(location) | ValuePlacement::Nested(location),
		) = plan.value(node)
		else {
			panic!("expected computation");
		};
		location
	}

	#[test]
	fn single_operand_occurrences_nest_but_repeated_operands_stay_shared() {
		let graph = graph_of(
			r#"
			func f(x: i32, y: i32) -> i32 {
				local shared = x + y;
				(shared * shared) - (x - y)
			}
			export { f as "f" }
			"#,
			"f",
		);
		let uses = Uses::collect(&graph);
		let locations = Locations::build(&graph);
		let plan = Placement::build(&uses, &locations).unwrap();
		let mut shared = 0;
		let mut nested = 0;
		for &node in plan.computations() {
			match plan.value(node).unwrap() {
				ValuePlacement::Stored(_) => {
					assert_eq!(uses.sites(node).count(), 2);
					assert!(matches!(
						graph.kind(node),
						NodeKind::Binary(BinaryOp::Add, ..)
					));
					shared += 1;
				}
				ValuePlacement::Nested(location) => {
					let mut readers = uses.sites(node);
					assert_eq!(
						location,
						plan.reader(readers.next().unwrap(), &locations)
					);
					assert_eq!(readers.next(), None);
					nested += 1;
				}
				_ => panic!("expected a computation"),
			}
		}
		assert_eq!((shared, nested), (1, 3));
	}

	#[test]
	fn branch_shared_arithmetic_precedes_dispatch_and_inputs_precede_consumers()
	{
		let graph = graph_of(
			r#"
			func f(c: Bool, x: i32) -> i32 {
				local shared = (x + 1) * 2;
				if c { shared + 3 } else { shared + 4 }
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		let plan = plan(&graph);
		let shared = plan
			.computations()
			.iter()
			.copied()
			.find(|&node| {
				matches!(graph.kind(node), NodeKind::Binary(BinaryOp::Mul, ..))
			})
			.unwrap();
		let NodeKind::Binary(_, input, _) = graph.kind(shared) else {
			unreachable!()
		};
		let dispatch = graph
			.regions
			.iter()
			.enumerate()
			.find_map(|(index, region)| {
				matches!(region.kind, RegionKind::If { .. }).then(|| {
					locations
						.entry(super::super::RegionId::new(index as u32))
						.unwrap()
				})
			})
			.unwrap();
		assert_eq!(computed(&plan, shared), dispatch);
		assert_eq!(computed(&plan, input), dispatch);
		assert!(
			plan.computations()
				.iter()
				.position(|&node| node == input)
				.unwrap() < plan
				.computations()
				.iter()
				.position(|&node| node == shared)
				.unwrap()
		);
	}

	#[test]
	fn call_results_stay_fixed_and_branch_only_arithmetic_stays_in_its_arm() {
		let graph = graph_of(
			r#"
			func get(x: i32) -> i32 { x }
			func f(c: Bool, x: i32) -> i32 {
				local result = get(x);
				if c { result + 1 } else { result + 2 }
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		let plan = plan(&graph);
		let mut calls = 0;
		for (index, kind) in graph.kinds.iter().enumerate() {
			let node = NodeId::new(index as u32);
			if let NodeKind::Result { effect, .. } = *kind {
				let before = locations.before(effect);
				assert_eq!(
					plan.value(node),
					Some(ValuePlacement::Fixed(Location {
						position: before.position + 1,
						..before
					}))
				);
				calls += 1;
			}
		}
		assert_eq!(calls, 1);
		let arms: Vec<_> = graph
			.regions
			.iter()
			.find_map(|region| match region.kind {
				RegionKind::If {
					then, otherwise, ..
				} => Some(vec![then, otherwise]),
				_ => None,
			})
			.unwrap();
		for &node in plan.computations() {
			assert!(arms.contains(&computed(&plan, node).region));
		}
	}

	#[test]
	fn a_loop_value_shared_with_the_return_is_computed_inside_the_loop() {
		let graph = graph_of(
			r#"
			func f(n: i32) -> i32 {
				local mut i: i32 = 0;
				loop {
					local next = i + 1;
					if i == n { break; };
					i = next;
				};
				i + 1
			}
			export { f as "f" }
		"#,
			"f",
		);
		let uses = Uses::collect(&graph);
		let locations = Locations::build(&graph);
		let plan = plan(&graph);
		let shared = plan.computations().iter().copied().find(|&node| matches!(graph.kind(node), NodeKind::Binary(BinaryOp::Add, ..)) && uses.sites(node).any(|site| matches!(site, UseSite::Row { .. })) && uses.sites(node).any(|site| matches!(site, UseSite::Effect(effect) if matches!(graph.effects[usize::from(effect)], Effect::Return { .. })))).expect("one interned addition is read inside and after the loop");
		let decision = graph
			.regions
			.iter()
			.enumerate()
			.find_map(|(index, region)| {
				matches!(region.kind, RegionKind::If { .. }).then(|| {
					locations
						.entry(super::super::RegionId::new(index as u32))
						.unwrap()
				})
			})
			.unwrap();
		assert_eq!(computed(&plan, shared), decision);
		let NodeKind::Binary(_, phi, _) = graph.kind(shared) else {
			unreachable!()
		};
		assert!(matches!(plan.value(phi), Some(ValuePlacement::Fixed(_))));
	}

	#[test]
	fn loop_swaps_are_fixed_definitions_not_pure_dependency_cycles() {
		let graph = graph_of(
			r#"
			func f(n: i32, x: i32, y: i32) -> i32 {
				local mut a = x;
				local mut b = y;
				local mut i: i32 = 0;
				loop {
					if i == n { break; };
					local old = a;
					a = b;
					b = old;
					i += 1;
				};
				a + b
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		let plan = plan(&graph);
		let mut headers = 0;
		for (index, kind) in graph.kinds.iter().enumerate() {
			let node = NodeId::new(index as u32);
			if graph.resolve(node) != node {
				continue;
			}
			if let NodeKind::Phi { join, .. } = *kind {
				if let JoinLocation::LoopHeader { owner } = locations.join(join)
				{
					if plan.value(node).is_some() {
						assert_eq!(
							plan.value(node),
							Some(ValuePlacement::Fixed(Location {
								region: owner,
								position: 0
							}))
						);
						headers += 1;
					}
				}
			}
		}
		assert!(headers >= 3);
	}

	#[test]
	fn three_value_rotations_keep_distinct_rows_for_multiple_back_edges() {
		let graph = graph_of(
			r#"
			func f(n: i32, x: i32, y: i32, z: i32, unchanged: i32) -> i32 {
				local mut a = x;
				local mut b = y;
				local mut c = z;
				local mut i: i32 = 0;
				loop {
					if i == n { break; };
					local old = a;
					if i == 2 {
						a = c; c = b; b = old;
						i += 1;
						continue;
					};
					a = b; b = c; c = old;
					i += 1;
				};
				a + b * 10 + c * 100 + unchanged
			}
			export { f as "f" }
		"#,
			"f",
		);
		let (owner, header) = graph
			.regions
			.iter()
			.enumerate()
			.find_map(|(index, region)| match region.kind {
				RegionKind::Loop { header, .. } => {
					Some((super::super::RegionId::new(index as u32), header))
				}
				_ => None,
			})
			.unwrap();
		let plan = plan(&graph);
		let uses = Uses::collect(&graph);
		let columns: Vec<_> = (1..=3)
			.map(|parameter| {
				graph
					.row(header, 0)
					.iter()
					.position(|&node| {
						graph.kind(node) == NodeKind::Param(parameter)
					})
					.unwrap()
			})
			.collect();
		let phis: Vec<_> = columns
			.iter()
			.map(|&column| {
				uses.used_nodes()
					.iter()
					.copied()
					.find(|&node| {
						graph.kind(node)
							== NodeKind::Phi {
								join: header,
								column: column as u32,
							}
					})
					.unwrap()
			})
			.collect();
		assert_eq!(graph.edges(header), 3, "entry and two distinct back edges");
		let mut rotations = Vec::new();
		for row in 1..graph.edges(header) {
			let incoming: Vec<_> = columns
				.iter()
				.map(|&column| graph.resolve(graph.row(header, row)[column]))
				.collect();
			for &node in &incoming {
				assert!(
					uses.sites(node)
						.any(|site| site == UseSite::Row { join: header, row })
				);
			}
			rotations.push(incoming);
		}
		assert!(rotations.contains(&vec![phis[1], phis[2], phis[0]]));
		assert!(rotations.contains(&vec![phis[2], phis[0], phis[1]]));
		for phi in phis {
			assert_eq!(
				plan.value(phi),
				Some(ValuePlacement::Fixed(Location {
					region: owner,
					position: 0
				}))
			);
		}
		assert!(
			!graph
				.row(header, 0)
				.iter()
				.any(|&node| graph.kind(node) == NodeKind::Param(4)),
			"an unchanged local needs no header column"
		);
		let unchanged = uses
			.used_nodes()
			.iter()
			.copied()
			.find(|&node| graph.kind(node) == NodeKind::Param(4))
			.unwrap();
		assert_eq!(plan.value(unchanged), Some(ValuePlacement::Direct));
	}

	#[test]
	fn a_loop_header_value_cannot_supply_its_own_entry_row() {
		let mut graph = graph_of(
			r#"
			func f(n: i32) -> i32 {
				local mut i: i32 = 0;
				loop { if i == n { break; }; i += 1; };
				i
			}
			export { f as "f" }
		"#,
			"f",
		);
		let phi = Uses::collect(&graph).used_nodes().iter().copied().find(|&node| matches!(graph.kind(node), NodeKind::Phi { join, .. } if graph.regions.iter().any(|region| matches!(region.kind, RegionKind::Loop { header, .. } if header == join)))).unwrap();
		let NodeKind::Phi { join, column } = graph.kind(phi) else {
			unreachable!()
		};
		let cell =
			graph.joins[usize::from(join)].rows as usize + column as usize;
		graph.rows[cell] = phi;
		graph.verify().unwrap();
		assert!(
			matches!(Placement::build(&Uses::collect(&graph), &Locations::build(&graph)), Err(PlacementError::Unavailable { node, .. }) if node == phi)
		);
	}

	#[test]
	fn unused_calls_and_divisions_stay_ordered_in_their_branch() {
		let graph = graph_of(
			r#"
			func get(x: i32) -> i32 { x }
			func f(c: Bool, x: i32, y: i32) -> i32 {
				if c {
					_ = get(x);
					local ignored = x / y;
					x + 1
				} else {
					_ = get(y);
					local ignored = y / x;
					y + 2
				}
			}
			export { f as "f" }
		"#,
			"f",
		);
		let uses = Uses::collect(&graph);
		let plan = plan(&graph);
		let mut arms = 0;
		for region in &graph.regions {
			if !matches!(region.kind, RegionKind::Arm) {
				continue;
			}
			let effects = &graph.sequence[region.effects.range()];
			if !effects.iter().any(|&id| {
				matches!(graph.effects[usize::from(id)], Effect::Call { .. })
			}) {
				continue;
			}
			assert!(matches!(
				graph.effects[usize::from(effects[0])],
				Effect::Call { .. }
			));
			assert!(matches!(
				graph.effects[usize::from(effects[1])],
				Effect::Trapping(super::super::TrappingOp::Binary(
					BinaryOp::DivS,
					..
				))
			));
			for &effect in &effects[..2] {
				graph.operands(effect, |input| {
					assert!(
						uses.sites(input)
							.any(|site| site == UseSite::Effect(effect))
					)
				});
			}
			arms += 1;
		}
		assert_eq!(arms, 2);
		for (index, kind) in graph.kinds.iter().enumerate() {
			if matches!(kind, NodeKind::Result { .. }) {
				assert_eq!(
					plan.value(NodeId::new(index as u32)),
					None,
					"unused outputs do not remove their producing effects"
				);
			}
		}
	}

	#[test]
	fn long_shared_dependencies_are_iterative_and_dead_chains_stay_unused() {
		let mut graph = Function::new();
		let x = graph.push(NodeKind::Param(0), ScalarType::I32);
		let mut live = x;
		let mut dead = x;
		let mut expected = Vec::new();
		for _ in 0..4096 {
			live = graph.push(
				NodeKind::Binary(BinaryOp::Add, live, live),
				ScalarType::I32,
			);
			dead = graph.push(
				NodeKind::Binary(BinaryOp::Mul, dead, dead),
				ScalarType::I32,
			);
			expected.push(live);
		}
		let values = graph.push_operands(&[live]);
		graph.effects.push(Effect::Return { values });
		graph.sequence.push(EffectId::new(0));
		graph.regions.push(Region {
			kind: RegionKind::Arm,
			effects: Run::of(0, 1),
		});
		graph.verify().unwrap();
		let uses = Uses::collect(&graph);
		let plan = plan(&graph);
		assert_eq!(plan.computations(), expected);
		assert_eq!(uses.used_nodes().len(), 4097);
		assert_eq!(plan.value(dead), None);
		assert_eq!(
			uses.sites(x).count(),
			2,
			"duplicate operands are distinct reads"
		);
		for &node in plan.computations() {
			assert_eq!(
				computed(&plan, node),
				Location {
					region: graph.root,
					position: 0
				}
			);
		}
	}

	#[test]
	fn wide_loop_joins_keep_every_required_column() {
		for width in [4, 32, 128] {
			let mut body = String::from("local mut i: i32 = 0;");
			for column in 0..width {
				body.push_str(&format!("local mut v{column} = x + {column};"));
			}
			body.push_str("loop { if i == n { break; };");
			for column in 0..width {
				body.push_str(&format!("v{column} += {};", column + 1));
			}
			body.push_str("i += 1; }; i");
			for column in 0..width {
				body.push_str(&format!(" + v{column}"));
			}
			let graph = graph_of(
				&format!(
					"func f(n: i32, x: i32) -> i32 {{ {body} }} export {{ f as \"f\" }}"
				),
				"f",
			);
			let header = graph
				.regions
				.iter()
				.find_map(|region| match region.kind {
					RegionKind::Loop { header, .. } => Some(header),
					_ => None,
				})
				.unwrap();
			// MIR can introduce assignment temporaries which also have stored
			// columns. Only the source values and counter should be demanded.
			assert!(graph.width(header) >= width + 1);
			let uses = Uses::collect(&graph);
			let plan = plan(&graph);
			let phis: Vec<_> = uses.used_nodes().iter().copied().filter(|&node| matches!(graph.kind(node), NodeKind::Phi { join, .. } if join == header)).collect();
			assert_eq!(phis.len(), width + 1);
			for phi in phis {
				assert!(matches!(
					plan.value(phi),
					Some(ValuePlacement::Fixed(_))
				));
				let NodeKind::Phi { column, .. } = graph.kind(phi) else {
					unreachable!()
				};
				for row in 0..graph.edges(header) {
					let input = graph.row(header, row)[column as usize];
					assert!(
						uses.sites(input)
							.any(|site| site
								== UseSite::Row { join: header, row })
					);
				}
			}
		}
	}

	#[test]
	fn multiple_effect_outputs_are_available_before_same_gap_computations() {
		let mut graph = Function::new();
		let input = graph.push(NodeKind::Param(0), ScalarType::I32);
		let args = graph.push_operands(&[input]);
		let call = EffectId::new(0);
		graph.effects.push(Effect::Call {
			function: crate::mir::FunctionId::new(0),
			args,
		});
		let outputs: Vec<_> = (0..3)
			.map(|index| {
				graph.push(
					NodeKind::Result {
						effect: call,
						index,
					},
					ScalarType::I32,
				)
			})
			.collect();
		let sum = graph.push(
			NodeKind::Binary(BinaryOp::Add, outputs[0], outputs[1]),
			ScalarType::I32,
		);
		let product = graph
			.push(NodeKind::Binary(BinaryOp::Mul, sum, sum), ScalarType::I32);
		let values = graph.push_operands(&[product, outputs[1]]);
		graph.effects.push(Effect::Return { values });
		graph.sequence.extend([call, EffectId::new(1)]);
		graph.regions.push(Region {
			kind: RegionKind::Arm,
			effects: Run::of(0, 2),
		});
		graph.verify().unwrap();
		let plan = plan(&graph);
		let gap = Location {
			region: graph.root,
			position: 1,
		};
		for output in &outputs[..2] {
			assert_eq!(plan.value(*output), Some(ValuePlacement::Fixed(gap)));
		}
		assert_eq!(plan.value(outputs[2]), None);
		assert_eq!(computed(&plan, sum), gap);
		assert_eq!(computed(&plan, product), gap);
		assert_eq!(plan.computations(), &[sum, product]);
	}

	#[test]
	fn unavailable_effect_results_are_rejected() {
		let mut graph = Function::new();
		let result = graph.push(
			NodeKind::Result {
				effect: EffectId::new(1),
				index: 0,
			},
			ScalarType::I32,
		);
		graph.effects.extend([
			Effect::GlobalSet(GlobalId::new(0), result),
			Effect::GlobalGet(GlobalId::new(0)),
			Effect::Return { values: Run::EMPTY },
		]);
		graph.sequence.extend((0..3).map(EffectId::new));
		graph.regions.push(Region {
			kind: RegionKind::Arm,
			effects: Run::of(0, 3),
		});
		graph.verify().unwrap();
		assert!(
			matches!(Placement::build(&Uses::collect(&graph), &Locations::build(&graph)), Err(PlacementError::Unavailable { node, .. }) if node == result)
		);
	}

	#[test]
	fn sibling_effect_results_cannot_be_read_together_without_a_merge() {
		let mut graph = graph_of(
			r#"
			func get(x: i32) -> i32 { x }
			func f(c: Bool, x: i32) -> i32 { if c { get(x) } else { get(x + 1) } }
			export { f as "f" }
		"#,
			"f",
		);
		let results: Vec<_> = graph
			.kinds
			.iter()
			.enumerate()
			.filter_map(|(index, kind)| {
				matches!(kind, NodeKind::Result { .. })
					.then(|| NodeId::new(index as u32))
			})
			.collect();
		assert_eq!(results.len(), 2);
		let invalid = graph.push(
			NodeKind::Binary(BinaryOp::Add, results[0], results[1]),
			ScalarType::I32,
		);
		let values = graph
			.effects
			.iter()
			.find_map(|effect| match *effect {
				Effect::Return { values } => Some(values),
				_ => None,
			})
			.unwrap();
		graph.operands[values.range().start] = invalid;
		// Bounds/order remain valid, but this bypasses the required exit phi.
		graph.verify().unwrap();
		assert!(
			matches!(Placement::build(&Uses::collect(&graph), &Locations::build(&graph)), Err(PlacementError::IncomparableInputs { node }) if node == invalid)
		);
	}

	#[test]
	fn aliases_share_the_canonical_plan_and_unused_computations_stay_absent() {
		let mut graph = Function::new();
		let x = graph.push(NodeKind::Param(0), ScalarType::I32);
		let alias = graph.push(NodeKind::Int(0), ScalarType::I32);
		graph.node_replacements[usize::from(alias)] = x;
		let dead =
			graph.push(NodeKind::Binary(BinaryOp::Add, x, x), ScalarType::I32);
		let values = graph.push_operands(&[alias]);
		graph.effects.push(Effect::Return { values });
		graph.sequence.push(EffectId::new(0));
		graph.regions.push(Region {
			kind: RegionKind::Arm,
			effects: Run::of(0, 1),
		});
		graph.verify().unwrap();
		let plan = plan(&graph);
		assert_eq!(plan.value(alias), Some(ValuePlacement::Direct));
		assert_eq!(plan.value(x), plan.value(alias));
		assert_eq!(plan.value(dead), None);
		assert!(plan.computations().is_empty());
	}

	#[test]
	fn replacement_induced_pure_cycles_are_rejected() {
		let mut graph = Function::new();
		let x = graph.push(NodeKind::Param(0), ScalarType::I32);
		let alias = graph.push(NodeKind::Int(0), ScalarType::I32);
		let sum = graph
			.push(NodeKind::Binary(BinaryOp::Add, x, alias), ScalarType::I32);
		graph.node_replacements[usize::from(alias)] = sum;
		let values = graph.push_operands(&[sum]);
		graph.effects.push(Effect::Return { values });
		graph.sequence.push(EffectId::new(0));
		graph.regions.push(Region {
			kind: RegionKind::Arm,
			effects: Run::of(0, 1),
		});
		graph.verify().unwrap();
		assert!(
			matches!(Placement::build(&Uses::collect(&graph), &Locations::build(&graph)), Err(PlacementError::PureCycle { node }) if node == sum)
		);
	}
}
