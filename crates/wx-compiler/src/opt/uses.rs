//! Discover required values and record their readers together. See
//! `notes/opt-demands.md`. Discovery order is not emission order.

use super::{EffectId, Function, JoinId, NodeId};
use crate::index::index_newtype;

index_newtype!(UseId);

/// Where an operand occurrence is read, before placement is decided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UseSite {
	Node(NodeId),
	Effect(EffectId),
	/// A phi's incoming value. Loop-header row zero is the loop entry;
	/// other rows are supplied by branch effects.
	Row {
		join: JoinId,
		row: u32,
	},
}

struct UseRecord {
	site: UseSite,
	next: Option<UseId>,
}

/// Reverse edges for used values in one immutable graph version.
/// Records preserve operand multiplicity, but not execution order.
pub struct Uses<'a> {
	function: &'a Function,
	first_use: Vec<Option<UseId>>,
	records: Vec<UseRecord>,
	used_nodes: Vec<NodeId>,
}

impl<'a> Uses<'a> {
	pub(super) fn function(&self) -> &'a Function {
		self.function
	}

	/// All stored effects are retained, including loads and trapping
	/// operations whose results are unused. Requires a well-formed graph:
	/// every effect belongs to exactly one reachable structured region.
	pub fn collect(function: &'a Function) -> Self {
		let mut uses = Self {
			function,
			first_use: vec![None; function.kinds.len()],
			records: Vec::new(),
			used_nodes: Vec::new(),
		};
		// Region structure supplies execution order later. Seeding does not
		// need that order, so visit the flat effect table just once.
		for index in 0..function.effects.len() {
			let effect = EffectId::new(u32::try_from(index).unwrap());
			function.operands(effect, |value| {
				uses.record_use(value, UseSite::Effect(effect));
			});
		}
		let mut cursor = 0;
		while cursor < uses.used_nodes.len() {
			let node = uses.used_nodes[cursor];
			cursor += 1;
			function.inputs(node, |value, site| uses.record_use(value, site));
		}
		uses
	}

	fn record_use(&mut self, value: NodeId, site: UseSite) {
		let value = self.function.resolve(value);
		let head = &mut self.first_use[usize::from(value)];
		let previous = *head;
		let id = UseId::new(u32::try_from(self.records.len()).unwrap());
		self.records.push(UseRecord {
			site,
			next: previous,
		});
		*head = Some(id);
		// Installing the first use before expansion also breaks loop cycles.
		if previous.is_none() {
			self.used_nodes.push(value);
		}
	}

	/// Canonical nodes with recorded uses, each once, in discovery order.
	pub fn used_nodes(&self) -> &[NodeId] {
		&self.used_nodes
	}

	/// Read sites for a value (aliases accepted), newest record first.
	pub fn sites(&self, value: NodeId) -> impl Iterator<Item = UseSite> + '_ {
		let value = self.function.resolve(value);
		let mut next = self.first_use[usize::from(value)];
		std::iter::from_fn(move || {
			let record = &self.records[usize::from(next?)];
			next = record.next;
			Some(record.site)
		})
	}
}

#[cfg(test)]
mod tests {
	use super::super::{Effect, NodeKind, Region, RegionKind, Run, TrappingOp};
	use super::*;
	use crate::mir::{BinaryOp, FunctionId, LoadAccess, MemoryId};
	use crate::wasm::ScalarType;

	fn value(graph: &mut Function, kind: NodeKind) -> NodeId {
		graph.push(kind, ScalarType::I32)
	}

	fn effect(graph: &mut Function, effect: Effect) -> EffectId {
		let id = EffectId::new(graph.effects.len() as u32);
		graph.effects.push(effect);
		graph.sequence.push(id);
		id
	}

	fn finish(graph: &mut Function) {
		graph.regions.push(Region {
			kind: RegionKind::Arm,
			effects: Run::of(0, graph.sequence.len()),
		});
		graph.verify().unwrap();
	}

	#[test]
	fn shared_values_expand_once_but_duplicate_operands_have_two_uses() {
		let mut graph = Function::new();
		let x = value(&mut graph, NodeKind::Param(0));
		let shared = value(&mut graph, NodeKind::Binary(BinaryOp::Mul, x, x));
		let dead =
			value(&mut graph, NodeKind::Binary(BinaryOp::Add, x, shared));
		let values = graph.push_operands(&[shared, shared]);
		let ret = effect(&mut graph, Effect::Return { values });
		finish(&mut graph);
		let uses = Uses::collect(&graph);
		assert_eq!(uses.used_nodes(), &[shared, x]);
		assert_eq!(
			uses.sites(shared).collect::<Vec<_>>(),
			vec![UseSite::Effect(ret); 2]
		);
		assert_eq!(
			uses.sites(x).collect::<Vec<_>>(),
			vec![UseSite::Node(shared); 2]
		);
		assert_eq!(uses.sites(dead).count(), 0);
	}

	#[test]
	fn forwarding_is_canonical_for_requests_readers_and_queries() {
		let mut graph = Function::new();
		let x = value(&mut graph, NodeKind::Param(0));
		let alias = value(&mut graph, NodeKind::Int(0));
		graph.node_replacements[usize::from(alias)] = x;
		let sum = value(&mut graph, NodeKind::Binary(BinaryOp::Add, alias, x));
		let values = graph.push_operands(&[sum, alias]);
		effect(&mut graph, Effect::Return { values });
		finish(&mut graph);
		let uses = Uses::collect(&graph);
		assert_eq!(uses.used_nodes(), &[sum, x]);
		assert_eq!(uses.sites(x).count(), 3);
		assert_eq!(
			uses.sites(alias).collect::<Vec<_>>(),
			uses.sites(x).collect::<Vec<_>>()
		);
		let mut inputs = Vec::new();
		graph.inputs(alias, |input, site| inputs.push((input, site)));
		assert!(inputs.is_empty());
	}

	#[test]
	fn unused_effect_results_still_demand_their_operands() {
		let mut graph = Function::new();
		let x = value(&mut graph, NodeKind::Param(0));
		let float = graph.push(NodeKind::Param(1), ScalarType::F64);
		let args = graph.push_operands(&[x]);
		let call = effect(
			&mut graph,
			Effect::Call {
				function: FunctionId::new(0),
				args,
			},
		);
		let load = effect(
			&mut graph,
			Effect::Load {
				address: x,
				offset: 0,
				memory: MemoryId::new(0),
				access: LoadAccess::I32,
			},
		);
		let trap = effect(
			&mut graph,
			Effect::Trapping(TrappingOp::Binary(BinaryOp::DivS, x, x)),
		);
		let conversion = effect(
			&mut graph,
			Effect::Trapping(TrappingOp::Convert(
				crate::mir::ConvertOp::TruncS,
				float,
			)),
		);
		let result = value(
			&mut graph,
			NodeKind::Result {
				effect: call,
				index: 0,
			},
		);
		finish(&mut graph);
		let uses = Uses::collect(&graph);
		assert_eq!(uses.used_nodes(), &[x, float]);
		assert_eq!(
			uses.sites(float).collect::<Vec<_>>(),
			vec![UseSite::Effect(conversion)]
		);
		assert_eq!(uses.sites(result).count(), 0);
		assert_eq!(
			uses.sites(x).collect::<Vec<_>>(),
			vec![
				UseSite::Effect(trap),
				UseSite::Effect(trap),
				UseSite::Effect(load),
				UseSite::Effect(call)
			]
		);
	}

	#[test]
	fn loop_discovery_follows_live_cycles_and_ignores_dead_cycles() {
		let graph = super::super::tests::graph_of(
			r#"
			func f(n: i32) -> i32 {
				local mut i: i32 = 0;
				local mut dead: i32 = 0;
				loop {
					if i == n { break };
					i += 1;
					dead += 2;
				};
				i
			}
			export { f as "f" }
		"#,
			"f",
		);
		let uses = Uses::collect(&graph);
		let mut live = 0;
		let mut dead = 0;
		for index in 0..graph.kinds.len() {
			let node = NodeId::new(index as u32);
			if let NodeKind::Phi { join, column } = graph.kind(node) {
				if graph.resolve(node) != node {
					continue;
				}
				if uses.sites(node).next().is_some() {
					live += 1;
					for row in 0..graph.edges(join) {
						let incoming = graph.row(join, row)[column as usize];
						assert!(
							uses.sites(incoming)
								.any(|site| site == UseSite::Row { join, row })
						);
					}
				} else {
					dead += 1;
				}
			}
		}
		assert!(live > 0 && dead > 0);
		let mut unique = uses.used_nodes().to_vec();
		unique.sort();
		unique.dedup();
		assert_eq!(unique.len(), uses.used_nodes().len());
		let two = graph
			.kinds
			.iter()
			.position(|kind| *kind == NodeKind::Int(2))
			.unwrap();
		assert_eq!(uses.sites(NodeId::new(two as u32)).count(), 0);
	}

	#[test]
	fn nested_conditions_are_roots_and_only_live_phi_columns_request_rows() {
		let graph = super::super::tests::graph_of(
			r#"
			func f(c: Bool, x: i32, y: i32) -> i32 {
				local mut dead: i32 = 0;
				if c { dead = x + 10 } else { dead = y + 20 };
				if c { x } else { y }
			}
			export { f as "f" }
		"#,
			"f",
		);
		let uses = Uses::collect(&graph);
		for (index, kind) in graph.kinds.iter().enumerate() {
			let node = NodeId::new(index as u32);
			match kind {
				NodeKind::Param(0) => assert!(
					uses.sites(node)
						.all(|site| matches!(site, UseSite::Effect(_)))
				),
				NodeKind::Int(10 | 20) => {
					assert_eq!(uses.sites(node).count(), 0)
				}
				_ => {}
			}
		}
		assert!(
			uses.records
				.iter()
				.any(|record| matches!(record.site, UseSite::Row { .. }))
		);
	}
}
