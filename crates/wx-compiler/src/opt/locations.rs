//! Structural positions used by placement, before any movable value has
//! been assigned a location. See `notes/opt-placement.md`.

use super::{Effect, EffectId, Function, JoinId, RegionId, RegionKind};

/// A gap before effect `position` in an executable region's sequence.
/// Position equal to the sequence length is its end. A gap alone does not
/// prove that control can reach it or that a value is available there.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Location {
	pub region: RegionId,
	pub position: u32,
}

/// The construct owning a join, and where the joined values become available.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JoinLocation {
	/// Available after the owning construct completes.
	Exit { owner: RegionId },
	/// Available at the start of each iteration of the owning loop.
	LoopHeader { owner: RegionId },
}

/// Per-function indexes over one immutable graph. These describe structure,
/// not placement decisions, execution reachability, or dependency order.
pub struct Locations<'a> {
	function: &'a Function,
	effects: Vec<Location>,
	/// The enclosing construct's position; only the root has no entry.
	entries: Vec<Option<Location>>,
	joins: Vec<JoinLocation>,
	row_starts: Vec<usize>,
	rows: Vec<Location>,
}

impl<'a> Locations<'a> {
	pub(super) fn function(&self) -> &'a Function {
		self.function
	}

	/// Index a well-formed graph. Every effect, region, join and incoming
	/// row must belong to the structured program. No MIR traversal is needed.
	pub fn build(function: &'a Function) -> Self {
		let root = function.root;
		let initial = Location {
			region: root,
			position: 0,
		};
		let mut row_starts = Vec::with_capacity(function.joins.len() + 1);
		row_starts.push(0);
		for join in &function.joins {
			row_starts.push(row_starts.last().unwrap() + join.edges as usize);
		}
		// The structural walk fills every slot under the graph invariants.
		// Initial values are allocation defaults, not missing-entry sentinels.
		let mut locations = Self {
			function,
			effects: vec![initial; function.effects.len()],
			entries: vec![None; function.regions.len()],
			joins: vec![
				JoinLocation::Exit { owner: root };
				function.joins.len()
			],
			rows: vec![initial; *row_starts.last().unwrap()],
			row_starts,
		};
		let mut pending = vec![(root, None)];
		while let Some((id, entry)) = pending.pop() {
			locations.entries[usize::from(id)] = entry;
			let region = &function.regions[usize::from(id)];
			match region.kind {
				RegionKind::Block { exit } => locations.exit(exit, id),
				RegionKind::Loop { header, exit } => {
					locations.exit(exit, id);
					locations.joins[usize::from(header)] =
						JoinLocation::LoopHeader { owner: id };
					locations.set_row(
						header,
						0,
						entry.expect("a loop has an enclosing construct"),
					);
				}
				RegionKind::If {
					then,
					otherwise,
					exit,
					..
				} => {
					locations.exit(exit, id);
					// Both arms enter at the parent's if effect. The wrapper
					// has no executable sequence to place shared code into.
					pending.extend([(otherwise, entry), (then, entry)]);
				}
				RegionKind::Switch {
					cases,
					default,
					exit,
					..
				} => {
					locations.exit(exit, id);
					if let Some(default) = default {
						pending.push((default, entry));
					}
					for case in function.cases[cases.range()].iter().rev() {
						pending.push((case.region, entry));
					}
				}
				RegionKind::Arm => {}
			}
			for (position, &effect) in
				function.sequence[region.effects.range()].iter().enumerate()
			{
				let location = Location {
					region: id,
					position: u32::try_from(position).unwrap(),
				};
				locations.effects[usize::from(effect)] = location;
				match function.effects[usize::from(effect)] {
					Effect::Region(nested) => {
						pending.push((nested, Some(location)))
					}
					Effect::Branch { join, row } => {
						locations.set_row(join, row, location)
					}
					_ => {}
				}
			}
		}
		locations
	}

	fn exit(&mut self, join: JoinId, owner: RegionId) {
		self.joins[usize::from(join)] = JoinLocation::Exit { owner };
	}

	fn set_row(&mut self, join: JoinId, row: u32, location: Location) {
		self.rows[self.row_starts[usize::from(join)] + row as usize] = location;
	}

	/// An effect's operand-read position, before the effect runs.
	pub fn before(&self, effect: EffectId) -> Location {
		self.effects[usize::from(effect)]
	}

	/// Position of the enclosing construct in the parent executable region.
	/// Arms skip their if/switch wrapper, sharing its entry location. Only
	/// the function root returns None; wrappers also have an entry location.
	pub fn entry(&self, region: RegionId) -> Option<Location> {
		self.entries[usize::from(region)]
	}

	/// If/switch wrappers own arms but do not have an executable sequence.
	pub fn is_executable(&self, region: RegionId) -> bool {
		!matches!(
			self.function.regions[usize::from(region)].kind,
			RegionKind::If { .. } | RegionKind::Switch { .. }
		)
	}

	pub fn join(&self, join: JoinId) -> JoinLocation {
		self.joins[usize::from(join)]
	}

	/// Incoming values are read before this row's branch, or before the
	/// loop construct for a loop header's implicit entry row zero.
	pub fn row(&self, join: JoinId, row: u32) -> Location {
		assert!(row < self.function.edges(join), "row outside join");
		self.rows[self.row_starts[usize::from(join)] + row as usize]
	}
}

#[cfg(test)]
mod tests {
	use super::super::tests::graph_of;
	use super::super::{Case, Join, Region, Run};
	use super::*;

	fn containing_effect(graph: &Function, region: RegionId) -> EffectId {
		graph
			.effects
			.iter()
			.enumerate()
			.find_map(|(index, effect)| {
				matches!(effect, Effect::Region(id) if *id == region)
					.then(|| EffectId::new(index as u32))
			})
			.unwrap()
	}

	fn check_effect_positions(graph: &Function, locations: &Locations<'_>) {
		assert_eq!(locations.entry(graph.root), None);
		assert!(locations.is_executable(graph.root));
		for index in 0..graph.effects.len() {
			let effect = EffectId::new(index as u32);
			let location = locations.before(effect);
			assert!(locations.is_executable(location.region));
			let region = &graph.regions[usize::from(location.region)];
			assert_eq!(
				graph.sequence[region.effects.range()]
					[location.position as usize],
				effect
			);
		}
	}

	#[test]
	fn if_arms_share_the_parent_construct_entry_not_the_wrapper() {
		let graph = graph_of(
			r#"
			func f(c: Bool, x: i32) -> i32 {
				if c { x + 1 } else { x + 2 }
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		check_effect_positions(&graph, &locations);
		let (wrapper, then, otherwise, exit) = graph
			.regions
			.iter()
			.enumerate()
			.find_map(|(index, region)| match region.kind {
				RegionKind::If {
					then,
					otherwise,
					exit,
					..
				} => Some((RegionId::new(index as u32), then, otherwise, exit)),
				_ => None,
			})
			.unwrap();
		let entry = locations.before(containing_effect(&graph, wrapper));
		assert!(!locations.is_executable(wrapper));
		assert_eq!(locations.entry(wrapper), Some(entry));
		for arm in [then, otherwise] {
			assert!(locations.is_executable(arm));
			assert_eq!(locations.entry(arm), Some(entry));
			assert_ne!(entry.region, wrapper);
		}
		assert_eq!(locations.join(exit), JoinLocation::Exit { owner: wrapper });
		assert_eq!(locations.row(exit, 0).region, then);
		assert_eq!(locations.row(exit, 1).region, otherwise);
	}

	#[test]
	fn nested_loop_rows_distinguish_entry_back_edges_and_outer_exits() {
		let graph = graph_of(
			r#"
			func f(n: i32) -> i32 {
				local mut i: i32 = 0;
				loop :outer {
					if i == n { break :outer; };
					loop {
						i += 1;
						if i == 2 { continue :outer; };
						break :outer;
					};
				};
				i
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		check_effect_positions(&graph, &locations);
		let mut headers = Vec::new();
		let mut exits = Vec::new();
		for (index, region) in graph.regions.iter().enumerate() {
			if let RegionKind::Loop { header, exit } = region.kind {
				let owner = RegionId::new(index as u32);
				assert_eq!(
					locations.join(header),
					JoinLocation::LoopHeader { owner }
				);
				assert_eq!(locations.join(exit), JoinLocation::Exit { owner });
				assert_eq!(
					locations.row(header, 0),
					locations.before(containing_effect(&graph, owner))
				);
				assert_eq!(
					locations.entry(owner),
					Some(locations.row(header, 0))
				);
				headers.push(header);
				exits.push(exit);
			}
		}
		assert_eq!(headers.len(), 2);
		assert_ne!(locations.row(headers[0], 0), locations.row(headers[1], 0));
		let mut back_edges = 0;
		let mut nested_exits = 0;
		for (index, effect) in graph.effects.iter().enumerate() {
			if let Effect::Branch { join, row } = *effect {
				let position = locations.before(EffectId::new(index as u32));
				assert_eq!(locations.row(join, row), position);
				if headers.contains(&join) {
					assert_ne!(row, 0);
					assert_ne!(position, locations.row(join, 0));
					back_edges += 1;
				}
				if exits.contains(&join) {
					let JoinLocation::Exit { owner } = locations.join(join)
					else {
						unreachable!()
					};
					let mut region = position.region;
					while region != owner {
						if matches!(
							graph.regions[usize::from(region)].kind,
							RegionKind::Loop { .. }
						) {
							nested_exits += 1;
						}
						region = locations
							.entry(region)
							.expect("the exit owner encloses its branch")
							.region;
					}
				}
			}
		}
		assert_eq!(back_edges, 1);
		assert!(nested_exits > 0);
	}

	#[test]
	fn switch_default_has_the_same_entry_as_its_cases() {
		let graph = graph_of(
			r#"
			func f(x: i32) -> i32 {
				match x { 0 => { 10 }, 1 => { 20 }, _ => { 30 } }
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		check_effect_positions(&graph, &locations);
		let mut switches = 0;
		for (index, region) in graph.regions.iter().enumerate() {
			if let RegionKind::Switch {
				cases,
				default,
				exit,
				..
			} = region.kind
			{
				let owner = RegionId::new(index as u32);
				let entry = locations.before(containing_effect(&graph, owner));
				assert!(!locations.is_executable(owner));
				assert_eq!(locations.join(exit), JoinLocation::Exit { owner });
				for arm in graph.cases[cases.range()]
					.iter()
					.map(|case| case.region)
					.chain(default)
				{
					assert_eq!(locations.entry(arm), Some(entry));
					assert!(locations.is_executable(arm));
				}
				switches += 1;
			}
		}
		assert_eq!(switches, 1);
	}

	#[test]
	fn zero_width_rows_and_a_switch_without_default_still_have_locations() {
		let mut graph = Function::new();
		let root = RegionId::new(0);
		let wrapper = RegionId::new(1);
		let arm0 = RegionId::new(2);
		let arm1 = RegionId::new(3);
		let exit = JoinId::new(0);
		let selector = graph.push(
			super::super::NodeKind::Param(0),
			crate::wasm::ScalarType::I32,
		);
		graph.joins.push(Join {
			columns: Run::EMPTY,
			rows: 0,
			edges: 2,
		});
		graph.cases.extend([
			Case {
				value: 0,
				region: arm0,
			},
			Case {
				value: 1,
				region: arm1,
			},
		]);
		graph.effects.extend([
			Effect::Region(wrapper),
			Effect::Return { values: Run::EMPTY },
			Effect::Branch { join: exit, row: 0 },
			Effect::Branch { join: exit, row: 1 },
		]);
		graph.sequence.extend((0..4).map(EffectId::new));
		graph.regions.extend([
			Region {
				kind: RegionKind::Arm,
				effects: Run::of(0, 2),
			},
			Region {
				kind: RegionKind::Switch {
					selector,
					cases: Run::of(0, 2),
					default: None,
					exit,
				},
				effects: Run::EMPTY,
			},
			Region {
				kind: RegionKind::Arm,
				effects: Run::of(2, 3),
			},
			Region {
				kind: RegionKind::Arm,
				effects: Run::of(3, 4),
			},
		]);
		graph.verify().unwrap();
		let locations = Locations::build(&graph);
		check_effect_positions(&graph, &locations);
		assert_eq!(
			locations.before(EffectId::new(1)),
			Location {
				region: root,
				position: 1
			}
		);
		assert_eq!(
			locations.row(exit, 0),
			Location {
				region: arm0,
				position: 0
			}
		);
		assert_eq!(
			locations.row(exit, 1),
			Location {
				region: arm1,
				position: 0
			}
		);
		assert!(graph.rows.is_empty());
	}
}
