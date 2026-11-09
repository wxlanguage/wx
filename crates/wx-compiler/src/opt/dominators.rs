//! Execution-path ancestry for placement. Structured region ancestry is
//! insufficient when a value is read inside a loop and after its exit.
//! Temporary control edges are discarded once the dominator tree is built.

use super::{
	Effect, EffectId, Function, JoinLocation, Location, Locations, RegionId,
	RegionKind,
};
use crate::index::index_newtype;

index_newtype!(PointId);

#[cfg(test)]
mod reference_tests;

/// A dominates B when every path from function entry to B passes through A.
/// These are control gaps, before any movable computation has been placed.
pub struct Dominators<'a> {
	function: &'a Function,
	region_starts: Vec<Option<usize>>,
	points: Vec<Location>,
	parents: Vec<Option<PointId>>,
	depths: Vec<u32>,
}

impl<'a> Dominators<'a> {
	/// Requires the same well-formed structured graph as `Locations::build`.
	/// The iterative predecessor-intersection solver is deliberately simple;
	/// construction is not guaranteed linear in graph size.
	pub fn build(locations: &Locations<'a>) -> Self {
		let function = locations.function();
		let mut region_starts = vec![None; function.regions.len()];
		let mut points = Vec::new();
		for (index, region) in function.regions.iter().enumerate() {
			let region_id = RegionId::new(u32::try_from(index).unwrap());
			if locations.is_executable(region_id) {
				region_starts[index] = Some(points.len());
				for position in 0..=region.effects.len() {
					points.push(Location {
						region: region_id,
						position: u32::try_from(position).unwrap(),
					});
				}
			}
		}
		let mut dominators = Self {
			function,
			region_starts,
			parents: vec![None; points.len()],
			depths: vec![0; points.len()],
			points,
		};
		let mut edges = Vec::new();
		for (index, effect) in function.effects.iter().enumerate() {
			let before =
				locations.before(EffectId::new(u32::try_from(index).unwrap()));
			let from = dominators.point(before);
			let next = Location {
				position: before.position + 1,
				..before
			};
			let mut edge = |to| edges.push((from, dominators.point(to)));
			match *effect {
				Effect::Region(region) => {
					match function.regions[usize::from(region)].kind {
						RegionKind::Block { .. } | RegionKind::Loop { .. } => {
							edge(Location {
								region,
								position: 0,
							})
						}
						RegionKind::If {
							then, otherwise, ..
						} => {
							edge(Location {
								region: then,
								position: 0,
							});
							edge(Location {
								region: otherwise,
								position: 0,
							});
						}
						RegionKind::Switch { cases, default, .. } => {
							for case in &function.cases[cases.range()] {
								edge(Location {
									region: case.region,
									position: 0,
								});
							}
							if let Some(region) = default {
								edge(Location {
									region,
									position: 0,
								});
							}
						}
						RegionKind::Arm => {
							unreachable!("an arm is entered by its construct")
						}
					}
				}
				Effect::Branch { join, .. } => match locations.join(join) {
					JoinLocation::Exit { owner } => {
						let entry = locations
							.entry(owner)
							.expect("an exit has an owning construct");
						edge(Location {
							position: entry.position + 1,
							..entry
						});
					}
					JoinLocation::LoopHeader { owner } => edge(Location {
						region: owner,
						position: 0,
					}),
				},
				Effect::Return { .. } | Effect::Unreachable => {}
				_ => edge(next),
			}
		}
		let successors =
			Adjacency::build(dominators.points.len(), &edges, false);
		let predecessors =
			Adjacency::build(dominators.points.len(), &edges, true);
		drop(edges);
		let root = dominators.point(Location {
			region: function.root,
			position: 0,
		});
		let order = reverse_postorder(root, &successors);
		drop(successors);
		let mut ranks = vec![usize::MAX; dominators.points.len()];
		for (rank, &point) in order.iter().enumerate() {
			ranks[usize::from(point)] = rank;
		}
		dominators.parents[usize::from(root)] = Some(root);
		loop {
			let mut changed = false;
			for &point in order.iter().skip(1) {
				let mut parent = None;
				for &predecessor in predecessors.of(point) {
					if dominators.parents[usize::from(predecessor)].is_none() {
						continue;
					}
					parent = Some(match parent {
						None => predecessor,
						Some(current) => intersect(
							current,
							predecessor,
							&dominators.parents,
							&ranks,
						),
					});
				}
				let previous = &mut dominators.parents[usize::from(point)];
				if *previous != parent {
					*previous = parent;
					changed = true;
				}
			}
			if !changed {
				break;
			}
		}
		for &point in order.iter().skip(1) {
			let parent = dominators.parents[usize::from(point)]
				.expect("a reachable point has a dominator");
			debug_assert!(
				ranks[usize::from(parent)] < ranks[usize::from(point)]
			);
			dominators.depths[usize::from(point)] =
				dominators.depths[usize::from(parent)] + 1;
		}
		dominators
	}

	fn point(&self, location: Location) -> PointId {
		let region = usize::from(location.region);
		let start = self.region_starts[region]
			.expect("a wrapper has no control points");
		assert!(
			location.position as usize
				<= self.function.regions[region].effects.len(),
			"location outside region"
		);
		PointId::new(u32::try_from(start + location.position as usize).unwrap())
	}

	pub fn is_reachable(&self, location: Location) -> bool {
		self.parents[usize::from(self.point(location))].is_some()
	}

	/// None for the root or an unreachable gap.
	pub fn immediate_dominator(&self, location: Location) -> Option<Location> {
		let point = self.point(location);
		let parent = self.parents[usize::from(point)]?;
		(point != parent).then(|| self.points[usize::from(parent)])
	}

	/// The latest shared control ancestor. None if either gap is unreachable.
	pub fn common_dominator(
		&self,
		a: Location,
		b: Location,
	) -> Option<Location> {
		let mut a = self.point(a);
		let mut b = self.point(b);
		self.parents[usize::from(a)]?;
		self.parents[usize::from(b)]?;
		while a != b {
			if self.depths[usize::from(a)] >= self.depths[usize::from(b)] {
				a = self.parents[usize::from(a)].unwrap();
			} else {
				b = self.parents[usize::from(b)].unwrap();
			}
		}
		Some(self.points[usize::from(a)])
	}

	/// False for unreachable gaps. A reachable point dominates itself.
	pub fn dominates(&self, definition: Location, reader: Location) -> bool {
		self.common_dominator(definition, reader) == Some(definition)
	}
}

/// Flat outgoing or incoming control edges, used only during construction.
struct Adjacency {
	starts: Vec<usize>,
	targets: Vec<PointId>,
}

impl Adjacency {
	fn build(
		points: usize,
		edges: &[(PointId, PointId)],
		reverse: bool,
	) -> Self {
		let mut starts = vec![0; points + 1];
		for &(from, to) in edges {
			let source = if reverse { to } else { from };
			starts[usize::from(source) + 1] += 1;
		}
		for index in 1..starts.len() {
			starts[index] += starts[index - 1];
		}
		let mut cursors = starts[..points].to_vec();
		let mut targets = vec![PointId::new(0); edges.len()];
		for &(from, to) in edges {
			let (source, target) =
				if reverse { (to, from) } else { (from, to) };
			let cursor = &mut cursors[usize::from(source)];
			targets[*cursor] = target;
			*cursor += 1;
		}
		Self { starts, targets }
	}

	fn of(&self, point: PointId) -> &[PointId] {
		let index = usize::from(point);
		&self.targets[self.starts[index]..self.starts[index + 1]]
	}
}

fn reverse_postorder(root: PointId, successors: &Adjacency) -> Vec<PointId> {
	let mut visited = vec![false; successors.starts.len() - 1];
	let mut pending = vec![(root, false)];
	let mut order = Vec::new();
	while let Some((point, leaving)) = pending.pop() {
		if leaving {
			order.push(point);
			continue;
		}
		if std::mem::replace(&mut visited[usize::from(point)], true) {
			continue;
		}
		pending.push((point, true));
		for &next in successors.of(point).iter().rev() {
			pending.push((next, false));
		}
	}
	order.reverse();
	order
}

fn intersect(
	mut a: PointId,
	mut b: PointId,
	parents: &[Option<PointId>],
	ranks: &[usize],
) -> PointId {
	while a != b {
		if ranks[usize::from(a)] > ranks[usize::from(b)] {
			a = parents[usize::from(a)].unwrap();
		} else {
			b = parents[usize::from(b)].unwrap();
		}
	}
	a
}

#[cfg(test)]
mod tests {
	use super::super::{Region, Run, tests::graph_of};
	use super::*;
	use crate::mir::GlobalId;

	fn after(location: Location) -> Location {
		Location {
			position: location.position + 1,
			..location
		}
	}

	pub(super) fn straight(effects: Vec<Effect>) -> Function {
		let mut graph = Function::new();
		graph
			.sequence
			.extend((0..effects.len() as u32).map(EffectId::new));
		graph.regions.push(Region {
			kind: RegionKind::Arm,
			effects: Run::of(0, effects.len()),
		});
		graph.effects = effects;
		graph.verify().unwrap();
		graph
	}

	#[test]
	fn straight_line_gaps_order_definitions_and_return_has_no_successor() {
		let graph = straight(vec![
			Effect::GlobalGet(GlobalId::new(0)),
			Effect::GlobalGet(GlobalId::new(0)),
			Effect::Return { values: Run::EMPTY },
		]);
		let locations = Locations::build(&graph);
		let dominators = Dominators::build(&locations);
		let first = locations.before(EffectId::new(0));
		let second = locations.before(EffectId::new(1));
		let ret = locations.before(EffectId::new(2));
		assert!(dominators.dominates(first, second));
		assert!(!dominators.dominates(second, first));
		assert_eq!(dominators.immediate_dominator(first), None);
		assert_eq!(dominators.immediate_dominator(second), Some(first));
		assert_eq!(dominators.common_dominator(second, ret), Some(second));
		assert!(!dominators.is_reachable(after(ret)));
		assert_eq!(dominators.common_dominator(first, after(ret)), None);
	}

	#[test]
	fn unreachable_does_not_advance_to_the_following_gap() {
		let graph = straight(vec![
			Effect::Unreachable,
			Effect::Return { values: Run::EMPTY },
		]);
		let locations = Locations::build(&graph);
		let dominators = Dominators::build(&locations);
		assert!(dominators.is_reachable(locations.before(EffectId::new(0))));
		assert!(!dominators.is_reachable(locations.before(EffectId::new(1))));
	}

	#[test]
	fn sibling_arms_share_dispatch_but_do_not_dominate_each_other_or_the_merge()
	{
		let graph = graph_of(
			r#"
			func f(c: Bool, x: i32) -> i32 { if c { x + 1 } else { x + 2 } }
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		let dominators = Dominators::build(&locations);
		let (owner, then, otherwise) = graph
			.regions
			.iter()
			.enumerate()
			.find_map(|(index, region)| match region.kind {
				RegionKind::If {
					then, otherwise, ..
				} => Some((RegionId::new(index as u32), then, otherwise)),
				_ => None,
			})
			.unwrap();
		let dispatch = locations.entry(owner).unwrap();
		let then = Location {
			region: then,
			position: 0,
		};
		let otherwise = Location {
			region: otherwise,
			position: 0,
		};
		assert_eq!(
			dominators.common_dominator(then, otherwise),
			Some(dispatch)
		);
		assert!(!dominators.dominates(then, otherwise));
		assert!(!dominators.dominates(then, after(dispatch)));
		assert_eq!(
			dominators.immediate_dominator(after(dispatch)),
			Some(dispatch)
		);
	}

	#[test]
	fn loop_body_can_dominate_its_exit_without_enclosing_the_exit_region() {
		let graph = graph_of(
			r#"
			func f(n: i32) -> i32 {
				local mut i: i32 = 0;
				loop {
					local next = i + 1;
					if i == n { break; };
					if i == 1 { i = next; continue; };
					i = next;
				};
				i + 1
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		let dominators = Dominators::build(&locations);
		let (owner, header) = graph
			.regions
			.iter()
			.enumerate()
			.find_map(|(index, region)| match region.kind {
				RegionKind::Loop { header, .. } => {
					Some((RegionId::new(index as u32), header))
				}
				_ => None,
			})
			.unwrap();
		let decisions: Vec<_> = graph
			.regions
			.iter()
			.enumerate()
			.filter_map(|(index, region)| {
				matches!(region.kind, RegionKind::If { .. }).then(|| {
					locations.entry(RegionId::new(index as u32)).unwrap()
				})
			})
			.collect();
		assert_eq!(decisions.len(), 2);
		let exit = after(locations.entry(owner).unwrap());
		assert!(dominators.dominates(
			Location {
				region: owner,
				position: 0
			},
			exit
		));
		assert!(dominators.dominates(decisions[0], exit));
		assert!(!dominators.dominates(decisions[1], exit));
		for row in 1..graph.edges(header) {
			assert_eq!(
				dominators.common_dominator(locations.row(header, row), exit),
				Some(decisions[0])
			);
		}
		// The common point is inside the loop, unlike the parent sequence's
		// position before the loop. This is the placement regression.
		assert_ne!(decisions[0].region, exit.region);
	}

	#[test]
	fn switch_cases_and_nonlocal_exits_have_real_control_ancestry() {
		let graph = graph_of(
			r#"
			func f(x: i32) -> i32 {
				block :done {
					match x { 0 => { break :done 10; }, 1 => { 20 }, _ => { 30 } }
				}
			}
			export { f as "f" }
		"#,
			"f",
		);
		let locations = Locations::build(&graph);
		let dominators = Dominators::build(&locations);
		let mut checked = false;
		for (index, region) in graph.regions.iter().enumerate() {
			if let RegionKind::Switch { cases, default, .. } = region.kind {
				let dispatch =
					locations.entry(RegionId::new(index as u32)).unwrap();
				let first = Location {
					region: graph.cases[cases.range()][0].region,
					position: 0,
				};
				let default = Location {
					region: default.unwrap(),
					position: 0,
				};
				assert_eq!(
					dominators.common_dominator(first, default),
					Some(dispatch)
				);
				// The nonlocal-break arm never reaches the switch's normal exit.
				assert!(!dominators.dominates(first, after(dispatch)));
				assert!(!dominators.dominates(default, after(dispatch)));
				checked = true;
			}
		}
		assert!(checked);
	}
}
