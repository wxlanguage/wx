//! A deliberately slow oracle: A dominates B iff removing A makes B
//! unreachable. It shares neither the solver nor the location/join indexes.

use super::*;
use crate::opt::{Placement, UseSite, Uses, ValuePlacement, tests::graph_of};

struct Reference {
	points: Vec<Location>,
	successors: Vec<Vec<usize>>,
	root: usize,
}

impl Reference {
	fn new(graph: &Function) -> Self {
		let mut points = Vec::new();
		for (index, region) in graph.regions.iter().enumerate() {
			if matches!(
				region.kind,
				RegionKind::If { .. } | RegionKind::Switch { .. }
			) {
				continue;
			}
			for position in 0..=region.effects.len() {
				points.push(Location {
					region: RegionId::new(index as u32),
					position: position as u32,
				});
			}
		}
		let index =
			|location| points.iter().position(|&p| p == location).unwrap();
		let start = |region| Location {
			region,
			position: 0,
		};
		let mut successors = vec![Vec::new(); points.len()];
		// Resolve transfers from the structured representation directly, not
		// from Locations or the solver's predecessor/successor arrays.
		let mut transfers = vec![None; graph.joins.len()];
		for (region_index, region) in graph.regions.iter().enumerate() {
			for (position, &effect) in
				graph.sequence[region.effects.range()].iter().enumerate()
			{
				if let Effect::Region(child) =
					graph.effects[usize::from(effect)]
				{
					let continuation = Location {
						region: RegionId::new(region_index as u32),
						position: position as u32 + 1,
					};
					let exit = match graph.regions[usize::from(child)].kind {
						RegionKind::Loop { header, exit } => {
							transfers[usize::from(header)] = Some(start(child));
							exit
						}
						RegionKind::Block { exit }
						| RegionKind::If { exit, .. }
						| RegionKind::Switch { exit, .. } => exit,
						RegionKind::Arm => {
							panic!("an arm is not a standalone construct")
						}
					};
					transfers[usize::from(exit)] = Some(continuation);
				}
			}
		}
		for (from, &location) in points.iter().enumerate() {
			let region = &graph.regions[usize::from(location.region)];
			let Some(&effect) = graph.sequence[region.effects.range()]
				.get(location.position as usize)
			else {
				continue;
			};
			let mut connect = |to| successors[from].push(index(to));
			match graph.effects[usize::from(effect)] {
				Effect::Region(child) => {
					match graph.regions[usize::from(child)].kind {
						RegionKind::Block { .. } | RegionKind::Loop { .. } => {
							connect(start(child))
						}
						RegionKind::If {
							then, otherwise, ..
						} => {
							connect(start(then));
							connect(start(otherwise));
						}
						RegionKind::Switch { cases, default, .. } => {
							for case in &graph.cases[cases.range()] {
								connect(start(case.region));
							}
							if let Some(arm) = default {
								connect(start(arm));
							}
						}
						RegionKind::Arm => unreachable!(),
					}
				}
				Effect::Branch { join, .. } => {
					connect(transfers[usize::from(join)].unwrap())
				}
				Effect::Return { .. } | Effect::Unreachable => {}
				_ => connect(Location {
					position: location.position + 1,
					..location
				}),
			}
		}
		let root = index(start(graph.root));
		Self {
			points,
			successors,
			root,
		}
	}

	fn reachable_without(&self, removed: Option<usize>) -> Vec<bool> {
		let mut seen = vec![false; self.points.len()];
		let mut pending = vec![self.root];
		while let Some(point) = pending.pop() {
			if Some(point) == removed
				|| std::mem::replace(&mut seen[point], true)
			{
				continue;
			}
			pending.extend(&self.successors[point]);
		}
		seen
	}
}

fn check(graph: &Function) {
	let reference = Reference::new(graph);
	let reachable = reference.reachable_without(None);
	let dominates: Vec<Vec<bool>> = (0..reference.points.len())
		.map(|removed| {
			let without = reference.reachable_without(Some(removed));
			reachable
				.iter()
				.zip(without)
				.map(|(&reached, bypass)| {
					reachable[removed] && reached && !bypass
				})
				.collect()
		})
		.collect();
	let locations = Locations::build(graph);
	let actual = Dominators::build(&locations);
	// A common/immediate dominator is the candidate dominated by every
	// other candidate. This does not use the implementation's tree depths.
	let deepest = |candidates: Vec<usize>| {
		candidates
			.iter()
			.copied()
			.find(|&candidate| {
				candidates.iter().all(|&other| dominates[other][candidate])
			})
			.map(|i| reference.points[i])
	};
	for (a, &point) in reference.points.iter().enumerate() {
		assert_eq!(
			actual.is_reachable(point),
			reachable[a],
			"reachability at {point:?}"
		);
		let strict = (0..reference.points.len())
			.filter(|&d| d != a && dominates[d][a])
			.collect();
		assert_eq!(
			actual.immediate_dominator(point),
			deepest(strict),
			"parent of {point:?}"
		);
		for (b, &reader) in reference.points.iter().enumerate() {
			assert_eq!(
				actual.dominates(point, reader),
				dominates[a][b],
				"{point:?} dominates {reader:?}"
			);
			let common = (0..reference.points.len())
				.filter(|&d| dominates[d][a] && dominates[d][b])
				.collect();
			assert_eq!(
				actual.common_dominator(point, reader),
				deepest(common),
				"common ancestor of {point:?}, {reader:?}"
			);
		}
	}
	// Independently check the resulting placement, including phi incoming
	// reads. Derive reader locations from region sequences, not Locations.
	let uses = Uses::collect(graph);
	let plan = Placement::build(&uses, &locations).unwrap();
	let effect_location = |effect| {
		graph
			.regions
			.iter()
			.enumerate()
			.find_map(|(region, data)| {
				graph.sequence[data.effects.range()]
					.iter()
					.position(|&id| id == effect)
					.map(|position| Location {
						region: RegionId::new(region as u32),
						position: position as u32,
					})
			})
			.unwrap()
	};
	for &node in uses.used_nodes() {
		for site in uses.sites(node) {
			let reader = match site {
				UseSite::Node(consumer) => {
					match plan.value(consumer).unwrap() {
						ValuePlacement::Compute(location) => location,
						_ => panic!(
							"an ordinary consumer must have a computation"
						),
					}
				}
				UseSite::Effect(effect) => effect_location(effect),
				UseSite::Row { join, row } => {
					let supplier = graph.effects.iter().position(|effect| matches!(*effect, Effect::Branch { join: target, row: edge } if target == join && edge == row));
					let effect = supplier.unwrap_or_else(|| {
						assert_eq!(row, 0, "only a loop entry has an implicit row");
						let owner = graph.regions.iter().position(|region| matches!(region.kind, RegionKind::Loop { header, .. } if header == join)).unwrap();
						graph.effects.iter().position(|effect| matches!(*effect, Effect::Region(region) if usize::from(region) == owner)).unwrap()
					});
					effect_location(EffectId::new(effect as u32))
				}
			};
			let reader = reference
				.points
				.iter()
				.position(|&point| point == reader)
				.unwrap();
			assert!(reachable[reader], "a required read must be reachable");
			match plan.value(node).unwrap() {
				ValuePlacement::Direct => {}
				ValuePlacement::Fixed(definition)
				| ValuePlacement::Compute(definition) => {
					let definition = reference
						.points
						.iter()
						.position(|&point| point == definition)
						.unwrap();
					assert!(
						dominates[definition][reader],
						"oracle rejected {node:?} at {site:?}"
					);
				}
			}
		}
	}
}

#[test]
fn path_removal_oracle_checks_nested_branches_loops_and_nonlocal_exits() {
	let bodies = [
		"if n == 0 { return 1; }; n + 2",
		"if n == 0 { return 1; } else { return 2; }",
		"local x = get(n); if n == 0 { x + 1 } else { x + 2 }",
		"if n == 0 { n / 2 } else { 2 / n }",
		"block :done { match n { 0 => { break :done 10; }, 1 => { 20 }, _ => { 30 } } }",
		"local mut i: i32 = 0; loop { if i == n { break; }; if i == 2 { i += 1; continue; }; i += 1; }; i",
		"block :done { local mut i: i32 = 0; loop { loop { if i == n { break :done i; }; if i == 2 { break; }; i += 1; }; if i > n { break; }; i += 1; }; i }",
		"loop { if n == 0 { return 1; }; continue; }",
	];
	for body in bodies {
		let source = format!(
			"func get(x: i32) -> i32 {{ x }} func f(n: i32) -> i32 {{ {body} }} export {{ f as \"f\" }}"
		);
		let graph = graph_of(&source, "f");
		check(&graph);
	}
	// Deterministically vary nesting and early-return paths without a random
	// generator or a new testing dependency.
	for depth in 1..=5 {
		let mut body = "n + 7".to_owned();
		for level in 0..depth {
			body = format!(
				"if n == {level} {{ return {level}; }} else {{ {body} }}"
			);
		}
		let source = format!(
			"func f(n: i32) -> i32 {{ {body} }} export {{ f as \"f\" }}"
		);
		check(&graph_of(&source, "f"));
	}
}

#[test]
fn path_removal_oracle_checks_gaps_after_terminators() {
	for terminator in [
		Effect::Return {
			values: super::super::Run::EMPTY,
		},
		Effect::Unreachable,
	] {
		let graph =
			super::tests::straight(vec![terminator, Effect::Unreachable]);
		check(&graph);
	}
}
