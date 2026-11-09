//! Test-only checks for graph structure and join rows.

use super::{
	Effect, EffectId, Function, JoinId, NodeId, NodeKind, RegionId, RegionKind,
};

impl Function {
	/// Check the graph's invariants: every node's inputs before it but a
	/// phi's (a loop's back edge comes later), every phi a column of its
	/// join, every result an effect's, every join's rows in range, every
	/// effect in exactly one region's statements, and every branch inside
	/// the construct owning its join, giving a row that exists, each row
	/// given once (a loop header's row 0 by its entry).
	pub fn verify(&self) -> Result<(), VerifyError> {
		for index in 0..self.kinds.len() {
			let node = NodeId::new(index as u32);
			match self.kind(node) {
				NodeKind::Phi { join, column } => {
					if usize::from(join) >= self.joins.len()
						|| column as usize >= self.width(join)
					{
						return Err(VerifyError::BadPhi { node });
					}
				}
				NodeKind::Result { effect, .. } => {
					if usize::from(effect) >= self.effects.len() {
						return Err(VerifyError::BadResult { node });
					}
				}
				kind => {
					let mut after = false;
					visit_operands(kind, |input| {
						after |= u32::from(input) >= u32::from(node)
					});
					if after {
						return Err(VerifyError::InputAfterUser { node });
					}
				}
			}
		}
		for (index, join) in self.joins.iter().enumerate() {
			let end =
				join.rows as usize + join.edges as usize * join.columns.len();
			if end > self.rows.len() {
				return Err(VerifyError::RowsOutOfRange {
					join: JoinId::new(index as u32),
				});
			}
		}
		let mut row_starts = Vec::with_capacity(self.joins.len() + 1);
		row_starts.push(0usize);
		for join in &self.joins {
			row_starts.push(row_starts.last().unwrap() + join.edges as usize);
		}
		let mut verifier = Verifier {
			function: self,
			seen: vec![false; self.effects.len()],
			given: vec![false; *row_starts.last().unwrap()],
			row_starts,
			open: Vec::new(),
		};
		verifier.region(self.root)?;
		if let Some(effect) = verifier.seen.iter().position(|&seen| !seen) {
			return Err(VerifyError::Orphan {
				effect: EffectId::new(effect as u32),
			});
		}
		for index in 0..self.joins.len() {
			if verifier.given
				[verifier.row_starts[index]..verifier.row_starts[index + 1]]
				.iter()
				.any(|&given| !given)
			{
				return Err(VerifyError::RowCount {
					join: JoinId::new(index as u32),
				});
			}
		}
		Ok(())
	}
}

/// A node's own operands, unresolved: the verifier's order check reads
/// what was written, not what it resolved to.
fn visit_operands(kind: NodeKind, mut f: impl FnMut(NodeId)) {
	match kind {
		NodeKind::Unary(_, value) | NodeKind::Convert(_, value) => f(value),
		NodeKind::Binary(_, lhs, rhs) | NodeKind::Compare(_, lhs, rhs) => {
			f(lhs);
			f(rhs);
		}
		_ => {}
	}
}

#[derive(Debug)]
pub enum VerifyError {
	InputAfterUser {
		node: NodeId,
	},
	BadPhi {
		node: NodeId,
	},
	BadResult {
		node: NodeId,
	},
	RowsOutOfRange {
		join: JoinId,
	},
	/// An effect in no region, or in two.
	Orphan {
		effect: EffectId,
	},
	/// A branch to a join whose construct does not enclose it, or giving a
	/// row past its join's.
	BadBranch {
		effect: EffectId,
	},
	/// A join whose rows are not each given by one branch.
	RowCount {
		join: JoinId,
	},
}

struct Verifier<'a> {
	function: &'a Function,
	seen: Vec<bool>,
	/// Each row is supplied exactly once, including a header's entry.
	given: Vec<bool>,
	row_starts: Vec<usize>,
	/// The joins a branch here may reach.
	open: Vec<JoinId>,
}

impl Verifier<'_> {
	fn give(&mut self, join: JoinId, row: u32) -> Result<(), VerifyError> {
		if row >= self.function.edges(join) {
			return Err(VerifyError::RowCount { join });
		}
		let given =
			&mut self.given[self.row_starts[usize::from(join)] + row as usize];
		if *given {
			return Err(VerifyError::RowCount { join });
		}
		*given = true;
		Ok(())
	}

	fn region(&mut self, region: RegionId) -> Result<(), VerifyError> {
		let function = self.function;
		let region = &function.regions[usize::from(region)];
		for &effect in &function.sequence[region.effects.range()] {
			let seen = &mut self.seen[usize::from(effect)];
			if *seen {
				return Err(VerifyError::Orphan { effect });
			}
			*seen = true;
			match function.effects[usize::from(effect)] {
				Effect::Branch { join, row } => {
					if !self.open.contains(&join) || row >= function.edges(join)
					{
						return Err(VerifyError::BadBranch { effect });
					}
					self.give(join, row)?;
				}
				Effect::Region(nested) => self.nested(nested)?,
				_ => {}
			}
		}
		Ok(())
	}

	fn nested(&mut self, region: RegionId) -> Result<(), VerifyError> {
		let open = self.open.len();
		match self.function.regions[usize::from(region)].kind {
			RegionKind::Block { exit } => {
				self.open.push(exit);
				self.region(region)?;
			}
			RegionKind::Loop { header, exit } => {
				self.give(header, 0)?;
				self.open.extend([exit, header]);
				self.region(region)?;
			}
			RegionKind::If {
				then,
				otherwise,
				exit,
				..
			} => {
				self.open.push(exit);
				self.region(then)?;
				self.region(otherwise)?;
			}
			RegionKind::Switch {
				cases,
				default,
				exit,
				..
			} => {
				self.open.push(exit);
				for case in &self.function.cases[cases.range()] {
					self.region(case.region)?;
				}
				if let Some(default) = default {
					self.region(default)?;
				}
			}
			RegionKind::Arm => {
				unreachable!("an arm is entered by its construct")
			}
		}
		self.open.truncate(open);
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::super::tests::graph_of;
	use super::*;

	#[test]
	fn two_branches_cannot_supply_the_same_row() {
		let mut graph = graph_of(
			r#"
				func f(c: Bool, x: i32) -> i32 {
					if c { x } else { 0 }
				}
				export { f as "f" }
			"#,
			"f",
		);
		let mut branches = 0;
		for effect in &mut graph.effects {
			if let Effect::Branch { row, .. } = effect {
				*row = 0;
				branches += 1;
			}
		}
		assert_eq!(branches, 2);
		assert!(matches!(graph.verify(), Err(VerifyError::RowCount { .. })));
	}

	#[test]
	fn a_join_given_a_row_no_branch_gives_is_rejected() {
		let mut graph = graph_of(
			r#"
				func f(c: Bool, x: i32) -> i32 {
					if c { x } else { 0 }
				}
				export { f as "f" }
			"#,
			"f",
		);
		let join = &mut graph.joins[0];
		join.edges -= 1;
		assert!(matches!(graph.verify(), Err(VerifyError::BadBranch { .. })));
	}
}
