//! Optimize reached MIR function bodies through the structured graph.
//!
//! `optimize_reachable` coordinates root discovery and per-function optimization.
//! Each function's graph, uses, locations and placement expire after emission;
//! reachability marks live through codegen while MIR item IDs remain stable.

use std::hash::BuildHasher;
use std::ops::Range;

use hashbrown::HashTable;
use rustc_hash::FxBuildHasher;

use crate::index::index_newtype;
use crate::mir::{
	BinaryOp, CompareOp, ConvertOp, FunctionId, GlobalId, LoadAccess,
	LocalIndex, MemoryId, StaticEntryId, StoreAccess, UnaryOp,
};
use crate::wasm::ScalarType;

mod build;
mod dominators;
mod emit;
mod function;
mod locations;
mod placement;
mod reachability;
mod uses;
#[cfg(test)]
mod verify;

pub use build::build;
pub use dominators::Dominators;
pub use emit::emit;
#[cfg(test)]
pub(crate) use emit::emit_for_tests;
pub use function::optimize_function;
pub use locations::{JoinLocation, Location, Locations};
pub use placement::{Placement, PlacementError, ValuePlacement};
pub use reachability::{Reachability, optimize_reachable};
pub use uses::{UseSite, Uses};

index_newtype!(
	/// A value.
	NodeId
);
index_newtype!(
	/// A statement, pinned in program order.
	EffectId
);
index_newtype!(
	/// A block, a loop's body, an arm, a case, or the function's body.
	RegionId
);
index_newtype!(
	/// Where values from several edges meet.
	JoinId
);

/// `len` entries of a column from `start`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub struct Run {
	start: u32,
	len: u32,
}

impl Run {
	pub const EMPTY: Self = Self { start: 0, len: 0 };

	fn of(start: usize, end: usize) -> Self {
		Self {
			start: u32::try_from(start).unwrap(),
			len: u32::try_from(end - start).unwrap(),
		}
	}

	pub fn len(self) -> usize {
		self.len as usize
	}

	pub fn is_empty(self) -> bool {
		self.len == 0
	}

	fn range(self) -> Range<usize> {
		self.start as usize..(self.start + self.len) as usize
	}
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub enum NodeKind {
	Int(i64),
	/// The scalar's bits, so that it hashes. F32 uses the low 32 bits;
	/// F64 uses all 64 bits.
	Float(u64),
	Param(u32),
	Unary(UnaryOp, NodeId),
	Binary(BinaryOp, NodeId, NodeId),
	Compare(CompareOp, NodeId, NodeId),
	Convert(ConvertOp, NodeId),
	DataEnd(MemoryId),
	MemoryIndex(MemoryId),
	StaticPointer {
		entry: StaticEntryId,
		offset: u32,
	},
	/// Column `column` of `join`, where its rows disagree.
	Phi {
		join: JoinId,
		column: u32,
	},
	/// Result `index` of an effect.
	Result {
		effect: EffectId,
		index: u32,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub enum Effect {
	Call {
		function: FunctionId,
		args: Run,
	},
	Load {
		address: NodeId,
		offset: u32,
		memory: MemoryId,
		access: LoadAccess,
	},
	Store {
		address: NodeId,
		value: NodeId,
		offset: u32,
		memory: MemoryId,
		access: StoreAccess,
	},
	/// An operation that can trap: it runs where it is written.
	Trapping(TrappingOp),
	GlobalGet(GlobalId),
	GlobalSet(GlobalId, NodeId),
	MemorySize(MemoryId),
	MemoryGrow(MemoryId, NodeId),
	MemoryFill {
		memory: MemoryId,
		dst: NodeId,
		value: NodeId,
		len: NodeId,
	},
	MemoryCopy {
		dst_memory: MemoryId,
		src_memory: MemoryId,
		dst: NodeId,
		src: NodeId,
		len: NodeId,
	},
	/// A nested block, loop, `if` or switch.
	Region(RegionId),
	/// Control moves to `join`, giving its row `row`: a `break`, a
	/// `continue`, or a region's end where it falls through to its join.
	Branch {
		join: JoinId,
		row: u32,
	},
	Return {
		values: Run,
	},
	Unreachable,
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub enum TrappingOp {
	Binary(BinaryOp, NodeId, NodeId),
	Convert(ConvertOp, NodeId),
}

pub struct Region {
	kind: RegionKind,
	/// Into `Function::sequence`.
	effects: Run,
}

#[derive(Clone, Copy)]
pub enum RegionKind {
	/// A block: its breaks and its end reach `exit`.
	Block { exit: JoinId },
	/// A loop: its `continue`s and its end reach `header`, whose row 0 is
	/// the entry; its breaks reach `exit`.
	Loop { header: JoinId, exit: JoinId },
	/// Two arms, each a region, joined at `exit`. Without an `else` in MIR,
	/// `otherwise` only reaches `exit`.
	If {
		condition: NodeId,
		then: RegionId,
		otherwise: RegionId,
		exit: JoinId,
	},
	/// Each case an arm; `default` is absent where the cases are
	/// exhaustive.
	Switch {
		selector: NodeId,
		cases: Run,
		default: Option<RegionId>,
		exit: JoinId,
	},
	/// An arm, a case, or the function's body: statements, no join.
	Arm,
}

#[derive(Clone, Copy)]
pub struct Case {
	pub value: i64,
	pub region: RegionId,
}

pub struct Join {
	/// Into `Function::columns`.
	columns: Run,
	/// Where its rows start in `Function::rows`, row-major,
	/// `columns.len` wide.
	rows: u32,
	edges: u32,
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub enum Column {
	/// A local the construct writes.
	Local(LocalIndex),
	/// Scalar `i` of the construct's value.
	Result(u32),
}

pub struct Function {
	kinds: Vec<NodeKind>,
	types: Vec<ScalarType>,
	/// Indexed by node: itself, or a loop placeholder's replacement.
	/// Replacements can form chains; `resolve` follows them to the final node.
	node_replacements: Vec<NodeId>,
	/// Construction lookup for identical `(kind, type)` pairs, storing IDs only.
	interned_nodes: HashTable<NodeId>,
	/// Hashes node keys for `interned_nodes`.
	node_hasher: FxBuildHasher,
	/// Runs of the effects' operands.
	operands: Vec<NodeId>,

	effects: Vec<Effect>,
	/// Every region's statements, each region's a run.
	sequence: Vec<EffectId>,
	regions: Vec<Region>,
	cases: Vec<Case>,
	root: RegionId,

	joins: Vec<Join>,
	columns: Vec<Column>,
	rows: Vec<NodeId>,
}

impl Function {
	fn new() -> Self {
		Self {
			kinds: Vec::new(),
			types: Vec::new(),
			node_replacements: Vec::new(),
			interned_nodes: HashTable::new(),
			node_hasher: FxBuildHasher,
			operands: Vec::new(),
			effects: Vec::new(),
			sequence: Vec::new(),
			regions: Vec::new(),
			cases: Vec::new(),
			root: RegionId::new(0),
			joins: Vec::new(),
			columns: Vec::new(),
			rows: Vec::new(),
		}
	}

	/// The node `kind` of type `ty`: an equal one if there is one.
	fn node(&mut self, kind: NodeKind, ty: ScalarType) -> NodeId {
		let hash = self.node_hasher.hash_one((kind, ty));
		let Self {
			kinds,
			types,
			interned_nodes,
			..
		} = self;
		if let Some(&node) = interned_nodes.find(hash, |&node| {
			kinds[usize::from(node)] == kind && types[usize::from(node)] == ty
		}) {
			return node;
		}
		let node = self.push(kind, ty);
		let Self {
			kinds,
			types,
			interned_nodes,
			node_hasher,
			..
		} = self;
		interned_nodes.insert_unique(hash, node, |&node| {
			let index = usize::from(node);
			node_hasher.hash_one((kinds[index], types[index]))
		});
		node
	}

	/// A node no other equals: a phi, an effect's result.
	fn push(&mut self, kind: NodeKind, ty: ScalarType) -> NodeId {
		let node = NodeId::new(u32::try_from(self.kinds.len()).unwrap());
		self.kinds.push(kind);
		self.types.push(ty);
		self.node_replacements.push(node);
		node
	}

	fn push_operands(&mut self, values: &[NodeId]) -> Run {
		let start = self.operands.len();
		self.operands.extend_from_slice(values);
		Run::of(start, self.operands.len())
	}

	pub fn kind(&self, node: NodeId) -> NodeKind {
		self.kinds[usize::from(node)]
	}

	pub fn ty(&self, node: NodeId) -> ScalarType {
		self.types[usize::from(node)]
	}

	/// What `node` stands for: itself, or a resolved loop placeholder's
	/// value.
	pub fn resolve(&self, mut node: NodeId) -> NodeId {
		loop {
			let next = self.node_replacements[usize::from(node)];
			if next == node {
				return node;
			}
			node = next;
		}
	}

	pub fn width(&self, join: JoinId) -> usize {
		self.joins[usize::from(join)].columns.len()
	}

	pub fn edges(&self, join: JoinId) -> u32 {
		self.joins[usize::from(join)].edges
	}

	pub fn columns(&self, join: JoinId) -> &[Column] {
		&self.columns[self.joins[usize::from(join)].columns.range()]
	}

	/// Row `row` of `join`, unresolved.
	pub fn row(&self, join: JoinId, row: u32) -> &[NodeId] {
		let width = self.width(join);
		let start =
			self.joins[usize::from(join)].rows as usize + row as usize * width;
		&self.rows[start..start + width]
	}

	/// Resolved input occurrences and their read sites. Phi inputs are read
	/// on incoming rows, rather than at the merge itself.
	pub fn inputs(&self, node: NodeId, mut f: impl FnMut(NodeId, UseSite)) {
		let node = self.resolve(node);
		let mut input = |value| f(self.resolve(value), UseSite::Node(node));
		match self.kind(node) {
			NodeKind::Int(_)
			| NodeKind::Float(_)
			| NodeKind::Param(_)
			| NodeKind::DataEnd(_)
			| NodeKind::MemoryIndex(_)
			| NodeKind::StaticPointer { .. }
			| NodeKind::Result { .. } => {}
			NodeKind::Unary(_, value) | NodeKind::Convert(_, value) => {
				input(value)
			}
			NodeKind::Binary(_, lhs, rhs) | NodeKind::Compare(_, lhs, rhs) => {
				input(lhs);
				input(rhs);
			}
			NodeKind::Phi { join, column } => {
				for row in 0..self.edges(join) {
					f(
						self.resolve(self.row(join, row)[column as usize]),
						UseSite::Row { join, row },
					);
				}
			}
		}
	}

	/// An effect's operands, resolved. A branch has none: its row is read
	/// by the join's phis, not by the branch.
	pub fn operands(&self, effect: EffectId, mut f: impl FnMut(NodeId)) {
		let mut operand = |node| f(self.resolve(node));
		match self.effects[usize::from(effect)] {
			Effect::Call { args: values, .. } | Effect::Return { values } => {
				for &value in &self.operands[values.range()] {
					operand(value);
				}
			}
			Effect::Load { address, .. } => operand(address),
			Effect::GlobalSet(_, value) | Effect::MemoryGrow(_, value) => {
				operand(value)
			}
			Effect::Store { address, value, .. } => {
				operand(address);
				operand(value);
			}
			Effect::Trapping(TrappingOp::Binary(_, lhs, rhs)) => {
				operand(lhs);
				operand(rhs);
			}
			Effect::Trapping(TrappingOp::Convert(_, value)) => operand(value),
			Effect::MemoryFill {
				dst, value, len, ..
			} => {
				operand(dst);
				operand(value);
				operand(len);
			}
			Effect::MemoryCopy { dst, src, len, .. } => {
				operand(dst);
				operand(src);
				operand(len);
			}
			Effect::Region(region) => {
				match self.regions[usize::from(region)].kind {
					RegionKind::If { condition, .. } => operand(condition),
					RegionKind::Switch { selector, .. } => operand(selector),
					_ => {}
				}
			}
			Effect::GlobalGet(_)
			| Effect::MemorySize(_)
			| Effect::Branch { .. }
			| Effect::Unreachable => {}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mir::{self, MIR};
	use crate::testing::DiagnosticView;
	use crate::vfs;

	/// The graph of the function exported as `name` from `source`, as
	/// lowered (no inlining).
	pub(super) fn graph_of(source: &str, name: &str) -> Function {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)]),
				),
			)
			.unwrap();
		let mut unit = builder.build(root);
		let (diagnostics, mir) = crate::tir::build(&mut unit);
		DiagnosticView::new("tir", &diagnostics, &unit.files)
			.assert_no_errors();
		let mir: MIR = mir.expect("the source lowers");
		let id = mir
			.exports
			.iter()
			.find_map(|export| match export.item {
				mir::Item::Function(id)
					if unit.strings.resolve(export.name) == Some(name) =>
				{
					Some(id)
				}
				_ => None,
			})
			.expect("the export exists");
		let graph = build(&mir, id);
		graph.verify().expect("the graph is well formed");
		graph
	}

	/// The phis no resolution removed.
	fn phis(graph: &Function) -> Vec<NodeId> {
		(0..graph.kinds.len() as u32)
			.map(NodeId::new)
			.filter(|&node| {
				matches!(graph.kind(node), NodeKind::Phi { .. })
					&& graph.resolve(node) == node
			})
			.collect()
	}

	fn loop_header(graph: &Function) -> JoinId {
		graph
			.regions
			.iter()
			.find_map(|region| match region.kind {
				RegionKind::Loop { header, .. } => Some(header),
				_ => None,
			})
			.expect("a loop")
	}

	/// Arms that leave a local with the same value merge to that value.
	#[test]
	fn arms_that_agree_need_no_phi() {
		let graph = graph_of(
			r#"
				func f(c: Bool, x: i32) -> i32 {
					local mut y: i32 = 0;
					if c { y = x } else { y = x };
					y
				}
				export { f as "f" }
			"#,
			"f",
		);
		assert!(phis(&graph).is_empty());
	}

	/// A block's join merges only what the block writes: here its value,
	/// not the locals around it.
	#[test]
	fn a_block_join_has_columns_only_for_what_it_writes() {
		let graph = graph_of(
			r#"
				func f(a: i32, b: i32) -> i32 {
					local s = a + b;
					local r: i32 = block :done {
						if b > 0 { break :done 1 };
						2
					};
					s + r
				}
				export { f as "f" }
			"#,
			"f",
		);
		let exit = graph
			.regions
			.iter()
			.find_map(|region| match region.kind {
				RegionKind::Block { exit } => Some(exit),
				_ => None,
			})
			.expect("a block");
		assert_eq!(graph.columns(exit), &[Column::Result(0)]);
		assert_eq!(graph.edges(exit), 2);
		assert_eq!(phis(&graph).len(), 1);
	}

	/// The placeholder of `local` at `header`.
	fn placeholder(graph: &Function, header: JoinId, local: u32) -> NodeId {
		let column = graph
			.columns(header)
			.iter()
			.position(|&column| column == Column::Local(LocalIndex::new(local)))
			.expect("the local is a column") as u32;
		(0..graph.kinds.len() as u32)
			.map(NodeId::new)
			.find(|&node| {
				graph.kind(node)
					== NodeKind::Phi {
						join: header,
						column,
					}
			})
			.expect("its placeholder")
	}

	/// A loop's header merges the locals its body writes (lowering's
	/// temporaries among them, whose phis nothing reads) and no others.
	#[test]
	fn a_loop_header_merges_only_the_locals_its_body_writes() {
		// Locals: `n` 0, `k` 1, `i` 2, `s` 3.
		let graph = graph_of(
			r#"
				func sum(n: i32) -> i32 {
					local k: i32 = n * 2;
					local mut i: i32 = 0;
					local mut s: i32 = 0;
					loop {
						if i == n { break };
						s += i + k;
						i += 1;
					};
					s
				}
				export { sum as "sum" }
			"#,
			"sum",
		);
		let header = loop_header(&graph);
		let columns = graph.columns(header);
		for local in [2, 3] {
			assert!(columns.contains(&Column::Local(LocalIndex::new(local))));
		}
		for local in [0, 1] {
			assert!(!columns.contains(&Column::Local(LocalIndex::new(local))));
		}
		// Entry and the back edge.
		assert_eq!(graph.edges(header), 2);
	}

	/// A placeholder whose back edge gives it back unchanged is its entry
	/// value.
	#[test]
	fn a_loop_placeholder_given_back_unchanged_resolves() {
		// Locals: `n` 0, `x` 1, `i` 2, `y` 3.
		let graph = graph_of(
			r#"
				func f(n: i32, x: i32) -> i32 {
					local mut i: i32 = 0;
					local mut y: i32 = x;
					loop {
						if i == n { break };
						y = y;
						i += 1;
					};
					y
				}
				export { f as "f" }
			"#,
			"f",
		);
		let header = loop_header(&graph);
		let y = placeholder(&graph, header, 3);
		assert_eq!(graph.kind(graph.resolve(y)), NodeKind::Param(1));
		let i = placeholder(&graph, header, 2);
		assert_eq!(graph.resolve(i), i);
	}
}
