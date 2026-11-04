//! Static data: the evaluator's allocations (`Solver::allocations`) as MIR's
//! static entries. An allocation becomes an entry the first time a value
//! lowered here points into it, together with every allocation its
//! relocations reach; entries with the same contents in the same memory are
//! one. Addresses are codegen's, which lays out only the entries something
//! reaches.

use std::hash::BuildHasher;

use hashbrown::HashTable;
use rustc_hash::{FxBuildHasher, FxHashMap};

use super::{Body, ExprIdx, FunctionState, Lowerer, mir};
use crate::tir::eval::{AddressTarget, AllocIdx};
use crate::tir::types::TypeIndex;

/// The entries lowering has made, indexed by `StaticEntryId`.
#[derive(Default)]
pub(super) struct StaticData {
	entries: Vec<mir::StaticEntry>,
	/// Each entry once, by contents.
	lookup: HashTable<mir::StaticEntryId>,
	hasher: FxBuildHasher,
	/// The entry each converted allocation became.
	of_allocation: FxHashMap<AllocIdx, mir::StaticEntryId>,
}

impl StaticData {
	/// `entry`'s id: an existing entry's if one has the same contents.
	fn intern(&mut self, entry: mir::StaticEntry) -> mir::StaticEntryId {
		let hash = self.hasher.hash_one(&entry);
		let entries = &self.entries;
		if let Some(&id) = self
			.lookup
			.find(hash, |&id| entries[usize::from(id)] == entry)
		{
			return id;
		}
		let id =
			mir::StaticEntryId::new(u32::try_from(self.entries.len()).unwrap());
		self.entries.push(entry);
		let (entries, hasher) = (&self.entries, &self.hasher);
		self.lookup.insert_unique(hash, id, |&id| {
			hasher.hash_one(&entries[usize::from(id)])
		});
		id
	}

	pub(super) fn finish(self) -> Vec<mir::StaticEntry> {
		self.entries
	}
}

impl Lowerer<'_, '_, '_, '_> {
	/// A piece of static data in `state`'s body (a literal, or a constant
	/// holding data, placed): its value for the instance, a pointer to its
	/// data. Its evaluation's failure is reported by the query.
	pub(super) fn lower_static(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let args: Box<[TypeIndex]> = state.args.clone();
		let value = (self.context)
			.static_value(state.instance.function, &args, expr)
			.ok_or(())?
			.to_vec();
		self.materialize_constant(
			state,
			state.file_id,
			body.span(expr),
			ty,
			&value,
		)
	}

	/// The static entry `alloc` is, converted with every allocation its
	/// relocations point into. An allocation only points into ones made
	/// before it, so this recursion ends.
	pub(super) fn static_entry(
		&mut self,
		alloc: AllocIdx,
	) -> mir::StaticEntryId {
		if let Some(&id) = self.statics.of_allocation.get(&alloc) {
			return id;
		}
		let allocation = &self.context.solver.allocations[usize::from(alloc)];
		let (memory, align, bytes, targets) = (
			allocation.memory,
			allocation.align,
			allocation.bytes.clone(),
			allocation.relocations.clone(),
		);
		let relocations = (targets.iter())
			.map(|&(offset, target)| mir::Relocation {
				offset,
				target: match target {
					AddressTarget::Allocation(alloc) => {
						mir::AddressTarget::Entry(self.static_entry(alloc))
					}
					AddressTarget::DataEnd(memory) => {
						mir::AddressTarget::DataEnd(self.memory(memory))
					}
				},
			})
			.collect();
		let entry = mir::StaticEntry {
			bytes,
			align,
			memory: self.memory(memory),
			relocations,
		};
		let id = self.statics.intern(entry);
		self.statics.of_allocation.insert(alloc, id);
		id
	}
}
