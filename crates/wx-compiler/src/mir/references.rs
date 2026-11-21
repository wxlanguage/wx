//! Module references shared by dependency discovery and ID remapping.
//!
//! Enumeration reports stored references, including duplicates, without
//! building a dependency graph. The module driver owns marking and scheduling.

use super::{
	AddressTarget, ConstInit, FunctionId, GlobalId, Item, MIR, MemoryId,
	StaticEntry, StaticEntryId,
};

/// A reachability target. Backing data is not an importable/exportable item.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Reference {
	Item(Item),
	Data(StaticEntryId),
}

/// One stored module ID, borrowed for remapping. Body-local indices and
/// import/signature table indices are deliberately separate.
pub enum ItemRef<'a> {
	Function(&'a mut FunctionId),
	Global(&'a mut GlobalId),
	Memory(&'a mut MemoryId),
	Data(&'a mut StaticEntryId),
}

impl ItemRef<'_> {
	pub fn target(&self) -> Reference {
		match self {
			Self::Function(id) => Reference::Item(Item::Function(**id)),
			Self::Global(id) => Reference::Item(Item::Global(**id)),
			Self::Memory(id) => Reference::Item(Item::Memory(**id)),
			Self::Data(id) => Reference::Data(**id),
		}
	}
}

impl Item {
	pub fn items_mut(&mut self, mut f: impl FnMut(ItemRef<'_>)) {
		match self {
			Self::Function(id) => f(ItemRef::Function(id)),
			Self::Global(id) => f(ItemRef::Global(id)),
			Self::Memory(id) => f(ItemRef::Memory(id)),
		}
	}
}

impl ConstInit {
	pub fn items_mut(&mut self, mut f: impl FnMut(ItemRef<'_>)) {
		match self {
			Self::Static { entry, .. } => f(ItemRef::Data(entry)),
			Self::DataEnd { memory } => f(ItemRef::Memory(memory)),
			Self::Int(_) | Self::Float(_) => {}
		}
	}
}

impl AddressTarget {
	pub fn items_mut(&mut self, mut f: impl FnMut(ItemRef<'_>)) {
		match self {
			Self::Entry(entry) => f(ItemRef::Data(entry)),
			Self::DataEnd(memory) => f(ItemRef::Memory(memory)),
		}
	}
}

impl StaticEntry {
	/// Placement memory first, followed by relocation targets in stored order.
	pub fn items_mut(&mut self, mut f: impl FnMut(ItemRef<'_>)) {
		f(ItemRef::Memory(&mut self.memory));
		for relocation in &mut self.relocations {
			relocation.target.items_mut(&mut f);
		}
	}
}

impl MIR {
	/// Exports of every kind and the start function. Imports are metadata of
	/// reached items, not roots. Duplicate roots are left to the worklist.
	pub fn roots(&self, mut f: impl FnMut(Reference)) {
		for export in &self.exports {
			f(Reference::Item(export.item));
		}
		if let Some(function) = self.start_function {
			f(Reference::Item(Item::Function(function)));
		}
	}

	/// Direct dependencies only. For functions this scans the current arena:
	/// the driver must optimize/replace a reached body before calling this.
	/// It does not infer control-flow reachability or chase transitive edges.
	///
	/// Memories have no outgoing edges: keeping a memory does not retain all
	/// candidate backing data in it. DATA_END retains only its memory.
	pub fn dependencies(&self, node: Reference, mut f: impl FnMut(Reference)) {
		match node {
			Reference::Item(Item::Function(id)) => {
				if let Some(code) = self.function(id).code() {
					for mut kind in code.body.kinds().iter().copied() {
						kind.items_mut(|reference| f(reference.target()));
					}
				}
			}
			Reference::Item(Item::Global(id)) => {
				if let Some(mut init) =
					self.global(id).origin.defined().copied()
				{
					init.items_mut(|reference| f(reference.target()));
				}
			}
			Reference::Item(Item::Memory(_)) => {}
			Reference::Data(id) => {
				let entry = &self.static_entries[usize::from(id)];
				f(Reference::Item(Item::Memory(entry.memory)));
				for relocation in &entry.relocations {
					let mut target = relocation.target;
					target.items_mut(|reference| f(reference.target()));
				}
			}
		}
	}
}

#[cfg(test)]
mod tests;
