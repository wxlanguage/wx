use std::collections::{HashMap, VecDeque, hash_map::Entry};

use crate::ast::{self, DefIdGenerator};

use super::types::TypeId;

/// One generic function instance waiting to be lowered.
pub(super) struct PendingMono {
	pub(super) original_id: ast::DefId,
	pub(super) type_args: Box<[TypeId]>,
	pub(super) mono_id: ast::DefId,
}

/// Assigns stable synthetic ids to generic function instantiations and owns
/// the work queue populated while MIR expressions are lowered.
pub(super) struct MonoRegistry {
	map: HashMap<(ast::DefId, Box<[TypeId]>), ast::DefId>,
	pending: VecDeque<PendingMono>,
	id_generator: DefIdGenerator,
}

impl MonoRegistry {
	pub(super) fn new(id_generator: DefIdGenerator) -> Self {
		Self {
			map: HashMap::new(),
			pending: VecDeque::new(),
			id_generator,
		}
	}

	pub(super) fn generate_id(&mut self) -> ast::DefId {
		self.id_generator.generate()
	}

	pub(super) fn get_or_insert(
		&mut self,
		original_id: ast::DefId,
		type_args: Box<[TypeId]>,
	) -> ast::DefId {
		match self.map.entry((original_id, type_args)) {
			Entry::Occupied(entry) => *entry.get(),
			Entry::Vacant(entry) => {
				let mono_id = self.id_generator.generate();
				// The map keeps the original allocation. Only the pending
				// work item needs a separate owned copy.
				let type_args = entry.key().1.clone();
				entry.insert(mono_id);

				self.pending.push_back(PendingMono {
					original_id,
					type_args,
					mono_id,
				});

				mono_id
			}
		}
	}

	pub(super) fn next_pending(&mut self) -> Option<PendingMono> {
		self.pending.pop_front()
	}
}
