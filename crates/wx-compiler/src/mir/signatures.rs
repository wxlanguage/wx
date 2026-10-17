use std::collections::HashMap;

use super::{FunctionSignature, SignatureIndex};

/// Interns concrete MIR function signatures and owns their final table.
#[derive(Default)]
pub(super) struct SignatureInterner {
	lookup: HashMap<FunctionSignature, SignatureIndex>,
}

impl SignatureInterner {
	pub(super) fn intern(
		&mut self,
		signature: FunctionSignature,
	) -> SignatureIndex {
		let next = SignatureIndex::new(self.lookup.len() as u32);
		*self.lookup.entry(signature).or_insert(next)
	}

	pub(super) fn finish(self) -> Vec<FunctionSignature> {
		let mut entries: Vec<Option<FunctionSignature>> =
			vec![None; self.lookup.len()];

		for (signature, index) in self.lookup {
			let slot = &mut entries[usize::from(index)];
			debug_assert!(slot.is_none());
			*slot = Some(signature);
		}

		entries
			.into_iter()
			.map(|entry| {
				entry.expect(
					"signature interner produced a non-contiguous index",
				)
			})
			.collect()
	}
}
