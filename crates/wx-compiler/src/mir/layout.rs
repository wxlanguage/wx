use super::{Aggregate, AggregateIndex, AggregateMemory, ValueType};

/// Owns materialized flat representations. Lowering caches conversions by
/// concrete TIR type; there is no second content/layout interner in MIR.
/// All memory offsets, sizes, and alignments must already be decided by TIR.
#[derive(Default)]
pub(crate) struct AggregateTable {
	entries: Vec<Aggregate>,
}

impl AggregateTable {
	pub(crate) fn get(&self, index: AggregateIndex) -> &Aggregate {
		&self.entries[usize::from(index)]
	}

	pub(crate) fn push(
		&mut self,
		scalars: Box<[ValueType]>,
		memory: Option<AggregateMemory>,
	) -> AggregateIndex {
		assert!(!scalars.is_empty(), "zero-sized values use Unit");
		assert!(scalars.iter().all(|ty| !matches!(ty,
			ValueType::Aggregate { .. } | ValueType::Unit | ValueType::Never
		)), "a flat pack contains scalar types only");
		if let Some(memory) = &memory {
			assert_eq!(scalars.len(), memory.offsets.len());
		}
		let index = AggregateIndex::new(self.entries.len().try_into().unwrap());
		self.entries.push(Aggregate { scalars, memory });
		index
	}

	pub(crate) fn finish(self) -> Box<[Aggregate]> {
		self.entries.into_boxed_slice()
	}
}
