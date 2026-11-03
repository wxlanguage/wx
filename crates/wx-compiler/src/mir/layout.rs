use std::collections::HashMap;

use super::{
	Aggregate, AggregateIndex, Field, Layout, Scalar, ScalarTable, ValueType,
};

/// Builds the final MIR aggregate table from layouts decided by TIR.
///
/// This type deliberately computes no sizes and no offsets: [`super`]
/// receives them from `tir::AggregateLayout`, which is the one layout
/// authority. The interner keeps declaration order for fields and scalar
/// slots and only pairs each with the byte offset TIR supplied.
#[derive(Default)]
pub(crate) struct AggregateInterner {
	lookup: HashMap<Box<[ValueType]>, AggregateIndex>,
	entries: Vec<Aggregate>,
}

impl AggregateInterner {
	#[inline]
	pub(crate) fn get(&self, index: AggregateIndex) -> &Aggregate {
		&self.entries[usize::from(index)]
	}

	/// Intern one aggregate.
	///
	/// `field_types` and `offsets` are both in declaration order, and
	/// `layout` is the whole aggregate's TIR-decided size and alignment.
	/// Nested aggregates must already be interned, so their own slot tables
	/// can be rebased onto this aggregate's offsets.
	pub(crate) fn intern(
		&mut self,
		field_types: Box<[ValueType]>,
		offsets: Box<[u32]>,
		layout: Layout,
	) -> AggregateIndex {
		assert_eq!(
			field_types.len(),
			offsets.len(),
			"every field must have exactly one offset"
		);
		if let Some(&index) = self.lookup.get(&field_types) {
			return index;
		}

		let fields: Box<[Field]> = field_types
			.iter()
			.copied()
			.zip(offsets.iter().copied())
			.map(|(ty, offset)| Field { ty, offset })
			.collect();

		let mut scalars = Vec::with_capacity(fields.len());
		let mut field_starts = Vec::with_capacity(fields.len() + 1);
		for field in fields.iter() {
			field_starts.push(scalars.len() as u32);
			match field.ty {
				ValueType::Unit | ValueType::Never => {}
				ValueType::Aggregate { aggregate_index } => {
					let nested = self.get(aggregate_index);
					scalars.extend(nested.scalars.iter().map(|scalar| {
						Scalar {
							ty: scalar.ty,
							offset: field.offset + scalar.offset,
						}
					}));
				}
				ty => scalars.push(Scalar {
					ty,
					offset: field.offset,
				}),
			}
		}
		field_starts.push(scalars.len() as u32);

		let index = AggregateIndex::new(self.entries.len() as u32);
		self.lookup.insert(field_types, index);
		self.entries.push(Aggregate {
			fields,
			layout,
			scalars: ScalarTable {
				entries: scalars.into_boxed_slice(),
				field_starts: field_starts.into_boxed_slice(),
			},
		});
		index
	}

	pub(crate) fn finish(self) -> Box<[Aggregate]> {
		self.entries.into_boxed_slice()
	}
}
