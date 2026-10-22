use std::collections::HashMap;

use super::{
	Aggregate, AggregateIndex, Field, Layout, PhysIndex, Scalar, ScalarTable,
	ValueType,
};

impl Layout {
	fn pad_to_align(self) -> Self {
		Layout {
			size: (self.size + self.align - 1) & !(self.align - 1),
			align: self.align,
		}
	}
}

/// How an aggregate's fields are physically ordered in memory.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum FieldOrder {
	/// Fields are sorted by alignment descending to minimize padding.
	Sorted,
	/// Fields keep declaration order, as required by `#[fixed_order]` and
	/// fixed ABI aggregates such as slices.
	Fixed,
}

/// Interns physical aggregate layouts and owns their final MIR table.
#[derive(Default)]
pub(super) struct AggregateInterner {
	lookup: HashMap<(FieldOrder, Box<[ValueType]>), AggregateIndex>,
	entries: Vec<Aggregate>,
}

impl AggregateInterner {
	#[inline]
	pub(super) fn get(&self, index: AggregateIndex) -> &Aggregate {
		&self.entries[usize::from(index)]
	}

	pub(super) fn intern(
		&mut self,
		fields: Box<[ValueType]>,
		order: FieldOrder,
	) -> AggregateIndex {
		let key = (order, fields);
		if let Some(&index) = self.lookup.get(&key) {
			return index;
		}
		let (_, fields) = key;

		let mut sorted: Vec<(u32, Layout)> = fields
			.iter()
			.copied()
			.enumerate()
			.map(|(declaration, ty)| (declaration as u32, self.type_layout(ty)))
			.collect();
		if order == FieldOrder::Sorted {
			sorted.sort_by_key(|(_, layout)| std::cmp::Reverse(layout.align));
		}

		let mut layout = Layout { size: 0, align: 1 };
		let mut physical_fields = Vec::with_capacity(sorted.len());
		let mut declaration_to_physical = vec![PhysIndex::new(0); sorted.len()];
		for (physical, (declaration, field_layout)) in
			sorted.iter().copied().enumerate()
		{
			layout.size = (layout.size + field_layout.align - 1)
				& !(field_layout.align - 1);
			physical_fields.push(Field {
				ty: fields[declaration as usize],
				offset: layout.size,
			});
			layout.size += field_layout.size;
			layout.align = layout.align.max(field_layout.align);
			declaration_to_physical[declaration as usize] =
				PhysIndex::new(physical as u32);
		}
		layout = layout.pad_to_align();

		let mut scalars = Vec::with_capacity(physical_fields.len());
		let mut field_starts = Vec::with_capacity(physical_fields.len() + 1);
		for field in &physical_fields {
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
		self.lookup.insert((order, fields), index);
		self.entries.push(Aggregate {
			fields: physical_fields.into_boxed_slice(),
			layout,
			scalars: ScalarTable {
				entries: scalars.into_boxed_slice(),
				field_starts: field_starts.into_boxed_slice(),
			},
			decl_to_phys: declaration_to_physical.into_boxed_slice(),
		});
		index
	}

	pub(super) fn type_layout(&self, ty: ValueType) -> Layout {
		match ty {
			ValueType::Unit | ValueType::Never => Layout { size: 0, align: 1 },
			ValueType::U8 | ValueType::I8 | ValueType::Bool => {
				Layout { size: 1, align: 1 }
			}
			ValueType::U16 | ValueType::I16 => Layout { size: 2, align: 2 },
			ValueType::I32
			| ValueType::U32
			| ValueType::F32
			| ValueType::Function { .. } => Layout { size: 4, align: 4 },
			ValueType::I64 | ValueType::U64 | ValueType::F64 => {
				Layout { size: 8, align: 8 }
			}
			ValueType::Pointer { kind, .. } => {
				let size = kind.pointer_size();
				Layout { size, align: size }
			}
			ValueType::Aggregate { aggregate_index } => {
				self.get(aggregate_index).layout
			}
		}
	}

	pub(super) fn finish(self) -> Box<[Aggregate]> {
		self.entries.into_boxed_slice()
	}
}
