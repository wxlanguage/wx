//! How lowering holds a value of a struct, a tuple or a fat pointer on the
//! Wasm stack: its scalars, one MIR value each, in declaration pre-order,
//! nested values flattened and zero-sized ones dropped; and which of them
//! each field is. Built once per concrete type, the first time the type is
//! lowered, and read by every field of a value in locals, a pattern's
//! projection and a call's argument tuple.
//!
//! Only lowering reads it, so only lowering stores it. Its scalars' types
//! are MIR's signature table, read through the shape's MIR type; what
//! it adds is each field's range among them. Where a value's bytes are is
//! TIR's (`tir/layout.rs`), in the same order: a load or a store pairs this
//! shape's scalar `i` with the layout's.

use std::collections::HashMap;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::{FunctionState, Lowerer, mir};
use crate::diagnostics::{DiagnosticCode, TextSpan};
use crate::tir::defs::FieldIdx;
use crate::tir::types::{Type, TypeIndex};
use crate::vfs::FileId;

/// How many Wasm values one type may flatten to. A resource limit, not a
/// language rule: interned types share their parts, so a doubling chain
/// (`f((x, x))` in `f<T>`) is a handful of types that flatten to
/// exponentially many values, long before the recursion limit stops it.
/// Far above what a program writes by hand.
const SLOT_LIMIT: usize = 1 << 16;

/// Positions among one value's scalars: `len` of them from `start`. A
/// field's, among its struct's; read against anything indexed by those
/// positions (a run of locals holding the value, a pattern's projection).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct ScalarRange {
	pub(super) start: u32,
	pub(super) len: u32,
}

impl ScalarRange {
	pub(super) fn new(start: u32, len: u32) -> Self {
		Self { start, len }
	}
}

/// A run of `StackShapes::field_scalars`: one row per field, by declared
/// index.
#[derive(Clone, Copy)]
struct FieldList {
	start: u32,
	len: u32,
}

/// One type's shape.
#[derive(Clone, Copy)]
struct StackShape {
	/// Its MIR type: `Unit`, the one scalar, or the aggregate of its
	/// scalars.
	ty: mir::ValueType,
	fields: FieldList,
}

/// The shapes of the types lowered so far, which live as long as lowering.
#[derive(Default)]
pub(super) struct StackShapes {
	/// Each type's shape, by its normalized, concrete type.
	shapes: HashMap<TypeIndex, StackShape>,
	/// Each field's scalars, among its value's.
	field_scalars: Vec<ScalarRange>,
}

/// One field of a value being shaped: a source type, or a value with no
/// source type of its own (a fat pointer's address).
enum Field {
	Type(TypeIndex),
	Lowered(mir::ValueType),
}

impl Lowerer<'_, '_, '_, '_> {
	/// The scalars of field `field` of the concrete `ty`, among its
	/// value's.
	pub(super) fn field_range(
		&mut self,
		ty: TypeIndex,
		state: &FunctionState,
		field: FieldIdx,
		span: TextSpan,
	) -> Result<ScalarRange, ()> {
		let ty = self.normalize_type(ty, state.file_id, span)?;
		self.lower_type(ty, state.file_id, span)?;
		let fields = self.shapes.shapes[&ty].fields;
		let field = u32::from(field);
		assert!(field < fields.len, "a field of the type");
		Ok(self.shapes.field_scalars[(fields.start + field) as usize])
	}

	/// The MIR type of the struct, tuple or fat pointer `ty`, normalized and
	/// concrete, building its shape the first time.
	pub(super) fn lower_aggregate_type(
		&mut self,
		ty: TypeIndex,
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::ValueType, ()> {
		if let Some(shape) = self.shapes.shapes.get(&ty) {
			return Ok(shape.ty);
		}

		let fields = match *self.context.types.resolve(ty) {
			// The address has no TIR type of its own (`Pointer::address`
			// reads it as the memory's `Size`); MIR keeps it a pointer.
			Type::Pointer { to, memory, .. } => {
				let metadata = self.pointer_metadata(to, memory)?;
				let id = self.memory_of_type(memory);
				let address =
					self.memories[usize::from(id)].kind.address_type();
				vec![Field::Lowered(address), Field::Type(metadata)]
			}
			_ => self
				.aggregate_field_types(ty, file_id, span)?
				.into_iter()
				.map(Field::Type)
				.collect(),
		};
		// Every field is lowered before this shape's rows are pushed: a
		// nested struct pushes its own, and this shape's are one run.
		let mut lowered = Vec::with_capacity(fields.len());
		let mut count = 0;
		for field in fields {
			let field = match field {
				Field::Type(field) => self.lower_type(field, file_id, span)?,
				Field::Lowered(field) => field,
			};
			if field == mir::ValueType::Never {
				self.unsupported(
					file_id,
					span,
					"an uninhabited aggregate value",
				)?;
			}
			count += self.signatures.scalars(&field).len();
			// Every field passed this check when it was lowered, so this
			// stops a doubling chain after one step past the limit.
			if count > SLOT_LIMIT {
				self.report_slot_limit(ty, file_id, span);
				return Err(());
			}
			lowered.push(field);
		}

		let Self {
			shapes, signatures, ..
		} = self;
		let fields = FieldList {
			start: u32::try_from(shapes.field_scalars.len()).unwrap(),
			len: u32::try_from(lowered.len()).unwrap(),
		};
		let mut scalars = Vec::with_capacity(count);
		for field in &lowered {
			let start = u32::try_from(scalars.len()).unwrap();
			scalars.extend_from_slice(signatures.scalars(field));
			let len = u32::try_from(scalars.len()).unwrap() - start;
			shapes.field_scalars.push(ScalarRange::new(start, len));
		}
		// A value of one scalar is that scalar (`Char`, `Meters(u32)`).
		let ty_lowered = signatures.value_of(&scalars);
		shapes.shapes.insert(
			ty,
			StackShape {
				ty: ty_lowered,
				fields,
			},
		);
		Ok(ty_lowered)
	}

	fn report_slot_limit(
		&mut self,
		ty: TypeIndex,
		file_id: FileId,
		span: TextSpan,
	) {
		let name = self.context.type_formatter().display_type(ty);
		self.context.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::SlotLimit.code())
				.with_message(format!(
					"the type `{name}` is too large to lower"
				))
				.with_label(
					Label::primary(file_id, span)
						.with_message("a value of this type is used here"),
				)
				.with_note(format!(
					"a value is held as one Wasm value per scalar it contains, \
					 and the limit is {SLOT_LIMIT} for one type"
				)),
		);
	}
}
