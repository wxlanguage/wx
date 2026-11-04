//! Places in linear memory: reading one, writing one, and taking its
//! address.
//!
//! Every place is reached through a pointer (`p.*`), with fields after it
//! (`p.*.x.y`), so it lowers to the pointer, evaluated once, a constant byte
//! offset (TIR's, the fields' offsets in declaration order summed), and the
//! memory the pointer's type names. An element (`s[i]`) moves the pointer:
//! it is checked against the length and scaled by the element's size, and
//! the fields after it are the constant offset. `Slice::len` and
//! `Slice::as_ref`, which the compiler supplies, read the same two parts of
//! a pointer to a slice or an array (`sequence_length`, `sequence_base`). A write evaluates its value first and
//! the place's address after it, as an assignment to a local does; a
//! compound write then reads the place, applies the operation, and writes
//! it back through the same address.

use super::{
	Body, FunctionInstance, FunctionState, Lowerer, binary_kind,
	canonical_narrow, mir,
};
use crate::ast::BinaryOp;
use crate::diagnostics::TextSpan;
use crate::tir::body::{ExprIdx, Place, PlaceIdx, PlaceKind};
use crate::tir::bounds::AssumptionEnvIdx;
use crate::tir::defs::FunctionIdx;
use crate::tir::types::{GenericArgs, Type, TypeIndex};

/// Where a place's bytes are: `offset` bytes past the address `pointer`
/// computes, in `memory`.
#[derive(Clone, Copy)]
struct Address {
	pointer: mir::ExprId,
	offset: u32,
	memory: mir::MemoryId,
}

/// What a compound write applies to the value it reads.
#[derive(Clone, Copy)]
pub(super) enum Operation {
	/// A primitive scalar's operator.
	Primitive(BinaryOp),
	/// An operator trait's method: the impl's, or the trait's declaration
	/// that the place's type selects.
	Method {
		method: FunctionIdx,
		type_args: GenericArgs,
	},
}

impl Lowerer<'_, '_, '_, '_> {
	/// `place`'s address. Its pointer may diverge (`Never`), in which case
	/// the caller returns it in place of the access.
	fn lower_place(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		place: PlaceIdx,
	) -> Result<Address, ()> {
		let data = *body.place(place);
		match data.kind {
			PlaceKind::Deref { pointer } => {
				let pointer = self.lower_expr(body, state, pointer)?;
				let memory =
					self.substitute(data.memory, state.env, &state.args);
				Ok(Address {
					pointer,
					offset: 0,
					memory: self.memory_of_type(memory),
				})
			}
			PlaceKind::Field { object, field } => {
				let address = self.lower_place(body, state, object)?;
				let object_ty = body.place(object).ty;
				let object_ty =
					self.substitute(object_ty, state.env, &state.args);
				let object_ty =
					self.normalize_type(object_ty, state.file_id, data.span)?;
				let layout = match self
					.context
					.aggregate_layout(AssumptionEnvIdx::ROOT, object_ty)
				{
					Ok(Some(layout)) => layout,
					// A slice as the last field leaves the aggregate unsized.
					Ok(None) => {
						self.unsupported(
							state.file_id,
							data.span,
							"a field of an aggregate with no layout (an \
							 unsized type)",
						)?;
						unreachable!()
					}
					// Checking reported a failure on this type.
					Err(_) => return Err(()),
				};
				let offset =
					self.context.solver.layouts.aggregate(layout).fields
						[usize::from(field)];
				Ok(Address {
					offset: address.offset + offset,
					..address
				})
			}
			PlaceKind::Element { object, index } => {
				self.lower_element(body, state, data, object, index)
			}
		}
	}

	/// `sequence[index]`: the sequence's address, then the index, each
	/// evaluated once into a temporary; a trap unless `index < len`, compared
	/// unsigned; and the address `base + index * stride`. A slice's address
	/// and length are its pointer's; an array is any place (`p.*`, a field,
	/// an element), its length its type's, and the constant offset of its
	/// place carries over to the element, as later fields' do.
	fn lower_element(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		element: Place,
		object: PlaceIdx,
		index: ExprIdx,
	) -> Result<Address, ()> {
		let (file_id, span) = (state.file_id, element.span);
		let sequence = *body.place(object);
		let memory = self.substitute(sequence.memory, state.env, &state.args);
		let memory = self.memory_of_type(memory);
		let sequence_ty = self.substitute(sequence.ty, state.env, &state.args);
		let sequence_ty = self.normalize_type(sequence_ty, file_id, span)?;
		let element_ty = self.substitute(element.ty, state.env, &state.args);
		let element_ty = self.normalize_type(element_ty, file_id, span)?;
		let stride = match self
			.context
			.memory_layout(AssumptionEnvIdx::ROOT, element_ty)
		{
			Ok(Some(layout)) => layout.size,
			Ok(None) => {
				self.unsupported(
					file_id,
					span,
					"an element with no linear-memory layout",
				)?;
				unreachable!()
			}
			// Checking reported a failure on this type.
			Err(_) => return Err(()),
		};

		// A slice is reached through its pointer, which holds its length;
		// an array is wherever its place is, as a field is.
		let is_slice = matches!(
			self.context.types.resolve(sequence_ty),
			Type::Slice { .. }
		);
		let (pointer, offset) = match sequence.kind {
			PlaceKind::Deref { pointer } if is_slice => {
				(self.lower_expr(body, state, pointer)?, 0)
			}
			_ if is_slice => {
				self.unsupported(
					file_id,
					sequence.span,
					"a slice that is a field (an unsized type)",
				)?;
				unreachable!()
			}
			_ => {
				let address = self.lower_place(body, state, object)?;
				(address.pointer, address.offset)
			}
		};
		if state.ty(pointer) == mir::ValueType::Never {
			return Ok(Address {
				pointer,
				offset,
				memory,
			});
		}
		let pointer_ty = state.ty(pointer);
		let (set_pointer, pointer_local) = self.temporary(state, pointer);
		let mut prefix = vec![set_pointer];

		let index = self.lower_expr(body, state, index)?;
		if state.ty(index) == mir::ValueType::Never {
			return Ok(Address {
				pointer: self.sequence(state, prefix, index),
				offset,
				memory,
			});
		}
		let size_ty = state.ty(index);
		let (set_index, index_local) = self.temporary(state, index);
		prefix.push(set_index);
		let index =
			state.push(mir::ExprKind::LocalGet { local: index_local }, size_ty);

		let base = self.sequence_base(state, pointer_local, pointer_ty);
		let length = self.sequence_length(
			state,
			pointer_local,
			pointer_ty,
			sequence_ty,
			size_ty,
		);

		let out_of_bounds = state.push(
			mir::ExprKind::Compare {
				op: mir::CompareOp::Ge,
				lhs: index,
				rhs: length,
			},
			mir::ValueType::Bool,
		);
		let trap =
			state.push(mir::ExprKind::Unreachable, mir::ValueType::Never);
		prefix.push(state.push(
			mir::ExprKind::IfElse {
				condition: out_of_bounds,
				then: trap,
				otherwise: None,
			},
			mir::ValueType::Unit,
		));

		let address_ty = state.ty(base);
		let address = match stride {
			0 => base,
			_ => {
				let index = state.push(
					mir::ExprKind::LocalGet { local: index_local },
					size_ty,
				);
				let scaled = match stride {
					1 => index,
					_ => {
						let stride = state.push(
							mir::ExprKind::Int {
								value: i64::from(stride),
							},
							size_ty,
						);
						state.push(
							mir::ExprKind::Binary {
								op: mir::BinaryOp::Mul,
								lhs: index,
								rhs: stride,
							},
							size_ty,
						)
					}
				};
				let scaled = state.push(
					mir::ExprKind::Transmute { value: scaled },
					address_ty,
				);
				state.push(
					mir::ExprKind::Binary {
						op: mir::BinaryOp::Add,
						lhs: base,
						rhs: scaled,
					},
					address_ty,
				)
			}
		};
		Ok(Address {
			pointer: self.sequence(state, prefix, address),
			offset,
			memory,
		})
	}

	/// The address a pointer to a slice or an array holds, read from the
	/// temporary `local` holding the pointer, of `pointer_ty`: a slice's
	/// first scalar, or the whole thin pointer.
	fn sequence_base(
		&self,
		state: &mut FunctionState,
		local: mir::LocalIndex,
		pointer_ty: mir::ValueType,
	) -> mir::ExprId {
		match pointer_ty {
			mir::ValueType::Aggregate { aggregate_index } => {
				let address_ty =
					self.aggregates.get(aggregate_index).scalars[0];
				state.push(
					mir::ExprKind::AggregateGet {
						local,
						range: mir::ScalarRange::new(0, 1),
					},
					address_ty,
				)
			}
			_ => state.push(mir::ExprKind::LocalGet { local }, pointer_ty),
		}
	}

	/// The length of the slice or array (`sequence_ty`, concrete) a pointer
	/// in the temporary `local` points at, as `size_ty`, its memory's
	/// `Size`: a slice's metadata, or an array's length, a constant.
	fn sequence_length(
		&self,
		state: &mut FunctionState,
		local: mir::LocalIndex,
		pointer_ty: mir::ValueType,
		sequence_ty: TypeIndex,
		size_ty: mir::ValueType,
	) -> mir::ExprId {
		match pointer_ty {
			mir::ValueType::Aggregate { aggregate_index } => {
				let length_ty = self.aggregates.get(aggregate_index).scalars[1];
				debug_assert_eq!(length_ty, size_ty);
				state.push(
					mir::ExprKind::AggregateGet {
						local,
						range: mir::ScalarRange::new(1, 1),
					},
					length_ty,
				)
			}
			_ => {
				let Type::Array { length, .. } =
					*self.context.types.resolve(sequence_ty)
				else {
					unreachable!("a thin pointer to a sequence is an array's")
				};
				let Type::Value { bits } = *self.context.types.resolve(length)
				else {
					unreachable!("a concrete array's length is a value")
				};
				state.push(mir::ExprKind::Int { value: bits as i64 }, size_ty)
			}
		}
	}

	/// A call of a function the compiler supplies, `callee` the
	/// declaration's instance (`[Self, M]` for `Slice`'s), on the value of
	/// `receiver`, evaluated once: `len` is the sequence's length and
	/// `as_ref` its address, as `sequence_length` and `sequence_base` read
	/// them.
	pub(super) fn lower_supplied(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		callee: FunctionInstance,
		receiver: ExprIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let (file_id, span) = (state.file_id, body.span(expr));
		let intrinsics = &self.context.defs.intrinsics;
		let function = Some(callee.function);
		let is_len = function == intrinsics.slice_len;
		if !is_len && function != intrinsics.slice_as_ref {
			self.unsupported(
				file_id,
				span,
				"a call of a function reference (`call_ref`)",
			)?;
			unreachable!()
		}
		let sequence_ty = self.context.types.list(callee.args)[0];
		let sequence_ty = self.normalize_type(sequence_ty, file_id, span)?;
		let pointer = self.lower_expr(body, state, receiver)?;
		if state.ty(pointer) == mir::ValueType::Never {
			return Ok(pointer);
		}
		let pointer_ty = state.ty(pointer);
		let (set, local) = self.temporary(state, pointer);
		let value = if is_len {
			self.sequence_length(state, local, pointer_ty, sequence_ty, ty)
		} else {
			self.sequence_base(state, local, pointer_ty)
		};
		debug_assert_eq!(state.ty(value), ty);
		Ok(self.sequence(state, vec![set], value))
	}

	/// `value` stored in a fresh temporary: the store, and the temporary,
	/// which the caller reads as often as it needs.
	fn temporary(
		&mut self,
		state: &mut FunctionState,
		value: mir::ExprId,
	) -> (mir::ExprId, mir::LocalIndex) {
		let ty = state.ty(value);
		let local = self.push_temp_local(state, ty);
		let set = state.push(
			mir::ExprKind::LocalSet { local, value },
			mir::ValueType::Unit,
		);
		(set, local)
	}

	/// The MIR type of the value stored at `place`, which must have bytes
	/// in linear memory.
	fn place_type(
		&mut self,
		body: &Body,
		state: &FunctionState,
		place: PlaceIdx,
	) -> Result<mir::ValueType, ()> {
		let data = *body.place(place);
		let ty = self.substitute(data.ty, state.env, &state.args);
		let lowered = self.lower_type(ty, state.file_id, data.span)?;
		let has_bytes = match lowered {
			mir::ValueType::Never => false,
			mir::ValueType::Aggregate { aggregate_index } => {
				self.aggregates.get(aggregate_index).memory.is_some()
			}
			_ => true,
		};
		if !has_bytes {
			self.unsupported(
				state.file_id,
				data.span,
				"a value with no linear-memory layout in memory",
			)?;
			unreachable!()
		}
		Ok(lowered)
	}

	/// A load of `place`'s address, offset and memory, of type `ty`.
	fn load(
		state: &mut FunctionState,
		address: Address,
		pointer: mir::ExprId,
		ty: mir::ValueType,
	) -> mir::ExprId {
		state.push(
			mir::ExprKind::PointerLoad {
				pointer,
				offset: address.offset,
				memory: address.memory,
			},
			ty,
		)
	}

	fn store(
		state: &mut FunctionState,
		address: Address,
		pointer: mir::ExprId,
		value: mir::ExprId,
	) -> mir::ExprId {
		state.push(
			mir::ExprKind::PointerStore {
				pointer,
				value,
				offset: address.offset,
				memory: address.memory,
			},
			mir::ValueType::Unit,
		)
	}

	/// `place` read: `p.*`, `p.*.x`. A zero-sized value takes no bytes, so
	/// only its pointer runs.
	pub(super) fn lower_load(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		place: PlaceIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let ty = match ty {
			mir::ValueType::Never => ty,
			_ => self.place_type(body, state, place)?,
		};
		let address = self.lower_place(body, state, place)?;
		if state.ty(address.pointer) == mir::ValueType::Never {
			return Ok(address.pointer);
		}
		if ty == mir::ValueType::Unit {
			let drop = state.push(
				mir::ExprKind::Drop {
					value: address.pointer,
				},
				mir::ValueType::Unit,
			);
			let unit = state.push(mir::ExprKind::Noop, mir::ValueType::Unit);
			return Ok(self.sequence(state, vec![drop], unit));
		}
		Ok(Self::load(state, address, address.pointer, ty))
	}

	/// `place.&`: the place's address, its fields' offset added. A shared
	/// pointer to a place has the place's memory, so its width is the
	/// pointer's it was reached through.
	pub(super) fn lower_address_of(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		place: PlaceIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let address = self.lower_place(body, state, place)?;
		if state.ty(address.pointer) == mir::ValueType::Never
			|| address.offset == 0
		{
			return Ok(address.pointer);
		}
		let offset = state.push(
			mir::ExprKind::Int {
				value: i64::from(address.offset),
			},
			ty,
		);
		Ok(state.push(
			mir::ExprKind::Binary {
				op: mir::BinaryOp::Add,
				lhs: address.pointer,
				rhs: offset,
			},
			ty,
		))
	}

	/// `place = value`: the value runs first, then the place's address, then
	/// the write.
	pub(super) fn lower_store(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		place: PlaceIdx,
		value: ExprIdx,
	) -> Result<mir::ExprId, ()> {
		let ty = self.place_type(body, state, place)?;
		let value = self.lower_expr(body, state, value)?;
		if state.ty(value) == mir::ValueType::Never {
			return Ok(value);
		}
		let mut prefix = vec![];
		let value = if ty == mir::ValueType::Unit {
			prefix.push(value);
			None
		} else {
			let (set, get) = self.spill(state, value);
			prefix.push(set);
			Some(get)
		};
		let address = self.lower_place(body, state, place)?;
		if state.ty(address.pointer) == mir::ValueType::Never {
			return Ok(self.sequence(state, prefix, address.pointer));
		}
		let write = match value {
			Some(value) => Self::store(state, address, address.pointer, value),
			None => state.push(
				mir::ExprKind::Drop {
					value: address.pointer,
				},
				mir::ValueType::Unit,
			),
		};
		Ok(self.sequence(state, prefix, write))
	}

	/// `place op= value`: the value runs first, then the place's address,
	/// held in a temporary; the place is read through it, `operation`
	/// applied, and the result written back through it.
	pub(super) fn lower_compound_store(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		place: PlaceIdx,
		value: ExprIdx,
		operation: Operation,
		span: TextSpan,
	) -> Result<mir::ExprId, ()> {
		let ty = self.place_type(body, state, place)?;
		let value = self.lower_expr(body, state, value)?;
		if state.ty(value) == mir::ValueType::Never {
			return Ok(value);
		}
		let (set_value, operand) = self.spill(state, value);
		let address = self.lower_place(body, state, place)?;
		if state.ty(address.pointer) == mir::ValueType::Never {
			return Ok(self.sequence(state, vec![set_value], address.pointer));
		}
		let pointer_ty = state.ty(address.pointer);
		let (set_pointer, read_pointer) = self.spill(state, address.pointer);
		let mir::ExprKind::LocalGet { local } =
			state.mir_body.kind(read_pointer)
		else {
			unreachable!("a spill reads its temporary back")
		};
		let read = Self::load(state, address, read_pointer, ty);
		let result = match operation {
			Operation::Primitive(op) => {
				let Some(kind) = binary_kind(op, read, operand) else {
					unreachable!("a compound store's operator is arithmetic")
				};
				let result = state.push(kind, ty);
				canonical_narrow(state, result, ty)
			}
			Operation::Method { method, type_args } => {
				let (callee, callee_id) =
					self.callee(state, method, type_args, span)?;
				let (_, callee_params, ..) = self.lower_signature(callee)?;
				if callee_params.len() != 2 {
					self.unsupported(
						state.file_id,
						span,
						"a compound assignment method that is not a binary \
						 operator",
					)?;
					unreachable!()
				}
				self.build_call(state, callee_id, vec![read, operand], ty)
			}
		};
		let write_pointer =
			state.push(mir::ExprKind::LocalGet { local }, pointer_ty);
		let write = Self::store(state, address, write_pointer, result);
		Ok(self.sequence(state, vec![set_value, set_pointer], write))
	}
}
