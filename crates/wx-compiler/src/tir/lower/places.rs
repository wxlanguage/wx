//! Places in linear memory: reading one, writing one, and taking its
//! address.
//!
//! Every place is reached through a pointer (`p.*`), with fields after it
//! (`p.*.x.y`), so it lowers to the pointer, evaluated once, a constant byte
//! offset (TIR's, the fields' offsets in declaration order summed), and the
//! memory the pointer's type names. A write evaluates its value first and
//! the place's address after it, as an assignment to a local does; a
//! compound write then reads the place, applies the operation, and writes
//! it back through the same address.

use super::{Body, FunctionState, Lowerer, binary_kind, canonical_narrow, mir};
use crate::ast::BinaryOp;
use crate::diagnostics::TextSpan;
use crate::tir::body::{ExprIdx, PlaceIdx, PlaceKind};
use crate::tir::defs::FunctionIdx;
use crate::tir::bounds::AssumptionEnvIdx;
use crate::tir::types::GenericArgs;

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
				let Ok(Some(layout)) =
					self.context.aggregate_layout(AssumptionEnvIdx::ROOT, object_ty)
				else {
					unreachable!("a field's place is in a laid-out aggregate")
				};
				let offset =
					self.context.solver.layouts.aggregate(layout).fields
						[usize::from(field)];
				Ok(Address {
					offset: address.offset + offset,
					..address
				})
			}
			// Waits for the slices step: an element's address is checked
			// against its slice's length.
			PlaceKind::Element { .. } => {
				self.unsupported(
					state.file_id,
					data.span,
					"an element of a slice or an array (the static-data \
					 checkpoint)",
				)?;
				unreachable!()
			}
		}
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
