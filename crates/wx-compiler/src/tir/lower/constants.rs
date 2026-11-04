//! Concrete constant values: a `True`/`False` variant, an enum variant, or a
//! free `const`, read from the checker's memoized evaluation and written as
//! the MIR node its flat value calls for.
//!
//! Associating an abstract constant with an impl needs dispatch (and, for a
//! generic constant, its type arguments substituted); that is not part of
//! this checkpoint. Memory-backed and vector values likewise wait for the
//! static-data checkpoint, so they are reported rather than approximated.

use super::{Body, ExprIdx, FunctionState, Lowerer, mir};
use crate::diagnostics::TextSpan;
use crate::tir::defs::ConstIdx;
use crate::tir::eval::{ConstScalar, Val};
use crate::tir::types::TypeList;
use crate::vfs::FileId;

impl Lowerer<'_, '_, '_, '_> {
	pub(super) fn lower_constant(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		constant: ConstIdx,
		type_args: TypeList,
		ty: mir::ValueType,
	) -> Result<mir::Expression, ()> {
		if !type_args.is_empty() {
			self.unsupported(
				state.file_id,
				body.span(expr),
				"an associated or generic constant (dispatch is not implemented)",
			)?;
			unreachable!()
		}
		let span = body.span(expr);
		let file_id = state.file_id;
		// Copy the flat value out before lowering: building its nodes needs
		// the context mutably, and the evaluator's slice borrows it.
		let scalars = match self.context.const_value(constant) {
			Ok(value) => value.to_vec(),
			Err(_) => {
				self.unsupported(
					file_id,
					span,
					"a constant with no evaluated value",
				)?;
				unreachable!()
			}
		};
		self.materialize_constant(file_id, span, ty, &scalars)
	}

	/// Write a constant's flat scalars as the MIR value of `ty`, which is the
	/// checked type of the expression or pattern naming it.
	pub(super) fn materialize_constant(
		&mut self,
		file_id: FileId,
		span: TextSpan,
		ty: mir::ValueType,
		scalars: &[ConstScalar],
	) -> Result<mir::Expression, ()> {
		match ty {
			mir::ValueType::Unit => {
				if !scalars.is_empty() {
					return self.reject_constant_shape(file_id, span);
				}
				Ok(mir::Expression {
					kind: mir::ExprKind::Noop,
					ty,
				})
			}
			mir::ValueType::Bool => {
				let [scalar] = scalars else {
					return self.reject_constant_shape(file_id, span);
				};
				let value = match scalar.val {
					Val::I32(bits) => bits != 0,
					_ => return self.reject_constant_shape(file_id, span),
				};
				Ok(mir::Expression::boolean(value))
			}
			mir::ValueType::Aggregate { aggregate_index } => {
				let leaves =
					self.aggregates.get(aggregate_index).scalars.clone();
				if leaves.len() != scalars.len() {
					return self.reject_constant_shape(file_id, span);
				}
				let mut values = Vec::with_capacity(scalars.len());
				for (&leaf, scalar) in leaves.iter().zip(scalars) {
					values.push(
						self.constant_scalar(file_id, span, leaf, *scalar)?,
					);
				}
				Ok(mir::Expression {
					kind: mir::ExprKind::Aggregate {
						values: values.into_boxed_slice(),
					},
					ty,
				})
			}
			leaf => {
				let [scalar] = scalars else {
					return self.reject_constant_shape(file_id, span);
				};
				self.constant_scalar(file_id, span, leaf, *scalar)
			}
		}
	}

	/// One flat leaf of a constant, as the scalar instruction its target
	/// type holds.
	pub(super) fn constant_scalar(
		&mut self,
		file_id: FileId,
		span: TextSpan,
		ty: mir::ValueType,
		scalar: ConstScalar,
	) -> Result<mir::Expression, ()> {
		let kind = match (ty, scalar.val) {
			(mir::ValueType::Bool, Val::I32(bits)) => mir::ExprKind::Int {
				value: if bits != 0 { 1 } else { 0 },
			},
			(
				mir::ValueType::U8
				| mir::ValueType::I8
				| mir::ValueType::U16
				| mir::ValueType::I16
				| mir::ValueType::U32
				| mir::ValueType::I32,
				Val::I32(bits),
			) => mir::ExprKind::Int {
				value: i64::from(bits),
			},
			(mir::ValueType::U64 | mir::ValueType::I64, Val::I64(bits)) => {
				mir::ExprKind::Int { value: bits as i64 }
			}
			(mir::ValueType::F32, Val::F32(bits)) => mir::ExprKind::Float {
				value: f32::from_bits(bits) as f64,
			},
			(mir::ValueType::F64, Val::F64(bits)) => mir::ExprKind::Float {
				value: f64::from_bits(bits),
			},
			_ => {
				self.unsupported(
					file_id,
					span,
					"a constant of a memory-backed, function or vector type",
				)?;
				unreachable!()
			}
		};
		Ok(mir::Expression { kind, ty })
	}

	fn reject_constant_shape(
		&mut self,
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::Expression, ()> {
		self.unsupported(
			file_id,
			span,
			"a constant whose value does not match its checked type",
		)?;
		unreachable!()
	}
}
