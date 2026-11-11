//! Concrete constant values: a `True`/`False` variant, an enum variant, or a
//! free `const`, read from the checker's memoized evaluation and written as
//! the MIR node its flat value calls for.
//!
//! A constant with arguments is read per instance: its arguments are made
//! concrete with the function instance's, and a trait's declaration reads
//! what the impl its `Self` selects provides (`resolve_constant`). An address
//! into evaluated data is a pointer to its static entry (`statics.rs`); a
//! vector value is reported rather than approximated.

use super::{Body, ExprIdx, FunctionState, Lowerer, mir};
use crate::diagnostics::{SourceSpan, TextSpan};
use crate::tir::decls::ConstIdx;
use crate::tir::eval::{ConstScalar, ResolvedConstant, Unevaluable, Val};
use crate::tir::types::{GenericArgs, Type, TypeIndex};
use crate::vfs::FileId;

impl Lowerer<'_> {
	pub(super) fn lower_constant(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		constant: ConstIdx,
		type_args: GenericArgs,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let span = body.span(expr);
		let file_id = state.file_id;
		let written: Vec<TypeIndex> =
			self.sema.generic_args.types(type_args).to_vec();
		let args = written
			.into_iter()
			.map(|arg| {
				let arg = self.substitute(arg, state.env, &state.args);
				self.normalize_type(arg, file_id, span)
			})
			.collect::<Result<Vec<TypeIndex>, ()>>()?;
		let instance =
			match self.sema.resolve_constant(self.strings, constant, &args) {
				Ok(ResolvedConstant::Instance(instance)) => instance,
				Ok(ResolvedConstant::Length(length)) => {
					let length = self.normalize_type(length, file_id, span)?;
					let Type::Value { bits } = *self.sema.types.resolve(length)
					else {
						unreachable!("a concrete array's length is a value")
					};
					return Ok(state
						.push(mir::ExprKind::Int { value: bits as i64 }, ty));
				}
				Ok(ResolvedConstant::DataEnd(memory)) => {
					let memory = self.memory(memory);
					return Ok(
						state.push(mir::ExprKind::DataEnd { memory }, ty)
					);
				}
				Ok(ResolvedConstant::Abstract) => {
					unreachable!("an instance's arguments are concrete")
				}
				// The checker proved the bound, so only a reported failure
				// reaches here.
				Err(_) => return Err(()),
			};
		// Copy the flat value out before lowering: building its nodes needs
		// `sema` mutably, and the evaluator's slice borrows it.
		let used_at = SourceSpan::new(file_id, span);
		let scalars = match self.sema.instance_value(
			self.strings,
			instance,
			Some(used_at),
		) {
			Ok(value) => value.to_vec(),
			Err(Unevaluable::NoValue) => {
				self.unsupported(
					file_id,
					span,
					"a constant with no evaluated value",
				)?;
				unreachable!()
			}
			// Reported by the instance's first reader.
			Err(Unevaluable::Silent) => return Err(()),
		};
		self.materialize_constant(state, file_id, span, ty, &scalars)
	}

	/// Write a constant's flat scalars as the MIR value of `ty`, which is the
	/// checked type of the expression or pattern naming it.
	pub(super) fn materialize_constant(
		&mut self,
		state: &mut FunctionState,
		file_id: FileId,
		span: TextSpan,
		ty: mir::ValueType,
		scalars: &[ConstScalar],
	) -> Result<mir::ExprId, ()> {
		match ty {
			mir::ValueType::Unit => {
				if !scalars.is_empty() {
					return self.reject_constant_shape(file_id, span);
				}
				Ok(state.push(mir::ExprKind::Noop, ty))
			}
			mir::ValueType::Aggregate { .. } => {
				let leaves = self.signatures.scalars(&ty).to_vec();
				if leaves.len() != scalars.len() {
					return self.reject_constant_shape(file_id, span);
				}
				let mut values = Vec::with_capacity(scalars.len());
				for (&leaf, scalar) in leaves.iter().zip(scalars) {
					values.push(self.constant_scalar(
						state, file_id, span, leaf, *scalar,
					)?);
				}
				let values = state.list(values);
				Ok(state.push(mir::ExprKind::Values { values }, ty))
			}
			leaf => {
				let [scalar] = scalars else {
					return self.reject_constant_shape(file_id, span);
				};
				self.constant_scalar(state, file_id, span, leaf, *scalar)
			}
		}
	}

	/// One flat leaf of a constant, as the scalar instruction its target
	/// type holds.
	pub(super) fn constant_scalar(
		&mut self,
		state: &mut FunctionState,
		file_id: FileId,
		span: TextSpan,
		ty: mir::ValueType,
		scalar: ConstScalar,
	) -> Result<mir::ExprId, ()> {
		// A constant is its bits: a `Bool` holding 5 (by `transmute`) is 5,
		// as it would be at run time.
		let kind = match (ty, scalar.val) {
			(mir::ValueType::I32, Val::I32(bits)) => mir::ExprKind::Int {
				value: i64::from(bits),
			},
			(mir::ValueType::I64, Val::I64(bits)) => {
				mir::ExprKind::Int { value: bits as i64 }
			}
			(mir::ValueType::F32, Val::F32(bits)) => mir::ExprKind::Float {
				value: f32::from_bits(bits) as f64,
			},
			(mir::ValueType::F64, Val::F64(bits)) => mir::ExprKind::Float {
				value: f64::from_bits(bits),
			},
			(
				mir::ValueType::I32 | mir::ValueType::I64,
				Val::DataEnd { memory },
			) => mir::ExprKind::DataEnd {
				memory: self.memory(memory),
			},
			(
				mir::ValueType::I32 | mir::ValueType::I64,
				Val::MemoryOffset { alloc, offset },
			) => mir::ExprKind::StaticPointer {
				entry: self.static_entry(alloc),
				offset: u32::try_from(offset).unwrap(),
			},
			_ => {
				self.unsupported(
					file_id,
					span,
					"a constant of a function or vector type",
				)?;
				unreachable!()
			}
		};
		Ok(state.push(kind, ty))
	}

	fn reject_constant_shape(
		&mut self,
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::ExprId, ()> {
		self.unsupported(
			file_id,
			span,
			"a constant whose value does not match its checked type",
		)?;
		unreachable!()
	}
}
