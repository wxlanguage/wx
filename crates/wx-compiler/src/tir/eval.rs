//! Constant evaluation: folds a constant's checked `Body` into a value.
//!
//! The evaluator handles literals, builtin operators over them, references to
//! other constants and the construction of structs, and nothing else: whatever
//! else a body holds (a call, a form the checker does not cover yet) is not a
//! constant. Arithmetic follows the operand type exactly, and a result outside
//! it is an error, not a wrapped value.
//!
//! A constant's value is a memoized query (`const_value`), and evaluation asks
//! it on demand: a constant is read when the node naming it is evaluated, so a
//! branch that is not taken reads nothing. Like an impl member's value
//! (`Verdict`), a constant owns the failures of its own evaluation: the body
//! phase reports them, and a constant that reads a failed one fails silently. A
//! loop through constants is owned by its first-defined member, so it is
//! reported once whichever constant is asked first.

use codespan_reporting::diagnostic::Diagnostic;

use super::body::{ExprIdx, ExprKind};
use super::defs::{ConstIdx, EnumIdx, StructIdx};
use super::operators::Scalar;
use super::signatures::TypeContext;
use super::types::{Type, TypeEnvIdx, TypeIndex};
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};

/// A constant's value. Integers are held exactly, in the range of their type.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ConstValue {
	Int {
		value: i128,
		scalar: Scalar,
	},
	Float {
		value: f64,
		scalar: Scalar,
	},
	Bool(bool),
	Char(char),
	/// A struct's field values, in declaration order.
	Struct(Box<[ConstValue]>),
}

/// Why evaluating a body failed, at the node that failed.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct EvalError {
	pub(super) span: TextSpan,
	pub(super) kind: EvalErrorKind,
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum EvalErrorKind {
	/// The node is not a constant expression.
	NotConst,
	/// The result does not fit the operand type, or a shift amount is outside
	/// its width.
	Overflow(Operation),
	DivisionByZero,
	RemainderByZero,
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Operation {
	Binary(BinaryOp),
	Negate,
}

/// The value query's state for one constant.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ConstValueState {
	Unevaluated,
	/// Being evaluated; asking for it again closes a loop.
	InProgress,
	Evaluated(ConstValue),
	/// Not evaluated at all: the evaluator holds no values of its type
	/// (`check_value_type`), or it has no initializer. A constant that reads
	/// it is not a constant expression.
	NoValue,
	/// No value, and the failure is reported elsewhere: it derives from
	/// another constant's failure or from an error in its signature.
	Poisoned,
	/// No value; this constant owns the error and its check reports it.
	Failed(EvalError),
	/// No value; this constant owns the loop (its first member) and its check
	/// reports it.
	Cyclic(Box<[ConstIdx]>),
}

impl ConstValueState {
	/// What a reader of the constant learns, once the state is final.
	fn answer(&self) -> Option<Result<ConstValue, Unevaluable>> {
		match self {
			Self::Unevaluated | Self::InProgress => None,
			Self::Evaluated(value) => Some(Ok(value.clone())),
			Self::NoValue => Some(Err(Unevaluable::NoValue)),
			Self::Poisoned | Self::Failed(_) | Self::Cyclic(_) => {
				Some(Err(Unevaluable::Silent))
			}
		}
	}
}

/// Why `const_value` has no value for its caller.
enum Unevaluable {
	/// The constant has no compile-time value; reading it is the reader's
	/// error.
	NoValue,
	/// Reported, or to be reported, by whoever owns it; the caller is silent.
	Silent,
	/// A loop still unwinding towards its owner.
	Cycle(Box<[ConstIdx]>),
}

/// Why evaluating a node gave no value.
enum Halt {
	/// The constant being evaluated fails here; it owns the failure.
	Own(EvalError),
	/// Reported, or to be reported, by whoever owns it.
	Silent,
	/// A loop still unwinding towards its owner.
	Cycle(Box<[ConstIdx]>),
}

impl TypeContext<'_, '_, '_> {
	/// Evaluates a constant in the body phase, and reports what it owns.
	pub(super) fn evaluate_constant(&mut self, const_index: ConstIdx) {
		let _ = self.const_value(const_index);
		let diagnostic = match &self.const_values[usize::from(const_index)] {
			ConstValueState::Failed(error) => {
				self.report_eval_failure(const_index, error)
			}
			ConstValueState::Cyclic(cycle) => {
				self.report_const_cycle(const_index, cycle)
			}
			_ => return,
		};
		self.diagnostics.push(diagnostic);
	}

	/// The memoized value of a constant.
	fn const_value(
		&mut self,
		const_index: ConstIdx,
	) -> Result<ConstValue, Unevaluable> {
		let state = &self.const_values[usize::from(const_index)];
		if let Some(answer) = state.answer() {
			return answer;
		}
		if matches!(state, ConstValueState::InProgress) {
			return Err(Unevaluable::Cycle(self.const_cycle(const_index)));
		}
		let ty = match self.constant_value_type(const_index) {
			Ok(ty) => ty,
			Err(state) => return self.settle_constant(const_index, state),
		};
		self.ensure_const_body(const_index);
		let Some(body) = &self.const_bodies[usize::from(const_index)] else {
			return self.settle_constant(const_index, ConstValueState::NoValue);
		};
		let root = body.root();
		self.const_values[usize::from(const_index)] =
			ConstValueState::InProgress;
		self.const_stack.push(const_index);
		let evaluated = self.eval(const_index, root);
		self.const_stack.pop();

		let state = match evaluated {
			Ok(value) if value.scalar() == Scalar::from_type(ty) => {
				ConstValueState::Evaluated(value)
			}
			// A root of another type is `ERROR` once the checker reports it, so
			// this is a value the checker accepted in another scalar.
			Ok(_) => ConstValueState::Poisoned,
			Err(Halt::Own(error)) => ConstValueState::Failed(error),
			Err(Halt::Silent) => ConstValueState::Poisoned,
			// The owner keeps the loop; its readers further out derive from it.
			Err(Halt::Cycle(cycle)) if cycle[0] == const_index => {
				ConstValueState::Cyclic(cycle)
			}
			// Still unwinding: the one answer that is not a function of the
			// state, since the loop it carries belongs to another constant.
			Err(Halt::Cycle(cycle)) => {
				self.const_values[usize::from(const_index)] =
					ConstValueState::Poisoned;
				return Err(Unevaluable::Cycle(cycle));
			}
		};
		self.settle_constant(const_index, state)
	}

	/// Records the final state of a constant and answers its reader with it.
	fn settle_constant(
		&mut self,
		const_index: ConstIdx,
		state: ConstValueState,
	) -> Result<ConstValue, Unevaluable> {
		let answer = state.answer().expect("a settled state is final");
		self.const_values[usize::from(const_index)] = state;
		answer
	}

	/// Folds one node of `owner`'s body. Each step reads the node by index, so
	/// no borrow of the body is held while a constant it names is evaluated.
	fn eval(
		&mut self,
		owner: ConstIdx,
		expr: ExprIdx,
	) -> Result<ConstValue, Halt> {
		let body = self.const_bodies[usize::from(owner)].as_ref().unwrap();
		let (kind, ty, span) =
			(body.kind(expr), body.ty(expr), body.span(expr));
		if ty == TypeIndex::ERROR && !matches!(kind, ExprKind::Unsupported) {
			return Err(Halt::Silent);
		}
		let own = |kind| Halt::Own(EvalError { span, kind });
		match kind {
			ExprKind::Error => Err(Halt::Silent),
			ExprKind::Unsupported
			| ExprKind::MethodCall { .. }
			| ExprKind::GenericMethodCall { .. } => Err(own(EvalErrorKind::NotConst)),
			ExprKind::Int(value) => match Scalar::from_type(ty) {
				Some(scalar) => Ok(ConstValue::Int {
					value: i128::from(value),
					scalar,
				}),
				None => Err(own(EvalErrorKind::NotConst)),
			},
			ExprKind::Float(value) => match Scalar::from_type(ty) {
				Some(scalar) => Ok(ConstValue::Float { value, scalar }),
				None => Err(own(EvalErrorKind::NotConst)),
			},
			ExprKind::Bool(value) => Ok(ConstValue::Bool(value)),
			ExprKind::Char(value) => Ok(ConstValue::Char(value)),
			ExprKind::Const(const_index) => {
				self.read_constant(const_index, span)
			}
			ExprKind::NextDiscriminant(previous) => {
				let ConstValue::Int { value, scalar } =
					self.read_constant(previous, span)?
				else {
					unreachable!("a variant's value is an integer")
				};
				int(value + 1, scalar, Operation::Binary(BinaryOp::Add))
					.map_err(own)
			}
			ExprKind::Unary { op, operand } => {
				let operand = self.eval(owner, operand)?;
				unary(op, operand).map_err(own)
			}
			ExprKind::Construct {
				struct_index,
				args,
				order,
			} => {
				let body =
					self.const_bodies[usize::from(owner)].as_ref().unwrap();
				let fields: Vec<_> = (0..args.len())
					.map(|at| {
						(body.args(args)[at], body.declared_index(order, at))
					})
					.collect();
				let count = self.struct_field_types(struct_index).len();
				// A missing field was reported.
				if fields.len() != count {
					return Err(Halt::Silent);
				}
				// Evaluated in written order, held in declaration order.
				let mut values = vec![None; count];
				for (expr, field) in fields {
					values[usize::from(field)] = Some(self.eval(owner, expr)?);
				}
				Ok(ConstValue::Struct(
					values.into_iter().map(Option::unwrap).collect(),
				))
			}
			ExprKind::Binary { op, lhs, rhs } => {
				let lhs = self.eval(owner, lhs)?;
				// `&&` and `||` do not evaluate a right side they do not need.
				match (op, &lhs) {
					(BinaryOp::And, ConstValue::Bool(false)) => {
						return Ok(ConstValue::Bool(false));
					}
					(BinaryOp::Or, ConstValue::Bool(true)) => {
						return Ok(ConstValue::Bool(true));
					}
					_ => {}
				}
				let rhs = self.eval(owner, rhs)?;
				binary(op, lhs, rhs).map_err(own)
			}
		}
	}

	/// The value of a constant a node names. One with no compile-time value
	/// (its type is not a scalar) makes the naming node not a constant
	/// expression.
	fn read_constant(
		&mut self,
		const_index: ConstIdx,
		span: TextSpan,
	) -> Result<ConstValue, Halt> {
		self.const_value(const_index)
			.map_err(|failure| match failure {
				Unevaluable::NoValue => Halt::Own(EvalError {
					span,
					kind: EvalErrorKind::NotConst,
				}),
				Unevaluable::Silent => Halt::Silent,
				Unevaluable::Cycle(cycle) => Halt::Cycle(cycle),
			})
	}

	/// `const_index` was asked for again while it is evaluated: the loop is
	/// the stack from its first request, read from its first-defined member:
	/// each member requires the next, and the last requires the first.
	fn const_cycle(&self, const_index: ConstIdx) -> Box<[ConstIdx]> {
		let start = self
			.const_stack
			.iter()
			.position(|&member| member == const_index)
			.expect("an in-progress constant is on the stack");
		let mut members = self.const_stack[start..].to_vec();
		let owner = (0..members.len())
			.min_by_key(|&at| usize::from(members[at]))
			.unwrap();
		members.rotate_left(owner);
		members.into_boxed_slice()
	}

	/// The type a constant's value is held in: its declared type, normalized,
	/// or for a value of an enum, the enum's repr. `Err` is the final state of
	/// a constant of a type the evaluator holds no values of.
	fn constant_value_type(
		&mut self,
		const_index: ConstIdx,
	) -> Result<TypeIndex, ConstValueState> {
		let (ty, scope) = self.constant_type(const_index);
		let mut ty = self.normalize_type_query(scope, ty).unwrap_or(ty);
		if let Type::Enum { enum_index } = *self.types.resolve(ty) {
			ty = self.enum_repr(enum_index);
		}
		self.check_value_type(ty, &mut Vec::new())?;
		Ok(ty)
	}

	/// Whether the evaluator holds values of the normalized type `ty`: a
	/// scalar, an enum (in its repr), or a struct that is not generic and
	/// whose fields it holds. `Err` is the final state of a constant of a
	/// type it does not: no value, or poisoned when the type, or a field's,
	/// failed to resolve, which was reported where it is written. A struct
	/// reached again through `visiting`, the structs being looked through,
	/// contains itself, which is reported on the struct.
	fn check_value_type(
		&mut self,
		ty: TypeIndex,
		visiting: &mut Vec<StructIdx>,
	) -> Result<(), ConstValueState> {
		if ty == TypeIndex::ERROR {
			return Err(ConstValueState::Poisoned);
		}
		if Scalar::from_type(ty).is_some() {
			return Ok(());
		}
		match *self.types.resolve(ty) {
			Type::Enum { enum_index } => {
				if self.enum_repr(enum_index) == TypeIndex::ERROR {
					Err(ConstValueState::Poisoned)
				} else {
					Ok(())
				}
			}
			Type::Struct { struct_index, .. } => {
				if visiting.contains(&struct_index) {
					return Err(ConstValueState::Poisoned);
				}
				if self.structs[usize::from(struct_index)].type_params
					!= TypeEnvIdx::ROOT
				{
					return Err(ConstValueState::NoValue);
				}
				visiting.push(struct_index);
				let mut held = Ok(());
				for field in self.struct_field_types(struct_index).to_vec() {
					let field = self
						.normalize_type_query(TypeEnvIdx::ROOT, field)
						.unwrap_or(field);
					match self.check_value_type(field, visiting) {
						Ok(()) => {}
						// A poisoned field poisons the struct, whatever the other
						// fields are, so a reader of it is never reported.
						Err(ConstValueState::Poisoned) => {
							held = Err(ConstValueState::Poisoned);
							break;
						}
						Err(state) => held = Err(state),
					}
				}
				visiting.pop();
				held
			}
			_ => Err(ConstValueState::NoValue),
		}
	}

	/// Reports each set of an enum's variants that share a value, once, on the
	/// enum. A variant without a value reports itself and is left out.
	pub(super) fn check_discriminants(&mut self, enum_index: EnumIdx) {
		let enum_def = &self.defs.enums[usize::from(enum_index)];
		let (file_id, name_span) = (enum_def.file_id, enum_def.name.span);
		let run = enum_def.variants.clone();
		let mut values = Vec::new();
		for variant in u32::from(run.start)..u32::from(run.end) {
			let variant = ConstIdx::new(variant);
			if let Ok(ConstValue::Int { value, .. }) = self.const_value(variant)
			{
				values.push((value, variant));
			}
		}
		// Stable, so each set keeps source order; the sets are then reported in
		// the source order of their first variant.
		values.sort_by_key(|&(value, _)| value);
		let mut groups: Vec<&[(i128, ConstIdx)]> = values
			.chunk_by(|a, b| a.0 == b.0)
			.filter(|group| group.len() > 1)
			.collect();
		groups.sort_unstable_by_key(|group| usize::from(group[0].1));
		for group in groups {
			let value = group[0].0;
			let mut diagnostic = Diagnostic::error()
				.with_code(DiagnosticCode::EnumDuplicateValue.code())
				.with_message(format!(
					"multiple variants of this enum have the same value \
					 `{value}`"
				))
				.with_label(
					SourceSpan::new(file_id, name_span).primary_label(),
				);
			for &(_, variant) in group {
				// The written value, or the name of a variant counted on.
				let body =
					self.const_bodies[usize::from(variant)].as_ref().unwrap();
				let span = body.span(body.root());
				diagnostic = diagnostic.with_label(
					SourceSpan::new(file_id, span)
						.secondary_label()
						.with_message(format!("value `{value}` assigned here")),
				);
			}
			self.diagnostics.push(diagnostic);
		}
	}

	fn const_name(&self, index: ConstIdx) -> &str {
		let def = &self.defs.constants[usize::from(index)];
		self.strings.resolve(def.name.inner).unwrap()
	}

	fn report_eval_failure(
		&self,
		const_index: ConstIdx,
		error: &EvalError,
	) -> Diagnostic<crate::vfs::FileId> {
		let def = &self.defs.constants[usize::from(const_index)];
		let site = SourceSpan::new(def.file_id, error.span);
		let message = match error.kind {
			EvalErrorKind::NotConst => format!(
				"`{}` cannot be evaluated at compile time",
				self.const_name(const_index)
			),
			_ => format!(
				"evaluation of constant `{}` failed",
				self.const_name(const_index)
			),
		};
		Diagnostic::error()
			.with_code(error.kind.code().code())
			.with_message(message)
			.with_label(site.primary_label().with_message(error.kind.label()))
	}

	fn report_const_cycle(
		&self,
		const_index: ConstIdx,
		cycle: &[ConstIdx],
	) -> Diagnostic<crate::vfs::FileId> {
		let def = &self.defs.constants[usize::from(const_index)];
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::CyclicConstant.code())
			.with_message(format!(
				"cycle detected when evaluating constant `{}`",
				self.const_name(cycle[0])
			))
			.with_label(
				SourceSpan::new(def.file_id, def.name.span).primary_label(),
			);
		for (at, &member) in cycle.iter().enumerate() {
			let next = cycle[(at + 1) % cycle.len()];
			let member_def = &self.defs.constants[usize::from(member)];
			diagnostic = diagnostic.with_label(
				SourceSpan::new(member_def.file_id, member_def.name.span)
					.secondary_label()
					.with_message(format!(
						"`{}` requires evaluating `{}`",
						self.const_name(member),
						self.const_name(next)
					)),
			);
		}
		diagnostic
	}
}

impl EvalErrorKind {
	fn code(self) -> DiagnosticCode {
		match self {
			Self::NotConst => DiagnosticCode::NotConstEvaluatable,
			_ => DiagnosticCode::ConstEvaluationFailed,
		}
	}

	fn label(self) -> String {
		match self {
			Self::NotConst => "not a constant expression".to_string(),
			Self::Overflow(operation) => {
				format!("attempt to {} with overflow", operation.verb())
			}
			Self::DivisionByZero => "attempt to divide by zero".to_string(),
			Self::RemainderByZero => {
				"attempt to calculate the remainder with a divisor of zero"
					.to_string()
			}
		}
	}
}

impl ConstValue {
	/// The scalar the value is held in; `None` for a struct.
	fn scalar(&self) -> Option<Scalar> {
		match *self {
			Self::Int { scalar, .. } | Self::Float { scalar, .. } => {
				Some(scalar)
			}
			Self::Bool(_) => Some(Scalar::Bool),
			Self::Char(_) => Some(Scalar::Char),
			Self::Struct(_) => None,
		}
	}
}

impl Operation {
	fn verb(self) -> &'static str {
		match self {
			Self::Negate => "negate",
			Self::Binary(BinaryOp::Add) => "add",
			Self::Binary(BinaryOp::Sub) => "subtract",
			Self::Binary(BinaryOp::Mul) => "multiply",
			Self::Binary(BinaryOp::Div) => "divide",
			Self::Binary(BinaryOp::Rem) => "calculate the remainder",
			Self::Binary(BinaryOp::LeftShift) => "shift left",
			Self::Binary(BinaryOp::RightShift) => "shift right",
			Self::Binary(_) => "evaluate",
		}
	}
}

fn unary(
	op: UnaryOp,
	operand: ConstValue,
) -> Result<ConstValue, EvalErrorKind> {
	Ok(match (op, operand) {
		(UnaryOp::InvertSign, ConstValue::Int { value, scalar }) => {
			int(-value, scalar, Operation::Negate)?
		}
		(UnaryOp::InvertSign, ConstValue::Float { value, scalar }) => {
			ConstValue::Float {
				value: -value,
				scalar,
			}
		}
		(UnaryOp::BitNot, ConstValue::Int { value, scalar }) => {
			ConstValue::Int {
				value: from_bits(!to_bits(value, scalar), scalar),
				scalar,
			}
		}
		(UnaryOp::Not, ConstValue::Bool(value)) => ConstValue::Bool(!value),
		_ => unreachable!(
			"the checker builds builtin operators on their scalars"
		),
	})
}

fn binary(
	op: BinaryOp,
	lhs: ConstValue,
	rhs: ConstValue,
) -> Result<ConstValue, EvalErrorKind> {
	use ConstValue::{Bool, Float, Int};
	if let Some(ordering) = compare(op, &lhs, &rhs) {
		return Ok(Bool(ordering));
	}
	Ok(match (lhs, rhs) {
		(Int { value: a, scalar }, Int { value: b, .. }) => {
			let overflow = Operation::Binary(op);
			match op {
				BinaryOp::Add => int(a + b, scalar, overflow)?,
				BinaryOp::Sub => int(a - b, scalar, overflow)?,
				BinaryOp::Mul => int(a * b, scalar, overflow)?,
				BinaryOp::Div if b == 0 => {
					return Err(EvalErrorKind::DivisionByZero);
				}
				// Truncating, as wasm's `div_s`; `MIN / -1` overflows.
				BinaryOp::Div => int(a / b, scalar, overflow)?,
				BinaryOp::Rem if b == 0 => {
					return Err(EvalErrorKind::RemainderByZero);
				}
				// The sign of the dividend, as wasm's `rem_s`.
				BinaryOp::Rem => int(a % b, scalar, overflow)?,
				BinaryOp::BitAnd => Int {
					value: a & b,
					scalar,
				},
				BinaryOp::BitOr => Int {
					value: a | b,
					scalar,
				},
				BinaryOp::BitXor => Int {
					value: a ^ b,
					scalar,
				},
				BinaryOp::LeftShift | BinaryOp::RightShift => {
					if b < 0 || b >= i128::from(scalar.bits()) {
						return Err(EvalErrorKind::Overflow(overflow));
					}
					// Bits shifted past the width are dropped, as at runtime;
					// a right shift is arithmetic on a signed type.
					let value = if op == BinaryOp::LeftShift {
						from_bits(to_bits(a, scalar) << b, scalar)
					} else {
						a >> b
					};
					Int { value, scalar }
				}
				_ => unreachable!(
					"the checker builds builtin operators on their scalars"
				),
			}
		}
		(Float { value: a, scalar }, Float { value: b, .. }) => {
			let value = match op {
				BinaryOp::Add => a + b,
				BinaryOp::Sub => a - b,
				BinaryOp::Mul => a * b,
				BinaryOp::Div => a / b,
				BinaryOp::Rem => a % b,
				_ => unreachable!(),
			};
			// An `f32` operation rounds the exact result once. A double holds
			// the result of `+ - * /` on two `f32`s closely enough that rounding
			// it to `f32` agrees, and `%` is exact in both.
			let value = if scalar == Scalar::F32 {
				f64::from(value as f32)
			} else {
				value
			};
			Float { value, scalar }
		}
		(Bool(a), Bool(b)) => Bool(match op {
			BinaryOp::BitAnd | BinaryOp::And => a & b,
			BinaryOp::BitOr | BinaryOp::Or => a | b,
			BinaryOp::BitXor => a ^ b,
			_ => unreachable!(),
		}),
		_ => unreachable!(
			"the checker builds builtin operators on their scalars"
		),
	})
}

/// The answer of a comparison, `None` for any other operator.
fn compare(op: BinaryOp, lhs: &ConstValue, rhs: &ConstValue) -> Option<bool> {
	use std::cmp::Ordering;
	let ordering = match (lhs, rhs) {
		(
			ConstValue::Int { value: a, .. },
			ConstValue::Int { value: b, .. },
		) => a.partial_cmp(b),
		// IEEE: any comparison with NaN is false, except `!=`.
		(
			ConstValue::Float { value: a, .. },
			ConstValue::Float { value: b, .. },
		) => a.partial_cmp(b),
		(ConstValue::Bool(a), ConstValue::Bool(b)) => a.partial_cmp(b),
		(ConstValue::Char(a), ConstValue::Char(b)) => a.partial_cmp(b),
		_ => None,
	};
	Some(match op {
		BinaryOp::Eq => ordering == Some(Ordering::Equal),
		BinaryOp::NotEq => ordering != Some(Ordering::Equal),
		BinaryOp::Less => ordering == Some(Ordering::Less),
		BinaryOp::LessEq => {
			matches!(ordering, Some(Ordering::Less | Ordering::Equal))
		}
		BinaryOp::Greater => ordering == Some(Ordering::Greater),
		BinaryOp::GreaterEq => {
			matches!(ordering, Some(Ordering::Greater | Ordering::Equal))
		}
		_ => return None,
	})
}

/// `value` if it is in `scalar`'s range, an overflow of `operation` otherwise.
fn int(
	value: i128,
	scalar: Scalar,
	operation: Operation,
) -> Result<ConstValue, EvalErrorKind> {
	let bits = scalar.bits();
	let (min, max) = if scalar.is_signed() {
		(-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
	} else {
		(0, (1i128 << bits) - 1)
	};
	if value < min || value > max {
		return Err(EvalErrorKind::Overflow(operation));
	}
	Ok(ConstValue::Int { value, scalar })
}

/// The two's-complement bit pattern of an in-range value, at `scalar`'s width.
fn to_bits(value: i128, scalar: Scalar) -> u128 {
	(value as u128) & ((1u128 << scalar.bits()) - 1)
}

/// The value a bit pattern means at `scalar`'s width and signedness.
fn from_bits(bits: u128, scalar: Scalar) -> i128 {
	let width = scalar.bits();
	let bits = bits & ((1u128 << width) - 1);
	if scalar.is_signed() && bits >> (width - 1) == 1 {
		bits as i128 - (1i128 << width)
	} else {
		bits as i128
	}
}
