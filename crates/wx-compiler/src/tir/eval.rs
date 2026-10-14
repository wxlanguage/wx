//! Constant evaluation: folds a constant's checked `Body` into a value.
//!
//! The evaluator handles literals, builtin operators over them and references
//! to other constants, and nothing else: whatever else a body holds (a call, a
//! form the checker does not cover yet) is not a constant. Arithmetic follows
//! the operand type exactly, and a result outside it is an error, not a wrapped
//! value.
//!
//! A constant's value is a memoized query (`const_value`). Like an impl
//! member's value (`AssocValue`), a constant owns the failures of its own
//! evaluation: its check reports them, and a constant that reads a failed one
//! fails silently. A loop through constants is owned by its first-defined
//! member, so it is reported once whichever constant is asked first.

use codespan_reporting::diagnostic::Diagnostic;

use super::body::{Body, ExprIdx, ExprKind};
use super::defs::ConstIdx;
use super::operators::Scalar;
use super::signatures::TypeContext;
use super::types::TypeIndex;
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};

/// A constant's value. Integers are held exactly, in the range of their type.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ConstValue {
	Int { value: i128, scalar: Scalar },
	Float { value: f64, scalar: Scalar },
	Bool(bool),
	Char(char),
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
	/// The result does not fit the operand type.
	Overflow(Operation),
	DivisionByZero,
	RemainderByZero,
	/// A shift amount outside the operand's width.
	ShiftOverflow(BinaryOp),
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Operation {
	Binary(BinaryOp),
	Negate,
}

/// A loop through constants, read from its owner: each member requires the
/// next, and the last requires the first.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct ConstCycle {
	pub(super) members: Box<[ConstIdx]>,
}

/// A failure this constant owns and its check reports.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum OwnedFailure {
	Eval(EvalError),
	Cycle(ConstCycle),
}

/// The value query's state for one constant.
#[derive(Clone, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ConstValueState {
	Unevaluated,
	/// Being evaluated; asking for it again closes a loop.
	InProgress,
	Evaluated(ConstValue),
	/// Not evaluated at all: its type is not a scalar, or it has no
	/// initializer. A constant that reads it is not a constant expression.
	NotEvaluated,
	/// No value. `Some` holds the failure this constant owns; `None` derives
	/// from one reported elsewhere.
	Failed(Option<OwnedFailure>),
}

/// Why `const_value` has no value for its caller.
enum Unevaluable {
	/// The constant has no compile-time value; reading it is the reader's
	/// error.
	NotEvaluated,
	/// Reported, or to be reported, by whoever owns it; the caller is silent.
	Silent,
	/// A loop still unwinding towards its owner.
	Cycle(ConstCycle),
}

impl TypeContext<'_, '_, '_> {
	/// Evaluates a constant once its check runs, and reports what it owns.
	pub(super) fn evaluate_constant(&mut self, const_index: ConstIdx) {
		let _ = self.const_value(const_index);
		let ConstValueState::Failed(Some(failure)) =
			&self.const_values[usize::from(const_index)]
		else {
			return;
		};
		let diagnostic =
			self.report_owned_failure(const_index, failure.clone());
		self.diagnostics.push(diagnostic);
	}

	/// The memoized value of a constant whose type is a scalar.
	fn const_value(
		&mut self,
		const_index: ConstIdx,
	) -> Result<ConstValue, Unevaluable> {
		match &self.const_values[usize::from(const_index)] {
			ConstValueState::Evaluated(value) => return Ok(*value),
			ConstValueState::NotEvaluated => {
				return Err(Unevaluable::NotEvaluated);
			}
			ConstValueState::Failed(_) => return Err(Unevaluable::Silent),
			ConstValueState::InProgress => {
				return Err(Unevaluable::Cycle(self.const_cycle(const_index)));
			}
			ConstValueState::Unevaluated => {}
		}
		let Some(scalar) = self.constant_scalar(const_index) else {
			self.const_values[usize::from(const_index)] =
				ConstValueState::NotEvaluated;
			return Err(Unevaluable::NotEvaluated);
		};
		self.ensure_const_body(const_index);
		// Every constant the body names is evaluated first, as a required
		// input, whether or not the branch naming it is taken.
		let referenced = match &self.const_bodies[usize::from(const_index)] {
			Some(body) => referenced_constants(body),
			None => {
				self.const_values[usize::from(const_index)] =
					ConstValueState::NotEvaluated;
				return Err(Unevaluable::NotEvaluated);
			}
		};
		self.const_values[usize::from(const_index)] =
			ConstValueState::InProgress;
		self.const_stack.push(const_index);
		let mut inputs = Vec::with_capacity(referenced.len());
		let mut outcome = Ok(());
		for referenced in referenced {
			match self.const_value(referenced) {
				Ok(value) => inputs.push((referenced, value)),
				// The node naming it is not a constant expression; evaluation
				// reports it there, if it gets that far.
				Err(Unevaluable::NotEvaluated) => {}
				Err(failure) => {
					outcome = Err(failure);
					break;
				}
			}
		}
		self.const_stack.pop();

		let (state, answer) = match outcome {
			Ok(()) => {
				let body = self.const_bodies[usize::from(const_index)]
					.as_ref()
					.unwrap();
				let evaluated = Evaluator {
					body,
					inputs: &inputs,
				}
				.eval(body.root());
				match evaluated {
					Ok(value) if value.scalar() == Some(scalar) => {
						(ConstValueState::Evaluated(value), Ok(value))
					}
					// The initializer has another type; the checker reported
					// the mismatch.
					Ok(_) => (
						ConstValueState::Failed(None),
						Err(Unevaluable::Silent),
					),
					Err(Some(error)) => (
						ConstValueState::Failed(Some(OwnedFailure::Eval(
							error,
						))),
						Err(Unevaluable::Silent),
					),
					Err(None) => (
						ConstValueState::Failed(None),
						Err(Unevaluable::Silent),
					),
				}
			}
			Err(Unevaluable::Silent) => {
				(ConstValueState::Failed(None), Err(Unevaluable::Silent))
			}
			Err(Unevaluable::NotEvaluated) => {
				unreachable!("an unevaluated input is skipped, not a failure")
			}
			// The owner keeps the loop; its readers further out derive from it.
			Err(Unevaluable::Cycle(cycle))
				if cycle.members[0] == const_index =>
			{
				(
					ConstValueState::Failed(Some(OwnedFailure::Cycle(cycle))),
					Err(Unevaluable::Silent),
				)
			}
			Err(cycle @ Unevaluable::Cycle(_)) => {
				(ConstValueState::Failed(None), Err(cycle))
			}
		};
		self.const_values[usize::from(const_index)] = state;
		answer
	}

	/// `const_index` was asked for again while it is evaluated: the loop is
	/// the stack from its first request, read from its first-defined member.
	fn const_cycle(&self, const_index: ConstIdx) -> ConstCycle {
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
		ConstCycle {
			members: members.into_boxed_slice(),
		}
	}

	/// The scalar a constant's declared type means, if it is one.
	fn constant_scalar(&mut self, const_index: ConstIdx) -> Option<Scalar> {
		let (ty, scope) = self.constant_type(const_index);
		let ty = self.normalize_type_query(scope, ty).unwrap_or(ty);
		Scalar::from_type(ty)
	}

	fn report_owned_failure(
		&self,
		const_index: ConstIdx,
		failure: OwnedFailure,
	) -> Diagnostic<crate::vfs::FileId> {
		let def = &self.defs.constants[usize::from(const_index)];
		let name = |index: ConstIdx| {
			let def = &self.defs.constants[usize::from(index)];
			self.strings.resolve(def.name.inner).unwrap()
		};
		match failure {
			OwnedFailure::Eval(error) => {
				let site = SourceSpan::new(def.file_id, error.span);
				let (code, label) = match error.kind {
					EvalErrorKind::NotConst => (
						DiagnosticCode::NotConstEvaluatable,
						"not a constant expression".to_string(),
					),
					EvalErrorKind::Overflow(operation) => (
						DiagnosticCode::ConstEvaluationFailed,
						format!("attempt to {} with overflow", operation.verb()),
					),
					EvalErrorKind::DivisionByZero => (
						DiagnosticCode::ConstEvaluationFailed,
						"attempt to divide by zero".to_string(),
					),
					EvalErrorKind::RemainderByZero => (
						DiagnosticCode::ConstEvaluationFailed,
						"attempt to calculate the remainder with a divisor of zero"
							.to_string(),
					),
					EvalErrorKind::ShiftOverflow(op) => (
						DiagnosticCode::ConstEvaluationFailed,
						format!(
							"attempt to {} with overflow",
							Operation::Binary(op).verb()
						),
					),
				};
				let message = match error.kind {
					EvalErrorKind::NotConst => format!(
						"`{}` cannot be evaluated at compile time",
						name(const_index)
					),
					_ => format!(
						"evaluation of constant `{}` failed",
						name(const_index)
					),
				};
				Diagnostic::error()
					.with_code(code.code())
					.with_message(message)
					.with_label(site.primary_label().with_message(label))
			}
			OwnedFailure::Cycle(cycle) => {
				let mut diagnostic = Diagnostic::error()
					.with_code(DiagnosticCode::CyclicConstant.code())
					.with_message(format!(
						"cycle detected when evaluating constant `{}`",
						name(cycle.members[0])
					))
					.with_label(
						SourceSpan::new(def.file_id, def.name.span)
							.primary_label(),
					);
				for (at, &member) in cycle.members.iter().enumerate() {
					let next = cycle.members[(at + 1) % cycle.members.len()];
					let member_def = &self.defs.constants[usize::from(member)];
					diagnostic = diagnostic.with_label(
						SourceSpan::new(
							member_def.file_id,
							member_def.name.span,
						)
						.secondary_label()
						.with_message(format!(
							"`{}` requires evaluating `{}`",
							name(member),
							name(next)
						)),
					);
				}
				diagnostic
			}
		}
	}
}

/// The distinct constants a body names, in order of first mention.
fn referenced_constants(body: &Body) -> Vec<ConstIdx> {
	let mut referenced = Vec::new();
	for index in 0..=usize::from(body.root()) {
		if let ExprKind::Const(const_index) =
			body.kind(ExprIdx::new(index as u32))
			&& !referenced.contains(&const_index)
		{
			referenced.push(const_index);
		}
	}
	referenced
}

/// Folds one body, given the values of the constants it names. `Err(None)`
/// is a failure already reported elsewhere (a node the checker marked as an
/// error); `Err(Some)` is this body's own.
struct Evaluator<'b> {
	body: &'b Body,
	inputs: &'b [(ConstIdx, ConstValue)],
}

impl Evaluator<'_> {
	fn eval(&self, expr: ExprIdx) -> Result<ConstValue, Option<EvalError>> {
		let ty = self.body.ty(expr);
		if ty == TypeIndex::ERROR
			&& !matches!(self.body.kind(expr), ExprKind::Unsupported)
		{
			return Err(None);
		}
		let fail = |kind| {
			Err(Some(EvalError {
				span: self.body.span(expr),
				kind,
			}))
		};
		match self.body.kind(expr) {
			ExprKind::Error => Err(None),
			ExprKind::Unsupported
			| ExprKind::MethodCall { .. }
			| ExprKind::GenericMethodCall { .. } => fail(EvalErrorKind::NotConst),
			ExprKind::Int(value) => match Scalar::from_type(ty) {
				Some(scalar) => Ok(ConstValue::Int {
					value: i128::from(value),
					scalar,
				}),
				None => fail(EvalErrorKind::NotConst),
			},
			ExprKind::Float(value) => match Scalar::from_type(ty) {
				Some(scalar) => Ok(ConstValue::Float { value, scalar }),
				None => fail(EvalErrorKind::NotConst),
			},
			ExprKind::Bool(value) => Ok(ConstValue::Bool(value)),
			ExprKind::Char(value) => Ok(ConstValue::Char(value)),
			// Every named constant was evaluated first; one without a value is
			// not a constant (its type is not a scalar).
			ExprKind::Const(const_index) => match self
				.inputs
				.iter()
				.find(|(input, _)| *input == const_index)
			{
				Some(&(_, value)) => Ok(value),
				None => fail(EvalErrorKind::NotConst),
			},
			ExprKind::Unary { op, operand } => {
				let operand = self.eval(operand)?;
				unary(op, operand).map_err(|kind| {
					Some(EvalError {
						span: self.body.span(expr),
						kind,
					})
				})
			}
			ExprKind::Binary { op, lhs, rhs } => {
				let lhs = self.eval(lhs)?;
				// `&&` and `||` do not evaluate a right side they do not need.
				match (op, lhs) {
					(BinaryOp::And, ConstValue::Bool(false)) => {
						return Ok(ConstValue::Bool(false));
					}
					(BinaryOp::Or, ConstValue::Bool(true)) => {
						return Ok(ConstValue::Bool(true));
					}
					_ => {}
				}
				let rhs = self.eval(rhs)?;
				binary(op, lhs, rhs).map_err(|kind| {
					Some(EvalError {
						span: self.body.span(expr),
						kind,
					})
				})
			}
		}
	}
}

impl ConstValue {
	fn scalar(self) -> Option<Scalar> {
		match self {
			Self::Int { scalar, .. } | Self::Float { scalar, .. } => {
				Some(scalar)
			}
			Self::Bool(_) => Some(Scalar::Bool),
			Self::Char(_) => Some(Scalar::Char),
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
	if let Some(ordering) = compare(op, lhs, rhs) {
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
						return Err(EvalErrorKind::ShiftOverflow(op));
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
			let value = if scalar == Scalar::F32 {
				let (a, b) = (a as f32, b as f32);
				f64::from(match op {
					BinaryOp::Add => a + b,
					BinaryOp::Sub => a - b,
					BinaryOp::Mul => a * b,
					BinaryOp::Div => a / b,
					BinaryOp::Rem => a % b,
					_ => unreachable!(),
				})
			} else {
				match op {
					BinaryOp::Add => a + b,
					BinaryOp::Sub => a - b,
					BinaryOp::Mul => a * b,
					BinaryOp::Div => a / b,
					BinaryOp::Rem => a % b,
					_ => unreachable!(),
				}
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
fn compare(op: BinaryOp, lhs: ConstValue, rhs: ConstValue) -> Option<bool> {
	use std::cmp::Ordering;
	let ordering = match (lhs, rhs) {
		(
			ConstValue::Int { value: a, .. },
			ConstValue::Int { value: b, .. },
		) => a.partial_cmp(&b),
		// IEEE: any comparison with NaN is false, except `!=`.
		(
			ConstValue::Float { value: a, .. },
			ConstValue::Float { value: b, .. },
		) => a.partial_cmp(&b),
		(ConstValue::Bool(a), ConstValue::Bool(b)) => a.partial_cmp(&b),
		(ConstValue::Char(a), ConstValue::Char(b)) => a.partial_cmp(&b),
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
