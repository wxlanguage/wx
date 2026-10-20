//! Constant evaluation: folds a constant's checked `Body` into a value.
//!
//! The evaluator handles literals, primitive operators over them, references to
//! other constants and the construction of structs, and nothing else: whatever
//! else a body holds (a call, a form the checker does not cover yet) is not a
//! constant. Arithmetic follows the operand type exactly, and a result outside
//! it is an error, not a wrapped value.
//!
//! A value is held as a Wasm runtime holds one: a list of Wasm numbers, one
//! per Wasm value the type occupies, each with the scalar it means. A struct
//! or tuple is its fields' numbers in declaration order, and a zero-sized
//! value is the empty list. Nodes are evaluated on a value stack: each pushes
//! its numbers, and an operator pops its operands.
//!
//! A constant's value is a memoized query (`const_value`), and evaluation asks
//! it on demand: a constant is read when the node naming it is evaluated, so a
//! branch that is not taken reads nothing. Like an impl member's value
//! (`Verdict`), a constant owns the failures of its own evaluation: the body
//! phase reports them, and a constant that reads a failed one fails silently. A
//! loop through constants is owned by its first-defined member, so it is
//! reported once whichever constant is asked first.

use codespan_reporting::diagnostic::Diagnostic;

use super::body::{ArgOrder, ExprIdx, ExprKind};
use super::defs::{ConstIdx, EnumIdx, StructIdx};
use super::operators::Scalar;
use super::signatures::TypeContext;
use super::types::{Substitution, Type, TypeEnvIdx, TypeIndex};
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};

/// A Wasm number, as its bits.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Val {
	I32(u32),
	I64(u64),
	F32(u32),
	F64(u64),
	V128(u128),
}

/// One number of a constant's value: a Wasm number and the scalar it means.
/// A `bool`, `char` or narrow integer is an `I32`; a signed one is held
/// sign-extended. Built and read only through one constructor and one
/// `expect_*` reader per scalar, the one place each scalar's holding is
/// written.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct ConstScalar {
	pub(super) val: Val,
	pub(super) scalar: Scalar,
}

/// A constant's value: its numbers, in declaration order.
pub(super) type ConstValue = Box<[ConstScalar]>;

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
	fn answer(&self) -> Option<Result<&[ConstScalar], Unevaluable>> {
		match self {
			Self::Unevaluated | Self::InProgress => None,
			Self::Evaluated(value) => Some(Ok(value)),
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
	) -> Result<&[ConstScalar], Unevaluable> {
		match self.const_values[usize::from(const_index)] {
			ConstValueState::Unevaluated => {}
			ConstValueState::InProgress => {
				return Err(Unevaluable::Cycle(self.const_cycle(const_index)));
			}
			_ => {
				return self.const_values[usize::from(const_index)]
					.answer()
					.expect("a state past evaluation is final");
			}
		}
		let scalars = match self.constant_scalars(const_index) {
			Ok(scalars) => scalars,
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
		let mut stack = Vec::new();
		let evaluated = self.eval(const_index, root, &mut stack);
		self.const_stack.pop();

		let state = match evaluated {
			Ok(())
				if stack
					.iter()
					.map(|value| value.scalar)
					.eq(scalars.iter().copied()) =>
			{
				ConstValueState::Evaluated(stack.into_boxed_slice())
			}
			// A root of another type is `ERROR` once the checker reports it, so
			// this is a value the checker accepted in another scalar.
			Ok(()) => ConstValueState::Poisoned,
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
	) -> Result<&[ConstScalar], Unevaluable> {
		self.const_values[usize::from(const_index)] = state;
		self.const_values[usize::from(const_index)]
			.answer()
			.expect("a settled state is final")
	}

	/// Folds one node of `owner`'s body onto `stack`: it pushes the node's
	/// numbers. Each step reads the node by index, so no borrow of the body is
	/// held while a constant it names is evaluated.
	fn eval(
		&mut self,
		owner: ConstIdx,
		expr: ExprIdx,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let body = self.const_bodies[usize::from(owner)].as_ref().unwrap();
		let (kind, ty, span) =
			(body.kind(expr), body.ty(expr), body.span(expr));
		if ty == TypeIndex::ERROR {
			return Err(Halt::Silent);
		}
		let own = |kind| Halt::Own(EvalError { span, kind });
		match kind {
			ExprKind::Error => return Err(Halt::Silent),
			// Locals, calls, control flow and memory are not evaluated (yet).
			ExprKind::String(_)
			| ExprKind::AbstractCall { .. }
			| ExprKind::Local(_)
			| ExprKind::Global(_)
			| ExprKind::Function(_)
			| ExprKind::Drop { .. }
			| ExprKind::Call { .. }
			| ExprKind::Cast { .. }
			| ExprKind::FieldAccess { .. }
			| ExprKind::Load(_)
			| ExprKind::AddressOf(_)
			| ExprKind::Block { .. }
			| ExprKind::LocalDeclaration { .. }
			| ExprKind::Match { .. }
			| ExprKind::IfElse { .. }
			| ExprKind::Loop { .. }
			| ExprKind::Break { .. }
			| ExprKind::Continue { .. }
			| ExprKind::Return { .. }
			| ExprKind::Assign { .. }
			| ExprKind::Store { .. }
			| ExprKind::PrimitiveCompoundAssign { .. }
			| ExprKind::ConcreteCompoundAssign { .. }
			| ExprKind::AbstractCompoundAssign { .. }
			| ExprKind::PrimitiveCompoundStore { .. }
			| ExprKind::ConcreteCompoundStore { .. }
			| ExprKind::AbstractCompoundStore { .. } => {
				return Err(own(EvalErrorKind::NotConst));
			}
			ExprKind::Int(value) => match Scalar::from_type(ty) {
				Some(scalar) => {
					stack.push(literal(value, false, scalar).expect(
						"the checker keeps a literal in its type's range",
					))
				}
				None => return Err(own(EvalErrorKind::NotConst)),
			},
			ExprKind::Float(value) => match Scalar::from_type(ty) {
				Some(Scalar::F32) => stack.push(ConstScalar::f32(value as f32)),
				Some(Scalar::F64) => stack.push(ConstScalar::f64(value)),
				_ => return Err(own(EvalErrorKind::NotConst)),
			},
			ExprKind::Bool(value) => stack.push(ConstScalar::bool(value)),
			ExprKind::Char(value) => stack.push(ConstScalar::char(value)),
			// An impl's constant may depend on the impl's arguments, which
			// evaluation does not substitute (yet).
			ExprKind::Const {
				constant,
				type_args,
			} if type_args.is_empty() => {
				self.read_constant(constant, span, stack)?;
			}
			ExprKind::Const { .. } | ExprKind::AbstractConst { .. } => {
				return Err(own(EvalErrorKind::NotConst));
			}
			ExprKind::NextDiscriminant(previous) => {
				self.read_constant(previous, span, stack)?;
				let previous = stack.pop().expect("a variant's value");
				let one = literal(1, false, previous.scalar)
					.expect("an enum's repr holds one");
				stack.push(binary(BinaryOp::Add, previous, one).map_err(own)?);
			}
			// A negated literal is one literal, so `-128` fits an `i8` although
			// `128` does not.
			ExprKind::PrimitiveUnary {
				op: UnaryOp::InvertSign,
				operand,
			} if let ExprKind::Int(value) = body.kind(operand)
				&& let Some(scalar) = Scalar::from_type(ty) =>
			{
				stack.push(
					literal(value, true, scalar).ok_or(own(
						EvalErrorKind::Overflow(Operation::Negate),
					))?,
				);
			}
			ExprKind::PrimitiveUnary { op, operand } => {
				self.eval(owner, operand, stack)?;
				let operand = stack.pop().expect("an operand's value");
				stack.push(unary(op, operand).map_err(own)?);
			}
			// Its values are its elements', in order, as its type's layout is.
			ExprKind::Tuple { elements } => {
				for at in 0..elements.len() {
					let body =
						self.const_bodies[usize::from(owner)].as_ref().unwrap();
					let element = body.args(elements)[at];
					self.eval(owner, element, stack)?;
				}
			}
			ExprKind::StructConstructor {
				struct_index,
				args,
				order,
			} => {
				let count =
					self.structs[usize::from(struct_index)].field_types.len();
				// A missing field was reported.
				if args.len() != count {
					return Err(Halt::Silent);
				}
				// Evaluated in written order, held in declaration order.
				let start = stack.len();
				let mut fields = Vec::new();
				for at in 0..count {
					let body =
						self.const_bodies[usize::from(owner)].as_ref().unwrap();
					let (arg, field) =
						(body.args(args)[at], body.declared_index(order, at));
					let field_start = stack.len();
					self.eval(owner, arg, stack)?;
					if matches!(order, ArgOrder::Permuted { .. }) {
						fields.push((
							usize::from(field),
							field_start - start..stack.len() - start,
						));
					}
				}
				if !fields.is_empty() {
					fields.sort_unstable_by_key(|&(field, _)| field);
					let written = stack.split_off(start);
					for (_, range) in fields {
						stack.extend_from_slice(&written[range]);
					}
				}
			}
			ExprKind::PrimitiveBinary { op, lhs, rhs } => {
				self.eval(owner, lhs, stack)?;
				// `&&` and `||` do not evaluate a right side they do not need;
				// otherwise the right side is the answer.
				if matches!(op, BinaryOp::And | BinaryOp::Or) {
					let lhs = stack.last().expect("an operand's value");
					if lhs.expect_bool() == (op == BinaryOp::Or) {
						return Ok(());
					}
					stack.pop();
					return self.eval(owner, rhs, stack);
				}
				self.eval(owner, rhs, stack)?;
				let rhs = stack.pop().expect("an operand's value");
				let lhs = stack.pop().expect("an operand's value");
				stack.push(binary(op, lhs, rhs).map_err(own)?);
			}
		}
		Ok(())
	}

	/// The value of a constant a node names. One with no compile-time value
	/// (its type is not a scalar) makes the naming node not a constant
	/// expression.
	fn read_constant(
		&mut self,
		const_index: ConstIdx,
		span: TextSpan,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		match self.const_value(const_index) {
			Ok(value) => {
				stack.extend_from_slice(value);
				Ok(())
			}
			Err(Unevaluable::NoValue) => Err(Halt::Own(EvalError {
				span,
				kind: EvalErrorKind::NotConst,
			})),
			Err(Unevaluable::Silent) => Err(Halt::Silent),
			Err(Unevaluable::Cycle(cycle)) => Err(Halt::Cycle(cycle)),
		}
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

	/// The scalars a value of the constant's declared type holds, one per
	/// number. `Err` is the final state of a constant of a type the evaluator
	/// holds no values of.
	fn constant_scalars(
		&mut self,
		const_index: ConstIdx,
	) -> Result<Vec<Scalar>, ConstValueState> {
		let (ty, scope) = self.constant_type(const_index);
		let mut scalars = Vec::new();
		self.push_scalars(scope, ty, &mut scalars, &mut Vec::new())?;
		Ok(scalars)
	}

	/// Appends the scalars a value of `ty` holds, normalized in `scope`: a
	/// scalar's own, an enum's repr, a struct's or tuple's fields in
	/// declaration order, nothing for a zero-sized type. `Err` is the final
	/// state of a constant of a type the evaluator holds no values of: no
	/// value (`!`, an address, a function reference, an abstract type), or
	/// poisoned when the type, or a field's, failed to resolve, which was
	/// reported where it is written. A struct reached again through
	/// `visiting`, the structs being looked through, contains itself, which is
	/// reported on the struct.
	fn push_scalars(
		&mut self,
		scope: TypeEnvIdx,
		ty: TypeIndex,
		out: &mut Vec<Scalar>,
		visiting: &mut Vec<StructIdx>,
	) -> Result<(), ConstValueState> {
		let ty = self.normalize_type_query(scope, ty).unwrap_or(ty);
		if ty == TypeIndex::ERROR {
			return Err(ConstValueState::Poisoned);
		}
		if let Some(scalar) = Scalar::from_type(ty) {
			out.push(scalar);
			return Ok(());
		}
		match *self.types.resolve(ty) {
			Type::Function { .. }
			| Type::Memory { .. }
			| Type::Global { .. } => Ok(()),
			Type::Enum { enum_index } => {
				let repr = self.enum_repr(enum_index);
				self.push_scalars(scope, repr, out, visiting)
			}
			Type::Tuple { elements } => {
				let mut held = Ok(());
				for at in 0..self.types.list(elements).len() {
					let element = self.types.list(elements)[at];
					held = merge(
						held,
						self.push_scalars(scope, element, out, visiting),
					);
					if held == Err(ConstValueState::Poisoned) {
						break;
					}
				}
				held
			}
			Type::Struct {
				struct_index,
				type_args,
			} => {
				if visiting.contains(&struct_index) {
					return Err(ConstValueState::Poisoned);
				}
				let env = self.structs[usize::from(struct_index)].type_params;
				visiting.push(struct_index);
				let args: Box<[TypeIndex]> = self.types.list(type_args).into();
				let mut held = Ok(());
				let count =
					self.structs[usize::from(struct_index)].field_types.len();
				for at in 0..count {
					let field =
						self.structs[usize::from(struct_index)].field_types[at];
					let field = self.types.substitute(
						field,
						Substitution {
							envs: &self.type_envs,
							env,
							args: &args,
						},
					);
					held = merge(
						held,
						self.push_scalars(scope, field, out, visiting),
					);
					if held == Err(ConstValueState::Poisoned) {
						break;
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
			if let Ok(&[value]) = self.const_value(variant) {
				values.push((value, variant));
			}
		}
		// Every variant has the repr's scalar, so equal values are equal
		// numbers. Stable, so each set keeps source order; the sets are then
		// reported in the source order of their first variant.
		values.sort_by_key(|&(value, _)| value.val);
		let mut groups: Vec<&[(ConstScalar, ConstIdx)]> = values
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

impl ConstScalar {
	pub(super) fn u8(value: u8) -> Self {
		Self {
			val: Val::I32(u32::from(value)),
			scalar: Scalar::U8,
		}
	}

	pub(super) fn i8(value: i8) -> Self {
		Self {
			val: Val::I32(i32::from(value) as u32),
			scalar: Scalar::I8,
		}
	}

	pub(super) fn u16(value: u16) -> Self {
		Self {
			val: Val::I32(u32::from(value)),
			scalar: Scalar::U16,
		}
	}

	pub(super) fn i16(value: i16) -> Self {
		Self {
			val: Val::I32(i32::from(value) as u32),
			scalar: Scalar::I16,
		}
	}

	pub(super) fn u32(value: u32) -> Self {
		Self {
			val: Val::I32(value),
			scalar: Scalar::U32,
		}
	}

	pub(super) fn i32(value: i32) -> Self {
		Self {
			val: Val::I32(value as u32),
			scalar: Scalar::I32,
		}
	}

	pub(super) fn u64(value: u64) -> Self {
		Self {
			val: Val::I64(value),
			scalar: Scalar::U64,
		}
	}

	pub(super) fn i64(value: i64) -> Self {
		Self {
			val: Val::I64(value as u64),
			scalar: Scalar::I64,
		}
	}

	pub(super) fn f32(value: f32) -> Self {
		Self {
			val: Val::F32(value.to_bits()),
			scalar: Scalar::F32,
		}
	}

	pub(super) fn f64(value: f64) -> Self {
		Self {
			val: Val::F64(value.to_bits()),
			scalar: Scalar::F64,
		}
	}

	pub(super) fn bool(value: bool) -> Self {
		Self {
			val: Val::I32(u32::from(value)),
			scalar: Scalar::Bool,
		}
	}

	pub(super) fn char(value: char) -> Self {
		Self {
			val: Val::I32(u32::from(value)),
			scalar: Scalar::Char,
		}
	}

	pub(super) fn expect_u8(self) -> u8 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::U8,
			} => bits as u8,
			_ => unreachable!("not a `u8`"),
		}
	}

	pub(super) fn expect_i8(self) -> i8 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::I8,
			} => bits as i8,
			_ => unreachable!("not an `i8`"),
		}
	}

	pub(super) fn expect_u16(self) -> u16 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::U16,
			} => bits as u16,
			_ => unreachable!("not a `u16`"),
		}
	}

	pub(super) fn expect_i16(self) -> i16 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::I16,
			} => bits as i16,
			_ => unreachable!("not an `i16`"),
		}
	}

	pub(super) fn expect_u32(self) -> u32 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::U32,
			} => bits,
			_ => unreachable!("not a `u32`"),
		}
	}

	pub(super) fn expect_i32(self) -> i32 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::I32,
			} => bits as i32,
			_ => unreachable!("not an `i32`"),
		}
	}

	pub(super) fn expect_u64(self) -> u64 {
		match self {
			Self {
				val: Val::I64(bits),
				scalar: Scalar::U64,
			} => bits,
			_ => unreachable!("not a `u64`"),
		}
	}

	pub(super) fn expect_i64(self) -> i64 {
		match self {
			Self {
				val: Val::I64(bits),
				scalar: Scalar::I64,
			} => bits as i64,
			_ => unreachable!("not an `i64`"),
		}
	}

	pub(super) fn expect_f32(self) -> f32 {
		match self {
			Self {
				val: Val::F32(bits),
				scalar: Scalar::F32,
			} => f32::from_bits(bits),
			_ => unreachable!("not an `f32`"),
		}
	}

	pub(super) fn expect_f64(self) -> f64 {
		match self {
			Self {
				val: Val::F64(bits),
				scalar: Scalar::F64,
			} => f64::from_bits(bits),
			_ => unreachable!("not an `f64`"),
		}
	}

	pub(super) fn expect_bool(self) -> bool {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::Bool,
			} => bits != 0,
			_ => unreachable!("not a `bool`"),
		}
	}

	pub(super) fn expect_char(self) -> char {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Scalar::Char,
			} => char::from_u32(bits).expect("a `char` holds a scalar value"),
			_ => unreachable!("not a `char`"),
		}
	}
}

impl std::fmt::Display for ConstScalar {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self.scalar {
			Scalar::U8 => write!(f, "{}", self.expect_u8()),
			Scalar::I8 => write!(f, "{}", self.expect_i8()),
			Scalar::U16 => write!(f, "{}", self.expect_u16()),
			Scalar::I16 => write!(f, "{}", self.expect_i16()),
			Scalar::U32 => write!(f, "{}", self.expect_u32()),
			Scalar::I32 => write!(f, "{}", self.expect_i32()),
			Scalar::U64 => write!(f, "{}", self.expect_u64()),
			Scalar::I64 => write!(f, "{}", self.expect_i64()),
			Scalar::F32 => write!(f, "{}", self.expect_f32()),
			Scalar::F64 => write!(f, "{}", self.expect_f64()),
			Scalar::Bool => write!(f, "{}", self.expect_bool()),
			Scalar::Char => write!(f, "{:?}", self.expect_char()),
		}
	}
}

/// The integer literal `value` as `scalar`, negated when it is written
/// `-value`; `None` when it does not fit.
fn literal(value: u64, negated: bool, scalar: Scalar) -> Option<ConstScalar> {
	if !scalar.is_signed() {
		if negated && value != 0 {
			return None;
		}
		return Some(match scalar {
			Scalar::U8 => ConstScalar::u8(u8::try_from(value).ok()?),
			Scalar::U16 => ConstScalar::u16(u16::try_from(value).ok()?),
			Scalar::U32 => ConstScalar::u32(u32::try_from(value).ok()?),
			Scalar::U64 => ConstScalar::u64(value),
			_ => unreachable!("an integer literal has an integer type"),
		});
	}
	let value = if negated {
		0i64.checked_sub_unsigned(value)?
	} else {
		i64::try_from(value).ok()?
	};
	Some(match scalar {
		Scalar::I8 => ConstScalar::i8(i8::try_from(value).ok()?),
		Scalar::I16 => ConstScalar::i16(i16::try_from(value).ok()?),
		Scalar::I32 => ConstScalar::i32(i32::try_from(value).ok()?),
		Scalar::I64 => ConstScalar::i64(value),
		_ => unreachable!("an integer literal has an integer type"),
	})
}

/// The state of a value walked so far and of its next part: a poisoned part
/// poisons the whole, whatever the other parts are, so a reader of it is
/// never reported.
fn merge(
	held: Result<(), ConstValueState>,
	part: Result<(), ConstValueState>,
) -> Result<(), ConstValueState> {
	match (held, part) {
		(Err(ConstValueState::Poisoned), _)
		| (_, Err(ConstValueState::Poisoned)) => Err(ConstValueState::Poisoned),
		(Err(state), _) | (Ok(()), Err(state)) => Err(state),
		(Ok(()), Ok(())) => Ok(()),
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
	operand: ConstScalar,
) -> Result<ConstScalar, EvalErrorKind> {
	match (op, operand.scalar) {
		(UnaryOp::InvertSign, Scalar::F32) => {
			Ok(ConstScalar::f32(-operand.expect_f32()))
		}
		(UnaryOp::InvertSign, Scalar::F64) => {
			Ok(ConstScalar::f64(-operand.expect_f64()))
		}
		(UnaryOp::Not, _) => Ok(ConstScalar::bool(!operand.expect_bool())),
		(UnaryOp::InvertSign | UnaryOp::BitNot, _) => {
			integer_unary(op, operand)
				.ok_or(EvalErrorKind::Overflow(Operation::Negate))
		}
	}
}

/// `-a` or `^a` on an integer, at its own width: `None` when the negation
/// overflows (`-MIN`, or a nonzero unsigned value).
fn integer_unary(op: UnaryOp, operand: ConstScalar) -> Option<ConstScalar> {
	let negate = op == UnaryOp::InvertSign;
	Some(match operand.scalar {
		Scalar::U8 => {
			let a = operand.expect_u8();
			ConstScalar::u8(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::I8 => {
			let a = operand.expect_i8();
			ConstScalar::i8(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::U16 => {
			let a = operand.expect_u16();
			ConstScalar::u16(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::I16 => {
			let a = operand.expect_i16();
			ConstScalar::i16(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::U32 => {
			let a = operand.expect_u32();
			ConstScalar::u32(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::I32 => {
			let a = operand.expect_i32();
			ConstScalar::i32(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::U64 => {
			let a = operand.expect_u64();
			ConstScalar::u64(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::I64 => {
			let a = operand.expect_i64();
			ConstScalar::i64(if negate { a.checked_neg()? } else { !a })
		}
		Scalar::F32 | Scalar::F64 | Scalar::Bool | Scalar::Char => {
			unreachable!(
				"the checker builds primitive operators on their scalars"
			)
		}
	})
}

fn binary(
	op: BinaryOp,
	lhs: ConstScalar,
	rhs: ConstScalar,
) -> Result<ConstScalar, EvalErrorKind> {
	if let Some(ordering) = compare(op, lhs, rhs) {
		return Ok(ConstScalar::bool(ordering));
	}
	match lhs.scalar {
		Scalar::F32 => {
			let (a, b) = (lhs.expect_f32(), rhs.expect_f32());
			Ok(ConstScalar::f32(match op {
				BinaryOp::Add => a + b,
				BinaryOp::Sub => a - b,
				BinaryOp::Mul => a * b,
				BinaryOp::Div => a / b,
				BinaryOp::Rem => a % b,
				_ => unreachable!(),
			}))
		}
		Scalar::F64 => {
			let (a, b) = (lhs.expect_f64(), rhs.expect_f64());
			Ok(ConstScalar::f64(match op {
				BinaryOp::Add => a + b,
				BinaryOp::Sub => a - b,
				BinaryOp::Mul => a * b,
				BinaryOp::Div => a / b,
				BinaryOp::Rem => a % b,
				_ => unreachable!(),
			}))
		}
		Scalar::Bool => {
			let (a, b) = (lhs.expect_bool(), rhs.expect_bool());
			Ok(ConstScalar::bool(match op {
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				_ => unreachable!(),
			}))
		}
		_ => {
			// A checked division answers `None` for a zero divisor too.
			let zero = Some(rhs) == literal(0, false, rhs.scalar);
			match op {
				BinaryOp::Div if zero => Err(EvalErrorKind::DivisionByZero),
				BinaryOp::Rem if zero => Err(EvalErrorKind::RemainderByZero),
				_ => integer_binary(op, lhs, rhs)
					.ok_or(EvalErrorKind::Overflow(Operation::Binary(op))),
			}
		}
	}
}

/// `a op b` on two integers of one scalar, at its own width: `None` when the
/// result is outside it, or a shift amount is outside its width. Division
/// truncates and `MIN / -1` overflows, as wasm's `div_s`; a remainder has
/// the dividend's sign and never overflows, as wasm's `rem_s`. A shift drops
/// the bits shifted past the width, and a right shift of a signed type is
/// arithmetic.
fn integer_binary(
	op: BinaryOp,
	lhs: ConstScalar,
	rhs: ConstScalar,
) -> Option<ConstScalar> {
	Some(match lhs.scalar {
		Scalar::U8 => {
			let (a, b) = (lhs.expect_u8(), rhs.expect_u8());
			ConstScalar::u8(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(u32::from(b))?,
				BinaryOp::RightShift => a.checked_shr(u32::from(b))?,
				_ => unreachable!(),
			})
		}
		Scalar::I8 => {
			let (a, b) = (lhs.expect_i8(), rhs.expect_i8());
			ConstScalar::i8(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(u32::try_from(b).ok()?)?,
				BinaryOp::RightShift => {
					a.checked_shr(u32::try_from(b).ok()?)?
				}
				_ => unreachable!(),
			})
		}
		Scalar::U16 => {
			let (a, b) = (lhs.expect_u16(), rhs.expect_u16());
			ConstScalar::u16(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(u32::from(b))?,
				BinaryOp::RightShift => a.checked_shr(u32::from(b))?,
				_ => unreachable!(),
			})
		}
		Scalar::I16 => {
			let (a, b) = (lhs.expect_i16(), rhs.expect_i16());
			ConstScalar::i16(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(u32::try_from(b).ok()?)?,
				BinaryOp::RightShift => {
					a.checked_shr(u32::try_from(b).ok()?)?
				}
				_ => unreachable!(),
			})
		}
		Scalar::U32 => {
			let (a, b) = (lhs.expect_u32(), rhs.expect_u32());
			ConstScalar::u32(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(b)?,
				BinaryOp::RightShift => a.checked_shr(b)?,
				_ => unreachable!(),
			})
		}
		Scalar::I32 => {
			let (a, b) = (lhs.expect_i32(), rhs.expect_i32());
			ConstScalar::i32(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(u32::try_from(b).ok()?)?,
				BinaryOp::RightShift => {
					a.checked_shr(u32::try_from(b).ok()?)?
				}
				_ => unreachable!(),
			})
		}
		Scalar::U64 => {
			let (a, b) = (lhs.expect_u64(), rhs.expect_u64());
			ConstScalar::u64(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(u32::try_from(b).ok()?)?,
				BinaryOp::RightShift => {
					a.checked_shr(u32::try_from(b).ok()?)?
				}
				_ => unreachable!(),
			})
		}
		Scalar::I64 => {
			let (a, b) = (lhs.expect_i64(), rhs.expect_i64());
			ConstScalar::i64(match op {
				BinaryOp::Add => a.checked_add(b)?,
				BinaryOp::Sub => a.checked_sub(b)?,
				BinaryOp::Mul => a.checked_mul(b)?,
				BinaryOp::Div => a.checked_div(b)?,
				BinaryOp::Rem => a.wrapping_rem(b),
				BinaryOp::BitAnd => a & b,
				BinaryOp::BitOr => a | b,
				BinaryOp::BitXor => a ^ b,
				BinaryOp::LeftShift => a.checked_shl(u32::try_from(b).ok()?)?,
				BinaryOp::RightShift => {
					a.checked_shr(u32::try_from(b).ok()?)?
				}
				_ => unreachable!(),
			})
		}
		Scalar::F32 | Scalar::F64 | Scalar::Bool | Scalar::Char => {
			unreachable!(
				"the checker builds primitive operators on their scalars"
			)
		}
	})
}

/// The answer of a comparison, `None` for any other operator.
fn compare(op: BinaryOp, lhs: ConstScalar, rhs: ConstScalar) -> Option<bool> {
	use std::cmp::Ordering;
	let ordering = match lhs.scalar {
		Scalar::U8 => lhs.expect_u8().partial_cmp(&rhs.expect_u8()),
		Scalar::I8 => lhs.expect_i8().partial_cmp(&rhs.expect_i8()),
		Scalar::U16 => lhs.expect_u16().partial_cmp(&rhs.expect_u16()),
		Scalar::I16 => lhs.expect_i16().partial_cmp(&rhs.expect_i16()),
		Scalar::U32 => lhs.expect_u32().partial_cmp(&rhs.expect_u32()),
		Scalar::I32 => lhs.expect_i32().partial_cmp(&rhs.expect_i32()),
		Scalar::U64 => lhs.expect_u64().partial_cmp(&rhs.expect_u64()),
		Scalar::I64 => lhs.expect_i64().partial_cmp(&rhs.expect_i64()),
		// IEEE: any comparison with NaN is false, except `!=`.
		Scalar::F32 => lhs.expect_f32().partial_cmp(&rhs.expect_f32()),
		Scalar::F64 => lhs.expect_f64().partial_cmp(&rhs.expect_f64()),
		Scalar::Bool => lhs.expect_bool().partial_cmp(&rhs.expect_bool()),
		Scalar::Char => lhs.expect_char().partial_cmp(&rhs.expect_char()),
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
