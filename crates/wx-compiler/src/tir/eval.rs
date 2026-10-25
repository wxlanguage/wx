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
use string_interner::symbol::SymbolU32;

use super::body::{
	Body, BodyOwner, ConstBody, ElementOrder, ExprIdx, ExprKind, ExprRange,
};
use super::defs::{ConstIdx, EnumIdx, MemoryIdx};
use super::layout::Primitive;
use super::operators::Scalar;
use super::signatures::TypeContext;
use super::types::{Substitution, Type, TypeEnvIdx, TypeIndex};
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::index::index_newtype;

index_newtype!(AllocIdx);

/// A Wasm value, as its bits. An address into linear memory has no bits
/// yet: it is an offset into an allocation, and its number is known once
/// the allocation is placed in its memory.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Val {
	I32(u32),
	I64(u64),
	F32(u32),
	F64(u64),
	V128(u128),
	/// As wide as its allocation's memory's `Size`.
	MemoryOffset {
		alloc: AllocIdx,
		offset: u64,
	},
}

/// Bytes a constant's value points into, placed in `memory`'s data when
/// the program is laid out. Constant evaluation creates them (a string
/// literal's contents) and never writes them afterwards.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Allocation {
	pub(super) memory: MemoryIdx,
	pub(super) align: u32,
	pub(super) bytes: Box<[u8]>,
	/// The addresses written in `bytes`, sorted by offset: the address at
	/// each offset points into that allocation, and the bytes there hold the
	/// offset into it.
	pub(super) relocations: Box<[(u32, AllocIdx)]>,
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
	/// Static data takes more bytes than an allocation holds.
	TooLarge,
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

	/// A constant's value as a pattern compares with it: the bits of its one
	/// Wasm number (a narrow signed integer sign-extended, as it is held).
	/// `None` when it has no value or is more than one number.
	pub(super) fn constant_bits(
		&mut self,
		const_index: ConstIdx,
	) -> Option<u64> {
		match self.const_value(const_index) {
			Ok([scalar]) => match scalar.val {
				Val::I32(bits) => Some(u64::from(bits)),
				Val::I64(bits) => Some(bits),
				Val::F32(_)
				| Val::F64(_)
				| Val::V128(_)
				| Val::MemoryOffset { .. } => None,
			},
			_ => None,
		}
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
		let Some(body) = self.const_body(const_index) else {
			// The body is being built, and we are inside its own build: its
			// value cannot be known yet, and building its body again would
			// ask it for its value again. The caller reads it as "no value
			// here", which is what a constant whose value is not known
			// means.
			if matches!(
				self.const_bodies[usize::from(const_index)],
				ConstBody::Building
			) {
				return Err(Unevaluable::Silent);
			}
			// A constant with no initializer at all: a required trait
			// constant.
			return self.settle_constant(const_index, ConstValueState::NoValue);
		};
		let root = body.root();
		self.const_values[usize::from(const_index)] =
			ConstValueState::InProgress;
		self.const_stack.push(const_index);
		let mut stack = Vec::new();
		let evaluated =
			self.eval(BodyOwner::Const(const_index), root, &mut stack);
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

	/// The values of a tuple's `elements`, evaluated in written order and
	/// held in the positions `order` gives them.
	fn eval_ordered(
		&mut self,
		owner: BodyOwner,
		elements: ExprRange,
		order: ElementOrder,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let ElementOrder::Permuted { .. } = order else {
			for at in 0..elements.len() {
				let arg = self.body_of(owner).args(elements)[at];
				self.eval(owner, arg, stack)?;
			}
			return Ok(());
		};
		let start = stack.len();
		let mut declared = Vec::with_capacity(elements.len());
		for at in 0..elements.len() {
			let body = self.body_of(owner);
			let (arg, index) =
				(body.args(elements)[at], body.declared_index(order, at));
			let arg_start = stack.len();
			self.eval(owner, arg, stack)?;
			declared.push((
				usize::from(index),
				arg_start - start..stack.len() - start,
			));
		}
		declared.sort_unstable_by_key(|&(index, _)| index);
		let written = stack.split_off(start);
		for (_, range) in declared {
			stack.extend_from_slice(&written[range]);
		}
		Ok(())
	}

	/// Folds one node of `owner`'s body onto `stack`: it pushes the node's
	/// numbers. Each step reads the node by index, so no borrow of the body is
	/// held while a constant it names is evaluated.
	fn eval(
		&mut self,
		owner: BodyOwner,
		expr: ExprIdx,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let body = self.body_of(owner);
		let (kind, ty, span) =
			(body.kind(expr), body.ty(expr), body.span(expr));
		if ty == TypeIndex::ERROR {
			return Err(Halt::Silent);
		}
		let own = |kind| Halt::Own(EvalError { span, kind });
		match kind {
			ExprKind::Error => return Err(Halt::Silent),
			// Locals, calls, control flow and memory are not evaluated (yet).
			ExprKind::AbstractCall { .. }
			| ExprKind::Local(_)
			| ExprKind::Drop { .. }
			| ExprKind::Call { .. }
			| ExprKind::MethodCall { .. }
			| ExprKind::AbstractMethodCall { .. }
			| ExprKind::CallRef { .. }
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
			// A function item and a global's handle are zero-sized: the type
			// says everything.
			ExprKind::Function { .. } | ExprKind::Global(_) => {}
			ExprKind::String(contents) => {
				self.eval_string(owner, contents, ty, span, stack)?;
			}
			// Each element's values, one after another, laid out as static
			// data.
			ExprKind::Array { elements } => {
				let start = stack.len();
				for at in 0..elements.len() {
					let element = self.body_of(owner).args(elements)[at];
					self.eval(owner, element, stack)?;
				}
				let count = u64::try_from(elements.len()).unwrap();
				self.place_static(owner, ty, span, count, start, stack)?;
			}
			// One element's values, laid out `count` times; `_` is the
			// array's own length.
			ExprKind::ArrayRepeat { value, count } => {
				let start = stack.len();
				self.eval(owner, value, stack)?;
				let count = match count {
					Some(count) => {
						self.eval(owner, count, stack)?;
						match stack.pop().expect("a count's value").val {
							Val::I32(bits) => u64::from(bits),
							Val::I64(bits) => bits,
							_ => {
								unreachable!("a count is of a memory's `Size`")
							}
						}
					}
					None => {
						let Type::Array { length, .. } =
							*self.types.resolve(ty)
						else {
							unreachable!("`_` is the length of an array")
						};
						let Type::Value { bits } = *self.types.resolve(length)
						else {
							unreachable!("a checked array has a length")
						};
						bits
					}
				};
				self.place_static(owner, ty, span, count, start, stack)?;
			}
			// A cast to the value's own type changes nothing; a literal cast
			// has the target as its type.
			ExprKind::Cast { value } if body.ty(value) == ty => {
				self.eval(owner, value, stack)?;
			}
			// Making an address from an integer, or reading the bits of one,
			// is not evaluated (yet).
			ExprKind::Cast { .. } => return Err(own(EvalErrorKind::NotConst)),
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
			// Its values are its elements', in declared order, as its type's
			// layout is.
			ExprKind::Tuple { elements, order } => {
				self.eval_ordered(owner, elements, order, stack)?;
			}
			// Its fields' value; one missing was reported, which makes it
			// `ERROR`.
			ExprKind::StructConstructor { fields, .. } => {
				self.eval(owner, fields, stack)?;
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

	/// The checked body of `owner`. Evaluation reads a body only once it is
	/// built.
	fn body_of(&self, owner: BodyOwner) -> &Body {
		match owner {
			BodyOwner::Const(const_index) => self
				.const_body(const_index)
				.expect("an evaluated constant's body is built"),
			BodyOwner::Function(function_index) => self.function_bodies
				[usize::from(function_index)]
			.as_ref()
			.expect("an evaluated function's body is built"),
			BodyOwner::Global(global_index) => self.global_bodies
				[usize::from(global_index)]
			.as_ref()
			.expect("an evaluated global's body is built"),
		}
	}

	/// The type scope `owner`'s body is checked in.
	fn body_env(&self, owner: BodyOwner) -> TypeEnvIdx {
		match owner {
			BodyOwner::Const(const_index) => {
				self.constants[usize::from(const_index)].env
			}
			BodyOwner::Function(function_index) => {
				self.functions[usize::from(function_index)].type_params
			}
			BodyOwner::Global(_) => TypeEnvIdx::ROOT,
		}
	}

	/// A string literal's value: its contents, placed as static data.
	fn eval_string(
		&mut self,
		owner: BodyOwner,
		contents: SymbolU32,
		ty: TypeIndex,
		span: TextSpan,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let (memory, width) = self.static_memory(owner, ty, span)?;
		let bytes: Box<[u8]> =
			self.strings.resolve(contents).unwrap().as_bytes().into();
		let len = bytes.len() as u64;
		let allocation = Allocation {
			memory,
			align: 1,
			bytes,
			relocations: Box::default(),
		};
		self.push_static(allocation, width, ty, len, stack);
		Ok(())
	}

	/// Replaces `stack[start..]` with the address of static data of type
	/// `ty` holding `count` elements: each element's values, in declaration
	/// order, written at its place in the element type's layout. The values
	/// are every element's, one after another, or one element's for a repeat,
	/// which every element takes.
	fn place_static(
		&mut self,
		owner: BodyOwner,
		ty: TypeIndex,
		span: TextSpan,
		count: u64,
		start: usize,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let (memory, width) = self.static_memory(owner, ty, span)?;
		let (Type::Slice { of, .. } | Type::Array { of, .. }) =
			*self.types.resolve(ty)
		else {
			unreachable!("static data is an array or a slice")
		};
		// Elements whose bytes are not known yet (of an abstract type) cannot
		// be written.
		let (layout, places) =
			match self.memory_values(self.body_env(owner), of) {
				Ok(Some(layout)) => layout,
				Ok(None) => {
					return Err(Halt::Own(EvalError {
						span,
						kind: EvalErrorKind::NotConst,
					}));
				}
				Err(_) => return Err(Halt::Silent),
			};
		// An offset into an allocation is a `u32`.
		let Some(size) = count
			.checked_mul(u64::from(layout.size))
			.and_then(|size| u32::try_from(size).ok())
		else {
			return Err(Halt::Own(EvalError {
				span,
				kind: EvalErrorKind::TooLarge,
			}));
		};
		let mut bytes = vec![0; size as usize];
		let mut relocations = Vec::new();
		// A zero-sized element has no values to write.
		if !places.is_empty() {
			let elements = stack[start..].chunks_exact(places.len()).cycle();
			for (at, value) in (0..u32::try_from(count).unwrap()).zip(elements)
			{
				write_value(
					&mut bytes,
					&mut relocations,
					at * layout.size,
					value,
					&places,
				);
			}
		}
		stack.truncate(start);
		// Within an element, values are in declaration order, not offset order.
		relocations.sort_unstable_by_key(|&(offset, _)| offset);
		let allocation = Allocation {
			memory,
			align: layout.align,
			bytes: bytes.into_boxed_slice(),
			relocations: relocations.into_boxed_slice(),
		};
		self.push_static(allocation, width, ty, count, stack);
		Ok(())
	}

	/// The memory static data of type `ty` (a shared array or slice) is
	/// placed in, and the scalar its address is held as. In a memory not
	/// known yet there is nowhere to place it.
	fn static_memory(
		&mut self,
		owner: BodyOwner,
		ty: TypeIndex,
		span: TextSpan,
	) -> Result<(MemoryIdx, Scalar), Halt> {
		let scope = self.body_env(owner);
		let (Type::Slice { memory, .. } | Type::Array { memory, .. }) =
			*self.types.resolve(ty)
		else {
			unreachable!("static data is an array or a slice")
		};
		let Some(memory_index) = self.memory_of(scope, memory) else {
			return Err(Halt::Own(EvalError {
				span,
				kind: EvalErrorKind::NotConst,
			}));
		};
		// The memory is known, so its `Size` is: a failure was reported.
		let width = self
			.address_scalar(scope, memory)
			.map_err(|_| Halt::Silent)?;
		Ok((memory_index, width))
	}

	/// Stores `allocation` and pushes its address, followed by `len` for a
	/// slice (`ty`).
	fn push_static(
		&mut self,
		allocation: Allocation,
		width: Scalar,
		ty: TypeIndex,
		len: u64,
		stack: &mut Vec<ConstScalar>,
	) {
		let alloc =
			AllocIdx::new(u32::try_from(self.allocations.len()).unwrap());
		self.allocations.push(allocation);
		stack.push(ConstScalar {
			val: Val::MemoryOffset { alloc, offset: 0 },
			scalar: width,
		});
		if let Type::Slice { .. } = self.types.resolve(ty) {
			stack.push(match width {
				Scalar::U32 => ConstScalar::u32(u32::try_from(len).unwrap()),
				Scalar::U64 => ConstScalar::u64(len),
				_ => unreachable!("`PointerSize` holds `u32` and `u64`"),
			});
		}
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
		let signature = &self.constants[usize::from(const_index)];
		let (ty, scope) = (signature.ty, signature.env);
		let mut scalars = Vec::new();
		self.push_scalars(scope, ty, &mut scalars, &mut Vec::new())?;
		Ok(scalars)
	}

	/// Appends the scalars a value of `ty` holds, normalized in `scope`: a
	/// scalar's own, an enum's repr, a struct's or tuple's fields in
	/// declaration order, an address as its memory's `Size` (a slice is its
	/// address and its length), nothing for a zero-sized type. `Err` is the
	/// final state of a constant of a type the evaluator holds no values of:
	/// no value (`!`, a function reference, an abstract type, an address into
	/// a memory not known), or poisoned when the type, or a field's, failed to
	/// resolve, which was reported where it is written. A struct reached
	/// again through `visiting`, the structs being looked through as
	/// instantiated, contains itself, which is reported on the struct.
	fn push_scalars(
		&mut self,
		scope: TypeEnvIdx,
		ty: TypeIndex,
		out: &mut Vec<Scalar>,
		visiting: &mut Vec<TypeIndex>,
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
			Type::Pointer { memory, .. } | Type::Array { memory, .. } => {
				out.push(self.address_scalar(scope, memory)?);
				Ok(())
			}
			Type::Slice { memory, .. } => {
				let scalar = self.address_scalar(scope, memory)?;
				out.extend([scalar, scalar]);
				Ok(())
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
				if visiting.contains(&ty)
					|| visiting.len() > self.solver.state.recursion_budget
				{
					return Err(ConstValueState::Poisoned);
				}
				let env = self.structs[usize::from(struct_index)].type_params;
				visiting.push(ty);
				let args: Box<[TypeIndex]> = self.types.list(type_args).into();
				let mut held = Ok(());
				let count =
					self.structs[usize::from(struct_index)].field_types.len();
				for at in 0..count {
					let fields =
						self.structs[usize::from(struct_index)].field_types;
					let field = self.types.list(fields)[at];
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

	/// The scalar an address into `memory` is held as, its `Size`; no value
	/// for an address into a memory not known yet.
	fn address_scalar(
		&mut self,
		scope: TypeEnvIdx,
		memory: TypeIndex,
	) -> Result<Scalar, ConstValueState> {
		let Some(memory_index) = self.memory_of(scope, memory) else {
			return Err(ConstValueState::NoValue);
		};
		let size =
			self.defs.memories[usize::from(memory_index)].size_assoc_type_index;
		let size = self.assoc_types[usize::from(size)]
			.as_ref()
			.and_then(|signature| signature.value)
			.ok_or(ConstValueState::Poisoned)?;
		let size = self.normalize_type_query(scope, size).unwrap_or(size);
		Scalar::from_type(size).ok_or(ConstValueState::Poisoned)
	}

	/// The memory `memory` names in `scope`, if it is a known one.
	fn memory_of(
		&mut self,
		scope: TypeEnvIdx,
		memory: TypeIndex,
	) -> Option<MemoryIdx> {
		let memory = self.normalize_type_query(scope, memory).unwrap_or(memory);
		match *self.types.resolve(memory) {
			Type::Memory { memory_index } => Some(memory_index),
			_ => None,
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
		// Every variant has the repr's scalar, an integer, so equal values are
		// equal numbers. Stable, so each set keeps source order; the sets are
		// then reported in the source order of their first variant.
		values.sort_by_key(|&(value, _)| match value.val {
			Val::I32(bits) => u64::from(bits),
			Val::I64(bits) => bits,
			_ => unreachable!("an enum's repr is an integer"),
		});
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
				let body = self.const_body(variant).unwrap();
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
			Self::TooLarge => {
				"static data of more than 4 GiB is not supported".to_string()
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

/// Writes `value`, a value's numbers in declaration order, into `bytes` at
/// `base`: each number at its place in the value's layout, little-endian and
/// as wide as its primitive. An address is written as its offset, and
/// recorded as a relocation to its allocation.
fn write_value(
	bytes: &mut [u8],
	relocations: &mut Vec<(u32, AllocIdx)>,
	base: u32,
	value: &[ConstScalar],
	places: &[(Primitive, u32)],
) {
	debug_assert_eq!(value.len(), places.len());
	for (number, &(primitive, offset)) in value.iter().zip(places) {
		let at = base + offset;
		let bits = match number.val {
			Val::I32(bits) | Val::F32(bits) => u128::from(bits),
			Val::I64(bits) | Val::F64(bits) => u128::from(bits),
			Val::V128(bits) => bits,
			Val::MemoryOffset { alloc, offset } => {
				relocations.push((at, alloc));
				u128::from(offset)
			}
		};
		let size = primitive.size() as usize;
		bytes[at as usize..][..size]
			.copy_from_slice(&bits.to_le_bytes()[..size]);
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

#[cfg(test)]
mod tests {
	use codespan_reporting::diagnostic::Diagnostic;
	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::DiagnosticCode;
	use crate::testing::DiagnosticView;
	use crate::tir::defs::{
		AstEntry, DefKind, DefinitionRegistry, Scope, Tier,
	};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::paths::PathResolver;
	use crate::tir::resolutions::NameResolutions;
	use crate::vfs::{self, FileId, Files};

	const STDLIB: &str = include_str!("../../std/main.wx");

	/// `test_case!(case = "source")` declares the graph, the inputs and the
	/// swept `TestCase` borrowing them as three locals of the calling test.
	/// The test's items are appended to the real stdlib.
	macro_rules! test_case {
		($case:ident = $source:expr $(,)?) => {
			let mut graph = source_graph($source);
			let mut inputs = TestInputs::new(&mut graph);
			let $case = TestCase::new(&mut inputs);
		};
	}

	fn source_graph(source: &str) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						format!("{STDLIB}\n{source}"),
					)]),
				),
			)
			.unwrap();
		builder.set_stdlib(root_id);
		let graph = builder.build(root_id);
		DiagnosticView::new(
			"parse",
			&graph.collect_parser_diagnostics(),
			&graph.files,
		)
		.assert_no_errors();
		graph
	}

	/// Everything a `TypeContext` borrows, kept on the test's stack.
	struct TestInputs<'g> {
		files: &'g Files,
		strings: &'g mut StringInterner,
		defs: DefinitionRegistry,
		ast_nodes: Vec<AstEntry<'g>>,
		impl_dispatch: ImplDispatch,
		diagnostics: Vec<Diagnostic<FileId>>,
		resolutions: NameResolutions,
	}

	impl<'g> TestInputs<'g> {
		fn new(graph: &'g mut vfs::CompilationUnit) -> Self {
			let vfs::CompilationUnit {
				files,
				packages,
				strings,
				stdlib_package,
				root_package,
			} = graph;
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				packages,
				files,
				strings,
				&mut diagnostics,
				&mut resolutions,
				*stdlib_package,
				*root_package,
			);
			let impl_dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				strings,
				&defs,
				&ast_nodes,
			);
			Self {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			}
		}
	}

	/// A swept `TypeContext` over `TestInputs`.
	struct TestCase<'a> {
		defs: &'a DefinitionRegistry,
		context: TypeContext<'a, 'a, 'a>,
	}

	impl<'a> TestCase<'a> {
		fn new(inputs: &'a mut TestInputs<'_>) -> Self {
			let TestInputs {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			} = inputs;
			let mut context = TypeContext::new(
				diagnostics,
				resolutions,
				strings,
				files,
				defs,
				ast_nodes,
				impl_dispatch,
			);
			context.sweep();
			// The stdlib's own bodies use forms the checker does not cover
			// yet; those reports are not what this suite is about.
			let stdlib_end = STDLIB.len() as u32;
			context.diagnostics.retain(|diagnostic| {
				let in_stdlib =
					diagnostic.labels.first().is_some_and(|label| {
						(label.range.start as u32) < stdlib_end
					});
				!(in_stdlib
					&& diagnostic.code.as_deref()
						== Some(DiagnosticCode::UnsupportedExpression.code()))
			});
			Self { defs, context }
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"eval",
				self.context.diagnostics,
				self.context.files,
			)
		}

		/// What a root-level `name` resolves to in `tier`, by real path
		/// resolution.
		fn resolve(&self, tier: Tier, name: &str) -> DefKind {
			let root = Scope::Package(self.defs.root_package);
			let file_id = self.defs.namespaces.file_id(root.into());
			let segment = ast::PathSegment {
				ident: Spanned {
					inner: self.context.strings.get(name).unwrap(),
					span: TextSpan::new(0, 0),
				},
				type_args: Box::new([]),
			};
			let mut scratch = Vec::new();
			let mut resolutions = NameResolutions::default();
			PathResolver::new(
				&mut scratch,
				&mut resolutions,
				self.context.strings,
				self.defs,
			)
			.resolve_path(file_id, root, &[segment], tier)
			.def_key()
			.unwrap_or_else(|| panic!("expected `{name}` to resolve"))
			.symbol_kind(self.defs)
		}

		fn state(&self, name: &str) -> &ConstValueState {
			let DefKind::Const(index) = self.resolve(Tier::Value, name) else {
				panic!("expected `{name}` to be a constant");
			};
			&self.context.const_values[usize::from(index)]
		}

		fn value(&self, name: &str) -> &[ConstScalar] {
			match self.state(name) {
				ConstValueState::Evaluated(value) => value,
				state => panic!("expected `{name}` to have a value: {state:?}"),
			}
		}

		fn memory(&self, name: &str) -> MemoryIdx {
			let DefKind::Memory(index) = self.resolve(Tier::Value, name) else {
				panic!("expected `{name}` to be a memory");
			};
			index
		}

		/// The allocation an address points into, and the offset there.
		fn pointee(&self, address: ConstScalar) -> (&Allocation, u64) {
			let Val::MemoryOffset { alloc, offset } = address.val else {
				panic!("expected an address, got {address:?}");
			};
			(&self.context.allocations[usize::from(alloc)], offset)
		}
	}

	#[test]
	fn a_string_constant_points_into_an_allocation_of_its_contents() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				const SLICE: heap::&[u8] = "hello";
				const ARRAY: heap::&[u8; 2] = "a\n";
			"#}
		);
		case.diagnostics().assert_none();

		// A slice is its address and its length.
		let [address, length] = case.value("SLICE") else {
			panic!("expected two values");
		};
		assert_eq!(*length, ConstScalar::u32(5));
		assert_eq!(address.scalar, Scalar::U32);
		let (allocation, offset) = case.pointee(*address);
		assert_eq!(offset, 0);
		assert_eq!(
			*allocation,
			Allocation {
				memory: case.memory("heap"),
				align: 1,
				bytes: Box::from(*b"hello"),
				relocations: Box::default(),
			}
		);

		// An array is its address; its length is in its type.
		let [address] = case.value("ARRAY") else {
			panic!("expected one value");
		};
		assert_eq!(&*case.pointee(*address).0.bytes, b"a\n");
	}

	#[test]
	fn an_address_into_a_64_bit_memory_is_64_bits_wide() {
		test_case!(
			case = indoc! {r#"
				memory wide: u64;
				const TEXT: wide::&[u8] = "abc";
			"#}
		);
		case.diagnostics().assert_none();
		let [address, length] = case.value("TEXT") else {
			panic!("expected two values");
		};
		assert!(matches!(address.val, Val::MemoryOffset { offset: 0, .. }));
		assert_eq!(address.scalar, Scalar::U64);
		assert_eq!(*length, ConstScalar::u64(3));
		assert_eq!(case.pointee(*address).0.memory, case.memory("wide"));
	}

	#[test]
	fn a_constant_naming_another_shares_its_allocation() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				const ORIGINAL: heap::&[u8] = "shared";
				const COPY: heap::&[u8] = ORIGINAL;
			"#}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.value("COPY"), case.value("ORIGINAL"));
	}

	#[test]
	fn an_aggregate_holds_an_address_among_its_values() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				struct Text(len: u8, bytes: heap::&[u8]);
				const GREETING: Text = Text(5, "hello");
			"#}
		);
		case.diagnostics().assert_none();
		// In declaration order: the length field, then the slice's address
		// and its length.
		let [len, address, length] = case.value("GREETING") else {
			panic!("expected three values");
		};
		assert_eq!(*len, ConstScalar::u8(5));
		assert_eq!(&*case.pointee(*address).0.bytes, b"hello");
		assert_eq!(*length, ConstScalar::u32(5));
	}

	#[test]
	fn a_pointer_constant_with_no_constant_initializer_is_reported() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				func make() -> heap::&u8 { loop {} }
				const P: heap::&u8 = make();
			"#}
		);
		case.diagnostics()
			.assert_error(DiagnosticCode::NotConstEvaluatable);
	}

	#[test]
	fn a_struct_nested_in_itself_with_other_arguments_is_evaluated() {
		test_case!(
			case = indoc! {r#"
				struct Pair<T>(a: T, b: T);
				const P: Pair<Pair<u8>> = Pair(Pair(1, 2), Pair(3, 4));
			"#}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.value("P"),
			[1, 2, 3, 4].map(ConstScalar::u8).as_slice()
		);
	}

	/// The address and the length of the slice constant `name`, and the
	/// allocation it points to.
	fn slice<'c>(case: &'c TestCase<'_>, name: &str) -> (&'c Allocation, u64) {
		let [address, length] = case.value(name) else {
			panic!("expected `{name}` to be a slice");
		};
		let (allocation, offset) = case.pointee(*address);
		assert_eq!(offset, 0);
		let length = match length.val {
			Val::I32(bits) => u64::from(bits),
			Val::I64(bits) => bits,
			_ => panic!("expected a length"),
		};
		(allocation, length)
	}

	#[test]
	fn an_array_constant_is_its_elements_laid_out() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				struct Mixed(a: u8, b: u32);
				const WORDS: heap::&[u32] = [1, 2, 0x01020304];
				const SIGNED: heap::&[i8] = [-1, 2];
				const FLAGS: heap::&[bool] = [true, false];
				const STRUCTS: heap::&[Mixed; 2] = [Mixed(1, 2), Mixed(3, 4)];
			"#}
		);
		case.diagnostics().assert_none();

		let (words, len) = slice(&case, "WORDS");
		assert_eq!(len, 3);
		assert_eq!(words.align, 4);
		assert_eq!(&*words.bytes, [1, 0, 0, 0, 2, 0, 0, 0, 4, 3, 2, 1]);

		// A narrow signed integer is written at its own width.
		assert_eq!(&*slice(&case, "SIGNED").0.bytes, [0xFF, 2]);
		assert_eq!(&*slice(&case, "FLAGS").0.bytes, [1, 0]);

		// `b` is placed first, then `a`, padded to the struct's alignment.
		let [address] = case.value("STRUCTS") else {
			panic!("expected an array's address");
		};
		let (structs, _) = case.pointee(*address);
		assert_eq!(structs.align, 4);
		assert_eq!(
			&*structs.bytes,
			[2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0]
		);
	}

	#[test]
	fn a_nested_literal_is_an_allocation_its_outer_one_points_to() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				const NESTED: heap::&[heap::&[u8]] = [[1], [2, 3]];
				const NAMES: heap::&[heap::&[u8]] = ["ab", "c"];
			"#}
		);
		case.diagnostics().assert_none();
		for (name, inner) in
			[("NESTED", [&[1u8][..], &[2, 3]]), ("NAMES", [b"ab", b"c"])]
		{
			let (outer, len) = slice(&case, name);
			assert_eq!(len, 2);
			// Each element is a slice: its address (an offset into the
			// inner allocation, 0) and its length.
			let mut bytes = Vec::new();
			for contents in inner {
				bytes.extend(0u32.to_le_bytes());
				bytes.extend((contents.len() as u32).to_le_bytes());
			}
			assert_eq!(&*outer.bytes, bytes.as_slice(), "{name}");
			let offsets: Vec<u32> = outer
				.relocations
				.iter()
				.map(|&(offset, _)| offset)
				.collect();
			assert_eq!(offsets, [0, 8], "{name}");
			for (&(_, alloc), contents) in outer.relocations.iter().zip(inner) {
				assert_eq!(
					&*case.context.allocations[usize::from(alloc)].bytes,
					contents,
					"{name}"
				);
			}
		}
	}

	#[test]
	fn a_repeat_writes_its_value_count_times() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				const SIZE: u32 = 2;
				const SEVENS: heap::&[u16; 3] = [7; 3];
				const ZEROS: heap::&[u8] = [0; SIZE];
				const NINES: heap::&[u8; 2] = [9; _];
			"#}
		);
		case.diagnostics().assert_none();
		let [address] = case.value("NINES") else {
			panic!("expected an array's address");
		};
		assert_eq!(&*case.pointee(*address).0.bytes, [9, 9]);
		let [address] = case.value("SEVENS") else {
			panic!("expected an array's address");
		};
		assert_eq!(&*case.pointee(*address).0.bytes, [7, 0, 7, 0, 7, 0]);
		let (zeros, len) = slice(&case, "ZEROS");
		assert_eq!(len, 2);
		assert_eq!(&*zeros.bytes, [0, 0]);
	}

	#[test]
	fn an_address_in_64_bit_static_data_is_8_bytes_wide() {
		test_case!(
			case = indoc! {r#"
				memory wide: u64;
				const NAMES: wide::&[wide::&[u8]] = ["a"];
			"#}
		);
		case.diagnostics().assert_none();
		let (names, len) = slice(&case, "NAMES");
		assert_eq!(len, 1);
		assert_eq!(names.align, 8);
		let mut bytes = 0u64.to_le_bytes().to_vec();
		bytes.extend(1u64.to_le_bytes());
		assert_eq!(&*names.bytes, bytes.as_slice());
		assert_eq!(names.relocations.len(), 1);
	}

	#[test]
	fn an_element_that_is_not_constant_is_reported() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				func one() -> u8 { 1 }
				const BAD: heap::&[u8] = [1, one()];
			"#}
		);
		case.diagnostics()
			.assert_error(DiagnosticCode::NotConstEvaluatable);
	}

	#[test]
	fn a_cast_to_its_own_type_is_its_value() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				const NUMBER: u8 = 7 as u8;
				const TEXT: heap::&[u8] = "ab" as heap::&[u8];
				const PAIR: heap::&[u8; 2] = [1, 2] as heap::&[u8; 2];
			"#}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.value("NUMBER"), [ConstScalar::u8(7)]);
		let (text, len) = slice(&case, "TEXT");
		assert_eq!((&*text.bytes, len), (&b"ab"[..], 2));
		let [address] = case.value("PAIR") else {
			panic!("expected an array's address");
		};
		assert_eq!(&*case.pointee(*address).0.bytes, [1, 2]);
	}

	#[test]
	fn a_repeat_of_a_zero_sized_value_takes_no_bytes() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				const UNITS: heap::&[()] = [(); 3];
			"#}
		);
		case.diagnostics().assert_none();
		let (units, len) = slice(&case, "UNITS");
		assert_eq!(len, 3);
		assert!(units.bytes.is_empty());
	}

	#[test]
	fn static_data_of_more_than_4_gib_is_reported() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				const BIG: heap::&[u64] = [0; 1000000000];
			"#}
		);
		case.diagnostics()
			.assert_error(DiagnosticCode::ConstEvaluationFailed);
	}
}
