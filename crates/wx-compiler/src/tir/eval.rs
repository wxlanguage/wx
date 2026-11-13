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
//! A constant's value is a memoized query of the solver (`Solver::const_value`),
//! and evaluation asks it on demand: a constant is read when the node naming it
//! is evaluated, so a branch that is not taken reads nothing. Like an impl
//! member's value (`Verdict`), a constant owns the failures of its own
//! evaluation: the body phase reports them, and a constant that reads a failed
//! one fails silently. An evaluation is a frame on the solver's stack, so a loop
//! through constants is read from the same stack as a loop through projections,
//! and is owned by its first-defined member: it is reported once whichever
//! constant is asked first. The solver reads bodies and builds none: every
//! constant body is built before anything evaluates
//! (`Semantics::build_constant_bodies`).
//!
//! A constant with parameters (a trait's, an impl's with arguments) has a
//! value per instance, the constant with its arguments (`Instance`): its body
//! is checked once and evaluated per instance with the arguments substituted,
//! and a trait's declaration reads the member of the impl its `Self` selects,
//! or the default the impl inherits (`resolve_constant`). No sweep reaches an
//! instance, so its failure is reported by the reader that first asks for it.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use super::body::{
	Body, ConstBody, ElementOrder, ExprIdx, ExprKind, ExprRange,
	FunctionImplementation,
};
use super::bounds::AssumptionEnvIdx;
use super::decls::{
	ConstIdx, EnumIdx, FunctionIdx, GlobalIdx, MemberKind, MemberOwner,
	MemoryIdx,
};
use super::literals::ConcreteType;
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::numbers::DecimalFloat;
use super::signatures::Semantics;
use super::solver::{
	NormalizationDepth, RewriteFlags, Solver, SolverError, SolverFrame,
	metadata_len,
};
use super::types::{
	GenericEnvIdx, Primitive, Substitution, Type, TypeIndex, TypeList,
};
use crate::ast::{BinaryOp, StringInterner, UnaryOp};
use crate::diagnostics::{DiagnosticCode, Diagnostics, SourceSpan, TextSpan};
use crate::index::index_newtype;

index_newtype!(AllocIdx);

/// A Wasm value, as its bits. An address into linear memory has no bits
/// yet: it is an offset into an allocation, and its number is known once
/// the allocation is placed in its memory.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Val {
	I32(u32),
	I64(u64),
	F32(u32),
	F64(u64),
	// V128(u128),
	/// As wide as its allocation's memory's `Size`.
	MemoryOffset {
		alloc: AllocIdx,
		offset: u64,
	},
	/// `Memory::DATA_END`: the address right after `memory`'s static data,
	/// known once the program's data is laid out. As wide as the memory's
	/// `Size`.
	DataEnd {
		memory: MemoryIdx,
	},
}

/// What an address written in an allocation's bytes points at.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum AddressTarget {
	/// The bytes hold the offset into the allocation.
	Allocation(AllocIdx),
	/// The memory's data end; the bytes hold zero.
	DataEnd(MemoryIdx),
}

/// Bytes a constant's value points into, placed in `memory`'s data when
/// the program is laid out. Constant evaluation creates them (a string
/// literal's contents) and never writes them afterwards.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct Allocation {
	pub(super) memory: MemoryIdx,
	pub(super) align: u32,
	pub(super) bytes: Box<[u8]>,
	/// The addresses written in `bytes`, sorted by offset, with what each
	/// points at.
	pub(super) relocations: Box<[(u32, AddressTarget)]>,
}

/// One number of a constant's value: a Wasm number and the scalar it means.
/// A narrow integer is an `I32`; a signed one is held
/// sign-extended. Built and read only through one constructor and one
/// `expect_*` reader per scalar, the one place each scalar's holding is
/// written.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub struct ConstScalar {
	pub val: Val,
	pub scalar: Primitive,
}

/// A constant's value: its numbers, in declaration order.
pub(super) type ConstValue = Box<[ConstScalar]>;

/// Why evaluating a body failed, at the node that failed.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct EvalError {
	pub(super) span: TextSpan,
	pub(super) kind: EvalErrorKind,
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum EvalErrorKind {
	/// The node is not a constant expression.
	NotConst,
	/// Precision-independent floating arithmetic is not implemented yet.
	UnsupportedFloatArithmetic,
	/// The result is not representable as the operand type, or a shift amount
	/// is outside its width.
	Overflow(Operation),
	DivisionByZero,
	RemainderByZero,
	/// Static data takes more bytes than an allocation holds.
	TooLarge,
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Operation {
	Binary(BinaryOp),
	Negate,
}

/// The value query's state for one constant.
#[derive(Clone, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum ConstValueState {
	/// Its body is built but not checked: what building it recorded is not
	/// decided. Asking for its value checks it first (`check_constant`), and a
	/// body that reported an error is never evaluated.
	Unchecked,
	/// Checked without an error, and not evaluated yet.
	Checked,
	/// Being checked or evaluated; asking for it again closes a loop.
	InProgress,
	Evaluated(ConstValue),
	/// The value of an untyped constant (`const X: const_int`): a number of
	/// its kind, exact, with no type until a use gives it one
	/// (`Semantics::exact_value`).
	Exact(i128),
	/// Exact decimal value and sign, with no concrete precision yet.
	FloatLiteral(DecimalFloat),
	/// Not evaluated at all: the evaluator holds no values of its type
	/// (`check_value_type`), or it has no initializer. A constant that reads
	/// it is not a constant expression.
	NoValue,
	/// No value, and the failure is reported elsewhere: it derives from
	/// another constant's failure or from an error in its signature.
	Poisoned,
	/// No value; this constant owns the error and its check reports it.
	Failed(EvalError),
}

impl ConstValueState {
	/// What a reader of the constant learns, once the state is final.
	fn answer(&self) -> Option<Result<&[ConstScalar], Unevaluable>> {
		match self {
			Self::Unchecked | Self::Checked | Self::InProgress => None,
			Self::Evaluated(value) => Some(Ok(value)),
			// Read as a number of a type only through `exact_value`, by the
			// use that gives it one.
			Self::NoValue | Self::Exact(_) | Self::FloatLiteral(_) => {
				Some(Err(Unevaluable::NoValue))
			}
			Self::Poisoned | Self::Failed(_) => Some(Err(Unevaluable::Silent)),
		}
	}
}

/// The bits of a value of one integer number; `None` for any other value.
pub(super) fn value_bits(value: &[ConstScalar]) -> Option<u64> {
	match value {
		[scalar] => match scalar.val {
			Val::I32(bits) => Some(u64::from(bits)),
			Val::I64(bits) => Some(bits),
			Val::F32(_)
			| Val::F64(_)
			| Val::MemoryOffset { .. }
			| Val::DataEnd { .. } => None,
		},
		_ => None,
	}
}

/// Why `const_value` has no value for its caller.
pub(super) enum Unevaluable {
	/// The constant has no compile-time value; reading it is the reader's
	/// error.
	NoValue,
	/// Reported, or to be reported, by whoever owns it; the caller is silent.
	Silent,
}

/// Why evaluating a node gave no value.
enum Halt {
	/// The constant being evaluated fails here; it owns the failure.
	Own(EvalError),
	/// Reported, or to be reported, by whoever owns it.
	Silent,
}

/// A constant with the type arguments its body is read with: its impl's, or
/// `Self` for a trait's default. `args` is the list of the interned
/// `Type::ConstRef`, so equal instances are equal; empty for a constant with no
/// parameters, which is its own one instance.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct Instance {
	pub(super) constant: ConstIdx,
	args: TypeList,
}

impl Instance {
	pub(super) fn of(constant: ConstIdx) -> Self {
		Self {
			constant,
			args: TypeList::EMPTY,
		}
	}
}

/// One piece of a function body's static data (a string or array literal,
/// or a constant holding data in no memory, placed) for one instance of the
/// function: its arguments are interned as the function's item type's, so
/// equal instances are equal.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct StaticInstance {
	function: FunctionIdx,
	args: TypeList,
	expr: ExprIdx,
}

/// The body evaluated, with its instance's arguments.
#[derive(Clone, Copy)]
struct Owner<'a> {
	body: Evaluated,
	args: &'a [TypeIndex],
}

/// Whose body is evaluated: a constant's, a global's initializer, which
/// must be a constant expression and has no parameters, or a function's,
/// of which only static data is.
#[derive(Clone, Copy)]
enum Evaluated {
	Constant(ConstIdx),
	Global(GlobalIdx),
	Function(FunctionIdx),
}

/// What a constant named with arguments reads.
pub(super) enum ResolvedConstant {
	/// This instance's value.
	Instance(Instance),
	/// `Array::SIZE`: the array type's length.
	Length(TypeIndex),
	/// `Memory::DATA_END` of a declared memory, which its synthetic impl
	/// does not hold: it is known once the program's data is laid out.
	DataEnd(MemoryIdx),
	/// A trait's declaration whose `Self` is not known here.
	Abstract,
}

/// The checked body `owner` evaluates, as built.
fn body_of<'a>(sema: &'a Semantics, owner: Owner<'_>) -> &'a Body {
	match owner.body {
		Evaluated::Constant(const_index) => {
			match sema.const_bodies[usize::from(const_index)] {
				ConstBody::Built(body) => sema.body(body),
				_ => unreachable!("an evaluated constant's body is built"),
			}
		}
		Evaluated::Global(global_index) => sema.body(
			sema.global_bodies[usize::from(global_index)]
				.expect("an evaluated global's body is built"),
		),
		Evaluated::Function(function_index) => {
			match sema.function_implementations[usize::from(function_index)] {
				FunctionImplementation::Defined(body) => sema.body(body),
				_ => unreachable!("an evaluated function's body is checked"),
			}
		}
	}
}

/// The type scope `owner`'s body is checked in: a global's is the root.
fn body_env(sema: &Semantics, owner: Owner<'_>) -> GenericEnvIdx {
	match owner.body {
		Evaluated::Constant(const_index) => {
			sema.constants[usize::from(const_index)].env
		}
		Evaluated::Global(_) => GenericEnvIdx::ROOT,
		Evaluated::Function(function_index) => {
			sema.functions[usize::from(function_index)].type_params
		}
	}
}

/// The file `owner`'s body is written in.
fn body_file(sema: &Semantics, owner: Owner<'_>) -> crate::vfs::FileId {
	match owner.body {
		Evaluated::Constant(const_index) => sema
			.decls
			.file_id(sema.decls.constants[usize::from(const_index)].loc),
		Evaluated::Global(global_index) => sema
			.decls
			.file_id(sema.decls.globals[usize::from(global_index)].loc),
		Evaluated::Function(function_index) => sema
			.decls
			.file_id(sema.decls.functions[usize::from(function_index)].loc),
	}
}

impl Semantics {
	/// Evaluates a constant in the body phase, and reports what it owns. One
	/// with parameters is only checked: its instances are evaluated, and
	/// reported, where they are read.
	pub(super) fn evaluate_constant(
		&mut self,
		strings: &StringInterner,
		const_index: ConstIdx,
	) {
		let env = self.constants[usize::from(const_index)].env;
		if self.generic_envs.generic_count(env) > 0 {
			if self.solver.const_values[usize::from(const_index)]
				== ConstValueState::Unchecked
			{
				self.check_constant(strings, const_index);
			}
			return;
		}
		let _ = self.const_value(strings, const_index);
		let diagnostic =
			match &self.solver.const_values[usize::from(const_index)] {
				ConstValueState::Failed(error) => self.report_eval_failure(
					strings,
					Instance::of(const_index),
					error,
					None,
				),
				_ => return,
			};
		self.diagnostics.push(diagnostic);
	}

	/// Evaluates a global's initializer, which must be a constant
	/// expression, into `global_values`, and reports a failure. Called once
	/// its body is checked without an error. A global reads no other global
	/// (reading one is a call of `Global::get`, which is not constant), so
	/// no loop can pass through it and it needs no frame of its own.
	pub(super) fn evaluate_global(
		&mut self,
		strings: &StringInterner,
		global_index: GlobalIdx,
	) {
		let owner = Owner {
			body: Evaluated::Global(global_index),
			args: &[],
		};
		let root = body_of(self, owner).root();
		let ty = self.global_value_type(global_index);
		let mut scalars = Vec::new();
		// A value type of other than one Wasm value is reported by the type's
		// check (`Global::Value`'s bounds).
		if self
			.push_scalars(
				strings,
				AssumptionEnvIdx::ROOT,
				ty,
				&mut scalars,
				&mut Vec::new(),
			)
			.is_err() || scalars.len() != 1
		{
			return;
		}
		let mut stack = Vec::new();
		match self.eval(strings, owner, root, &mut stack) {
			Ok(()) if stack.iter().map(|value| value.scalar).eq(scalars) => {
				self.global_values[usize::from(global_index)] =
					Some(stack.into_boxed_slice());
			}
			Ok(()) | Err(Halt::Silent) => {}
			Err(Halt::Own(error)) => {
				let diagnostic =
					self.report_global_failure(strings, global_index, &error);
				self.diagnostics.push(diagnostic);
			}
		}
	}

	/// The value of the static data `expr` of `function`'s body (one of
	/// `Body::statics`) for the instance with the concrete `args`: placed, a
	/// pointer to its data. Memoized per instance; a failure is reported by
	/// the first reader and is `None` to every reader after it. The check
	/// pass reads a function with no parameters, and lowering every instance,
	/// so a failure that depends on the arguments is reported where the
	/// instance is lowered.
	pub(super) fn static_value(
		&mut self,
		strings: &StringInterner,
		function: FunctionIdx,
		args: &[TypeIndex],
		expr: ExprIdx,
	) -> Option<&[ConstScalar]> {
		let args = if args.is_empty() {
			TypeList::EMPTY
		} else {
			let item = self.types.intern_function(function, args);
			let Type::Function { type_args, .. } = *self.types.resolve(item)
			else {
				unreachable!("a function interns as a `Type::Function`")
			};
			type_args
		};
		let key = StaticInstance {
			function,
			args,
			expr,
		};
		if !self.solver.static_values.contains_key(&key) {
			let value = self.evaluate_static(strings, key);
			self.solver.static_values.insert(key, value);
		}
		self.solver.static_values[&key].as_deref()
	}

	/// Pushes the value of a function's static data `expr`; its failure is
	/// its query's to report.
	fn push_static_value(
		&mut self,
		strings: &StringInterner,
		function: FunctionIdx,
		args: &[TypeIndex],
		expr: ExprIdx,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let value = self
			.static_value(strings, function, args, expr)
			.ok_or(Halt::Silent)?;
		stack.extend_from_slice(value);
		Ok(())
	}

	/// Evaluates `key`'s static data, reporting what fails in it.
	fn evaluate_static(
		&mut self,
		strings: &StringInterner,
		key: StaticInstance,
	) -> Option<ConstValue> {
		let args: Box<[TypeIndex]> = self.types.list(key.args).into();
		let owner = Owner {
			body: Evaluated::Function(key.function),
			args: &args,
		};
		let ty = self.instance_type(
			strings,
			owner,
			body_of(self, owner).ty(key.expr),
		);
		let mut stack = Vec::new();
		// Placed: a literal, or a constant holding one (`place_data`); not
		// placed (an element of an enclosing array), only its elements.
		let placed = match self.types.resolve(ty) {
			Type::Error => return None,
			Type::Pointer { .. } => true,
			_ => false,
		};
		let result = if placed {
			self.place_data(strings, owner, key.expr, ty, &mut stack)
		} else {
			self.eval_static(strings, owner, key.expr, ty, &mut stack)
		};
		match result {
			Ok(()) => Some(stack.into_boxed_slice()),
			Err(Halt::Silent) => None,
			Err(Halt::Own(error)) => {
				let file_id = body_file(self, owner);
				let diagnostic = report_static_failure(file_id, &error);
				self.diagnostics.push(diagnostic);
				None
			}
		}
	}

	fn report_global_failure(
		&self,
		strings: &StringInterner,
		global_index: GlobalIdx,
		error: &EvalError,
	) -> Diagnostic<crate::vfs::FileId> {
		let decl = &self.decls.globals[usize::from(global_index)];
		let name = strings
			.resolve(self.decls.item(decl.loc).name.inner)
			.unwrap_or("?");
		let site = SourceSpan::new(self.decls.file_id(decl.loc), error.span);
		let (code, message) = match error.kind {
			EvalErrorKind::NotConst => (
				DiagnosticCode::NonConstantGlobalInitializer,
				format!(
					"the initializer of global `{name}` cannot be evaluated \
					 at compile time"
				),
			),
			_ => (
				error.kind.code(),
				format!("evaluation of global `{name}` failed"),
			),
		};
		Diagnostic::error()
			.with_code(code.code())
			.with_message(message)
			.with_label(site.primary_label().with_message(error.kind.label()))
			.with_note(
				"a global's initializer is evaluated at compile time; the \
				 module holds its value",
			)
	}

	/// Checks a constant's body: decides what building it recorded, reading
	/// the values of the constants those name, which are checked on demand the
	/// same way. A body that reported an error, building or here, is never
	/// evaluated: its constant is `Poisoned`, and so is every reader. Reading
	/// the constant while it is checked closes a loop (`const_cycle`).
	pub(super) fn check_constant(
		&mut self,
		strings: &StringInterner,
		const_index: ConstIdx,
	) {
		let at = usize::from(const_index);
		debug_assert!(matches!(
			self.solver.const_values[at],
			ConstValueState::Unchecked
		));
		debug_assert!(self.solver.state.blocked_at.is_none());
		self.solver.const_values[at] = ConstValueState::InProgress;
		self.solver.state.frames.push(SolverFrame::Evaluation {
			instance: Instance::of(const_index),
			outer_budget: std::mem::replace(
				&mut self.solver.state.recursion_budget,
				self.solver.recursion_limit,
			),
		});
		let reported = self.diagnostics.len();
		self.decide_obligations(strings, const_index);
		let clean = !self.diagnostics[reported..].has_errors();
		let Some(SolverFrame::Evaluation { outer_budget, .. }) =
			self.solver.state.frames.pop()
		else {
			unreachable!("the check is the innermost frame once it is done")
		};
		self.solver.state.recursion_budget = outer_budget;
		let state = if clean {
			ConstValueState::Checked
		} else {
			ConstValueState::Poisoned
		};
		self.solver
			.set_const_state(Instance::of(const_index), state);
	}

	/// The bits of `instance`'s one number, as a type means it; `None` when
	/// it has no such value, which its check or the site naming it reports.
	pub(super) fn instance_bits(
		&mut self,
		strings: &StringInterner,
		instance: Instance,
	) -> Option<u64> {
		// An untyped constant is a count where a type reads it.
		if self.constants[usize::from(instance.constant)]
			.ty
			.is_const_kind()
		{
			return self
				.exact_value(strings, instance.constant)
				.ok()
				.and_then(|value| u64::try_from(value).ok());
		}
		self.instance_value(strings, instance, None)
			.ok()
			.and_then(value_bits)
	}

	/// The value of an untyped constant (`const X: const_int`), memoized and
	/// read on the solver's stack as any constant's is. `Err` as
	/// `const_value`'s.
	pub(super) fn exact_value(
		&mut self,
		strings: &StringInterner,
		const_index: ConstIdx,
	) -> Result<i128, Unevaluable> {
		let instance = Instance::of(const_index);
		if let Err(Unevaluable::Silent) =
			self.instance_value(strings, instance, None)
		{
			return Err(Unevaluable::Silent);
		}
		match *self.solver.const_state(instance) {
			ConstValueState::Exact(value) => Ok(value),
			ConstValueState::NoValue => Err(Unevaluable::NoValue),
			_ => Err(Unevaluable::Silent),
		}
	}

	/// A `const_float` instance's exact decimal value, with no default
	/// precision. Only its typed use converts that value to f32 or f64.
	pub(super) fn float_value(
		&mut self,
		strings: &StringInterner,
		instance: Instance,
	) -> Result<DecimalFloat, Unevaluable> {
		if let Err(Unevaluable::Silent) =
			self.instance_value(strings, instance, None)
		{
			return Err(Unevaluable::Silent);
		}
		match *self.solver.const_state(instance) {
			ConstValueState::FloatLiteral(value) => Ok(value),
			ConstValueState::NoValue => Err(Unevaluable::NoValue),
			_ => Err(Unevaluable::Silent),
		}
	}

	/// A constant's value as a pattern compares with it: the bits of its one
	/// Wasm number (a narrow signed integer sign-extended, as it is held).
	/// `None` when it is more than one number.
	pub(super) fn constant_bits(
		&mut self,
		strings: &StringInterner,
		const_index: ConstIdx,
	) -> Result<Option<u64>, Unevaluable> {
		self.const_value(strings, const_index).map(value_bits)
	}

	/// Reports each set of an enum's variants that share a value, once, on the
	/// enum. A variant without a value reports itself and is left out.
	pub(super) fn check_discriminants(
		&mut self,
		strings: &StringInterner,
		enum_index: EnumIdx,
	) {
		let enum_decl = &self.decls.enums[usize::from(enum_index)];
		let (file_id, name_span) = (
			self.decls.file_id(enum_decl.loc),
			self.decls.item(enum_decl.loc).name.span,
		);
		let (run, open) = (enum_decl.variants.clone(), enum_decl.open);
		let mut values = Vec::new();
		for variant in u32::from(run.start)..u32::from(run.end) {
			let variant = ConstIdx::new(variant);
			if let Ok(&[value]) = self.const_value(strings, variant) {
				values.push((value, variant));
			}
		}
		// An open enum whose variants already name every value of its repr has
		// nothing left for its `..` to admit.
		if let Some(open) = open
			&& values.len() as u32 == u32::from(run.end) - u32::from(run.start)
		{
			let bits: u32 = match self.enum_repr(enum_index) {
				TypeIndex::U8 | TypeIndex::I8 => 8,
				TypeIndex::U16 | TypeIndex::I16 => 16,
				TypeIndex::U32 | TypeIndex::I32 => 32,
				_ => 64,
			};
			let mut distinct: Vec<u64> = values
				.iter()
				.map(|(value, _)| match value.val {
					Val::I32(bits) => u64::from(bits),
					Val::I64(bits) => bits,
					_ => unreachable!("an enum's repr is an integer"),
				})
				.collect();
			distinct.sort_unstable();
			distinct.dedup();
			if distinct.len() as u128 == 1u128 << bits {
				self.diagnostics.push(
					Diagnostic::warning()
						.with_code(DiagnosticCode::RedundantOpenMarker.code())
						.with_message("this `..` is redundant")
						.with_label(
							SourceSpan::new(file_id, open)
								.primary_label()
								.with_message(
									"the variants already name every value of \
									 the repr",
								),
						),
				);
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

	/// An instance as a path names it (`<P as Tr>::X`).
	fn instance_name(
		&self,
		strings: &StringInterner,
		instance: Instance,
	) -> String {
		self.type_formatter(strings)
			.display_constant(instance.constant, self.types.list(instance.args))
	}

	/// A constant's failure, at the node that failed. An instance's is
	/// reported by its first reader, `used_at`.
	fn report_eval_failure(
		&self,
		strings: &StringInterner,
		instance: Instance,
		error: &EvalError,
		used_at: Option<SourceSpan>,
	) -> Diagnostic<crate::vfs::FileId> {
		let decl = &self.decls.constants[usize::from(instance.constant)];
		let site = SourceSpan::new(self.decls.file_id(decl.loc), error.span);
		let name = self.instance_name(strings, instance);
		let message = match error.kind {
			EvalErrorKind::NotConst => {
				format!("`{name}` cannot be evaluated at compile time")
			}
			_ => format!("evaluation of constant `{name}` failed"),
		};
		let mut diagnostic = Diagnostic::error()
			.with_code(error.kind.code().code())
			.with_message(message)
			.with_label(site.primary_label().with_message(error.kind.label()));
		if let Some(used_at) = used_at {
			diagnostic =
				diagnostic.with_label(used_at.secondary_label().with_message(
					format!("`{name}` is evaluated for this use"),
				));
		}
		diagnostic
	}

	fn report_const_cycle(
		&self,
		strings: &StringInterner,
		cycle: &[Instance],
	) -> Diagnostic<crate::vfs::FileId> {
		let decl = &self.decls.constants[usize::from(cycle[0].constant)];
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::CyclicConstant.code())
			.with_message(format!(
				"cycle detected when evaluating constant `{}`",
				self.instance_name(strings, cycle[0])
			))
			.with_label(self.decls.declaration_span(decl.loc).primary_label());
		for (at, &member) in cycle.iter().enumerate() {
			let next = cycle[(at + 1) % cycle.len()];
			let member_decl =
				&self.decls.constants[usize::from(member.constant)];
			diagnostic = diagnostic.with_label(
				self.decls
					.declaration_span(member_decl.loc)
					.secondary_label()
					.with_message(format!(
						"`{}` requires evaluating `{}`",
						self.instance_name(strings, member),
						self.instance_name(strings, next)
					)),
			);
		}
		diagnostic
	}
}

impl Semantics {
	/// An evaluated constant's numbers, in declaration order. `None` when it
	/// has not been evaluated (or has no compile-time value).
	pub fn constant_value(&self, constant: ConstIdx) -> Option<&[ConstScalar]> {
		match &self.solver.const_values[usize::from(constant)] {
			ConstValueState::Evaluated(value) => Some(value),
			_ => None,
		}
	}
}

impl Solver {
	fn const_state(&self, instance: Instance) -> &ConstValueState {
		if instance.args.is_empty() {
			&self.const_values[usize::from(instance.constant)]
		} else {
			self.instance_values
				.get(&instance)
				.unwrap_or(&ConstValueState::Checked)
		}
	}

	fn const_state_mut(&mut self, instance: Instance) -> &mut ConstValueState {
		if instance.args.is_empty() {
			&mut self.const_values[usize::from(instance.constant)]
		} else {
			self.instance_values
				.entry(instance)
				.or_insert(ConstValueState::Checked)
		}
	}

	/// Records the final state of a constant, unless a loop through it
	/// already poisoned it while it was checked or evaluated.
	fn set_const_state(&mut self, instance: Instance, state: ConstValueState) {
		let slot = self.const_state_mut(instance);
		if !matches!(slot, ConstValueState::Poisoned) {
			*slot = state;
		}
	}

	/// `instance` was asked for again while it is evaluated: the loop is
	/// the constants evaluated on the stack from its own evaluation, read
	/// from its first-defined member: each requires the next, and the last
	/// requires the first.
	fn const_cycle(&mut self, instance: Instance) -> Box<[Instance]> {
		let start = self
			.state
			.frames
			.iter()
			.position(|frame| {
				matches!(frame, SolverFrame::Evaluation { instance: on, .. } if *on == instance)
			})
			.expect("an in-progress constant is on the stack");
		self.state.lowest_frame_read = self.state.lowest_frame_read.min(start);
		let mut members: Vec<Instance> = self.state.frames[start..]
			.iter()
			.filter_map(|frame| match *frame {
				SolverFrame::Evaluation { instance, .. } => Some(instance),
				_ => None,
			})
			.collect();
		let owner = (0..members.len())
			.min_by_key(|&at| usize::from(members[at].constant))
			.unwrap();
		members.rotate_left(owner);
		members.into_boxed_slice()
	}
}

impl Semantics {
	/// The memoized value of a constant, evaluated on first use. The
	/// evaluation is a frame on the solver's own stack, with a budget of its
	/// own, as an impl member's judgement is: reaching the constant again
	/// while it is evaluated closes a loop, read from that stack. Its body
	/// must be built.
	pub(super) fn const_value(
		&mut self,
		strings: &StringInterner,
		const_index: ConstIdx,
	) -> Result<&[ConstScalar], Unevaluable> {
		self.instance_value(strings, Instance::of(const_index), None)
	}

	/// The memoized value of `instance`, as `const_value`. An instance of a
	/// constant with parameters is evaluated once its constant is checked,
	/// with its arguments substituted, and its failure is reported by the
	/// reader that first asks for it, `used_at`.
	pub(super) fn instance_value(
		&mut self,
		strings: &StringInterner,
		instance: Instance,
		used_at: Option<SourceSpan>,
	) -> Result<&[ConstScalar], Unevaluable> {
		let const_index = instance.constant;
		if self.solver.const_values[usize::from(const_index)]
			== ConstValueState::Unchecked
		{
			self.check_constant(strings, const_index);
		}
		if !instance.args.is_empty() {
			match self.solver.const_values[usize::from(const_index)] {
				ConstValueState::Poisoned => return Err(Unevaluable::Silent),
				// Read while its constant is checked.
				ConstValueState::InProgress => {
					return Err(self
						.close_const_loop(strings, Instance::of(const_index)));
				}
				_ => {}
			}
		}
		match self.solver.const_state(instance) {
			ConstValueState::Unchecked => {
				unreachable!("a constant is checked before it is read")
			}
			ConstValueState::Checked => {}
			ConstValueState::InProgress => {
				return Err(self.close_const_loop(strings, instance));
			}
			_ => {
				return self
					.solver
					.const_state(instance)
					.answer()
					.expect("a state past evaluation is final");
			}
		}
		let root = match self.const_bodies[usize::from(const_index)] {
			ConstBody::Built(body) => self.body(body).root(),
			// A required trait constant, with no initializer at all. An
			// instance reads one only for an impl missing it, which
			// conformance reports.
			ConstBody::Missing => {
				let state = if instance.args.is_empty() {
					ConstValueState::NoValue
				} else {
					ConstValueState::Poisoned
				};
				return self.settle_constant(strings, instance, state, used_at);
			}
			ConstBody::NotBuilt => {
				unreachable!("every constant body is built before it evaluates")
			}
		};
		// In progress before its declared type is read: the type may name
		// the constant itself (`const A: heap::&[u8; A]`).
		*self.solver.const_state_mut(instance) = ConstValueState::InProgress;
		self.solver.state.frames.push(SolverFrame::Evaluation {
			instance,
			outer_budget: std::mem::replace(
				&mut self.solver.state.recursion_budget,
				self.solver.recursion_limit,
			),
		});
		let args: Box<[TypeIndex]> = self.types.list(instance.args).into();
		let owner = Owner {
			body: Evaluated::Constant(const_index),
			args: &args,
		};
		// An untyped constant's value is one exact number of its kind.
		let declared = self.constants[usize::from(const_index)].ty;
		let untyped = declared.is_const_kind();
		let scalars = if untyped {
			Ok(Vec::new())
		} else {
			self.constant_scalars(strings, const_index, owner)
		};
		let mut stack = Vec::new();
		let mut exact = None;
		let mut float_literal = None;
		let evaluated = match &scalars {
			Ok(_) if declared == TypeIndex::CONST_FLOAT => self
				.eval_untyped_float(strings, owner, root)
				.map(|value| float_literal = Some(value)),
			Ok(_) if untyped => self
				.eval_exact(strings, owner, root)
				.map(|value| exact = Some(value)),
			Ok(_) => self.eval(strings, owner, root, &mut stack),
			Err(_) => Ok(()),
		};
		let Some(SolverFrame::Evaluation { outer_budget, .. }) =
			self.solver.state.frames.pop()
		else {
			unreachable!(
				"the evaluation is the innermost frame once it is done"
			)
		};
		self.solver.state.recursion_budget = outer_budget;
		let scalars = match scalars {
			Ok(scalars) => scalars,
			Err(state) => {
				return self.settle_constant(strings, instance, state, used_at);
			}
		};

		let state = match evaluated {
			Ok(()) if let Some(value) = float_literal => {
				ConstValueState::FloatLiteral(value)
			}
			Ok(()) if let Some(value) = exact => ConstValueState::Exact(value),
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
		};
		self.settle_constant(strings, instance, state, used_at)
	}

	/// Records the final state of `instance` and answers its reader with it.
	/// The failure of an instance of a constant with parameters is reported
	/// here, by its first reader: no sweep reaches it.
	fn settle_constant(
		&mut self,
		strings: &StringInterner,
		instance: Instance,
		state: ConstValueState,
		used_at: Option<SourceSpan>,
	) -> Result<&[ConstScalar], Unevaluable> {
		self.solver.set_const_state(instance, state);
		if !instance.args.is_empty()
			&& let ConstValueState::Failed(error) =
				self.solver.const_state(instance)
		{
			let diagnostic =
				self.report_eval_failure(strings, instance, error, used_at);
			self.diagnostics.push(diagnostic);
		}
		self.solver
			.const_state(instance)
			.answer()
			.expect("a settled state is final")
	}

	/// Reports the loop `instance`, asked for again while it is checked or
	/// evaluated, closes, once, against its first-defined member. Its members
	/// are poisoned, so every later reader, and the members' own checks and
	/// evaluations, fail silently.
	fn close_const_loop(
		&mut self,
		strings: &StringInterner,
		instance: Instance,
	) -> Unevaluable {
		let cycle = self.solver.const_cycle(instance);
		let diagnostic = self.report_const_cycle(strings, &cycle);
		self.diagnostics.push(diagnostic);
		for &member in &*cycle {
			*self.solver.const_state_mut(member) = ConstValueState::Poisoned;
		}
		Unevaluable::Silent
	}

	/// The values of a tuple's `elements`, evaluated in written order and
	/// held in the positions `order` gives them.
	fn eval_ordered(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		elements: ExprRange,
		order: ElementOrder,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let ElementOrder::Permuted { .. } = order else {
			for at in 0..elements.len() {
				let arg = body_of(self, owner).args(elements)[at];
				self.eval(strings, owner, arg, stack)?;
			}
			return Ok(());
		};
		let start = stack.len();
		let mut declared = Vec::with_capacity(elements.len());
		for at in 0..elements.len() {
			let body = body_of(self, owner);
			let (arg, index) =
				(body.args(elements)[at], body.declared_index(order, at));
			let arg_start = stack.len();
			self.eval(strings, owner, arg, stack)?;
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
		strings: &StringInterner,
		owner: Owner<'_>,
		expr: ExprIdx,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let body = body_of(self, owner);
		let (kind, ty, span) =
			(body.kind(expr), body.ty(expr), body.span(expr));
		let ty = self.instance_type(strings, owner, ty);
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
			ExprKind::Int(value) => match Primitive::of(ty) {
				Some(scalar) => {
					stack.push(literal(value, false, scalar).expect(
						"the checker keeps a literal in its type's range",
					))
				}
				None => return Err(own(EvalErrorKind::NotConst)),
			},
			ExprKind::Float(literal) => {
				let value = self
					.read_float_literal(literal, ConcreteType::Target(ty))
					.ok()
					.ok_or(own(EvalErrorKind::NotConst))?;
				stack.push(match Primitive::of(ty) {
					Some(Primitive::F32) => ConstScalar::f32(value as f32),
					Some(Primitive::F64) => ConstScalar::f64(value),
					_ => return Err(own(EvalErrorKind::NotConst)),
				});
			}
			// A function item and a global's or a memory's handle are
			// zero-sized: the type says everything.
			ExprKind::Function { .. }
			| ExprKind::Global(_)
			| ExprKind::Memory(_) => {}
			// A function's static data is evaluated once per instance, by
			// its query.
			ExprKind::String(_)
			| ExprKind::Array { .. }
			| ExprKind::ArrayRepeat { .. }
				if let Evaluated::Function(function) = owner.body =>
			{
				self.push_static_value(
					strings, function, owner.args, expr, stack,
				)?;
			}
			ExprKind::String(_)
			| ExprKind::Array { .. }
			| ExprKind::ArrayRepeat { .. } => {
				self.eval_static(strings, owner, expr, ty, stack)?;
			}
			// A constant holding data in no memory, placed here: a copy of
			// its data in the memory `ty` names.
			ExprKind::Const { constant, .. }
				if matches!(self.types.resolve(ty), Type::Pointer { .. })
					&& self.types.is_unplaced(
						self.constants[usize::from(constant)].ty,
					) =>
			{
				if let Evaluated::Function(function) = owner.body {
					self.push_static_value(
						strings, function, owner.args, expr, stack,
					)?;
				} else {
					self.place_data(strings, owner, expr, ty, stack)?;
				}
			}
			// Data in no memory has no value of its own; as an element of
			// other data it is its elements, read from its body as each
			// placed use reads it.
			ExprKind::Const { constant, .. }
				if self
					.types
					.is_unplaced(self.constants[usize::from(constant)].ty) =>
			{
				let root = match self.const_bodies[usize::from(constant)] {
					ConstBody::Built(body) => self.body(body).root(),
					// Reported where the constant is.
					_ => return Err(Halt::Silent),
				};
				let owner = Owner {
					body: Evaluated::Constant(constant),
					args: &[],
				};
				self.eval(strings, owner, root, stack)?;
			}
			ExprKind::Char(value) => stack.push(ConstScalar::char(value)),
			ExprKind::Const {
				constant,
				type_args,
			}
			| ExprKind::AbstractConst {
				constant,
				type_args,
			} => {
				let args: Vec<TypeIndex> = (0..type_args.len())
					.map(|at| {
						let arg = self.generic_args.types(type_args)[at];
						self.instance_type(strings, owner, arg)
					})
					.collect();
				self.read_reference(
					strings, owner, constant, &args, ty, span, stack,
				)?;
			}
			ExprKind::NextDiscriminant(previous) => {
				self.read_constant(
					strings,
					Instance::of(previous),
					None,
					span,
					stack,
				)?;
				let previous = stack.pop().expect("a variant's value");
				let one = literal(1, false, previous.scalar)
					.expect("an enum's repr holds one");
				stack.push(binary(BinaryOp::Add, previous, one).map_err(own)?);
			}
			// A negated literal is one literal, so `-128` is representable as
			// an `i8` although `128` does not.
			ExprKind::PrimitiveUnary {
				op: UnaryOp::InvertSign,
				operand,
			} if let ExprKind::Int(value) =
				body_of(self, owner).kind(operand)
				&& let Some(scalar) = Primitive::of(ty) =>
			{
				stack.push(
					literal(value, true, scalar).ok_or(own(
						EvalErrorKind::Overflow(Operation::Negate),
					))?,
				);
			}
			ExprKind::PrimitiveUnary { op, operand } => {
				self.eval(strings, owner, operand, stack)?;
				let operand = stack.pop().expect("an operand's value");
				stack.push(unary(op, operand).map_err(own)?);
			}
			// Its values are its elements', in declared order, as its type's
			// layout is.
			ExprKind::Tuple { elements, order } => {
				self.eval_ordered(strings, owner, elements, order, stack)?;
			}
			// Its fields' value; one missing was reported, which makes it
			// `ERROR`.
			ExprKind::StructConstructor { fields, .. } => {
				self.eval(strings, owner, fields, stack)?;
			}
			ExprKind::PrimitiveBinary { op, lhs, rhs } => {
				self.eval(strings, owner, lhs, stack)?;
				// `&&` and `||` do not evaluate a right side they do not need;
				// otherwise the right side is the answer.
				if matches!(op, BinaryOp::And | BinaryOp::Or) {
					let lhs = stack.last().expect("an operand's value");
					if lhs.expect_bool() == (op == BinaryOp::Or) {
						return Ok(());
					}
					stack.pop();
					return self.eval(strings, owner, rhs, stack);
				}
				self.eval(strings, owner, rhs, stack)?;
				let rhs = stack.pop().expect("an operand's value");
				let lhs = stack.pop().expect("an operand's value");
				stack.push(binary(op, lhs, rhs).map_err(own)?);
			}
		}
		Ok(())
	}

	/// Preserve a floating literal through references and sign changes.
	/// Binary arithmetic requires a precision-independent evaluator; calls
	/// and other unsupported expressions follow the normal constant rules.
	fn eval_untyped_float(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		expr: ExprIdx,
	) -> Result<DecimalFloat, Halt> {
		let body = body_of(self, owner);
		let (kind, ty, span) =
			(body.kind(expr), body.ty(expr), body.span(expr));
		if ty == TypeIndex::ERROR {
			return Err(Halt::Silent);
		}
		let own = |kind| Halt::Own(EvalError { span, kind });
		match kind {
			ExprKind::Float(value) => Ok(value),
			ExprKind::PrimitiveUnary {
				op: UnaryOp::InvertSign,
				operand,
			} => {
				let mut value =
					self.eval_untyped_float(strings, owner, operand)?;
				value.negative = !value.negative;
				Ok(value)
			}
			ExprKind::Const {
				constant,
				type_args,
			}
			| ExprKind::AbstractConst {
				constant,
				type_args,
			} => {
				let args = self.generic_args.types(type_args).to_vec();
				let args: Vec<_> = args
					.into_iter()
					.map(|arg| self.instance_type(strings, owner, arg))
					.collect();
				let resolved = self
					.resolve_constant(strings, constant, &args)
					.map_err(|_| Halt::Silent)?;
				let ResolvedConstant::Instance(instance) = resolved else {
					return Err(own(EvalErrorKind::NotConst));
				};
				self.float_value(strings, instance)
					.map_err(|error| match error {
						Unevaluable::NoValue => own(EvalErrorKind::NotConst),
						Unevaluable::Silent => Halt::Silent,
					})
			}
			ExprKind::PrimitiveBinary { .. }
			| ExprKind::PrimitiveUnary { .. } => {
				Err(own(EvalErrorKind::UnsupportedFloatArithmetic))
			}
			ExprKind::Error => Err(Halt::Silent),
			_ => Err(own(EvalErrorKind::NotConst)),
		}
	}

	/// The exact value of a node of an untyped constant's body: a literal of
	/// its kind, another untyped constant, or `-` and a binary operator over
	/// them, computed as mathematical integers (in `i128`), since the value has
	/// no type yet; each use checks it is representable as the type it is
	/// given.
	fn eval_exact(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		expr: ExprIdx,
	) -> Result<i128, Halt> {
		let body = body_of(self, owner);
		let (kind, ty, span) =
			(body.kind(expr), body.ty(expr), body.span(expr));
		if ty == TypeIndex::ERROR {
			return Err(Halt::Silent);
		}
		let own = |kind| Halt::Own(EvalError { span, kind });
		match kind {
			ExprKind::Int(value) => Ok(i128::from(value)),
			ExprKind::Char(value) => Ok(i128::from(u32::from(value))),
			ExprKind::Const { constant, .. } => self
				.exact_value(strings, constant)
				.map_err(|error| match error {
					Unevaluable::NoValue => own(EvalErrorKind::NotConst),
					Unevaluable::Silent => Halt::Silent,
				}),
			ExprKind::PrimitiveUnary {
				op: UnaryOp::InvertSign,
				operand,
			} => self
				.eval_exact(strings, owner, operand)?
				.checked_neg()
				.ok_or(own(EvalErrorKind::Overflow(Operation::Negate))),
			ExprKind::PrimitiveBinary { op, lhs, rhs } => {
				let a = self.eval_exact(strings, owner, lhs)?;
				let b = self.eval_exact(strings, owner, rhs)?;
				exact_binary(op, a, b).map_err(own)
			}
			ExprKind::Error => Err(Halt::Silent),
			_ => Err(own(EvalErrorKind::NotConst)),
		}
	}

	/// The data `expr` of `owner`'s body is (a string or array literal, or a
	/// constant holding one) placed in the memory the pointer type `ty`
	/// names: the pointer, pushed.
	fn place_data(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		expr: ExprIdx,
		ty: TypeIndex,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let body = body_of(self, owner);
		let (kind, span) = (body.kind(expr), body.span(expr));
		match kind {
			ExprKind::String(_)
			| ExprKind::Array { .. }
			| ExprKind::ArrayRepeat { .. } => {
				self.eval_static(strings, owner, expr, ty, stack)
			}
			ExprKind::Const { constant, .. } => {
				let root = match self.const_bodies[usize::from(constant)] {
					ConstBody::Built(body) => self.body(body).root(),
					// Reported where the constant is.
					_ => return Err(Halt::Silent),
				};
				let owner = Owner {
					body: Evaluated::Constant(constant),
					args: &[],
				};
				self.place_data(strings, owner, root, ty, stack)
			}
			_ => Err(Halt::Own(EvalError {
				span,
				kind: EvalErrorKind::NotConst,
			})),
		}
	}

	/// A string or array literal `expr` of `owner`'s body as type `ty`:
	/// placed (`ty` a pointer), its data is allocated and its pointer pushed.
	/// Not placed (`ty` an array: an element of other data, or a constant's
	/// value), its elements' values are pushed, one element after another,
	/// as the data holding it writes them in place.
	fn eval_static(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		expr: ExprIdx,
		ty: TypeIndex,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let body = body_of(self, owner);
		let (kind, span) = (body.kind(expr), body.span(expr));
		let placed = matches!(self.types.resolve(ty), Type::Pointer { .. });
		let start = stack.len();
		match kind {
			ExprKind::String(contents) if placed => {
				self.eval_string(strings, owner, contents, ty, span, stack)
			}
			ExprKind::String(contents) => {
				let bytes = strings.resolve(contents).unwrap().as_bytes();
				stack.extend(bytes.iter().map(|&byte| ConstScalar::u8(byte)));
				Ok(())
			}
			// Each element's values, one after another, laid out as static
			// data.
			ExprKind::Array { elements } => {
				for at in 0..elements.len() {
					let element = body_of(self, owner).args(elements)[at];
					self.eval(strings, owner, element, stack)?;
				}
				if !placed {
					return Ok(());
				}
				let count = u64::try_from(elements.len()).unwrap();
				self.place_static(strings, owner, ty, span, count, start, stack)
			}
			// One element's values, laid out `count` times; `_` is the
			// array's own length.
			ExprKind::ArrayRepeat { value, count } => {
				self.eval(strings, owner, value, stack)?;
				let array = if placed { self.static_pointee(ty) } else { ty };
				let count = match count {
					Some(count) => self.repeat_count(strings, owner, count)?,
					// As long as its array.
					None => {
						let Type::Array { length, .. } =
							*self.types.resolve(array)
						else {
							unreachable!("`_` is the length of an array")
						};
						self.length_value(strings, owner, length)?
					}
				};
				if placed {
					return self.place_static(
						strings, owner, ty, span, count, start, stack,
					);
				}
				// The one element's values, once per element.
				let element = stack.split_off(start);
				let count = usize::try_from(count).map_err(|_| {
					Halt::Own(EvalError {
						span,
						kind: EvalErrorKind::TooLarge,
					})
				})?;
				for _ in 0..count {
					stack.extend_from_slice(&element);
				}
				Ok(())
			}
			_ => unreachable!("only a literal is static data"),
		}
	}

	/// A repeat's `count`, a node of `owner`'s body: an integer literal or a
	/// free constant (`repeat_length`), a count whatever type it was given.
	fn repeat_count(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		count: ExprIdx,
	) -> Result<u64, Halt> {
		match body_of(self, owner).kind(count) {
			ExprKind::Int(bits) => Ok(bits),
			ExprKind::Const { constant, .. } => {
				let length = self.types.intern_const_ref(constant, &[]);
				self.length_value(strings, owner, length)
			}
			// Reported where the count is written.
			_ => Err(Halt::Silent),
		}
	}

	/// A string literal's value: its contents, placed as static data.
	fn eval_string(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		contents: SymbolU32,
		ty: TypeIndex,
		span: TextSpan,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let (memory, width) = self.static_memory(strings, owner, ty, span)?;
		let bytes: Box<[u8]> =
			strings.resolve(contents).unwrap().as_bytes().into();
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
	#[allow(clippy::too_many_arguments)]
	fn place_static(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		ty: TypeIndex,
		span: TextSpan,
		count: u64,
		start: usize,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		let (memory, width) = self.static_memory(strings, owner, ty, span)?;
		let (Type::Slice { of } | Type::Array { of, .. }) =
			*self.types.resolve(self.static_pointee(ty))
		else {
			unreachable!("static data is an array or a slice")
		};
		// Elements whose bytes are not known yet (of an abstract type) cannot
		// be written.
		let (layout, places) = match self.memory_values(
			strings,
			self.assumption_envs.of_frame(body_env(self, owner)),
			of,
		) {
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

	/// The slice or array static data of type `ty`, a pointer to it, points
	/// at.
	fn static_pointee(&self, ty: TypeIndex) -> TypeIndex {
		let Type::Pointer { to, .. } = *self.types.resolve(ty) else {
			unreachable!("static data is behind a pointer")
		};
		to
	}

	/// The memory static data of type `ty` (a shared pointer to an array or
	/// a slice) is placed in, and the scalar its address is held as. In a
	/// memory not known yet there is nowhere to place it.
	fn static_memory(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		ty: TypeIndex,
		span: TextSpan,
	) -> Result<(MemoryIdx, Primitive), Halt> {
		let scope = self.assumption_envs.of_frame(body_env(self, owner));
		let Type::Pointer { memory, .. } = *self.types.resolve(ty) else {
			unreachable!("static data is behind a pointer")
		};
		let Some(memory_index) = self.memory_of(strings, scope, memory) else {
			return Err(Halt::Own(EvalError {
				span,
				kind: EvalErrorKind::NotConst,
			}));
		};
		// The memory is known, so its `Size` is: a failure was reported.
		let width = self
			.address_scalar(strings, scope, memory)
			.map_err(|_| Halt::Silent)?;
		Ok((memory_index, width))
	}

	/// Stores `allocation` and pushes its address, followed by `len` for a
	/// slice (`ty`).
	fn push_static(
		&mut self,
		allocation: Allocation,
		width: Primitive,
		ty: TypeIndex,
		len: u64,
		stack: &mut Vec<ConstScalar>,
	) {
		let alloc = AllocIdx::new(
			u32::try_from(self.solver.allocations.len()).unwrap(),
		);
		self.solver.allocations.push(allocation);
		stack.push(ConstScalar {
			val: Val::MemoryOffset { alloc, offset: 0 },
			scalar: width,
		});
		if let Type::Slice { .. } = self.types.resolve(self.static_pointee(ty))
		{
			stack.push(match width {
				Primitive::U32 => ConstScalar::u32(u32::try_from(len).unwrap()),
				Primitive::U64 => ConstScalar::u64(len),
				_ => unreachable!("`PointerSize` holds `u32` and `u64`"),
			});
		}
	}

	/// An array type's `length`, read in `owner`'s body: a value, or a
	/// constant it names, evaluated. A constant that fails reports itself.
	fn length_value(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		length: TypeIndex,
	) -> Result<u64, Halt> {
		let env = body_env(self, owner);
		match self.normalize(
			strings,
			self.assumption_envs.of_frame(env),
			length,
			NormalizationDepth::Shallow,
			RewriteFlags::ALL,
		) {
			Ok(length) => match *self.types.resolve(length) {
				Type::Value { bits } => Ok(bits),
				_ => Err(Halt::Silent),
			},
			Err(_) => Err(Halt::Silent),
		}
	}

	/// `ty`, written in `owner`'s body, with the instance's arguments.
	fn instance_type(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		ty: TypeIndex,
	) -> TypeIndex {
		if owner.args.is_empty() {
			return ty;
		}
		let env = body_env(self, owner);
		let ty = self.types.substitute(
			ty,
			Substitution {
				envs: &self.generic_envs,
				env,
				args: owner.args,
			},
		);
		self.normalize(
			strings,
			self.assumption_envs.of_frame(env),
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		)
		.unwrap_or(TypeIndex::ERROR)
	}

	/// The instance of `constant` with `args`, keyed by its interned
	/// `Type::ConstRef`.
	fn instance(&mut self, constant: ConstIdx, args: &[TypeIndex]) -> Instance {
		if args.is_empty() {
			return Instance::of(constant);
		}
		let interned = self.types.intern_const_ref(constant, args);
		let Type::ConstRef { type_args, .. } = *self.types.resolve(interned)
		else {
			unreachable!("a constant interns as a `Type::ConstRef`")
		};
		Instance {
			constant,
			args: type_args,
		}
	}

	/// What `constant` with `args` reads: itself, or, for a trait's
	/// declaration, the member of the impl its `Self` selects, the trait's
	/// default when the impl inherits it, or the compiler's answer for a
	/// trait it implements (`Array::LEN`).
	pub(super) fn resolve_constant(
		&mut self,
		strings: &StringInterner,
		constant: ConstIdx,
		args: &[TypeIndex],
	) -> Result<ResolvedConstant, SolverError> {
		let MemberOwner::Trait(trait_index) =
			self.decls.constants[usize::from(constant)].owner
		else {
			return Ok(ResolvedConstant::Instance(
				self.instance(constant, args),
			));
		};
		let receiver = args[0];
		if self.types.has_param(receiver) {
			return Ok(ResolvedConstant::Abstract);
		}
		Ok(
			match self.find_trait_impl_query(
				strings,
				AssumptionEnvIdx::ROOT,
				receiver,
				trait_index,
			)? {
				Some(TraitImplLookup::Concrete {
					impl_index,
					args: impl_args,
				}) => {
					match self.decls.select_trait_member(
						impl_index,
						MemberKind::Constant(constant),
					) {
						TraitMemberSelection::Impl(MemberKind::Constant(
							own,
						)) => ResolvedConstant::Instance(
							self.instance(own, &impl_args),
						),
						_ if Some(constant)
							== self.decls.intrinsics.memory_data_end
							&& let Type::Memory { memory_index } =
								*self.types.resolve(receiver) =>
						{
							ResolvedConstant::DataEnd(memory_index)
						}
						_ => ResolvedConstant::Instance(
							self.instance(constant, args),
						),
					}
				}
				Some(TraitImplLookup::Builtin) => {
					let Type::Array { length, .. } =
						*self.types.resolve(receiver)
					else {
						unreachable!(
							"the compiler implements only `Array::LEN`"
						)
					};
					debug_assert_eq!(
						Some(constant),
						self.decls.intrinsics.array_len
					);
					ResolvedConstant::Length(length)
				}
				Some(TraitImplLookup::Abstract) => ResolvedConstant::Abstract,
				// The unmet bound was reported where the constant is named.
				None => return Err(SolverError::Poisoned),
			},
		)
	}

	/// The value of the constant a node of `owner`'s body names with `args`,
	/// of type `ty`.
	#[allow(clippy::too_many_arguments)]
	fn read_reference(
		&mut self,
		strings: &StringInterner,
		owner: Owner<'_>,
		constant: ConstIdx,
		args: &[TypeIndex],
		ty: TypeIndex,
		span: TextSpan,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		match self.resolve_constant(strings, constant, args) {
			Ok(ResolvedConstant::Instance(instance))
				if self.constants[usize::from(instance.constant)].ty
					== TypeIndex::CONST_FLOAT =>
			{
				let value =
					self.float_value(strings, instance).map_err(|error| {
						match error {
							Unevaluable::NoValue => Halt::Own(EvalError {
								span,
								kind: EvalErrorKind::NotConst,
							}),
							Unevaluable::Silent => Halt::Silent,
						}
					})?;
				let read = self
					.read_float_literal(value, ConcreteType::Target(ty))
					.ok()
					.ok_or(Halt::Silent)?;
				stack.push(match ty {
					TypeIndex::F32 => ConstScalar::f32(read as f32),
					TypeIndex::F64 => ConstScalar::f64(read),
					_ => return Err(Halt::Silent),
				});
				Ok(())
			}
			Ok(ResolvedConstant::Instance(instance))
				if self.constants[usize::from(instance.constant)]
					.ty
					.is_const_kind() =>
			{
				let value = match self.exact_value(strings, instance.constant) {
					Ok(value) => value,
					Err(Unevaluable::NoValue) => {
						return Err(Halt::Own(EvalError {
							span,
							kind: EvalErrorKind::NotConst,
						}));
					}
					Err(Unevaluable::Silent) => return Err(Halt::Silent),
				};
				// Its use checked that the value is representable.
				stack.push(exact_scalar(value, ty).ok_or(Halt::Silent)?);
				Ok(())
			}
			Ok(ResolvedConstant::Instance(instance)) => {
				let used_at = SourceSpan::new(body_file(self, owner), span);
				self.read_constant(
					strings,
					instance,
					Some(used_at),
					span,
					stack,
				)
			}
			Ok(ResolvedConstant::Length(length)) => {
				let length = self.length_value(strings, owner, length)?;
				let scalar = Primitive::of(ty)
					.expect("an array's length is of a memory's `Size`");
				stack.push(literal(length, false, scalar).expect(
					"an array's length is representable as its memory's `Size`",
				));
				Ok(())
			}
			Ok(ResolvedConstant::DataEnd(memory)) => {
				let memory_type = self.types.intern(Type::Memory {
					memory_index: memory,
				});
				let scalar = self
					.address_scalar(
						strings,
						AssumptionEnvIdx::ROOT,
						memory_type,
					)
					.map_err(|_| Halt::Silent)?;
				stack.push(ConstScalar {
					val: Val::DataEnd { memory },
					scalar,
				});
				Ok(())
			}
			Ok(ResolvedConstant::Abstract) => Err(Halt::Own(EvalError {
				span,
				kind: EvalErrorKind::NotConst,
			})),
			Err(_) => Err(Halt::Silent),
		}
	}

	/// The value of `instance`, which a node names at `used_at` (for an
	/// instance's first reader). One with no compile-time value (its type is
	/// not a scalar) makes the naming node not a constant expression.
	fn read_constant(
		&mut self,
		strings: &StringInterner,
		instance: Instance,
		used_at: Option<SourceSpan>,
		span: TextSpan,
		stack: &mut Vec<ConstScalar>,
	) -> Result<(), Halt> {
		match self.instance_value(strings, instance, used_at) {
			Ok(value) => {
				stack.extend_from_slice(value);
				Ok(())
			}
			Err(Unevaluable::NoValue) => Err(Halt::Own(EvalError {
				span,
				kind: EvalErrorKind::NotConst,
			})),
			Err(Unevaluable::Silent) => Err(Halt::Silent),
		}
	}

	/// The scalars a value of the constant's declared type holds, one per
	/// number. `Err` is the final state of a constant of a type the evaluator
	/// holds no values of.
	fn constant_scalars(
		&mut self,
		strings: &StringInterner,
		const_index: ConstIdx,
		owner: Owner<'_>,
	) -> Result<Vec<Primitive>, ConstValueState> {
		let signature = &self.constants[usize::from(const_index)];
		let (ty, scope) = (signature.ty, signature.env);
		let ty = self.instance_type(strings, owner, ty);
		let mut scalars = Vec::new();
		self.push_scalars(
			strings,
			self.assumption_envs.of_frame(scope),
			ty,
			&mut scalars,
			&mut Vec::new(),
		)?;
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
		strings: &StringInterner,
		scope: AssumptionEnvIdx,
		ty: TypeIndex,
		out: &mut Vec<Primitive>,
		visiting: &mut Vec<TypeIndex>,
	) -> Result<(), ConstValueState> {
		let ty = self
			.normalize(
				strings,
				scope,
				ty,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)
			.unwrap_or(ty);
		if ty == TypeIndex::ERROR {
			return Err(ConstValueState::Poisoned);
		}
		if let Some(scalar) = Primitive::of(ty) {
			out.push(scalar);
			return Ok(());
		}
		match *self.types.resolve(ty) {
			Type::Function { .. }
			| Type::Memory { .. }
			| Type::Global { .. } => Ok(()),
			Type::Enum { enum_index } => {
				let repr = self.enums[usize::from(enum_index)].repr;
				self.push_scalars(strings, scope, repr, out, visiting)
			}
			// An address, then the pointee's counts.
			Type::Pointer { to, memory, .. } => {
				let scalar = self.address_scalar(strings, scope, memory)?;
				let metadata =
					self.pointer_metadata(strings, scope, to, memory);
				let count = match metadata {
					Ok(Some(metadata)) => metadata_len(&self.types, metadata),
					Ok(None) => return Err(ConstValueState::NoValue),
					Err(_) => return Err(ConstValueState::Poisoned),
				};
				out.extend(std::iter::repeat_n(scalar, 1 + count));
				Ok(())
			}
			Type::Tuple { elements } => {
				let mut held = Ok(());
				for at in 0..self.types.list(elements).len() {
					let element = self.types.list(elements)[at];
					held = merge(
						held,
						self.push_scalars(
							strings, scope, element, out, visiting,
						),
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
							envs: &self.generic_envs,
							env,
							args: &args,
						},
					);
					held = merge(
						held,
						self.push_scalars(strings, scope, field, out, visiting),
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
		strings: &StringInterner,
		scope: AssumptionEnvIdx,
		memory: TypeIndex,
	) -> Result<Primitive, ConstValueState> {
		let Some(memory_index) = self.memory_of(strings, scope, memory) else {
			return Err(ConstValueState::NoValue);
		};
		let size = self.decls.memories[usize::from(memory_index)]
			.size_assoc_type_index;
		let size = self.assoc_types[usize::from(size)]
			.as_ref()
			.and_then(|signature| signature.value)
			.ok_or(ConstValueState::Poisoned)?;
		let size = self
			.normalize(
				strings,
				scope,
				size,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)
			.unwrap_or(size);
		Primitive::of(size).ok_or(ConstValueState::Poisoned)
	}

	/// The memory `memory` names in `scope`, if it is a known one.
	fn memory_of(
		&mut self,
		strings: &StringInterner,
		scope: AssumptionEnvIdx,
		memory: TypeIndex,
	) -> Option<MemoryIdx> {
		let memory = self
			.normalize(
				strings,
				scope,
				memory,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)
			.unwrap_or(memory);
		match *self.types.resolve(memory) {
			Type::Memory { memory_index } => Some(memory_index),
			_ => None,
		}
	}
}

impl EvalErrorKind {
	fn code(self) -> DiagnosticCode {
		match self {
			Self::NotConst => DiagnosticCode::NotConstEvaluatable,
			Self::UnsupportedFloatArithmetic => {
				DiagnosticCode::UnsupportedExpression
			}
			_ => DiagnosticCode::ConstEvaluationFailed,
		}
	}

	fn label(self) -> String {
		match self {
			Self::NotConst => "not a constant expression".to_string(),
			Self::UnsupportedFloatArithmetic => {
				"untyped floating-point arithmetic is not supported yet"
					.to_string()
			}
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

/// What fails in a function's static data, at the node that fails.
fn report_static_failure(
	file_id: crate::vfs::FileId,
	error: &EvalError,
) -> Diagnostic<crate::vfs::FileId> {
	let message = match error.kind {
		EvalErrorKind::NotConst => {
			"static data cannot be evaluated at compile time"
		}
		_ => "evaluation of static data failed",
	};
	Diagnostic::error()
		.with_code(error.kind.code().code())
		.with_message(message)
		.with_label(
			SourceSpan::new(file_id, error.span)
				.primary_label()
				.with_message(error.kind.label()),
		)
		.with_note(
			"a string or array literal is placed as data before the program \
			 runs, so its elements are constant expressions",
		)
}

impl ConstScalar {
	pub(super) fn u8(value: u8) -> Self {
		Self {
			val: Val::I32(u32::from(value)),
			scalar: Primitive::U8,
		}
	}

	pub(super) fn i8(value: i8) -> Self {
		Self {
			val: Val::I32(i32::from(value) as u32),
			scalar: Primitive::I8,
		}
	}

	pub(super) fn u16(value: u16) -> Self {
		Self {
			val: Val::I32(u32::from(value)),
			scalar: Primitive::U16,
		}
	}

	pub(super) fn i16(value: i16) -> Self {
		Self {
			val: Val::I32(i32::from(value) as u32),
			scalar: Primitive::I16,
		}
	}

	pub(super) fn u32(value: u32) -> Self {
		Self {
			val: Val::I32(value),
			scalar: Primitive::U32,
		}
	}

	pub(super) fn i32(value: i32) -> Self {
		Self {
			val: Val::I32(value as u32),
			scalar: Primitive::I32,
		}
	}

	pub(super) fn u64(value: u64) -> Self {
		Self {
			val: Val::I64(value),
			scalar: Primitive::U64,
		}
	}

	pub(super) fn i64(value: i64) -> Self {
		Self {
			val: Val::I64(value as u64),
			scalar: Primitive::I64,
		}
	}

	pub(super) fn f32(value: f32) -> Self {
		Self {
			val: Val::F32(value.to_bits()),
			scalar: Primitive::F32,
		}
	}

	pub(super) fn f64(value: f64) -> Self {
		Self {
			val: Val::F64(value.to_bits()),
			scalar: Primitive::F64,
		}
	}

	/// A `Bool`, held as its repr.
	pub(super) fn bool(value: bool) -> Self {
		Self::u8(u8::from(value))
	}

	/// A `Char`, held as its field.
	pub(super) fn char(value: char) -> Self {
		Self::u32(u32::from(value))
	}

	pub(super) fn expect_u8(self) -> u8 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Primitive::U8,
			} => bits as u8,
			_ => unreachable!("not a `u8`"),
		}
	}

	pub(super) fn expect_i8(self) -> i8 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Primitive::I8,
			} => bits as i8,
			_ => unreachable!("not an `i8`"),
		}
	}

	pub(super) fn expect_u16(self) -> u16 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Primitive::U16,
			} => bits as u16,
			_ => unreachable!("not a `u16`"),
		}
	}

	pub(super) fn expect_i16(self) -> i16 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Primitive::I16,
			} => bits as i16,
			_ => unreachable!("not an `i16`"),
		}
	}

	pub(super) fn expect_u32(self) -> u32 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Primitive::U32,
			} => bits,
			_ => unreachable!("not a `u32`"),
		}
	}

	pub(super) fn expect_i32(self) -> i32 {
		match self {
			Self {
				val: Val::I32(bits),
				scalar: Primitive::I32,
			} => bits as i32,
			_ => unreachable!("not an `i32`"),
		}
	}

	pub(super) fn expect_u64(self) -> u64 {
		match self {
			Self {
				val: Val::I64(bits),
				scalar: Primitive::U64,
			} => bits,
			_ => unreachable!("not a `u64`"),
		}
	}

	pub(super) fn expect_i64(self) -> i64 {
		match self {
			Self {
				val: Val::I64(bits),
				scalar: Primitive::I64,
			} => bits as i64,
			_ => unreachable!("not an `i64`"),
		}
	}

	pub(super) fn expect_f32(self) -> f32 {
		match self {
			Self {
				val: Val::F32(bits),
				scalar: Primitive::F32,
			} => f32::from_bits(bits),
			_ => unreachable!("not an `f32`"),
		}
	}

	pub(super) fn expect_f64(self) -> f64 {
		match self {
			Self {
				val: Val::F64(bits),
				scalar: Primitive::F64,
			} => f64::from_bits(bits),
			_ => unreachable!("not an `f64`"),
		}
	}

	pub(super) fn expect_bool(self) -> bool {
		self.expect_u8() != 0
	}
}

impl std::fmt::Display for ConstScalar {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self.scalar {
			Primitive::U8 => write!(f, "{}", self.expect_u8()),
			Primitive::I8 => write!(f, "{}", self.expect_i8()),
			Primitive::U16 => write!(f, "{}", self.expect_u16()),
			Primitive::I16 => write!(f, "{}", self.expect_i16()),
			Primitive::U32 => write!(f, "{}", self.expect_u32()),
			Primitive::I32 => write!(f, "{}", self.expect_i32()),
			Primitive::U64 => write!(f, "{}", self.expect_u64()),
			Primitive::I64 => write!(f, "{}", self.expect_i64()),
			Primitive::F32 => write!(f, "{}", self.expect_f32()),
			Primitive::F64 => write!(f, "{}", self.expect_f64()),
		}
	}
}

/// Writes `value`, a value's numbers in declaration order, into `bytes` at
/// `base`: each number at its place in the value's layout, little-endian and
/// as wide as its primitive. An address is written as its offset, and
/// recorded as a relocation to its allocation.
fn write_value(
	bytes: &mut [u8],
	relocations: &mut Vec<(u32, AddressTarget)>,
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
			Val::MemoryOffset { alloc, offset } => {
				relocations.push((at, AddressTarget::Allocation(alloc)));
				u128::from(offset)
			}
			Val::DataEnd { memory } => {
				relocations.push((at, AddressTarget::DataEnd(memory)));
				0
			}
		};
		let size = primitive.size() as usize;
		bytes[at as usize..][..size]
			.copy_from_slice(&bits.to_le_bytes()[..size]);
	}
}

/// An untyped constant's exact `value` as a value of `ty`, the type its use
/// gave it: a `Char`, an integer or a float. `None` when it is not
/// representable, which that use reports.
fn exact_scalar(value: i128, ty: TypeIndex) -> Option<ConstScalar> {
	if ty == TypeIndex::CHAR {
		return char::from_u32(u32::try_from(value).ok()?)
			.map(ConstScalar::char);
	}
	match Primitive::of(ty)? {
		Primitive::F32 => Some(ConstScalar::f32(value as f32)),
		Primitive::F64 => Some(ConstScalar::f64(value as f64)),
		scalar => literal(
			u64::try_from(value.unsigned_abs()).ok()?,
			value < 0,
			scalar,
		),
	}
}

/// `a op b` on two exact integers: `Err` when the result is outside `i128`,
/// for a zero divisor, or a shift amount that is negative or past the
/// width. Division truncates and a remainder has the dividend's sign, as
/// wasm's `div_s`/`rem_s`; a right shift is arithmetic.
fn exact_binary(op: BinaryOp, a: i128, b: i128) -> Result<i128, EvalErrorKind> {
	let overflow = EvalErrorKind::Overflow(Operation::Binary(op));
	let shift = || u32::try_from(b).ok().filter(|&shift| shift < i128::BITS);
	match op {
		BinaryOp::Add => a.checked_add(b).ok_or(overflow),
		BinaryOp::Sub => a.checked_sub(b).ok_or(overflow),
		BinaryOp::Mul => a.checked_mul(b).ok_or(overflow),
		BinaryOp::Div if b == 0 => Err(EvalErrorKind::DivisionByZero),
		BinaryOp::Rem if b == 0 => Err(EvalErrorKind::RemainderByZero),
		BinaryOp::Div => a.checked_div(b).ok_or(overflow),
		BinaryOp::Rem => a.checked_rem(b).ok_or(overflow),
		BinaryOp::BitAnd => Ok(a & b),
		BinaryOp::BitOr => Ok(a | b),
		BinaryOp::BitXor => Ok(a ^ b),
		// Exact: no bit is shifted out.
		BinaryOp::LeftShift => shift()
			.map(|shift| a << shift)
			.filter(|&shifted| shifted >> shift().unwrap() == a)
			.ok_or(overflow),
		BinaryOp::RightShift => shift().map(|shift| a >> shift).ok_or(overflow),
		_ => unreachable!("an untyped operator is arithmetic"),
	}
}

/// The integer literal `value` as `scalar`, negated when it is written
/// `-value`; `None` when it is not representable.
fn literal(
	value: u64,
	negated: bool,
	scalar: Primitive,
) -> Option<ConstScalar> {
	// Integer spelling stays an Int node even when its checked type is a
	// float. Representability was checked before evaluation.
	let sign = if negated { -1.0 } else { 1.0 };
	match scalar {
		Primitive::F32 => {
			return Some(ConstScalar::f32(sign as f32 * value as f32));
		}
		Primitive::F64 => return Some(ConstScalar::f64(sign * value as f64)),
		_ => {}
	}
	if !scalar.is_signed() {
		if negated && value != 0 {
			return None;
		}
		return Some(match scalar {
			Primitive::U8 => ConstScalar::u8(u8::try_from(value).ok()?),
			Primitive::U16 => ConstScalar::u16(u16::try_from(value).ok()?),
			Primitive::U32 => ConstScalar::u32(u32::try_from(value).ok()?),
			Primitive::U64 => ConstScalar::u64(value),
			_ => unreachable!("an integer literal has an integer type"),
		});
	}
	let value = if negated {
		0i64.checked_sub_unsigned(value)?
	} else {
		i64::try_from(value).ok()?
	};
	Some(match scalar {
		Primitive::I8 => ConstScalar::i8(i8::try_from(value).ok()?),
		Primitive::I16 => ConstScalar::i16(i16::try_from(value).ok()?),
		Primitive::I32 => ConstScalar::i32(i32::try_from(value).ok()?),
		Primitive::I64 => ConstScalar::i64(value),
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
		(UnaryOp::InvertSign, Primitive::F32) => {
			Ok(ConstScalar::f32(-operand.expect_f32()))
		}
		(UnaryOp::InvertSign, Primitive::F64) => {
			Ok(ConstScalar::f64(-operand.expect_f64()))
		}
		(UnaryOp::Not, _) => unreachable!("`!` is a call of `Not::not`"),
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
		Primitive::U8 => {
			let a = operand.expect_u8();
			ConstScalar::u8(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::I8 => {
			let a = operand.expect_i8();
			ConstScalar::i8(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::U16 => {
			let a = operand.expect_u16();
			ConstScalar::u16(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::I16 => {
			let a = operand.expect_i16();
			ConstScalar::i16(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::U32 => {
			let a = operand.expect_u32();
			ConstScalar::u32(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::I32 => {
			let a = operand.expect_i32();
			ConstScalar::i32(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::U64 => {
			let a = operand.expect_u64();
			ConstScalar::u64(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::I64 => {
			let a = operand.expect_i64();
			ConstScalar::i64(if negate { a.checked_neg()? } else { !a })
		}
		Primitive::F32 | Primitive::F64 => {
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
		Primitive::F32 => {
			let (a, b) = (lhs.expect_f32(), rhs.expect_f32());
			Ok(ConstScalar::f32(match op {
				BinaryOp::Add => a + b,
				BinaryOp::Sub => a - b,
				BinaryOp::Mul => a * b,
				BinaryOp::Div => a / b,
				// core implements no `Rem` for a float (an `fmod` is the math
				// library's), so checked source never asks for one.
				BinaryOp::Rem => unreachable!("a float has no `%`"),
				_ => unreachable!(),
			}))
		}
		Primitive::F64 => {
			let (a, b) = (lhs.expect_f64(), rhs.expect_f64());
			Ok(ConstScalar::f64(match op {
				BinaryOp::Add => a + b,
				BinaryOp::Sub => a - b,
				BinaryOp::Mul => a * b,
				BinaryOp::Div => a / b,
				// core implements no `Rem` for a float (an `fmod` is the math
				// library's), so checked source never asks for one.
				BinaryOp::Rem => unreachable!("a float has no `%`"),
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
		Primitive::U8 => {
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
		Primitive::I8 => {
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
		Primitive::U16 => {
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
		Primitive::I16 => {
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
		Primitive::U32 => {
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
		Primitive::I32 => {
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
		Primitive::U64 => {
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
		Primitive::I64 => {
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
		Primitive::F32 | Primitive::F64 => {
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
		Primitive::U8 => lhs.expect_u8().partial_cmp(&rhs.expect_u8()),
		Primitive::I8 => lhs.expect_i8().partial_cmp(&rhs.expect_i8()),
		Primitive::U16 => lhs.expect_u16().partial_cmp(&rhs.expect_u16()),
		Primitive::I16 => lhs.expect_i16().partial_cmp(&rhs.expect_i16()),
		Primitive::U32 => lhs.expect_u32().partial_cmp(&rhs.expect_u32()),
		Primitive::I32 => lhs.expect_i32().partial_cmp(&rhs.expect_i32()),
		Primitive::U64 => lhs.expect_u64().partial_cmp(&rhs.expect_u64()),
		Primitive::I64 => lhs.expect_i64().partial_cmp(&rhs.expect_i64()),
		// IEEE: any comparison with NaN is false, except `!=`.
		Primitive::F32 => lhs.expect_f32().partial_cmp(&rhs.expect_f32()),
		Primitive::F64 => lhs.expect_f64().partial_cmp(&rhs.expect_f64()),
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
	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::DiagnosticCode;
	use crate::testing::DiagnosticView;
	use crate::tir::decls::{DeclKind, Scope, Tier};
	use crate::tir::paths::PathResolver;
	use crate::tir::resolutions::NameResolutions;
	use crate::vfs::{self, Files};

	fn source_graph(
		source: &str,
		strings: &mut StringInterner,
	) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new(strings);
		builder.load_core();
		let root_id = builder
			.load_package(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)]),
				),
			)
			.unwrap();
		let graph = builder.build(root_id);
		DiagnosticView::new(
			"parse",
			&graph.collect_parser_diagnostics(),
			&graph.files,
		)
		.assert_no_errors();
		graph
	}

	/// A checked `Semantics`, with the inputs it was checked from.
	/// The source is a binary over the real core.
	struct TestCase {
		files: Files,
		strings: StringInterner,
		sema: Semantics,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut strings = ast::Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
			let mut sema = crate::tir::check(&graph, &mut strings);
			// The core's own bodies use forms the checker does not cover
			// yet; those reports are not what this suite is about.
			let root_file = sema
				.decls
				.namespaces
				.file_id(Scope::Package(sema.decls.root_package).into());
			sema.diagnostics.retain(|diagnostic| {
				let in_core = diagnostic
					.labels
					.first()
					.is_some_and(|label| label.file_id != root_file);
				!(in_core
					&& diagnostic.code.as_deref()
						== Some(DiagnosticCode::UnsupportedExpression.code()))
			});
			Self {
				files: graph.files,
				strings,
				sema,
			}
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new("eval", &self.sema.diagnostics, &self.files)
		}

		/// What a root-level `name` resolves to in `tier`, by real path
		/// resolution.
		fn resolve(&self, tier: Tier, name: &str) -> DeclKind {
			let root = Scope::Package(self.sema.decls.root_package);
			let file_id = self.sema.decls.namespaces.file_id(root.into());
			let segment = ast::PathSegment::new(Spanned {
				inner: self.strings.get(name).unwrap(),
				span: TextSpan::new(0, 0),
			});
			let mut scratch = Vec::new();
			let mut resolutions = NameResolutions::default();
			PathResolver::new(
				&mut scratch,
				&mut resolutions,
				&self.strings,
				&self.sema.decls,
			)
			.resolve_path(file_id, root, &[segment], tier)
			.loc()
			.unwrap_or_else(|| panic!("expected `{name}` to resolve"))
			.symbol_kind(&self.sema.decls)
		}

		fn state(&self, name: &str) -> &ConstValueState {
			let DeclKind::Const(index) = self.resolve(Tier::Value, name) else {
				panic!("expected `{name}` to be a constant");
			};
			&self.sema.solver.const_values[usize::from(index)]
		}

		fn value(&self, name: &str) -> &[ConstScalar] {
			match self.state(name) {
				ConstValueState::Evaluated(value) => value,
				state => panic!("expected `{name}` to have a value: {state:?}"),
			}
		}

		fn memory(&self, name: &str) -> MemoryIdx {
			let DeclKind::Memory(index) = self.resolve(Tier::Value, name)
			else {
				panic!("expected `{name}` to be a memory");
			};
			index
		}

		/// The allocation an address points into, and the offset there.
		fn pointee(&self, address: ConstScalar) -> (&Allocation, u64) {
			let Val::MemoryOffset { alloc, offset } = address.val else {
				panic!("expected an address, got {address:?}");
			};
			(&self.sema.solver.allocations[usize::from(alloc)], offset)
		}
	}

	#[test]
	fn a_trait_constant_is_its_impls_or_the_default_it_inherits() {
		let case = TestCase::new(indoc! {r#"
				trait Tr { const X: u32 = Self::Y + 1; const Y: u32; }
				struct P();
				struct Q();
				impl Tr for P { const Y: u32 = 7; }
				impl Tr for Q { const X: u32 = 2; const Y: u32 = 3; }
				struct W<T>(T);
				impl<T: Tr> Tr for W<T> { const Y: u32 = T::X * 10; }
				const INHERITED: u32 = P::X;
				const OVERRIDDEN: u32 = <Q as Tr>::X;
				const OF_GENERIC_IMPL: u32 = <W<P> as Tr>::Y;
				const INHERITED_BY_GENERIC_IMPL: u32 = W::<Q>::X;
			"#});
		case.diagnostics().assert_none();
		assert_eq!(case.value("INHERITED"), [ConstScalar::u32(8)]);
		assert_eq!(case.value("OVERRIDDEN"), [ConstScalar::u32(2)]);
		assert_eq!(case.value("OF_GENERIC_IMPL"), [ConstScalar::u32(80)]);
		assert_eq!(
			case.value("INHERITED_BY_GENERIC_IMPL"),
			[ConstScalar::u32(21)]
		);
	}

	#[test]
	fn a_loop_through_a_default_is_reported_once_for_its_instance() {
		let case = TestCase::new(indoc! {r#"
				trait Loop { const A: u32 = Self::A + 1; }
				struct P();
				impl Loop for P {}
				const FIRST: u32 = P::A;
				const SECOND: u32 = P::A;
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicConstant]);
		case.diagnostics().assert_error_saying(
			"cycle detected when evaluating constant `<P as Loop>::A`",
		);
	}

	#[test]
	fn an_instance_failure_is_reported_once_by_its_first_reader() {
		let case = TestCase::new(indoc! {r#"
				trait Fail { const F: u8 = Self::G + 200; const G: u8; }
				struct P();
				struct Q();
				impl Fail for P { const G: u8 = 100; }
				impl Fail for Q { const G: u8 = 1; }
				const FIRST: u8 = P::F;
				const SECOND: u8 = P::F;
				const FITS: u8 = Q::F;
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ConstEvaluationFailed]);
		case.diagnostics().assert_error_saying(
			"evaluation of constant `<P as Fail>::F` failed",
		);
		// The first reader is the one the report points at.
		let labels = &case.sema.diagnostics[0].labels;
		assert!(labels.iter().any(|label| {
			label.message == "`<P as Fail>::F` is evaluated for this use"
		}));
		assert_eq!(case.value("FITS"), [ConstScalar::u8(201)]);
	}

	#[test]
	fn an_arrays_len_is_its_length() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const N: u32 = 3;
				type A = [u8; 4];
				const QUALIFIED: u32 = <[u8; 4] as Array>::LEN;
				const ALIASED: u32 = A::LEN;
				const NAMED: u32 = <[u16; N] as Array>::LEN + 1;
				const WIDE: u64 = <[u8; 9] as Array>::LEN;
				const NARROW: u8 = <[u8; 9] as Array>::LEN;
				const FILLED: heap::&[u8; A::LEN] = [7; _];
			"#});
		case.diagnostics().assert_none();
		let [address] = case.value("FILLED") else {
			panic!("expected an address");
		};
		let Val::MemoryOffset { alloc, .. } = address.val else {
			panic!("expected an address");
		};
		assert_eq!(
			*case.sema.solver.allocations[usize::from(alloc)].bytes,
			[7; 4]
		);
		assert_eq!(case.value("QUALIFIED"), [ConstScalar::u32(4)]);
		assert_eq!(case.value("ALIASED"), [ConstScalar::u32(4)]);
		assert_eq!(case.value("NAMED"), [ConstScalar::u32(4)]);
		assert_eq!(case.value("WIDE"), [ConstScalar::u64(9)]);
		assert_eq!(case.value("NARROW"), [ConstScalar::u8(9)]);
	}

	#[test]
	fn a_string_constant_points_into_an_allocation_of_its_contents() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const SLICE: heap::&[u8] = "hello";
				const ARRAY: heap::&[u8; 2] = "a\n";
			"#});
		case.diagnostics().assert_none();

		// A slice is its address and its length.
		let [address, length] = case.value("SLICE") else {
			panic!("expected two values");
		};
		assert_eq!(*length, ConstScalar::u32(5));
		assert_eq!(address.scalar, Primitive::U32);
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
	fn a_constant_of_data_is_placed_at_each_use() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				memory wide: u64;
				const GREETING: [u8; 5] = "hello";
				const NUMBERS: [u16; 3] = [1, 2, 3];
				const FILLED: [u8; 4] = [7; 4];
				const ALIAS: [u8; 5] = GREETING;
				const HEAP: heap::&[u8] = GREETING;
				const WIDE: wide::&[u8; 5] = ALIAS;
				const AGAIN: heap::&[u8; 5] = GREETING;
				const WORDS: heap::&[u16] = NUMBERS;
				const SEVENS: heap::&[u8; 4] = FILLED;
			"#});
		case.diagnostics().assert_none();
		// Data in no memory has no value of its own: each use places it.
		assert!(matches!(case.state("GREETING"), ConstValueState::NoValue));
		let [address, length] = case.value("HEAP") else {
			panic!("expected two values");
		};
		assert_eq!(*length, ConstScalar::u32(5));
		let (allocation, _) = case.pointee(*address);
		assert_eq!(allocation.memory, case.memory("heap"));
		assert_eq!(&*allocation.bytes, b"hello");
		let [wide] = case.value("WIDE") else {
			panic!("expected an address");
		};
		assert_eq!(wide.scalar, Primitive::U64);
		assert_eq!(case.pointee(*wide).0.memory, case.memory("wide"));
		assert_eq!(&*case.pointee(*wide).0.bytes, b"hello");
		// Each use is a copy of its own.
		let [again] = case.value("AGAIN") else {
			panic!("expected an address");
		};
		assert_ne!(again.val, address.val);
		let [words, _] = case.value("WORDS") else {
			panic!("expected two values");
		};
		assert_eq!(&*case.pointee(*words).0.bytes, [1, 0, 2, 0, 3, 0]);
		let [sevens] = case.value("SEVENS") else {
			panic!("expected an address");
		};
		assert_eq!(&*case.pointee(*sevens).0.bytes, [7; 4]);
	}

	#[test]
	fn an_address_into_a_64_bit_memory_is_64_bits_wide() {
		let case = TestCase::new(indoc! {r#"
				memory wide: u64;
				const TEXT: wide::&[u8] = "abc";
			"#});
		case.diagnostics().assert_none();
		let [address, length] = case.value("TEXT") else {
			panic!("expected two values");
		};
		assert!(matches!(address.val, Val::MemoryOffset { offset: 0, .. }));
		assert_eq!(address.scalar, Primitive::U64);
		assert_eq!(*length, ConstScalar::u64(3));
		assert_eq!(case.pointee(*address).0.memory, case.memory("wide"));
	}

	/// `Memory::DATA_END` is known once the program's data is laid out: its
	/// value is the memory's data end, as wide as the memory's addresses.
	#[test]
	fn data_end_is_a_late_bound_address() {
		let case = TestCase::new(indoc! {r#"
				memory wide: u64;
				const END: wide::*u8 = wide::DATA_END;
			"#});
		case.diagnostics().assert_none();
		let [end] = case.value("END") else {
			panic!("expected one value");
		};
		assert_eq!(
			end.val,
			Val::DataEnd {
				memory: case.memory("wide")
			}
		);
		assert_eq!(end.scalar, Primitive::U64);
	}

	#[test]
	fn a_constant_naming_another_shares_its_allocation() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const ORIGINAL: heap::&[u8] = "shared";
				const COPY: heap::&[u8] = ORIGINAL;
			"#});
		case.diagnostics().assert_none();
		assert_eq!(case.value("COPY"), case.value("ORIGINAL"));
	}

	#[test]
	fn an_aggregate_holds_an_address_among_its_values() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				struct Text(len: u8, bytes: heap::&[u8]);
				const GREETING: Text = Text(5, "hello");
			"#});
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
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func make() -> heap::&u8 { loop {} }
				const P: heap::&u8 = make();
			"#});
		case.diagnostics()
			.assert_error(DiagnosticCode::NotConstEvaluatable);
	}

	#[test]
	fn a_struct_nested_in_itself_with_other_arguments_is_evaluated() {
		let case = TestCase::new(indoc! {r#"
				struct Pair<T>(a: T, b: T);
				const P: Pair<Pair<u8>> = Pair(Pair(1, 2), Pair(3, 4));
			"#});
		case.diagnostics().assert_none();
		assert_eq!(
			case.value("P"),
			[1, 2, 3, 4].map(ConstScalar::u8).as_slice()
		);
	}

	/// The address and the length of the slice constant `name`, and the
	/// allocation it points to.
	fn slice<'c>(case: &'c TestCase, name: &str) -> (&'c Allocation, u64) {
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
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				struct Mixed(a: u8, b: u32);
				const WORDS: heap::&[u32] = [1, 2, 0x01020304];
				const SIGNED: heap::&[i8] = [-1, 2];
				const FLAGS: heap::&[Bool] = [True, False];
				const STRUCTS: heap::&[Mixed; 2] = [Mixed(1, 2), Mixed(3, 4)];
			"#});
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
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const NESTED: heap::&[heap::&[u8]] = [[1], [2, 3]];
				const NAMES: heap::&[heap::&[u8]] = ["ab", "c"];
			"#});
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
			for (&(_, target), contents) in outer.relocations.iter().zip(inner)
			{
				let AddressTarget::Allocation(alloc) = target else {
					panic!("expected an address into an allocation");
				};
				assert_eq!(
					&*case.sema.solver.allocations[usize::from(alloc)].bytes,
					contents,
					"{name}"
				);
			}
		}
	}

	#[test]
	fn a_repeat_writes_its_value_count_times() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const SIZE: u32 = 2;
				const SEVENS: heap::&[u16; 3] = [7; 3];
				const ZEROS: heap::&[u8] = [0; SIZE];
				const NINES: heap::&[u8; TWO] = [9; _];
				const TWO: u32 = SIZE;
			"#});
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
		let case = TestCase::new(indoc! {r#"
				memory wide: u64;
				const NAMES: wide::&[wide::&[u8]] = ["a"];
			"#});
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
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func one() -> u8 { 1 }
				const BAD: heap::&[u8] = [1, one()];
			"#});
		case.diagnostics()
			.assert_error(DiagnosticCode::NotConstEvaluatable);
	}

	#[test]
	fn a_repeat_of_a_zero_sized_value_takes_no_bytes() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const UNITS: heap::&[()] = [(); 3];
			"#});
		case.diagnostics().assert_none();
		let (units, len) = slice(&case, "UNITS");
		assert_eq!(len, 3);
		assert!(units.bytes.is_empty());
	}

	#[test]
	fn static_data_of_more_than_4_gib_is_reported() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const BIG: heap::&[u64] = [0; 1000000000];
			"#});
		case.diagnostics()
			.assert_error(DiagnosticCode::ConstEvaluationFailed);
	}

	fn exact(case: &TestCase, name: &str) -> i128 {
		match case.state(name) {
			ConstValueState::Exact(value) => *value,
			state => panic!("expected `{name}` to be untyped: {state:?}"),
		}
	}

	#[test]
	fn an_untyped_float_preserves_its_exact_value_until_each_use() {
		const TEXT: &str =
			"1.0000000596046447753906250000000000000000000000000000001";
		let mut case = TestCase::new(&format!(
			"const F: const_float = {TEXT};\nconst NEG: const_float = -F;\nconst A: f32 = F;\nconst B: f64 = NEG;\nconst ZERO: const_float = -0.0e100;\nconst Z: f32 = ZERO;"
		));
		case.diagnostics().assert_none();
		let ConstValueState::FloatLiteral(literal) = *case.state("F") else {
			panic!("an untyped float must retain its literal");
		};

		assert!(
			case.strings.get(TEXT).is_none(),
			"float text must not enter the name interner"
		);
		let direct = TEXT.parse::<f32>().unwrap();
		assert_ne!(
			direct.to_bits(),
			(TEXT.parse::<f64>().unwrap() as f32).to_bits(),
			"this value detects double rounding"
		);
		assert_eq!(case.value("A"), [ConstScalar::f32(direct)]);
		assert_eq!(
			case.value("B"),
			[ConstScalar::f64(-TEXT.parse::<f64>().unwrap())]
		);
		assert_eq!(case.value("Z"), [ConstScalar::f32(-0.0)]);
		// The numeric value must not depend on retaining the original source.
		let DeclKind::Const(index) = case.resolve(Tier::Value, "F") else {
			unreachable!()
		};
		let file = case
			.sema
			.decls
			.file_id(case.sema.decls.constants[usize::from(index)].loc);
		case.files.update(file, "edited".to_string());

		assert_eq!(
			case.sema
				.read_float_literal(
					literal,
					ConcreteType::Target(TypeIndex::F32)
				)
				.unwrap(),
			f64::from(direct)
		);
	}

	#[test]
	fn an_untyped_float_is_checked_at_each_use() {
		for (literal, target, code) in [
			("1e39", "f32", DiagnosticCode::FloatLiteralOverflow),
			("1e-50", "f32", DiagnosticCode::FloatLiteralUnderflow),
			("1e400", "f64", DiagnosticCode::FloatLiteralOverflow),
			("1e-400", "f64", DiagnosticCode::FloatLiteralUnderflow),
			(
				"1e999999999999999999999999999999999999999999",
				"f64",
				DiagnosticCode::FloatLiteralOverflow,
			),
			(
				"1e-999999999999999999999999999999999999999999",
				"f64",
				DiagnosticCode::FloatLiteralUnderflow,
			),
		] {
			let case = TestCase::new(&format!(
				"const F: const_float = {literal}; const A: {target} = F;"
			));
			case.diagnostics().assert_codes(&[code]);
		}
		TestCase::new(
			"const HUGE: const_float = 1e400; const TINY: const_float = 1e-400;",
		)
		.diagnostics()
		.assert_none();
	}

	#[test]
	fn an_untyped_float_has_no_default_and_no_binary_arithmetic_yet() {
		for (source, code) in [
			(
				"const F: const_float = 1.25; func f() { local x = F; }",
				DiagnosticCode::TypeAnnotationRequired,
			),
			(
				"const F: const_float = 1.0 + 2.0;",
				DiagnosticCode::UnsupportedExpression,
			),
			(
				"const F: const_float = 1.0 / 3.0;",
				DiagnosticCode::UnsupportedExpression,
			),
			("const F: const_float = 1;", DiagnosticCode::TypeMistmatch),
			(
				"const F: const_float = 1.25; const BAD: u32 = F;",
				DiagnosticCode::UnableToCoerce,
			),
			(
				"func f() -> f64 { 1.25 } const F: f64 = f();",
				DiagnosticCode::NotConstEvaluatable,
			),
		] {
			TestCase::new(source).diagnostics().assert_codes(&[code]);
		}
	}

	#[test]
	fn untyped_float_references_keep_cycle_detection() {
		TestCase::new("const A: const_float = B; const B: const_float = A;")
			.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicConstant]);
	}

	#[test]
	fn an_untyped_constant_takes_the_type_of_each_use() {
		let case = TestCase::new(indoc! {r#"
				const X: const_int = 200 + 55;
				const A: u8 = X;
				const B: i64 = -X;
				const C: u32 = X * 2;
				const F: f32 = X;
				const U: const_char = 'u';
				const CODE: u8 = U;
				const LETTER: Char = U;
			"#});
		case.diagnostics().assert_none();
		assert_eq!(exact(&case, "X"), 255);
		assert_eq!(case.value("A"), [ConstScalar::u8(255)]);
		assert_eq!(case.value("B"), [ConstScalar::i64(-255)]);
		assert_eq!(case.value("C"), [ConstScalar::u32(510)]);
		assert_eq!(case.value("F"), [ConstScalar::f32(255.0)]);
		assert_eq!(exact(&case, "U"), 117);
		assert_eq!(case.value("CODE"), [ConstScalar::u8(117)]);
		assert_eq!(case.value("LETTER"), [ConstScalar::char('u')]);
	}

	/// The value has no type yet, so nothing in between is bounded by one.
	/// A typed use types each operand, as it would literals: `BIG >> 66` in a
	/// `u8` is `BIG` as a `u8`.
	#[test]
	fn an_untyped_constant_is_computed_exactly() {
		let case = TestCase::new(indoc! {r#"
				const BIG: const_int = 1 << 70;
				const SHIFTED: const_int = BIG >> 66;
				const SMALL: u8 = SHIFTED;
				const TYPED_OPERAND: u8 = BIG >> 66;
				const MINUS_ONE: const_int = 0 - 1;
				const SIGNED: i8 = MINUS_ONE;
				const TOO_BIG: const_int = 1 << 127;
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::IntegerLiteralOutOfRange,
			DiagnosticCode::ConstEvaluationFailed,
		]);
		case.diagnostics().assert_error_saying(
			"constant `BIG` cannot be represented as `u8`",
		);
		case.diagnostics()
			.assert_error_saying("evaluation of constant `TOO_BIG` failed");
		assert_eq!(exact(&case, "BIG"), 1 << 70);
		assert_eq!(case.value("SMALL"), [ConstScalar::u8(16)]);
		assert_eq!(case.value("SIGNED"), [ConstScalar::i8(-1)]);
	}

	#[test]
	fn an_untyped_constant_is_checked_where_it_is_used() {
		let case = TestCase::new(indoc! {r#"
				const X: const_int = 300;
				const MINUS: const_int = -1;
				const A: u8 = X;
				const B: u16 = X;
				func f() -> u32 { MINUS }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::IntegerLiteralOutOfRange,
			DiagnosticCode::IntegerLiteralOutOfRange,
		]);
		case.diagnostics()
			.assert_error_saying("constant `X` cannot be represented as `u8`");
		case.diagnostics().assert_error_saying(
			"constant `MINUS` cannot be represented as `u32`",
		);
		assert_eq!(case.value("B"), [ConstScalar::u16(300)]);
	}

	/// No default type: an untyped constant needs a use that gives one, as
	/// a literal does.
	#[test]
	fn an_untyped_constant_has_no_default_type() {
		let case = TestCase::new(indoc! {r#"
				const X: const_int = 4;
				func f() { local x = X; }
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeAnnotationRequired]);
	}

	#[test]
	fn an_untyped_constant_holds_only_its_kind() {
		let case = TestCase::new(indoc! {r#"
				const LETTER: const_int = 'a';
				const TYPED: u32 = 4;
				const NAMED: const_int = TYPED;
				const NUMBER: const_char = 'a' + 1;
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
		]);
		assert_eq!(exact(&case, "NUMBER"), 98);
	}

	/// A length is a count: an untyped constant is representable as it by
	/// value.
	#[test]
	fn an_untyped_constant_is_an_array_length() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const N: const_int = 2 * 2;
				const NEGATIVE: const_int = -4;
				const HUGE: const_int = 1 << 40;
				const S: heap::&[u8; N] = "abcd";
				const T: heap::&[u8; NEGATIVE] = "abcd";
				func g(p: heap::&[u8; HUGE]) {}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::IntegerLiteralOutOfRange,
			DiagnosticCode::IntegerLiteralOutOfRange,
		]);
		case.diagnostics().assert_error_saying(
			"an array's length is a count, but `NEGATIVE` is `-4`",
		);
		let [address, ..] = case.value("S") else {
			panic!("expected an address");
		};
		assert_eq!(*case.pointee(*address).0.bytes, *b"abcd");
	}
}
