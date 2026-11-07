//! Expand compiler-provided function implementations, never source names.

use super::{Body, ExprIdx, FunctionInstance, FunctionState, Lowerer, mir};
use crate::tir::bounds::AssumptionEnvIdx;
use crate::tir::intrinsics::Intrinsic;
use crate::tir::types::Type;

impl Lowerer<'_, '_, '_, '_> {
	pub(super) fn lower_intrinsic(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		callee: FunctionInstance,
		intrinsic: Intrinsic,
		args: ExprIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		// `size_of<T, Mem>()`/`align_of<T, Mem>()` are `T`'s layout, a
		// constant of `Mem::Size`; they take no arguments.
		if let Intrinsic::SizeOf | Intrinsic::AlignOf = intrinsic {
			let [value_type, _] = *self.context.types.list(callee.args) else {
				unreachable!("`size_of` and `align_of` take `T` and `Mem`")
			};
			let Ok(Some(layout)) = self
				.context
				.memory_layout(AssumptionEnvIdx::ROOT, value_type)
			else {
				self.unsupported(
					state.file_id,
					body.span(expr),
					"the layout of a type with no linear-memory layout",
				)?;
				unreachable!()
			};
			let value = match intrinsic {
				Intrinsic::SizeOf => layout.size,
				_ => layout.align,
			};
			let value = state.push(
				mir::ExprKind::Int {
					value: i64::from(value),
				},
				ty,
			);
			// The arguments are `()`; they still run.
			let args = self.lower_expr(body, state, args)?;
			return Ok(self.sequence(state, vec![args], value));
		}

		let mut prefix = Vec::new();
		// A lone argument is its parameter's value, so it must not be
		// unpacked even when that value is itself a tuple (`transmute((a, b))`).
		let params =
			self.context.functions[usize::from(callee.function)].param_types;
		let arguments = if params.len() == 1 {
			vec![self.lower_expr(body, state, args)?]
		} else {
			self.lower_arguments(body, state, args, &mut prefix)?
		};
		if let Some(at) = arguments
			.iter()
			.position(|&arg| state.ty(arg) == mir::ValueType::Never)
		{
			// A diverging argument prevents the operation from executing. Do
			// not feed `Never` to a scalar instruction expecting a real value.
			// The arguments after it are kept in the tree, after it, where
			// they never run.
			let mut statements = prefix;
			for (position, &value) in arguments.iter().enumerate() {
				statements.push(if position == at {
					value
				} else {
					state.push(
						mir::ExprKind::Drop { value },
						mir::ValueType::Unit,
					)
				});
			}
			let statements = state.list(statements);
			return Ok(state.push(
				mir::ExprKind::Sequence { statements },
				mir::ValueType::Never,
			));
		}
		self.expand_intrinsic(state, callee, intrinsic, arguments, prefix, ty)
	}

	/// `intrinsic`'s operation over `arguments`, its operands already lowered
	/// (one per parameter), after `prefix`. A call site lowers the operands
	/// from its arguments; an intrinsic's own function
	/// (`lower_intrinsic_function`) reads them from its parameters.
	pub(super) fn expand_intrinsic(
		&mut self,
		state: &mut FunctionState,
		callee: FunctionInstance,
		intrinsic: Intrinsic,
		arguments: Vec<mir::ExprId>,
		mut prefix: Vec<mir::ExprId>,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let mut arguments = arguments.into_iter();
		macro_rules! operand {
			() => {
				arguments.next().expect("std intrinsic operand")
			};
		}
		macro_rules! unary {
			($op:ident) => {
				mir::ExprKind::Unary {
					op: mir::UnaryOp::$op,
					value: operand!(),
				}
			};
		}
		macro_rules! binary {
			($op:ident) => {
				mir::ExprKind::Binary {
					op: mir::BinaryOp::$op,
					lhs: operand!(),
					rhs: operand!(),
				}
			};
		}
		macro_rules! compare {
			($op:ident) => {
				mir::ExprKind::Compare {
					op: mir::CompareOp::$op,
					lhs: operand!(),
					rhs: operand!(),
				}
			};
		}
		macro_rules! convert {
			($op:ident) => {
				mir::ExprKind::Convert {
					op: mir::ConvertOp::$op,
					value: operand!(),
				}
			};
		}
		// Wasm has no integer negation or bitwise not: `0 - x`, `x ^ -1`.
		macro_rules! with_constant {
			($op:ident, $constant:expr, $first:expr) => {{
				let value = operand!();
				let constant =
					state.push(mir::ExprKind::Int { value: $constant }, ty);
				let (lhs, rhs) = if $first {
					(constant, value)
				} else {
					(value, constant)
				};
				mir::ExprKind::Binary {
					op: mir::BinaryOp::$op,
					lhs,
					rhs,
				}
			}};
		}
		let kind = match intrinsic {
			Intrinsic::Trap => mir::ExprKind::Unreachable,
			Intrinsic::I32Neg | Intrinsic::I64Neg => {
				with_constant!(Sub, 0, true)
			}
			Intrinsic::F32Neg | Intrinsic::F64Neg => unary!(Neg),
			Intrinsic::I32BitNot | Intrinsic::I64BitNot => {
				with_constant!(Xor, -1, false)
			}
			Intrinsic::I32Eqz => unary!(Eqz),
			Intrinsic::F32Sqrt | Intrinsic::F64Sqrt => unary!(Sqrt),
			Intrinsic::F32Abs | Intrinsic::F64Abs => unary!(Abs),
			Intrinsic::F32Floor | Intrinsic::F64Floor => unary!(Floor),
			Intrinsic::F32Ceil | Intrinsic::F64Ceil => unary!(Ceil),
			Intrinsic::F32Trunc | Intrinsic::F64Trunc => unary!(Trunc),
			Intrinsic::F32Nearest | Intrinsic::F64Nearest => unary!(Nearest),
			Intrinsic::I32Add
			| Intrinsic::I64Add
			| Intrinsic::F32Add
			| Intrinsic::F64Add => binary!(Add),
			Intrinsic::I32Sub
			| Intrinsic::I64Sub
			| Intrinsic::F32Sub
			| Intrinsic::F64Sub => binary!(Sub),
			Intrinsic::I32Mul
			| Intrinsic::I64Mul
			| Intrinsic::F32Mul
			| Intrinsic::F64Mul => binary!(Mul),
			Intrinsic::I32DivS | Intrinsic::I64DivS => binary!(DivS),
			Intrinsic::I32DivU | Intrinsic::I64DivU => binary!(DivU),
			Intrinsic::F32Div | Intrinsic::F64Div => binary!(Div),
			Intrinsic::I32RemS | Intrinsic::I64RemS => binary!(RemS),
			Intrinsic::I32RemU | Intrinsic::I64RemU => binary!(RemU),
			Intrinsic::I32BitAnd | Intrinsic::I64BitAnd => binary!(And),
			Intrinsic::I32BitOr | Intrinsic::I64BitOr => binary!(Or),
			Intrinsic::I32BitXor | Intrinsic::I64BitXor => binary!(Xor),
			Intrinsic::I32Shl | Intrinsic::I64Shl => binary!(Shl),
			Intrinsic::I32ShrS | Intrinsic::I64ShrS => binary!(ShrS),
			Intrinsic::I32ShrU | Intrinsic::I64ShrU => binary!(ShrU),
			Intrinsic::I32Eq
			| Intrinsic::I64Eq
			| Intrinsic::F32Eq
			| Intrinsic::F64Eq => compare!(Eq),
			Intrinsic::I32Ne
			| Intrinsic::I64Ne
			| Intrinsic::F32Ne
			| Intrinsic::F64Ne => compare!(Ne),
			Intrinsic::I32LtS | Intrinsic::I64LtS => compare!(LtS),
			Intrinsic::I32LtU | Intrinsic::I64LtU => compare!(LtU),
			Intrinsic::F32Lt | Intrinsic::F64Lt => compare!(Lt),
			Intrinsic::I32LeS | Intrinsic::I64LeS => compare!(LeS),
			Intrinsic::I32LeU | Intrinsic::I64LeU => compare!(LeU),
			Intrinsic::F32Le | Intrinsic::F64Le => compare!(Le),
			Intrinsic::I32GtS | Intrinsic::I64GtS => compare!(GtS),
			Intrinsic::I32GtU | Intrinsic::I64GtU => compare!(GtU),
			Intrinsic::F32Gt | Intrinsic::F64Gt => compare!(Gt),
			Intrinsic::I32GeS | Intrinsic::I64GeS => compare!(GeS),
			Intrinsic::I32GeU | Intrinsic::I64GeU => compare!(GeU),
			Intrinsic::F32Ge | Intrinsic::F64Ge => compare!(Ge),
			Intrinsic::F32Min | Intrinsic::F64Min => binary!(Min),
			Intrinsic::F32Max | Intrinsic::F64Max => binary!(Max),
			Intrinsic::F32Copysign | Intrinsic::F64Copysign => {
				binary!(Copysign)
			}
			Intrinsic::I64ExtendI32S => convert!(ExtendS),
			Intrinsic::I64ExtendI32U => convert!(ExtendU),
			Intrinsic::I32WrapI64 => convert!(Wrap),
			Intrinsic::F32ConvertI32
			| Intrinsic::F32ConvertI64
			| Intrinsic::F64ConvertI32
			| Intrinsic::F64ConvertI64 => convert!(ConvertS),
			Intrinsic::F32ConvertU32
			| Intrinsic::F32ConvertU64
			| Intrinsic::F64ConvertU32
			| Intrinsic::F64ConvertU64 => convert!(ConvertU),
			Intrinsic::I32TruncF32
			| Intrinsic::I32TruncF64
			| Intrinsic::I64TruncF32
			| Intrinsic::I64TruncF64 => convert!(TruncS),
			Intrinsic::U32TruncF32
			| Intrinsic::U32TruncF64
			| Intrinsic::U64TruncF32
			| Intrinsic::U64TruncF64 => convert!(TruncU),
			Intrinsic::F64PromoteF32 => convert!(Promote),
			Intrinsic::F32DemoteF64 => convert!(Demote),
			Intrinsic::I32ReinterpretF32
			| Intrinsic::F32ReinterpretI32
			| Intrinsic::I64ReinterpretF64
			| Intrinsic::F64ReinterpretI64 => convert!(Reinterpret),
			// Its bounds give both types the same Wasm values, which are one
			// MIR type: the operand is the value.
			Intrinsic::Transmute => {
				let value = operand!();
				debug_assert!(
					state.ty(value) == ty,
					"`transmute`'s two types are one MIR type"
				);
				assert!(
					arguments.next().is_none(),
					"std intrinsic operand count"
				);
				return Ok(self.sequence(state, prefix, value));
			}
			// `global_get<G>(g)`/`global_set<G>(g, value)`: the handle `g` is
			// zero-sized and runs for its effects; `G` names the global, whose
			// value is one scalar (`Meters(u32)` is its `I32`).
			Intrinsic::GlobalGet | Intrinsic::GlobalSet => {
				let id = self.global_of(callee)?;
				prefix.push(operand!());
				let value = if intrinsic == Intrinsic::GlobalGet {
					debug_assert!(ty == self.globals[usize::from(id)].ty);
					state.push(mir::ExprKind::Global { id }, ty)
				} else {
					let value = operand!();
					state.push(mir::ExprKind::GlobalSet { id, value }, ty)
				};
				assert!(
					arguments.next().is_none(),
					"std intrinsic operand count"
				);
				return Ok(self.sequence(state, prefix, value));
			}
			// `memory_size<Mem>(mem)`, `memory_grow<Mem>(mem, delta)`: the
			// handle `mem` is zero-sized and runs for its effects; `Mem`
			// names the memory.
			Intrinsic::MemorySize => {
				let memory = self.memory_argument(callee, 0);
				prefix.push(operand!());
				mir::ExprKind::MemorySize { memory }
			}
			Intrinsic::MemoryGrow => {
				let memory = self.memory_argument(callee, 0);
				prefix.push(operand!());
				mir::ExprKind::MemoryGrow {
					memory,
					delta: operand!(),
				}
			}
			// `memory_fill<Mem>(dst, val, len)`.
			Intrinsic::MemoryFill => mir::ExprKind::MemoryFill {
				memory: self.memory_argument(callee, 0),
				dst: operand!(),
				value: operand!(),
				len: operand!(),
			},
			// `memory_copy<Size, SrcMem, DstMem>(dst, src, len)`.
			Intrinsic::MemoryCopy => mir::ExprKind::MemoryCopy {
				src_memory: self.memory_argument(callee, 1),
				dst_memory: self.memory_argument(callee, 2),
				dst: operand!(),
				src: operand!(),
				len: operand!(),
			},
			Intrinsic::SizeOf | Intrinsic::AlignOf => {
				unreachable!(
					"lowered by its call site before its arguments, and \
					 generic, so it has no function of its own"
				)
			}
		};
		assert!(arguments.next().is_none(), "std intrinsic operand count");
		let value = state.push(kind, ty);
		Ok(self.sequence(state, prefix, value))
	}

	/// The memory an instance of a memory intrinsic names as its type
	/// argument at `position`.
	fn memory_argument(
		&mut self,
		callee: FunctionInstance,
		position: usize,
	) -> mir::MemoryId {
		let memory = self.context.types.list(callee.args)[position];
		self.memory_of_type(memory)
	}

	/// The global a `global_get<G>`/`global_set<G>` instance names: its one
	/// type argument, a global's handle type.
	fn global_of(
		&mut self,
		callee: FunctionInstance,
	) -> Result<mir::GlobalId, ()> {
		let [handle] = *self.context.types.list(callee.args) else {
			unreachable!("`global_get` and `global_set` take one type argument")
		};
		let Type::Global { global_index } = *self.context.types.resolve(handle)
		else {
			unreachable!("an instance's `G: Global` is a global's handle type")
		};
		self.global(global_index)
	}
}
