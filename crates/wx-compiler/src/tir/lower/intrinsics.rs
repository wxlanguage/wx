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
		let kind = match intrinsic {
			Intrinsic::Trap => mir::ExprKind::Unreachable,
			Intrinsic::I32Neg => unary!(Neg),
			Intrinsic::I64Neg => unary!(Neg),
			Intrinsic::F32Neg => unary!(Neg),
			Intrinsic::F64Neg => unary!(Neg),
			Intrinsic::I32BitNot => unary!(BitNot),
			Intrinsic::I64BitNot => unary!(BitNot),
			Intrinsic::I32Eqz => unary!(Eqz),
			Intrinsic::F32Sqrt => unary!(Sqrt),
			Intrinsic::F64Sqrt => unary!(Sqrt),
			Intrinsic::F32Abs => unary!(Abs),
			Intrinsic::F64Abs => unary!(Abs),
			Intrinsic::F32Floor => unary!(Floor),
			Intrinsic::F64Floor => unary!(Floor),
			Intrinsic::F32Ceil => unary!(Ceil),
			Intrinsic::F64Ceil => unary!(Ceil),
			Intrinsic::F32Trunc => unary!(Trunc),
			Intrinsic::F64Trunc => unary!(Trunc),
			Intrinsic::F32Nearest => unary!(Nearest),
			Intrinsic::F64Nearest => unary!(Nearest),
			Intrinsic::I32Add => binary!(Add),
			Intrinsic::I64Add => binary!(Add),
			Intrinsic::F32Add => binary!(Add),
			Intrinsic::F64Add => binary!(Add),
			Intrinsic::I32Sub => binary!(Sub),
			Intrinsic::I64Sub => binary!(Sub),
			Intrinsic::F32Sub => binary!(Sub),
			Intrinsic::F64Sub => binary!(Sub),
			Intrinsic::I32Mul => binary!(Mul),
			Intrinsic::I64Mul => binary!(Mul),
			Intrinsic::F32Mul => binary!(Mul),
			Intrinsic::F64Mul => binary!(Mul),
			Intrinsic::I32DivS => binary!(Div),
			Intrinsic::I32DivU => binary!(Div),
			Intrinsic::I64DivS => binary!(Div),
			Intrinsic::I64DivU => binary!(Div),
			Intrinsic::F32Div => binary!(Div),
			Intrinsic::F64Div => binary!(Div),
			Intrinsic::I32RemS => binary!(Rem),
			Intrinsic::I32RemU => binary!(Rem),
			Intrinsic::I64RemS => binary!(Rem),
			Intrinsic::I64RemU => binary!(Rem),
			Intrinsic::I32BitAnd => binary!(BitAnd),
			Intrinsic::I64BitAnd => binary!(BitAnd),
			Intrinsic::I32BitOr => binary!(BitOr),
			Intrinsic::I64BitOr => binary!(BitOr),
			Intrinsic::I32BitXor => binary!(BitXor),
			Intrinsic::I64BitXor => binary!(BitXor),
			Intrinsic::I32Shl => binary!(Shl),
			Intrinsic::I64Shl => binary!(Shl),
			Intrinsic::I32ShrS => binary!(Shr),
			Intrinsic::I32ShrU => binary!(Shr),
			Intrinsic::I64ShrS => binary!(Shr),
			Intrinsic::I64ShrU => binary!(Shr),
			Intrinsic::I32Eq => compare!(Eq),
			Intrinsic::I64Eq => compare!(Eq),
			Intrinsic::F32Eq => compare!(Eq),
			Intrinsic::F64Eq => compare!(Eq),
			Intrinsic::I32Ne => compare!(Ne),
			Intrinsic::I64Ne => compare!(Ne),
			Intrinsic::F32Ne => compare!(Ne),
			Intrinsic::F64Ne => compare!(Ne),
			Intrinsic::I32LtS => compare!(Lt),
			Intrinsic::I32LtU => compare!(Lt),
			Intrinsic::I64LtS => compare!(Lt),
			Intrinsic::I64LtU => compare!(Lt),
			Intrinsic::F32Lt => compare!(Lt),
			Intrinsic::F64Lt => compare!(Lt),
			Intrinsic::I32LeS => compare!(Le),
			Intrinsic::I32LeU => compare!(Le),
			Intrinsic::I64LeS => compare!(Le),
			Intrinsic::I64LeU => compare!(Le),
			Intrinsic::F32Le => compare!(Le),
			Intrinsic::F64Le => compare!(Le),
			Intrinsic::I32GtS => compare!(Gt),
			Intrinsic::I32GtU => compare!(Gt),
			Intrinsic::I64GtS => compare!(Gt),
			Intrinsic::I64GtU => compare!(Gt),
			Intrinsic::F32Gt => compare!(Gt),
			Intrinsic::F64Gt => compare!(Gt),
			Intrinsic::I32GeS => compare!(Ge),
			Intrinsic::I32GeU => compare!(Ge),
			Intrinsic::I64GeS => compare!(Ge),
			Intrinsic::I64GeU => compare!(Ge),
			Intrinsic::F32Ge => compare!(Ge),
			Intrinsic::F64Ge => compare!(Ge),
			Intrinsic::F32Min => binary!(Min),
			Intrinsic::F64Min => binary!(Min),
			Intrinsic::F32Max => binary!(Max),
			Intrinsic::F64Max => binary!(Max),
			Intrinsic::F32Copysign => binary!(Copysign),
			Intrinsic::F64Copysign => binary!(Copysign),
			Intrinsic::I64ExtendI32S => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::I64ExtendI32U => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::I32WrapI64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F32ConvertI32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F32ConvertU32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F32ConvertI64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F32ConvertU64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F64ConvertI32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F64ConvertU32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F64ConvertI64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F64ConvertU64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::I32TruncF32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::U32TruncF32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::I32TruncF64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::U32TruncF64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::I64TruncF32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::U64TruncF32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::I64TruncF64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::U64TruncF64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F64PromoteF32 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::F32DemoteF64 => {
				mir::ExprKind::Convert { value: operand!() }
			}
			Intrinsic::I32ReinterpretF32 => {
				mir::ExprKind::Reinterpret { value: operand!() }
			}
			Intrinsic::F32ReinterpretI32 => {
				mir::ExprKind::Reinterpret { value: operand!() }
			}
			Intrinsic::I64ReinterpretF64 => {
				mir::ExprKind::Reinterpret { value: operand!() }
			}
			Intrinsic::F64ReinterpretI64 => {
				mir::ExprKind::Reinterpret { value: operand!() }
			}
			// Its bounds make both types flatten to the same Wasm values, so
			// it needs no type arguments: the operand's type and `ty` say it.
			Intrinsic::Transmute => {
				mir::ExprKind::Transmute { value: operand!() }
			}
			// `global_get<G>(g)`/`global_set<G>(g, value)`: the handle `g` is
			// zero-sized and runs for its effects; `G` names the global. The
			// module holds the value as its one scalar, which a one-value
			// pack (`Meters(u32)`) is read as and written from.
			Intrinsic::GlobalGet | Intrinsic::GlobalSet => {
				let id = self.global_of(callee)?;
				let scalar = self.globals[usize::from(id)].ty;
				prefix.push(operand!());
				let value = if intrinsic == Intrinsic::GlobalGet {
					let get = state.push(mir::ExprKind::Global { id }, scalar);
					if ty == scalar {
						get
					} else {
						state.push(mir::ExprKind::Transmute { value: get }, ty)
					}
				} else {
					let mut value = operand!();
					if state.ty(value) != scalar {
						value = state
							.push(mir::ExprKind::Transmute { value }, scalar);
					}
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
				unreachable!("lowered before its arguments")
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
