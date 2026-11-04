//! Expand compiler-provided function implementations, never source names.

use super::{Body, ExprIdx, FunctionState, Lowerer, mir};
use crate::tir::intrinsics::Intrinsic;

impl Lowerer<'_, '_, '_, '_> {
	pub(super) fn lower_intrinsic(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		intrinsic: Intrinsic,
		args: ExprIdx,
		ty: mir::ValueType,
	) -> Result<mir::Expression, ()> {
		// Generic memory/global operations are recognized implementations,
		// not ordinary functions awaiting a body or monomorphization. Keep
		// their checkpoint boundary explicit until those features can lower.
		match intrinsic {
			Intrinsic::MemoryGrow
			| Intrinsic::MemorySize
			| Intrinsic::MemoryFill
			| Intrinsic::MemoryCopy
			| Intrinsic::GlobalGet
			| Intrinsic::GlobalSet
			| Intrinsic::Transmute
			| Intrinsic::SizeOf
			| Intrinsic::AlignOf => {
				self.unsupported(
					state.file_id,
					body.span(expr),
					&format!("the compiler intrinsic {intrinsic:?}"),
				)?;
				unreachable!()
			}
			_ => {}
		}

		let mut prefix = Vec::new();
		let mut arguments =
			self.lower_arguments(body, state, args, &mut prefix)?;
		if let Some(at) = arguments
			.iter()
			.position(|arg| arg.ty == mir::ValueType::Never)
		{
			// A diverging argument prevents the operation from executing. Do
			// not feed `Never` to a scalar instruction expecting a real value.
			let divergent = arguments.remove(at);
			prefix.extend(arguments.into_iter().take(at).map(|value| {
				mir::Expression {
					kind: mir::ExprKind::Drop {
						value: Box::new(value),
					},
					ty: mir::ValueType::Unit,
				}
			}));
			return Ok(self.sequence(state, prefix, divergent));
		}
		let mut arguments = arguments.into_iter();
		macro_rules! unary {
			($kind:ident) => {
				mir::ExprKind::$kind {
					value: Box::new(
						arguments.next().expect("std intrinsic operand"),
					),
				}
			};
		}
		macro_rules! binary {
			($kind:ident) => {
				mir::ExprKind::$kind {
					left: Box::new(
						arguments.next().expect("std intrinsic left operand"),
					),
					right: Box::new(
						arguments.next().expect("std intrinsic right operand"),
					),
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
			Intrinsic::I32Shl => binary!(LeftShift),
			Intrinsic::I64Shl => binary!(LeftShift),
			Intrinsic::I32ShrS => binary!(RightShift),
			Intrinsic::I32ShrU => binary!(RightShift),
			Intrinsic::I64ShrS => binary!(RightShift),
			Intrinsic::I64ShrU => binary!(RightShift),
			Intrinsic::I32Eq => binary!(Eq),
			Intrinsic::I64Eq => binary!(Eq),
			Intrinsic::F32Eq => binary!(Eq),
			Intrinsic::F64Eq => binary!(Eq),
			Intrinsic::I32Ne => binary!(NotEq),
			Intrinsic::I64Ne => binary!(NotEq),
			Intrinsic::F32Ne => binary!(NotEq),
			Intrinsic::F64Ne => binary!(NotEq),
			Intrinsic::I32LtS => binary!(Less),
			Intrinsic::I32LtU => binary!(Less),
			Intrinsic::I64LtS => binary!(Less),
			Intrinsic::I64LtU => binary!(Less),
			Intrinsic::F32Lt => binary!(Less),
			Intrinsic::F64Lt => binary!(Less),
			Intrinsic::I32LeS => binary!(LessEq),
			Intrinsic::I32LeU => binary!(LessEq),
			Intrinsic::I64LeS => binary!(LessEq),
			Intrinsic::I64LeU => binary!(LessEq),
			Intrinsic::F32Le => binary!(LessEq),
			Intrinsic::F64Le => binary!(LessEq),
			Intrinsic::I32GtS => binary!(Greater),
			Intrinsic::I32GtU => binary!(Greater),
			Intrinsic::I64GtS => binary!(Greater),
			Intrinsic::I64GtU => binary!(Greater),
			Intrinsic::F32Gt => binary!(Greater),
			Intrinsic::F64Gt => binary!(Greater),
			Intrinsic::I32GeS => binary!(GreaterEq),
			Intrinsic::I32GeU => binary!(GreaterEq),
			Intrinsic::I64GeS => binary!(GreaterEq),
			Intrinsic::I64GeU => binary!(GreaterEq),
			Intrinsic::F32Ge => binary!(GreaterEq),
			Intrinsic::F64Ge => binary!(GreaterEq),
			Intrinsic::F32Min => binary!(Min),
			Intrinsic::F64Min => binary!(Min),
			Intrinsic::F32Max => binary!(Max),
			Intrinsic::F64Max => binary!(Max),
			Intrinsic::F32Copysign => binary!(Copysign),
			Intrinsic::F64Copysign => binary!(Copysign),
			Intrinsic::I64ExtendI32S => unary!(I64ExtendI32S),
			Intrinsic::I64ExtendI32U => unary!(I64ExtendI32U),
			Intrinsic::I32WrapI64 => unary!(I32WrapI64),
			Intrinsic::F32ConvertI32 => unary!(F32ConvertI32),
			Intrinsic::F32ConvertU32 => unary!(F32ConvertU32),
			Intrinsic::F32ConvertI64 => unary!(F32ConvertI64),
			Intrinsic::F32ConvertU64 => unary!(F32ConvertU64),
			Intrinsic::F64ConvertI32 => unary!(F64ConvertI32),
			Intrinsic::F64ConvertU32 => unary!(F64ConvertU32),
			Intrinsic::F64ConvertI64 => unary!(F64ConvertI64),
			Intrinsic::F64ConvertU64 => unary!(F64ConvertU64),
			Intrinsic::I32TruncF32 => unary!(I32TruncF32),
			Intrinsic::U32TruncF32 => unary!(U32TruncF32),
			Intrinsic::I32TruncF64 => unary!(I32TruncF64),
			Intrinsic::U32TruncF64 => unary!(U32TruncF64),
			Intrinsic::I64TruncF32 => unary!(I64TruncF32),
			Intrinsic::U64TruncF32 => unary!(U64TruncF32),
			Intrinsic::I64TruncF64 => unary!(I64TruncF64),
			Intrinsic::U64TruncF64 => unary!(U64TruncF64),
			Intrinsic::F64PromoteF32 => unary!(F64PromoteF32),
			Intrinsic::F32DemoteF64 => unary!(F32DemoteF64),
			Intrinsic::I32ReinterpretF32 => unary!(I32ReinterpretF32),
			Intrinsic::F32ReinterpretI32 => unary!(F32ReinterpretI32),
			Intrinsic::I64ReinterpretF64 => unary!(I64ReinterpretF64),
			Intrinsic::F64ReinterpretI64 => unary!(F64ReinterpretI64),
			Intrinsic::MemoryGrow
			| Intrinsic::MemorySize
			| Intrinsic::MemoryFill
			| Intrinsic::MemoryCopy
			| Intrinsic::GlobalGet
			| Intrinsic::GlobalSet
			| Intrinsic::Transmute
			| Intrinsic::SizeOf
			| Intrinsic::AlignOf => unreachable!("diagnosed before argument lowering"),
		};
		assert!(arguments.next().is_none(), "std intrinsic operand count");
		Ok(self.sequence(state, prefix, mir::Expression { kind, ty }))
	}
}
