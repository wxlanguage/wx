use super::super::*;

impl<'tir> Builder<'tir> {
	pub(in crate::mir) fn lower_intrinsic(
		&mut self,
		func_ctx: &mut FunctionContext,
		name: SymbolU32,
		expr_ty: tir::TypeIndex,
		type_args: &[tir::TypeIndex],
		arguments: &[tir::Expression],
		sink: &mut Vec<Expression>,
	) -> Expression {
		let name_str = self.interner.resolve(name).unwrap();
		match name_str {
			"memory_grow" => {
				let memory = self.resolve_memory_id(type_args[0]);
				let delta = Box::new(self.lower_expression(
					func_ctx,
					&arguments[1],
					sink,
				));
				Expression {
					kind: ExprKind::MemoryGrow { memory, delta },
					ty: self.lower_type_index(expr_ty),
				}
			}
			"memory_size" => {
				let memory = self.resolve_memory_id(type_args[0]);
				Expression {
					kind: ExprKind::MemorySize { memory },
					ty: self.lower_type_index(expr_ty),
				}
			}
			"slice_len" => {
				let result_ty = self.lower_type_index(expr_ty);
				let slice_arg = &arguments[0];
				match &slice_arg.kind {
					tir::ExprKind::Local {
						scope_index,
						local_index,
					} => Expression {
						kind: ExprKind::AggregateGet {
							scope_index: ScopeIndex::new(u32::from(
								*scope_index,
							)),
							local_index: LocalIndex::new(u32::from(
								*local_index,
							)),
							value_index: PhysIndex::new(1),
						},
						ty: result_ty,
					},
					_ => {
						let slice_ty = self.lower_type_index(slice_arg.ty);
						let lowered =
							self.lower_expression(func_ctx, slice_arg, sink);
						let temp_idx = LocalIndex::new(
							func_ctx.frame[0].locals.len() as u32,
						);
						func_ctx.frame[0].locals.push(Local {
							ty: slice_ty,
							mutability: Mutability::Immutable,
						});
						sink.push(Expression {
							kind: ExprKind::LocalSet {
								scope_index: ScopeIndex::new(0),
								local_index: temp_idx,
								value: Box::new(lowered),
							},
							ty: ValueType::Unit,
						});
						Expression {
							kind: ExprKind::AggregateGet {
								scope_index: ScopeIndex::new(0),
								local_index: temp_idx,
								value_index: PhysIndex::new(1),
							},
							ty: result_ty,
						}
					}
				}
			}
			"slice_ptr" => {
				let result_ty = self.lower_type_index(expr_ty);
				let slice_arg = &arguments[0];
				match &slice_arg.kind {
					tir::ExprKind::Local {
						scope_index,
						local_index,
					} => Expression {
						kind: ExprKind::AggregateGet {
							scope_index: ScopeIndex::new(u32::from(
								*scope_index,
							)),
							local_index: LocalIndex::new(u32::from(
								*local_index,
							)),
							value_index: PhysIndex::new(0),
						},
						ty: result_ty,
					},
					_ => {
						let slice_ty = self.lower_type_index(slice_arg.ty);
						let lowered =
							self.lower_expression(func_ctx, slice_arg, sink);
						let temp_idx = LocalIndex::new(
							func_ctx.frame[0].locals.len() as u32,
						);
						func_ctx.frame[0].locals.push(Local {
							ty: slice_ty,
							mutability: Mutability::Immutable,
						});
						sink.push(Expression {
							kind: ExprKind::LocalSet {
								scope_index: ScopeIndex::new(0),
								local_index: temp_idx,
								value: Box::new(lowered),
							},
							ty: ValueType::Unit,
						});
						Expression {
							kind: ExprKind::AggregateGet {
								scope_index: ScopeIndex::new(0),
								local_index: temp_idx,
								value_index: PhysIndex::new(0),
							},
							ty: result_ty,
						}
					}
				}
			}
			"slice_from_parts" => {
				let data = self.lower_expression(func_ctx, &arguments[0], sink);
				let len = self.lower_expression(func_ctx, &arguments[1], sink);
				let result_ty = self.lower_type_index(expr_ty);
				Expression {
					kind: ExprKind::Aggregate {
						values: Box::new([data, len]),
					},
					ty: result_ty,
				}
			}
			"size_of" => {
				let layout = self.compute_layout(type_args[0]);
				Expression {
					kind: ExprKind::Int {
						value: layout.size as i64,
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"align_of" => {
				let layout = self.compute_layout(type_args[0]);
				Expression {
					kind: ExprKind::Int {
						value: layout.align as i64,
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"f32_sqrt" | "f64_sqrt" => Expression {
				kind: ExprKind::Sqrt {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_abs" | "f64_abs" => Expression {
				kind: ExprKind::Abs {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_floor" | "f64_floor" => Expression {
				kind: ExprKind::Floor {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_ceil" | "f64_ceil" => Expression {
				kind: ExprKind::Ceil {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_trunc" | "f64_trunc" => Expression {
				kind: ExprKind::Trunc {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_nearest" | "f64_nearest" => Expression {
				kind: ExprKind::Nearest {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_min" | "f64_min" => Expression {
				kind: ExprKind::Min {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_max" | "f64_max" => Expression {
				kind: ExprKind::Max {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_copysign" | "f64_copysign" => Expression {
				kind: ExprKind::Copysign {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_neg" | "i64_neg" | "f32_neg" | "f64_neg" => Expression {
				kind: ExprKind::Neg {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitnot" | "i64_bitnot" => Expression {
				kind: ExprKind::BitNot {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_eqz" => Expression {
				kind: ExprKind::Eqz {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_eq" | "i64_eq" | "f32_eq" | "f64_eq" => Expression {
				kind: ExprKind::Eq {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_ne" | "i64_ne" | "f32_ne" | "f64_ne" => Expression {
				kind: ExprKind::NotEq {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_lt" | "u32_lt" | "i64_lt" | "u64_lt" | "f32_lt" | "f64_lt" => {
				Expression {
					kind: ExprKind::Less {
						left: Box::new(self.lower_expression(
							func_ctx,
							&arguments[0],
							sink,
						)),
						right: Box::new(self.lower_expression(
							func_ctx,
							&arguments[1],
							sink,
						)),
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"i32_le" | "u32_le" | "i64_le" | "u64_le" | "f32_le" | "f64_le" => {
				Expression {
					kind: ExprKind::LessEq {
						left: Box::new(self.lower_expression(
							func_ctx,
							&arguments[0],
							sink,
						)),
						right: Box::new(self.lower_expression(
							func_ctx,
							&arguments[1],
							sink,
						)),
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"i32_gt" | "u32_gt" | "i64_gt" | "u64_gt" | "f32_gt" | "f64_gt" => {
				Expression {
					kind: ExprKind::Greater {
						left: Box::new(self.lower_expression(
							func_ctx,
							&arguments[0],
							sink,
						)),
						right: Box::new(self.lower_expression(
							func_ctx,
							&arguments[1],
							sink,
						)),
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"i32_ge" | "u32_ge" | "i64_ge" | "u64_ge" | "f32_ge" | "f64_ge" => {
				Expression {
					kind: ExprKind::GreaterEq {
						left: Box::new(self.lower_expression(
							func_ctx,
							&arguments[0],
							sink,
						)),
						right: Box::new(self.lower_expression(
							func_ctx,
							&arguments[1],
							sink,
						)),
					},
					ty: self.lower_type_index(expr_ty),
				}
			}
			"i32_add" | "i64_add" | "f32_add" | "f64_add" => Expression {
				kind: ExprKind::Add {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_sub" | "i64_sub" | "f32_sub" | "f64_sub" => Expression {
				kind: ExprKind::Sub {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_mul" | "i64_mul" | "f32_mul" | "f64_mul" => Expression {
				kind: ExprKind::Mul {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_div" | "u32_div" | "i64_div" | "u64_div" | "f32_div"
			| "f64_div" => Expression {
				kind: ExprKind::Div {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_rem" | "u32_rem" | "i64_rem" | "u64_rem" => Expression {
				kind: ExprKind::Rem {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitand" | "i64_bitand" => Expression {
				kind: ExprKind::BitAnd {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitor" | "i64_bitor" => Expression {
				kind: ExprKind::BitOr {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_bitxor" | "i64_bitxor" => Expression {
				kind: ExprKind::BitXor {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_shl" | "i64_shl" => Expression {
				kind: ExprKind::LeftShift {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_shr" | "u32_shr" | "i64_shr" | "u64_shr" => Expression {
				kind: ExprKind::RightShift {
					left: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
					right: Box::new(self.lower_expression(
						func_ctx,
						&arguments[1],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_extend_i32" => Expression {
				kind: ExprKind::I64ExtendI32S {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u64_extend_u32" => Expression {
				kind: ExprKind::I64ExtendI32U {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_wrap_i64" => Expression {
				kind: ExprKind::I32WrapI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_i32" => Expression {
				kind: ExprKind::F32ConvertI32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_u32" => Expression {
				kind: ExprKind::F32ConvertU32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_i64" => Expression {
				kind: ExprKind::F32ConvertI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_convert_u64" => Expression {
				kind: ExprKind::F32ConvertU64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_i32" => Expression {
				kind: ExprKind::F64ConvertI32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_u32" => Expression {
				kind: ExprKind::F64ConvertU32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_i64" => Expression {
				kind: ExprKind::F64ConvertI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_convert_u64" => Expression {
				kind: ExprKind::F64ConvertU64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_trunc_f32" => Expression {
				kind: ExprKind::I32TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u32_trunc_f32" => Expression {
				kind: ExprKind::U32TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_trunc_f64" => Expression {
				kind: ExprKind::I32TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u32_trunc_f64" => Expression {
				kind: ExprKind::U32TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_trunc_f32" => Expression {
				kind: ExprKind::I64TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u64_trunc_f32" => Expression {
				kind: ExprKind::U64TruncF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_trunc_f64" => Expression {
				kind: ExprKind::I64TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"u64_trunc_f64" => Expression {
				kind: ExprKind::U64TruncF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_promote_f32" => Expression {
				kind: ExprKind::F64PromoteF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_demote_f64" => Expression {
				kind: ExprKind::F32DemoteF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i32_reinterpret_f32" => Expression {
				kind: ExprKind::I32ReinterpretF32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f32_reinterpret_i32" => Expression {
				kind: ExprKind::F32ReinterpretI32 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"i64_reinterpret_f64" => Expression {
				kind: ExprKind::I64ReinterpretF64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"f64_reinterpret_i64" => Expression {
				kind: ExprKind::F64ReinterpretI64 {
					value: Box::new(self.lower_expression(
						func_ctx,
						&arguments[0],
						sink,
					)),
				},
				ty: self.lower_type_index(expr_ty),
			},
			"memory_fill" => {
				let memory = self.resolve_memory_id(type_args[0]);
				let dst = Box::new(self.lower_expression(
					func_ctx,
					&arguments[0],
					sink,
				));
				let val = Box::new(self.lower_expression(
					func_ctx,
					&arguments[1],
					sink,
				));
				let len = Box::new(self.lower_expression(
					func_ctx,
					&arguments[2],
					sink,
				));
				Expression {
					kind: ExprKind::MemoryFill {
						memory,
						dst,
						val,
						len,
					},
					ty: ValueType::Unit,
				}
			}
			"memory_copy" => {
				let src_memory = self.resolve_memory_id(type_args[1]);
				let dst_memory = self.resolve_memory_id(type_args[2]);
				let dst = Box::new(self.lower_expression(
					func_ctx,
					&arguments[0],
					sink,
				));
				let src = Box::new(self.lower_expression(
					func_ctx,
					&arguments[1],
					sink,
				));
				let len = Box::new(self.lower_expression(
					func_ctx,
					&arguments[2],
					sink,
				));
				Expression {
					kind: ExprKind::MemoryCopy {
						dst_memory,
						src_memory,
						dst,
						src,
						len,
					},
					ty: ValueType::Unit,
				}
			}
			name => unreachable!("cannot lower unknown intrinsic `{name}`"),
		}
	}
}
