//! Literals and compile-time values: escape/char-literal parsing, coercion of
//! untyped integer and float literals to a concrete type, `as` casts, and the
//! constant folding that `const` items, enum discriminants and array sizes are
//! resolved through.

use crate::diagnostics::DiagnosticCode;

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Evaluates the compile-time value of an already-built `Expression`, for the
	/// small subset of shapes that are actually constant. `Err(())` means "does not
	/// fold" — for the const-initializer/enum-variant callers, that doubles as "not a
	/// constant expression," since `build_expression` itself imposes no shape
	/// restriction. Recursive calls propagate `Err(())` via `?` without pushing a
	/// diagnostic; only the top-level call site reports one.
	///
	/// `Const`/`NamespaceAccess` references read the referenced constant's own
	/// already-cached `const_value` rather than re-walking its expression tree, so a
	/// chain of const-on-const arithmetic stays linear instead of blowing up.
	pub(super) fn eval_const_expr(
		&self,
		expr: &Expression,
	) -> Result<ConstValue, ()> {
		match &expr.kind {
			// `value` is a raw, non-negative literal magnitude (see
			// `ExprKind::Int`'s doc comment) — bit-reinterpret into the
			// unified `ConstValue::Int(i64)` representation, same
			// convention `IntegerRange` already uses (e.g. `u64::MAX as
			// i64 == -1`, correct for an already-`u64`-typed constant).
			ExprKind::Int { value } => Ok(ConstValue::Int(*value as i64)),
			ExprKind::Float { value } => Ok(ConstValue::Float(*value)),
			ExprKind::Bool { value } => Ok(ConstValue::Bool(*value)),
			ExprKind::Char { value } => Ok(ConstValue::Char(*value)),
			ExprKind::Unary { operator, operand } => {
				// A literal being negated directly (`-128`) must be
				// negated from its raw `u64` magnitude, not from the
				// bit-cast `i64` recursing through `eval_const_expr`
				// would otherwise produce for it — negating *that* value
				// would panic on `-9223372036854775808` (`i64::MIN`'s
				// magnitude bit-casts to `i64::MIN` itself, and only
				// `wrapping_neg` on the raw magnitude wraps that back to
				// the correct answer).
				if let ast::UnaryOp::InvertSign = operator.inner
					&& let ExprKind::Int { value } = operand.kind
				{
					return Ok(ConstValue::Int((value as i64).wrapping_neg()));
				}

				let value = self.eval_const_expr(operand)?;
				match (operator.inner, value) {
					(ast::UnaryOp::InvertSign, ConstValue::Float(value)) => {
						Ok(ConstValue::Float(-value))
					}
					(ast::UnaryOp::InvertSign, ConstValue::Int(value)) => {
						Ok(ConstValue::Int(value.wrapping_neg()))
					}
					(ast::UnaryOp::BitNot, ConstValue::Int(value)) => {
						Ok(ConstValue::Int(!value))
					}
					_ => Err(()),
				}
			}
			ExprKind::Binary {
				operator,
				left,
				right,
			} => {
				let left = self.eval_const_expr(left)?;
				let right = self.eval_const_expr(right)?;
				// Float operands are representation-agnostic the same way
				// int Add/Sub/Mul are: plain `f64` arithmetic already
				// follows IEEE-754 (division by zero yields ±∞/NaN rather
				// than panicking), so no divide-by-zero guard is needed
				// here the way the integer Div/Rem arms below need one.
				if let (ConstValue::Float(left), ConstValue::Float(right)) =
					(left, right)
				{
					return match operator.inner {
						BinaryOp::Add => Ok(ConstValue::Float(left + right)),
						BinaryOp::Sub => Ok(ConstValue::Float(left - right)),
						BinaryOp::Mul => Ok(ConstValue::Float(left * right)),
						BinaryOp::Div => Ok(ConstValue::Float(left / right)),
						BinaryOp::Rem => Ok(ConstValue::Float(left % right)),
						_ => Err(()),
					};
				}
				let ConstValue::Int(left) = left else {
					return Err(());
				};
				let ConstValue::Int(right) = right else {
					return Err(());
				};
				// `Add`/`Sub`/`Mul` are representation-agnostic in two's
				// complement — the wrapped bit pattern is identical
				// whether `left`/`right` are interpreted as signed or
				// unsigned, so folding them via plain `i64` wrapping ops
				// is correct regardless of `expr.ty`'s real signedness.
				// `Div`/`Rem` are not: dividing the same bit pattern as
				// signed vs. unsigned gives different answers whenever a
				// `u64` constant's magnitude exceeds `i64::MAX` (e.g.
				// `u64::MAX / 2`, which as signed `i64` is `-1 / 2 == 0`,
				// but is `9223372036854775807` as unsigned) — those two
				// need to consult `expr.ty` and pick the matching
				// operation.
				let unsigned = expr.ty == TypeIndex::U8
					|| expr.ty == TypeIndex::U16
					|| expr.ty == TypeIndex::U32
					|| expr.ty == TypeIndex::U64;
				match operator.inner {
					BinaryOp::Add => {
						Ok(ConstValue::Int(left.wrapping_add(right)))
					}
					BinaryOp::Sub => {
						Ok(ConstValue::Int(left.wrapping_sub(right)))
					}
					BinaryOp::Mul => {
						Ok(ConstValue::Int(left.wrapping_mul(right)))
					}
					BinaryOp::Div if unsigned => {
						if right == 0 {
							Err(())
						} else {
							Ok(ConstValue::Int(
								((left as u64).wrapping_div(right as u64))
									as i64,
							))
						}
					}
					BinaryOp::Div => {
						if right == 0 {
							Err(())
						} else {
							Ok(ConstValue::Int(left.wrapping_div(right)))
						}
					}
					BinaryOp::Rem if unsigned => {
						if right == 0 {
							Err(())
						} else {
							Ok(ConstValue::Int(
								((left as u64).wrapping_rem(right as u64))
									as i64,
							))
						}
					}
					BinaryOp::Rem => {
						if right == 0 {
							Err(())
						} else {
							Ok(ConstValue::Int(left.wrapping_rem(right)))
						}
					}
					BinaryOp::BitAnd => Ok(ConstValue::Int(left & right)),
					BinaryOp::BitOr => Ok(ConstValue::Int(left | right)),
					BinaryOp::BitXor => Ok(ConstValue::Int(left ^ right)),
					// Masking (rather than a plain `<<`/`>>`) keeps an
					// out-of-range shift amount (e.g. a typo'd `1 << 99`)
					// from panicking the compiler itself — it folds to
					// *some* wrapped value, which the caller's own
					// range/repr check then rejects like any other
					// out-of-range constant.
					BinaryOp::LeftShift => {
						Ok(ConstValue::Int(left.wrapping_shl(right as u32)))
					}
					// Right shift mirrors the same signed/arithmetic vs.
					// unsigned/logical split codegen uses for the runtime
					// `ShrS`/`ShrU` instructions (`opt/builder.rs`): `unsigned`
					// picks a logical shift on the bit pattern, otherwise an
					// arithmetic (sign-extending) shift on the `i64` value —
					// correct here because that value is already the sign-
					// extended bit-reinterpretation `ExprKind::Int`/`Unary`
					// produced for it.
					BinaryOp::RightShift if unsigned => Ok(ConstValue::Int(
						(left as u64).wrapping_shr(right as u32) as i64,
					)),
					BinaryOp::RightShift => {
						Ok(ConstValue::Int(left.wrapping_shr(right as u32)))
					}
					_ => Err(()),
				}
			}
			ExprKind::Const { id } => {
				let const_index = self.items.expect_const_index(*id);
				self.items.constants[usize::from(const_index)]
					.const_value
					.ok_or(())
			}
			ExprKind::NamespaceAccess { member, .. } => {
				self.eval_const_expr(member)
			}
			_ => Err(()),
		}
	}

	/// Builds a constant-context expression (enum variant value, const initializer)
	/// via the general expression builder, using a throwaway single-scope
	/// `BodyContext` (mirrors the `Global` initializer path). `scope: None` since
	/// const expressions can never be generic and have no `Self`. Coerces untyped
	/// int/float literals to `ty` and reports a type mismatch if the result doesn't
	/// match — same idiom `Global` initializers already use. Does *not* check
	/// constant-ness; callers that need that call `eval_const_expr` on the result.
	pub(super) fn build_const_context_expression(
		&mut self,
		resolve_context: ResolveContext,
		expr: &ast::Spanned<ast::Expression>,
		ty: TypeIndex,
	) -> Result<Expression, ()> {
		let root_scope = BlockScope {
			parent: None,
			label: None,
			kind: BlockKind::Block,
			span: expr.span,
			locals: Vec::new(),
			inferred_type: TypeIndex::INFER,
			expected_type: ty,
		};
		let mut func_ctx = ExprContext {
			stack: StackFrame {
				scopes: vec![root_scope],
				labels: Vec::new(),
			},
			scope_index: ScopeIndex::new(0),
			lookup: HashMap::new(),
			resolve_context,
			scope: None,
			// `const`/enum-discriminant values never reach MIR — only the
			// literal `const_value` `eval_const_expr` computes survives,
			// inlined at every reference site — so operator dispatch is
			// never worth attempting here; see `EvalMode`'s doc comment.
			mode: EvalMode::Comptime,
		};
		let mut value_expr = self.build_expression(
			&mut func_ctx,
			AccessContext {
				expected_type: ty,
				access_kind: AccessKind::Read,
			},
			expr,
		)?;

		if value_expr.ty.is_comptime_number() && ty != TypeIndex::INFER {
			_ = self.coerce_untyped_expr(&mut func_ctx, &mut value_expr, ty);
		}

		if value_expr.ty.is_comptime_number() {
			self.diagnostics.push(report_type_annotation_required(
				SourceSpan::new(resolve_context.file_id, expr.span),
			));
			return Err(());
		}
		if ty != TypeIndex::ERROR && !self.coercible_to(value_expr.ty, ty) {
			self.diagnostics.push(report_type_mistmatch(
				self.formatter(resolve_context.namespace),
				TypeMistmatchDiagnostic {
					expected_type: ty,
					actual_type: value_expr.ty,
					span: SourceSpan::new(resolve_context.file_id, expr.span),
				},
			));
			return Err(());
		}
		Ok(value_expr)
	}

	pub(super) fn build_cast_expression(
		&mut self,
		ctx: &mut ExprContext,
		access_ctx: AccessContext,
		value: &Spanned<ast::Expression>,
		cast_type: &Spanned<ast::TypeExpression>,
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let cast_type =
			self.resolve_type(ctx.resolve_context, ctx.scope, cast_type);
		if cast_type == TypeIndex::ERROR {
			return self.build_expression(ctx, access_ctx, value);
		}
		let cast_type = if cast_type == TypeIndex::INFER {
			let expected = access_ctx.expected_type;
			if expected == TypeIndex::INFER {
				self.diagnostics.push(report_type_annotation_required(
					SourceSpan::new(ctx.resolve_context.file_id, expr_span),
				));
				return self.build_expression(ctx, access_ctx, value);
			}
			expected
		} else {
			cast_type
		};
		let mut value = self.build_expression(
			ctx,
			AccessContext {
				expected_type: cast_type,
				access_kind: access_ctx.access_kind,
			},
			value,
		)?;
		if value.ty.is_comptime_number() {
			self.coerce_untyped_expr(ctx, &mut value, cast_type)?;
		} else if self.are_scalar_compatible(value.ty, cast_type) {
			// TODO: add checks for unsafe/lossy casts like i32 to u8, or u32 to char
			value.ty = cast_type;
		} else {
			self.diagnostics.push(report_invalid_cast(
				self.formatter(ctx.resolve_context.namespace),
				value.ty,
				cast_type,
				SourceSpan::new(ctx.resolve_context.file_id, expr_span),
			));
		}

		Ok(value)
	}

	fn are_scalar_compatible(&self, a: TypeIndex, b: TypeIndex) -> bool {
		if a == b {
			return true;
		}
		match (self.types.resolve(a), self.types.resolve(b)) {
			// KNOWN GAP: casts only check `memory` equality, not ownership —
			// `&T as *T` currently passes, silently defeating "a `&T` is
			// always read-only". Fixing this properly needs a real rework of
			// `as`-cast checking (and probably lands alongside whatever
			// borrow-checker-alternative wx eventually gets), so it's left
			// as-is for now rather than patched in isolation here.
			(
				Type::Pointer { memory: a_mem, .. },
				Type::Pointer { memory: b_mem, .. },
			) => a_mem == b_mem,
			(
				Type::Array { memory: a_mem, .. },
				Type::Array { memory: b_mem, .. },
			) => a_mem == b_mem,
			(
				Type::Slice { memory: a_mem, .. },
				Type::Slice { memory: b_mem, .. },
			) => a_mem == b_mem,
			// Allow M::Size ↔ M::*T (both directions): same memory base, assoc type is "Size"
			(
				Type::AssocTypeProjection {
					base: a_base,
					assoc_name,
					..
				},
				Type::Pointer { memory: b_mem, .. },
			) => {
				a_base == b_mem
					&& self.interner.resolve(*assoc_name) == Some("Size")
			}
			(
				Type::Pointer { memory: a_mem, .. },
				Type::AssocTypeProjection {
					base: b_base,
					assoc_name,
					..
				},
			) => {
				a_mem == b_base
					&& self.interner.resolve(*assoc_name) == Some("Size")
			}
			_ => matches!(
				(self.type_scalar(a), self.type_scalar(b)),
				(Some(x), Some(y)) if x == y
			),
		}
	}

	fn type_scalar(&self, ty: TypeIndex) -> Option<WasmScalar> {
		match self.types.resolve(ty) {
			Type::Bool
			| Type::U8
			| Type::I8
			| Type::U16
			| Type::I16
			| Type::I32
			| Type::U32
			| Type::Char
			| Type::Function { .. } => Some(WasmScalar::I32),
			Type::Enum { enum_index } => {
				let repr_type =
					self.items.enums[usize::from(*enum_index)].repr_type;
				self.type_scalar(repr_type)
			}
			Type::U64 | Type::I64 => Some(WasmScalar::I64),
			Type::F32 => Some(WasmScalar::F32),
			Type::F64 => Some(WasmScalar::F64),
			Type::Pointer { memory, .. } => match self.types.resolve(*memory) {
				Type::Memory { size, .. } => self.type_scalar(*size),
				_ => None,
			},
			Type::Tuple { .. }
			| Type::Array { .. }
			| Type::AssociatedType { .. }
			| Type::AssocTypeProjection { .. }
			| Type::FunctionItem { .. }
			| Type::Struct { .. }
			| Type::Slice { .. }
			| Type::Namespace { .. }
			| Type::Memory { .. }
			| Type::TypeParam { .. }
			| Type::Error
			| Type::Infer
			| Type::Never
			| Type::Unit
			| Type::Integer
			| Type::Float => None,
		}
	}

	pub(super) fn coerce_untyped_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &mut Expression,
		target_type: TypeIndex,
	) -> Result<(), ()> {
		// if target_type == TypeIndex::INFER {
		//     self.diagnostics
		//         .push(report_type_annotation_required(SourceSpan::new(
		//             file_id, expr.span,
		//         )));
		//     return Err(());
		// }
		match expr.kind {
			ExprKind::Int { .. } => self.coerce_untyped_int_expr(
				ctx.resolve_context,
				expr,
				target_type,
			),
			ExprKind::Float { .. } => self.coerce_untyped_float_expr(
				ctx.resolve_context,
				expr,
				target_type,
			),
			ExprKind::Unary { .. } => {
				self.coerce_untyped_unary_expr(ctx, expr, target_type)
			}
			ExprKind::Binary { .. } => {
				self.coerce_untyped_binary_expression(ctx, expr, target_type)
			}
			ExprKind::Block {
				scope_index,
				result: Some(ref mut result),
				..
			} => {
				self.coerce_untyped_expr(ctx, result, target_type)?;
				expr.ty = target_type;
				ctx.stack.scopes[usize::from(scope_index)].inferred_type =
					target_type;
				Ok(())
			}
			// Any other expression kind that ends up here already had an error
			// reported; propagate failure without emitting a second diagnostic.
			_ => Err(()),
		}
	}

	fn coerce_untyped_int_expr(
		&mut self,
		resolve_context: ResolveContext,
		expr: &mut Expression,
		target_idx: TypeIndex,
	) -> Result<(), ()> {
		let file_id = resolve_context.file_id;
		let value = match expr.kind {
			ExprKind::Int { value } => value,
			_ => unreachable!(),
		};
		let formatter = self.formatter(resolve_context.namespace);

		// `value` is always the raw, non-negative magnitude as written (see
		// `ExprKind::Int`'s doc comment) — negation is a separate `Unary`
		// node handled by `coerce_untyped_unary_expr`, never reaching here.
		// So every primitive-integer target below only ever needs an
		// upper-bound check against its own `MAX` (as `u64`); a lower bound
		// can never fire and isn't checked.
		let primitive_int_max: Option<u64> = match target_idx {
			TypeIndex::I32 => Some(i32::MAX as u64),
			TypeIndex::I64 => Some(i64::MAX as u64),
			TypeIndex::U32 => Some(u32::MAX as u64),
			TypeIndex::U64 => Some(u64::MAX),
			TypeIndex::U8 => Some(u8::MAX as u64),
			TypeIndex::I8 => Some(i8::MAX as u64),
			TypeIndex::U16 => Some(u16::MAX as u64),
			TypeIndex::I16 => Some(i16::MAX as u64),
			TypeIndex::CHAR => Some(u32::MAX as u64),
			_ => None,
		};
		if let Some(max) = primitive_int_max {
			if value > max {
				self.diagnostics.push(report_integer_literal_out_of_range(
					formatter,
					IntegerLiteralOutOfRangeDiagnostic {
						ty: target_idx,
						value: value as i64,
						span: SourceSpan::new(file_id, expr.span),
					},
				));
			}
			expr.ty = target_idx;
			Ok(())
		} else if target_idx == TypeIndex::F32 || target_idx == TypeIndex::F64 {
			self.diagnostics.push(report_integer_literal_for_float_type(
				SourceSpan::new(file_id, expr.span),
			));
			Err(())
		} else if matches!(self.types.resolve(target_idx), Type::Pointer { .. })
		{
			match self.type_scalar(target_idx) {
				Some(WasmScalar::I32) => {
					if value > u32::MAX as u64 {
						self.diagnostics.push(
							report_integer_literal_out_of_range(
								formatter,
								IntegerLiteralOutOfRangeDiagnostic {
									ty: TypeIndex::U32,
									value: value as i64,
									span: SourceSpan::new(file_id, expr.span),
								},
							),
						);
					}
				}
				// `value` is a `u64`, so it can never exceed `u64::MAX` —
				// nothing to check.
				Some(WasmScalar::I64) => {}
				_ => {
					// Generic pointer (TypeParam memory) — validate against the
					// `#[tag = "pointer_size"]` typeset (`PointerSize` in std.wx).
					if let Some(ts) = self
						.interner
						.get("pointer_size")
						.and_then(|key| self.items.tagged_items.get(&key))
						.and_then(|tagged_id| {
							self.items.typeset_index(*tagged_id)
						})
						.map(|idx| &self.items.typesets[usize::from(idx)])
					{
						if !ts.intersection_range.contains(value as i64) {
							let ts_name = self
								.interner
								.resolve(ts.name.inner)
								.unwrap_or("PointerSize")
								.to_string();
							self.diagnostics.push(
								report_integer_literal_out_of_typeset_range(
									value as i64,
									&ts_name,
									&ts.intersection_range,
									SourceSpan::new(file_id, expr.span),
								),
							);
							return Err(());
						}
					}
				}
			}
			expr.ty = target_idx;
			Ok(())
		} else if let Some(typeset_index) = self
			.items
			.abstract_type_bounds(&self.types, target_idx)
			.and_then(|bounds| bounds.typeset)
			.map(|typeset_bound| typeset_bound.typeset_index)
		{
			let ts = &self.items.typesets[usize::from(typeset_index)];
			let range = &ts.intersection_range;
			let ts_name =
				self.interner.resolve(ts.name.inner).unwrap().to_string();
			if !range.contains(value as i64) {
				self.diagnostics.push(
					report_integer_literal_out_of_typeset_range(
						value as i64,
						&ts_name,
						range,
						SourceSpan::new(file_id, expr.span),
					),
				);
				return Err(());
			}
			expr.ty = target_idx;
			Ok(())
		} else {
			self.diagnostics.push(report_unable_to_coerce(
				formatter,
				target_idx,
				SourceSpan::new(file_id, expr.span),
			));
			Err(())
		}
	}

	fn coerce_untyped_float_expr(
		&mut self,
		resolve_context: ResolveContext,
		expr: &mut Expression,
		target_idx: TypeIndex,
	) -> Result<(), ()> {
		let file_id = resolve_context.file_id;
		if target_idx == TypeIndex::F32 {
			// TODO: add a diagnostic if the literal is out of range
			expr.ty = TypeIndex::F32;
			Ok(())
		} else if target_idx == TypeIndex::F64 {
			// TODO: add a diagnostic if the literal is out of range
			expr.ty = TypeIndex::F64;
			Ok(())
		} else {
			self.diagnostics.push(report_unable_to_coerce(
				self.formatter(resolve_context.namespace),
				target_idx,
				SourceSpan::new(file_id, expr.span),
			));
			Err(())
		}
	}

	fn coerce_untyped_unary_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &mut Expression,
		target_idx: TypeIndex,
	) -> Result<(), ()> {
		let file_id = ctx.resolve_context.file_id;
		let (operand, operator) = match &mut expr.kind {
			ExprKind::Unary { operand, operator } => (operand, *operator),
			_ => unreachable!(),
		};

		match operator.inner {
			// `-x`: valid for any signed numeric target — all four signed
			// integer widths plus both floats. Unsigned targets are
			// deliberately excluded (`local x: u32 = -1;` must fail to
			// coerce, same as negating an already-typed `u32` operand does
			// elsewhere).
			ast::UnaryOp::InvertSign => {
				let is_valid = target_idx == TypeIndex::I8
					|| target_idx == TypeIndex::I16
					|| target_idx == TypeIndex::I32
					|| target_idx == TypeIndex::I64
					|| target_idx == TypeIndex::F32
					|| target_idx == TypeIndex::F64;
				if !is_valid {
					self.diagnostics.push(report_unable_to_coerce(
						self.formatter(ctx.resolve_context.namespace),
						target_idx,
						SourceSpan::new(file_id, expr.span),
					));
					return Err(());
				}

				// Two's-complement's negative range holds one more
				// magnitude than its positive range (e.g. `i8::MIN` is
				// `-128` but `i8::MAX` is only `127`). `operand` here is
				// always the un-negated positive literal, so delegating
				// straight to `coerce_untyped_expr` would range-check
				// that magnitude against the ordinary (narrower)
				// positive-max bound and wrongly reject exactly the
				// most-negative value of each width (`-128i8`,
				// `-32768i16`, `-2147483648i32`,
				// `-9223372036854775808i64`) — check the true
				// negation-aware bound here instead, and skip the
				// generic recursive coercion for this shape entirely.
				if let ExprKind::Int { value } = operand.kind {
					let max_magnitude: u64 = match target_idx {
						TypeIndex::I8 => i8::MIN.unsigned_abs() as u64,
						TypeIndex::I16 => i16::MIN.unsigned_abs() as u64,
						TypeIndex::I32 => i32::MIN.unsigned_abs() as u64,
						TypeIndex::I64 => i64::MIN.unsigned_abs(),
						// F32/F64: no integer range to check.
						_ => u64::MAX,
					};
					if value > max_magnitude {
						self.diagnostics.push(
							report_integer_literal_out_of_range(
								self.formatter(ctx.resolve_context.namespace),
								IntegerLiteralOutOfRangeDiagnostic {
									ty: target_idx,
									value: (value as i64).wrapping_neg(),
									span: SourceSpan::new(file_id, expr.span),
								},
							),
						);
					}
					operand.ty = target_idx;
				} else {
					self.coerce_untyped_expr(ctx, operand, target_idx)?;
				}
			}
			// `^x`: valid for any integer width, signed or unsigned — sign
			// doesn't matter for bitwise complement.
			ast::UnaryOp::BitNot => {
				if !target_idx.is_integer() {
					self.diagnostics.push(report_unable_to_coerce(
						self.formatter(ctx.resolve_context.namespace),
						target_idx,
						SourceSpan::new(file_id, expr.span),
					));
					return Err(());
				}
				self.coerce_untyped_expr(ctx, operand, target_idx)?;
			}
			_ => unreachable!(),
		}

		// Same reasoning as `coerce_untyped_binary_expression`'s equivalent
		// go-to-definition fix: the node stays `Unary` either way (`Neg`'s
		// impls all bottom out in the same intrinsic MIR's native `Neg`
		// lowering would use anyway), so this is solely to record the
		// operator's own span as an access, for `Runtime` mode only.
		if operator.inner == ast::UnaryOp::InvertSign
			&& let EvalMode::Runtime(traits) = &ctx.mode
			&& let Some((trait_index, method_symbol)) =
				traits.for_unary_op(operator.inner)
			&& let Some(func_idx) = self.resolve_trait_method(
				trait_index,
				method_symbol,
				target_idx,
			) {
			self.items.functions[usize::from(func_idx)]
				.accesses
				.push(SourceSpan::new(file_id, operator.span));
		}

		expr.ty = target_idx;
		Ok(())
	}

	fn coerce_untyped_binary_expression(
		&mut self,
		ctx: &mut ExprContext,
		expr: &mut Expression,
		target_idx: TypeIndex,
	) -> Result<(), ()> {
		let file_id = ctx.resolve_context.file_id;
		let (left, right, operator) = match &mut expr.kind {
			ExprKind::Binary {
				operator,
				left,
				right,
			} => (left, right, *operator),
			_ => unreachable!(),
		};

		// Arithmetic only: unlike `build_arithmetic_expr`, which leaves a
		// comptime-comptime `Binary` node's `ty` as the untyped pseudo-type
		// for coercion to be deferred to here, `build_bitwise_binary_expr`
		// always resolves its own type inline (against `access_ctx`'s
		// expected type, or by reporting "type annotation required" itself
		// when that's unknown) — so a bitwise `Binary` node is never left
		// untyped for this function to reach.
		debug_assert!(operator.inner.is_arithmetic());
		if !target_idx.is_primitive() {
			self.diagnostics.push(report_unable_to_coerce(
				self.formatter(ctx.resolve_context.namespace),
				target_idx,
				SourceSpan::new(file_id, expr.span),
			));
			return Err(());
		}

		let left_result = self.coerce_untyped_expr(ctx, left, target_idx);
		let right_result = self.coerce_untyped_expr(ctx, right, target_idx);
		match (left_result, right_result) {
			(Ok(_), Ok(_)) => {
				// Both operands were still untyped literals when this
				// `Binary` node was first built (`build_arithmetic_expr`
				// can't dispatch without a concrete type yet), so trait
				// dispatch — for `Runtime` mode only, matching every other
				// dispatch site — was deferred until now. The node stays a
				// `Binary` either way — MIR's native lowering for
				// Add/Sub/Mul/Div/Rem always bottoms out at the same
				// intrinsic the resolved trait method would call, so
				// there's no correctness reason to rebuild it as a
				// `MethodCall` — this is solely to record the operator's own
				// span as a go-to-definition access, same as
				// `build_operator_dispatch`'s success case.
				if operator.inner.is_arithmetic()
					&& let EvalMode::Runtime(traits) = &ctx.mode
					&& let Some((trait_index, method_symbol)) =
						traits.for_op(operator.inner)
					&& let Some(func_idx) = self.resolve_trait_method(
						trait_index,
						method_symbol,
						target_idx,
					) {
					self.items.functions[usize::from(func_idx)]
						.accesses
						.push(SourceSpan::new(file_id, operator.span));
				}
				expr.ty = target_idx;
				Ok(())
			}
			_ => Err(()),
		}
	}
}

pub fn unescape_string(s: &str) -> String {
	// Remove surrounding quotes
	let s = if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
		&s[1..s.len() - 1]
	} else {
		s
	};

	let mut result = String::with_capacity(s.len());
	let mut chars = s.chars();

	while let Some(ch) = chars.next() {
		if ch == '\\' {
			match chars.next() {
				Some('n') => result.push('\n'),
				Some('r') => result.push('\r'),
				Some('t') => result.push('\t'),
				Some('\\') => result.push('\\'),
				Some('"') => result.push('"'),
				Some('0') => result.push('\0'),
				// If we encounter an unknown escape, keep the backslash and the character
				Some(c) => {
					result.push('\\');
					result.push(c);
				}
				None => result.push('\\'),
			}
		} else {
			result.push(ch);
		}
	}

	result
}

#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum CharLiteralError {
	Empty,
	TooLong,
}

pub fn parse_char_literal(s: &str) -> Result<char, CharLiteralError> {
	let content = if s.starts_with('\'') && s.ends_with('\'') && s.len() >= 2 {
		&s[1..s.len() - 1]
	} else {
		s
	};

	let mut chars = content.chars();
	let value = match chars.next() {
		None => return Err(CharLiteralError::Empty),
		Some('\\') => match chars.next() {
			None => return Err(CharLiteralError::Empty),
			Some('n') => '\n',
			Some('r') => '\r',
			Some('t') => '\t',
			Some('\\') => '\\',
			Some('\'') => '\'',
			Some('0') => '\0',
			Some('x') => {
				let hi = chars.next().and_then(|c| c.to_digit(16));
				let lo = chars.next().and_then(|c| c.to_digit(16));
				match (hi, lo) {
					(Some(h), Some(l)) => {
						let codepoint = h * 16 + l;
						char::from_u32(codepoint).unwrap()
					}
					_ => return Err(CharLiteralError::TooLong),
				}
			}
			Some(c) => c,
		},
		Some(c) => c,
	};

	if chars.next().is_some() {
		return Err(CharLiteralError::TooLong);
	}

	Ok(value)
}
/// For const initializers and enum variant values (never `mut`-able) that build
/// successfully but don't fold — distinct from `report_non_constant_global_initializer`,
/// whose "add `mut`" suggestion only makes sense for globals.
pub(super) fn report_not_const_evaluatable(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::NotConstEvaluatable.code())
		.with_message(
			"expression cannot be evaluated as a compile-time constant",
		)
		.with_label(span.primary_label())
}
pub(super) fn report_empty_char_literal(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidCharacterLiteral.code())
		.with_message("empty character literal")
		.with_label(span.primary_label())
}

pub(super) fn report_char_literal_too_long(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidCharacterLiteral.code())
		.with_message("character literal may only contain one codepoint")
		.with_label(span.primary_label())
		.with_note(
			"if you meant to write a string literal, use double quotes: `\"`, `\"`",
		)
}
pub(super) struct IntegerLiteralOutOfRangeDiagnostic {
	pub(super) ty: TypeIndex,
	pub(super) value: i64,
	pub(super) span: SourceSpan,
}

pub(super) fn report_integer_literal_out_of_range(
	fmt: TypeFormatter,
	diagnostic: IntegerLiteralOutOfRangeDiagnostic,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::IntegerLiteralOutOfRange.code())
		.with_message(format!(
			"literal `{}` out of range for `{}`",
			diagnostic.value,
			fmt.display_type(diagnostic.ty).unwrap()
		))
		.with_label(diagnostic.span.primary_label())
}

fn report_unable_to_coerce(
	fmt: TypeFormatter,
	target_type: TypeIndex,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnableToCoerce.code())
		.with_message(format!(
			"unable to coerce to type `{}`",
			fmt.display_type(target_type).unwrap()
		))
		.with_label(span.primary_label())
}

fn report_integer_literal_out_of_typeset_range(
	value: i64,
	typeset_name: &str,
	range: &IntegerRange,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
        .with_code(DiagnosticCode::TypesetBoundViolation.code())
        .with_message(format!(
            "integer literal `{value}` is out of the safe range for typeset `{typeset_name}`"
        ))
        .with_label(span.primary_label().with_message(format!(
            "safe range for `{typeset_name}` is `{}..={}`",
            range.min_i64(),
            range.max_u64(),
        )))
}

fn report_integer_literal_for_float_type(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::LiteralTypeMismatch.code())
		.with_message("cannot use an integer literal for a float type")
		.with_label(span.primary_label())
		.with_note("consider adding a decimal point, e.g. `1.0` instead of `1`")
}
fn report_invalid_cast(
	fmt: TypeFormatter,
	from_type: TypeIndex,
	to_type: TypeIndex,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidCast.code())
		.with_message(format!(
			"cannot cast `{}` to `{}`",
			fmt.display_type(from_type).unwrap(),
			fmt.display_type(to_type).unwrap(),
		))
		.with_label(span.primary_label())
}
