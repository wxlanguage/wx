//! Control flow and pattern matching: `if`/`else`, `loop`, labelled blocks,
//! `break`/`continue`/`return`, and `match` together with the pattern
//! machinery (`local` destructuring included) and its exhaustiveness check.

use super::*;

impl<'ast> Builder<'ast, '_> {
	pub(super) fn build_label_expression(
		&mut self,
		ctx: &mut ExprContext,
		access_ctx: AccessContext,
		block: &Spanned<ast::Expression>,
		label: Spanned<SymbolU32>,
	) -> Result<Expression, ()> {
		let label_index = ctx.stack.push_label(label);
		match &block.inner {
			ast::Expression::Block { .. } => ctx.enter_block(
				BlockScope {
					label: Some(label_index),
					kind: BlockKind::Block,
					parent: Some(ctx.scope_index),
					span: block.span,
					locals: Vec::new(),
					inferred_type: TypeIndex::INFER,
					expected_type: access_ctx.expected_type,
				},
				|ctx| {
					self.build_block_expression(
						ctx,
						block.inner.as_block_statements(),
						block.span,
					)
				},
			),
			ast::Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => self.build_if_else_expression(
				ctx,
				AccessContext {
					expected_type: access_ctx.expected_type,
					access_kind: AccessKind::Read,
				},
				condition,
				then_block,
				else_block.as_deref(),
				block.span,
				Some(label_index),
			),
			ast::Expression::Loop { block: inner_block } => self
				.build_loop_expression(
					ctx,
					AccessContext {
						expected_type: access_ctx.expected_type,
						access_kind: AccessKind::Read,
					},
					inner_block,
					block.span,
					Some(label_index),
				),
			_ => unreachable!(),
		}
	}

	pub(super) fn build_loop_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		block: &Spanned<ast::Expression>,
		expr_span: TextSpan,
		label: Option<LabelIndex>,
	) -> Result<Expression, ()> {
		let file_id = func_ctx.resolve_context.file_id;
		func_ctx.enter_block(
			BlockScope {
				label,
				kind: BlockKind::Loop,
				parent: Some(func_ctx.scope_index),
				span: expr_span,
				locals: Vec::new(),
				inferred_type: TypeIndex::INFER,
				expected_type: access_ctx.expected_type,
			},
			|ctx| {
				let block = self.build_block_expression(
					ctx,
					block.inner.as_block_statements(),
					block.span,
				)?;

				let scope = &ctx.stack.scopes[ctx.scope_index as usize];
				let (expected_type, inferred_type) =
					(scope.expected_type, scope.inferred_type);
				if expected_type != TypeIndex::INFER
					&& inferred_type != TypeIndex::INFER
					&& !self.coercible_to(inferred_type, expected_type)
				{
					self.tir.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type,
							actual_type: inferred_type,
							span: SourceSpan::new(file_id, expr_span),
						},
					));
					return Err(());
				}

				// No `break` was encountered → loop is infinite → type is Never.
				let ty = inferred_type.infer_or(TypeIndex::NEVER);
				Ok(Expression {
					kind: ExprKind::Loop {
						scope_index: ctx.scope_index,
						block: Box::new(block),
					},
					ty,
					span: expr_span,
				})
			},
		)
	}

	pub(super) fn build_continue_expression(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let label = match &expr.inner {
			ast::Expression::Continue { label } => *label,
			_ => unreachable!(),
		};

		let scope_index = match label {
			Some(label) => match ctx.resolve_label(label.inner) {
				Some((scope_index, label_index)) => {
					ctx.stack.labels[label_index as usize]
						.accesses
						.push(label.span);
					scope_index
				}
				None => {
					self.tir.diagnostics.push(report_undeclared_label(
						self.interner.resolve(label.inner).unwrap(),
						SourceSpan::new(
							ctx.resolve_context.file_id,
							label.span,
						),
					));
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::NEVER,
						span: expr.span,
					});
				}
			},
			None => match ctx.get_closest_loop_block() {
				Some(scope_index) => scope_index,
				None => {
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::ContinueOutsideOfLoop.code(),
							)
							.with_message("`continue` outside of a loop")
							.with_label(
								SourceSpan::new(
									ctx.resolve_context.file_id,
									expr.span,
								)
								.primary_label()
								.with_message(
									"cannot `continue` outside of a loop",
								),
							),
					);
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::NEVER,
						span: expr.span,
					});
				}
			},
		};

		Ok(Expression {
			kind: ExprKind::Continue { scope_index },
			ty: TypeIndex::NEVER,
			span: expr.span,
		})
	}

	#[allow(clippy::too_many_arguments)]
	pub(super) fn build_if_else_expression(
		&mut self,
		ctx: &mut ExprContext,
		access_ctx: AccessContext,
		condition: &Spanned<ast::Expression>,
		then_block: &Spanned<ast::Expression>,
		else_block: Option<&Spanned<ast::Expression>>,
		expr_span: TextSpan,
		label: Option<LabelIndex>,
	) -> Result<Expression, ()> {
		let condition = match self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::BOOL,
				access_kind: AccessKind::Read,
			},
			condition,
		) {
			Ok(expr) => expr,
			Err(_) => Expression {
				kind: ExprKind::Error,
				ty: TypeIndex::ERROR,
				span: condition.span,
			},
		};

		let mut then_block = ctx.enter_block(
			BlockScope {
				label,
				kind: BlockKind::Block,
				parent: Some(ctx.scope_index),
				span: then_block.span,
				locals: Vec::new(),
				inferred_type: TypeIndex::INFER,
				expected_type: match else_block {
					Some(_) => access_ctx.expected_type,
					None => TypeIndex::INFER,
				},
			},
			|ctx| {
				self.build_block_expression(
					ctx,
					then_block.inner.as_block_statements(),
					then_block.span,
				)
			},
		)?;
		let (else_block, ty) = match else_block {
			Some(else_block) => {
				let mut else_block = ctx.enter_block(
					BlockScope {
						label,
						kind: BlockKind::Block,
						parent: Some(ctx.scope_index),
						span: else_block.span,
						locals: Vec::new(),
						inferred_type: TypeIndex::INFER,
						expected_type: access_ctx.expected_type,
					},
					|ctx| {
						self.build_block_expression(
							ctx,
							else_block.inner.as_block_statements(),
							else_block.span,
						)
					},
				)?;

				// Cross-branch comptime coercion: coerce the comptime branch to match the
				// concrete sibling. Break values inside a comptime branch still need a type
				// annotation — they're resolved at build time before we see the sibling type.
				if then_block.ty.is_comptime_number()
					&& !else_block.ty.is_comptime_number()
				{
					self.coerce_untyped_expr(
						ctx,
						&mut then_block,
						else_block.ty,
					)?;
				} else if else_block.ty.is_comptime_number()
					&& !then_block.ty.is_comptime_number()
				{
					self.coerce_untyped_expr(
						ctx,
						&mut else_block,
						then_block.ty,
					)?;
				}

				match self.unify(then_block.ty, else_block.ty) {
					Ok(ty) => (Some(else_block), ty),
					Err(_) => {
						self.tir.diagnostics.push(report_type_mistmatch(
							self.formatter(ctx.resolve_context.namespace),
							TypeMistmatchDiagnostic {
								expected_type: then_block.ty,
								actual_type: else_block.ty,
								span: SourceSpan::new(
									ctx.resolve_context.file_id,
									else_block.span,
								),
							},
						));
						return Err(());
					}
				}
			}
			None => {
				if then_block.ty == TypeIndex::UNIT
					|| then_block.ty == TypeIndex::NEVER
				{
					(None, TypeIndex::UNIT)
				} else {
					self.tir.diagnostics.push(report_missing_else_block(
						self.formatter(ctx.resolve_context.namespace),
						then_block.ty,
						SourceSpan::new(
							ctx.resolve_context.file_id,
							then_block.span,
						),
					));
					return Err(());
				}
			}
		};

		Ok(Expression {
			kind: ExprKind::IfElse {
				condition: Box::new(condition),
				then_block: Box::new(then_block),
				else_block: else_block.map(Box::new),
			},
			ty,
			span: expr_span,
		})
	}

	pub(super) fn build_match_expression(
		&mut self,
		ctx: &mut ExprContext,
		access_ctx: AccessContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (scrutinee_expr, arms) = match &expr.inner {
			ast::Expression::Match { scrutinee, arms } => (scrutinee, arms),
			_ => unreachable!(),
		};

		let scrutinee = self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			scrutinee_expr,
		)?;
		let scrutinee_ty = scrutinee.ty;

		let is_valid_scrutinee = matches!(
			self.tir.types[scrutinee_ty.as_usize()],
			Type::Enum { .. }
		) || scrutinee_ty == TypeIndex::BOOL
			|| scrutinee_ty == TypeIndex::CHAR
			|| scrutinee_ty.is_integer();
		if !is_valid_scrutinee {
			self.tir
				.diagnostics
				.push(report_invalid_match_scrutinee_type(
					self.formatter(ctx.resolve_context.namespace),
					scrutinee_ty,
					SourceSpan::new(
						ctx.resolve_context.file_id,
						scrutinee_expr.span,
					),
				));
			return Err(());
		}

		if arms.is_empty() {
			self.tir
				.diagnostics
				.push(report_non_exhaustive_match_no_wildcard(
					SourceSpan::new(ctx.resolve_context.file_id, expr.span),
				));
			return Err(());
		}

		let mut arm_data: Vec<(Pattern, TextSpan, Expression)> =
			Vec::with_capacity(arms.len());
		for arm in arms.iter().map(|arm| &arm.inner.inner) {
			let pattern =
				self.build_pattern(ctx, scrutinee_ty, &arm.pattern)?;
			let body = ctx.enter_block(
				BlockScope {
					label: None,
					kind: BlockKind::Block,
					parent: Some(ctx.scope_index),
					span: arm.body.span,
					locals: Vec::new(),
					inferred_type: TypeIndex::INFER,
					expected_type: access_ctx.expected_type,
				},
				|ctx| {
					self.build_block_expression(
						ctx,
						arm.body.inner.as_block_statements(),
						arm.body.span,
					)
				},
			)?;
			arm_data.push((pattern, arm.pattern.span, body));
		}

		// Exact-duplicate-pattern / dead-arm-after-wildcard detection — cheap
		// byproduct of walking the arm list once; a warning, not an error.
		{
			let mut seen_wildcard = false;
			let mut seen_ints: HashSet<i64> = HashSet::new();
			let mut seen_chars: HashSet<char> = HashSet::new();
			let mut seen_bools: HashSet<bool> = HashSet::new();
			let mut seen_variants: HashSet<EnumVariantIndex> = HashSet::new();
			for (pattern, pattern_span, _) in &arm_data {
				let unreachable = if seen_wildcard {
					true
				} else {
					match pattern {
						Pattern::Wildcard => false,
						Pattern::Int(v) => !seen_ints.insert(*v),
						Pattern::Char(v) => !seen_chars.insert(*v),
						Pattern::Bool(v) => !seen_bools.insert(*v),
						Pattern::EnumVariant { variant_index, .. } => {
							!seen_variants.insert(*variant_index)
						}
					}
				};
				if matches!(pattern, Pattern::Wildcard) {
					seen_wildcard = true;
				}
				if unreachable {
					self.tir.diagnostics.push(report_unreachable_match_arm(
						SourceSpan::new(
							ctx.resolve_context.file_id,
							*pattern_span,
						),
					));
				}
			}
		}

		// Cross-arm comptime coercion + unification, folded left-to-right —
		// same idiom `build_if_else_expression` uses pairwise for two branches.
		let target_ty = arm_data
			.iter()
			.map(|(_, _, body)| body.ty)
			.find(|ty| !ty.is_comptime_number())
			.unwrap_or(arm_data[0].2.ty);

		let mut result_ty = target_ty;
		for (_, _, body) in arm_data.iter_mut() {
			if body.ty.is_comptime_number() && !target_ty.is_comptime_number() {
				self.coerce_untyped_expr(ctx, body, target_ty)?;
			}
			match self.unify(result_ty, body.ty) {
				Ok(ty) => result_ty = ty,
				Err(_) => {
					self.tir.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type: result_ty,
							actual_type: body.ty,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								body.span,
							),
						},
					));
					return Err(());
				}
			}
		}

		let built_arms: Box<[MatchArm]> = arm_data
			.into_iter()
			.map(|(pattern, pattern_span, body)| MatchArm {
				pattern,
				pattern_span,
				body: Box::new(body),
			})
			.collect();

		self.check_match_exhaustiveness(
			ctx.resolve_context.file_id,
			scrutinee_ty,
			&built_arms,
			expr.span,
		)?;

		Ok(Expression {
			kind: ExprKind::Match {
				scrutinee: Box::new(scrutinee),
				arms: built_arms,
			},
			ty: result_ty,
			span: expr.span,
		})
	}

	/// Resolves a `match` arm's pattern by re-running the ordinary expression
	/// builder on its syntax and interpreting the result — reuses
	/// `build_path_expression`'s existing `Enum::Variant` resolution (and its
	/// "used" tracking) rather than a separate pattern-resolution path.
	fn build_pattern(
		&mut self,
		ctx: &mut ExprContext,
		scrutinee_ty: TypeIndex,
		pattern_expr: &Spanned<ast::Expression>,
	) -> Result<Pattern, ()> {
		if matches!(pattern_expr.inner, ast::Expression::Placeholder) {
			return Ok(Pattern::Wildcard);
		}

		let built = self.build_expression(
			ctx,
			AccessContext {
				expected_type: scrutinee_ty,
				access_kind: AccessKind::Read,
			},
			pattern_expr,
		)?;

		if matches!(self.tir.types[scrutinee_ty.as_usize()], Type::Enum { .. })
		{
			if let ExprKind::NamespaceAccess { member, .. } = &built.kind
				&& let ExprKind::EnumVariant {
					enum_index,
					variant_index,
				} = member.kind
				&& built.ty == scrutinee_ty
			{
				return Ok(Pattern::EnumVariant {
					enum_index,
					variant_index,
				});
			}
			self.tir
				.diagnostics
				.push(report_invalid_pattern(SourceSpan::new(
					ctx.resolve_context.file_id,
					pattern_expr.span,
				)));
			return Err(());
		}

		let mut built = built;
		if built.ty.is_comptime_number() {
			self.coerce_untyped_expr(ctx, &mut built, scrutinee_ty)?;
		}

		match self.eval_const_expr(&built) {
			Ok(ConstValue::Int(v)) if scrutinee_ty.is_integer() => {
				Ok(Pattern::Int(v))
			}
			Ok(ConstValue::Bool(v)) if scrutinee_ty == TypeIndex::BOOL => {
				Ok(Pattern::Bool(v))
			}
			Ok(ConstValue::Char(v)) if scrutinee_ty == TypeIndex::CHAR => {
				Ok(Pattern::Char(v))
			}
			_ => {
				self.tir.diagnostics.push(report_invalid_pattern(
					SourceSpan::new(
						ctx.resolve_context.file_id,
						pattern_expr.span,
					),
				));
				Err(())
			}
		}
	}

	/// Full exhaustiveness is required unless a wildcard arm is present: an
	/// enum scrutinee must cover every variant, and any other scrutinee type
	/// (whose domain isn't enumerable) always requires `_`.
	fn check_match_exhaustiveness(
		&mut self,
		file_id: FileId,
		scrutinee_ty: TypeIndex,
		arms: &[MatchArm],
		match_span: TextSpan,
	) -> Result<(), ()> {
		let has_wildcard = arms
			.iter()
			.any(|arm| matches!(arm.pattern, Pattern::Wildcard));
		if has_wildcard {
			return Ok(());
		}

		match &self.tir.types[scrutinee_ty.as_usize()] {
			Type::Enum { enum_index } => {
				let enum_index = *enum_index as usize;
				let variant_count = self.tir.enums[enum_index].variants.len();
				let mut covered = vec![false; variant_count];
				for arm in arms {
					if let Pattern::EnumVariant { variant_index, .. } =
						arm.pattern
					{
						covered[variant_index as usize] = true;
					}
				}
				let missing: Vec<Spanned<SymbolU32>> = covered
					.iter()
					.enumerate()
					.filter(|&(_, &covered)| !covered)
					.map(|(i, _)| self.tir.enums[enum_index].variants[i].name)
					.collect();
				if missing.is_empty() {
					Ok(())
				} else {
					self.tir.diagnostics.push(report_non_exhaustive_match(
						self.interner,
						SourceSpan::new(file_id, match_span),
						&missing,
					));
					Err(())
				}
			}
			_ => {
				self.tir.diagnostics.push(
					report_non_exhaustive_match_no_wildcard(SourceSpan::new(
						file_id, match_span,
					)),
				);
				Err(())
			}
		}
	}

	pub(super) fn build_break_expression(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (label, value) = match &expr.inner {
			ast::Expression::Break { label, value } => (*label, value),
			_ => unreachable!(),
		};

		let scope_index = match label {
			Some(label) => match ctx.resolve_label(label.inner) {
				Some((scope_index, label_index)) => {
					ctx.stack.labels[label_index as usize]
						.accesses
						.push(label.span);
					scope_index
				}
				None => {
					self.tir.diagnostics.push(report_undeclared_label(
						self.interner.resolve(label.inner).unwrap(),
						SourceSpan::new(
							ctx.resolve_context.file_id,
							label.span,
						),
					));

					// TODO: how to handle this better? we don't parse the value if the label is
					// undeclared
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::NEVER,
						span: expr.span,
					});
				}
			},
			None => match ctx.get_closest_loop_block() {
				Some(scope_index) => scope_index,
				None => {
					self.tir.diagnostics.push(report_break_outside_of_loop(
						SourceSpan::new(ctx.resolve_context.file_id, expr.span),
					));

					// TODO: same as above, we don't parse the value if the break is outside of a
					// loop
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::NEVER,
						span: expr.span,
					});
				}
			},
		};

		match value {
			Some(value) => {
				let expected_type = ctx
					.stack
					.scopes
					.get(scope_index as usize)
					.unwrap()
					.expected_type;
				let mut built = match self.build_expression(
					ctx,
					AccessContext {
						expected_type,
						access_kind: AccessKind::Read,
					},
					value,
				) {
					Ok(v) => v,
					Err(()) => {
						return Ok(Expression {
							kind: ExprKind::Error,
							ty: TypeIndex::NEVER,
							span: expr.span,
						});
					}
				};

				let inferred_type = {
					let scope =
						ctx.stack.scopes.get_mut(scope_index as usize).unwrap();
					let inferred_type = self.infer_block_type(
						ctx.resolve_context,
						scope,
						&built,
					)?;
					scope.inferred_type = inferred_type;
					inferred_type
				};

				if built.ty.is_comptime_number() {
					if inferred_type.is_comptime_number() {
						self.tir.diagnostics.push(
							report_type_annotation_required(SourceSpan::new(
								ctx.resolve_context.file_id,
								built.span,
							)),
						);
						return Err(());
					}
					self.coerce_untyped_expr(ctx, &mut built, inferred_type)?;
				}

				Ok(Expression {
					kind: ExprKind::Break {
						scope_index,
						value: Some(Box::new(built)),
					},
					ty: TypeIndex::NEVER,
					span: expr.span,
				})
			}
			None => {
				let scope =
					ctx.stack.scopes.get_mut(scope_index as usize).unwrap();
				if scope.inferred_type != TypeIndex::INFER {
					let inferred = scope.inferred_type;
					if !self.coercible_to(TypeIndex::UNIT, inferred) {
						let formatter =
							self.formatter(ctx.resolve_context.namespace);
						self.tir.diagnostics.push(report_type_mistmatch(
							formatter,
							TypeMistmatchDiagnostic {
								expected_type: inferred,
								actual_type: TypeIndex::UNIT,
								span: SourceSpan::new(
									ctx.resolve_context.file_id,
									expr.span,
								),
							},
						));
					}
				} else {
					scope.inferred_type = TypeIndex::UNIT;
				}

				Ok(Expression {
					kind: ExprKind::Break {
						scope_index,
						value: None,
					},
					ty: TypeIndex::NEVER,
					span: expr.span,
				})
			}
		}
	}

	pub(super) fn build_return_expression(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let value = match &expr.inner {
			ast::Expression::Return { value } => value,
			_ => unreachable!(),
		};

		match value {
			Some(value) => {
				let expected_type =
					ctx.stack.scopes.first().unwrap().expected_type;
				let mut built = match self.build_expression(
					ctx,
					AccessContext {
						expected_type,
						access_kind: AccessKind::Read,
					},
					value,
				) {
					Ok(v) => v,
					Err(()) => {
						return Ok(Expression {
							kind: ExprKind::Unreachable,
							ty: TypeIndex::NEVER,
							span: expr.span,
						});
					}
				};

				let inferred_type = {
					let scope = ctx.stack.scopes.get_mut(0).unwrap();
					let inferred_type = self.infer_block_type(
						ctx.resolve_context,
						scope,
						&built,
					)?;
					scope.inferred_type = inferred_type;
					inferred_type
				};

				if built.ty.is_comptime_number() {
					if inferred_type.is_comptime_number() {
						self.tir.diagnostics.push(
							report_type_annotation_required(SourceSpan::new(
								ctx.resolve_context.file_id,
								built.span,
							)),
						);
						return Err(());
					}
					self.coerce_untyped_expr(ctx, &mut built, inferred_type)?;
				}

				let expected_type =
					ctx.stack.scopes.first().unwrap().expected_type;
				if expected_type != TypeIndex::INFER
					&& !self.coercible_to(inferred_type, expected_type)
				{
					self.tir.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type,
							actual_type: inferred_type,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								built.span,
							),
						},
					));
					return Err(());
				}

				Ok(Expression {
					kind: ExprKind::Return {
						value: Some(Box::new(built)),
					},
					ty: TypeIndex::NEVER,
					span: expr.span,
				})
			}
			None => {
				let scope =
					ctx.stack.scopes.get_mut(ctx.scope_index as usize).unwrap();

				let inferred_type =
					scope.inferred_type.infer_or(TypeIndex::UNIT);
				scope.inferred_type = inferred_type;

				let expected_type = scope.expected_type;
				if expected_type != TypeIndex::INFER
					&& self.coercible_to(inferred_type, expected_type)
				{
					self.tir.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type,
							actual_type: inferred_type,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								expr.span,
							),
						},
					));
					return Err(());
				}

				Ok(Expression {
					kind: ExprKind::Return { value: None },
					ty: TypeIndex::NEVER,
					span: expr.span,
				})
			}
		}
	}

	/// Walks `pattern` against the scrutinee type `ty`, registering one local
	/// per bound name and recording the projection that reaches its value.
	///
	/// `path` is the projection accumulated so far, pushed to on the way down
	/// and popped on the way back up, so each binding captures the full route
	/// from the scrutinee to itself. Nested patterns are flattened this way
	/// rather than kept nested.
	///
	/// A `ty` of `ERROR` means the initializer already failed. The walk still
	/// happens — every name in the pattern is bound, as `ERROR` — so later
	/// references resolve instead of piling on cascading errors, and no
	/// shape diagnostics are reported against a type that was never real.
	pub(super) fn collect_pattern_bindings(
		&mut self,
		ctx: &mut ExprContext,
		pattern: &Spanned<ast::Pattern>,
		ty: TypeIndex,
		path: &mut Vec<PathStep>,
		out: &mut Vec<PatternBinding>,
	) {
		let file_id = ctx.resolve_context.file_id;
		match &pattern.inner {
			// Binds nothing: the value it would name is simply never read.
			// Projections are pure reads of the scrutinee, so unlike the
			// top-level `_` there is nothing to evaluate for effect either.
			ast::Pattern::Wildcard => {}
			ast::Pattern::Binding { mut_span, name } => {
				let local_index = ctx.push_local(Local {
					name: *name,
					ty,
					mut_span: *mut_span,
					accesses: Vec::new(),
				});
				out.push(PatternBinding {
					scope_index: ctx.scope_index,
					local_index,
					path: path.as_slice().into(),
				});
			}
			ast::Pattern::Tuple { elements } => {
				// `()` is `UNIT`, not a zero-element `Type::Tuple`, so an
				// empty tuple pattern has nothing to check or bind.
				if ty == TypeIndex::UNIT && elements.is_empty() {
					return;
				}

				let element_types = match &self.tir.types[ty.as_usize()] {
					Type::Tuple { elements } => Some(elements.clone()),
					_ => None,
				};

				let element_types = match element_types {
					Some(types) if types.len() == elements.len() => types,
					other => {
						if ty != TypeIndex::ERROR {
							let found = self
								.formatter(ctx.resolve_context.namespace)
								.display_type(ty)
								.unwrap();
							let message = match &other {
								Some(types) => format!(
									"expected a {}-element tuple, found `{}` with {} elements",
									elements.len(),
									found,
									types.len()
								),
								None => format!(
									"expected a tuple, found `{}`",
									found
								),
							};
							self.tir.diagnostics.push(
								Diagnostic::error()
									.with_code(
										DiagnosticCode::TypeMistmatch.code(),
									)
									.with_message(
										"tuple pattern does not match the value",
									)
									.with_label(
										Label::primary(file_id, pattern.span)
											.with_message(message),
									),
							);
						}
						// Bind every name anyway, so nothing cascades.
						for element in elements.iter() {
							self.collect_pattern_bindings(
								ctx,
								&element.inner,
								TypeIndex::ERROR,
								path,
								out,
							);
						}
						return;
					}
				};

				for (index, element) in elements.iter().enumerate() {
					path.push(PathStep {
						aggregate_ty: ty,
						index: index as u32,
					});
					self.collect_pattern_bindings(
						ctx,
						&element.inner,
						element_types[index],
						path,
						out,
					);
					path.pop();
				}
			}
			ast::Pattern::Struct { .. } => self
				.collect_struct_pattern_bindings(ctx, pattern, ty, path, out),
		}
	}

	/// The `Path::{ ... }` arm of `collect_pattern_bindings`, split out only
	/// because resolving the path, matching it against the scrutinee, and
	/// checking the field list is a lot to nest inside one match arm.
	fn collect_struct_pattern_bindings(
		&mut self,
		ctx: &mut ExprContext,
		pattern: &Spanned<ast::Pattern>,
		ty: TypeIndex,
		path: &mut Vec<PathStep>,
		out: &mut Vec<PatternBinding>,
	) {
		let ast::Pattern::Struct {
			path: struct_path,
			fields,
			rest,
		} = &pattern.inner
		else {
			unreachable!()
		};
		let file_id = ctx.resolve_context.file_id;

		// The scrutinee decides which struct this is and how it is
		// instantiated; the written path only has to agree with it.
		let scrutinee = match &self.tir.types[ty.as_usize()] {
			Type::Struct { struct_index, args } => {
				Some((*struct_index, args.clone()))
			}
			_ => None,
		};

		// Resolve the written path regardless, so a bad name is reported even
		// when the scrutinee is already broken.
		let named_ty = self.resolve_path_type(
			ctx.resolve_context,
			ctx.scope,
			struct_path,
			pattern.span,
			TypeArgArity::AllowInfer,
		);
		let named_index = match &self.tir.types[named_ty.as_usize()] {
			Type::Struct { struct_index, .. } => Some(*struct_index),
			_ => None,
		};
		if named_index.is_none() && named_ty != TypeIndex::ERROR {
			let last = struct_path.last().expect("path is non-empty");
			let name =
				self.interner.resolve(last.ident.inner).unwrap().to_string();
			self.tir.diagnostics.push(report_not_a_struct_type(
				file_id,
				name,
				last.ident.span,
			));
		}

		let (struct_index, args) = match scrutinee {
			Some((struct_index, args))
				if named_index.is_none_or(|named| named == struct_index) =>
			{
				(struct_index, args)
			}
			other => {
				if ty != TypeIndex::ERROR {
					let fmt = self.formatter(ctx.resolve_context.namespace);
					let message = match other {
						Some(_) => format!(
							"value is `{}`",
							fmt.display_type(ty).unwrap()
						),
						None => format!(
							"expected a struct, found `{}`",
							fmt.display_type(ty).unwrap()
						),
					};
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_code(DiagnosticCode::TypeMistmatch.code())
							.with_message(
								"struct pattern does not match the value",
							)
							.with_label(
								Label::primary(file_id, pattern.span)
									.with_message(message),
							),
					);
				}
				for field in fields.iter() {
					self.bind_struct_pattern_field(
						ctx,
						&field.inner,
						TypeIndex::ERROR,
						path,
						out,
					);
				}
				return;
			}
		};

		let field_count = self.tir.structs[struct_index as usize].fields.len();
		let mut first_mention: Vec<Option<TextSpan>> = vec![None; field_count];

		for field in fields.iter() {
			let name = field.inner.inner.name;
			let Some(resolved) = self.resolve_struct_field(
				ctx.resolve_context,
				struct_index,
				&args,
				name,
				FieldAccessKind::Read,
			) else {
				let struct_name = self
					.interner
					.resolve(self.tir.structs[struct_index as usize].name.inner)
					.unwrap()
					.to_string();
				let field_name =
					self.interner.resolve(name.inner).unwrap().to_string();
				self.tir.diagnostics.push(report_unknown_struct_field(
					UnknownStructFieldDiagnostic {
						file_id,
						struct_name: &struct_name,
						field_name: &field_name,
						field_span: name.span,
					},
				));
				self.bind_struct_pattern_field(
					ctx,
					&field.inner,
					TypeIndex::ERROR,
					path,
					out,
				);
				continue;
			};

			let field_index = resolved.index.as_usize();
			if let Some(first_span) = first_mention[field_index] {
				let field_name =
					self.interner.resolve(name.inner).unwrap().to_string();
				self.tir
					.diagnostics
					.push(report_duplicate_struct_field_init(
						&field_name,
						SourceSpan::new(file_id, first_span),
						SourceSpan::new(file_id, name.span),
					));
			} else {
				first_mention[field_index] = Some(name.span);
			}

			path.push(PathStep {
				aggregate_ty: ty,
				index: resolved.index.as_u32(),
			});
			self.bind_struct_pattern_field(
				ctx,
				&field.inner,
				resolved.ty,
				path,
				out,
			);
			path.pop();
		}

		if rest.is_none() {
			let missing: Box<[&str]> = first_mention
				.iter()
				.enumerate()
				.filter(|(_, mention)| mention.is_none())
				.map(|(index, _)| {
					self.interner
						.resolve(
							self.tir.structs[struct_index as usize].fields
								[index]
								.name
								.inner,
						)
						.unwrap()
				})
				.collect();
			if !missing.is_empty() {
				let fields_str = missing
					.iter()
					.map(|field| format!("`{}`", field))
					.collect::<Vec<_>>()
					.join(", ");
				let struct_name = self
					.interner
					.resolve(self.tir.structs[struct_index as usize].name.inner)
					.unwrap();
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::MissingStructFields.code())
						.with_message(format!(
							"missing fields {} in pattern for `{}`",
							fields_str, struct_name
						))
						.with_note(
							"add the remaining fields, or end the pattern with `..` to ignore them",
						)
						.with_label(Label::primary(file_id, pattern.span)),
				);
			}
		}
	}

	/// Binds one entry of a struct pattern. `{ x }` is shorthand for
	/// `{ x: x }`, so a field with no sub-pattern binds a local named after
	/// the field itself.
	fn bind_struct_pattern_field(
		&mut self,
		ctx: &mut ExprContext,
		field: &Spanned<ast::PatternField>,
		field_ty: TypeIndex,
		path: &mut Vec<PathStep>,
		out: &mut Vec<PatternBinding>,
	) {
		match &field.inner.pattern {
			Some(sub_pattern) => self.collect_pattern_bindings(
				ctx,
				sub_pattern,
				field_ty,
				path,
				out,
			),
			None => {
				let local_index = ctx.push_local(Local {
					name: field.inner.name,
					ty: field_ty,
					mut_span: None,
					accesses: Vec::new(),
				});
				out.push(PatternBinding {
					scope_index: ctx.scope_index,
					local_index,
					path: path.as_slice().into(),
				});
			}
		}
	}
}

fn report_missing_else_block(
	fmt: TypeFormatter,
	then_ty: TypeIndex,
	then_span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingElseBlock.code())
		.with_message("`if` may be missing an `else` clause")
		.with_label(then_span.primary_label().with_message(format!(
			"expected `()`, found `{}`",
			fmt.display_type(then_ty).unwrap()
		)))
		.with_note("`if` expressions without `else` evaluate to `()`")
		.with_note(
			"consider adding an `else` block that evaluates to the expected type",
		)
}

fn report_invalid_match_scrutinee_type(
	fmt: TypeFormatter,
	ty: TypeIndex,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidMatchScrutineeType.code())
		.with_message("invalid `match` scrutinee type")
		.with_label(span.primary_label().with_message(format!(
			"cannot match on `{}`",
			fmt.display_type(ty).unwrap_or_default()
		)))
		.with_note(
			"`match` scrutinees must be an enum, integer, `char`, or `bool`",
		)
}

fn report_invalid_pattern(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidPattern.code())
		.with_message("invalid pattern")
		.with_label(span.primary_label())
		.with_note(
			"patterns are: an integer/char/bool literal, `EnumName::Variant`, or `_`",
		)
}

/// One diagnostic per non-exhaustive `match` on an enum scrutinee, grouping
/// every uncovered variant into one message — mirrors
/// `report_unused_enum_variants`'s 1/2/3-5/many phrasing.
fn report_non_exhaustive_match(
	interner: &ast::StringInterner,
	span: SourceSpan,
	missing_variants: &[Spanned<SymbolU32>],
) -> Diagnostic<FileId> {
	let message = match missing_variants.len() {
		1 => {
			let name = interner.resolve(missing_variants[0].inner).unwrap();
			format!("non-exhaustive `match`: variant `{name}` not covered")
		}
		2 => {
			let a = interner.resolve(missing_variants[0].inner).unwrap();
			let b = interner.resolve(missing_variants[1].inner).unwrap();
			format!(
				"non-exhaustive `match`: variants `{a}` and `{b}` not covered"
			)
		}
		3..=5 => {
			let (last, rest) = missing_variants.split_last().unwrap();
			let rest = rest
				.iter()
				.map(|name| {
					format!("`{}`", interner.resolve(name.inner).unwrap())
				})
				.collect::<Vec<_>>()
				.join(", ");
			let last = interner.resolve(last.inner).unwrap();
			format!(
				"non-exhaustive `match`: variants {rest}, and `{last}` not covered"
			)
		}
		_ => {
			"non-exhaustive `match`: multiple variants not covered".to_string()
		}
	};
	Diagnostic::error()
		.with_code(DiagnosticCode::NonExhaustiveMatch.code())
		.with_message(message)
		.with_label(span.primary_label())
		.with_note("add a wildcard arm `_ -> { ... }` or cover every variant")
}

fn report_non_exhaustive_match_no_wildcard(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::NonExhaustiveMatch.code())
		.with_message(
			"non-exhaustive `match`: this type's values cannot be fully enumerated",
		)
		.with_label(span.primary_label())
		.with_note(
			"add a wildcard arm `_ -> { ... }` to handle any other value",
		)
}

fn report_unreachable_match_arm(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::UnreachableMatchArm.code())
		.with_message("unreachable match arm")
		.with_label(
			span.primary_label().with_message(
				"this pattern is already covered by an earlier arm",
			),
		)
}

fn report_undeclared_label(
	label_name: &str,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredLabel.code())
		.with_message(format!("use of undeclared label `{}`", label_name))
		.with_label(span.primary_label().with_message("undeclared label"))
}

fn report_break_outside_of_loop(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::BreakOutsideOfLoop.code())
		.with_message("`break` outside of a loop or labeled block")
		.with_label(span.primary_label())
		.with_note("cannot `break` outside of a loop or labeled block")
}
