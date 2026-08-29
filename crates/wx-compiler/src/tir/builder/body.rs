//! Phase 3 — function bodies. The entry point that walks a body, the block and
//! statement machinery it is built from, `local` definitions, and the
//! expression dispatcher that routes each expression kind to its own module.

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Resolves the body of `def_id`. Not idempotent — calling twice
	/// double-counts accesses.
	pub(super) fn ensure_body(&mut self, def_id: ast::DefId) {
		self.ensure_signature(def_id);

		let node_idx = self.sig_state.get(&def_id).unwrap().node_idx;
		let AstEntry {
			file_id,
			namespace,
			node,
			..
		} = self.ast_nodes[node_idx].clone();

		let (sig, body_expr, func_index, self_type) = match node {
			AstNodeRef::Function { item } => match item {
				ast::Item::Function {
					id,
					signature,
					block,
					..
				} => {
					let func_index = self.tir.expect_function_index(*id);
					(signature, block.as_ref(), func_index, None)
				}
				ast::Item::FunctionDeclaration { id, signature, .. } => {
					let func_index = self.tir.expect_function_index(*id);
					if self.tir.functions[func_index as usize]
						.attributes
						.contains(&ItemAttribute::Intrinsic)
					{
						/* allow missing body for intrinsics */
					} else {
						self.tir.diagnostics.push(
							report_missing_function_body(SourceSpan::new(
								file_id,
								signature.name.span,
							)),
						);
					}
					return;
				}
				_ => unreachable!(),
			},
			AstNodeRef::TraitImplFunction {
				item, parent_id, ..
			} => {
				let ast::ImplItem::Function {
					id,
					signature,
					block,
					..
				} = item
				else {
					return;
				};
				let Some(fi) = self.tir.function_index(*id) else {
					return;
				};
				let self_type = self
					.tir
					.trait_impl_index(parent_id)
					.map(|idx| self.tir.trait_impls[idx as usize].target.inner);
				(signature, block.as_ref(), fi, self_type)
			}
			AstNodeRef::InherentImplFunction {
				item, block_index, ..
			} => {
				let ast::ImplItem::Function {
					id,
					signature,
					block,
					..
				} = item
				else {
					return;
				};
				let Some(fi) = self.tir.function_index(*id) else {
					return;
				};
				let self_type = Some(
					self.tir.inherent_impls[block_index as usize].target.inner,
				);
				(signature, block.as_ref(), fi, self_type)
			}
			AstNodeRef::TraitFunction { trait_index, item } => {
				let ast::TraitItem::Function {
					id,
					signature,
					body: Some(body),
					..
				} = item
				else {
					return;
				};
				let Some(fi) = self.tir.function_index(*id) else {
					return;
				};
				let self_type = Some(self.intern_type(Type::TypeParam {
					owner: TypeParamOwner::Trait(trait_index),
					param_index: 0,
				}));
				(signature, body.as_ref(), fi, self_type)
			}
			AstNodeRef::Global { item } => {
				let ast::Item::Global { id, value, .. } = item else {
					unreachable!();
				};

				let global_index = self.tir.expect_global_index(*id);
				let global_ty =
					self.tir.globals[global_index as usize].ty.inner;

				let root_scope = BlockScope {
					parent: None,
					label: None,
					kind: BlockKind::Block,
					span: value.span,
					locals: Vec::new(),
					inferred_type: TypeIndex::INFER,
					expected_type: global_ty,
				};
				let mut func_ctx = ExprContext {
					stack: StackFrame {
						scopes: vec![root_scope],
						labels: Vec::new(),
					},
					scope_index: 0 as ScopeIndex,
					lookup: HashMap::new(),
					resolve_context: ResolveContext::new(file_id, namespace),
					// Globals can't be generic and have no `Self` — no honest
					// `GenericScope` to give them.
					scope: None,
					// A global's initializer is genuine executable code (a
					// synthesized `start` function actually runs it — see
					// `EvalMode`'s doc comment), so operator dispatch applies
					// here exactly as in a regular function body.
					mode: EvalMode::Runtime(
						self.operator_traits
							.clone()
							.expect("operator traits resolved after Phase 2"),
					),
				};
				let mut value_expr = match self.build_expression(
					&mut func_ctx,
					AccessContext {
						expected_type: global_ty,
						access_kind: AccessKind::Read,
					},
					value,
				) {
					Ok(expr) => expr,
					Err(_) => return,
				};

				if value_expr.ty.is_comptime_number()
					&& global_ty != TypeIndex::INFER
				{
					_ = self.coerce_untyped_expr(
						&mut func_ctx,
						&mut value_expr,
						global_ty,
					);
				}

				if value_expr.ty.is_comptime_number() {
					self.tir.diagnostics.push(report_type_annotation_required(
						SourceSpan::new(
							func_ctx.resolve_context.file_id,
							value.span,
						),
					));
				} else if !self.coercible_to(value_expr.ty, global_ty) {
					self.tir.diagnostics.push(report_type_mistmatch(
						self.formatter(func_ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type: global_ty,
							actual_type: value_expr.ty,
							span: SourceSpan::new(
								func_ctx.resolve_context.file_id,
								value.span,
							),
						},
					));
				} else if self.tir.globals[global_index as usize]
					.mut_span
					.is_none() && !matches!(
					value_expr.kind,
					ExprKind::Int { .. } | ExprKind::Float { .. }
				) {
					self.tir.diagnostics.push(
						report_non_constant_global_initializer(
							SourceSpan::new(
								func_ctx.resolve_context.file_id,
								value.span,
							),
						),
					);
				}

				self.report_stack_warnings(
					func_ctx.resolve_context.file_id,
					&func_ctx.stack,
				);

				self.tir.globals[global_index as usize].value =
					Some(FunctionBody {
						block: Box::new(value_expr),
						stack: func_ctx.stack,
					});

				return;
			}
			_ => return,
		};

		// Self is TypeParam{0} in trait default methods (see ensure_signature).
		let resolve_context = ResolveContext::new(file_id, namespace);
		let scope = GenericScope {
			owner: TypeParamOwner::Function(
				self.tir.functions[func_index as usize].id,
			),
			self_type,
		};

		if let Ok(body) = self.build_function_body(
			resolve_context,
			&scope,
			sig,
			body_expr,
			func_index,
		) {
			self.tir.functions[func_index as usize].body = Some(body);
		}
	}

	fn build_function_body(
		&mut self,
		resolve_context: ResolveContext,
		scope: &GenericScope,
		signature: &ast::FunctionSignature,
		block: &Spanned<ast::Expression>,
		func_index: FunctionIndex,
	) -> Result<FunctionBody, ()> {
		let lookup = signature
			.params
			.iter()
			.enumerate()
			.map(|(index, param)| {
				(
					(0 as ScopeIndex, param.inner.inner.name.inner),
					index as LocalIndex,
				)
			})
			.collect();

		let root_scope = BlockScope {
			parent: None,
			label: None,
			kind: BlockKind::Block,
			span: block.span,
			locals: self.tir.functions[func_index as usize]
				.params
				.iter()
				.map(|param| Local {
					name: param.name,
					accesses: Vec::new(),
					mut_span: param.mut_span,
					ty: param.ty.inner,
				})
				.collect(),
			inferred_type: TypeIndex::INFER,
			expected_type: self.tir.functions[func_index as usize]
				.result
				.map(|ty| ty.inner)
				.unwrap_or(TypeIndex::UNIT),
		};

		let mut ctx = ExprContext {
			stack: StackFrame {
				scopes: vec![root_scope],
				labels: Vec::new(),
			},
			scope_index: 0 as ScopeIndex,
			lookup,
			resolve_context,
			scope: Some(GenericScope {
				owner: scope.owner,
				self_type: scope.self_type,
			}),
			mode: EvalMode::Runtime(
				self.operator_traits
					.clone()
					.expect("operator traits resolved after Phase 2"),
			),
		};
		let statements = block.inner.as_block_statements();
		let result =
			self.build_block_expression(&mut ctx, statements, block.span)?;
		self.report_stack_warnings(ctx.resolve_context.file_id, &ctx.stack);
		Ok(FunctionBody {
			block: Box::new(result),
			stack: ctx.stack,
		})
	}

	pub(super) fn build_block_expression(
		&mut self,
		ctx: &mut ExprContext,
		statements: &[Separated<Spanned<Statement>>],
		block_span: TextSpan,
	) -> Result<Expression, ()> {
		let (statements, result) = match statements.split_last() {
			Some((last, rest)) if last.separator.is_none() => {
				match &last.inner.inner {
					Statement::Expression(expr) => (rest, Some(expr.as_ref())),
					_ => (statements, None),
				}
			}
			_ => (statements, None),
		};

		let expressions = match self.build_block_statements(ctx, statements) {
			BlockState::Exhaustive(expressions) => {
				let unreachable_start = statements
					.get(expressions.len())
					.map(|s| s.inner.span.start)
					.or_else(|| result.as_ref().map(|r| r.span.start));

				let unreachable_end = result
					.map(|r| r.span.end)
					.or_else(|| statements.last().map(|s| s.inner.span.end));

				if let (Some(start), Some(end)) =
					(unreachable_start, unreachable_end)
				{
					self.tir.diagnostics.push(report_unreachable_code(
						SourceSpan::new(
							ctx.resolve_context.file_id,
							TextSpan::new(start, end),
						),
					));
				}

				let scope = &mut ctx.stack.scopes[ctx.scope_index as usize];
				let inferred_type =
					scope.inferred_type.infer_or(TypeIndex::NEVER);
				scope.inferred_type = inferred_type;

				return Ok(Expression {
					kind: ExprKind::Block {
						scope_index: ctx.scope_index,
						expressions,
						result: None,
					},
					ty: inferred_type,
					span: block_span,
				});
			}
			BlockState::Incomplete(expressions) => expressions,
		};

		match ctx.stack.scopes[ctx.scope_index as usize].kind {
			BlockKind::Loop => {
				let result = match result {
					Some(result) => Some(self.build_expression(
						ctx,
						AccessContext {
							expected_type: TypeIndex::UNIT,
							access_kind: AccessKind::Read,
						},
						result,
					)?),
					None => None,
				};

				let scope = &ctx.stack.scopes[ctx.scope_index as usize];
				let inferred_type =
					scope.inferred_type.infer_or(TypeIndex::NEVER);
				Ok(Expression {
					kind: ExprKind::Block {
						scope_index: ctx.scope_index,
						expressions,
						result: result.map(Box::new),
					},
					ty: inferred_type,
					span: block_span,
				})
			}
			BlockKind::Block => {
				let result = self.build_block_result(ctx, result)?;

				let scope = &ctx.stack.scopes[ctx.scope_index as usize];
				let inferred_type = scope.inferred_type;
				let expected_type = scope.expected_type;
				let block_ty = if expected_type != TypeIndex::INFER
					&& !self.coercible_to(inferred_type, expected_type)
				{
					self.tir.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type,
							actual_type: inferred_type,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								block_span,
							),
						},
					));
					TypeIndex::ERROR
				} else {
					inferred_type
				};

				Ok(Expression {
					kind: ExprKind::Block {
						scope_index: ctx.scope_index,
						expressions,
						result: result.map(Box::new),
					},
					ty: block_ty,
					span: block_span,
				})
			}
		}
	}

	fn build_block_result(
		&mut self,
		ctx: &mut ExprContext,
		result: Option<&Spanned<ast::Expression>>,
	) -> Result<Option<Expression>, ()> {
		match result {
			Some(result) => {
				let mut result = self.build_expression(
					ctx,
					AccessContext {
						expected_type: ctx.stack.scopes
							[ctx.scope_index as usize]
							.expected_type,
						access_kind: AccessKind::Read,
					},
					result,
				)?;

				let scope = &mut ctx.stack.scopes[ctx.scope_index as usize];
				let inferred_type =
					self.infer_block_type(ctx.resolve_context, scope, &result)?;
				scope.inferred_type = inferred_type;
				if result.ty.is_comptime_number()
					&& !inferred_type.is_comptime_number()
				{
					_ = self.coerce_untyped_expr(
						ctx,
						&mut result,
						inferred_type,
					);
				}

				Ok(Some(result))
			}
			None => {
				let scope = &mut ctx.stack.scopes[ctx.scope_index as usize];
				let inferred_type =
					scope.inferred_type.infer_or(TypeIndex::UNIT);
				scope.inferred_type = inferred_type;

				Ok(None)
			}
		}
	}

	fn build_block_statements(
		&mut self,
		ctx: &mut ExprContext,
		statements: &[Separated<Spanned<ast::Statement>>],
	) -> BlockState {
		let mut expressions = Vec::with_capacity(statements.len());
		for stmt in statements.iter() {
			let result = match &stmt.inner.inner {
				ast::Statement::Expression(_) => {
					self.build_expression_statement(ctx, &stmt.inner.inner)
				}
				ast::Statement::LocalDefinition { .. } => {
					self.build_local_definition_statement(ctx, stmt)
				}
			};
			let expr = match result {
				Ok(expr) => expr,
				Err(_) => continue,
			};

			match expr.ty {
				_ if expr.ty == TypeIndex::NEVER => {
					expressions.push(expr);
					return BlockState::Exhaustive(
						expressions.into_boxed_slice(),
					);
				}
				_ => {
					// Expression statement with unused value (already reported as warning)
					// Treat it as a Unit statement
					expressions.push(expr);
				}
			}
		}

		BlockState::Incomplete(expressions.into_boxed_slice())
	}

	pub(super) fn infer_block_type(
		&mut self,
		resolve_context: ResolveContext,
		scope: &BlockScope,
		value: &Expression,
	) -> Result<TypeIndex, ()> {
		let file_id = resolve_context.file_id;
		if value.ty.is_comptime_number() {
			let coerce_to = scope.inferred_type.infer_or(scope.expected_type);
			if coerce_to != TypeIndex::INFER {
				return Ok(coerce_to);
			} else {
				// No type context — let the comptime type bubble up. The caller
				// (e.g. build_if_else_expression) may resolve it via the other branch.
				return Ok(value.ty);
			}
		}
		let result_type = value.ty;
		if scope.inferred_type != TypeIndex::INFER {
			let inferred_type = scope.inferred_type;
			if !self.coercible_to(result_type, inferred_type) {
				self.tir.diagnostics.push(report_type_mistmatch(
					self.formatter(resolve_context.namespace),
					TypeMistmatchDiagnostic {
						expected_type: inferred_type,
						actual_type: result_type,
						span: SourceSpan::new(file_id, value.span),
					},
				));
			}
			Ok(inferred_type)
		} else if scope.expected_type != TypeIndex::INFER {
			let expected_type = scope.expected_type;
			if !self.coercible_to(result_type, expected_type) {
				self.tir.diagnostics.push(report_type_mistmatch(
					self.formatter(resolve_context.namespace),
					TypeMistmatchDiagnostic {
						expected_type,
						actual_type: result_type,
						span: SourceSpan::new(file_id, value.span),
					},
				));
				return Err(());
			}
			Ok(result_type)
		} else {
			Ok(result_type)
		}
	}

	fn build_expression_statement(
		&mut self,
		ctx: &mut ExprContext,
		stmt: &ast::Statement,
	) -> Result<Expression, ()> {
		let value = match &stmt {
			ast::Statement::Expression(value) => value,
			_ => unreachable!(),
		};

		let value = self.build_expression(
			ctx,
			AccessContext {
				access_kind: AccessKind::Read,
				expected_type: TypeIndex::INFER,
			},
			value,
		)?;
		if value.ty == TypeIndex::UNIT {
			return Ok(value);
		} else if value.ty == TypeIndex::ERROR {
			// Skip reporting unused value for error types, as the error has already been
			// reported
			return Ok(value);
		} else if value.ty == TypeIndex::NEVER {
			let scope =
				ctx.stack.scopes.get_mut(ctx.scope_index as usize).unwrap();
			if scope.inferred_type == TypeIndex::INFER {
				scope.inferred_type = TypeIndex::NEVER;
			}
			return Ok(value);
		} else if value.ty.is_comptime_number() {
			self.tir.diagnostics.push(report_type_annotation_required(
				SourceSpan::new(ctx.resolve_context.file_id, value.span),
			));
			return Err(());
		}
		self.tir
			.diagnostics
			.push(report_unused_value(SourceSpan::new(
				ctx.resolve_context.file_id,
				value.span,
			)));
		Ok(value)
	}

	pub(super) fn build_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		match &expr.inner {
			ast::Expression::QualifiedPath { root, segments } => self
				.build_qualified_path_expression(
					func_ctx, root, segments, expr.span,
				),
			ast::Expression::Grouped { inner, segments } => self
				.build_grouped_path_expression(
					func_ctx, inner, segments, expr.span,
				),
			ast::Expression::Int { value } => Ok(Expression {
				kind: ExprKind::Int { value: *value },
				ty: TypeIndex::INTEGER,
				span: expr.span,
			}),
			ast::Expression::Float { value } => Ok(Expression {
				kind: ExprKind::Float { value: *value },
				ty: TypeIndex::FLOAT,
				span: expr.span,
			}),
			ast::Expression::Unreachable => Ok(Expression {
				kind: ExprKind::Unreachable,
				ty: TypeIndex::NEVER,
				span: expr.span,
			}),
			ast::Expression::True => Ok(Expression {
				kind: ExprKind::Bool { value: true },
				ty: TypeIndex::BOOL,
				span: expr.span,
			}),
			ast::Expression::False => Ok(Expression {
				kind: ExprKind::Bool { value: false },
				ty: TypeIndex::BOOL,
				span: expr.span,
			}),
			ast::Expression::Placeholder => Ok(Expression {
				kind: ExprKind::Placeholder,
				ty: access_ctx.expected_type.infer_or(TypeIndex::ERROR),
				span: expr.span,
			}),
			ast::Expression::Error => Ok(Expression {
				kind: ExprKind::Error,
				ty: TypeIndex::ERROR,
				span: expr.span,
			}),
			ast::Expression::String => {
				let source = &self
					.files
					.get(func_ctx.resolve_context.file_id)
					.unwrap()
					.source;
				let raw = expr.span.extract_str(source);
				let unescaped = unescape_string(raw);
				let symbol = self.interner.get_or_intern(&unescaped);
				// An expected slice type pins the literal's memory (`local
				// s: other::&[u8] = "…"`); ambient resolution is the
				// fallback and is ambiguous with more than one memory.
				let memory_ty = match &self.tir.types
					[access_ctx.expected_type.as_usize()]
				{
					Type::Slice { memory, .. } => *memory,
					_ => self.resolve_ambient_memory(SourceSpan::new(
						func_ctx.resolve_context.file_id,
						expr.span,
					))?,
				};
				Ok(Expression {
					kind: ExprKind::String { symbol },
					ty: self.intern_type(Type::Slice {
						of: TypeIndex::U8,
						memory: memory_ty,
						ownership: ast::Ownership::Shared,
					}),
					span: expr.span,
				})
			}
			ast::Expression::Char => {
				let source = &self
					.files
					.get(func_ctx.resolve_context.file_id)
					.unwrap()
					.source;
				let raw = expr.span.extract_str(source);
				match parse_char_literal(raw) {
					Ok(value) => Ok(Expression {
						kind: ExprKind::Char { value },
						ty: TypeIndex::CHAR,
						span: expr.span,
					}),
					Err(CharLiteralError::Empty) => {
						self.tir.diagnostics.push(report_empty_char_literal(
							SourceSpan::new(
								func_ctx.resolve_context.file_id,
								expr.span,
							),
						));
						Err(())
					}
					Err(CharLiteralError::TooLong) => {
						self.tir.diagnostics.push(
							report_char_literal_too_long(SourceSpan::new(
								func_ctx.resolve_context.file_id,
								expr.span,
							)),
						);
						Err(())
					}
				}
			}
			ast::Expression::Path(path) => self
				.build_path_expression(func_ctx, access_ctx, path, expr.span),
			ast::Expression::Binary { .. } => {
				self.build_binary_expression(func_ctx, access_ctx, expr)
			}
			ast::Expression::Grouping { value } => {
				self.build_expression(func_ctx, access_ctx, value)
			}
			ast::Expression::Unary { .. } => {
				self.build_unary_expression(func_ctx, access_ctx, expr)
			}
			ast::Expression::Call { .. } => {
				self.build_call_expression(func_ctx, access_ctx, expr)
			}
			ast::Expression::MethodCall(_) => {
				self.build_method_call_expression(func_ctx, access_ctx, expr)
			}
			ast::Expression::ObjectAccess { object, member } => self
				.build_object_access_expression(
					func_ctx, access_ctx, object, *member, expr.span,
				),
			ast::Expression::Deref { pointer } => self.build_deref_expression(
				func_ctx, access_ctx, expr.span, pointer,
			),
			ast::Expression::Return { .. } => {
				self.build_return_expression(func_ctx, expr)
			}
			ast::Expression::Block { .. } => func_ctx.enter_block(
				BlockScope {
					label: None,
					kind: BlockKind::Block,
					parent: Some(func_ctx.scope_index),
					span: expr.span,
					locals: Vec::new(),
					inferred_type: TypeIndex::INFER,
					expected_type: access_ctx.expected_type,
				},
				|ctx| {
					self.build_block_expression(
						ctx,
						expr.inner.as_block_statements(),
						expr.span,
					)
				},
			),
			ast::Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => self.build_if_else_expression(
				func_ctx,
				access_ctx,
				condition,
				then_block,
				else_block.as_deref(),
				expr.span,
				None,
			),
			ast::Expression::Match { .. } => {
				self.build_match_expression(func_ctx, access_ctx, expr)
			}
			ast::Expression::Loop { block } => self.build_loop_expression(
				func_ctx, access_ctx, block, expr.span, None,
			),
			ast::Expression::Cast { value, ty } => self.build_cast_expression(
				func_ctx, access_ctx, value, ty, expr.span,
			),
			ast::Expression::Break { .. } => {
				self.build_break_expression(func_ctx, expr)
			}
			ast::Expression::Continue { .. } => {
				self.build_continue_expression(func_ctx, expr)
			}
			ast::Expression::Label { block, label } => {
				self.build_label_expression(func_ctx, access_ctx, block, *label)
			}
			ast::Expression::StructInit { path, fields } => self
				.build_struct_init_expression(
					func_ctx, access_ctx, expr.span, path, fields,
				),
			ast::Expression::Tuple { elements } => self.build_tuple_expression(
				func_ctx, expr.span, elements, access_ctx,
			),
			ast::Expression::TypeApplication { callee, args } => self
				.build_type_application_expression(
					func_ctx, callee, args, expr.span,
				),
			ast::Expression::ArrayList { elements } => self
				.build_array_literal_expression(
					func_ctx, access_ctx, expr.span, elements,
				),
			ast::Expression::ArrayRepeat { value, count } => self
				.build_array_repeat_expression(
					func_ctx, access_ctx, expr.span, value, count,
				),
			ast::Expression::Index { object, index } => self
				.build_index_expression(
					func_ctx, access_ctx, expr.span, object, index,
				),
			ast::Expression::SliceRange { object, start, end } => self
				.build_slice_range_expression(
					func_ctx, expr.span, object, start, end,
				),
			ast::Expression::AddressOf { value } => {
				let operand = self.build_expression(
					func_ctx,
					AccessContext {
						expected_type: TypeIndex::INFER,
						access_kind: AccessKind::Read,
					},
					value,
				)?;
				match operand.kind {
					ExprKind::Load { place } => {
						let pointer_ty = self.intern_type(Type::Pointer {
							to: place.ty,
							memory: place.memory,
							ownership: ast::Ownership::Shared,
						});
						Ok(Expression {
							kind: ExprKind::AddressOf { place },
							ty: pointer_ty,
							span: expr.span,
						})
					}
					_ => {
						self.tir.diagnostics.push(
							report_cannot_take_address_of_value(
								SourceSpan::new(
									func_ctx.resolve_context.file_id,
									operand.span,
								),
							),
						);
						Err(())
					}
				}
			}
		}
	}

	fn build_local_definition_statement(
		&mut self,
		ctx: &mut ExprContext,
		stmt: &Separated<Spanned<ast::Statement>>,
	) -> Result<Expression, ()> {
		let ast::Statement::LocalDefinition { pattern, ty, value } =
			&stmt.inner.inner
		else {
			unreachable!()
		};

		let expected_type = match ty {
			Some(ty) => self.resolve_type(ctx.resolve_context, ctx.scope, ty),
			None => TypeIndex::INFER,
		};
		let value_result = self.build_expression(
			ctx,
			AccessContext {
				expected_type,
				access_kind: AccessKind::Read,
			},
			value,
		);

		let (ty, value) = match value_result {
			Err(()) => {
				// Expression failed; register the local with the declared type so
				// subsequent references don't produce cascading errors.
				let ty = expected_type.infer_or(TypeIndex::ERROR);
				let error_expr = Expression {
					kind: ExprKind::Error,
					ty: TypeIndex::ERROR,
					span: value.span,
				};
				(ty, error_expr)
			}
			Ok(mut value) => {
				let ty = self.resolve_local_type(
					ctx,
					pattern.span,
					&mut value,
					expected_type,
				)?;
				(ty, value)
			}
		};

		let statement_ty = if ty == TypeIndex::NEVER {
			TypeIndex::NEVER
		} else {
			TypeIndex::UNIT
		};

		let kind = match &pattern.inner {
			ast::Pattern::Binding { mut_span, name } => {
				let local_index = ctx.push_local(Local {
					name: *name,
					ty,
					mut_span: *mut_span,
					accesses: Vec::new(),
				});
				ExprKind::LocalDeclaration {
					name: *name,
					scope_index: ctx.scope_index,
					local_index,
					value: Box::new(value),
				}
			}
			// `local _ = f();` binds nothing. It exists only to run `f()` for
			// its effects and throw the result away — which is exactly what
			// `_ = f();` already means, so it lowers to the same node and
			// reaches MIR's existing `Drop`.
			ast::Pattern::Wildcard => ExprKind::Assign {
				left: Box::new(Expression {
					kind: ExprKind::Placeholder,
					ty,
					span: pattern.span,
				}),
				right: Box::new(value),
			},
			ast::Pattern::Tuple { .. } | ast::Pattern::Struct { .. } => {
				let mut bindings = Vec::new();
				let mut path = Vec::new();
				self.collect_pattern_bindings(
					ctx,
					pattern,
					ty,
					&mut path,
					&mut bindings,
				);
				ExprKind::DestructureDeclaration {
					value: Box::new(value),
					bindings: bindings.into_boxed_slice(),
				}
			}
		};

		Ok(Expression {
			kind,
			ty: statement_ty,
			span: stmt.inner.span,
		})
	}

	fn resolve_local_type(
		&mut self,
		ctx: &mut ExprContext,
		name_span: TextSpan,
		value: &mut Expression,
		expected_type: TypeIndex,
	) -> Result<TypeIndex, ()> {
		let file_id = ctx.resolve_context.file_id;
		if expected_type == TypeIndex::INFER {
			// TODO: impove diagnostic for case where value.ty contains infer
			if self.contains_comptime_number(value.ty)
				|| self.contains_infer(value.ty)
			{
				self.tir.diagnostics.push(report_type_annotation_required(
					SourceSpan::new(file_id, name_span),
				));
				return Ok(TypeIndex::ERROR);
			}
			return Ok(value.ty);
		}

		if value.ty == TypeIndex::ERROR {
			return Ok(expected_type);
		}

		if value.ty.is_comptime_number() {
			if self.coerce_untyped_expr(ctx, value, expected_type).is_err() {
				return Ok(TypeIndex::ERROR);
			}
			return Ok(expected_type);
		}

		if self.contains_infer(expected_type) {
			if self.type_satisfies_annotation(value.ty, expected_type) {
				return Ok(value.ty);
			}
			self.tir.diagnostics.push(report_type_mistmatch(
				self.formatter(ctx.resolve_context.namespace),
				TypeMistmatchDiagnostic {
					expected_type,
					actual_type: value.ty,
					span: SourceSpan::new(file_id, value.span),
				},
			));
			return Ok(expected_type);
		}

		if self.coercible_to(value.ty, expected_type) {
			return Ok(expected_type);
		}

		self.tir.diagnostics.push(report_type_mistmatch(
			self.formatter(ctx.resolve_context.namespace),
			TypeMistmatchDiagnostic {
				expected_type,
				actual_type: value.ty,
				span: SourceSpan::new(file_id, value.span),
			},
		));
		Ok(expected_type)
	}

	fn report_stack_warnings(&mut self, file_id: FileId, stack: &StackFrame) {
		for label in stack.labels.iter() {
			if label.accesses.is_empty() {
				self.tir.diagnostics.push(
					Diagnostic::warning()
						.with_code(DiagnosticCode::UnusedLabel.code())
						.with_message("unused label")
						.with_label(
							SourceSpan::new(file_id, label.name.span)
								.primary_label(),
						),
				);
			}
		}

		let self_symbol = self.interner.get_or_intern("self");
		for scope in stack.scopes.iter() {
			for local in scope.locals.iter() {
				let is_underscore_prefixed = self
					.interner
					.resolve(local.name.inner)
					.is_some_and(|name| name.starts_with('_'));
				// `self` is a keyword, so this is unambiguously the
				// method/trait-fn receiver, never an ordinary local — match
				// Rust, which never warns about an unused `self`, since a
				// method not reading its receiver (e.g. state lives in a
				// global instead) is a normal, deliberate pattern.
				let is_self = local.name.inner == self_symbol;
				if local.accesses.is_empty()
					&& local.ty != TypeIndex::ERROR
					&& !is_underscore_prefixed
					&& !is_self
				{
					self.tir.diagnostics.push(report_unused_variable(
						SourceSpan::new(file_id, local.name.span),
					));
				}

				match local.mut_span {
					Some(mut_span)
						if !local.accesses.iter().any(|access| {
							access.kind == AccessKind::Write
								|| access.kind == AccessKind::ReadWrite
						}) =>
					{
						self.tir.diagnostics.push(
							report_unnecessary_mutability(SourceSpan::new(
								file_id, mut_span,
							)),
						);
					}
					_ => {}
				}
			}
		}
	}
}

enum BlockState {
	Exhaustive(Box<[Expression]>),
	Incomplete(Box<[Expression]>),
}

fn report_unused_variable(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::UnusedVariable.code())
		.with_message("unused variable")
		.with_label(span.primary_label())
}

fn report_unnecessary_mutability(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::UnnecessaryMutability.code())
		.with_message("unnecessary mutability")
		.with_label(span.primary_label())
}

fn report_unused_value(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnusedValue.code())
		.with_message("value must be used")
		.with_label(span.primary_label().with_message("value never used"))
		.with_note(
			"if you don't need the value, consider dropping it with assignment to `_`",
		)
}
