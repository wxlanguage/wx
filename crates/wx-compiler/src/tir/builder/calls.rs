//! Calls and method dispatch: plain and generic call arguments, `obj.method()`
//! and `Type::method()` resolution against inherent and trait impls, and the
//! abstract-method path that defers dispatch to monomorphisation.

use crate::diagnostics::DiagnosticCode;

use super::*;

impl<'ast> Builder<'ast, '_> {
	pub(super) fn build_call_expression(
		&mut self,
		ctx: &mut ExprContext,
		access_ctx: AccessContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (ast_callee, arguments) = match &expr.inner {
			ast::Expression::Call { callee, arguments } => (callee, arguments),
			_ => unreachable!(),
		};

		// A callee that failed outright becomes an error-typed expression
		// rather than propagating `Err`, so it lands in the non-function `_`
		// arm below — which already builds the arguments (so mistakes inside
		// the argument list still get reported) and already stays silent
		// about the callee itself once its type is `ERROR`.
		let callee = self
			.build_expression(
				ctx,
				AccessContext {
					expected_type: TypeIndex::INFER,
					access_kind: AccessKind::Read,
				},
				ast_callee,
			)
			.unwrap_or(Expression {
				kind: ExprKind::Error,
				ty: TypeIndex::ERROR,
				span: ast_callee.span,
			});
		let signature = match self.types.resolve(callee.ty) {
			Type::Function { signature } => signature.clone(),
			Type::FunctionItem { id, .. } => {
				let signature_index = self.items.functions
					[usize::from(self.items.expect_function_index(*id))]
				.signature_index;
				match self.types.resolve(signature_index) {
					Type::Function { signature } => signature.clone(),
					_ => unreachable!(),
				}
			}
			_ => {
				// Still trying to check arguments, even though we don't have
				// information about the parameters. `ERROR` rather than
				// `INFER` as the expected type: both mean "no parameter type
				// to check against", but `INFER` also means "so tell me what
				// it is", which makes `build_generic_call_arguments` demand
				// an annotation for a type parameter this missing callee is
				// the reason it couldn't pin down.
				let arguments: Box<_> = arguments
					.iter()
					.map(|arg| {
						match self.build_expression(
							ctx,
							AccessContext {
								expected_type: TypeIndex::ERROR,
								access_kind: AccessKind::Read,
							},
							&arg.inner,
						) {
							Ok(expr) => expr,
							Err(_) => Expression {
								kind: ExprKind::Error,
								ty: TypeIndex::ERROR,
								span: arg.inner.span,
							},
						}
					})
					.collect();

				if callee.ty != TypeIndex::ERROR {
					let formatter =
						self.formatter(ctx.resolve_context.namespace);
					let mut diagnostic = Diagnostic::error()
						.with_code(DiagnosticCode::CannotCallExpression.code())
						.with_message("call expression requires function")
						.with_label(
							SourceSpan::new(
								ctx.resolve_context.file_id,
								ast_callee.span,
							)
							.primary_label()
							.with_message(format!(
								"expected function, found `{}`",
								formatter.display_type(callee.ty).unwrap()
							)),
						);
					if ast_callee.inner.is_block_like() {
						diagnostic = diagnostic.with_note(
							"consider using a semicolon here to finish the statement: `;`",
						);
					}
					self.diagnostics.push(diagnostic);
				}

				return Ok(Expression {
					kind: ExprKind::Call {
						callee: Box::new(callee),
						arguments,
					},
					ty: TypeIndex::ERROR,
					span: expr.span,
				});
			}
		};
		if arguments.len() != signature.params().len() {
			self.diagnostics.push(report_argument_count_mismatch(
				self.formatter(ctx.resolve_context.namespace),
				ArgumentCountMismatchDiagnostic {
					actual_count: arguments.len(),
					params: signature.params(),
					call_span: SourceSpan::new(
						ctx.resolve_context.file_id,
						callee.span,
					),
					is_method: false,
				},
			));
		}

		let direct_id = match &callee.kind {
			ExprKind::Function { id } => Some(*id),
			ExprKind::NamespaceAccess { member, .. } => {
				if let ExprKind::Function { id } = &member.kind {
					Some(*id)
				} else {
					None
				}
			}
			_ => None,
		};
		if let Some(callee_id) = direct_id {
			let func_index = self.items.expect_function_index(callee_id);
			let type_params_len = self.items.functions[usize::from(func_index)]
				.total_type_param_count();
			if type_params_len > 0 {
				// FunctionItem.type_args is always padded to type_params_len (with
				// impl-level args pre-filled and remaining slots as INFER) by the time
				// we get here — build_namespace_member_expression enforces this invariant.
				let mut type_args: Box<[TypeIndex]> = match self
					.types
					.resolve(callee.ty)
				{
					Type::FunctionItem { type_args, .. } => type_args.clone(),
					_ => vec![TypeIndex::INFER; type_params_len]
						.into_boxed_slice(),
				};

				// Seed type_args from the call's own expected type *before*
				// building arguments, so an argument that's itself a generic
				// call (e.g. `Layout::of::<T>()`) can use it as inference
				// context instead of only being checked against it after the
				// fact — see test_generic_call_arg_infers_from_expected_type.
				if access_ctx.expected_type != TypeIndex::INFER {
					let result_type = self.items.functions
						[usize::from(func_index)]
					.result
					.as_ref()
					.map(|r| r.inner)
					.unwrap_or(TypeIndex::UNIT);
					// Ignored — see the identical seeding step in
					// `build_generic_call_arguments`.
					let _ = self.types.infer_type_args(
						&mut type_args,
						result_type,
						access_ctx.expected_type,
					);
				}

				let mut built_args = Vec::with_capacity(arguments.len());
				for (index, arg) in arguments.iter().enumerate() {
					let param_type = self.items.functions
						[usize::from(func_index)]
					.params
					.get(index)
					.map(|p| p.ty.inner);
					let expected_type = param_type
						.map(|pt| self.substitute_expected_type(pt, &type_args))
						.filter(|&t| !self.contains_infer(t))
						.unwrap_or(TypeIndex::INFER);
					let built = self.build_expression(
						ctx,
						AccessContext {
							expected_type,
							access_kind: AccessKind::Read,
						},
						&arg.inner,
					)?;
					if let Some(param_type) = param_type {
						// Ignored — see the identical per-argument step in
						// `build_generic_call_arguments`.
						let _ = self.types.infer_type_args(
							&mut type_args,
							param_type,
							built.ty,
						);
					}
					built_args.push(built);
				}

				let type_args = self.build_generic_call_arguments(
					ctx,
					func_index,
					&mut built_args,
					type_args,
					access_ctx.expected_type,
					expr.span,
				);
				let return_ty =
					self.substitute_type(signature.result(), &type_args);

				return Ok(Expression {
					kind: ExprKind::GenericCall {
						id: callee_id,
						type_args,
						arguments: built_args.into_boxed_slice(),
					},
					ty: return_ty,
					span: expr.span,
				});
			}
		}

		let arguments =
			self.build_call_arguments(ctx, arguments, signature.params(), &[]);
		Ok(Expression {
			kind: ExprKind::Call {
				callee: Box::new(callee),
				arguments,
			},
			ty: signature.result(),
			span: expr.span,
		})
	}

	fn build_call_arguments(
		&mut self,
		ctx: &mut ExprContext,
		arguments: &[Separated<Spanned<ast::Expression>>],
		params: &[TypeIndex],
		type_args: &[TypeIndex],
	) -> Box<[Expression]> {
		let mut result: Vec<Expression> = Vec::with_capacity(arguments.len());
		for (index, argument) in arguments.iter().enumerate() {
			let expected_type = params
				.get(index)
				.copied()
				.map(|param_type| {
					self.substitute_expected_type(param_type, type_args)
				})
				.unwrap_or(TypeIndex::INFER);

			let mut argument = match self.build_expression(
				ctx,
				AccessContext {
					expected_type,
					access_kind: AccessKind::Read,
				},
				&argument.inner,
			) {
				Ok(expr) => expr,
				Err(_) => {
					result.push(Expression {
						kind: ExprKind::Error,
						span: argument.inner.span,
						ty: TypeIndex::ERROR,
					});
					continue;
				}
			};

			if expected_type != TypeIndex::INFER {
				if argument.ty.is_comptime_number() {
					_ = self.coerce_untyped_expr(
						ctx,
						&mut argument,
						expected_type,
					);
				} else if !self.coercible_to(argument.ty, expected_type) {
					self.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type,
							actual_type: argument.ty,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								argument.span,
							),
						},
					));
				}
			} else if argument.ty.is_comptime_number() {
				self.diagnostics.push(report_type_annotation_required(
					SourceSpan::new(ctx.resolve_context.file_id, argument.span),
				));
			}

			result.push(argument);
		}

		result.into_boxed_slice()
	}

	/// Builds/coerces `arguments` against `func_index`'s signature and
	/// resolves `type_args`. Never fails: a type mismatch or unresolvable
	/// type param is reported as a diagnostic but the caller still gets back
	/// a usable `type_args` (any leftover `INFER` slot sanitized to `ERROR`)
	/// so it can keep building a real expression tree instead of discarding
	/// the whole call — see `test_generic_call_arg_mismatch_preserves_body`.
	fn build_generic_call_arguments(
		&mut self,
		ctx: &mut ExprContext,
		func_index: FunctionIndex,
		arguments: &mut [Expression],
		mut type_args: Box<[TypeIndex]>,
		expected_result: TypeIndex,
		call_span: TextSpan,
	) -> Box<[TypeIndex]> {
		let result_type = self.items.functions[usize::from(func_index)]
			.result
			.as_ref()
			.map(|r| r.inner)
			.unwrap_or(TypeIndex::UNIT);
		if expected_result != TypeIndex::INFER {
			// Ignored: an inconsistent result-type seed here is a real user
			// error, but it's caught below by the leftover-`INFER`/
			// substituted-result check, which reports a clearer diagnostic
			// than this structural signal could on its own.
			_ = self.types.infer_type_args(
				&mut type_args,
				result_type,
				expected_result,
			);
		}
		for (index, arg) in arguments.iter().enumerate() {
			let param_type = match self.items.functions[usize::from(func_index)]
				.params
				.get(index)
			{
				Some(p) => p.ty.inner,
				None => break,
			};
			// Ignored: a genuine mismatch here surfaces separately when
			// this argument gets checked against the (by-then substituted)
			// param type, with the actual expected/found types shown.
			_ = self
				.types
				.infer_type_args(&mut type_args, param_type, arg.ty);
		}

		// Detect unresolvable type parameters by substituting the current type_args
		// into the function's result type and checking whether INFER survives.
		//
		// substitute_type propagates INFER through TypeParam positions but leaves
		// AssocTypeProjection positions unchanged (because those are resolved
		// structurally at the call site rather than requiring a concrete type arg).
		// This means `contains_infer` on the substituted result is false for
		// params that appear only via `C::Item` style projections, and true for
		// params that appear directly (e.g. M in `Layout<M>`).
		let substituted_result = self.substitute_type(result_type, &type_args);
		if self.contains_infer(substituted_result) {
			// Nothing at this call site could pin these slots down. Whether
			// that's the user's problem depends on why there was nothing:
			// in a poisoned context (`expected_result == ERROR`) the
			// enclosing callee is already an error and took the inference
			// context down with it, so demanding an annotation would blame
			// the user for a gap the error itself opened. Elsewhere the
			// annotation genuinely is missing.
			//
			// Reaching here at all means the argument loop above already
			// had its chance to bind these slots, so an argument that does
			// constrain a param has bound it — which is why a mismatch
			// between two arguments sharing one param (`same(1, true)`)
			// still gets reported rather than absorbed.
			if expected_result != TypeIndex::ERROR {
				for (i, &slot) in type_args.iter().enumerate() {
					if slot == TypeIndex::INFER {
						let name_symbol = self
							.items
							.function_type_params_iter(func_index)
							.nth(i)
							.expect(
								"type_args length must equal total_type_param_count",
							)
							.name
							.inner;
						let param_name =
							self.interner.resolve(name_symbol).unwrap();
						self.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::TypeAnnotationRequired
										.code(),
								)
								.with_message(format!(
									"cannot infer type for type parameter `{param_name}`"
								))
								.with_label(
									Label::primary(
										ctx.resolve_context.file_id,
										call_span,
									)
									.with_message("type annotation required"),
								),
						);
					}
				}
			}
			// Unresolved either way: poison the open slots and skip the
			// argument checks below, which can only produce noise once the
			// result type is unknown.
			for slot in type_args.iter_mut() {
				if *slot == TypeIndex::INFER {
					*slot = TypeIndex::ERROR;
				}
			}
			return type_args;
		}

		let mut had_error = false;
		for (index, arg) in arguments.iter_mut().enumerate() {
			let param_type = match self.items.functions[usize::from(func_index)]
				.params
				.get(index)
			{
				Some(p) => p.ty.inner,
				None => break,
			};

			let substituted_expected =
				self.substitute_expected_type(param_type, &type_args);
			let expected_type = if self.contains_infer(substituted_expected) {
				// `substituted_expected` still has an open type-param slot
				// somewhere (e.g. `Box<T>` with `T` unresolved) — but an
				// open slot doesn't mean this argument is fine to defer on.
				// If `arg.ty` structurally can't match this shape no matter
				// what the open slot turns out to be (e.g. `i32` against
				// `Box<_>` — a scalar can never be a `Box`, regardless of
				// `T`), that's a real, unconditional mismatch, not a
				// "provide a type annotation" situation — report it here,
				// using the partially-substituted type so the message names
				// the real expected shape (`Box<_>`, not just `_`).
				if !self.type_satisfies_annotation(arg.ty, substituted_expected)
				{
					self.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type: substituted_expected,
							actual_type: arg.ty,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								arg.span,
							),
						},
					));
					had_error = true;
					continue;
				}
				TypeIndex::INFER
			} else {
				substituted_expected
			};

			if expected_type != TypeIndex::INFER {
				if arg.ty.is_comptime_number() {
					if self
						.coerce_untyped_expr(ctx, arg, expected_type)
						.is_err()
					{
						had_error = true;
					}
				} else if !self.coercible_to(arg.ty, expected_type) {
					self.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type,
							actual_type: arg.ty,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								arg.span,
							),
						},
					));
					had_error = true;
				}
			} else if arg.ty.is_comptime_number() {
				self.diagnostics.push(report_type_annotation_required(
					SourceSpan::new(ctx.resolve_context.file_id, arg.span),
				));
				had_error = true;
			}
		}

		// Any slot still INFER after return-type and argument inference is a
		// phantom param — one that appears nowhere in the function's signature
		// and can never be constrained.  Skip if coercion already failed to
		// avoid double-reporting on top of a TypeMistmatch.
		if !had_error {
			for (index, slot) in type_args.iter().copied().enumerate() {
				if slot == TypeIndex::INFER {
					let name_symbol = self
						.items
						.function_type_params_iter(func_index)
						.nth(index)
						.expect(
							"type_args length must equal total_type_param_count",
						)
						.name
						.inner;
					let param_name =
						self.interner.resolve(name_symbol).unwrap();
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::TypeAnnotationRequired.code(),
							)
							.with_message(format!(
								"cannot infer type for type parameter `{param_name}`"
							))
							.with_label(
								Label::primary(
									ctx.resolve_context.file_id,
									call_span,
								)
								.with_message("type annotation required"),
							),
					);
				}
			}
		}

		for slot in type_args.iter_mut() {
			if *slot == TypeIndex::INFER {
				*slot = TypeIndex::ERROR;
			}
		}

		// Collected here instead of pushed straight to `self.diagnostics`:
		// `param_info` below borrows `self.items` for the rest of each
		// iteration (both the trait loop and the typeset check use it, with
		// `continue`s in between), so nothing in this loop can also hold
		// `&mut self.diagnostics` at the same time. Costs nothing on the
		// common no-violation path — `Vec::new()` doesn't allocate until the
		// first `push` — unlike cloning `param_info.bounds` would on every
		// call regardless of outcome.
		let mut diagnostics: Vec<Diagnostic<FileId>> = Vec::new();
		// Every `(arg_ty, trait_bound)` pair whose bound carries at least one
		// `where { Assoc: Bound }` constraint — deferred and checked in a
		// second pass below, once the `function_type_params_iter` borrow
		// (held across this whole loop, same as the reason `diagnostics`
		// above is collected rather than pushed live) has ended, since
		// resolving a concrete associated-type value needs
		// `self.substitute_type` (`&mut self`), not just `&mut
		// self.diagnostics`. Cloning `trait_bound` only happens here, on
		// the path that already found a `: Bound` entry — the common case
		// (no `where` clause at all, or only `= Type` entries) never
		// allocates for this.
		let mut assoc_checks: Vec<(TypeIndex, TraitBound)> = Vec::new();
		// Zipped once, in lockstep, rather than re-deriving `param_info` via
		// a fresh `.nth(arg_index)` per iteration (which would re-walk the
		// chained parent/own type-param iterator from the start every time)
		// — safe now that nothing in this loop needs `&mut self.items`
		// (diagnostics are collected above instead), so holding this one
		// iterator borrowed across the whole loop is fine.
		for (index, (param_info, arg_ty)) in self
			.items
			.function_type_params_iter(func_index)
			.zip(type_args.iter().copied())
			.enumerate()
		{
			if arg_ty == TypeIndex::ERROR {
				continue;
			}
			// A declared bound can list several traits (`T: Foo + Bar`) —
			// report every one `arg_ty` fails, not just the first.
			for trait_bound in param_info.bounds.traits.iter() {
				if self.items.type_implements_trait(
					&self.types,
					arg_ty,
					trait_bound.trait_index,
				) {
					if trait_bound.bindings.iter().any(|(_, kind)| {
						matches!(kind, AssocBindingKind::Bound(_))
					}) {
						assoc_checks.push((arg_ty, trait_bound.clone()));
					}
					continue;
				}
				let type_name = self
					.formatter(ctx.resolve_context.namespace)
					.display_type(arg_ty)
					.unwrap_or_default();
				let trait_name = self
					.interner
					.resolve(
						self.items.traits[usize::from(trait_bound.trait_index)]
							.name
							.inner,
					)
					.unwrap();
				// Narrow the primary span to whichever argument's declared
				// type is exactly this type param, if one exists (a
				// turbofish-only or return-only param has none)
				let arg_span = self.items.functions[usize::from(func_index)]
					.params
					.iter()
					.zip(arguments.iter())
					.find_map(|(param, arg)| {
						match self.types.resolve(param.ty.inner) {
							Type::TypeParam { param_index, .. }
								if *param_index as usize == index =>
							{
								Some(arg.span)
							}
							_ => None,
						}
					})
					.unwrap_or(call_span);
				let func_name = self
					.interner
					.resolve(
						self.items.functions[usize::from(func_index)]
							.name
							.inner,
					)
					.unwrap();
				let func_file_id =
					self.items.functions[usize::from(func_index)].file_id;
				diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::TraitBoundViolation.code())
						.with_message(format!(
							"the trait bound `{type_name}: {trait_name}` is not satisfied"
						))
						.with_label(
							Label::primary(
								ctx.resolve_context.file_id,
								arg_span,
							)
							.with_message(format!(
								"the trait `{trait_name}` is not implemented for `{type_name}`"
							)),
						)
						.with_label(
							Label::secondary(func_file_id, trait_bound.span)
								.with_message(format!(
									"required by a bound in `{func_name}`"
								)),
						),
				);
			}

			let Some(param_bound) = param_info.bounds.typeset else {
				continue;
			};
			let satisfied = self.items.type_in_typeset(
				&self.types,
				arg_ty,
				param_bound.typeset_index,
			);
			if !satisfied {
				let type_name = self
					.formatter(ctx.resolve_context.namespace)
					.display_type(arg_ty)
					.unwrap_or_default();
				let set_name = self
					.interner
					.resolve(
						self.items.typesets
							[usize::from(param_bound.typeset_index)]
						.name
						.inner,
					)
					.unwrap();
				let param_name_str =
					self.interner.resolve(param_info.name.inner).unwrap();
				diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::TypesetBoundViolation.code())
						.with_message(format!(
							"type `{type_name}` is not a member of typeset `{set_name}`"
						))
						.with_label(
							Label::primary(
								ctx.resolve_context.file_id,
								call_span,
							)
							.with_message(format!(
								"`{param_name_str}` requires a type from `{set_name}`"
							)),
						),
				);
			}
		}
		self.diagnostics.extend(diagnostics);

		// Second pass: for each `T: Trait where { Assoc: Bound }` the call's
		// own arguments satisfied `T: Trait` for, also check that `Assoc`'s
		// *actual* concrete value (looked up through the now-concrete
		// `arg_ty`'s own impl) satisfies `Bound` — the part
		// `type_implements_trait` above can't see, since it only knows
		// about `trait_bound.trait_index` itself, not any associated-type
		// constraint layered onto it by the callee's `where` clause.
		for (arg_ty, trait_bound) in assoc_checks {
			for (assoc_name, kind) in trait_bound.bindings.iter() {
				let AssocBindingKind::Bound(required) = kind else {
					continue;
				};
				let Some(concrete) = self.concrete_assoc_type_value(
					arg_ty,
					trait_bound.trait_index,
					*assoc_name,
				) else {
					continue;
				};
				let assoc_name_str =
					self.interner.resolve(*assoc_name).unwrap();
				let concrete_name = self
					.formatter(ctx.resolve_context.namespace)
					.display_type(concrete)
					.unwrap_or_default();
				let func_name = self
					.interner
					.resolve(
						self.items.functions[usize::from(func_index)]
							.name
							.inner,
					)
					.unwrap();
				let func_file_id =
					self.items.functions[usize::from(func_index)].file_id;

				for req_trait in required.traits.iter() {
					if self.items.type_implements_trait(
						&self.types,
						concrete,
						req_trait.trait_index,
					) {
						continue;
					}
					let req_trait_name = self
						.interner
						.resolve(
							self.items.traits
								[usize::from(req_trait.trait_index)]
							.name
							.inner,
						)
						.unwrap();
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(DiagnosticCode::TraitBoundViolation.code())
							.with_message(format!(
								"the trait bound `{concrete_name}: {req_trait_name}` is not satisfied"
							))
							.with_label(
								Label::primary(
									ctx.resolve_context.file_id,
									call_span,
								)
								.with_message(format!(
									"associated type `{assoc_name_str}` is `{concrete_name}`, which does not implement `{req_trait_name}`"
								)),
							)
							.with_label(
								Label::secondary(func_file_id, trait_bound.span)
									.with_message(format!(
										"required by a `where` clause on `{func_name}`"
									)),
							),
					);
				}

				if let Some(req_typeset) = required.typeset
					&& !self.items.type_in_typeset(
						&self.types,
						concrete,
						req_typeset.typeset_index,
					) {
					let set_name = self
						.interner
						.resolve(
							self.items.typesets
								[usize::from(req_typeset.typeset_index)]
							.name
							.inner,
						)
						.unwrap();
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::TypesetBoundViolation.code(),
							)
							.with_message(format!(
								"associated type `{assoc_name_str}` (`{concrete_name}`) is not a member of typeset `{set_name}`"
							))
							.with_label(
								Label::primary(
									ctx.resolve_context.file_id,
									call_span,
								)
								.with_message(format!(
									"`{assoc_name_str}` requires a type from `{set_name}`"
								)),
							)
							.with_label(
								Label::secondary(func_file_id, trait_bound.span)
									.with_message(format!(
										"required by a `where` clause on `{func_name}`"
									)),
							),
					);
				}
			}
		}

		type_args
	}

	pub(super) fn build_method_call_expression(
		&mut self,
		ctx: &mut ExprContext,
		access_ctx: AccessContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let MethodCallExpr {
			arguments,
			method,
			object,
			type_args: ast_type_args,
		} = match &expr.inner {
			ast::Expression::MethodCall(method_call) => method_call.as_ref(),
			_ => unreachable!(),
		};

		let object = self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			object,
		)?;

		let file_id = ctx.resolve_context.file_id;
		let (func_index, mut type_args) = match self.resolve_method_call(
			ctx.resolve_context,
			Spanned {
				inner: object.ty,
				span: object.span,
			},
			*method,
		) {
			Ok(resolved) => resolved,
			// The method didn't resolve, so there are no parameters to check
			// against — but still build the arguments so a mistake *inside*
			// the argument list gets reported rather than hidden behind the
			// unresolved method. `ERROR` as the expected type for the same
			// reason as the non-function arm of `build_call_expression`: it
			// marks the context as already broken, so nothing downstream
			// asks the user to annotate their way out of it.
			Err(()) => {
				for argument in arguments {
					_ = self.build_expression(
						ctx,
						AccessContext {
							expected_type: TypeIndex::ERROR,
							access_kind: AccessKind::Read,
						},
						&argument.inner,
					);
				}
				return Err(());
			}
		};

		self.items.functions[usize::from(func_index)]
			.accesses
			.push(SourceSpan::new(file_id, method.span));
		let id = self.items.functions[usize::from(func_index)].id;
		let signature_index =
			self.items.functions[usize::from(func_index)].signature_index;
		let signature = match self.types.resolve(signature_index) {
			Type::Function { signature } => signature.clone(),
			_ => unreachable!(),
		};
		let non_self_params = &signature.params()[1..];
		if arguments.len() != non_self_params.len() {
			self.diagnostics.push(report_argument_count_mismatch(
				self.formatter(ctx.resolve_context.namespace),
				ArgumentCountMismatchDiagnostic {
					actual_count: arguments.len(),
					params: non_self_params,
					call_span: SourceSpan::new(file_id, object.span),
					is_method: true,
				},
			));
		}

		if type_args.is_empty() {
			if let (Some(first), Some(last)) =
				(ast_type_args.first(), ast_type_args.last())
			{
				let count = ast_type_args.len();
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::TypeArgCountMismatch.code())
						.with_message(format!(
							"method takes 0 generic arguments but {count} generic argument{} {} supplied",
							if count == 1 { "" } else { "s" },
							if count == 1 { "was" } else { "were" },
						))
						.with_label(
							SourceSpan::new(
								file_id,
								TextSpan::new(first.span.start, last.span.end),
							)
							.primary_label()
							.with_message("expected 0 generic arguments"),
						)
						.with_note("remove the unnecessary generics"),
				);
			}
			if let Some(&self_param_ty) = signature.params().first() {
				if !self.coercible_to(object.ty, self_param_ty) {
					self.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type: self_param_ty,
							actual_type: object.ty,
							span: SourceSpan::new(file_id, object.span),
						},
					));
				}
			}
			let args =
				self.build_call_arguments(ctx, arguments, non_self_params, &[]);
			return Ok(Expression {
				kind: ExprKind::MethodCall {
					arguments: std::iter::once(object).chain(args).collect(),
					id,
				},
				ty: signature.result(),
				span: expr.span,
			});
		}

		// Merge explicit method-call turbofish (`.method::<T>()`) into the
		// function's own (non-inherited) type_args slots — mirrors how
		// build_namespace_member_expression merges turbofish for
		// `Type::method::<T>()`.
		let fn_params_len = self.items.functions[usize::from(func_index)]
			.type_params
			.len();
		if !ast_type_args.is_empty() && ast_type_args.len() != fn_params_len {
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeArgCountMismatch.code())
					.with_message(format!(
						"expected {} type argument{}, found {}",
						fn_params_len,
						if fn_params_len == 1 { "" } else { "s" },
						ast_type_args.len()
					))
					.with_label(
						SourceSpan::new(file_id, expr.span)
							.primary_label()
							.with_message("wrong number of type arguments"),
					),
			);
		}
		let own_start = type_args.len() - fn_params_len;
		for (slot, ast_arg) in
			type_args[own_start..].iter_mut().zip(ast_type_args.iter())
		{
			*slot = self.resolve_type(ctx.resolve_context, ctx.scope, ast_arg);
		}

		// Seed type_args from the call's own expected type *before* building
		// arguments, so an argument that's itself a generic call can use it
		// as inference context — mirrors the analogous seeding in
		// build_call_expression's generic branch.
		if access_ctx.expected_type != TypeIndex::INFER {
			// Ignored — see the identical seeding step in
			// `build_generic_call_arguments`.
			let _ = self.types.infer_type_args(
				&mut type_args,
				signature.result(),
				access_ctx.expected_type,
			);
		}

		let mut built_arguments = Vec::with_capacity(arguments.len() + 1);
		built_arguments.push(object);
		for (index, arg) in arguments.iter().enumerate() {
			let param_type = non_self_params.get(index).copied();
			let expected_type = param_type
				.map(|pt| self.substitute_expected_type(pt, &type_args))
				.filter(|&t| !self.contains_infer(t))
				.unwrap_or(TypeIndex::INFER);
			let built = self.build_expression(
				ctx,
				AccessContext {
					expected_type,
					access_kind: AccessKind::Read,
				},
				&arg.inner,
			)?;
			if let Some(param_type) = param_type {
				// Ignored — see the identical per-argument step in
				// `build_generic_call_arguments`.
				let _ = self.types.infer_type_args(
					&mut type_args,
					param_type,
					built.ty,
				);
			}
			built_arguments.push(built);
		}
		let mut built_arguments = built_arguments.into_boxed_slice();
		let inferred_type_args = self.build_generic_call_arguments(
			ctx,
			func_index,
			&mut built_arguments,
			type_args,
			access_ctx.expected_type,
			expr.span,
		);
		let return_ty =
			self.substitute_type(signature.result(), &inferred_type_args);
		Ok(Expression {
			kind: ExprKind::GenericMethodCall {
				id,
				type_args: inferred_type_args,
				arguments: built_arguments,
			},
			ty: return_ty,
			span: expr.span,
		})
	}

	/// Resolves a method call on `receiver`, including one level of pointer auto-deref.
	/// Returns `(func_index, type_args)` on success. `type_args` is empty for non-generic
	/// methods, filled with `INFER` for generic methods whose args must be inferred from
	/// the call, and pre-concrete for generic impl methods (inferred from the receiver type).
	/// Reports a diagnostic and returns `Err` when no method is found or the entry is not
	/// callable as a method.
	fn resolve_method_call(
		&mut self,
		resolve_context: ResolveContext,
		receiver: Spanned<TypeIndex>,
		method: Spanned<SymbolU32>,
	) -> Result<(FunctionIndex, Box<[TypeIndex]>), ()> {
		let file_id = resolve_context.file_id;
		// Pointer types cannot have impl blocks, so look up methods on the inner type directly.
		let lookup_ty = match self.types.resolve(receiver.inner) {
			Type::Pointer { to, .. } => *to,
			_ => receiver.inner,
		};

		if lookup_ty == TypeIndex::ERROR {
			return Err(());
		}

		let lookup = self.resolve_impl_member(
			resolve_context,
			lookup_ty,
			method.inner,
			method.span,
		);
		// `resolve_impl_member`'s `TypeParam` branch is the only path that
		// can produce `MemberLookup::Trait` for a `TypeParam` receiver
		// (inherent methods are structurally impossible there), so this is
		// exactly the abstract-dispatch case: the concrete impl actually
		// invoked is only known at MIR monomorphization, so every impl of
		// the trait — not just the one entry returned here — has to be
		// marked accessed, or dead-code detection would flag all of them
		// as unused even though any could end up being the one called.
		if let MemberLookup::Trait { trait_index, .. } = &lookup
			&& matches!(self.types.resolve(lookup_ty), Type::TypeParam { .. })
		{
			self.record_abstract_dispatch_access(
				*trait_index,
				method.inner,
				SourceSpan::new(file_id, method.span),
			);
		}

		match lookup {
			MemberLookup::Inherent {
				entry: ImplEntry::Method(func_index),
				type_args,
			}
			| MemberLookup::Trait {
				entry: ImplEntry::Method(func_index),
				type_args,
				..
			} => {
				let func = &self.items.functions[usize::from(func_index)];
				let self_param_ty = func.params[0].ty.inner;
				if matches!(
					self.types.resolve(self_param_ty),
					Type::Pointer { .. }
				) != matches!(
					self.types.resolve(receiver.inner),
					Type::Pointer { .. }
				) {
					self.diagnostics.push(report_type_mistmatch(
						self.formatter(resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type: self_param_ty,
							actual_type: receiver.inner,
							span: SourceSpan::new(file_id, receiver.span),
						},
					));
					// TODO: improve error recovery
					return Err(());
				}
				// Non-empty `type_args` means this came from a generic
				// inherent impl block and is already the substitution
				// inferred from the receiver (e.g. `M = heap`), but it's only
				// as long as the *impl block's* own type params — pad it out
				// to the method's total (impl-inherited + its own), leaving
				// the method's own generics (if any) as `INFER` slots for the
				// call site to resolve. Otherwise (no impl-level generics at
				// all) start every slot as `INFER`.
				let type_args = if type_args.is_empty() {
					vec![TypeIndex::INFER; func.total_type_param_count()]
						.into_boxed_slice()
				} else {
					let mut padded =
						vec![TypeIndex::INFER; func.total_type_param_count()];
					padded[..type_args.len()].copy_from_slice(&type_args);
					padded.into_boxed_slice()
				};
				Ok((func_index, type_args))
			}
			MemberLookup::Inherent { .. } | MemberLookup::Trait { .. } => {
				self.diagnostics.push(report_not_a_method(
					SourceSpan::new(file_id, method.span),
					self.formatter(resolve_context.namespace),
					method.inner,
					lookup_ty,
				));
				Err(())
			}
			MemberLookup::NotFound => {
				self.diagnostics.push(report_method_not_found(
					SourceSpan::new(file_id, method.span),
					self.formatter(resolve_context.namespace),
					method.inner,
					receiver.inner,
				));
				Err(())
			}
			MemberLookup::Ambiguous => Err(()),
		}
	}

	pub(super) fn resolve_impl_member(
		&mut self,
		resolve_context: ResolveContext,
		target_type: TypeIndex,
		member_symbol: SymbolU32,
		member_span: TextSpan,
	) -> MemberLookup {
		struct MemberCandidate {
			trait_index: TraitIndex,
			entry: ImplEntry,
			type_args: Box<[TypeIndex]>,
		}
		let mut candidates: Vec<MemberCandidate> = Vec::new();
		let mut candidate: Option<MemberCandidate> = None;

		match self.types.resolve(target_type) {
			Type::TypeParam { owner, param_index } => {
				for trait_index in self
					.items
					.type_param_info(*owner, *param_index as usize)
					.bounds
					.traits
					.iter()
					.map(|bound| bound.trait_index)
				{
					let entry = match self.items.traits
						[usize::from(trait_index)]
					.entries
					.get(&member_symbol)
					.cloned()
					{
						Some(entry) => entry,
						None => continue,
					};
					let type_args =
						self.pad_type_args(entry, Box::new([target_type]));
					match candidate.take() {
						Some(existing) => {
							candidates.push(existing);
							candidates.push(MemberCandidate {
								trait_index,
								entry,
								type_args,
							});
						}
						None => {
							candidate = Some(MemberCandidate {
								trait_index,
								entry,
								type_args,
							});
						}
					};
				}
			}
			_ => {
				let target = match ImplTarget::from_type(
					self.types.resolve(target_type),
				) {
					Ok(target) => target,
					Err(_) => return MemberLookup::NotFound,
				};
				if let Some(result) = self.resolve_inherent_member(
					target,
					target_type,
					member_symbol,
					SourceSpan::new(resolve_context.file_id, member_span),
				) {
					return result;
				}

				// Every trait impl (concrete or generic) whose target
				// unifies with `ty` — `unify_trait_impl_target` degenerates to
				// exact equality for concrete impls, so this covers exactly
				// what the old exact-key `type_trait_impls` lookup did, plus
				// generic impls.
				for (trait_index, impl_index) in self
					.items
					.trait_impl_dispatch
					.get(&target)
					.map(|v| v.as_slice())
					.unwrap_or_default()
					.iter()
					.copied()
				{
					let Some((entry, type_args)) = self.trait_member_via_impl(
						trait_index,
						impl_index,
						target_type,
						member_symbol,
					) else {
						continue;
					};
					match candidate.take() {
						Some(existing) => {
							candidates.push(existing);
							candidates.push(MemberCandidate {
								trait_index,
								entry,
								type_args,
							});
						}
						None => {
							candidate = Some(MemberCandidate {
								trait_index,
								entry,
								type_args,
							})
						}
					}
				}
			}
		};

		// Both loops above route their single-match case through `candidate`
		// and only ever spill into `candidates` once a *second* match shows
		// up (via `candidate.take()`), so `candidates` is never left holding
		// exactly one entry — it's either empty or a genuine 2+-way
		// conflict. `candidate` is therefore the one place a clean match
		// can come from; `candidates.is_empty()` alone decides `NotFound`
		// vs. ambiguous.
		if let Some(candidate) = candidate {
			debug_assert!(candidates.is_empty());
			return MemberLookup::Trait {
				entry: candidate.entry,
				type_args: candidate.type_args,
				trait_index: candidate.trait_index,
			};
		}

		if candidates.is_empty() {
			MemberLookup::NotFound
		} else {
			let formatter = self.formatter(resolve_context.namespace);
			let mut diagnostic = Diagnostic {
				severity: Severity::Error,
				code: Some(
					DiagnosticCode::AmbiguousTraitMember.code().to_string(),
				),
				message: "multiple applicable items in scope".to_string(),
				labels: Vec::with_capacity(candidates.len() + 1),
				notes: Vec::new(),
			};
			diagnostic.labels.push(
				SourceSpan::new(resolve_context.file_id, member_span)
					.primary_label()
					.with_message(format!(
						"multiple `{}` found",
						formatter.interner.resolve(member_symbol).unwrap()
					)),
			);
			let type_name = formatter.display_type(target_type).unwrap();
			for (idx, candidate) in candidates.iter().enumerate() {
				let trait_name = self.items.traits
					[usize::from(candidate.trait_index)]
				.name
				.inner;
				let trait_name =
					formatter.interner.resolve(trait_name).unwrap();
				let message = format!(
					"candidate #{} is defined in an impl of the trait `{trait_name}` for the type `{type_name}`",
					idx + 1
				);
				diagnostic.labels.push(
					candidate
						.entry
						.def_span(&self.items)
						.secondary_label()
						.with_message(message),
				);
			}
			self.diagnostics.push(diagnostic);
			MemberLookup::Ambiguous
		}
	}

	/// Inherent-impl half of `resolve_impl_member`'s dispatch: every block in
	/// `target`'s `(kind, member)` bucket that actually matches
	/// `target_type` (`unify_inherent_impl_target` filters the rest out). `None` means
	/// no inherent match at all — the caller falls through to the trait
	/// scan. More than one match is a real conflict (see the comment on
	/// `resolve_impl_member`'s trait-impl loop) and is reported here as
	/// `Some(Ambiguous)`. Mirrors the `TypeParam` branch's
	/// `candidate`/`candidates` split so the common single-match case never
	/// allocates a `Vec`.
	fn resolve_inherent_member(
		&mut self,
		target: ImplTarget,
		target_type: TypeIndex,
		member_symbol: SymbolU32,
		member_span: SourceSpan,
	) -> Option<MemberLookup> {
		struct InherentCandidate {
			entry: ImplEntry,
			type_args: Box<[TypeIndex]>,
		}
		let mut candidate: Option<InherentCandidate> = None;
		let mut candidates: Vec<InherentCandidate> = Vec::new();

		for block_idx in self
			.items
			.inherent_impl_dispatch
			.get(&(target, member_symbol))
			.map(|v| v.as_slice())
			.unwrap_or_default()
			.iter()
			.copied()
		{
			let Some(entry) = self.items.inherent_impls[usize::from(block_idx)]
				.members
				.get(&member_symbol)
				.copied()
			else {
				continue;
			};
			let Some(type_args) = self.items.unify_inherent_impl_target(
				&self.types,
				usize::from(block_idx),
				target_type,
			) else {
				continue;
			};
			let type_args = self.pad_type_args(entry, type_args);
			match candidate.take() {
				Some(existing) => {
					candidates.push(existing);
					candidates.push(InherentCandidate { entry, type_args });
				}
				None => {
					candidate = Some(InherentCandidate { entry, type_args })
				}
			}
		}

		if !candidates.is_empty() {
			let member_name =
				self.interner.resolve(member_symbol).unwrap().to_string();
			let mut diagnostic = Diagnostic {
				severity: Severity::Error,
				code: Some(
					DiagnosticCode::DuplicateDefinition.code().to_string(),
				),
				message: format!(
					"the name `{member_name}` is defined multiple times"
				),
				labels: Vec::with_capacity(candidates.len() + 1),
				notes: Vec::new(),
			};
			diagnostic.labels.push(
				member_span
					.primary_label()
					.with_message(format!("multiple `{member_name}` found")),
			);
			for (idx, candidate) in candidates.iter().enumerate() {
				diagnostic.labels.push(
					candidate
						.entry
						.def_span(&self.items)
						.secondary_label()
						.with_message(format!(
							"candidate #{} defined here",
							idx + 1
						)),
				);
			}
			self.diagnostics.push(diagnostic);
			return Some(MemberLookup::Ambiguous);
		}

		candidate.map(|candidate| MemberLookup::Inherent {
			entry: candidate.entry,
			type_args: candidate.type_args,
		})
	}

	/// Checks whether `impl_index` (an impl of `trait_index`) or
	/// `trait_index`'s own default body provides `member_symbol` for
	/// `target_type`, unifying the impl's target against it. Returns `None`
	/// if this impl isn't a match. This is the "does this one candidate
	/// apply" check shared by `resolve_impl_member`'s multi-candidate search
	/// and `resolve_trait_member`'s single-known-trait lookup, so the
	/// unification/default-body rules can't drift between the two callers.
	fn trait_member_via_impl(
		&self,
		trait_index: TraitIndex,
		impl_index: TraitImplIndex,
		target_type: TypeIndex,
		member_symbol: SymbolU32,
	) -> Option<(ImplEntry, Box<[TypeIndex]>)> {
		// Membership check first — plain `HashMap` lookups, independent of
		// `target_type` — before paying for `unify_trait_impl_target`'s
		// unification (which allocates for a generic impl). Most traits
		// implemented for a constructor won't provide the member being
		// looked up, so this avoids probing every one of them just to find
		// out it was never a candidate.
		let from_impl = self.items.trait_impls[usize::from(impl_index)]
			.members
			.get(&member_symbol)
			.cloned();
		let from_trait_default = self.items.traits[usize::from(trait_index)]
			.entries
			.get(&member_symbol)
			.cloned()
			.filter(|entry| self.entry_has_body(*entry));
		if from_impl.is_none() && from_trait_default.is_none() {
			return None;
		}

		let impl_type_args = self.items.unify_trait_impl_target(
			&self.types,
			impl_index,
			target_type,
		)?;
		// `type_args` must match whichever owner `entry` actually inherits
		// from: the impl's own params (`impl_type_args`, already in that
		// scheme) when the impl overrides this member itself, or just
		// `[target_type]` — the receiver, matching `Trait(trait_index)`'s
		// single inherited `Self` param — when it falls back to the
		// trait's own default body. These are different owners with
		// independently-indexed param schemes; using `impl_type_args` for a
		// trait default would substitute the impl's `T` where `Self`
		// belongs.
		let (entry, type_args) = match from_impl {
			Some(entry) => (entry, impl_type_args),
			None => (
				from_trait_default?,
				Box::new([target_type]) as Box<[TypeIndex]>,
			),
		};
		Some((entry, self.pad_type_args(entry, type_args)))
	}

	/// Looks up `member_symbol` on `target_type` under exactly
	/// `required_trait` — used by qualified paths (`<Type as Trait>::item`),
	/// which already know which trait they mean and so need neither the
	/// inherent-member fallback nor the multi-trait ambiguity bookkeeping
	/// that `resolve_impl_member` (the unqualified lookup) has to do. The
	/// caller, which knows whether it's in type or expression position (and
	/// therefore which existing diagnostic code applies), reports the
	/// specific error itself.
	pub(super) fn resolve_trait_member(
		&self,
		target_type: TypeIndex,
		required_trait: TraitIndex,
		member_symbol: SymbolU32,
	) -> Result<(ImplEntry, Box<[TypeIndex]>), TraitMemberError> {
		match self.types.resolve(target_type) {
			Type::TypeParam { owner, param_index } => {
				let bound = self
					.items
					.type_param_info(*owner, *param_index as usize)
					.bounds
					.traits
					.iter()
					.any(|bound| bound.trait_index == required_trait);
				if !bound {
					return Err(TraitMemberError::NotImplemented);
				}
				let entry = self.items.traits[usize::from(required_trait)]
					.entries
					.get(&member_symbol)
					.cloned()
					.ok_or(TraitMemberError::NoSuchMember)?;
				Ok((entry, self.pad_type_args(entry, Box::new([target_type]))))
			}
			_ => {
				let target =
					ImplTarget::from_type(self.types.resolve(target_type))
						.map_err(|_| TraitMemberError::NotImplemented)?;
				let &(_, impl_index) = self
					.items
					.trait_impl_dispatch
					.get(&target)
					.and_then(|impls| {
						impls.iter().find(|(t, _)| *t == required_trait)
					})
					.ok_or(TraitMemberError::NotImplemented)?;
				self.trait_member_via_impl(
					required_trait,
					impl_index,
					target_type,
					member_symbol,
				)
				.ok_or(TraitMemberError::NoSuchMember)
			}
		}
	}

	/// Whether `entry` (an item pulled from a `Trait::members` table) has a
	/// real, usable definition on its own — a bodied default method — as
	/// opposed to being a bare declaration that only exists to record the
	/// item's kind. Trait-level `Const`/`AssociatedType` entries are always
	/// placeholders — traits cannot give them default values — so they never
	/// act as a fallback default the way a bodied method can.
	///
	/// Checks the AST's `body: Option<...>` directly (via `sig_state`)
	/// rather than `Function::body` — the latter is only populated once
	/// Phase 3 has actually built that specific function, which is not
	/// guaranteed yet at every call site that may reach here.
	///
	/// No `ensure_signature` call needed: this is only ever reached from
	/// `resolve_impl_member`, which only runs while building expression
	/// bodies (Phase 3) — and `TIR::build` runs Phase 2 to completion, for
	/// every registered `DefId`, before Phase 3 starts for anything. So by
	/// the time this can run, every signature — including this one — has
	/// already been ensured.
	fn entry_has_body(&self, entry: ImplEntry) -> bool {
		match entry {
			ImplEntry::Method(func_index)
			| ImplEntry::AssocFunction(func_index) => {
				let def_id = self.items.functions[usize::from(func_index)].id;
				match self.sig_state.get(&def_id) {
					Some(e) => matches!(
						&self.ast_nodes[e.node_idx].node,
						AstNodeRef::TraitFunction {
							item: ast::TraitItem::Function {
								body: Some(_),
								..
							},
							..
						}
					),
					None => false,
				}
			}
			// Unlike a method's body (resolved lazily in the separate,
			// later `ensure_body` phase — so `tir.items.functions[..].body` can
			// still be `None` for a default method whose body just hasn't
			// been demanded yet), a const's `value` is resolved eagerly,
			// atomically, within `ensure_signature` itself, strictly before
			// its `ImplEntry::AssocConstant` entry is inserted into
			// `trait.entries` — so by the time this entry is even
			// reachable to look up, `value` is guaranteed already set.
			ImplEntry::AssocConstant(const_index) => self.items.constants
				[usize::from(const_index)]
			.value
			.is_some(),
			ImplEntry::AssocType(_) => false,
		}
	}

	/// Whenever a member access resolves to a trait's own *abstract*
	/// declaration (no body/value anywhere — the real thing lives in
	/// whichever impl ends up being the concrete receiver, decided
	/// dynamically at MIR monomorphization time via a bounded generic
	/// parameter or `Self` inside a trait default body), record a
	/// conservative "used" signal on every impl of that trait providing this
	/// member. Without this, `report_unused_items` would flag every such
	/// impl's own method/associated const as dead code: only the abstract
	/// declaration's own `accesses` — never any specific impl's — gets a
	/// direct hit from this call path, since dispatch to a concrete impl
	/// never goes through the impl's own `DefId` at the TIR level at all.
	/// `AssociatedType` has no `accesses` tracking (it's a type alias, not a
	/// lint-tracked item) so it's a no-op here. DCE (a later, MIR-level, and
	/// far more precise pass over actual call-graph edges) is what
	/// determines which impls are genuinely reachable; this is only about
	/// not falsely warning here.
	pub(super) fn record_abstract_dispatch_access(
		&mut self,
		trait_index: TraitIndex,
		member_symbol: SymbolU32,
		span: SourceSpan,
	) {
		// Disjoint-field borrow (rather than collecting matching impl indices
		// into a `Vec` first) avoids a heap allocation on every call — this
		// runs once per abstract-dispatch call site, so it's on a hot path.
		let ItemRegistry {
			trait_impls,
			functions,
			constants,
			..
		} = &mut self.items;
		for trait_impl in trait_impls
			.iter()
			.filter(|trait_impl| trait_impl.trait_index == trait_index)
		{
			match trait_impl.members.get(&member_symbol).copied() {
				Some(ImplEntry::Method(fi) | ImplEntry::AssocFunction(fi)) => {
					functions[usize::from(fi)].accesses.push(span);
				}
				Some(ImplEntry::AssocConstant(ci)) => {
					constants[usize::from(ci)].accesses.push(span);
				}
				Some(ImplEntry::AssocType(_)) | None => {}
			}
		}
	}

	fn pad_type_args(
		&self,
		entry: ImplEntry,
		parent_args: Box<[TypeIndex]>,
	) -> Box<[TypeIndex]> {
		match entry {
			ImplEntry::Method(func_index)
			| ImplEntry::AssocFunction(func_index) => {
				let total = self.items.functions[usize::from(func_index)]
					.total_type_param_count();
				if parent_args.len() == total {
					return parent_args;
				}
				let mut type_args = Vec::with_capacity(total);
				type_args.extend_from_slice(&parent_args);
				type_args.resize(total, TypeIndex::INFER);
				type_args.into_boxed_slice()
			}
			_ => parent_args,
		}
	}
}

fn report_method_not_found(
	span: SourceSpan,
	formatter: TypeFormatter<'_>,
	method: SymbolU32,
	ty: TypeIndex,
) -> Diagnostic<FileId> {
	let method_name = formatter.interner.resolve(method).unwrap();
	let type_name = formatter.display_type(ty).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::MethodNotFound.code())
		.with_message(format!(
			"no method `{method_name}` found for type `{type_name}`"
		))
		.with_label(span.primary_label())
}

fn report_not_a_method(
	span: SourceSpan,
	formatter: TypeFormatter<'_>,
	method: SymbolU32,
	ty: TypeIndex,
) -> Diagnostic<FileId> {
	let member_name = formatter.interner.resolve(method).unwrap();
	let type_name = formatter.display_type(ty).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotAMethod.code())
		.with_message(format!(
			"`{member_name}` is not a method on type `{type_name}`"
		))
		.with_label(span.primary_label())
		.with_note("use `::` to access associated items")
}

fn report_argument_count_mismatch(
	fmt: TypeFormatter,
	details: ArgumentCountMismatchDiagnostic<'_>,
) -> Diagnostic<FileId> {
	let mut diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::ArgumentCountMismatch.code())
		.with_message(format!(
			"this {} takes {} {} but {} {} supplied",
			if details.is_method {
				"method"
			} else {
				"function"
			},
			details.params.len(),
			if details.params.len() == 1 {
				"argument"
			} else {
				"arguments"
			},
			details.actual_count,
			if details.actual_count == 1 {
				"argument was"
			} else {
				"arguments were"
			},
		))
		.with_label(details.call_span.primary_label());

	if details.actual_count < details.params.len() {
		let missing_count = details.params.len() - details.actual_count;
		let missing_types: Vec<String> = details.params[details.actual_count..]
			.iter()
			.map(|ty| fmt.display_type(*ty).unwrap())
			.collect();

		if missing_count == 1 {
			diagnostic = diagnostic.with_note(format!(
				"argument #{} of type `{}` is missing",
				details.actual_count + 1,
				missing_types[0]
			));
		} else {
			let types_str = missing_types.join("`, `");
			diagnostic = diagnostic.with_note(format!(
				"{} arguments of type `{}` are missing",
				missing_count, types_str
			));
		}
	} else {
		let extra_count = details.actual_count - details.params.len();
		if extra_count == 1 {
			diagnostic = diagnostic.with_note(format!(
				"unexpected argument #{}",
				details.actual_count
			));
		} else {
			diagnostic = diagnostic
				.with_note(format!("{} unexpected arguments", extra_count));
		}
	}

	diagnostic
}

struct ArgumentCountMismatchDiagnostic<'a> {
	actual_count: usize,
	params: &'a [TypeIndex],
	call_span: SourceSpan,
	is_method: bool,
}
