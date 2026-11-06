//! Aggregate expressions: struct initialisation, tuples, array literals and
//! repeats, and the indexing and slice-range expressions that read out of them.

use crate::diagnostics::{DiagnosticCode, TextSpan};

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Resolves `name` as a field of `struct_index` instantiated with `args`,
	/// recording the access and enforcing the field's visibility.
	///
	/// `None` means the struct has no such field, deliberately without a
	/// diagnostic: the callers disagree about what a miss means. `a.b` falls
	/// through to method lookup, while a struct literal and a struct pattern
	/// each report their own `UnknownStructField` and recover differently.
	///
	/// A *private* field is reported but still returned. Its type is known,
	/// so the caller keeps building and every later check still runs against
	/// the real type instead of collapsing into the privacy error.
	pub(super) fn resolve_struct_field(
		&mut self,
		resolve_context: ResolveContext,
		struct_index: StructIndex,
		args: &[TypeIndex],
		name: Spanned<SymbolU32>,
		kind: FieldAccessKind,
	) -> Option<ResolvedField> {
		let declaration = &mut self.items.structs[usize::from(struct_index)];
		let declaring_namespace = declaration.namespace;
		// Tuple-struct fields have no names to look up — this is not an
		// error here, callers disagree about what a miss means (see above).
		let StructKind::Record { fields, lookup } = &mut declaration.fields
		else {
			return None;
		};
		let index = lookup.get(&name.inner).copied()?;
		let raw_ty = fields[usize::from(index)].ty.inner;
		fields[usize::from(index)].accesses.push(FieldAccess {
			kind,
			file_id: resolve_context.file_id,
			span: name.span,
		});

		let visibility = self.field_visibility(struct_index, index);
		if !self.is_accessible_from(
			resolve_context.namespace,
			declaring_namespace,
			visibility,
		) {
			self.report_private_field(
				struct_index,
				index,
				SourceSpan::new(resolve_context.file_id, name.span),
			);
		}

		// The overwhelmingly common case is a non-generic struct, which has
		// nothing to substitute — checked here rather than inside
		// `substitute_type` so it costs a branch instead of a call.
		let ty = if args.is_empty() {
			raw_ty
		} else {
			self.substitute_type(raw_ty, args)
		};

		Some(ResolvedField { index, ty })
	}

	pub(super) fn build_struct_init_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		init_span: TextSpan,
		path: &[ast::PathSegment],
		fields: &[ast::Separated<ast::Spanned<ast::StructInitField>>],
	) -> Result<Expression, ()> {
		let struct_seg = path.last().expect("path has at least one segment");
		let file_id = func_ctx.resolve_context.file_id;

		// Shared with type-position resolution: handles namespace walking,
		// turbofish (with alias support), and plain identifiers uniformly.
		// `AllowInfer` since struct-init always has field values alongside it
		// to infer any omitted type arguments from.
		let struct_ty = self.resolve_path_type(
			func_ctx.resolve_context,
			func_ctx.scope,
			path,
			init_span,
			TypeArgArity::AllowInfer,
		);
		if struct_ty == TypeIndex::ERROR {
			return Err(());
		}

		let struct_index = match self.types.resolve(struct_ty) {
			Type::Struct { struct_index, .. } => *struct_index,
			_ => {
				let name = self
					.interner
					.resolve(struct_seg.ident.inner)
					.unwrap()
					.to_string();
				self.diagnostics.push(report_not_a_struct_type(
					file_id,
					name,
					struct_seg.ident.span,
				));
				return Err(());
			}
		};

		// Priority: explicit turbofish (already resolved, alias-substituted,
		// and INFER-padded into struct_ty's args by resolve_path_type) >
		// args concretely embedded in path type (e.g. `Self` inside
		// `impl<M,T> Vec<M,T>` — must be more than just INFER placeholders,
		// or a bare generic reference padded by resolve_path_type would be
		// mistaken for a real instantiation) > infer from expected type >
		// empty (inferred per-field below).
		let type_params_len = self.items.structs[usize::from(struct_index)]
			.type_params
			.len();
		let resolved_args: Box<[TypeIndex]> =
			if !struct_seg.type_args.is_empty() {
				match self.types.resolve(struct_ty) {
					Type::Struct { args, .. } => args.clone(),
					_ => Box::new([]),
				}
			} else if type_params_len == 0 {
				Box::new([])
			} else {
				match self.types.resolve(struct_ty) {
					Type::Struct { args, .. }
						if args.len() == type_params_len
							&& args.iter().any(|a| *a != TypeIndex::INFER) =>
					{
						args.clone()
					}
					_ => match self.types.resolve(access_ctx.expected_type) {
						Type::Struct {
							struct_index: esi,
							args,
						} if *esi == struct_index
							&& args.len() == type_params_len =>
						{
							args.clone()
						}
						_ => Box::new([]),
					},
				}
			};

		let struct_name = self
			.interner
			.resolve(self.items.structs[usize::from(struct_index)].name.inner)
			.unwrap()
			.to_string();
		let field_count =
			match &self.items.structs[usize::from(struct_index)].fields {
				StructKind::Record { fields, .. } => fields.len(),
				StructKind::Tuple { .. } => {
					self.diagnostics.push(report_tuple_struct_brace_literal(
						file_id,
						&struct_name,
						init_span,
					));
					return Err(());
				}
			};
		// Tracks the field name span of the first mention of each field (regardless of
		// whether the value built successfully). Used for duplicate detection and to
		// distinguish genuinely-missing fields from errored ones.
		let mut first_mention: Vec<Option<TextSpan>> =
			(0..field_count).map(|_| None).collect();
		// Built in source-written order (not declaration order) so that
		// evaluation order — and any side effects field initializers
		// contain — matches what the user wrote; see `ExprKind::StructInit`.
		let mut ordered_fields: Vec<(FieldIndex, Expression)> =
			Vec::with_capacity(field_count);

		for field in fields.iter() {
			let field = &field.inner.inner;

			let Some(resolved) = self.resolve_struct_field(
				func_ctx.resolve_context,
				struct_index,
				&resolved_args,
				field.name,
				FieldAccessKind::Init,
			) else {
				let field_name =
					self.interner.resolve(field.name.inner).unwrap();
				self.diagnostics.push(report_unknown_struct_field(
					UnknownStructFieldDiagnostic {
						file_id: func_ctx.resolve_context.file_id,
						struct_name: &struct_name,
						field_name,
						field_span: field.name.span,
					},
				));
				continue;
			};
			let field_index = usize::from(resolved.index);

			if let Some(first_span) = first_mention[field_index] {
				let field_name =
					self.interner.resolve(field.name.inner).unwrap();
				self.diagnostics.push(report_duplicate_struct_field_init(
					field_name,
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						first_span,
					),
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						field.name.span,
					),
				));
				continue;
			}
			// Mark this field as mentioned (by its name span) before building the value,
			// so that build errors don't cause it to appear in the "missing fields" list.
			first_mention[field_index] = Some(field.name.span);

			let expected_ty = resolved.ty;
			let field_value = match &field.value {
				Some(expr) => expr.as_ref(),
				None => {
					// Shorthand: treat `{ a }` as `{ a: a }` by synthesising a single-segment path
					&ast::Spanned {
						inner: ast::Expression::Path(Box::new([
							ast::PathSegment {
								ident: field.name,
								type_args: Box::new([]),
							},
						])),
						span: field.name.span,
					}
				}
			};
			let mut field_expr = match self.build_expression(
				func_ctx,
				AccessContext {
					expected_type: expected_ty,
					access_kind: AccessKind::Read,
				},
				field_value,
			) {
				Ok(e) => e,
				Err(_) => continue,
			};

			if field_expr.ty.is_comptime_number() {
				match self.coerce_untyped_expr(
					func_ctx,
					&mut field_expr,
					expected_ty,
				) {
					Ok(_) => {}
					Err(_) => continue,
				}
			} else if !self.coercible_to(field_expr.ty, expected_ty) {
				self.diagnostics.push(report_type_mistmatch(
					self.formatter(func_ctx.resolve_context.namespace),
					TypeMistmatchDiagnostic {
						expected_type: expected_ty,
						actual_type: field_expr.ty,
						span: SourceSpan::new(
							func_ctx.resolve_context.file_id,
							field_expr.span,
						),
					},
				));
				continue;
			}

			ordered_fields.push((resolved.index, field_expr));
		}

		let missing: Box<[&str]> = first_mention
			.iter()
			.enumerate()
			.filter(|(_, m)| m.is_none())
			.map(|(i, _)| {
				self.interner
					.resolve(
						match &self.items.structs[usize::from(struct_index)]
							.fields
						{
							StructKind::Record { fields, .. } => {
								fields[i].name.inner
							}
							StructKind::Tuple { .. } => {
								unreachable!("tuple structs rejected above")
							}
						},
					)
					.unwrap()
			})
			.collect();
		if !missing.is_empty() {
			self.diagnostics.push(report_missing_struct_fields(
				MissingStructFieldsDiagnostic {
					file_id: func_ctx.resolve_context.file_id,
					struct_name: &struct_name,
					missing_fields: missing,
					init_span,
				},
			));
		}

		let ty = self.types.intern(Type::Struct {
			struct_index,
			args: resolved_args,
		});

		// `ordered_fields` may be short of `field_count` here — a missing or
		// failed-to-build field was already diagnosed above; there's nothing
		// unsafe about handing back whatever fields did build.
		Ok(Expression {
			kind: ExprKind::RecordStructInit {
				struct_index,
				fields: ordered_fields.into_boxed_slice(),
			},
			ty,
			span: init_span,
		})
	}

	/// Builds `Point(1, 2)` — positional tuple-struct construction. The
	/// positional sibling of [`Self::build_struct_init_expression`]: same
	/// expected-type seeding and per-field coercion/inference, just walking
	/// fields by position instead of by name. Privacy is *not* checked
	/// here — a struct with any private field has its Value-namespace
	/// constructor binding itself marked private at registration time
	/// (`signature.rs`), so an inaccessible call was already rejected by
	/// `resolve_symbol_and_type_args` before this function is ever reached.
	///
	/// `type_args` arrives already `INFER`-padded to `struct_index`'s own
	/// `type_params.len()` — the caller's job (`calls.rs`), not this
	/// function's, since only the caller knows which symbol kind it
	/// resolved and therefore what the correct arity is.
	pub(super) fn build_tuple_struct_call_expression(
		&mut self,
		ctx: &mut ExprContext,
		struct_index: StructIndex,
		mut type_args: Box<[TypeIndex]>,
		arguments: &[ast::Separated<ast::Spanned<ast::Expression>>],
		expected_result: TypeIndex,
		call_span: TextSpan,
	) -> Result<Expression, ()> {
		let resolve_context = ctx.resolve_context;
		let StructKind::Tuple { fields } =
			&self.items.structs[usize::from(struct_index)].fields
		else {
			unreachable!("caller already checked StructKind::Tuple")
		};
		let field_count = fields.len();

		let struct_name = self
			.interner
			.resolve(self.items.structs[usize::from(struct_index)].name.inner)
			.unwrap()
			.to_string();
		if arguments.len() != field_count {
			self.diagnostics.push(report_tuple_struct_arity_mismatch(
				&struct_name,
				field_count,
				arguments.len(),
				SourceSpan::new(resolve_context.file_id, call_span),
			));
		}

		// Cheap expected-type seed, identical in spirit to
		// `build_struct_init_expression`'s: only bother when every slot is
		// still open (a turbofish-free reference) and there's an expected
		// type shaped like this exact struct to copy args from — no real
		// unification, just reusing an already-concrete answer if one's
		// sitting right there.
		if type_args.is_empty() {
			let type_params_len = self.items.structs[usize::from(struct_index)]
				.type_params
				.len();
			if type_params_len > 0
				&& let Type::Struct {
					struct_index: esi,
					args,
				} = self.types.resolve(expected_result)
				&& *esi == struct_index
				&& args.len() == type_params_len
			{
				type_args = args.clone();
			} else {
				type_args =
					vec![TypeIndex::INFER; type_params_len].into_boxed_slice();
			}
		}

		self.items.structs[usize::from(struct_index)]
			.accesses
			.push(SourceSpan::new(resolve_context.file_id, call_span));

		// Position *is* the field index for a tuple struct — no per-entry
		// `FieldIndex` to carry, unlike `RecordStructInit`. May end up
		// shorter than `field_count` if a field failed to build or an
		// arity mismatch was diagnosed above; safe the same way
		// `RecordStructInit`'s own `ordered_fields` is — a diagnosed TIR
		// error halts compilation before MIR ever lowers this expression,
		// so a short/misaligned array is never actually observed.
		let mut built_arguments: Vec<Expression> =
			Vec::with_capacity(field_count.min(arguments.len()));
		for (position, argument) in arguments.iter().enumerate() {
			let StructKind::Tuple { fields } =
				&self.items.structs[usize::from(struct_index)].fields
			else {
				unreachable!("checked above")
			};
			// Extra arguments past arity: still build (and discard) so
			// mistakes inside them are still reported, matching
			// `build_call_expression`'s own broken-callee convention —
			// but with nothing to check them against.
			let Some(raw_field_ty) = fields.get(position).map(|f| f.ty.inner)
			else {
				let _ = self.build_expression(
					ctx,
					AccessContext {
						expected_type: TypeIndex::ERROR,
						access_kind: AccessKind::Read,
					},
					&argument.inner,
				);
				continue;
			};
			let expected_ty = if type_args.is_empty() {
				raw_field_ty
			} else {
				self.substitute_type(raw_field_ty, &type_args)
			};

			let mut field_expr = match self.build_expression(
				ctx,
				AccessContext {
					expected_type: expected_ty,
					access_kind: AccessKind::Read,
				},
				&argument.inner,
			) {
				Ok(e) => e,
				Err(_) => continue,
			};

			// Ignored — same convention as every other call site: a genuine
			// mismatch still surfaces below via the ordinary coercion check
			// against the (by-then possibly still-generic) expected type.
			let _ = self.types.infer_type_args(
				&mut type_args,
				raw_field_ty,
				field_expr.ty,
			);

			if field_expr.ty.is_comptime_number() {
				match self.coerce_untyped_expr(
					ctx,
					&mut field_expr,
					expected_ty,
				) {
					Ok(_) => {}
					Err(_) => continue,
				}
			} else if !self.coercible_to(field_expr.ty, expected_ty) {
				self.diagnostics.push(report_type_mistmatch(
					self.formatter(resolve_context.namespace),
					TypeMistmatchDiagnostic {
						expected_type: expected_ty,
						actual_type: field_expr.ty,
						span: SourceSpan::new(
							resolve_context.file_id,
							field_expr.span,
						),
					},
				));
				continue;
			}

			let StructKind::Tuple { fields } =
				&mut self.items.structs[usize::from(struct_index)].fields
			else {
				unreachable!("checked above")
			};
			fields[position].accesses.push(FieldAccess {
				kind: FieldAccessKind::Init,
				file_id: resolve_context.file_id,
				span: field_expr.span,
			});

			built_arguments.push(field_expr);
		}

		for (i, slot) in type_args.iter_mut().enumerate() {
			if *slot != TypeIndex::INFER {
				continue;
			}
			let param_name = self.interner.resolve(
				self.items.structs[usize::from(struct_index)].type_params[i]
					.name
					.inner,
			);
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeAnnotationRequired.code())
					.with_message(format!(
						"cannot infer type for type parameter `{}`",
						param_name.unwrap()
					))
					.with_label(
						Label::primary(resolve_context.file_id, call_span)
							.with_message("type annotation required"),
					),
			);
			*slot = TypeIndex::ERROR;
		}

		let ty = self.types.intern(Type::Struct {
			struct_index,
			args: type_args,
		});
		Ok(Expression {
			kind: ExprKind::TupleStructInit {
				struct_index,
				arguments: built_arguments.into_boxed_slice(),
			},
			ty,
			span: call_span,
		})
	}

	pub(super) fn build_tuple_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		span: TextSpan,
		ast_elements: &[ast::Spanned<ast::Expression>],
		access_ctx: AccessContext,
	) -> Result<Expression, ()> {
		if ast_elements.is_empty() {
			return Ok(Expression {
				kind: ExprKind::TupleInit {
					elements: Box::new([]),
				},
				ty: TypeIndex::UNIT,
				span,
			});
		}

		// If the expected type is a tuple, use its element types as hints.
		let expected_elems: Option<Box<[TypeIndex]>> =
			match self.types.resolve(access_ctx.expected_type) {
				Type::Tuple { elements }
					if elements.len() == ast_elements.len() =>
				{
					Some(elements.clone())
				}
				_ => None,
			};

		let mut built = Vec::with_capacity(ast_elements.len());
		let mut had_error = false;
		for (i, elem_expr) in ast_elements.iter().enumerate() {
			let expected = expected_elems
				.as_ref()
				.map(|e| e[i])
				.unwrap_or(TypeIndex::INFER);
			match self.build_expression(
				func_ctx,
				AccessContext {
					expected_type: expected,
					access_kind: AccessKind::Read,
				},
				elem_expr,
			) {
				Ok(mut e) => {
					if e.ty.is_comptime_number() && expected != TypeIndex::INFER
					{
						let _ = self
							.coerce_untyped_expr(func_ctx, &mut e, expected);
					}
					built.push(e);
				}
				Err(()) => {
					had_error = true;
				}
			}
		}

		let elem_types: Box<[TypeIndex]> = built.iter().map(|e| e.ty).collect();
		let ty = self.types.intern(Type::Tuple {
			elements: elem_types,
		});

		if had_error {
			return Ok(Expression {
				kind: ExprKind::TupleInit {
					elements: Box::new([]),
				},
				ty,
				span,
			});
		}

		Ok(Expression {
			kind: ExprKind::TupleInit {
				elements: built.into_boxed_slice(),
			},
			ty,
			span,
		})
	}

	pub(super) fn build_array_literal_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		span: TextSpan,
		elements: &[ast::Spanned<ast::Expression>],
	) -> Result<Expression, ()> {
		let source_span =
			SourceSpan::new(func_ctx.resolve_context.file_id, span);

		let (expected_of, expected_memory, expected_size, expected_ownership) =
			match self.types.resolve(access_ctx.expected_type) {
				&Type::Array {
					of,
					memory,
					size,
					ownership,
				} => (of, Some(memory), Some(size), ownership),
				_ => (TypeIndex::INFER, None, None, ast::Ownership::Shared),
			};

		if let Some(expected_size) = expected_size {
			if elements.len() as u32 != expected_size {
				self.diagnostics.push(report_array_size_mismatch(
					source_span,
					expected_size,
					elements.len(),
				));
				return Err(());
			}
		}

		let mut built = Vec::with_capacity(elements.len());
		for element in elements {
			let mut elem = self.build_expression(
				func_ctx,
				AccessContext {
					expected_type: expected_of,
					access_kind: AccessKind::Read,
				},
				element,
			)?;
			if elem.ty.is_comptime_number() {
				if expected_of != TypeIndex::INFER {
					self.coerce_untyped_expr(func_ctx, &mut elem, expected_of)?;
				} else {
					self.diagnostics.push(report_type_annotation_required(
						SourceSpan::new(
							func_ctx.resolve_context.file_id,
							elem.span,
						),
					));
					return Err(());
				}
			}
			if !elem.ty.is_numeric() {
				self.diagnostics.push(
					Diagnostic::error()
						.with_message(
							"array element type must be a numeric type",
						)
						.with_label(Label::primary(
							func_ctx.resolve_context.file_id,
							elem.span,
						)),
				);
				return Err(());
			}
			if !matches!(
				elem.kind,
				ExprKind::Int { .. } | ExprKind::Float { .. }
			) {
				self.diagnostics.push(report_array_element_not_const(
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						elem.span,
					),
				));
				return Err(());
			}
			built.push(elem);
		}

		let elem_type = if let Some(first) = built.first() {
			let ty = first.ty;
			for elem in &built[1..] {
				if elem.ty != ty {
					self.diagnostics.push(report_type_mistmatch(
						self.formatter(func_ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type: ty,
							actual_type: elem.ty,
							span: SourceSpan::new(
								func_ctx.resolve_context.file_id,
								elem.span,
							),
						},
					));
					return Err(());
				}
			}
			ty
		} else if expected_of != TypeIndex::INFER {
			expected_of
		} else {
			self.diagnostics
				.push(report_type_annotation_required(source_span));
			return Err(());
		};

		let memory = match expected_memory {
			Some(m) => m,
			None => self.resolve_ambient_memory(source_span)?,
		};
		let array_ty = self.types.intern(Type::Array {
			of: elem_type,
			size: elements.len() as u32,
			memory,
			ownership: expected_ownership,
		});

		Ok(Expression {
			kind: ExprKind::ArrayLiteral {
				elements: built.into_boxed_slice(),
				memory,
			},
			ty: array_ty,
			span,
		})
	}

	pub(super) fn build_array_repeat_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		span: TextSpan,
		value_expr: &ast::Spanned<ast::Expression>,
		count_expr: &ast::Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let source_span =
			SourceSpan::new(func_ctx.resolve_context.file_id, span);

		let (expected_of, expected_memory, expected_ownership) =
			match self.types.resolve(access_ctx.expected_type) {
				&Type::Array {
					of,
					memory,
					ownership,
					..
				} => (of, Some(memory), ownership),
				_ => (TypeIndex::INFER, None, ast::Ownership::Shared),
			};

		let count_built = self.build_expression(
			func_ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			count_expr,
		)?;
		let count = match count_built.kind {
			// `value` is always non-negative (see `ExprKind::Int`'s
			// doc comment) — no guard needed.
			ExprKind::Int { value } => value as u32,
			_ => {
				self.diagnostics.push(report_array_repeat_count_not_const(
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						count_expr.span,
					),
				));
				return Err(());
			}
		};

		if let &Type::Array { size, .. } =
			self.types.resolve(access_ctx.expected_type)
		{
			if count != size {
				self.diagnostics.push(report_array_size_mismatch(
					source_span,
					size,
					count as usize,
				));
				return Err(());
			}
		}

		let mut value = self.build_expression(
			func_ctx,
			AccessContext {
				expected_type: expected_of,
				access_kind: AccessKind::Read,
			},
			value_expr,
		)?;
		if value.ty.is_comptime_number() {
			if expected_of != TypeIndex::INFER {
				self.coerce_untyped_expr(func_ctx, &mut value, expected_of)?;
			} else {
				self.diagnostics.push(report_type_annotation_required(
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						value.span,
					),
				));
				return Err(());
			}
		}
		if !value.ty.is_numeric() {
			self.diagnostics.push(
				Diagnostic::error()
					.with_message("array element type must be a numeric type")
					.with_label(Label::primary(
						func_ctx.resolve_context.file_id,
						value.span,
					)),
			);
			return Err(());
		}
		if !matches!(value.kind, ExprKind::Int { .. } | ExprKind::Float { .. })
		{
			self.diagnostics.push(report_array_element_not_const(
				SourceSpan::new(func_ctx.resolve_context.file_id, value.span),
			));
			return Err(());
		}

		let memory = match expected_memory {
			Some(m) => m,
			None => self.resolve_ambient_memory(source_span)?,
		};
		let array_ty = self.types.intern(Type::Array {
			of: value.ty,
			size: count,
			memory,
			ownership: expected_ownership,
		});

		Ok(Expression {
			kind: ExprKind::ArrayRepeat {
				value: Box::new(value),
				count,
				memory,
			},
			ty: array_ty,
			span,
		})
	}

	pub(super) fn build_index_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		span: TextSpan,
		object_expr: &ast::Spanned<ast::Expression>,
		index_expr: &ast::Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		// Always build the indexed object with Read — write-through is governed
		// by the array/slice type's mutable flag, not the binding.
		let object = self.build_expression(
			func_ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			object_expr,
		)?;

		let indexable = match self.types.resolve(object.ty) {
			&Type::Array {
				of,
				memory,
				ownership,
				..
			}
			| &Type::Slice {
				of,
				memory,
				ownership,
			} => Some((of, memory, ownership)),
			Type::Error => return Err(()),
			_ => None,
		};
		let Some((elem_type, memory, ownership)) = indexable else {
			self.diagnostics.push(report_index_on_non_indexable(
				SourceSpan::new(func_ctx.resolve_context.file_id, object.span),
				self.formatter(func_ctx.resolve_context.namespace)
					.display_type(object.ty)
					.unwrap(),
			));
			return Err(());
		};
		let mutable = ownership == ast::Ownership::Exclusive;

		if matches!(
			access_ctx.access_kind,
			AccessKind::Write | AccessKind::ReadWrite
		) && !mutable
		{
			self.diagnostics.push(
				report_cannot_store_through_immutable_pointer(SourceSpan::new(
					func_ctx.resolve_context.file_id,
					span,
				)),
			);
		}

		let index_type = self.pointer_type_for_memory(memory);

		let mut index = self.build_expression(
			func_ctx,
			AccessContext {
				expected_type: index_type,
				access_kind: AccessKind::Read,
			},
			index_expr,
		)?;
		if index.ty.is_comptime_number() {
			self.coerce_untyped_expr(func_ctx, &mut index, index_type)?;
		} else if index.ty != index_type {
			self.diagnostics.push(report_type_mistmatch(
				self.formatter(func_ctx.resolve_context.namespace),
				TypeMistmatchDiagnostic {
					expected_type: index_type,
					actual_type: index.ty,
					span: SourceSpan::new(
						func_ctx.resolve_context.file_id,
						index.span,
					),
				},
			));
		}

		Ok(Expression {
			kind: ExprKind::Load {
				place: Box::new(Place {
					kind: PlaceKind::Index {
						object: Box::new(object),
						index: Box::new(index),
					},
					ty: elem_type,
					memory,
					mutable,
					span,
				}),
			},
			ty: elem_type,
			span,
		})
	}

	pub(super) fn build_slice_range_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		span: TextSpan,
		object_expr: &ast::Spanned<ast::Expression>,
		start_expr: &Option<Box<ast::Spanned<ast::Expression>>>,
		end_expr: &Option<Box<ast::Spanned<ast::Expression>>>,
	) -> Result<Expression, ()> {
		let object = self.build_expression(
			func_ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			object_expr,
		)?;

		let indexable = match self.types.resolve(object.ty) {
			&Type::Array {
				of,
				memory,
				ownership,
				..
			}
			| &Type::Slice {
				of,
				memory,
				ownership,
			} => Some((of, memory, ownership)),
			Type::Error => return Err(()),
			_ => None,
		};
		let Some((elem_type, memory, ownership)) = indexable else {
			self.diagnostics.push(report_index_on_non_indexable(
				SourceSpan::new(func_ctx.resolve_context.file_id, object.span),
				self.formatter(func_ctx.resolve_context.namespace)
					.display_type(object.ty)
					.unwrap(),
			));
			return Err(());
		};

		let index_type = self.pointer_type_for_memory(memory);

		let mut build_bound = |builder: &mut Self,
		                       ast_expr: &ast::Spanned<ast::Expression>|
		 -> Result<Expression, ()> {
			let mut bound = builder.build_expression(
				func_ctx,
				AccessContext {
					expected_type: index_type,
					access_kind: AccessKind::Read,
				},
				ast_expr,
			)?;
			if bound.ty.is_comptime_number() {
				builder
					.coerce_untyped_expr(func_ctx, &mut bound, index_type)?;
			} else if bound.ty != index_type {
				builder.diagnostics.push(report_type_mistmatch(
					builder.formatter(func_ctx.resolve_context.namespace),
					TypeMistmatchDiagnostic {
						expected_type: index_type,
						actual_type: bound.ty,
						span: SourceSpan::new(
							func_ctx.resolve_context.file_id,
							ast_expr.span,
						),
					},
				));
				return Err(());
			}
			Ok(bound)
		};

		let start = start_expr
			.as_ref()
			.map(|e| build_bound(self, e).map(Box::new))
			.transpose()?;
		let end = end_expr
			.as_ref()
			.map(|e| build_bound(self, e).map(Box::new))
			.transpose()?;

		let result_ty = self.types.intern(Type::Slice {
			of: elem_type,
			memory,
			ownership,
		});
		Ok(Expression {
			kind: ExprKind::SliceRange {
				object: Box::new(object),
				start,
				end,
			},
			ty: result_ty,
			span,
		})
	}
}

fn report_tuple_struct_arity_mismatch(
	struct_name: &str,
	field_count: usize,
	found: usize,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeMistmatch.code())
		.with_message("tuple struct call does not match its fields")
		.with_label(span.primary_label().with_message(format!(
			"expected {} argument{}, found {} for `{}`",
			field_count,
			if field_count == 1 { "" } else { "s" },
			found,
			struct_name,
		)))
}

pub(super) fn report_not_a_struct_type(
	file_id: FileId,
	name: String,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeMistmatch.code())
		.with_message(format!("expected struct, found `{}`", name))
		.with_label(Label::primary(file_id, span))
}

pub(super) fn report_tuple_struct_brace_literal(
	file_id: FileId,
	struct_name: &str,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::TupleStructBraceLiteral.code())
		.with_message(format!(
			"tuple struct `{struct_name}` must be constructed with `{struct_name}(...)`"
		))
		.with_label(Label::primary(file_id, span))
}

pub(super) fn report_unknown_struct_field(
	details: UnknownStructFieldDiagnostic<'_>,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnknownStructField.code())
		.with_message(format!(
			"no such field `{}` in struct `{}`",
			details.field_name, details.struct_name
		))
		.with_label(Label::primary(details.file_id, details.field_span))
}

pub(super) fn report_duplicate_struct_field_init(
	field_name: &str,
	first_span: SourceSpan,
	second_span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateStructFieldInit.code())
		.with_message(format!(
			"field `{}` specified more than once",
			field_name
		))
		.with_label(second_span.primary_label())
		.with_label(
			first_span
				.secondary_label()
				.with_message("first use of this field"),
		)
}

fn report_missing_struct_fields(
	details: MissingStructFieldsDiagnostic<'_>,
) -> Diagnostic<FileId> {
	let fields_str = details
		.missing_fields
		.iter()
		.map(|field| format!("`{}`", field))
		.collect::<Vec<_>>()
		.join(", ");
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingStructFields.code())
		.with_message(format!(
			"missing fields {} in initializer of `{}`",
			fields_str, details.struct_name
		))
		.with_label(Label::primary(details.file_id, details.init_span))
}

fn report_index_on_non_indexable(
	span: SourceSpan,
	type_name: String,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::IndexOnNonIndexable.code())
		.with_message(format!(
			"cannot index into a value of type `{type_name}`"
		))
		.with_label(span.primary_label())
		.with_note(
			"indexing is only supported on array `&[T; N]` and slice `&[T]` types",
		)
}

pub(super) struct UnknownStructFieldDiagnostic<'a> {
	pub(super) file_id: FileId,
	pub(super) struct_name: &'a str,
	pub(super) field_name: &'a str,
	pub(super) field_span: TextSpan,
}

struct MissingStructFieldsDiagnostic<'a> {
	file_id: FileId,
	struct_name: &'a str,
	missing_fields: Box<[&'a str]>,
	init_span: TextSpan,
}

fn report_array_size_mismatch(
	span: SourceSpan,
	expected: u32,
	actual: usize,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ArraySizeMismatch.code())
		.with_message(format!(
			"array literal has {actual} element(s) but the type expects {expected}"
		))
		.with_label(span.primary_label())
}

fn report_array_repeat_count_not_const(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ArrayRepeatCountNotConst.code())
		.with_message(
			"array repeat count must be a compile-time integer constant",
		)
		.with_label(span.primary_label())
}

fn report_array_element_not_const(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ArrayElementNotConst.code())
		.with_message("array literal elements must be compile-time constants")
		.with_label(span.primary_label())
		.with_note(
			"only integer and float literals are allowed in array literals",
		)
}
