//! Path and member expressions: bare identifiers, `a::b::c`, qualified
//! (`<T as Trait>::x`) and grouped paths, field/method access on a value, and
//! turning an already-resolved symbol or namespace member into an expression.

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Converts a `ResolvedSymbol` into an `Expression`, registering any
	/// access entries along the way. The caller is responsible for emitting
	/// the not-found diagnostic when `resolve_symbol` returned `None`.
	fn resolved_symbol_to_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		resolved: ResolvedSymbol,
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		match resolved {
			ResolvedSymbol::Local {
				scope_index,
				local_index,
			} => {
				func_ctx.stack.record_local_access(
					scope_index,
					local_index,
					LocalAccess {
						kind: access_ctx.access_kind,
						span: expr_span,
					},
				);
				let local = func_ctx.stack.get_local(scope_index, local_index);
				if matches!(
					access_ctx.access_kind,
					AccessKind::Write | AccessKind::ReadWrite
				) && local.mut_span.is_none()
				{
					self.tir.diagnostics.push(report_cannot_mutate_immutable(
						SourceSpan::new(
							func_ctx.resolve_context.file_id,
							expr_span,
						),
					));
				}
				Ok(Expression {
					kind: ExprKind::Local {
						local_index,
						scope_index,
					},
					ty: local.ty,
					span: expr_span,
				})
			}
			ResolvedSymbol::Global(kind) => self.global_symbol_to_expression(
				func_ctx.resolve_context,
				access_ctx,
				kind,
				expr_span,
			),
		}
	}

	/// Converts a global `SymbolKind` into an `Expression`. Takes only a
	/// `ResolveContext` so it is usable from const/global initializer resolution
	/// which has no enclosing function.
	fn global_symbol_to_expression(
		&mut self,
		resolve_ctx: ResolveContext,
		access_ctx: AccessContext,
		kind: SymbolKind,
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		match kind {
			SymbolKind::Function { func_index } => {
				let func_id = self.tir.functions[func_index as usize].id;
				let type_params_len =
					self.tir.functions[func_index as usize].type_params.len();
				self.tir.functions[func_index as usize]
					.accesses
					.push(SourceSpan::new(resolve_ctx.file_id, expr_span));
				let ty = self.intern_type(Type::FunctionItem {
					id: func_id,
					type_args: vec![TypeIndex::INFER; type_params_len]
						.into_boxed_slice(),
				});
				Ok(Expression {
					kind: ExprKind::Function { id: func_id },
					ty,
					span: expr_span,
				})
			}
			SymbolKind::Global { global_index } => {
				let global = &mut self.tir.globals[global_index as usize];
				global
					.accesses
					.push(SourceSpan::new(resolve_ctx.file_id, expr_span));
				if matches!(
					access_ctx.access_kind,
					AccessKind::Write | AccessKind::ReadWrite
				) && global.mut_span.is_none()
				{
					self.tir.diagnostics.push(report_cannot_mutate_immutable(
						SourceSpan::new(resolve_ctx.file_id, expr_span),
					));
				}
				let id = global.id;
				let ty = global.ty.inner;
				Ok(Expression {
					kind: ExprKind::Global { id },
					ty,
					span: expr_span,
				})
			}
			SymbolKind::Const { const_index } => {
				let constant = &mut self.tir.constants[const_index as usize];
				constant
					.accesses
					.push(SourceSpan::new(resolve_ctx.file_id, expr_span));
				let id = constant.id;
				let ty = constant.ty.inner;
				Ok(Expression {
					kind: ExprKind::Const { id },
					ty,
					span: expr_span,
				})
			}
			SymbolKind::Memory {
				memory_index,
				size: kind,
			} => {
				let memory = &mut self.tir.memories[memory_index as usize];
				memory
					.accesses
					.push(SourceSpan::new(resolve_ctx.file_id, expr_span));
				let id = memory.id;
				let ty = self.intern_type(Type::Memory { size: kind, id });
				Ok(Expression {
					kind: ExprKind::Memory { id },
					ty,
					span: expr_span,
				})
			}
			SymbolKind::Enum { .. }
			| SymbolKind::Module { .. }
			| SymbolKind::Struct { .. }
			| SymbolKind::Trait { .. }
			| SymbolKind::TypeSet { .. }
			| SymbolKind::TypeAlias { .. } => {
				self.tir.diagnostics.push(report_namespace_used_as_value(
					SourceSpan::new(resolve_ctx.file_id, expr_span),
				));
				Ok(Expression {
					kind: ExprKind::Error,
					ty: TypeIndex::ERROR,
					span: expr_span,
				})
			}
			#[cfg(debug_assertions)]
			SymbolKind::TraitAssocType { .. } => unreachable!(),
			#[cfg(not(debug_assertions))]
			_ => unreachable!(),
		}
	}

	pub(super) fn build_object_access_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		object: &Spanned<ast::Expression>,
		member: Spanned<SymbolU32>,
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let object = self.build_expression(func_ctx, access_ctx, object)?;

		if let Type::Struct { struct_index, args } =
			&self.tir.types[object.ty.as_usize()]
		{
			let (struct_index, args) = (*struct_index, args.clone());
			if let Some(resolved) = self.resolve_struct_field(
				func_ctx.resolve_context,
				struct_index,
				&args,
				member,
				FieldAccessKind::for_access(access_ctx.access_kind),
			) {
				let field_ty = resolved.ty;
				return match object.kind {
					ExprKind::Load { place } => {
						let memory = place.memory;
						let mutable = place.mutable;
						Ok(Expression {
							kind: ExprKind::Load {
								place: Box::new(Place {
									kind: PlaceKind::Field {
										object: place,
										member,
									},
									ty: field_ty,
									memory,
									mutable,
									span: expr_span,
								}),
							},
							ty: field_ty,
							span: expr_span,
						})
					}
					_ => Ok(Expression {
						kind: ExprKind::FieldAccess {
							object: Box::new(object),
							field: member,
						},
						ty: field_ty,
						span: expr_span,
					}),
				};
			}
		}

		let entry = self.resolve_impl_member(
			func_ctx.resolve_context,
			object.ty,
			member.inner,
			member.span,
		);
		match entry {
			MemberLookup::Inherent { .. } | MemberLookup::Trait { .. } => {
				let member_name = self.interner.resolve(member.inner).unwrap();
				let type_name = self
					.formatter(func_ctx.resolve_context.namespace)
					.display_type(object.ty)
					.unwrap();
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::NotAField.code())
						.with_message(format!(
							"cannot access `{member_name}` as a field"
						))
						.with_label(
							SourceSpan::new(
								func_ctx.resolve_context.file_id,
								member.span,
							)
							.primary_label()
							.with_message("not a field"),
						)
						.with_note(format!(
							"use `{type_name}::{member_name}` to access it instead"
						)),
				);
				Err(())
			}
			MemberLookup::NotFound => {
				self.tir.diagnostics.push(report_undeclared_identifier(
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						member.span,
					),
				));
				Err(())
			}
			MemberLookup::Ambiguous => Err(()),
		}
	}

	/// Build a TIR expression from a parsed `Path`.
	///
	/// - Single segment, no type args  → identifier / local / global lookup
	/// - Single segment, with type args → generic function reference
	/// - Multiple segments              → resolve each leading segment as a
	///   namespace `TypeIndex`, then dispatch via
	///   `build_namespace_member_expression`
	pub(super) fn build_path_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		path: &[ast::PathSegment],
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let last = path.last().expect("path is non-empty");

		// ── single-segment, no type args: plain identifier / local / global ───
		if path.len() == 1 && last.type_args.is_empty() {
			let resolved = match self
				.resolve_symbol_forcing(func_ctx, last.ident)
			{
				Ok(resolved) => resolved,
				// Cyclic — already reported.
				Err(()) => {
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: access_ctx.expected_type.infer_or(TypeIndex::ERROR),
						span: expr_span,
					});
				}
			};
			return match resolved {
				Some(resolved) => self.resolved_symbol_to_expression(
					func_ctx, access_ctx, resolved, expr_span,
				),
				None => {
					self.tir.diagnostics.push(report_undeclared_identifier(
						SourceSpan::new(
							func_ctx.resolve_context.file_id,
							expr_span,
						),
					));
					Ok(Expression {
						kind: ExprKind::Error,
						ty: access_ctx.expected_type.infer_or(TypeIndex::ERROR),
						span: expr_span,
					})
				}
			};
		}

		// ── single-segment with type args: generic function reference ──────────
		if path.len() == 1 {
			let seg = &path[0];
			let func_index = match self
				.lookup_global_symbol_reporting(
					func_ctx.resolve_context.namespace,
					(SymbolNamespace::Value, seg.ident.inner),
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						seg.ident.span,
					),
				)
				.and_then(SymbolEntry::resolved_kind)
			{
				Some(SymbolKind::Function { func_index }) => func_index,
				_ => {
					self.tir.diagnostics.push(report_undeclared_identifier(
						SourceSpan::new(
							func_ctx.resolve_context.file_id,
							expr_span,
						),
					));
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::ERROR,
						span: expr_span,
					});
				}
			};

			let type_params_len =
				self.tir.functions[func_index as usize].type_params.len();
			if type_params_len == 0 {
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::TypeArgCountMismatch.code())
						.with_message("function is not generic")
						.with_label(
							SourceSpan::new(
								func_ctx.resolve_context.file_id,
								expr_span,
							)
							.primary_label()
							.with_message(
								"type arguments provided but this function has no type parameters",
							),
						),
				);
				return Ok(Expression {
					kind: ExprKind::Error,
					ty: TypeIndex::ERROR,
					span: expr_span,
				});
			}
			if seg.type_args.len() > type_params_len {
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::TypeArgCountMismatch.code())
						.with_message(format!(
							"expected {} type argument{}, found {}",
							type_params_len,
							if type_params_len == 1 { "" } else { "s" },
							seg.type_args.len()
						))
						.with_label(
							SourceSpan::new(
								func_ctx.resolve_context.file_id,
								expr_span,
							)
							.primary_label()
							.with_message("wrong number of type arguments"),
						),
				);
			}

			let type_params =
				self.tir.functions[func_index as usize].type_params.len();
			let resolved_args: Box<[TypeIndex]> = seg
				.type_args
				.iter()
				.map(|arg| {
					self.resolve_type(
						func_ctx.resolve_context,
						func_ctx.scope,
						arg,
					)
				})
				.chain(std::iter::repeat(TypeIndex::INFER))
				.take(type_params)
				.collect();
			let func = &mut self.tir.functions[func_index as usize];
			func.accesses.push(SourceSpan::new(
				func_ctx.resolve_context.file_id,
				seg.ident.span,
			));
			let func_id = func.id;
			let ty = self.intern_type(Type::FunctionItem {
				id: func_id,
				type_args: resolved_args,
			});
			return Ok(Expression {
				kind: ExprKind::Function { id: func_id },
				ty,
				span: expr_span,
			});
		}

		// ── multi-segment: resolve namespace chain then dispatch on last member ─
		// Walk segments[0..n-1] left-to-right: each resolves to a namespace TypeIndex.
		let first = &path[0];
		let mut namespace_ty = self.resolve_type_identifier(
			func_ctx.resolve_context,
			func_ctx.scope,
			first.ident,
			TypeArgArity::AllowInfer,
		)?;
		let mut namespace_span = first.ident.span;

		// Apply turbofish type args on the first segment when present, e.g.
		// `Wrapper::<u32>::new(...)` → instantiate to `Wrapper<u32>`.
		if !first.type_args.is_empty() {
			let resolve_context = func_ctx.resolve_context;
			let struct_index = match &self.tir.types[namespace_ty.as_usize()] {
				Type::Struct { struct_index, .. } => *struct_index,
				_ => {
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_message(
								"type arguments are not supported here",
							)
							.with_label(Label::primary(
								resolve_context.file_id,
								first.ident.span,
							)),
					);
					return Err(());
				}
			};
			let resolved_args: Box<[TypeIndex]> = first
				.type_args
				.iter()
				.map(|arg| {
					self.resolve_type(resolve_context, func_ctx.scope, arg)
				})
				.collect();
			namespace_ty = self.intern_type(Type::Struct {
				struct_index,
				args: resolved_args,
			});
		}

		for segment in &path[1..path.len() - 1] {
			// namespace_span grows to cover all qualifier segments so far.
			// TODO: per-segment span requires a nested namespace expression node.
			namespace_ty = self.resolve_namespace_type_member(
				func_ctx.resolve_context,
				func_ctx.scope,
				Spanned {
					inner: namespace_ty,
					span: namespace_span,
				},
				segment,
				TypeArgArity::AllowInfer,
			)?;
			namespace_span =
				TextSpan::new(namespace_span.start, segment.ident.span.end);
		}

		self.build_namespace_member_expression(
			func_ctx,
			ast::Spanned {
				inner: namespace_ty,
				span: namespace_span,
			},
			last,
			expr_span,
		)
	}

	/// Resolves `<Type as Trait>::item` in expression position. Resolves
	/// `root.self_type` and `root.trait_path` the ordinary way, then — if
	/// `segments[0]` is the last segment — builds it as a value via
	/// `build_required_trait_member_expression`, which looks up exactly the
	/// named trait instead of searching every applicable one. If there are
	/// further segments (rare, but Rust allows `<T as
	/// Trait>::Assoc::method()`), `segments[0]` must instead resolve to an
	/// intermediate namespace `TypeIndex` — the same job
	/// `resolve_required_trait_member_type` already does on the type side —
	/// and only the last segment becomes the value, exactly like
	/// `build_path_expression`'s own multi-segment case above.
	pub(super) fn build_qualified_path_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		root: &ast::QualifiedPathRoot,
		segments: &[ast::PathSegment],
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let base_ty = Spanned {
			inner: self.resolve_type(
				func_ctx.resolve_context,
				func_ctx.scope,
				&root.self_type,
			),
			span: root.self_type.span,
		};
		let required_trait = match self.resolve_path_segments_as_bound(
			func_ctx.resolve_context,
			&root.trait_path,
			root.span,
		) {
			Ok(BoundKind::Trait(trait_bound)) => trait_bound.trait_index,
			Ok(BoundKind::TypeSet(_)) => {
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_message(
							"expected a trait after `as`, found a typeset",
						)
						.with_label(Label::primary(
							func_ctx.resolve_context.file_id,
							root.span,
						)),
				);
				return Err(());
			}
			Err(()) => return Err(()),
		};

		let first = &segments[0];
		if segments.len() == 1 {
			return self.build_required_trait_member_expression(
				func_ctx,
				base_ty,
				required_trait,
				first,
				root.span,
				expr_span,
			);
		}

		let mut namespace_ty = self.resolve_required_trait_member_type(
			func_ctx.resolve_context,
			base_ty,
			required_trait,
			first,
			root.span,
		)?;
		let mut namespace_span = first.ident.span;
		for segment in &segments[1..segments.len() - 1] {
			namespace_ty = self.resolve_namespace_type_member(
				func_ctx.resolve_context,
				func_ctx.scope,
				Spanned {
					inner: namespace_ty,
					span: namespace_span,
				},
				segment,
				TypeArgArity::AllowInfer,
			)?;
			namespace_span =
				TextSpan::new(namespace_span.start, segment.ident.span.end);
		}

		self.build_namespace_member_expression(
			func_ctx,
			Spanned {
				inner: namespace_ty,
				span: namespace_span,
			},
			segments.last().unwrap(),
			expr_span,
		)
	}

	/// Resolves `<Type>::item` in expression position — a bare bracketed
	/// self-type with no trait qualification. Structurally identical to
	/// `build_path_expression`'s multi-segment case; `inner` just fills the
	/// role the first segment normally plays.
	pub(super) fn build_grouped_path_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		inner: &ast::Spanned<ast::TypeExpression>,
		segments: &[ast::PathSegment],
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let base_ty = Spanned {
			inner: self.resolve_type(
				func_ctx.resolve_context,
				func_ctx.scope,
				inner,
			),
			span: inner.span,
		};

		let first = &segments[0];
		if segments.len() == 1 {
			return self.build_namespace_member_expression(
				func_ctx, base_ty, first, expr_span,
			);
		}

		let mut namespace_ty = self.resolve_namespace_type_member(
			func_ctx.resolve_context,
			func_ctx.scope,
			base_ty,
			first,
			TypeArgArity::AllowInfer,
		)?;
		let mut namespace_span = first.ident.span;
		for segment in &segments[1..segments.len() - 1] {
			namespace_ty = self.resolve_namespace_type_member(
				func_ctx.resolve_context,
				func_ctx.scope,
				Spanned {
					inner: namespace_ty,
					span: namespace_span,
				},
				segment,
				TypeArgArity::AllowInfer,
			)?;
			namespace_span =
				TextSpan::new(namespace_span.start, segment.ident.span.end);
		}

		self.build_namespace_member_expression(
			func_ctx,
			Spanned {
				inner: namespace_ty,
				span: namespace_span,
			},
			segments.last().unwrap(),
			expr_span,
		)
	}

	/// Resolve a type-namespace member (used when walking intermediate path
	/// segments, and the final one): given a resolved namespace `TypeIndex`,
	/// look up `member_sym` as a nested namespace and return its `TypeIndex`.
	/// `type_args` is the member's own turbofish, if any (always empty for
	/// intermediate segments — only the final segment of a path can carry
	/// one); resolving it here, rather than having the caller resolve a
	/// bare reference first and separately re-resolve it with real args
	/// after, keeps this the one place that both looks up the symbol and
	/// applies its arguments.
	/// Searches `base`'s own declared bound traits (via `abstract_type_bounds`
	/// — works for both a `TypeParam` and a nested `AssocTypeProjection`) for
	/// ones declaring an associated type named `member_name`, returning the
	/// resulting `AssocTypeProjection`. `Ok(None)` means no bound trait
	/// declares it at all — the caller reports its own tailored
	/// not-found diagnostic. More than one candidate is a real ambiguity
	/// (e.g. `Mem::Size::Foo` where `Size` is bound by both a trait
	/// declaring `Foo` and an extra `where { Size: OtherTrait }` that also
	/// declares one) — reported the same way `resolve_impl_member` reports
	/// multiple applicable expression-position items, pointing at the
	/// qualified `<Type as Trait>::Item` syntax as the fix.
	fn resolve_assoc_type_via_bounds(
		&mut self,
		resolve_context: ResolveContext,
		base: TypeIndex,
		member_name: SymbolU32,
		member_span: TextSpan,
	) -> Result<Option<TypeIndex>, ()> {
		// Collected once into an owned `Vec<TraitIndex>` (`TraitIndex` is
		// `Copy`, so this is just a handful of `u32`s) rather than
		// re-fetching `abstract_type_bounds(base)` on every iteration —
		// `ensure_signature` below needs `&mut self`, so it can't interleave
		// with a live borrow of the bounds list, but for an
		// `AssocTypeProjection` base `abstract_type_bounds` is a real
		// recursive scan (see its own doc comment), not a cheap field read,
		// so re-deriving it per iteration was real wasted work.
		let bound_trait_indices: Vec<TraitIndex> = self
			.tir
			.abstract_type_bounds(base)
			.map(|bounds| bounds.traits.iter().map(|b| b.trait_index).collect())
			.unwrap_or_default();
		let mut found: Option<TraitIndex> = None;
		let mut candidates: Vec<TraitIndex> = Vec::new();
		for trait_index in bound_trait_indices {
			self.ensure_signature(self.tir.traits[trait_index as usize].id);
			if !matches!(
				self.tir.traits[trait_index as usize]
					.entries
					.get(&member_name),
				Some(ImplEntry::AssocType(_))
			) {
				continue;
			}
			match found {
				None => found = Some(trait_index),
				// The same trait showing up twice (e.g. a redundant `where`
				// bound repeating what the assoc type's own declaration
				// already requires, or plain `T: Foo + Foo`) isn't a second
				// candidate — it's one trait, counted once, same as Rust
				// silently collapsing a duplicate bound instead of erroring.
				Some(first) if first == trait_index => {}
				Some(first) => {
					if candidates.is_empty() {
						candidates.push(first);
					}
					candidates.push(trait_index);
				}
			}
		}

		if !candidates.is_empty() {
			let member_name_str = self.interner.resolve(member_name).unwrap();
			let type_name = self
				.formatter(resolve_context.namespace)
				.display_type(base)
				.unwrap_or_default();
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
						"ambiguous — use `<{type_name} as Trait>::{member_name_str}` to specify which trait's `{member_name_str}` is meant"
					)),
			);
			for trait_index in &candidates {
				let trait_ = &self.tir.traits[*trait_index as usize];
				let trait_name =
					self.interner.resolve(trait_.name.inner).unwrap();
				let name_span = trait_
					.assoc_types
					.get(&member_name)
					.map(|at| at.name_span)
					.unwrap_or(trait_.name.span);
				diagnostic.labels.push(
					Label::secondary(trait_.file_id, name_span).with_message(
						format!("candidate: `{trait_name}::{member_name_str}`"),
					),
				);
			}
			self.tir.diagnostics.push(diagnostic);
			return Err(());
		}

		let Some(trait_index) = found else {
			return Ok(None);
		};
		if let Some(at) = self.tir.traits[trait_index as usize]
			.assoc_types
			.get_mut(&member_name)
		{
			at.accesses
				.push(SourceSpan::new(resolve_context.file_id, member_span));
		}
		Ok(Some(self.intern_type(Type::AssocTypeProjection {
			trait_index,
			assoc_name: member_name,
			base,
		})))
	}

	pub(super) fn resolve_namespace_type_member(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		namespace: Spanned<TypeIndex>,
		member: &ast::PathSegment,
		arity: TypeArgArity,
	) -> Result<TypeIndex, ()> {
		// Type args are only ever meaningful on a struct/alias found in a
		// module namespace (below); every other kind of member (an
		// associated type reached through a type param or a nested
		// projection) can never carry them.
		if !member.type_args.is_empty()
			&& !matches!(
				&self.tir.types[namespace.inner.as_usize()],
				Type::Namespace { .. }
			) {
			self.tir.diagnostics.push(
				Diagnostic::error()
					.with_message("type arguments are not supported here")
					.with_label(Label::primary(
						resolve_context.file_id,
						// TODO: improve diagnostic span, point to the actaul turbofish
						member.ident.span,
					)),
			);
			return Err(());
		}
		match &self.tir.types[namespace.inner.as_usize()] {
			// No access recorded for `namespace` itself here: a
			// `Type::Namespace` value only ever comes from
			// `symbol_kind_to_type`, whose only two call sites both call
			// `record_symbol_access` immediately beforehand, at the
			// exact segment span that produced it — recording it again
			// here would duplicate that entry.
			Type::Namespace { namespace_idx } => {
				let namespace_idx = *namespace_idx;
				let kind = self.resolve_pending_namespace_symbol(
					resolve_context.namespace,
					namespace_idx,
					(SymbolNamespace::Type, member.ident.inner),
					SourceSpan::new(resolve_context.file_id, member.ident.span),
				)?;
				match kind {
					Some(
						kind @ (SymbolKind::Struct { .. }
						| SymbolKind::TypeAlias { .. }),
					) => {
						let resolved_args: Vec<_> = member
							.type_args
							.iter()
							.map(|arg| {
								self.resolve_type(resolve_context, scope, arg)
							})
							.collect();
						let ty = self.resolve_generic_type_application(
							resolve_context,
							kind,
							&resolved_args,
							member.ident.span,
							arity,
						);
						if ty == TypeIndex::ERROR {
							Err(())
						} else {
							Ok(ty)
						}
					}
					Some(kind) => {
						self.tir.record_symbol_access(
							resolve_context.file_id,
							kind,
							member.ident.span,
						);
						self.symbol_kind_to_type(kind).ok_or_else(|| {
							self.tir.diagnostics.push(report_undeclared_type(
								SourceSpan::new(
									resolve_context.file_id,
									member.ident.span,
								),
							));
						})
					}
					None => {
						self.tir.diagnostics.push(report_undeclared_type(
							SourceSpan::new(
								resolve_context.file_id,
								member.ident.span,
							),
						));
						// TODO: typecheck member.type_args if any?
						Err(())
					}
				}
			}
			Type::TypeParam { .. } => {
				// `abstract_type_bounds` already dispatches on `TypeParam`
				// vs. the `AssocTypeProjection` case below internally, so
				// both arms share `resolve_assoc_type_via_bounds` for their
				// candidate search.
				match self.resolve_assoc_type_via_bounds(
					resolve_context,
					namespace.inner,
					member.ident.inner,
					member.ident.span,
				)? {
					Some(ty) => Ok(ty),
					None => {
						self.tir.diagnostics.push(report_undeclared_type(
							SourceSpan::new(
								resolve_context.file_id,
								member.ident.span,
							),
						));
						Err(())
					}
				}
			}
			Type::AssocTypeProjection { .. } => {
				// Nested projection: e.g. `A::M::Size` where namespace_ty = `A::M`.
				if let Some(ty) = self.resolve_assoc_type_via_bounds(
					resolve_context,
					namespace.inner,
					member.ident.inner,
					member.ident.span,
				)? {
					return Ok(ty);
				}
				let member_name =
					self.interner.resolve(member.ident.inner).unwrap();
				let type_name = self
					.formatter(resolve_context.namespace)
					.display_type(namespace.inner)
					.unwrap_or_default();
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::UndeclaredType.code())
						.with_message(format!(
							"no type named `{member_name}` found for type `{type_name}`",
						))
						.with_label(Label::primary(
							resolve_context.file_id,
							member.ident.span,
						)),
				);
				Err(())
			}
			_ => match self.resolve_impl_member(
				resolve_context,
				namespace.inner,
				member.ident.inner,
				member.ident.span,
			) {
				MemberLookup::Trait {
					entry: ImplEntry::AssocType(idx),
					trait_index,
					..
				} => {
					if let Some(assoc_type) = self.tir.traits
						[trait_index as usize]
						.assoc_types
						.get_mut(&member.ident.inner)
					{
						assoc_type.accesses.push(SourceSpan::new(
							resolve_context.file_id,
							member.ident.span,
						));
					}
					Ok(self.tir.assoc_type_impls[idx as usize]
						.ty
						.unwrap()
						.inner)
				}
				MemberLookup::Inherent {
					entry: ImplEntry::AssocType(idx),
					..
				} => Ok(self.tir.assoc_type_impls[idx as usize]
					.ty
					.unwrap()
					.inner),
				MemberLookup::Ambiguous => Err(()),
				_ => {
					// TODO: we could improve the diagnostics here
					// one case for MemberLookup::NotFound and another for Found with not correct kind
					let member_name =
						self.interner.resolve(member.ident.inner).unwrap();
					let type_name = self
						.formatter(resolve_context.namespace)
						.display_type(namespace.inner)
						.unwrap();
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_code(DiagnosticCode::UndeclaredType.code())
							.with_message(format!(
								"no type named `{member_name}` found for type `{type_name}`",
							))
							.with_label(Label::primary(
								resolve_context.file_id,
								member.ident.span,
							)),
					);
					Err(())
				}
			},
		}
	}

	/// Resolve `member_sym` within `namespace_ty`, emitting a diagnostic and
	/// returning `Err(())` when resolution fails. On success returns
	/// `Ok(ResolvedMember)` — the caller decides whether the specific kind is
	/// valid in its context (e.g. callability).
	fn resolve_namespace_member(
		&mut self,
		resolve_context: ResolveContext,
		namespace: Spanned<TypeIndex>,
		member: Spanned<SymbolU32>,
	) -> Result<ResolvedMember, ()> {
		let file_id = resolve_context.file_id;
		let lookup = self.resolve_impl_member(
			resolve_context,
			namespace.inner,
			member.inner,
			member.span,
		);
		// See the identical check in `resolve_method_call`: a `TypeParam`
		// namespace (e.g. `T::SOME_CONST` inside `fn f<T: SomeTrait>()`)
		// resolving to `MemberLookup::Trait` is abstract dispatch — mark
		// every impl of the trait accessed, not just the one entry
		// returned, since the concrete one is only known at monomorphization.
		if let MemberLookup::Trait { trait_index, .. } = &lookup
			&& matches!(
				self.tir.types[namespace.inner.as_usize()],
				Type::TypeParam { .. }
			) {
			self.record_abstract_dispatch_access(
				*trait_index,
				member.inner,
				SourceSpan::new(file_id, member.span),
			);
		}

		match lookup {
			MemberLookup::Inherent {
				entry: ImplEntry::AssocConstant(index),
				type_args,
			}
			| MemberLookup::Trait {
				entry: ImplEntry::AssocConstant(index),
				type_args,
				..
			} => {
				return Ok(ResolvedMember::Const {
					const_index: index,
					type_args,
				});
			}
			MemberLookup::Inherent {
				entry:
					ImplEntry::Method(func_index)
					| ImplEntry::AssocFunction(func_index),
				type_args,
			}
			| MemberLookup::Trait {
				entry:
					ImplEntry::Method(func_index)
					| ImplEntry::AssocFunction(func_index),
				type_args,
				..
			} => {
				return Ok(ResolvedMember::Function {
					func_index,
					type_args,
				});
			}
			MemberLookup::Inherent {
				entry: ImplEntry::AssocType(_),
				..
			}
			| MemberLookup::Trait {
				entry: ImplEntry::AssocType(_),
				..
			}
			| MemberLookup::NotFound => {}
			MemberLookup::Ambiguous => return Err(()),
		}

		match &self.tir.types[namespace.inner.as_usize()] {
			Type::Memory { .. } => {
				self.tir.diagnostics.push(report_undeclared_identifier(
					SourceSpan::new(file_id, member.span),
				));
				Err(())
			}
			Type::Enum { enum_index } => {
				let enum_idx = *enum_index;
				match self.tir.enums[enum_idx as usize]
					.variant_lookup
					.get(&member.inner)
					.copied()
				{
					Some(variant_index) => Ok(ResolvedMember::EnumVariant {
						enum_index: enum_idx,
						variant_index,
					}),
					None => {
						self.tir.diagnostics.push(
							report_undeclared_identifier(SourceSpan::new(
								file_id,
								member.span,
							)),
						);
						Err(())
					}
				}
			}
			Type::Namespace { namespace_idx } => {
				let ns_idx = *namespace_idx;
				let resolved = self.resolve_pending_namespace_symbol(
					resolve_context.namespace,
					ns_idx,
					(SymbolNamespace::Value, member.inner),
					SourceSpan::new(file_id, member.span),
				)?;
				match resolved {
					Some(SymbolKind::Function { func_index }) => {
						// A plain module-level function has no impl/trait to
						// inherit a substitution from, but still needs its
						// own `type_params` slots present — `INFER` for all
						// of them, same as any other never-yet-called
						// generic function reference. Without this, `combined`
						// in the caller below would be built from a
						// too-short array and its own type params could
						// never bind at the call site.
						let total = self.tir.functions[func_index as usize]
							.total_type_param_count();
						Ok(ResolvedMember::Function {
							func_index,
							type_args: vec![TypeIndex::INFER; total]
								.into_boxed_slice(),
						})
					}
					Some(SymbolKind::Global { global_index }) => {
						Ok(ResolvedMember::Global { global_index })
					}
					Some(SymbolKind::Const { const_index }) => {
						Ok(ResolvedMember::Const {
							const_index,
							type_args: Box::new([]),
						})
					}
					_ => {
						self.tir.diagnostics.push(
							report_undeclared_identifier(SourceSpan::new(
								file_id,
								member.span,
							)),
						);
						Err(())
					}
				}
			}
			_ => {
				let member_name = self.interner.resolve(member.inner).unwrap();
				let type_name = self
					.formatter(resolve_context.namespace)
					.display_type(namespace.inner)
					.unwrap();
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::UndeclaredIdentifier.code())
						.with_message(format!(
							"no associated item named `{member_name}` found for type `{type_name}`",
						))
						.with_label(
							SourceSpan::new(file_id, member.span)
								.primary_label(),
						),
				);
				Err(())
			}
		}
	}

	/// Core namespace-member dispatch: look up `member` inside a type whose
	/// `TypeIndex` has already been resolved.
	///
	/// No access recorded for `namespace` itself here: a `Type::Namespace`
	/// value only ever comes from `symbol_kind_to_type`, whose only two
	/// call sites both call `record_symbol_access` immediately
	/// beforehand, at the exact segment span that produced it — recording
	/// it again here would duplicate that entry.
	fn build_namespace_member_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		namespace: Spanned<TypeIndex>,
		segment: &ast::PathSegment,
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let resolved = self.resolve_namespace_member(
			func_ctx.resolve_context,
			namespace,
			segment.ident,
		)?;

		self.build_resolved_member_expression(
			func_ctx, namespace, resolved, segment, expr_span,
		)
	}

	/// Turns an already-resolved [`ResolvedMember`] into an [`Expression`] —
	/// the shared tail of [`Self::build_namespace_member_expression`] (the
	/// ordinary, searching lookup) and qualified-path expression resolution
	/// (`<Type as Trait>::item`, which resolves the member itself via
	/// `resolve_trait_member` instead but still needs the same
	/// turbofish-count check, access recording, and `NamespaceAccess`
	/// wrapping once it has one).
	fn build_resolved_member_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		namespace: Spanned<TypeIndex>,
		resolved: ResolvedMember,
		segment: &ast::PathSegment,
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let file_id = func_ctx.resolve_context.file_id;
		let member_span = segment.ident.span;
		match resolved {
			ResolvedMember::Function {
				func_index,
				type_args: impl_args,
			} => {
				let func_id = self.tir.functions[func_index as usize].id;
				let fn_params_len =
					self.tir.functions[func_index as usize].type_params.len();
				let type_params_len = self.tir.functions[func_index as usize]
					.total_type_param_count();

				if !segment.type_args.is_empty()
					&& segment.type_args.len() != fn_params_len
				{
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::TypeArgCountMismatch.code(),
							)
							.with_message(format!(
								"expected {} type argument{}, found {}",
								fn_params_len,
								if fn_params_len == 1 { "" } else { "s" },
								segment.type_args.len()
							))
							.with_label(
								SourceSpan::new(file_id, expr_span)
									.primary_label()
									.with_message(
										"wrong number of type arguments",
									),
							),
					);
				}

				self.tir.functions[func_index as usize]
					.accesses
					.push(SourceSpan::new(file_id, member_span));

				// `impl_args` is already `resolve_impl_member`'s full,
				// padded scheme (impl-inherited slots resolved from the
				// receiver where possible, `INFER` elsewhere) — reuse it in
				// place rather than rebuilding, and merge any explicit
				// turbofish into the function's *own* slots, which start
				// after the inherited prefix.
				let mut combined = impl_args;
				let inherited = type_params_len - fn_params_len;
				for (slot, ast_arg) in combined[inherited..]
					.iter_mut()
					.zip(segment.type_args.iter())
				{
					*slot = self.resolve_type(
						func_ctx.resolve_context,
						func_ctx.scope,
						ast_arg,
					);
				}

				let func_ty = self.intern_type(Type::FunctionItem {
					id: func_id,
					type_args: combined,
				});
				Ok(Expression {
					kind: ExprKind::NamespaceAccess {
						namespace,
						member: Box::new(Expression {
							kind: ExprKind::Function { id: func_id },
							ty: func_ty,
							span: member_span,
						}),
					},
					ty: func_ty,
					span: expr_span,
				})
			}
			ResolvedMember::Const {
				const_index,
				type_args,
			} => {
				self.tir.constants[const_index as usize]
					.accesses
					.push(SourceSpan::new(file_id, member_span));
				let id = self.tir.constants[const_index as usize].id;
				let raw_ty = self.tir.constants[const_index as usize].ty.inner;
				// Substitutes the owning trait's `Self` for the receiver's
				// own type — a no-op (`type_args` empty) for a plain
				// module-level const, and for a trait const whose type
				// never mentions `Self` in the first place (`substitute_type`
				// returns any type unchanged when it contains nothing to
				// substitute). For a generic receiver (`Mem: Memory`),
				// `type_args` is `[Mem's own TypeIndex]`, so this leaves the
				// projection deferred (still `Mem::Size`, not yet
				// concrete) rather than forcing it — exactly like a
				// `GenericMethodCall`'s abstract-method type stays
				// deferred until monomorphization substitutes a concrete
				// `Self`.
				let ty = self.substitute_type(raw_ty, &type_args);
				Ok(Expression {
					kind: ExprKind::NamespaceAccess {
						namespace,
						member: Box::new(Expression {
							kind: ExprKind::Const { id },
							ty,
							span: member_span,
						}),
					},
					ty,
					span: expr_span,
				})
			}
			ResolvedMember::Global { global_index } => {
				let global = &mut self.tir.globals[global_index as usize];
				global.accesses.push(SourceSpan::new(file_id, member_span));
				let global_id = global.id;
				let ty = global.ty.inner;
				Ok(Expression {
					kind: ExprKind::NamespaceAccess {
						namespace,
						member: Box::new(Expression {
							kind: ExprKind::Global { id: global_id },
							ty,
							span: member_span,
						}),
					},
					ty,
					span: expr_span,
				})
			}
			ResolvedMember::EnumVariant {
				enum_index,
				variant_index,
			} => {
				self.tir.enums[enum_index as usize].variants
					[variant_index as usize]
					.accesses
					.push(SourceSpan::new(file_id, member_span));
				Ok(Expression {
					kind: ExprKind::NamespaceAccess {
						namespace,
						member: Box::new(Expression {
							kind: ExprKind::EnumVariant {
								enum_index,
								variant_index,
							},
							ty: namespace.inner,
							span: member_span,
						}),
					},
					ty: namespace.inner,
					span: expr_span,
				})
			}
		}
	}

	/// Resolves `member` on `base_ty` under exactly `required_trait` and
	/// builds the resulting value expression — the expression-position half
	/// of qualified-path resolution (`<Type as Trait>::item`), used when
	/// `member` is the path's last segment. Mirrors
	/// `resolve_required_trait_member_type`'s use of `resolve_trait_member`
	/// instead of the ordinary searching lookup, then hands off to
	/// `build_resolved_member_expression` for the actual `Expression`
	/// construction shared with the unqualified path. `root_span` covers
	/// exactly `<Type as Trait>` — see
	/// `resolve_required_trait_member_type`'s doc comment for why it's used
	/// for the "trait not implemented" diagnostic instead of `member`'s own
	/// span.
	fn build_required_trait_member_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		base_ty: Spanned<TypeIndex>,
		required_trait: TraitIndex,
		segment: &ast::PathSegment,
		root_span: TextSpan,
		expr_span: TextSpan,
	) -> Result<Expression, ()> {
		let file_id = func_ctx.resolve_context.file_id;
		let member_span = SourceSpan::new(file_id, segment.ident.span);

		let lookup = self.resolve_trait_member(
			base_ty.inner,
			required_trait,
			segment.ident.inner,
		);
		// Same abstract-dispatch bookkeeping as `resolve_namespace_member`'s
		// identical check: a `TypeParam` receiver resolving through a known
		// trait is still abstract dispatch — every impl of the trait is a
		// potential access, since the concrete one is only known at
		// monomorphization.
		if lookup.is_ok()
			&& matches!(
				self.tir.types[base_ty.inner.as_usize()],
				Type::TypeParam { .. }
			) {
			self.record_abstract_dispatch_access(
				required_trait,
				segment.ident.inner,
				member_span,
			);
		}

		let resolved = match lookup {
			Ok((ImplEntry::AssocConstant(const_index), type_args)) => {
				ResolvedMember::Const {
					const_index,
					type_args,
				}
			}
			Ok((
				ImplEntry::Method(func_index)
				| ImplEntry::AssocFunction(func_index),
				type_args,
			)) => ResolvedMember::Function {
				func_index,
				type_args,
			},
			Ok((ImplEntry::AssocType(_), _))
			| Err(TraitMemberError::NoSuchMember) => {
				let trait_name = self
					.interner
					.resolve(
						self.tir.traits[required_trait as usize].name.inner,
					)
					.unwrap();
				let member_name =
					self.interner.resolve(segment.ident.inner).unwrap();
				self.tir
					.diagnostics
					.push(report_qualified_path_no_such_value(
						member_span,
						member_name,
						trait_name,
					));
				return Err(());
			}
			Err(TraitMemberError::NotImplemented) => {
				let type_name = self
					.formatter(func_ctx.resolve_context.namespace)
					.display_type(base_ty.inner)
					.unwrap_or_default();
				let trait_name = self
					.interner
					.resolve(
						self.tir.traits[required_trait as usize].name.inner,
					)
					.unwrap();
				self.tir.diagnostics.push(
					report_qualified_path_trait_not_satisfied(
						SourceSpan::new(file_id, root_span),
						&type_name,
						trait_name,
					),
				);
				return Err(());
			}
		};

		self.build_resolved_member_expression(
			func_ctx, base_ty, resolved, segment, expr_span,
		)
	}

	pub(super) fn build_type_application_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		callee: &Spanned<ast::Expression>,
		_args: &[Spanned<ast::TypeExpression>],
		expr_span: ast::TextSpan,
	) -> Result<Expression, ()> {
		// TypeApplication on a non-path callee, e.g. a bare `obj.field::<T>`
		// without a following call.  Method turbofish calls (`obj.m::<T>(args)`)
		// are handled by MethodCall.  Identifier-started turbofish (`f::<T>()`)
		// is fully handled by build_path_expression and never reaches here.
		// Type args are not semantically resolved for these forms; just build
		// the callee and carry its type through.
		let mut result = self.build_expression(
			func_ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			callee,
		)?;
		result.span = expr_span;
		Ok(result)
	}
}

/// Reported for a qualified path (`<Type as Trait>::item`) when `Type`
/// isn't bound by / doesn't implement `Trait` at all — same code/message
/// shape as the existing (unqualified) trait-bound-violation diagnostic.
pub(super) fn report_qualified_path_trait_not_satisfied(
	span: SourceSpan,
	type_name: &str,
	trait_name: &str,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::TraitBoundViolation.code())
		.with_message(format!(
			"the trait bound `{type_name}: {trait_name}` is not satisfied"
		))
		.with_label(span.primary_label().with_message(format!(
			"the trait `{trait_name}` is not implemented for `{type_name}`"
		)))
}

/// Reported for a qualified path in type position (`<Type as
/// Trait>::Item`) when `Trait` is implemented but has no associated type
/// with that name — same code as the unqualified "no type named" fallback.
pub(super) fn report_qualified_path_no_such_type(
	span: SourceSpan,
	member_name: &str,
	trait_name: &str,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredType.code())
		.with_message(format!(
			"no type named `{member_name}` found in trait `{trait_name}`",
		))
		.with_label(span.primary_label())
}

/// Reported for a qualified path in expression position (`<Type as
/// Trait>::item`) when `Trait` is implemented but has no value member
/// (function/const) with that name — same code as the unqualified "no
/// associated item" fallback.
fn report_qualified_path_no_such_value(
	span: SourceSpan,
	member_name: &str,
	trait_name: &str,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredIdentifier.code())
		.with_message(format!(
			"no associated item named `{member_name}` found in trait `{trait_name}`",
		))
		.with_label(span.primary_label())
}

fn report_namespace_used_as_value(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::NamespaceUsedAsValue.code())
		.with_message("expected a value, found a namespace")
		.with_label(span.primary_label())
		.with_note("use `::` to access members of this namespace")
}

pub(super) fn report_cannot_take_address_of_value(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
        .with_code(DiagnosticCode::InvalidAssignmentTarget.code())
        .with_message("cannot take address of a temporary or stack value")
        .with_label(
            span.primary_label()
                .with_message("this expression is a value, not a location in memory"),
        )
        .with_note(
            "`.&` is only valid on places reachable through a pointer, e.g. `ptr.*` or `ptr.*.field`",
        )
}
