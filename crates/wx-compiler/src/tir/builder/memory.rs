//! Linear memory and pointers: `memory` declarations and their
//! `#[memory_limits(..)]` attribute, the synthetic `Memory` trait impl each
//! declaration gets, pointer dereference, and the ambient-memory lookup that
//! an unqualified `*T` resolves through.

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Phase 2 for a `memory` declaration: resolves its `Memory where { Size
	/// = .. }` bound, records the `Memory` entry, interns its `Type::Memory`,
	/// and registers the synthetic trait impl that makes `Memory`'s members
	/// (`Size`, `INDEX`, `DATA_END`, `PAGE_SIZE`, ...) reachable on it.
	///
	/// Every early return here leaves the declaration bound to a placeholder
	/// (see `register_placeholder_memory`) after reporting a diagnostic;
	/// `ensure_signature` marks the `DefId` `Done` once this returns, so
	/// bailing out early is safe.
	pub(super) fn signature_memory(
		&mut self,
		resolve_context: ResolveContext,
		item: &'ast ast::Item,
	) {
		// Not `unreachable!()`: `AstNodeRef::Memory` has a second construction
		// site in `pre_scan_item`'s `ast::ImportDeclaration::Memory` arm, which
		// stores the *enclosing* `ast::Item::Import` rather than an
		// `ast::Item::Memory`. An imported memory therefore lands here with a
		// non-`Memory` item and is skipped, exactly as it was before this was
		// split out of `ensure_signature`.
		let ast::Item::Memory {
			name,
			bound: kind,
			id,
			attributes,
		} = item
		else {
			return;
		};

		let kind_bounds = self.resolve_bounds(resolve_context, None, kind);
		let trait_index =
			match (kind_bounds.traits.as_ref(), kind_bounds.typeset) {
				([tb], None) => tb.trait_index,
				_ => {
					self.diagnostics.push(report_invalid_memory_kind(
						SourceSpan::new(resolve_context.file_id, kind.span),
					));
					self.register_placeholder_memory(
						resolve_context,
						*id,
						name,
					);
					return;
				}
			};

		let mut bindings: HashMap<SymbolU32, Spanned<TypeIndex>> =
			HashMap::new();
		if let ast::BoundExpression::WithBindings {
			bindings: where_bindings,
			..
		} = &kind.inner
		{
			for binding in where_bindings.iter() {
				// A memory declaration's `where` clause only ever pins an
				// associated type down to a concrete type (`Size = u32`) —
				// there's no sense in which `Size: SomeTrait` could determine
				// the pointer width this memory needs, so that kind of binding
				// is rejected here rather than silently ignored.
				let ty_expr = match &binding.kind {
					ast::AssocTypeBindingKind::Equals(ty_expr) => ty_expr,
					ast::AssocTypeBindingKind::Bound(bound) => {
						self.diagnostics.push(report_invalid_memory_kind(
							SourceSpan::new(
								resolve_context.file_id,
								bound.span,
							),
						));
						self.register_placeholder_memory(
							resolve_context,
							*id,
							name,
						);
						return;
					}
				};
				let val_ty = self.resolve_type(resolve_context, None, ty_expr);
				bindings.insert(
					binding.name.inner,
					Spanned {
						inner: val_ty,
						span: ty_expr.span,
					},
				);
				if let Some(at) = self.items.traits[usize::from(trait_index)]
					.assoc_types
					.get_mut(&binding.name.inner)
				{
					at.accesses.push(SourceSpan::new(
						resolve_context.file_id,
						binding.name.span,
					));
				}
				// No real `Self` exists yet at this point — the memory's own
				// `Type::Memory` isn't interned until after this loop (it
				// depends on `Size`, which is one of these very bindings).
				// `Memory::Size`'s bound (`PointerSize`) has no `where { .. =
				// Self }` clause today, so this is a no-op in practice;
				// `ERROR` only bites if a future bound here starts requiring
				// one.
				self.check_assoc_type_bounds(
					resolve_context,
					trait_index,
					TypeIndex::ERROR,
					binding.name,
					Spanned {
						inner: val_ty,
						span: ty_expr.span,
					},
				);
			}
		}

		let size_symbol = self.interner.get_or_intern("Size");
		let memory_size = match bindings.get(&size_symbol).copied() {
			Some(ty)
				if ty.inner == TypeIndex::U32 || ty.inner == TypeIndex::U64 =>
			{
				ty
			}
			_ => {
				self.diagnostics.push(report_invalid_memory_kind(
					SourceSpan::new(resolve_context.file_id, kind.span),
				));
				self.register_placeholder_memory(resolve_context, *id, name);
				return;
			}
		};

		let (min_pages, max_pages) = self.resolve_memory_limits_attribute(
			resolve_context.file_id,
			attributes,
		);

		let memory_index = self.items.expect_memory_index(*id);
		self.items.memories[usize::from(memory_index)] = Memory {
			id: *id,
			file_id: resolve_context.file_id,
			size: memory_size,
			name: *name,
			min_pages,
			max_pages,
			accesses: Vec::new(),
		};
		let memory_type = self.intern_type(Type::Memory {
			size: memory_size.inner,
			id: *id,
		});
		let members = self.seed_memory_trait_impl_with(
			trait_index,
			memory_type,
			memory_size,
		);

		// Register the memory type as implementing its declared trait so that
		// check_assoc_type_bounds can verify `type M: Memory` bindings on
		// concrete impls (e.g. `impl Allocator for T { type M = heap; }`). This
		// is an ordinary `TraitImpl` like any hand-written one — its members go
		// through the same ambiguity-checked trait tier as everything else, no
		// special-casing.
		let synthetic_def_id = self.id_generator.generate();
		let trait_impl_index = self.items.push_trait_impl(TraitImpl {
			id: synthetic_def_id,
			trait_index,
			type_params: Box::new([]),
			target: Spanned {
				inner: memory_type,
				span: name.span,
			},
			members,
			namespace: resolve_context.namespace,
			span: name.span,
			file_id: resolve_context.file_id,
			self_accesses: Vec::new(),
		});
		self.register_trait_impl(memory_type, trait_index, trait_impl_index);

		// Bind each namespace only if this occurrence still holds its own
		// `Pending` slot there — see the identical comment on the Struct
		// branch. Type and Value are independent claims (mirroring the two
		// separate `claim_name_binding` calls in `pre_scan_item`).
		let type_key = (SymbolNamespace::Type, name.inner);
		if self.still_pending(resolve_context.namespace, type_key, *id) {
			self.insert_symbol(
				resolve_context.namespace,
				type_key,
				SymbolKind::Memory {
					memory_index,
					size: memory_size.inner,
				},
				None,
			);
		}
		let value_key = (SymbolNamespace::Value, name.inner);
		if self.still_pending(resolve_context.namespace, value_key, *id) {
			self.insert_symbol(
				resolve_context.namespace,
				value_key,
				SymbolKind::Memory {
					memory_index,
					size: memory_size.inner,
				},
				None,
			);
		}
	}

	/// Binds a malformed `memory` declaration's name to an `ERROR`-sized
	/// placeholder so later references resolve to *something* and don't pile
	/// "undeclared identifier" on top of the real diagnostic. Keeps "still
	/// pending" unreachable in `resolve_symbol_kind_to_expression`. The
	/// stub itself (already defaulted to `TypeIndex::ERROR`, no bounds) was
	/// allocated in `pre_scan_item`; this only needs to bind the name. This
	/// placeholder is never actually reached downstream: `report_invalid_
	/// memory_kind` is an error diagnostic, and the real compile pipeline
	/// (`wx-cli`) aborts before `MIR::build` whenever TIR has any errors.
	fn register_placeholder_memory(
		&mut self,
		resolve_context: ResolveContext,
		id: ast::DefId,
		name: &ast::Spanned<SymbolU32>,
	) {
		let memory_index = self.items.expect_memory_index(id);
		let kind = TypeIndex::ERROR;
		let type_key = (SymbolNamespace::Type, name.inner);
		if self.still_pending(resolve_context.namespace, type_key, id) {
			self.insert_symbol(
				resolve_context.namespace,
				type_key,
				SymbolKind::Memory {
					memory_index,
					size: kind,
				},
				None,
			);
		}
		let value_key = (SymbolNamespace::Value, name.inner);
		if self.still_pending(resolve_context.namespace, value_key, id) {
			self.insert_symbol(
				resolve_context.namespace,
				value_key,
				SymbolKind::Memory {
					memory_index,
					size: kind,
				},
				None,
			);
		}
	}

	/// Reads and validates a `#[memory_limits(min_pages = .., max_pages = ..)]`
	/// attribute off a memory declaration. These are hints, not obligations —
	/// codegen may still bump the emitted initial page count above
	/// `min_pages` when static data requires it — so this only validates the
	/// attribute's own shape, not anything about actual memory usage.
	fn resolve_memory_limits_attribute(
		&mut self,
		file_id: FileId,
		attributes: &[ast::Attribute],
	) -> (Option<u32>, Option<u32>) {
		let mut min_pages: Option<Spanned<u32>> = None;
		let mut max_pages: Option<Spanned<u32>> = None;
		let mut seen = false;

		for attr in attributes {
			if self.interner.resolve(attr.name.inner) != Some("memory_limits") {
				continue;
			}
			if seen {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidMemoryLimitsAttribute.code(),
						)
						.with_message(
							"duplicate `#[memory_limits(...)]` attribute",
						)
						.with_label(
							SourceSpan::new(file_id, attr.name.span)
								.primary_label(),
						),
				);
				continue;
			}
			seen = true;

			let args = match &attr.value {
				ast::AttributeValue::Args(args) => args,
				_ => {
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::InvalidMemoryLimitsAttribute
									.code(),
							)
							.with_message(
								"`#[memory_limits(...)]` requires parenthesized arguments",
							)
							.with_note(
								"example: #[memory_limits(min_pages = 1, max_pages = 10)]",
							)
							.with_label(
								SourceSpan::new(file_id, attr.name.span)
									.primary_label(),
							),
					);
					continue;
				}
			};

			for entry in args.iter() {
				let arg = &entry.inner.inner;
				let arg_name = self.interner.resolve(arg.name.inner).unwrap();
				let slot = match arg_name {
					"min_pages" => &mut min_pages,
					"max_pages" => &mut max_pages,
					_ => {
						self.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::InvalidMemoryLimitsAttribute
										.code(),
								)
								.with_message(format!(
									"unknown `memory_limits` argument `{arg_name}`, expected `min_pages` or `max_pages`"
								))
								.with_label(
									SourceSpan::new(file_id, arg.name.span)
										.primary_label(),
								),
						);
						continue;
					}
				};

				let raw = match &arg.value {
					ast::AttributeArgValue::Int(v) => v,
					ast::AttributeArgValue::String(v) => {
						self.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::InvalidMemoryLimitsAttribute
										.code(),
								)
								.with_message(format!(
									"`{arg_name}` must be an integer"
								))
								.with_label(
									SourceSpan::new(file_id, v.span)
										.primary_label(),
								),
						);
						continue;
					}
				};

				if !(0..=u32::MAX as i64).contains(&raw.inner) {
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::InvalidMemoryLimitsAttribute
									.code(),
							)
							.with_message(format!(
								"`{arg_name}` must fit in a 32-bit unsigned integer"
							))
							.with_label(
								SourceSpan::new(file_id, raw.span)
									.primary_label(),
							),
					);
					continue;
				}

				if slot.is_some() {
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::InvalidMemoryLimitsAttribute
									.code(),
							)
							.with_message(format!(
								"duplicate `{arg_name}` argument"
							))
							.with_label(
								SourceSpan::new(file_id, arg.name.span)
									.primary_label(),
							),
					);
					continue;
				}

				*slot = Some(Spanned {
					inner: raw.inner as u32,
					span: raw.span,
				});
			}
		}

		if let (Some(min), Some(max)) = (&min_pages, &max_pages) {
			if min.inner > max.inner {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidMemoryLimitsAttribute.code(),
						)
						.with_message(format!(
							"`min_pages` ({}) cannot exceed `max_pages` ({})",
							min.inner, max.inner
						))
						.with_label(
							SourceSpan::new(file_id, min.span).primary_label(),
						),
				);
			}
		}

		(min_pages.map(|s| s.inner), max_pages.map(|s| s.inner))
	}

	fn seed_memory_trait_impl_with(
		&mut self,
		trait_index: TraitIndex,
		memory_self: TypeIndex,
		memory_size: Spanned<TypeIndex>,
	) -> HashMap<SymbolU32, ImplEntry> {
		let self_symbol = self.interner.get_or_intern("self");
		let raw_members: Vec<(SymbolU32, ImplEntry)> = self.items.traits
			[usize::from(trait_index)]
		.entries
		.iter()
		.map(|(&sym, entry)| (sym, *entry))
		.collect();
		let mut members: HashMap<SymbolU32, ImplEntry> =
			HashMap::with_capacity(raw_members.len());
		for (sym, entry) in raw_members {
			let processed = match entry {
				ImplEntry::Method(fi) => {
					let func = &self.items.functions[usize::from(fi)];
					if func
						.params
						.first()
						.map(|param| param.name.inner == self_symbol)
						.unwrap_or(false)
					{
						ImplEntry::Method(fi)
					} else {
						ImplEntry::AssocFunction(fi)
					}
				}
				ImplEntry::AssocType(idx) => {
					let original =
						&self.items.assoc_type_impls[usize::from(idx)];
					let new_id = self.id_generator.generate();
					let new_entry = AssocTypeImpl {
						id: new_id,
						file_id: original.file_id,
						namespace: original.namespace,
						name: original.name,
						ty: Some(memory_size),
						attributes: Box::new([]),
					};
					let new_index = self.items.push_assoc_type_impl(new_entry);
					ImplEntry::AssocType(new_index)
				}
				ImplEntry::AssocConstant(index) => {
					// Fork a copy of the template `Constant` with Self
					// (TypeParam at param_index 0) substituted for the
					// concrete memory type. `Constant` can't just be
					// `.clone()`d (its `value` field holds an
					// un-Clone-able `Expression`), but nothing else
					// actually changes here.
					let original_ty =
						self.items.constants[usize::from(index)].ty.inner;
					let concrete_ty =
						self.substitute_type(original_ty, &[memory_self]);
					let c = &self.items.constants[usize::from(index)];
					let new_id = self.id_generator.generate();
					// `value` itself can't be forked (not `Clone` — see
					// above), but `const_value` can: it's what MIR lowering
					// actually reads for a `Memory`-trait const access (see
					// the `NamespaceAccess` handling in `mir::build`), so a
					// default value's already-folded result (e.g.
					// `PAGE_SIZE`'s `Int(65536)`) needs to carry over here
					// or every memory's clone silently loses it, unlike
					// `INDEX`/`DATA_END` (always `None` on the template
					// too, since their values are synthesized by name in
					// MIR instead).
					let const_value = c.const_value;
					let new_constant = Constant {
						id: new_id,
						file_id: c.file_id,
						namespace: c.namespace,
						parent: c.parent,
						pub_span: c.pub_span,
						name: c.name,
						ty: Spanned {
							inner: concrete_ty,
							span: c.ty.span,
						},
						value: None,
						const_value,
						accesses: Vec::new(),
						attributes: Box::new([]),
					};
					let new_index = self.items.push_constant(new_constant);
					ImplEntry::AssocConstant(new_index)
				}
				other => other,
			};
			members.insert(sym, processed);
		}
		members
	}

	pub(super) fn build_deref_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		span: ast::TextSpan,
		pointer: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		// Always build the pointer expression with Read — we only need to read
		// the pointer value itself. Write-through is governed by the pointer type.
		let pointer = self.build_expression(
			func_ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			pointer,
		)?;

		let (inner_ty, memory, mutable) = match self.types.resolve(pointer.ty) {
			Type::Pointer {
				to,
				memory,
				ownership,
			} => (*to, *memory, *ownership == ast::Ownership::Exclusive),
			// Error already reported — absorb it instead of reporting a
			// bogus "`{unknown}` is not a pointer" on top of it. An
			// `ExprKind::Error` rather than `Err(())` so callers keep
			// going and still check what surrounds the deref: an
			// assignment, for instance, goes on to type-check its
			// right-hand side against `{unknown}`.
			Type::Error => {
				return Ok(Expression {
					kind: ExprKind::Error,
					ty: TypeIndex::ERROR,
					span,
				});
			}
			_ => {
				self.diagnostics.push(report_cannot_deref_non_pointer(
					SourceSpan::new(
						func_ctx.resolve_context.file_id,
						pointer.span,
					),
					self.formatter(func_ctx.resolve_context.namespace)
						.display_type(pointer.ty)
						.unwrap(),
				));
				return Err(());
			}
		};

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

		Ok(Expression {
			kind: ExprKind::Load {
				place: Box::new(Place {
					kind: PlaceKind::Deref {
						pointer: Box::new(pointer),
					},
					ty: inner_ty,
					memory,
					mutable,
					span,
				}),
			},
			ty: inner_ty,
			span,
		})
	}

	pub(super) fn resolve_ambient_memory(
		&mut self,
		span: SourceSpan,
	) -> Result<TypeIndex, ()> {
		match self.items.memories.len() {
			0 => {
				self.diagnostics.push(report_no_memory_for_pointer(span));
				Err(())
			}
			1 => {
				// The memory item's own signature may not have run yet if it
				// appears later in the file than this ambient reference (e.g.
				// an `import` block ahead of the `memory` declaration) — its
				// `kind` is a placeholder `TypeIndex::ERROR` until then. Force
				// it now so we intern the same `Type::Memory{ id, kind }` that
				// every other reference to this memory resolves to, instead of
				// a stale, differently-kinded duplicate.
				// A `memory` declaration's own signature resolves from its
				// size expression alone, which cannot mention a memory, so
				// this can never re-enter and the status is always `Resolved`.
				let id = self.items.memories[0].id;
				let _ = self.ensure_signature(id);
				Ok(self.intern_type(Type::Memory {
					id,
					size: self.items.memories[0].size.inner,
				}))
			}
			_ => {
				self.diagnostics.push(report_ambiguous_pointer_memory(span));
				Err(())
			}
		}
	}

	pub(super) fn pointer_type_for_memory(
		&mut self,
		memory: TypeIndex,
	) -> TypeIndex {
		let (owner, param_index) = match self.types.resolve(memory) {
			Type::Memory { id, .. } => {
				let idx = self.items.expect_memory_index(*id);
				return self.items.memories[usize::from(idx)].size.inner;
			}
			Type::TypeParam { owner, param_index } => (owner, param_index),
			_ => return TypeIndex::INTEGER,
		};

		// Generic `M: Memory` — the index type is `M::Size`.
		// Find the first bound trait that declares `Size` as an assoc type.
		let size_sym = self.interner.get_or_intern("Size");
		let trait_index = self
			.items
			.type_param_info(*owner, *param_index as usize)
			.bounds
			.traits
			.iter()
			.find(|b| {
				self.items.traits[usize::from(b.trait_index)]
					.assoc_types
					.contains_key(&size_sym)
			})
			.map(|b| b.trait_index);
		match trait_index {
			Some(trait_index) => self.intern_type(Type::AssocTypeProjection {
				trait_index,
				assoc_name: size_sym,
				base: memory,
			}),
			// No bound with Size — fall back to untyped; will be caught
			// by type checking if the user provides a typed index.
			None => TypeIndex::INTEGER,
		}
	}
}

fn report_invalid_memory_kind(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidMemoryKind.code())
		.with_message("invalid memory kind")
		.with_label(span.primary_label())
		.with_note(
			"expected `Memory where { Size = u32 }` or `Memory where { Size = u64 }`",
		)
}

pub(super) fn report_cannot_store_through_immutable_pointer(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::CannotMutateImmutable.code())
		.with_message("cannot write through a shared reference")
		.with_label(span.primary_label())
		.with_note("consider changing the reference type to `*T`")
}

fn report_cannot_deref_non_pointer(
	span: SourceSpan,
	ty_display: String,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::CannotDerefNonPointer.code())
		.with_message("dereference of non-pointer type")
		.with_label(
			span.primary_label().with_message(format!(
				"type `{}` is not a pointer",
				ty_display
			)),
		)
}

fn report_no_memory_for_pointer(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
        .with_code(DiagnosticCode::NoMemoryForPointer.code())
        .with_message("pointer dereference requires a linear memory")
        .with_label(span.primary_label())
        .with_note("declare a memory in this module: `memory <name>: Memory where { Size = u32 };`")
}

fn report_ambiguous_pointer_memory(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousPointerMemory.code())
		.with_message(
			"pointer dereference is ambiguous: multiple memories defined",
		)
		.with_label(span.primary_label())
		.with_note("specify which memory with `<memory_name>::*T` syntax")
}
