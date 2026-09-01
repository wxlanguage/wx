//! The type pool and type-expression resolution: interning, unification and
//! coercion, resolving a written type expression (including paths, qualified
//! and grouped forms) to a `TypeIndex`, and the direct-recursion check.

use super::*;

impl<'ast> Builder<'ast, '_> {
	pub(super) fn intern_type(&mut self, ty: Type) -> TypeIndex {
		self.types.intern(ty)
	}

	pub(super) fn coercible_to(&mut self, a: TypeIndex, b: TypeIndex) -> bool {
		if a == b
			|| a == TypeIndex::NEVER
			|| a == TypeIndex::ERROR
			|| b == TypeIndex::ERROR
		{
			return true;
		}
		match (self.types.resolve(a), self.types.resolve(b)) {
			// *T coerces to &T (dropping write permission is always safe).
			(
				Type::Pointer {
					to: a_to,
					memory: a_mem,
					ownership: ast::Ownership::Exclusive,
				},
				Type::Pointer {
					to: b_to,
					memory: b_mem,
					ownership: ast::Ownership::Shared,
				},
			) => a_to == b_to && a_mem == b_mem,
			// *[T] coerces to &[T] (dropping write permission is always safe).
			(
				Type::Slice {
					of: a_of,
					memory: a_mem,
					ownership: ast::Ownership::Exclusive,
				},
				Type::Slice {
					of: b_of,
					memory: b_mem,
					ownership: ast::Ownership::Shared,
				},
			) => a_of == b_of && a_mem == b_mem,
			// *[T; N] coerces to &[T; N] (dropping write permission is always safe).
			(
				Type::Array {
					of: a_of,
					size: a_size,
					memory: a_mem,
					ownership: ast::Ownership::Exclusive,
				},
				Type::Array {
					of: b_of,
					size: b_size,
					memory: b_mem,
					ownership: ast::Ownership::Shared,
				},
			) => a_of == b_of && a_size == b_size && a_mem == b_mem,
			// FunctionItem coerces implicitly to its matching Function type.
			(Type::FunctionItem { id, type_args }, Type::Function { .. }) => {
				let func_index =
					usize::from(self.items.expect_function_index(*id));
				let generic_sig =
					self.items.functions[func_index].signature_index;
				self.substitute_type(generic_sig, &type_args.clone()) == b
			}
			_ => false,
		}
	}

	pub(super) fn unify(
		&mut self,
		a: TypeIndex,
		b: TypeIndex,
	) -> Result<TypeIndex, ()> {
		if a == b {
			return Ok(a);
		}
		if a == TypeIndex::NEVER {
			return Ok(b);
		}
		if b == TypeIndex::NEVER {
			return Ok(a);
		}
		if a == TypeIndex::ERROR || b == TypeIndex::ERROR {
			return Ok(TypeIndex::ERROR);
		}
		// Two FunctionItems (generic or not) unify to their common concrete Function
		// type. Handles: `if cond { fn_a } else { fn_b }` and `if cond {
		// f::<i32> } else { g::<i32> }`.
		if let (
			&Type::FunctionItem {
				id: a_id,
				type_args: ref a_args,
			},
			&Type::FunctionItem {
				id: b_id,
				type_args: ref b_args,
			},
		) = (self.types.resolve(a), self.types.resolve(b))
		{
			let a_args = a_args.clone();
			let b_args = b_args.clone();
			let a_sig = self.items.functions
				[usize::from(self.items.expect_function_index(a_id))]
			.signature_index;
			let b_sig = self.items.functions
				[usize::from(self.items.expect_function_index(b_id))]
			.signature_index;
			let concrete_a = self.substitute_type(a_sig, &a_args);
			let concrete_b = self.substitute_type(b_sig, &b_args);
			if concrete_a == concrete_b {
				return Ok(concrete_a);
			}
		}
		Err(())
	}

	/// A type formatter that renders package names as `namespace`'s own
	/// package sees them — a package has no name of its own, so what it's
	/// called depends on who's looking.
	pub(super) fn formatter(
		&self,
		namespace: NamespaceIndex,
	) -> TypeFormatter<'_> {
		TypeFormatter::new(
			&self.types,
			&self.items,
			&self.modules,
			self.interner,
			self.packages,
			self.modules.namespaces[usize::from(namespace)].package,
		)
	}

	pub(super) fn symbol_kind_to_type(
		&mut self,
		kind: SymbolKind,
	) -> Option<TypeIndex> {
		match kind {
			SymbolKind::Memory {
				size: kind,
				memory_index,
			} => {
				let id = self.items.memories[usize::from(memory_index)].id;
				Some(self.intern_type(Type::Memory { size: kind, id }))
			}
			SymbolKind::Module { namespace_idx } => {
				Some(self.intern_type(Type::Namespace { namespace_idx }))
			}
			SymbolKind::Enum { enum_index } => {
				Some(self.intern_type(Type::Enum { enum_index }))
			}
			SymbolKind::Struct { struct_index } => {
				Some(self.intern_type(Type::Struct {
					struct_index,
					args: Box::new([]),
				}))
			}
			SymbolKind::Const { const_index } => {
				let constant = &self.items.constants[usize::from(const_index)];
				Some(constant.ty.inner)
			}
			SymbolKind::Global { global_index } => {
				let global = &self.items.globals[usize::from(global_index)];
				Some(global.ty.inner)
			}
			SymbolKind::Function { func_index } => {
				let function = &self.items.functions[usize::from(func_index)];
				Some(function.signature_index)
			}
			SymbolKind::Trait { .. }
			| SymbolKind::TypeSet { .. }
			| SymbolKind::TraitAssocType { .. } => None,
			SymbolKind::TypeAlias { type_alias_index } => Some(
				self.items.type_aliases[usize::from(type_alias_index)].body,
			),
		}
	}

	/// Resolve a bare identifier symbol to a `TypeIndex`.
	/// Extracted from the `TypeExpression::Identifier` arm so it can be called
	/// directly from path-walking code without constructing AST nodes.
	pub(super) fn resolve_type_identifier(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		identifier: Spanned<SymbolU32>,
		arity: TypeArgArity,
	) -> Result<TypeIndex, ()> {
		if let Some(scope) = scope {
			// Search the owner's own type params first (innermost scope wins).
			let own_params: &[TypeParamInfo] = match scope.owner {
				TypeParamOwner::ImplBlock(block_idx) => {
					&self.items.inherent_impls[usize::from(block_idx)]
						.type_params
				}
				TypeParamOwner::Function(id) => {
					self.items.function_index(id).map_or(&[], |idx| {
						&self.items.functions[usize::from(idx)].type_params
					})
				}
				TypeParamOwner::Struct(id) => {
					self.items.struct_index(id).map_or(&[], |idx| {
						&self.items.structs[usize::from(idx)].type_params
					})
				}
				// `Self` — literally that name (see `self_type_param`), so
				// this is how `Self` resolves for trait consts/assoc-types,
				// whose scope owner is `Trait` directly. Default method
				// bodies reach the same slice via the parent-chase below
				// instead (their own scope owner is `Function`).
				TypeParamOwner::Trait(trait_index) => std::slice::from_ref(
					&self.items.traits[usize::from(trait_index)]
						.self_type_param,
				),
				TypeParamOwner::TraitImpl(impl_idx) => {
					&self.items.trait_impls[usize::from(impl_idx)].type_params
				}
				TypeParamOwner::TypeAlias(id) => {
					self.items.type_alias_index(id).map_or(&[], |idx| {
						&self.items.type_aliases[usize::from(idx)].type_params
					})
				}
			};
			if let Some(own_idx) = own_params
				.iter()
				.position(|p| p.name.inner == identifier.inner)
			{
				let owner = scope.owner;
				let abs_index =
					(self.inherited_type_param_count(owner) + own_idx) as u32;

				self.items
					.type_param_info_mut(owner, abs_index as usize)
					.accesses
					.push(SourceSpan::new(
						resolve_context.file_id,
						identifier.span,
					));
				return Ok(self.intern_type(Type::TypeParam {
					owner,
					param_index: abs_index,
				}));
			}
			// Not found in own params — check the parent impl block (if any).
			if let TypeParamOwner::Function(fn_id) = scope.owner {
				if let Some(fn_idx) = self.items.function_index(fn_id) {
					if let Some(parent_owner) = self.items.functions
						[usize::from(fn_idx)]
					.type_param_parent
					{
						let parent_params =
							self.owner_type_params(parent_owner);
						if let Some(i) = parent_params
							.iter()
							.position(|p| p.name.inner == identifier.inner)
						{
							// ImplBlock has no grandparent, so abs_index == i.
							let abs_index = i as u32;
							self.items
								.type_param_info_mut(
									parent_owner,
									abs_index as usize,
								)
								.accesses
								.push(SourceSpan::new(
									resolve_context.file_id,
									identifier.span,
								));
							return Ok(self.intern_type(Type::TypeParam {
								owner: parent_owner,
								param_index: abs_index,
							}));
						}
					}
				}
			}
		}
		// `Self` as a concrete type — impl blocks and trait impls, where
		// it's the target type directly rather than a type param (the
		// trait case is already handled above, via `own_params`/the
		// parent-chase: `Self` there is literally the trait's
		// `self_type_param` by name). Must stay the resolved type itself,
		// never wrapped in `Type::TypeParam` like the search above does —
		// mono/codegen key off this being the literal `Type::Struct`/
		// `Type::Enum`/etc.
		if self.interner.resolve(identifier.inner) == Some("Self")
			&& let Some(self_ty) = scope.and_then(|s| s.self_type)
		{
			let span =
				SourceSpan::new(resolve_context.file_id, identifier.span);
			// Deliberately not also recorded into the resolved type's own
			// `accesses` — `self_accesses` is `Self`'s only bookkeeping now.
			// Keeping both would make `Self` show up as a
			// `SymbolKind::Struct`/`Enum` reference again in the LSP,
			// defeating the reason it's tracked separately (`Rename` would
			// go back to rewriting the keyword text).
			if let Some(owner) = scope.map(|s| s.owner) {
				self.record_self_keyword_access(owner, span);
			}
			return Ok(self_ty);
		}
		let symbol = match self.resolve_pending_global_symbol(
			resolve_context.namespace,
			(SymbolNamespace::Type, identifier.inner),
			SourceSpan::new(resolve_context.file_id, identifier.span),
		)? {
			Some(symbol) => symbol,
			None => {
				self.diagnostics
					.push(report_undeclared_type(SourceSpan::new(
						resolve_context.file_id,
						identifier.span,
					)));
				return Err(());
			}
		};
		match symbol {
			SymbolKind::TraitAssocType { assoc_name, .. } => {
				let name = self.interner.resolve(assoc_name).unwrap();
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::UndeclaredType.code())
						.with_message(format!(
							"cannot find type `{name}` in this scope",
						))
						.with_label(Label::primary(
							resolve_context.file_id,
							identifier.span,
						))
						.with_note(format!(
							"you might have meant to use the associated type: `Self::{name}`"
						)),
				);
				Err(())
			}
			SymbolKind::Trait { .. } | SymbolKind::TypeSet { .. } => {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::ExpectedBound.code())
						.with_message("cannot use a bound as a type")
						.with_label(Label::primary(
							resolve_context.file_id,
							identifier.span,
						)),
				);
				Err(())
			}
			SymbolKind::Struct { .. } | SymbolKind::TypeAlias { .. } => {
				let ty = self.resolve_generic_type_application(
					resolve_context,
					symbol,
					&[],
					identifier.span,
					arity,
				);
				if ty == TypeIndex::ERROR {
					Err(())
				} else {
					Ok(ty)
				}
			}
			symbol => {
				self.record_symbol_access(
					resolve_context.file_id,
					symbol,
					identifier.span,
				);
				if let Some(ty) = self.symbol_kind_to_type(symbol) {
					return Ok(ty);
				}
				self.diagnostics
					.push(report_undeclared_type(SourceSpan::new(
						resolve_context.file_id,
						identifier.span,
					)));
				Err(())
			}
		}
	}

	/// If `name` names a type parameter reachable from `scope` (its own
	/// owner, or — for a function nested in an impl block — the parent impl
	/// block), returns its absolute index. Mirrors the type-param branch of
	/// [`Self::resolve_type_identifier`] but without any of its resolution
	/// side effects (no interning, no access recording): used purely to
	/// detect type-param/global shadowing before deciding whether turbofish
	/// applies to a global struct/alias.
	fn identifier_type_param_index(
		&self,
		scope: GenericScope,
		name: SymbolU32,
	) -> Option<u32> {
		let own_params: &[TypeParamInfo] = match scope.owner {
			TypeParamOwner::ImplBlock(block_idx) => {
				&self.items.inherent_impls[usize::from(block_idx)].type_params
			}
			TypeParamOwner::Function(id) => {
				self.items.function_index(id).map_or(&[], |idx| {
					&self.items.functions[usize::from(idx)].type_params
				})
			}
			TypeParamOwner::Struct(id) => {
				self.items.struct_index(id).map_or(&[], |idx| {
					&self.items.structs[usize::from(idx)].type_params
				})
			}
			TypeParamOwner::Trait(_) => &[],
			TypeParamOwner::TraitImpl(impl_idx) => {
				&self.items.trait_impls[usize::from(impl_idx)].type_params
			}
			TypeParamOwner::TypeAlias(id) => {
				self.items.type_alias_index(id).map_or(&[], |idx| {
					&self.items.type_aliases[usize::from(idx)].type_params
				})
			}
		};
		if let Some(own_idx) =
			own_params.iter().position(|p| p.name.inner == name)
		{
			return Some(
				(self.inherited_type_param_count(scope.owner) + own_idx) as u32,
			);
		}
		if let TypeParamOwner::Function(fn_id) = scope.owner {
			if let Some(fn_idx) = self.items.function_index(fn_id) {
				if let Some(parent_owner) =
					self.items.functions[usize::from(fn_idx)].type_param_parent
				{
					// ImplBlock has no grandparent, so abs_index == i.
					if let Some(i) = self
						.owner_type_params(parent_owner)
						.iter()
						.position(|p| p.name.inner == name)
					{
						return Some(i as u32);
					}
				}
			}
		}
		None
	}

	/// Like [`resolve_type`], but rejects `_` in positions where a concrete type
	/// is required (item signatures, struct fields, globals). Emits a diagnostic
	/// but still returns the (possibly `Infer`-shaped) resolved type rather than
	/// collapsing it to `ERROR` — this keeps struct/alias identity intact (e.g.
	/// `Arena<_>` instead of `{unknown}`) for callers and diagnostics further
	/// down the line. Safe because compilation aborts on any TIR error before
	/// MIR is ever built, so a lingering `Infer` here can't reach codegen.
	pub(super) fn resolve_signature_type(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		type_expr: &Spanned<ast::TypeExpression>,
	) -> TypeIndex {
		let ty = self.resolve_type(resolve_context, scope, type_expr);
		if self.contains_infer(ty) {
			self.diagnostics
				.push(report_infer_in_signature(SourceSpan::new(
					resolve_context.file_id,
					type_expr.span,
				)));
		}
		ty
	}

	pub fn resolve_type(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		type_expr: &Spanned<ast::TypeExpression>,
	) -> TypeIndex {
		match &type_expr.inner {
			ast::TypeExpression::QualifiedPath { root, segments } => self
				.resolve_qualified_path_type(
					resolve_context,
					scope,
					root,
					segments,
					TypeArgArity::RequireExact,
				),
			ast::TypeExpression::Grouped { inner, segments } => self
				.resolve_grouped_path_type(
					resolve_context,
					scope,
					inner,
					segments,
					TypeArgArity::RequireExact,
				),
			ast::TypeExpression::Infer => TypeIndex::INFER,
			// Every `ast::TypeExpression::Path`, wherever it appears (a fn
			// param, an impl target, a `local` annotation, nested inside
			// `Vec<Pair>`...), is a place with no expression alongside it to
			// unify a gap against later — so type-expression position always
			// requires the full argument count. Writing `_` per slot still
			// works fine here; only *omitting* args is rejected. Contrast
			// [`Self::resolve_path_type`]'s other caller (struct-init,
			// `Wrapper::<T>::method()`), which resolves a raw
			// `&[ast::PathSegment]` in expression/path position and passes
			// `TypeArgArity::AllowInfer` instead.
			ast::TypeExpression::Path(path) => self.resolve_path_type(
				resolve_context,
				scope,
				path,
				type_expr.span,
				TypeArgArity::RequireExact,
			),
			ast::TypeExpression::Function { params, result } => {
				let result_idx = match result {
					Some(result) => {
						self.resolve_type(resolve_context, scope, result)
					}
					None => TypeIndex::UNIT,
				};

				// TODO: use intern_function?
				let params_count = params.len();
				let mut items: Vec<TypeIndex> =
					Vec::with_capacity(params_count + 1);
				for ty in params.iter() {
					items.push(self.resolve_type(
						resolve_context,
						scope,
						&ty.inner.inner.ty,
					));
				}
				items.push(result_idx);
				let items: Box<[TypeIndex]> = items.into();
				self.intern_type(Type::Function {
					signature: FunctionSignature {
						params_count: params_count as u32,
						items,
					},
				})
			}
			ast::TypeExpression::Pointer { ownership, inner } => {
				let to = self.resolve_type(resolve_context, scope, inner);
				let span =
					SourceSpan::new(resolve_context.file_id, type_expr.span);
				let Ok(memory) = self.resolve_ambient_memory(span) else {
					return TypeIndex::ERROR;
				};
				self.intern_type(Type::Pointer {
					to,
					memory,
					ownership: *ownership,
				})
			}
			ast::TypeExpression::Slice { ownership, inner } => {
				let of = self.resolve_type(resolve_context, scope, inner);
				let span =
					SourceSpan::new(resolve_context.file_id, type_expr.span);
				let Ok(memory) = self.resolve_ambient_memory(span) else {
					return TypeIndex::ERROR;
				};
				self.intern_type(Type::Slice {
					of,
					memory,
					ownership: *ownership,
				})
			}
			ast::TypeExpression::Array {
				ownership,
				inner,
				size,
			} => {
				let of = self.resolve_type(resolve_context, scope, inner);
				let span =
					SourceSpan::new(resolve_context.file_id, type_expr.span);
				let Ok(memory) = self.resolve_ambient_memory(span) else {
					return TypeIndex::ERROR;
				};
				self.intern_type(Type::Array {
					of,
					size: size.inner as u32,
					memory,
					ownership: *ownership,
				})
			}
			ast::TypeExpression::Tuple { elements } => {
				if elements.is_empty() {
					return TypeIndex::UNIT;
				}
				let mut elems: Vec<TypeIndex> =
					Vec::with_capacity(elements.len());
				for e in elements.iter() {
					elems.push(self.resolve_type(resolve_context, scope, e));
				}
				self.intern_type(Type::Tuple {
					elements: elems.into(),
				})
			}
			ast::TypeExpression::MemoryTagged { memory, inner } => {
				let first = &memory[0];
				let Ok(mut memory_ty) = self.resolve_type_identifier(
					resolve_context,
					scope,
					first.ident,
					TypeArgArity::RequireExact,
				) else {
					return TypeIndex::ERROR;
				};
				// Walk remaining segments (e.g. `Self::M` has two: `Self`, then `M`).
				let mut namespace_span = first.ident.span;
				for segment in &memory[1..] {
					match self.resolve_namespace_type_member(
						resolve_context,
						scope,
						Spanned {
							inner: memory_ty,
							span: namespace_span,
						},
						segment,
						TypeArgArity::RequireExact,
					) {
						Ok(ty) => {
							memory_ty = ty;
							namespace_span = segment.ident.span;
						}
						Err(()) => return TypeIndex::ERROR,
					}
				}
				match self.types.resolve(memory_ty) {
					Type::Memory { .. }
					| Type::TypeParam { .. }
					| Type::AssocTypeProjection { .. } => {}
					_ => {
						let span = TextSpan::new(
							memory.first().unwrap().ident.span.start,
							memory.last().unwrap().ident.span.end,
						);
						self.diagnostics.push(
							Diagnostic::error()
								.with_message(format!(
									"`{}` is not a memory declaration",
									self.formatter(resolve_context.namespace)
										.display_type(memory_ty)
										.unwrap()
								))
								.with_label(Label::primary(
									resolve_context.file_id,
									span,
								)),
						);
						return TypeIndex::ERROR;
					}
				};
				// Resolve the inner expression directly by AST kind so the outer
				// memory is applied without triggering ambient memory resolution
				// for untagged pointer/array/slice annotations.
				match &inner.inner {
					ast::TypeExpression::Pointer {
						ownership,
						inner: ptr_inner,
					} => {
						let to = self.resolve_type(
							resolve_context,
							scope,
							ptr_inner,
						);
						self.intern_type(Type::Pointer {
							to,
							memory: memory_ty,
							ownership: *ownership,
						})
					}
					ast::TypeExpression::Array {
						ownership,
						inner: arr_inner,
						size,
					} => {
						let of = self.resolve_type(
							resolve_context,
							scope,
							arr_inner,
						);
						self.intern_type(Type::Array {
							of,
							size: size.inner as u32,
							memory: memory_ty,
							ownership: *ownership,
						})
					}
					ast::TypeExpression::Slice {
						ownership,
						inner: sl_inner,
					} => {
						let of =
							self.resolve_type(resolve_context, scope, sl_inner);
						self.intern_type(Type::Slice {
							of,
							memory: memory_ty,
							ownership: *ownership,
						})
					}
					_ => {
						self.diagnostics.push(
							Diagnostic::error()
								.with_message(
									"memory namespace can only prefix pointer, slice, or array types",
								)
								.with_label(Label::primary(
									resolve_context.file_id,
									inner.span,
								)),
						);
						TypeIndex::ERROR
					}
				}
			}
			ast::TypeExpression::GenericApplication { name, args } => {
				if let Some(SymbolEntry::Pending(def_id)) = self
					.lookup_global_symbol_reporting(
						resolve_context.namespace,
						(SymbolNamespace::Type, name.inner),
						SourceSpan::new(resolve_context.file_id, name.span),
					) && self.ensure_signature(def_id) == SignatureStatus::Cycle
				{
					self.report_cyclic_type_dependency(
						def_id,
						SourceSpan::new(resolve_context.file_id, name.span),
					);
					return TypeIndex::ERROR;
				}
				match self
					.lookup_global_symbol(
						resolve_context.namespace,
						(SymbolNamespace::Type, name.inner),
					)
					.and_then(SymbolEntry::resolved_kind)
				{
					Some(
						kind @ (SymbolKind::Struct { .. }
						| SymbolKind::TypeAlias { .. }),
					) => {
						let mut resolved_args: Vec<TypeIndex> =
							Vec::with_capacity(args.len());
						for sep in args.iter() {
							resolved_args.push(self.resolve_type(
								resolve_context,
								scope,
								&sep.inner,
							));
						}
						self.resolve_generic_type_application(
							resolve_context,
							kind,
							&resolved_args,
							name.span,
							TypeArgArity::RequireExact,
						)
					}
					_ => {
						// Not a struct — eagerly resolve args to surface type errors.
						// TODO: fix this weird ast type construction
						for sep in args.iter() {
							self.resolve_type(
								resolve_context,
								scope,
								&sep.inner,
							);
						}
						let base = Spanned {
							inner: ast::TypeExpression::Path(Box::new([
								ast::PathSegment {
									ident: *name,
									type_args: Box::new([]),
								},
							])),
							span: name.span,
						};
						self.resolve_type(resolve_context, scope, &base)
					}
				}
			}
		}
	}

	/// Resolves a `::`-separated path in type position — plain identifiers,
	/// namespaced paths (`module::Type`), and turbofish generic args
	/// (`Wrapper::<T>`, `module::Wrapper::<T>`). Shared by [`Self::resolve_type`]
	/// and struct-init expression resolution, so both spellings of "apply type
	/// args to a struct/alias" go through [`Self::resolve_generic_type_application`].
	pub(super) fn resolve_path_type(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		path: &[ast::PathSegment],
		span: TextSpan,
		arity: TypeArgArity,
	) -> TypeIndex {
		let last = path.last().expect("path is non-empty");

		// ── single segment, no type args: plain identifier ─────────────
		if path.len() == 1 && last.type_args.is_empty() {
			return self
				.resolve_type_identifier(
					resolve_context,
					scope,
					last.ident,
					arity,
				)
				.unwrap_or(TypeIndex::ERROR);
		}

		// ── single segment with turbofish args: `Wrapper::<T>` ─────────
		if path.len() == 1 {
			// A name that shadows a type param in this scope resolves via
			// the type-param scope, not the global symbol table, so it can
			// never carry turbofish args. Checked without a full
			// `resolve_type_identifier` call so a bare generic struct/alias
			// reference below doesn't waste-intern a padded placeholder type.
			if scope.is_some_and(|s| {
				self.identifier_type_param_index(s, last.ident.inner)
					.is_some()
			}) {
				self.diagnostics.push(
					Diagnostic::error()
						.with_message("type arguments are not supported here")
						.with_label(Label::primary(
							resolve_context.file_id,
							span,
						)),
				);
				return TypeIndex::ERROR;
			}
			if let Some(SymbolEntry::Pending(def_id)) = self
				.lookup_global_symbol_reporting(
					resolve_context.namespace,
					(SymbolNamespace::Type, last.ident.inner),
					SourceSpan::new(resolve_context.file_id, last.ident.span),
				) && self.ensure_signature(def_id) == SignatureStatus::Cycle
			{
				self.report_cyclic_type_dependency(
					def_id,
					SourceSpan::new(resolve_context.file_id, last.ident.span),
				);
				return TypeIndex::ERROR;
			}
			let Some(symbol_kind) = self
				.lookup_global_symbol(
					resolve_context.namespace,
					(SymbolNamespace::Type, last.ident.inner),
				)
				.and_then(SymbolEntry::resolved_kind)
			else {
				self.diagnostics.push(
					Diagnostic::error()
						.with_message("type arguments are not supported here")
						.with_label(Label::primary(
							resolve_context.file_id,
							span,
						)),
				);
				return TypeIndex::ERROR;
			};
			let mut resolved_args: Vec<TypeIndex> =
				Vec::with_capacity(last.type_args.len());
			for arg in last.type_args.iter() {
				resolved_args.push(self.resolve_type(
					resolve_context,
					scope,
					arg,
				));
			}
			return self.resolve_generic_type_application(
				resolve_context,
				symbol_kind,
				&resolved_args,
				last.ident.span,
				arity,
			);
		}

		// ── multi-segment: walk namespace chain ────────────────────────
		// TODO: for full LSP per-segment support, ExprKind needs a nested
		// namespace node so each intermediate segment carries its own span and
		// TypeIndex.  Until then each lookup registers only its own segment span.
		let first = &path[0];
		let Ok(mut namespace_ty) = self.resolve_type_identifier(
			resolve_context,
			scope,
			first.ident,
			arity,
		) else {
			return TypeIndex::ERROR;
		};
		let mut namespace_span = first.ident.span;

		for segment in &path[1..path.len() - 1] {
			match self.resolve_namespace_type_member(
				resolve_context,
				scope,
				Spanned {
					inner: namespace_ty,
					span: namespace_span,
				},
				segment,
				arity,
			) {
				Ok(ty) => {
					namespace_ty = ty;
					namespace_span = segment.ident.span;
				}
				Err(()) => return TypeIndex::ERROR,
			}
		}

		// Resolve the last segment (and its turbofish, if any) within the
		// current namespace.
		self.resolve_namespace_type_member(
			resolve_context,
			scope,
			Spanned {
				inner: namespace_ty,
				span: namespace_span,
			},
			last,
			arity,
		)
		.unwrap_or(TypeIndex::ERROR)
	}

	/// Resolves `<Type as Trait>::Item` in type position. Resolves
	/// `root.self_type` and `root.trait_path` the ordinary way, then
	/// resolves `segments[0]` against them via
	/// `resolve_required_trait_member_type`, which looks up exactly the
	/// named trait instead of searching every applicable one — the whole
	/// point of the syntax. Any further segments (rare, but Rust allows
	/// `<T as Trait>::Item::More`) chain through the ordinary unqualified
	/// `resolve_namespace_type_member`, exactly like `resolve_path_type`'s
	/// own multi-segment loop above.
	fn resolve_qualified_path_type(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		root: &ast::QualifiedPathRoot,
		segments: &[ast::PathSegment],
		arity: TypeArgArity,
	) -> TypeIndex {
		let base_ty = Spanned {
			inner: self.resolve_type(resolve_context, scope, &root.self_type),
			span: root.self_type.span,
		};
		let required_trait = match self.resolve_path_segments_as_bound(
			resolve_context,
			&root.trait_path,
			root.span,
		) {
			Ok(BoundKind::Trait(trait_bound)) => trait_bound.trait_index,
			Ok(BoundKind::TypeSet(_)) => {
				self.diagnostics.push(
					Diagnostic::error()
						.with_message(
							"expected a trait after `as`, found a typeset",
						)
						.with_label(Label::primary(
							resolve_context.file_id,
							root.span,
						)),
				);
				return TypeIndex::ERROR;
			}
			Err(()) => return TypeIndex::ERROR,
		};

		let first = &segments[0];
		let mut namespace_ty = match self.resolve_required_trait_member_type(
			resolve_context,
			base_ty,
			required_trait,
			first,
			root.span,
		) {
			Ok(ty) => ty,
			Err(()) => return TypeIndex::ERROR,
		};

		let mut namespace_span = first.ident.span;
		for segment in &segments[1..] {
			match self.resolve_namespace_type_member(
				resolve_context,
				scope,
				Spanned {
					inner: namespace_ty,
					span: namespace_span,
				},
				segment,
				arity,
			) {
				Ok(ty) => {
					namespace_ty = ty;
					namespace_span = segment.ident.span;
				}
				Err(()) => return TypeIndex::ERROR,
			}
		}
		namespace_ty
	}

	/// Resolves `<Type>::Item` in type position — a bare bracketed
	/// self-type with no trait qualification. Structurally identical to
	/// `resolve_path_type`'s multi-segment walk; `inner` just fills the role
	/// the first segment normally plays (which here doesn't have to be a
	/// plain identifier — the whole point of the bracketed form).
	fn resolve_grouped_path_type(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		inner: &ast::Spanned<ast::TypeExpression>,
		segments: &[ast::PathSegment],
		arity: TypeArgArity,
	) -> TypeIndex {
		let base_ty = Spanned {
			inner: self.resolve_type(resolve_context, scope, inner),
			span: inner.span,
		};
		let first = &segments[0];
		let last_arity = if segments.len() == 1 {
			arity
		} else {
			TypeArgArity::AllowInfer
		};
		let mut namespace_ty = match self.resolve_namespace_type_member(
			resolve_context,
			scope,
			base_ty,
			first,
			last_arity,
		) {
			Ok(ty) => ty,
			Err(()) => return TypeIndex::ERROR,
		};

		let mut namespace_span = first.ident.span;
		for segment in &segments[1..] {
			match self.resolve_namespace_type_member(
				resolve_context,
				scope,
				Spanned {
					inner: namespace_ty,
					span: namespace_span,
				},
				segment,
				arity,
			) {
				Ok(ty) => {
					namespace_ty = ty;
					namespace_span = segment.ident.span;
				}
				Err(()) => return TypeIndex::ERROR,
			}
		}
		namespace_ty
	}

	/// Resolves `member` on `base_ty` under exactly `required_trait` — the
	/// type-position half of qualified-path resolution (`<Type as
	/// Trait>::Item`). Unlike `resolve_namespace_type_member`'s ordinary
	/// per-segment resolution (which searches every applicable trait/impl
	/// and reports ambiguity), this looks up exactly the one trait already
	/// named, so ambiguity can't arise. `root_span` covers exactly `<Type as
	/// Trait>` (not including `::member`) — used for the "trait not
	/// implemented" diagnostic, since that's genuinely where the problem is;
	/// "no such member" diagnostics still point at `member` itself.
	pub(super) fn resolve_required_trait_member_type(
		&mut self,
		resolve_context: ResolveContext,
		base_ty: Spanned<TypeIndex>,
		required_trait: TraitIndex,
		member: &ast::PathSegment,
		root_span: TextSpan,
	) -> Result<TypeIndex, ()> {
		if !member.type_args.is_empty() {
			self.diagnostics.push(
				Diagnostic::error()
					.with_message("type arguments are not supported here")
					.with_label(Label::primary(
						resolve_context.file_id,
						member.ident.span,
					)),
			);
			return Err(());
		}

		// `Type::AssocTypeProjection` (e.g. `Mem::Size` in the motivating
		// `<Mem::Size as Unsigned>::Signed` example) is resolved against the
		// bounds *declared on the associated type itself* (`type Size:
		// Memory`) rather than against impls — a different data source than
		// every other case, mirroring `resolve_namespace_type_member`'s own
		// `AssocTypeProjection` arm but filtered to the one trait already
		// named instead of searching every declared bound.
		if matches!(
			self.types.resolve(base_ty.inner),
			Type::AssocTypeProjection { .. }
		) {
			// Check trait membership first, independent of whether the bound
			// below actually holds — whether `required_trait` declares this
			// assoc type is a static fact about the trait itself, not about
			// whether `base_ty` satisfies it, and knowing it lets us recover
			// the intended type even when the bound check fails. Best-effort:
			// in progress means this trait is the one asking, and `entries`
			// holds whatever it has declared so far.
			let _ = self.ensure_signature(
				self.items.traits[usize::from(required_trait)].id,
			);
			let has_member = matches!(
				self.items.traits[usize::from(required_trait)]
					.entries
					.get(&member.ident.inner),
				Some(ImplEntry::AssocType(_))
			);
			if !has_member {
				let member_name =
					self.interner.resolve(member.ident.inner).unwrap();
				let trait_name = self
					.interner
					.resolve(
						self.items.traits[usize::from(required_trait)]
							.name
							.inner,
					)
					.unwrap();
				self.diagnostics.push(report_qualified_path_no_such_type(
					SourceSpan::new(resolve_context.file_id, member.ident.span),
					member_name,
					trait_name,
				));
				return Err(());
			}
			if let Some(assoc_type) = self.items.traits
				[usize::from(required_trait)]
			.assoc_types
			.get_mut(&member.ident.inner)
			{
				assoc_type.accesses.push(SourceSpan::new(
					resolve_context.file_id,
					member.ident.span,
				));
			}
			let recovered = self.intern_type(Type::AssocTypeProjection {
				trait_index: required_trait,
				assoc_name: member.ident.inner,
				base: base_ty.inner,
			});

			// Fetched fresh here (rather than upfront) so this stays a
			// borrow of `self.items` alone, not an owned clone kept alive
			// across the `ensure_signature`/`intern_type` calls above —
			// this is the only place it's used.
			let bound_satisfied = self
				.items
				.abstract_type_bounds(&self.types, base_ty.inner)
				.is_some_and(|bounds| {
					bounds
						.traits
						.iter()
						.any(|b| b.trait_index == required_trait)
				});
			if !bound_satisfied {
				let type_name = self
					.formatter(resolve_context.namespace)
					.display_type(base_ty.inner)
					.unwrap_or_default();
				let trait_name = self
					.interner
					.resolve(
						self.items.traits[usize::from(required_trait)]
							.name
							.inner,
					)
					.unwrap();
				self.diagnostics.push(
					report_qualified_path_trait_not_satisfied(
						SourceSpan::new(resolve_context.file_id, root_span),
						&type_name,
						trait_name,
					),
				);
				// Recovered anyway: we know exactly which trait item was
				// named even though the bound isn't proven, so the type
				// keeps its shape here instead of collapsing to
				// `TypeIndex::ERROR` — hover and any further type-checking
				// in this scope stay useful rather than cascading into
				// unrelated `{unknown}` noise. Matches rustc: an unsatisfied
				// predicate doesn't erase the type it was checked against.
			}
			return Ok(recovered);
		}

		let member_span =
			SourceSpan::new(resolve_context.file_id, member.ident.span);
		match self.resolve_trait_member(
			base_ty.inner,
			required_trait,
			member.ident.inner,
		) {
			Ok((ImplEntry::AssocType(idx), _)) => {
				if let Some(assoc_type) = self.items.traits
					[usize::from(required_trait)]
				.assoc_types
				.get_mut(&member.ident.inner)
				{
					assoc_type.accesses.push(SourceSpan::new(
						resolve_context.file_id,
						member.ident.span,
					));
				}
				// `resolve_trait_member`'s `TypeParam` branch returns the
				// *trait's own abstract declaration* entry (there's no
				// concrete impl to have provided one), which always has
				// `ty: None` — only a concrete-type impl's entry has a
				// real `ty` to unwrap. So for an abstract `base_ty`, build
				// the projection type itself instead, exactly like every
				// other abstract-base case in this file.
				let ty = if self
					.items
					.abstract_type_bounds(&self.types, base_ty.inner)
					.is_some()
				{
					self.intern_type(Type::AssocTypeProjection {
						trait_index: required_trait,
						assoc_name: member.ident.inner,
						base: base_ty.inner,
					})
				} else {
					self.items.assoc_type_impls[usize::from(idx)]
						.ty
						.unwrap()
						.inner
				};
				Ok(ty)
			}
			Ok(_) => {
				// Found a value member (function/const), but this is type
				// position — same diagnostic as "no such type" since a value
				// member isn't a valid answer here either.
				let member_name =
					self.interner.resolve(member.ident.inner).unwrap();
				let trait_name = self
					.interner
					.resolve(
						self.items.traits[usize::from(required_trait)]
							.name
							.inner,
					)
					.unwrap();
				self.diagnostics.push(report_qualified_path_no_such_type(
					member_span,
					member_name,
					trait_name,
				));
				Err(())
			}
			Err(TraitMemberError::NotImplemented) => {
				let type_name = self
					.formatter(resolve_context.namespace)
					.display_type(base_ty.inner)
					.unwrap_or_default();
				let trait_name = self
					.interner
					.resolve(
						self.items.traits[usize::from(required_trait)]
							.name
							.inner,
					)
					.unwrap();
				self.diagnostics.push(
					report_qualified_path_trait_not_satisfied(
						SourceSpan::new(resolve_context.file_id, root_span),
						&type_name,
						trait_name,
					),
				);
				// Same recovery as the `AssocTypeProjection` branch above:
				// `resolve_trait_member` bails before checking membership,
				// but we can check it ourselves — if `required_trait`
				// really does declare this assoc type, keep the type's
				// shape instead of collapsing to `TypeIndex::ERROR`, even
				// though the bound isn't proven. A trait that doesn't
				// define the member at all has nothing to recover.
				// Best-effort, same as the `AssocTypeProjection` branch.
				let _ = self.ensure_signature(
					self.items.traits[usize::from(required_trait)].id,
				);
				match self.items.traits[usize::from(required_trait)]
					.entries
					.get(&member.ident.inner)
				{
					Some(ImplEntry::AssocType(_)) => {
						if let Some(assoc_type) = self.items.traits
							[usize::from(required_trait)]
						.assoc_types
						.get_mut(&member.ident.inner)
						{
							assoc_type.accesses.push(member_span);
						}
						Ok(self.intern_type(Type::AssocTypeProjection {
							trait_index: required_trait,
							assoc_name: member.ident.inner,
							base: base_ty.inner,
						}))
					}
					_ => Err(()),
				}
			}
			Err(TraitMemberError::NoSuchMember) => {
				let member_name =
					self.interner.resolve(member.ident.inner).unwrap();
				let trait_name = self
					.interner
					.resolve(
						self.items.traits[usize::from(required_trait)]
							.name
							.inner,
					)
					.unwrap();
				self.diagnostics.push(report_qualified_path_no_such_type(
					member_span,
					member_name,
					trait_name,
				));
				Err(())
			}
		}
	}

	// TODO: this silently drops unrecognized attribute names/values (the
	// `_ => None` arm below) and never checks whether a resolved attribute
	// is actually valid on the item kind it was attached to (e.g.
	// `#[fixed_order]` on a function, or `#[intrinsic]` on a struct) or
	// whether the same attribute appears more than once on one item.
	// Add validation + diagnostics for unknown attributes, attributes used
	// on the wrong item kind, and duplicates once this needs to be correct
	// rather than best-effort.

	/// Structural compatibility check for type annotations that contain `_` holes.
	/// `expected` is the annotation type (may contain `TypeIndex::INFER`); `actual`
	/// is the inferred type.  INFER positions in `expected` match any type in `actual`.
	/// Used only when `self.contains_infer(expected)` is true.
	pub(super) fn type_satisfies_annotation(
		&self,
		actual: TypeIndex,
		expected: TypeIndex,
	) -> bool {
		if expected == TypeIndex::INFER || actual == expected {
			return true;
		}
		match (self.types.resolve(actual), self.types.resolve(expected)) {
			(
				Type::Struct {
					struct_index: ai,
					args: aa,
				},
				Type::Struct {
					struct_index: bi,
					args: ba,
				},
			) if ai == bi && aa.len() == ba.len() => aa
				.iter()
				.copied()
				.zip(ba.iter().copied())
				.all(|(a, b)| self.type_satisfies_annotation(a, b)),
			(
				Type::Pointer {
					to: at,
					memory: amem,
					ownership: aown,
				},
				Type::Pointer {
					to: bt,
					memory: bmem,
					ownership: bown,
				},
			) => {
				// *T satisfies &T (dropping write permission is safe); the reverse is not.
				!(*aown == ast::Ownership::Shared
					&& *bown == ast::Ownership::Exclusive)
					&& self.type_satisfies_annotation(*at, *bt)
					&& self.type_satisfies_annotation(*amem, *bmem)
			}
			(Type::Tuple { elements: ae }, Type::Tuple { elements: be })
				if ae.len() == be.len() =>
			{
				ae.iter()
					.copied()
					.zip(be.iter().copied())
					.all(|(a, b)| self.type_satisfies_annotation(a, b))
			}
			_ => false,
		}
	}

	/// Returns `true` if `TypeIndex::INFER` appears anywhere in `ty`'s structure.
	/// Used to detect when a generic type parameter was not resolved during inference
	/// and has propagated into the call's result type.
	pub(super) fn contains_infer(&self, ty: TypeIndex) -> bool {
		if ty == TypeIndex::INFER {
			return true;
		}
		match self.types.resolve(ty) {
			Type::Struct { args, .. } => {
				args.iter().copied().any(|a| self.contains_infer(a))
			}
			Type::Pointer { to, memory, .. } => {
				self.contains_infer(*to) || self.contains_infer(*memory)
			}
			Type::Array { of, memory, .. } => {
				self.contains_infer(*of) || self.contains_infer(*memory)
			}
			Type::Slice { of, memory, .. } => {
				self.contains_infer(*of) || self.contains_infer(*memory)
			}
			Type::Tuple { elements } => {
				elements.iter().copied().any(|e| self.contains_infer(e))
			}
			Type::Function { signature } => signature
				.items
				.iter()
				.copied()
				.any(|t| self.contains_infer(t)),
			_ => false,
		}
	}

	/// Returns `true` if a comptime number — the type a literal carries before
	/// anything has pinned it down — appears anywhere in `ty`.
	///
	/// Only tuples are walked, because only a tuple can be *built* out of
	/// literals and still come out with a type. There is no surface syntax
	/// for the comptime types, so any type the user wrote is already
	/// concrete, and every other way to construct an aggregate from literals
	/// is rejected before it produces one: `[1, 2]` demands an annotation of
	/// its own, and inferring a struct's type argument from a bare literal
	/// fails to coerce. A tuple is the one construction that silently keeps
	/// its elements comptime, and it can nest inside itself.
	pub(super) fn contains_comptime_number(&self, ty: TypeIndex) -> bool {
		if ty.is_comptime_number() {
			return true;
		}
		match self.types.resolve(ty) {
			Type::Tuple { elements } => elements
				.iter()
				.copied()
				.any(|e| self.contains_comptime_number(e)),
			_ => false,
		}
	}

	/// Walk `ty` without crossing pointer/slice boundaries and return the span
	/// of the first field whose type directly contains `root_struct_index`.
	/// `visited` prevents re-entering structs already on the walk path.
	fn find_direct_struct_recursion(
		&self,
		ty: TypeIndex,
		root_struct_index: StructIndex,
		visited: &mut Vec<StructIndex>,
	) -> bool {
		match self.types.resolve(ty) {
			Type::Struct { struct_index, .. } => {
				if *struct_index == root_struct_index {
					return true;
				}
				if visited.contains(struct_index) {
					return false;
				}
				visited.push(*struct_index);
				let found = self.items.structs[usize::from(*struct_index)]
					.fields
					.iter()
					.map(|field| field.ty.inner)
					.any(|field_type| {
						self.find_direct_struct_recursion(
							field_type,
							root_struct_index,
							visited,
						)
					});
				visited.pop();
				found
			}
			Type::Tuple { elements } => {
				elements.iter().copied().any(|element| {
					self.find_direct_struct_recursion(
						element,
						root_struct_index,
						visited,
					)
				})
			}
			// Pointer and slice are indirection — stop here.
			Type::Pointer { .. } | Type::Slice { .. } | Type::Array { .. } => {
				false
			}
			_ => false,
		}
	}

	/// Report an error if any field of the struct at `struct_index` directly
	/// (without pointer/slice indirection) contains the struct itself.
	/// Cycles through generic struct instantiation are not detected here; see
	/// the TODO in `mir::Builder::ensure_aggregate_for_struct`.
	pub(super) fn check_struct_fields_for_direct_recursion(
		&mut self,
		struct_index: StructIndex,
		struct_span: SourceSpan,
	) {
		let mut visited = vec![struct_index];
		for (field_ty, field_span) in self.items.structs
			[usize::from(struct_index)]
		.fields
		.iter()
		.map(|field| {
			(
				field.ty.inner,
				SourceSpan::new(
					self.items.structs[usize::from(struct_index)].file_id,
					field.ty.span,
				),
			)
		}) {
			if self.find_direct_struct_recursion(
				field_ty,
				struct_index,
				&mut visited,
			) {
				let name = self
					.interner
					.resolve(
						self.items.structs[usize::from(struct_index)]
							.name
							.inner,
					)
					.unwrap();
				self.diagnostics.push(report_recursive_type(
					name,
					struct_span,
					field_span,
				));
				return;
			}
			visited.truncate(1);
		}
	}
}

fn report_infer_in_signature(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InferInSignature.code())
		.with_message("`_` is not allowed within types on item signatures")
		.with_label(
			span.primary_label()
				.with_message("type must be specified explicitly"),
		)
}

pub(super) fn report_undeclared_type(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredType.code())
		.with_message("undeclared type")
		.with_label(span.primary_label())
}

fn report_recursive_type(
	name: &str,
	struct_span: SourceSpan,
	field_span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::CyclicTypeDependency.code())
		.with_message(format!("recursive type `{name}` has infinite size"))
		.with_label(struct_span.primary_label())
		.with_label(
			field_span
				.secondary_label()
				.with_message("recursive without indirection"),
		)
		.with_note(
			"insert some indirection (e.g. a pointer) to break the cycle",
		)
}
