//! Generics: type parameters and the trait/typeset bounds written on them,
//! substituting concrete arguments into a generic type, and checking that an
//! associated type's value satisfies the bounds its declaration imposes.

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Resolves a single bound name (identifier or `module::name`) directly to a [`BoundKind`]
	/// without going through the type pool.
	fn resolve_identifier_as_bound(
		&mut self,
		resolve_context: ResolveContext,
		identifier: Spanned<SymbolU32>,
		full_span: TextSpan,
	) -> Result<BoundKind, ()> {
		let file_id = resolve_context.file_id;
		let symbol =
			match self.resolve_pending_global_symbol(
				resolve_context.namespace,
				(SymbolNamespace::Type, identifier.inner),
				SourceSpan::new(file_id, identifier.span),
			)? {
				Some(symbol) => symbol,
				None => {
					self.diagnostics.push(report_undeclared_type(
						SourceSpan::new(file_id, identifier.span),
					));
					return Err(());
				}
			};
		match symbol {
			SymbolKind::Trait { trait_index } => {
				self.items.traits[usize::from(trait_index)]
					.accesses
					.push(SourceSpan::new(file_id, identifier.span));
				Ok(BoundKind::Trait(TraitBound {
					trait_index,
					bindings: Box::new([]),
					span: full_span,
				}))
			}
			SymbolKind::TypeSet { typeset_index } => {
				self.items.typesets[usize::from(typeset_index)]
					.accesses
					.push(SourceSpan::new(file_id, identifier.span));
				self.ensure_typeset_members(typeset_index);
				Ok(BoundKind::TypeSet(TypesetBound {
					typeset_index,
					span: full_span,
				}))
			}
			_ => {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::ExpectedBound.code())
						.with_message("expected bound")
						.with_label(Label::primary(file_id, full_span)),
				);
				Err(())
			}
		}
	}

	/// Resolves the members of the typeset a bound just named.
	///
	/// A typeset's symbol is registered *resolved* at prescan, so naming one
	/// never forces its signature the way a `Pending` symbol would — and
	/// `members`/`intersection_range` stay empty until its own node comes up in
	/// the sweep. Every membership check in between then reads an empty set and
	/// reports a perfectly good type as not belonging (E1047), depending on
	/// nothing but declaration order. Forcing it where the bound is built is
	/// what makes `T: Integer` mean the same thing wherever it is written.
	fn ensure_typeset_members(&mut self, typeset_index: TypesetIndex) {
		let def_id = self.items.typesets[usize::from(typeset_index)].id;
		// A cycle would mean this typeset's own declaration named itself;
		// whatever it has resolved so far is all there will ever be.
		let _ = self.ensure_signature(def_id);
	}

	/// Resolves a path (possibly `module::Trait`) to a [`BoundKind`] without touching the
	/// type pool. Intermediate segments are walked as type namespaces; only the final
	/// segment is converted to a bound.
	pub(super) fn resolve_path_segments_as_bound(
		&mut self,
		resolve_context: ResolveContext,
		segs: &[ast::PathSegment],
		full_span: TextSpan,
	) -> Result<BoundKind, ()> {
		debug_assert!(!segs.is_empty());
		if segs.len() == 1 {
			return self.resolve_identifier_as_bound(
				resolve_context,
				segs[0].ident,
				full_span,
			);
		}
		// Walk all but the last segment as type namespaces (modules).
		let first = &segs[0];
		let Ok(mut namespace_ty) = self.resolve_type_identifier(
			resolve_context,
			None,
			first.ident,
			TypeArgArity::RequireExact,
		) else {
			return Err(());
		};
		let mut namespace_span = first.ident.span;
		for seg in &segs[1..segs.len() - 1] {
			match self.resolve_namespace_type_member(
				resolve_context,
				None,
				Spanned {
					inner: namespace_ty,
					span: namespace_span,
				},
				seg,
				TypeArgArity::RequireExact,
			) {
				Ok(ty) => {
					namespace_ty = ty;
					namespace_span = seg.ident.span;
				}
				Err(()) => return Err(()),
			}
		}

		// Final segment: look up the symbol in the final namespace and convert to BoundKind.
		let last = segs.last().unwrap();
		let file_id = resolve_context.file_id;
		let &Type::Namespace { namespace_idx } =
			self.types.resolve(namespace_ty)
		else {
			self.diagnostics.push(
				Diagnostic::error()
					.with_message(
						"expected a module namespace before a bound name",
					)
					.with_label(Label::primary(file_id, namespace_span)),
			);
			return Err(());
		};
		let kind =
			match self.resolve_pending_namespace_symbol(
				resolve_context.namespace,
				namespace_idx,
				(SymbolNamespace::Type, last.ident.inner),
				SourceSpan::new(file_id, last.ident.span),
			)? {
				Some(kind) => kind,
				None => {
					self.diagnostics.push(report_undeclared_type(
						SourceSpan::new(file_id, last.ident.span),
					));
					return Err(());
				}
			};
		match kind {
			SymbolKind::Trait { trait_index } => {
				self.items.traits[usize::from(trait_index)]
					.accesses
					.push(SourceSpan::new(file_id, last.ident.span));
				Ok(BoundKind::Trait(TraitBound {
					trait_index,
					bindings: Box::new([]),
					span: full_span,
				}))
			}
			SymbolKind::TypeSet { typeset_index } => {
				self.items.typesets[usize::from(typeset_index)]
					.accesses
					.push(SourceSpan::new(file_id, last.ident.span));
				self.ensure_typeset_members(typeset_index);
				Ok(BoundKind::TypeSet(TypesetBound {
					typeset_index,
					span: full_span,
				}))
			}
			_ => {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::ExpectedBound.code())
						.with_message(
							"expected a trait or typeset name as a bound",
						)
						.with_label(Label::primary(file_id, last.ident.span)),
				);
				Err(())
			}
		}
	}

	/// Resolves a bound expression into a [`Bounds`], handling `BoundList` (flattening into
	/// multiple trait/typeset entries), `WithBindings` (resolving associated-type bindings),
	/// and plain `Path` bounds. At most one typeset bound is allowed; a second one is an error.
	pub(super) fn resolve_bounds(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		bound: &ast::Spanned<ast::BoundExpression>,
	) -> Bounds {
		match &bound.inner {
			ast::BoundExpression::Path(segs) => {
				match self.resolve_path_segments_as_bound(
					resolve_context,
					segs,
					bound.span,
				) {
					Ok(BoundKind::Trait(trait_bound)) => Bounds {
						traits: Box::new([trait_bound]),
						typeset: None,
					},
					Ok(BoundKind::TypeSet(typeset_bound)) => Bounds {
						traits: Box::new([]),
						typeset: Some(typeset_bound),
					},
					Err(()) => Bounds::default(),
				}
			}
			ast::BoundExpression::WithBindings {
				path,
				bindings: where_bindings,
			} => {
				let segs = match path.as_ref() {
					ast::BoundExpression::Path(segs) => segs,
					_ => {
						self.diagnostics.push(
							Diagnostic::error()
								.with_message(
									"expected a single trait bound here",
								)
								.with_label(Label::primary(
									resolve_context.file_id,
									bound.span,
								)),
						);
						return Bounds::default();
					}
				};
				let trait_index = match self.resolve_path_segments_as_bound(
					resolve_context,
					segs,
					bound.span,
				) {
					Ok(BoundKind::Trait(tb)) => tb.trait_index,
					Ok(BoundKind::TypeSet(typeset)) => {
						self.diagnostics.push(
							Diagnostic::error()
								// TODO: add diagnostic code here
								.with_message(
									"typesets cannot have associated type bindings",
								)
								.with_label(Label::primary(
									resolve_context.file_id,
									bound.span,
								)),
						);
						return Bounds {
							traits: Box::new([]),
							typeset: Some(typeset),
						};
					}
					Err(()) => return Bounds::default(),
				};
				// At most one entry per name — a name is only ever
				// meaningful once per `where { }` block, whether it's
				// written twice the same way (`Size = u32, Size = u64`) or
				// mixed (`Size = u32, Size: Unsigned`, which would otherwise
				// silently let a concrete `Size` also carry an abstract
				// bound requirement alongside it). Only the first occurrence
				// is kept; every later one is diagnosed and dropped rather
				// than resolved — checked directly against this same Vec,
				// since there's only the one list to check against now.
				let mut bindings: Vec<AssocBinding> = Vec::new();
				for binding in where_bindings.iter() {
					if bindings.iter().any(|resolved| {
						resolved.name.inner == binding.name.inner
					}) {
						let assoc_name_str =
							self.interner.resolve(binding.name.inner).unwrap();
						self.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::DuplicateAssocTypeBinding
										.code(),
								)
								.with_message(format!(
									"associated type `{assoc_name_str}` is bound more than once in this `where` clause"
								))
								.with_label(
									Label::primary(
										resolve_context.file_id,
										binding.name.span,
									)
									.with_message("duplicate binding"),
								),
						);
						continue;
					}
					// Identity is usable even while recursive associated bounds are resolving.
					let _ = self.declared_trait_member(
						trait_index,
						binding.name.inner,
						SourceSpan::new(
							resolve_context.file_id,
							binding.name.span,
						),
					);
					if let Some(at) = self.items.trait_associated_type_mut(
						trait_index,
						binding.name.inner,
					) {
						at.accesses.push(SourceSpan::new(
							resolve_context.file_id,
							binding.name.span,
						));
					}
					match &binding.kind {
						ast::AssocTypeBindingKind::Equals(ty) => {
							let rhs_ty =
								self.resolve_type(resolve_context, scope, ty);
							bindings.push(AssocBinding {
								file_id: resolve_context.file_id,
								name: binding.name,
								rhs: Spanned {
									inner: AssocBindingKind::Equals(rhs_ty),
									span: ty.span,
								},
							});
						}
						ast::AssocTypeBindingKind::Bound(rhs_bound) => {
							let rhs_bounds = self.resolve_bounds(
								resolve_context,
								scope,
								rhs_bound,
							);
							bindings.push(AssocBinding {
								file_id: resolve_context.file_id,
								name: binding.name,
								rhs: Spanned {
									inner: AssocBindingKind::Bound(rhs_bounds),
									span: rhs_bound.span,
								},
							});
						}
					}
				}
				// Sorted for deterministic equality (see `TraitBound::
				// bindings`'s doc comment) — comparing two `Bounds` (e.g.
				// when checking whether a call site's inferred bound matches
				// a declared one) needs list order to only ever reflect name
				// order, not whatever order the `where` clause happened to
				// be written in.
				bindings.sort_unstable_by_key(|binding| binding.name.inner);
				Bounds {
					traits: Box::new([TraitBound {
						trait_index,
						bindings: bindings.into_boxed_slice(),
						span: bound.span,
					}]),
					typeset: None,
				}
			}
			ast::BoundExpression::BoundList(items) => {
				let mut traits: Vec<TraitBound> = Vec::new();
				let mut typeset: Option<TypesetBound> = None;
				for item in items.iter() {
					let resolved =
						self.resolve_bounds(resolve_context, scope, item);
					traits.extend_from_slice(&resolved.traits);
					if let Some(ts) = resolved.typeset {
						if typeset.is_some() {
							self.diagnostics.push(
								Diagnostic::error()
									.with_code(
										DiagnosticCode::MultipleTypesetBounds
											.code(),
									)
									.with_message(
										"at most one typeset bound is allowed",
									)
									.with_label(Label::primary(
										resolve_context.file_id,
										item.span,
									)),
							);
						} else {
							typeset = Some(ts);
						}
					}
				}
				Bounds {
					traits: traits.into_boxed_slice(),
					typeset,
				}
			}
		}
	}

	/// Resolves and writes bounds for `ast_params` into the type params already
	/// registered in TIR under `owner`. Must be called after the item is pushed
	/// and its index-lookup entry is inserted.
	///
	/// `self_type` makes `Self` resolvable inside bound expressions for impl
	/// block methods (where `Self` is a concrete type alias, not a type param).
	/// For trait methods `Self` is found via the parent-chain lookup instead.
	///
	/// The offset — how many inherited params precede the first AST param in the
	/// absolute-index space — is read directly from the owner's registered
	/// `inherited_type_param_count` rather than computed by subtraction.
	pub(super) fn resolve_type_param_bounds(
		&mut self,
		resolve_context: ResolveContext,
		owner: TypeParamOwner,
		self_type: Option<TypeIndex>,
		ast_params: &'ast [ast::TypeParam],
	) {
		if ast_params.is_empty() {
			return;
		}
		let offset = self.inherited_type_param_count(owner) as usize;
		for (i, tp) in ast_params.iter().enumerate() {
			let resolved = tp
				.bounds
				.as_ref()
				.map(|b| {
					self.resolve_bounds(
						resolve_context,
						Some(GenericScope { owner, self_type }),
						b,
					)
				})
				.unwrap_or_default();
			let roots: Vec<_> = resolved
				.traits
				.iter()
				.map(|bound| bound.trait_index)
				.collect();
			self.items.type_param_info_mut(owner, offset + i).bounds = resolved;
			for root in roots {
				self.ensure_trait_supertraits(root);
			}
		}
	}

	/// Returns the type params owned directly by `owner` (not including any
	/// params inherited from a parent impl block).
	pub(super) fn owner_type_params(
		&self,
		owner: TypeParamOwner,
	) -> &[TypeParamInfo] {
		match owner {
			TypeParamOwner::InherentImpl(block_idx) => {
				&self.items.inherent_impls[usize::from(block_idx)].type_params
			}
			TypeParamOwner::Function(id) => {
				let func_index = self.items.expect_function_index(id);
				&self.items.functions[usize::from(func_index)].type_params
			}
			TypeParamOwner::Struct(id) => {
				let struct_index = self.items.expect_struct_index(id);
				&self.items.structs[usize::from(struct_index)].type_params
			}
			TypeParamOwner::Trait(trait_index) => std::slice::from_ref(
				&self.items.traits[usize::from(trait_index)].self_type_param,
			),
			TypeParamOwner::TypeAlias(id) => {
				let alias_index = self.items.expect_type_alias_index(id);
				&self.items.type_aliases[usize::from(alias_index)].type_params
			}
			TypeParamOwner::TraitImpl(impl_idx) => {
				&self.items.trait_impls[usize::from(impl_idx)].type_params
			}
		}
	}

	pub(super) fn inherited_type_param_count(
		&self,
		owner: TypeParamOwner,
	) -> u32 {
		match owner {
			TypeParamOwner::Function(id) => {
				self.items.function_index(id).map_or(0, |idx| {
					self.items.functions[usize::from(idx)]
						.inherited_type_param_count
				})
			}
			_ => 0,
		}
	}

	/// Finishes resolving `Alias::<T, U>` / `Alias<T, U>` once the caller has
	/// already resolved the type arguments: checks the count against the
	/// alias's own type params, then substitutes them into the alias's
	/// (possibly `TypeParam`-laden) template via `substitute_type`. Aliases
	/// are transparent: the result is always the substituted target type,
	/// never anything alias-shaped.
	/// Applies type arguments to a generic struct or type alias, used by every
	/// turbofish / `GenericApplication` / bare-reference call site. Providing
	/// more arguments than declared is always an error. Under
	/// [`TypeArgArity::RequireExact`], providing fewer is an error too,
	/// reported immediately here rather than left to pad and be caught later.
	/// Under [`TypeArgArity::AllowInfer`], the count must still be
	/// all-or-nothing: either every argument is given, or none are (padded
	/// entirely with `TypeIndex::INFER` for a later inference step) — a
	/// partial count (some given, some omitted) is rejected rather than
	/// silently inferring only the missing tail, since that's exactly as
	/// unspecified-on-purpose as omitting all of them, just less obviously
	/// so. See [`TypeArgArity`]'s doc comment for which callers use which.
	///
	/// On a mismatch, the struct/alias identity is kept — every arg slot
	/// becomes `TypeIndex::ERROR` rather than the whole result collapsing to
	/// a bare `TypeIndex::ERROR` — so callers further down (field access,
	/// method resolution, other diagnostics) still see e.g. "a `Pair`" and
	/// don't cascade a second, unrelated "not a struct" error on top of this
	/// one.
	pub(super) fn resolve_generic_type_application(
		&mut self,
		resolve_context: ResolveContext,
		symbol_kind: SymbolKind,
		resolved_args: &[TypeIndex],
		span: TextSpan,
		arity: TypeArgArity,
	) -> TypeIndex {
		let (expected, name_sym) = match symbol_kind {
			SymbolKind::Struct { struct_index } => {
				let s = &self.items.structs[usize::from(struct_index)];
				(s.type_params.len(), s.name.inner)
			}
			SymbolKind::TypeAlias { type_alias_index } => {
				let a = &self.items.type_aliases[usize::from(type_alias_index)];
				(a.type_params.len(), a.name.inner)
			}
			_ => {
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
		};
		let mismatched = match arity {
			TypeArgArity::AllowInfer => {
				resolved_args.len() != expected && !resolved_args.is_empty()
			}
			TypeArgArity::RequireExact => resolved_args.len() != expected,
		};
		let args = if mismatched {
			let name = self.interner.resolve(name_sym).unwrap();
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeArgCountMismatch.code())
					.with_message(format!(
						"`{}` expects {} type argument{}, found {}",
						name,
						expected,
						if expected == 1 { "" } else { "s" },
						resolved_args.len(),
					))
					.with_label(Label::primary(resolve_context.file_id, span)),
			);
			vec![TypeIndex::ERROR; expected]
		} else {
			let mut args = resolved_args.to_vec();
			args.resize(expected, TypeIndex::INFER);
			args
		};

		match symbol_kind {
			SymbolKind::Struct { struct_index } => {
				self.items.structs[usize::from(struct_index)]
					.accesses
					.push(SourceSpan::new(resolve_context.file_id, span));
				self.types.intern(Type::Struct {
					struct_index,
					args: args.into_boxed_slice(),
				})
			}
			SymbolKind::TypeAlias { type_alias_index } => {
				self.items.type_aliases[usize::from(type_alias_index)]
					.accesses
					.push(SourceSpan::new(resolve_context.file_id, span));
				let template =
					self.items.type_aliases[usize::from(type_alias_index)].body;
				self.substitute_type(template, &args)
			}
			_ => unreachable!("filtered above"),
		}
	}

	/// The `&mut self` convenience wrapper over [`TypeCtx::substitute_type`],
	/// for the many callers that have the whole `Builder` to hand.
	///
	/// The [`TypeCtx`] is built inline rather than by a `fn type_ctx(&mut
	/// self)` helper, because such a helper borrows all of `self` and so
	/// cannot serve the callers that need field-level control — the bound
	/// checker holds `&self.modules` and `&mut self.diagnostics` alongside
	/// its `TypeCtx`, and trait conformance builds one while walking
	/// `&self.items`. Those construct their own; a shared helper would be
	/// usable by exactly this one caller.
	pub(super) fn substitute_type(
		&mut self,
		ty: TypeIndex,
		type_args: &[TypeIndex],
	) -> TypeIndex {
		TypeCtx {
			types: &mut self.types,
			items: &self.items,
			interner: self.interner,
		}
		.substitute_type(ty, type_args)
	}

	/// Returns the concrete expected type for an argument position, or `None`
	/// if inference hasn't resolved it to a usable type yet. `None` tells the
	/// caller to emit a "type annotation required" diagnostic rather than
	/// attempt coercion against an unknown target.
	pub(super) fn substitute_expected_type(
		&mut self,
		ty: TypeIndex,
		type_args: &[TypeIndex],
	) -> TypeIndex {
		let result = self.substitute_type(ty, type_args);
		match self.types.resolve(result) {
			Type::TypeParam { .. }
			| Type::Integer
			| Type::Float
			| Type::Error => TypeIndex::INFER,
			_ => result,
		}
	}

	/// `true` when `ty` is an `AssocTypeProjection` (e.g. `M::Size` where
	/// `type Size: PointerSize`) whose owning trait declares that
	/// associated type with a typeset bound. Currently all typesets consist
	/// entirely of integer primitives, so any typeset-bounded projection is
	/// unconditionally accepted here.
	/// TODO: re-check each typeset member when non-numeric typesets are added.
	pub(super) fn is_typeset_bounded_assoc_type(&self, ty: TypeIndex) -> bool {
		let Type::AssocTypeProjection {
			trait_index,
			assoc_name,
			..
		} = self.types.resolve(ty)
		else {
			return false;
		};
		self.items
			.trait_associated_type(*trait_index, *assoc_name)
			.is_some_and(|a| a.bounds.typeset.is_some())
	}
}
