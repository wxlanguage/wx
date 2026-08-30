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
		let symbol = match self.resolve_pending_global_symbol(
			resolve_context.namespace,
			(SymbolNamespace::Type, identifier.inner),
			SourceSpan::new(file_id, identifier.span),
		)? {
			Some(symbol) => symbol,
			None => {
				self.tir.diagnostics.push(report_undeclared_type(
					SourceSpan::new(file_id, identifier.span),
				));
				return Err(());
			}
		};
		match symbol {
			SymbolKind::Trait { trait_index } => {
				self.tir.traits[trait_index as usize]
					.accesses
					.push(SourceSpan::new(file_id, identifier.span));
				Ok(BoundKind::Trait(TraitBound {
					trait_index,
					bindings: Box::new([]),
					span: full_span,
				}))
			}
			SymbolKind::TypeSet { typeset_index } => {
				self.tir.typesets[typeset_index as usize]
					.accesses
					.push(SourceSpan::new(file_id, identifier.span));
				Ok(BoundKind::TypeSet(TypesetBound {
					typeset_index,
					span: full_span,
				}))
			}
			_ => {
				self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::ExpectedBound.code())
						.with_message("expected bound")
						.with_label(Label::primary(file_id, full_span)),
				);
				Err(())
			}
		}
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
			&self.tir.types[namespace_ty.as_usize()]
		else {
			self.tir.diagnostics.push(
				Diagnostic::error()
					.with_message(
						"expected a module namespace before a bound name",
					)
					.with_label(Label::primary(file_id, namespace_span)),
			);
			return Err(());
		};
		let kind = match self.resolve_pending_namespace_symbol(
			resolve_context.namespace,
			namespace_idx,
			(SymbolNamespace::Type, last.ident.inner),
			SourceSpan::new(file_id, last.ident.span),
		)? {
			Some(kind) => kind,
			None => {
				self.tir.diagnostics.push(report_undeclared_type(
					SourceSpan::new(file_id, last.ident.span),
				));
				return Err(());
			}
		};
		match kind {
			SymbolKind::Trait { trait_index } => {
				self.tir.traits[trait_index as usize]
					.accesses
					.push(SourceSpan::new(file_id, last.ident.span));
				Ok(BoundKind::Trait(TraitBound {
					trait_index,
					bindings: Box::new([]),
					span: full_span,
				}))
			}
			SymbolKind::TypeSet { typeset_index } => {
				self.tir.typesets[typeset_index as usize]
					.accesses
					.push(SourceSpan::new(file_id, last.ident.span));
				Ok(BoundKind::TypeSet(TypesetBound {
					typeset_index,
					span: full_span,
				}))
			}
			_ => {
				self.tir.diagnostics.push(
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
						self.tir.diagnostics.push(
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
						self.tir.diagnostics.push(
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
				// Force the bound trait's own signature — and therefore its
				// members' `assoc_types` entries — to resolve before looking
				// up bindings below. Without this, a trait that hasn't been
				// visited by the main signature-resolution pass yet (e.g. two
				// traits whose assoc-type `where` clauses reference each
				// other, such as `trait A { type X: B where { Y = Self } }`
				// next to `trait B { type Y: A where { X = Self } }`) would
				// have an empty `assoc_types` map here, silently dropping the
				// access instead of recording it. Best-effort, hence the
				// discarded status: in progress means the trait is already
				// resolving further up the stack, and the access is recorded
				// against whatever it has populated by now.
				let _ = self
					.ensure_signature(self.tir.traits[trait_index as usize].id);
				// At most one entry per name — a name is only ever
				// meaningful once per `where { }` block, whether it's
				// written twice the same way (`Size = u32, Size = u64`) or
				// mixed (`Size = u32, Size: Unsigned`, which would otherwise
				// silently let a concrete `Size` also carry an abstract
				// bound requirement alongside it). Only the first occurrence
				// is kept; every later one is diagnosed and dropped rather
				// than resolved — checked directly against this same Vec,
				// since there's only the one list to check against now.
				let mut bindings: Vec<(SymbolU32, AssocBindingKind)> =
					Vec::new();
				for binding in where_bindings.iter() {
					if let Some((_, _)) = bindings
						.iter()
						.find(|(name, _)| *name == binding.name.inner)
					{
						let assoc_name_str =
							self.interner.resolve(binding.name.inner).unwrap();
						self.tir.diagnostics.push(
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
					if let Some(at) = self.tir.traits[trait_index as usize]
						.assoc_types
						.get_mut(&binding.name.inner)
					{
						at.accesses.push(SourceSpan::new(
							resolve_context.file_id,
							binding.name.span,
						));
					}
					match &binding.kind {
						ast::AssocTypeBindingKind::Equals(ty) => {
							let rhs_ty =
								self.resolve_type(resolve_context, scope, ty);
							bindings.push((
								binding.name.inner,
								AssocBindingKind::Equals(rhs_ty),
							));
						}
						ast::AssocTypeBindingKind::Bound(rhs_bound) => {
							let rhs_bounds = self.resolve_bounds(
								resolve_context,
								scope,
								rhs_bound,
							);
							// Merged once, here, rather than every time
							// something later asks what this associated
							// type's bounds are (`abstract_type_bounds`) —
							// this is the one place resolving this `where`
							// clause happens at all, so it's also the only
							// place that needs to know about the trait's own
							// declared bound (`type Size: PointerSize`) to
							// fold it in and check for a conflict.
							let declared = self.tir.traits
								[trait_index as usize]
								.assoc_types
								.get(&binding.name.inner)
								.map(|at| at.bounds.clone())
								.unwrap_or_default();
							let merged_typeset = match (
								declared.typeset,
								rhs_bounds.typeset,
							) {
								(Some(declared_ts), Some(_)) => {
									let assoc_name_str = self
										.interner
										.resolve(binding.name.inner)
										.unwrap();
									let trait_name_str = self
										.interner
										.resolve(
											self.tir.traits
												[trait_index as usize]
												.name
												.inner,
										)
										.unwrap();
									self.tir.diagnostics.push(
										Diagnostic::error()
											.with_code(
												DiagnosticCode::MultipleTypesetBounds
													.code(),
											)
											.with_message(format!(
												"associated type `{assoc_name_str}` already has a typeset bound from `{trait_name_str}`'s own declaration"
											))
											.with_label(
												Label::primary(
													resolve_context.file_id,
													rhs_bound.span,
												)
												.with_message(
													"this `where` clause cannot add another typeset bound",
												),
											)
											.with_label(
												Label::secondary(
													self.tir.traits
														[trait_index as usize]
														.file_id,
													declared_ts.span,
												)
												.with_message(format!(
													"`{assoc_name_str}`'s typeset bound is already declared here"
												)),
											),
									);
									Some(declared_ts)
								}
								(declared_ts, rhs_ts) => declared_ts.or(rhs_ts),
							};
							// A trait bound set is idempotent, same as
							// writing `T: Foo + Foo` — if the `where` clause
							// names a trait the assoc type's own declaration
							// already requires (e.g. `Memory::Size:
							// PointerSize + UnsignedInt` and a function
							// separately writes `where { Size: UnsignedInt
							// }`), that's simply redundant, not a second,
							// distinct bound. Silently drop it rather than
							// keeping a duplicate entry: kept, it would make
							// an unqualified `Mem::Size::Signed` look
							// ambiguous between two "different" candidates
							// that are actually the same trait, and would
							// print as `UnsignedInt + UnsignedInt` on hover.
							let merged = Bounds {
								traits: declared
									.traits
									.iter()
									.cloned()
									.chain(
										rhs_bounds
											.traits
											.iter()
											.filter(|rhs_bound| {
												!declared.traits.iter().any(
													|d| {
														d.trait_index
															== rhs_bound
																.trait_index
													},
												)
											})
											.cloned(),
									)
									.collect::<Vec<_>>()
									.into_boxed_slice(),
								typeset: merged_typeset,
							};
							bindings.push((
								binding.name.inner,
								AssocBindingKind::Bound(merged),
							));
						}
					}
				}
				// Sorted for deterministic equality (see `TraitBound::
				// bindings`'s doc comment) — comparing two `Bounds` (e.g.
				// when checking whether a call site's inferred bound matches
				// a declared one) needs list order to only ever reflect name
				// order, not whatever order the `where` clause happened to
				// be written in.
				bindings.sort_unstable_by_key(|(name, _)| *name);
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
							self.tir.diagnostics.push(
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
		ast_params: &[ast::TypeParam],
	) {
		if ast_params.is_empty() {
			return;
		}
		let offset = self.inherited_type_param_count(owner);
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
			self.tir.type_param_info_mut(owner, offset + i).bounds = resolved;
		}
	}

	/// Returns the type params owned directly by `owner` (not including any
	/// params inherited from a parent impl block).
	pub(super) fn owner_type_params(
		&self,
		owner: TypeParamOwner,
	) -> &[TypeParamInfo] {
		match owner {
			TypeParamOwner::ImplBlock(block_idx) => {
				&self.tir.inherent_impls[block_idx as usize].type_params
			}
			TypeParamOwner::Function(id) => {
				let func_index = self.tir.expect_function_index(id);
				&self.tir.functions[func_index as usize].type_params
			}
			TypeParamOwner::Struct(id) => {
				let struct_index = self.tir.expect_struct_index(id);
				&self.tir.structs[struct_index as usize].type_params
			}
			TypeParamOwner::Trait(trait_index) => std::slice::from_ref(
				&self.tir.traits[trait_index as usize].self_type_param,
			),
			TypeParamOwner::TypeAlias(id) => {
				let alias_index = self.tir.expect_type_alias_index(id);
				&self.tir.type_aliases[alias_index as usize].type_params
			}
			TypeParamOwner::TraitImpl(impl_idx) => {
				&self.tir.trait_impls[impl_idx as usize].type_params
			}
		}
	}

	pub(super) fn inherited_type_param_count(
		&self,
		owner: TypeParamOwner,
	) -> usize {
		match owner {
			TypeParamOwner::Function(id) => {
				self.tir.function_index(id).map_or(0, |idx| {
					self.tir.functions[idx as usize].inherited_type_param_count
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
				let s = &self.tir.structs[struct_index as usize];
				(s.type_params.len(), s.name.inner)
			}
			SymbolKind::TypeAlias { type_alias_index } => {
				let a = &self.tir.type_aliases[type_alias_index as usize];
				(a.type_params.len(), a.name.inner)
			}
			_ => {
				self.tir.diagnostics.push(
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
			self.tir.diagnostics.push(
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
				self.tir.structs[struct_index as usize]
					.accesses
					.push(SourceSpan::new(resolve_context.file_id, span));
				self.intern_type(Type::Struct {
					struct_index,
					args: args.into_boxed_slice(),
				})
			}
			SymbolKind::TypeAlias { type_alias_index } => {
				self.tir.type_aliases[type_alias_index as usize]
					.accesses
					.push(SourceSpan::new(resolve_context.file_id, span));
				let template =
					self.tir.type_aliases[type_alias_index as usize].body;
				self.substitute_type(template, &args)
			}
			_ => unreachable!("filtered above"),
		}
	}

	pub(super) fn substitute_type(
		&mut self,
		ty: TypeIndex,
		type_args: &[TypeIndex],
	) -> TypeIndex {
		match &self.tir.types[ty.as_usize()] {
			// Types that can never contain TypeParams — return immediately.
			Type::Unit
			| Type::Bool
			| Type::Error
			| Type::Infer
			| Type::Never
			| Type::Integer
			| Type::Float
			| Type::I8
			| Type::I16
			| Type::I32
			| Type::I64
			| Type::U8
			| Type::U16
			| Type::U32
			| Type::U64
			| Type::F32
			| Type::F64
			| Type::Char
			| Type::Enum { .. }
			| Type::Namespace { .. }
			| Type::Memory { .. }
			| Type::AssociatedType { .. } => ty,
			Type::TypeParam { param_index, .. } => type_args
				.get(*param_index as usize)
				.copied()
				.filter(|&t| t != TypeIndex::ERROR)
				.unwrap_or(ty),
			Type::AssocTypeProjection {
				base,
				assoc_name,
				trait_index,
			} => {
				let (base, assoc_name, trait_index) =
					(*base, *assoc_name, *trait_index);
				let substituted = self.substitute_type(base, type_args);
				match &self.tir.types[substituted.as_usize()] {
					Type::TypeParam { .. }
					| Type::AssocTypeProjection { .. } => {
						if substituted == base {
							ty
						} else {
							self.intern_type(Type::AssocTypeProjection {
								trait_index,
								assoc_name,
								base: substituted,
							})
						}
					}
					// `Type::Memory` is compiler-synthesized (a `memory`
					// declaration, never a hand-written `impl Memory for
					// ..`), so it never gets a real `TraitImpl` entry the
					// `find_trait_impl` branch below could find — its
					// `Size` is already known directly as a struct field
					// (same fact `pointer_type_for_memory` relies on).
					// Also sidesteps an ordering hazard: this substitution
					// runs from `seed_memory_trait_impl_with`, called
					// *before* the caller registers this memory's real
					// `TraitImpl` — so even a `Type::Memory` impl entry
					// existing wouldn't yet be visible to `find_trait_impl`
					// at this point.
					Type::Memory { size, .. }
						if assoc_name
							== self.interner.get_or_intern("Size") =>
					{
						*size
					}
					// `trait_index` is already known here (it's part of the
					// projection type itself), so go straight to that one
					// impl instead of the ambiguity-scanning
					// `resolve_impl_member` — there's nothing to
					// disambiguate when the trait is already pinned down.
					_ => {
						match self.tir.find_trait_impl(substituted, trait_index)
						{
							Some((impl_idx, impl_type_args)) => {
								match self.tir.trait_impls[impl_idx as usize]
									.members
									.get(&assoc_name)
								{
									Some(ImplEntry::AssocType(idx)) => {
										let concrete = self
											.tir
											.assoc_type_impls[*idx as usize]
											.ty
											.unwrap();
										// The impl's own assoc-type value may
										// reference its own type params (e.g.
										// `impl<T> Trait for Foo<T> { type
										// Assoc = T; }`) — substitute those
										// through the args just inferred from
										// `substituted`.
										self.substitute_type(
											concrete.inner,
											&impl_type_args,
										)
									}
									_ => ty,
								}
							}
							None => {
								// `substituted` can land here either because
								// it's a genuinely concrete type that just
								// doesn't implement `trait_index` (a real,
								// permanent bound failure — the call site's
								// own bound check already reports this; don't
								// hand back the stale pre-substitution
								// projection as if it were valid), or because
								// it's still `INFER`/`ERROR` itself (type-arg
								// inference hasn't finished yet) — that's not
								// a failure, just "not resolved yet," so defer
								// the same way the TypeParam/AssocTypeProjection
								// arm above does.
								if substituted == TypeIndex::INFER
									|| substituted == TypeIndex::ERROR
								{
									ty
								} else {
									TypeIndex::ERROR
								}
							}
						}
					}
				}
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => {
				let (to, memory, ownership) = (*to, *memory, *ownership);
				let next_to = self.substitute_type(to, type_args);
				let next_memory = self.substitute_type(memory, type_args);
				if next_to == to && next_memory == memory {
					ty
				} else {
					self.intern_type(Type::Pointer {
						to: next_to,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Array {
				of,
				size,
				memory,
				ownership,
			} => {
				let (of, size, memory, ownership) =
					(*of, *size, *memory, *ownership);
				let next_of = self.substitute_type(of, type_args);
				let next_memory = self.substitute_type(memory, type_args);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.intern_type(Type::Array {
						of: next_of,
						size,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Slice {
				of,
				memory,
				ownership,
			} => {
				let (of, memory, ownership) = (*of, *memory, *ownership);
				let next_of = self.substitute_type(of, type_args);
				let next_memory = self.substitute_type(memory, type_args);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.intern_type(Type::Slice {
						of: next_of,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Tuple { elements } => {
				let mut changed = false;
				let substituted: Box<[TypeIndex]> = elements
					.clone()
					.iter()
					.copied()
					.map(|element| {
						let next = self.substitute_type(element, type_args);
						changed |= next != element;
						next
					})
					.collect();
				if changed {
					self.intern_type(Type::Tuple {
						elements: substituted,
					})
				} else {
					ty
				}
			}
			Type::Function { signature } => {
				let signature = signature.clone();
				let mut changed = false;
				let items: Box<[TypeIndex]> = signature
					.items
					.iter()
					.copied()
					.map(|item| {
						let next = self.substitute_type(item, type_args);
						changed |= next != item;
						next
					})
					.collect();
				if changed {
					self.intern_type(Type::Function {
						signature: FunctionSignature {
							items,
							params_count: signature.params_count,
						},
					})
				} else {
					ty
				}
			}
			Type::Struct {
				struct_index,
				args: struct_args,
			} => {
				if struct_args.is_empty() {
					return ty;
				}
				let mut changed = false;
				let struct_index = *struct_index;
				let substituted: Box<[TypeIndex]> = struct_args
					.clone()
					.iter()
					.copied()
					.map(|a| {
						let next = self.substitute_type(a, type_args);
						changed |= next != a;
						next
					})
					.collect();
				if changed {
					self.intern_type(Type::Struct {
						struct_index,
						args: substituted,
					})
				} else {
					ty
				}
			}
			Type::FunctionItem {
				id,
				type_args: item_args,
			} => {
				if item_args.is_empty() {
					return ty;
				}
				let mut changed = false;
				let id = *id;
				let substituted: Box<[TypeIndex]> = item_args
					.clone()
					.iter()
					.copied()
					.map(|item_arg| {
						let next = self.substitute_type(item_arg, type_args);
						changed |= next != item_arg;
						next
					})
					.collect();
				if changed {
					self.intern_type(Type::FunctionItem {
						id,
						type_args: substituted,
					})
				} else {
					ty
				}
			}
		}
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
		match &self.tir.types[result.as_usize()] {
			Type::TypeParam { .. }
			| Type::Integer
			| Type::Float
			| Type::Error => TypeIndex::INFER,
			_ => result,
		}
	}

	/// Resolves the concrete value `ty`'s impl of `trait_index` provides for
	/// `assoc_name` — e.g. `ty = u32`, `trait_index = UnsignedInt`,
	/// `assoc_name = Signed` resolves to `i32`. `None` if `ty` doesn't
	/// implement `trait_index` at all, or its impl doesn't (yet) provide
	/// `assoc_name` — a missing-item error already reported separately by
	/// `check_trait_conformance`.
	pub(super) fn concrete_assoc_type_value(
		&mut self,
		ty: TypeIndex,
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
	) -> Option<TypeIndex> {
		let (impl_idx, impl_type_args) =
			self.tir.find_trait_impl(ty, trait_index)?;
		match self.tir.trait_impls[impl_idx as usize]
			.members
			.get(&assoc_name)
			.copied()
		{
			Some(ImplEntry::AssocType(idx)) => {
				let raw = self.tir.assoc_type_impls[idx as usize].ty.unwrap();
				Some(self.substitute_type(raw.inner, &impl_type_args))
			}
			_ => None,
		}
	}

	/// Emits a diagnostic for each bound on `assoc_name` that `concrete_ty`
	/// does not satisfy. `self_ty` is what `Self` refers to in this checking
	/// context — the type that `assoc_name` is *the associated type of*
	/// (e.g. `u8` when checking `impl UnsignedInt for u8`'s `Signed`
	/// binding) — needed to check `where { OtherAssoc = Self }` bindings on
	/// `assoc_name`'s own bounds (e.g. `SignedInt`'s `Unsigned` must equal
	/// `Self`, not just that `concrete_ty: SignedInt`). `error_span` is where
	/// the type was written.
	pub(super) fn check_assoc_type_bounds(
		&mut self,
		resolve_context: ResolveContext,
		trait_index: TraitIndex,
		self_type: TypeIndex,
		name: Spanned<SymbolU32>,
		ty: Spanned<TypeIndex>,
	) {
		let file_id = resolve_context.file_id;
		let Some(bounds) = self.tir.traits[trait_index as usize]
			.assoc_types
			.get(&name.inner)
			.map(|assoc_type| assoc_type.bounds.clone())
		else {
			// TODO: handle unknown associated type
			return;
		};

		for bound in bounds.traits.iter() {
			match self.tir.find_trait_impl(ty.inner, bound.trait_index) {
				Some((impl_idx, impl_type_args)) => {
					// Verify the impl's *actual* value for each binding on
					// `bound` matches what's required — not just that the
					// trait itself is implemented. `Equals` bindings
					// (`where { OtherAssoc = Self }`) check equality against
					// a concrete expected type; `Bound` bindings
					// (`where { OtherAssoc: SomeBound }`) check the actual
					// value against a whole `Bounds`, the same shape of
					// check the call-site enforcement pass does for a direct
					// call (`concrete_assoc_type_value` + the loop below it)
					// — this is that same check, applied at
					// impl-declaration time instead of call time.
					for (binding_name, kind) in bound.bindings.iter() {
						let binding_name = *binding_name;
						let actual = match self.tir.trait_impls
							[impl_idx as usize]
							.members
							.get(&binding_name)
						{
							Some(ImplEntry::AssocType(idx)) => {
								let raw = self.tir.assoc_type_impls
									[*idx as usize]
									.ty
									.unwrap();
								self.substitute_type(raw.inner, &impl_type_args)
							}
							// Missing item is already reported separately by
							// `check_trait_conformance`'s `MissingItem` check.
							_ => continue,
						};
						match kind {
							AssocBindingKind::Equals(expected_ty) => {
								let expected = self.substitute_type(
									*expected_ty,
									&[self_type],
								);
								if expected != actual {
									let assoc_name_str = self
										.interner
										.resolve(name.inner)
										.unwrap();
									let binding_name_str = self
										.interner
										.resolve(binding_name)
										.unwrap();
									let bound_name = self
										.interner
										.resolve(
											self.tir.traits
												[bound.trait_index as usize]
												.name
												.inner,
										)
										.unwrap();
									let fmt = self
										.formatter(resolve_context.namespace);
									let concrete_name = fmt
										.display_type(ty.inner)
										.unwrap_or_default();
									let expected_name = fmt
										.display_type(expected)
										.unwrap_or_default();
									let actual_name = fmt
										.display_type(actual)
										.unwrap_or_default();
									self.tir.diagnostics.push(
										Diagnostic::error()
											.with_code(
												DiagnosticCode::TypeMistmatch
													.code(),
											)
											.with_message(format!(
												"associated type `{assoc_name_str}` = `{concrete_name}` does not satisfy `{bound_name}`'s required binding `{binding_name_str} = {expected_name}`",
											))
											.with_label(
												Label::primary(
													file_id, name.span,
												)
												.with_message(format!(
													"`{concrete_name}::{binding_name_str}` is `{actual_name}`, not `{expected_name}`"
												)),
											),
									);
								}
							}
							AssocBindingKind::Bound(required) => {
								let assoc_name_str =
									self.interner.resolve(name.inner).unwrap();
								let binding_name_str = self
									.interner
									.resolve(binding_name)
									.unwrap();
								let bound_name = self
									.interner
									.resolve(
										self.tir.traits
											[bound.trait_index as usize]
											.name
											.inner,
									)
									.unwrap();
								let fmt =
									self.formatter(resolve_context.namespace);
								let concrete_name = fmt
									.display_type(ty.inner)
									.unwrap_or_default();
								let actual_name = fmt
									.display_type(actual)
									.unwrap_or_default();
								for req_trait in required.traits.iter() {
									if self.tir.type_implements_trait(
										actual,
										req_trait.trait_index,
									) {
										continue;
									}
									let req_trait_name = self
										.interner
										.resolve(
											self.tir.traits[req_trait
												.trait_index
												as usize]
												.name
												.inner,
										)
										.unwrap();
									self.tir.diagnostics.push(
										Diagnostic::error()
											.with_code(
												DiagnosticCode::TraitBoundViolation.code(),
											)
											.with_message(format!(
												"associated type `{assoc_name_str}` = `{concrete_name}` does not satisfy `{bound_name}`'s required bound `{binding_name_str}: {req_trait_name}`",
											))
											.with_label(
												Label::primary(
													file_id, name.span,
												)
												.with_message(format!(
													"`{concrete_name}::{binding_name_str}` is `{actual_name}`, which does not implement `{req_trait_name}`"
												)),
											),
									);
								}
								if let Some(req_typeset) = required.typeset
									&& !self.tir.type_in_typeset(
										actual,
										req_typeset.typeset_index,
									) {
									let set_name = self
										.interner
										.resolve(
											self.tir.typesets[req_typeset
												.typeset_index
												as usize]
												.name
												.inner,
										)
										.unwrap();
									self.tir.diagnostics.push(
										Diagnostic::error()
											.with_code(
												DiagnosticCode::TypesetBoundViolation.code(),
											)
											.with_message(format!(
												"associated type `{assoc_name_str}` = `{concrete_name}` does not satisfy `{bound_name}`'s required bound `{binding_name_str}: {set_name}`",
											))
											.with_label(
												Label::primary(
													file_id, name.span,
												)
												.with_message(format!(
													"`{concrete_name}::{binding_name_str}` is `{actual_name}`, which is not a member of typeset `{set_name}`"
												)),
											),
									);
								}
							}
						}
					}
				}
				None => {
					let assoc_name = self.interner.resolve(name.inner).unwrap();
					let type_name = self
						.formatter(resolve_context.namespace)
						.display_type(ty.inner)
						.unwrap();
					let trait_name = self
						.interner
						.resolve(
							self.tir.traits[bound.trait_index as usize]
								.name
								.inner,
						)
						.unwrap();
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::TraitBoundViolation.code(),
							)
							.with_message(format!(
								"the trait bound `{type_name}: {trait_name}` is not satisfied",
							))
							.with_label(
								Label::primary(file_id, ty.span).with_message(
									format!(
										"the trait `{trait_name}` is not implemented for `{type_name}`"
									),
								),
							)
							.with_label(
								Label::secondary(
									self.tir.traits[trait_index as usize]
										.file_id,
									bound.span,
								)
								.with_message(format!(
									"required by a bound in `{trait_name}::{assoc_name}`"
								)),
							),
					);
				}
			}
		}

		if let Some(typeset) = bounds.typeset
			&& !self
				.tir
				.concrete_type_in_typeset(ty.inner, typeset.typeset_index)
		{
			let typeset_name = self
				.interner
				.resolve(
					self.tir.typesets[typeset.typeset_index as usize]
						.name
						.inner,
				)
				.unwrap();
			let assoc_name = self.interner.resolve(name.inner).unwrap();
			let type_name = self
				.formatter(resolve_context.namespace)
				.display_type(ty.inner)
				.unwrap();
			let trait_name = self
				.interner
				.resolve(self.tir.traits[trait_index as usize].name.inner)
				.unwrap();
			self.tir.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::TypesetBoundViolation.code())
						.with_message(format!(
							"associated type `{assoc_name}` must be a member of typeset `{typeset_name}`",
						))
						.with_label(
							Label::primary(
								file_id,
								name.span,
							).with_message(
								format!("`{type_name}` is not a member of typeset `{typeset_name}`")
							)
						)
						.with_label(
							Label::secondary(
								self.tir.traits[trait_index as usize]
									.file_id,
								typeset.span,
							)
							.with_message(format!(
								"required by a bound in `{trait_name}::{assoc_name}`"
							)),
						),
				);
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
		} = &self.tir.types[ty.as_usize()]
		else {
			return false;
		};
		self.tir.traits[*trait_index as usize]
			.assoc_types
			.get(assoc_name)
			.is_some_and(|a| a.bounds.typeset.is_some())
	}
}
