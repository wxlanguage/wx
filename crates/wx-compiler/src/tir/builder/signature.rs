//! Phase 2 — signatures. Dispatches each registered item to its own resolver and
//! handles the item kinds that have no slice of their own: structs, type
//! aliases, enums, functions, typesets, globals, consts, `import` declarations
//! and the `export { .. }` block.

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Resolves the signature of `def_id`, and reports whether the result is
	/// usable. Idempotent; detects cycles via `sig_state`.
	///
	/// Must have no early `return` of its own: every path out has to reach
	/// the unwind at the bottom, or `def_id` is left `InProgress` forever and
	/// its `sig_stack` frame is never popped — which would make every later
	/// cycle report name items that finished resolving long ago.
	pub(super) fn ensure_signature(
		&mut self,
		def_id: ast::DefId,
	) -> SignatureStatus {
		let node_idx = {
			let entry = self.sig_state.get_mut(&def_id).unwrap();
			match entry.state {
				ComputeState::Done => return SignatureStatus::Resolved,
				ComputeState::InProgress => return SignatureStatus::Cycle,
				ComputeState::Pending => entry.state = ComputeState::InProgress,
			}
			entry.node_idx
		};
		self.sig_stack.push(def_id);
		let AstEntry {
			file_id,
			namespace,
			node,
			..
		} = self.ast_nodes[node_idx].clone();

		let resolve_context = ResolveContext::new(file_id, namespace);

		match node {
			AstNodeRef::Struct { item } => {
				let (id, name, ast_type_params, fields, pub_span) = match item {
					ast::Item::Struct {
						id,
						name,
						type_params,
						fields,
						pub_span,
						..
					} => (id, name, type_params, fields, pub_span),
					_ => unreachable!(),
				};
				let struct_index = self.tir.expect_struct_index(*id);
				// Bind the name now, before resolving fields, exactly like
				// the pre-refactor code did: this lets a self-referential
				// pointer field (e.g. `*Node`) resolve directly instead of
				// recursing into `ensure_signature` again. Only do this if
				// this occurrence still holds its own `Pending` slot — if
				// an earlier duplicate already claimed the name (or, for a
				// duplicate itself, if it never held the slot to begin
				// with), skip the bind: this struct still gets its fields
				// fully resolved below, it just never becomes referenceable.
				let key = (SymbolNamespace::Type, name.inner);
				if self.still_pending(resolve_context.namespace, key, *id) {
					self.insert_symbol(
						resolve_context.namespace,
						key,
						SymbolKind::Struct { struct_index },
						*pub_span,
					);
				}
				// Resolve bounds now that the struct is registered and names are in TIR.
				self.resolve_type_param_bounds(
					resolve_context,
					TypeParamOwner::Struct(*id),
					None,
					ast_type_params,
				);
				let field_scope = if ast_type_params.is_empty() {
					None
				} else {
					Some(GenericScope {
						owner: TypeParamOwner::Struct(*id),
						self_type: None,
					})
				};

				// Resolve all field types. Referenced structs that haven't been
				// seen yet are pulled in demand-driven via ensure_signature.
				let field_count = fields.len();
				let mut seen_fields: HashMap<SymbolU32, ast::TextSpan> =
					HashMap::with_capacity(field_count);
				let mut tir_fields: Vec<StructField> =
					Vec::with_capacity(field_count);
				let mut field_lookup: HashMap<SymbolU32, FieldIndex> =
					HashMap::with_capacity(field_count);

				for f in fields.iter() {
					let field = &f.inner.inner;
					let sym = field.name.inner;
					if let Some(&first_span) = seen_fields.get(&sym) {
						let fname = self.interner.resolve(sym).unwrap();
						self.tir.diagnostics.push(
							report_duplicate_struct_field(
								fname,
								SourceSpan::new(
									resolve_context.file_id,
									first_span,
								),
								SourceSpan::new(
									resolve_context.file_id,
									field.name.span,
								),
							),
						);
						continue;
					}
					let field_ty = self.resolve_signature_type(
						resolve_context,
						field_scope,
						&field.ty,
					);
					seen_fields.insert(sym, field.name.span);
					let idx = FieldIndex::new(tir_fields.len() as u32);
					field_lookup.insert(sym, idx);
					tir_fields.push(StructField {
						name: field.name,
						ty: Spanned {
							inner: field_ty,
							span: field.ty.span,
						},
						pub_span: field.pub_span,
						accesses: Vec::new(),
					});
				}

				// Fill in the placeholder now that all field types are resolved.
				self.tir.structs[struct_index as usize].fields =
					tir_fields.into_boxed_slice();
				self.tir.structs[struct_index as usize].lookup = field_lookup;

				// Check for direct (non-pointer) self-recursion. Cycles through
				// generic struct instantiation are not caught here — see TODO in
				// mir::Builder::ensure_aggregate_for_struct.
				self.check_struct_fields_for_direct_recursion(
					struct_index,
					SourceSpan::new(resolve_context.file_id, name.span),
				);
			}
			AstNodeRef::TypeAlias { item } => {
				let (id, name, ast_type_params, body_expr, pub_span) =
					match item {
						ast::Item::TypeAlias {
							id,
							name,
							type_params,
							body,
							pub_span,
							..
						} => (id, name, type_params, body, pub_span),
						_ => unreachable!(),
					};
				let type_alias_index = self.tir.expect_type_alias_index(*id);

				// Deliberately NOT calling insert_symbol yet: the symbol table
				// still holds SymbolKind::Pending(*id) while the RHS resolves,
				// so a self-reference (`type A = A;`) hits the InProgress
				// cyclic-dependency guard in resolve_type_identifier instead of
				// resolving through a half-built alias. Aliases are transparent
				// with no indirection to break a cycle, unlike struct fields.
				self.resolve_type_param_bounds(
					resolve_context,
					TypeParamOwner::TypeAlias(*id),
					None,
					ast_type_params,
				);
				let scope = if ast_type_params.is_empty() {
					None
				} else {
					Some(GenericScope {
						owner: TypeParamOwner::TypeAlias(*id),
						self_type: None,
					})
				};
				let template = match body_expr {
					Some(ty_expr) => self.resolve_signature_type(
						resolve_context,
						scope,
						ty_expr,
					),
					// `#[intrinsic] type i8;` etc — bodiless, only legal for
					// the primitives declared in `std/main.wx`. Same trust
					// model as `#[intrinsic]` on functions (see
					// `resolve_attributes`'s doc comment): not validated
					// against the item kind or checked against user modules
					// yet, since only the stdlib we control uses it today.
					None if self.tir.type_aliases
						[type_alias_index as usize]
						.attributes
						.contains(&ItemAttribute::Intrinsic) =>
					{
						Type::try_from(
							self.interner.resolve(name.inner).unwrap(),
						)
						.map(|ty| self.intern_type(ty))
						.unwrap_or(TypeIndex::ERROR)
					}
					None => {
						self.tir.diagnostics.push(
							report_missing_type_alias_body(SourceSpan::new(
								resolve_context.file_id,
								name.span,
							)),
						);
						TypeIndex::ERROR
					}
				};
				self.tir.type_aliases[type_alias_index as usize].body =
					template;

				// Bind the name only if this occurrence still holds its own
				// `Pending` slot — see the identical comment on the Struct
				// branch.
				let key = (SymbolNamespace::Type, name.inner);
				if self.still_pending(resolve_context.namespace, key, *id) {
					self.insert_symbol(
						resolve_context.namespace,
						key,
						SymbolKind::TypeAlias { type_alias_index },
						*pub_span,
					);
				}
			}
			AstNodeRef::Enum { item } => {
				if let ast::Item::Enum {
					id,
					name,
					repr,
					variants,
					pub_span,
					..
				} = item
				{
					let enum_index = self.tir.expect_enum_index(*id);
					self.build_enum(
						resolve_context,
						name,
						repr.as_deref(),
						variants,
						enum_index,
					);

					// Bind the name only if this occurrence still holds its
					// own `Pending` slot — see the identical comment on the
					// Struct branch.
					let key = (SymbolNamespace::Type, name.inner);
					if self.still_pending(resolve_context.namespace, key, *id) {
						self.insert_symbol(
							resolve_context.namespace,
							key,
							SymbolKind::Enum { enum_index },
							*pub_span,
						);
					}
				}
			}
			AstNodeRef::Function { item } => match item {
				ast::Item::Function {
					id,
					signature,
					pub_span,
					..
				}
				| ast::Item::FunctionDeclaration {
					id,
					signature,
					pub_span,
					..
				} => {
					let func_index = self.tir.expect_function_index(*id);
					self.resolve_type_param_bounds(
						resolve_context,
						TypeParamOwner::Function(*id),
						None,
						&signature.type_params,
					);
					let signature_scope = GenericScope {
						owner: TypeParamOwner::Function(*id),
						self_type: None,
					};
					let (params, result) = self.build_function_signature(
						resolve_context,
						Some(signature_scope),
						signature,
					);
					let signature_index = self.intern_function(&params, result);
					let func = &mut self.tir.functions[func_index as usize];
					func.params = params;
					func.result = result;
					func.signature_index = signature_index;

					// Bind the name only if this occurrence still holds its
					// own `Pending` slot — see the identical comment on the
					// Struct branch.
					let key = (SymbolNamespace::Value, signature.name.inner);
					if self.still_pending(resolve_context.namespace, key, *id) {
						self.insert_symbol(
							resolve_context.namespace,
							key,
							SymbolKind::Function { func_index },
							*pub_span,
						);
					}
				}
				_ => {}
			},
			AstNodeRef::InherentImplConst {
				block_id,
				item,
				block_index,
			} => self.signature_inherent_impl_const(
				resolve_context,
				block_id,
				item,
				block_index,
			),
			AstNodeRef::InherentImplFunction {
				block_id,
				item,
				block_index,
			} => self.signature_inherent_impl_function(
				resolve_context,
				block_id,
				item,
				block_index,
			),
			AstNodeRef::InherentImplBlock {
				impl_type_params,
				impl_target,
				block_index,
			} => self.signature_inherent_impl_block(
				resolve_context,
				impl_type_params,
				impl_target,
				block_index,
			),
			AstNodeRef::Trait { trait_index, item } => {
				self.signature_trait(resolve_context, trait_index, item)
			}
			AstNodeRef::TypeSet {
				typeset_index,
				item,
				..
			} => {
				let members = match item {
					ast::Item::TypeSet { members, .. } => members,
					_ => unreachable!(),
				};

				let resolved_members: Box<[TypeIndex]> = members
					.iter()
					.filter_map(|m| {
						let ty =
							self.resolve_type(resolve_context, None, &m.inner);
						if !ty.is_integer() {
							self.tir.diagnostics.push(
								Diagnostic::error()
									.with_code(
										DiagnosticCode::TypesetMemberNotInteger
											.code(),
									)
									.with_message(
										"typeset member must be an integer type",
									)
									.with_label(
										Label::primary(
											resolve_context.file_id,
											m.inner.span,
										)
										.with_message(format!(
											"`{}` is not an integer type",
											self.formatter(
												resolve_context.namespace
											)
											.display_type(ty)
											.unwrap_or_default()
										)),
									),
							);
							None
						} else {
							Some(ty)
						}
					})
					.collect();

				let intersection_range = resolved_members
					.iter()
					.filter_map(|&ty| IntegerRange::for_integer_type(ty))
					.fold(IntegerRange::widest(), IntegerRange::intersect);
				self.tir.typesets[typeset_index as usize].members =
					resolved_members;
				self.tir.typesets[typeset_index as usize].intersection_range =
					intersection_range;
			}
			AstNodeRef::TraitFunction { trait_index, item } => self
				.signature_trait_function(resolve_context, trait_index, item),
			AstNodeRef::TraitConst { trait_index, item } => {
				self.signature_trait_const(resolve_context, trait_index, item)
			}
			AstNodeRef::Global { item } => {
				if let ast::Item::Global {
					name,
					ty,
					id,
					pub_span,
					..
				} = item
				{
					let global_index = self.tir.expect_global_index(*id);
					let (ty_idx, ty_span) = match ty {
						Some(ty) => (
							self.resolve_signature_type(
								resolve_context,
								None,
								ty,
							),
							ty.span,
						),
						None => {
							self.tir.diagnostics.push(
								report_type_annotation_required(
									SourceSpan::new(
										resolve_context.file_id,
										name.span,
									),
								),
							);
							(TypeIndex::ERROR, name.span)
						}
					};
					self.tir.globals[global_index as usize].ty = ast::Spanned {
						inner: ty_idx,
						span: ty_span,
					};

					// Bind the name only if this occurrence still holds its
					// own `Pending` slot — see the identical comment on the
					// Struct branch.
					let key = (SymbolNamespace::Value, name.inner);
					if self.still_pending(resolve_context.namespace, key, *id) {
						self.insert_symbol(
							resolve_context.namespace,
							key,
							SymbolKind::Global { global_index },
							*pub_span,
						);
					}
				}
			}
			AstNodeRef::Memory { item } => {
				self.signature_memory(resolve_context, item)
			}
			AstNodeRef::Constant { item } => {
				if let ast::Item::Const {
					id,
					name,
					ty,
					value,
					pub_span,
					..
				} = item
				{
					let const_index = self.tir.expect_const_index(*id);
					let (ty_idx, ty_span) = match ty {
						Some(ty) => (
							self.resolve_type(resolve_context, None, ty),
							ty.span,
						),
						None => {
							self.tir.diagnostics.push(
								report_type_annotation_required(
									SourceSpan::new(
										resolve_context.file_id,
										name.span,
									),
								),
							);
							(TypeIndex::ERROR, name.span)
						}
					};
					self.tir.constants[const_index as usize].ty =
						ast::Spanned {
							inner: ty_idx,
							span: ty_span,
						};
					// A const whose value fails to build keeps `value: None`
					// and `const_value: None` on its stub — but it still
					// binds its name below, so it stays referenceable.
					if let Ok(value_expr) = self.build_const_context_expression(
						resolve_context,
						value,
						ty_idx,
					) {
						let const_value =
							match self.eval_const_expr(&value_expr) {
								Ok(v) => Some(v),
								Err(_) => {
									self.tir.diagnostics.push(
										report_not_const_evaluatable(
											SourceSpan::new(
												resolve_context.file_id,
												value.span,
											),
										),
									);
									None
								}
							};
						self.tir.constants[const_index as usize].value =
							Some(Box::new(value_expr));
						self.tir.constants[const_index as usize].const_value =
							const_value;
					}

					// Bind the name whether or not the value resolved. Every
					// other item kind binds unconditionally once it holds its
					// own `Pending` slot; a const used to bind only on
					// success, which left the name permanently `Pending` and
					// made the next use of it in value position hit the
					// "signature resolved but symbol still pending"
					// unreachable in `global_symbol_to_expression` — the same
					// hole `register_placeholder_memory` exists to close for
					// `memory` declarations, and with the same trust model:
					// `build_const_context_expression` has already reported
					// why the value failed, and `wx-cli` aborts before
					// `MIR::build` whenever TIR carries any error, so the
					// value-less stub never reaches lowering.
					let key = (SymbolNamespace::Value, name.inner);
					if self.still_pending(resolve_context.namespace, key, *id) {
						self.insert_symbol(
							resolve_context.namespace,
							key,
							SymbolKind::Const { const_index },
							*pub_span,
						);
					}
				}
			}
			AstNodeRef::ImportedFunction {
				import_module_index,
				decl,
				..
			} => {
				if let ast::ImportDeclaration::Function { id, signature } = decl
				{
					let (params, result) = self.build_function_signature(
						resolve_context,
						None,
						signature,
					);
					let signature_index = self.intern_function(&params, result);
					let func_index = self.tir.functions.len() as u32;
					let import_ns_idx = self.tir.import_decls
						[import_module_index as usize]
						.namespace_idx;
					self.tir.functions.push(Function {
						id: *id,
						file_id: resolve_context.file_id,
						namespace: import_ns_idx,
						parent: None,
						signature_index,
						body: None,
						type_params: Box::new([]),
						type_param_parent: None,
						inherited_type_param_count: 0,
						pub_span: None,
						name: signature.name,
						accesses: Vec::new(),
						params,
						result,
						attributes: Box::new([]),
					});
					self.tir
						.item_lookup
						.insert(*id, ItemIndex::Function(func_index));
					let import_decl = &mut self.tir.import_decls
						[import_module_index as usize];
					import_decl.lookup.insert(
						signature.name.inner,
						ImportValue::Function { id: *id },
					);
					let namespace_idx = import_decl.namespace_idx;
					self.tir.namespaces[namespace_idx as usize].symbols.insert(
						(SymbolNamespace::Value, signature.name.inner),
						SymbolEntry::Resolved {
							kind: SymbolKind::Function { func_index },
							visibility: Visibility::Public,
						},
					);
				}
			}
			AstNodeRef::ImportedGlobal {
				import_module_index,
				decl,
				..
			} => {
				if let ast::ImportDeclaration::Global {
					id,
					name,
					ty,
					mut_span,
				} = decl
				{
					let resolved_ty =
						self.resolve_type(resolve_context, None, ty);
					let global_index = self.tir.globals.len() as u32;
					let import_ns_idx = self.tir.import_decls
						[import_module_index as usize]
						.namespace_idx;
					self.tir.globals.push(Global {
						id: *id,
						file_id: resolve_context.file_id,
						namespace: import_ns_idx,
						value: None,
						name: *name,
						ty: ast::Spanned {
							inner: resolved_ty,
							span: ty.span,
						},
						pub_span: None,
						mut_span: *mut_span,
						accesses: Vec::new(),
					});
					self.tir
						.item_lookup
						.insert(*id, ItemIndex::Global(global_index));
					let import_decl = &mut self.tir.import_decls
						[import_module_index as usize];
					import_decl
						.lookup
						.insert(name.inner, ImportValue::Global { id: *id });
					let namespace_idx = import_decl.namespace_idx;
					self.tir.namespaces[namespace_idx as usize].symbols.insert(
						(SymbolNamespace::Value, name.inner),
						SymbolEntry::Resolved {
							kind: SymbolKind::Global { global_index },
							visibility: Visibility::Public,
						},
					);
				}
			}
			AstNodeRef::Use { use_index } => {
				self.resolve_use_item(use_index);
			}
			AstNodeRef::Export { item } => {
				self.signature_export_block(file_id, namespace, item)
			}
			AstNodeRef::TraitImplBlock { item } => {
				self.signature_trait_impl_block(resolve_context, item)
			}
			AstNodeRef::TraitImplFunction { parent_id, item } => self
				.signature_trait_impl_function(
					resolve_context,
					parent_id,
					item,
				),
			AstNodeRef::TraitImplConstant { parent_id, item } => self
				.signature_trait_impl_constant(
					resolve_context,
					parent_id,
					item,
				),
			AstNodeRef::TraitAssocType { trait_index, item } => self
				.signature_trait_assoc_type(resolve_context, trait_index, item),
			AstNodeRef::TraitImplAssocType { parent_id, item } => self
				.signature_trait_impl_assoc_type(
					resolve_context,
					parent_id,
					item,
				),
		}

		self.sig_stack.pop();
		self.sig_state.get_mut(&def_id).unwrap().state = ComputeState::Done;
		SignatureStatus::Resolved
	}

	/// The `export { .. }` arm of [`Self::ensure_signature`], extracted so its
	/// three rejections can stay early `return`s without escaping that
	/// function's unwind.
	fn signature_export_block(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		item: &'ast ast::Item,
	) {
		// The block's own `DefId` is only ever the `ast_nodes` / `sig_state`
		// key that got us here; nothing downstream of resolution refers to a
		// block by id.
		let ast::Item::Export {
			keyword_span,
			entries,
			..
		} = item
		else {
			unreachable!()
		};
		let keyword = SourceSpan::new(file_id, *keyword_span);
		let block_package = self.tir.namespaces[namespace as usize].package;

		// A library has no ABI of its own — it is consumed through `pub`, not
		// through exports. This also catches every block in a dependency,
		// since a dependency is only ever loaded as a library, and "you can't
		// export from here" is the useful thing to say about one: moving the
		// block wouldn't help.
		if matches!(
			self.packages[block_package.as_usize()].kind,
			PackageKind::Library
		) {
			self.tir
				.diagnostics
				.push(report_library_cannot_export(keyword));
			return;
		}

		// The entry file's top level is the only namespace equal to its
		// package's root, so this one comparison rejects both a submodule file
		// and an inline `mod { .. }` block.
		let root_namespace = self.tir.package_namespaces[&self.root_package];
		if namespace != root_namespace {
			self.tir
				.diagnostics
				.push(report_export_block_not_at_root(keyword));
			return;
		}

		// The single `Option` that stores a block's exports is also what
		// proves no earlier block exists, so the two can't disagree. Note that
		// every rejection above returns *before* this point: a misplaced block
		// must not claim the slot, or the package's real block would be
		// reported as the duplicate of one that was itself rejected.
		if let Some(existing) = &self.tir.export_block {
			self.tir
				.diagnostics
				.push(report_duplicate_export_block(existing.keyword, keyword));
			return;
		}

		// `export { .. }` is a top-level item, so the names it lists resolve
		// against the package's own root namespace and no wider one.
		let items = self.build_exports(file_id, root_namespace, entries);
		self.tir.export_block = Some(ExportBlock { keyword, items });
	}

	/// Resolves a signature's params and result. When `scope.self_type` is
	/// `Some` (method-shaped signatures — `ImplBlockFunction`, `TraitFunction`,
	/// `ImplTraitFunction`), a `self`-named param is additionally validated to
	/// have type `Self`/`*Self` (or defaulted to `Self` if untyped); plain
	/// functions (`scope: None` or `self_type: None`) skip that entirely.
	pub(super) fn build_function_signature(
		&mut self,
		resolve_context: ResolveContext,
		scope: Option<GenericScope>,
		signature: &ast::FunctionSignature,
	) -> (Box<[FunctionParam]>, Option<Spanned<TypeIndex>>) {
		let self_type = scope.and_then(|s| s.self_type);
		let self_symbol = self.interner.get_or_intern("self");
		let mut seen_params: HashMap<SymbolU32, ast::TextSpan> = HashMap::new();
		let mut params: Vec<FunctionParam> =
			Vec::with_capacity(signature.params.len());
		for param in signature.params.iter() {
			let name = param.inner.inner.name;
			if let Some(first_span) = seen_params.get(&name.inner).copied() {
				let name_str = self.interner.resolve(name.inner).unwrap();
				self.tir.diagnostics.push(report_duplicate_parameter(
					name_str,
					SourceSpan::new(resolve_context.file_id, first_span),
					SourceSpan::new(resolve_context.file_id, name.span),
				));
			} else {
				seen_params.insert(name.inner, name.span);
			}
			let ty = match &param.inner.inner.ty {
				Some(ty) => {
					let resolved =
						self.resolve_signature_type(resolve_context, scope, ty);
					if let Some(self_type) = self_type
						&& name.inner == self_symbol
					{
						let valid_self_type = resolved == self_type
							|| matches!(
								&self.tir.types[resolved.as_usize()],
								Type::Pointer { to, .. } if *to == self_type
							);
						if !valid_self_type {
							self.tir.diagnostics.push(
								report_invalid_self_type(
									SourceSpan::new(
										resolve_context.file_id,
										ty.span,
									),
									self.formatter(resolve_context.namespace),
									resolved,
								),
							);
						}
					}
					Spanned {
						inner: resolved,
						span: ty.span,
					}
				}
				None => Spanned {
					inner: if let Some(self_type) = self_type
						&& name.inner == self_symbol
					{
						self_type
					} else {
						TypeIndex::ERROR
					},
					span: name.span,
				},
			};
			params.push(FunctionParam {
				mut_span: param.inner.inner.mut_span,
				name,
				ty,
			});
		}
		let result = signature.result.as_ref().map(|result| Spanned {
			inner: self.resolve_signature_type(resolve_context, scope, result),
			span: result.span,
		});

		(params.into_boxed_slice(), result)
	}

	pub(super) fn resolve_attributes(
		&mut self,
		id: DefId,
		attributes: &[ast::Attribute],
	) -> Box<[ItemAttribute]> {
		attributes
			.iter()
			.filter_map(|a| {
				match (&a.value, self.interner.resolve(a.name.inner)) {
					(ast::AttributeValue::Word, Some("inline")) => {
						Some(ItemAttribute::Inline)
					}
					(ast::AttributeValue::Word, Some("intrinsic")) => {
						Some(ItemAttribute::Intrinsic)
					}
					(ast::AttributeValue::Word, Some("fixed_order")) => {
						Some(ItemAttribute::FixedOrder)
					}
					(ast::AttributeValue::NameValue(value), Some("tag")) => {
						let raw = self.interner.resolve(value.inner).unwrap();
						let key =
							self.interner.get_or_intern(unescape_string(raw));
						self.tir.tagged_items.insert(key, id);
						Some(ItemAttribute::Tag(key))
					}
					_ => None,
				}
			})
			.collect()
	}

	/// Resolves an enum's repr type, folds every variant's value (explicit or
	/// auto-incremented) to a `ConstValue`, range-checks it against the repr, and
	/// reports one grouped diagnostic per set of variants that collide on the same
	/// value. Writes `ty`/`variants`/`lookup` directly onto `self.tir.enums[enum_index]`.
	fn build_enum(
		&mut self,
		resolve_context: ResolveContext,
		name: &ast::Spanned<SymbolU32>,
		repr_type: Option<&ast::Spanned<ast::TypeExpression>>,
		ast_variants: &[ast::Separated<ast::Spanned<ast::EnumVariant>>],
		enum_index: EnumIndex,
	) {
		let repr_type = match repr_type {
			Some(repr_type) => {
				let resolved =
					self.resolve_type(resolve_context, None, repr_type);
				if resolved != TypeIndex::ERROR && !resolved.is_integer() {
					self.tir.diagnostics.push(report_enum_repr_not_integer(
						self.formatter(resolve_context.namespace),
						resolved,
						SourceSpan::new(
							resolve_context.file_id,
							repr_type.span,
						),
					));
					TypeIndex::ERROR
				} else {
					resolved
				}
			}
			None => {
				self.tir.diagnostics.push(report_missing_enum_repr(
					SourceSpan::new(resolve_context.file_id, name.span),
				));
				TypeIndex::ERROR
			}
		};
		let ty_range = IntegerRange::for_integer_type(repr_type);

		let mut variants: Vec<EnumVariant> =
			Vec::with_capacity(ast_variants.len());
		let mut variant_lookup: HashMap<SymbolU32, EnumVariantIndex> =
			HashMap::with_capacity(variants.len());
		// `None` until some variant provides a known value to continue
		// from — either an explicit `= <value>` that actually evaluated,
		// or a prior implicit variant that itself continued from one. An
		// implicit variant reached while this is still `None` has nothing
		// to anchor to, which is an error (see the `None` arm below)
		// rather than a silent `0`-based default.
		let mut next_auto_value: Option<i64> = None;

		for ast_variant in ast_variants.iter().map(|v| &v.inner.inner) {
			if let Some(first_index) =
				variant_lookup.get(&ast_variant.name.inner).copied()
			{
				let first_span = variants[first_index as usize].name.span;
				let vname =
					self.interner.resolve(ast_variant.name.inner).unwrap();
				self.tir.diagnostics.push(report_duplicate_definition(
					DuplicateDefinitionDiagnostic {
						name: vname,
						namespace: SymbolNamespace::Value,
						first_definition: SourceSpan::new(
							resolve_context.file_id,
							first_span,
						),
						second_definition: SourceSpan::new(
							resolve_context.file_id,
							ast_variant.name.span,
						),
					},
				));
				continue;
			}

			let (value, const_value) = match &ast_variant.value {
				// `repr_type` is `ERROR` only because it already failed to
				// resolve (missing or non-integer repr) — that's reported
				// once on the enum itself, so don't also try to type-check
				// every variant's value against it and cascade into
				// "unable to coerce"/"type annotation required" per variant.
				Some(_) if repr_type == TypeIndex::ERROR => (None, None),
				Some(value_expr) => {
					match self.build_const_context_expression(
						resolve_context,
						value_expr,
						repr_type,
					) {
						Ok(expr) => {
							let value = match self.eval_const_expr(&expr) {
								Ok(ConstValue::Int(v)) => Some(v),
								Ok(_) => None,
								Err(_) => {
									self.tir.diagnostics.push(
										report_not_const_evaluatable(
											SourceSpan::new(
												resolve_context.file_id,
												value_expr.span,
											),
										),
									);
									None
								}
							};
							(Some(Box::new(expr)), value)
						}
						Err(_) => (None, None),
					}
				}
				None => match next_auto_value {
					Some(v) => {
						if let Some(ref range) = ty_range
							&& !range.contains(v)
						{
							self.tir.diagnostics.push(
								report_integer_literal_out_of_range(
									self.formatter(resolve_context.namespace),
									IntegerLiteralOutOfRangeDiagnostic {
										ty: repr_type,
										value: v,
										span: SourceSpan::new(
											resolve_context.file_id,
											ast_variant.name.span,
										),
									},
								),
							);
						}
						(None, Some(v))
					}
					// Nothing above this variant established a value to
					// continue from — same "already reported once on the
					// enum itself" cascade guard as the `Some(_) if
					// repr_type == TypeIndex::ERROR` arm above.
					None => {
						if repr_type != TypeIndex::ERROR {
							self.tir.diagnostics.push(
								report_enum_variant_requires_explicit_value(
									SourceSpan::new(
										resolve_context.file_id,
										ast_variant.name.span,
									),
								),
							);
						}
						(None, None)
					}
				},
			};
			next_auto_value = const_value.map(|v| v.wrapping_add(1));

			let variant_index = variants.len() as EnumVariantIndex;
			variant_lookup.insert(ast_variant.name.inner, variant_index);
			variants.push(EnumVariant {
				name: ast_variant.name,
				value,
				const_value: const_value.map(ConstValue::Int),
				accesses: Vec::new(),
			});
		}

		self.report_enum_duplicate_values(
			resolve_context,
			name.span,
			&variants,
		);

		let enumeration = &mut self.tir.enums[enum_index as usize];
		enumeration.repr_type = repr_type;
		enumeration.variants = variants.into_boxed_slice();
		enumeration.variant_lookup = variant_lookup;
	}

	/// Reports one grouped diagnostic per set of variants that share the same
	/// discriminant value (rustc's `E0081`-style grouping, primary label on
	/// the enum name, one secondary label per colliding variant).
	///
	/// Runs as a single pass over the already-built `tir_variants` rather than
	/// accumulating a `HashMap<i64, Vec<SourceSpan>>` while folding: that would
	/// allocate a `Vec` for every *unique* value, even though the overwhelming
	/// majority of enums have no collisions at all and every such `Vec` would
	/// just be thrown away. Sorting by value once and scanning for runs keeps
	/// the common (no-duplicates) case to a single flat allocation.
	fn report_enum_duplicate_values(
		&mut self,
		resolve_context: ResolveContext,
		enum_name_span: ast::TextSpan,
		tir_variants: &[EnumVariant],
	) {
		let mut by_value: Vec<(i64, &EnumVariant)> = tir_variants
			.iter()
			.filter_map(|variant| match variant.const_value {
				Some(ConstValue::Int(value)) => Some((value, variant)),
				_ => None,
			})
			.collect();
		by_value.sort_unstable_by_key(|(value, _)| *value);

		let mut duplicate_groups: Vec<(i64, Vec<SourceSpan>)> = Vec::new();
		let mut i = 0;
		while i < by_value.len() {
			let mut j = i + 1;
			while j < by_value.len() && by_value[j].0 == by_value[i].0 {
				j += 1;
			}
			if j - i > 1 {
				let spans = by_value[i..j]
					.iter()
					.map(|(_, variant)| {
						// Auto-incremented variants have no explicit
						// expression (see `build_enum`) — point at the
						// variant's name instead.
						let span = variant
							.value
							.as_deref()
							.map_or(variant.name.span, |expr| expr.span);
						SourceSpan::new(resolve_context.file_id, span)
					})
					.collect();
				duplicate_groups.push((by_value[i].0, spans));
			}
			i = j;
		}

		// Grouping above is ordered by value, not by where it appears in
		// source — re-sort just the (typically few) colliding groups by their
		// earliest span so diagnostics come out in source order.
		duplicate_groups
			.sort_by_key(|(_, spans)| spans.iter().map(|s| s.span.start).min());
		for (value, spans) in &duplicate_groups {
			self.tir.diagnostics.push(report_enum_duplicate_value(
				SourceSpan::new(resolve_context.file_id, enum_name_span),
				*value,
				spans,
			));
		}
	}

	/// `package_namespace` is the exporting package's own root namespace —
	/// `export { .. }` is a top-level item, so the names it lists are
	/// resolved against exactly that scope and no wider one.
	fn build_exports(
		&mut self,
		file_id: FileId,
		package_namespace: NamespaceIndex,
		entries: &[Separated<Spanned<ast::ExportEntry>>],
	) -> HashMap<SymbolU32, ExportItem> {
		let mut items: HashMap<SymbolU32, ExportItem> = HashMap::new();
		for entry in entries.iter() {
			let internal_name = &entry.inner.inner.name;

			let span = SourceSpan::new(file_id, internal_name.span);
			// Force the listed name through `ensure_signature` rather than
			// reading whatever happens to be resolved already: an export
			// block is just another reference site, so it pulls in what it
			// names the same way any other reference does.
			//
			// And it resolves through the *scope chain*, not the package
			// root's own symbol map, so an entry names whatever that name
			// means at the root — including something a `use` put there.
			// A direct map lookup made every submodule item unexportable by
			// any spelling at all: `use math::add; export { add }` would
			// resolve `add` for every other reference site in the file and
			// then fail here alone.
			let Ok(value_symbol) = self.resolve_pending_global_symbol(
				package_namespace,
				(SymbolNamespace::Value, internal_name.inner),
				span,
			) else {
				continue;
			};
			let global_value = match value_symbol {
				Some(value) => value,
				None => {
					// Not a value, but it might still name a real item that
					// simply isn't exportable (an enum, struct, trait, ...) —
					// report the more precise diagnostic instead of treating
					// it as an unresolved name. Still record the access so
					// the LSP can resolve hover/go-to-definition on it.
					if let Ok(Some(type_value)) = self
						.resolve_pending_global_symbol(
							package_namespace,
							(SymbolNamespace::Type, internal_name.inner),
							span,
						) {
						self.tir.record_symbol_access(
							file_id,
							type_value,
							internal_name.span,
						);
						self.tir.diagnostics.push(report_cannot_export_item(
							self.interner.resolve(internal_name.inner).unwrap(),
							SourceSpan::new(file_id, internal_name.span),
						));
					} else {
						self.tir.diagnostics.push(
							report_undeclared_identifier(SourceSpan::new(
								file_id,
								internal_name.span,
							)),
						);
					}
					continue;
				}
			};

			let external_name =
				entry.inner.inner.alias.as_ref().map(|alias_span| {
					let escaped_text =
						self.interner.resolve(alias_span.inner).unwrap();
					let unescaped = unescape_string(escaped_text);
					let symbol = self.interner.get_or_intern(&unescaped);
					ast::Spanned {
						inner: symbol,
						span: alias_span.span,
					}
				});

			let export_item = match global_value {
				SymbolKind::Function { func_index } => {
					if self.tir.functions[func_index as usize]
						.total_type_param_count()
						> 0
					{
						self.tir.functions[func_index as usize]
							.accesses
							.push(SourceSpan::new(file_id, internal_name.span));
						self.tir.diagnostics.push(
							report_cannot_export_generic_function(
								self.interner
									.resolve(internal_name.inner)
									.unwrap(),
								SourceSpan::new(file_id, internal_name.span),
							),
						);
						continue;
					}

					self.tir.functions[func_index as usize]
						.accesses
						.push(SourceSpan::new(file_id, internal_name.span));

					ExportItem::Function {
						id: self.tir.functions[func_index as usize].id,
						internal_name: *internal_name,
						external_name,
					}
				}
				SymbolKind::Global { global_index } => {
					self.tir.globals[global_index as usize]
						.accesses
						.push(SourceSpan::new(file_id, internal_name.span));

					ExportItem::Global {
						id: self.tir.globals[global_index as usize].id,
						internal_name: *internal_name,
						external_name,
					}
				}
				SymbolKind::Memory { memory_index, .. } => {
					self.tir.memories[memory_index as usize]
						.accesses
						.push(SourceSpan::new(file_id, internal_name.span));

					ExportItem::Memory {
						id: self.tir.memories[memory_index as usize].id,
						internal_name: *internal_name,
						external_name,
					}
				}
				_ => {
					self.tir.record_symbol_access(
						file_id,
						global_value,
						internal_name.span,
					);
					self.tir.diagnostics.push(report_cannot_export_item(
						self.interner.resolve(internal_name.inner).unwrap(),
						SourceSpan::new(file_id, internal_name.span),
					));
					continue;
				}
			};

			let (export_symbol, export_span) = match &export_item {
				ExportItem::Function {
					internal_name,
					external_name,
					..
				}
				| ExportItem::Global {
					internal_name,
					external_name,
					..
				}
				| ExportItem::Memory {
					internal_name,
					external_name,
					..
				} => {
					if let Some(ext) = external_name {
						(ext.inner, ext.span)
					} else {
						(internal_name.inner, internal_name.span)
					}
				}
			};

			match items.get(&export_symbol) {
				Some(existing_export) => {
					let name = self.interner.resolve(export_symbol).unwrap();
					let first_export_span = match existing_export {
						ExportItem::Function {
							internal_name,
							external_name,
							..
						}
						| ExportItem::Global {
							internal_name,
							external_name,
							..
						}
						| ExportItem::Memory {
							internal_name,
							external_name,
							..
						} => {
							if let Some(ext) = external_name {
								ext.span
							} else {
								internal_name.span
							}
						}
					};

					self.tir.diagnostics.push(report_duplicate_export(
						name,
						SourceSpan::new(file_id, first_export_span),
						SourceSpan::new(file_id, export_span),
					));
				}
				None => {
					items.insert(export_symbol, export_item);
				}
			}
		}
		items
	}

	pub fn intern_function(
		&mut self,
		params: &[FunctionParam],
		result: Option<Spanned<TypeIndex>>,
	) -> TypeIndex {
		self.intern_type(Type::Function {
			signature: FunctionSignature {
				items: params
					.iter()
					.map(|p| p.ty.inner)
					.chain(Some(match result {
						Some(ty) => ty.inner,
						None => TypeIndex::UNIT,
					}))
					.collect(),
				params_count: params.len() as u32,
			},
		})
	}
}

fn report_missing_enum_repr(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingEnumRepr.code())
		.with_message("enum requires a repr type")
		.with_label(span.primary_label().with_message("add `: <type>` here"))
}

fn report_enum_repr_not_integer(
	fmt: TypeFormatter,
	ty: TypeIndex,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::EnumReprNotInteger.code())
		.with_message("enum repr type must be an integer type")
		.with_label(span.primary_label().with_message(format!(
			"`{}` is not an integer type",
			fmt.display_type(ty).unwrap_or_default()
		)))
}

fn report_enum_variant_requires_explicit_value(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::EnumVariantRequiresExplicitValue.code())
		.with_message("enum variant requires an explicit value")
		.with_label(span.primary_label().with_message("add `= <value>` here"))
		.with_note(
			"or add a value to an earlier variant to anchor auto-increment",
		)
}

/// One diagnostic per colliding value, not pairwise: primary label on the enum's own
/// name, one secondary label per variant that shares `value` (all of them, not just
/// the 2nd/3rd onward) — mirrors rustc's grouped `E0081` presentation.
fn report_enum_duplicate_value(
	enum_name_span: SourceSpan,
	value: i64,
	variant_spans: &[SourceSpan],
) -> Diagnostic<FileId> {
	let mut diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::EnumDuplicateValue.code())
		.with_message(format!(
			"multiple variants of this enum have the same value `{value}`"
		))
		.with_label(enum_name_span.primary_label());
	for span in variant_spans {
		diagnostic = diagnostic.with_label(
			span.secondary_label()
				.with_message(format!("value `{value}` assigned here")),
		);
	}
	diagnostic
}

pub(super) fn report_missing_function_body(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingFunctionBody.code())
		.with_message("free function without a body")
		.with_label(span.primary_label())
		.with_note("provide a definition for the function: `{ <body> }`")
}

fn report_missing_type_alias_body(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingTypeAliasBody.code())
		.with_message("free type alias without body")
		.with_label(span.primary_label())
		.with_label(
			Label::secondary(span.file_id, span.span)
				.with_message("provide a definition for the type: `= <type>;`"),
		)
}

fn report_duplicate_parameter(
	name: &str,
	first_definition: SourceSpan,
	second_definition: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateDefinition.code())
		.with_message(format!(
			"identifier `{}` is bound more than once in this parameter list",
			name
		))
		.with_label(second_definition.primary_label())
		.with_label(
			first_definition
				.secondary_label()
				.with_message(format!("first use of `{}` as parameter", name)),
		)
}

pub(super) fn report_non_constant_global_initializer(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::NonConstantGlobalInitializer.code())
		.with_message(
			"immutable global initializer must be an integer or float literal",
		)
		.with_label(
			span.primary_label()
				.with_message("add `mut` to use a computed initializer"),
		)
}

fn report_invalid_self_type(
	span: SourceSpan,
	formatter: TypeFormatter<'_>,
	ty: TypeIndex,
) -> Diagnostic<FileId> {
	let type_name = formatter.display_type(ty).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidSelfType.code())
		.with_message(format!("invalid `self` parameter type: `{type_name}`"))
		.with_label(span.primary_label().with_message(
			"type of `self` must be `Self` or a type that dereferences to it",
		))
		.with_note("consider changing to `Self` or `*Self`")
}

fn report_duplicate_export(
	name: &str,
	first_export: SourceSpan,
	second_export: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateExport.code())
		.with_message(format!("the name `{}` is exported multiple times", name))
		.with_label(second_export.primary_label())
		.with_label(
			first_export
				.secondary_label()
				.with_message(format!("previous export of `{}` here", name)),
		)
		.with_note(format!(
			"`{}` can only be exported once from this module",
			name
		))
}

fn report_duplicate_export_block(
	first_block: SourceSpan,
	second_block: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateExportBlock.code())
		.with_message("a package can only have one `export` block")
		.with_label(second_block.primary_label())
		.with_label(
			first_block
				.secondary_label()
				.with_message("previous `export` block here"),
		)
		.with_note(
			"an `export` block declares the package's entire public ABI, so \
			 there is nothing for a second one to add — merge the two blocks",
		)
}

fn report_export_block_not_at_root(block: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ExportBlockNotAtRoot.code())
		.with_message(
			"an `export` block must be at the top level of the package's \
			 entry file",
		)
		.with_label(block.primary_label())
		.with_note(
			"exports name the artifact's exit points, which belong to the \
			 package as a whole rather than to any one module inside it",
		)
}

fn report_library_cannot_export(block: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::LibraryCannotExport.code())
		.with_message("a library package cannot have an `export` block")
		.with_label(block.primary_label())
		.with_note(
			"a library is consumed by another package, not run — mark its \
			 items `pub` to expose them to dependents, or set `\"type\": \
			 \"bin\"` in the manifest to build this package as an artifact",
		)
}

fn report_cannot_export_item(
	name: &str,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::CannotExportItem.code())
		.with_message(format!("cannot export `{}`", name))
		.with_label(span.primary_label())
		.with_note(
			"only functions, global variables, and memories can be exported",
		)
}

fn report_cannot_export_generic_function(
	name: &str,
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::CannotExportItem.code())
		.with_message(format!("cannot export generic function `{}`", name))
		.with_label(span.primary_label())
		.with_note(
			"exported functions must be non-generic; call the generic function from a concrete wrapper instead",
		)
}

fn report_duplicate_struct_field(
	name: &str,
	first_span: SourceSpan,
	second_span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateStructField.code())
		.with_message(format!("field `{}` is already declared", name))
		.with_label(second_span.primary_label())
		.with_label(
			first_span
				.secondary_label()
				.with_message(format!("`{}` first declared here", name)),
		)
}
