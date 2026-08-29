//! Phase 1 — the prescan. Walks every item in every file, allocates its TIR
//! entry and claims its name, and records it in `ast_nodes` for the
//! demand-driven signature pass to pick up. No type checking happens here.

use super::*;

impl<'ast> Builder<'ast, '_> {
	pub(super) fn pre_scan_item(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		item: &'ast ast::Item,
	) {
		match item {
			ast::Item::Function {
				id,
				signature,
				attributes,
				pub_span,
				..
			}
			| ast::Item::FunctionDeclaration {
				id,
				signature,
				attributes,
				pub_span,
				..
			} => {
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Value, signature.name.inner),
					*id,
					SourceSpan::new(file_id, signature.name.span),
				);
				let attributes = self.resolve_attributes(*id, attributes);
				let func_index = self.tir.functions.len() as u32;
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Function(func_index));
				self.tir.functions.push(Function {
					id: *id,
					file_id,
					namespace,
					parent: None,
					body: None,
					type_params: signature
						.type_params
						.iter()
						.map(|tp| TypeParamInfo::new(tp.name))
						.collect(),
					type_param_parent: None,
					inherited_type_param_count: 0,
					pub_span: *pub_span,
					signature_index: TypeIndex::ERROR,
					name: signature.name,
					accesses: Vec::new(),
					params: Box::new([]),
					result: None,
					attributes,
				});
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Function { item },
				});
			}
			ast::Item::Global {
				id,
				pub_span,
				mut_span,
				name,
				attributes,
				..
			} => {
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Value, name.inner),
					*id,
					SourceSpan::new(file_id, name.span),
				);
				// `Global` has no `attributes` field of its own, so this runs
				// purely for the `#[tag = ".."]` registration, as on `Trait`.
				self.resolve_attributes(*id, attributes);
				let global_index = self.tir.globals.len() as u32;
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Global(global_index));
				self.tir.globals.push(Global {
					id: *id,
					file_id,
					namespace,
					value: None,
					name: *name,
					ty: ast::Spanned {
						inner: TypeIndex::ERROR,
						span: name.span,
					},
					pub_span: *pub_span,
					mut_span: *mut_span,
					accesses: Vec::new(),
				});
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Global { item },
				});
			}
			ast::Item::Struct {
				id,
				pub_span,
				attributes,
				name,
				type_params,
				..
			} => {
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Type, name.inner),
					*id,
					SourceSpan::new(file_id, name.span),
				);
				let struct_index = self.tir.structs.len() as u32;
				let self_type = self.intern_type(Type::Struct {
					struct_index,
					args: Box::new([]),
				});
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Struct(struct_index));
				let attributes = self.resolve_attributes(*id, attributes);
				self.tir.structs.push(Struct {
					id: *id,
					file_id,
					namespace,
					pub_span: *pub_span,
					name: *name,
					type_params: type_params
						.iter()
						.map(|tp| TypeParamInfo::new(tp.name))
						.collect(),
					self_type,
					attributes,
					fields: Box::new([]),
					lookup: HashMap::new(),
					accesses: Vec::new(),
				});
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Struct { item },
				});
			}
			ast::Item::Enum {
				id,
				pub_span,
				name,
				attributes,
				..
			} => {
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Type, name.inner),
					*id,
					SourceSpan::new(file_id, name.span),
				);
				// See the `Global` arm: registers `#[tag = ".."]` only.
				self.resolve_attributes(*id, attributes);
				let enum_index = self.tir.enums.len() as u32;
				let self_type = self.intern_type(Type::Enum { enum_index });
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Enum(enum_index));
				self.tir.enums.push(Enum {
					id: *id,
					file_id,
					namespace,
					pub_span: *pub_span,
					name: *name,
					repr_type: TypeIndex::ERROR,
					self_type,
					variants: Box::new([]),
					variant_lookup: HashMap::new(),
					accesses: Vec::new(),
				});
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Enum { item },
				});
			}
			ast::Item::TypeAlias {
				id,
				pub_span,
				name,
				type_params,
				attributes,
				..
			} => {
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Type, name.inner),
					*id,
					SourceSpan::new(file_id, name.span),
				);
				let type_alias_index = self.tir.type_aliases.len() as u32;
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::TypeAlias(type_alias_index));
				let attributes = self.resolve_attributes(*id, attributes);
				self.tir.type_aliases.push(TypeAlias {
					id: *id,
					file_id,
					namespace,
					pub_span: *pub_span,
					name: *name,
					attributes,
					type_params: type_params
						.iter()
						.map(|tp| TypeParamInfo::new(tp.name))
						.collect(),
					body: TypeIndex::ERROR,
					accesses: Vec::new(),
				});
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::TypeAlias { item },
				});
			}
			ast::Item::Memory {
				id,
				name,
				bound,
				attributes,
				..
			} => {
				// See the `Global` arm: registers `#[tag = ".."]` only. The
				// `#[memory_limits(..)]` attribute is read separately, in
				// `signature_memory`.
				self.resolve_attributes(*id, attributes);
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Type, name.inner),
					*id,
					SourceSpan::new(file_id, name.span),
				);
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Value, name.inner),
					*id,
					SourceSpan::new(file_id, name.span),
				);
				let memory_index = self.tir.memories.len() as u32;
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Memory(memory_index));
				self.tir.memories.push(Memory {
					id: *id,
					file_id,
					name: *name,
					size: Spanned {
						inner: TypeIndex::ERROR,
						span: bound.span,
					},
					min_pages: None,
					max_pages: None,
					accesses: Vec::new(),
				});
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Memory { item },
				});
			}
			ast::Item::Const {
				id,
				pub_span,
				name,
				attributes,
				..
			} => {
				let id = *id;
				self.claim_name_binding(
					namespace,
					(SymbolNamespace::Value, name.inner),
					id,
					SourceSpan::new(file_id, name.span),
				);
				let const_index = self.tir.constants.len() as ConstIndex;
				self.tir
					.item_lookup
					.insert(id, ItemIndex::Const(const_index));
				let attributes = self.resolve_attributes(id, attributes);
				self.tir.constants.push(Constant {
					id,
					file_id,
					namespace,
					parent: None,
					pub_span: *pub_span,
					name: *name,
					ty: ast::Spanned {
						inner: TypeIndex::ERROR,
						span: name.span,
					},
					value: None,
					const_value: None,
					accesses: Vec::new(),
					attributes,
				});
				self.ast_nodes.push(AstEntry {
					def_id: id,
					file_id,
					namespace,
					node: AstNodeRef::Constant { item },
				});
			}
			ast::Item::Module {
				name,
				items,
				pub_span,
			} => {
				let namespace_index =
					self.ensure_module(file_id, namespace, *name, *pub_span);
				for child in items.iter() {
					self.pre_scan_item(
						file_id,
						namespace_index,
						&child.inner.inner,
					);
				}
			}
			// Nothing to do: Phase 1a already created this module's
			// namespace (and set its `pub_span`) directly from vfs's
			// `SourceModule` tree, before any file's items were scanned.
			ast::Item::ModuleDeclaration { .. } => {}
			ast::Item::Trait {
				id,
				name,
				items,
				pub_span,
				..
			} => {
				let trait_key = (SymbolNamespace::Type, name.inner);
				let existing_direct =
					self.direct_scope_lookup(namespace, trait_key);
				if let Some(existing) = existing_direct
					.filter(|k| !matches!(k, SymbolEntry::Pending(_)))
				{
					let name_str = self.interner.resolve(name.inner).unwrap();
					let first_definition = self.get_symbol_location(existing);
					self.tir.diagnostics.push(report_duplicate_definition(
						DuplicateDefinitionDiagnostic {
							name: name_str,
							namespace: SymbolNamespace::Type,
							first_definition,
							second_definition: SourceSpan::new(
								file_id, name.span,
							),
						},
					));
				}

				let trait_index = self.tir.traits.len() as u32;
				for trait_item in items.iter() {
					match &trait_item.inner.inner {
						ast::TraitItem::Function { id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitFunction {
									trait_index,
									item: &trait_item.inner.inner,
								},
							});
						}
						ast::TraitItem::Const { id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitConst {
									trait_index,
									item: &trait_item.inner.inner,
								},
							});
						}
						ast::TraitItem::AssociatedType { id, name, .. } => {
							self.insert_pending(
								namespace,
								(SymbolNamespace::Type, name.inner),
								*id,
							);
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::TraitAssocType {
									trait_index,
									item: &trait_item.inner.inner,
								},
							});
						}
					}
				}

				let self_name_sym = self.interner.get_or_intern("Self");
				self.tir.traits.push(Trait {
					id: *id,
					file_id,
					namespace,
					pub_span: *pub_span,
					name: *name,
					self_type_param: TypeParamInfo {
						name: Spanned {
							inner: self_name_sym,
							span: name.span,
						},
						bounds: Bounds {
							traits: Box::new([TraitBound {
								trait_index,
								bindings: Box::new([]),
								span: name.span,
							}]),
							typeset: None,
						},
						accesses: Vec::new(),
					},
					entries: HashMap::new(),
					assoc_types: HashMap::new(),
					bounds: Bounds::default(),
					accesses: Vec::new(),
				});
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Trait(trait_index));
				self.insert_symbol(
					namespace,
					(SymbolNamespace::Type, name.inner),
					SymbolKind::Trait { trait_index },
					*pub_span,
				);
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Trait { trait_index, item },
				});
			}
			ast::Item::InherentImpl {
				id: impl_id,
				type_params,
				target,
				items,
			} => {
				// Every inherent impl block gets an `ImplBlock` entry now,
				// concrete (`type_params` empty) or generic alike — allocate
				// it, register a dedicated init entry (resolves bounds +
				// target), then register each item referencing the block's
				// AST id.
				let block_index = self.tir.inherent_impls.len() as u32;
				self.tir.inherent_impls.push(InherentImpl {
					id: *impl_id,
					file_id,
					type_params: type_params
						.iter()
						.map(|tp| TypeParamInfo::new(tp.name))
						.collect(),
					target: Spanned {
						inner: TypeIndex::ERROR,
						span: target.span,
					},
					members: HashMap::new(),
					self_accesses: Vec::new(),
				});
				self.ast_nodes.push(AstEntry {
					def_id: *impl_id,
					file_id,
					namespace,
					node: AstNodeRef::InherentImplBlock {
						impl_type_params: type_params,
						impl_target: target,
						block_index,
					},
				});
				for impl_item in items.iter() {
					match &impl_item.inner.inner {
						ast::ImplItem::Function { id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::InherentImplFunction {
									block_id: *impl_id,
									item: &impl_item.inner.inner,
									block_index,
								},
							});
						}
						ast::ImplItem::Constant { id, .. } => {
							if type_params.is_empty() {
								self.ast_nodes.push(AstEntry {
									def_id: *id,
									file_id,
									namespace,
									node: AstNodeRef::InherentImplConst {
										block_id: *impl_id,
										item: &impl_item.inner.inner,
										block_index,
									},
								});
							} else {
								todo!("support consts in generic impls")
							}
						}
						ast::ImplItem::AssocType { name, .. } => {
							if type_params.is_empty() {
								self.tir.diagnostics.push(
									report_associated_type_in_inherent_impl(
										SourceSpan::new(file_id, name.span),
									),
								);
							}
							// else: TODO: support/diagnose associated types in
							// generic impls too
						}
					}
				}
			}
			ast::Item::Import {
				module: import_module_name,
				alias,
				entries,
			} => {
				// Imports are processed eagerly: their signatures depend only on
				// primitive types or previously-registered stdlib types.
				let import_decl_index = self.tir.import_decls.len() as u32;
				let external_name = {
					let s = self
						.interner
						.resolve(import_module_name.inner)
						.unwrap();
					let unquoted = unescape_string(s);
					Spanned {
						inner: self.interner.get_or_intern(&unquoted),
						span: import_module_name.span,
					}
				};
				let namespace_idx = self.tir.namespaces.len() as u32;
				let decl_idx = self.tir.import_decls.len() as u32;
				let package = self.tir.namespaces[namespace as usize].package;
				self.tir.namespaces.push(ModuleNamespace {
					parent: Some(namespace),
					package,
					declaration: ModuleDeclarationKind::Import(decl_idx),
					symbols: HashMap::new(),
					wildcard_imports: Vec::new(),
					accesses: Vec::new(),
				});
				self.seed_path_root_symbols(
					namespace_idx,
					package,
					Some(namespace),
				);
				// Only a real, user-written alias is ever checked for a
				// collision or bound as a `Type`-namespace name —
				// `external_name` (the unescaped import-path string) was
				// never something the user wrote as an identifier, so
				// there's nothing legitimate to check or bind it under.
				// Either failure still lets the import's own namespace,
				// decl, and entries register normally below — it just
				// isn't reachable by name.
				match *alias {
					Some(alias) => {
						if self
							.check_module_collision(file_id, namespace, alias)
							.is_none()
						{
							self.insert_symbol(
								namespace,
								(SymbolNamespace::Type, alias.inner),
								SymbolKind::Module { namespace_idx },
								None,
							);
						}
					}
					None => {
						self.tir.diagnostics.push(report_missing_import_alias(
							SourceSpan::new(file_id, import_module_name.span),
						));
					}
				}
				for entry in entries.iter() {
					match &entry.inner.inner.declaration {
						ast::ImportDeclaration::Function { id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::ImportedFunction {
									import_module_index: import_decl_index,
									decl: &entry.inner.inner.declaration,
								},
							});
						}
						ast::ImportDeclaration::Global { id, name, .. } => {
							self.insert_pending(
								namespace,
								(SymbolNamespace::Value, name.inner),
								*id,
							);
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::ImportedGlobal {
									import_module_index: import_decl_index,
									decl: &entry.inner.inner.declaration,
								},
							});
						}
						ast::ImportDeclaration::Memory { id, name, .. } => {
							self.insert_pending(
								namespace,
								(SymbolNamespace::Type, name.inner),
								*id,
							);
							self.insert_pending(
								namespace,
								(SymbolNamespace::Value, name.inner),
								*id,
							);
							self.ast_nodes.push(AstEntry {
								def_id: *id,
								file_id,
								namespace,
								node: AstNodeRef::Memory { item },
							});
						}
					}
				}
				self.tir.import_decls.push(ImportDecl {
					namespace_idx,
					file_id,
					external_name,
					internal_name: *alias,
					lookup: HashMap::new(),
				});
			}
			ast::Item::Use { tree, pub_span } => {
				let mut prefix: Vec<ast::Spanned<SymbolU32>> = Vec::new();
				self.pre_scan_use_tree(
					ResolveContext::new(file_id, namespace),
					*pub_span,
					tree,
					&mut prefix,
					tree.span.start,
					None,
				);
			}
			ast::Item::Export { id, .. } => {
				// No name binding of its own — an export block declares
				// nothing, it only names items declared elsewhere. It still
				// gets an `ast_nodes` entry so the Phase 2 sweep reaches it
				// in parse order, at which point it can force each listed
				// name through `ensure_signature` like any other reference.
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::Export { item },
				});
			}
			ast::Item::TypeSet {
				id,
				name,
				pub_span,
				attributes,
				..
			} => {
				let attributes = self.resolve_attributes(*id, attributes);
				let typeset_index = self.tir.typesets.len() as TypesetIndex;
				self.tir.typesets.push(TypeSet {
					id: *id,
					file_id,
					namespace,
					name: *name,
					pub_span: *pub_span,
					members: Box::new([]),
					intersection_range: IntegerRange::widest(),
					accesses: Vec::new(),
					attributes,
				});
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::TypeSet(typeset_index));
				self.insert_symbol(
					namespace,
					(SymbolNamespace::Type, name.inner),
					SymbolKind::TypeSet { typeset_index },
					*pub_span,
				);
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::TypeSet {
						typeset_index,
						item,
					},
				});
			}
			ast::Item::TraitImpl { id, items, .. } => {
				self.ast_nodes.push(AstEntry {
					def_id: *id,
					file_id,
					namespace,
					node: AstNodeRef::TraitImplBlock { item },
				});
				for mi in items.iter() {
					match &mi.inner.inner {
						ast::ImplItem::Function { id: method_id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *method_id,
								file_id,
								namespace,
								node: AstNodeRef::TraitImplFunction {
									parent_id: *id,
									item: &mi.inner.inner,
								},
							});
						}
						ast::ImplItem::Constant { id: const_id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *const_id,
								file_id,
								namespace,
								node: AstNodeRef::TraitImplConstant {
									parent_id: *id,
									item: &mi.inner.inner,
								},
							});
						}
						ast::ImplItem::AssocType { id: type_id, .. } => {
							self.ast_nodes.push(AstEntry {
								def_id: *type_id,
								file_id,
								namespace,
								node: AstNodeRef::TraitImplAssocType {
									parent_id: *id,
									item: &mi.inner.inner,
								},
							});
						}
					}
				}
			}
		}
	}
}
