//! Traits and impls: registering a trait impl against its target type, and
//! Phase 2 for every trait, inherent-impl and trait-impl item — blocks, methods,
//! associated consts and associated types — plus the conformance check that
//! verifies each impl provides everything its trait requires.

use crate::diagnostics::DiagnosticCode;

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Registers `trait_impl_index` (already pushed into `items.trait_impls`,
	/// target already resolved to `target_type`) into `trait_impl_dispatch`,
	/// unless a prior impl of the same trait already claims this type
	/// constructor — WX allows at most one implementation of a given trait
	/// per type constructor (generic arguments never participate in impl
	/// selection), so a second one is a hard error at declaration time
	/// rather than something arbitrated later per call site. On conflict,
	/// the new impl is left unregistered (unreachable via dispatch) but its
	/// `DefId` still exists and its body still gets type-checked normally in
	/// Phase 3, so unrelated errors inside it are still reported.
	pub(super) fn register_trait_impl(
		&mut self,
		target_type: TypeIndex,
		trait_index: TraitIndex,
		trait_impl_index: TraitImplIndex,
	) {
		let Ok(kind) = ImplTarget::from_type(self.types.resolve(target_type))
		else {
			let trait_name_sym =
				self.items.traits[usize::from(trait_index)].name.inner;
			let trait_name = self.interner.resolve(trait_name_sym).unwrap();
			let imp = &self.items.trait_impls[usize::from(trait_impl_index)];
			let span = SourceSpan::new(imp.file_id, imp.span);
			let type_str = self
				.formatter(self.modules.file_namespaces[imp.file_id.as_usize()])
				.display_type(target_type)
				.unwrap();
			self.diagnostics.push(Diagnostic {
				severity: Severity::Error,
				code: Some(
					DiagnosticCode::InvalidImplTarget.code().to_string(),
				),
				message: format!(
					"cannot implement `{trait_name}` for `{type_str}`"
				),
				labels: vec![span.primary_label()],
				notes: Vec::new(),
			});
			return;
		};
		let bucket = self.items.trait_impl_dispatch.entry(kind).or_default();
		if let Some(&(_, existing_index)) =
			bucket.iter().find(|(ti, _)| *ti == trait_index)
		{
			let trait_name_sym =
				self.items.traits[usize::from(trait_index)].name.inner;
			let trait_name = self.interner.resolve(trait_name_sym).unwrap();
			let new_impl =
				&self.items.trait_impls[usize::from(trait_impl_index)];
			let new_span = SourceSpan::new(new_impl.file_id, new_impl.span);
			let existing_impl =
				&self.items.trait_impls[usize::from(existing_index)];
			let existing_span =
				SourceSpan::new(existing_impl.file_id, existing_impl.span);
			self.diagnostics.push(Diagnostic {
				severity: Severity::Error,
				code: Some(
					DiagnosticCode::DuplicateTraitImpl.code().to_string(),
				),
				message: format!(
					"`{trait_name}` is already implemented for this type constructor"
				),
				labels: vec![
					new_span.primary_label().with_message(format!(
						"duplicate implementation of `{trait_name}`"
					)),
					existing_span
						.secondary_label()
						.with_message("first implementation here"),
				],
				notes: Vec::new(),
			});
			return;
		}
		bucket.push((trait_index, trait_impl_index));
	}

	pub(super) fn check_trait_conformance(&mut self) {
		for trait_impl in self.items.trait_impls.iter() {
			let trait_def =
				&self.items.traits[usize::from(trait_impl.trait_index)];
			let mut missing_items: Vec<(SymbolU32, TextSpan)> = Vec::new();

			for (&name, &def_entry) in trait_def.members.iter() {
				let def_entry = def_entry.entry(&self.items);
				match trait_impl.members.get(&name).copied() {
					Some(provided_impl) => match (provided_impl, def_entry) {
						(
							ImplEntry::Method(impl_index),
							ImplEntry::Method(def_index),
						)
						| (
							ImplEntry::AssocFunction(impl_index),
							ImplEntry::AssocFunction(def_index),
						) => {
							if let SignatureComparison::Incompatible(
								difference,
							) = self.compare_method_signature(
								def_index, impl_index, trait_impl,
							) {
								self.diagnostics.push(
									self.report_incompatible_method_signature(
										trait_def.name.inner,
										name,
										def_index,
										impl_index,
										&difference,
									),
								);
							}
						}
						(
							ImplEntry::AssocConstant(impl_index),
							ImplEntry::AssocConstant(def_index),
						) => {
							if let TypeComparison::Different(difference) = self
								.compare_assoc_const_type(
									def_index, impl_index, trait_impl,
								) {
								self.diagnostics.push(
									self.report_incompatible_const_type(
										trait_def.name.inner,
										name,
										def_index,
										impl_index,
										&difference,
									),
								);
							}
						}
						(
							ImplEntry::AssocType(_impl_index),
							ImplEntry::AssocType(_def_index),
						) => {}
						_ => {
							missing_items.push((
								name,
								def_entry.def_span(&self.items).span,
							));
							self.diagnostics.push(
									Diagnostic::new(Severity::Error)
										.with_code(
											DiagnosticCode::TraitImplItemKindMismatch,
										)
										.with_message(format!(
											"item `{}` is a {}, which doesn't match its trait `{}`",
											self.interner.resolve(name).unwrap(),
											provided_impl.noun(),
											self.interner
												.resolve(trait_def.name.inner)
												.unwrap(),
										))
										.with_label(
											provided_impl
												.def_span(&self.items)
												.primary_label()
												.with_message("does not match trait"),
										)
										.with_label(
											def_entry
												.def_span(&self.items)
												.secondary_label()
												.with_message("item in trait"),
										),
								);
						}
					},
					None => {
						let default_impl_exists = match def_entry {
							ImplEntry::AssocFunction(func_index)
							| ImplEntry::Method(func_index) => self.items.functions
								[usize::from(func_index)]
							.body
							.is_some(),
							ImplEntry::AssocConstant(const_index) => {
								self.items.constants[usize::from(const_index)]
									.value
									.is_some()
							}
							// TODO: We may add default associated types in traits later
							// https://github.com/rust-lang/rust/issues/29661
							// In rust there's much more edge cases with dispatch, impl specialization and triat objects
							// but for us it should be failrly simple
							// The only thing is that we shouldn't assume that defautl type bounds the associated type to anythinig automatically
							// It should act just like a fallback
							ImplEntry::AssocType(_) => false,
						};

						if !default_impl_exists {
							missing_items.push((
								name,
								def_entry.def_span(&self.items).span,
							));
						}
					}
				};
			}

			if !missing_items.is_empty() {
				missing_items.sort_unstable_by_key(|(_, span)| span.start);
				// TODO: join without allocating intermediate Box<[_]>
				let names = missing_items
					.iter()
					.map(|(symbol, _)| self.interner.resolve(*symbol).unwrap())
					.collect::<Box<[_]>>()
					.join(", ");

				let mut diagnostic = Diagnostic::error()
					.with_code(DiagnosticCode::IncompleteTraitImpl)
					.with_message("not all trait items implemented")
					.with_label(
						SourceSpan::new(trait_impl.file_id, trait_impl.span)
							.primary_label()
							.with_message(format!(
								"missing {} in implementation",
								names
							)),
					);
				for (symbol, item_span) in missing_items {
					diagnostic.labels.push(
						SourceSpan::new(trait_def.file_id, item_span)
							.secondary_label()
							.with_message(format!(
								"`{}` from trait",
								self.interner.resolve(symbol).unwrap()
							)),
					);
				}
				self.diagnostics.push(diagnostic);
			}

			for (&name, &impl_entry) in trait_impl.members.iter() {
				if !trait_def.members.contains_key(&name) {
					let trait_name =
						self.interner.resolve(trait_def.name.inner).unwrap();
					let item_name = self.interner.resolve(name).unwrap();
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(DiagnosticCode::NotATraitMember)
							.with_message(format!(
								"{} `{item_name}` is not a member of trait `{trait_name}`",
								impl_entry.noun(),
							))
							.with_label(
								impl_entry
									.def_span(&self.items)
									.primary_label()
									.with_message(format!(
										"not a member of trait `{trait_name}`"
									)),
							),
					);
				}
			}

			for supertrait in trait_def.supertraits(trait_impl.trait_index) {
				if self
					.items
					.find_trait_impl(
						&self.types,
						trait_impl.target.inner,
						supertrait.trait_index,
					)
					.is_none()
				{
					let supertrait_name = self
						.interner
						.resolve(
							self.items.traits
								[usize::from(supertrait.trait_index)]
							.name
							.inner,
						)
						.unwrap();
					let trait_name =
						self.interner.resolve(trait_def.name.inner).unwrap();
					let target_name = self
						.formatter(trait_impl.namespace)
						.display_type(trait_impl.target.inner)
						.unwrap();
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::UnsatisfiedTraitBound.code(),
							)
							.with_message(format!(
								"the trait bound `{}: {}` is not satisfied",
								target_name, supertrait_name,
							))
							.with_label(
								SourceSpan::new(
									trait_impl.file_id,
									trait_impl.target.span,
								)
								.primary_label()
								.with_message("unsatisfied trait bound"),
							)
							.with_label(
								SourceSpan::new(
									trait_def.file_id,
									trait_def.name.span,
								)
								.secondary_label()
								.with_message(format!(
									"required by a bound in `{}`",
									trait_name
								)),
							),
					);
				}
			}
		}

		// iterating without borrowing so that there's no issues when trying to borrow again with mutable reference in check_assoc_type_bounds
		for trait_impl_index in 0..self.items.trait_impls.len() {
			let trait_impl = &self.items.trait_impls[trait_impl_index];
			let trait_index = trait_impl.trait_index;
			let target_type = trait_impl.target.inner;
			let resolve_context = ResolveContext {
				file_id: trait_impl.file_id,
				namespace: trait_impl.namespace,
			};

			let mut assoc_types: Box<[_]> = self.items.trait_impls
				[trait_impl_index]
				.members
				.values()
				.copied()
				.filter_map(|entry| match entry {
					ImplEntry::AssocType(idx) => {
						let assoc_type =
							&self.items.associated_types[usize::from(idx)];
						Some((assoc_type.name, assoc_type.ty.unwrap()))
					}
					_ => None,
				})
				.collect();
			if assoc_types.is_empty() {
				continue;
			};
			assoc_types.sort_unstable_by_key(|(name, _)| name.span.start);
			for (name, ty) in assoc_types.into_iter() {
				self.check_assoc_type_bounds(
					resolve_context,
					trait_index,
					target_type,
					name,
					ty,
				);
			}
		}
	}

	pub(super) fn signature_inherent_impl_const(
		&mut self,
		resolve_context: ResolveContext,
		block_id: ast::DefId,
		item: &'ast ast::ImplItem,
		block_index: InherentImplIndex,
	) {
		// Ensure the impl block's target is resolved first. In progress means
		// the block is what forced this member, and it resolves its target
		// before doing so — see `signature_inherent_impl_block`.
		let _ = self.ensure_signature(block_id);

		if let ast::ImplItem::Constant {
			id,
			pub_span,
			name,
			ty,
			value,
			attributes,
		} = item
		{
			let attributes = self.resolve_attributes(*id, attributes);
			let self_type = self.items.inherent_impls[usize::from(block_index)]
				.target
				.inner;
			let self_scope = GenericScope {
				owner: TypeParamOwner::InherentImpl(block_index),
				self_type: Some(self_type),
			};
			let resolved_ty = match ty {
				Some(te) => {
					self.resolve_type(resolve_context, Some(self_scope), te)
				}
				None => TypeIndex::ERROR,
			};
			if let Ok(value_expr) = self.build_const_context_expression(
				resolve_context,
				value,
				resolved_ty,
			) {
				let const_value = match self.eval_const_expr(&value_expr) {
					Ok(v) => Some(v),
					Err(_) => {
						self.diagnostics.push(report_not_const_evaluatable(
							SourceSpan::new(
								resolve_context.file_id,
								value.span,
							),
						));
						None
					}
				};
				let const_index = self.items.push_constant(Constant {
					id: *id,
					file_id: resolve_context.file_id,
					namespace: resolve_context.namespace,
					parent: Some(ItemParent::InherentImpl(block_index)),
					pub_span: *pub_span,
					name: *name,
					ty: ast::Spanned {
						inner: resolved_ty,
						span: name.span,
					},
					value: Some(Box::new(value_expr)),
					const_value,
					accesses: Vec::new(),
					attributes,
				});
				self.register_inherent_impl_member(
					block_index,
					*id,
					name.inner,
					ImplEntry::AssocConstant(const_index),
				);
			}
		}
	}

	pub(super) fn signature_inherent_impl_function(
		&mut self,
		resolve_context: ResolveContext,
		block_id: ast::DefId,
		item: &'ast ast::ImplItem,
		block_index: InherentImplIndex,
	) {
		// Ensure the impl block's bounds and target are resolved first. Same
		// parent-before-member ordering as `signature_inherent_impl_const`.
		let _ = self.ensure_signature(block_id);

		let ast::ImplItem::Function {
			id,
			pub_span,
			attributes,
			signature,
			..
		} = item
		else {
			return;
		};

		// The impl block already has its bounds and target resolved.
		let self_type = self.items.inherent_impls[usize::from(block_index)]
			.target
			.inner;
		let inherited_type_param_count = u32::try_from(
			self.items.inherent_impls[usize::from(block_index)]
				.type_params
				.len(),
		)
		.unwrap();

		let attributes = self.resolve_attributes(*id, attributes);
		// Register the function with only its own (method-level) type
		// params. Impl-level params (if any) are inherited via
		// type_param_parent.
		let func_index = self.items.push_function(Function {
			is_method: signature.params.first().is_some_and(|p| {
				self.interner.resolve(p.inner.inner.name.inner) == Some("self")
			}),
			id: *id,
			file_id: resolve_context.file_id,
			namespace: resolve_context.namespace,
			parent: Some(ItemParent::InherentImpl(block_index)),
			body: None,
			type_params: signature
				.type_params
				.iter()
				.map(|tp| TypeParamInfo::new(tp.name))
				.collect(),
			inherited_type_param_count,
			pub_span: *pub_span,
			signature_index: TypeIndex::ERROR,
			name: signature.name,
			accesses: Vec::new(),
			params: Box::new([]),
			result: None,
			attributes,
		});

		// Resolve the function's own param bounds. resolve_type_identifier
		// automatically walks up to ImplBlock when a name isn't found in
		// own params.
		self.resolve_type_param_bounds(
			resolve_context,
			TypeParamOwner::Function(*id),
			None,
			&signature.type_params,
		);

		let self_symbol = self.interner.get_or_intern("self");
		let is_method = signature
			.params
			.first()
			.map(|p| p.inner.inner.name.inner == self_symbol)
			.unwrap_or(false);

		let scope = GenericScope {
			owner: TypeParamOwner::Function(*id),
			self_type: Some(self_type),
		};
		let (params, result) = self.build_function_signature(
			resolve_context,
			Some(scope),
			signature,
		);
		let signature_index = self.intern_function(&params, result);
		let func = &mut self.items.functions[usize::from(func_index)];
		func.params = params;
		func.result = result;
		func.signature_index = signature_index;

		let entry = if is_method {
			ImplEntry::Method(func_index)
		} else {
			ImplEntry::AssocFunction(func_index)
		};

		self.register_inherent_impl_member(
			block_index,
			*id,
			signature.name.inner,
			entry,
		);
	}

	/// Registers `entry` under `name`, if this declaration is the one that
	/// still holds it: `member_decls` is what a block answers to, and
	/// [`Self::register_inherent_impl_decls`] has already settled and reported
	/// every name two declarations wanted.
	fn register_inherent_impl_member(
		&mut self,
		block_index: InherentImplIndex,
		id: ast::DefId,
		name: SymbolU32,
		entry: ImplEntry,
	) {
		let block = &mut self.items.inherent_impls[usize::from(block_index)];
		if block
			.member_decls
			.get(&name)
			.is_some_and(|decl| decl.id == id)
		{
			block.members.insert(name, entry);
		}
	}

	/// Enters the block's declared names into `inherent_impl_dispatch`, and
	/// reports each one that another block already claimed for a receiver this
	/// one would also claim — see [`Self::conflicting_inherent_block`].
	///
	/// This runs with the header, from `member_decls` alone, because the
	/// bucket *is* the candidate set: a lookup that finds no bucket entry
	/// concludes the type has no such member, so a block missing from it until
	/// its members happen to resolve makes `S::N` an error or not depending on
	/// where the `impl` was written. Nothing here needs a resolved member —
	/// which block claims which name is settled by syntax, and only the target
	/// type has to be resolved first, to key the bucket by.
	///
	/// `resolve_impl_member` arbitrates between candidates as well, and still
	/// does — both blocks stay in the bucket — but only per call site and only
	/// where there is one, so a conflict nobody happens to call would
	/// otherwise ship unreported.
	fn register_inherent_impl_decls(
		&mut self,
		block_index: InherentImplIndex,
		self_type: TypeIndex,
		items: &[ast::Separated<ast::Spanned<ast::ImplItem>>],
	) {
		// A block whose target failed to resolve has no `ImplTarget`, so it
		// never reaches a bucket at all — and can conflict with nothing, since
		// there is no receiver it is known to claim.
		let Ok(target) = ImplTarget::from_type(self.types.resolve(self_type))
		else {
			return;
		};
		let file_id =
			self.items.inherent_impls[usize::from(block_index)].file_id;
		// Source order, rather than `member_decls`' iteration order, so the
		// diagnostics below come out the same way twice.
		for item in items.iter() {
			let name = match &item.inner.inner {
				ast::ImplItem::Function { signature, .. } => signature.name,
				ast::ImplItem::Constant { name, .. }
				| ast::ImplItem::AssocType { name, .. } => *name,
			};
			let block = &self.items.inherent_impls[usize::from(block_index)];
			// A name this block declares twice is already reported, and is in
			// the bucket once under the winning declaration.
			if block
				.member_decls
				.get(&name.inner)
				.is_none_or(|decl| decl.span != name.span)
			{
				continue;
			}
			if let Some(other) = self.conflicting_inherent_block(
				target,
				block_index,
				self_type,
				name.inner,
			) {
				let other_block =
					&self.items.inherent_impls[usize::from(other)];
				let existing = other_block.member_decls[&name.inner];
				self.diagnostics.push(report_duplicate_definition(
					DuplicateDefinitionDiagnostic {
						name: self.interner.resolve(name.inner).unwrap(),
						namespace: existing.kind.namespace(),
						first_definition: SourceSpan::new(
							other_block.file_id,
							existing.span,
						),
						second_definition: SourceSpan::new(file_id, name.span),
					},
				));
			}
			// Both blocks stay candidates even so, the way rustc keeps both
			// inherent impls and reports E0034 at each use: the declaration is
			// a real one, and dropping it would silence every call site in
			// favour of one diagnostic pointing at neither of them.
			self.items
				.inherent_impl_dispatch
				.entry((target, name.inner))
				.or_default()
				.push(block_index);
		}
	}

	/// An already-registered block that provides `name` for a receiver
	/// `block_index` would also claim, if there is one.
	///
	/// The dispatch bucket is the candidate set, and a precise one: keyed by
	/// `(ImplTarget, name)`, it holds every block providing this name for
	/// this type constructor and nothing else. rustc reaches for the same
	/// index — grouping impls by shared item identifier — only past
	/// `ALLOCATING_ALGO_THRESHOLD`, because building it is a cost there;
	/// here dispatch needs it anyway, so the narrow candidate set is free.
	///
	/// `ImplTarget` is coarse, though — `impl Box<i32>` and `impl Box<bool>`
	/// share a bucket while overlapping on no receiver at all — so the
	/// targets themselves decide. Overlap is asked as unification in both
	/// directions: one-sided unification treats only the *left* target's
	/// params as holes, and `Box<i32>` is concrete as far as `Box<T>` is
	/// concerned, so trying each as the pattern in turn covers a generic
	/// block against a concrete one either way round.
	fn conflicting_inherent_block(
		&self,
		target: ImplTarget,
		block_index: InherentImplIndex,
		self_type: TypeIndex,
		name: SymbolU32,
	) -> Option<InherentImplIndex> {
		let own_params = self.items.inherent_impls[usize::from(block_index)]
			.type_params
			.len();
		let bucket = self.items.inherent_impl_dispatch.get(&(target, name))?;
		bucket.iter().copied().find(|&other| {
			if other == block_index {
				return false;
			}
			let other_block = &self.items.inherent_impls[usize::from(other)];
			self.items
				.unify_impl_target(
					&self.types,
					own_params,
					self_type,
					other_block.target.inner,
				)
				.is_some() || self
				.items
				.unify_impl_target(
					&self.types,
					other_block.type_params.len(),
					other_block.target.inner,
					self_type,
				)
				.is_some()
		})
	}

	pub(super) fn signature_inherent_impl_block(
		&mut self,
		resolve_context: ResolveContext,
		item: &'ast ast::Item,
		block_index: InherentImplIndex,
	) {
		let (impl_type_params, impl_target, items) = match item {
			ast::Item::InherentImpl {
				type_params,
				target,
				items,
				..
			} => (type_params.as_ref(), target.as_ref(), items),
			_ => unreachable!(),
		};

		// What this block declares, by name, before any member resolves —
		// see `MemberDecl`.
		self.items.inherent_impls[usize::from(block_index)].member_decls =
			self.collect_member_decls(resolve_context, items);

		self.resolve_type_param_bounds(
			resolve_context,
			TypeParamOwner::InherentImpl(block_index),
			None,
			impl_type_params,
		);
		let self_type = self.resolve_signature_type(
			resolve_context,
			Some(GenericScope {
				owner: TypeParamOwner::InherentImpl(block_index),
				self_type: None,
			}),
			impl_target,
		);

		let target = match ImplTarget::from_type(self.types.resolve(self_type))
		{
			Ok(kind) => {
				self.check_inherent_impl_locality(
					resolve_context,
					kind,
					impl_target.span,
				);
				self_type
			}
			Err(_) => {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::InvalidImplTarget.code())
						.with_message(format!(
							"cannot define an `impl` block for `{}`",
							self.formatter(resolve_context.namespace)
								.display_type(self_type)
								.unwrap()
						))
						.with_label(Label::primary(
							resolve_context.file_id,
							impl_target.span,
						)),
				);
				TypeIndex::ERROR
			}
		};
		self.items.inherent_impls[usize::from(block_index)]
			.target
			.inner = target;
		self.register_inherent_impl_decls(block_index, target, items);
	}

	/// The package that defines the type an inherent `impl` targets.
	///
	/// Only a struct or enum has a declaration to read this off; the rest are
	/// answered by rule.
	///
	/// - A memory may only be declared in the root module of a binary
	///   package. Not enforced everywhere yet, but a memory belonging to
	///   anything but the root package is not a state the language allows.
	/// - The primitives are the stdlib's because that is where they are
	///   declared (`#[intrinsic] pub type i32;` and friends in
	///   `std/main.wx`). Their alias is transparent, so the target arrives
	///   here as a bare [`Type::I32`] with no declaration left to consult.
	/// - Nothing declares a slice or an array — the type system builds them
	///   from an element type — leaving the owner of every other built-in as
	///   the only sensible answer.
	fn impl_target_package(&self, target: ImplTarget) -> PackageId {
		let namespace = match target {
			ImplTarget::Struct(struct_index) => {
				self.items.structs[usize::from(struct_index)].namespace
			}
			ImplTarget::Enum(enum_index) => {
				self.items.enums[usize::from(enum_index)].namespace
			}
			ImplTarget::Memory(_) => return self.root_package,
			ImplTarget::Slice
			| ImplTarget::Array
			| ImplTarget::U8
			| ImplTarget::I8
			| ImplTarget::U16
			| ImplTarget::I16
			| ImplTarget::U32
			| ImplTarget::I32
			| ImplTarget::U64
			| ImplTarget::I64
			| ImplTarget::F32
			| ImplTarget::F64
			| ImplTarget::Bool
			| ImplTarget::Char => return self.stdlib_package,
		};
		self.modules.namespaces[usize::from(namespace)].package
	}

	/// An inherent `impl` may only be written in the package that defines its
	/// target type.
	///
	/// Otherwise two packages could each hang a method of the same name off a
	/// third package's type, and every call site seeing both would have to
	/// arbitrate — a conflict neither author can detect, since neither one's
	/// package holds both halves. Confining inherent members to the defining
	/// package is what lets [`Self::register_impl_member`] treat a name
	/// collision as a plain duplicate definition.
	///
	/// Trait impls are deliberately untouched: implementing a trait for a
	/// foreign type is the supported way to extend one, and its coherence
	/// question is already answered by [`Self::register_trait_impl`].
	fn check_inherent_impl_locality(
		&mut self,
		resolve_context: ResolveContext,
		target: ImplTarget,
		span: ast::TextSpan,
	) {
		let target_package = self.impl_target_package(target);
		let declaring_package = self.modules.namespaces
			[usize::from(resolve_context.namespace)]
		.package;
		if target_package == declaring_package {
			return;
		}
		self.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::ForeignImplTarget.code())
				.with_message(
					"cannot define inherent `impl` for a type outside of the \
					 package where the type is defined",
				)
				.with_label(
					SourceSpan::new(resolve_context.file_id, span)
						.primary_label()
						.with_message(
							"impl for type defined outside of package",
						),
				)
				.with_note(
					"consider defining a trait and implementing it for the \
					 type, or wrapping it in a struct of your own and \
					 implementing that instead"
						.to_string(),
				),
		);
	}

	/// Resolves `trait Sub: Super + Other { .. }`'s supertrait clause into
	/// `Sub`'s own `Self` bounds — the sole writer of that field, reflexive
	/// `Self: Sub` entry included. Everything that asks what a type parameter
	/// satisfies (method and associated-item resolution,
	/// `type_implements_trait`) then sees a supertrait without knowing
	/// supertraits exist; `Trait::supertraits` reads them back out by
	/// filtering the reflexive entry.
	///
	/// Demands only the supertrait clauses. Attribute processing and binding
	/// validation belong to `signature_trait`; member demands must not pull
	/// that validation back in while resolving a bound's associated type.
	/// Members are always demanded separately by declaration identity.
	///
	/// Recurses into each supertrait's own clause, so reading a trait's
	/// `Self` bounds guarantees its supertraits' bounds are resolved too —
	/// what a transitive walk over the supertrait graph
	/// ([`ItemRegistry::trait_implies`]) reads.
	pub(super) fn ensure_trait_supertraits(&mut self, trait_index: TraitIndex) {
		// The walk's own path, which only it can see and only for as long as
		// it runs — see `resolve_supertrait_clause`. Never allocates unless
		// there is a clause left to resolve, since the guard there returns
		// before the first push.
		self.resolve_supertrait_clause(trait_index, &mut Vec::new());
	}

	/// [`Self::ensure_trait_supertraits`], carrying the chain of traits the
	/// walk is currently inside so that a supertrait which is already on it
	/// can be told from one that is merely already resolved.
	///
	/// That distinction is the whole difference between a diamond and a cycle,
	/// and the bounds themselves cannot make it: they are written *before* the
	/// recursion (so the walk terminates at all), which leaves "non-empty"
	/// meaning done-or-in-progress. The path is also what names the loop in
	/// the diagnostic, so one structure answers both.
	///
	/// A `Vec` threaded through the recursion rather than a field on
	/// `Builder`: it means something only inside this function's dynamic
	/// extent, and `sig_stack` — the other stack in the builder — belongs to
	/// `ensure_signature`, whose frames these are deliberately not.
	fn resolve_supertrait_clause(
		&mut self,
		trait_index: TraitIndex,
		stack: &mut Vec<TraitIndex>,
	) {
		// The write below is the guard: `Self`'s bounds always get at least
		// the reflexive entry, and they get it *before* this recurses, so a
		// non-empty list means this trait is done — or is on `stack`, which
		// the caller checks before recursing here.
		if !self.items.traits[usize::from(trait_index)]
			.self_type_param
			.bounds
			.traits
			.is_empty()
		{
			return;
		}

		// The trait's own AST node, reached the same way `ensure_signature`
		// reaches any item's: `sig_state` maps its `DefId` to its
		// `ast_nodes` slot.
		let def_id = self.items.traits[usize::from(trait_index)].id;
		let node_idx = self.sig_state[&def_id].node_idx;
		let AstEntry {
			file_id,
			namespace,
			node,
			..
		} = self.ast_nodes[node_idx].clone();
		let AstNodeRef::Trait {
			item: ast::Item::Trait {
				supertraits, name, ..
			},
			..
		} = node
		else {
			unreachable!("a TraitIndex's DefId always maps to a trait node")
		};

		let bounds = match supertraits {
			Some(spanned) => self.resolve_bounds(
				ResolveContext::new(file_id, namespace),
				None,
				spanned,
			),
			None => Bounds::default(),
		};

		// `Self: ThisTrait` first — a default body reaches the trait's own
		// members through it, and `Trait::supertraits` filters it back out by
		// trait index. A typeset supertrait (`trait Foo: Integer`) fills the
		// one typeset slot, the same way it would on any other type param.
		let self_param =
			&mut self.items.traits[usize::from(trait_index)].self_type_param;
		let mut traits = Vec::with_capacity(1 + bounds.traits.len());
		traits.push(TraitBound {
			trait_index,
			bindings: Box::new([]),
			span: name.span,
		});
		traits.extend(bounds.traits.iter().cloned());
		self_param.bounds.traits = traits.into_boxed_slice();
		self_param.bounds.typeset = bounds.typeset;

		// Up the parent chain: after this returns, every ancestor's `Self`
		// bounds are resolved too, which is what a transitive walk over the
		// supertrait graph (`ItemRegistry::trait_implies`) reads. Their
		// *members* stay lazy — nothing here needs them.
		stack.push(trait_index);
		for supertrait in bounds.traits.iter() {
			match stack.iter().position(|&t| t == supertrait.trait_index) {
				// Reported from here rather than one frame down, because this
				// is where the bound that closes the loop has a span. A
				// self-referential `trait A: A` lands here too: it is `A`'s
				// own frame that the position finds.
				Some(start) => self.report_supertrait_cycle(
					&stack[start..],
					SourceSpan::new(file_id, supertrait.span),
				),
				None => self
					.resolve_supertrait_clause(supertrait.trait_index, stack),
			}
		}
		stack.pop();
	}

	/// Reports `chain` — the traits from the one the cycle closes back onto
	/// through to the one whose clause `span` is in — as a supertrait cycle.
	///
	/// Reported once per cycle, not once per trait in it: the bounds of every
	/// trait on `chain` are written by the time this runs, so the walk that
	/// found the loop is also the last one to enter it.
	fn report_supertrait_cycle(
		&mut self,
		chain: &[TraitIndex],
		span: SourceSpan,
	) {
		let mut names: Vec<&str> = Vec::with_capacity(chain.len());
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::CyclicSupertrait.code())
			.with_message("cyclic supertrait dependency");
		for &trait_index in chain {
			let trait_def = &self.items.traits[usize::from(trait_index)];
			let name = self.interner.resolve(trait_def.name.inner).unwrap();
			names.push(name);
			diagnostic = diagnostic.with_label(
				SourceSpan::new(trait_def.file_id, trait_def.name.span)
					.secondary_label()
					.with_message(format!("`{name}` is declared here")),
			);
		}
		self.diagnostics.push(
			diagnostic
				.with_label(span.primary_label().with_message(format!(
					"this bound closes the cycle back onto `{}`",
					names[0]
				)))
				.with_note(format!(
					"the cycle is `{}` -> `{}`",
					names.join("` -> `"),
					names[0]
				))
				.with_note(
					"a trait cannot be its own supertrait, directly or \
					 through the chain",
				),
		);
	}

	pub(super) fn signature_trait(
		&mut self,
		trait_index: TraitIndex,
		item: &'ast ast::Item,
	) {
		// The supertrait clause itself is read by
		// `ensure_trait_supertraits`, which may already have run it.
		let (trait_id, attributes) = match item {
			ast::Item::Trait { id, attributes, .. } => (id, attributes),
			_ => unreachable!(),
		};
		// `Trait` has no `attributes` field of its own to store the
		// result in — `#[inline]`/`#[intrinsic]`/`#[fixed_order]`
		// don't apply to traits, and `#[tag = "..."]` (the only one
		// that does) works purely through the global
		// `self.items.tagged_items` map, populated as a side effect
		// here.
		self.resolve_attributes(*trait_id, attributes);
		// Already done if any member got here first — this is idempotent,
		// and it is the only writer of the supertrait half of `Self`'s
		// bounds.
		self.ensure_trait_supertraits(trait_index);
	}

	pub(super) fn signature_trait_function(
		&mut self,
		resolve_context: ResolveContext,
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	) {
		// Supertraits before member: this member's signature can name an
		// associated item inherited from one (`Self::AssocFromSupertrait`),
		// and prescan registers a trait's members *before* the trait
		// itself, so without this the member usually resolves first,
		// against a `Self` that only knows the trait it is declared in.
		// Deliberately not `ensure_signature` on the parent — see
		// `ensure_trait_supertraits`.
		self.ensure_trait_supertraits(trait_index);
		// Self is encoded as TypeParam{0} so default implementations can be
		// monomorphized: type_args[0] = concrete receiver type at the call site.
		if let ast::TraitItem::Function { id, signature, .. } = item {
			// `Self` is owned by the trait; the function inherits it via
			// type_param_parent so type_params holds only explicit params.
			let MemberIndex::Function(func_index) = self.items.traits
				[usize::from(trait_index)]
			.members[&signature.name.inner] else {
				unreachable!()
			};

			let self_type = self.types.intern(Type::TypeParam {
				owner: TypeParamOwner::Trait(trait_index),
				param_index: 0,
			});
			self.resolve_type_param_bounds(
				resolve_context,
				TypeParamOwner::Function(*id),
				Some(self_type),
				&signature.type_params,
			);
			let sig_scope = GenericScope {
				owner: TypeParamOwner::Function(*id),
				self_type: Some(self_type),
			};
			let (params, result) = self.build_function_signature(
				resolve_context,
				Some(sig_scope),
				signature,
			);
			let sig_idx = self.intern_function(&params, result);
			let func = &mut self.items.functions[usize::from(func_index)];
			func.params = params;
			func.result = result;
			func.signature_index = sig_idx;
		}
	}

	pub(super) fn signature_trait_const(
		&mut self,
		resolve_context: ResolveContext,
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	) {
		// Supertraits before member: this member's signature can name an
		// associated item inherited from one (`Self::AssocFromSupertrait`),
		// and prescan registers a trait's members *before* the trait
		// itself, so without this the member usually resolves first,
		// against a `Self` that only knows the trait it is declared in.
		// Deliberately not `ensure_signature` on the parent — see
		// `ensure_trait_supertraits`.
		self.ensure_trait_supertraits(trait_index);
		// Self is a TypeParam owned by the trait so `Self::*mut u8` is valid.
		let self_type_param = self.types.intern(Type::TypeParam {
			owner: TypeParamOwner::Trait(trait_index),
			param_index: 0,
		});
		let self_scope = GenericScope {
			owner: TypeParamOwner::Trait(trait_index),
			self_type: Some(self_type_param),
		};
		if let ast::TraitItem::Const {
			name, ty, value, ..
		} = item
		{
			let ty_idx =
				self.resolve_type(resolve_context, Some(self_scope), ty);
			// A default value's `Self`-relative type (`Self::Size`)
			// is already resolved above into `ty_idx`, an abstract
			// `Type::TypeParam` — building/coercing the value
			// expression against it needs no further generic-scope
			// threading, the same way an ordinary comptime literal
			// already coerces against a typeset-bounded type param
			// (see `test_typeset_intersection_range_literal_in_local`).
			let (value_expr, const_value) = match value {
				Some(value_ast) => match self.build_const_context_expression(
					resolve_context,
					value_ast,
					ty_idx,
				) {
					Ok(value_expr) => {
						let const_value =
							match self.eval_const_expr(&value_expr) {
								Ok(v) => Some(v),
								Err(_) => {
									self.diagnostics.push(
										report_not_const_evaluatable(
											SourceSpan::new(
												resolve_context.file_id,
												value_ast.span,
											),
										),
									);
									None
								}
							};
						(Some(Box::new(value_expr)), const_value)
					}
					Err(_) => (None, None),
				},
				None => (None, None),
			};
			let MemberIndex::Constant(index) = self.items.traits
				[usize::from(trait_index)]
			.members[&name.inner] else {
				unreachable!()
			};
			let constant = &mut self.items.constants[usize::from(index)];
			constant.ty.inner = ty_idx;
			constant.value = value_expr;
			constant.const_value = const_value;
		}
	}

	pub(super) fn signature_trait_impl_block(
		&mut self,
		resolve_context: ResolveContext,
		item: &'ast ast::Item,
	) {
		let (block_id, type_params, trait_name, target, items) = match item {
			ast::Item::TraitImpl {
				id,
				type_params,
				trait_name,
				target,
				items,
			} => (id, type_params, trait_name, target, items),
			_ => unreachable!(),
		};

		let trait_name_span = TextSpan::new(
			trait_name.first().unwrap().ident.span.start,
			trait_name.last().unwrap().ident.span.end,
		);
		let trait_index = match self.resolve_path_segments_as_bound(
			resolve_context,
			trait_name,
			trait_name_span,
		) {
			Ok(BoundKind::Trait(tb)) => tb.trait_index,
			Ok(BoundKind::TypeSet(_)) => {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::ExpectedBound.code())
						.with_message("expected a trait name")
						.with_label(Label::primary(
							resolve_context.file_id,
							trait_name_span,
						)),
				);
				return;
			}
			Err(()) => return,
		};

		let member_decls = self.collect_member_decls(resolve_context, items);

		// Push a placeholder first (target unresolved), same reason
		// as `ImplBlock`/`InherentImplBlock`: resolving the target
		// type expression below needs `TypeParamOwner::TraitImpl(
		// trait_impl_index)` to already have somewhere to record
		// bounds/params against.
		let trait_impl_index = self.items.push_trait_impl(TraitImpl {
			id: *block_id,
			trait_index,
			type_params: type_params
				.iter()
				.map(|tp| TypeParamInfo::new(tp.name))
				.collect(),
			target: Spanned {
				inner: TypeIndex::ERROR,
				span: target.span,
			},
			namespace: resolve_context.namespace,
			members: HashMap::new(),
			member_decls,
			span: trait_name_span,
			file_id: resolve_context.file_id,
			self_accesses: Vec::new(),
		});

		self.resolve_type_param_bounds(
			resolve_context,
			TypeParamOwner::TraitImpl(trait_impl_index),
			None,
			type_params,
		);

		let target_type = self.resolve_signature_type(
			resolve_context,
			Some(GenericScope {
				owner: TypeParamOwner::TraitImpl(trait_impl_index),
				self_type: None,
			}),
			target,
		);
		self.items.trait_impls[usize::from(trait_impl_index)]
			.target
			.inner = target_type;

		self.register_trait_impl(target_type, trait_index, trait_impl_index);

		// Trait-provided members (explicit overrides and bodied
		// defaults) are resolved lazily and ambiguity-checked by
		// `resolve_impl_member` — they are intentionally never
		// written into `impl_block_list`, which is reserved for
		// inherent impls only.
	}

	/// What an `impl` block declares, by name, read straight off the AST.
	///
	/// Runs with the block's own header, before any member's signature: an
	/// impl is reached by type rather than by name, so a lookup that lands on
	/// one cannot ask for a member that has not been resolved yet — it asks
	/// this instead, and forces the single member it needs.
	///
	/// Two members of one block sharing a name is decided here too, and only
	/// here: the first declaration wins and every later one is reported. Once
	/// a lookup can force an arbitrary member out of order, "first" is no
	/// longer whichever happened to resolve first, so the resolved `members`
	/// map cannot be what answers this — declaration order is a property of
	/// the source, and this is the one place that still sees it.
	fn collect_member_decls(
		&mut self,
		resolve_context: ResolveContext,
		items: &[ast::Separated<ast::Spanned<ast::ImplItem>>],
	) -> HashMap<SymbolU32, MemberDecl> {
		let mut decls: HashMap<SymbolU32, MemberDecl> =
			HashMap::with_capacity(items.len());
		for item in items.iter() {
			let (name, kind, id) = match &item.inner.inner {
				ast::ImplItem::Function { id, signature, .. } => {
					(signature.name, MemberKind::Function, *id)
				}
				ast::ImplItem::Constant { id, name, .. } => {
					(*name, MemberKind::Const, *id)
				}
				ast::ImplItem::AssocType { id, name, .. } => {
					(*name, MemberKind::AssocType, *id)
				}
			};
			if let Some(existing) = decls.get(&name.inner) {
				self.diagnostics.push(report_duplicate_definition(
					DuplicateDefinitionDiagnostic {
						name: self.interner.resolve(name.inner).unwrap(),
						namespace: existing.kind.namespace(),
						first_definition: SourceSpan::new(
							resolve_context.file_id,
							existing.span,
						),
						second_definition: SourceSpan::new(
							resolve_context.file_id,
							name.span,
						),
					},
				));
				continue;
			}
			decls.insert(
				name.inner,
				MemberDecl {
					kind,
					id,
					span: name.span,
				},
			);
		}
		decls
	}

	/// Registers `entry` under `name`, unless another member of this block
	/// already claimed that name — `collect_member_decls` decided and reported
	/// that when the header ran, so this only has to honour the outcome.
	/// Which one survives is deliberately not decided by what the trait
	/// declares: an item of the wrong kind no longer masks anything, since
	/// `check_trait_conformance` compares kinds rather than just names.
	fn register_trait_impl_member(
		&mut self,
		trait_impl_index: TraitImplIndex,
		id: ast::DefId,
		name: SymbolU32,
		entry: ImplEntry,
	) {
		let block = &mut self.items.trait_impls[usize::from(trait_impl_index)];
		if block
			.member_decls
			.get(&name)
			.is_some_and(|decl| decl.id != id)
		{
			return;
		}
		block.members.insert(name, entry);
	}

	pub(super) fn signature_trait_impl_function(
		&mut self,
		resolve_context: ResolveContext,
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	) {
		// Parent before member, as in `signature_inherent_impl_const`: in
		// progress means the block forced us, having already resolved
		// everything below reads from it.
		let _ = self.ensure_signature(parent_id);
		let trait_impl_index = match self.items.trait_impl_index(parent_id) {
			Some(idx) => idx,
			None => return,
		};
		let self_type = self.items.trait_impls[usize::from(trait_impl_index)]
			.target
			.inner;
		let inherited_type_param_count = u32::try_from(
			self.items.trait_impls[usize::from(trait_impl_index)]
				.type_params
				.len(),
		)
		.unwrap();
		let self_symbol = self.interner.get_or_intern("self");

		if let ast::ImplItem::Function {
			id,
			pub_span,
			attributes,
			signature,
			..
		} = item
		{
			let attributes = self.resolve_attributes(*id, attributes);
			let func_index = self.items.push_function(Function {
				is_method: signature.params.first().is_some_and(|p| {
					self.interner.resolve(p.inner.inner.name.inner)
						== Some("self")
				}),
				id: *id,
				file_id: resolve_context.file_id,
				namespace: resolve_context.namespace,
				parent: Some(ItemParent::TraitImpl(trait_impl_index)),
				body: None,
				// Own (method-level) type params only — impl-level
				// params are inherited via type_param_parent, same
				// convention as InherentImplFunction.
				type_params: signature
					.type_params
					.iter()
					.map(|tp| TypeParamInfo::new(tp.name))
					.collect(),
				inherited_type_param_count,
				pub_span: *pub_span,
				signature_index: TypeIndex::ERROR,
				name: signature.name,
				accesses: Vec::new(),
				params: Box::new([]),
				result: None,
				attributes,
			});

			// Resolve the method's own param bounds (e.g. `Mem:
			// Memory` in `fn write<Mem: Memory>(...)`)  — without
			// this, resolve_type_identifier can still find the type
			// param by name (it's registered above), but any trait
			// bound on it is silently dropped.
			self.resolve_type_param_bounds(
				resolve_context,
				TypeParamOwner::Function(*id),
				None,
				&signature.type_params,
			);

			let self_scope = GenericScope {
				owner: TypeParamOwner::Function(*id),
				self_type: Some(self_type),
			};
			let (params, result) = self.build_function_signature(
				resolve_context,
				Some(self_scope),
				signature,
			);
			let signature_index = self.intern_function(&params, result);
			let func = &mut self.items.functions[usize::from(func_index)];
			func.params = params;
			func.result = result;
			func.signature_index = signature_index;

			let is_method = signature
				.params
				.first()
				.map(|p| p.inner.inner.name.inner == self_symbol)
				.unwrap_or(false);
			let entry = if is_method {
				ImplEntry::Method(func_index)
			} else {
				ImplEntry::AssocFunction(func_index)
			};
			self.register_trait_impl_member(
				trait_impl_index,
				*id,
				signature.name.inner,
				entry,
			);
		}
	}

	pub(super) fn signature_trait_impl_constant(
		&mut self,
		resolve_context: ResolveContext,
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	) {
		// Parent before member, as in `signature_inherent_impl_const`: in
		// progress means the block forced us, having already resolved
		// everything below reads from it.
		let _ = self.ensure_signature(parent_id);
		let trait_impl_index = match self.items.trait_impl_index(parent_id) {
			Some(idx) => idx,
			None => return,
		};
		let self_type = self.items.trait_impls[usize::from(trait_impl_index)]
			.target
			.inner;

		if let ast::ImplItem::Constant {
			id,
			pub_span: _,
			name,
			ty,
			value,
			attributes,
		} = item
		{
			let attributes = self.resolve_attributes(*id, attributes);
			let self_scope = GenericScope {
				owner: TypeParamOwner::TraitImpl(trait_impl_index),
				self_type: Some(self_type),
			};
			let resolved_ty = match ty {
				Some(te) => {
					self.resolve_type(resolve_context, Some(self_scope), te)
				}
				None => TypeIndex::ERROR,
			};
			if let Ok(value_expr) = self.build_const_context_expression(
				resolve_context,
				value,
				resolved_ty,
			) {
				let const_value = match self.eval_const_expr(&value_expr) {
					Ok(v) => Some(v),
					Err(_) => {
						self.diagnostics.push(report_not_const_evaluatable(
							SourceSpan::new(
								resolve_context.file_id,
								value.span,
							),
						));
						None
					}
				};
				let const_index = self.items.push_constant(Constant {
					id: *id,
					file_id: resolve_context.file_id,
					namespace: resolve_context.namespace,
					parent: Some(ItemParent::TraitImpl(trait_impl_index)),
					pub_span: None,
					name: *name,
					ty: ast::Spanned {
						inner: resolved_ty,
						span: name.span,
					},
					value: Some(Box::new(value_expr)),
					const_value,
					accesses: Vec::new(),
					attributes,
				});
				let entry = ImplEntry::AssocConstant(const_index);
				self.register_trait_impl_member(
					trait_impl_index,
					*id,
					name.inner,
					entry,
				);
			}
		}
	}

	pub(super) fn signature_trait_assoc_type(
		&mut self,
		resolve_context: ResolveContext,
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	) {
		// Supertraits before member: this member's signature can name an
		// associated item inherited from one (`Self::AssocFromSupertrait`),
		// and prescan registers a trait's members *before* the trait
		// itself, so without this the member usually resolves first,
		// against a `Self` that only knows the trait it is declared in.
		// Deliberately not `ensure_signature` on the parent — see
		// `ensure_trait_supertraits`.
		self.ensure_trait_supertraits(trait_index);
		if let ast::TraitItem::AssociatedType { name, bounds, .. } = item {
			let self_type_param = self.types.intern(Type::TypeParam {
				owner: TypeParamOwner::Trait(trait_index),
				param_index: 0,
			});
			let self_scope = GenericScope {
				owner: TypeParamOwner::Trait(trait_index),
				self_type: Some(self_type_param),
			};

			let MemberIndex::AssociatedType(assoc_type_index) =
				self.items.traits[usize::from(trait_index)].members
					[&name.inner]
			else {
				unreachable!()
			};

			let bounds = bounds
				.as_ref()
				.map(|bound| {
					self.resolve_bounds(
						resolve_context,
						Some(self_scope),
						bound,
					)
				})
				.unwrap_or_default();
			self.items.associated_types[usize::from(assoc_type_index)].bounds =
				bounds;
		}
	}

	pub(super) fn signature_trait_impl_assoc_type(
		&mut self,
		resolve_context: ResolveContext,
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	) {
		// Parent before member, as in `signature_inherent_impl_const`: in
		// progress means the block forced us, having already resolved
		// everything below reads from it.
		let _ = self.ensure_signature(parent_id);
		let trait_impl_index = match self.items.trait_impl_index(parent_id) {
			Some(idx) => idx,
			None => return,
		};
		let trait_index =
			self.items.trait_impls[usize::from(trait_impl_index)].trait_index;
		let self_type = self.items.trait_impls[usize::from(trait_impl_index)]
			.target
			.inner;

		if let ast::ImplItem::AssocType {
			id,
			name,
			ty,
			attributes,
			..
		} = item
		{
			let attributes = self.resolve_attributes(*id, attributes);
			// Reserve the arena slot (and its `item_lookup` entry) before
			// resolving `ty`: a mutually-referential definition
			// (`impl C for A { type X = B::X }` next to
			// `impl C for B { type X = A::X }`) re-enters this member's own
			// `ensure_signature` while `ty` resolves, and
			// `report_cyclic_type_dependency` needs the `DefId` to be
			// nameable. The entry is *not* published into the impl's
			// `members` map until `ty` is filled, so `trait_member_via_impl`
			// still observes the cycle and reports it rather than handing
			// back a `ty: None` placeholder.
			let assoc_type_index =
				self.items.push_associated_type(AssociatedType {
					bounds: Bounds::default(),
					accesses: Vec::new(),
					id: *id,
					file_id: resolve_context.file_id,
					namespace: resolve_context.namespace,
					name: *name,
					parent: Some(ItemParent::TraitImpl(trait_impl_index)),
					ty: None,
					attributes,
				});
			let self_scope = GenericScope {
				owner: TypeParamOwner::TraitImpl(trait_impl_index),
				self_type: Some(self_type),
			};
			let concrete_ty =
				self.resolve_type(resolve_context, Some(self_scope), ty);
			self.items.associated_types[usize::from(assoc_type_index)].ty =
				Some(Spanned {
					inner: concrete_ty,
					span: ty.span,
				});
			let entry = ImplEntry::AssocType(assoc_type_index);
			self.register_trait_impl_member(
				trait_impl_index,
				*id,
				name.inner,
				entry,
			);
			if let Some(at) = self
				.items
				.trait_associated_type_mut(trait_index, name.inner)
			{
				at.accesses
					.push(SourceSpan::new(resolve_context.file_id, name.span));
			}
			// Bound conformance is checked later, in
			// `check_trait_conformance` (Phase 3.5) — not here.
		}
	}
}

pub(super) fn report_associated_type_in_inherent_impl(
	span: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::AssociatedTypeInInherentImpl.code())
		.with_message(
			"associated types are not allowed in inherent impl blocks",
		)
		.with_label(span.primary_label())
		.with_note(
			"associated types can only be defined in `impl Trait for Type` blocks",
		)
}
