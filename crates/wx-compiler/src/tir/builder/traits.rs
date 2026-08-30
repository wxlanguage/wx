//! Traits and impls: registering a trait impl against its target type, and
//! Phase 2 for every trait, inherent-impl and trait-impl item — blocks, methods,
//! associated consts and associated types — plus the conformance check that
//! verifies each impl provides everything its trait requires.

use super::*;

impl<'ast> Builder<'ast, '_> {
	/// Registers `trait_impl_index` (already pushed into `tir.trait_impls`,
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
		let Ok(kind) =
			ImplTarget::from_type(&self.tir.types[target_type.as_usize()])
		else {
			let trait_name_sym =
				self.tir.traits[trait_index as usize].name.inner;
			let trait_name = self.interner.resolve(trait_name_sym).unwrap();
			let imp = &self.tir.trait_impls[trait_impl_index as usize];
			let span = SourceSpan::new(imp.file_id, imp.span);
			let type_str = self
				.formatter(self.tir.file_namespaces[imp.file_id.as_usize()])
				.display_type(target_type)
				.unwrap();
			self.tir.diagnostics.push(Diagnostic {
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
		let bucket = self.tir.trait_impl_dispatch.entry(kind).or_default();
		if let Some(&(_, existing_index)) =
			bucket.iter().find(|(ti, _)| *ti == trait_index)
		{
			let trait_name_sym =
				self.tir.traits[trait_index as usize].name.inner;
			let trait_name = self.interner.resolve(trait_name_sym).unwrap();
			let new_impl = &self.tir.trait_impls[trait_impl_index as usize];
			let new_span = SourceSpan::new(new_impl.file_id, new_impl.span);
			let existing_impl = &self.tir.trait_impls[existing_index as usize];
			let existing_span =
				SourceSpan::new(existing_impl.file_id, existing_impl.span);
			self.tir.diagnostics.push(Diagnostic {
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
		enum Violation {
			MissingItem {
				file_id: FileId,
				span: TextSpan,
				item_sym: SymbolU32,
				trait_sym: SymbolU32,
				kind: &'static str,
			},
			MissingSupertrait {
				file_id: FileId,
				span: TextSpan,
				trait_sym: SymbolU32,
				supertrait_sym: SymbolU32,
			},
			/// An item the impl provides that its trait does not declare —
			/// either under no name the trait knows, or under one it declares
			/// as a different kind of item. `declared` is the trait's own
			/// entry in the latter case.
			UnexpectedItem {
				span: SourceSpan,
				item_sym: SymbolU32,
				trait_sym: SymbolU32,
				provided: ImplEntry,
				declared: Option<ImplEntry>,
			},
		}

		let mut violations: Vec<Violation> = Vec::new();

		for ti in &self.tir.trait_impls {
			let trait_ = &self.tir.traits[ti.trait_index as usize];

			// `ti.members` = only what the impl block explicitly provided
			// (unlike `resolve_impl_member`, which also falls back to bodied
			// trait defaults). We use `ti.members` intentionally here: a
			// default method must not satisfy an abstract (no-body) requirement.
			for (&sym, entry) in &trait_.entries {
				// `body.is_none()` distinguishes abstract from default methods.
				// Requires Phase 3 to have populated bodies before this runs.
				let (required, kind) = match entry {
					ImplEntry::Method(fi) => {
						(self.tir.functions[*fi as usize].body.is_none(), "fn")
					}
					ImplEntry::AssocConstant(ci) => (
						self.tir.constants[*ci as usize].value.is_none(),
						"const",
					),
					ImplEntry::AssocType(_) => (true, "type"),
					_ => continue,
				};
				// Kind-aware, not just `contains_key`: an item of the wrong
				// kind under the required name satisfies nothing, and would
				// otherwise mask the requirement being unimplemented. It is
				// reported on its own account below.
				let provided = ti
					.members
					.get(&sym)
					.is_some_and(|provided| provided.is_same_kind(*entry));
				if required && !provided {
					violations.push(Violation::MissingItem {
						file_id: ti.file_id,
						span: ti.span,
						item_sym: sym,
						trait_sym: trait_.name.inner,
						kind,
					});
				}
			}

			// The mirror of the loop above: everything the impl provides has
			// to be something the trait declares, under the same kind. An
			// extra item is unreachable rather than harmless — a trait impl's
			// members are only ever looked up through the trait
			// (`resolve_impl_member`), so nothing could name it.
			for (&sym, provided) in &ti.members {
				let declared = trait_.entries.get(&sym).copied();
				if declared.is_some_and(|entry| entry.is_same_kind(*provided)) {
					continue;
				}
				violations.push(Violation::UnexpectedItem {
					span: provided.def_span(&self.tir),
					item_sym: sym,
					trait_sym: trait_.name.inner,
					provided: *provided,
					declared,
				});
			}

			for supertrait in &trait_.bounds.traits {
				if self
					.tir
					.find_trait_impl(ti.target.inner, supertrait.trait_index)
					.is_none()
				{
					let supertrait_sym = self.tir.traits
						[supertrait.trait_index as usize]
						.name
						.inner;
					violations.push(Violation::MissingSupertrait {
						file_id: ti.file_id,
						span: ti.span,
						trait_sym: trait_.name.inner,
						supertrait_sym,
					});
				}
			}
		}

		for trait_impl_index in 0..self.tir.trait_impls.len() {
			// `.members` is a HashMap keyed by symbol (kept that way for the
			// O(1) point lookups on the hot path in `resolve_impl_member`),
			// so unlike a slice there's no cheap per-index re-derive here.
			// Collecting just the matching `AssocTypeIndex` values — bounded
			// by how many associated types one impl provides, so a handful
			// at most — is the smallest way to end the borrow on `members`
			// before `check_assoc_type_bounds` needs `&mut self` below.
			let assoc_type_indices: Vec<AssocTypeIndex> = self.tir.trait_impls
				[trait_impl_index]
				.members
				.values()
				.copied()
				.filter_map(|entry| match entry {
					ImplEntry::AssocType(idx) => Some(idx),
					_ => None,
				})
				.collect();
			for assoc_type_index in assoc_type_indices {
				let assoc_type_impl = self.tir.assoc_type_impls
					[assoc_type_index as usize]
					.clone();
				let trait_index =
					self.tir.trait_impls[trait_impl_index].trait_index;
				let self_type =
					self.tir.trait_impls[trait_impl_index].target.inner;
				self.check_assoc_type_bounds(
					ResolveContext::new(
						assoc_type_impl.file_id,
						assoc_type_impl.namespace,
					),
					trait_index,
					self_type,
					assoc_type_impl.name,
					assoc_type_impl.ty.unwrap(),
				);
			}
		}

		for v in violations {
			match v {
				Violation::MissingItem {
					file_id,
					span,
					item_sym,
					trait_sym,
					kind,
				} => {
					let item_name = self.interner.resolve(item_sym).unwrap();
					let trait_name = self.interner.resolve(trait_sym).unwrap();
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::MissingTraitImplItem.code(),
							)
							.with_message(format!(
								"missing {} `{}` required by `{}`",
								kind, item_name, trait_name
							))
							.with_label(Label::primary(file_id, span)),
					);
				}
				Violation::UnexpectedItem {
					span,
					item_sym,
					trait_sym,
					provided,
					declared,
				} => {
					let item_name = self.interner.resolve(item_sym).unwrap();
					let trait_name = self.interner.resolve(trait_sym).unwrap();
					let label = span.primary_label();
					let diagnostic = match declared {
						Some(declared) => Diagnostic::error()
							.with_message(format!(
								"`{item_name}` is a {} in this impl, but \
								 trait `{trait_name}` declares it as a {}",
								provided.noun(),
								declared.noun(),
							))
							.with_label(label.with_message(format!(
								"expected a {}",
								declared.noun()
							))),
						None => Diagnostic::error()
							.with_message(format!(
								"{} `{item_name}` is not a member of trait \
								 `{trait_name}`",
								provided.noun(),
							))
							.with_label(label.with_message(format!(
								"not a member of trait `{trait_name}`"
							))),
					};
					self.tir.diagnostics.push(
						diagnostic
							.with_code(DiagnosticCode::NotATraitMember.code()),
					);
				}
				Violation::MissingSupertrait {
					file_id,
					span,
					trait_sym,
					supertrait_sym,
				} => {
					let trait_name = self.interner.resolve(trait_sym).unwrap();
					let supertrait_name =
						self.interner.resolve(supertrait_sym).unwrap();
					self.tir.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::MissingSupertraitImpl.code(),
							)
							.with_message(format!(
								"cannot implement `{}` without implementing supertrait `{}`",
								trait_name, supertrait_name
							))
							.with_label(Label::primary(file_id, span)),
					);
				}
			}
		}
	}

	pub(super) fn signature_inherent_impl_const(
		&mut self,
		resolve_context: ResolveContext,
		block_id: ast::DefId,
		item: &'ast ast::ImplItem,
		block_index: u32,
	) {
		// Ensure the impl block's target is resolved first.
		self.ensure_signature(block_id);

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
			let self_type =
				self.tir.inherent_impls[block_index as usize].target.inner;
			let self_scope = GenericScope {
				owner: TypeParamOwner::ImplBlock(block_index),
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
						self.tir.diagnostics.push(
							report_not_const_evaluatable(SourceSpan::new(
								resolve_context.file_id,
								value.span,
							)),
						);
						None
					}
				};
				let const_index = self.tir.constants.len() as ConstIndex;
				self.tir.constants.push(Constant {
					id: *id,
					file_id: resolve_context.file_id,
					namespace: resolve_context.namespace,
					parent: Some(ItemParent::Impl(self_type)),
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
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Const(const_index));
				self.register_inherent_impl_member(
					resolve_context,
					block_index,
					self_type,
					*name,
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
		block_index: u32,
	) {
		// Ensure the impl block's bounds and target are resolved first.
		self.ensure_signature(block_id);

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
		let self_type =
			self.tir.inherent_impls[block_index as usize].target.inner;
		let inherited_type_param_count = self.tir.inherent_impls
			[block_index as usize]
			.type_params
			.len();

		let attributes = self.resolve_attributes(*id, attributes);
		let func_index = self.tir.functions.len() as u32;

		// Register the function with only its own (method-level) type
		// params. Impl-level params (if any) are inherited via
		// type_param_parent.
		self.tir.functions.push(Function {
			id: *id,
			file_id: resolve_context.file_id,
			namespace: resolve_context.namespace,
			parent: Some(ItemParent::GenericImpl(block_index)),
			body: None,
			type_params: signature
				.type_params
				.iter()
				.map(|tp| TypeParamInfo::new(tp.name))
				.collect(),
			type_param_parent: Some(TypeParamOwner::ImplBlock(block_index)),
			inherited_type_param_count,
			pub_span: *pub_span,
			signature_index: TypeIndex::ERROR,
			name: signature.name,
			accesses: Vec::new(),
			params: Box::new([]),
			result: None,
			attributes,
		});
		self.tir
			.item_lookup
			.insert(*id, ItemIndex::Function(func_index));

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
		let func = &mut self.tir.functions[func_index as usize];
		func.params = params;
		func.result = result;
		func.signature_index = signature_index;

		let entry = if is_method {
			ImplEntry::Method(func_index)
		} else {
			ImplEntry::AssocFunction(func_index)
		};

		self.register_inherent_impl_member(
			resolve_context,
			block_index,
			self_type,
			signature.name,
			entry,
		);
	}

	/// Registers `entry` under `name`, unless the block already has a member
	/// of that name — the first declaration wins and every later one is
	/// reported, matching [`Self::register_trait_impl_member`].
	///
	/// The duplicate is dropped from the dispatch bucket too, not just from
	/// `members`: a second entry there would make the block a candidate twice
	/// over for a name it only answers to once.
	///
	/// A collision with a *different* block counts too, when the two can ever
	/// apply to the same receiver — see [`Self::conflicting_inherent_block`].
	/// `resolve_impl_member` arbitrates between candidates as well, but only
	/// per call site and only where there is one, so a conflict nobody
	/// happens to call would otherwise ship unreported.
	fn register_inherent_impl_member(
		&mut self,
		resolve_context: ResolveContext,
		block_index: u32,
		self_type: TypeIndex,
		name: ast::Spanned<SymbolU32>,
		entry: ImplEntry,
	) {
		let target =
			ImplTarget::from_type(&self.tir.types[self_type.as_usize()]).ok();
		// The block's own members answer first, and separately from the
		// bucket below: a block whose target failed to resolve has no
		// `ImplTarget`, so it never reaches a bucket at all, but its own
		// members can still collide with each other.
		let existing = self.tir.inherent_impls[block_index as usize]
			.members
			.get(&name.inner)
			.copied();
		let existing = existing.or_else(|| {
			let other = self.conflicting_inherent_block(
				target?,
				block_index,
				self_type,
				name.inner,
			)?;
			self.tir.inherent_impls[other as usize]
				.members
				.get(&name.inner)
				.copied()
		});
		if let Some(existing) = existing {
			let namespace = match existing {
				ImplEntry::AssocType(_) => SymbolNamespace::Type,
				_ => SymbolNamespace::Value,
			};
			self.tir.diagnostics.push(report_duplicate_definition(
				DuplicateDefinitionDiagnostic {
					name: self.interner.resolve(name.inner).unwrap(),
					namespace,
					first_definition: existing.def_span(&self.tir),
					second_definition: SourceSpan::new(
						resolve_context.file_id,
						name.span,
					),
				},
			));
			return;
		}

		self.tir.inherent_impls[block_index as usize]
			.members
			.insert(name.inner, entry);
		if let Some(target) = target {
			self.tir
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
		block_index: u32,
		self_type: TypeIndex,
		name: SymbolU32,
	) -> Option<u32> {
		let own_params = self.tir.inherent_impls[block_index as usize]
			.type_params
			.len();
		let bucket = self.tir.inherent_impl_dispatch.get(&(target, name))?;
		bucket.iter().copied().find(|&other| {
			if other == block_index {
				return false;
			}
			let other_block = &self.tir.inherent_impls[other as usize];
			self.tir
				.unify_impl_target(
					own_params,
					self_type,
					other_block.target.inner,
				)
				.is_some() || self
				.tir
				.unify_impl_target(
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
		impl_type_params: &'ast [ast::TypeParam],
		impl_target: &'ast ast::Spanned<ast::TypeExpression>,
		block_index: u32,
	) {
		self.resolve_type_param_bounds(
			resolve_context,
			TypeParamOwner::ImplBlock(block_index),
			None,
			impl_type_params,
		);
		let self_type = self.resolve_signature_type(
			resolve_context,
			Some(GenericScope {
				owner: TypeParamOwner::ImplBlock(block_index),
				self_type: None,
			}),
			impl_target,
		);

		let target = match ImplTarget::from_type(
			&self.tir.types[self_type.as_usize()],
		) {
			Ok(kind) => {
				self.check_inherent_impl_locality(
					resolve_context,
					kind,
					impl_target.span,
				);
				self_type
			}
			Err(_) => {
				self.tir.diagnostics.push(
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
		self.tir.inherent_impls[block_index as usize].target.inner = target;
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
				self.tir.structs[struct_index as usize].namespace
			}
			ImplTarget::Enum(enum_index) => {
				self.tir.enums[enum_index as usize].namespace
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
		self.tir.namespaces[namespace as usize].package
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
		let declaring_package =
			self.tir.namespaces[resolve_context.namespace as usize].package;
		if target_package == declaring_package {
			return;
		}
		self.tir.diagnostics.push(
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

	pub(super) fn signature_trait(
		&mut self,
		resolve_context: ResolveContext,
		trait_index: TraitIndex,
		item: &'ast ast::Item,
	) {
		let (supertraits, trait_id, attributes, items) = match item {
			ast::Item::Trait {
				id,
				supertraits,
				attributes,
				items,
				..
			} => (supertraits, id, attributes, items),
			_ => unreachable!(),
		};
		// `Trait` has no `attributes` field of its own to store the
		// result in — `#[inline]`/`#[intrinsic]`/`#[fixed_order]`
		// don't apply to traits, and `#[tag = "..."]` (the only one
		// that does) works purely through the global
		// `self.tir.tagged_items` map, populated as a side effect
		// here.
		self.resolve_attributes(*trait_id, attributes);
		let bounds = if let Some(spanned) = supertraits {
			self.resolve_bounds(resolve_context, None, spanned)
		} else {
			Bounds::default()
		};

		self.tir.traits[trait_index as usize].bounds = bounds.clone();

		// Force every member's own signature to resolve right along
		// with the trait's — `entries`/`assoc_types` only get
		// populated when a member's own `ensure_signature` (via its
		// own `AstNodeRef::Trait{Function,Const,AssocType}` entry)
		// runs, and callers that demand-pull a trait mid-signature
		// (e.g. resolving `M::Size` for `M: Memory` before `Memory`
		// itself is reached in parse order) only call
		// `ensure_signature` on the trait's own id, expecting that
		// to be transitive over its members.
		for trait_item in items.iter() {
			let member_id = match &trait_item.inner.inner {
				ast::TraitItem::Function { id, .. }
				| ast::TraitItem::Const { id, .. }
				| ast::TraitItem::AssociatedType { id, .. } => *id,
			};
			self.ensure_signature(member_id);
		}

		// `Self` here is this trait's own — a supertrait binding like
		// `trait Foo: Bar where { AssocX = SomeType }` states a
		// constraint that must hold for whatever type ends up
		// implementing `Foo` (and therefore `Bar`), which is exactly
		// `Foo`'s own `Self` placeholder — there's no concrete
		// receiver yet at trait-declaration time.
		let self_type = self.intern_type(Type::TypeParam {
			owner: TypeParamOwner::Trait(trait_index),
			param_index: 0,
		});
		for supertrait in bounds.traits.iter() {
			for (assoc_name, kind) in supertrait.bindings.iter() {
				// Only an equality binding (`AssocX = SomeType`) has
				// a concrete value here to check against `AssocX`'s
				// own declared bounds — a `: Bound` entry has
				// already had that same declared bound folded into
				// it directly by `resolve_bounds`, so there's
				// nothing left to check against a value that
				// doesn't exist.
				let AssocBindingKind::Equals(val_ty) = kind else {
					continue;
				};
				self.check_assoc_type_bounds(
					resolve_context,
					supertrait.trait_index,
					self_type,
					Spanned {
						inner: *assoc_name,
						span: supertrait.span,
					},
					Spanned {
						inner: *val_ty,
						span: supertrait.span,
					},
				);
			}
		}
	}

	pub(super) fn signature_trait_function(
		&mut self,
		resolve_context: ResolveContext,
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	) {
		// Self is encoded as TypeParam{0} so default implementations can be
		// monomorphized: type_args[0] = concrete receiver type at the call site.
		let self_sym = self.interner.get_or_intern("self");
		if let ast::TraitItem::Function {
			id,
			attributes,
			signature,
			..
		} = item
		{
			// `Self` is owned by the trait; the function inherits it via
			// type_param_parent so type_params holds only explicit params.
			let attributes = self.resolve_attributes(*id, attributes);
			let func_index = self.tir.functions.len() as u32;
			self.tir.functions.push(Function {
				id: *id,
				file_id: resolve_context.file_id,
				namespace: resolve_context.namespace,
				parent: Some(ItemParent::Trait(trait_index)),
				body: None,
				pub_span: None,
				type_params: signature
					.type_params
					.iter()
					.map(|tp| TypeParamInfo::new(tp.name))
					.collect(),
				type_param_parent: Some(TypeParamOwner::Trait(trait_index)),
				inherited_type_param_count: 1,
				signature_index: TypeIndex::ERROR,
				name: signature.name,
				accesses: Vec::new(),
				params: Box::new([]),
				result: None,
				attributes,
			});
			self.tir
				.item_lookup
				.insert(*id, ItemIndex::Function(func_index));
			let self_type = self.intern_type(Type::TypeParam {
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
			let func = &mut self.tir.functions[func_index as usize];
			func.params = params;
			func.result = result;
			func.signature_index = sig_idx;
			let is_method = signature
				.params
				.first()
				.map(|p| p.inner.inner.name.inner == self_sym)
				.unwrap_or(false);
			let entry = if is_method {
				ImplEntry::Method(func_index)
			} else {
				ImplEntry::AssocFunction(func_index)
			};
			self.tir.traits[trait_index as usize]
				.entries
				.insert(signature.name.inner, entry);
		}
	}

	pub(super) fn signature_trait_const(
		&mut self,
		resolve_context: ResolveContext,
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	) {
		// Self is a TypeParam owned by the trait so `Self::*mut u8` is valid.
		let self_type_param = self.intern_type(Type::TypeParam {
			owner: TypeParamOwner::Trait(trait_index),
			param_index: 0,
		});
		let self_scope = GenericScope {
			owner: TypeParamOwner::Trait(trait_index),
			self_type: Some(self_type_param),
		};
		if let ast::TraitItem::Const {
			id,
			name,
			ty,
			attributes,
			value,
		} = item
		{
			let ty_idx =
				self.resolve_type(resolve_context, Some(self_scope), ty);
			let attributes = self.resolve_attributes(*id, attributes);
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
									self.tir.diagnostics.push(
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
			// Captured only now, right before the push — building the
			// value expression above can itself demand-drive other
			// items' signatures, which may push their own entries
			// onto `self.tir.constants` first. Snapshotting the
			// index any earlier (as the surrounding TIR structs
			// mostly do, safely, since they never resolve a value
			// expression in between) would go stale the moment that
			// happens, pointing this entry at whatever unrelated
			// constant ended up in the slot instead.
			let const_index = self.tir.constants.len() as ConstIndex;
			self.tir.constants.push(Constant {
				id: *id,
				file_id: resolve_context.file_id,
				namespace: resolve_context.namespace,
				parent: Some(ItemParent::Trait(trait_index)),
				pub_span: None,
				name: *name,
				ty: Spanned {
					inner: ty_idx,
					span: ty.span,
				},
				value: value_expr,
				const_value,
				accesses: Vec::new(),
				attributes,
			});
			self.tir
				.item_lookup
				.insert(*id, ItemIndex::Const(const_index));
			self.tir.traits[trait_index as usize]
				.entries
				.insert(name.inner, ImplEntry::AssocConstant(const_index));
		}
	}

	pub(super) fn signature_trait_impl_block(
		&mut self,
		resolve_context: ResolveContext,
		item: &'ast ast::Item,
	) {
		let (block_id, type_params, trait_name, target) = match item {
			ast::Item::TraitImpl {
				id,
				type_params,
				trait_name,
				target,
				..
			} => (id, type_params, trait_name, target),
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
				self.tir.diagnostics.push(
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

		// Push a placeholder first (target unresolved), same reason
		// as `ImplBlock`/`InherentImplBlock`: resolving the target
		// type expression below needs `TypeParamOwner::TraitImpl(
		// trait_impl_index)` to already have somewhere to record
		// bounds/params against.
		let trait_impl_index = self.tir.trait_impls.len() as TraitImplIndex;
		self.tir.trait_impls.push(TraitImpl {
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
			members: HashMap::new(),
			span: trait_name_span,
			file_id: resolve_context.file_id,
			self_accesses: Vec::new(),
		});
		self.tir
			.item_lookup
			.insert(*block_id, ItemIndex::TraitImpl(trait_impl_index));

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
		self.tir.trait_impls[trait_impl_index as usize].target.inner =
			target_type;

		self.register_trait_impl(target_type, trait_index, trait_impl_index);

		// Trait-provided members (explicit overrides and bodied
		// defaults) are resolved lazily and ambiguity-checked by
		// `resolve_impl_member` — they are intentionally never
		// written into `impl_block_list`, which is reserved for
		// inherent impls only.
	}

	/// Registers `entry` under `name`, unless the impl already has a member of
	/// that name — the first declaration wins and every later one is reported,
	/// rather than the last quietly taking the name over. Which one survives
	/// is deliberately not decided by what the trait declares: an item of the
	/// wrong kind no longer masks anything, since `check_trait_conformance`
	/// compares kinds rather than just names.
	fn register_trait_impl_member(
		&mut self,
		resolve_context: ResolveContext,
		trait_impl_index: TraitImplIndex,
		name: ast::Spanned<SymbolU32>,
		entry: ImplEntry,
	) {
		let existing = self.tir.trait_impls[trait_impl_index as usize]
			.members
			.get(&name.inner)
			.copied();
		if let Some(existing) = existing {
			let namespace = match existing {
				ImplEntry::AssocType(_) => SymbolNamespace::Type,
				_ => SymbolNamespace::Value,
			};
			self.tir.diagnostics.push(report_duplicate_definition(
				DuplicateDefinitionDiagnostic {
					name: self.interner.resolve(name.inner).unwrap(),
					namespace,
					first_definition: existing.def_span(&self.tir),
					second_definition: SourceSpan::new(
						resolve_context.file_id,
						name.span,
					),
				},
			));
			return;
		}
		self.tir.trait_impls[trait_impl_index as usize]
			.members
			.insert(name.inner, entry);
	}

	pub(super) fn signature_trait_impl_function(
		&mut self,
		resolve_context: ResolveContext,
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	) {
		self.ensure_signature(parent_id);
		let trait_impl_index = match self.tir.trait_impl_index(parent_id) {
			Some(idx) => idx,
			None => return,
		};
		let self_type =
			self.tir.trait_impls[trait_impl_index as usize].target.inner;
		let inherited_type_param_count = self.tir.trait_impls
			[trait_impl_index as usize]
			.type_params
			.len();
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
			let func_index = self.tir.functions.len() as u32;
			self.tir.functions.push(Function {
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
				type_param_parent: Some(TypeParamOwner::TraitImpl(
					trait_impl_index,
				)),
				inherited_type_param_count,
				pub_span: *pub_span,
				signature_index: TypeIndex::ERROR,
				name: signature.name,
				accesses: Vec::new(),
				params: Box::new([]),
				result: None,
				attributes,
			});
			self.tir
				.item_lookup
				.insert(*id, ItemIndex::Function(func_index));

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
			let func = &mut self.tir.functions[func_index as usize];
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
				resolve_context,
				trait_impl_index,
				signature.name,
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
		self.ensure_signature(parent_id);
		let trait_impl_index = match self.tir.trait_impl_index(parent_id) {
			Some(idx) => idx,
			None => return,
		};
		let self_type =
			self.tir.trait_impls[trait_impl_index as usize].target.inner;

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
						self.tir.diagnostics.push(
							report_not_const_evaluatable(SourceSpan::new(
								resolve_context.file_id,
								value.span,
							)),
						);
						None
					}
				};
				let const_index = self.tir.constants.len() as ConstIndex;
				self.tir.constants.push(Constant {
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
				self.tir
					.item_lookup
					.insert(*id, ItemIndex::Const(const_index));
				let entry = ImplEntry::AssocConstant(const_index);
				self.register_trait_impl_member(
					resolve_context,
					trait_impl_index,
					*name,
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
		if let ast::TraitItem::AssociatedType {
			id,
			name,
			bounds,
			attributes,
		} = item
		{
			let attributes = self.resolve_attributes(*id, attributes);
			let self_type_param = self.intern_type(Type::TypeParam {
				owner: TypeParamOwner::Trait(trait_index),
				param_index: 0,
			});
			let self_scope = GenericScope {
				owner: TypeParamOwner::Trait(trait_index),
				self_type: Some(self_type_param),
			};

			// Register the assoc type (name, entries, symbol) before
			// resolving its own bounds — a `where` clause can reference
			// this exact assoc type indirectly through a mutually
			// recursive trait (e.g. `trait A { type X: B where { Y =
			// Self } }` next to `trait B { type Y: A where { X = Self }
			// }`), and that reference needs an already-present
			// `assoc_types` entry to record its access against, even
			// though this assoc type's own bounds haven't resolved yet.
			self.tir.traits[trait_index as usize].assoc_types.insert(
				name.inner,
				TraitAssocType {
					id: *id,
					name_span: name.span,
					bounds: Bounds::default(),
					accesses: Vec::new(),
				},
			);
			let assoc_type_index =
				self.tir.assoc_type_impls.len() as AssocTypeIndex;
			self.tir.assoc_type_impls.push(AssocTypeImpl {
				id: *id,
				file_id: resolve_context.file_id,
				namespace: resolve_context.namespace,
				name: *name,
				ty: None,
				attributes,
			});
			self.tir.traits[trait_index as usize]
				.entries
				.insert(name.inner, ImplEntry::AssocType(assoc_type_index));

			// Replace Pending with TraitAssocType only if it's still our
			// own Pending — never clobber a same-named resolved symbol.
			if matches!(
				self.lookup_global_symbol(resolve_context.namespace, (SymbolNamespace::Type, name.inner)),
				Some(SymbolEntry::Pending(d)) if d == *id
			) {
				// Shares the trait's own visibility — trait bodies
				// reject a `pub` qualifier on their own members (see
				// `symbol_kind_is_gated`'s doc comment), so there's
				// no separate span of this assoc type's own to read.
				let trait_pub_span =
					self.tir.traits[trait_index as usize].pub_span;
				self.insert_symbol(
					resolve_context.namespace,
					(SymbolNamespace::Type, name.inner),
					SymbolKind::TraitAssocType {
						trait_index,
						assoc_name: name.inner,
					},
					trait_pub_span,
				);
			}

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
			self.tir.traits[trait_index as usize]
				.assoc_types
				.get_mut(&name.inner)
				.unwrap()
				.bounds = bounds;
		}
	}

	pub(super) fn signature_trait_impl_assoc_type(
		&mut self,
		resolve_context: ResolveContext,
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	) {
		self.ensure_signature(parent_id);
		let trait_impl_index = match self.tir.trait_impl_index(parent_id) {
			Some(idx) => idx,
			None => return,
		};
		let trait_index =
			self.tir.trait_impls[trait_impl_index as usize].trait_index;
		let self_type =
			self.tir.trait_impls[trait_impl_index as usize].target.inner;

		if let ast::ImplItem::AssocType {
			id,
			name,
			ty,
			attributes,
			..
		} = item
		{
			let attributes = self.resolve_attributes(*id, attributes);
			let self_scope = GenericScope {
				owner: TypeParamOwner::TraitImpl(trait_impl_index),
				self_type: Some(self_type),
			};
			let concrete_ty =
				self.resolve_type(resolve_context, Some(self_scope), ty);
			let assoc_type_index =
				self.tir.assoc_type_impls.len() as AssocTypeIndex;
			self.tir.assoc_type_impls.push(AssocTypeImpl {
				id: *id,
				file_id: resolve_context.file_id,
				namespace: resolve_context.namespace,
				name: *name,
				ty: Some(Spanned {
					inner: concrete_ty,
					span: ty.span,
				}),
				attributes,
			});
			let entry = ImplEntry::AssocType(assoc_type_index);
			self.register_trait_impl_member(
				resolve_context,
				trait_impl_index,
				*name,
				entry,
			);
			if let Some(at) = self.tir.traits[trait_index as usize]
				.assoc_types
				.get_mut(&name.inner)
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
