//! Declaration obligations, checked once after the signature sweep.
//! Reads written TIR bounds; this pass never demands another signature.

use super::*;

impl Builder<'_, '_> {
	pub(super) fn validate_declarations(&mut self) {
		debug_assert!(
			self.sig_state
				.values()
				.all(|entry| matches!(entry.state, ComputeState::Done)),
			"declaration validation requires completed signatures"
		);
		for index in 0..self.items.functions.len() {
			let item = &self.items.functions[index];
			let context = ResolveContext::new(item.file_id, item.namespace);
			self.validate_owner_bounds(
				context,
				TypeParamOwner::Function(item.id),
			);
		}
		for index in 0..self.items.structs.len() {
			let item = &self.items.structs[index];
			let context = ResolveContext::new(item.file_id, item.namespace);
			self.validate_owner_bounds(
				context,
				TypeParamOwner::Struct(item.id),
			);
		}
		for index in 0..self.items.type_aliases.len() {
			let item = &self.items.type_aliases[index];
			let context = ResolveContext::new(item.file_id, item.namespace);
			self.validate_owner_bounds(
				context,
				TypeParamOwner::TypeAlias(item.id),
			);
		}
		for index in 0..self.items.inherent_impls.len() {
			let item = &self.items.inherent_impls[index];
			let context = ResolveContext::new(item.file_id, item.namespace);
			self.validate_owner_bounds(
				context,
				TypeParamOwner::InherentImpl(InherentImplIndex(index as u32)),
			);
		}
		for index in 0..self.items.trait_impls.len() {
			let item = &self.items.trait_impls[index];
			let context = ResolveContext::new(item.file_id, item.namespace);
			self.validate_owner_bounds(
				context,
				TypeParamOwner::TraitImpl(TraitImplIndex(index as u32)),
			);
		}
		for index in 0..self.items.traits.len() {
			let item = &self.items.traits[index];
			let context = ResolveContext::new(item.file_id, item.namespace);
			self.validate_owner_bounds(
				context,
				TypeParamOwner::Trait(TraitIndex(index as u32)),
			);
		}
		for index in 0..self.items.associated_types.len() {
			let item = &self.items.associated_types[index];
			let Some(ItemParent::Trait(trait_index)) = item.parent else {
				continue;
			};
			let context = ResolveContext::new(item.file_id, item.namespace);
			let name = item.name.inner;
			let bounds = item.bounds.clone();
			if bounds.traits.iter().all(|bound| bound.bindings.is_empty()) {
				continue;
			}
			let base = self.types.intern(Type::TypeParam {
				owner: TypeParamOwner::Trait(trait_index),
				param_index: 0,
			});
			let projection = self.types.intern(Type::AssocTypeProjection {
				base,
				trait_index,
				assoc_name: name,
			});
			self.check_bound_bindings(context, projection, &bounds.traits);
		}
	}

	fn validate_owner_bounds(
		&mut self,
		context: ResolveContext,
		owner: TypeParamOwner,
	) {
		let offset = self.inherited_type_param_count(owner) as usize;
		for local_index in 0..self.owner_type_params(owner).len() {
			let param_index = offset + local_index;
			// Release the registry borrow before the checker writes diagnostics
			// and interns temporary projection types. No deferred storage is needed.
			let bounds = self
				.items
				.type_param_info(owner, param_index)
				.bounds
				.clone();
			if bounds.traits.iter().all(|bound| bound.bindings.is_empty()) {
				continue;
			}
			let subject = self.types.intern(Type::TypeParam {
				owner,
				param_index: param_index as u32,
			});
			self.check_bound_bindings(context, subject, &bounds.traits);
		}
	}

	/// Validate written TIR constraints after the declaration's bounds are stored.
	pub(super) fn check_bound_bindings(
		&mut self,
		resolve_context: ResolveContext,
		self_type: TypeIndex,
		bounds: &[TraitBound],
	) {
		for bound in bounds {
			for binding in &bound.bindings {
				let context = ResolveContext::new(
					binding.file_id,
					resolve_context.namespace,
				);
				match &binding.rhs.inner {
					AssocBindingKind::Equals(ty) => self
						.check_assoc_type_bounds(
							context,
							bound.trait_index,
							self_type,
							binding.name,
							Spanned {
								inner: *ty,
								span: binding.rhs.span,
							},
						),
					AssocBindingKind::Bound(required) => {
						self.check_binding_typeset(
							context,
							bound.trait_index,
							binding,
							required,
						);
						let projection =
							self.types.intern(Type::AssocTypeProjection {
								base: self_type,
								trait_index: bound.trait_index,
								assoc_name: binding.name.inner,
							});
						self.check_bound_bindings(
							context,
							projection,
							&required.traits,
						);
					}
				}
			}
		}
	}

	fn check_binding_typeset(
		&mut self,
		context: ResolveContext,
		trait_index: TraitIndex,
		binding: &AssocBinding,
		required: &Bounds,
	) {
		if required.typeset.is_none() {
			return;
		}
		let Some(declared) = self
			.items
			.trait_associated_type(trait_index, binding.name.inner)
		else {
			return;
		};
		let Some(typeset) = declared.bounds.typeset else {
			return;
		};
		let assoc_name = self.interner.resolve(binding.name.inner).unwrap();
		let owner = &self.items.traits[usize::from(trait_index)];
		let trait_name = self.interner.resolve(owner.name.inner).unwrap();
		self.diagnostics.push(Diagnostic::error()
			.with_code(DiagnosticCode::MultipleTypesetBounds.code())
			.with_message(format!("associated type `{assoc_name}` already has a typeset bound from `{trait_name}`'s own declaration"))
			.with_label(Label::primary(context.file_id, binding.rhs.span)
				.with_message("this `where` clause cannot add another typeset bound"))
			.with_label(Label::secondary(owner.file_id, typeset.span)
				.with_message(format!("`{assoc_name}`'s typeset bound is already declared here"))));
	}
}
