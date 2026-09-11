//! Declaration obligations, checked once after the signature sweep.
//! Reads written TIR bounds; this pass never demands another signature.
//!
//! Answers one question per declaration, once: whether the declared subject
//! *satisfies* its written bounds ([`Builder::check_bounds`] in `bounds.rs`,
//! which this module only feeds).

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
			let name = item.name;
			if item.bounds.traits.iter().all(|b| b.bindings.is_empty()) {
				continue;
			}
			let base = self.types.intern(Type::TypeParam {
				owner: TypeParamOwner::Trait(trait_index),
				param_index: 0,
			});
			let subject = self.types.intern(Type::AssocTypeProjection {
				base,
				trait_index,
				assoc_name: name.inner,
			});
			let diagnostics = self.check_bounds(
				context.namespace,
				Subject::new(
					SourceSpan::new(context.file_id, name.span),
					subject,
				),
				BoundOrigin::TraitAssocType {
					trait_index,
					name: name.inner,
				},
				// A declaration checks its bounds as written — nothing has
				// pinned its type parameters to anything yet.
				&[],
			);
			self.diagnostics.extend(diagnostics);
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
			let info = self.items.type_param_info(owner, param_index);
			// Only written refinements need checking here; a bare `T: Trait`
			// bound is a constraint on callers, satisfied by definition.
			if info.bounds.traits.iter().all(|b| b.bindings.is_empty()) {
				continue;
			}
			let name_span = info.name.span;
			let subject = self.types.intern(Type::TypeParam {
				owner,
				param_index: param_index as u32,
			});
			let diagnostics = self.check_bounds(
				context.namespace,
				Subject::new(
					SourceSpan::new(context.file_id, name_span),
					subject,
				),
				BoundOrigin::TypeParam {
					owner,
					index: param_index,
				},
				&[],
			);
			self.diagnostics.extend(diagnostics);
		}
	}
}
