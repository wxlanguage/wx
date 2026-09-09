//! Declaration obligations, checked once after the signature sweep.
//! Reads written TIR bounds; this pass never demands another signature.
//!
//! Two separate questions, both answered once per declaration and never
//! again: whether a written bound is *sayable*
//! ([`check_written_bounds`], a free function because it needs three
//! disjoint `Builder` fields rather than `&mut Builder`, and no
//! subject at all) and whether the declared subject *satisfies* it
//! ([`Builder::check_bounds`] in `bounds.rs`, which this module only feeds).

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
			check_written_bounds(
				&self.items,
				self.interner,
				&mut self.diagnostics,
				&self.items.associated_types[index].bounds,
			);
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
			check_written_bounds(
				&self.items,
				self.interner,
				&mut self.diagnostics,
				&self.items.type_param_info(owner, param_index).bounds,
			);
		}
	}
}

/// Reject what a `where` clause is not allowed to *say*, as opposed to
/// what a type must *satisfy*. Only one rule today: a
/// `where { A: <typeset> }` binding may not add a typeset when the
/// trait's own `type A: <typeset>` declaration already carries one, since
/// [`Bounds`] has a single typeset slot and the second would silently
/// replace it or be dropped.
///
/// This is a property of the written bound alone — no subject, no
/// substitution — so it belongs to the declaration and is reported once
/// here. Checking it from inside `check_bounds` instead meant re-reporting
/// it at every call site that passed through the bound, each copy pointing
/// back at the same declaration.
fn check_written_bounds(
	items: &ItemRegistry,
	interner: &ast::StringInterner,
	out: &mut Vec<Diagnostic<FileId>>,
	bounds: &Bounds,
) {
	for trait_bound in bounds.traits.iter() {
		for binding in trait_bound.bindings.iter() {
			let AssocBindingKind::Bound(inner) = &binding.rhs.inner else {
				continue;
			};
			if inner.typeset.is_some()
				&& let Some(declared) = items
					.trait_associated_type(
						trait_bound.trait_index,
						binding.name.inner,
					)
					.and_then(|assoc| assoc.bounds.typeset)
			{
				out.push(report_redundant_typeset_binding(
					items,
					interner,
					binding,
					trait_bound.trait_index,
					declared.span,
				));
			}
			check_written_bounds(items, interner, out, inner);
		}
	}
}

fn report_redundant_typeset_binding(
	items: &ItemRegistry,
	interner: &ast::StringInterner,
	binding: &AssocBinding,
	trait_index: TraitIndex,
	declared_span: TextSpan,
) -> Diagnostic<FileId> {
	let assoc_name = interner.resolve(binding.name.inner).unwrap().to_string();
	let trait_ = &items.traits[usize::from(trait_index)];
	let trait_name = interner.resolve(trait_.name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::MultipleTypesetBounds.code())
		.with_message(format!(
			"associated type `{assoc_name}` already has a typeset bound from `{trait_name}`'s own declaration"
		))
		.with_label(
			Label::primary(binding.file_id, binding.rhs.span)
				.with_message(
					"this `where` clause cannot add another typeset bound",
				),
		)
		.with_label(
			Label::secondary(trait_.file_id, declared_span).with_message(
				format!(
					"`{assoc_name}`'s typeset bound is already declared here"
				),
			),
		)
}
