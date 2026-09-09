//! Trait declaration demands and member discovery through abstract bounds.

use super::*;

#[derive(Clone, Copy)]
pub(super) struct TraitMemberCandidate {
	pub trait_index: TraitIndex,
	pub entry: ImplEntry,
}

impl<'ast> Builder<'ast, '_> {
	/// Resolve exactly one declaration, without traversing supertraits or
	/// demanding siblings. `Ok(None)` means absent; `Err` means a diagnosed
	/// signature dependency could not be resolved.
	///
	/// All members have identities from prescan. Associated-type identities
	/// remain usable for recursive projections while bounds resolve; functions
	/// and constants require a completed signature.
	pub(super) fn declared_trait_member(
		&mut self,
		trait_index: TraitIndex,
		name: SymbolU32,
		span: SourceSpan,
	) -> Result<Option<ImplEntry>, ()> {
		let Some(member) = self.items.traits[usize::from(trait_index)]
			.members
			.get(&name)
			.copied()
		else {
			return Ok(None);
		};
		let id = member.id(&self.items);
		let status = self.ensure_signature(id);
		if status == SignatureStatus::Cycle
			&& !matches!(member, MemberIndex::AssociatedType(_))
		{
			self.report_cyclic_type_dependency(id, span);
			return Err(());
		}
		Ok(Some(member.entry(&self.items)))
	}

	/// `receiver`'s directly declared bound traits, with their supertrait
	/// clauses resolved. The temporary list ends the registry borrow before
	/// `ensure_trait_supertraits` mutates the builder.
	fn bound_trait_roots(&mut self, receiver: TypeIndex) -> Vec<TraitIndex> {
		let roots: Vec<_> = self
			.items
			.effective_bounds(&self.types, receiver)
			.map(|bounds| bounds.traits().map(|b| b.trait_index).collect())
			.unwrap_or_default();
		for &root in &roots {
			self.ensure_trait_supertraits(root);
		}
		roots
	}

	/// Every trait `receiver` is bound by, directly or through a supertrait.
	pub(super) fn bound_traits(
		&mut self,
		receiver: TypeIndex,
	) -> Vec<TraitIndex> {
		let roots = self.bound_trait_roots(receiver);
		self.items.reachable_traits(roots).collect()
	}

	/// Whether `needle` is one of `receiver`'s bounds, directly or through a
	/// supertrait. Checks effective direct bounds before walking supertraits.
	pub(super) fn bound_traits_contains(
		&mut self,
		receiver: TypeIndex,
		needle: TraitIndex,
	) -> bool {
		let Some(bounds) = self.items.effective_bounds(&self.types, receiver)
		else {
			return false;
		};
		if bounds.traits().any(|b| b.trait_index == needle) {
			return true;
		}
		let roots = self.bound_trait_roots(receiver);
		self.items.reachable_traits(roots).any(|t| t == needle)
	}

	/// Search abstract bounds, retaining the declaring trait for projections
	/// and diagnostics. `None` preserves expression lookup's existing rule
	/// of considering every member kind; type lookup requests the type namespace.
	pub(super) fn member_via_bounds(
		&mut self,
		receiver: TypeIndex,
		name: SymbolU32,
		namespace: Option<SymbolNamespace>,
		span: SourceSpan,
	) -> Result<CandidateSelection<TraitMemberCandidate>, ()> {
		let mut candidates = CandidateSet::new();
		for trait_index in self.bound_traits(receiver) {
			let Some(member) = self.items.traits[usize::from(trait_index)]
				.members
				.get(&name)
			else {
				continue;
			};
			if namespace.is_some_and(|ns| ns != member.namespace()) {
				continue;
			}
			if let Some(entry) =
				self.declared_trait_member(trait_index, name, span)?
			{
				candidates.insert(
					trait_index,
					TraitMemberCandidate { trait_index, entry },
				);
			}
		}
		Ok(candidates.finish())
	}

	pub(super) fn report_trait_member_ambiguity(
		&mut self,
		context: ResolveContext,
		receiver: TypeIndex,
		name: SymbolU32,
		span: TextSpan,
		candidates: &[TraitMemberCandidate],
	) {
		let formatter = self.formatter(context.namespace);
		let member_name = self.interner.resolve(name).unwrap();
		let type_name = formatter.display_type(receiver).unwrap_or_default();
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::AmbiguousTraitMember.code())
			.with_message("multiple applicable items in scope")
			.with_label(
				SourceSpan::new(context.file_id, span)
					.primary_label()
					.with_message(format!("multiple `{member_name}` found")),
			);
		for candidate in candidates {
			let trait_name = self
				.interner
				.resolve(
					self.items.traits[usize::from(candidate.trait_index)]
						.name
						.inner,
				)
				.unwrap();
			diagnostic = diagnostic.with_label(
				candidate
					.entry
					.def_span(&self.items)
					.secondary_label()
					.with_message(format!(
						"candidate from trait `{trait_name}`"
					)),
			);
		}
		self.diagnostics.push(diagnostic.with_note(format!(
			"use `<{type_name} as Trait>::{member_name}` to specify the declaring trait"
		)));
	}
}
