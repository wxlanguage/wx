//! Trait bounds as source occurrences and merged query results. Each written
//! bound is stored once in the arena; merged sets keep binding references so
//! their source spans remain available as nested requirements are combined.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::index::index_newtype;
use crate::vfs::FileId;

use super::defs::{AssocTypeIdx, DefinitionRegistry, TraitIdx};
use super::signatures::{QueryInfo, SignatureBuilder, SignatureStatus};
use super::types::TypeIndex;

index_newtype!(BoundId);

/// One binding within a source bound. The index is stable because an
/// occurrence's binding slice is immutable after allocation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct BindingRef {
	pub(super) bound: BoundId,
	pub(super) index: u32,
}

/// One resolved trait bound as written, including its source location.
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct SourceTraitBound {
	pub(super) trait_index: TraitIdx,
	pub(super) span: SourceSpan,
	pub(super) bindings: Box<[SourceAssocBinding]>,
}

/// One `Assoc = Type` or `Assoc: Bounds` clause inside a written bound.
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct SourceAssocBinding {
	pub(super) assoc_type_index: AssocTypeIdx,
	pub(super) name: Spanned<SymbolU32>,
	pub(super) kind: BindingRequirement,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum BindingRequirement {
	Equals(Spanned<TypeIndex>),
	Bound(Box<[BoundId]>),
}

/// One trait in a union of implied bounds. `source` is the first
/// occurrence that introduced the trait; bindings hold their own origins.
#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct ImpliedTraitBound {
	pub(super) trait_index: TraitIdx,
	pub(super) source: BoundId,
	pub(super) bindings: Vec<ImpliedAssocBinding>,
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct ImpliedAssocBinding {
	pub(super) source: BindingRef,
	pub(super) kind: ImpliedBindingKind,
	/// Trait requirements on this associated type remain in force even when
	/// an equality supplies its concrete type.
	pub(super) required_bounds: Vec<ImpliedTraitBound>,
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum ImpliedBindingKind {
	Equals(BindingRef),
	Bound,
	Conflicting,
}

#[derive(Default)]
pub(super) struct BoundArena {
	bounds: Vec<SourceTraitBound>,
}

impl BoundArena {
	pub(super) fn push(&mut self, bound: SourceTraitBound) -> BoundId {
		let index = u32::try_from(self.bounds.len())
			.expect("bound arena exceeded u32 index capacity");
		self.bounds.push(bound);
		BoundId::new(index)
	}

	pub(super) fn get(&self, id: BoundId) -> &SourceTraitBound {
		&self.bounds[usize::from(id)]
	}

	pub(super) fn binding(&self, reference: BindingRef) -> &SourceAssocBinding {
		&self.get(reference.bound).bindings[reference.index as usize]
	}
}

impl SignatureBuilder<'_, '_> {
	/// `subject` names the trait, type parameter, or associated type whose
	/// bounds are being merged, for conflict diagnostics.
	pub(super) fn compute_implied_bounds(
		&mut self,
		bounds: &[BoundId],
		subject: SymbolU32,
	) -> Vec<ImpliedTraitBound> {
		let mut conflicts = Vec::new();
		let implied = self.merge_bound_set(bounds, &mut conflicts);
		for conflict in conflicts {
			self.diagnostics.push(report_conflicting_assoc_type_binding(
				self.strings,
				self.defs,
				&self.bounds,
				subject,
				conflict,
			));
		}
		implied
	}

	fn merge_bound_set(
		&mut self,
		bounds: &[BoundId],
		conflicts: &mut Vec<AssocBindingConflict>,
	) -> Vec<ImpliedTraitBound> {
		let mut implied = Vec::new();
		for id in bounds.iter().copied() {
			let bound = self.merged_from_source(id, conflicts);
			let trait_index = bound.trait_index;
			union_trait_bound(&self.bounds, &mut implied, conflicts, bound, id);
			let def_id = self.defs.traits[usize::from(trait_index)].def_id;
			let reference = self.bounds.get(id).span;
			match self.ensure_signature(QueryInfo {
				def_id,
				requested_at: Some(reference),
			}) {
				// Already have `trait_index`; this call is purely to force
				// `self.traits[trait_index]` to be populated below.
				SignatureStatus::Resolved(_) => {}
				SignatureStatus::Cycle => {
					let diagnostic = self
						.report_cyclic_implied_trait_bounds(def_id, reference);
					self.diagnostics.push(diagnostic);
					continue;
				}
				SignatureStatus::CycleReported => continue,
			}

			let trait_env = self.traits[usize::from(trait_index)].env;
			let trait_bounds =
				&self.param_bounds[usize::from(trait_env)][0].implied_bounds;
			for inherited in trait_bounds.iter().cloned() {
				// Borrowed from the trait's own cached signature, which must
				// survive for future queries against it — this is the one
				// place this data is genuinely shared, so it's the one place
				// that actually needs to clone it.
				union_trait_bound(
					&self.bounds,
					&mut implied,
					conflicts,
					inherited,
					id,
				);
			}
		}
		implied
	}

	fn merged_from_source(
		&mut self,
		id: BoundId,
		conflicts: &mut Vec<AssocBindingConflict>,
	) -> ImpliedTraitBound {
		let source = self.bounds.get(id);
		let trait_index = source.trait_index;
		let binding_count = source.bindings.len();
		let mut bindings = Vec::with_capacity(binding_count);
		for index in 0..binding_count {
			let reference = BindingRef {
				bound: id,
				index: u32::try_from(index)
					.expect("bound binding count exceeded u32 capacity"),
			};
			let (kind, nested_ids) = match &self.bounds.binding(reference).kind
			{
				BindingRequirement::Equals(_) => {
					(ImpliedBindingKind::Equals(reference), None)
				}
				BindingRequirement::Bound(ids) => {
					(ImpliedBindingKind::Bound, Some(ids.to_vec()))
				}
			};
			bindings.push(ImpliedAssocBinding {
				source: reference,
				kind,
				required_bounds: nested_ids
					.map(|ids| self.merge_bound_set(&ids, conflicts))
					.unwrap_or_default(),
			});
		}
		ImpliedTraitBound {
			trait_index,
			source: id,
			bindings,
		}
	}
}

struct AssocBindingConflict {
	first: BindingRef,
	second: BindingRef,
	/// The written bound whose expansion brought the two values together.
	merge_point: BoundId,
}

pub(super) fn equals_type(
	arena: &BoundArena,
	reference: BindingRef,
) -> TypeIndex {
	let BindingRequirement::Equals(value) = &arena.binding(reference).kind
	else {
		unreachable!("merged equality points to a source equality")
	};
	value.inner
}

fn union_trait_bound(
	arena: &BoundArena,
	accum: &mut Vec<ImpliedTraitBound>,
	conflicts: &mut Vec<AssocBindingConflict>,
	bound: ImpliedTraitBound,
	merge_point: BoundId,
) {
	let existing = match accum
		.iter_mut()
		.find(|b| b.trait_index == bound.trait_index)
	{
		Some(existing) => existing,
		None => {
			accum.push(bound);
			return;
		}
	};

	// A repeated plain trait bound contributes no associated-type facts.
	if bound.bindings.is_empty() {
		return;
	}
	if existing.bindings.is_empty() {
		existing.bindings = bound.bindings;
		return;
	}

	for incoming in bound.bindings {
		let assoc_type_index = arena.binding(incoming.source).assoc_type_index;
		match existing.bindings.iter().position(|b| {
			arena.binding(b.source).assoc_type_index == assoc_type_index
		}) {
			None => existing.bindings.push(incoming),
			Some(index) => {
				let merged = &mut existing.bindings[index];
				for required in incoming.required_bounds {
					union_trait_bound(
						arena,
						&mut merged.required_bounds,
						conflicts,
						required,
						merge_point,
					);
				}
				match (&mut merged.kind, incoming.kind) {
					(ImpliedBindingKind::Conflicting, _) => {}
					(kind, ImpliedBindingKind::Conflicting) => {
						*kind = ImpliedBindingKind::Conflicting;
					}
					(
						ImpliedBindingKind::Equals(first),
						ImpliedBindingKind::Equals(second),
					) if equals_type(arena, *first)
						!= equals_type(arena, second) =>
					{
						conflicts.push(AssocBindingConflict {
							first: *first,
							second,
							merge_point,
						});
						merged.kind = ImpliedBindingKind::Conflicting;
					}
					(
						kind @ ImpliedBindingKind::Bound,
						ImpliedBindingKind::Equals(second),
					) => {
						*kind = ImpliedBindingKind::Equals(second);
					}
					(
						ImpliedBindingKind::Equals(_),
						ImpliedBindingKind::Bound,
					)
					| (
						ImpliedBindingKind::Equals(_),
						ImpliedBindingKind::Equals(_),
					)
					| (ImpliedBindingKind::Bound, ImpliedBindingKind::Bound) => {}
				}
			}
		}
	}
}

pub(super) fn report_expected_trait_bound(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	noun: &str,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::ExpectedTraitBound.code())
		.with_message(format!("expected trait, found {noun} `{name_str}`"))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("not a trait"),
		)
}

pub(super) fn report_duplicate_assoc_type_binding(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateAssocTypeBinding.code())
		.with_message(format!(
			"associated type `{name_str}` is bound more than once in this `where` clause"
		))
		.with_label(
			SourceSpan::new(file_id, name.span)
				.primary_label()
				.with_message("duplicate binding"),
		)
}

/// Two paths reaching the same trait pin one associated type to
/// incompatible values. The references retain both original value spans.
fn report_conflicting_assoc_type_binding(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	arena: &BoundArena,
	subject: SymbolU32,
	conflict: AssocBindingConflict,
) -> Diagnostic<FileId> {
	let first = arena.binding(conflict.first);
	let second = arena.binding(conflict.second);
	let BindingRequirement::Equals(first_value) = &first.kind else {
		unreachable!("conflict points to a source equality")
	};
	let BindingRequirement::Equals(second_value) = &second.kind else {
		unreachable!("conflict points to a source equality")
	};
	let subject_str = strings.resolve(subject).unwrap();
	let trait_index = arena.get(conflict.first.bound).trait_index;
	let trait_name = defs.traits[usize::from(trait_index)].name.inner;
	let trait_str = strings.resolve(trait_name).unwrap();
	let assoc_str = strings.resolve(first.name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicateAssocTypeBinding.code())
		.with_message(format!(
			"`{subject_str}` requires conflicting bindings for `{trait_str}::{assoc_str}`"
		))
		.with_label(
			SourceSpan::new(
				arena.get(conflict.second.bound).span.file_id,
				second_value.span,
			)
				.primary_label()
				.with_message("conflicting value bound here"),
		)
		.with_label(
			SourceSpan::new(
				arena.get(conflict.first.bound).span.file_id,
				first_value.span,
			)
				.secondary_label()
				.with_message("first bound to this value here"),
		)
		.with_label(
			arena
				.get(conflict.merge_point)
				.span
				.secondary_label()
				.with_message("bounds merged here"),
		)
}

pub(super) fn report_not_an_associated_type(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	trait_name: SymbolU32,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	let trait_str = strings.resolve(trait_name).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitMember.code())
		.with_message(format!(
			"`{name_str}` is not an associated type of trait `{trait_str}`"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}
