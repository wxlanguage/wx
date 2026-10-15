//! Trait bounds as source occurrences and merged query results. Each written
//! bound is stored once in the arena; merged sets keep binding references so
//! their source spans remain available as nested requirements are combined.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::index::index_newtype;
use crate::vfs::FileId;

use super::defs::{AssocTypeIdx, DefId, DefKind, DefinitionRegistry, TraitIdx};
use super::signatures::{QueryInfo, SignatureStatus, TypeContext};
use super::types::{Substitution, Type, TypeIndex, TypeInterner};

index_newtype!(BoundId);

/// One binding within a source bound. The index is stable because an
/// occurrence's completed binding slice is immutable after publication.
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
	pub(super) assoc_type_index: AssocTypeIdx,
	pub(super) kind: ImpliedBindingKind,
	/// Trait requirements on this associated type remain in force even when
	/// an equality supplies its concrete type.
	pub(super) required_bounds: Vec<ImpliedTraitBound>,
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) struct EqualityFact {
	pub(super) source: BindingRef,
	pub(super) value: TypeIndex,
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum ImpliedBindingKind {
	Equals(EqualityFact),
	/// Distinct symbolic values are not yet evidence of a conflict.
	Ambiguous(Vec<EqualityFact>),
	Bound,
	Conflicting,
}

/// The lifecycle of a subject's effective bound facts. Direct/inherited
/// memberships are published (via `provisional_from_occurrences`) before
/// equality RHS types are resolved, so sibling-bound resolution can read a
/// `Provisional` table; a reader that needs the completed equalities
/// (normalization, satisfaction) must wait for `Ready`. Replaces a separate
/// `facts_ready: bool` next to the facts it describes — the two could never
/// drift out of sync by construction this way, and a caller can't read one
/// without naming which state it's prepared to handle.
#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub(super) enum BoundFacts {
	Provisional(Box<[ImpliedTraitBound]>),
	Ready(Box<[ImpliedTraitBound]>),
}

impl BoundFacts {
	pub(super) fn empty() -> Self {
		BoundFacts::Provisional(Box::new([]))
	}

	/// The best-known facts so far, regardless of readiness — for consumers
	/// (sibling-bound resolution, membership-only lookup) that are allowed
	/// to read a provisional table.
	pub(super) fn current(&self) -> &[ImpliedTraitBound] {
		match self {
			BoundFacts::Provisional(facts) | BoundFacts::Ready(facts) => facts,
		}
	}

	pub(super) fn is_ready(&self) -> bool {
		matches!(self, BoundFacts::Ready(_))
	}

	/// Takes the current facts out for merging, leaving an empty
	/// provisional placeholder behind — mirrors `std::mem::take`, which a
	/// bare `Box<[ImpliedTraitBound]>` field supported directly but an enum
	/// needs a named replacement value for.
	pub(super) fn take(&mut self) -> Vec<ImpliedTraitBound> {
		match std::mem::replace(self, BoundFacts::empty()) {
			BoundFacts::Provisional(facts) | BoundFacts::Ready(facts) => {
				facts.into_vec()
			}
		}
	}
}

#[derive(Default)]
pub(super) struct BoundArena {
	bounds: Vec<BoundEntry>,
}

/// Construction state belongs to the arena, not to a written requirement.
/// A reservation carries only the identity and location needed by membership
/// lookup; the AST retains the unresolved binding expressions.
enum BoundEntry {
	Reserved {
		trait_index: TraitIdx,
		span: SourceSpan,
	},
	Resolved(SourceTraitBound),
}

impl BoundArena {
	fn next_id(&self) -> BoundId {
		BoundId::new(
			u32::try_from(self.bounds.len())
				.expect("bound arena exceeded u32 index capacity"),
		)
	}

	pub(super) fn reserve(
		&mut self,
		trait_index: TraitIdx,
		span: SourceSpan,
	) -> BoundId {
		let id = self.next_id();
		self.bounds.push(BoundEntry::Reserved { trait_index, span });
		id
	}

	pub(super) fn span(&self, id: BoundId) -> SourceSpan {
		match &self.bounds[usize::from(id)] {
			BoundEntry::Reserved { span, .. } => *span,
			BoundEntry::Resolved(bound) => bound.span,
		}
	}

	pub(super) fn trait_index(&self, id: BoundId) -> TraitIdx {
		match &self.bounds[usize::from(id)] {
			BoundEntry::Reserved { trait_index, .. } => *trait_index,
			BoundEntry::Resolved(bound) => bound.trait_index,
		}
	}

	pub(super) fn fill(&mut self, id: BoundId, bound: SourceTraitBound) {
		let slot = &mut self.bounds[usize::from(id)];
		let BoundEntry::Reserved { trait_index, span } = slot else {
			panic!("source bounds are immutable after publication")
		};
		assert_eq!(*trait_index, bound.trait_index);
		assert_eq!(*span, bound.span);
		*slot = BoundEntry::Resolved(bound);
	}

	pub(super) fn get(&self, id: BoundId) -> &SourceTraitBound {
		match &self.bounds[usize::from(id)] {
			BoundEntry::Resolved(bound) => bound,
			BoundEntry::Reserved { .. } => {
				panic!("source bound has not finished resolving")
			}
		}
	}

	pub(super) fn binding(&self, reference: BindingRef) -> &SourceAssocBinding {
		&self.get(reference.bound).bindings[reference.index as usize]
	}
}

impl TypeContext<'_, '_, '_> {
	/// Merge completed source facts, including inherited bounds.
	pub(super) fn compute_implied_bounds(
		&mut self,
		bounds: &[BoundId],
		subject: SymbolU32,
		subject_type: TypeIndex,
	) -> Vec<ImpliedTraitBound> {
		let mut conflicts = Vec::new();
		let mut implied = Vec::new();
		for &id in bounds {
			let bound =
				self.implied_from_source(id, subject_type, &mut conflicts);
			self.merge_implied_bound(
				&mut implied,
				bound,
				subject_type,
				&mut conflicts,
			);
		}
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

	/// Complete the membership closure in the existing effective-bound tree.
	/// Direct memberships come from `provisional_from_occurrences`, without
	/// equality RHS values — a `Provisional` `BoundFacts` prevents a reader
	/// from mistaking this reduction for the completed one.
	pub(super) fn merge_implied_memberships(
		&mut self,
		bounds: Vec<ImpliedTraitBound>,
		subject: TypeIndex,
	) -> Vec<ImpliedTraitBound> {
		let mut implied = Vec::new();
		let mut conflicts = Vec::new();
		for mut bound in bounds {
			for binding in &mut bound.bindings {
				if binding.required_bounds.is_empty() {
					continue;
				}
				let projected = self.types.intern(Type::AssocTypeProjection {
					base: subject,
					trait_index: bound.trait_index,
					assoc_type_index: binding.assoc_type_index,
				});
				binding.required_bounds = self.merge_implied_memberships(
					std::mem::take(&mut binding.required_bounds),
					projected,
				);
			}
			self.merge_implied_bound(
				&mut implied,
				bound,
				subject,
				&mut conflicts,
			);
		}
		implied
	}

	fn merge_implied_bound(
		&mut self,
		implied: &mut Vec<ImpliedTraitBound>,
		bound: ImpliedTraitBound,
		subject: TypeIndex,
		conflicts: &mut Vec<AssocBindingConflict>,
	) {
		let trait_index = bound.trait_index;
		let id = bound.source;
		union_trait_bound(&self.types, implied, conflicts, bound, id);
		let def_id = match self.defs.traits[usize::from(trait_index)].typeset {
			Some(typeset_index) => DefId::Typeset(typeset_index),
			None => DefId::Trait(trait_index),
		};
		let reference = self.bounds.span(id);
		match self.ensure_signature(QueryInfo {
			def_id,
			requested_at: Some(reference),
		}) {
			SignatureStatus::Available(_) => {}
			SignatureStatus::Cycle => {
				let diagnostic =
					self.report_cyclic_implied_trait_bounds(def_id, reference);
				self.diagnostics.push(diagnostic);
				return;
			}
			SignatureStatus::CycleReported => return,
		}
		let trait_env = self.traits[usize::from(trait_index)].env;
		let substitution = Substitution {
			env: trait_env,
			args: &[subject],
		};
		let count = self.param_bounds[usize::from(trait_env)][0]
			.facts
			.current()
			.len();
		for index in 0..count {
			let source = &self.param_bounds[usize::from(trait_env)][0]
				.facts
				.current()[index];
			let inherited =
				instantiate_bound(&mut self.types, source, &substitution);
			union_trait_bound(&self.types, implied, conflicts, inherited, id);
		}
	}

	fn implied_from_source(
		&mut self,
		id: BoundId,
		subject: TypeIndex,
		conflicts: &mut Vec<AssocBindingConflict>,
	) -> ImpliedTraitBound {
		let source = self.bounds.get(id);
		let trait_index = source.trait_index;
		let count = source.bindings.len();
		let mut bindings = Vec::with_capacity(count);
		for index in 0..count {
			let reference = BindingRef {
				bound: id,
				index: u32::try_from(index)
					.expect("bound binding count exceeded u32 capacity"),
			};
			let binding = self.bounds.binding(reference);
			let assoc_type_index = binding.assoc_type_index;
			let kind = match binding.kind {
				BindingRequirement::Equals(value) => {
					ImpliedBindingKind::Equals(EqualityFact {
						source: reference,
						value: value.inner,
					})
				}
				BindingRequirement::Bound(_) => ImpliedBindingKind::Bound,
			};
			let mut required_bounds = Vec::new();
			if let BindingRequirement::Bound(ids) = &binding.kind {
				let count = ids.len();
				let projected = self.types.intern(Type::AssocTypeProjection {
					base: subject,
					trait_index,
					assoc_type_index,
				});
				for nested_index in 0..count {
					// Re-read stable handles across recursion instead of cloning IDs.
					let BindingRequirement::Bound(ids) =
						&self.bounds.binding(reference).kind
					else {
						unreachable!()
					};
					let nested_id = ids[nested_index];
					let nested = self
						.implied_from_source(nested_id, projected, conflicts);
					self.merge_implied_bound(
						&mut required_bounds,
						nested,
						projected,
						conflicts,
					);
				}
			}
			bindings.push(ImpliedAssocBinding {
				assoc_type_index,
				kind,
				required_bounds,
			});
		}
		ImpliedTraitBound {
			trait_index,
			source: id,
			bindings,
		}
	}
}

impl TypeContext<'_, '_, '_> {
	/// Demand declaration bounds only where a projected receiver needs them.
	/// A published provisional table is usable for identity/membership lookup,
	/// but does not authorize equality reduction.
	pub(super) fn prepare_effective_bounds(
		&mut self,
		mut receiver: TypeIndex,
		reference: SourceSpan,
	) -> Result<(), ()> {
		while let Type::AssocTypeProjection {
			base,
			assoc_type_index,
			..
		} = *self.types.resolve(receiver)
		{
			if self.assoc_types[usize::from(assoc_type_index)].is_none() {
				self.ensure_assoc_type_bounds(assoc_type_index, reference)?;
			}
			receiver = base;
		}
		Ok(())
	}
}

struct AssocBindingConflict {
	first: BindingRef,
	second: BindingRef,
	/// The written bound whose expansion brought the two values together.
	merge_point: BoundId,
}

/// Builds a substituted copy of a cached inherited-bound tree in one pass —
/// the copy and the substitution used to be two separate full traversals
/// (`clone()` then a mutating walk); a caller that needs an owned,
/// already-substituted tree gets it from one recursive walk instead.
fn instantiate_bound(
	types: &mut TypeInterner,
	bound: &ImpliedTraitBound,
	substitution: &Substitution<'_>,
) -> ImpliedTraitBound {
	ImpliedTraitBound {
		trait_index: bound.trait_index,
		source: bound.source,
		bindings: bound
			.bindings
			.iter()
			.map(|binding| ImpliedAssocBinding {
				assoc_type_index: binding.assoc_type_index,
				kind: instantiate_binding_kind(
					types,
					&binding.kind,
					substitution,
				),
				required_bounds: binding
					.required_bounds
					.iter()
					.map(|nested| {
						instantiate_bound(types, nested, substitution)
					})
					.collect(),
			})
			.collect(),
	}
}

fn instantiate_binding_kind(
	types: &mut TypeInterner,
	kind: &ImpliedBindingKind,
	substitution: &Substitution<'_>,
) -> ImpliedBindingKind {
	match kind {
		ImpliedBindingKind::Equals(fact) => {
			ImpliedBindingKind::Equals(EqualityFact {
				source: fact.source,
				value: types.substitute(fact.value, substitution),
			})
		}
		ImpliedBindingKind::Ambiguous(facts) => ImpliedBindingKind::Ambiguous(
			facts
				.iter()
				.map(|fact| EqualityFact {
					source: fact.source,
					value: types.substitute(fact.value, substitution),
				})
				.collect(),
		),
		ImpliedBindingKind::Bound => ImpliedBindingKind::Bound,
		ImpliedBindingKind::Conflicting => ImpliedBindingKind::Conflicting,
	}
}

/// Only incompatible outer constructors establish a conflict here. Symbolic
/// values and differing arguments remain unavailable for reduction; semantic
/// equality checking belongs to a later phase.
fn known_distinct(types: &TypeInterner, a: TypeIndex, b: TypeIndex) -> bool {
	let (a, b) = (types.resolve(a), types.resolve(b));
	if matches!(
		a,
		Type::Error
			| Type::Infer
			| Type::Integer
			| Type::Float
			| Type::TypeParam { .. }
			| Type::AssociatedType { .. }
			| Type::AssocTypeProjection { .. }
	) || matches!(
		b,
		Type::Error
			| Type::Infer
			| Type::Integer
			| Type::Float
			| Type::TypeParam { .. }
			| Type::AssociatedType { .. }
			| Type::AssocTypeProjection { .. }
	) {
		return false;
	}
	match (a, b) {
		(
			Type::Struct {
				struct_index: a, ..
			},
			Type::Struct {
				struct_index: b, ..
			},
		) => a != b,
		(Type::Tuple { elements: a }, Type::Tuple { elements: b }) => {
			a.len() != b.len()
		}
		_ => std::mem::discriminant(a) != std::mem::discriminant(b),
	}
}

/// Adds one equality fact to a binding's known set, checking it against
/// every fact already present. The only place `known_distinct` runs, so
/// every merge path — regardless of whether the binding started at `Bound`,
/// `Equals`, or `Ambiguous` — gets the same conflict check instead of each
/// transition needing to remember it separately.
fn add_equality_fact(
	types: &TypeInterner,
	kind: &mut ImpliedBindingKind,
	incoming: EqualityFact,
	conflicts: &mut Vec<AssocBindingConflict>,
	merge_point: BoundId,
) {
	let existing: &[EqualityFact] = match kind {
		ImpliedBindingKind::Conflicting => return,
		ImpliedBindingKind::Bound => &[],
		ImpliedBindingKind::Equals(fact) => std::slice::from_ref(fact),
		ImpliedBindingKind::Ambiguous(facts) => facts,
	};

	if let Some(conflict) = existing
		.iter()
		.find(|fact| known_distinct(types, fact.value, incoming.value))
	{
		conflicts.push(AssocBindingConflict {
			first: conflict.source,
			second: incoming.source,
			merge_point,
		});
		*kind = ImpliedBindingKind::Conflicting;
		return;
	}
	if existing.iter().any(|fact| fact.value == incoming.value) {
		return;
	}
	*kind = match std::mem::replace(kind, ImpliedBindingKind::Bound) {
		ImpliedBindingKind::Bound => ImpliedBindingKind::Equals(incoming),
		ImpliedBindingKind::Equals(first) => {
			ImpliedBindingKind::Ambiguous(vec![first, incoming])
		}
		ImpliedBindingKind::Ambiguous(mut facts) => {
			facts.push(incoming);
			ImpliedBindingKind::Ambiguous(facts)
		}
		ImpliedBindingKind::Conflicting => unreachable!("handled above"),
	};
}

fn union_trait_bound(
	types: &TypeInterner,
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
		let assoc_type_index = incoming.assoc_type_index;
		match existing
			.bindings
			.iter()
			.position(|b| b.assoc_type_index == assoc_type_index)
		{
			None => existing.bindings.push(incoming),
			Some(index) => {
				let merged = &mut existing.bindings[index];
				for required in incoming.required_bounds {
					union_trait_bound(
						types,
						&mut merged.required_bounds,
						conflicts,
						required,
						merge_point,
					);
				}
				match incoming.kind {
					ImpliedBindingKind::Conflicting => {
						merged.kind = ImpliedBindingKind::Conflicting;
					}
					ImpliedBindingKind::Bound => {}
					ImpliedBindingKind::Equals(fact) => add_equality_fact(
						types,
						&mut merged.kind,
						fact,
						conflicts,
						merge_point,
					),
					ImpliedBindingKind::Ambiguous(facts) => {
						for fact in facts {
							add_equality_fact(
								types,
								&mut merged.kind,
								fact,
								conflicts,
								merge_point,
							);
						}
					}
				}
			}
		}
	}
}

pub(super) fn report_not_a_trait_bound(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
	kind: DefKind,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitBound.code())
		.with_message(format!(
			"expected trait, found {} `{name_str}`",
			kind.noun()
		))
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

#[cfg(test)]
mod tests {
	use super::*;

	fn fact(index: u32, value: TypeIndex) -> EqualityFact {
		EqualityFact {
			source: BindingRef {
				bound: BoundId::new(0),
				index,
			},
			value,
		}
	}

	fn merge(
		kind: &mut ImpliedBindingKind,
		incoming: EqualityFact,
	) -> Vec<AssocBindingConflict> {
		let types = TypeInterner::new();
		let mut conflicts = Vec::new();
		add_equality_fact(
			&types,
			kind,
			incoming,
			&mut conflicts,
			BoundId::new(0),
		);
		conflicts
	}

	#[test]
	fn bound_plus_fact_becomes_equals() {
		let mut kind = ImpliedBindingKind::Bound;
		let conflicts = merge(&mut kind, fact(0, TypeIndex::U32));
		assert!(conflicts.is_empty());
		assert!(
			matches!(kind, ImpliedBindingKind::Equals(f) if f.value == TypeIndex::U32)
		);
	}

	#[test]
	fn equals_plus_same_value_is_a_no_op() {
		let mut kind = ImpliedBindingKind::Equals(fact(0, TypeIndex::U32));
		let conflicts = merge(&mut kind, fact(1, TypeIndex::U32));
		assert!(conflicts.is_empty());
		assert!(
			matches!(kind, ImpliedBindingKind::Equals(f) if f.source.index == 0)
		);
	}

	#[test]
	fn equals_plus_distinct_concrete_value_conflicts() {
		let mut kind = ImpliedBindingKind::Equals(fact(0, TypeIndex::U32));
		let conflicts = merge(&mut kind, fact(1, TypeIndex::U64));
		assert_eq!(conflicts.len(), 1);
		assert!(matches!(kind, ImpliedBindingKind::Conflicting));
	}

	#[test]
	fn equals_plus_symbolic_value_becomes_ambiguous() {
		let mut kind = ImpliedBindingKind::Equals(fact(0, TypeIndex::U32));
		let conflicts = merge(&mut kind, fact(1, TypeIndex::INFER));
		assert!(conflicts.is_empty());
		assert!(
			matches!(kind, ImpliedBindingKind::Ambiguous(ref f) if f.len() == 2)
		);
	}

	/// The bug this module's `add_equality_fact` fixes: a concrete conflict
	/// used to be missed once a symbolic fact had already forced the
	/// binding into `Ambiguous`, because that merge case only deduped by
	/// value instead of also checking `known_distinct`.
	#[test]
	fn ambiguous_plus_distinct_concrete_value_still_conflicts() {
		let mut kind = ImpliedBindingKind::Ambiguous(vec![
			fact(0, TypeIndex::U32),
			fact(1, TypeIndex::INFER),
		]);
		let conflicts = merge(&mut kind, fact(2, TypeIndex::U64));
		assert_eq!(conflicts.len(), 1);
		assert!(matches!(kind, ImpliedBindingKind::Conflicting));
	}

	#[test]
	fn conflicting_absorbs_further_facts() {
		let mut kind = ImpliedBindingKind::Conflicting;
		let conflicts = merge(&mut kind, fact(0, TypeIndex::U32));
		assert!(conflicts.is_empty());
		assert!(matches!(kind, ImpliedBindingKind::Conflicting));
	}
}
