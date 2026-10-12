//! Work owned by a declaration while its signature is being constructed.
//! Requirements refer to their eventual bound table, so provisional tables
//! cannot lose inherited requirements that have not been published yet.

use super::assumptions::AssumptionContext;
use super::defs::{AssocTypeIdx, IntrinsicDefs, TraitIdx};
use super::types::{
	Type, TypeEnvIdx, TypeEnvOwner, TypeFolder, TypeIndex, TypeInterner,
};
use crate::ast::Spanned;
use crate::diagnostics::SourceSpan;

#[derive(Clone, Copy)]
pub(super) enum BoundRequirements {
	Parameter { env: TypeEnvIdx, index: usize },
	AssociatedType(AssocTypeIdx),
}

#[derive(Clone, Copy)]
pub(super) enum Obligation {
	CheckBounds {
		context: AssumptionContext,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	},
	CheckTraitMembership {
		context: AssumptionContext,
		subject: TypeIndex,
		required: TraitIdx,
		reference: SourceSpan,
	},
	Normalize {
		context: AssumptionContext,
		subject: TypeIndex,
		reference: SourceSpan,
	},
}

impl Obligation {
	pub(super) fn context(self) -> AssumptionContext {
		match self {
			Self::CheckBounds { context, .. }
			| Self::CheckTraitMembership { context, .. }
			| Self::Normalize { context, .. } => context,
		}
	}
}

/// One-based indices keep an empty chain in the same four-byte slot.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct ObligationIdx(std::num::NonZeroU32);

struct ObligationNode {
	next: Option<ObligationIdx>,
	obligation: Option<Obligation>,
}

/// All deferred work shares the type context's lifetime and one allocation buffer.
/// Links preserve declaration ownership across reentrant, interleaved queries.
#[derive(Default)]
pub(super) struct ObligationArena {
	nodes: Vec<ObligationNode>,
}

impl ObligationArena {
	#[cfg(test)]
	pub(super) fn is_empty(&self) -> bool {
		self.nodes.is_empty()
	}

	/// Completed payloads are dropped by the time a sweep finishes.
	/// This audit traverses deferred slots only, with no release-build cost.
	pub(super) fn assert_drained(&self) {
		debug_assert!(
			self.nodes.iter().all(|node| node.obligation.is_none()),
			"completed signatures cannot leave orphaned obligations"
		);
	}

	#[cfg(test)]
	pub(super) fn len(&self) -> usize {
		self.nodes.len()
	}

	pub(super) fn push(
		&mut self,
		head: &mut Option<ObligationIdx>,
		obligation: Obligation,
	) {
		let index = u32::try_from(self.nodes.len())
			.expect("too many signature obligations");
		let id = ObligationIdx(
			std::num::NonZeroU32::new(
				index
					.checked_add(1)
					.expect("too many signature obligations"),
			)
			.unwrap(),
		);
		self.nodes.push(ObligationNode {
			next: *head,
			obligation: Some(obligation),
		});
		*head = Some(id);
	}

	/// Detach a payload before executing it: execution may grow this arena.
	pub(super) fn take(
		&mut self,
		id: ObligationIdx,
	) -> (Option<ObligationIdx>, Obligation) {
		let node = &mut self.nodes[(id.0.get() - 1) as usize];
		(
			node.next,
			node.obligation
				.take()
				.expect("only live obligations are resumed"),
		)
	}

	pub(super) fn retain(
		&mut self,
		id: ObligationIdx,
		head: &mut Option<ObligationIdx>,
		obligation: Obligation,
	) {
		let node = &mut self.nodes[(id.0.get() - 1) as usize];
		assert!(node.obligation.is_none());
		node.next = *head;
		node.obligation = Some(obligation);
		*head = Some(id);
	}

	/// Restore source insertion order without allocating a second list.
	pub(super) fn reverse(
		&mut self,
		mut head: Option<ObligationIdx>,
	) -> Option<ObligationIdx> {
		let mut reversed = None;
		while let Some(id) = head {
			let node = &mut self.nodes[(id.0.get() - 1) as usize];
			head = node.next;
			node.next = reversed;
			reversed = Some(id);
		}
		reversed
	}
}

/// A completed retry changes only types within its owning declaration.
/// It is applied transiently, not retained as another result table.
/// Examples below use `<error>` to denote `TypeIndex::ERROR`.
pub(super) enum TypeRepair {
	/// Replace a stored type after deferred normalization completes, or after
	/// normalization or an associated-type value's bound check fails.
	///
	/// For example, once `T::Item` normalizes to `i32`, `(T::Item, bool)`
	/// becomes `(i32, bool)`. A failed check replaces the affected type with
	/// `<error>` instead. Replacement contents are inserted without folding
	/// them again.
	ReplaceType(ReplaceType),
	/// Reject a specific generic argument after its deferred bound check fails.
	///
	/// For example, given `Need<X: Marker>`, a failed `U: Marker` check turns
	/// `(Need<U>, U)` into `(Need<error>, U)`. Only the matching argument slot
	/// in `Need` is rejected; ordinary uses of `U` remain valid.
	RejectArgument(RejectArgument),
	/// Invalidate structural dependencies after deferred trait membership fails.
	///
	/// A failed `T: Project` check replaces `<T as Project>::Output` with
	/// `<error>`, while an ordinary `T` remains valid. A failed `T: Memory`
	/// check turns `T::*u8` into `<error>::*u8`: the pointer and its pointee
	/// remain intact, and only its memory field becomes error. Slices and
	/// arrays recover the same way.
	InvalidateTraitDependents(InvalidateTraitDependents),
}

impl TypeRepair {
	pub(super) fn apply(
		&self,
		types: &mut TypeInterner,
		intrinsics: &IntrinsicDefs,
		ty: TypeIndex,
	) -> TypeIndex {
		match *self {
			Self::ReplaceType(mut folder) => folder.fold_type(types, ty),
			Self::RejectArgument(mut folder) => folder.fold_type(types, ty),
			Self::InvalidateTraitDependents(operation) => {
				TraitDependentsFolder {
					operation,
					intrinsics,
				}
				.fold_type(types, ty)
			}
		}
	}
}

#[derive(Clone, Copy)]
pub(super) struct ReplaceType {
	pub(super) from: TypeIndex,
	pub(super) to: TypeIndex,
}

impl TypeFolder for ReplaceType {
	fn fold_type(
		&mut self,
		types: &mut TypeInterner,
		ty: TypeIndex,
	) -> TypeIndex {
		if ty == self.from {
			self.to
		} else {
			fold_recovering_children(types, ty, self)
		}
	}
}

#[derive(Clone, Copy)]
pub(super) struct RejectArgument {
	pub(super) owner: TypeEnvOwner,
	pub(super) index: usize,
	pub(super) argument: TypeIndex,
	pub(super) normalized: TypeIndex,
}

impl TypeFolder for RejectArgument {
	fn fold_type(
		&mut self,
		types: &mut TypeInterner,
		ty: TypeIndex,
	) -> TypeIndex {
		if let Type::Struct { struct_index, .. } = types.resolve(ty) {
			let struct_index = *struct_index;
			if self.owner == TypeEnvOwner::Struct(struct_index) {
				let type_args = types.map_type_list(
					ty,
					|ty| {
						let Type::Struct { type_args, .. } = ty else {
							unreachable!()
						};
						type_args
					},
					|types, index, child| {
						if index == self.index
							&& (child == self.argument
								|| child == self.normalized)
						{
							TypeIndex::ERROR
						} else {
							self.fold_type(types, child)
						}
					},
				);
				return match type_args {
					Some(type_args) => types.intern(Type::Struct {
						struct_index,
						type_args,
					}),
					None => ty,
				};
			}
		}
		fold_recovering_children(types, ty, self)
	}
}

#[derive(Clone, Copy)]
pub(super) struct InvalidateTraitDependents {
	pub(super) subject: TypeIndex,
	pub(super) normalized: TypeIndex,
	pub(super) required: TraitIdx,
}

impl InvalidateTraitDependents {
	fn matches_subject(&self, ty: TypeIndex) -> bool {
		ty == self.subject || ty == self.normalized
	}
}

/// Borrow traversal context without storing it in the repair operation.
struct TraitDependentsFolder<'a> {
	operation: InvalidateTraitDependents,
	intrinsics: &'a IntrinsicDefs,
}

impl TraitDependentsFolder<'_> {
	/// A memory field structurally requires Memory; ordinary occurrences
	/// of the same subject remain valid when only that proof fails.
	fn rejects_memory(&self, memory: TypeIndex) -> bool {
		memory != TypeIndex::ERROR
			&& self.operation.required
				== self
					.intrinsics
					.memory
					.expect("memory fields require the intrinsic Memory trait")
			&& self.operation.matches_subject(memory)
	}
}

impl TypeFolder for TraitDependentsFolder<'_> {
	fn fold_type(
		&mut self,
		types: &mut TypeInterner,
		ty: TypeIndex,
	) -> TypeIndex {
		match *types.resolve(ty) {
			Type::AssocTypeProjection {
				base, trait_index, ..
			} if trait_index == self.operation.required
				&& self.operation.matches_subject(base) =>
			{
				TypeIndex::ERROR
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} if self.rejects_memory(memory) => {
				let to = self.fold_type(types, to);
				types.intern(Type::Pointer {
					to,
					memory: TypeIndex::ERROR,
					ownership,
				})
			}
			Type::Slice {
				of,
				memory,
				ownership,
			} if self.rejects_memory(memory) => {
				let of = self.fold_type(types, of);
				types.intern(Type::Slice {
					of,
					memory: TypeIndex::ERROR,
					ownership,
				})
			}
			Type::Array {
				of,
				size,
				memory,
				ownership,
			} if self.rejects_memory(memory) => {
				let of = self.fold_type(types, of);
				types.intern(Type::Array {
					of,
					size,
					memory: TypeIndex::ERROR,
					ownership,
				})
			}
			_ => fold_recovering_children(types, ty, self),
		}
	}
}

/// Recovery invalidates a projection when its receiver becomes error.
/// Structural folding and substitution preserve projections as written.
fn fold_recovering_children<F: TypeFolder>(
	types: &mut TypeInterner,
	ty: TypeIndex,
	folder: &mut F,
) -> TypeIndex {
	let Type::AssocTypeProjection {
		base,
		trait_index,
		assoc_type_index,
	} = *types.resolve(ty)
	else {
		return types.fold_children(ty, folder);
	};
	let next_base = folder.fold_type(types, base);
	if next_base == TypeIndex::ERROR {
		TypeIndex::ERROR
	} else if next_base == base {
		ty
	} else {
		types.intern(Type::AssocTypeProjection {
			base: next_base,
			trait_index,
			assoc_type_index,
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn replacement_inserts_the_result_without_folding_it_again() {
		let mut types = TypeInterner::new();
		let subject = types.intern(Type::TypeParam {
			env: TypeEnvIdx::new(1),
			param_index: 0,
		});
		let replacement = types.intern(Type::Tuple {
			elements: Box::new([subject]),
		});
		let original = types.intern(Type::Tuple {
			elements: Box::new([subject, TypeIndex::BOOL]),
		});
		let result = TypeRepair::ReplaceType(ReplaceType {
			from: subject,
			to: replacement,
		})
		.apply(&mut types, &IntrinsicDefs::default(), original);
		assert_eq!(
			types.resolve(result),
			&Type::Tuple {
				elements: Box::new([replacement, TypeIndex::BOOL])
			}
		);
		assert_eq!(
			types.resolve(original),
			&Type::Tuple {
				elements: Box::new([subject, TypeIndex::BOOL])
			}
		);
	}

	#[test]
	fn replacement_recovers_a_projection_with_an_invalid_receiver() {
		let mut types = TypeInterner::new();
		let subject = types.intern(Type::TypeParam {
			env: TypeEnvIdx::new(1),
			param_index: 0,
		});
		let projection = types.intern(Type::AssocTypeProjection {
			base: subject,
			trait_index: TraitIdx::new(0),
			assoc_type_index: AssocTypeIdx::new(0),
		});
		let result = TypeRepair::ReplaceType(ReplaceType {
			from: subject,
			to: TypeIndex::ERROR,
		})
		.apply(&mut types, &IntrinsicDefs::default(), projection);
		assert_eq!(result, TypeIndex::ERROR);
	}
}
