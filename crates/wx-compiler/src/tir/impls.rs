//! Coarse impl dispatch. Headers are resolved by `signatures.rs`; this module
//! indexes their outer target type so later lookups can inspect candidates
//! without depending on declaration order. A bucket is not a match: generic
//! arguments and bounds must still be checked against the full receiver.

use codespan_reporting::diagnostic::Diagnostic;

use crate::{
	ast::{DefId, Spanned},
	diagnostics::{DiagnosticCode, SourceSpan},
	vfs::FileId,
};

use super::{
	defs::{
		EnumIndex, InherentImplIndex, StructIndex, TraitImplIndex, TraitIndex,
	},
	signatures::{SignatureBuilder, SignatureRegistry},
	types::{Type, TypeIndex},
};

/// The outer, injective part of a resolved type. Type arguments and array
/// elements are intentionally absent: every possible impl for a receiver
/// must land in the same bucket as that receiver.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum ImplTarget {
	U8,
	I8,
	U16,
	I16,
	U32,
	I32,
	U64,
	I64,
	F32,
	F64,
	Bool,
	Char,
	Array,
	Slice,
	Struct(StructIndex),
	Enum(EnumIndex),
	Memory(DefId),
}

impl ImplTarget {
	pub(super) fn from_type(ty: &Type) -> Option<Self> {
		Some(match ty {
			Type::U8 => Self::U8,
			Type::I8 => Self::I8,
			Type::U16 => Self::U16,
			Type::I16 => Self::I16,
			Type::U32 => Self::U32,
			Type::I32 => Self::I32,
			Type::U64 => Self::U64,
			Type::I64 => Self::I64,
			Type::F32 => Self::F32,
			Type::F64 => Self::F64,
			Type::Bool => Self::Bool,
			Type::Char => Self::Char,
			Type::Array { .. } => Self::Array,
			Type::Slice { .. } => Self::Slice,
			Type::Struct { struct_index, .. } => Self::Struct(*struct_index),
			Type::Enum { enum_index } => Self::Enum(*enum_index),
			Type::Memory { id, .. } => Self::Memory(*id),
			Type::Error
			| Type::Infer
			| Type::Unit
			| Type::Never
			| Type::Integer
			| Type::Float
			| Type::Tuple { .. }
			| Type::Function { .. }
			| Type::FunctionItem { .. }
			| Type::Pointer { .. }
			| Type::TypeParam { .. }
			| Type::AssociatedType { .. }
			| Type::AssocTypeProjection { .. } => return None,
		})
	}
}

impl SignatureBuilder<'_, '_> {
	/// Buckets one resolved inherent impl into dispatch, reporting
	/// `InvalidImplTarget` if its target isn't a legal impl target. Called
	/// the moment an impl header finishes resolving — right where its
	/// `InherentImplSignature` slot is written — so dispatch is complete by
	/// construction the moment every item has resolved, with no separate
	/// "resolve everything, then build dispatch" pass needed (and nothing
	/// to keep in sync when a *new* kind of impl-producing item shows up —
	/// see `register_trait_impl`'s doc comment).
	pub(super) fn register_inherent_impl(
		&mut self,
		index: InherentImplIndex,
		file_id: FileId,
		target: Spanned<TypeIndex>,
	) {
		let ty = self.types.resolve(target.inner);
		if let Some(impl_target) = ImplTarget::from_type(ty) {
			self.inherent_impl_dispatch
				.entry(impl_target)
				.or_default()
				.push(index);
		} else if !matches!(ty, Type::Error) {
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::InvalidImplTarget.code())
					.with_message("cannot define an `impl` block for this type")
					.with_label(
						SourceSpan::new(file_id, target.span).primary_label(),
					),
			);
		}
	}

	/// Buckets one resolved trait impl into dispatch, reporting
	/// `InvalidImplTarget`/`DuplicateTraitImpl` as needed. Called the
	/// moment a trait impl's header finishes resolving — both a
	/// hand-written `impl Trait for Type {}` (from its own
	/// `TraitImplBlock` arm) and a typeset's synthetic per-member impl
	/// (from the owning typeset's own arm, once per member) go through
	/// this same call, so a typeset needs no special-casing here at all:
	/// whichever caller resolves a target type against a `TraitIndex`
	/// registers it, and dispatch never has an "is everything resolved
	/// yet" question to answer.
	pub(super) fn register_trait_impl(
		&mut self,
		index: TraitImplIndex,
		trait_index: TraitIndex,
		file_id: FileId,
		target: Spanned<TypeIndex>,
	) {
		let ty = self.types.resolve(target.inner);
		let Some(impl_target) = ImplTarget::from_type(ty) else {
			if !matches!(ty, Type::Error) {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::InvalidImplTarget.code())
						.with_message("cannot implement a trait for this type")
						.with_label(
							SourceSpan::new(file_id, target.span)
								.primary_label(),
						),
				);
			}
			return;
		};
		let bucket = self.trait_impl_dispatch.entry(impl_target).or_default();
		if let Some(&(_, earlier)) =
			bucket.iter().find(|(t, _)| *t == trait_index)
		{
			let name = self
				.strings
				.resolve(self.defs.traits[usize::from(trait_index)].name.inner)
				.unwrap();
			let earlier_def = &self.defs.trait_impls[usize::from(earlier)];
			let earlier_header =
				self.trait_impls[usize::from(earlier)].as_ref().unwrap();
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::DuplicateTraitImpl.code())
					.with_message(format!(
						"`{name}` is already implemented for this type constructor"
					))
					.with_label(
						SourceSpan::new(file_id, target.span).primary_label(),
					)
					.with_label(
						SourceSpan::new(
							earlier_def.file_id,
							earlier_header.target.span,
						)
						.secondary_label()
						.with_message("first implementation here"),
					),
			);
			return;
		}
		bucket.push((trait_index, index));
	}
}

impl SignatureRegistry {
	#[cfg(test)]
	pub(super) fn impl_dispatch_is_empty(&self) -> bool {
		self.inherent_impl_dispatch.is_empty()
			&& self.trait_impl_dispatch.is_empty()
	}

	pub(super) fn inherent_candidates(
		&self,
		target: ImplTarget,
	) -> &[InherentImplIndex] {
		self.inherent_impl_dispatch
			.get(&target)
			.map(Vec::as_slice)
			.unwrap_or(&[])
	}

	pub(super) fn trait_candidates(
		&self,
		target: ImplTarget,
	) -> &[(TraitIndex, TraitImplIndex)] {
		self.trait_impl_dispatch
			.get(&target)
			.map(Vec::as_slice)
			.unwrap_or(&[])
	}
}
