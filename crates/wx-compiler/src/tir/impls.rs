//! Coarse impl dispatch. Headers are resolved by `signatures.rs`; this module
//! indexes their outer target type so later lookups can inspect candidates
//! without depending on declaration order. A bucket is not a match: generic
//! arguments and bounds must still be checked against the full receiver.

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;

use crate::{
	ast::DefId,
	diagnostics::{DiagnosticCode, SourceSpan},
};

use super::{
	defs::{
		EnumIndex, InherentImplIndex, StructIndex, TraitImplIndex, TraitIndex,
	},
	signatures::{SignatureBuilder, SignatureRegistry},
	types::Type,
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
	/// Called after every impl header query completes. The slices stay
	/// index-aligned with the impl arenas in `defs`; members need not have
	/// signatures yet because their names already live there.
	pub(super) fn build_impl_dispatch(&mut self) {
		assert_eq!(self.inherent_impls.len(), self.defs.inherent_impls.len());
		assert_eq!(self.trait_impls.len(), self.defs.trait_impls.len());
		let mut inherent_dispatch: HashMap<ImplTarget, Vec<InherentImplIndex>> =
			HashMap::new();
		let mut trait_dispatch: HashMap<
			ImplTarget,
			Vec<(TraitIndex, TraitImplIndex)>,
		> = HashMap::new();

		for (i, header) in self.inherent_impls.iter().enumerate() {
			let header = header.as_ref().expect("impl header not resolved");
			let def = &self.defs.inherent_impls[i];
			let ty = self.types.resolve(header.target.inner);
			if let Some(target) = ImplTarget::from_type(ty) {
				inherent_dispatch
					.entry(target)
					.or_default()
					.push(InherentImplIndex::new(u32::try_from(i).unwrap()));
			} else if !matches!(ty, Type::Error) {
				self.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::InvalidImplTarget.code())
						.with_message(
							"cannot define an `impl` block for this type",
						)
						.with_label(
							SourceSpan::new(def.file_id, header.target.span)
								.primary_label(),
						),
				);
			}
		}

		for (i, header) in self.trait_impls.iter().enumerate() {
			let header = header.as_ref().expect("impl header not resolved");
			let def = &self.defs.trait_impls[i];
			let ty = self.types.resolve(header.target.inner);
			let Some(target) = ImplTarget::from_type(ty) else {
				if !matches!(ty, Type::Error) {
					self.diagnostics.push(
						Diagnostic::error()
							.with_code(DiagnosticCode::InvalidImplTarget.code())
							.with_message(
								"cannot implement a trait for this type",
							)
							.with_label(
								SourceSpan::new(
									def.file_id,
									header.target.span,
								)
								.primary_label(),
							),
					);
				}
				continue;
			};
			let Some(trait_ref) = header.trait_ref else {
				continue; // The path error was reported by the header query.
			};
			let bucket = trait_dispatch.entry(target).or_default();
			if let Some(&(_, earlier)) =
				bucket.iter().find(|(t, _)| *t == trait_ref.inner)
			{
				let name = self
					.strings
					.resolve(
						self.defs.traits[usize::from(trait_ref.inner)]
							.name
							.inner,
					)
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
							SourceSpan::new(def.file_id, header.target.span)
								.primary_label(),
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
				continue;
			}
			bucket.push((
				trait_ref.inner,
				TraitImplIndex::new(u32::try_from(i).unwrap()),
			));
		}
		self.inherent_impl_dispatch = inherent_dispatch;
		self.trait_impl_dispatch = trait_dispatch;
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
