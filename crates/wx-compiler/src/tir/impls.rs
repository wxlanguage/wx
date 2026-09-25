//! Dispatch candidates collected from declaration identities before any
//! signature is resolved. This deliberately does not inspect type parameter
//! bounds or expand user-written type aliases.

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{self, DefId, Spanned, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	tir::defs::DefKey,
	vfs::{FileId, PackageId},
};

use super::{
	bounds::report_expected_trait_bound,
	defs::{
		AstEntry, AstNodeRef, BindingKey, BindingNamespace, DefKind,
		DefinitionRegistry, DuplicateDefinitionDiagnostic, InherentImplIndex,
		NamespaceIndex, NamespaceKind, TraitImplIndex, TraitIndex,
	},
	paths::PathResolver,
	signatures::{SignatureBuilder, SignatureRegistry},
	types::{Type, TypeIndex},
};

/// The outer, injective part of a resolved type. Type arguments and array
/// elements are intentionally absent: a bucket identifies candidates, not
/// whether a candidate's complete target matches.
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
	Struct(DefId),
	Enum(DefId),
}

impl ImplTarget {
	pub(super) fn from_type(
		ty: &Type,
		defs: &DefinitionRegistry,
	) -> Option<Self> {
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
			Type::Struct { struct_index, .. } => {
				Self::Struct(defs.structs[usize::from(*struct_index)].def_id)
			}
			Type::Enum { enum_index } => {
				Self::Enum(defs.enums[usize::from(*enum_index)].def_id)
			}
			Type::Error
			| Type::Infer
			| Type::Unit
			| Type::Never
			| Type::Integer
			| Type::Float
			| Type::Tuple { .. }
			| Type::Memory { .. }
			| Type::Function { .. }
			| Type::FunctionItem { .. }
			| Type::Pointer { .. }
			| Type::TypeParam { .. }
			| Type::AssociatedType { .. }
			| Type::AssocTypeProjection { .. } => return None,
		})
	}
}

#[derive(Clone, Copy)]
pub(super) struct TraitImplHead {
	pub(super) trait_def: Option<Spanned<DefId>>,
	pub(super) target: Option<Spanned<ImplTarget>>,
}

pub(super) struct ImplDispatch {
	inherent: HashMap<ImplTarget, Vec<InherentImplIndex>>,
	traits: HashMap<ImplTarget, Vec<(DefId, TraitImplIndex)>>,
	inherent_targets: Vec<Option<Spanned<ImplTarget>>>,
	trait_headers: Vec<TraitImplHead>,
}

struct ImplDispatchBuilder<'a, 'ast> {
	diagnostics: &'a mut Vec<Diagnostic<FileId>>,
	strings: &'a StringInterner,
	defs: &'a DefinitionRegistry,
	ast_nodes: &'a [AstEntry<'ast>],
	stdlib_package: PackageId,
	inherent: HashMap<ImplTarget, Vec<InherentImplIndex>>,
	traits: HashMap<ImplTarget, Vec<(DefId, TraitImplIndex)>>,
	inherent_targets: Vec<Option<Spanned<ImplTarget>>>,
	trait_headers: Vec<TraitImplHead>,
}

impl ImplDispatch {
	pub(super) fn build(
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		defs: &DefinitionRegistry,
		ast_nodes: &[AstEntry<'_>],
		stdlib_package: PackageId,
	) -> Self {
		ImplDispatchBuilder::new(
			diagnostics,
			strings,
			defs,
			ast_nodes,
			stdlib_package,
		)
		.build()
	}

	pub(super) fn inherent_target(
		&self,
		index: InherentImplIndex,
	) -> Option<Spanned<ImplTarget>> {
		self.inherent_targets[usize::from(index)]
	}

	pub(super) fn trait_header(&self, index: TraitImplIndex) -> TraitImplHead {
		self.trait_headers[usize::from(index)]
	}

	pub(super) fn inherent_candidates(
		&self,
		target: ImplTarget,
	) -> &[InherentImplIndex] {
		self.inherent.get(&target).map(Vec::as_slice).unwrap_or(&[])
	}

	pub(super) fn trait_candidates(
		&self,
		target: ImplTarget,
	) -> &[(DefId, TraitImplIndex)] {
		self.traits.get(&target).map(Vec::as_slice).unwrap_or(&[])
	}

	#[cfg(test)]
	pub(super) fn is_empty(&self) -> bool {
		self.inherent.is_empty() && self.traits.is_empty()
	}
}

impl<'a, 'ast> ImplDispatchBuilder<'a, 'ast> {
	fn new(
		diagnostics: &'a mut Vec<Diagnostic<FileId>>,
		strings: &'a StringInterner,
		defs: &'a DefinitionRegistry,
		ast_nodes: &'a [AstEntry<'ast>],
		stdlib_package: PackageId,
	) -> Self {
		Self {
			diagnostics,
			strings,
			defs,
			ast_nodes,
			stdlib_package,
			inherent: HashMap::new(),
			traits: HashMap::new(),
			inherent_targets: vec![None; defs.inherent_impls.len()],
			trait_headers: vec![
				TraitImplHead {
					trait_def: None,
					target: None,
				};
				defs.trait_impls.len()
			],
		}
	}

	fn build(mut self) -> ImplDispatch {
		let ast_nodes = self.ast_nodes;
		let defs = self.defs;
		for entry in ast_nodes {
			match &entry.node {
				AstNodeRef::InherentImplBlock { item, block_index } => {
					let ast::Item::InherentImpl {
						type_params,
						target,
						..
					} = item
					else {
						unreachable!()
					};
					let target = self.resolve_target(
						entry.file_id,
						entry.namespace,
						target,
						type_params,
					);
					self.inherent_targets[usize::from(*block_index)] = target;
					if let Some(target) = target {
						self.register_inherent(
							target,
							*block_index,
							entry.file_id,
						);
					}
				}
				AstNodeRef::TraitImplBlock { item, block_index } => {
					let ast::Item::TraitImpl {
						type_params,
						trait_name,
						target,
						..
					} = item
					else {
						unreachable!()
					};
					let target = self.resolve_target(
						entry.file_id,
						entry.namespace,
						target,
						type_params,
					);
					let trait_def = self.resolve_trait(
						entry.file_id,
						entry.namespace,
						trait_name,
					);
					self.trait_headers[usize::from(*block_index)] =
						TraitImplHead { trait_def, target };
					if let (Some(trait_def), Some(target)) = (trait_def, target)
					{
						self.register_trait(
							target,
							trait_def.inner,
							trait_name.segments.last().unwrap().ident.inner,
							*block_index,
							entry.file_id,
						);
					}
				}
				AstNodeRef::TypeSet {
					typeset_index,
					item,
				} => {
					let ast::Item::TypeSet { name, members, .. } = item else {
						unreachable!()
					};
					let def = &defs.typesets[usize::from(*typeset_index)];
					for (member, &impl_index) in
						members.iter().zip(def.member_impls.iter())
					{
						let target = self.resolve_target(
							entry.file_id,
							entry.namespace,
							&member.inner.inner,
							&[],
						);
						let trait_def = Spanned {
							inner: defs.traits[usize::from(def.trait_index)]
								.def_id,
							span: member.inner.span,
						};
						self.trait_headers[usize::from(impl_index)] =
							TraitImplHead {
								trait_def: Some(trait_def),
								target,
							};
						if let Some(target) = target {
							self.register_trait(
								target,
								trait_def.inner,
								name.inner,
								impl_index,
								entry.file_id,
							);
						}
					}
				}
				_ => {}
			}
		}
		ImplDispatch {
			inherent: self.inherent,
			traits: self.traits,
			inherent_targets: self.inherent_targets,
			trait_headers: self.trait_headers,
		}
	}

	fn register_trait(
		&mut self,
		target: Spanned<ImplTarget>,
		trait_def: DefId,
		trait_name: SymbolU32,
		index: TraitImplIndex,
		file_id: FileId,
	) {
		let bucket = self.traits.entry(target.inner).or_default();
		if let Some(&(_, earlier)) =
			bucket.iter().find(|(item, _)| *item == trait_def)
		{
			let name = self.strings.resolve(trait_name).unwrap();
			let earlier_target =
				self.trait_headers[usize::from(earlier)].target.unwrap();
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
							self.defs.trait_impls[usize::from(earlier)].file_id,
							earlier_target.span,
						)
						.secondary_label()
						.with_message("first implementation here"),
					),
			);
			return;
		}
		bucket.push((trait_def, index));
	}

	/// Buckets one inherent impl under `target`, reporting
	/// `DuplicateDefinition` for any member name it shares with an impl
	/// already in the same bucket — the inherent-impl twin of
	/// `register_trait`'s "one trait impl per bucket" rule, except here
	/// it's per member name rather than per whole impl, since ordinary
	/// `impl Foo { }` blocks are just separate sources of members for one
	/// bucket, not competing candidates. Reuses each impl's own
	/// `bindings`/`members` (already built by `defs.rs`) rather than
	/// keeping a second copy of this data just for the check.
	fn register_inherent(
		&mut self,
		target: Spanned<ImplTarget>,
		index: InherentImplIndex,
		file_id: FileId,
	) {
		let defs = self.defs;
		let new_impl = &defs.inherent_impls[usize::from(index)];
		let earlier_in_bucket = self
			.inherent
			.get(&target.inner)
			.map(Vec::as_slice)
			.unwrap_or(&[]);

		// Sorted by source position so a diagnostic here can't depend on
		// `HashMap` iteration order.
		let mut new_members: Vec<(BindingKey, TextSpan)> = new_impl
			.bindings
			.iter()
			.map(|(&key, &member)| {
				(key, new_impl.members[usize::from(member)].span)
			})
			.collect();
		new_members.sort_by_key(|&(_, span)| span.start);

		for (key, span) in new_members {
			let collision = earlier_in_bucket.iter().find_map(|&earlier| {
				let earlier_impl = &defs.inherent_impls[usize::from(earlier)];
				earlier_impl.bindings.get(&key).map(|&member| {
					(
						earlier_impl.file_id,
						earlier_impl.members[usize::from(member)].span,
					)
				})
			});
			if let Some((earlier_file, earlier_span)) = collision {
				self.diagnostics.push(
					DuplicateDefinitionDiagnostic {
						strings: self.strings,
						key,
						definitions: (
							SourceSpan::new(earlier_file, earlier_span),
							SourceSpan::new(file_id, span),
						),
					}
					.report(),
				);
			}
		}
		self.inherent.entry(target.inner).or_default().push(index);
	}

	fn resolve_target(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		path: &ast::Path,
		params: &[ast::TypeParam],
	) -> Option<Spanned<ImplTarget>> {
		let defs = self.defs;
		let stdlib_root =
			defs.package_namespaces[self.stdlib_package.as_usize()];
		let segments = &path.segments;
		let span = path.span();
		let invalid = |message: String| {
			Diagnostic::error()
				.with_code(DiagnosticCode::InvalidImplTarget.code())
				.with_message(message)
				.with_label(SourceSpan::new(file_id, span).primary_label())
		};
		// Normal type resolution checks local type parameters before namespace
		// bindings. The dispatch-only path walk must make the same distinction.
		if params
			.iter()
			.any(|param| param.name.inner == segments[0].ident.inner)
		{
			self.diagnostics.push(invalid(
				"cannot use a type parameter as an impl target".into(),
			));
			return None;
		}
		let binding =
			PathResolver::new(&defs.namespaces, &defs.use_items, stdlib_root)
				.resolve_path(
					self.diagnostics,
					self.strings,
					file_id,
					namespace,
					segments,
					BindingNamespace::Type,
				);
		let Some(key) = binding.def_key() else {
			return None;
		};
		let kind = key.symbol_kind(defs);
		let head = match kind {
			DefKind::Struct(id) => Some(ImplTarget::Struct(id)),
			DefKind::Enum(namespace) => {
				match defs.namespaces[usize::from(namespace)].kind {
					NamespaceKind::Enum(index) => Some(ImplTarget::Enum(
						defs.enums[usize::from(index)].def_id,
					)),
					_ => unreachable!(),
				}
			}
			_ => self.intrinsic_target(key),
		};
		if head.is_none() {
			self.diagnostics.push(invalid(format!(
				"cannot use this {} as an impl target",
				kind.noun(),
			)));
		}
		head.map(|inner| Spanned { inner, span })
	}

	fn resolve_trait(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIndex,
		path: &ast::Path,
	) -> Option<Spanned<DefId>> {
		let defs = self.defs;
		let stdlib_root =
			defs.package_namespaces[self.stdlib_package.as_usize()];
		let binding =
			PathResolver::new(&defs.namespaces, &defs.use_items, stdlib_root)
				.resolve_path(
					self.diagnostics,
					self.strings,
					file_id,
					namespace,
					&path.segments,
					BindingNamespace::Type,
				);
		let key = binding.def_key()?;
		let id = match key.symbol_kind(defs) {
			DefKind::Trait(id) => id,
			other => {
				self.diagnostics.push(report_expected_trait_bound(
					file_id,
					self.strings,
					path.segments.last().unwrap().ident,
					other.noun(),
				));
				return None;
			}
		};
		Some(Spanned {
			inner: id,
			span: path.span(),
		})
	}

	fn intrinsic_target(&self, key: DefKey) -> Option<ImplTarget> {
		let intrinsic = &self.defs.intrinsics;
		for (candidate, target) in [
			(intrinsic.u8, ImplTarget::U8),
			(intrinsic.i8, ImplTarget::I8),
			(intrinsic.u16, ImplTarget::U16),
			(intrinsic.i16, ImplTarget::I16),
			(intrinsic.u32, ImplTarget::U32),
			(intrinsic.i32, ImplTarget::I32),
			(intrinsic.u64, ImplTarget::U64),
			(intrinsic.i64, ImplTarget::I64),
			(intrinsic.f32, ImplTarget::F32),
			(intrinsic.f64, ImplTarget::F64),
			(intrinsic.bool, ImplTarget::Bool),
			(intrinsic.char, ImplTarget::Char),
		] {
			if candidate == Some(key) {
				return Some(target);
			}
		}
		None
	}
}

impl SignatureBuilder<'_, '_> {
	/// Resolves a target's type to intern as `Self`. Dispatch (`impls.rs`'s
	/// own build pass) only ever buckets by outer constructor identity —
	/// two `impl Foo { }` blocks are just two sources of members for the
	/// same bucket, checked against each other only for duplicate member
	/// names (`ImplDispatchBuilder::register_inherent`), the same way
	/// `register_trait` allows only one trait impl per bucket. A target's
	/// own generic arguments (`impl<Mem, T> RawPtr<Mem, T> { }`) still need
	/// real resolution against the struct/enum's own declared parameters —
	/// not implemented yet, so a written argument is a `todo!()` here
	/// rather than silently dropped.
	pub(super) fn resolve_impl_target(
		&mut self,
		path: &ast::Path,
		head: Option<Spanned<ImplTarget>>,
	) -> TypeIndex {
		let Some(head) = head else {
			return TypeIndex::ERROR;
		};
		if !path.segments.last().unwrap().type_args.is_empty() {
			todo!("generic impl target arguments aren't resolved yet")
		}
		self.impl_target_type(head.inner)
	}

	pub(super) fn impl_target_type(&mut self, target: ImplTarget) -> TypeIndex {
		match target {
			ImplTarget::U8 => TypeIndex::U8,
			ImplTarget::I8 => TypeIndex::I8,
			ImplTarget::U16 => TypeIndex::U16,
			ImplTarget::I16 => TypeIndex::I16,
			ImplTarget::U32 => TypeIndex::U32,
			ImplTarget::I32 => TypeIndex::I32,
			ImplTarget::U64 => TypeIndex::U64,
			ImplTarget::I64 => TypeIndex::I64,
			ImplTarget::F32 => TypeIndex::F32,
			ImplTarget::F64 => TypeIndex::F64,
			ImplTarget::Bool => TypeIndex::BOOL,
			ImplTarget::Char => TypeIndex::CHAR,
			ImplTarget::Struct(def_id) => {
				let struct_index = match self.ast_node(def_id) {
					AstNodeRef::RecordStruct { struct_index, .. }
					| AstNodeRef::TupleStruct { struct_index, .. } => *struct_index,
					_ => unreachable!(
						"struct target must name a struct definition"
					),
				};
				self.types.intern(Type::Struct {
					struct_index,
					args: Box::new([]),
				})
			}
			ImplTarget::Enum(def_id) => {
				let AstNodeRef::Enum { enum_index, .. } = self.ast_node(def_id)
				else {
					unreachable!("enum target must name an enum definition")
				};
				self.types.intern(Type::Enum {
					enum_index: *enum_index,
				})
			}
			ImplTarget::Array | ImplTarget::Slice => {
				unreachable!(
					"array and slice types cannot be path-only impl targets"
				)
			}
		}
	}

	pub(super) fn impl_trait_index(&self, def_id: DefId) -> TraitIndex {
		match self.ast_node(def_id) {
			AstNodeRef::Trait { trait_index, .. } => *trait_index,
			AstNodeRef::TypeSet { typeset_index, .. } => {
				self.defs.typesets[usize::from(*typeset_index)].trait_index
			}
			_ => unreachable!("dispatch trait must name a trait or typeset"),
		}
	}
}

impl SignatureRegistry {
	#[cfg(test)]
	pub(super) fn impl_dispatch_is_empty(&self) -> bool {
		self.impl_dispatch.is_empty()
	}

	pub(super) fn inherent_candidates(
		&self,
		target: ImplTarget,
	) -> &[InherentImplIndex] {
		self.impl_dispatch.inherent_candidates(target)
	}

	pub(super) fn trait_candidates(
		&self,
		target: ImplTarget,
	) -> &[(DefId, TraitImplIndex)] {
		self.impl_dispatch.trait_candidates(target)
	}
}
