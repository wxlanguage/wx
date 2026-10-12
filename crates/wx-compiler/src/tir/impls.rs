//! Dispatch candidates collected from declaration identities before any
//! signature is resolved. This deliberately does not inspect type parameter
//! bounds or expand user-written type aliases.

use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{self, DefId, Spanned, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	tir::defs::{EnumIdx, GlobalIdx, MemoryIdx, StructIdx},
	vfs::FileId,
};

use super::{
	bounds::report_not_a_trait_bound,
	defs::{
		AstEntry, AstNodeRef, BindingKey, BindingNamespace, DefKind,
		DefinitionRegistry, DuplicateDefinitionDiagnostic, InherentImplIdx,
		NamespaceIdx, TraitIdx, TraitImplIdx, TypeAliasIdx,
	},
	paths::PathResolver,
	signatures::TypeContext,
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
	Struct(StructIdx),
	Enum(EnumIdx),
	Memory(MemoryIdx),
	Global(GlobalIdx),
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
			Type::Memory { memory_index } => Self::Memory(*memory_index),
			Type::Global { global_index } => Self::Global(*global_index),
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

#[derive(Clone, Copy)]
pub(super) struct TraitImplHead {
	pub(super) trait_def: Option<Spanned<TraitIdx>>,
	pub(super) target: Option<Spanned<ImplTarget>>,
}

pub(super) struct ImplDispatch {
	inherent: HashMap<ImplTarget, Vec<InherentImplIdx>>,
	traits: HashMap<ImplTarget, Vec<(TraitIdx, TraitImplIdx)>>,
	inherent_targets: Vec<Option<Spanned<ImplTarget>>>,
	trait_headers: Vec<TraitImplHead>,
}

struct ImplDispatchBuilder<'a, 'ast> {
	diagnostics: &'a mut Vec<Diagnostic<FileId>>,
	strings: &'a StringInterner,
	defs: &'a DefinitionRegistry,
	ast_nodes: &'a [AstEntry<'ast>],
	inherent: HashMap<ImplTarget, Vec<InherentImplIdx>>,
	traits: HashMap<ImplTarget, Vec<(TraitIdx, TraitImplIdx)>>,
	inherent_targets: Vec<Option<Spanned<ImplTarget>>>,
	trait_headers: Vec<TraitImplHead>,
}

impl ImplDispatch {
	pub(super) fn build(
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		defs: &DefinitionRegistry,
		ast_nodes: &[AstEntry<'_>],
	) -> Self {
		ImplDispatchBuilder::new(diagnostics, strings, defs, ast_nodes).build()
	}

	pub(super) fn inherent_target(
		&self,
		index: InherentImplIdx,
	) -> Option<Spanned<ImplTarget>> {
		self.inherent_targets[usize::from(index)]
	}

	pub(super) fn trait_header(&self, index: TraitImplIdx) -> TraitImplHead {
		self.trait_headers[usize::from(index)]
	}

	pub(super) fn inherent_candidates(
		&self,
		target: ImplTarget,
	) -> &[InherentImplIdx] {
		self.inherent.get(&target).map(Vec::as_slice).unwrap_or(&[])
	}

	pub(super) fn trait_candidates(
		&self,
		target: ImplTarget,
	) -> &[(TraitIdx, TraitImplIdx)] {
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
	) -> Self {
		Self {
			diagnostics,
			strings,
			defs,
			ast_nodes,
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
						target: target_path,
						..
					} = item
					else {
						unreachable!()
					};
					let Ok(target) = self.resolve_target(
						entry.file_id,
						entry.namespace,
						target_path,
						type_params,
					) else {
						continue;
					};
					let target = Spanned {
						inner: target,
						span: target_path.span(),
					};
					self.inherent_targets[usize::from(*block_index)] =
						Some(target);
					self.register_inherent(target, *block_index, entry.file_id);
				}
				AstNodeRef::TraitImplBlock { item, block_index } => {
					let ast::Item::TraitImpl {
						type_params,
						trait_name,
						target: target_path,
						..
					} = item
					else {
						unreachable!()
					};
					let target = self
						.resolve_target(
							entry.file_id,
							entry.namespace,
							target_path,
							type_params,
						)
						.ok()
						.map(|inner| Spanned {
							inner,
							span: target_path.span(),
						});
					let trait_idx = self.resolve_trait(
						entry.file_id,
						entry.namespace,
						trait_name,
					);
					self.trait_headers[usize::from(*block_index)] =
						TraitImplHead {
							trait_def: trait_idx.map(|idx| Spanned {
								inner: idx,
								span: trait_name.span(),
							}),
							target,
						};
					if let (Some(trait_idx), Some(target)) = (trait_idx, target)
					{
						self.register_trait(
							target,
							trait_idx,
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
						let target = self
							.resolve_target(
								entry.file_id,
								entry.namespace,
								&member.inner.inner,
								&[],
							)
							.ok()
							.map(|inner| Spanned {
								inner,
								span: member.inner.span,
							});
						self.trait_headers[usize::from(impl_index)] =
							TraitImplHead {
								trait_def: Some(Spanned {
									inner: def.trait_index,
									span: member.inner.span,
								}),
								target,
							};
						if let Some(target) = target {
							self.register_trait(
								target,
								def.trait_index,
								name.inner,
								impl_index,
								entry.file_id,
							);
						}
					}
				}
				AstNodeRef::Memory { memory_index, item } => {
					let ast::Item::Memory { name, .. } = item else {
						unreachable!()
					};
					self.register_memory_impl(
						*memory_index,
						name.span,
						entry.file_id,
					);
				}
				AstNodeRef::ImportedMemory { memory_index, decl } => {
					let ast::ImportDeclaration::Memory { name, .. } = decl
					else {
						unreachable!()
					};
					self.register_memory_impl(
						*memory_index,
						name.span,
						entry.file_id,
					);
				}
				AstNodeRef::Global { global_index, item } => {
					let ast::Item::Global { name, mut_span, .. } = item else {
						unreachable!()
					};
					self.register_global_impl(
						*global_index,
						name.span,
						*mut_span,
						entry.file_id,
					);
				}
				AstNodeRef::ImportedGlobal { global_index, decl } => {
					let ast::ImportDeclaration::Global {
						name, mut_span, ..
					} = decl
					else {
						unreachable!()
					};
					self.register_global_impl(
						*global_index,
						name.span,
						*mut_span,
						entry.file_id,
					);
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
		trait_idx: TraitIdx,
		trait_name: SymbolU32,
		trait_impl_idx: TraitImplIdx,
		file_id: FileId,
	) {
		let bucket = self.traits.entry(target.inner).or_default();
		if let Some(&(_, earlier)) =
			bucket.iter().find(|(idx, _)| *idx == trait_idx)
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
		bucket.push((trait_idx, trait_impl_idx));
	}

	/// Registers a `memory` declaration's synthetic `Memory` impl under its
	/// own `ImplTarget::Memory` bucket. Shared by `AstNodeRef::Memory` and
	/// `AstNodeRef::ImportedMemory` — a memory's target is its own identity
	/// either way, so a locally declared memory and an imported one register
	/// exactly the same way.
	fn register_memory_impl(
		&mut self,
		memory_index: MemoryIdx,
		name_span: TextSpan,
		file_id: FileId,
	) {
		let defs = self.defs;
		let memory_def = &defs.memories[usize::from(memory_index)];
		let trait_idx = defs.intrinsics.memory.unwrap_or_else(|| {
			panic!(
				"the stdlib package must declare a `Memory` trait — every `memory` declaration needs one to synthesize its impl against"
			)
		});
		self.trait_headers[usize::from(memory_def.trait_impl_index)] =
			TraitImplHead {
				trait_def: Some(Spanned {
					inner: trait_idx,
					span: name_span,
				}),
				target: Some(Spanned {
					inner: ImplTarget::Memory(memory_index),
					span: name_span,
				}),
			};
		self.register_trait(
			Spanned {
				inner: ImplTarget::Memory(memory_index),
				span: name_span,
			},
			trait_idx,
			defs.traits[usize::from(trait_idx)].name.inner,
			memory_def.trait_impl_index,
			file_id,
		);
	}

	/// Registers a `global` declaration's synthetic `Global` impl (and, for
	/// `global mut`, its `GlobalMut` impl too) under its own
	/// `ImplTarget::Global` bucket. Shared by `AstNodeRef::Global` and
	/// `AstNodeRef::ImportedGlobal`, same reasoning as `register_memory_impl`.
	fn register_global_impl(
		&mut self,
		global_index: GlobalIdx,
		name_span: TextSpan,
		mut_span: Option<TextSpan>,
		file_id: FileId,
	) {
		let defs = self.defs;
		let global_def = &defs.globals[usize::from(global_index)];
		let global_trait_idx = defs.intrinsics.global.unwrap_or_else(|| {
			panic!(
				"the stdlib package must declare a `Global` trait — every `global` declaration needs one to synthesize its impl against"
			)
		});
		self.trait_headers[usize::from(global_def.trait_impl_index)] =
			TraitImplHead {
				trait_def: Some(Spanned {
					inner: global_trait_idx,
					span: name_span,
				}),
				target: Some(Spanned {
					inner: ImplTarget::Global(global_index),
					span: name_span,
				}),
			};
		self.register_trait(
			Spanned {
				inner: ImplTarget::Global(global_index),
				span: name_span,
			},
			global_trait_idx,
			defs.traits[usize::from(global_trait_idx)].name.inner,
			global_def.trait_impl_index,
			file_id,
		);
		if let Some(mut_trait_impl_index) = global_def.mut_trait_impl_index {
			debug_assert!(mut_span.is_some());
			let global_mut_trait_idx =
				defs.intrinsics.global_mut.unwrap_or_else(|| {
					panic!(
						"the stdlib package must declare a `GlobalMut` trait — every `global mut` declaration needs one to synthesize its impl against"
					)
				});
			self.trait_headers[usize::from(mut_trait_impl_index)] =
				TraitImplHead {
					trait_def: Some(Spanned {
						inner: global_mut_trait_idx,
						span: name_span,
					}),
					target: Some(Spanned {
						inner: ImplTarget::Global(global_index),
						span: name_span,
					}),
				};
			self.register_trait(
				Spanned {
					inner: ImplTarget::Global(global_index),
					span: name_span,
				},
				global_mut_trait_idx,
				defs.traits[usize::from(global_mut_trait_idx)].name.inner,
				mut_trait_impl_index,
				file_id,
			);
		}
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
		index: InherentImplIdx,
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
		namespace: NamespaceIdx,
		path: &ast::Path,
		params: &[ast::TypeParam],
	) -> Result<ImplTarget, ()> {
		if params
			.iter()
			.any(|param| param.name.inner == path.segments[0].ident.inner)
		{
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::InvalidImplTarget.code())
					.with_message(
						"cannot use a type parameter as an impl target",
					)
					.with_label(
						SourceSpan::new(file_id, path.span()).primary_label(),
					),
			);
			return Err(());
		}
		let binding = PathResolver::new(self.defs).resolve_path(
			self.diagnostics,
			self.strings,
			file_id,
			namespace,
			&path.segments,
			BindingNamespace::Type,
		);
		let kind = binding.def_key().ok_or(())?.symbol_kind(self.defs);
		let target = match kind {
			DefKind::Struct(idx) => Some(ImplTarget::Struct(idx)),
			DefKind::Enum(idx) => Some(ImplTarget::Enum(idx)),
			// A user-written alias (`type Foo = Bar;`) has no identity of
			// its own to dispatch on — only the closed set of std's own
			// bodiless `#[intrinsic]` aliases (`u8`, `char`, ...) do, via
			// their pre-interned `TypeIndex`. `intrinsic_target` returns
			// `None` for every other alias, same as any non-namespace kind.
			DefKind::TypeAlias(idx) => self.intrinsic_target(idx),
			_ => None,
		};
		target.ok_or_else(|| {
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::InvalidImplTarget.code())
					.with_message(format!(
						"cannot use {} as an impl target",
						kind.noun()
					))
					.with_label(
						SourceSpan::new(file_id, path.span()).primary_label(),
					),
			);
		})
	}

	fn resolve_trait(
		&mut self,
		file_id: FileId,
		namespace: NamespaceIdx,
		path: &ast::Path,
	) -> Option<TraitIdx> {
		let binding = PathResolver::new(self.defs).resolve_path(
			self.diagnostics,
			self.strings,
			file_id,
			namespace,
			&path.segments,
			BindingNamespace::Type,
		);
		match binding.def_key()?.symbol_kind(self.defs) {
			DefKind::Trait(idx) => Some(idx),
			other => {
				self.diagnostics.push(report_not_a_trait_bound(
					file_id,
					self.strings,
					path.segments.last().unwrap().ident,
					other,
				));
				None
			}
		}
	}

	/// The dispatch bucket for `idx`, if it's one of std's own
	/// `#[intrinsic]` primitive aliases — `None` for an ordinary alias.
	/// `never` has no bucket here (nothing can be implemented on it), so
	/// it's the one `IntrinsicDefs` type slot this deliberately excludes.
	fn intrinsic_target(&self, idx: TypeAliasIdx) -> Option<ImplTarget> {
		let intrinsics = &self.defs.intrinsics;
		[
			(intrinsics.u8, ImplTarget::U8),
			(intrinsics.i8, ImplTarget::I8),
			(intrinsics.u16, ImplTarget::U16),
			(intrinsics.i16, ImplTarget::I16),
			(intrinsics.u32, ImplTarget::U32),
			(intrinsics.i32, ImplTarget::I32),
			(intrinsics.u64, ImplTarget::U64),
			(intrinsics.i64, ImplTarget::I64),
			(intrinsics.f32, ImplTarget::F32),
			(intrinsics.f64, ImplTarget::F64),
			(intrinsics.bool, ImplTarget::Bool),
			(intrinsics.char, ImplTarget::Char),
		]
		.into_iter()
		.find_map(|(slot, target)| (slot == Some(idx)).then_some(target))
	}
}

impl TypeContext<'_, '_, '_> {
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
			ImplTarget::Struct(struct_index) => {
				self.types.intern(Type::Struct {
					struct_index,
					type_args: Box::new([]),
				})
			}
			ImplTarget::Enum(enum_index) => {
				self.types.intern(Type::Enum { enum_index })
			}
			ImplTarget::Array | ImplTarget::Slice => {
				unreachable!(
					"array and slice types cannot be path-only impl targets"
				)
			}
			ImplTarget::Memory(_) | ImplTarget::Global(_) => unreachable!(
				"memory/global impls are never resolved through a written path — see ImplTarget's own doc comment"
			),
		}
	}

	pub(super) fn impl_trait_index(&self, def_id: DefId) -> TraitIdx {
		match self.ast_node(def_id) {
			AstNodeRef::Trait { trait_index, .. } => *trait_index,
			AstNodeRef::TypeSet { typeset_index, .. } => {
				self.defs.typesets[usize::from(*typeset_index)].trait_index
			}
			_ => unreachable!("dispatch trait must name a trait or typeset"),
		}
	}
}
