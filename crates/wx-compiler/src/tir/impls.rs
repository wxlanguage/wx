//! Dispatch candidates collected from declaration identities before any
//! signature is resolved. This deliberately does not inspect type parameter
//! bounds or expand user-written type aliases.

use rustc_hash::FxHashMap;

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{self, Spanned, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	tir::decls::{EnumIdx, FunctionIdx, GlobalIdx, MemoryIdx, StructIdx},
	vfs::FileId,
};

use super::{
	bounds::report_not_a_trait_bound,
	decls::{
		AstEntry, AstNodeRef, BindingKey, DeclKind, Declarations,
		DuplicateDefinitionDiagnostic, InherentImplIdx, IntrinsicDefs,
		MemberIdx, Scope, Tier, TraitIdx, TraitImplIdx, TypeAliasIdx,
	},
	paths::PathResolver,
	resolutions::NameResolutions,
	signatures::Semantics,
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
	Funcref,
	TypedFuncref,
	Array,
	Slice,
	Struct(StructIdx),
	Enum(EnumIdx),
	Memory(MemoryIdx),
	Global(GlobalIdx),
	Function(FunctionIdx),
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
			Type::Funcref => Self::Funcref,
			Type::TypedFuncref { .. } => Self::TypedFuncref,
			Type::Array { .. } => Self::Array,
			Type::Slice { .. } => Self::Slice,
			Type::Struct { struct_index, .. } => Self::Struct(*struct_index),
			Type::Enum { enum_index } => Self::Enum(*enum_index),
			Type::Memory { memory_index } => Self::Memory(*memory_index),
			Type::Global { global_index } => Self::Global(*global_index),
			Type::Function { func_index, .. } => Self::Function(*func_index),
			Type::Error
			| Type::Infer
			| Type::Never
			| Type::ConstInt
			| Type::ConstFloat
			| Type::ConstChar
			| Type::Tuple { .. }
			| Type::Pointer { .. }
			| Type::TypeParam { .. }
			| Type::TypeProjection { .. }
			| Type::Value { .. }
			| Type::ConstRef { .. } => return None,
		})
	}
}

#[derive(Clone, Copy)]
pub(super) struct TraitImplHead {
	pub(super) trait_decl: Option<Spanned<TraitIdx>>,
	pub(super) target: Option<Spanned<ImplTarget>>,
}

pub(super) struct ImplDispatch {
	inherent: FxHashMap<ImplTarget, Vec<InherentImplIdx>>,
	traits: FxHashMap<ImplTarget, Vec<(TraitIdx, TraitImplIdx)>>,
	inherent_targets: Vec<Option<Spanned<ImplTarget>>>,
	trait_headers: Vec<TraitImplHead>,
}

struct ImplDispatchBuilder<'a, 'ast> {
	diagnostics: &'a mut Vec<Diagnostic<FileId>>,
	resolutions: &'a mut NameResolutions,
	strings: &'a StringInterner,
	decls: &'a Declarations,
	ast_nodes: &'a [AstEntry<'ast>],
	inherent: FxHashMap<ImplTarget, Vec<InherentImplIdx>>,
	traits: FxHashMap<ImplTarget, Vec<(TraitIdx, TraitImplIdx)>>,
	inherent_targets: Vec<Option<Spanned<ImplTarget>>>,
	trait_headers: Vec<TraitImplHead>,
}

impl IntrinsicDefs {
	/// Whether `ty` has `trait_index` by the compiler's rule: a typed
	/// function reference is a `Call`; every pointer is a `Pointer`; every
	/// slice and array (`[T]`, `[T; N]`) is a `Slice`, and an array an
	/// `Array`; every enum is `Eq` and `PartialEq` because its repr is an
	/// `Integer` typeset member. `None` when the rule says nothing about the
	/// pair.
	pub(super) fn implements_structurally(
		&self,
		ty: &Type,
		trait_index: TraitIdx,
	) -> Option<bool> {
		let this = Some(trait_index);
		let is_array = match *ty {
			Type::TypedFuncref { .. } => {
				return (this == self.call).then_some(true);
			}
			Type::Enum { .. } => {
				return (this == self.eq || this == self.partial_eq)
					.then_some(true);
			}
			Type::Pointer { .. } => {
				return (this == self.pointer).then_some(true);
			}
			Type::Slice { .. } => false,
			Type::Array { .. } => true,
			_ => return None,
		};
		if this == self.slice {
			Some(true)
		} else if this == self.array {
			Some(is_array)
		} else {
			None
		}
	}
}

impl ImplDispatch {
	pub(super) fn build(
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		resolutions: &mut NameResolutions,
		strings: &StringInterner,
		decls: &Declarations,
		ast_nodes: &[AstEntry<'_>],
	) -> Self {
		ImplDispatchBuilder::new(
			diagnostics,
			resolutions,
			strings,
			decls,
			ast_nodes,
		)
		.build()
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
		resolutions: &'a mut NameResolutions,
		strings: &'a StringInterner,
		decls: &'a Declarations,
		ast_nodes: &'a [AstEntry<'ast>],
	) -> Self {
		Self {
			diagnostics,
			resolutions,
			strings,
			decls,
			ast_nodes,
			inherent: FxHashMap::default(),
			traits: FxHashMap::default(),
			inherent_targets: vec![None; decls.inherent_impls.len()],
			trait_headers: vec![
				TraitImplHead {
					trait_decl: None,
					target: None,
				};
				decls.trait_impls.len()
			],
		}
	}

	fn build(mut self) -> ImplDispatch {
		let ast_nodes = self.ast_nodes;
		let decls = self.decls;
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
					self.check_inherent_impl_locality(
						entry.file_id,
						entry.namespace,
						target,
					);
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
							trait_decl: trait_idx.map(|idx| Spanned {
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
					let decl = &decls.typesets[usize::from(*typeset_index)];
					for (member, &impl_index) in
						members.iter().zip(decl.member_impls.iter())
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
								trait_decl: Some(Spanned {
									inner: decl.trait_index,
									span: member.inner.span,
								}),
								target,
							};
						if let Some(target) = target {
							self.register_trait(
								target,
								decl.trait_index,
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
				AstNodeRef::ImportedMemory {
					memory_index,
					import_block,
					..
				} => {
					let ast::ImportDeclaration::Memory { name, .. } =
						import_block
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
				AstNodeRef::ImportedGlobal {
					global_index,
					import_block,
					..
				} => {
					let ast::ImportDeclaration::Global {
						name, mut_span, ..
					} = import_block
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
				AstNodeRef::Function { func_index, .. } => {
					self.register_function_impls(*func_index, entry.file_id);
				}
				AstNodeRef::ImportedFunction { function_index, .. }
				| AstNodeRef::TraitFunction { function_index, .. }
				| AstNodeRef::InherentImplFunction { function_index, .. }
				| AstNodeRef::TraitImplFunction { function_index, .. } => {
					self.register_function_impls(
						*function_index,
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
							self.decls.trait_impls[usize::from(earlier)]
								.file_id,
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
		let decls = self.decls;
		let memory_decl = &decls.memories[usize::from(memory_index)];
		let trait_idx = decls.intrinsics.memory.unwrap_or_else(|| {
			panic!(
				"the core package must declare a `Memory` trait — every `memory` declaration needs one to synthesize its impl against"
			)
		});
		self.trait_headers[usize::from(memory_decl.trait_impl_index)] =
			TraitImplHead {
				trait_decl: Some(Spanned {
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
			decls.name(trait_idx).inner,
			memory_decl.trait_impl_index,
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
		let decls = self.decls;
		let global_decl = &decls.globals[usize::from(global_index)];
		let global_trait_idx = decls.intrinsics.global.unwrap_or_else(|| {
			panic!(
				"the core package must declare a `Global` trait — every `global` declaration needs one to synthesize its impl against"
			)
		});
		self.trait_headers[usize::from(global_decl.trait_impl_index)] =
			TraitImplHead {
				trait_decl: Some(Spanned {
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
			decls.name(global_trait_idx).inner,
			global_decl.trait_impl_index,
			file_id,
		);
		if let Some(mut_trait_impl_index) = global_decl.mut_trait_impl_index {
			debug_assert!(mut_span.is_some());
			let global_mut_trait_idx =
				decls.intrinsics.global_mut.unwrap_or_else(|| {
					panic!(
						"the core package must declare a `GlobalMut` trait — every `global mut` declaration needs one to synthesize its impl against"
					)
				});
			self.trait_headers[usize::from(mut_trait_impl_index)] =
				TraitImplHead {
					trait_decl: Some(Spanned {
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
				decls.name(global_mut_trait_idx).inner,
				mut_trait_impl_index,
				file_id,
			);
		}
	}

	/// Registers a function's synthetic `Call` and
	/// `Function` impls under its own `ImplTarget::Function` bucket, same
	/// reasoning as `register_global_impl`.
	fn register_function_impls(
		&mut self,
		func_index: FunctionIdx,
		file_id: FileId,
	) {
		let decls = self.decls;
		let function_decl = &decls.functions[usize::from(func_index)];
		let function_impls = function_decl.function_impls;
		let name_span = decls.item(function_decl.loc).name.span;
		let call_trait_idx = decls.intrinsics.call.unwrap_or_else(|| {
			panic!(
				"the core package must declare a `Call` trait — every function needs one to synthesize its impl against"
			)
		});
		let function_trait_idx = decls.intrinsics.function.unwrap_or_else(|| {
			panic!(
				"the core package must declare a `Function` trait — every function needs one to synthesize its impl against"
			)
		});
		for (trait_idx, trait_impl_index) in [
			(call_trait_idx, function_impls.call_impl_index),
			(function_trait_idx, function_impls.function_impl_index),
		] {
			self.trait_headers[usize::from(trait_impl_index)] = TraitImplHead {
				trait_decl: Some(Spanned {
					inner: trait_idx,
					span: name_span,
				}),
				target: Some(Spanned {
					inner: ImplTarget::Function(func_index),
					span: name_span,
				}),
			};
			self.register_trait(
				Spanned {
					inner: ImplTarget::Function(func_index),
					span: name_span,
				},
				trait_idx,
				decls.name(trait_idx).inner,
				trait_impl_index,
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
	/// `bindings`/`members` (already built by `decls.rs`) rather than
	/// keeping a second copy of this data just for the check.
	fn register_inherent(
		&mut self,
		target: Spanned<ImplTarget>,
		index: InherentImplIdx,
		file_id: FileId,
	) {
		let decls = self.decls;
		let new_impl = &decls.inherent_impls[usize::from(index)];
		let earlier_in_bucket = self
			.inherent
			.get(&target.inner)
			.map(Vec::as_slice)
			.unwrap_or(&[]);

		// Sorted by source position so a diagnostic here can't depend on
		// `HashMap` iteration order. A function is bound in both tiers but is
		// one definition: its value key comes first, and it is reported once.
		let mut new_members: Vec<(BindingKey, MemberIdx, TextSpan)> = new_impl
			.bindings
			.iter()
			.map(|(&key, &member)| {
				(key, member, new_impl.members[usize::from(member)].span)
			})
			.collect();
		new_members.sort_by_key(|&(key, _, span)| {
			(span.start, key.tier == Tier::Type)
		});
		let mut reported: Vec<MemberIdx> = Vec::new();

		for (key, member, span) in new_members {
			if reported.contains(&member) {
				continue;
			}
			let collision = earlier_in_bucket.iter().find_map(|&earlier| {
				let earlier_impl = &decls.inherent_impls[usize::from(earlier)];
				earlier_impl.bindings.get(&key).map(|&member| {
					(
						earlier_impl.file_id,
						earlier_impl.members[usize::from(member)].span,
					)
				})
			});
			if let Some((earlier_file, earlier_span)) = collision {
				reported.push(member);
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

	/// Inherent members belong to the package defining their target. Builtin
	/// constructors belong to core; named targets keep their declaration's
	/// owner even when reached through an import or a package instance.
	/// Trait impls deliberately have no such restriction.
	fn check_inherent_impl_locality(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		target: Spanned<ImplTarget>,
	) {
		let decls = self.decls;
		let target_scope = match target.inner {
			ImplTarget::Struct(index) => {
				decls.scope(decls.structs[usize::from(index)].loc)
			}
			ImplTarget::Enum(index) => {
				decls.scope(decls.enums[usize::from(index)].loc)
			}
			ImplTarget::Memory(index) => {
				decls.scope(decls.memories[usize::from(index)].loc)
			}
			ImplTarget::Global(index) => {
				decls.scope(decls.globals[usize::from(index)].loc)
			}
			ImplTarget::Function(index) => {
				decls.scope(decls.functions[usize::from(index)].loc)
			}
			ImplTarget::U8
			| ImplTarget::I8
			| ImplTarget::U16
			| ImplTarget::I16
			| ImplTarget::U32
			| ImplTarget::I32
			| ImplTarget::U64
			| ImplTarget::I64
			| ImplTarget::F32
			| ImplTarget::F64
			| ImplTarget::Funcref
			| ImplTarget::TypedFuncref
			| ImplTarget::Array
			| ImplTarget::Slice => Scope::Package(decls.core_package),
		};
		if decls.namespaces.scope(target_scope).package_id
			== decls.namespaces.scope(namespace).package_id
		{
			return;
		}
		self.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::ForeignImplTarget.code())
				.with_message(
					"cannot define inherent `impl` for a type outside of the \
					 package where the type is defined",
				)
				.with_label(
					SourceSpan::new(file_id, target.span)
						.primary_label()
						.with_message(
							"impl for type defined outside of package",
						),
				)
				.with_note(
					"consider defining a trait and implementing it for the \
					 type, or wrapping it in a struct of your own and \
					 implementing that instead",
				),
		);
	}

	fn resolve_target(
		&mut self,
		file_id: FileId,
		namespace: Scope,
		path: &ast::Path,
		params: &[Spanned<ast::TypeParam>],
	) -> Result<ImplTarget, ()> {
		if params.iter().any(|param| {
			param.inner.name().inner == path.segments[0].ident.inner
		}) {
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
		let definition = PathResolver::new(
			self.diagnostics,
			self.resolutions,
			self.strings,
			self.decls,
		)
		.resolve_definition(file_id, namespace, &path.segments, Tier::Type);
		let kind = definition?.symbol_kind(self.decls);
		let target = match kind {
			DeclKind::Struct(idx) => Some(ImplTarget::Struct(idx)),
			DeclKind::Enum(idx) => Some(ImplTarget::Enum(idx)),
			// A user-written alias (`type Foo = Bar;`) has no identity of
			// its own to dispatch on — only the closed set of core's own
			// bodiless `#[intrinsic]` aliases (`u8`, `funcref`, ...) do, via
			// their pre-interned `TypeIndex`. `intrinsic_target` returns
			// `None` for every other alias, same as any non-namespace kind.
			DeclKind::TypeAlias(idx) => self.intrinsic_target(idx),
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
		namespace: Scope,
		path: &ast::Path,
	) -> Option<TraitIdx> {
		let definition = PathResolver::new(
			self.diagnostics,
			self.resolutions,
			self.strings,
			self.decls,
		)
		.resolve_definition(file_id, namespace, &path.segments, Tier::Type);
		match definition.ok()?.symbol_kind(self.decls) {
			DeclKind::Trait(idx) => Some(idx),
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

	/// The dispatch bucket for `idx`, if it's one of core's own
	/// `#[intrinsic]` primitive aliases — `None` for an ordinary alias.
	/// `never` has no bucket here (nothing can be implemented on it), so
	/// it's the one `IntrinsicDefs` type slot this deliberately excludes.
	fn intrinsic_target(&self, idx: TypeAliasIdx) -> Option<ImplTarget> {
		let intrinsics = &self.decls.intrinsics;
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
			(intrinsics.funcref, ImplTarget::Funcref),
		]
		.into_iter()
		.find_map(|(slot, target)| (slot == Some(idx)).then_some(target))
	}
}

impl Semantics {
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
			ImplTarget::Funcref => TypeIndex::FUNCREF,
			ImplTarget::Struct(struct_index) => {
				self.types.intern_struct(struct_index, &[])
			}
			ImplTarget::Enum(enum_index) => {
				self.types.intern(Type::Enum { enum_index })
			}
			ImplTarget::TypedFuncref
			| ImplTarget::Array
			| ImplTarget::Slice => {
				unreachable!(
					"function reference, array and slice types cannot be path-only impl targets"
				)
			}
			ImplTarget::Memory(_)
			| ImplTarget::Global(_)
			| ImplTarget::Function(_) => unreachable!(
				"memory/global/function impls are never resolved through a written path — see ImplTarget's own doc comment"
			),
		}
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

	use super::*;
	use crate::ast::Keyword;
	use crate::testing::DiagnosticView;
	use crate::vfs::{self, Files};

	struct TestCase {
		files: Files,
		diagnostics: Vec<Diagnostic<FileId>>,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut strings = Keyword::create_interner();
			let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
			builder.load_core();
			let root = builder
				.load_package(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)])),
				)
				.unwrap();
			Self::from_graph(builder.build(root), strings)
		}

		/// Collect declarations and dispatch candidates only: signature and
		/// body checking are not needed to establish an impl's ownership.
		fn from_graph(
			graph: vfs::CompilationUnit,
			mut strings: StringInterner,
		) -> Self {
			DiagnosticView::new(
				"parse/link",
				&graph.collect_diagnostics(),
				&graph.files,
			)
			.assert_no_errors();
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (decls, ast_nodes) = Declarations::build(
				&graph.packages,
				&graph.asts,
				&graph.files,
				&mut strings,
				&mut diagnostics,
				&mut resolutions,
				graph.core_package,
				graph.root_package,
			);
			DiagnosticView::new("declarations", &diagnostics, &graph.files)
				.assert_none();
			ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				&strings,
				&decls,
				&ast_nodes,
			);
			Self {
				files: graph.files,
				diagnostics,
			}
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new("impl dispatch", &self.diagnostics, &self.files)
		}
	}

	#[test]
	fn inherent_impl_locality_rejects_foreign_targets_through_imports() {
		const SOURCE: &str = indoc! {r#"
			package "dep" as dep;
			use dep::Point as Imported;
			impl Imported {}
			mod nested {
				impl super::dep::Kind {}
			}
			trait Extension {}
			impl Extension for Imported {}
			impl Extension for dep::Kind {}
		"#};
		let mut strings = Keyword::create_interner();
		let name = strings.get_or_intern("dep");
		let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
		builder.load_core();
		let workspace = vfs::VirtualFileSource::from_relative(HashMap::from([
			("main.wx".to_string(), SOURCE.to_string()),
			(
				"dep.wx".to_string(),
				indoc! {"
				pub struct Point();
				pub enum Kind(u8) { A = 0 }
				impl Point {}
				mod nested { impl super::Kind {} }
			"}
				.to_string(),
			),
		]));
		let dep = builder
			.load_package(vfs::AbsolutePath::new("/dep.wx"), &workspace)
			.unwrap();
		let root = builder
			.load_package(vfs::AbsolutePath::new("/main.wx"), &workspace)
			.unwrap();
		builder.add_dependency(root, name, dep);
		let graph = builder.build(root);
		let case = TestCase::from_graph(graph, strings);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ForeignImplTarget,
			DiagnosticCode::ForeignImplTarget,
		]);
		for (diagnostic, target) in case
			.diagnostics
			.iter()
			.zip(["Imported", "super::dep::Kind"])
		{
			assert_eq!(
				diagnostic.severity,
				codespan_reporting::diagnostic::Severity::Error
			);
			assert_eq!(
				diagnostic.message,
				"cannot define inherent `impl` for a type outside of the package where the type is defined"
			);
			assert_eq!(diagnostic.labels.len(), 1);
			let label = &diagnostic.labels[0];
			assert_eq!(
				label.style,
				codespan_reporting::diagnostic::LabelStyle::Primary
			);
			let file = case.files.get(label.file_id).unwrap();
			assert_eq!(file.source, SOURCE);
			assert_eq!(&file.source[label.range.clone()], target);
			assert_eq!(
				label.message,
				"impl for type defined outside of package"
			);
			assert_eq!(
				diagnostic.notes,
				[
					"consider defining a trait and implementing it for the type, or wrapping it in a struct of your own and implementing that instead"
				]
			);
		}
	}

	#[test]
	fn inherent_impl_locality_allows_other_files_of_the_defining_package() {
		let mut strings = Keyword::create_interner();
		let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
		builder.load_core();
		let workspace = vfs::VirtualFileSource::from_relative(HashMap::from([
			(
				"main.wx".to_string(),
				indoc! {"
				mod geom;
				use geom::Point;
				impl<T: StackValue> Point<T> {}
				mod nested { impl super::geom::Kind {} }
			"}
				.to_string(),
			),
			(
				"geom.wx".to_string(),
				"pub struct Point<T>(T); pub enum Kind(u8) { A = 0 }"
					.to_string(),
			),
		]));
		let root = builder
			.load_package(vfs::AbsolutePath::new("/main.wx"), &workspace)
			.unwrap();
		let graph = builder.build(root);
		let case = TestCase::from_graph(graph, strings);
		case.diagnostics().assert_none();
	}

	#[test]
	fn inherent_impl_locality_reserves_primitives_and_core_types_for_core() {
		for target in [
			"u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64", "f32", "f64",
			"funcref", "Bool", "Char",
		] {
			let case = TestCase::new(&format!(
				"use core::{target} as Imported; impl Imported {{}} \
				 trait Extension {{}} impl Extension for Imported {{}}"
			));
			case.diagnostics()
				.assert_codes(&[DiagnosticCode::ForeignImplTarget]);
		}
	}

	#[test]
	fn inherent_impl_locality_allows_core_to_implement_its_builtins() {
		let source = indoc! {"
			type u8; type u32; type funcref;
			enum Bool(u8) { False = 0, True = 1 }
			struct Char(value: u32);
			mod nested {
				impl u8 {} impl u32 {} impl funcref {}
				impl Bool {} impl Char {}
			}
		"};
		let mut strings = Keyword::create_interner();
		let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
		let root = builder
			.load_package(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					source.to_string(),
				)])),
			)
			.unwrap();
		builder.set_core(root);
		let case = TestCase::from_graph(builder.build(root), strings);
		case.diagnostics().assert_none();
	}
}
