use std::collections::HashMap;
use string_interner::symbol::SymbolU32;
use wx_compiler::ast::{DefId, StringInterner, TextSpan};
use wx_compiler::tir::{
	EnumVariantIndex, ExportItem, FieldAccessKind, ImplTarget, LocalIndex,
	ModuleDeclarationKind, NamespaceIndex, ScopeIndex, SourceSpan, TIR,
	TraitImplIndex, TypeParamOwner,
};
use wx_compiler::vfs::FileId;

#[cfg_attr(debug_assertions, derive(Debug))]
#[derive(Clone, Copy, PartialEq)]
pub enum SymbolKind {
	Function(DefId),
	Global(DefId),
	Const(DefId),
	Memory(DefId),
	Enum(DefId),
	Struct(DefId),
	Namespace(NamespaceIndex),
	Local {
		func_id: DefId,
		scope_idx: ScopeIndex,
		local_idx: LocalIndex,
	},
	Param {
		func_id: DefId,
		param_idx: u32,
	},
	/// The `self` receiver parameter — always param index 0, so unlike
	/// `Param` it doesn't need to carry one. Kept distinct from `Param` for
	/// the same reason `InherentImplSelf`/`TraitImplSelf` are distinct from
	/// `Struct`/`Enum`: it's the `self` keyword, not a name the user chose,
	/// so semantic tokens shouldn't color it like an ordinary parameter.
	SelfParam(DefId),
	EnumVariant {
		enum_id: DefId,
		variant_idx: EnumVariantIndex,
	},
	Label {
		func_id: DefId,
		scope_idx: ScopeIndex,
	},
	Trait(DefId),
	TypeSet(DefId),
	TypeParam {
		owner: TypeParamOwner,
		param_index: u32,
	},
	AssocType {
		trait_id: DefId,
		assoc_name: SymbolU32,
	},
	StructField {
		struct_id: DefId,
		field_idx: u32,
	},
	/// `Self` inside an inherent impl block (`impl Target { .. }`). Kept
	/// distinct from `Struct`/`Enum` (even though it resolves to the same
	/// target type) so `Rename` — which matches purely on `SymbolKind`
	/// equality — doesn't rewrite the `Self` keyword text when renaming the
	/// target type, and semantic tokens don't color `Self` like a type
	/// reference. See `wx_compiler::tir::ImplBlock::self_accesses`.
	InherentImplSelf(u32),
	/// `Self` inside a trait impl (`impl Trait for Target { .. }`). Same
	/// reasoning as `InherentImplSelf`. See
	/// `wx_compiler::tir::TraitImpl::self_accesses`.
	TraitImplSelf(TraitImplIndex),
}

/// One entry in `SymbolIndex::impls_by_target` — an impl block or trait
/// impl, before it's known which. Kept as one merged map (rather than two,
/// one per collection) because every consumer looks up a target's impls and
/// immediately wants both kinds together (see `reference_search_kinds`,
/// `implementation_locations`); a single lookup returning both is simpler
/// than two lookups whose results always get merged anyway.
#[cfg_attr(debug_assertions, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum ImplRef {
	/// Index into `TIR::impl_block_list`.
	Inherent(u32),
	/// Index into `TIR::trait_impls`.
	Trait(TraitImplIndex),
}

#[cfg_attr(debug_assertions, derive(Debug))]
#[derive(Clone, Copy)]
pub struct SpanInfo {
	pub source: SourceSpan,
	pub kind: SymbolKind,
}

/// A named module-level definition, tagged with the namespace it's declared
/// in so completion can filter to what's actually visible from a given
/// cursor position instead of every item in the compilation graph.
#[cfg_attr(debug_assertions, derive(Debug))]
#[derive(Clone)]
pub struct GlobalDefinition {
	pub name: SymbolU32,
	/// `None` means the implicit root namespace.
	pub namespace: Option<NamespaceIndex>,
	pub info: SpanInfo,
}

pub struct SymbolIndex {
	pub definitions: Vec<SpanInfo>,
	pub references: Vec<SpanInfo>,
	/// Redirect targets for synthetic kinds (currently just
	/// `InherentImplSelf`/`TraitImplSelf`) that a query can land *on* but
	/// must never be found *at* — e.g. an impl header's target span is
	/// where `Self` inside that impl redirects to, but clicking the target
	/// name itself must resolve as a plain reference to that type (and
	/// from there, goto-definition to the type's real declaration), not
	/// back to this same spot. Kept out of `definitions` so
	/// `find_at_position` never returns them; consulted only by kind, once
	/// a query has already resolved to one of these kinds some other way.
	pub transparent_definitions: Vec<SpanInfo>,
	/// Named module-level definitions sorted by string value for prefix search.
	/// Excludes scope-sensitive items (locals, params, type params, labels).
	pub global_definitions: Vec<GlobalDefinition>,
	/// Every impl block and trait impl, keyed by the struct/enum it targets
	/// — `ImplTarget` identity only, so every instantiation of a generic
	/// struct's impls lands under the same key (unlike
	/// `TIR::type_trait_impls`, which is keyed by exact `TypeIndex` for a
	/// different consumer — see its doc comment). Lets `References`/
	/// `textDocument/implementation` find every impl of a struct/enum in
	/// O(1) instead of scanning `impl_block_list`/`trait_impls` per query.
	pub impls_by_target: HashMap<ImplTarget, Vec<ImplRef>>,
}

impl SymbolIndex {
	fn new() -> Self {
		Self {
			definitions: Vec::new(),
			references: Vec::new(),
			transparent_definitions: Vec::new(),
			global_definitions: Vec::new(),
			impls_by_target: HashMap::new(),
		}
	}

	fn build(&mut self, interner: &StringInterner) {
		self.definitions.sort_by_key(|e| e.source.span.start);
		self.references.sort_by_key(|e| e.source.span.start);
		self.global_definitions.sort_by(|a, b| {
			interner
				.resolve(a.name)
				.unwrap_or("")
				.cmp(interner.resolve(b.name).unwrap_or(""))
		});
	}

	pub fn find_at_position(
		&self,
		file_id: FileId,
		pos: u32,
	) -> Option<&SpanInfo> {
		let in_defs = find_narrowest(&self.definitions, file_id, pos);
		let in_refs = find_narrowest(&self.references, file_id, pos);
		match (in_defs, in_refs) {
			(Some(d), Some(r)) => {
				let d_len = d.source.span.end - d.source.span.start;
				let r_len = r.source.span.end - r.source.span.start;
				Some(if d_len <= r_len { d } else { r })
			}
			(Some(d), None) => Some(d),
			(None, Some(r)) => Some(r),
			(None, None) => None,
		}
	}

	/// The redirect target for `kind`, if it's one of the synthetic kinds
	/// that has one (see `transparent_definitions`). Falls back to a normal
	/// kind-matching search of `definitions` for every other kind, so
	/// callers can use this as their one lookup regardless of which bucket
	/// a kind's definition happens to live in. The two buckets are a strict
	/// partition — every kind lives in exactly one — so it's enough to
	/// decide which one up front from the shape of `kind` itself, rather
	/// than scanning `transparent_definitions` on every call regardless of
	/// whether `kind` could even be there. `TypeParam` needs the `owner`
	/// check because it's the one variant that appears in both: a trait's
	/// own implicit `Self` (`owner: Trait(_)`) is transparent, but every
	/// other owner's type params are ordinary `definitions`.
	pub fn definition_for_kind(&self, kind: SymbolKind) -> Option<&SpanInfo> {
		let definitions = match kind {
			SymbolKind::InherentImplSelf(_)
			| SymbolKind::TraitImplSelf(_)
			| SymbolKind::TypeParam {
				owner: TypeParamOwner::Trait(_),
				..
			} => &self.transparent_definitions,
			_ => &self.definitions,
		};
		definitions.iter().find(|e| e.kind == kind)
	}
}

fn find_narrowest(
	entries: &[SpanInfo],
	file_id: FileId,
	pos: u32,
) -> Option<&SpanInfo> {
	let upper = entries.partition_point(|e| e.source.span.start <= pos);
	entries[..upper]
		.iter()
		.rev()
		.filter(|e| e.source.file_id == file_id && e.source.span.end >= pos)
		.min_by_key(|e| e.source.span.end - e.source.span.start)
}

pub fn build_symbol_index(tir: &TIR, interner: &StringInterner) -> SymbolIndex {
	let mut index = SymbolIndex::new();
	// `self` is a soft keyword — TIR carries no receiver flag on
	// `FunctionParam`, only the convention (checked ad hoc in half a dozen
	// places in `tir/builder.rs`) that a method's first param is named
	// `self`. `None` only if no method anywhere interned "self" yet (no
	// methods at all), in which case no param can match it below anyway.
	let self_sym = interner.get("self");

	for global in &tir.globals {
		let info = SpanInfo {
			source: SourceSpan::new(global.file_id, global.name.span),
			kind: SymbolKind::Global(global.id),
		};
		index.global_definitions.push(GlobalDefinition {
			name: global.name.inner,
			namespace: global.namespace,
			info,
		});
		index.definitions.push(info);
		for access in &global.accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind: SymbolKind::Global(global.id),
			});
		}
	}

	for function in &tir.functions {
		let func_id = function.id;
		let file_id = function.file_id;

		let info = SpanInfo {
			source: SourceSpan::new(file_id, function.name.span),
			kind: SymbolKind::Function(func_id),
		};
		// Methods/associated functions (`function.parent.is_some()`) are only
		// reachable via `Type::name()` or `value.name()` — never bare `name()`.
		if function.parent.is_none() {
			index.global_definitions.push(GlobalDefinition {
				name: function.name.inner,
				namespace: function.namespace,
				info,
			});
		}
		index.definitions.push(info);

		for access in &function.accesses {
			index.references.push(SpanInfo {
				source: SourceSpan::new(access.file_id, access.span),
				kind: SymbolKind::Function(func_id),
			});
		}

		for (param_index, tp) in function.type_params.iter().enumerate() {
			let kind = SymbolKind::TypeParam {
				owner: TypeParamOwner::Function(func_id),
				param_index: param_index as u32,
			};
			index.definitions.push(SpanInfo {
				source: SourceSpan::new(file_id, tp.name.span),
				kind,
			});
			for access in &tp.accesses {
				index.references.push(SpanInfo {
					source: SourceSpan::new(access.file_id, access.span),
					kind,
				});
			}
		}

		let num_params = function.params.len();
		for (param_idx, param) in function.params.iter().enumerate() {
			let kind = if param_idx == 0 && Some(param.name.inner) == self_sym {
				SymbolKind::SelfParam(func_id)
			} else {
				SymbolKind::Param {
					func_id,
					param_idx: param_idx as u32,
				}
			};
			index.definitions.push(SpanInfo {
				source: SourceSpan::new(file_id, param.name.span),
				kind,
			});
		}

		if let Some(body) = &function.body {
			for (scope_idx, scope) in body.stack.scopes.iter().enumerate() {
				if let Some(label_index) = scope.label {
					let label = &body.stack.labels[label_index as usize];
					let kind = SymbolKind::Label {
						func_id,
						scope_idx: scope_idx as ScopeIndex,
					};
					index.definitions.push(SpanInfo {
						source: SourceSpan::new(file_id, label.name.span),
						kind,
					});
					for access_span in label.accesses.iter().copied() {
						index.references.push(SpanInfo {
							source: SourceSpan::new(file_id, access_span),
							kind,
						});
					}
				}
				for (local_idx, local) in scope.locals.iter().enumerate() {
					let is_param = scope_idx == 0 && local_idx < num_params;
					let kind = if is_param
						&& local_idx == 0 && Some(local.name.inner)
						== self_sym
					{
						SymbolKind::SelfParam(func_id)
					} else if is_param {
						SymbolKind::Param {
							func_id,
							param_idx: local_idx as u32,
						}
					} else {
						SymbolKind::Local {
							func_id,
							scope_idx: scope_idx as ScopeIndex,
							local_idx: local_idx as LocalIndex,
						}
					};
					if !is_param {
						index.definitions.push(SpanInfo {
							source: SourceSpan::new(file_id, local.name.span),
							kind,
						});
					}
					for access in local.accesses.iter().copied() {
						index.references.push(SpanInfo {
							source: SourceSpan::new(file_id, access.span),
							kind,
						});
					}
				}
			}
		}
	}

	for struct_ in tir.structs.iter() {
		let info = SpanInfo {
			source: SourceSpan::new(struct_.file_id, struct_.name.span),
			kind: SymbolKind::Struct(struct_.id),
		};
		index.global_definitions.push(GlobalDefinition {
			name: struct_.name.inner,
			namespace: struct_.namespace,
			info,
		});
		index.definitions.push(info);
		for access in &struct_.accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind: SymbolKind::Struct(struct_.id),
			});
		}
		for (param_index, tp) in struct_.type_params.iter().enumerate() {
			let kind = SymbolKind::TypeParam {
				owner: TypeParamOwner::Struct(struct_.id),
				param_index: param_index as u32,
			};
			index.definitions.push(SpanInfo {
				source: SourceSpan::new(struct_.file_id, tp.name.span),
				kind,
			});
			for access in &tp.accesses {
				index.references.push(SpanInfo {
					source: SourceSpan::new(access.file_id, access.span),
					kind,
				});
			}
		}

		for (field_idx, field) in struct_.fields.iter().enumerate() {
			let kind = SymbolKind::StructField {
				struct_id: struct_.id,
				field_idx: field_idx as u32,
			};
			index.definitions.push(SpanInfo {
				source: SourceSpan::new(struct_.file_id, field.name.span),
				kind,
			});
			for access in &field.accesses {
				if matches!(
					access.kind,
					FieldAccessKind::Read | FieldAccessKind::Init
				) {
					index.references.push(SpanInfo {
						source: SourceSpan::new(access.file_id, access.span),
						kind,
					});
				}
			}
		}
	}

	for enum_ in tir.enums.iter() {
		let info = SpanInfo {
			source: SourceSpan::new(enum_.file_id, enum_.name.span),
			kind: SymbolKind::Enum(enum_.id),
		};
		index.global_definitions.push(GlobalDefinition {
			name: enum_.name.inner,
			namespace: enum_.namespace,
			info,
		});
		index.definitions.push(info);
		for access in &enum_.accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind: SymbolKind::Enum(enum_.id),
			});
		}
		for (variant_idx, variant) in enum_.variants.iter().enumerate() {
			let variant_kind = SymbolKind::EnumVariant {
				enum_id: enum_.id,
				variant_idx: variant_idx as EnumVariantIndex,
			};
			let variant_info = SpanInfo {
				source: SourceSpan::new(enum_.file_id, variant.name.span),
				kind: variant_kind,
			};
			// Unlike methods/associated consts (guarded by `parent.is_none()`
			// above), variants have no "maybe bare, maybe qualified" case to
			// gate on — `Enum::Variant` is the only legal access (see
			// `ResolvedMember::EnumVariant` in `tir/builder.rs`, the sole
			// place variants get resolved, always through member lookup) —
			// so they never belong in `global_definitions` at all.
			index.definitions.push(variant_info);
			for access in &variant.accesses {
				index.references.push(SpanInfo {
					source: *access,
					kind: variant_kind,
				});
			}
		}
	}

	for constant in &tir.constants {
		// `value.is_some()` alone would wrongly exclude associated consts
		// that structurally never have one: a trait's own abstract
		// declaration (`const NAME: T;`, no body) and a memory's
		// compiler-synthesized instantiation of it (e.g. `heap::DATA_END`,
		// forked in `seed_memory_trait_impl_with`). Both are always fully
		// resolved once present in `tir.constants` — `parent.is_some()`
		// alone is enough to index them. Only a *top-level* const
		// (`parent: None`) can be the broken placeholder described at its
		// `AstNodeRef::Const` finalization site — one whose initializer
		// failed to build stays permanently `value: None` and never claims
		// its name, so `value.is_some()` still gates that case correctly.
		if constant.value.is_some() || constant.parent.is_some() {
			let info = SpanInfo {
				source: SourceSpan::new(constant.file_id, constant.name.span),
				kind: SymbolKind::Const(constant.id),
			};
			// Associated consts (`constant.parent.is_some()`) are only
			// reachable via `Type::NAME` — never bare `NAME`.
			if constant.parent.is_none() {
				index.global_definitions.push(GlobalDefinition {
					name: constant.name.inner,
					namespace: constant.namespace,
					info,
				});
			}
			index.definitions.push(info);
			for access in constant.accesses.iter().copied() {
				index.references.push(SpanInfo {
					source: access,
					kind: SymbolKind::Const(constant.id),
				});
			}
		}
	}

	for memory in tir.memories.iter() {
		index.definitions.push(SpanInfo {
			source: SourceSpan::new(memory.file_id, memory.name.span),
			kind: SymbolKind::Memory(memory.id),
		});
		for access in memory.accesses.iter().copied() {
			index.references.push(SpanInfo {
				source: access,
				kind: SymbolKind::Memory(memory.id),
			});
		}
	}

	for (ns_idx, ns) in tir.namespaces.iter().enumerate() {
		let kind = SymbolKind::Namespace(ns_idx as NamespaceIndex);
		let (def_source, name_sym) = match ns.declaration {
			ModuleDeclarationKind::Module(decl_idx) => {
				let decl = &tir.module_decls[decl_idx as usize];
				let source = match decl.own_file_id {
					Some(fid) => SourceSpan::new(fid, TextSpan::new(0, 0)),
					None => {
						SourceSpan::new(decl.declaring_file_id, decl.name.span)
					}
				};
				// The `module foo;` name in the declaring file is itself a reference.
				if decl.own_file_id.is_some() {
					index.references.push(SpanInfo {
						source: SourceSpan::new(
							decl.declaring_file_id,
							decl.name.span,
						),
						kind,
					});
				}
				(source, decl.name.inner)
			}
			ModuleDeclarationKind::Import(import_idx) => {
				let decl = &tir.import_decls[import_idx as usize];
				let (name_sym, span) = match &decl.internal_name {
					Some(n) => (n.inner, n.span),
					None => (decl.external_name.inner, decl.external_name.span),
				};
				(SourceSpan::new(decl.file_id, span), name_sym)
			}
			ModuleDeclarationKind::Crate(_, file_id) => {
				(SourceSpan::new(file_id, TextSpan::new(0, 0)), ns.name)
			}
		};
		let info = SpanInfo {
			source: def_source,
			kind,
		};
		index.global_definitions.push(GlobalDefinition {
			name: name_sym,
			namespace: ns.parent,
			info,
		});
		index.definitions.push(info);
		for access in &ns.accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind,
			});
		}
	}

	for (trait_index, trait_) in tir.traits.iter().enumerate() {
		let kind = SymbolKind::Trait(trait_.id);
		let info = SpanInfo {
			source: SourceSpan::new(trait_.file_id, trait_.name.span),
			kind,
		};
		index.global_definitions.push(GlobalDefinition {
			name: trait_.name.inner,
			namespace: trait_.namespace,
			info,
		});
		index.definitions.push(info);
		for access in &trait_.accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind,
			});
		}

		let self_kind = SymbolKind::TypeParam {
			owner: TypeParamOwner::Trait(trait_index as u32),
			param_index: 0,
		};
		// Same reasoning as `InherentImplSelf`/`TraitImplSelf`: this
		// redirect target sits at the exact same span as the trait's own
		// `Trait(id)` definition just above (`self_type_param.name.span` is
		// set to `trait_.name.span` at construction), so it must stay out
		// of `definitions` — otherwise clicking the trait's own declared
		// name can resolve as this synthetic kind instead, whose redirect
		// target is that same spot, making go-to-definition a no-op.
		index.transparent_definitions.push(SpanInfo {
			source: SourceSpan::new(
				trait_.file_id,
				trait_.self_type_param.name.span,
			),
			kind: self_kind,
		});
		for access in &trait_.self_type_param.accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind: self_kind,
			});
		}

		for (assoc_name, at) in &trait_.assoc_types {
			let at_kind = SymbolKind::AssocType {
				trait_id: trait_.id,
				assoc_name: *assoc_name,
			};
			let at_info = SpanInfo {
				source: SourceSpan::new(trait_.file_id, at.name_span),
				kind: at_kind,
			};
			index.global_definitions.push(GlobalDefinition {
				name: *assoc_name,
				namespace: trait_.namespace,
				info: at_info,
			});
			index.definitions.push(at_info);
			for access in &at.accesses {
				index.references.push(SpanInfo {
					source: *access,
					kind: at_kind,
				});
			}
		}
	}

	for typeset in tir.typesets.iter() {
		let kind = SymbolKind::TypeSet(typeset.id);
		let info = SpanInfo {
			source: SourceSpan::new(typeset.file_id, typeset.name.span),
			kind,
		};
		index.global_definitions.push(GlobalDefinition {
			name: typeset.name.inner,
			namespace: typeset.namespace,
			info,
		});
		index.definitions.push(info);
		for access in &typeset.accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind,
			});
		}
	}

	for (block_idx, block) in tir.inherent_impls.iter().enumerate() {
		if let Ok(target) =
			ImplTarget::from_type(&tir.types[block.target.inner.as_usize()])
		{
			index
				.impls_by_target
				.entry(target)
				.or_default()
				.push(ImplRef::Inherent(block_idx as u32));
		}

		for (param_index, tp) in block.type_params.iter().enumerate() {
			let kind = SymbolKind::TypeParam {
				owner: TypeParamOwner::ImplBlock(block_idx as u32),
				param_index: param_index as u32,
			};
			index.definitions.push(SpanInfo {
				source: SourceSpan::new(block.file_id, tp.name.span),
				kind,
			});
			for access in &tp.accesses {
				index.references.push(SpanInfo {
					source: SourceSpan::new(access.file_id, access.span),
					kind,
				});
			}
		}

		if !block.self_accesses.is_empty() {
			let kind = SymbolKind::InherentImplSelf(block_idx as u32);
			index.transparent_definitions.push(SpanInfo {
				source: SourceSpan::new(block.file_id, block.target.span),
				kind,
			});
			for access in &block.self_accesses {
				index.references.push(SpanInfo {
					source: *access,
					kind,
				});
			}
		}
	}

	for (trait_impl_index, trait_impl) in tir.trait_impls.iter().enumerate() {
		if let Ok(target) = ImplTarget::from_type(
			&tir.types[trait_impl.target.inner.as_usize()],
		) {
			index
				.impls_by_target
				.entry(target)
				.or_default()
				.push(ImplRef::Trait(trait_impl_index as TraitImplIndex));
		}

		if trait_impl.self_accesses.is_empty() {
			continue;
		}
		let kind =
			SymbolKind::TraitImplSelf(trait_impl_index as TraitImplIndex);
		index.transparent_definitions.push(SpanInfo {
			source: SourceSpan::new(trait_impl.file_id, trait_impl.target.span),
			kind,
		});
		for access in &trait_impl.self_accesses {
			index.references.push(SpanInfo {
				source: *access,
				kind,
			});
		}
	}

	for export in tir.exports.values() {
		match export {
			ExportItem::Function {
				internal_name, id, ..
			} => {
				if let Some(fi) = tir.function_index(*id) {
					index.references.push(SpanInfo {
						source: SourceSpan::new(
							tir.functions[fi as usize].file_id,
							internal_name.span,
						),
						kind: SymbolKind::Function(*id),
					});
				}
			}
			ExportItem::Global {
				internal_name, id, ..
			} => {
				if let Some(gi) = tir.global_index(*id) {
					index.references.push(SpanInfo {
						source: SourceSpan::new(
							tir.globals[gi as usize].file_id,
							internal_name.span,
						),
						kind: SymbolKind::Global(*id),
					});
				}
			}
			ExportItem::Memory {
				internal_name, id, ..
			} => {
				if let Some(mi) = tir.memory_index(*id) {
					index.references.push(SpanInfo {
						source: SourceSpan::new(
							tir.memories[mi as usize].file_id,
							internal_name.span,
						),
						kind: SymbolKind::Memory(*id),
					});
				}
			}
		}
	}

	index.build(interner);
	index
}
