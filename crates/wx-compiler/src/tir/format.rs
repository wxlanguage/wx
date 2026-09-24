//! Renders a resolved [`TypeIndex`] back into source-like text for
//! diagnostics — the one place a `Type` gets turned into a string. Every
//! other module that needs to name a type in a message goes through
//! [`TypeFormatter::display_type`] rather than matching on [`Type`] itself.
//!
//! A separate borrowing entity (the legacy `TypeFormatter<'a>`'s own
//! shape), not methods directly on `SignatureBuilder`: formatting is a
//! read-only concern with its own vocabulary (`write_type`, `write_bounds`,
//! ...), and keeping it off `SignatureBuilder` means a call site can hold
//! one to build a message while the surrounding code is about to mutate
//! `self` right after — the same reason the legacy one existed as its own
//! type rather than living on the (bigger, `&mut`-heavy) `Builder`.
//!
//! Holds exactly the five read-only pieces it actually reads —
//! `types`/`defs`/`strings` plus `type_envs` for a `TypeParam`'s name, and
//! `ast_nodes` (an `AstNodeLookup`, not the whole `SignatureBuilder`) for a
//! struct/enum/function's — rather than one `&SignatureBuilder` borrow.
//! `SignatureBuilder` has ~20 other fields (a diagnostics sink, the
//! in-progress `query_stack`, every still-growing signature vector, ...)
//! that formatting a type never touches; a formatter built from the whole
//! thing would borrow all of it just to read four parts of it. Nothing
//! outside Phase 2 needs to format a type yet — a frozen `SignatureRegistry`
//! has no `ast_nodes` to read a struct/enum/function's name from at all
//! (see `AstNodeLookup`'s own doc comment) — so this only ever wraps a
//! `SignatureBuilder`'s pieces. Add a `SignatureRegistry`-backed
//! constructor once that second caller actually exists.

use std::fmt::Write as _;

use crate::ast::{self, DefId, Ownership, StringInterner};

use super::defs::{AstNodeRef, DefinitionRegistry, TraitIndex};
use super::signatures::{AstNodeLookup, SignatureBuilder};
use super::types::{Type, TypeEnvArena, TypeIndex, TypeInterner};

pub(super) struct TypeFormatter<'a, 'ast> {
	types: &'a TypeInterner,
	defs: &'a DefinitionRegistry,
	strings: &'a StringInterner,
	type_envs: &'a TypeEnvArena,
	ast_nodes: AstNodeLookup<'a, 'ast>,
}

impl<'ast> SignatureBuilder<'ast, '_> {
	pub(super) fn formatter(&self) -> TypeFormatter<'_, 'ast> {
		TypeFormatter {
			types: &self.types,
			defs: self.defs,
			strings: self.strings,
			type_envs: &self.type_envs,
			ast_nodes: self.ast_lookup(),
		}
	}
}

impl TypeFormatter<'_, '_> {
	pub(super) fn display_type(&self, ty: TypeIndex) -> String {
		let mut buffer = String::new();
		self.write_type(&mut buffer, ty);
		buffer
	}

	fn write_type(&self, f: &mut String, ty: TypeIndex) {
		match self.types.resolve(ty) {
			Type::Error => f.push_str("{unknown}"),
			Type::Infer => f.push('_'),
			Type::Unit => f.push_str("()"),
			Type::Never => f.push_str("never"),
			Type::Integer => f.push_str("{integer}"),
			Type::Float => f.push_str("{float}"),
			Type::U8 => f.push_str("u8"),
			Type::I8 => f.push_str("i8"),
			Type::U16 => f.push_str("u16"),
			Type::I16 => f.push_str("i16"),
			Type::U32 => f.push_str("u32"),
			Type::I32 => f.push_str("i32"),
			Type::U64 => f.push_str("u64"),
			Type::I64 => f.push_str("i64"),
			Type::F32 => f.push_str("f32"),
			Type::F64 => f.push_str("f64"),
			Type::Bool => f.push_str("bool"),
			Type::Char => f.push_str("char"),
			Type::Tuple { elements } => {
				f.push('(');
				for (i, element) in elements.iter().copied().enumerate() {
					if i > 0 {
						f.push_str(", ");
					}
					self.write_type(f, element);
				}
				f.push(')');
			}
			Type::Struct { struct_index, args } => {
				let def_id =
					self.defs.structs[usize::from(*struct_index)].def_id;
				self.write_item_name(f, def_id);
				self.write_type_args(f, args);
			}
			Type::Enum { enum_index } => {
				let def_id = self.defs.enums[usize::from(*enum_index)].def_id;
				self.write_item_name(f, def_id);
			}
			Type::Memory { id, .. } => self.write_item_name(f, *id),
			Type::Pointer {
				to,
				memory,
				ownership,
			} => {
				self.write_type(f, *memory);
				f.push_str("::");
				f.push(ownership_sigil(*ownership));
				self.write_type(f, *to);
			}
			Type::Slice {
				of,
				memory,
				ownership,
			} => {
				self.write_type(f, *memory);
				f.push_str("::");
				f.push(ownership_sigil(*ownership));
				f.push('[');
				self.write_type(f, *of);
				f.push(']');
			}
			Type::Array {
				of,
				size,
				memory,
				ownership,
			} => {
				self.write_type(f, *memory);
				f.push_str("::");
				f.push(ownership_sigil(*ownership));
				f.push('[');
				self.write_type(f, *of);
				let _ = write!(f, "; {}]", *size);
			}
			Type::Function { params, result } => {
				let result = *result;
				f.push_str("fn(");
				for (i, param) in params.iter().copied().enumerate() {
					if i > 0 {
						f.push_str(", ");
					}
					self.write_type(f, param);
				}
				f.push_str(") -> ");
				self.write_type(f, result);
			}
			Type::FunctionItem { id, type_args } => {
				f.push_str("fn ");
				self.write_item_name(f, *id);
				self.write_type_args(f, type_args);
			}
			Type::TypeParam {
				env, param_index, ..
			} => {
				let symbol = self.type_envs.param_name(*env, *param_index);
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			Type::AssociatedType {
				trait_index,
				assoc_name,
			} => {
				self.write_trait_name(f, *trait_index);
				f.push_str("::");
				f.push_str(self.strings.resolve(*assoc_name).unwrap());
			}
			// Always qualified (`<Base as Trait>::name`), never the shorter
			// `base::name` a formatter with ambiguity detection could use
			// when only one of `base`'s bounds declares `name` — that check
			// (walking every bound trait `base` carries, same as the legacy
			// `assoc_type_bound_is_ambiguous`) has no second caller yet, so
			// it isn't built. Always-qualified is longer but never wrong.
			Type::AssocTypeProjection {
				trait_index,
				assoc_name,
				base,
			} => {
				f.push('<');
				self.write_type(f, *base);
				f.push_str(" as ");
				self.write_trait_name(f, *trait_index);
				f.push_str(">::");
				f.push_str(self.strings.resolve(*assoc_name).unwrap());
			}
		}
	}

	fn write_type_args(&self, f: &mut String, args: &[TypeIndex]) {
		if args.is_empty() {
			return;
		}
		f.push('<');
		for (i, arg) in args.iter().copied().enumerate() {
			if i > 0 {
				f.push_str(", ");
			}
			self.write_type(f, arg);
		}
		f.push('>');
	}

	fn write_trait_name(&self, f: &mut String, trait_index: TraitIndex) {
		let def_id = self.defs.traits[usize::from(trait_index)].def_id;
		self.write_item_name(f, def_id);
	}

	/// `def_id`'s own written name, read straight from its AST node (via
	/// `ast_node`, not `ensure_signature` — a type being formatted can
	/// legitimately name an item whose own query is still `InProgress`,
	/// e.g. a cyclic struct's field type naming itself). None of the
	/// resolved-signature structs (`StructSignature`, `EnumSignature`, ...)
	/// carry a name of their own to read instead — see their doc comments.
	fn write_item_name(&self, f: &mut String, def_id: DefId) {
		let symbol = match self.ast_nodes.get(def_id) {
			AstNodeRef::RecordStruct { item, .. }
			| AstNodeRef::TupleStruct { item, .. } => {
				let (ast::Item::RecordStruct { name, .. }
				| ast::Item::TupleStruct { name, .. }) = item
				else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::Enum { item, .. } => {
				let ast::Item::Enum { name, .. } = item else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::Memory { item } => {
				let ast::Item::Memory { name, .. } = item else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::Trait { item, .. } => {
				let ast::Item::Trait { name, .. } = item else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::TypeAlias { item } => {
				let ast::Item::TypeAlias { name, .. } = item else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::TypeSet { item, .. } => {
				let ast::Item::TypeSet { name, .. } = item else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::Function { function_index, .. } => {
				self.defs.functions[usize::from(*function_index)].name.inner
			}
			AstNodeRef::TraitFunction { function_index, .. } => {
				self.defs.functions[usize::from(*function_index)].name.inner
			}
			AstNodeRef::TraitConst { item, .. } => {
				let ast::TraitItem::Const { name, .. } = item else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::TraitAssocType { item, .. } => {
				let ast::TraitItem::AssociatedType { name, .. } = item else {
					unreachable!()
				};
				name.inner
			}
			AstNodeRef::Global { .. }
			| AstNodeRef::Constant { .. }
			| AstNodeRef::TraitImplBlock { .. }
			| AstNodeRef::TraitImplFunction { .. }
			| AstNodeRef::TraitImplConstant { .. }
			| AstNodeRef::TraitImplAssocType { .. }
			| AstNodeRef::InherentImplBlock { .. }
			| AstNodeRef::InherentImplFunction { .. }
			| AstNodeRef::InherentImplConst { .. }
			| AstNodeRef::ImportedMemory { .. }
			| AstNodeRef::ImportedFunction { .. }
			| AstNodeRef::ImportedGlobal { .. }
			| AstNodeRef::Export { .. } => {
				unreachable!(
					"no `Type` variant currently projects a name from this item kind"
				)
			}
		};
		f.push_str(self.strings.resolve(symbol).unwrap());
	}
}

fn ownership_sigil(ownership: Ownership) -> char {
	match ownership {
		Ownership::Exclusive => '*',
		Ownership::Shared => '&',
	}
}
