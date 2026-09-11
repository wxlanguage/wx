//! `TypeCtx` — the minimal context for *materializing* and naming types:
//! `&mut TypeInterner` (to re-intern substituted / projected types), plus a
//! read-only `&ItemRegistry` (to look impls and associated types up) and
//! `&StringInterner` (to name what it finds). The interner is shared, not
//! mutable: nothing here mints a symbol.
//!
//! Split out of `Builder` so an operation that only needs to build types can
//! borrow exactly this and leave the rest of `Builder` available alongside —
//! the bound checker holds `&modules` and `&mut diagnostics` next to its
//! `TypeCtx`, and trait conformance builds one while walking `&items`. Each
//! writes the field split itself; a `fn type_ctx(&mut self)` helper cannot
//! serve them, since it borrows all of `self`. This is the same disjoint-field
//! reasoning the `Builder` struct's own doc comment spells out.

use super::*;

pub(super) struct TypeCtx<'a> {
	pub(super) types: &'a mut TypeInterner,
	pub(super) items: &'a ItemRegistry,
	pub(super) interner: &'a ast::StringInterner,
}

impl TypeCtx<'_> {
	pub(super) fn substitute_type(
		&mut self,
		ty: TypeIndex,
		type_args: &[TypeIndex],
	) -> TypeIndex {
		match self.types.resolve(ty) {
			// Types that can never contain TypeParams — return immediately.
			Type::Unit
			| Type::Bool
			| Type::Error
			| Type::Infer
			| Type::Never
			| Type::Integer
			| Type::Float
			| Type::I8
			| Type::I16
			| Type::I32
			| Type::I64
			| Type::U8
			| Type::U16
			| Type::U32
			| Type::U64
			| Type::F32
			| Type::F64
			| Type::Char
			| Type::Enum { .. }
			| Type::Namespace { .. }
			| Type::Memory { .. }
			| Type::AssociatedType { .. } => ty,
			Type::TypeParam { param_index, .. } => type_args
				.get(*param_index as usize)
				.copied()
				.filter(|&t| t != TypeIndex::ERROR)
				.unwrap_or(ty),
			Type::AssocTypeProjection {
				base,
				assoc_name,
				trait_index,
			} => {
				let (base, assoc_name, trait_index) =
					(*base, *assoc_name, *trait_index);
				let substituted = self.substitute_type(base, type_args);
				match self.types.resolve(substituted) {
					Type::TypeParam { .. }
					| Type::AssocTypeProjection { .. } => {
						if substituted == base {
							ty
						} else {
							self.types.intern(Type::AssocTypeProjection {
								trait_index,
								assoc_name,
								base: substituted,
							})
						}
					}
					// `trait_index` is already known here (it's part of the
					// projection type itself), so go straight to that one
					// impl instead of the ambiguity-scanning
					// `resolve_impl_member` — there's nothing to
					// disambiguate when the trait is already pinned down.
					_ => {
						match self.items.find_trait_impl(
							self.types,
							substituted,
							trait_index,
						) {
							Some((impl_idx, impl_type_args)) => {
								match self.items.trait_impls
									[usize::from(impl_idx)]
								.members
								.get(&assoc_name)
								{
									Some(ImplEntry::AssocType(idx)) => {
										let concrete = self
											.items
											.associated_types[usize::from(*idx)]
										.ty
										.unwrap();
										// The impl's own assoc-type value may
										// reference its own type params (e.g.
										// `impl<T> Trait for Foo<T> { type
										// Assoc = T; }`) — substitute those
										// through the args just inferred from
										// `substituted`.
										self.substitute_type(
											concrete.inner,
											&impl_type_args,
										)
									}
									_ => ty,
								}
							}
							None => {
								// `substituted` can land here either because
								// it's a genuinely concrete type that just
								// doesn't implement `trait_index` (a real,
								// permanent bound failure — the call site's
								// own bound check already reports this; don't
								// hand back the stale pre-substitution
								// projection as if it were valid), or because
								// it's still `INFER`/`ERROR` itself (type-arg
								// inference hasn't finished yet) — that's not
								// a failure, just "not resolved yet," so defer
								// the same way the TypeParam/AssocTypeProjection
								// arm above does.
								if substituted == TypeIndex::INFER
									|| substituted == TypeIndex::ERROR
								{
									ty
								} else {
									TypeIndex::ERROR
								}
							}
						}
					}
				}
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => {
				let (to, memory, ownership) = (*to, *memory, *ownership);
				let next_to = self.substitute_type(to, type_args);
				let next_memory = self.substitute_type(memory, type_args);
				if next_to == to && next_memory == memory {
					ty
				} else {
					self.types.intern(Type::Pointer {
						to: next_to,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Array {
				of,
				size,
				memory,
				ownership,
			} => {
				let (of, size, memory, ownership) =
					(*of, *size, *memory, *ownership);
				let next_of = self.substitute_type(of, type_args);
				let next_memory = self.substitute_type(memory, type_args);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.types.intern(Type::Array {
						of: next_of,
						size,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Slice {
				of,
				memory,
				ownership,
			} => {
				let (of, memory, ownership) = (*of, *memory, *ownership);
				let next_of = self.substitute_type(of, type_args);
				let next_memory = self.substitute_type(memory, type_args);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.types.intern(Type::Slice {
						of: next_of,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Tuple { elements } => {
				let mut changed = false;
				let substituted: Box<[TypeIndex]> = elements
					.clone()
					.iter()
					.copied()
					.map(|element| {
						let next = self.substitute_type(element, type_args);
						changed |= next != element;
						next
					})
					.collect();
				if changed {
					self.types.intern(Type::Tuple {
						elements: substituted,
					})
				} else {
					ty
				}
			}
			Type::Function { signature } => {
				let signature = signature.clone();
				let mut changed = false;
				let items: Box<[TypeIndex]> = signature
					.items
					.iter()
					.copied()
					.map(|item| {
						let next = self.substitute_type(item, type_args);
						changed |= next != item;
						next
					})
					.collect();
				if changed {
					self.types.intern(Type::Function {
						signature: FunctionSignature {
							items,
							params_count: signature.params_count,
						},
					})
				} else {
					ty
				}
			}
			Type::Struct {
				struct_index,
				args: struct_args,
			} => {
				if struct_args.is_empty() {
					return ty;
				}
				let mut changed = false;
				let struct_index = *struct_index;
				let substituted: Box<[TypeIndex]> = struct_args
					.clone()
					.iter()
					.copied()
					.map(|a| {
						let next = self.substitute_type(a, type_args);
						changed |= next != a;
						next
					})
					.collect();
				if changed {
					self.types.intern(Type::Struct {
						struct_index,
						args: substituted,
					})
				} else {
					ty
				}
			}
			Type::FunctionItem {
				id,
				type_args: item_args,
			} => {
				if item_args.is_empty() {
					return ty;
				}
				let mut changed = false;
				let id = *id;
				let substituted: Box<[TypeIndex]> = item_args
					.clone()
					.iter()
					.copied()
					.map(|item_arg| {
						let next = self.substitute_type(item_arg, type_args);
						changed |= next != item_arg;
						next
					})
					.collect();
				if changed {
					self.types.intern(Type::FunctionItem {
						id,
						type_args: substituted,
					})
				} else {
					ty
				}
			}
		}
	}

	/// The value `ty`'s impl of `trait_index` gives `assoc_name`, built out in
	/// full: a generic impl's `type Item = Wrapper<T>` is materialized as
	/// `Wrapper<u8>`, interning that type if it does not exist yet. `None`
	/// only when there is no such impl or no such member.
	///
	/// Interning is why this takes `&mut self` and why it cannot be used
	/// during impl *selection*, which reads what it can without building
	/// anything — see `ItemRegistry::assoc_bindings_hold`.
	pub(super) fn materialize_assoc_value(
		&mut self,
		ty: TypeIndex,
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
	) -> Option<TypeIndex> {
		let (impl_idx, impl_type_args) =
			self.items.find_trait_impl(self.types, ty, trait_index)?;
		match self.items.trait_impls[usize::from(impl_idx)]
			.members
			.get(&assoc_name)
			.copied()
		{
			Some(ImplEntry::AssocType(idx)) => {
				let raw =
					self.items.associated_types[usize::from(idx)].ty.unwrap();
				Some(self.substitute_type(raw.inner, &impl_type_args))
			}
			_ => None,
		}
	}
}
