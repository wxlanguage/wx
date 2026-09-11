//! Fully-instantiated semantic types used while building MIR.
//!
//! TIR types still contain inference sentinels, type parameters and associated
//! type projections. This module is the boundary that will resolve those
//! nodes without adding anything to TIR's type interner. A [`ConcreteType`]
//! retains nominal information until the MIR builder deliberately lowers it
//! to the physical [`super::ValueType`] representation.

use std::collections::HashMap;

use string_interner::symbol::SymbolU32;

use crate::{ast, index::index_newtype, tir};

index_newtype!(
	/// Index into the MIR builder's concrete semantic type interner.
	TypeId
);

index_newtype!(
	/// A persistent substitution environment in [`TypeEnvArena`].
	TypeEnvId
);

/// A fully-instantiated semantic type. Unlike [`tir::Type`], this cannot
/// contain inference sentinels, type parameters or associated projections.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ConcreteType {
	Unit,
	Never,
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
	Tuple {
		elements: Box<[TypeId]>,
	},
	Struct {
		struct_index: tir::StructIndex,
		args: Box<[TypeId]>,
	},
	Enum {
		enum_index: tir::EnumIndex,
	},
	Function {
		params: Box<[TypeId]>,
		result: TypeId,
	},
	FunctionItem {
		id: ast::DefId,
		type_args: Box<[TypeId]>,
	},
	Pointer {
		to: TypeId,
		memory: TypeId,
		ownership: ast::Ownership,
	},
	Array {
		of: TypeId,
		size: u32,
		memory: TypeId,
		ownership: ast::Ownership,
	},
	Slice {
		of: TypeId,
		memory: TypeId,
		ownership: ast::Ownership,
	},
	Memory {
		id: ast::DefId,
	},
}

/// Canonicalizes concrete types independently of TIR's immutable interner.
#[derive(Default)]
pub(super) struct TypeInterner {
	entries: Vec<ConcreteType>,
	lookup: HashMap<ConcreteType, TypeId>,
}

impl TypeInterner {
	pub(super) fn intern(&mut self, ty: ConcreteType) -> TypeId {
		if let Some(&id) = self.lookup.get(&ty) {
			return id;
		}
		let index = u32::try_from(self.entries.len())
			.expect("MIR concrete type interner exceeded u32 index capacity");
		let id = TypeId::new(index);
		self.entries.push(ty.clone());
		self.lookup.insert(ty, id);
		id
	}

	pub(super) fn get(&self, id: TypeId) -> &ConcreteType {
		&self.entries[usize::from(id)]
	}
}

/// One owner-scoped set of substitutions, linked to its enclosing set.
struct TypeEnv {
	owner: tir::TypeParamOwner,
	/// Offset of `args[0]` in `Type::TypeParam::param_index` space.
	/// Function-owned parameters start after any inherited parameters.
	param_offset: u32,
	args: Box<[TypeId]>,
	parent: Option<TypeEnvId>,
}

/// Persistent substitution environments built during MIR monomorphization.
/// Every arena entry is a real environment; `None` represents an empty chain.
#[derive(Default)]
pub(super) struct TypeEnvArena {
	envs: Vec<TypeEnv>,
}

impl TypeEnvArena {
	fn push(&mut self, env: TypeEnv) -> TypeEnvId {
		let index = u32::try_from(self.envs.len())
			.expect("MIR type environment arena exceeded u32 index capacity");
		let id = TypeEnvId::new(index);
		self.envs.push(env);
		id
	}

	fn resolve(
		&self,
		mut env: Option<TypeEnvId>,
		owner: tir::TypeParamOwner,
		param_index: u32,
	) -> Option<TypeId> {
		while let Some(id) = env {
			let frame = &self.envs[usize::from(id)];
			if frame.owner == owner
				&& let Some(relative) =
					param_index.checked_sub(frame.param_offset)
				&& let Some(&arg) = frame.args.get(relative as usize)
			{
				return Some(arg);
			}
			env = frame.parent;
		}
		None
	}
}

/// Owns concrete semantic types and the substitution environments used to
/// instantiate them. It only reads TIR; every newly materialized type lives in
/// this MIR-owned interner.
pub(super) struct TypeContext<'tir> {
	tir: &'tir tir::TIR,
	pub interner: TypeInterner,
	pub envs: TypeEnvArena,
}

impl<'tir> TypeContext<'tir> {
	pub(super) fn new(tir: &'tir tir::TIR) -> Self {
		Self {
			tir,
			interner: TypeInterner::default(),
			envs: TypeEnvArena::default(),
		}
	}

	#[inline]
	pub(super) fn get(&self, id: TypeId) -> &ConcreteType {
		self.interner.get(id)
	}

	/// Builds the owner-scoped environment expected by `function` from its
	/// full argument list: inherited arguments first, then the function's own.
	pub(super) fn push_function_env(
		&mut self,
		function: &tir::Function,
		type_args: &[TypeId],
	) -> Option<TypeEnvId> {
		debug_assert_eq!(type_args.len(), function.type_param_count());
		let inherited = function.inherited_type_param_count as usize;
		let mut env = None;
		if inherited != 0 {
			env = Some(self.envs.push(TypeEnv {
				owner: function.type_param_parent().expect(
					"function with inherited type parameters has no owner",
				),
				args: type_args[..inherited].into(),
				param_offset: 0,
				parent: env,
			}));
		}
		if type_args.len() != inherited {
			env = Some(self.envs.push(TypeEnv {
				param_offset: inherited as u32,
				owner: tir::TypeParamOwner::Function(function.id),
				parent: env,
				args: type_args[inherited..].into(),
			}));
		}
		env
	}

	pub(super) fn push_struct_env(
		&mut self,
		struct_: &tir::Struct,
		type_args: &[TypeId],
	) -> Option<TypeEnvId> {
		if type_args.is_empty() {
			None
		} else {
			Some(self.envs.push(TypeEnv {
				owner: tir::TypeParamOwner::Struct(struct_.id),
				args: type_args.into(),
				param_offset: 0,
				parent: None,
			}))
		}
	}

	pub(super) fn instantiate_type(
		&mut self,
		type_index: tir::TypeIndex,
		env: Option<TypeEnvId>,
	) -> TypeId {
		let concrete = match self.tir.types.resolve(type_index) {
			tir::Type::Error
			| tir::Type::Infer
			| tir::Type::Integer
			| tir::Type::Float
			| tir::Type::Namespace { .. }
			| tir::Type::AssociatedType { .. } => unreachable!(
				"invalid or unresolved TIR type reached MIR instantiation"
			),
			tir::Type::Unit => ConcreteType::Unit,
			tir::Type::Never => ConcreteType::Never,
			tir::Type::U8 => ConcreteType::U8,
			tir::Type::I8 => ConcreteType::I8,
			tir::Type::U16 => ConcreteType::U16,
			tir::Type::I16 => ConcreteType::I16,
			tir::Type::U32 => ConcreteType::U32,
			tir::Type::I32 => ConcreteType::I32,
			tir::Type::U64 => ConcreteType::U64,
			tir::Type::I64 => ConcreteType::I64,
			tir::Type::F32 => ConcreteType::F32,
			tir::Type::F64 => ConcreteType::F64,
			tir::Type::Bool => ConcreteType::Bool,
			tir::Type::Char => ConcreteType::Char,
			tir::Type::TypeParam { owner, param_index } => {
				return self
					.envs
					.resolve(env, *owner, *param_index)
					.unwrap_or_else(|| {
						panic!(
							"missing MIR substitution for type parameter index \
							 {param_index}"
						)
					});
			}
			tir::Type::Tuple { elements } => ConcreteType::Tuple {
				elements: elements
					.iter()
					.copied()
					.map(|element| self.instantiate_type(element, env))
					.collect(),
			},
			tir::Type::Struct { struct_index, args } => ConcreteType::Struct {
				struct_index: *struct_index,
				args: args
					.iter()
					.copied()
					.map(|arg| self.instantiate_type(arg, env))
					.collect(),
			},
			tir::Type::Enum { enum_index } => ConcreteType::Enum {
				enum_index: *enum_index,
			},
			tir::Type::Function { signature } => ConcreteType::Function {
				params: signature
					.params()
					.iter()
					.copied()
					.map(|param| self.instantiate_type(param, env))
					.collect(),
				result: self.instantiate_type(signature.result(), env),
			},
			tir::Type::FunctionItem { id, type_args } => {
				ConcreteType::FunctionItem {
					id: *id,
					type_args: type_args
						.iter()
						.copied()
						.map(|arg| self.instantiate_type(arg, env))
						.collect(),
				}
			}
			tir::Type::Pointer {
				to,
				memory,
				ownership,
			} => ConcreteType::Pointer {
				to: self.instantiate_type(*to, env),
				memory: self.instantiate_type(*memory, env),
				ownership: *ownership,
			},
			tir::Type::Array {
				of,
				size,
				memory,
				ownership,
			} => ConcreteType::Array {
				of: self.instantiate_type(*of, env),
				size: *size,
				memory: self.instantiate_type(*memory, env),
				ownership: *ownership,
			},
			tir::Type::Slice {
				of,
				memory,
				ownership,
			} => ConcreteType::Slice {
				of: self.instantiate_type(*of, env),
				memory: self.instantiate_type(*memory, env),
				ownership: *ownership,
			},
			tir::Type::Memory { id, .. } => ConcreteType::Memory { id: *id },
			tir::Type::AssocTypeProjection {
				trait_index,
				assoc_name,
				base,
			} => {
				return self.instantiate_projection(
					*base,
					*trait_index,
					*assoc_name,
					env,
				);
			}
		};
		self.interner.intern(concrete)
	}

	pub(super) fn instantiate_types(
		&mut self,
		types: &[tir::TypeIndex],
		env: Option<TypeEnvId>,
	) -> Box<[TypeId]> {
		types
			.iter()
			.copied()
			.map(|ty| self.instantiate_type(ty, env))
			.collect()
	}

	fn instantiate_projection(
		&mut self,
		base: tir::TypeIndex,
		trait_index: tir::TraitIndex,
		assoc_name: SymbolU32,
		env: Option<TypeEnvId>,
	) -> TypeId {
		let base = self.instantiate_type(base, env);
		// TIR rejects cyclic associated-type definitions before MIR is built.
		// Instantiation may therefore recurse through projections directly;
		// reaching a cycle here would violate that TIR validation contract,
		// rather than represent a case MIR should recover from locally.
		let (impl_index, impl_args) =
			self.find_trait_impl(base, trait_index).expect(
				"no trait impl found for associated-type projection in MIR",
			);
		let member = self
			.trait_member(impl_index, assoc_name)
			.expect("validated trait impl is missing an associated type");
		let (assoc_index, owner, args) = match member {
			TraitMember::Impl(tir::ImplEntry::AssocType(index)) => {
				(index, tir::TypeParamOwner::TraitImpl(impl_index), impl_args)
			}
			TraitMember::Default(tir::ImplEntry::AssocType(index)) => (
				index,
				tir::TypeParamOwner::Trait(trait_index),
				Box::new([base]) as Box<[TypeId]>,
			),
			_ => {
				unreachable!(
					"trait impl member for associated-type projection is not a type"
				)
			}
		};
		let raw = self.tir.items.associated_types[usize::from(assoc_index)]
			.ty
			.expect("associated type selected by MIR has no value")
			.inner;
		let projection_env = self.envs.push(TypeEnv {
			owner,
			param_offset: 0,
			args,
			parent: env,
		});
		self.instantiate_type(raw, Some(projection_env))
	}

	/// Selects an impl-provided member when present, otherwise the trait's
	/// default. TIR has finished resolving and validating every member before
	/// MIR is built, so this is a read-only selection rather than another
	/// signature-resolution or diagnostic phase.
	pub(super) fn trait_member(
		&self,
		impl_index: tir::TraitImplIndex,
		name: SymbolU32,
	) -> Option<TraitMember> {
		let imp = &self.tir.items.trait_impls[usize::from(impl_index)];
		let member = self.tir.items.traits[usize::from(imp.trait_index)]
			.members
			.get(&name)?;
		let default = member.entry(&self.tir.items);
		if let Some(&entry) = imp.members.get(&name)
			&& entry != default
		{
			return Some(TraitMember::Impl(entry));
		}
		self.entry_has_default(default)
			.then_some(TraitMember::Default(default))
	}

	fn entry_has_default(&self, entry: tir::ImplEntry) -> bool {
		match entry {
			tir::ImplEntry::Method(index)
			| tir::ImplEntry::AssocFunction(index) => {
				self.tir.items.functions[usize::from(index)].body.is_some()
			}
			tir::ImplEntry::AssocConstant(index) => {
				self.tir.items.constants[usize::from(index)].value.is_some()
			}
			// Trait-level associated-type defaults are not supported yet.
			tir::ImplEntry::AssocType(_) => false,
		}
	}

	/// Finds the unique impl registered for `receiver`'s type constructor and
	/// recovers its generic arguments from the concrete MIR type.
	///
	/// TIR has already checked that the concrete trait use is valid, including
	/// all bounds on the impl's type parameters. MIR only repeats the structural
	/// walk needed to express those parameters as [`TypeId`]s; it does not run
	/// type checking or diagnostics again.
	pub(super) fn find_trait_impl(
		&self,
		receiver: TypeId,
		trait_index: tir::TraitIndex,
	) -> Option<(tir::TraitImplIndex, Box<[TypeId]>)> {
		let impl_index = self.find_trait_impl_index(receiver, trait_index)?;
		let args = self.infer_impl_args(impl_index, receiver)?;
		Some((impl_index, args))
	}

	fn find_trait_impl_index(
		&self,
		receiver: TypeId,
		trait_index: tir::TraitIndex,
	) -> Option<tir::TraitImplIndex> {
		let target = self.impl_target(receiver)?;
		self.tir
			.items
			.trait_impl_dispatch
			.get(&target)?
			.iter()
			.find_map(|&(candidate, index)| {
				(candidate == trait_index).then_some(index)
			})
	}

	fn infer_impl_args(
		&self,
		impl_index: tir::TraitImplIndex,
		receiver: TypeId,
	) -> Option<Box<[TypeId]>> {
		let imp = &self.tir.items.trait_impls[usize::from(impl_index)];
		let mut args = vec![None; imp.type_params.len()];
		self.match_impl_target(
			imp.target.inner,
			receiver,
			impl_index,
			&mut args,
		)
		.then(|| {
			args.into_iter()
				.map(|arg| {
					arg.expect(
						"validated trait impl target left a type parameter uninferred",
					)
				})
				.collect()
		})
	}

	fn impl_target(&self, ty: TypeId) -> Option<tir::ImplTarget> {
		Some(match self.interner.get(ty) {
			ConcreteType::U8 => tir::ImplTarget::U8,
			ConcreteType::I8 => tir::ImplTarget::I8,
			ConcreteType::U16 => tir::ImplTarget::U16,
			ConcreteType::I16 => tir::ImplTarget::I16,
			ConcreteType::U32 => tir::ImplTarget::U32,
			ConcreteType::I32 => tir::ImplTarget::I32,
			ConcreteType::U64 => tir::ImplTarget::U64,
			ConcreteType::I64 => tir::ImplTarget::I64,
			ConcreteType::F32 => tir::ImplTarget::F32,
			ConcreteType::F64 => tir::ImplTarget::F64,
			ConcreteType::Bool => tir::ImplTarget::Bool,
			ConcreteType::Char => tir::ImplTarget::Char,
			ConcreteType::Slice { .. } => tir::ImplTarget::Slice,
			ConcreteType::Array { .. } => tir::ImplTarget::Array,
			ConcreteType::Struct { struct_index, .. } => {
				tir::ImplTarget::Struct(*struct_index)
			}
			ConcreteType::Enum { enum_index } => {
				tir::ImplTarget::Enum(*enum_index)
			}
			ConcreteType::Memory { id } => tir::ImplTarget::Memory(*id),
			ConcreteType::Unit
			| ConcreteType::Never
			| ConcreteType::Tuple { .. }
			| ConcreteType::Function { .. }
			| ConcreteType::FunctionItem { .. }
			| ConcreteType::Pointer { .. } => return None,
		})
	}

	fn match_impl_target(
		&self,
		pattern: tir::TypeIndex,
		actual: TypeId,
		impl_index: tir::TraitImplIndex,
		args: &mut [Option<TypeId>],
	) -> bool {
		let pattern = self.tir.types.resolve(pattern);
		if let tir::Type::TypeParam {
			owner: tir::TypeParamOwner::TraitImpl(owner),
			param_index,
		} = pattern
		{
			if *owner != impl_index {
				return false;
			}
			let slot = &mut args[*param_index as usize];
			return match *slot {
				Some(existing) => existing == actual,
				None => {
					*slot = Some(actual);
					true
				}
			};
		}

		match (pattern, self.interner.get(actual)) {
			(tir::Type::Unit, ConcreteType::Unit)
			| (tir::Type::Never, ConcreteType::Never)
			| (tir::Type::U8, ConcreteType::U8)
			| (tir::Type::I8, ConcreteType::I8)
			| (tir::Type::U16, ConcreteType::U16)
			| (tir::Type::I16, ConcreteType::I16)
			| (tir::Type::U32, ConcreteType::U32)
			| (tir::Type::I32, ConcreteType::I32)
			| (tir::Type::U64, ConcreteType::U64)
			| (tir::Type::I64, ConcreteType::I64)
			| (tir::Type::F32, ConcreteType::F32)
			| (tir::Type::F64, ConcreteType::F64)
			| (tir::Type::Bool, ConcreteType::Bool)
			| (tir::Type::Char, ConcreteType::Char) => true,
			(
				tir::Type::Struct {
					struct_index: expected,
					args: pattern_args,
				},
				ConcreteType::Struct {
					struct_index: found,
					args: actual_args,
				},
			) if expected == found
				&& pattern_args.len() == actual_args.len() =>
			{
				pattern_args.iter().zip(actual_args).all(|(&p, &a)| {
					self.match_impl_target(p, a, impl_index, args)
				})
			}
			(
				tir::Type::Tuple {
					elements: pattern_elements,
				},
				ConcreteType::Tuple {
					elements: actual_elements,
				},
			) if pattern_elements.len() == actual_elements.len() => pattern_elements
				.iter()
				.zip(actual_elements)
				.all(|(&p, &a)| self.match_impl_target(p, a, impl_index, args)),
			(
				tir::Type::Function { signature },
				ConcreteType::Function { params, result },
			) if signature.params().len() == params.len() => {
				signature.params().iter().zip(params).all(
					|(&pattern, &actual)| {
						self.match_impl_target(
							pattern, actual, impl_index, args,
						)
					},
				) && self.match_impl_target(
					signature.result(),
					*result,
					impl_index,
					args,
				)
			}
			(
				tir::Type::FunctionItem {
					id: expected,
					type_args: pattern_args,
				},
				ConcreteType::FunctionItem {
					id: found,
					type_args: actual_args,
				},
			) if expected == found
				&& pattern_args.len() == actual_args.len() =>
			{
				pattern_args.iter().zip(actual_args).all(|(&p, &a)| {
					self.match_impl_target(p, a, impl_index, args)
				})
			}
			(
				tir::Type::Enum {
					enum_index: expected,
				},
				ConcreteType::Enum { enum_index: found },
			) => expected == found,
			(
				tir::Type::Memory { id: expected, .. },
				ConcreteType::Memory { id: found },
			) => expected == found,
			(
				tir::Type::Pointer {
					to: pattern_to,
					memory: pattern_memory,
					ownership: expected_ownership,
				},
				ConcreteType::Pointer {
					to: actual_to,
					memory: actual_memory,
					ownership: found_ownership,
				},
			) => {
				expected_ownership == found_ownership
					&& self.match_impl_target(
						*pattern_to,
						*actual_to,
						impl_index,
						args,
					) && self.match_impl_target(
					*pattern_memory,
					*actual_memory,
					impl_index,
					args,
				)
			}
			(
				tir::Type::Array {
					of: pattern_of,
					size: expected_size,
					memory: pattern_memory,
					ownership: expected_ownership,
				},
				ConcreteType::Array {
					of: actual_of,
					size: found_size,
					memory: actual_memory,
					ownership: found_ownership,
				},
			) => {
				expected_size == found_size
					&& expected_ownership == found_ownership
					&& self.match_impl_target(
						*pattern_of,
						*actual_of,
						impl_index,
						args,
					) && self.match_impl_target(
					*pattern_memory,
					*actual_memory,
					impl_index,
					args,
				)
			}
			(
				tir::Type::Slice {
					of: pattern_of,
					memory: pattern_memory,
					ownership: expected_ownership,
				},
				ConcreteType::Slice {
					of: actual_of,
					memory: actual_memory,
					ownership: found_ownership,
				},
			) => {
				expected_ownership == found_ownership
					&& self.match_impl_target(
						*pattern_of,
						*actual_of,
						impl_index,
						args,
					) && self.match_impl_target(
					*pattern_memory,
					*actual_memory,
					impl_index,
					args,
				)
			}
			_ => false,
		}
	}
}

#[derive(Clone, Copy)]
pub(super) enum TraitMember {
	Impl(tir::ImplEntry),
	Default(tir::ImplEntry),
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use super::*;
	use crate::vfs;

	#[test]
	fn interner_canonicalizes_equal_types() {
		let mut types = TypeInterner::default();
		let first = types.intern(ConcreteType::I32);
		let second = types.intern(ConcreteType::I32);
		assert_eq!(first, second);
		assert_eq!(types.get(first), &ConcreteType::I32);
	}

	#[test]
	fn environments_resolve_exact_owner_through_parent_chain() {
		let mut types = TypeInterner::default();
		let i32_ty = types.intern(ConcreteType::I32);
		let bool_ty = types.intern(ConcreteType::Bool);
		let mut envs = TypeEnvArena::default();

		let outer_owner = tir::TypeParamOwner::Trait(tir::TraitIndex::new(1));
		let inner_owner = tir::TypeParamOwner::Trait(tir::TraitIndex::new(2));
		let outer = envs.push(TypeEnv {
			owner: outer_owner,
			param_offset: 0,
			args: Box::new([i32_ty]),
			parent: None,
		});
		let inner = envs.push(TypeEnv {
			owner: inner_owner,
			param_offset: 0,
			args: Box::new([bool_ty]),
			parent: Some(outer),
		});

		assert_eq!(envs.resolve(Some(inner), inner_owner, 0), Some(bool_ty));
		assert_eq!(envs.resolve(Some(inner), outer_owner, 0), Some(i32_ty));
		assert_eq!(envs.resolve(Some(inner), outer_owner, 1), None);
		assert_eq!(
			envs.resolve(
				Some(inner),
				tir::TypeParamOwner::Trait(tir::TraitIndex::new(3)),
				0,
			),
			None
		);
	}

	#[test]
	fn environment_supports_params_after_an_inherited_prefix() {
		let mut types = TypeInterner::default();
		let bool_ty = types.intern(ConcreteType::Bool);
		let mut envs = TypeEnvArena::default();
		let owner = tir::TypeParamOwner::Trait(tir::TraitIndex::new(1));
		let env = envs.push(TypeEnv {
			owner,
			param_offset: 2,
			args: Box::new([bool_ty]),
			parent: None,
		});

		assert_eq!(envs.resolve(Some(env), owner, 1), None);
		assert_eq!(envs.resolve(Some(env), owner, 2), Some(bool_ty));
	}

	#[test]
	fn instantiation_resolves_a_composite_associated_type() {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					r#"
						trait Container { type Item; }
						struct Wrapper<T> { value: T }
						impl<T> Container for Wrapper<T> { type Item = (T,); }
						fn project<U: Container>(value: U) -> U::Item { unreachable }
						fn concrete(value: Wrapper<i32>) {}
						export {}
					"#
					.to_string(),
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id);
		let tir = tir::TIR::build(&mut graph);
		assert!(
			!tir.diagnostics.iter().any(|diagnostic| diagnostic.severity
				== codespan_reporting::diagnostic::Severity::Error),
			"unexpected TIR errors"
		);

		let function = |name: &str| {
			tir.items
				.functions
				.iter()
				.find(|function| {
					graph.interner.resolve(function.name.inner) == Some(name)
				})
				.unwrap()
		};
		let project = function("project");
		let concrete = function("concrete");
		let concrete_wrapper = concrete.params[0].ty.inner;
		let projection = project.result.unwrap().inner;

		let mut types = TypeContext::new(&tir);
		let wrapper = types.instantiate_type(concrete_wrapper, None);
		let env = types.envs.push(TypeEnv {
			owner: tir::TypeParamOwner::Function(project.id),
			param_offset: 0,
			args: Box::new([wrapper]),
			parent: None,
		});
		let item = types.instantiate_type(projection, Some(env));
		let ConcreteType::Tuple { elements } = types.get(item) else {
			panic!("associated type should instantiate to a tuple")
		};
		assert_eq!(elements.len(), 1);
		assert_eq!(types.get(elements[0]), &ConcreteType::I32);
	}

	#[test]
	fn impl_argument_inference_descends_into_function_types() {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					r#"
						trait Callable { type Arg; }
						struct Wrapper<T> { value: T }
						impl<T> Callable for Wrapper<fn(T) -> T> { type Arg = T; }
						fn project<U: Callable>(value: U) -> U::Arg { unreachable }
						fn concrete(value: Wrapper<fn(i32) -> i32>) {}
						export {}
					"#
					.to_string(),
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id);
		let tir = tir::TIR::build(&mut graph);
		assert!(
			!tir.diagnostics.iter().any(|diagnostic| diagnostic.severity
				== codespan_reporting::diagnostic::Severity::Error),
			"unexpected TIR errors"
		);

		let function = |name: &str| {
			tir.items
				.functions
				.iter()
				.find(|function| {
					graph.interner.resolve(function.name.inner) == Some(name)
				})
				.unwrap()
		};
		let project = function("project");
		let concrete = function("concrete");
		let mut types = TypeContext::new(&tir);
		let wrapper = types.instantiate_type(concrete.params[0].ty.inner, None);
		let env = types.envs.push(TypeEnv {
			owner: tir::TypeParamOwner::Function(project.id),
			param_offset: 0,
			args: Box::new([wrapper]),
			parent: None,
		});

		let arg =
			types.instantiate_type(project.result.unwrap().inner, Some(env));
		assert_eq!(types.get(arg), &ConcreteType::I32);
	}

	#[test]
	fn trait_member_prefers_impl_and_falls_back_to_defaults() {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					r#"
						trait Values {
							fn default_value() -> i32 { 1 }
							fn replaced_value() -> i32 { 2 }
							const DEFAULT: i32 = 3;
							const REPLACED: i32 = 4;
						}
						struct Subject {}
						impl Values for Subject {
							fn replaced_value() -> i32 { 5 }
							const REPLACED: i32 = 6;
						}
						export {}
					"#
					.to_string(),
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id);
		let tir = tir::TIR::build(&mut graph);
		assert!(
			!tir.diagnostics.iter().any(|diagnostic| diagnostic.severity
				== codespan_reporting::diagnostic::Severity::Error),
			"unexpected TIR errors"
		);

		let values = tir
			.items
			.traits
			.iter()
			.position(|item| {
				graph.interner.resolve(item.name.inner) == Some("Values")
			})
			.map(|index| tir::TraitIndex::new(index as u32))
			.unwrap();
		let impl_index = tir
			.items
			.trait_impls
			.iter()
			.position(|imp| imp.trait_index == values)
			.map(|index| tir::TraitImplIndex::new(index as u32))
			.unwrap();
		let types = TypeContext::new(&tir);

		assert!(matches!(
			types.trait_member(
				impl_index,
				graph.interner.get("default_value").unwrap()
			),
			Some(TraitMember::Default(tir::ImplEntry::AssocFunction(_)))
		));
		assert!(matches!(
			types.trait_member(
				impl_index,
				graph.interner.get("replaced_value").unwrap()
			),
			Some(TraitMember::Impl(tir::ImplEntry::AssocFunction(_)))
		));
		assert!(matches!(
			types.trait_member(
				impl_index,
				graph.interner.get("DEFAULT").unwrap()
			),
			Some(TraitMember::Default(tir::ImplEntry::AssocConstant(_)))
		));
		assert!(matches!(
			types.trait_member(
				impl_index,
				graph.interner.get("REPLACED").unwrap()
			),
			Some(TraitMember::Impl(tir::ImplEntry::AssocConstant(_)))
		));
	}
}
