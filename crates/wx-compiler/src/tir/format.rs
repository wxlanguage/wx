//! Renders resolved types and declared bounds into source-like text.
//! [`BoundFormatter`] reads source occurrences from the bound arena and
//! delegates equality types to [`TypeFormatter`], sharing one output buffer.
//!
//! A separate borrowing entity (the legacy `TypeFormatter<'a>`'s own
//! shape), not methods directly on `TypeContext`: formatting is a
//! read-only concern with its own vocabulary (`write_type`, `write_bounds`,
//! ...), and keeping it off `TypeContext` means a call site can hold
//! one to build a message while the surrounding code is about to mutate
//! `self` right after — the same reason the legacy one existed as its own
//! type rather than living on the (bigger, `&mut`-heavy) `Builder`.
//!
//! Borrows `types`/`defs`/`strings` plus `type_envs` for generic parameter
//! names. Struct, enum, function, trait, and memory names come directly
//! from their definitions, without forcing signature resolution.
//! The formatter currently wraps `TypeContext`'s pieces.

use std::fmt::Write as _;

use crate::ast::{Ownership, StringInterner};

use super::bounds::{BindingRequirement, BoundArena, BoundId};
use super::defs::{DefinitionRegistry, MemberOwner};
use super::signatures::TypeContext;
use super::types::{Type, TypeEnvArena, TypeIndex, TypeInterner};

pub(super) struct TypeFormatter<'a> {
	pub(super) types: &'a TypeInterner,
	pub(super) defs: &'a DefinitionRegistry,
	pub(super) strings: &'a StringInterner,
	pub(super) type_envs: &'a TypeEnvArena,
}

/// Formats declared source bounds, preserving their order and bindings.
/// Implied bounds are merged requirements and cannot be rendered by reading
/// only their originating source occurrences.
pub(super) struct BoundFormatter<'a> {
	type_formatter: TypeFormatter<'a>,
	bounds: &'a BoundArena,
}

impl TypeContext<'_, '_, '_> {
	pub(super) fn type_formatter(&self) -> TypeFormatter<'_> {
		TypeFormatter {
			types: &self.types,
			defs: self.defs,
			strings: self.strings,
			type_envs: &self.type_envs,
		}
	}

	pub(super) fn bound_formatter(&self) -> BoundFormatter<'_> {
		BoundFormatter {
			type_formatter: self.type_formatter(),
			bounds: &self.bounds,
		}
	}
}

impl BoundFormatter<'_> {
	pub(super) fn display_bound(&self, bound: BoundId) -> String {
		let mut buffer = String::new();
		self.write_bound(&mut buffer, bound);
		buffer
	}

	pub(super) fn display_bounds(&self, bounds: &[BoundId]) -> String {
		let mut buffer = String::new();
		self.write_bounds(&mut buffer, bounds);
		buffer
	}

	fn write_bounds(&self, f: &mut String, bounds: &[BoundId]) {
		for (i, bound) in bounds.iter().copied().enumerate() {
			if i > 0 {
				f.push_str(" + ");
			}
			self.write_bound(f, bound);
		}
	}

	fn write_bound(&self, f: &mut String, bound: BoundId) {
		let bound = self.bounds.get(bound);
		let symbol = self.type_formatter.defs.traits
			[usize::from(bound.trait_index)]
		.name
		.inner;
		f.push_str(self.type_formatter.strings.resolve(symbol).unwrap());
		if bound.bindings.is_empty() {
			return;
		}
		f.push_str(" where { ");
		for (i, binding) in bound.bindings.iter().enumerate() {
			if i > 0 {
				f.push_str(", ");
			}
			let symbol = self.type_formatter.defs.assoc_types
				[usize::from(binding.target.assoc_type_index)]
			.name
			.inner;
			f.push_str(self.type_formatter.strings.resolve(symbol).unwrap());
			match &binding.kind {
				BindingRequirement::Equals(ty) => {
					f.push_str(" = ");
					self.type_formatter.write_type(f, ty.inner);
				}
				BindingRequirement::Bound(bounds) => {
					f.push_str(": ");
					self.write_bounds(f, bounds);
				}
			}
		}
		f.push_str(" }");
	}
}

impl TypeFormatter<'_> {
	pub(super) fn display_type(&self, ty: TypeIndex) -> String {
		let mut buffer = String::new();
		self.write_type(&mut buffer, ty);
		buffer
	}

	fn write_type(&self, f: &mut String, ty: TypeIndex) {
		match self.types.resolve(ty) {
			Type::Error => f.push_str("{unknown}"),
			Type::Infer => f.push('_'),
			Type::Never => f.push('!'),
			Type::Integer => f.push_str("{integer}"),
			Type::Float => f.push_str("{float}"),
			Type::String => f.push_str("{string}"),
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
				for (i, element) in
					self.types.list(*elements).iter().copied().enumerate()
				{
					if i > 0 {
						f.push_str(", ");
					}
					self.write_type(f, element);
				}
				if elements.len() == 1 {
					f.push(',');
				}
				f.push(')');
			}
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let symbol =
					self.defs.structs[usize::from(*struct_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
				self.write_type_args(f, self.types.list(*type_args));
			}
			Type::Enum { enum_index } => {
				let symbol =
					self.defs.enums[usize::from(*enum_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			Type::Memory { memory_index, .. } => {
				let symbol =
					self.defs.memories[usize::from(*memory_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			Type::Global { global_index } => {
				let symbol =
					self.defs.globals[usize::from(*global_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
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
			Type::FunctionRef { param, result } => {
				let (param, result) = (*param, *result);
				f.push_str("func(");
				// A parameter list is written back as one; a one-element
				// tuple is not a list, so it keeps its own parentheses.
				match self.types.resolve(param) {
					Type::Tuple { elements } if elements.len() != 1 => {
						for (i, element) in self
							.types
							.list(*elements)
							.iter()
							.copied()
							.enumerate()
						{
							if i > 0 {
								f.push_str(", ");
							}
							self.write_type(f, element);
						}
					}
					_ => self.write_type(f, param),
				}
				f.push_str(") -> ");
				self.write_type(f, result);
			}
			Type::Function {
				func_index: function_index,
				type_args,
			} => {
				let function =
					&self.defs.functions[usize::from(*function_index)];
				let mut type_args = self.types.list(*type_args);
				// A trait's declaration takes `Self` first; it is written as
				// the receiver, `<Self as Trait>::f<own>`, always qualified
				// for the same reason a projection is.
				if let MemberOwner::Trait(trait_index) = function.owner {
					let (&receiver, own) = type_args
						.split_first()
						.expect("a trait's function takes `Self` first");
					f.push('<');
					self.write_type(f, receiver);
					f.push_str(" as ");
					let symbol =
						self.defs.traits[usize::from(trait_index)].name.inner;
					f.push_str(self.strings.resolve(symbol).unwrap());
					f.push_str(">::");
					type_args = own;
				}
				f.push_str(self.strings.resolve(function.name.inner).unwrap());
				self.write_type_args(f, type_args);
			}
			Type::TypeParam {
				env, param_index, ..
			} => {
				let symbol = self.type_envs.param_names(*env)
					[*param_index as usize]
					.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			// Always qualified (`<Base as Trait>::name`), never the shorter
			// `base::name` a formatter with ambiguity detection could use
			// when only one of `base`'s bounds declares `name` — that check
			// (walking every bound trait `base` carries, same as the legacy
			// `assoc_type_bound_is_ambiguous`) has no second caller yet, so
			// it isn't built. Always-qualified is longer but never wrong.
			Type::AssocTypeProjection {
				trait_index,
				assoc_type_index,
				base,
			} => {
				f.push('<');
				self.write_type(f, *base);
				f.push_str(" as ");
				let symbol =
					self.defs.traits[usize::from(*trait_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
				f.push_str(">::");
				let assoc_symbol = self.defs.assoc_types
					[usize::from(*assoc_type_index)]
				.name
				.inner;
				f.push_str(self.strings.resolve(assoc_symbol).unwrap());
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
}

fn ownership_sigil(ownership: Ownership) -> char {
	match ownership {
		Ownership::Exclusive => '*',
		Ownership::Shared => '&',
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

	use super::*;
	use crate::testing::DiagnosticView;
	use crate::tir::defs::{
		AssocTypeIdx, BindingKey, BindingTarget, DefKind, FunctionIdx,
		MemberKind, Namespace, Tier, TraitIdx,
	};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::resolutions::NameResolutions;
	use crate::tir::signatures::{FunctionSignature, ParamBounds, QueryInfo};
	use crate::tir::types::TypeEnvIdx;
	use crate::vfs;

	struct TestCase {
		graph: vfs::CompilationUnit,
		defs: DefinitionRegistry,
		types: TypeInterner,
		type_envs: TypeEnvArena,
		bounds: BoundArena,
		param_bounds: Vec<Box<[ParamBounds]>>,
		functions: Vec<FunctionSignature>,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			let root = builder
				.load_binary(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)])),
				)
				.unwrap();
			builder.set_stdlib(root);
			let mut graph = builder.build(root);
			DiagnosticView::new(
				"parse",
				&graph.collect_parser_diagnostics(),
				&graph.files,
			)
			.assert_no_errors();
			DiagnosticView::new(
				"link",
				&graph.collect_linker_diagnostics(),
				&graph.files,
			)
			.assert_no_errors();

			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				&mut resolutions,
				graph.stdlib_package,
				graph.root_package,
			);
			DiagnosticView::new("prescan", &diagnostics, &graph.files)
				.assert_none();

			let dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				&graph.strings,
				&defs,
				&ast_nodes,
			);
			let mut signatures = TypeContext::new(
				&mut diagnostics,
				&mut resolutions,
				&mut graph.strings,
				&graph.files,
				&defs,
				&ast_nodes,
				&dispatch,
			);
			for entry in &ast_nodes {
				let _ = signatures.ensure_signature(QueryInfo {
					def_id: entry.node.def_id(),
					requested_at: None,
				});
			}
			DiagnosticView::new(
				"signature",
				signatures.diagnostics,
				&graph.files,
			)
			.assert_none();

			Self {
				types: signatures.types,
				type_envs: signatures.type_envs,
				bounds: signatures.bounds,
				param_bounds: signatures.param_bounds,
				functions: signatures.functions,
				graph,
				defs,
			}
		}

		fn definition(&self, tier: Tier, name: &str) -> DefKind {
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("expected a fixture name");
			let root = Namespace::Package(self.defs.root_package);
			let BindingTarget::Accessible(key) =
				self.defs.namespaces.symbols(root).bindings
					[&BindingKey::new(tier, symbol)]
					.target
			else {
				panic!("expected `{name}` to be accessible");
			};
			key.symbol_kind(&self.defs)
		}

		fn function(&self, name: &str) -> FunctionIdx {
			let DefKind::Function(index) = self.definition(Tier::Value, name)
			else {
				panic!("expected `{name}` to be a function");
			};
			index
		}

		fn parameter(&self, function: &str, name: &str) -> (TypeEnvIdx, usize) {
			let env = self.functions[usize::from(self.function(function))]
				.type_params;
			let index = self
				.type_envs
				.param_names(env)
				.iter()
				.position(|param| {
					self.graph.strings.resolve(param.inner) == Some(name)
				})
				.unwrap_or_else(|| {
					panic!(
						"expected `{function}` to have a type parameter `{name}`"
					)
				});
			(env, index)
		}

		fn type_formatter(&self) -> TypeFormatter<'_> {
			TypeFormatter {
				types: &self.types,
				defs: &self.defs,
				strings: &self.graph.strings,
				type_envs: &self.type_envs,
			}
		}

		fn type_param(&self, function: &str, name: &str) -> TypeIndex {
			let (env, index) = self.parameter(function, name);
			self.type_envs.param_types(env)[index]
		}

		fn declared_bounds(&self, function: &str, param: &str) -> &[BoundId] {
			let (env, index) = self.parameter(function, param);
			&self.param_bounds[usize::from(env)][index].declared_bounds
		}

		/// `name` is looked up directly against the trait's own member
		/// bindings, same reasoning as `signatures::tests::TestCase`'s own
		/// `assoc_type_signature` — `Trait::Assoc` isn't a resolvable path
		/// yet.
		fn assoc_type_index(
			&self,
			trait_index: TraitIdx,
			name: &str,
		) -> AssocTypeIdx {
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("already interned from source");
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			let &member_index = trait_def
				.bindings
				.get(&BindingKey::ty(symbol))
				.unwrap_or_else(|| {
					panic!(
						"expected the trait to have an associated type `{name}`"
					)
				});
			let MemberKind::AssociatedType(index) =
				trait_def.members[usize::from(member_index)].kind
			else {
				panic!("expected `{name}` to be an associated type");
			};
			index
		}

		fn bound_formatter(&self) -> BoundFormatter<'_> {
			BoundFormatter {
				type_formatter: self.type_formatter(),
				bounds: &self.bounds,
			}
		}
	}

	#[test]
	fn function_types_format_nested_tuples_and_recovery_placeholders() {
		let mut case = TestCase::new("");
		let tuple =
			case.types.intern_tuple(&[TypeIndex::I32, TypeIndex::ERROR]);
		let param = case.types.intern_tuple(&[tuple, TypeIndex::INFER]);
		let function = case.types.intern(Type::FunctionRef {
			param,
			result: TypeIndex::NEVER,
		});
		assert_eq!(
			case.type_formatter().display_type(function),
			"func((i32, {unknown}), _) -> !"
		);
	}

	#[test]
	fn memory_qualified_types_preserve_ownership_and_shape() {
		let mut case = TestCase::new(
			"pub trait Call { type Args; type Result; } pub trait Function: Call {} func allocate<M>() {}",
		);
		let memory = case.type_param("allocate", "M");
		let slice = case.types.intern(Type::Slice {
			of: TypeIndex::I32,
			memory,
			ownership: Ownership::Shared,
		});
		let pointer = case.types.intern(Type::Pointer {
			to: slice,
			memory,
			ownership: Ownership::Exclusive,
		});
		let array = case.types.intern(Type::Array {
			of: TypeIndex::I32,
			size: 4,
			memory,
			ownership: Ownership::Exclusive,
		});
		let formatter = case.type_formatter();
		assert_eq!(formatter.display_type(pointer), "M::*M::&[i32]");
		assert_eq!(formatter.display_type(array), "M::*[i32; 4]");
	}

	#[test]
	fn named_functions_and_associated_types_keep_names_and_qualification() {
		let mut case = TestCase::new(indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Iterable { type Item; }
			func iterate<T: Iterable>() {}
		"});
		let param = case.type_param("iterate", "T");
		let DefKind::Trait(trait_index) =
			case.definition(Tier::Type, "Iterable")
		else {
			panic!("expected Iterable to be a trait");
		};
		let assoc_type_index = case.assoc_type_index(trait_index, "Item");
		let projection = case.types.intern(Type::AssocTypeProjection {
			trait_index,
			assoc_type_index,
			base: param,
		});
		let function = case
			.types
			.intern_function(case.function("iterate"), &[param]);
		let formatter = case.type_formatter();
		assert_eq!(formatter.display_type(function), "iterate<T>");
		assert_eq!(formatter.display_type(projection), "<T as Iterable>::Item");
	}

	#[test]
	fn bound_lists_preserve_written_order_without_expanding_supertraits() {
		let case = TestCase::new(indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Base {}
			trait A: Base {}
			trait B {}
			func subject<T, U: A, V: B + A + B>() {}
		"});
		let formatter = case.bound_formatter();
		for (param, expected) in [("T", ""), ("U", "A"), ("V", "B + A + B")] {
			assert_eq!(
				formatter
					.display_bounds(case.declared_bounds("subject", param)),
				expected
			);
		}
	}

	#[test]
	fn bound_only_associated_binding_keeps_its_where_clause() {
		let case = TestCase::new(indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Unsigned {}
			trait Store { type Size; }
			func grow<S: Store where { Size: Unsigned }>() {}
		"});
		assert_eq!(
			case.bound_formatter()
				.display_bound(case.declared_bounds("grow", "S")[0]),
			"Store where { Size: Unsigned }"
		);
	}

	#[test]
	fn nested_bounds_and_equalities_share_type_formatting() {
		let case = TestCase::new(indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Plain {}
			trait Leaf {}
			trait Inner { type Value; }
			trait Outer { type Item; type Count; }
			struct Wrapper<T>( value: T );
			func subject<T, S: Outer where {
				Item: Inner where { Value = Wrapper<T> } + Leaf,
				Count = u32
			} + Plain>() {}
		"});
		assert_eq!(
			case.bound_formatter()
				.display_bounds(case.declared_bounds("subject", "S")),
			"Outer where { Item: Inner where { Value = Wrapper<T> } + Leaf, Count = u32 } + Plain"
		);
	}
}
