//! Renders resolved types and declared bounds into source-like text.
//! [`BoundFormatter`] reads source occurrences from the bound arena and
//! delegates equality types to [`TypeFormatter`], sharing one output buffer.
//!
//! A separate borrowing entity (the legacy `TypeFormatter<'a>`'s own
//! shape), not methods directly on `SignatureBuilder`: formatting is a
//! read-only concern with its own vocabulary (`write_type`, `write_bounds`,
//! ...), and keeping it off `SignatureBuilder` means a call site can hold
//! one to build a message while the surrounding code is about to mutate
//! `self` right after — the same reason the legacy one existed as its own
//! type rather than living on the (bigger, `&mut`-heavy) `Builder`.
//!
//! Borrows `types`/`defs`/`strings` plus `type_envs` for generic parameter
//! names. Struct, enum, function, trait, and memory names come directly
//! from their definitions, without forcing signature resolution.
//! The formatter currently wraps `SignatureBuilder`'s pieces.

use std::fmt::Write as _;

use crate::ast::{Ownership, StringInterner};

use super::bounds::{BindingRequirement, BoundArena, BoundId};
use super::defs::DefinitionRegistry;
use super::signatures::SignatureBuilder;
use super::types::{Type, TypeEnvArena, TypeIndex, TypeInterner};

pub(super) struct TypeFormatter<'a> {
	types: &'a TypeInterner,
	defs: &'a DefinitionRegistry,
	strings: &'a StringInterner,
	type_envs: &'a TypeEnvArena,
}

/// Formats declared source bounds, preserving their order and bindings.
/// Implied bounds are merged requirements and cannot be rendered by reading
/// only their originating source occurrences.
pub(super) struct BoundFormatter<'a> {
	type_formatter: TypeFormatter<'a>,
	bounds: &'a BoundArena,
}

impl SignatureBuilder<'_, '_> {
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
				[usize::from(binding.assoc_type_index)]
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
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let symbol =
					self.defs.structs[usize::from(*struct_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
				self.write_type_args(f, type_args);
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
			Type::FunctionItem {
				func_index: function_index,
				type_args,
			} => {
				f.push_str("fn ");
				let symbol = self.defs.functions[usize::from(*function_index)]
					.name
					.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
				self.write_type_args(f, type_args);
			}
			Type::TypeParam {
				env, param_index, ..
			} => {
				let symbol = self.type_envs.frame(*env)[*param_index as usize]
					.name
					.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			Type::AssociatedType {
				trait_index,
				assoc_name,
			} => {
				let symbol =
					self.defs.traits[usize::from(*trait_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
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
				let symbol =
					self.defs.traits[usize::from(*trait_index)].name.inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
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
		BindingKey, BindingNamespace, BindingTarget, DefKind, FunctionIdx,
	};
	use crate::tir::impls::ImplDispatch;
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
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				graph.stdlib_package,
				graph.root_package,
			);
			DiagnosticView::new("prescan", &diagnostics, &graph.files)
				.assert_none();

			let dispatch = ImplDispatch::build(
				&mut diagnostics,
				&graph.strings,
				&defs,
				&ast_nodes,
			);
			let mut signatures = SignatureBuilder::new(
				&mut diagnostics,
				&graph.strings,
				&defs,
				&ast_nodes,
				dispatch,
			);
			for entry in &ast_nodes {
				let _ = signatures.ensure_signature(QueryInfo {
					def_id: entry.def_id,
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

		fn definition(&self, tier: BindingNamespace, name: &str) -> DefKind {
			let symbol = self
				.graph
				.strings
				.get(name)
				.expect("expected a fixture name");
			let root = self.defs.root_package.root_namespace();
			let BindingTarget::Accessible(key) = self.defs.namespaces
				[usize::from(root)]
			.bindings[&BindingKey::new(tier, symbol)]
				.target
			else {
				panic!("expected `{name}` to be accessible");
			};
			key.symbol_kind(&self.defs)
		}

		fn function(&self, name: &str) -> FunctionIdx {
			let DefKind::Function(index) =
				self.definition(BindingNamespace::Value, name)
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
				.frame(env)
				.iter()
				.position(|param| {
					self.graph.strings.resolve(param.name.inner) == Some(name)
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
			self.type_envs.frame(env)[index].ty
		}

		fn declared_bounds(&self, function: &str, param: &str) -> &[BoundId] {
			let (env, index) = self.parameter(function, param);
			&self.param_bounds[usize::from(env)][index].declared_bounds
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
		let tuple = case.types.intern(Type::Tuple {
			elements: Box::new([TypeIndex::I32, TypeIndex::ERROR]),
		});
		let function = case.types.intern(Type::Function {
			params: Box::new([tuple, TypeIndex::INFER]),
			result: TypeIndex::NEVER,
		});
		assert_eq!(
			case.type_formatter().display_type(function),
			"fn((i32, {unknown}), _) -> never"
		);
	}

	#[test]
	fn memory_qualified_types_preserve_ownership_and_shape() {
		let mut case = TestCase::new("fn allocate<M>() {}");
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
			trait Iterable { type Item; }
			fn iterate<T: Iterable>() {}
		"});
		let param = case.type_param("iterate", "T");
		let DefKind::Trait(trait_index) =
			case.definition(BindingNamespace::Type, "Iterable")
		else {
			panic!("expected Iterable to be a trait");
		};
		let assoc_name = case.graph.strings.get("Item").unwrap();
		let associated = case.types.intern(Type::AssociatedType {
			trait_index,
			assoc_name,
		});
		let projection = case.types.intern(Type::AssocTypeProjection {
			trait_index,
			assoc_name,
			base: param,
		});
		let function = case.types.intern(Type::FunctionItem {
			func_index: case.function("iterate"),
			type_args: Box::new([param]),
		});
		let formatter = case.type_formatter();
		assert_eq!(formatter.display_type(function), "fn iterate<T>");
		assert_eq!(formatter.display_type(associated), "Iterable::Item");
		assert_eq!(formatter.display_type(projection), "<T as Iterable>::Item");
	}

	#[test]
	fn bound_lists_preserve_written_order_without_expanding_supertraits() {
		let case = TestCase::new(indoc! {"
			trait Base {}
			trait A: Base {}
			trait B {}
			fn subject<T, U: A, V: B + A + B>() {}
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
			trait Unsigned {}
			trait Store { type Size; }
			fn grow<S: Store where { Size: Unsigned }>() {}
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
			type u32;
			trait Plain {}
			trait Leaf {}
			trait Inner { type Value; }
			trait Outer { type Item; type Count; }
			struct Wrapper<T> { value: T }
			fn subject<T, S: Outer where {
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
