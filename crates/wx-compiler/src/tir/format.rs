//! Renders resolved types and declared bounds into source-like text.
//! [`BoundFormatter`] reads source occurrences from the bound arena and
//! delegates equality types to [`TypeFormatter`], sharing one output buffer.
//!
//! A separate borrowing entity (the legacy `TypeFormatter<'a>`'s own
//! shape), not methods directly on `Semantics`: formatting is a
//! read-only concern with its own vocabulary (`write_type`, `write_bounds`,
//! ...), and keeping it off `Semantics` means a call site can hold
//! one to build a message while the surrounding code is about to mutate
//! `self` right after — the same reason the legacy one existed as its own
//! type rather than living on the (bigger, `&mut`-heavy) `Builder`.
//!
//! Borrows `types`/`decls`/`strings` plus `generic_envs` for generic parameter
//! names. Struct, enum, function, trait, and memory names come directly
//! from their definitions, without forcing signature resolution.
//! The formatter currently wraps `Semantics`'s pieces.

use std::fmt::Write as _;

use crate::ast::{Ownership, StringInterner};

use super::bounds::{BindingRequirement, BoundArena, BoundId};
use super::decls::{ConstIdx, Declarations, MemberOwner};
use super::signatures::Semantics;
use super::types::{GenericEnvArena, Type, TypeIndex, TypeInterner};

/// The bytes a type may take in a message, as rustc shortens a long type.
const TYPE_DISPLAY_BUDGET: usize = 64;

pub struct TypeFormatter<'a> {
	pub(super) types: &'a TypeInterner,
	pub(super) decls: &'a Declarations,
	pub(super) strings: &'a StringInterner,
	pub(super) generic_envs: &'a GenericEnvArena,
	/// How many bytes a type may take before the rest of it is written as
	/// `...`. A type can be far larger than its interned form (a doubling
	/// chain of shared parts is a handful of types and 2^n leaves), so this
	/// bounds both what a message shows and what printing it costs.
	pub(super) budget: usize,
}

/// Formats declared source bounds, preserving their order and bindings.
/// Implied bounds are merged requirements and cannot be rendered by reading
/// only their originating source occurrences.
pub struct BoundFormatter<'a> {
	type_formatter: TypeFormatter<'a>,
	bounds: &'a BoundArena,
}

impl Semantics {
	pub fn type_formatter<'a>(
		&'a self,
		strings: &'a StringInterner,
	) -> TypeFormatter<'a> {
		TypeFormatter {
			types: &self.types,
			decls: &self.decls,
			strings,
			generic_envs: &self.generic_envs,
			budget: TYPE_DISPLAY_BUDGET,
		}
	}

	pub fn bound_formatter<'a>(
		&'a self,
		strings: &'a StringInterner,
	) -> BoundFormatter<'a> {
		BoundFormatter {
			type_formatter: self.type_formatter(strings),
			bounds: &self.bounds,
		}
	}
}

impl BoundFormatter<'_> {
	pub fn display_bound(&self, bound: BoundId) -> String {
		let mut buffer = String::new();
		self.write_bound(&mut buffer, bound);
		buffer
	}

	pub fn display_bounds(&self, bounds: &[BoundId]) -> String {
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
		let symbol = self.type_formatter.decls.name(bound.trait_index).inner;
		f.push_str(self.type_formatter.strings.resolve(symbol).unwrap());
		if bound.bindings.is_empty() {
			return;
		}
		f.push_str(" where { ");
		for (i, binding) in bound.bindings.iter().enumerate() {
			if i > 0 {
				f.push_str(", ");
			}
			let decls = self.type_formatter.decls;
			let name =
				|symbol| self.type_formatter.strings.resolve(symbol).unwrap();
			match &binding.kind {
				BindingRequirement::Equals(target, ty) => {
					f.push_str(name(decls.name(target.assoc_type_index).inner));
					f.push_str(" = ");
					self.type_formatter.write_type(f, ty.inner);
				}
				BindingRequirement::Bound(target, bounds) => {
					f.push_str(name(decls.name(target.assoc_type_index).inner));
					f.push_str(": ");
					self.write_bounds(f, bounds);
				}
				BindingRequirement::Representable(target, ty) => {
					f.push_str("const ");
					f.push_str(name(decls.name(target.constant).inner));
					f.push_str(": ");
					self.type_formatter.write_type(f, ty.inner);
				}
			}
		}
		f.push_str(" }");
	}
}

impl TypeFormatter<'_> {
	pub fn display_type(&self, ty: TypeIndex) -> String {
		let mut buffer = String::new();
		self.write_type(&mut buffer, ty);
		buffer
	}

	/// Writes `ty` at the end of `f`, within `budget` bytes of where it
	/// starts.
	pub fn write_type(&self, f: &mut String, ty: TypeIndex) {
		let limit = f.len().saturating_add(self.budget);
		self.write_part(f, limit, ty);
	}

	/// Writes `ty`, a part of a type that must end by byte `limit` of `f`.
	///
	/// Past `limit`, a part is `...`, which stands for the rest of the
	/// type up to the next text its parent writes itself: parts that follow
	/// one another share one `...`, and the parts already open still close
	/// their brackets on the way out, so what is written stays a well-formed
	/// type (`((u32, ...))`, `func(u32, ...) -> ...`).
	fn write_part(&self, f: &mut String, limit: usize, ty: TypeIndex) {
		if f.len() >= limit {
			if !f.ends_with("...") {
				f.push_str("...");
			}
			return;
		}
		match self.types.resolve(ty) {
			Type::Error => f.push_str("{unknown}"),
			Type::Infer => f.push('_'),
			Type::Never => f.push('!'),
			Type::ConstInt => f.push_str("const_int"),
			Type::ConstFloat => f.push_str("const_float"),
			Type::ConstChar => f.push_str("const_char"),
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
			Type::Funcref => f.push_str("funcref"),
			Type::Tuple { elements } => {
				f.push('(');
				self.write_list(f, limit, self.types.list(*elements));
				if elements.len() == 1 {
					f.push(',');
				}
				f.push(')');
			}
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let symbol = self.decls.name(*struct_index).inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
				self.write_type_args(f, limit, self.types.list(*type_args));
			}
			Type::Enum { enum_index } => {
				let symbol = self.decls.name(*enum_index).inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			Type::Memory { memory_index, .. } => {
				let symbol = self.decls.name(*memory_index).inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			Type::Global { global_index } => {
				let symbol = self.decls.name(*global_index).inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => {
				self.write_part(f, limit, *memory);
				f.push_str("::");
				f.push(ownership_sigil(*ownership));
				self.write_part(f, limit, *to);
			}
			Type::Slice { of } => {
				f.push('[');
				self.write_part(f, limit, *of);
				f.push(']');
			}
			Type::Array { of, length } => {
				f.push('[');
				self.write_part(f, limit, *of);
				f.push_str("; ");
				self.write_part(f, limit, *length);
				f.push(']');
			}
			Type::Value { bits } => {
				let _ = write!(f, "{bits}");
			}
			// Written as its name, with its own arguments when it has any.
			Type::ConstRef {
				constant,
				type_args,
			} => {
				self.write_constant(
					f,
					limit,
					*constant,
					self.types.list(*type_args),
				);
			}
			Type::TypedFuncref { param, result } => {
				let (param, result) = (*param, *result);
				f.push_str("func(");
				// A parameter list is written back as one; a one-element
				// tuple is not a list, so it keeps its own parentheses.
				match self.types.resolve(param) {
					Type::Tuple { elements } if elements.len() != 1 => {
						self.write_list(f, limit, self.types.list(*elements));
					}
					_ => self.write_part(f, limit, param),
				}
				f.push_str(") -> ");
				self.write_part(f, limit, result);
			}
			Type::Function {
				func_index: function_index,
				type_args,
			} => {
				let function =
					&self.decls.functions[usize::from(*function_index)];
				let mut type_args = self.types.list(*type_args);
				// A trait's declaration takes `Self` first; it is written as
				// the receiver, `<Self as Trait>::f<own>`, always qualified
				// for the same reason a projection is.
				if let MemberOwner::Trait(trait_index) = function.owner {
					let (&receiver, own) = type_args
						.split_first()
						.expect("a trait's function takes `Self` first");
					f.push('<');
					self.write_part(f, limit, receiver);
					f.push_str(" as ");
					let symbol = self.decls.name(trait_index).inner;
					f.push_str(self.strings.resolve(symbol).unwrap());
					f.push_str(">::");
					type_args = own;
				}
				f.push_str(
					self.strings
						.resolve(self.decls.item(function.loc).name.inner)
						.unwrap(),
				);
				self.write_type_args(f, limit, type_args);
			}
			Type::TypeParam {
				env, param_index, ..
			} => {
				let symbol = self.generic_envs.param_names(*env)
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
			Type::TypeProjection {
				trait_index,
				assoc_type_index,
				base,
			} => {
				f.push('<');
				self.write_part(f, limit, *base);
				f.push_str(" as ");
				let symbol = self.decls.name(*trait_index).inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
				f.push_str(">::");
				let assoc_symbol = self.decls.name(*assoc_type_index).inner;
				f.push_str(self.strings.resolve(assoc_symbol).unwrap());
			}
		}
	}

	/// `constant` with `args`: a trait's declaration over its `Self` as a
	/// projection is (`<T as Array>::LEN`), any other with its arguments.
	pub fn display_constant(
		&self,
		constant: ConstIdx,
		args: &[TypeIndex],
	) -> String {
		let mut buffer = String::new();
		self.write_constant(&mut buffer, self.budget, constant, args);
		buffer
	}

	fn write_constant(
		&self,
		f: &mut String,
		limit: usize,
		constant: ConstIdx,
		args: &[TypeIndex],
	) {
		let decl = &self.decls.constants[usize::from(constant)];
		let name = self
			.strings
			.resolve(self.decls.item(decl.loc).name.inner)
			.unwrap();
		match decl.owner {
			MemberOwner::Trait(trait_index) => {
				f.push('<');
				self.write_part(f, limit, args[0]);
				f.push_str(" as ");
				let symbol = self.decls.name(trait_index).inner;
				f.push_str(self.strings.resolve(symbol).unwrap());
				f.push_str(">::");
				f.push_str(name);
			}
			_ => {
				f.push_str(name);
				self.write_type_args(f, limit, args);
			}
		}
	}

	fn write_type_args(
		&self,
		f: &mut String,
		limit: usize,
		args: &[TypeIndex],
	) {
		if args.is_empty() {
			return;
		}
		f.push('<');
		self.write_list(f, limit, args);
		f.push('>');
	}

	/// `items` separated by `, `. Past `limit` the rest of the list is
	/// `, ...`, unless the type already holds one: the `...` written inside
	/// an element stands for this list's rest too (`((x, ...))`, not
	/// `((x, ...), ...)`), which keeps a deeply nested type short.
	fn write_list(&self, f: &mut String, limit: usize, items: &[TypeIndex]) {
		for (i, &item) in items.iter().enumerate() {
			if i > 0 {
				if f.len() >= limit {
					let start = limit.saturating_sub(self.budget);
					if !f[start..].contains("...") {
						f.push_str(", ...");
					}
					return;
				}
				f.push_str(", ");
			}
			self.write_part(f, limit, item);
		}
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

	use indoc::indoc;

	use super::*;
	use crate::testing::DiagnosticView;
	use crate::tir::decls::{
		AssocTypeIdx, BindingKey, BindingTarget, DeclKind, FunctionIdx,
		MemberKind, Namespace, Tier, TraitIdx,
	};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::resolutions::NameResolutions;
	use crate::tir::signatures::tests::source_graph;
	use crate::tir::signatures::{QueryInfo, SemanticsBuilder};
	use crate::tir::types::GenericEnvIdx;

	/// A `Semantics` with every signature built and no body checked, and
	/// its interner.
	struct TestCase {
		strings: StringInterner,
		sema: Semantics,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut strings = crate::symbols::Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
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
			let (decls, ast_nodes) = Declarations::build(
				&graph.packages,
				&graph.files,
				&mut strings,
				&mut diagnostics,
				&mut resolutions,
				graph.core_package,
				graph.root_package,
			);
			DiagnosticView::new("prescan", &diagnostics, &graph.files)
				.assert_none();

			let dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				&strings,
				&decls,
				&ast_nodes,
			);
			let mut sema = Semantics::new(
				decls,
				dispatch,
				diagnostics,
				resolutions,
				&strings,
			);
			let mut builder = SemanticsBuilder::new(
				&graph.files,
				&graph.packages,
				&mut strings,
				&ast_nodes,
			);
			for entry in &ast_nodes {
				let _ = builder.ensure_signature(
					&mut sema,
					QueryInfo {
						query: entry.node.query(),
						requested_at: None,
					},
				);
			}
			DiagnosticView::new("signature", &sema.diagnostics, &graph.files)
				.assert_none();

			Self { strings, sema }
		}

		fn definition(&self, tier: Tier, name: &str) -> DeclKind {
			let symbol =
				self.strings.get(name).expect("expected a fixture name");
			let root = Namespace::Package(self.sema.decls.root_package);
			let BindingTarget::Accessible(key) =
				self.sema.decls.namespaces.symbols(root).bindings
					[&BindingKey::new(tier, symbol)]
					.target
			else {
				panic!("expected `{name}` to be accessible");
			};
			key.symbol_kind(&self.sema.decls)
		}

		fn function(&self, name: &str) -> FunctionIdx {
			let DeclKind::Function(index) = self.definition(Tier::Value, name)
			else {
				panic!("expected `{name}` to be a function");
			};
			index
		}

		fn parameter(
			&self,
			function: &str,
			name: &str,
		) -> (GenericEnvIdx, usize) {
			let env = self.sema.functions[usize::from(self.function(function))]
				.type_params;
			let index = self
				.sema
				.generic_envs
				.param_names(env)
				.iter()
				.position(|param| {
					self.strings.resolve(param.inner) == Some(name)
				})
				.unwrap_or_else(|| {
					panic!(
						"expected `{function}` to have a type parameter `{name}`"
					)
				});
			(env, index)
		}

		fn type_formatter(&self) -> TypeFormatter<'_> {
			self.sema.type_formatter(&self.strings)
		}

		fn type_param(&self, function: &str, name: &str) -> TypeIndex {
			let (env, index) = self.parameter(function, name);
			self.sema.generic_envs.param_types(env)[index]
		}

		/// The bounds written on `param`, as written: every top-level bound
		/// between its name and the next parameter's.
		fn declared_bounds(&self, function: &str, param: &str) -> Vec<BoundId> {
			let (env, index) = self.parameter(function, param);
			let names = self.sema.generic_envs.param_names(env);
			let after = names[index].span.end;
			let before =
				names.get(index + 1).map_or(u32::MAX, |n| n.span.start);
			let file_id = self.sema.decls.file_id(
				self.sema.decls.functions[usize::from(self.function(function))]
					.loc,
			);
			let written: Vec<BoundId> = self
				.sema
				.bounds
				.ids()
				.filter(|&id| {
					let span = self.sema.bounds.span(id);
					span.file_id == file_id
						&& (after..before).contains(&span.span.start)
				})
				.collect();
			let nested: Vec<BoundId> = written
				.iter()
				.flat_map(|&id| self.sema.bounds.get(id).bindings.iter())
				.flat_map(|binding| match &binding.kind {
					BindingRequirement::Bound(_, nested) => nested.to_vec(),
					BindingRequirement::Equals(..)
					| BindingRequirement::Representable(..) => Vec::new(),
				})
				.collect();
			written
				.into_iter()
				.filter(|id| !nested.contains(id))
				.collect()
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
				.strings
				.get(name)
				.expect("already interned from source");
			let trait_decl = &self.sema.decls.traits[usize::from(trait_index)];
			let &member_index = trait_decl
				.bindings
				.get(&BindingKey::ty(symbol))
				.unwrap_or_else(|| {
					panic!(
						"expected the trait to have an associated type `{name}`"
					)
				});
			let MemberKind::AssociatedType(index) =
				trait_decl.members[usize::from(member_index)].kind
			else {
				panic!("expected `{name}` to be an associated type");
			};
			index
		}

		fn bound_formatter(&self) -> BoundFormatter<'_> {
			self.sema.bound_formatter(&self.strings)
		}
	}

	#[test]
	fn function_types_format_nested_tuples_and_recovery_placeholders() {
		let mut case = TestCase::new("");
		let tuple = case
			.sema
			.types
			.intern_tuple(&[TypeIndex::I32, TypeIndex::ERROR]);
		let param = case.sema.types.intern_tuple(&[tuple, TypeIndex::INFER]);
		let function = case.sema.types.intern(Type::TypedFuncref {
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
		let mut case = TestCase::new("func allocate<M>() {}");
		let memory = case.type_param("allocate", "M");
		let slice = case.sema.types.intern(Type::Slice { of: TypeIndex::I32 });
		let slice = case.sema.types.intern(Type::Pointer {
			to: slice,
			memory,
			ownership: Ownership::Shared,
		});
		let pointer = case.sema.types.intern(Type::Pointer {
			to: slice,
			memory,
			ownership: Ownership::Exclusive,
		});
		let four = case.sema.types.intern(Type::Value { bits: 4 });
		let array = case.sema.types.intern(Type::Array {
			of: TypeIndex::I32,
			length: four,
		});
		let to_array = case.sema.types.intern(Type::Pointer {
			to: array,
			memory,
			ownership: Ownership::Exclusive,
		});
		let formatter = case.type_formatter();
		assert_eq!(formatter.display_type(pointer), "M::*M::&[i32]");
		assert_eq!(formatter.display_type(to_array), "M::*[i32; 4]");
		assert_eq!(formatter.display_type(array), "[i32; 4]");
	}

	#[test]
	fn named_functions_and_associated_types_keep_names_and_qualification() {
		let mut case = TestCase::new(indoc! {"
			trait Iterable { type Item; }
			func iterate<T: Iterable>() {}
		"});
		let param = case.type_param("iterate", "T");
		let DeclKind::Trait(trait_index) =
			case.definition(Tier::Type, "Iterable")
		else {
			panic!("expected Iterable to be a trait");
		};
		let assoc_type_index = case.assoc_type_index(trait_index, "Item");
		let projection = case.sema.types.intern(Type::TypeProjection {
			trait_index,
			assoc_type_index,
			base: param,
		});
		let function = case
			.sema
			.types
			.intern_function(case.function("iterate"), &[param]);
		let formatter = case.type_formatter();
		assert_eq!(formatter.display_type(function), "iterate<T>");
		assert_eq!(formatter.display_type(projection), "<T as Iterable>::Item");
	}

	#[test]
	fn bound_lists_preserve_written_order_without_expanding_supertraits() {
		let case = TestCase::new(indoc! {"
			trait Base {}
			trait A: Base {}
			trait B {}
			func subject<T, U: A, V: B + A + B>() {}
		"});
		let formatter = case.bound_formatter();
		for (param, expected) in [("T", ""), ("U", "A"), ("V", "B + A + B")] {
			assert_eq!(
				formatter
					.display_bounds(&case.declared_bounds("subject", param)),
				expected
			);
		}
	}

	#[test]
	fn bound_only_associated_binding_keeps_its_where_clause() {
		let case = TestCase::new(indoc! {"
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
				.display_bounds(&case.declared_bounds("subject", "S")),
			"Outer where { Item: Inner where { Value = Wrapper<T> } + Leaf, Count = u32 } + Plain"
		);
	}
	/// `(u32, u32, ..., ...)`, the first `fit` elements of a long tuple of
	/// `u32` and the rest elided.
	fn elided_u32s(fit: usize) -> String {
		format!("({}, ...)", vec!["u32"; fit].join(", "))
	}

	#[test]
	fn a_type_within_the_budget_is_written_whole() {
		let mut case = TestCase::new("");
		let tuple = case.sema.types.intern_tuple(&[TypeIndex::U32; 4]);
		assert_eq!(
			case.type_formatter().display_type(tuple),
			"(u32, u32, u32, u32)"
		);
	}

	#[test]
	fn a_long_list_ends_in_an_ellipsis_once_the_budget_is_spent() {
		let mut case = TestCase::new("");
		let tuple = case.sema.types.intern_tuple(&[TypeIndex::U32; 30]);
		assert_eq!(case.type_formatter().display_type(tuple), elided_u32s(13));
	}

	#[test]
	fn an_ellipsis_stands_for_the_rest_of_the_enclosing_lists() {
		// The `u8` after the long tuple is part of the elided rest, so the
		// outer list adds no `, ...` of its own.
		let mut case = TestCase::new("");
		let inner = case.sema.types.intern_tuple(&[TypeIndex::U32; 30]);
		let outer = case.sema.types.intern_tuple(&[inner, TypeIndex::U8]);
		assert_eq!(
			case.type_formatter().display_type(outer),
			format!("({})", elided_u32s(13))
		);
	}

	#[test]
	fn a_part_after_its_parents_own_text_is_elided_on_its_own() {
		let mut case = TestCase::new("");
		let param = case.sema.types.intern_tuple(&[TypeIndex::U32; 30]);
		let function = case.sema.types.intern(Type::TypedFuncref {
			param,
			result: TypeIndex::U8,
		});
		assert_eq!(
			case.type_formatter().display_type(function),
			// `func` spends four bytes of the budget, one element's worth.
			format!("func{} -> ...", elided_u32s(12))
		);
	}

	#[test]
	fn a_type_far_larger_than_its_interned_form_prints_in_bounded_length() {
		// 300 interned tuples, 2^300 leaves: only the start is ever visited,
		// and every bracket it opened is closed.
		let mut case = TestCase::new("");
		let mut doubled = TypeIndex::U8;
		for _ in 0..300 {
			doubled = case.sema.types.intern_tuple(&[doubled, doubled]);
		}
		let depth = TYPE_DISPLAY_BUDGET;
		assert_eq!(
			case.type_formatter().display_type(doubled),
			format!("{}...{}", "(".repeat(depth), ")".repeat(depth))
		);
	}

	#[test]
	fn the_budget_counts_from_where_the_type_starts() {
		// A message written before the type does not spend its budget.
		let mut case = TestCase::new("");
		let short = case.sema.types.intern_tuple(&[TypeIndex::U32; 4]);
		let long = case.sema.types.intern_tuple(&[TypeIndex::U32; 30]);
		let formatter = case.type_formatter();
		let prefix = "x".repeat(2 * TYPE_DISPLAY_BUDGET);
		let mut buffer = prefix.clone();
		formatter.write_type(&mut buffer, short);
		assert_eq!(&buffer[prefix.len()..], "(u32, u32, u32, u32)");
		let mut buffer = prefix.clone();
		formatter.write_type(&mut buffer, long);
		assert_eq!(&buffer[prefix.len()..], elided_u32s(13));
	}
}
