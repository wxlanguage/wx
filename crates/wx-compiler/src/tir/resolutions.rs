//! Every written name the compiler resolved, in one table.
//!
//! The caller owns the table next to the diagnostics sink and lends it
//! `&mut` to every stage: phase 1 records the segments of `use` paths, the
//! path walk records every segment it resolves, and signature construction
//! records generic parameters and selected members. Only code that has
//! committed to a meaning records it, so a lookup that is tried and
//! discarded leaves no trace.
//!
//! Entries are keyed by where the name is written, so resolving the same
//! site again overwrites it instead of adding a second entry. The order is
//! by file and then position, which turns "what does the name under the
//! cursor mean" into a range lookup. Who refers to a definition, or which
//! `use` items are never used, is the inverse of this table and is computed
//! from it when needed.
//!
//! This is a reference table, not a token index: declaration names live in
//! their owning definition/body tables, and unresolved names have no entry.
//! Identities are local to one compilation; locals and labels need their body
//! owner, and fields need their struct because their indices are owner-relative.
//!
//! A shorthand argument (`f({ x })` or `S({ x })`) has two references at
//! one span and value tier. `Resolution::Shorthand` preserves both the label's
//! parameter/field and the value it supplies; the lookup key stays unchanged.

use std::collections::BTreeMap;

use super::body::{BodyOwner, LabelIdx, LocalIdx, ParamIdx};
use super::defs::{
	DefKey, FieldIdx, FunctionIdx, InherentImplIdx, MemberKind, StructIdx,
	Tier, TraitImplIdx, UseItemIndex,
};
use super::types::GenericEnvIdx;
use crate::diagnostics::SourceSpan;

/// Keyed by the written name's span and the tier it was looked up in: a
/// `use` leaf names a type and a value at the same span.
#[derive(Default)]
pub(super) struct NameResolutions {
	pub(super) by_site: BTreeMap<(SourceSpan, Tier), Resolution>,
}

impl NameResolutions {
	pub(super) fn record(
		&mut self,
		site: (SourceSpan, Tier),
		referent: Referent,
	) {
		self.by_site.insert(site, Resolution::Reference(referent));
	}

	pub(super) fn record_selection(
		&mut self,
		site: (SourceSpan, Tier),
		selection: Selection,
	) {
		self.by_site.insert(site, Resolution::Selection(selection));
	}
}

/// The meaning of one written name: one target, or the two targets of shorthand.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Resolution {
	Reference(Referent),
	Selection(Selection),
	/// `selection` is a parameter or field; `value` is the independently resolved
	/// value name, which can be a local, a constant, or an imported definition.
	Shorthand {
		selection: Selection,
		value: Referent,
	},
}

/// A target reached through name lookup, independent of its source occurrence.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Referent {
	/// A definition declared in the namespace the name was looked up in:
	/// an item, a module, a package or an import block.
	Definition(DefKey),
	/// A definition the namespace it was looked up in made visible through
	/// a `use` item there, a named import or a glob. Only that first `use`
	/// is recorded; one it leads through in another namespace can be found
	/// again by looking the name up from it.
	Import {
		definition: DefKey,
		import: UseItemIndex,
	},
	/// A generic parameter, or a trait's own `Self`: its frame and position
	/// in it.
	TypeParam { env: GenericEnvIdx, index: u32 },
	/// `Self` inside an inherent impl, which names the impl's target and is
	/// not a parameter of it.
	InherentImplSelf(InherentImplIdx),
	/// `Self` inside a trait impl; see `InherentImplSelf`.
	TraitImplSelf(TraitImplIdx),
	/// A member selected through a type: `T::A`, `<X as Tr>::A`.
	Member(MemberKind),
	/// A local of the body `owner`: a parameter or a `local`.
	Local { owner: BodyOwner, local: LocalIdx },
	/// A label of the body `owner`, named by a `break` or `continue`.
	Label { owner: BodyOwner, label: LabelIdx },
}

/// A field or parameter selected by name from a known owner.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Selection {
	/// A field selected on a struct value, a place or a named pattern.
	Field { owner: StructIdx, field: FieldIdx },
	/// A named argument's parameter, owned by the declaration whose names the
	/// call uses (the trait declaration for a trait implementation's method).
	/// This does not require the callee to have a body or a corresponding local.
	Parameter {
		function: FunctionIdx,
		parameter: ParamIdx,
	},
}

impl Referent {
	/// What a namespace lookup found: `import` is the `use` item it came
	/// through, as `BindingLookup::Found` reports it.
	pub(super) fn from_lookup(
		definition: DefKey,
		import: Option<UseItemIndex>,
	) -> Self {
		match import {
			Some(import) => Self::Import { definition, import },
			None => Self::Definition(definition),
		}
	}
}

#[cfg(test)]
mod tests {
	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::{Diagnostics, TextSpan};
	use crate::tir::body::Local;
	use crate::tir::defs::{BindingKey, DefKind, DefinitionRegistry, Scope};
	use crate::tir::impls::{ImplDispatch, ImplTarget};
	use crate::tir::paths::PathResolver;
	use crate::tir::signatures::TypeContext;
	use crate::tir::solver::Solver;
	use crate::vfs::{self, FileId};

	struct Analysis<'s> {
		source: &'s str,
		file: FileId,
		resolutions: NameResolutions,
		defs: DefinitionRegistry,
		strings: StringInterner,
		impl_dispatch: ImplDispatch,
		function_locals: Vec<Vec<Local>>,
		function_envs: Vec<GenericEnvIdx>,
		trait_envs: Vec<GenericEnvIdx>,
		errors: Vec<String>,
	}

	impl<'s> Analysis<'s> {
		fn new(source: &'s str) -> Self {
			let mut strings = ast::Keyword::create_interner();
			let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
			builder.load_stdlib();
			let root = builder
				.load_binary(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(
						std::collections::HashMap::from([(
							"main.wx".to_string(),
							source.to_string(),
						)]),
					),
				)
				.unwrap();
			let compilation = builder.build(root);
			let parse_diagnostics = compilation.collect_diagnostics();
			assert!(!parse_diagnostics.has_errors(), "{parse_diagnostics:?}");
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, nodes) = DefinitionRegistry::build(
				&compilation.packages,
				&compilation.files,
				&mut strings,
				&mut diagnostics,
				&mut resolutions,
				compilation.stdlib_package,
				root,
			);
			let file = defs
				.namespaces
				.file_id(crate::tir::defs::Scope::Package(root).into());
			let dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				&strings,
				&defs,
				&nodes,
			);
			let mut solver = Solver::new(defs.constants.len());
			let mut context = TypeContext::new(
				&mut diagnostics,
				&mut resolutions,
				&mut strings,
				&mut solver,
				&compilation.files,
				&defs,
				&nodes,
				&dispatch,
			);
			context.sweep();
			let function_locals = context
				.function_implementations
				.iter()
				.map(|implementation| {
					implementation
						.body()
						.map(|body| context.body(body).locals().to_vec())
						.unwrap_or_default()
				})
				.collect();
			let function_envs = context
				.functions
				.iter()
				.map(|signature| signature.type_params)
				.collect();
			let trait_envs = context
				.traits
				.iter()
				.map(|signature| signature.env)
				.collect();
			drop(context);
			let errors =
				diagnostics.errors().map(|d| d.message.clone()).collect();
			Self {
				source,
				file,
				resolutions,
				defs,
				strings,
				impl_dispatch: dispatch,
				function_locals,
				function_envs,
				trait_envs,
				errors,
			}
		}

		fn clean(source: &'s str) -> Self {
			let analysis = Self::new(source);
			assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
			analysis
		}

		fn at(
			&self,
			context: &str,
			name: &str,
			tier: Tier,
		) -> Option<Referent> {
			self.resolution(context, name, tier).map(|resolution| {
				let Resolution::Reference(referent) = resolution else {
					panic!("expected one target for `{name}` in `{context}`");
				};
				referent
			})
		}

		fn resolution(
			&self,
			context: &str,
			name: &str,
			tier: Tier,
		) -> Option<Resolution> {
			let span = self.span(context, name);
			self.resolutions
				.by_site
				.get(&(SourceSpan::new(self.file, span), tier))
				.copied()
		}

		fn span(&self, context: &str, name: &str) -> TextSpan {
			let start = self.source.find(context).unwrap()
				+ context.find(name).unwrap();
			TextSpan::new(start as u32, (start + name.len()) as u32)
		}

		fn value(&self, context: &str, name: &str) -> Referent {
			self.at(context, name, Tier::Value).unwrap_or_else(|| {
				panic!("`{name}` in `{context}` was not recorded")
			})
		}

		fn selection(&self, context: &str, name: &str) -> Selection {
			let Some(Resolution::Selection(selection)) =
				self.resolution(context, name, Tier::Value)
			else {
				panic!("expected a selection for `{name}` in `{context}`");
			};
			selection
		}

		fn resolve(&self, path: &str, tier: Tier) -> DefKind {
			self.definition(path, tier).symbol_kind(&self.defs)
		}

		fn definition(&self, path: &str, tier: Tier) -> DefKey {
			let segments: Box<[ast::PathSegment]> = path
				.split("::")
				.map(|name| ast::PathSegment {
					ident: Spanned {
						inner: self.strings.get(name).unwrap(),
						span: TextSpan::new(0, 0),
					},
					type_args: Box::new([]),
				})
				.collect();
			// Keep synthetic lookup spans out of the table under test.
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let target = PathResolver::new(
				&mut diagnostics,
				&mut resolutions,
				&self.strings,
				&self.defs,
			)
			.resolve_path(
				self.file,
				Scope::Package(self.defs.root_package),
				&segments,
				tier,
			);
			assert!(diagnostics.is_empty(), "{diagnostics:?}");
			target
				.def_key()
				.unwrap_or_else(|| panic!("expected `{path}` to resolve"))
		}

		fn struct_index(&self, path: &str) -> StructIdx {
			let DefKind::Struct(index) = self.resolve(path, Tier::Type) else {
				panic!("expected `{path}` to name a struct");
			};
			index
		}

		fn function_index(&self, path: &str) -> FunctionIdx {
			let DefKind::Function(index) = self.resolve(path, Tier::Value)
			else {
				panic!("expected `{path}` to name a function");
			};
			index
		}

		fn trait_member(
			&self,
			path: &str,
			name: &str,
			tier: Tier,
		) -> MemberKind {
			let DefKind::Trait(index) = self.resolve(path, Tier::Type) else {
				panic!("expected `{path}` to name a trait");
			};
			self.defs
				.declared_trait_member(
					index,
					BindingKey::new(tier, self.strings.get(name).unwrap()),
				)
				.unwrap()
		}
	}

	#[test]
	fn local_reads_writes_and_shadowing_keep_their_identity() {
		let a = Analysis::clean(indoc! {"
			func f(x: u32) -> u32 {
				local mut y = x;
				y = x + 1;
				y += 2;
				local _ = block {
					local y: u32 = 3;
					y
				};
				y
			}
		"});
		let x = a.value("= x;", "x");
		let y = a.value("y = x +", "y");
		assert!(matches!(x, Referent::Local { .. }));
		assert!(matches!(y, Referent::Local { .. }));
		assert_ne!(x, y);
		assert_eq!(x, a.value("= x +", "x"));
		assert_eq!(y, a.value("y +=", "y"));
		assert_eq!(y, a.value("\n\ty\n", "y"));
		assert_ne!(y, a.value("\n\t\ty\n", "y"));
		// Bindings are declarations, not references.
		assert_eq!(a.at("mut y =", "y", Tier::Value), None);
	}

	#[test]
	fn locals_in_different_bodies_do_not_alias() {
		let a = Analysis::clean(indoc! {"
			func f(x: u32) -> u32 { x }
			func g(x: u32) -> u32 { x + 1 }
		"});
		let Referent::Local { owner: f, local: x } = a.value("{ x }", "x")
		else {
			panic!()
		};
		let Referent::Local { owner: g, local: y } = a.value("{ x +", "x")
		else {
			panic!()
		};
		assert_eq!(x, y);
		assert_ne!(f, g);
	}

	#[test]
	fn destructured_bindings_are_recorded_when_read() {
		let a = Analysis::clean(indoc! {"
			func f(p: (u32, u32)) -> u32 {
				local (left, right) = p;
				left + right
			}
		"});
		let left = a.value("left +", "left");
		let right = a.value("+ right", "right");
		assert!(matches!(left, Referent::Local { .. }));
		assert!(matches!(right, Referent::Local { .. }));
		assert_ne!(left, right);
	}

	#[test]
	fn paths_record_each_segment_and_import_provenance() {
		let a = Analysis::clean(indoc! {"
			mod m {
				pub func run() {}
			}
			use m::run as alias;
			func f() {
				m::run();
				alias();
			}
		"});
		assert!(matches!(
			a.at("m::run();", "m", Tier::Type),
			Some(Referent::Definition(_))
		));
		let Referent::Definition(direct) = a.value("m::run();", "run") else {
			panic!()
		};
		let Referent::Import { definition, .. } = a.value("alias();", "alias")
		else {
			panic!()
		};
		assert_eq!(direct, definition);
	}

	#[test]
	fn generic_type_references_and_method_names_are_recorded() {
		let a = Analysis::clean(indoc! {"
			struct S();
			impl S {
				func get(self: Self) -> u32 { 1 }
			}
			func f<T: StackValue>(x: T, s: S) -> T {
				local _ = s.get();
				x
			}
		"});
		assert!(matches!(
			a.at("x: T", "T", Tier::Type),
			Some(Referent::TypeParam { .. })
		));
		assert_eq!(
			a.at("x: T", "T", Tier::Type),
			a.at("-> T", "T", Tier::Type)
		);
		assert!(matches!(
			a.value("s.get()", "get"),
			Referent::Member(MemberKind::Method(_))
		));
	}

	#[test]
	fn field_reads_and_assignment_targets_record_owner_relative_identity() {
		let a = Analysis::clean(indoc! {"
			struct A(value: u32);
			struct B(value: u32);
			func f(mut a: A, b: B) -> u32 {
				a.value = b.value;
				a.value
			}
		"});
		let first = a.selection("a.value =", "value");
		assert_eq!(
			first,
			Selection::Field {
				owner: a.struct_index("A"),
				field: FieldIdx::new(0),
			}
		);
		assert_eq!(first, a.selection("\n\ta.value\n", "value"));
		let Selection::Field {
			owner: a_owner,
			field: a_field,
		} = first
		else {
			panic!()
		};
		let Selection::Field {
			owner: b_owner,
			field: b_field,
		} = a.selection("b.value;", "value")
		else {
			panic!()
		};
		assert_eq!(
			a.selection("b.value;", "value"),
			Selection::Field {
				owner: a.struct_index("B"),
				field: FieldIdx::new(0),
			}
		);
		assert_eq!(a_field, b_field);
		assert_ne!(a_owner, b_owner);
	}

	#[test]
	fn unresolved_names_do_not_erase_resolved_neighbors() {
		let a = Analysis::new(indoc! {"
			func f(x: u32) {
				x;
				missing;
				x;
			}
		"});
		assert!(!a.errors.is_empty());
		assert_eq!(a.at("missing;", "missing", Tier::Value), None);
		assert_eq!(a.value("\n\tx;\n", "x"), a.value("missing;\n\tx;", "x"));
	}

	#[test]
	fn named_arguments_record_labels_and_both_shorthand_references() {
		let a = Analysis::clean(indoc! {"
			func take(x: u32) {}
			func f(x: u32) -> u32 {
				take({ x: 1 });
				take({ x });
				x
			}
		"});
		let selection = Selection::Parameter {
			function: a.function_index("take"),
			parameter: ParamIdx::new(0),
		};
		assert_eq!(a.selection("{ x: 1", "x"), selection);
		assert_eq!(
			a.resolution("{ x }", "x", Tier::Value),
			Some(Resolution::Shorthand {
				selection,
				value: a.value("\n\tx\n", "x"),
			})
		);
	}

	#[test]
	fn constructor_arguments_record_fields_and_both_shorthand_references() {
		let a = Analysis::clean(indoc! {"
			struct S(other: u32, value: u32);
			func f(value: u32) -> u32 {
				local _ = S({ other: 0, value: 1 });
				local _ = S({ other: 0, value });
				value
			}
		"});
		let field = Selection::Field {
			owner: a.struct_index("S"),
			field: FieldIdx::new(1),
		};
		assert_eq!(a.selection("value: 1", "value"), field);
		assert_eq!(
			a.resolution("value });", "value", Tier::Value),
			Some(Resolution::Shorthand {
				selection: field,
				value: a.value("\n\tvalue\n", "value"),
			})
		);
	}

	#[test]
	fn shorthand_can_supply_an_imported_constant_instead_of_a_local() {
		let a = Analysis::clean(indoc! {"
			mod m { pub const value: u32 = 7; }
			use m::value;
			func take(value: u32) {}
			func f() -> u32 {
				take({ value });
				value
			}
		"});
		let value = a.value("\n\tvalue\n", "value");
		assert!(matches!(value, Referent::Import { .. }));
		assert_eq!(
			a.resolution("{ value }", "value", Tier::Value),
			Some(Resolution::Shorthand {
				selection: Selection::Parameter {
					function: a.function_index("take"),
					parameter: ParamIdx::new(0),
				},
				value,
			})
		);
	}

	#[test]
	fn unresolved_shorthand_values_still_record_the_parameter() {
		let a = Analysis::new(indoc! {"
			func take(value: u32) {}
			func f() {
				take({ value });
			}
		"});
		assert!(!a.errors.is_empty());
		assert_eq!(
			a.selection("{ value }", "value"),
			Selection::Parameter {
				function: a.function_index("take"),
				parameter: ParamIdx::new(0),
			}
		);
	}

	#[test]
	fn unknown_argument_labels_do_not_erase_shorthand_value_references() {
		let a = Analysis::new(indoc! {"
			func take(other: u32) {}
			func f(value: u32) -> u32 {
				take({ value });
				value
			}
		"});
		assert!(!a.errors.is_empty());
		assert_eq!(
			a.value("{ value }", "value"),
			a.value("\n\tvalue\n", "value")
		);
	}

	#[test]
	fn trait_argument_labels_refer_to_the_naming_declaration_without_a_body() {
		let a = Analysis::clean(indoc! {"
			trait Make: StackValue {
				func make(value: u32) -> Self;
			}
			struct S(value: u32);
			impl Make for S {
				func make(_: u32) -> Self { S(0) }
			}
			func concrete(value: u32) -> S {
				S::make({ value })
			}
			func generic<T: Make>(value: u32) -> T {
				T::make({ value })
			}
		"});
		let DefKind::Trait(trait_index) = a.resolve("Make", Tier::Type) else {
			panic!("expected a trait");
		};
		let Some(MemberKind::Function(function)) =
			a.defs.declared_trait_member(
				trait_index,
				crate::tir::defs::BindingKey::value(
					a.strings.get("make").unwrap(),
				),
			)
		else {
			panic!("expected the trait's function declaration");
		};
		for (call, caller) in [
			("S::make({ value })", "concrete"),
			("T::make({ value })", "generic"),
		] {
			assert_eq!(
				a.resolution(call, "value", Tier::Value),
				Some(Resolution::Shorthand {
					selection: Selection::Parameter {
						function,
						parameter: ParamIdx::new(0),
					},
					value: Referent::Local {
						owner: BodyOwner::Function(a.function_index(caller)),
						local: LocalIdx::new(0),
					},
				})
			);
		}
	}

	#[test]
	fn named_pattern_fields_refer_to_the_same_field_as_an_access() {
		let a = Analysis::clean(indoc! {"
			struct S(value: u32);
			func f(s: S) -> u32 {
				local _ = s.value;
				local S({ value: x }) = s;
				x
			}
		"});
		assert_eq!(
			a.selection("{ value: x", "value"),
			Selection::Field {
				owner: a.struct_index("S"),
				field: FieldIdx::new(0),
			}
		);
		assert_eq!(
			a.selection("{ value: x", "value"),
			a.selection("s.value;", "value")
		);
		assert!(matches!(a.value("\n\tx\n", "x"), Referent::Local { .. }));
	}

	#[test]
	fn field_selection_through_a_pointer_uses_the_struct_identity() {
		let a = Analysis::clean(indoc! {"
			memory heap: u32;
			struct S(value: u32);
			func f(p: heap::*S, s: S) -> u32 {
				p.value = s.value;
				p.value
			}
		"});
		assert_eq!(
			a.selection("p.value =", "value"),
			Selection::Field {
				owner: a.struct_index("S"),
				field: FieldIdx::new(0),
			}
		);
		assert_eq!(
			a.selection("p.value =", "value"),
			a.selection("s.value;", "value")
		);
		assert_eq!(
			a.selection("p.value =", "value"),
			a.selection("\n\tp.value\n", "value")
		);
	}

	#[test]
	fn labelled_break_and_continue_refer_to_the_same_label() {
		let a = Analysis::clean(indoc! {"
			func f(c: Bool) {
				loop :outer {
					if c { continue :outer; }
					break :outer;
				}
			}
		"});
		let label = a.value("break :outer", "outer");
		assert!(matches!(label, Referent::Label { .. }));
		assert_eq!(label, a.value("continue :outer", "outer"));
		assert_eq!(a.at("loop :outer", "outer", Tier::Value), None);
	}

	#[test]
	fn a_failed_path_retains_only_its_resolved_prefix() {
		let a = Analysis::new(indoc! {"
			mod m {}
			func f() {
				m::missing();
			}
		"});
		assert!(!a.errors.is_empty());
		assert!(matches!(
			a.at("m::missing", "m", Tier::Type),
			Some(Referent::Definition(_))
		));
		assert_eq!(a.at("m::missing", "missing", Tier::Value), None);
	}

	#[test]
	fn private_fields_are_resolved_even_when_access_is_rejected() {
		let a = Analysis::new(indoc! {"
			mod m {
				pub struct S(other: u32, value: u32);
			}
			func f(s: m::S) -> u32 {
				s.value
			}
		"});
		assert!(!a.errors.is_empty());
		assert_eq!(
			a.selection("s.value", "value"),
			Selection::Field {
				owner: a.struct_index("m::S"),
				field: FieldIdx::new(1),
			}
		);
	}

	#[test]
	fn pattern_shorthand_selects_a_field_and_keeps_the_local_declaration() {
		let a = Analysis::clean(indoc! {"
			struct S(value: u32);
			func f(s: S) -> u32 {
				local S({ value }) = s;
				value
			}
		"});
		let function = a.function_index("f");
		assert_eq!(
			a.selection("{ value }", "value"),
			Selection::Field {
				owner: a.struct_index("S"),
				field: FieldIdx::new(0),
			}
		);
		assert_eq!(
			a.value("\n\tvalue\n", "value"),
			Referent::Local {
				owner: BodyOwner::Function(function),
				local: LocalIdx::new(1),
			}
		);
		let declaration = &a.function_locals[usize::from(function)][1];
		assert_eq!(declaration.name.span, a.span("{ value }", "value"));
		assert_eq!(a.strings.resolve(declaration.name.inner), Some("value"));
	}

	#[test]
	fn associated_types_constants_and_qualified_calls_record_exact_declarations()
	 {
		let a = Analysis::clean(indoc! {"
			trait Tr: StackValue {
				type Value: StackValue;
				const COUNT: u32;
				func make(value: Self::Value) -> Self::Value;
			}
			func f<T: Tr>(value: T::Value) -> <T as Tr>::Value {
				local _ = T::COUNT;
				local _ = <T as Tr>::COUNT;
				<T as Tr>::make(value)
			}
		"});
		let parameter = Referent::TypeParam {
			env: a.function_envs[usize::from(a.function_index("f"))],
			index: 0,
		};
		for context in [
			"value: T::Value",
			"-> <T as Tr>::Value",
			"T::COUNT",
			"<T as Tr>::COUNT",
			"<T as Tr>::make",
		] {
			assert_eq!(a.at(context, "T", Tier::Type), Some(parameter));
		}
		for context in ["value: T::Value", "-> <T as Tr>::Value"] {
			assert_eq!(
				a.at(context, "Value", Tier::Type),
				Some(Referent::Member(a.trait_member(
					"Tr",
					"Value",
					Tier::Type
				)))
			);
		}
		for context in ["T::COUNT", "<T as Tr>::COUNT"] {
			assert_eq!(
				a.value(context, "COUNT"),
				Referent::Member(a.trait_member("Tr", "COUNT", Tier::Value))
			);
		}
		assert_eq!(
			a.value("<T as Tr>::make", "make"),
			Referent::Member(a.trait_member("Tr", "make", Tier::Value))
		);
		assert_eq!(
			a.at("<T as Tr>::make", "Tr", Tier::Type),
			Some(Referent::Definition(a.definition("Tr", Tier::Type)))
		);
	}

	#[test]
	fn self_types_and_receiver_values_keep_their_distinct_identities() {
		let a = Analysis::clean(indoc! {"
			trait Tr: StackValue {
				func id(self: Self) -> Self { self }
			}
			struct S();
			impl S {
				func make() -> Self { Self() }
			}
			impl Tr for S {
				func id(self: Self) -> Self { self }
			}
		"});
		let DefKind::Trait(trait_index) = a.resolve("Tr", Tier::Type) else {
			panic!()
		};
		assert_eq!(
			a.at("self: Self", "Self", Tier::Type),
			Some(Referent::TypeParam {
				env: a.trait_envs[usize::from(trait_index)],
				index: 0,
			})
		);
		let target = ImplTarget::Struct(a.struct_index("S"));
		let &[inherent] = a.impl_dispatch.inherent_candidates(target) else {
			panic!("expected one inherent impl")
		};
		assert_eq!(
			a.at("make() -> Self", "Self", Tier::Type),
			Some(Referent::InherentImplSelf(inherent))
		);
		assert_eq!(
			a.at("{ Self()", "Self", Tier::Value),
			Some(Referent::InherentImplSelf(inherent))
		);
		let &[(actual_trait, implementation)] =
			a.impl_dispatch.trait_candidates(target)
		else {
			panic!("expected one trait impl")
		};
		assert_eq!(actual_trait, trait_index);
		assert_eq!(
			a.at("impl Tr for S {\n\tfunc id(self: Self)", "Self", Tier::Type),
			Some(Referent::TraitImplSelf(implementation))
		);
		let MemberKind::Method(function) =
			a.trait_member("Tr", "id", Tier::Value)
		else {
			panic!()
		};
		assert_eq!(
			a.value("{ self }", "self"),
			Referent::Local {
				owner: BodyOwner::Function(function),
				local: LocalIdx::new(0),
			}
		);
	}

	#[test]
	fn imports_and_exports_record_source_names_not_external_names() {
		let a = Analysis::clean(indoc! {"
			mod m {
				pub func run() {}
			}
			use m::run as alias;
			func f() { alias(); }
			export alias as \"external\"
		"});
		let definition = a.definition("m::run", Tier::Value);
		assert_eq!(
			a.value("use m::run", "run"),
			Referent::Definition(definition)
		);
		let imported = a.value("alias();", "alias");
		let Referent::Import {
			definition: actual, ..
		} = imported
		else {
			panic!("expected an import")
		};
		assert_eq!(actual, definition);
		assert_eq!(a.value("export alias", "alias"), imported);
		assert_eq!(
			a.resolution("as \"external\"", "external", Tier::Value),
			None
		);
	}

	#[test]
	fn glob_imports_and_both_tiers_of_a_constructor_use_are_recorded() {
		let a = Analysis::clean(indoc! {"
			mod m {
				pub struct S();
				pub func run() {}
			}
			use m::S;
			use m::*;
			func f(s: S) -> S {
				run();
				S()
			}
		"});
		for tier in [Tier::Type, Tier::Value] {
			assert_eq!(
				a.at("use m::S", "S", tier),
				Some(Referent::Definition(a.definition("m::S", tier)))
			);
		}
		let imported = a.value("\n\tS()", "S");
		let Referent::Import { definition, .. } = imported else {
			panic!("expected a named import")
		};
		assert_eq!(definition, a.definition("m::S", Tier::Value));
		let Referent::Import { definition, .. } = a.value("run();", "run")
		else {
			panic!("expected a glob import")
		};
		assert_eq!(definition, a.definition("m::run", Tier::Value));
	}

	#[test]
	fn failed_members_keep_receivers_arguments_and_later_references() {
		let a = Analysis::new(indoc! {"
			struct S(value: u32);
			func f(s: S, x: u32) -> u32 {
				local _ = s.missing(x);
				local _ = s.missing({ value: x });
				local _ = s.absent;
				x
			}
		"});
		assert!(!a.errors.is_empty());
		let function = a.function_index("f");
		let receiver = Referent::Local {
			owner: BodyOwner::Function(function),
			local: LocalIdx::new(0),
		};
		let argument = Referent::Local {
			owner: BodyOwner::Function(function),
			local: LocalIdx::new(1),
		};
		assert_eq!(a.value("s.missing", "s"), receiver);
		assert_eq!(a.value("s.absent", "s"), receiver);
		assert_eq!(a.value("missing(x)", "x"), argument);
		assert_eq!(a.value("value: x", "x"), argument);
		assert_eq!(a.resolution("value: x", "value", Tier::Value), None);
		assert_eq!(a.value("\n\tx\n", "x"), argument);
		assert_eq!(a.resolution("s.missing", "missing", Tier::Value), None);
		assert_eq!(a.resolution("s.absent", "absent", Tier::Value), None);
	}

	#[test]
	fn invalid_arguments_preserve_successful_labels_and_value_references() {
		let a = Analysis::new(indoc! {"
			func take(x: u32, y: u32) {}
			func f(x: u32) -> u32 {
				take({ x, y: missing });
				x
			}
		"});
		assert!(!a.errors.is_empty());
		assert_eq!(
			a.resolution("{ x,", "x", Tier::Value),
			Some(Resolution::Shorthand {
				selection: Selection::Parameter {
					function: a.function_index("take"),
					parameter: ParamIdx::new(0)
				},
				value: Referent::Local {
					owner: BodyOwner::Function(a.function_index("f")),
					local: LocalIdx::new(0)
				},
			})
		);
		assert_eq!(
			a.selection("y: missing", "y"),
			Selection::Parameter {
				function: a.function_index("take"),
				parameter: ParamIdx::new(1)
			}
		);
		assert_eq!(a.resolution("y: missing", "missing", Tier::Value), None);
		assert_eq!(
			a.value("\n\tx\n", "x"),
			Referent::Local {
				owner: BodyOwner::Function(a.function_index("f")),
				local: LocalIdx::new(0)
			}
		);
	}

	#[test]
	fn unresolved_calls_still_record_positional_and_named_argument_values() {
		let a = Analysis::new(indoc! {"
			struct S();
			func f(x: u32) -> u32 {
				missing(x);
				S::absent({ x });
				<Missing>::absent({ value: x });
				x
			}
		"});
		assert!(!a.errors.is_empty());
		let expected = Referent::Local {
			owner: BodyOwner::Function(a.function_index("f")),
			local: LocalIdx::new(0),
		};
		for context in ["missing(x)", "{ x }", "value: x", "\n\tx\n"] {
			assert_eq!(a.value(context, "x"), expected);
		}
		assert_eq!(a.resolution("value: x", "value", Tier::Value), None);
	}

	#[test]
	fn import_block_uses_and_imported_function_calls_record_each_name() {
		let a = Analysis::clean(indoc! {r#"
			mod types {
				pub struct S();
			}
			import "host" as host {
				use super::types::S;
				func run(value: S);
			}
			func f(value: types::S) {
				host::run(value);
			}
		"#});
		assert_eq!(
			a.at("super::types::S", "types", Tier::Type),
			Some(Referent::Definition(a.definition("types", Tier::Type)))
		);
		assert_eq!(
			a.at("super::types::S", "S", Tier::Type),
			Some(Referent::Definition(a.definition("types::S", Tier::Type)))
		);
		assert_eq!(
			a.at("host::run", "host", Tier::Type),
			Some(Referent::Definition(a.definition("host", Tier::Type)))
		);
		assert_eq!(
			a.value("host::run", "run"),
			Referent::Definition(a.definition("host::run", Tier::Value))
		);
		assert_eq!(
			a.value("run(value)", "value"),
			Referent::Local {
				owner: BodyOwner::Function(a.function_index("f")),
				local: LocalIdx::new(0),
			}
		);
	}

	#[test]
	fn constant_patterns_record_the_constant_and_enum_path_segments() {
		let a = Analysis::clean(indoc! {"
			const LIMIT: u32 = 1;
			enum E(u8) { A = 0, B = 1 }
			func f(x: u32) -> u32 {
				match x { const LIMIT => 1, _ => 0 }
			}
			func g(x: E) -> u32 {
				match x { E::A => 1, _ => 0 }
			}
		"});
		assert_eq!(
			a.value("const LIMIT =>", "LIMIT"),
			Referent::Definition(a.definition("LIMIT", Tier::Value))
		);
		assert_eq!(
			a.at("E::A =>", "E", Tier::Type),
			Some(Referent::Definition(a.definition("E", Tier::Type)))
		);
		assert_eq!(
			a.value("E::A =>", "A"),
			Referent::Definition(a.definition("E::A", Tier::Value))
		);
	}
}
