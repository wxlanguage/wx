use indoc::indoc;

use super::*;
use crate::diagnostics::DiagnosticCode;
use crate::testing::DiagnosticView;
use crate::vfs::{FileOrigin, Files};

/// A single parsed file, kept together with the [`Files`] its spans point
/// into so diagnostics can be rendered with source context.
///
/// Parser tests deliberately skip the package machinery — no stdlib, no
/// `CompilationUnit` — because nothing here needs it, and every extra stage
/// would be another way for a test to fail for reasons it is not about.
struct TestCase {
	strings: StringInterner,
	files: Files,
	ast: AST,
}

impl TestCase {
	fn new(source: &str) -> Self {
		// Keywords pre-interned, as every compilation's interner is: the
		// parser names some by `Keyword::symbol` (`self` alone is `self:
		// Self`).
		let mut strings = Keyword::create_interner();
		let mut files = Files::new();
		let file_id = files
			.add("main.wx".to_string(), source.to_string(), FileOrigin::Local)
			.unwrap();
		let ast = Parser::parse(file_id, &files, &mut strings);
		TestCase {
			strings,
			files,
			ast,
		}
	}

	/// Everything the parser reported. See [`DiagnosticView`] for the
	/// assertions; prefer them over poking at `ast.diagnostics` directly, since
	/// they render the offending source when they fail.
	fn diagnostics(&self) -> DiagnosticView<'_> {
		DiagnosticView::new("parse", &self.ast.diagnostics, &self.files)
	}

	/// Resolves an interned symbol, so assertions can name things rather than
	/// compare opaque `SymbolU32` integers (which is all a snapshot shows).
	fn name(&self, symbol: SymbolU32) -> &str {
		self.strings
			.resolve(symbol)
			.expect("symbol was interned by this parse")
	}

	/// The signature of the function item at `index`.
	fn function_signature(&self, index: usize) -> &FunctionSignature {
		let Item::Function { signature, .. } = self.item(index) else {
			panic!(
				"item {index} is {}, not a function",
				item_kind(self.item(index))
			)
		};

		signature
	}

	/// Renders an expression as a compact S-expression: `a + b * c` becomes
	/// `(+ a (* b c))`.
	///
	/// Precedence and associativity are claims about *tree shape*, and a
	/// nest of `matches!` states that shape far less clearly than the shape
	/// itself does. Only the node kinds those tests need are rendered;
	/// anything else falls back to its variant name, which is enough to make
	/// a mismatch obvious.
	fn shape(&self, expr: &Expression) -> String {
		match expr {
			Expression::Binary {
				operator,
				left,
				right,
			} => format!(
				"({} {} {})",
				operator.inner,
				self.shape(&left.inner),
				self.shape(&right.inner)
			),
			// `u` prefix keeps unary `-` distinguishable from binary `-`
			Expression::Unary { operator, operand } => {
				format!("(u{} {})", operator.inner, self.shape(&operand.inner))
			}
			Expression::Path(segments) => segments
				.iter()
				.map(|segment| self.name(segment.ident.inner))
				.collect::<Vec<_>>()
				.join("::"),
			Expression::Int { value } => value.to_string(),
			other => format!("<{}>", expression_kind(other)),
		}
	}

	/// A pattern as an S-expression that names every node, so what each
	/// term is visible: a binding is `x`, a constant is `(const x)`, a
	/// qualified path is `(value Ordering::Less)`.
	fn pattern(&self, pattern: &Pattern) -> String {
		match pattern {
			Pattern::Wildcard => "_".to_string(),
			Pattern::Binding { mut_span, name } => match mut_span {
				Some(_) => format!("mut {}", self.name(name.inner)),
				None => self.name(name.inner).to_string(),
			},
			Pattern::Constant { path } => match &**path {
				[segment] if segment.type_args.is_empty() => {
					format!("(const {})", self.name(segment.ident.inner))
				}
				_ => format!("(const {})", self.path(path)),
			},
			Pattern::Literal(PatternLiteral::Int(value)) => value.to_string(),
			Pattern::Literal(PatternLiteral::NegInt(value)) => {
				format!("-{value}")
			}
			Pattern::Literal(PatternLiteral::Char) => "char".to_string(),
			Pattern::Literal(PatternLiteral::Float) => "float".to_string(),
			Pattern::Literal(PatternLiteral::String) => "string".to_string(),
			Pattern::Literal(PatternLiteral::Bool(value)) => value.to_string(),
			Pattern::Or(alternatives) => {
				let alternatives = alternatives
					.iter()
					.map(|alternative| self.pattern(&alternative.inner.inner))
					.collect::<Vec<_>>();
				format!("(| {})", alternatives.join(" "))
			}
			Pattern::Destructure(destructure) => self.destructure(destructure),
			Pattern::Error => "<error>".to_string(),
		}
	}

	fn destructure(&self, destructure: &Destructure) -> String {
		let elements = |elements: &PatternElements| {
			elements
				.iter()
				.map(|element| match &element.inner.inner {
					PatternElement::Pattern(pattern) => self.pattern(pattern),
					PatternElement::Rest => "..".to_string(),
				})
				.collect::<Vec<_>>()
		};
		match destructure {
			Destructure::Tuple { elements: items } => {
				let mut parts = vec!["tuple".to_string()];
				parts.extend(elements(items));
				format!("({})", parts.join(" "))
			}
			Destructure::Struct {
				path,
				elements: items,
			} => {
				let mut parts = vec![self.path(path)];
				parts.extend(elements(items));
				format!("({})", parts.join(" "))
			}
			Destructure::NamedStruct { path, fields } => {
				let fields = fields
					.iter()
					.map(|item| match &item.inner.inner {
						PatternFieldItem::Field(field) => {
							match &field.pattern {
								Some(pattern) => format!(
									"{}: {}",
									self.name(field.name.inner),
									self.pattern(&pattern.inner)
								),
								None => self.name(field.name.inner).to_string(),
							}
						}
						PatternFieldItem::Rest => "..".to_string(),
					})
					.collect::<Vec<_>>();
				format!("({} {{ {} }})", self.path(path), fields.join(", "))
			}
		}
	}

	fn path(&self, path: &[PathSegment]) -> String {
		path.iter()
			.map(|segment| self.name(segment.ident.inner))
			.collect::<Vec<_>>()
			.join("::")
	}

	/// Every `local` pattern in function `index`, rendered.
	fn local_patterns(&self, index: usize) -> Vec<String> {
		self.function_block(index)
			.iter()
			.filter_map(|statement| match &statement.inner.inner {
				Statement::LocalDefinition { pattern, .. } => {
					Some(self.pattern(&pattern.inner))
				}
				Statement::Expression(_) => None,
			})
			.collect()
	}

	/// Every arm pattern of the match that is function `index`'s first
	/// statement, rendered.
	fn arm_patterns(&self, index: usize) -> Vec<String> {
		let Expression::Match { arms, .. } =
			statement_expression(self.function_block(index), 0)
		else {
			panic!("expected a match")
		};
		arms.iter()
			.map(|arm| self.pattern(&arm.inner.inner.pattern.inner))
			.collect()
	}

	fn item(&self, index: usize) -> &Item {
		&self.ast.items[index].inner.inner
	}

	fn function_block(&self, index: usize) -> &[Separated<Spanned<Statement>>] {
		let Item::Function { block, .. } = self.item(index) else {
			panic!(
				"item {index} is {}, not a function",
				item_kind(self.item(index))
			)
		};

		block.inner.as_block_statements()
	}

	fn struct_fields(
		&self,
		index: usize,
	) -> &[Separated<Spanned<StructField>>] {
		let Item::Struct { fields, .. } = self.item(index) else {
			panic!(
				"item {index} is {}, not a struct",
				item_kind(self.item(index))
			)
		};

		fields
	}
}

/// Parses `expression` as the whole body of a function and renders its shape.
/// See [`TestCase::shape`].
fn shape_of(expression: &str) -> String {
	let case = TestCase::new(&format!("func f() {{ {expression} }}"));
	case.diagnostics().assert_none();
	case.shape(statement_expression(case.function_block(0), 0))
}

/// Fallback naming for [`TestCase::shape`] — just enough to identify an
/// unexpected node without depending on `Debug`.
fn expression_kind(expression: &Expression) -> &'static str {
	match expression {
		Expression::Call { .. } => "call",
		Expression::NamedCall { .. } => "named-call",
		Expression::MethodCall(_) => "method-call",
		Expression::NamedMethodCall(_) => "named-method-call",
		Expression::ObjectAccess { .. } => "field",
		Expression::Tuple { .. } => "tuple",
		Expression::Cast { .. } => "cast",
		Expression::Float { .. } => "float",
		Expression::Char => "char",
		Expression::String => "string",
		Expression::Placeholder => "placeholder",
		Expression::Error => "error",
		_ => "other",
	}
}

/// Names an item variant, so a failed destructure says what was actually
/// parsed instead of only what was wanted.
fn item_kind(item: &Item) -> &'static str {
	match item {
		Item::Function { .. } => "a function",
		Item::FunctionDeclaration { .. } => "a function declaration",
		Item::Global { .. } => "a global",
		Item::Export { .. } => "an export",
		Item::ExportBlock { .. } => "an export block",
		Item::Import { .. } => "an import block",
		Item::Enum { .. } => "an enum",
		Item::InherentImpl { .. } => "an inherent impl",
		Item::TraitImpl { .. } => "a trait impl",
		Item::Struct { .. } => "a struct",
		Item::Memory { .. } => "a memory",
		Item::Const { .. } => "a const",
		Item::Module { .. } => "an inline module",
		Item::ModuleDeclaration { .. } => "a module declaration",
		Item::PackageInstance { .. } => "a package instance",
		Item::Trait { .. } => "a trait",
		Item::TypeSet { .. } => "a typeset",
		Item::Use { .. } => "a use",
		Item::TypeAlias { .. } => "a type alias",
	}
}

fn statement_expression(
	statements: &[Separated<Spanned<Statement>>],
	index: usize,
) -> &Expression {
	let Statement::Expression(expr) = &statements[index].inner.inner else {
		panic!("expected expression statement")
	};

	&expr.inner
}

fn local_definition_value(
	statements: &[Separated<Spanned<Statement>>],
	index: usize,
) -> &Expression {
	let Statement::LocalDefinition { value, .. } =
		&statements[index].inner.inner
	else {
		panic!("expected local definition")
	};

	&value.inner
}

fn local_definition_pattern(
	statements: &[Separated<Spanned<Statement>>],
	index: usize,
) -> &Pattern {
	let Statement::LocalDefinition { pattern, .. } =
		&statements[index].inner.inner
	else {
		panic!("expected local definition")
	};

	&pattern.inner
}

// ── Top-level items ──────────────────────────────────────────────────────────

#[test]
fn test_top_level_items() {
	let case = TestCase::new(indoc! {"
        func add(a: i32, b: i32) -> i32 {
            a + b
        }

        memory MEM: u32;
        global mut counter: i32 = 0;
        const MAX: i32 = 100;

        struct Point(
            pub x: i32,
            y: i32,
        );

        import \"env\" as env {
            func log(message: string)
        }

        enum Color {
            Red,
            Green = 1,
            Blue,
        }
    "});
	insta::assert_yaml_snapshot!(case.ast);
}

#[test]
fn test_enum_repr_after_name() {
	let case = TestCase::new(indoc! {"
        enum Status: i32 {
            Foo,
            Bar,
        }
    "});

	case.diagnostics().assert_none();

	let Item::Enum {
		repr,
		name,
		variants,
		..
	} = case.item(0)
	else {
		panic!("expected enum item")
	};

	assert_eq!(case.strings.resolve(name.inner), Some("Status"));
	assert!(matches!(
		repr.as_deref().map(|repr| &repr.inner),
		Some(TypeExpression::Path(p))
			if p.len() == 1
				&& case.strings.resolve(p[0].ident.inner) == Some("i32")
	));
	assert_eq!(variants.len(), 2);
}

#[test]
fn test_function_mut_param() {
	// mut on a parameter; mut local with compound assignment
	let case = TestCase::new(indoc! {"
        func sum_down(mut n: i32) -> i32 {
            local mut acc: i32 = 0;
            acc += n;
            acc
        }
    "});
	case.diagnostics().assert_none();

	let param = &case.function_signature(0).params[0].inner.inner;
	let Some(Binding::Name { mut_span, name }) = param.binding else {
		panic!("`n` is named")
	};
	assert_eq!(case.name(name.inner), "n");
	assert!(mut_span.is_some(), "`mut n` should record a mut span");

	// `mut` on a local lives on its binding pattern, not on the statement
	let statements = case.function_block(0);
	let Pattern::Binding { mut_span, name } =
		local_definition_pattern(statements, 0)
	else {
		panic!("expected a binding pattern")
	};
	assert_eq!(case.name(name.inner), "acc");
	assert!(
		mut_span.is_some(),
		"`local mut acc` should record a mut span"
	);
}

#[test]
fn test_fn_pointer_param() {
	// func(…) -> … as a parameter type
	let case = TestCase::new(indoc! {"
        func apply(f: func(i32) -> i32, x: i32) -> i32 {
            f(x)
        }
    "});
	case.diagnostics().assert_none();

	let param = &case.function_signature(0).params[0].inner.inner;
	let ty = &param.ty.inner;
	let TypeExpression::Function { params, result } = ty else {
		panic!("expected a function type, got {ty:?}")
	};
	assert_eq!(params.len(), 1);
	assert!(result.is_some(), "`-> i32` should be recorded");
}

#[test]
fn test_type_expression_forms() {
	let case = TestCase::new(indoc! {"
        struct TypeForms(
            ptr: *u8,
            slice: &[u8],
            array: &[u8; 4],
            tuple: (i32, u32),
            namespaced: math::Number,
        );
    "});

	case.diagnostics().assert_none();
	let Item::Struct { fields, .. } = case.item(0) else {
		panic!("expected struct item")
	};

	assert!(matches!(
		Some(&fields[0].inner.inner.ty.inner),
		Some(TypeExpression::Pointer { .. })
	));
	assert!(matches!(
		Some(&fields[1].inner.inner.ty.inner),
		Some(TypeExpression::Slice { .. })
	));
	assert!(matches!(
		Some(&fields[2].inner.inner.ty.inner),
		Some(TypeExpression::Array {
			size: Spanned { inner: 4, .. },
			..
		})
	));
	assert!(matches!(
		Some(&fields[3].inner.inner.ty.inner),
		Some(TypeExpression::Tuple { elements }) if elements.len() == 2
	));
	assert!(matches!(
		Some(&fields[4].inner.inner.ty.inner),
		Some(TypeExpression::Path(p)) if p.len() == 2
	));
}

#[test]
fn test_impl() {
	// impl block with an attribute and a pub method
	let case = TestCase::new(indoc! {"
        impl i32 {
            #[inline]
            pub func double(self: Self) -> i32 {
                self * 2
            }
        }
    "});
	case.diagnostics().assert_none();

	let Item::InherentImpl { items, .. } = case.item(0) else {
		panic!("item 0 is {}, not an impl", item_kind(case.item(0)))
	};
	assert_eq!(items.len(), 1);
	let ImplItem::Function {
		pub_span,
		attributes,
		signature,
		..
	} = &items[0].inner.inner
	else {
		panic!("expected a method")
	};
	assert_eq!(case.name(signature.name.inner), "double");
	assert!(pub_span.is_some(), "`pub func` should record a pub span");
	assert_eq!(attributes.len(), 1);
	assert_eq!(case.name(attributes[0].name.inner), "inline");
}

#[test]
fn test_impl_trait_for_type() {
	// impl Trait for Type — trait implementation block
	let case = TestCase::new(indoc! {"
        impl Drawable for Point {
            func draw(self: Self) {
                draw_point(self.x, self.y)
            }
        }
    "});
	case.diagnostics().assert_none();

	let Item::TraitImpl {
		trait_name,
		target,
		items,
		..
	} = case.item(0)
	else {
		panic!("item 0 is {}, not a trait impl", item_kind(case.item(0)))
	};
	assert_eq!(trait_name.segments.len(), 1);
	assert_eq!(case.name(trait_name.segments[0].ident.inner), "Drawable");
	assert_eq!(case.name(target.segments[0].ident.inner), "Point");
	assert_eq!(items.len(), 1);
}

#[test]
fn test_impl_placeholder_is_rejected_by_parser() {
	let case = TestCase::new("impl _ {}");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::ReservedIdentifier]);
}

#[test]
fn test_impl_target_must_be_a_path() {
	let case = TestCase::new("impl (Point) {}");
	assert_eq!(
		case.ast.diagnostics[0].code.as_deref(),
		Some(DiagnosticCode::UnexpectedToken.code())
	);
}

#[test]
fn test_typeset_member_must_be_a_path() {
	let case = TestCase::new("typeset Bad { (i32, i32) }");
	assert_eq!(
		case.ast.diagnostics[0].code.as_deref(),
		Some(DiagnosticCode::UnexpectedToken.code())
	);
}

#[test]
fn test_trait_items() {
	let case = TestCase::new(indoc! {"
        trait Widget: Drawable + Sized {
            const SIZE: u32;

            func render(self: Self);

            #[inline]
            func grow(self: Self, delta: u32) -> u32 {
                delta
            }
        }
    "});
	case.diagnostics().assert_none();

	let Item::Trait {
		name,
		supertraits,
		items,
		..
	} = case.item(0)
	else {
		panic!("item 0 is {}, not a trait", item_kind(case.item(0)))
	};
	assert_eq!(case.name(name.inner), "Widget");
	assert!(
		supertraits.is_some(),
		"`: Drawable + Sized` should be recorded"
	);
	assert_eq!(items.len(), 3);

	let TraitItem::Const { name, .. } = &items[0].inner.inner else {
		panic!("expected an associated const")
	};
	assert_eq!(case.name(name.inner), "SIZE");

	// `render` is abstract, `grow` carries a default body
	let TraitItem::Function {
		signature, body, ..
	} = &items[1].inner.inner
	else {
		panic!("expected a trait method")
	};
	assert_eq!(case.name(signature.name.inner), "render");
	assert!(
		body.is_none(),
		"`func render(self: Self);` has no default body"
	);

	let TraitItem::Function {
		signature,
		body,
		attributes,
		..
	} = &items[2].inner.inner
	else {
		panic!("expected a trait method")
	};
	assert_eq!(case.name(signature.name.inner), "grow");
	assert!(body.is_some(), "`grow` has a default body");
	assert_eq!(attributes.len(), 1);
}

#[test]
fn test_pub_not_permitted_in_trait_items() {
	let case = TestCase::new(indoc! {"
        trait Widget {
            pub const SIZE: u32;
            pub type Assoc;
            pub func render(self: Self);
        }
    "});

	case.diagnostics().assert_codes(&[
		DiagnosticCode::VisibilityNotPermitted,
		DiagnosticCode::VisibilityNotPermitted,
		DiagnosticCode::VisibilityNotPermitted,
	]);
	let Item::Trait { items, .. } = case.item(0) else {
		panic!("expected trait item")
	};
	assert_eq!(items.len(), 3);
}

#[test]
fn test_pub_not_permitted_in_trait_impl_items() {
	// The inherent-impl counterpart below keeps its `pub`: the same member
	// parser produces both, so the qualifier is judged by the impl, not by
	// the member.
	let case = TestCase::new(indoc! {"
        impl Widget for Button {
            pub const SIZE: u32 = 1;
            pub type Assoc = u32;
            pub func render(self: Self) {}
        }

        impl Button {
            pub func area(self: Self) -> u32 { 1 }
        }
    "});

	case.diagnostics().assert_codes(&[
		DiagnosticCode::VisibilityNotPermitted,
		DiagnosticCode::VisibilityNotPermitted,
		DiagnosticCode::VisibilityNotPermitted,
	]);
	let Item::TraitImpl { items, .. } = case.item(0) else {
		panic!("expected trait impl item")
	};
	assert_eq!(items.len(), 3);
}

/// The `pub` has to survive parsing even where it is an error, or the
/// formatter — which rebuilds source from the AST alone — deletes it.
#[test]
fn test_pub_on_impl_assoc_type_is_recorded() {
	let case = TestCase::new(indoc! {"
        impl Widget for Button {
            pub type Assoc = u32;
        }
    "});

	let Item::TraitImpl { items, .. } = case.item(0) else {
		panic!("expected trait impl item")
	};
	let ImplItem::AssocType { pub_span, .. } = &items[0].inner.inner else {
		panic!("expected an associated type")
	};
	assert!(pub_span.is_some());
}

#[test]
fn test_pub_memory_and_global_record_pub_span() {
	let case = TestCase::new(indoc! {"
        pub memory MEM: u32;
        pub global mut G: u32 = 0;
        memory PRIVATE: u32;
    "});

	case.diagnostics().assert_none();
	let Item::Memory { pub_span, .. } = case.item(0) else {
		panic!("item 0 is {}, not a memory", item_kind(case.item(0)))
	};
	assert!(pub_span.is_some());
	let Item::Global { pub_span, .. } = case.item(1) else {
		panic!("item 1 is {}, not a global", item_kind(case.item(1)))
	};
	assert!(pub_span.is_some());
	let Item::Memory { pub_span, .. } = case.item(2) else {
		panic!("item 2 is {}, not a memory", item_kind(case.item(2)))
	};
	assert!(pub_span.is_none());
}

#[test]
fn test_bare_glob_with_no_path_reports_unexpected_token() {
	// `*` needs at least one namespace segment before it — `parse_use_tree`
	// always parses an identifier first, so a lone `*` right after `use`
	// (or `pub use`) is a plain parse error, not a valid "glob the current
	// scope" form.
	let case = TestCase::new(indoc! {"
        use *;
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::UnexpectedToken]);
}

#[test]
fn test_pub_use_reexports_without_diagnostic() {
	let case = TestCase::new(indoc! {"
        pub use foo::*;
    "});

	case.diagnostics().assert_none();
	let Item::Use { pub_span, .. } = case.item(0) else {
		panic!("expected use item")
	};
	assert!(pub_span.is_some());
}

/// Every `use` form the grammar accepts, in one snapshot — the tree shape
/// is the part worth pinning, since resolution reads it structurally.
#[test]
fn test_use_tree_forms() {
	let case = TestCase::new(indoc! {"
        use math::*;
        use math::add;
        use math::add as plus;
        use math::{add, sub};
        use math::{trig::{sin, cos}, ops::*};
        use a::b::c::d;
    "});

	case.diagnostics().assert_none();
	insta::assert_yaml_snapshot!(case.ast);
}

#[test]
fn test_export_alias() {
	let case = TestCase::new(indoc! {"
        func add(a: i32, b: i32) -> i32 { a + b }
        export { add as \"wasm_add\" }
    "});
	case.diagnostics().assert_none();

	let Item::ExportBlock { entries, .. } = case.item(1) else {
		panic!("item 1 is {}, not an export block", item_kind(case.item(1)))
	};
	assert_eq!(entries.len(), 1);
	let entry = &entries[0].inner.inner;
	assert_eq!(case.name(entry.name.inner), "add");
	let alias = entry
		.alias
		.expect("`as \"wasm_add\"` should record an alias");
	assert_eq!(
		alias.extract_str(&case.files.get(case.ast.file_id).unwrap().source),
		r#""wasm_add""#
	);
}

#[test]
fn single_exports_preserve_raw_aliases_and_use_item_separators() {
	let source = indoc! {"
        export foo
        export foo;
        export foo as \"line\\n\"
        export foo as \"line\\n\";

        func foo() {
        }
    "};
	let case = TestCase::new(source);
	case.diagnostics().assert_none();
	assert_eq!(case.ast.items.len(), 5);
	assert!(case.strings.get("line\n").is_none());

	for index in 0..4 {
		let item = &case.ast.items[index];
		let Item::Export { entry } = &item.inner.inner else {
			panic!("expected single export");
		};
		assert_eq!(case.name(entry.inner.name.inner), "foo");
		assert_eq!(item.separator.is_some(), index % 2 == 1);
		if index < 2 {
			assert!(entry.inner.alias.is_none());
			assert_eq!(entry.span.extract_str(source), "foo");
			assert_eq!(item.inner.span.extract_str(source), "export foo");
		} else {
			assert_eq!(
				entry.inner.alias.unwrap().extract_str(source),
				"\"line\\n\""
			);
			assert_eq!(entry.span.extract_str(source), "foo as \"line\\n\"");
			assert_eq!(
				item.inner.span.extract_str(source),
				"export foo as \"line\\n\""
			);
		}
	}
	assert!(matches!(case.item(4), Item::Function { .. }));
}

// ── Expressions ──────────────────────────────────────────────────────────────

#[test]
fn test_literals() {
	// float, char, and string literals (int is covered everywhere else)
	let case = TestCase::new(indoc! {"
        func f() {
            local a = 2.75;
            local b = 'z';
            local c = \"hello\";
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	assert!(
		matches!(local_definition_value(statements, 0), Expression::Float),
		"expected a float literal"
	);
	// Literal contents are recovered from spans and interpreted in TIR.
	assert!(matches!(
		local_definition_value(statements, 1),
		Expression::Char
	));
	assert!(matches!(
		local_definition_value(statements, 2),
		Expression::String
	));
}

#[test]
fn test_if_else() {
	let case = TestCase::new(indoc! {"
        func sign(x: i32) -> i32 {
            if x > 0 {
                1
            } else {
                0
            }
        }
    "});
	case.diagnostics().assert_none();

	let statements = case.function_block(0);
	let Expression::IfElse {
		condition,
		then_block,
		else_block,
	} = statement_expression(statements, 0)
	else {
		panic!("expected an if/else")
	};
	assert!(matches!(condition.inner, Expression::Binary { .. }));
	assert!(matches!(then_block.inner, Expression::Block { .. }));
	let else_block = else_block.as_ref().expect("`else` should be recorded");
	assert!(matches!(else_block.inner, Expression::Block { .. }));
}

#[test]
fn test_match_int_literal_patterns() {
	let case = TestCase::new(indoc! {"
        func sign(x: i32) -> i32 {
            match x {
                0 -> { 0 },
                1 | 2 -> { 1 },
                _ -> { -1 },
            }
        }
    "});
	case.diagnostics().assert_none();

	let statements = case.function_block(0);
	let Expression::Match { scrutinee, .. } =
		statement_expression(statements, 0)
	else {
		panic!("expected a match")
	};
	assert!(matches!(scrutinee.inner, Expression::Path(_)));
	assert_eq!(case.arm_patterns(0), ["0", "(| 1 2)", "_"]);
}

#[test]
fn test_match_enum_variant_patterns() {
	let case = TestCase::new(indoc! {"
        enum FileDescriptor: u8 {
            StdIn,
            StdOut,
            StdErr,
        }

        func name(fd: FileDescriptor) -> u8 {
            match fd {
                FileDescriptor::StdIn -> { 0 },
                FileDescriptor::StdOut -> { 1 },
                FileDescriptor::StdErr -> { 2 },
            }
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(
		case.arm_patterns(1),
		[
			"(const FileDescriptor::StdIn)",
			"(const FileDescriptor::StdOut)",
			"(const FileDescriptor::StdErr)",
		]
	);
}

#[test]
fn test_match_missing_arrow_recovers_with_diagnostic() {
	// The missing `->` itself is reported as E0002. `SeparatedGroup`'s
	// recovery matches the arm list's closing brace by token *kind*, not
	// nesting depth, so it mistakes `{ 1 }`'s own `}` for the match's
	// closing brace here — a pre-existing characteristic of recovery
	// shared by every brace-delimited construct in this parser, not
	// specific to `match` — which cascades into a second diagnostic
	// (E0009) while re-syncing at the enclosing item boundary.
	let case = TestCase::new(indoc! {"
        func f(x: i32) -> i32 {
            match x {
                0 { 1 },
                _ -> { 0 },
            }
        }
    "});
	case.diagnostics().assert_codes(&[
		DiagnosticCode::UnexpectedToken,
		DiagnosticCode::InvalidItem,
	]);
}

#[test]
fn test_loop_break_label() {
	// labeled loop, break with label and a value, continue
	let case = TestCase::new(indoc! {"
        func first_positive(mut n: i32) -> i32 {
            result: loop {
                if n > 0 {
                    break :result n;
                }
                n += 1;
                continue;
            }
        }
    "});
	case.diagnostics().assert_none();

	// the label wraps the loop, rather than the loop carrying a label field
	let statements = case.function_block(0);
	let Expression::Label { label, block } =
		statement_expression(statements, 0)
	else {
		panic!("expected a labelled expression")
	};
	assert_eq!(case.name(label.inner), "result");
	let Expression::Loop { block } = &block.inner else {
		panic!("expected a loop inside the label")
	};
	let Expression::Block { statements } = &block.inner else {
		panic!("expected a block as the loop body")
	};

	// `break :result n` carries both a label and a value
	let Expression::IfElse { then_block, .. } =
		statement_expression(statements, 0)
	else {
		panic!("expected an if")
	};
	let Expression::Block { statements: body } = &then_block.inner else {
		panic!("expected a block")
	};
	let Expression::Break { label, value } = statement_expression(body, 0)
	else {
		panic!("expected a break")
	};
	assert_eq!(
		case.name(label.expect("`break :result` should record a label").inner),
		"result"
	);
	assert!(value.is_some(), "`break :result n` should record a value");

	assert!(matches!(
		statement_expression(statements, 2),
		Expression::Continue { .. }
	));
}

#[test]
fn test_label_requires_block_like_expression() {
	let case = TestCase::new(indoc! {"
        func f(value: i32) {
            target: value
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::IncompleteExpression]);
	assert!(case.function_block(0).is_empty());
}

#[test]
fn test_multi_segment_label_reports_diagnostic_instead_of_panicking() {
	// A partially-typed namespace access (`std::io` followed by a lone `:`
	// while typing the second `::`) parses as a multi-segment path immediately
	// followed by a colon, which used to hit `unreachable!()` in
	// `parse_labelled_expression`.
	let case = TestCase::new(indoc! {"
        func f() {
            std::io:
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidLabel]);
}

/// A named call's path callee and arguments.
fn named_call(
	expression: &Expression,
) -> (&[PathSegment], &[Separated<Spanned<NamedArgument>>]) {
	let Expression::NamedCall { callee, arguments } = expression else {
		panic!(
			"expected a named call, found {}",
			expression_kind(expression)
		)
	};
	let Expression::Path(path) = &callee.inner else {
		panic!("expected a path callee")
	};
	(path, arguments)
}

#[test]
fn test_named_call() {
	// explicit names, shorthand ({ x } == { x: x }), an empty named list, and
	// a struct constructed by position
	let case = TestCase::new(indoc! {"
        func make(x: i32, y: i32) {
            local full  = Point({ x: x, y: y });
            local short = Point({ x, y });
            local empty = f({});
            local unit  = Unit();
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);
	let call =
		|index: usize| named_call(local_definition_value(statements, index));

	// explicit `x: x` records a value; shorthand `x` leaves it `None`
	let (path, explicit) = call(0);
	assert_eq!(case.name(path[0].ident.inner), "Point");
	assert!(explicit.iter().all(|f| f.inner.inner.value.is_some()));

	let (_, shorthand) = call(1);
	assert!(
		shorthand.iter().all(|f| f.inner.inner.value.is_none()),
		"`Point({{ x, y }})` is shorthand, so no explicit values"
	);
	let names: Vec<&str> = shorthand
		.iter()
		.map(|f| case.name(f.inner.inner.name.inner))
		.collect();
	assert_eq!(names, ["x", "y"]);

	assert!(call(2).1.is_empty());
	// No arguments at all is the positional form.
	assert!(matches!(
		local_definition_value(statements, 3),
		Expression::Call { arguments, .. } if arguments.is_empty()
	));
}

#[test]
fn test_named_method_call_and_turbofish() {
	let case = TestCase::new(indoc! {"
        func make(x: f32, y: f32, o: Obj) {
            local p = Point::<f32>({ x: x, y: y });
            o.move_to({ x, y });
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);
	let (path, arguments) = named_call(local_definition_value(stmts, 0));
	// the turbofish binds to the final segment: `Point::<f32>`
	assert_eq!(path.len(), 1);
	assert_eq!(path[0].type_args.len(), 1);
	assert_eq!(arguments.len(), 2);

	let Expression::NamedMethodCall(call) = statement_expression(stmts, 1)
	else {
		panic!("expected a named method call")
	};
	assert_eq!(case.name(call.method.ident.inner), "move_to");
	assert_eq!(call.arguments.len(), 2);
}

#[test]
fn a_receiver_is_given_by_name_as_self() {
	// `self` names a method's receiver; any other keyword is no name.
	let case = TestCase::new(indoc! {"
        func f(s: S) {
            S::m({ self: s, n: 1 });
            S::m({ self });
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);
	for index in 0..2 {
		let (_, arguments) = named_call(statement_expression(stmts, index));
		assert_eq!(case.name(arguments[0].inner.inner.name.inner), "self");
	}

	let case = TestCase::new("func f() { g({ loop: 1 }); }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::ReservedIdentifier]);
}

#[test]
fn named_and_positional_arguments_do_not_mix() {
	for source in [
		"func f() { g({ a: 1 }, 2); }",
		"func f() { g(1, { a: 2 }); }",
		"func f() { o.m(1, { a: 2 }); }",
	] {
		let case = TestCase::new(source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::MixedCallArguments]);
	}
}

#[test]
fn a_plain_block_is_written_with_its_keyword() {
	let case = TestCase::new(indoc! {"
        func f() -> i32 {
            local x = block { 1 };
            block { x; }
            outer: block { break :outer; }
            if true { x } else { 2 }
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);
	assert!(matches!(
		local_definition_value(statements, 0),
		Expression::Block { .. }
	));
	assert!(matches!(
		statement_expression(statements, 1),
		Expression::Block { .. }
	));
	assert!(matches!(
		statement_expression(statements, 2),
		Expression::Label { .. }
	));

	// Without the keyword, `{` is reported and still read as a block.
	let case = TestCase::new("func f() { local x = { 1 }; }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::BlockNeedsKeyword]);
	assert!(matches!(
		local_definition_value(case.function_block(0), 0),
		Expression::Block { .. }
	));
}

#[test]
fn old_struct_forms_are_reported_and_read_as_the_new_ones() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32 };
        func f(p: Point) {
            local q = Point::{ x: 1, y: 2 };
            local Point::{ x, .. } = p;
        }
    "});
	case.diagnostics().assert_codes(&[
		DiagnosticCode::StructFieldsNeedParentheses,
		DiagnosticCode::StructLiteralIsACall,
		DiagnosticCode::StructLiteralIsACall,
	]);
	assert_eq!(case.struct_fields(0).len(), 2);
	let statements = case.function_block(1);
	let (_, arguments) = named_call(local_definition_value(statements, 0));
	assert_eq!(arguments.len(), 2);
	// The old *pattern* form is gone: it is reported and read as an error,
	// not as the new one.
	assert_eq!(case.local_patterns(1)[1], "<error>");
}

#[test]
fn struct_fields_have_optional_names() {
	let case = TestCase::new(indoc! {"
        struct Named(pub x: i32, y: Vec<T>);
        struct Positional(i32, pub heap::*u8, func(i32) -> i32, Self, _);
        struct Mixed(pub id: u32, math::Number);
        struct Unit();
    "});
	case.diagnostics().assert_none();
	let names = |index: usize| -> Vec<Option<String>> {
		case.struct_fields(index)
			.iter()
			.map(|f| {
				f.inner
					.inner
					.binding
					.and_then(Binding::name)
					.map(|n| case.name(n.inner).to_string())
			})
			.collect()
	};
	assert_eq!(names(0), [Some("x".into()), Some("y".into())]);
	assert_eq!(names(1), [None, None, None, None, None]);
	assert_eq!(names(2), [Some("id".into()), None]);
	assert!(names(3).is_empty());
	// A positional field's type that starts with an identifier is parsed on
	// from it: `math::Number`, `heap::*u8`.
	assert!(matches!(
		case.struct_fields(2)[1].inner.inner.ty.inner,
		TypeExpression::Path(ref segments) if segments.len() == 2
	));
	assert!(matches!(
		case.struct_fields(1)[1].inner.inner.ty.inner,
		TypeExpression::Pointer { .. }
	));
	assert!(case.struct_fields(1)[1].inner.inner.pub_span.is_some());
}

/// A parameter and a field are both written `binding: Type`, or `Type`
/// alone. A binding (`_`, `name`, `mut name`) is always followed by `:`, so
/// anything else is a type.
#[test]
fn parameters_and_fields_share_the_slot_grammar() {
	let case = TestCase::new(indoc! {"
        func f(i32, _: u8, c: i32, mut d: i32, x, _) {}
        struct S(i32, _: u8, c: i32, mut d: i32, pub mut e: i32, x, _);
    "});
	case.diagnostics().assert_none();
	let expected: [Option<&str>; 6] =
		[None, None, Some("c"), Some("d"), None, None];
	let params = &case.function_signature(0).params;
	let names: Vec<_> = params
		.iter()
		.map(|param| {
			param
				.inner
				.inner
				.binding
				.and_then(Binding::name)
				.map(|n| case.name(n.inner))
		})
		.collect();
	assert_eq!(names, expected);
	let muts: Vec<_> = params
		.iter()
		.map(|param| {
			param.inner.inner.binding.is_some_and(|b| {
				matches!(
					b,
					Binding::Name {
						mut_span: Some(_),
						..
					}
				)
			})
		})
		.collect();
	assert_eq!(muts, [false, false, false, true, false, false]);
	// `_:` is written, a binding that binds nothing; a type alone has none.
	assert!(params[0].inner.inner.binding.is_none());
	assert!(matches!(
		params[1].inner.inner.binding,
		Some(Binding::Wildcard(_))
	));
	// `x` alone is the type `x`, `_` alone the type `_`.
	let ty = |index: usize| &params[index].inner.inner.ty.inner;
	assert!(
		matches!(ty(4), TypeExpression::Path(segments) if segments.len() == 1)
	);
	assert!(matches!(ty(5), TypeExpression::Infer));

	let fields = case.struct_fields(1);
	let names: Vec<_> = fields
		.iter()
		.map(|field| {
			field
				.inner
				.inner
				.binding
				.and_then(Binding::name)
				.map(|n| case.name(n.inner))
		})
		.collect();
	assert_eq!(
		names,
		[None, None, Some("c"), Some("d"), Some("e"), None, None]
	);
	let muts: Vec<_> = fields
		.iter()
		.map(|field| {
			field.inner.inner.binding.is_some_and(|b| {
				matches!(
					b,
					Binding::Name {
						mut_span: Some(_),
						..
					}
				)
			})
		})
		.collect();
	assert_eq!(muts, [false, false, false, true, true, false, false]);
	assert!(fields[4].inner.inner.pub_span.is_some());
}

/// `self` is a binding like any other: its type is written.
#[test]
fn the_receiver_is_written_with_its_type() {
	let case = TestCase::new(indoc! {"
        func a(self: Self) {}
        func b(mut self: heap::*Self) {}
    "});
	case.diagnostics().assert_none();
	for index in 0..2 {
		let param = &case.function_signature(index).params[0].inner.inner;
		let Some(Binding::Name { mut_span, name }) = param.binding else {
			panic!("`self` is a name")
		};
		assert_eq!(case.name(name.inner), "self");
		assert_eq!(mut_span.is_some(), index == 1);
	}
}

/// A binding needs a type, and `mut` needs a name, in a parameter and in a
/// field alike.
#[test]
fn a_binding_needs_a_type_and_mut_a_name() {
	for (source, code, message) in [
		(
			"func f(self) {}",
			DiagnosticCode::MissingTypeAnnotation,
			"expected a type annotation",
		),
		(
			"func f(mut self) {}",
			DiagnosticCode::MissingTypeAnnotation,
			"expected a type annotation",
		),
		(
			"func f(mut i32) {}",
			DiagnosticCode::MissingTypeAnnotation,
			"expected a type annotation",
		),
		(
			"func f(mut x) {}",
			DiagnosticCode::MissingTypeAnnotation,
			"expected a type annotation",
		),
		(
			"func f(mut heap::*u8) {}",
			DiagnosticCode::InvalidMutBinding,
			"`mut` needs a name",
		),
		(
			"struct S(mut i32);",
			DiagnosticCode::MissingTypeAnnotation,
			"expected a type annotation",
		),
		(
			"func f(mut _: i32) {}",
			DiagnosticCode::InvalidMutBinding,
			"`mut` needs a name",
		),
		(
			"func f(mut _) {}",
			DiagnosticCode::InvalidMutBinding,
			"`mut` needs a name",
		),
		(
			"func f(mut *u8) {}",
			DiagnosticCode::InvalidMutBinding,
			"`mut` needs a name",
		),
		(
			"struct S(mut _: i32);",
			DiagnosticCode::InvalidMutBinding,
			"`mut` needs a name",
		),
	] {
		let case = TestCase::new(source);
		let diagnostics = case.diagnostics();
		diagnostics.assert_codes(&[code]);
		diagnostics.assert_error_saying(message);
	}
}

/// A binding written without its type keeps its name and is given an error
/// type, so the parameter, and those after it, are still there.
#[test]
fn a_binding_without_a_type_recovers_with_an_error_type() {
	let case = TestCase::new("func f(self, mut x, y: i32) {}");
	case.diagnostics().assert_codes(&[
		DiagnosticCode::MissingTypeAnnotation,
		DiagnosticCode::MissingTypeAnnotation,
	]);
	let params = &case.function_signature(0).params;
	let names: Vec<_> = params
		.iter()
		.map(|param| {
			param
				.inner
				.inner
				.binding
				.and_then(Binding::name)
				.map(|n| case.name(n.inner))
		})
		.collect();
	assert_eq!(names, [Some("self"), Some("x"), Some("y")]);
	for param in &params[..2] {
		assert!(matches!(param.inner.inner.ty.inner, TypeExpression::Error));
	}
}

/// Parentheses always make a `Tuple`, recorded as written, separators
/// included; what one element means is TIR's.
#[test]
fn test_parenthesized_lists_are_tuples_as_written() {
	let case = TestCase::new(indoc! {"
        func shapes(x: i32, y: i32) {
            local grouped = (x);
            local single = (x,);
            local pair = (x, y,);
        }
    "});

	case.diagnostics().assert_none();
	let statements = case.function_block(0);
	assert!(matches!(
		local_definition_value(statements, 0),
		Expression::Tuple { elements }
			if matches!(&**elements, [element] if element.separator.is_none())
	));
	assert!(matches!(
		local_definition_value(statements, 1),
		Expression::Tuple { elements }
			if matches!(&**elements, [element] if element.separator.is_some())
	));
	assert!(matches!(
		local_definition_value(statements, 2),
		Expression::Tuple { elements }
			if matches!(&**elements, [_, last] if last.separator.is_some())
	));
}

#[test]
fn test_call_field_namespace() {
	// function call, field access, namespace access, unary ops
	let case = TestCase::new(indoc! {"
        func ops(x: i32, p: Point) -> i32 {
            local neg   = -x;
            local inv   = ^x;
            local field = p.x;
            local ns    = console::log;
            add(field, neg)
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	let unary = |index: usize| {
		let Expression::Unary { operator, .. } =
			local_definition_value(statements, index)
		else {
			panic!("expected a unary expression")
		};
		operator.inner
	};
	assert_eq!(unary(0), UnaryOp::InvertSign);
	assert_eq!(unary(1), UnaryOp::BitNot);

	// `p.x` is field access; `console::log` is a two-segment path — the
	// distinction between `.` and `::` is settled here, not in TIR
	let Expression::ObjectAccess { member, .. } =
		local_definition_value(statements, 2)
	else {
		panic!("expected field access")
	};
	assert_eq!(case.name(member.ident.inner), "x");

	let Expression::Path(segments) = local_definition_value(statements, 3)
	else {
		panic!("expected a path")
	};
	let path: Vec<&str> =
		segments.iter().map(|s| case.name(s.ident.inner)).collect();
	assert_eq!(path, ["console", "log"]);

	let Expression::Call { arguments, .. } =
		statement_expression(statements, 4)
	else {
		panic!("expected a call")
	};
	assert_eq!(arguments.len(), 2);
}

#[test]
fn test_operator_precedence() {
	let case = TestCase::new(indoc! {"
        func f(a: i32, b: i32, c: i32) -> i32 {
            a + b * c
        }
    "});

	let statements = case.function_block(0);
	let Expression::Binary { right, .. } = statement_expression(statements, 0)
	else {
		panic!("expected outer binary expression")
	};
	assert!(
		matches!(
			&right.inner,
			Expression::Binary {
				operator: Spanned {
					inner: BinaryOp::Mul,
					..
				},
				..
			}
		),
		"expected multiplication on the right-hand side of addition"
	);
}

#[test]
fn test_left_associativity() {
	let case = TestCase::new(indoc! {"
        func f(a: i32, b: i32, c: i32) -> i32 {
            a - b - c
        }
    "});

	let statements = case.function_block(0);
	let Expression::Binary { left, operator, .. } =
		statement_expression(statements, 0)
	else {
		panic!("expected outer binary expression")
	};
	assert_eq!(operator.inner, BinaryOp::Sub);
	assert!(
		matches!(
			&left.inner,
			Expression::Binary {
				operator: Spanned {
					inner: BinaryOp::Sub,
					..
				},
				..
			}
		),
		"expected subtraction to associate to the left"
	);
}

#[test]
fn test_cast_precedence() {
	let case = TestCase::new(indoc! {"
        func arith(a: i32, b: i32) -> i32 { a + b as i32 }
        func unary(x: i32) -> i32 { -x as i32 }
    "});

	let arithmetic = case.function_block(0);
	let Expression::Binary { right, .. } = statement_expression(arithmetic, 0)
	else {
		panic!("expected arithmetic binary expression")
	};
	assert!(
		matches!(&right.inner, Expression::Cast { .. }),
		"expected cast to bind tighter than addition"
	);

	let unary = case.function_block(1);
	let Expression::Unary { operand, .. } = statement_expression(unary, 0)
	else {
		panic!("expected unary expression")
	};
	assert!(
		matches!(&operand.inner, Expression::Cast { .. }),
		"expected cast to bind tighter than unary negation"
	);
}

#[test]
fn test_chained_member_access() {
	// member access is left-associative: p.x.y  =>  (p.x).y
	// a call result can be immediately accessed:  p.foo().z  =>  (p.foo()).z
	let case = TestCase::new(indoc! {"
        func f(p: Point) {
            local a = p.x.y;
            local b = p.foo().z;
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	let Expression::ObjectAccess { object, member } =
		local_definition_value(statements, 0)
	else {
		panic!("expected object access")
	};
	assert_eq!(case.name(member.ident.inner), "y");
	let Expression::ObjectAccess { member: inner, .. } = &object.inner else {
		panic!("`p.x.y` should nest as `(p.x).y`")
	};
	assert_eq!(case.name(inner.ident.inner), "x");

	let Expression::ObjectAccess { object, member } =
		local_definition_value(statements, 1)
	else {
		panic!("expected object access")
	};
	assert_eq!(case.name(member.ident.inner), "z");
	assert!(
		matches!(object.inner, Expression::MethodCall(_)),
		"`p.foo().z` should access the call's result"
	);
}

#[test]
fn test_address_of() {
	// ptr.*.& — address-of; value is Deref. Always produces a shared reference.
	let case = TestCase::new(indoc! {"
        func f(ptr: &i32) {
            local a = ptr.*.&;
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);
	let expr = local_definition_value(stmts, 0);
	let Expression::AddressOf { value } = expr else {
		panic!("expected AddressOf, got {expr:?}");
	};
	assert!(
		matches!(value.inner, Expression::Deref { .. }),
		"expected Deref as AddressOf operand"
	);
}

#[test]
fn test_address_of_through_field() {
	// ptr.*.field.& — address-of a field: AddressOf > ObjectAccess > Deref
	let case = TestCase::new(indoc! {"
        func f(ptr: &Point) {
            local a = ptr.*.x.&;
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);
	let expr = local_definition_value(stmts, 0);
	let Expression::AddressOf { value } = expr else {
		panic!("expected AddressOf, got {expr:?}");
	};
	let Expression::ObjectAccess { object, .. } = &value.inner else {
		panic!("expected ObjectAccess inside AddressOf");
	};
	assert!(
		matches!(object.inner, Expression::Deref { .. }),
		"expected Deref as root of field place"
	);
}

#[test]
fn test_numeric_literal_forms() {
	let case = TestCase::new(indoc! {"
        func f() {
            local hex    = 0xFF;
            local binary = 0b1010;
            local sep    = 1_000_000;
        }
    "});

	let statements = case.function_block(0);
	assert_eq!(statements.len(), 3);
	assert!(matches!(
		local_definition_value(statements, 0),
		Expression::Int { value: 255 }
	));
	assert!(matches!(
		local_definition_value(statements, 1),
		Expression::Int { value: 10 }
	));
	assert!(matches!(
		local_definition_value(statements, 2),
		Expression::Int { value: 1_000_000 }
	));
}

#[test]
fn test_scientific_notation_float_literals() {
	let case = TestCase::new(indoc! {"
        func f() {
            local plain  = 1e10;
            local dot    = 3.4e2;
            local plus   = 1e+5;
            local minus  = 1.5e-3;
            local upper  = 2E3;
        }
    "});

	case.diagnostics().assert_none();
	let statements = case.function_block(0);
	assert_eq!(statements.len(), 5);
	// Each `…e…` form parses cleanly as a single float expression; the lexer
	// commits the whole span to one `Float` token (the tricky run-into-EOF
	// case is `test_scientific_notation_literal_at_end_of_input_is_float`). The
	// value is assembled in TIR — see `test_scientific_notation_float_values`.
	for i in 0..statements.len() {
		assert!(
			matches!(local_definition_value(statements, i), Expression::Float),
			"statement {i} should parse as a float literal"
		);
	}
}

#[test]
fn test_scientific_notation_literal_at_end_of_input_is_float() {
	// Regression: the exponent scanner must commit to Float even when the
	// digits run straight into EOF with no following token to stop the
	// scan — a dot-less mantissa like `1e5` would otherwise fall through
	// to the `seen_dot` check and lex as a (bogus) Int.
	for src in ["1e5", "2E3", "1e+5", "1e", "1E-"] {
		let tok = Lexer::new(src).advance();
		assert!(tok.inner == Token::Float, "`{src}` should lex as Float");
		assert_eq!(tok.span.end - tok.span.start, src.len() as u32);
	}
}

// ── Patterns ─────────────────────────────────────────────────────────────────

#[test]
fn test_pattern_simple_binding() {
	let case = TestCase::new(indoc! {"
        func f(v: i32) {
            local x = v;
            local mut y = v;
            local _ = v;
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(case.local_patterns(0), ["x", "mut y", "_"]);
}

#[test]
fn test_pattern_tuple_destructuring() {
	let case = TestCase::new(indoc! {"
        func f(pair: (i32, i32)) {
            local (a, b) = pair;
            local (mut c, _) = pair;
            local (x, (y, z)) = pair;
            local (a, ..) = pair;
            local (.., z) = pair;
            local (a, .., z) = pair;
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(
		case.local_patterns(0),
		[
			"(tuple a b)",
			"(tuple mut c _)",
			"(tuple x (tuple y z))",
			"(tuple a ..)",
			"(tuple .. z)",
			"(tuple a .. z)",
		]
	);
}

#[test]
fn test_pattern_struct_destructuring() {
	let case = TestCase::new(indoc! {"
        func f(p: Point) {
            local Point({ x, y }) = p;
            local Point({ x: a, y: b }) = p;
            local geom::Point({ x, .. }) = p;
            local Point(a, ..) = p;
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(
		case.local_patterns(0),
		[
			"(Point { x, y })",
			"(Point { x: a, y: b })",
			"(geom::Point { x, .. })",
			"(Point a ..)",
		]
	);
}

#[test]
fn a_pattern_path_starts_where_an_expression_path_can() {
	// `Self`, `crate` and `super` lead a path, and `super` continues one;
	// any other keyword is no name.
	let case = TestCase::new(indoc! {"
        func f(p: Point) {
            local Self(a, ..) = p;
            local crate::geom::Point({ x, .. }) = p;
            local super::super::Point(b, ..) = p;
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(
		case.local_patterns(0),
		[
			"(Self a ..)",
			"(crate::geom::Point { x, .. })",
			"(super::super::Point b ..)",
		]
	);

	let case = TestCase::new("func f(p: P) { local loop(a) = p; }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::ReservedIdentifier]);
}

#[test]
fn test_pattern_rests_are_kept_as_written() {
	// More than one `..` is a semantic error, not a syntax one: the parser
	// keeps every rest where it was written and leaves the judgement to TIR.
	let case = TestCase::new(indoc! {"
        func f(p: Point) {
            local (.., a, ..) = p;
            local Point(.., ..) = p;
            local Point({ .., x, .. }) = p;
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(
		case.local_patterns(0),
		["(tuple .. a ..)", "(Point .. ..)", "(Point { .., x, .. })"]
	);
}

#[test]
fn test_pattern_terms_say_what_they_are() {
	// A literal compares with that value, a qualified path with that
	// constant, and a name binds — unless `const` says it is a constant.
	let case = TestCase::new(indoc! {"
        func f(p: Point) {
            match p {
                Point(0, 0) -> {},
                Point(x, const MAX) -> {},
                Point(x, 0) -> {},
                Point(-1, 'a' | true) -> {},
                (mut x, _) -> {},
                Point({ x, y: const MAX }) -> {},
                x -> {},
            }
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(
		case.arm_patterns(0),
		[
			"(Point 0 0)",
			"(Point x (const MAX))",
			"(Point x 0)",
			"(Point -1 (| char true))",
			"(tuple mut x _)",
			"(Point { x, y: (const MAX) })",
			"x",
		]
	);
}

#[test]
fn test_pattern_const_marks_a_name_as_a_constant() {
	// `const` is the one marker left: a single-segment name that should
	// compare with a constant rather than bind.
	let case = TestCase::new(indoc! {"
        func f(x: i32) {
            match x {
                const MAX -> {},
                const MAX | const MIN -> {},
            }
        }
    "});
	case.diagnostics().assert_none();
	assert_eq!(
		case.arm_patterns(0),
		["(const MAX)", "(| (const MAX) (const MIN))"]
	);
}

#[test]
fn test_pattern_redundant_const_is_dropped_and_warned() {
	// A `const` before a path that is a constant already changes nothing:
	// the parser warns and drops it.
	let case = TestCase::new(indoc! {"
        func f(x: i32) {
            match x {
                const Ordering::Less -> {},
                const MAX -> {},
            }
        }
    "});
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::RedundantPatternMarker]);
	case.diagnostics()
		.assert_warning(DiagnosticCode::RedundantPatternMarker);
	assert_eq!(
		case.arm_patterns(0),
		["(const Ordering::Less)", "(const MAX)"]
	);
}

#[test]
fn test_pattern_a_literal_is_a_test() {
	// A literal cannot bind, so it is a comparison on its own: no marker
	// is needed to say what it means.
	for pattern in ["0", "-1", "'a'", "true"] {
		let case = TestCase::new(&format!(
			"func f(x: i32) {{ match x {{ {pattern} -> {{}} }} }}"
		));
		case.diagnostics().assert_none();
	}
}

#[test]
fn test_pattern_const_takes_a_path_and_nothing_else() {
	// Only a path can be marked: a literal is a comparison already, and a
	// destructure has no name to mark.
	for (pattern, code) in [
		("const 0", DiagnosticCode::UnexpectedToken),
		("const (1, 2)", DiagnosticCode::UnexpectedToken),
		("const _", DiagnosticCode::ReservedIdentifier),
		("const mut y", DiagnosticCode::ReservedIdentifier),
	] {
		let case = TestCase::new(&format!(
			"func f(x: i32) {{ match x {{ {pattern} -> {{}} }} }}"
		));
		case.diagnostics().assert_error(code);
	}
}

#[test]
fn test_pattern_local_is_not_needed() {
	// A name binds by default, so `local` says nothing in a pattern.
	let case = TestCase::new("func f(x: i32) { local local y = x; }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidBindingPattern]);
	case.diagnostics()
		.assert_error_saying("`local` is not needed in a pattern");
}

#[test]
fn test_pattern_a_float_or_string_is_read() {
	// The parser reads them; whether they can be matched is the checker's
	// judgement, so the rest of the file still parses.
	for pattern in ["1.5", "-1.5", "\"hi\""] {
		let case = TestCase::new(&format!(
			"func f(x: i32) {{ match x {{ {pattern} -> {{}} }} }}"
		));
		case.diagnostics().assert_none();
	}
}

#[test]
fn test_pattern_with_type_annotation() {
	let case = TestCase::new(indoc! {"
        func f(pair: (i32, i32)) {
            local (a, b): (i32, i32) = pair;
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);

	let Statement::LocalDefinition { ty, .. } = &stmts[0].inner.inner else {
		panic!("expected local definition")
	};
	assert_eq!(case.local_patterns(0), ["(tuple a b)"]);
	assert!(ty.is_some(), "type annotation should be present");
}

// ── Diagnostics ──────────────────────────────────────────────────────────────

#[test]
fn test_missing_semicolon_warns_but_parses() {
	let case = TestCase::new(indoc! {"
        func f(x: i32) -> i32 {
            local y: i32 = x
            y
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::MissingSeparator]);
	assert_eq!(case.function_block(0).len(), 2);
}

#[test]
fn test_unclosed_delimiter() {
	let case = TestCase::new(indoc! {"
        func f() {
            local x: i32 = 1;
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::UnclosedDelimiter]);
	assert_eq!(case.function_block(0).len(), 1);
}

#[test]
fn test_invalid_function_param_type_reports_parse_error() {
	let case = TestCase::new(indoc! {"
        func f(x: =) {}
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::UnexpectedToken]);
}

#[test]
fn test_invalid_integer_literal() {
	let case = TestCase::new(indoc! {"
        func f() -> i32 {
            99999999999999999999
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidNumericLiteral]);
	assert!(matches!(
		statement_expression(case.function_block(0), 0),
		Expression::Int { value: 0 }
	));
}

#[test]
fn test_invalid_float_literal_empty_exponent() {
	// `1e` and `1e+` still lex as a single (malformed) Float token rather
	// than backtracking to split off `e`/`e+` as a separate identifier —
	// see the comment on `Lexer::consume_number`'s exponent handling.
	let case = TestCase::new(indoc! {"
        func f() -> f32 {
            1e
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidNumericLiteral]);
	assert!(matches!(
		statement_expression(case.function_block(0), 0),
		Expression::Float
	));
}

#[test]
fn test_incomplete_expression() {
	let case = TestCase::new(indoc! {"
        func binary() -> i32 { 1 + }
        func unary()  -> i32 { -   }
    "});

	case.diagnostics().assert_codes(&[
		DiagnosticCode::IncompleteExpression,
		DiagnosticCode::IncompleteExpression,
	]);
	assert!(case.function_block(0).is_empty());
	assert!(case.function_block(1).is_empty());
}

#[test]
fn test_reserved_identifier() {
	let case = TestCase::new(indoc! {"
        func f() {
            local func = 1;
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::ReservedIdentifier]);
	assert_eq!(case.function_block(0).len(), 1);
}

#[test]
fn test_invalid_attribute_and_namespace_diagnostics() {
	let case = TestCase::new(indoc! {"
        #[123]
        func attr() {}

        func namespace_error(x: i32, y: i32) {
            (x + y)::value
        }
    "});

	case.diagnostics().assert_codes(&[
		DiagnosticCode::InvalidAttribute,
		DiagnosticCode::InvalidItem,
		DiagnosticCode::InvalidNamespace,
	]);
	assert_eq!(case.ast.items.len(), 2);
	assert!(matches!(case.item(0), Item::Function { .. }));
}

#[test]
fn test_missing_initializer() {
	let case = TestCase::new(indoc! {"
        func f() {
            local x: i32
        }
        global y: i32
    "});
	let missing_initializer_count = case
		.ast
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref() == Some(DiagnosticCode::MissingInitializer.code())
		})
		.count();
	assert_eq!(
		missing_initializer_count, 2,
		"expected one MissingInitializer for local and one for global"
	);
	assert_eq!(case.ast.items.len(), 1);
	assert!(case.function_block(0).is_empty());
}

#[test]
fn test_missing_comma_between_struct_fields_warns_but_parses() {
	let case = TestCase::new(indoc! {"
        struct Pair(
            left: i32
            right: i32,
        );
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::MissingSeparator]);
	assert_eq!(case.struct_fields(0).len(), 2);
}

#[test]
fn test_module_pub_items_and_associated_types() {
	let case = TestCase::new(indoc! {"
        pub mod math {
            pub func zero() -> i32 {
                0
            }
        }

        pub struct Counter(
            value: i32,
        );

        pub trait Iterator {
            type Item: Show + Clone;
            func next(self: Self) -> Self::Item;
        }

        impl Iterator for Range {
            type Item = i32;

            func next(self: Self) -> Self::Item {
                0
            }
        }
    "});

	case.diagnostics().assert_none();

	let Item::Module {
		pub_span, items, ..
	} = case.item(0)
	else {
		panic!("expected public module")
	};
	assert!(pub_span.is_some());
	assert!(matches!(
		items.inner[0].inner.inner,
		Item::Function {
			pub_span: Some(_),
			..
		}
	));

	let Item::Struct { pub_span, .. } = case.item(1) else {
		panic!("expected public struct")
	};
	assert!(pub_span.is_some());

	let Item::Trait {
		pub_span,
		items: trait_items,
		..
	} = case.item(2)
	else {
		panic!("expected public trait")
	};
	assert!(pub_span.is_some());
	assert!(matches!(
		trait_items[0].inner.inner,
		TraitItem::AssociatedType { ref bounds, .. }
			if matches!(
				bounds.as_ref().map(|b| &b.inner),
				Some(BoundExpression::BoundList(list)) if list.len() == 2
			)
	));

	let Item::TraitImpl {
		items: impl_items, ..
	} = case.item(3)
	else {
		panic!("expected trait impl")
	};
	assert!(matches!(
		impl_items[0].inner.inner,
		ImplItem::AssocType { .. }
	));
}

#[test]
fn test_external_module_item() {
	let case = TestCase::new("mod math;");

	case.diagnostics().assert_none();

	let Item::ModuleDeclaration { pub_span, name, .. } = case.item(0) else {
		panic!("expected external module")
	};

	assert!(pub_span.is_none());
	assert_eq!(case.strings.resolve(name.inner), Some("math"));
}

#[test]
fn test_package_instances() {
	let case = TestCase::new(indoc! {"
        crate \"math\" as math;
        pub crate \"math\" as math2;
    "});

	case.diagnostics().assert_none();

	let Item::PackageInstance {
		pub_span,
		package,
		alias,
	} = case.item(0)
	else {
		panic!(
			"expected a package instance, got {}",
			item_kind(case.item(0))
		)
	};
	assert!(pub_span.is_none());
	assert_eq!(
		package.extract_str(&case.files.get(case.ast.file_id).unwrap().source),
		"\"math\"",
		"the key stays as written, quotes included"
	);
	assert_eq!(case.strings.resolve(alias.inner), Some("math"));

	let Item::PackageInstance {
		pub_span, alias, ..
	} = case.item(1)
	else {
		panic!(
			"expected a package instance, got {}",
			item_kind(case.item(1))
		)
	};
	assert!(pub_span.is_some());
	assert_eq!(case.strings.resolve(alias.inner), Some("math2"));
}

/// A package instance is an item like any other, so it is not limited to the
/// package root.
#[test]
fn test_package_instance_in_a_nested_module() {
	let case = TestCase::new(indoc! {"
        mod outer {
            mod inner {
                pub crate \"math\" as math;
            }
        }
    "});

	case.diagnostics().assert_none();
	let Item::Module { items, .. } = case.item(0) else {
		panic!("expected a module")
	};
	let Item::Module { items, .. } = &items.inner[0].inner.inner else {
		panic!("expected a nested module")
	};
	assert!(matches!(
		items.inner[0].inner.inner,
		Item::PackageInstance {
			pub_span: Some(_),
			..
		}
	));
}

#[test]
fn test_package_instance_requires_an_alias() {
	let case = TestCase::new("crate \"math\";");

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::MissingPackageAlias]);
}

#[test]
fn test_chained_comparison_error() {
	let case = TestCase::new(indoc! {"
        func f(a: i32, b: i32, c: i32) -> bool {
            a < b < c
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::ChainedComparison]);
	let Expression::Binary { left, operator, .. } =
		statement_expression(case.function_block(0), 0)
	else {
		panic!("expected outer comparison")
	};
	assert_eq!(operator.inner, BinaryOp::Less);
	assert!(matches!(
		&left.inner,
		Expression::Binary {
			operator: Spanned {
				inner: BinaryOp::Less,
				..
			},
			..
		}
	));
}

// ── Generics ─────────────────────────────────────────────────────────────────

#[test]
fn test_generic_signatures() {
	let case = TestCase::new(indoc! {"
        func zip<T, U: Show + Clone, V: Scalable>(left: T, middle: U, right: V) -> U {
            middle
        }
    "});
	case.diagnostics().assert_none();

	let signature = case.function_signature(0);
	let params: Vec<&str> = signature
		.type_params
		.iter()
		.map(|param| case.name(param.name.inner))
		.collect();
	assert_eq!(params, ["T", "U", "V"]);
	// only the bounded ones carry a bound expression
	let bounded: Vec<bool> = signature
		.type_params
		.iter()
		.map(|param| param.bounds.is_some())
		.collect();
	assert_eq!(bounded, [false, true, true]);
	assert_eq!(signature.params.len(), 3);
	assert!(signature.result.is_some());
}

#[test]
fn test_generic_struct() {
	let case = TestCase::new(indoc! {"
        struct Pair<T, U>(
            first: T,
            second: U,
        );
    "});
	case.diagnostics().assert_none();
	let Item::Struct {
		name,
		type_params,
		fields,
		..
	} = case.item(0)
	else {
		panic!("expected struct item")
	};
	assert_eq!(case.strings.resolve(name.inner), Some("Pair"));
	assert_eq!(type_params.len(), 2);
	assert_eq!(case.strings.resolve(type_params[0].name.inner), Some("T"));
	assert!(type_params[0].bounds.is_none());
	assert_eq!(case.strings.resolve(type_params[1].name.inner), Some("U"));
	assert!(type_params[1].bounds.is_none());
	assert_eq!(fields.len(), 2);
}

#[test]
fn test_generic_struct_with_bounds() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<T: Add + Clone>(
            value: T,
        );
    "});
	case.diagnostics().assert_none();
	let Item::Struct { type_params, .. } = case.item(0) else {
		panic!("expected struct item")
	};
	assert_eq!(type_params.len(), 1);
	assert!(matches!(
		type_params[0].bounds.as_ref().map(|b| &b.inner),
		Some(BoundExpression::BoundList(list)) if list.len() == 2
	));
}

#[test]
fn test_import_alias_and_entry_kinds() {
	let case = TestCase::new(indoc! {"
        import \"env\" as host {
            func log(message: string);
            global mut counter: i32;
            memory MEM: u32;
        }
    "});

	case.diagnostics().assert_none();
	let Item::Import {
		internal_name,
		items,
		..
	} = case.item(0)
	else {
		panic!("expected import block")
	};
	assert_eq!(case.strings.resolve(internal_name.inner), Some("host"));
	assert!(matches!(
		items.inner[0].inner.inner.declaration,
		ImportDeclaration::Function { .. }
	));
	assert!(matches!(
		items.inner[1].inner.inner.declaration,
		ImportDeclaration::Global {
			mut_span: Some(_),
			..
		}
	));
	assert!(matches!(
		items.inner[2].inner.inner.declaration,
		ImportDeclaration::Memory { .. }
	));
}

#[test]
fn test_turbofish_call() {
	let case = TestCase::new(indoc! {"
        func main() {
            identity::<i32>(42)
        }
    "});
	case.diagnostics().assert_none();

	let statements = case.function_block(0);
	let Expression::Call { callee, arguments } =
		statement_expression(statements, 0)
	else {
		panic!("expected a call")
	};
	assert_eq!(arguments.len(), 1);
	let Expression::Path(segments) = &callee.inner else {
		panic!("expected a path callee")
	};
	// the turbofish binds to the final segment, not to the call
	assert_eq!(segments.len(), 1);
	assert_eq!(case.name(segments[0].ident.inner), "identity");
	assert_eq!(segments[0].type_args.len(), 1);
}

#[test]
fn test_turbofish_method_call() {
	let case = TestCase::new(indoc! {"
        func main(obj: Foo) {
            obj.transform::<i32>()
        }
    "});
	case.diagnostics().assert_none();

	let statements = case.function_block(0);
	// a called member's turbofish is a `MethodCall`'s
	let Expression::MethodCall(call) = statement_expression(statements, 0)
	else {
		panic!("expected a method call")
	};
	assert_eq!(case.name(call.method.ident.inner), "transform");
	assert_eq!(call.method.type_args.len(), 1);
	assert!(call.arguments.is_empty());
}

#[test]
fn test_generic_application_type_args() {
	let case = TestCase::new(indoc! {"
        struct Pair<T, U>(
            first: T,
            second: U,
        );
        func make(x: Pair<i32, f64>) {}
    "});
	case.diagnostics().assert_none();
	let Item::Function { signature, .. } = case.item(1) else {
		panic!("expected function")
	};
	let param_ty = &signature.params[0].inner.inner.ty.inner;
	let TypeExpression::Path(segments) = param_ty else {
		panic!("expected a path")
	};
	assert_eq!(segments.len(), 1);
	let type_args = &segments[0].type_args;
	assert_eq!(type_args.len(), 2);
	assert!(matches!(type_args[0].inner, TypeExpression::Path(_)));
	assert!(matches!(type_args[1].inner, TypeExpression::Path(_)));
}

#[test]
fn test_path_continues_after_a_segment_with_type_args() {
	let case = TestCase::new(indoc! {"
        func make(x: Vec<i32>::Item) {}
    "});
	case.diagnostics().assert_none();
	let Item::Function { signature, .. } = case.item(0) else {
		panic!("expected function")
	};
	let param_ty = &signature.params[0].inner.inner.ty.inner;
	let TypeExpression::Path(segments) = param_ty else {
		panic!("expected a path")
	};
	assert_eq!(segments.len(), 2);
	assert_eq!(case.name(segments[0].ident.inner), "Vec");
	assert_eq!(segments[0].type_args.len(), 1);
	assert_eq!(case.name(segments[1].ident.inner), "Item");
	assert!(segments[1].type_args.is_empty());
}

#[test]
fn test_double_right_arrow_split() {
	// Regression: `>>` in nested generics was eagerly lexed as `DoubleRightArrow`
	// instead of two separate `>` tokens. Test across type expressions,
	// bare generics in a bound, and turbofish in an expression.
	let case = TestCase::new(indoc! {"
        func type_expr(x: Outer<Inner<u32>>) {}
        func bound_generic<T: Wrapper<Inner<u32>>>(t: T) {}
        func method_turbofish(obj: Foo) { obj.transform::<Vec<u32>>() }
    "});
	case.diagnostics().assert_none();
}

#[test]
fn test_where_binding_parses_as_bound_with_bindings() {
	let case = TestCase::new(indoc! {"
        func f<T: Memory where { Size = u32 }>(t: T) {}
    "});
	case.diagnostics().assert_none();
	let Item::Function { signature, .. } = case.item(0) else {
		panic!("expected function")
	};
	let bounds = signature.type_params[0]
		.bounds
		.as_ref()
		.expect("expected bounds");
	let BoundExpression::WithBindings { path, bindings } = &bounds.inner else {
		panic!("expected WithBindings")
	};
	assert!(matches!(path.as_ref(), BoundExpression::Path(_)));
	assert_eq!(bindings.len(), 1);
}

#[test]
fn test_impl_trait_multi_segment_trait_name() {
	// `impl gfx::Drawable for Point` — trait_name must be two path segments.
	let case = TestCase::new(indoc! {"
        impl gfx::Drawable for Point {
            func draw(self: Self) {}
        }
    "});
	case.diagnostics().assert_none();
	let Item::TraitImpl { trait_name, .. } = case.item(0) else {
		panic!("expected ImplTrait")
	};
	assert_eq!(
		trait_name.segments.len(),
		2,
		"expected two path segments: gfx, Drawable"
	);
}

#[test]
fn test_typeset_attributes_parsed() {
	let case = TestCase::new(indoc! {"
        #[tag = \"my_typeset\"]
        typeset Foo { u32, u64 }
    "});
	case.diagnostics().assert_none();
	let Item::TypeSet { attributes, .. } = case.item(0) else {
		panic!("expected TypeSet")
	};
	assert_eq!(attributes.len(), 1, "expected one attribute on the typeset");
}

#[test]
fn test_typeset_without_bounds_has_none() {
	let case = TestCase::new("typeset Foo { u32, u64 }");
	case.diagnostics().assert_none();
	let Item::TypeSet {
		bounds, members, ..
	} = case.item(0)
	else {
		panic!("expected TypeSet")
	};
	assert!(bounds.is_none());
	assert_eq!(members.len(), 2);
}

#[test]
fn test_typeset_bound_clause_parses() {
	let case = TestCase::new("typeset Integer: Add + Sub { i32, i64 }");
	case.diagnostics().assert_none();
	let Item::TypeSet {
		bounds, members, ..
	} = case.item(0)
	else {
		panic!("expected TypeSet")
	};
	assert_eq!(members.len(), 2);
	let Some(bounds) = bounds else {
		panic!("expected a bound clause")
	};
	assert!(
		matches!(bounds.inner, BoundExpression::BoundList(ref b) if b.len() == 2)
	);
}

#[test]
fn test_typeset_bound_clause_with_where_bindings_parses() {
	let case = TestCase::new(
		"typeset Integer: Add where { Output = Self } { i32, i64 }",
	);
	case.diagnostics().assert_none();
	let Item::TypeSet {
		bounds, members, ..
	} = case.item(0)
	else {
		panic!("expected TypeSet")
	};
	assert_eq!(members.len(), 2);
	assert!(matches!(
		bounds.as_ref().map(|b| &b.inner),
		Some(BoundExpression::WithBindings { .. })
	));
}

// ── binary operators ─────────────────────────────────────────────────────────

#[test]
fn test_every_binary_operator_parses_to_its_own_operator() {
	// One row per `BinaryOp` variant. The rendered operator comes from
	// `BinaryOp::as_str`, so this is really a round-trip through
	// lex -> `TryFrom<Token> for BinaryOp` -> `as_str`: a mis-wired arm (say
	// `%=` reaching `MulAssign`) renders the wrong symbol and fails here.
	let operators = [
		// arithmetic
		"+", "-", "*", "/", "%", // comparison
		"==", "!=", "<", "<=", ">", ">=", // logical
		"&&", "||", // bitwise
		"&", "|", "^", "<<", ">>", // assignment
		"=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
	];
	assert_eq!(
		operators.len(),
		29,
		"every `BinaryOp` variant should have a row here"
	);

	for operator in operators {
		assert_eq!(
			shape_of(&format!("a {operator} b")),
			format!("({operator} a b)"),
			"parsing `a {operator} b`"
		);
	}
}

#[test]
fn test_binary_operator_precedence_ladder() {
	// Each row pairs two adjacent rungs of `BindingPower`, loosest first, so
	// together they pin the whole ordering: assignment < || < && < | < ^ < &
	// < comparison < shift < additive < multiplicative. The looser operator
	// must end up at the root, with the tighter one nested on the right.
	for (source, expected) in [
		("a = b || c", "(= a (|| b c))"),
		("a || b && c", "(|| a (&& b c))"),
		("a && b | c", "(&& a (| b c))"),
		("a | b ^ c", "(| a (^ b c))"),
		("a ^ b & c", "(^ a (& b c))"),
		// `&` looser than `==` — the C precedence trap, deliberate here
		("a & b == c", "(& a (== b c))"),
		("a == b << c", "(== a (<< b c))"),
		("a << b + c", "(<< a (+ b c))"),
		("a + b * c", "(+ a (* b c))"),
	] {
		assert_eq!(shape_of(source), expected, "parsing `{source}`");
	}
}

#[test]
fn test_binary_operators_associate_to_the_left() {
	// `parse_binary_expression` recurses with the *same* binding power, which
	// makes every operator left-associative.
	for (source, expected) in [
		("a - b - c", "(- (- a b) c)"),
		("a / b / c", "(/ (/ a b) c)"),
		("a << b << c", "(<< (<< a b) c)"),
		// Assignment is left-associative too, unlike most languages. That is
		// intended and unobservable: an assignment evaluates to `()`, so
		// `a = b = c` is rejected either way — as an invalid assignment
		// target when grouped `(a = b) = c`, or as a type mismatch were it
		// grouped `a = (b = c)`. Only if assignment ever yields its assigned
		// value would the grouping become meaningful.
		("a = b = c", "(= (= a b) c)"),
		("a += b += c", "(+= (+= a b) c)"),
	] {
		assert_eq!(shape_of(source), expected, "parsing `{source}`");
	}
}

#[test]
fn test_unary_binds_tighter_than_any_binary_operator() {
	for (source, expected) in [
		("-a * b", "(* (u- a) b)"),
		("^a & b", "(& (u^ a) b)"),
		("!a && b", "(&& (u! a) b)"),
		// and a unary operand is not swallowed by the binary operator
		("a * -b", "(* a (u- b))"),
	] {
		assert_eq!(shape_of(source), expected, "parsing `{source}`");
	}
}

// ── indexing, slicing and array literals ─────────────────────────────────────

#[test]
fn test_index_and_array_literal_expressions() {
	let case = TestCase::new(indoc! {"
        func f(a: &[i32]) {
            local list   = [1, 2, 3];
            local repeat = [0; 8];
            local single = a[0];
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	let Expression::ArrayList { elements } =
		local_definition_value(statements, 0)
	else {
		panic!("expected an array literal")
	};
	assert_eq!(elements.len(), 3);

	// `[value; count]` keeps the two apart rather than expanding the value
	let Expression::ArrayRepeat { value, count } =
		local_definition_value(statements, 1)
	else {
		panic!("expected an array repeat")
	};
	assert_eq!(case.shape(&value.inner), "0");
	assert_eq!(case.shape(&count.inner), "8");

	// a single subscript is an `Index`, never a one-bound `SliceRange`
	assert!(matches!(
		local_definition_value(statements, 2),
		Expression::Index { .. }
	));
}

#[test]
fn test_slice_range_bounds_are_independently_optional() {
	let case = TestCase::new(indoc! {"
        func f(a: &[i32]) {
            local both = a[1..3];
            local from = a[1..];
            local to   = a[..3];
            local all  = a[..];
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	let bounds = |index: usize| {
		let Expression::SliceRange { start, end, .. } =
			local_definition_value(statements, index)
		else {
			panic!("expected a slice range")
		};
		(start.is_some(), end.is_some())
	};
	assert_eq!(bounds(0), (true, true), "a[1..3]");
	assert_eq!(bounds(1), (true, false), "a[1..]");
	assert_eq!(bounds(2), (false, true), "a[..3]");
	assert_eq!(bounds(3), (false, false), "a[..]");
}

// ── qualified and grouped paths ──────────────────────────────────────────────

#[test]
fn test_qualified_path_records_its_trait_and_grouped_does_not() {
	// The two forms differ only in whether a trait disambiguates the item, so
	// that is the thing worth pinning.
	let case = TestCase::new(indoc! {"
        func f() -> i32 {
            <Point as Show>::render()
        }

        func g() -> i32 {
            <Point>::origin()
        }
    "});
	case.diagnostics().assert_none();

	let Expression::Call { callee, .. } =
		statement_expression(case.function_block(0), 0)
	else {
		panic!("expected a call")
	};
	let Expression::QualifiedPath { root, segments } = &callee.inner else {
		panic!("expected a qualified path")
	};
	assert_eq!(case.name(root.trait_path[0].ident.inner), "Show");
	assert_eq!(case.name(segments[0].ident.inner), "render");

	let Expression::Call { callee, .. } =
		statement_expression(case.function_block(1), 0)
	else {
		panic!("expected a call")
	};
	let Expression::Grouped { segments, .. } = &callee.inner else {
		panic!("expected a grouped path — `<T>::x` names no trait")
	};
	assert_eq!(case.name(segments[0].ident.inner), "origin");
}

#[test]
fn test_qualified_and_grouped_paths_in_type_position() {
	let case = TestCase::new(indoc! {"
        func f(a: <Point as Show>::Out, b: <Point>::Out) {}
    "});
	case.diagnostics().assert_none();

	let params = &case.function_signature(0).params;
	let ty = |index: usize| &params[index].inner.inner.ty.inner;
	let TypeExpression::QualifiedPath { root, segments } = ty(0) else {
		panic!("expected a qualified path type")
	};
	assert_eq!(case.name(root.trait_path[0].ident.inner), "Show");
	assert_eq!(case.name(segments[0].ident.inner), "Out");

	assert!(
		matches!(ty(1), TypeExpression::Grouped { .. }),
		"`<Point>::Out` names no trait, so it is a grouped path"
	);
}

#[test]
fn test_a_qualified_type_may_open_another_without_a_space() {
	// `<<` is one token to the lexer, but here it is two openings; the parser
	// splits it, as it splits `>>` where generic lists close together.
	let case = TestCase::new(indoc! {"
        func f(a: <<Point as Show>::Out as Draw>::Frame, b: < <Point as Show>::Out as Draw>::Frame) {}
    "});
	case.diagnostics().assert_none();

	let params = &case.function_signature(0).params;
	for index in 0..2 {
		let TypeExpression::QualifiedPath { root, segments } =
			&params[index].inner.inner.ty.inner
		else {
			panic!("expected a qualified path type")
		};
		assert_eq!(case.name(root.trait_path[0].ident.inner), "Draw");
		assert_eq!(case.name(segments[0].ident.inner), "Frame");
		let TypeExpression::QualifiedPath { root: inner, .. } =
			&root.self_type.inner
		else {
			panic!("the self type is itself a qualified path")
		};
		assert_eq!(case.name(inner.trait_path[0].ident.inner), "Show");
	}
}

// ── keyword expressions ──────────────────────────────────────────────────────

#[test]
fn test_keyword_expressions() {
	let case = TestCase::new(indoc! {"
        func f() -> bool {
            local t = true;
            local u = false;
            return t;
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	assert!(matches!(
		local_definition_value(statements, 0),
		Expression::True
	));
	assert!(matches!(
		local_definition_value(statements, 1),
		Expression::False
	));

	// `return` carries an optional value
	let Expression::Return { value } = statement_expression(statements, 2)
	else {
		panic!("expected a return")
	};
	assert!(value.is_some(), "`return t` should record its value");
}

#[test]
fn test_bare_return_has_no_value() {
	let case = TestCase::new("func f() { return; }");
	case.diagnostics().assert_none();
	let Expression::Return { value } =
		statement_expression(case.function_block(0), 0)
	else {
		panic!("expected a return")
	};
	assert!(value.is_none());
}

#[test]
fn test_turbofish_on_a_member_is_kept_on_its_segment() {
	let case = TestCase::new(indoc! {"
        func f(obj: Foo) {
            local a = obj.m::<i32>;
        }
    "});
	case.diagnostics().assert_none();
	let Expression::ObjectAccess { member, .. } =
		local_definition_value(case.function_block(0), 0)
	else {
		panic!("expected an object access")
	};
	assert_eq!(member.type_args.len(), 1);
}

#[test]
fn test_turbofish_on_any_other_expression_is_an_error() {
	for source in ["(g)::<i32>", "g(1)::<i32>", "a.*::<i32>"] {
		let case =
			TestCase::new(&format!("func f() {{ local a = {source}; }}"));
		case.diagnostics()
			.assert_error(DiagnosticCode::TypeArgumentsNotAllowed);
	}
}

// ── remaining type expressions ───────────────────────────────────────────────

#[test]
fn test_never_type() {
	let case = TestCase::new("func f(a: !) -> ! {}");
	case.diagnostics().assert_none();
	let signature = case.function_signature(0);
	let param = &signature.params[0].inner.inner.ty;
	assert!(matches!(param.inner, TypeExpression::Never));
	let result = signature.result.as_ref().expect("a result type");
	assert!(matches!(result.inner, TypeExpression::Never));
}

#[test]
fn test_infer_and_memory_tagged_types() {
	let case = TestCase::new(indoc! {"
        func f(p: heap::*u8, s: heap::&[i32]) {
            local a: _ = 1;
        }
    "});
	case.diagnostics().assert_none();

	// a memory-tagged type names the memory its pointer or slice belongs to
	let params = &case.function_signature(0).params;
	for index in [0, 1] {
		let ty = &params[index].inner.inner.ty.inner;
		let memory = match ty {
			TypeExpression::Pointer { memory, .. }
			| TypeExpression::Slice { memory, .. } => {
				memory.as_ref().expect("tagged with an explicit memory")
			}
			_ => panic!("expected a pointer or slice type"),
		};
		assert_eq!(case.name(memory[0].ident.inner), "heap");
	}

	let Statement::LocalDefinition { ty, .. } =
		&case.function_block(0)[0].inner.inner
	else {
		panic!("expected a local definition")
	};
	assert!(matches!(
		ty.as_ref().expect("annotated `_`").inner,
		TypeExpression::Infer
	));
}

// ── remaining items ──────────────────────────────────────────────────────────

#[test]
fn test_type_alias_item() {
	let case = TestCase::new(indoc! {"
        type Id = i32;
        type Pair<T> = (T, T);
    "});
	case.diagnostics().assert_none();

	let Item::TypeAlias { name, .. } = case.item(0) else {
		panic!("item 0 is {}, not a type alias", item_kind(case.item(0)))
	};
	assert_eq!(case.name(name.inner), "Id");

	let Item::TypeAlias {
		name, type_params, ..
	} = case.item(1)
	else {
		panic!("item 1 is {}, not a type alias", item_kind(case.item(1)))
	};
	assert_eq!(case.name(name.inner), "Pair");
	assert_eq!(type_params.len(), 1);
}

#[test]
fn test_imported_function_is_a_declaration_without_a_body() {
	let case = TestCase::new(indoc! {"
        import \"env\" as env {
            func log(x: i32)
        }
    "});
	case.diagnostics().assert_none();

	let Item::Import { items: entries, .. } = case.item(0) else {
		panic!("item 0 is {}, not an import", item_kind(case.item(0)))
	};
	assert_eq!(entries.inner.len(), 1);
	let ImportDeclaration::Function { signature, .. } =
		&entries.inner[0].inner.inner.declaration
	else {
		panic!("expected an imported function")
	};
	assert_eq!(case.name(signature.name.inner), "log");
}

#[test]
fn test_bodyless_function_is_a_declaration() {
	// A `func` with no block is an `Item::FunctionDeclaration` rather than an
	// `Item::Function` with an empty body — that split is what lets
	// `#[intrinsic]` and imported functions carry a signature and nothing else.
	let case = TestCase::new(indoc! {"
        #[intrinsic]
        func raw_load(address: u32) -> i32;

        func real() -> i32 { 1 }
    "});
	case.diagnostics().assert_none();

	let Item::FunctionDeclaration {
		signature,
		attributes,
		..
	} = case.item(0)
	else {
		panic!(
			"item 0 is {}, not a function declaration",
			item_kind(case.item(0))
		)
	};
	assert_eq!(case.name(signature.name.inner), "raw_load");
	assert_eq!(case.name(attributes[0].name.inner), "intrinsic");

	// the one with a body still parses as a plain function
	assert!(matches!(case.item(1), Item::Function { .. }));
}

#[test]
fn test_impl_associated_const() {
	let case = TestCase::new(indoc! {"
        impl i32 {
            const ZERO: i32 = 0;
        }
    "});
	case.diagnostics().assert_none();

	let Item::InherentImpl { items, .. } = case.item(0) else {
		panic!("item 0 is {}, not an impl", item_kind(case.item(0)))
	};
	let ImplItem::Constant { name, ty, .. } = &items[0].inner.inner else {
		panic!("expected an associated const")
	};
	assert_eq!(case.name(name.inner), "ZERO");
	assert!(ty.is_some(), "`const ZERO: i32` is annotated");
}

#[test]
fn test_attribute_with_arguments() {
	// `#[word]` and `#[name = value]` are covered elsewhere; this is the
	// third shape, `#[name(arg = value, ...)]`.
	let case = TestCase::new(indoc! {"
        #[memory_limits(min_pages = 1, max_pages = 4)]
        memory m: u32;
    "});
	case.diagnostics().assert_none();

	let Item::Memory { attributes, .. } = case.item(0) else {
		panic!("item 0 is {}, not a memory", item_kind(case.item(0)))
	};
	assert_eq!(case.name(attributes[0].name.inner), "memory_limits");
	let AttributeValue::Args(args) = &attributes[0].value else {
		panic!("expected parenthesised attribute arguments")
	};
	let names: Vec<&str> = args
		.iter()
		.map(|arg| case.name(arg.inner.inner.name.inner))
		.collect();
	assert_eq!(names, ["min_pages", "max_pages"]);
}

// ── remaining parser diagnostics ─────────────────────────────────────────────

#[test]
fn test_local_without_initializer_reports() {
	let case = TestCase::new("func f() { local x: i32; }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::MissingInitializer]);
}

#[test]
fn test_path_in_pattern_position_is_a_constant() {
	// A qualified path cannot bind, so it is a constant — and a `local`
	// cannot test one, which the type checker reports.
	let case = TestCase::new("func f() { local Foo::Bar = 1; }");
	case.diagnostics().assert_none();
}

#[test]
fn test_case_is_not_a_keyword() {
	// `case` marked a mode; the mode is gone, and the word is ordinary
	// again.
	let case = TestCase::new("func f() { local case = 1; }");
	case.diagnostics().assert_none();
}

#[test]
fn test_unknown_token_reports() {
	// `@` lexes to nothing, and is reported for itself. Skipping it leaves
	// `1 2`, which is still two statements with no separator between them —
	// so this is the one case where an unknown token legitimately keeps a
	// follow-on diagnostic.
	//
	// Listed parse-error-first only because unknown tokens are appended once
	// lexing is done; nothing reads diagnostics positionally, so the order
	// here records what happens rather than anything that must hold.
	let case = TestCase::new("func f() -> i32 { 1 @ 2 }");
	case.diagnostics().assert_codes(&[
		DiagnosticCode::MissingSeparator,
		DiagnosticCode::UnknownToken,
	]);
}

#[test]
fn test_a_run_of_unknown_characters_reports_once() {
	// Adjacent unknown characters coalesce into one run, so `@@@` is one
	// diagnostic rather than three...
	let case = TestCase::new("func f() { @@@ }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::UnknownToken]);

	// ...while separate runs stay separate.
	let case = TestCase::new("func f() { @ } func g() { $ }");
	case.diagnostics().assert_codes(&[
		DiagnosticCode::UnknownToken,
		DiagnosticCode::UnknownToken,
	]);
}

#[test]
fn test_unknown_characters_are_skipped_rather_than_derailing_the_parse() {
	// Because the run is skipped like a comment, what surrounds it still
	// parses: none of these produce a second, misleading diagnostic pointing
	// at whatever token happened to follow the unknown one.
	for source in [
		"@",
		"func f() {} @",
		"func f() -> i32 { 1 + @ 2 }",
		"func f() -> i32 { g(@) }",
	] {
		let case = TestCase::new(source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnknownToken]);
	}
}

#[test]
fn string_contexts_preserve_raw_spans_without_interning_contents() {
	let source = indoc! {"
        #[tag = \"line\\nslash\\\\n\"]
        #[other(value = \"line\\nslash\\\\n\")]
        func f() {
            local text = \"line\\nslash\\\\n\";
        }

        import \"line\\nslash\\\\n\" as host {
            func imported();
        }

        export {
            f as \"line\\nslash\\\\n\",
        }
    "};
	let case = TestCase::new(source);
	case.diagnostics().assert_none();
	assert!(case.strings.get("line\nslash\\n").is_none());
	assert!(case.strings.get(r#""line\nslash\\n""#).is_none());
	let Item::Function { attributes, .. } = case.item(0) else {
		panic!("expected function");
	};
	let AttributeValue::NameValue(tag) = &attributes[0].value else {
		panic!("expected name/value attribute");
	};
	let AttributeValue::Args(args) = &attributes[1].value else {
		panic!("expected attribute args");
	};
	let AttributeArgValue::String(arg) = &args[0].inner.inner.value else {
		panic!("expected string argument");
	};
	let Item::Import { external_name, .. } = case.item(1) else {
		panic!("expected import");
	};
	let Item::ExportBlock { entries, .. } = case.item(2) else {
		panic!("expected export");
	};
	for span in [
		tag,
		arg,
		external_name,
		entries[0].inner.inner.alias.as_ref().unwrap(),
	] {
		assert_eq!(span.extract_str(source), r#""line\nslash\\n""#);
	}
	assert!(matches!(
		local_definition_value(case.function_block(0), 0),
		Expression::String
	));
}

#[test]
fn invalid_escapes_preserve_string_nodes_and_surrounding_syntax() {
	let source = indoc! {"
        #[tag = \"\\o\"]
        #[other(value = \"\\o\")]
        func f() {
            local bad = \"\\o\";
            local good = \"ok\";
        }

        import \"\\o\" as host {
            func imported();
        }

        export {
            f as \"\\o\",
            f as \"valid\",
        }

        func after() {}
    "};
	let case = TestCase::new(source);
	case.diagnostics().assert_none();
	assert_eq!(case.ast.items.len(), 4);
	assert!(case.strings.get("ok").is_none());
	assert!(case.strings.get(r#""\o""#).is_none());
	let statements = case.function_block(0);
	for index in [0, 1] {
		assert!(matches!(
			local_definition_value(statements, index),
			Expression::String
		));
	}
	let Item::ExportBlock { entries, .. } = case.item(2) else {
		panic!("expected export");
	};
	assert_eq!(entries.len(), 2);
}
