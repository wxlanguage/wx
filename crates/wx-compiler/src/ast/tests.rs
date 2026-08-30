use indoc::indoc;

use super::*;
use crate::testing::DiagnosticView;
use crate::vfs::{FileOrigin, Files};

/// A single parsed file, kept together with the [`Files`] its spans point
/// into so diagnostics can be rendered with source context.
///
/// Parser tests deliberately skip the package machinery — no stdlib, no
/// `CompilationUnit` — because nothing here needs it, and every extra stage
/// would be another way for a test to fail for reasons it is not about.
struct TestCase {
	interner: StringInterner,
	files: Files,
	ast: AST,
}

impl TestCase {
	fn new(source: &str) -> Self {
		let mut interner = StringInterner::new();
		let mut id_generator = DefIdGenerator::new();
		let mut files = Files::new();
		let file_id = files
			.add("main.wx".to_string(), source.to_string(), FileOrigin::Local)
			.unwrap();
		let ast =
			Parser::parse(file_id, &files, &mut interner, &mut id_generator);
		TestCase {
			interner,
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
		self.interner
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
	let case = TestCase::new(&format!("fn f() {{ {expression} }}"));
	case.diagnostics().assert_none();
	case.shape(statement_expression(case.function_block(0), 0))
}

/// Fallback naming for [`TestCase::shape`] — just enough to identify an
/// unexpected node without depending on `Debug`.
fn expression_kind(expression: &Expression) -> &'static str {
	match expression {
		Expression::Call { .. } => "call",
		Expression::MethodCall(_) => "method-call",
		Expression::ObjectAccess { .. } => "field",
		Expression::Grouping { .. } => "grouping",
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
		Item::Export { .. } => "an export block",
		Item::Import { .. } => "an import block",
		Item::Enum { .. } => "an enum",
		Item::InherentImpl { .. } => "an inherent impl",
		Item::TraitImpl { .. } => "a trait impl",
		Item::Struct { .. } => "a struct",
		Item::Memory { .. } => "a memory",
		Item::Const { .. } => "a const",
		Item::Module { .. } => "an inline module",
		Item::ModuleDeclaration { .. } => "a module declaration",
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
        fn add(a: i32, b: i32) -> i32 {
            a + b
        }

        memory MEM: Memory where { Size = u32 };
        global mut counter: i32 = 0;
        const MAX: i32 = 100;

        struct Point {
            pub x: i32,
            y: i32,
        }

        import \"env\" as env {
            fn log(message: string)
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

	assert_eq!(case.interner.resolve(name.inner), Some("Status"));
	assert!(matches!(
		repr.as_deref().map(|repr| &repr.inner),
		Some(TypeExpression::Path(p))
			if p.len() == 1
				&& case.interner.resolve(p[0].ident.inner) == Some("i32")
	));
	assert_eq!(variants.len(), 2);
}

#[test]
fn test_function_mut_param() {
	// mut on a parameter; mut local with compound assignment
	let case = TestCase::new(indoc! {"
        fn sum_down(mut n: i32) -> i32 {
            local mut acc: i32 = 0;
            acc += n;
            acc
        }
    "});
	case.diagnostics().assert_none();

	let param = &case.function_signature(0).params[0].inner.inner;
	assert_eq!(case.name(param.name.inner), "n");
	assert!(param.mut_span.is_some(), "`mut n` should record a mut span");

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
	// fn(…) -> … as a parameter type
	let case = TestCase::new(indoc! {"
        fn apply(f: fn(i32) -> i32, x: i32) -> i32 {
            f(x)
        }
    "});
	case.diagnostics().assert_none();

	let param = &case.function_signature(0).params[0].inner.inner;
	let ty = &param.ty.as_ref().expect("`f` is annotated").inner;
	let TypeExpression::Function { params, result } = ty else {
		panic!("expected a function type, got {ty:?}")
	};
	assert_eq!(params.len(), 1);
	assert!(result.is_some(), "`-> i32` should be recorded");
}

#[test]
fn test_type_expression_forms() {
	let case = TestCase::new(indoc! {"
        struct TypeForms {
            ptr: *u8,
            slice: &[u8],
            array: &[u8; 4],
            tuple: (i32, u32),
            namespaced: math::Number,
        }
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
            pub fn double(self) -> i32 {
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
	assert!(pub_span.is_some(), "`pub fn` should record a pub span");
	assert_eq!(attributes.len(), 1);
	assert_eq!(case.name(attributes[0].name.inner), "inline");
}

#[test]
fn test_impl_trait_for_type() {
	// impl Trait for Type — trait implementation block
	let case = TestCase::new(indoc! {"
        impl Drawable for Point {
            fn draw(self) {
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
	assert_eq!(trait_name.len(), 1);
	assert_eq!(case.name(trait_name[0].ident.inner), "Drawable");
	let TypeExpression::Path(segments) = &target.inner else {
		panic!("expected a path target")
	};
	assert_eq!(case.name(segments[0].ident.inner), "Point");
	assert_eq!(items.len(), 1);
}

#[test]
fn test_trait_items() {
	let case = TestCase::new(indoc! {"
        trait Widget: Drawable + Sized {
            const SIZE: u32;

            fn render(self);

            #[inline]
            fn grow(self, delta: u32) -> u32 {
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
	assert!(body.is_none(), "`fn render(self);` has no default body");

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
            pub fn render(self);
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
            pub fn render(self) {}
        }

        impl Button {
            pub fn area(self) -> u32 { 1 }
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
fn test_pub_not_applicable_to_memory_item_recovers() {
	let case = TestCase::new(indoc! {"
        pub memory MEM: Memory where { Size = u32 };
        fn add(a: i32, b: i32) -> i32 { a + b }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::VisibilityNotPermitted]);
	assert!(matches!(case.item(0), Item::Memory { .. }));
	assert!(matches!(case.item(1), Item::Function { .. }));
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
        fn add(a: i32, b: i32) -> i32 { a + b }
        export { add as \"wasm_add\" }
    "});
	case.diagnostics().assert_none();

	let Item::Export { entries, .. } = case.item(1) else {
		panic!("item 1 is {}, not an export block", item_kind(case.item(1)))
	};
	assert_eq!(entries.len(), 1);
	let entry = &entries[0].inner.inner;
	assert_eq!(case.name(entry.name.inner), "add");
	let alias = entry
		.alias
		.expect("`as \"wasm_add\"` should record an alias");
	// the alias keeps its quotes: it is the raw WASM export name
	assert_eq!(case.name(alias.inner), "\"wasm_add\"");
}

// ── Expressions ──────────────────────────────────────────────────────────────

#[test]
fn test_literals() {
	// float, char, and string literals (int is covered everywhere else)
	let case = TestCase::new(indoc! {"
        fn f() {
            local a = 2.75;
            local b = 'z';
            local c = \"hello\";
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	let Expression::Float { value } = local_definition_value(statements, 0)
	else {
		panic!("expected a float literal")
	};
	assert_eq!(*value, 2.75);
	// `Char` and `String` carry no payload — the text is recovered from the
	// span, so all the AST records is which kind of literal it was.
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
        fn sign(x: i32) -> i32 {
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
        fn sign(x: i32) -> i32 {
            match x {
                0 -> { 0 },
                1 -> { 1 },
                _ -> { -1 },
            }
        }
    "});
	case.diagnostics().assert_none();

	let statements = case.function_block(0);
	let Expression::Match { scrutinee, arms } =
		statement_expression(statements, 0)
	else {
		panic!("expected a match")
	};
	assert!(matches!(scrutinee.inner, Expression::Path(_)));
	assert_eq!(arms.len(), 3);

	// arm patterns are ordinary expressions at parse time; TIR is what
	// later decides which of them are valid patterns
	let patterns: Vec<&Expression> = arms
		.iter()
		.map(|arm| &arm.inner.inner.pattern.inner)
		.collect();
	assert!(matches!(patterns[0], Expression::Int { value: 0 }));
	assert!(matches!(patterns[1], Expression::Int { value: 1 }));
	assert!(
		matches!(patterns[2], Expression::Placeholder),
		"`_` should parse as a placeholder, got {:?}",
		patterns[2]
	);
}

#[test]
fn test_match_enum_variant_patterns() {
	let case = TestCase::new(indoc! {"
        enum FileDescriptor: u8 {
            StdIn,
            StdOut,
            StdErr,
        }

        fn name(fd: FileDescriptor) -> u8 {
            match fd {
                FileDescriptor::StdIn -> { 0 },
                FileDescriptor::StdOut -> { 1 },
                FileDescriptor::StdErr -> { 2 },
            }
        }
    "});
	case.diagnostics().assert_none();

	let statements = case.function_block(1);
	let Expression::Match { arms, .. } = statement_expression(statements, 0)
	else {
		panic!("expected a match")
	};
	assert_eq!(arms.len(), 3);

	// each arm pattern is a two-segment path `Enum::Variant`
	let variants: Vec<&str> = arms
		.iter()
		.map(|arm| {
			let Expression::Path(segments) = &arm.inner.inner.pattern.inner
			else {
				panic!("expected a path pattern")
			};
			assert_eq!(segments.len(), 2);
			assert_eq!(case.name(segments[0].ident.inner), "FileDescriptor");
			case.name(segments[1].ident.inner)
		})
		.collect();
	assert_eq!(variants, ["StdIn", "StdOut", "StdErr"]);
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
        fn f(x: i32) -> i32 {
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
        fn first_positive(mut n: i32) -> i32 {
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
        fn f(value: i32) {
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
        fn f() {
            std::io:
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidLabel]);
}

#[test]
fn test_struct_init() {
	// explicit fields, shorthand ({ field } == { field: field }), and empty
	let case = TestCase::new(indoc! {"
        fn make(x: i32, y: i32) {
            local full  = Point::{ x: x, y: y };
            local short = Point::{ x, y };
            local empty = Unit::{};
        }
    "});
	case.diagnostics().assert_none();
	let statements = case.function_block(0);

	let init = |index: usize| {
		let Expression::StructInit { path, fields } =
			local_definition_value(statements, index)
		else {
			panic!("expected a struct initialiser")
		};
		(path, fields)
	};

	// explicit `x: x` records a value; shorthand `x` leaves it `None`
	let (path, explicit) = init(0);
	assert_eq!(case.name(path[0].ident.inner), "Point");
	assert!(explicit.iter().all(|f| f.inner.inner.value.is_some()));

	let (_, shorthand) = init(1);
	assert_eq!(shorthand.len(), 2);
	assert!(
		shorthand.iter().all(|f| f.inner.inner.value.is_none()),
		"`Point::{{ x, y }}` is shorthand, so no explicit values"
	);
	let names: Vec<&str> = shorthand
		.iter()
		.map(|f| case.name(f.inner.inner.name.inner))
		.collect();
	assert_eq!(names, ["x", "y"]);

	let (path, empty) = init(2);
	assert_eq!(case.name(path[0].ident.inner), "Unit");
	assert!(empty.is_empty());
}

#[test]
fn test_generic_struct_init() {
	let case = TestCase::new(indoc! {"
        fn make(x: f32, y: f32) {
            local p = Point::<f32>::{ x: x, y: y };
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);
	let init = local_definition_value(stmts, 0);
	let Expression::StructInit { path, fields } = init else {
		panic!("expected StructInit");
	};
	// path must be a single-segment path with one type arg: `Point::<f32>`
	assert_eq!(path.len(), 1);
	assert_eq!(path[0].type_args.len(), 1);
	assert_eq!(fields.len(), 2);
}

#[test]
fn test_grouping_and_tuple_expressions() {
	let case = TestCase::new(indoc! {"
        fn shapes(x: i32, y: i32) {
            local grouped = (x);
            local single = (x,);
            local pair = (x, y);
        }
    "});

	case.diagnostics().assert_none();
	let statements = case.function_block(0);
	assert!(matches!(
		local_definition_value(statements, 0),
		Expression::Grouping { .. }
	));
	assert!(matches!(
		local_definition_value(statements, 1),
		Expression::Tuple { elements } if elements.len() == 1
	));
	assert!(matches!(
		local_definition_value(statements, 2),
		Expression::Tuple { elements } if elements.len() == 2
	));
}

#[test]
fn test_call_field_namespace() {
	// function call, field access, namespace access, unary ops
	let case = TestCase::new(indoc! {"
        fn ops(x: i32, p: Point) -> i32 {
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
	assert_eq!(case.name(member.inner), "x");

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
        fn f(a: i32, b: i32, c: i32) -> i32 {
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
        fn f(a: i32, b: i32, c: i32) -> i32 {
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
        fn arith(a: i32, b: i32) -> i32 { a + b as i32 }
        fn unary(x: i32) -> i32 { -x as i32 }
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
        fn f(p: Point) {
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
	assert_eq!(case.name(member.inner), "y");
	let Expression::ObjectAccess { member: inner, .. } = &object.inner else {
		panic!("`p.x.y` should nest as `(p.x).y`")
	};
	assert_eq!(case.name(inner.inner), "x");

	let Expression::ObjectAccess { object, member } =
		local_definition_value(statements, 1)
	else {
		panic!("expected object access")
	};
	assert_eq!(case.name(member.inner), "z");
	assert!(
		matches!(object.inner, Expression::MethodCall(_)),
		"`p.foo().z` should access the call's result"
	);
}

#[test]
fn test_address_of() {
	// ptr.*.& — address-of; value is Deref. Always produces a shared reference.
	let case = TestCase::new(indoc! {"
        fn f(ptr: &i32) {
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
        fn f(ptr: &Point) {
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
        fn f() {
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
        fn f() {
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
	assert!(matches!(
		local_definition_value(statements, 0),
		Expression::Float { value } if *value == 1e10
	));
	assert!(matches!(
		local_definition_value(statements, 1),
		Expression::Float { value } if *value == 3.4e2
	));
	assert!(matches!(
		local_definition_value(statements, 2),
		Expression::Float { value } if *value == 1e+5
	));
	assert!(matches!(
		local_definition_value(statements, 3),
		Expression::Float { value } if *value == 1.5e-3
	));
	assert!(matches!(
		local_definition_value(statements, 4),
		Expression::Float { value } if *value == 2E3
	));
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
        fn f(v: i32) {
            local x = v;
            local mut y = v;
            local _ = v;
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);

	assert!(matches!(
		local_definition_pattern(stmts, 0),
		Pattern::Binding { mut_span: None, name } if case.interner.resolve(name.inner) == Some("x")
	));
	assert!(matches!(
		local_definition_pattern(stmts, 1),
		Pattern::Binding { mut_span: Some(_), name } if case.interner.resolve(name.inner) == Some("y")
	));
	assert!(matches!(
		local_definition_pattern(stmts, 2),
		Pattern::Wildcard
	));
}

#[test]
fn test_pattern_tuple_destructuring() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) {
            local (a, b) = pair;
            local (mut c, _) = pair;
            local (x, (y, z)) = pair;
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);

	let Pattern::Tuple { elements } = local_definition_pattern(stmts, 0) else {
		panic!("expected tuple pattern")
	};
	assert_eq!(elements.len(), 2);
	assert!(matches!(
		&elements[0].inner.inner,
		Pattern::Binding { mut_span: None, .. }
	));
	assert!(matches!(
		&elements[1].inner.inner,
		Pattern::Binding { mut_span: None, .. }
	));

	let Pattern::Tuple { elements } = local_definition_pattern(stmts, 1) else {
		panic!("expected tuple pattern")
	};
	assert!(matches!(
		&elements[0].inner.inner,
		Pattern::Binding {
			mut_span: Some(_),
			..
		}
	));
	assert!(matches!(&elements[1].inner.inner, Pattern::Wildcard));

	let Pattern::Tuple { elements } = local_definition_pattern(stmts, 2) else {
		panic!("expected tuple pattern")
	};
	assert!(matches!(&elements[1].inner.inner, Pattern::Tuple { .. }));
}

#[test]
fn test_pattern_struct_destructuring() {
	let case = TestCase::new(indoc! {"
        fn f(p: Point) {
            local Point::{ x, y } = p;
            local Point::{ x: a, y: b } = p;
            local geom::Point::{ x, .. } = p;
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);

	let Pattern::Struct { path, fields, rest } =
		local_definition_pattern(stmts, 0)
	else {
		panic!("expected struct pattern")
	};
	assert_eq!(path.len(), 1);
	assert_eq!(case.interner.resolve(path[0].ident.inner), Some("Point"));
	assert!(rest.is_none());
	assert_eq!(fields.len(), 2);
	assert!(
		fields[0].inner.inner.pattern.is_none(),
		"shorthand field should have no sub-pattern"
	);
	assert!(
		fields[1].inner.inner.pattern.is_none(),
		"shorthand field should have no sub-pattern"
	);

	let Pattern::Struct { fields, .. } = local_definition_pattern(stmts, 1)
	else {
		panic!("expected struct pattern")
	};
	assert!(
		fields[0].inner.inner.pattern.is_some(),
		"renamed field should have sub-pattern"
	);
	assert!(
		fields[1].inner.inner.pattern.is_some(),
		"renamed field should have sub-pattern"
	);

	// A multi-segment path names a struct in another module, and `..` stands
	// in for the fields the pattern does not bind.
	let Pattern::Struct { path, fields, rest } =
		local_definition_pattern(stmts, 2)
	else {
		panic!("expected struct pattern")
	};
	assert_eq!(path.len(), 2);
	assert_eq!(case.interner.resolve(path[0].ident.inner), Some("geom"));
	assert_eq!(case.interner.resolve(path[1].ident.inner), Some("Point"));
	assert_eq!(fields.len(), 1);
	assert!(rest.is_some());
}

#[test]
fn test_pattern_with_type_annotation() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) {
            local (a, b): (i32, i32) = pair;
        }
    "});
	case.diagnostics().assert_none();
	let stmts = case.function_block(0);

	let Statement::LocalDefinition { pattern, ty, .. } = &stmts[0].inner.inner
	else {
		panic!("expected local definition")
	};
	assert!(matches!(pattern.inner, Pattern::Tuple { .. }));
	assert!(ty.is_some(), "type annotation should be present");
}

// ── Diagnostics ──────────────────────────────────────────────────────────────

#[test]
fn test_missing_semicolon_warns_but_parses() {
	let case = TestCase::new(indoc! {"
        fn f(x: i32) -> i32 {
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
        fn f() {
            local x: i32 = 1;
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::UnclosedDelimiter]);
	assert_eq!(case.function_block(0).len(), 1);
}

#[test]
fn test_invalid_function_param_type_reports_parse_error() {
	let case = TestCase::new(indoc! {"
        fn f(x: =) {}
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::UnexpectedToken]);
}

#[test]
fn test_invalid_integer_literal() {
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            99999999999999999999
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidLiteral]);
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
        fn f() -> f32 {
            1e
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidLiteral]);
	assert!(matches!(
		statement_expression(case.function_block(0), 0),
		Expression::Float { value } if *value == 0.0
	));
}

#[test]
fn test_incomplete_expression() {
	let case = TestCase::new(indoc! {"
        fn binary() -> i32 { 1 + }
        fn unary()  -> i32 { -   }
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
        fn f() {
            local fn = 1;
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
        fn attr() {}

        fn namespace_error(x: i32, y: i32) {
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
        fn f() {
            local x: i32
        }
        global y: i32
    "});
	let e0010_count = case
		.ast
		.diagnostics
		.iter()
		.filter(|d| d.code.as_deref() == Some("E0010"))
		.count();
	assert_eq!(
		e0010_count, 2,
		"expected one E0010 for local and one for global"
	);
	assert_eq!(case.ast.items.len(), 1);
	assert!(case.function_block(0).is_empty());
}

#[test]
fn test_missing_comma_between_struct_fields_warns_but_parses() {
	let case = TestCase::new(indoc! {"
        struct Pair {
            left: i32
            right: i32,
        }
    "});

	case.diagnostics()
		.assert_codes(&[DiagnosticCode::MissingSeparator]);
	assert_eq!(case.struct_fields(0).len(), 2);
}

#[test]
fn test_module_pub_items_and_associated_types() {
	let case = TestCase::new(indoc! {"
        pub mod math {
            pub fn zero() -> i32 {
                0
            }
        }

        pub struct Counter {
            value: i32,
        }

        pub trait Iterator {
            type Item: Show + Clone;
            fn next(self) -> Self::Item;
        }

        impl Iterator for Range {
            type Item = i32;

            fn next(self) -> Self::Item {
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
		items[0].inner.inner,
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

	let Item::ModuleDeclaration { pub_span, name } = case.item(0) else {
		panic!("expected external module")
	};

	assert!(pub_span.is_none());
	assert_eq!(case.interner.resolve(name.inner), Some("math"));
}

#[test]
fn test_chained_comparison_error() {
	let case = TestCase::new(indoc! {"
        fn f(a: i32, b: i32, c: i32) -> bool {
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
        fn zip<T, U: Show + Clone, V: Scalable>(left: T, middle: U, right: V) -> U {
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
        struct Pair<T, U> {
            first: T,
            second: U,
        }
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
	assert_eq!(case.interner.resolve(name.inner), Some("Pair"));
	assert_eq!(type_params.len(), 2);
	assert_eq!(case.interner.resolve(type_params[0].name.inner), Some("T"));
	assert!(type_params[0].bounds.is_none());
	assert_eq!(case.interner.resolve(type_params[1].name.inner), Some("U"));
	assert!(type_params[1].bounds.is_none());
	assert_eq!(fields.len(), 2);
}

#[test]
fn test_generic_struct_with_bounds() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<T: Add + Clone> {
            value: T,
        }
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
            fn log(message: string);
            global mut counter: i32;
            memory MEM: Memory where { Size = u32 };
        }
    "});

	case.diagnostics().assert_none();
	let Item::Import { alias, entries, .. } = case.item(0) else {
		panic!("expected import block")
	};
	assert_eq!(
		alias.as_ref().and_then(|a| case.interner.resolve(a.inner)),
		Some("host")
	);
	assert!(matches!(
		entries[0].inner.inner.declaration,
		ImportDeclaration::Function { .. }
	));
	assert!(matches!(
		entries[1].inner.inner.declaration,
		ImportDeclaration::Global {
			mut_span: Some(_),
			..
		}
	));
	assert!(matches!(
		entries[2].inner.inner.declaration,
		ImportDeclaration::Memory { .. }
	));
}

#[test]
fn test_turbofish_call() {
	let case = TestCase::new(indoc! {"
        fn main() {
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
        fn main(obj: Foo) {
            obj.transform::<i32>()
        }
    "});
	case.diagnostics().assert_none();

	let statements = case.function_block(0);
	// a method turbofish is a `MethodCall`, never a `TypeApplication`
	let Expression::MethodCall(call) = statement_expression(statements, 0)
	else {
		panic!("expected a method call")
	};
	assert_eq!(case.name(call.method.inner), "transform");
	assert_eq!(call.type_args.len(), 1);
	assert!(call.arguments.is_empty());
}

#[test]
fn test_generic_application_type_args() {
	let case = TestCase::new(indoc! {"
        struct Pair<T, U> {
            first: T,
            second: U,
        }
        fn make(x: Pair<i32, f64>) {}
    "});
	case.diagnostics().assert_none();
	let Item::Function { signature, .. } = case.item(1) else {
		panic!("expected function")
	};
	let param_ty = &signature.params[0].inner.inner.ty.as_ref().unwrap().inner;
	assert!(matches!(
		param_ty,
		TypeExpression::GenericApplication { args, .. } if args.len() == 2
	));
	if let TypeExpression::GenericApplication { args, .. } = param_ty {
		assert!(matches!(
			&args[0].inner,
			Spanned {
				inner: TypeExpression::Path(_),
				..
			}
		));
		assert!(matches!(
			&args[1].inner,
			Spanned {
				inner: TypeExpression::Path(_),
				..
			}
		));
	}
}

#[test]
fn test_double_right_arrow_split() {
	// Regression: `>>` in nested generics was eagerly lexed as `DoubleRightArrow`
	// instead of two separate `>` tokens. Test across type expressions and
	// turbofish in bounds.
	let case = TestCase::new(indoc! {"
        fn type_expr(x: Outer<Inner<u32>>) {}
        fn bound_turbofish<T: Wrapper::<Inner<u32>>>(t: T) {}
        fn method_turbofish(obj: Foo) { obj.transform::<Vec<u32>>() }
    "});
	case.diagnostics().assert_none();
}

#[test]
fn test_where_binding_parses_as_bound_with_bindings() {
	let case = TestCase::new(indoc! {"
        fn f<T: Memory where { Size = u32 }>(t: T) {}
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
            fn draw(self) {}
        }
    "});
	case.diagnostics().assert_none();
	let Item::TraitImpl { trait_name, .. } = case.item(0) else {
		panic!("expected ImplTrait")
	};
	assert_eq!(
		trait_name.len(),
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
        fn f(a: &[i32]) {
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
        fn f(a: &[i32]) {
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
        fn f() -> i32 {
            <Point as Show>::render()
        }

        fn g() -> i32 {
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
        fn f(a: <Point as Show>::Out, b: <Point>::Out) {}
    "});
	case.diagnostics().assert_none();

	let params = &case.function_signature(0).params;
	let ty = |index: usize| {
		&params[index]
			.inner
			.inner
			.ty
			.as_ref()
			.expect("annotated")
			.inner
	};
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

// ── keyword expressions ──────────────────────────────────────────────────────

#[test]
fn test_keyword_expressions() {
	let case = TestCase::new(indoc! {"
        fn f() -> bool {
            local t = true;
            local u = false;
            local v = unreachable;
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
	assert!(matches!(
		local_definition_value(statements, 2),
		Expression::Unreachable
	));

	// `return` carries an optional value
	let Expression::Return { value } = statement_expression(statements, 3)
	else {
		panic!("expected a return")
	};
	assert!(value.is_some(), "`return t` should record its value");
}

#[test]
fn test_bare_return_has_no_value() {
	let case = TestCase::new("fn f() { return; }");
	case.diagnostics().assert_none();
	let Expression::Return { value } =
		statement_expression(case.function_block(0), 0)
	else {
		panic!("expected a return")
	};
	assert!(value.is_none());
}

#[test]
fn test_turbofish_on_a_non_path_expression_is_a_type_application() {
	// A turbofish on a plain path attaches to the segment (see
	// `test_turbofish_call`); on anything else it becomes its own node.
	let case = TestCase::new(indoc! {"
        fn f() {
            local a = (g)::<i32>;
        }
    "});
	case.diagnostics().assert_none();
	let Expression::TypeApplication { args, .. } =
		local_definition_value(case.function_block(0), 0)
	else {
		panic!("expected a type application")
	};
	assert_eq!(args.len(), 1);
}

// ── remaining type expressions ───────────────────────────────────────────────

#[test]
fn test_infer_and_memory_tagged_types() {
	let case = TestCase::new(indoc! {"
        fn f(p: heap::*u8, s: heap::&[i32]) {
            local a: _ = 1;
        }
    "});
	case.diagnostics().assert_none();

	// a memory-tagged type names the memory its pointer or slice belongs to
	let params = &case.function_signature(0).params;
	for index in [0, 1] {
		let ty = &params[index]
			.inner
			.inner
			.ty
			.as_ref()
			.expect("annotated")
			.inner;
		let TypeExpression::MemoryTagged { memory, .. } = ty else {
			panic!("expected a memory-tagged type")
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
        import \"env\" {
            fn log(x: i32)
        }
    "});
	case.diagnostics().assert_none();

	let Item::Import { entries, .. } = case.item(0) else {
		panic!("item 0 is {}, not an import", item_kind(case.item(0)))
	};
	assert_eq!(entries.len(), 1);
	let ImportDeclaration::Function { signature, .. } =
		&entries[0].inner.inner.declaration
	else {
		panic!("expected an imported function")
	};
	assert_eq!(case.name(signature.name.inner), "log");
}

#[test]
fn test_bodyless_function_is_a_declaration() {
	// A `fn` with no block is an `Item::FunctionDeclaration` rather than an
	// `Item::Function` with an empty body — that split is what lets
	// `#[intrinsic]` and imported functions carry a signature and nothing else.
	let case = TestCase::new(indoc! {"
        #[intrinsic]
        fn raw_load(address: u32) -> i32;

        fn real() -> i32 { 1 }
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
        memory m: Memory where { Size = u32 };
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
	let case = TestCase::new("fn f() { local x: i32; }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::MissingInitializer]);
}

#[test]
fn test_path_in_pattern_position_reports() {
	// A path is only a pattern as a struct pattern, `Path::{ .. }`.
	let case = TestCase::new("fn f() { local Foo::Bar = 1; }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::InvalidPattern]);
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
	let case = TestCase::new("fn f() -> i32 { 1 @ 2 }");
	case.diagnostics().assert_codes(&[
		DiagnosticCode::MissingSeparator,
		DiagnosticCode::UnknownToken,
	]);
}

#[test]
fn test_a_run_of_unknown_characters_reports_once() {
	// Adjacent unknown characters coalesce into one run, so `@@@` is one
	// diagnostic rather than three...
	let case = TestCase::new("fn f() { @@@ }");
	case.diagnostics()
		.assert_codes(&[DiagnosticCode::UnknownToken]);

	// ...while separate runs stay separate.
	let case = TestCase::new("fn f() { @ } fn g() { $ }");
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
		"fn f() {} @",
		"fn f() -> i32 { 1 + @ 2 }",
		"fn f() -> i32 { g(@) }",
	] {
		let case = TestCase::new(source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnknownToken]);
	}
}
