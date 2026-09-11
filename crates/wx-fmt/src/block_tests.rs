use super::tests::TestCase;
use super::*;
use wx_compiler::vfs;

fn checked_format(source: &str, width: u32, indent: u8) -> String {
	let case = TestCase::new(source);
	assert!(
		case.ast.diagnostics.is_empty(),
		"{:#?}\n{source}",
		case.ast.diagnostics
	);
	let config = RendererConfig {
		max_line_width: width,
		indent_width: indent,
		..RendererConfig::default()
	};
	let output = format(&case.ast, &case.interner, source, config);
	let reparsed = TestCase::new(&output);
	assert!(
		reparsed.ast.diagnostics.is_empty(),
		"{:#?}\n{output}",
		reparsed.ast.diagnostics
	);
	assert_eq!(
		format(&reparsed.ast, &reparsed.interner, &output, config),
		output,
		"idempotence: {source}"
	);
	for (before, after) in case.ast.items.iter().zip(&reparsed.ast.items) {
		if let (
			ast::Item::Function { block: a, .. },
			ast::Item::Function { block: b, .. },
		) = (&before.inner.inner, &after.inner.inner)
		{
			preserve_roles(&a.inner, &b.inner);
		}
	}
	output
}

// Compare nested block roles while allowing precisely the two authorized
// normalizations: non-final block-like separators and local definitions.
fn preserve_roles(a: &ast::Expression, b: &ast::Expression) {
	use ast::Expression as E;
	assert_eq!(std::mem::discriminant(a), std::mem::discriminant(b));
	match (a, b) {
		(E::Block { statements: a }, E::Block { statements: b }) => {
			assert_eq!(a.len(), b.len());
			let count = a.len();
			for (i, (a, b)) in a.iter().zip(b).enumerate() {
				match (&a.inner.inner, &b.inner.inner) {
					(
						ast::Statement::Expression(x),
						ast::Statement::Expression(y),
					) => {
						if i + 1 == count || !x.inner.is_block_like() {
							assert_eq!(
								a.separator.is_some(),
								b.separator.is_some(),
								"expression role changed"
							);
						}
						preserve_roles(&x.inner, &y.inner);
					}
					(
						ast::Statement::LocalDefinition { value: x, .. },
						ast::Statement::LocalDefinition { value: y, .. },
					) => {
						assert!(b.separator.is_some());
						preserve_roles(&x.inner, &y.inner);
					}
					_ => panic!("statement kind changed"),
				}
			}
		}
		(
			E::IfElse {
				condition: ac,
				then_block: at,
				else_block: ae,
			},
			E::IfElse {
				condition: bc,
				then_block: bt,
				else_block: be,
			},
		) => {
			preserve_roles(&ac.inner, &bc.inner);
			preserve_roles(&at.inner, &bt.inner);
			assert_eq!(ae.is_some(), be.is_some());
			if let (Some(a), Some(b)) = (ae, be) {
				preserve_roles(&a.inner, &b.inner);
			}
		}
		(
			E::Loop { block: a } | E::Label { block: a, .. },
			E::Loop { block: b } | E::Label { block: b, .. },
		) => preserve_roles(&a.inner, &b.inner),
		(
			E::Match {
				scrutinee: a,
				arms: aa,
			},
			E::Match {
				scrutinee: b,
				arms: ba,
			},
		) => {
			preserve_roles(&a.inner, &b.inner);
			assert_eq!(aa.len(), ba.len());
			for (a, b) in aa.iter().zip(ba) {
				preserve_roles(
					&a.inner.inner.body.inner,
					&b.inner.inner.body.inner,
				);
			}
		}
		(E::StructInit { fields: a, .. }, E::StructInit { fields: b, .. }) => {
			for (a, b) in a.iter().zip(b) {
				if let (Some(a), Some(b)) =
					(&a.inner.inner.value, &b.inner.inner.value)
				{
					preserve_roles(&a.inner, &b.inner);
				}
			}
		}
		(
			E::Return { value: a } | E::Break { value: a, .. },
			E::Return { value: b } | E::Break { value: b, .. },
		) => {
			if let (Some(a), Some(b)) = (a, b) {
				preserve_roles(&a.inner, &b.inner);
			}
		}
		_ => {}
	}
}

#[test]
fn executable_block_eligibility() {
	for (body, expected) in [
		("", "fn f() {}\n"),
		("foo()", "fn f() { foo() }\n"),
		("a + b", "fn f() { a + b }\n"),
		("foo();", "fn f() {\n    foo();\n}\n"),
		("local a = 1", "fn f() {\n    local a = 1;\n}\n"),
		("local a = 1;", "fn f() {\n    local a = 1;\n}\n"),
		("foo(); bar()", "fn f() {\n    foo();\n    bar()\n}\n"),
		("_ = foo()", "fn f() { _ = foo() }\n"),
		("return 1", "fn f() { return 1 }\n"),
		("return 1;", "fn f() {\n    return 1;\n}\n"),
		("break 1", "fn f() { break 1 }\n"),
		("continue", "fn f() { continue }\n"),
		("unreachable", "fn f() { unreachable }\n"),
	] {
		assert_eq!(
			checked_format(&format!("fn f() {{ {{ {body} }} }}"), 80, 4),
			format!(
				"fn f() {{\n    {}\n}}\n",
				expected
					.strip_prefix("fn f() ")
					.unwrap()
					.trim_end()
					.replace("\n", "\n    ")
			)
		);
	}
	for body in [
		"// leading\nfoo()",
		"foo() // trailing\n",
		"foo()\n// trailing\n",
		"// empty\n",
	] {
		let output = checked_format(&format!("fn f() {{ {body} }}"), 80, 4);
		assert!(output.starts_with("fn f() {\n"), "{output}");
		assert!(output.contains("//"));
	}
}

#[test]
fn function_bodies_always_break_without_expanding_short_signatures() {
	let flat = "fn f(x: i32) -> i32 { x }";
	for width in [flat.len() - 1, flat.len(), flat.len() + 1] {
		let output = checked_format(flat, width as u32, 4);
		assert!(output.ends_with("{\n    x\n}\n"), "{output}");
		assert!(output.starts_with("fn f(x: i32) -> i32 {"));
	}
	for body in ["foo()", "foo();", "a + b", "return 1", "_ = foo()"] {
		assert_eq!(
			checked_format(&format!("fn f() {{ {body} }}"), 120, 4),
			format!("fn f() {{\n    {body}\n}}\n"),
		);
	}
	assert_eq!(checked_format("fn f() {}", 120, 4), "fn f() {}\n");

	let output = checked_format(
		"fn many(first: i32, second: i32, third: i32) -> i32 { first }",
		36,
		4,
	);
	assert!(output.starts_with("fn many(\n"), "{output}");
	assert!(output.ends_with(") -> i32 {\n    first\n}\n"), "{output}");
	for body in ["if x { a() } else { b() }", "a(); b()"] {
		let output =
			checked_format(&format!("fn f(x: bool) {{ {body} }}"), 80, 4);
		assert!(output.starts_with("fn f(x: bool) {\n"), "{output}");
	}
	assert_eq!(
		checked_format("#[inline] fn f() { 1 }", 80, 4),
		"#[inline]\nfn f() {\n    1\n}\n"
	);
	let output =
		checked_format("fn f() { very_long_function_name(argument) }", 35, 2);
	assert_eq!(output, "fn f() {\n  very_long_function_name(argument)\n}\n");
}

#[test]
fn all_block_like_variants_and_separator_positions() {
	for expression in [
		"{ foo() }",
		"if true { foo() } else { bar() }",
		"loop { break 1 }",
		"label: { break :label 1 }",
		"Point::{ x: 1, y: 2 }",
		"if true {}",
		"{}",
		"loop {}",
		"label: {}",
		"Point::{}",
		"match n {}",
	] {
		for separator in ["", ";"] {
			let source = format!("fn f() {{ {expression}{separator} next() }}");
			let output = checked_format(&source, 120, 4);
			assert!(
				output.contains(&format!("    {expression};\n    next()")),
				"{output}"
			);
			let final_source = format!("fn f() {{ {expression}{separator} }}");
			assert_eq!(
				checked_format(&final_source, 120, 4),
				format!("fn f() {{\n    {expression}{separator}\n}}\n")
			);
		}
	}
	for expression in [
		"{ foo(); }",
		"if true { foo(); } else { bar() }",
		"loop { break 1; }",
		"label: { break :label 1; }",
		"match n { _ -> { 1 } }",
	] {
		for separator in ["", ";"] {
			let output = checked_format(
				&format!("fn f() {{ {expression}{separator} next() }}"),
				80,
				4,
			);
			assert!(output.contains("\n    }\n    next()"), "{output}");
			let output = checked_format(
				&format!("fn f() {{ {expression}{separator} }}"),
				80,
				4,
			);
			assert!(
				output.ends_with(&format!("    }}{separator}\n}}\n")),
				"{output}"
			);
		}
	}
}

#[test]
fn branch_coordination_and_comments() {
	for body in [
		"foo();",
		"prepare(); foo()",
		"// branch\nfoo()",
		"foo() // branch\n",
	] {
		for (a, b) in [(body, "bar()"), ("bar()", body)] {
			let output = checked_format(
				&format!(
					"fn f() {{ if true {{ {a} }} else {{ {b} }}; next() }}"
				),
				80,
				4,
			);
			assert!(output.contains("if true {\n"), "{output}");
			assert!(output.contains("} else {\n"), "{output}");
			assert!(output.contains("\n    }\n    next()"), "{output}");
		}
	}
	let output = checked_format(
		"fn f() { if true { foo() } // boundary\nnext() }",
		80,
		4,
	);
	assert!(
		output.contains("if true { foo() }; // boundary\n"),
		"{output}"
	);
	let output = checked_format(
		"fn f() { if true { foo(); }; // boundary\nnext() }",
		80,
		4,
	);
	assert!(output.contains("    } // boundary\n"), "{output}");
}

#[test]
fn flat_semicolon_participates_in_width() {
	for expression in [
		"if true { foo() } else { bar() }",
		"Point::{ x: 1, y: 2 }",
		"loop { break value }",
		"label: { break :label 1 }",
	] {
		let boundary = 4 + expression.len() + 1;
		for width in [boundary - 1, boundary, boundary + 1] {
			for separator in ["", ";"] {
				let output = checked_format(
					&format!("fn f() {{ {expression}{separator} next() }}"),
					width as u32,
					4,
				);
				if width >= boundary {
					assert!(
						output.contains(&format!("    {expression};\n")),
						"{output}"
					);
				} else {
					assert!(output.contains("\n    }\n    next()"), "{output}");
				}
			}
		}
	}
}

#[test]
fn diagnostics_and_tir_types_survive_formatting() {
	use std::collections::HashMap;
	use wx_compiler::tir::TIR;
	fn build(source: &str) -> (vfs::CompilationUnit, TIR) {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::new(HashMap::from([(
					vfs::AbsolutePath::new("/main.wx"),
					source.to_owned(),
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root);
		let tir = TIR::build(&mut graph);
		(graph, tir)
	}
	for (source, invalid) in [
		(
			"fn calculate() -> i32 { 1 } fn f() { calculate(); } export { f }",
			true,
		),
		(
			"fn effect() {} fn f(flag: bool) -> i32 { if flag { effect() } else { effect() }; if flag { effect(); }; local x: i32 = 1; x } export { f }",
			false,
		),
		(
			"fn f() -> i32 { local x: i32 = loop { break 1 }; x } export { f }",
			false,
		),
		("fn f() { local x: i32 = 1 } export { f }", false),
	] {
		let (_graph, before) = build(source);
		if !invalid {
			assert!(
				!before.diagnostics.iter().any(|d| d
					.code
					.as_deref()
					.is_some_and(|code| code.starts_with('E'))),
				"{:#?}",
				before.diagnostics
			);
		}
		assert_eq!(
			before
				.diagnostics
				.iter()
				.any(|d| d.code.as_deref() == Some("E1003")),
			invalid,
			"{:#?}",
			before.diagnostics
		);
		for width in [30, 120] {
			let output = checked_format(source, width, 4);
			let (_, after) = build(&output);
			let diagnostics = |tir: &TIR| {
				tir.diagnostics
					.iter()
					.map(|d| (d.severity, d.code.clone(), d.message.clone()))
					.collect::<Vec<_>>()
			};
			assert_eq!(diagnostics(&before), diagnostics(&after));
			assert_eq!(
				before
					.items
					.bodies
					.iter()
					.map(|b| b.block.ty)
					.collect::<Vec<_>>(),
				after
					.items
					.bodies
					.iter()
					.map(|b| b.block.ty)
					.collect::<Vec<_>>()
			);
		}
	}
}

#[test]
fn empty_constructs_use_broken_mode_at_tiny_widths() {
	for expression in [
		"{}",
		"if true {}",
		"loop {}",
		"label: {}",
		"Point::{}",
		"match n {}",
	] {
		let output =
			checked_format(&format!("fn f() {{ {expression} next() }}"), 1, 4);
		assert!(output.contains(&format!("    {expression}\n")), "{output}");
	}
}

#[test]
fn nested_mandatory_lines_prevent_flat_layout() {
	let output = checked_format(
		"fn f() { return if true { a(); } else { b() } }",
		120,
		4,
	);
	assert!(output.starts_with("fn f() {\n"), "{output}");
	assert!(output.contains("} else {\n"), "{output}");
	// The top-level rule deliberately allows an unterminated return whose
	// operand is block-like when the whole thing is physically one line.
	assert_eq!(
		checked_format(
			"fn f() { return if true { a() } else { b() } }",
			120,
			4
		),
		"fn f() {\n    return if true { a() } else { b() }\n}\n"
	);
	let output =
		checked_format("fn f() { wrap(Point::{ x: { a(); } }) }", 120, 4);
	assert!(output.starts_with("fn f() {\n"), "{output}");
}

#[test]
fn methods_and_generic_signatures_follow_the_function_rule() {
	for source in [
		"impl Point { fn f(self) -> i32 { 1 } }",
		"trait T { fn f(self) -> i32 { 1 } }",
		"impl T for Point { fn f(self) -> i32 { 1 } }",
	] {
		let output = checked_format(source, 80, 4);
		assert!(
			output.contains("fn f(self) -> i32 {\n        1\n    }"),
			"{output}"
		);
		let output = checked_format(source, 24, 4);
		assert!(output.contains("-> i32 {\n"), "{output}");
		assert!(!output.contains("{ 1 }"), "{output}");
	}
	let output = checked_format(
		"fn f<First: VeryLongBound, Second: AnotherVeryLongBound>(x: First) -> First { x }",
		40,
		4,
	);
	assert!(output.starts_with("fn f<\n"), "{output}");
	assert!(output.ends_with("{\n    x\n}\n"), "{output}");
}

#[test]
fn empty_branches_follow_the_owning_group_mode() {
	for expression in ["if test(a) {}", "if !test(a) {}", "match test(a) {}"] {
		for separator in ["", ";"] {
			let source = format!("fn f() {{ {expression}{separator} next() }}");
			let boundary = (4 + expression.len() + 1) as u32;
			for width in [boundary - 1, boundary, boundary + 1] {
				let output = checked_format(&source, width, 4);
				// Below the flat width, the owning group chooses Break even
				// though the nested condition and empty braces stay on one line.
				let semi = if width >= boundary { ";" } else { "" };
				assert_eq!(
					output,
					format!(
						"fn f() {{\n    {expression}{semi}\n    next()\n}}\n"
					)
				);
			}
			let output = checked_format(&source, 8, 4);
			assert!(!output.contains("{};"), "{output}");
		}
	}
}

#[test]
fn source_newlines_prevent_flat_blocks() {
	let output = checked_format(
		r#"fn f() { "one
two" }"#,
		120,
		4,
	);
	assert!(output.starts_with("fn f() {\n"), "{output}");
	assert!(output.contains("one\ntwo"), "{output}");
}
