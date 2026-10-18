use indoc::indoc;
use wx_compiler::ast;
use wx_compiler::vfs;

use super::*;

#[allow(unused)]
pub(super) struct TestCase {
	pub(super) interner: ast::StringInterner,
	files: vfs::Files,
	pub(super) ast: ast::AST,
}

impl TestCase {
	pub(super) fn new(source: &str) -> Self {
		// The builder's interner is the one the real pipeline parses with: it
		// has the keywords pre-interned, which `StringInterner::new()` does not.
		let builder = vfs::CompilationUnitBuilder::new();
		let mut interner = builder.strings;
		let mut files = builder.files;
		let file_id = files
			.add(
				"main.wx".to_string(),
				source.to_string(),
				vfs::FileOrigin::Local,
			)
			.unwrap();
		let ast = ast::Parser::parse(file_id, &files, &mut interner);

		TestCase {
			interner,
			files,
			ast,
		}
	}
}

#[test]
fn test_format_simple_function() {
	let case = TestCase::new(indoc! {"
        func add(a: i32, b: i32) -> i32 {
            a + b
        }

        export { add, add as \"plus\", minus }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 40,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func add(a: i32, b: i32) -> i32 {
                a + b
            }

            export {
                add,
                add as \"plus\",
                minus
            }
        "}
	);
}

/// `use` trees round-trip through the formatter unchanged, groups included.
/// They stay on one line even at a narrow `max_line_width`: a `use` names
/// things living elsewhere, so its length tracks the path being imported
/// rather than anything in this file.
#[test]
fn test_format_use_trees() {
	let source = indoc! {"
        use math::*;
        use math::add;
        use math::add as plus;
        use math::{add, sub};
        use math::{trig::{sin, cos}, ops::*};
    "};
	let case = TestCase::new(source);
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 40,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(output, source);
}

#[test]
fn test_format_import_block() {
	let case = TestCase::new(indoc! {"
        import \"math\" as math {
            func sqrt(f64) -> f64;
            func pow(base: f64, exponent: f64) -> f64;
            func log(x: string);
        }

        func main() {
            local x = sqrt(2.0);
            local y = pow(x, 2.0);
        }

        export { main }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            import \"math\" as math {
                func sqrt(f64) -> f64;
                func pow(base: f64, exponent: f64) -> f64;
                func log(x: string);
            }

            func main() {
                local x = sqrt(2.0);
                local y = pow(x, 2.0);
            }

            export {
                main
            }
        "}
	);
}

#[test]
fn test_format_single_import_function_stays_inline() {
	let case = TestCase::new(indoc! {"
        import \"console\" as console {
            func log(message: string);
         }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            import \"console\" as console {
                func log(message: string);
            }
        "}
	);
}

#[test]
fn test_format_module_items() {
	let case = TestCase::new(indoc! {"
        pub mod wasm {
            pub func answer() -> i32{
                42
            }

            func helper(  ) {}
        }

        mod math;
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            pub mod wasm {
                pub func answer() -> i32 {
                    42
                }

                func helper() {}
            }

            mod math;
        "}
	);
}

#[test]
fn test_format_impl_items() {
	let case = TestCase::new(indoc! {"
        impl i32 {
            #[inline]
            pub func double(self) -> i32 {
                self * 2
            }

            const ZERO: i32 = 0;
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            impl i32 {
                #[inline]
                pub func double(self) -> i32 {
                    self * 2
                }

                const ZERO: i32 = 0;
            }
        "}
	);
}

#[test]
fn test_format_trait_items() {
	let case = TestCase::new(indoc! {"
        pub trait Widget: Drawable + Sized {
            type Output: Show + Clone;

            const SIZE: u32;
            func render(self);

            #[inline]
            func grow(self, delta: u32) -> u32 {
                delta
            }
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            pub trait Widget: Drawable + Sized {
                type Output: Show + Clone;

                const SIZE: u32;

                func render(self);

                #[inline]
                func grow(self, delta: u32) -> u32 {
                    delta
                }
            }
        "}
	);
}

#[test]
fn test_format_where_clause_assoc_type_bound() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};

	// `Assoc: Bound` alongside the existing `Assoc = Type` equality form.
	assert_eq!(
		fmt(
			"func grow<Mem: Memory where { Size: Unsigned }>(mem: Mem) -> Mem {}"
		),
		"func grow<Mem: Memory where { Size: Unsigned }>(mem: Mem) -> Mem {}\n",
	);

	assert_eq!(
		fmt(
			"func f<Mem: Memory where { Size = u32, Size: Unsigned }>(mem: Mem) -> Mem {}"
		),
		"func f<Mem: Memory where { Size = u32, Size: Unsigned }>(mem: Mem) -> Mem {}\n",
	);
}

#[test]
fn test_format_qualified_path() {
	// `<Type as Trait>::item` in both type position (a function's return
	// type) and expression position (a call), with and without the `as
	// Trait` part.
	let case = TestCase::new(indoc! {"
        func grow<Mem: Memory>(mem: Mem, delta: Mem::Size) -> <Mem::Size as Unsigned>::Signed {
            <Thing as Greeter>::greet(mem)
        }

        func plain(x: <T>::Item) -> <T>::Item {
            <T>::method(x)
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func grow<Mem: Memory>(mem: Mem, delta: Mem::Size) -> <Mem::Size as Unsigned>::Signed {
                <Thing as Greeter>::greet(mem)
            }

            func plain(x: <T>::Item) -> <T>::Item {
                <T>::method(x)
            }
        "}
	);
}

#[test]
fn test_format_const_items() {
	let case = TestCase::new(indoc! {"
        const MAX: i32 = 100;

        const ANSWER = 42;
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            const MAX: i32 = 100;

            const ANSWER = 42;
        "}
	);
}

#[test]
fn test_format_enum_items() {
	let case = TestCase::new(indoc! {"
        enum Status: i32 {
            Foo,
            Bar = 1,
            Baz,
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            enum Status: i32 {
                Foo,
                Bar = 1,
                Baz,
            }
        "}
	);
}

#[test]
fn test_format_struct_items() {
	let case = TestCase::new(indoc! {"
        pub struct Point(pub x: i32, y: i32);

        struct Unit(value: f64);
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            pub struct Point(
                pub x: i32,
                y: i32,
            );

            struct Unit(
                value: f64,
            );
        "}
	);
}

#[test]
fn test_format_typeset_items() {
	let case = TestCase::new(indoc! {"
        #[tag = \"pointer_size\"]
        pub typeset PointerSize { u32, u64 }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            #[tag = \"pointer_size\"]
            pub typeset PointerSize { u32, u64 }
        "}
	);
}

#[test]
fn test_format_typeset_with_bound_clause() {
	let case = TestCase::new(indoc! {"
        typeset  Integer :  Add+Sub  { i32 , i64 }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            typeset Integer: Add + Sub { i32, i64 }
        "}
	);
}

/// Regression test for a formatter bug where `Item::Trait`/`Item::Enum`/
/// `Item::Const`/`Item::Global`'s dispatch arms in `build_item` destructured
/// `attributes` away via `..` and never passed it to their respective
/// `build_*_definition` functions — silently dropping any `#[...]` on those
/// four item kinds (unlike `func`/`struct`/`typeset`/`type`, which were never
/// affected). Caught by round-tripping `std/main.wx`'s `#[tag = "add"]`-style
/// operator traits through `wx format`.
#[test]
fn test_format_preserves_attributes_on_trait_enum_const_and_global() {
	let case = TestCase::new(indoc! {r#"
        #[tag = "add"]
        pub trait Add {
            func add(self: Self, rhs: Self) -> Self;
        }

        #[tag = "example"]
        enum Color { Red, Green, Blue }

        #[tag = "example"]
        pub const LIMIT: i32 = 10;

        #[tag = "example"]
        global mut counter: i32 = 0;
    "#});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {r#"
            #[tag = "add"]
            pub trait Add {
                func add(self: Self, rhs: Self) -> Self;
            }

            #[tag = "example"]
            enum Color {
                Red,
                Green,
                Blue,
            }

            #[tag = "example"]
            pub const LIMIT: i32 = 10;

            #[tag = "example"]
            global mut counter: i32 = 0;
        "#}
	);
}

#[test]
fn test_format_generic_struct_stays_inline() {
	let case = TestCase::new(indoc! {"
        struct Pair<A, B>(first: A, second: B);

        struct Wrapper<T>(value: T);
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            struct Pair<A, B>(
                first: A,
                second: B,
            );

            struct Wrapper<T>(
                value: T,
            );
        "}
	);
}

#[test]
fn test_format_generic_function() {
	let case = TestCase::new(indoc! {"
        func identity<T>(value: T) -> T {
            value
        }

        func zip<A, B: Clone + Debug>(a: A, b: B) -> A {
            a
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func identity<T>(value: T) -> T {
                value
            }

            func zip<A, B: Clone + Debug>(a: A, b: B) -> A {
                a
            }
        "}
	);
}

#[test]
fn test_format_struct_init() {
	let case = TestCase::new(indoc! {"
        func main() {
            local a = Point({ x: 1, y: 2 });
            local b = Point({ x: 1, y: 2, z: 3, w: 4, extra_long_field: 99 })
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 40,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func main() {
                local a = Point({ x: 1, y: 2 });
                local b = Point({
                    x: 1,
                    y: 2,
                    z: 3,
                    w: 4,
                    extra_long_field: 99,
                });
            }
        "}
	);
}

#[test]
fn test_format_struct_init_block_value() {
	let case = TestCase::new(indoc! {"
        func main() -> i32 {
            local p = Point({ x: g: block { break :g 5 }, y: 10 })
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func main() -> i32 {
                local p = Point({
                    x: g: block { break :g 5 },
                    y: 10,
                });
            }
        "}
	);
}

#[test]
fn test_format_local_patterns() {
	let case = TestCase::new(indoc! {"
        func f(p: Point, pair: (i32, i32)) {
            local x = 1;
            local mut y = 2;
            local _ = 3;
            local (a,b) = pair;
            local (mut c,_) = pair;
            local Point({x,y:renamed}) = p;
            local geom::Point({x,..}) = p;
            local Point({..}) = p;
            local (a,b): (i32,i32) = pair;
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func f(p: Point, pair: (i32, i32)) {
                local x = 1;
                local mut y = 2;
                local _ = 3;
                local (a, b) = pair;
                local (mut c, _) = pair;
                local Point({ x, y: renamed }) = p;
                local geom::Point({ x, .. }) = p;
                local Point({ .. }) = p;
                local (a, b): (i32, i32) = pair;
            }
        "}
	);
}

#[test]
fn test_format_impl_trait_items() {
	let case = TestCase::new(indoc! {"
        impl Iterator for Range {
            type Item = i32;

            func next(self) -> Self::Item {
                0
            }
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            impl Iterator for Range {
                type Item = i32;

                func next(self) -> Self::Item {
                    0
                }
            }
        "}
	);
}

#[test]
fn test_format_block_like_statement_semicolon() {
	// Flat non-final block-like expressions acquire a separator.
	let case = TestCase::new(indoc! {"
        func f() -> i32 {
            if true {}
            42
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func f() -> i32 {
                if true {};
                42
            }
        "}
	);

	// The same flat form results when the source already has a separator.
	let case = TestCase::new(indoc! {"
        func f() -> i32 {
            if true {};
            42
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            func f() -> i32 {
                if true {};
                42
            }
        "}
	);
}

#[test]
fn test_format_call_args_wrap() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};

	// Short call: stays on one line.
	assert_eq!(
		fmt("func f() { foo(1, 2, 3); }"),
		indoc! {"
            func f() {
                foo(1, 2, 3);
            }
        "},
	);

	// Long call: each argument on its own line.
	assert_eq!(
		fmt(
			"func f() { host::draw_rect(food_x * CELL_SIZE, food_y * CELL_SIZE, CELL_SIZE, CELL_SIZE, 0xFFFFFF00); }"
		),
		indoc! {"
            func f() {
                host::draw_rect(
                    food_x * CELL_SIZE,
                    food_y * CELL_SIZE,
                    CELL_SIZE,
                    CELL_SIZE,
                    0xFFFFFF00,
                );
            }
        "},
	);

	// Long method call wraps the same way.
	assert_eq!(
		fmt(
			"func f() { obj.render(food_x * CELL_SIZE, food_y * CELL_SIZE, CELL_SIZE, CELL_SIZE, 0xFFFFFF00); }"
		),
		indoc! {"
            func f() {
                obj.render(
                    food_x * CELL_SIZE,
                    food_y * CELL_SIZE,
                    CELL_SIZE,
                    CELL_SIZE,
                    0xFFFFFF00,
                );
            }
        "},
	);
}

#[test]
fn test_format_local_definition_wraps() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};

	// Short assignment stays on one line.
	assert_eq!(
		fmt("func f() { local x = 42; }"),
		indoc! {"
            func f() {
                local x = 42;
            }
        "},
	);

	// Long non-block-like value: breaks after =, value indented on next line.
	// Using FB_WIDTH (a named constant) makes the expression exceed 80 cols.
	assert_eq!(
		fmt(
			"memory heap: Memory32; func set_pixel(x: u32, y: u32) { local base: heap::*u8 = (fb_ptr() + (y * FB_WIDTH + x) * 3 + 12345) as heap::*u8; }"
		),
		indoc! {"
            memory heap: Memory32;

            func set_pixel(x: u32, y: u32) {
                local base: heap::*u8 =
                    (fb_ptr() + (y * FB_WIDTH + x) * 3 + 12345) as heap::*u8;
            }
        "},
	);

	// Block-like value (call by name): = stays on the same line, the braces break inside.
	assert_eq!(
		fmt(
			"func f() { local p = Point({ x: very_long_name_one, y: very_long_name_two, z: very_long_name_three }); }"
		),
		indoc! {"
            func f() {
                local p = Point({
                    x: very_long_name_one,
                    y: very_long_name_two,
                    z: very_long_name_three,
                });
            }
        "},
	);

	// A single-argument call whose argument is a (possibly nested) struct
	// literal hugs: no break after `=`, no extra indent from the call's own
	// parens — only the struct literal's own fields get one indent level.
	// Regression test for a bug where each level (the `local =` wrapper, the
	// call's argument-list wrapper, and every nested struct literal's own
	// wrapper) stacked its own indent on top of the others, since
	// the old `measure_flat` reported hard-line groups as short/"fits"
	// and `Indent` bumps the indent level regardless of whether the group
	// it's in is actually rendered Flat or Break.
	assert_eq!(
		fmt(
			"func f() { local p = alloc(Outer({ tag: 10001, inner: Inner({ id: 20002, timeout: 30003 }) })); }"
		),
		indoc! {"
            func f() {
                local p = alloc(Outer({
                    tag: 10001,
                    inner: Inner({ id: 20002, timeout: 30003 }),
                }));
            }
        "},
	);
}

#[test]
fn test_format_inline_blocks() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};

	// Single-statement if guard: fits → inline.
	assert_eq!(
		fmt(
			"memory heap: Memory32; func check(data: heap::&[u8]) -> bool { if data.len() < 4 { return false }; true }"
		),
		indoc! {"
            memory heap: Memory32;

            func check(data: heap::&[u8]) -> bool {
                if data.len() < 4 { return false };
                true
            }
        "},
	);

	// if-else as a value expression: both branches fit → inline.
	assert_eq!(
		fmt(
			"func pick(cond: bool) -> i32 { local x: i32 = if cond { 5 } else { 6 }; x }"
		),
		indoc! {"
            func pick(cond: bool) -> i32 {
                local x: i32 = if cond { 5 } else { 6 };
                x
            }
        "},
	);

	// Block that is too long to fit inline → multi-line.
	// indent=4, cond takes 43 chars → remaining=33; block flat=50 > 33 → Break.
	assert_eq!(
		fmt(
			"func f() -> i32 { if some_very_long_condition_variable { return some_very_long_return_value_here } 0 }"
		),
		indoc! {"
            func f() -> i32 {
                if some_very_long_condition_variable {
                    return some_very_long_return_value_here
                }
                0
            }
        "},
	);

	// Multi-statement block always breaks even when short.
	assert_eq!(
		fmt("func f() -> i32 { local x = 1; x }"),
		indoc! {"
            func f() -> i32 {
                local x = 1;
                x
            }
        "},
	);
}

#[test]
fn test_format_keeps_pub_on_memory_and_global() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};

	assert_eq!(
		fmt("pub memory heap: Memory32;"),
		"pub memory heap: Memory32;\n"
	);
	assert_eq!(
		fmt("#[memory_limits(min_pages = 4)] pub memory heap: Memory32;"),
		"#[memory_limits(min_pages = 4)]\npub memory heap: Memory32;\n",
	);
	assert_eq!(
		fmt("pub global mut g: u32 = 0;"),
		"pub global mut g: u32 = 0;\n"
	);
}

#[test]
fn test_format_memory_config() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};

	// No config block
	assert_eq!(fmt("memory heap: Memory32;"), "memory heap: Memory32;\n",);

	// min_pages only
	assert_eq!(
		fmt("#[memory_limits(min_pages = 4)] memory heap: Memory32;"),
		"#[memory_limits(min_pages = 4)]\nmemory heap: Memory32;\n",
	);

	// max_pages only
	assert_eq!(
		fmt("#[memory_limits(max_pages = 10)] memory heap: Memory32;"),
		"#[memory_limits(max_pages = 10)]\nmemory heap: Memory32;\n",
	);

	// both fields
	assert_eq!(
		fmt(
			"#[memory_limits(min_pages = 1, max_pages = 10)] memory heap: Memory32;"
		),
		"#[memory_limits(min_pages = 1, max_pages = 10)]\nmemory heap: Memory32;\n",
	);
}

#[test]
fn test_format_binary_chain_breaks_at_line_limit() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};

	// Short chain: fits on one line, stays flat.
	assert_eq!(
		fmt("func f(a: i32, b: i32, c: i32) -> i32 { a | b | c }"),
		indoc! {"
            func f(a: i32, b: i32, c: i32) -> i32 {
                a | b | c
            }
        "},
	);

	// Long chain: exceeds 80 columns, each operand on its own line.
	assert_eq!(
		fmt(
			"memory heap: Memory32; func read(data: heap::&[u8], off: u32) -> i32 { (data[off] as i32) | ((data[off + 1] as i32) << 8) | ((data[off + 2] as i32) << 16) | ((data[off + 3] as i32) << 24) }"
		),
		indoc! {"
            memory heap: Memory32;

            func read(data: heap::&[u8], off: u32) -> i32 {
                (data[off] as i32)
                    | ((data[off + 1] as i32) << 8)
                    | ((data[off + 2] as i32) << 16)
                    | ((data[off + 3] as i32) << 24)
            }
        "},
	);
}

#[test]
fn test_format_comments_preserved() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	// File-header comment before first item.
	assert_eq!(
		fmt(indoc! {"
            // Framebuffer helpers
            const FB_WIDTH: u32 = 320;
            const FB_HEIGHT: u32 = 200;
        "}),
		indoc! {"
            // Framebuffer helpers
            const FB_WIDTH: u32 = 320;
            const FB_HEIGHT: u32 = 200;
        "},
	);

	// Comment between compact items.
	assert_eq!(
		fmt(indoc! {"
            const A: u32 = 1;
            // separator
            const B: u32 = 2;
        "}),
		indoc! {"
            const A: u32 = 1;
            // separator
            const B: u32 = 2;
        "},
	);

	// Comment with blank line before it between compact items.
	assert_eq!(
		fmt(indoc! {"
            const A: u32 = 1;

            // group B
            const B: u32 = 2;
        "}),
		indoc! {"
            const A: u32 = 1;

            // group B
            const B: u32 = 2;
        "},
	);

	// Comment between statements inside a function body.
	assert_eq!(
		fmt(indoc! {"
            func f() {
                local x: i32 = 1;
                // compute y
                local y: i32 = 2;
            }
        "}),
		indoc! {"
            func f() {
                local x: i32 = 1;
                // compute y
                local y: i32 = 2;
            }
        "},
	);

	// Comment as the first thing in a block, before any statement.
	assert_eq!(
		fmt(indoc! {"
            func f() -> i32 {
                // load value
                42
            }
        "}),
		indoc! {"
            func f() -> i32 {
                // load value
                42
            }
        "},
	);

	// Comment as the last thing in a block, after the final expression.
	assert_eq!(
		fmt(indoc! {"
            func f() -> i32 {
                42
                // load value
            }
        "}),
		indoc! {"
            func f() -> i32 {
                42
                // load value
            }
        "},
	);

	// Comment as the only content of an otherwise empty block.
	assert_eq!(
		fmt(indoc! {"
            func f() {
                // nothing here yet
            }
        "}),
		indoc! {"
            func f() {
                // nothing here yet
            }
        "},
	);

	// Truly empty block still collapses to `{}`.
	assert_eq!(fmt("func f() {}\n"), "func f() {}\n");

	// Doc comment preserved like a regular comment.
	assert_eq!(
		fmt(indoc! {"
            /// Returns the sum.
            func add(a: i32, b: i32) -> i32 {
                a + b
            }
        "}),
		indoc! {"
            /// Returns the sum.
            func add(a: i32, b: i32) -> i32 {
                a + b
            }
        "},
	);

	// Comment as the only content of an otherwise empty export block.
	assert_eq!(
		fmt(indoc! {"
            export {
                // heap
            }
        "}),
		indoc! {"
            export {
                // heap
            }
        "},
	);

	// Comment as the only content of an otherwise empty import block.
	assert_eq!(
		fmt(indoc! {"
            import \"env\" as env {
                // nothing yet
            }
        "}),
		indoc! {"
            import \"env\" as env {
                // nothing yet
            }
        "},
	);

	// Leading/gap/trailing comments around export entries.
	assert_eq!(
		fmt(indoc! {"
            func heap() -> i32 {
                1
            }
            func other() -> i32 {
                2
            }
            export {
                // leading comment
                heap,
                // middle comment
                other
                // trailing comment
            }
        "}),
		indoc! {"
            func heap() -> i32 {
                1
            }

            func other() -> i32 {
                2
            }

            export {
                // leading comment
                heap,
                // middle comment
                other
                // trailing comment
            }
        "},
	);

	// Truly empty export/import blocks collapse to one line, matching
	// every other empty brace body (struct/module/trait/enum/impl).
	assert_eq!(fmt("export {}\n"), "export {}\n");
	assert_eq!(
		fmt("import \"env\" as env {}\n"),
		"import \"env\" as env {}\n"
	);

	// Comment as the only content of an otherwise empty body, for every
	// other brace-bodied item kind.
	assert_eq!(
		fmt(indoc! {"
            struct Foo(
                // fields tbd
            );
        "}),
		indoc! {"
            struct Foo(
                // fields tbd
            );
        "},
	);
	assert_eq!(
		fmt(indoc! {"
            mod m {
                // nothing yet
            }
        "}),
		indoc! {"
            mod m {
                // nothing yet
            }
        "},
	);
	assert_eq!(
		fmt(indoc! {"
            trait T {
                // methods tbd
            }
        "}),
		indoc! {"
            trait T {
                // methods tbd
            }
        "},
	);
	assert_eq!(
		fmt(indoc! {"
            enum E {
                // variants tbd
            }
        "}),
		indoc! {"
            enum E {
                // variants tbd
            }
        "},
	);
	assert_eq!(
		fmt(indoc! {"
            struct Foo();
            impl Foo {
                // methods tbd
            }
        "}),
		indoc! {"
            struct Foo();

            impl Foo {
                // methods tbd
            }
        "},
	);
	assert_eq!(
		fmt(indoc! {"
            trait T {}
            struct Foo();
            impl T for Foo {
                // methods tbd
            }
        "}),
		indoc! {"
            trait T {}

            struct Foo();

            impl T for Foo {
                // methods tbd
            }
        "},
	);

	// Leading comment before the first (non-empty) item in an impl body —
	// regression test: `build_impl_item_list`'s gap-comment handling used
	// to only look between consecutive items (`index > 0`), so a comment
	// before the very first item had no gap to be found in and was
	// silently dropped.
	assert_eq!(
		fmt(indoc! {"
            struct Foo();
            impl Foo {
                // first method
                func bar(self: Self) -> Self {
                    self
                }
            }
        "}),
		indoc! {"
            struct Foo();

            impl Foo {
                // first method
                func bar(self: Self) -> Self {
                    self
                }
            }
        "},
	);

	// Same regression, for the first item in a trait body.
	assert_eq!(
		fmt(indoc! {"
            trait T {
                // first method
                func bar(self: Self) -> Self;
            }
        "}),
		indoc! {"
            trait T {
                // first method
                func bar(self: Self) -> Self;
            }
        "},
	);
}

#[test]
fn test_format_long_type_params_wrap() {
	let case = TestCase::new(indoc! {"
        pub func memory_copy<Size: PointerSize, SrcMem: Memory where {
            Size = Size
        }, DstMem: Memory where { Size = Size }>(dst: DstMem::*u8, src: SrcMem::&u8, len: Size) {}
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            pub func memory_copy<
                Size: PointerSize,
                SrcMem: Memory where { Size = Size },
                DstMem: Memory where { Size = Size },
            >(dst: DstMem::*u8, src: SrcMem::&u8, len: Size) {}
        "},
	);
}

#[test]
fn test_format_address_of() {
	let case = TestCase::new(indoc! {r#"
        func f(ptr: &i32) {
            local a = ptr.*.&;
        }
    "#});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {r#"
            func f(ptr: &i32) {
                local a = ptr.*.&;
            }
        "#}
	);
}

#[test]
fn test_format_impl_trait_multi_segment() {
	// Multi-segment trait name in `impl a::b::Trait for Type` must be
	// rendered with `::` separators (exercises build_path_segments for
	// the ImplTrait trait_name field).
	let case = TestCase::new(indoc! {"
        impl module::Drawable for Point {
            func draw(self) {}
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            impl module::Drawable for Point {
                func draw(self) {}
            }
        "}
	);
}

#[test]
fn test_format_impl_trait_generic_type_params() {
	// Regression test: build_impl_trait_definition previously dropped the
	// impl's own type_params (e.g. `impl<T> Trait for Type<T>` lost `<T>`),
	// silently changing the code's meaning.
	let case = TestCase::new(indoc! {"
        impl<T> Trait for Wrapper<T> {
            func get(self) -> T {
                self.value
            }
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert_eq!(
		output,
		indoc! {"
            impl<T> Trait for Wrapper<T> {
                func get(self) -> T {
                    self.value
                }
            }
        "}
	);
}

#[test]
fn test_format_deep_indent_past_max_width_does_not_panic() {
	// Regression test: once accumulated indentation alone exceeds
	// max_line_width, Renderer::render_node's Group arm computed
	// `max_line_width - position`, underflowing (panicking in debug builds).
	// It must saturate to 0 (always break) instead.
	let case = TestCase::new(indoc! {"
        func f() {
          if true {
            if true {
              if true {
                if true {
                  local x = 1 + 2;
                }
              }
            }
          }
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig {
			max_line_width: 10,
			indent_width: 4,
			trailing_comma: true,
		},
	);
	assert!(!output.is_empty());
}

/// A comment keeps the line the author put it on. Whether it trails the code
/// before it or owns its line is decided purely by whether a newline separates
/// them in the source — never by how wide the result is, the same rule rustfmt
/// and Prettier use. Moving a comment across a line boundary would silently
/// change which item it appears to document.
#[test]
fn test_format_trailing_comments_keep_their_line() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	// Every construct with a list of entries: items, struct fields, enum
	// variants, impl members, match arms, export entries, block statements.
	// Each keeps a comment trailing the entry, a comment owning its own line,
	// and a comment after the last entry.
	let source = indoc! {"
        // File header.

        const A: u32 = 1; // trailing on item
        const B: u32 = 2;

        struct S(
            // leading on first field
            x: u32, // trailing on field
            y: u32,
            // own-line before closing brace
        );

        enum E: u32 {
            A = 0, // trailing on variant
            B = 1,
        }

        impl S {
            // leading on first member
            func a(self) -> u32 {
                self.x
            } // trailing on member

            func b(self) -> u32 {
                self.y
            }
        }

        func g(v: u32) -> u32 {
            local a = 1; // trailing on statement

            // own-line, documents b
            local b = 2;
            match v {
                0 -> { a }, // trailing on arm
                // own-line before arm
                _ -> { b },
            }
            // own-line before closing brace
        }

        export {
            // leading on first entry
            g, // trailing on entry
        }

        const LAST: u32 = 4; // trailing after the last item
        // own-line at end of file
    "};

	// Nothing is dropped, nothing changes line — the source is already in
	// normal form, so formatting is the identity.
	assert_eq!(fmt(source), source);
	// ...and stays that way on a second pass.
	assert_eq!(fmt(&fmt(source)), source);
}

/// A doc comment documents whatever follows it, so it never gets pulled up
/// onto the previous line even when nothing but spaces separates the two.
#[test]
fn test_format_doc_comment_never_trails() {
	let case = TestCase::new(
		"const A: u32 = 1; /// Documents B.\nconst B: u32 = 2;\n",
	);
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig::default(),
	);
	assert_eq!(
		output,
		indoc! {"
            const A: u32 = 1;
            /// Documents B.
            const B: u32 = 2;
        "},
	);
}

/// An item's attributes sit *outside* its span, so the region a gap measures
/// for blank lines runs from the end of the previous entry all the way past
/// the `#[...]` lines to the item's own `span.start`. Only the whitespace in
/// that region counts as a blank line — the newline ending an attribute's line
/// must not, or a blank line appears between a doc comment and its item.
///
/// Blank lines the author actually wrote are still preserved, wherever they
/// fall relative to the attribute, matching rustfmt (verified against it: it
/// keeps all of these and only collapses runs of two or more to one).
#[test]
fn test_format_blank_lines_around_attributes() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	// No blank anywhere the author didn't write one — the regression: the
	// attribute's own newline used to read as a blank line after the doc.
	let glued = indoc! {"
        /// Doc line one.
        /// Doc line two.
        #[inline]
        pub func f() -> u32 {
            1
        }
    "};
	assert_eq!(fmt(glued), glued);

	// A blank the author did write, on either side of the attribute, survives.
	let spaced = indoc! {"
        /// Doc, then a blank, then the attribute.

        #[inline]
        pub func f() -> u32 {
            1
        }
    "};
	assert_eq!(fmt(spaced), spaced);

	// And a blank between two plain items is still kept — the region there
	// opens with the previous item's `;`, which is not whitespace either.
	let items = indoc! {"
        const A: u32 = 1;

        #[inline]
        pub func f() -> u32 {
            1
        }
    "};
	assert_eq!(fmt(items), items);
}

/// No line ends in whitespace — in particular a blank line between two
/// indented statements is bare, not the previous line's indent.
#[test]
fn test_format_no_trailing_whitespace() {
	let case = TestCase::new(indoc! {"
        func f() -> i32 {
            local a = 1;

            a
        }
    "});
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig::default(),
	);
	assert!(
		!output.lines().any(|line| line.ends_with(' ')),
		"line ends in whitespace:\n{output:?}",
	);
}

/// Nothing trails the token that *opens* a list. A comment written after `{`
/// documents the body, not the opener, so it wraps onto its own line — for
/// every construct alike, which is what rustfmt does (verified against it:
/// `mod`, `struct`, `enum`, `impl`, a block and `match` all wrap).
///
/// This is the one place the same-line rule does not apply, because the code
/// on that line is the opener rather than an entry of the list.
#[test]
fn test_format_comment_after_a_list_opener_wraps() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	let source = indoc! {"
        mod inner { // opens a `mod`
            pub const A: u32 = 1;
        }

        struct S( // opens a `struct`
            x: u32,
        );

        enum E: u32 { // opens an `enum`
            A = 0,
        }

        impl S { // opens an `impl`
            func a(self) -> u32 {
                self.x
            }
        }

        import \"env\" as env { // opens an `import`
            func h() -> u32;
        }

        func g(v: u32) -> u32 { // opens a block
            match v { // opens a `match`
                _ -> { v },
            }
        }

        trait T { // opens a `trait`
            func t(self) -> u32;
        }

        export { // opens an `export`
            g,
        }
    "};

	let expected = indoc! {"
        mod inner {
            // opens a `mod`
            pub const A: u32 = 1;
        }

        struct S(
            // opens a `struct`
            x: u32,
        );

        enum E: u32 {
            // opens an `enum`
            A = 0,
        }

        impl S {
            // opens an `impl`
            func a(self) -> u32 {
                self.x
            }
        }

        import \"env\" as env {
            // opens an `import`
            func h() -> u32;
        }

        func g(v: u32) -> u32 {
            // opens a block
            match v {
                // opens a `match`
                _ -> { v },
            }
        }

        trait T {
            // opens a `trait`
            func t(self) -> u32;
        }

        export {
            // opens an `export`
            g,
        }
    "};

	assert_eq!(fmt(source), expected);
	// Wrapping happens once: the result is already in normal form.
	assert_eq!(fmt(expected), expected);
}

/// The comment that motivated the same-line rule in the first place: one
/// sitting after an ordinary, non-block entry. Wrapping opener comments must
/// not pull these down with them.
#[test]
fn test_format_trailing_comment_after_a_non_block_item_is_kept() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	let source = indoc! {"
        const X: i32 = 5; // documents X, not Y
        const Y: i32 = 6;

        struct S(
            x: u32, // documents x
            y: u32,
        );

        func g() -> i32 {
            local a = 1; // documents a
            a
        }
    "};

	assert_eq!(fmt(source), source);
	assert_eq!(fmt(&fmt(source)), source);
}

/// `trait` bodies were the one list with no comment handling of their own at
/// all: a comment trailing a member was reattached to the next one, and a
/// comment after the last member was dropped on the floor.
#[test]
fn test_format_trait_body_comments_are_kept_in_place() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	let source = indoc! {"
        trait T {
            // opens the trait
            func a(self) -> u32; // trails a member

            // own-line before b
            func b(self) -> u32;
            // after the last member
        }
    "};

	assert_eq!(fmt(source), source);
	assert_eq!(fmt(&fmt(source)), source);
}

/// A file holding nothing but comments keeps them. Formatting never deletes a
/// comment, and "there are no items" is not an exception to that.
#[test]
fn test_format_comment_only_file_is_preserved() {
	let source = "// A header-only file.\n// Second line.\n";
	let case = TestCase::new(source);
	let output = format(
		&case.ast,
		&case.interner,
		&case.files.get(case.ast.file_id).unwrap().source,
		RendererConfig::default(),
	);
	assert_eq!(output, source);
}

/// The author's vertical whitespace is theirs wherever it falls — including
/// between two comments that lead the first entry of a list, not just between
/// comments further down it. rustfmt preserves these too.
#[test]
fn test_format_blank_line_between_leading_comments() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	let source = indoc! {"
        struct S(
            // one

            // two
            x: u32,
        );

        impl S {
            // one

            // two
            func a(self) -> u32 {
                self.x
            }
        }

        func g() -> u32 {
            // one

            // two
            1
        }
    "};

	assert_eq!(fmt(source), source);
	assert_eq!(fmt(&fmt(source)), source);
}

/// A body with no entries is still a list, and its comments go through the
/// same gap as any other — an opener on one side, the closing brace on the
/// other. So an empty body spaces its comments exactly like a body with one
/// entry in it, rather than collapsing the blank as it used to.
#[test]
fn test_format_empty_body_comments_match_a_non_empty_one() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	// The only difference between the two is the field. It must not be what
	// decides whether the blank line between the comments survives.
	let source = indoc! {"
        struct Empty(
            // one

            // two
        );

        struct HasAField(
            // one

            // two
            x: u32,
        );

        impl Empty {
            // one

            // two
        }

        func f() {
            // one

            // two
        }
    "};

	assert_eq!(fmt(source), source);
	assert_eq!(fmt(&fmt(source)), source);
}

/// A blank line right after an opener is dropped — there is nothing above it
/// for it to separate the body from. Matches rustfmt, which removes it while
/// keeping blank lines everywhere else.
#[test]
fn test_format_no_blank_line_after_a_list_opener() {
	let fmt = |src: &str| -> String {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig::default(),
		)
	};

	let source = indoc! {"
        struct S(

            // separated from the brace
            x: u32,
        );

        impl S {

            func a(self) -> u32 {
                self.x
            }
        }

        func g() -> u32 {

            1
        }
    "};

	let expected = indoc! {"
        struct S(
            // separated from the brace
            x: u32,
        );

        impl S {
            func a(self) -> u32 {
                self.x
            }
        }

        func g() -> u32 {
            1
        }
    "};

	assert_eq!(fmt(source), expected);
	assert_eq!(fmt(expected), expected);
}

#[test]
fn export_aliases_preserve_their_quoted_source_spelling() {
	let fmt = |src: &str| {
		let case = TestCase::new(src);
		format(
			&case.ast,
			&case.interner,
			&case.files.get(case.ast.file_id).unwrap().source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};
	let source = r#"export { f as "line\n", f as "slash\\n", f as "quote\"" }
"#;
	let formatted = fmt(source);
	assert!(formatted.contains(r#""line\n""#));
	assert!(formatted.contains(r#""slash\\n""#));
	assert!(formatted.contains(r#""quote\"""#));
	assert_eq!(fmt(&formatted), formatted);
}

#[test]
fn raw_ast_strings_preserve_original_spelling_when_formatted() {
	let fmt = |source: &str| {
		let case = TestCase::new(source);
		format(
			&case.ast,
			&case.interner,
			source,
			RendererConfig {
				max_line_width: 80,
				indent_width: 4,
				trailing_comma: true,
			},
		)
	};
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
	let formatted = fmt(source);
	assert_eq!(formatted.matches(r#""line\nslash\\n""#).count(), 5);
	assert_eq!(fmt(&formatted), formatted);
}

// Formatting must keep what the author wrote readable as the same program:
// the output reparses cleanly, formats to itself, and every block keeps the
// role of its statements (see `preserve_roles`). The tests below go through
// `checked_format` so each case gets all three checks.

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
		(
			E::NamedCall { arguments: a, .. },
			E::NamedCall { arguments: b, .. },
		) => {
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
		("", "func f() {}\n"),
		("foo()", "func f() { foo() }\n"),
		("a + b", "func f() { a + b }\n"),
		("foo();", "func f() {\n    foo();\n}\n"),
		("local a = 1", "func f() {\n    local a = 1;\n}\n"),
		("local a = 1;", "func f() {\n    local a = 1;\n}\n"),
		("foo(); bar()", "func f() {\n    foo();\n    bar()\n}\n"),
		("_ = foo()", "func f() { _ = foo() }\n"),
		("return 1", "func f() { return 1 }\n"),
		("return 1;", "func f() {\n    return 1;\n}\n"),
		("break 1", "func f() { break 1 }\n"),
		("continue", "func f() { continue }\n"),
		("unreachable", "func f() { unreachable }\n"),
	] {
		assert_eq!(
			checked_format(
				&format!("func f() {{ block {{ {body} }} }}"),
				80,
				4
			),
			format!(
				"func f() {{\n    block {}\n}}\n",
				expected
					.strip_prefix("func f() ")
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
		let output = checked_format(&format!("func f() {{ {body} }}"), 80, 4);
		assert!(output.starts_with("func f() {\n"), "{output}");
		assert!(output.contains("//"));
	}
}

#[test]
fn function_bodies_always_break() {
	// A body always breaks, but never expands a short signature.
	{
		let flat = "func f(x: i32) -> i32 { x }";
		for width in [flat.len() - 1, flat.len(), flat.len() + 1] {
			let output = checked_format(flat, width as u32, 4);
			assert!(output.ends_with("{\n    x\n}\n"), "{output}");
			assert!(output.starts_with("func f(x: i32) -> i32 {"));
		}
		for body in ["foo()", "foo();", "a + b", "return 1", "_ = foo()"] {
			assert_eq!(
				checked_format(&format!("func f() {{ {body} }}"), 120, 4),
				format!("func f() {{\n    {body}\n}}\n"),
			);
		}
		assert_eq!(checked_format("func f() {}", 120, 4), "func f() {}\n");

		let output = checked_format(
			"func many(first: i32, second: i32, third: i32) -> i32 { first }",
			36,
			4,
		);
		assert!(output.starts_with("func many(\n"), "{output}");
		assert!(output.ends_with(") -> i32 {\n    first\n}\n"), "{output}");
		for body in ["if x { a() } else { b() }", "a(); b()"] {
			let output =
				checked_format(&format!("func f(x: bool) {{ {body} }}"), 80, 4);
			assert!(output.starts_with("func f(x: bool) {\n"), "{output}");
		}
		assert_eq!(
			checked_format("#[inline] func f() { 1 }", 80, 4),
			"#[inline]\nfunc f() {\n    1\n}\n"
		);
		let output = checked_format(
			"func f() { very_long_function_name(argument) }",
			35,
			2,
		);
		assert_eq!(
			output,
			"func f() {\n  very_long_function_name(argument)\n}\n"
		);
	}

	// Methods follow the same rule; generic signatures wrap before the body.
	{
		for source in [
			"impl Point { func f(self) -> i32 { 1 } }",
			"trait T { func f(self) -> i32 { 1 } }",
			"impl T for Point { func f(self) -> i32 { 1 } }",
		] {
			let output = checked_format(source, 80, 4);
			assert!(
				output.contains("func f(self) -> i32 {\n        1\n    }"),
				"{output}"
			);
			let output = checked_format(source, 24, 4);
			assert!(output.contains("-> i32 {\n"), "{output}");
			assert!(!output.contains("{ 1 }"), "{output}");
		}
		let output = checked_format(
			"func f<First: VeryLongBound, Second: AnotherVeryLongBound>(x: First) -> First { x }",
			40,
			4,
		);
		assert!(output.starts_with("func f<\n"), "{output}");
		assert!(output.ends_with("{\n    x\n}\n"), "{output}");
	}
}

#[test]
fn block_like_statement_separators() {
	// Every block-like form, with and without its optional `;`.
	{
		for expression in [
			"block { foo() }",
			"if true { foo() } else { bar() }",
			"loop { break 1 }",
			"label: block { break :label 1 }",
			"if true {}",
			"block {}",
			"loop {}",
			"label: block {}",
			"match n {}",
		] {
			for separator in ["", ";"] {
				let source =
					format!("func f() {{ {expression}{separator} next() }}");
				let output = checked_format(&source, 120, 4);
				assert!(
					output.contains(&format!("    {expression};\n    next()")),
					"{output}"
				);
				let final_source =
					format!("func f() {{ {expression}{separator} }}");
				assert_eq!(
					checked_format(&final_source, 120, 4),
					format!("func f() {{\n    {expression}{separator}\n}}\n")
				);
			}
		}
		for expression in [
			"block { foo(); }",
			"if true { foo(); } else { bar() }",
			"loop { break 1; }",
			"label: block { break :label 1; }",
			"match n { _ -> { 1 } }",
		] {
			for separator in ["", ";"] {
				let output = checked_format(
					&format!("func f() {{ {expression}{separator} next() }}"),
					80,
					4,
				);
				assert!(output.contains("\n    }\n    next()"), "{output}");
				let output = checked_format(
					&format!("func f() {{ {expression}{separator} }}"),
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

	// The flat `;` counts toward the width the line must fit.
	{
		for expression in [
			"if true { foo() } else { bar() }",
			"loop { break value }",
			"label: block { break :label 1 }",
		] {
			let boundary = 4 + expression.len() + 1;
			for width in [boundary - 1, boundary, boundary + 1] {
				for separator in ["", ";"] {
					let output = checked_format(
						&format!(
							"func f() {{ {expression}{separator} next() }}"
						),
						width as u32,
						4,
					);
					if width >= boundary {
						assert!(
							output.contains(&format!("    {expression};\n")),
							"{output}"
						);
					} else {
						assert!(
							output.contains("\n    }\n    next()"),
							"{output}"
						);
					}
				}
			}
		}
	}

	// Empty bodies follow the mode of the group that owns them.
	{
		for expression in [
			"if test(a) {}",
			"if !test(a) {}",
			"match test(a) {}",
			"loop {}",
			"block {}",
			"label: block {}",
		] {
			for separator in ["", ";"] {
				let source =
					format!("func f() {{ {expression}{separator} next() }}");
				let boundary = (4 + expression.len() + 1) as u32;
				for width in [boundary - 1, boundary, boundary + 1] {
					let output = checked_format(&source, width, 4);
					// Below the flat width, the owning group chooses Break even
					// though the nested condition and empty braces stay on one line.
					let semi = if width >= boundary { ";" } else { "" };
					assert_eq!(
						output,
						format!(
							"func f() {{\n    {expression}{semi}\n    next()\n}}\n"
						)
					);
				}
				let output = checked_format(&source, 8, 4);
				assert!(!output.contains("{};"), "{output}");
			}
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
					"func f() {{ if true {{ {a} }} else {{ {b} }}; next() }}"
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
		"func f() { if true { foo() } // boundary\nnext() }",
		80,
		4,
	);
	assert!(
		output.contains("if true { foo() }; // boundary\n"),
		"{output}"
	);
	let output = checked_format(
		"func f() { if true { foo(); }; // boundary\nnext() }",
		80,
		4,
	);
	assert!(output.contains("    } // boundary\n"), "{output}");
}

#[test]
fn mandatory_lines_prevent_flat_layout() {
	// A nested block that must break stops its parents going flat.
	{
		let output = checked_format(
			"func f() { return if true { a(); } else { b() } }",
			120,
			4,
		);
		assert!(output.starts_with("func f() {\n"), "{output}");
		assert!(output.contains("} else {\n"), "{output}");
		// The top-level rule deliberately allows an unterminated return whose
		// operand is block-like when the whole thing is physically one line.
		assert_eq!(
			checked_format(
				"func f() { return if true { a() } else { b() } }",
				120,
				4
			),
			"func f() {\n    return if true { a() } else { b() }\n}\n"
		);
		let output = checked_format(
			"func f() { wrap(Point({ x: block { a(); } })) }",
			120,
			4,
		);
		assert!(output.starts_with("func f() {\n"), "{output}");
	}

	// So does a newline inside a source token.
	{
		let output = checked_format(
			r#"func f() { "one
two" }"#,
			120,
			4,
		);
		assert!(output.starts_with("func f() {\n"), "{output}");
		assert!(output.contains("one\ntwo"), "{output}");
	}
}

/// Forms that exist only in the current syntax, each written the way the
/// formatter should leave it: a single `export`, `use` globs and groups,
/// structs with unnamed fields, patterns that mirror construction, calls by
/// name, memory-tagged and qualified paths, and an associated type default.
#[test]
fn test_format_current_syntax_forms() {
	let source = indoc! {"
        memory heap: Memory32;

        export main;

        use a::b::*;
        use a::{b, c::{d, e as f}, g::*};

        struct Pair(i32, pub u8);

        struct Unit();

        trait Tr {
            type A: Bound = u32;

            func f(self);
        }

        func main() {
            local Pair(a, ..) = p;
            local Named({ x, y: (q, _), .. }) = n;
            local v = obj.method::<u32>({ a: 1, b });
            local w = <Vec<u32> as Tr>::A::f::<u8>(x);
            local z = <u32>::MAX;
            local f: func(a: i32, i32) -> heap::*u8 = g;
        }
    "};
	let case = TestCase::new(source);
	assert!(
		case.ast.diagnostics.is_empty(),
		"{:#?}",
		case.ast.diagnostics
	);
	let output =
		format(&case.ast, &case.interner, source, RendererConfig::default());
	assert_eq!(
		output,
		indoc! {"
            memory heap: Memory32;

            export main;

            use a::b::*;
            use a::{b, c::{d, e as f}, g::*};

            struct Pair(
                i32,
                pub u8,
            );

            struct Unit();

            trait Tr {
                type A: Bound = u32;

                func f(self);
            }

            func main() {
                local Pair(a, ..) = p;
                local Named({ x, y: (q, _), .. }) = n;
                local v = obj.method::<u32>({ a: 1, b });
                local w = <Vec<u32> as Tr>::A::f::<u8>(x);
                local z = <u32>::MAX;
                local f: func(a: i32, i32) -> heap::*u8 = g;
            }
        "}
	);
}

// Disabled with the old `TIR::build` it drives: this checks that formatting
// changes neither the diagnostics nor the body types of a program. Port it onto
// the new `TypeContext` once function bodies are checked again.
// #[test]
// fn diagnostics_and_tir_types_survive_formatting() {
// 	use std::collections::HashMap;
// 	use wx_compiler::tir::TIR;
// 	fn build(source: &str) -> (vfs::CompilationUnit, TIR) {
// 		let mut builder = vfs::CompilationUnitBuilder::new();
// 		builder.load_stdlib();
// 		let root = builder
// 			.load_binary(
// 				vfs::AbsolutePath::new("/main.wx"),
// 				&vfs::VirtualFileSource::new(HashMap::from([(
// 					vfs::AbsolutePath::new("/main.wx"),
// 					source.to_owned(),
// 				)])),
// 			)
// 			.unwrap();
// 		let mut graph = builder.build(root);
// 		let tir = TIR::build(&mut graph);
// 		(graph, tir)
// 	}
// 	for (source, invalid) in [
// 		(
// 			"func calculate() -> i32 { 1 } func f() { calculate(); } export { f }",
// 			true,
// 		),
// 		(
// 			"func effect() {} func f(flag: bool) -> i32 { if flag { effect() } else { effect() }; if flag { effect(); }; local x: i32 = 1; x } export { f }",
// 			false,
// 		),
// 		(
// 			"func f() -> i32 { local x: i32 = loop { break 1 }; x } export { f }",
// 			false,
// 		),
// 		("func f() { local x: i32 = 1 } export { f }", false),
// 	] {
// 		let (_graph, before) = build(source);
// 		if !invalid {
// 			assert!(
// 				!before.diagnostics.iter().any(|d| d
// 					.code
// 					.as_deref()
// 					.is_some_and(|code| code.starts_with('E'))),
// 				"{:#?}",
// 				before.diagnostics
// 			);
// 		}
// 		assert_eq!(
// 			before.diagnostics.iter().any(|d| d.code.as_deref()
// 				== Some(DiagnosticCode::UnusedValue.code())),
// 			invalid,
// 			"{:#?}",
// 			before.diagnostics
// 		);
// 		for width in [30, 120] {
// 			let output = checked_format(source, width, 4);
// 			let (_, after) = build(&output);
// 			let diagnostics = |tir: &TIR| {
// 				tir.diagnostics
// 					.iter()
// 					.map(|d| (d.severity, d.code.clone(), d.message.clone()))
// 					.collect::<Vec<_>>()
// 			};
// 			assert_eq!(diagnostics(&before), diagnostics(&after));
// 			assert_eq!(
// 				before
// 					.items
// 					.bodies
// 					.iter()
// 					.map(|b| b.block.ty)
// 					.collect::<Vec<_>>(),
// 				after
// 					.items
// 					.bodies
// 					.iter()
// 					.map(|b| b.block.ty)
// 					.collect::<Vec<_>>()
// 			);
// 		}
// 	}
// }
