use indoc::indoc;
use wx_compiler::ast;
use wx_compiler::vfs;

use super::*;

#[allow(unused)]
struct TestCase {
	interner: ast::StringInterner,
	files: vfs::Files,
	ast: ast::AST,
}

impl TestCase {
	fn new(source: &str) -> Self {
		let mut interner = ast::StringInterner::new();
		let mut files = vfs::Files::new();
		let file_id = files
			.add(
				"main.wx".to_string(),
				source.to_string(),
				vfs::FileOrigin::Local,
			)
			.unwrap();
		let mut id_generator = ast::DefIdGenerator::new();
		let ast = ast::Parser::parse(
			file_id,
			&files,
			&mut interner,
			&mut id_generator,
		);

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
        fn add(a: i32, b: i32) -> i32 {
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
            fn add(a: i32, b: i32) -> i32 {
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
            fn sqrt(f64) -> f64;
            fn pow(base: f64, exponent: f64) -> f64;
            fn log(x: string);
        }

        fn main() {
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
                fn sqrt(f64) -> f64;
                fn pow(base: f64, exponent: f64) -> f64;
                fn log(x: string);
            }

            fn main() {
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
            fn log(message: string);
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
                fn log(message: string);
            }
        "}
	);
}

#[test]
fn test_format_module_items() {
	let case = TestCase::new(indoc! {"
        pub mod wasm {
            pub fn answer() -> i32{
                42
            }

            fn helper(  ) {}
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
                pub fn answer() -> i32 {
                    42
                }

                fn helper() {}
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
            pub fn double(self) -> i32 {
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
                pub fn double(self) -> i32 {
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
            fn render(self);

            #[inline]
            fn grow(self, delta: u32) -> u32 {
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

                fn render(self);

                #[inline]
                fn grow(self, delta: u32) -> u32 {
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
			"fn grow<Mem: Memory where { Size: Unsigned }>(mem: Mem) -> Mem {}"
		),
		"fn grow<Mem: Memory where { Size: Unsigned }>(mem: Mem) -> Mem {}\n",
	);

	assert_eq!(
		fmt(
			"fn f<Mem: Memory where { Size = u32, Size: Unsigned }>(mem: Mem) -> Mem {}"
		),
		"fn f<Mem: Memory where { Size = u32, Size: Unsigned }>(mem: Mem) -> Mem {}\n",
	);
}

#[test]
fn test_format_qualified_path() {
	// `<Type as Trait>::item` in both type position (a function's return
	// type) and expression position (a call), with and without the `as
	// Trait` part.
	let case = TestCase::new(indoc! {"
        fn grow<Mem: Memory>(mem: Mem, delta: Mem::Size) -> <Mem::Size as Unsigned>::Signed {
            <Thing as Greeter>::greet(mem)
        }

        fn plain(x: <T>::Item) -> <T>::Item {
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
            fn grow<Mem: Memory>(mem: Mem, delta: Mem::Size) -> <Mem::Size as Unsigned>::Signed {
                <Thing as Greeter>::greet(mem)
            }

            fn plain(x: <T>::Item) -> <T>::Item {
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
        pub struct Point { pub x: i32, y: i32 }

        struct Unit { value: f64 }
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
            pub struct Point {
                pub x: i32,
                y: i32,
            }

            struct Unit {
                value: f64,
            }
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

/// Regression test for a formatter bug where `Item::Trait`/`Item::Enum`/
/// `Item::Const`/`Item::Global`'s dispatch arms in `build_item` destructured
/// `attributes` away via `..` and never passed it to their respective
/// `build_*_definition` functions — silently dropping any `#[...]` on those
/// four item kinds (unlike `fn`/`struct`/`typeset`/`type`, which were never
/// affected). Caught by round-tripping `std/main.wx`'s `#[tag = "add"]`-style
/// operator traits through `wx format`.
#[test]
fn test_format_preserves_attributes_on_trait_enum_const_and_global() {
	let case = TestCase::new(indoc! {r#"
        #[tag = "add"]
        pub trait Add {
            fn add(self: Self, rhs: Self) -> Self;
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
                fn add(self: Self, rhs: Self) -> Self;
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
        struct Pair<A, B> { first: A, second: B }

        struct Wrapper<T> { value: T }
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
            struct Pair<A, B> {
                first: A,
                second: B,
            }

            struct Wrapper<T> {
                value: T,
            }
        "}
	);
}

#[test]
fn test_format_generic_function() {
	let case = TestCase::new(indoc! {"
        fn identity<T>(value: T) -> T {
            value
        }

        fn zip<A, B: Clone + Debug>(a: A, b: B) -> A {
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
            fn identity<T>(value: T) -> T {
                value
            }

            fn zip<A, B: Clone + Debug>(a: A, b: B) -> A {
                a
            }
        "}
	);
}

#[test]
fn test_format_struct_init() {
	let case = TestCase::new(indoc! {"
        fn main() {
            local a = Point::{ x: 1, y: 2 };
            local b = Point::{ x: 1, y: 2, z: 3, w: 4, extra_long_field: 99 }
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
            fn main() {
                local a = Point::{ x: 1, y: 2 };
                local b = Point::{
                    x: 1,
                    y: 2,
                    z: 3,
                    w: 4,
                    extra_long_field: 99,
                }
            }
        "}
	);
}

#[test]
fn test_format_struct_init_block_value() {
	let case = TestCase::new(indoc! {"
        fn main() -> i32 {
            local p = Point::{ x: g: { break :g 5 }, y: 10 }
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
            fn main() -> i32 {
                local p = Point::{
                    x: g: { break :g 5 },
                    y: 10,
                }
            }
        "}
	);
}

#[test]
fn test_format_local_patterns() {
	let case = TestCase::new(indoc! {"
        fn f(p: Point, pair: (i32, i32)) {
            local x = 1;
            local mut y = 2;
            local _ = 3;
            local (a,b) = pair;
            local (mut c,_) = pair;
            local Point::{x,y:renamed} = p;
            local geom::Point::{x,..} = p;
            local Point::{..} = p;
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
            fn f(p: Point, pair: (i32, i32)) {
                local x = 1;
                local mut y = 2;
                local _ = 3;
                local (a, b) = pair;
                local (mut c, _) = pair;
                local Point::{ x, y: renamed } = p;
                local geom::Point::{ x, .. } = p;
                local Point::{ .. } = p;
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

            fn next(self) -> Self::Item {
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

                fn next(self) -> Self::Item {
                    0
                }
            }
        "}
	);
}

#[test]
fn test_format_block_like_statement_semicolon() {
	// Without explicit `;`: formatter does not add one after block-like statements.
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
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
            fn f() -> i32 {
                if true {}
                42
            }
        "}
	);

	// With explicit `;`: formatter preserves it so the user can visually
	// separate the block statement from the expression that follows.
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
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
            fn f() -> i32 {
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
		fmt("fn f() { foo(1, 2, 3); }"),
		indoc! {"
            fn f() {
                foo(1, 2, 3);
            }
        "},
	);

	// Long call: each argument on its own line.
	assert_eq!(
		fmt(
			"fn f() { host::draw_rect(food_x * CELL_SIZE, food_y * CELL_SIZE, CELL_SIZE, CELL_SIZE, 0xFFFFFF00); }"
		),
		indoc! {"
            fn f() {
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
			"fn f() { obj.render(food_x * CELL_SIZE, food_y * CELL_SIZE, CELL_SIZE, CELL_SIZE, 0xFFFFFF00); }"
		),
		indoc! {"
            fn f() {
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
		fmt("fn f() { local x = 42; }"),
		indoc! {"
            fn f() {
                local x = 42;
            }
        "},
	);

	// Long non-block-like value: breaks after =, value indented on next line.
	// Using FB_WIDTH (a named constant) makes the expression exceed 80 cols.
	assert_eq!(
		fmt(
			"memory heap: Memory where { Size = u32 }; fn set_pixel(x: u32, y: u32) { local base: heap::*u8 = (fb_ptr() + (y * FB_WIDTH + x) * 3 + 12345) as heap::*u8; }"
		),
		indoc! {"
            memory heap: Memory where { Size = u32 };

            fn set_pixel(x: u32, y: u32) {
                local base: heap::*u8 =
                    (fb_ptr() + (y * FB_WIDTH + x) * 3 + 12345) as heap::*u8;
            }
        "},
	);

	// Block-like value (struct init): = stays on the same line, struct breaks inside.
	assert_eq!(
		fmt(
			"fn f() { local p = Point::{ x: very_long_name_one, y: very_long_name_two, z: very_long_name_three }; }"
		),
		indoc! {"
            fn f() {
                local p = Point::{
                    x: very_long_name_one,
                    y: very_long_name_two,
                    z: very_long_name_three,
                };
            }
        "},
	);

	// A single-argument call whose argument is a (possibly nested) struct
	// literal hugs: no break after `=`, no extra indent from the call's own
	// parens — only the struct literal's own fields get one indent level.
	// Regression test for a bug where each level (the `local =` wrapper, the
	// call's argument-list wrapper, and every nested struct literal's own
	// wrapper) stacked its own indent on top of the others, since
	// `measure_flat` reports groups containing a hard line as short/"fits"
	// and `Indent` bumps the indent level regardless of whether the group
	// it's in is actually rendered Flat or Break.
	assert_eq!(
		fmt(
			"fn f() { local p = alloc(Outer::{ tag: 1, inner: Inner::{ id: 2, timeout: 3 } }); }"
		),
		indoc! {"
            fn f() {
                local p = alloc(Outer::{
                    tag: 1,
                    inner: Inner::{ id: 2, timeout: 3 },
                });
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
			"memory heap: Memory where { Size = u32 }; fn check(data: heap::&[u8]) -> bool { if data.len() < 4 { return false }; true }"
		),
		indoc! {"
            memory heap: Memory where { Size = u32 };

            fn check(data: heap::&[u8]) -> bool {
                if data.len() < 4 { return false };
                true
            }
        "},
	);

	// if-else as a value expression: both branches fit → inline.
	assert_eq!(
		fmt(
			"fn pick(cond: bool) -> i32 { local x: i32 = if cond { 5 } else { 6 }; x }"
		),
		indoc! {"
            fn pick(cond: bool) -> i32 {
                local x: i32 = if cond { 5 } else { 6 };
                x
            }
        "},
	);

	// Block that is too long to fit inline → multi-line.
	// indent=4, cond takes 43 chars → remaining=33; block flat=50 > 33 → Break.
	assert_eq!(
		fmt(
			"fn f() -> i32 { if some_very_long_condition_variable { return some_very_long_return_value_here } 0 }"
		),
		indoc! {"
            fn f() -> i32 {
                if some_very_long_condition_variable {
                    return some_very_long_return_value_here
                }
                0
            }
        "},
	);

	// Multi-statement block always breaks even when short.
	assert_eq!(
		fmt("fn f() -> i32 { local x = 1; x }"),
		indoc! {"
            fn f() -> i32 {
                local x = 1;
                x
            }
        "},
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
	assert_eq!(
		fmt("memory heap: Memory where { Size = u32 };"),
		"memory heap: Memory where { Size = u32 };\n",
	);

	// min_pages only
	assert_eq!(
		fmt(
			"#[memory_limits(min_pages = 4)] memory heap: Memory where { Size = u32 };"
		),
		"#[memory_limits(min_pages = 4)]\nmemory heap: Memory where { Size = u32 };\n",
	);

	// max_pages only
	assert_eq!(
		fmt(
			"#[memory_limits(max_pages = 10)] memory heap: Memory where { Size = u32 };"
		),
		"#[memory_limits(max_pages = 10)]\nmemory heap: Memory where { Size = u32 };\n",
	);

	// both fields
	assert_eq!(
		fmt(
			"#[memory_limits(min_pages = 1, max_pages = 10)] memory heap: Memory where { Size = u32 };"
		),
		"#[memory_limits(min_pages = 1, max_pages = 10)]\nmemory heap: Memory where { Size = u32 };\n",
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
		fmt("fn f(a: i32, b: i32, c: i32) -> i32 { a | b | c }"),
		indoc! {"
            fn f(a: i32, b: i32, c: i32) -> i32 {
                a | b | c
            }
        "},
	);

	// Long chain: exceeds 80 columns, each operand on its own line.
	assert_eq!(
		fmt(
			"memory heap: Memory where { Size = u32 }; fn read(data: heap::&[u8], off: u32) -> i32 { (data[off] as i32) | ((data[off + 1] as i32) << 8) | ((data[off + 2] as i32) << 16) | ((data[off + 3] as i32) << 24) }"
		),
		indoc! {"
            memory heap: Memory where { Size = u32 };

            fn read(data: heap::&[u8], off: u32) -> i32 {
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
            fn f() {
                local x: i32 = 1;
                // compute y
                local y: i32 = 2;
            }
        "}),
		indoc! {"
            fn f() {
                local x: i32 = 1;
                // compute y
                local y: i32 = 2;
            }
        "},
	);

	// Comment as the first thing in a block, before any statement.
	assert_eq!(
		fmt(indoc! {"
            fn f() -> i32 {
                // load value
                42
            }
        "}),
		indoc! {"
            fn f() -> i32 {
                // load value
                42
            }
        "},
	);

	// Comment as the last thing in a block, after the final expression.
	assert_eq!(
		fmt(indoc! {"
            fn f() -> i32 {
                42
                // load value
            }
        "}),
		indoc! {"
            fn f() -> i32 {
                42
                // load value
            }
        "},
	);

	// Comment as the only content of an otherwise empty block.
	assert_eq!(
		fmt(indoc! {"
            fn f() {
                // nothing here yet
            }
        "}),
		indoc! {"
            fn f() {
                // nothing here yet
            }
        "},
	);

	// Truly empty block still collapses to `{}`.
	assert_eq!(fmt("fn f() {}\n"), "fn f() {}\n");

	// Doc comment preserved like a regular comment.
	assert_eq!(
		fmt(indoc! {"
            /// Returns the sum.
            fn add(a: i32, b: i32) -> i32 {
                a + b
            }
        "}),
		indoc! {"
            /// Returns the sum.
            fn add(a: i32, b: i32) -> i32 {
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
            import \"env\" {
                // nothing yet
            }
        "}),
		indoc! {"
            import \"env\" {
                // nothing yet
            }
        "},
	);

	// Leading/gap/trailing comments around export entries.
	assert_eq!(
		fmt(indoc! {"
            fn heap() -> i32 { 1 }
            fn other() -> i32 { 2 }
            export {
                // leading comment
                heap,
                // middle comment
                other
                // trailing comment
            }
        "}),
		indoc! {"
            fn heap() -> i32 {
                1
            }

            fn other() -> i32 {
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
	assert_eq!(fmt("import \"env\" {}\n"), "import \"env\" {}\n");

	// Comment as the only content of an otherwise empty body, for every
	// other brace-bodied item kind.
	assert_eq!(
		fmt(indoc! {"
            struct Foo {
                // fields tbd
            }
        "}),
		indoc! {"
            struct Foo {
                // fields tbd
            }
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
            struct Foo {}
            impl Foo {
                // methods tbd
            }
        "}),
		indoc! {"
            struct Foo {}

            impl Foo {
                // methods tbd
            }
        "},
	);
	assert_eq!(
		fmt(indoc! {"
            trait T {}
            struct Foo {}
            impl T for Foo {
                // methods tbd
            }
        "}),
		indoc! {"
            trait T {}

            struct Foo {}

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
            struct Foo {}
            impl Foo {
                // first method
                fn bar(self: Self) -> Self {
                    self
                }
            }
        "}),
		indoc! {"
            struct Foo {}

            impl Foo {
                // first method
                fn bar(self: Self) -> Self {
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
                fn bar(self: Self) -> Self;
            }
        "}),
		indoc! {"
            trait T {
                // first method
                fn bar(self: Self) -> Self;
            }
        "},
	);
}

#[test]
fn test_format_long_type_params_wrap() {
	let case = TestCase::new(indoc! {"
        pub fn memory_copy<Size: PointerSize, SrcMem: Memory where { Size = Size }, DstMem: Memory where { Size = Size }>(dst: DstMem::*u8, src: SrcMem::&u8, len: Size) {}
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
            pub fn memory_copy<
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
        fn f(ptr: &i32) {
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
            fn f(ptr: &i32) {
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
            fn draw(self) {}
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
                fn draw(self) {}
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
            fn get(self) -> T {
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
                fn get(self) -> T {
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
        fn f() {
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

        struct S {
            // leading on first field
            x: u32, // trailing on field
            y: u32,
            // own-line before closing brace
        }

        enum E: u32 {
            A = 0, // trailing on variant
            B = 1,
        }

        impl S {
            // leading on first member
            fn a(self) -> u32 {
                self.x
            } // trailing on member

            fn b(self) -> u32 {
                self.y
            }
        }

        fn g(v: u32) -> u32 {
            local a = 1; // trailing on statement

            // own-line, documents b
            local b = 2;
            match v {
                0 -> { a }, // trailing on arm
                // own-line before arm
                _ -> { b }
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
        pub fn f() -> u32 {
            1
        }
    "};
	assert_eq!(fmt(glued), glued);

	// A blank the author did write, on either side of the attribute, survives.
	let spaced = indoc! {"
        /// Doc, then a blank, then the attribute.

        #[inline]
        pub fn f() -> u32 {
            1
        }
    "};
	assert_eq!(fmt(spaced), spaced);

	// And a blank between two plain items is still kept — the region there
	// opens with the previous item's `;`, which is not whitespace either.
	let items = indoc! {"
        const A: u32 = 1;

        #[inline]
        pub fn f() -> u32 {
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
        fn f() -> i32 {
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

        struct S { // opens a `struct`
            x: u32,
        }

        enum E: u32 { // opens an `enum`
            A = 0,
        }

        impl S { // opens an `impl`
            fn a(self) -> u32 {
                self.x
            }
        }

        import \"env\" { // opens an `import`
            fn h() -> u32;
        }

        fn g(v: u32) -> u32 { // opens a block
            match v { // opens a `match`
                _ -> { v }
            }
        }

        trait T { // opens a `trait`
            fn t(self) -> u32;
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

        struct S {
            // opens a `struct`
            x: u32,
        }

        enum E: u32 {
            // opens an `enum`
            A = 0,
        }

        impl S {
            // opens an `impl`
            fn a(self) -> u32 {
                self.x
            }
        }

        import \"env\" {
            // opens an `import`
            fn h() -> u32;
        }

        fn g(v: u32) -> u32 {
            // opens a block
            match v {
                // opens a `match`
                _ -> { v }
            }
        }

        trait T {
            // opens a `trait`
            fn t(self) -> u32;
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

        struct S {
            x: u32, // documents x
            y: u32,
        }

        fn g() -> i32 {
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
            fn a(self) -> u32; // trails a member

            // own-line before b
            fn b(self) -> u32;
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
        struct S {
            // one

            // two
            x: u32,
        }

        impl S {
            // one

            // two
            fn a(self) -> u32 {
                self.x
            }
        }

        fn g() -> u32 {
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
        struct Empty {
            // one

            // two
        }

        struct HasAField {
            // one

            // two
            x: u32,
        }

        impl Empty {
            // one

            // two
        }

        fn f() {
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
        struct S {

            // separated from the brace
            x: u32,
        }

        impl S {

            fn a(self) -> u32 {
                self.x
            }
        }

        fn g() -> u32 {

            1
        }
    "};

	let expected = indoc! {"
        struct S {
            // separated from the brace
            x: u32,
        }

        impl S {
            fn a(self) -> u32 {
                self.x
            }
        }

        fn g() -> u32 {
            1
        }
    "};

	assert_eq!(fmt(source), expected);
	assert_eq!(fmt(expected), expected);
}
