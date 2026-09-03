use std::collections::HashMap;

use codespan_reporting::diagnostic::Severity;
use indoc::indoc;

use super::*;
use crate::tir::builder::{
	CharLiteralError, parse_char_literal, unescape_string,
};
use crate::vfs;

#[allow(unused)]
struct TestCase {
	graph: vfs::CompilationUnit,
	tir: TIR,
}

impl TestCase {
	fn new(source: &str) -> Self {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					source.to_string(),
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id);
		let tir = TIR::build(&mut graph);
		TestCase { graph, tir }
	}

	/// Same as [`Self::new`], but the root package is a **library** rather
	/// than a binary. `load_binary` is the only constructor the other
	/// helpers use, so without this there is no way to reach any rule that
	/// depends on the root package's kind.
	fn new_library(source: &str) -> Self {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_package(
				vfs::PackageKind::Library,
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					source.to_string(),
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id);
		let tir = TIR::build(&mut graph);
		TestCase { graph, tir }
	}

	/// A binary root package that depends on one library, which it names
	/// `dep`. The only way to reach a rule that spans a package boundary.
	fn new_with_dependency(source: &str, dependency: &str) -> Self {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let dependency_path = vfs::AbsolutePath::new("/dep/lib.wx");
		let dependency_id = builder
			.load_package(
				vfs::PackageKind::Library,
				dependency_path.clone(),
				&vfs::VirtualFileSource::new(HashMap::from([(
					dependency_path,
					dependency.to_string(),
				)])),
			)
			.unwrap();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					source.to_string(),
				)])),
			)
			.unwrap();
		let name = builder.interner.get_or_intern("dep");
		builder.add_dependency(root_id, name, dependency_id);
		let mut graph = builder.build(root_id);
		let tir = TIR::build(&mut graph);
		TestCase { graph, tir }
	}

	fn new_multi_file(
		entry_path: &str,
		source: &str,
		extra_files: &[(&str, &str)],
	) -> Self {
		let mut workspace_files =
			HashMap::from([(entry_path.to_string(), source.to_string())]);
		for (path, source) in extra_files {
			workspace_files.insert((*path).to_string(), (*source).to_string());
		}

		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new(format!("/{entry_path}")),
				&vfs::VirtualFileSource::from_relative(workspace_files),
			)
			.unwrap();
		let mut graph = builder.build(root_id);
		let tir = TIR::build(&mut graph);
		TestCase { graph, tir }
	}
}

#[test]
fn type_interner_seeds_and_deduplicates_types() {
	let mut types = TypeInterner::new();
	let builtins = [
		(TypeIndex::ERROR, Type::Error),
		(TypeIndex::INFER, Type::Infer),
		(TypeIndex::UNIT, Type::Unit),
		(TypeIndex::NEVER, Type::Never),
		(TypeIndex::INTEGER, Type::Integer),
		(TypeIndex::FLOAT, Type::Float),
		(TypeIndex::U8, Type::U8),
		(TypeIndex::I8, Type::I8),
		(TypeIndex::U16, Type::U16),
		(TypeIndex::I16, Type::I16),
		(TypeIndex::U32, Type::U32),
		(TypeIndex::I32, Type::I32),
		(TypeIndex::U64, Type::U64),
		(TypeIndex::I64, Type::I64),
		(TypeIndex::F32, Type::F32),
		(TypeIndex::F64, Type::F64),
		(TypeIndex::BOOL, Type::Bool),
		(TypeIndex::CHAR, Type::Char),
	];
	let builtin_count = builtins.len();

	for (index, ty) in builtins {
		assert_eq!(types.resolve(index), &ty);
		assert_eq!(types.intern(ty), index);
	}

	let tuple = Type::Tuple {
		elements: Box::new([TypeIndex::I32, TypeIndex::BOOL]),
	};
	let first = types.intern(tuple.clone());
	let second = types.intern(tuple);
	assert_eq!(first, second);
	assert_eq!(usize::from(first), builtin_count);
	assert_eq!(types.entries.len(), builtin_count + 1);
}

/// The stdlib has to typecheck as a package in its own right, not only as
/// everyone else's dependency. Loading it as the **root** package is what
/// makes that checkable: nothing else calls `load_stdlib()`, so there is no
/// second copy of `std` for it to collide with.
///
/// This checks the *embedded* `STDLIB_FILES` — the artifact actually shipped
/// inside the binary — rather than a copy read back off disk, so it can't
/// drift from what users get.
///
/// Errors and bugs only, deliberately: `report_unused_items` fires on
/// essentially all of `std` here, since nothing imports it. Same known gap
/// `test_imported_global` works around.
#[test]
fn test_stdlib_typechecks_as_root_package() {
	let mut builder = vfs::CompilationUnitBuilder::new();
	let std_id = builder.load_stdlib();
	// Root *and* stdlib provider are the same package here — that's the whole
	// point of loading it this way.
	let mut graph = builder.build(std_id);

	// Linker and parse diagnostics live on the package graph and on each
	// module's own AST respectively — neither is folded into `tir.diagnostics`,
	// so both have to be checked explicitly (same chain the CLI walks).
	let load_errors: Vec<String> = graph
		.packages
		.iter()
		.flat_map(|package_graph| {
			package_graph.diagnostics.iter().chain(
				package_graph
					.modules
					.iter()
					.flat_map(|module| module.ast.diagnostics.iter()),
			)
		})
		.filter(|d| matches!(d.severity, Severity::Error | Severity::Bug))
		.map(|d| format!("{}: {}", d.code.as_deref().unwrap_or("?"), d.message))
		.collect();
	assert!(
		load_errors.is_empty(),
		"stdlib failed to load cleanly:\n{}",
		load_errors.join("\n")
	);

	let tir = TIR::build(&mut graph);
	let type_errors: Vec<String> = tir
		.diagnostics
		.iter()
		.filter(|d| matches!(d.severity, Severity::Error | Severity::Bug))
		.map(|d| format!("{}: {}", d.code.as_deref().unwrap_or("?"), d.message))
		.collect();
	assert!(
		type_errors.is_empty(),
		"stdlib failed to typecheck standalone:\n{}",
		type_errors.join("\n")
	);
}

#[test]
fn test_unescape_string() {
	assert_eq!(unescape_string(r#""hello""#), "hello");
	assert_eq!(unescape_string(r#""hello\nworld""#), "hello\nworld");
	assert_eq!(unescape_string(r#""tab\tthere""#), "tab\tthere");
	assert_eq!(unescape_string(r#""quote\"here""#), "quote\"here");
	assert_eq!(unescape_string(r#""backslash\\here""#), "backslash\\here");
	assert_eq!(unescape_string(r#""null\0byte""#), "null\0byte");
	assert_eq!(unescape_string(r#""carriage\rreturn""#), "carriage\rreturn");
	// Multiple escapes
	assert_eq!(
		unescape_string(r#""line1\nline2\nline3""#),
		"line1\nline2\nline3"
	);
	// No quotes (should return as-is)
	assert_eq!(unescape_string("hello"), "hello");
}

#[test]
fn test_parse_char_literal() {
	// Plain characters
	assert_eq!(parse_char_literal("'a'"), Ok('a'));
	assert_eq!(parse_char_literal("'Z'"), Ok('Z'));
	assert_eq!(parse_char_literal("'0'"), Ok('0'));
	assert_eq!(parse_char_literal("' '"), Ok(' '));

	// Named escape sequences
	assert_eq!(parse_char_literal(r"'\n'"), Ok('\n'));
	assert_eq!(parse_char_literal(r"'\r'"), Ok('\r'));
	assert_eq!(parse_char_literal(r"'\t'"), Ok('\t'));
	assert_eq!(parse_char_literal(r"'\\'"), Ok('\\'));
	assert_eq!(parse_char_literal(r"'\''"), Ok('\''));
	assert_eq!(parse_char_literal(r"'\0'"), Ok('\0'));

	// Hex escapes
	assert_eq!(parse_char_literal(r"'\x41'"), Ok('A')); // 0x41 = 65 = 'A'
	assert_eq!(parse_char_literal(r"'\x0A'"), Ok('\n')); // 0x0A = 10 = '\n'
	assert_eq!(parse_char_literal(r"'\x00'"), Ok('\0'));

	// Without surrounding quotes — content passed directly
	assert_eq!(parse_char_literal("a"), Ok('a'));

	// Errors
	assert!(matches!(
		parse_char_literal("''"),
		Err(CharLiteralError::Empty)
	));
	assert!(matches!(
		parse_char_literal("'ab'"),
		Err(CharLiteralError::TooLong)
	));
}

#[test]
fn test_build_with_package_graph_lowers_child_module_items() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		"mod math;",
		&[("src/math.wx", "fn add() -> i32 { 1 }")],
	);

	assert!(
		case.tir.items.functions.iter().any(|function| case
			.graph
			.interner
			.resolve(function.name.inner)
			== Some("add"))
	);
}

#[test]
fn test_build_with_package_graph_resolves_cross_file_module_function_call() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod math;

            fn main() -> i32 {
                math::add()
            }

            export { main }
        "},
		&[("src/math.wx", "pub fn add() -> i32 { 1 }")],
	);

	no_errors(&case);
}

#[test]
fn test_build_with_package_graph_resolves_cross_file_module_type_access() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod shapes;

            fn use_circle(circle: shapes::Circle) {
                unreachable
            }
        "},
		&[("src/shapes.wx", "pub struct Circle {}")],
	);

	no_errors(&case);
}

/// An `export { .. }` block rides the Phase 2 sweep as an ordinary
/// `ast_nodes` entry, so it resolves the names it lists by forcing them
/// through `ensure_signature` — exactly like any other reference site.
/// That makes a forward reference work: the block can precede everything it
/// names, including a `memory` whose `Size` binding has to check trait
/// bounds (`u32: PointerSize + UnsignedInt`) against the stdlib.
#[test]
fn test_export_block_preceding_the_items_it_names() {
	let case = TestCase::new(indoc! {"
        export { heap, elem }

        memory heap: Memory where { Size = u32 }

        fn elem(arr: heap::&[i32; 4], i: u32) -> i32 { arr[i] }
    "});

	no_errors(&case);
	assert_eq!(case.tir.export_block.as_ref().unwrap().items.len(), 2);
}

// ── `use` trees ──────────────────────────────────────────────────────────

/// Convenience for the `use` tests: a two-file package whose `src/math.wx`
/// is `math`.
fn use_case(entry: &str, math: &str) -> TestCase {
	TestCase::new_multi_file(
		"src/main.wx",
		&format!("mod math;\n{entry}"),
		&[("src/math.wx", math)],
	)
}

#[test]
fn test_use_named_import_binds_the_name() {
	let case = use_case(
		indoc! {"
            use math::add;
            fn main() -> i32 { add() }
            export { main }
        "},
		"pub fn add() -> i32 { 1 }",
	);
	no_errors(&case);
}

#[test]
fn test_use_alias_binds_the_local_name() {
	let case = use_case(
		indoc! {"
            use math::add as plus;
            fn main() -> i32 { plus() }
            export { main }
        "},
		"pub fn add() -> i32 { 1 }",
	);
	no_errors(&case);
}

#[test]
fn test_use_group_imports_every_leaf() {
	let case = use_case(
		indoc! {"
            use math::{add, sub};
            fn main() -> i32 { add() + sub() }
            export { main }
        "},
		"pub fn add() -> i32 { 1 }\npub fn sub() -> i32 { 2 }",
	);
	no_errors(&case);
	assert_eq!(
		case.tir.items.use_items.len(),
		2,
		"one `UseItem` per named leaf"
	);
}

/// Nested groups and both leaf kinds in one item — the shape that proves
/// the tree is really recursive rather than a prefix plus a leaf.
#[test]
fn test_use_nested_group_with_both_leaf_kinds() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod math;
            use math::{trig::{sin, cos}, ops::*};
            fn main() -> i32 { sin() + cos() + double(1) }
            export { main }
        "},
		&[
			("src/math.wx", "pub mod trig;\npub mod ops;"),
			(
				"src/math/trig.wx",
				"pub fn sin() -> i32 { 1 }\npub fn cos() -> i32 { 2 }",
			),
			("src/math/ops.wx", "pub fn double(x: i32) -> i32 { x * 2 }"),
		],
	);
	no_errors(&case);
}

/// A group's prefix is one mention of `math` in the source, so it is walked
/// once and recorded once however many names hang off it. Per-leaf walking
/// recorded it per leaf, and since the LSP turns every access into a
/// reference, that gave find-references repeats and made rename emit two
/// overlapping edits at a single range.
#[test]
fn test_group_prefix_is_walked_once() {
	let case = use_case(
		indoc! {"
            use math::{add, sub};
            fn main() -> i32 { add() + sub() }
            export { main }
        "},
		"pub fn add() -> i32 { 1 }\npub fn sub() -> i32 { 2 }",
	);
	no_errors(&case);

	assert_eq!(
		case.tir.items.use_prefixes.len(),
		1,
		"both leaves name the same `math`, so it is stored once"
	);
	let math = case.tir.items.use_items[0].prefix;
	let PrefixTarget::Resolved(math_ns) =
		case.tir.items.use_prefixes[usize::from(math)].target
	else {
		panic!("`math` should have resolved")
	};
	assert_eq!(
		case.tir.modules.namespaces[usize::from(math_ns)]
			.accesses
			.len(),
		1,
		"one source mention of `math` is one access"
	);
}

/// Two statements naming the same module are two separate mentions, so they
/// get an entry — and an access — each.
#[test]
fn test_separate_use_statements_do_not_share_a_prefix() {
	let case = use_case(
		indoc! {"
            use math::add;
            use math::sub;
            fn main() -> i32 { add() + sub() }
            export { main }
        "},
		"pub fn add() -> i32 { 1 }\npub fn sub() -> i32 { 2 }",
	);
	no_errors(&case);
	assert_eq!(case.tir.items.use_prefixes.len(), 2);
}

/// A glob binds no name, so it needs no prefix entry of its own.
#[test]
fn test_glob_allocates_no_prefix() {
	let case = use_case(
		"use math::*;\nfn main() -> i32 { add() }\nexport { main }",
		"pub fn add() -> i32 { 1 }",
	);
	no_errors(&case);
	assert!(case.tir.items.use_prefixes.is_empty());
}

#[test]
fn test_use_imports_a_type() {
	let case = use_case(
		indoc! {"
            use math::Point;
            fn main() -> i32 { local p: Point = Point::{ x: 1 }; p.x }
            export { main }
        "},
		"pub struct Point { pub x: i32 }",
	);
	no_errors(&case);
}

#[test]
fn test_use_private_item_reports_at_the_use_site() {
	let case = use_case(
		"use math::hidden;\nfn main() -> i32 { 1 }\nexport { main }",
		"fn hidden() -> i32 { 1 }",
	);
	assert!(has_error_code(&case.tir, DiagnosticCode::PrivateItem));
}

/// The glob path stays silent on an unresolvable prefix — it has to, since
/// it runs before other files are scanned — but a named leaf resolves late
/// enough that silence would just lose the error.
#[test]
fn test_use_unresolved_name_reports() {
	let case = use_case(
		"use math::nope;\nfn main() -> i32 { 1 }\nexport { main }",
		"pub fn add() -> i32 { 1 }",
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

#[test]
fn test_use_unresolved_prefix_reports() {
	let case = use_case(
		"use nothere::thing;\nfn main() -> i32 { 1 }\nexport { main }",
		"pub fn add() -> i32 { 1 }",
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

/// `use add;` names no module to import from. It used to be accepted in
/// silence: the prefix walker returned a bare `Option`, so "resolved",
/// "failed, already reported" and "there were no segments at all" were the
/// same value, and the last one fell through the reporting path entirely.
#[test]
fn test_use_without_a_module_reports() {
	let case = use_case(
		"use add;\nfn main() -> i32 { 1 }\nexport { main }",
		"pub fn add() -> i32 { 1 }",
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"a bare `use add;` imports nothing and must say so: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_use_prefix_that_is_not_a_module_reports() {
	let case = use_case(
		"use S::thing;\nstruct S {}\nfn main() -> i32 { 1 }\nexport { main }",
		"pub fn add() -> i32 { 1 }",
	);
	assert!(has_error_code(&case.tir, DiagnosticCode::NotANamespace));
}

/// An import claims both symbol namespaces at prescan, before its target is
/// known. When the target turns out to occupy only one of them, the other
/// claim must vanish without a trace — a function import next to a struct
/// of the same name is legal.
#[test]
fn test_value_import_does_not_collide_with_a_type_declaration() {
	let case = use_case(
		indoc! {"
            use math::add;
            struct add { x: i32 }
            fn main() -> i32 { add() }
            export { main }
        "},
		"pub fn add() -> i32 { 1 }",
	);
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"`add` the function and `add` the struct occupy different symbol \
		 namespaces: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_type_import_does_not_collide_with_a_value_declaration() {
	let case = use_case(
		indoc! {"
            use math::Point;
            fn Point() -> i32 { 2 }
            fn main() -> i32 { Point() }
            export { main }
        "},
		"pub struct Point { x: i32 }",
	);
	assert!(!has_error_code(
		&case.tir,
		DiagnosticCode::DuplicateDefinition
	));
}

/// The collision that *is* real still has to be reported — and exactly
/// once, in either source order, since prescan defers the judgement and
/// Phase 2 must not double it.
#[test]
fn test_import_colliding_in_the_same_namespace_reports_once() {
	for source in [
		"use math::add;\nfn add() -> i32 { 2 }\nfn main() -> i32 { add() }",
		"fn add() -> i32 { 2 }\nuse math::add;\nfn main() -> i32 { add() }",
	] {
		let case = use_case(
			&format!("{source}\nexport {{ main }}"),
			"pub fn add() -> i32 { 1 }",
		);
		let duplicates = case
			.tir
			.diagnostics
			.iter()
			.filter(|d| {
				d.code.as_deref()
					== Some(DiagnosticCode::DuplicateDefinition.code())
			})
			.count();
		assert_eq!(duplicates, 1, "for source:\n{source}");
	}
}

/// Value position had no `Pending` forcing at all, so a reference resolved
/// before its target's signature hit an `unreachable!`. Both ways of
/// getting there are legal source.
#[test]
fn test_value_reference_forces_a_pending_signature() {
	// A `use` written *below* the reference to what it imports.
	let case = use_case(
		indoc! {"
            const DOUBLE: i32 = BASE;
            use math::BASE;
            fn main() -> i32 { DOUBLE }
            export { main }
        "},
		"pub const BASE: i32 = 21;",
	);
	no_errors(&case);

	// A const naming a const declared later — no `use` involved at all,
	// which is why this one crashed long before `use` trees existed.
	let case = TestCase::new(indoc! {"
        const A: i32 = B;
        const B: i32 = 1;
        fn main() -> i32 { A }
        export { main }
    "});
	no_errors(&case);
}

#[test]
fn test_self_referential_const_reports_a_cycle() {
	let case = TestCase::new(indoc! {"
        const A: i32 = A;
        fn main() -> i32 { A }
        export { main }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::CyclicTypeDependency
	));
}

/// `A`'s own initializer is the self-reference that trips the cycle once,
/// while `ensure_signature(A)` is `InProgress`. Once that call unwinds,
/// `sig_state[A]` lands on `Done` — never stuck `InProgress` forever, never
/// reset back to `Pending` — so `main` and `other`, which each reference `A`
/// afterward from ordinary (non-cyclic) contexts, should see a plain
/// resolved `Const` and neither re-derive the cycle nor get a diagnostic of
/// their own.
#[test]
fn test_cyclic_const_referenced_afterward_reports_once_not_per_reference() {
	let case = TestCase::new(indoc! {"
        const A: i32 = A;
        fn main() -> i32 { A }
        fn other() -> i32 { A + 1 }
        export { main, other }
    "});

	let by_code = |code: DiagnosticCode| {
		case.tir
			.diagnostics
			.iter()
			.filter(move |d| d.code.as_deref() == Some(code.code()))
			.count()
	};
	// A's own initializer legitimately produces two diagnostics on its own
	// declaration: the cycle itself, and — since the resolved value is an
	// error placeholder, not a real constant — "not const-evaluable" for
	// the initializer expression as a whole. Neither should multiply with
	// the number of *later* references to A: `main` and `other` both read
	// the already-`Done` A as a plain `i32` const and shouldn't re-trigger
	// either diagnostic.
	assert_eq!(
		by_code(DiagnosticCode::CyclicTypeDependency),
		1,
		"expected exactly one cyclic-dependency diagnostic (from A's own \
		 initializer), not one per later reference to A; got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert_eq!(
		by_code(DiagnosticCode::NotConstEvaluatable),
		1,
		"expected exactly one not-const-evaluable diagnostic (from A's own \
		 initializer failing to fold), not one per later reference to A; \
		 got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert_eq!(
		case.tir.diagnostics.len(),
		2,
		"main/other referencing the already-Done A should type-check \
		 cleanly against its declared type, not cascade into further \
		 errors of their own; got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Same question as above, but for a mutual cycle (`A` depends on `B`
/// depends on `A`) instead of direct self-reference, and with each side
/// referenced afterward from its own function. Only the inner hop that
/// actually closes the cycle (`B`'s reference back to the still-`InProgress`
/// `A`) should report — `A`'s own reference to `B` resolves normally, since
/// by the time that lookup runs `ensure_signature(B)` has already finished
/// and `B` is bound to a plain `Const`, not left `Pending`.
#[test]
fn test_mutual_const_cycle_referenced_afterward_reports_once() {
	let case = TestCase::new(indoc! {"
        const A: i32 = B;
        const B: i32 = A;
        fn main() -> i32 { A }
        fn other() -> i32 { B }
        export { main, other }
    "});

	let cyclic_count = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::CyclicTypeDependency.code())
		})
		.count();
	assert_eq!(
		cyclic_count,
		1,
		"expected exactly one cyclic-dependency diagnostic for the A/B \
		 mutual cycle, not one per hop or per later reference; got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── named-import cycle edge cases ───────────────────────────────────────

/// Two modules alias each other's still-unresolved name — `a::Foo` is never
/// anything but `b::Bar` and vice versa, so neither side ever bottoms out at
/// a real item. Deliberately doesn't reference `Foo`/`Bar` from anywhere:
/// Phase 2 calls `ensure_signature` on every registered `DefId` in parse
/// order regardless of whether anything downstream ever looks it up, so the
/// cycle should surface on its own.
#[test]
fn test_named_import_alias_cycle_across_modules_reports_a_cycle() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod b;
            fn main() -> i32 { 1 }
            export { main }
        "},
		&[
			("src/a.wx", "pub use b::bar as foo;"),
			("src/b.wx", "pub use a::foo as bar;"),
		],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::CyclicTypeDependency
	));
}

/// Looks superficially symmetric to the cycle above — each module imports a
/// name from the other — but both sides bottom out at a real, independent
/// item, so this is not cyclic. The false-positive case the notes flagged
/// for a whole-namespace or naive symmetric check.
#[test]
fn test_two_modules_importing_concrete_items_from_each_other_is_not_cyclic() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod b;
            fn main() -> i32 { a::use_b() + b::use_a() }
            export { main }
        "},
		&[
			(
				"src/a.wx",
				"use b::real_b;\npub fn use_b() -> i32 { real_b() }\npub fn real_a() -> i32 { 1 }",
			),
			(
				"src/b.wx",
				"use a::real_a;\npub fn use_a() -> i32 { real_a() }\npub fn real_b() -> i32 { 2 }",
			),
		],
	);
	no_errors(&case);
}

/// Two named imports of the same local name from two distinct sources
/// collide eagerly, at prescan — unlike a glob collision (which defers to
/// the first actual reference and produces `AmbiguousWildcardImport`), this
/// is an ordinary same-scope duplicate binding.
#[test]
fn test_duplicate_named_import_is_duplicate_definition_not_ambiguity() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod x;
            mod y;
            use x::pick;
            use y::pick;
            fn main() -> i32 { pick() }
            export { main }
        "},
		&[
			("src/x.wx", "pub fn pick() -> i32 { 6 }"),
			("src/y.wx", "pub fn pick() -> i32 { 5 }"),
		],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::DuplicateDefinition
	));
	assert!(!has_error_code(
		&case.tir,
		DiagnosticCode::AmbiguousWildcardImport
	));
}

/// The span a wildcard ambiguity will point at (Part 4): the path and the
/// star, not the `use` keyword, and — for a glob nested in a group — only
/// the part that is a contiguous range of source.
#[test]
fn test_glob_import_records_its_path_span() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		"mod math;\nuse math::{trig::*};\nfn main() -> i32 { 1 }\nexport { main }",
		&[
			("src/math.wx", "pub mod trig;"),
			("src/math/trig.wx", "pub fn sin() -> i32 { 1 }"),
		],
	);
	no_errors(&case);

	let root = case.tir.modules.file_namespaces[1];
	let spelled: Vec<&str> = case.tir.modules.namespaces[usize::from(root)]
		.wildcard_imports
		.iter()
		.map(|import| {
			let source = &case
				.graph
				.files
				.get(import.span.file_id)
				.expect("the entry file is in the compilation unit")
				.source;
			&source
				[import.span.span.start as usize..import.span.span.end as usize]
		})
		.collect();

	// A span reaching back to `math` would cross the `{` and not be a
	// contiguous range of source.
	assert_eq!(spelled, vec!["trig::*"]);
}

// ── wildcard ambiguity ───────────────────────────────────────────────────

/// Two modules, `x` and `y`, both glob-imported into the entry file.
fn ambiguity_case(entry: &str, x: &str, y: &str) -> TestCase {
	TestCase::new_multi_file(
		"src/main.wx",
		&format!("mod x;\nmod y;\nuse x::*;\nuse y::*;\n{entry}"),
		&[("src/x.wx", x), ("src/y.wx", y)],
	)
}

/// The labels belong on the `use` statements, not the definitions: each
/// definition is fine on its own, and it's importing both into one scope
/// that isn't.
#[test]
fn test_two_globs_supplying_one_name_is_ambiguous() {
	let case = ambiguity_case(
		"fn main() -> i32 { FOO }\nexport { main }",
		"pub const FOO: i32 = 6;",
		"pub const FOO: i32 = 5;",
	);

	let diagnostic = case
		.tir
		.diagnostics
		.iter()
		.find(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::AmbiguousWildcardImport.code())
		})
		.expect("expected E1075");

	let secondary: Vec<&str> = diagnostic
		.labels
		.iter()
		.filter(|label| {
			label.style == codespan_reporting::diagnostic::LabelStyle::Secondary
		})
		.map(|label| {
			let source = &case.graph.files.get(label.file_id).unwrap().source;
			&source[label.range.clone()]
		})
		.collect();
	assert_eq!(
		secondary,
		vec!["x::*", "y::*"],
		"one label per glob, spanning the path and star — not the `use` \
		 keyword, and not the definition it resolved to"
	);
}

/// Value position goes through `resolve_symbol`, which is `&self` and can't
/// report; wiring the check only into the `&mut self` forcing wrappers
/// would have covered types and missed this — rustc's own example.
#[test]
fn test_ambiguity_is_reported_in_value_position() {
	let case = ambiguity_case(
		"fn main() -> i32 { pick() }\nexport { main }",
		"pub fn pick() -> i32 { 6 }",
		"pub fn pick() -> i32 { 5 }",
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::AmbiguousWildcardImport
	));
}

#[test]
fn test_ambiguity_is_reported_in_type_position() {
	let case = ambiguity_case(
		"fn main(p: Point) -> i32 { 1 }\nexport { main }",
		"pub struct Point { pub x: i32 }",
		"pub struct Point { pub y: i32 }",
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::AmbiguousWildcardImport
	));
}

/// Reachable from the export block now that Part 3 resolves entries through
/// the scope chain — without this, `export { pick }` would silently bake
/// one of two `pick`s into the module ABI.
#[test]
fn test_ambiguity_is_reported_from_the_export_block() {
	let case = ambiguity_case(
		"export { pick }",
		"pub fn pick() -> i32 { 6 }",
		"pub fn pick() -> i32 { 5 }",
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::AmbiguousWildcardImport
	));
}

/// One item reachable two ways is not a conflict — there's nothing to
/// arbitrate, since both globs name the same thing.
#[test]
fn test_one_item_through_two_globs_is_not_ambiguous() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod base;
            mod x;
            mod y;
            use x::*;
            use y::*;

            fn main() -> i32 { shared() }
            export { main }
        "},
		&[
			("src/base.wx", "pub fn shared() -> i32 { 1 }"),
			("src/x.wx", "pub use base::shared;"),
			("src/y.wx", "pub use base::shared;"),
		],
	);
	no_errors(&case);
}

/// The fix the diagnostic recommends has to actually work: a namespace's
/// own symbols are consulted before its globs, so an explicit import wins
/// outright.
#[test]
fn test_explicit_import_disambiguates_two_globs() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod x;
            mod y;
            use x::*;
            use y::*;
            use x::pick;

            fn main() -> i32 { pick() }
            export { main }
        "},
		&[
			("src/x.wx", "pub fn pick() -> i32 { 6 }"),
			("src/y.wx", "pub fn pick() -> i32 { 5 }"),
		],
	);
	no_errors(&case);
}

/// A glob here and a glob on an enclosing scope is ordinary shadowing, not
/// ambiguity — which is why the walk stops at the first level that
/// resolves rather than gathering candidates across levels.
#[test]
fn test_glob_in_an_inner_scope_shadows_an_outer_one() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod x;
            mod y;
            use x::*;

            mod inner {
                use y::*;
                pub fn get() -> i32 { pick() }
            }

            fn main() -> i32 { inner::get() }
            export { main }
        "},
		&[
			("src/x.wx", "pub fn pick() -> i32 { 6 }"),
			("src/y.wx", "pub fn pick() -> i32 { 5 }"),
		],
	);
	no_errors(&case);
}

// ── the prelude ──────────────────────────────────────────────────────────
//
// The standard library's root namespace is the last tier `lookup_scope_chain`
// consults, below every glob. These tests pin that ordering, since it's what
// lets std grow new items without breaking programs that already compile.

/// A file that never mentions `std` still resolves std's items.
#[test]
fn test_prelude_resolves_without_any_import() {
	let case = TestCase::new(indoc! {"
        fn main(x: f32) -> f32 { f32_sqrt(x) }
        export { main }
    "});
	no_errors(&case);
}

/// The prelude reaches submodules, not just the package root — it is a
/// property of every namespace rather than something inherited from an
/// ancestor.
#[test]
fn test_prelude_reaches_a_submodule() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            fn main(x: f32) -> f32 { a::call_it(x) }
            export { main }
        "},
		&[("src/a.wx", "pub fn call_it(x: f32) -> f32 { f32_sqrt(x) }")],
	);
	no_errors(&case);
}

/// A local declaration outranks the prelude, silently — no ambiguity, and
/// the local one is what the call resolves to (the `bool` return is what
/// makes the choice observable: std's `f32_sqrt` returns `f32`).
#[test]
fn test_local_declaration_shadows_the_prelude() {
	let case = TestCase::new(indoc! {"
        fn f32_sqrt(x: f32) -> bool { true }
        fn main(x: f32) -> bool { f32_sqrt(x) }
        export { main }
    "});
	no_errors(&case);
}

/// A glob import outranks the prelude too, and just as silently — unlike a
/// collision between two globs, which is an ambiguity error. This is the
/// case that would regress if the prelude were ever implemented as a
/// synthetic `use std::*;` seeded into each namespace.
#[test]
fn test_glob_import_shadows_the_prelude() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            use a::*;
            fn main(x: f32) -> bool { f32_sqrt(x) }
            export { main }
        "},
		&[("src/a.wx", "pub fn f32_sqrt(x: f32) -> bool { true }")],
	);
	no_errors(&case);
}

// ── crate/super paths ────────────────────────────────────────────────────
//
// `crate`/`super` are ordinary `SymbolKind::Module` entries every namespace
// is pre-populated with at creation (`Builder::seed_path_root_symbols`) —
// no dedicated resolver logic, so these tests exercise the existing
// use/type/value path machinery, not anything new.

/// `crate::x` from a submodule reaches the package root's items.
#[test]
fn test_crate_path_reaches_package_root_from_submodule() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            pub fn helper() -> i32 { 1 }
            fn main() -> i32 { a::call_it() }
            export { main }
        "},
		&[("src/a.wx", "pub fn call_it() -> i32 { crate::helper() }")],
	);
	no_errors(&case);
}

/// `use crate::x;` — the same path root, in `use`-tree position.
#[test]
fn test_use_crate_path_binds_a_package_root_item() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            pub fn helper() -> i32 { 1 }
            fn main() -> i32 { a::call_it() }
            export { main }
        "},
		&[(
			"src/a.wx",
			"use crate::helper;\npub fn call_it() -> i32 { helper() }",
		)],
	);
	no_errors(&case);
}

/// `use crate::*;` — `crate` as a glob root. Falls out of the same
/// `walk_use_prefix` resolution every other glob prefix already uses.
#[test]
fn test_use_crate_glob_imports_the_package_root() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            pub fn helper() -> i32 { 1 }
            fn main() -> i32 { a::call_it() }
            export { main }
        "},
		&[(
			"src/a.wx",
			"use crate::*;\npub fn call_it() -> i32 { helper() }",
		)],
	);
	no_errors(&case);
}

/// `crate::x` in type position.
#[test]
fn test_crate_path_in_type_position_resolves() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            pub struct Point { pub x: i32 }
            fn main() -> i32 { a::make().x }
            export { main }
        "},
		&[(
			"src/a.wx",
			"pub fn make() -> crate::Point { crate::Point::{ x: 1 } }",
		)],
	);
	no_errors(&case);
}

/// `super::x` from a nested inline module reaches its immediate parent.
#[test]
fn test_super_path_reaches_parent_from_nested_module() {
	let case = TestCase::new(indoc! {"
        pub fn outer_helper() -> i32 { 1 }
        mod inner {
            pub fn call_super() -> i32 { super::outer_helper() }
        }
        fn main() -> i32 { inner::call_super() }
        export { main }
    "});
	no_errors(&case);
}

/// `super::super::x` chains two hops up — each namespace on the walk
/// carries its own `super` entry, so this needs no chaining-specific logic.
#[test]
fn test_super_super_path_chains_to_grandparent() {
	let case = TestCase::new(indoc! {"
        pub fn root_helper() -> i32 { 1 }
        mod outer {
            pub mod inner {
                pub fn call_grandparent() -> i32 { super::super::root_helper() }
            }
        }
        fn main() -> i32 { outer::inner::call_grandparent() }
        export { main }
    "});
	no_errors(&case);
}

/// `foo::super::bar` — a non-leading `super`. Accepted by design, not an
/// oversight: `super` inside `a`'s own namespace always means `a`'s parent,
/// consistently, wherever it's written, so restricting it to leading
/// position would cost real resolver complexity for no ambiguity payoff.
#[test]
fn test_non_leading_super_segment_resolves() {
	let case = TestCase::new(indoc! {"
        pub fn root_helper() -> i32 { 1 }
        mod a {
            pub fn unused() -> i32 { 0 }
        }
        fn main() -> i32 { a::super::root_helper() }
        export { main }
    "});
	no_errors(&case);
}

/// `super` walked past the package root reports the same "not found" a
/// reference to any other undeclared name would — no dedicated diagnostic
/// exists, or is needed, since a package root simply has no `super` entry.
#[test]
fn test_super_beyond_package_root_is_undeclared() {
	let case = TestCase::new(indoc! {"
        fn main() -> i32 { super::main() }
        export { main }
    "});
	assert!(
		!case.tir.diagnostics.is_empty(),
		"expected `super` above the package root to be reported as a \
		 plain unresolved reference"
	);
}

// ── wildcard transitivity & cycles (not yet implemented) ────────────────
//
// `lookup_scope_chain`'s wildcard branch currently checks only a glob
// source's *direct* `.symbols` map, never that source's own
// `wildcard_imports` — so there is neither transitive glob-of-glob
// resolution nor a cycle risk today, because there is no recursion into a
// glob source's own globs at all. These are `#[ignore]`d until that
// recursion (guarded by an on-stack "currently visiting" set of
// `NamespaceIndex`, the same idiom `ComputeState::InProgress` already uses
// for named-import cycles) lands — see notes/module_resolution_design_notes.md.

/// `c` globs `b`, `b` re-exports `a` wholesale (`pub use crate::a::*;`) —
/// `c` should see `a`'s items without naming `a` itself.
#[test]
#[ignore = "wildcard glob resolution is single-hop only today; \
            transitive re-export via `pub use x::*;` chains isn't \
            implemented yet"]
fn test_transitive_glob_import_two_hops() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod b;
            use b::*;
            fn main() -> i32 { foo() }
            export { main }
        "},
		&[
			("src/a.wx", "pub fn foo() -> i32 { 1 }"),
			("src/b.wx", "pub use crate::a::*;"),
		],
	);
	no_errors(&case);
}

/// Same as the two-hop case, one hop deeper — transitivity shouldn't have
/// an arbitrary depth cap, only the cycle check should bound it.
#[test]
#[ignore = "wildcard glob resolution is single-hop only today; \
            transitive re-export via `pub use x::*;` chains isn't \
            implemented yet"]
fn test_transitive_glob_import_three_hops() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod b;
            mod c;
            use c::*;
            fn main() -> i32 { foo() }
            export { main }
        "},
		&[
			("src/a.wx", "pub fn foo() -> i32 { 1 }"),
			("src/b.wx", "pub use crate::a::*;"),
			("src/c.wx", "pub use crate::b::*;"),
		],
	);
	no_errors(&case);
}

/// `a` globs `b`, `b` globs `a` — a namespace transitively importing itself
/// via globs, the case constraint #3 in the design notes wants to be a hard
/// error with the full cycle chain, not Rust's iterative-fixed-point
/// behavior (which would just never stabilize).
///
/// Diagnostic code is a placeholder: reusing `CyclicTypeDependency` (like
/// struct/type-alias cycles already do) is the simplest option, but a
/// dedicated "circular wildcard import" code is also on the table — pick
/// one when implementing and update this assertion.
#[test]
#[ignore = "no cycle check exists yet for the wildcard-import graph"]
fn test_two_module_glob_cycle_is_a_cyclic_error() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod b;
            fn main() -> i32 { 1 }
            export { main }
        "},
		&[
			("src/a.wx", "pub use crate::b::*;"),
			("src/b.wx", "pub use crate::a::*;"),
		],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::CyclicTypeDependency
	));
}

/// Degenerate one-node case of the same cycle: a module glob-importing
/// itself. Should fall out of the same detector as the two-module case
/// above with no special-casing — worth its own test so nobody adds one.
#[test]
#[ignore = "no cycle check exists yet for the wildcard-import graph"]
fn test_module_glob_importing_itself_is_a_cyclic_error() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            fn main() -> i32 { 1 }
            export { main }
        "},
		&[("src/a.wx", "pub use crate::a::*;")],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::CyclicTypeDependency
	));
}

// ── `use` re-export privacy ────────────────────────────────────────────────
//
// A `use` leaf's own `pub_span` (`UseItem::pub_span`) governs whether *that
// binding* is visible outside its own namespace — independent of whatever
// visibility the re-exported item itself declared, which is only checked
// once, when the leaf's own prefix resolved. `SymbolEntry::Resolved`'s
// `visibility` field carries this per-binding answer regardless of how a
// name was reached (direct qualified path, or via someone else's glob).
//
// Still a real gap: `WildcardImport` itself carries no visibility of its
// own, so a glob-of-glob re-export (`pub use a::*;` inside `b`, reached via
// `use b::*;` elsewhere) isn't gated — see the wildcard-transitivity tests
// below, which are `#[ignore]`d for a separate reason (transitivity itself
// isn't implemented, so there's nothing yet to gate).

/// A private `use` should only make the name visible inside its own
/// namespace and descendants — not to an external qualified-path reference,
/// same as a plain private item would be (hence the same diagnostic,
/// `PrivateItem`, that a direct private declaration would get here).
#[test]
fn test_private_use_is_not_visible_via_qualified_path_from_outside() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod baz;
            fn main() -> i32 { baz::bar() }
            export { main }
        "},
		&[
			("src/a.wx", "pub fn bar() -> i32 { 1 }"),
			("src/baz.wx", "use a::bar;"),
		],
	);
	assert!(has_error_code(&case.tir, DiagnosticCode::PrivateItem));
}

/// The `pub use` counterpart of the case above — already correct today, and
/// should stay correct once privacy tracking lands.
#[test]
fn test_pub_use_is_visible_via_qualified_path_from_outside() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod baz;
            fn main() -> i32 { baz::bar() }
            export { main }
        "},
		&[
			("src/a.wx", "pub fn bar() -> i32 { 1 }"),
			("src/baz.wx", "pub use a::bar;"),
		],
	);
	no_errors(&case);
}

/// A private `use` inside `baz` must not be pulled in by someone else's
/// `use baz::*;` — private imports don't propagate through an external
/// glob.
#[test]
fn test_private_use_is_not_reachable_through_an_external_glob() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod baz;
            use baz::*;
            fn main() -> i32 { bar() }
            export { main }
        "},
		&[
			("src/a.wx", "pub fn bar() -> i32 { 1 }"),
			("src/baz.wx", "use a::bar;"),
		],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

/// The `pub use` counterpart — already correct today (see also
/// `test_one_item_through_two_globs_is_not_ambiguous`, which exercises the
/// same shape), and should stay correct once privacy tracking lands.
#[test]
fn test_pub_use_is_reachable_through_an_external_glob() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod baz;
            use baz::*;
            fn main() -> i32 { bar() }
            export { main }
        "},
		&[
			("src/a.wx", "pub fn bar() -> i32 { 1 }"),
			("src/baz.wx", "pub use a::bar;"),
		],
	);
	no_errors(&case);
}

/// A chain of *named* `pub use` re-exports (not globs) — already works
/// mechanically today via the same demand-driven `ensure_signature` path
/// that resolves any other named import; worth locking in so privacy work
/// on named imports doesn't regress the chain itself.
#[test]
fn test_chained_pub_use_re_export_resolves() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod b;
            mod c;
            fn main() -> i32 { c::foo() }
            export { main }
        "},
		&[
			("src/a.wx", "pub fn foo() -> i32 { 1 }"),
			("src/b.wx", "pub use a::foo;"),
			("src/c.wx", "pub use b::foo;"),
		],
	);
	no_errors(&case);
}

/// A rejected private-item reference should still record an access, the
/// same way `export { .. }` naming an unexportable item does (see
/// `test_export_reports_cannot_export_and_records_access`): name resolution
/// found the item — only the accessibility check failed — so it's a real
/// reference, not an absence. Recording it is what lets hover/go-to-definition
/// still work on it, and it must also keep the item from *additionally*
/// being flagged `UnusedItem` on top of `PrivateItem` — a bare, unreferenced
/// item and a referenced-but-inaccessible one are different situations.
#[test]
fn test_private_item_reference_records_access_and_is_not_flagged_unused() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            fn main() -> i32 { a::foo() }
            export { main }
        "},
		&[("src/a.wx", "fn foo() -> i32 { 1 }")],
	);
	assert!(has_error_code(&case.tir, DiagnosticCode::PrivateItem));
	assert!(!has_error_code(&case.tir, DiagnosticCode::UnusedItem));
	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| {
			case.graph
				.interner
				.resolve(f.name.inner)
				.map(|n| n == "foo")
				.unwrap_or(false)
		})
		.expect("function 'foo' not found in TIR");
	assert_eq!(func.accesses.len(), 1);
}

// ── struct field privacy ─────────────────────────────────────────────────

/// The three ways a field name is resolved — a read/write through `.`, a
/// struct literal, and a `local` destructuring pattern — each gate on the
/// field's own `pub`, against the namespace of the struct that declares it.
/// A field has no scope of its own, so that struct's module is what it is
/// private to.
#[test]
fn test_private_field_read_rejected_across_modules() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod geom;
            fn main(p: geom::Point) -> i32 { p.y }
            export { main }
        "},
		&[("src/geom.wx", "pub struct Point { pub x: i32, y: i32 }")],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::PrivateStructField
	));
}

#[test]
fn test_private_field_init_rejected_across_modules() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod geom;
            fn main() -> geom::Point { geom::Point::{ x: 1, y: 2 } }
            export { main }
        "},
		&[("src/geom.wx", "pub struct Point { pub x: i32, y: i32 }")],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::PrivateStructField
	));
}

#[test]
fn test_private_field_destructuring_rejected_across_modules() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod geom;
            fn main(p: geom::Point) -> i32 {
                local geom::Point::{ x, y } = p;
                x + y
            }
            export { main }
        "},
		&[("src/geom.wx", "pub struct Point { pub x: i32, y: i32 }")],
	);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::PrivateStructField
	));
}

/// A private field stays readable from the module that declares the struct,
/// and — Rust-style default visibility — from every module nested inside it.
#[test]
fn test_private_field_visible_to_declaring_module_and_descendants() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod geom;
            fn main() -> i32 { geom::read() }
            export { main }
        "},
		&[
			(
				"src/geom.wx",
				indoc! {"
                    mod inner;
                    pub struct Point { y: i32 }
                    pub fn read() -> i32 {
                        local p = Point::{ y: 1 };
                        p.y + inner::read(p)
                    }
                "},
			),
			(
				"src/geom/inner.wx",
				"pub fn read(p: super::Point) -> i32 { p.y }",
			),
		],
	);
	no_errors(&case);
}

/// Reporting is recoverable: the field exists and its type is known, so the
/// expression is still built and nothing downstream re-reports. Exactly one
/// diagnostic, and no cascade of the `undeclared identifier` kind that a
/// poisoned binding would produce.
#[test]
fn test_private_field_access_reports_once_and_recovers() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod geom;
            fn main(p: geom::Point) -> i32 { p.y + p.y }
            export { main }
        "},
		&[("src/geom.wx", "pub struct Point { y: i32 }")],
	);
	let private = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref() == Some(DiagnosticCode::PrivateStructField.code())
		})
		.count();
	assert_eq!(private, 2, "one diagnostic per access, and no more");
	assert!(!has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

// ── export reach ─────────────────────────────────────────────────────────

/// A submodule item used to be unexportable by any spelling: the block did a
/// direct lookup in the package root's own symbol map, so a name that a
/// `use` had put in scope resolved everywhere in the file *except* here.
#[test]
fn test_export_reaches_a_named_import() {
	let case = use_case(
		indoc! {"
            use math::add;
            export { add }
        "},
		"pub fn add() -> i32 { 1 }",
	);
	no_errors(&case);
	assert_eq!(case.tir.export_block.as_ref().unwrap().items.len(), 1);
}

#[test]
fn test_export_reaches_a_glob_import() {
	let case = use_case(
		indoc! {"
            use math::*;
            export { add }
        "},
		"pub fn add() -> i32 { 1 }",
	);
	no_errors(&case);
	assert_eq!(case.tir.export_block.as_ref().unwrap().items.len(), 1);
}

/// The alias renames into wx's scope, so that — not the original — is the
/// name the export block sees, and the wasm export takes the alias too
/// unless the entry renames it again.
#[test]
fn test_export_reaches_an_aliased_import() {
	let case = use_case(
		indoc! {"
            use math::add as plus;
            export { plus }
        "},
		"pub fn add() -> i32 { 1 }",
	);
	no_errors(&case);
	let block = case.tir.export_block.as_ref().unwrap();
	assert_eq!(block.items.len(), 1);
}

/// Reaching through the scope chain must not reach *past* what's visible:
/// a non-`pub` submodule item stays unexportable, and says why.
#[test]
fn test_export_cannot_reach_a_private_item_through_a_glob() {
	let case = use_case(
		indoc! {"
            use math::*;
            export { hidden }
        "},
		"fn hidden() -> i32 { 1 }",
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"a private item is not in scope here, so it is not exportable: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	assert!(case.tir.export_block.as_ref().unwrap().items.is_empty());
}

#[test]
fn test_second_export_block_reports_duplicate() {
	let case = TestCase::new(indoc! {"
        fn foo() -> i32 { 42 }
        fn bar() -> i32 { 43 }

        export { foo }
        export { bar }
    "});

	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::DuplicateExportBlock
	));
	// The first block still owns the slot, so its exports are unaffected —
	// the second block is rejected, not merged in.
	let block = case.tir.export_block.as_ref().unwrap();
	assert_eq!(block.items.len(), 1);
}

#[test]
fn test_export_block_in_submodule_reports_not_at_root() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod math;

            fn main() -> i32 { math::add() }

            export { main }
        "},
		&[("src/math.wx", "pub fn add() -> i32 { 1 }\nexport { add }")],
	);

	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::ExportBlockNotAtRoot
	));
}

#[test]
fn test_export_block_in_inline_module_reports_not_at_root() {
	// An inline `mod` in the entry file has a namespace of its own, so the
	// single "is this the package root's namespace?" comparison catches it
	// for the same reason it catches a separate module file.
	let case = TestCase::new(indoc! {"
        mod inner {
            pub fn f() -> i32 { 1 }
            export { f }
        }
    "});

	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::ExportBlockNotAtRoot
	));
}

/// A block rejected for sitting in the wrong place must not claim the
/// package's one export slot on its way out — otherwise the entry file's
/// legitimate block gets reported as a duplicate of a block that was
/// itself rejected, and the real ABI silently loses its exports.
#[test]
fn test_misplaced_export_block_does_not_claim_the_export_slot() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod math;

            fn main() -> i32 { math::add() }

            export { main }
        "},
		&[("src/math.wx", "pub fn add() -> i32 { 1 }\nexport { add }")],
	);

	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::ExportBlockNotAtRoot
	));
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::DuplicateExportBlock),
		"the entry file's block is the only one that claimed the slot, so \
		 nothing should be reported as a duplicate: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	let block = case
		.tir
		.export_block
		.as_ref()
		.expect("the entry file's block still owns the slot");
	assert_eq!(block.items.len(), 1);
}

#[test]
fn test_library_package_cannot_export() {
	let case = TestCase::new_library(indoc! {"
        pub fn add() -> i32 { 1 }

        export { add }
    "});

	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::LibraryCannotExport
	));
	assert!(
		case.tir.export_block.is_none(),
		"a library has no ABI, so nothing should have been exported"
	);
}

#[test]
fn test_duplicate_export() {
	let case = TestCase::new(indoc! {"
        fn foo() -> i32 { 42 }
        fn bar() -> i32 { 43 }

        export {
            foo as \"add\",
            bar as \"add\",
        }
    "});

	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateExport),
		"expected E1018 (DuplicateExport), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_export_enum_reports_cannot_export_not_undeclared() {
	// Regression test: `Status` is a real, declared item — exporting it
	// used to fall through to "undeclared identifier" (E1007) because the
	// export lookup only checked the value namespace, where enum names
	// never live. It should report E1019 (CannotExportItem) instead.
	let case = TestCase::new(indoc! {"
        enum Status: u8 {
            Ok = 200,
        }

        export {
            Status,
        }
    "});

	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotExportItem),
		"expected E1019 (CannotExportItem), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"should not report E1007 (UndeclaredIdentifier) for a real, non-exportable item: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	assert_eq!(
		case.tir.items.enums[0].accesses.len(),
		1,
		"the `Status` mention in `export {{ Status }}` must still be recorded as an \
		 access so the LSP can resolve hover/go-to-definition on it despite the error"
	);
}

#[test]
fn test_export_generic_function_reports_cannot_export() {
	// Regression test: exporting a generic function used to pass TIR
	// silently and only fail later, in the MIR phase, with a much less
	// helpful error. It should be rejected at export time instead.
	let case = TestCase::new(indoc! {"
        fn identity<T>(value: T) -> T {
            value
        }

        export {
            identity,
        }
    "});

	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotExportItem),
		"expected E1019 (CannotExportItem), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| {
			case.graph
				.interner
				.resolve(f.name.inner)
				.map(|n| n == "identity")
				.unwrap_or(false)
		})
		.expect("function 'identity' not found in TIR");
	assert_eq!(
		func.accesses.len(),
		1,
		"the `identity` mention in `export {{ identity }}` must still be recorded as \
		 an access so the LSP can resolve hover/go-to-definition on it despite the error"
	);
}

#[test]
fn test_export_const_reports_cannot_export_and_records_access() {
	// `const` is never emitted as a WASM global (it's inlined at every use
	// site), so it can't be exported either — but the mention should still
	// be recorded as an access for the LSP.
	let case = TestCase::new(indoc! {"
        const LIMIT: i32 = 10;

        export {
            LIMIT,
        }
    "});

	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotExportItem),
		"expected E1019 (CannotExportItem), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	let constant = case
		.tir
		.items
		.constants
		.iter()
		.find(|c| {
			case.graph
				.interner
				.resolve(c.name.inner)
				.map(|n| n == "LIMIT")
				.unwrap_or(false)
		})
		.expect("const 'LIMIT' not found in TIR");
	assert_eq!(
		constant.accesses.len(),
		1,
		"the `LIMIT` mention in `export {{ LIMIT }}` must still be recorded as an \
		 access so the LSP can resolve hover/go-to-definition on it despite the error"
	);
}

#[test]
fn test_duplicate_export_with_alias() {
	let case = TestCase::new(indoc! {"
        fn foo() -> i32 { 42 }
        fn bar() -> i32 { 43 }

        export {
            foo,
            bar as \"foo\",
        }
    "});

	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateExport),
		"expected E1018 (DuplicateExport), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_parse_simple_addition() {
	let case = TestCase::new(indoc! {"
        fn add(a: i32, b: i32) -> i32 { a + b }

        export { add, add as \"plus\" }
    "});
	insta::assert_yaml_snapshot!(case.tir);
}

#[test]
fn test_parse_import_with_alias() {
	let case = TestCase::new(indoc! {"
        import \"console\" as console {
            fn log(ptr: u32, len: u32) -> ();
        }

        fn main() {
            console::log(0, 0);
        }

        export { main }
    "});
	insta::assert_yaml_snapshot!(case.tir);
}

#[test]
fn test_imported_global() {
	let case = TestCase::new(indoc! {"
        import \"env\" as env {
            global counter: i32;
            global mut flag: bool;
        }

        fn read() -> i32 {
            env::counter
        }

        export { read }
    "});
	// TODO: change to diagnostics.is_empty() once unused-warning for lib/stdlib
	// items is fixed
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity
				== codespan_reporting::diagnostic::Severity::Error)
	);
	// Both imported globals land in tir.items.globals with no value and namespace
	// pointing to the import block.
	assert_eq!(case.tir.items.globals.len(), 2);
	assert!(case.tir.items.globals.iter().all(|g| g.value.is_none()));
	assert!(
		case.tir
			.items
			.globals
			.iter()
			.all(|g| case.tir.is_import_namespace(g.namespace))
	);
	// They appear in the import_decl lookup.
	let decl = &case.tir.modules.import_decls[0];
	assert_eq!(decl.lookup.len(), 2);
}

#[test]
fn test_import_without_alias_reports_error_but_recovers() {
	let case = TestCase::new(indoc! {"
        import \"env\" {
            fn log(message: i32);
        }

        fn main() {
            env::log(42);
        }

        export { main }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::MissingImportAlias
	));
	// Recovery: the missing alias falls back to the module string as the
	// namespace name, so the call site below still resolves instead of
	// cascading into an unrelated "undeclared identifier" error.
	assert!(!has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

#[test]
fn test_local_variable_used_in_import_call() {
	let case = TestCase::new(indoc! {"
        import \"console\" as console {
            fn log(ptr: u32, len: u32);
        }

        fn main() {
            local length = \"test\".len();
            console::log(0, length);
        }

        export { main }
    "});
	insta::assert_yaml_snapshot!(case.tir);
}

#[test]
fn test_local_with_type_annotation_invalid_rhs_recovers() {
	// When the RHS of a `local` declaration fails to resolve (e.g. unknown function),
	// the checker must still register the local with the declared type so that
	// subsequent uses don't cascade into "undeclared identifier" errors.
	let case = TestCase::new(indoc! {"
        fn use_ptr(x: u32) -> u32 { x }
        fn main() -> u32 {
            local p: u32 = unknown_fn()
            use_ptr(p)
        }
        export { main }
    "});
	// Exactly one error: unknown_fn is undeclared. No cascading error for `p`.
	assert_eq!(case.tir.diagnostics.len(), 1);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

#[test]
fn test_generic_call_arg_mismatch_preserves_function_body() {
	// Regression: `build_generic_call_arguments` returned `Err(())` on a plain
	// argument type mismatch (an already-fully-diagnosed, recoverable error —
	// unlike an unresolvable type param), and every caller up the chain
	// (`build_call_expression` -> `build_expression` -> `build_block_result`
	// -> `build_block_expression` -> `build_function_body`) propagated that
	// `Err` with `?` all the way out. `ensure_body` then left `function.body`
	// as `None` entirely — not just the failing call, the *whole* body,
	// including the unrelated `local ptr = ...` statement. With no body at
	// all, LSP hover/go-to-definition on `ptr` had nothing to look up.
	// `build_generic_call_arguments` is now infallible: it still reports the
	// diagnostic but returns a usable `type_args` (sanitizing any leftover
	// `INFER` to `ERROR`), so callers keep building a real expression tree.
	let case = TestCase::new(indoc! {"
        #[memory_limits(min_pages = 1)]
        memory heap: Memory where { Size = u32 };
        fn make_ptr() -> heap::&u16 { unreachable }
        fn f(count: heap::Size) -> heap::&[u8] {
            local ptr = make_ptr();
            std::slice_from_parts(ptr, count)
        }
        export { heap as \"memory\", f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (type mismatch), got: {:?}",
		case.tir.diagnostics
	);
	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| {
			case.graph
				.interner
				.resolve(f.name.inner)
				.map(|n| n == "f")
				.unwrap_or(false)
		})
		.expect("function 'f' not found");
	let body = func.body.as_ref().expect(
		"function body should be preserved despite the argument mismatch",
	);
	let ExprKind::Block {
		expressions,
		result,
		..
	} = &body.block.kind
	else {
		panic!("expected a block expression");
	};
	assert_eq!(expressions.len(), 1, "expected the `local ptr` statement");
	let ExprKind::GenericCall { arguments, .. } =
		&result.as_ref().expect("expected a tail expression").kind
	else {
		panic!(
			"expected the tail expression to be the `slice_from_parts` call"
		);
	};
	assert!(
		matches!(arguments[0].kind, ExprKind::Local { .. }),
		"expected `ptr`'s reference to survive as a Local node, got: {:?}",
		arguments[0].kind
	);
	assert_ne!(
		arguments[0].ty,
		TypeIndex::ERROR,
		"`ptr`'s real (mismatched) type should be preserved, not poisoned to ERROR"
	);
}

#[test]
fn test_local_with_pointer_type_annotation_dereference_recovers() {
	// When the RHS errors (e.g. `alloc` is undeclared), the local must still carry
	// the declared pointer type so that `n.*` doesn't cascade into a "not a pointer" error.
	let case = TestCase::new(indoc! {"
        #[memory_limits(min_pages = 1)]
        memory heap: Memory where { Size = u32 }
        struct Node { x: i32 }
        fn write(x: i32) {
            local p: heap::*Node = alloc_node()
            p.*.x = x
        }
        export { write }
    "});
	// Only one error: alloc_node is undeclared. No cascading pointer/field errors.
	assert_eq!(case.tir.diagnostics.len(), 1);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

#[test]
fn test_assign_to_undeclared_identifier_no_e1013() {
	// Assignment to an undeclared variable should produce only E1007 (undeclared
	// identifier), not a cascading E1013 (invalid assignment target).
	let case = TestCase::new(indoc! {"
        fn f() {
            undeclared_var = 42
        }
        export { f }
    "});
	assert_eq!(case.tir.diagnostics.len(), 1);
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::UndeclaredIdentifier
	));
}

#[test]
fn test_compare_mutable_pointer_with_null() {
	// `cur == ptr::null()` must infer M and T for null<M,T>() from the type of `cur`
	// (`heap::*Node`), even though null()'s return type is an immutable pointer.
	// Previously `infer_type_args` required matching mutability, causing E1002.
	let case = TestCase::new(indoc! {"
        #[memory_limits(min_pages = 1)]
        memory heap: Memory where { Size = u32 }
        struct Node { x: i32 }
        fn is_null(p: heap::&Node) -> bool {
            p == ptr::null()
        }
        export { is_null }
    "});
	assert!(case.tir.diagnostics.is_empty());
}

fn has_error_code(tir: &TIR, code: DiagnosticCode) -> bool {
	tir.diagnostics
		.iter()
		.any(|d| d.code.as_deref() == Some(code.code()))
}

// ── coerce_untyped_int_expr ──────────────────────────────────────────────

#[test]
fn test_coerce_int_to_i32() {
	let case = TestCase::new("fn f() -> i32 { 42 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_to_i64() {
	let case = TestCase::new("fn f() -> i64 { 9999999999 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_to_u32() {
	let case = TestCase::new("fn f() -> u32 { 100 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_to_u64() {
	let case = TestCase::new("fn f() -> u64 { 0 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_overflow_i32() {
	// i32::MAX + 1 = 2147483648 overflows i32
	let case = TestCase::new("fn f() -> i32 { 2147483648 } export { f }");
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IntegerLiteralOutOfRange),
		"expected E1004 (out of range), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_negative_for_u32() {
	let case = TestCase::new("fn f() -> u32 { -1 } export { f }");
	// `-1` is `Unary { InvertSign, Int(1) }` — coerce_untyped_unary_expr
	// allows InvertSign for any signed numeric target (i8/i16/i32/i64/
	// f32/f64) but deliberately excludes unsigned targets, so u32
	// produces E1005 (UnableToCoerce).
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnableToCoerce),
		"expected E1005 (UnableToCoerce) for negated literal coerced to u32, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_coerce_negated_literal_to_every_signed_width_and_float() {
	// Regression test: `coerce_untyped_unary_expr`'s target-type allowlist
	// used to only accept i32/i64 for `InvertSign`, rejecting `-1`/`-1.5`
	// coerced to any other signed numeric type.
	let case = TestCase::new(indoc! {"
        fn a() -> i8 { -1 }
        fn b() -> i16 { -1 }
        fn c() -> i32 { -1 }
        fn d() -> i64 { -1 }
        fn e() -> f32 { -1.5 }
        fn f() -> f64 { -1.5 }
        export { a, b, c, d, e, f }
    "});
	no_errors(&case);
}

#[test]
fn test_coerce_min_value_literal_for_every_signed_width() {
	// Regression test: two's-complement's negative range holds one more
	// magnitude than its positive range (`i8::MIN` is `-128` but `i8::MAX`
	// is only `127`) — `coerce_untyped_unary_expr` used to range-check the
	// un-negated magnitude against the ordinary positive-max bound,
	// wrongly rejecting exactly the most-negative value of each width.
	let case = TestCase::new(indoc! {"
        fn a() -> i8 { -128 }
        fn b() -> i16 { -32768 }
        fn c() -> i32 { -2147483648 }
        fn d() -> i64 { -9223372036854775808 }
        export { a, b, c, d }
    "});
	no_errors(&case);
}

#[test]
fn test_coerce_one_past_min_value_literal_still_out_of_range() {
	let case = TestCase::new("fn f() -> i8 { -129 } export { f }");
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IntegerLiteralOutOfRange),
		"expected E1004 (out of range) for `-129i8` (one past `i8::MIN`), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_u64_max_literal_succeeds() {
	// Regression test: `parse_integer_literal` used to parse straight into
	// `i64`, so any literal magnitude beyond `i64::MAX` (including
	// `u64::MAX` itself, a purely positive literal with no negation
	// involved) failed to parse at all.
	let case =
		TestCase::new("fn f() -> u64 { 18446744073709551615 } export { f }");
	no_errors(&case);
}

#[test]
fn test_eval_const_expr_double_negated_i64_min_does_not_panic() {
	// `-(-9223372036854775808)` — the inner negation must fold via
	// `wrapping_neg` (not a bare `-`, which would panic on `i64::MIN`).
	let case = TestCase::new(
		"const X: i64 = -(-9223372036854775808); fn f() -> i64 { X } export { f }",
	);
	no_errors(&case);
}

#[test]
fn test_eval_const_expr_u64_div_uses_unsigned_semantics() {
	// Regression test: `eval_const_expr`'s `Div`/`Rem` folding used to
	// operate on the bit-reinterpreted `i64` unconditionally — correct
	// for `Add`/`Sub`/`Mul` (representation-agnostic in two's complement)
	// but wrong for division, where signed vs. unsigned interpretation of
	// the same bits genuinely differ once a `u64` magnitude exceeds
	// `i64::MAX`. `u64::MAX` bit-casts to `-1i64`, and `-1i64 / 2 == 0`
	// under signed division — but the correct unsigned answer is
	// `9223372036854775807`.
	let case = TestCase::new(indoc! {"
        #[tag = \"x\"]
        const X: u64 = 18446744073709551615 / 2;
        export {}
    "});
	no_errors(&case);
	let tag = case.graph.interner.get("x").unwrap();
	let def_id = *case.tir.items.tagged_items.get(&tag).unwrap();
	let const_index = case.tir.items.expect_const_index(def_id);
	assert_eq!(
		case.tir.items.constants[usize::from(const_index)].const_value,
		Some(ConstValue::Int(9223372036854775807))
	);
}

#[test]
fn test_eval_const_expr_u64_rem_uses_unsigned_semantics() {
	let case = TestCase::new(indoc! {"
        #[tag = \"x\"]
        const X: u64 = 18446744073709551615 % 100;
        export {}
    "});
	no_errors(&case);
	let tag = case.graph.interner.get("x").unwrap();
	let def_id = *case.tir.items.tagged_items.get(&tag).unwrap();
	let const_index = case.tir.items.expect_const_index(def_id);
	assert_eq!(
		case.tir.items.constants[usize::from(const_index)].const_value,
		Some(ConstValue::Int(15))
	);
}

#[test]
fn test_eval_const_expr_signed_div_unaffected_by_unsigned_fix() {
	let case = TestCase::new(indoc! {"
        #[tag = \"x\"]
        const X: i64 = -10 / 3;
        export {}
    "});
	no_errors(&case);
	let tag = case.graph.interner.get("x").unwrap();
	let def_id = *case.tir.items.tagged_items.get(&tag).unwrap();
	let const_index = case.tir.items.expect_const_index(def_id);
	assert_eq!(
		case.tir.items.constants[usize::from(const_index)].const_value,
		Some(ConstValue::Int(-3))
	);
}

#[test]
fn test_eval_const_expr_float_div_by_zero_folds_to_infinity() {
	// Regression test: `eval_const_expr`'s `Binary` arm used to only
	// destructure `ConstValue::Int` operands, so any float arithmetic
	// (including this) was rejected as not-const-evaluatable rather than
	// following plain IEEE-754 semantics the way runtime float division
	// already does.
	let case = TestCase::new(indoc! {"
        #[tag = \"x\"]
        const X: f32 = 1.0 / 0.0;
        export {}
    "});
	no_errors(&case);
	let tag = case.graph.interner.get("x").unwrap();
	let def_id = *case.tir.items.tagged_items.get(&tag).unwrap();
	let const_index = case.tir.items.expect_const_index(def_id);
	assert_eq!(
		case.tir.items.constants[usize::from(const_index)].const_value,
		Some(ConstValue::Float(f64::INFINITY))
	);
}

#[test]
fn test_eval_const_expr_float_neg_div_by_zero_folds_to_neg_infinity() {
	let case = TestCase::new(indoc! {"
        #[tag = \"x\"]
        const X: f32 = -1.0 / 0.0;
        export {}
    "});
	no_errors(&case);
	let tag = case.graph.interner.get("x").unwrap();
	let def_id = *case.tir.items.tagged_items.get(&tag).unwrap();
	let const_index = case.tir.items.expect_const_index(def_id);
	assert_eq!(
		case.tir.items.constants[usize::from(const_index)].const_value,
		Some(ConstValue::Float(f64::NEG_INFINITY))
	);
}

#[test]
fn test_eval_const_expr_zero_div_zero_folds_to_nan() {
	let case = TestCase::new(indoc! {"
        #[tag = \"x\"]
        const X: f32 = 0.0 / 0.0;
        export {}
    "});
	no_errors(&case);
	let tag = case.graph.interner.get("x").unwrap();
	let def_id = *case.tir.items.tagged_items.get(&tag).unwrap();
	let const_index = case.tir.items.expect_const_index(def_id);
	let Some(ConstValue::Float(value)) =
		case.tir.items.constants[usize::from(const_index)].const_value
	else {
		panic!("expected a folded float const");
	};
	assert!(value.is_nan());
}

#[test]
fn test_f32_nan_infinity_neg_infinity_consts_resolve() {
	let case = TestCase::new(indoc! {"
        fn f() -> bool {
            f32::NAN != f32::NAN
                && f32::INFINITY > 0.0
                && f32::NEG_INFINITY < 0.0
        }
        export { f }
    "});
	no_errors(&case);
}

#[test]
fn test_f64_nan_infinity_neg_infinity_consts_resolve() {
	let case = TestCase::new(indoc! {"
        fn f() -> bool {
            f64::NAN != f64::NAN
                && f64::INFINITY > 0.0
                && f64::NEG_INFINITY < 0.0
        }
        export { f }
    "});
	no_errors(&case);
}

#[test]
fn test_coerce_int_literal_for_float_type_errors() {
	// An untyped integer literal cannot be coerced to f32 (must write 1.0)
	let case = TestCase::new("fn f() -> f32 { 1 } export { f }");
	assert!(
		has_error_code(&case.tir, DiagnosticCode::LiteralTypeMismatch),
		"expected E1006 (int literal for float type), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_to_bool_errors() {
	let case = TestCase::new("fn f() -> bool { 1 } export { f }");
	// int literal is not coercible to bool — expect E1005 (unable to coerce)
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnableToCoerce),
		"expected E1005 (unable to coerce), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── coerce_untyped_float_expr ────────────────────────────────────────────

#[test]
fn test_coerce_float_to_f32() {
	let case = TestCase::new("fn f() -> f32 { 3.14 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_float_to_f64() {
	let case = TestCase::new("fn f() -> f64 { 2.718 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_float_to_i32_errors() {
	let case = TestCase::new("fn f() -> i32 { 1.5 } export { f }");
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnableToCoerce),
		"expected E1005 (unable to coerce float to i32), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── binary arithmetic coercion ───────────────────────────────────────────

#[test]
fn test_coerce_binary_arithmetic_i32() {
	let case = TestCase::new("fn f() -> i32 { 1 + 2 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_binary_bitwise_i32() {
	let case = TestCase::new("fn f() -> i32 { 10 & 12 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_primitive_bitwise_compound_assign_operators() {
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local mut x: i32 = 10;
            x &= 12;
            x |= 3;
            x ^= 5;
            x <<= 1;
            x >>= 2;
            x
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── direct coercion to small integer types ───────────────────────────────

#[test]
fn test_coerce_int_to_i8() {
	let case = TestCase::new("fn f() -> i8 { 127 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_to_u8() {
	let case = TestCase::new("fn f() -> u8 { 255 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_to_i16() {
	let case = TestCase::new("fn f() -> i16 { 1000 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_int_to_u16() {
	let case = TestCase::new("fn f() -> u16 { 65535 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── float binary arithmetic propagation ─────────────────────────────────

#[test]
fn test_coerce_binary_arithmetic_f32() {
	let case = TestCase::new("fn f() -> f32 { 1.5 + 0.5 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_binary_arithmetic_f64() {
	let case = TestCase::new("fn f() -> f64 { 1.0 + 2.0 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_binary_float_multiply() {
	let case = TestCase::new("fn f() -> f64 { 2.0 * 3.0 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── INTEGER + FLOAT mismatch ─────────────────────────────────────────────

#[test]
fn test_integer_plus_float_literal_errors() {
	// 1 is INTEGER, 1.0 is FLOAT — different comptime kinds → type mismatch
	let case = TestCase::new("fn f() -> i32 { 1 + 1.0 } export { f }");
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (type mismatch for INTEGER + FLOAT), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_float_plus_integer_literal_errors() {
	// Symmetric: FLOAT on the left, INTEGER on the right
	let case = TestCase::new("fn f() -> f64 { 1.0 + 1 } export { f }");
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (type mismatch for FLOAT + INTEGER), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── if without else ──────────────────────────────────────────────────────

#[test]
fn test_if_without_else_returning_value_is_error() {
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local x: i32 = if true { 5 };
            x
        }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::MissingElseBlock));
}

#[test]
fn test_if_without_else_unit_body_is_ok() {
	let case = TestCase::new(indoc! {"
        fn f() {
            if true { local x: i32 = 1; }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_if_bad_condition_still_checks_branches() {
	let case = TestCase::new(indoc! {"
        fn f() {
            if undefined_var { undefined_then(); } else { undefined_else(); }
        }
    "});
	let count = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::UndeclaredIdentifier.code())
		})
		.count();
	assert_eq!(
		count,
		3,
		"expected an UndeclaredIdentifier for the condition and each branch, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── chained (nested) comptime binary expressions ─────────────────────────

#[test]
fn test_coerce_chained_integer_arithmetic() {
	// All three literals are INTEGER; type propagates through both additions
	let case = TestCase::new("fn f() -> i32 { 1 + 2 + 3 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_coerce_chained_float_arithmetic() {
	let case = TestCase::new("fn f() -> f64 { 1.0 + 2.0 + 3.0 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── typed operand drives coercion of comptime literal ────────────────────

#[test]
fn test_comptime_right_operand_coerced_by_typed_left() {
	// x has concrete type i32; literal `1` (INTEGER) on the right gets coerced
	let case = TestCase::new("fn f(x: i32) -> i32 { x + 1 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_left_operand_coerced_by_typed_right() {
	// literal `1` (INTEGER) on the left, x has concrete type i32 on the right
	let case = TestCase::new("fn f(x: i32) -> i32 { 1 + x } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_float_operand_coerced_by_typed_variable() {
	let case = TestCase::new("fn f(x: f64) -> f64 { x + 1.0 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── coercion through local variable binding ──────────────────────────────

#[test]
fn test_comptime_integer_coerced_in_local_binding() {
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local x: i32 = 1 + 2;
            x
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_float_coerced_in_local_binding() {
	let case = TestCase::new(indoc! {"
        fn f() -> f64 {
            local x: f64 = 1.0 + 2.0;
            x
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_integer_local_missing_annotation_errors() {
	// No type annotation on the binding and no outer context → type annotation
	// required
	let case = TestCase::new(indoc! {"
        fn f() {
            local x = 1 + 2;
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeAnnotationRequired),
		"expected E1002 (type annotation required), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── coercion through function call arguments ─────────────────────────────

#[test]
fn test_comptime_literal_coerced_by_fn_param_type() {
	let case = TestCase::new(indoc! {"
        fn add(a: i32, b: i32) -> i32 { a + b }
        fn f() -> i32 { add(1, 2) }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_float_literal_coerced_by_fn_param_type() {
	let case = TestCase::new(indoc! {"
        fn scale(x: f32, factor: f32) -> f32 { x * factor }
        fn f(x: f32) -> f32 { scale(x, 2.0) }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── comparison operators with comptime literals ──────────────────────────

#[test]
fn test_comptime_integers_standalone_comparison_requires_annotation() {
	// `1 == 2` has no type context: cannot decide i32.eq vs i64.eq → E1014
	let case = TestCase::new("fn f() -> bool { 1 == 2 } export { f }");
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::ComparisonTypeAnnotationRequired
		),
		"expected E1014 (comparison annotation required), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_integer_coerced_by_typed_comparand() {
	// Typed variable on the left drives coercion of the literal on the right
	let case = TestCase::new("fn f(x: i32) -> bool { x == 1 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_integer_coerced_by_typed_comparand_on_right() {
	let case = TestCase::new("fn f(x: i32) -> bool { 1 == x } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_float_coerced_by_typed_comparand() {
	let case = TestCase::new("fn f(x: f64) -> bool { x < 1.0 } export { f }");
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_comptime_integer_vs_float_comparison_errors() {
	// When both sides are comptime numbers (INTEGER and FLOAT), the comparison
	// builder emits E1014 (ComparisonTypeAnnotationRequired) since neither side
	// has a concrete type to drive resolution.
	let case = TestCase::new("fn f() -> bool { 1 == 1.0 } export { f }");
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::ComparisonTypeAnnotationRequired
		),
		"expected E1014 (ComparisonTypeAnnotationRequired) for INTEGER == FLOAT, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

// ── struct definition & initialization ──────────────────────────────────

/// Basic valid struct definition and initialization.
#[test]
fn test_struct_valid_init() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
            pub y: i32,
        }

        fn make() -> Point {
            Point::{ x: 1, y: 2 }
        }

        export { make }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	insta::assert_yaml_snapshot!(case.tir);
}

/// Shorthand field init `{ x }` should behave like `{ x: x }`.
#[test]
fn test_struct_shorthand_init() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
            pub y: i32,
        }

        fn make(x: i32, y: i32) -> Point {
            Point::{ x, y }
        }

        export { make }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Fields may be provided in any order.
#[test]
fn test_struct_init_out_of_order() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
            pub y: i32,
        }

        fn make() -> Point {
            Point::{ y: 2, x: 1 }
        }

        export { make }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Duplicate field in the struct *definition* should produce E1022.
#[test]
fn test_struct_duplicate_field_definition() {
	let case = TestCase::new(indoc! {"
        struct Bad {
            pub x: i32,
            pub x: i32,
        }

        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateStructField),
		"expected E1022 (duplicate struct field), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Using an undeclared name in struct init position should produce an error.
#[test]
fn test_struct_init_undeclared_name() {
	let case = TestCase::new(indoc! {"
        fn main() {
            Unknown::{ }
        }

        export { main }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected E1021 (UndeclaredType) for unknown struct name, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

/// Unknown field name in struct init should produce E1025.
#[test]
fn test_struct_init_unknown_field() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
            pub y: i32,
        }

        fn make() -> Point {
            Point::{ x: 1, y: 2, z: 3 }
        }

        export { make }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnknownStructField),
		"expected E1025 (unknown struct field), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Specifying the same field twice in init should produce E1026 but NOT
/// E1027 (the field was mentioned, just duplicated — it should not
/// appear as missing).
#[test]
fn test_struct_init_duplicate_field() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
            pub y: i32,
        }

        fn make() -> Point {
            Point::{ x: 1, y: 2, x: 3 }
        }

        export { make }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateStructFieldInit),
		"expected E1026 (duplicate field in init), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	// x was mentioned (just duplicated) — must NOT also appear as missing
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::MissingStructFields),
		"E1027 must not fire for a duplicated field (it was mentioned)"
	);
}

/// Omitting required fields in init should produce E1027.
#[test]
fn test_struct_init_missing_fields() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
            pub y: i32,
        }

        fn make() -> Point {
            Point::{ x: 1 }
        }

        export { make }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::MissingStructFields),
		"expected E1027 (missing fields), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// A field whose value fails type-checking should NOT cause that field to
/// appear in the missing-fields list (E1027).
#[test]
fn test_struct_init_errored_field_not_reported_as_missing() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
            pub y: i32,
        }

        fn make() -> Point {
            Point::{ x: true, y: 2 }
        }

        export { make }
    "});
	// Should have E1001 (TypeMistmatch) for field `x` receiving a bool instead of i32.
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (TypeMistmatch) for bool assigned to i32 field, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	// …but must NOT report `x` as a missing field
	let missing_x = case.tir.diagnostics.iter().any(|d| {
		d.code.as_deref() == Some(DiagnosticCode::MissingStructFields.code())
			&& d.message.contains('x')
	});
	assert!(
		!missing_x,
		"errored field `x` must not be reported as missing"
	);
}

/// Snapshot test for the duplicate-field-in-init case to lock in diagnostic
/// details.
#[test]
fn test_structs() {
	let case = TestCase::new(indoc! {"
        struct str {
            pub ptr: u32,
            pub len: u32,
        }

        fn main() -> str {
            str::{ ptr: 0, ptr: 10 }
        }

        export { main }
    "});
	insta::assert_yaml_snapshot!(case.tir);
}

// ── char / primitive type tests ──────────────────────────────────────────

/// `char` is a built-in primitive — comparisons work without any stdlib.
#[test]
fn test_stdlib_types_available() {
	let case = TestCase::new(indoc! {"
        fn is_lower(c: char) -> bool {
            c >= 'a' && c <= 'z'
        }

        export { is_lower }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// `char` deliberately has no `impl Add`/`impl Sub` of its own — matching
/// Rust, arithmetic on a `char` requires an explicit cast to an integer
/// type first (`std/main.wx`'s own `to_ascii_uppercase`/`to_ascii_lowercase`
/// use the same `(self as u8) ... as char` idiom).
#[test]
fn test_char_arithmetic_requires_explicit_cast() {
	let case = TestCase::new(indoc! {"
        fn shift(c: char) -> char {
            ((c as u8) - 32) as char
        }

        export { shift }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// The direct-arithmetic counterpart of the above: `char - int` without a
/// cast must be rejected, not silently allowed — locks in the design
/// decision (char arithmetic is opt-in via cast, not implicit) as an
/// explicit regression test rather than an accident of `char` simply
/// lacking an impl.
#[test]
fn test_char_arithmetic_without_cast_is_error() {
	let case = TestCase::new(indoc! {"
        fn shift(c: char) -> char {
            c - 32
        }

        export { shift }
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::BinaryOperatorCannotBeApplied
		),
		"expected E1008 (BinaryOperatorCannotBeApplied) for `char - int` without a cast, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Accessing a method via field syntax (`p.area`, no call parens) must
/// report a diagnostic (E1060) instead of panicking.
#[test]
fn test_method_accessed_as_field_is_error() {
	let case = TestCase::new(indoc! {"
        struct Point {
            pub x: i32,
        }

        impl Point {
            pub fn area(self) -> i32 {
                self.x
            }
        }

        fn f(p: Point) -> i32 {
            p.area
        }

        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::NotAField),
		"expected E1060 (not a field), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Methods on built-in types defined in stdlib are callable from user code.
#[test]
fn test_stdlib_method_callable() {
	let case = TestCase::new(indoc! {"
        fn uppercase(c: char) -> char {
            c.to_ascii_uppercase()
        }

        export { uppercase }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// impl methods and associated functions are registered in the impl block's
/// `members` under the correct `ImplEntry` variant.
#[test]
fn test_impl_members_registered() {
	let case = TestCase::new(indoc! {"
        struct Signed { value: i32 }

        impl Signed {
            pub fn magnitude(self) -> i32 {
                if self.value < 0 { -self.value } else { self.value }
            }

            pub fn from_flag(b: bool) -> i32 {
                if b { 1 } else { 0 }
            }
        }

        fn use_them(x: i32, b: bool) -> i32 {
            Signed::{ value: x }.magnitude() + Signed::from_flag(b)
        }

        export { use_them }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	let method_sym = case
		.graph
		.interner
		.get("magnitude")
		.expect("symbol not interned");
	let assoc_fn_sym = case
		.graph
		.interner
		.get("from_flag")
		.expect("symbol not interned");

	// `inherent_impls` holds every one of the stdlib's blocks too, so find
	// this one by membership rather than assuming it's the only one.
	let members = &case
		.tir
		.items
		.inherent_impls
		.iter()
		.find(|b| b.members.contains_key(&method_sym))
		.expect("inherent_impls should have the `Signed` block")
		.members;

	// method takes `self` → Method; assoc fn has no receiver → AssociatedFn
	let method_entry = members
		.get(&method_sym)
		.expect("method missing from members");
	let assoc_fn_entry = members
		.get(&assoc_fn_sym)
		.expect("assoc fn missing from members");

	assert!(
		matches!(method_entry, ImplEntry::Method(_)),
		"method should be ImplEntry::Method, got {:?}",
		method_entry
	);
	assert!(
		matches!(assoc_fn_entry, ImplEntry::AssocFunction(_)),
		"assoc fn should be ImplEntry::AssociatedFn, got {:?}",
		assoc_fn_entry
	);

	// Both entries must point to valid function indices
	let &ImplEntry::Method(method_idx) = method_entry else {
		unreachable!()
	};
	let &ImplEntry::AssocFunction(assoc_fn_idx) = assoc_fn_entry else {
		unreachable!()
	};
	assert!(
		(usize::from(method_idx)) < case.tir.items.functions.len(),
		"method func_index out of bounds"
	);
	assert!(
		(usize::from(assoc_fn_idx)) < case.tir.items.functions.len(),
		"assoc fn func_index out of bounds"
	);
}

/// `pub fn` on a user-defined function suppresses the unused warning.
#[test]
fn test_pub_fn_no_unused_warning() {
	let case = TestCase::new(indoc! {"
        pub fn helper() -> i32 {
            42
        }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"expected no diagnostics for pub fn, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// TIR preserves struct fields in declaration order; physical reordering for
/// optimal memory layout is a MIR concern (tested in mir::tests).
#[test]
fn test_struct_fields_kept_in_declaration_order() {
	let case = TestCase::new(indoc! {"
        struct Mixed {
            a: bool,
            b: i64,
            c: u32,
            d: f64,
        }

        fn dummy(m: Mixed) -> Mixed { m }
        export { dummy }
    "});
	eprintln!(
		"diags: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert!(case.tir.diagnostics.is_empty());

	let mixed_sym = case.graph.interner.get("Mixed").unwrap();
	let struct_index = case
		.tir
		.types
		.entries
		.iter()
		.find_map(|t| {
			if let Type::Struct { struct_index, .. } = t {
				if case.tir.items.structs[usize::from(*struct_index)]
					.name
					.inner == mixed_sym
				{
					Some(*struct_index)
				} else {
					None
				}
			} else {
				None
			}
		})
		.unwrap();
	let field_names: Vec<&str> = case.tir.items.structs
		[usize::from(struct_index)]
	.fields
	.iter()
	.map(|f| case.graph.interner.resolve(f.name.inner).unwrap())
	.collect();
	assert_eq!(field_names, vec!["a", "b", "c", "d"]);
}

/// A non-pub function that is never called should still produce a warning.
#[test]
fn test_non_pub_fn_unused_warning() {
	let case = TestCase::new(indoc! {"
        fn unused() -> i32 {
            42
        }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.message == "function `unused` is never used"),
		"expected unused-function diagnostic"
	);
}

/// Functions declared inside a `mod` block are intrinsics/imports and must
/// not trigger an unused-function warning even if they are never called.
#[test]
fn test_module_fn_no_unused_warning() {
	let case = TestCase::new(indoc! {"
        mod math {
            #[intrinsic]
            fn add(a: i32, b: i32) -> i32;
        }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.message.contains("is never used")),
		"module functions should not warn as unused, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// User-defined struct with `pub struct` should not warn as unused.
#[test]
fn test_pub_struct_no_unused_warning() {
	// Structs don't currently emit unused warnings; this test just
	// verifies that `pub struct` parses and compiles without error.
	let case = TestCase::new(indoc! {"
        pub struct Point {
            pub x: i32,
            pub y: i32,
        }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_memory_declaration_registers_kind() {
	let case32 = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory MEM: Memory where { Size = u32 };
    "},
		&[],
	);
	assert!(case32.tir.diagnostics.is_empty(), "unexpected diagnostics");
	assert_eq!(
		case32
			.tir
			.items
			.memories
			.iter()
			.map(|m| m.size.inner)
			.collect::<Vec<_>>(),
		vec![TypeIndex::U32]
	);

	let case64 = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory MEM: Memory where { Size = u64 };
    "},
		&[],
	);
	assert!(case64.tir.diagnostics.is_empty(), "unexpected diagnostics");
	assert_eq!(
		case64
			.tir
			.items
			.memories
			.iter()
			.map(|m| m.size.inner)
			.collect::<Vec<_>>(),
		vec![TypeIndex::U64]
	);
}

#[test]
fn test_memory_invalid_kind_is_error() {
	let case = TestCase::new("memory MEM: i32;");
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::InvalidMemoryKind.code())),
		"expected invalid memory kind diagnostic"
	);
}

#[test]
fn test_memory_unresolved_kind_does_not_panic() {
	// Regression test: an unresolvable trait bound means the memory's kind
	// can't be determined. This must not leave `MEM` stuck as
	// `SymbolKind::Pending`, which used to panic (`unreachable!`) as soon as
	// anything referenced it.
	let case = TestCase::new(indoc! {"
        memory MEM: NoSuchTrait where { Size = u32 };
        pub fn f() -> u32 { MEM::INDEX }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::InvalidMemoryKind.code())),
		"expected invalid memory kind diagnostic"
	);
}

#[test]
fn test_fn_declaration_without_body_is_error() {
	// A bare `fn` with no body and no #[intrinsic] must produce E0011.
	let case = TestCase::new(indoc! {"
        fn add(a: i32, b: i32) -> i32
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::MissingFunctionBody.code())),
		"expected E0011 diagnostic for missing function body"
	);
}

#[test]
fn test_memory_index_const_resolves() {
	// `MEM::INDEX` — namespace access to a memory constant resolves cleanly.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory MEM: Memory where { Size = u32 };
        pub fn f() -> u32 { MEM::INDEX }
    "},
		&[],
	);
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_memory_size_call_resolves() {
	// `.size_pages()` is a method from the Memory trait; calling it should
	// produce no errors.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory MEM: Memory where { Size = u32 };
        pub fn f() { _ = MEM.size_pages(); }
    "},
		&[],
	);
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_memory_grow_call_resolves() {
	// `.grow()` is a method from the Memory trait; calling it should produce no
	// errors.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory MEM: Memory where { Size = u32 };
        pub fn f() { _ = MEM.grow(1); }
    "},
		&[],
	);
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_memory_unknown_member_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory MEM: Memory where { Size = u32 };
        fn f() { _ = MEM::pages; }
    "},
		&[],
	);
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UndeclaredIdentifier.code())),
		"expected undeclared identifier diagnostic for unknown memory member"
	);
}

#[test]
fn test_memory_as_value_in_expression() {
	// Memory identifiers are valid value expressions (for method calls like
	// MEM.grow(1)).
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory MEM: Memory where { Size = u32 };
        fn f() { _ = MEM; }
    "},
		&[],
	);
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::NamespaceUsedAsValue.code())),
		"memory identifier should be usable as a value expression"
	);
}

// ── impl trait for type
// ───────────────────────────────────────────────────────

#[test]
fn test_impl_trait_for_type_registers_trait_impl() {
	let case = TestCase::new(indoc! {"
        trait Drawable {
            fn draw(self);
        }

        struct Point {
            x: i32,
            y: i32,
        }

        impl Drawable for Point {
            fn draw(self) {
                unreachable
            }
        }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"unexpected errors: {:?}",
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.severity == Severity::Error)
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	let draw_sym = case
		.graph
		.interner
		.get("draw")
		.expect("symbol `draw` not interned");

	// Find the impl that contains `draw` — avoids hardcoding impl indices
	// (stdlib adds its own impls before user ones).
	let ti = case
		.tir
		.items
		.trait_impls
		.iter()
		.find(|ti| ti.members.contains_key(&draw_sym))
		.expect("no TraitImpl has 'draw' method");

	// target type is Point (a struct)
	assert!(
		matches!(case.tir.types.resolve(ti.target.inner), Type::Struct { .. }),
		"target should be a struct type"
	);

	let point_type = ti.target.inner;
	let drawable_index = ti.trait_index;

	// find_trait_impl is queryable for (Point, Drawable)
	assert!(
		case.tir
			.items
			.find_trait_impl(&case.tir.types, point_type, drawable_index)
			.is_some(),
		"find_trait_impl should resolve (Point, Drawable)"
	);

	// trait_impl_dispatch maps Point's outer shape → a list that includes this impl
	let (ti_index, _) = case
		.tir
		.items
		.find_trait_impl(&case.tir.types, point_type, drawable_index)
		.unwrap();
	let kind = ImplTarget::from_type(case.tir.types.resolve(point_type))
		.expect("Point should be a valid impl target");
	assert!(
		case.tir
			.items
			.trait_impl_dispatch
			.get(&kind)
			.map(|v| v.iter().any(|&(_, idx)| idx == ti_index))
			.unwrap_or(false),
		"trait_impl_dispatch should include the Drawable impl for Point"
	);

	// draw method is registered in TraitImpl.members
	assert!(
		matches!(ti.members.get(&draw_sym), Some(ImplEntry::Method(_))),
		"`draw` should be ImplEntry::Method in TraitImpl.members"
	);

	// `impl_block_list` is for inherent impls only — trait-provided methods
	// (like `draw`, from the `Drawable` impl above) are resolved on demand
	// from `trait_impls`/`trait_impl_dispatch` instead (see
	// `Builder::resolve_impl_member`), so they must never leak into an
	// inherent impl block's `members` for `Point`.
	assert!(
		case.tir
			.items
			.inherent_impls
			.iter()
			.filter(|b| b.target.inner == point_type)
			.all(|b| !b.members.contains_key(&draw_sym)),
		"`draw` (a trait method) should not appear in any inherent impl block for Point"
	);
}

// ── inherent vs. trait member dispatch
// ───────────────────────────────────────

#[test]
fn test_inherent_method_wins_over_same_named_trait_method() {
	// `Foo` has both an inherent `greet` and a trait-provided `greet` of the
	// same name — the inherent one must win outright, with no ambiguity
	// diagnostic, exactly like Rust's inherent-shadows-trait rule.
	let case = TestCase::new(indoc! {"
        trait Greeter {
            fn greet(self) -> i32;
        }

        struct Foo {}

        impl Foo {
            pub fn greet(self) -> i32 { 1 }
        }

        impl Greeter for Foo {
            fn greet(self) -> i32 { 2 }
        }

        fn use_it(f: Foo) -> i32 {
            f.greet()
        }

        export { use_it }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"unexpected errors: {:?}",
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.severity == Severity::Error)
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_single_applicable_trait_method_resolves_without_ambiguity() {
	// Only one trait provides `foo` for `S` — resolution must succeed
	// cleanly via the bodied trait default, with no ambiguity diagnostic.
	let case = TestCase::new(indoc! {"
        trait A {
            fn foo(self) -> i32 { 1 }
        }

        struct S {}

        impl A for S {}

        fn use_it(s: S) -> i32 {
            s.foo()
        }

        export { use_it }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"unexpected errors: {:?}",
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.severity == Severity::Error)
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_two_trait_impls_with_colliding_method_name_is_ambiguous() {
	// `S` implements both `A` and `B`, each providing a `foo` method —
	// `s.foo()` cannot pick one without disambiguation.
	let case = TestCase::new(indoc! {"
        trait A {
            fn foo(self) -> i32;
        }

        trait B {
            fn foo(self) -> i32;
        }

        struct S {}

        impl A for S {
            fn foo(self) -> i32 { 1 }
        }

        impl B for S {
            fn foo(self) -> i32 { 2 }
        }

        fn use_it(s: S) -> i32 {
            s.foo()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::AmbiguousTraitMember),
		"expected an ambiguity diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_qualified_path_expression_disambiguates_trait_method() {
	// Same setup as `test_two_trait_impls_with_colliding_method_name_is_ambiguous`
	// (`S` implements both `A` and `B`, each with a colliding `foo`), but
	// calling through `<S as A>::foo(s)` / `<S as B>::foo(s)` instead of
	// `s.foo()` — the qualified path pins down which trait's method is
	// meant, so neither call should be ambiguous.
	let case = TestCase::new(indoc! {"
        trait A {
            fn foo(self) -> i32;
        }

        trait B {
            fn foo(self) -> i32;
        }

        struct S {}

        impl A for S {
            fn foo(self) -> i32 { 1 }
        }

        impl B for S {
            fn foo(self) -> i32 { 2 }
        }

        fn use_a(s: S) -> i32 {
            <S as A>::foo(s)
        }

        fn use_b(s: S) -> i32 {
            <S as B>::foo(s)
        }

        export { use_a, use_b }
    "});
	no_errors(&case);
}

#[test]
fn test_qualified_path_type_position_assoc_type_projection() {
	// The motivating example: `<Mem::Size as Unsigned>::Signed` in a
	// generic function's return type, where `Mem::Size` is itself an
	// `AssocTypeProjection` (via `Mem: Memory`) rather than a plain type
	// param — exercises `resolve_required_trait_member_type`'s
	// `AssocTypeProjection` branch, which searches the bounds declared on
	// the associated type (`type Size: Unsigned`) rather than impls.
	let case = TestCase::new(indoc! {"
        trait Unsigned {
            type Signed;
        }
        trait Memory {
            type Size: Unsigned;
        }
        struct Mem32 {}
        impl Memory for Mem32 {
            type Size = u32;
        }
        impl Unsigned for u32 {
            type Signed = i32;
        }
        fn grow<Mem: Memory>(mem: Mem, delta: Mem::Size) -> <Mem::Size as Unsigned>::Signed {
            unreachable
        }
        fn grow_concrete(mem: Mem32, delta: u32) -> i32 {
            grow(mem, delta)
        }
        export { grow_concrete }
    "});
	no_errors(&case);
}

#[test]
fn test_qualified_path_trait_not_implemented_is_error() {
	// `Empty` never implements `Greeter` at all — `<Empty as
	// Greeter>::greet` should report the same "trait bound not satisfied"
	// diagnostic as an ordinary unsatisfied bound, not a generic
	// undeclared-item error.
	let case = TestCase::new(indoc! {"
        trait Greeter {
            fn greet(self) -> u32;
        }
        struct Empty {}
        fn use_it(e: Empty) -> u32 {
            <Empty as Greeter>::greet(e)
        }
        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound-violation diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_qualified_path_no_such_member_is_error() {
	// `Thing` does implement `Other`, but `Other` has no `greet` member —
	// distinct from the "not implemented at all" case above, and should be
	// reported with the same code the unqualified "no associated item"
	// fallback already uses.
	let case = TestCase::new(indoc! {"
        trait Other {
            fn shout(self) -> u32;
        }
        struct Thing {}
        impl Other for Thing {
            fn shout(self) -> u32 { 3 }
        }
        fn use_it(t: Thing) -> u32 {
            <Thing as Other>::greet(t)
        }
        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"expected an undeclared-identifier diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_qualified_path_type_param_not_bound_is_error() {
	// `T` is bound by `A` but not `B` — `<T as B>::foo` should report that
	// `T` doesn't satisfy `B`, exercising
	// `resolve_trait_member`/`build_required_trait_member_expression`'s
	// `Type::TypeParam` branch rather than the concrete-type one.
	let case = TestCase::new(indoc! {"
        trait A {
            fn foo(self) -> i32;
        }
        trait B {
            fn foo(self) -> i32;
        }
        fn use_it<T: A>(x: T) -> i32 {
            <T as B>::foo(x)
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound-violation diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_qualified_path_trait_not_satisfied_span_covers_bracket_only() {
	// Regression test: the "trait bound not satisfied" diagnostic for
	// `<Mem::Size as Unsigned>::Signed` used to point at `Signed` (the
	// unrelated final segment) instead of the `<Mem::Size as Unsigned>`
	// clause that's actually wrong — `Mem::Size` (i.e. `Memory::Size`)
	// never declared an `Unsigned` bound. The primary label's span must
	// cover exactly the bracketed `<...>` clause, not the trailing
	// `::Signed`.
	let source = indoc! {"
        trait Unsigned {
            type Signed;
        }
        trait Memory {
            type Size;
        }
        fn grow<Mem: Memory>(mem: Mem, delta: Mem::Size) -> <Mem::Size as Unsigned>::Signed {
            unreachable
        }
        export { }
    "};
	let case = TestCase::new(source);
	let diag = case
		.tir
		.diagnostics
		.iter()
		.find(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::TraitBoundViolation.code())
		})
		.expect("expected a trait-bound-violation diagnostic");

	let bracket_start = source.find("<Mem::Size as Unsigned>").unwrap();
	let bracket_end = bracket_start + "<Mem::Size as Unsigned>".len();

	let primary = diag
		.labels
		.iter()
		.find(|l| {
			l.style == codespan_reporting::diagnostic::LabelStyle::Primary
		})
		.expect("missing primary label");
	assert_eq!(
		primary.range,
		bracket_start..bracket_end,
		"expected the primary label to span exactly `<Mem::Size as Unsigned>`, not include `::Signed`"
	);
}

#[test]
fn test_qualified_path_grouped_form_resolves_like_unqualified_path() {
	// `<Type>::item` (no `as Trait`) — the bare bracketed-self-type form,
	// kept as its own `Grouped` AST node distinct from `QualifiedPath`
	// (which always requires a trait). Exercised in both type position (a
	// return type) and expression position (a call), and should resolve
	// exactly like the unbracketed `Type::item` would — no errors, no
	// disambiguation involved.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
            fn get(self) -> Self::Item;
        }
        struct Boxed {}
        impl Container for Boxed {
            type Item = u32;
            fn get(self) -> u32 { 42 }
        }
        fn use_it<T: Container>(x: T) -> <T>::Item {
            <T>::get(x)
        }
        export { }
    "});
	no_errors(&case);
}

#[test]
fn test_qualified_path_assoc_type_projection_recovers_type_despite_unsatisfied_bound()
 {
	// Generic regression case: `Mem::Item` never declares `Converter` in its
	// own bounds (`type Item;`, no `: Converter`), so
	// `<Mem::Item as Converter>::Output` reports a trait-bound-violation —
	// but `Converter` *does* declare an `Output` assoc type, so the return
	// type should still resolve to the `AssocTypeProjection` it would have
	// been rather than collapsing to `TypeIndex::ERROR`. Matches rustc: an
	// unsatisfied predicate doesn't erase the type it was checked against,
	// so hover/further type-checking stays useful instead of cascading into
	// unrelated `{unknown}` noise.
	let case = TestCase::new(indoc! {"
        trait Converter {
            type Output;
        }
        trait Container {
            type Item;
        }
        fn f<Mem: Container>(mem: Mem, delta: Mem::Item) -> <Mem::Item as Converter>::Output {
            unreachable
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound-violation diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("f"))
		.expect("function 'f' not found");
	let result_ty = func.result.as_ref().expect("expected a return type").inner;

	let converter_trait = TraitIndex::new(
		case.tir
			.items
			.traits
			.iter()
			.position(|t| {
				case.graph.interner.resolve(t.name.inner) == Some("Converter")
			})
			.expect("trait 'Converter' not found") as u32,
	);
	let output_sym = case.graph.interner.get("Output").unwrap();

	match case.tir.types.resolve(result_ty) {
		Type::AssocTypeProjection {
			trait_index,
			assoc_name,
			..
		} => {
			assert_eq!(
				*trait_index, converter_trait,
				"recovered type should still be keyed on the named trait `Converter`"
			);
			assert_eq!(
				*assoc_name, output_sym,
				"recovered type should still name the requested assoc type `Output`"
			);
		}
		other => panic!(
			"expected the return type to recover to AssocTypeProjection despite the unsatisfied bound, got {other:?}"
		),
	}
}

#[test]
fn test_qualified_path_assoc_type_on_bound_type_param_resolves() {
	// Regression test: `<T as A>::Item` where `T` genuinely *is* bound by
	// `A` (the success path, not the recovery path exercised by the test
	// below). `resolve_trait_member`'s `TypeParam` branch returns the
	// trait's own abstract declaration entry for an assoc type — which has
	// no concrete `ty` to unwrap, unlike a real impl's entry — so this used
	// to panic (`Option::unwrap()` on `None`) instead of building the
	// `AssocTypeProjection` the abstract case actually needs.
	let case = TestCase::new(indoc! {"
        trait A {
            type Item;
        }
        fn use_it<T: A>(x: T) -> <T as A>::Item {
            unreachable
        }
        export { }
    "});
	no_errors(&case);

	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("use_it"))
		.expect("function 'use_it' not found");
	let result_ty = func.result.as_ref().expect("expected a return type").inner;
	assert!(
		matches!(
			case.tir.types.resolve(result_ty),
			Type::AssocTypeProjection { .. }
		),
		"expected the return type to resolve to AssocTypeProjection, got {:?}",
		case.tir.types.resolve(result_ty)
	);
}

#[test]
fn test_qualified_path_type_param_not_bound_recovers_type() {
	// Same recovery, but through the general (non-`AssocTypeProjection`)
	// branch: `T` is bound by `A` but not `B`, yet `B` does declare an
	// `Item` assoc type — `<T as B>::Item` should still recover that shape.
	let case = TestCase::new(indoc! {"
        trait A {
            fn foo(self) -> i32;
        }
        trait B {
            type Item;
        }
        fn use_it<T: A>(x: T) -> <T as B>::Item {
            unreachable
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound-violation diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("use_it"))
		.expect("function 'use_it' not found");
	let result_ty = func.result.as_ref().expect("expected a return type").inner;
	assert!(
		matches!(
			case.tir.types.resolve(result_ty),
			Type::AssocTypeProjection { .. }
		),
		"expected the return type to recover to AssocTypeProjection despite the unsatisfied bound, got {:?}",
		case.tir.types.resolve(result_ty)
	);
}

#[test]
fn test_qualified_path_no_such_member_does_not_recover() {
	// Contrast with the two tests above: when the named trait genuinely has
	// no member by that name (not a bound-satisfaction problem, a typo/
	// nonexistent-name problem), there's nothing sensible to recover — the
	// return type must stay `TypeIndex::ERROR`, not silently invent a type
	// for a name that was never declared anywhere.
	let case = TestCase::new(indoc! {"
        trait Other {
            fn shout(self) -> u32;
        }
        struct Thing {}
        impl Other for Thing {
            fn shout(self) -> u32 { 3 }
        }
        fn use_it(t: Thing) -> <Thing as Other>::Nope {
            unreachable
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected an undeclared-type diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("use_it"))
		.expect("function 'use_it' not found");
	let result_ty = func.result.as_ref().expect("expected a return type").inner;
	assert_eq!(
		result_ty,
		TypeIndex::ERROR,
		"a nonexistent member name has nothing to recover — return type should stay ERROR"
	);
}

#[test]
fn test_ambiguity_between_explicit_override_and_bodied_default() {
	// `A::foo` is a bodied default that `S` doesn't override; `B::foo` is
	// explicitly provided by `S`. Both are still live candidates for
	// `s.foo()` — an override in one trait doesn't remove the other trait
	// from candidacy.
	let case = TestCase::new(indoc! {"
        trait A {
            fn foo(self) -> i32 { 1 }
        }

        trait B {
            fn foo(self) -> i32;
        }

        struct S {}

        impl A for S {}

        impl B for S {
            fn foo(self) -> i32 { 2 }
        }

        fn use_it(s: S) -> i32 {
            s.foo()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::AmbiguousTraitMember),
		"expected an ambiguity diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_inherent_impl_repeated_type_param_rejects_inconsistent_receiver()
 {
	// `impl<T> Pair<T, T>` pins both fields to one shared `T` — a receiver
	// like `Pair<i32, bool>` has no consistent `T` that makes it apply.
	// `infer_type_args` alone wouldn't catch this (first-binding-wins would
	// bind `T = i32` from the first field and silently drop the conflicting
	// `bool` from the second) — `unify_impl_target` rejects it by checking
	// `infer_type_args`'s own consistency result, so the block never
	// becomes a candidate at all, and resolution falls through to the
	// ordinary "no applicable method" diagnostic — matching what real Rust
	// reports for the identical case (`E0599: no method named foo found`,
	// verified against rustc directly).
	let case = TestCase::new(indoc! {"
        struct Pair<A, B> { a: A, b: B }

        impl<T> Pair<T, T> {
            fn foo(self) {}
        }

        fn use_it(p: Pair<i32, bool>) {
            p.foo()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::MethodNotFound),
		"expected a method-not-found diagnostic (no consistent `T` makes \
		 `Pair<T, T>` apply to `Pair<i32, bool>`), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_overlapping_generic_inherent_impls_cannot_share_a_member_name() {
	// `impl<T> Pair<T, T>` is a strict subset of `impl<A, B> Pair<A, B>` —
	// `Pair<i32, i32>` is claimed by both — so a `foo` in each is a conflict
	// between the *declarations*, whatever any particular call site does with
	// it. Matches rustc, which rejects this exact pair with `E0592:
	// duplicate definitions with name `foo`` (verified against rustc
	// directly).
	//
	// This used to be accepted because the conflict was only ever arbitrated
	// per call site, and here the receiver (`Pair<i32, bool>`) has no
	// consistent `T`, so only one block applied. What that really tested —
	// `unify_impl_target` rejecting `Pair<T, T>` for `Pair<i32, bool>`
	// instead of letting it become a bogus candidate — is covered on its own
	// by `test_generic_inherent_impl_repeated_type_param_rejects_inconsistent_receiver`
	// above, which needs no second block to say it.
	let case = TestCase::new(indoc! {"
        struct Pair<A, B> { a: A, b: B }

        impl<T> Pair<T, T> {
            fn foo(self) {}
        }

        impl<A, B> Pair<A, B> {
            fn foo(self) -> i32 { 1 }
        }

        fn use_it(p: Pair<i32, bool>) -> i32 {
            p.foo()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected the two overlapping blocks to conflict on `foo`, got: {:?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_disjoint_generic_inherent_impls_may_share_a_member_name() {
	// The counterpart: `Box<i32>` and `Box<bool>` share the `(Struct(Box),
	// "get")` dispatch bucket but overlap on no receiver at all, so both may
	// provide `get`. This is why the check unifies the targets rather than
	// rejecting on the shared bucket alone.
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        impl Box<i32> {
            pub fn get(self) -> i32 { self.v }
        }

        impl Box<bool> {
            pub fn get(self) -> bool { self.v }
        }

        fn use_it(a: Box<i32>, b: Box<bool>) -> i32 {
            if b.get() { a.get() } else { 0 }
        }

        export { use_it }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_inherent_impls_in_separate_blocks_conflict_without_a_call_site() {
	// The conflict is in the declarations, so it is reported whether or not
	// anything calls `turns`. Nothing here does — previously that meant
	// nothing checked, since only `resolve_impl_member` ever compared
	// candidates and it runs per call site.
	let case = TestCase::new(indoc! {"
        struct Deg { value: i32 }

        impl Deg {
            pub fn turns(self) -> i32 { self.value }
        }

        impl Deg {
            pub fn turns(self) -> bool { true }
        }

        fn use_it(d: Deg) -> i32 { d.value }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"{:?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_generic_inherent_impl_blanket_conflicts_with_a_concrete_block() {
	// `impl<T> Box<T>` claims `Box<i32>` too. Unification is tried in both
	// directions precisely for this: only the generic side has holes, so
	// whichever block registers second has to be able to act as the pattern.
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        impl<T> Box<T> {
            pub fn get(self) -> T { self.v }
        }

        impl Box<i32> {
            pub fn get(self) -> i32 { self.v }
        }

        fn use_it(a: Box<i32>) -> i32 { a.v }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"{:?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_generic_inherent_impl_bound_violation_rejects_receiver() {
	// `impl<T: Numeric> Box<T>` requires `T` to implement `Numeric` — a
	// receiver like `Box<NotNumeric>` doesn't satisfy that bound, so `get`
	// shouldn't resolve through this impl at all. Unlike the repeated-param
	// case, nothing downstream re-checks this (only `.bounds.typeset` is
	// re-validated post-call, not `.bounds.traits`), so today this compiles
	// with no diagnostic whatsoever.
	let case = TestCase::new(indoc! {"
        trait Numeric {}

        struct Box<T> { value: T }

        impl<T: Numeric> Box<T> {
            fn get(self) -> T { self.value }
        }

        struct NotNumeric {}

        fn use_it(b: Box<NotNumeric>) -> NotNumeric {
            b.get()
        }

        export { use_it }
    "});
	// `has_error_code` alone isn't enough here: unrelated stdlib-resolution
	// noise (`Allocator::alloc`'s `self.reserve(..)`, tracked separately)
	// also carries `MethodNotFound`, so this checks the message names `get`
	// specifically rather than matching that noise by accident.
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::MethodNotFound.code())
			&& d.message.contains("get")),
		"expected a method-not-found diagnostic naming `get` (resolving it \
		 on `Box<NotNumeric>`, which doesn't implement `Numeric`), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_impl_trait_function_origin_is_trait_impl() {
	let case = TestCase::new(indoc! {"
        trait Greet {
            fn hello(self);
        }

        struct Foo {}

        impl Greet for Foo {
            fn hello(self) {
                unreachable
            }
        }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error)
	);

	let hello_sym = case
		.graph
		.interner
		.get("hello")
		.expect("symbol `hello` not interned");
	let ti = case
		.tir
		.items
		.trait_impls
		.iter()
		.find(|ti| ti.members.contains_key(&hello_sym))
		.expect("no TraitImpl has 'hello' method");

	let func_index = match ti.members.get(&hello_sym) {
		Some(ImplEntry::Method(fi)) => *fi,
		other => panic!("expected Method entry, got {:?}", other),
	};
	assert!(
		matches!(
			case.tir.items.functions[usize::from(func_index)].type_param_parent,
			Some(TypeParamOwner::TraitImpl(_))
		),
		"method inside trait impl block should point `type_param_parent` at its \
		 `TraitImpl` — not to inherit type params (trait impls have none yet), \
		 but so `Self` inside the body can be traced back to its container"
	);
}

/// Regression test: a method declared with its own generic type param
/// (`fn write<Mem: Memory>(...)`, distinct from any impl-level type param)
/// previously failed to resolve that param when the method lived inside a
/// `impl Trait for Type { .. }` block — `AstNodeRef::TraitImplFunction`
/// hardcoded the new `Function`'s own `type_params` to empty and skipped
/// `resolve_type_param_bounds` entirely, unlike the exactly analogous
/// `InherentImplFunction`/`TraitFunction` arms, which both do this
/// correctly. The same signature written directly on the trait (`Hasher`'s
/// own `write`) never had this bug — only the impl providing it did.
#[test]
fn test_trait_impl_method_with_own_generic_type_param_resolves() {
	let case = TestCase::new(indoc! {"
        trait Hasher {
            fn write<Mem: Memory>(self: Mem::*Self, bytes: Mem::&[u8]);
        }

        struct DefaultHasher {
            value: u64,
        }

        impl Hasher for DefaultHasher {
            fn write<Mem: Memory>(self: Mem::*Self, bytes: Mem::&[u8]) {
                unreachable
            }
        }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.map(|d| &d.message)
		.collect();
	assert!(errors.is_empty(), "{:?}", errors);
}

#[test]
fn test_self_keyword_recorded_in_impl_block_self_accesses() {
	let case = TestCase::new(indoc! {"
        struct Foo {}
        impl Foo {
            fn make() -> Self {
                Self::{}
            }
            fn other() -> Self {
                Self::make()
            }
        }
        export {}
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.all(|d| d.severity != Severity::Error),
		"unexpected errors: {:?}",
		case.tir.diagnostics
	);
	// `impl_block_list` also holds stdlib's own inherent impls (e.g. `impl
	// char { .. }`), so find our block by membership rather than assuming
	// an index.
	let make_sym = case
		.graph
		.interner
		.get("make")
		.expect("symbol `make` not interned");
	let block = case
		.tir
		.items
		.inherent_impls
		.iter()
		.find(|b| b.members.contains_key(&make_sym))
		.expect("no ImplBlock has a 'make' member");
	// `Self` appears four times: `-> Self` on both signatures, `Self::{}`
	// in `make`'s body, and `Self::make()` in `other`'s body.
	assert_eq!(block.self_accesses.len(), 4);
}

#[test]
fn test_self_keyword_recorded_in_trait_impl_self_accesses() {
	let case = TestCase::new(indoc! {"
        trait Greet {
            fn make() -> Self;
            fn other() -> Self;
        }
        #[tag = \"target\"]
        struct Foo {}
        impl Greet for Foo {
            fn make() -> Self {
                Self::{}
            }
            fn other() -> Self {
                Self::make()
            }
        }
        export {}
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.all(|d| d.severity != Severity::Error),
		"unexpected errors: {:?}",
		case.tir.diagnostics
	);
	// `std` registers its own trait impls first, so find the one that
	// targets this test's own (tagged) `Foo` struct rather than assuming index 0.
	let target_tag = case.graph.interner.get("target").unwrap();
	let foo_def_id = *case.tir.items.tagged_items.get(&target_tag).unwrap();
	let foo_self_type = case.tir.items.structs
		[usize::from(case.tir.items.struct_index(foo_def_id).unwrap())]
	.self_type;
	let trait_impl = case
		.tir
		.items
		.trait_impls
		.iter()
		.find(|i| i.target.inner == foo_self_type)
		.expect("no TraitImpl targets 'Foo'");
	assert_eq!(trait_impl.self_accesses.len(), 4);
}

#[test]
fn test_self_keyword_recorded_in_trait_impl_assoc_type_self_accesses() {
	// Regression test: `TraitImplAssocType` built its `GenericScope` with
	// `owner: TypeParamOwner::Trait(trait_index)` instead of
	// `TypeParamOwner::TraitImpl(trait_impl_index)` — harmless for type
	// resolution itself (`Self` resolves off `scope.self_type`, which was
	// already correct), but `record_self_keyword_access` only recognizes
	// `ImplBlock`/`TraitImpl` owners, so the access was silently dropped
	// instead of landing in `self_accesses`.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Elem;
        }
        #[tag = \"target\"]
        struct Foo {}
        impl Container for Foo {
            type Elem = Self;
        }
        export {}
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.all(|d| d.severity != Severity::Error),
		"unexpected errors: {:?}",
		case.tir.diagnostics
	);
	let target_tag = case.graph.interner.get("target").unwrap();
	let foo_def_id = *case.tir.items.tagged_items.get(&target_tag).unwrap();
	let foo_self_type = case.tir.items.structs
		[usize::from(case.tir.items.struct_index(foo_def_id).unwrap())]
	.self_type;
	let trait_impl = case
		.tir
		.items
		.trait_impls
		.iter()
		.find(|i| i.target.inner == foo_self_type)
		.expect("no TraitImpl targets 'Foo'");
	assert_eq!(trait_impl.self_accesses.len(), 1);
}

// ── trait duplicate definition ────────────────────────────────────────────────

#[test]
fn test_duplicate_trait_definition_is_error() {
	let case = TestCase::new(indoc! {"
        trait Foo { }
        trait Foo { }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected duplicate definition error for two traits with same name, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_local_trait_silently_shadows_wildcard_import() {
	// Defining a trait with the same name as one from `use std::*` is allowed —
	// local definitions always win over wildcard imports without a diagnostic.
	let case = TestCase::new(indoc! {"
        trait PointerSize { }
        export { }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"local trait shadowing wildcard import should not produce a duplicate error"
	);
}

// ── privacy / visibility ──────────────────────────────────────────────────────

#[test]
fn test_private_module_item_not_visible_via_wildcard_import() {
	// A non-`pub` item stays invisible through `use foo::*;` — wildcard
	// imports only ever bring in a module's public surface.
	let case = TestCase::new(indoc! {"
        mod foo {
            const SECRET: i32 = 1;
        }
        use foo::*;
        fn f() -> i32 {
            SECRET
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"expected 'SECRET' to be invisible (undeclared) through the wildcard import, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_pub_module_item_visible_via_wildcard_import() {
	let case = TestCase::new(indoc! {"
        mod foo {
            pub const PUBLIC: i32 = 1;
        }
        use foo::*;
        fn f() -> i32 {
            PUBLIC
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics for a pub item reached via wildcard import: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_private_module_item_not_visible_via_qualified_path() {
	// Same rule, but named explicitly as `foo::SECRET` — bypasses the
	// wildcard-import path entirely and exercises the explicit-qualified-path
	// resolver instead, which reports the dedicated "is private" diagnostic.
	let case = TestCase::new(indoc! {"
        mod foo {
            const SECRET: i32 = 1;
        }
        fn f() -> i32 {
            foo::SECRET
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::PrivateItem),
		"expected a private-item diagnostic for 'foo::SECRET', got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_pub_module_item_visible_via_qualified_path() {
	let case = TestCase::new(indoc! {"
        mod foo {
            pub const PUBLIC: i32 = 1;
        }
        fn f() -> i32 {
            foo::PUBLIC
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics for a pub item reached via qualified path: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_private_item_visible_to_descendant_module_not_to_ancestor() {
	// Rust-style default visibility: a non-`pub` item is visible to its own
	// declaring module and every descendant module, but not to an ancestor —
	// even though the ancestor is exactly where the child module's own name
	// is declared and reachable from.
	let case = TestCase::new(indoc! {"
        mod foo {
            const SECRET: i32 = 1;

            mod bar {
                pub fn uses_secret() -> i32 {
                    foo::SECRET
                }
            }
        }

        fn ancestor_access() -> i32 {
            foo::SECRET
        }

        export { }
    "});
	let private_item_errors = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref() == Some(DiagnosticCode::PrivateItem.code())
		})
		.count();
	assert_eq!(
		private_item_errors,
		1,
		"expected exactly one private-item diagnostic (the root-level access), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_default_body_referencing_sibling_method_does_not_panic() {
	// Regression: ensure_signature for TraitFunction left a Pending entry in the
	// namespace. When a default method body referenced another trait method by
	// name, lookup_global_symbol returned that Pending, reaching an unreachable!()
	// in global_symbol_to_expression.
	let _case = TestCase::new(indoc! {"
        trait Counter {
            fn step() -> i32;
            fn doubled() -> i32 { step() + step() }
        }
    "});
	// Test passes as long as it does not panic.
}

#[test]
fn test_method_call_on_self_less_trait_fn_reports_not_a_method() {
	// Regression: `TraitFunction` registration always inserted `ImplEntry::Method`
	// into `traits[..].members`, even when the function's first param isn't
	// `self`. `resolve_impl_member`'s `Type::TypeParam` branch reads that map
	// directly, so calling such a function with method-call syntax on a
	// trait-bounded generic reached `build_method_call_expression`'s
	// `signature.params()[1..]` with an empty params list and panicked.
	let case = TestCase::new(indoc! {"
        trait Reserve {
            fn reserve() -> i32;
        }

        fn use_it<T: Reserve>(x: T) -> i32 {
            x.reserve()
        }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"expected a 'not a method' style error, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── trait conformance check
// ───────────────────────────────────────────────────

#[test]
fn test_trait_conformance_missing_fn() {
	// impl block omits the required abstract method → E1033
	let case = TestCase::new(indoc! {"
        trait Drawable {
            fn draw(self);
        }

        struct Point {
            x: i32,
            y: i32,
        }

        impl Drawable for Point {}
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::IncompleteTraitImpl.code())),
		"expected E1033 for missing trait item, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| (d.code.as_deref(), &d.message))
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_impl_item_not_declared_by_trait() {
	// The mirror of the missing-item check: an impl may only provide what its
	// trait declares. Neither extra item is reachable — a trait impl's members
	// are looked up through the trait — so both are errors, not silent
	// additions to the type.
	let case = TestCase::new(indoc! {"
        trait Drawable {
            fn draw(self);
        }

        struct Point { x: i32 }

        impl Drawable for Point {
            fn draw(self) {}

            fn hide(self) {}

            const SCALE: i32 = 2;
        }
    "});
	assert_eq!(
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.code.as_deref()
				== Some(DiagnosticCode::NotATraitMember.code()))
			.count(),
		2,
		"expected `hide` and `SCALE` to be rejected: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| (d.code.as_deref(), &d.message))
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_impl_duplicate_member_keeps_the_first() {
	// The second `turns` is reported rather than silently taking the name
	// over. `use_it` type-checks against the first one's `i32`, which is what
	// proves the survivor: had the later `bool` won, the call would not.
	let case = TestCase::new(indoc! {"
        trait Angle {
            fn turns(self) -> i32;
        }

        struct Deg { value: i32 }

        impl Angle for Deg {
            fn turns(self) -> i32 { self.value }

            fn turns(self) -> bool { true }
        }

        fn use_it(d: Deg) -> i32 { d.turns() }

        export { use_it }
    "});
	let errors = error_messages(&case.tir);
	assert_eq!(
		errors.len(),
		1,
		"the duplicate alone should be reported: {errors:#?}"
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"{errors:#?}"
	);
}

#[test]
fn test_inherent_impl_duplicate_member_keeps_the_first() {
	// Same first-wins rule as the trait impl case. `use_it` type-checks
	// against the first `turns`'s `i32`, which is what proves the survivor.
	// The duplicate const was previously not checked at all — only methods
	// were — so it stands alongside as its own case.
	let case = TestCase::new(indoc! {"
        struct Deg { value: i32 }

        impl Deg {
            pub fn turns(self) -> i32 { self.value }

            pub fn turns(self) -> bool { true }

            pub const SCALE: i32 = 1;

            pub const SCALE: bool = true;
        }

        fn use_it(d: Deg) -> i32 { d.turns() }

        export { use_it }
    "});
	let errors = error_messages(&case.tir);
	assert_eq!(
		errors.len(),
		2,
		"one per duplicated name, and nothing at the call site: {errors:#?}"
	);
	assert!(
		errors
			.iter()
			.all(|message| message.contains("defined multiple times")),
		"{errors:#?}"
	);
}

/// A wrong-kind item must not stand in for the requirement it shadows the
/// name of — the missing-item check compares kinds, not just names, so both
/// halves of the mistake are reported.
#[test]
fn test_trait_impl_item_of_the_wrong_kind_does_not_satisfy_the_requirement() {
	let case = TestCase::new(indoc! {"
        trait Angle {
            fn turns(self) -> i32;
        }

        struct Deg { value: i32 }

        impl Angle for Deg {
            const turns: i32 = 0;
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IncompleteTraitImpl),
		"{:?}",
		error_messages(&case.tir)
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitImplItemKindMismatch),
		"{:?}",
		error_messages(&case.tir)
	);
}

/// A method or an associated function differ only in whether a receiver is
/// declared, which is a question about a signature — not about whether the
/// impl is providing the member the trait asked for.
#[test]
fn test_trait_impl_may_drop_the_receiver_without_a_membership_error() {
	let case = TestCase::new(indoc! {"
        trait Drawable {
            fn draw(self);
        }

        struct Point { x: i32 }

        impl Drawable for Point {
            fn draw() {}
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitImplItemKindMismatch),
		"{:?}",
		error_messages(&case.tir),
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IncompleteTraitImpl),
		"{:?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_trait_impl_method_return_type_mismatch_is_error() {
	// The exact case from the original TODO this feature replaces (E0053):
	// trait declares `-> i32`, impl omits a return type entirely (implicit
	// unit).
	let case = TestCase::new(indoc! {"
        trait T {
            fn foo(b: i32, d: i32, o: i32) -> i32;
        }
        struct X {}
        impl T for X {
            fn foo(b: i32, d: i32, o: i32) {}
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitImplSignatureMismatch),
		"{:?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_trait_impl_method_param_type_mismatch_is_error() {
	let case = TestCase::new(indoc! {"
        trait T {
            fn foo(x: i32);
        }
        struct X {}
        impl T for X {
            fn foo(x: bool) {}
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitImplSignatureMismatch),
		"{:?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_trait_impl_assoc_const_type_mismatch_is_error() {
	let case = TestCase::new(indoc! {"
        trait T {
            const N: i32;
        }
        struct X {}
        impl T for X {
            const N: bool = true;
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitImplConstTypeMismatch),
		"{:?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_trait_impl_method_matching_signature_no_error() {
	let case = TestCase::new(indoc! {"
        trait T {
            fn foo(x: i32, y: bool) -> i32;
        }
        struct X {}
        impl T for X {
            fn foo(x: i32, y: bool) -> i32 { x }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_trait_impl_method_own_generic_param_alpha_equivalent_no_error() {
	// The trait method's own `T` and the impl method's own `U` are matched
	// by relative position, not by name — this must not false-positive as
	// a `TypeParam` mismatch.
	let case = TestCase::new(indoc! {"
        trait Container {
            fn wrap<T>(self, value: T) -> T;
        }
        struct X {}
        impl Container for X {
            fn wrap<U>(self, value: U) -> U { value }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_trait_impl_method_self_type_projection_matching_no_error() {
	// Regression guard: `Self::Elem` on the trait side must resolve through
	// `find_trait_impl` down to the exact same concrete leaf the impl
	// writes directly (`u32`), even though the two sides end up under
	// different `Frame`s by the time they're compared — frame identity
	// must not gate the fast-path equality check for an already-concrete
	// leaf (this exact shape broke the stdlib's `Memory::PAGE_SIZE` during
	// development).
	let case = TestCase::new(indoc! {"
        trait Bound {}
        impl Bound for u32 {}
        trait Container {
            type Elem: Bound;
            fn first(self) -> Self::Elem;
        }
        struct X {}
        impl Container for X {
            type Elem = u32;
            fn first(self) -> u32 { 0 }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_nested_assoc_type_projection_mismatch_is_detected() {
	// `Self::Mid::Out` — the outer projection's base (`Self::Mid`) is itself
	// a projection, not a bare `TypeParam`. `X`'s `Mid = M` and `M`'s
	// `Out = i32`, so `Self::Mid::Out` normalizes to `i32`, making the
	// impl's `bool` return type a genuine signature mismatch. `resolve_head`
	// has to resolve the nested base recursively before the outer step, so
	// the comparison must not degrade to a silent `Indeterminate`.
	let case = TestCase::new(indoc! {"
        trait Inner { type Out; }

        trait Outer {
            type Mid: Inner;
            fn f(self) -> Self::Mid::Out;
        }

        struct M {}
        impl Inner for M { type Out = i32; }

        struct X {}
        impl Outer for X {
            type Mid = M;
            fn f(self) -> bool { true }
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitImplSignatureMismatch),
		"expected a signature-mismatch diagnostic for `f`'s return type \
		 (Self::Mid::Out normalizes to i32, impl returns bool), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_nested_assoc_type_projection_match_is_accepted() {
	// Same shape as the mismatch case above, but the impl's return type
	// genuinely does normalize to what the trait requires — the companion
	// case the comparator must *accept*, not just correctly reject.
	let case = TestCase::new(indoc! {"
        trait Inner { type Out; }

        trait Outer {
            type Mid: Inner;
            fn f(self) -> Self::Mid::Out;
        }

        struct M {}
        impl Inner for M { type Out = i32; }

        struct X {}
        impl Outer for X {
            type Mid = M;
            fn f(self) -> i32 { 0 }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_impl_side_projection_normalizes_against_concrete_trait_return_type() {
	// The trait returns a concrete `i32`; the impl expresses the same value
	// through its own method generic's binding (`V::Out` where
	// `V: Inner where { Out = i32 }`). Both sides run through `resolve_head`
	// symmetrically, so `found`'s `V::Out` normalizes to `i32` too — no
	// mismatch.
	let case = TestCase::new(indoc! {"
        trait Inner { type Out; }
        trait T {
            fn f<U: Inner where { Out = i32 }>(u: U) -> i32;
        }
        struct X {}
        impl T for X {
            fn f<V: Inner where { Out = i32 }>(v: V) -> V::Out { unreachable }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_recursive_same_impl_nonidentity_binding_is_detected() {
	// `Self::Next::Value` normalizes through `impl<T> C for Wrap<T>` twice:
	// once for `Self::Next` (identity binding, `T` -> `T`), then once more
	// for the outer `::Value` against `Next`'s hardcoded `Wrap<i32>` (a
	// *non-identity* binding, `T` -> `i32`). Both land on the same interned
	// `(T,)`, but the trait side's is under an env where `T` means `i32`
	// while the impl's own `fn f(self) -> (T,)` is under the root env where
	// `T` is the impl's free parameter. `compare`'s fast path must reject
	// them as equal — index match, env mismatch — and let structural
	// comparison find that `(i32,)` != `(T,)`.
	let case = TestCase::new(indoc! {"
        trait C {
            type Next: C;
            type Value;
            fn f(self) -> Self::Next::Value;
        }

        struct Wrap<T> {}

        impl<T> C for Wrap<T> {
            type Next = Wrap<i32>;
            type Value = (T,);

            fn f(self) -> (T,) {
                unreachable
            }
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitImplSignatureMismatch),
		"expected a signature-mismatch diagnostic for `f`'s return type \
		 (Self::Next::Value normalizes to (i32,) via the impl's own \
		 hardcoded Next, but the impl declares (T,) for a general T), \
		 got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_error_in_intermediate_resolution_does_not_cascade() {
	// `Out`'s declared value (`MissingType`) is undeclared, so it is
	// `TypeIndex::ERROR` from Phase 2, with an `E1021` already reported.
	// When `resolve_head` hits that `ERROR` partway through normalizing the
	// trait's `Self::Out`, the comparison must yield `Indeterminate` — not
	// fall through to `compare_structural` and stack a spurious `E1080`
	// signature mismatch on top of the error that already explains it.
	let case = TestCase::new(indoc! {"
        trait T {
            type Out;
            fn f(self) -> Self::Out;
        }
        struct X {}
        impl T for X {
            type Out = MissingType;
            fn f(self) -> i32 { 0 }
        }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::TraitImplSignatureMismatch),
		"an undeclared assoc-type value should not cascade into a \
		 spurious signature-mismatch diagnostic on top of the \
		 'undeclared type' error that already explains it, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_expected_typeparam_reduces_against_found_projection() {
	// The trait returns the bare method generic `A`; the impl returns
	// `D::Out`, which normalizes to `C` via `D`'s own `where { Out = C }`
	// binding, and `C` is alpha-equivalent to `A` (same position among each
	// function's own generics). Both sides go through `resolve_head`
	// symmetrically, so `found`'s projection is normalized before the
	// positional check — no mismatch.
	let case = TestCase::new(indoc! {"
        trait Inner { type Out; }
        trait T {
            fn f<A, B: Inner where { Out = A }>(b: B) -> A;
        }
        struct X {}
        impl T for X {
            fn f<C, D: Inner where { Out = C }>(d: D) -> D::Out {
                unreachable
            }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_found_side_nested_projection_normalizes_via_find_trait_impl() {
	// The impl returns `B::Mid::Out`. `B::Mid` becomes `M` via `B`'s own
	// `where { Mid = M }` binding, then `M::Out` is `i32` via `impl Inner
	// for M`. That second step needs `find_trait_impl` on a base that only
	// became concrete through a binding local to this signature, so the
	// impl side of the comparison has to run the full `resolve_head` /
	// `project` path, not just a bound lookup. It normalizes to `i32`,
	// matching the trait's declared return type.
	let case = TestCase::new(indoc! {"
        trait Inner { type Out; }
        trait Outer { type Mid: Inner; }
        struct M {}
        impl Inner for M { type Out = i32; }

        trait T {
            fn f<A: Outer where { Mid = M }>(a: A) -> i32;
        }
        struct X {}
        impl T for X {
            fn f<B: Outer where { Mid = M }>(b: B) -> B::Mid::Out {
                unreachable
            }
        }
    "});
	no_errors(&case);
}

/// A self-referential associated-type value (`type Value = Self::Value`) in a
/// generic trait impl whose method returns `Self::Value`. The comparator's
/// `resolve_head` pushes a `TypeEnv::Impl` per `find_trait_impl` step, so a
/// real projection cycle here would grow the arena without bound.
///
/// It can't: `type Value = Self::Value` fails to resolve during Phase 2
/// (`E1021`), so its stored value is `TypeIndex::ERROR`, and `resolve_head`
/// bails to `Indeterminate` before it can loop. This locks in "terminates,
/// and doesn't stack a `TraitImplSignatureMismatch` on top of the `E1021`."
#[test]
fn test_self_referential_assoc_type_value_does_not_hang_or_cascade() {
	let case = TestCase::new(indoc! {"
        trait C {
            type Value;
            fn f(self) -> Self::Value;
        }
        struct Wrap<T> {}
        impl<T> C for Wrap<T> {
            type Value = Self::Value;
            fn f(self) -> i32 { unreachable }
        }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::TraitImplSignatureMismatch),
		"the unresolvable self-referential assoc-type value should surface \
		 as its own error, not cascade into a signature mismatch, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Satisfying a trait requirement is itself the "use" — the same exemption a
/// trait impl's methods already had, which a const could not read off its
/// `ItemParent` while that named the target type rather than the impl.
#[test]
fn test_trait_impl_const_is_not_reported_unused() {
	let case = TestCase::new(indoc! {"
        trait Scaled {
            const SCALE: i32;
        }

        struct Point { x: i32 }

        impl Scaled for Point {
            const SCALE: i32 = 2;
        }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref()
				== Some(DiagnosticCode::UnusedItem.code())),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| (d.code.as_deref(), &d.message))
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_conformance_missing_const() {
	// impl block omits a required associated const → E1033
	let case = TestCase::new(indoc! {"
        trait Sized {
            const SIZE: u32;
        }

        struct Foo {}

        impl Sized for Foo {}
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::IncompleteTraitImpl.code())),
		"expected E1033 for missing const, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| (d.code.as_deref(), &d.message))
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_conformance_default_fn_not_required() {
	// Trait methods with a default body are optional to override — no E1033
	let case = TestCase::new(indoc! {"
        trait Greet {
            fn hello(self) {
                unreachable
            }
        }

        struct Bar {}

        impl Greet for Bar {}
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"unexpected errors: {:?}",
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.severity == Severity::Error)
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── supertrait bounds
// ─────────────────────────────────────────────────────────

#[test]
fn test_supertrait_resolved() {
	// `Drawable: Sized` — the TIR Trait should carry Sized in its supertraits
	let case = TestCase::new(indoc! {"
        trait Sized {
            const SIZE: u32;
        }

        trait Drawable: Sized {
            fn draw(self);
        }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"unexpected errors: {:?}",
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.severity == Severity::Error)
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	let drawable_idx = TraitIndex::new(
		case.tir
			.items
			.traits
			.iter()
			.position(|t| {
				case.graph.interner.resolve(t.name.inner) == Some("Drawable")
			})
			.expect("Drawable not found") as u32,
	);
	let sized_idx = TraitIndex::new(
		case.tir
			.items
			.traits
			.iter()
			.position(|t| {
				case.graph.interner.resolve(t.name.inner) == Some("Sized")
			})
			.expect("Sized not found") as u32,
	);

	assert_eq!(
		case.tir.items.traits[usize::from(drawable_idx)]
			.bounds
			.traits
			.iter()
			.map(|trait_bound| trait_bound.trait_index)
			.collect::<Vec<_>>(),
		vec![sized_idx],
		"Drawable should list Sized as a supertrait"
	);
}

#[test]
fn test_supertrait_missing_impl_errors() {
	// impl Drawable for Point without impl Sized for Point → E1034
	let case = TestCase::new(indoc! {"
        trait Sized {
            const SIZE: u32;
        }

        trait Drawable: Sized {
            fn draw(self);
        }

        struct Point {
            x: i32,
            y: i32,
        }

        impl Drawable for Point {
            fn draw(self) {
                unreachable
            }
        }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnsatisfiedTraitBound.code())),
		"expected E1034 for missing supertrait impl, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| (d.code.as_deref(), &d.message))
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_supertrait_satisfied_impl_no_errors() {
	// Both Sized and Drawable implemented for Point — no E1034
	let case = TestCase::new(indoc! {"
        trait Sized {
            const SIZE: u32;
        }

        trait Drawable: Sized {
            fn draw(self);
        }

        struct Point {
            x: i32,
            y: i32,
        }

        impl Sized for Point {
            const SIZE: u32 = 8
        }

        impl Drawable for Point {
            fn draw(self) {
                unreachable
            }
        }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"unexpected errors: {:?}",
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.severity == Severity::Error)
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── demand-driven forward reference resolution
// ─────────────────────────────────────────────

#[test]
fn test_forward_ref_resolves_on_demand() {
	// The query system resolves trait forward-references on demand. Using a trait
	// name directly as a type is now invalid (traits are bounds, not types), but
	// the resolution must still find the trait — producing ExpectedTrait (E1031),
	// NOT UndeclaredType (E1021). E1021 would mean the forward reference was
	// never resolved at all.
	let case = TestCase::new(indoc! {"
        fn uses_memory32(mem: Memory32, delta: u32) -> u32 {
            mem.grow(delta)
        }

        trait Memory32 {
            fn grow(self, delta: u32) -> u32;
        }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UndeclaredType.code())),
		"E1021 should not be emitted: the query system resolves traits on demand"
	);
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref()
				== Some(DiagnosticCode::ExpectedBound.code())),
		"E1031 should be emitted: traits cannot be used directly as types"
	);
}

// ── cyclic type dependency tests
// ──────────────────────────────────────────────

#[test]
fn test_struct_direct_cycle_is_error() {
	// A struct that contains itself by value has infinite size — E1032.
	let case = TestCase::new(indoc! {"
        struct A {
            field: A
        }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::CyclicTypeDependency.code())),
		"expected E1032 for direct self-referential struct"
	);
}

#[test]
fn test_struct_mutual_cycle_is_error() {
	// A <-> B by value is an infinite-size cycle — E1032.
	let case = TestCase::new(indoc! {"
        struct A {
            b: B
        }
        struct B {
            a: A
        }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::CyclicTypeDependency.code())),
		"expected E1032 for mutually recursive structs"
	);
}

#[test]
fn test_struct_three_way_cycle_is_error() {
	// A -> B -> C -> A cycle — E1032.
	let case = TestCase::new(indoc! {"
        struct A { b: B }
        struct B { c: C }
        struct C { a: A }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::CyclicTypeDependency.code())),
		"expected E1032 for three-way struct cycle"
	);
}

#[test]
fn test_cyclic_type_dependency_names_every_item_in_the_chain() {
	// Which reference closes a cycle is an accident of parse order, so the
	// span alone doesn't identify the loop. `sig_stack` supplies the rest:
	// every participant gets a label, and the note spells out the order.
	let case = TestCase::new(indoc! {"
        type A = B;
        type B = C;
        type C = A;
        fn f(x: A) -> i32 { 1 }
    "});
	let diagnostic = case
		.tir
		.diagnostics
		.iter()
		.find(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::CyclicTypeDependency.code())
		})
		.expect("expected E1032 for a three-way type alias cycle");
	assert!(
		diagnostic
			.notes
			.iter()
			.any(|note| note == "the cycle is `A` -> `B` -> `C` -> `A`"),
		"expected the full chain in a note, got: {:?}",
		diagnostic.notes
	);
	// One primary label for the reference that closed the loop, plus one
	// secondary per participant.
	assert_eq!(
		diagnostic.labels.len(),
		4,
		"expected the closing reference plus one label per item in the cycle"
	);
}

#[test]
fn test_self_referential_alias_cycle_omits_the_chain_note() {
	// A one-item cycle is already spelled out by its single label — repeating
	// it as "the cycle is `A` -> `A`" would be noise.
	let case = TestCase::new(indoc! {"
        type A = A;
        fn f(x: A) -> i32 { 1 }
    "});
	let diagnostic = case
		.tir
		.diagnostics
		.iter()
		.find(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::CyclicTypeDependency.code())
		})
		.expect("expected E1032 for a self-referential type alias");
	assert!(
		!diagnostic
			.notes
			.iter()
			.any(|note| note.starts_with("the cycle is")),
		"a single-item cycle should not get a chain note, got: {:?}",
		diagnostic.notes
	);
}

#[test]
fn test_generic_alias_cycle_is_reported_exactly_once() {
	// `GenericApplication` forces a pending signature on its own rather than
	// through `resolve_pending_global_symbol`, so it has to recognise a cycle
	// itself. Before it did, the error surfaced only because the fallback path
	// re-resolved the name as a bare path and reported it there instead.
	let case = TestCase::new(indoc! {"
        type A<T> = B<T>;
        type B<T> = A<T>;
        fn f(x: A<i32>) -> i32 { 1 }
    "});
	let cyclic: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::CyclicTypeDependency.code())
		})
		.collect();
	assert_eq!(
		cyclic.len(),
		1,
		"expected exactly one E1032 for the generic alias cycle, got: {:?}",
		cyclic.iter().map(|d| &d.message).collect::<Vec<_>>()
	);
	assert!(
		cyclic[0]
			.notes
			.iter()
			.any(|note| note == "the cycle is `A` -> `B` -> `A`"),
		"expected the chain note, got: {:?}",
		cyclic[0].notes
	);
}

#[test]
fn test_struct_forward_reference_resolves() {
	// B used as a field type before B is declared — no cycle, no diagnostic.
	let case = TestCase::new(indoc! {"
        struct A { b: B }
        struct B { val: i32 }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.map(|d| &d.message)
		.collect::<Vec<_>>();
	assert!(
		errors.is_empty(),
		"unexpected errors for valid forward reference: {:?}",
		errors
	);
}

#[test]
fn test_struct_forward_reference_reversed_order_resolves() {
	// Same as above but B declared first — both orderings must work.
	let case = TestCase::new(indoc! {"
        struct B { val: i32 }
        struct A { b: B }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.map(|d| &d.message)
		.collect::<Vec<_>>();
	assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
}

#[test]
fn test_fn_uses_struct_declared_after_is_ok() {
	// A function's parameter/return type that references a struct defined later
	// in the file must resolve cleanly — no type errors.
	let case = TestCase::new(indoc! {"
        fn f(x: Point) -> Point { x }
        struct Point { x: i32, y: i32 }
    "});
	let type_errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.code.as_deref().is_some_and(|c| c.starts_with('E')))
		.collect();
	assert!(
		type_errors.is_empty(),
		"unexpected type errors for forward-referenced struct in function: {:?}",
		type_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
	);
}

#[test]
fn test_struct_cycle_does_not_prevent_other_structs_from_resolving() {
	// Even with a cyclic struct present, independent structs should resolve fine.
	let case = TestCase::new(indoc! {"
        struct Bad { bad: Bad }
        struct Good { val: i32 }
        fn uses_good(x: Good) -> i32 { x.val }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::CyclicTypeDependency.code())),
		"expected E1032 for Bad"
	);
	// Good should still be registered; the function should compile without
	// an undeclared-type error.
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UndeclaredType.code())),
		"Good struct should still resolve despite Bad being cyclic"
	);
}

// ── Generic structs
// ───────────────────────────────────────────────────────────

#[test]
fn test_generic_struct_definition_stores_type_params() {
	let case = TestCase::new(indoc! {"
        struct Point<T> { x: T, y: T }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.severity == codespan_reporting::diagnostic::Severity::Error
		})
		.collect();
	assert!(errors.is_empty(), "{:?}", errors);
	let s = case
		.tir
		.items
		.structs
		.iter()
		.find(|s| case.graph.interner.resolve(s.name.inner) == Some("Point"))
		.expect("Point struct not found");
	assert_eq!(s.type_params.len(), 1);
}

#[test]
fn test_generic_struct_field_type_is_type_param() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { value: T }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.severity == codespan_reporting::diagnostic::Severity::Error
		})
		.collect();
	assert!(errors.is_empty(), "{:?}", errors);
	let s = case
		.tir
		.items
		.structs
		.iter()
		.find(|s| case.graph.interner.resolve(s.name.inner) == Some("Wrapper"))
		.expect("Wrapper struct not found");
	// Field `value` should have type TypeParam { param_index: 0 }.
	assert!(
		matches!(
			case.tir.types.resolve(s.fields[0].ty.inner),
			Type::TypeParam { param_index: 0, .. }
		),
		"expected TypeParam, got {:?}",
		case.tir.types.resolve(s.fields[0].ty.inner)
	);
}

#[test]
fn test_generic_struct_in_type_position_resolves() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { value: T }
        fn get(w: Wrapper<i32>) -> i32 { w.value }
        export { get }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
	insta::assert_yaml_snapshot!(case.tir);
}

#[test]
fn test_turbofish_first_segment_resolves_enclosing_type_param() {
	// Regression: `build_path_expression`'s handling of turbofish on a
	// multi-segment path's first segment (e.g. `Wrapper::<T>::make()`)
	// resolved that segment's type args with `scope: None`, discarding the
	// enclosing function's generic scope entirely. Any type param reference
	// there — not just `Self` — silently failed to resolve; this manifested
	// as either a bogus "undeclared type" or (with a struct's generic args
	// resolving to an inconsistent length) a panic in monomorphization.
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { x: T }
        impl <T> Wrapper<T> {
            pub fn make() -> i32 { 0 }
        }
        fn use_it<T>() -> i32 {
            Wrapper::<T>::make()
        }
        fn concrete() -> i32 { use_it::<i32>() }
        export { concrete }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_struct_init_with_type_args() {
	let case = TestCase::new(indoc! {"
        struct Pair<T> { pub first: T, pub second: T }
        fn make() -> Pair<i32> {
            Pair::<i32>::{ first: 1, second: 2 }
        }
        export { make }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
	insta::assert_yaml_snapshot!(case.tir);
}

#[test]
fn test_generic_struct_field_access_substitutes_type() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { value: T }
        fn get_i32(w: Wrapper<i32>) -> i32 { w.value }
        fn get_f64(w: Wrapper<f64>) -> f64 { w.value }
        export { get_i32, get_f64 }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_generic_struct_wrong_type_arg_count_is_error() {
	let case = TestCase::new(indoc! {"
        struct Point<T> { x: T, y: T }
        fn bad(p: Point<i32, f64>) -> i32 { p.x }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::TypeArgCountMismatch.code())),
		"expected E1040 for wrong type arg count"
	);
}

#[test]
fn test_generic_struct_init_wrong_type_arg_count_is_error() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { value: T }
        fn bad() -> Wrapper<i32> {
            Wrapper::<i32, f64>::{ value: 1 }
        }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::TypeArgCountMismatch.code())),
		"expected E1040 for wrong type arg count in init"
	);
}

#[test]
fn test_generic_struct_fewer_type_args_in_signature_is_error() {
	// A short type-arg list on a `Path`/`GenericApplication` is always
	// resolved via `TypeArgArity::RequireExact` (every position `resolve_type`
	// dispatches into, since there's no expression anywhere to unify a gap
	// against later) — so this is a `TypeArgCountMismatch`, reported at the
	// point of the mismatch itself, not a later "`_` isn't allowed here" check.
	let case = TestCase::new(indoc! {"
        struct Pair<T, U> { a: T, b: U }
        fn f(p: Pair<i32>) -> i32 { p.a }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for partially-applied generic struct in signature, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_generic_struct_bare_reference_in_signature_is_error() {
	// No turbofish at all is the extreme case of "fewer args than declared" —
	// still an arity mismatch, same as a partial list.
	let case = TestCase::new(indoc! {"
        struct Pair<T, U> { a: T, b: U }
        fn f(p: Pair) { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for bare generic struct reference in signature, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_impl_block_bare_generic_struct_target_is_error() {
	// `impl Pair { .. }` for a generic `Pair<T, U>` used to silently pad the
	// impl target's args with TypeIndex::INFER instead of erroring — there is
	// no expression anywhere near an impl target that could fill the gap in,
	// so this must be an immediate arity error, same as a bare reference
	// anywhere else in type-expression position.
	let case = TestCase::new(indoc! {"
        struct Pair<T, U> { a: T, b: U }
        impl Pair {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for bare generic struct target in impl block, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	// `resolve_generic_type_application` keeps the struct's shape
	// (`Pair<{error}, {error}>`) instead of collapsing to a bare
	// `TypeIndex::ERROR`, so `ImplTarget::from_type` still recognizes it as a
	// struct target and doesn't raise a second, redundant "cannot define
	// inherit `impl` for `{unknown}`" diagnostic on top of the arity one.
	assert_eq!(
		case.tir.diagnostics.len(),
		1,
		"expected only the E1040 diagnostic, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_generic_struct_fewer_type_args_infers_from_local_initializer() {
	// `local`'s annotation is still resolved via `TypeArgArity::RequireExact`
	// (it's a type-expression position — omitting args isn't allowed even
	// though there's an initializer alongside it), but explicit `_` per slot
	// satisfies the arity check and still gets filled in from the
	// initializer afterward, same as it always has.
	let case = TestCase::new(indoc! {"
        struct Pair<T, U> { a: T, b: U }
        fn f() {
            local p: Pair<_, _> = Pair::<i32, bool>::{ a: 1, b: true }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_struct_fewer_type_args_in_local_annotation_without_underscore_is_error()
 {
	// Unlike struct-init/turbofish-on-a-call (`TypeArgArity::AllowInfer`), a
	// `local` annotation is type-expression position, so omitting args
	// outright (rather than writing `_` for each) is rejected — same as any
	// other type-expression position.
	let case = TestCase::new(indoc! {"
        struct Pair<T, U> { a: T, b: U }
        fn f() {
            local p: Pair<i32> = Pair::<i32, bool>::{ a: 1, b: true }
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for partially-applied generic struct in local annotation, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_generic_struct_too_many_type_args_still_errors() {
	let case = TestCase::new(indoc! {"
        struct Pair<T, U> { a: T, b: U }
        fn f(p: Pair<i32, f64, bool>) { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for too many type args"
	);
}

// ── Type aliases
// ─────────────────────────────────────────────────────────

#[test]
fn test_type_alias_simple() {
	let case = TestCase::new(indoc! {"
        type Foo = i32;
        fn f(x: Foo) -> Foo { x }
    "});
	no_errors(&case);
	let alias = case
		.tir
		.items
		.type_aliases
		.iter()
		.find(|a| case.graph.interner.resolve(a.name.inner) == Some("Foo"))
		.expect("Foo alias not found");
	assert_eq!(alias.body, TypeIndex::I32);
}

#[test]
fn test_type_alias_to_struct_is_transparent() {
	// Field access through the alias must type-check with no special-casing.
	let case = TestCase::new(indoc! {"
        struct Bar { field: i32 }
        type Foo = Bar;
        fn f(x: Foo) -> i32 { x.field }
    "});
	no_errors(&case);
}

#[test]
fn test_type_alias_generic_rhs() {
	// The alias's RHS is itself a generic instantiation; the alias just
	// names the concrete `Wrapper<i32>` struct type.
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { data: T }
        type WrapperI32 = Wrapper<i32>;
        fn f(w: WrapperI32) -> i32 { w.data }
    "});
	no_errors(&case);
	let alias = case
		.tir
		.items
		.type_aliases
		.iter()
		.find(|a| {
			case.graph.interner.resolve(a.name.inner) == Some("WrapperI32")
		})
		.expect("WrapperI32 alias not found");
	match case.tir.types.resolve(alias.body) {
		Type::Struct { args, .. } => {
			assert_eq!(args.len(), 1);
			assert_eq!(case.tir.types.resolve(args[0]), &Type::I32);
		}
		other => panic!("expected Type::Struct template, got {:?}", other),
	}
}

#[test]
fn test_parametric_type_alias_instantiated_at_use_site() {
	// The alias itself is generic; instantiating it with args must substitute
	// through the tuple template, producing a plain concrete tuple type.
	let case = TestCase::new(indoc! {"
        type Pair<T> = (T, T);
        fn make() -> Pair<i32> {
            (1, 2)
        }
        export { make }
    "});
	no_errors(&case);
	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("make"))
		.expect("make function not found");
	let result_ty = case.tir.types.resolve(func.signature_index).clone();
	let Type::Function { signature } = result_ty else {
		panic!("expected Type::Function, got {:?}", result_ty);
	};
	match case.tir.types.resolve(signature.result()) {
		Type::Tuple { elements } => {
			assert_eq!(elements.len(), 2);
			assert_eq!(case.tir.types.resolve(elements[0]), &Type::I32);
			assert_eq!(case.tir.types.resolve(elements[1]), &Type::I32);
		}
		other => panic!("expected Type::Tuple, got {:?}", other),
	}
}

#[test]
fn test_type_alias_direct_cycle_is_error() {
	let case = TestCase::new(indoc! {"
        type A = A;
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CyclicTypeDependency),
		"expected E1032 for direct self-referential alias"
	);
}

#[test]
fn test_type_alias_mutual_cycle_is_error() {
	let case = TestCase::new(indoc! {"
        type A = B;
        type B = A;
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CyclicTypeDependency),
		"expected E1032 for mutually recursive aliases"
	);
}

#[test]
fn test_type_alias_wrong_type_arg_count_is_error() {
	let case = TestCase::new(indoc! {"
        type Pair<T> = (T, T);
        fn f(p: Pair<i32, f64>) { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for wrong type arg count on alias"
	);
}

#[test]
fn test_type_alias_fewer_type_args_in_signature_is_error() {
	// Same rule as generic structs: a short type-arg list is always an
	// immediate arity mismatch in type-expression position.
	let case = TestCase::new(indoc! {"
        type Pair<T, U> = (T, U);
        fn f(p: Pair<i32>) { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for partially-applied alias in signature, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_type_alias_fewer_type_args_infers_from_local_initializer() {
	// Explicit `_` per slot satisfies the arity check, then gets filled in
	// from the initializer, same as for a generic struct.
	let case = TestCase::new(indoc! {"
        type Pair<T, U> = (T, U);
        fn f() {
            local p: Pair<_, _> = (1, true)
        }
    "});
	no_errors(&case);
}

#[test]
fn test_type_alias_fewer_type_args_in_local_annotation_without_underscore_is_error()
 {
	let case = TestCase::new(indoc! {"
        type Pair<T, U> = (T, U);
        fn f() {
            local p: Pair<i32> = (1, true)
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 for partially-applied alias in local annotation, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_type_alias_forward_reference_resolves() {
	// Foo is used before its declaration further down the file.
	let case = TestCase::new(indoc! {"
        fn f(x: Foo) -> i32 { x.field }
        struct Bar { field: i32 }
        type Foo = Bar;
    "});
	no_errors(&case);
}

// ── Generics ─────────────────────────────────────────────────────────────────

#[test]
fn test_generic_identity_resolves() {
	// identity<T>(t: T) -> T called with i32 — TIR must have no diagnostics
	// and the function must carry one TypeParamInfo named "T".
	let case = TestCase::new(indoc! {"
        pub fn identity<T>(t: T) -> T {
            t
        }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"unexpected errors (count: {})",
		errors.len()
	);
	let func = case.tir.items.functions.iter().find(|f| {
		case.graph
			.interner
			.resolve(f.name.inner)
			.map(|n| n == "identity")
			.unwrap_or(false)
	});
	let func = func.expect("function 'identity' not found in TIR");
	assert_eq!(func.type_params.len(), 1, "expected one type param");
	assert_eq!(
		case.graph.interner.resolve(func.type_params[0].name.inner),
		Some("T")
	);
	assert!(
		func.type_params[0].bounds.traits.is_empty(),
		"T should have no bounds"
	);
	insta::assert_yaml_snapshot!(case.tir);
}

#[test]
fn test_generic_call_return_type_substituted() {
	// Calling identity(42) must produce no diagnostics — the return type
	// is substituted from TypeParam{0} → i32 via the argument.
	let case = TestCase::new(indoc! {"
        pub fn identity<T>(t: T) -> T {
            t
        }
        pub fn main() -> i32 {
            identity(42)
        }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"unexpected errors (count: {})",
		errors.len()
	);
}

#[test]
fn test_generic_with_bound_resolves() {
	// fn with a trait bound — TypeParamInfo.bounds must contain the trait index.
	let case = TestCase::new(indoc! {"
        trait Scalable {
            fn scale(self, factor: i32) -> i32;
        }
        fn call_scale<T: Scalable>(t: T, n: i32) -> i32 {
            t.scale(n)
        }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"unexpected errors (count: {})",
		errors.len()
	);
	let func = case.tir.items.functions.iter().find(|f| {
		case.graph
			.interner
			.resolve(f.name.inner)
			.map(|n| n == "call_scale")
			.unwrap_or(false)
	});
	let func = func.expect("function 'call_scale' not found in TIR");
	assert_eq!(func.type_params.len(), 1);
	assert_eq!(
		func.type_params[0].bounds.traits.len(),
		1,
		"T should have one bound (Scalable)"
	);
}

#[test]
fn test_type_param_referenced_in_binding_rhs_records_access() {
	// When a type param appears as the RHS of a `where { AssocType = TypeParam }` binding,
	// that reference must be recorded in TypeParamInfo.accesses so that:
	//   (a) the "unused type param" warning is suppressed, and
	//   (b) callers relying on accesses for liveness are correct.
	//
	// `T` below is only used in the binding — not in any param type or return type —
	// so its accesses count must be exactly 1 after type-checking.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
        }
        fn wrap<T, C: Container where { Item = T }>(c: C) -> C {
            c
        }
    "});
	no_errors(&case);
	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| {
			case.graph
				.interner
				.resolve(f.name.inner)
				.map(|n| n == "wrap")
				.unwrap_or(false)
		})
		.expect("function 'wrap' not found in TIR");
	assert_eq!(func.type_params.len(), 2, "expected two type params (T, C)");
	assert_eq!(
		func.type_params[0].accesses.len(),
		1,
		"T should have exactly 1 access recorded (from the binding `Item = T`)"
	);
}

#[test]
fn test_generic_unknown_bound_is_error() {
	// A bound that names an undeclared type should produce a diagnostic.
	let case = TestCase::new(indoc! {"
        fn f<T: Nonexistent>(t: T) -> T {
            t
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected E1021 (UndeclaredType) for unknown trait bound 'Nonexistent', got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

// ── NamespaceAccess / associated type projection ────────────────────────────

fn no_errors(case: &TestCase) {
	use codespan_reporting::diagnostic::Severity;
	use codespan_reporting::term;
	use codespan_reporting::term::DisplayStyle;
	use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
	let writer = StandardStream::stderr(ColorChoice::Always);
	let config = term::Config {
		display_style: DisplayStyle::Rich,
		..term::Config::default()
	};
	for package_ in &case.graph.packages {
		let package_diagnostics = package_.diagnostics.iter().chain(
			package_
				.modules
				.iter()
				.flat_map(|m| m.ast.diagnostics.iter()),
		);
		for diagnostic in
			package_diagnostics.filter(|diagnostic| match diagnostic.severity {
				Severity::Error | Severity::Bug => true,
				_ => false,
			}) {
			term::emit_to_write_style(
				&mut writer.lock(),
				&config,
				&case.graph.files,
				diagnostic,
			)
			.unwrap();
		}
	}
	for diagnostic in case.tir.diagnostics.iter().filter(|diagnostic| {
		match diagnostic.severity {
			Severity::Error | Severity::Bug => true,
			_ => false,
		}
	}) {
		term::emit_to_write_style(
			&mut writer.lock(),
			&config,
			&case.graph.files,
			diagnostic,
		)
		.unwrap();
	}

	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"unexpected errors: {:?}",
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.severity == Severity::Error)
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

fn has_error_matching(case: &TestCase, substring: &str) {
	assert!(
		case.tir.diagnostics.iter().any(|d| {
			d.severity == Severity::Error
				&& (d.message.contains(substring)
					|| d.notes.iter().any(|n| n.contains(substring)))
		}),
		"expected an error containing {:?}; got: {:#?}",
		substring,
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_assoc_type_declared_in_trait() {
	// A trait with an associated type must register it in `members` and
	// `assoc_type_bounds`.
	let case = TestCase::new(indoc! {"
        trait Bound {}
        trait Container {
            type Elem: Bound;
        }
    "});
	no_errors(&case);

	let container_trait = case
		.tir
		.items
		.traits
		.iter()
		.find(|t| {
			case.graph.interner.resolve(t.name.inner) == Some("Container")
		})
		.expect("trait 'Container' not found");

	let elem_sym = case
		.graph
		.interner
		.get("Elem")
		.expect("symbol 'Elem' not interned");

	assert!(
		matches!(
			container_trait.entries.get(&elem_sym),
			Some(ImplEntry::AssocType(_))
		),
		"expected 'Elem' in Container::members as AssociatedType"
	);
	assert!(
		container_trait.assoc_types.contains_key(&elem_sym),
		"expected 'Elem' in Container::assoc_types"
	);
}

#[test]
fn test_assoc_type_projection_in_return_type() {
	// `fn foo<C: Container>() -> C::Elem` — the return type must resolve to
	// `AssocTypeProjection` (no error diagnostics).
	let case = TestCase::new(indoc! {"
        trait Bound {}
        trait Container {
            type Elem: Bound;
        }
        fn foo<C: Container>() -> C::Elem {
            unreachable
        }
    "});
	no_errors(&case);

	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("foo"))
		.expect("function 'foo' not found");

	let result_ty = func.result.as_ref().expect("expected a return type").inner;
	assert!(
		matches!(
			case.tir.types.resolve(result_ty),
			Type::AssocTypeProjection { .. }
		),
		"return type should be AssocTypeProjection for C::Elem, got type index {}",
		u32::from(result_ty)
	);
	assert_eq!(
		case.tir
			.formatter(
				&case.graph.interner,
				&case.graph.packages,
				case.graph.root_package,
			)
			.display_type(result_ty)
			.unwrap(),
		"C::Elem",
		"unambiguous — C is only bound by Container, which is the only bound declaring Elem — should stay unqualified"
	);
}

#[test]
fn test_assoc_type_projection_display_is_qualified_when_ambiguous() {
	// `T: A + B`, and *both* `A` and `B` declare an `Item` associated type —
	// unlike the unambiguous case above, printing `T::Item` here would be
	// genuinely ambiguous to a reader (which trait's `Item`?), so the
	// formatter must spell out `<T as A>::Item` instead, matching rustc's
	// own qualified-path printing for the same situation.
	let case = TestCase::new(indoc! {"
        trait A {
            type Item;
        }
        trait B {
            type Item;
        }
        fn foo<T: A + B>() -> <T as A>::Item {
            unreachable
        }
    "});
	no_errors(&case);

	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("foo"))
		.expect("function 'foo' not found");
	let result_ty = func.result.as_ref().expect("expected a return type").inner;

	assert_eq!(
		case.tir
			.formatter(
				&case.graph.interner,
				&case.graph.packages,
				case.graph.root_package,
			)
			.display_type(result_ty)
			.unwrap(),
		"<T as A>::Item",
		"T is bound by both A and B, both declaring Item — display must qualify which trait's Item this is"
	);
}

#[test]
fn test_assoc_type_projection_in_param_type() {
	// `fn consume<C: Container>(elem: C::Elem)` — the parameter type resolves to
	// `AssocTypeProjection` without errors.
	let case = TestCase::new(indoc! {"
        trait Bound {}
        trait Container {
            type Elem: Bound;
        }
        fn consume<C: Container>(elem: C::Elem) {
            unreachable
        }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_unknown_member_is_error() {
	// `M::Nonexistent` where `Memory` has no such associated type → diagnostic.
	let case = TestCase::new(indoc! {"
        trait Memory {
            type Size;
        }
        fn bad<M: Memory>() -> M::Nonexistent {
            unreachable
        }
    "});
	// TODO: improve to "undeclared associated type 'Nonexistent'" for better diagnostics
	has_error_matching(&case, "undeclared type");
}

#[test]
fn test_assoc_type_bare_name_suggests_self_prefix() {
	// Using the associated type name directly (e.g. `Size` instead of
	// `Self::Size`) must produce a targeted error with a `Self::` suggestion.
	let case = TestCase::new(indoc! {"
        trait Memory {
            type Size;
            fn alloc(n: Size) -> *u8;
        }
    "});
	// report_bare_assoc_type emits E1021 with message "cannot find type `Size` in
	// this scope" and a note containing the "Self::Size" suggestion.
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected E1021 (UndeclaredType) for bare associated type name, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_assoc_type_impl_registers_in_trait_impl() {
	// `impl Container for Heap { type Elem = u32; }` — the impl must store
	// a concrete type in `TraitImpl::members`.
	let case = TestCase::new(indoc! {"
        trait Bound {}
        impl Bound for u32 {}
        trait Container {
            type Elem: Bound;
        }
        struct Heap {}
        impl Container for Heap {
            type Elem = u32;
        }
    "});
	no_errors(&case);

	let ti = case
		.tir
		.items
		.trait_impls
		.iter()
		.find(|ti| {
			case.tir
				.items
				.traits
				.get(usize::from(ti.trait_index))
				.and_then(|t| case.graph.interner.resolve(t.name.inner))
				== Some("Container")
		})
		.expect("TraitImpl for Container not found");

	let elem_sym = case
		.graph
		.interner
		.get("Elem")
		.expect("symbol 'Elem' not interned");

	assert!(
		matches!(
			ti.members.get(&elem_sym),
			Some(ImplEntry::AssocType(idx))
				if case.tir.items.assoc_type_impls[usize::from(*idx)].ty.unwrap().inner == TypeIndex::U32
		),
		"expected 'Elem' → u32 in TraitImpl::members"
	);
}

#[test]
fn test_self_assoc_type_projection_in_inherent_impl_records_access() {
	// Regression test: `Self::Elem` inside a plain (non-trait) `impl Heap { .. }`
	// block resolves `Self` to the concrete `Type::Struct` for `Heap` (not a
	// `TypeParam`/`AssocTypeProjection`), so the associated-type lookup for
	// `Elem` fell into `resolve_impl_member`'s inherent/trait-impl fallback —
	// which never recorded an access on `Container::assoc_types["Elem"]`,
	// leaving hover/go-to-definition on `Elem` with nothing to find.
	let source = indoc! {"
        trait Bound {}
        impl Bound for u32 {}
        trait Container {
            type Elem: Bound;
        }
        struct Heap {}
        impl Container for Heap {
            type Elem = u32;
        }
        impl Heap {
            fn zero() -> Self::Elem {
                0
            }
        }
    "};
	let case = TestCase::new(source);
	no_errors(&case);

	let container_trait = case
		.tir
		.items
		.traits
		.iter()
		.find(|t| {
			case.graph.interner.resolve(t.name.inner) == Some("Container")
		})
		.expect("trait 'Container' not found");

	let elem_sym = case
		.graph
		.interner
		.get("Elem")
		.expect("symbol 'Elem' not interned");

	let elem_assoc_type = container_trait
		.assoc_types
		.get(&elem_sym)
		.expect("expected 'Elem' in Container::assoc_types");

	let self_elem_offset = source.find("Self::Elem").unwrap() + "Self::".len();
	assert!(
		elem_assoc_type
			.accesses
			.iter()
			.any(|access| access.span.start == self_elem_offset as u32),
		"expected an access recorded at the `Self::Elem` usage (offset {self_elem_offset}), got: {:?}",
		elem_assoc_type.accesses
	);
}

#[test]
fn test_mutually_recursive_trait_assoc_type_where_bindings_record_accesses() {
	// Regression test: `resolve_bounds`'s `WithBindings` arm looked up
	// `assoc_types.get_mut(&binding.name)` on the *other* trait before that
	// trait had necessarily inserted its own entry — for two traits whose
	// assoc-type `where` clauses reference each other (`A::X` bound by `B
	// where { Y = Self }`, and vice versa), the first trait processed (`A`,
	// being earlier in parse order) would reference `B::Y` before `B`'s own
	// `TraitAssocType` node had run, silently dropping the access (no
	// diagnostic — the lookup just missed). Fixed by pre-registering the
	// assoc type in `assoc_types` (with placeholder bounds) before resolving
	// its own bounds, so a same-name lookup during mutual resolution always
	// finds an entry to record against.
	//
	// Deliberately named `A`/`B`/`X`/`Y` rather than something like
	// `UnsignedInt`/`SignedInt` — the stdlib now declares its own traits by
	// those names, and this test needs to stay independent of stdlib
	// content (searching `case.tir.items.traits` by name would otherwise find the
	// stdlib's same-named trait instead of this test's local one).
	let source = indoc! {"
        trait A {
            type X: B where { Y = Self };
        }

        trait B {
            type Y: A where { X = Self };
        }
    "};
	let case = TestCase::new(source);
	no_errors(&case);

	let find_trait = |name: &str| {
		case.tir
			.items
			.traits
			.iter()
			.find(|t| case.graph.interner.resolve(t.name.inner) == Some(name))
			.unwrap_or_else(|| panic!("trait '{name}' not found"))
	};
	let trait_a = find_trait("A");
	let trait_b = find_trait("B");

	let x_sym = case.graph.interner.get("X").unwrap();
	let y_sym = case.graph.interner.get("Y").unwrap();

	let y_binding_offset = source.find("Y = Self").unwrap();
	let x_binding_offset = source.find("X = Self").unwrap();

	let x_at = trait_a
		.assoc_types
		.get(&x_sym)
		.expect("expected 'X' in A::assoc_types");
	assert!(
		x_at.accesses
			.iter()
			.any(|acc| acc.span.start == x_binding_offset as u32),
		"expected an access on A::X at the `X = Self` binding (offset \
		 {x_binding_offset}), got: {:?}",
		x_at.accesses
	);

	let y_at = trait_b
		.assoc_types
		.get(&y_sym)
		.expect("expected 'Y' in B::assoc_types");
	assert!(
		y_at.accesses
			.iter()
			.any(|acc| acc.span.start == y_binding_offset as u32),
		"expected an access on B::Y at the `Y = Self` binding (offset \
		 {y_binding_offset}), got: {:?}",
		y_at.accesses
	);
}

#[test]
fn test_assoc_type_impl_bound_violation_is_error() {
	// `type Size = bool` where `Size: PointerSize` and `bool` does not
	// implement `PointerSize` → diagnostic.
	let case = TestCase::new(indoc! {"
        trait PointerSize {}
        impl PointerSize for u32 {}
        trait Memory {
            type Size: PointerSize;
        }
        struct Heap {}
        impl Memory for Heap {
            type Size = bool;
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected E1063 (TraitBoundViolation) for `bool` not implementing `PointerSize`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
#[ignore = "false-positive TraitBoundViolation for an abstract projection's own trait-declared bound — see comment above"]
fn test_generic_impl_assoc_type_projection_satisfies_its_own_declared_bound() {
	// `impl<T: Container> Container for Wrap<T> { type Elem = T::Elem; }` —
	// the impl's own `Elem` value is the still-abstract projection `T::Elem`,
	// not a concrete type, because `T` is a type param at this impl's own
	// signature-resolution time.
	//
	// `check_trait_conformance`'s Phase 3.5 (`check_assoc_type_bounds`,
	// generics.rs) then verifies this value against `Container::Elem`'s own
	// declared bound (`type Elem: Bound`) — i.e. it asks "does `T::Elem`
	// implement `Bound`?" via `find_trait_impl(&self.types, ty.inner,
	// bound.trait_index)`. `find_trait_impl` only ever resolves a *concrete*
	// `ImplTarget` (struct/enum/primitive/...), so it returns `None` for an
	// abstract `AssocTypeProjection` — and `check_assoc_type_bounds` reports
	// that as a genuine violation, exactly as if `T::Elem` were some
	// concrete type that simply doesn't implement `Bound`.
	//
	// That's a false positive: `T::Elem: Bound` holds unconditionally here,
	// by construction — `Container::Elem` is declared as `type Elem: Bound`
	// in the trait itself, so *any* concrete type that ends up standing in
	// for `T` already had its own `Elem` checked against `Bound` when *its*
	// impl was conformance-checked. `check_assoc_type_bounds` has no case
	// for "the projection's base is abstract, but its own trait declaration
	// already guarantees the bound" — it only ever consults `find_trait_impl`,
	// which needs a concrete receiver.
	//
	// Found while investigating a hypothesized `substitute_type` projection
	// cycle for the trait-conformance-diff refactor; that specific cycle did
	// not reproduce as a hang or crash (self- and mutual-reference at
	// declaration time can't infinitely recurse — `members` is only
	// populated after a value is computed, and a deferred `TypeParam`-rooted
	// projection never consults any impl's `members` table until a concrete
	// substitution shrinks it) — see
	// `test_mutual_concrete_assoc_type_value_reference_should_report_cyclic_dependency`
	// below for what *does* go wrong with that case (a misleading diagnostic,
	// not a hang). This is a separate, real gap surfaced along the way.
	let case = TestCase::new(indoc! {"
        trait Bound {}
        trait Container {
            type Elem: Bound;
        }
        struct Wrap<T> {}
        impl<T: Container> Container for Wrap<T> {
            type Elem = T::Elem;
        }
    "});
	no_errors(&case);
}

#[test]
#[ignore = "mutual assoc-type-value reference reports a misleading cascade instead of CyclicTypeDependency — see comment above"]
fn test_mutual_concrete_assoc_type_value_reference_should_report_cyclic_dependency()
 {
	// `impl Container for A { type Elem = B::Elem; }` next to
	// `impl Container for B { type Elem = A::Elem; }` — a genuine cycle:
	// neither side can be given a value without the other already having
	// one, in either processing order. This is structurally the same
	// problem `test_self_referential_const_reports_a_cycle` already handles
	// correctly for `const A: i32 = A;` via `ensure_signature`'s
	// `ComputeState::InProgress` guard + `report_cyclic_type_dependency`.
	//
	// That machinery isn't wired up for this path, though:
	// `resolve_namespace_type_member`'s catch-all arm (paths.rs, reached
	// because `B`/`A` are concrete struct types) reads
	// `self.items.assoc_type_impls[idx].ty.unwrap()` straight off the
	// found `AssocTypeImpl`, without first calling `ensure_signature` on
	// *that specific assoc-type-impl's own* `DefId` the way
	// `resolve_bounds`'s `WithBindings` arm (generics.rs) and every
	// "parent before member" call in traits.rs already do before reading
	// something another item owns. So instead of catching the cycle via
	// `ComputeState::InProgress`, whichever impl is processed first (parse
	// order: `A` here) just finds the other's `Elem` isn't in `members` yet
	// — not because of a cycle, but because `B`'s own `Elem` member hasn't
	// been registered at all yet — and reports a plain "not found" instead.
	// That result (`TypeIndex::ERROR`) then flows into `B`'s `Elem`, which
	// resolves "successfully" against it, and the whole thing cascades into
	// two more confusing `TraitBoundViolation`s on top, none of which say
	// anything about a cycle.
	//
	// Fix sketch: in `resolve_namespace_type_member`'s
	// `MemberLookup::Trait`/`MemberLookup::Inherent` arms for
	// `ImplEntry::AssocType(idx)`, call
	// `self.ensure_signature(self.items.assoc_type_impls[idx].id)` first,
	// and report via `report_cyclic_type_dependency` on `SignatureStatus::
	// Cycle` — mirroring `resolve_pending_global_symbol`/
	// `resolve_pending_namespace_symbol` (modules.rs). Each `AssocTypeImpl`
	// already carries its own registered `id`/`ast_nodes` entry
	// (`AstNodeRef::TraitImplAssocType`, prescan.rs), so `ensure_signature`
	// dispatches correctly — it's just never called on this path.
	//
	// One more thing the fix needs: `push_assoc_type_impl` (tir/mod.rs)
	// never inserts its `id` into `item_lookup`, unlike every other
	// `push_*` — so `item_name()`, which `report_cyclic_type_dependency`
	// uses to label each frame in the "the cycle is `X` -> `Y`" note, has
	// no case for an associated type and would silently skip that frame.
	// Needs an `ItemIndex::AssocType` variant added the same way
	// `push_typeset` registers `ItemIndex::TypeSet` right below it.
	let case = TestCase::new(indoc! {"
        trait Bound {}
        impl Bound for u32 {}
        trait Container {
            type Elem: Bound;
        }
        struct A {}
        struct B {}
        impl Container for A {
            type Elem = B::Elem;
        }
        impl Container for B {
            type Elem = A::Elem;
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CyclicTypeDependency),
		"expected a CyclicTypeDependency diagnostic for the A::Elem <-> \
		 B::Elem cycle, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_assoc_type_where_binding_out_of_order_type_param_resolves() {
	// `Src: Memory where { Size = S }` where `S` is defined AFTER `Src` —
	// the two-pass resolution must find `S` in the full scope even though
	// it wasn't yet built when the bound was first parsed.
	let case = TestCase::new(indoc! {"
        trait PointerSize {}
        trait Memory {
            type Size: PointerSize;
        }
        fn copy<Src: Memory where { Size = S }, S: PointerSize>() {
            unreachable
        }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_unconstrained_no_error() {
	// An associated type with no bounds accepts any concrete type.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
        }
        struct Bag {}
        impl Container for Bag {
            type Item = i32;
        }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_projection_forwarded_in_generic_wrapper() {
	// A generic wrapper that passes a `C::Item` argument to another function
	// also expecting `C::Item` must compile without errors.
	// Previously, the expected_type was silently dropped to None when the
	// receiver was itself a TypeParam, skipping the check entirely.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
        }
        fn process<C: Container>(item: C::Item) {
            unreachable
        }
        fn wrap<C: Container>(item: C::Item) {
            process(item)
        }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_projection_concrete_mismatch_in_generic_wrapper() {
	// Passing a concrete `i32` where `C::Item` is expected must be a type
	// error — even inside a generic wrapper where the receiver is a TypeParam.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
        }
        fn process<C: Container>(item: C::Item) {
            unreachable
        }
        fn wrap<C: Container>(item: C::Item, n: i32) {
            process(n)
        }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

#[test]
fn test_assoc_type_projection_in_nested_function_type_wrapper() {
	// Recursive substitution must also rebind projections nested inside
	// function types, not only top-level parameter and result types.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
        }
        fn process<C: Container>(f: fn(C::Item) -> C::Item) {
            unreachable
        }
        fn wrap<C: Container>(f: fn(C::Item) -> C::Item) {
            process(f)
        }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_projection_in_tuple_wrapper() {
	// Recursive substitution must also preserve projections nested inside
	// tuple elements.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
        }
        fn process<C: Container>(pair: (C::Item, C::Item)) {
            unreachable
        }
        fn wrap<C: Container>(pair: (C::Item, C::Item)) {
            process(pair)
        }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_projection_in_pointer_wrapper() {
	// Recursive substitution must also preserve projections nested under
	// pointer types. Untagged `&C::Item` resolves memory from the single
	// ambient memory declaration.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            trait Container {
                type Item;
            }
            fn process<C: Container>(ptr: &C::Item) {
                unreachable
            }
            fn wrap<C: Container>(ptr: &C::Item) {
                process(ptr)
            }
        "},
		&[],
	);
	no_errors(&case);
}

// ── generic functions over Memory ────────────────────────────────────────────

#[test]
fn test_generic_over_memory_size_in_signature() {
	// A generic fn<M: Memory>(M::Size) → M::Size must resolve without errors:
	// M::Size stays as AssocTypeProjection in the generic signature.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn pass<M: Memory>(mem: M, n: M::Size) -> M::Size {
                n
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_generic_over_memory_called_with_concrete_memory() {
	// Calling pass(heap, 42u32) must unify M=heap → M::Size=u32 with no errors.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn pass<M: Memory>(mem: M, n: M::Size) -> M::Size {
                n
            }
            pub fn caller(n: u32) -> u32 {
                pass(heap, n)
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_generic_over_memory_wrong_size_type_is_error() {
	// Passing i64 where M::Size=u32 is expected must be a type error.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn pass<M: Memory>(mem: M, n: M::Size) -> M::Size {
                n
            }
            pub fn caller(n: i64) -> u32 {
                pass(heap, n)
            }
        "},
		&[],
	);
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

#[test]
fn test_generic_over_memory_two_concrete_memories() {
	// The same generic fn called with both a Memory32 and a Memory64 must
	// resolve correctly for each — M::Size = u32 and M::Size = u64.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            memory stack: Memory where { Size = u64 };
            fn pass<M: Memory>(mem: M, n: M::Size) -> M::Size {
                n
            }
            pub fn use_heap(n: u32) -> u32 {
                pass(heap, n)
            }
            pub fn use_stack(n: u64) -> u64 {
                pass(stack, n)
            }
        "},
		&[],
	);
	no_errors(&case);
}

// ── Type::Infer / underscore type placeholder ────────────────────────────────

#[test]
fn test_infer_placeholder_in_generic_type_arg() {
	// `Layout<_>` where the local variable's assigned value fully constrains
	// the type arg — the `_` is the user-written inference placeholder and
	// must not cause an error when the context resolves it.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            struct Layout<M: Memory> { size: M::Size }
            impl <M: Memory> Layout<M> {
                pub fn new(size: M::Size) -> Layout<M> {
                    Layout::{ size }
                }
            }
            pub fn demo() {
                local x: Layout<_> = Layout::<heap>::new(4 as u32);
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_cannot_infer_generic_type_param_error() {
	// Calling a generic constructor without enough context to infer the type
	// parameter must be an error with a "cannot infer type for type parameter"
	// diagnostic.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            struct Layout<M: Memory> { size: M::Size }
            impl <M: Memory> Layout<M> {
                pub fn array<T>(count: M::Size) -> Layout<M> {
                    Layout::{ size: count }
                }
            }
            pub fn demo() {
                local y = Layout::array::<i32>(4);
            }
        "},
		&[],
	);
	has_error_matching(&case, "cannot infer type for type parameter `M`");

	// When M is also specified via turbofish on the first segment, both params
	// are fully resolved and there should be no errors.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            struct Layout<M: Memory> { size: M::Size }
            impl <M: Memory> Layout<M> {
                pub fn array<T>(count: M::Size) -> Layout<M> {
                    Layout::{ size: count }
                }
            }
            pub fn demo() {
                local y = Layout::<heap>::array::<i32>(10);
            }
        "},
		&[],
	);
	no_errors(&case);
}

// ── `_` (infer placeholder) edge cases ──────────────────────────────────────

#[test]
fn test_infer_in_function_param_type_is_error() {
	let case = TestCase::new(indoc! {"
        fn foo(x: _) -> i32 { 0 }
    "});
	has_error_matching(
		&case,
		"`_` is not allowed within types on item signatures",
	);
}

#[test]
fn test_infer_in_function_return_type_is_error() {
	let case = TestCase::new(indoc! {"
        fn foo() -> _ { 0 }
    "});
	has_error_matching(
		&case,
		"`_` is not allowed within types on item signatures",
	);
}

#[test]
fn test_infer_in_struct_field_is_error() {
	let case = TestCase::new(indoc! {"
        struct Foo { x: _ }
    "});
	has_error_matching(
		&case,
		"`_` is not allowed within types on item signatures",
	);
}

#[test]
fn test_infer_in_global_declaration_is_error() {
	let case = TestCase::new(indoc! {"
        global x: _ = 0;
    "});
	has_error_matching(
		&case,
		"`_` is not allowed within types on item signatures",
	);
}

#[test]
fn test_infer_in_cast_without_context_is_error() {
	// `42 as _` with no type context — target type cannot be inferred.
	let case = TestCase::new(indoc! {"
        fn foo() { local x = 42 as _; }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::TypeAnnotationRequired
	));
}

#[test]
fn test_infer_in_cast_with_context_succeeds() {
	// `42 as _` where context supplies the target type — should lower cleanly.
	let case = TestCase::new(indoc! {"
        fn foo() -> i32 { 42 as _ }
    "});
	no_errors(&case);
}

#[test]
fn test_infer_multi_wildcard_tuple_annotation() {
	// Both `_` slots should be filled from the RHS — no error.
	let case = TestCase::new(indoc! {"
        fn foo() {
            local x: (i32, f32) = (1 as i32, 2.0 as f32);
            local y: (_, _) = (1 as i32, 2.0 as f32);
        }
    "});
	no_errors(&case);
}

#[test]
fn test_infer_annotation_type_mismatch_still_errors() {
	// `local x: i32 = 1.0 as f32` should still produce a type mismatch even
	// when using `_` for the other slot.
	let case = TestCase::new(indoc! {"
        fn foo() {
            local x: (i32, _) = (1.0 as f32, 2 as i32);
        }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

#[test]
fn test_infer_local_no_rhs_annotation_only_is_error() {
	// `local x: _` with no initializer is not valid syntax, but `local x: _ = expr`
	// where expr is also completely unconstrained should produce an error.
	let case = TestCase::new(indoc! {"
        fn foo() -> i32 {
            local x: _ = 42;
            x
        }
    "});
	// The integer literal 42 by itself with no constraint should require annotation.
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::TypeAnnotationRequired
	));
}

#[test]
fn test_module_namespace_type_access() {
	// `module::Type` — a type accessed through a module namespace resolves
	// to the module's declared type without errors.
	let case = TestCase::new(indoc! {"
        mod shapes {
            pub struct Circle {}
        }
        fn use_circle(c: shapes::Circle) {
            unreachable
        }
    "});
	no_errors(&case);
}

// ── Memory-tagged pointer types ──────────────────────────────────────────────

#[test]
fn test_memory_tagged_pointer() {
	// `heap::&i32` resolves to Type::Pointer { memory: Some(heap_id) }
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(p: heap::&i32) {
                unreachable
            }
        "},
		&[],
	);
	no_errors(&case);

	let heap_id = case.tir.items.memories[0].id;
	let f = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("f"))
		.expect("function 'f' not found");

	let param_ty = f.params[0].ty.inner;
	let is_heap_ptr = match case.tir.types.resolve(param_ty) {
		Type::Pointer { memory, .. } => {
			matches!(case.tir.types.resolve(*memory), Type::Memory { id, .. } if *id == heap_id)
		}
		_ => false,
	};
	assert!(
		is_heap_ptr,
		"expected heap::&i32 (pointer tagged with heap), got index {}",
		u32::from(param_ty)
	);
}

#[test]
fn test_memory_tagged_slice() {
	// `heap::&[u8]` resolves to Type::Slice { memory: Some(heap_id) }
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(s: heap::&[u8]) {
                unreachable
            }
        "},
		&[],
	);
	no_errors(&case);

	let heap_id = case.tir.items.memories[0].id;
	let f = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("f"))
		.expect("function 'f' not found");

	let param_ty = f.params[0].ty.inner;
	let is_heap_slice = match case.tir.types.resolve(param_ty) {
		Type::Slice { memory, .. } => {
			matches!(case.tir.types.resolve(*memory), Type::Memory { id, .. } if *id == heap_id)
		}
		_ => false,
	};
	assert!(
		is_heap_slice,
		"expected heap::&[u8] (slice tagged with heap), got index {}",
		u32::from(param_ty)
	);
}

#[test]
fn test_memory_tagged_array() {
	// `heap::&[u8; 4]` resolves to Type::Array { size: 4, memory: Some(heap_id) }
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[u8; 4]) {
                unreachable
            }
        "},
		&[],
	);
	no_errors(&case);

	let heap_id = case.tir.items.memories[0].id;
	let f = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("f"))
		.expect("function 'f' not found");

	let param_ty = f.params[0].ty.inner;
	let is_heap_array = match case.tir.types.resolve(param_ty) {
		Type::Array {
			size: 4, memory, ..
		} => {
			matches!(case.tir.types.resolve(*memory), Type::Memory { id, .. } if *id == heap_id)
		}
		_ => false,
	};
	assert!(
		is_heap_array,
		"expected heap::&[u8; 4] (array tagged with heap), got index {}",
		u32::from(param_ty)
	);
}

#[test]
fn test_memory_tagged_nested_array() {
	// `heap::&[heap::&[u8; 4]; 4]` — outer array in heap, elements are heap-tagged arrays
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[heap::&[u8; 4]; 4]) {
                unreachable
            }
        "},
		&[],
	);
	no_errors(&case);

	let heap_id = case.tir.items.memories[0].id;
	let f = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("f"))
		.expect("function 'f' not found");

	let outer_ty = f.params[0].ty.inner;
	let is_heap_mem = |memory: &TypeIndex| matches!(case.tir.types.resolve(*memory), Type::Memory { id, .. } if *id == heap_id);
	let (inner_ty, outer_tagged) = match case.tir.types.resolve(outer_ty) {
		Type::Array {
			of,
			size: 4,
			memory,
			..
		} if is_heap_mem(memory) => (*of, true),
		_ => (TypeIndex::ERROR, false),
	};
	assert!(
		outer_tagged,
		"outer array should be tagged with heap memory"
	);
	let inner_tagged = match case.tir.types.resolve(inner_ty) {
		Type::Array {
			size: 4, memory, ..
		} => is_heap_mem(memory),
		_ => false,
	};
	assert!(
		inner_tagged,
		"inner array should also be tagged with heap memory"
	);
}

#[test]
fn test_memory_tagged_non_pointer_is_error() {
	// `heap::i32` — memory namespace before a scalar type should error
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(x: heap::i32) {
                unreachable
            }
        "},
		&[],
	);
	assert!(has_error_code(&case.tir, DiagnosticCode::UndeclaredType)); // heap::i32 — `i32` is not a member of the memory namespace
}

#[test]
fn test_untagged_and_tagged_pointer_resolve_to_same_type() {
	// With one memory in scope, `&i32` and `heap::&i32` resolve to the same type.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: &i32, b: heap::&i32) {
                unreachable
            }
        "},
		&[],
	);
	no_errors(&case);

	let f = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("f"))
		.expect("function 'f' not found");

	let untagged = f.params[0].ty.inner;
	let tagged = f.params[1].ty.inner;
	assert_eq!(
		untagged, tagged,
		"with one memory, &i32 and heap::&i32 should intern to the same TypeIndex"
	);
}

// ── FunctionItem type tests
// ───────────────────────────────────────────────────

#[test]
fn test_function_reference_has_function_item_type() {
	// When a function name is used as a value (not immediately called), the
	// resulting expression type must be `FunctionItem`, not `Function`. This
	// ensures the compiler preserves the function's identity rather than
	// exposing its raw (potentially TypeParam-polluted) signature.
	let case = TestCase::new(indoc! {"
        fn square(n: i32) -> i32 { n * n }
        fn main() {
            local f = square
        }
    "});
	no_errors(&case);

	let square_id = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("square"))
		.expect("function 'square' not found")
		.id;

	let has_function_item = case.tir.types.entries.iter().any(|t| {
		if let Type::FunctionItem { id, type_args } = t {
			*id == square_id && type_args.is_empty()
		} else {
			false
		}
	});
	assert!(
		has_function_item,
		"expected Type::FunctionItem for 'square' in the type pool"
	);
}

#[test]
fn test_generic_function_reference_has_function_item_not_fn_pointer() {
	// A reference to a generic function must produce `FunctionItem`, not
	// `Function { signature: fn(TypeParam{0}) -> TypeParam{0} }`. The old
	// representation leaked TypeParam internals and made it impossible to
	// distinguish which function was being referenced.
	let case = TestCase::new(indoc! {"
        fn identity<T>(t: T) -> T { t }
        fn main() {
            local f = identity
        }
    "});
	no_errors(&case);

	let identity_id = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("identity"))
		.expect("function 'identity' not found")
		.id;

	let has_function_item = case.tir.types.entries.iter().any(
		|t| matches!(t, Type::FunctionItem { id, .. } if *id == identity_id),
	);
	assert!(
		has_function_item,
		"expected Type::FunctionItem for generic 'identity'"
	);

	// The function's own signature_index is still fn(TypeParam{0}) ->
	// TypeParam{0} in the pool (needed for the function body), but function
	// *reference* expressions must use FunctionItem, not expose that raw
	// signature as their value type.
}

#[test]
fn test_indirect_call_via_function_item_local_compiles() {
	// Storing a function in a local and calling it via the local is valid.
	// `f` has type `FunctionItem`, but calling it works because
	// `build_call_expression` resolves the signature through the function id.
	let case = TestCase::new(indoc! {"
        fn square(n: i32) -> i32 { n * n }
        fn main() -> i32 {
            local f = square
            f(5)
        }
    "});
	no_errors(&case);
}

#[test]
fn test_function_item_type_error_label_names_function() {
	// When a `FunctionItem` is passed where a concrete function-pointer type is
	// expected, the error label must name the function ("identity"), not show
	// its raw signature ("fn(T0) -> T0"). This verifies `display_type` for
	// `Type::FunctionItem` returns the function name.
	let case = TestCase::new(indoc! {"
        fn identity<T>(t: T) -> T { t }
        fn take_fn(f: fn(i32) -> i32) -> i32 { f(0) }
        fn main() -> i32 {
            take_fn(identity)
        }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"expected a type error when passing FunctionItem where fn pointer expected"
	);
	assert!(
		case.tir.diagnostics.iter().any(|d| {
			d.labels.iter().any(|l| l.message.contains("identity"))
		}),
		"error label must name the function 'identity', not show raw TypeParam signature"
	);
}

#[test]
fn test_missing_argument_uses_callee_type_param_names() {
	let case = TestCase::new(indoc! {"
        fn take<T>(value: T) {
            unreachable
        }

        fn wrap<U>() {
            take()
        }
    "});

	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"expected missing argument error"
	);
	assert!(
		case.tir.diagnostics.iter().any(|d| {
			d.notes
				.iter()
				.any(|note| note.contains("argument #1 of type `T` is missing"))
		}),
		"missing argument diagnostic should use callee type parameter name `T`"
	);
}

#[test]
fn test_two_functions_have_distinct_function_item_types() {
	// Each distinct function must intern to a distinct `FunctionItem` TypeIndex.
	// Sharing a type between different functions would break identity-based
	// dispatch and type checking.
	let case = TestCase::new(indoc! {"
        fn square(n: i32) -> i32 { n * n }
        fn double(n: i32) -> i32 { n + n }
        fn main() {
            local a = square
            local b = double
        }
    "});
	no_errors(&case);

	let find_id = |name: &str| {
		case.tir
			.items
			.functions
			.iter()
			.find(|f| case.graph.interner.resolve(f.name.inner) == Some(name))
			.unwrap_or_else(|| panic!("function '{}' not found", name))
			.id
	};
	let square_id = find_id("square");
	let double_id = find_id("double");

	let type_idx = |id: DefId| {
		case.tir
			.types
			.entries
			.iter()
			.enumerate()
			.find_map(|(i, t)| {
				if matches!(t, Type::FunctionItem { id: fid, .. } if *fid == id)
				{
					Some(TypeIndex(i as u32))
				} else {
					None
				}
			})
			.unwrap_or_else(|| panic!("FunctionItem for {:?} not found", id))
	};
	assert_ne!(
		type_idx(square_id),
		type_idx(double_id),
		"square and double must have distinct FunctionItem TypeIndex values"
	);
}

#[test]
fn test_function_item_coerces_to_matching_fn_pointer_type() {
	// A FunctionItem must be implicitly coercible to a `fn(...)` parameter
	// whose signature matches exactly. This is the `func_pointers.wx` pattern:
	// passing a named function where a function-pointer argument is expected.
	let case = TestCase::new(indoc! {"
        fn add(a: i32, b: i32) -> i32 { a + b }
        fn sub(a: i32, b: i32) -> i32 { a - b }
        fn apply(binop: fn(i32, i32) -> i32, a: i32, b: i32) -> i32 {
            binop(a, b)
        }
        fn main() -> i32 {
            local a = apply(add, 5, 10)
            local b = apply(sub, 10, 5)
            a + b
        }
    "});
	no_errors(&case);
}

#[test]
fn test_function_item_wrong_signature_is_error() {
	// A FunctionItem must NOT coerce to a `fn(...)` type with a different
	// signature — the arity or parameter types must match exactly.
	let case = TestCase::new(indoc! {"
        fn add(a: i32, b: i32) -> i32 { a + b }
        fn apply(binop: fn(i32) -> i32, n: i32) -> i32 { binop(n) }
        fn main() -> i32 {
            apply(add, 5)
        }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

// ── Type application expressions ─────────────────────────────────────────────

#[test]
fn test_type_application_coerces_to_fn_pointer() {
	// `identity::<i32>` must coerce to `fn(i32) -> i32`.
	let case = TestCase::new(indoc! {"
        fn identity<T>(t: T) -> T { t }
        fn main() {
            local f: fn(i32) -> i32 = identity::<i32>
        }
    "});
	no_errors(&case);
}

#[test]
fn test_type_application_wrong_arg_count_is_error() {
	let case = TestCase::new(indoc! {"
        fn identity<T>(t: T) -> T { t }
        fn main() {
            local f = identity::<i32, i64>
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 (TypeArgCountMismatch) for too many type args, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_type_application_on_non_generic_is_error() {
	let case = TestCase::new(indoc! {"
        fn add(a: i32, b: i32) -> i32 { a + b }
        fn main() {
            local f = add::<i32>
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 (TypeArgCountMismatch) for type args on non-generic fn, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_generic_method_self_shape_mismatch_reports_clear_diagnostic() {
	// Regression: calling a method whose `self` requires a pointer
	// (`self: &Self`) on a plain value receiver used to report a
	// confusing "cannot infer type for type parameter `Self`" —
	// `infer_type_args` only unifies matching shapes (Pointer only binds
	// against Pointer), so a value receiver just silently failed to bind
	// `Self` rather than reporting *why*. `resolve_method_call` now catches
	// the pointer-vs-value shape mismatch directly (before any type_args
	// machinery runs) and reports one clear `TypeMistmatch` instead of
	// leaving it to surface later as an unhelpful "type annotation required".
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        trait Foo {
            fn bar<T>(self: &Self) -> T { unreachable }
        }

        struct S {}

        impl Foo for S {}

        fn f() {
            local s = S::{};
            local n = s.bar::<u32>();
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (type mismatch), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::TypeAnnotationRequired),
		"should not also report 'cannot infer type parameter Self', got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_method_call_turbofish_resolves_own_type_param() {
	// Regression: `build_method_call_expression` destructured `MethodCallExpr`
	// with `..`, silently discarding the AST's `type_args` field — explicit
	// turbofish on a method call (`.make::<u32>()`) was parsed but never used,
	// forcing inference to work it out from context alone (or fail).
	let case = TestCase::new(indoc! {"
        struct Wrapper<M> { x: M }
        impl <M> Wrapper<M> {
            pub fn make<T>(self) -> T { unreachable }
        }
        fn f(w: Wrapper<i32>) -> u32 {
            w.make::<u32>()
        }
        export { f }
    "});
	no_errors(&case);
}

#[test]
fn test_method_call_turbofish_pads_past_impl_level_type_args() {
	// Regression: `resolve_method_call` returned the impl-level substitution
	// (e.g. `[M = heap]`, length 1) as-is whenever it was non-empty, instead
	// of padding it out to the method's *total* type param count (impl-level
	// + the method's own). For a generic inherent-impl method that also
	// declares its own additional type param (`fn make<T>` on `impl<M> Wrapper<M>`),
	// this left `type_args` one slot too short. Turbofish merging (which
	// writes into the trailing "own" slots, offset by the impl-level count)
	// then corrupted the *impl-level* slot instead — `M` got overwritten with
	// the turbofish value meant for `T`, breaking the object's own type check.
	// Fixed by padding the impl-level substitution to `total_type_param_count()`
	// with `INFER` before returning it.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Wrapper<M: Memory> { x: M::Size }
        impl <M: Memory> Wrapper<M> {
            pub fn make<T>(self) -> T { unreachable }
        }
        fn f(w: Wrapper<heap>) -> u32 {
            w.make::<u32>()
        }
        export { f }
    "});
	no_errors(&case);
}

#[test]
fn test_method_call_turbofish_wrong_count_is_error() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<M> { x: M }
        impl <M> Wrapper<M> {
            pub fn make<T>(self) -> T { unreachable }
        }
        fn f(w: Wrapper<i32>) -> u32 {
            w.make::<u32, i32>()
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 (TypeArgCountMismatch) for too many type args on method call, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_method_call_turbofish_on_non_generic_method_is_error() {
	let case = TestCase::new(indoc! {"
        struct Wrapper<M> { x: M }
        impl <M> Wrapper<M> {
            pub fn plain(self) -> i32 { 0 }
        }
        fn f(w: Wrapper<i32>) -> i32 {
            w.plain::<i32>()
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeArgCountMismatch),
		"expected E1040 (TypeArgCountMismatch) for type args on non-generic method, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_type_application_in_if_else_unifies() {
	// Two distinct generic instantiations with the same signature unify.
	let case = TestCase::new(indoc! {"
        fn identity<T>(t: T) -> T { t }
        fn wrap<T>(t: T) -> T { t }
        fn main() -> fn(i32) -> i32 {
            local f: fn(i32) -> i32 = if true { identity::<i32> } else { wrap::<i32> }
            f
        }
    "});
	no_errors(&case);
}

// ── Pointer dereference ──────────────────────────────────────────────────────

#[test]
fn test_deref_load_through_pointer() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn read(ptr: heap::&i32) -> i32 { ptr.* }
    "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_deref_store_through_mutable_pointer() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn write(ptr: heap::*i32) { ptr.* = 42 }
    "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_deref_arithmetic_assignment_through_mutable_pointer() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn increment(ptr: heap::*i32) { ptr.* += 1 }
    "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_deref_non_pointer_type_is_error() {
	let case = TestCase::new(indoc! {"
        fn bad(x: i32) -> i32 { x.* }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotDerefNonPointer),
		"expected E1037 (dereference of non-pointer type)"
	);
}

#[test]
fn test_deref_no_memory_is_error() {
	let case = TestCase::new(indoc! {"
        fn bad(ptr: *i32) -> i32 { ptr.* }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::NoMemoryForPointer),
		"expected E1038 (no memory for pointer)"
	);
}

#[test]
fn test_deref_store_through_immutable_pointer_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn bad(ptr: heap::&i32) { ptr.* = 42 }
    "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"expected W1000 (CannotMutateImmutable) for store through immutable pointer, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_deref_arithmetic_assignment_through_immutable_pointer_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn bad(ptr: heap::&i32) { ptr.* += 1 }
    "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"expected W1000 (CannotMutateImmutable) for arithmetic-assign through immutable pointer, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_deref_type_mismatch_on_store_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn bad(ptr: heap::*i32) { ptr.* = true }
    "},
		&[],
	);
	has_error_matching(&case, "cannot assign");
}

// ── Multi-segment path resolution
// ─────────────────────────────────────────────

#[test]
fn test_path_type_associated_fn_ufcs() {
	// `Signed::abs(s)` — 2-segment path where the first segment is a type and
	// the second is an associated function; all params (including self) are
	// explicit.
	let case = TestCase::new(indoc! {"
        struct Signed { value: i32 }
        impl Signed {
            pub fn abs(self) -> i32 {
                if self.value < 0 { -self.value } else { self.value }
            }
        }
        fn f(x: i32) -> i32 {
            Signed::abs(Signed::{ value: x })
        }
        export { f }
    "});
	no_errors(&case);
}

#[test]
fn test_path_struct_associated_fn_no_params() {
	// `Counter::zero()` — zero-parameter associated function on a user-defined struct.
	let case = TestCase::new(indoc! {"
        struct Counter { value: u32 }
        impl Counter {
            pub fn zero() -> Counter { Counter::{ value: 0 } }
        }
        fn test() -> Counter { Counter::zero() }
        export { test }
    "});
	no_errors(&case);
}

#[test]
fn test_path_generic_struct_associated_fn() {
	// `Wrapper::<u32>::new(42)` — associated function on a generic struct via generic impl.
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { value: T }
        impl<T> Wrapper<T> {
            pub fn new(value: T) -> Wrapper<T> { Wrapper::{ value } }
        }
        fn test() -> Wrapper<u32> { Wrapper::<u32>::new(42) }
        export { test }
    "});
	no_errors(&case);
}

#[test]
fn test_path_inline_module_type_associated_fn() {
	// `math::Point::zero()` — 3-segment path through an inline module to an
	// associated function: module → type → fn.
	let case = TestCase::new(indoc! {"
        mod math {
            pub struct Point {}
            impl Point {
                pub fn zero() -> i32 { 0 }
            }
        }
        fn f() -> i32 {
            math::Point::zero()
        }
        export { f }
    "});
	no_errors(&case);
}

#[test]
fn test_path_cross_module_struct_init() {
	// `shapes::Point::{ x: 1, y: 2 }` — struct literal via a cross-module path.
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod shapes;

            fn make() -> shapes::Point {
                shapes::Point::{ x: 1, y: 2 }
            }

            export { make }
        "},
		&[(
			"src/shapes.wx",
			"pub struct Point { pub x: i32, pub y: i32 }",
		)],
	);
	no_errors(&case);
}

#[test]
fn test_path_cross_module_generic_struct_init() {
	// `containers::Wrapper::<i32>::{ value: 42 }` — generic struct literal via a
	// cross-module path with explicit type args on the last segment.
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod containers;

            fn make() -> containers::Wrapper::<i32> {
                containers::Wrapper::<i32>::{ value: 42 }
            }

            export { make }
        "},
		&[(
			"src/containers.wx",
			"pub struct Wrapper<T> { pub value: T }",
		)],
	);
	no_errors(&case);
}

#[test]
fn test_generic_struct_concrete_impl() {
	// impl Point<i32> — concrete monomorphic impl, no type params needed
	let case = TestCase::new(indoc! {"
        struct Point<T> {
            x: T,
            y: T,
        }

        impl Point<i32> {
            pub fn sum(self) -> i32 { self.x + self.y }
        }

        fn run() -> i32 {
            local p: Point<i32> = Point::{ x: 3, y: 4 };
            p.sum()
        }

        export { run }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_struct_method() {
	// impl Point<T> — generic impl; T in scope, field access returns T
	let case = TestCase::new(indoc! {"
        struct Point<T> {
            x: T,
            y: T,
        }

        impl<T> Point<T> {
            pub fn get_x(self) -> T { self.x }
        }

        fn run() -> i32 {
            local p: Point<i32> = Point::{ x: 3, y: 4 };
            p.get_x()
        }

        export { run }
    "});
	no_errors(&case);
}

// ── Array literals
// ────────────────────────────────────────────────────────────

#[test]
fn test_array_literal_basic() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() -> heap::&[i32; 3] {
                local x: heap::&[i32; 3] = [1, 2, 3];
                x
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_array_literal_mutable() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() -> heap::*[i32; 3] {
                local x: heap::*[i32; 3] = [1, 2, 3];
                x
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_array_literal_float_elements() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() -> heap::&[f32; 2] {
                local x: heap::&[f32; 2] = [1.0, 2.0];
                x
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_array_literal_empty_with_annotation() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() -> heap::&[i32; 0] {
                local x: heap::&[i32; 0] = [];
                x
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_array_literal_size_mismatch_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() {
                local x: heap::&[i32; 3] = [1, 2];
            }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ArraySizeMismatch),
		"expected E1043 (array size mismatch)"
	);
}

#[test]
fn test_array_literal_no_annotation_is_error() {
	// Without a type annotation the element type cannot be inferred from comptime
	// ints.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() {
                local x = [1, 2, 3];
            }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeAnnotationRequired),
		"expected E1002 (type annotation required)"
	);
}

#[test]
fn test_array_literal_no_memory_is_error() {
	// No memory declaration — array cannot be placed in linear memory.
	let case = TestCase::new(indoc! {"
        fn f() {
            local x: &[i32; 3] = [1, 2, 3];
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::NoMemoryForPointer),
		"expected E1038 (no memory for pointer)"
	);
}

#[test]
fn test_array_literal_non_numeric_element_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() {
                local x: heap::&[i32; 2] = [true, false];
            }
        "},
		&[],
	);
	has_error_matching(&case, "array element type must be a numeric type");
}

#[test]
fn test_array_literal_mixed_element_types_is_error() {
	// Mixing a typed expression (true: bool) after a comptime int should mismatch.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(b: bool) {
                local x: heap::&[bool; 2] = [b, b];
            }
        "},
		&[],
	);
	has_error_matching(&case, "array element type must be a numeric type");
}

// ── Array repeat
// ──────────────────────────────────────────────────────────────

#[test]
fn test_array_repeat_basic() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() -> heap::&[i32; 4] {
                local x: heap::&[i32; 4] = [0; 4];
                x
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_array_repeat_float() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() -> heap::&[f64; 8] {
                local x: heap::&[f64; 8] = [0.0; 8];
                x
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_array_repeat_count_not_const_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(n: u32) {
                local x: heap::&[i32; 4] = [0; n];
            }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ArrayRepeatCountNotConst),
		"expected E1044 (array repeat count not const)"
	);
}

#[test]
fn test_array_repeat_size_mismatch_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() {
                local x: heap::&[i32; 4] = [0; 3];
            }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ArraySizeMismatch),
		"expected E1043 (array size mismatch)"
	);
}

#[test]
fn test_array_repeat_no_annotation_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f() {
                local x = [0; 4];
            }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeAnnotationRequired),
		"expected E1002 (type annotation required)"
	);
}

#[test]
fn test_array_repeat_non_numeric_value_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(b: bool) {
                local x: heap::&[i32; 4] = [b; 4];
            }
        "},
		&[],
	);
	has_error_matching(&case, "array element type must be a numeric type");
}

// ── Index operator
// ────────────────────────────────────────────────────────────

#[test]
fn test_index_read_from_array() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[i32; 4]) -> i32 { a[0] }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_read_from_slice() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[i32]) -> i32 { a[0] }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_on_non_indexable_is_error() {
	let case = TestCase::new(indoc! {"
        fn f(x: i32) -> i32 { x[0] }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IndexOnNonIndexable),
		"expected E1042 (index on non-indexable type)"
	);
}

#[test]
fn test_index_wrong_index_type_is_error() {
	// Memory where { Size = u32 } requires u32 index; passing i64 should be a type mismatch.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[i32; 4], i: i64) -> i32 { a[i] }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (TypeMistmatch) for wrong index type, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_index_store_through_mutable_array() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::*[i32; 4]) { a[0] = 42 }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_store_through_immutable_array_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[i32; 4]) { a[0] = 42 }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"expected W1000 (CannotMutateImmutable) for store through immutable array, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_index_arithmetic_assignment_through_mutable_array() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::*[i32; 4]) { a[0] += 1 }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_arithmetic_assignment_through_immutable_array_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[i32; 4]) { a[0] += 1 }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"expected W1000 (CannotMutateImmutable) for arithmetic-assign through immutable array, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_index_store_type_mismatch_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::*[i32; 4]) { a[0] = true }
        "},
		&[],
	);
	has_error_matching(&case, "cannot assign");
}

#[test]
fn test_index_memory64_requires_u64_index() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u64 };
            fn f(a: heap::&[i32; 4]) -> i32 { a[0] }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_ambiguous_memory_is_error() {
	// Two memories and no tag on the array type — cannot resolve memory for
	// indexing.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            memory stack: Memory where { Size = u32 };
            fn f(a: heap::&[i32; 4]) -> i32 { a[0] }
        "},
		&[],
	);
	// The array type already carries heap's memory id, so indexing it should
	// succeed even with two memories declared.
	no_errors(&case);
}

#[test]
fn test_array_literal_runtime_element_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(x: i32) {
                local arr: heap::&[i32; 2] = [x, 1];
            }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ArrayElementNotConst),
		"expected E1045 (array element not const)"
	);
}

#[test]
fn test_array_repeat_runtime_value_is_error() {
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(x: i32) {
                local arr: heap::&[i32; 4] = [x; 4];
            }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ArrayElementNotConst),
		"expected E1045 (array element not const)"
	);
}

// ── abstract memory indexing ──────────────────────────────────────────────────

#[test]
fn test_index_concrete_memory32_typed_variable() {
	// Typed u32 variable (not a literal) as index into a Memory32 array.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[i32; 4], i: u32) -> i32 { a[i] }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_concrete_memory64_typed_variable() {
	// Typed u64 variable as index into a Memory64 array.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u64 };
            fn f(a: heap::&[i32; 4], i: u64) -> i32 { a[i] }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_memory32_with_u64_variable_is_error() {
	// Typed u64 index on a Memory32 (u32-indexed) array must be rejected.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn f(a: heap::&[i32; 4], i: u64) -> i32 { a[i] }
        "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (TypeMistmatch) for u64 index on Memory32 array, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_index_generic_array_with_assoc_size_type() {
	// Generic fn over M: Memory indexing M::&[i32; 4] with M::Size — the index
	// type must accept M::Size rather than requiring a concrete integer type.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn read<M: Memory>(arr: M::&[i32; 4], i: M::Size) -> i32 {
                arr[i]
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_generic_slice_with_assoc_size_type() {
	// Same as above but for a slice (runtime-length).
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn read<M: Memory>(s: M::&[i32], i: M::Size) -> i32 {
                s[i]
            }
        "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_index_generic_array_call_with_concrete_memory() {
	// The generic indexing fn must be callable with a concrete memory so
	// M::Size is substituted to u32 at the call site.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            memory heap: Memory where { Size = u32 };
            fn read<M: Memory>(arr: M::&[i32; 4], i: M::Size) -> i32 {
                arr[i]
            }
            fn caller(arr: heap::&[i32; 4], i: u32) -> i32 {
                read(arr, i)
            }
        "},
		&[],
	);
	no_errors(&case);
}

// ── generic trait bound checking
// ─────────────────────────────────────────────────────────

#[test]
fn test_generic_call_with_satisfying_type_is_ok() {
	let case = TestCase::new(indoc! {"
        trait UnsignedInteger {}
        impl UnsignedInteger for u32 {}
        fn test<U: UnsignedInteger>(u: U) {}
        fn main() { test(42 as u32); }
        export { main }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.severity == codespan_reporting::diagnostic::Severity::Error
		})
		.collect();
	assert!(
		errors.is_empty(),
		"expected no errors when calling test() with u32 (implements UnsignedInteger): {:?}",
		errors
	);
}

#[test]
fn test_generic_call_turbofish_with_non_satisfying_type_is_error() {
	// `i32` does not implement `UnsignedInt` (only u8/u16/u32/u64 do), so
	// `get_signed::<i32>(...)` should be a trait-bound error — currently
	// `build_generic_call_arguments` only checks typeset bounds on a
	// function's own type params, never `.traits`, so this call is wrongly
	// accepted.
	let case = TestCase::new(indoc! {"
        trait UnsignedInt {
            type Signed: SignedInt where { Unsigned = Self };
        }
        trait SignedInt {
            type Unsigned: UnsignedInt where { Signed = Self };
        }
        impl UnsignedInt for u32 { type Signed = i32; }
        impl SignedInt for i32 { type Unsigned = u32; }
        fn get_signed<T: UnsignedInt>(unsigne: T) -> T::Signed { unreachable }
        fn test() {
            local x = get_signed::<i32>(1);
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound error for `i32` not implementing `UnsignedInt` \
		 (called via turbofish), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_generic_call_inferred_with_non_satisfying_type_is_error() {
	// Same as above but T is inferred from the argument instead of supplied
	// via turbofish — both paths converge on the same unchecked code, so
	// this must fail identically.
	let case = TestCase::new(indoc! {"
        trait UnsignedInt {
            type Signed: SignedInt where { Unsigned = Self };
        }
        trait SignedInt {
            type Unsigned: UnsignedInt where { Signed = Self };
        }
        impl UnsignedInt for u32 { type Signed = i32; }
        impl SignedInt for i32 { type Unsigned = u32; }
        fn get_signed<T: UnsignedInt>(unsigne: T) -> T::Signed { unreachable }
        fn test() {
            local x = get_signed(1 as i32);
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound error for `i32` not implementing `UnsignedInt` \
		 (inferred from argument type), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

// ── enum tests
// ────────────────────────────────────────────────────────────────

#[test]
fn test_enum_variants_are_populated() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            Red = 1,
            Green,
            Blue,
        }
        export {}
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(errors.is_empty(), "expected no errors: {:?}", errors);

	let enum_ = case
		.tir
		.items
		.enums
		.iter()
		.find(|e| case.graph.interner.resolve(e.name.inner) == Some("Color"))
		.expect("Color enum not found");

	assert_eq!(enum_.variants.len(), 3, "expected 3 variants");
	assert!(enum_.variant_lookup.len() == 3);

	let red_idx = *enum_.variant_lookup.values().min().unwrap();
	let red = &enum_.variants[usize::from(red_idx)];
	assert_eq!(red.const_value, Some(ConstValue::Int(1)));

	let green = &enum_.variants[1];
	assert_eq!(green.const_value, Some(ConstValue::Int(2)));

	let blue = &enum_.variants[2];
	assert_eq!(blue.const_value, Some(ConstValue::Int(3)));
}

#[test]
fn test_enum_variants_after_anchor_auto_increment() {
	// Only the first variant needs an explicit value — every variant
	// after it (`East`/`South`/`West`) may still omit one, auto-
	// incrementing from `North`'s explicit `0`.
	let case = TestCase::new(indoc! {"
        enum Direction: u32 {
            North = 0,
            East,
            South,
            West,
        }
        export {}
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(errors.is_empty(), "expected no errors: {:?}", errors);

	let enum_ = case
		.tir
		.items
		.enums
		.iter()
		.find(|e| {
			case.graph.interner.resolve(e.name.inner) == Some("Direction")
		})
		.expect("Direction enum not found");

	assert_eq!(enum_.variants.len(), 4);
	for (i, variant) in enum_.variants.iter().enumerate() {
		assert_eq!(
			variant.const_value,
			Some(ConstValue::Int(i as i64)),
			"variant {} should have value {}",
			i,
			i
		);
	}
}

#[test]
fn test_enum_variant_access_resolves() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            Red = 1,
            Green,
            Blue,
        }
        fn get_red() -> Color {
            Color::Red
        }
        export { get_red }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"expected no errors accessing Color::Red: {:?}",
		errors
	);
}

#[test]
fn test_enum_comparison() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            Red = 1,
            Green,
            Blue,
        }
        fn is_red(c: Color) -> bool {
            c == Color::Red
        }
        export { is_red }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"expected no errors comparing enum values: {:?}",
		errors
	);
}

#[test]
fn test_enum_missing_repr_is_error() {
	let case = TestCase::new(indoc! {"
        enum Color {
            Red,
            Green,
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::MissingEnumRepr),
		"expected E1036 (MissingEnumRepr), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_missing_repr_with_explicit_values_reports_once() {
	// Explicit variant values used to be type-checked against the repr type
	// even when the repr itself failed to resolve, cascading into a spurious
	// "unable to coerce"/"type annotation required" pair per variant on top
	// of the one real "enum requires a repr type" error.
	let case = TestCase::new(indoc! {"
        enum Direction {
            Right = 0,
            Down = 1,
            Left = 2,
            Up = 3,
        }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert_eq!(
		errors.len(),
		1,
		"expected exactly one diagnostic, got: {:?}",
		errors.iter().map(|d| &d.message).collect::<Vec<_>>()
	);
	assert!(has_error_code(&case.tir, DiagnosticCode::MissingEnumRepr));
}

#[test]
fn test_enum_duplicate_variant_is_error() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            Red = 0,
            Red,
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected E1000 (DuplicateDefinition), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_repr_not_integer_is_error() {
	let case = TestCase::new(indoc! {"
        enum Color: bool {
            Red,
            Green,
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::EnumReprNotInteger),
		"expected E1055 (EnumReprNotInteger), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_constant_folds_arithmetic_for_auto_increment() {
	// Regression test for the motivating bug: `next_auto_value` used to only
	// special-case a bare `Int` literal, so `B` got a stale value instead of the
	// correctly-folded `1 + 1 = 2` from `A`.
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            A = 1 + 1,
            B,
        }
        export {}
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(errors.is_empty(), "{:?}", errors);

	let enum_ = case
		.tir
		.items
		.enums
		.iter()
		.find(|e| case.graph.interner.resolve(e.name.inner) == Some("Color"))
		.expect("Color enum not found");

	assert_eq!(enum_.variants[0].const_value, Some(ConstValue::Int(2)));
	assert_eq!(enum_.variants[1].const_value, Some(ConstValue::Int(3)));
}

#[test]
fn test_enum_negation_folds_for_signed_repr() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            A = -1,
        }
        export {}
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(errors.is_empty(), "{:?}", errors);
	let enum_ = case
		.tir
		.items
		.enums
		.iter()
		.find(|e| case.graph.interner.resolve(e.name.inner) == Some("Color"))
		.expect("Color enum not found");
	assert_eq!(enum_.variants[0].const_value, Some(ConstValue::Int(-1)));
}

#[test]
fn test_enum_implicit_first_variant_no_longer_collides_silently() {
	// This used to be `test_enum_duplicate_value_is_error`: `A` (implicit)
	// silently got the auto-incremented `0`, colliding with `B = 0` —
	// exactly the motivating bug for requiring an explicit anchor
	// (`examples/compare/main.wx`'s real `Ordering` enum hit this exact
	// shape). Under the new rule `A` is rejected outright before any
	// collision has a chance to happen; `EnumDuplicateValue` itself still
	// has coverage via `test_enum_duplicate_value_groups_all_colliding_variants`
	// (fully-explicit variants can still collide with each other).
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            A,
            B = 0,
        }
        export {}
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::EnumVariantRequiresExplicitValue
		),
		"expected E1071 (EnumVariantRequiresExplicitValue) for implicit `A` with nothing to anchor to, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_first_variant_requires_explicit_value() {
	let case = TestCase::new(indoc! {"
        enum E: i32 {
            A,
            B,
        }
        export {}
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::EnumVariantRequiresExplicitValue
		),
		"expected E1071 (EnumVariantRequiresExplicitValue) for `A`, the \
		 first variant, with no explicit value, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_anchored_by_non_adjacent_earlier_variant_is_ok() {
	// `C` is implicit and isn't immediately preceded by an explicit value
	// (`B` is also implicit) — it's anchored transitively by `A`, above
	// both. Auto-increment still counts from `B` (`5`), not from `A`
	// (`0`) — only the *requirement* that an anchor exists looks
	// backward arbitrarily far; the numeric continuation is still always
	// "previous variant's value + 1".
	let case = TestCase::new(indoc! {"
        enum E: i32 {
            A = 0,
            B = 5,
            C,
        }
        export {}
    "});
	no_errors(&case);
	let enum_ = case
		.tir
		.items
		.enums
		.iter()
		.find(|e| case.graph.interner.resolve(e.name.inner) == Some("E"))
		.expect("E enum not found");
	assert_eq!(enum_.variants[2].const_value, Some(ConstValue::Int(6)));
}

#[test]
fn test_enum_variant_with_broken_value_does_not_anchor_later_variants() {
	// A variant with a syntactically-present but unresolvable `=` value
	// does not establish a numeric baseline (there is none to give) —
	// `B` correctly still reports "requires an explicit value" on top of
	// whatever error `A`'s own broken expression produced. This is a
	// straightforward consequence of representing the auto-increment
	// cursor as a single `Option<i64>` (`build_enum`'s `next_auto_value`)
	// rather than tracking "has an anchor" and "next numeric value"
	// separately.
	let case = TestCase::new(indoc! {"
        enum E: i32 {
            A = some_undefined_const,
            B,
        }
        export {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"expected E1007 (UndeclaredIdentifier) for `A`'s broken value, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::EnumVariantRequiresExplicitValue
		),
		"expected E1071 (EnumVariantRequiresExplicitValue) for `B` too, \
		 since `A`'s value never resolved to a usable baseline, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_missing_value_does_not_cascade_when_repr_missing() {
	let case = TestCase::new(indoc! {"
        enum E {
            A,
            B,
        }
        export {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::MissingEnumRepr),
		"expected E1036 (MissingEnumRepr), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert!(
		!has_error_code(
			&case.tir,
			DiagnosticCode::EnumVariantRequiresExplicitValue
		),
		"E1071 (EnumVariantRequiresExplicitValue) must not cascade on top \
		 of an already-broken repr type, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_duplicate_value_groups_all_colliding_variants() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            A = 1,
            B = 1,
            C = 1,
        }
        export {}
    "});
	let dup_diags: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref() == Some(DiagnosticCode::EnumDuplicateValue.code())
		})
		.collect();
	assert_eq!(
		dup_diags.len(),
		1,
		"expected exactly one grouped diagnostic for all three colliding variants, got: {:?}",
		case.tir.diagnostics
	);
	// Primary label (enum name) + one secondary label per colliding variant (3).
	assert_eq!(dup_diags[0].labels.len(), 4);
}

#[test]
fn test_enum_range_check_explicit_literal_is_error() {
	let case = TestCase::new(indoc! {"
        enum Color: i8 {
            A = 300,
        }
        export {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IntegerLiteralOutOfRange),
		"expected E1004 (IntegerLiteralOutOfRange), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_auto_increment_overflow_is_error() {
	let case = TestCase::new(indoc! {"
        enum Color: u8 {
            A = 255,
            B,
        }
        export {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IntegerLiteralOutOfRange),
		"expected E1004 (IntegerLiteralOutOfRange) for auto-increment overflowing u8, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_negative_value_on_unsigned_repr_is_error() {
	let case = TestCase::new(indoc! {"
        enum Color: u32 {
            A = -1,
        }
        export {}
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"expected an error for negative value on unsigned repr, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_type_mismatched_value_is_error() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            A = true,
        }
        export {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (TypeMistmatch), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_not_const_evaluatable_value_is_error() {
	// `%` by a literal `0` builds fine (it's a valid integer expression) but
	// doesn't fold — must not reuse `report_non_constant_global_initializer`'s
	// "add `mut`" wording, since enum variants (like consts) can never be `mut`.
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            A = 32 % 0,
        }
        export {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::NotConstEvaluatable),
		"expected E1057 (NotConstEvaluatable), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_const_not_const_evaluatable_value_is_error() {
	let case = TestCase::new(indoc! {"
        const GRID_W: i32 = 32 % 0;
        export {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::NotConstEvaluatable),
		"expected E1057 (NotConstEvaluatable), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_const_whose_value_failed_to_build_is_still_referenceable() {
	// A const whose *value* fails to build still has to claim its name in
	// Phase 2. It used to bind only on success, so the name stayed
	// `SymbolKind::Pending` forever and the first use of it in value position
	// panicked on the "signature resolved but symbol still pending"
	// unreachable rather than reporting the original error. Checking
	// `std/main.wx` as a binary package reached this through a long cascade;
	// this is the direct form.
	//
	// The unresolved associated item is deliberate — it mirrors the stdlib
	// cascade (`f64::EPSILON`) and is one of the few forms that actually
	// makes `build_const_context_expression` return `Err`. A bare undeclared
	// identifier (`const A: f64 = NOPE;`) still builds *Ok*, as an error
	// expression, and only fails to fold, so it never reaches that branch.
	let case = TestCase::new(indoc! {"
        const A: f64 = f64::NOPE;

        fn f() -> f64 {
            local x = A;
            x
        }

        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"expected E1007 (UndeclaredIdentifier) for the const's own value, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_unused_is_warned() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            Red = 0,
            Green,
        }
        export {}
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedItem.code())
			&& d.message.contains("Color")),
		"expected W1004 for unused enum `Color`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_pub_const_in_inherent_impl_not_warned_unused() {
	// Regression test: `ImplItem::Constant` (unlike `ImplItem::Function`,
	// which already carries `pub_span`) never recorded whether an inherent
	// impl's associated const was declared `pub` — the parser parsed the
	// `pub` keyword via the same shared `parse_impl_member` prefix used for
	// methods, but silently dropped it for consts, and TIR then hardcoded
	// `pub_span: None` when building the `Constant` entry. Since the
	// unused-item check only skips items with `pub_span.is_some()`, every
	// `pub const` inside an `impl` block was wrongly flagged as unused
	// regardless of its actual visibility.
	let case = TestCase::new(indoc! {"
        struct Foo {}
        impl Foo {
            pub const BAR: i32 = 1;
        }
        export {}
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedItem.code())
			&& d.message.contains("BAR")),
		"pub const in an inherent impl block must not be flagged unused, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_private_const_in_inherent_impl_is_warned_unused() {
	// Companion to the test above: confirms the fix respects `pub_span`
	// rather than blanket-suppressing the unused check for every impl
	// const.
	let case = TestCase::new(indoc! {"
        struct Foo {}
        impl Foo {
            const BAR: i32 = 1;
        }
        export {}
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedItem.code())
			&& d.message.contains("BAR")),
		"expected W1004 for unused private const `BAR`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_pub_enum_no_unused_warn() {
	let case = TestCase::new(indoc! {"
        pub enum Color: i32 {
            Red = 0,
            Green,
        }
        export {}
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedItem.code())
			&& d.message.contains("Color")),
		"pub enum should not warn as unused even with no in-package references"
	);
}

#[test]
fn test_enum_variant_unused_is_warned() {
	// The enum itself is used (so it doesn't get the whole-enum warning),
	// but `Green` is never referenced through `Color::Green`.
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            Red = 0,
            Green,
        }
        fn get_red() -> Color {
            Color::Red
        }
        export { get_red }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedEnumVariant.code())
			&& d.message.contains("Green")),
		"expected W1009 for unused variant `Green`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedEnumVariant.code())
			&& d.message.contains("Red")),
		"`Red` is referenced and should not warn"
	);
}

#[test]
fn test_enum_all_variants_used_no_warn() {
	let case = TestCase::new(indoc! {"
        enum Color: i32 {
            Red = 0,
            Green,
        }
        fn both(c: Color) -> bool {
            c == Color::Red || c == Color::Green
        }
        export { both }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedEnumVariant.code())),
		"all variants referenced should not warn, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_two_unused_variants_grouped_without_oxford_comma() {
	let case = TestCase::new(indoc! {"
        enum Direction: i32 {
            Right = 0,
            Down,
            Left,
        }
        fn get_right() -> Direction {
            Direction::Right
        }
        export { get_right }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedEnumVariant.code())
			&& d.message == "variants `Down` and `Left` are never constructed"),
		"expected exact grouped message for 2 unused variants, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_five_unused_variants_grouped_with_oxford_comma() {
	let case = TestCase::new(indoc! {"
        enum Direction: i32 {
            Right = 0,
            Down,
            Left,
            Up,
            Boo,
            Bar,
        }
        fn get_right() -> Direction {
            Direction::Right
        }
        export { get_right }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedEnumVariant.code())
			&& d.message
				== "variants `Down`, `Left`, `Up`, `Boo`, and `Bar` are never constructed"),
		"expected exact grouped message for 5 unused variants, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_enum_six_unused_variants_collapses_to_generic_message() {
	let case = TestCase::new(indoc! {"
        enum Direction: i32 {
            Right = 0,
            Down,
            Left,
            Up,
            Boo,
            Bar,
            Baz,
        }
        fn get_right() -> Direction {
            Direction::Right
        }
        export { get_right }
    "});
	let matches: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref() == Some(DiagnosticCode::UnusedEnumVariant.code())
		})
		.collect();
	assert_eq!(
		matches.len(),
		1,
		"expected exactly one grouped diagnostic, got: {:?}",
		matches
	);
	assert_eq!(
		matches[0].message,
		"multiple variants are never constructed"
	);
	assert_eq!(
		matches[0].labels.len(),
		6,
		"expected one label per unused variant"
	);
}

#[test]
fn test_tagged_items_registered_for_every_taggable_item_kind() {
	let case = TestCase::new(indoc! {"
        #[tag = \"tagged_fn\"]
        fn f() -> i32 { 1 }
        #[tag = \"tagged_struct\"]
        struct S { x: i32 }
        #[tag = \"tagged_const\"]
        const C: i32 = 1;
        #[tag = \"tagged_alias\"]
        type A = i32;
        #[tag = \"tagged_global\"]
        global mut G: i32 = 0;
        #[tag = \"tagged_enum\"]
        enum E: i32 { A = 1 }
        #[tag = \"tagged_memory\"]
        memory M: Memory where { Size = u32 };
        #[tag = \"tagged_trait\"]
        trait T { fn m(self) -> i32; }
        export { f }
    "});
	// Warnings are expected here (nothing reads these items); errors are not.
	let errors = error_messages(&case.tir);
	assert!(errors.is_empty(), "unexpected errors: {errors:#?}");
	for tag in [
		"tagged_fn",
		"tagged_struct",
		"tagged_const",
		"tagged_alias",
		"tagged_global",
		"tagged_enum",
		"tagged_memory",
		"tagged_trait",
	] {
		let symbol = case
			.graph
			.interner
			.get(tag)
			.unwrap_or_else(|| panic!("`{tag}` was never interned"));
		assert!(
			case.tir.items.tagged_items.contains_key(&symbol),
			"`#[tag = \"{tag}\"]` was not registered in `tagged_items`"
		);
	}
}

#[test]
fn test_tagged_items_registered() {
	let case = TestCase::new(indoc! {"
        #[tag = \"my_trait\"]
        pub trait MyTrait {}

        #[tag = \"my_fn\"]
        pub fn my_function() {}
    "});
	assert!(case.tir.diagnostics.is_empty());
	let trait_key = case
		.graph
		.interner
		.get("my_trait")
		.expect("tag key not interned");
	let fn_key = case
		.graph
		.interner
		.get("my_fn")
		.expect("tag key not interned");
	let fn_def_id = *case
		.tir
		.items
		.tagged_items
		.get(&fn_key)
		.expect("fn tagged item not registered");
	assert!(
		case.tir.items.tagged_items.contains_key(&trait_key),
		"trait tagged item not registered"
	);
	assert!(case.tir.items.function_index(fn_def_id).is_some());
}

#[test]
fn test_tagged_items_registered_for_trait_members() {
	let case = TestCase::new(indoc! {"
        pub trait MyTrait {
            #[tag = \"my_assoc_const\"]
            const FOO: i32;
            #[tag = \"my_assoc_type\"]
            type Bar;
        }
    "});
	assert!(case.tir.diagnostics.is_empty());
	let const_key = case
		.graph
		.interner
		.get("my_assoc_const")
		.expect("tag key not interned");
	let type_key = case
		.graph
		.interner
		.get("my_assoc_type")
		.expect("tag key not interned");
	assert!(
		case.tir.items.tagged_items.contains_key(&const_key),
		"assoc const tagged item not registered"
	);
	assert!(
		case.tir.items.tagged_items.contains_key(&type_key),
		"assoc type tagged item not registered"
	);
}

#[test]
fn test_generic_impl_block_registers_and_dispatches() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        fn get_len(s: heap::&[u8]) -> u32 {
            s.len()
        }

        export { get_len }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_generic_impl_bare_type_param_is_error() {
	let case = TestCase::new(indoc! {"
        impl<T> T {
            pub fn nope(self) {}
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::InvalidImplTarget),
		"expected InvalidImplTarget (no nominal type) for bare type param impl, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_slice_range_full_is_ok() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        fn f(s: heap::&[u8]) -> heap::&[u8] {
            s[..]
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_slice_range_with_bounds_is_ok() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        fn f(s: heap::&[u8], i: u32, n: u32) -> heap::&[u8] {
            s[i..n]
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_slice_range_on_array_is_ok() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        fn f(arr: heap::&[u8; 4]) -> heap::&[u8] {
            arr[1..3]
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_slice_range_on_non_indexable_is_error() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        fn f(x: i32) -> heap::&[i32] {
            x[..]
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::IndexOnNonIndexable),
		"expected E1042 (IndexOnNonIndexable) for range-index on i32, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

// ── global initializers
// ──────────────────────────────────────────────────────────

#[test]
fn test_global_init_function_call_resolves() {
	let case = TestCase::new(indoc! {"
        fn compute() -> i32 { 42 as i32 }
        global mut result: i32 = compute()
        export { result }
    "});
	no_errors(&case);
	assert!(case.tir.items.globals[0].value.is_some());
}

#[test]
fn test_global_init_block_with_locals_resolves() {
	let case = TestCase::new(indoc! {"
        global mut x: i32 = {
            local a = 3 as i32;
            local b = 4 as i32;
            a + b
        }
        export { x }
    "});
	no_errors(&case);
	assert!(case.tir.items.globals[0].value.is_some());
}

#[test]
fn test_global_init_arithmetic_resolves() {
	let case = TestCase::new(indoc! {"
        global mut x: i32 = 2 + 3
        export { x }
    "});
	no_errors(&case);
	assert!(case.tir.items.globals[0].value.is_some());
}

#[test]
fn test_global_init_type_mismatch_reports_error() {
	let case = TestCase::new(indoc! {"
        global mut x: i32 = true
        export { x }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

#[test]
fn test_global_init_cross_global_reference_resolves() {
	// g2's initializer reads g1 — g1 is in scope, so this type-checks cleanly.
	// At runtime g1 is already set before g2 (declaration order), so g2 = 10 + 1.
	let case = TestCase::new(indoc! {"
        global mut g1: i32 = 10
        global mut g2: i32 = g1 + 1
        export { g1, g2 }
    "});
	no_errors(&case);
	assert_eq!(case.tir.items.globals.len(), 2);
	assert!(case.tir.items.globals.iter().all(|g| g.value.is_some()));
}

#[test]
fn test_global_init_reverse_cross_reference_resolves() {
	// g2 is declared before g1, so when g2's initializer reads g1 the value
	// will be the WASM zero-default (g1 hasn't been set yet).
	// This is defined behaviour: type-checks clean, init order is declaration order.
	let case = TestCase::new(indoc! {"
        global mut g2: i32 = g1 + 1
        global mut g1: i32 = 10
        export { g1, g2 }
    "});
	no_errors(&case);
}

#[test]
fn test_global_init_if_expression_resolves() {
	let case = TestCase::new(indoc! {"
        fn flag() -> bool { true }
        global mut x: i32 = if flag() { 1 as i32 } else { 2 as i32 }
        export { x }
    "});
	no_errors(&case);
	assert!(case.tir.items.globals[0].value.is_some());
}

#[test]
fn test_global_initialized_to_data_end_tir() {
	let case = TestCase::new(indoc! {"
        #[memory_limits(min_pages = 1)]
        memory heap: Memory where { Size = u32 };
        global mut bump: heap::*u8 = heap::DATA_END;
        export { heap }
    "});
	// Only warning expected: "never used" (no functions read bump in this test).
	assert!(
		case.tir
			.diagnostics
			.iter()
			.all(|d| d.severity
				!= codespan_reporting::diagnostic::Severity::Error)
	);
	assert_eq!(case.tir.items.globals.len(), 1);
}

#[test]
fn test_typeset_definition_registers_in_tir() {
	let case = TestCase::new(indoc! {"
        typeset Numbers { u8, i8, u16, i16, u32, i32, u64, i64 }
        fn identity<N: Numbers>(x: N) -> N { x }
        fn use_it() -> i32 { identity(42 as i32) }
        export { use_it }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
	// At least stdlib Integer + user Numbers typesets are registered
	assert!(!case.tir.items.typesets.is_empty());
	// The user-defined identity function has one type param with one typeset bound
	let identity = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| {
			case.graph.interner.resolve(f.name.inner) == Some("identity")
				&& f.type_params.iter().any(|tp| tp.bounds.typeset.is_some())
		})
		.expect("no identity function with typeset bounds found");
	assert_eq!(identity.type_params.len(), 1);
	assert!(identity.type_params[0].bounds.typeset.is_some());
}

#[test]
fn test_typeset_bound_violation_reports_error() {
	let case = TestCase::new(indoc! {"
        typeset Numbers { u8, i8, u16, i16, u32, i32, u64, i64 }
        fn identity<N: Numbers>(x: N) -> N { x }
        fn main() -> f32 {
            identity(1.0 as f32)
        }
        export { main }
    "});
	assert!(case.tir.diagnostics.iter().any(|d| d.code.as_deref()
		== Some(DiagnosticCode::TypesetBoundViolation.code())));
}

#[test]
fn test_typeset_member_not_integer_reports_error() {
	let case = TestCase::new(indoc! {"
        typeset BadSet { u32, f32 }
        export { }
    "});
	assert!(case.tir.diagnostics.iter().any(|d| d.code.as_deref()
		== Some(DiagnosticCode::TypesetMemberNotInteger.code())));
}

#[test]
fn test_stdlib_integer_typeset_exists() {
	let case = TestCase::new(indoc! {"
        fn double<N: Integer>(x: N) -> N { x }
        fn use_it() -> i32 { double(21 as i32) }
        export { use_it }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_typeset_intersection_range_in_bounds() {
	// Integer intersection is [0, 127]; literals within that range are accepted
	let case = TestCase::new(indoc! {"
        fn make<N: Integer>(x: N) -> N { x }
        fn use_zero() -> i32 { make(0 as i32) }
        fn use_mid() -> u8 { make(100 as u8) }
        fn use_max() -> i8 { make(127 as i8) }
        export { use_zero, use_mid, use_max }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_typeset_intersection_range_literal_in_local() {
	// 0 and 100 are within Integer intersection [0, 127]; locals typed as TypeParam should be fine
	let case = TestCase::new(indoc! {"
        fn with_bounds<N: Integer>(x: N) -> N {
            local _lo: N = 0;
            local _hi: N = 100;
            x
        }
        fn use_it() -> i32 { with_bounds(50 as i32) }
        export { use_it }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.severity == codespan_reporting::diagnostic::Severity::Error
		})
		.collect();
	assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
}

#[test]
fn test_typeset_intersection_range_out_of_bounds_reports_error() {
	// Integer intersection max is 127; 200 is outside the safe range
	// This fires when assigning an untyped literal to a local of TypeParam type
	let case = TestCase::new(indoc! {"
        fn test<N: Integer>() {
            local x: N = 200;
        }
        fn use_it() { test() }
        export { use_it }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::TypesetBoundViolation.code())),
		"expected E1047, got: {:?}",
		case.tir.diagnostics
	);
}

// ── operators on typeset-bounded type params ─────────────────────────────
//
// A bare `T: Size`-style typeset bound and a typeset-bounded associated
// type (`Mem::Size`, bounded by `PointerSize`) are both "this will concretize
// to one of a fixed set of integer primitives" — `resolve_bounded_operator_method`
// trusts a typeset bound for any operator trait the same way `AssocTypeProjection`
// already is, so both spellings should support arithmetic/bitwise operators and
// their compound-assignment forms identically.

#[test]
fn test_typeset_bounded_type_param_supports_arithmetic_operator() {
	let case = TestCase::new(indoc! {"
        fn add<N: Integer>(a: N, b: N) -> N { a + b }
        fn use_it() -> i32 { add(1 as i32, 2 as i32) }
        export { use_it }
    "});
	no_errors(&case);
}

#[test]
fn test_typeset_bounded_type_param_supports_bitwise_operator() {
	let case = TestCase::new(indoc! {"
        fn and<N: Integer>(a: N, b: N) -> N { a & b }
        fn use_it() -> i32 { and(6 as i32, 3 as i32) }
        export { use_it }
    "});
	no_errors(&case);
}

#[test]
fn test_typeset_bounded_type_param_supports_compound_assignment() {
	let case = TestCase::new(indoc! {"
        fn add_assign<N: Integer>(a: N, b: N) -> N {
            local mut x: N = a;
            x += b;
            x
        }
        fn use_it() -> i32 { add_assign(1 as i32, 2 as i32) }
        export { use_it }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_slice_index_coerces_to_pointer_size() {
	// Indexing `M::&[T]` needs an `M::Size`, whose typeset bound is
	// `PointerSize { u32, u64 }`. An untyped literal must coerce to it, and
	// the range it's checked against is the *intersection* of the typeset's
	// members — [0, u32::MAX] — not `u64`'s. So both ends of that range are
	// valid, and so is an index already of type `M::Size`.
	let case = TestCase::new(indoc! {"
        fn _low<M: Memory, T>(s: M::&[T]) -> T { s[0] }
        fn _high<M: Memory, T>(s: M::&[T]) -> T { s[4294967295] }
        fn _exact<M: Memory, T>(s: M::&[T], i: M::Size) -> T { s[i] }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_generic_slice_index_rejects_out_of_range_literal() {
	// One past the intersection range's top. Fits `u64`, so it is only
	// rejectable by checking the typeset as a whole.
	let case = TestCase::new(indoc! {"
        fn _f<M: Memory, T>(s: M::&[T]) -> T { s[4294967296] }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypesetBoundViolation),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_generic_slice_index_rejects_negative_literal() {
	// Every `PointerSize` member is unsigned, so there is no member for a
	// negative literal to coerce to at all.
	let case = TestCase::new(indoc! {"
        fn _f<M: Memory, T>(s: M::&[T]) -> T { s[-1] }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnableToCoerce),
		"{:?}",
		case.tir.diagnostics
	);
}

// ── type-position namespace resolution ─────────────────────────────────────

#[test]
fn test_type_position_inline_module_registers_module_access() {
	// Accessing a type via an inline module path should register an LSP access
	// on the module declaration.
	let case = TestCase::new(indoc! {"
        mod math {
            pub struct Vec2 { pub x: i32, pub y: i32 }
        }

        fn f(v: math::Vec2) { }

        export { f }
    "});
	no_errors(&case);
	assert!(
		case.tir
			.modules
			.namespaces
			.iter()
			.any(|ns| !ns.accesses.is_empty()),
		"expected at least one access registered on a namespace, got: {:?}",
		case.tir
			.modules
			.namespaces
			.iter()
			.map(|ns| ns.accesses.len())
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_type_position_three_segment_inline_module_path() {
	// `outer::inner::Point` — three-segment type path through two nested inline
	// modules. Exercises the intermediate loop in resolve_type.
	let case = TestCase::new(indoc! {"
        mod outer {
            pub mod inner {
                pub struct Point { pub x: i32, pub y: i32 }
            }
        }

        fn f(p: outer::inner::Point) { }

        export { f }
    "});
	no_errors(&case);
}

#[test]
fn test_module_colliding_with_implicit_std_dependency_is_duplicate_definition()
{
	// Every package implicitly depends on `std`, materialized as a `Module`
	// symbol in the root package's own namespace before any file is
	// scanned. A user `mod std { }` declaration must not silently merge
	// its contents into the real stdlib's namespace — it should be reported
	// as a same-scope duplicate definition, same as any other name clash.
	let case = TestCase::new(indoc! {"
        mod std {
            pub fn my_helper() -> i32 { 42 }
        }

        fn main() -> i32 { std::my_helper() }

        export { main }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected E1000 (DuplicateDefinition) for `mod std` colliding \
		 with the implicit std dependency, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_file_declared_module_colliding_with_implicit_std_dependency_is_duplicate_definition()
 {
	// Same collision as above, but through the file-pointing form
	// (`mod std;`, resolved by Phase 1a directly from vfs's
	// `SourceModule` tree) rather than an inline block. Regression test:
	// this form used to silently steal the `std` binding with zero
	// diagnostic, since Phase 1a's `create_module_namespace` had no
	// collision check at all — `use std::*;` (and every other `std::x`
	// reference) would then resolve against the user's own file instead
	// of the real stdlib, producing a cascade of unrelated "undeclared
	// type"/"cannot coerce" errors instead of one clear diagnostic.
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod std;
            fn main() -> i32 { 1 }
            export { main }
        "},
		&[("src/std.wx", "pub fn my_helper() -> i32 { 42 }")],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected E1000 (DuplicateDefinition) for file-declared `mod \
		 std;` colliding with the implicit std dependency, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_import_alias_colliding_with_implicit_std_dependency_is_duplicate_definition()
 {
	// The third name-owning mechanism alongside dependencies and
	// `mod`: an `import "..." as std { }` block must not silently
	// steal the `std` binding either.
	let case = TestCase::new(indoc! {"
        import \"env\" as std {
            fn foo();
        }

        fn main() -> i32 { 1 }

        export { main }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected E1000 (DuplicateDefinition) for `import ... as std` \
		 colliding with the implicit std dependency, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_type_position_undeclared_in_module_path_is_error() {
	// `shapes::NonExistent` — the module exists but the type does not.
	// Should produce exactly one error (not a cascade) and not panic.
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod shapes;

            fn f(x: shapes::NonExistent) { }

            export { f }
        "},
		&[("src/shapes.wx", "pub struct Point { pub x: i32 }")],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected E1021 (UndeclaredType) for missing type in module path, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_sibling_modules_get_independent_same_named_children() {
	// `a` and `b` are siblings, both declaring `mod shared;`. Each
	// module's own children live under a directory named after *that
	// module* (`src/a/`, `src/b/`) regardless of whether the module itself
	// was found via the sibling-file or `mod.wx` form — so these resolve
	// to two entirely independent files, not a collision (vfs/mod.rs's
	// `owned_dir` accumulation). Confirmed by giving each `shared` a
	// different return value and checking both come through unmodified.
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod a;
            mod b;
            fn main() -> i32 { a::use_a() + b::use_b() }
            export { main }
        "},
		&[
			(
				"src/a.wx",
				"mod shared;\npub fn use_a() -> i32 { shared::x() }",
			),
			("src/a/shared.wx", "pub fn x() -> i32 { 1 }"),
			(
				"src/b.wx",
				"mod shared;\npub fn use_b() -> i32 { shared::x() }",
			),
			("src/b/shared.wx", "pub fn x() -> i32 { 2 }"),
		],
	);
	no_errors(&case);
}

#[test]
fn test_type_position_non_namespace_as_intermediate_is_error() {
	// `i32::Foo` — `i32` is a primitive, not a module; looking up an associated
	// type that doesn't exist should produce E1021 (UndeclaredType).
	let case = TestCase::new(indoc! {"
        fn f(x: i32::Foo) { }

        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected E1021 (UndeclaredType) when a primitive is used as a type namespace, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn test_struct_init_three_segment_inline_module_path() {
	// `outer::inner::Point::{ x: 1, y: 2 }` — struct literal via a 3-segment
	// inline module path. Exercises the namespace_span tracking loop added to
	// build_struct_init_expression.
	let case = TestCase::new(indoc! {"
        mod outer {
            pub mod inner {
                pub struct Point { pub x: i32, pub y: i32 }
            }
        }

        fn make() -> outer::inner::Point {
            outer::inner::Point::{ x: 1, y: 2 }
        }

        export { make }
    "});
	no_errors(&case);
}

#[test]
fn test_struct_init_undeclared_type_in_module_path_is_error() {
	// `shapes::Ghost::{ }` — the module exists but `Ghost` is not defined there.
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod shapes;

            fn f() -> shapes::Ghost {
                shapes::Ghost::{ }
            }

            export { f }
        "},
		&[("src/shapes.wx", "pub struct Point { pub x: i32 }")],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected E1021 (UndeclaredType) for missing struct in module path, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

/// `@size_of::<T, M>` returns `M::Size` projected from @size_of's own param list
/// (where M is at index 1).  The struct field `size: M::Size` is projected from
/// Layout's param list (where M is at index 0).  After substitution both must
/// normalise to the same TypeIndex so the struct init type-checks cleanly.
#[test]
fn test_assoc_type_projection_normalised_across_functions() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        struct Layout<M: Memory> {
            pub size: M::Size,
            pub align: M::Size,
        }

        impl<M: Memory> Layout<M> {
            pub fn of<T>() -> Layout<M> {
                Layout::{ size: size_of::<T, M>(), align: align_of::<T, M>() }
            }

            pub fn array<T>(count: M::Size) -> Layout<M> {
                Layout::{ size: size_of::<T, M>() * count, align: align_of::<T, M>() }
            }
        }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_assoc_type_as_memory_tag_in_trait() {
	// `Self::M` where M: Memory should be valid as a memory tag in pointer types
	// inside a trait definition.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        struct Layout<M: Memory> {
            size: M::Size,
            align: M::Size,
        }

        trait Allocator {
            type M: Memory;

            fn alloc(self: *Self, layout: Layout<Self::M>) -> Self::M::*u8;

            fn dealloc(self: *Self, ptr: Self::M::*u8, layout: Layout<Self::M>);
        }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_resolves_in_trait_default_body() {
	// Regression: `Self::M` resolved fine in a trait method *signature* (see
	// `test_assoc_type_as_memory_tag_in_trait` above) but failed with
	// "undeclared type" inside a default *body*. Two bugs combined to cause
	// it: (1) `ensure_body`'s `TraitFunction` arm built `Self` as
	// `TypeParam { owner: Function(fi), .. }` instead of
	// `TypeParam { owner: Trait(trait_index), .. }` like signature
	// resolution does, so it didn't carry the implicit `Self: <trait>` bound
	// needed to look up associated types; (2) even after fixing that,
	// `build_path_expression`'s turbofish-on-first-segment handling (e.g.
	// `Layout::<Self::M>`) resolved its type args with `scope: None`,
	// discarding the enclosing function's generic scope entirely.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        trait Allocator {
            type M: Memory;

            fn reserve(self: Self::M::*Self, layout: Layout<Self::M>) -> Self::M::*u8;

            #[inline]
            fn alloc_slice<T>(self: Self::M::*Self, count: Self::M::Size) -> Self::M::*u8 {
                local layout = Layout::<Self::M>::array::<T>(count);
                self.reserve(layout)
            }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_call_result_type_infers_assoc_type_arg() {
	// Regression: `self.reserve(Layout::of::<T>())` (no `::<M>` turbofish on
	// `Layout::of`, since only `T` is explicit) failed with "cannot infer
	// type for type parameter `M`" even though `M` is fully determined by
	// context — `reserve`'s param type is `Layout<Self::M>`. Both
	// `build_call_expression` and `build_method_call_expression`'s
	// generic-call branches built every argument with a flat
	// `expected_type: TypeIndex::INFER`, deferring all inference to a
	// post-hoc check against each argument's *already-built* type. That
	// works when an argument is self-determining, but `Layout::of::<T>()`
	// takes no value arguments — the call's own expected result type is the
	// *only* way to learn `M` — so it was never inferred, and the call fell
	// back to displaying its uninstantiated `Layout<M>`, producing a
	// spurious second "type mismatch" against the expected `Layout<Self::M>`.
	// Fixed by seeding `type_args` from the call's own expected type
	// *before* building arguments, so nested generic calls can use it.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        trait Allocator {
            type M: Memory;

            fn reserve(self: Self::M::*Self, layout: Layout<Self::M>) -> Self::M::*u8;

            #[inline]
            fn alloc<T>(self: Self::M::*Self) -> Self::M::*T {
                self.reserve(Layout::of::<T>()) as _
            }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_function_call_result_type_infers_nested_call_arg() {
	// Same class of bug as `test_generic_call_result_type_infers_assoc_type_arg`,
	// isolated to a plain function call (no traits/methods/assoc types) to
	// show it's a general gap in generic-call argument building, not
	// something specific to associated-type projections.
	let case = TestCase::new(indoc! {"
        struct Wrapper<T> { x: T }
        impl <T> Wrapper<T> {
            pub fn make() -> Self { unreachable }
        }
        fn take<T>(w: Wrapper<T>) -> T { unreachable }
        fn use_it() -> i32 {
            take(Wrapper::make())
        }
        export { use_it }
    "});
	no_errors(&case);
}

#[test]
fn test_assoc_type_memory_bound_satisfied_by_memory_decl() {
	// `impl Allocator for BumpAllocator { type M = heap; }` — concrete memory
	// satisfies the `M: Memory` bound on the associated type.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        struct Layout<M: Memory> {
            size: M::Size,
            align: M::Size,
        }

        trait Allocator {
            type M: Memory;

            fn alloc(self: *Self, layout: Layout<Self::M>) -> Self::M::*u8;
        }

        struct BumpAllocator {}

        impl Allocator for BumpAllocator {
            type M = heap;

            fn alloc(self: *Self, layout: Layout<Self::M>) -> Self::M::*u8 {
                unreachable
            }
        }
    "});
	no_errors(&case);
}

#[test]
fn test_memory_records_access_in_type_position() {
	// Regression test: `memory` declarations had no `accesses` field at all,
	// so referencing `heap` as a type (here, `type M = heap;`) never recorded
	// anything — hover/go-to-definition on `heap` had nothing to find.
	let source = indoc! {"
        memory heap: Memory where { Size = u32 };

        trait Allocator {
            type M: Memory;
        }

        struct BumpAllocator {}

        impl Allocator for BumpAllocator {
            type M = heap;
        }
    "};
	let case = TestCase::new(source);
	no_errors(&case);

	let memory = case
		.tir
		.items
		.memories
		.iter()
		.find(|m| case.graph.interner.resolve(m.name.inner) == Some("heap"))
		.expect("memory 'heap' not found");

	let heap_in_type_m_offset =
		source.find("type M = heap;").unwrap() + "type M = ".len();
	assert!(
		memory
			.accesses
			.iter()
			.any(|access| access.span.start == heap_in_type_m_offset as u32),
		"expected an access recorded at `type M = heap;`'s `heap` (offset {heap_in_type_m_offset}), got: {:?}",
		memory.accesses
	);
}

// ── loop type inference ───────────────────────────────────────────────────────

#[test]
fn test_infinite_loop_has_never_type() {
	// `loop {}` with no break coerces to any return type — proves Never type.
	let case = TestCase::new(indoc! {"
        pub fn f() -> i32 { loop {} }
    "});
	no_errors(&case);
}

#[test]
fn test_loop_with_break_has_unit_type() {
	// bare `break` makes the loop yield Unit; returning it from a () fn is fine.
	let case = TestCase::new(indoc! {"
        pub fn f() { loop { break; } }
    "});
	no_errors(&case);
}

#[test]
fn test_loop_with_break_value_has_that_type() {
	// `break 42` makes the loop yield i32.
	let case = TestCase::new(indoc! {"
        pub fn f() -> i32 { loop { break 42; } }
    "});
	no_errors(&case);
}

#[test]
fn test_loop_with_continue_only_has_never_type() {
	// `continue` does not count as a break — loop still has Never type.
	let case = TestCase::new(indoc! {"
        pub fn f() -> i32 { loop { continue; } }
    "});
	no_errors(&case);
}

#[test]
fn test_break_outside_of_loop_reports_diagnostic() {
	let case = TestCase::new(indoc! {"
        pub fn f() { break; }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::BreakOutsideOfLoop),
		"expected E1012 (BreakOutsideOfLoop), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_continue_outside_of_loop_reports_diagnostic() {
	let case = TestCase::new(indoc! {"
        pub fn f() { continue; }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ContinueOutsideOfLoop),
		"expected E1054 (ContinueOutsideOfLoop), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_break_with_undeclared_label_reports_only_that_diagnostic() {
	// No loop anywhere in `f`, so the label-less "outside of loop" check
	// must not also fire alongside the undeclared-label error.
	let case = TestCase::new(indoc! {"
        pub fn f() { break :outer; }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredLabel),
		"expected E1011 (UndeclaredLabel), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert_eq!(
		case.tir.diagnostics.len(),
		1,
		"expected only UndeclaredLabel, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_continue_with_undeclared_label_reports_only_that_diagnostic() {
	// Same as above but for `continue`.
	let case = TestCase::new(indoc! {"
        pub fn f() { continue :outer; }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredLabel),
		"expected E1011 (UndeclaredLabel), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	assert_eq!(
		case.tir.diagnostics.len(),
		1,
		"expected only UndeclaredLabel, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_unused_label_reports_diagnostic() {
	// `outer` is declared but never referenced by a `break`/`continue`.
	let case = TestCase::new(indoc! {"
        pub fn f() {
            outer: loop {
                break;
            }
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnusedLabel),
		"expected W1008 (UnusedLabel), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_used_label_reports_no_unused_label_diagnostic() {
	// `outer` is referenced by `break :outer;`, so it must not be flagged.
	let case = TestCase::new(indoc! {"
        pub fn f() {
            outer: loop {
                break :outer;
            }
        }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::UnusedLabel),
		"did not expect W1008 (UnusedLabel), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── supertrait constraint tests ───────────────────────────────────────────────

// Known limitation: passing an *abstract* type parameter (not yet a concrete
// type) through to a second generic call whose bound is one of the first
// bound's supertraits is not yet recognized as satisfying that bound — the
// call-site trait-bound check (`build_generic_call_arguments`, via
// `TIR::type_implements_trait`) only looks at a TypeParam's own *directly*
// declared bounds (`abstract_type_bounds`), not its supertraits.
//
// This is narrower than "supertraits don't work": a *concrete* type is
// unaffected, since `check_trait_conformance` already requires every impl to
// also directly implement all of its trait's supertraits (`Violation::
// MissingSupertrait`, builder.rs) — so `find_trait_impl(SomeStruct, A)`
// already succeeds whenever `SomeStruct` implements a subtrait of `A`. The
// gap only bites for an in-progress generic body forwarding its own
// still-abstract type param into another bounded generic call, as in both
// tests below.
//
// To fix this, `TIR::type_implements_trait`'s abstract branch would need to
// walk supertraits of a TypeParam's declared bounds, transitively. That
// requires supertrait-cycle detection first — `trait A: B {} trait B: A {}`
// is not currently rejected anywhere (`resolve_identifier_as_bound`,
// builder.rs, resolves a supertrait purely to its `TraitIndex` without
// forcing the supertrait's own signature to resolve first, so no existing
// re-entrancy guard — e.g. `ensure_signature`'s `sig_state` — ever sees this
// case) — an unbounded transitive walk over user-controlled trait
// declarations could recurse forever. The likely fix: make supertrait
// resolution (in the `AstNodeRef::Trait` arm of `ensure_signature`,
// builder.rs) force-resolve each supertrait's own signature first (e.g. via
// `ensure_signature` on the supertrait's `DefId`), so `sig_state`'s existing
// `ComputeState::InProgress` re-entrancy check naturally detects the cycle —
// matching rustc's E0391 — and report a dedicated diagnostic there, rather
// than adding an ad hoc cycle guard inside the trait-bound-checking walk
// itself.
#[test]
#[ignore = "supertrait transitivity through an abstract type param isn't implemented yet — see comment above"]
fn test_supertrait_single_level_satisfies_bound() {
	// T: B where B: A — passing T to a fn requiring A should type-check.
	let case = TestCase::new(indoc! {"
        trait A {}
        trait B: A {}
        fn requires_a<T: A>(x: T) {}
        fn call_with_b<T: B>(x: T) { requires_a(x); }
        export {}
    "});
	no_errors(&case);
}

#[test]
#[ignore = "supertrait transitivity through an abstract type param isn't implemented yet — see comment above"]
fn test_supertrait_two_levels_deep_satisfies_bound() {
	// T: C where C: B and B: A — passing T to a fn requiring A should type-check.
	let case = TestCase::new(indoc! {"
        trait A {}
        trait B: A {}
        trait C: B {}
        fn requires_a<T: A>(x: T) {}
        fn call_with_c<T: C>(x: T) { requires_a(x); }
        export {}
    "});
	no_errors(&case);
}

#[test]
fn test_nested_assoc_type_projection_resolves() {
	// `A::M::Size` — associated type of an associated type — must resolve
	// without error when `type M: Memory` is declared in the Allocator trait.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        trait Allocator {
            type M: Memory;
            fn alloc(mut self, size: Self::M::Size) -> Self::M::*u8;
        }
        struct Vec<T, A: Allocator> {
            len: A::M::Size,
        }
        export {}
    "});
	no_errors(&case);
}

#[test]
fn test_phantom_type_param_as_infer_is_error() {
	// T does not appear in the return type of `phantom`, so `_` for T
	// cannot be verified by the result-type check — it should still error.
	let case = TestCase::new(indoc! {"
        fn phantom<T>() -> i32 { 0 }
        fn f() -> i32 { phantom::<_>() }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::TypeAnnotationRequired
	));
}

#[test]
fn test_phantom_inherited_type_param_reports_error_not_panic() {
	// Regression: the phantom-param check indexed
	// `functions[func_index].type_params[i]` directly, which only holds a
	// function's own explicit type params — not ones inherited from a parent
	// impl block. When the phantom slot was an *inherited* param (like `M`
	// here, inherited from `impl<M> Holder<M>` since `get` declares no type
	// params of its own), `i` pointed past the end of that empty vec and
	// panicked ("index out of bounds: the len is 0 but the index is 0")
	// instead of reporting E1002. Fixed by using
	// `function_type_params_iter(func_index).nth(i)`, matching the sibling
	// check just above it that already accounted for inherited params.
	let case = TestCase::new(indoc! {"
        struct Holder<M> { x: i32 }
        impl<M> Holder<M> {
            pub fn get() -> i32 { 0 }
        }
        fn use_it() -> i32 {
            Holder::get()
        }
        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeAnnotationRequired),
		"expected E1002 (type annotation required) for unresolvable `M`, got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_phantom_type_param_suppressed_by_type_mismatch() {
	// When the argument for a NON-phantom param causes TypeMistmatch, the
	// phantom-param check is skipped to avoid double-reporting on the same
	// call site.  Only TypeMistmatch should appear.
	let case = TestCase::new(indoc! {"
        fn phantom<T>(x: i32) -> i32 { x }
        fn f() -> i32 { phantom::<_>(true) }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
	assert!(!has_error_code(
		&case.tir,
		DiagnosticCode::TypeAnnotationRequired
	));
}

#[test]
fn test_phantom_type_param_suppressed_when_unrelated_arg_mismatches() {
	// Phantom param U is unrelated to the TypeMistmatch on y — but the check
	// is still suppressed.  Known limitation: fixing the TypeMistmatch will
	// then reveal the phantom error on U in a second compilation.
	//
	// `true` is a concrete bool (not a comptime literal), so T is properly
	// inferred as bool without triggering the comptime-literal annotation path.
	let case = TestCase::new(indoc! {"
        fn f<T, U>(x: T, y: i32) -> i32 { y }
        fn g() -> i32 { f(true, true) }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
	assert!(!has_error_code(
		&case.tir,
		DiagnosticCode::TypeAnnotationRequired
	));
}

// ── unused type parameter warnings ───────────────────────────────────────────

#[test]
fn test_unused_type_param_warns() {
	let case = TestCase::new(indoc! {"
        pub fn phantom<T>() -> i32 { 0 }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedTypeParam.code())
			&& d.message.contains('T')),
		"expected W1006 for phantom T, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_used_type_param_in_param_no_warn() {
	let case = TestCase::new(indoc! {"
        pub fn identity<T>(x: T) -> T { x }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedTypeParam.code())),
		"T used in param and result should not warn"
	);
}

#[test]
fn test_implicit_self_type_param_in_trait_method_no_warn() {
	let case = TestCase::new(indoc! {"
        pub trait PointerSize {
            fn size() -> u32;
        }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedTypeParam.code())),
		"implicit Self type param should not warn"
	);
}

#[test]
fn test_used_type_param_in_return_only_no_warn() {
	let case = TestCase::new(indoc! {"
        pub fn produce<T>() -> T { loop {} }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedTypeParam.code())),
		"T used in return type should not warn"
	);
}

// ── unused struct field warnings ──────────────────────────────────────────────

#[test]
fn test_unused_field_init_but_not_read_warns() {
	let case = TestCase::new(indoc! {"
        pub struct Pair { pub x: i32, y: i32 }
        pub fn make(x: i32) -> Pair {
            Pair::{ x: x, y: 0 }
        }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedStructField.code())
			&& d.message.contains('y')),
		"expected W1007 for private field `y` which is initialized but never read, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_unused_field_read_suppresses_warn() {
	let case = TestCase::new(indoc! {"
        pub struct Pair { x: i32, y: i32 }
        pub fn make(x: i32, y: i32) -> Pair { Pair::{ x: x, y: y } }
        pub fn get_x(p: Pair) -> i32 { p.x }
        pub fn get_y(p: Pair) -> i32 { p.y }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedStructField.code())),
		"fields that are read should not warn"
	);
}

/// A plain `s.a = 1` used to record a *read*, because assignment targets and
/// ordinary reads are built by the same function and it hardcoded
/// `FieldAccessKind::Read` — so writing to a field silently suppressed the
/// "never read" warning it should have left standing.
#[test]
fn test_unused_field_write_does_not_suppress_warn() {
	let case = TestCase::new(indoc! {"
        pub struct Pair { x: i32, y: i32 }
        pub fn make(x: i32) -> Pair {
            local mut p = Pair::{ x: x, y: 0 };
            p.y = 1;
            p
        }
        pub fn get_x(p: Pair) -> i32 { p.x }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedStructField.code())
			&& d.message.contains('y')),
		"a field that is only ever written is still never read, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// The counterpart to the above: a compound assignment *does* read the field
/// before storing back to it, so it must keep suppressing the warning. This
/// is the distinction `FieldAccessKind::ReadWrite` exists to preserve —
/// folding it into either `Read` or `Write` gets one of these two tests
/// wrong.
#[test]
fn test_unused_field_compound_assignment_counts_as_read() {
	let case = TestCase::new(indoc! {"
        pub struct Pair { x: i32, y: i32 }
        pub fn make(x: i32) -> Pair {
            local mut p = Pair::{ x: x, y: 0 };
            p.y += 1;
            p
        }
        pub fn get_x(p: Pair) -> i32 { p.x }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedStructField.code())),
		"`p.y += 1` reads `y`, so it must not warn, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_pub_field_no_unused_warn() {
	let case = TestCase::new(indoc! {"
        pub struct Pair { pub x: i32, pub y: i32 }
        pub fn make() -> Pair { Pair::{ x: 1, y: 2 } }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedStructField.code())),
		"pub fields should not warn even if never read in this file"
	);
}

#[test]
fn test_never_initialized_field_no_warn() {
	let case = TestCase::new(indoc! {"
        pub struct Node { value: i32, next: i32 }
        pub fn is_zero(n: Node) -> bool { false }
    "});
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedStructField.code())),
		"fields that are never initialized should not warn (struct itself may be unused)"
	);
}

#[test]
fn test_type_param_multiple_bounds_both_enforced() {
	// `T: Scalable + Printable` — BoundList must be flattened so both bounds
	// end up in TypeParamInfo.bounds (exercises resolve_type_param_bounds).
	let case = TestCase::new(indoc! {"
        trait Scalable { fn scale(self, n: i32) -> i32; }
        trait Printable { fn print(self); }
        fn do_both<T: Scalable + Printable>(t: T) -> i32 {
            t.print();
            t.scale(1)
        }
    "});
	no_errors(&case);

	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("do_both"))
		.expect("function 'do_both' not found");

	assert_eq!(func.type_params.len(), 1);
	assert_eq!(
		func.type_params[0].bounds.traits.len(),
		2,
		"T should have two bounds (Scalable and Printable)"
	);
}

#[test]
#[ignore = "TODO: TIR does not currently check trait bound satisfaction at generic call sites"]
fn test_type_param_multiple_bounds_missing_impl_is_error() {
	// Pass a type that only satisfies one of two bounds — should error once
	// call-site trait bound checking is implemented.
	let case = TestCase::new(indoc! {"
        trait Scalable { fn scale(self, n: i32) -> i32; }
        trait Printable { fn print(self); }
        fn do_both<T: Scalable + Printable>(t: T) {}
        struct Num {}
        impl Scalable for Num { fn scale(self, n: i32) -> i32 { n } }
        fn call() { do_both(Num::{}); }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"expected an error: Num does not implement Printable"
	);
}

#[test]
fn test_multiple_supertraits_both_resolved() {
	// `trait Widget: Drawable + Sized` — both supertraits must appear in
	// tir.items.traits[widget_idx].supertraits (exercises BoundList flattening in
	// the supertrait resolution handler).
	let case = TestCase::new(indoc! {"
        trait Drawable { fn draw(self); }
        trait Sized { const SIZE: u32; }
        trait Widget: Drawable + Sized {}
    "});
	no_errors(&case);

	let widget_idx = case
		.tir
		.items
		.traits
		.iter()
		.position(|t| {
			case.graph.interner.resolve(t.name.inner) == Some("Widget")
		})
		.expect("trait 'Widget' not found");
	let drawable_idx = TraitIndex::new(
		case.tir
			.items
			.traits
			.iter()
			.position(|t| {
				case.graph.interner.resolve(t.name.inner) == Some("Drawable")
			})
			.expect("trait 'Drawable' not found") as u32,
	);
	let sized_idx = TraitIndex::new(
		case.tir
			.items
			.traits
			.iter()
			.position(|t| {
				case.graph.interner.resolve(t.name.inner) == Some("Sized")
			})
			.expect("trait 'Sized' not found") as u32,
	);

	let supertraits = &case.tir.items.traits[widget_idx]
		.bounds
		.traits
		.iter()
		.map(|bound| bound.trait_index)
		.collect::<Vec<_>>();
	assert_eq!(supertraits.len(), 2, "Widget should have two supertraits");
	assert!(
		supertraits.contains(&drawable_idx),
		"Drawable missing from supertraits"
	);
	assert!(
		supertraits.contains(&sized_idx),
		"Sized missing from supertraits"
	);
}

#[test]
fn test_multiple_supertraits_missing_one_impl_is_error() {
	// impl Widget for Point without impl Sized for Point — must error.
	let case = TestCase::new(indoc! {"
        trait Drawable { fn draw(self); }
        trait Sized { const SIZE: u32; }
        trait Widget: Drawable + Sized {}
        struct Point { x: i32 }
        impl Drawable for Point { fn draw(self) {} }
        impl Widget for Point {}
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnsatisfiedTraitBound.code())),
		"expected E1034 for missing Sized impl"
	);
}

#[test]
fn test_assoc_type_multiple_bounds_both_stored() {
	// `type Elem: A + B` — both bounds must be stored in the associated-type
	// entry (exercises BoundList flattening in TraitAssociatedType handler).
	let case = TestCase::new(indoc! {"
        trait A {}
        trait B {}
        trait Container {
            type Elem: A + B;
        }
    "});
	no_errors(&case);

	let container = case
		.tir
		.items
		.traits
		.iter()
		.find(|t| {
			case.graph.interner.resolve(t.name.inner) == Some("Container")
		})
		.expect("trait 'Container' not found");

	let elem_sym = case
		.graph
		.interner
		.get("Elem")
		.expect("symbol 'Elem' not interned");
	let assoc = container
		.assoc_types
		.get(&elem_sym)
		.expect("assoc type 'Elem' not found");
	assert_eq!(
		assoc.bounds.traits.len(),
		2,
		"Elem should have two trait bounds (A and B)"
	);
}

#[test]
fn test_assoc_type_multiple_bounds_violation_is_error() {
	// Provide a concrete type that satisfies A but not B — must error.
	let case = TestCase::new(indoc! {"
        trait A {}
        trait B {}
        impl A for i32 {}
        trait Container {
            type Elem: A + B;
        }
        struct Bag {}
        impl Container for Bag {
            type Elem = i32;
        }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"expected an error: i32 does not implement B"
	);
}

#[test]
fn test_impl_module_trait_for_type_resolves() {
	// `impl module::Drawable for Point` — multi-segment trait_name must be
	// resolved via resolve_path_segments_as_type (not resolve_type).
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
            mod shapes;
            use shapes::*;
            struct Point { x: i32 }
            impl shapes::Drawable for Point {
                fn draw(self) {}
            }
        "},
		&[(
			"shapes.wx",
			indoc! {"
                pub trait Drawable {
                    pub fn draw(self);
                }
            "},
		)],
	);
	no_errors(&case);

	let draw_sym = case
		.graph
		.interner
		.get("draw")
		.expect("symbol 'draw' not interned");
	let ti = case
		.tir
		.items
		.trait_impls
		.iter()
		.find(|ti| ti.members.contains_key(&draw_sym))
		.expect("no TraitImpl has 'draw' method");
	assert!(
		matches!(case.tir.types.resolve(ti.target.inner), Type::Struct { .. }),
		"target should be Point (a struct)"
	);
}

#[test]
fn test_invalid_self_type_rejected() {
	let case = TestCase::new(indoc! {"
        struct Foo { x: i32 }
        impl Foo {
            pub fn bad(self: u32) -> i32 { 0 }
        }
        export { }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref() == Some("E1053")),
		"expected InvalidSelfType diagnostic, got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_invalid_self_type_rejected_in_trait_declaration() {
	// Regression: unlike `ImplBlockMethod`, the `TraitFunction` registration
	// site never called `is_valid_self_type`, so a trait method could declare
	// `self: i32` (any type, not just `Self`/`*Self`) without a diagnostic —
	// and since the entry is still `ImplEntry::Method`, callers downstream
	// that assume `self` typechecks against the receiver would silently
	// accept a mismatched receiver.
	let case = TestCase::new(indoc! {"
        trait Drawable {
            fn bad(self: i32) -> i32;
        }
        export { }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref() == Some("E1053")),
		"expected InvalidSelfType diagnostic, got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_invalid_self_type_rejected_in_trait_impl() {
	// Same gap as above, but for the `impl Trait for Type` registration site.
	let case = TestCase::new(indoc! {"
        trait Drawable {
            fn bad(self) -> i32;
        }
        struct Foo { x: i32 }
        impl Drawable for Foo {
            fn bad(self: i32) -> i32 { 0 }
        }
        export { }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref() == Some("E1053")),
		"expected InvalidSelfType diagnostic, got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_duplicate_param_name_in_method_rejected() {
	// Regression: `build_method_signature` used to duplicate the param loop
	// from `build_function_signature` without its duplicate-name check, so a
	// method could redeclare a param name without a diagnostic. Merging both
	// into one `build_function_signature` closed that gap for methods too.
	let case = TestCase::new(indoc! {"
        struct Foo { x: i32 }
        impl Foo {
            pub fn bad(self, a: i32, a: i32) -> i32 { a }
        }
        export { }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref() == Some("E1000")),
		"expected DuplicateDefinition diagnostic, got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_infer_in_method_param_type_rejected() {
	// Regression: methods resolved param types via raw `resolve_type`, which
	// silently accepts `_` (INFER) — unlike free functions, which go through
	// `resolve_signature_type` and reject it. Merging into one
	// `build_function_signature` closed that gap for methods too.
	let case = TestCase::new(indoc! {"
        struct Foo { x: i32 }
        impl Foo {
            pub fn bad(self, a: _) -> i32 { 0 }
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::InferInSignature),
		"expected E1051 for `_` in method param type, got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_bare_self_param_resolves_to_self_type() {
	// Regression: merging `build_method_signature` into `build_function_signature`
	// dropped the `is_self` defaulting in the untyped-param branch, so a bare
	// `self` (no `: Type`) silently resolved to `TypeIndex::ERROR` instead of
	// `Self` — no diagnostic fired (`ERROR` is a poison value, not an error
	// site), so `no_errors`-style assertions couldn't catch it; only checking
	// the actual resolved type does.
	let case = TestCase::new(indoc! {"
        struct Foo { x: i32 }
        impl Foo {
            pub fn by_value(self) -> i32 { 0 }
        }
        export { }
    "});
	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| {
			case.graph
				.interner
				.resolve(f.name.inner)
				.map(|n| n == "by_value")
				.unwrap_or(false)
		})
		.expect("by_value not found");
	assert_ne!(
		func.params[0].ty.inner,
		TypeIndex::ERROR,
		"bare self param resolved to ERROR"
	);
}

#[test]
fn test_valid_self_types_accepted() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Foo { x: i32 }
        impl Foo {
            pub fn by_value(self) -> i32 { 0 }
            pub fn by_const_ptr(self: heap::*Foo) -> i32 { 0 }
            pub fn by_mut_ptr(self: heap::*Foo) -> i32 { 0 }
        }
        export { }
    "});
	no_errors(&case);
}

#[test]
fn test_duplicate_method_name_in_impl_rejected() {
	let case = TestCase::new(indoc! {"
        struct Foo { x: i32 }
        impl Foo {
            pub fn bar(self) -> i32 { 0 }
            pub fn bar(self) -> i32 { 1 }
        }
        export { }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref() == Some("E1000")),
		"expected DuplicateDefinition diagnostic, got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_duplicate_method_name_in_generic_impl_rejected() {
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Vec<T> { len: u32 }
        impl<T> Vec<T> {
            pub fn len(self) -> u32 { 0 }
            pub fn len(self) -> u32 { 1 }
        }
        export { }
    "});
	assert!(
		case.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref() == Some("E1000")),
		"expected DuplicateDefinition diagnostic, got: {:?}",
		case.tir.diagnostics
	);
}

// ── Tree mutability verification ──────────────────────────────────────────────

#[test]
fn test_tree_mut_binding_mut_does_not_grant_write_through() {
	// `mut` on binding does NOT grant write-through — pointer type must be `*T`.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn bad(mut ptr: heap::&i32) { ptr.* = 42 }
    "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"mut binding + &i32 should NOT allow write-through; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_tree_mut_immutable_binding_mutable_pointer_write_ok() {
	// Immutable binding + `*T` IS sufficient for write-through.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn ok(ptr: heap::*i32) { ptr.* = 42 }
    "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_tree_mut_nested_inner_immutable_blocks_deep_write() {
	// `p: *&i32` — outer `*` (exclusive) allows storing a pointer, but inner `&i32` (shared) blocks write-through.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn bad(p: heap::*heap::&i32) { p.*.* = 99 }
    "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"p.*.* write should error: inner &i32 is shared; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_tree_mut_nested_both_mutable_write_ok() {
	// `p: **i32` — both levels mutable, p.*.* = val should work.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn ok(p: heap::*heap::*i32) { p.*.* = 99 }
    "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_tree_mut_struct_field_through_immutable_ptr_is_error() {
	// `ptr: &Node` — cannot write any field through it.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { x: i32 }
        fn bad(ptr: heap::&Node) { ptr.*.x = 1 }
    "},
		&[],
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"field write through &Node should error; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_tree_mut_struct_field_through_mutable_ptr_ok() {
	// `ptr: *Node` — can write fields.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { x: i32 }
        fn ok(ptr: heap::*Node) { ptr.*.x = 1 }
    "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_tree_mut_mutable_ptr_coerces_to_immutable_param() {
	// Passing `*T` (exclusive) where `&T` (shared) is expected is allowed (safe downgrade).
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn read(ptr: heap::&i32) -> i32 { ptr.* }
        fn call(p: heap::*i32) -> i32 { read(p) }
    "},
		&[],
	);
	no_errors(&case);
}

#[test]
fn test_tree_mut_immutable_ptr_cannot_satisfy_mutable_param() {
	// Passing `&T` (shared) where `*T` (exclusive) is expected is NOT allowed.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn write(ptr: heap::*i32) { ptr.* = 1 }
        fn call(p: heap::&i32) { write(p) }
    "},
		&[],
	);
	assert!(
		!case.tir.diagnostics.is_empty(),
		"passing &i32 to *i32 param must error; got no diagnostics"
	);
}

#[test]
fn test_tree_mut_binding_mut_allows_reassign_but_not_write_through() {
	// `local mut p: &i32` — can reassign p, but cannot write through p.*.
	let case = TestCase::new_multi_file(
		"main.wx",
		indoc! {"
        memory heap: Memory where { Size = u32 };
        fn bad(a: heap::&i32, b: heap::&i32) {
            local mut p: heap::&i32 = a;
            p = b;
            p.* = 99
        }
    "},
		&[],
	);
	// Reassign `p = b` is ok (mut binding). Write `p.* = 99` must error (pointer type shared).
	assert!(
		has_error_code(&case.tir, DiagnosticCode::CannotMutateImmutable),
		"write through &i32 must error even with mut binding; got: {:?}",
		case.tir.diagnostics
	);
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.severity == codespan_reporting::diagnostic::Severity::Error
		})
		.collect();
	assert_eq!(
		errors.len(),
		1,
		"expected exactly 1 error (write-through only, not the reassign); got: {:?}",
		errors
	);
}

#[test]
fn test_ptr_autoderef_calls_method_on_inner_type() {
	// `ptr.value()` on a concrete struct should resolve via auto-deref.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { value: i32 }
        impl Node {
            pub fn value(self: heap::&Node) -> i32 { self.*.value }
        }
        fn get(n: heap::&Node) -> i32 { n.value() }
        export { get }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"auto-deref method call should succeed; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_ptr_autoderef_mutable_ptr_calls_mut_self_method() {
	// `ptr.set()` on `*Node` should resolve to a method taking `self: heap::*Self`.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { value: i32 }
        impl Node {
            pub fn set(self: heap::*Node, v: i32) { self.*.value = v }
        }
        fn update(n: heap::*Node) { n.set(42) }
        export { update }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"auto-deref mut method call should succeed; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_ptr_autoderef_mutable_ptr_coerces_to_immutable_self() {
	// `*T` calling a method with `self: &T` should succeed via `*T → &T` coercion.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { val: i32 }
        impl Node {
            pub fn read(self: heap::&Node) -> i32 { self.*.val }
        }
        fn get(n: heap::*Node) -> i32 { n.read() }
        export { get }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"mutable pointer calling immutable-self method must succeed; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_ptr_autoderef_immutable_ptr_rejects_mut_self_method() {
	// `ptr.set()` on `&Node` (shared) with `self: *Node` should be a type mismatch.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { value: i32 }
        impl Node {
            pub fn set(self: heap::*Node, v: i32) { self.*.value = v }
        }
        fn bad(n: heap::&Node) { n.set(42) }
        export { bad }
    "});
	assert!(
		!case.tir.diagnostics.is_empty(),
		"immutable pointer calling mut-self method must error"
	);
}

#[test]
fn test_ptr_autoderef_owned_self_reports_mismatch() {
	// Calling a method with `self: Node` (owned) via a pointer should report a type mismatch,
	// not "method not found". The user is expected to write `ptr.*.method()` to deref first.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { value: i32 }
        impl Node {
            pub fn owned(self: Node) -> i32 { self.value }
        }
        fn bad(n: heap::*Node) -> i32 { n.owned() }
        export { bad }
    "});
	assert!(
		!case.tir.diagnostics.is_empty(),
		"calling owned-self method via pointer must error"
	);
}

#[test]
fn test_ptr_autoderef_generic_impl_method() {
	// Auto-deref through a pointer to a generic struct should find the generic impl method.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Wrapper<T> { inner: T }
        impl <T> Wrapper<T> {
            pub fn get(self: heap::&Wrapper<T>) -> T { self.*.inner }
        }
        fn unwrap(w: heap::&Wrapper<i32>) -> i32 { w.get() }
        export { unwrap }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"auto-deref on generic impl method should succeed; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_ptr_autoderef_memory_qualifier_mismatch_errors() {
	// `other::&Node` calling a method with `self: heap::&Node` — the inner type `Node`
	// is found, but the self-param check fails because the memory qualifiers differ.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        memory other: Memory where { Size = u32 };
        struct Node { val: i32 }
        impl Node {
            pub fn read(self: heap::&Node) -> i32 { self.*.val }
        }
        fn bad(n: other::&Node) -> i32 { n.read() }
        export { bad }
    "});
	assert!(
		!case.tir.diagnostics.is_empty(),
		"calling heap method via other-memory pointer must error"
	);
}

#[test]
fn test_ptr_autoderef_double_pointer_not_found() {
	// `&&Node` — auto-deref is one level only. The inner type is `&Node`, which has no
	// impl block, so the method is not found.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { val: i32 }
        impl Node {
            pub fn read(self: heap::&Node) -> i32 { self.*.val }
        }
        fn bad(n: heap::&heap::&Node) -> i32 { n.read() }
        export { bad }
    "});
	assert!(
		!case.tir.diagnostics.is_empty(),
		"double-pointer auto-deref must error — only one level deep"
	);
}

#[test]
fn test_ptr_field_access_does_not_auto_deref() {
	// `ptr.field` (no `.*`) — field access does NOT auto-deref pointers.
	// The user must write `ptr.*.field`.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { val: i32 }
        fn bad(n: heap::&Node) -> i32 { n.val }
        export { bad }
    "});
	assert!(
		!case.tir.diagnostics.is_empty(),
		"field access through pointer without deref must error"
	);
}

#[test]
fn test_ptr_autoderef_chained_calls() {
	// `ptr.next().get_val()` — `next()` returns `&Node`, then `get_val()` auto-derefs
	// the returned pointer. Each call goes through resolve_method_call independently.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Node { val: i32 }
        impl Node {
            pub fn next(self: heap::&Node) -> heap::&Node { self }
            pub fn get_val(self: heap::&Node) -> i32 { self.*.val }
        }
        fn chain(n: heap::&Node) -> i32 { n.next().get_val() }
        export { chain }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"chained auto-deref method calls should succeed; got: {:?}",
		case.tir.diagnostics
	);
}

// ── AddressOf (.&) ──────────────────────────────────────────────────────────

#[test]
fn test_address_of_non_place_rejected() {
	// `.&` on a stack value (not a memory place) must emit a diagnostic.
	let case = TestCase::new(indoc! {"
        fn bad() -> i32 { (5 as i32).& }
        export { bad }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::InvalidAssignmentTarget),
		"expected InvalidAssignmentTarget for .& on a temporary; got: {:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_address_of_place_has_correct_pointer_type() {
	// `arr[i].&` on a heap array must resolve to a `heap::&i32` reference type,
	// and `ptr.*.field.&` on a struct field must resolve to the field's reference type.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        struct Point { x: i32, y: i32 }
        fn arr_elem_ptr(arr: heap::&[i32; 4], i: u32) -> heap::&i32 { arr[i].& }
        fn field_ptr(ptr: heap::&Point) -> heap::&i32 { ptr.*.x.& }
        export { arr_elem_ptr, field_ptr }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"unexpected diagnostics: {:?}",
		case.tir.diagnostics
	);
}

// ── Phase-1 duplicate detection (struct/enum/memory) ──────────────────────

#[test]
fn test_struct_triple_duplicate_attributes_to_first_definition() {
	// Regression test: `uses_foo` references `Foo` before any of the three
	// same-named structs are reached in the natural Phase-2 sweep, forcing
	// early resolution. Before the Phase-1 first-wins fix, this forced
	// resolution of whichever struct's `Pending` marker happened to survive
	// Phase 1's blind overwrite (the *last* one, C) — so B and C's
	// diagnostics both misattributed to C instead of the true first
	// definition, A. Both duplicates must now attribute to the same
	// (first) definition.
	let case = TestCase::new(indoc! {"
        fn uses_foo(x: Foo) -> i32 { 0 }
        struct Foo { a: i32 }
        struct Foo { b: i32 }
        struct Foo { c: i32 }
        export { }
    "});
	let dup_diags: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| {
			d.code.as_deref()
				== Some(DiagnosticCode::DuplicateDefinition.code())
		})
		.collect();
	assert_eq!(
		dup_diags.len(),
		2,
		"expected exactly 2 duplicate diagnostics (B and C dup of A), got: {:?}",
		case.tir.diagnostics
	);
	let previous_definition_ranges: Vec<_> = dup_diags
		.iter()
		.map(|d| {
			d.labels
				.iter()
				.find(|l| l.message.starts_with("previous definition"))
				.expect("missing previous-definition label")
				.range
				.clone()
		})
		.collect();
	assert_eq!(
		previous_definition_ranges[0], previous_definition_ranges[1],
		"both duplicates must attribute to the same (first) definition, got: {:?}",
		previous_definition_ranges
	);
}

#[test]
fn test_duplicate_enum_definition_is_error() {
	// Regression test: Enum's duplicate check used to have no `else`
	// branch reporting a diagnostic at all — two same-named enums were
	// silently accepted with the second one just dropped.
	let case = TestCase::new(indoc! {"
        enum Foo: i32 { A = 0 }
        enum Foo: i32 { B = 0 }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected duplicate definition error for two enums with same name, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_duplicate_memory_definition_is_error() {
	// Regression test: Memory had no duplicate check anywhere — two
	// same-named memories were silently accepted.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };
        memory heap: Memory where { Size = u32 };
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected duplicate definition error for two memories with same name, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_true_false_are_keywords_not_shadowable() {
	// Regression test: `true`/`false` used to be resolved through the
	// ordinary identifier/symbol-table path, so a local named `true` or
	// `false` would silently shadow the boolean literal. They are now
	// keywords parsed directly into dedicated `Bool` expressions, so a
	// same-named local can never be referenced and is flagged as unused.
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local true = false;
            if true { 1 } else { 2 }
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnusedVariable),
		"expected the shadowed `local true` to be reported as unused, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_underscore_prefixed_local_suppresses_unused_warning() {
	// `_foo` still binds the name (unlike a bare `_` wildcard) but, matching
	// Rust's convention, should not trigger the unused-variable lint.
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local _unused: i32 = 1;
            2
        }
        export { f }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::UnusedVariable),
		"expected no unused-variable warning for `_unused`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_underscore_prefixed_param_suppresses_unused_warning() {
	let case = TestCase::new(indoc! {"
        fn f(_unused: i32) -> i32 {
            1
        }
        export { f }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::UnusedVariable),
		"expected no unused-variable warning for param `_unused`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_plain_unused_local_still_warns() {
	// Sanity check that the underscore-prefix exemption didn't accidentally
	// disable the lint entirely.
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local unused: i32 = 1;
            2
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnusedVariable),
		"expected unused-variable warning for `unused`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_trait_impl_resolves() {
	// `impl<T> Getter for Box<T>` — the impl's own `T` (not the struct's,
	// though here it happens to line up) must be resolvable at the target
	// type expression, and dispatch must find it for a concrete receiver.
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        trait Getter {
            fn get(self) -> i32;
        }

        impl<T> Getter for Box<T> {
            fn get(self) -> i32 { 1 }
        }

        fn use_it(b: Box<i32>) -> i32 {
            b.get()
        }

        export { use_it }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"unexpected errors: {:?}",
		errors.iter().map(|d| &d.message).collect::<Vec<_>>()
	);
	let getter_sym = case
		.graph
		.interner
		.get("Getter")
		.expect("symbol `Getter` not interned");
	let trait_impl = case
		.tir
		.items
		.trait_impls
		.iter()
		.find(|ti| {
			case.tir.items.traits[usize::from(ti.trait_index)]
				.name
				.inner == getter_sym
		})
		.expect("no TraitImpl for Getter");
	assert_eq!(
		trait_impl.type_params.len(),
		1,
		"the impl's own type param should be registered on the TraitImpl"
	);
}

#[test]
fn test_generic_inherent_impl_vs_trait_priority() {
	// A generic inherent impl and a concrete trait impl both provide `get`
	// on `Box<i32>` with different return types (`T` vs `bool`) — inherent
	// must win outright, so `use_it`'s `-> i32` body type-checks cleanly
	// only if the inherent (T = i32) method was chosen.
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        impl<T> Box<T> {
            pub fn get(self) -> T { self.v }
        }

        trait Getter {
            fn get(self) -> bool;
        }

        impl Getter for Box<i32> {
            fn get(self) -> bool { true }
        }

        fn use_it(b: Box<i32>) -> i32 {
            b.get()
        }

        export { use_it }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"expected the inherent impl to win over the trait impl, got errors: {:?}",
		errors.iter().map(|d| &d.message).collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_trait_impl_bound_satisfied() {
	// `impl<T: Foo> Getter for Box<T>` applies to `Box<Yes>` since `Yes: Foo`.
	let case = TestCase::new(indoc! {"
        trait Foo {}

        struct Yes {}
        impl Foo for Yes {}

        struct Box<T> { v: T }

        trait Getter {
            fn get(self) -> i32;
        }

        impl<T: Foo> Getter for Box<T> {
            fn get(self) -> i32 { 1 }
        }

        fn use_it(b: Box<Yes>) -> i32 {
            b.get()
        }

        export { use_it }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::MethodNotFound),
		"expected the bounded impl to apply since Yes: Foo, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_trait_impl_bound_violation_reports_error() {
	// Same shape as `test_generic_trait_impl_bound_satisfied`, but the
	// receiver's type argument (`No`) does not implement the impl's bound
	// (`Foo`) — the impl must not apply, so `.get()` resolves to nothing.
	let case = TestCase::new(indoc! {"
        trait Foo {}

        struct No {}

        struct Box<T> { v: T }

        trait Getter {
            fn get(self) -> i32;
        }

        impl<T: Foo> Getter for Box<T> {
            fn get(self) -> i32 { 1 }
        }

        fn use_it(b: Box<No>) -> i32 {
            b.get()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::MethodNotFound),
		"expected no method found since No does not implement Foo, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_trait_impl_and_concrete_impl_ambiguous() {
	// A concrete `impl Getter for Box<i32>` and a generic
	// `impl<T> Getter for Box<T>` both target the same type constructor
	// `Box` — WX allows at most one implementation of a given trait per type
	// constructor, so this is a `DuplicateTraitImpl` error at the second
	// impl's declaration, not a call-site ambiguity (generic arguments never
	// participate in impl selection, so it doesn't matter that the two
	// impls' receivers happen to overlap here).
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        trait Getter {
            fn get(self) -> i32;
        }

        impl Getter for Box<i32> {
            fn get(self) -> i32 { 1 }
        }

        impl<T> Getter for Box<T> {
            fn get(self) -> i32 { 2 }
        }

        fn use_it(b: Box<i32>) -> i32 {
            b.get()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateTraitImpl),
		"expected a duplicate-trait-impl error for the second `impl Getter for Box<_>`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_two_concrete_trait_impls_for_same_struct_is_duplicate() {
	// Two non-overlapping concrete impls (`Box<i32>` and `Box<u8>`) of the
	// same trait still target the same type constructor `Box` — illegal
	// regardless of the fact that their receivers never actually collide.
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        trait Getter {
            fn get(self) -> i32;
        }

        impl Getter for Box<i32> {
            fn get(self) -> i32 { 1 }
        }

        impl Getter for Box<u8> {
            fn get(self) -> i32 { 2 }
        }

        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateTraitImpl),
		"expected a duplicate-trait-impl error for two concrete impls of Getter for Box<_>, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_two_generic_trait_impls_for_same_struct_is_duplicate() {
	// Two independently-bounded generic impls of the same trait for the
	// same constructor — illegal even though `Foo`/`Bar` could be disjoint
	// bounds satisfiable by no common type; WX doesn't reason about bound
	// overlap here, the constructor match alone is enough to conflict.
	let case = TestCase::new(indoc! {"
        trait Foo {}
        trait Bar {}

        struct Box<T> { v: T }

        trait Getter {
            fn get(self) -> i32;
        }

        impl<T: Foo> Getter for Box<T> {
            fn get(self) -> i32 { 1 }
        }

        impl<T: Bar> Getter for Box<T> {
            fn get(self) -> i32 { 2 }
        }

        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateTraitImpl),
		"expected a duplicate-trait-impl error for two generic impls of Getter for Box<_>, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_blanket_trait_impl_reports_invalid_impl_target() {
	// `impl<T> Getter for T` has a bare `Type::TypeParam` as its target.
	// `ImplTarget::from_type` has no case for that (see its `Err(())` arm
	// list), so this must be reported right at the impl block via
	// `DiagnosticCode::InvalidImplTarget` — mirroring the equivalent
	// mistake on an *inherent* impl (`impl<T> T { .. }`), which reports the
	// same code ("cannot define an `impl` block for `T`"). Before this was
	// wired up, `register_trait_impl` silently discarded the impl instead
	// (see git history), leaving it dead code with no diagnostic at all,
	// and the only symptom was a disconnected `MethodNotFound` at every
	// call site instead.
	let case = TestCase::new(indoc! {"
        trait Getter {
            fn get(self) -> i32;
        }

        impl<T> Getter for T {
            fn get(self) -> i32 { 1 }
        }

        export { }
    "});

	assert!(
		has_error_code(&case.tir, DiagnosticCode::InvalidImplTarget),
		"expected an `InvalidImplTarget` error at the blanket impl, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_trait_impl_associated_type_substitutes() {
	// `impl<T> Container for Box<T> { type Item = T; ... }` — the
	// associated type's stored value is the impl's own type param, so
	// resolving `Self::Item` for a concrete `Box<i32>` receiver must
	// substitute through the type args inferred from that receiver rather
	// than leaking the impl's bare `TypeParam`.
	let case = TestCase::new(indoc! {"
        trait Container {
            type Item;
            fn get(self) -> Self::Item;
        }

        struct Box<T> { v: T }

        impl<T> Container for Box<T> {
            type Item = T;
            fn get(self) -> Self::Item { self.v }
        }

        fn use_it(b: Box<i32>) -> i32 {
            b.get()
        }

        export { use_it }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(
		errors.is_empty(),
		"expected Self::Item to substitute to i32, got errors: {:?}",
		errors.iter().map(|d| &d.message).collect::<Vec<_>>()
	);
}

#[test]
fn test_abstract_dispatch_access_recorded_for_associated_const() {
	// `T::FOO` inside a bounded-generic function resolves to `HasConst`'s
	// abstract declaration (no value — only impls provide one), so
	// `record_abstract_dispatch_access` must mark `Impl1::FOO` as accessed
	// too, exactly as it already does for methods. Before it handled
	// `ImplEntry::AssociatedConst`, this fell through as a no-op and
	// `Impl1::FOO` was flagged as an unused-item false positive even though
	// it's reachable via abstract dispatch.
	let case = TestCase::new(indoc! {"
        trait HasConst {
            const FOO: i32;
        }

        struct Impl1 {}
        impl HasConst for Impl1 {
            const FOO: i32 = 42;
        }

        fn use_it<T: HasConst>() -> i32 {
            T::FOO
        }

        fn run() -> i32 {
            use_it::<Impl1>()
        }

        export { run }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"expected no diagnostics (in particular no false-positive unused-item warning for Impl1::FOO), got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_type_param_ambiguous_bound_methods_reports_error() {
	// Two bound traits on the same type param both declare `foo` — this goes
	// through `resolve_impl_member`'s `Type::TypeParam` branch, which used to
	// be a separate `find_map` (first-bound-wins, no ambiguity check) at each
	// call site before it was unified into the same candidate-scanning logic
	// as concrete types.
	let case = TestCase::new(indoc! {"
        trait A {
            fn foo(self) -> i32;
        }
        trait B {
            fn foo(self) -> i32;
        }
        fn use_it<T: A + B>(x: T) -> i32 {
            x.foo()
        }
        export { }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::AmbiguousTraitMember),
		"expected an ambiguity diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_stdlib_inherent_slice_method_beats_trait_no_ambiguity() {
	// Same inherent-always-wins rule as the struct case, but on
	// `ImplTarget::Slice`. The inherent side is the stdlib's own
	// `impl<Mem: Memory, T> Mem::&[T] { fn len(self) -> Mem::Size }`, which
	// is now the only inherent impl a slice can have. `Counter::len` returns
	// `bool`, so picking it would make `use_it`'s return type fail to check.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        trait Counter {
            fn len(self) -> bool;
        }

        impl Counter for heap::&[i32] {
            fn len(self) -> bool { true }
        }

        fn use_it(s: heap::&[i32]) -> u32 {
            s.len()
        }

        export { use_it }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_generic_inherent_impl_resolves_via_path_call_syntax() {
	// Same generic inherent impl as the method-call case, but resolved
	// through `Type::method(receiver)` path syntax (`resolve_namespace_member`)
	// instead of `x.method()` — exercises the fix that threads the inferred
	// `type_args` (`T = i32`) through that call site instead of hardcoding
	// `Box::new([])`, which would leave `T` unresolved and fail to type check.
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        impl<T> Box<T> {
            pub fn get(self) -> T { self.v }
        }

        fn use_it(b: Box<i32>) -> i32 {
            Box::get(b)
        }

        export { use_it }
    "});
	no_errors(&case);
}

#[test]
fn test_concrete_and_generic_inherent_impl_collision_is_rejected() {
	// `impl Box<i32> { fn get(...) -> bool }` (concrete) and
	// `impl<T> Box<T> { fn get(...) -> T }` (generic) both provide `get` for
	// `Box<i32>`. Concrete and generic inherent impls are no longer two
	// separate registries (`impl_members` vs `generic_impl_list`) — they're
	// both just `ImplBlock`s sharing the same `impl_block_dispatch` bucket,
	// so `resolve_impl_member`'s candidate scan sees both and reports the
	// conflict instead of one silently shadowing the other.
	let case = TestCase::new(indoc! {"
        struct Box<T> { v: T }

        impl<T> Box<T> {
            pub fn get(self) -> T { self.v }
        }

        impl Box<i32> {
            pub fn get(self) -> bool { true }
        }

        fn use_it(b: Box<i32>) -> i32 {
            b.get()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected a duplicate-definition diagnostic about the colliding `get`s, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_two_generic_impl_blocks_with_colliding_method_name_is_rejected() {
	// Two SEPARATE `impl<T> S<T> { .. }` blocks for the same struct, each
	// providing `foo`, land in the same `impl_block_dispatch` bucket.
	// Neither registration writes a single "winner" anymore — every block
	// sharing the bucket is a candidate, and `resolve_impl_member` catches
	// the conflict when both turn out to apply to the same receiver.
	let case = TestCase::new(indoc! {"
        struct S<T> { v: T }

        impl<T> S<T> {
            pub fn foo(self) -> i32 { 1 }
        }

        impl<T> S<T> {
            pub fn foo(self) -> i32 { 2 }
        }

        fn use_it(s: S<i32>) -> i32 {
            s.foo()
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected a duplicate-definition diagnostic about the colliding `foo`s, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_two_generic_impl_blocks_colliding_despite_differing_bounds_is_rejected()
{
	// Same collision as above, but the two blocks have DIFFERENT bounds on
	// their otherwise-unconstrained type param (`impl<T: Marker> Y` vs
	// `impl<T> Y`). Real rustc still rejects this as E0592 — a differing
	// bound doesn't carve out non-overlapping applicability, since for any
	// hypothetically valid `T` both impls could apply; Rust's coherence
	// checker is deliberately bound-blind here (this is part of why full
	// specialization is still unstable). The collision check must be
	// bound-blind too, i.e. keyed only on `(ImplTarget, name)`.
	let case = TestCase::new(indoc! {"
        struct Y {}

        trait Marker {}

        impl<T: Marker> Y {
            pub fn bar(self, x: T) -> i32 { 1 }
        }

        impl<T> Y {
            pub fn bar(self, x: T) -> i32 { 2 }
        }

        fn use_it(y: Y, v: i32) -> i32 {
            y.bar(v)
        }

        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateDefinition),
		"expected a duplicate-definition diagnostic about the colliding `bar`s, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_impl_resolution_uses_global_index_not_local_position() {
	// `trait_impl_dispatch[kind]` holds GLOBAL indices into
	// `self.tir.items.trait_impls` (assigned in registration order across the
	// whole file), not positions local to `kind`. `Unrelated`'s impl
	// registers first (`trait_impls[0]`); `S`'s impl (the one we actually
	// care about) registers second (`trait_impls[1]`), so
	// `trait_impl_dispatch[Struct(S)] == [1]` (a bucket shared by outer
	// shape, not narrowed to `S` specifically until `unify_trait_impl_target`
	// checks each candidate). A regression here (e.g. using the loop
	// position `0..impl_count` to index `trait_impls` directly instead of
	// dereferencing through the dispatch bucket first) would look at
	// `Unrelated`'s impl instead of `S`'s and wrongly report `S` as not
	// having `foo`.
	let case = TestCase::new(indoc! {"
        trait Other {
            fn bar(self) -> i32;
        }
        struct Unrelated {}
        impl Other for Unrelated {
            fn bar(self) -> i32 { 1 }
        }

        trait Foo {
            fn foo(self) -> i32;
        }
        struct S {}
        impl Foo for S {
            fn foo(self) -> i32 { 2 }
        }

        fn use_it(s: S) -> i32 { s.foo() }
        export { use_it }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::MethodNotFound),
		"expected `s.foo()` to resolve via `S`'s own impl, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_where_clause_bound_on_assoc_type_lets_qualified_path_resolve() {
	// `type Size: PointerSize` alone doesn't make `Mem::Size: UnsignedInt`
	// provable — that extra fact only becomes visible once `grow` adds
	// `where { Size: UnsignedInt }` to its own `Mem: Memory` bound, which
	// `abstract_type_bounds` must merge with `Memory::Size`'s own declared
	// bound before `<Mem::Size as UnsignedInt>::Signed` can typecheck.
	let case = TestCase::new(indoc! {"
        trait UnsignedInt {
            type Signed: SignedInt where { Unsigned = Self };
        }

        trait SignedInt {
            type Unsigned: UnsignedInt where { Signed = Self };
        }

        impl UnsignedInt for u32 {
            type Signed = i32;
        }

        impl SignedInt for i32 {
            type Unsigned = u32;
        }

        fn grow<Mem: Memory where { Size: UnsignedInt }>(_mem: Mem, _delta: Mem::Size) -> <Mem::Size as UnsignedInt>::Signed {
            unreachable
        }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected no trait-bound-violation diagnostic, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_conformance_checks_bound_kind_assoc_binding_trait_violation() {
	// `Container::Elem` requires `HasSize where { Size: Marker }` — an impl
	// providing an `Elem` whose `Size` doesn't implement `Marker` must be
	// rejected at the `impl` site itself, with no call ever needed to
	// trigger it. Regression test for `check_assoc_type_bounds` previously
	// only verifying `Equals`-kind bindings and silently skipping `Bound`.
	let case = TestCase::new(indoc! {"
        trait Marker {}
        trait HasSize {
            type Size;
        }
        trait Container {
            type Elem: HasSize where { Size: Marker };
        }
        struct BadElem {}
        impl HasSize for BadElem {
            type Size = u32;
        }
        struct Foo {}
        impl Container for Foo {
            type Elem = BadElem;
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound-violation diagnostic for BadElem::Size not implementing Marker, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_conformance_checks_bound_kind_assoc_binding_typeset_violation() {
	// Same shape, but the `Bound` is a typeset rather than a trait.
	let case = TestCase::new(indoc! {"
        pub typeset Ints { u32, u64 }
        trait HasSize {
            type Size;
        }
        trait Container {
            type Elem: HasSize where { Size: Ints };
        }
        struct BadElem {}
        impl HasSize for BadElem {
            type Size = bool;
        }
        struct Foo {}
        impl Container for Foo {
            type Elem = BadElem;
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypesetBoundViolation),
		"expected a typeset-bound-violation diagnostic for BadElem::Size (bool) not in Ints, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_trait_conformance_bound_kind_assoc_binding_satisfied_no_error() {
	let case = TestCase::new(indoc! {"
        trait Marker {}
        trait HasSize {
            type Size;
        }
        trait Container {
            type Elem: HasSize where { Size: Marker };
        }
        struct GoodElem {}
        impl HasSize for GoodElem {
            type Size = u32;
        }
        impl Marker for u32 {}
        struct Foo {}
        impl Container for Foo {
            type Elem = GoodElem;
        }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"unexpected trait-bound-violation diagnostic: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_call_site_assoc_bound_satisfied_no_error() {
	// `needs_marker`'s own `where { Size: Marker }` isn't checked merely by
	// unifying `Mem: Memory` — the call site's *concrete* `Mem32::Size`
	// (`u32`) must actually implement `Marker` too. Here it does.
	let case = TestCase::new(indoc! {"
        trait Marker {}
        trait Memory {
            type Size;
        }
        struct Mem32 {}
        impl Memory for Mem32 {
            type Size = u32;
        }
        impl Marker for u32 {}
        fn needs_marker<Mem: Memory where { Size: Marker }>(_mem: Mem, _delta: Mem::Size) {}
        fn use_it(mem: Mem32, delta: u32) {
            needs_marker(mem, delta);
        }
        export { use_it }
    "});
	no_errors(&case);
}

#[test]
fn test_call_site_assoc_bound_violated_reports_error() {
	// Same shape as `test_call_site_assoc_bound_satisfied_no_error`, but
	// `u32` never implements `Marker` here — `needs_marker`'s `where { Size:
	// Marker }` bound must be enforced against `Mem32`'s *actual* `Size`
	// at the call site, not just checked in the abstract (inside
	// `needs_marker`'s own body, where `Mem::Size: Marker` is taken on
	// faith from the signature).
	let case = TestCase::new(indoc! {"
        trait Marker {}
        trait Memory {
            type Size;
        }
        struct Mem32 {}
        impl Memory for Mem32 {
            type Size = u32;
        }
        fn needs_marker<Mem: Memory where { Size: Marker }>(_mem: Mem, _delta: Mem::Size) {}
        fn use_it(mem: Mem32, delta: u32) {
            needs_marker(mem, delta);
        }
        export { use_it }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TraitBoundViolation),
		"expected a trait-bound-violation diagnostic for `u32: Marker`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_unqualified_chained_projection_resolves_when_unambiguous() {
	// `Mem::Size::Signed` (no `<... as Trait>::` qualification) should
	// resolve on its own once `Size`'s bounds include exactly one trait
	// declaring `Signed` — here that's only true because of the `where {
	// Size: Unsigned }` merge; `Memory::Size` alone declares no bound at
	// all.
	let case = TestCase::new(indoc! {"
        trait Unsigned { type Signed; }
        trait Memory { type Size; }
        struct Mem32 {}
        impl Memory for Mem32 { type Size = u32; }
        impl Unsigned for u32 { type Signed = i32; }

        fn f<Mem: Memory where { Size: Unsigned }>(_m: Mem) -> Mem::Size::Signed { unreachable }
        fn f_concrete(m: Mem32) -> i32 { f(m) }
        export { f_concrete }
    "});
	no_errors(&case);
}

#[test]
fn test_unqualified_chained_projection_ambiguous_reports_error() {
	// `Size`'s bounds end up including *two* traits that both declare
	// `Foo` — one from `Memory::Size`'s own declaration (`TraitA`), one
	// from `f`'s `where { Size: TraitB }`. The unqualified `Mem::Size::Foo`
	// can't tell them apart and must be rejected rather than silently
	// picking whichever bound happens to be checked first.
	let case = TestCase::new(indoc! {"
        trait TraitA { type Foo; }
        trait TraitB { type Foo; }
        trait Memory { type Size: TraitA; }
        struct Mem32 {}
        impl Memory for Mem32 { type Size = u32; }
        impl TraitA for u32 { type Foo = i32; }
        impl TraitB for u32 { type Foo = i64; }

        fn f<Mem: Memory where { Size: TraitB }>(_m: Mem) -> Mem::Size::Foo { unreachable }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::AmbiguousTraitMember),
		"expected an ambiguous-trait-member diagnostic for `Mem::Size::Foo`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_where_clause_assoc_type_conflicting_typeset_bound_reports_error() {
	// `Memory::Size` is already pinned to `SetA` by the trait's own
	// declaration (`type Size: SetA`); `f`'s `where { Size: SetB }` tries to
	// layer on a second, different typeset bound for the same associated
	// type. `Bounds` only ever holds one typeset slot, so this must be
	// rejected at the point the `where` clause is resolved rather than
	// silently keeping (or silently dropping) one of the two.
	let case = TestCase::new(indoc! {"
        typeset SetA { u8, u16 }
        typeset SetB { u32, u64 }
        trait Memory { type Size: SetA; }
        struct Mem8 {}
        impl Memory for Mem8 { type Size = u8; }

        fn f<Mem: Memory where { Size: SetB }>(_m: Mem) {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::MultipleTypesetBounds),
		"expected a multiple-typeset-bounds diagnostic, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_display_bounds_includes_where_clause_assoc_type_bound() {
	// Regression test: `TypeFormatter::write_bounds` (shared by diagnostic
	// messages and LSP hover) used to only look at `TraitBound.bindings`'
	// `Equals` entries when deciding whether to print a `where { }` clause
	// at all — a bound with *only* a `where { Size: Unsigned }` entry (no
	// `=` binding) printed as bare `Memory`, silently dropping the
	// constraint from what the user sees on hover.
	let case = TestCase::new(indoc! {"
        trait Unsigned {}
        trait Memory { type Size; }
        fn grow<Mem: Memory where { Size: Unsigned }>(mem: Mem, delta: Mem::Size) -> Mem::Size {
            unreachable
        }
    "});
	let func = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| {
			case.graph
				.interner
				.resolve(f.name.inner)
				.map(|n| n == "grow")
				.unwrap_or(false)
		})
		.unwrap();
	let fmt = case.tir.formatter(
		&case.graph.interner,
		&case.graph.packages,
		case.graph.root_package,
	);
	let s = fmt.display_bounds(&func.type_params[0].bounds).unwrap();
	assert_eq!(s, "Memory where { Size: Unsigned }");
}

#[test]
fn test_where_clause_duplicate_binding_name_reports_error() {
	// Whether written as two equality bindings, two bounds, or a mix, the
	// same associated-type name can only be bound once per `where { }`
	// block — a second occurrence is diagnosed and dropped rather than
	// silently overriding or merging with the first.
	let case = TestCase::new(indoc! {"
        trait Unsigned {}
        trait Memory { type Size; }
        struct Mem32 {}
        impl Memory for Mem32 { type Size = u32; }

        fn f<Mem: Memory where { Size = u32, Size: Unsigned }>(_m: Mem) {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::DuplicateAssocTypeBinding),
		"expected a duplicate-assoc-type-binding diagnostic, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Regression test: `resolve_path_segments_as_bound`'s final-segment lookup
/// (`module::Missing`) used to hit a bare `todo!()` when the name wasn't
/// found in the namespace, panicking the whole compilation (and, in the
/// LSP, the single actor task that owns all its state — killing every
/// language feature until the client noticed and respawned the server).
/// It must report an ordinary diagnostic instead.
#[test]
fn test_qualified_bound_with_undeclared_member_reports_diagnostic_not_panic() {
	let case = TestCase::new(indoc! {"
        mod ns {
            pub trait Marker {}
        }

        fn f<T: ns::Missing>() {}
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredType),
		"expected an undeclared-type diagnostic, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

/// Regression test: a bare identifier that resolves to a module (the first
/// segment of a qualified bound like `ns::Marker`) went through
/// `record_symbol_access`, whose `match` had no arm for
/// `SymbolKind::Module` — so the namespace's own `accesses` list never
/// gained an entry for that token, even though the trait it named
/// (`Marker`) was recorded correctly. Hover/go-to-definition/semantic
/// highlighting had nothing to find at the `ns` token as a result.
#[test]
fn test_qualified_bound_namespace_segment_records_access() {
	let case = TestCase::new(indoc! {"
        mod ns {
            pub trait Marker {}
        }

        fn f<T: ns::Marker>(_x: T) {}
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| matches!(d.severity, Severity::Error | Severity::Bug)),
		"expected no error diagnostics; got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	let has_namespace_access = case
		.tir
		.modules
		.namespaces
		.iter()
		.any(|ns| !ns.accesses.is_empty());
	assert!(
		has_namespace_access,
		"expected some namespace to have a recorded access for the `ns` \
		 token in `T: ns::Marker`"
	);
}

// ── match ────────────────────────────────────────────────────────────────

#[test]
fn test_match_int_exhaustive_with_wildcard() {
	let case = TestCase::new(indoc! {"
        fn sign(x: i32) -> i32 {
            match x {
                0 -> { 0 },
                1 -> { 1 },
                _ -> { -1 },
            }
        }
        export { sign }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
	insta::assert_yaml_snapshot!(case.tir);
}

#[test]
fn test_match_enum_all_variants_covered_no_wildcard_ok() {
	let case = TestCase::new(indoc! {"
        enum FileDescriptor: u8 {
            StdIn = 0,
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
        export { name }
    "});
	assert!(
		case.tir.diagnostics.is_empty(),
		"expected exhaustive enum match without `_` to need no diagnostics, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_match_enum_missing_variant_is_error() {
	let case = TestCase::new(indoc! {"
        enum FileDescriptor: u8 {
            StdIn = 0,
            StdOut,
            StdErr,
        }
        fn name(fd: FileDescriptor) -> u8 {
            match fd {
                FileDescriptor::StdIn -> { 0 },
                FileDescriptor::StdOut -> { 1 },
            }
        }
        export { name }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::NonExhaustiveMatch),
		"expected E1066 (NonExhaustiveMatch) for missing StdErr, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_match_int_without_wildcard_is_error() {
	let case = TestCase::new(indoc! {"
        fn sign(x: i32) -> i32 {
            match x {
                0 -> { 0 },
                1 -> { 1 },
            }
        }
        export { sign }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::NonExhaustiveMatch),
		"expected E1066 (NonExhaustiveMatch) for an int match without `_`, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_match_invalid_pattern_shape_is_error() {
	// `y` is a legal expression (a local reference) but not a legal
	// pattern: it isn't a literal, `_`, or an `Enum::Variant` path, and it
	// doesn't fold to a compile-time constant.
	let case = TestCase::new(indoc! {"
        fn f(x: i32, y: i32) -> i32 {
            match x {
                y -> { 1 },
                _ -> { 2 },
            }
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::InvalidPattern),
		"expected E1068 (InvalidPattern) for a non-constant pattern, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_match_arm_type_mismatch_reuses_type_mismatch_diagnostic() {
	let case = TestCase::new(indoc! {"
        fn f(x: i32) {
            local y = match x {
                0 -> { x > 0 },
                _ -> { x },
            };
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 (TypeMistmatch) reused for mismatched arm types, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_match_enum_variant_marks_variant_used() {
	let case = TestCase::new(indoc! {"
        enum FileDescriptor: u8 {
            StdIn = 0,
            StdOut,
            StdErr,
        }
        fn name(fd: FileDescriptor) -> u8 {
            match fd {
                FileDescriptor::StdIn -> { 0 },
                _ -> { 1 },
            }
        }
        export { name }
    "});
	let errors: Vec<_> = case
		.tir
		.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.collect();
	assert!(errors.is_empty(), "{:?}", errors);
	let enum_ = case
		.tir
		.items
		.enums
		.iter()
		.find(|e| {
			case.graph.interner.resolve(e.name.inner) == Some("FileDescriptor")
		})
		.expect("FileDescriptor enum not found");
	let std_in = enum_
		.variants
		.iter()
		.find(|v| case.graph.interner.resolve(v.name.inner) == Some("StdIn"))
		.expect("StdIn variant not found");
	assert!(
		!std_in.accesses.is_empty(),
		"expected the match pattern `FileDescriptor::StdIn` to record a variant access"
	);
}

#[test]
fn test_match_duplicate_pattern_warns_unreachable() {
	let case = TestCase::new(indoc! {"
        fn f(x: i32) -> i32 {
            match x {
                0 -> { 1 },
                0 -> { 2 },
                _ -> { 3 },
            }
        }
        export { f }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnreachableMatchArm),
		"expected W1010 (UnreachableMatchArm) for a duplicate `0` pattern, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── generic type param bounded by an operator trait ─────────────────────────

#[test]
fn test_generic_type_param_bounded_by_add_dispatches() {
	let case = TestCase::new(indoc! {"
        pub fn add_generic<T: Add>(a: T, b: T) -> T {
            a + b
        }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_type_param_unbounded_operator_reports_diagnostic() {
	let case = TestCase::new(indoc! {"
        pub fn add_generic<T>(a: T, b: T) -> T {
            a + b
        }
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::BinaryOperatorCannotBeApplied
		),
		"expected E1008 (BinaryOperatorCannotBeApplied) for unbounded T + T, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_type_param_bounded_compound_assign_dispatches() {
	let case = TestCase::new(indoc! {"
        pub fn add_assign_generic<T: Add>(a: T, b: T) -> T {
            local mut x: T = a;
            x += b;
            x
        }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_type_param_bitand_bounded_compound_assign_dispatches() {
	let case = TestCase::new(indoc! {"
        pub fn and_assign_generic<T: BitAnd>(a: T, b: T) -> T {
            local mut x: T = a;
            x &= b;
            x
        }
    "});
	no_errors(&case);
}

#[test]
fn test_generic_type_param_unbounded_compound_assign_reports_diagnostic() {
	let case = TestCase::new(indoc! {"
        pub fn add_assign_generic<T>(a: T, b: T) -> T {
            local mut x: T = a;
            x += b;
            x
        }
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::BinaryOperatorCannotBeApplied
		),
		"expected E1008 (BinaryOperatorCannotBeApplied) for unbounded T += T, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

// ── struct operator-trait impls ─────────────────────────────────────────────
//
// Every `impl Add for X` exercised above (and in `std/main.wx` itself) is for
// a primitive. `ImplTarget::from_type` (`tir/mod.rs`) treats `Type::Struct`
// as an equally valid dispatch target via the same `find_trait_impl` lookup,
// but nothing previously exercised that path — these are the first tests to
// implement an operator trait for a user-defined struct rather than a
// primitive.

#[test]
fn test_struct_impl_add_dispatches() {
	let case = TestCase::new(indoc! {"
        struct Vec2 { x: i32, y: i32 }

        impl Add for Vec2 {
            fn add(self: Self, rhs: Self) -> Self {
                Vec2::{ x: self.x + rhs.x, y: self.y + rhs.y }
            }
        }

        pub fn add_vec2(a: Vec2, b: Vec2) -> Vec2 {
            a + b
        }
    "});
	no_errors(&case);
}

#[test]
fn test_struct_operator_dispatch_records_goto_definition_access() {
	// Mirrors `test_export_const_reports_cannot_export_and_records_access`'s
	// use of `accesses` to verify LSP hover/go-to-definition — except here
	// dispatch succeeds, so the check is that the `+` operator's own span
	// was recorded against the resolved `Vec2::add` method, exactly as the
	// prior conversation's hover/go-to-def-on-operators behavior requires.
	let case = TestCase::new(indoc! {"
        struct Vec2 { x: i32, y: i32 }

        impl Add for Vec2 {
            #[tag = \"vec2_add\"]
            fn add(self: Self, rhs: Self) -> Self {
                Vec2::{ x: self.x + rhs.x, y: self.y + rhs.y }
            }
        }

        pub fn add_vec2(a: Vec2, b: Vec2) -> Vec2 {
            a + b
        }
    "});
	no_errors(&case);

	let add_tag = case.graph.interner.get("vec2_add").unwrap();
	let add_def_id = *case.tir.items.tagged_items.get(&add_tag).unwrap();
	let add_index = case.tir.items.function_index(add_def_id).unwrap();

	assert_eq!(
		case.tir.items.functions[usize::from(add_index)]
			.accesses
			.len(),
		1,
		"the `+` in `a + b` must be recorded as a go-to-definition access on \
		 Vec2's `add` method, the same way an ordinary `.add()` method call \
		 would be"
	);
}

#[test]
fn test_struct_without_operator_impl_reports_diagnostic() {
	let case = TestCase::new(indoc! {"
        struct Vec2 { x: i32, y: i32 }

        pub fn add_vec2(a: Vec2, b: Vec2) -> Vec2 {
            a + b
        }
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::BinaryOperatorCannotBeApplied
		),
		"expected E1008 (BinaryOperatorCannotBeApplied) for `Vec2 + Vec2` \
		 with no `Add` impl, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_struct_operator_impl_does_not_grant_other_operators() {
	// Implementing `Add` for a struct must not make `Mul` (or any other
	// operator trait) resolve too — each operator dispatches through its own
	// trait independently (`OperatorTraits::for_op`); there is no
	// "implements one, gets all" fallback.
	let case = TestCase::new(indoc! {"
        struct Vec2 { x: i32, y: i32 }

        impl Add for Vec2 {
            fn add(self: Self, rhs: Self) -> Self {
                Vec2::{ x: self.x + rhs.x, y: self.y + rhs.y }
            }
        }

        pub fn mul_vec2(a: Vec2, b: Vec2) -> Vec2 {
            a * b
        }
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::BinaryOperatorCannotBeApplied
		),
		"expected E1008 (BinaryOperatorCannotBeApplied) for `Vec2 * Vec2` \
		 when only `Add` (not `Mul`) is implemented, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_struct_impl_neg_dispatches() {
	let case = TestCase::new(indoc! {"
        struct Vec2 { x: i32, y: i32 }

        impl Neg for Vec2 {
            fn neg(self: Self) -> Self {
                Vec2::{ x: -self.x, y: -self.y }
            }
        }

        pub fn neg_vec2(a: Vec2) -> Vec2 {
            -a
        }
    "});
	no_errors(&case);
}

#[test]
fn test_struct_compound_assignment_dispatches_to_add_method() {
	let case = TestCase::new(indoc! {"
        struct Vec2 { x: i32, y: i32 }

        impl Add for Vec2 {
            fn add(self: Self, rhs: Self) -> Self {
                Vec2::{ x: self.x + rhs.x, y: self.y + rhs.y }
            }
        }

        pub fn add_assign_vec2(mut a: Vec2, b: Vec2) -> Vec2 {
            a += b;
            a
        }
    "});
	no_errors(&case);
}

#[test]
fn test_struct_compound_assignment_dispatches_to_bitand_method() {
	let case = TestCase::new(indoc! {"
        struct Flags { bits: i32 }

        impl BitAnd for Flags {
            fn bitand(self: Self, rhs: Self) -> Self {
                Flags::{ bits: self.bits & rhs.bits }
            }
        }

        pub fn and_assign_flags(mut a: Flags, b: Flags) -> Flags {
            a &= b;
            a
        }
    "});
	no_errors(&case);
}

// ── struct bitwise operator-trait impls
// ──────────────────────────────────────
//
// `BitAnd`/`BitOr`/`BitXor`/`Shl`/`Shr` dispatch through the same
// `OperatorTraits`/`build_operator_dispatch` machinery as arithmetic once a
// struct is involved (`build_bitwise_result`, `tir/builder.rs`) — primitives
// keep the pre-existing native fast path (see `is_integer()`/`== BOOL`
// checks there), so these tests only need to cover the struct side; the
// primitive side is unchanged and already covered by every existing
// bitwise-on-primitive test.

#[test]
fn test_struct_impl_bitand_dispatches() {
	let case = TestCase::new(indoc! {"
        struct Flags { bits: i32 }

        impl BitAnd for Flags {
            fn bitand(self: Self, rhs: Self) -> Self {
                Flags::{ bits: self.bits & rhs.bits }
            }
        }

        pub fn and_flags(a: Flags, b: Flags) -> Flags {
            a & b
        }
    "});
	no_errors(&case);
}

#[test]
fn test_struct_without_bitand_impl_reports_diagnostic() {
	// Same type on both sides but no `BitAnd` impl — before
	// `build_bitwise_result` existed this fell through to the generic
	// "type mismatch" catch-all (misleading, since the types *do* match);
	// it must now report the accurate "operator cannot be applied" code,
	// exactly like the arithmetic path already does.
	let case = TestCase::new(indoc! {"
        struct Flags { bits: i32 }

        pub fn and_flags(a: Flags, b: Flags) -> Flags {
            a & b
        }
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::BinaryOperatorCannotBeApplied
		),
		"expected E1008 (BinaryOperatorCannotBeApplied) for `Flags & Flags` \
		 with no `BitAnd` impl, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_struct_bitand_impl_does_not_grant_other_bitwise_operators() {
	let case = TestCase::new(indoc! {"
        struct Flags { bits: i32 }

        impl BitAnd for Flags {
            fn bitand(self: Self, rhs: Self) -> Self {
                Flags::{ bits: self.bits & rhs.bits }
            }
        }

        pub fn or_flags(a: Flags, b: Flags) -> Flags {
            a | b
        }
    "});
	assert!(
		has_error_code(
			&case.tir,
			DiagnosticCode::BinaryOperatorCannotBeApplied
		),
		"expected E1008 (BinaryOperatorCannotBeApplied) for `Flags | Flags` \
		 when only `BitAnd` (not `BitOr`) is implemented, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_bitand_bound_dispatches() {
	let case = TestCase::new(indoc! {"
        pub fn and_it<T: BitAnd>(a: T, b: T) -> T {
            a & b
        }

        pub fn use_and(a: i32, b: i32) -> i32 {
            and_it(a, b)
        }
    "});
	no_errors(&case);
}

// ── struct `BitNot` overload (unary `^`) ────────────────────────────────────
//
// `^x` reuses the same dispatch machinery as `-x` (`Neg`) —
// `build_unary_operator_dispatch`, generalized via `OperatorTraits::
// for_unary_op` — gated the same way the binary bitwise operators are:
// primitives/typeset-bounded types keep the pre-existing native fast path
// (`build_unary_expression`'s `is_primitive()` check, unchanged), only a
// struct falls through to real dispatch.

#[test]
fn test_struct_impl_bitnot_dispatches() {
	let case = TestCase::new(indoc! {"
        struct Flags { bits: i32 }

        impl BitNot for Flags {
            fn bitnot(self: Self) -> Self {
                Flags::{ bits: ^self.bits }
            }
        }

        pub fn not_flags(a: Flags) -> Flags {
            ^a
        }
    "});
	no_errors(&case);
}

#[test]
fn test_struct_without_bitnot_impl_reports_diagnostic() {
	let case = TestCase::new(indoc! {"
        struct Flags { bits: i32 }

        pub fn not_flags(a: Flags) -> Flags {
            ^a
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnaryOperatorCannotBeApplied),
		"expected E1010 (UnaryOperatorCannotBeApplied) for `^Flags` with \
		 no `BitNot` impl, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_struct_bitnot_impl_does_not_grant_neg() {
	// Implementing `BitNot` for a struct must not make `Neg` resolve too
	// — each unary operator dispatches through its own trait
	// independently (`OperatorTraits::for_unary_op`), no "implements one,
	// gets all" fallback, mirroring the binary operators' equivalent test.
	let case = TestCase::new(indoc! {"
        struct Flags { bits: i32 }

        impl BitNot for Flags {
            fn bitnot(self: Self) -> Self {
                Flags::{ bits: ^self.bits }
            }
        }

        pub fn neg_flags(a: Flags) -> Flags {
            -a
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UnaryOperatorCannotBeApplied),
		"expected E1010 (UnaryOperatorCannotBeApplied) for `-Flags` when \
		 only `BitNot` (not `Neg`) is implemented, got: {:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_generic_bitnot_bound_dispatches() {
	// `build_unary_operator_dispatch` now has a `Type::TypeParam` branch
	// mirroring the binary `build_operator_dispatch` — a bare type param
	// bounded by `BitNot` dispatches through `resolve_bounded_operator_method`
	// instead of failing with "operator cannot be applied".
	let case = TestCase::new(indoc! {"
        pub fn not_it<T: BitNot>(a: T) -> T {
            ^a
        }

        pub fn use_not(a: i32) -> i32 {
            not_it(a)
        }
    "});
	assert!(
		!case
			.tir
			.diagnostics
			.iter()
			.any(|d| d.severity == Severity::Error),
		"{:?}",
		case.tir
			.diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);
}

#[test]
fn test_deref_of_error_type_does_not_repeat_diagnostic() {
	// The `{unknown}` type means an error was already reported for this
	// binding; dereferencing it must absorb that rather than piling an
	// E1037 on top.
	let case = TestCase::new(indoc! {"
        fn bad() { local p = nonexistent(); p.* = 1; }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"expected the original E1007 (undeclared identifier)"
	);
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::CannotDerefNonPointer),
		"E1037 should be absorbed when the operand is already `{{unknown}}`"
	);
}

#[test]
fn test_deref_of_error_type_still_checks_the_assigned_value() {
	// A deref whose operand is already `{unknown}` absorbs its own
	// diagnostic, but must not swallow the rest of the statement with it —
	// the right-hand side still gets built, so its own errors surface.
	for src in [
		"fn bad() { local p = nonexistent(); p.* = also_missing(); }",
		"fn bad() { local p = nonexistent(); p.* += also_missing(); }",
		"fn bad() { local p = nonexistent(); p.*.field = also_missing(); }",
	] {
		let case = TestCase::new(src);
		let undeclared = case
			.tir
			.diagnostics
			.iter()
			.filter(|d| {
				d.code.as_deref()
					== Some(DiagnosticCode::UndeclaredIdentifier.code())
			})
			.count();
		assert_eq!(
			undeclared, 2,
			"expected E1007 for both `nonexistent` and `also_missing` in `{src}`"
		);
		assert!(
			!has_error_code(&case.tir, DiagnosticCode::CannotDerefNonPointer),
			"E1037 should be absorbed in `{src}`"
		);
		assert!(
			!has_error_code(&case.tir, DiagnosticCode::InvalidAssignmentTarget),
			"E1013 should not cascade off an already-errored target in `{src}`"
		);
	}
}

#[test]
fn test_unresolved_callee_still_checks_its_arguments() {
	// A callee that doesn't resolve leaves no signature to check arguments
	// against, but must not swallow the argument list with it — errors
	// *inside* the arguments still have to surface.
	for (src, args) in [
		// method not found
		(
			"struct S {} fn f(s: S) { s.nope(missing_a(), missing_b()); }",
			2,
		),
		// resolves, but to a field rather than a method
		("struct S { x: i32 } fn f(s: S) { s.x(missing_a()); }", 1),
		// associated function that doesn't exist
		("struct S {} fn f() { S::nope(missing_a()); }", 1),
	] {
		let case = TestCase::new(src);
		let undeclared = case
			.tir
			.diagnostics
			.iter()
			.filter(|d| {
				d.code.as_deref()
					== Some(DiagnosticCode::UndeclaredIdentifier.code())
					&& d.message == "undeclared identifier"
			})
			.count();
		assert_eq!(
			undeclared, args,
			"expected E1007 for each unresolved argument in `{src}`"
		);
	}
}

#[test]
fn test_unresolved_callee_does_not_demand_a_type_annotation() {
	// The missing callee is what removed the inference context, so asking
	// the user to annotate their way out of it misdirects. Both the method
	// and the plain-call path must stay quiet.
	for src in [
		"struct S {} fn f<T>(s: S) { local p = s.nope(Layout::of::<T>()); }",
		"struct S {} fn f<T>() { local p = nope(Layout::of::<T>()); }",
	] {
		let case = TestCase::new(src);
		assert!(
			!has_error_code(&case.tir, DiagnosticCode::TypeAnnotationRequired),
			"E1002 should be absorbed in a poisoned context: `{src}`"
		);
	}
}

#[test]
fn test_poisoned_context_still_reports_mismatch_between_sibling_arguments() {
	// Guards the ordering in `build_generic_call_arguments`: the slots are
	// poisoned *after* argument inference, so `T` is still bound to `i32`
	// by `a` and `b: bool` is still a real mismatch. Poisoning any earlier
	// checks both arguments against `ERROR` and loses this silently.
	let case = TestCase::new(indoc! {"
        struct S {}
        fn same<T>(a: T, b: T) -> T { a }
        fn f(s: S) { local p = s.missing(same(1 as i32, true)); }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::MethodNotFound),
		"expected E1049 for the unresolved method"
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::TypeMistmatch),
		"expected E1001 for `true` against `T = i32` inferred from `a`"
	);
}

#[test]
fn test_poisoned_deref_store_records_rhs_access_for_hover() {
	// The editor-visible half of the deref fix. `SymbolIndex` is built from
	// `local.accesses`, which are pushed while an identifier expression is
	// built — so a right-hand side that never gets built has no access, and
	// hovering it shows nothing at all. Before the fix this was 0.
	//
	// Distinct from `test_deref_of_error_type_still_checks_the_assigned_value`:
	// that asserts the RHS produces diagnostics, this asserts it leaves the
	// index entry behind. Nothing else in the suite covers the latter.
	let case = TestCase::new(
		"fn bad(value: i32) { local p = nonexistent(); p.* = value; }",
	);
	let function = case
		.tir
		.items
		.functions
		.iter()
		.find(|f| case.graph.interner.resolve(f.name.inner) == Some("bad"))
		.expect("`bad` should be registered");
	let body = function.body.as_ref().expect("`bad` should have a body");
	let value = body.stack.scopes[0]
		.locals
		.iter()
		.find(|l| case.graph.interner.resolve(l.name.inner) == Some("value"))
		.expect("`value` param should be a scope-0 local");
	assert_eq!(
		value.accesses.len(),
		1,
		"the `value` on the right-hand side must record an access, or hover \
		 over it returns nothing"
	);
}

// ── local pattern destructuring ──────────────────────────────────────────

/// Every error-severity diagnostic, rendered for assertion messages.
fn error_messages(tir: &TIR) -> Vec<String> {
	tir.diagnostics
		.iter()
		.filter(|d| d.severity == Severity::Error)
		.map(|d| format!("{:?}: {}", d.code, d.message))
		.collect()
}

fn assert_no_errors(case: &TestCase) {
	let errors = error_messages(&case.tir);
	assert!(errors.is_empty(), "unexpected errors: {:#?}", errors);
}

#[test]
fn test_tuple_destructuring_binds_each_element() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) -> i32 {
            local (a, b) = pair;
            a + b
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_tuple_destructuring_nested() {
	let case = TestCase::new(indoc! {"
        fn f(nested: (i32, (i32, i32))) -> i32 {
            local (x, (y, z)) = nested;
            x + y + z
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_tuple_destructuring_arity_mismatch_errors() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) -> i32 {
            local (a, b, c) = pair;
            a + b + c
        }
        export { f }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

#[test]
fn test_tuple_pattern_on_non_tuple_errors() {
	let case = TestCase::new(indoc! {"
        fn f(x: i32) -> i32 {
            local (a, b) = x;
            a + b
        }
        export { f }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

/// A shape mismatch must still bind every name in the pattern, or each later
/// use of them reports a second, spurious "undeclared identifier".
#[test]
fn test_failed_tuple_pattern_still_binds_names() {
	let case = TestCase::new(indoc! {"
        fn f(x: i32) -> i32 {
            local (a, b) = x;
            a + b
        }
        export { f }
    "});
	assert!(
		!has_error_code(&case.tir, DiagnosticCode::UndeclaredIdentifier),
		"names bound by a failed pattern must still resolve: {:#?}",
		error_messages(&case.tir)
	);
}

#[test]
fn test_tuple_destructuring_untyped_literal_requires_annotation() {
	// Same rule as `local x = 1;` — an untyped literal never picks a type on
	// its own, and a tuple of them must not sneak past it.
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local (a, b) = (1, 2);
            a + b
        }
        export { f }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::TypeAnnotationRequired
	));
}

#[test]
fn test_tuple_destructuring_with_annotation_coerces_literals() {
	let case = TestCase::new(indoc! {"
        fn f() -> i32 {
            local (a, b): (i32, i32) = (1, 2);
            a + b
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_destructured_binding_mutability_is_per_binding() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) -> i32 {
            local (mut a, b) = pair;
            a = a + b;
            a
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_destructured_immutable_binding_cannot_be_assigned() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) -> i32 {
            local (a, b) = pair;
            a = b;
            a
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::CannotMutateImmutable.code())),
		"assigning to a non-`mut` destructured binding must be rejected"
	);
}

/// `_` inside a pattern binds nothing, so it must not trip the unused-local
/// lint the way a real unused name does.
#[test]
fn test_wildcard_in_tuple_pattern_is_not_an_unused_local() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) -> i32 {
            local (a, _) = pair;
            a
        }
        export { f }
    "});
	assert_no_errors(&case);
	assert!(
		!case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedVariable.code())),
		"`_` binds nothing, so there is no local to be unused"
	);
}

#[test]
fn test_unused_destructured_binding_still_warns() {
	let case = TestCase::new(indoc! {"
        fn f(pair: (i32, i32)) -> i32 {
            local (a, b) = pair;
            a
        }
        export { f }
    "});
	assert!(
		case.tir.diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::UnusedVariable.code())),
		"`b` is a real binding that is never read"
	);
}

#[test]
fn test_top_level_wildcard_local_is_accepted() {
	let case = TestCase::new(indoc! {"
        fn g() -> i32 { 1 }
        fn f() -> i32 {
            local _ = g();
            2
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_struct_destructuring_shorthand_and_renamed() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32 }
        fn f(p: Point) -> i32 {
            local Point::{ x, y } = p;
            local Point::{ x: a, y: b } = p;
            x + y + a + b
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_struct_destructuring_missing_field_errors() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32 }
        fn f(p: Point) -> i32 {
            local Point::{ x } = p;
            x
        }
        export { f }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::MissingStructFields
	));
}

#[test]
fn test_struct_destructuring_rest_allows_omitted_fields() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32, z: i32 }
        fn f(p: Point) -> i32 {
            local Point::{ x, .. } = p;
            x
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_struct_destructuring_unknown_field_errors() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32 }
        fn f(p: Point) -> i32 {
            local Point::{ x, y, w } = p;
            x
        }
        export { f }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::UnknownStructField
	));
}

#[test]
fn test_struct_destructuring_duplicate_field_errors() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32 }
        fn f(p: Point) -> i32 {
            local Point::{ x, x: other, y } = p;
            x + other
        }
        export { f }
    "});
	assert!(has_error_code(
		&case.tir,
		DiagnosticCode::DuplicateStructFieldInit
	));
}

#[test]
fn test_struct_pattern_naming_the_wrong_struct_errors() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32 }
        struct Size { x: i32, y: i32 }
        fn f(p: Point) -> i32 {
            local Size::{ x, y } = p;
            x + y
        }
        export { f }
    "});
	assert!(has_error_code(&case.tir, DiagnosticCode::TypeMistmatch));
}

#[test]
fn test_struct_destructuring_nested_in_tuple() {
	let case = TestCase::new(indoc! {"
        struct Point { x: i32, y: i32 }
        fn f(pair: (Point, i32)) -> i32 {
            local (Point::{ x, y }, n) = pair;
            x + y + n
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_struct_destructuring_generic_substitutes_field_types() {
	let case = TestCase::new(indoc! {"
        struct Pair<T> { first: T, second: T }
        fn f(p: Pair<i64>) -> i64 {
            local Pair::{ first, second } = p;
            first + second
        }
        export { f }
    "});
	assert_no_errors(&case);
}

#[test]
fn test_struct_destructuring_across_modules() {
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod geom;
            fn f(p: geom::Point) -> i32 {
                local geom::Point::{ x, y } = p;
                x + y
            }
            export { f }
        "},
		&[("src/geom.wx", "pub struct Point { pub x: i32, pub y: i32 }")],
	);
	assert_no_errors(&case);
}

// ── inherent impl locality ─────────────────────────────────────────────────

#[test]
fn test_inherent_impl_on_type_from_another_package_rejected() {
	let case = TestCase::new_with_dependency(
		indoc! {"
            impl dep::Point {
                pub fn sum(self) -> i32 { self.x + self.y }
            }
        "},
		"pub struct Point { pub x: i32, pub y: i32 }",
	);
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ForeignImplTarget),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_trait_impl_on_type_from_another_package_allowed() {
	// The escape hatch the diagnostic points at: a trait impl may target a
	// foreign type, and stays governed by its own one-impl-per-type rule.
	let case = TestCase::new_with_dependency(
		indoc! {"
            trait Sum {
                fn sum(self) -> i32;
            }

            impl Sum for dep::Point {
                fn sum(self) -> i32 { self.x + self.y }
            }
        "},
		"pub struct Point { pub x: i32, pub y: i32 }",
	);
	assert_no_errors(&case);
}

#[test]
fn test_inherent_impl_from_another_module_of_the_same_package_allowed() {
	// The boundary is the package, not the module: `Point` is declared in a
	// submodule and implemented from the root, both inside the root package.
	let case = TestCase::new_multi_file(
		"src/main.wx",
		indoc! {"
            mod geom;

            impl geom::Point {
                pub fn sum(self) -> i32 { self.x + self.y }
            }
        "},
		&[("src/geom.wx", "pub struct Point { pub x: i32, pub y: i32 }")],
	);
	assert_no_errors(&case);
}

#[test]
fn test_inherent_impl_on_primitive_rejected_outside_stdlib() {
	// `i32` is declared by `std/main.wx` (`#[intrinsic] pub type i32;`), so
	// its inherent impls are the stdlib's alone.
	let case = TestCase::new(indoc! {"
        impl i32 {
            pub fn double(self) -> i32 { self * 2 }
        }
    "});
	assert!(
		has_error_code(&case.tir, DiagnosticCode::ForeignImplTarget),
		"{:?}",
		case.tir.diagnostics
	);
}

#[test]
fn test_inherent_impl_on_slice_rejected_outside_stdlib() {
	// Nothing declares a slice type, so no package can claim to define one —
	// which leaves the stdlib, where every other built-in lives, as the only
	// place an inherent impl for one may be written. The trait impl beside it
	// is legal, so exactly one diagnostic is expected.
	let case = TestCase::new(indoc! {"
        memory heap: Memory where { Size = u32 };

        trait Counter {
            fn count(self) -> u32;
        }

        impl<M: Memory, T> M::&[T] {
            pub fn count(self) -> u32 { 0 }
        }

        impl Counter for heap::&[i32] {
            fn count(self) -> u32 { 0 }
        }
    "});
	assert_eq!(
		case.tir
			.diagnostics
			.iter()
			.filter(|d| d.code.as_deref()
				== Some(DiagnosticCode::ForeignImplTarget.code()))
			.count(),
		1,
		"only the inherent impl should be rejected: {:?}",
		case.tir.diagnostics
	);
}
