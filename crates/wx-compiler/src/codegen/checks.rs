//! Migration checks, independent of backend-selection environment flags.
//! Run with `cargo test -p wx-compiler --lib codegen::checks -- --nocapture`.

mod reachability;

use super::*;
use crate::testing::DiagnosticView;
use crate::vfs;

fn lower(source: &str) -> (ast::StringInterner, mir::MIR) {
	let mut strings = crate::symbols::Keyword::create_interner();
	let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
	builder.load_core();
	let root = builder
		.load_package(
			vfs::AbsolutePath::new("/main.wx"),
			&vfs::VirtualFileSource::from_relative(
				std::collections::HashMap::from([(
					"main.wx".to_string(),
					source.to_string(),
				)]),
			),
		)
		.unwrap();
	let unit = builder.build(root);
	let mut sema = crate::tir::check(&unit, &mut strings);
	let mir = crate::tir::lower(&mut sema, &strings).ok();
	let diagnostics = sema.diagnostics();
	DiagnosticView::new("tir", &diagnostics, &unit.files).assert_no_errors();
	(strings, mir.expect("source lowers"))
}

#[derive(Clone, Copy, Debug)]
enum Mode {
	Direct,
	Graph,
	GraphWithTee,
}

fn compile(
	mir: &mut mir::MIR,
	strings: &ast::StringInterner,
	mode: Mode,
) -> WasmModule {
	if matches!(mode, Mode::Graph | Mode::GraphWithTee) {
		crate::opt::optimize_reachable(mir);
	}
	let schedule: fn(&mir::MIR, mir::FunctionId) -> wasm::Function = match mode
	{
		Mode::GraphWithTee => |mir, id| {
			let mut function = linearize::linearize(mir, mir.code(id));
			wasm::peephole_local_tee(&mut function.body);
			function
		},
		_ => |mir, id| linearize::linearize(mir, mir.code(id)),
	};
	Builder::build_with(
		mir,
		strings,
		&Reachability::collect_for_tests(mir),
		schedule,
	)
	.expect("module encodes")
}

/// Report actual module bytes and declared non-parameter Wasm locals.
/// These are observations, not size budgets or runtime benchmarks.
#[test]
fn compare_emitter_size_locals_and_execution() {
	let corpus = [
		("arithmetic", "", "(n + x) * (n + x) + (n - x)"),
		("if", "", "if n == 0 { (x + 1) * 2 } else { (x + 1) * 3 }"),
		(
			"switch",
			"",
			"match n { 0 => { x + 10 }, 1 => { x + 20 }, 2 => { x + 30 }, _ => { x + 40 } }",
		),
		(
			"swap_loop",
			"",
			"local mut a = x; local mut b = x + 7; local mut i: i32 = 0; loop { if i == n { break; }; local old = a; a = b; b = old; i += 1; }; a * 100 + b",
		),
		(
			"nested_loops",
			"",
			"local mut i: i32 = 0; local mut sum = x; loop :outer { if i == n { break; }; local mut j: i32 = 0; loop { sum += i + j; j += 1; if j == 2 { i += 1; continue :outer; }; }; }; sum",
		),
		(
			"calls",
			"func helper(x: i32) -> i32 { (x + 1) * (x + 2) }",
			"helper(n) + helper(x)",
		),
	];
	let engine = wasmtime::Engine::default();
	println!("case,mode,module_bytes,non_param_locals,defined_functions");
	for (name, helpers, body) in corpus {
		let source = format!(
			"{helpers}\nfunc run(n: i32, x: i32) -> i32 {{ {body} }}\nexport {{ run as \"run\" }}"
		);
		let mut reference = None;
		for mode in [Mode::Direct, Mode::Graph, Mode::GraphWithTee] {
			let (strings, mut mir) = lower(&source);
			mir::inline::run(&mut mir, mir::inline::Policy::DEFAULT);
			let module = compile(&mut mir, &strings, mode);
			let locals: usize = module
				.code
				.functions
				.iter()
				.zip(&module.functions.types)
				.map(|(body, signature)| {
					body.locals.len()
						- module.types.signatures[signature.0 as usize]
							.param_count
				})
				.sum();
			let bytes = module.encode();
			println!(
				"{name},{mode:?},{},{locals},{}",
				bytes.len(),
				module.code.functions.len()
			);
			let module =
				wasmtime::Module::new(&engine, &bytes).expect("valid Wasm");
			let mut store = wasmtime::Store::new(&engine, ());
			let instance =
				wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
			let run = instance
				.get_typed_func::<(i32, i32), i32>(&mut store, "run")
				.unwrap();
			let outputs: Vec<_> = (0..6)
				.flat_map(|n| [-17, 0, 31].map(|x| (n, x)))
				.map(|args| run.call(&mut store, args).unwrap())
				.collect();
			match &reference {
				None => reference = Some(outputs),
				Some(expected) => {
					assert_eq!(&outputs, expected, "{name}, {mode:?}")
				}
			}
		}
	}
}

/// Per-function emission removes dead call nodes while preserving MIR item IDs.
#[test]
fn graph_emission_removes_dead_calls_without_changing_item_ids() {
	let source = r#"
		func helper(x: i32) -> i32 { (x + 1) * (x + 2) }
		func run(n: i32, x: i32) -> i32 {
			return x;
			helper(n) + helper(x)
		}
		export { run as "run" }
	"#;
	for inline in [false, true] {
		let (strings, mut mir) = lower(source);
		// ATTRIBUTE_ONLY keeps helper calls in the arena until graph construction.
		if inline {
			mir::inline::run(&mut mir, mir::inline::Policy::ATTRIBUTE_ONLY);
		}
		assert_eq!(
			mir.functions.len(),
			2,
			"inlining preserves both MIR entries"
		);
		crate::opt::emit_for_tests(&mut mir);
		assert_eq!(
			mir.functions.len(),
			2,
			"per-function emission does not run module DCE"
		);
		assert!(
			mir.functions
				.iter()
				.filter_map(|function| function.code())
				.all(|code| code.callees().next().is_none())
		);
		let module = Builder::build_linearized(&mir, &strings).unwrap();
		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, module.encode()).unwrap();
		let mut store = wasmtime::Store::new(&engine, ());
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (3, 41)).unwrap(), 41);
	}
}

/// Discovery reads the replacement caller before deciding whether to process
/// its callee. Exercise the public driver, then force the direct linearizer.
#[test]
fn reachability_skips_a_removed_callee_and_the_program_still_executes() {
	let source = r#"
		func helper(x: i32) -> i32 { (x + 1) * (x + 2) }
		func run(n: i32, x: i32) -> i32 {
			return x;
			helper(n) + helper(x)
		}
		export { run as "run" }
	"#;
	for inline in [false, true] {
		let (strings, mut mir) = lower(source);
		if inline {
			mir::inline::run(&mut mir, mir::inline::Policy::ATTRIBUTE_ONLY);
		}
		let mir::Item::Function(caller) = mir.exports[0].item else {
			panic!("run is an exported function");
		};
		let callee = mir.code(caller).callees().next().unwrap();
		let callee_nodes = mir.code(callee).body.kinds().as_ptr();
		let callee_before = format!("{:?}", mir.code(callee).body.kinds());
		let reached = crate::opt::optimize_reachable(&mut mir);
		assert!(reached.is_reachable(mir::references::Reference::Item(
			mir::Item::Function(caller)
		)));
		assert!(!reached.is_reachable(mir::references::Reference::Item(
			mir::Item::Function(callee)
		)));
		assert!(mir.code(caller).callees().next().is_none());
		assert_eq!(mir.code(callee).body.kinds().as_ptr(), callee_nodes);
		assert_eq!(
			format!("{:?}", mir.code(callee).body.kinds()),
			callee_before
		);
		assert_eq!(mir.functions.len(), 2, "MIR tables keep their stable IDs");
		let module = Builder::build(&mir, &strings, &reached).unwrap();
		assert_eq!(module.code.functions.len(), 1);
		assert_eq!(module.functions.types.len(), 1);
		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, module.encode()).unwrap();
		let mut store = wasmtime::Store::new(&engine, ());
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		for input in [0, 41, i32::MIN, i32::MAX] {
			assert_eq!(run.call(&mut store, (3, input)).unwrap(), input);
		}
	}
}
