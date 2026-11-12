//! Execute graph emission through the MIR linearizer, with no old
//! optimizer between the emitted body and Wasm. The direct original MIR is
//! the execution reference, including observable traps of unused loads.

use super::*;
use crate::mir::{ExprKind as E, ValueType as T};
use crate::opt;

fn run_mode(
	mut mir: mir::MIR,
	interner: &StringInterner,
	emitted: bool,
) -> (wasmtime::Store<()>, wasmtime::Instance) {
	let module = if emitted {
		crate::backend::emit(&mut mir, interner, None)
	} else {
		crate::codegen::Builder::build_linearized(&mir, interner)
	}
	.unwrap();
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	(store, instance)
}

fn shared_arithmetic(name: SymbolU32) -> mir::MIR {
	scalar_function(name, |f| {
		let x = f.local(0, T::I32);
		let y = f.local(1, T::I32);
		let left = f.binary(mir::BinaryOp::Add, x, y, T::I32);
		let x = f.local(0, T::I32);
		let y = f.local(1, T::I32);
		let right = f.binary(mir::BinaryOp::Add, x, y, T::I32);
		f.binary(mir::BinaryOp::Mul, left, right, T::I32)
	})
}

#[test]
fn optimizing_one_function_preserves_other_bodies_and_module_identity() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut mir = scalar_function(name, |f| {
		let x = f.local(0, T::I32);
		let y = f.local(1, T::I32);
		let left = f.binary(mir::BinaryOp::Add, x, y, T::I32);
		let x = f.local(0, T::I32);
		let y = f.local(1, T::I32);
		let right = f.binary(mir::BinaryOp::Add, x, y, T::I32);
		let square = f.binary(mir::BinaryOp::Mul, left, right, T::I32);
		let y = f.local(1, T::I32);
		let args = f.body.push_list([square, y]);
		f.push(
			E::Call {
				function: mir::FunctionId::new(1),
				args,
			},
			T::I32,
		)
	});
	let helper = scalar_add(name).functions.remove(0);
	mir.functions.push(helper);
	mir.function_flags.push(mir::FunctionFlags::INLINE);
	let caller = mir::FunctionId::new(0);
	let callee = mir::FunctionId::new(1);
	let signature = mir.function(caller).signature;
	let helper_nodes = mir.code(callee).body.kinds().as_ptr();
	let helper_before = format!("{:?}", mir.code(callee).body.kinds());
	let flags = mir.function_flags.clone();

	crate::opt::optimize_function(&mut mir, caller);

	assert_eq!(mir.functions.len(), 2);
	assert_eq!(mir.function(caller).signature, signature);
	assert_eq!(mir.function(callee).signature, signature);
	assert_eq!(mir.function_flags, flags);
	assert_eq!(mir.exports.len(), 1);
	assert_eq!(mir.exports[0].item, mir::Item::Function(caller));
	assert_eq!(mir.start_function, None);
	assert_eq!(mir.code(caller).callees().collect::<Vec<_>>(), [callee]);
	assert_eq!(mir.code(callee).body.kinds().as_ptr(), helper_nodes);
	assert_eq!(
		format!("{:?}", mir.code(callee).body.kinds()),
		helper_before
	);
	assert_eq!(mir.code(callee).locals.len(), 2);
	let mut references = Vec::new();
	mir.dependencies(
		mir::references::Reference::Item(mir::Item::Function(caller)),
		|reference| references.push(reference),
	);
	assert_eq!(
		references,
		[mir::references::Reference::Item(mir::Item::Function(
			callee
		))]
	);

	// The optimized caller executes against a callee that has not been
	// optimized. Its signature is sufficient; it need not run through the
	// graph pipeline first.
	let (mut store, instance) = run_mode(mir, &interner, false);
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	for (x, y) in [(3i32, 4i32), (i32::MAX, 1), (i32::MIN, -1)] {
		let sum = x.wrapping_add(y);
		assert_eq!(
			run.call(&mut store, (x, y)).unwrap(),
			sum.wrapping_mul(sum).wrapping_add(y)
		);
	}
}

#[test]
fn shared_arithmetic_is_materialized_once_and_executes_with_wrapping_values() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut mir = shared_arithmetic(name);
	opt::emit_for_tests(&mut mir);
	let code = mir.code(mir::FunctionId::new(0));
	assert_eq!(
		code.body
			.kinds()
			.iter()
			.filter(|kind| matches!(
				kind,
				E::Binary {
					op: mir::BinaryOp::Add,
					..
				}
			))
			.count(),
		1
	);
	assert_eq!(
		code.locals.len(),
		3,
		"two parameters and one shared computation"
	);
	for emitted in [false, true] {
		let (mut store, instance) =
			run_mode(shared_arithmetic(name), &interner, emitted);
		let function = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		for (x, y) in [(3i32, 4i32), (-7, 2), (i32::MAX, 1), (i32::MIN, -1)] {
			let sum = x.wrapping_add(y);
			assert_eq!(
				function.call(&mut store, (x, y)).unwrap(),
				sum.wrapping_mul(sum)
			);
		}
	}
}

fn add_counter(mir: &mut mir::MIR, name: SymbolU32) {
	let id = mir::GlobalId::new(0);
	mir.globals.push(mir::Global {
		id,
		ty: T::I32,
		mutability: mir::Mutability::Mutable,
		origin: mir::Origin::Defined(mir::ConstInit::Int(0)),
	});
	mir.exports.push(mir::Export {
		name,
		item: mir::Item::Global(id),
	});
}

fn partial_call_results(name: SymbolU32, counter_name: SymbolU32) -> mir::MIR {
	let mut signatures = mir::Signatures::default();
	let results = [T::I32, T::I64, T::I32];
	let aggregate = signatures.value_of(&results);
	let callee_signature = signatures.intern(&[T::I32], &results);
	let caller_signature = signatures.intern(&[T::I32], &[T::I64]);
	let mut callee = Fixture::new(&[T::I32]);
	let counter = callee.push(
		E::Global {
			id: mir::GlobalId::new(0),
		},
		T::I32,
	);
	let one = callee.int(1, T::I32);
	let next = callee.binary(mir::BinaryOp::Add, counter, one, T::I32);
	let update = callee.push(
		E::GlobalSet {
			id: mir::GlobalId::new(0),
			value: next,
		},
		T::Unit,
	);
	let first = callee.local(0, T::I32);
	let middle = callee.int(1 << 40, T::I64);
	let last = callee.local(0, T::I32);
	let one = callee.int(1, T::I32);
	let last = callee.binary(mir::BinaryOp::Add, last, one, T::I32);
	let values = callee.body.push_list([first, middle, last]);
	let values = callee.push(E::Values { values }, aggregate);
	let callee_root = callee.sequence([update, values], aggregate);
	let mut caller = Fixture::new(&[T::I32, T::I64, T::I32]);
	let input = caller.local(0, T::I32);
	let args = caller.body.push_list([input]);
	let ignored_call = caller.push(
		E::Call {
			function: mir::FunctionId::new(1),
			args,
		},
		aggregate,
	);
	let ignored = caller.push(
		E::Drop {
			value: ignored_call,
		},
		T::Unit,
	);
	let input = caller.local(0, T::I32);
	let args = caller.body.push_list([input]);
	let call = caller.push(
		E::Call {
			function: mir::FunctionId::new(1),
			args,
		},
		aggregate,
	);
	let targets = caller.body.push_targets([
		None,
		Some(mir::LocalIndex::new(1)),
		Some(mir::LocalIndex::new(2)),
	]);
	let capture = caller.push(
		E::SetLocals {
			targets,
			value: call,
		},
		T::Unit,
	);
	let middle = caller.local(1, T::I64);
	let last = caller.local(2, T::I32);
	let last = caller.push(
		E::Convert {
			op: mir::ConvertOp::ExtendS,
			value: last,
		},
		T::I64,
	);
	let sum = caller.binary(mir::BinaryOp::Add, middle, last, T::I64);
	let root = caller.sequence([ignored, capture, sum], T::I64);
	let mut mir = module(
		vec![
			caller.finish(caller_signature, root),
			callee.finish(callee_signature, callee_root),
		],
		signatures,
		export(name),
		Vec::new(),
	);
	add_counter(&mut mir, counter_name);
	mir
}

#[test]
fn mixed_call_outputs_are_captured_once_and_unused_outputs_are_dropped() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let counter = interner.get_or_intern("counter");
	for emitted in [false, true] {
		let (mut store, instance) =
			run_mode(partial_call_results(name, counter), &interner, emitted);
		let function = instance
			.get_typed_func::<i32, i64>(&mut store, "run")
			.unwrap();
		let counter = instance.get_global(&mut store, "counter").unwrap();
		for (iteration, x) in [7, -9, 1024].into_iter().enumerate() {
			assert_eq!(
				function.call(&mut store, x).unwrap(),
				(1i64 << 40) + x as i64 + 1
			);
			assert_eq!(
				counter.get(&mut store).i32(),
				Some(2 * (iteration as i32 + 1)),
				"both calls execute exactly once"
			);
		}
	}
}

fn unused_traps(name: SymbolU32, counter: SymbolU32) -> mir::MIR {
	let mut mir = scalar_function(name, |f| {
		let mut statements = Vec::new();
		for mark in 1..=3 {
			let value = f.int(mark, T::I32);
			statements.push(f.push(
				E::GlobalSet {
					id: mir::GlobalId::new(0),
					value,
				},
				T::Unit,
			));
			let value = match mark {
				1 => {
					let pointer = f.local(0, T::I32);
					f.push(
						E::PointerLoad {
							pointer,
							offset: 0,
							memory: mir::MemoryId::new(0),
							access: mir::LoadAccess::I32,
						},
						T::I32,
					)
				}
				2 => {
					let numerator = f.int(9, T::I32);
					let divisor = f.local(1, T::I32);
					f.binary(mir::BinaryOp::DivS, numerator, divisor, T::I32)
				}
				_ => continue,
			};
			statements.push(f.push(E::Drop { value }, T::Unit));
		}
		let result = f.int(7, T::I32);
		statements.push(f.ret(result));
		// This dead operation must not be resurrected by graph emission.
		statements.push(f.unreachable());
		f.sequence(statements, T::Never)
	});
	add_counter(&mut mir, counter);
	mir.memories.push(mir::MemoryInfo {
		id: mir::MemoryId::new(0),
		kind: mir::MemoryKind::Memory32,
		min_pages: Some(1),
		max_pages: None,
		origin: mir::Origin::Defined(()),
	});
	mir
}

#[test]
fn unused_loads_and_divisions_preserve_traps_and_global_write_order() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let counter = interner.get_or_intern("counter");
	for emitted in [false, true] {
		let (mut store, instance) =
			run_mode(unused_traps(name, counter), &interner, emitted);
		let function = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		let counter = instance.get_global(&mut store, "counter").unwrap();
		for (args, expected_mark, expected_trap) in [
			((65536, 0), 1, wasmtime::Trap::MemoryOutOfBounds),
			((0, 0), 2, wasmtime::Trap::IntegerDivisionByZero),
		] {
			let error = function.call(&mut store, args).unwrap_err();
			assert_eq!(
				error.downcast_ref::<wasmtime::Trap>(),
				Some(&expected_trap)
			);
			assert_eq!(counter.get(&mut store).i32(), Some(expected_mark));
		}
		assert_eq!(function.call(&mut store, (0, 3)).unwrap(), 7);
		assert_eq!(counter.get(&mut store).i32(), Some(3));
	}
}

#[test]
fn trapping_conversions_keep_their_destination_type() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	for emitted in [false, true] {
		let mut signatures = mir::Signatures::default();
		let signature = signatures.intern(&[T::F64], &[T::I32]);
		let mut f = Fixture::new(&[T::F64]);
		let value = f.local(0, T::F64);
		let root = f.push(
			E::Convert {
				op: mir::ConvertOp::TruncS,
				value,
			},
			T::I32,
		);
		let mir = module(
			vec![f.finish(signature, root)],
			signatures,
			export(name),
			Vec::new(),
		);
		let (mut store, instance) = run_mode(mir, &interner, emitted);
		let function = instance
			.get_typed_func::<f64, i32>(&mut store, "run")
			.unwrap();
		for (value, expected) in [(3.9, 3), (-2.9, -2), (-0.0, 0)] {
			assert_eq!(function.call(&mut store, value).unwrap(), expected);
		}
		for value in [f64::NAN, f64::INFINITY, 1e100] {
			assert!(function.call(&mut store, value).is_err());
		}
	}
}

#[test]
fn typed_operations_and_float_leaves_survive_multi_value_returns() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let nan_bits = 0x7ff8_0000_0000_1234u64;
	for emitted in [false, true] {
		let mut signatures = mir::Signatures::default();
		let results = [T::I32, T::F64, T::I32, T::F32, T::I64];
		let aggregate = signatures.value_of(&results);
		let signature = signatures.intern(&[T::I64, T::F64], &results);
		let mut f = Fixture::new(&[T::I64, T::F64]);
		let lhs = f.local(0, T::I64);
		let rhs = f.int(0, T::I64);
		let comparison = f.push(
			E::Compare {
				op: mir::CompareOp::LtS,
				lhs,
				rhs,
			},
			T::I32,
		);
		let value = f.local(1, T::F64);
		let negation = f.push(
			E::Unary {
				op: mir::UnaryOp::Neg,
				value,
			},
			T::F64,
		);
		let value = f.local(0, T::I64);
		let wrap = f.push(
			E::Convert {
				op: mir::ConvertOp::Wrap,
				value,
			},
			T::I32,
		);
		let zero = f.push(E::Float { value: -0.0 }, T::F32);
		let value = f.push(
			E::Float {
				value: f64::from_bits(nan_bits),
			},
			T::F64,
		);
		let bits = f.push(
			E::Convert {
				op: mir::ConvertOp::Reinterpret,
				value,
			},
			T::I64,
		);
		let values = f.body.push_list([comparison, negation, wrap, zero, bits]);
		let root = f.push(E::Values { values }, aggregate);
		let mir = module(
			vec![f.finish(signature, root)],
			signatures,
			export(name),
			Vec::new(),
		);
		let (mut store, instance) = run_mode(mir, &interner, emitted);
		let function = instance
			.get_typed_func::<(i64, f64), (i32, f64, i32, f32, i64)>(
				&mut store, "run",
			)
			.unwrap();
		for (integer, float) in [(-1, 0.0f64), (1 << 40, -0.0), (i64::MIN, 3.5)]
		{
			let (comparison, negation, wrap, zero, bits) =
				function.call(&mut store, (integer, float)).unwrap();
			assert_eq!(comparison, i32::from(integer < 0));
			assert_eq!(negation.to_bits(), (-float).to_bits());
			assert_eq!(wrap, integer as i32);
			assert_eq!(zero.to_bits(), (-0.0f32).to_bits());
			assert_eq!(bits as u64, nan_bits);
		}
	}
}

#[test]
fn a_diverging_call_gets_an_explicit_unreachable_boundary() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut signatures = mir::Signatures::default();
	let caller_signature = signatures.intern(&[], &[T::I32]);
	let callee_signature = signatures.intern(&[], &[]);
	let mut caller = Fixture::new(&[]);
	let call = caller.push(
		E::Call {
			function: mir::FunctionId::new(1),
			args: mir::ExprList::EMPTY,
		},
		T::Never,
	);
	let mut callee = Fixture::new(&[]);
	let trap = callee.unreachable();
	let mir = module(
		vec![
			caller.finish(caller_signature, call),
			callee.finish(callee_signature, trap),
		],
		signatures,
		export(name),
		Vec::new(),
	);
	let (mut store, instance) = run_mode(mir, &interner, true);
	let function = instance
		.get_typed_func::<(), i32>(&mut store, "run")
		.unwrap();
	assert!(function.call(&mut store, ()).is_err());
}

#[test]
fn empty_and_zero_initialized_values_need_no_computation_locals() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	for emitted in [false, true] {
		let mut signatures = mir::Signatures::default();
		let signature = signatures.intern(&[], &[]);
		let mut f = Fixture::new(&[]);
		let root = f.push(E::Noop, T::Unit);
		let mir = module(
			vec![f.finish(signature, root)],
			signatures,
			export(name),
			Vec::new(),
		);
		let (mut store, instance) = run_mode(mir, &interner, emitted);
		instance
			.get_typed_func::<(), ()>(&mut store, "run")
			.unwrap()
			.call(&mut store, ())
			.unwrap();
		let mut signatures = mir::Signatures::default();
		let signature = signatures.intern(&[], &[T::I64]);
		let mut f = Fixture::new(&[T::I64]);
		let root = f.local(0, T::I64);
		let mut mir = module(
			vec![f.finish(signature, root)],
			signatures,
			export(name),
			Vec::new(),
		);
		if emitted {
			opt::emit_for_tests(&mut mir);
			assert!(mir.code(mir::FunctionId::new(0)).locals.is_empty());
		}
		let (mut store, instance) = run_mode(mir, &interner, emitted);
		let function = instance
			.get_typed_func::<(), i64>(&mut store, "run")
			.unwrap();
		assert_eq!(function.call(&mut store, ()).unwrap(), 0);
	}
}

fn lower_source(source: &str) -> (StringInterner, mir::MIR) {
	let mut strings = crate::symbols::Keyword::create_interner();
	let mut builder = crate::vfs::CompilationUnitBuilder::new(&mut strings);
	builder.load_core();
	let root = builder
		.load_package(
			crate::vfs::AbsolutePath::new("/main.wx"),
			&crate::vfs::VirtualFileSource::from_relative(
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
	crate::testing::DiagnosticView::new("tir", &diagnostics, &unit.files)
		.assert_no_errors();
	(strings, mir.expect("source lowers"))
}

fn run_source(
	source: &str,
	emitted: bool,
) -> (wasmtime::Store<()>, wasmtime::Instance) {
	let (strings, mir) = lower_source(source);
	run_mode(mir, &strings, emitted)
}

#[test]
fn loop_swaps_read_all_sources_before_writing_any_destination() {
	let source = r#"
		func run(n: i32, x: i32, y: i32) -> i32 {
			local mut a = x; local mut b = y; local mut i: i32 = 0;
			loop {
				if i == n { break; };
				local old = a; a = b; b = old;
				i += 1;
			};
			a * 100 + b
		}
		export { run as "run" }
	"#;
	for emitted in [false, true] {
		let (mut store, instance) = run_source(source, emitted);
		let run = instance
			.get_typed_func::<(i32, i32, i32), i32>(&mut store, "run")
			.unwrap();
		for n in 0..12 {
			let expected = if n % 2 == 0 { 307 } else { 703 };
			assert_eq!(
				run.call(&mut store, (n, 3, 7)).unwrap(),
				expected,
				"emitted={emitted}, n={n}"
			);
		}
	}
}

#[test]
fn loop_rotations_on_distinct_back_edges_and_post_loop_computations() {
	let source = r#"
		func run(n: i32) -> i32 {
			local mut a: i32 = 2; local mut b: i32 = 3; local mut c: i32 = 7;
			local mut i: i32 = 0;
			loop {
				if i == n { break; };
				local old = a;
				if i == 2 {
					a = c; c = b; b = old; i += 1; continue;
				};
				a = b; b = c; c = old; i += 1;
			};
			a + b * 10 + c * 100 + (i + 1)
		}
		export { run as "run" }
	"#;
	for emitted in [false, true] {
		let (mut store, instance) = run_source(source, emitted);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		let (mut a, mut b, mut c) = (2, 3, 7);
		for n in 0..15 {
			assert_eq!(
				run.call(&mut store, n).unwrap(),
				a + b * 10 + c * 100 + n + 1,
				"emitted={emitted}, n={n}"
			);
			(a, b, c) = if n == 2 { (c, a, b) } else { (b, c, a) };
		}
	}
}

#[test]
fn nested_loop_entry_and_nonlocal_continue_and_break_keep_join_values() {
	let source = r#"
		func run(n: i32) -> i32 {
			local mut a: i32 = 2; local mut b: i32 = 7; local mut i: i32 = 0;
			loop :outer {
				if i == n { break; };
				local mut j: i32 = 0;
				loop {
					local old = a; a = b; b = old;
					j += 1;
					if j == 2 {
						i += 1;
						if i == n { break :outer; };
						continue :outer;
					};
				};
			};
			a * 100 + b + i
		}
		export { run as "run" }
	"#;
	for emitted in [false, true] {
		let (mut store, instance) = run_source(source, emitted);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		for n in 0..10 {
			assert_eq!(
				run.call(&mut store, n).unwrap(),
				207 + n,
				"emitted={emitted}, n={n}"
			);
		}
	}
}

#[test]
fn block_exits_switches_and_early_returns_execute_only_selected_arms() {
	let source = r#"
		func run(n: i32) -> i32 {
			local value: i32 = block :done {
				match n {
					0 => { return 11; },
					1 => { local answer: i32 = 20; break :done answer; },
					2 => { 30 },
					_ => { if n < 0 { return 99; }; 40 }
				}
			};
			value + 1
		}
		export { run as "run" }
	"#;
	for emitted in [false, true] {
		let (mut store, instance) = run_source(source, emitted);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		for (n, expected) in
			[(-1, 99), (0, 11), (1, 21), (2, 31), (3, 41), (i32::MAX, 41)]
		{
			assert_eq!(
				run.call(&mut store, n).unwrap(),
				expected,
				"emitted={emitted}, n={n}"
			);
		}
	}
}

#[test]
fn exhaustive_and_sparse_switches_preserve_results() {
	let source = r#"
		func run(n: i32, flag: Bool) -> i32 {
			local a: i32 = match flag { const True => { 2 }, const False => { 7 } };
			local b: i32 = match n { -100 => { 10 }, 10000 => { 20 }, _ => { 30 } };
			a + b
		}
		export { run as "run" }
	"#;
	for emitted in [false, true] {
		let (mut store, instance) = run_source(source, emitted);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		for (n, b) in [(-100, 10), (10000, 20), (0, 30)] {
			for flag in [0, 1] {
				assert_eq!(
					run.call(&mut store, (n, flag)).unwrap(),
					b + if flag == 1 { 2 } else { 7 }
				);
			}
		}
	}
}

#[test]
fn branch_effects_and_unused_traps_preserve_order_and_do_not_run_in_other_arms()
{
	// Hand-built MIR makes the unused trapping operation unambiguous.
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let counter_name = interner.get_or_intern("counter");
	for emitted in [false, true] {
		let mut mir = unused_traps(name, counter_name);
		let code = mir.functions[0].code_mut().unwrap();
		let condition = code.body.push(
			E::LocalGet {
				local: mir::LocalIndex::new(0),
			},
			T::I32,
		);
		let other = code.body.push(E::Int { value: 123 }, T::I32);
		// Original arm returns or traps; the other returns normally.
		code.root = code.body.push(
			E::IfElse {
				condition,
				then: code.root,
				otherwise: Some(other),
			},
			T::I32,
		);
		let (mut store, instance) = run_mode(mir, &interner, emitted);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		let counter = instance.get_global(&mut store, "counter").unwrap();
		assert_eq!(run.call(&mut store, (0, 0)).unwrap(), 123);
		assert_eq!(counter.get(&mut store).i32(), Some(0));
		let error = run.call(&mut store, (65536, 0)).unwrap_err();
		assert_eq!(
			error.downcast_ref::<wasmtime::Trap>(),
			Some(&wasmtime::Trap::MemoryOutOfBounds)
		);
		assert_eq!(counter.get(&mut store).i32(), Some(1));
		assert_eq!(run.call(&mut store, (1, 3)).unwrap(), 7);
		assert_eq!(counter.get(&mut store).i32(), Some(3));
	}
}

#[test]
fn mixed_scalar_values_cross_all_construct_exit_joins() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	for emitted in [false, true] {
		for construct in 0..4 {
			let mir = pack_join_mir(name, |f, pack| match construct {
				0 | 1 => {
					let label = f.label();
					let value = pack_param(f, pack);
					let exit = f.push(
						E::Break {
							label,
							value: Some(value),
						},
						T::Never,
					);
					if construct == 0 {
						let statements = f.body.push_list([exit]);
						f.push(E::Block { label, statements }, pack)
					} else {
						f.push(E::Loop { label, body: exit }, pack)
					}
				}
				_ => {
					let selector = f.local(N, T::I32);
					let first = pack_param(f, pack);
					let other = pack_literal(f, pack, (11, 1 << 40, 19));
					if construct == 2 {
						f.if_else(selector, first, Some(other), pack)
					} else {
						let cases = f.body.push_cases([mir::Case {
							value: 1,
							body: first,
						}]);
						f.push(
							E::Switch {
								selector,
								cases,
								default: Some(other),
							},
							pack,
						)
					}
				}
			});
			let (mut store, instance) = run_mode(mir, &interner, emitted);
			let run = instance
				.get_typed_func::<(i32, i64, i32, i32), (i32, i64, i32)>(
					&mut store, "run",
				)
				.unwrap();
			for n in [0, 1] {
				let expected = if construct < 2 || n == 1 {
					(3, 1 << 45, 7)
				} else {
					(11, 1 << 40, 19)
				};
				assert_eq!(
					run.call(&mut store, (3, 1 << 45, 7, n)).unwrap(),
					expected
				);
			}
		}
	}
}

#[test]
fn call_results_and_shared_computations_remain_available_across_branches() {
	let source = r#"
		global mut counter: i32 = 0;
		func tick(x: i32) -> i32 { counter.set(counter.get() + 1); x + 1 }
		func run(n: i32, flag: Bool) -> i32 {
			local x = tick(n);
			local result: i32 = if flag { tick(x + 2) } else { x + 2 };
			result + (x + 2)
		}
		export { run as "run", counter as "counter" }
	"#;
	for emitted in [false, true] {
		let (mut store, instance) = run_source(source, emitted);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		let counter = instance.get_global(&mut store, "counter").unwrap();
		assert_eq!(run.call(&mut store, (10, 0)).unwrap(), 26);
		assert_eq!(counter.get(&mut store).i32(), Some(1));
		assert_eq!(run.call(&mut store, (10, 1)).unwrap(), 27);
		assert_eq!(counter.get(&mut store).i32(), Some(3));
	}
}

#[test]
fn computations_shared_by_back_edges_and_post_loop_reads_stay_inside_loop() {
	let source = r#"
		func run(n: i32) -> i32 {
			local mut i: i32 = 0;
			loop {
				if i == n { break; };
				i = i + 1;
			};
			i + 1
		}
		export { run as "run" }
	"#;
	for emitted in [false, true] {
		let (mut store, instance) = run_source(source, emitted);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		for n in [0, 1, 2, 20] {
			assert_eq!(run.call(&mut store, n).unwrap(), n + 1);
		}
	}
}

#[test]
fn untargeted_blocks_fall_through_without_labels_or_transfers() {
	let source = r#"
		func run(x: i32) -> i32 {
			block { block {}; block {}; block { x + 1 } }
		}
		export { run as "run" }
	"#;
	let (strings, mut mir) = lower_source(source);
	opt::emit_for_tests(&mut mir);
	let code = mir.code(mir::FunctionId::new(0));
	assert_eq!(code.label_count, 0);
	assert!(!code.body.kinds().iter().any(|kind| matches!(
		kind,
		E::Block { .. } | E::Break { .. } | E::Continue { .. }
	)));
	let (mut store, instance) = run_mode(mir, &strings, false);
	let run = instance
		.get_typed_func::<i32, i32>(&mut store, "run")
		.unwrap();
	for x in [0i32, -1, 42, i32::MAX] {
		assert_eq!(run.call(&mut store, x).unwrap(), x.wrapping_add(1));
	}
}

#[test]
fn falling_through_if_and_switch_arms_keep_computations_and_join_updates() {
	for body in [
		"if n == 0 { block { x + 1 } } else { block { x * 2 } }",
		"match n { 0 => block { x + 1 }, 1 => block { x * 2 }, 2 => block { x * 2 }, _ => block { x * 2 } }",
	] {
		let source = format!(
			"func run(n: i32, x: i32) -> i32 {{ {body} }} export {{ run as \"run\" }}"
		);
		let (strings, mut mir) = lower_source(&source);
		opt::emit_for_tests(&mut mir);
		let code = mir.code(mir::FunctionId::new(0));
		assert_eq!(code.label_count, 0, "normal arm exits need no labels");
		assert!(
			!code
				.body
				.kinds()
				.iter()
				.any(|kind| matches!(kind, E::Block { .. } | E::Break { .. }))
		);
		assert!(code.body.kinds().iter().any(|kind| matches!(kind,
			E::SetLocals { targets, .. } if !code.body.targets(*targets).is_empty())));
		let (mut store, instance) = run_mode(mir, &strings, false);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		for n in [-1, 0, 1, 2, 3] {
			for x in [-17i32, 0, 42, i32::MAX] {
				let expected = if n == 0 {
					x.wrapping_add(1)
				} else {
					x.wrapping_mul(2)
				};
				assert_eq!(run.call(&mut store, (n, x)).unwrap(), expected);
			}
		}
	}
}

#[test]
fn nonlocal_exits_keep_their_wrapper_and_skip_parent_continuation() {
	let source = r#"
		global mut trace: i32 = 0;
		func run(flag: Bool) -> (i32, i32) {
			trace.set(0);
			local value: i32 = block :done {
				block {
					if flag { trace.set(1); break :done 7; };
				};
				trace.set(2);
				9
			};
			(value, trace.get())
		}
		export { run as "run" }
	"#;
	let (strings, mut mir) = lower_source(source);
	opt::emit_for_tests(&mut mir);
	let code = mir.code(mir::FunctionId::new(0));
	assert_eq!(code.label_count, 1, "only the nonlocal exit needs a label");
	assert!(
		code.body
			.kinds()
			.iter()
			.any(|kind| matches!(kind, E::Break { .. }))
	);
	assert_eq!(
		code.body
			.kinds()
			.iter()
			.filter(|kind| matches!(kind, E::Block { .. }))
			.count(),
		1
	);
	let (mut store, instance) = run_mode(mir, &strings, false);
	let run = instance
		.get_typed_func::<i32, (i32, i32)>(&mut store, "run")
		.unwrap();
	for flag in [0, 1, 0, 1] {
		assert_eq!(
			run.call(&mut store, flag).unwrap(),
			if flag == 0 { (9, 2) } else { (7, 1) }
		);
	}
}

#[test]
fn single_use_arithmetic_nests_without_intermediate_locals() {
	let source = r#"
		func run(x: i32, y: i32) -> i32 { (x - y) * (x + y) }
		export { run as "run" }
	"#;
	let (strings, mut mir) = lower_source(source);
	opt::emit_for_tests(&mut mir);
	let code = mir.code(mir::FunctionId::new(0));
	assert_eq!(code.locals.len(), 2, "only the two parameters need locals");
	assert!(
		!code
			.body
			.kinds()
			.iter()
			.any(|kind| matches!(kind, E::LocalSet { .. }))
	);
	let (mut store, instance) = run_mode(mir, &strings, false);
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	for (x, y) in [(5i32, 3i32), (-5, 3), (i32::MAX, 1), (i32::MIN, -1)] {
		assert_eq!(
			run.call(&mut store, (x, y)).unwrap(),
			x.wrapping_sub(y).wrapping_mul(x.wrapping_add(y))
		);
	}
}

#[test]
fn long_single_use_chains_construct_and_linearize_without_recursion() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut mir = scalar_function(name, |f| {
		// Flat input MIR becomes a deep expression only after graph emission.
		let mut statements = Vec::new();
		for _ in 0..4096 {
			let input = f.local(0, T::I32);
			let one = f.int(1, T::I32);
			let value = f.binary(mir::BinaryOp::Add, input, one, T::I32);
			statements.push(f.push(
				E::LocalSet {
					local: mir::LocalIndex::new(0),
					value,
				},
				T::Unit,
			));
		}
		statements.push(f.local(0, T::I32));
		f.sequence(statements, T::I32)
	});
	opt::optimize_function(&mut mir, mir::FunctionId::new(0));
	assert_eq!(mir.code(mir::FunctionId::new(0)).locals.len(), 2);
	let (mut store, instance) = run_mode(mir, &interner, false);
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	for x in [0i32, -4096, i32::MAX, i32::MIN] {
		assert_eq!(run.call(&mut store, (x, 0)).unwrap(), x.wrapping_add(4096));
	}
}
