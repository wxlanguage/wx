//! Backend fixtures: hand-built MIR, lowered through `opt` and `codegen` and
//! executed under wasmtime.
//!
//! These tests deliberately do not go through TIR. They pin the MIR → Wasm
//! contract on its own, so a regression in the optimizer, scheduler, encoder
//! or ABI shows up here even while the TIR → MIR lowerer is still being built.
//! Each fixture states the MIR shape it assumes in words, so the lowerer has
//! something concrete to target.

use string_interner::symbol::SymbolU32;

use crate::ast::StringInterner;
use crate::mir;
use crate::wasm;

/// `func add(a: i32, b: i32) -> i32 { a + b }`, written directly as MIR.
///
/// Contract this fixture depends on:
/// - parameters are the first `params_count` entries of `Function::locals`,
/// - the body is an `ExprKind::Block` whose value is its last expression,
/// - the block's value is returned implicitly,
/// - `MIR::signatures[signature_index]` is the sole source of the Wasm
///   signature.
fn scalar_add(name: SymbolU32) -> mir::MIR {
	let i32_ty = mir::ValueType::I32;
	let local = |index: u32| mir::Expression {
		kind: mir::ExprKind::LocalGet {
			local_index: mir::LocalIndex::new(index),
		},
		ty: i32_ty,
	};

	mir::MIR {
		functions: vec![mir::Function {
			id: mir::FunctionId::new(0),
			signature_index: mir::SignatureIndex::new(0),
			scopes: vec![mir::BlockScope {
				kind: mir::BlockKind::Block,
				result: i32_ty,
			}],
			locals: vec![
				mir::Local {
					ty: i32_ty,
					mutability: mir::Mutability::Immutable,
				},
				mir::Local {
					ty: i32_ty,
					mutability: mir::Mutability::Immutable,
				},
			],
			block: mir::Expression {
				kind: mir::ExprKind::Block {
					scope_index: mir::ScopeIndex::new(0),
					expressions: Box::new([mir::Expression {
						kind: mir::ExprKind::Add {
							left: Box::new(local(0)),
							right: Box::new(local(1)),
						},
						ty: i32_ty,
					}]),
				},
				ty: i32_ty,
			},
			static_data: Vec::new(),
		}],
		inline_functions: Default::default(),
		signatures: vec![mir::FunctionSignature {
			items: Box::new([i32_ty, i32_ty, i32_ty]),
			params_count: 2,
		}],
		globals: Vec::new(),
		exports: vec![mir::ExportItem::Function {
			id: mir::FunctionId::new(0),
			name,
		}],
		imports: Vec::new(),
		memories: Vec::new(),
		aggregates: Box::new([]),
		static_entries: Vec::new(),
		call_edges: Vec::new(),
		start_function: None,
	}
}

fn instantiate(bytes: &[u8]) -> (wasmtime::Engine, wasmtime::Module) {
	let engine = wasmtime::Engine::default();
	let module = wasmtime::Module::new(&engine, bytes)
		.expect("backend emitted an invalid Wasm module");
	(engine, module)
}

#[test]
fn hand_built_scalar_add_runs_under_wasmtime() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("add");
	let mir = scalar_add(name);

	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a scalar MIR module must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);

	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[])
		.expect("a backend module with no imports must instantiate");
	let add = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "add")
		.expect("`add` must be exported under its external name");

	assert_eq!(add.call(&mut store, (5, 3)).unwrap(), 8);
	assert_eq!(add.call(&mut store, (-5, 3)).unwrap(), -2);
	assert_eq!(add.call(&mut store, (0, 0)).unwrap(), 0);
}

/// The same body, but the export is the only thing that makes it reachable.
/// Asserts the module does not accidentally export a name it was not told to.
#[test]
fn hand_built_scalar_add_exports_only_the_requested_name() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("sum");
	let mir = scalar_add(name);

	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a scalar MIR module must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);

	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let sum = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "sum")
		.expect("exported under the MIR export name");
	assert_eq!(sum.call(&mut store, (1, 2)).unwrap(), 3);

	assert!(
		instance.get_func(&mut store, "add").is_none(),
		"the fixture's internal identity must not leak into the ABI"
	);
}

/// A signature-only check that does not execute anything: flattening a
/// zero-slot result must not produce a Wasm result slot.
#[test]
fn unit_result_flattens_to_no_wasm_slots() {
	assert!(
		wasm::flatten_type_to_scalars(mir::ValueType::Unit, &[]).is_empty()
	);
}

/// Two functions whose backend IDs deliberately disagree with their positions
/// in `MIR::functions` and with their Wasm indices.
///
/// `triple` (id 7, wasm index 0) calls `add` (id 3, wasm index 1). An encoder
/// that confused an ID with a table position would emit `call 3` and fail
/// validation, so this is the test that keeps the identity contract honest.
#[test]
fn direct_call_resolves_backend_ids_not_table_positions() {
	let mut interner = StringInterner::new();
	let triple_name = interner.get_or_intern("triple");

	let i32_ty = mir::ValueType::I32;
	let add_id = mir::FunctionId::new(3);
	let triple_id = mir::FunctionId::new(7);
	let add_sig = mir::SignatureIndex::new(0);
	let triple_sig = mir::SignatureIndex::new(1);

	let scalar_local = mir::Local {
		ty: i32_ty,
		mutability: mir::Mutability::Immutable,
	};
	let local = |index: u32| mir::Expression {
		kind: mir::ExprKind::LocalGet {
			local_index: mir::LocalIndex::new(index),
		},
		ty: i32_ty,
	};
	let body = |expressions: Box<[mir::Expression]>| mir::Expression {
		kind: mir::ExprKind::Block {
			scope_index: mir::ScopeIndex::new(0),
			expressions,
		},
		ty: i32_ty,
	};
	let call_add = |arguments: [mir::Expression; 2]| mir::Expression {
		kind: mir::ExprKind::Call {
			callee: Box::new(mir::Expression {
				kind: mir::ExprKind::Function { id: add_id },
				ty: mir::ValueType::Function {
					signature_index: add_sig,
				},
			}),
			arguments: Box::new(arguments),
		},
		ty: i32_ty,
	};

	let add = mir::Function {
		id: add_id,
		signature_index: add_sig,
		scopes: vec![mir::BlockScope {
			kind: mir::BlockKind::Block,
			result: i32_ty,
		}],
		locals: vec![scalar_local.clone(), scalar_local.clone()],
		block: body(Box::new([mir::Expression {
			kind: mir::ExprKind::Add {
				left: Box::new(local(0)),
				right: Box::new(local(1)),
			},
			ty: i32_ty,
		}])),
		static_data: Vec::new(),
	};

	// `triple(a) = add(add(a, a), a)`
	let triple = mir::Function {
		id: triple_id,
		signature_index: triple_sig,
		scopes: vec![mir::BlockScope {
			kind: mir::BlockKind::Block,
			result: i32_ty,
		}],
		locals: vec![scalar_local],
		block: body(Box::new([call_add([
			call_add([local(0), local(0)]),
			local(0),
		])])),
		static_data: Vec::new(),
	};

	let mir = mir::MIR {
		// Definition order is `triple`, `add`; Wasm indices follow this order,
		// so they are 0 and 1 while the IDs are 7 and 3.
		functions: vec![triple, add],
		inline_functions: Default::default(),
		signatures: vec![
			mir::FunctionSignature {
				items: Box::new([i32_ty, i32_ty, i32_ty]),
				params_count: 2,
			},
			mir::FunctionSignature {
				items: Box::new([i32_ty, i32_ty]),
				params_count: 1,
			},
		],
		globals: Vec::new(),
		exports: vec![mir::ExportItem::Function {
			id: triple_id,
			name: triple_name,
		}],
		imports: Vec::new(),
		memories: Vec::new(),
		aggregates: Box::new([]),
		static_entries: Vec::new(),
		call_edges: Vec::new(),
		start_function: None,
	};

	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a two-function scalar MIR module must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);

	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let triple = instance
		.get_typed_func::<i32, i32>(&mut store, "triple")
		.expect("`triple` must be exported");
	assert_eq!(triple.call(&mut store, 5).unwrap(), 15);
	assert_eq!(triple.call(&mut store, -2).unwrap(), -6);
}

// ── Aggregate layout fixtures ────────────────────────────────────────────────

use crate::mir::layout::AggregateTable;
use crate::wasm::ScalarType;

/// MIR for `identity(s: T) -> T`, where `T` is the aggregate at
/// `aggregate_index`. The Wasm signature is entirely derived from
/// `FunctionSignature::items` + the aggregate's `ScalarTable`, so this pins
/// the parameter/result flattening without involving TIR.
fn aggregate_identity_mir(
	name: SymbolU32,
	aggregate_index: mir::AggregateIndex,
	aggregates: Box<[mir::Aggregate]>,
) -> mir::MIR {
	let ty = mir::ValueType::Aggregate { aggregate_index };
	mir::MIR {
		functions: vec![mir::Function {
			id: mir::FunctionId::new(0),
			signature_index: mir::SignatureIndex::new(0),
			scopes: vec![mir::BlockScope {
				kind: mir::BlockKind::Block,
				result: ty,
			}],
			locals: vec![mir::Local {
				ty,
				mutability: mir::Mutability::Immutable,
			}],
			block: mir::Expression {
				kind: mir::ExprKind::Block {
					scope_index: mir::ScopeIndex::new(0),
					expressions: Box::new([mir::Expression {
						kind: mir::ExprKind::LocalGet {
							local_index: mir::LocalIndex::new(0),
						},
						ty,
					}]),
				},
				ty,
			},
			static_data: Vec::new(),
		}],
		inline_functions: Default::default(),
		signatures: vec![mir::FunctionSignature {
			items: Box::new([ty, ty]),
			params_count: 1,
		}],
		globals: Vec::new(),
		exports: vec![mir::ExportItem::Function {
			id: mir::FunctionId::new(0),
			name,
		}],
		imports: Vec::new(),
		memories: Vec::new(),
		aggregates,
		static_entries: Vec::new(),
		call_edges: Vec::new(),
		start_function: None,
	}
}

fn run_aggregate_identity(mir: &mir::MIR, interner: &StringInterner) {
	let module = crate::codegen::Builder::build(mir, interner)
		.expect("an aggregate identity module must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);

	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let identity = instance
		.get_typed_func::<(i32, i64, i32), (i32, i64, i32)>(
			&mut store, "identity",
		)
		.expect("an aggregate's Wasm ABI is its flattened scalars");

	let input = (7, 1 << 40, 9);
	assert_eq!(identity.call(&mut store, input).unwrap(), input);
}

/// `struct S { a: u8, b: i64, c: u8 }` is laid out alignment-sorted, so its
/// memory offsets are `b=0, a=8, c=9` — but its *value* order, and therefore
/// its Wasm parameter and result order, stays declaration order: `a, b, c`.
///
/// This is the fixture that keeps "memory order is never a value order"
/// honest: an encoder that sorted the slots would call this with the wrong
/// values, and the round trip below would fail.
#[test]
fn aggregate_slots_stay_in_declaration_order_while_offsets_are_sorted() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("identity");

	let mut table = AggregateTable::default();
	let aggregate_index = table.push(
		Box::new([mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8]),
		Some(mir::AggregateMemory {
			offsets: Box::new([8, 0, 9]),
			layout: mir::Layout { size: 16, align: 8 },
		}),
	);
	let aggregates = table.finish();

	let aggregate = &aggregates[usize::from(aggregate_index)];
	let memory = aggregate.memory.as_ref().unwrap();
	assert_eq!(
		memory.offsets.as_ref(),
		[8, 0, 9],
		"memory layout is alignment-sorted"
	);
	assert_eq!((memory.layout.size, memory.layout.align), (16, 8));

	let scalar_types: Vec<ScalarType> = aggregate
		.scalars
		.iter()
		.map(|&ty| ScalarType::try_from(ty).unwrap())
		.collect();
	assert_eq!(
		scalar_types,
		vec![ScalarType::I32, ScalarType::I64, ScalarType::I32],
		"slots follow declaration order, not memory order"
	);

	assert_eq!(
		wasm::flatten_type_to_scalars(
			mir::ValueType::Aggregate { aggregate_index },
			&aggregates,
		),
		vec![ScalarType::I32, ScalarType::I64, ScalarType::I32],
	);

	let mir = aggregate_identity_mir(name, aggregate_index, aggregates);
	run_aggregate_identity(&mir, &interner);
}

/// The `#[fixed_order]` counterpart: the same fields keep declaration
/// offsets, so the only difference is memory layout. Value order is
/// identical to the sorted case, which is what makes `#[fixed_order]` a pure
/// layout attribute.
#[test]
fn fixed_order_changes_offsets_only() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("identity");

	let mut table = AggregateTable::default();
	let aggregate_index = table.push(
		Box::new([mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8]),
		Some(mir::AggregateMemory {
			offsets: Box::new([0, 8, 16]),
			layout: mir::Layout { size: 24, align: 8 },
		}),
	);
	let aggregates = table.finish();

	let aggregate = &aggregates[usize::from(aggregate_index)];
	let memory = aggregate.memory.as_ref().unwrap();
	assert_eq!(
		memory.offsets.as_ref(),
		[0, 8, 16],
		"declaration order, padded"
	);
	assert_eq!((memory.layout.size, memory.layout.align), (24, 8));

	let mir = aggregate_identity_mir(name, aggregate_index, aggregates);
	run_aggregate_identity(&mir, &interner);
}

/// A source zero-sized field has already disappeared. MIR selects the
/// remaining second slot directly, without a declaration-field map.
#[test]
fn projection_indexes_flat_slots_not_source_fields() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("last");

	let mut table = AggregateTable::default();
	let aggregate_index = table.push(
		Box::new([mir::ValueType::U8, mir::ValueType::U8]),
		Some(mir::AggregateMemory {
			offsets: Box::new([0, 1]),
			layout: mir::Layout { size: 2, align: 1 },
		}),
	);
	let aggregates = table.finish();

	let aggregate = &aggregates[usize::from(aggregate_index)];
	assert_eq!(aggregate.scalars.len(), 2);

	let aggregate_ty = mir::ValueType::Aggregate { aggregate_index };
	assert_eq!(
		wasm::flatten_type_to_scalars(aggregate_ty, &aggregates),
		vec![ScalarType::I32, ScalarType::I32],
		"the zero-sized field consumes no parameter slot"
	);

	// `last(s: S) -> u8 { s.c }` — field 2, past the zero-sized field.
	let mir = mir::MIR {
		functions: vec![mir::Function {
			id: mir::FunctionId::new(0),
			signature_index: mir::SignatureIndex::new(0),
			scopes: vec![mir::BlockScope {
				kind: mir::BlockKind::Block,
				result: mir::ValueType::U8,
			}],
			locals: vec![mir::Local {
				ty: aggregate_ty,
				mutability: mir::Mutability::Immutable,
			}],
			block: mir::Expression {
				kind: mir::ExprKind::Block {
					scope_index: mir::ScopeIndex::new(0),
					expressions: Box::new([mir::Expression {
						kind: mir::ExprKind::AggregateGet {
							local_index: mir::LocalIndex::new(0),
							range: mir::ScalarRange::new(1, 1),
						},
						ty: mir::ValueType::U8,
					}]),
				},
				ty: mir::ValueType::U8,
			},
			static_data: Vec::new(),
		}],
		inline_functions: Default::default(),
		signatures: vec![mir::FunctionSignature {
			items: Box::new([aggregate_ty, mir::ValueType::U8]),
			params_count: 1,
		}],
		globals: Vec::new(),
		exports: vec![mir::ExportItem::Function {
			id: mir::FunctionId::new(0),
			name,
		}],
		imports: Vec::new(),
		memories: Vec::new(),
		aggregates,
		static_entries: Vec::new(),
		call_edges: Vec::new(),
		start_function: None,
	};

	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a ZST-bearing aggregate module must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let last = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "last")
		.expect("two scalar params, one scalar result");
	assert_eq!(last.call(&mut store, (5, 42)).unwrap(), 42);
}

/// Store the reordered aggregate to memory and load it back, at the same
/// address. The store walks declaration-order slots paired with their
/// (sorted) byte offsets; the load walks the same pairs in reverse. Nothing
/// permutes the value list, so the round trip must return the input
/// unchanged.
#[test]
fn aggregate_memory_roundtrip_pairs_slots_with_their_offsets() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("identity");

	let mut table = AggregateTable::default();
	let aggregate_index = table.push(
		Box::new([mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8]),
		Some(mir::AggregateMemory {
			offsets: Box::new([8, 0, 9]),
			layout: mir::Layout { size: 16, align: 8 },
		}),
	);
	let aggregates = table.finish();
	let aggregate_ty = mir::ValueType::Aggregate { aggregate_index };

	let memory = mir::MemoryId::new(0);
	let address = || mir::Expression {
		kind: mir::ExprKind::Int { value: 0 },
		ty: mir::ValueType::I32,
	};
	let param = mir::Expression {
		kind: mir::ExprKind::LocalGet {
			local_index: mir::LocalIndex::new(0),
		},
		ty: aggregate_ty,
	};

	let mir = mir::MIR {
		functions: vec![mir::Function {
			id: mir::FunctionId::new(0),
			signature_index: mir::SignatureIndex::new(0),
			scopes: vec![mir::BlockScope {
				kind: mir::BlockKind::Block,
				result: aggregate_ty,
			}],
			locals: vec![mir::Local {
				ty: aggregate_ty,
				mutability: mir::Mutability::Immutable,
			}],
			block: mir::Expression {
				kind: mir::ExprKind::Block {
					scope_index: mir::ScopeIndex::new(0),
					expressions: Box::new([
						mir::Expression {
							kind: mir::ExprKind::PointerStore {
								pointer: Box::new(address()),
								value: Box::new(param),
								offset: 0,
								memory,
							},
							ty: mir::ValueType::Unit,
						},
						mir::Expression {
							kind: mir::ExprKind::PointerLoad {
								pointer: Box::new(address()),
								offset: 0,
								memory,
							},
							ty: aggregate_ty,
						},
					]),
				},
				ty: aggregate_ty,
			},
			static_data: Vec::new(),
		}],
		inline_functions: Default::default(),
		signatures: vec![mir::FunctionSignature {
			items: Box::new([aggregate_ty, aggregate_ty]),
			params_count: 1,
		}],
		globals: Vec::new(),
		exports: vec![mir::ExportItem::Function {
			id: mir::FunctionId::new(0),
			name,
		}],
		imports: Vec::new(),
		memories: vec![mir::MemoryInfo {
			id: memory,
			source: mir::MemorySource::Internal,
			kind: mir::MemoryKind::Memory32,
			min_pages: Some(1),
			max_pages: None,
		}],
		aggregates,
		static_entries: Vec::new(),
		call_edges: Vec::new(),
		start_function: None,
	};

	run_aggregate_identity(&mir, &interner);
}

#[test]
fn flat_stack_values_do_not_require_a_memory_layout() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("identity");
	let mut table = AggregateTable::default();
	let index = table.push(
		Box::new([
			mir::ValueType::I32,
			mir::ValueType::I64,
			mir::ValueType::I32,
		]),
		None,
	);
	let mir = aggregate_identity_mir(name, index, table.finish());
	assert!(mir.aggregate(index).memory.is_none());
	run_aggregate_identity(&mir, &interner);
}

// ── Control-flow pack joins ─────────────────────────────────────────────────

/// The pack every fixture below passes around: three scalars with no memory
/// layout. Having no layout matters — it forces the aggregate through the
/// flattened, local-per-scalar path instead of a memory round trip.
const PACK_INPUT: (i32, i64, i32) = (7, 1 << 40, 9);

fn local(index: u32, ty: mir::ValueType) -> mir::Expression {
	mir::Expression {
		kind: mir::ExprKind::LocalGet {
			local_index: mir::LocalIndex::new(index),
		},
		ty,
	}
}

fn int(value: i64, ty: mir::ValueType) -> mir::Expression {
	mir::Expression {
		kind: mir::ExprKind::Int { value },
		ty,
	}
}

fn block(
	scope_index: u32,
	ty: mir::ValueType,
	expressions: Box<[mir::Expression]>,
) -> mir::Expression {
	mir::Expression {
		kind: mir::ExprKind::Block {
			scope_index: mir::ScopeIndex::new(scope_index),
			expressions,
		},
		ty,
	}
}

/// Register a new block scope on `function` and return its index.
fn push_scope(
	function: &mut mir::Function,
	kind: mir::BlockKind,
	result: mir::ValueType,
) -> mir::ScopeIndex {
	let scope_index = mir::ScopeIndex::new(function.scopes.len() as u32);
	function.scopes.push(mir::BlockScope { kind, result });
	scope_index
}

/// Wrap `value` in a fresh `Block` scope: the shape MIR uses for a branch
/// body.
fn arm(
	function: &mut mir::Function,
	value: mir::Expression,
) -> mir::Expression {
	let ty = value.ty;
	let scope_index = push_scope(function, mir::BlockKind::Block, ty);
	block(u32::from(scope_index), ty, Box::new([value]))
}

/// Base MIR shared by the control-flow fixtures:
///
/// ```text
/// fn run(pack: (i32, i64, i32), n: i32) -> (i32, i64, i32)
/// ```
///
/// Each test replaces the function body with one control-flow construct and
/// checks that the pack still crosses its join unchanged.
fn pack_join_mir(name: SymbolU32) -> (mir::MIR, mir::ValueType) {
	let mut table = AggregateTable::default();
	let aggregate_index = table.push(
		Box::new([
			mir::ValueType::I32,
			mir::ValueType::I64,
			mir::ValueType::I32,
		]),
		None,
	);
	let pack = mir::ValueType::Aggregate { aggregate_index };
	let mut mir = aggregate_identity_mir(name, aggregate_index, table.finish());
	mir.signatures[0] = mir::FunctionSignature {
		items: Box::new([pack, mir::ValueType::I32, pack]),
		params_count: 2,
	};
	// Parameter 0 is the pack, parameter 1 is `n`. The loop fixture mutates
	// both; marking them mutable here keeps the fixtures otherwise identical.
	mir.functions[0].locals.push(mir::Local {
		ty: mir::ValueType::I32,
		mutability: mir::Mutability::Mutable,
	});
	mir.functions[0].locals[0].mutability = mir::Mutability::Mutable;
	(mir, pack)
}

fn pack_literal(
	pack: mir::ValueType,
	values: (i32, i64, i32),
) -> mir::Expression {
	mir::Expression {
		kind: mir::ExprKind::Aggregate {
			values: Box::new([
				int(i64::from(values.0), mir::ValueType::I32),
				int(values.1, mir::ValueType::I64),
				int(i64::from(values.2), mir::ValueType::I32),
			]),
		},
		ty: pack,
	}
}

/// Run `mir`'s exported `run` for a few values of `n` and compare the pack
/// result. Every fixture passes the same `PACK_INPUT` pack and varies only
/// `n`, so `expected` fully describes the control-flow behaviour.
fn assert_pack_join(
	mir: &mir::MIR,
	interner: &StringInterner,
	expected: impl Fn(i32) -> (i32, i64, i32),
) {
	let module = crate::codegen::Builder::build(mir, interner)
		.expect("a flat-pack control-flow module must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let run = instance
		.get_typed_func::<(i32, i64, i32, i32), (i32, i64, i32)>(
			&mut store, "run",
		)
		.expect("`run` exports the flattened pack and scalar ABI");

	for n in [0, 1, 2, 3] {
		let input = (PACK_INPUT.0, PACK_INPUT.1, PACK_INPUT.2, n);
		assert_eq!(
			run.call(&mut store, input).unwrap(),
			expected(n),
			"n = {n}"
		);
	}
}

/// `if n != 0 { pack } else { (1, 2, 3) }`
#[test]
fn flat_pack_crosses_an_if_join() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let (mut mir, pack) = pack_join_mir(name);

	let then_block = arm(&mut mir.functions[0], local(0, pack));
	let else_block = arm(&mut mir.functions[0], pack_literal(pack, (1, 2, 3)));
	let value = mir::Expression {
		kind: mir::ExprKind::IfElse {
			condition: Box::new(local(1, mir::ValueType::I32)),
			then_block: Box::new(then_block),
			else_block: Some(Box::new(else_block)),
		},
		ty: pack,
	};
	mir.functions[0].block = block(0, pack, Box::new([value]));

	assert_pack_join(&mir, &interner, |n| {
		if n == 0 { (1, 2, 3) } else { PACK_INPUT }
	});
}

/// ```text
/// match n {
///     0 => (1, 2, 3),
///     1 => pack,
///     2 => (4, 5, 6),
///     _ => pack,
/// }
/// ```
///
/// `should_use_br_table` needs at least three i32 cases to take the real
/// `Switch` path. With fewer, `build_switch_as_if_chain` lowers the match to
/// `IfElse`s and this fixture would just repeat `flat_pack_crosses_an_if_join`.
/// The two literal arms return different packs, so both are genuine case
/// bodies rather than padding to reach the case count.
#[test]
fn flat_pack_crosses_a_switch_join() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let (mut mir, pack) = pack_join_mir(name);

	let case_zero = arm(&mut mir.functions[0], pack_literal(pack, (1, 2, 3)));
	let case_one = arm(&mut mir.functions[0], local(0, pack));
	let case_two = arm(&mut mir.functions[0], pack_literal(pack, (4, 5, 6)));
	let default = arm(&mut mir.functions[0], local(0, pack));
	let value = mir::Expression {
		kind: mir::ExprKind::Switch {
			selector: Box::new(local(1, mir::ValueType::I32)),
			cases: Box::new([(0, case_zero), (1, case_one), (2, case_two)]),
			default: Some(Box::new(default)),
		},
		ty: pack,
	};
	mir.functions[0].block = block(0, pack, Box::new([value]));

	assert_pack_join(&mir, &interner, |n| match n {
		0 => (1, 2, 3),
		2 => (4, 5, 6),
		_ => PACK_INPUT,
	});
}

/// ```text
/// while n != 0 {
///     pack.0 += 1;
///     n -= 1;
/// }
/// pack
/// ```
#[test]
fn flat_pack_crosses_a_loop_join() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let (mut mir, pack) = pack_join_mir(name);
	let unit = mir::ValueType::Unit;
	let function = &mut mir.functions[0];

	let loop_scope = push_scope(function, mir::BlockKind::Loop, unit);

	// `if n == 0 { break }`
	let break_when_zero = mir::Expression {
		kind: mir::ExprKind::IfElse {
			condition: Box::new(mir::Expression {
				kind: mir::ExprKind::Eqz {
					value: Box::new(local(1, mir::ValueType::I32)),
				},
				ty: mir::ValueType::Bool,
			}),
			then_block: Box::new(arm(
				function,
				mir::Expression {
					kind: mir::ExprKind::Break {
						scope_index: loop_scope,
						value: None,
					},
					ty: mir::ValueType::Never,
				},
			)),
			else_block: None,
		},
		ty: unit,
	};

	// `pack.0 += 1`
	let bump_first_scalar = mir::Expression {
		kind: mir::ExprKind::AggregateSet {
			local_index: mir::LocalIndex::new(0),
			range: mir::ScalarRange::new(0, 1),
			value: Box::new(mir::Expression {
				kind: mir::ExprKind::Add {
					left: Box::new(mir::Expression {
						kind: mir::ExprKind::AggregateGet {
							local_index: mir::LocalIndex::new(0),
							range: mir::ScalarRange::new(0, 1),
						},
						ty: mir::ValueType::I32,
					}),
					right: Box::new(int(1, mir::ValueType::I32)),
				},
				ty: mir::ValueType::I32,
			}),
		},
		ty: unit,
	};

	// `n -= 1`
	let decrement_n = mir::Expression {
		kind: mir::ExprKind::LocalSet {
			local_index: mir::LocalIndex::new(1),
			value: Box::new(mir::Expression {
				kind: mir::ExprKind::Sub {
					left: Box::new(local(1, mir::ValueType::I32)),
					right: Box::new(int(1, mir::ValueType::I32)),
				},
				ty: mir::ValueType::I32,
			}),
		},
		ty: unit,
	};

	let body = block(
		u32::from(loop_scope),
		unit,
		Box::new([break_when_zero, bump_first_scalar, decrement_n]),
	);
	let loop_expression = mir::Expression {
		kind: mir::ExprKind::Loop {
			scope_index: loop_scope,
			block: Box::new(body),
		},
		ty: unit,
	};
	mir.functions[0].block =
		block(0, pack, Box::new([loop_expression, local(0, pack)]));

	assert_pack_join(&mir, &interner, |n| {
		(PACK_INPUT.0 + n, PACK_INPUT.1, PACK_INPUT.2)
	});
}

/// ```text
/// {
///     if n != 0 { break pack; }
///     (1, 2, 3)
/// }
/// ```
///
/// A `break` contributes one value to the join and the fallthrough
/// contributes another, so every scalar needs a phi.
#[test]
fn flat_pack_crosses_a_block_join() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let (mut mir, pack) = pack_join_mir(name);
	let function = &mut mir.functions[0];

	let block_scope = push_scope(function, mir::BlockKind::Block, pack);
	let break_value = arm(
		function,
		mir::Expression {
			kind: mir::ExprKind::Break {
				scope_index: block_scope,
				value: Some(Box::new(local(0, pack))),
			},
			ty: mir::ValueType::Never,
		},
	);
	let break_if_nonzero = mir::Expression {
		kind: mir::ExprKind::IfElse {
			condition: Box::new(local(1, mir::ValueType::I32)),
			then_block: Box::new(break_value),
			else_block: None,
		},
		ty: mir::ValueType::Unit,
	};
	let value = block(
		u32::from(block_scope),
		pack,
		Box::new([break_if_nonzero, pack_literal(pack, (1, 2, 3))]),
	);
	mir.functions[0].block = block(0, pack, Box::new([value]));

	assert_pack_join(&mir, &interner, |n| {
		if n == 0 { (1, 2, 3) } else { PACK_INPUT }
	});
}

/// A function body that is `Never` never falls through, but its final Wasm
/// instruction may still be the `end` of a nested construct. The function
/// needs an explicit terminator so validation does not expect the declared
/// result at the end.
#[test]
fn a_diverging_function_body_is_terminated_for_wasm() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut mir = scalar_add(name);
	let i32_ty = mir::ValueType::I32;
	let then_block = arm(
		&mut mir.functions[0],
		mir::Expression {
			kind: mir::ExprKind::Return {
				value: Some(Box::new(int(1, i32_ty))),
			},
			ty: mir::ValueType::Never,
		},
	);
	let else_block = arm(
		&mut mir.functions[0],
		mir::Expression {
			kind: mir::ExprKind::Return {
				value: Some(Box::new(int(2, i32_ty))),
			},
			ty: mir::ValueType::Never,
		},
	);
	let body = mir::Expression {
		kind: mir::ExprKind::IfElse {
			condition: Box::new(int(1, mir::ValueType::Bool)),
			then_block: Box::new(then_block),
			else_block: Some(Box::new(else_block)),
		},
		ty: mir::ValueType::Never,
	};
	mir.functions[0].block = block(0, mir::ValueType::Never, Box::new([body]));
	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a body that returns from every branch must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	assert_eq!(run.call(&mut store, (0, 0)).unwrap(), 1);
}

/// A `Never` branch inside a value-producing `if` needs its own terminator:
/// the enclosing `if` passes a result out, and Wasm still treats the point
/// after the nested `if` as reachable.
#[test]
fn a_never_branch_in_a_value_if_is_terminated_for_wasm() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut mir = scalar_add(name);
	let i32_ty = mir::ValueType::I32;

	let inner_then = arm(
		&mut mir.functions[0],
		mir::Expression {
			kind: mir::ExprKind::Return {
				value: Some(Box::new(int(1, i32_ty))),
			},
			ty: mir::ValueType::Never,
		},
	);
	let inner_else = arm(
		&mut mir.functions[0],
		mir::Expression {
			kind: mir::ExprKind::Return {
				value: Some(Box::new(int(2, i32_ty))),
			},
			ty: mir::ValueType::Never,
		},
	);
	let inner = mir::Expression {
		kind: mir::ExprKind::IfElse {
			condition: Box::new(local(0, i32_ty)),
			then_block: Box::new(inner_then),
			else_block: Some(Box::new(inner_else)),
		},
		ty: mir::ValueType::Never,
	};

	let then_block = arm(&mut mir.functions[0], inner);
	let else_block = arm(&mut mir.functions[0], int(3, i32_ty));
	let body = mir::Expression {
		kind: mir::ExprKind::IfElse {
			condition: Box::new(local(0, i32_ty)),
			then_block: Box::new(then_block),
			else_block: Some(Box::new(else_block)),
		},
		ty: i32_ty,
	};
	mir.functions[0].block = block(0, i32_ty, Box::new([body]));

	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a never branch in a value if must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	assert_eq!(run.call(&mut store, (1, 0)).unwrap(), 1);
	assert_eq!(run.call(&mut store, (0, 0)).unwrap(), 3);
}

/// A binary operator with a `Never` operand cannot be performed: the
/// operand already left the block through `unreachable`, so the add must not
/// be emitted and the enclosing body diverges. This holds in either operand
/// position.
#[test]
fn a_diverging_operand_makes_a_binary_unreachable() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let i32_ty = mir::ValueType::I32;
	let unreachable = || mir::Expression {
		kind: mir::ExprKind::Unreachable,
		ty: mir::ValueType::Never,
	};

	for left_diverges in [true, false] {
		let mut mir = scalar_add(name);
		let left = if left_diverges {
			unreachable()
		} else {
			int(1, i32_ty)
		};
		let right = if left_diverges {
			int(1, i32_ty)
		} else {
			unreachable()
		};
		mir.functions[0].block = block(
			0,
			mir::ValueType::Never,
			Box::new([mir::Expression {
				kind: mir::ExprKind::Add {
					left: Box::new(left),
					right: Box::new(right),
				},
				ty: i32_ty,
			}]),
		);

		let module = crate::codegen::Builder::build(&mir, &interner)
			.expect("a diverging binary operand must lower");
		let bytes = module.encode();
		let (engine, module) = instantiate(&bytes);
		let mut store = wasmtime::Store::new(&engine, ());
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert!(
			run.call(&mut store, (0, 0)).is_err(),
			"left_diverges = {left_diverges}"
		);
	}
}

/// A `Never` condition means neither branch is entered, so the `if` itself
/// diverges and its branch bodies are never emitted.
#[test]
fn a_diverging_if_condition_never_enters_a_branch() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut mir = scalar_add(name);
	let i32_ty = mir::ValueType::I32;

	let then_block = arm(&mut mir.functions[0], int(1, i32_ty));
	let else_block = arm(&mut mir.functions[0], int(2, i32_ty));
	let body = mir::Expression {
		kind: mir::ExprKind::IfElse {
			condition: Box::new(mir::Expression {
				kind: mir::ExprKind::Unreachable,
				ty: mir::ValueType::Never,
			}),
			then_block: Box::new(then_block),
			else_block: Some(Box::new(else_block)),
		},
		ty: i32_ty,
	};
	mir.functions[0].block = block(0, i32_ty, Box::new([body]));

	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a diverging condition must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	assert!(run.call(&mut store, (0, 0)).is_err());
}

/// `break trap()` evaluates the value, which diverges, so the break never
/// runs. The loop therefore gets no exit value and the function diverges.
#[test]
fn a_diverging_break_value_does_not_break() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("run");
	let mut mir = scalar_add(name);
	let unit = mir::ValueType::Unit;
	let function = &mut mir.functions[0];

	let loop_scope = push_scope(function, mir::BlockKind::Loop, unit);
	let body = block(
		u32::from(loop_scope),
		mir::ValueType::Never,
		Box::new([mir::Expression {
			kind: mir::ExprKind::Break {
				scope_index: loop_scope,
				value: Some(Box::new(mir::Expression {
					kind: mir::ExprKind::Unreachable,
					ty: mir::ValueType::Never,
				})),
			},
			ty: mir::ValueType::Never,
		}]),
	);
	let loop_expression = mir::Expression {
		kind: mir::ExprKind::Loop {
			scope_index: loop_scope,
			block: Box::new(body),
		},
		ty: mir::ValueType::Never,
	};
	mir.functions[0].block =
		block(0, mir::ValueType::Never, Box::new([loop_expression]));

	let module = crate::codegen::Builder::build(&mir, &interner)
		.expect("a diverging break value must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	assert!(run.call(&mut store, (0, 0)).is_err());
}
