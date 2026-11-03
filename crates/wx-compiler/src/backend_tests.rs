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

use crate::mir::layout::AggregateInterner;
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

	let mut layout_interner = AggregateInterner::default();
	let aggregate_index = layout_interner.intern(
		Box::new([mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8]),
		Box::new([8, 0, 9]),
		mir::Layout { size: 16, align: 8 },
	);
	let aggregates = layout_interner.finish();

	let aggregate = &aggregates[usize::from(aggregate_index)];
	let offsets: Vec<u32> =
		aggregate.fields.iter().map(|field| field.offset).collect();
	assert_eq!(offsets, vec![8, 0, 9], "memory layout is alignment-sorted");
	assert_eq!((aggregate.layout.size, aggregate.layout.align), (16, 8));

	let scalar_types: Vec<ScalarType> = aggregate
		.scalars
		.iter()
		.map(|scalar| ScalarType::try_from(scalar.ty).unwrap())
		.collect();
	assert_eq!(
		scalar_types,
		vec![ScalarType::I32, ScalarType::I64, ScalarType::I32],
		"slots follow declaration order, not memory order"
	);
	let scalar_offsets: Vec<u32> = aggregate
		.scalars
		.iter()
		.map(|scalar| scalar.offset)
		.collect();
	assert_eq!(scalar_offsets, vec![8, 0, 9]);

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

	let mut layout_interner = AggregateInterner::default();
	let aggregate_index = layout_interner.intern(
		Box::new([mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8]),
		Box::new([0, 8, 16]),
		mir::Layout { size: 24, align: 8 },
	);
	let aggregates = layout_interner.finish();

	let aggregate = &aggregates[usize::from(aggregate_index)];
	let offsets: Vec<u32> =
		aggregate.fields.iter().map(|field| field.offset).collect();
	assert_eq!(offsets, vec![0, 8, 16], "declaration order, padded");
	assert_eq!((aggregate.layout.size, aggregate.layout.align), (24, 8));

	let scalar_offsets: Vec<u32> = aggregate
		.scalars
		.iter()
		.map(|scalar| scalar.offset)
		.collect();
	assert_eq!(scalar_offsets, vec![0, 8, 16]);

	let mir = aggregate_identity_mir(name, aggregate_index, aggregates);
	run_aggregate_identity(&mir, &interner);
}

/// A zero-sized field in the middle keeps its declaration position but owns
/// no slot, so the second slot belongs to the *third* field. This is the
/// case that used to project the wrong value: `field_range(zst).start` names
/// its neighbour.
#[test]
fn zero_sized_field_has_a_position_but_no_slot() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("last");

	let mut layout_interner = AggregateInterner::default();
	let aggregate_index = layout_interner.intern(
		Box::new([
			mir::ValueType::U8,
			mir::ValueType::Unit,
			mir::ValueType::U8,
		]),
		Box::new([0, 1, 1]),
		mir::Layout { size: 2, align: 1 },
	);
	let aggregates = layout_interner.finish();

	let aggregate = &aggregates[usize::from(aggregate_index)];
	assert_eq!(aggregate.field_count(), 3);
	assert_eq!(aggregate.scalars.len(), 2);

	let zst = mir::FieldIndex::new(1);
	assert!(aggregate.scalars.of_field(zst).is_empty());
	assert_eq!(aggregate.scalars.field_range(zst), 1..1);

	// Slot 0 belongs to field 0; slot 1 must belong to field 2, never to the
	// zero-sized field 1.
	assert_eq!(
		aggregate.scalars.owner(mir::ScalarIndex::new(0)),
		mir::FieldIndex::new(0)
	);
	assert_eq!(
		aggregate.scalars.owner(mir::ScalarIndex::new(1)),
		mir::FieldIndex::new(2)
	);

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
							value_index: mir::FieldIndex::new(2),
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

	let mut layout_interner = AggregateInterner::default();
	let aggregate_index = layout_interner.intern(
		Box::new([mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8]),
		Box::new([8, 0, 9]),
		mir::Layout { size: 16, align: 8 },
	);
	let aggregates = layout_interner.finish();
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
