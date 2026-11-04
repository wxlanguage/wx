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

/// A function under construction: its arena, locals and labels.
struct Fixture {
	body: mir::Body,
	locals: Vec<mir::Local>,
	label_count: u32,
}

impl Fixture {
	fn new(locals: &[mir::ValueType]) -> Self {
		Self {
			body: mir::Body::default(),
			locals: locals
				.iter()
				.map(|&ty| mir::Local {
					ty,
					mutability: mir::Mutability::Mutable,
				})
				.collect(),
			label_count: 0,
		}
	}

	fn push(&mut self, kind: mir::ExprKind, ty: mir::ValueType) -> mir::ExprId {
		self.body.push(kind, ty)
	}

	fn local(&mut self, index: u32, ty: mir::ValueType) -> mir::ExprId {
		self.push(
			mir::ExprKind::LocalGet {
				local: mir::LocalIndex::new(index),
			},
			ty,
		)
	}

	fn int(&mut self, value: i64, ty: mir::ValueType) -> mir::ExprId {
		self.push(mir::ExprKind::Int { value }, ty)
	}

	fn unreachable(&mut self) -> mir::ExprId {
		self.push(mir::ExprKind::Unreachable, mir::ValueType::Never)
	}

	fn binary(
		&mut self,
		op: mir::BinaryOp,
		lhs: mir::ExprId,
		rhs: mir::ExprId,
		ty: mir::ValueType,
	) -> mir::ExprId {
		self.push(mir::ExprKind::Binary { op, lhs, rhs }, ty)
	}

	fn sequence(
		&mut self,
		statements: impl IntoIterator<Item = mir::ExprId>,
		ty: mir::ValueType,
	) -> mir::ExprId {
		let statements = self.body.push_list(statements);
		self.push(mir::ExprKind::Sequence { statements }, ty)
	}

	fn if_else(
		&mut self,
		condition: mir::ExprId,
		then: mir::ExprId,
		otherwise: Option<mir::ExprId>,
		ty: mir::ValueType,
	) -> mir::ExprId {
		self.push(
			mir::ExprKind::IfElse {
				condition,
				then,
				otherwise,
			},
			ty,
		)
	}

	fn ret(&mut self, value: mir::ExprId) -> mir::ExprId {
		self.push(
			mir::ExprKind::Return { value: Some(value) },
			mir::ValueType::Never,
		)
	}

	fn label(&mut self) -> mir::LabelId {
		let label = mir::LabelId::new(self.label_count);
		self.label_count += 1;
		label
	}

	/// The finished function, whose body is `root`. Its arena must satisfy
	/// MIR's invariants, as lowering's does.
	fn finish(
		self,
		signature_index: mir::SignatureIndex,
		root: mir::ExprId,
	) -> mir::Function {
		mir::body::verify(&self.body, root, &self.locals, self.label_count)
			.expect("a fixture is a valid MIR arena");
		mir::Function {
			signature_index,
			origin: mir::Origin::Defined(mir::Code {
				locals: self.locals,
				label_count: self.label_count,
				body: self.body,
				root,
			}),
		}
	}
}

/// A module of `functions`, which export `exports` and use `signatures`,
/// `aggregates` and `memories`.
fn module(
	functions: Vec<mir::Function>,
	signatures: Vec<mir::FunctionSignature>,
	exports: Vec<mir::Export>,
	aggregates: Box<[mir::Aggregate]>,
	memories: Vec<mir::MemoryInfo>,
) -> mir::MIR {
	let function_flags = vec![mir::FunctionFlags::empty(); functions.len()];
	mir::MIR {
		functions,
		function_flags,
		signatures,
		globals: Vec::new(),
		exports,
		imports: Vec::new(),
		memories,
		aggregates,
		static_entries: Vec::new(),
		start_function: None,
	}
}

fn export(name: SymbolU32) -> Vec<mir::Export> {
	vec![mir::Export {
		name,
		item: mir::Item::Function(mir::FunctionId::new(0)),
	}]
}

fn signature(
	items: impl Into<Box<[mir::ValueType]>>,
	params_count: usize,
) -> mir::FunctionSignature {
	mir::FunctionSignature {
		items: items.into(),
		params_count,
	}
}

/// `func add(a: i32, b: i32) -> i32 { a + b }`, written directly as MIR, with
/// the body built by `body` over the two `i32` parameters.
///
/// Contract this fixture depends on:
/// - parameters are the first `params_count` entries of `Function::locals`,
/// - the root's value is returned implicitly,
/// - `MIR::signatures[signature_index]` is the sole source of the Wasm
///   signature.
fn scalar_function(
	name: SymbolU32,
	body: impl FnOnce(&mut Fixture) -> mir::ExprId,
) -> mir::MIR {
	let i32_ty = mir::ValueType::I32;
	let mut fixture = Fixture::new(&[i32_ty, i32_ty]);
	let root = body(&mut fixture);
	module(
		vec![fixture.finish(mir::SignatureIndex::new(0), root)],
		vec![signature([i32_ty, i32_ty, i32_ty], 2)],
		export(name),
		Box::new([]),
		Vec::new(),
	)
}

fn scalar_add(name: SymbolU32) -> mir::MIR {
	scalar_function(name, |f| {
		let i32_ty = mir::ValueType::I32;
		let a = f.local(0, i32_ty);
		let b = f.local(1, i32_ty);
		f.binary(mir::BinaryOp::Add, a, b, i32_ty)
	})
}

fn instantiate(bytes: &[u8]) -> (wasmtime::Engine, wasmtime::Module) {
	let engine = wasmtime::Engine::default();
	let module = wasmtime::Module::new(&engine, bytes)
		.expect("backend emitted an invalid Wasm module");
	(engine, module)
}

/// Encode `mir` and instantiate it with no imports.
fn run(
	mir: &mir::MIR,
	interner: &StringInterner,
) -> (wasmtime::Store<()>, wasmtime::Instance) {
	let module = crate::codegen::Builder::build(mir, interner)
		.expect("a fixture module must lower");
	let bytes = module.encode();
	let (engine, module) = instantiate(&bytes);
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[])
		.expect("a backend module with no imports must instantiate");
	(store, instance)
}

#[test]
fn hand_built_scalar_add_runs_under_wasmtime() {
	let mut interner = StringInterner::new();
	let name = interner.get_or_intern("add");
	let (mut store, instance) = run(&scalar_add(name), &interner);
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
	let (mut store, instance) = run(&scalar_add(name), &interner);
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

/// `triple` (id 1) calls `add` (id 0) and is the only export. A call names its
/// callee by `FunctionId`, which codegen maps to a Wasm index through its own
/// table, so the export's index and the callee's are both looked up.
#[test]
fn direct_call_resolves_its_callee_by_id() {
	let mut interner = StringInterner::new();
	let triple_name = interner.get_or_intern("triple");

	let i32_ty = mir::ValueType::I32;
	let add_id = mir::FunctionId::new(0);
	let triple_id = mir::FunctionId::new(1);
	let add_sig = mir::SignatureIndex::new(0);
	let triple_sig = mir::SignatureIndex::new(1);

	let mut add = Fixture::new(&[i32_ty, i32_ty]);
	let a = add.local(0, i32_ty);
	let b = add.local(1, i32_ty);
	let sum = add.binary(mir::BinaryOp::Add, a, b, i32_ty);
	let add = add.finish(add_sig, sum);

	// `triple(a) = add(add(a, a), a)`
	let mut triple = Fixture::new(&[i32_ty]);
	let call_add = |f: &mut Fixture, lhs, rhs| {
		let args = f.body.push_list([lhs, rhs]);
		f.push(
			mir::ExprKind::Call {
				function: add_id,
				args,
			},
			i32_ty,
		)
	};
	let first = triple.local(0, i32_ty);
	let second = triple.local(0, i32_ty);
	let inner = call_add(&mut triple, first, second);
	let third = triple.local(0, i32_ty);
	let outer = call_add(&mut triple, inner, third);
	let triple = triple.finish(triple_sig, outer);

	let mir = module(
		vec![add, triple],
		vec![
			signature([i32_ty, i32_ty, i32_ty], 2),
			signature([i32_ty, i32_ty], 1),
		],
		vec![mir::Export {
			name: triple_name,
			item: mir::Item::Function(triple_id),
		}],
		Box::new([]),
		Vec::new(),
	);

	let (mut store, instance) = run(&mir, &interner);
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
/// `FunctionSignature::items` + the aggregate's scalars, so this pins the
/// parameter/result flattening without involving TIR.
fn aggregate_identity_mir(
	name: SymbolU32,
	aggregate_index: mir::AggregateIndex,
	aggregates: Box<[mir::Aggregate]>,
) -> mir::MIR {
	let ty = mir::ValueType::Aggregate { aggregate_index };
	let mut fixture = Fixture::new(&[ty]);
	let root = fixture.local(0, ty);
	module(
		vec![fixture.finish(mir::SignatureIndex::new(0), root)],
		vec![signature([ty, ty], 1)],
		export(name),
		aggregates,
		Vec::new(),
	)
}

fn run_aggregate_identity(mir: &mir::MIR, interner: &StringInterner) {
	let (mut store, instance) = run(mir, interner);
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
	let mut fixture = Fixture::new(&[aggregate_ty]);
	let root = fixture.push(
		mir::ExprKind::AggregateGet {
			local: mir::LocalIndex::new(0),
			range: mir::ScalarRange::new(1, 1),
		},
		mir::ValueType::U8,
	);
	let mir = module(
		vec![fixture.finish(mir::SignatureIndex::new(0), root)],
		vec![signature([aggregate_ty, mir::ValueType::U8], 1)],
		export(name),
		aggregates,
		Vec::new(),
	);

	let (mut store, instance) = run(&mir, &interner);
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

	let mut fixture = Fixture::new(&[aggregate_ty]);
	let store_address = fixture.int(0, mir::ValueType::I32);
	let param = fixture.local(0, aggregate_ty);
	let store = fixture.push(
		mir::ExprKind::PointerStore {
			pointer: store_address,
			value: param,
			offset: 0,
			memory,
		},
		mir::ValueType::Unit,
	);
	let load_address = fixture.int(0, mir::ValueType::I32);
	let load = fixture.push(
		mir::ExprKind::PointerLoad {
			pointer: load_address,
			offset: 0,
			memory,
		},
		aggregate_ty,
	);
	let root = fixture.sequence([store, load], aggregate_ty);
	let mir = module(
		vec![fixture.finish(mir::SignatureIndex::new(0), root)],
		vec![signature([aggregate_ty, aggregate_ty], 1)],
		export(name),
		aggregates,
		vec![mir::MemoryInfo {
			id: memory,
			kind: mir::MemoryKind::Memory32,
			min_pages: Some(1),
			max_pages: None,
			origin: mir::Origin::Defined(()),
		}],
	);

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

/// The pack type and its aggregate table, for
///
/// ```text
/// fn run(pack: (i32, i64, i32), n: i32) -> (i32, i64, i32)
/// ```
///
/// Each test builds the body as one control-flow construct and checks that
/// the pack still crosses its join unchanged.
fn pack_type() -> (mir::ValueType, Box<[mir::Aggregate]>) {
	let mut table = AggregateTable::default();
	let aggregate_index = table.push(
		Box::new([
			mir::ValueType::I32,
			mir::ValueType::I64,
			mir::ValueType::I32,
		]),
		None,
	);
	(
		mir::ValueType::Aggregate { aggregate_index },
		table.finish(),
	)
}

/// The `run` module whose body `body` builds over the pack (local 0) and `n`
/// (local 1).
fn pack_join_mir(
	name: SymbolU32,
	body: impl FnOnce(&mut Fixture, mir::ValueType) -> mir::ExprId,
) -> mir::MIR {
	let (pack, aggregates) = pack_type();
	let mut fixture = Fixture::new(&[pack, mir::ValueType::I32]);
	let root = body(&mut fixture, pack);
	module(
		vec![fixture.finish(mir::SignatureIndex::new(0), root)],
		vec![signature([pack, mir::ValueType::I32, pack], 2)],
		export(name),
		aggregates,
		Vec::new(),
	)
}

fn pack_literal(
	f: &mut Fixture,
	pack: mir::ValueType,
	values: (i32, i64, i32),
) -> mir::ExprId {
	let first = f.int(i64::from(values.0), mir::ValueType::I32);
	let second = f.int(values.1, mir::ValueType::I64);
	let third = f.int(i64::from(values.2), mir::ValueType::I32);
	let values = f.body.push_list([first, second, third]);
	f.push(mir::ExprKind::Aggregate { values }, pack)
}

/// Run `mir`'s exported `run` for a few values of `n` and compare the pack
/// result. Every fixture passes the same `PACK_INPUT` pack and varies only
/// `n`, so `expected` fully describes the control-flow behaviour.
fn assert_pack_join(
	mir: &mir::MIR,
	interner: &StringInterner,
	expected: impl Fn(i32) -> (i32, i64, i32),
) {
	let (mut store, instance) = run(mir, interner);
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
	let mir = pack_join_mir(name, |f, pack| {
		let condition = f.local(1, mir::ValueType::I32);
		let then = f.local(0, pack);
		let otherwise = pack_literal(f, pack, (1, 2, 3));
		f.if_else(condition, then, Some(otherwise), pack)
	});

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
	let mir = pack_join_mir(name, |f, pack| {
		let selector = f.local(1, mir::ValueType::I32);
		let case_zero = pack_literal(f, pack, (1, 2, 3));
		let case_one = f.local(0, pack);
		let case_two = pack_literal(f, pack, (4, 5, 6));
		let default = f.local(0, pack);
		let cases = f.body.push_cases([
			mir::Case {
				value: 0,
				body: case_zero,
			},
			mir::Case {
				value: 1,
				body: case_one,
			},
			mir::Case {
				value: 2,
				body: case_two,
			},
		]);
		f.push(
			mir::ExprKind::Switch {
				selector,
				cases,
				default: Some(default),
			},
			pack,
		)
	});

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
	let mir = pack_join_mir(name, |f, pack| {
		let unit = mir::ValueType::Unit;
		let i32_ty = mir::ValueType::I32;
		let label = f.label();

		// `if n == 0 { break }`
		let n = f.local(1, i32_ty);
		let is_zero = f.push(
			mir::ExprKind::Unary {
				op: mir::UnaryOp::Eqz,
				value: n,
			},
			mir::ValueType::Bool,
		);
		let leave = f.push(
			mir::ExprKind::Break { label, value: None },
			mir::ValueType::Never,
		);
		let break_when_zero = f.if_else(is_zero, leave, None, unit);

		// `pack.0 += 1`
		let first = f.push(
			mir::ExprKind::AggregateGet {
				local: mir::LocalIndex::new(0),
				range: mir::ScalarRange::new(0, 1),
			},
			i32_ty,
		);
		let one = f.int(1, i32_ty);
		let bumped = f.binary(mir::BinaryOp::Add, first, one, i32_ty);
		let bump_first_scalar = f.push(
			mir::ExprKind::AggregateSet {
				local: mir::LocalIndex::new(0),
				range: mir::ScalarRange::new(0, 1),
				value: bumped,
			},
			unit,
		);

		// `n -= 1`
		let n = f.local(1, i32_ty);
		let one = f.int(1, i32_ty);
		let decremented = f.binary(mir::BinaryOp::Sub, n, one, i32_ty);
		let decrement_n = f.push(
			mir::ExprKind::LocalSet {
				local: mir::LocalIndex::new(1),
				value: decremented,
			},
			unit,
		);

		let body =
			f.sequence([break_when_zero, bump_first_scalar, decrement_n], unit);
		let looped = f.push(mir::ExprKind::Loop { label, body }, unit);
		let result = f.local(0, pack);
		f.sequence([looped, result], pack)
	});

	assert_pack_join(&mir, &interner, |n| {
		(PACK_INPUT.0 + n, PACK_INPUT.1, PACK_INPUT.2)
	});
}

/// ```text
/// block :l {
///     if n != 0 { break :l pack; }
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
	let mir = pack_join_mir(name, |f, pack| {
		let label = f.label();
		let condition = f.local(1, mir::ValueType::I32);
		let value = f.local(0, pack);
		let leave = f.push(
			mir::ExprKind::Break {
				label,
				value: Some(value),
			},
			mir::ValueType::Never,
		);
		let break_if_nonzero =
			f.if_else(condition, leave, None, mir::ValueType::Unit);
		let fallthrough = pack_literal(f, pack, (1, 2, 3));
		let statements = f.body.push_list([break_if_nonzero, fallthrough]);
		f.push(mir::ExprKind::Block { label, statements }, pack)
	});

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
	let mir = scalar_function(name, |f| {
		let i32_ty = mir::ValueType::I32;
		let condition = f.int(1, mir::ValueType::Bool);
		let one = f.int(1, i32_ty);
		let then = f.ret(one);
		let two = f.int(2, i32_ty);
		let otherwise = f.ret(two);
		f.if_else(condition, then, Some(otherwise), mir::ValueType::Never)
	});
	let (mut store, instance) = run(&mir, &interner);
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
	let mir = scalar_function(name, |f| {
		let i32_ty = mir::ValueType::I32;
		let inner_condition = f.local(0, i32_ty);
		let one = f.int(1, i32_ty);
		let inner_then = f.ret(one);
		let two = f.int(2, i32_ty);
		let inner_else = f.ret(two);
		let inner = f.if_else(
			inner_condition,
			inner_then,
			Some(inner_else),
			mir::ValueType::Never,
		);
		let condition = f.local(0, i32_ty);
		let three = f.int(3, i32_ty);
		f.if_else(condition, inner, Some(three), i32_ty)
	});

	let (mut store, instance) = run(&mir, &interner);
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

	for left_diverges in [true, false] {
		let mir = scalar_function(name, |f| {
			let i32_ty = mir::ValueType::I32;
			let (lhs, rhs) = if left_diverges {
				let lhs = f.unreachable();
				(lhs, f.int(1, i32_ty))
			} else {
				let lhs = f.int(1, i32_ty);
				(lhs, f.unreachable())
			};
			let sum = f.binary(mir::BinaryOp::Add, lhs, rhs, i32_ty);
			f.sequence([sum], mir::ValueType::Never)
		});

		let (mut store, instance) = run(&mir, &interner);
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
	let mir = scalar_function(name, |f| {
		let i32_ty = mir::ValueType::I32;
		let condition = f.unreachable();
		let then = f.int(1, i32_ty);
		let otherwise = f.int(2, i32_ty);
		f.if_else(condition, then, Some(otherwise), i32_ty)
	});

	let (mut store, instance) = run(&mir, &interner);
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
	let mir = scalar_function(name, |f| {
		let label = f.label();
		let value = f.unreachable();
		let leave = f.push(
			mir::ExprKind::Break {
				label,
				value: Some(value),
			},
			mir::ValueType::Never,
		);
		let body = f.sequence([leave], mir::ValueType::Never);
		f.push(mir::ExprKind::Loop { label, body }, mir::ValueType::Never)
	});

	let (mut store, instance) = run(&mir, &interner);
	let run = instance
		.get_typed_func::<(i32, i32), i32>(&mut store, "run")
		.unwrap();
	assert!(run.call(&mut store, (0, 0)).is_err());
}
