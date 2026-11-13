use super::*;
use crate::mir::{
	AddressTarget, Body, Code, ConstInit, Export, ExprId, ExprKind, ExprList,
	Function, FunctionFlags, Global, GlobalId, Import, ImportIdx, MemoryId,
	MemoryInfo, MemoryKind, Mutability, Origin, Relocation, Signatures,
	StaticEntry, StaticEntryId, ValueType,
};
use string_interner::{Symbol, symbol::SymbolU32};

fn empty() -> MIR {
	MIR {
		functions: vec![],
		function_flags: vec![],
		signatures: Signatures::default(),
		globals: vec![],
		exports: vec![],
		imports: vec![],
		memories: vec![],
		static_entries: vec![],
		start_function: None,
	}
}

fn symbol() -> SymbolU32 {
	SymbolU32::try_from_usize(0).unwrap()
}

fn export(mir: &mut MIR, item: Item) {
	mir.exports.push(Export {
		name: symbol(),
		item,
	});
}

fn function(id: u32) -> Reference {
	Reference::Item(Item::Function(FunctionId::new(id)))
}

fn data(id: u32) -> Reference {
	Reference::Data(StaticEntryId::new(id))
}

fn memory(id: u32) -> Reference {
	Reference::Item(Item::Memory(MemoryId::new(id)))
}

fn call(id: u32) -> ExprKind {
	ExprKind::Call {
		function: FunctionId::new(id),
		args: ExprList::EMPTY,
	}
}

fn add_body(mir: &mut MIR, body: Body, root: ExprId) -> FunctionId {
	let results = if body.ty(root).is_scalar() {
		vec![body.ty(root)]
	} else {
		vec![]
	};
	let signature = mir.signatures.intern(&[], &results);
	let id = FunctionId::new(mir.functions.len() as u32);
	mir.functions.push(Function {
		signature,
		origin: Origin::Defined(Code {
			locals: vec![],
			label_count: 0,
			body,
			root,
		}),
	});
	mir.function_flags.push(FunctionFlags::empty());
	id
}

fn add_function(
	mir: &mut MIR,
	kinds: impl IntoIterator<Item = ExprKind>,
) -> FunctionId {
	let mut body = Body::default();
	let statements: Vec<_> = kinds
		.into_iter()
		.map(|kind| {
			let ty = if matches!(
				kind,
				ExprKind::Return { .. } | ExprKind::Unreachable
			) {
				ValueType::Never
			} else {
				ValueType::Unit
			};
			body.push(kind, ty)
		})
		.collect();
	let statements = body.push_list(statements);
	let root = body.push(ExprKind::Sequence { statements }, ValueType::Unit);
	add_body(mir, body, root)
}

fn add_memory(mir: &mut MIR) -> MemoryId {
	let id = MemoryId::new(mir.memories.len() as u32);
	mir.memories.push(MemoryInfo {
		id,
		kind: MemoryKind::Memory32,
		min_pages: None,
		max_pages: None,
		origin: Origin::Defined(()),
	});
	id
}

fn add_global(mir: &mut MIR, init: ConstInit) -> GlobalId {
	let id = GlobalId::new(mir.globals.len() as u32);
	mir.globals.push(Global {
		id,
		ty: ValueType::I32,
		mutability: Mutability::Mutable,
		origin: Origin::Defined(init),
	});
	id
}

fn add_data(
	mir: &mut MIR,
	memory: MemoryId,
	targets: &[AddressTarget],
) -> StaticEntryId {
	let id = StaticEntryId::new(mir.static_entries.len() as u32);
	mir.static_entries.push(StaticEntry {
		memory,
		align: 4,
		bytes: vec![0; targets.len().max(1) * 4].into(),
		relocations: targets
			.iter()
			.enumerate()
			.map(|(index, &target)| Relocation {
				offset: index as u32 * 4,
				target,
			})
			.collect(),
	});
	id
}

fn import(mir: &mut MIR, item: Item) {
	let id = ImportIdx::new(mir.imports.len() as u32);
	mir.imports.push(Import {
		module: symbol(),
		name: symbol(),
		item,
	});
	match item {
		Item::Function(function) => {
			mir.functions[usize::from(function)].origin = Origin::Imported(id)
		}
		Item::Global(global) => {
			mir.globals[usize::from(global)].origin = Origin::Imported(id)
		}
		Item::Memory(memory) => {
			mir.memories[usize::from(memory)].origin = Origin::Imported(id)
		}
	}
}

fn discover_counted(mir: &mut MIR) -> (Reachability, Vec<usize>) {
	let mut counts = vec![0; mir.functions.len()];
	let reached = discover(mir, |mir, id| {
		counts[usize::from(id)] += 1;
		crate::opt::optimize_function(mir, id);
	});
	(reached, counts)
}

#[test]
fn removed_calls_do_not_schedule_callees_and_ids_stay_stable() {
	let mut mir = empty();
	let root = add_function(
		&mut mir,
		[call(1), ExprKind::Return { value: None }, call(2)],
	);
	add_function(&mut mir, [ExprKind::Noop]);
	let dead = add_function(&mut mir, [call(2)]);
	export(&mut mir, Item::Function(root));
	let untouched = mir.code(dead).body.kinds().as_ptr();
	let signatures: Vec<_> = mir
		.functions
		.iter()
		.map(|function| function.signature)
		.collect();
	let flags = mir.function_flags.clone();
	let (reached, counts) = discover_counted(&mut mir);
	assert_eq!(counts, [1, 1, 0]);
	assert_eq!(reached.functions, [true, true, false]);
	assert_eq!(mir.functions.len(), 3, "discovery does not compact");
	assert_eq!(mir.function_flags, flags);
	assert_eq!(
		mir.functions
			.iter()
			.map(|function| function.signature)
			.collect::<Vec<_>>(),
		signatures
	);
	assert_eq!(mir.exports[0].item, Item::Function(root));
	assert_eq!(
		mir.code(root).callees().collect::<Vec<_>>(),
		[FunctionId::new(1)]
	);
	assert_eq!(mir.code(dead).body.kinds().as_ptr(), untouched);
	assert_eq!(mir.code(dead).callees().collect::<Vec<_>>(), [dead]);
}

#[test]
fn duplicate_roots_calls_and_recursive_cycles_process_each_function_once() {
	let mut mir = empty();
	let root = add_function(&mut mir, [call(0), call(1), call(1)]);
	add_function(&mut mir, [call(2)]);
	add_function(&mut mir, [call(1)]);
	add_function(&mut mir, [call(4)]);
	add_function(&mut mir, [call(3)]);
	export(&mut mir, Item::Function(root));
	export(&mut mir, Item::Function(root));
	mir.start_function = Some(root);
	let (reached, counts) = discover_counted(&mut mir);
	assert_eq!(counts, [1, 1, 1, 0, 0]);
	assert_eq!(reached.functions, [true, true, true, false, false]);
	assert_eq!(mir.start_function, Some(root));
	assert_eq!(mir.functions.len(), 5);
}

#[test]
fn imports_are_retained_by_references_but_never_optimized_or_independent_roots()
{
	let mut mir = empty();
	let exported = add_function(&mut mir, []);
	let caller = add_function(&mut mir, [call(2)]);
	let called = add_function(&mut mir, []);
	let unused = add_function(&mut mir, []);
	for id in [exported, called, unused] {
		import(&mut mir, Item::Function(id));
	}
	for _ in 0..2 {
		let global = add_global(&mut mir, ConstInit::Int(0));
		import(&mut mir, Item::Global(global));
		let memory = add_memory(&mut mir);
		import(&mut mir, Item::Memory(memory));
	}
	for item in [
		Item::Function(exported),
		Item::Function(caller),
		Item::Global(GlobalId::new(0)),
		Item::Memory(MemoryId::new(0)),
	] {
		export(&mut mir, item);
	}
	assert_eq!(mir.verify_imports(), Ok(()));
	let (reached, counts) = discover_counted(&mut mir);
	assert_eq!(counts, [0, 1, 0, 0]);
	assert_eq!(reached.functions, [true, true, true, false]);
	assert_eq!(reached.globals, [true, false]);
	assert_eq!(reached.memories, [true, false]);
	assert_eq!(mir.imports.len(), 7);
	assert_eq!(mir.verify_imports(), Ok(()));
}

#[test]
fn backing_data_follows_pointer_and_relocation_edges_without_reverse_memory_edges()
 {
	let mut mir = empty();
	let first_memory = add_memory(&mut mir);
	let second_memory = add_memory(&mut mir);
	add_data(
		&mut mir,
		first_memory,
		&[
			AddressTarget::Entry(StaticEntryId::new(1)),
			AddressTarget::DataEnd(second_memory),
		],
	);
	add_data(
		&mut mir,
		first_memory,
		&[AddressTarget::Entry(StaticEntryId::new(0))],
	);
	add_data(
		&mut mir,
		first_memory,
		&[AddressTarget::Entry(StaticEntryId::new(2))],
	);
	let pointer = add_global(
		&mut mir,
		ConstInit::Static {
			entry: StaticEntryId::new(0),
			offset: 0,
		},
	);
	export(&mut mir, Item::Memory(first_memory));
	// An exported memory alone does not keep any entries, even cyclic ones.
	let reached = optimize_reachable(&mut mir);
	assert_eq!(reached.data, [false, false, false]);
	assert_eq!(reached.memories, [true, false]);
	export(&mut mir, Item::Global(pointer));
	let reached = optimize_reachable(&mut mir);
	assert_eq!(reached.data, [true, true, false]);
	assert_eq!(reached.memories, [true, true]);
	assert!(reached.is_reachable(data(0)));
	assert!(!reached.is_reachable(data(2)));
	assert!(reached.is_reachable(memory(1)));
	assert_eq!(mir.static_entries.len(), 3);
}

#[test]
fn data_end_does_not_keep_backing_data_and_function_pointers_do() {
	let mut mir = empty();
	let memory = add_memory(&mut mir);
	let entry = add_data(&mut mir, memory, &[]);
	let end = add_global(&mut mir, ConstInit::DataEnd { memory });
	export(&mut mir, Item::Global(end));
	let reached = optimize_reachable(&mut mir);
	assert_eq!(reached.memories, [true]);
	assert_eq!(reached.data, [false]);
	let mut body = Body::default();
	let pointer =
		body.push(ExprKind::StaticPointer { entry, offset: 0 }, ValueType::I32);
	let root = add_body(&mut mir, body, pointer);
	export(&mut mir, Item::Function(root));
	let (reached, counts) = discover_counted(&mut mir);
	assert_eq!(counts, [1]);
	assert!(reached.is_reachable(function(0)));
	assert_eq!(reached.data, [true]);
}

#[test]
fn start_root_preserves_initialization_and_global_dependencies() {
	let mut mir = empty();
	let memory = add_memory(&mut mir);
	let entry = add_data(&mut mir, memory, &[]);
	let global = add_global(&mut mir, ConstInit::Int(0));
	let mut body = Body::default();
	let value =
		body.push(ExprKind::StaticPointer { entry, offset: 0 }, ValueType::I32);
	let root =
		body.push(ExprKind::GlobalSet { id: global, value }, ValueType::Unit);
	let start = add_body(&mut mir, body, root);
	mir.start_function = Some(start);
	let (reached, counts) = discover_counted(&mut mir);
	assert_eq!(counts, [1]);
	assert_eq!(reached.globals, [true]);
	assert_eq!(reached.data, [true]);
	assert_eq!(reached.memories, [true]);
	assert!(mir.code(start).body.kinds().iter().any(
		|kind| matches!(kind, ExprKind::GlobalSet { id, .. } if *id == global)
	));
}

#[test]
fn rootless_program_does_no_body_work() {
	let mut mir = empty();
	add_function(&mut mir, [call(1)]);
	add_function(&mut mir, [call(0)]);
	let memory = add_memory(&mut mir);
	add_data(&mut mir, memory, &[]);
	let (reached, counts) = discover_counted(&mut mir);
	assert_eq!(counts, [0, 0]);
	assert_eq!(reached.functions, [false, false]);
	assert_eq!(reached.memories, [false]);
	assert_eq!(reached.data, [false]);
}

#[test]
fn deep_call_chain_uses_the_worklist_without_recursive_discovery() {
	let mut mir = empty();
	const COUNT: u32 = 4096;
	for id in 0..COUNT - 1 {
		add_function(&mut mir, [call(id + 1)]);
	}
	add_function(&mut mir, []);
	export(&mut mir, Item::Function(FunctionId::new(0)));
	let (reached, counts) = discover_counted(&mut mir);
	assert!(counts.iter().all(|&count| count == 1));
	assert!(reached.functions.iter().all(|&marked| marked));
	assert_eq!(mir.functions.len(), COUNT as usize);
}
