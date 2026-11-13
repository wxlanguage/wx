use super::*;
use crate::mir::{
	Body, Code, Export, ExprId, ExprKind, ExprList, Function, FunctionFlags,
	Global, ImportIdx, LoadAccess, MemoryInfo, MemoryKind, Mutability, Origin,
	Relocation, Signatures, StoreAccess, ValueType,
};
use string_interner::Symbol;

fn function(id: u32) -> Reference {
	Reference::Item(Item::Function(FunctionId::new(id)))
}

fn global(id: u32) -> Reference {
	Reference::Item(Item::Global(GlobalId::new(id)))
}

fn memory(id: u32) -> Reference {
	Reference::Item(Item::Memory(MemoryId::new(id)))
}

fn data(id: u32) -> Reference {
	Reference::Data(StaticEntryId::new(id))
}

fn dependencies(mir: &MIR, node: Reference) -> Vec<Reference> {
	let mut result = Vec::new();
	mir.dependencies(node, |target| result.push(target));
	result
}

fn rewrite(reference: ItemRef<'_>) {
	match reference {
		ItemRef::Function(id) => *id = FunctionId::new(u32::from(*id) + 10),
		ItemRef::Global(id) => *id = GlobalId::new(u32::from(*id) + 10),
		ItemRef::Memory(id) => *id = MemoryId::new(u32::from(*id) + 10),
		ItemRef::Data(id) => *id = StaticEntryId::new(u32::from(*id) + 10),
	}
}

#[test]
fn expression_references_support_discovery_and_remapping() {
	let memory_id = MemoryId::new(2);
	let expr = ExprId::new(99);
	let cases = [
		(
			ExprKind::Call {
				function: FunctionId::new(1),
				args: ExprList::EMPTY,
			},
			vec![function(1)],
			vec![function(11)],
		),
		(
			ExprKind::Global {
				id: GlobalId::new(3),
			},
			vec![global(3)],
			vec![global(13)],
		),
		(
			ExprKind::GlobalSet {
				id: GlobalId::new(3),
				value: expr,
			},
			vec![global(3)],
			vec![global(13)],
		),
		(
			ExprKind::DataEnd { memory: memory_id },
			vec![memory(2)],
			vec![memory(12)],
		),
		(
			ExprKind::MemoryIndex { memory: memory_id },
			vec![memory(2)],
			vec![memory(12)],
		),
		(
			ExprKind::MemorySize { memory: memory_id },
			vec![memory(2)],
			vec![memory(12)],
		),
		(
			ExprKind::MemoryGrow {
				memory: memory_id,
				delta: expr,
			},
			vec![memory(2)],
			vec![memory(12)],
		),
		(
			ExprKind::MemoryFill {
				memory: memory_id,
				dst: expr,
				value: expr,
				len: expr,
			},
			vec![memory(2)],
			vec![memory(12)],
		),
		(
			ExprKind::MemoryCopy {
				dst_memory: memory_id,
				src_memory: MemoryId::new(4),
				dst: expr,
				src: expr,
				len: expr,
			},
			vec![memory(2), memory(4)],
			vec![memory(12), memory(14)],
		),
		(
			ExprKind::MemoryCopy {
				dst_memory: memory_id,
				src_memory: memory_id,
				dst: expr,
				src: expr,
				len: expr,
			},
			vec![memory(2), memory(2)],
			vec![memory(12), memory(12)],
		),
		(
			ExprKind::PointerLoad {
				memory: memory_id,
				pointer: expr,
				offset: 7,
				access: LoadAccess::I32,
			},
			vec![memory(2)],
			vec![memory(12)],
		),
		(
			ExprKind::PointerStore {
				memory: memory_id,
				pointer: expr,
				value: expr,
				offset: 7,
				access: StoreAccess::I32,
			},
			vec![memory(2)],
			vec![memory(12)],
		),
		(
			ExprKind::StaticPointer {
				entry: StaticEntryId::new(5),
				offset: 7,
			},
			vec![data(5)],
			vec![data(15)],
		),
		(ExprKind::Int { value: 5 }, vec![], vec![]),
		(ExprKind::Return { value: Some(expr) }, vec![], vec![]),
	];
	for (mut kind, expected, remapped) in cases {
		let mut found = Vec::new();
		kind.items_mut(|reference| found.push(reference.target()));
		assert_eq!(found, expected, "{kind:?}");
		kind.items_mut(rewrite);
		found.clear();
		kind.items_mut(|reference| found.push(reference.target()));
		assert_eq!(found, remapped, "{kind:?}");
	}
}

fn fixture() -> MIR {
	let mut signatures = Signatures::default();
	let signature = signatures.intern(&[], &[]);
	let mut body = Body::default();
	let pointer = body.push(
		ExprKind::StaticPointer {
			entry: StaticEntryId::new(0),
			offset: 0,
		},
		ValueType::I32,
	);
	let read = body.push(
		ExprKind::Global {
			id: GlobalId::new(0),
		},
		ValueType::I32,
	);
	let call = body.push(
		ExprKind::Call {
			function: FunctionId::new(1),
			args: ExprList::EMPTY,
		},
		ValueType::Unit,
	);
	let statements = body.push_list([pointer, read, call]);
	let root = body.push(ExprKind::Sequence { statements }, ValueType::Unit);
	let symbol = string_interner::symbol::SymbolU32::try_from_usize(0).unwrap();
	MIR {
		functions: vec![
			Function {
				signature,
				origin: Origin::Defined(Code {
					locals: vec![],
					label_count: 0,
					body,
					root,
				}),
			},
			Function {
				signature,
				origin: Origin::Imported(ImportIdx::new(0)),
			},
		],
		function_flags: vec![FunctionFlags::empty(); 2],
		signatures,
		globals: vec![
			Global {
				id: GlobalId::new(0),
				ty: ValueType::I32,
				mutability: Mutability::Immutable,
				origin: Origin::Defined(ConstInit::Static {
					entry: StaticEntryId::new(0),
					offset: 3,
				}),
			},
			Global {
				id: GlobalId::new(1),
				ty: ValueType::I32,
				mutability: Mutability::Immutable,
				origin: Origin::Defined(ConstInit::DataEnd {
					memory: MemoryId::new(0),
				}),
			},
			Global {
				id: GlobalId::new(2),
				ty: ValueType::I32,
				mutability: Mutability::Immutable,
				origin: Origin::Imported(ImportIdx::new(1)),
			},
			Global {
				id: GlobalId::new(3),
				ty: ValueType::I32,
				mutability: Mutability::Immutable,
				origin: Origin::Defined(ConstInit::Int(0)),
			},
		],
		exports: vec![
			Export {
				name: symbol,
				item: Item::Function(FunctionId::new(0)),
			},
			Export {
				name: symbol,
				item: Item::Global(GlobalId::new(0)),
			},
			Export {
				name: symbol,
				item: Item::Memory(MemoryId::new(0)),
			},
		],
		imports: vec![
			crate::mir::Import {
				module: symbol,
				name: symbol,
				item: Item::Function(FunctionId::new(1)),
			},
			crate::mir::Import {
				module: symbol,
				name: symbol,
				item: Item::Global(GlobalId::new(2)),
			},
		],
		memories: vec![MemoryInfo {
			id: MemoryId::new(0),
			kind: MemoryKind::Memory32,
			min_pages: None,
			max_pages: None,
			origin: Origin::Defined(()),
		}],
		static_entries: vec![
			StaticEntry {
				bytes: vec![0; 8].into(),
				align: 4,
				memory: MemoryId::new(0),
				relocations: vec![
					Relocation {
						offset: 0,
						target: AddressTarget::Entry(StaticEntryId::new(1)),
					},
					Relocation {
						offset: 4,
						target: AddressTarget::DataEnd(MemoryId::new(0)),
					},
				]
				.into(),
			},
			StaticEntry {
				bytes: vec![0; 4].into(),
				align: 4,
				memory: MemoryId::new(0),
				relocations: vec![Relocation {
					offset: 0,
					target: AddressTarget::Entry(StaticEntryId::new(0)),
				}]
				.into(),
			},
		],
		start_function: Some(FunctionId::new(0)),
	}
}

#[test]
fn roots_and_dependencies_follow_reference_based_storage_policy() {
	let mir = fixture();
	assert_eq!(mir.verify_imports(), Ok(()));
	let mut roots = Vec::new();
	mir.roots(|reference| roots.push(reference));
	assert_eq!(roots, [function(0), global(0), memory(0), function(0)]);
	assert_eq!(
		dependencies(&mir, function(0)),
		[data(0), global(0), function(1)]
	);
	assert!(dependencies(&mir, function(1)).is_empty());
	assert_eq!(dependencies(&mir, global(0)), [data(0)]);
	assert_eq!(dependencies(&mir, global(1)), [memory(0)]);
	assert!(dependencies(&mir, global(2)).is_empty());
	assert!(dependencies(&mir, global(3)).is_empty());
	assert_eq!(dependencies(&mir, data(0)), [memory(0), data(1), memory(0)]);
	assert_eq!(dependencies(&mir, data(1)), [memory(0), data(0)]);
	// Exported memory and DATA_END have no reverse edge to backing data.
	assert!(dependencies(&mir, memory(0)).is_empty());
}

#[test]
fn metadata_remapping_changes_ids_without_changing_payloads() {
	let mut mir = fixture();
	let entry = &mut mir.static_entries[0];
	entry.items_mut(rewrite);
	assert_eq!(entry.memory, MemoryId::new(10));
	assert!(
		matches!(entry.relocations[0].target, AddressTarget::Entry(id) if id == StaticEntryId::new(11))
	);
	assert!(
		matches!(entry.relocations[1].target, AddressTarget::DataEnd(id) if id == MemoryId::new(10))
	);
	assert_eq!(&*entry.bytes, &[0; 8]);
	assert_eq!(entry.align, 4);
	assert_eq!(entry.relocations[1].offset, 4);
	let init = mir.globals[0].origin.defined().copied().unwrap();
	let mut init = init;
	init.items_mut(rewrite);
	assert!(
		matches!(init, ConstInit::Static { entry, offset: 3 } if entry == StaticEntryId::new(10))
	);
	let mut end = ConstInit::DataEnd {
		memory: MemoryId::new(0),
	};
	end.items_mut(rewrite);
	assert!(
		matches!(end, ConstInit::DataEnd { memory } if memory == MemoryId::new(10))
	);
	for (mut item, expected) in [
		(Item::Function(FunctionId::new(0)), function(10)),
		(Item::Global(GlobalId::new(0)), global(10)),
		(Item::Memory(MemoryId::new(0)), memory(10)),
	] {
		item.items_mut(rewrite);
		assert_eq!(Reference::Item(item), expected);
	}
}
