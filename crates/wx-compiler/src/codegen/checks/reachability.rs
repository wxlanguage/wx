use super::*;
use mir::{
	AddressTarget, Body, Code, ConstInit, ExprKind, ExprList, FunctionId,
	GlobalId, Item, MemoryId, Origin, StaticEntryId, ValueType,
};

struct Program {
	mir: mir::MIR,
	strings: ast::StringInterner,
}

impl Program {
	fn new() -> Self {
		Self {
			mir: mir::MIR {
				functions: vec![],
				function_flags: vec![],
				signatures: mir::Signatures::default(),
				globals: vec![],
				exports: vec![],
				imports: vec![],
				memories: vec![],
				static_entries: vec![],
				start_function: None,
			},
			strings: ast::StringInterner::default(),
		}
	}

	fn function(&mut self, kind: ExprKind, ty: ValueType) -> FunctionId {
		let mut body = Body::default();
		let root = body.push(kind, ty);
		let signature = self.mir.signatures.intern(
			&[],
			if ty.is_scalar() {
				std::slice::from_ref(&ty)
			} else {
				&[]
			},
		);
		let id = FunctionId::new(self.mir.functions.len() as u32);
		self.mir.functions.push(mir::Function {
			signature,
			origin: Origin::Defined(Code {
				locals: vec![],
				label_count: 0,
				body,
				root,
			}),
		});
		self.mir.function_flags.push(mir::FunctionFlags::empty());
		id
	}

	fn global(&mut self, init: ConstInit) -> GlobalId {
		let id = GlobalId::new(self.mir.globals.len() as u32);
		self.mir.globals.push(mir::Global {
			id,
			ty: ValueType::I32,
			mutability: mir::Mutability::Mutable,
			origin: Origin::Defined(init),
		});
		id
	}

	fn memory(&mut self) -> MemoryId {
		let id = MemoryId::new(self.mir.memories.len() as u32);
		self.mir.memories.push(mir::MemoryInfo {
			id,
			kind: mir::MemoryKind::Memory32,
			min_pages: Some(1),
			max_pages: None,
			origin: Origin::Defined(()),
		});
		id
	}

	fn data(
		&mut self,
		memory: MemoryId,
		bytes: &[u8],
		align: u32,
		relocations: Vec<mir::Relocation>,
	) -> StaticEntryId {
		let id = StaticEntryId::new(self.mir.static_entries.len() as u32);
		self.mir.static_entries.push(mir::StaticEntry {
			memory,
			bytes: bytes.into(),
			align,
			relocations: relocations.into(),
		});
		id
	}

	fn export(&mut self, name: &str, item: Item) {
		self.mir.exports.push(mir::Export {
			name: self.strings.get_or_intern(name),
			item,
		});
	}

	fn import(&mut self, name: &str, item: Item) {
		let id = mir::ImportIdx::new(self.mir.imports.len() as u32);
		self.mir.imports.push(mir::Import {
			module: self.strings.get_or_intern("host"),
			name: self.strings.get_or_intern(name),
			item,
		});
		match item {
			Item::Function(id_) => {
				self.mir.functions[usize::from(id_)].origin =
					Origin::Imported(id)
			}
			Item::Global(id_) => {
				self.mir.globals[usize::from(id_)].origin = Origin::Imported(id)
			}
			Item::Memory(id_) => {
				self.mir.memories[usize::from(id_)].origin =
					Origin::Imported(id)
			}
		}
	}

	fn emit(&mut self) -> WasmModule {
		let reached = crate::opt::optimize_reachable(&mut self.mir);
		Builder::build(&self.mir, &self.strings, &reached).unwrap()
	}
}

#[test]
fn selective_output_maps_gaps_and_merges_only_retained_imports() {
	let mut p = Program::new();
	// Dead bodies deliberately contain invalid references: neither discovery,
	// codegen's verifier hooks nor linearization may inspect them.
	p.function(
		ExprKind::Call {
			function: FunctionId::new(999),
			args: ExprList::EMPTY,
		},
		ValueType::I32,
	);
	let helper = p.function(ExprKind::Int { value: 43 }, ValueType::I32);
	let run = p.function(
		ExprKind::Call {
			function: helper,
			args: ExprList::EMPTY,
		},
		ValueType::I32,
	);
	p.export("run", Item::Function(run));
	p.global(ConstInit::Int(999));
	let global = p.global(ConstInit::Int(29));
	p.export("global", Item::Global(global));
	p.memory();
	let memory = p.memory();
	p.export("memory", Item::Memory(memory));

	// Definitions precede imports in MIR. First matching import is dead;
	// the next two are reached and must share one Wasm index in each space.
	for (suffix, reached) in [("dead", false), ("a", true), ("b", true)] {
		let f = p.function(ExprKind::Int { value: 0 }, ValueType::I32);
		let g = p.global(ConstInit::Int(0));
		let m = p.memory();
		for (name, item) in [
			("f", Item::Function(f)),
			("g", Item::Global(g)),
			("m", Item::Memory(m)),
		] {
			p.import(name, item);
			if reached {
				p.export(&format!("{name}_{suffix}"), item);
			}
		}
	}
	let unused_import = p.function(ExprKind::Noop, ValueType::Unit);
	p.mir.functions[usize::from(unused_import)].signature =
		p.mir.signatures.intern(&[ValueType::F64], &[]);
	p.import("unused", Item::Function(unused_import));
	let read_global =
		p.function(ExprKind::Global { id: global }, ValueType::I32);
	let read_memory_index =
		p.function(ExprKind::MemoryIndex { memory }, ValueType::I32);
	p.export("read_global", Item::Function(read_global));
	p.export("memory_index", Item::Function(read_memory_index));
	let module = p.emit();
	assert_eq!(module.imports.imports.len(), 3);
	assert_eq!(
		module.types.signatures.len(),
		1,
		"dead import signatures are not registered"
	);
	assert_eq!(module.functions.types.len(), 4);
	assert_eq!(module.code.functions.len(), 4);
	assert_eq!(module.globals.globals.len(), 1);
	assert_eq!(module.memory.memories.len(), 1);
	for export in &module.exports.items {
		match export {
			ExportItem::Function { name, func_index }
				if name.starts_with("f_") =>
			{
				assert_eq!(func_index.0, 0)
			}
			ExportItem::Global { name, global_index } => {
				assert_eq!(global_index.0, u32::from(name == "global"))
			}
			ExportItem::Memory { name, memory_index } => {
				assert_eq!(*memory_index, u32::from(name == "memory"))
			}
			_ => {}
		}
	}
	assert_eq!(p.mir.functions.len(), 9);
	assert_eq!(p.mir.globals.len(), 5);
	assert_eq!(p.mir.memories.len(), 5);
	assert_eq!(p.mir.imports.len(), 10);

	let engine = wasmtime::Engine::default();
	let module = wasmtime::Module::new(&engine, module.encode()).unwrap();
	let mut store = wasmtime::Store::new(&engine, ());
	let f = wasmtime::Func::wrap(&mut store, || 17i32);
	let g = wasmtime::Global::new(
		&mut store,
		wasmtime::GlobalType::new(
			wasmtime::ValType::I32,
			wasmtime::Mutability::Var,
		),
		wasmtime::Val::I32(11),
	)
	.unwrap();
	let m =
		wasmtime::Memory::new(&mut store, wasmtime::MemoryType::new(1, None))
			.unwrap();
	let instance = wasmtime::Instance::new(
		&mut store,
		&module,
		&[f.into(), g.into(), m.into()],
	)
	.unwrap();
	for (name, expected) in [
		("run", 43),
		("read_global", 29),
		("memory_index", 1),
		("f_a", 17),
		("f_b", 17),
	] {
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, name)
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			expected
		);
	}
}

#[test]
fn selected_data_layout_patches_relocations_and_data_end_without_dead_bytes() {
	let mut p = Program::new();
	p.memory();
	let memory = p.memory();
	p.data(memory, &[255; 64], 16, vec![]); // dead, even in retained memory
	let target = p.data(memory, &[7, 8, 9, 10], 4, vec![]);
	p.data(memory, &[255; 64], 16, vec![]);
	let pointer = p.data(
		memory,
		&[1, 0, 0, 0, 0, 0, 0, 0],
		8,
		vec![
			mir::Relocation {
				offset: 0,
				target: AddressTarget::Entry(target),
			},
			mir::Relocation {
				offset: 4,
				target: AddressTarget::DataEnd(memory),
			},
		],
	);
	p.global(ConstInit::Int(999));
	let address = p.global(ConstInit::Static {
		entry: pointer,
		offset: 4,
	});
	let end = p.global(ConstInit::DataEnd { memory });
	p.export("address", Item::Global(address));
	p.export("end", Item::Global(end));
	p.export("memory", Item::Memory(memory));
	let read_pointer = p.function(
		ExprKind::StaticPointer {
			entry: target,
			offset: 2,
		},
		ValueType::I32,
	);
	p.export("read_pointer", Item::Function(read_pointer));
	let read_end = p.function(ExprKind::DataEnd { memory }, ValueType::I32);
	p.export("read_end", Item::Function(read_end));
	let module = p.emit();
	assert_eq!(module.data.segments.len(), 1);
	let segment = &module.data.segments[0];
	assert_eq!(segment.memory_index, 0);
	assert_eq!(&*segment.bytes, &[9, 0, 0, 0, 16, 0, 0, 0, 7, 8, 9, 10]);
	assert_eq!(p.mir.static_entries.len(), 4);
	assert!(
		p.mir.static_entries[3].relocations[0].target
			== AddressTarget::Entry(target)
	);

	let engine = wasmtime::Engine::default();
	let module = wasmtime::Module::new(&engine, module.encode()).unwrap();
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	for (name, expected) in [("address", 4), ("end", 16)] {
		assert_eq!(
			instance
				.get_global(&mut store, name)
				.unwrap()
				.get(&mut store)
				.i32(),
			Some(expected)
		);
	}
	assert_eq!(
		instance
			.get_typed_func::<(), i32>(&mut store, "read_end")
			.unwrap()
			.call(&mut store, ())
			.unwrap(),
		16
	);
	assert_eq!(
		instance
			.get_typed_func::<(), i32>(&mut store, "read_pointer")
			.unwrap()
			.call(&mut store, ())
			.unwrap(),
		10
	);
}

#[test]
fn exported_memory_and_data_end_do_not_root_backing_data() {
	let mut p = Program::new();
	let memory = p.memory();
	p.data(memory, &[99; 100], 4, vec![]);
	p.export("memory", Item::Memory(memory));
	let end = p.global(ConstInit::DataEnd { memory });
	p.export("end", Item::Global(end));
	let module = p.emit();
	assert!(module.data.segments.is_empty());
	assert!(matches!(
		module.globals.globals[0].value,
		wasm::Instruction::I32Const(0)
	));
	wasmtime::Module::new(&wasmtime::Engine::default(), module.encode())
		.unwrap();
}

#[test]
fn start_only_output_uses_retained_indices_and_preserves_initialization() {
	let mut p = Program::new();
	p.function(ExprKind::Noop, ValueType::Unit);
	p.global(ConstInit::Int(999));
	let global = p.global(ConstInit::Int(0));
	let start = p.function(ExprKind::Noop, ValueType::Unit);
	let code = p.mir.functions[usize::from(start)].code_mut().unwrap();
	let value = code.body.push(ExprKind::Int { value: 42 }, ValueType::I32);
	code.root = code
		.body
		.push(ExprKind::GlobalSet { id: global, value }, ValueType::Unit);
	p.mir.start_function = Some(start);
	let mut module = p.emit();
	assert!(module.exports.items.is_empty());
	assert_eq!(module.start.as_ref().unwrap().func_index, 0);
	assert_eq!(module.code.functions.len(), 1);
	assert_eq!(module.globals.globals.len(), 1);
	// Expose a probe only after discovery and output selection. The MIR has
	// no exports: the start root alone must have retained this global.
	module.exports.items = Box::new([ExportItem::Global {
		name: "probe".into(),
		global_index: GlobalIndex(0),
	}]);
	let engine = wasmtime::Engine::default();
	let module = wasmtime::Module::new(&engine, module.encode()).unwrap();
	let mut store = wasmtime::Store::new(&engine, ());
	let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	assert_eq!(
		instance
			.get_global(&mut store, "probe")
			.unwrap()
			.get(&mut store)
			.i32(),
		Some(42)
	);
}

#[test]
fn no_roots_emit_no_imports_bodies_or_data() {
	let mut p = Program::new();
	let f = p.function(ExprKind::Noop, ValueType::Unit);
	p.import("unused", Item::Function(f));
	let memory = p.memory();
	p.data(memory, &[99; 100], 4, vec![]);
	p.global(ConstInit::Int(42));
	let module = p.emit();
	assert!(module.imports.imports.is_empty());
	assert!(module.types.signatures.is_empty());
	assert!(module.functions.types.is_empty());
	assert!(module.code.functions.is_empty());
	assert!(module.memory.memories.is_empty());
	assert!(module.globals.globals.is_empty());
	assert!(module.data.segments.is_empty());
	wasmtime::Module::new(&wasmtime::Engine::default(), module.encode())
		.unwrap();
}
