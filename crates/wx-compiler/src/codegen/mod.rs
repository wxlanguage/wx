use std::collections::HashMap;

use string_interner::symbol::SymbolU32;

use leb128fmt;

use crate::wasm::{self, ScalarType};

#[cfg(test)]
mod checks;
mod linearize;
use crate::mir::references::Reference;
use crate::opt::Reachability;
use crate::{ast, mir};
pub use linearize::uses_br_table;

#[derive(Debug, Clone, Copy, serde::Serialize)]
pub struct FuncIndex(pub u32);

#[derive(Debug, Clone, Copy, serde::Serialize)]
pub struct GlobalIndex(pub u32);

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct FunctionSignature {
	pub param_count: usize,
	pub param_results: Box<[ScalarType]>,
}

impl FunctionSignature {
	pub fn params(&self) -> &[ScalarType] {
		self.param_results.get(..self.param_count).unwrap_or(&[])
	}

	pub fn results(&self) -> &[ScalarType] {
		self.param_results.get(self.param_count..).unwrap_or(&[])
	}
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct TypeSection {
	signatures: Box<[FunctionSignature]>,
}

#[derive(
	Debug,
	Clone,
	Copy,
	PartialEq,
	PartialOrd,
	Eq,
	Ord,
	Hash,
	serde::Serialize
)]
pub struct SignatureIndex(pub u32);

#[derive(Debug, Clone, Copy, serde::Serialize)]
pub struct TableIndex(pub u32);

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct FunctionSection {
	types: Box<[SignatureIndex]>,
}

#[derive(Debug, Clone, serde::Serialize)]
pub enum ExportItem {
	Function {
		name: String,
		func_index: FuncIndex,
	},
	Global {
		name: String,
		global_index: GlobalIndex,
	},
	// Table,
	Memory {
		name: String,
		memory_index: u32,
	},
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ExportSection {
	items: Box<[ExportItem]>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct FunctionBody {
	locals: Box<[wasm::Local]>,
	expressions: Box<[u8]>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct CodeSection {
	functions: Box<[FunctionBody]>,
}

#[derive(Debug, Clone, Copy, serde::Serialize)]
pub enum RefType {
	FuncRef,
	ExternRef,
}

#[derive(Debug, Clone, serde::Serialize)]
pub enum ResizableLimits {
	Initial(u32),
	InitialAndMax { initial: u32, maximum: u32 },
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct TableType {
	ty: RefType,
	limits: ResizableLimits,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct TableSection {
	tables: Box<[TableType]>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ElementSegment {
	table_index: TableIndex,
	offset: u32,
	indices: Box<[FuncIndex]>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ElementSection {
	segments: Box<[ElementSegment]>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct GlobalSection {
	globals: Box<[Global]>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Mutability {
	Immutable,
	Mutable,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
struct Global {
	ty: ScalarType,
	mutability: Mutability,
	/// Only the four `*Const` variants of `wasm::Instruction` are valid WASM
	/// global init expressions; anything else is a construction bug upstream.
	value: wasm::Instruction,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub enum ImportDesc {
	Function {
		signature_index: SignatureIndex,
	},
	Global {
		ty: ScalarType,
		mutability: Mutability,
	},
	Memory {
		memory: Memory,
	},
}

#[derive(Clone)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct Import {
	pub module: String,
	pub name: String,
	pub desc: ImportDesc,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct ImportSection {
	imports: Box<[Import]>,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
struct StartSection {
	func_index: u32,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct WasmModule {
	types: TypeSection,
	imports: ImportSection,
	functions: FunctionSection,
	tables: TableSection,
	memory: MemorySection,
	globals: GlobalSection,
	exports: ExportSection,
	start: Option<StartSection>,
	elements: ElementSection,
	code: CodeSection,
	data: DataSection,
}

struct MemoryEntry {
	wasm_index: u32,
	kind: mir::MemoryKind,
}

/// The static data codegen lays out: each memory's segment bytes, each live
/// entry's address in its memory, and where each memory's data ends.
struct StaticLayout {
	segments: HashMap<mir::MemoryId, Vec<u8>>,
	addresses: HashMap<mir::StaticEntryId, u32>,
}

/// How `Memory::DATA_END` is aligned: past the static data, at an address
/// any value's alignment divides, so an allocator can start there.
const DATA_END_ALIGN: u32 = 16;

impl StaticLayout {
	/// The address right after `memory`'s static data (`Memory::DATA_END`).
	fn data_end(&self, memory: mir::MemoryId) -> u32 {
		let size = self.segments.get(&memory).map_or(0, Vec::len);
		u32::try_from(size)
			.unwrap()
			.next_multiple_of(DATA_END_ALIGN)
	}

	fn address(&self, target: mir::AddressTarget) -> u32 {
		match target {
			mir::AddressTarget::Entry(entry) => self.addresses[&entry],
			mir::AddressTarget::DataEnd(memory) => self.data_end(memory),
		}
	}
}

/// The memory an address into `target` belongs to.
fn target_memory(mir: &mir::MIR, target: mir::AddressTarget) -> mir::MemoryId {
	match target {
		mir::AddressTarget::Entry(entry) => {
			mir.static_entries[usize::from(entry)].memory
		}
		mir::AddressTarget::DataEnd(memory) => memory,
	}
}

/// Place selected entries by decreasing alignment, then ID for deterministic
/// output. Patch relocations only after every selected address is known.
fn lay_out_static_data(
	mir: &mir::MIR,
	mut order: Vec<mir::StaticEntryId>,
) -> StaticLayout {
	order.sort_by_key(|&entry| {
		(
			std::cmp::Reverse(mir.static_entries[usize::from(entry)].align),
			usize::from(entry),
		)
	});

	let mut layout = StaticLayout {
		segments: HashMap::new(),
		addresses: HashMap::new(),
	};
	for &entry in &order {
		let data = &mir.static_entries[usize::from(entry)];
		let bytes = layout.segments.entry(data.memory).or_default();
		bytes.resize(bytes.len().next_multiple_of(data.align as usize), 0);
		layout
			.addresses
			.insert(entry, u32::try_from(bytes.len()).unwrap());
		bytes.extend_from_slice(&data.bytes);
	}
	let mut patches = Vec::new();
	for &entry in &order {
		let data = &mir.static_entries[usize::from(entry)];
		let base = layout.addresses[&entry] as usize;
		for relocation in &data.relocations {
			let memory = target_memory(mir, relocation.target);
			let width = mir.memory(memory).kind.pointer_size() as usize;
			patches.push((
				data.memory,
				base + relocation.offset as usize,
				width,
				layout.address(relocation.target),
			));
		}
	}
	for (memory, at, width, address) in patches {
		let bytes = layout.segments.get_mut(&memory).unwrap();
		let at = &mut bytes[at..][..width];
		let mut number = [0; 8];
		number[..width].copy_from_slice(at);
		let patched = u64::from_le_bytes(number) + u64::from(address);
		at.copy_from_slice(&patched.to_le_bytes()[..width]);
	}
	layout
}

pub struct Builder {
	table: Vec<FuncIndex>,
	/// The address of each live static entry in its memory.
	statics: StaticLayout,
	/// Maps each retained function DefId (imported or defined) to its wasm function
	/// index. Imported functions occupy indices 0..import_func_count;
	/// defined functions follow.
	func_wasm_index: HashMap<mir::FunctionId, u32>,
	/// Maps each retained global DefId (imported or defined) to its wasm global index.
	/// Imported globals occupy indices 0..import_global_count; defined globals
	/// follow.
	global_wasm_index: HashMap<mir::GlobalId, u32>,
	/// Maps each retained memory DefId (imported or defined) to its wasm index and kind.
	/// Imported memories occupy indices 0..import_memory_count; defined follow.
	memories: HashMap<mir::MemoryId, MemoryEntry>,
	/// Deduplicated function-type entries for the wasm type section.
	/// Shared between function signatures and multi-value block types.
	signatures: HashMap<FunctionSignature, SignatureIndex>,
}

impl Builder {
	/// The module's type index for MIR's signature `signature`, given
	/// on first use: only the types the module's functions and blocks use
	/// are written.
	fn register_signature(
		&mut self,
		signatures: &mir::Signatures,
		signature: mir::SignatureIndex,
	) -> SignatureIndex {
		let scalar = |&ty| ScalarType::try_from(ty).expect("a scalar");
		let params = signatures.params(signature);
		let param_count = params.len();
		let param_results: Vec<ScalarType> = params
			.iter()
			.chain(signatures.results(signature))
			.map(scalar)
			.collect();
		let signature = FunctionSignature {
			param_count,
			param_results: param_results.into_boxed_slice(),
		};
		let next = SignatureIndex(self.signatures.len() as u32);
		*self.signatures.entry(signature).or_insert(next)
	}

	/// Emit optimized MIR using current reachability marks, keeping MIR IDs intact.
	pub fn build(
		mir: &mir::MIR,
		interner: &ast::StringInterner,
		reached: &Reachability,
	) -> Result<WasmModule, ()> {
		Self::build_with(mir, interner, reached, |mir, id| {
			linearize::linearize(mir, mir.code(id))
		})
	}

	/// Direct original-MIR reference for execution checks, without optimization.
	#[cfg(test)]
	pub(crate) fn build_linearized(
		mir: &mir::MIR,
		interner: &ast::StringInterner,
	) -> Result<WasmModule, ()> {
		let reached = Reachability::collect_for_tests(mir);
		Self::build(mir, interner, &reached)
	}

	fn build_with(
		mir: &mir::MIR,
		interner: &ast::StringInterner,
		reached: &Reachability,
		schedule: fn(&mir::MIR, mir::FunctionId) -> wasm::Function,
	) -> Result<WasmModule, ()> {
		let retains = |item| reached.is_reachable(Reference::Item(item));
		let data = (0..mir.static_entries.len())
			.map(|index| mir::StaticEntryId::new(index as u32))
			.filter(|&id| reached.is_reachable(Reference::Data(id)))
			.collect();
		let statics = lay_out_static_data(mir, data);

		let mut builder = Builder {
			table: Vec::new(),
			statics,
			func_wasm_index: HashMap::new(),
			global_wasm_index: HashMap::new(),
			memories: HashMap::new(),
			signatures: HashMap::new(),
		};

		// Every index space numbers its imports first. One pass over the
		// import table gives each entry the next index of its kind, or the
		// index of an earlier entry with the same names and external type:
		// the host provides both from the same names, so they are one import
		// to it. Defined items follow, in id order.
		let mut imports = Vec::<Import>::new();
		let mut merged: HashMap<(SymbolU32, SymbolU32, ImportDesc), u32> =
			HashMap::new();
		let mut next_func_idx: u32 = 0;
		let mut next_global_idx: u32 = 0;
		let mut next_memory_idx: u32 = 0;
		for import in &mir.imports {
			if !retains(import.item) {
				continue;
			}
			let desc = match import.item {
				mir::Item::Function(id) => ImportDesc::Function {
					signature_index: builder.register_signature(
						&mir.signatures,
						mir.function(id).signature,
					),
				},
				mir::Item::Global(id) => {
					let global = mir.global(id);
					ImportDesc::Global {
						ty: ScalarType::try_from(global.ty).unwrap(),
						mutability: match global.mutability {
							mir::Mutability::Mutable => Mutability::Mutable,
							mir::Mutability::Immutable => Mutability::Immutable,
						},
					}
				}
				mir::Item::Memory(id) => ImportDesc::Memory {
					memory: memory_type(mir.memory(id), 0),
				},
			};
			let next = match import.item {
				mir::Item::Function(_) => &mut next_func_idx,
				mir::Item::Global(_) => &mut next_global_idx,
				mir::Item::Memory(_) => &mut next_memory_idx,
			};
			let index = *merged
				.entry((import.module, import.name, desc.clone()))
				.or_insert_with(|| {
					imports.push(Import {
						module: interner.resolve(import.module).unwrap().into(),
						name: interner.resolve(import.name).unwrap().into(),
						desc,
					});
					*next += 1;
					*next - 1
				});
			match import.item {
				mir::Item::Function(id) => {
					builder.func_wasm_index.insert(id, index);
				}
				mir::Item::Global(id) => {
					builder.global_wasm_index.insert(id, index);
				}
				mir::Item::Memory(id) => {
					builder.memories.insert(
						id,
						MemoryEntry {
							wasm_index: index,
							kind: mir.memory(id).kind,
						},
					);
				}
			}
		}
		let import_function_count = next_func_idx;
		for (id, function) in mir.functions_with_ids() {
			if retains(mir::Item::Function(id)) && function.code().is_some() {
				builder.func_wasm_index.insert(id, next_func_idx);
				next_func_idx += 1;
			}
		}
		for global in &mir.globals {
			if retains(mir::Item::Global(global.id))
				&& global.origin.defined().is_some()
			{
				builder.global_wasm_index.insert(global.id, next_global_idx);
				next_global_idx += 1;
			}
		}
		for memory in &mir.memories {
			if retains(mir::Item::Memory(memory.id))
				&& memory.origin.defined().is_some()
			{
				builder.memories.insert(
					memory.id,
					MemoryEntry {
						wasm_index: next_memory_idx,
						kind: memory.kind,
					},
				);
				next_memory_idx += 1;
			}
		}

		let defined_function_count =
			(next_func_idx - import_function_count) as usize;
		let mut function_signatures =
			Vec::<SignatureIndex>::with_capacity(defined_function_count);
		let exports: Box<_> = mir
			.exports
			.iter()
			.map(|export| {
				let name = interner.resolve(export.name).unwrap().to_string();
				match export.item {
					mir::Item::Global(id) => ExportItem::Global {
						name,
						global_index: GlobalIndex(
							builder.global_wasm_index[&id],
						),
					},
					mir::Item::Function(id) => ExportItem::Function {
						name,
						func_index: FuncIndex(builder.func_wasm_index[&id]),
					},
					mir::Item::Memory(id) => ExportItem::Memory {
						name,
						memory_index: builder.memories[&id].wasm_index,
					},
				}
			})
			.collect();

		let mut functions =
			Vec::<FunctionBody>::with_capacity(defined_function_count);
		for (id, func) in mir.functions_with_ids() {
			if !retains(mir::Item::Function(id)) || func.code().is_none() {
				continue;
			}
			let signature_index =
				builder.register_signature(&mir.signatures, func.signature);
			function_signatures.push(signature_index);

			let scheduled = schedule(mir, id);
			let body = builder.encode_scheduled(&scheduled, mir);

			functions.push(body);
		}

		let globals = GlobalSection {
			globals: mir
				.globals
				.iter()
				.filter(|global| retains(mir::Item::Global(global.id)))
				.filter_map(|global| {
					let &const_init = global.origin.defined()?;
					if let mir::ConstInit::DataEnd { memory } = const_init {
						assert!(
							builder.memories.contains_key(&memory),
							"DATA_END requires a retained memory"
						);
					}
					let init_value = match (
						const_init,
						ScalarType::try_from(global.ty).unwrap(),
					) {
						(mir::ConstInit::Int(v), ScalarType::I32) => {
							wasm::Instruction::I32Const(v as i32)
						}
						(mir::ConstInit::Int(v), ScalarType::I64) => {
							wasm::Instruction::I64Const(v)
						}
						(mir::ConstInit::Float(v), ScalarType::F32) => {
							wasm::Instruction::F32Const(v as f32)
						}
						(mir::ConstInit::Float(v), ScalarType::F64) => {
							wasm::Instruction::F64Const(v)
						}
						(
							mir::ConstInit::Static { entry, offset },
							ScalarType::I32,
						) => wasm::Instruction::I32Const(
							(builder.statics.addresses[&entry] + offset) as i32,
						),
						(
							mir::ConstInit::Static { entry, offset },
							ScalarType::I64,
						) => wasm::Instruction::I64Const(i64::from(
							builder.statics.addresses[&entry] + offset,
						)),
						(
							mir::ConstInit::DataEnd { memory },
							ScalarType::I32,
						) => wasm::Instruction::I32Const(
							builder.statics.data_end(memory) as i32,
						),
						(
							mir::ConstInit::DataEnd { memory },
							ScalarType::I64,
						) => wasm::Instruction::I64Const(i64::from(
							builder.statics.data_end(memory),
						)),
						_ => unreachable!(),
					};
					Some(Global {
						ty: ScalarType::try_from(global.ty).unwrap(),
						mutability: match global.mutability {
							mir::Mutability::Mutable => Mutability::Mutable,
							mir::Mutability::Immutable => Mutability::Immutable,
						},
						value: init_value,
					})
				})
				.collect::<Box<_>>(),
		};

		let start = mir.start_function.map(|id| StartSection {
			func_index: builder.func_wasm_index[&id],
		});

		// A defined memory must be large enough for its own static data; an
		// imported memory's size is the host's business.
		let memories = mir
			.memories
			.iter()
			.filter(|info| {
				retains(mir::Item::Memory(info.id))
					&& info.origin.defined().is_some()
			})
			.map(|info| {
				memory_type(
					info,
					builder.statics.data_end(info.id).div_ceil(65536),
				)
			})
			.collect();

		Ok(WasmModule {
			types: TypeSection {
				signatures: {
					let mut sorted_types: Vec<_> =
						builder.signatures.drain().collect();
					sorted_types.sort_by_key(|&(_, index)| index);
					sorted_types
						.into_iter()
						.map(|(ty, _)| ty)
						.collect::<Box<_>>()
				},
			},
			imports: ImportSection {
				imports: imports.into_boxed_slice(),
			},
			data: DataSection {
				segments: {
					let mut segments: Vec<DataSegment> =
						std::mem::take(&mut builder.statics.segments)
							.into_iter()
							.filter(|(_, bytes)| !bytes.is_empty())
							.map(|(id, bytes)| DataSegment {
								memory_index: builder.memories[&id].wasm_index,
								offset: 0,
								memory_kind: builder.memories[&id].kind,
								bytes: bytes.into_boxed_slice(),
							})
							.collect();
					segments.sort_by_key(|s| s.memory_index);
					segments.into_boxed_slice()
				},
			},
			memory: MemorySection { memories },
			globals,
			tables: TableSection {
				tables: match builder.table.len() {
					0 => Box::new([]),
					_ => Box::new([TableType {
						ty: RefType::FuncRef,
						limits: ResizableLimits::Initial(
							builder.table.len() as u32
						),
					}]),
				},
			},
			elements: ElementSection {
				segments: match builder.table.len() {
					0 => Box::new([]),
					_ => Box::new([ElementSegment {
						table_index: TableIndex(0),
						offset: 0,
						indices: builder.table.into_boxed_slice(),
					}]),
				},
			},
			functions: FunctionSection {
				types: function_signatures.into_boxed_slice(),
			},
			exports: ExportSection { items: exports },
			start,
			code: CodeSection {
				functions: functions.into_boxed_slice(),
			},
		})
	}

	/// Encode a [`wasm::Function`] into a [`FunctionBody`].
	///
	/// All index resolution (function WASM indices, global WASM indices, string
	/// byte offsets, data section end) is performed here using the maps and
	/// pools already built on `self`.
	fn encode_scheduled(
		&mut self,
		scheduled: &wasm::Function,
		mir: &mir::MIR,
	) -> FunctionBody {
		let locals: Box<[wasm::Local]> =
			scheduled.locals.iter().copied().collect();

		let mut sink = Vec::new();
		for instr in scheduled.body.iter().copied() {
			self.encode_scheduled_instr(
				instr,
				mir,
				&scheduled.br_table_depths,
				&mut sink,
			);
		}

		FunctionBody {
			locals,
			expressions: sink.into_boxed_slice(),
		}
	}

	fn encode_scheduled_instr(
		&mut self,
		instr: wasm::Instruction,
		mir: &mir::MIR,
		br_table_depths: &[u32],
		sink: &mut Vec<u8>,
	) {
		use wasm::Instruction as SI;
		match instr {
			SI::I32Const(v) => {
				sink.push(Opcode::I32Const as u8);
				v.encode(sink);
			}
			SI::I64Const(v) => {
				sink.push(Opcode::I64Const as u8);
				v.encode(sink);
			}
			SI::F32Const(v) => {
				sink.push(Opcode::F32Const as u8);
				v.encode(sink);
			}
			SI::F64Const(v) => {
				sink.push(Opcode::F64Const as u8);
				v.encode(sink);
			}
			SI::LocalGet(i) => {
				sink.push(Opcode::LocalGet as u8);
				i.encode(sink);
			}
			SI::LocalSet(i) => {
				sink.push(Opcode::LocalSet as u8);
				i.encode(sink);
			}
			SI::LocalTee(i) => {
				sink.push(Opcode::LocalTee as u8);
				i.encode(sink);
			}
			SI::GlobalGet(id) => {
				let wasm_idx = self.global_wasm_index[&id];
				sink.push(Opcode::GlobalGet as u8);
				wasm_idx.encode(sink);
			}
			SI::GlobalSet(id) => {
				let wasm_idx = self.global_wasm_index[&id];
				sink.push(Opcode::GlobalSet as u8);
				wasm_idx.encode(sink);
			}
			SI::Unary(op, ty) => sink.push(unary_opcode(op, ty) as u8),
			SI::Binary(op, ty) => sink.push(binary_opcode(op, ty) as u8),
			SI::Compare(op, ty) => sink.push(compare_opcode(op, ty) as u8),
			SI::Convert { op, from, to } => {
				sink.push(convert_opcode(op, from, to) as u8)
			}
			SI::Load(access, m) => encode_memory_access(
				load_opcode(access),
				m.align,
				m.offset,
				self.memories[&m.memory].wasm_index,
				sink,
			),
			SI::Store(access, m) => encode_memory_access(
				store_opcode(access),
				m.align,
				m.offset,
				self.memories[&m.memory].wasm_index,
				sink,
			),
			SI::Block { ty } => {
				sink.push(Opcode::Block as u8);
				self.encode_block_type(ty, mir, sink);
			}
			SI::Loop { ty } => {
				sink.push(Opcode::Loop as u8);
				self.encode_block_type(ty, mir, sink);
			}
			SI::If { ty } => {
				sink.push(Opcode::If as u8);
				self.encode_block_type(ty, mir, sink);
			}
			SI::Else => sink.push(Opcode::Else as u8),
			SI::End => sink.push(Opcode::End as u8),
			SI::Br(depth) => {
				sink.push(Opcode::Br as u8);
				depth.encode(sink);
			}
			SI::BrIf(depth) => {
				sink.push(Opcode::BrIf as u8);
				depth.encode(sink);
			}
			SI::BrTable { start, len } => {
				sink.push(Opcode::BrTable as u8);
				// WASM's `br_table` encodes as `vec(labelidx) labelidx` — a
				// table of length `depths.len() - 1` followed by the
				// default depth as a separate trailing immediate. The
				// scheduler folds both into one `[start, start+len)` range
				// into `br_table_depths` (its trailing element *is* the
				// default) since both stages need the same split.
				let depths =
					&br_table_depths[start as usize..(start + len) as usize];
				let (default_depth, table) =
					depths.split_last().expect("BrTable is never empty");
				(table.len() as u32).encode(sink);
				for depth in table {
					depth.encode(sink);
				}
				default_depth.encode(sink);
			}
			SI::Return => sink.push(Opcode::Return as u8),
			SI::Unreachable => sink.push(Opcode::Unreachable as u8),
			SI::Drop => sink.push(Opcode::Drop as u8),
			SI::Call(id) => {
				let wasm_idx = self.func_wasm_index[&id];
				sink.push(Opcode::Call as u8);
				wasm_idx.encode(sink);
			}
			SI::CallIndirectSym { mir_sig_index } => {
				let type_index =
					self.register_signature(&mir.signatures, mir_sig_index);
				sink.push(Opcode::CallIndirect as u8);
				type_index.0.encode(sink);
				0u32.encode(sink); // table index 0 (single function table)
			}
			SI::MemorySize(id) => {
				let mi = self.memories[&id].wasm_index;
				sink.push(Opcode::MemorySize as u8);
				mi.encode(sink);
			}
			SI::MemoryGrow(id) => {
				let mi = self.memories[&id].wasm_index;
				sink.push(Opcode::MemoryGrow as u8);
				mi.encode(sink);
			}
			SI::MemoryFill(id) => {
				let mi = self.memories[&id].wasm_index;
				sink.push(Opcode::BulkMemoryPrefix as u8);
				0x0Bu32.encode(sink); // memory.fill secondary opcode
				mi.encode(sink);
			}
			SI::MemoryCopy { dst, src } => {
				let dst_mi = self.memories[&dst].wasm_index;
				let src_mi = self.memories[&src].wasm_index;
				sink.push(Opcode::BulkMemoryPrefix as u8);
				0x0Au32.encode(sink); // memory.copy secondary opcode
				dst_mi.encode(sink);
				src_mi.encode(sink);
			}
			SI::MemoryIndex { memory } => {
				let mi = self.memories[&memory].wasm_index as i32;
				sink.push(Opcode::I32Const as u8);
				mi.encode(sink);
			}
			SI::Nop => sink.push(Opcode::Nop as u8),
			SI::FunctionPointer(id) => {
				let wasm_idx = self.func_wasm_index[&id];
				let table_idx = self.table.len() as i32;
				self.table.push(FuncIndex(wasm_idx));
				sink.push(Opcode::I32Const as u8);
				table_idx.encode(sink);
			}
			SI::StaticDataPointer { entry, offset, ty } => {
				let offset = self.statics.addresses[&entry] + offset;
				match ty {
					ScalarType::I64 => {
						sink.push(Opcode::I64Const as u8);
						(offset as i64).encode(sink);
					}
					_ => {
						sink.push(Opcode::I32Const as u8);
						(offset as i32).encode(sink);
					}
				}
			}
			SI::DataEnd { memory } => {
				let entry = &self.memories[&memory];
				match entry.kind {
					mir::MemoryKind::Memory32 => {
						sink.push(Opcode::I32Const as u8);
						(self.statics.data_end(memory) as i32).encode(sink);
					}
					mir::MemoryKind::Memory64 => {
						sink.push(Opcode::I64Const as u8);
						(i64::from(self.statics.data_end(memory))).encode(sink);
					}
				}
			}
		}
	}

	fn encode_block_type(
		&mut self,
		ty: wasm::BlockType,
		mir: &mir::MIR,
		sink: &mut Vec<u8>,
	) {
		match ty {
			wasm::BlockType::Empty => sink.push(0x40),
			wasm::BlockType::Value(vt) => vt.encode(sink),
			// A type index, as a positive `s33`.
			wasm::BlockType::Results(signature) => {
				let index = self.register_signature(&mir.signatures, signature);
				i64::from(index.0).encode(sink);
			}
		}
	}
}

#[allow(unused)]
#[repr(u8)]
enum SectionId {
	Custom = 0,
	Type = 1,
	Import = 2,
	Function = 3,
	Table = 4,
	Memory = 5,
	Global = 6,
	Export = 7,
	Start = 8,
	Element = 9,
	Code = 10,
	Data = 11,
}

#[allow(unused)]
#[derive(Clone, Copy)]
#[repr(u8)]
enum Opcode {
	Unreachable = 0x00,
	Nop = 0x01,
	Block = 0x02,
	Loop = 0x03,
	If = 0x04,
	Else = 0x05,
	// Try = 0x06,
	// Catch = 0x07,
	// Throw = 0x08,
	// Rethrow = 0x09,
	// ThrowRef = 0x0A,
	End = 0x0B,
	Br = 0x0C,
	BrIf = 0x0D,
	BrTable = 0x0E,
	Return = 0x0F,
	Call = 0x10,
	CallIndirect = 0x11,
	// ReturnCall = 0x12,
	// ReturnCallIndirect = 0x13,
	// CallRef = 0x14,
	// ReturnCallRef = 0x15,
	// 0x16 (reserved)
	// 0x17 (reserved)
	// Delegate = 0x18,
	// CatchAll = 0x19,
	Drop = 0x1A,
	Select = 0x1B,
	// SelectT = 0x1C,
	// 0x1D (reserved)
	// 0x1E (reserved)
	// TryTable = 0x1F,
	LocalGet = 0x20,
	LocalSet = 0x21,
	LocalTee = 0x22,
	GlobalGet = 0x23,
	GlobalSet = 0x24,
	// TableGet = 0x25,
	// TableSet = 0x26,
	// 0x27 (reserved)
	// - Load instructions
	I32Load = 0x28,
	I64Load = 0x29,
	F32Load = 0x2A,
	F64Load = 0x2B,
	I32Load8S = 0x2C,
	I32Load8U = 0x2D,
	I32Load16S = 0x2E,
	I32Load16U = 0x2F,
	I64Load8S = 0x30,
	I64Load8U = 0x31,
	I64Load16S = 0x32,
	I64Load16U = 0x33,
	I64Load32S = 0x34,
	I64Load32U = 0x35,
	// - Store instructions
	I32Store = 0x36,
	I64Store = 0x37,
	F32Store = 0x38,
	F64Store = 0x39,
	I32Store8 = 0x3A,
	I32Store16 = 0x3B,
	I64Store8 = 0x3C,
	I64Store16 = 0x3D,
	I64Store32 = 0x3E,
	// - Memory instructions
	MemorySize = 0x3F,
	MemoryGrow = 0x40,
	// - Constant instructions
	I32Const = 0x41,
	I64Const = 0x42,
	F32Const = 0x43,
	F64Const = 0x44,
	// I32 logical and comparison
	I32Eqz = 0x45,
	I32Eq = 0x46,
	I32Ne = 0x47,
	I32LtS = 0x48,
	I32LtU = 0x49,
	I32GtS = 0x4A,
	I32GtU = 0x4B,
	I32LeS = 0x4C,
	I32LeU = 0x4D,
	I32GeS = 0x4E,
	I32GeU = 0x4F,
	// I64 logical and comparison
	I64Eqz = 0x50,
	I64Eq = 0x51,
	I64Ne = 0x52,
	I64LtS = 0x53,
	I64LtU = 0x54,
	I64GtS = 0x55,
	I64GtU = 0x56,
	I64LeS = 0x57,
	I64LeU = 0x58,
	I64GeS = 0x59,
	I64GeU = 0x5A,
	// F32 comparison
	F32Eq = 0x5B,
	F32Ne = 0x5C,
	F32Lt = 0x5D,
	F32Gt = 0x5E,
	F32Le = 0x5F,
	F32Ge = 0x60,
	// F64 comparison
	F64Eq = 0x61,
	F64Ne = 0x62,
	F64Lt = 0x63,
	F64Gt = 0x64,
	F64Le = 0x65,
	F64Ge = 0x66,
	// - I32 arithmetic and bitwise operations
	I32Clz = 0x67,
	I32Ctz = 0x68,
	I32Popcnt = 0x69,
	I32Add = 0x6A,
	I32Sub = 0x6B,
	I32Mul = 0x6C,
	I32DivS = 0x6D,
	I32DivU = 0x6E,
	I32RemS = 0x6F,
	I32RemU = 0x70,
	I32And = 0x71,
	I32Or = 0x72,
	I32Xor = 0x73,
	I32Shl = 0x74,
	I32ShrS = 0x75,
	I32ShrU = 0x76,
	I32Rotl = 0x77,
	I32Rotr = 0x78,
	// - I64 arithmetic and bitwise operations
	I64Clz = 0x79,
	I64Ctz = 0x7A,
	I64Popcnt = 0x7B,
	I64Add = 0x7C,
	I64Sub = 0x7D,
	I64Mul = 0x7E,
	I64DivS = 0x7F,
	I64DivU = 0x80,
	I64RemS = 0x81,
	I64RemU = 0x82,
	I64And = 0x83,
	I64Or = 0x84,
	I64Xor = 0x85,
	I64Shl = 0x86,
	I64ShrS = 0x87,
	I64ShrU = 0x88,
	I64Rotl = 0x89,
	I64Rotr = 0x8A,
	// - F32 arithmetic operations
	F32Abs = 0x8B,
	F32Neg = 0x8C,
	F32Ceil = 0x8D,
	F32Floor = 0x8E,
	F32Trunc = 0x8F,
	F32Nearest = 0x90,
	F32Sqrt = 0x91,
	F32Add = 0x92,
	F32Sub = 0x93,
	F32Mul = 0x94,
	F32Div = 0x95,
	F32Min = 0x96,
	F32Max = 0x97,
	F32Copysign = 0x98,
	// - F64 arithmetic operations
	F64Abs = 0x99,
	F64Neg = 0x9A,
	F64Ceil = 0x9B,
	F64Floor = 0x9C,
	F64Trunc = 0x9D,
	F64Nearest = 0x9E,
	F64Sqrt = 0x9F,
	F64Add = 0xA0,
	F64Sub = 0xA1,
	F64Mul = 0xA2,
	F64Div = 0xA3,
	F64Min = 0xA4,
	F64Max = 0xA5,
	F64Copysign = 0xA6,
	// - Conversion instructions
	I32WrapI64 = 0xA7,
	I32TruncF32S = 0xA8,
	I32TruncF32U = 0xA9,
	I32TruncF64S = 0xAA,
	I32TruncF64U = 0xAB,
	I64ExtendI32S = 0xAC,
	I64ExtendI32U = 0xAD,
	I64TruncF32S = 0xAE,
	I64TruncF32U = 0xAF,
	I64TruncF64S = 0xB0,
	I64TruncF64U = 0xB1,
	F32ConvertI32S = 0xB2,
	F32ConvertI32U = 0xB3,
	F32ConvertI64S = 0xB4,
	F32ConvertI64U = 0xB5,
	F32DemoteF64 = 0xB6,
	F64ConvertI32S = 0xB7,
	F64ConvertI32U = 0xB8,
	F64ConvertI64S = 0xB9,
	F64ConvertI64U = 0xBA,
	F64PromoteF32 = 0xBB,
	I32ReinterpretF32 = 0xBC,
	I64ReinterpretF64 = 0xBD,
	F32ReinterpretI32 = 0xBE,
	F64ReinterpretI64 = 0xBF,
	// Bulk memory extension prefix (memory.copy, memory.fill, etc.).
	// Secondary opcode is a separate LEB128 u32 immediately following.
	BulkMemoryPrefix = 0xFC,
}

trait Encode {
	fn encode(&self, sink: &mut Vec<u8>);
}

/// A `memarg`: the alignment, then the offset. Memory 0 is implied; any
/// other is written between them, flagged by bit 6 of the alignment
/// (multi-memory).
fn encode_memarg(
	align: u32,
	offset: u32,
	memory_index: u32,
	sink: &mut Vec<u8>,
) {
	if memory_index == 0 {
		align.encode(sink);
	} else {
		(align | 0x40).encode(sink);
		memory_index.encode(sink);
	}
	offset.encode(sink);
}

/// A memory instruction: its opcode, then its `memarg`.
fn encode_memory_access(
	opcode: Opcode,
	align: u32,
	offset: u32,
	memory_index: u32,
	sink: &mut Vec<u8>,
) {
	sink.push(opcode as u8);
	encode_memarg(align, offset, memory_index, sink);
}

// An operation's opcode is a row indexed by its operand type: one entry per
// type its opcode takes (`Operands`), in `ScalarType` order.

fn column(operands: mir::Operands, ty: ScalarType) -> usize {
	use ScalarType::*;
	match (operands, ty) {
		(mir::Operands::Any, I32) => 0,
		(mir::Operands::Any, I64) => 1,
		(mir::Operands::Any, F32) => 2,
		(mir::Operands::Any, F64) => 3,
		(mir::Operands::Integer, I32) | (mir::Operands::Float, F32) => 0,
		(mir::Operands::Integer, I64) | (mir::Operands::Float, F64) => 1,
		_ => unreachable!("an opcode given a type it does not take"),
	}
}

fn unary_opcode(op: mir::UnaryOp, ty: ScalarType) -> Opcode {
	use Opcode::*;
	use mir::UnaryOp as U;
	let row: &[Opcode] = match op {
		U::Eqz => &[I32Eqz, I64Eqz],
		U::Neg => &[F32Neg, F64Neg],
		U::Abs => &[F32Abs, F64Abs],
		U::Sqrt => &[F32Sqrt, F64Sqrt],
		U::Floor => &[F32Floor, F64Floor],
		U::Ceil => &[F32Ceil, F64Ceil],
		U::Trunc => &[F32Trunc, F64Trunc],
		U::Nearest => &[F32Nearest, F64Nearest],
	};
	row[column(op.operands(), ty)]
}

fn binary_opcode(op: mir::BinaryOp, ty: ScalarType) -> Opcode {
	use Opcode::*;
	use mir::BinaryOp as B;
	let row: &[Opcode] = match op {
		B::Add => &[I32Add, I64Add, F32Add, F64Add],
		B::Sub => &[I32Sub, I64Sub, F32Sub, F64Sub],
		B::Mul => &[I32Mul, I64Mul, F32Mul, F64Mul],
		B::And => &[I32And, I64And],
		B::Or => &[I32Or, I64Or],
		B::Xor => &[I32Xor, I64Xor],
		B::Shl => &[I32Shl, I64Shl],
		B::ShrS => &[I32ShrS, I64ShrS],
		B::ShrU => &[I32ShrU, I64ShrU],
		B::DivS => &[I32DivS, I64DivS],
		B::DivU => &[I32DivU, I64DivU],
		B::RemS => &[I32RemS, I64RemS],
		B::RemU => &[I32RemU, I64RemU],
		B::Div => &[F32Div, F64Div],
		B::Min => &[F32Min, F64Min],
		B::Max => &[F32Max, F64Max],
		B::Copysign => &[F32Copysign, F64Copysign],
	};
	row[column(op.operands(), ty)]
}

fn compare_opcode(op: mir::CompareOp, ty: ScalarType) -> Opcode {
	use Opcode::*;
	use mir::CompareOp as C;
	let row: &[Opcode] = match op {
		C::Eq => &[I32Eq, I64Eq, F32Eq, F64Eq],
		C::Ne => &[I32Ne, I64Ne, F32Ne, F64Ne],
		C::LtS => &[I32LtS, I64LtS],
		C::LtU => &[I32LtU, I64LtU],
		C::LeS => &[I32LeS, I64LeS],
		C::LeU => &[I32LeU, I64LeU],
		C::GtS => &[I32GtS, I64GtS],
		C::GtU => &[I32GtU, I64GtU],
		C::GeS => &[I32GeS, I64GeS],
		C::GeU => &[I32GeU, I64GeU],
		C::Lt => &[F32Lt, F64Lt],
		C::Le => &[F32Le, F64Le],
		C::Gt => &[F32Gt, F64Gt],
		C::Ge => &[F32Ge, F64Ge],
	};
	row[column(op.operands(), ty)]
}

fn convert_opcode(
	op: mir::ConvertOp,
	from: ScalarType,
	to: ScalarType,
) -> Opcode {
	use Opcode::*;
	use ScalarType::{F32, F64, I32, I64};
	use mir::ConvertOp as V;
	match (op, from, to) {
		(V::ExtendS, I32, I64) => I64ExtendI32S,
		(V::ExtendU, I32, I64) => I64ExtendI32U,
		(V::Wrap, I64, I32) => I32WrapI64,
		(V::TruncS, F32, I32) => I32TruncF32S,
		(V::TruncU, F32, I32) => I32TruncF32U,
		(V::TruncS, F64, I32) => I32TruncF64S,
		(V::TruncU, F64, I32) => I32TruncF64U,
		(V::TruncS, F32, I64) => I64TruncF32S,
		(V::TruncU, F32, I64) => I64TruncF32U,
		(V::TruncS, F64, I64) => I64TruncF64S,
		(V::TruncU, F64, I64) => I64TruncF64U,
		(V::ConvertS, I32, F32) => F32ConvertI32S,
		(V::ConvertU, I32, F32) => F32ConvertI32U,
		(V::ConvertS, I64, F32) => F32ConvertI64S,
		(V::ConvertU, I64, F32) => F32ConvertI64U,
		(V::ConvertS, I32, F64) => F64ConvertI32S,
		(V::ConvertU, I32, F64) => F64ConvertI32U,
		(V::ConvertS, I64, F64) => F64ConvertI64S,
		(V::ConvertU, I64, F64) => F64ConvertI64U,
		(V::Promote, F32, F64) => F64PromoteF32,
		(V::Demote, F64, F32) => F32DemoteF64,
		(V::Reinterpret, F32, I32) => I32ReinterpretF32,
		(V::Reinterpret, I32, F32) => F32ReinterpretI32,
		(V::Reinterpret, F64, I64) => I64ReinterpretF64,
		(V::Reinterpret, I64, F64) => F64ReinterpretI64,
		_ => unreachable!("a conversion between types it does not convert"),
	}
}

fn load_opcode(access: mir::LoadAccess) -> Opcode {
	use mir::LoadAccess as L;
	match access {
		L::I8S => Opcode::I32Load8S,
		L::I8U => Opcode::I32Load8U,
		L::I16S => Opcode::I32Load16S,
		L::I16U => Opcode::I32Load16U,
		L::I32 => Opcode::I32Load,
		L::I64 => Opcode::I64Load,
		L::F32 => Opcode::F32Load,
		L::F64 => Opcode::F64Load,
	}
}

fn store_opcode(access: mir::StoreAccess) -> Opcode {
	use mir::StoreAccess as S;
	match access {
		S::I8 => Opcode::I32Store8,
		S::I16 => Opcode::I32Store16,
		S::I32 => Opcode::I32Store,
		S::I64 => Opcode::I64Store,
		S::F32 => Opcode::F32Store,
		S::F64 => Opcode::F64Store,
	}
}

impl Encode for i32 {
	fn encode(&self, sink: &mut Vec<u8>) {
		let (value, pos) = leb128fmt::encode_s32(*self).unwrap();
		sink.extend_from_slice(&value[..pos]);
	}
}

impl Encode for i64 {
	fn encode(&self, sink: &mut Vec<u8>) {
		let (value, pos) = leb128fmt::encode_s64(*self).unwrap();
		sink.extend_from_slice(&value[..pos]);
	}
}

impl Encode for f32 {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.extend_from_slice(&self.to_le_bytes());
	}
}

impl Encode for f64 {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.extend_from_slice(&self.to_le_bytes());
	}
}

impl Encode for u32 {
	fn encode(&self, sink: &mut Vec<u8>) {
		let (value, pos) = leb128fmt::encode_u32(*self).unwrap();
		sink.extend_from_slice(&value[..pos]);
	}
}

impl Encode for u64 {
	fn encode(&self, sink: &mut Vec<u8>) {
		let (value, pos) = leb128fmt::encode_u64(*self).unwrap();
		sink.extend_from_slice(&value[..pos]);
	}
}

impl Encode for ScalarType {
	fn encode(&self, sink: &mut Vec<u8>) {
		let opcode = match self {
			ScalarType::I32 => 0x7F,
			ScalarType::I64 => 0x7E,
			ScalarType::F32 => 0x7D,
			ScalarType::F64 => 0x7C,
		};

		sink.push(opcode);
	}
}

impl Encode for FunctionSignature {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(0x60); // Function type

		let param_count = self.param_count as u32;
		param_count.encode(sink);
		for param in self.params() {
			param.encode(sink);
		}

		let result_count = (self.param_results.len() - self.param_count) as u32;
		result_count.encode(sink);
		for result in self.results().iter() {
			result.encode(sink);
		}
	}
}

impl Encode for TypeSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Type as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		(self.signatures.len() as u32).encode(&mut section_sink);
		for signature in &self.signatures {
			signature.encode(&mut section_sink);
		}

		(section_sink.len() as u32).encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

impl Encode for ImportSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Import as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		(self.imports.len() as u32).encode(&mut section_sink);
		for import in &self.imports {
			// Module name
			(import.module.len() as u32).encode(&mut section_sink);
			section_sink.extend_from_slice(import.module.as_bytes());

			// Import name
			(import.name.len() as u32).encode(&mut section_sink);
			section_sink.extend_from_slice(import.name.as_bytes());

			// Import description
			match &import.desc {
				ImportDesc::Function { signature_index } => {
					section_sink.push(0x00); // Function import kind
					signature_index.0.encode(&mut section_sink);
				}
				ImportDesc::Global { ty, mutability } => {
					section_sink.push(0x03); // Global import kind
					ty.encode(&mut section_sink);
					match mutability {
						Mutability::Immutable => section_sink.push(0x00),
						Mutability::Mutable => section_sink.push(0x01),
					}
				}
				ImportDesc::Memory { memory } => {
					section_sink.push(0x02); // Memory import kind
					memory.encode(&mut section_sink);
				}
			}
		}

		(section_sink.len() as u32).encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

impl Encode for FunctionSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Function as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		let size = self.types.len() as u32;
		size.encode(&mut section_sink);
		for type_index in &self.types {
			type_index.0.encode(&mut section_sink);
		}

		let section_size = section_sink.len() as u32;
		section_size.encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

#[repr(u8)]
enum ExportKind {
	Function = 0x00,
	_Table = 0x01,
	Memory = 0x02,
	Global = 0x03,
}

impl Encode for ExportItem {
	fn encode(&self, sink: &mut Vec<u8>) {
		match self.clone() {
			ExportItem::Function { name, func_index } => {
				(name.len() as u32).encode(sink);
				sink.extend_from_slice(name.as_bytes());
				sink.push(ExportKind::Function as u8);
				func_index.0.encode(sink);
			}
			ExportItem::Global { name, global_index } => {
				(name.len() as u32).encode(sink);
				sink.extend_from_slice(name.as_bytes());
				sink.push(ExportKind::Global as u8);
				global_index.0.encode(sink);
			}
			ExportItem::Memory { name, memory_index } => {
				(name.len() as u32).encode(sink);
				sink.extend_from_slice(name.as_bytes());
				sink.push(ExportKind::Memory as u8);
				memory_index.encode(sink);
			}
		}
	}
}

impl Encode for ExportSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Export as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		let export_count = self.items.len() as u32;
		export_count.encode(&mut section_sink);
		for item in &self.items {
			item.encode(&mut section_sink);
		}

		let section_size = section_sink.len() as u32;
		section_size.encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

impl Encode for Global {
	fn encode(&self, sink: &mut Vec<u8>) {
		self.ty.encode(sink);
		sink.push(match self.mutability {
			Mutability::Immutable => 0x00,
			Mutability::Mutable => 0x01,
		});

		match self.value {
			wasm::Instruction::I32Const(value) => {
				sink.push(Opcode::I32Const as u8);
				value.encode(sink);
			}
			wasm::Instruction::F32Const(value) => {
				sink.push(Opcode::F32Const as u8);
				value.encode(sink);
			}
			wasm::Instruction::I64Const(value) => {
				sink.push(Opcode::I64Const as u8);
				value.encode(sink);
			}
			wasm::Instruction::F64Const(value) => {
				sink.push(Opcode::F64Const as u8);
				value.encode(sink);
			}
			_ => unreachable!(),
		}
		sink.push(Opcode::End as u8);
	}
}

impl Encode for GlobalSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Global as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		let global_count = self.globals.len() as u32;
		global_count.encode(&mut section_sink);
		for global in &self.globals {
			global.encode(&mut section_sink);
		}

		let section_size = section_sink.len() as u32;
		section_size.encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

impl Encode for StartSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		// TODO: maybe encode it without intermediate vec?
		sink.push(SectionId::Start as u8);
		let mut section_sink: Vec<u8> = Vec::new();
		self.func_index.encode(&mut section_sink);
		(section_sink.len() as u32).encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

impl FunctionBody {
	fn encode(
		&self,
		sink: &mut Vec<u8>,
		module: &WasmModule,
		func_index: FuncIndex,
	) {
		let mut body_content: Vec<u8> = Vec::new();

		let type_index = module.functions.types[func_index.0 as usize];
		let signature = module.types.signatures[type_index.0 as usize].clone();

		let mut grouped_locals = Vec::<(ScalarType, u32)>::new();
		for local in self.locals.iter().skip(signature.param_count) {
			match grouped_locals.last_mut() {
				Some((last_ty, count)) if *last_ty == local.ty => {
					*count += 1;
				}
				_ => {
					grouped_locals.push((local.ty, 1));
				}
			}
		}

		(grouped_locals.len() as u32).encode(&mut body_content);
		for (group_type, count) in grouped_locals {
			count.encode(&mut body_content);
			group_type.encode(&mut body_content);
		}

		body_content.extend_from_slice(
			&module.code.functions[func_index.0 as usize].expressions,
		);
		body_content.push(Opcode::End as u8);

		let body_size = body_content.len() as u32;
		body_size.encode(sink);
		sink.extend_from_slice(&body_content);
	}
}

trait ContextEncode {
	fn encode(&self, sink: &mut Vec<u8>, module: &WasmModule);
}

impl ContextEncode for CodeSection {
	fn encode(&self, sink: &mut Vec<u8>, module: &WasmModule) {
		sink.push(SectionId::Code as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		let function_count = self.functions.len() as u32;
		function_count.encode(&mut section_sink);
		for (index, func) in self.functions.iter().enumerate() {
			func.encode(&mut section_sink, module, FuncIndex(index as u32));
		}

		let section_size = section_sink.len() as u32;
		section_size.encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

impl Encode for RefType {
	fn encode(&self, sink: &mut Vec<u8>) {
		let ref_type = match self {
			RefType::FuncRef => 0x70,
			RefType::ExternRef => 0x6F,
		};
		sink.push(ref_type);
	}
}

impl Encode for ResizableLimits {
	fn encode(&self, sink: &mut Vec<u8>) {
		match self {
			ResizableLimits::Initial(initial) => {
				sink.push(0x00);
				initial.encode(sink);
			}
			ResizableLimits::InitialAndMax { initial, maximum } => {
				sink.push(0x01);
				initial.encode(sink);
				maximum.encode(sink);
			}
		}
	}
}

impl Encode for TableType {
	fn encode(&self, sink: &mut Vec<u8>) {
		self.ty.encode(sink);
		self.limits.encode(sink);
	}
}

impl Encode for TableSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Table as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		let table_count = self.tables.len() as u32;
		table_count.encode(&mut section_sink);
		for table in &self.tables {
			table.encode(&mut section_sink);
		}

		let section_size = section_sink.len() as u32;
		section_size.encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

impl Encode for ElementSegment {
	fn encode(&self, sink: &mut Vec<u8>) {
		self.table_index.0.encode(sink);
		sink.push(Opcode::I32Const as u8);
		self.offset.encode(sink);
		sink.push(Opcode::End as u8);

		let indicies_count = self.indices.len() as u32;
		indicies_count.encode(sink);
		for index in self.indices.iter().copied() {
			index.0.encode(sink);
		}
	}
}

impl Encode for ElementSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Element as u8);

		let mut section_sink: Vec<u8> = Vec::new();
		let segment_count = self.segments.len() as u32;
		segment_count.encode(&mut section_sink);
		for segment in &self.segments {
			segment.encode(&mut section_sink);
		}

		let section_size = section_sink.len() as u32;
		section_size.encode(sink);
		sink.extend_from_slice(&section_sink);
	}
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct DataSection {
	pub segments: Box<[DataSegment]>,
}

impl Encode for DataSection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Data as u8);

		let mut content = Vec::new();
		(self.segments.len() as u32).encode(&mut content);
		for segment in self.segments.iter() {
			segment.encode(&mut content);
		}

		(content.len() as u32).encode(sink);
		sink.extend_from_slice(&content);
	}
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct DataSegment {
	pub memory_index: u32,
	pub offset: u32,
	/// Width of the target memory: the offset init expression must be an
	/// `i64.const` for a 64-bit memory, `i32.const` otherwise.
	pub memory_kind: mir::MemoryKind,
	pub bytes: Box<[u8]>,
}

impl Encode for DataSegment {
	fn encode(&self, sink: &mut Vec<u8>) {
		// Segment flags: 0 = active in memory 0; 2 = active with an
		// explicit memory index (multi-memory). Never emit flags 2 for
		// memory 0 so single-memory modules stay extension-free.
		if self.memory_index == 0 {
			0u32.encode(sink);
		} else {
			2u32.encode(sink);
			self.memory_index.encode(sink);
		}
		// offset is encoded as a const init expr followed by end opcode
		match self.memory_kind {
			mir::MemoryKind::Memory32 => {
				sink.push(Opcode::I32Const as u8);
				(self.offset as i32).encode(sink);
			}
			mir::MemoryKind::Memory64 => {
				sink.push(Opcode::I64Const as u8);
				(self.offset as i64).encode(sink);
			}
		}
		sink.push(Opcode::End as u8);
		(self.bytes.len() as u32).encode(sink);
		sink.extend_from_slice(&self.bytes);
	}
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct MemorySection {
	pub memories: Box<[Memory]>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct Memory {
	pub limits: MemoryLimits,
	pub kind: mir::MemoryKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub enum MemoryLimits {
	Unbounded { initial_pages: u64 },
	Bounded { initial_pages: u64, max_pages: u64 },
}

/// `info`'s Wasm memory type, at least `required_pages` large.
///
/// `min_pages`/`max_pages` are hints, not obligations: just like `initial`
/// gets bumped above a too-small `min_pages`, `max_pages` gets bumped above
/// `initial` when it would otherwise be violated, rather than emitting an
/// `initial > max` module (invalid per spec).
fn memory_type(info: &mir::MemoryInfo, required_pages: u32) -> Memory {
	let initial = info.min_pages.unwrap_or(0).max(u64::from(required_pages));
	Memory {
		limits: match info.max_pages {
			Some(max) => MemoryLimits::Bounded {
				initial_pages: initial,
				max_pages: max.max(initial),
			},
			None => MemoryLimits::Unbounded {
				initial_pages: initial,
			},
		},
		kind: info.kind,
	}
}

impl Encode for MemorySection {
	fn encode(&self, sink: &mut Vec<u8>) {
		sink.push(SectionId::Memory as u8);

		let mut content = Vec::new();
		(self.memories.len() as u32).encode(&mut content);
		for memory in self.memories.iter() {
			memory.encode(&mut content);
		}

		(content.len() as u32).encode(sink);
		sink.extend_from_slice(&content);
	}
}

impl Encode for Memory {
	fn encode(&self, sink: &mut Vec<u8>) {
		// Limits flags byte: bit 0 = has max, bit 2 = 64-bit address space.
		let memory64 = match self.kind {
			mir::MemoryKind::Memory32 => 0x00,
			mir::MemoryKind::Memory64 => 0x04,
		};
		match &self.limits {
			MemoryLimits::Unbounded { initial_pages } => {
				sink.push(memory64);
				initial_pages.encode(sink);
			}
			MemoryLimits::Bounded {
				initial_pages,
				max_pages,
			} => {
				sink.push(0x01 | memory64);
				initial_pages.encode(sink);
				max_pages.encode(sink);
			}
		}
	}
}

impl WasmModule {
	pub fn encode(&self) -> Vec<u8> {
		let mut sink = [
			0x00, 0x61, 0x73, 0x6D, // Magic
			0x01, 0x00, 0x00, 0x00, // Version
		]
		.to_vec();

		self.types.encode(&mut sink);
		match self.imports.imports.len() {
			0 => {}
			_ => self.imports.encode(&mut sink),
		}
		match self.functions.types.len() {
			0 => {}
			_ => self.functions.encode(&mut sink),
		}
		match self.tables.tables.len() {
			0 => {}
			_ => self.tables.encode(&mut sink),
		}
		match self.memory.memories.len() {
			0 => {}
			_ => self.memory.encode(&mut sink),
		}
		match self.globals.globals.len() {
			0 => {}
			_ => self.globals.encode(&mut sink),
		}
		match self.exports.items.len() {
			0 => {}
			_ => self.exports.encode(&mut sink),
		}
		if let Some(ref start) = self.start {
			start.encode(&mut sink);
		}
		match self.elements.segments.len() {
			0 => {}
			_ => self.elements.encode(&mut sink),
		}
		self.code.encode(&mut sink, self);
		match self.data.segments.len() {
			0 => {}
			_ => self.data.encode(&mut sink),
		}

		sink
	}
}

// Disconnected from the module graph: `tests.rs` still calls the removed
// `tir::TIR::build` and is kept on disk as a reference corpus for new tests.
// #[cfg(test)]
// mod tests;
