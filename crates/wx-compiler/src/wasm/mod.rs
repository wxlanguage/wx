//! The WASM-shaped instruction representation the scheduler targets — a
//! flat, linear sequence of instructions for a stack machine, as opposed to
//! the tree (`mir::Function`) or graph (`opt::Function`) representations
//! earlier in the pipeline. `opt::scheduler` is the sole producer of a
//! [`Function`] today; it doesn't own these types — they're the contract
//! `codegen` consumes — which is also why the peephole optimizations that
//! operate purely on this representation ([`coalesce_locals`],
//! [`peephole_local_tee`]) live here rather than inside the producer.

use crate::mir;

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum ScalarType {
	I32,
	I64,
	F32,
	F64,
}

impl TryFrom<mir::Type> for ScalarType {
	type Error = ();
	fn try_from(ty: mir::Type) -> Result<Self, ()> {
		Ok(match ty {
			mir::Type::I32
			| mir::Type::U32
			| mir::Type::Bool
			| mir::Type::U8
			| mir::Type::I8
			| mir::Type::U16
			| mir::Type::I16
			| mir::Type::Function { .. } => ScalarType::I32,
			mir::Type::I64 | mir::Type::U64 => ScalarType::I64,
			mir::Type::Pointer { kind, .. } => match kind {
				mir::MemoryKind::Memory32 => ScalarType::I32,
				mir::MemoryKind::Memory64 => ScalarType::I64,
			},
			mir::Type::F32 => ScalarType::F32,
			mir::Type::F64 => ScalarType::F64,
			_ => return Err(()),
		})
	}
}

/// Recursively flatten a MIR type into its constituent WASM scalar types.
/// Unit/Never produce zero slots; Aggregate recurses into its fields. The
/// one place this conversion happens; every producer of a `Function` should
/// call this rather than repeating the match itself.
pub fn flatten_type_to_scalars(
	ty: mir::Type,
	aggregates: &[mir::Aggregate],
) -> Vec<ScalarType> {
	match ty {
		mir::Type::Unit | mir::Type::Never => vec![],
		mir::Type::Aggregate { aggregate_index } => aggregates
			[aggregate_index as usize]
			.values
			.iter()
			.flat_map(|&f| flatten_type_to_scalars(f, aggregates))
			.collect(),
		t => vec![ScalarType::try_from(t).expect("must be scalar")],
	}
}

/// The `memarg` immediate carried by every WebAssembly memory instruction.
#[cfg_attr(test, derive(Debug, PartialEq, serde::Serialize))]
#[derive(Clone, Copy)]
pub struct MemArg {
	/// Log2 of the alignment hint in bytes (e.g. 2 = 4-byte aligned).
	pub align: u32,
	/// Static byte offset added to the runtime address.
	pub offset: u32,
	pub memory: crate::ast::DefId,
}

/// A WASM local variable declaration.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(test, serde(transparent))]
#[derive(Clone, Copy)]
pub struct Local {
	pub ty: ScalarType,
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct Function {
	/// Locals in declaration order (params first, then spill slots).
	pub locals: Vec<Local>,
	/// Flat WASM stack-machine instruction sequence for the function body.
	pub body: Vec<Instruction>,
	/// Flat arena backing every [`Instruction::BrTable`] in `body` — each
	/// instruction stores a `(start, len)` range into this `Vec` instead of
	/// its own heap allocation, so `br_table`-heavy functions don't pay one
	/// allocation per switch.
	pub br_table_depths: Vec<u32>,
}

/// A subset of WASM instructions produced by the scheduler.
/// Each variant maps 1-to-1 to a WASM opcode; operands are pushed onto the
/// implicit value stack by the preceding instructions.
#[cfg_attr(test, derive(Debug, serde::Serialize))]
#[derive(Clone)]
pub enum Instruction {
	// Constants
	I32Const(i32),
	I64Const(i64),
	F32Const(f32),
	F64Const(f64),
	// Locals
	LocalGet(u32),
	LocalSet(u32),
	LocalTee(u32),
	// Globals
	GlobalGet(crate::ast::DefId),
	GlobalSet(crate::ast::DefId),
	// Arithmetic — i32
	I32Add,
	I32Sub,
	I32Mul,
	I32DivS,
	I32DivU,
	I32RemS,
	I32RemU,
	I32And,
	I32Or,
	I32Xor,
	I32Shl,
	I32ShrS,
	I32ShrU,
	I32Eqz,
	I32Eq,
	I32Ne,
	I32LtS,
	I32LtU,
	I32LeS,
	I32LeU,
	I32GtS,
	I32GtU,
	I32GeS,
	I32GeU,
	I32Clz,
	I32Ctz,
	// Arithmetic — i64
	I64Add,
	I64Sub,
	I64Mul,
	I64DivS,
	I64DivU,
	I64RemS,
	I64RemU,
	I64And,
	I64Or,
	I64Xor,
	I64Shl,
	I64ShrS,
	I64ShrU,
	I64Eqz,
	I64Eq,
	I64Ne,
	I64LtS,
	I64LtU,
	I64LeS,
	I64LeU,
	I64GtS,
	I64GtU,
	I64GeS,
	I64GeU,
	// Arithmetic — f32 / f64
	F32Add,
	F32Sub,
	F32Mul,
	F32Div,
	F32Neg,
	F32Sqrt,
	F32Abs,
	F32Floor,
	F32Ceil,
	F32Trunc,
	F32Nearest,
	F32Min,
	F32Max,
	F32Copysign,
	F64Add,
	F64Sub,
	F64Mul,
	F64Div,
	F64Neg,
	F64Sqrt,
	F64Abs,
	F64Floor,
	F64Ceil,
	F64Trunc,
	F64Nearest,
	F64Min,
	F64Max,
	F64Copysign,
	F32Eq,
	F32Ne,
	F32Lt,
	F32Le,
	F32Gt,
	F32Ge,
	F64Eq,
	F64Ne,
	F64Lt,
	F64Le,
	F64Gt,
	F64Ge,
	// Control flow
	Block {
		ty: BlockType,
	},
	Loop {
		ty: BlockType,
	},
	If {
		ty: BlockType,
	},
	Else,
	End,
	Br(u32), // break by depth
	BrIf(u32),
	/// `[start, start + len)` range into [`Function::br_table_depths`].
	/// All entries but the last are the concrete per-case branch depths; the
	/// last entry is the default branch depth.
	BrTable {
		start: u32,
		len: u32,
	},
	Return,
	Unreachable,
	Drop,
	// Calls
	/// Direct call; the encoder resolves the WASM function index from
	/// `func_wasm_index`, covering both internal and imported functions.
	Call(crate::ast::DefId),
	/// Indirect call via the function table; the encoder resolves `type_index`
	/// from the referenced MIR signature.
	CallIndirectSym {
		mir_sig_index: u32,
	},
	// Memory
	MemorySize(crate::ast::DefId),
	MemoryGrow(crate::ast::DefId),
	MemoryFill(crate::ast::DefId),
	MemoryCopy {
		dst: crate::ast::DefId,
		src: crate::ast::DefId,
	},
	/// Wasm linear-memory index as an `i32.const`, resolved at codegen.
	MemoryIndex {
		memory: crate::ast::DefId,
	},
	// Pointer load/store
	I32Load8S(MemArg),
	I32Load8U(MemArg),
	I32Load16S(MemArg),
	I32Load16U(MemArg),
	I32Load(MemArg),
	I64Load(MemArg),
	F32Load(MemArg),
	F64Load(MemArg),
	I32Store8(MemArg),
	I32Store16(MemArg),
	I32Store(MemArg),
	I64Store(MemArg),
	F32Store(MemArg),
	F64Store(MemArg),
	// Conversion
	I64ExtendI32S,
	I64ExtendI32U,
	I32WrapI64,
	F32ConvertI32S,
	F32ConvertI32U,
	F32ConvertI64S,
	F32ConvertI64U,
	F64ConvertI32S,
	F64ConvertI32U,
	F64ConvertI64S,
	F64ConvertI64U,
	I32TruncF32S,
	I32TruncF32U,
	I32TruncF64S,
	I32TruncF64U,
	I64TruncF32S,
	I64TruncF32U,
	I64TruncF64S,
	I64TruncF64U,
	F64PromoteF32,
	F32DemoteF64,
	I32ReinterpretF32,
	F32ReinterpretI32,
	I64ReinterpretF64,
	F64ReinterpretI64,
	// Nop (used as a placeholder)
	Nop,
	// Symbolic references — resolved to concrete i32.const values by the
	// codegen encoder, which has access to the string pool and function table.
	/// A function referenced as a value; the encoder pushes it into the
	/// function table and emits `i32.const <table_index>`.
	FunctionPointer(crate::ast::DefId),
	/// End of the static data section for a given memory (base of writable
	/// heap); the encoder emits `i32.const <data_section_end>`.
	DataSectionEnd {
		memory: crate::ast::DefId,
	},
	/// A static array; the encoder resolves the index to a byte offset in the
	/// data segment and emits `i32.const <byte_offset>`.
	StaticDataPointer {
		data_index: u32,
		ty: ScalarType,
	},
}

#[cfg_attr(test, derive(Debug, serde::Serialize))]
#[derive(Clone, Copy)]
pub enum BlockType {
	Empty,
	Value(ScalarType),
}

// ── Local coalescing ──────────────────────────────────────────────────────────

/// Reuse WASM local slots for spilled values whose live ranges do not overlap.
///
/// Each spill slot has a live range `[first_write, last_read]` measured in flat
/// instruction-list positions. Two slots of the same WASM type can share a slot
/// number when one range ends strictly before the other begins.
///
/// Param slots (indices `0..params_count`) are never remapped — WASM passes
/// arguments via the first N locals and the ABI cannot be changed.
pub fn coalesce_locals(
	body: &mut [Instruction],
	locals: &mut Vec<Local>,
	params_count: usize,
) {
	let n = locals.len();
	if n <= params_count {
		return;
	}

	// ── Step 1: compute live ranges ──────────────────────────────────────────
	let mut first_write = vec![usize::MAX; n];
	let mut last_read = vec![0usize; n];

	for (i, instr) in body.iter().enumerate() {
		match instr {
			Instruction::LocalSet(s) => {
				let s = *s as usize;
				if s >= params_count {
					first_write[s] = first_write[s].min(i);
				}
			}
			Instruction::LocalGet(s) => {
				let s = *s as usize;
				if s >= params_count {
					last_read[s] = last_read[s].max(i);
				}
			}
			Instruction::LocalTee(s) => {
				let s = *s as usize;
				if s >= params_count {
					first_write[s] = first_write[s].min(i);
					last_read[s] = last_read[s].max(i);
				}
			}
			_ => {}
		}
	}

	// A `[first_write, last_read]` window computed from flat textual positions
	// is only valid for straight-line code: it implicitly assumes every
	// instruction executes at most once. `Loop` is the one construct that
	// breaks that assumption — its body is a single textual span that
	// actually runs many times, via a back-edge (`Br`) to the `Loop`
	// instruction itself. A slot written once before the loop and read once
	// inside it gets `last_read` pinned to that first textual occurrence,
	// even though the same read recurs on every later iteration. If some
	// other slot's write/read pair falls entirely after that position but
	// still inside the loop body, the ranges look non-overlapping and the
	// allocator happily hands them the same physical local — which then
	// gets clobbered by the second slot's write before the first slot's
	// value is read again on the next iteration.
	//
	// Fix: widen every slot touched anywhere inside a loop so its range
	// covers that loop's entire `[Loop, End]` span (and transitively every
	// loop it's nested in, since the same argument applies at each nesting
	// level). Two slots both live inside the same loop then always overlap
	// and can never be coalesced together, which is what correctness under
	// repeated execution requires.
	let mut frame_starts: Vec<usize> = Vec::new();
	let mut loop_spans: Vec<(usize, usize)> = Vec::new();
	for (i, instr) in body.iter().enumerate() {
		match instr {
			Instruction::Block { .. } | Instruction::If { .. } => {
				frame_starts.push(usize::MAX);
			}
			Instruction::Loop { .. } => {
				frame_starts.push(i);
			}
			Instruction::End => {
				if let Some(start) = frame_starts.pop() {
					if start != usize::MAX {
						loop_spans.push((start, i));
					}
				}
			}
			_ => {}
		}
	}

	for &(ls, le) in &loop_spans {
		for instr in &body[ls..=le] {
			let s = match instr {
				Instruction::LocalGet(s)
				| Instruction::LocalSet(s)
				| Instruction::LocalTee(s) => *s as usize,
				_ => continue,
			};
			if s >= params_count {
				first_write[s] = first_write[s].min(ls);
				last_read[s] = last_read[s].max(le);
			}
		}
	}

	// Normalize: dead stores (written, never read) collapse to a point range.
	// Slots never written (shouldn't normally happen) get range [0, 0].
	for s in params_count..n {
		if first_write[s] == usize::MAX {
			first_write[s] = 0;
		}
		if last_read[s] < first_write[s] {
			last_read[s] = first_write[s];
		}
	}

	// ── Step 2: linear scan ──────────────────────────────────────────────────
	let mut order: Vec<usize> = (params_count..n).collect();
	order.sort_unstable_by_key(|&s| first_write[s]);

	let ty_idx = |ty: ScalarType| match ty {
		ScalarType::I32 => 0usize,
		ScalarType::I64 => 1,
		ScalarType::F32 => 2,
		ScalarType::F64 => 3,
	};

	// Per-type free lists of slot numbers available for reuse.
	let mut free: [Vec<u32>; 4] =
		[Vec::new(), Vec::new(), Vec::new(), Vec::new()];
	// Active intervals: (last_read, new_slot_number, type_index).
	let mut active: Vec<(usize, u32, usize)> = Vec::new();
	let mut next_slot = params_count as u32;
	let mut mapping = vec![0u32; n];
	for (i, slot) in mapping.iter_mut().enumerate().take(params_count) {
		*slot = i as u32;
	}

	for old in order {
		let start = first_write[old];
		let end = last_read[old];
		let ti = ty_idx(locals[old].ty);

		// Expire intervals that ended strictly before this one starts.
		let mut i = 0;
		while i < active.len() {
			if active[i].0 < start {
				let (_, freed, freed_ti) = active.swap_remove(i);
				free[freed_ti].push(freed);
			} else {
				i += 1;
			}
		}

		let new_slot = free[ti].pop().unwrap_or_else(|| {
			let s = next_slot;
			next_slot += 1;
			s
		});

		mapping[old] = new_slot;
		active.push((end, new_slot, ti));
	}

	// ── Step 3: rebuild locals and rewrite instructions ──────────────────────
	let new_spill_count = (next_slot - params_count as u32) as usize;
	let mut spill_types = vec![ScalarType::I32; new_spill_count];
	for old in params_count..n {
		let new = mapping[old] as usize;
		if new >= params_count {
			spill_types[new - params_count] = locals[old].ty;
		}
	}
	locals.truncate(params_count);
	locals.extend(spill_types.into_iter().map(|ty| Local { ty }));

	for instr in body.iter_mut() {
		match instr {
			Instruction::LocalGet(s)
			| Instruction::LocalSet(s)
			| Instruction::LocalTee(s) => {
				*s = mapping[*s as usize];
			}
			_ => {}
		}
	}
}

/// Replace `LocalSet(n), LocalGet(n)` pairs with a single `LocalTee(n)`,
/// and eliminate `LocalTee(n), LocalSet(n)` by dropping the redundant tee.
///
/// `local.tee` writes the top-of-stack value to the local *and* leaves a copy
/// on the stack, which is exactly what set+get does in two instructions.
/// Conversely, `local.tee(n)` immediately followed by `local.set(n)` writes
/// the same value to the local twice — the tee is redundant; a plain set suffices.
pub fn peephole_local_tee(body: &mut Vec<Instruction>) {
	let mut out = Vec::with_capacity(body.len());
	let mut i = 0;
	while i < body.len() {
		if let Instruction::LocalSet(s) = body[i] {
			// set(N), get(N), set(N) → set(N): the middle get feeds back into a set
			// of the same slot, so both the tee and the redundant write collapse.
			if i + 2 < body.len() {
				if let (Instruction::LocalGet(g), Instruction::LocalSet(s2)) =
					(&body[i + 1], &body[i + 2])
				{
					if *g == s && *s2 == s {
						out.push(Instruction::LocalSet(s));
						i += 3;
						continue;
					}
				}
			}
			// set(N), get(N) → tee(N)
			if i + 1 < body.len() {
				if let Instruction::LocalGet(g) = body[i + 1] {
					if s == g {
						out.push(Instruction::LocalTee(s));
						i += 2;
						continue;
					}
				}
			}
		}
		out.push(body[i].clone());
		i += 1;
	}
	*body = out;
}
