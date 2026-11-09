//! Wasm-shaped stack instructions produced by MIR linearization and consumed
//! by codegen's encoder. Optional local coalescing and peepholes live here;
//! they are independent of graph construction and are not required by the
//! default backend pipeline.

use crate::mir;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub enum ScalarType {
	I32,
	I64,
	F32,
	F64,
}

impl ScalarType {
	pub fn is_float(self) -> bool {
		matches!(self, Self::F32 | Self::F64)
	}
}

impl TryFrom<mir::ValueType> for ScalarType {
	type Error = ();
	fn try_from(ty: mir::ValueType) -> Result<Self, ()> {
		Ok(match ty {
			mir::ValueType::I32 => ScalarType::I32,
			mir::ValueType::I64 => ScalarType::I64,
			mir::ValueType::F32 => ScalarType::F32,
			mir::ValueType::F64 => ScalarType::F64,
			_ => return Err(()),
		})
	}
}

/// The `memarg` immediate carried by every WebAssembly memory instruction.
#[cfg_attr(test, derive(Debug, PartialEq))]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
#[derive(Clone, Copy)]
pub struct MemArg {
	/// Log2 of the alignment hint in bytes (e.g. 2 = 4-byte aligned).
	pub align: u32,
	/// Static byte offset added to the runtime address.
	pub offset: u32,
	pub memory: mir::MemoryId,
}

/// A WASM local variable declaration.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
#[cfg_attr(any(debug_assertions, test), serde(transparent))]
#[derive(Clone, Copy)]
pub struct Local {
	pub ty: ScalarType,
}

#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
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

/// One Wasm instruction; operands are pushed onto the implicit value stack
/// by the preceding instructions. An operation carries MIR's opcode and the
/// type of its operands, which name the instruction together (`Binary(DivU,
/// I32)` is `i32.div_u`); only a pair MIR's `verify` admits is ever built.
#[cfg_attr(test, derive(Debug))]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
#[derive(Clone, Copy)]
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
	GlobalGet(mir::GlobalId),
	GlobalSet(mir::GlobalId),
	// Operations, each typed by its operands
	Unary(mir::UnaryOp, ScalarType),
	Binary(mir::BinaryOp, ScalarType),
	Compare(mir::CompareOp, ScalarType),
	Convert {
		op: mir::ConvertOp,
		from: ScalarType,
		to: ScalarType,
	},
	Load(mir::LoadAccess, MemArg),
	Store(mir::StoreAccess, MemArg),
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
	Call(mir::FunctionId),
	/// Indirect call via the function table; the encoder resolves `type_index`
	/// from the referenced MIR signature.
	CallIndirectSym {
		mir_sig_index: mir::SignatureIndex,
	},
	// Memory
	MemorySize(mir::MemoryId),
	MemoryGrow(mir::MemoryId),
	MemoryFill(mir::MemoryId),
	MemoryCopy {
		dst: mir::MemoryId,
		src: mir::MemoryId,
	},
	/// Wasm linear-memory index as an `i32.const`, resolved at codegen.
	MemoryIndex {
		memory: mir::MemoryId,
	},
	// Nop (used as a placeholder)
	Nop,
	// Symbolic references — resolved to concrete i32.const values by the
	// codegen encoder, which has access to the string pool and function table.
	/// A function referenced as a value; the encoder pushes it into the
	/// function table and emits `i32.const <table_index>`.
	FunctionPointer(mir::FunctionId),
	/// The address right after a memory's static data; the encoder emits a
	/// constant as wide as the memory's addresses.
	DataEnd {
		memory: mir::MemoryId,
	},
	/// The address `offset` bytes into a static entry; the encoder adds the
	/// entry's address and emits a constant of `ty`.
	StaticDataPointer {
		entry: mir::StaticEntryId,
		offset: u32,
		ty: ScalarType,
	},
}

#[cfg_attr(test, derive(Debug))]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
#[derive(Clone, Copy)]
pub enum BlockType {
	Empty,
	Value(ScalarType),
	/// Several results: the signature's, which has no parameters.
	Results(mir::SignatureIndex),
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
		out.push(body[i]);
		i += 1;
	}
	*body = out;
}
