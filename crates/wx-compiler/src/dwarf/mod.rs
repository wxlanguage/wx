//! Hand-rolled DWARF5 debug-info encoder for `--debug` wasm builds. See
//! `WebAssembly/tool-conventions/Dwarf.md` for how DWARF is adapted to
//! wasm: addresses are Code-section-relative byte offsets (exactly what
//! `codegen::DebugSpan`/`FunctionDebugInfo` already carry), and variable
//! locations use the vendor `DW_OP_WASM_location` extension instead of
//! registers.
//!
//! Deliberately hand-rolled rather than built on `gimli::write`: the
//! feature surface actually needed is narrow — one compile unit, no
//! relocations (every address here is already a resolved constant), no
//! location lists, no range lists, no call-frame info, no split-DWARF — and
//! this matches the rest of the compiler's style: `codegen/mod.rs` already
//! hand-rolls the entire wasm binary encoder the same way, with
//! `leb128fmt` as the only real primitive dependency. `gimli`'s *read* side
//! is used only in this module's own tests (a dev-dependency), to verify
//! this encoder's output actually parses the way a real consumer would see
//! it — never shipped in the release binary.
//!
//! Every byte layout below (DWARF5's CU header field order, the
//! `.debug_line` v5 header's directory/file-entry-format tables, form
//! widths) was cross-checked against `gimli`'s own parser
//! (`gimli::read::unit::parse_unit_header`, `gimli::read::line::parse`) —
//! not just recalled from memory.
//!
//! Scope, matching what wasm's `--debug` lowering (`mir::scheduler`)
//! actually produces:
//! - No `DW_TAG_lexical_block` — every variable/parameter DIE is a direct
//!   child of its function's `DW_TAG_subprogram`, visible for the whole
//!   function. This matches wasm's own local-storage model: every declared
//!   local gets function-lifetime storage regardless of which source block
//!   declared it, so this isn't a loss of precision.
//! - Struct-typed locals use `DW_OP_piece` composite locations: one
//!   `DW_OP_WASM_location`+`DW_OP_piece` pair per flattened leaf field, in
//!   the same physical order `mir::Aggregate::values`/`::offsets` already
//!   use — the standard DWARF mechanism for "this value's storage is split
//!   across several locations" (the textbook case being a struct promoted
//!   into two registers), not a hack.
//! - Struct type DIEs are never deduplicated across the compile unit
//!   (unlike base/pointer types, which are): `mir::Aggregate` is shared
//!   structurally, so two differently-named, identically-shaped structs
//!   can point at the same `AggregateIndex` — building one shared, named
//!   `DW_TAG_structure_type` per `AggregateIndex` would mean one of them
//!   shows the other's name. Building a fresh structure DIE per
//!   `LocalDebugInfo::struct_debug` occurrence sidesteps that entirely, at
//!   the cost of some duplicate DIEs when the same struct type is used by
//!   several locals — a reasonable size/simplicity trade for a first cut.
//! - Struct field names are one level deep only: a field that's itself a
//!   struct falls back to positional member names (`field0`, `field1`,
//!   ...), matching the same limit already established on
//!   `mir::StructDebugInfo`.
//! - The line-number program uses only the general opcodes
//!   (`DW_LNS_advance_pc`/`DW_LNS_advance_line`/`DW_LNS_set_file`/
//!   `DW_LNS_set_column`/`DW_LNS_copy` + `DW_LNE_end_sequence`/
//!   `DW_LNE_set_address`) — no special-opcode compression table, which is
//!   a size optimization, not a correctness requirement.

use std::collections::HashMap;

use crate::codegen::{DebugSpan, FunctionDebugInfo};
use crate::{ast, mir, vfs, wasm};

#[cfg(test)]
mod tests;

mod constants {
	// DW_TAG_*
	pub const DW_TAG_FORMAL_PARAMETER: u64 = 0x05;
	pub const DW_TAG_MEMBER: u64 = 0x0d;
	pub const DW_TAG_POINTER_TYPE: u64 = 0x0f;
	pub const DW_TAG_COMPILE_UNIT: u64 = 0x11;
	pub const DW_TAG_STRUCTURE_TYPE: u64 = 0x13;
	pub const DW_TAG_BASE_TYPE: u64 = 0x24;
	pub const DW_TAG_SUBPROGRAM: u64 = 0x2e;
	pub const DW_TAG_VARIABLE: u64 = 0x34;

	// DW_AT_*
	pub const DW_AT_LOCATION: u64 = 0x02;
	pub const DW_AT_NAME: u64 = 0x03;
	pub const DW_AT_BYTE_SIZE: u64 = 0x0b;
	pub const DW_AT_STMT_LIST: u64 = 0x10;
	pub const DW_AT_LOW_PC: u64 = 0x11;
	pub const DW_AT_HIGH_PC: u64 = 0x12;
	pub const DW_AT_COMP_DIR: u64 = 0x1b;
	pub const DW_AT_PRODUCER: u64 = 0x25;
	pub const DW_AT_DATA_MEMBER_LOCATION: u64 = 0x38;
	pub const DW_AT_ENCODING: u64 = 0x3e;
	pub const DW_AT_TYPE: u64 = 0x49;

	// DW_FORM_*
	pub const DW_FORM_ADDR: u64 = 0x01;
	pub const DW_FORM_DATA1: u64 = 0x0b;
	pub const DW_FORM_DATA4: u64 = 0x06;
	pub const DW_FORM_STRP: u64 = 0x0e;
	pub const DW_FORM_UDATA: u64 = 0x0f;
	pub const DW_FORM_REF4: u64 = 0x13;
	pub const DW_FORM_SEC_OFFSET: u64 = 0x17;
	pub const DW_FORM_EXPRLOC: u64 = 0x18;
	pub const DW_FORM_LINE_STRP: u64 = 0x1f;

	// DW_ATE_* (base_type encodings)
	pub const DW_ATE_BOOLEAN: u8 = 0x02;
	pub const DW_ATE_FLOAT: u8 = 0x04;
	pub const DW_ATE_SIGNED: u8 = 0x05;
	pub const DW_ATE_UNSIGNED: u8 = 0x07;

	pub const DW_UT_COMPILE: u8 = 0x01;

	// Standard line-number opcodes actually emitted (opcode_base = 13
	// covers 1..=12; the table above 12 exists purely for reader
	// compatibility — see `standard_opcode_lengths` in `LineProgramBuilder`).
	pub const DW_LNS_COPY: u8 = 0x01;
	pub const DW_LNS_ADVANCE_PC: u8 = 0x02;
	pub const DW_LNS_ADVANCE_LINE: u8 = 0x03;
	pub const DW_LNS_SET_FILE: u8 = 0x04;
	pub const DW_LNS_SET_COLUMN: u8 = 0x05;

	pub const DW_LNE_END_SEQUENCE: u8 = 0x01;
	pub const DW_LNE_SET_ADDRESS: u8 = 0x02;

	pub const DW_LNCT_PATH: u64 = 0x1;
	pub const DW_LNCT_DIRECTORY_INDEX: u64 = 0x2;

	/// Vendor extension opcode for wasm-specific location descriptions —
	/// not part of core DWARF. See
	/// <https://github.com/WebAssembly/tool-conventions/blob/main/Dwarf.md>.
	pub const DW_OP_WASM_LOCATION: u8 = 0xED;
	/// `wasm-op` selector for `DW_OP_WASM_LOCATION`: value is in a wasm
	/// local, ULEB128 index follows.
	pub const WASM_LOCATION_LOCAL: u8 = 0x00;
	pub const DW_OP_PIECE: u8 = 0x93;
	/// Marks the preceding operations as having computed the value itself
	/// (not an address to dereference) — see `build_location_expr`.
	pub const DW_OP_STACK_VALUE: u8 = 0x9f;

	/// Fixed abbreviation codes — one per DIE shape this module ever
	/// emits, hand-written rather than dynamically deduplicated (see the
	/// module doc comment).
	pub mod abbrev_code {
		pub const COMPILE_UNIT: u64 = 1;
		pub const SUBPROGRAM: u64 = 2;
		pub const FORMAL_PARAMETER: u64 = 3;
		pub const VARIABLE: u64 = 4;
		pub const BASE_TYPE: u64 = 5;
		pub const POINTER_TYPE: u64 = 6;
		pub const STRUCTURE_TYPE: u64 = 7;
		pub const MEMBER: u64 = 8;
	}
}

use constants::*;

fn push_uleb128(sink: &mut Vec<u8>, value: u64) {
	let (bytes, len) = leb128fmt::encode_u64(value).unwrap();
	sink.extend_from_slice(&bytes[..len]);
}

fn push_sleb128(sink: &mut Vec<u8>, value: i64) {
	let (bytes, len) = leb128fmt::encode_s64(value).unwrap();
	sink.extend_from_slice(&bytes[..len]);
}

/// An append-only, deduplicating string pool — the shared shape behind
/// `.debug_str` and `.debug_line_str` (kept as two separate instances,
/// never cross-referenced, matching DWARF5's convention that regular names
/// and line-table file/directory names live in different sections).
#[derive(Default)]
struct StringTable {
	bytes: Vec<u8>,
	offsets: HashMap<String, u32>,
}

impl StringTable {
	fn intern(&mut self, s: &str) -> u32 {
		if let Some(&offset) = self.offsets.get(s) {
			return offset;
		}
		let offset = self.bytes.len() as u32;
		self.bytes.extend_from_slice(s.as_bytes());
		self.bytes.push(0);
		self.offsets.insert(s.to_string(), offset);
		offset
	}
}

/// The DWARF sections this module produces, ready to embed as wasm custom
/// sections via [`custom_section`].
pub struct Sections {
	pub debug_abbrev: Vec<u8>,
	pub debug_info: Vec<u8>,
	pub debug_line: Vec<u8>,
	pub debug_str: Vec<u8>,
	pub debug_line_str: Vec<u8>,
	pub debug_aranges: Vec<u8>,
}

/// Builds every DWARF section for a `--debug` module from the data
/// `codegen::WasmModule::encode_with_debug_spans` already produced, plus
/// `mir`/`interner`/`files` for names, struct layouts, and source
/// positions. `function_debug_info` must be index-aligned with
/// `mir.functions` (true by construction: both come from the same
/// `mir.functions.iter()` walk in `codegen::Builder::build`).
pub fn build(
	debug_spans: &[DebugSpan],
	function_debug_info: &[FunctionDebugInfo],
	mir: &mir::MIR,
	interner: &ast::StringInterner,
	files: &vfs::Files,
) -> Sections {
	let debug_abbrev = build_debug_abbrev();

	let mut info_builder = DebugInfoBuilder::new();
	let debug_info = info_builder.build(function_debug_info, mir, interner);

	let mut line_builder = LineProgramBuilder::new();
	let debug_line =
		line_builder.build(debug_spans, function_debug_info, files);

	let cu_low_pc = function_debug_info
		.iter()
		.map(|f| f.start)
		.min()
		.unwrap_or(0);
	let cu_high_pc =
		function_debug_info.iter().map(|f| f.end).max().unwrap_or(0);
	let debug_aranges = build_debug_aranges(cu_low_pc, cu_high_pc);

	Sections {
		debug_abbrev,
		debug_info,
		debug_line,
		debug_str: info_builder.debug_str.bytes,
		debug_line_str: line_builder.debug_line_str.bytes,
		debug_aranges,
	}
}

/// `.debug_aranges`: a fast address-range → compile-unit index, separate
/// from (and not required by) the DIE tree in `.debug_info` — some DWARF
/// consumers use it specifically to resolve "which compile unit/function
/// contains this PC" at runtime (e.g. when a debugger pauses), rather than
/// walking the DIE tree, which is otherwise sufficient for everything else
/// this module does (source-line lookups, variable locations, ...). One
/// entry, covering the whole module, since there's only ever one compile
/// unit. Byte layout verified against `gimli::read::aranges::ArangeHeader::
/// parse` — notably its version field is *always* 2 regardless of the
/// referenced CU's own DWARF version (a real, spec-mandated quirk, not a
/// typo), and the header is padded to a `2 * address_size` boundary before
/// the first `(address, length)` tuple.
fn build_debug_aranges(low_pc: u32, high_pc: u32) -> Vec<u8> {
	let mut sink = Vec::new();
	sink.extend_from_slice(&0u32.to_le_bytes()); // unit_length placeholder
	let body_start = sink.len();

	sink.extend_from_slice(&2u16.to_le_bytes()); // version — always 2
	sink.extend_from_slice(&0u32.to_le_bytes()); // debug_info_offset: our one CU, at offset 0
	sink.push(4); // address_size
	sink.push(0); // segment_selector_size
	sink.extend_from_slice(&[0u8; 4]); // pad header (12 bytes) to a 8-byte tuple boundary

	sink.extend_from_slice(&low_pc.to_le_bytes());
	sink.extend_from_slice(&(high_pc - low_pc).to_le_bytes());
	sink.extend_from_slice(&0u32.to_le_bytes()); // terminator: (0, 0)
	sink.extend_from_slice(&0u32.to_le_bytes());

	let unit_length = (sink.len() - body_start) as u32;
	sink[0..4].copy_from_slice(&unit_length.to_le_bytes());
	sink
}

/// Encodes the wasm custom section framing (section id 0, name,
/// length-prefixed payload) around raw section bytes — the same shape for
/// every DWARF section (`.debug_info`, `.debug_line`, ...): a `name` (with
/// its leading dot, per `WebAssembly/tool-conventions`) and the section's
/// own bytes verbatim as the payload.
pub fn custom_section(name: &str, payload: &[u8]) -> Vec<u8> {
	let mut content = Vec::new();
	push_uleb128(&mut content, name.len() as u64);
	content.extend_from_slice(name.as_bytes());
	content.extend_from_slice(payload);

	let mut section = vec![0x00]; // wasm SectionId::Custom
	push_uleb128(&mut section, content.len() as u64);
	section.extend_from_slice(&content);
	section
}

/// Writes one `(tag, has_children, [(attr, form), ...])` abbreviation
/// declaration.
fn push_abbrev_decl(
	sink: &mut Vec<u8>,
	code: u64,
	tag: u64,
	has_children: bool,
	attrs: &[(u64, u64)],
) {
	push_uleb128(sink, code);
	push_uleb128(sink, tag);
	sink.push(has_children as u8);
	for &(attr, form) in attrs {
		push_uleb128(sink, attr);
		push_uleb128(sink, form);
	}
	push_uleb128(sink, 0);
	push_uleb128(sink, 0);
}

/// The fixed `.debug_abbrev` table — one declaration per DIE shape this
/// module ever emits (see `constants::abbrev_code`), never dynamically
/// deduplicated.
fn build_debug_abbrev() -> Vec<u8> {
	let mut sink = Vec::new();

	push_abbrev_decl(
		&mut sink,
		abbrev_code::COMPILE_UNIT,
		DW_TAG_COMPILE_UNIT,
		true,
		&[
			(DW_AT_PRODUCER, DW_FORM_STRP),
			(DW_AT_NAME, DW_FORM_STRP),
			(DW_AT_COMP_DIR, DW_FORM_STRP),
			(DW_AT_LOW_PC, DW_FORM_ADDR),
			// DW_AT_high_pc as DW_FORM_data4: a *size* (high_pc = low_pc +
			// this value), not an absolute address. Both are spec-legal —
			// DW_AT_high_pc's class is address-or-constant, and the reader
			// is supposed to branch on the attribute's form — but the
			// size-relative-to-low_pc encoding is the near-universal
			// real-world convention (what LLVM/GCC always emit), and at
			// least one real consumer (Chrome's C/C++ DWARF extension)
			// turned out not to handle the address-class alternative
			// correctly, silently rejecting the DIE.
			(DW_AT_HIGH_PC, DW_FORM_DATA4),
			(DW_AT_STMT_LIST, DW_FORM_SEC_OFFSET),
		],
	);
	push_abbrev_decl(
		&mut sink,
		abbrev_code::SUBPROGRAM,
		DW_TAG_SUBPROGRAM,
		true,
		&[
			(DW_AT_NAME, DW_FORM_STRP),
			(DW_AT_LOW_PC, DW_FORM_ADDR),
			(DW_AT_HIGH_PC, DW_FORM_DATA4),
		],
	);
	push_abbrev_decl(
		&mut sink,
		abbrev_code::FORMAL_PARAMETER,
		DW_TAG_FORMAL_PARAMETER,
		false,
		&[
			(DW_AT_NAME, DW_FORM_STRP),
			(DW_AT_TYPE, DW_FORM_REF4),
			(DW_AT_LOCATION, DW_FORM_EXPRLOC),
		],
	);
	push_abbrev_decl(
		&mut sink,
		abbrev_code::VARIABLE,
		DW_TAG_VARIABLE,
		false,
		&[
			(DW_AT_NAME, DW_FORM_STRP),
			(DW_AT_TYPE, DW_FORM_REF4),
			(DW_AT_LOCATION, DW_FORM_EXPRLOC),
		],
	);
	push_abbrev_decl(
		&mut sink,
		abbrev_code::BASE_TYPE,
		DW_TAG_BASE_TYPE,
		false,
		&[
			(DW_AT_NAME, DW_FORM_STRP),
			(DW_AT_ENCODING, DW_FORM_DATA1),
			(DW_AT_BYTE_SIZE, DW_FORM_DATA1),
		],
	);
	push_abbrev_decl(
		&mut sink,
		abbrev_code::POINTER_TYPE,
		DW_TAG_POINTER_TYPE,
		false,
		&[(DW_AT_TYPE, DW_FORM_REF4), (DW_AT_BYTE_SIZE, DW_FORM_DATA1)],
	);
	push_abbrev_decl(
		&mut sink,
		abbrev_code::STRUCTURE_TYPE,
		DW_TAG_STRUCTURE_TYPE,
		true,
		&[(DW_AT_NAME, DW_FORM_STRP), (DW_AT_BYTE_SIZE, DW_FORM_UDATA)],
	);
	push_abbrev_decl(
		&mut sink,
		abbrev_code::MEMBER,
		DW_TAG_MEMBER,
		false,
		&[
			(DW_AT_NAME, DW_FORM_STRP),
			(DW_AT_TYPE, DW_FORM_REF4),
			(DW_AT_DATA_MEMBER_LOCATION, DW_FORM_UDATA),
		],
	);

	push_uleb128(&mut sink, 0); // table terminator
	sink
}

/// Builds `.debug_info` (and, alongside it, `.debug_str`, since every name
/// referenced from `.debug_info` needs to be interned there as it's
/// written).
struct DebugInfoBuilder {
	sink: Vec<u8>,
	debug_str: StringTable,
	/// Base/pointer/function-reference type DIEs, deduplicated by
	/// `mir::Type` — safe because these carry no ambiguous names (see the
	/// module doc comment for why struct types can't use the same
	/// treatment).
	type_cache: HashMap<mir::Type, u32>,
}

impl DebugInfoBuilder {
	fn new() -> Self {
		DebugInfoBuilder {
			sink: Vec::new(),
			debug_str: StringTable::default(),
			type_cache: HashMap::new(),
		}
	}

	fn push_strp(&mut self, s: &str) {
		let offset = self.debug_str.intern(s);
		self.sink.extend_from_slice(&offset.to_le_bytes());
	}

	fn build(
		&mut self,
		function_debug_info: &[FunctionDebugInfo],
		mir: &mir::MIR,
		interner: &ast::StringInterner,
	) -> Vec<u8> {
		// `unit_length` (the CU's total byte size, excluding this field
		// itself) can only be known once everything after it has been
		// written — reserve it here and patch it in place at the end,
		// rather than building into a separate buffer first: everything
		// else in this builder already writes straight into `self.sink`.
		self.sink.extend_from_slice(&0u32.to_le_bytes());
		let unit_length_at = 0;
		let body_start = self.sink.len();

		self.sink.extend_from_slice(&5u16.to_le_bytes()); // version
		self.sink.push(DW_UT_COMPILE);
		self.sink.push(4); // address_size — matches wasm's u32 code offsets
		self.sink.extend_from_slice(&0u32.to_le_bytes()); // debug_abbrev_offset (single CU, always 0)

		let low_pc = function_debug_info
			.iter()
			.map(|f| f.start)
			.min()
			.unwrap_or(0);
		let high_pc =
			function_debug_info.iter().map(|f| f.end).max().unwrap_or(0);
		let cu_name = mir
			.functions
			.iter()
			.find_map(|f| f.name)
			.and_then(|s| interner.resolve(s))
			.unwrap_or("wx");

		push_uleb128(&mut self.sink, abbrev_code::COMPILE_UNIT);
		self.push_strp(concat!("wx ", env!("CARGO_PKG_VERSION")));
		self.push_strp(cu_name);
		self.push_strp(".");
		self.sink.extend_from_slice(&low_pc.to_le_bytes());
		self.sink
			.extend_from_slice(&(high_pc - low_pc).to_le_bytes());
		self.sink.extend_from_slice(&0u32.to_le_bytes()); // DW_AT_stmt_list: .debug_line has one CU, at offset 0

		// Phase 1: every local's type DIE, across every function — fully
		// written (and, for structs, closed) before any subprogram DIE
		// references them, so every DW_FORM_ref4 below is a completed,
		// known offset, never a forward reference needing a later patch.
		let local_types: Vec<Vec<u32>> = function_debug_info
			.iter()
			.map(|info| {
				info.locals
					.iter()
					.map(|local| self.build_local_type(local, mir, interner))
					.collect()
			})
			.collect();

		// Phase 2: subprogram DIEs, each with its own formal_parameter/
		// variable children (see the module doc comment for why there's no
		// lexical-block nesting).
		for (func, (info, types)) in mir
			.functions
			.iter()
			.zip(function_debug_info.iter().zip(&local_types))
		{
			self.build_subprogram(func, info, types, interner, mir);
		}

		push_uleb128(&mut self.sink, 0); // close compile_unit's children

		let unit_length = (self.sink.len() - body_start) as u32;
		self.sink[unit_length_at..unit_length_at + 4]
			.copy_from_slice(&unit_length.to_le_bytes());
		std::mem::take(&mut self.sink)
	}

	fn build_subprogram(
		&mut self,
		func: &mir::Function,
		info: &FunctionDebugInfo,
		local_type_offsets: &[u32],
		interner: &ast::StringInterner,
		mir: &mir::MIR,
	) {
		let name = func
			.name
			.and_then(|s| interner.resolve(s))
			.unwrap_or("$start");

		push_uleb128(&mut self.sink, abbrev_code::SUBPROGRAM);
		self.push_strp(name);
		self.sink.extend_from_slice(&info.start.to_le_bytes());
		self.sink
			.extend_from_slice(&(info.end - info.start).to_le_bytes());

		let params_count =
			mir.signatures[func.signature_index as usize].params_count;
		for (i, (local, &type_offset)) in
			info.locals.iter().zip(local_type_offsets).enumerate()
		{
			let leaf_count =
				wasm::flatten_type_to_scalars(local.ty, &mir.aggregates).len();
			if leaf_count == 0 {
				// Unit/Never-typed local: no meaningful location to
				// describe (shouldn't occur for a real source local, but
				// guard rather than emit a malformed empty exprloc).
				continue;
			}
			let abbrev = if i < params_count {
				abbrev_code::FORMAL_PARAMETER
			} else {
				abbrev_code::VARIABLE
			};
			push_uleb128(&mut self.sink, abbrev);
			let local_name = interner.resolve(local.name).unwrap_or("?");
			self.push_strp(local_name);
			self.sink.extend_from_slice(&type_offset.to_le_bytes());
			let expr = build_location_expr(local, &mir.aggregates);
			push_uleb128(&mut self.sink, expr.len() as u64);
			self.sink.extend_from_slice(&expr);
		}

		push_uleb128(&mut self.sink, 0); // close subprogram's children
	}

	fn build_local_type(
		&mut self,
		local: &wasm::LocalDebugInfo,
		mir: &mir::MIR,
		interner: &ast::StringInterner,
	) -> u32 {
		self.build_type(local.ty, local.struct_debug.as_ref(), mir, interner)
	}

	fn build_type(
		&mut self,
		ty: mir::Type,
		name_hint: Option<&mir::StructDebugInfo>,
		mir: &mir::MIR,
		interner: &ast::StringInterner,
	) -> u32 {
		match ty {
			mir::Type::Aggregate { aggregate_index } => {
				self.build_struct_die(aggregate_index, name_hint, mir, interner)
			}
			_ => self.build_scalar_type(ty),
		}
	}

	/// Base/pointer/function-reference types — deduplicated (see
	/// `type_cache`'s doc comment).
	fn build_scalar_type(&mut self, ty: mir::Type) -> u32 {
		if let Some(&offset) = self.type_cache.get(&ty) {
			return offset;
		}
		if let mir::Type::Pointer { kind, .. } = ty {
			// Resolve the pointee *before* capturing this DIE's own
			// offset below — same reasoning as `build_struct_die`: a
			// dependency built inline here would otherwise land its bytes
			// between `offset` and this DIE's own header, corrupting the
			// very offset this call is about to return. Pointee isn't
			// tracked at the MIR level for `Pointer`, so this points at a
			// generic byte-sized type rather than a precise pointee — a
			// stated simplification (module doc comment).
			let pointee = self.build_scalar_type(mir::Type::U8);
			let byte_size = kind.pointer_size() as u8;
			let offset = self.sink.len() as u32;
			push_uleb128(&mut self.sink, abbrev_code::POINTER_TYPE);
			self.sink.extend_from_slice(&pointee.to_le_bytes());
			self.sink.push(byte_size);
			self.type_cache.insert(ty, offset);
			return offset;
		}
		let (name, encoding, byte_size) = base_type_info(ty);
		let offset = self.sink.len() as u32;
		push_uleb128(&mut self.sink, abbrev_code::BASE_TYPE);
		self.push_strp(name);
		self.sink.push(encoding);
		self.sink.push(byte_size);
		self.type_cache.insert(ty, offset);
		offset
	}

	/// Always builds a fresh structure DIE — see the module doc comment for
	/// why struct types are never deduplicated by `AggregateIndex`.
	fn build_struct_die(
		&mut self,
		aggregate_index: mir::AggregateIndex,
		name_hint: Option<&mir::StructDebugInfo>,
		mir: &mir::MIR,
		interner: &ast::StringInterner,
	) -> u32 {
		let aggregate = &mir.aggregates[aggregate_index as usize];
		let struct_name = name_hint
			.and_then(|s| interner.resolve(s.name))
			.unwrap_or("tuple")
			.to_string();
		let byte_size = aggregate.layout.size;

		// Build every member's type DIE first (recursing one level with no
		// further name hint — see the module doc comment), so this
		// struct's own bytes (written below) never end up straddling a
		// nested type DIE's bytes.
		let members: Vec<(String, u32, u32)> = (0..aggregate.values.len())
			.map(|i| {
				let field_name = name_hint
					.and_then(|s| s.field_names.get(i))
					.and_then(|&sym| interner.resolve(sym))
					.map(str::to_string)
					.unwrap_or_else(|| format!("field{i}"));
				let field_type =
					self.build_type(aggregate.values[i], None, mir, interner);
				(field_name, field_type, aggregate.offsets[i])
			})
			.collect();

		let struct_offset = self.sink.len() as u32;
		push_uleb128(&mut self.sink, abbrev_code::STRUCTURE_TYPE);
		self.push_strp(&struct_name);
		push_uleb128(&mut self.sink, byte_size as u64);

		for (field_name, field_type, field_offset) in &members {
			push_uleb128(&mut self.sink, abbrev_code::MEMBER);
			self.push_strp(field_name);
			self.sink.extend_from_slice(&field_type.to_le_bytes());
			push_uleb128(&mut self.sink, *field_offset as u64);
		}
		push_uleb128(&mut self.sink, 0); // close structure_type's children

		struct_offset
	}
}

fn base_type_info(ty: mir::Type) -> (&'static str, u8, u8) {
	match ty {
		mir::Type::I8 => ("i8", DW_ATE_SIGNED, 1),
		mir::Type::U8 => ("u8", DW_ATE_UNSIGNED, 1),
		mir::Type::I16 => ("i16", DW_ATE_SIGNED, 2),
		mir::Type::U16 => ("u16", DW_ATE_UNSIGNED, 2),
		mir::Type::I32 => ("i32", DW_ATE_SIGNED, 4),
		mir::Type::U32 => ("u32", DW_ATE_UNSIGNED, 4),
		mir::Type::I64 => ("i64", DW_ATE_SIGNED, 8),
		mir::Type::U64 => ("u64", DW_ATE_UNSIGNED, 8),
		mir::Type::F32 => ("f32", DW_ATE_FLOAT, 4),
		mir::Type::F64 => ("f64", DW_ATE_FLOAT, 8),
		// Matches the actual wasm i32 storage width a bool local occupies,
		// not the 1-byte logical size — see the module doc comment.
		mir::Type::Bool => ("bool", DW_ATE_BOOLEAN, 4),
		mir::Type::Function { .. } => ("function", DW_ATE_UNSIGNED, 4),
		mir::Type::Pointer { .. }
		| mir::Type::Aggregate { .. }
		| mir::Type::Unit
		| mir::Type::Never => {
			unreachable!("base_type_info called on a non-scalar mir::Type")
		}
	}
}

fn scalar_byte_size(ty: wasm::ScalarType) -> u64 {
	match ty {
		wasm::ScalarType::I32 | wasm::ScalarType::F32 => 4,
		wasm::ScalarType::I64 | wasm::ScalarType::F64 => 8,
	}
}

/// Builds a `DW_AT_location` expression for one local: a single
/// `DW_OP_WASM_location` for a scalar, or a chained
/// `DW_OP_WASM_location`+`DW_OP_piece` pair per flattened leaf field for an
/// aggregate — see the module doc comment.
///
/// Each `DW_OP_WASM_location` is followed by `DW_OP_stack_value`: without
/// it, a consumer must treat the wasm-local reference as an *address* to
/// dereference (standard DWARF location-expression default) rather than the
/// value itself — real producers (LLVM's wasm backend) always emit this
/// pairing. Confirmed the hard way: wasmtime's own DWARF→native transform
/// (`crates/cranelift/src/debug/transform/expression.rs`) sets
/// `need_deref = true` unconditionally per operation and only clears it on
/// `DW_OP_stack_value`, so a bare `DW_OP_WASM_location` sent it down the
/// memory-dereference path — which then hard-errored on modules with no
/// declared linear memory (`ModuleMemoryOffset::None`).
fn build_location_expr(
	local: &wasm::LocalDebugInfo,
	aggregates: &[mir::Aggregate],
) -> Vec<u8> {
	let leaves = wasm::flatten_type_to_scalars(local.ty, aggregates);
	let mut expr = Vec::new();
	if leaves.len() == 1 {
		expr.push(DW_OP_WASM_LOCATION);
		expr.push(WASM_LOCATION_LOCAL);
		push_uleb128(&mut expr, local.wasm_local_start as u64);
		expr.push(DW_OP_STACK_VALUE);
	} else {
		for (i, &leaf) in leaves.iter().enumerate() {
			expr.push(DW_OP_WASM_LOCATION);
			expr.push(WASM_LOCATION_LOCAL);
			push_uleb128(&mut expr, (local.wasm_local_start + i as u32) as u64);
			expr.push(DW_OP_STACK_VALUE);
			expr.push(DW_OP_PIECE);
			push_uleb128(&mut expr, scalar_byte_size(leaf));
		}
	}
	expr
}

/// Builds `.debug_line` (and, alongside it, `.debug_line_str`).
struct LineProgramBuilder {
	debug_line_str: StringTable,
	file_index: HashMap<vfs::FileId, u32>,
	file_names: Vec<(u32, u32)>, // (path line_strp offset, directory_index)
}

impl LineProgramBuilder {
	fn new() -> Self {
		LineProgramBuilder {
			debug_line_str: StringTable::default(),
			file_index: HashMap::new(),
			file_names: Vec::new(),
		}
	}

	fn file_index_for(
		&mut self,
		file_id: vfs::FileId,
		files: &vfs::Files,
	) -> u32 {
		if let Some(&index) = self.file_index.get(&file_id) {
			return index;
		}
		use codespan_reporting::files::Files as _;
		let name = files.name(file_id).unwrap_or("<unknown>");
		let path_offset = self.debug_line_str.intern(name);
		let index = self.file_names.len() as u32;
		self.file_names.push((path_offset, 0));
		self.file_index.insert(file_id, index);
		index
	}

	fn build(
		&mut self,
		debug_spans: &[DebugSpan],
		function_debug_info: &[FunctionDebugInfo],
		files: &vfs::Files,
	) -> Vec<u8> {
		// Assign file indices (and intern their names) before building any
		// row, since row emission just references indices by number.
		for span in debug_spans {
			self.file_index_for(span.file_id, files);
		}
		// A single shared directory (index 0, ".") — every file's own name
		// is used as-is, so there's no real directory/filename split to
		// model here. Deliberately not an empty string: legal per raw
		// DWARF, but real consumers assume non-empty (e.g. wasmtime's own
		// `gimli::write`-based DWARF transform panics on it —
		// `assert!(!val.is_empty())` in `gimli::write::line`).
		let directory_offset = self.debug_line_str.intern(".");

		let program =
			self.build_program(debug_spans, function_debug_info, files);
		let header_content = self.build_header_content(directory_offset);

		let mut body = Vec::new();
		body.extend_from_slice(&5u16.to_le_bytes()); // version
		body.push(4); // address_size
		body.push(0); // segment_selector_size
		body.extend_from_slice(&(header_content.len() as u32).to_le_bytes());
		body.extend_from_slice(&header_content);
		body.extend_from_slice(&program);

		let mut sink = Vec::new();
		sink.extend_from_slice(&(body.len() as u32).to_le_bytes());
		sink.extend_from_slice(&body);
		sink
	}

	/// Everything from `minimum_instruction_length` through the file-name
	/// table — the part `header_length` itself measures.
	fn build_header_content(&mut self, directory_offset: u32) -> Vec<u8> {
		let mut h = Vec::new();
		h.push(1); // minimum_instruction_length: every wasm byte is addressable
		h.push(1); // maximum_operations_per_instruction: non-VLIW
		h.push(1); // default_is_stmt: true
		h.push((-5i8) as u8); // line_base
		h.push(14); // line_range
		h.push(13); // opcode_base: standard opcodes 1..=12
		// standard_opcode_lengths[opcode - 1], opcodes 1..=12 — required
		// even though only a subset is ever emitted, so a reader that
		// doesn't implement every standard opcode can still skip unknown
		// ones by their declared operand count.
		h.extend_from_slice(&[0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);

		// directory_entry_format: one (DW_LNCT_path, DW_FORM_line_strp) pair.
		h.push(1);
		push_uleb128(&mut h, DW_LNCT_PATH);
		push_uleb128(&mut h, DW_FORM_LINE_STRP);
		push_uleb128(&mut h, 1); // directories_count
		h.extend_from_slice(&directory_offset.to_le_bytes());

		// file_name_entry_format: (path, line_strp) + (directory_index, udata).
		h.push(2);
		push_uleb128(&mut h, DW_LNCT_PATH);
		push_uleb128(&mut h, DW_FORM_LINE_STRP);
		push_uleb128(&mut h, DW_LNCT_DIRECTORY_INDEX);
		push_uleb128(&mut h, DW_FORM_UDATA);
		push_uleb128(&mut h, self.file_names.len() as u64);
		for &(path_offset, dir_index) in &self.file_names {
			h.extend_from_slice(&path_offset.to_le_bytes());
			push_uleb128(&mut h, dir_index as u64);
		}

		h
	}

	/// The actual line-number program: one sequence per function that has
	/// any spans, terminated by `DW_LNE_end_sequence`. Functions are
	/// matched to their spans by absolute offset range (`DebugSpan`s are
	/// globally sorted ascending — see `codegen::WasmModule::
	/// encode_with_debug_spans` — and `FunctionDebugInfo` ranges are
	/// non-overlapping and in the same order), not by an explicit
	/// per-span function index.
	fn build_program(
		&mut self,
		debug_spans: &[DebugSpan],
		function_debug_info: &[FunctionDebugInfo],
		files: &vfs::Files,
	) -> Vec<u8> {
		let mut program = Vec::new();
		let mut cursor = 0;
		for info in function_debug_info {
			let start = cursor;
			while cursor < debug_spans.len()
				&& debug_spans[cursor].offset < info.end
			{
				cursor += 1;
			}
			let spans = &debug_spans[start..cursor];
			if !spans.is_empty() {
				self.emit_sequence(&mut program, spans, info, files);
			}
		}
		program
	}

	fn emit_sequence(
		&mut self,
		program: &mut Vec<u8>,
		spans: &[DebugSpan],
		info: &FunctionDebugInfo,
		files: &vfs::Files,
	) {
		use codespan_reporting::files::Files as _;

		program.push(0x00); // extended opcode escape
		push_uleb128(program, 1 + 4); // length: sub-opcode + 4-byte address
		program.push(DW_LNE_SET_ADDRESS);
		program.extend_from_slice(&spans[0].offset.to_le_bytes());

		let mut address = spans[0].offset;
		let mut file = None;
		let mut line: i64 = 1;
		let mut column = 0u64;

		for span in spans {
			if span.offset != address {
				program.push(DW_LNS_ADVANCE_PC);
				push_uleb128(program, (span.offset - address) as u64);
				address = span.offset;
			}
			let file_index = self.file_index_for(span.file_id, files);
			if file != Some(file_index) {
				program.push(DW_LNS_SET_FILE);
				push_uleb128(program, file_index as u64);
				file = Some(file_index);
			}
			let location = files
				.location(span.file_id, span.span.start as usize)
				.expect("debug span's start offset is within its file");
			// Both already 1-indexed, matching DWARF's line/column register
			// convention directly (column 0 is reserved as a "left edge of
			// the line" sentinel, unlike source maps' 0-indexed columns).
			let span_line = location.line_number as i64;
			let span_column = location.column_number as u64;
			if span_line != line {
				program.push(DW_LNS_ADVANCE_LINE);
				push_sleb128(program, span_line - line);
				line = span_line;
			}
			if span_column != column {
				program.push(DW_LNS_SET_COLUMN);
				push_uleb128(program, span_column);
				column = span_column;
			}
			program.push(DW_LNS_COPY);
		}

		if info.end != address {
			program.push(DW_LNS_ADVANCE_PC);
			push_uleb128(program, (info.end - address) as u64);
		}
		program.push(0x00);
		push_uleb128(program, 1);
		program.push(DW_LNE_END_SEQUENCE);
	}
}
