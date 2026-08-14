use std::collections::HashMap;

use gimli::{EndianSlice, LittleEndian, Reader as _};
use indoc::indoc;

use super::*;
use crate::{codegen, mir, tir};

/// Compiles `source` in `--debug` mode through the full pipeline and
/// returns everything needed to build (and then parse back) its DWARF
/// sections.
#[allow(unused)]
struct DebugBuild {
	graph: vfs::CompilationGraph,
	mir: mir::MIR,
	bytecode: Vec<u8>,
	debug_spans: Vec<DebugSpan>,
	function_debug_info: Vec<FunctionDebugInfo>,
}

impl DebugBuild {
	fn new(source: &str) -> Self {
		let mut builder = vfs::CompilationGraphBuilder::new();
		let stdlib_id = builder.load_stdlib();
		let prefixed = format!("use std::*;\n{source}");
		let root_id = builder
			.load_binary(
				"main.wx".to_string(),
				&vfs::VirtualFileSource::new(HashMap::from([(
					"main.wx".to_string(),
					prefixed,
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id, stdlib_id);
		let tir = tir::TIR::build(&mut graph);
		assert!(
			tir.diagnostics.is_empty(),
			"unexpected diagnostics: {:?}",
			tir.diagnostics
		);
		let mut mir = mir::MIR::build(
			&tir,
			&graph.interner,
			graph.id_generator,
			crate::CompilationMode::Debug,
		);
		let call_graph = mir::CallGraph::build(&mir.functions, &mir.call_edges);
		mir.dead_code_eliminate(&call_graph);
		let wasm = codegen::Builder::build(
			&mir,
			&graph.interner,
			crate::CompilationMode::Debug,
		)
		.unwrap();
		let (bytecode, debug_spans, function_debug_info) =
			wasm.encode_with_debug_spans();

		DebugBuild {
			graph,
			mir,
			bytecode,
			debug_spans,
			function_debug_info,
		}
	}

	fn sections(&self) -> Sections {
		build(
			&self.debug_spans,
			&self.function_debug_info,
			&self.mir,
			&self.graph.interner,
			&self.graph.files,
		)
	}
}

/// Loads a `gimli::Dwarf` view directly over `Sections`' byte buffers — no
/// object-file container involved, matching how `codegen`'s own tests
/// operate on raw wasm bytes rather than a `.wasm` file on disk.
fn load_dwarf(
	sections: &Sections,
) -> gimli::Dwarf<EndianSlice<'_, LittleEndian>> {
	gimli::Dwarf::load(|id| -> Result<_, gimli::Error> {
		let data: &[u8] = match id {
			gimli::SectionId::DebugAbbrev => &sections.debug_abbrev,
			gimli::SectionId::DebugInfo => &sections.debug_info,
			gimli::SectionId::DebugLine => &sections.debug_line,
			gimli::SectionId::DebugStr => &sections.debug_str,
			gimli::SectionId::DebugLineStr => &sections.debug_line_str,
			gimli::SectionId::DebugAranges => &sections.debug_aranges,
			_ => &[],
		};
		Ok(EndianSlice::new(data, LittleEndian))
	})
	.unwrap()
}

/// Decodes a `DW_OP_WASM_location 0x00 <index> DW_OP_stack_value`
/// expression's wasm-local index — independent of the encoder (manual byte
/// parsing), so this exercises the real wire format rather than checking
/// the encoder against itself. Panics if `expr` isn't exactly that
/// one-operation shape. The trailing `DW_OP_stack_value` is required for
/// real consumers (see `build_location_expr`'s doc comment) — without it, a
/// wasm-local reference is (mis)read as an address to dereference.
fn wasm_local_index(expr: &[u8]) -> u32 {
	assert_eq!(expr[0], DW_OP_WASM_LOCATION);
	assert_eq!(expr[1], WASM_LOCATION_LOCAL);
	let (index, index_len) = decode_uleb128(&expr[2..]);
	assert_eq!(expr[2 + index_len], DW_OP_STACK_VALUE);
	assert_eq!(expr.len(), 2 + index_len + 1);
	index
}

/// Decodes a chain of `(DW_OP_WASM_location 0x00 <index> DW_OP_stack_value,
/// DW_OP_piece <size>)` pairs into `(index, size)` tuples.
fn wasm_pieces(expr: &[u8]) -> Vec<(u32, u32)> {
	let mut out = Vec::new();
	let mut pos = 0;
	while pos < expr.len() {
		assert_eq!(expr[pos], DW_OP_WASM_LOCATION);
		assert_eq!(expr[pos + 1], WASM_LOCATION_LOCAL);
		let (index, index_len) = decode_uleb128(&expr[pos + 2..]);
		pos += 2 + index_len;
		assert_eq!(expr[pos], DW_OP_STACK_VALUE);
		pos += 1;
		assert_eq!(expr[pos], DW_OP_PIECE);
		let (size, size_len) = decode_uleb128(&expr[pos + 1..]);
		pos += 1 + size_len;
		out.push((index, size));
	}
	out
}

#[test]
fn custom_section_has_wasm_custom_section_shape() {
	let bytes = custom_section(".debug_info", &[1, 2, 3]);

	assert_eq!(bytes[0], 0x00); // wasm SectionId::Custom
	let (section_len, len_bytes) = decode_uleb128(&bytes[1..]);
	assert_eq!(1 + len_bytes + section_len as usize, bytes.len());

	let mut pos = 1 + len_bytes;
	let (name_len, extra) = decode_uleb128(&bytes[pos..]);
	pos += extra;
	assert_eq!(name_len, ".debug_info".len() as u32);
	assert_eq!(&bytes[pos..pos + name_len as usize], b".debug_info");
	pos += name_len as usize;

	assert_eq!(&bytes[pos..], &[1, 2, 3]);
}

/// Plain unsigned LEB128, decoded byte-by-byte — independent of
/// `push_uleb128`, matching the round-trip philosophy used throughout this
/// module's tests.
fn decode_uleb128(bytes: &[u8]) -> (u32, usize) {
	let mut result = 0u32;
	let mut shift = 0;
	let mut pos = 0;
	loop {
		let byte = bytes[pos];
		result |= ((byte & 0x7F) as u32) << shift;
		pos += 1;
		if byte & 0x80 == 0 {
			break;
		}
		shift += 7;
	}
	(result, pos)
}

#[test]
fn scalar_function_produces_valid_dwarf5_compile_unit_and_subprogram() {
	let build = DebugBuild::new(indoc! {"
        fn compute(x: i32) -> i32 {
            local y = x + 1;
            y * 2
        }
        export { compute }
    "});
	let sections = build.sections();
	let dwarf = load_dwarf(&sections);

	let header = dwarf.units().next().unwrap().unwrap();
	assert_eq!(header.version(), 5);
	assert_eq!(header.address_size(), 4);

	let unit = dwarf.unit(header).unwrap();
	let mut cursor = unit.entries();

	// compile_unit
	let root = cursor.next_dfs().unwrap().unwrap();
	assert_eq!(root.tag(), gimli::DW_TAG_compile_unit);

	// Every local's type DIE is emitted as a compile_unit child *before*
	// any subprogram DIE (see the module doc comment on Phase 1/Phase 2),
	// so skip forward past those rather than assuming the subprogram comes
	// immediately after compile_unit.
	let subprogram = loop {
		let entry = cursor.next_dfs().unwrap().unwrap();
		if entry.tag() == gimli::DW_TAG_subprogram {
			break entry.clone();
		}
	};
	let name = dwarf
		.attr_string(&unit, subprogram.attr_value(gimli::DW_AT_name).unwrap())
		.unwrap();
	assert_eq!(name.to_string_lossy(), "compute");

	let expected_info = &build.function_debug_info[0];
	let gimli::AttributeValue::Addr(low_pc) =
		subprogram.attr_value(gimli::DW_AT_low_pc).unwrap()
	else {
		panic!("expected Addr");
	};
	// DW_AT_high_pc is encoded as a size relative to low_pc (DW_FORM_data4),
	// not an absolute address — see `DebugInfoBuilder::build_subprogram`.
	let high_pc_size = subprogram
		.attr_value(gimli::DW_AT_high_pc)
		.unwrap()
		.udata_value()
		.unwrap();
	assert_eq!(
		(low_pc as u32, low_pc as u32 + high_pc_size as u32),
		(expected_info.start, expected_info.end)
	);

	// formal_parameter `x`, wasm local 0
	let param = cursor.next_dfs().unwrap().unwrap();
	assert_eq!(param.tag(), gimli::DW_TAG_formal_parameter);
	let param_name = dwarf
		.attr_string(&unit, param.attr_value(gimli::DW_AT_name).unwrap())
		.unwrap();
	assert_eq!(param_name.to_string_lossy(), "x");
	let param_loc = param.attr_value(gimli::DW_AT_location).unwrap();
	let gimli::AttributeValue::Exprloc(expr) = param_loc else {
		panic!("expected Exprloc");
	};
	assert_eq!(
		wasm_local_index(&expr.0.to_slice().unwrap()),
		expected_info.locals[0].wasm_local_start
	);

	// variable `y`, its own wasm local
	let var = cursor.next_dfs().unwrap().unwrap();
	assert_eq!(var.tag(), gimli::DW_TAG_variable);
	let var_name = dwarf
		.attr_string(&unit, var.attr_value(gimli::DW_AT_name).unwrap())
		.unwrap();
	assert_eq!(var_name.to_string_lossy(), "y");
	let var_loc = var.attr_value(gimli::DW_AT_location).unwrap();
	let gimli::AttributeValue::Exprloc(expr) = var_loc else {
		panic!("expected Exprloc");
	};
	assert_eq!(
		wasm_local_index(&expr.0.to_slice().unwrap()),
		expected_info.locals[1].wasm_local_start
	);
}

#[test]
fn line_program_rows_match_debug_spans() {
	let build = DebugBuild::new(indoc! {"
        fn compute(x: i32) -> i32 {
            local y = x + 1;
            y * 2
        }
        export { compute }
    "});
	let sections = build.sections();
	let dwarf = load_dwarf(&sections);

	let header = dwarf.units().next().unwrap().unwrap();
	let unit = dwarf.unit(header).unwrap();
	let program = unit.line_program.clone().unwrap();
	let mut rows = program.rows();

	let mut actual: Vec<(u32, u64, u64)> = Vec::new();
	while let Some((_, row)) = rows.next_row().unwrap() {
		if row.end_sequence() {
			continue;
		}
		let column = match row.column() {
			gimli::ColumnType::LeftEdge => 0,
			gimli::ColumnType::Column(n) => n.get(),
		};
		actual.push((row.address() as u32, row.line().unwrap().get(), column));
	}

	use codespan_reporting::files::Files as _;
	let expected: Vec<(u32, u64, u64)> = build
		.debug_spans
		.iter()
		.map(|d| {
			let location = build
				.graph
				.files
				.location(d.file_id, d.span.start as usize)
				.unwrap();
			(
				d.offset,
				location.line_number as u64,
				location.column_number as u64,
			)
		})
		.collect();

	assert_eq!(actual, expected);
}

#[test]
fn struct_local_uses_dw_op_piece_and_real_field_names() {
	let build = DebugBuild::new(indoc! {"
        struct Vec2 { x: i32, y: i32 }
        fn compute() -> i32 {
            local v: Vec2 = Vec2::{ x: 1, y: 2 };
            v.x + v.y
        }
        export { compute }
    "});
	let sections = build.sections();
	let dwarf = load_dwarf(&sections);

	let header = dwarf.units().next().unwrap().unwrap();
	let unit = dwarf.unit(header).unwrap();
	let mut cursor = unit.entries();

	// Find the `variable` DIE for `v` and, separately, the structure_type
	// DIE it points at.
	let mut var_entry = None;
	let mut struct_offset = None;
	while let Some(entry) = cursor.next_dfs().unwrap() {
		if entry.tag() == gimli::DW_TAG_variable {
			let name = dwarf
				.attr_string(
					&unit,
					entry.attr_value(gimli::DW_AT_name).unwrap(),
				)
				.unwrap();
			if name.to_string_lossy() == "v" {
				let gimli::AttributeValue::UnitRef(offset) =
					entry.attr_value(gimli::DW_AT_type).unwrap()
				else {
					panic!("expected UnitRef");
				};
				struct_offset = Some(offset);
				var_entry = Some(entry.clone());
			}
		}
	}
	let var_entry = var_entry.expect("variable `v` not found");
	let struct_offset = struct_offset.expect("`v` has no type reference");

	// The struct type itself: name "Vec2", byte_size 8, two members with
	// real field names in physical order.
	let struct_die = unit.entry(struct_offset).unwrap();
	assert_eq!(struct_die.tag(), gimli::DW_TAG_structure_type);
	let struct_name = dwarf
		.attr_string(&unit, struct_die.attr_value(gimli::DW_AT_name).unwrap())
		.unwrap();
	assert_eq!(struct_name.to_string_lossy(), "Vec2");
	assert_eq!(
		struct_die
			.attr_value(gimli::DW_AT_byte_size)
			.unwrap()
			.udata_value()
			.unwrap(),
		8
	);

	let mut tree = unit.entries_tree(Some(struct_offset)).unwrap();
	let root = tree.root().unwrap();
	let mut children = root.children();
	let mut members = Vec::new();
	while let Some(node) = children.next().unwrap() {
		let entry = node.entry();
		assert_eq!(entry.tag(), gimli::DW_TAG_member);
		let name = dwarf
			.attr_string(&unit, entry.attr_value(gimli::DW_AT_name).unwrap())
			.unwrap();
		let offset = entry
			.attr_value(gimli::DW_AT_data_member_location)
			.unwrap()
			.udata_value()
			.unwrap();
		members.push((name.to_string_lossy().into_owned(), offset));
	}
	assert_eq!(members, vec![("x".to_string(), 0), ("y".to_string(), 4)]);

	// `v`'s own location: two DW_OP_WASM_location+DW_OP_piece pairs, 4
	// bytes each, one per flattened field.
	let loc = var_entry.attr_value(gimli::DW_AT_location).unwrap();
	let gimli::AttributeValue::Exprloc(expr) = loc else {
		panic!("expected Exprloc");
	};
	let pieces = wasm_pieces(&expr.0.to_slice().unwrap());
	assert_eq!(pieces.len(), 2);
	assert_eq!(pieces[0].1, 4);
	assert_eq!(pieces[1].1, 4);
	assert_eq!(pieces[1].0, pieces[0].0 + 1); // consecutive wasm locals
}

#[test]
fn debug_aranges_covers_every_function_debug_info_range() {
	let build = DebugBuild::new(indoc! {"
        fn compute(x: i32) -> i32 {
            local y = x + 1;
            y * 2
        }
        export { compute }
    "});
	let sections = build.sections();

	let debug_aranges =
		gimli::DebugAranges::new(&sections.debug_aranges, LittleEndian);
	let mut headers = debug_aranges.headers();
	let header = headers.next().unwrap().expect("one arange header");
	assert!(headers.next().unwrap().is_none(), "only one compile unit");
	// Points at our one compile unit, which starts at offset 0.
	assert_eq!(header.debug_info_offset().0, 0);

	let mut entries = header.entries();
	let entry = entries.next().unwrap().expect("one address range");
	assert!(entries.next().unwrap().is_none(), "only one range emitted");

	let expected_low = build
		.function_debug_info
		.iter()
		.map(|f| f.start)
		.min()
		.unwrap();
	let expected_high = build
		.function_debug_info
		.iter()
		.map(|f| f.end)
		.max()
		.unwrap();
	assert_eq!(entry.address() as u32, expected_low);
	assert_eq!(entry.length() as u32, expected_high - expected_low);
}

/// Regression test for a real bug this module used to have: every
/// `DW_OP_WASM_location` must be followed by `DW_OP_stack_value` (see
/// `build_location_expr`'s doc comment) — without it, wasmtime's own
/// DWARF→native transform (`crates/cranelift/src/debug/transform/
/// expression.rs`) treats the wasm-local reference as an *address* that
/// needs dereferencing through the module's linear memory, and hard-errors
/// with gimli's `Error::InvalidAttributeValue` ("The attribute value is an
/// invalid for writing") on any module with zero declared memories
/// (`ModuleMemoryOffset::None`). This module deliberately has no `memory`
/// declaration, to pin the fix rather than accidentally re-passing via the
/// workaround of declaring one.
#[test]
fn wasmtime_accepts_our_debug_info_for_a_module_with_no_memory() {
	let build = DebugBuild::new(indoc! {"
        fn add(a: i32, b: i32) -> i32 {
            local sum = a + b;
            sum
        }

        fn compute(n: i32) -> i32 {
            local mut total: i32 = 0;
            local mut i: i32 = 0;
            loop {
                if i >= n { break };
                total = add(total, i);
                i += 1;
            }
            total
        }

        export { compute }
    "});
	let sections = build.sections();
	let mut bytecode = build.bytecode.clone();
	for (name, payload) in [
		(".debug_abbrev", &sections.debug_abbrev),
		(".debug_info", &sections.debug_info),
		(".debug_line", &sections.debug_line),
		(".debug_str", &sections.debug_str),
		(".debug_line_str", &sections.debug_line_str),
		(".debug_aranges", &sections.debug_aranges),
	] {
		bytecode.extend_from_slice(&custom_section(name, payload));
	}

	let mut config = wasmtime::Config::new();
	config.debug_info(true);
	let engine = wasmtime::Engine::new(&config).unwrap();
	let module = wasmtime::Module::new(&engine, &bytecode).unwrap();
	let mut store = wasmtime::Store::new(&engine, ());
	let instance =
		wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
	let compute = instance
		.get_typed_func::<i32, i32>(&mut store, "compute")
		.unwrap();
	let result = compute.call(&mut store, 5).unwrap();
	assert_eq!(result, 10);
}

/// Independent, real-world verification beyond this module's own tests:
/// `addr2line` (same `gimli-rs` org as `gimli` itself, the standard Rust
/// tool for "what function/file/line is this address in") performs exactly
/// the address→function resolution that Chrome's DWARF extension was
/// observed failing at in manual browser testing — this gives a fast,
/// scriptable way to check that resolution independently of a browser.
#[test]
fn addr2line_resolves_function_and_location_for_a_mid_function_pc() {
	let build = DebugBuild::new(indoc! {"
        fn compute(x: i32) -> i32 {
            local y = x + 1;
            y * 2
        }
        export { compute }
    "});
	let sections = build.sections();
	let dwarf = load_dwarf(&sections);
	let context = addr2line::Context::from_dwarf(dwarf).unwrap();

	// Probe a PC in the middle of the function, not just its first
	// instruction — mirrors "paused mid-function", the exact scenario
	// Chrome's extension failed to resolve to a function.
	let info = &build.function_debug_info[0];
	let probe = info.start + (info.end - info.start) / 2;

	let mut frames =
		context.find_frames(probe as u64).skip_all_loads().unwrap();
	let frame = frames
		.next()
		.unwrap()
		.expect("addr2line found no frame for this pc");

	let function = frame.function.unwrap();
	assert_eq!(function.raw_name().unwrap(), "compute");

	let location = frame.location.expect("addr2line found no source location");
	// "./main.wx", not "main.wx": addr2line joins our (empty, by design —
	// see `LineProgramBuilder::build`) directory entry with the file name,
	// normalizing an empty directory to "." — not a bug in our encoder.
	assert_eq!(location.file, Some("./main.wx"));
	assert!(location.line.is_some());
}
