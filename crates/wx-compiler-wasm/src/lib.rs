use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use serde::Serialize;
use serde_wasm_bindgen::Serializer;
use wasm_bindgen::prelude::*;
use wx_compiler::*;

#[wasm_bindgen]
extern "C" {
	#[wasm_bindgen(typescript_type = "Record<string, string>")]
	pub type FileMap;

	#[wasm_bindgen(typescript_type = "CompilationResult")]
	pub type CompilationResultJs;
}

#[wasm_bindgen(typescript_custom_section)]
const COMPILATION_RESULT_TS: &'static str = r#"
export type Severity = "Bug" | "Error" | "Warning" | "Note" | "Help";
export type LabelStyle = "Primary" | "Secondary";

export interface DiagnosticLabel {
	style: LabelStyle;
	file_id: number;
	range: { start: number; end: number };
	message: string;
}

export interface Diagnostic {
	severity: Severity;
	code: string | null;
	message: string;
	labels: DiagnosticLabel[];
	notes: string[];
}

export interface CompilationResult {
	diagnostics: Diagnostic[];
	bytecode: Uint8Array<ArrayBuffer> | null;
}
"#;

/// The outcome of a compilation attempt that got far enough to produce
/// diagnostics or bytecode. Genuine usage errors (a malformed `files` map,
/// or an `entry_path` missing from it) instead surface through the
/// `Err(String)` case of `compile`'s return type.
#[derive(serde::Serialize)]
struct CompilationResult {
	diagnostics: Vec<Diagnostic<vfs::FileId>>,
	#[serde(with = "serde_bytes")]
	bytecode: Option<Vec<u8>>,
}

impl CompilationResult {
	fn into_js(self) -> CompilationResultJs {
		let serializer = Serializer::new().serialize_missing_as_null(true);
		let value = self
			.serialize(&serializer)
			.expect("CompilationResult always serializes");
		value.into()
	}
}

#[wasm_bindgen]
pub fn compile(
	entry_path: String,
	files: FileMap,
) -> Result<CompilationResultJs, String> {
	let files: HashMap<String, String> =
		serde_wasm_bindgen::from_value(files.into())
			.map_err(|err| err.to_string())?;
	// Callers are responsible for providing absolute (`/`-rooted) paths,
	// same as every other `FileSource` consumer.
	let files: HashMap<vfs::AbsolutePath, String> = files
		.into_iter()
		.map(|(path, source)| (vfs::AbsolutePath::new(path), source))
		.collect();

	let mut builder = vfs::CompilationUnitBuilder::new();
	builder.load_stdlib();
	let root_id = builder
		.load_binary(
			vfs::AbsolutePath::new(entry_path),
			&vfs::VirtualFileSource::new(files),
		)
		.map_err(|_| "entry file not found among `files`".to_string())?;
	let mut compilation = builder.build(root_id);

	let pre_tir_diagnostics: Vec<_> = compilation
		.packages
		.iter()
		.flat_map(|package_graph| {
			package_graph.linker_diagnostics.iter().cloned().chain(
				package_graph
					.modules
					.iter()
					.flat_map(|module| module.ast.diagnostics.iter().cloned()),
			)
		})
		.collect();
	if !pre_tir_diagnostics.is_empty() {
		return Ok(CompilationResult {
			diagnostics: pre_tir_diagnostics,
			bytecode: None,
		}
		.into_js());
	}

	let hir = tir::TIR::build(&mut compilation);
	if !hir.diagnostics.is_empty() {
		return Ok(CompilationResult {
			diagnostics: hir.diagnostics,
			bytecode: None,
		}
		.into_js());
	}

	let mir =
		mir::MIR::build(&hir, &compilation.interner, compilation.id_generator);
	let module = codegen::Builder::build(&mir, &compilation.interner)
		.map_err(|_| "codegen failed".to_string())?;
	let bytecode = module.encode();

	Ok(CompilationResult {
		diagnostics: Vec::new(),
		bytecode: Some(bytecode),
	}
	.into_js())
}
