use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;
use serde::Serialize;
use serde_wasm_bindgen::Serializer;
use wasm_bindgen::prelude::*;
use wx_compiler::diagnostics::Diagnostics;
use wx_compiler::*;

#[wasm_bindgen]
extern "C" {
	#[wasm_bindgen(typescript_type = "Record<string, string>")]
	pub type FileMap;

	#[wasm_bindgen(typescript_type = "CompilationResult")]
	pub type CompilationResultJs;
}

#[wasm_bindgen(typescript_custom_section)]
const COMPILATION_RESULT_TS: &str = r#"
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

/// Source errors are returned as diagnostics; invalid JS input, missing entry
/// files/manifests, and backend failures throw a JS exception.
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

/// Paths are rooted in a synthetic `/` filesystem, never the host filesystem.
/// Accept both playground-relative and absolute paths at the JS boundary.
fn virtual_path(path: String) -> vfs::AbsolutePath {
	let path = path.replace('\\', "/");
	vfs::AbsolutePath::new("/")
		.join(&vfs::RelativePath::new(path.trim_start_matches('/')))
}

fn file_source(files: FileMap) -> Result<vfs::VirtualFileSource, String> {
	let files: HashMap<String, String> =
		serde_wasm_bindgen::from_value(files.into())
			.map_err(|err| err.to_string())?;
	let mut normalized = HashMap::with_capacity(files.len());
	for (path, source) in files {
		let path = virtual_path(path);
		if normalized.insert(path.clone(), source).is_some() {
			return Err(format!("duplicate virtual file: `{path}`"));
		}
	}
	Ok(vfs::VirtualFileSource::new(normalized))
}

/// Compile an entry file and its modules with embedded core, without a manifest.
/// Use `compile_package` for packages declaring dependencies in `wx.json`.
#[wasm_bindgen]
pub fn compile(
	entry_path: String,
	files: FileMap,
) -> Result<CompilationResultJs, String> {
	let source = file_source(files)?;
	let mut strings = symbols::Keyword::create_interner();
	let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
	builder.load_core();
	let root_id = builder
		.load_package(virtual_path(entry_path), &source)
		.map_err(|_| "entry file not found among `files`".to_string())?;
	compile_unit(builder.build(root_id), &mut strings)
		.map(CompilationResult::into_js)
}

/// Compile a directory containing `wx.json`, using the CLI's package resolver.
/// Supply all manifests and sources, including local dependencies, in `files`.
#[wasm_bindgen]
pub fn compile_package(
	package_path: String,
	files: FileMap,
) -> Result<CompilationResultJs, String> {
	let source = file_source(files)?;
	let mut strings = symbols::Keyword::create_interner();
	let compilation = vfs::open_manifest(
		virtual_path(package_path),
		&source,
		&mut strings,
	)
	.map_err(|_| {
		"could not load package: check manifests, entry files, and dependencies in `files`"
			.to_string()
	})?;
	compile_unit(compilation, &mut strings).map(CompilationResult::into_js)
}

fn compile_unit(
	compilation: vfs::CompilationUnit,
	strings: &mut symbols::StringInterner,
) -> Result<CompilationResult, String> {
	let mut diagnostics = compilation.collect_diagnostics();
	if diagnostics.has_errors() {
		return Ok(CompilationResult {
			diagnostics,
			bytecode: None,
		});
	}

	let mut sema = tir::check(&compilation, strings);
	let lowered = tir::lower(&mut sema, strings);
	diagnostics.extend_from_slice(sema.diagnostics());
	if diagnostics.has_errors() {
		return Ok(CompilationResult {
			diagnostics,
			bytecode: None,
		});
	}
	let mut mir = lowered.map_err(|_| "lowering failed".to_string())?;
	let module =
		backend::emit(&mut mir, strings, Some(mir::inline::Policy::DEFAULT))
			.map_err(|_| "codegen failed".to_string())?;

	Ok(CompilationResult {
		diagnostics,
		bytecode: Some(module.encode()),
	})
}
