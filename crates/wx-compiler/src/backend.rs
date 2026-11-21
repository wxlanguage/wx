//! The backend sequence after lowering: what every build runs between
//! [`crate::tir::build`]'s MIR and the encoded module, so the CLI and the
//! execution tests compile the same way.

use crate::ast::StringInterner;
use crate::codegen::{self, WasmModule};
use crate::mir::{self, MIR};

/// Optionally inline, optimize reached function bodies, and emit retained items.
/// `None` skips inlining; function optimization and reachability always run.
pub fn emit(
	mir: &mut MIR,
	strings: &StringInterner,
	inline: Option<mir::inline::Policy>,
) -> Result<WasmModule, ()> {
	if let Some(policy) = inline {
		mir::inline::run(mir, policy);
	}
	let reached = crate::opt::optimize_reachable(mir);
	codegen::Builder::build(mir, strings, &reached)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::testing::DiagnosticView;
	use crate::vfs;

	fn source_graph(
		source: &str,
		strings: &mut StringInterner,
	) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new(strings);
		builder.load_core();
		let root_id = builder
			.load_package(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)]),
				),
			)
			.unwrap();
		let graph = builder.build(root_id);
		DiagnosticView::new(
			"parse",
			&graph.collect_diagnostics(),
			&graph.files,
		)
		.assert_no_errors();
		graph
	}

	#[test]
	fn ordinary_manifests_emit_wasm_with_or_without_exports() {
		for export in ["", "export { answer }"] {
			let mut strings = crate::symbols::Keyword::create_interner();
			let source = vfs::VirtualFileSource::from_relative(
				std::collections::HashMap::from([
					(
						"wx.json".to_string(),
						r#"{ "entry": "main.wx" }"#.to_string(),
					),
					(
						"main.wx".to_string(),
						format!(
							"pub func answer() -> i32 {{ core::i32_add(40, 2) }} {export}"
						),
					),
				]),
			);
			let graph = vfs::open_manifest(
				vfs::AbsolutePath::new("/"),
				&source,
				&mut strings,
			)
			.unwrap();
			let mut sema = crate::tir::check(&graph, &mut strings);
			let lowered = crate::tir::lower(&mut sema, &strings);
			DiagnosticView::new("check", sema.diagnostics(), &graph.files)
				.assert_no_errors();
			let mut mir = lowered.expect("the package lowers");
			let bytes =
				emit(&mut mir, &strings, Some(mir::inline::Policy::DEFAULT))
					.unwrap()
					.encode();
			let engine = wasmtime::Engine::default();
			let module = wasmtime::Module::new(&engine, &bytes).unwrap();
			let mut store = wasmtime::Store::new(&engine, ());
			let instance =
				wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
			if export.is_empty() {
				assert_eq!(bytes, b"\0asm\x01\0\0\0");
				assert_eq!(instance.exports(&mut store).count(), 0);
			} else {
				let answer = instance
					.get_typed_func::<(), i32>(&mut store, "answer")
					.unwrap();
				assert_eq!(answer.call(&mut store, ()).unwrap(), 42);
			}
		}
	}

	/// The build sequence honours `#[inline]`: the callee is spliced into
	/// its caller and omitted from output, and the module still computes the result.
	#[test]
	fn a_build_inlines_an_inline_callee() {
		let source = r#"
			#[inline]
			func double(x: i32) -> i32 { x + x }
			func run(x: i32) -> i32 { double(x) + 1 }
			export { run as "run" }
		"#;
		let mut strings = crate::symbols::Keyword::create_interner();
		let graph = source_graph(source, &mut strings);
		let mut mir = crate::tir::lower(
			&mut crate::tir::check(&graph, &mut strings),
			&strings,
		)
		.expect("the source lowers");
		assert_eq!(mir.functions.len(), 2);
		let bytes =
			emit(&mut mir, &strings, Some(mir::inline::Policy::DEFAULT))
				.expect("the MIR encodes")
				.encode();
		assert_eq!(mir.functions.len(), 2, "MIR IDs stay stable");
		assert!(
			mir.functions
				.iter()
				.filter_map(|f| f.code())
				.all(|code| code.callees().next().is_none())
		);

		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, &bytes).unwrap();
		let mut store = wasmtime::Store::new(&engine, ());
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 20).unwrap(), 41);
	}

	#[test]
	fn removed_calls_do_not_keep_host_imports_with_or_without_inlining() {
		let source = r#"
			import "host" as host { func probe(value: i32) -> i32; }
			func dead(x: i32) -> i32 { host::probe(x) }
			func run(x: i32) -> i32 { return x; dead(x) }
			export { run as "run" }
		"#;
		for inline in [None, Some(mir::inline::Policy::DEFAULT)] {
			let mut strings = crate::symbols::Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
			let mut mir = crate::tir::lower(
				&mut crate::tir::check(&graph, &mut strings),
				&strings,
			)
			.unwrap();
			let count = mir.functions.len();
			let exports: Vec<_> = mir.exports.iter().map(|e| e.item).collect();
			let module = emit(&mut mir, &strings, inline).unwrap();
			assert_eq!(mir.functions.len(), count);
			assert_eq!(
				mir.exports.iter().map(|e| e.item).collect::<Vec<_>>(),
				exports
			);
			assert_eq!(
				mir.imports.len(),
				1,
				"import metadata keeps its MIR ID"
			);
			mir.verify_imports().unwrap();
			let engine = wasmtime::Engine::default();
			let module =
				wasmtime::Module::new(&engine, module.encode()).unwrap();
			assert_eq!(
				module.imports().count(),
				0,
				"dead imports are omitted from output"
			);
			let mut store = wasmtime::Store::new(&engine, ());
			let instance =
				wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
			let run = instance
				.get_typed_func::<i32, i32>(&mut store, "run")
				.unwrap();
			for x in [0, 42, i32::MIN, i32::MAX] {
				assert_eq!(run.call(&mut store, x).unwrap(), x);
			}
		}
	}
}
