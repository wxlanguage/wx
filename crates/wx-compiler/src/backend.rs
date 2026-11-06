//! The backend sequence after lowering: what every build runs between
//! [`crate::tir::build`]'s MIR and the encoded module, so the CLI and the
//! execution tests compile the same way.

use crate::ast::StringInterner;
use crate::codegen::{self, WasmModule};
use crate::mir::{self, MIR};

/// Transforms `mir` in place (inlining under `inline`, which also drops
/// functions nothing reaches) and generates its module. A build passes
/// `Some(mir::inline::Policy::DEFAULT)`; `None` emits the MIR as lowered,
/// for tests that tell lowering apart from inlining.
pub fn emit(
	mir: &mut MIR,
	strings: &StringInterner,
	inline: Option<mir::inline::Policy>,
) -> Result<WasmModule, ()> {
	if let Some(policy) = inline {
		mir::inline::run(mir, policy);
	}
	codegen::Builder::build(mir, strings)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::testing::DiagnosticView;
	use crate::vfs;

	fn source_graph(source: &str) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new();
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
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

	/// The build sequence honours `#[inline]`: the callee is spliced into
	/// its caller and dropped, and the module still computes the result.
	#[test]
	fn a_build_inlines_an_inline_callee() {
		let source = r#"
			#[inline]
			func double(x: i32) -> i32 { x + x }
			func run(x: i32) -> i32 { double(x) + 1 }
			export { run as "run" }
		"#;
		let mut graph = source_graph(source);
		let mut mir =
			crate::tir::build(&mut graph).1.expect("the source lowers");
		assert_eq!(mir.functions.len(), 2);
		let bytes =
			emit(&mut mir, &graph.strings, Some(mir::inline::Policy::DEFAULT))
				.expect("the MIR encodes")
				.encode();
		assert_eq!(mir.functions.len(), 1);
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
}
