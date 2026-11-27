//! `wx_wasm`: the module the package builds to, as WAT. Built the way
//! `wx build` builds it: lowered, inlined, optimized, emitted.

use schemars::JsonSchema;
use serde::Deserialize;
use wx_compiler::diagnostics::Diagnostics as _;
use wx_compiler::{backend, mir, tir};

use super::capped;
use crate::analysis::Analysis;

/// The tool's arguments, as the client sends them; `path` locates the
/// package, which the server loads before calling the tool.
#[derive(Deserialize, JsonSchema)]
pub(crate) struct Options {
	/// A file of the package or its directory; the package is the nearest
	/// directory above it holding a `wx.json`.
	pub(crate) path: String,
	/// How many lines of WAT to show.
	#[serde(default = "Options::default_limit")]
	pub(crate) limit: usize,
}

impl Options {
	fn default_limit() -> usize {
		2000
	}
}

pub(crate) fn wasm(
	mut analysis: Analysis,
	options: &Options,
) -> Result<String, String> {
	let limit = options.limit;
	let lints_fail = analysis.lints().is_ok_and(|lints| lints.has_errors());
	if analysis.compilation.has_errors()
		|| analysis.sema.diagnostics().has_errors()
		|| lints_fail
	{
		return Err(
			"the package has errors; run wx_check to see them".to_owned()
		);
	}
	let mut mir = tir::lower(&mut analysis.sema, &analysis.strings)
		.map_err(|()| "lowering failed; run wx_check to see why".to_owned())?;
	let module = backend::emit(
		&mut mir,
		&analysis.strings,
		Some(mir::inline::Policy::DEFAULT),
	)
	.map_err(|()| "WebAssembly code generation failed".to_owned())?;
	let bytes = module.encode();
	let wat = wasmprinter::print_bytes(&bytes)
		.map_err(|error| format!("cannot print the module: {error}"))?;
	let lines = wat.lines().map(str::to_owned).collect();
	Ok(format!(
		"{} bytes\n{}",
		bytes.len(),
		capped(lines, limit, "pass a larger `limit` to see the rest")
	))
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::json;

	use crate::analysis::tests::{Fixture, options};

	#[test]
	fn an_exported_function_is_printed_as_wat() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"func answer() -> i32 { 42 }\nexport { answer }\n",
		)]);
		let text =
			wasm(fixture.analysis(), &options(json!({ "path": "" }))).unwrap();
		assert!(text.contains("(export \"answer\" (func"), "{text}");
		assert!(text.contains("i32.const 42"), "{text}");
	}

	#[test]
	fn a_package_with_errors_is_not_built() {
		let fixture =
			Fixture::new(&[("main.wx", "func main() -> u32 { missing }\n")]);
		let error = wasm(fixture.analysis(), &options(json!({ "path": "" })))
			.unwrap_err();
		assert_eq!(error, "the package has errors; run wx_check to see them");
	}
}
