//! `wx_check`: the package's diagnostics, a few lines each, every line
//! starting with where it points, for an agent to scan rather than a
//! person to read: no source excerpts, no ASCII art.

use codespan_reporting::diagnostic::{Diagnostic, LabelStyle, Severity};
use schemars::JsonSchema;
use serde::Deserialize;
use wx_compiler::vfs::FileId;

use crate::analysis::Analysis;

/// The tool's arguments, as the client sends them; `path` locates the
/// package, which the server loads before calling the tool.
#[derive(Deserialize, JsonSchema)]
pub(crate) struct Options {
	/// A file of the package or its directory; the package is the nearest
	/// directory above it holding a `wx.json`.
	pub(crate) path: String,
	/// How many diagnostics to list; all are counted.
	#[serde(default = "Options::default_limit")]
	pub(crate) limit: usize,
}

impl Options {
	fn default_limit() -> usize {
		30
	}
}

pub(crate) fn check(analysis: &Analysis, options: &Options) -> String {
	let limit = options.limit;
	let loading = analysis.compilation.collect_diagnostics();
	let lints = analysis.lints();
	let diagnostics: Vec<_> = loading
		.iter()
		.chain(analysis.sema.diagnostics())
		.chain(lints.as_deref().unwrap_or_default())
		.collect();
	let mut text = String::new();
	for diagnostic in diagnostics.iter().take(limit) {
		text.push_str(&render(analysis, diagnostic));
	}
	if diagnostics.len() > limit {
		text.push_str(&format!(
			"… {} more diagnostics; fix these first or pass a larger `limit`\n",
			diagnostics.len() - limit
		));
	}
	if let Err(reason) = &lints {
		text.push_str(&format!("note: lints did not run: {reason}\n"));
	}
	let count = |severity: Severity| {
		diagnostics
			.iter()
			.filter(|diagnostic| diagnostic.severity >= severity)
			.count()
	};
	let errors = count(Severity::Error);
	let warnings = count(Severity::Warning) - errors;
	text.push_str(&match (errors, warnings) {
		(0, 0) => "No errors found.".to_owned(),
		(errors, warnings) => {
			format!("{errors} error(s), {warnings} warning(s).")
		}
	});
	text
}

/// One diagnostic: a line with its primary location, severity, code and
/// message, then a line for each label that says more, at its own location,
/// and one for each note.
///
/// ```text
/// main.wx:4:15: error[E2004]: value must be used
///   main.wx:4:15: value never used
///   = if you don't need the value, drop it with an assignment to `_`
/// ```
fn render(analysis: &Analysis, diagnostic: &Diagnostic<FileId>) -> String {
	let position =
		|file_id, offset| format!("{}: ", analysis.position(file_id, offset));
	let primary = (diagnostic.labels.iter())
		.find(|label| label.style == LabelStyle::Primary);
	let severity = match diagnostic.severity {
		Severity::Bug => "bug",
		Severity::Error => "error",
		Severity::Warning => "warning",
		Severity::Note => "note",
		Severity::Help => "help",
	};
	let code = (diagnostic.code.as_deref())
		.map_or_else(String::new, |code| format!("[{code}]"));
	let mut text = format!(
		"{}{severity}{code}: {}\n",
		primary.map_or_else(String::new, |label| {
			position(label.file_id, label.range.start)
		}),
		diagnostic.message
	);
	for label in &diagnostic.labels {
		if !label.message.is_empty() {
			text.push_str(&format!(
				"  {}{}\n",
				position(label.file_id, label.range.start),
				label.message
			));
		}
	}
	for note in &diagnostic.notes {
		text.push_str(&format!("  = {}\n", note.replace('\n', "\n    ")));
	}
	text
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::json;

	use crate::analysis::tests::{Fixture, options};

	#[test]
	fn a_clean_package_reports_no_errors() {
		let fixture = Fixture::new(&[("main.wx", "func main() {}\n")]);
		assert_eq!(
			check(&fixture.analysis(), &options(json!({ "path": "" }))),
			"No errors found."
		);
	}

	#[test]
	fn an_error_is_a_few_lines_led_by_its_location() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"func one() -> u32 { 1 }\nfunc main() { one(); }\n",
		)]);
		let text = check(&fixture.analysis(), &options(json!({ "path": "" })));
		assert_eq!(
			text,
			"\
main.wx:2:15: error[E2004]: value must be used
  main.wx:2:15: value never used
  = if you don't need the value, drop it with an assignment to `_`
1 error(s), 0 warning(s)."
		);
	}

	#[test]
	fn a_limit_renders_that_many_and_counts_the_rest() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"func a() -> u32 { one }\nfunc b() -> u32 { two }\n",
		)]);
		let text = check(
			&fixture.analysis(),
			&options(json!({ "path": "", "limit": 1 })),
		);
		assert_eq!(text.matches("error[E2008]").count(), 1, "{text}");
		assert!(text.contains("… 1 more diagnostics"), "{text}");
		assert!(text.ends_with("2 error(s), 0 warning(s)."), "{text}");
	}
}
