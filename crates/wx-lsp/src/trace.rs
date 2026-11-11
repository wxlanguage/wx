//! Timed, grouped log output for one logical operation.

use std::path::PathBuf;

use tower_lsp_server::Client;
use tower_lsp_server::ls_types::MessageType;

/// Flushes buffered log lines (collected via `logs.push(...)` in plain,
/// `Client`-less helpers like `analyze_root`/`compile_root`/`parse_root`) to
/// the client. Not raw `eprintln!`: `vscode-languageclient` pipes a server's
/// stderr straight into `outputChannel.error(...)`, so every line written
/// there shows up tagged `[error]` regardless of content — `window/logMessage`
/// is the channel that actually carries a real severity.
pub(crate) async fn flush_logs(client: &Client, logs: Vec<String>) {
	for line in logs {
		client.log_message(MessageType::LOG, line).await;
	}
}

/// Accumulates named, timed steps for one logical operation — e.g. parsing
/// a package as part of typechecking it, or parsing a package as part of
/// formatting one of its files — so the whole dependency chain renders as
/// one readable block instead of one independent log line per step with no
/// visible relationship between them.
pub(crate) struct Trace {
	/// The file that caused this trace (the one edited/opened/formatted).
	/// Its package root is whatever `wx.json`-bearing ancestor it shares a
	/// path prefix with — no need to store that separately.
	path: PathBuf,
	steps: Vec<(&'static str, web_time::Duration)>,
}

impl Trace {
	pub(crate) fn new(path: PathBuf) -> Self {
		Self {
			path,
			steps: Vec::new(),
		}
	}

	/// Times `f`, records its duration under `label`, and returns its
	/// result unchanged — so callers thread this through exactly like the
	/// bare `Instant::now()` calls it replaces, `?` included.
	pub(crate) fn step<T>(
		&mut self,
		label: &'static str,
		f: impl FnOnce() -> T,
	) -> T {
		let start = web_time::Instant::now();
		let result = f();
		self.steps.push((label, start.elapsed()));
		result
	}

	/// Renders the causing file and every recorded step as an indented
	/// tree under `operation`, with the steps' total on the heading line
	/// itself (it's a summary of the block, not a sibling step that ran).
	/// Every line past the heading is indented two spaces so it reads as
	/// part of this one log entry rather than the surrounding log list —
	/// VS Code's Output panel only timestamp-prefixes a message's first
	/// line, so the rest need their own visual cue to stay grouped:
	/// ```text
	/// typecheck — 1.664473ms
	///   file: "/examples/pow/main.wx"
	///   ├─ parse:      772.593µs
	///   └─ typecheck:  891.88µs
	/// ```
	pub(crate) fn finish(&self, operation: &str) -> String {
		let mut out = if self.steps.is_empty() {
			operation.to_string()
		} else {
			let total: web_time::Duration =
				self.steps.iter().map(|(_, d)| *d).sum();
			format!("{operation} — {total:?}")
		};
		out.push_str(&format!("\n  file: {:?}", self.path));
		let width = self
			.steps
			.iter()
			.map(|(label, _)| label.len())
			.max()
			.unwrap_or(0)
			+ 1;
		let last = self.steps.len().saturating_sub(1);
		for (i, (label, duration)) in self.steps.iter().enumerate() {
			let branch = if i == last { "└─" } else { "├─" };
			let label_colon = format!("{label}:");
			out.push_str(&format!(
				"\n  {branch} {label_colon:<width$}  {duration:?}"
			));
		}
		out
	}
}
