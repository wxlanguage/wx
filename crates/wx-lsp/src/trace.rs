//! Timed log output for one actor command.

use std::borrow::Cow;
use std::path::PathBuf;

use tower_lsp_server::Client;
use tower_lsp_server::ls_types::MessageType;

/// Sends a finished trace to the client. Not raw `eprintln!`:
/// `vscode-languageclient` pipes a server's stderr straight into
/// `outputChannel.error(...)`, so every line written there shows up tagged
/// `[error]` regardless of content — `window/logMessage` is the channel that
/// actually carries a real severity.
pub(crate) async fn flush(client: &Client, trace: Trace) {
	client.log_message(MessageType::LOG, trace.finish()).await;
}

/// How long one command took, and the named parts of it that were timed:
/// checking each package a change reaches, and within it parsing and
/// checking. Parts nest, so a command that rechecks two packages renders
/// one group per package.
pub(crate) struct Trace {
	command: &'static str,
	/// The file the command is about, when it is about one.
	path: Option<PathBuf>,
	start: web_time::Instant,
	/// In the order they started; a group comes before its parts.
	steps: Vec<Step>,
	depth: usize,
}

struct Step {
	label: Cow<'static, str>,
	depth: usize,
	duration: web_time::Duration,
}

impl Trace {
	pub(crate) fn new(command: &'static str, path: Option<PathBuf>) -> Self {
		Self {
			command,
			path,
			start: web_time::Instant::now(),
			steps: Vec::new(),
			depth: 0,
		}
	}

	/// Times `f` as a part of the command named `label`, and returns its
	/// result unchanged, `?` included.
	pub(crate) fn step<T>(
		&mut self,
		label: impl Into<Cow<'static, str>>,
		f: impl FnOnce(&mut Self) -> T,
	) -> T {
		let at = self.steps.len();
		self.steps.push(Step {
			label: label.into(),
			depth: self.depth,
			duration: web_time::Duration::ZERO,
		});
		let start = web_time::Instant::now();
		self.depth += 1;
		let result = f(self);
		self.depth -= 1;
		self.steps[at].duration = start.elapsed();
		result
	}

	/// How many parts named `label` were timed.
	#[cfg(test)]
	pub(crate) fn count(&self, label: &str) -> usize {
		self.steps.iter().filter(|step| step.label == label).count()
	}

	/// The command and its duration, then every part as an indented tree.
	/// Every line past the heading is indented two spaces so it reads as
	/// part of this one log entry: VS Code's Output panel only
	/// timestamp-prefixes a message's first line.
	/// ```text
	/// textDocument/didChange — 1.664473ms
	///   file: "/examples/pow/main.wx"
	///   └─ /examples/pow: 1.5ms
	///      ├─ parse:      772.593µs
	///      └─ check:      691.88µs
	/// ```
	pub(crate) fn finish(&self) -> String {
		let mut out = format!("{} — {:?}", self.command, self.start.elapsed());
		if let Some(path) = &self.path {
			out.push_str(&format!("\n  file: {path:?}"));
		}
		let width = self
			.steps
			.iter()
			.map(|step| 3 * step.depth + step.label.len())
			.max()
			.unwrap_or(0)
			+ 1;
		// Whether the open group at each depth has a later part, which
		// draws its line down past the parts nested under this one.
		let mut continues = Vec::new();
		for (at, step) in self.steps.iter().enumerate() {
			let last = self.steps[at + 1..]
				.iter()
				.find(|next| next.depth <= step.depth)
				.is_none_or(|next| next.depth < step.depth);
			continues.truncate(step.depth);
			let mut prefix = String::new();
			for &more in &continues {
				prefix.push_str(if more { "│  " } else { "   " });
			}
			prefix.push_str(if last { "└─ " } else { "├─ " });
			continues.push(!last);
			let label = format!("{}:", step.label);
			let pad = width - 3 * step.depth;
			out.push_str(&format!(
				"\n  {prefix}{label:<pad$}  {:?}",
				step.duration
			));
		}
		out
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn a_command_renders_its_parts_as_a_tree() {
		let mut trace = Trace::new(
			"textDocument/didChange",
			Some(PathBuf::from("/p/main.wx")),
		);
		trace.step("/p", |trace| {
			trace.step("parse", |_| ());
			trace.step("check", |_| ());
		});
		trace.step("/q", |trace| trace.step("check", |_| ()));
		let rendered = trace.finish();
		let mut lines = rendered.lines();
		assert!(
			lines
				.next()
				.unwrap()
				.starts_with("textDocument/didChange — ")
		);
		// The parts, without their durations.
		let parts: Vec<_> = lines
			.map(|line| line.rsplit_once(':').map_or(line, |(part, _)| part))
			.collect();
		assert_eq!(
			parts,
			[
				"  file",
				"  ├─ /p",
				"  │  ├─ parse",
				"  │  └─ check",
				"  └─ /q",
				"     └─ check",
			]
		);
	}
}
