//! What each tool answers, from one [`Analysis`](crate::analysis::Analysis)
//! of a package, as plain text. A tool that cannot answer returns why.

mod check;
mod describe;
mod inspect;
mod outline;
mod references;
mod search;
mod wasm;

pub(crate) use check::{Options as CheckOptions, check};
pub(crate) use describe::{Options as DescribeOptions, describe};
pub(crate) use inspect::{Options as InspectOptions, inspect};
pub(crate) use outline::{Options as OutlineOptions, outline};
pub(crate) use references::{Options as ReferencesOptions, references};
pub(crate) use search::{Options as SearchOptions, search};
pub(crate) use wasm::{Options as WasmOptions, wasm};

/// `lines`, at most `limit` of them, and how many more there were.
fn capped(lines: Vec<String>, limit: usize, hint: &str) -> String {
	let more = lines.len().saturating_sub(limit);
	let mut text = lines.into_iter().take(limit).collect::<Vec<_>>().join("\n");
	if more > 0 {
		text.push_str(&format!("\n… {more} more; {hint}"));
	}
	text
}
