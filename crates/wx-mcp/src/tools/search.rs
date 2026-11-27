//! `wx_search`: items by a part of their name, among those the root package
//! can name; and the near names suggested for a path that names nothing.

use schemars::JsonSchema;
use serde::Deserialize;

use super::capped;
use crate::analysis::{Analysis, IndexedItem};

/// The tool's arguments, as the client sends them; `path` locates the
/// package, which the server loads before calling the tool.
#[derive(Deserialize, JsonSchema)]
pub(crate) struct Options {
	/// A file of the package or its directory; the package is the nearest
	/// directory above it holding a `wx.json`.
	pub(crate) path: String,
	/// Part of an item's name or path.
	pub(crate) query: String,
	/// Only items of this kind: function, struct, enum, enum variant,
	/// trait, typeset, type alias, constant, associated type, memory,
	/// global, module, import block.
	pub(crate) kind: Option<String>,
	/// How many matches to list.
	#[serde(default = "Options::default_limit")]
	pub(crate) limit: usize,
}

impl Options {
	fn default_limit() -> usize {
		40
	}
}

pub(crate) fn search(analysis: &Analysis, options: &Options) -> String {
	let query = options.query.as_str();
	let kind = options.kind.as_deref();
	let limit = options.limit;
	let lowercase = query.to_lowercase();
	let root = analysis.compilation.root_package;
	let mut found: Vec<_> = (analysis.items.nameable(root))
		.filter(|entry| {
			kind.is_none_or(|kind| {
				analysis.sema.declaration_kind(entry.item).noun() == kind
			})
		})
		.filter_map(|entry| Some((rank(entry, &lowercase)?, entry)))
		.collect();
	// A path matches only when no name does: a query names what it looks
	// for, and the items of a module named like it are not that.
	if found.iter().any(|&(rank, _)| rank != Rank::InPath) {
		found.retain(|&(rank, _)| rank != Rank::InPath);
	}
	found.sort_by_key(|&(rank, entry)| (rank, &entry.path));
	if found.is_empty() {
		return format!("no item matches `{query}`");
	}
	let lines = found
		.into_iter()
		.map(|(_, entry)| analysis.item_line(entry))
		.collect();
	capped(
		lines,
		limit,
		"make the query or the kind more specific, or pass a larger `limit`",
	)
}

/// How an item matches a query, best first. Letter case is ignored.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Rank {
	Name,
	NameStart,
	InName,
	InPath,
}

/// How `entry` matches `query`, already in lowercase.
fn rank(entry: &IndexedItem, query: &str) -> Option<Rank> {
	let path = entry.path.to_lowercase();
	let name = last_segment(&path);
	if name == query {
		Some(Rank::Name)
	} else if name.starts_with(query) {
		Some(Rank::NameStart)
	} else if name.contains(query) {
		Some(Rank::InName)
	} else if path.contains(query) {
		Some(Rank::InPath)
	} else {
		None
	}
}

fn last_segment(path: &str) -> &str {
	path.rsplit("::").next().unwrap_or(path)
}

/// Why `path` names nothing, with the nameable items named most like it:
/// those whose name contains its last segment, then those a few letters
/// away from it.
pub(crate) fn unknown_path(analysis: &Analysis, path: &str) -> String {
	let name = last_segment(path).to_lowercase();
	// A typo is a letter or two; more than a third of the name is another
	// name.
	let tolerance = (name.chars().count() / 3).max(1);
	let root = analysis.compilation.root_package;
	let mut near: Vec<_> = (analysis.items.nameable(root))
		.filter_map(|entry| {
			let candidate = last_segment(&entry.path).to_lowercase();
			let closeness = if candidate.contains(&name) {
				0
			} else {
				let distance = edit_distance(&candidate, &name);
				if distance > tolerance {
					return None;
				}
				distance
			};
			Some((closeness, entry.path.as_str()))
		})
		.collect();
	near.sort();
	near.dedup_by_key(|&mut (_, path)| path);
	let mut message = format!("no item has the path `{path}`");
	if !near.is_empty() {
		let names: Vec<_> =
			near.iter().take(5).map(|&(_, path)| path).collect();
		message.push_str("; did you mean: ");
		message.push_str(&names.join(", "));
	}
	message
}

/// How many single-letter insertions, deletions and substitutions turn `a`
/// into `b`.
fn edit_distance(a: &str, b: &str) -> usize {
	let b: Vec<char> = b.chars().collect();
	let mut row: Vec<usize> = (0..=b.len()).collect();
	for (i, a) in a.chars().enumerate() {
		let mut diagonal = row[0];
		row[0] = i + 1;
		for (j, &b) in b.iter().enumerate() {
			let above = row[j + 1];
			row[j + 1] = (diagonal + usize::from(a != b))
				.min(row[j] + 1)
				.min(above + 1);
			diagonal = above;
		}
	}
	row[b.len()]
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::json;

	use crate::analysis::tests::{Fixture, options};

	fn paths(text: &str) -> Vec<&str> {
		text.lines()
			.map(|line| line.split(' ').next().unwrap())
			.collect()
	}

	#[test]
	fn matches_are_ranked_exact_name_first() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"struct Grow(x: i32);\nfunc grow_twice() {}\nfunc main() {}\n",
		)]);
		let text = search(
			&fixture.analysis(),
			&options(json!({ "path": "", "query": "grow" })),
		);
		assert_eq!(paths(&text)[0], "Grow", "{text}");
		assert!(paths(&text).contains(&"grow_twice"), "{text}");
		assert!(
			text.contains(
				"grow_twice (internal) — func grow_twice() -> ()  [main.wx:2:6]"
			),
			"{text}"
		);
	}

	#[test]
	fn a_path_matches_only_when_no_name_does() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"mod sine {\n    pub const S1: u32 = 1;\n}\nfunc sine_of() {}\n",
		)]);
		assert_eq!(
			paths(&search(
				&fixture.analysis(),
				&options(json!({ "path": "", "query": "sine" }))
			)),
			["sine", "sine_of"]
		);
		assert_eq!(
			paths(&search(
				&fixture.analysis(),
				&options(json!({ "path": "", "query": "sine::s" }))
			)),
			["sine::S1"]
		);
	}

	#[test]
	fn a_match_reads_as_declared_with_its_field_names() {
		let fixture =
			Fixture::new(&[("main.wx", "struct Grow(mut size: i32);\n")]);
		let text = search(
			&fixture.analysis(),
			&options(json!({ "path": "", "query": "grow", "kind": "struct" })),
		);
		assert_eq!(
			text,
			"Grow (internal) — struct Grow(mut size: i32)  [main.wx:1:8]"
		);
	}

	#[test]
	fn nothing_matching_says_so() {
		let fixture = Fixture::new(&[("main.wx", "func main() {}\n")]);
		assert_eq!(
			search(
				&fixture.analysis(),
				&options(json!({ "path": "", "query": "zzzz_nothing" }))
			),
			"no item matches `zzzz_nothing`"
		);
	}

	#[test]
	fn a_typo_suggests_the_names_a_letter_or_two_away() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"struct Vec(len: u32);\nimpl Vec {\n    func push() {}\n}\n",
		)]);
		assert_eq!(
			unknown_path(&fixture.analysis(), "Vec::pusj"),
			"no item has the path `Vec::pusj`; did you mean: Vec::push"
		);
	}

	#[test]
	fn edit_distance_counts_single_letter_edits() {
		assert_eq!(edit_distance("push", "push"), 0);
		assert_eq!(edit_distance("push", "pusj"), 1);
		assert_eq!(edit_distance("push", "pus"), 1);
		assert_eq!(edit_distance("kitten", "sitting"), 3);
	}
}
