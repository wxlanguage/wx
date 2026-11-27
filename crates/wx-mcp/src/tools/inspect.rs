//! `wx_inspect`: what each name written on one line means.

use std::collections::BTreeMap;
use std::path::Path;

use codespan_reporting::files::Files as _;
use schemars::JsonSchema;
use serde::Deserialize;
use wx_compiler::diagnostics::{TextOffset, TextSpan};
use wx_compiler::tir::{Definition, Reference, Site};

use crate::analysis::Analysis;

/// The tool's arguments, as the client sends them; the server loads the
/// package `file` is in before calling the tool.
#[derive(Deserialize, JsonSchema)]
pub(crate) struct Options {
	/// The source file.
	pub(crate) file: String,
	/// The line, counting from 1.
	pub(crate) line: usize,
	/// Only the names containing this text.
	pub(crate) text: Option<String>,
}

pub(crate) fn inspect(
	analysis: &Analysis,
	options: &Options,
) -> Result<String, String> {
	let file = Path::new(&options.file);
	let line = options.line;
	let filter = options.text.as_deref();
	let file_id = analysis.file(file)?;
	let files = &analysis.compilation.files;
	let range = line
		.checked_sub(1)
		.and_then(|index| files.line_range(file_id, index).ok())
		.ok_or_else(|| format!("`{}` has no line {line}", file.display()))?;
	let source = &files
		.get(file_id)
		.map_err(|error| error.to_string())?
		.source;
	let on_line = |span: TextSpan| {
		span.start != span.end && range.contains(&usize::from(span.start))
	};

	// One meaning per written name: where a name resolved in several roles
	// (a `use` leaf as a type and a value), the one it has where it is used.
	let mut names: BTreeMap<TextOffset, (TextSpan, Site, Reference)> =
		BTreeMap::new();
	for (site, reference) in analysis.sema.resolutions.iter() {
		let span = site.span();
		if span.file_id != file_id || !on_line(span.span) {
			continue;
		}
		let kept = names.get(&span.span.start);
		if kept.is_none_or(|&(_, kept, _)| priority(site) > priority(kept)) {
			names.insert(span.span.start, (span.span, site, reference));
		}
	}
	let formatter = analysis.sema.definition_formatter(&analysis.strings);
	let text = |span: TextSpan| {
		&source[usize::from(span.start)..usize::from(span.end)]
	};

	// Each written name with what it means, in source order.
	let mut explained: Vec<(TextSpan, String)> = Vec::new();
	for entry in analysis.items.iter() {
		let Some(span) =
			analysis.sema.definition_span(Definition::Item(entry.item))
		else {
			continue;
		};
		if span.file_id == file_id && on_line(span.span) {
			let signature = analysis.signature(entry.item);
			explained.push((
				span.span,
				format!("declares `{signature}` → {}", entry.path),
			));
		}
	}
	for (span, _, reference) in names.values() {
		let definition = reference.definition();
		let mut meaning = format!(
			"`{}`",
			formatter
				.jump(*reference)
				.or_else(|| formatter.signature(definition))
				.unwrap_or_else(|| "?".to_owned())
		);
		// `Self` in an impl names the declaration the impl is for.
		let named = analysis.row(definition).or_else(|| match definition {
			Definition::InherentImplTarget(index) => {
				analysis.sema.inherent_impl_target(index)
			}
			Definition::TraitImplTarget(index) => {
				analysis.sema.trait_impl_target(index)
			}
			_ => None,
		});
		if let Some(item) = named
			&& let Some(path) = analysis.items.path_of(item)
		{
			meaning.push_str(&format!(
				" → {path} [{}]",
				analysis.item_location(item)
			));
		}
		explained.push((*span, meaning));
	}
	explained.sort_by_key(|(span, _)| span.start);

	// A name written several times with one meaning is one line, with each
	// column it is written at.
	let mut merged: Vec<(&str, Vec<usize>, String)> = Vec::new();
	for (span, meaning) in explained {
		let name = text(span);
		if filter.is_some_and(|filter| !name.contains(filter)) {
			continue;
		}
		let column = usize::from(span.start) - range.start + 1;
		match merged.iter_mut().find(|(seen, _, seen_meaning)| {
			*seen == name && *seen_meaning == meaning
		}) {
			Some((_, columns, _)) => columns.push(column),
			None => merged.push((name, vec![column], meaning)),
		}
	}
	if merged.is_empty() {
		return Ok(format!("no resolved names on line {line}"));
	}
	let lines: Vec<_> = merged
		.into_iter()
		.map(|(name, columns, meaning)| {
			let columns: Vec<_> =
				columns.iter().map(usize::to_string).collect();
			let noun = if columns.len() == 1 {
				"column"
			} else {
				"columns"
			};
			format!("{name} ({noun} {}): {meaning}", columns.join(", "))
		})
		.collect();
	Ok(lines.join("\n"))
}

/// Which of the roles one written name plays is the one it means there:
/// the value, then the type, then the label.
fn priority(site: Site) -> u8 {
	match site {
		Site::Value(_) => 2,
		Site::Type(_) => 1,
		Site::Label(_) => 0,
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::json;

	use crate::analysis::tests::{Fixture, options};

	const SOURCE: &str = "\
struct Point(x: i32);
impl Point {
    func origin() -> Self { Self(0) }
}
func main() -> i32 {
    local point = Point::origin();
    point.x
}
";

	#[test]
	fn each_name_on_the_line_is_explained() {
		let fixture = Fixture::new(&[("main.wx", SOURCE)]);
		let text = inspect(
			&fixture.analysis(),
			&options(json!({ "file": fixture.path("main.wx"), "line": 6 })),
		)
		.unwrap();
		assert_eq!(
			text,
			"\
Point (column 19): `struct Point(x: i32)` → Point [main.wx:1:8]
origin (column 26): `func origin() -> Point` → Point::origin [main.wx:3:10]"
		);
	}

	#[test]
	fn a_declaration_on_the_line_is_named_with_its_path() {
		let fixture = Fixture::new(&[("main.wx", SOURCE)]);
		let text = inspect(
			&fixture.analysis(),
			&options(
				json!({ "file": fixture.path("main.wx"), "line": 5, "text": "main" }),
			),
		)
		.unwrap();
		assert_eq!(
			text,
			"main (column 6): declares `func main() -> i32` → main"
		);
	}

	#[test]
	fn self_names_the_impls_target_and_repeats_share_a_line() {
		let fixture = Fixture::new(&[("main.wx", SOURCE)]);
		let text = inspect(
			&fixture.analysis(),
			&options(json!({ "file": fixture.path("main.wx"), "line": 3 })),
		)
		.unwrap();
		assert_eq!(
			text,
			"\
origin (column 10): declares `func origin() -> Point` → Point::origin
Self (columns 22, 29): `type Self = Point` → Point [main.wx:1:8]"
		);
	}

	#[test]
	fn a_line_past_the_end_is_an_error() {
		let fixture = Fixture::new(&[("main.wx", SOURCE)]);
		let error = inspect(
			&fixture.analysis(),
			&options(json!({ "file": fixture.path("main.wx"), "line": 99 })),
		)
		.unwrap_err();
		assert!(error.ends_with("has no line 99"), "{error}");
	}
}
