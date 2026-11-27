//! `wx_references`: every use of an item, grouped by file.
//!
//! A call on a value of a concrete type resolves to the impl's member, and
//! one through a bound to the trait's, so the uses of a trait member are
//! both: its own and those of the impl members implementing it.

use std::collections::HashMap;
use std::mem::discriminant;

use codespan_reporting::files::Files as _;
use schemars::JsonSchema;
use serde::Deserialize;
use wx_compiler::tir::{ItemLoc, MemberOwner};

use super::capped;
use super::search::unknown_path;
use crate::analysis::Analysis;

/// The tool's arguments, as the client sends them; `path` locates the
/// package, which the server loads before calling the tool.
#[derive(Deserialize, JsonSchema)]
pub(crate) struct Options {
	/// A file of the package or its directory; the package is the nearest
	/// directory above it holding a `wx.json`.
	pub(crate) path: String,
	/// An item's path as written from the root package's entry file:
	/// `parse`, `net::Client`, `Point::origin`, a dependency's
	/// `json::Value`, core's `Memory`. Other tools print these paths.
	pub(crate) item: String,
	/// How many uses to list; all are counted.
	#[serde(default = "Options::default_limit")]
	pub(crate) limit: usize,
}

impl Options {
	fn default_limit() -> usize {
		200
	}
}

pub(crate) fn references(
	analysis: &Analysis,
	options: &Options,
) -> Result<String, String> {
	let path = options.item.as_str();
	let limit = options.limit;
	let named = analysis.items.named(path);
	if named.is_empty() {
		return Err(unknown_path(analysis, path));
	}
	// Each item whose uses count, with the implementation a use goes
	// through when it is not the named item itself.
	let mut targets: HashMap<ItemLoc, Option<&str>> = HashMap::new();
	for entry in named {
		targets.insert(entry.item, None);
		for implementation in implementations(analysis, entry.item) {
			let via = analysis.items.path_of(implementation);
			targets.entry(implementation).or_insert(via);
		}
	}
	let files = &analysis.compilation.files;
	let mut uses: Vec<_> = (analysis.sema.resolutions.iter())
		.filter(|(site, _)| site.span().span.start != site.span().span.end)
		.filter_map(|(site, reference)| {
			let row = analysis.row(reference.definition())?;
			Some((site.span(), *targets.get(&row)?))
		})
		.collect();
	uses.sort();
	uses.dedup_by_key(|&mut (span, _)| span);
	if uses.is_empty() {
		return Ok(format!("`{path}` is not used"));
	}
	let count = uses.len();
	let mut lines = Vec::new();
	let mut current_file = None;
	for (span, via) in uses {
		if current_file != Some(span.file_id) {
			lines.push(format!("{}:", analysis.file_name(span.file_id)));
			current_file = Some(span.file_id);
		}
		let source = files
			.line_index(span.file_id, usize::from(span.span.start))
			.and_then(|index| files.line_range(span.file_id, index))
			.ok()
			.zip(files.get(span.file_id).ok())
			.map_or("", |(range, file)| file.source[range].trim());
		let (line, column) = analysis.line_column(span);
		let via = via.map_or_else(String::new, |via| format!("  (via {via})"));
		lines.push(format!("  {line}:{column}  {source}{via}"));
	}
	let header = format!("{count} use(s) of `{path}`:");
	Ok(format!(
		"{header}\n{}",
		capped(lines, limit, "pass a larger `limit` to see the rest")
	))
}

/// The impl members implementing the trait member `item`: members of an
/// impl of its trait, of its kind and with its name. None for anything
/// that is not a trait's member.
fn implementations(analysis: &Analysis, item: ItemLoc) -> Vec<ItemLoc> {
	let sema = &analysis.sema;
	let MemberOwner::Trait(trait_index) = sema.member_owner(item) else {
		return Vec::new();
	};
	let kind = discriminant(&sema.declaration_kind(item));
	let name = sema.decls.item(item).name.inner;
	(analysis.items.iter())
		.map(|entry| entry.item)
		.filter(|&candidate| {
			matches!(
				sema.member_owner(candidate),
				MemberOwner::TraitImpl(index)
					if sema.trait_impl_trait(index) == Some(trait_index)
			) && discriminant(&sema.declaration_kind(candidate)) == kind
				&& sema.decls.item(candidate).name.inner == name
		})
		.collect()
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::json;

	use crate::analysis::tests::{Fixture, options};

	/// Files come in the order the package loads them, its entry first.
	#[test]
	fn uses_are_grouped_by_file_with_their_line() {
		let fixture = Fixture::new(&[
			(
				"main.wx",
				"mod geometry;\nfunc main() -> i32 { geometry::double(2) }\n",
			),
			(
				"geometry.wx",
				"pub func double(x: i32) -> i32 { x * 2 }\nfunc quad(x: i32) -> i32 { double(double(x)) }\n",
			),
		]);
		let text = references(
			&fixture.analysis(),
			&options(json!({ "path": "", "item": "geometry::double" })),
		)
		.unwrap();
		assert_eq!(
			text,
			"\
3 use(s) of `geometry::double`:
main.wx:
  2:32  func main() -> i32 { geometry::double(2) }
geometry.wx:
  2:28  func quad(x: i32) -> i32 { double(double(x)) }
  2:35  func quad(x: i32) -> i32 { double(double(x)) }"
		);
	}

	#[test]
	fn an_unused_item_says_so() {
		let fixture = Fixture::new(&[("main.wx", "func lonely() {}\n")]);
		assert_eq!(
			references(
				&fixture.analysis(),
				&options(json!({ "path": "", "item": "lonely" }))
			)
			.unwrap(),
			"`lonely` is not used"
		);
	}

	const TRAIT_CALLS: &str = "\
trait Describe: StackValue {
    func describe(self: Self) -> u32;
}
struct Point(x: i32);
impl Describe for Point {
    func describe(self: Self) -> u32 { 1 }
}
func generic<T: Describe>(value: T) -> u32 { value.describe() }
func concrete(point: Point) -> u32 { point.describe() }
";

	/// A call through a bound is the trait member's; one on a `Point` is
	/// the impl member's, and also counts for the trait member it
	/// implements.
	#[test]
	fn a_trait_members_uses_include_its_implementations() {
		let fixture = Fixture::new(&[("main.wx", TRAIT_CALLS)]);
		let analysis = fixture.analysis();
		assert_eq!(
			references(&analysis, &options(json!({ "path": "", "item": "Describe::describe" }))).unwrap(),
			"\
2 use(s) of `Describe::describe`:
main.wx:
  8:52  func generic<T: Describe>(value: T) -> u32 { value.describe() }
  9:44  func concrete(point: Point) -> u32 { point.describe() }  (via Point::describe)"
		);
		assert_eq!(
			references(
				&analysis,
				&options(json!({ "path": "", "item": "Point::describe" }))
			)
			.unwrap(),
			"\
1 use(s) of `Point::describe`:
main.wx:
  9:44  func concrete(point: Point) -> u32 { point.describe() }"
		);
	}
}
