//! `wx_describe`: one item by path, with its documentation and its members.

use std::collections::BTreeMap;

use schemars::JsonSchema;
use serde::Deserialize;
use wx_compiler::tir::{DeclKind, Definition, ItemLoc, TraitIdx, TraitImplIdx};

use super::search::unknown_path;
use crate::analysis::{Analysis, IndexedItem};

/// How many of a trait's implementations are listed.
const IMPLEMENTATIONS_SHOWN: usize = 30;

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
}

pub(crate) fn describe(
	analysis: &Analysis,
	options: &Options,
) -> Result<String, String> {
	let path = options.item.as_str();
	let matches = analysis.items.named(path);
	if matches.is_empty() {
		return Err(unknown_path(analysis, path));
	}
	let sections: Vec<_> =
		matches.iter().map(|entry| item(analysis, entry)).collect();
	Ok(sections.join("\n---\n\n").trim_end().to_owned())
}

/// One item: what and where it is, its signature and documentation, its
/// members, and the traits on either side of it.
fn item(analysis: &Analysis, entry: &IndexedItem) -> String {
	let formatter = analysis.sema.definition_formatter(&analysis.strings);
	let kind = analysis.sema.declaration_kind(entry.item);
	let internal = if entry.public { "" } else { ", internal" };
	let mut text = format!(
		"{} ({}{internal}, {})\n",
		entry.path,
		kind.noun(),
		analysis.item_location(entry.item)
	);
	if let Some(owner) = formatter.owner(Definition::Item(entry.item)) {
		text.push_str(&format!("in {owner}\n"));
	}
	text.push_str(&format!("\n{}\n", analysis.signature(entry.item)));
	if let Some(doc) = analysis.documentation(entry.item) {
		text.push_str(&format!("\n{doc}\n"));
	}
	let members =
		members(analysis, entry.item, matches!(kind, DeclKind::Trait(_)));
	if !members.is_empty() {
		text.push_str(&format!("\nmembers:\n{members}"));
	}
	let implemented = implemented_traits(analysis, entry.item);
	if !implemented.is_empty() {
		text.push_str(&format!("\nimplements: {}\n", implemented.join(", ")));
	}
	if let DeclKind::Trait(trait_index) = kind {
		text.push_str(&implementations(analysis, trait_index));
	}
	text
}

/// The items one step below `item`, grouped under the trait or impl they
/// belong to, in path order within each: a type's inherent members and
/// each of its trait impls'. A trait's own members need no header.
fn members(analysis: &Analysis, item: ItemLoc, is_trait: bool) -> String {
	let formatter = analysis.sema.definition_formatter(&analysis.strings);
	let mut children: Vec<_> = (analysis.items.children(item))
		.map(|child| {
			let owner = (formatter.owner(Definition::Item(child.item)))
				.filter(|_| !is_trait);
			(owner, analysis.signature(child.item))
		})
		.collect();
	children.sort_by(|(a, _), (b, _)| a.cmp(b));
	let mut text = String::new();
	let mut current_owner = None;
	for (owner, signature) in children {
		if let Some(header) = owner.as_deref()
			&& owner != current_owner
		{
			text.push_str(&format!("  {header}\n"));
		}
		let indent = if owner.is_some() { "    " } else { "  " };
		text.push_str(&format!("{indent}{signature}\n"));
		current_owner = owner;
	}
	text
}

/// Every trait impl, by its index.
fn trait_impls(analysis: &Analysis) -> impl Iterator<Item = TraitImplIdx> {
	(0..analysis.sema.decls.trait_impls.len())
		.map(|index| TraitImplIdx::new(index as u32))
}

/// The paths of the traits implemented for `item`, sorted: the impls with
/// members already show under them, and a marker trait's only here.
fn implemented_traits(analysis: &Analysis, item: ItemLoc) -> Vec<String> {
	let sema = &analysis.sema;
	let mut traits: Vec<_> = trait_impls(analysis)
		.filter(|&index| sema.trait_impl_target(index) == Some(item))
		.filter_map(|index| sema.trait_impl_trait(index))
		.map(|trait_index| {
			let loc = sema.decls.traits[usize::from(trait_index)].loc;
			(analysis.items.path_of(loc)).map_or_else(
				|| {
					let name = sema.decls.item(loc).name.inner;
					analysis.strings.resolve(name).unwrap_or("?").to_owned()
				},
				str::to_owned,
			)
		})
		.collect();
	traits.sort();
	traits.dedup();
	traits
}

/// What a trait is implemented for: each written impl's target by path and
/// where the impl names it, and a count of those generated for functions,
/// memories and globals, which no source writes.
fn implementations(analysis: &Analysis, trait_index: TraitIdx) -> String {
	let sema = &analysis.sema;
	let mut written = Vec::new();
	let mut generated: BTreeMap<&str, usize> = BTreeMap::new();
	for index in trait_impls(analysis) {
		if sema.trait_impl_trait(index) != Some(trait_index) {
			continue;
		}
		let Some(target) = sema.trait_impl_target(index) else {
			continue;
		};
		match sema.declaration_kind(target) {
			kind @ (DeclKind::Function(_)
			| DeclKind::Memory(_)
			| DeclKind::Global(_)) => *generated.entry(kind.noun()).or_default() += 1,
			_ => {
				let path = analysis.items.path_of(target).unwrap_or("?");
				let at = sema
					.definition_span(Definition::TraitImplTarget(index))
					.map_or_else(String::new, |span| {
						format!("  [{}]", analysis.location(span))
					});
				written.push(format!("  {path}{at}"));
			}
		}
	}
	written.sort();
	let mut text = String::new();
	if !written.is_empty() {
		let more = written.len().saturating_sub(IMPLEMENTATIONS_SHOWN);
		written.truncate(IMPLEMENTATIONS_SHOWN);
		text.push_str(&format!("\nimplemented for:\n{}\n", written.join("\n")));
		if more > 0 {
			text.push_str(&format!("  … {more} more\n"));
		}
	}
	for (noun, count) in generated {
		text.push_str(&format!(
			"generated for every {noun} ({count} in this compilation)\n"
		));
	}
	text
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::json;

	use crate::analysis::tests::{Fixture, options};

	#[test]
	fn a_type_shows_its_documentation_and_members_by_owner() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"\
/// A point on the plane.
struct Point(x: i32);
impl Point {
    func origin() -> Self { Self(0) }
}
trait Describe {
    func describe() -> u32;
}
impl Describe for Point {
    func describe() -> u32 { 1 }
}
func main() {}
",
		)]);
		let text = describe(
			&fixture.analysis(),
			&options(json!({ "path": "", "item": "Point" })),
		)
		.unwrap();
		assert_eq!(
			text,
			"\
Point (struct, internal, main.wx:2:8)

struct Point(x: i32)

A point on the plane.

members:
  impl Describe for Point
    func describe() -> u32
  impl Point
    func origin() -> Point

implements: Describe"
		);
	}

	#[test]
	fn a_traits_members_are_listed_without_a_header() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"trait Shape {\n    type Unit;\n    func area() -> u32;\n}\n",
		)]);
		let text = describe(
			&fixture.analysis(),
			&options(json!({ "path": "", "item": "Shape" })),
		)
		.unwrap();
		assert!(
			text.ends_with("members:\n  type Unit\n  func area() -> u32"),
			"{text}"
		);
	}

	#[test]
	fn a_trait_lists_what_implements_it_and_a_type_its_traits() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"\
trait Marker {}
struct Point(x: i32);
impl Marker for Point {}
impl Marker for u8 {}
",
		)]);
		let analysis = fixture.analysis();
		let text = describe(
			&analysis,
			&options(json!({ "path": "", "item": "Marker" })),
		)
		.unwrap();
		assert!(
			text.ends_with(
				"implemented for:\n  Point  [main.wx:3:17]\n  u8  [main.wx:4:17]"
			),
			"{text}"
		);
		let text = describe(
			&analysis,
			&options(json!({ "path": "", "item": "Point" })),
		)
		.unwrap();
		assert!(text.ends_with("implements: Marker"), "{text}");
	}

	#[test]
	fn a_generated_implementation_is_counted() {
		let fixture =
			Fixture::new(&[("main.wx", "memory heap: u32;\nfunc main() {}\n")]);
		let text = describe(
			&fixture.analysis(),
			&options(json!({ "path": "", "item": "Memory" })),
		)
		.unwrap();
		assert!(text.contains("generated for every memory ("), "{text}");
	}

	#[test]
	fn an_internal_item_is_marked() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"pub struct Open(x: i32);\nstruct Hidden(x: i32);\n",
		)]);
		let analysis = fixture.analysis();
		assert!(
			describe(
				&analysis,
				&options(json!({ "path": "", "item": "Open" }))
			)
			.unwrap()
			.starts_with("Open (struct, main.wx")
		);
		assert!(
			describe(
				&analysis,
				&options(json!({ "path": "", "item": "Hidden" }))
			)
			.unwrap()
			.starts_with("Hidden (struct, internal, main.wx")
		);
	}

	#[test]
	fn a_member_names_the_impl_it_belongs_to() {
		let fixture = Fixture::new(&[(
			"main.wx",
			"struct Point(x: i32);\nimpl Point {\n    func origin() -> Self { Self(0) }\n}\n",
		)]);
		let text = describe(
			&fixture.analysis(),
			&options(json!({ "path": "", "item": "Point::origin" })),
		)
		.unwrap();
		assert!(
			text.starts_with(
				"Point::origin (function, internal, main.wx:3:10)\nin impl Point\n"
			),
			"{text}"
		);
	}

	#[test]
	fn an_unknown_path_suggests_close_names() {
		let fixture = Fixture::new(&[("main.wx", "struct Point(x: i32);\n")]);
		let error = describe(
			&fixture.analysis(),
			&options(json!({ "path": "", "item": "shapes::Point" })),
		)
		.unwrap_err();
		assert!(
			error.starts_with(
				"no item has the path `shapes::Point`; did you mean: Point"
			),
			"{error}"
		);
	}
}
