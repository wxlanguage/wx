//! `wx_outline`: a package's items by path, each with its signature and the
//! first line of its documentation. An item is internal when something on
//! its path is not `pub`, so no other package can name it; another
//! package's internal items are listed only when asked for.

use schemars::JsonSchema;
use serde::Deserialize;

use super::capped;
use crate::analysis::Analysis;

/// The tool's arguments, as the client sends them; `path` locates the
/// package, which the server loads before calling the tool.
#[derive(Deserialize, JsonSchema)]
pub(crate) struct Options {
	/// A file of the package or its directory; the package is the nearest
	/// directory above it holding a `wx.json`.
	pub(crate) path: String,
	/// `core`, or the key of one of the root package's dependencies; the
	/// root package itself when absent.
	pub(crate) package: Option<String>,
	/// Only items at or below this path, e.g. `net` or `Point`.
	pub(crate) scope: Option<String>,
	/// Also list another package's internal items, which the root package
	/// cannot name; the root package's own are always listed.
	#[serde(default)]
	pub(crate) internal: bool,
	/// How many items to list.
	#[serde(default = "Options::default_limit")]
	pub(crate) limit: usize,
}

impl Options {
	fn default_limit() -> usize {
		300
	}
}

pub(crate) fn outline(
	analysis: &Analysis,
	options: &Options,
) -> Result<String, String> {
	let package = analysis.package(options.package.as_deref())?;
	let scope = options.scope.as_deref();
	let internal =
		options.internal || package == analysis.compilation.root_package;
	let within = |path: &str| {
		scope.is_none_or(|scope| {
			path == scope
				|| path
					.strip_prefix(scope)
					.is_some_and(|rest| rest.starts_with("::"))
		})
	};
	let lines: Vec<_> = (analysis.items.iter())
		.filter(|entry| entry.package == package && within(&entry.path))
		.filter(|entry| entry.public || internal)
		.map(|entry| {
			let mut line = analysis.item_line(entry);
			if let Some(doc) = analysis.documentation(entry.item)
				&& let Some(first) =
					doc.lines().find(|line| !line.trim().is_empty())
			{
				line.push_str(&format!("\n    {first}"));
			}
			line
		})
		.collect();
	if lines.is_empty() {
		return Err(match scope {
			Some(scope) => format!("no items at or below `{scope}`"),
			None => "the package declares no items".to_owned(),
		});
	}
	Ok(capped(
		lines,
		options.limit,
		"pass `scope` to list part of the package, or a larger `limit`",
	))
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::json;

	use crate::analysis::tests::{Fixture, options};

	const SOURCE: &str = "\
pub mod shapes {
    /// A point on the plane.
    ///
    /// Its coordinates are integers.
    pub struct Point(x: i32, y: i32);
    impl Point {
        pub func origin() -> Self { Self(0, 0) }
    }
}
func main() {}
";

	#[test]
	fn items_are_listed_by_path_with_signature_and_summary() {
		let fixture = Fixture::new(&[("main.wx", SOURCE)]);
		let text =
			outline(&fixture.analysis(), &options(json!({ "path": "" })))
				.unwrap();
		assert_eq!(
			text,
			"\
main (internal) — func main() -> ()  [main.wx:10:6]
shapes — mod shapes  [main.wx:1:9]
shapes::Point — struct Point(x: i32, y: i32)  [main.wx:5:16]
    A point on the plane.
shapes::Point::origin — func origin() -> Point  [main.wx:7:18]"
		);
	}

	#[test]
	fn a_scope_keeps_the_items_at_or_below_it() {
		let fixture = Fixture::new(&[("main.wx", SOURCE)]);
		let text = outline(
			&fixture.analysis(),
			&options(json!({ "path": "", "scope": "shapes::Point" })),
		)
		.unwrap();
		assert!(text.starts_with("shapes::Point — "), "{text}");
		assert!(!text.contains("main (internal)"), "{text}");
		let error = outline(
			&fixture.analysis(),
			&options(json!({ "path": "", "scope": "shape" })),
		)
		.unwrap_err();
		assert_eq!(error, "no items at or below `shape`");
	}

	#[test]
	fn core_can_be_outlined() {
		let fixture = Fixture::new(&[("main.wx", "func main() {}\n")]);
		let text = outline(
			&fixture.analysis(),
			&options(
				json!({ "path": "", "package": "core", "scope": "Memory" }),
			),
		)
		.unwrap();
		assert!(text.starts_with("Memory — trait Memory"), "{text}");
	}

	const APP_AND_LIB: &[(&str, &str)] = &[
		(
			"app/wx.json",
			r#"{ "entry": "main.wx", "dependencies": { "geometry": { "type": "local", "path": "../lib" } } }"#,
		),
		(
			"app/main.wx",
			"package \"geometry\" as geometry;\nfunc main() {}\n",
		),
		("lib/wx.json", r#"{ "entry": "lib.wx" }"#),
		(
			"lib/lib.wx",
			"pub func area(side: i32) -> i32 { side * side }\nfunc helper() {}\n",
		),
	];

	#[test]
	fn a_dependency_shows_its_public_api_under_its_alias() {
		let fixture = Fixture::new(APP_AND_LIB);
		let analysis = fixture.analysis_of("app");
		assert_eq!(
			outline(
				&analysis,
				&options(json!({ "path": "", "package": "geometry" }))
			)
			.unwrap(),
			"geometry::area — func area(side: i32) -> i32  [../lib/lib.wx:1:10]"
		);
		let all = outline(
			&analysis,
			&options(
				json!({ "path": "", "package": "geometry", "internal": true }),
			),
		)
		.unwrap();
		assert!(
			all.ends_with(
				"geometry::helper (internal) — func helper() -> ()  [../lib/lib.wx:2:6]"
			),
			"{all}"
		);
	}
}
