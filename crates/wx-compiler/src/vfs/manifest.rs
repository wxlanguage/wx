use std::collections::HashMap;

use super::{AbsolutePath, RelativePath};

/// A parsed `wx.json`. Resolved into `PackageGraph`s by
/// [`super::resolve::open_manifest`].
///
/// Flat rather than nesting `type`/`entry` under a `"package"` object:
/// there's no longer a second, package-scoped namespace of keys to justify
/// the nesting now that a package has no name of its own to put in there
/// either — every key here just is a property of this manifest.
///
/// Unknown keys are ignored rather than rejected: `wx.json` is expected to
/// grow further top-level keys (`meta`), and a manifest written for a newer
/// wx should still load on an older one rather than failing outright.
#[derive(serde::Deserialize)]
pub struct PackageManifest {
	#[serde(default, rename = "type")]
	pub kind: Option<PackageManifestKind>,
	/// Where compilation starts, relative to this manifest's own directory
	/// — required, not defaulted to a conventional filename like `main.wx`,
	/// so a directory argument never has to guess which file is the root.
	/// The same field regardless of `kind`: entry-point resolution doesn't
	/// vary with what kind of package this is.
	pub entry: RelativePath,
	/// Arbitrary string keys selected by `package "key" as alias;`.
	#[serde(default)]
	pub dependencies: HashMap<String, DependencySource>,
	#[serde(default)]
	pub format: FormatManifest,
}

/// The optional `"format"` section: `wx.json`'s copy of `wx-fmt`'s
/// `RendererConfig`, one field looser. Lives here rather than as
/// `wx_fmt::RendererConfig` itself — `wx-fmt` depends on `wx-compiler`, not
/// the reverse, so this crate has no way to name that type. `wx-fmt` reads
/// this struct directly and overlays whatever's `Some` onto
/// `RendererConfig::default()`; there's deliberately no second, duplicate
/// set of these fields anywhere.
///
/// Every field optional and defaulted, at both the struct level (a manifest
/// with no `"format"` key at all) and per-field (one that sets only e.g.
/// `max_line_width`) — a manifest should be able to override a single
/// setting without restating the other.
#[derive(serde::Deserialize, Default, Clone, Copy)]
pub struct FormatManifest {
	#[serde(default)]
	pub max_line_width: Option<u32>,
	#[serde(default)]
	pub indent_width: Option<u8>,
}

impl PackageManifest {
	/// Parses a `wx.json` manifest from its raw source text.
	pub fn parse(source: &str) -> Result<Self, serde_json::Error> {
		serde_json::from_str(source)
	}
}

/// The optional `"type"` field identifies the package providing the language's
/// primitives, operator traits and intrinsics. Ordinary packages omit it;
/// every package can be imported or compiled to WebAssembly.
#[derive(serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PackageManifestKind {
	/// Supplies core itself, so the embedded core is not loaded alongside it.
	/// Recorded as [`super::CompilationUnit::core_package`].
	Core,
}

/// A single `dependencies` entry. Tagged from the start so a future
/// remote/registry source is an additive new variant, not a breaking reshape
/// of every existing `wx.json`'s `dependencies`.
///
/// `path: RelativePath`, not a general path type: this design's
/// dependency-resolution rule requires a declared dependency path to
/// always be relative to the declaring manifest, never the process's
/// cwd — making that a real type invariant instead of a convention.
#[derive(serde::Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum DependencySource {
	Local { path: RelativePath },
}

/// The resolved identity of a dependency — what [`DependencySource::resolve`]
/// produces, used to dedupe a diamond dependency (the same physical
/// package reached via two different declaring packages). Kept as its own
/// tagged enum mirroring `DependencySource`'s own shape, rather than just
/// the resolved `AbsolutePath` alone: a future `Remote`/`Registry`
/// variant's resolved identity (whatever that ends up being — a URL, a
/// cache path, ...) could otherwise collide with an unrelated `Local`
/// dependency that happens to resolve to the same string, even though
/// they're not the same thing at all. Tagging by variant makes that
/// impossible by construction.
#[derive(PartialEq, Eq, Hash, Clone)]
pub(super) enum ResolvedDependency {
	Local(AbsolutePath),
}

impl DependencySource {
	/// Resolves `self` as declared relative to `base_dir`.
	pub(super) fn resolve(
		&self,
		base_dir: &AbsolutePath,
	) -> ResolvedDependency {
		match self {
			DependencySource::Local { path } => {
				ResolvedDependency::Local(base_dir.join(path))
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn dependency<'m>(
		manifest: &'m PackageManifest,
		key: &str,
	) -> Option<&'m DependencySource> {
		manifest.dependencies.get(key)
	}

	#[test]
	fn manifest_parses_ordinary_package() {
		let manifest = PackageManifest::parse(r#"{ "entry": "main.wx" }"#)
			.expect("valid ordinary manifest should parse");

		assert!(manifest.kind.is_none());
		assert_eq!(manifest.entry.as_str(), "main.wx");
		assert!(manifest.dependencies.is_empty());
	}

	#[test]
	fn manifest_defaults_format_section_when_absent() {
		let manifest = PackageManifest::parse(r#"{ "entry": "main.wx" }"#)
			.expect("valid ordinary manifest should parse");

		assert_eq!(manifest.format.max_line_width, None);
		assert_eq!(manifest.format.indent_width, None);
	}

	#[test]
	fn manifest_parses_full_format_section() {
		let manifest = PackageManifest::parse(
			r#"{
				"entry": "main.wx",
				"format": {
					"max_line_width": 100,
					"indent_width": 2
				}
			}"#,
		)
		.expect("valid format section should parse");

		assert_eq!(manifest.format.max_line_width, Some(100));
		assert_eq!(manifest.format.indent_width, Some(2));
	}

	/// A manifest should be able to override a single setting without
	/// restating the other.
	#[test]
	fn manifest_format_section_fields_are_individually_optional() {
		let manifest = PackageManifest::parse(
			r#"{
				"entry": "main.wx",
				"format": { "max_line_width": 100 }
			}"#,
		)
		.expect("a partial format section should parse");

		assert_eq!(manifest.format.max_line_width, Some(100));
		assert_eq!(manifest.format.indent_width, None);
	}

	#[test]
	fn manifest_parses_core_package() {
		let manifest =
			PackageManifest::parse(r#"{ "type": "core", "entry": "main.wx" }"#)
				.expect("valid core manifest should parse");

		assert!(matches!(manifest.kind, Some(PackageManifestKind::Core)));
	}

	#[test]
	fn manifest_parses_package_with_dependencies() {
		let manifest = PackageManifest::parse(
			r#"{
				"entry": "main.wx",
				"dependencies": {
					"somelib": { "type": "local", "path": "../somelib" }
				}
			}"#,
		)
		.expect("valid ordinary manifest should parse");

		assert!(manifest.kind.is_none());
		match dependency(&manifest, "somelib") {
			Some(DependencySource::Local { path }) => {
				assert_eq!(path.as_str(), "../somelib")
			}
			None => panic!("expected a `somelib` dependency entry"),
		}
	}

	/// A package no longer declares a name, and unknown keys are ignored
	/// rather than rejected (so a manifest written for a newer wx still
	/// loads on an older one) — so a stale `"name"` parses and is dropped.
	#[test]
	fn manifest_ignores_stale_package_name() {
		let manifest =
			PackageManifest::parse(r#"{ "entry": "main.wx", "name": "core" }"#)
				.expect("an unknown key should be ignored, not rejected");

		assert!(manifest.kind.is_none());
	}

	#[test]
	fn manifest_rejects_invalid_package_type() {
		for kind in ["wat", "lib", "bin", "std"] {
			let source =
				format!(r#"{{ "type": "{kind}", "entry": "main.wx" }}"#);
			assert!(
				PackageManifest::parse(&source).is_err(),
				"invalid type: {kind}"
			);
		}
	}

	#[test]
	fn manifest_rejects_missing_entry() {
		let result = PackageManifest::parse(r#"{}"#);
		assert!(result.is_err(), "a missing `entry` should fail");
	}

	#[test]
	fn manifest_preserves_arbitrary_dependency_keys() {
		for key in [
			"SomeLib",
			"my-lib",
			"loop",
			"my_lib",
			"@org/math",
			"with spaces",
			"数学",
			"",
			"a\"b\\c\n",
		] {
			let source = serde_json::json!({
				"entry": "main.wx",
				"dependencies": HashMap::from([(
					key,
					serde_json::json!({ "type": "local", "path": "../somelib" }),
				)]),
			})
			.to_string();
			let manifest = PackageManifest::parse(&source)
				.expect("any string key should parse");
			assert!(
				dependency(&manifest, key).is_some(),
				"key must be preserved: {key:?}"
			);
		}
	}

	#[test]
	fn manifest_rejects_unrecognized_dependency_type() {
		let result = PackageManifest::parse(
			r#"{
				"entry": "main.wx",
				"dependencies": {
					"somelib": { "type": "remote", "url": "https://example.com" }
				}
			}"#,
		);
		assert!(
			result.is_err(),
			"an unrecognized dependency `type` should fail"
		);
	}
}
