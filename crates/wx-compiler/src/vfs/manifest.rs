use std::collections::HashMap;

use serde::Deserialize;

use super::{AbsolutePath, RelativePath};
use crate::ast;

/// A parsed `wx.json`. Not yet consulted by any loader — `open_package`
/// (a later step) is what will actually resolve one of these into a
/// `PackageGraph`.
///
/// A struct wrapping a tagged enum, not the enum alone, so `dependencies` is
/// declared once and shared by both kinds instead of duplicated per variant.
#[derive(serde::Deserialize)]
pub struct PackageManifest {
	pub package: PackageManifestKind,
	#[serde(default)]
	pub dependencies: HashMap<String, DependencySource>,
}

impl PackageManifest {
	/// Parses a `wx.json` manifest from its raw source text.
	pub fn parse(source: &str) -> Result<Self, serde_json::Error> {
		serde_json::from_str(source)
	}
}

/// What `wx.json`'s `"package"` object deserializes to. Distinct from
/// [`super::PackageKind`] (the resolved runtime kind on `PackageGraph`) —
/// this one is purely what the manifest's `"type"` field says, and
/// additionally carries `name` for `Lib` (a binary's name, if it ever gets
/// one, wouldn't belong here — it's not part of what `"type"` means).
#[derive(serde::Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum PackageManifestKind {
	Lib {
		#[serde(deserialize_with = "deserialize_package_name")]
		name: String,
	},
	Bin,
}

/// A single `dependencies` entry. Only one variant today, but tagged from
/// the start so a future remote/registry source is an additive new variant,
/// not a breaking reshape of every existing `wx.json`'s `dependencies`.
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

/// Whether `name` could ever be lexed as a wx identifier at all: ordinary
/// snake_case shape, and not a reserved keyword. A package named e.g. `loop`
/// would otherwise load without error and then be permanently
/// unreferenceable from any `.wx` file (`loop::Item` can't parse as a path).
///
/// `pub(super)`: also used by `vfs::resolve` to validate a `dependencies`
/// key before using it as a package's name (see `PackageKind::Library`'s
/// name being sourced from the dependency key, not the target's own
/// manifest).
pub(super) fn is_valid_package_name(name: &str) -> bool {
	let mut chars = name.chars();
	let first_ok =
		matches!(chars.next(), Some(c) if c == '_' || c.is_ascii_lowercase());
	first_ok
		&& chars
			.all(|c| c == '_' || c.is_ascii_lowercase() || c.is_ascii_digit())
		&& ast::Keyword::try_from(name).is_err()
}

fn deserialize_package_name<'de, D>(deserializer: D) -> Result<String, D::Error>
where
	D: serde::Deserializer<'de>,
{
	let name = String::deserialize(deserializer)?;
	if is_valid_package_name(&name) {
		Ok(name)
	} else {
		Err(serde::de::Error::custom(format!(
			"invalid package name `{name}`: must be a snake_case \
			 identifier and not a reserved keyword"
		)))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn manifest_parses_valid_lib_package() {
		let manifest = PackageManifest::parse(
			r#"{ "package": { "type": "lib", "name": "std" } }"#,
		)
		.expect("valid lib manifest should parse");

		match manifest.package {
			PackageManifestKind::Lib { name } => assert_eq!(name, "std"),
			PackageManifestKind::Bin => panic!("expected Lib"),
		}
		assert!(manifest.dependencies.is_empty());
	}

	#[test]
	fn manifest_parses_valid_bin_package_with_dependencies() {
		let manifest = PackageManifest::parse(
			r#"{
				"package": { "type": "bin" },
				"dependencies": {
					"somelib": { "type": "local", "path": "../somelib" }
				}
			}"#,
		)
		.expect("valid bin manifest should parse");

		assert!(matches!(manifest.package, PackageManifestKind::Bin));
		match manifest.dependencies.get("somelib") {
			Some(DependencySource::Local { path }) => {
				assert_eq!(path.as_str(), "../somelib")
			}
			None => panic!("expected a `somelib` dependency entry"),
		}
	}

	#[test]
	fn manifest_rejects_lib_without_name() {
		let result =
			PackageManifest::parse(r#"{ "package": { "type": "lib" } }"#);
		assert!(result.is_err(), "a lib manifest without `name` should fail");
	}

	#[test]
	fn manifest_rejects_invalid_package_type() {
		let result = PackageManifest::parse(
			r#"{ "package": { "type": "wat", "name": "std" } }"#,
		);
		assert!(result.is_err(), "an unrecognized `type` should fail");
	}

	#[test]
	fn manifest_rejects_uppercase_package_name() {
		let result = PackageManifest::parse(
			r#"{ "package": { "type": "lib", "name": "Std" } }"#,
		);
		assert!(result.is_err(), "an uppercase package name should fail");
	}

	#[test]
	fn manifest_rejects_hyphenated_package_name() {
		let result = PackageManifest::parse(
			r#"{ "package": { "type": "lib", "name": "my-lib" } }"#,
		);
		assert!(result.is_err(), "a hyphenated package name should fail");
	}

	#[test]
	fn manifest_rejects_reserved_keyword_package_name() {
		let result = PackageManifest::parse(
			r#"{ "package": { "type": "lib", "name": "loop" } }"#,
		);
		assert!(
			result.is_err(),
			"a reserved-keyword package name should fail"
		);
	}

	#[test]
	fn manifest_rejects_unrecognized_dependency_type() {
		let result = PackageManifest::parse(
			r#"{
				"package": { "type": "bin" },
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
