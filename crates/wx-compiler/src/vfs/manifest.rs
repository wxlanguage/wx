use std::collections::HashMap;

use super::{AbsolutePath, RelativePath};
use crate::ast;

/// A parsed `wx.json`. Resolved into `PackageGraph`s by
/// [`super::resolve::open_package`].
///
/// A struct wrapping a tagged enum, not the enum alone, so `dependencies` is
/// declared once and shared by every kind instead of duplicated per variant.
///
/// Unknown keys are ignored rather than rejected: `wx.json` is expected to
/// grow further sections (`meta`, `format`), and a manifest written for a
/// newer wx should still load on an older one rather than failing outright.
#[derive(serde::Deserialize)]
pub struct PackageManifest {
	pub package: PackageManifestKind,
	#[serde(default)]
	pub dependencies: HashMap<PackageName, DependencySource>,
}

/// A `dependencies` key: the name a package is known by inside the package
/// that declared it, and — since a package no longer declares a name of its
/// own — the only source of package names there is.
///
/// A newtype rather than a bare `String` so validity is a type invariant
/// established at parse time, not a check some resolution step has to
/// remember to run. It also means an invalid key is a real `serde` error
/// carrying a message, instead of the bare `Err(())` the resolver used to
/// return, which aborted the whole compilation with nothing printed.
#[derive(PartialEq, Eq, Hash, Clone, PartialOrd, Ord, Debug)]
pub struct PackageName(String);

impl PackageName {
	pub fn as_str(&self) -> &str {
		&self.0
	}
}

impl<'de> serde::Deserialize<'de> for PackageName {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: serde::Deserializer<'de>,
	{
		let name = String::deserialize(deserializer)?;
		if is_valid_package_name(&name) {
			Ok(PackageName(name))
		} else {
			Err(serde::de::Error::custom(format!(
				"invalid package name `{name}`: must be a snake_case \
				 identifier and not a reserved keyword"
			)))
		}
	}
}

impl PackageManifest {
	/// Parses a `wx.json` manifest from its raw source text.
	pub fn parse(source: &str) -> Result<Self, serde_json::Error> {
		serde_json::from_str(source)
	}
}

/// What `wx.json`'s `"package"` object deserializes to. Distinct from
/// [`super::PackageKind`] (the resolved runtime kind on `PackageGraph`) —
/// this one is purely what the manifest's `"type"` field says.
///
/// No variant carries a name. What a package is called is decided by
/// whoever depends on it (its `dependencies` key), so a self-declared name
/// would be either ignored or a second, conflicting source of truth. A
/// globally-unique registry identity is a separate future concern
/// (`meta.name`), not this.
#[derive(serde::Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum PackageManifestKind {
	Lib,
	Bin,
	/// This package *is* the stdlib: it defines the `#[tag = "..."]` items
	/// the language itself needs (the twelve operator traits), so the
	/// embedded stdlib must not also be loaded alongside it.
	///
	/// Not "no stdlib" — wx has no freestanding mode, since those tagged
	/// items are mandatory for every compilation. It means "I provide it
	/// myself". Resolves to an ordinary [`super::PackageKind::Library`];
	/// the std-ness is recorded once, as
	/// [`super::CompilationUnit::stdlib_package`].
	Std,
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

/// Whether `name` could ever be lexed as a wx identifier at all: ordinary
/// snake_case shape, and not a reserved keyword. A package named e.g. `loop`
/// would otherwise load without error and then be permanently
/// unreferenceable from any `.wx` file (`loop::Item` can't parse as a path).
///
/// Private: [`PackageName`] is now the only way a name enters the system, so
/// this has exactly one caller (that type's `Deserialize`) plus its own
/// tests. Validating anywhere else would mean a name had already been built
/// unchecked.
fn is_valid_package_name(name: &str) -> bool {
	let mut chars = name.chars();
	let first_ok =
		matches!(chars.next(), Some(c) if c == '_' || c.is_ascii_lowercase());
	first_ok
		&& chars
			.all(|c| c == '_' || c.is_ascii_lowercase() || c.is_ascii_digit())
		&& ast::Keyword::try_from(name).is_err()
}

#[cfg(test)]
mod tests {
	use super::*;

	/// Dependency keys are the only names a manifest declares, so they're
	/// what the name-validation tests below exercise.
	fn dependency<'m>(
		manifest: &'m PackageManifest,
		key: &str,
	) -> Option<&'m DependencySource> {
		manifest
			.dependencies
			.iter()
			.find(|(name, _)| name.as_str() == key)
			.map(|(_, source)| source)
	}

	#[test]
	fn manifest_parses_valid_lib_package() {
		let manifest =
			PackageManifest::parse(r#"{ "package": { "type": "lib" } }"#)
				.expect("valid lib manifest should parse");

		assert!(matches!(manifest.package, PackageManifestKind::Lib));
		assert!(manifest.dependencies.is_empty());
	}

	#[test]
	fn manifest_parses_std_package() {
		let manifest =
			PackageManifest::parse(r#"{ "package": { "type": "std" } }"#)
				.expect("valid std manifest should parse");

		assert!(matches!(manifest.package, PackageManifestKind::Std));
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
		let manifest = PackageManifest::parse(
			r#"{ "package": { "type": "lib", "name": "std" } }"#,
		)
		.expect("an unknown key should be ignored, not rejected");

		assert!(matches!(manifest.package, PackageManifestKind::Lib));
	}

	#[test]
	fn manifest_rejects_invalid_package_type() {
		let result =
			PackageManifest::parse(r#"{ "package": { "type": "wat" } }"#);
		assert!(result.is_err(), "an unrecognized `type` should fail");
	}

	fn parse_with_dependency_key(key: &str) -> Result<PackageManifest, ()> {
		PackageManifest::parse(&format!(
			r#"{{
				"package": {{ "type": "bin" }},
				"dependencies": {{
					"{key}": {{ "type": "local", "path": "../somelib" }}
				}}
			}}"#
		))
		.map_err(|_| ())
	}

	#[test]
	fn manifest_rejects_uppercase_dependency_key() {
		assert!(
			parse_with_dependency_key("SomeLib").is_err(),
			"an uppercase package name should fail"
		);
	}

	#[test]
	fn manifest_rejects_hyphenated_dependency_key() {
		assert!(
			parse_with_dependency_key("my-lib").is_err(),
			"a hyphenated package name should fail"
		);
	}

	#[test]
	fn manifest_rejects_reserved_keyword_dependency_key() {
		assert!(
			parse_with_dependency_key("loop").is_err(),
			"a reserved-keyword package name should fail"
		);
	}

	#[test]
	fn manifest_accepts_snake_case_dependency_key() {
		assert!(parse_with_dependency_key("my_lib").is_ok());
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
