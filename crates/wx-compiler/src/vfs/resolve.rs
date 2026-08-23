use std::collections::{HashMap, HashSet};

use codespan_reporting::diagnostic::Diagnostic;

use super::manifest::{ResolvedDependency, is_valid_package_name};
use super::{
	AbsolutePath, CompilationUnit, CompilationUnitBuilder, DiagnosticCode,
	FileId, FileSource, PackageId, PackageKind, PackageManifest,
	PackageManifestKind, RelativePath,
};
use crate::ast;

/// Maps a manifest's declared `"package"` kind to the resolved
/// `PackageKind` used at runtime, interning a `Lib`'s name into `interner`.
/// `name_override`, when `Some`, replaces a `Lib`'s own declared name —
/// used when loading a dependency (its declaring package's `dependencies`
/// key becomes its actual name, not whatever it calls itself, see
/// `open_manifest_package`); `None` for any package being resolved as
/// itself (the root, or an explicitly `--manifest`-given formatting
/// target).
pub fn package_kind(
	kind: &PackageManifestKind,
	name_override: Option<&str>,
	interner: &mut ast::StringInterner,
) -> PackageKind {
	match kind {
		PackageManifestKind::Bin => PackageKind::Binary,
		PackageManifestKind::Lib { name } => {
			let name = name_override.unwrap_or(name);
			PackageKind::Library {
				name: interner.get_or_intern(name),
			}
		}
	}
}

/// Loads whatever `entry` points at, resolving a `wx.json` manifest if one
/// governs it — the single entry point every frontend (CLI, LSP, wasm,
/// tests) should use instead of hand-rolling the `load_stdlib()` +
/// `load_binary()` dance.
///
/// `entry` is always absolute — every frontend is responsible for making
/// it so before calling this (joining a CLI argument against
/// `std::env::current_dir()`, or following the synthetic `/`-rooted
/// convention `VirtualFileSource`-backed compilations use). Nothing past
/// this point ever has to wonder whether a path is absolute or relative.
///
/// - No `wx.json` in `entry`'s containing directory: today's exact
///   anonymous behavior — `load_stdlib()` then `load_binary(entry, ..)`,
///   in that order.
/// - `wx.json` found: `entry` itself is ignored from here on — the entry
///   file is always `main.wx` next to the manifest, regardless of
///   `"type"` (see the design doc for why the filename never varies with
///   kind) — and every `dependencies` entry is resolved recursively,
///   relative to *its declaring* manifest's own directory. The embedded
///   stdlib is then loaded under the name `std` iff nothing already
///   claimed that name — this one check implements the implicit-`std`
///   rule in full: it no-ops when the root package is itself named `std`,
///   and is overridden for free by an explicit `"std"` dependency, with no
///   special-casing either way.
///
/// `source` is shared, unchanged, across every package this resolves —
/// correct today only because `Local` is the only `DependencySource`
/// variant, so every dependency necessarily lives in the same "world" as
/// whatever's resolving it (the same filesystem, or the same
/// `VirtualFileSource` map in tests). A future `Remote`/`Registry` variant
/// would need its own `FileSource` (fetched/cached separately), which
/// can't be threaded through `&impl FileSource` here without widening it
/// to `&dyn FileSource` first — deliberately not done now, since that
/// variant is explicitly out of scope for this plan.
pub fn open_package(
	entry: AbsolutePath,
	source: &impl FileSource,
) -> Result<CompilationUnit, ()> {
	let mut builder = CompilationUnitBuilder::new();
	let dir = entry.parent();
	let manifest_path = dir.join(&RelativePath::new("wx.json"));

	if !source.exists(&manifest_path) {
		builder.load_stdlib();
		let root_id = builder.load_binary(entry, source)?;
		return Ok(builder.build(root_id));
	}

	let root_id = open_manifest_package(
		&mut builder,
		&dir,
		None,
		source,
		&mut HashMap::new(),
		&mut HashSet::new(),
	)?;

	let std_name = builder.interner.get_or_intern("std");
	if !builder.package_by_name.contains_key(&std_name) {
		builder.load_stdlib();
	}

	Ok(builder.build(root_id))
}

/// Loads the package whose manifest lives at `{dir}/wx.json`, then
/// recursively does the same for each of its `dependencies` — each
/// resolved relative to *this* manifest's own directory, never the
/// process's cwd, so a dependency chain composes correctly regardless of
/// where compilation started.
///
/// `name_override` is `None` only for the root (nothing depends on it
/// within this compilation, so it must use its own manifest-declared
/// name) — every other call passes `Some(key)`, the *depending* package's
/// `dependencies` key, which becomes the loaded package's actual name,
/// **not** whatever its own manifest happens to declare. This is what
/// makes the implicit-`std` override work by simply using the key
/// `"std"` regardless of the replacement's own self-declared name, and
/// what lets two unrelated packages that each happen to name themselves
/// the same thing internally still both be depended on, as long as their
/// respective dependents pick different keys for them. The known rough
/// edge: if the *same* physical package is reached as a dependency under
/// two different keys (a diamond, see `resolved` below), whichever is
/// resolved first wins the name and the second key silently doesn't
/// apply — consistent with this plan's existing punt on transitive
/// dependency semantics generally.
///
/// `resolved` memoizes by [`DependencySource::resolve`]'s identity, so a
/// diamond dependency is only ever parsed and loaded once. `in_progress`
/// tracks the current recursion stack by that same identity: if a
/// dependency edge points back at something still `in_progress`, that's a
/// cycle — this function still returns `Ok`, but records a
/// `CircularDependency` diagnostic on the package that made the cyclic
/// reference and simply doesn't recurse into it again, rather than
/// failing resolution outright or recursing forever.
fn open_manifest_package(
	builder: &mut CompilationUnitBuilder,
	dir: &AbsolutePath,
	name_override: Option<&str>,
	source: &impl FileSource,
	resolved: &mut HashMap<ResolvedDependency, PackageId>,
	in_progress: &mut HashSet<ResolvedDependency>,
) -> Result<PackageId, ()> {
	let manifest_path = dir.join(&RelativePath::new("wx.json"));
	let manifest_source = source.read_to_string(&manifest_path)?;
	let manifest = PackageManifest::parse(&manifest_source).map_err(|_| ())?;

	let kind =
		package_kind(&manifest.package, name_override, &mut builder.interner);
	let entry_path = dir.join(&RelativePath::new("main.wx"));
	let id = builder.load_package(kind, entry_path, source)?;

	// Sorted so a name collision among dependencies is diagnosed the same
	// way on every run, not depending on `HashMap`'s randomized order.
	let mut dependencies: Vec<_> = manifest.dependencies.into_iter().collect();
	dependencies.sort_by(|(a, _), (b, _)| a.cmp(b));

	for (key, dependency) in dependencies {
		if !is_valid_package_name(&key) {
			return Err(());
		}

		let identity = dependency.resolve(dir);
		if resolved.contains_key(&identity) {
			continue; // diamond dependency: already loaded, name already decided
		}
		if in_progress.contains(&identity) {
			builder.packages[id.as_usize()]
				.linker_diagnostics
				.push(report_circular_dependency(&key));
			continue;
		}

		let ResolvedDependency::Local(dependency_dir) = &identity;

		in_progress.insert(identity.clone());
		let dependency_id = open_manifest_package(
			builder,
			dependency_dir,
			Some(&key),
			source,
			resolved,
			in_progress,
		)?;
		in_progress.remove(&identity);
		resolved.insert(identity, dependency_id);
	}

	Ok(id)
}

/// No label: there's no specific span inside a `wx.json` to point at from
/// here (see `DuplicatePackageName`'s own reasoning) — the message just
/// names the dependency key whose edge closes the cycle.
fn report_circular_dependency(key: &str) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::CircularDependency.code())
		.with_message(format!(
			"circular dependency: `{key}` depends (directly or \
			 transitively) on a package that depends back on it"
		))
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::vfs::VirtualFileSource;

	fn virtual_source(files: &[(&str, &str)]) -> VirtualFileSource {
		VirtualFileSource::new(
			files
				.iter()
				.map(|(path, source)| {
					(AbsolutePath::new(*path), source.to_string())
				})
				.collect(),
		)
	}

	#[test]
	fn plain_binary_with_no_manifest_gets_std() {
		let source = virtual_source(&[("/main.wx", "fn add() {}")]);
		let compilation =
			open_package(AbsolutePath::new("/main.wx"), &source).unwrap();

		assert_eq!(compilation.packages.len(), 2, "root + std");
		let std_name = compilation.interner.get("std").unwrap();
		assert!(compilation.package_by_name.contains_key(&std_name));
		let root = &compilation.packages[compilation.root_package.as_usize()];
		assert!(matches!(root.kind, PackageKind::Binary));
	}

	#[test]
	fn manifested_binary_with_no_dependencies_gets_std() {
		let source = virtual_source(&[
			("/app/wx.json", r#"{ "package": { "type": "bin" } }"#),
			("/app/main.wx", "fn add() {}"),
		]);
		let compilation =
			open_package(AbsolutePath::new("/app/main.wx"), &source).unwrap();

		assert_eq!(compilation.packages.len(), 2, "root + std");
		let std_name = compilation.interner.get("std").unwrap();
		assert!(compilation.package_by_name.contains_key(&std_name));
		let root = &compilation.packages[compilation.root_package.as_usize()];
		assert!(matches!(root.kind, PackageKind::Binary));
		assert_eq!(root.entry_path.as_str(), "/app/main.wx");
	}

	#[test]
	fn root_package_named_std_does_not_get_a_second_std_loaded() {
		let source = virtual_source(&[
			(
				"/app/wx.json",
				r#"{ "package": { "type": "lib", "name": "std" } }"#,
			),
			("/app/main.wx", "fn add() {}"),
		]);
		let compilation =
			open_package(AbsolutePath::new("/app/main.wx"), &source).unwrap();

		assert_eq!(
			compilation.packages.len(),
			1,
			"only the root, no embedded std"
		);
		let std_name = compilation.interner.get("std").unwrap();
		assert_eq!(
			compilation.package_by_name.get(&std_name),
			Some(&compilation.root_package)
		);
	}

	#[test]
	fn explicit_std_dependency_is_used_instead_of_the_embedded_one() {
		let source = virtual_source(&[
			(
				"/app/wx.json",
				r#"{
					"package": { "type": "bin" },
					"dependencies": {
						"std": { "type": "local", "path": "../alt_std" }
					}
				}"#,
			),
			("/app/main.wx", "fn add() {}"),
			(
				"/alt_std/wx.json",
				r#"{ "package": { "type": "lib", "name": "whatever_this_calls_itself" } }"#,
			),
			("/alt_std/main.wx", "fn replacement() {}"),
		]);
		let compilation =
			open_package(AbsolutePath::new("/app/main.wx"), &source).unwrap();

		assert_eq!(
			compilation.packages.len(),
			2,
			"root + alt_std, no embedded std"
		);
		let std_name = compilation.interner.get("std").unwrap();
		let alt_std_id = *compilation.package_by_name.get(&std_name).unwrap();
		let alt_std = &compilation.packages[alt_std_id.as_usize()];
		assert_eq!(alt_std.entry_path.as_str(), "/alt_std/main.wx");
		assert!(
			alt_std.linker_diagnostics.is_empty(),
			"the replacement's own internal name shouldn't matter at all"
		);
	}

	#[test]
	fn two_different_dependencies_claiming_the_same_key_is_diagnosed() {
		let source = virtual_source(&[
			(
				"/app/wx.json",
				r#"{
					"package": { "type": "bin" },
					"dependencies": {
						"libx": { "type": "local", "path": "../x" },
						"liby": { "type": "local", "path": "../y" }
					}
				}"#,
			),
			("/app/main.wx", "fn add() {}"),
			(
				"/x/wx.json",
				r#"{ "package": { "type": "lib", "name": "x" } }"#,
			),
			("/x/main.wx", "fn from_x() {}"),
			(
				"/y/wx.json",
				r#"{
					"package": { "type": "bin" },
					"dependencies": {
						"libx": { "type": "local", "path": "../z" }
					}
				}"#,
			),
			("/y/main.wx", "fn from_y() {}"),
			(
				"/z/wx.json",
				r#"{ "package": { "type": "lib", "name": "z" } }"#,
			),
			("/z/main.wx", "fn from_z() {}"),
		]);
		let compilation =
			open_package(AbsolutePath::new("/app/main.wx"), &source).unwrap();

		let all_diagnostics: Vec<_> = compilation
			.packages
			.iter()
			.flat_map(|p| p.linker_diagnostics.iter())
			.collect();
		assert!(
			all_diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::DuplicatePackageName.code())),
			"expected a duplicate-name diagnostic; got: {:?}",
			all_diagnostics
				.iter()
				.map(|d| &d.message)
				.collect::<Vec<_>>()
		);
	}

	#[test]
	fn diamond_dependency_is_loaded_only_once() {
		let source = virtual_source(&[
			(
				"/app/wx.json",
				r#"{
					"package": { "type": "bin" },
					"dependencies": {
						"a": { "type": "local", "path": "../a" },
						"b": { "type": "local", "path": "../b" }
					}
				}"#,
			),
			("/app/main.wx", "fn add() {}"),
			(
				"/a/wx.json",
				r#"{
					"package": { "type": "lib", "name": "a" },
					"dependencies": {
						"shared": { "type": "local", "path": "../shared" }
					}
				}"#,
			),
			("/a/main.wx", "fn from_a() {}"),
			(
				"/b/wx.json",
				r#"{
					"package": { "type": "lib", "name": "b" },
					"dependencies": {
						"shared": { "type": "local", "path": "../shared" }
					}
				}"#,
			),
			("/b/main.wx", "fn from_b() {}"),
			(
				"/shared/wx.json",
				r#"{ "package": { "type": "lib", "name": "shared" } }"#,
			),
			("/shared/main.wx", "fn from_shared() {}"),
		]);
		let compilation =
			open_package(AbsolutePath::new("/app/main.wx"), &source).unwrap();

		assert_eq!(
			compilation.packages.len(),
			5,
			"app, std, a, b, shared — shared loaded exactly once despite two paths to it"
		);
		let all_diagnostics: Vec<_> = compilation
			.packages
			.iter()
			.flat_map(|p| p.linker_diagnostics.iter())
			.collect();
		assert!(
			all_diagnostics.is_empty(),
			"a diamond dependency isn't a collision; got: {:?}",
			all_diagnostics
				.iter()
				.map(|d| &d.message)
				.collect::<Vec<_>>()
		);
	}

	#[test]
	fn circular_dependency_is_diagnosed_without_infinite_recursion() {
		let source = virtual_source(&[
			(
				"/a/wx.json",
				r#"{
					"package": { "type": "lib", "name": "a" },
					"dependencies": {
						"b": { "type": "local", "path": "../b" }
					}
				}"#,
			),
			("/a/main.wx", "fn from_a() {}"),
			(
				"/b/wx.json",
				r#"{
					"package": { "type": "lib", "name": "b" },
					"dependencies": {
						"a": { "type": "local", "path": "../a" }
					}
				}"#,
			),
			("/b/main.wx", "fn from_b() {}"),
		]);
		let compilation =
			open_package(AbsolutePath::new("/a/main.wx"), &source).unwrap();

		let all_diagnostics: Vec<_> = compilation
			.packages
			.iter()
			.flat_map(|p| p.linker_diagnostics.iter())
			.collect();
		assert!(
			all_diagnostics.iter().any(|d| d.code.as_deref()
				== Some(DiagnosticCode::CircularDependency.code())),
			"expected a circular-dependency diagnostic; got: {:?}",
			all_diagnostics
				.iter()
				.map(|d| &d.message)
				.collect::<Vec<_>>()
		);
	}
}
