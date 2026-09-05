use std::collections::HashMap;

use codespan_reporting::diagnostic::Diagnostic;

use super::manifest::ResolvedDependency;
use super::{
	AbsolutePath, CompilationUnit, CompilationUnitBuilder, DependencySource,
	DiagnosticCode, FileId, FileSource, PackageId, PackageKind,
	PackageManifest, PackageManifestKind, PackageName, RelativePath,
};

/// Maps a manifest's declared `"type"` to the resolved `PackageKind` used
/// at runtime. No name is involved: what a package is
/// called is decided by whoever depends on it, and is threaded separately
/// (see `open_manifest_package`).
///
/// `Std` collapses to `Library` deliberately — being the stdlib is not a
/// different kind of package, it's an ordinary library that additionally
/// happens to be `CompilationUnit::stdlib_package`. Everything a library
/// can't do (`export`, `memory`, ...) a stdlib can't do either, so the two
/// must not diverge here.
pub fn package_kind(kind: &PackageManifestKind) -> PackageKind {
	match kind {
		PackageManifestKind::Bin => PackageKind::Binary,
		PackageManifestKind::Lib | PackageManifestKind::Std => {
			PackageKind::Library
		}
	}
}

/// Loads the package whose manifest lives at `{dir}/wx.json` as the root of
/// a compilation, resolving every dependency it declares. Requires a
/// manifest to exist — there's no anonymous, manifest-less fallback; every
/// compilation belongs to a project, the same rule `wx format` follows.
///
/// `dir` is always absolute — every frontend is responsible for making it
/// so before calling this (joining a CLI argument against
/// `std::env::current_dir()`, or following the synthetic `/`-rooted
/// convention `VirtualFileSource`-backed compilations use).
///
/// The manifest's `entry` field (relative to `dir`) says where compilation
/// starts, regardless of `type` — see the design doc for why entry-point
/// resolution never varies with kind. Every `dependencies` entry is then
/// resolved recursively, relative to *its declaring* manifest's own
/// directory. The embedded stdlib is loaded first, before the root and
/// before any dependency, unless the root declares `"type": "std"` and so
/// provides it itself. That is the whole of the implicit-`std` rule: the
/// stdlib is not replaceable, so there is no override path and no
/// reserved-key check — a dependency bound to the key `std` simply loses
/// the first-claim-wins race and gets `DuplicatePackageName`.
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
pub fn open_manifest(
	dir: AbsolutePath,
	source: &impl FileSource,
) -> Result<CompilationUnit, ()> {
	open_manifest_with_manifests(dir, source, &HashMap::new())
}

/// Uses retained manifest data supplied by a frontend. Entries not supplied
/// are read through the same FileSource as modules. The data is only an input
/// to resolution; no manifest is stored on the resulting CompilationUnit.
pub fn open_manifest_with_manifests(
	dir: AbsolutePath,
	source: &impl FileSource,
	manifests: &HashMap<AbsolutePath, &PackageManifest>,
) -> Result<CompilationUnit, ()> {
	let mut resolution = DependencyResolution {
		manifests,
		resolved: HashMap::new(),
		in_progress: HashMap::new(),
	};
	let mut builder = CompilationUnitBuilder::new();

	// Loaded here rather than through `open_manifest_package` because two
	// things are true of the root and of nothing else: it has no name
	// (nothing in this compilation depends on it), and its `"type"` is the
	// only one that can decide whether a stdlib is loaded at all. Both are
	// properties of *being* the root, so threading them through the
	// recursion would mean every dependency carrying parameters only the
	// outermost call could ever use.
	let loaded;
	let manifest = if let Some(manifest) = manifests.get(&dir) {
		*manifest
	} else {
		let text =
			source.read_to_string(&dir.join(&RelativePath::new("wx.json")))?;
		loaded = PackageManifest::parse(&text).map_err(|_| ())?;
		&loaded
	};
	let entry_path = dir.join(&manifest.entry);
	let kind = package_kind(&manifest.kind);

	// The two kinds differ in *when* the stdlib is established relative to
	// the root, which is the whole of the implicit-`std` rule — so the
	// ordering lives in the arms rather than in flags read further down.
	let root_id = match manifest.kind {
		// The root provides the tagged items itself, so no embedded stdlib
		// is loaded. Marked after loading, so it isn't listed as its own
		// dependency; everything resolved below still sees it.
		PackageManifestKind::Std => {
			let root_id = builder.load_package(kind, entry_path, source)?;
			builder.set_stdlib(root_id);
			root_id
		}
		// Established first, so the root gets `std` seeded into its
		// dependencies like every other package.
		PackageManifestKind::Lib | PackageManifestKind::Bin => {
			builder.load_stdlib();
			builder.load_package(kind, entry_path, source)?
		}
	};

	resolve_dependencies(
		&mut builder,
		root_id,
		&dir,
		&manifest.dependencies,
		source,
		&mut resolution,
	)?;

	Ok(builder.build(root_id))
}

struct DependencyResolution<'a> {
	manifests: &'a HashMap<AbsolutePath, &'a PackageManifest>,
	resolved: HashMap<ResolvedDependency, PackageId>,
	in_progress: HashMap<ResolvedDependency, PackageId>,
}

/// Loads the package whose manifest lives at `{dir}/wx.json`, then
/// recursively does the same for each of its `dependencies` — each
/// resolved relative to *this* manifest's own directory, never the
/// process's cwd, so a dependency chain composes correctly regardless of
/// where compilation started.
///
/// `name` is the declaring package's `dependencies` key. It is *not* stored
/// on the package loaded here — the binding belongs to the edge, and
/// `resolve_dependencies` records it on the declarer — so this only carries
/// it far enough to name it in a diagnostic.
///
/// Only ever called for dependencies — the root is loaded directly by
/// `open_manifest`. Being in this function is therefore itself the proof
/// that a package is *not* the root, which is what makes the `"type":
/// "std"` check below need no flag to tell the two cases apart.
///
/// Registers itself in `in_progress` under `identity` as soon as it has an
/// id and *before* recursing, so a dependency edge that points back here
/// finds a real package to bind its own name to rather than only a
/// diagnostic.
fn open_manifest_package(
	builder: &mut CompilationUnitBuilder,
	dir: &AbsolutePath,
	name: &PackageName,
	identity: &ResolvedDependency,
	source: &impl FileSource,
	resolution: &mut DependencyResolution<'_>,
) -> Result<PackageId, ()> {
	let loaded;
	let manifest = if let Some(manifest) = resolution.manifests.get(dir) {
		*manifest
	} else {
		let text =
			source.read_to_string(&dir.join(&RelativePath::new("wx.json")))?;
		loaded = PackageManifest::parse(&text).map_err(|_| ())?;
		&loaded
	};
	let entry_path = dir.join(&manifest.entry);

	let id = builder.load_package(
		package_kind(&manifest.kind),
		entry_path,
		source,
	)?;
	resolution.in_progress.insert(identity.clone(), id);

	// A stdlib can only ever be the root of its own compilation. Declaring
	// `"type": "std"` has exactly one effect — suppressing the embedded
	// stdlib — and that decision belongs to the root, so here it could only
	// ever be inert. Inert-but-accepted is the dangerous outcome: the
	// package would load as an ordinary library while its `#[tag = "..."]`
	// items still landed in the one compilation-wide `tagged_items` map,
	// silently competing for `add`/`sub`/... against the real stdlib's.
	if matches!(manifest.kind, PackageManifestKind::Std) {
		builder.packages[id.as_usize()]
			.diagnostics
			.push(report_std_package_as_dependency(name.as_str()));
	}

	resolve_dependencies(
		builder,
		id,
		dir,
		&manifest.dependencies,
		source,
		resolution,
	)?;
	resolution.in_progress.remove(identity);

	Ok(id)
}

/// Resolves every entry of one manifest's `dependencies` map, relative to
/// *that* manifest's own directory (`dir`) rather than the process's cwd, so
/// a dependency chain composes correctly regardless of where compilation
/// started. `owner` is the package that declared them — the one any
/// diagnostic about a bad edge is recorded against.
///
/// `resolved` memoizes by [`DependencySource::resolve`]'s identity, so a
/// diamond dependency is only ever parsed and loaded once. `in_progress`
/// tracks the current recursion stack by that same identity: if a dependency
/// edge points back at something still `in_progress`, that's a cycle — this
/// still returns `Ok`, but records a `CircularDependency` diagnostic on the
/// package that made the cyclic reference and doesn't recurse into it again,
/// rather than failing resolution outright or recursing forever.
fn resolve_dependencies(
	builder: &mut CompilationUnitBuilder,
	owner: PackageId,
	dir: &AbsolutePath,
	dependencies: &HashMap<PackageName, DependencySource>,
	source: &impl FileSource,
	resolution: &mut DependencyResolution<'_>,
) -> Result<(), ()> {
	// Sorted so a name collision among dependencies is diagnosed the same
	// way on every run, not depending on `HashMap`'s randomized order.
	let mut dependencies: Vec<_> = dependencies.iter().collect();
	dependencies.sort_by_key(|(name, _)| *name);

	for (key, dependency) in dependencies {
		let identity = dependency.resolve(dir);

		// Every branch below yields a `PackageId` to bind `key` to, because
		// the name is a property of *this* edge: whether the target happens
		// to have been loaded already (a diamond), or is still being loaded
		// further up the stack (a cycle), `owner` still calls it `key`.
		let dependency_id = match (
			resolution.resolved.get(&identity),
			resolution.in_progress.get(&identity),
		) {
			// Diamond: reached by another edge already, so its modules are
			// loaded. Only the binding below is still owed.
			(Some(&loaded), _) => loaded,
			// Cycle: recursing again would not terminate, and the diagnostic
			// stands — but the package does exist, so the name still binds
			// and paths through it keep resolving.
			(None, Some(&pending)) => {
				builder.packages[owner.as_usize()]
					.diagnostics
					.push(report_circular_dependency(key.as_str()));
				pending
			}
			(None, None) => {
				let ResolvedDependency::Local(dependency_dir) = &identity;
				let id = open_manifest_package(
					builder,
					dependency_dir,
					key,
					&identity,
					source,
					resolution,
				)?;
				resolution.resolved.insert(identity, id);
				id
			}
		};

		let name = builder.interner.get_or_intern(key.as_str());
		builder.add_dependency(owner, name, dependency_id);
	}

	Ok(())
}

/// No label, for the same reason `report_duplicate_dependency_name` has
/// none: there's no span inside a `wx.json` to point at from here.
fn report_std_package_as_dependency(key: &str) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::StdPackageAsDependency.code())
		.with_message(format!(
			"dependency `{key}` declares `\"type\": \"std\"`: a standard \
			 library can only be the root of its own compilation, never a \
			 dependency of one"
		))
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
	use crate::testing::DiagnosticView;
	use crate::vfs::tests::workspace;

	/// What `owner` calls the package it reaches under `name`. Replaces the
	/// old global `package_by_name`: a name is a property of the edge, so
	/// asking "what is `std` here?" now requires saying *here*.
	fn dependency_of(
		compilation: &CompilationUnit,
		owner: PackageId,
		name: &str,
	) -> Option<PackageId> {
		let symbol = compilation.interner.get(name)?;
		compilation.packages[owner.as_usize()]
			.dependencies
			.get(&symbol)
			.copied()
	}

	#[test]
	fn retained_manifests_load_root_and_dependencies_without_json_reads() {
		struct Source {
			files: crate::vfs::VirtualFileSource,
			json_reads: std::cell::Cell<usize>,
		}
		impl FileSource for Source {
			fn read_to_string(
				&self,
				path: &AbsolutePath,
			) -> Result<String, ()> {
				if path.as_str().ends_with("/wx.json") {
					self.json_reads.set(self.json_reads.get() + 1);
					return Err(());
				}
				self.files.read_to_string(path)
			}
			fn exists(&self, path: &AbsolutePath) -> bool {
				self.files.exists(path)
			}
			fn origin(&self) -> crate::vfs::FileOrigin {
				crate::vfs::FileOrigin::Local
			}
		}
		let source = Source {
			files: workspace(&[
				("/app/main.wx", "fn main() {}"),
				("/dep/main.wx", "pub fn helper() {}"),
			]),
			json_reads: std::cell::Cell::new(0),
		};
		let app = PackageManifest::parse(r#"{"type":"bin","entry":"main.wx","dependencies":{"dep":{"type":"local","path":"../dep"}}}"#).unwrap();
		let dep = PackageManifest::parse(r#"{"type":"lib","entry":"main.wx"}"#)
			.unwrap();
		let manifests = HashMap::from([
			(AbsolutePath::new("/app"), &app),
			(AbsolutePath::new("/dep"), &dep),
		]);
		for _ in 0..2 {
			let graph = open_manifest_with_manifests(
				AbsolutePath::new("/app"),
				&source,
				&manifests,
			)
			.unwrap();
			assert!(dependency_of(&graph, graph.root_package, "dep").is_some());
		}
		assert_eq!(source.json_reads.get(), 0);
	}

	#[test]
	fn manifested_binary_with_no_dependencies_gets_std() {
		let source = workspace(&[
			("/app/wx.json", r#"{ "type": "bin", "entry": "main.wx" }"#),
			("/app/main.wx", "fn add() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		assert_eq!(compilation.packages.len(), 2, "root + std");
		assert_eq!(
			dependency_of(&compilation, compilation.root_package, "std"),
			Some(compilation.stdlib_package),
			"every package can reach the stdlib without declaring it"
		);
		let root = &compilation.packages[compilation.root_package.as_usize()];
		assert!(matches!(root.kind, PackageKind::Binary));
		assert_eq!(root.entry_path.as_str(), "/app/main.wx");
	}

	/// The `entry` field, not a hardcoded `main.wx` convention — proves the
	/// entry file can be named anything, and is resolved relative to the
	/// manifest's own directory.
	#[test]
	fn manifested_binary_resolves_a_non_conventional_entry_name() {
		let source = workspace(&[
			(
				"/app/wx.json",
				r#"{ "type": "bin", "entry": "src/start.wx" }"#,
			),
			("/app/src/start.wx", "fn add() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		let root = &compilation.packages[compilation.root_package.as_usize()];
		assert_eq!(root.entry_path.as_str(), "/app/src/start.wx");
	}

	#[test]
	fn manifest_directory_without_a_wx_json_fails() {
		let source = workspace(&[("/app/main.wx", "fn add() {}")]);
		assert!(
			open_manifest(AbsolutePath::new("/app"), &source).is_err(),
			"a directory argument commits to the manifest-driven path — no \
			 fallback to guessing an entry file"
		);
	}

	#[test]
	fn std_root_package_does_not_get_a_second_std_loaded() {
		let source = workspace(&[
			("/app/wx.json", r#"{ "type": "std", "entry": "main.wx" }"#),
			("/app/main.wx", "fn add() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		assert_eq!(
			compilation.packages.len(),
			1,
			"only the root, no embedded std"
		);
		assert_eq!(compilation.stdlib_package, compilation.root_package);
		assert_eq!(
			dependency_of(&compilation, compilation.root_package, "std"),
			None,
			"a stdlib doesn't depend on itself — nothing seeds `std` into \
			 the package that provides it"
		);
	}

	/// The stdlib isn't replaceable, and this is how that's enforced: it's
	/// loaded before anything else, so a dependency bound to `std` loses the
	/// first-claim-wins race rather than needing a reserved-key check.
	#[test]
	fn dependency_bound_to_std_collides_with_the_stdlib() {
		let source = workspace(&[
			(
				"/app/wx.json",
				r#"{
					"type": "bin",
					"entry": "main.wx",
					"dependencies": {
						"std": { "type": "local", "path": "../alt_std" }
					}
				}"#,
			),
			("/app/main.wx", "fn add() {}"),
			(
				"/alt_std/wx.json",
				r#"{ "type": "lib", "entry": "main.wx" }"#,
			),
			("/alt_std/main.wx", "fn replacement() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		assert_eq!(
			dependency_of(&compilation, compilation.root_package, "std"),
			Some(compilation.stdlib_package),
			"the seeded stdlib holds the name; the declared one can't take it"
		);

		let diagnostics = compilation.collect_linker_diagnostics();
		DiagnosticView::new("link", &diagnostics, &compilation.files)
			.assert_error(DiagnosticCode::DuplicatePackageName);
	}

	/// `"type": "std"` says "suppress the embedded stdlib for this
	/// compilation" — a decision only the root can make. A dependency
	/// declaring it would be inert, while its `#[tag]` items still competed
	/// with the real stdlib's, so it's rejected rather than ignored.
	#[test]
	fn std_package_as_a_dependency_is_diagnosed() {
		let source = workspace(&[
			(
				"/app/wx.json",
				r#"{
					"type": "bin",
					"entry": "main.wx",
					"dependencies": {
						"mystd": { "type": "local", "path": "../mystd" }
					}
				}"#,
			),
			("/app/main.wx", "fn add() {}"),
			("/mystd/wx.json", r#"{ "type": "std", "entry": "main.wx" }"#),
			("/mystd/main.wx", "fn replacement() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		assert_eq!(
			compilation.packages.len(),
			3,
			"std, root, mystd — the embedded stdlib is still loaded"
		);
		assert_eq!(
			dependency_of(&compilation, compilation.root_package, "std"),
			Some(compilation.stdlib_package),
			"a `std`-kind dependency does not become the stdlib provider"
		);

		let diagnostics = compilation.collect_linker_diagnostics();
		DiagnosticView::new("link", &diagnostics, &compilation.files)
			.assert_error(DiagnosticCode::StdPackageAsDependency);
	}

	/// Inverted deliberately. Under the old model a name was a property of
	/// the package, so two packages reached under the same key collided
	/// globally. A name is now a property of the edge, so `app` calling `/x`
	/// "libx" and `y` calling `/z` "libx" are two independent bindings in
	/// two different maps — the whole point of edge-scoped names, and not
	/// something to diagnose.
	#[test]
	fn one_package_declared_under_two_names_is_diagnosed() {
		// The inverse of `two_packages_may_use_the_same_key_for_different_
		// targets`: there, two owners each bind `libx` to a target of their
		// own, which is fine. Here one owner reaches the *same* package twice
		// under different keys, which is not — a `dependencies` entry is a
		// declaration, so the mapping is kept one-to-one in both directions
		// and a second name has to be spelled with an alias instead.
		let source = workspace(&[
			(
				"/app/wx.json",
				r#"{
					"type": "bin",
					"entry": "main.wx",
					"dependencies": {
						"one": { "type": "local", "path": "../shared" },
						"two": { "type": "local", "path": "../shared" }
					}
				}"#,
			),
			("/app/main.wx", "fn add() {}"),
			(
				"/shared/wx.json",
				r#"{ "type": "lib", "entry": "main.wx" }"#,
			),
			("/shared/main.wx", "fn shared() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		let diagnostics = compilation.collect_linker_diagnostics();
		DiagnosticView::new("link", &diagnostics, &compilation.files)
			.assert_error(DiagnosticCode::PackageDeclaredTwice);

		// The first key still binds — the package loaded, it just cannot be
		// reached under both names.
		assert!(
			dependency_of(&compilation, compilation.root_package, "one")
				.is_some(),
			"the first declaration should still bind its name"
		);
	}

	#[test]
	fn two_packages_may_use_the_same_key_for_different_targets() {
		let source = workspace(&[
			(
				"/app/wx.json",
				r#"{
					"type": "bin",
					"entry": "main.wx",
					"dependencies": {
						"libx": { "type": "local", "path": "../x" },
						"liby": { "type": "local", "path": "../y" }
					}
				}"#,
			),
			("/app/main.wx", "fn add() {}"),
			("/x/wx.json", r#"{ "type": "lib", "entry": "main.wx" }"#),
			("/x/main.wx", "fn from_x() {}"),
			(
				"/y/wx.json",
				r#"{
					"type": "bin",
					"entry": "main.wx",
					"dependencies": {
						"libx": { "type": "local", "path": "../z" }
					}
				}"#,
			),
			("/y/main.wx", "fn from_y() {}"),
			("/z/wx.json", r#"{ "type": "lib", "entry": "main.wx" }"#),
			("/z/main.wx", "fn from_z() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		// The same key in two different packages is not a collision.
		let diagnostics = compilation.collect_linker_diagnostics();
		DiagnosticView::new("link", &diagnostics, &compilation.files)
			.assert_none();

		// Each `libx` resolves within its own package, to a different target.
		let app = compilation.root_package;
		let y = dependency_of(&compilation, app, "liby").unwrap();
		assert_ne!(
			dependency_of(&compilation, app, "libx"),
			dependency_of(&compilation, y, "libx"),
			"`libx` means `/x` in `app` and `/z` in `y`"
		);
	}

	#[test]
	fn diamond_dependency_is_loaded_only_once() {
		let source = workspace(&[
			(
				"/app/wx.json",
				r#"{
					"type": "bin",
					"entry": "main.wx",
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
					"type": "lib",
					"entry": "main.wx",
					"dependencies": {
						"shared": { "type": "local", "path": "../shared" }
					}
				}"#,
			),
			("/a/main.wx", "fn from_a() {}"),
			(
				"/b/wx.json",
				r#"{
					"type": "lib",
					"entry": "main.wx",
					"dependencies": {
						"shared": { "type": "local", "path": "../shared" }
					}
				}"#,
			),
			("/b/main.wx", "fn from_b() {}"),
			(
				"/shared/wx.json",
				r#"{ "type": "lib", "entry": "main.wx" }"#,
			),
			("/shared/main.wx", "fn from_shared() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/app"), &source).unwrap();

		assert_eq!(
			compilation.packages.len(),
			5,
			"app, std, a, b, shared — shared loaded exactly once despite two paths to it"
		);
		// A diamond dependency isn't a collision.
		let diagnostics = compilation.collect_linker_diagnostics();
		DiagnosticView::new("link", &diagnostics, &compilation.files)
			.assert_none();
	}

	#[test]
	fn circular_dependency_is_diagnosed_without_infinite_recursion() {
		let source = workspace(&[
			(
				"/a/wx.json",
				r#"{
					"type": "lib",
					"entry": "main.wx",
					"dependencies": {
						"b": { "type": "local", "path": "../b" }
					}
				}"#,
			),
			("/a/main.wx", "fn from_a() {}"),
			(
				"/b/wx.json",
				r#"{
					"type": "lib",
					"entry": "main.wx",
					"dependencies": {
						"a": { "type": "local", "path": "../a" }
					}
				}"#,
			),
			("/b/main.wx", "fn from_b() {}"),
		]);
		let compilation =
			open_manifest(AbsolutePath::new("/a"), &source).unwrap();

		let all_diagnostics: Vec<_> = compilation
			.packages
			.iter()
			.flat_map(|p| p.diagnostics.iter())
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
