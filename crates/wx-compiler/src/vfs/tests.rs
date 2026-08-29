use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use super::*;
use crate::testing::DiagnosticView;

/// Builds a [`VirtualFileSource`] from `(path, source)` pairs.
///
/// Module resolution only ever asks a [`FileSource`] whether a path
/// [`exists`](FileSource::exists) and to
/// [`read_to_string`](FileSource::read_to_string) it, so a directory layout
/// is just two keys: `/src/math.wx` and `/src/math/mod.wx` sit side by side
/// here exactly as they would on disk. The one thing that does differ,
/// [`FileOrigin`], is read only by wx-lsp when building URIs and has no
/// bearing on loading.
pub(super) fn workspace(files: &[(&str, &str)]) -> VirtualFileSource {
	VirtualFileSource::new(
		files
			.iter()
			.map(|(path, source)| {
				(AbsolutePath::new(*path), source.to_string())
			})
			.collect(),
	)
}

/// One package loaded from virtual files, kept together with the builder
/// that produced it so diagnostics can be rendered against its `Files`.
struct TestCase {
	builder: CompilationUnitBuilder,
	package: PackageId,
}

impl TestCase {
	/// Loads `files` as a binary package rooted at `entry`, which must be
	/// readable — a missing entry file is a hard error rather than a
	/// diagnostic, and has its own test.
	fn binary(entry: &str, files: &[(&str, &str)]) -> Self {
		let mut builder = CompilationUnitBuilder::new();
		let package = builder
			.load_binary(AbsolutePath::new(entry), &workspace(files))
			.expect("the entry file is readable");
		TestCase { builder, package }
	}

	fn graph(&self) -> &PackageGraph {
		&self.builder.packages[self.package.as_usize()]
	}

	/// Diagnostics raised while resolving this package's `mod` declarations
	/// to files.
	///
	/// Scoped to the one package rather than going through
	/// [`CompilationUnit::link_diagnostics`]: these tests stop at
	/// `load_binary` and never `build()`, since building demands a stdlib
	/// that a single-package module-resolution test has no use for.
	fn diagnostics(&self) -> DiagnosticView<'_> {
		DiagnosticView::new(
			"link",
			&self.graph().diagnostics,
			&self.builder.files,
		)
	}

	fn root_module(&self) -> &SourceModule {
		&self.graph().modules[self.graph().root.as_usize()]
	}

	/// The `index`-th child of `module`, resolved through the package's own
	/// module arena — `module.children` holds ids, not modules.
	fn child<'a>(
		&'a self,
		module: &'a SourceModule,
		index: usize,
	) -> &'a SourceModule {
		&self.graph().modules[module.children[index].as_usize()]
	}

	fn name(&self, symbol: SymbolU32) -> &str {
		self.builder
			.interner
			.resolve(symbol)
			.expect("symbol was interned while loading")
	}
}

/// A real directory that removes itself on drop.
///
/// The manual `fs::remove_*` calls this replaces sat at the end of each test
/// body, after the assertions — so any failing assertion leaked the directory
/// and everything in it, permanently, on every run.
struct TempDir(PathBuf);

impl TempDir {
	fn new(name: &str) -> Self {
		let unique = SystemTime::now()
			.duration_since(UNIX_EPOCH)
			.unwrap()
			.as_nanos();
		let path = std::env::temp_dir()
			.join(format!("wx-vfs-{name}-{}-{unique}", std::process::id()));
		fs::create_dir_all(&path).unwrap();
		TempDir(path)
	}

	/// Writes `contents` to `relative`, creating any directories it names.
	fn write(&self, relative: &str, contents: &str) -> PathBuf {
		let path = self.0.join(relative);
		fs::create_dir_all(path.parent().unwrap()).unwrap();
		fs::write(&path, contents).unwrap();
		path
	}
}

impl Drop for TempDir {
	fn drop(&mut self) {
		let _ = fs::remove_dir_all(&self.0);
	}
}

fn as_absolute(path: &Path) -> AbsolutePath {
	AbsolutePath::new(path.to_str().unwrap())
}

#[test]
fn load_package_parses_entry_file() {
	let case = TestCase::binary(
		"/main.wx",
		&[("/main.wx", "mod math;"), ("/math.wx", "fn add() {} ")],
	);
	case.diagnostics().assert_none();
	assert_eq!(case.graph().modules.len(), 2);

	let root = case.root_module();
	assert_eq!(root.children.len(), 1);

	let child = case.child(root, 0);
	let declaration = child.declaration.as_ref().unwrap();
	assert_eq!(declaration.parent, case.graph().root);
	assert_eq!(case.name(declaration.name.inner), "math");
}

#[test]
fn load_package_reports_missing_entry_file() {
	let mut builder = CompilationUnitBuilder::new();
	assert_eq!(
		builder.load_binary(AbsolutePath::new("/missing.wx"), &workspace(&[])),
		Err(()),
		"expected missing entry file to be a fatal error, not a diagnostic \
		 — there's no package to build without it"
	);
}

#[test]
fn load_package_diagnoses_missing_child_module_without_aborting() {
	// Regression test: `mod boo;` referencing a file that doesn't exist
	// yet used to abort loading the entire package. It should instead produce
	// a diagnostic attached to the `mod boo;` declaration and let the
	// rest of the package — including other, unrelated top-level items in the
	// same file — still load normally.
	let case = TestCase::binary(
		"/main.wx",
		&[("/main.wx", "mod boo;\nfn works() -> i32 { 1 }")],
	);

	let root = case.root_module();
	assert_eq!(
		root.children.len(),
		0,
		"the unresolved `boo` module should be omitted, not present as a stub"
	);
	assert!(
		root.ast.items.iter().any(|item| matches!(
			&item.inner.inner,
			ast::Item::Function { .. }
		)),
		"the rest of main.wx should still parse normally"
	);
	case.diagnostics()
		.assert_error(DiagnosticCode::ModuleFileNotFound);
}

#[test]
fn load_package_rejects_ambiguous_module_paths() {
	// Both `math.wx` and `math/mod.wx` could satisfy `mod math;`.
	let case = TestCase::binary(
		"/main.wx",
		&[
			("/main.wx", "mod math;"),
			("/math.wx", "fn from_file() {}"),
			("/math/mod.wx", "fn from_dir() {}"),
		],
	);

	assert_eq!(
		case.root_module().children.len(),
		0,
		"the ambiguous module should be omitted rather than arbitrarily picked"
	);
	case.diagnostics()
		.assert_error(DiagnosticCode::AmbiguousModuleFile);
}

#[test]
fn load_package_resolves_module_directory_file() {
	// The one test that goes through `NativeFileSource`. Everything else here
	// runs on `VirtualFileSource`, which shares no code with the real
	// filesystem beyond the `FileSource` trait — so without this, nothing
	// would exercise actual directory traversal or path normalisation.
	let dir = TempDir::new("dir-module-root");
	let entry = dir.write("main.wx", "mod math;");
	let child_path = dir.write("math/mod.wx", "fn add() {}");

	let mut builder = CompilationUnitBuilder::new();
	let package_id = builder
		.load_binary(as_absolute(&entry), &NativeFileSource)
		.unwrap();
	let graph = &builder.packages[package_id.as_usize()];

	let root = &graph.modules[graph.root.as_usize()];
	let child = &graph.modules[root.children[0].as_usize()];
	assert_eq!(
		child.file_path.as_str(),
		child_path.to_str().unwrap().replace('\\', "/")
	);
}

#[test]
fn load_virtual_compilation_resolves_child_modules_from_workspace_files() {
	let mut builder = CompilationUnitBuilder::new();
	builder.load_stdlib();
	let root_id = builder
		.load_binary(
			AbsolutePath::new("/src/main.wx"),
			&workspace(&[
				("/src/main.wx", "mod math;"),
				("/src/math.wx", "fn add() {}"),
			]),
		)
		.expect("failed to load package");
	let graph = builder.build(root_id);

	let entry_package = &graph.packages[1];
	assert_eq!(entry_package.modules.len(), 2);
	let root = &entry_package.modules[entry_package.root.as_usize()];
	assert_eq!(root.file_path.as_str(), "/src/main.wx");
	assert_eq!(root.children.len(), 1);

	let child = &entry_package.modules[root.children[0].as_usize()];
	assert_eq!(child.file_path.as_str(), "/src/math.wx");
}

#[test]
fn load_virtual_compilation_child_of_a_sibling_file_module_resolves_under_its_own_name()
 {
	// A module's own children always resolve under a directory named after
	// *that module* — `a.wx` declaring `mod shared;` looks for
	// `/src/a/shared.wx`, not `/src/shared.wx`, regardless of `a.wx` being
	// the plain-sibling form rather than `a/mod.wx`. Placing `shared.wx` at
	// `/src/shared.wx` (the pre-fix resolution target, and formerly also
	// reachable from a second sibling `b.wx` — a silent, asymmetric
	// collision between the two) is now simply the wrong location, and
	// reported as an honest, ordinary `ModuleFileNotFound`.
	let case = TestCase::binary(
		"/src/main.wx",
		&[
			("/src/main.wx", "mod a;"),
			("/src/a.wx", "mod shared;"),
			("/src/shared.wx", "pub fn x() -> i32 { 1 }"),
		],
	);

	let a = case.child(case.root_module(), 0);
	assert_eq!(
		a.children.len(),
		0,
		"the unresolved `shared` module should be omitted, not present as \
		 a stub"
	);
	case.diagnostics()
		.assert_error(DiagnosticCode::ModuleFileNotFound);
}

#[test]
fn load_package_diagnoses_module_declaration_nested_inside_inline_module() {
	// `mod extra;` inside an inline `mod utils { }` block is not a
	// legal declaration site — unlike Rust, wx doesn't resolve it by
	// accumulating a directory segment per inline level. It should be
	// diagnosed, not silently ignored, and the surrounding file should
	// still load its own top-level items normally.
	let case = TestCase::binary(
		"/main.wx",
		&[(
			"/main.wx",
			"mod utils { mod extra; }\nfn works() -> i32 { 1 }",
		)],
	);

	assert_eq!(
		case.graph().modules.len(),
		1,
		"the nested `extra` declaration should not cause a file to load"
	);
	case.diagnostics()
		.assert_error(DiagnosticCode::NestedModuleDeclaration);
}
