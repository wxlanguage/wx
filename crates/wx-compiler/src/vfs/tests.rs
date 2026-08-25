use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

use super::*;

fn temp_test_dir(test_name: &str) -> PathBuf {
	let unique = SystemTime::now()
		.duration_since(UNIX_EPOCH)
		.unwrap()
		.as_nanos();
	let path = std::env::temp_dir().join(format!(
		"wx-vfs-{test_name}-{}-{unique}",
		std::process::id()
	));
	fs::create_dir(&path).unwrap();
	path
}

#[test]
fn load_package_parses_entry_file() {
	let dir = temp_test_dir("root");
	let path = dir.join("main.wx");
	let child_path = dir.join("math.wx");
	fs::write(&path, "module math;").unwrap();
	fs::write(&child_path, "fn add() {} ").unwrap();

	let mut builder = CompilationUnitBuilder::new();
	let package_id = builder
		.load_binary(
			AbsolutePath::new(path.to_str().unwrap()),
			&NativeFileSource,
		)
		.unwrap();
	let graph = &builder.packages[package_id.as_u32() as usize];

	assert_eq!(graph.modules.len(), 2);

	let root = &graph.modules[graph.root.as_u32() as usize];
	assert_eq!(root.children.len(), 1);

	let child = &graph.modules[root.children[0].as_u32() as usize];
	let declaration = child.declaration.as_ref().unwrap();
	assert_eq!(declaration.parent, graph.root);
	assert_eq!(
		builder.interner.resolve(declaration.name.inner),
		Some("math")
	);

	fs::remove_file(&path).unwrap();
	fs::remove_file(&child_path).unwrap();
	fs::remove_dir(&dir).unwrap();
}

#[test]
fn load_package_reports_missing_entry_file() {
	let dir = temp_test_dir("missing");
	let path = dir.join("missing.wx");
	let path_str = path.to_str().unwrap().to_string();

	let mut builder = CompilationUnitBuilder::new();
	assert_eq!(
		builder.load_binary(AbsolutePath::new(path_str), &NativeFileSource),
		Err(()),
		"expected missing entry file to be a fatal error, not a diagnostic \
		 — there's no package to build without it"
	);

	fs::remove_dir(&dir).unwrap();
}

#[test]
fn load_package_diagnoses_missing_child_module_without_aborting() {
	// Regression test: `module boo;` referencing a file that doesn't exist
	// yet used to abort loading the entire package. It should instead produce
	// a diagnostic attached to the `module boo;` declaration and let the
	// rest of the package — including other, unrelated top-level items in the
	// same file — still load normally.
	let dir = temp_test_dir("missing-child-module");
	let path = dir.join("main.wx");
	fs::write(&path, "module boo;\nfn works() -> i32 { 1 }").unwrap();

	let mut builder = CompilationUnitBuilder::new();
	let package_id = builder
		.load_binary(
			AbsolutePath::new(path.to_str().unwrap()),
			&NativeFileSource,
		)
		.expect(
			"a missing child module should be a diagnostic, not a fatal \
			 error — the entry file itself is still readable",
		);
	let graph = &builder.packages[package_id.as_u32() as usize];

	let root = &graph.modules[graph.root.as_u32() as usize];
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
	assert!(
		graph.linker_diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::ModuleFileNotFound.code())),
		"expected a module-not-found diagnostic; got: {:?}",
		graph
			.linker_diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	fs::remove_file(&path).unwrap();
	fs::remove_dir(&dir).unwrap();
}

#[test]
fn load_package_resolves_module_directory_file() {
	let dir = temp_test_dir("dir-module-root");
	let path = dir.join("main.wx");
	let child_dir = dir.join("math");
	let child_path = child_dir.join("mod.wx");
	fs::create_dir(&child_dir).unwrap();
	fs::write(&path, "module math;").unwrap();
	fs::write(&child_path, "fn add() {}").unwrap();

	let mut builder = CompilationUnitBuilder::new();
	let package_id = builder
		.load_binary(
			AbsolutePath::new(path.to_str().unwrap()),
			&NativeFileSource,
		)
		.unwrap();
	let graph = &builder.packages[package_id.as_u32() as usize];

	let root = &graph.modules[graph.root.as_u32() as usize];
	let child = &graph.modules[root.children[0].as_u32() as usize];
	assert_eq!(
		child.file_path.as_str(),
		child_path.to_str().unwrap().replace('\\', "/")
	);

	fs::remove_file(&path).unwrap();
	fs::remove_file(&child_path).unwrap();
	fs::remove_dir(&child_dir).unwrap();
	fs::remove_dir(&dir).unwrap();
}

#[test]
fn load_package_rejects_ambiguous_module_paths() {
	let dir = temp_test_dir("ambiguous-module-root");
	let path = dir.join("main.wx");
	let sibling_path = dir.join("math.wx");
	let child_dir = dir.join("math");
	let directory_path = child_dir.join("mod.wx");
	fs::create_dir(&child_dir).unwrap();
	fs::write(&path, "module math;").unwrap();
	fs::write(&sibling_path, "fn from_file() {}").unwrap();
	fs::write(&directory_path, "fn from_dir() {}").unwrap();

	let mut builder = CompilationUnitBuilder::new();
	let package_id = builder
		.load_binary(
			AbsolutePath::new(path.to_str().unwrap()),
			&NativeFileSource,
		)
		.expect(
			"an ambiguous child module should be a diagnostic, not a fatal \
			 error — the package itself still loads",
		);
	let graph = &builder.packages[package_id.as_u32() as usize];

	let root = &graph.modules[graph.root.as_u32() as usize];
	assert_eq!(
		root.children.len(),
		0,
		"the ambiguous module should be omitted rather than arbitrarily picked"
	);
	assert!(
		graph.linker_diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::AmbiguousModuleFile.code())),
		"expected an ambiguous-module diagnostic; got: {:?}",
		graph
			.linker_diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>()
	);

	fs::remove_file(&path).unwrap();
	fs::remove_file(&sibling_path).unwrap();
	fs::remove_file(&directory_path).unwrap();
	fs::remove_dir(&child_dir).unwrap();
	fs::remove_dir(&dir).unwrap();
}

#[test]
fn load_virtual_compilation_resolves_child_modules_from_workspace_files() {
	let mut builder = CompilationUnitBuilder::new();
	builder.load_stdlib();
	let root_id = builder
		.load_binary(
			AbsolutePath::new("/src/main.wx"),
			&VirtualFileSource::new(HashMap::from([
				(
					AbsolutePath::new("/src/main.wx"),
					"module math;".to_string(),
				),
				(AbsolutePath::new("/src/math.wx"), "fn add() {}".to_string()),
			])),
		)
		.expect("failed to load package");
	let graph = builder.build(root_id);

	let entry_package = &graph.packages[1];
	assert_eq!(entry_package.modules.len(), 2);
	let root = &entry_package.modules[entry_package.root.as_u32() as usize];
	assert_eq!(root.file_path.as_str(), "/src/main.wx");
	assert_eq!(root.children.len(), 1);

	let child = &entry_package.modules[root.children[0].as_u32() as usize];
	assert_eq!(child.file_path.as_str(), "/src/math.wx");
}

#[test]
fn load_virtual_compilation_child_of_a_sibling_file_module_resolves_under_its_own_name()
 {
	// A module's own children always resolve under a directory named after
	// *that module* — `a.wx` declaring `module shared;` looks for
	// `/src/a/shared.wx`, not `/src/shared.wx`, regardless of `a.wx` being
	// the plain-sibling form rather than `a/mod.wx`. Placing `shared.wx` at
	// `/src/shared.wx` (the pre-fix resolution target, and formerly also
	// reachable from a second sibling `b.wx` — a silent, asymmetric
	// collision between the two) is now simply the wrong location, and
	// reported as an honest, ordinary `ModuleFileNotFound`.
	let mut builder = CompilationUnitBuilder::new();
	builder.load_stdlib();
	let root_id = builder
		.load_binary(
			AbsolutePath::new("/src/main.wx"),
			&VirtualFileSource::new(HashMap::from([
				(AbsolutePath::new("/src/main.wx"), "module a;".to_string()),
				(AbsolutePath::new("/src/a.wx"), "module shared;".to_string()),
				(
					AbsolutePath::new("/src/shared.wx"),
					"pub fn x() -> i32 { 1 }".to_string(),
				),
			])),
		)
		.expect("a.wx itself is still readable");
	let graph = &builder.packages[root_id.as_u32() as usize];

	let root = &graph.modules[graph.root.as_u32() as usize];
	let a = &graph.modules[root.children[0].as_u32() as usize];
	assert_eq!(
		a.children.len(),
		0,
		"the unresolved `shared` module should be omitted, not present as \
		 a stub"
	);
	assert!(
		graph.linker_diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::ModuleFileNotFound.code())),
		"expected E2000 (ModuleFileNotFound), got: {:?}",
		graph
			.linker_diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}

#[test]
fn load_package_diagnoses_module_declaration_nested_inside_inline_module() {
	// `module extra;` inside an inline `module utils { }` block is not a
	// legal declaration site — unlike Rust, wx doesn't resolve it by
	// accumulating a directory segment per inline level. It should be
	// diagnosed, not silently ignored, and the surrounding file should
	// still load its own top-level items normally.
	let mut builder = CompilationUnitBuilder::new();
	let package_id = builder
		.load_binary(
			AbsolutePath::new("/main.wx"),
			&VirtualFileSource::new(HashMap::from([(
				AbsolutePath::new("/main.wx"),
				"module utils { module extra; }\nfn works() -> i32 { 1 }"
					.to_string(),
			)])),
		)
		.expect("the entry file itself is still readable");
	let graph = &builder.packages[package_id.as_u32() as usize];

	assert_eq!(
		graph.modules.len(),
		1,
		"the nested `extra` declaration should not cause a file to load"
	);
	assert!(
		graph.linker_diagnostics.iter().any(|d| d.code.as_deref()
			== Some(DiagnosticCode::NestedModuleDeclaration.code())),
		"expected E2006 (NestedModuleDeclaration), got: {:?}",
		graph
			.linker_diagnostics
			.iter()
			.map(|d| &d.message)
			.collect::<Vec<_>>(),
	);
}
