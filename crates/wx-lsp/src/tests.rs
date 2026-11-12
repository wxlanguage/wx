use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::str::FromStr;

use tower_lsp_server::LanguageServer as _;
use tower_lsp_server::ls_types::{
	Diagnostic, DiagnosticSeverity, GotoDefinitionParams,
	GotoDefinitionResponse, HoverContents, HoverParams, Position, Range,
	TextDocumentIdentifier, TextDocumentPositionParams, Uri,
};
use wx_compiler::diagnostics::Diagnostics;
use wx_compiler::vfs::FileId;

use crate::actor::{Command, handle_command};
use crate::convert::{
	byte_to_position, file_id_to_uri, position_to_offset, uri_to_path,
};
use crate::diagnostics::{add_compiler_diagnostic, diagnostic_publish_paths};
use crate::documents::OpenDocument;
use crate::projects::{ManifestState, ProjectState, discover_package_root};
use crate::requests;
use crate::snapshot::Snapshot;
use crate::state::{
	ClientConfig, ServerState, analyze_root, compute_active_refresh,
	compute_refresh, refresh_project_manifest,
};
use crate::{Backend, build_service};

fn open_document(text: &str) -> OpenDocument {
	OpenDocument {
		text: text.to_string(),
		version: 0,
	}
}

fn file_id_for(snapshot: &Snapshot, path: &Path) -> FileId {
	snapshot
		.compilation
		.packages
		.iter()
		.flat_map(|package| package.modules.iter())
		.find(|module| Path::new(module.file_path.as_str()) == path)
		.unwrap_or_else(|| {
			panic!("file not found in compiled graph: {}", path.display())
		})
		.file_id
}

fn is_error(diagnostic: &Diagnostic) -> bool {
	diagnostic.severity == Some(DiagnosticSeverity::ERROR)
}

/// Opens `{dir}/wx.json` with `entry` set to the entry file's own name.
fn open_synthetic_manifest(state: &mut ServerState, entry: &Path) -> PathBuf {
	let dir = entry.parent().unwrap().to_path_buf();
	let entry_name = entry.file_name().and_then(|name| name.to_str()).unwrap();
	state.open_documents.insert(
		dir.join("wx.json"),
		open_document(&format!(r#"{{ "entry": "{entry_name}" }}"#)),
	);
	dir
}

/// Analyses `source` as the entry file of its own package and returns the
/// state it was cached in, with the package's directory.
fn analyzed(root: &Path, source: &str) -> (ServerState, PathBuf) {
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(root.to_path_buf(), open_document(source));
	let dir = open_synthetic_manifest(&mut state, root);
	analyze_root(&mut state, &dir, root, &mut Vec::new());
	assert!(state.cached.contains_key(&dir), "analysis failed");
	(state, dir)
}

/// The position of the `occurrence`-th `needle` in an ASCII `source`.
fn position_of(source: &str, needle: &str, occurrence: usize) -> Position {
	let offset = source.match_indices(needle).nth(occurrence).unwrap().0;
	let line = source[..offset].matches('\n').count();
	let line_start = source[..offset].rfind('\n').map_or(0, |at| at + 1);
	Position {
		line: line as u32,
		character: (offset - line_start) as u32,
	}
}

fn definition_params(uri: &Uri, position: Position) -> GotoDefinitionParams {
	GotoDefinitionParams {
		text_document_position_params: TextDocumentPositionParams {
			text_document: TextDocumentIdentifier { uri: uri.clone() },
			position,
		},
		work_done_progress_params: Default::default(),
		partial_result_params: Default::default(),
	}
}

fn reference_params(
	uri: &Uri,
	position: Position,
	include_declaration: bool,
) -> tower_lsp_server::ls_types::ReferenceParams {
	tower_lsp_server::ls_types::ReferenceParams {
		text_document_position: TextDocumentPositionParams {
			text_document: TextDocumentIdentifier { uri: uri.clone() },
			position,
		},
		context: tower_lsp_server::ls_types::ReferenceContext {
			include_declaration,
		},
		work_done_progress_params: Default::default(),
		partial_result_params: Default::default(),
	}
}

fn scalar(
	response: Option<GotoDefinitionResponse>,
) -> tower_lsp_server::ls_types::Location {
	let Some(GotoDefinitionResponse::Scalar(location)) = response else {
		panic!("expected one definition, got {response:?}");
	};
	location
}

/// A client whose messages are drained, so the actor never blocks on them.
fn backend_with_drained_socket() -> tower_lsp_server::LspService<Backend> {
	let (service, socket) = build_service();
	tokio::spawn(async move {
		use futures::stream::StreamExt;
		let (mut requests, _responses) = socket.split();
		while requests.next().await.is_some() {}
	});
	service
}

#[test]
fn discover_package_root_walks_up_to_wx_json() {
	let workspace_root = PathBuf::from("/workspace");
	let package_dir = workspace_root.join("app");
	let child_file = package_dir.join("math").join("add.wx");

	let mut open_documents = HashMap::new();
	open_documents.insert(
		package_dir.join("wx.json"),
		open_document(r#"{ "entry": "main.wx" }"#),
	);

	let discovered =
		discover_package_root(&open_documents, &[workspace_root], &child_file);

	assert_eq!(discovered, Some(package_dir));
}

#[test]
fn diagnostic_publish_paths_keeps_previous_files_for_clearing() {
	let main = PathBuf::from("/workspace/app/main.wx");
	let child = PathBuf::from("/workspace/app/math.wx");

	let previous = HashSet::from([main.clone(), child.clone()]);
	let owned_files = HashSet::from([main.clone()]);
	let diagnostics_by_file = HashMap::from([(
		main.clone(),
		vec![Diagnostic {
			range: Range::default(),
			severity: Some(DiagnosticSeverity::ERROR),
			source: Some("wx".to_string()),
			message: "error".to_string(),
			..Default::default()
		}],
	)]);

	let publish_paths =
		diagnostic_publish_paths(&previous, &owned_files, &diagnostics_by_file);

	assert!(publish_paths.contains(&main));
	assert!(publish_paths.contains(&child));
	assert_eq!(publish_paths.len(), 2);
}

#[test]
fn editing_a_dependency_file_does_not_clear_the_dependent_root() {
	// A dependency file (`pow/main.wx`, reached as part of `hashing`'s graph)
	// is also, independently, the entry file of its own project. Editing it
	// must rebuild its consumer without moving its own ownership or wiping
	// the consumer's diagnostics.
	let hashing_dir = PathBuf::from("/examples/hashing");
	let hashing_main = hashing_dir.join("main.wx");
	let pow_dir = PathBuf::from("/examples/pow");
	let pow_main = pow_dir.join("main.wx");

	let mut state = ServerState::default();
	state.open_documents.insert(
		hashing_dir.join("wx.json"),
		open_document(
			r#"{
				"entry": "main.wx",
				"dependencies": { "pow": { "type": "local", "path": "../pow" } }
			}"#,
		),
	);
	state.open_documents.insert(
		hashing_main.clone(),
		open_document(
			"package \"pow\" as pow;\nfunc test() -> i32 { pow::pow(2, 3) }\nexport { test }\n",
		),
	);
	state.open_documents.insert(
		pow_dir.join("wx.json"),
		open_document(r#"{ "entry": "main.wx" }"#),
	);
	state.open_documents.insert(
		pow_main.clone(),
		open_document("pub func pow(base: i32, exp: i32) -> i32 { base }\n"),
	);

	compute_refresh(&mut state, &hashing_main, &mut Vec::new());
	assert!(state.cached.contains_key(&hashing_dir));

	state.open_documents.insert(
		pow_main.clone(),
		open_document("pub func pow(base: i32, exp: i32) -> Bool { True }"),
	);
	let mut logs = Vec::new();
	let publications = compute_active_refresh(
		&mut state,
		vec![pow_main.clone(), pow_main],
		&mut logs,
	);
	assert_eq!(
		logs.len(),
		2,
		"each active root must compile once per batch"
	);
	let final_diagnostics: HashMap<_, _> = publications.into_iter().collect();
	assert!(final_diagnostics[&hashing_main].iter().any(is_error));
	assert!(state.cached.contains_key(&hashing_dir));
}

#[test]
fn analyze_root_updates_multi_file_diagnostics_when_overlay_changes() {
	let root = PathBuf::from("/workspace/app/main.wx");
	let child = PathBuf::from("/workspace/app/math.wx");

	let mut state = ServerState::default();
	state.open_documents.insert(
		root.clone(),
		open_document(
			"mod math;\n\nfunc compute() -> i32 {\n    math::add()\n}\n",
		),
	);
	state.open_documents.insert(
		child.clone(),
		open_document("pub func add() -> Bool {\n    True\n}\n"),
	);
	let dir = open_synthetic_manifest(&mut state, &root);

	let broken = analyze_root(&mut state, &dir, &root, &mut Vec::new());
	assert!(broken.owned_files.contains(&root));
	assert!(broken.owned_files.contains(&child));
	assert!(
		broken
			.diagnostics_by_file
			.get(&root)
			.is_some_and(|d| d.iter().any(is_error)),
		"expected a root file error when the child's type is incompatible"
	);

	state.open_documents.insert(
		child.clone(),
		open_document("pub func add() -> i32 {\n    1\n}\n"),
	);
	let fixed = analyze_root(&mut state, &dir, &root, &mut Vec::new());
	assert!(
		fixed
			.diagnostics_by_file
			.get(&root)
			.is_none_or(|d| !d.iter().any(is_error)),
		"expected the root's errors to clear after fixing the child overlay"
	);
}

#[test]
fn refresh_from_a_child_path_discovers_the_root_and_republishes_its_diagnostics()
 {
	let workspace_root = PathBuf::from("/workspace");
	let root = workspace_root.join("app").join("main.wx");
	let child = workspace_root.join("app").join("math.wx");

	let mut state = ServerState {
		client: ClientConfig {
			workspace_folders: vec![workspace_root],
			..Default::default()
		},
		..Default::default()
	};
	state.open_documents.insert(
		root.clone(),
		open_document(
			"mod math;\n\nfunc compute() -> i32 {\n    math::add()\n}\n",
		),
	);
	state.open_documents.insert(
		child.clone(),
		open_document("pub func add() -> Bool {\n    True\n}\n"),
	);
	open_synthetic_manifest(&mut state, &root);

	let broken = compute_refresh(&mut state, &child, &mut Vec::new());
	assert_eq!(
		state.own_root.get(&child),
		root.parent().map(PathBuf::from).as_ref()
	);
	assert!(
		broken.iter().any(|(path, diagnostics)| path == &root
			&& diagnostics.iter().any(is_error)),
		"expected a refresh from the child to publish the root's error"
	);

	state.open_documents.insert(
		child.clone(),
		open_document("pub func add() -> i32 {\n    1\n}\n"),
	);
	let fixed = compute_refresh(&mut state, &child, &mut Vec::new());
	assert!(
		fixed.iter().any(|(path, diagnostics)| path == &root
			&& !diagnostics.iter().any(is_error)),
		"expected the root's error to clear once the child is fixed"
	);
}

#[test]
fn position_conversion_handles_non_ascii_lines() {
	// `Position::character` counts UTF-16 units. Cyrillic is 1 unit but 2
	// UTF-8 bytes, so using it as a byte offset lands inside a character.
	let source =
		"func alpha() -> i32 { 0 }\nfunc beta() -> i32 {\n    // привет al\n}";
	let al_byte_offset = source.rfind("al").unwrap();
	let position = Position {
		line: 2,
		character: 14,
	};

	let root = PathBuf::from("/test/main.wx");
	let (state, dir) = analyzed(&root, source);
	let snapshot = &state.cached[&dir];
	let file = file_id_for(snapshot, &root);
	let files = &snapshot.compilation.files;

	let offset = position_to_offset(files, file, position).unwrap() as usize;
	assert_eq!(offset, al_byte_offset);
	assert!(source.is_char_boundary(offset));
	// Round-tripping recovers the UTF-16 count, not a byte count.
	assert_eq!(
		byte_to_position(files, file, al_byte_offset),
		Some(position)
	);
}

#[test]
fn resolve_uri_finds_a_virtual_core_module() {
	// `Uri::to_file_path` does not check the scheme and returns a bogus path
	// for `wx://core/...`, so the lookup must not short-circuit on it.
	let root = PathBuf::from("/test/main.wx");
	let (state, dir) = analyzed(&root, "func main() {}");
	let snapshot = &state.cached[&dir];
	let core_file = snapshot
		.compilation
		.packages
		.iter()
		.flat_map(|package| package.modules.iter())
		.find(|module| module.file_path.as_str() == "/main.wx")
		.map(|module| module.file_id)
		.expect("the core module is in the graph");
	let uri = file_id_to_uri(&snapshot.compilation.files, core_file).unwrap();

	let resolved = state.resolve_uri(&uri);
	assert_eq!(resolved.map(|(_, file)| file), Some(core_file));
}

#[test]
fn a_shared_file_resolves_to_its_own_project_whatever_the_hash_order() {
	// `/dep/main.wx` is a dependency of both `/a` and `/b` and its own
	// project. Requests about it must always be answered from `/dep`.
	let mut state = ServerState::default();
	for consumer in ["/a", "/b"] {
		state.open_documents.insert(
			PathBuf::from(consumer).join("wx.json"),
			open_document(
				r#"{ "entry": "main.wx",
				     "dependencies": { "dep": { "type": "local", "path": "../dep" } } }"#,
			),
		);
		state.open_documents.insert(
			PathBuf::from(consumer).join("main.wx"),
			open_document("package \"dep\" as dep;\nfunc main() {}\n"),
		);
	}
	let dep_dir = PathBuf::from("/dep");
	let dep_main = dep_dir.join("main.wx");
	state.open_documents.insert(
		dep_dir.join("wx.json"),
		open_document(r#"{ "entry": "main.wx" }"#),
	);
	state
		.open_documents
		.insert(dep_main.clone(), open_document("pub func helper() {}\n"));
	for file in ["/a/main.wx", "/b/main.wx", "/dep/main.wx"] {
		compute_refresh(&mut state, Path::new(file), &mut Vec::new());
	}
	assert_eq!(state.cached.len(), 3);

	let uri = Uri::from_str("file:///dep/main.wx").unwrap();
	for _ in 0..20 {
		let (snapshot, file) = state.resolve_uri(&uri).unwrap();
		assert!(std::ptr::eq(snapshot, &state.cached[&dep_dir]));
		assert_eq!(file, file_id_for(snapshot, &dep_main));
	}
}

#[test]
fn full_diagnostic_renders_and_handles_a_bad_index() {
	let root = PathBuf::from("/test/main.wx");
	let (state, dir) =
		analyzed(&root, "func main() -> i32 { True }\nexport { main }\n");
	assert!(
		!state.cached[&dir].sema.diagnostics().is_empty(),
		"expected a type error to drive this test"
	);

	let uri = Uri::from_file_path(&root).unwrap();
	let rendered = requests::render_full_diagnostic(&state, &uri, 0);
	assert!(rendered.contains("True"), "{rendered}");
	assert!(rendered.contains('\x1b'), "{rendered:?}");

	let out_of_range = requests::render_full_diagnostic(&state, &uri, 99);
	assert!(out_of_range.contains("Unable to find original wx diagnostic"));

	let untracked = Uri::from_str("file:///not/a/tracked/file.wx").unwrap();
	let untracked = requests::render_full_diagnostic(&state, &untracked, 0);
	assert!(untracked.contains("Unable to find original wx diagnostic"));
}

#[test]
fn a_diagnostic_without_a_primary_label_gets_one_squiggle_per_label() {
	// Every label of such a diagnostic is equally "the problem", so each is
	// squiggled on its own instead of collapsing to the first one.
	use codespan_reporting::diagnostic::{Diagnostic as Report, Label};
	use wx_compiler::vfs::{FileOrigin, Files};

	let mut files = Files::new();
	let file = files
		.add(
			"/test/main.wx".to_string(),
			"enum E { A, B }".to_string(),
			FileOrigin::Local,
		)
		.unwrap();
	let report = Report::warning()
		.with_message("unused variants")
		.with_labels(vec![
			Label::secondary(file, 9..10),
			Label::secondary(file, 12..13),
		]);

	let mut grouped = HashMap::new();
	add_compiler_diagnostic(&mut grouped, &files, &report);

	let diagnostics = &grouped[&PathBuf::from("/test/main.wx")];
	assert_eq!(diagnostics.len(), 2);
	assert_ne!(diagnostics[0].range, diagnostics[1].range);
}

#[test]
fn where_binding_names_support_definition_and_references() {
	let root = PathBuf::from("/test/main.wx");
	let source = "trait Representation { type Repr; }\n\
		trait Scalar {}\n\
		trait Derived: Representation {}\n\
		trait Example { type Value: Representation where { Repr: Scalar }; }\n\
		func equality<T: Representation where { Repr = i32 }>() {}\n\
		func inherited<T: Derived where { Repr: Scalar }>() {}\n";
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let declaration = position_of(source, "Repr;", 0);
	let uses = [
		position_of(source, "Repr: Scalar", 0),
		position_of(source, "Repr = i32", 0),
		position_of(source, "Repr: Scalar", 1),
	];
	for position in uses {
		let location = scalar(requests::goto_definition(
			&state,
			&definition_params(&uri, position),
		));
		assert_eq!(location.uri, uri);
		assert_eq!(location.range.start, declaration);
	}
	let references = requests::references(
		&state,
		&reference_params(&uri, declaration, false),
	)
	.unwrap();
	assert_eq!(references.len(), uses.len());
	for position in uses {
		assert!(references.iter().any(|location| {
			location.uri == uri && location.range.start == position
		}));
	}
}

#[test]
fn goto_definition_goes_to_the_declaring_name() {
	let root = PathBuf::from("/test/main.wx");
	let source = "func add(a: i32, b: i32) -> i32 { a + b }\nfunc main() -> i32 { add(1, 2) }\nexport { main }\n";
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();

	let location = scalar(requests::goto_definition(
		&state,
		&definition_params(&uri, position_of(source, "add", 1)),
	));
	assert_eq!(location.uri, uri);
	assert_eq!(
		location.range,
		Range {
			start: position_of(source, "add", 0),
			end: Position {
				line: 0,
				character: 8
			},
		}
	);

	// A parameter use goes to the parameter.
	let location = scalar(requests::goto_definition(
		&state,
		&definition_params(&uri, position_of(source, "a +", 0)),
	));
	assert_eq!(location.range.start, position_of(source, "a:", 0));

	// Nothing resolved under the cursor: no answer.
	assert!(
		requests::goto_definition(
			&state,
			&definition_params(&uri, position_of(source, "export", 0)),
		)
		.is_none()
	);
}

#[test]
fn goto_definition_works_in_a_file_with_errors() {
	// A type error elsewhere must not take navigation away: the snapshot
	// keeps the partial semantic data of an erroneous program.
	let root = PathBuf::from("/test/main.wx");
	let source = "func helper() {}\nfunc broken() -> i32 { True }\nfunc main() { helper() }\nexport { main }\n";
	let (state, dir) = analyzed(&root, source);
	assert!(state.cached[&dir].sema.diagnostics().iter().any(|d| {
		d.severity == codespan_reporting::diagnostic::Severity::Error
	}));
	let uri = Uri::from_file_path(&root).unwrap();

	let location = scalar(requests::goto_definition(
		&state,
		&definition_params(&uri, position_of(source, "helper", 1)),
	));
	assert_eq!(location.range.start, position_of(source, "helper", 0));
}

#[tokio::test]
async fn a_query_queued_after_an_edit_sees_that_edit() {
	use tower_lsp_server::ls_types::*;

	let service = backend_with_drained_socket();
	let backend: &Backend = service.inner();
	let manifest_uri = Uri::from_str("file:///tmp/probe/wx.json").unwrap();
	backend
		.did_open(DidOpenTextDocumentParams {
			text_document: TextDocumentItem {
				uri: manifest_uri,
				language_id: "json".into(),
				version: 1,
				text: r#"{ "entry": "main.wx" }"#.into(),
			},
		})
		.await;

	let uri = Uri::from_str("file:///tmp/probe/main.wx").unwrap();
	let first = "func add() {}\nfunc main() { add() }\nexport { main }\n";
	backend
		.did_open(DidOpenTextDocumentParams {
			text_document: TextDocumentItem {
				uri: uri.clone(),
				language_id: "wx".into(),
				version: 1,
				text: first.into(),
			},
		})
		.await;

	// Two edits, then a query: no edit may be skipped, and the query must be
	// answered from the last one.
	let second = "\n\nfunc add() {}\nfunc main() { add() }\nexport { main }\n";
	let third =
		"\n\n\n\nfunc add() {}\nfunc main() { add() }\nexport { main }\n";
	for (version, text) in [(2, second), (3, third)] {
		backend
			.did_change(DidChangeTextDocumentParams {
				text_document: VersionedTextDocumentIdentifier {
					uri: uri.clone(),
					version,
				},
				content_changes: vec![TextDocumentContentChangeEvent {
					range: None,
					range_length: None,
					text: text.into(),
				}],
			})
			.await;
	}
	let location = scalar(
		backend
			.goto_definition(definition_params(
				&uri,
				position_of(third, "add", 1),
			))
			.await
			.expect("goto definition should not error"),
	);
	assert_eq!(location.range.start, position_of(third, "add", 0));
	let references = backend
		.references(reference_params(&uri, position_of(third, "add", 0), false))
		.await
		.unwrap()
		.unwrap();
	assert_eq!(references.len(), 1);
	assert_eq!(references[0].range.start, position_of(third, "add", 1));
}

#[test]
fn references_work_from_declarations_and_uses_and_honor_include_declaration() {
	let root = PathBuf::from("/test/main.wx");
	let source = "func helper() {}\nfunc main() { helper(); helper(); }\n";
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(root).unwrap();
	for occurrence in 0..3 {
		for include in [false, true] {
			let references = requests::references(
				&state,
				&reference_params(
					&uri,
					position_of(source, "helper", occurrence),
					include,
				),
			)
			.unwrap();
			let expected: Vec<_> = (usize::from(!include)..3)
				.map(|i| position_of(source, "helper", i))
				.collect();
			assert_eq!(
				references
					.iter()
					.map(|loc| loc.range.start)
					.collect::<Vec<_>>(),
				expected
			);
			assert!(references.iter().all(|loc| loc.uri == uri));
		}
	}
}

#[test]
fn references_keep_shorthand_field_and_value_roles_separate() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct S(value: u32);
		func take(value: u32) -> u32 { value }
		func f(value: u32) -> u32 {
			local s = S({ value });
			_ = take({ value: s.value });
			value
		}
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(root).unwrap();
	let refs = |needle, occurrence| {
		requests::references(
			&state,
			&reference_params(
				&uri,
				position_of(source, needle, occurrence),
				false,
			),
		)
		.unwrap()
		.into_iter()
		.map(|loc| loc.range.start)
		.collect::<Vec<_>>()
	};
	// The field and caller's local each include the shorthand, but are not
	// the same symbol. The shorthand cursor chooses the value, as hover does.
	let field = vec![
		position_of(source, "value });", 0),
		position_of(source, "value });", 1),
	];
	assert_eq!(refs("value:", 0), field);
	let local = vec![
		position_of(source, "value });", 0),
		position_of(source, "value\n", 0),
	];
	assert_eq!(refs("value:", 2), local);
	assert_eq!(refs("value });", 0), local);
	// The callee's parameter includes both its body local and its call label.
	assert_eq!(
		refs("value:", 1),
		vec![
			position_of(source, "value }", 0),
			position_of(source, "value: s", 0),
		]
	);
}

#[test]
fn references_search_loaded_modules_and_include_the_module_name_not_file_start()
{
	let root = PathBuf::from("/test/main.wx");
	let child = PathBuf::from("/test/shared.wx");
	let source = "mod shared;\nuse shared::run as alias;\nfunc main() { shared::run(); alias(); }\n";
	let child_source = "pub func run() {}\nfunc other() { run(); }\n";
	let (mut state, dir) = analyzed(&root, source);
	state
		.open_documents
		.insert(child.clone(), open_document(child_source));
	analyze_root(&mut state, &dir, &root, &mut Vec::new());
	let uri = Uri::from_file_path(&root).unwrap();
	let child_uri = Uri::from_file_path(&child).unwrap();
	let refs = requests::references(
		&state,
		&reference_params(&uri, position_of(source, "alias();", 0), true),
	)
	.unwrap();
	assert_eq!(refs.len(), 5);
	assert_eq!(refs.iter().filter(|loc| loc.uri == uri).count(), 3);
	assert_eq!(refs.iter().filter(|loc| loc.uri == child_uri).count(), 2);
	let module = requests::references(
		&state,
		&reference_params(&uri, position_of(source, "shared", 1), true),
	)
	.unwrap();
	assert_eq!(module.len(), 3);
	assert_eq!(module[0].uri, uri);
	assert_eq!(module[0].range.start, position_of(source, "shared", 0));
	assert_eq!(
		module[0].range.end.character - module[0].range.start.character,
		6
	);
}

#[test]
fn references_return_empty_for_unused_symbols_and_none_for_unresolved_names() {
	let root = PathBuf::from("/test/main.wx");
	let source = "func unused() {}\nfunc broken() { missing(); }\n";
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(root).unwrap();
	let params = |needle, include| {
		reference_params(&uri, position_of(source, needle, 0), include)
	};
	assert_eq!(
		requests::references(&state, &params("unused", false)),
		Some(vec![])
	);
	assert_eq!(
		requests::references(&state, &params("unused", true))
			.unwrap()
			.len(),
		1
	);
	assert_eq!(
		requests::references(&state, &params("missing", false)),
		None
	);
	assert_eq!(requests::references(&state, &params("func", false)), None);
}

#[tokio::test]
async fn initialization_advertises_references() {
	let service = backend_with_drained_socket();
	let result = service
		.inner()
		.initialize(Default::default())
		.await
		.unwrap();
	assert_eq!(
		result.capabilities.references_provider,
		Some(tower_lsp_server::ls_types::OneOf::Left(true))
	);
}

#[test]
fn references_reach_dependencies_without_comparing_ids_from_other_snapshots() {
	let app = PathBuf::from("/refs/app/main.wx");
	let lib = PathBuf::from("/refs/lib/main.wx");
	let source = "package \"lib\" as lib; func main() { lib::run(); }";
	let lib_source = "pub func run() {} func other() { run(); }";
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(app.clone(), open_document(source));
	state
		.open_documents
		.insert(lib.clone(), open_document(lib_source));
	state.open_documents.insert(app.parent().unwrap().join("wx.json"), open_document(
		r#"{"entry":"main.wx","dependencies":{"lib":{"type":"local","path":"../lib"}}}"#,
	));
	state.open_documents.insert(
		lib.parent().unwrap().join("wx.json"),
		open_document(r#"{"entry":"main.wx"}"#),
	);
	compute_refresh(&mut state, &app, &mut Vec::new());
	assert_eq!(state.cached.len(), 2);
	let uri = Uri::from_file_path(&app).unwrap();
	let lib_uri = Uri::from_file_path(&lib).unwrap();
	let references = requests::references(
		&state,
		&reference_params(&uri, position_of(source, "run", 0), true),
	)
	.unwrap();
	assert_eq!(references.len(), 3);
	assert_eq!(references.iter().filter(|loc| loc.uri == uri).count(), 1);
	assert_eq!(
		references.iter().filter(|loc| loc.uri == lib_uri).count(),
		2
	);
	// A query in the library's own project searches that graph, not every
	// cached consumer. Cross-root search is intentionally not inferred from
	// arena indices or navigation spans.
	let references = requests::references(
		&state,
		&reference_params(&lib_uri, position_of(lib_source, "run", 0), false),
	)
	.unwrap();
	assert_eq!(references.len(), 1);
	assert_eq!(references[0].uri, lib_uri);
}

#[test]
fn references_reuse_utf16_conversion_and_virtual_core_uris() {
	let root = PathBuf::from("/test/main.wx");
	let source =
		"func helper() {}\nfunc f() { local _: u32 = '😀'; helper(); }\n";
	let column =
		"func f() { local _: u32 = '😀'; ".encode_utf16().count() as u32;
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(root).unwrap();
	let references = requests::references(
		&state,
		&reference_params(&uri, Position::new(1, column), false),
	)
	.unwrap();
	assert_eq!(references.len(), 1);
	assert_eq!(
		references[0].range,
		Range::new(Position::new(1, column), Position::new(1, column + 6))
	);
	let core = Uri::from_str("wx://core/main.wx").unwrap();
	let (snapshot, file) = state.resolve_uri(&core).unwrap();
	let source = &snapshot.compilation.files.get(file).unwrap().source;
	let offset = source.find("pub type u32;").unwrap() + "pub type ".len();
	let position =
		byte_to_position(&snapshot.compilation.files, file, offset).unwrap();
	let references =
		requests::references(&state, &reference_params(&core, position, true))
			.unwrap();
	assert!(
		references
			.iter()
			.any(|loc| loc.uri == core && loc.range.start == position)
	);
}

/// The hover text at the `occurrence`-th `needle` of `source`.
fn hover_text(
	state: &ServerState,
	uri: &Uri,
	source: &str,
	needle: &str,
	occurrence: usize,
) -> Option<String> {
	let params = HoverParams {
		text_document_position_params: TextDocumentPositionParams {
			text_document: TextDocumentIdentifier { uri: uri.clone() },
			position: position_of(source, needle, occurrence),
		},
		work_done_progress_params: Default::default(),
	};
	let hover = requests::hover(state, &params)?;
	let HoverContents::Markup(markup) = hover.contents else {
		panic!("expected markup contents");
	};
	Some(markup.value)
}

#[test]
fn hover_renders_signatures_from_the_resolved_name() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point(x: i32, pub y: i32);
		/// Adds two numbers.
		///
		/// Wraps on overflow.
		func add<T: StackValue>(a: i32, b: i32, extra: T) -> i32 { a + b }
		const LIMIT: u32 = 10;
		func main() -> i32 {
		    local mut total: i32 = 0;
		    local p = Point(1, 2);
		    _ = p;
		    total = add(1, 2, 3);
		    total
		}
		export { main }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let hover = |needle, occurrence| {
		hover_text(&state, &uri, source, needle, occurrence)
	};

	let call = hover("add", 1).expect("hover on the call");
	assert!(
		call.starts_with(
			"```wx\nfunc add<T>(a: i32, b: i32, extra: T) -> i32\n```"
		),
		"{call}"
	);
	assert!(
		call.contains("Adds two numbers.\n\nWraps on overflow."),
		"{call}"
	);

	assert_eq!(
		hover("total", 1).unwrap(),
		"```wx\nlocal mut total: i32\n```"
	);
	assert_eq!(hover("a +", 0).unwrap(), "```wx\na: i32\n```");
	assert_eq!(
		hover("Point", 1).unwrap(),
		"```wx\nstruct Point(x: i32, y: i32)\n```"
	);
	assert_eq!(hover("i32", 1).unwrap(), "```wx\ntype i32\n```");
	assert_eq!(hover("T:", 0).unwrap(), "```wx\ntype T\n```");
	assert_eq!(hover("export", 0), None);
}

#[test]
fn hover_renders_the_other_declaration_kinds() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		memory heap: u32;
		global mut bump: u32 = 4;
		global fixed: u32 = 1;
		enum Color(u8) { Red = 0, Green = 1 }
		trait Shape { type Unit; }
		typeset Small { u8, u16 }
		func main() -> u32 {
		    _ = Color::Red;
		    _ = heap;
		    _ = bump;
		    _ = fixed;
		    0
		}
		export { main }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let hover = |needle, occurrence| {
		hover_text(&state, &uri, source, needle, occurrence)
	};
	assert_eq!(hover("heap", 1).unwrap(), "```wx\nmemory heap: u32\n```");
	assert_eq!(
		hover("bump", 1).unwrap(),
		"```wx\nglobal mut bump: u32\n```"
	);
	assert_eq!(hover("fixed", 1).unwrap(), "```wx\nglobal fixed: u32\n```");
	assert_eq!(hover("Red;", 0).unwrap(), "```wx\nColor::Red = 0\n```");
	assert_eq!(
		hover("Color::", 0).unwrap(),
		"```wx\nenum Color(u8) { .. }\n```"
	);
}

#[test]
fn hover_on_a_trait_method_shows_its_signature() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		trait Shl {
		    func shl(self: Self, rhs: Self) -> Self;
		}
		impl Shl for i32 {
		    func shl(self: Self, rhs: Self) -> Self { self }
		}
		func main() -> u32 { 0 }
		export { main }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	assert_eq!(
		hover_text(&state, &uri, source, "shl", 0).unwrap(),
		"```wx\ntrait Shl\nfunc shl(self: Self, rhs: Self) -> Self\n```"
	);
	assert_eq!(
		hover_text(&state, &uri, source, "shl", 1).unwrap(),
		"```wx\nimpl Shl for i32\nfunc shl(self: i32, rhs: i32) -> i32\n```"
	);
}

#[test]
fn hover_separates_inherent_impl_and_function_type_params() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Layout<Mem: Memory>(size: Mem::Size);
		impl<Mem: Memory> Layout<Mem> {
		    func size(self: Self) -> Mem::Size { self.size }
		    func with_extra<T: StackValue>(self: Self, extra: T) -> T { extra }
		    func make(size: Mem::Size) -> Self { Self(size) }
		}
		memory heap: u32;
		func main() -> u32 {
		    local layout = Layout::<heap>(4);
		    _ = layout.with_extra::<u32>(0);
		    _ = Layout::<heap>::make(4);
		    layout.size()
		}
		export { main }
	"};
	let (state, dir) = analyzed(&root, source);
	assert!(
		!state.cached[&dir].sema.diagnostics().has_errors(),
		"{:?}",
		state.cached[&dir].sema.diagnostics()
	);
	let uri = Uri::from_file_path(&root).unwrap();
	for (needle, expected) in [
		(
			"size(",
			"impl<Mem> Layout<Mem>\nfunc size(self: Layout<Mem>) -> <Mem as Memory>::Size",
		),
		(
			"with_extra",
			"impl<Mem> Layout<Mem>\nfunc with_extra<T>(self: Layout<Mem>, extra: T) -> T",
		),
		(
			"make",
			"impl<Mem> Layout<Mem>\nfunc make(size: <Mem as Memory>::Size) -> Layout<Mem>",
		),
	] {
		for occurrence in 0..2 {
			assert_eq!(
				hover_text(&state, &uri, source, needle, occurrence).unwrap(),
				format!("```wx\n{expected}\n```"),
				"{needle}, occurrence {occurrence}",
			);
		}
	}
}

#[test]
fn hover_separates_trait_impl_and_function_type_params() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Wrapper<T: StackValue>(value: T);
		trait Convert: StackValue {
		    func convert<Self: StackValue, U: StackValue>(self: Self, value: U) -> U;
		    func identity(self: Self) -> Self;
		}
		impl<T: StackValue> Convert for Wrapper<T> {
		    func convert<Self: StackValue, U: StackValue>(self: Self, value: U) -> U { value }
		    func identity(self: Self) -> Self { self }
		}
		func main() -> u32 {
		    local wrapper = Wrapper::<u32>(0);
		    _ = wrapper.identity();
		    wrapper.convert::<u32>(1)
		}
		export { main }
	"};
	let (state, dir) = analyzed(&root, source);
	assert!(
		!state.cached[&dir].sema.diagnostics().has_errors(),
		"{:?}",
		state.cached[&dir].sema.diagnostics()
	);
	let uri = Uri::from_file_path(&root).unwrap();
	assert_eq!(
		hover_text(&state, &uri, source, "convert", 0).unwrap(),
		"```wx\ntrait Convert\nfunc convert<U>(self: Self, value: U) -> U\n```",
	);
	assert_eq!(
		hover_text(&state, &uri, source, "identity", 0).unwrap(),
		"```wx\ntrait Convert\nfunc identity(self: Self) -> Self\n```",
	);
	for (needle, expected) in [
		(
			"convert",
			"impl<T> Convert for Wrapper<T>\nfunc convert<U>(self: Wrapper<T>, value: U) -> U",
		),
		(
			"identity",
			"impl<T> Convert for Wrapper<T>\nfunc identity(self: Wrapper<T>) -> Wrapper<T>",
		),
	] {
		for occurrence in 1..3 {
			assert_eq!(
				hover_text(&state, &uri, source, needle, occurrence).unwrap(),
				format!("```wx\n{expected}\n```"),
				"{needle}, occurrence {occurrence}",
			);
		}
	}
}

#[test]
fn hover_and_goto_definition_work_on_the_declaration_itself() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point(x: i32, y: i32);
		enum Color(u8) { Red = 0 }
		/// Doubles.
		func twice<T: StackValue>(value: i32, extra: T) -> i32 {
		    local mut total: i32 = value;
		    block :done { break :done; }
		    total
		}
		export { twice }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let hover = |needle, occurrence| {
		hover_text(&state, &uri, source, needle, occurrence)
	};
	assert_eq!(
		hover("Point", 0).unwrap(),
		"```wx\nstruct Point(x: i32, y: i32)\n```"
	);
	assert_eq!(hover("x:", 0).unwrap(), "```wx\nx: i32\n```");
	assert_eq!(
		hover("Color", 0).unwrap(),
		"```wx\nenum Color(u8) { .. }\n```"
	);
	assert_eq!(hover("Red", 0).unwrap(), "```wx\nColor::Red = 0\n```");
	let function = hover("twice", 0).unwrap();
	assert!(
		function.starts_with("```wx\nfunc twice<T>(value: i32, extra: T)"),
		"{function}"
	);
	assert!(function.contains("Doubles."), "{function}");
	assert_eq!(hover("value:", 0).unwrap(), "```wx\nvalue: i32\n```");
	assert_eq!(hover("T:", 0).unwrap(), "```wx\ntype T\n```");
	assert_eq!(
		hover("total", 0).unwrap(),
		"```wx\nlocal mut total: i32\n```"
	);
	assert_eq!(hover("export", 0), None);

	let goto = |needle, occurrence| {
		let params =
			definition_params(&uri, position_of(source, needle, occurrence));
		requests::goto_definition(&state, &params)
	};
	let own = goto("Point", 0).expect("a declaration names itself");
	let from_use = goto("twice", 1).expect("the export names the function");
	assert_ne!(format!("{own:?}"), format!("{from_use:?}"));
}

#[test]
fn self_in_an_impl_shows_and_leads_to_its_target() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point(x: i32, y: i32);
		impl Point {
		    func flip(self: Self) -> Self { self }
		}
		export { Point::flip }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	assert_eq!(
		hover_text(&state, &uri, source, "Self", 0).unwrap(),
		"```wx\ntype Self = Point\n```"
	);
	assert_eq!(
		hover_text(&state, &uri, source, "flip", 0).unwrap(),
		"```wx\nimpl Point\nfunc flip(self: Point) -> Point\n```",
	);
	let params = definition_params(&uri, position_of(source, "Self", 1));
	let Some(GotoDefinitionResponse::Scalar(location)) =
		requests::goto_definition(&state, &params)
	else {
		panic!("`Self` should lead to the impl's target");
	};
	let target = position_of(source, "Point {", 0);
	assert_eq!(location.range.start, target);
}

#[test]
fn an_import_alias_and_a_module_show_and_lead_to_their_names() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		import \"env\" as host {
		    func exit(code: u32) -> !;
		}
		mod util {
		    pub func one() -> u32 { 1 }
		}
		func main() -> u32 {
		    _ = util::one();
		    host::exit(0)
		}
		export { main }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let hover = |needle, occurrence| {
		hover_text(&state, &uri, source, needle, occurrence)
	};
	let import = "```wx\nimport \"env\" as host\n```";
	assert_eq!(hover("host", 0).unwrap(), import, "the alias, declared");
	assert_eq!(hover("host", 1).unwrap(), import, "the alias, used");
	let module = "```wx\nmod util\n```";
	assert_eq!(hover("util", 0).unwrap(), module);
	assert_eq!(hover("util", 1).unwrap(), module);

	let goto = |needle, occurrence| {
		let params =
			definition_params(&uri, position_of(source, needle, occurrence));
		let Some(GotoDefinitionResponse::Scalar(location)) =
			requests::goto_definition(&state, &params)
		else {
			panic!("`{needle}` should lead somewhere");
		};
		location.range.start
	};
	assert_eq!(goto("host", 1), position_of(source, "host", 0));
	assert_eq!(goto("util", 1), position_of(source, "util", 0));
}

#[test]
fn a_module_in_its_own_file_leads_to_that_file() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		mod shared;
		func main() -> u32 { shared::one() }
		export { main }
	"};
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(root.clone(), open_document(source));
	state.open_documents.insert(
		PathBuf::from("/test/shared.wx"),
		open_document("pub func one() -> u32 { 1 }"),
	);
	let dir = open_synthetic_manifest(&mut state, &root);
	analyze_root(&mut state, &dir, &root, &mut Vec::new());
	let uri = Uri::from_file_path(&root).unwrap();
	let shared = Uri::from_file_path("/test/shared.wx").unwrap();
	for occurrence in [0, 1] {
		let params =
			definition_params(&uri, position_of(source, "shared", occurrence));
		let Some(GotoDefinitionResponse::Scalar(location)) =
			requests::goto_definition(&state, &params)
		else {
			panic!("`shared` should lead to its file");
		};
		assert_eq!(location.uri, shared);
		assert_eq!(location.range.start, Position::new(0, 0));
	}
	assert_eq!(
		hover_text(&state, &uri, source, "shared", 0).unwrap(),
		"```wx\nmod shared\n```"
	);
}

#[test]
fn watched_manifest_creation_and_deletion_moves_open_file_ownership() {
	let mut state = ServerState::default();
	let outer = PathBuf::from("/watch-test");
	let inner = outer.join("nested");
	let file = inner.join("main.wx");
	state.open_documents.insert(
		file.clone(),
		open_document("func main() {} export { main }"),
	);
	state.open_documents.insert(
		outer.join("wx.json"),
		open_document(r#"{"entry":"nested/main.wx"}"#),
	);
	compute_refresh(&mut state, &file, &mut Vec::new());
	assert_eq!(state.own_root.get(&file), Some(&outer));

	let manifest = inner.join("wx.json");
	state
		.open_documents
		.insert(manifest.clone(), open_document(r#"{"entry":"main.wx"}"#));
	compute_active_refresh(
		&mut state,
		vec![manifest.clone(), manifest.clone()],
		&mut Vec::new(),
	);
	assert_eq!(state.own_root.get(&file), Some(&inner));
	assert!(state.cached.contains_key(&outer));
	assert!(state.cached.contains_key(&inner));

	state.open_documents.remove(&manifest);
	compute_refresh(&mut state, &manifest, &mut Vec::new());
	assert_eq!(state.own_root.get(&file), Some(&outer));
	assert!(state.cached.contains_key(&outer));
	assert!(!state.cached.contains_key(&inner));
	assert!(!state.projects.contains_key(&inner));
}

#[tokio::test]
async fn formatting_reuses_project_manifests() {
	use crate::actor::Command;
	use tokio::sync::oneshot;
	use tower_lsp_server::ls_types::*;

	let service = backend_with_drained_socket();
	let client = &service.inner().client;
	let root = PathBuf::from("/manifest-format-test");
	let manifest_path = root.join("wx.json");
	let source_path = root.join("main.wx");
	let dep_path = root.join("dep/wx.json");
	let manifest = |width| {
		format!(
			r#"{{"entry":"main.wx","format":{{"indent_width":{width}}},"dependencies":{{"dep":{{"type":"local","path":"dep"}}}}}}"#
		)
	};
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(manifest_path.clone(), open_document(&manifest(2)));
	state.open_documents.insert(
		source_path.clone(),
		open_document("func main() { local x = true; } export { main }"),
	);
	state
		.open_documents
		.insert(dep_path.clone(), open_document(r#"{"entry":"main.wx"}"#));
	state.open_documents.insert(
		root.join("dep/main.wx"),
		open_document("pub func helper() {}"),
	);

	async fn format(
		state: &mut ServerState,
		client: &tower_lsp_server::Client,
	) -> Option<Vec<TextEdit>> {
		let (tx, rx) = oneshot::channel();
		handle_command(
			Command::Formatting(
				DocumentFormattingParams {
					text_document: TextDocumentIdentifier {
						uri: Uri::from_str(
							"file:///manifest-format-test/main.wx",
						)
						.unwrap(),
					},
					options: FormattingOptions {
						tab_size: 8,
						insert_spaces: false,
						..Default::default()
					},
					work_done_progress_params: Default::default(),
				},
				tx,
			),
			state,
			client,
		)
		.await;
		rx.await.unwrap()
	}

	// First formatting discovers both manifests without a compiled cache.
	let first = format(&mut state, client).await.unwrap();
	assert!(state.cached.is_empty());
	assert_eq!(state.projects.len(), 2);
	assert!(
		first[0].new_text.contains("\n  local"),
		"{}",
		first[0].new_text
	);

	// Alter the backing text without an event: both manifests must be reused,
	// not read or parsed again by formatting or package resolution.
	state.open_documents.get_mut(&manifest_path).unwrap().text = "{".into();
	state.open_documents.get_mut(&dep_path).unwrap().text = "{".into();
	assert_eq!(format(&mut state, client).await.unwrap(), first);
	compute_refresh(&mut state, &source_path, &mut Vec::new());
	assert_eq!(format(&mut state, client).await.unwrap(), first);

	let change = |text: String, version| Command::DidChange {
		path: manifest_path.clone(),
		text,
		version,
	};
	handle_command(change(manifest(3), 2), &mut state, client).await;
	let updated = format(&mut state, client).await.unwrap();
	assert!(updated[0].new_text.contains("\n   local"));
	assert!(!updated[0].new_text.contains("\n      local"));

	// A failed parse replaces the last valid value.
	handle_command(change("{".into(), 3), &mut state, client).await;
	assert!(matches!(
		state.projects[&root].manifest,
		ManifestState::Invalid
	));
	assert!(format(&mut state, client).await.is_none());
	state.open_documents.get_mut(&manifest_path).unwrap().text = manifest(4);
	assert!(
		format(&mut state, client).await.is_none(),
		"invalid results are retained until an event"
	);
	handle_command(change(manifest(4), 4), &mut state, client).await;
	let edits = format(&mut state, client).await.unwrap();
	assert!(edits[0].new_text.contains("\n    local"));

	// Feeding that output back in yields no edits at all, or every
	// format-on-save would dirty the document.
	state.open_documents.get_mut(&source_path).unwrap().text =
		edits[0].new_text.clone();
	assert!(format(&mut state, client).await.unwrap().is_empty());
}

#[tokio::test]
async fn watched_file_events_skip_documents_the_editor_already_owns() {
	let service = backend_with_drained_socket();
	let client = &service.inner().client;
	let root = PathBuf::from("/watch-skip-test");
	let file = root.join("main.wx");
	let mut state = ServerState::default();
	state.open_documents.insert(
		root.join("wx.json"),
		open_document(r#"{"entry":"main.wx"}"#),
	);
	state.open_documents.insert(
		file.clone(),
		open_document("func main() {} export { main }"),
	);
	compute_refresh(&mut state, &file, &mut Vec::new());
	assert!(state.cached.contains_key(&root));

	// Saving an open buffer is reported by the watcher, but the overlay
	// already held that text: no rebuild.
	state.cached.clear();
	handle_command(
		Command::DidChangeWatchedFiles(vec![file, root.join("wx.json")]),
		&mut state,
		client,
	)
	.await;
	assert!(state.cached.is_empty());

	// A file the editor does not own still invalidates: that is how
	// `git checkout` and external edits reach the server.
	handle_command(
		Command::DidChangeWatchedFiles(vec![root.join("other.wx")]),
		&mut state,
		client,
	)
	.await;
	assert!(state.cached.contains_key(&root));
}

/// A path that cannot be converted to `&str` must be declined, not turned
/// into an empty one: `AbsolutePath::new` asserts on a path that does not
/// start with `/`, and this runs on the state actor, so a panic would end
/// analysis for the rest of the session.
#[cfg(unix)]
#[test]
fn an_unconvertible_manifest_path_does_not_delete_the_project() {
	use std::ffi::OsStr;
	use std::os::unix::ffi::OsStrExt;

	let mut state = ServerState::default();
	let root = PathBuf::from("/project");
	state.projects.insert(
		root.clone(),
		ProjectState {
			manifest: ManifestState::Invalid,
			published_files: HashSet::from([root.join("main.wx")]),
		},
	);
	// `wx.json` itself is valid UTF-8; the directory holding it is not.
	let mut invalid = PathBuf::from(OsStr::from_bytes(b"/project/\xff"));
	invalid.push("wx.json");

	let publications = refresh_project_manifest(&mut state, &invalid);

	assert!(publications.is_empty());
	assert!(state.projects.contains_key(&root));
}

/// A refresh that changes nothing must publish each file once. Clearing an
/// active root before re-analysing it drained the `published_files` the
/// diff is taken against, so every still-diagnosed file got an empty publish
/// followed by an identical real one: a squiggle blinking on every keystroke.
#[test]
fn a_repeated_refresh_publishes_each_file_once() {
	let mut state = ServerState::default();
	let root = PathBuf::from("/republish");
	let main = root.join("main.wx");
	state.open_documents.insert(
		root.join("wx.json"),
		open_document(r#"{"entry":"main.wx"}"#),
	);
	state.open_documents.insert(
		main.clone(),
		open_document("func main() -> i32 { True }\nexport { main }"),
	);

	compute_refresh(&mut state, &main, &mut Vec::new());
	let publications = compute_refresh(&mut state, &main, &mut Vec::new());

	let for_main: Vec<_> = publications
		.iter()
		.filter(|(path, _)| path == &main)
		.collect();
	assert_eq!(for_main.len(), 1, "{for_main:?}");
	assert!(!for_main[0].1.is_empty(), "the type error must survive");
}

#[test]
fn uri_paths_round_trip_for_local_files() {
	let uri = Uri::from_str("file:///a/b/main.wx").unwrap();
	assert_eq!(uri_to_path(&uri), Some(PathBuf::from("/a/b/main.wx")));
}

/// Each semantic token of `uri`, decoded back to its text, type and
/// modifiers: `name:type.modifier..`.
fn semantic_tokens(
	state: &ServerState,
	uri: &Uri,
	source: &str,
	range: Option<Range>,
) -> Vec<String> {
	use tower_lsp_server::ls_types::{
		SemanticTokensParams, SemanticTokensRangeParams,
		SemanticTokensRangeResult, SemanticTokensResult,
	};
	let text_document = TextDocumentIdentifier { uri: uri.clone() };
	let data = match range {
		None => {
			let params = SemanticTokensParams {
				text_document,
				work_done_progress_params: Default::default(),
				partial_result_params: Default::default(),
			};
			let Some(SemanticTokensResult::Tokens(tokens)) =
				requests::semantic_tokens_full(state, &params)
			else {
				panic!("expected tokens");
			};
			tokens.data
		}
		Some(range) => {
			let params = SemanticTokensRangeParams {
				text_document,
				range,
				work_done_progress_params: Default::default(),
				partial_result_params: Default::default(),
			};
			let Some(SemanticTokensRangeResult::Tokens(tokens)) =
				requests::semantic_tokens_range(state, &params)
			else {
				panic!("expected tokens");
			};
			tokens.data
		}
	};
	let legend = crate::semantic_tokens::legend();
	let lines: Vec<&str> = source.lines().collect();
	let (mut line, mut character) = (0, 0);
	data.iter()
		.map(|token| {
			line += token.delta_line;
			character = match token.delta_line {
				0 => character + token.delta_start,
				_ => token.delta_start,
			};
			let units: Vec<u16> = lines[line as usize]
				.encode_utf16()
				.skip(character as usize)
				.take(token.length as usize)
				.collect();
			let text = String::from_utf16(&units).unwrap();
			let mut rendered = format!(
				"{text}:{}",
				legend.token_types[token.token_type as usize].as_str()
			);
			for (bit, modifier) in legend.token_modifiers.iter().enumerate() {
				if token.token_modifiers_bitset & (1 << bit) != 0 {
					rendered.push('.');
					rendered.push_str(modifier.as_str());
				}
			}
			rendered
		})
		.collect()
}

#[test]
fn semantic_tokens_colour_resolved_and_declared_names() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		mod geo {
		    pub struct Point(pub x: i32, pub y: i32);
		    impl Point {
		        pub func sum(self: Self) -> i32 { self.x + self.y }
		        pub func origin() -> Self { Self(0, 0) }
		    }
		    pub func limit() -> u32 { super::LIMIT + package::LIMIT }
		}
		use geo::Point;
		global COUNT: u32 = 0;
		const LIMIT: u32 = 10;
		func id<T: StackValue>(value: T) -> T { value }
		func main() -> i32 {
		    local mut total: i32 = 0;
		    local p = Point(1, 2);
		    total = p.sum();
		    total += id(1: i32);
		    block :out { break :out; }
		    total
		}
		export { main, COUNT }
	"};
	let (state, dir) = analyzed(&root, source);
	assert!(
		!state.cached[&dir].sema.diagnostics().has_errors(),
		"the fixture checks cleanly"
	);
	let uri = Uri::from_file_path(&root).unwrap();
	let tokens = semantic_tokens(&state, &uri, source, None);
	// A name written as a keyword is a keyword token, whatever it resolves
	// to (the receiver, the impl's target, the parent module), with no
	// modifiers; the label `out` is no token.
	assert_eq!(
		tokens,
		[
			"geo:namespace.declaration",
			"Point:struct.declaration",
			"x:property.declaration",
			"i32:type.defaultLibrary",
			"y:property.declaration",
			"i32:type.defaultLibrary",
			"Point:struct",
			"sum:method.declaration",
			"self:keyword",
			"Self:keyword",
			"i32:type.defaultLibrary",
			"self:keyword",
			"x:property",
			"self:keyword",
			"y:property",
			"origin:function.declaration",
			"Self:keyword",
			"Self:keyword",
			"limit:function.declaration",
			"u32:type.defaultLibrary",
			"super:keyword",
			"LIMIT:variable.readonly",
			"package:keyword",
			"LIMIT:variable.readonly",
			"geo:namespace",
			"Point:struct",
			"COUNT:variable.declaration.readonly.static",
			"u32:type.defaultLibrary",
			"LIMIT:variable.declaration.readonly",
			"u32:type.defaultLibrary",
			"id:function.declaration",
			"T:typeParameter.declaration",
			"StackValue:interface",
			"value:parameter.declaration",
			"T:typeParameter",
			"T:typeParameter",
			"value:parameter",
			"main:function.declaration",
			"i32:type.defaultLibrary",
			"total:variable.declaration",
			"i32:type.defaultLibrary",
			"p:variable.declaration",
			"Point:struct",
			"total:variable.modification",
			"p:variable",
			"sum:method",
			"total:variable.modification",
			"id:function",
			"i32:type.defaultLibrary",
			"total:variable",
			"main:function",
			"COUNT:variable.readonly.static",
		]
	);
}

#[test]
fn semantic_tokens_count_columns_in_utf16_and_honour_a_range() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Pair(left: u32, right: u32);
		func main() -> u32 {
		    local c: Char = '😀'; local d = c;
		    _ = d;
		    local Pair({ left, right }) = Pair(1, 2);
		    left + right
		}
		export { main }
	"};
	let (state, dir) = analyzed(&root, source);
	assert!(
		!state.cached[&dir].sema.diagnostics().has_errors(),
		"the fixture checks cleanly"
	);
	let uri = Uri::from_file_path(&root).unwrap();
	// The emoji is two UTF-16 units: `d` and `c` after it still decode to
	// their own text.
	let line = Range {
		start: position_of(source, "local c", 0),
		end: position_of(source, "_ = d", 0),
	};
	assert_eq!(
		semantic_tokens(&state, &uri, source, Some(line)),
		[
			"c:variable.declaration",
			"Char:struct",
			"d:variable.declaration",
			"c:variable",
		]
	);
	// A shorthand field pattern names the field and binds the local; the
	// binding is what it means.
	let pattern = Range {
		start: position_of(source, "local Pair", 0),
		end: position_of(source, "left +", 0),
	};
	assert_eq!(
		semantic_tokens(&state, &uri, source, Some(pattern)),
		[
			"Pair:struct",
			"left:variable.declaration",
			"right:variable.declaration",
			"Pair:struct",
			"left:variable",
		]
	);
}

#[test]
fn semantic_tokens_mark_only_what_the_compiler_provides() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		func main() -> i32 {
		    local same = (1: u32).ne(2);
		    _ = same;
		    transmute(7: u32)
		}
		export { main }
	"};
	let (state, dir) = analyzed(&root, source);
	assert!(
		!state.cached[&dir].sema.diagnostics().has_errors(),
		"the fixture checks cleanly"
	);
	let uri = Uri::from_file_path(&root).unwrap();
	// `transmute` is a function core leaves to the compiler, and `u32` a
	// primitive; `ne` has a body in core, so it is an ordinary method.
	assert_eq!(
		semantic_tokens(&state, &uri, source, None),
		[
			"main:function.declaration",
			"i32:type.defaultLibrary",
			"same:variable.declaration",
			"u32:type.defaultLibrary",
			"ne:method",
			"same:variable",
			"transmute:function.defaultLibrary",
			"u32:type.defaultLibrary",
			"main:function",
		]
	);
}

/// Renames the `occurrence`-th `needle` of an ASCII `source` to `new_name`
/// and applies the edits for `uri`: the renamed source, or why the rename
/// was refused.
fn renamed(
	state: &ServerState,
	uri: &Uri,
	source: &str,
	needle: &str,
	occurrence: usize,
	new_name: &str,
) -> Result<String, String> {
	let position = TextDocumentPositionParams {
		text_document: TextDocumentIdentifier { uri: uri.clone() },
		position: position_of(source, needle, occurrence),
	};
	let prepared = crate::rename::prepare(state, &position)?;
	assert!(prepared.is_some(), "a name under the cursor");
	let params = tower_lsp_server::ls_types::RenameParams {
		text_document_position: position,
		new_name: new_name.to_string(),
		work_done_progress_params: Default::default(),
	};
	let edit = crate::rename::rename(state, &params)?.expect("an edit");
	let mut edits = edit.changes.unwrap().remove(uri).unwrap_or_default();
	let offset = |position: Position| {
		let line_start: usize = source
			.split_inclusive('\n')
			.take(position.line as usize)
			.map(str::len)
			.sum();
		line_start + position.character as usize
	};
	edits.sort_by_key(|edit| std::cmp::Reverse(offset(edit.range.start)));
	let mut text = source.to_string();
	for edit in edits {
		text.replace_range(
			offset(edit.range.start)..offset(edit.range.end),
			&edit.new_text,
		);
	}
	Ok(text)
}

#[test]
fn rename_rewrites_the_declaration_and_every_use() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		mod geo {
		    pub struct Point(pub x: i32, pub y: i32);
		    impl Point {
		        pub func origin() -> Self { Self(0, 0) }
		    }
		}
		use geo::Point;
		use geo::Point as P;
		func area(p: Point) -> i32 { p.x * p.y }
		func main() -> i32 {
		    local p: P = Point(2, 3);
		    block :out { break :out; }
		    area(p)
		}
		export { main }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let rename = |needle, occurrence, new| {
		renamed(&state, &uri, source, needle, occurrence, new)
	};

	// The struct, its constructor call and the `use` leaf; `Self` and the
	// alias `P` keep their spelling.
	let text = rename("Point", 0, "Spot").unwrap();
	assert!(text.contains("pub struct Spot(pub x: i32"), "{text}");
	assert!(text.contains("impl Spot {"), "{text}");
	assert!(text.contains("-> Self { Self(0, 0) }"), "{text}");
	assert!(
		text.contains("use geo::Spot;\nuse geo::Spot as P;"),
		"{text}"
	);
	assert!(text.contains("func area(p: Spot)"), "{text}");
	assert!(text.contains("local p: P = Spot(2, 3);"), "{text}");

	// A field, from one of its uses.
	let text = rename("x * ", 0, "width").unwrap();
	assert!(text.contains("pub width: i32"), "{text}");
	assert!(text.contains("p.width * p.y"), "{text}");

	// A label, without its `:`.
	let text = rename("out;", 0, "done").unwrap();
	assert!(text.contains("block :done { break :done; }"), "{text}");

	// An export with no `as` keeps its Wasm name.
	let text = rename("main", 0, "start").unwrap();
	assert!(text.contains("func start() -> i32"), "{text}");
	assert!(text.contains("export { start as \"main\" }"), "{text}");
}

#[test]
fn rename_expands_a_shorthand_to_keep_its_other_side() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Pair(left: u32, right: u32);
		func take(left: u32) -> u32 { left }
		func main() -> u32 {
		    local left: u32 = 1;
		    local pair = Pair({ left, right: 2 });
		    local Pair({ right, .. }) = pair;
		    take({ left }) + right
		}
		export { main }
	"};
	let (state, dir) = analyzed(&root, source);
	assert!(
		!state.cached[&dir].sema.diagnostics().has_errors(),
		"the fixture checks cleanly"
	);
	let uri = Uri::from_file_path(&root).unwrap();
	let rename = |needle, occurrence, new| {
		renamed(&state, &uri, source, needle, occurrence, new)
	};

	// The caller's local is the value side of both argument shorthands.
	let text = rename("left: u32 = 1", 0, "first").unwrap();
	assert!(text.contains("local first: u32 = 1;"), "{text}");
	assert!(text.contains("Pair({ left: first, right: 2 })"), "{text}");
	assert!(text.contains("take({ left: first })"), "{text}");

	// The field is the label side of the construction's shorthand.
	let text = rename("left: u32, right", 0, "head").unwrap();
	assert!(text.contains("struct Pair(head: u32"), "{text}");
	assert!(text.contains("Pair({ head: left, right: 2 })"), "{text}");
	assert!(text.contains("take({ left })"), "{text}");

	// The callee's parameter is the label side of the call's shorthand.
	let text = rename("left: u32) -> u32", 0, "value").unwrap();
	assert!(
		text.contains("func take(value: u32) -> u32 { value }"),
		"{text}"
	);
	assert!(text.contains("take({ value: left })"), "{text}");

	// A pattern's shorthand names the field and binds the local.
	let text = rename("right: u32", 0, "tail").unwrap();
	assert!(text.contains("local Pair({ tail: right, .. })"), "{text}");
	assert!(text.contains("+ right"), "{text}");
	let text = rename("right\n}", 0, "rest").unwrap();
	assert!(text.contains("local Pair({ right: rest, .. })"), "{text}");
	assert!(text.contains("+ rest"), "{text}");
}

#[test]
fn rename_keeps_the_field_a_host_import_is_imported_as() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		import \"host\" as host {
		    func log(value: i32);
		    \"Tick\": func tick();
		}
		mod inner {
		    import \"host\" as host { global depth: i32; }
		}
		func main() { host::log(1); host::tick(); }
		export { main }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let text = renamed(&state, &uri, source, "log(1", 0, "print").unwrap();
	assert!(text.contains("\"log\": func print(value: i32);"), "{text}");
	assert!(text.contains("host::print(1)"), "{text}");
	// Already named by its field, which renaming leaves alone.
	let text = renamed(&state, &uri, source, "tick()", 1, "step").unwrap();
	assert!(text.contains("\"Tick\": func step();"), "{text}");
	assert!(text.contains("host::step()"), "{text}");
	// A global, in an inline module's block.
	let text = renamed(&state, &uri, source, "depth", 0, "level").unwrap();
	assert!(text.contains("\"depth\": global level: i32;"), "{text}");
}

#[test]
fn rename_refuses_what_it_cannot_rename() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		mod geo {
		    pub struct Point(x: i32);
		}
		use geo::Point as P;
		struct Meters(value: u32);
		impl Meters {
		    func get(self: Self) -> u32 { self.value }
		}
		func main(p: P) -> u32 { 0 }
		export { main }
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let refusal = |needle, occurrence| {
		renamed(&state, &uri, source, needle, occurrence, "fresh")
			.expect_err("refused")
	};
	assert!(refusal("u32", 0).contains("standard library"));
	assert!(refusal("self.", 0).contains("keyword"));
	assert!(refusal("P)", 0).contains("through an alias"));
	assert_eq!(
		renamed(&state, &uri, source, "Meters", 0, "fn Bad").unwrap_err(),
		"`fn Bad` is not an identifier"
	);
	assert_eq!(
		renamed(&state, &uri, source, "Meters", 0, "loop").unwrap_err(),
		"`loop` is a keyword"
	);
}

#[test]
fn rename_refuses_a_module_in_a_file_of_its_own() {
	let dir = PathBuf::from("/test");
	let main = dir.join("main.wx");
	let source =
		"mod geo;\nfunc main() -> i32 { geo::two() }\nexport { main }\n";
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(main.clone(), open_document(source));
	state.open_documents.insert(
		dir.join("geo.wx"),
		open_document("pub func two() -> i32 { 2 }\n"),
	);
	open_synthetic_manifest(&mut state, &main);
	analyze_root(&mut state, &dir, &main, &mut Vec::new());
	let uri = Uri::from_file_path(&main).unwrap();
	let refusal = renamed(&state, &uri, source, "geo::", 0, "shapes")
		.expect_err("refused");
	assert!(refusal.contains("file of its own"), "{refusal}");
}

// ── Completion ──────────────────────────────────────────────────────────

/// The labels completion offers where `$0` is written in `source`, in the
/// order they sort; `None` when it offers nothing there.
fn completions(source: &str) -> Option<Vec<String>> {
	let items = completion_items(source, false)?;
	Some(items.into_iter().map(|item| item.label).collect())
}

/// The items offered at `$0`, sorted as the client shows them, by a server
/// whose client takes snippets or not.
fn completion_items(
	source: &str,
	snippets: bool,
) -> Option<Vec<tower_lsp_server::ls_types::CompletionItem>> {
	let offset = source.find("$0").expect("a `$0` marks the cursor");
	let text = source.replacen("$0", "", 1);
	let root = PathBuf::from("/test/main.wx");
	let (mut state, _) = analyzed(&root, &text);
	state.client.completion_snippets = snippets;
	let uri = Uri::from_file_path(&root).unwrap();
	let line = text[..offset].matches('\n').count();
	let line_start = text[..offset].rfind('\n').map_or(0, |at| at + 1);
	let params = tower_lsp_server::ls_types::CompletionParams {
		text_document_position: TextDocumentPositionParams {
			text_document: TextDocumentIdentifier { uri },
			position: Position {
				line: line as u32,
				character: (offset - line_start) as u32,
			},
		},
		work_done_progress_params: Default::default(),
		partial_result_params: Default::default(),
		context: None,
	};
	let Some(tower_lsp_server::ls_types::CompletionResponse::Array(mut items)) =
		crate::completion::completion(&state, &params)
	else {
		return None;
	};
	if items.is_empty() {
		return None;
	}
	items.sort_by(|a, b| a.sort_text.cmp(&b.sort_text));
	Some(items)
}

/// Whether `labels` holds every one of `expected`, and none of `absent`.
fn assert_offers(labels: &[String], expected: &[&str], absent: &[&str]) {
	for name in expected {
		assert!(
			labels.iter().any(|l| l == name),
			"`{name}` missing: {labels:?}"
		);
	}
	for name in absent {
		assert!(
			!labels.iter().any(|l| l == name),
			"`{name}` offered: {labels:?}"
		);
	}
}

const COMPLETION_ITEMS: &str = "struct Point(x: u32);\nfunc helper() {}\n";

#[test]
fn completion_of_a_value_offers_locals_first_then_items() {
	let labels = completions(&format!(
		"{COMPLETION_ITEMS}func f(count: u32) {{\n    local total = count;\n    to$0\n}}\n"
	))
	.expect("a name is being written");
	assert_offers(&labels, &["total", "count", "helper", "Point"], &["u32"]);
	assert_eq!(&labels[..2], ["count", "total"], "locals sort first");
}

#[test]
fn completion_of_a_type_offers_types() {
	let labels = completions(&format!(
		"{COMPLETION_ITEMS}func f<T>(count: u32) {{\n    local p: P$0 = Point(1);\n}}\n"
	))
	.expect("a type is being written");
	assert_offers(&labels, &["T", "Point", "u32"], &["count"]);
}

#[test]
fn completion_where_nothing_is_written_yet() {
	// A local's value, a local's type, a statement, an argument.
	for (source, tier_name) in [
		("func f() {\n    local a = $0\n}\n", "helper"),
		("func f() {\n    local a: $0\n}\n", "u32"),
		("func f() {\n    helper();\n    $0\n}\n", "helper"),
		(
			"func g(a: u32, b: u32) {}\nfunc f() {\n    g(1, $0)\n}\n",
			"helper",
		),
	] {
		let labels = completions(&format!("{COMPLETION_ITEMS}{source}"))
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(&labels, &[tier_name], &[]);
	}
}

#[test]
fn completion_at_the_end_of_a_constant_initializer() {
	let labels = completions("const B: u32 = 1;\nconst A: u32 = B$0;\n")
		.expect("an initializer is a body");
	assert_offers(&labels, &["B", "A"], &[]);
}

#[test]
fn completion_in_a_value_after_a_part_left_out() {
	// An enum with no repr: its variant's value; a constant with no type.
	for source in [
		"const B: u32 = 1;\nenum E { A = B$0 }\n",
		"const B: u32 = 1;\nglobal g = B$0;\n",
	] {
		let labels = completions(source)
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(&labels, &["B"], &[]);
	}
}

#[test]
fn completion_inside_a_keyword_blocks_braces() {
	let labels = completions(&format!(
		"{COMPLETION_ITEMS}func f() {{\n    block :done {{ $0 }};\n}}\n"
	))
	.expect("the room inside the braces");
	assert_offers(&labels, &["helper"], &[]);
}

#[test]
fn completion_offers_nothing_where_no_name_is_looked_up() {
	for source in [
		// A comment, a binding's own name, a literal, a member, a segment
		// after a type.
		"func f() {\n    // hel$0\n}\n",
		"func f() {\n    local na$0me = 1;\n}\n",
		"func f() {\n    local a: u32 = 12$0;\n}\n",
		"func f(p: Point) {\n    p.x$0;\n}\n",
		// After a type: its members, which are not completed yet.
		"func f() {\n    Point::$0\n}\n",
		// A parameter's own name, and its type's later segment.
		"func f(cou$0nt: u32) {}\n",
		"func f(p: Point::$0) {}\n",
		// A use and an export.
		"use hel$0per;\n",
		// Right after a call's arguments.
		"func f() {\n    helper()$0;\n}\n",
		// A keyword block's keyword and label, before its braces.
		"func f() {\n    blo$0ck { 1 };\n}\n",
		"func f() {\n    block :do$0ne { 1 };\n}\n",
	] {
		assert_eq!(
			completions(&format!("{COMPLETION_ITEMS}{source}")),
			None,
			"{source:?}"
		);
	}
}

#[test]
fn completion_after_a_module_offers_what_it_makes_visible() {
	let source = "mod shapes {\n    pub func area() -> u32 { 1 }\n    func hidden() {}\n}\nfunc f() {\n    shapes::$0\n}\n";
	let labels = completions(source).expect("a segment after a module");
	assert_offers(&labels, &["area"], &["hidden", "f"]);
	// A segment being written continues the same path.
	let typed = completions(&source.replace("::$0", "::ar$0")).unwrap();
	assert_offers(&typed, &["area"], &["hidden"]);
}

#[test]
fn completion_after_an_enum_offers_its_variants() {
	let labels = completions(
		"enum Kind(u8) { A = 0, B }\nfunc f(k: Kind) -> u8 {\n    match k {\n        Kind::$0 => 1,\n        _ => 2,\n    }\n}\n",
	)
	.expect("a pattern path after an enum");
	assert_eq!(labels, ["A", "B"]);
}

#[test]
fn completion_of_a_label_offers_the_ones_a_jump_can_name() {
	let source = "func f() {\n    loop :outer {\n        block :inner {\n            break :$0\n        }\n    }\n}\n";
	assert_eq!(completions(source).unwrap(), ["inner", "outer"]);
	let continuing = source.replace("break :$0", "continue :$0");
	assert_eq!(
		completions(&continuing).unwrap(),
		["outer"],
		"a `continue` restarts only a loop"
	);
}

#[test]
fn completion_in_a_signature_offers_its_parameters_and_types() {
	for (source, expected, absent) in [
		// A parameter's type: the function's own parameters.
		(
			"func f<T>(p: Po$0) {}\n",
			&["T", "Point", "u32"][..],
			&["p"][..],
		),
		// A parameter's type not written yet, and a field's.
		(
			"func f(x: u32, y: $0) -> u32 {}\n",
			&["Point", "u32"],
			&["x"],
		),
		("func f(x: u32, y:$0) -> u32 {}\n", &["Point", "u32"], &[]),
		("struct Pair(a: u32, b: $0);\n", &["Point", "u32"], &[]),
		// A result, a field, a bound.
		("func f<T>() -> T$0 {}\n", &["T"], &[]),
		("struct Pair<A>(left: A$0);\n", &["A", "Point"], &[]),
		(
			"trait Show {}\nfunc f<T: Sh$0>() {}\n",
			&["Show"],
			&["T", "Point"],
		),
		// A bound not written yet, as a supertrait.
		(
			"trait Show {}\ntrait X: $0 {}\n",
			&["Show", "Add"],
			&["Point", "u32"],
		),
		// A trait's member: its own parameters; its associated type's
		// bound, in the trait's scope.
		(
			"trait Tr {\n    func m<U>(self: Self, u: U$0);\n}\n",
			&["U"],
			&[],
		),
		(
			"trait Show {}\ntrait Tr {\n    type Item: Sh$0;\n}\n",
			&["Show"],
			&[],
		),
		// What has no bounds: a typeset's members, an associated type's
		// default.
		("typeset Small { u8, u1$0 }\n", &["u16"], &[]),
		(
			"trait Show {}\ntrait Tr {\n    type Item = u3$0;\n}\n",
			&["Self", "Point", "u32"],
			&["Show", "Tr"],
		),
		// An impl: its header, its members' signatures and associated types,
		// with the impl's parameters.
		(
			"struct W<T>(v: T);\ntrait Tr { type Item; }\nimpl<T> Tr for W<T$0> {\n    type Item = T;\n}\n",
			&["T", "W"],
			&[],
		),
		(
			"struct W<T>(v: T);\ntrait Tr { type Item; }\nimpl<T> Tr for W<T> {\n    type Item = T$0;\n}\n",
			&["T"],
			&[],
		),
		(
			"struct W<T>(v: T);\nimpl<T> W<T> {\n    func get<U>(self: Self, u: U$0) {}\n}\n",
			&["U", "T"],
			&[],
		),
	] {
		let labels = completions(&format!("{COMPLETION_ITEMS}{source}"))
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert!(
			expected.iter().all(|name| labels.iter().any(|l| l == name))
				&& absent.iter().all(|name| labels.iter().all(|l| l != name)),
			"wrong completions in {source:?}: {labels:?}"
		);
	}
}

#[test]
fn completion_lists_the_renamed_literal_kinds() {
	let labels = completions("const N: con$0 = 42;\n")
		.expect("a constant annotation offers literal kinds");
	assert_offers(
		&labels,
		&["const_int", "const_float", "const_char"],
		&["integer", "char"],
	);
}

#[test]
fn completion_in_a_missing_function_result_offers_types() {
	for (source, parameters) in [
		("pub func f<T>(x: T) -> $0 {}", &["T"][..]),
		("func f()->$0{}", &[][..]),
		("func f() -> $0 { 1 }", &[][..]),
		(
			"struct W<T>(v: T); impl<T> W<T> { pub func to_f64(self: Self) -> $0 { 1 } }",
			&["Self", "T"][..],
		),
		(
			"trait Tr: StackValue { func f(self: Self) -> f64; } impl Tr for Point { func f(self: Self) -> $0 { 1 } }",
			&["Self"][..],
		),
		("trait Tr { func f(self: Self) -> $0; }", &["Self"][..]),
		(
			"trait Tr { func f(self: Self) -> $0 { self } }",
			&["Self"][..],
		),
	] {
		let labels = completions(&format!(
			"{COMPLETION_ITEMS}trait Show {{}}\n{source}\n"
		))
		.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(&labels, &["Point", "u32", "f64"], &["x", "Show"]);
		assert_offers(&labels, parameters, &[]);
	}
}

#[test]
fn completion_distinguishes_bounds_from_impl_traits() {
	const ITEMS: &str = "trait Show {}\ntypeset Small { u8, u16 }\nstruct Point();\nfunc helper() {}\n";
	for source in [
		"func f<T: Sh$0>() {}",
		"func f<T: $0>() {}",
		"func f<T:$0>() {}",
		"trait X: Sh$0 {}",
		"trait X: $0 {}",
		"trait X:$0 {}",
		"trait X { type Item: $0; }",
		"trait X { type Item: $0 = u8; }",
		"typeset X: $0 { u8 }",
		"func f<T: Show where { Item: $0 }>() {}",
		"func f<T>() { <T as Sh$0>::x; }",
	] {
		let labels = completions(&format!("{ITEMS}{source}\n"))
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(
			&labels,
			&["Show", "Small", "Add", "PointerSize", "core"],
			&["Self", "T", "Point", "u32", "helper"],
		);
	}
	let labels = completions(&format!("{ITEMS}impl Sh$0 for Point {{}}\n"))
		.expect("an impl names a declared trait");
	assert_offers(
		&labels,
		&["Show", "Add", "core"],
		&["Small", "PointerSize", "Self", "Point", "u32", "helper"],
	);
	// The same distinction applies to the final segment after a namespace.
	const MODULE: &str = "mod names { pub trait Show {} pub typeset Small { u8 } pub struct Other(); pub func helper() {} }\nstruct Point();\n";
	for (source, bound) in [
		("func f<T: names::Sh$0>() {}", true),
		("trait X: names::Sh$0 {}", true),
		("impl names::Sh$0 for Point {}", false),
	] {
		let labels = completions(&format!("{MODULE}{source}\n"))
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(&labels, &["Show"], &["Other", "helper"]);
		assert_eq!(
			labels.iter().any(|name| name == "Small"),
			bound,
			"{source:?}"
		);
	}
}

const NAMED_CALLS: &str = "\
func g(alpha: u32, beta: u32) {}
struct W();
trait Tr { func m(self: Self, count: u32); }
impl Tr for W { func m(self: Self, _: u32) {} }
impl W { func own(self: Self, first: u32) {} }
func h(u32) {}
";

#[test]
fn completion_of_a_named_argument_offers_the_callees_names() {
	for (source, expected, absent) in [
		// The room in the braces, and a name being written (a shorthand).
		("g({ $0 })", &["alpha", "beta"][..], &["helper"][..]),
		("g({ al$0 })", &["alpha", "beta"], &[]),
		// A name written already is reported if written again.
		("g({ alpha: 1, $0 })", &["beta"], &["alpha"]),
		// A struct's fields.
		("Point({ $0 })", &["x"], &[]),
		// A method's receiver: named through its type, given by the object.
		("W::own({ $0 })", &["self", "first"], &[]),
		("W().own({ $0 })", &["first"], &["self"]),
		// A trait impl's function is named as its trait declares it, even
		// where the impl leaves the parameter unnamed.
		("W().m({ $0 })", &["count"], &["self"]),
	] {
		let labels = completions(&format!(
			"{COMPLETION_ITEMS}{NAMED_CALLS}func f() {{\n    {source};\n}}\n"
		))
		.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(&labels, expected, absent);
	}
}

#[test]
fn completion_after_a_named_arguments_colon_offers_values() {
	let labels = completions(&format!(
		"{COMPLETION_ITEMS}{NAMED_CALLS}func f(n: u32) {{\n    g({{ alpha: $0 }});\n}}\n"
	))
	.expect("a value not written yet");
	assert_offers(&labels, &["n", "helper"], &["alpha", "beta"]);
}

#[test]
fn completion_offers_no_argument_names_the_checker_would_refuse() {
	for source in [
		// An unnamed parameter makes a call positional only (E2123).
		"func f() {\n    h({ $0 });\n}\n",
		// After the list.
		"func f() {\n    g({ alpha: 1, beta: 2 })$0;\n}\n",
		// Braces not closed yet.
		"func f() {\n    g({ $0",
	] {
		assert_eq!(
			completions(&format!("{COMPLETION_ITEMS}{NAMED_CALLS}{source}")),
			None,
			"{source:?}"
		);
	}
}

/// What each label inserts at `$0` for a client that takes snippets: the
/// label itself when the item carries no text of its own.
fn inserted(source: &str) -> Vec<(String, String)> {
	let items = completion_items(&format!("{COMPLETION_ITEMS}{source}"), true)
		.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
	(items.into_iter())
		.map(|item| {
			let text = item.insert_text.unwrap_or_else(|| item.label.clone());
			(item.label, text)
		})
		.collect()
}

#[test]
fn completion_inserts_a_call_of_a_function_or_a_constructor() {
	let find = |source: &str, label: &str| {
		inserted(source)
			.into_iter()
			.find(|(each, _)| each == label)
			.unwrap_or_else(|| panic!("`{label}` missing in {source:?}"))
			.1
	};
	let body = "func g(a: u32) {}\nfunc f(n: u32) {\n    $0\n}\n";
	// A call's parameters to fill, none, and a constructor's fields.
	assert_eq!(find(body, "g"), "g($1)");
	assert_eq!(find(body, "helper"), "helper()");
	assert_eq!(find(body, "Point"), "Point($1)");
	// A local is its name.
	assert_eq!(find(body, "n"), "n");
	// Written as a type, a function is its name; a call written already
	// keeps its arguments.
	assert_eq!(find("func f(p: hel$0) {}\n", "helper"), "helper");
	assert_eq!(find("func f() {\n    hel$0(1);\n}\n", "helper"), "helper");
	// A client without snippets gets the name.
	let items = completion_items(
		&format!("{COMPLETION_ITEMS}func f() {{\n    $0\n}}\n"),
		false,
	)
	.expect("names in a body");
	assert!(items.iter().all(|item| item.insert_text.is_none()));
}

#[test]
fn completion_after_a_module_in_a_signature() {
	let labels = completions(
		"mod shapes {\n    pub struct Square();\n    struct Hidden();\n}\nfunc f(s: shapes::$0) {}\n",
	)
	.expect("a segment after a module");
	assert_offers(&labels, &["Square"], &["Hidden"]);
}
