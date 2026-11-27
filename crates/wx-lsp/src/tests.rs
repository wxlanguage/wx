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
use crate::projects::{Manifest, ProjectState, discover_package_root};
use crate::requests;
use crate::snapshot::Snapshot;
use crate::state::{
	ClientConfig, ServerState, analyze_root, compute_active_refresh,
	compute_refresh, refresh_project_manifest,
};
use crate::trace::Trace;
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
/// A trace for a command the test performs directly.
fn trace() -> Trace {
	Trace::new("test", None)
}

fn analyzed(root: &Path, source: &str) -> (ServerState, PathBuf) {
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(root.to_path_buf(), open_document(source));
	let dir = open_synthetic_manifest(&mut state, root);
	analyze_root(&mut state, &dir, &mut trace());
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

	compute_refresh(&mut state, &hashing_main, &mut trace());
	assert!(state.cached.contains_key(&hashing_dir));

	state.open_documents.insert(
		pow_main.clone(),
		open_document("pub func pow(base: i32, exp: i32) -> Bool { True }"),
	);
	let mut trace = trace();
	let publications = compute_active_refresh(
		&mut state,
		vec![pow_main.clone(), pow_main],
		&mut trace,
	);
	assert_eq!(
		trace.count("check"),
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

	let broken = analyze_root(&mut state, &dir, &mut trace());
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
	let fixed = analyze_root(&mut state, &dir, &mut trace());
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

	let broken = compute_refresh(&mut state, &child, &mut trace());
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
	let fixed = compute_refresh(&mut state, &child, &mut trace());
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

	let offset =
		usize::from(position_to_offset(files, file, position).unwrap());
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
		compute_refresh(&mut state, Path::new(file), &mut trace());
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
fn lints_are_published_at_the_level_the_manifest_sets() {
	let root = PathBuf::from("/workspace/app/main.wx");
	let manifest_path = PathBuf::from("/workspace/app/wx.json");
	let mut state = ServerState::default();
	state.open_documents.insert(
		root.clone(),
		open_document("func f() {\n    local unused: i32 = 1;\n}\n"),
	);
	let dir = open_synthetic_manifest(&mut state, &root);
	let published = |state: &mut ServerState, manifest: &str| {
		state
			.open_documents
			.insert(manifest_path.clone(), open_document(manifest));
		refresh_project_manifest(state, &manifest_path);
		let analysis = analyze_root(state, &dir, &mut trace());
		analysis
			.diagnostics_by_file
			.get(&root)
			.cloned()
			.unwrap_or_default()
	};

	let warned = published(&mut state, r#"{ "entry": "main.wx" }"#);
	assert_eq!(warned.len(), 1);
	assert_eq!(warned[0].severity, Some(DiagnosticSeverity::WARNING));
	assert_eq!(
		warned[0].code,
		Some(tower_lsp_server::ls_types::NumberOrString::String(
			wx_lint::Lint::UnusedVariable.code().to_string()
		))
	);
	assert_eq!(
		warned[0].tags,
		Some(vec![tower_lsp_server::ls_types::DiagnosticTag::UNNECESSARY])
	);

	let denied = published(
		&mut state,
		r#"{ "entry": "main.wx", "lint": { "unused_variable": "error" } }"#,
	);
	assert!(denied.len() == 1 && is_error(&denied[0]));

	let off = r#"{ "entry": "main.wx", "lint": { "unused_variable": "off" } }"#;
	assert!(published(&mut state, off).is_empty());

	// An invalid `lint` section disables linting, not the project.
	let invalid = r#"{ "entry": "main.wx", "lint": { "unused": "off" } }"#;
	assert!(published(&mut state, invalid).is_empty());
	let sections = &state.projects[&dir].manifest;
	assert!(sections.package.is_some() && sections.lint.is_none());
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
fn a_jump_keyword_and_its_label_lead_to_different_declarations() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		func f(c: Bool) -> u32 {
			local x: u32 = block { break 2; };
			if (c) { return x; }
			loop :outer {
				loop {
					if (c) { continue :outer; }
					break;
				}
				break :outer x;
			}
		}
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(root).unwrap();
	let definition = |needle, occurrence| {
		scalar(requests::goto_definition(
			&state,
			&definition_params(&uri, position_of(source, needle, occurrence)),
		))
		.range
		.start
	};
	let references = |needle, occurrence| {
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

	// A keyword leads to the loop or block it leaves or restarts, labelled
	// or not.
	assert_eq!(definition("break", 0), position_of(source, "block", 0));
	assert_eq!(definition("continue", 0), position_of(source, "loop", 0));
	assert_eq!(definition("break", 1), position_of(source, "loop", 1));
	assert_eq!(definition("break", 2), position_of(source, "loop", 0));
	// A `return` leads to the keyword of the function it leaves, not to its
	// name, as a `break` leads to its loop's keyword and not its label.
	assert_eq!(definition("return", 0), position_of(source, "func", 0));
	// A label leads to the label.
	assert_eq!(definition("outer", 1), position_of(source, "outer", 0));
	assert_eq!(definition("outer", 2), position_of(source, "outer", 0));

	assert_eq!(
		references("loop", 0),
		[
			position_of(source, "continue", 0),
			position_of(source, "break", 2),
		]
	);
	assert_eq!(references("loop", 1), [position_of(source, "break", 1)]);
	assert_eq!(references("block", 0), [position_of(source, "break", 0)]);
	assert_eq!(references("func", 0), [position_of(source, "return", 0)]);
	assert_eq!(
		references("outer", 0),
		[
			position_of(source, "outer", 1),
			position_of(source, "outer", 2)
		]
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
			local s = S{ value };
			_ = take{ value: s.value };
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
		position_of(source, "value };", 0),
		position_of(source, "value };", 1),
	];
	assert_eq!(refs("value:", 0), field);
	let local = vec![
		position_of(source, "value };", 0),
		position_of(source, "value\n", 0),
	];
	assert_eq!(refs("value:", 2), local);
	assert_eq!(refs("value };", 0), local);
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
	analyze_root(&mut state, &dir, &mut trace());
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
	// A function's keyword declares its body, which no `return` leaves.
	assert_eq!(
		requests::references(&state, &params("func", false)),
		Some(vec![])
	);
}

#[tokio::test]
async fn initialization_advertises_references_and_completion_triggers() {
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
	assert_eq!(
		result
			.capabilities
			.completion_provider
			.unwrap()
			.trigger_characters,
		Some(vec![".".into(), ":".into(), "\"".into()])
	);
	let help = result.capabilities.signature_help_provider.unwrap();
	assert_eq!(
		help.trigger_characters,
		Some(vec!["(".into(), ",".into(), "{".into(), ":".into()])
	);
	assert_eq!(
		help.retrigger_characters,
		Some(vec![")".into(), "}".into()])
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
	compute_refresh(&mut state, &app, &mut trace());
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
fn hover_renders_a_jump_and_its_target_as_signatures() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		func f(n: u32) -> u32 {
			local x: u32 = block :done { if (n == 0) { break :done 1 }; 2 };
			loop :outer (i: u32 = 0, mut total: u32 = x) {
				if (i == n) { break total };
				loop {
					if (i == 1) { continue :outer(i + 1, total) };
					break;
				}
				continue { i: i + 1, total: total + i }
			}
		}
		func pair() -> (u32, u32) {
			loop { break (1, 2) }
		}
		func spin() {
			loop {}
		}
		func pick(c: Bool, d: Bool) -> u8 {
			if (c) { 1 } else if (d) { 2 } else { 3 }
		}
		func split(a: u8, b: Bool) -> (u8, Bool) {
			if (b) { return (a, b) };
			match (a, b) {
				(0, _) => (1, b),
				_ => return (0, b),
			}
		}
		func stop() {
			return;
		}
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(root).unwrap();
	let hover = |needle, occurrence| {
		hover_text(&state, &uri, source, needle, occurrence)
			.unwrap_or_else(|| panic!("no hover on `{needle}` #{occurrence}"))
	};
	let wx = |signature: &str| format!("```wx\n{signature}\n```");

	// A target: its parameters and the type leaving it gives.
	assert_eq!(hover("block", 0), wx("block :done() -> u32"));
	assert_eq!(
		hover("loop", 0),
		wx("loop :outer(i: u32, mut total: u32) -> u32")
	);
	assert_eq!(hover("loop", 1), wx("loop() -> ()"));
	assert_eq!(hover("loop", 2), wx("loop() -> (u32, u32)"));
	assert_eq!(hover("loop", 3), wx("loop() -> !"));
	// A `break` takes the values its target gives, a `continue` its loop's
	// parameters; neither falls through.
	assert_eq!(hover("break", 0), wx("break :done(u32) -> !"));
	assert_eq!(hover("break", 1), wx("break :outer(u32) -> !"));
	assert_eq!(hover("break", 2), wx("break() -> !"));
	assert_eq!(hover("break", 3), wx("break(u32, u32) -> !"));
	assert_eq!(
		hover("continue", 0),
		wx("continue :outer(i: u32, mut total: u32) -> !")
	);
	assert_eq!(
		hover("continue", 1),
		wx("continue :outer(i: u32, mut total: u32) -> !")
	);
	// An `if` takes its condition and gives its branches' value; it is no
	// target, and one without `else` gives `()`.
	assert_eq!(hover("if", 0), wx("if(Bool) -> ()"));
	assert_eq!(hover("if (c)", 0), wx("if(Bool) -> u8"));
	assert_eq!(hover("if (d)", 0), wx("if(Bool) -> u8"));
	// A `match` takes the value it matches, a tuple as its values.
	assert_eq!(hover("match", 0), wx("match(u8, Bool) -> (u8, Bool)"));
	// A `return` takes the values its body gives.
	assert_eq!(hover("return", 0), wx("return(u8, Bool) -> !"));
	assert_eq!(hover("return", 2), wx("return() -> !"));
	// The keyword declaring a body reads as its owner.
	assert_eq!(hover("func", 3), wx("func pick(c: Bool, d: Bool) -> u8"));
}

#[test]
fn hover_renders_signatures_from_the_resolved_name() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point(x: i32, pub mut y: i32);
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
			"```wx\nfunc add<T: StackValue>(a: i32, b: i32, extra: T) -> i32\n```"
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
		"```wx\nstruct Point(x: i32, pub mut y: i32)\n```"
	);
	assert_eq!(hover("y:", 0).unwrap(), "```wx\npub mut y: i32\n```");
	assert_eq!(hover("x:", 0).unwrap(), "```wx\nx: i32\n```");
	assert_eq!(hover("i32", 1).unwrap(), "```wx\ntype i32\n```");
	assert_eq!(hover("T:", 0).unwrap(), "```wx\ntype T: StackValue\n```");
	assert_eq!(hover("export", 0), None);
}

#[test]
fn hover_renders_the_other_declaration_kinds() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		memory heap: u32;
		global mut bump: u32 = 4;
		global fixed: u32 = 1;
		enum Color(value: u8) { Red = 0, Green = 1 }
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
		"```wx\nenum Color(value: u8) { .. }\n```"
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
			"impl<Mem: Memory> Layout<Mem>\nfunc size(self: Layout<Mem>) -> <Mem as Memory>::Size",
		),
		(
			"with_extra",
			"impl<Mem: Memory> Layout<Mem>\nfunc with_extra<T: StackValue>(self: Layout<Mem>, extra: T) -> T",
		),
		(
			"make",
			"impl<Mem: Memory> Layout<Mem>\nfunc make(size: <Mem as Memory>::Size) -> Layout<Mem>",
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
		"```wx\ntrait Convert\nfunc convert<U: StackValue>(self: Self, value: U) -> U\n```",
	);
	assert_eq!(
		hover_text(&state, &uri, source, "identity", 0).unwrap(),
		"```wx\ntrait Convert\nfunc identity(self: Self) -> Self\n```",
	);
	for (needle, expected) in [
		(
			"convert",
			"impl<T: StackValue> Convert for Wrapper<T>\nfunc convert<U: StackValue>(self: Wrapper<T>, value: U) -> U",
		),
		(
			"identity",
			"impl<T: StackValue> Convert for Wrapper<T>\nfunc identity(self: Wrapper<T>) -> Wrapper<T>",
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
		enum Color(value: u8) { Red = 0 }
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
		"```wx\nenum Color(value: u8) { .. }\n```"
	);
	assert_eq!(hover("Red", 0).unwrap(), "```wx\nColor::Red = 0\n```");
	let function = hover("twice", 0).unwrap();
	assert!(
		function.starts_with(
			"```wx\nfunc twice<T: StackValue>(value: i32, extra: T)"
		),
		"{function}"
	);
	assert!(function.contains("Doubles."), "{function}");
	assert_eq!(hover("value:", 0).unwrap(), "```wx\nvalue: u8\n```");
	assert_eq!(hover("value:", 1).unwrap(), "```wx\nvalue: i32\n```");
	assert_eq!(hover("T:", 0).unwrap(), "```wx\ntype T: StackValue\n```");
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
	analyze_root(&mut state, &dir, &mut trace());
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
	compute_refresh(&mut state, &file, &mut trace());
	assert_eq!(state.own_root.get(&file), Some(&outer));

	let manifest = inner.join("wx.json");
	state
		.open_documents
		.insert(manifest.clone(), open_document(r#"{"entry":"main.wx"}"#));
	compute_active_refresh(
		&mut state,
		vec![manifest.clone(), manifest.clone()],
		&mut trace(),
	);
	assert_eq!(state.own_root.get(&file), Some(&inner));
	assert!(state.cached.contains_key(&outer));
	assert!(state.cached.contains_key(&inner));

	state.open_documents.remove(&manifest);
	compute_refresh(&mut state, &manifest, &mut trace());
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
	compute_refresh(&mut state, &source_path, &mut trace());
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

	// An invalid `format` section disables formatting, not the project.
	let wide = r#"{"entry":"main.wx","format":{"indent_width":"wide"},"dependencies":{"dep":{"type":"local","path":"dep"}}}"#;
	handle_command(change(wide.into(), 3), &mut state, client).await;
	let sections = &state.projects[&root].manifest;
	assert!(sections.package.is_some() && sections.format.is_none());
	assert!(format(&mut state, client).await.is_none());

	// A failed parse replaces the last valid value.
	handle_command(change("{".into(), 3), &mut state, client).await;
	let sections = &state.projects[&root].manifest;
	assert!(
		sections.package.is_none()
			&& sections.format.is_none()
			&& sections.lint.is_none()
	);
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
	compute_refresh(&mut state, &file, &mut trace());
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
			manifest: Manifest::default(),
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

	compute_refresh(&mut state, &main, &mut trace());
	let publications = compute_refresh(&mut state, &main, &mut trace());

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
		    pub struct Point(pub x: i32, pub mut y: i32);
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
	// modifiers; the label `out` is no token. A `mut` field is marked as a
	// `mut` local is, where it is declared and where it is named.
	assert_eq!(
		tokens,
		[
			"geo:namespace.declaration",
			"Point:struct.declaration",
			"x:property.declaration",
			"i32:type.defaultLibrary",
			"y:property.declaration.modification",
			"i32:type.defaultLibrary",
			"Point:struct",
			"func:keyword",
			"sum:method.declaration",
			"self:keyword",
			"Self:keyword",
			"i32:type.defaultLibrary",
			"self:keyword",
			"x:property",
			"self:keyword",
			"y:property.modification",
			"func:keyword",
			"origin:function.declaration",
			"Self:keyword",
			"Self:keyword",
			"func:keyword",
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
			"func:keyword",
			"id:function.declaration",
			"T:typeParameter.declaration",
			"StackValue:interface",
			"value:parameter.declaration",
			"T:typeParameter",
			"T:typeParameter",
			"value:parameter",
			"func:keyword",
			"main:function.declaration",
			"i32:type.defaultLibrary",
			"total:variable.declaration.modification",
			"i32:type.defaultLibrary",
			"p:variable.declaration",
			"Point:struct",
			"total:variable.modification",
			"p:variable",
			"sum:method",
			"total:variable.modification",
			"id:function",
			"i32:type.defaultLibrary",
			"block:keyword",
			"break:keyword",
			"total:variable.modification",
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
		    local Pair{ left, right } = Pair(1, 2);
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
			"func:keyword",
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
		    local pair = Pair{ left, right: 2 };
		    local Pair{ right, .. } = pair;
		    take{ left } + right
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
	assert!(text.contains("Pair{ left: first, right: 2 }"), "{text}");
	assert!(text.contains("take{ left: first }"), "{text}");

	// The field is the label side of the construction's shorthand.
	let text = rename("left: u32, right", 0, "head").unwrap();
	assert!(text.contains("struct Pair(head: u32"), "{text}");
	assert!(text.contains("Pair{ head: left, right: 2 }"), "{text}");
	assert!(text.contains("take{ left }"), "{text}");

	// The callee's parameter is the label side of the call's shorthand.
	let text = rename("left: u32) -> u32", 0, "value").unwrap();
	assert!(
		text.contains("func take(value: u32) -> u32 { value }"),
		"{text}"
	);
	assert!(text.contains("take{ value: left }"), "{text}");

	// A pattern's shorthand names the field and binds the local.
	let text = rename("right: u32", 0, "tail").unwrap();
	assert!(text.contains("local Pair{ tail: right, .. }"), "{text}");
	assert!(text.contains("+ right"), "{text}");
	let text = rename("right\n}", 0, "rest").unwrap();
	assert!(text.contains("local Pair{ right: rest, .. }"), "{text}");
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
	analyze_root(&mut state, &dir, &mut trace());
	let uri = Uri::from_file_path(&main).unwrap();
	let refusal = renamed(&state, &uri, source, "geo::", 0, "shapes")
		.expect_err("refused");
	assert!(refusal.contains("file of its own"), "{refusal}");
}

// ── Completion ──────────────────────────────────────────────────────────

/// The names completion offers at `$0`, before display punctuation, in
/// client sort order; `None` when it offers nothing there.
fn completions(source: &str) -> Option<Vec<String>> {
	let items = completion_items(source, false)?;
	Some(
		items
			.into_iter()
			.map(|item| item.filter_text.unwrap_or(item.label))
			.collect(),
	)
}

/// The items offered at `$0`, sorted as the client shows them, by a server
/// whose client supports secondary labels and takes snippets or not.
fn completion_items(
	source: &str,
	snippets: bool,
) -> Option<Vec<tower_lsp_server::ls_types::CompletionItem>> {
	let offset = source.find("$0").expect("a `$0` marks the cursor");
	let text = source.replacen("$0", "", 1);
	let root = PathBuf::from("/test/main.wx");
	let (mut state, _) = analyzed(&root, &text);
	state.client.completion = crate::state::CompletionSupport {
		snippets,
		label_details: true,
	};
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
		crate::completion::completion(&mut state, &params)
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
		// A comment, a binding's own name, a literal, a segment after a type.
		"func f() {\n    // hel$0\n}\n",
		"func f() {\n    local na$0me = 1;\n}\n",
		"func f() {\n    local a: u32 = 12$0;\n}\n",
		// A parameter's own name, and an associated type of a type that
		// has none.
		"func f(cou$0nt: u32) {}\n",
		"func f(p: Point::$0) {}\n",
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

const USE_ITEMS: &str = "mod shapes {
    pub struct Square(pub side: u32);
    pub func area() -> u32 { 1 }
    func hidden() {}
    pub mod inner { pub func deep() {} }
    pub enum Kind(value: u8) { A = 0, B }
}
";

/// The labels offered at `$0` in a `use` written after `USE_ITEMS`, sorted.
fn use_completions(source: &str) -> Option<Vec<String>> {
	let mut labels = completions(&format!("{USE_ITEMS}{source}"))?;
	labels.sort();
	Some(labels)
}

#[test]
fn completion_of_a_use_path_starts_in_its_scope_and_the_prelude() {
	let root = ["Bool", "Ordering", "core", "package", "self", "shapes"];
	for source in [
		"use $0;\n",
		"use sha$0;\n",
		"use sha$0::*;\n",
		"use $0\nfunc f() {}\n",
	] {
		assert_eq!(use_completions(source).unwrap(), root, "{source:?}");
	}
	// No enclosing module's names, and `core` is bound in the root only.
	assert_eq!(
		use_completions("mod m {\n    use $0;\n}\n").unwrap(),
		["Bool", "Ordering", "package", "self", "super"]
	);
	assert_eq!(
		use_completions("import \"env\" as env {\n    use $0;\n}\n").unwrap(),
		["Bool", "Ordering", "package", "self", "super"]
	);
}

#[test]
fn completion_of_a_use_path_continues_into_namespaces() {
	assert_eq!(
		use_completions("use shapes::in$0ner::deep;\n").unwrap(),
		["Kind", "inner", "package", "self"]
	);
	assert_eq!(
		use_completions("use shapes::Kind::$0;\n").unwrap(),
		["A", "B"]
	);
}

#[test]
fn completion_of_a_use_leaf_offers_anything_once() {
	// `hidden` is private to `shapes`; `Square` and `area` are in both tiers.
	assert_eq!(
		use_completions("use shapes::$0;\n").unwrap(),
		["Kind", "Square", "area", "inner"]
	);
	assert_eq!(
		use_completions("use shapes::inner::$0;\n").unwrap(),
		["deep"]
	);
	// A group: a gap is a leaf, minus the names the group lists already.
	assert_eq!(
		use_completions("use shapes::{area, $0};\n").unwrap(),
		["Kind", "Square", "inner"]
	);
	assert_eq!(
		use_completions("use shapes::{ar$0, Kind};\n").unwrap(),
		["Square", "area", "inner"]
	);
	assert_eq!(
		use_completions("use shapes::{area, inner::$0};\n").unwrap(),
		["deep"]
	);
	assert_eq!(
		use_completions("use shapes::{area, in$0ner::deep};\n").unwrap(),
		["Kind", "inner", "package", "self"]
	);
}

#[test]
fn completion_of_a_use_offers_nothing_for_an_alias_or_a_glob() {
	for source in [
		"use shapes::area as a$0;\n",
		"use shapes::{area as a$0};\n",
		"use shapes::*$0;\n",
	] {
		assert_eq!(use_completions(source), None, "{source:?}");
	}
}

#[test]
fn completion_of_a_use_inserts_the_name_only() {
	let items =
		completion_items(&format!("{USE_ITEMS}use shapes::ar$0;\n"), true)
			.unwrap();
	let area = items
		.iter()
		.find(|item| item.filter_text.as_deref() == Some("area"))
		.unwrap();
	assert_eq!(area.insert_text.as_deref(), Some("area"));
	assert_ne!(
		area.insert_text_format,
		Some(tower_lsp_server::ls_types::InsertTextFormat::SNIPPET),
		"no call snippet: {area:?}"
	);
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
fn completion_of_a_value_offers_the_namespaces_a_path_starts_with() {
	let source = "mod shapes {\n    pub func area() -> u32 { 1 }\n}\nfunc f() {\n    sha$0\n}\n";
	let items = completion_items(source, true).expect("a value position");
	let shapes = items
		.iter()
		.find(|item| item.label == "shapes")
		.expect("the module is offered");
	assert_eq!(
		shapes.kind,
		Some(tower_lsp_server::ls_types::CompletionItemKind::MODULE)
	);
	assert_eq!(shapes.insert_text, None, "a module is not called");
	let labels: Vec<_> = items.into_iter().map(|item| item.label).collect();
	// The root module has no `super`.
	assert_offers(&labels, &["core", "package", "self"], &["super"]);
	// A local of the module's name does not hide it: a path's prefix is
	// read as a type.
	let shadowed = completions(
		&source.replace("    sha$0", "    local shapes: u32 = 1;\n    sha$0"),
	)
	.unwrap();
	assert_eq!(
		shadowed.iter().filter(|label| *label == "shapes").count(),
		2,
		"{shadowed:?}"
	);
}

#[test]
fn completion_after_a_module_in_a_value_offers_its_modules() {
	let source = "mod a {\n    pub mod b {\n        pub func g() {}\n    }\n    mod hidden {}\n    pub func h() {}\n}\nfunc f() {\n    a::$0\n}\n";
	let labels = completions(source).expect("a segment after a module");
	assert_offers(&labels, &["b", "h"], &["hidden", "f"]);
	let labels = completions(&source.replace("a::$0", "package::$0")).unwrap();
	assert_offers(&labels, &["a", "f"], &[]);
}

#[test]
fn completion_after_an_enum_offers_its_variants() {
	let labels = completions(
		"enum Kind(value: u8) { A = 0, B }\nfunc f(k: Kind) -> u8 {\n    match (k) {\n        Kind::$0 => 1,\n        _ => 2,\n    }\n}\n",
	)
	.expect("a pattern path after an enum");
	assert_eq!(labels, ["A", "B"]);
}

const TYPE_MEMBER_ITEMS: &str = "trait Show: StackValue {
    func show(self: Self) -> u32;
    func make() -> Self;
}
mod shapes {
    pub struct Point(pub x: u32);
    impl Point {
        pub const ZERO: u32 = 0;
        pub func origin() -> Self { Self(0) }
        pub func flip(self: Self) -> Self { self }
        func hidden() {}
    }
}
impl Show for shapes::Point {
    func show(self: Self) -> u32 { 1 }
    func make() -> Self { shapes::Point(0) }
}
";

#[test]
fn completion_after_a_type_offers_its_members() {
	let labels = completions(&format!(
		"{TYPE_MEMBER_ITEMS}func f() {{\n    shapes::Point::$0\n}}\n"
	))
	.expect("a segment after a type");
	assert_offers(
		&labels,
		&["ZERO", "origin", "flip", "show", "make"],
		&["hidden", "x"],
	);
	// Its own impl's private member is visible inside the module.
	let labels = completions(&TYPE_MEMBER_ITEMS.replace(
		"func hidden() {}",
		"func hidden() {}\n        func g() { Point::$0 }",
	))
	.unwrap();
	assert_offers(&labels, &["hidden", "origin"], &[]);
}

#[test]
fn completion_after_self_and_a_type_parameter_offers_their_members() {
	let labels = completions(&TYPE_MEMBER_ITEMS.replace(
		"func hidden() {}",
		"func hidden() {}\n        func g() { Self::$0 }",
	))
	.expect("a segment after `Self`");
	assert_offers(&labels, &["hidden", "origin", "show"], &[]);
	let labels = completions(&format!(
		"{TYPE_MEMBER_ITEMS}func f<T: Show>() -> T {{\n    T::$0\n}}\n"
	))
	.expect("a segment after a type parameter");
	assert_eq!(labels, ["make", "show"]);
}

#[test]
fn completion_after_a_type_inserts_a_methods_self() {
	let items = completion_items(
		&format!("{TYPE_MEMBER_ITEMS}func f() {{\n    shapes::Point::$0\n}}\n"),
		true,
	)
	.unwrap();
	let insert = |name: &str| {
		items
			.iter()
			.find(|item| item.filter_text.as_deref() == Some(name))
			.and_then(|item| item.insert_text.clone())
	};
	assert_eq!(insert("flip").as_deref(), Some("flip($1)"));
	assert_eq!(insert("origin").as_deref(), Some("origin()"));
}

#[test]
fn completion_after_a_generic_type_without_arguments_offers_inherent_members() {
	let labels = completions(&format!(
		"{TYPE_MEMBER_ITEMS}struct Wrap<T>(value: T);\nimpl<T: StackValue> Wrap<T> {{\n    pub func new(value: T) -> Self {{ Self(value) }}\n}}\nimpl<T: StackValue> Show for Wrap<T> {{\n    func show(self: Self) -> u32 {{ 1 }}\n    func make() -> Self {{ Wrap::make() }}\n}}\nfunc f() {{\n    Wrap::$0\n}}\n"
	))
	.expect("a segment after a generic type");
	assert_eq!(labels, ["new"]);
}

#[test]
fn completion_after_an_enum_in_a_value_offers_variants_then_members() {
	let labels = completions(
		"enum Kind(value: u8) { A = 0, B }\nimpl Kind {\n    pub func of(n: u8) -> Self { Kind::A }\n}\nfunc f() {\n    Kind::$0\n}\n",
	)
	.expect("a segment after an enum");
	assert_offers(&labels, &["A", "B", "of"], &[]);
}

#[test]
fn completion_after_a_type_in_a_signature_offers_associated_types() {
	let labels = completions(
		"trait Container {\n    type Item;\n    const SIZE: u32;\n}\nfunc f<C: Container>(item: C::$0) {}\n",
	)
	.expect("a type segment after a type parameter");
	assert_eq!(labels, ["Item"]);
}

const QUALIFIED_ITEMS: &str = "trait Base: StackValue {
    func base() -> u32;
}
trait Tr: Base {
    type Item;
    type Other;
    const SIZE: u32;
    func make() -> Self;
    func show(self: Self) -> u32;
}
memory heap: u32;
";

#[test]
fn completion_after_a_trait_qualified_root_in_a_value_offers_its_values() {
	// The trait's own members only, as its lookup searches: not `Base`'s.
	let labels = completions(&format!(
		"{QUALIFIED_ITEMS}func f<T: Tr>() {{\n    <T as Tr>::$0\n}}\n"
	))
	.expect("a member after a trait-qualified root");
	assert_eq!(labels, ["SIZE", "make", "show"]);
	// A partly written name, and the type before `as` does not choose them.
	let labels = completions(&format!(
		"{QUALIFIED_ITEMS}func f() {{\n    <u32 as Tr>::ma$0\n}}\n"
	))
	.unwrap();
	assert_eq!(labels, ["SIZE", "make", "show"]);
}

#[test]
fn completion_after_a_trait_qualified_root_in_a_type_offers_its_types() {
	let labels = completions(&format!(
		"{QUALIFIED_ITEMS}func f<T: Tr>(item: <T as Tr>::$0) {{}}\n"
	))
	.expect("a type after a trait-qualified root in a signature");
	assert_eq!(labels, ["Item", "Other"]);
	let labels = completions(&format!(
		"{QUALIFIED_ITEMS}func f<T: Tr>() {{\n    local item: <T as Tr>::$0 = 1;\n}}\n"
	))
	.expect("a type after a trait-qualified root in a body");
	assert_eq!(labels, ["Item", "Other"]);
}

#[test]
fn completion_after_a_trait_qualified_root_in_a_length_offers_its_constants() {
	let labels = completions(&format!(
		"{QUALIFIED_ITEMS}func f<T: Tr>(p: heap::&[u8; <T as Tr>::$0]) {{}}\n"
	))
	.expect("a constant after a trait-qualified root in a length");
	assert_eq!(labels, ["SIZE"]);
}

const LENGTH_ITEMS: &str = "memory heap: u32;
const SIZE: u32 = 4;
func helper() -> u32 { 1 }
enum Kind(value: u32) { A = 0, B }
struct Point(x: u32);
impl Point {
    pub const DIM: u32 = 2;
    pub func new() -> Self { Self(0) }
}
mod m {
    pub const INNER: u32 = 1;
    pub func f() {}
}
";

#[test]
fn completion_in_a_length_offers_constants_and_what_leads_to_them() {
	// A constant, and what a path to one starts with; no function or local.
	for source in [
		"func f(p: heap::&[u8; $0]) {}\n",
		"func f(p: heap::&[u8; S$0]) {}\n",
		"func f() {\n    local count = 1;\n    local p: heap::&[u8; $0] = [0; 4];\n}\n",
		"func f() {\n    local count = 1;\n    local p: heap::&[u8; 4] = [0; $0];\n}\n",
	] {
		let labels = completions(&format!("{LENGTH_ITEMS}{source}"))
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(
			&labels,
			&["SIZE", "Kind", "Point", "m"],
			&["helper", "count", "f"],
		);
	}
	// After a module, an enum and a type: their constants alone.
	let after = |prefix: &str| {
		completions(&format!(
			"{LENGTH_ITEMS}func f(p: heap::&[u8; {prefix}::$0]) {{}}\n"
		))
	};
	assert_offers(&after("m").unwrap(), &["INNER"], &["f"]);
	assert_eq!(after("Kind").unwrap(), ["A", "B"]);
	assert_eq!(after("Point").unwrap(), ["DIM"]);
}

#[test]
fn completion_after_a_trait_qualified_root_inserts_a_methods_self() {
	let items = completion_items(
		&format!(
			"{QUALIFIED_ITEMS}func f<T: Tr>() {{\n    <T as Tr>::$0\n}}\n"
		),
		true,
	)
	.unwrap();
	let insert = |name: &str| {
		items
			.iter()
			.find(|item| {
				item.filter_text.as_deref().unwrap_or(&item.label) == name
			})
			.and_then(|item| item.insert_text.clone())
	};
	assert_eq!(insert("show").as_deref(), Some("show($1)"));
	assert_eq!(insert("make").as_deref(), Some("make()"));
}

const PATTERN_ITEMS: &str = "struct Point(x: u32, y: u32, z: u32);
struct Pair(a: u32, b: u32);
enum Signal(pub number: i32) { Off = 0, On }
const LIMIT: u32 = 4;
func helper() -> u32 { 1 }
";

#[test]
fn completion_in_a_struct_pattern_offers_its_fields() {
	// In a destructuring and a match arm, the room after a comma, and a
	// name being written: the fields not written yet.
	for source in [
		"func f(p: Point) {\n    local Point{ x, $0 } = p;\n}\n",
		"func f(p: Point) {\n    local Point{ x, y$0 } = p;\n}\n",
		"func f(p: Point) -> u32 {\n    match (p) {\n        Point{ y$0, x } => 1,\n    }\n}\n",
	] {
		let labels = completions(&format!("{PATTERN_ITEMS}{source}"))
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_eq!(labels, ["y", "z"], "{source:?}");
	}
	// An enum's repr, read as a struct's fields are.
	let labels = completions(&format!(
		"{PATTERN_ITEMS}func f(s: Signal) {{\n    local Signal{{ $0 }} = s;\n}}\n"
	))
	.unwrap();
	assert_eq!(labels, ["number"]);
	// `Self` in an impl for the struct.
	let labels = completions(&format!(
		"{PATTERN_ITEMS}impl Point {{\n    func g(self: Self) {{\n        local Self{{ z, $0 }} = self;\n    }}\n}}\n"
	))
	.unwrap();
	assert_eq!(labels, ["x", "y"]);
}

#[test]
fn completion_in_a_struct_pattern_needs_no_space_before_the_closing_brace() {
	for (pattern, expected) in [
		("Point{$0}", &["x", "y", "z"][..]),
		("Point{ $0 }", &["x", "y", "z"][..]),
		("Point{ $0}", &["x", "y", "z"][..]),
		("Point{x,$0}", &["y", "z"][..]),
		("Point{x,y$0}", &["y", "z"][..]),
	] {
		for source in [
			format!("func f(p: Point) {{ local {pattern} = p; }}"),
			format!("func f(p: Point) {{ match (p) {{ {pattern} => (), }} }}"),
		] {
			let labels = completions(&format!("{PATTERN_ITEMS}{source}"))
				.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
			assert_eq!(labels, expected, "{source:?}");
		}
	}
}

#[test]
fn completion_of_a_match_pattern_prefix_offers_only_the_expected_constructor() {
	for pattern in ["$0", "Poi$0", "Point$0", "Poi$0nt"] {
		for suffix in ["", " => ()"] {
			let source = format!(
				"{PATTERN_ITEMS}func f(p: Point) {{ match (p) {{ {pattern}{suffix} }} }}"
			);
			let labels = completions(&source)
				.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
			assert_offers(
				&labels,
				&["Point", "_"],
				&["Pair", "Signal", "LIMIT", "p", "helper", "f", "transmute"],
			);
		}
	}
}

#[test]
fn completion_of_a_qualified_pattern_includes_constructors_but_not_functions() {
	let declarations = "mod shapes {
		pub struct Point(pub x: u32);
		pub struct Hidden(x: u32);
		pub enum Signal(value: u32) { Off = 0, On }
		pub const LIMIT: u32 = 4;
		pub func make() -> Point { Point(1) }
	}";
	for pattern in ["shapes::$0", "shapes::Poi$0"] {
		let source = format!(
			"{declarations}func f(p: shapes::Point) {{ match (p) {{ {pattern} }} }}"
		);
		let labels = completions(&source).unwrap();
		assert_offers(
			&labels,
			&["Point"],
			&["Signal", "LIMIT", "Hidden", "make", "p"],
		);
	}
	let source = format!(
		"{declarations}func f(p: shapes::Signal) {{ match (p) {{ shapes::Signal::$0 }} }}"
	);
	assert_eq!(completions(&source).unwrap(), ["Off", "On"]);
}

#[test]
fn completion_of_a_pattern_inserts_destructuring_not_a_binding_or_call() {
	for (pattern, inserted) in [
		("Poi$0", "Point{ ${1:..} }"),
		("Poi$0nt", "Point{ ${1:..} }"),
		("Poi$0nt{}", "Point"),
		("Poi$0nt()", "Point"),
		("Poi$0nt // fields\n{}", "Point"),
		("Poi$0nt // elements\n()", "Point"),
	] {
		let source = format!(
			"{PATTERN_ITEMS}func f(p: Point) {{ match (p) {{ {pattern} }} }}"
		);
		let items = completion_items(&source, true).unwrap();
		let point = items
			.iter()
			.find(|item| item.filter_text.as_deref() == Some("Point"))
			.unwrap();
		assert_eq!(point.label, "Point");
		assert_eq!(point.insert_text.as_deref(), Some(inserted), "{source}");
		assert_eq!(
			point.insert_text_format,
			inserted.contains('$').then_some(
				tower_lsp_server::ls_types::InsertTextFormat::SNIPPET
			),
			"{source}"
		);
	}
	let source =
		format!("{PATTERN_ITEMS}func f(p: Point) {{ match (p) {{ Poi$0 }} }}");
	let items = completion_items(&source, false).unwrap();
	let point = items
		.iter()
		.find(|item| item.filter_text.as_deref() == Some("Point"))
		.unwrap();
	assert_eq!(point.insert_text.as_deref(), Some("Point{ .. }"));
	assert!(!items.iter().any(|item| item.label == "LIMIT"));
}

#[test]
fn pattern_completion_handles_arm_gaps_nested_patterns_and_end_of_file() {
	for body in [
		"match (p) { $0 }",
		"match (p) { Point{..} => (), $0 }",
		"match (p) { Point{..} => (), Poi$0 }",
		"match (p) { Point{..} | Poi$0 => (), }",
		"match (p) { Poi$0",
	] {
		let source = format!("{PATTERN_ITEMS}func f(p: Point) {{ {body} }}");
		let labels = completions(&source)
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(&labels, &["Point"], &["p", "helper"]);
	}
	let source =
		format!("{PATTERN_ITEMS}func f(p: Point) {{ match (p) {{ Poi$0");
	assert_offers(&completions(&source).unwrap(), &["Point"], &["p", "helper"]);
	for body in [
		"match (p) { Point{ x: Poi$0, .. } => (), }",
		"match (p) { (Poi$0, _) => (), }",
	] {
		let source = format!("{PATTERN_ITEMS}func f(p: Point) {{ {body} }}");
		assert_eq!(completions(&source).unwrap(), ["_"]);
	}
}

#[test]
fn pattern_constant_completion_labels_show_only_the_entity_name() {
	let source = "func f(b: Bool) { match (b) { $0 } }";
	for snippets in [false, true] {
		let items = completion_items(source, snippets).unwrap();
		for name in ["False", "True"] {
			let item = items
				.iter()
				.find(|item| item.label == name)
				.unwrap_or_else(|| panic!("missing completion label `{name}`"));
			assert_eq!(item.filter_text.as_deref(), Some(name));
			assert_eq!(item.insert_text, Some(format!("Bool::{name}")));
		}
		assert!(!items.iter().any(|item| item.label.starts_with("const ")));
	}
}

#[test]
fn pattern_variants_follow_nested_generic_and_positional_expectations() {
	for (declarations, subject, pattern) in [
		(
			"struct Holder<T>(value: T);",
			"Holder<Bool>",
			"Holder{ value: Tr$0 }",
		),
		(
			"struct Holder<T>(value: T);",
			"Holder<Bool>",
			"Holder::<Bool>{ value: ((Tr$0)) }",
		),
		("struct Pair(a: u32, b: Bool);", "Pair", "Pair(_, Tr$0)"),
		(
			"struct Wrapper(value: (u32, Bool));",
			"Wrapper",
			"Wrapper(_, Tr$0)",
		),
		(
			"struct Three(a: u8, b: u32, c: Bool);",
			"Three",
			"Three(.., Tr$0)",
		),
		("", "(u32, Bool)", "(_, Tr$0)"),
		("", "Bool", "Bool::False | Tr$0"),
	] {
		let source = format!(
			"{declarations}const LIMIT: u32 = 4;
			 func f(value: {subject}) {{ match (value) {{ {pattern} => () }} }}"
		);
		assert_eq!(
			completions(&source).unwrap(),
			["_", "False", "True"],
			"{source}"
		);
		let items = completion_items(&source, false).unwrap();
		assert_eq!(
			items
				.iter()
				.find(|item| item.label == "True")
				.unwrap()
				.insert_text
				.as_deref(),
			Some("Bool::True")
		);
	}
}

#[test]
fn vacant_pattern_slots_use_prospective_positional_types() {
	for (declarations, subject, pattern, expected) in [
		(
			"struct Pair(a: u32, b: Bool);",
			"Pair",
			"Pair($0)",
			vec!["_"],
		),
		(
			"struct Pair(a: u32, b: Bool);",
			"Pair",
			"Pair(first, $0)",
			vec!["_", "False", "True"],
		),
		(
			"struct Wrapper(value: (u32, Bool));",
			"Wrapper",
			"Wrapper(first, $0)",
			vec!["_", "False", "True"],
		),
		(
			"struct Three(a: u8, b: u32, c: Bool);",
			"Three",
			"Three(.., $0)",
			vec!["_", "False", "True"],
		),
	] {
		let source = format!(
			"{declarations}func f(value: {subject}) {{ match (value) {{ {pattern} => () }} }}"
		);
		assert_eq!(completions(&source).unwrap(), expected, "{source}");
	}
}

#[test]
fn enum_representation_context_survives_nested_cursor_descent() {
	// The invalid repr still has a known Bool field type during recovery.
	// That knowledge must not make value tests legal inside its destructure.
	for pattern in ["Flag(((Tr$0)))", "Flag{ value: ((Tr$0)) }", "Flag($0)"] {
		let source = format!(
			"enum Flag(pub value: Bool) {{ Off = 0 }}
			 func f(value: Flag) {{ match (value) {{ {pattern} => () }} }}"
		);
		assert_eq!(completions(&source).unwrap(), ["_"], "{source}");
	}
}

#[test]
fn ordinary_patterns_exclude_constants_and_incompatible_qualifiers() {
	for (subject, pattern) in [
		("Bool", "Point::$0"),
		("Point", "Bool::$0"),
		("Point", "Point::LIM$0"),
	] {
		let source = format!(
			"struct Point(x: u32);
			 impl Point {{ pub const LIMIT: u32 = 1; }}
			 func f(value: {subject}) {{ match (value) {{ {pattern} => () }} }}"
		);
		assert_eq!(completions(&source), None, "{source}");
	}
	for (subject, pattern) in [
		("u32", "Tr$0"),
		("Point", "Unknown{ x: Tr$0 }"),
		("Point", "Other{ x: Tr$0 }"),
		("Holder<Bool>", "Holder::<u32>{ value: Tr$0 }"),
	] {
		let source = format!(
			"struct Point(x: u32); struct Other(x: Bool); struct Holder<T>(value: T);
			 const LIMIT: u32 = 1;
			 func f(value: {subject}) {{ match (value) {{ {pattern} => () }} }}"
		);
		assert_eq!(completions(&source).unwrap(), ["_"], "{source}");
	}
}

#[test]
fn enum_completion_respects_namespaces_and_declaration_order() {
	let declarations = "mod signals {
		pub enum Signal(value: u8) { Zed = 0, Alpha = 1 }
	}";
	for (pattern, inserted) in [
		("signals::$0", "Signal::Alpha"),
		("signals::Signal::$0", "Alpha"),
	] {
		let source = format!(
			"{declarations}func f(value: signals::Signal) {{ match (value) {{ {pattern} => () }} }}"
		);
		assert_eq!(completions(&source).unwrap(), ["Zed", "Alpha"]);
		let items = completion_items(&source, false).unwrap();
		assert_eq!(items[1].insert_text.as_deref(), Some(inserted));
	}
}

#[test]
fn accepting_enum_pattern_completions_checks_without_a_const_marker() {
	for (pattern, replaced) in [("Tr$0", "Tr$0"), ("Bool::Tr$0", "Tr$0")] {
		let source = format!(
			"func f(value: Bool) -> u32 {{
				match (value) {{ {pattern} => 1, _ => 0 }}
			 }}"
		);
		for snippets in [false, true] {
			let items = completion_items(&source, snippets).unwrap();
			let variant =
				items.iter().find(|item| item.label == "True").unwrap();
			let completed =
				source.replace(replaced, variant.insert_text.as_ref().unwrap());
			let (state, dir) =
				analyzed(&PathBuf::from("/test/main.wx"), &completed);
			let snapshot = &state.cached[&dir];
			assert!(
				snapshot.compilation.collect_diagnostics().is_empty(),
				"{completed}"
			);
			assert!(
				snapshot.sema.diagnostics().is_empty(),
				"{completed}: {:?}",
				snapshot.sema.diagnostics()
			);
		}
	}
}

#[test]
fn pattern_completion_preserves_qualified_and_marked_constant_spelling() {
	for (pattern, subject, expected) in [
		("const LIM$0", "Point", "LIMIT"),
		("Signal::O$0", "Signal", "Off"),
		("const Point::LIM$0", "Point", "LIMIT"),
	] {
		let source = format!(
			"{PATTERN_ITEMS}impl Point {{ pub const LIMIT: u32 = 1; }}\
			func f(p: {subject}) {{ match (p) {{ {pattern} }} }}"
		);
		let items = completion_items(&source, true).unwrap();
		let item = items.iter().find(|item| item.label == expected).unwrap();
		assert_eq!(
			item.insert_text.as_deref().unwrap_or(&item.label),
			expected
		);
	}
}

#[test]
fn accepting_a_pattern_constructor_completion_produces_a_valid_pattern() {
	let source = "struct Point(x: u32, y: u32);\nfunc f(p: Point) { match (p) { Poi$0 => (), } }";
	for snippets in [false, true] {
		let items = completion_items(source, snippets).unwrap();
		let point = items
			.iter()
			.find(|item| item.filter_text.as_deref() == Some("Point"))
			.unwrap();
		let inserted =
			point.insert_text.as_ref().unwrap().replace("${1:..}", "..");
		let completed = source.replace("Poi$0", &inserted);
		let (state, dir) =
			analyzed(&PathBuf::from("/test/main.wx"), &completed);
		let snapshot = &state.cached[&dir];
		assert!(
			snapshot.compilation.collect_diagnostics().is_empty(),
			"{completed}"
		);
		assert!(
			snapshot.sema.diagnostics().is_empty(),
			"{completed}: {:?}",
			snapshot.sema.diagnostics()
		);
	}
}

#[test]
fn completion_of_a_match_pattern_does_not_complete_binding_declarations() {
	for source in [
		"func f(p: Point) { local Poi$0 = p; }",
		"func f(p: Point) { match (p) { mut Poi$0 => (), } }",
	] {
		assert_eq!(completions(&format!("{PATTERN_ITEMS}{source}")), None);
	}
}

#[test]
fn completion_in_an_unfinished_match_arm_keeps_its_pattern() {
	for pattern in ["Point{$0}", "Point{x,$0}", "Poi$0nt{}", "Signal::$0"] {
		for suffix in ["", ",", " =>", " =>,"] {
			let subject = if pattern == "Signal::$0" {
				"Signal"
			} else {
				"Point"
			};
			let source = format!(
				"{PATTERN_ITEMS}func f(p: {subject}) {{ match (p) {{ {pattern}{suffix} }} }}"
			);
			let labels = completions(&source)
				.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
			match pattern {
				"Point{$0}" => assert_eq!(labels, ["x", "y", "z"], "{source}"),
				"Point{x,$0}" => assert_eq!(labels, ["y", "z"], "{source}"),
				"Poi$0nt{}" => assert_offers(&labels, &["Point"], &[]),
				"Signal::$0" => assert_eq!(labels, ["Off", "On"], "{source}"),
				_ => unreachable!(),
			}
		}
	}
}

#[test]
fn an_unfinished_match_arm_keeps_completion_at_end_of_file() {
	for suffix in ["", " =>"] {
		let source = format!(
			"{PATTERN_ITEMS}func f(p: Point) {{ match (p) {{ Point{{$0}}{suffix}"
		);
		assert_eq!(completions(&source).unwrap(), ["x", "y", "z"], "{source}");
	}
}

#[test]
fn an_unfinished_match_arm_keeps_definition_and_hover() {
	let root = PathBuf::from("/test/main.wx");
	for suffix in ["", " =>"] {
		let source = format!(
			"struct Point(x: i32, y: i32);\nfunc f(p: Point) {{ match (p) {{ Point{{ x, .. }}{suffix} }} }}"
		);
		let (state, _) = analyzed(&root, &source);
		let uri = Uri::from_file_path(&root).unwrap();
		for (name, declaration) in [("Point{", "Point("), ("x, ..", "x: i32")] {
			let location = scalar(requests::goto_definition(
				&state,
				&definition_params(&uri, position_of(&source, name, 0)),
			));
			assert_eq!(location.uri, uri);
			assert_eq!(
				location.range.start,
				position_of(&source, declaration, 0)
			);
		}
		let hover = hover_text(&state, &uri, &source, "Point{", 0)
			.expect("the retained pattern resolves its constructor");
		assert!(hover.contains("Point"), "{hover}");
	}
}

#[test]
fn completion_in_a_struct_pattern_offers_nothing_the_checker_would_refuse() {
	for source in [
		// After `..`, and outside the braces.
		"func f(p: Point) {\n    local Point{ x, ..$0 } = p;\n}\n",
		"func f(p: Point) {\n    local Point{ x }$0 = p;\n}\n",
		"func f(p: Point) {\n    local Point{}$0 = p;\n}\n",
		"func f(p: Point) {\n    match (p) { Point{}$0 => (), }\n}\n",
	] {
		assert_eq!(
			completions(&format!("{PATTERN_ITEMS}{source}")),
			None,
			"{source:?}"
		);
	}
}

#[test]
fn completion_in_a_fields_pattern_reads_the_pattern_after_its_colon() {
	let labels = completions(&format!(
		"{PATTERN_ITEMS}func f(p: Point) -> u32 {{\n    match (p) {{\n        Point{{ x: const L$0, .. }} => 1,\n        _ => 2,\n    }}\n}}\n"
	))
	.expect("a constant in a field's pattern");
	assert_offers(&labels, &["LIMIT"], &["x", "helper"]);
}

#[test]
fn completion_of_a_constant_pattern_offers_constants() {
	let labels = completions(&format!(
		"{PATTERN_ITEMS}func f(n: u32) -> u32 {{\n    match (n) {{\n        const L$0 => 1,\n        _ => 2,\n    }}\n}}\n"
	))
	.expect("a constant pattern");
	assert_offers(&labels, &["LIMIT", "Signal"], &["helper", "n"]);
	let labels = completions(&format!(
		"{PATTERN_ITEMS}func f(s: Signal) -> u32 {{\n    match (s) {{\n        Signal::$0 => 1,\n        _ => 2,\n    }}\n}}\n"
	))
	.expect("a variant pattern");
	assert_eq!(labels, ["Off", "On"]);
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

const BINDING_ITEMS: &str = "trait Base { type Item; const LEN: const_int; const SIZE: u32; }
trait Container: Base { type Key; const COUNT: const_int; type Value; func get(self: Self); }
trait Other { type Item; }
trait Both: Base + Other { type Own; }
trait Deep: Container { type Extra; }
";

fn binding_completions(source: &str) -> Option<Vec<String>> {
	let mut labels = completions(&format!("{BINDING_ITEMS}{source}\n"))?;
	labels.sort();
	Some(labels)
}

#[test]
fn completion_of_a_where_entry_offers_associated_types_and_constants() {
	for source in [
		"func f<T: Container where { $0 }>() {}",
		"func f<T: Container where {$0}>() {}",
		"func f<T: Container where { Va$0 }>() {}",
		"trait X { type T: Container where { $0 }; }",
		"func f<T: Show + Container where { $0 }>() {}",
	] {
		assert_eq!(
			binding_completions(source).unwrap(),
			["COUNT", "Item", "Key", "LEN", "SIZE", "Value"],
			"{source:?}"
		);
	}
	// An entry with its `=` written is a type's, one marked `const` a
	// constant's.
	assert_eq!(
		binding_completions("func f<T: Container where { Va$0 = u8 }>() {}")
			.unwrap(),
		["Item", "Key", "Value"]
	);
	assert_eq!(
		binding_completions("func f<T: Container where { const L$0 }>() {}")
			.unwrap(),
		["COUNT", "LEN", "SIZE"]
	);
	// The names written already are not offered again.
	assert_eq!(
		binding_completions(
			"func f<T: Container where { Key = u32, const LEN: u8, $0 }>() {}"
		)
		.unwrap(),
		["COUNT", "Item", "SIZE", "Value"]
	);
	assert_eq!(
		binding_completions(
			"func f<T: Container where { Key = u32, It$0, Value = u8 }>() {}"
		)
		.unwrap(),
		["COUNT", "Item", "LEN", "SIZE"]
	);
	// Two supertraits declaring `Item` make it ambiguous, as the checker
	// finds it.
	assert_eq!(
		binding_completions("func f<T: Both where { $0 }>() {}").unwrap(),
		["LEN", "Own", "SIZE"]
	);
	assert_eq!(
		binding_completions("func f<M: Memory where { $0 }>() {}").unwrap(),
		["DATA_END", "PAGE_SIZE", "Repr", "Size"]
	);
	assert_eq!(
		binding_completions("func f<T: Array where { $0 }>() {}").unwrap(),
		["LEN", "Value"]
	);
}

#[test]
fn completion_of_a_where_entry_lists_the_nearest_trait_first() {
	let entries = |source: &str| {
		completion_items(&format!("{BINDING_ITEMS}{source}\n"), false)
			.unwrap()
			.into_iter()
			.map(|item| {
				let from =
					item.label_details.and_then(|details| details.detail);
				(item.label, from)
			})
			.collect::<Vec<_>>()
	};
	let own = |name: &str| (name.to_string(), None);
	let from = |name: &str, from: &str| {
		(name.to_string(), Some(format!("(as {from})")))
	};
	assert_eq!(
		entries("func f<T: Deep where { $0 }>() {}"),
		[
			own("Extra"),
			from("Key", "Container"),
			from("COUNT", "Container"),
			from("Value", "Container"),
			from("Item", "Base"),
			from("LEN", "Base"),
			from("SIZE", "Base"),
		]
	);
	assert_eq!(
		entries("func f<M: Memory where { $0 }>() {}"),
		[
			own("Size"),
			own("DATA_END"),
			own("PAGE_SIZE"),
			from("Repr", "StackValue"),
		]
	);
}

#[test]
fn completion_of_a_where_entry_inserts_a_constants_keyword() {
	let inserted = |source: &str| {
		completion_items(&format!("{BINDING_ITEMS}{source}\n"), true)
			.unwrap()
			.into_iter()
			.map(|item| {
				(
					item.filter_text.unwrap_or(item.label.clone()),
					item.insert_text,
				)
			})
			.collect::<Vec<_>>()
	};
	let name = |name: &str| (name.to_string(), None);
	let constant =
		|name: &str| (name.to_string(), Some(format!("const {name}")));
	for source in [
		"func f<T: Base where { $0 }>() {}",
		"func f<T: Base where { L$0 }>() {}",
	] {
		assert_eq!(
			inserted(source),
			[name("Item"), constant("LEN"), constant("SIZE")]
		);
	}
	for source in [
		"func f<T: Base where { const L$0 }>() {}",
		"func f<T: Base where { const $0 }>() {}",
		"func f<T: Base where { const $0}>() {}",
		"func f<T: Base where { Item = u8, const $0 }>() {}",
		"func f<T: Base where { const $0, Item = u8 }>() {}",
	] {
		assert_eq!(inserted(source), [name("LEN"), name("SIZE")], "{source:?}");
	}
}

#[test]
fn completion_after_a_where_entry_offers_types_or_bounds() {
	let labels =
		binding_completions("func f<T: Container where { Key = $0 }>() {}")
			.unwrap();
	assert_offers(&labels, &["u32", "Bool"], &["Base", "Item", "Key"]);
	let labels =
		binding_completions("func f<T: Container where { Key: $0 }>() {}")
			.unwrap();
	assert_offers(&labels, &["Base", "Add"], &["u32", "Key"]);
	// Outside the braces, nothing of the trait's.
	assert_eq!(
		binding_completions("func f<T: Container where$0 { }>() {}"),
		None
	);
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
trait Tr { func m(self: Self, a: u32); }
impl Tr for W { func m(self: Self, count: u32) {} }
impl W { func own(self: Self, first: u32) {} }
func h(a: u32) {}
";

#[test]
fn completion_of_a_named_argument_offers_the_callees_names() {
	for (source, expected, absent) in [
		// The room in the braces, and a name being written (a shorthand).
		("g{ $0 }", &["alpha", "beta"][..], &["helper"][..]),
		("g{ al$0 }", &["alpha", "beta"], &[]),
		// A name written already is reported if written again.
		("g{ alpha: 1, $0 }", &["beta"], &["alpha"]),
		// A struct's fields.
		("Point{ $0 }", &["x"], &[]),
		// A method's receiver: named through its type, given by the object.
		("W::own{ $0 }", &["self", "first"], &[]),
		("W().own{ $0 }", &["first"], &["self"]),
		// A trait impl's function is named as the impl names it, even where
		// its trait leaves the parameter unnamed.
		("W().m{ $0 }", &["count"], &["self"]),
	] {
		let labels = completions(&format!(
			"{COMPLETION_ITEMS}{NAMED_CALLS}func f() {{\n    {source};\n}}\n"
		))
		.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		assert_offers(&labels, expected, absent);
	}
}

#[test]
fn completion_of_a_named_argument_through_self_offers_the_structs_fields() {
	const PAIR: &str = "struct Pair(first: u32, second: u32);\n";
	for source in [
		"impl Pair { func make() -> Self { Self{ $0 } } }",
		"impl Pair { func make() -> Self { Pair{ $0 } } }",
		"impl Pair { func make() -> Self { Self{ first: 1, $0 } } }",
		"trait Make { func make() -> Self; }\nimpl Make for Pair { func make() -> Self { Self{ $0 } } }",
	] {
		let labels = completions(&format!("{PAIR}{source}\n"))
			.unwrap_or_else(|| panic!("nothing offered in {source:?}"));
		let expected: &[&str] = if source.contains("first: 1") {
			&["second"]
		} else {
			&["first", "second"]
		};
		assert_eq!(labels, expected, "{source:?}");
	}
}

/// A loop's next state by name, written directly as `continue`'s value or
/// as the body's result, offers the parameters of the loop it restarts,
/// with their types.
#[test]
fn completion_of_a_named_state_offers_the_loops_parameters() {
	let source = |site: &str| {
		format!(
			"func f(n: u32) -> u32 {{\n    loop :outer (low: u32 = 0, high = n) {{\n        \
			 if (low == high) {{ break low }};\n        loop (i: u32 = 0) {{\n            \
			 {site}\n        }}\n    }}\n}}\n"
		)
	};
	for (site, expected, absent) in [
		("continue { $0 }", &["i"][..], &["low", "high"][..]),
		("continue :outer { $0 }", &["low", "high"], &["i"]),
		("continue :outer { low: 1, $0 }", &["high"], &["low"]),
	] {
		let labels = completions(&source(site))
			.unwrap_or_else(|| panic!("nothing offered in {site:?}"));
		assert_offers(&labels, expected, absent);
	}
	let items =
		completion_items(&source("continue :outer { $0 }"), false).unwrap();
	let mut details: Vec<_> =
		items.iter().map(|item| item.detail.as_deref()).collect();
	details.sort();
	assert_eq!(details, [Some("high: u32"), Some("low: u32")]);

	// A named list anywhere else, a body's result or one wrapped in
	// parentheses included, gives no loop's state.
	for site in ["local x = ({ $0 });", "({ $0 })", "continue(({ $0 }))"] {
		let labels = completions(&source(site)).unwrap_or_default();
		assert_offers(&labels, &[], &["i", "low", "high"]);
	}
}

/// Names a declaration lists in order are offered in that order, not by
/// name, as the editor sorts by each item's sort text.
#[test]
fn completion_of_names_by_declaration_offers_them_in_declaration_order() {
	const DECLARED: &str = "\
		struct Rect(width: u32, height: u32, area: u32);\n\
		func g(zeta: u32, alpha: u32, mid: u32) {}\n";
	for (site, expected) in [
		("g{ $0 }", &["zeta", "alpha", "mid"][..]),
		("g{ zeta: 1, $0 }", &["alpha", "mid"]),
		("Rect{ $0 }", &["width", "height", "area"]),
		(
			"local Rect{ $0 } = Rect(1, 2, 3);",
			&["width", "height", "area"],
		),
		(
			"loop (zeta: u32 = 0, alpha: u32 = 0) { continue { $0 } }",
			&["zeta", "alpha"],
		),
	] {
		let labels =
			completions(&format!("{DECLARED}func f() {{\n    {site};\n}}\n"))
				.unwrap_or_else(|| panic!("nothing offered in {site:?}"));
		assert_eq!(labels, expected, "{site:?}");
	}
}

/// A name a declaration lists shows its type beside it, as the call
/// instantiates it.
#[test]
fn completion_of_names_by_declaration_shows_their_types_beside_them() {
	let source = "\
		struct Wrap<T>(value: T, count: u32);\n\
		func g(flag: Bool, size: u64) {}\n\
		func f() {\n    g{ $0 };\n    local w: Wrap<i8> = Wrap{ value: 1, count: 2 };\n}\n";
	let descriptions = |source: &str| -> Vec<(String, Option<String>)> {
		completion_items(source, false)
			.unwrap()
			.into_iter()
			.map(|item| {
				let description =
					item.label_details.and_then(|details| details.description);
				(item.label, description)
			})
			.collect()
	};
	assert_eq!(
		descriptions(source),
		[
			("flag".to_owned(), Some("Bool".to_owned())),
			("size".to_owned(), Some("u64".to_owned())),
		]
	);
	let generic = source
		.replacen("g{ $0 }", "g{ flag: True, size: 1 }", 1)
		.replacen("Wrap{ value: 1, count: 2 }", "Wrap{ $0 }", 1);
	assert_eq!(
		descriptions(&generic),
		[
			("value".to_owned(), Some("i8".to_owned())),
			("count".to_owned(), Some("u32".to_owned())),
		]
	);
}

/// A field shows its type on the receiver or on the type a pattern was
/// checked against, the struct's type arguments in place of its
/// parameters.
#[test]
fn completion_of_a_field_shows_its_type_on_the_value() {
	const PAIR: &str = "\
		memory heap: u32;\n\
		struct Pair<T>(first: T, count: u32);\n";
	let typed = |site: &str| -> Vec<(String, Option<String>, Option<String>)> {
		let source = format!(
			"{PAIR}func f(p: Pair<i32>, q: heap::&Pair<u8>) {{\n    {site};\n}}\n"
		);
		completion_items(&source, false)
			.unwrap_or_else(|| panic!("nothing offered in {site:?}"))
			.into_iter()
			.map(|item| {
				let description =
					item.label_details.and_then(|details| details.description);
				(item.label, item.detail, description)
			})
			.collect()
	};
	let expected = |first: &str| {
		vec![
			(
				"first".to_owned(),
				Some(format!("first: {first}")),
				Some(first.to_owned()),
			),
			(
				"count".to_owned(),
				Some("count: u32".to_owned()),
				Some("u32".to_owned()),
			),
		]
	};
	assert_eq!(typed("p.$0"), expected("i32"));
	assert_eq!(typed("q.$0"), expected("u8"));
	assert_eq!(typed("local Pair{ $0 } = p"), expected("i32"));
}

/// A name that holds a value shows its type beside it: a local, a constant,
/// a type's constant. Its detail stays its signature.
#[test]
fn completion_of_a_value_shows_its_type_beside_it() {
	let source = |site: &str| {
		format!(
			"const LIMIT: u32 = 10;\n\
			 global mut bump: u64 = 4;\n\
			 struct S();\n\
			 impl S {{\n    pub const ZERO: i8 = 0;\n}}\n\
			 func f() {{\n    local count: i16 = 1;\n    {site};\n}}\n"
		)
	};
	let beside = |site: &str, label: &str| {
		let items = completion_items(&source(site), false)
			.unwrap_or_else(|| panic!("nothing offered in {site:?}"));
		let item = items
			.into_iter()
			.find(|item| item.label == label)
			.unwrap_or_else(|| panic!("`{label}` not offered in {site:?}"));
		let description =
			item.label_details.and_then(|details| details.description);
		(item.detail, description)
	};
	assert_eq!(
		beside("$0", "count"),
		(Some("local count: i16".to_owned()), Some("i16".to_owned()))
	);
	assert_eq!(
		beside("$0", "LIMIT"),
		(Some("const LIMIT: u32".to_owned()), Some("u32".to_owned()))
	);
	// A global's name is a handle of its own type: it shows its declaration.
	assert_eq!(
		beside("$0", "bump").1,
		Some("global mut bump: u64".to_owned())
	);
	assert_eq!(
		beside("S::$0", "ZERO"),
		(Some("const ZERO: i8".to_owned()), Some("i8".to_owned()))
	);
}

#[test]
fn completion_after_a_named_arguments_colon_offers_values() {
	let labels = completions(&format!(
		"{COMPLETION_ITEMS}{NAMED_CALLS}func f(n: u32) {{\n    g{{ alpha: $0 }};\n}}\n"
	))
	.expect("a value not written yet");
	assert_offers(&labels, &["n", "helper"], &["alpha", "beta"]);
}

#[test]
fn completion_in_a_named_lists_value_offers_values() {
	let labels = completions(&format!(
		"{COMPLETION_ITEMS}func f(n: u32) {{\n    ({{ alpha: $0 }});\n}}\n"
	))
	.expect("a value not written yet");
	assert_offers(&labels, &["n", "helper"], &[]);
}

#[test]
fn completion_offers_no_argument_names_the_checker_would_refuse() {
	for source in [
		// After the list.
		"func f() {\n    g{ alpha: 1, beta: 2 }$0;\n}\n",
		// Braces not closed yet.
		"func f() {\n    g{ $0",
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
			(item.filter_text.unwrap_or(item.label), text)
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
	assert!(items.iter().all(|item| item.insert_text_format.is_none()));
	assert_eq!(
		items
			.iter()
			.find(|item| item.filter_text.as_deref() == Some("helper"))
			.unwrap()
			.insert_text
			.as_deref(),
		Some("helper")
	);
}

#[test]
fn completion_after_a_module_in_a_signature() {
	let labels = completions(
		"mod shapes {\n    pub struct Square();\n    struct Hidden();\n}\nfunc f(s: shapes::$0) {}\n",
	)
	.expect("a segment after a module");
	assert_offers(&labels, &["Square"], &["Hidden"]);
}

const MEMBER_RECEIVERS: &str = "
memory heap: u32;
struct Inner(pub z: u32, pub a: u32);
impl Inner {
    pub func get(self: heap::&Self) -> u32 { self.z }
    pub func set(self: heap::*Self, v: u32) { self.z = v; }
    pub func twice(self: Self) -> u32 { self.z + self.z }
    pub func add(self: Self, v: u32) -> u32 { self.z + v }
    pub func make() -> Inner { Inner(0, 0) }
}
struct Outer(inner: Inner);
";

/// `x.` on a line of its own offers `x`'s members whatever the next line
/// starts with: a path there is not read as part of the access.
#[test]
fn completion_of_a_member_before_a_path_on_the_next_line() {
	let source = "\
		mod host { pub func clear(v: u32) {} }\n\
		struct Point(x: u32, y: u32);\n\
		func f(p: Point) {\n    p.$0\n\n    host::clear(1);\n}\n";
	assert_eq!(completions(source).unwrap(), ["x", "y"]);
}

#[test]
fn completion_of_a_member_keeps_fields_then_methods_in_declaration_order() {
	for (receiver, expected) in [
		("Inner", vec!["z", "a", "twice", "add"]),
		("heap::*Inner", vec!["z", "a", "get", "set"]),
		("heap::&Inner", vec!["z", "a", "get"]),
	] {
		let labels = completions(&format!(
			"{MEMBER_RECEIVERS}func f(i: {receiver}) {{ local a = i.$0 }}"
		))
		.expect("members of a checked receiver");
		assert_eq!(labels, expected, "{receiver}");
	}
}

#[test]
fn completion_of_a_partly_written_member_returns_every_candidate() {
	assert_eq!(
		completions(&format!(
			"{MEMBER_RECEIVERS}func f(p: heap::*Inner) {{ p.ge$0; }}"
		))
		.unwrap(),
		["z", "a", "get", "set"]
	);
}

#[test]
fn completion_of_a_member_reads_place_and_parenthesized_objects() {
	for (params, object) in [
		("o: heap::*Outer", "o.inner"),
		("i: Inner", "(i)"),
		("i: Inner", "(i: Inner)"),
	] {
		assert_eq!(
			completions(&format!(
				"{MEMBER_RECEIVERS}func f({params}) {{ local a = {object}.$0 }}"
			))
			.unwrap(),
			["z", "a", "twice", "add"],
			"{object}"
		);
	}
}

#[test]
fn completion_of_a_member_uses_the_receivers_trait_bounds() {
	assert_eq!(
		completions(
			"trait Show: StackValue { func show(self: Self) -> u32; }
			func f<T: Show>(t: T) { local a = t.$0 }"
		)
		.unwrap(),
		["show"]
	);
}

#[test]
fn completion_before_a_member_on_the_next_line_has_an_empty_prefix() {
	assert_eq!(
		completions(&format!(
			"{MEMBER_RECEIVERS}func f(p: heap::*Inner) {{ p.$0\nfoo(1); }}"
		))
		.unwrap(),
		["z", "a", "get", "set"]
	);
}

#[test]
fn completion_of_a_method_inserts_only_the_arguments_after_self() {
	use tower_lsp_server::ls_types::{CompletionItemKind, InsertTextFormat};

	for (access, snippets, expected, format) in [
		(
			"p.ge$0",
			true,
			Some("get()"),
			Some(InsertTextFormat::SNIPPET),
		),
		("p.ge$0()", true, Some("get"), None),
		(
			"p.se$0",
			true,
			Some("set($1)"),
			Some(InsertTextFormat::SNIPPET),
		),
		("p.se$0(1)", true, Some("set"), None),
		("p.ge$0", false, Some("get"), None),
	] {
		let items = completion_items(
			&format!(
				"{MEMBER_RECEIVERS}func f(p: heap::*Inner) {{ {access}; }}"
			),
			snippets,
		)
		.unwrap();
		assert_eq!(
			items
				.iter()
				.map(|item| item.label.as_str())
				.collect::<Vec<_>>(),
			["z", "a", "get()", "set(…)"]
		);
		for field in &items[..2] {
			assert_eq!(field.kind, Some(CompletionItemKind::FIELD));
			assert_eq!(field.insert_text, None);
			assert_eq!(field.insert_text_format, None);
		}
		let label = if access.starts_with("p.ge") {
			"get"
		} else {
			"set"
		};
		let method = items
			.iter()
			.find(|item| {
				item.filter_text.as_deref().unwrap_or(&item.label) == label
			})
			.unwrap();
		assert_eq!(method.kind, Some(CompletionItemKind::METHOD));
		assert_eq!(method.insert_text.as_deref(), expected, "{access}");
		assert_eq!(method.insert_text_format, format, "{access}");
	}
}

#[test]
fn completion_of_a_member_excludes_private_fields_and_methods() {
	assert_eq!(
		completions(
			"mod m {
			    pub struct S(pub a: u32, b: u32);
			    impl S {
			        pub func get(self: Self) -> u32 { self.a }
			        func hidden(self: Self) -> u32 { self.b }
			    }
			}
			func f(i: m::S) { local a = i.$0 }"
		)
		.unwrap(),
		["a", "get"]
	);
}

#[test]
fn completion_of_a_member_excludes_methods_whose_impl_bounds_fail() {
	let source = |state: &str| {
		format!(
			"struct Open();
			struct Closed();
			pub struct Conn<S>(pub fd: i32);
			trait CanSend {{}}
			impl CanSend for Open {{}}
			impl<S: CanSend> Conn<S> {{ pub func send(self: Self) -> i32 {{ 1 }} }}
			func f(c: Conn<{state}>) {{ local a = c.$0 }}"
		)
	};
	assert_eq!(completions(&source("Open")).unwrap(), ["fd", "send"]);
	assert_eq!(completions(&source("Closed")).unwrap(), ["fd"]);
}

#[test]
fn completion_inside_a_members_object_still_offers_local_names() {
	let labels = completions(&format!(
		"{MEMBER_RECEIVERS}func f(i: Inner) {{ i$0.z; }}"
	))
	.unwrap();
	assert_offers(&labels, &["i"], &["z", "a", "twice", "add", "get", "set"]);
}

#[test]
fn completion_after_a_method_call_offers_the_results_members() {
	for object in [
		"x.trunc()",
		"x.trunc().abs()",
		"x.trunc{}",
		"x.trunc( /* arguments */ )",
		"x.trunc{ /* arguments */ }",
	] {
		let labels = completions(&format!("func f(x: f32) {{ {object}.$0 }}"))
			.expect("members of the call's f32 result");
		assert_offers(&labels, &["trunc", "promote", "to_bits"], &[]);
	}
	assert_eq!(
		completions(&format!(
			"{MEMBER_RECEIVERS}func f() {{ Inner::make().$0 }}"
		))
		.unwrap(),
		["z", "a", "twice", "add"]
	);
}

#[test]
fn completion_after_a_call_of_a_value_uses_its_result() {
	for object in ["g()", "g{}", "cb()", "c()", "consume_unit()"] {
		let labels = completions(&format!(
			"struct Caller();
			impl Call for Caller {{
			    type Args = ();
			    type Result = f32;
			    func call(self: Self, args: ()) -> f32 {{ 1.0 }}
			}}
			func make() -> f32 {{ 1.0 }}
			func consume_unit(args: ()) -> f32 {{ 1.0 }}
			func f(cb: func() -> f32, c: Caller) {{
			    local g = make;
			    {object}.$0
			    local n: u32 = 1;
			}}"
		))
		.unwrap_or_else(|| panic!("no members after {object}"));
		assert_offers(&labels, &["trunc", "promote", "to_bits"], &[]);
	}
}

#[test]
fn completion_after_an_empty_construction_uses_the_struct() {
	for object in ["Empty()", "Empty{}"] {
		assert_eq!(
			completions(&format!(
				"struct Empty();
				impl Empty {{ pub func id(self: Self) -> Self {{ self }} }}
				func f() {{ {object}.$0 }}"
			))
			.unwrap(),
			["id"],
			"{object}"
		);
	}
}

// ── Signature help ──────────────────────────────────────────────────────

/// Signature help at `$0`, with the client's requested label format.
fn signature_help(
	source: &str,
	offsets: bool,
) -> Option<tower_lsp_server::ls_types::SignatureHelp> {
	let offset = source.find("$0").expect("a `$0` marks the cursor");
	let text = source.replacen("$0", "", 1);
	let root = PathBuf::from("/test/main.wx");
	let (mut state, _) = analyzed(&root, &text);
	state.client.signature_label_offsets = offsets;
	let line = text[..offset].matches('\n').count();
	let start = text[..offset].rfind('\n').map_or(0, |at| at + 1);
	let params = tower_lsp_server::ls_types::SignatureHelpParams {
		text_document_position_params: TextDocumentPositionParams {
			text_document: TextDocumentIdentifier {
				uri: Uri::from_file_path(root).unwrap(),
			},
			position: Position {
				line: line as u32,
				character: text[start..offset].encode_utf16().count() as u32,
			},
		},
		work_done_progress_params: Default::default(),
		context: None,
	};
	crate::signature_help::signature_help(&mut state, &params)
}

const SIGNATURE_FUNCTIONS: &str =
	"func pair(first: u32, second: u32) -> u32 { first }\n";

#[test]
fn signature_help_tracks_positional_arguments_and_incomplete_calls() {
	for (call, active) in [
		("pair($0)", Some(0)),
		("pair(1, $0)", Some(1)),
		("pair(1$0)", Some(0)),
		("pair(1, 2$0)", Some(1)),
		("pair(1, 2 $0)", Some(1)),
		("pair(1, 2, $0)", None),
		("pair(   $0", Some(0)),
		("pair(1,   $0", Some(1)),
		("pair(1, $0 }", Some(1)),
		("local values = [pair(1, $0", Some(1)),
	] {
		let help = signature_help(
			&format!("{SIGNATURE_FUNCTIONS}func f() {{ {call}"),
			true,
		)
		.unwrap_or_else(|| panic!("no signature for {call}"));
		assert_eq!(
			help.signatures[0].label,
			"func pair(first: u32, second: u32) -> u32",
			"{call}"
		);
		assert_eq!(help.active_parameter, active, "{call}");
	}
}

#[test]
fn signature_help_tracks_named_arguments_by_name_and_recovers_the_call() {
	for call in [
		"pair{ second: $0 }",
		"pair{ second: $0",
		"pair{ first: 1, second: $0",
		"pair{ second$0 }",
	] {
		let help = signature_help(
			&format!("{SIGNATURE_FUNCTIONS}func f() {{ {call}"),
			true,
		)
		.unwrap_or_else(|| panic!("no signature for {call}"));
		assert_eq!(
			help.signatures[0].label,
			"func pair(first: u32, second: u32) -> u32"
		);
		assert_eq!(help.active_parameter, Some(1), "{call}");
	}
	let help = signature_help(
		&format!("{SIGNATURE_FUNCTIONS}func f() {{ pair{{ $0"),
		true,
	)
	.unwrap();
	assert_eq!(help.active_parameter, None);
}

#[test]
fn signature_help_chooses_the_innermost_call_and_ignores_comment_commas() {
	let source =
		"func outer(a: u32, b: u32) {} func inner(value: u32) -> u32 { value }";
	for (call, label, active) in [
		(
			"outer(inner($0), 2)",
			"func inner(value: u32) -> u32",
			Some(0),
		),
		(
			"outer(inner(1), $0)",
			"func outer(a: u32, b: u32) -> ()",
			Some(1),
		),
		(
			"outer(1, 2 // a comma ,\n $0)",
			"func outer(a: u32, b: u32) -> ()",
			Some(1),
		),
	] {
		let help =
			signature_help(&format!("{source}func f() {{ {call}; }}"), true)
				.unwrap();
		assert_eq!(help.signatures[0].label, label);
		assert_eq!(help.active_parameter, active);
	}
}

#[test]
fn signature_help_omits_only_an_implicit_method_receiver() {
	let source = "struct S(); impl S { pub func get(self: Self, count: u32) -> u32 { count } pub func sin(self: Self) -> f64 { 0.0 } }";
	for (call, expected, active) in [
		("s.get($0)", "func get(count: u32) -> u32", Some(0)),
		("s.sin($0)", "func sin() -> f64", None),
		(
			"S::get(s, $0)",
			"func get(self: S, count: u32) -> u32",
			Some(1),
		),
		("s.get{ count: $0 }", "func get(count: u32) -> u32", Some(0)),
	] {
		let help = signature_help(
			&format!("{source}func f(s: S) {{ {call}; }}"),
			true,
		)
		.unwrap();
		assert_eq!(help.signatures[0].label, expected);
		assert_eq!(help.active_parameter, active);
	}
}

#[test]
fn signature_help_instantiates_types_and_keeps_unknown_generic_names() {
	let source = "func id<T: StackValue>(value: T) -> T { value } struct Point(x: u32, y: u32);";
	for (call, expected) in [
		("id::<u32>($0)", "func id(value: u32) -> u32"),
		("id($0)", "func id(value: ()) -> ()"),
		("Point(1, $0)", "Point(x: u32, y: u32) -> Point"),
	] {
		let help =
			signature_help(&format!("{source}func f() {{ {call}; }}"), true)
				.unwrap();
		assert_eq!(help.signatures[0].label, expected);
	}
}

#[test]
fn signature_help_supports_function_items_references_and_tuple_parameters() {
	for (body, expected, active) in [
		(
			"local g = pair; g(1, $0)",
			"func g(first: u32, second: u32) -> u32",
			Some(1),
		),
		("cb(1, $0)", "func cb(u32, u32) -> u32", Some(1)),
		("one(1, $0)", "func one(args: (u32, u32)) -> u32", Some(0)),
		(
			"pair(p$0)",
			"func pair(first: u32, second: u32) -> u32",
			None,
		),
	] {
		let help = signature_help(&format!("{SIGNATURE_FUNCTIONS}func one(args: (u32, u32)) -> u32 {{ 0 }} func f(cb: func(u32, u32) -> u32, p: (u32, u32)) {{ {body}; }}"), true).unwrap();
		assert_eq!(help.signatures[0].label, expected);
		assert_eq!(help.active_parameter, active, "{body}");
	}
}

#[test]
fn signature_help_offers_nothing_outside_arguments_or_for_unresolved_calls() {
	for body in [
		"pair$0(1, 2);",
		"pair(1, 2)$0;",
		"unknown($0);",
		"// pair($0\n",
		"local text = \"pair($0\";",
	] {
		assert_eq!(
			signature_help(
				&format!("{SIGNATURE_FUNCTIONS}func f() {{ {body} }}"),
				true
			),
			None,
			"{body}"
		);
	}
}

#[test]
fn signature_help_names_parameters_through_impls_and_bounds() {
	let source =
		"trait Get: StackValue { func get(self: Self, count: u32) -> u32; }
	struct S(); impl Get for S { func get(self: Self, count: u32) -> u32 { 0 } }";
	for function in [
		"func f(s: S) { s.get{ count: $0 }; }",
		"func f<T: Get>(s: T) { s.get($0); }",
	] {
		let help =
			signature_help(&format!("{source}{function}"), true).unwrap();
		assert_eq!(help.signatures[0].label, "func get(count: u32) -> u32");
		assert_eq!(help.active_parameter, Some(0));
	}
}

#[test]
fn signature_help_reads_custom_call_signatures_and_generic_constructors() {
	let source = "struct C(); impl Call for C {
	    type Args = (u32, u32); type Result = u32;
	    func call(self: Self, args: (u32, u32)) -> u32 { 0 }
	}
	struct Point<T: StackValue>(x: T, y: T);
	func pick<T: StackValue>(a: T, b: T) -> T { a }";
	for (call, label) in [
		("c(1, $0)", "func c(args: (u32, u32)) -> u32"),
		("Point::<u32>($0)", "Point(x: u32, y: u32) -> Point<u32>"),
		("Point($0)", "Point(x: T, y: T) -> Point<T>"),
		("pick($0)", "func pick(a: T, b: T) -> T"),
	] {
		let help = signature_help(
			&format!("{source}func f(c: C) {{ {call}; }}"),
			true,
		)
		.unwrap();
		assert_eq!(help.signatures[0].label, label, "{call}");
	}
}

#[test]
fn signature_help_renders_parameter_labels_and_documentation() {
	use tower_lsp_server::ls_types::{Documentation, ParameterLabel};

	let source = "/// Reads a value.\nfunc read(alpha: u32, beta: u32) {}\nfunc f() { local text: [u8; 4] = \"😀\"; read(1, $0); }";
	for offsets in [true, false] {
		let help = signature_help(source, offsets).unwrap();
		let signature = &help.signatures[0];
		assert_eq!(signature.label, "func read(alpha: u32, beta: u32) -> ()");
		assert_eq!(signature.active_parameter, Some(1));
		let parameters = signature.parameters.as_ref().unwrap();
		if offsets {
			assert_eq!(
				parameters[0].label,
				ParameterLabel::LabelOffsets([10, 20])
			);
			assert_eq!(
				parameters[1].label,
				ParameterLabel::LabelOffsets([22, 31])
			);
		} else {
			assert_eq!(
				parameters[0].label,
				ParameterLabel::Simple("alpha: u32".into())
			);
			assert_eq!(
				parameters[1].label,
				ParameterLabel::Simple("beta: u32".into())
			);
		}
		let Some(Documentation::MarkupContent(doc)) = &signature.documentation
		else {
			panic!("missing documentation");
		};
		assert_eq!(doc.value, "Reads a value.");
	}
}

#[test]
fn completion_labels_name_the_trait_that_supplies_a_method() {
	let source = "trait Named: StackValue { func named(self: Self) -> u32; }
	trait Defaulted: StackValue { func defaulted(self: Self) -> u32 { 0 } }
	struct S(pub field: u32);
	impl S { pub func inherent(self: Self) -> u32 { self.field } }
	impl Named for S { func named(self: Self) -> u32 { self.field } }
	impl Defaulted for S {}
	func f(s: S) { s.$0 }";
	let items = completion_items(source, true).unwrap();
	assert_eq!(
		items
			.iter()
			.skip(1)
			.map(|item| item.detail.as_deref())
			.collect::<Vec<_>>(),
		[
			Some("func inherent(self: S) -> u32"),
			Some("func named(self: S) -> u32"),
			Some("func defaulted(self: Self) -> u32"),
		]
	);
	assert_eq!(
		items
			.iter()
			.skip(1)
			.map(|item| item
				.label_details
				.as_ref()
				.and_then(|details| details.description.as_deref()))
			.collect::<Vec<_>>(),
		[
			Some("func inherent(self: S) -> u32"),
			Some("func named(self: S) -> u32"),
			Some("func defaulted(self: Self) -> u32"),
		]
	);
	let labels: Vec<_> = items
		.iter()
		.map(|item| {
			(
				item.label.as_str(),
				item.label_details
					.as_ref()
					.and_then(|details| details.detail.as_deref()),
				item.insert_text.as_deref(),
			)
		})
		.collect();
	assert_eq!(
		labels,
		[
			("field", None, None),
			("inherent()", None, Some("inherent()")),
			("named()", Some("(as Named)"), Some("named()")),
			("defaulted()", Some("(as Defaulted)"), Some("defaulted()")),
		]
	);
}

#[test]
fn completion_labels_name_a_methods_declaring_supertrait() {
	let items = completion_items(
		"trait Named: StackValue { func named(self: Self) -> u32; }
		trait Sub: Named {}
		func f<T: Sub>(s: T) { s.$0 }",
		false,
	)
	.unwrap();
	assert_eq!(items.len(), 1);
	assert_eq!(items[0].label, "named()");
	assert_eq!(
		items[0].label_details.as_ref().unwrap().detail.as_deref(),
		Some("(as Named)")
	);
	assert_eq!(items[0].insert_text.as_deref(), Some("named"));
}

#[test]
fn completion_omits_secondary_labels_for_clients_without_support() {
	let root = PathBuf::from("/test/main.wx");
	let source = "trait Named: StackValue { func named(self: Self) -> u32; }
	func f<T: Named>(s: T) { s. }";
	let (mut state, _) = analyzed(&root, source);
	let mut position = position_of(source, "s.", 0);
	position.character += 2;
	let params = tower_lsp_server::ls_types::CompletionParams {
		text_document_position: TextDocumentPositionParams {
			text_document: TextDocumentIdentifier {
				uri: Uri::from_file_path(root).unwrap(),
			},
			position,
		},
		work_done_progress_params: Default::default(),
		partial_result_params: Default::default(),
		context: None,
	};
	let Some(tower_lsp_server::ls_types::CompletionResponse::Array(items)) =
		crate::completion::completion(&mut state, &params)
	else {
		panic!("a member site");
	};
	assert_eq!(items.len(), 1);
	assert_eq!(items[0].label, "named()");
	assert_eq!(items[0].label_details, None);
}

#[test]
fn completion_documentation_renders_item_doc_comments_as_markdown() {
	use tower_lsp_server::ls_types::{
		Documentation, MarkupContent, MarkupKind,
	};

	let items = completion_items(
		"/// Computes **a value** using `x`.
		///
		/// More details.
		func documented(x: u32) -> u32 { x }
		func plain() {}
		func f() { $0 }",
		false,
	)
	.unwrap();
	let documented = items
		.iter()
		.find(|item| item.filter_text.as_deref() == Some("documented"))
		.unwrap();
	assert_eq!(
		documented.detail.as_deref(),
		Some("func documented(x: u32) -> u32")
	);
	assert_eq!(
		documented.documentation,
		Some(Documentation::MarkupContent(MarkupContent {
			kind: MarkupKind::Markdown,
			value: "Computes **a value** using `x`.\n\nMore details.".into(),
		}))
	);
	assert_eq!(
		items
			.iter()
			.find(|item| item.filter_text.as_deref() == Some("plain"))
			.unwrap()
			.documentation,
		None
	);
}

#[test]
fn completion_documentation_uses_the_selected_methods_declaration() {
	use tower_lsp_server::ls_types::{
		Documentation, MarkupContent, MarkupKind,
	};

	let items = completion_items(
		"trait Tr: StackValue {
		    func get(self: Self) -> u32;
		    /// The default method.
		    func defaulted(self: Self) -> u32 { 0 }
		}
		/// Documentation for the struct.
		struct S(pub field: u32);
		impl S { pub func plain(self: Self) {} }
		impl Tr for S {
		    /// Reads **this** value.
		    ///
		    /// Returned in `u32`.
		    func get(self: Self) -> u32 { self.field }
		}
		func f(s: S) { s.$0 }",
		true,
	)
	.unwrap();
	for (label, expected) in [
		("field", None),
		("plain", None),
		("get", Some("Reads **this** value.\n\nReturned in `u32`.")),
		("defaulted", Some("The default method.")),
	] {
		let item = items
			.iter()
			.find(|item| {
				item.filter_text.as_deref().unwrap_or(&item.label) == label
			})
			.unwrap();
		assert_eq!(
			item.documentation,
			expected.map(|value| Documentation::MarkupContent(MarkupContent {
				kind: MarkupKind::Markdown,
				value: value.into(),
			})),
			"{label}"
		);
	}
}

#[test]
fn completion_documentation_does_not_use_a_functions_docs_for_its_parameters() {
	for (source, label) in [
		(
			"/// The function.\nfunc f(parameter: u32) { $0 }",
			"parameter",
		),
		(
			"/// The function.\nfunc f(parameter: u32) {}\nfunc g() { f{ $0 }; }",
			"parameter",
		),
	] {
		let items = completion_items(source, false).unwrap();
		assert_eq!(
			items
				.iter()
				.find(|item| item.filter_text.as_deref().unwrap_or(&item.label)
					== label)
				.unwrap()
				.documentation,
			None
		);
	}
}

#[test]
fn completion_displays_call_punctuation_and_compact_signatures() {
	for (access, snippets, get_insert, set_insert) in [
		("p.$0", true, Some("get()"), Some("set($1)")),
		("p.$0", false, Some("get"), Some("set")),
		("p.ge$0()", true, Some("get"), Some("set")),
	] {
		let items = completion_items(
			&format!(
				"{MEMBER_RECEIVERS}func f(p: heap::*Inner) {{ {access}; }}"
			),
			snippets,
		)
		.unwrap();
		assert_eq!(
			items
				.iter()
				.map(|item| item.label.as_str())
				.collect::<Vec<_>>(),
			["z", "a", "get()", "set(…)"]
		);
		// A field shows its type beside it, as a call shows its signature.
		for field in &items[..2] {
			assert_eq!(
				field
					.label_details
					.as_ref()
					.and_then(|details| details.description.as_deref()),
				Some("u32")
			);
		}
		for (label, punctuation, description, inserted) in [
			(
				"get",
				"()",
				"func get(self: heap::&Inner) -> u32",
				get_insert,
			),
			(
				"set",
				"(…)",
				"func set(self: heap::*Inner, u32) -> ()",
				set_insert,
			),
		] {
			let item = items
				.iter()
				.find(|item| {
					item.filter_text.as_deref().unwrap_or(&item.label) == label
				})
				.unwrap();
			let details = item.label_details.as_ref().unwrap();
			assert_eq!(item.label, format!("{label}{punctuation}"));
			assert_eq!(item.filter_text.as_deref(), Some(label));
			assert_eq!(details.detail, None);
			assert_eq!(details.description.as_deref(), Some(description));
			assert_eq!(item.insert_text.as_deref(), inserted);
		}
	}
}

/// A function's, a constructor's, a memory's or a global's type is its
/// own, so beside its name is its declaration, not a type: its type
/// parameters by name, its parameters by type.
#[test]
fn completion_shows_a_declaration_beside_its_name() {
	let items = completion_items(
		"memory heap: u32;\n\
		 global fixed: u8 = 1;\n\
		 struct Box<T>(value: T);\n\
		 func id<T: StackValue>(value: T) -> T { value }\n\
		 func f() { $0 }",
		false,
	)
	.unwrap();
	let beside = |name: &str| {
		items
			.iter()
			.find(|item| {
				item.filter_text.as_deref().unwrap_or(&item.label) == name
			})
			.unwrap_or_else(|| panic!("`{name}` not offered"))
			.label_details
			.as_ref()
			.and_then(|details| details.description.clone())
	};
	assert_eq!(beside("heap").as_deref(), Some("memory heap: u32"));
	assert_eq!(beside("fixed").as_deref(), Some("global fixed: u8"));
	assert_eq!(beside("Box").as_deref(), Some("struct Box<T>(T)"));
	assert_eq!(beside("id").as_deref(), Some("func id<T>(T) -> T"));
}

#[test]
fn completion_displays_call_punctuation_for_functions_and_constructors() {
	let items = completion_items("func zero() {} func one(value: u32) -> u32 { value } struct Empty(); struct Pair(a: u32, b: u32); func f() { $0 }", false).unwrap();
	for (label, punctuation, description) in [
		("zero", "()", "func zero() -> ()"),
		("one", "(…)", "func one(u32) -> u32"),
		("Empty", "()", "struct Empty()"),
		("Pair", "(…)", "struct Pair(u32, u32)"),
	] {
		let item = items
			.iter()
			.find(|item| {
				item.filter_text.as_deref().unwrap_or(&item.label) == label
			})
			.unwrap();
		let details = item.label_details.as_ref().unwrap();
		assert_eq!(item.label, format!("{label}{punctuation}"));
		assert_eq!(item.filter_text.as_deref(), Some(label));
		assert_eq!(details.detail, None);
		assert_eq!(details.description.as_deref(), Some(description));
		assert_eq!(item.insert_text.as_deref(), Some(label));
		assert_eq!(item.insert_text_format, None);
	}
}

#[test]
fn named_argument_completion_instantiates_a_methods_self_type() {
	for call in ["x.add{ $0 }", "x.add{ rh$0 }", "x.add{ rhs$0: 0.0 }"] {
		let items =
			completion_items(&format!("func f(x: f64) {{ {call}; }}"), false)
				.unwrap();
		assert_eq!(
			items
				.iter()
				.map(|item| item.label.as_str())
				.collect::<Vec<_>>(),
			["rhs"]
		);
		assert_eq!(items[0].detail.as_deref(), Some("rhs: f64"), "{call}");
	}
}

#[test]
fn named_argument_completion_uses_inferred_and_explicit_generic_arguments() {
	let declarations = "func choose<T: StackValue>(first: T, second: T) -> T { first }\nstruct Pair<T: StackValue>(first: T, second: T);";
	for (function, expected) in [
		(
			"func f(x: f64) { choose{ first: x, $0 }; }",
			vec![("second", "second: f64")],
		),
		(
			"func f() { choose::<u32>{ $0 }; }",
			vec![("first", "first: u32"), ("second", "second: u32")],
		),
		(
			"func f() { choose{ $0 }; }",
			vec![("first", "first: T"), ("second", "second: T")],
		),
		(
			"func f<T: StackValue>(x: T) { choose{ first: x, $0 }; }",
			vec![("second", "second: T")],
		),
		(
			"func f(x: u32) { Pair{ first: x, $0 }; }",
			vec![("second", "second: u32")],
		),
	] {
		let items =
			completion_items(&format!("{declarations}{function}"), false)
				.unwrap();
		assert_eq!(
			items
				.iter()
				.map(|item| (
					item.label.as_str(),
					item.detail.as_deref().unwrap()
				))
				.collect::<Vec<_>>(),
			expected,
			"{function}"
		);
	}
}

#[test]
fn named_argument_completion_normalizes_associated_types_when_known() {
	let declarations = "trait Has: StackValue {
	    type Item: StackValue;
	    func put(self: Self, value: Self::Item) {}
	}
	struct S(); impl Has for S { type Item = u32; }";
	for (function, expected) in [
		("func f(s: S) { s.put{ $0 }; }", "value: u32"),
		(
			"func f<T: Has>(s: T) { s.put{ $0 }; }",
			"value: <T as Has>::Item",
		),
	] {
		let items =
			completion_items(&format!("{declarations}{function}"), false)
				.unwrap();
		assert_eq!(items.len(), 1);
		assert_eq!(items[0].label, "value");
		assert_eq!(items[0].detail.as_deref(), Some(expected), "{function}");
	}
}

#[test]
fn named_argument_completion_uses_the_impls_parameter_names() {
	let declarations =
		"trait Tr: StackValue { func take(self: Self, a: Self); }
	struct S(); impl Tr for S { func take(self: Self, rhs: Self) {} }";
	for (call, expected) in [
		("s.take{ $0 }", vec![("rhs", "rhs: S")]),
		(
			"S::take{ $0 }",
			vec![("self", "self: S"), ("rhs", "rhs: S")],
		),
	] {
		let items = completion_items(
			&format!("{declarations}func f(s: S) {{ {call}; }}"),
			false,
		)
		.unwrap();
		assert_eq!(
			items
				.iter()
				.map(|item| (
					item.label.as_str(),
					item.detail.as_deref().unwrap()
				))
				.collect::<Vec<_>>(),
			expected,
			"{call}"
		);
	}
}

#[test]
fn named_argument_completion_keeps_declaration_types_without_a_checked_call() {
	let items = completion_items(
		"memory heap: u32;
		trait Tr: StackValue { func take(self: Self, rhs: Self); }
		func f<T: Tr>(p: heap::&T) { p.take{ $0 }; }",
		false,
	)
	.unwrap();
	assert_eq!(items.len(), 1);
	assert_eq!(items[0].label, "rhs");
	assert_eq!(items[0].detail.as_deref(), Some("rhs: Self"));
}

#[test]
fn hover_shows_the_bounds_written_on_a_type() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		trait Show {}
		trait Container: StackValue {
		    type Item: Show + StackValue;
		    type Key = u32;
		    type Value: StackValue where { Repr: StackScalar };
		    func get(self: Self) -> Self;
		}
		struct Box(value: u32);
		impl Container for Box {
		    type Item = Box;
		    type Value = u32;
		    func get(self: Self) -> Self { self }
		}
		typeset Small: Add { u8, u16 }
		func f<M: Memory where { Size = u32 }, T: Container where { Value: Show }>(m: M) {}
	"};
	let (state, _) = analyzed(&root, source);
	let uri = Uri::from_file_path(&root).unwrap();
	let hover = |needle, occurrence| {
		hover_text(&state, &uri, source, needle, occurrence).unwrap()
	};
	for (needle, occurrence, expected) in [
		// An associated type's declaration, with its default, and nested
		// bindings, under its trait; an impl's value has no bounds of its
		// own and is under its impl.
		("Item", 0, "trait Container\ntype Item: Show + StackValue"),
		("Key", 0, "trait Container\ntype Key = u32"),
		(
			"Value:",
			0,
			"trait Container\ntype Value: StackValue where { Repr: StackScalar }",
		),
		("Item", 1, "impl Container for Box\ntype Item = Box"),
		// What a trait or typeset writes, not what it implies; a trait's
		// own `Self` is the trait.
		("Container", 0, "trait Container: StackValue"),
		("Self", 0, "type Self: Container"),
		("Small", 0, "typeset Small: Add { u8, u16 }"),
		// Type parameters, alone and in their declaration's signature.
		("M:", 0, "type M: Memory where { Size = u32 }"),
		("T:", 0, "type T: Container where { Value: Show }"),
		(
			"f<",
			0,
			"func f<M: Memory where { Size = u32 }, T: Container where { Value: Show }>(m: M) -> ()",
		),
	] {
		assert_eq!(
			hover(needle, occurrence),
			format!("```wx\n{expected}\n```"),
			"{needle}, occurrence {occurrence}"
		);
	}
}

const KEYS_APP: &str = "/keys/app/main.wx";
const KEYS_LIB: &str = "/keys/lib/main.wx";

/// A server that has checked `text` as `KEYS_APP`, whose manifest declares
/// `lib` and `"odd\key"`, both the package at `KEYS_LIB`.
fn package_keys_state(text: &str) -> ServerState {
	let app = PathBuf::from(KEYS_APP);
	let lib = PathBuf::from(KEYS_LIB);
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(app.clone(), open_document(text));
	state
		.open_documents
		.insert(lib.clone(), open_document("pub func run() {}"));
	state.open_documents.insert(
		app.parent().unwrap().join("wx.json"),
		open_document(
			r#"{"entry":"main.wx","dependencies":{
				"lib":{"type":"local","path":"../lib"},
				"odd\"key":{"type":"local","path":"../lib"}}}"#,
		),
	);
	state.open_documents.insert(
		lib.parent().unwrap().join("wx.json"),
		open_document(r#"{"entry":"main.wx"}"#),
	);
	compute_refresh(&mut state, &app, &mut trace());
	state
}

/// The items offered at `$0` in `KEYS_APP` (`package_keys_state`).
fn package_key_items(
	source: &str,
) -> Option<Vec<tower_lsp_server::ls_types::CompletionItem>> {
	let offset = source.find("$0").expect("a `$0` marks the cursor");
	let text = source.replacen("$0", "", 1);
	let app = PathBuf::from(KEYS_APP);
	let mut state = package_keys_state(&text);
	let line = text[..offset].matches('\n').count();
	let line_start = text[..offset].rfind('\n').map_or(0, |at| at + 1);
	let params = tower_lsp_server::ls_types::CompletionParams {
		text_document_position: TextDocumentPositionParams {
			text_document: TextDocumentIdentifier {
				uri: Uri::from_file_path(&app).unwrap(),
			},
			position: Position {
				line: line as u32,
				character: (offset - line_start) as u32,
			},
		},
		work_done_progress_params: Default::default(),
		partial_result_params: Default::default(),
		context: None,
	};
	match crate::completion::completion(&mut state, &params)? {
		tower_lsp_server::ls_types::CompletionResponse::Array(items) => {
			Some(items)
		}
		_ => None,
	}
}

/// Each item's label and the text its edit writes over `range`.
fn package_key_edits(
	items: &[tower_lsp_server::ls_types::CompletionItem],
) -> Vec<(&str, Range, &str)> {
	items
		.iter()
		.map(|item| {
			let Some(tower_lsp_server::ls_types::CompletionTextEdit::Edit(
				edit,
			)) = &item.text_edit
			else {
				panic!("`{}` has no text edit", item.label);
			};
			(item.label.as_str(), edit.range, edit.new_text.as_str())
		})
		.collect()
}

#[test]
fn completion_of_a_package_key_offers_the_manifests_dependencies() {
	let span = |start, end| Range {
		start: Position::new(0, start),
		end: Position::new(0, end),
	};
	// Between empty quotes; the core is not offered.
	let items = package_key_items("package \"$0\" as lib;\n").unwrap();
	assert_eq!(
		package_key_edits(&items),
		[
			("lib", span(9, 9), "lib"),
			("odd\"key", span(9, 9), "odd\\\"key")
		]
	);
	// Inside a written key, all of it is replaced.
	let items = package_key_items("package \"l$0i\" as lib;\n").unwrap();
	assert_eq!(package_key_edits(&items)[0], ("lib", span(9, 11), "lib"));
	// An open literal is closed, and nothing after the cursor is replaced.
	let items = package_key_items("package \"l$0").unwrap();
	assert_eq!(package_key_edits(&items)[0], ("lib", span(9, 10), "lib\""));
	// Before the opening quote and after the closing one is not the key.
	assert!(package_key_items("package $0\"lib\" as lib;\n").is_none());
	assert!(package_key_items("package \"lib\"$0 as lib;\n").is_none());
	// Nor is another string literal.
	assert!(
		package_key_items("import \"$0env\" as env { func f(); }\n").is_none()
	);
}

#[test]
fn goto_definition_on_a_package_key_opens_the_packages_entry_file() {
	let source = "package \"lib\" as lib;\nfunc main() { lib::run(); }\n";
	let state = package_keys_state(source);
	let app = Uri::from_file_path(KEYS_APP).unwrap();
	let definition = |needle, occurrence| match requests::goto_definition(
		&state,
		&definition_params(&app, position_of(source, needle, occurrence)),
	) {
		Some(GotoDefinitionResponse::Scalar(location)) => location,
		other => panic!("{needle}: {other:?}"),
	};
	// On the key, from either quote, into the package.
	for needle in ["\"lib\"", "lib\" as"] {
		let location = definition(needle, 0);
		assert_eq!(location.uri, Uri::from_file_path(KEYS_LIB).unwrap());
		assert_eq!(location.range, Range::default());
	}
	// The alias, written or used, is the instance's own name.
	for needle in ["lib;", "lib::"] {
		let location = definition(needle, 0);
		assert_eq!(location.uri, app);
		assert_eq!(location.range.start, position_of(source, "lib;", 0));
	}
}

#[test]
fn hover_on_a_package_key_shows_where_its_package_is() {
	let source = "package \"lib\" as lib;\nfunc main() { lib::run(); }\n";
	let state = package_keys_state(source);
	let app = Uri::from_file_path(KEYS_APP).unwrap();
	assert_eq!(
		hover_text(&state, &app, source, "lib\"", 0),
		Some(format!("```wx\npackage\n```\n\n---\n\n`{KEYS_LIB}`"))
	);
	// The alias is the instance.
	for needle in ["lib;", "lib::"] {
		assert_eq!(
			hover_text(&state, &app, source, needle, 0).as_deref(),
			Some("```wx\npackage \"lib\" as lib\n```"),
			"{needle}"
		);
	}
}

#[test]
fn semantic_tokens_leave_a_package_key_a_string() {
	let source = "package \"lib\" as lib;\nfunc main() { lib::run(); }\n";
	let state = package_keys_state(source);
	let app = Uri::from_file_path(KEYS_APP).unwrap();
	let tokens = semantic_tokens(&state, &app, source, None);
	assert!(
		!tokens.iter().any(|token| token.starts_with('"')),
		"{tokens:?}"
	);
	assert!(tokens.contains(&"lib:namespace.declaration".to_owned()));
}

/// Only a written `block` or loop is a jump target, so nothing claims a
/// keyword that is not written: not braces the parser read without their
/// `block` (here, after an unfinished `local`), nor an `if` read without the
/// label it cannot take.
#[test]
fn semantic_tokens_survive_recovered_blocks_and_labels() {
	for source in [
		indoc::indoc! {"
			func f(n: i32) -> i32 {
			    local

			    loop (a: i32 = 0, k = n) {
			        if (k == 1) { break a };
			        (a + 1, k - 1)
			    }
			}
		"},
		indoc::indoc! {"
			func f(c: Bool) -> u8 {
			    if :l (c) { 1 } else { 2 }
			}
		"},
	] {
		let root = PathBuf::from("/test/main.wx");
		let (state, _) = analyzed(&root, source);
		let uri = Uri::from_file_path(&root).unwrap();
		let tokens = semantic_tokens(&state, &uri, source, None);
		assert!(
			!tokens.iter().any(|token| token.starts_with('{')),
			"{tokens:?}"
		);
	}
}

#[test]
fn a_local_destructuring_path_offers_constructors_and_no_tests() {
	for (body, constructor) in [
		("func f(p: Point) { local Poi$0(..) = p; }", "Point"),
		("func f(s: Signal) { local Sig$0(..) = s; }", "Signal"),
	] {
		let source = format!("{PATTERN_ITEMS}{body}");
		let items = completion_items(&source, false).unwrap();
		for item in &items {
			let text = item.insert_text.as_deref().unwrap_or(&item.label);
			assert!(!text.starts_with("const "), "{text:?}");
		}
		assert_offers(
			&completions(&source).unwrap(),
			&[constructor],
			&["LIMIT", "On", "Off"],
		);
	}
}
