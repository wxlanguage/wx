use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::str::FromStr;

use tower_lsp_server::ls_types::{
	Diagnostic, DiagnosticSeverity, NumberOrString, Position, Range, Uri,
};
use wx_compiler::vfs::FileId;

use crate::completion::{completion_items, find_enclosing_function};
use crate::symbol_index::SymbolKind;
use crate::{
	Backend, CompiledRoot, OpenDocument, ServerState, analyze_root,
	build_service, compute_refresh, diagnostic_publish_paths,
	discover_crate_root, find_active_call, implementation_locations,
	owning_root, reference_search_kinds, symbol_kind_to_token_type,
};
use tower_lsp_server::LanguageServer as _;
use wx_compiler::tir::TypeParamOwner;

/// Exercises `Backend` through its real `LanguageServer` trait methods
/// (rather than the `ServerState` free functions the other tests in this
/// file use), which is the only way to touch the actor/channel plumbing in
/// `run_actor`/`Command` that replaced the old `Arc<Mutex<ServerState>>`.
/// Asserts two things that plumbing must get right: a `hover` query queued
/// after a `did_change` observes that edit's text (not a stale one racing
/// ahead of it — the ordering bug this actor design closes), and it
/// completes promptly rather than deadlocking.
#[tokio::test]
async fn hover_after_did_change_observes_latest_edit_through_backend() {
	use std::time::Instant;
	use tower_lsp_server::ls_types::*;

	let (service, socket) = build_service();
	let backend: &Backend = service.inner();
	// The actor's `Client::log_message`/`publish_diagnostics` calls send into
	// `ClientSocket`'s internal channel; nothing reads it back out unless we
	// drain it here (in a real server, `tower_lsp_server::Server::serve`
	// forwards it to the transport), so without this those calls would block
	// forever waiting for room in that channel.
	tokio::spawn(async move {
		use futures::stream::StreamExt;
		let (mut requests, _responses) = socket.split();
		while requests.next().await.is_some() {}
	});

	let uri: Uri = Uri::from_str("file:///tmp/probe/main.wx").unwrap();
	backend
		.did_open(DidOpenTextDocumentParams {
			text_document: TextDocumentItem {
				uri: uri.clone(),
				language_id: "wx".into(),
				version: 1,
				text:
					"fn add(a: i32, b: i32) -> i32 { a + b }\nexport { add }\n"
						.into(),
			},
		})
		.await;

	backend
		.did_change(DidChangeTextDocumentParams {
			text_document: VersionedTextDocumentIdentifier {
				uri: uri.clone(),
				version: 2,
			},
			content_changes: vec![TextDocumentContentChangeEvent {
				range: None,
				range_length: None,
				text:
					"fn add(x: i64, y: i64) -> i64 { x + y }\nexport { add }\n"
						.into(),
			}],
		})
		.await;

	let start = Instant::now();
	let result = backend
		.hover(HoverParams {
			text_document_position_params: TextDocumentPositionParams {
				text_document: TextDocumentIdentifier { uri: uri.clone() },
				position: Position {
					line: 0,
					character: 4,
				},
			},
			work_done_progress_params: Default::default(),
		})
		.await
		.expect("hover should not error");
	assert!(
		start.elapsed().as_secs() < 5,
		"hover took suspiciously long — the actor may be deadlocked"
	);

	let HoverContents::Markup(markup) =
		result.expect("hover should resolve `add`").contents
	else {
		panic!("expected markup hover contents");
	};
	assert!(
		markup.value.contains("x: i64, y: i64"),
		"hover should reflect the `did_change` edit (i64 params), got: {}",
		markup.value
	);
}

/// Resolves the `FileId` for a given file path from a compiled root.
fn file_id_for(compiled: &CompiledRoot, path: &Path) -> FileId {
	compiled
		.graph
		.crates
		.iter()
		.flat_map(|cg| cg.modules.iter())
		.find(|m| Path::new(&m.file_path) == path)
		.unwrap_or_else(|| {
			panic!("file not found in compiled graph: {}", path.display())
		})
		.file_id
}

fn open_document(text: &str) -> OpenDocument {
	use std::sync::atomic::{AtomicI32, Ordering};
	static COUNTER: AtomicI32 = AtomicI32::new(1);
	OpenDocument {
		text: text.to_string(),
		lsp_version: COUNTER.fetch_add(1, Ordering::Relaxed),
	}
}

#[test]
fn discover_crate_root_walks_up_to_main_wx() {
	let workspace_root = PathBuf::from("/workspace");
	let crate_root = workspace_root.join("app").join("main.wx");
	let child_file = workspace_root.join("app").join("math").join("add.wx");

	let mut open_documents = HashMap::new();
	open_documents.insert(crate_root.clone(), open_document("module math;"));

	let discovered =
		discover_crate_root(&open_documents, &[workspace_root], &child_file);

	assert_eq!(discovered, Some(crate_root));
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
			code: None,
			code_description: None,
			source: Some("wx".to_string()),
			message: "error".to_string(),
			related_information: None,
			tags: None,
			data: None,
		}],
	)]);

	let publish_paths =
		diagnostic_publish_paths(&previous, &owned_files, &diagnostics_by_file);

	assert!(publish_paths.contains(&main));
	assert!(publish_paths.contains(&child));
	assert_eq!(publish_paths.len(), 2);
}

#[test]
#[ignore = "fix lsp later"]
fn analyze_root_updates_multi_file_diagnostics_when_overlay_changes() {
	let root = PathBuf::from("/workspace/app/main.wx");
	let child = PathBuf::from("/workspace/app/math.wx");

	let mut state = ServerState::default();
	state.open_documents.insert(
		root.clone(),
		open_document(
			"module math;\n\nfn compute() -> i32 {\n    math::add()\n}\n",
		),
	);
	state.open_documents.insert(
		child.clone(),
		open_document("fn add() -> bool {\n    true\n}\n"),
	);

	let broken = analyze_root(&mut state, &root, &mut Vec::new());
	assert!(broken.owned_files.contains(&root));
	assert!(broken.owned_files.contains(&child));
	assert!(
		broken
			.diagnostics_by_file
			.get(&root)
			.is_some_and(|diagnostics| diagnostics
				.iter()
				.any(|d| d.severity == Some(DiagnosticSeverity::ERROR))),
		"expected a root file error when child module has incompatible type"
	);

	state.open_documents.insert(
		child.clone(),
		open_document("fn add() -> i32 {\n    1\n}\n"),
	);

	let fixed = analyze_root(&mut state, &root, &mut Vec::new());
	assert!(fixed.owned_files.contains(&root));
	assert!(fixed.owned_files.contains(&child));
	assert!(
		fixed
			.diagnostics_by_file
			.get(&root)
			.is_none_or(|diagnostics| diagnostics
				.iter()
				.all(|d| d.severity != Some(DiagnosticSeverity::ERROR))),
		"expected root file errors to clear after fixing the child module overlay"
	);
}

#[test]
#[ignore = "fix lsp later"]
fn refresh_file_from_child_path_discovers_root_and_republishes_root_diagnostics()
 {
	let workspace_root = PathBuf::from("/workspace");
	let root = workspace_root.join("app").join("main.wx");
	let child = workspace_root.join("app").join("math.wx");

	let mut state = ServerState {
		workspace_folders: vec![workspace_root],
		..Default::default()
	};
	state.open_documents.insert(
		root.clone(),
		open_document(
			"module math;\n\nfn compute() -> i32 {\n    math::add()\n}\n",
		),
	);
	state.open_documents.insert(
		child.clone(),
		open_document("fn add() -> bool {\n    true\n}\n"),
	);

	let broken_publish = compute_refresh(&mut state, &child, &mut Vec::new());

	assert_eq!(owning_root(&state, &child), Some(root.as_path()));
	assert_eq!(owning_root(&state, &root), Some(root.as_path()));

	assert!(
		broken_publish.iter().any(|(path, diags)| {
			path == &root
				&& diags
					.iter()
					.any(|d| d.severity == Some(DiagnosticSeverity::ERROR))
		}),
		"expected refresh from child path to publish a root-file error"
	);

	state.open_documents.insert(
		child.clone(),
		open_document("fn add() -> i32 {\n    1\n}\n"),
	);

	let fixed_publish = compute_refresh(&mut state, &child, &mut Vec::new());

	assert!(
		fixed_publish.iter().any(|(path, diags)| {
			path == &root
				&& diags
					.iter()
					.all(|d| d.severity != Some(DiagnosticSeverity::ERROR))
		}),
		"expected refresh from child path to clear root-file errors after fixing the child overlay"
	);
}

// ── Completion integration tests
// ─────────────────────────────────────────────────────

fn compile_source(root: &PathBuf, source: &str) -> (ServerState, CompiledRoot) {
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(root.clone(), open_document(source));
	analyze_root(&mut state, root, &mut Vec::new());
	let compiled = state.cached.remove(root).expect("compilation failed");
	(state, compiled)
}

/// Compiles `root_source` alongside additional `(path, source)` files (e.g.
/// files pulled in via `module foo;` declarations).
fn compile_multi_source(
	root: &PathBuf,
	root_source: &str,
	extra_files: &[(&PathBuf, &str)],
) -> (ServerState, CompiledRoot) {
	let mut state = ServerState::default();
	state
		.open_documents
		.insert(root.clone(), open_document(root_source));
	for (path, source) in extra_files {
		state
			.open_documents
			.insert((*path).clone(), open_document(source));
	}
	analyze_root(&mut state, root, &mut Vec::new());
	let compiled = state.cached.remove(root).expect("compilation failed");
	(state, compiled)
}

#[test]
fn completion_inside_function_includes_params() {
	let root = PathBuf::from("/test/main.wx");
	// Cursor is on the blank line inside the function body (after the newline).
	let source = "fn add(a: i32, b: i32) -> i32 {\n    \n}";
	// offset 37 lands in the "    " whitespace on the second line, inside the body.
	let cursor = 37;

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"a"),
		"expected param `a` in completions; got: {labels:?}"
	);
	assert!(
		labels.contains(&"b"),
		"expected param `b` in completions; got: {labels:?}"
	);
}

#[test]
fn completion_inside_function_includes_locals_declared_before_cursor() {
	let root = PathBuf::from("/test/main.wx");
	// "x" is declared before cursor; "y" is declared after.
	let source = "fn f() -> i32 {\n    local x: i32 = 1;\n    \n    local y: i32 = 2;\n    x\n}";
	// Find the offset of the blank line (after "    local x: i32 = 1;\n    ").
	let cursor = source.find("\n    local y").unwrap(); // just before "local y"

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"x"),
		"expected `x` in completions; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"y"),
		"expected `y` NOT in completions yet; got: {labels:?}"
	);
}

#[test]
fn completion_in_type_annotation_position_excludes_functions_and_consts() {
	// Regression test: `CompletionContext::TypeAnnotation` used to reuse
	// `global_completion_items` wholesale, which includes every kind
	// (functions, consts, globals, traits, ...) valid in *value* position —
	// so typing `local x: ` offered a free function or const as if it were
	// a type. Fixed by `type_completion_items`, restricted to
	// `is_type_like` kinds (`Struct`/`Enum`/`TypeSet`/`Namespace`).
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point {
		    x: i32,
		}

		const MAX: i32 = 10;

		fn helper() -> i32 {
		    0
		}

		fn test() {
		    local p:
		}
	"};
	let cursor = source.find("local p:").unwrap() + "local p:".len();

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"Point"),
		"expected struct `Point` in type-position completions; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"MAX"),
		"const `MAX` must not be offered in type position; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"helper"),
		"function `helper` must not be offered in type position; got: {labels:?}"
	);
}

#[test]
fn completion_excludes_impl_methods_and_associated_functions() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! { "
		struct Point {
		    x: i32,
		    y: i32,
		}

		impl Point {
		    fn new(x: i32, y: i32) -> Point {
		        Point { x: x, y: y }
		    }

		    pub fn sum(self) -> i32 {
		        self.x + self.y
		    }
		}

		fn test() {

		}
	" };
	// Cursor on the blank line inside `test`'s body.
	let cursor = source.find("fn test() {\n").unwrap() + "fn test() {\n".len();

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"test"),
		"expected free function `test` in completions; got: {labels:?}"
	);
	assert!(
		labels.contains(&"Point"),
		"expected struct `Point` in completions; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"new"),
		"associated function `Point::new` must not be bare-callable; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"sum"),
		"method `Point::sum` must not be bare-callable; got: {labels:?}"
	);
}

#[test]
fn completion_excludes_enum_variants_from_bare_identifier_position() {
	// Regression test: enum variants are only ever resolved as a qualified
	// member (`Enum::Variant` — see `ResolvedMember::EnumVariant` in
	// `tir/builder.rs`, the sole place they're resolved), never as a bare
	// name, but `build_symbol_index` unconditionally pushed them into
	// `global_definitions` (unlike methods/associated consts, which already
	// gate on `parent.is_none()`), so they leaked into plain-identifier
	// completion as if `StdIn` alone were a valid expression.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! { "
		enum FileDescriptor: u8 {
		    StdIn,
		    StdOut,
		    StdErr,
		}

		fn test() {

		}
	" };
	let cursor = source.find("fn test() {\n").unwrap() + "fn test() {\n".len();

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"FileDescriptor"),
		"expected enum `FileDescriptor` in completions; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"StdIn"),
		"variant `FileDescriptor::StdIn` must not be bare-accessible; got: {labels:?}"
	);
}

#[test]
fn completion_inside_function_shows_globals_too() {
	let root = PathBuf::from("/test/main.wx");
	let source = "fn helper() -> i32 { 0 }\nfn main() -> i32 {\n    \n}";
	// Cursor in the blank line inside main's body.
	let cursor = source.find("\n    \n}").unwrap() + 5;

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"helper"),
		"expected global function `helper` in completions; got: {labels:?}"
	);
}

#[test]
fn completion_sorts_locals_before_globals() {
	let root = PathBuf::from("/test/main.wx");
	// "zeta" (local) would sort after "alpha" (global) alphabetically by
	// label — locals should still come first via `sort_text`.
	let source =
		"fn alpha() -> i32 { 0 }\nfn main() -> i32 {\n    local zeta = 1;\n\n}";
	let cursor = source.find("1;\n").unwrap() + "1;\n".len();

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);

	let zeta = items
		.iter()
		.find(|i| i.label == "zeta")
		.expect("local `zeta` should be suggested");
	let alpha = items
		.iter()
		.find(|i| i.label == "alpha")
		.expect("global `alpha` should be suggested");

	assert!(
		zeta.sort_text < alpha.sort_text,
		"expected local `zeta` to sort before global `alpha`; zeta sort_text={:?}, alpha sort_text={:?}",
		zeta.sort_text,
		alpha.sort_text
	);
}

#[test]
fn completion_prefix_filters_results() {
	let root = PathBuf::from("/test/main.wx");
	let source = "fn alpha() -> i32 { 0 }\nfn beta() -> i32 {\n    al\n}";
	// Cursor right after "al" inside beta's body.
	let cursor = source.find("al\n}").unwrap() + 2;

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"alpha"),
		"expected `alpha` in completions; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"beta"),
		"expected `beta` filtered out; got: {labels:?}"
	);
}

#[test]
fn completion_hides_sibling_module_items_without_use() {
	let root = PathBuf::from("/test/main.wx");
	let math = PathBuf::from("/test/math.wx");
	let source = "module math;\nfn main() -> i32 {\n    \n}";
	let cursor = source.find("\n    \n}").unwrap() + 5;

	let (_, compiled) = compile_multi_source(
		&root,
		source,
		&[(&math, "pub fn add() -> i32 { 1 }")],
	);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"main"),
		"expected root-level `main` in completions; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"add"),
		"expected `math::add` NOT to be visible unqualified from root; got: {labels:?}"
	);
}

#[test]
fn completion_shows_sibling_module_items_via_wildcard_use() {
	let root = PathBuf::from("/test/main.wx");
	let math = PathBuf::from("/test/math.wx");
	let source = "module math;\nuse math::*;\nfn main() -> i32 {\n    \n}";
	let cursor = source.find("\n    \n}").unwrap() + 5;

	let (_, compiled) = compile_multi_source(
		&root,
		source,
		&[(&math, "pub fn add() -> i32 { 1 }")],
	);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"add"),
		"expected `add` visible after `use math::*;`; got: {labels:?}"
	);
}

#[test]
fn path_completion_after_enum_lists_variants() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		enum FileDescriptor: u8 {
		    StdIn,
		    StdOut,
		    StdErr,
		}

		fn test() {
		    FileDescriptor::
		}
	"};
	let cursor =
		source.find("FileDescriptor::").unwrap() + "FileDescriptor::".len();

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"StdIn")
			&& labels.contains(&"StdOut")
			&& labels.contains(&"StdErr"),
		"expected all three variants after `FileDescriptor::`; got: {labels:?}"
	);
}

#[test]
fn path_completion_after_struct_lists_only_pub_methods() {
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point {
		    x: i32,
		}

		impl Point {
		    pub fn origin() -> Self {
		        Self::{ x: 0 }
		    }

		    fn private_helper() -> i32 {
		        0
		    }
		}

		fn test() {
		    Point::
		}
	"};
	let cursor = source.rfind("Point::").unwrap() + "Point::".len();

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"origin"),
		"expected `pub fn origin` after `Point::`; got: {labels:?}"
	);
	assert!(
		!labels.contains(&"private_helper"),
		"non-pub `private_helper` must not be offered via `Point::`; got: {labels:?}"
	);
}

#[test]
fn path_completion_after_namespace_lists_module_members() {
	let root = PathBuf::from("/test/main.wx");
	let math = PathBuf::from("/test/math.wx");
	let source = "module math;\nfn test() {\n    math::\n}";
	let cursor = source.find("math::\n").unwrap() + "math::".len();

	let (_, compiled) = compile_multi_source(
		&root,
		source,
		&[(&math, "pub fn add() -> i32 { 1 }")],
	);
	let file_id = file_id_for(&compiled, &root);

	let items = completion_items(
		&compiled.tir,
		&compiled.graph.interner,
		&compiled.symbol_index,
		file_id,
		source,
		cursor,
	);
	let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

	assert!(
		labels.contains(&"add"),
		"expected `add` after `math::`; got: {labels:?}"
	);
}

#[test]
fn resolve_source_and_offset_prefers_live_buffer_over_stale_compiled_source() {
	// Regression test: signature_help used to compute `offset` from
	// `compiled.graph.files` (the source as of the last save) and then slice
	// into that same stale, shorter string. Typing new lines above the
	// cursor without saving (e.g. wrapping existing code in a new `module`
	// block) pushed the live cursor position past the stale source's length
	// and panicked on `source[..offset]`. `resolve_source_and_offset` is the
	// shared fix both `completion` and `signature_help` now go through —
	// this exercises it directly against the exact reported scenario.
	let root = PathBuf::from("/test/main.wx");
	let stale_source = "fn test() {\n\n}";
	let (mut state, compiled) = compile_source(&root, stale_source);
	state.cached.insert(root.clone(), compiled);

	let live_source = "module test {\n    fn foo()\n}\n\nfn test() {\n\n}";
	state
		.open_documents
		.insert(root.clone(), open_document(live_source));

	// Cursor right after "fn foo()" on line 1 — this line doesn't exist at
	// all in `stale_source`, which is only 14 bytes long.
	let position = Position {
		line: 1,
		character: 11,
	};
	let uri = Uri::from_file_path(&root).expect("valid file uri");
	let compiled = state.cached.get(&root).unwrap();
	let file_id = file_id_for(compiled, &root);

	// Must not panic, and must resolve against the live buffer (not the
	// 14-byte stale one) — this is exactly what used to panic.
	let (source, offset) = crate::resolve_source_and_offset(
		&state, compiled, &uri, file_id, position,
	)
	.expect("should resolve source/offset from the live buffer");
	assert_eq!(source, live_source);
	assert!(offset <= source.len());

	let call = find_active_call(source, offset);
	assert!(call.is_some(), "expected an active call for `fn foo(`");
}

#[test]
fn resolve_uri_finds_virtual_stdlib_module() {
	// Regression test: `Uri::to_file_path()` doesn't check the scheme, so it
	// returns a bogus `Some(path)` for a `wx://std/...` virtual URI instead
	// of `None`. `resolve_uri` must not use that to short-circuit past the
	// string-comparison fallback, or hover/goto-definition/semantic-tokens
	// silently stop working inside the standard library file.
	let root = PathBuf::from("/test/main.wx");
	let (_, compiled) = compile_source(&root, "fn main() {}");
	let stdlib_file_id = compiled
		.graph
		.crates
		.iter()
		.flat_map(|cg| cg.modules.iter())
		.find(|m| m.file_path == "lib.wx")
		.map(|m| m.file_id)
		.expect("stdlib module should be present in the compiled graph");
	let uri = crate::file_id_to_uri(&compiled, stdlib_file_id)
		.expect("should construct a wx://std/ URI for the stdlib module");

	let mut state = ServerState::default();
	state.cached.insert(root.clone(), compiled);

	let resolved = crate::resolve_uri(&state, &uri);
	assert_eq!(
		resolved.map(|(_, file_id)| file_id),
		Some(stdlib_file_id),
		"resolve_uri should find the stdlib module via its constructed wx:// URI"
	);
}

#[test]
fn full_diagnostic_renders_and_handles_bad_index() {
	let root = PathBuf::from("/test/main.wx");
	let (_, compiled) = compile_source(
		&root,
		"fn main() {\n    local x: i32 = 1;\n}\nexport { main }\n",
	);

	assert!(
		compiled
			.tir
			.diagnostics
			.iter()
			.any(|d| d.code.as_deref() == Some("W1001")),
		"expected an unused-variable warning to drive this test's diagnostic"
	);

	let uri = Uri::from_file_path(&root).unwrap();
	let mut state = ServerState::default();
	state.cached.insert(root.clone(), compiled);

	let rendered = crate::render_full_diagnostic(&state, &uri, 0);
	assert!(
		rendered.contains('x'),
		"expected the rendered diagnostic to include the source snippet: {rendered}"
	);
	assert!(
		rendered.contains('\x1b'),
		"expected ANSI escape codes so the client can color the view: {rendered:?}"
	);

	let out_of_range = crate::render_full_diagnostic(&state, &uri, 99);
	assert!(
		out_of_range.contains("Unable to find original wx diagnostic"),
		"expected a fallback message for an out-of-range index: {out_of_range}"
	);

	let untracked_uri = Uri::from_str("file:///not/a/tracked/file.wx").unwrap();
	let untracked = crate::render_full_diagnostic(&state, &untracked_uri, 0);
	assert!(
		untracked.contains("Unable to find original wx diagnostic"),
		"expected a fallback message for a URI outside any tracked root: {untracked}"
	);
}

#[test]
fn unused_enum_variants_get_one_squiggle_each() {
	// `report_unused_enum_variants` has no primary label — every listed
	// variant is equally "the problem" — so `diagnostic_locations` must
	// expand it into one LSP diagnostic per variant instead of collapsing
	// to whichever label happens to be first in the vec (regression test
	// for the bug where only the first unused variant got underlined).
	let root = PathBuf::from("/test/main.wx");
	let (_, compiled) = compile_source(
		&root,
		indoc::indoc! {"
			enum Direction: i32 {
			    Right,
			    Down,
			    Left,
			}
			fn get_right() -> Direction {
			    Direction::Right
			}
			export { get_right }
		"},
	);

	let analysis = crate::analysis_from_compiled_root(&compiled);
	let diagnostics = analysis
		.diagnostics_by_file
		.get(&root)
		.expect("expected diagnostics for main.wx");

	let unused: Vec<_> = diagnostics
		.iter()
		.filter(|d| {
			d.code.as_ref().is_some_and(
				|code| matches!(code, NumberOrString::String(s) if s == "W1009"),
			)
		})
		.collect();

	assert_eq!(
		unused.len(),
		2,
		"expected one LSP diagnostic per unused variant (Down, Left), got: {diagnostics:?}"
	);
	assert_ne!(
		unused[0].range, unused[1].range,
		"each unused variant should get its own distinct squiggle range"
	);
}

#[test]
fn enum_type_used_as_return_type_resolves_to_its_definition() {
	// Regression test: `build_symbol_index` recorded accesses for enum
	// *variants* but never read `enum_.accesses`, so a bare enum type name
	// used in a type position (like a return type) had no reference entry —
	// hover/go-to-definition on it silently failed.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		enum Status: u8 {
		    Ok = 200,
		}

		fn test() -> Status {
		    Status::Ok
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	// Offset of `Status` in `-> Status`, not the `Status::Ok` namespace access.
	let return_type_offset = source.find("-> Status").unwrap() + "-> ".len();

	let found = compiled
		.symbol_index
		.find_at_position(file_id, return_type_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the return type position")
		});

	assert!(
		matches!(found.kind, SymbolKind::Enum(_)),
		"expected the return type reference to resolve to the enum; got: {found:?}"
	);

	let definition = compiled
		.symbol_index
		.definitions
		.iter()
		.find(|d| d.kind == found.kind)
		.expect("expected a matching enum definition entry");
	assert_eq!(
		&source[definition.source.span.start as usize
			..definition.source.span.end as usize],
		"Status",
		"go-to-definition should land on the `enum Status` name"
	);
}

#[test]
fn self_type_in_trait_method_resolves_to_trait_definition() {
	// Regression test: `build_symbol_index` recorded accesses for a trait's
	// own name and its associated types, but never read the trait's implicit
	// `self_type_param` — so a `Self` reference inside a trait method (e.g. a
	// return type) had no reference entry and hover/go-to-definition on it
	// silently did nothing.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		trait Cloneable {
		    fn duplicate(self) -> Self;
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let self_offset = source.find("-> Self").unwrap() + "-> ".len();

	let found = compiled
		.symbol_index
		.find_at_position(file_id, self_offset as u32)
		.unwrap_or_else(|| panic!("expected a symbol at the `Self` position"));

	assert!(
		matches!(
			found.kind,
			SymbolKind::TypeParam {
				owner: TypeParamOwner::Trait(_),
				param_index: 0
			}
		),
		"expected the `Self` reference to resolve to the trait's implicit type param; got: {found:?}"
	);

	let definition = compiled
		.symbol_index
		.definition_for_kind(found.kind)
		.expect("expected a matching Self type param redirect target");
	assert_eq!(
		&source[definition.source.span.start as usize
			..definition.source.span.end as usize],
		"Cloneable",
		"go-to-definition for `Self` should land on the enclosing trait's name"
	);
}

#[test]
fn trait_own_name_resolves_to_trait_not_self_type_param() {
	// Regression test: the trait's own declared name sits at the exact same
	// span as its implicit `self_type_param`'s redirect target
	// (`self_type_param.name.span` is set to the trait's own `name.span` at
	// construction — see `self_type_in_trait_method_resolves_to_trait_definition`).
	// Before `transparent_definitions` existed, both lived in `definitions`,
	// and `find_narrowest`'s reversed iteration order happened to prefer the
	// type-param entry on that tie — so clicking the trait's own declared
	// name resolved as `TypeParam { owner: Trait(_), .. }` instead of
	// `Trait`. Go-to-definition itself was unaffected (both kinds' redirect
	// targets are this same span either way), but everything else keyed off
	// `SymbolKind` was wrong: hover showed the type-param's text instead of
	// the trait's, semantic tokens emitted two conflicting overlapping
	// entries for one span, and — worst — Rename from this position would
	// have renamed every `Self` occurrence in the trait's default bodies
	// while leaving the trait's own name untouched.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		trait Cloneable {
		    fn duplicate(self) -> Self;
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let trait_name_offset =
		source.find("trait Cloneable").unwrap() + "trait ".len();
	let found = compiled
		.symbol_index
		.find_at_position(file_id, trait_name_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the trait's own declared name")
		});

	assert!(
		matches!(found.kind, SymbolKind::Trait(_)),
		"expected the trait's own name to resolve as SymbolKind::Trait, not the implicit Self type param; got: {found:?}"
	);

	let definition = compiled
		.symbol_index
		.definition_for_kind(found.kind)
		.expect("expected a matching trait definition entry");
	assert_eq!(
		definition.source.span.start, trait_name_offset as u32,
		"sanity check: a Trait definition's redirect target is its own declaration site"
	);
}

#[test]
fn self_type_in_impl_block_resolves_to_struct_definition() {
	// Regression test: `Self` inside a plain `impl` block resolves to the
	// target's concrete `Type::Struct`/`Type::Enum` directly (not a
	// `Type::TypeParam`). It's tracked as `SymbolKind::InherentImplSelf`
	// rather than `SymbolKind::Struct` — same underlying target, but a
	// distinct kind — so `Rename` (which matches purely on `SymbolKind`
	// equality) renaming the struct doesn't also rewrite the `Self`
	// keyword text. Hover/go-to-definition still redirect to the impl's
	// target type, via a synthetic definition entry at the impl header's
	// own target span.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point {
		    x: i32,
		    y: i32,
		}

		impl Point {
		    pub fn origin() -> Self {
		        Self::{ x: 0, y: 0 }
		    }
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let return_type_offset = source.find("-> Self").unwrap() + "-> ".len();

	let found = compiled
		.symbol_index
		.find_at_position(file_id, return_type_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the `Self` return type position")
		});

	assert!(
		matches!(found.kind, SymbolKind::InherentImplSelf(_)),
		"expected the `Self` reference to resolve to the impl block; got: {found:?}"
	);

	let definition = compiled
		.symbol_index
		.definition_for_kind(found.kind)
		.expect("expected a matching InherentImplSelf redirect target");
	assert_eq!(
		&source[definition.source.span.start as usize
			..definition.source.span.end as usize],
		"Point",
		"go-to-definition for `Self` should land on the impl header's target"
	);

	// `Self::{ .. }` struct-init syntax goes through a different call site
	// than the return-type position but funnels into the same resolution
	// function, so it should resolve too.
	let init_offset = source.find("Self::{").unwrap();
	let found_init = compiled
		.symbol_index
		.find_at_position(file_id, init_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the `Self::{{ }}` init position")
		});
	assert!(
		matches!(found_init.kind, SymbolKind::InherentImplSelf(_)),
		"expected `Self::{{ }}` to resolve to the impl block; got: {found_init:?}"
	);
}

#[test]
fn self_receiver_param_resolves_to_self_param_not_plain_param() {
	// Regression test: a method's `self` receiver used to be indistinguishable
	// from any other named parameter (`SymbolKind::Param { func_id,
	// param_idx: 0 }`), so semantic tokens colored it like an ordinary
	// parameter instead of leaving it to the editor's keyword highlighting —
	// same class of bug as `Self`/`self` inside impl bodies. Fixed by giving
	// it its own `SymbolKind::SelfParam`, detected the same way TIR itself
	// decides a function is a method: first param named `self`.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point {
		    x: i32,
		}

		impl Point {
		    pub fn x_value(self) -> i32 {
		        self.x
		    }
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let param_offset = source.find("(self)").unwrap() + "(".len();
	let found_param = compiled
		.symbol_index
		.find_at_position(file_id, param_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the `self` parameter position")
		});
	assert!(
		matches!(found_param.kind, SymbolKind::SelfParam(_)),
		"expected the `self` receiver to resolve to SymbolKind::SelfParam; got: {found_param:?}"
	);

	let body_offset = source.find("self.x").unwrap();
	let found_body = compiled
		.symbol_index
		.find_at_position(file_id, body_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the `self` body reference")
		});
	assert!(
		matches!(found_body.kind, SymbolKind::SelfParam(_)),
		"expected `self.x` to resolve to SymbolKind::SelfParam too; got: {found_body:?}"
	);

	assert!(
		symbol_kind_to_token_type(found_param.kind).is_none(),
		"the `self` receiver must not get a semantic token — the editor's \
		 keyword grammar highlights it instead"
	);
}

#[test]
fn impl_header_target_resolves_to_struct_not_self() {
	// Regression test: the impl header's own target mention (`impl Point`'s
	// `Point`) sits at the exact same span as `InherentImplSelf`'s redirect
	// target (`Self` inside the impl lands there too). Before
	// `transparent_definitions` existed, both lived in `definitions`, and
	// `find_at_position` ties toward definitions — so clicking the header's
	// own `Point` resolved as `InherentImplSelf`, whose redirect target was
	// that exact same position, making go-to-definition a no-op (which
	// editors typically show as a references picker instead of navigating).
	// It must resolve as a plain `Struct` reference instead, landing on the
	// real `struct Point` declaration.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point {
		    x: i32,
		}

		impl Point {
		    pub fn origin() -> Self {
		        Self::{ x: 0 }
		    }
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let header_target_offset =
		source.find("impl Point").unwrap() + "impl ".len();
	let found = compiled
		.symbol_index
		.find_at_position(file_id, header_target_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the impl header's `Point`")
		});

	assert!(
		matches!(found.kind, SymbolKind::Struct(_)),
		"expected the impl header's own target to resolve as a plain struct reference, not InherentImplSelf; got: {found:?}"
	);

	let definition = compiled
		.symbol_index
		.definition_for_kind(found.kind)
		.expect("expected a matching struct definition entry");
	let declaration_offset =
		source.find("struct Point").unwrap() + "struct ".len();
	assert_eq!(
		definition.source.span.start, declaration_offset as u32,
		"go-to-definition on the impl header's target should land on the real `struct Point` declaration, not the impl header itself"
	);
}

#[test]
fn reference_search_kinds_merges_self_usages_targeting_the_struct() {
	// Regression test: `textDocument/references` on a struct name used to
	// match `SymbolKind::Struct` exactly, so it missed every `Self` usage
	// inside that struct's own impls — tracked separately as
	// `InherentImplSelf` specifically so `Rename` wouldn't rewrite them
	// (see `self_type_in_impl_block_resolves_to_struct_definition`), but
	// References should still surface them, matching rust-analyzer.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		struct Point {
		    x: i32,
		}

		impl Point {
		    pub fn origin() -> Self {
		        Self::{ x: 0 }
		    }
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let struct_name_offset =
		source.find("struct Point").unwrap() + "struct ".len();
	let found = compiled
		.symbol_index
		.find_at_position(file_id, struct_name_offset as u32)
		.unwrap_or_else(|| panic!("expected a symbol at the `Point` name"));
	assert!(
		matches!(found.kind, SymbolKind::Struct(_)),
		"expected the struct name to resolve to SymbolKind::Struct; got: {found:?}"
	);

	let search_kinds = reference_search_kinds(
		&compiled.tir,
		&compiled.symbol_index,
		found.kind,
	);
	assert!(
		search_kinds.contains(&found.kind),
		"expected the literal struct name kind to still be included"
	);
	assert!(
		search_kinds
			.iter()
			.any(|k| matches!(k, SymbolKind::InherentImplSelf(_))),
		"expected `Self` usages in Point's impl to be merged in; got: {search_kinds:?}"
	);
	assert_eq!(
		search_kinds.len(),
		2,
		"expected exactly the struct kind plus one InherentImplSelf kind (one impl block); got: {search_kinds:?}"
	);

	// Rename must NOT use this merge — it stays exact-kind-only, or it
	// would rewrite `Self` keyword text when renaming the struct.
	let rename_kinds = compiled
		.symbol_index
		.references
		.iter()
		.filter(|e| e.kind == found.kind);
	assert!(
		rename_kinds.clone().count() > 0,
		"sanity check: Point should have at least one literal reference"
	);
	assert!(
		rename_kinds
			.clone()
			.all(|e| !matches!(e.kind, SymbolKind::InherentImplSelf(_))),
		"exact-kind filtering (what Rename uses) must never include InherentImplSelf"
	);
}

#[test]
fn implementation_locations_finds_inherent_and_trait_impls_of_a_struct() {
	// `textDocument/implementation` on `struct Point` should land on both
	// impl headers' target-type spans — the inherent `impl Point { }` and
	// the `impl Drawable for Point { }` trait impl — reusing the same
	// `ImplTarget`-keyed reverse indices `reference_search_kinds` uses.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		trait Drawable {
		    fn draw(&self) -> i32;
		}

		struct Point {
		    x: i32,
		}

		impl Point {
		    pub fn origin() -> Self {
		        Self::{ x: 0 }
		    }
		}

		impl Drawable for Point {
		    fn draw(&self) -> i32 {
		        self.x
		    }
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let struct_name_offset =
		source.find("struct Point").unwrap() + "struct ".len();
	let found = compiled
		.symbol_index
		.find_at_position(file_id, struct_name_offset as u32)
		.unwrap_or_else(|| panic!("expected a symbol at the `Point` name"));
	assert!(matches!(found.kind, SymbolKind::Struct(_)));

	let locations = implementation_locations(
		&compiled.tir,
		&compiled.symbol_index,
		found.kind,
	);
	assert_eq!(
		locations.len(),
		2,
		"expected the inherent impl and the trait impl; got: {locations:?}"
	);

	let inherent_target_offset =
		source.find("impl Point").unwrap() + "impl ".len();
	let trait_impl_target_offset =
		source.find("impl Drawable for Point").unwrap()
			+ "impl Drawable for ".len();
	let offsets: Vec<u32> = locations.iter().map(|s| s.span.start).collect();
	assert!(
		offsets.contains(&(inherent_target_offset as u32)),
		"expected a location at the inherent impl's target span; got: {offsets:?}"
	);
	assert!(
		offsets.contains(&(trait_impl_target_offset as u32)),
		"expected a location at the trait impl's target span; got: {offsets:?}"
	);
}

#[test]
fn implementation_locations_finds_impls_of_a_trait() {
	// `textDocument/implementation` on `trait Drawable` should land on every
	// impl of it, regardless of target type.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		trait Drawable {
		    fn draw(&self) -> i32;
		}

		struct Point {
		    x: i32,
		}

		impl Drawable for Point {
		    fn draw(&self) -> i32 {
		        self.x
		    }
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let trait_name_offset =
		source.find("trait Drawable").unwrap() + "trait ".len();
	let found = compiled
		.symbol_index
		.find_at_position(file_id, trait_name_offset as u32)
		.unwrap_or_else(|| panic!("expected a symbol at the `Drawable` name"));
	assert!(matches!(found.kind, SymbolKind::Trait(_)));

	let locations = implementation_locations(
		&compiled.tir,
		&compiled.symbol_index,
		found.kind,
	);
	let trait_impl_target_offset =
		source.find("impl Drawable for Point").unwrap()
			+ "impl Drawable for ".len();
	assert_eq!(
		locations.iter().map(|s| s.span.start).collect::<Vec<_>>(),
		vec![trait_impl_target_offset as u32]
	);
}

#[test]
fn self_assoc_type_in_inherent_impl_resolves_to_trait_assoc_type() {
	// Regression test: `Self::Elem` inside a plain `impl Heap { .. }` block
	// (where `Heap` implements `Container` elsewhere) resolves `Self` to the
	// concrete `Heap` struct, so the `Elem` lookup went through
	// `resolve_impl_member`'s trait-impl fallback in the TIR builder — which
	// never recorded an access on `Container`'s associated type. Fixed by
	// having `resolve_impl_member` report which trait a member came from
	// (`MemberLookup::Trait { trait_index, .. }`) so the caller can record it.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		trait Bound {}
		impl Bound for u32 {}
		trait Container {
		    type Elem: Bound;
		}
		struct Heap {}
		impl Container for Heap {
		    type Elem = u32;
		}
		impl Heap {
		    fn zero() -> Self::Elem {
		        0
		    }
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let self_elem_offset = source.find("Self::Elem").unwrap() + "Self::".len();

	let found = compiled
		.symbol_index
		.find_at_position(file_id, self_elem_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the `Self::Elem` position")
		});

	assert!(
		matches!(found.kind, SymbolKind::AssocType { .. }),
		"expected `Self::Elem` to resolve to the associated type; got: {found:?}"
	);

	let definition = compiled
		.symbol_index
		.definitions
		.iter()
		.find(|d| d.kind == found.kind)
		.expect("expected a matching associated type definition entry");
	assert_eq!(
		&source[definition.source.span.start as usize
			..definition.source.span.end as usize],
		"Elem",
		"go-to-definition for `Self::Elem` should land on the trait's `type Elem` declaration"
	);
}

#[test]
fn memory_declaration_records_accesses_in_type_value_and_export_positions() {
	// Regression test: `memory` declarations never recorded any access at
	// all (unlike struct/enum/trait/const), and `wx-lsp`'s `SymbolKind` had
	// no `Memory` variant to begin with — so hover/go-to-definition on a
	// memory name silently did nothing everywhere: as a type (`heap::[]u8`,
	// `type M = heap;`), as a value receiver (`heap.size()`), and in an
	// `export { heap as "..." }` list.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		use std::*;

		memory heap: Memory where { Size = u32 } { min_pages: 1 };

		fn heap_size() -> u32 {
		    heap.size()
		}

		export {
		    heap as \"memory\",
		    heap_size
		}
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let definition = compiled
		.symbol_index
		.definitions
		.iter()
		.find(|d| matches!(d.kind, SymbolKind::Memory(_)))
		.expect("expected a definition entry for `memory heap`");

	// Value position: `heap.size()`.
	let value_offset = source.find("heap.size()").unwrap();
	let found_value = compiled
		.symbol_index
		.find_at_position(file_id, value_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the `heap.size()` receiver position")
		});
	assert_eq!(
		found_value.kind, definition.kind,
		"expected `heap` in `heap.size()` to resolve to the memory declaration"
	);

	// Export-list position: `heap as "memory"`.
	let export_offset = source.find("heap as").unwrap();
	let found_export = compiled
		.symbol_index
		.find_at_position(file_id, export_offset as u32)
		.unwrap_or_else(|| {
			panic!(
				"expected a symbol at the `heap as \"memory\"` export position"
			)
		});
	assert_eq!(
		found_export.kind, definition.kind,
		"expected `heap` in the export list to resolve to the memory declaration"
	);
}

#[test]
fn memory_associated_const_namespace_access_resolves() {
	// Regression test: `heap::DATA_END` resolves fine in the TIR (its access
	// is correctly recorded on a per-memory `Constant` forked by
	// `seed_memory_trait_impl_with`), but that forked const never gets a
	// `value` (its value is compiler-synthesized, not a user-written
	// initializer) — and `build_symbol_index`'s constant loop gated *both*
	// definitions and references behind `constant.value.is_some()`, which
	// wrongly excludes any associated const that structurally never has a
	// value (this one, and a trait's own abstract `const NAME: T;`
	// declaration). So `heap::DATA_END` had no definition or reference
	// entry at all — hover/go-to-definition silently did nothing.
	let root = PathBuf::from("/test/main.wx");
	let source = indoc::indoc! {"
		use std::*;

		memory heap: Memory where { Size = u32 } { min_pages: 1 };
		global mut bump: *u8 = heap::DATA_END;
	"};
	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	let data_end_offset = source.find("DATA_END").unwrap();
	let found = compiled
		.symbol_index
		.find_at_position(file_id, data_end_offset as u32)
		.unwrap_or_else(|| {
			panic!("expected a symbol at the `heap::DATA_END` position")
		});
	assert!(
		matches!(found.kind, SymbolKind::Const(_)),
		"expected `DATA_END` to resolve to a const; got: {found:?}"
	);

	let definition = compiled
		.symbol_index
		.definitions
		.iter()
		.find(|d| d.kind == found.kind)
		.expect("expected a matching const definition entry");

	// The forked per-memory const has no user-written declaration of its
	// own — `seed_memory_trait_impl_with` copies the `name`/`file_id` of the
	// `Memory` trait's abstract `const DATA_END: Self::*u8;` straight from
	// its template, so go-to-definition correctly lands there (in
	// `std/lib.wx`) rather than anywhere in this test's own source.
	let SymbolKind::Const(const_id) = found.kind else {
		unreachable!("checked above");
	};
	let const_index = compiled.tir.const_index(const_id).unwrap();
	let const_name = compiled.tir.constants[const_index as usize].name.inner;
	assert_eq!(
		compiled.graph.interner.resolve(const_name),
		Some("DATA_END"),
		"expected the resolved const to be named `DATA_END`"
	);
	assert_eq!(
		definition.source.span,
		compiled.tir.constants[const_index as usize].name.span,
		"go-to-definition should land on the `Memory` trait's `const DATA_END` declaration"
	);
}

#[test]
fn find_enclosing_function_returns_correct_function() {
	let root = PathBuf::from("/test/main.wx");
	let source = "fn first() -> i32 { 1 }\nfn second() -> i32 { 2 }";

	let (_, compiled) = compile_source(&root, source);
	let file_id = file_id_for(&compiled, &root);

	// Cursor inside "first" body — "{ 1 }" roughly at [19, 24)
	let in_first = source.find("{ 1 }").unwrap() as u32 + 2;
	let in_second = source.find("{ 2 }").unwrap() as u32 + 2;

	let first_idx = find_enclosing_function(&compiled.tir, file_id, in_first);
	let second_idx = find_enclosing_function(&compiled.tir, file_id, in_second);

	assert!(
		first_idx.is_some(),
		"expected to find enclosing function for cursor in `first`"
	);
	assert!(
		second_idx.is_some(),
		"expected to find enclosing function for cursor in `second`"
	);
	assert_ne!(
		first_idx, second_idx,
		"cursor positions in different functions should map to different indices"
	);
}
