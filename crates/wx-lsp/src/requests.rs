//! Answers to individual requests, each from one snapshot or one fresh parse.

use std::path::Path;

use codespan_reporting::term;
use codespan_reporting::term::termcolor::Ansi;
use tower_lsp_server::ls_types::{
	GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverContents,
	HoverParams, Location, MarkupContent, MarkupKind, Position, Range,
	ReferenceParams, SemanticTokens, SemanticTokensParams,
	SemanticTokensRangeParams, SemanticTokensRangeResult, SemanticTokensResult,
	TextEdit, Uri,
};
use wx_compiler::diagnostics::Diagnostics as _;
use wx_compiler::symbols::Keyword;

use crate::convert::{
	byte_to_position, file_id_to_uri, position_to_offset, span_to_range,
	uri_to_path,
};
use crate::diagnostics::diagnostic_locations;
use crate::hover;
use crate::projects::{ManifestState, discover_package_root};
use crate::semantic_tokens;
use crate::snapshot::load_compilation;
use crate::state::ServerState;
use crate::trace::Trace;

/// Where the name under the cursor is defined. Answered by the compiler's
/// own name resolutions, so a file with errors still navigates.
pub(crate) fn goto_definition(
	state: &ServerState,
	params: &GotoDefinitionParams,
) -> Option<GotoDefinitionResponse> {
	let position = &params.text_document_position_params;
	let (snapshot, file) = state.resolve_uri(&position.text_document.uri)?;
	let files = &snapshot.compilation.files;
	let offset = position_to_offset(files, file, position.position)?;
	let (_, definition) = snapshot.definition_at(file, offset)?;
	let definition = snapshot.sema.definition_target(definition)?;
	Some(GotoDefinitionResponse::Scalar(Location {
		uri: file_id_to_uri(files, definition.file_id)?,
		range: span_to_range(files, definition)?,
	}))
}

/// Project-wide references in the selected snapshot's package graph. No
/// compiler identities are compared across independently built snapshots.
pub(crate) fn references(
	state: &ServerState,
	params: &ReferenceParams,
) -> Option<Vec<Location>> {
	let position = &params.text_document_position;
	let (snapshot, file) = state.resolve_uri(&position.text_document.uri)?;
	let files = &snapshot.compilation.files;
	let offset = position_to_offset(files, file, position.position)?;
	let (_, definition) = snapshot.definition_at(file, offset)?;
	let mut spans = snapshot.sema.references_to(definition);
	if params.context.include_declaration
		&& let Some(span) = snapshot.sema.definition_span(definition)
		&& span.span.start != span.span.end
	{
		spans.push(span);
		spans.sort_unstable();
		spans.dedup();
	}
	Some(
		spans
			.into_iter()
			.filter_map(|span| {
				Some(Location {
					uri: file_id_to_uri(files, span.file_id)?,
					range: span_to_range(files, span)?,
				})
			})
			.collect(),
	)
}

/// The signature and doc comment of the name under the cursor.
pub(crate) fn hover(
	state: &ServerState,
	params: &HoverParams,
) -> Option<Hover> {
	let position = &params.text_document_position_params;
	let (snapshot, file) = state.resolve_uri(&position.text_document.uri)?;
	let files = &snapshot.compilation.files;
	let offset = position_to_offset(files, file, position.position)?;
	let (name, definition) = snapshot.definition_at(file, offset)?;
	let signature =
		hover::signature(&snapshot.sema, &snapshot.strings, definition)?;
	let doc = hover::has_doc_comment(definition)
		.then(|| snapshot.sema.definition_span(definition))
		.flatten()
		.and_then(|definition| {
			let source = &files.get(definition.file_id).ok()?.source;
			hover::leading_doc_comment(source, definition.span.start)
		});
	let value = match doc {
		Some(doc) => format!("```wx\n{signature}\n```\n\n---\n\n{doc}"),
		None => format!("```wx\n{signature}\n```"),
	};
	Some(Hover {
		contents: HoverContents::Markup(MarkupContent {
			kind: MarkupKind::Markdown,
			value,
		}),
		range: span_to_range(files, name),
	})
}

/// Every coloured name of the file.
pub(crate) fn semantic_tokens_full(
	state: &ServerState,
	params: &SemanticTokensParams,
) -> Option<SemanticTokensResult> {
	let (snapshot, file) = state.resolve_uri(&params.text_document.uri)?;
	let data = semantic_tokens::tokens(snapshot, file, None)?;
	Some(SemanticTokensResult::Tokens(SemanticTokens {
		result_id: None,
		data,
	}))
}

/// The coloured names of the file that overlap the requested range.
pub(crate) fn semantic_tokens_range(
	state: &ServerState,
	params: &SemanticTokensRangeParams,
) -> Option<SemanticTokensRangeResult> {
	let (snapshot, file) = state.resolve_uri(&params.text_document.uri)?;
	let data = semantic_tokens::tokens(snapshot, file, Some(params.range))?;
	Some(SemanticTokensRangeResult::Tokens(SemanticTokens {
		result_id: None,
		data,
	}))
}

/// The whole-file edit that formats `uri`, or no edits when it is already
/// formatted. Always reparses the live buffer instead of reading a snapshot,
/// so a format request never sees older text than the editor has; the
/// package's `wx.json` decides the layout, as it does for `wx format`.
pub(crate) fn format(
	state: &mut ServerState,
	uri: &Uri,
	trace: &mut Trace,
) -> Option<Vec<TextEdit>> {
	let path = uri_to_path(uri)?;
	let root = discover_package_root(
		&state.open_documents,
		&state.client.workspace_folders,
		&path,
	)?;
	let mut strings = Keyword::create_interner();
	let compilation = load_compilation(
		&state.open_documents,
		&mut state.projects,
		&root,
		&mut strings,
		trace,
	)
	.ok()?;
	let module = compilation
		.packages
		.iter()
		.flat_map(|package| package.modules.iter())
		.find(|module| {
			Path::new(module.file_path.as_str()) == path.as_path()
		})?;
	let ast = compilation.ast(module.file_id);
	if compilation.parse_diagnostics(module.file_id).has_errors() {
		return None;
	}
	let file = compilation.files.get(module.file_id).ok()?;
	let source = file.source.as_str();
	let ManifestState::Parsed(manifest) = &state.projects.get(&root)?.manifest
	else {
		return None;
	};
	let config = wx_fmt::RendererConfig::from_manifest(manifest.format);
	let formatted = trace.step("render", || {
		wx_fmt::format(
			ast,
			compilation.comments(module.file_id),
			&strings,
			source,
			config,
		)
	});
	// An already-formatted file is the common case for format-on-save. No
	// edits leaves the buffer untouched, so the client never sends a
	// `didChange` and nothing re-checks an identical document.
	if formatted == source {
		return Some(Vec::new());
	}
	let end =
		byte_to_position(&compilation.files, module.file_id, source.len())?;
	Some(vec![TextEdit {
		range: Range {
			start: Position::default(),
			end,
		},
		new_text: formatted,
	}])
}

/// One diagnostic's full, source-annotated text, re-rendered on demand for
/// the client's "full diagnostic" view. `index` counts the diagnostics
/// published for this file in `Snapshot::analysis`'s order.
pub(crate) fn render_full_diagnostic(
	state: &ServerState,
	uri: &Uri,
	index: usize,
) -> String {
	let Some((snapshot, _)) = state.resolve_uri(uri) else {
		return "Unable to find original wx diagnostic (file is no longer tracked)."
			.to_string();
	};
	let Some(target_path) = uri_to_path(uri) else {
		return "Unable to find original wx diagnostic.".to_string();
	};
	let files = &snapshot.compilation.files;
	let loading = snapshot.compilation.collect_diagnostics();
	let diagnostic = loading
		.iter()
		.chain(snapshot.sema.diagnostics())
		.flat_map(|diagnostic| {
			let target_path = &target_path;
			diagnostic_locations(files, diagnostic)
				.into_iter()
				.filter(move |(path, _)| path == target_path)
				.map(move |_| diagnostic)
		})
		.nth(index);
	let Some(diagnostic) = diagnostic else {
		return "Unable to find original wx diagnostic (it may have changed since this link was created)."
			.to_string();
	};
	// ANSI-colored, as `wx-cli` prints it: the client parses the escape codes
	// to match the user's terminal theme.
	let mut buffer = Ansi::new(Vec::new());
	if let Err(error) = term::emit_to_write_style(
		&mut buffer,
		&term::Config::default(),
		files,
		diagnostic,
	) {
		return format!("Unable to render wx diagnostic: {error}");
	}
	String::from_utf8(buffer.into_inner()).unwrap_or_default()
}
