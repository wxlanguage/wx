//! The protocol surface: capabilities, notifications and requests, each
//! forwarded to the state actor.

use std::str::FromStr;
use std::sync::atomic::{AtomicBool, Ordering};

use tower_lsp_server::jsonrpc::{Error as JsonRpcError, Result};
use tower_lsp_server::ls_types::{
	DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
	DidChangeWatchedFilesRegistrationOptions, DidCloseTextDocumentParams,
	DidOpenTextDocumentParams, DocumentFormattingParams, FileSystemWatcher,
	GlobPattern, GotoDefinitionParams, GotoDefinitionResponse, Hover,
	HoverParams, HoverProviderCapability, InitializeParams, InitializeResult,
	InitializedParams, Location, MessageType, OneOf, PrepareRenameResponse,
	ReferenceParams, Registration, RenameOptions, RenameParams,
	SemanticTokensFullOptions, SemanticTokensOptions, SemanticTokensParams,
	SemanticTokensRangeParams, SemanticTokensRangeResult, SemanticTokensResult,
	SemanticTokensServerCapabilities, ServerCapabilities,
	TextDocumentPositionParams, TextDocumentSyncCapability,
	TextDocumentSyncKind, TextDocumentSyncOptions, TextEdit, Uri,
	WorkspaceEdit,
};
use tower_lsp_server::{Client, LanguageServer, LspService};
use wx_compiler::vfs::{AbsolutePath, StdlibFileSource};

use crate::actor::{Command, StateHandle};
use crate::convert::uri_to_path;

#[derive(serde::Deserialize)]
struct VirtualFileContentParams {
	uri: String,
}

#[derive(serde::Deserialize)]
struct FullDiagnosticParams {
	uri: String,
	index: usize,
}

pub struct Backend {
	pub(crate) client: Client,
	state: StateHandle,
	/// Whether the client accepts `client/registerCapability`, recorded from
	/// `initialize` for `initialized` to act on. An `AtomicBool` because both
	/// handlers take `&self` and one flag written once needs no lock.
	supports_dynamic_registration: AtomicBool,
}

/// The files a change to which can invalidate an analysis: sources, and the
/// `wx.json` manifests that decide which sources belong to which package and
/// how they are formatted.
///
/// Registered with the client from `initialized` rather than declared by
/// each editor's own client code. Declaring them here is what makes an
/// editor with no file-watching API of its own (Zed, whose extensions can
/// only supply a server command) see manifest and off-buffer source edits
/// at all — and it keeps every editor watching exactly the same set instead
/// of each maintaining its own copy of this list.
const WATCHED_GLOBS: &[&str] = &["**/*.wx", "**/wx.json"];

impl LanguageServer for Backend {
	async fn initialize(
		&self,
		params: InitializeParams,
	) -> Result<InitializeResult> {
		self.client
			.log_message(MessageType::LOG, "initializing...")
			.await;
		let workspace_folders = params
			.workspace_folders
			.iter()
			.flatten()
			.filter_map(|folder| uri_to_path(&folder.uri))
			.collect();
		self.state
			.notify(Command::SetWorkspaceFolders(workspace_folders));
		self.state.notify(Command::SetSemanticTokensRefresh(
			params
				.capabilities
				.workspace
				.as_ref()
				.and_then(|workspace| workspace.semantic_tokens.as_ref())
				.and_then(|tokens| tokens.refresh_support)
				.unwrap_or(false),
		));
		self.supports_dynamic_registration.store(
			params
				.capabilities
				.workspace
				.as_ref()
				.and_then(|workspace| {
					workspace.did_change_watched_files.as_ref()
				})
				.and_then(|watched_files| watched_files.dynamic_registration)
				.unwrap_or(false),
			Ordering::Relaxed,
		);
		// Only what is connected to the new checker is advertised.
		Ok(InitializeResult {
			capabilities: ServerCapabilities {
				text_document_sync: Some(TextDocumentSyncCapability::Options(
					TextDocumentSyncOptions {
						open_close: Some(true),
						change: Some(TextDocumentSyncKind::FULL),
						..Default::default()
					},
				)),
				hover_provider: Some(HoverProviderCapability::Simple(true)),
				definition_provider: Some(OneOf::Left(true)),
				references_provider: Some(OneOf::Left(true)),
				rename_provider: Some(OneOf::Right(RenameOptions {
					prepare_provider: Some(true),
					work_done_progress_options: Default::default(),
				})),
				document_formatting_provider: Some(OneOf::Left(true)),
				semantic_tokens_provider: Some(
					SemanticTokensServerCapabilities::SemanticTokensOptions(
						SemanticTokensOptions {
							legend: crate::semantic_tokens::legend(),
							full: Some(SemanticTokensFullOptions::Bool(true)),
							range: Some(true),
							..Default::default()
						},
					),
				),
				..Default::default()
			},
			..Default::default()
		})
	}

	async fn initialized(&self, _: InitializedParams) {
		self.client
			.log_message(MessageType::LOG, "initialized")
			.await;
		if !self.supports_dynamic_registration.load(Ordering::Relaxed) {
			// Sources still recover on their own — every refresh re-reads
			// them from disk through `OverlayFileSource` — so the loss
			// there is promptness, not correctness. Manifests don't:
			// `parse_root` reads a `wx.json` once, on first encountering
			// its directory, and only a manifest event ever replaces it.
			// No client binds this server to JSON documents, so without
			// watched files that event never arrives and the manifest is
			// pinned for the rest of the session. Say so, since the
			// symptom is otherwise a silently stale package layout.
			self.client
				.log_message(
					MessageType::WARNING,
					"client does not support dynamic capability \
					 registration: `wx.json` changes will not be picked up, \
					 and source changes made outside the editor will only \
					 apply on the next edit",
				)
				.await;
			return;
		}
		let options = DidChangeWatchedFilesRegistrationOptions {
			watchers: WATCHED_GLOBS
				.iter()
				.map(|glob| FileSystemWatcher {
					glob_pattern: GlobPattern::String((*glob).to_string()),
					// `None` is create | change | delete, all three of
					// which move a file in or out of a package.
					kind: None,
				})
				.collect(),
		};
		let registration = Registration {
			id: "wx-watched-files".to_string(),
			method: "workspace/didChangeWatchedFiles".to_string(),
			register_options: Some(
				serde_json::to_value(options)
					.expect("watcher globs are plain strings"),
			),
		};
		if let Err(error) =
			self.client.register_capability(vec![registration]).await
		{
			self.client
				.log_message(
					MessageType::WARNING,
					format!("registering file watchers failed: {error}"),
				)
				.await;
		}
	}

	async fn shutdown(&self) -> Result<()> {
		Ok(())
	}

	async fn did_open(&self, params: DidOpenTextDocumentParams) {
		let Some(path) = uri_to_path(&params.text_document.uri) else {
			return;
		};
		self.state.notify(Command::DidOpen {
			path,
			text: params.text_document.text,
			version: params.text_document.version,
		});
	}

	async fn did_change(&self, params: DidChangeTextDocumentParams) {
		let Some(path) = uri_to_path(&params.text_document.uri) else {
			return;
		};
		// Full-document sync: the last change is the whole text.
		let Some(change) = params.content_changes.into_iter().last() else {
			return;
		};
		self.state.notify(Command::DidChange {
			path,
			text: change.text,
			version: params.text_document.version,
		});
	}

	async fn did_change_watched_files(
		&self,
		params: DidChangeWatchedFilesParams,
	) {
		self.state.notify(Command::DidChangeWatchedFiles(
			params
				.changes
				.into_iter()
				.filter_map(|event| uri_to_path(&event.uri))
				// Re-checked rather than trusted from `WATCHED_GLOBS`: a
				// client is free to deliver events for anything it happens
				// to watch, including watchers registered by its own
				// editor-side code, and every path here costs a rebuild.
				.filter(|path| {
					path.file_name().is_some_and(|name| name == "wx.json")
						|| path
							.extension()
							.is_some_and(|extension| extension == "wx")
				})
				.collect(),
		));
	}

	async fn did_close(&self, params: DidCloseTextDocumentParams) {
		let Some(path) = uri_to_path(&params.text_document.uri) else {
			return;
		};
		self.state.notify(Command::DidClose { path });
	}

	async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
		Ok(self
			.state
			.query(|reply| Command::Hover(params, reply))
			.await
			.flatten())
	}

	async fn goto_definition(
		&self,
		params: GotoDefinitionParams,
	) -> Result<Option<GotoDefinitionResponse>> {
		Ok(self
			.state
			.query(|reply| Command::GotoDefinition(params, reply))
			.await
			.flatten())
	}

	async fn references(
		&self,
		params: ReferenceParams,
	) -> Result<Option<Vec<Location>>> {
		Ok(self
			.state
			.query(|reply| Command::References(params, reply))
			.await
			.flatten())
	}

	async fn prepare_rename(
		&self,
		params: TextDocumentPositionParams,
	) -> Result<Option<PrepareRenameResponse>> {
		self.state
			.query(|reply| Command::PrepareRename(params, reply))
			.await
			.map_or(Ok(None), |answer| answer.map_err(request_failed))
	}

	async fn rename(
		&self,
		params: RenameParams,
	) -> Result<Option<WorkspaceEdit>> {
		self.state
			.query(|reply| Command::Rename(params, reply))
			.await
			.map_or(Ok(None), |answer| answer.map_err(request_failed))
	}

	async fn semantic_tokens_full(
		&self,
		params: SemanticTokensParams,
	) -> Result<Option<SemanticTokensResult>> {
		Ok(self
			.state
			.query(|reply| Command::SemanticTokensFull(params, reply))
			.await
			.flatten())
	}

	async fn semantic_tokens_range(
		&self,
		params: SemanticTokensRangeParams,
	) -> Result<Option<SemanticTokensRangeResult>> {
		Ok(self
			.state
			.query(|reply| Command::SemanticTokensRange(params, reply))
			.await
			.flatten())
	}

	async fn formatting(
		&self,
		params: DocumentFormattingParams,
	) -> Result<Option<Vec<TextEdit>>> {
		Ok(self
			.state
			.query(|reply| Command::Formatting(params, reply))
			.await
			.flatten())
	}
}

impl Backend {
	async fn virtual_file_content(
		&self,
		params: VirtualFileContentParams,
	) -> Result<String> {
		let filename =
			params.uri.strip_prefix("wx://std").ok_or_else(|| {
				JsonRpcError::invalid_params(format!(
					"not a wxstd URI: {}",
					params.uri
				))
			})?;
		// Keyed exactly as the stdlib package's own module paths, so any file
		// the stdlib grows is servable here without touching this match.
		match StdlibFileSource::source(&AbsolutePath::new(filename)) {
			Some(source) => Ok(source.to_string()),
			None => Err(JsonRpcError::invalid_params(format!(
				"unknown stdlib file: {filename}"
			))),
		}
	}

	/// Re-renders one diagnostic's full, source-annotated text on demand;
	/// see `notes/lsp-full-diagnostic-view-plan.md`.
	async fn full_diagnostic(
		&self,
		params: FullDiagnosticParams,
	) -> Result<String> {
		let uri = Uri::from_str(&params.uri).map_err(|_| {
			JsonRpcError::invalid_params(format!("bad uri: {}", params.uri))
		})?;
		Ok(self
			.state
			.query(|reply| Command::FullDiagnostic(uri, params.index, reply))
			.await
			.unwrap_or_else(|| {
				"wx-lsp internal error: state actor unavailable".to_string()
			}))
	}
}

/// A request the server understood and refuses, with the reason shown to
/// the user: LSP's `RequestFailed`.
fn request_failed(message: String) -> JsonRpcError {
	JsonRpcError {
		code: tower_lsp_server::jsonrpc::ErrorCode::ServerError(-32803),
		message: message.into(),
		data: None,
	}
}

/// Builds the `Backend`/`LspService` pair. The transport is up to the
/// caller — the native binary serves it over stdio, `wx-lsp-wasm` bridges it
/// over `postMessage` — but the server construction itself doesn't change.
pub fn build_service() -> (LspService<Backend>, tower_lsp_server::ClientSocket)
{
	LspService::build(|client| Backend {
		state: StateHandle::spawn(client.clone()),
		client,
		supports_dynamic_registration: AtomicBool::new(false),
	})
	.custom_method("wx/virtualFileContent", Backend::virtual_file_content)
	.custom_method("wx/fullDiagnostic", Backend::full_diagnostic)
	.finish()
}

/// Serves the language server over the given transport until the client
/// disconnects. Requires a Tokio runtime to already be running (the
/// caller's responsibility, e.g. `wx-cli`'s `lsp` subcommand).
///
/// Generic over the reader/writer rather than hardcoding
/// `tokio::io::stdin()`/`stdout()`, so the caller owns constructing them —
/// this crate no longer needs Tokio's `io-std` feature just for itself.
///
/// Native-only (`#[cfg]`ed out for `wasm32`, this crate's other embedder via
/// `wx-lsp-wasm`), not just unused there: `tower_lsp_server::Server`'s
/// `AsyncRead`/`AsyncWrite` bounds resolve to a *different* trait depending
/// on which of its features is active — `tokio::io`'s under
/// `runtime-tokio` (native), `futures::io`'s under `runtime-agnostic`
/// (wasm32, see `transport.rs` in that crate). A single generic signature
/// can satisfy one or the other, not both, so this can only compile for the
/// target whose trait it's actually bounded by.
#[cfg(not(target_arch = "wasm32"))]
pub async fn run_stdio<I, O>(stdin: I, stdout: O)
where
	I: tokio::io::AsyncRead + Unpin,
	O: tokio::io::AsyncWrite,
{
	let (service, socket) = build_service();
	tower_lsp_server::Server::new(stdin, stdout, socket)
		.serve(service)
		.await;
}
