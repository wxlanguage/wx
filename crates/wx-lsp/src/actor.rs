//! The one task that owns `ServerState`, and the commands it serves.
//!
//! Every handler reaches the state only through `Command`s on one ordered
//! channel, so events apply in the order the client sent them and a request
//! queued behind an edit always sees that edit. Nothing is skipped or merged:
//! each edit is analysed before the next command is looked at.

use std::collections::HashSet;
use std::path::PathBuf;

use tokio::sync::{mpsc, oneshot};
use tower_lsp_server::Client;
use tower_lsp_server::ls_types::{
	CompletionParams, CompletionResponse, Diagnostic, DocumentFormattingParams,
	GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverParams, Location,
	PrepareRenameResponse, ReferenceParams, RenameParams, SemanticTokensParams,
	SemanticTokensRangeParams, SemanticTokensRangeResult, SemanticTokensResult,
	SignatureHelp, SignatureHelpParams, TextDocumentPositionParams, TextEdit,
	Uri, WorkspaceEdit,
};

use crate::convert::path_to_file_uri;
use crate::documents::OpenDocument;
use crate::state::{
	ClientConfig, ServerState, compute_active_refresh, compute_refresh,
	refresh_project_manifest,
};
use crate::trace::{Trace, flush_logs};
use crate::{completion, rename, requests, signature_help};

pub(crate) enum Command {
	Initialize(ClientConfig),
	DidChangeWatchedFiles(Vec<PathBuf>),
	DidOpen {
		path: PathBuf,
		text: String,
		version: i32,
	},
	DidChange {
		path: PathBuf,
		text: String,
		version: i32,
	},
	DidClose {
		path: PathBuf,
	},
	GotoDefinition(
		GotoDefinitionParams,
		oneshot::Sender<Option<GotoDefinitionResponse>>,
	),
	Hover(HoverParams, oneshot::Sender<Option<Hover>>),
	Completion(
		CompletionParams,
		oneshot::Sender<Option<CompletionResponse>>,
	),
	SignatureHelp(SignatureHelpParams, oneshot::Sender<Option<SignatureHelp>>),
	References(ReferenceParams, oneshot::Sender<Option<Vec<Location>>>),
	PrepareRename(
		TextDocumentPositionParams,
		oneshot::Sender<Result<Option<PrepareRenameResponse>, String>>,
	),
	Rename(
		RenameParams,
		oneshot::Sender<Result<Option<WorkspaceEdit>, String>>,
	),
	SemanticTokensFull(
		SemanticTokensParams,
		oneshot::Sender<Option<SemanticTokensResult>>,
	),
	SemanticTokensRange(
		SemanticTokensRangeParams,
		oneshot::Sender<Option<SemanticTokensRangeResult>>,
	),
	Formatting(
		DocumentFormattingParams,
		oneshot::Sender<Option<Vec<TextEdit>>>,
	),
	FullDiagnostic(Uri, usize, oneshot::Sender<String>),
}

/// Cheap-to-clone handle to the actor task.
#[derive(Clone)]
pub(crate) struct StateHandle(mpsc::UnboundedSender<Command>);

impl StateHandle {
	pub(crate) fn spawn(client: Client) -> Self {
		let (tx, rx) = mpsc::unbounded_channel();
		crate::task::spawn(run_actor(rx, client));
		StateHandle(tx)
	}

	/// Enqueues a state-mutating command without waiting for it. Never
	/// blocks: notification handlers must return to the client immediately.
	pub(crate) fn notify(&self, command: Command) {
		// The receiver only goes away if the actor panicked, and then there
		// is nothing a notification handler could do about it.
		let _ = self.0.send(command);
	}

	/// Enqueues a query built from a fresh reply channel and awaits the
	/// reply. `None` only if the actor is gone.
	pub(crate) async fn query<T>(
		&self,
		build: impl FnOnce(oneshot::Sender<T>) -> Command,
	) -> Option<T> {
		let (tx, rx) = oneshot::channel();
		self.0.send(build(tx)).ok()?;
		rx.await.ok()
	}
}

async fn run_actor(mut rx: mpsc::UnboundedReceiver<Command>, client: Client) {
	let mut state = ServerState::default();
	while let Some(command) = rx.recv().await {
		handle_command(command, &mut state, &client).await;
	}
}

pub(crate) async fn handle_command(
	command: Command,
	state: &mut ServerState,
	client: &Client,
) {
	match command {
		Command::Initialize(client) => {
			state.client = client;
		}
		Command::DidChangeWatchedFiles(paths) => {
			// A disk event for a file the editor has open carries no
			// information: the overlay answers from the buffer whatever the
			// disk says, so the rebuild would recompute what `DidChange`
			// already produced. Dropping those keeps a plain save from
			// re-running the whole check.
			let paths: HashSet<_> = paths
				.into_iter()
				.filter(|path| !state.open_documents.contains_key(path))
				.collect();
			if paths.is_empty() {
				return;
			}
			let mut logs = Vec::new();
			let mut publications = Vec::new();
			for path in &paths {
				publications.extend(refresh_project_manifest(state, path));
			}
			publications.extend(compute_active_refresh(
				state,
				paths.into_iter().collect(),
				&mut logs,
			));
			flush_logs(client, logs).await;
			publish(client, state, publications).await;
			refresh_semantic_tokens(client, state);
		}
		Command::DidOpen {
			path,
			text,
			version,
		}
		| Command::DidChange {
			path,
			text,
			version,
		} => {
			state
				.open_documents
				.insert(path.clone(), OpenDocument { text, version });
			let mut logs = Vec::new();
			let publications = compute_refresh(state, &path, &mut logs);
			flush_logs(client, logs).await;
			publish(client, state, publications).await;
			refresh_semantic_tokens(client, state);
		}
		Command::DidClose { path } => {
			state.open_documents.remove(&path);
			let mut logs = Vec::new();
			let publications = compute_refresh(state, &path, &mut logs);
			flush_logs(client, logs).await;
			publish(client, state, publications).await;
			refresh_semantic_tokens(client, state);
		}
		Command::GotoDefinition(params, reply) => {
			let _ = reply.send(requests::goto_definition(state, &params));
		}
		Command::Hover(params, reply) => {
			let _ = reply.send(requests::hover(state, &params));
		}
		Command::Completion(params, reply) => {
			let _ = reply.send(completion::completion(state, &params));
		}
		Command::SignatureHelp(params, reply) => {
			let _ = reply.send(signature_help::signature_help(state, &params));
		}
		Command::References(params, reply) => {
			let _ = reply.send(requests::references(state, &params));
		}
		Command::PrepareRename(params, reply) => {
			let _ = reply.send(rename::prepare(state, &params));
		}
		Command::Rename(params, reply) => {
			let _ = reply.send(rename::rename(state, &params));
		}
		Command::SemanticTokensFull(params, reply) => {
			let _ = reply.send(requests::semantic_tokens_full(state, &params));
		}
		Command::SemanticTokensRange(params, reply) => {
			let _ = reply.send(requests::semantic_tokens_range(state, &params));
		}
		Command::Formatting(params, reply) => {
			let mut trace = Trace::new(PathBuf::from(
				params.text_document.uri.path().as_str(),
			));
			let edits =
				requests::format(state, &params.text_document.uri, &mut trace);
			flush_logs(client, vec![trace.finish("format")]).await;
			let _ = reply.send(edits);
		}
		Command::FullDiagnostic(uri, index, reply) => {
			let _ = reply
				.send(requests::render_full_diagnostic(state, &uri, index));
		}
	}
}

/// Asks the client to re-request the semantic tokens of every open file,
/// after a rebuild: an edit to one file can change what names in another
/// mean, and the client asks again on its own only for the edited one.
/// Spawned, so the actor does not wait for the client's answer.
fn refresh_semantic_tokens(client: &Client, state: &ServerState) {
	if state.client.semantic_tokens_refresh {
		let client = client.clone();
		crate::task::spawn(async move {
			let _ = client.semantic_tokens_refresh().await;
		});
	}
}

/// Publishes each file's diagnostics, against the version of its open buffer
/// when it has one, so the client can discard a result for text it has since
/// replaced.
async fn publish(
	client: &Client,
	state: &ServerState,
	publications: Vec<(PathBuf, Vec<Diagnostic>)>,
) {
	for (path, diagnostics) in publications {
		if let Some(uri) = path_to_file_uri(&path) {
			let version = state
				.open_documents
				.get(&path)
				.map(|document| document.version);
			client.publish_diagnostics(uri, diagnostics, version).await;
		}
	}
}
