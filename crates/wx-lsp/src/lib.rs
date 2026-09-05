use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, Ordering};

use codespan_reporting::diagnostic::{
	Diagnostic as CodeDiagnostic, Label, LabelStyle, Severity,
};
use codespan_reporting::files::Files as _;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::Ansi;
use tokio::sync::{mpsc, oneshot};
use tower_lsp_server::jsonrpc::{Error as JsonRpcError, Result};
use tower_lsp_server::ls_types::{
	CompletionOptions, CompletionParams, CompletionResponse, Diagnostic,
	DiagnosticRelatedInformation, DiagnosticSeverity, DiagnosticTag,
	DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
	DidChangeWatchedFilesRegistrationOptions, DidCloseTextDocumentParams,
	DidOpenTextDocumentParams, DocumentFormattingParams, FileSystemWatcher,
	GlobPattern, GotoDefinitionParams, GotoDefinitionResponse, Hover,
	HoverContents, HoverParams, HoverProviderCapability,
	ImplementationProviderCapability, InitializeParams, InitializeResult,
	InitializedParams, Location, MarkupContent, MarkupKind, MessageType,
	NumberOrString, OneOf, ParameterInformation, ParameterLabel, Position,
	Range, ReferenceParams, Registration, RenameParams, SemanticToken,
	SemanticTokenType, SemanticTokensFullOptions, SemanticTokensLegend,
	SemanticTokensOptions, SemanticTokensParams, SemanticTokensResult,
	SemanticTokensServerCapabilities, ServerCapabilities, SignatureHelp,
	SignatureHelpOptions, SignatureHelpParams, SignatureInformation,
	TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
	TextEdit, Uri, WorkspaceEdit,
};
use tower_lsp_server::{Client, LanguageServer, LspService};
use wx_compiler::ast;
use wx_compiler::ast::TextSpan;
use wx_compiler::tir::{
	ImplTarget, ItemAttribute, ModuleDeclarationKind, SourceSpan, TIR,
	TypeParamInfo, TypeParamOwner,
};
use wx_compiler::vfs::{
	self, AbsolutePath, FileId, FileSource, NativeFileSource,
};

mod completion;
mod symbol_index;
pub mod task;
use symbol_index::{ImplRef, SymbolIndex, SymbolKind, build_symbol_index};

/// Ordered list of token types declared in the semantic tokens legend.
#[repr(u32)]
enum TokenType {
	Function = 0,
	Variable = 1,
	Enum = 2,
	Struct = 3,
	Namespace = 4,
	Parameter = 5,
	EnumMember = 6,
	Interface = 7,
	TypeParameter = 8,
	Type = 9,
}

/// The index of each entry is what gets emitted as `token_type` in the data.
const SEMANTIC_TOKEN_TYPES: &[SemanticTokenType] = &[
	SemanticTokenType::FUNCTION,    // TokenType::Function
	SemanticTokenType::VARIABLE,    // TokenType::Variable
	SemanticTokenType::ENUM,        // TokenType::Enum
	SemanticTokenType::STRUCT,      // TokenType::Struct
	SemanticTokenType::NAMESPACE,   // TokenType::Namespace
	SemanticTokenType::PARAMETER,   // TokenType::Parameter
	SemanticTokenType::ENUM_MEMBER, // TokenType::EnumMember
	SemanticTokenType::INTERFACE,   // TokenType::Interface
	SemanticTokenType::TYPE_PARAMETER, // TokenType::TypeParameter
	SemanticTokenType::TYPE,        // TokenType::Type
];

#[derive(serde::Deserialize)]
struct VirtualFileContentParams {
	uri: String,
}

#[derive(serde::Deserialize)]
struct FullDiagnosticParams {
	uri: String,
	index: usize,
}

/// Flushes buffered log lines (collected via `logs.push(...)` in plain,
/// `Client`-less helpers like `analyze_root`/`compile_root`/`parse_root`) to
/// the client. Not raw `eprintln!`: `vscode-languageclient` pipes a server's
/// stderr straight into `outputChannel.error(...)`, so every line written
/// there shows up tagged `[error]` regardless of content — `window/logMessage`
/// is the channel that actually carries a real severity.
async fn flush_logs(client: &Client, logs: Vec<String>) {
	for line in logs {
		client.log_message(MessageType::LOG, line).await;
	}
}

/// Accumulates named, timed steps for one logical operation — e.g. parsing
/// a package as part of typechecking it, or parsing a package as part of
/// formatting one of its files — so the whole dependency chain renders as
/// one readable block instead of one independent log line per step with no
/// visible relationship between them.
struct Trace {
	/// The file that caused this trace (the one edited/opened/formatted).
	/// Its package root is whatever `wx.json`-bearing ancestor it shares a
	/// path prefix with — no need to store that separately.
	path: PathBuf,
	steps: Vec<(&'static str, web_time::Duration)>,
}

impl Trace {
	fn new(path: PathBuf) -> Self {
		Self {
			path,
			steps: Vec::new(),
		}
	}

	/// Times `f`, records its duration under `label`, and returns its
	/// result unchanged — so callers thread this through exactly like the
	/// bare `Instant::now()` calls it replaces, `?` included.
	fn step<T>(&mut self, label: &'static str, f: impl FnOnce() -> T) -> T {
		let start = web_time::Instant::now();
		let result = f();
		self.steps.push((label, start.elapsed()));
		result
	}

	/// Renders the causing file and every recorded step as an indented
	/// tree under `operation`, with the steps' total on the heading line
	/// itself (it's a summary of the block, not a sibling step that ran).
	/// Every line past the heading is indented two spaces so it reads as
	/// part of this one log entry rather than the surrounding log list —
	/// VS Code's Output panel only timestamp-prefixes a message's first
	/// line, so the rest need their own visual cue to stay grouped:
	/// ```text
	/// typecheck — 1.664473ms
	///   file: "/examples/pow/main.wx"
	///   ├─ parse:      772.593µs
	///   └─ typecheck:  891.88µs
	/// ```
	fn finish(&self, operation: &str) -> String {
		let mut out = if self.steps.is_empty() {
			operation.to_string()
		} else {
			let total: web_time::Duration =
				self.steps.iter().map(|(_, d)| *d).sum();
			format!("{operation} — {total:?}")
		};
		out.push_str(&format!("\n  file: {:?}", self.path));
		let width = self
			.steps
			.iter()
			.map(|(label, _)| label.len())
			.max()
			.unwrap_or(0)
			+ 1;
		let last = self.steps.len().saturating_sub(1);
		for (i, (label, duration)) in self.steps.iter().enumerate() {
			let branch = if i == last { "└─" } else { "├─" };
			let label_colon = format!("{label}:");
			out.push_str(&format!(
				"\n  {branch} {label_colon:<width$}  {duration:?}"
			));
		}
		out
	}
}

#[derive(Clone)]
struct OpenDocument {
	text: String,
}

#[derive(Default)]
struct ServerState {
	open_documents: HashMap<PathBuf, OpenDocument>,
	workspace_folders: Vec<PathBuf>,
	/// Compiled artifacts per package root — the one source of truth. Which
	/// `CompiledRoot`/`FileId` a given URI belongs to is computed on demand
	/// by `resolve_uri` rather than tracked in a second index, since keeping
	/// a hand-maintained reverse map in sync with this one is exactly the
	/// kind of bookkeeping that silently drifts.
	///
	/// Written by `analyze_root`, which rebuilds unconditionally rather than
	/// checking whether the previous entry is still valid. There is no
	/// staleness check because every mutation already goes through a
	/// notification that rebuilds — a validity predicate would re-derive, per
	/// request, what each mutation site already knew. Invalidation belongs on
	/// the event, not on the read. Manifest changes on disk are pushed by
	/// the client file watcher.
	/// Source changes on disk use the same refresh path as buffer edits.
	cached: HashMap<PathBuf, CompiledRoot>,
	/// Persistent manifest and publication state, independent of compiled
	/// artifacts. Dependency-only entries do not become active analysis roots.
	projects: HashMap<PathBuf, ProjectState>,
	/// file -> the root `discover_package_root` returned for it, as of the
	/// last refresh batch that re-resolved its ownership. Kept
	/// separate from project publication tracking — that answers "which files
	/// does root R currently reach" (many-to-many, since a dependency file
	/// is reachable from every root that depends on it) — this one answers
	/// "what is file F's own project" (one answer per file, never derived
	/// from the other map). Refresh batches re-resolve tracked files and
	/// open buffers so manifest creation/deletion updates their ownership.
	own_root: HashMap<PathBuf, PathBuf>,
}

/// Source edits retain this state; manifest events replace the parse result.
/// Invalid manifests remain project boundaries. Removing a manifest from both
/// disk and the editor removes the project after its publications are cleared.
struct ProjectState {
	manifest: ManifestState,
	published_files: HashSet<PathBuf>,
}

enum ManifestState {
	Parsed(vfs::PackageManifest),
	Invalid,
}

struct AnalysisResult {
	diagnostics_by_file: HashMap<PathBuf, Vec<Diagnostic>>,
	owned_files: HashSet<PathBuf>,
}

struct CompiledRoot {
	graph: vfs::CompilationUnit,
	tir: TIR,
	symbol_index: SymbolIndex,
}

struct OverlayFileSource<'a> {
	open_documents: &'a HashMap<PathBuf, OpenDocument>,
	native: NativeFileSource,
}

impl<'a> OverlayFileSource<'a> {
	fn new(open_documents: &'a HashMap<PathBuf, OpenDocument>) -> Self {
		Self {
			open_documents,
			native: NativeFileSource,
		}
	}
}

impl FileSource for OverlayFileSource<'_> {
	fn read_to_string(
		&self,
		path: &AbsolutePath,
	) -> std::result::Result<String, ()> {
		if let Some(doc) = self.open_documents.get(Path::new(path.as_str())) {
			return Ok(doc.text.clone());
		}
		self.native.read_to_string(path)
	}

	fn exists(&self, path: &AbsolutePath) -> bool {
		self.open_documents.contains_key(Path::new(path.as_str()))
			|| self.native.exists(path)
	}

	fn origin(&self) -> vfs::FileOrigin {
		vfs::FileOrigin::Local
	}
}

/// One state-mutating or state-reading operation dispatched to the single
/// task that owns `ServerState` (see [`run_actor`]). Query variants carry a
/// `oneshot::Sender` for the reply; notification variants carry none, since
/// their handlers return to the client immediately without waiting for the
/// corresponding recompute/publish to happen.
enum Command {
	SetWorkspaceFolders(Vec<PathBuf>),
	DidChangeWatchedFiles(Vec<PathBuf>),
	DidOpen {
		path: PathBuf,
		text: String,
	},
	DidChange {
		path: PathBuf,
		text: String,
	},
	DidClose {
		path: PathBuf,
	},
	Hover(HoverParams, oneshot::Sender<Option<Hover>>),
	GotoDefinition(
		GotoDefinitionParams,
		oneshot::Sender<Option<GotoDefinitionResponse>>,
	),
	// `GotoImplementationParams`/`GotoImplementationResponse` are just type
	// aliases for `GotoDefinitionParams`/`GotoDefinitionResponse` in
	// `lsp_types` (see `lsp_types::request::GotoImplementation`) — reusing
	// the same types here instead of importing the aliases.
	GotoImplementation(
		GotoDefinitionParams,
		oneshot::Sender<Option<GotoDefinitionResponse>>,
	),
	References(ReferenceParams, oneshot::Sender<Option<Vec<Location>>>),
	Rename(RenameParams, oneshot::Sender<Option<WorkspaceEdit>>),
	Formatting(
		DocumentFormattingParams,
		oneshot::Sender<Option<Vec<TextEdit>>>,
	),
	SignatureHelp(SignatureHelpParams, oneshot::Sender<Option<SignatureHelp>>),
	SemanticTokensFull(
		SemanticTokensParams,
		oneshot::Sender<Option<SemanticTokensResult>>,
	),
	Completion(
		CompletionParams,
		oneshot::Sender<Option<CompletionResponse>>,
	),
	FullDiagnostic(Uri, usize, oneshot::Sender<String>),
}

/// Cheap-to-clone handle to the actor task that owns `ServerState`. This
/// replaces a shared `Arc<Mutex<ServerState>>`: instead of every LSP handler
/// locking the same state and racing over who gets the lock next (see the
/// note on `run_actor`), every handler just enqueues a `Command` and, for
/// queries, awaits its reply — ordering is then whatever order `Command`s
/// land in the channel, which is a single, unambiguous FIFO queue rather than
/// a lock's acquisition order.
#[derive(Clone)]
struct StateHandle(mpsc::UnboundedSender<Command>);

impl StateHandle {
	fn spawn(client: Client) -> Self {
		let (tx, rx) = mpsc::unbounded_channel();
		task::spawn(run_actor(rx, client));
		StateHandle(tx)
	}

	/// Enqueues a state-mutating command without waiting for it to be
	/// processed. Never blocks: notification handlers (`did_open`,
	/// `did_change`, ...) must return to the client immediately.
	fn notify(&self, cmd: Command) {
		// The receiver only goes away if the actor task itself panicked, in
		// which case there's nothing a notification handler could do about
		// it — silently drop rather than panicking the caller too.
		let _ = self.0.send(cmd);
	}

	/// Enqueues a query command built from a fresh reply channel, then awaits
	/// the reply. `None` only if the actor task is gone (panicked).
	async fn query<T>(
		&self,
		build: impl FnOnce(oneshot::Sender<T>) -> Command,
	) -> Option<T> {
		let (tx, rx) = oneshot::channel();
		self.0.send(build(tx)).ok()?;
		rx.await.ok()
	}
}

/// The single task that owns `ServerState` for the lifetime of the server —
/// no other code ever touches it. Every LSP handler reaches it only through
/// `Command`s sent over an ordered channel, so document edits are always
/// applied in the exact order they were enqueued, with no possibility of two
/// concurrent handlers racing to write `open_documents` out of order (the
/// hazard a shared `Arc<Mutex<ServerState>>` had: `tower-lsp-server` runs
/// notification futures concurrently, so two overlapping `did_change` calls
/// racing to *acquire* the lock could apply their edits in either order,
/// independent of which edit the client actually sent first).
async fn run_actor(mut rx: mpsc::UnboundedReceiver<Command>, client: Client) {
	let mut state = ServerState::default();
	// Commands already pulled out of `rx` but not yet processed — draining
	// into this lets one iteration look ahead at what's already queued (see
	// the `DidChange` coalescing below) without losing anything.
	let mut pending: VecDeque<Command> = VecDeque::new();
	loop {
		let cmd = match pending.pop_front() {
			Some(cmd) => cmd,
			None => match rx.recv().await {
				Some(cmd) => cmd,
				None => return,
			},
		};
		while let Ok(cmd) = rx.try_recv() {
			pending.push_back(cmd);
		}
		handle_command(cmd, &pending, &mut state, &client).await;
	}
}

async fn handle_command(
	cmd: Command,
	pending: &VecDeque<Command>,
	state: &mut ServerState,
	client: &Client,
) {
	match cmd {
		Command::SetWorkspaceFolders(folders) => {
			state.workspace_folders = folders;
		}
		Command::DidChangeWatchedFiles(paths) => {
			// A disk event for a file the editor has open carries no
			// information: `OverlayFileSource` answers both `exists` and
			// `read_to_string` from `open_documents` whatever the disk
			// says, so the rebuild it would trigger recomputes a result
			// `DidChange` already produced. Dropping those is what keeps
			// a plain save from re-running the whole typecheck.
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
			publish_diagnostics(client, publications).await;
		}
		Command::DidOpen { path, text } => {
			state
				.open_documents
				.insert(path.clone(), OpenDocument { text });
			let mut logs = Vec::new();
			let publications = compute_refresh(state, &path, &mut logs);
			flush_logs(client, logs).await;
			publish_diagnostics(client, publications).await;
		}
		Command::DidChange { path, text } => {
			state
				.open_documents
				.insert(path.clone(), OpenDocument { text });
			// Ahead of the supersession gate below, and returning nothing to
			// publish by construction: `path` was just inserted into
			// `open_documents`, so the overlay reports the manifest as
			// existing and the deletion branch — the only one that produces
			// diagnostic clears — cannot be taken from here. What this call
			// is for is the state it writes, keeping `projects` level with
			// `open_documents` even for an edit whose rebuild is skipped, so
			// a `Formatting` queued behind one formats to the manifest the
			// buffer currently says rather than the last compiled one.
			let mut publications = refresh_project_manifest(state, &path);
			debug_assert!(
				publications.is_empty(),
				"a `didChange` cannot report its own document as deleted; \
				 if that changes, the `return` below drops these"
			);
			// Skip the recompute if a newer edit to this same file is
			// already waiting right behind this one — it'll trigger its own
			// recompute once it's processed, so this one would just be
			// wasted work superseded before it could ever be published.
			let superseded = pending.iter().any(
				|c| matches!(c, Command::DidChange { path: p, .. } if *p == path),
			);
			if superseded {
				return;
			}
			let mut logs = Vec::new();
			publications.extend(compute_active_refresh(
				state,
				vec![path],
				&mut logs,
			));
			flush_logs(client, logs).await;
			publish_diagnostics(client, publications).await;
		}
		Command::DidClose { path } => {
			state.open_documents.remove(&path);
			let mut logs = Vec::new();
			let publications = compute_refresh(state, &path, &mut logs);
			flush_logs(client, logs).await;
			publish_diagnostics(client, publications).await;
		}
		Command::Hover(params, reply) => {
			let result = (|| {
				let (compiled, file_id) = resolve_uri(
					state,
					&params.text_document_position_params.text_document.uri,
				)?;
				let offset = position_to_offset(
					&compiled.graph.files,
					file_id,
					params.text_document_position_params.position,
				)?;
				let info =
					compiled.symbol_index.find_at_position(file_id, offset)?;
				// The package the *hovered file* belongs to, not the
				// compilation's overall root — those only coincide when
				// hovering inside the binary's own files. A `crate`/`super`
				// reference (or any package-qualified name) hovered inside a
				// dependency like `std` needs `std`'s own package here, or
				// `namespace_name` names things from the wrong package's
				// perspective.
				let from = compiled.tir.modules.namespaces[usize::from(
					compiled.tir.modules.file_namespaces[file_id.as_usize()],
				)]
				.package;
				let text = symbol_hover_text(
					&compiled.tir,
					&compiled.graph.interner,
					&compiled.graph.packages,
					from,
					&info.kind,
				)?;
				let range = span_to_range(&compiled.graph.files, info.source)?;
				let doc = doc_comment_anchor(&compiled.tir, &info.kind)
					.and_then(|anchor| {
						let source = &compiled
							.graph
							.files
							.get(anchor.file_id)
							.ok()?
							.source;
						leading_doc_comment(source, anchor.span.start)
					});
				let value = match doc {
					Some(doc) => format!("```wx\n{text}\n```\n\n---\n\n{doc}"),
					None => format!("```wx\n{text}\n```"),
				};
				Some(Hover {
					contents: HoverContents::Markup(MarkupContent {
						kind: MarkupKind::Markdown,
						value,
					}),
					range: Some(range),
				})
			})();
			let _ = reply.send(result);
		}
		Command::GotoDefinition(params, reply) => {
			let result = (|| {
				let (compiled, file_id) = resolve_uri(
					state,
					&params.text_document_position_params.text_document.uri,
				)?;
				let offset = position_to_offset(
					&compiled.graph.files,
					file_id,
					params.text_document_position_params.position,
				)?;
				let info =
					compiled.symbol_index.find_at_position(file_id, offset)?;
				let def = compiled
					.symbol_index
					.definition_for_kind(info.kind)
					.map(|e| e.source)?;
				let uri = file_id_to_uri(&compiled.graph.files, def.file_id)?;
				let range = span_to_range(&compiled.graph.files, def)?;
				Some(GotoDefinitionResponse::Scalar(Location { uri, range }))
			})();
			let _ = reply.send(result);
		}
		Command::GotoImplementation(params, reply) => {
			let result = (|| {
				let (compiled, file_id) = resolve_uri(
					state,
					&params.text_document_position_params.text_document.uri,
				)?;
				let offset = position_to_offset(
					&compiled.graph.files,
					file_id,
					params.text_document_position_params.position,
				)?;
				let info =
					compiled.symbol_index.find_at_position(file_id, offset)?;
				let locations = implementation_locations(
					&compiled.tir,
					&compiled.symbol_index,
					info.kind,
				)
				.into_iter()
				.filter_map(|source| {
					let uri =
						file_id_to_uri(&compiled.graph.files, source.file_id)?;
					let range = span_to_range(&compiled.graph.files, source)?;
					Some(Location { uri, range })
				})
				.collect::<Vec<_>>();
				(!locations.is_empty())
					.then_some(GotoDefinitionResponse::Array(locations))
			})();
			let _ = reply.send(result);
		}
		Command::References(params, reply) => {
			let result = (|| {
				let (compiled, file_id) = resolve_uri(
					state,
					&params.text_document_position.text_document.uri,
				)?;
				let offset = position_to_offset(
					&compiled.graph.files,
					file_id,
					params.text_document_position.position,
				)?;
				let info =
					compiled.symbol_index.find_at_position(file_id, offset)?;
				let search_kinds = reference_search_kinds(
					&compiled.tir,
					&compiled.symbol_index,
					info.kind,
				);
				let locations = compiled
					.symbol_index
					.references
					.iter()
					.filter(|e| search_kinds.contains(&e.kind))
					.chain(
						params
							.context
							.include_declaration
							.then(|| {
								compiled
									.symbol_index
									.definitions
									.iter()
									.filter(|d| search_kinds.contains(&d.kind))
							})
							.into_iter()
							.flatten(),
					)
					.filter_map(|entry| {
						let uri = file_id_to_uri(
							&compiled.graph.files,
							entry.source.file_id,
						)?;
						let range =
							span_to_range(&compiled.graph.files, entry.source)?;
						Some(Location { uri, range })
					})
					.collect::<Vec<_>>();
				match locations.len() {
					0 => None,
					_ => Some(locations),
				}
			})();
			let _ = reply.send(result);
		}
		Command::Rename(params, reply) => {
			let result = (|| {
				let (compiled, file_id) = resolve_uri(
					state,
					&params.text_document_position.text_document.uri,
				)?;
				let offset = position_to_offset(
					&compiled.graph.files,
					file_id,
					params.text_document_position.position,
				)?;
				let info =
					compiled.symbol_index.find_at_position(file_id, offset)?;
				let mut changes: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
				compiled
					.symbol_index
					.references
					.iter()
					.chain(compiled.symbol_index.definitions.iter())
					.filter(|e| e.kind == info.kind)
					.filter_map(|entry| {
						let uri = file_id_to_uri(
							&compiled.graph.files,
							entry.source.file_id,
						)?;
						let range =
							span_to_range(&compiled.graph.files, entry.source)?;
						Some((uri, range))
					})
					.for_each(|(uri, range)| {
						changes.entry(uri).or_default().push(TextEdit {
							range,
							new_text: params.new_name.clone(),
						});
					});
				if changes.is_empty() {
					return None;
				}
				Some(WorkspaceEdit {
					changes: Some(changes),
					..Default::default()
				})
			})();
			let _ = reply.send(result);
		}
		Command::Formatting(params, reply) => {
			let result = async {
				let path = uri_to_path(&params.text_document.uri)?;
				let root = discover_package_root(
					&state.open_documents,
					&state.workspace_folders,
					&path,
				)?;

				// Computed synchronously so `?` can short-circuit freely on
				// any failure without skipping the trace flush below —
				// there's exactly one `.await` point for this whole
				// command (the flush itself), not one per step.
				let mut trace = Trace::new(path.clone());
				let outcome = (|| {
					// Always reparse fresh from the live buffer rather
					// than going through `cached`, which can lag
					// `open_documents`: a superseded `DidChange` stores
					// its text but skips the rebuild, so a format request
					// queued behind one would format the previous edit.
					// Parsing is cheap enough (~1ms on typical files) that
					// there's no need to cache it across calls.
					let graph = parse_root(state, &root, &mut trace).ok()?;
					let module = graph
						.packages
						.iter()
						.flat_map(|cg| cg.modules.iter())
						.find(|m| {
							Path::new(m.file_path.as_str()) == path.as_path()
						})?;
					let has_errors = module.ast.diagnostics.iter().any(|d| {
						matches!(
							d.severity,
							codespan_reporting::diagnostic::Severity::Error
								| codespan_reporting::diagnostic::Severity::Bug
						)
					});
					if has_errors {
						return None;
					}
					let file = graph.files.get(module.file_id).ok()?;
					let source = file.source.as_str();
					// The package's `wx.json`, not the editor's tab size:
					// formatting on save and running `wx format` are the
					// same operation and must produce the same bytes.
					let ManifestState::Parsed(manifest) =
						&state.projects.get(&root)?.manifest
					else {
						return None;
					};
					let config =
						wx_fmt::RendererConfig::from_manifest(manifest.format);
					let formatted = trace.step("render", || {
						wx_fmt::format(
							&module.ast,
							&graph.interner,
							source,
							config,
						)
					});
					// An already-formatted file is the common case for
					// format-on-save. Reporting no edits leaves the buffer
					// untouched, so the client never fires a `DidChange` and
					// nothing downstream re-parses or re-checks an identical
					// document.
					if formatted == source {
						return Some(Vec::new());
					}
					let end = byte_to_position(
						&graph.files,
						module.file_id,
						source.len(),
					)?;
					Some(vec![TextEdit {
						range: Range {
							start: Position::default(),
							end,
						},
						new_text: formatted,
					}])
				})();

				flush_logs(client, vec![trace.finish("format")]).await;

				outcome
			}
			.await;
			let _ = reply.send(result);
		}
		Command::SignatureHelp(params, reply) => {
			let result = (|| {
				let uri =
					&params.text_document_position_params.text_document.uri;
				let (compiled, file_id) = resolve_uri(state, uri)?;
				let position = params.text_document_position_params.position;

				let (source, offset) = resolve_source_and_offset(
					state, compiled, uri, file_id, position,
				)?;

				let call = find_active_call(source, offset)?;
				let info = compiled
					.symbol_index
					.find_at_position(file_id, call.func_name_start as u32)?;
				let SymbolKind::Function(def_id) = &info.kind else {
					return None;
				};
				let fi =
					usize::from(compiled.tir.items.function_index(*def_id)?);
				let func = &compiled.tir.items.functions[fi];
				// The function's own package, not the compilation's overall
				// root — see the matching fix in the `Hover` handler above.
				let from = compiled.tir.modules.namespaces
					[usize::from(func.namespace)]
				.package;
				let fmt = compiled.tir.formatter(
					&compiled.graph.interner,
					&compiled.graph.packages,
					from,
				);
				let interner = &compiled.graph.interner;

				let name = interner.resolve(func.name.inner).unwrap();
				let mut label = format!("fn {name}(");
				let mut param_infos: Vec<ParameterInformation> = Vec::new();
				// If the first parameter is named `self`, treat this as a
				// method: show `self` in the signature label but do not
				// include it in the interactive `parameters` list so editors
				// won't tab into it.
				let is_method = func
					.params
					.first()
					.map(|p| {
						interner
							.resolve(p.name.inner)
							.map(|s| s == "self")
							.unwrap_or(false)
					})
					.unwrap_or(false);
				let start_idx = if is_method { 1 } else { 0 };
				for (i, param) in func.params.iter().enumerate() {
					if i > 0 {
						label.push_str(", ");
					}
					let param_start = label.len() as u32;
					let pname = interner.resolve(param.name.inner).unwrap();
					label.push_str(pname);
					label.push_str(": ");
					label.push_str(&fmt.display_type(param.ty.inner).unwrap());
					let param_end = label.len() as u32;
					if i >= start_idx {
						param_infos.push(ParameterInformation {
							label: ParameterLabel::LabelOffsets([
								param_start,
								param_end,
							]),
							documentation: None,
						});
					}
				}
				label.push_str(") -> ");
				match &func.result {
					Some(r) => {
						label.push_str(&fmt.display_type(r.inner).unwrap())
					}
					None => label.push_str("()"),
				}

				Some(SignatureHelp {
					signatures: vec![SignatureInformation {
						label,
						documentation: None,
						parameters: Some(param_infos),
						active_parameter: Some(call.active_param as u32),
					}],
					active_signature: Some(0),
					active_parameter: Some(call.active_param as u32),
				})
			})();
			let _ = reply.send(result);
		}
		Command::SemanticTokensFull(params, reply) => {
			let result = (|| {
				let (compiled, file_id) =
					resolve_uri(state, &params.text_document.uri)?;
				let files = &compiled.graph.files;
				let source = files.source(file_id).ok()?;

				let mut data: Vec<SemanticToken> = Vec::new();
				let mut prev_line = 0u32;
				let mut prev_char = 0u32;

				let mut entries: Vec<&symbol_index::SpanInfo> = compiled
					.symbol_index
					.definitions
					.iter()
					.chain(compiled.symbol_index.references.iter())
					.filter(|e| e.source.file_id == file_id)
					.collect();
				entries.sort_by_key(|e| e.source.span.start);

				for entry in entries {
					let Some(token_type) =
						symbol_kind_to_token_type(entry.kind)
					else {
						continue;
					};
					// Operator dispatch (`+`, `-`, `+=`, ...) pushes a
					// go-to-definition access at the *operator's own span*
					// onto the resolved trait method (`resolve_trait_method`
					// et al. in tir/builder.rs) — correct for go-to-def, but
					// it means these spans land in `references` too, tagged
					// with the callee's own `SymbolKind::Function`, which
					// would otherwise paint `+`/`-` the same color as a real
					// function call. An operator's span is never a valid
					// identifier (starts with a symbol character, never a
					// letter/underscore), so filtering on that excludes them
					// from semantic highlighting without touching how
					// go-to-definition/find-references (which read the same
					// `references` list) behave.
					let span_text = source.get(
						entry.source.span.start as usize
							..entry.source.span.end as usize,
					);
					if !span_text.is_some_and(|t| {
						t.starts_with(|c: char| c.is_alphabetic() || c == '_')
					}) {
						continue;
					}
					// `crate`/`super` resolve to an ordinary
					// `SymbolKind::Namespace` — the same variant a real
					// module name like `math` gets, so there's no dedicated
					// kind `symbol_kind_to_token_type` can exclude below the
					// way it already does for `self`/`Self`. Hardcoded text
					// check for now, reusing `span_text` already computed
					// above for the operator filter — TODO: revisit with a
					// cheaper, kind-based exclusion if this ever shows up on
					// a profile.
					if matches!(span_text, Some("crate" | "super")) {
						continue;
					}
					let Some(pos) = byte_to_position(
						files,
						file_id,
						entry.source.span.start as usize,
					) else {
						continue;
					};
					let length =
						entry.source.span.end - entry.source.span.start;
					let delta_line = pos.line - prev_line;
					let delta_start = if delta_line == 0 {
						pos.character - prev_char
					} else {
						pos.character
					};
					data.push(SemanticToken {
						delta_line,
						delta_start,
						length,
						token_type: token_type as u32,
						token_modifiers_bitset: 0,
					});
					prev_line = pos.line;
					prev_char = pos.character;
				}

				Some(SemanticTokensResult::Tokens(
					tower_lsp_server::ls_types::SemanticTokens {
						result_id: None,
						data,
					},
				))
			})();
			let _ = reply.send(result);
		}
		Command::Completion(params, reply) => {
			let result = async {
				let uri = &params.text_document_position.text_document.uri;
				let (compiled, file_id) = resolve_uri(state, uri)?;
				let position = params.text_document_position.position;

				let (source, offset) = resolve_source_and_offset(
					state, compiled, uri, file_id, position,
				)?;
				let completion_start = web_time::Instant::now();
				let items = completion::completion_items(
					&compiled.tir,
					&compiled.graph.interner,
					&compiled.graph.packages,
					&compiled.symbol_index,
					file_id,
					source,
					offset,
				);
				client
					.log_message(
						MessageType::LOG,
						format!(
							"completion took {:?}",
							completion_start.elapsed()
						),
					)
					.await;
				Some(CompletionResponse::Array(items))
			}
			.await;
			let _ = reply.send(result);
		}
		Command::FullDiagnostic(uri, index, reply) => {
			let _ = reply.send(render_full_diagnostic(state, &uri, index));
		}
	}
}

pub struct Backend {
	client: Client,
	state: StateHandle,
	/// Whether the client accepts `client/registerCapability`, recorded from
	/// `initialize` for `initialized` to act on.
	///
	/// An `AtomicBool` rather than a plain field because both handlers take
	/// `&self` — and a `Mutex` would be overkill for one flag written once,
	/// before the only read the protocol allows to follow it.
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
				completion_provider: Some(CompletionOptions {
					// Single characters only: LSP has no two-character
					// trigger, and a client matches the one character it
					// just inserted, so a `"::"` entry here would never
					// fire at all. `:` is declared to reach `::`, and
					// `classify_context` decides what each colon actually
					// meant — a decision made from the buffer, not from
					// how the request was triggered, so an explicit invoke
					// and a typed colon behave alike.
					trigger_characters: Some(vec![
						".".to_string(),
						":".to_string(),
					]),
					..Default::default()
				}),
				definition_provider: Some(OneOf::Left(true)),
				implementation_provider: Some(
					ImplementationProviderCapability::Simple(true),
				),
				references_provider: Some(OneOf::Left(true)),
				rename_provider: Some(OneOf::Left(true)),
				document_formatting_provider: Some(OneOf::Left(true)),
				signature_help_provider: Some(SignatureHelpOptions {
					trigger_characters: Some(vec![
						"(".to_string(),
						",".to_string(),
					]),
					..Default::default()
				}),
				semantic_tokens_provider: Some(
					SemanticTokensServerCapabilities::SemanticTokensOptions(
						SemanticTokensOptions {
							legend: SemanticTokensLegend {
								token_types: SEMANTIC_TOKEN_TYPES.to_vec(),
								token_modifiers: vec![],
							},
							full: Some(SemanticTokensFullOptions::Bool(true)),
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
		});
	}

	async fn did_change(&self, params: DidChangeTextDocumentParams) {
		let Some(path) = uri_to_path(&params.text_document.uri) else {
			return;
		};
		let Some(change) = params.content_changes.into_iter().last() else {
			return;
		};
		self.state.notify(Command::DidChange {
			path,
			text: change.text,
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

	async fn goto_implementation(
		&self,
		params: GotoDefinitionParams,
	) -> Result<Option<GotoDefinitionResponse>> {
		Ok(self
			.state
			.query(|reply| Command::GotoImplementation(params, reply))
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

	async fn rename(
		&self,
		params: RenameParams,
	) -> Result<Option<WorkspaceEdit>> {
		Ok(self
			.state
			.query(|reply| Command::Rename(params, reply))
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

	async fn signature_help(
		&self,
		params: SignatureHelpParams,
	) -> Result<Option<SignatureHelp>> {
		Ok(self
			.state
			.query(|reply| Command::SignatureHelp(params, reply))
			.await
			.flatten())
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

	async fn completion(
		&self,
		params: CompletionParams,
	) -> Result<Option<CompletionResponse>> {
		Ok(self
			.state
			.query(|reply| Command::Completion(params, reply))
			.await
			.flatten())
	}
}

impl Backend {
	async fn virtual_file_content(
		&self,
		params: VirtualFileContentParams,
	) -> Result<String> {
		self.client
			.log_message(
				MessageType::LOG,
				Trace::new(PathBuf::from(&params.uri))
					.finish("virtual_file_content"),
			)
			.await;
		let filename =
			params.uri.strip_prefix("wx://std").ok_or_else(|| {
				JsonRpcError::invalid_params(format!(
					"not a wxstd URI: {}",
					params.uri
				))
			})?;
		// Keyed exactly as the stdlib package's own module paths, so any file
		// the stdlib grows is servable here without touching this match.
		match wx_compiler::vfs::StdlibFileSource::source(&AbsolutePath::new(
			filename,
		)) {
			Some(source) => Ok(source.to_string()),
			None => Err(JsonRpcError::invalid_params(format!(
				"unknown stdlib file: {filename}"
			))),
		}
	}

	/// Re-renders one diagnostic's full, source-snippet-annotated text on
	/// demand — see `notes/lsp-full-diagnostic-view-plan.md`. Deliberately
	/// doesn't cache anything new: `state.cached` already keeps the raw
	/// `codespan_reporting::Diagnostic<FileId>` values alive for as long as
	/// this can usefully be called, so this just re-derives the same
	/// `(path, index)` list `add_compiler_diagnostic` would have produced and
	/// re-renders the one entry the client clicked.
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

/// Re-renders one diagnostic's full, source-snippet-annotated text on
/// demand — see `notes/lsp-full-diagnostic-view-plan.md`. Deliberately
/// doesn't cache anything new: `state.cached` already keeps the raw
/// `codespan_reporting::Diagnostic<FileId>` values alive for as long as this
/// can usefully be called, so this just re-derives the same `(path, index)`
/// list `add_compiler_diagnostic` would have produced and re-renders the one
/// entry the client clicked. Free function (rather than a `Backend` method
/// body) so it's directly testable without a real `Client`.
fn render_full_diagnostic(
	state: &ServerState,
	uri: &Uri,
	index: usize,
) -> String {
	let Some((compiled, _file_id)) = resolve_uri(state, uri) else {
		return "Unable to find original wx diagnostic (file is no longer tracked)."
			.to_string();
	};
	let Some(target_path) = uri_to_path(uri) else {
		return "Unable to find original wx diagnostic.".to_string();
	};
	// Same order `analysis_from_compiled_root`/`add_compiler_diagnostic`
	// iterate and expand in — per package, linker diagnostics then every
	// module's own AST diagnostics, then TIR diagnostics, one slot per
	// `diagnostic_locations` entry matching this path (a diagnostic with no
	// primary label, like unused-enum-variant warnings, contributes one slot
	// per variant) — so `index` lines up exactly with what the client saw
	// when this was published.
	let diagnostic = compiled
		.graph
		.packages
		.iter()
		.flat_map(|cg| {
			cg.diagnostics
				.iter()
				.chain(cg.modules.iter().flat_map(|m| m.ast.diagnostics.iter()))
		})
		.chain(compiled.tir.diagnostics.iter())
		.flat_map(|d| {
			let target_path = &target_path;
			diagnostic_locations(&compiled.graph.files, d)
				.into_iter()
				.filter(move |(path, _)| path == target_path)
				.map(move |_| d)
		})
		.nth(index);
	let Some(diagnostic) = diagnostic else {
		return "Unable to find original wx diagnostic (it may have changed since this link was created)."
			.to_string();
	};
	// ANSI-colored, not `emit_to_string`'s plain output: the client strips
	// (for the virtual doc's text) and separately re-parses (for
	// `TextEditorDecorationType`s matching the user's terminal theme) the
	// same escape codes `wx-cli` prints to a real terminal — see
	// `notes/lsp-full-diagnostic-view-plan.md`.
	let mut buffer = Ansi::new(Vec::new());
	if let Err(err) = term::emit_to_write_style(
		&mut buffer,
		&term::Config::default(),
		&compiled.graph.files,
		diagnostic,
	) {
		return format!("Unable to render wx diagnostic: {err}");
	}
	String::from_utf8(buffer.into_inner()).unwrap_or_default()
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

// ── State management
// ──────────────────────────────────────────────────────────

async fn publish_diagnostics(
	client: &Client,
	publications: Vec<(PathBuf, Vec<Diagnostic>)>,
) {
	for (path, diagnostics) in publications {
		if let Some(uri) = path_to_file_uri(&path) {
			client.publish_diagnostics(uri, diagnostics, None).await;
		}
	}
}

/// Resolves the `CompiledRoot`/`FileId` a URI belongs to by scanning
/// `state.cached`, rather than through a hand-maintained reverse index —
/// see the comment on `ServerState::cached`. Matches by reconstructing each
/// module's URI and comparing strings — not by comparing `uri_to_path(uri)`
/// against `m.file_path`, since `Uri::to_file_path()` doesn't check the
/// scheme and happily returns a bogus path for non-`file://` URIs (like the
/// virtual `wx://std/...` stdlib URI), which would wrongly fail to match.
fn resolve_uri<'a>(
	state: &'a ServerState,
	uri: &Uri,
) -> Option<(&'a CompiledRoot, FileId)> {
	state.cached.values().find_map(|compiled| {
		compiled
			.graph
			.packages
			.iter()
			.flat_map(|cg| cg.modules.iter())
			.find_map(|m| {
				let matches = file_id_to_uri(&compiled.graph.files, m.file_id)
					.is_some_and(|u| u.as_str() == uri.as_str());
				matches.then_some((compiled, m.file_id))
			})
	})
}

/// Apply a manifest event independently of compilation, including edits whose
/// rebuild will be skipped as superseded. Never replace editor text with disk.
fn refresh_project_manifest(
	state: &mut ServerState,
	path: &Path,
) -> Vec<(PathBuf, Vec<Diagnostic>)> {
	if path.file_name().is_none_or(|name| name != "wx.json") {
		return Vec::new();
	}
	let Some(root) = path.parent() else {
		return Vec::new();
	};
	// Declining, not substituting. `AbsolutePath::new` asserts its argument
	// starts with `/` — unconditionally, release included — so feeding it a
	// stand-in empty path panics, and this runs on the state actor task,
	// whose death leaves `notify` dropping every later command and `query`
	// answering `None`: a server still connected but permanently silent.
	// `parse_root` and `uri_to_path` already give up on the same conversion
	// rather than invent a path.
	let Some(manifest_path) = path.to_str().map(AbsolutePath::new) else {
		return Vec::new();
	};
	let overlay = OverlayFileSource::new(&state.open_documents);
	if !overlay.exists(&manifest_path) {
		let publications = collect_clear_operations(state, root);
		state.projects.remove(root);
		return publications;
	}
	let parsed = overlay
		.read_to_string(&manifest_path)
		.and_then(|text| vfs::PackageManifest::parse(&text).map_err(|_| ()));
	let manifest = match parsed {
		Ok(manifest) => ManifestState::Parsed(manifest),
		Err(()) => ManifestState::Invalid,
	};
	if let Some(project) = state.projects.get_mut(root) {
		project.manifest = manifest;
	} else {
		state.projects.insert(
			root.to_path_buf(),
			ProjectState {
				manifest,
				published_files: HashSet::new(),
			},
		);
	}
	Vec::new()
}

/// Refreshes active roots after either buffer or filesystem mutations. Disk
/// events never modify `open_documents`: the editor owns those contents until
/// didClose, and OverlayFileSource keeps unsaved text authoritative.
///
/// Rebuilds *every* active root once per batch, not just the one owning the
/// changed file — a known cost, deliberately deferred. `paths` is merged into
/// the set of all tracked files below, so by the time roots are chosen there
/// is nothing left distinguishing what actually changed. A full `wx check` of
/// the largest example here is ~10ms with process start, stdlib, and codegen
/// included, so one root is single-digit ms; this hurts on a workspace with
/// many packages, not on this repo.
///
/// Narrowing it needs more than inverting `analysis_from_compiled_root`'s file
/// list. A compiled graph records what was *found*, so a root whose `mod foo;`
/// failed to resolve holds no recorded dependency on `foo.wx`, and creating
/// that file later would leave the stale "unresolved module" error up forever.
/// The dependency set has to come from probes rather than results:
/// `OverlayFileSource` is the one chokepoint every `exists`/`read_to_string`
/// passes through, so logging each path it is asked about — hit or miss —
/// yields an exact set per root, which inverts into `path -> dependent roots`
/// and turns the loop below into a dirty set. Manifest creation/deletion stays
/// on the blanket path regardless: `discover_package_root` walks *up* the tree
/// outside the overlay, so re-parenting is not expressible as a per-root
/// dependency.
///
/// Keep invalidation event-driven rather than polling on queries.
fn compute_active_refresh(
	state: &mut ServerState,
	paths: Vec<PathBuf>,
	logs: &mut Vec<String>,
) -> Vec<(PathBuf, Vec<Diagnostic>)> {
	if paths.is_empty() {
		return Vec::new();
	}
	let old_roots: HashSet<_> = state
		.cached
		.keys()
		.chain(
			state
				.projects
				.iter()
				.filter(|(_, project)| !project.published_files.is_empty())
				.map(|(root, _)| root),
		)
		.chain(state.own_root.values())
		.cloned()
		.collect();
	let mut files: HashSet<_> = state
		.own_root
		.keys()
		.chain(state.open_documents.keys())
		.cloned()
		.collect();
	files.extend(paths);
	let mut roots = HashSet::new();
	// A removed manifest can expose an enclosing package instead. Discover
	// from the old manifest path before dropping the previous compiled state.
	for root in &old_roots {
		if let Some(root) = discover_package_root(
			&state.open_documents,
			&state.workspace_folders,
			&root.join("wx.json"),
		) {
			roots.insert(root);
		}
	}
	state.own_root.clear();
	let mut current: HashMap<PathBuf, Vec<Diagnostic>> = HashMap::new();
	for file in files {
		match discover_package_root(
			&state.open_documents,
			&state.workspace_folders,
			&file,
		) {
			Some(root) => {
				roots.insert(root.clone());
				state.own_root.insert(file, root);
			}
			None => {
				let diagnostics = if state.open_documents.contains_key(&file) {
					vec![orphan_file_diagnostic()]
				} else {
					Vec::new()
				};
				current.insert(file, diagnostics);
			}
		}
	}
	// Only roots that are *not* about to be re-analysed get cleared
	// wholesale. `collect_clear_operations` drains `published_files`, which
	// is exactly what `collect_publish_operations` diffs the new analysis
	// against — clearing an active root first would leave that diff nothing
	// to work with, so every file it still reports would be published empty
	// and then immediately republished with the identical diagnostics.
	// `analyze_root` replaces the cache entry for the roots skipped here.
	let mut publications = Vec::new();
	for root in &old_roots {
		if !roots.contains(root) {
			publications.extend(collect_clear_operations(state, root));
		}
	}
	let mut roots: Vec<_> = roots.into_iter().collect();
	roots.sort();
	for root in roots {
		let analysis = analyze_root(state, &root, &root.join("wx.json"), logs);
		for (file, diagnostics) in
			collect_publish_operations(state, &root, analysis)
		{
			// Shared files appear under multiple roots. Publish their union once,
			// so an empty result from one root cannot erase another root's errors.
			let merged = current.entry(file).or_default();
			for diagnostic in diagnostics {
				if !merged.contains(&diagnostic) {
					merged.push(diagnostic);
				}
			}
		}
	}
	let mut current: Vec<_> = current.into_iter().collect();
	current.sort_by(|a, b| a.0.cmp(&b.0));
	publications.extend(current);
	publications
}

pub(crate) fn compute_refresh(
	state: &mut ServerState,
	file_path: &Path,
	logs: &mut Vec<String>,
) -> Vec<(PathBuf, Vec<Diagnostic>)> {
	let mut publications = refresh_project_manifest(state, file_path);
	publications.extend(compute_active_refresh(
		state,
		vec![file_path.to_path_buf()],
		logs,
	));
	publications
}

pub(crate) fn analyze_root(
	state: &mut ServerState,
	root: &Path,
	file_path: &Path,
	logs: &mut Vec<String>,
) -> AnalysisResult {
	let mut trace = Trace::new(file_path.to_path_buf());
	let graph = match parse_root(state, root, &mut trace) {
		Ok(graph) => graph,
		Err(()) => {
			state.cached.remove(root);
			logs.push(trace.finish("typecheck"));
			return analysis_from_missing_entry_file(root);
		}
	};

	let compiled = compile_root(graph, &mut trace);
	logs.push(trace.finish("typecheck"));
	let result = analysis_from_compiled_root(&compiled);
	state.cached.insert(root.to_path_buf(), compiled);
	result
}

fn collect_publish_operations(
	state: &mut ServerState,
	root: &Path,
	analysis: AnalysisResult,
) -> Vec<(PathBuf, Vec<Diagnostic>)> {
	let AnalysisResult {
		diagnostics_by_file,
		mut owned_files,
	} = analysis;
	owned_files.extend(diagnostics_by_file.keys().cloned());

	let previous = state
		.projects
		.get(root)
		.map(|project| project.published_files.clone())
		.unwrap_or_default();
	let publish_paths =
		diagnostic_publish_paths(&previous, &owned_files, &diagnostics_by_file);

	if let Some(project) = state.projects.get_mut(root) {
		project.published_files = owned_files;
	}

	publish_paths
		.into_iter()
		.map(|path| {
			let diagnostics =
				diagnostics_by_file.get(&path).cloned().unwrap_or_default();
			(path, diagnostics)
		})
		.collect()
}

fn collect_clear_operations(
	state: &mut ServerState,
	root: &Path,
) -> Vec<(PathBuf, Vec<Diagnostic>)> {
	state.cached.remove(root);
	if let Some(project) = state.projects.get_mut(root) {
		std::mem::take(&mut project.published_files)
			.into_iter()
			.map(|path| (path, Vec::new()))
			.collect()
	} else {
		Vec::new()
	}
}

fn compile_root(
	mut graph: vfs::CompilationUnit,
	trace: &mut Trace,
) -> CompiledRoot {
	let tir = trace.step("typecheck", || TIR::build(&mut graph));
	let symbol_index = build_symbol_index(&tir, &graph.interner);
	CompiledRoot {
		graph,
		tir,
		symbol_index,
	}
}

/// Parses source modules fresh from the live overlay while reusing retained
/// project manifests. First discovery loads metadata eagerly; subsequent
/// source edits and format requests do not read or parse those manifests.
/// Missing/unreadable manifests or entry files fail loading; other compiler
/// diagnostics remain on the returned graph.
fn parse_root(
	state: &mut ServerState,
	root: &Path,
	trace: &mut Trace,
) -> std::result::Result<vfs::CompilationUnit, ()> {
	let overlay = OverlayFileSource::new(&state.open_documents);
	let projects = &mut state.projects;
	let root = AbsolutePath::new(root.to_str().ok_or(())?);
	trace.step("parse", || {
		// Eagerly load each newly encountered manifest, including dependencies.
		// Keep invalid results too; only manifest events retry those reads.
		let mut pending = vec![root.clone()];
		let mut visited = HashSet::new();
		while let Some(dir) = pending.pop() {
			if !visited.insert(dir.clone()) {
				continue;
			}
			let path = PathBuf::from(dir.as_str());
			if !projects.contains_key(&path) {
				let manifest_path =
					dir.join(&vfs::RelativePath::new("wx.json"));
				if !overlay.exists(&manifest_path) {
					return Err(());
				}
				let parsed =
					overlay.read_to_string(&manifest_path).and_then(|text| {
						vfs::PackageManifest::parse(&text).map_err(|_| ())
					});
				let manifest = match parsed {
					Ok(manifest) => ManifestState::Parsed(manifest),
					Err(()) => ManifestState::Invalid,
				};
				projects.insert(
					path.clone(),
					ProjectState {
						manifest,
						published_files: HashSet::new(),
					},
				);
			}
			let ManifestState::Parsed(manifest) = &projects[&path].manifest
			else {
				return Err(());
			};
			for dependency in manifest.dependencies.values() {
				let vfs::DependencySource::Local { path } = dependency;
				pending.push(dir.join(path));
			}
		}
		let manifests: HashMap<_, _> = visited
			.into_iter()
			.map(|dir| {
				let ManifestState::Parsed(manifest) =
					&projects[Path::new(dir.as_str())].manifest
				else {
					unreachable!()
				};
				(dir, manifest)
			})
			.collect();
		vfs::open_manifest_with_manifests(root, &overlay, &manifests)
	})
}

fn analysis_from_compiled_root(compiled: &CompiledRoot) -> AnalysisResult {
	let mut diagnostics_by_file = HashMap::new();
	let mut owned_files = HashSet::new();

	for package_graph in &compiled.graph.packages {
		for module in &package_graph.modules {
			let Ok(file) = compiled.graph.files.get(module.file_id) else {
				continue;
			};
			if file.origin == vfs::FileOrigin::Local {
				owned_files.insert(PathBuf::from(module.file_path.as_str()));
			}
		}
		for diagnostic in &package_graph.diagnostics {
			add_compiler_diagnostic(
				&mut diagnostics_by_file,
				&compiled.graph.files,
				diagnostic,
			);
		}
		for module in &package_graph.modules {
			for diagnostic in &module.ast.diagnostics {
				add_compiler_diagnostic(
					&mut diagnostics_by_file,
					&compiled.graph.files,
					diagnostic,
				);
			}
		}
	}

	for diagnostic in &compiled.tir.diagnostics {
		add_compiler_diagnostic(
			&mut diagnostics_by_file,
			&compiled.graph.files,
			diagnostic,
		);
	}

	AnalysisResult {
		diagnostics_by_file,
		owned_files,
	}
}

/// The only way `parse_root` can still fail now that `discover_package_root`
/// has already confirmed a `wx.json` exists: that manifest fails to parse,
/// or its `entry` can't be read (e.g. either was deleted between
/// `discover_package_root`'s existence check and this call). Everything
/// else — missing/ambiguous child modules, dependency resolution problems —
/// is a diagnostic on the graph rather than a hard failure, so this is a
/// rare, narrow case rather than the general error path it used to be.
fn analysis_from_missing_entry_file(root: &Path) -> AnalysisResult {
	let mut diagnostics_by_file = HashMap::new();
	let mut owned_files = HashSet::new();

	owned_files.insert(root.to_path_buf());
	diagnostics_by_file.insert(
		root.to_path_buf(),
		vec![Diagnostic {
			range: Range::default(),
			severity: Some(DiagnosticSeverity::ERROR),
			code: None,
			code_description: None,
			source: Some("wx-lsp".to_string()),
			message: format!(
				"failed to load the wx project at `{}` (its `wx.json` may \
				 not parse, or its `entry` may not be readable)",
				root.display()
			),
			related_information: None,
			tags: None,
			data: None,
		}],
	);

	AnalysisResult {
		diagnostics_by_file,
		owned_files,
	}
}

/// A file with no `wx.json` ancestor isn't part of any project the LSP can
/// resolve. Surfaced as a visible, whole-file hint rather than silence —
/// mirrors rust-analyzer's own "unlinked file" diagnostic, including its
/// trick for spanning the whole document without measuring it: an
/// intentionally out-of-range end position, which compliant clients clamp
/// to the real end of the document, needing no scan of `text` at all.
/// Tagged `UNNECESSARY` so editors render the file faded, making "wx-lsp
/// doesn't see this file" a visual property of the file itself, not just
/// an absence of red squiggles.
fn orphan_file_diagnostic() -> Diagnostic {
	Diagnostic {
		range: Range {
			start: Position {
				line: 0,
				character: 0,
			},
			end: Position {
				line: u32::MAX,
				character: u32::MAX,
			},
		},
		severity: Some(DiagnosticSeverity::INFORMATION),
		code: None,
		code_description: None,
		source: Some("wx-lsp".to_string()),
		message: "This file is not part of a wx project, so wx-lsp \
		          can't offer IDE services for it.\n\nAdd a `wx.json` in \
		          this directory (or an ancestor) with an `entry` that \
		          reaches this file."
			.to_string(),
		related_information: None,
		tags: Some(vec![DiagnosticTag::UNNECESSARY]),
		data: None,
	}
}

pub(crate) fn diagnostic_publish_paths(
	previous: &HashSet<PathBuf>,
	owned_files: &HashSet<PathBuf>,
	diagnostics_by_file: &HashMap<PathBuf, Vec<Diagnostic>>,
) -> HashSet<PathBuf> {
	let mut paths = previous.clone();
	paths.extend(owned_files.iter().cloned());
	paths.extend(diagnostics_by_file.keys().cloned());
	paths
}

/// Resolves one label to the absolute path + LSP range it points at, or
/// `None` if the label's file is `Virtual` (true for the stdlib's `wx://std/...`
/// "files", which have no real location on disk to file a diagnostic under),
/// or the span doesn't map to a valid range.
fn label_location(
	files: &vfs::Files,
	label: &Label<FileId>,
) -> Option<(PathBuf, Range)> {
	let file = files.get(label.file_id).ok()?;
	if file.origin != vfs::FileOrigin::Local {
		return None;
	}
	let path = PathBuf::from(&file.name);
	let range = span_to_range(
		files,
		SourceSpan::new(
			label.file_id,
			TextSpan::new(label.range.start as u32, label.range.end as u32),
		),
	)?;
	Some((path, range))
}

/// Returns the absolute path + LSP range(s) a diagnostic should be filed
/// under. A diagnostic with a primary label collapses to that one location —
/// secondary labels are supplementary context for that one site (e.g.
/// `report_enum_duplicate_value`'s "value assigned here" labels) and become
/// `related_information` instead, not separate squiggles. A diagnostic with
/// *no* primary label (e.g. `report_unused_enum_variants`, where every listed
/// variant is equally "the problem") instead gets one location per label, so
/// each is independently squiggled rather than arbitrarily collapsing to
/// whichever label happens to be first in the vec — LSP's `Diagnostic` only
/// carries a single `range`, so multiple equally-important locations can only
/// be represented as multiple `Diagnostic`s.
///
/// Single source of truth for "which diagnostics belong to file X, in what
/// order, and how many slots each contributes" — used both when building the
/// published list and when re-deriving it later for `wx/fullDiagnostic`, so
/// the two can't silently drift apart.
fn diagnostic_locations(
	files: &vfs::Files,
	diagnostic: &CodeDiagnostic<FileId>,
) -> Vec<(PathBuf, Range)> {
	if let Some(primary) = diagnostic
		.labels
		.iter()
		.find(|label| label.style == LabelStyle::Primary)
	{
		return label_location(files, primary).into_iter().collect();
	}
	diagnostic
		.labels
		.iter()
		.filter_map(|label| label_location(files, label))
		.collect()
}

fn add_compiler_diagnostic(
	grouped: &mut HashMap<PathBuf, Vec<Diagnostic>>,
	files: &vfs::Files,
	diagnostic: &CodeDiagnostic<FileId>,
) {
	let label_messages: Vec<String> = diagnostic
		.labels
		.iter()
		.filter(|&label| !label.message.is_empty())
		.map(|label| label.message.clone())
		.collect();
	let message = if label_messages.is_empty() {
		diagnostic.message.clone()
	} else {
		format!("{}\n{}", diagnostic.message, label_messages.join("\n"))
	};

	let tags = diagnostic.code.as_ref().and_then(|code| {
		use std::str::FromStr;
		use wx_compiler::diagnostics::DiagnosticCode;
		DiagnosticCode::from_str(code)
			.ok()
			.and_then(|code| match code {
				DiagnosticCode::UnreachableCode
				| DiagnosticCode::UnusedVariable
				| DiagnosticCode::UnusedTypeParam
				| DiagnosticCode::UnnecessaryMutability
				| DiagnosticCode::UnusedItem
				| DiagnosticCode::UnusedEnumVariant
				| DiagnosticCode::UnusedLabel
				| DiagnosticCode::UnusedStructField => {
					Some(vec![DiagnosticTag::UNNECESSARY])
				}
				_ => None,
			})
	});

	for (path, range) in diagnostic_locations(files, diagnostic) {
		let primary_uri = path_to_file_uri(&path);
		let related_information = diagnostic_related_information(
			files,
			diagnostic,
			primary_uri.as_ref(),
			range,
		);

		grouped.entry(path).or_default().push(Diagnostic {
			range,
			severity: Some(severity_to_lsp(diagnostic.severity)),
			code: diagnostic
				.code
				.as_ref()
				.map(|code| NumberOrString::String(code.to_string())),
			code_description: None,
			source: Some("wx".to_string()),
			message: message.clone(),
			related_information,
			tags: tags.clone(),
			data: None,
		});
	}
}

fn diagnostic_related_information(
	files: &vfs::Files,
	diagnostic: &CodeDiagnostic<FileId>,
	primary_uri: Option<&Uri>,
	primary_range: Range,
) -> Option<Vec<DiagnosticRelatedInformation>> {
	let label_infos = diagnostic.labels.iter().filter_map(|label| {
		if label.message.is_empty() {
			return None;
		}
		let uri = file_id_to_uri(files, label.file_id)?;
		let range = span_to_range(
			files,
			SourceSpan::new(
				label.file_id,
				TextSpan::new(label.range.start as u32, label.range.end as u32),
			),
		)?;
		Some(DiagnosticRelatedInformation {
			location: Location { uri, range },
			message: label.message.clone(),
		})
	});

	let note_infos = diagnostic.notes.iter().filter_map(|note| {
		let uri = primary_uri?.clone();
		Some(DiagnosticRelatedInformation {
			location: Location {
				uri,
				range: primary_range,
			},
			message: note.clone(),
		})
	});

	let infos: Vec<_> = label_infos.chain(note_infos).collect();
	(!infos.is_empty()).then_some(infos)
}

fn push_type_params(
	s: &mut String,
	tir: &TIR,
	interner: &ast::StringInterner,
	packages: &[vfs::PackageGraph],
	from: vfs::PackageId,
	type_params: &[TypeParamInfo],
) {
	if type_params.is_empty() {
		return;
	}
	s.push('<');
	for (i, tp) in type_params.iter().enumerate() {
		if i > 0 {
			s.push_str(", ");
		}
		s.push_str(interner.resolve(tp.name.inner).unwrap());
		let has_bounds =
			!tp.bounds.traits.is_empty() || tp.bounds.typeset.is_some();
		if has_bounds {
			s.push_str(": ");
			let fmt = tir.formatter(interner, packages, from);
			s.push_str(&fmt.display_bounds(&tp.bounds).unwrap_or_default());
		}
	}
	s.push('>');
}

/// The point to search backward from for `kind`'s own leading doc comment —
/// `pub_span`'s start when the item is `pub` (it sits to the left of
/// `fn`/`struct`/etc., closer to any attributes/doc comments above), else
/// the item's name span. `None` for symbol kinds that aren't a standalone
/// declaration with its own doc comment (locals, params, `self`, type
/// params, labels, enum variants, struct fields, associated types, and the
/// synthetic `Self`/namespace kinds).
fn doc_comment_anchor(tir: &TIR, kind: &SymbolKind) -> Option<SourceSpan> {
	fn anchor(
		file_id: FileId,
		pub_span: Option<TextSpan>,
		name_span: TextSpan,
	) -> SourceSpan {
		SourceSpan::new(file_id, pub_span.unwrap_or(name_span))
	}
	match kind {
		SymbolKind::Function(id) => {
			let f = &tir.items.functions
				[usize::from(tir.items.function_index(*id)?)];
			Some(anchor(f.file_id, f.pub_span, f.name.span))
		}
		SymbolKind::Global(id) => {
			let g =
				&tir.items.globals[usize::from(tir.items.global_index(*id)?)];
			Some(anchor(g.file_id, g.pub_span, g.name.span))
		}
		SymbolKind::Const(id) => {
			let c =
				&tir.items.constants[usize::from(tir.items.const_index(*id)?)];
			Some(anchor(c.file_id, c.pub_span, c.name.span))
		}
		SymbolKind::Struct(id) => {
			let s = tir
				.items
				.structs
				.get(usize::from(tir.items.struct_index(*id)?))?;
			Some(anchor(s.file_id, s.pub_span, s.name.span))
		}
		SymbolKind::Enum(id) => {
			let e = tir
				.items
				.enums
				.get(usize::from(tir.items.enum_index(*id)?))?;
			Some(anchor(e.file_id, e.pub_span, e.name.span))
		}
		SymbolKind::Trait(id) => {
			let t = tir
				.items
				.traits
				.get(usize::from(tir.items.trait_index(*id)?))?;
			Some(anchor(t.file_id, t.pub_span, t.name.span))
		}
		SymbolKind::TypeSet(id) => {
			let ts = tir
				.items
				.typesets
				.get(usize::from(tir.items.typeset_index(*id)?))?;
			Some(anchor(ts.file_id, ts.pub_span, ts.name.span))
		}
		SymbolKind::TypeAlias(id) => {
			let a = &tir.items.type_aliases
				[usize::from(tir.items.type_alias_index(*id)?)];
			Some(anchor(a.file_id, a.pub_span, a.name.span))
		}
		SymbolKind::Memory(id) => {
			let m =
				&tir.items.memories[usize::from(tir.items.memory_index(*id)?)];
			Some(SourceSpan::new(m.file_id, m.name.span))
		}
		_ => None,
	}
}

/// The markdown text of the doc-comment block (if any) immediately above
/// `anchor_offset` in `source` — walks backward one whole line at a time: a
/// `///` line is collected, a `#[...]` line is skipped (attributes sit
/// between a doc comment and the item they document, e.g. `std/main.wx`'s
/// `memory_grow`), and anything else (including a blank line) stops the
/// walk. Linear in the size of the doc-comment block being read — each
/// `rfind('\n')` scans backward only as far as the nearest newline, not the
/// whole `source[..k]` slice it's called on, so cost never depends on how
/// deep into the file `anchor_offset` is.
fn leading_doc_comment(source: &str, anchor_offset: u32) -> Option<String> {
	let mut doc_lines = Vec::new();
	let mut line_start = source[..anchor_offset as usize]
		.rfind('\n')
		.map_or(0, |i| i + 1);
	while line_start > 0 {
		let prev_line_start =
			source[..line_start - 1].rfind('\n').map_or(0, |i| i + 1);
		let line = source[prev_line_start..line_start - 1].trim();
		if let Some(text) = line.strip_prefix("///") {
			doc_lines.push(text.strip_prefix(' ').unwrap_or(text));
		} else if !line.starts_with("#[") {
			break;
		}
		line_start = prev_line_start;
	}
	if doc_lines.is_empty() {
		return None;
	}
	doc_lines.reverse();
	Some(doc_lines.join("\n"))
}

fn symbol_hover_text(
	tir: &TIR,
	interner: &ast::StringInterner,
	packages: &[vfs::PackageGraph],
	from: vfs::PackageId,
	kind: &SymbolKind,
) -> Option<String> {
	let fmt = tir.formatter(interner, packages, from);
	match kind {
		SymbolKind::Function(def_id) => {
			let fi = usize::from(tir.items.function_index(*def_id)?);
			let func = &tir.items.functions[fi];
			let name = interner.resolve(func.name.inner).unwrap();
			let pub_prefix = if func.pub_span.is_some() { "pub " } else { "" };
			let mut s = format!("{pub_prefix}fn {name}");
			push_type_params(
				&mut s,
				tir,
				interner,
				packages,
				from,
				&func.type_params,
			);
			s.push('(');
			for (i, param) in func.params.iter().enumerate() {
				if i > 0 {
					s.push_str(", ");
				}
				let pname = interner.resolve(param.name.inner).unwrap();
				s.push_str(pname);
				s.push_str(": ");
				s.push_str(&fmt.display_type(param.ty.inner).unwrap());
			}
			s.push(')');
			s.push_str(" -> ");
			match &func.result {
				Some(result) => {
					s.push_str(&fmt.display_type(result.inner).unwrap())
				}
				None => s.push_str("()"),
			}
			Some(s)
		}
		SymbolKind::Global(def_id) => {
			let gi = usize::from(tir.items.global_index(*def_id)?);
			let global = &tir.items.globals[gi];
			let name = interner.resolve(global.name.inner).unwrap();
			let type_str = fmt.display_type(global.ty.inner).unwrap();
			let pub_prefix = if global.pub_span.is_some() {
				"pub "
			} else {
				""
			};
			let mut_kw = if global.mut_span.is_some() {
				"mut "
			} else {
				""
			};
			Some(format!("{pub_prefix}global {mut_kw}{name}: {type_str}"))
		}
		SymbolKind::Memory(def_id) => {
			let mi = usize::from(tir.items.memory_index(*def_id)?);
			let memory = &tir.items.memories[mi];
			let name = interner.resolve(memory.name.inner).unwrap();
			let size_str = fmt.display_type(memory.size.inner).unwrap();
			Some(format!(
				"memory {name}: Memory where {{ Size = {size_str} }}"
			))
		}
		SymbolKind::Struct(def_id) => {
			let struct_ = tir
				.items
				.structs
				.get(usize::from(tir.items.struct_index(*def_id)?))?;
			let name = interner.resolve(struct_.name.inner).unwrap();
			let pub_prefix = if struct_.pub_span.is_some() {
				"pub "
			} else {
				""
			};
			let mut s = format!("{pub_prefix}struct {name}");
			push_type_params(
				&mut s,
				tir,
				interner,
				packages,
				from,
				&struct_.type_params,
			);
			Some(s)
		}
		SymbolKind::Enum(def_id) => {
			let enum_ = tir
				.items
				.enums
				.get(usize::from(tir.items.enum_index(*def_id)?))?;
			let name = interner.resolve(enum_.name.inner).unwrap();
			let pub_prefix = if enum_.pub_span.is_some() { "pub " } else { "" };
			let repr = fmt.display_type(enum_.repr_type).unwrap();
			Some(format!("{pub_prefix}enum {name}: {repr} {{ ... }}"))
		}
		SymbolKind::InherentImplSelf(block_idx) => {
			let target = tir
				.items
				.inherent_impls
				.get(usize::from(*block_idx))?
				.target;
			Some(format!("Self = {}", fmt.display_type(target.inner).ok()?))
		}
		SymbolKind::TraitImplSelf(trait_impl_idx) => {
			let target = tir
				.items
				.trait_impls
				.get(usize::from(*trait_impl_idx))?
				.target;
			Some(format!("Self = {}", fmt.display_type(target.inner).ok()?))
		}
		SymbolKind::Local {
			func_id,
			scope_idx,
			local_idx,
		} => {
			let fi = usize::from(tir.items.function_index(*func_id)?);
			let body_idx = tir.items.functions[fi].body?;
			let body = &tir.items.bodies[usize::from(body_idx)];
			let local = body
				.stack
				.scopes
				.get(usize::from(*scope_idx))?
				.locals
				.get(usize::from(*local_idx))?;
			let name = interner.resolve(local.name.inner).unwrap();
			let type_str = fmt.display_type(local.ty).unwrap();
			let mut_kw = if local.mut_span.is_some() { "mut " } else { "" };
			Some(format!("local {mut_kw}{name}: {type_str}"))
		}
		SymbolKind::Param { func_id, param_idx } => {
			let fi = usize::from(tir.items.function_index(*func_id)?);
			let param =
				tir.items.functions[fi].params.get(*param_idx as usize)?;
			let name = interner.resolve(param.name.inner).unwrap();
			let type_str = fmt.display_type(param.ty.inner).unwrap();
			let mut_kw = if param.mut_span.is_some() { "mut " } else { "" };
			Some(format!("{mut_kw}{name}: {type_str}"))
		}
		SymbolKind::SelfParam(func_id) => {
			let fi = usize::from(tir.items.function_index(*func_id)?);
			let param = tir.items.functions[fi].params.first()?;
			let type_str = fmt.display_type(param.ty.inner).unwrap();
			let mut_kw = if param.mut_span.is_some() { "mut " } else { "" };
			Some(format!("{mut_kw}self: {type_str}"))
		}
		SymbolKind::EnumVariant {
			enum_id,
			variant_idx,
		} => {
			let enum_ = tir
				.items
				.enums
				.get(usize::from(tir.items.enum_index(*enum_id)?))?;
			let variant = enum_.variants.get(usize::from(*variant_idx))?;
			let enum_name = interner.resolve(enum_.name.inner).unwrap();
			let variant_name = interner.resolve(variant.name.inner).unwrap();
			Some(format!("{enum_name}::{variant_name}"))
		}
		SymbolKind::Namespace(ns_idx) => {
			let ns = tir.modules.namespaces.get(usize::from(*ns_idx))?;
			match ns.declaration {
				ModuleDeclarationKind::Module(decl_idx) => {
					let decl =
						tir.modules.module_decls.get(usize::from(decl_idx))?;
					let name = interner.resolve(decl.name.inner).unwrap();
					let pub_prefix =
						if decl.pub_span.is_some() { "pub " } else { "" };
					Some(format!("{pub_prefix}mod {name}"))
				}
				ModuleDeclarationKind::Import(import_idx) => {
					let decl = tir
						.modules
						.import_decls
						.get(usize::from(import_idx))?;
					let external =
						interner.resolve(decl.external_name.inner).unwrap();
					match &decl.internal_name {
						Some(alias) => {
							let alias_name =
								interner.resolve(alias.inner).unwrap();
							Some(format!(
								"import \"{external}\" as {alias_name}"
							))
						}
						None => Some(format!("import \"{external}\"")),
					}
				}
				// A package has no name of its own — show it as the package
				// this hover is rendered from calls it (or, for `crate`/
				// `super` naming `from`'s own root, as the literal keyword).
				ModuleDeclarationKind::Package(_) => {
					let name =
						tir.namespace_name(*ns_idx, packages, from, interner);
					Some(format!("package {name}"))
				}
			}
		}
		SymbolKind::TypeParam { owner, param_index } => {
			let param_index = *param_index as usize;
			let tp: &TypeParamInfo = match owner {
				TypeParamOwner::Function(def_id) => {
					let fi = usize::from(tir.items.function_index(*def_id)?);
					let func = &tir.items.functions[fi];
					let local = param_index
						.checked_sub(func.inherited_type_param_count)?;
					func.type_params.get(local)?
				}
				TypeParamOwner::Struct(def_id) => {
					let si = usize::from(tir.items.struct_index(*def_id)?);
					tir.items.structs[si].type_params.get(param_index)?
				}
				TypeParamOwner::InherentImpl(block_idx) => tir
					.items
					.inherent_impls
					.get(usize::from(*block_idx))?
					.type_params
					.get(param_index)?,
				TypeParamOwner::Trait(trait_idx) => {
					let t = tir.items.traits.get(usize::from(*trait_idx))?;
					&t.self_type_param
				}
				TypeParamOwner::TypeAlias(def_id) => {
					let ai = usize::from(tir.items.type_alias_index(*def_id)?);
					tir.items.type_aliases[ai].type_params.get(param_index)?
				}
				TypeParamOwner::TraitImpl(_) => return None,
			};
			let name = interner.resolve(tp.name.inner).unwrap();
			let bounds_str = fmt.display_bounds(&tp.bounds).unwrap_or_default();
			if bounds_str.is_empty() {
				Some(name.to_string())
			} else {
				Some(format!("{name}: {bounds_str}"))
			}
		}
		SymbolKind::Label { .. } => None,
		SymbolKind::Trait(def_id) => {
			let trait_ = tir
				.items
				.traits
				.get(usize::from(tir.items.trait_index(*def_id)?))?;
			let name = interner.resolve(trait_.name.inner).unwrap();
			let bounds_str =
				fmt.display_bounds(&trait_.bounds).unwrap_or_default();
			if bounds_str.is_empty() {
				Some(format!("trait {name}"))
			} else {
				Some(format!("trait {name}: {bounds_str}"))
			}
		}
		SymbolKind::TypeSet(def_id) => {
			let typeset = tir
				.items
				.typesets
				.get(usize::from(tir.items.typeset_index(*def_id)?))?;
			let name = interner.resolve(typeset.name.inner).unwrap();
			Some(format!("typeset {name} {{ ... }}"))
		}
		SymbolKind::TypeAlias(def_id) => {
			let ai = usize::from(tir.items.type_alias_index(*def_id)?);
			let alias = &tir.items.type_aliases[ai];
			let name = interner.resolve(alias.name.inner).unwrap();
			let pub_prefix = if alias.pub_span.is_some() { "pub " } else { "" };
			let mut s = format!("{pub_prefix}type {name}");
			push_type_params(
				&mut s,
				tir,
				interner,
				packages,
				from,
				&alias.type_params,
			);
			// Bodiless `#[intrinsic] type u8;` — `alias.body` holds the
			// resolved primitive, not a source-written `= Type` (see the
			// doc comment on `TypeAlias::body`).
			if !alias.attributes.contains(&ItemAttribute::Intrinsic) {
				s.push_str(" = ");
				s.push_str(&fmt.display_type(alias.body).ok()?);
			}
			Some(s)
		}
		SymbolKind::Const(def_id) => {
			let ci = usize::from(tir.items.const_index(*def_id)?);
			let constant = &tir.items.constants[ci];
			let name = interner.resolve(constant.name.inner).unwrap();
			let type_str = fmt.display_type(constant.ty.inner).unwrap();
			let pub_prefix = if constant.pub_span.is_some() {
				"pub "
			} else {
				""
			};
			Some(format!("{pub_prefix}const {name}: {type_str}"))
		}
		SymbolKind::StructField {
			struct_id,
			field_idx,
		} => {
			let struct_ = tir
				.items
				.structs
				.get(usize::from(tir.items.struct_index(*struct_id)?))?;
			let field = struct_.fields.get(usize::from(*field_idx))?;
			let name = interner.resolve(field.name.inner).unwrap();
			let type_str = fmt.display_type(field.ty.inner).unwrap();
			let pub_prefix = if field.pub_span.is_some() { "pub " } else { "" };
			Some(format!("{pub_prefix}{name}: {type_str}"))
		}
		SymbolKind::AssocType {
			trait_id,
			assoc_name,
		} => {
			let trait_ = tir
				.items
				.traits
				.get(usize::from(tir.items.trait_index(*trait_id)?))?;
			let at = trait_.assoc_types.get(assoc_name)?;
			let name = interner.resolve(*assoc_name).unwrap();
			let bounds_str = fmt.display_bounds(&at.bounds).unwrap_or_default();
			if bounds_str.is_empty() {
				Some(format!("type {name}"))
			} else {
				Some(format!("type {name}: {bounds_str}"))
			}
		}
	}
}

struct ActiveCall {
	func_name_start: usize,
	active_param: usize,
}

/// Scans backwards from `offset` to find the innermost open function call.
fn find_active_call(source: &str, offset: usize) -> Option<ActiveCall> {
	let before = &source[..offset];

	// Walk backwards tracking paren depth to find the opening `(`
	let mut depth = 0usize;
	let mut paren_pos = None;
	for (i, ch) in before.char_indices().rev() {
		match ch {
			')' => depth += 1,
			'(' => {
				if depth == 0 {
					paren_pos = Some(i);
					break;
				}
				depth -= 1;
			}
			_ => {}
		}
	}
	let paren_pos = paren_pos?;

	// Find the identifier immediately before `(`
	let before_paren = before[..paren_pos].trim_end();
	let name_end = before_paren.len();
	let name_start = before_paren
		.char_indices()
		.rev()
		.take_while(|(_, ch)| ch.is_alphanumeric() || *ch == '_')
		.last()
		.map(|(i, _)| i)?;
	if name_start >= name_end {
		return None;
	}

	// Count top-level commas between `(` and cursor for the active parameter index
	let mut depth = 0usize;
	let mut active_param = 0usize;
	for ch in source[paren_pos + 1..offset].chars() {
		match ch {
			'(' => depth += 1,
			')' => depth = depth.saturating_sub(1),
			',' if depth == 0 => active_param += 1,
			_ => {}
		}
	}

	Some(ActiveCall {
		func_name_start: name_start,
		active_param,
	})
}

fn symbol_kind_to_token_type(kind: SymbolKind) -> Option<TokenType> {
	let tt = match kind {
		SymbolKind::Function(_) => TokenType::Function,
		SymbolKind::Global(_)
		| SymbolKind::Const(_)
		| SymbolKind::Memory(_)
		| SymbolKind::Local { .. }
		| SymbolKind::StructField { .. } => TokenType::Variable,
		SymbolKind::Enum(_) => TokenType::Enum,
		SymbolKind::Struct(_) => TokenType::Struct,
		SymbolKind::Namespace(_) => TokenType::Namespace,
		SymbolKind::Param { .. } => TokenType::Parameter,
		// The `self` receiver — excluded for the same reason as
		// `InherentImplSelf`/`TraitImplSelf` below: it's the `self` keyword,
		// not a name the user chose, so it shouldn't be colored like an
		// ordinary parameter.
		SymbolKind::SelfParam(_) => return None,
		SymbolKind::EnumVariant { .. } => TokenType::EnumMember,
		SymbolKind::Trait(_) => TokenType::Interface,
		// The trait's implicit `Self` is the only `TypeParam` a `Trait`
		// owns (see `Trait::self_type_param`) — excluded here for the same
		// reason as `InherentImplSelf`/`TraitImplSelf` below: it's the
		// `Self` keyword, not a name the user wrote, so it shouldn't be
		// colored like a type-parameter reference.
		SymbolKind::TypeParam {
			owner: TypeParamOwner::Trait(_),
			..
		} => return None,
		SymbolKind::TypeParam { .. } => TokenType::TypeParameter,
		SymbolKind::AssocType { .. }
		| SymbolKind::TypeSet(_)
		| SymbolKind::TypeAlias(_) => TokenType::Type,
		SymbolKind::Label { .. } => return None,
		// `Self` inside an impl block or trait impl — excluded so the
		// editor's grammar-based keyword highlighting applies instead (the
		// original ask this whole feature exists for), matching how
		// rust-analyzer treats `self`/`Self`. See
		// `symbol_index::SymbolKind::InherentImplSelf`.
		SymbolKind::InherentImplSelf(_) | SymbolKind::TraitImplSelf(_) => {
			return None;
		}
	};
	Some(tt)
}

/// Every `SymbolKind` that should count as "a reference to the same thing"
/// as `kind`, for `textDocument/references`. For most kinds this is just
/// `[kind]` — unchanged. For a struct/enum (or `Self` inside one of its
/// impls, normalized to the struct/enum it resolves to first), it's the
/// struct/enum's own kind plus `InherentImplSelf`/`TraitImplSelf` for every
/// impl block/trait impl targeting that type — so `Self` usages inside
/// those impls show up as references too, the way a literal name reference
/// would (matches rust-analyzer). Looked up via `SymbolIndex`'s
/// `ImplTarget`-keyed reverse indices (O(1)) rather than scanning
/// `impl_block_list`/`trait_impls` per query. `Rename` deliberately does
/// *not* use this — it must stay exact-kind-only, or it would rewrite
/// `Self` keyword text.
fn reference_search_kinds(
	tir: &TIR,
	index: &SymbolIndex,
	kind: SymbolKind,
) -> Vec<SymbolKind> {
	let target = match kind {
		SymbolKind::Struct(id) => {
			tir.items.struct_index(id).map(ImplTarget::Struct)
		}
		SymbolKind::Enum(id) => tir.items.enum_index(id).map(ImplTarget::Enum),
		SymbolKind::InherentImplSelf(block_idx) => tir
			.items
			.inherent_impls
			.get(usize::from(block_idx))
			.and_then(|b| {
				ImplTarget::from_type(tir.types.resolve(b.target.inner)).ok()
			}),
		SymbolKind::TraitImplSelf(trait_impl_idx) => tir
			.items
			.trait_impls
			.get(usize::from(trait_impl_idx))
			.and_then(|ti| {
				ImplTarget::from_type(tir.types.resolve(ti.target.inner)).ok()
			}),
		_ => return vec![kind],
	};
	let target_kind = target.and_then(|t| match t {
		ImplTarget::Struct(idx) => Some(SymbolKind::Struct(
			tir.items.structs.get(usize::from(idx))?.id,
		)),
		ImplTarget::Enum(idx) => {
			Some(SymbolKind::Enum(tir.items.enums.get(usize::from(idx))?.id))
		}
		_ => None,
	});
	let (Some(target), Some(target_kind)) = (target, target_kind) else {
		return vec![kind];
	};
	let mut kinds = vec![target_kind];
	if let Some(refs) = index.impls_by_target.get(&target) {
		kinds.extend(refs.iter().map(|r| match r {
			ImplRef::Inherent(idx) => SymbolKind::InherentImplSelf(*idx),
			ImplRef::Trait(idx) => SymbolKind::TraitImplSelf(*idx),
		}));
	}
	kinds
}

/// Every location `textDocument/implementation` should jump to for `kind`:
/// for a struct/enum, every impl block or trait impl targeting it (any
/// instantiation, via the same `ImplTarget`-keyed indices
/// `reference_search_kinds` uses); for a trait, every impl of that trait,
/// regardless of target type. Each location is the impl header's own
/// target-type span (`impl Target { }` / `impl Trait for Target { }`),
/// matching rust-analyzer's landing spot. Empty for every other kind — `Self`
/// itself isn't a sensible place to ask "go to implementations" from.
fn implementation_locations(
	tir: &TIR,
	index: &SymbolIndex,
	kind: SymbolKind,
) -> Vec<SourceSpan> {
	let target = match kind {
		SymbolKind::Struct(id) => {
			tir.items.struct_index(id).map(ImplTarget::Struct)
		}
		SymbolKind::Enum(id) => tir.items.enum_index(id).map(ImplTarget::Enum),
		SymbolKind::Trait(id) => {
			let Some(trait_index) = tir.items.trait_index(id) else {
				return Vec::new();
			};
			return tir
				.items
				.trait_impls
				.iter()
				.filter(|ti| ti.trait_index == trait_index)
				.map(|ti| SourceSpan::new(ti.file_id, ti.target.span))
				.collect();
		}
		_ => return Vec::new(),
	};
	let Some(target) = target else {
		return Vec::new();
	};
	index
		.impls_by_target
		.get(&target)
		.into_iter()
		.flatten()
		.copied()
		.filter_map(|impl_ref| match impl_ref {
			ImplRef::Inherent(idx) => tir
				.items
				.inherent_impls
				.get(usize::from(idx))
				.map(|b| SourceSpan::new(b.file_id, b.target.span)),
			ImplRef::Trait(idx) => tir
				.items
				.trait_impls
				.get(usize::from(idx))
				.map(|ti| SourceSpan::new(ti.file_id, ti.target.span)),
		})
		.collect()
}

// ── Helpers
// ───────────────────────────────────────────────────────────────────

/// Resolves `(source, offset)` for `uri`/`position`, preferring the live
/// in-memory buffer (unsaved edits) over the last-compiled source. The two
/// can diverge in both length and line/character shape, since TIR is only
/// rebuilt on save (see `did_change`) — resolving `source` and `offset` from
/// two different snapshots of the file is what let a stale, shorter source
/// get sliced with an offset computed for the live, longer one.
fn resolve_source_and_offset<'a>(
	state: &'a ServerState,
	compiled: &'a CompiledRoot,
	uri: &Uri,
	file_id: FileId,
	position: Position,
) -> Option<(&'a str, usize)> {
	let path = uri_to_path(uri);
	if let Some(doc) = path.as_ref().and_then(|p| state.open_documents.get(p)) {
		let source = doc.text.as_str();
		let offset = position_to_offset_in_str(source, position)?;
		Some((source, offset))
	} else {
		let source = compiled.graph.files.get(file_id).ok()?.source.as_str();
		let offset =
			position_to_offset(&compiled.graph.files, file_id, position)?
				as usize;
		Some((source, offset))
	}
}

/// Converts a UTF-16 code unit offset within `line` — the unit LSP's
/// `Position::character` is defined in (see the `PositionEncodingKind` spec;
/// this server never negotiates `utf-8`/`utf-32`, so every `Position` it
/// receives or sends is UTF-16) — to the corresponding UTF-8 byte offset.
/// Every character outside the Basic Multilingual Plane (emoji, some CJK)
/// counts as 2 UTF-16 units despite being a single `char`, and most non-ASCII
/// BMP characters (e.g. Cyrillic) take 1 UTF-16 unit but 2+ UTF-8 bytes — so
/// neither a byte count nor a `char` count can stand in for it. Treating
/// `character` as a byte offset directly (the previous behavior) sliced the
/// source at whatever byte the UTF-16 count landed on, which for non-ASCII
/// text can fall inside a multi-byte character and panic.
///
/// Fast-paths pure-ASCII lines (the overwhelming majority of source code):
/// there, byte offset and UTF-16 offset are the same number by construction,
/// so `str::is_ascii()` — a chunked, word-at-a-time check, not a per-char
/// loop — lets those lines skip the `char_indices` walk entirely.
fn utf16_offset_to_byte_offset(line: &str, utf16_offset: usize) -> usize {
	if line.is_ascii() {
		return utf16_offset.min(line.len());
	}
	let mut utf16_units = 0usize;
	for (byte_offset, ch) in line.char_indices() {
		if utf16_units >= utf16_offset {
			return byte_offset;
		}
		utf16_units += ch.len_utf16();
	}
	line.len()
}

/// The reverse of `utf16_offset_to_byte_offset`: counts how many UTF-16 code
/// units `prefix` encodes as, for building a `Position` to send back to the
/// client. Same ASCII fast path, for the same reason.
fn byte_offset_to_utf16_offset(prefix: &str) -> usize {
	if prefix.is_ascii() {
		return prefix.len();
	}
	prefix.chars().map(char::len_utf16).sum()
}

fn position_to_offset(
	files: &vfs::Files,
	file_id: FileId,
	position: Position,
) -> Option<u32> {
	let line_range = files.line_range(file_id, position.line as usize).ok()?;
	let source = files.source(file_id).ok()?;
	let line_text = &source[line_range.clone()];
	let byte_in_line =
		utf16_offset_to_byte_offset(line_text, position.character as usize);
	Some((line_range.start + byte_in_line) as u32)
}

/// Converts an LSP `Position` to a byte offset directly in a source string,
/// without needing a compiled file index. Returns `None` if the line is out of range.
fn position_to_offset_in_str(
	source: &str,
	position: Position,
) -> Option<usize> {
	let mut line = 0u32;
	let mut byte_offset = 0;
	for ch in source.chars() {
		if line == position.line {
			break;
		}
		if ch == '\n' {
			line += 1;
		}
		byte_offset += ch.len_utf8();
	}
	if line < position.line {
		return None;
	}
	let rest = &source[byte_offset..];
	let line_text = rest.split('\n').next().unwrap_or(rest);
	Some(
		byte_offset
			+ utf16_offset_to_byte_offset(
				line_text,
				position.character as usize,
			),
	)
}

fn span_to_range(files: &vfs::Files, source: SourceSpan) -> Option<Range> {
	let start =
		byte_to_position(files, source.file_id, source.span.start as usize)?;
	let end =
		byte_to_position(files, source.file_id, source.span.end as usize)?;
	Some(Range { start, end })
}

fn byte_to_position(
	files: &vfs::Files,
	file_id: FileId,
	byte_index: usize,
) -> Option<Position> {
	let line = files.line_index(file_id, byte_index).ok()?;
	let line_range = files.line_range(file_id, line).ok()?;
	let source = files.source(file_id).ok()?;
	let prefix = &source[line_range.start..byte_index.min(line_range.end)];
	Some(Position {
		line: line as u32,
		character: byte_offset_to_utf16_offset(prefix) as u32,
	})
}

fn severity_to_lsp(severity: Severity) -> DiagnosticSeverity {
	match severity {
		Severity::Bug | Severity::Error => DiagnosticSeverity::ERROR,
		Severity::Warning => DiagnosticSeverity::WARNING,
		Severity::Note => DiagnosticSeverity::INFORMATION,
		Severity::Help => DiagnosticSeverity::HINT,
	}
}

/// Finds the project directory governing `file_path` — the nearest
/// ancestor (bounded by `workspace_folders`, when given) with a `wx.json`
/// — or `None` if there is no such ancestor. Returns the *directory*, not
/// an entry file: which file compilation actually starts from is
/// `wx.json`'s own `entry` field, resolved later by `vfs::open_manifest`,
/// not a filename convention this function would have to know about.
///
/// No special case for a file itself being named `main.wx` — that
/// convention doesn't exist anymore. Every file, `main.wx` or not,
/// belongs to a project only by virtue of a `wx.json` somewhere above it.
pub(crate) fn discover_package_root(
	open_documents: &HashMap<PathBuf, OpenDocument>,
	workspace_folders: &[PathBuf],
	file_path: &Path,
) -> Option<PathBuf> {
	let mut current = file_path.parent();
	while let Some(dir) = current {
		if !workspace_folders.is_empty()
			&& !workspace_folders.iter().any(|root| dir.starts_with(root))
		{
			current = dir.parent();
			continue;
		}

		let candidate = dir.join("wx.json");
		if open_documents.contains_key(&candidate) || candidate.exists() {
			return Some(dir.to_path_buf());
		}
		current = dir.parent();
	}

	None
}

fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
	uri.to_file_path().map(|cow| cow.into_owned())
}

/// Builds a `file://` URI directly from an absolute path, bypassing
/// `Uri::from_file_path`'s `Path::is_absolute()` gate — see `file_id_to_uri`
/// for why that gate is unusable on `wasm32-unknown-unknown`. Every call
/// site that turns one of our own `Local` paths into a URI must go through
/// this (or `file_id_to_uri`) instead of `Uri::from_file_path` directly.
fn path_to_file_uri(path: &Path) -> Option<Uri> {
	let stripped = path.to_str()?.strip_prefix('/')?;
	Uri::from_str(&format!("file:///{stripped}")).ok()
}

/// Converts a `FileId` to a URI: a `Local` file gets a `file://` URI, a
/// `Virtual` file (i.e. the stdlib) gets a `wx://std/<name>` URI.
///
/// Deliberately not `Uri::from_file_path`: it gates on `Path::is_absolute()`
/// to decide whether it can skip `canonicalize()` — and `is_absolute()` is
/// (surprisingly) always `false` on `wasm32-unknown-unknown` even for
/// `/`-rooted paths, so it always falls through to `canonicalize()`, which
/// needs a real filesystem and always fails in the browser. `name` is our
/// own virtual path, not necessarily a real OS path, so we don't need any of
/// that — dispatch on `FileOrigin` and build the URI directly.
fn file_id_to_uri(files: &vfs::Files, file_id: FileId) -> Option<Uri> {
	let file = files.get(file_id).ok()?;
	match file.origin {
		vfs::FileOrigin::Local => path_to_file_uri(Path::new(&file.name)),
		// `file.name` is already `/`-prefixed (the embedded stdlib's own
		// `AbsolutePath` convention, e.g. `/main.wx`), so no separator goes
		// between `wx://std` and it — `wx://std/main.wx`, not
		// `wx://std//main.wx`. `virtual_file_content`'s `strip_prefix("wx://std")`
		// expects exactly this: a leading-slash remainder it can feed
		// straight into `stdlib_file`/`AbsolutePath::new`.
		vfs::FileOrigin::Virtual => {
			Uri::from_str(&format!("wx://std{}", file.name)).ok()
		}
	}
}

#[cfg(test)]
mod tests;
