//! The server's state, and how an event turns into published diagnostics.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use wx_compiler::vfs::{self, AbsolutePath, FileSource as _};

use tower_lsp_server::ls_types::{Diagnostic, Uri};
use wx_compiler::vfs::FileId;

use crate::convert::uri_to_path;
use crate::diagnostics::{
	AnalysisResult, analysis_from_missing_entry_file, diagnostic_publish_paths,
	orphan_file_diagnostic,
};
use crate::documents::OpenDocument;
use crate::documents::OverlayFileSource;
use crate::projects::{ManifestState, ProjectState, discover_package_root};
use crate::snapshot::Snapshot;
use crate::trace::Trace;

/// What the client says about itself at `initialize`, applied once, before
/// anything else.
#[derive(Default)]
pub(crate) struct ClientConfig {
	pub(crate) workspace_folders: Vec<PathBuf>,
	/// Whether the client accepts `workspace/semanticTokens/refresh`.
	pub(crate) semantic_tokens_refresh: bool,
	/// Whether the client takes snippets in completion items.
	pub(crate) completion_snippets: bool,
}

#[derive(Default)]
pub(crate) struct ServerState {
	pub(crate) client: ClientConfig,
	pub(crate) open_documents: HashMap<PathBuf, OpenDocument>,
	/// One snapshot per package root, rebuilt whole on every event that can
	/// change it. Invalidation belongs on the event, not on the read.
	pub(crate) cached: HashMap<PathBuf, Snapshot>,
	/// Persistent manifest and publication state, independent of snapshots.
	/// Dependency-only entries do not become active analysis roots.
	pub(crate) projects: HashMap<PathBuf, ProjectState>,
	/// file -> the root `discover_package_root` returned for it, as of the
	/// last refresh that re-resolved its ownership. This is "what is file
	/// F's own project", never derived from the publication map ("which
	/// files does root R reach", many-to-many).
	pub(crate) own_root: HashMap<PathBuf, PathBuf>,
}

impl ServerState {
	/// The snapshot a request for `uri` is answered from, and the file in
	/// it. The file's own project wins; a file only reached as another
	/// package's dependency (or the core) is taken from the first root in
	/// path order that reaches it, so the choice never depends on hash
	/// order.
	pub(crate) fn resolve_uri(&self, uri: &Uri) -> Option<(&Snapshot, FileId)> {
		let own = uri_to_path(uri)
			.and_then(|path| self.own_root.get(&path))
			.and_then(|root| self.cached.get(root));
		let mut roots: Vec<_> = self.cached.iter().collect();
		roots.sort_by(|a, b| a.0.cmp(b.0));
		own.into_iter()
			.chain(roots.into_iter().map(|(_, snapshot)| snapshot))
			.find_map(|snapshot| {
				let file = snapshot.file_for(uri)?;
				Some((snapshot, file))
			})
	}
}

/// Apply a manifest event independently of compilation, including edits whose
/// rebuild will be skipped as superseded. Never replace editor text with disk.
pub(crate) fn refresh_project_manifest(
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
/// the largest example here is ~10ms with process start, core, and codegen
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
pub(crate) fn compute_active_refresh(
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
			&state.client.workspace_folders,
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
			&state.client.workspace_folders,
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
	let snapshot = Snapshot::build(
		&state.open_documents,
		&mut state.projects,
		root,
		&mut trace,
	);
	logs.push(trace.finish("typecheck"));
	match snapshot {
		Ok(snapshot) => {
			let result = snapshot.analysis();
			state.cached.insert(root.to_path_buf(), snapshot);
			result
		}
		Err(()) => {
			state.cached.remove(root);
			analysis_from_missing_entry_file(root)
		}
	}
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
