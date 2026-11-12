//! One analysed package root: everything a request needs, built together and
//! replaced together.
//!
//! The interner is the snapshot's own, so every identity in it (files,
//! declarations, symbols) is local to this one build.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};

use tower_lsp_server::ls_types::Uri;
use wx_compiler::diagnostics::{SourceSpan, TextSpan};
use wx_compiler::symbols::{Keyword, StringInterner};
use wx_compiler::tir::{self, Definition, Semantics};
use wx_compiler::vfs::{self, AbsolutePath, FileId, FileSource as _};

use crate::convert::file_id_to_uri;
use crate::diagnostics::{AnalysisResult, add_compiler_diagnostic};
use crate::documents::{OpenDocument, OverlayFileSource};
use crate::projects::{ManifestState, ProjectState};
use crate::trace::Trace;

pub(crate) struct Snapshot {
	pub(crate) compilation: vfs::CompilationUnit,
	pub(crate) strings: StringInterner,
	pub(crate) sema: Semantics,
	/// Every declared name, by where it is written.
	definitions: BTreeMap<SourceSpan, Definition>,
}

impl Snapshot {
	/// Loads and checks the package at `root`. `Err` when the manifest or
	/// the entry file cannot be read; every other problem is a diagnostic.
	pub(crate) fn build(
		open_documents: &HashMap<PathBuf, OpenDocument>,
		projects: &mut HashMap<PathBuf, ProjectState>,
		root: &Path,
		trace: &mut Trace,
	) -> Result<Self, ()> {
		let mut strings = Keyword::create_interner();
		let compilation = load_compilation(
			open_documents,
			projects,
			root,
			&mut strings,
			trace,
		)?;
		let sema =
			trace.step("check", || tir::check(&compilation, &mut strings));
		let definitions = sema.definitions();
		Ok(Self {
			compilation,
			strings,
			sema,
			definitions,
		})
	}

	/// The name written at `offset` in `file`, whether it uses a declaration
	/// or declares one, and what it means: the name's span and its
	/// declaration. `None` when no resolved or declared name is written there.
	pub(crate) fn definition_at(
		&self,
		file: FileId,
		offset: u32,
	) -> Option<(SourceSpan, Definition)> {
		if let Some((span, reference)) = self.sema.symbol_at(file, offset) {
			return Some((span, reference.definition()));
		}
		let probe = SourceSpan::new(
			file,
			TextSpan {
				start: offset,
				end: u32::MAX,
			},
		);
		let (&span, &definition) =
			self.definitions.range(..=probe).next_back()?;
		(span.file_id == file && offset <= span.span.end)
			.then_some((span, definition))
	}

	/// Every declared name written in `file`, in source order.
	pub(crate) fn definitions_in(
		&self,
		file: FileId,
	) -> impl Iterator<Item = (SourceSpan, Definition)> + '_ {
		let start = SourceSpan::new(file, TextSpan { start: 0, end: 0 });
		self.definitions
			.range(start..)
			.take_while(move |(span, _)| span.file_id == file)
			.map(|(&span, &definition)| (span, definition))
	}

	/// What the name written at exactly `span` declares, if it declares
	/// anything.
	pub(crate) fn declared_at(&self, span: SourceSpan) -> Option<Definition> {
		self.definitions.get(&span).copied()
	}

	/// The file `uri` names in this snapshot. Matched by rebuilding each
	/// module's URI rather than converting `uri` to a path, since a path
	/// conversion accepts a `wx://core/...` URI and returns a bogus path.
	pub(crate) fn file_for(&self, uri: &Uri) -> Option<FileId> {
		self.compilation
			.packages
			.iter()
			.flat_map(|package| package.modules.iter())
			.find(|module| {
				file_id_to_uri(&self.compilation.files, module.file_id)
					.is_some_and(|candidate| candidate.as_str() == uri.as_str())
			})
			.map(|module| module.file_id)
	}

	/// Each file's diagnostics (loading's, then checking's), and the local
	/// files this root reaches.
	pub(crate) fn analysis(&self) -> AnalysisResult {
		let files = &self.compilation.files;
		let mut diagnostics_by_file = HashMap::new();
		let mut owned_files = HashSet::new();
		for package in &self.compilation.packages {
			for module in &package.modules {
				let Ok(file) = files.get(module.file_id) else {
					continue;
				};
				if file.origin == vfs::FileOrigin::Local {
					owned_files
						.insert(PathBuf::from(module.file_path.as_str()));
				}
			}
		}
		let diagnostics = self.compilation.collect_diagnostics();
		for diagnostic in diagnostics.iter().chain(self.sema.diagnostics()) {
			add_compiler_diagnostic(
				&mut diagnostics_by_file,
				files,
				diagnostic,
			);
		}
		AnalysisResult {
			diagnostics_by_file,
			owned_files,
		}
	}
}

/// Parses source modules fresh from the live overlay while reusing retained
/// project manifests. First discovery loads metadata eagerly; subsequent
/// source edits and format requests do not read or parse those manifests.
/// Missing/unreadable manifests or entry files fail loading; other compiler
/// diagnostics remain on the returned graph.
pub(crate) fn load_compilation(
	open_documents: &HashMap<PathBuf, OpenDocument>,
	projects: &mut HashMap<PathBuf, ProjectState>,
	root: &Path,
	strings: &mut StringInterner,
	trace: &mut Trace,
) -> std::result::Result<vfs::CompilationUnit, ()> {
	let overlay = OverlayFileSource::new(open_documents);
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
		vfs::open_manifest_with_manifests(root, &overlay, &manifests, strings)
	})
}
