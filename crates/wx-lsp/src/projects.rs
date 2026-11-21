//! Packages: their manifests and which package governs a file.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use wx_compiler::vfs;

use crate::documents::OpenDocument;

/// Source edits retain this state; manifest events replace the parse result.
/// Invalid manifests remain project boundaries. Removing a manifest from both
/// disk and the editor removes the project after its publications are cleared.
pub(crate) struct ProjectState {
	pub(crate) manifest: Manifest,
	pub(crate) published_files: HashSet<PathBuf>,
}

/// Each tool's view of one `wx.json`, parsed independently: `None` is a
/// section that is invalid, or a manifest that could not be read. The
/// default is a manifest none of whose sections parsed.
#[derive(Default)]
pub(crate) struct Manifest {
	pub(crate) package: Option<vfs::PackageManifest>,
	pub(crate) format: Option<wx_fmt::RendererConfig>,
	pub(crate) lint: Option<wx_lint::LintConfig>,
}

impl Manifest {
	pub(crate) fn parse(text: &str) -> Self {
		Self {
			package: vfs::PackageManifest::parse(text).ok(),
			format: wx_fmt::RendererConfig::from_manifest(text).ok(),
			lint: wx_lint::LintConfig::from_manifest(text).ok(),
		}
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
