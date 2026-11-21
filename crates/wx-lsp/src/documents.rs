//! Open editor buffers, and the file source that prefers them over disk.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use wx_compiler::vfs::{self, AbsolutePath, FileSource, NativeFileSource};

/// An editor buffer: its text and the version the client last sent for it,
/// which versioned diagnostics are published against.
#[derive(Clone)]
pub(crate) struct OpenDocument {
	pub(crate) text: String,
	pub(crate) version: i32,
}

pub(crate) struct OverlayFileSource<'a> {
	open_documents: &'a HashMap<PathBuf, OpenDocument>,
	native: NativeFileSource,
}

impl<'a> OverlayFileSource<'a> {
	pub(crate) fn new(
		open_documents: &'a HashMap<PathBuf, OpenDocument>,
	) -> Self {
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
