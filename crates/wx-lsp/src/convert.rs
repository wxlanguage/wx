//! Conversions between the compiler's byte spans and the protocol's
//! UTF-16 positions, URIs and severities.

use std::path::{Path, PathBuf};
use std::str::FromStr;

use codespan_reporting::diagnostic::Severity;
use codespan_reporting::files::Files as _;
use tower_lsp_server::ls_types::{DiagnosticSeverity, Position, Range, Uri};
use wx_compiler::diagnostics::SourceSpan;
use wx_compiler::vfs::{self, FileId};

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
pub(crate) fn utf16_offset_to_byte_offset(
	line: &str,
	utf16_offset: usize,
) -> usize {
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
pub(crate) fn byte_offset_to_utf16_offset(prefix: &str) -> usize {
	if prefix.is_ascii() {
		return prefix.len();
	}
	prefix.chars().map(char::len_utf16).sum()
}

pub(crate) fn position_to_offset(
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

pub(crate) fn span_to_range(
	files: &vfs::Files,
	source: SourceSpan,
) -> Option<Range> {
	let start =
		byte_to_position(files, source.file_id, source.span.start as usize)?;
	let end =
		byte_to_position(files, source.file_id, source.span.end as usize)?;
	Some(Range { start, end })
}

pub(crate) fn byte_to_position(
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

pub(crate) fn severity_to_lsp(severity: Severity) -> DiagnosticSeverity {
	match severity {
		Severity::Bug | Severity::Error => DiagnosticSeverity::ERROR,
		Severity::Warning => DiagnosticSeverity::WARNING,
		Severity::Note => DiagnosticSeverity::INFORMATION,
		Severity::Help => DiagnosticSeverity::HINT,
	}
}

pub(crate) fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
	uri.to_file_path().map(|cow| cow.into_owned())
}

/// Builds a `file://` URI directly from an absolute path, bypassing
/// `Uri::from_file_path`'s `Path::is_absolute()` gate — see `file_id_to_uri`
/// for why that gate is unusable on `wasm32-unknown-unknown`. Every call
/// site that turns one of our own `Local` paths into a URI must go through
/// this (or `file_id_to_uri`) instead of `Uri::from_file_path` directly.
pub(crate) fn path_to_file_uri(path: &Path) -> Option<Uri> {
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
pub(crate) fn file_id_to_uri(
	files: &vfs::Files,
	file_id: FileId,
) -> Option<Uri> {
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
