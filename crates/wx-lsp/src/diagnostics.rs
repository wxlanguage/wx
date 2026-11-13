//! Compiler diagnostics as protocol diagnostics, and the publication diff.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use codespan_reporting::diagnostic::{
	Diagnostic as CodeDiagnostic, Label, LabelStyle,
};
use tower_lsp_server::ls_types::{
	Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity,
	DiagnosticTag, Location, NumberOrString, Position, Range, Uri,
};
use wx_compiler::diagnostics::{SourceSpan, TextSpan};
use wx_compiler::vfs::{self, FileId};

use crate::convert::{
	file_id_to_uri, path_to_file_uri, severity_to_lsp, span_to_range,
};

/// What analysing one root found: each file's diagnostics, and every local
/// file the root reaches (so a file that stops being reported is cleared).
pub(crate) struct AnalysisResult {
	pub(crate) diagnostics_by_file: HashMap<PathBuf, Vec<Diagnostic>>,
	pub(crate) owned_files: HashSet<PathBuf>,
}

/// The result for a root whose manifest cannot be parsed or whose entry file
/// cannot be read: the one failure that is not a diagnostic of the graph.
pub(crate) fn analysis_from_missing_entry_file(root: &Path) -> AnalysisResult {
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
pub(crate) fn orphan_file_diagnostic() -> Diagnostic {
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
/// `None` if the label's file is `Virtual` (true for the core's `wx://core/...`
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
pub(crate) fn diagnostic_locations(
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

pub(crate) fn add_compiler_diagnostic(
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
