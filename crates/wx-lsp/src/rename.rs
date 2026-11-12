//! Renaming a declaration and every name that refers to it, in the package
//! graph of the file's own snapshot.
//!
//! The occurrences are the compiler's: the declaration's name
//! (`Semantics::definition_span`) and every resolved use of it
//! (`Semantics::references_to`). Only those written as the declared name are
//! rewritten, so an alias (`use geo::Point as P`), `Self` and a keyword that
//! resolves to the declaration keep their spelling. Three occurrences are
//! rewritten as more than the new name:
//! - a shorthand, one name for a label and a value (`f({ x })`, `P({ x })`
//!   in a construction or a pattern), is expanded so the other side keeps
//!   its name: `f({ new: x })` for the label, `f({ x: new })` for the value;
//! - an export entry with no `as` keeps its Wasm name: `new as "old"`;
//! - a host import with no field name keeps the field it is imported as:
//!   `"old": func new(..)`.
//!
//! What cannot be renamed is refused with the reason: a keyword, a
//! declaration of the standard library, a package, and a module in a file
//! of its own (its file would have to be renamed too).

use std::collections::HashMap;

use tower_lsp_server::ls_types::{
	PrepareRenameResponse, RenameParams, TextDocumentPositionParams, TextEdit,
	Uri, WorkspaceEdit,
};
use wx_compiler::diagnostics::{SourceSpan, TextSpan};
use wx_compiler::symbols::Keyword;
use wx_compiler::tir::{DeclKind, Definition, Reference};
use wx_compiler::vfs::{FileId, FileOrigin};

use crate::convert::{file_id_to_uri, position_to_offset, span_to_range};
use crate::snapshot::Snapshot;
use crate::state::ServerState;

/// The range of the name under the cursor, when it can be renamed.
pub(crate) fn prepare(
	state: &ServerState,
	params: &TextDocumentPositionParams,
) -> Result<Option<PrepareRenameResponse>, String> {
	let Some((snapshot, file)) = state.resolve_uri(&params.text_document.uri)
	else {
		return Ok(None);
	};
	let Some(target) = target(snapshot, file, params)? else {
		return Ok(None);
	};
	Ok(span_to_range(&snapshot.compilation.files, target.name)
		.map(PrepareRenameResponse::Range))
}

/// The edits that rename the declaration under the cursor to `new_name`.
pub(crate) fn rename(
	state: &ServerState,
	params: &RenameParams,
) -> Result<Option<WorkspaceEdit>, String> {
	let position = &params.text_document_position;
	let Some((snapshot, file)) = state.resolve_uri(&position.text_document.uri)
	else {
		return Ok(None);
	};
	let Some(target) = target(snapshot, file, position)? else {
		return Ok(None);
	};
	let new = params.new_name.as_str();
	if !is_identifier(new) {
		return Err(format!("`{new}` is not an identifier"));
	}
	if Keyword::try_from(new).is_ok() {
		return Err(format!("`{new}` is a keyword"));
	}

	let sema = &snapshot.sema;
	let files = &snapshot.compilation.files;
	let old = target.old.as_str();
	let old_symbol = snapshot.strings.get(old);
	let mut spans = sema.references_to(target.definition);
	spans.push(target.declaration);
	spans.sort_unstable();
	spans.dedup();

	let mut changes: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
	let mut edit = |span: SourceSpan, new_text: String| {
		if let (Some(uri), Some(range)) = (
			file_id_to_uri(files, span.file_id),
			span_to_range(files, span),
		) {
			changes
				.entry(uri)
				.or_default()
				.push(TextEdit { range, new_text });
		}
	};
	// A host import that writes no field is imported as its name: keep it.
	if let Definition::Item(loc) = target.definition
		&& let Some(entry) = sema.decls.import_entry(loc)
		&& entry.field.span == target.declaration.span
	{
		let start = entry.span.start;
		edit(
			SourceSpan::new(
				target.declaration.file_id,
				TextSpan { start, end: start },
			),
			format!("\"{old}\": "),
		);
	}
	for span in spans {
		if text(snapshot, span) != Some(old) {
			continue;
		}
		let new_text = match shorthand_side(snapshot, span, target.definition) {
			Some(Side::Label) => format!("{new}: {old}"),
			Some(Side::Value) => format!("{old}: {new}"),
			None if old_symbol.is_some_and(|symbol| {
				sema.exported_under_own_name(symbol, span)
			}) =>
			{
				format!("{new} as \"{old}\"")
			}
			None => new.to_string(),
		};
		edit(span, new_text);
	}
	Ok(Some(WorkspaceEdit {
		changes: Some(changes),
		..Default::default()
	}))
}

/// What a rename at the cursor renames.
struct Target {
	/// The name under the cursor.
	name: SourceSpan,
	definition: Definition,
	/// Where the declaration's name is written.
	declaration: SourceSpan,
	/// The declared name.
	old: String,
}

/// The declaration named under the cursor; `Err` with the reason when it
/// cannot be renamed, `Ok(None)` when no name is there.
fn target(
	snapshot: &Snapshot,
	file: FileId,
	position: &TextDocumentPositionParams,
) -> Result<Option<Target>, String> {
	let sema = &snapshot.sema;
	let files = &snapshot.compilation.files;
	let Some(offset) = position_to_offset(files, file, position.position)
	else {
		return Ok(None);
	};
	let Some((name, definition)) = snapshot.definition_at(file, offset) else {
		return Ok(None);
	};
	let written = text(snapshot, name).unwrap_or_default();
	if Keyword::try_from(written).is_ok() {
		return Err(format!("`{written}` is a keyword"));
	}
	let declaration = sema
		.definition_span(definition)
		.filter(|span| span.span.start != span.span.end)
		.ok_or_else(|| format!("`{written}` has no name of its own"))?;
	let old = text(snapshot, declaration).unwrap_or_default().to_string();
	if files
		.get(declaration.file_id)
		.is_ok_and(|file| file.origin == FileOrigin::Virtual)
	{
		return Err(format!("`{old}` is declared in the standard library"));
	}
	if let Definition::Item(key) = definition
		&& let DeclKind::Package(_) = sema.declaration_kind(key)
	{
		return Err(format!(
			"`{written}` is a package, named by its dependency key in wx.json"
		));
	}
	// Go-to-definition leads to a module's own file instead of its name.
	if sema.definition_target(definition) != Some(declaration) {
		return Err(format!(
			"`{old}` is a module in a file of its own, which renaming does \
			 not move yet"
		));
	}
	if written != old {
		return Err(format!(
			"`{written}` names `{old}` through an alias; rename `{old}` instead"
		));
	}
	Ok(Some(Target {
		name,
		definition,
		declaration,
		old,
	}))
}

/// Which side of a shorthand the renamed declaration is, at a name that is
/// one.
enum Side {
	/// The parameter or field it names: `f({ x })` is `f({ x: x })`.
	Label,
	/// The value it supplies, or the local a pattern binds.
	Value,
}

/// The side of a shorthand `definition` is at `span`, or `None` when the
/// name there means only `definition`. A shorthand is a name that also
/// means something else, a field or a parameter on one side.
fn shorthand_side(
	snapshot: &Snapshot,
	span: SourceSpan,
	definition: Definition,
) -> Option<Side> {
	let sema = &snapshot.sema;
	let (mut ours_label, mut other, mut other_label) = (false, false, false);
	for reference in sema.references_at(span) {
		let label = matches!(
			reference,
			Reference::Field { .. } | Reference::Parameter { .. }
		);
		if sema.same_definition(reference.definition(), definition) {
			ours_label |= label;
		} else {
			other = true;
			other_label |= label;
		}
	}
	// A pattern's shorthand binds a local where it names the field.
	if snapshot
		.declared_at(span)
		.is_some_and(|declared| !sema.same_definition(declared, definition))
	{
		other = true;
	}
	match (other, ours_label, other_label) {
		(true, true, _) => Some(Side::Label),
		(true, false, true) => Some(Side::Value),
		_ => None,
	}
}

fn text(snapshot: &Snapshot, span: SourceSpan) -> Option<&str> {
	let source = &snapshot.compilation.files.get(span.file_id).ok()?.source;
	source.get(span.span.start as usize..span.span.end as usize)
}

/// Whether `name` is written as an identifier is: an ASCII letter or `_`,
/// then letters, digits and `_`.
fn is_identifier(name: &str) -> bool {
	let mut chars = name.chars();
	chars
		.next()
		.is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
		&& chars.all(|rest| rest.is_ascii_alphanumeric() || rest == '_')
}
