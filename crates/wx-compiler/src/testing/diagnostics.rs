//! Assertions over one compilation stage's diagnostics.
//!
//! Parsing, module/package linking and type checking each report into their
//! own `Vec<Diagnostic<FileId>>`, but the questions tests ask of them are the
//! same two: "did this compile clean" and "was this code reported". Sharing
//! one vocabulary here is what stops those questions being re-invented per
//! suite — `tir/tests.rs` alone grew two spellings of "no errors"
//! (`no_errors` and `assert_no_errors`) defined 7,600 lines apart, alongside
//! 76 hand-rolled `diagnostics.is_empty()` calls that print nothing at all
//! when they fail.
//!
//! Every assertion here renders what it actually found, with source context,
//! into the panic message. A failing test should say what the compiler
//! reported, not merely that it was surprised.

use codespan_reporting::diagnostic::{Diagnostic, Severity};
use codespan_reporting::term;

use crate::diagnostics::{Code, Diagnostics};
use crate::vfs::{FileId, Files};

/// A view over one stage's diagnostics, paired with the [`Files`] they point
/// into so failures can be rendered with source context.
///
/// `stage` names the stage in panic messages ("parse", "link", "check"). With
/// three stages reporting into the same `FileId` space, "expected E1015" is a
/// good deal less useful than "expected E1015 during check".
///
/// Borrows throughout — a stage whose diagnostics are not already in one
/// place (linker diagnostics live per package, parse diagnostics per module)
/// gathers them into a `Vec` first and views that. Where the allocation
/// happens is the caller's business, not this type's.
pub struct DiagnosticView<'a> {
	stage: &'static str,
	items: &'a [Diagnostic<FileId>],
	files: &'a Files,
}

impl<'a> DiagnosticView<'a> {
	pub fn new(
		stage: &'static str,
		items: &'a [Diagnostic<FileId>],
		files: &'a Files,
	) -> Self {
		DiagnosticView {
			stage,
			items,
			files,
		}
	}

	/// Every diagnostic, whatever its severity.
	pub fn all(&self) -> &'a [Diagnostic<FileId>] {
		self.items
	}

	/// Delegates to [`Diagnostics::errors`], so "counts as an error" means
	/// the same here as it does to `wx check` — `Bug` included, since it is
	/// strictly worse than an error and slipping one past an "expected no
	/// errors" assertion would be actively misleading.
	pub fn errors(&self) -> impl Iterator<Item = &'a Diagnostic<FileId>> {
		self.items.errors()
	}

	pub fn warnings(&self) -> impl Iterator<Item = &'a Diagnostic<FileId>> {
		self.items
			.iter()
			.filter(|d| d.severity == Severity::Warning)
	}

	/// The code of every diagnostic, in report order.
	pub fn codes(&self) -> Vec<&'a str> {
		self.items
			.iter()
			.filter_map(|d| d.code.as_deref())
			.collect()
	}

	pub fn is_empty(&self) -> bool {
		self.items.is_empty()
	}

	// ── assertions ──────────────────────────────────────────────────────

	/// Nothing was reported at all, warnings included.
	pub fn assert_none(&self) {
		if !self.items.is_empty() {
			panic!(
				"expected no {} diagnostics, found {}:\n{}",
				self.stage,
				self.items.len(),
				self.render(self.items.iter()),
			);
		}
	}

	/// No errors. Warnings are allowed through: most sources under test
	/// legitimately produce them (an unread field, an unused local), and a
	/// test about something else should not have to care.
	pub fn assert_no_errors(&self) {
		let errors: Vec<_> = self.errors().collect();
		if !errors.is_empty() {
			panic!(
				"expected no {} errors, found {}:\n{}",
				self.stage,
				errors.len(),
				self.render(errors.into_iter()),
			);
		}
	}

	/// At least one *error* carrying `code`.
	pub fn assert_error(&self, code: impl Code) {
		self.assert_reported_inner(
			code.as_code(),
			Some(Severity::Error),
			"error",
		);
	}

	/// At least one *warning* carrying `code`.
	///
	/// Severity is genuinely checked here, unlike the `has_error_code` helper
	/// this replaces: that matched on the code alone, so the ~20 warning tests
	/// using it would have kept passing had the warning been promoted to an
	/// error.
	pub fn assert_warning(&self, code: impl Code) {
		self.assert_reported_inner(
			code.as_code(),
			Some(Severity::Warning),
			"warning",
		);
	}

	/// At least one diagnostic carrying `code`, whatever its severity.
	pub fn assert_reported(&self, code: impl Code) {
		self.assert_reported_inner(code.as_code(), None, "diagnostic");
	}

	/// Nothing carries `code`, whatever its severity.
	pub fn assert_absent(&self, code: impl Code) {
		let wanted = code.as_code();
		if self.items.iter().any(|d| d.code.as_deref() == Some(wanted)) {
			panic!(
				"expected no `{}` during {}, but it was reported:\n{}",
				wanted,
				self.stage,
				self.render(self.items.iter()),
			);
		}
	}

	/// An error whose message, or one of its notes, contains `substring`.
	pub fn assert_error_saying(&self, substring: &str) {
		let found = self.errors().any(|d| {
			d.message.contains(substring)
				|| d.notes.iter().any(|note| note.contains(substring))
		});
		if !found {
			panic!(
				"expected a {} error mentioning {:?}, found {}:\n{}",
				self.stage,
				substring,
				self.describe_count(),
				self.render(self.items.iter()),
			);
		}
	}

	/// The exact codes reported, in order.
	///
	/// Stronger than [`Self::assert_error`], which says nothing about whatever
	/// else the compiler decided to report alongside the expected one. This is
	/// `ast/tests.rs`'s existing `diagnostic_codes` idiom, generalised.
	pub fn assert_codes(&self, expected: &[impl Code]) {
		let expected: Vec<&str> =
			expected.iter().map(|code| code.as_code()).collect();
		let actual = self.codes();
		if actual != expected {
			panic!(
				"expected {} diagnostics {:?}, found {:?}:\n{}",
				self.stage,
				expected,
				actual,
				self.render(self.items.iter()),
			);
		}
	}

	// ── internals ───────────────────────────────────────────────────────

	fn assert_reported_inner(
		&self,
		wanted: &str,
		severity: Option<Severity>,
		noun: &str,
	) {
		let found = self.items.iter().any(|d| {
			d.code.as_deref() == Some(wanted)
				&& severity.is_none_or(|expected| d.severity == expected)
		});
		if !found {
			panic!(
				"expected {} `{}` during {}, found {}:\n{}",
				noun,
				wanted,
				self.stage,
				self.describe_count(),
				self.render(self.items.iter()),
			);
		}
	}

	fn describe_count(&self) -> String {
		match self.items.len() {
			0 => "none".to_string(),
			count => format!("{count} diagnostic(s)"),
		}
	}

	/// Renders with source context, so a failure shows the offending line
	/// rather than only a code and a message.
	fn render(
		&self,
		diagnostics: impl Iterator<Item = &'a Diagnostic<FileId>>,
	) -> String {
		let config = term::Config::default();
		let mut out = String::new();
		for diagnostic in diagnostics {
			match term::emit_into_string(&config, self.files, diagnostic) {
				Ok(rendered) => out.push_str(&rendered),
				// A span pointing outside its file is itself worth seeing, so
				// fall back to the bare message rather than panicking here and
				// masking whatever the test was actually asserting.
				Err(error) => out.push_str(&format!(
					"<unrenderable {:?}: {}: {error}>\n",
					diagnostic.code, diagnostic.message,
				)),
			}
		}
		out
	}
}

#[cfg(test)]
mod tests {
	use codespan_reporting::diagnostic::Diagnostic;

	use super::*;
	use crate::tir::DiagnosticCode;
	use crate::vfs::FileOrigin;

	/// One file plus a diagnostic per requested (code, severity), all pointing
	/// at the same span so rendering has something real to resolve.
	fn fixture(
		specs: &[(DiagnosticCode, Severity)],
	) -> (Files, Vec<Diagnostic<FileId>>) {
		let mut files = Files::new();
		let file_id = files
			.add(
				"main.wx".to_string(),
				"fn f() {}".to_string(),
				FileOrigin::Local,
			)
			.unwrap();
		let items = specs
			.iter()
			.map(|(code, severity)| {
				Diagnostic::new(*severity)
					.with_code(code.code())
					.with_message(format!("synthetic {}", code.code()))
					.with_label(codespan_reporting::diagnostic::Label::primary(
						file_id,
						0..2,
					))
			})
			.collect();
		(files, items)
	}

	fn view<'a>(
		files: &'a Files,
		items: &'a [Diagnostic<FileId>],
	) -> DiagnosticView<'a> {
		DiagnosticView::new("check", items, files)
	}

	fn fails(assertion: impl FnOnce() + std::panic::UnwindSafe) -> String {
		let hook = std::panic::take_hook();
		std::panic::set_hook(Box::new(|_| {}));
		let result = std::panic::catch_unwind(assertion);
		std::panic::set_hook(hook);
		let payload = result.expect_err("expected the assertion to fail");
		payload
			.downcast_ref::<String>()
			.cloned()
			.unwrap_or_else(|| "<non-string panic>".to_string())
	}

	#[test]
	fn no_errors_passes_when_only_warnings_were_reported() {
		let (files, items) =
			fixture(&[(DiagnosticCode::UnusedVariable, Severity::Warning)]);
		view(&files, &items).assert_no_errors();
	}

	#[test]
	fn no_errors_fails_and_renders_the_offending_source() {
		let (files, items) =
			fixture(&[(DiagnosticCode::PrivateItem, Severity::Error)]);
		let message = fails(|| view(&files, &items).assert_no_errors());
		assert!(message.contains("expected no check errors"), "{message}");
		// the whole point: the failure shows the source, not just a bool
		assert!(message.contains("fn f() {}"), "{message}");
	}

	#[test]
	fn bug_severity_counts_as_an_error() {
		let (files, items) =
			fixture(&[(DiagnosticCode::PrivateItem, Severity::Bug)]);
		let message = fails(|| view(&files, &items).assert_no_errors());
		assert!(message.contains("expected no check errors"), "{message}");
	}

	#[test]
	fn assert_error_distinguishes_severity_from_code() {
		// Same code, but reported as a warning: `assert_error` must not accept
		// it. This is exactly what the `has_error_code` helper it replaces got
		// wrong.
		let (files, items) =
			fixture(&[(DiagnosticCode::UnusedVariable, Severity::Warning)]);
		let message = fails(|| {
			view(&files, &items).assert_error(DiagnosticCode::UnusedVariable)
		});
		assert!(message.contains("expected error"), "{message}");
		view(&files, &items).assert_warning(DiagnosticCode::UnusedVariable);
		view(&files, &items).assert_reported(DiagnosticCode::UnusedVariable);
	}

	#[test]
	fn assert_absent_rejects_a_reported_code() {
		let (files, items) =
			fixture(&[(DiagnosticCode::PrivateItem, Severity::Error)]);
		view(&files, &items).assert_absent(DiagnosticCode::UnusedVariable);
		let message = fails(|| {
			view(&files, &items).assert_absent(DiagnosticCode::PrivateItem)
		});
		assert!(message.contains("but it was reported"), "{message}");
	}

	#[test]
	fn assert_codes_is_exact_and_ordered() {
		let (files, items) = fixture(&[
			(DiagnosticCode::PrivateItem, Severity::Error),
			(DiagnosticCode::UnusedVariable, Severity::Warning),
		]);
		view(&files, &items).assert_codes(&[
			DiagnosticCode::PrivateItem,
			DiagnosticCode::UnusedVariable,
		]);
		// order matters
		let message = fails(|| {
			view(&files, &items).assert_codes(&[
				DiagnosticCode::UnusedVariable,
				DiagnosticCode::PrivateItem,
			])
		});
		assert!(message.contains("expected check diagnostics"), "{message}");
		// and so does the full set: a subset is not enough
		let message = fails(|| {
			view(&files, &items).assert_codes(&[DiagnosticCode::PrivateItem])
		});
		assert!(message.contains("expected check diagnostics"), "{message}");
	}

	#[test]
	fn assert_error_saying_matches_message_and_notes() {
		let mut files = Files::new();
		let file_id = files
			.add(
				"main.wx".to_string(),
				"fn f() {}".to_string(),
				FileOrigin::Local,
			)
			.unwrap();
		let items = vec![
			Diagnostic::error()
				.with_code(DiagnosticCode::PrivateItem.code())
				.with_message("something went wrong")
				.with_notes(vec!["consider adding `pub`".to_string()])
				.with_label(codespan_reporting::diagnostic::Label::primary(
					file_id,
					0..2,
				)),
		];
		view(&files, &items).assert_error_saying("went wrong");
		view(&files, &items).assert_error_saying("consider adding");
		let message =
			fails(|| view(&files, &items).assert_error_saying("absent phrase"));
		assert!(message.contains("mentioning"), "{message}");
	}

	#[test]
	fn assert_none_rejects_even_a_warning() {
		let (files, items) =
			fixture(&[(DiagnosticCode::UnusedVariable, Severity::Warning)]);
		let message = fails(|| view(&files, &items).assert_none());
		assert!(
			message.contains("expected no check diagnostics"),
			"{message}"
		);
		let (files, items) = fixture(&[]);
		view(&files, &items).assert_none();
	}
}
