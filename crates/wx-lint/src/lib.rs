//! Lints: passes over a package the compiler checked without an error,
//! reporting what is valid but likely a mistake. Each lint has a name, the
//! key it is configured by in the `lint` section of `wx.json`, and a code
//! in the L3xxx range the compiler leaves to this crate.
//!
//! ```json
//! { "entry": "main.wx", "lint": { "unused_variable": "off" } }
//! ```

use std::collections::BTreeMap;

use codespan_reporting::diagnostic::{Diagnostic, Severity};
use wx_compiler::diagnostics::Diagnostics as _;
use wx_compiler::symbols::StringInterner;
use wx_compiler::tir::Semantics;
use wx_compiler::vfs::{CompilationUnit, FileId, PackageId};

mod unused;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[derive(serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Lint {
	/// A local never read.
	UnusedVariable,
	/// `mut` on a local never assigned.
	UnnecessaryMutability,
	/// A label no jump names.
	UnusedLabel,
}

impl Lint {
	pub const ALL: [Lint; 3] = [
		Lint::UnusedVariable,
		Lint::UnnecessaryMutability,
		Lint::UnusedLabel,
	];

	pub const fn code(self) -> &'static str {
		match self {
			Lint::UnusedVariable => "L3000",
			Lint::UnnecessaryMutability => "L3001",
			Lint::UnusedLabel => "L3002",
		}
	}

	pub fn from_code(code: &str) -> Option<Self> {
		Self::ALL.into_iter().find(|lint| lint.code() == code)
	}
}

/// What a lint reports as, ordered from quietest to strictest.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
#[derive(serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Level {
	Off,
	#[default]
	Warn,
	Error,
}

/// The level of every lint, from the `lint` section of `wx.json`. A lint
/// the section does not name keeps its default level.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct LintConfig {
	levels: [Level; Lint::ALL.len()],
}

impl LintConfig {
	/// Reads the `lint` section of a manifest's text, ignoring every other
	/// key. An unknown lint name or level is an error.
	pub fn from_manifest(manifest: &str) -> Result<Self, serde_json::Error> {
		#[derive(serde::Deserialize)]
		struct Manifest {
			#[serde(default)]
			lint: BTreeMap<Lint, Level>,
		}
		let manifest: Manifest = serde_json::from_str(manifest)?;
		let mut config = Self::default();
		for (lint, level) in manifest.lint {
			config.levels[lint as usize] = level;
		}
		Ok(config)
	}

	pub fn level(self, lint: Lint) -> Level {
		self.levels[lint as usize]
	}

	/// Lowers every lint stricter than `cap` to `cap`, as for a build that
	/// cares less about lints than the manifest does.
	pub fn capped(self, cap: Level) -> Self {
		Self {
			levels: self.levels.map(|level| level.min(cap)),
		}
	}

	/// What `lint` reports as, or `None` when it is off.
	pub fn severity(self, lint: Lint) -> Option<Severity> {
		match self.level(lint) {
			Level::Off => None,
			Level::Warn => Some(Severity::Warning),
			Level::Error => Some(Severity::Error),
		}
	}
}

/// Lints the bodies declared in `package`. Nothing is reported when loading
/// or checking reported an error: a failed path records only its resolved
/// prefix, so a local can look unused when it is not.
pub fn lint(
	compilation: &CompilationUnit,
	sema: &Semantics,
	strings: &StringInterner,
	package: PackageId,
	config: LintConfig,
) -> Vec<Diagnostic<FileId>> {
	if compilation.has_errors()
		|| sema.diagnostics().has_errors()
		|| Lint::ALL
			.into_iter()
			.all(|lint| config.level(lint) == Level::Off)
	{
		return Vec::new();
	}
	let mut diagnostics = Vec::new();
	unused::report_unused(&mut diagnostics, config, sema, strings, package);
	diagnostics
}
