use std::collections::HashMap;

use codespan_reporting::diagnostic::{Diagnostic, Severity};
use indoc::indoc;
use wx_compiler::diagnostics::Diagnostics as _;
use wx_compiler::symbols::Keyword;
use wx_compiler::tir;
use wx_compiler::vfs::{self, FileId};

use crate::{Level, Lint, LintConfig};

/// Lints `source`, the root package's only file, at `config`'s levels.
fn lint_with(source: &str, config: LintConfig) -> Vec<Diagnostic<FileId>> {
	let mut strings = Keyword::create_interner();
	let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
	builder.load_core();
	let workspace = vfs::VirtualFileSource::new(HashMap::from([(
		vfs::AbsolutePath::new("/main.wx"),
		source.to_string(),
	)]));
	let root = builder
		.load_package(vfs::AbsolutePath::new("/main.wx"), &workspace)
		.unwrap();
	let compilation = builder.build(root);
	let sema = tir::check(&compilation, &mut strings);
	crate::lint(&compilation, &sema, &strings, root, config)
}

/// Each lint reported, with the text it points at.
fn lints(source: &str) -> Vec<(Lint, &str)> {
	lint_with(source, LintConfig::default())
		.iter()
		.map(|diagnostic| {
			let code = diagnostic.code.as_deref().expect("a lint has a code");
			let range = diagnostic.labels[0].range.clone();
			(
				Lint::from_code(code).expect("a lint's code"),
				&source[range],
			)
		})
		.collect()
}

#[test]
fn a_local_or_parameter_never_read_is_reported() {
	let source = indoc! {"
		func f(a: u32, b: u32) -> u32 {
			local x: u32 = 1;
			local y: u32 = 2;
			local P(c, d) = P(1, 2);
			match (b) { n => {} }
			b + y + c
		}
		struct P(c: u32, d: u32);
	"};
	assert_eq!(
		lints(source),
		[
			(Lint::UnusedVariable, "a"),
			(Lint::UnusedVariable, "x"),
			(Lint::UnusedVariable, "d"),
			(Lint::UnusedVariable, "n"),
		]
	);
}

#[test]
fn assigning_or_compound_assigning_is_not_a_read() {
	let source = indoc! {"
		func f() {
			local mut assigned: u32 = 0;
			assigned = 1;
			local mut accumulated: u32 = 0;
			accumulated += 1;
		}
	"};
	assert_eq!(
		lints(source),
		[
			(Lint::UnusedVariable, "assigned"),
			(Lint::UnusedVariable, "accumulated")
		]
	);
	let diagnostics = lint_with(source, LintConfig::default());
	assert_eq!(
		diagnostics[0].message,
		"`assigned` is assigned but never read"
	);
}

#[test]
fn dropping_a_local_uses_it() {
	let source = indoc! {"
		func f(unused: u32) {
			_ = unused;
		}
	"};
	assert_eq!(lints(source), []);
}

#[test]
fn mut_on_a_local_never_assigned_is_reported() {
	let source = indoc! {"
		func f(mut a: u32) -> u32 {
			local mut b: u32 = 1;
			local mut c: u32 = 2;
			c += 1;
			local mut d: u32 = 3;
			d = 4;
			a + b + c + d
		}
	"};
	let starts: Vec<_> = lint_with(source, LintConfig::default())
		.iter()
		.map(|diagnostic| {
			assert_eq!(
				diagnostic.code.as_deref(),
				Some(Lint::UnnecessaryMutability.code())
			);
			diagnostic.labels[0].range.start
		})
		.collect();
	assert_eq!(
		starts,
		[source.find("mut a").unwrap(), source.find("mut b").unwrap()]
	);
}

#[test]
fn only_a_write_into_its_own_storage_needs_mut() {
	// A field chain from a local writes the local; a write through a pointer
	// it holds, by a field step or an index, writes memory and reads it.
	let source = indoc! {"
		memory heap: u32;
		struct Inner(mut value: u32);
		struct Outer(mut inner: Inner, pointer: heap::*Inner);
		func f(
			mut owned: Outer,
			mut holder: Outer,
			mut pointer: heap::*Outer,
			mut slice: heap::*[u32; 4],
			n: u32,
		) {
			owned.inner.value = n;
			holder.pointer.value = n;
			pointer.inner.value += n;
			slice[0] = n;
			_ = owned;
		}
	"};
	assert_eq!(
		lints(source),
		[
			(Lint::UnnecessaryMutability, "mut"),
			(Lint::UnnecessaryMutability, "mut"),
			(Lint::UnnecessaryMutability, "mut"),
		]
	);
	let starts: Vec<_> = lint_with(source, LintConfig::default())
		.iter()
		.map(|diagnostic| diagnostic.labels[0].range.start)
		.collect();
	assert_eq!(
		starts,
		[
			source.find("mut holder").unwrap(),
			source.find("mut pointer").unwrap(),
			source.find("mut slice").unwrap(),
		]
	);
}

#[test]
fn mut_on_a_private_field_never_written_in_place_is_reported() {
	// `chain` and `pointed` are written in place, through a local and through
	// a pointer. A `Pair` is only replaced as a whole value, which writes none
	// of its fields; `unused` is not written at all. A public field may be
	// written by another package.
	let source = indoc! {"
		memory heap: u32;
		struct Inner(mut pointed: u32, mut chain: u32);
		struct Pair(mut first: u32, mut second: u32);
		struct Outer(mut inner: Inner, mut unused: u32, pub mut open: u32);
		func f(mut o: Outer, p: heap::*Inner, q: heap::*Pair) -> u32 {
			o.inner.chain = 1;
			p.pointed += 2;
			local mut pair = Pair(3, 4);
			pair = Pair(5, 6);
			q.* = pair;
			o.inner.chain + o.unused + o.open
		}
	"};
	let reported: Vec<_> = lint_with(source, LintConfig::default())
		.iter()
		.map(|diagnostic| {
			(diagnostic.message.clone(), diagnostic.labels[0].range.start)
		})
		.collect();
	let expected = |field: &str| {
		(
			format!("field `{field}` does not need to be mutable"),
			source.find(&format!("mut {field}")).unwrap(),
		)
	};
	assert_eq!(
		reported,
		[expected("first"), expected("second"), expected("unused")]
	);
}

#[test]
fn a_label_no_jump_names_is_reported() {
	let source = indoc! {"
		func f() {
			loop :unused { break; }
			block :also_unused { }
			loop :left { break :left; }
			loop :restarted (i: u32 = 0) {
				if (i == 3) { break };
				loop { continue :restarted(i + 1); }
			}
		}
	"};
	assert_eq!(
		lints(source),
		[
			(Lint::UnusedLabel, "unused"),
			(Lint::UnusedLabel, "also_unused")
		]
	);
}

#[test]
fn a_receiver_is_not_reported() {
	let source = indoc! {"
		struct S();
		impl S {
			func ignore(self: Self) {}
		}
	"};
	assert_eq!(lints(source), []);
}

#[test]
fn nothing_is_reported_after_an_error() {
	let source = indoc! {"
		func f() -> u32 {
			local unused: u32 = 1;
			missing
		}
	"};
	assert_eq!(lints(source), []);
}

#[test]
fn nothing_is_reported_after_a_parse_error() {
	assert_eq!(lints("func f() { local unused: u32 = 1; ) }"), []);
}

#[test]
fn only_the_selected_package_is_reported() {
	let mut strings = Keyword::create_interner();
	let name = strings.get_or_intern("dep");
	let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
	builder.load_core();
	let workspace = vfs::VirtualFileSource::new(HashMap::from([
		(
			vfs::AbsolutePath::new("/main.wx"),
			indoc! {"
				package \"dep\" as dep;
				func main() -> u32 { dep::helper() }
			"}
			.to_string(),
		),
		(
			vfs::AbsolutePath::new("/dep.wx"),
			"pub func helper() -> u32 { local unused: u32 = 1; 2 }".to_string(),
		),
	]));
	let dep = builder
		.load_package(vfs::AbsolutePath::new("/dep.wx"), &workspace)
		.unwrap();
	let root = builder
		.load_package(vfs::AbsolutePath::new("/main.wx"), &workspace)
		.unwrap();
	builder.add_dependency(root, name, dep);
	let compilation = builder.build(root);
	let sema = tir::check(&compilation, &mut strings);
	assert!(!sema.diagnostics().has_errors());
	let config = LintConfig::default();
	assert_eq!(crate::lint(&compilation, &sema, &strings, root, config), []);
	assert_eq!(
		crate::lint(&compilation, &sema, &strings, dep, config).len(),
		1
	);
}

#[test]
fn a_lint_reports_at_its_configured_level() {
	let source = indoc! {"
		func f() {
			local unused: u32 = 1;
			loop :never { break; }
		}
	"};
	let config = LintConfig::from_manifest(
		r#"{ "lint": { "unused_variable": "error", "unused_label": "off" } }"#,
	)
	.unwrap();
	let diagnostics = lint_with(source, config);
	assert_eq!(diagnostics.len(), 1);
	assert_eq!(diagnostics[0].severity, Severity::Error);
	assert_eq!(
		diagnostics[0].code.as_deref(),
		Some(Lint::UnusedVariable.code())
	);
}

#[test]
fn a_manifest_without_a_lint_section_warns_for_every_lint() {
	let config =
		LintConfig::from_manifest(r#"{ "entry": "main.wx" }"#).unwrap();
	assert_eq!(config, LintConfig::default());
	for lint in Lint::ALL {
		assert_eq!(config.level(lint), Level::Warn);
		assert_eq!(config.severity(lint), Some(Severity::Warning));
	}
}

#[test]
fn a_lint_section_names_only_known_lints_and_levels() {
	for manifest in [
		r#"{ "lint": { "unused_import": "off" } }"#,
		r#"{ "lint": { "unused_variable": "allow" } }"#,
		r#"{ "lint": [] }"#,
	] {
		assert!(LintConfig::from_manifest(manifest).is_err(), "{manifest}");
	}
}

#[test]
fn a_cap_lowers_only_stricter_lints() {
	let config = LintConfig::from_manifest(
		r#"{ "lint": { "unused_variable": "error", "unused_label": "off" } }"#,
	)
	.unwrap();
	let capped = config.capped(Level::Warn);
	assert_eq!(capped.level(Lint::UnusedVariable), Level::Warn);
	assert_eq!(capped.level(Lint::UnnecessaryMutability), Level::Warn);
	assert_eq!(capped.level(Lint::UnusedLabel), Level::Off);
	assert_eq!(config.capped(Level::Error), config);
	for lint in Lint::ALL {
		assert_eq!(config.capped(Level::Off).level(lint), Level::Off);
	}
}

#[test]
fn nothing_is_reported_when_every_lint_is_off() {
	let source = "func f() { local unused: u32 = 1; }";
	let config = LintConfig::default().capped(Level::Off);
	assert_eq!(lint_with(source, config), []);
}

#[test]
fn each_lint_has_its_own_code() {
	for lint in Lint::ALL {
		assert_eq!(Lint::from_code(lint.code()), Some(lint));
		assert_eq!(Lint::ALL[lint as usize], lint);
	}
}
