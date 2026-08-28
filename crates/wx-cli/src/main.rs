use std::fs;
use std::io::Write;

use codespan_reporting::diagnostic::{Diagnostic, Severity};
use codespan_reporting::files::Files as _;
use codespan_reporting::term;
use codespan_reporting::term::DisplayStyle;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use wx_compiler::*;

mod format;

fn main() {
	let message_format = clap::Arg::new("message-format")
		.long("message-format")
		.value_name("FMT")
		.value_parser(clap::builder::PossibleValuesParser::new([
			clap::builder::PossibleValue::new("human"),
			clap::builder::PossibleValue::new("short"),
			clap::builder::PossibleValue::new("json"),
		]))
		.default_value("human");

	let matches = clap::Command::new("wx")
		.name("wx")
		.author(clap::crate_authors!())
		.version(clap::crate_version!())
		.subcommand_required(true)
		.arg_required_else_help(true)
		.subcommand(
			clap::Command::new("build")
				.about("Build a WX project to WebAssembly")
				.arg(
					clap::Arg::new("path")
						.help("The project directory to build (default: .)")
						.default_value("."),
				)
				.arg(
					clap::Arg::new("output")
						.short('o')
						.long("output")
						.value_name("PATH")
						.help(
							"Output path for the compiled .wasm; use `-` \
							 for stdout (default: <project-dir-name>.wasm)",
						),
				)
				.arg(message_format.clone()),
		)
		.subcommand(
			clap::Command::new("check")
				.about("Type-check a WX project without emitting output")
				.arg(
					clap::Arg::new("path")
						.help("The project directory to check (default: .)")
						.default_value("."),
				)
				.arg(message_format),
		)
		.subcommand(
			clap::Command::new("format")
				.visible_alias("fmt")
				.about("Format a WX project's source files in-place")
				.arg(
					clap::Arg::new("path")
						.help("The project directory to format (default: .)")
						.default_value("."),
				)
				.arg(
					clap::Arg::new("files")
						.long("files")
						.value_name("FILE,FILE,...")
						.value_delimiter(',')
						.help(
							"Format only these files, relative to the \
							 project root, instead of the whole project",
						),
				)
				.arg(
					clap::Arg::new("check")
						.long("check")
						.action(clap::ArgAction::SetTrue)
						.help(
							"Check formatting without writing; exit \
							 nonzero if any file would change",
						),
				),
		)
		.subcommand(
			clap::Command::new("lsp")
				.about("Start the WX language server over stdio"),
		)
		.get_matches();

	match matches.subcommand() {
		Some(("build", sub)) => {
			let path = sub.get_one::<String>("path").unwrap();
			let output = sub.get_one::<String>("output").map(String::as_str);
			let format = parse_message_format(
				sub.get_one::<String>("message-format").unwrap(),
			);
			cmd_build(path, output, format);
		}
		Some(("check", sub)) => {
			let path = sub.get_one::<String>("path").unwrap();
			let format = parse_message_format(
				sub.get_one::<String>("message-format").unwrap(),
			);
			cmd_check(path, format);
		}
		Some(("format", sub)) => {
			let path = sub.get_one::<String>("path").unwrap();
			let files: Option<Vec<String>> = sub
				.get_many::<String>("files")
				.map(|values| values.cloned().collect());
			let check = sub.get_flag("check");
			cmd_format(path, files.as_deref(), check);
		}
		Some(("lsp", _)) => cmd_lsp(),
		_ => unreachable!(),
	}
}

/// The other subcommands are synchronous; only this one needs an async
/// runtime, so it builds one for itself rather than making `main` async.
/// Current-thread is enough — `tower_lsp_server::Server` schedules its own
/// request concurrency independent of the runtime's thread count.
fn cmd_lsp() {
	tokio::runtime::Builder::new_current_thread()
		.build()
		.unwrap()
		.block_on(wx_lsp::run_stdio(tokio::io::stdin(), tokio::io::stdout()));
}

enum MessageFormat {
	Text(DisplayStyle),
	Json,
}

fn parse_message_format(s: &str) -> MessageFormat {
	match s {
		"json" => MessageFormat::Json,
		"medium" => MessageFormat::Text(DisplayStyle::Medium),
		"short" => MessageFormat::Text(DisplayStyle::Short),
		_ => MessageFormat::Text(DisplayStyle::Rich),
	}
}

/// One diagnostic label resolved to a human-facing line/column, for JSON output.
#[derive(serde::Serialize)]
struct JsonLabel {
	style: &'static str,
	file: String,
	line: usize,
	column: usize,
	message: String,
}

/// A single diagnostic in `--message-format=json` output. One JSON object
/// per line (NDJSON), matching `rustc --error-format=json`'s convention.
#[derive(serde::Serialize)]
struct JsonDiagnostic {
	severity: &'static str,
	code: Option<String>,
	message: String,
	labels: Vec<JsonLabel>,
	notes: Vec<String>,
}

fn severity_str(severity: Severity) -> &'static str {
	match severity {
		Severity::Bug => "bug",
		Severity::Error => "error",
		Severity::Warning => "warning",
		Severity::Note => "note",
		Severity::Help => "help",
	}
}

fn diagnostic_to_json(
	files: &vfs::Files,
	d: &Diagnostic<vfs::FileId>,
) -> JsonDiagnostic {
	let labels = d
		.labels
		.iter()
		.map(|label| {
			let file = files
				.name(label.file_id)
				.map(str::to_string)
				.unwrap_or_default();
			let location = files
				.location(label.file_id, label.range.start)
				.unwrap_or(codespan_reporting::files::Location {
					line_number: 0,
					column_number: 0,
				});
			JsonLabel {
				style: match label.style {
					codespan_reporting::diagnostic::LabelStyle::Primary => {
						"primary"
					}
					codespan_reporting::diagnostic::LabelStyle::Secondary => {
						"secondary"
					}
				},
				file,
				line: location.line_number,
				column: location.column_number,
				message: label.message.clone(),
			}
		})
		.collect();

	JsonDiagnostic {
		severity: severity_str(d.severity),
		code: d.code.clone(),
		message: d.message.clone(),
		labels,
		notes: d.notes.clone(),
	}
}

/// Resolves a CLI-provided file path to an absolute one, joining it
/// against the process's current directory if the user typed a relative
/// path — every `FileSource` consumer works with `AbsolutePath` only, so
/// this is the one place that has to make that true for whatever the user
/// actually typed.
///
/// Known gap: only checks for a leading `/`, so a Windows drive-letter
/// absolute path (`C:\...`) would incorrectly be treated as relative and
/// joined onto the cwd instead of used as-is.
fn resolve_cli_path(file_path: &str) -> vfs::AbsolutePath {
	if file_path.starts_with('/') {
		return vfs::AbsolutePath::new(file_path);
	}
	let cwd = std::env::current_dir()
		.expect("current directory should be accessible");
	vfs::AbsolutePath::new(cwd.to_string_lossy().into_owned())
		.join(&vfs::RelativePath::new(file_path))
}

/// Loads the project rooted at `path` — always a directory with a readable
/// `wx.json`/`entry`. There's no anonymous, manifest-less mode any more
/// than `wx format` has one; every file `build`/`check` touches belongs to
/// a project.
fn load_compilation(path: &str) -> vfs::CompilationUnit {
	let absolute = resolve_cli_path(path);
	match vfs::open_manifest(absolute, &vfs::NativeFileSource) {
		Ok(compilation) => compilation,
		Err(()) => {
			eprintln!(
				"error: '{path}' is not a wx project (no readable \
				 `wx.json`/`entry`)"
			);
			std::process::exit(1);
		}
	}
}

/// Emits every diagnostic in `diagnostics` to stderr in the given format.
/// Does not inspect severity — call `abort_if_errors` separately, after all
/// diagnostics across every stage have been emitted.
fn emit_diagnostics(
	compilation: &vfs::CompilationUnit,
	diagnostics: &[Diagnostic<vfs::FileId>],
	format: &MessageFormat,
) {
	match format {
		MessageFormat::Json => {
			let stderr = std::io::stderr();
			let mut lock = stderr.lock();
			for d in diagnostics {
				let json = diagnostic_to_json(&compilation.files, d);
				writeln!(lock, "{}", serde_json::to_string(&json).unwrap())
					.unwrap();
			}
		}
		MessageFormat::Text(style) => {
			let writer = StandardStream::stderr(ColorChoice::Always);
			let config = term::Config {
				display_style: style.clone(),
				..term::Config::default()
			};
			for d in diagnostics {
				term::emit_to_write_style(
					&mut writer.lock(),
					&config,
					&compilation.files,
					d,
				)
				.unwrap();
			}
		}
	}
}

/// Prints a rustc-style summary and exits the process if `count` is nonzero.
#[inline]
fn abort_if_errors(count: usize) {
	if count == 0 {
		return;
	}
	let noun = if count == 1 { "error" } else { "errors" };
	eprintln!("error: aborting due to {count} previous {noun}");
	std::process::exit(1);
}

fn cmd_build(project_path: &str, output: Option<&str>, format: MessageFormat) {
	let mut compilation = load_compilation(project_path);

	if compilation.packages[compilation.root_package.as_usize()].kind
		== vfs::PackageKind::Library
	{
		eprintln!(
			"error: '{project_path}' is a library package and has no WASM \
			 output to emit; use `wx check` instead"
		);
		std::process::exit(1);
	}

	for package_graph in &compilation.packages {
		emit_diagnostics(
			&compilation,
			&package_graph.linker_diagnostics,
			&format,
		);
		for module in &package_graph.modules {
			emit_diagnostics(&compilation, &module.ast.diagnostics, &format);
		}
	}
	abort_if_errors(
		compilation
			.packages
			.iter()
			.flat_map(|package_graph| {
				package_graph.linker_diagnostics.iter().chain(
					package_graph
						.modules
						.iter()
						.flat_map(|module| module.ast.diagnostics.iter()),
				)
			})
			.filter(|d| matches!(d.severity, Severity::Error | Severity::Bug))
			.count(),
	);

	let tir = tir::TIR::build(&mut compilation);
	emit_diagnostics(&compilation, &tir.diagnostics, &format);
	abort_if_errors(
		tir.diagnostics
			.iter()
			.filter(|d| matches!(d.severity, Severity::Error | Severity::Bug))
			.count(),
	);

	let mir =
		mir::MIR::build(&tir, &compilation.interner, compilation.id_generator);
	let module = codegen::Builder::build(&mir, &compilation.interner).unwrap();
	let bytecode = module.encode();

	if output == Some("-") {
		std::io::stdout().write_all(&bytecode).unwrap();
		return;
	}

	let out_path = match output {
		Some(path) => path.to_string(),
		None => format!("{}.wasm", output_stem(project_path)),
	};
	let mut file = fs::File::create(&out_path).unwrap();
	file.write_all(&bytecode).unwrap();
	eprintln!("Wrote {} bytes to {out_path}", bytecode.len());
}

fn cmd_check(project_path: &str, format: MessageFormat) {
	let mut compilation = load_compilation(project_path);

	for package_graph in &compilation.packages {
		emit_diagnostics(
			&compilation,
			&package_graph.linker_diagnostics,
			&format,
		);
		for module in &package_graph.modules {
			emit_diagnostics(&compilation, &module.ast.diagnostics, &format);
		}
	}
	abort_if_errors(
		compilation
			.packages
			.iter()
			.flat_map(|package_graph| {
				package_graph.linker_diagnostics.iter().chain(
					package_graph
						.modules
						.iter()
						.flat_map(|module| module.ast.diagnostics.iter()),
				)
			})
			.filter(|d| matches!(d.severity, Severity::Error | Severity::Bug))
			.count(),
	);

	let tir = tir::TIR::build(&mut compilation);
	emit_diagnostics(&compilation, &tir.diagnostics, &format);
	abort_if_errors(
		tir.diagnostics
			.iter()
			.filter(|d| matches!(d.severity, Severity::Error | Severity::Bug))
			.count(),
	);

	println!("No errors found.");
}

/// Resolves an explicit `--manifest <path>` into a `RendererConfig` once,
/// up front, for the whole invocation. Unlike a directory argument's own
/// `wx.json` (opportunistic — falls through to the next config rule on any
/// failure), this is an explicit ask: a bad or missing `--manifest` is a
/// hard error, not a silent fallback.
fn cmd_format(project_path: &str, files: Option<&[String]>, check: bool) {
	let project_dir = resolve_cli_path(project_path);
	let selection = match format::expand_project(
		&project_dir,
		files,
		&vfs::NativeFileSource,
	) {
		Ok(selection) => selection,
		Err(()) => {
			eprintln!(
				"error: '{project_path}' is not a wx project (no \
					 readable `wx.json`/`entry`, or a file named by \
					 `--files` could not be read)"
			);
			std::process::exit(1);
		}
	};

	let mut any_error = false;
	let mut any_would_change = false;

	for module in &selection.modules {
		// `Parser::parse` is error-recovering — it always returns *an*
		// AST, never a hard failure, so a syntax error alone wouldn't stop
		// this loop otherwise. That's the right call for `compile`/
		// `check`, which only report and abort; `format` overwrites the
		// file in place, so rendering and writing a recovered, error-laden
		// AST back over the original would silently corrupt it instead.
		if module
			.ast
			.diagnostics
			.iter()
			.any(|d| matches!(d.severity, Severity::Error | Severity::Bug))
		{
			eprintln!(
				"error: '{}' has syntax errors, skipping (run `wx check \
				 {}` for details)",
				module.file_path, module.file_path
			);
			any_error = true;
			continue;
		}

		let file = selection.files.get(module.file_id).unwrap();
		let formatted = wx_fmt::format(
			&module.ast,
			&selection.interner,
			&file.source,
			selection.config,
		);

		if formatted == file.source {
			continue;
		}
		if check {
			println!("Would reformat {}", module.file_path);
			any_would_change = true;
		} else {
			fs::write(module.file_path.as_str(), &formatted).unwrap();
			println!("Formatted {}", module.file_path);
		}
	}

	if any_error || (check && any_would_change) {
		std::process::exit(1);
	}
}

/// Derives a default output filename from the project's own directory
/// name — `path` is always a directory now, so there's no file extension
/// to strip the way there used to be. Resolved to an absolute path first
/// so `.`/`./` name the real directory rather than becoming a literal `.`.
fn output_stem(path: &str) -> String {
	let absolute = resolve_cli_path(path);
	absolute
		.as_str()
		.rsplit('/')
		.find(|segment| !segment.is_empty())
		.unwrap_or("out")
		.to_string()
}
