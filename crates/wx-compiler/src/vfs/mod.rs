use std::collections::HashMap;
use std::fs;
use std::path::Path;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files;
use string_interner::symbol::SymbolU32;

use crate::ast;

mod manifest;
pub use manifest::{DependencySource, PackageManifest, PackageManifestKind};

mod resolve;
pub use resolve::{open_package, package_kind};

mod path;
pub use path::{AbsolutePath, RelativePath};

// Diagnostic codes for this stage (resolving `module foo;` declarations to
// files and wiring up the package graph — closer to a linker than a parser or
// type checker). Follows the same per-stage numbering convention as
// `ast::DiagnosticCode` (E0xxx) and `tir::DiagnosticCode` (E1xxx).
macro_rules! define_diagnostic_codes {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $variant:ident => $code:literal,
            )*
        }
    ) => {
        $(#[$meta])*
        $vis enum $name {
            $($variant,)*
        }

        impl $name {
            pub const fn code(&self) -> &'static str {
                match self {
                    $(Self::$variant => $code,)*
                }
            }
        }

        impl std::str::FromStr for $name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($code => Ok(Self::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str(self.code())
            }
        }
    };
}

define_diagnostic_codes! {
	pub enum DiagnosticCode {
		ModuleFileNotFound => "E2000",
		AmbiguousModuleFile => "E2001",
		DuplicatePackageName => "E2002",
		CircularDependency => "E2003",
	}
}

#[cfg(test)]
mod tests;

/// Which kind of backend produced a file's content. This is what an editor
/// actually needs to know to address the file: a `Local` file has a real
/// location on disk and can be opened directly via `file://`; a `Virtual`
/// file has no such location (today: the embedded stdlib; potentially a
/// future remote-fetched dependency) and must instead be served through our
/// own `wx://` scheme. Deliberately binary rather than e.g. a third "remote"
/// variant — from the editor's addressing perspective there are only ever
/// these two cases.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum FileOrigin {
	Local,
	Virtual,
}

pub trait FileSource {
	fn read_to_string(&self, path: &AbsolutePath) -> Result<String, ()>;
	fn exists(&self, path: &AbsolutePath) -> bool;
	/// Which [`FileOrigin`] every file read through this source should be
	/// tagged with — no default, so a new `FileSource` impl has to make this
	/// call explicitly rather than silently inheriting `Local`.
	fn origin(&self) -> FileOrigin;
}

pub struct NativeFileSource;

impl FileSource for NativeFileSource {
	fn read_to_string(&self, path: &AbsolutePath) -> Result<String, ()> {
		fs::read_to_string(Path::new(path.as_str())).map_err(|_| ())
	}

	fn exists(&self, path: &AbsolutePath) -> bool {
		Path::new(path.as_str()).exists()
	}

	fn origin(&self) -> FileOrigin {
		FileOrigin::Local
	}
}

pub struct VirtualFileSource {
	files: HashMap<AbsolutePath, String>,
}

impl VirtualFileSource {
	pub fn new(files: HashMap<AbsolutePath, String>) -> Self {
		Self { files }
	}

	/// Builds from a plain, relative-keyed map — e.g. a fixture written as
	/// `HashMap::from([("main.wx".to_string(), source)])` — prepending `/`
	/// to every key to satisfy `AbsolutePath`'s invariant. Strips any
	/// leading `/` a key might already have first, so it's safe to call
	/// regardless of whether the fixture already followed the convention.
	/// Test-only: production callers (e.g. `wx-compiler-wasm`, deserializing
	/// from JS) are expected to already produce `AbsolutePath`-keyed data
	/// themselves, same as every other frontend.
	#[cfg(test)]
	pub(crate) fn from_relative(files: HashMap<String, String>) -> Self {
		Self {
			files: files
				.into_iter()
				.map(|(path, source)| {
					(
						AbsolutePath::new(format!(
							"/{}",
							path.trim_start_matches('/')
						)),
						source,
					)
				})
				.collect(),
		}
	}

	pub fn insert(
		&mut self,
		path: AbsolutePath,
		source: String,
	) -> Option<String> {
		self.files.insert(path, source)
	}
}

impl FileSource for VirtualFileSource {
	fn read_to_string(&self, path: &AbsolutePath) -> Result<String, ()> {
		self.files.get(path).cloned().ok_or(())
	}

	fn exists(&self, path: &AbsolutePath) -> bool {
		self.files.contains_key(path)
	}

	fn origin(&self) -> FileOrigin {
		FileOrigin::Virtual
	}
}

#[derive(Clone)]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct File {
	pub name: String,
	pub source: String,
	pub origin: FileOrigin,
	line_starts: Vec<usize>,
}

impl File {
	fn line_start(&self, line_index: usize) -> Result<usize, files::Error> {
		match line_index.cmp(&self.line_starts.len()) {
			core::cmp::Ordering::Less => Ok(*self
				.line_starts
				.get(line_index)
				.expect("failed despite previous check")),
			core::cmp::Ordering::Equal => Ok(self.source.len()),
			core::cmp::Ordering::Greater => Err(files::Error::LineTooLarge {
				given: line_index,
				max: self.line_starts.len() - 1,
			}),
		}
	}
}

#[cfg_attr(debug_assertions, derive(Debug))]
#[derive(Copy, Clone, PartialEq, Eq, serde::Serialize)]
pub struct FileId(u32);

#[cfg_attr(test, derive(serde::Serialize))]
pub struct Files {
	files: Vec<File>,
}

impl Default for Files {
	fn default() -> Self {
		Self::new()
	}
}

impl Files {
	pub fn new() -> Files {
		Files { files: Vec::new() }
	}

	pub fn add(
		&mut self,
		name: String,
		source: String,
		origin: FileOrigin,
	) -> Option<FileId> {
		let file_id = FileId(u32::try_from(self.files.len()).ok()?);
		let line_starts = files::line_starts(&source).collect();

		self.files.push(File {
			name,
			line_starts,
			source,
			origin,
		});

		Some(file_id)
	}

	pub fn get(&self, file_id: FileId) -> Result<&File, files::Error> {
		self.files
			.get(file_id.0 as usize)
			.ok_or(files::Error::FileMissing)
	}

	pub fn update(&mut self, file_id: FileId, source: String) {
		if let Some(file) = self.files.get_mut(file_id.0 as usize) {
			file.line_starts = files::line_starts(&source).collect();
			file.source = source;
		}
	}
}

impl<'files> files::Files<'files> for Files {
	type FileId = FileId;
	type Name = &'files str;
	type Source = &'files str;

	fn name(&'files self, file_id: FileId) -> Result<Self::Name, files::Error> {
		Ok(self.get(file_id)?.name.as_ref())
	}

	fn source(
		&'files self,
		file_id: FileId,
	) -> Result<Self::Source, files::Error> {
		Ok(&self.get(file_id)?.source)
	}

	fn line_index(
		&self,
		file_id: FileId,
		byte_index: usize,
	) -> Result<usize, files::Error> {
		self.get(file_id)?
			.line_starts
			.binary_search(&byte_index)
			.or_else(|next_line| Ok(next_line - 1))
	}

	fn line_range(
		&self,
		file_id: FileId,
		line_index: usize,
	) -> Result<core::ops::Range<usize>, files::Error> {
		let file = self.get(file_id)?;
		let line_start = file.line_start(line_index)?;
		let next_line_start = file.line_start(line_index + 1)?;

		Ok(line_start..next_line_start)
	}
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct ModuleId(u32);

impl ModuleId {
	#[inline]
	pub fn as_u32(self) -> u32 {
		self.0
	}

	#[inline]
	pub fn as_usize(self) -> usize {
		self.0 as usize
	}
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct PackageId(u32);

impl PackageId {
	#[inline]
	pub fn as_u32(self) -> u32 {
		self.0
	}

	#[inline]
	pub fn as_usize(self) -> usize {
		self.0 as usize
	}
}

pub struct SourceModule {
	pub package_id: PackageId,
	pub id: ModuleId,
	pub parent: Option<ModuleId>,
	pub children: Vec<ModuleId>,
	/// Intra-package path segment declared by `module foo;`. `None` for the package
	/// root — root items need no qualifier (`add`, not `root::add`).
	pub name: Option<SymbolU32>,
	pub file_id: FileId,
	pub file_path: AbsolutePath,
	pub ast: ast::AST,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PackageKind {
	/// Produces a WASM module and cannot be imported; has no name.
	Binary,
	/// Importable under `name` (`std` in `std::Memory`) — a library always
	/// has a name, so this is carried on the variant rather than as a
	/// separate `Option` that every reader would have to re-check.
	Library { name: SymbolU32 },
}

pub struct PackageGraph {
	pub id: PackageId,
	pub root: ModuleId,
	pub kind: PackageKind,
	pub entry_path: AbsolutePath,
	pub modules: Vec<SourceModule>,
	pub linker_diagnostics: Vec<Diagnostic<FileId>>,
	pub path_to_module: HashMap<AbsolutePath, ModuleId>,
}

pub struct CompilationUnit {
	pub files: Files,
	pub packages: Vec<PackageGraph>,
	/// Every package that successfully claimed a name, keyed by that name.
	/// Maintained by [`CompilationUnitBuilder::load_package`] itself (the
	/// one place a package's name is decided), so it's always complete and
	/// correct regardless of which frontend built this compilation —
	/// there's no separate resolution-time bookkeeping to keep in sync.
	pub package_by_name: HashMap<SymbolU32, PackageId>,
	pub root_package: PackageId,
	pub id_generator: ast::DefIdGenerator,
	pub interner: ast::StringInterner,
}

pub struct CompilationUnitBuilder {
	pub files: Files,
	pub id_generator: ast::DefIdGenerator,
	pub interner: ast::StringInterner,
	pub packages: Vec<PackageGraph>,
	pub package_by_name: HashMap<SymbolU32, PackageId>,
}

/// Every `.wx` file under `std/`, embedded at build time as
/// `("/"-prefixed path relative to `std/`, source)` and sorted by path.
/// Generated by `build.rs` — see there for why this is a directory walk
/// rather than a hand-maintained list, and why the path is `/`-prefixed
/// (matching `AbsolutePath`'s convention so `load_stdlib` can wrap each
/// entry directly, with no runtime string-patching to make it absolute).
///
/// The un-prefixed remainder is exactly the key the module resolver looks
/// up, so `std/math/mod.wx` appears here as `/math/mod.wx`, which is what a
/// `module math;` declaration in `main.wx` resolves to.
pub const STDLIB_FILES: &[(&str, &str)] =
	include!(concat!(env!("OUT_DIR"), "/stdlib_files.rs"));

/// The source of one embedded stdlib file, keyed as in [`STDLIB_FILES`] —
/// `path` must already be `/`-prefixed (e.g. `AbsolutePath::new("/math/mod.wx")`),
/// same as every other consumer of this convention; the caller (serving
/// `wx://std/...` documents to the editor) is responsible for constructing
/// one, same as any other frontend.
///
/// Used so go-to-definition can land inside the stdlib without it existing
/// on disk.
pub fn stdlib_file(path: &AbsolutePath) -> Option<&'static str> {
	STDLIB_FILES
		.iter()
		.find(|(name, _)| *name == path.as_str())
		.map(|(_, source)| *source)
}

impl Default for CompilationUnitBuilder {
	fn default() -> Self {
		Self::new()
	}
}

impl CompilationUnitBuilder {
	pub fn new() -> Self {
		Self {
			files: Files::new(),
			id_generator: ast::DefIdGenerator::new(),
			interner: ast::StringInterner::new(),
			packages: Vec::new(),
			package_by_name: HashMap::new(),
		}
	}

	/// Loads the stdlib as a named `std` package from its embedded sources.
	///
	/// Every file in [`STDLIB_FILES`] is handed to the loader up front, so the
	/// stdlib is an ordinary multi-file package from here on: `module foo;` in
	/// `main.wx` resolves against this map exactly as it would against the
	/// filesystem for a user package. Adding a stdlib file needs no change here.
	///
	/// The entry point is embedded, so this can never actually hit the "entry
	/// point unreadable" case `load_package` guards against.
	pub fn load_stdlib(&mut self) -> PackageId {
		let files: HashMap<AbsolutePath, String> = STDLIB_FILES
			.iter()
			.map(|(path, source)| {
				(AbsolutePath::new(*path), source.to_string())
			})
			.collect();
		self.load_library(
			"std",
			AbsolutePath::new("/main.wx"),
			&VirtualFileSource::new(files),
		)
		.expect("embedded stdlib source should always be readable")
	}

	#[inline]
	pub fn load_library(
		&mut self,
		name: &str,
		entry_path: AbsolutePath,
		file_source: &impl FileSource,
	) -> Result<PackageId, ()> {
		let name = self.interner.get_or_intern(name);
		self.load_package(
			PackageKind::Library { name },
			entry_path,
			file_source,
		)
	}

	#[inline]
	pub fn load_binary(
		&mut self,
		entry_path: AbsolutePath,
		file_source: &impl FileSource,
	) -> Result<PackageId, ()> {
		self.load_package(PackageKind::Binary, entry_path, file_source)
	}

	/// Loads a package starting from `entry_path`. Fails only if the entry
	/// point itself can't be read — there's no partial package to build
	/// without it. Everything past that point (missing/ambiguous `module`
	/// declarations) is recorded as a diagnostic instead of aborting, so one
	/// broken submodule doesn't take down the whole package.
	pub fn load_package(
		&mut self,
		kind: PackageKind,
		entry_path: AbsolutePath,
		file_source: &impl FileSource,
	) -> Result<PackageId, ()> {
		let package_id = PackageId(self.packages.len() as u32);
		let mut loader = Loader::new(self, package_id, file_source);
		let root = loader.load_module(entry_path.clone(), None, None)?;
		let mut package_graph = PackageGraph {
			id: package_id,
			kind,
			root,
			entry_path,
			modules: loader.modules,
			linker_diagnostics: loader.diagnostics,
			path_to_module: loader.path_to_module,
		};

		// This is the one place a package's name is decided, so it's the
		// one place that can both detect and diagnose two packages
		// claiming the same name — first claim wins (this is what makes
		// the implicit-`std` rule's override work: an explicit `"std"`
		// dependency just needs to load before the fallback ever runs),
		// and the loser gets a diagnostic naming the package that already
		// holds it.
		if let PackageKind::Library { name } = kind {
			match self.package_by_name.get(&name) {
				Some(&existing_id) => {
					let name_str = self.interner.resolve(name).unwrap();
					let existing_entry_path =
						&self.packages[existing_id.as_usize()].entry_path;
					package_graph.linker_diagnostics.push(
						report_duplicate_package_name(
							name_str,
							package_graph.entry_path.as_str(),
							existing_entry_path.as_str(),
						),
					);
				}
				None => {
					self.package_by_name.insert(name, package_id);
				}
			}
		}

		self.packages.push(package_graph);
		Ok(package_id)
	}

	pub fn build(self, root_package: PackageId) -> CompilationUnit {
		CompilationUnit {
			files: self.files,
			packages: self.packages,
			package_by_name: self.package_by_name,
			root_package,
			id_generator: self.id_generator,
			interner: self.interner,
		}
	}
}

impl PackageGraph {
	pub fn module_symbol_path(&self, module_id: ModuleId) -> Box<[SymbolU32]> {
		let mut path = Vec::new();
		let mut current = Some(module_id);

		while let Some(id) = current {
			let module = &self.modules[id.as_u32() as usize];
			if let Some(name) = module.name {
				path.push(name);
			}
			current = module.parent;
		}

		path.reverse();
		path.into_boxed_slice()
	}
}

/// Converts a `module foo;` resolution failure into a diagnostic attached to
/// that declaration's span, rather than to the (possibly nonexistent) file
/// it failed to resolve to.
fn report_module_not_found(
	file_id: FileId,
	span: ast::TextSpan,
	path: &str,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ModuleFileNotFound.code())
		.with_message(format!("module file not found: `{path}`"))
		.with_label(
			Label::primary(file_id, span)
				.with_message(format!("no such file: `{path}`")),
		)
}

fn report_ambiguous_module(
	file_id: FileId,
	span: ast::TextSpan,
	file: &str,
	directory_file: &str,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousModuleFile.code())
		.with_message("ambiguous module")
		.with_label(Label::primary(file_id, span).with_message(format!(
			"both `{file}` and `{directory_file}` exist"
		)))
}

/// No label: `serde_json` doesn't track a byte position for individual
/// manifest fields, so there's no real span inside either `wx.json` to
/// underline. Both packages' entry files are named in the message text
/// instead — enough to go find and fix the conflicting manifest, just
/// without a code frame.
fn report_duplicate_package_name(
	name: &str,
	this_entry_path: &str,
	first_entry_path: &str,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::DuplicatePackageName.code())
		.with_message(format!(
			"duplicate package name `{name}`: claimed by both the package \
			 rooted at `{first_entry_path}` and the one at `{this_entry_path}`"
		))
}

struct Loader<'ctx, 'src, S: FileSource> {
	package_id: PackageId,
	file_source: &'src S,
	modules: Vec<SourceModule>,
	diagnostics: Vec<Diagnostic<FileId>>,
	path_to_module: HashMap<AbsolutePath, ModuleId>,
	ctx: &'ctx mut CompilationUnitBuilder,
}

impl<'ctx, 'src, Source: FileSource> Loader<'ctx, 'src, Source> {
	#[inline]
	fn new(
		ctx: &'ctx mut CompilationUnitBuilder,
		package_id: PackageId,
		file_source: &'src Source,
	) -> Self {
		Self {
			package_id,
			ctx,
			file_source,
			diagnostics: Vec::new(),
			modules: Vec::new(),
			path_to_module: HashMap::new(),
		}
	}

	/// Loads a single module and, recursively, every child it can resolve.
	/// Fails only when *this* file itself can't be read — a missing or
	/// ambiguous child `module foo;` is instead recorded as a diagnostic on
	/// the declaration (see below) and simply omitted from `children`, so
	/// one broken submodule doesn't take down its siblings or its parent.
	fn load_module(
		&mut self,
		file_path: AbsolutePath,
		name: Option<SymbolU32>,
		parent: Option<ModuleId>,
	) -> Result<ModuleId, ()> {
		if let Some(&module_id) = self.path_to_module.get(&file_path) {
			return Ok(module_id);
		}

		let source = self.file_source.read_to_string(&file_path)?;
		let file_id = self
			.ctx
			.files
			.add(
				file_path.as_str().to_string(),
				source,
				self.file_source.origin(),
			)
			.expect(
				"file count should never realistically approach FileId's limit",
			);
		let ast = ast::Parser::parse(
			file_id,
			&self.ctx.files,
			&mut self.ctx.interner,
			&mut self.ctx.id_generator,
		);
		let child_decls: Box<[ast::Spanned<SymbolU32>]> = ast
			.items
			.iter()
			.filter_map(|item| match &item.inner.inner {
				ast::Item::ModuleDeclaration { name, .. } => Some(*name),
				_ => None,
			})
			.collect();

		let module_id = ModuleId(u32::try_from(self.modules.len()).expect(
			"module count should never realistically approach u32::MAX",
		));
		self.path_to_module.insert(file_path.clone(), module_id);
		self.modules.push(SourceModule {
			package_id: self.package_id,
			id: module_id,
			parent,
			children: Vec::new(),
			name,
			file_id,
			file_path,
			ast,
		});

		let mut children = Vec::with_capacity(child_decls.len());
		for child_name in child_decls {
			let Some(child_path) =
				self.resolve_child_module_path(module_id, child_name, file_id)
			else {
				continue; // already diagnosed as ambiguous
			};
			match self.load_module(
				child_path.clone(),
				Some(child_name.inner),
				Some(module_id),
			) {
				Ok(child_id) => children.push(child_id),
				Err(()) => self.diagnostics.push(report_module_not_found(
					file_id,
					child_name.span,
					child_path.as_str(),
				)),
			}
		}
		self.modules[module_id.0 as usize].children = children;

		Ok(module_id)
	}

	/// Resolves `module <child_module_name>;` declared at `child_span` in
	/// `parent_module_id`'s file to a candidate file path. Doesn't check the
	/// path actually exists (that's `load_module`'s job) except to detect
	/// the ambiguous case, which it diagnoses directly since — unlike a
	/// simple not-found — there's no single "the file" to report from
	/// `load_module`.
	fn resolve_child_module_path(
		&mut self,
		parent_module_id: ModuleId,
		child_module_name: ast::Spanned<SymbolU32>,
		parent_file_id: FileId,
	) -> Option<AbsolutePath> {
		let module_name = self
			.ctx
			.interner
			.resolve(child_module_name.inner)
			.expect("module symbol should resolve while loading package");
		let parent_dir =
			self.modules[parent_module_id.0 as usize].file_path.parent();
		let sibling_file =
			parent_dir.join(&RelativePath::new(format!("{module_name}.wx")));
		let directory_file = parent_dir
			.join(&RelativePath::new(format!("{module_name}/mod.wx")));

		if self.file_source.exists(&sibling_file)
			&& self.file_source.exists(&directory_file)
		{
			self.diagnostics.push(report_ambiguous_module(
				parent_file_id,
				child_module_name.span,
				sibling_file.as_str(),
				directory_file.as_str(),
			));
			return None;
		}

		if self.file_source.exists(&sibling_file) {
			return Some(sibling_file);
		}

		Some(directory_file)
	}
}
