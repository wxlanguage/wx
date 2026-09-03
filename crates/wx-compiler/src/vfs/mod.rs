use std::collections::HashMap;
use std::fs;
use std::path::Path;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files;
use string_interner::symbol::SymbolU32;

use crate::ast;
use crate::diagnostics::DiagnosticCode;

mod manifest;
pub use manifest::{
	DependencySource, FormatManifest, PackageManifest, PackageManifestKind,
	PackageName,
};

mod resolve;
pub use resolve::{open_manifest, package_kind};

mod path;
pub use path::{AbsolutePath, RelativePath};

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

impl FileId {
	/// File ids are dense within a compilation, so anything keyed by file can
	/// be a `Vec` rather than a map.
	pub fn as_usize(self) -> usize {
		self.0 as usize
	}
}

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

	pub fn len(&self) -> usize {
		self.files.len()
	}

	pub fn is_empty(&self) -> bool {
		self.files.is_empty()
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

/// Where a non-root module was declared: the parent that named it, and that
/// declaration's own name/span/visibility. `parent` and `name` always exist
/// or don't exist together — bundled here, rather than as two independent
/// `Option`s on `SourceModule`, so that invariant is enforced by the type
/// itself instead of a comment.
#[derive(Clone)]
pub struct ModuleDeclaration {
	pub parent: ModuleId,
	pub name: ast::Spanned<SymbolU32>,
	/// Whether the declaration was `pub`. Independently optional — a
	/// declaration that exists but isn't `pub` is a normal, valid state.
	pub pub_span: Option<ast::TextSpan>,
}

pub struct SourceModule {
	pub package_id: PackageId,
	pub children: Vec<ModuleId>,
	/// `None` only for the package root, which has no declaring site.
	pub declaration: Option<ModuleDeclaration>,
	pub file_id: FileId,
	pub file_path: AbsolutePath,
	pub ast: ast::AST,
}

/// What a package *is*, as declared by its manifest — deliberately carries
/// no name. A package's name is a property of the edge that reached it (see
/// [`PackageGraph::dependencies`]), not of the package itself. The stdlib is
/// not a kind either: it's an ordinary `Library` that additionally happens
/// to be [`CompilationUnit::stdlib_package`].
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PackageKind {
	/// Produces a WASM module and cannot be imported.
	Binary,
	/// Importable, and subject to the library restrictions (no `export`,
	/// no `memory`, ...).
	Library,
}

pub struct PackageGraph {
	pub id: PackageId,
	pub root: ModuleId,
	pub kind: PackageKind,
	/// The other packages *this* package may refer to, keyed by the name it
	/// refers to them by — its own `dependencies` keys, plus the implicit
	/// `std`.
	///
	/// A name lives here, on the edge, rather than on the target: the same
	/// package can legitimately be `foo` here and `bar` in another package's
	/// map, and no package has a name of its own at all. Nothing outside
	/// this map can name a package, which is what keeps a transitive
	/// dependency invisible to anyone who didn't declare it.
	///
	/// Read these as an implicit `mod <key>;` at the top of the package's
	/// entry file — that's exactly the meaning TIR gives them, and why a
	/// local `mod foo;` colliding with a key here is an ordinary
	/// duplicate definition rather than an ambiguity to arbitrate.
	pub dependencies: HashMap<SymbolU32, PackageId>,
	/// Inverse of [`Self::dependencies`]. Well-defined only because
	/// [`CompilationUnitBuilder::add_dependency`] keeps the mapping
	/// injective: a package is declared under exactly one name here, which
	/// is what makes that name its canonical one — it has none of its own.
	pub dependency_names: HashMap<PackageId, SymbolU32>,
	pub entry_path: AbsolutePath,
	pub modules: Vec<SourceModule>,
	pub diagnostics: Vec<Diagnostic<FileId>>,
	pub path_to_module: HashMap<AbsolutePath, ModuleId>,
}

pub struct CompilationUnit {
	pub files: Files,
	pub packages: Vec<PackageGraph>,
	pub root_package: PackageId,
	/// The package providing the language's `#[tag = "..."]` items (the
	/// twelve operator traits `resolve_operator_traits` looks up). Always
	/// present — see [`CompilationUnitBuilder::build`] for why this is not an
	/// `Option`. Equal to `root_package` when the root package *is* the
	/// stdlib.
	pub stdlib_package: PackageId,
	pub id_generator: ast::DefIdGenerator,
	pub interner: ast::StringInterner,
}

impl CompilationUnit {
	pub fn collect_parser_diagnostics(&self) -> Vec<Diagnostic<FileId>> {
		self.packages
			.iter()
			.flat_map(|package| package.modules.iter())
			.flat_map(|module| module.ast.diagnostics.iter().cloned())
			.collect()
	}

	pub fn collect_linker_diagnostics(&self) -> Vec<Diagnostic<FileId>> {
		self.packages
			.iter()
			.flat_map(|package| package.diagnostics.iter().cloned())
			.collect()
	}

	pub fn collect_diagnostics(&self) -> Vec<Diagnostic<FileId>> {
		self.packages
			.iter()
			.flat_map(|package| {
				package.diagnostics.iter().chain(
					package
						.modules
						.iter()
						.flat_map(|module| module.ast.diagnostics.iter()),
				)
			})
			.cloned()
			.collect()
	}
}

pub struct CompilationUnitBuilder {
	pub files: Files,
	pub id_generator: ast::DefIdGenerator,
	pub interner: ast::StringInterner,
	pub packages: Vec<PackageGraph>,
	/// Set once the stdlib exists, and seeded into every package loaded
	/// afterwards as its implicit `std` dependency. `None` only while the
	/// stdlib itself is being loaded — which is exactly what keeps it from
	/// depending on itself, with no check needed.
	stdlib: Option<PackageId>,
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
/// `mod math;` declaration in `main.wx` resolves to.
pub const STDLIB_FILES: &[(&str, &str)] =
	include!(concat!(env!("OUT_DIR"), "/stdlib_files.rs"));

/// Serves the embedded stdlib to the loader, reading straight out of
/// [`STDLIB_FILES`].
///
/// The alternative — copying the table into a [`VirtualFileSource`]'s map —
/// builds an owned duplicate of sources already sitting in the binary, one
/// that exists only to be read once and dropped. Reading the table directly
/// keeps it the single place the stdlib's contents live.
///
/// Files are tagged [`FileOrigin::Virtual`]: the stdlib has no on-disk home,
/// and consumers key off `Local` to pick out the user's own files.
pub struct StdlibFileSource;

impl StdlibFileSource {
	/// The source of one embedded stdlib file, keyed as in [`STDLIB_FILES`] —
	/// `path` must already be `/`-prefixed (e.g.
	/// `AbsolutePath::new("/math/mod.wx")`), same as every other consumer of
	/// this convention; the caller (serving `wx://std/...` documents to the
	/// editor) is responsible for constructing one, same as any other
	/// frontend.
	///
	/// Public because go-to-definition needs to land inside the stdlib
	/// without it existing on disk, and because both trait methods below
	/// want the same lookup — `exists` in particular, which would otherwise
	/// have to allocate a whole `String` just to answer a yes/no.
	pub fn source(path: &AbsolutePath) -> Option<&'static str> {
		STDLIB_FILES
			.iter()
			.find(|(name, _)| *name == path.as_str())
			.map(|(_, source)| *source)
	}
}

impl FileSource for StdlibFileSource {
	fn read_to_string(&self, path: &AbsolutePath) -> Result<String, ()> {
		Self::source(path).map(String::from).ok_or(())
	}

	fn exists(&self, path: &AbsolutePath) -> bool {
		Self::source(path).is_some()
	}

	fn origin(&self) -> FileOrigin {
		FileOrigin::Virtual
	}
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
			stdlib: None,
		}
	}

	/// Loads the embedded stdlib and marks it as this compilation's, so
	/// every package loaded afterwards gets `std` seeded into its
	/// dependencies.
	///
	/// [`StdlibFileSource`] resolves reads against [`STDLIB_FILES`] on demand,
	/// so the stdlib is an ordinary multi-file package from here on: `mod
	/// foo;` in `main.wx` resolves against the embedded table exactly as it
	/// would against the filesystem for a user package. Adding a stdlib file
	/// needs no change here.
	///
	/// The entry point is embedded, so this can never actually hit the "entry
	/// point unreadable" case `load_package` guards against.
	pub fn load_stdlib(&mut self) -> PackageId {
		let id = self
			.load_package(
				PackageKind::Library,
				AbsolutePath::new("/main.wx"),
				&StdlibFileSource,
			)
			.expect("embedded stdlib source should always be readable");
		self.set_stdlib(id);
		id
	}

	/// Marks an already-loaded package as this compilation's stdlib — used
	/// by `open_manifest` when the root declares `"type": "std"` and so
	/// provides the tagged items itself, which can't go through
	/// [`Self::load_stdlib`] because its sources come from a manifest rather
	/// than from [`STDLIB_FILES`].
	///
	/// Must run before any package that should be able to name `std`: the
	/// seed in [`Self::load_package`] only applies to packages loaded after
	/// this point.
	pub fn set_stdlib(&mut self, package: PackageId) {
		self.stdlib = Some(package);
	}

	#[inline]
	pub fn load_binary(
		&mut self,
		entry_path: AbsolutePath,
		file_source: &impl FileSource,
	) -> Result<PackageId, ()> {
		self.load_package(PackageKind::Binary, entry_path, file_source)
	}

	/// Records that `owner` refers to `dependency` by `name`, diagnosing a
	/// collision itself rather than handing one back.
	///
	/// A `dependencies` entry is a *declaration*, not an alias — it's what
	/// introduces a package into the compilation, the way `mod foo;`
	/// introduces a module. So the mapping is kept one-to-one in both
	/// directions: declaring one package under two names is a duplicate
	/// declaration, and a second name is spelled with an alias instead.
	///
	/// An existing binding always wins, which is what makes the seeded `std`
	/// survive a manifest that tries to bind that name — the stdlib is
	/// unreplaceable with no reserved-key check anywhere.
	pub fn add_dependency(
		&mut self,
		owner: PackageId,
		name: SymbolU32,
		dependency: PackageId,
	) {
		let package = &mut self.packages[owner.as_usize()];
		if let Some(existing) =
			package.dependency_names.get(&dependency).copied()
		{
			let diagnostic = Diagnostic::error()
				.with_code(DiagnosticCode::PackageDeclaredTwice.code())
				.with_message(format!(
					"this package is already declared as `{}`, so it cannot \
			 also be declared as `{}`",
					self.interner.resolve(existing).unwrap(),
					self.interner.resolve(name).unwrap(),
				));
			package.diagnostics.push(diagnostic);
			return;
		}
		if package.dependencies.contains_key(&name) {
			let diagnostic = Diagnostic::error()
				.with_code(DiagnosticCode::DuplicatePackageName.code())
				.with_message(format!(
					"the name `{}` is already used by another package this one \
			 depends on",
					self.interner.resolve(name).unwrap()
				));
			package.diagnostics.push(diagnostic);
			return;
		}

		package.dependencies.insert(name, dependency);
		package.dependency_names.insert(dependency, name);
	}

	/// Loads a package starting from `entry_path`. Fails only if the entry
	/// point itself can't be read — there's no partial package to build
	/// without it. Everything past that point (missing/ambiguous `mod`
	/// declarations) is recorded as a diagnostic instead of aborting, so one
	/// broken submodule doesn't take down the whole package.
	pub fn load_package(
		&mut self,
		kind: PackageKind,
		entry_path: AbsolutePath,
		file_source: &impl FileSource,
	) -> Result<PackageId, ()> {
		let package_id = PackageId(self.packages.len() as u32);

		// Every package can reach the stdlib under the name `std` without
		// declaring it — seeded here rather than left to each caller so it
		// cannot be forgotten, and seeded *before* any manifest key is
		// inserted so that declaring `"std"` yourself collides with it
		// instead of replacing it. `self.stdlib` is still `None` while the
		// stdlib itself is being loaded, so it never depends on itself.
		//
		// Computed before the loader takes its `&mut self`.
		let (dependencies, dependency_names) = match self.stdlib {
			Some(stdlib) => {
				let std = self.interner.get_or_intern("std");
				(
					HashMap::from([(std, stdlib)]),
					HashMap::from([(stdlib, std)]),
				)
			}
			None => (HashMap::new(), HashMap::new()),
		};

		let mut loader = Loader::new(self, package_id, file_source);
		let root_owned_dir = entry_path.parent();
		let root =
			loader.load_module(entry_path.clone(), None, root_owned_dir)?;

		// Built into a local first: moving the loader's fields out here is
		// what ends its borrow of `self`, which the push then needs.
		let package_graph = PackageGraph {
			id: package_id,
			kind,
			dependencies,
			dependency_names,
			root,
			entry_path,
			modules: loader.modules,
			diagnostics: loader.diagnostics,
			path_to_module: loader.path_to_module,
		};

		self.packages.push(package_graph);
		Ok(package_id)
	}

	/// Panics if no stdlib was ever established. Every compilation has
	/// exactly one provider of the language's `#[tag = "..."]` items — the
	/// embedded stdlib, or the root package itself when it declares
	/// `"type": "std"` — so a `CompilationUnit` without one isn't a state
	/// worth representing. The stdlib is taken from the builder rather than
	/// passed in, so the value that gets recorded is necessarily the same
	/// one that was seeded into every package's dependencies; passing it
	/// separately would let the two disagree.
	pub fn build(self, root_package: PackageId) -> CompilationUnit {
		let stdlib_package = self.stdlib.expect(
			"a stdlib must be established (`load_stdlib` or `set_stdlib`) \
			 before building a compilation",
		);
		CompilationUnit {
			files: self.files,
			packages: self.packages,
			root_package,
			stdlib_package,
			id_generator: self.id_generator,
			interner: self.interner,
		}
	}
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
	/// ambiguous child `mod foo;` is instead recorded as a diagnostic on
	/// the declaration (see below) and simply omitted from `children`, so
	/// one broken submodule doesn't take down its siblings or its parent.
	fn load_module(
		&mut self,
		file_path: AbsolutePath,
		declaration: Option<ModuleDeclaration>,
		owned_dir: AbsolutePath,
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
		let child_decls: Box<
			[(ast::Spanned<SymbolU32>, Option<ast::TextSpan>)],
		> = ast.items
			.iter()
			.filter_map(|item| match &item.inner.inner {
				ast::Item::ModuleDeclaration { name, pub_span } => {
					Some((*name, *pub_span))
				}
				ast::Item::Module { items, .. } => {
					self.diagnose_nested_module_declarations(file_id, items);
					None
				}
				_ => None,
			})
			.collect();

		let module_id = ModuleId(self.modules.len() as u32);
		self.path_to_module.insert(file_path.clone(), module_id);
		self.modules.push(SourceModule {
			package_id: self.package_id,
			children: Vec::new(),
			declaration,
			file_id,
			file_path,
			ast,
		});

		let mut children = Vec::with_capacity(child_decls.len());
		for (child_name, child_pub_span) in child_decls {
			let Some(child_path) =
				self.resolve_child_module_path(&owned_dir, child_name, file_id)
			else {
				continue; // already diagnosed as ambiguous
			};
			// A module's own children always live under a directory named
			// after *that module*, not wherever its own file physically
			// sits — so `math.wx` and `math/mod.wx` grant `math` the exact
			// same `owned_dir` for its children (both `src/math/`), same as
			// Rust's `foo.rs`/`foo/mod.rs` being interchangeable.
			let child_name_str =
				self.ctx.interner.resolve(child_name.inner).expect(
					"module symbol should resolve while loading package",
				);
			let child_owned_dir =
				owned_dir.join(&RelativePath::new(child_name_str.to_string()));
			match self.load_module(
				child_path.clone(),
				Some(ModuleDeclaration {
					parent: module_id,
					name: child_name,
					pub_span: child_pub_span,
				}),
				child_owned_dir,
			) {
				Ok(child_id) => children.push(child_id),
				Err(()) => {
					let diagnostic = Diagnostic::error()
						.with_code(DiagnosticCode::ModuleFileNotFound.code())
						.with_message(format!(
							"module file not found: `{}`",
							child_path.as_str()
						))
						.with_label(
							Label::primary(file_id, child_name.span)
								.with_message(format!(
									"no such file: `{}`",
									child_path.as_str()
								)),
						);
					self.diagnostics.push(diagnostic);
				}
			}
		}
		self.modules[module_id.0 as usize].children = children;

		Ok(module_id)
	}

	/// `mod { }` is the only item kind that can hide a `mod foo;`
	/// file declaration inside it — not legal there, since where a
	/// declared file lives should be readable from that one line, not
	/// require walking up through however many inline wrappers enclose it
	/// (unlike Rust, which resolves it by accumulating a directory segment
	/// per inline level).
	fn diagnose_nested_module_declarations(
		&mut self,
		file_id: FileId,
		items: &[ast::Separated<ast::Spanned<ast::Item>>],
	) {
		for item in items {
			match &item.inner.inner {
				ast::Item::ModuleDeclaration { name, .. } => {
					let diagnostic = Diagnostic::error()
						.with_code(
							DiagnosticCode::NestedModuleDeclaration.code(),
						)
						.with_message(
							"a `mod foo;` file declaration cannot appear inside an \
			 inline `mod { }` block",
						)
						.with_label(
							Label::primary(file_id, name.span).with_message(
								"move this declaration to the file's top level",
							),
						);
					self.diagnostics.push(diagnostic);
				}
				ast::Item::Module { items, .. } => {
					self.diagnose_nested_module_declarations(file_id, items);
				}
				_ => {}
			}
		}
	}

	/// Resolves `mod <child_module_name>;`, declared inside the module
	/// that owns `owned_dir`, to a candidate file path. `owned_dir` is
	/// *that module's* directory — accumulated from its own name, not
	/// wherever its own file happens to physically sit — so this doesn't
	/// need to look anything up about the declaring module itself. Doesn't
	/// check the path actually exists (that's `load_module`'s job) except
	/// to detect the ambiguous case, which it diagnoses directly since —
	/// unlike a simple not-found — there's no single "the file" to report
	/// from `load_module`.
	fn resolve_child_module_path(
		&mut self,
		owned_dir: &AbsolutePath,
		child_module_name: ast::Spanned<SymbolU32>,
		parent_file_id: FileId,
	) -> Option<AbsolutePath> {
		let module_name = self
			.ctx
			.interner
			.resolve(child_module_name.inner)
			.expect("module symbol should resolve while loading package");
		let sibling_file =
			owned_dir.join(&RelativePath::new(format!("{module_name}.wx")));
		let directory_file =
			owned_dir.join(&RelativePath::new(format!("{module_name}/mod.wx")));

		if self.file_source.exists(&sibling_file)
			&& self.file_source.exists(&directory_file)
		{
			let diagnostic = Diagnostic::error()
				.with_code(DiagnosticCode::AmbiguousModuleFile.code())
				.with_message("ambiguous module")
				.with_label(
					Label::primary(parent_file_id, child_module_name.span)
						.with_message(format!(
							"both `{}` and `{}` exist",
							sibling_file.as_str(),
							directory_file.as_str()
						)),
				);
			self.diagnostics.push(diagnostic);
			return None;
		}

		if self.file_source.exists(&sibling_file) {
			return Some(sibling_file);
		}

		Some(directory_file)
	}
}
