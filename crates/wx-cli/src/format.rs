use wx_compiler::ast;
use wx_compiler::vfs::{
	AbsolutePath, CompilationUnitBuilder, FileSource, Files, PackageManifest,
	RelativePath, SourceModule,
};
use wx_fmt::RendererConfig;

/// Everything a `wx format` invocation needs for one project: the parsed
/// modules to actually rewrite, the shared `Files`/interner they were
/// parsed with, and the project's own resolved format config — read once,
/// here, so nothing downstream re-resolves or re-reads it per file.
pub struct FormatSelection {
	pub files: Files,
	pub interner: ast::StringInterner,
	pub modules: Vec<SourceModule>,
	pub config: RendererConfig,
}

/// Loads the project rooted at `dir` and selects the modules to format.
///
/// `dir` must have a readable `wx.json` with a valid `entry` — `wx format`
/// has no anonymous, manifest-less mode; every file it touches belongs to
/// a project. This also means the config is unambiguous: there is exactly
/// one manifest to read, so there's nothing to fall back through.
///
/// `files`, if given, names an explicit list of paths relative to `dir` —
/// format exactly those files, with no module-tree walk. Each is loaded
/// independently via its own `load_binary` call; if it declares `mod`s
/// of its own, those get parsed too (parsing has to follow them to parse
/// the file at all) but are not selected — only the named file is, same
/// as a single shallow file always worked. With no `files`, every module
/// reachable from the manifest's `entry` is selected instead.
pub fn expand_project(
	dir: &AbsolutePath,
	files: Option<&[String]>,
	source: &impl FileSource,
) -> Result<FormatSelection, ()> {
	let manifest_path = dir.join(&RelativePath::new("wx.json"));
	let manifest_source = source.read_to_string(&manifest_path)?;
	let manifest = PackageManifest::parse(&manifest_source).map_err(|_| ())?;
	let config = RendererConfig::from_manifest(manifest.format);

	let mut builder = CompilationUnitBuilder::new();
	let modules = match files {
		None => {
			let entry = dir.join(&manifest.entry);
			let package_id = builder.load_binary(entry, source)?;
			// `load_binary` never resolves dependencies, so exactly one
			// package exists here — the one just loaded.
			builder.packages.remove(package_id.as_usize()).modules
		}
		Some(paths) => {
			let mut modules = Vec::with_capacity(paths.len());
			for path in paths {
				let file_path = dir.join(&RelativePath::new(path.clone()));
				let package_id = builder.load_binary(file_path, source)?;
				let mut graph = builder.packages.remove(package_id.as_usize());
				modules.push(graph.modules.swap_remove(graph.root.as_usize()));
			}
			modules
		}
	};

	Ok(FormatSelection {
		files: builder.files,
		interner: builder.interner,
		modules,
		config,
	})
}
