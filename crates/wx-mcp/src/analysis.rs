//! One checked package, loaded from disk for one tool call, and the index of
//! its items by path.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::files::Files as _;
use wx_compiler::diagnostics::SourceSpan;
use wx_compiler::symbols::{Keyword, StringInterner};
use wx_compiler::tir::{
	self, DeclKind, Definition, DefinitionFormatter, ItemLoc, MemberKind,
	MemberOwner, Semantics, Visibility,
};
use wx_compiler::vfs::{self, FileId, FileOrigin, PackageId};

/// A package checked from what is on disk now, with everything the tools
/// read from it.
pub(crate) struct Analysis {
	/// The directory holding the package's `wx.json`.
	pub(crate) root: PathBuf,
	pub(crate) strings: StringInterner,
	pub(crate) compilation: vfs::CompilationUnit,
	pub(crate) sema: Semantics,
	pub(crate) items: ItemIndex,
}

impl Analysis {
	/// Loads and checks the package governing `path`, a file in it or its
	/// directory: the nearest ancestor holding a `wx.json`.
	pub(crate) fn load(path: &Path) -> Result<Self, String> {
		let path = std::fs::canonicalize(path).map_err(|error| {
			format!("cannot read `{}`: {error}", path.display())
		})?;
		let root = path
			.ancestors()
			.find(|dir| dir.join("wx.json").is_file())
			.ok_or_else(|| {
				format!(
					"`{}` is not inside a wx package (no `wx.json` above it)",
					path.display()
				)
			})?
			.to_path_buf();
		let root_text = root.to_str().ok_or("the package path is not UTF-8")?;
		let mut strings = Keyword::create_interner();
		let compilation = vfs::open_manifest(
			vfs::AbsolutePath::new(root_text),
			&vfs::NativeFileSource,
			&mut strings,
		)
		.map_err(|()| {
			format!(
				"cannot load the package at `{root_text}`: its `wx.json` or its entry file is unreadable"
			)
		})?;
		let sema = tir::check(&compilation, &mut strings);
		let items = ItemIndex::build(&sema, &strings);
		Ok(Self {
			root,
			strings,
			compilation,
			sema,
			items,
		})
	}

	/// What the root package's lints report, at the levels its `wx.json`
	/// sets, or why they cannot run: its `lint` section is invalid.
	pub(crate) fn lints(&self) -> Result<Vec<Diagnostic<FileId>>, String> {
		let manifest = std::fs::read_to_string(self.root.join("wx.json"))
			.map_err(|error| format!("cannot read `wx.json`: {error}"))?;
		let config =
			wx_lint::LintConfig::from_manifest(&manifest).map_err(|error| {
				format!("invalid `lint` section in `wx.json`: {error}")
			})?;
		Ok(wx_lint::lint(
			&self.compilation,
			&self.sema,
			&self.strings,
			self.compilation.root_package,
			config,
		))
	}

	/// `item`'s signature as `wx` source.
	pub(crate) fn signature(&self, item: ItemLoc) -> String {
		self.sema
			.definition_formatter(&self.strings)
			.signature(Definition::Item(item))
			.unwrap_or_else(|| "?".to_owned())
	}

	/// One indexed item as the listing tools show it:
	/// `path — signature  [location]`, tagged when it is internal.
	pub(crate) fn item_line(&self, entry: &IndexedItem) -> String {
		let internal = if entry.public { "" } else { " (internal)" };
		format!(
			"{}{internal} — {}  [{}]",
			entry.path,
			self.signature(entry.item),
			self.item_location(entry.item)
		)
	}

	/// Where `span` starts, as `file:line:column`.
	pub(crate) fn location(&self, span: SourceSpan) -> String {
		self.position(span.file_id, usize::from(span.span.start))
	}

	/// Where byte `offset` of `file_id` is, as `file:line:column`.
	pub(crate) fn position(&self, file_id: FileId, offset: usize) -> String {
		let (line, column) = self.line_column_at(file_id, offset);
		format!("{}:{line}:{column}", self.file_name(file_id))
	}

	/// How `file` is shown: a file on disk by its path from the root
	/// package's directory (`shapes.wx`, `../math/sin.wx`), a core file as
	/// its `wx://core` URI.
	pub(crate) fn file_name(&self, file_id: FileId) -> String {
		let Ok(file) = self.compilation.files.get(file_id) else {
			return "<unknown file>".to_owned();
		};
		if file.origin == FileOrigin::Virtual {
			return format!("wx://core{}", file.name);
		}
		relative_to(Path::new(&file.name), &self.root)
	}

	/// The line and column `span` starts at, both counting from 1.
	pub(crate) fn line_column(&self, span: SourceSpan) -> (usize, usize) {
		self.line_column_at(span.file_id, usize::from(span.span.start))
	}

	fn line_column_at(&self, file_id: FileId, offset: usize) -> (usize, usize) {
		self.compilation
			.files
			.location(file_id, offset)
			.map_or((0, 0), |location| {
				(location.line_number, location.column_number)
			})
	}

	/// Where the name of `item` is written.
	pub(crate) fn item_location(&self, item: ItemLoc) -> String {
		self.sema
			.definition_span(Definition::Item(item))
			.map_or_else(
				|| "<generated>".to_owned(),
				|span| self.location(span),
			)
	}

	/// The row `definition` names, whichever way it names it: as an item,
	/// or as a trait's or an impl's member reached through a type. `None`
	/// for what is not a row (a local, a parameter, a field, a label).
	pub(crate) fn row(&self, definition: Definition) -> Option<ItemLoc> {
		let decls = &self.sema.decls;
		Some(match definition {
			Definition::Item(item) => item,
			Definition::Member(
				MemberKind::Function(index) | MemberKind::Method(index),
			) => decls.functions[usize::from(index)].loc,
			Definition::Member(MemberKind::Constant(index)) => {
				decls.constants[usize::from(index)].loc
			}
			Definition::Member(MemberKind::AssociatedType(index)) => {
				decls.assoc_types[usize::from(index)].loc
			}
			_ => return None,
		})
	}

	/// The doc comment written above `item`.
	pub(crate) fn documentation(&self, item: ItemLoc) -> Option<String> {
		let span = self.sema.definition_span(Definition::Item(item))?;
		let file = self.compilation.files.get(span.file_id).ok()?;
		self.compilation
			.comments(span.file_id)
			.documentation(&file.source, span.span.start)
	}

	/// The file of the package's modules at `path`.
	pub(crate) fn file(&self, path: &Path) -> Result<FileId, String> {
		let path = std::fs::canonicalize(path).map_err(|error| {
			format!("cannot read `{}`: {error}", path.display())
		})?;
		self.compilation
			.packages
			.iter()
			.flat_map(|package| &package.modules)
			.find(|module| Path::new(module.file_path.as_str()) == path)
			.map(|module| module.file_id)
			.ok_or_else(|| {
				format!(
					"`{}` is not a module of the package at `{}`",
					path.display(),
					self.root.display()
				)
			})
	}

	/// The package `name` names from the root: `core`, a dependency's key,
	/// or, for `None`, the root package itself.
	pub(crate) fn package(
		&self,
		name: Option<&str>,
	) -> Result<PackageId, String> {
		let Some(name) = name else {
			return Ok(self.compilation.root_package);
		};
		if name == "core" {
			return Ok(self.compilation.core_package);
		}
		let root = &self.compilation.packages
			[self.compilation.root_package.as_usize()];
		let key = self.strings.get(name);
		key.and_then(|key| root.dependencies.get(&key).copied())
			.ok_or_else(|| {
				format!("the root package has no dependency `{name}`")
			})
	}
}

/// Every named item of the compilation, by its path as written from the
/// root package, sorted by path. Two items can share a path: a type's
/// members from different trait impls, or a root item named as core's.
pub(crate) struct ItemIndex {
	entries: Vec<IndexedItem>,
	/// Each indexed item's position in `entries`.
	positions: HashMap<ItemLoc, usize>,
}

pub(crate) struct IndexedItem {
	pub(crate) path: String,
	pub(crate) item: ItemLoc,
	pub(crate) package: PackageId,
	/// Whether every step on its path is public, so that a package other
	/// than its own can name it.
	pub(crate) public: bool,
	/// The step before the item on its path: its namespace's declaration,
	/// its trait, or its impl's target. `None` at a package root.
	pub(crate) parent: Option<ItemLoc>,
}

impl ItemIndex {
	/// Indexes every named item under each path the root has to its
	/// package: a dependency's items once per instance of it. An item of a
	/// package the root reaches through no instance has no path, and is left
	/// out.
	fn build(sema: &Semantics, strings: &StringInterner) -> Self {
		let formatter = sema.definition_formatter(strings);
		let mut package_paths = PackagePaths::new(sema, &formatter);
		let mut by_package: HashMap<PackageId, Vec<PackagePath>> =
			HashMap::new();
		let mut entries = Vec::new();
		for item in sema.decls.namespaces.keys() {
			if !is_named_item(sema, item) {
				continue;
			}
			let Some(path) = sema.item_path(item) else {
				continue;
			};
			let prefixes = by_package
				.entry(path.package)
				.or_insert_with(|| package_paths.all(path.package));
			let written = formatter.path(&path);
			let public = path.steps.iter().all(|&step| is_public(sema, step));
			let parent = path.steps.iter().rev().nth(1).copied();
			for prefix in prefixes.iter() {
				entries.push(IndexedItem {
					path: prefix.join(&written),
					item,
					package: path.package,
					public: prefix.public && public,
					parent,
				});
			}
		}
		entries.sort_by(|a, b| a.path.cmp(&b.path));
		let mut positions = HashMap::new();
		for (position, entry) in entries.iter().enumerate() {
			positions.entry(entry.item).or_insert(position);
		}
		Self { entries, positions }
	}

	pub(crate) fn iter(&self) -> impl Iterator<Item = &IndexedItem> {
		self.entries.iter()
	}

	/// The items the root package can name: its own, and other packages'
	/// public ones.
	pub(crate) fn nameable(
		&self,
		root: PackageId,
	) -> impl Iterator<Item = &IndexedItem> {
		(self.entries.iter())
			.filter(move |entry| entry.package == root || entry.public)
	}

	/// The items whose path is exactly `path`.
	pub(crate) fn named(&self, path: &str) -> &[IndexedItem] {
		let start = self
			.entries
			.partition_point(|entry| entry.path.as_str() < path);
		let end = self
			.entries
			.partition_point(|entry| entry.path.as_str() <= path);
		&self.entries[start..end]
	}

	/// The path of `item`, if it is indexed: the first of its paths, when
	/// its package is instantiated more than once.
	pub(crate) fn path_of(&self, item: ItemLoc) -> Option<&str> {
		let position = *self.positions.get(&item)?;
		Some(self.entries[position].path.as_str())
	}

	/// The items one step below `parent` on their paths, each once, by
	/// the path [`Self::path_of`] gives it.
	pub(crate) fn children(
		&self,
		parent: ItemLoc,
	) -> impl Iterator<Item = &IndexedItem> {
		(self.entries.iter().enumerate())
			.filter(move |&(position, entry)| {
				entry.parent == Some(parent)
					&& self.positions.get(&entry.item) == Some(&position)
			})
			.map(|(_, entry)| entry)
	}
}

/// Whether `item` is a declaration someone wrote and can name: not a
/// generated row (an impl's generated associated type, whose name is
/// empty), nor a package's own entry or a package instance, which name
/// packages rather than items.
fn is_named_item(sema: &Semantics, item: ItemLoc) -> bool {
	if matches!(
		sema.declaration_kind(item),
		DeclKind::Package(_) | DeclKind::PackageInstance(_)
	) {
		return false;
	}
	sema.definition_span(Definition::Item(item))
		.is_some_and(|span| span.span.start != span.span.end)
}

/// Whether the declaration `item` is public where it is declared. A member
/// of a trait or of a trait impl is as visible as its trait and its type,
/// and a variant as its enum: the steps before it on a path decide.
fn is_public(sema: &Semantics, item: ItemLoc) -> bool {
	if let DeclKind::EnumVariant(_) = sema.declaration_kind(item) {
		return true;
	}
	match sema.member_owner(item) {
		MemberOwner::Trait(_) | MemberOwner::TraitImpl(_) => true,
		MemberOwner::Free | MemberOwner::InherentImpl(_) => {
			sema.decls.item(item).visibility == Visibility::Public
		}
	}
}

/// A path from the root package to a package, as the root writes it:
/// empty for the root and for core, whose items the prelude names, and
/// otherwise the path to a package instance of it.
#[derive(Clone)]
struct PackagePath {
	text: String,
	/// Whether the root can follow it: each step outside the root package
	/// is public.
	public: bool,
}

impl PackagePath {
	fn join(&self, rest: &str) -> String {
		if self.text.is_empty() {
			rest.to_owned()
		} else {
			format!("{}::{rest}", self.text)
		}
	}
}

/// The paths from the root to each package, through its instances.
/// Instances are not yet told apart, so an instance written in another
/// package continues the shortest path to that package only.
///
/// Temporary, until package instantiation is implemented: an item belongs
/// to its package, not to an instance, so its `ItemPath` cannot say which
/// instance reaches it and this rebuilds the routes from the root. Once an
/// item's identity carries its instance, its path should, and this goes.
struct PackagePaths<'a> {
	sema: &'a Semantics,
	formatter: &'a DefinitionFormatter<'a>,
	/// The shortest path to each package asked for; `None` while it is
	/// being found, so that a cycle of instances reaches nothing.
	shortest: HashMap<PackageId, Option<PackagePath>>,
}

impl<'a> PackagePaths<'a> {
	fn new(
		sema: &'a Semantics,
		formatter: &'a DefinitionFormatter<'a>,
	) -> Self {
		Self {
			sema,
			formatter,
			shortest: HashMap::new(),
		}
	}

	/// Every path to `package`: one through each instance of it that a path
	/// reaches.
	fn all(&mut self, package: PackageId) -> Vec<PackagePath> {
		let decls = &self.sema.decls;
		if package == decls.root_package
			|| package == decls.namespaces.core_package()
		{
			return vec![PackagePath {
				text: String::new(),
				public: true,
			}];
		}
		let mut paths = Vec::new();
		for instance in decls.namespaces.instances_of(package) {
			let Some(path) = self.sema.item_path(instance) else {
				continue;
			};
			let Some(base) = self.shortest(path.package) else {
				continue;
			};
			let public = path.package == decls.root_package
				|| path.steps.iter().all(|&step| is_public(self.sema, step));
			paths.push(PackagePath {
				text: base.join(&self.formatter.path(&path)),
				public: base.public && public,
			});
		}
		paths
	}

	/// The shortest path to `package` the root can follow, else the
	/// shortest of all.
	fn shortest(&mut self, package: PackageId) -> Option<PackagePath> {
		if let Some(known) = self.shortest.get(&package) {
			return known.clone();
		}
		self.shortest.insert(package, None);
		let shortest = (self.all(package).into_iter())
			.min_by_key(|path| (!path.public, path.text.len()));
		self.shortest.insert(package, shortest.clone());
		shortest
	}
}

/// `path` as written from `dir`: down from it, or up out of it first
/// (`../math/sin.wx`). A path sharing nothing with `dir` but the file
/// system's root stays absolute.
fn relative_to(path: &Path, dir: &Path) -> String {
	let common = (path.components().zip(dir.components()))
		.take_while(|(a, b)| a == b)
		.count();
	if common <= 1 {
		return path.display().to_string();
	}
	let mut relative = PathBuf::new();
	for _ in common..dir.components().count() {
		relative.push("..");
	}
	relative.extend(path.components().skip(common));
	relative.display().to_string()
}

#[cfg(test)]
pub(crate) mod tests {
	use std::path::{Path, PathBuf};
	use std::sync::atomic::{AtomicUsize, Ordering};

	use super::*;

	/// A tool's options from `arguments`, as the client sends them, so a
	/// test gets the defaults the client would.
	pub(crate) fn options<T: serde::de::DeserializeOwned>(
		arguments: serde_json::Value,
	) -> T {
		serde_json::from_value(arguments).expect("valid tool arguments")
	}

	/// A package written to a fresh directory, removed when dropped.
	pub(crate) struct Fixture {
		pub(crate) dir: PathBuf,
	}

	impl Fixture {
		/// Writes `files`, by path relative to the fixture's directory, and a
		/// `wx.json` naming `main.wx` its entry unless `files` has its own.
		pub(crate) fn new(files: &[(&str, &str)]) -> Self {
			static NEXT: AtomicUsize = AtomicUsize::new(0);
			let dir = std::env::temp_dir().join(format!(
				"wx-mcp-test-{}-{}",
				std::process::id(),
				NEXT.fetch_add(1, Ordering::Relaxed)
			));
			std::fs::create_dir_all(&dir).unwrap();
			if !files.iter().any(|&(path, _)| path.ends_with("wx.json")) {
				std::fs::write(
					dir.join("wx.json"),
					r#"{ "entry": "main.wx" }"#,
				)
				.unwrap();
			}
			for (path, source) in files {
				let path = dir.join(path);
				std::fs::create_dir_all(path.parent().unwrap()).unwrap();
				std::fs::write(path, source).unwrap();
			}
			Self { dir }
		}

		pub(crate) fn path(&self, relative: &str) -> PathBuf {
			self.dir.join(relative)
		}

		pub(crate) fn analysis(&self) -> Analysis {
			Analysis::load(&self.dir).expect("the fixture loads")
		}

		/// The analysis of the package in the directory `relative`.
		pub(crate) fn analysis_of(&self, relative: &str) -> Analysis {
			Analysis::load(&self.dir.join(relative)).expect("the package loads")
		}
	}

	impl Drop for Fixture {
		fn drop(&mut self) {
			let _ = std::fs::remove_dir_all(&self.dir);
		}
	}

	#[test]
	fn a_file_finds_the_package_above_it() {
		let fixture = Fixture::new(&[
			("main.wx", "mod shapes;\nfunc main() {}\n"),
			("shapes.wx", "pub struct Point(x: i32);\n"),
		]);
		let analysis = Analysis::load(&fixture.path("shapes.wx")).unwrap();
		assert_eq!(analysis.root, std::fs::canonicalize(&fixture.dir).unwrap());
		let [point] = analysis.items.named("shapes::Point") else {
			panic!("expected one `shapes::Point`");
		};
		assert_eq!(analysis.item_location(point.item), "shapes.wx:1:12");
	}

	#[test]
	fn a_path_outside_any_package_is_an_error() {
		let error = Analysis::load(Path::new("/")).err().unwrap();
		assert!(error.contains("not inside a wx package"), "{error}");
	}

	/// The manifest of a package depending on `../lib` as `geometry`.
	const APP: &str = r#"{ "entry": "main.wx", "dependencies": { "geometry": { "type": "local", "path": "../lib" } } }"#;
	const LIB: &[(&str, &str)] = &[
		("lib/wx.json", r#"{ "entry": "lib.wx" }"#),
		(
			"lib/lib.wx",
			"pub func area(side: i32) -> i32 { side * side }\n",
		),
	];

	fn paths_of(analysis: &Analysis, name: &str) -> Vec<String> {
		(analysis.items.iter())
			.filter(|entry| entry.path.rsplit("::").next() == Some(name))
			.map(|entry| entry.path.clone())
			.collect()
	}

	#[test]
	fn a_dependency_is_named_by_the_whole_path_to_its_instance() {
		let mut files = vec![
			("app/wx.json", APP),
			(
				"app/main.wx",
				"mod shapes {\n    pub package \"geometry\" as geo;\n}\nfunc main() {}\n",
			),
		];
		files.extend_from_slice(LIB);
		let fixture = Fixture::new(&files);
		let analysis = fixture.analysis_of("app");
		assert_eq!(paths_of(&analysis, "area"), ["shapes::geo::area"]);
		let [area] = analysis.items.named("shapes::geo::area") else {
			panic!("expected one `shapes::geo::area`");
		};
		assert_eq!(analysis.item_location(area.item), "../lib/lib.wx:1:10");
	}

	/// Instances are not told apart yet: each names the same items.
	#[test]
	fn a_dependency_instantiated_twice_is_named_through_each_instance() {
		let mut files = vec![
			("app/wx.json", APP),
			(
				"app/main.wx",
				"package \"geometry\" as a;\npackage \"geometry\" as b;\nfunc main() {}\n",
			),
		];
		files.extend_from_slice(LIB);
		let fixture = Fixture::new(&files);
		let analysis = fixture.analysis_of("app");
		assert_eq!(paths_of(&analysis, "area"), ["a::area", "b::area"]);
		let [a] = analysis.items.named("a::area") else {
			panic!("expected one `a::area`");
		};
		assert_eq!(analysis.items.path_of(a.item), Some("a::area"));
	}

	/// A package reached through another one's instance continues its
	/// path, and is nameable only when that instance is public.
	#[test]
	fn a_dependencys_dependency_continues_the_path_to_it() {
		let fixture = |instance: &'static str| {
			let mut files = vec![
				(
					"app/wx.json",
					r#"{ "entry": "main.wx", "dependencies": { "mid": { "type": "local", "path": "../mid" } } }"#,
				),
				("app/main.wx", "package \"mid\" as mid;\nfunc main() {}\n"),
				(
					"mid/wx.json",
					r#"{ "entry": "main.wx", "dependencies": { "geometry": { "type": "local", "path": "../lib" } } }"#,
				),
				("mid/main.wx", instance),
			];
			files.extend_from_slice(LIB);
			Fixture::new(&files)
		};
		let public = fixture("pub package \"geometry\" as geo;\n");
		let analysis = public.analysis_of("app");
		let [area] = analysis.items.named("mid::geo::area") else {
			panic!("expected one `mid::geo::area`");
		};
		assert!(area.public);
		let private = fixture("package \"geometry\" as geo;\n");
		let analysis = private.analysis_of("app");
		let [area] = analysis.items.named("mid::geo::area") else {
			panic!("expected one `mid::geo::area`");
		};
		assert!(!area.public);
	}

	#[test]
	fn a_path_is_written_from_the_root_directory() {
		assert_eq!(
			relative_to(Path::new("/w/app/src/a.wx"), Path::new("/w/app")),
			"src/a.wx"
		);
		assert_eq!(
			relative_to(Path::new("/w/lib/b.wx"), Path::new("/w/app")),
			"../lib/b.wx"
		);
		assert_eq!(
			relative_to(Path::new("/other/c.wx"), Path::new("/w/app")),
			"/other/c.wx"
		);
	}

	#[test]
	fn core_items_are_named_without_a_prefix() {
		let fixture = Fixture::new(&[("main.wx", "func main() {}\n")]);
		let analysis = fixture.analysis();
		let [memory] = analysis.items.named("Memory") else {
			panic!("expected core's `Memory`");
		};
		assert_eq!(memory.package, analysis.compilation.core_package);
		assert!(
			analysis
				.item_location(memory.item)
				.starts_with("wx://core/")
		);
	}
}
