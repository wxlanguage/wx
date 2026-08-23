use std::fmt;

/// Normalizes `\` to `/` (a real filesystem path read on Windows) so
/// lookups behave identically to a `/`-only virtual one — matches
/// `VirtualFileSource`'s plain string keys, which are always spelled
/// with `/`.
fn normalize_separators(path: String) -> String {
	if path.contains('\\') {
		path.replace('\\', "/")
	} else {
		path
	}
}

/// Concatenates `base` and `segment` with `/`, lexically collapsing
/// `..`/`.` segments along the way — unlike `std::path::Path::join`,
/// which leaves them un-collapsed (`Path::new("a").join("../b")` stays
/// `"a/../b"`). Collapsing matters here because `VirtualFileSource` has
/// no filesystem to resolve them for us, and leaving them un-collapsed
/// would otherwise leak into diagnostics and entry paths too.
fn join_segments(base: &str, segment: &str) -> String {
	let mut segments: Vec<&str> = Vec::new();
	let combined = format!("{base}/{segment}");
	for part in combined.split('/') {
		match part {
			"" | "." => {}
			".." => match segments.last() {
				Some(&top) if top != ".." => {
					segments.pop();
				}
				_ => segments.push(".."),
			},
			part => segments.push(part),
		}
	}
	segments.join("/")
}

/// A path fragment guaranteed, by construction, never to start with `/`
/// — used wherever "must be relative" is a real invariant, not just a
/// convention: a `wx.json` dependency's own declared `path` field (this
/// design's dependency-resolution rule requires exactly this: always
/// relative to the declaring manifest, never the process's cwd), and a
/// bare filename (`"main.wx"`, `"wx.json"`) being appended onto an
/// [`AbsolutePath`]. Deliberately has no `join`/`parent` of its own: every
/// real use here treats a relative path as something appended onto a
/// concrete, absolute location, never as a base in its own right — see
/// `AbsolutePath::join`.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct RelativePath(String);

impl RelativePath {
	/// Panics if `path` starts with `/`. The check is a single cheap
	/// `starts_with`, so this runs unconditionally rather than only in
	/// debug builds — every current call site passes a string literal or
	/// an interned identifier, so this is a programmer-error safety net,
	/// not something real input can trigger. `wx.json`-sourced paths go
	/// through [`RelativePath`]'s `Deserialize` impl instead, which
	/// rejects a leading `/` as a real, reportable error — user input
	/// deserves a message, not a panic.
	pub fn new(path: impl Into<String>) -> Self {
		let path = normalize_separators(path.into());
		assert!(
			!path.starts_with('/'),
			"RelativePath must not start with `/`: `{path}`"
		);
		RelativePath(path)
	}

	/// Skips the leading-`/` check `new` performs. Not `unsafe` in the
	/// memory-safety sense — nothing here can cause undefined behavior —
	/// but every other consumer of a `RelativePath` assumes the invariant
	/// holds, so getting it wrong produces confusing behavior far from
	/// wherever the mistake was made, mirroring `std`'s own `_unchecked`
	/// convention (`NonZeroU32::new_unchecked`,
	/// `str::from_utf8_unchecked`). Currently unused anywhere in this
	/// crate — kept for API completeness, not because a call site needs
	/// it yet.
	pub unsafe fn new_unchecked(path: String) -> Self {
		RelativePath(path)
	}

	pub fn as_str(&self) -> &str {
		&self.0
	}
}

impl fmt::Display for RelativePath {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str(&self.0)
	}
}

impl<'de> serde::Deserialize<'de> for RelativePath {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: serde::Deserializer<'de>,
	{
		let path = normalize_separators(String::deserialize(deserializer)?);
		if path.starts_with('/') {
			return Err(serde::de::Error::custom(format!(
				"path `{path}` must be relative (no leading `/`)"
			)));
		}
		Ok(RelativePath(path))
	}
}

/// An absolute, `/`-rooted path — the one location type this compiler
/// works with internally, whether that root is a real filesystem root
/// (`NativeFileSource`, e.g. from `wx-cli` joining a CLI argument against
/// `std::env::current_dir()`) or a synthetic one (`VirtualFileSource`
/// treats `/` as *its own* root purely by convention, stripping it back
/// off before consulting its in-memory map — see its own doc comment).
/// Every frontend is responsible for producing one of these before
/// calling into [`super::open_package`]/[`super::CompilationUnitBuilder`]
/// — nothing past that boundary ever has to wonder whether a path is
/// absolute or relative, because it always is.
///
/// Never `std::path::Path`, which bakes in real-OS semantics (drive
/// letters, backslash separators on Windows) that don't make sense for a
/// synthetic, `VirtualFileSource`-backed root with no OS concept at all.
/// `std::path::Path` stays confined to the one place it's actually
/// legitimate: inside `NativeFileSource`, at the exact point of a real
/// `std::fs` call.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct AbsolutePath(String);

impl AbsolutePath {
	/// Panics if `path` doesn't start with `/`. The check is a single
	/// cheap `starts_with`, so — like [`RelativePath::new`] — this runs
	/// unconditionally: an invariant this load-bearing (every other
	/// method on this type assumes it) is worth enforcing in every build,
	/// not just debug ones.
	pub fn new(path: impl Into<String>) -> Self {
		let path = normalize_separators(path.into());
		assert!(
			path.starts_with('/'),
			"AbsolutePath must start with `/`: `{path}`"
		);
		AbsolutePath(path)
	}

	/// Skips the leading-`/` check `new` performs — see
	/// [`RelativePath::new_unchecked`] for why this isn't `unsafe` in the
	/// memory-safety sense, just a sharp edge. Currently unused anywhere
	/// in this crate.
	pub unsafe fn new_unchecked(path: String) -> Self {
		AbsolutePath(path)
	}

	pub fn as_str(&self) -> &str {
		&self.0
	}

	/// This path with its last segment removed. Never shorter than `/`
	/// itself — an absolute path's root has no parent to walk above.
	pub fn parent(&self) -> AbsolutePath {
		match self.0[1..].rfind('/') {
			Some(i) => AbsolutePath(self.0[..=i].to_string()),
			None => AbsolutePath("/".to_string()),
		}
	}

	/// Appends `segment` — always relative by [`RelativePath`]'s own
	/// invariant, so this is the *only* join this codebase ever needs:
	/// joining two relative paths together wouldn't mean anything (relative
	/// to what?), and joining an absolute fragment onto another would mean
	/// "replace the whole path" (`std::path::Path::join`'s behavior for an
	/// absolute argument) — not something any caller here actually wants.
	/// Lexically collapses `..`/`.` the same way `join_segments` always
	/// has; see its own doc comment.
	pub fn join(&self, segment: &RelativePath) -> AbsolutePath {
		AbsolutePath(format!("/{}", join_segments(&self.0[1..], &segment.0)))
	}
}

impl fmt::Display for AbsolutePath {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str(&self.0)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn absolute_new_normalizes_backslashes() {
		assert_eq!(AbsolutePath::new("/a\\b\\c.wx").as_str(), "/a/b/c.wx");
	}

	#[test]
	#[should_panic(expected = "must start with `/`")]
	fn absolute_new_rejects_a_relative_path() {
		AbsolutePath::new("a/b");
	}

	#[test]
	#[should_panic(expected = "must not start with `/`")]
	fn relative_new_rejects_an_absolute_path() {
		RelativePath::new("/a/b");
	}

	#[test]
	fn parent_strips_last_segment() {
		assert_eq!(AbsolutePath::new("/src/main.wx").parent().as_str(), "/src");
	}

	#[test]
	fn parent_of_root_file_is_root() {
		assert_eq!(AbsolutePath::new("/main.wx").parent().as_str(), "/");
	}

	#[test]
	fn parent_of_root_is_root() {
		assert_eq!(AbsolutePath::new("/").parent().as_str(), "/");
	}

	#[test]
	fn join_appends_a_segment() {
		assert_eq!(
			AbsolutePath::new("/src")
				.join(&RelativePath::new("main.wx"))
				.as_str(),
			"/src/main.wx"
		);
	}

	#[test]
	fn join_from_root_has_a_single_leading_slash() {
		assert_eq!(
			AbsolutePath::new("/")
				.join(&RelativePath::new("main.wx"))
				.as_str(),
			"/main.wx"
		);
	}

	#[test]
	fn join_collapses_parent_dir_segments() {
		assert_eq!(
			AbsolutePath::new("/crates/wx-compiler/std")
				.join(&RelativePath::new("../other"))
				.as_str(),
			"/crates/wx-compiler/other"
		);
	}

	#[test]
	fn join_collapses_multiple_parent_dir_segments() {
		assert_eq!(
			AbsolutePath::new("/a/b/c")
				.join(&RelativePath::new("../../d"))
				.as_str(),
			"/a/d"
		);
	}

	#[test]
	fn join_collapses_double_slashes() {
		assert_eq!(
			AbsolutePath::new("/a/b/")
				.join(&RelativePath::new("c"))
				.as_str(),
			"/a/b/c"
		);
	}

	#[test]
	fn join_handles_a_multi_segment_relative_reference() {
		assert_eq!(
			AbsolutePath::new("/src")
				.join(&RelativePath::new("math/mod.wx"))
				.as_str(),
			"/src/math/mod.wx"
		);
	}

	#[test]
	fn relative_deserialize_rejects_a_leading_slash() {
		let result: Result<RelativePath, _> =
			serde_json::from_str("\"/etc/passwd\"");
		assert!(result.is_err());
	}

	#[test]
	fn relative_deserialize_accepts_a_relative_path() {
		let result: RelativePath =
			serde_json::from_str("\"../somelib\"").unwrap();
		assert_eq!(result.as_str(), "../somelib");
	}
}
