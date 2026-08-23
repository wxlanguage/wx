//! Embeds every `std/**/*.wx` file into the compiler at build time.
//!
//! The stdlib has to be available with no filesystem behind it: `wx` ships as
//! a single binary, and `wx-lsp-wasm` runs in a browser. Walking the directory
//! here, rather than maintaining a hand-written `include_str!` list, means
//! adding a stdlib file is just creating it and writing the `module`
//! declaration that references it — there is no third place to update and
//! forget, which would otherwise surface as a confusing "module file not
//! found" pointing at a file that is right there on disk.

use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

fn main() {
	let manifest_dir = PathBuf::from(
		env::var("CARGO_MANIFEST_DIR")
			.expect("cargo always sets CARGO_MANIFEST_DIR"),
	);
	let std_dir = manifest_dir.join("std");

	// Cargo rescans a directory target recursively, so this covers files being
	// added and removed, not just edited.
	println!("cargo:rerun-if-changed={}", std_dir.display());

	let mut entries = Vec::new();
	collect_wx_files(&std_dir, &std_dir, &mut entries);
	// Sorted so the generated table, and therefore the build, is reproducible.
	entries.sort();

	assert!(
		entries.iter().any(|(relative, _)| relative == "/main.wx"),
		"std/main.wx is the stdlib crate root and must exist"
	);

	let mut generated = String::from("&[\n");
	for (relative, absolute) in &entries {
		writeln!(generated, "\t({relative:?}, include_str!({absolute:?})),")
			.expect("writing to a String cannot fail");
	}
	generated.push_str("]\n");

	let out_path =
		PathBuf::from(env::var("OUT_DIR").expect("cargo always sets OUT_DIR"))
			.join("stdlib_files.rs");
	fs::write(&out_path, generated)
		.expect("OUT_DIR should be writable during a build");
}

/// Collects `("/"-prefixed path relative to `std/`, absolute path)` for
/// every `.wx` file under `dir`, recursively.
///
/// The first element is `/`-prefixed and always uses `/` as a separator, on
/// every platform, matching `vfs::AbsolutePath`'s own convention directly —
/// `load_stdlib` can then wrap each entry as-is, with no runtime
/// string-patching step to make it absolute.
fn collect_wx_files(root: &Path, dir: &Path, out: &mut Vec<(String, String)>) {
	let read = fs::read_dir(dir)
		.unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()));
	for entry in read {
		let path = entry
			.unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
			.path();
		if path.is_dir() {
			collect_wx_files(root, &path, out);
		} else if path.extension().is_some_and(|ext| ext == "wx") {
			let relative = path
				.strip_prefix(root)
				.expect("walked path is always under root")
				.to_string_lossy()
				.replace('\\', "/");
			out.push((
				format!("/{relative}"),
				path.to_string_lossy().into_owned(),
			));
		}
	}
}
