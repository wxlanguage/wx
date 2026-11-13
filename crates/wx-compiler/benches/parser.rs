//! Parser benchmark over every `.wx` file in the repository: lexing, parsing
//! and dropping the tree, timed separately, and what one parse allocates.
//!
//! Run: `cargo bench -p wx-compiler --features bench --bench parser`
//!
//! The numbers it prints are the baseline `notes/ast-arena-plan.md` measures
//! the arena AST against.

use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::mem::size_of;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use std::time::{Duration, Instant};

use wx_compiler::ast::{self, Parser};
use wx_compiler::vfs::{FileOrigin, Files};

/// The system allocator, counting while `COUNTING` is set. It is off while
/// timing, so the timings pay one relaxed load per allocation and nothing
/// more.
struct Counting;

static COUNTING: AtomicBool = AtomicBool::new(false);
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static REALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static REQUESTED: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
	unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
		if COUNTING.load(Relaxed) {
			ALLOCATIONS.fetch_add(1, Relaxed);
			REQUESTED.fetch_add(layout.size(), Relaxed);
			LIVE.fetch_add(layout.size(), Relaxed);
		}
		unsafe { System.alloc(layout) }
	}

	unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
		if COUNTING.load(Relaxed) {
			LIVE.fetch_sub(layout.size(), Relaxed);
		}
		unsafe { System.dealloc(pointer, layout) }
	}

	unsafe fn realloc(
		&self,
		pointer: *mut u8,
		layout: Layout,
		size: usize,
	) -> *mut u8 {
		if COUNTING.load(Relaxed) {
			REALLOCATIONS.fetch_add(1, Relaxed);
			REQUESTED.fetch_add(size, Relaxed);
			LIVE.fetch_add(size, Relaxed);
			LIVE.fetch_sub(layout.size(), Relaxed);
		}
		unsafe { System.realloc(pointer, layout, size) }
	}
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

/// The core and every example, in a stable order.
fn corpus() -> Vec<(String, String)> {
	let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
	let mut directories: Vec<PathBuf> =
		["crates/wx-compiler/core", "examples", "doom"]
			.iter()
			.map(|directory| root.join(directory))
			.collect();
	let mut files = Vec::new();
	while let Some(directory) = directories.pop() {
		let Ok(entries) = std::fs::read_dir(&directory) else {
			continue;
		};
		for entry in entries {
			let path = entry.unwrap().path();
			if path.is_dir() {
				directories.push(path);
			} else if path
				.extension()
				.is_some_and(|extension| extension == "wx")
			{
				let source = std::fs::read_to_string(&path).unwrap();
				files.push((path.display().to_string(), source));
			}
		}
	}
	files.sort();
	files
}

/// The fastest of `iterations` runs, after a warm-up.
fn fastest(iterations: usize, mut run: impl FnMut() -> Duration) -> Duration {
	for _ in 0..20 {
		run();
	}
	(0..iterations).map(|_| run()).min().unwrap()
}

fn main() {
	let sources = corpus();
	let mut files = Files::new();
	let ids: Vec<_> = sources
		.iter()
		.map(|(name, source)| {
			files
				.add(name.clone(), source.clone(), FileOrigin::Local)
				.unwrap()
		})
		.collect();
	let bytes: usize = sources.iter().map(|(_, source)| source.len()).sum();
	let tokens: usize = sources
		.iter()
		.map(|(_, source)| ast::bench_lex_to_eof(source))
		.sum();
	let mut strings = ast::Keyword::create_interner();

	println!(
		"corpus: {} files, {bytes} bytes, {tokens} tokens",
		ids.len()
	);
	println!(
		"node sizes: Spanned<Expression> {} B, TypeExpression {} B, Pattern {} B, \
		 Statement {} B, Item {} B, PathSegment {} B",
		size_of::<ast::Spanned<ast::Expression>>(),
		size_of::<ast::TypeExpression>(),
		size_of::<ast::Pattern>(),
		size_of::<ast::Statement>(),
		size_of::<ast::Item>(),
		size_of::<ast::PathSegment>(),
	);

	// One parse of the corpus, counted. The interner is warmed first, so its
	// own growth is not counted as the tree's.
	for &id in &ids {
		drop(Parser::parse(id, &files, &mut strings));
	}
	COUNTING.store(true, Relaxed);
	let trees: Vec<_> = ids
		.iter()
		.map(|&id| Parser::parse(id, &files, &mut strings))
		.collect();
	let retained = LIVE.load(Relaxed);
	COUNTING.store(false, Relaxed);
	drop(trees);
	let allocations = ALLOCATIONS.load(Relaxed);
	let reallocations = REALLOCATIONS.load(Relaxed);
	let requested = REQUESTED.load(Relaxed);
	let per_token = |n: usize| n as f64 / tokens as f64;
	println!(
		"allocations: {allocations} + {reallocations} reallocations ({:.2}/token), \
		 {requested} bytes requested ({:.1} B/token)",
		per_token(allocations + reallocations),
		per_token(requested),
	);
	println!(
		"retained tree: {retained} bytes ({:.1} B/token, {:.2}x the source)",
		per_token(retained),
		retained as f64 / bytes as f64,
	);

	let iterations = 300;
	let lex = fastest(iterations, || {
		let start = Instant::now();
		for (_, source) in &sources {
			black_box(ast::bench_lex_to_eof(black_box(source)));
		}
		start.elapsed()
	});
	let mut trees = Vec::with_capacity(ids.len());
	let mut drop_time = Duration::MAX;
	let parse = fastest(iterations, || {
		let start = Instant::now();
		for &id in &ids {
			trees.push(Parser::parse(id, &files, &mut strings));
		}
		let parse = start.elapsed();
		let start = Instant::now();
		trees.clear();
		drop_time = drop_time.min(start.elapsed());
		parse
	});

	let report = |time: Duration| {
		format!(
			"{:.3} ms ({:.1} ns/token, {:.0} MB/s)",
			time.as_secs_f64() * 1e3,
			time.as_nanos() as f64 / tokens as f64,
			bytes as f64 / time.as_secs_f64() / 1e6,
		)
	};
	println!("lex:        {}", report(lex));
	println!("lex+parse:  {}", report(parse));
	println!("drop tree:  {}", report(drop_time));
}
