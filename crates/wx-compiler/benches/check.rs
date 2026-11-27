//! Type-checking benchmark over the stress packages in `benches/check` and
//! every example: the fastest `tir::check` of each, and what one check
//! allocates. Every package includes core, so the stress packages are where
//! a change to one part of the checker shows.
//!
//! Run: `cargo bench -p wx-compiler --bench check [-- options]`
//!
//! - `<filter>`: only packages whose name contains it
//! - `--save <file>`: write the results to compare against later
//! - `--baseline <file>`: print each result's change against a saved run

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::HashMap;
use std::hint::black_box;
use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use std::time::{Duration, Instant};

use wx_compiler::diagnostics::Diagnostics as _;
use wx_compiler::{symbols, tir, vfs};

struct Counting;

static COUNTING: AtomicBool = AtomicBool::new(false);
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static REQUESTED: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

impl Counting {
	fn grow(size: usize) {
		ALLOCATIONS.fetch_add(1, Relaxed);
		REQUESTED.fetch_add(size, Relaxed);
		PEAK.fetch_max(LIVE.fetch_add(size, Relaxed) + size, Relaxed);
	}
}

unsafe impl GlobalAlloc for Counting {
	unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
		if COUNTING.load(Relaxed) {
			Self::grow(layout.size());
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
			LIVE.fetch_sub(layout.size(), Relaxed);
			Self::grow(size);
		}
		unsafe { System.realloc(pointer, layout, size) }
	}
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

struct Measurement {
	time: Duration,
	allocations: usize,
	requested: usize,
	peak: usize,
}

impl Measurement {
	fn fields(&self) -> [f64; 4] {
		[
			self.time.as_secs_f64() * 1e6,
			self.allocations as f64,
			self.requested as f64,
			self.peak as f64,
		]
	}
}

/// What one check allocates. `peak` is the most bytes live at once, counted
/// from zero at the start of the check, so frees of older memory can only
/// lower it.
fn count(run: impl FnOnce() -> tir::Semantics) -> (usize, usize, usize) {
	ALLOCATIONS.store(0, Relaxed);
	REQUESTED.store(0, Relaxed);
	LIVE.store(0, Relaxed);
	PEAK.store(0, Relaxed);
	COUNTING.store(true, Relaxed);
	let sema = run();
	COUNTING.store(false, Relaxed);
	drop(sema);
	(
		ALLOCATIONS.load(Relaxed),
		REQUESTED.load(Relaxed),
		PEAK.load(Relaxed),
	)
}

/// The fastest check within a time budget of about 300 ms, at least 10 runs.
fn fastest(mut run: impl FnMut() -> tir::Semantics) -> Duration {
	let budget = Instant::now();
	let mut best = Duration::MAX;
	let mut runs = 0;
	while runs < 10 || budget.elapsed() < Duration::from_millis(300) {
		let start = Instant::now();
		let sema = black_box(run());
		best = best.min(start.elapsed());
		drop(sema);
		runs += 1;
	}
	best
}

/// The stress packages beside this bench, then every example.
fn packages(filter: Option<&str>) -> Vec<(String, vfs::AbsolutePath)> {
	let root = Path::new(env!("CARGO_MANIFEST_DIR"));
	[
		("stress/", root.join("benches/check")),
		("", root.join("../../examples")),
	]
	.into_iter()
	.flat_map(|(prefix, directory)| {
		let mut packages: Vec<_> = std::fs::read_dir(&directory)
			.unwrap()
			.map(|entry| entry.unwrap().path().canonicalize().unwrap())
			.filter(|path| path.join("wx.json").is_file())
			.map(|path| {
				let name = path.file_name().unwrap().to_string_lossy();
				let path = path.to_string_lossy().into_owned();
				(format!("{prefix}{name}"), vfs::AbsolutePath::new(path))
			})
			.collect();
		packages.sort_by(|a, b| a.0.cmp(&b.0));
		packages
	})
	.filter(|(name, _)| filter.is_none_or(|filter| name.contains(filter)))
	.collect()
}

fn load_baseline(path: &str) -> HashMap<String, [f64; 4]> {
	std::fs::read_to_string(path)
		.unwrap_or_else(|_| panic!("cannot read baseline `{path}`"))
		.lines()
		.map(|line| {
			let mut columns = line.split_whitespace();
			let name = columns.next().unwrap().to_owned();
			let values = columns.map(|value| value.parse().unwrap());
			(
				name,
				std::array::from_fn({
					let mut values = values;
					move |_| values.next().unwrap()
				}),
			)
		})
		.collect()
}

fn change(now: f64, before: Option<f64>) -> String {
	match before {
		Some(before) if before > 0.0 => {
			format!("{:+6.1}%", (now / before - 1.0) * 100.0)
		}
		_ => String::from("      "),
	}
}

fn main() {
	let mut filter = None;
	let mut save = None;
	let mut baseline = None;
	let mut arguments = std::env::args().skip(1);
	while let Some(argument) = arguments.next() {
		match argument.as_str() {
			"--save" => save = arguments.next(),
			"--baseline" => baseline = arguments.next(),
			"--bench" => {}
			_ => filter = Some(argument),
		}
	}
	let baseline = baseline.map(|path| load_baseline(&path));

	println!(
		"{:<20} {:>10} {:>7} {:>10} {:>7} {:>10} {:>7} {:>10} {:>7}  errors",
		"package", "time µs", "", "allocs", "", "alloc KB", "", "peak KB", ""
	);
	let mut results = Vec::new();
	for (name, path) in packages(filter.as_deref()) {
		let mut strings = symbols::Keyword::create_interner();
		let compilation =
			vfs::open_manifest(path, &vfs::NativeFileSource, &mut strings)
				.unwrap_or_else(|()| panic!("cannot load `{name}`"));
		// The first check grows the interner; later ones find their symbols.
		let errors = tir::check(&compilation, &mut strings)
			.diagnostics()
			.error_count();
		let (allocations, requested, peak) =
			count(|| tir::check(&compilation, &mut strings));
		let time = fastest(|| tir::check(&compilation, &mut strings));
		let measurement = Measurement {
			time,
			allocations,
			requested,
			peak,
		};

		let fields = measurement.fields();
		let before = baseline.as_ref().and_then(|baseline| baseline.get(&name));
		let column = |index: usize, scale: f64| {
			format!(
				"{:>10.0} {}",
				fields[index] / scale,
				change(fields[index], before.map(|before| before[index]))
			)
		};
		println!(
			"{name:<20} {} {} {} {}  {errors}",
			column(0, 1.0),
			column(1, 1.0),
			column(2, 1e3),
			column(3, 1e3),
		);
		results.push((name, measurement));
	}

	if let Some(path) = save {
		let lines: String = results
			.iter()
			.map(|(name, measurement)| {
				let [time, allocations, requested, peak] = measurement.fields();
				format!("{name} {time:.2} {allocations} {requested} {peak}\n")
			})
			.collect();
		std::fs::write(&path, lines).unwrap();
		println!("saved to {path}");
	}
}
