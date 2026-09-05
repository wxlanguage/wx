//! Minimal harness-free lexer throughput benchmark.
//!
//! Run: `cargo bench -p wx-compiler --features bench --bench lexer`

use std::hint::black_box;
use std::time::{Duration, Instant};

use wx_compiler::ast::bench_lex_to_eof;

fn main() {
	// Representative wx source: identifiers/keywords, literals of every
	// flavour, two-char operators, line + doc comments, strings, and a lot of
	// indentation/newlines (what the whitespace-skip path exercises).
	let unit = r#"
/// Compute something over the given inputs.
fn transform(count: i32, scale: f64) -> f64 {
    local mut total = 0.0;
    local limit = 0xFF_u32;
    local mask  = 0b1010_1010;
    local ratio = 1.5e-3;
    local big   = 1_000_000;
    // running accumulation
    local i = 0;
    loop {
        if i >= count { break; }
        total = total + scale * (i as f64);
        i = i + 1;
    }
    local label = "result:";
    total >> 1 == 0 && total << 2 != 0;
    return total / ratio;
}
"#;

	let target = 1usize << 20;
	let mut source = String::with_capacity(target + unit.len());
	while source.len() < target {
		source.push_str(unit);
	}
	let bytes = source.len();

	for _ in 0..30 {
		black_box(bench_lex_to_eof(black_box(&source)));
	}

	let iters = 400;
	let mut best = Duration::MAX;
	let mut tokens = 0usize;
	for _ in 0..iters {
		let start = Instant::now();
		tokens = black_box(bench_lex_to_eof(black_box(&source)));
		best = best.min(start.elapsed());
	}

	let ns = best.as_nanos() as f64;
	println!(
		"lexer: {bytes} bytes, {tokens} tokens | {:.3} ms/pass | {:.3} ns/token | {:.0} MB/s",
		ns / 1e6,
		ns / tokens as f64,
		bytes as f64 / (best.as_secs_f64() * 1e6),
	);
}
