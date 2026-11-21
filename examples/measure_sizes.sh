#!/bin/sh
# Module sizes of the thesis examples, as the compiler emits them and, when
# binaryen's wasm-opt is on the PATH, after `wasm-opt -Oz`.
# Usage: cargo build -p wx-cli && sh examples/measure_sizes.sh
set -e
cd "$(dirname "$0")/.."
wx=${WX:-target/debug/wx}
out=$(mktemp -d)
printf '%-16s %8s %10s\n' program raw wasm-opt-Oz
for name in hello_browser hello_wasi memory_values memory_slices search two_memories wasi_cat wasi_wc wasi_args; do
  $wx build "examples/$name" -o "$out/$name.wasm" >/dev/null 2>&1
  raw=$(wc -c < "$out/$name.wasm")
  opt=-
  if command -v wasm-opt >/dev/null; then
    wasm-opt -Oz --all-features "$out/$name.wasm" -o "$out/$name.opt.wasm"
    opt=$(wc -c < "$out/$name.opt.wasm")
  fi
  printf '%-16s %8s %10s\n' "$name" "$raw" "$opt"
done
