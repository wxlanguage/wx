#!/bin/bash
# Build a wx project to .wasm and optimize with wasm-opt

if [ $# -eq 0 ]; then
    echo "Usage: $0 <project-dir> [optimization-level]"
    echo "  optimization-level: -O0, -O1, -O2, -O3, -O4, -Os, -Oz (default: -O3)"
    exit 1
fi

PROJECT_DIR="$1"
OPT_LEVEL="${2:--O3}"

if [ ! -d "$PROJECT_DIR" ]; then
    echo "Error: directory '$PROJECT_DIR' not found"
    exit 1
fi

BASENAME=$(basename "$PROJECT_DIR")
OUTPUT_WASM="${BASENAME}.wasm"
OPTIMIZED_WASM="${BASENAME}.optimized.wasm"

echo "=== Building $PROJECT_DIR ==="
./target/release/wx build "$PROJECT_DIR" -o "$OUTPUT_WASM"

if [ $? -ne 0 ]; then
    echo "Build failed!"
    exit 1
fi

echo ""
echo "=== Optimizing with wasm-opt $OPT_LEVEL ==="
wasm-opt $OPT_LEVEL "$OUTPUT_WASM" -o "$OPTIMIZED_WASM"

if [ $? -ne 0 ]; then
    echo "Optimization failed!"
    exit 1
fi

echo ""
echo "=== Results ==="
ORIGINAL_SIZE=$(wc -c < "$OUTPUT_WASM" | tr -d ' ')
OPTIMIZED_SIZE=$(wc -c < "$OPTIMIZED_WASM" | tr -d ' ')
SAVED=$((ORIGINAL_SIZE - OPTIMIZED_SIZE))
PERCENT=$((100 - OPTIMIZED_SIZE * 100 / ORIGINAL_SIZE))

echo "Original:  $OUTPUT_WASM ($ORIGINAL_SIZE bytes)"
echo "Optimized: $OPTIMIZED_WASM ($OPTIMIZED_SIZE bytes)"
echo "Saved:     $SAVED bytes ($PERCENT% reduction)"
echo ""
echo "✓ Done! Use $OPTIMIZED_WASM for production"
