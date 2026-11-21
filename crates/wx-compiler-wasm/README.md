# wx-compiler-wasm

JavaScript bindings for the WX compiler, with embedded core and an in-memory
filesystem. Compiling WX does not require WASI or host filesystem access.

## API

```ts
import init, { compile, compile_package } from "wx-compiler-wasm";
await init();

const result = compile("main.wx", {
  "main.wx": "func answer() -> i32 { 42 } export { answer }",
});
if (result.bytecode) {
  const { instance } = await WebAssembly.instantiate(result.bytecode);
  console.log(instance.exports.answer()); // 42
}

const packaged = compile_package("app", {
  "app/wx.json": '{ "entry": "main.wx" }',
  "app/main.wx": "func answer() -> i32 { 42 } export { answer }",
});
```

- `compile(entry_path, files)` loads an entry file and its modules without a
  manifest. This preserves the playground API.
- `compile_package(package_path, files)` takes a package **directory** and uses
  the same `wx.json` resolver as the CLI. Include dependency manifests and WX
  sources in the file map; local dependency paths are relative to the declaring
  manifest's directory.

Paths may be absolute or relative to a synthetic `/` root. Both forms are
normalized at the JS boundary, including separators and `.`/`..`; duplicate
normalized file keys throw an exception. No path is read from the host disk.

Both functions return `{ diagnostics, bytecode }`. Warnings remain in diagnostics
alongside successful bytecode (`Uint8Array`); errors and bugs yield `null`
bytecode. Loading/parsing and checking/lowering diagnostics use the compiler's
shared collection and severity rules. Malformed JS input, missing entry files,
manifest-resolution failures, and backend failures throw exceptions. The current
manifest resolver exposes only a generic loading failure to the wrapper.

The wrapper owns a keyword-seeded interner for each call. Loading produces a
`CompilationUnit`, `tir::check` produces `Semantics`, and `tir::lower` produces
MIR. `backend::emit` then runs default inlining, optimization, reachability, and
code generation, matching the CLI. There is no retained compiler session between
calls. Diagnostic labels preserve the existing numeric `file_id` contract;
returning a source-file lookup table is a future API extension.

## Build and validate

Run from the repository root. Install the `wasm32-unknown-unknown` Rust target,
`wasm-pack`, and, for the manual commands, `wasm-bindgen-cli` matching the
`wasm-bindgen` version in `Cargo.lock`.

For the usual browser package with JS, TypeScript declarations, and Wasm:

```sh
wasm-pack build crates/wx-compiler-wasm --target web --release
```

The old member-local release profile was ignored by Cargo. The workspace's
`wasm-release` profile explicitly selects `opt-level = "s"`, LTO, and one codegen
unit without changing ordinary native release builds. To build and inspect it:

```sh
CARGO_TARGET_DIR=target/compiler-wasm cargo build -p wx-compiler-wasm \
  --target wasm32-unknown-unknown --profile wasm-release
wasm-bindgen target/compiler-wasm/wasm32-unknown-unknown/wasm-release/wx_compiler_wasm.wasm \
  --target web --out-dir target/compiler-wasm/pkg
```

The JS boundary tests execute the **Wasm compiler**, then instantiate and execute
its WX output. They cover modules, generics, inlining, warnings, source errors,
invalid inputs, manifest dependencies, and repository examples. Node bindings
avoid needing a browser test runner:

```sh
wasm-bindgen target/compiler-wasm/wasm32-unknown-unknown/wasm-release/wx_compiler_wasm.wasm \
  --target nodejs --out-dir target/compiler-wasm/pkg-node
node crates/wx-compiler-wasm/tests/compile.mjs target/compiler-wasm/pkg-node
cargo check --workspace
cargo clippy -p wx-compiler-wasm --no-deps -- -D warnings
cargo fmt --check
```

Node tests do not exercise browser fetching or the playground UI.

## Size measurements

Measured on 2026-11-16 with rustc 1.97.0, wasm-bindgen 0.2.100, and Binaryen
117. Sizes include embedded core and the complete compilation pipeline. Gzip
uses level 9 and Brotli uses quality 11; values below are decimal bytes. Browser
rows exclude JS glue.

| Artifact | Bytes | Gzip bytes | Brotli bytes |
| --- | ---: | ---: | ---: |
| Cargo `release`, before wasm-bindgen | 2,002,155 | 657,513 | 492,673 |
| Browser bindings, `release` | 1,718,158 | 629,977 | 467,964 |
| Cargo `wasm-release`, before wasm-bindgen | 1,651,974 | 555,680 | 425,752 |
| Browser bindings, `wasm-release` | 1,400,463 | 510,773 | 397,404 |
| Browser bindings, `wasm-release` + `wasm-opt -Oz` | 1,299,334 | 529,829 | 412,448 |
| Browser JS glue | 17,485 | 4,065 | 3,542 |

The final Binaryen pass reduces raw size but **increases compressed size** for this
build. Keep its output separate when comparing deployment artifacts:

```sh
wasm-opt -Oz --enable-bulk-memory --enable-nontrapping-float-to-int \
  --enable-sign-ext target/compiler-wasm/pkg/wx_compiler_wasm_bg.wasm \
  -o target/compiler-wasm/pkg/wx_compiler_wasm_bg.opt.wasm
```

All six JS boundary tests passed with ordinary release bindings, size-profile
bindings, and the Binaryen-optimized browser module loaded in Node. To exercise
the browser bindings directly in Node (with bytes supplied instead of fetching):

```sh
node crates/wx-compiler-wasm/tests/compile.mjs target/compiler-wasm/pkg --web
```

These are artifact/download sizes, not runtime memory measurements. Compilation
speed has not been benchmarked between the profiles.
