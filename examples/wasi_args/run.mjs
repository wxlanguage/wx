// Runs main.wasm (compiled from main.wx) as a WASI Preview 1 "command"
// module using Node's built-in WASI runtime, passing it a few argv entries.
//
//   cargo run -p wx-cli -- compile examples/wasi_args/main.wx
//   mv main.wasm examples/wasi_args/main.wasm
//   node examples/wasi_args/run.mjs

import { readFile } from "node:fs/promises";
import { WASI } from "node:wasi";

const wasi = new WASI({
	version: "preview1",
	args: ["wasi_args_demo", "hello", "world"],
	env: {},
});

const wasmBuffer = await readFile(new URL("./main.wasm", import.meta.url));
const wasmModule = await WebAssembly.compile(wasmBuffer);
const instance = await WebAssembly.instantiate(
	wasmModule,
	wasi.getImportObject(),
);

wasi.start(instance);
