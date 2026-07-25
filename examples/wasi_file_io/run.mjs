// Runs main.wasm (compiled from main.wx) as a WASI Preview 1 "command"
// module using Node's built-in WASI runtime, with ./sandbox preopened as
// the guest's first preopened directory (fd 3).
//
//   cargo run -p wx-cli -- compile examples/wasi_file_io/main.wx
//   mv main.wasm examples/wasi_file_io/main.wasm
//   node examples/wasi_file_io/run.mjs

import { readFile } from "node:fs/promises";
import { WASI } from "node:wasi";

const wasi = new WASI({
	version: "preview1",
	args: [],
	env: {},
	preopens: {
		"/sandbox": new URL("./sandbox", import.meta.url).pathname,
	},
});

const wasmBuffer = await readFile(new URL("./main.wasm", import.meta.url));
const wasmModule = await WebAssembly.compile(wasmBuffer);
const instance = await WebAssembly.instantiate(
	wasmModule,
	wasi.getImportObject(),
);

wasi.start(instance);
