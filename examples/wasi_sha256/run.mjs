// Runs main.wasm as a WASI Preview 1 command.
//
//   wx build examples/wasi_sha256 -o examples/wasi_sha256/main.wasm
//   printf 'abc' | node examples/wasi_sha256/run.mjs
//   node examples/wasi_sha256/run.mjs examples/sha256/main.wx
//
// The working directory is preopened as "/" (guest fd 3), so file arguments
// are resolved relative to it. Standard input, output and error are inherited.
import { readFile } from "node:fs/promises";
import { WASI } from "node:wasi";

const wasi = new WASI({
	version: "preview1",
	args: ["wx-sha256", ...process.argv.slice(2)],
	env: {},
	preopens: { "/": process.cwd() },
});

const wasmBuffer = await readFile(new URL("./main.wasm", import.meta.url));
const wasmModule = await WebAssembly.compile(wasmBuffer);
const instance = await WebAssembly.instantiate(
	wasmModule,
	wasi.getImportObject(),
);

process.exitCode = wasi.start(instance);
