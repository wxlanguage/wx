// End-to-end test for the `wx-sha256` WASI command.
//
//   node examples/wasi_sha256/test.mjs
//
// The command is compiled with WX and then run under Node's WASI runtime, so
// this covers file descriptors, argument parsing, preopened paths, stdin and
// the library's host boundary as one unit. Expected digests come from node:crypto.
import assert from "node:assert/strict";
import { createHash, randomBytes } from "node:crypto";
import { spawnSync } from "node:child_process";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const here = fileURLToPath(new URL(".", import.meta.url));
const root = fileURLToPath(new URL("../../", import.meta.url));
const wasm = join(here, "main.wasm");
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-sha256-cli-"));
try {
    const built = spawnSync(process.env.WX || "wx",
        ["build", join(root, "examples/wasi_sha256"), "-o", wasm],
        { cwd: root, encoding: "utf8", timeout: 60000 });
    if (built.error) throw built.error;
    assert.equal(built.status, 0, built.stdout + built.stderr);

    function run(args, input = Buffer.alloc(0)) {
        const result = spawnSync(process.execPath,
            [join(here, "run.mjs"), ...args],
            { cwd: temporary, input, encoding: "buffer", timeout: 60000 });
        if (result.error) throw result.error;
        return {
            status: result.status,
            stdout: result.stdout.toString(),
            stderr: result.stderr.toString(),
        };
    }

    const digest = bytes => createHash("sha256").update(bytes).digest("hex");
    const cases = [
        Buffer.alloc(0),
        Buffer.from("abc"),
        Buffer.from("hello world\n"),
        Buffer.from("a".repeat(55)),
        Buffer.from("a".repeat(56)),
        Buffer.from("a".repeat(64)),
        Buffer.from("a".repeat(65)),
        randomBytes(4096),
        randomBytes(1_000_000),
    ];
    for (const input of cases) {
        const result = run([], input);
        assert.equal(result.status, 0, result.stderr);
        assert.equal(result.stdout, `${digest(input)}  -\n`, `stdin ${input.length}`);
    }
    // An explicit "-" means standard input even when other arguments follow.
    const stdinDash = run(["-"], Buffer.from("abc"));
    assert.equal(stdinDash.stdout, `${digest("abc")}  -\n`);

    const first = randomBytes(777);
    const second = randomBytes(31);
    await writeFile(join(temporary, "first.bin"), first);
    await writeFile(join(temporary, "second.bin"), second);
    const files = run(["first.bin", "second.bin"]);
    assert.equal(files.status, 0, files.stderr);
    assert.equal(files.stdout,
        `${digest(first)}  first.bin\n${digest(second)}  second.bin\n`);

    const missing = run(["does-not-exist"]);
    assert.equal(missing.status, 1);
    assert.match(missing.stderr, /cannot open input/);

    // A path with a space exercises WASI's string argument passing.
    await writeFile(join(temporary, "two words.txt"), "spaced");
    const spaced = run(["two words.txt"]);
    assert.equal(spaced.status, 0, spaced.stderr);
    assert.equal(spaced.stdout,
        `${digest("spaced")}  two words.txt\n`);

    // The tool is also a normal Wasm module: only `_start` and its memory cross
    // the boundary, and the SHA-256 package's scratch memory stays private.
    const module = await WebAssembly.compile(await readFile(wasm));
    assert.deepEqual(WebAssembly.Module.exports(module).map(e => e.name).sort(),
        ["_start", "memory"]);
    assert.deepEqual(
        WebAssembly.Module.imports(module).map(({ module, name }) => `${module}.${name}`).sort(),
        [
            "wasi_snapshot_preview1.args_get",
            "wasi_snapshot_preview1.args_sizes_get",
            "wasi_snapshot_preview1.fd_close",
            "wasi_snapshot_preview1.fd_read",
            "wasi_snapshot_preview1.fd_write",
            "wasi_snapshot_preview1.path_open",
            "wasi_snapshot_preview1.proc_exit",
        ],
    );

    console.log(`${cases.length} stdin hashes and file arguments match node:crypto`);
    console.log("PASS missing file: message and exit status 1");
    console.log("PASS paths with spaces, explicit - and multiple files");
    console.log(`Command: ${(await readFile(wasm)).length} Wasm bytes`);
} finally {
    await rm(temporary, { recursive: true, force: true });
}
