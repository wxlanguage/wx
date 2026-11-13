// Build and test the thesis's introductory memory examples.
// Usage: cargo build -p wx-cli
//        node examples/test_memory_examples.mjs
// WX may name another compiler binary. Outputs stay in a temporary directory.
import assert from "node:assert/strict";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, relative, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { closeSync, openSync } from "node:fs";
import { WASI } from "node:wasi";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));
const wx = process.env.WX || join(root, "target/debug/wx");
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-memory-"));

function command(args) {
    const result = spawnSync(wx, args, { cwd: root, encoding: "utf8", timeout: 20000 });
    if (result.error) throw result.error;
    assert.equal(result.signal, null, `Compiler terminated: ${result.signal}`);
    return result;
}

async function build(name, imports = {}) {
    const output = join(temporary, `${name}.wasm`);
    const result = command(["build", join(root, "examples", name), "-o", output]);
    assert.equal(result.status, 0, result.stdout + result.stderr);
    const bytes = await readFile(output);
    const module = await WebAssembly.compile(bytes);
    const instance = await WebAssembly.instantiate(module, imports);
    return { module, bytes, exports: instance.exports };
}

// Read section IDs, skipping their unsigned LEB128 byte lengths. This checks
// for an actual memory section, not merely the absence of a memory export.
function sectionIds(bytes) {
    const ids = [];
    let cursor = 8;
    while (cursor < bytes.length) {
        ids.push(bytes[cursor++]);
        let size = 0;
        let shift = 0;
        let byte;
        do {
            byte = bytes[cursor++];
            size += (byte & 0x7f) * 2 ** shift;
            shift += 7;
        } while (byte & 0x80);
        cursor += size;
    }
    assert.equal(cursor, bytes.length);
    return ids;
}

try {
    const values = await build("memory_values");
    assert.deepEqual(WebAssembly.Module.imports(values.module), []);
    assert.deepEqual(WebAssembly.Module.exports(values.module), [
        { name: "calibrate", kind: "function" },
    ]);
    assert.equal(sectionIds(values.bytes).includes(5), false, "No linear memory");
    assert.equal(values.exports.calibrate.length, 2);
    for (const [raw, offset] of [[0, 0], [25, -3], [-10, 7], [2147483647, 1]]) {
        assert.deepEqual(values.exports.calibrate(raw, offset), [raw, (raw + offset) | 0]);
    }
    console.log("PASS memory_values: multi-value struct result; no memory or imports");

    const buffer = new WebAssembly.Memory({ initial: 1 });
    const slices = await build("memory_slices", { host: { buffer } });
    assert.deepEqual(WebAssembly.Module.imports(slices.module), [
        { module: "host", name: "buffer", kind: "memory" },
    ]);
    assert.equal(sectionIds(slices.bytes).includes(5), false, "No defined memory");
    assert.equal(slices.exports.sum.length, 2);
    assert.equal(slices.exports.byte_at.length, 3);
    assert.equal(slices.exports.store_byte.length, 2);

    const bytes = new Uint8Array(buffer.buffer);
    const offset = 32;
    const inputs = [
        new Uint8Array(),
        new TextEncoder().encode("Hello, wx! zZ 123\n"),
        Uint8Array.from({ length: 256 }, (_, i) => i),
    ];
    for (const input of inputs) {
        bytes.fill(0xcc);
        bytes.set(input, offset);
        assert.equal(slices.exports.sum(offset, input.length), input.reduce((a, b) => a + b, 0));
        slices.exports.uppercase(offset, input.length);
        const expected = input.map(byte => byte >= 97 && byte <= 122 ? byte - 32 : byte);
        assert.deepEqual(bytes.slice(offset, offset + input.length), expected);
        assert.equal(bytes[offset - 1], 0xcc);
        assert.equal(bytes[offset + input.length], 0xcc);
    }
    slices.exports.store_byte(offset, 42);
    assert.equal(bytes[offset], 42);
    assert.equal(slices.exports.byte_at(offset, 1, 0), 42);
    assert.throws(() => slices.exports.byte_at(offset, 1, 1), WebAssembly.RuntimeError);
    assert.throws(() => slices.exports.byte_at(offset, 0, 0), WebAssembly.RuntimeError);
    assert.throws(() => slices.exports.byte_at(offset, 1, -1), WebAssembly.RuntimeError);
    assert.throws(() => slices.exports.store_byte(bytes.length, 42), WebAssembly.RuntimeError);
    assert.throws(() => slices.exports.sum(bytes.length - 1, 2), WebAssembly.RuntimeError);
    console.log("PASS memory_slices: shared bytes, pointer/slice ABI, ASCII conversion, bounds traps");

    const io = new WebAssembly.Memory({ initial: 1 });
    const two = await build("two_memories", { host: { io } });
    assert.deepEqual(WebAssembly.Module.imports(two.module), [
        { module: "host", name: "io", kind: "memory" },
    ]);
    assert.equal(sectionIds(two.bytes).includes(5), true, "policy memory is defined");
    // The host can send packets and read counters; it gets no handle to the rules.
    assert.deepEqual(WebAssembly.Module.exports(two.module).map(item => item.name).sort(), [
        "accepted", "dropped", "filter", "rule_count",
    ]);
    assert.equal(two.exports.filter.length, 2);
    assert.equal(two.exports.rule_count(), 4);

    // An independent implementation of the documented format and rules.
    const RULES = [[0, 23, 0], [6, 80, 1], [6, 443, 1], [17, 53, 1]];
    const DROP = 0, ACCEPT = 1, MALFORMED = 2;
    function oracle(p) {
        if (p.length < 5 || p[0] !== 1 || 5 + p[4] !== p.length) return MALFORMED;
        const port = p[2] * 256 + p[3];
        for (const [proto, rulePort, action] of RULES) {
            if ((proto === 0 || proto === p[1]) && rulePort === port) return action ? ACCEPT : DROP;
        }
        return DROP;
    }
    const packet = (version, proto, port, payload) =>
        Uint8Array.from([version, proto, port >> 8, port & 255, payload.length, ...payload]);

    const ioBytes = new Uint8Array(io.buffer);
    const at = 64;
    const cases = [
        packet(1, 6, 80, []), packet(1, 6, 443, [1, 2, 3]), packet(1, 17, 53, [9]),
        packet(1, 17, 80, []), packet(1, 6, 23, []), packet(1, 17, 23, [0]),
        packet(1, 6, 8080, []), packet(2, 6, 80, []),
        packet(1, 6, 80, [1, 2]).slice(0, 6), // length byte says 2, only 1 payload byte present
        packet(1, 6, 80, [1]).slice(0, 3),    // header cut short
        new Uint8Array(),
    ];
    // Exhaustive over protocols and a spread of ports, with and without payload.
    for (const proto of [0, 6, 17, 99]) {
        for (const port of [0, 22, 23, 53, 80, 443, 444, 0x1bb + 256, 65535]) {
            cases.push(packet(1, proto, port, []), packet(1, proto, port, [7, 7]));
        }
    }
    let accepted = 0, dropped = 0;
    for (const input of cases) {
        ioBytes.fill(0xcc);
        ioBytes.set(input, at);
        const expected = oracle(input);
        assert.equal(two.exports.filter(at, input.length), expected, `packet ${Array.from(input)}`);
        if (expected === ACCEPT) accepted++; else dropped++;
    }
    assert.equal(two.exports.accepted(), accepted);
    assert.equal(two.exports.dropped(), dropped);
    // A forged slice that starts outside the memory traps on its first read: that check is Wasm's.
    assert.throws(() => two.exports.filter(ioBytes.length, 5), WebAssembly.RuntimeError);
    console.log(`PASS two_memories: ${cases.length} packets match the oracle; rules stay private`);

    const data = new WebAssembly.Memory({ initial: 1 });
    const search = await build("search", { host: { data } });
    const mem = new Uint8Array(data.buffer);
    const encoder = new TextEncoder();
    const searchCases = [
        ["hello world", "world"], ["hello world", "hello"], ["hello world", "o w"],
        ["hello world", "xyz"], ["aaaaab", "aab"], ["abcabcabd", "abd"], ["abc", "abcd"],
        ["abc", "c"], ["abc", ""], ["", "a"], ["", ""], ["mississippi", "issip"],
        ["mississippi", "ssi"], ["aaaa", "aaaa"], ["aaaa", "aaaaa"],
    ];
    for (const [text, pattern] of searchCases) {
        const h = encoder.encode(text), n = encoder.encode(pattern);
        mem.fill(0xcc);
        mem.set(h, 100);
        mem.set(n, 500);
        const expected = text.indexOf(pattern);
        // `find` returns (found, position): the Bool is the enum's u8 held as an i32.
        assert.deepEqual(
            search.exports.find(100, h.length, 500, n.length),
            expected < 0 ? [0, 0] : [1, expected],
            `find(${JSON.stringify(text)}, ${JSON.stringify(pattern)})`,
        );
    }
    console.log(`PASS search: ${searchCases.length} substring cases match String.indexOf`);

    // Hello, world in a browser: the same loader index.html uses.
    {
        const output = join(temporary, "hello.wasm");
        const built = command(["build", join(root, "examples/hello_browser"), "-o", output]);
        assert.equal(built.status, 0, built.stdout + built.stderr);
        const bytes = await readFile(output);
        const module = await WebAssembly.compile(bytes);
        assert.deepEqual(WebAssembly.Module.imports(module), [{ module: "env", name: "print", kind: "function" }]);
        assert.deepEqual(WebAssembly.Module.exports(module).map(item => item.name).sort(), ["main", "memory"]);
        const { run } = await import(join(root, "examples/hello_browser/hello.mjs"));
        const lines = [];
        await run(bytes, line => lines.push(line));
        assert.deepEqual(lines, ["Hello, world!"]);
        console.log(`PASS hello_browser: ${bytes.length} bytes, prints through env.print`);
    }

    // Hello, world for WASI, run under Node's WASI with stdout sent to a file.
    {
        const output = join(temporary, "hello_wasi.wasm");
        const built = command(["build", join(root, "examples/hello_wasi"), "-o", output]);
        assert.equal(built.status, 0, built.stdout + built.stderr);
        const bytes = await readFile(output);
        const module = await WebAssembly.compile(bytes);
        assert.deepEqual(WebAssembly.Module.imports(module), [
            { module: "wasi_snapshot_preview1", name: "fd_write", kind: "function" },
        ]);
        const stdoutPath = join(temporary, "stdout.txt");
        const stdout = openSync(stdoutPath, "w");
        const wasi = new WASI({ version: "preview1", args: [], env: {}, stdout });
        const instance = await WebAssembly.instantiate(module, wasi.getImportObject());
        wasi.start(instance);
        closeSync(stdout);
        assert.equal(await readFile(stdoutPath, "utf8"), "Hello, world!\n");
        console.log(`PASS hello_wasi: ${bytes.length} bytes, writes to stdout through fd_write`);
    }

    // Streaming WASI programs (cat and wc) over the shared `wasi` package.
    {
        const run = async (name, input) => {
            const output = join(temporary, `${name}.wasm`);
            const built = command(["build", join(root, "examples", name), "-o", output]);
            assert.equal(built.status, 0, built.stdout + built.stderr);
            const module = await WebAssembly.compile(await readFile(output));
            const stdinPath = join(temporary, `${name}.in`), stdoutPath = join(temporary, `${name}.out`);
            await writeFile(stdinPath, input);
            const stdin = openSync(stdinPath, "r"), stdout = openSync(stdoutPath, "w");
            const wasi = new WASI({ version: "preview1", args: [], env: {}, stdin, stdout });
            wasi.start(await WebAssembly.instantiate(module, wasi.getImportObject()));
            closeSync(stdin);
            closeSync(stdout);
            return readFile(stdoutPath);
        };
        // The documented convention: a line is a byte 10, a word a run of bytes
        // that are not ASCII whitespace (9 to 13 and 32).
        const isSpace = byte => byte === 32 || (byte >= 9 && byte <= 13);
        const count = bytes => {
            let words = 0, inWord = false;
            for (const byte of bytes) {
                if (isSpace(byte)) inWord = false;
                else { if (!inWord) words++; inWord = true; }
            }
            return `${bytes.filter(byte => byte === 10).length} ${words} ${bytes.length}\n`;
        };
        let seed = 1;
        const random = limit => (seed = (seed * 1103515245 + 12345) >>> 0) % limit;
        const inputs = [
            new Uint8Array(),
            encoder.encode("Hello, wx!\nsecond line  with   spaces\n\tTabbed\r\nno trailing newline"),
            encoder.encode("a".repeat(5000) + " tail\n"),              // a word across the 4096-byte buffer
            encoder.encode("x".repeat(4095) + " y" + " z".repeat(3000)), // a space at the buffer's edge
            Uint8Array.from({ length: 300000 }, () => "abc \n\t".charCodeAt(random(6))),
            Uint8Array.from({ length: 20000 }, () => random(256)),
        ];
        for (const input of inputs) {
            assert.deepEqual(new Uint8Array(await run("wasi_cat", input)), input, `cat of ${input.length} bytes`);
            assert.equal((await run("wasi_wc", input)).toString(), count(input), `wc of ${input.length} bytes`);
        }
        // `or_exit` ends the program with the errno as its status: a write to a
        // descriptor that does not exist is `Badf` (8), and nothing runs after.
        {
            const bad = join(temporary, "bad_descriptor");
            await mkdir(bad);
            const dependency = relative(bad, join(root, "examples/wasi"));
            await writeFile(join(bad, "wx.json"), JSON.stringify({
                type: "bin", entry: "main.wx", dependencies: { wasi: { type: "local", path: dependency } },
            }));
            await writeFile(join(bad, "main.wx"), [
                'package "wasi" as wasi;',
                "use wasi::{Fd, heap};",
                "func main() {",
                "    local arena = wasi::arena();",
                '    Fd::Stdout.write(arena, "ok\\n");',
                '    Fd::from_raw(99).write(arena, "never\\n");',
                '    Fd::Stdout.write(arena, "unreachable\\n");',
                "}",
                'export { main as "_start", heap as "memory" }',
            ].join("\n"));
            const output = join(temporary, "bad_descriptor.wasm");
            const built = command(["build", bad, "-o", output]);
            assert.equal(built.status, 0, built.stdout + built.stderr);
            const stdoutPath = join(temporary, "bad.out");
            const stdout = openSync(stdoutPath, "w");
            const wasi = new WASI({ version: "preview1", args: [], env: {}, stdout, returnOnExit: true });
            const module = await WebAssembly.compile(await readFile(output));
            const status = wasi.start(await WebAssembly.instantiate(module, wasi.getImportObject()));
            closeSync(stdout);
            assert.equal(status, 8);
            assert.equal(await readFile(stdoutPath, "utf8"), "ok\n");
        }
        // `args`, `panic`, `write_signed` and `write_hex`, through a program written here.
        {
            const buildLocal = async (name, source) => {
                const dir = join(temporary, name);
                await mkdir(dir);
                await writeFile(join(dir, "wx.json"), JSON.stringify({
                    type: "bin", entry: "main.wx",
                    dependencies: {
                        wasi: { type: "local", path: relative(dir, join(root, "examples/wasi")) },
                        fmt: { type: "local", path: relative(dir, join(root, "examples/fmt")) },
                    },
                }));
                await writeFile(join(dir, "main.wx"), source);
                const output = join(temporary, `${name}.wasm`);
                const built = command(["build", dir, "-o", output]);
                assert.equal(built.status, 0, built.stdout + built.stderr);
                return WebAssembly.compile(await readFile(output));
            };
            const runWith = async (module, args) => {
                const out = join(temporary, "args.out"), err = join(temporary, "args.err");
                const stdout = openSync(out, "w"), stderr = openSync(err, "w");
                const wasi = new WASI({ version: "preview1", args, env: {}, stdout, stderr, returnOnExit: true });
                const status = wasi.start(await WebAssembly.instantiate(module, wasi.getImportObject()));
                closeSync(stdout);
                closeSync(stderr);
                return { status, out: await readFile(out, "utf8"), err: await readFile(err, "utf8") };
            };
            const argsModule = await (async () => {
                const output = join(temporary, "wasi_args.wasm");
                const built = command(["build", join(root, "examples/wasi_args"), "-o", output]);
                assert.equal(built.status, 0, built.stdout + built.stderr);
                return WebAssembly.compile(await readFile(output));
            })();
            const many = await runWith(argsModule, ["prog", "hello", "wörld", "x".repeat(300)]);
            assert.equal(many.status, 0);
            assert.equal(many.out, `0: prog\n1: hello\n2: wörld\n3: ${"x".repeat(300)}\n`);
            const none = await runWith(argsModule, ["prog"]);
            assert.equal(none.status, 1);
            assert.equal(none.out, "");
            assert.equal(none.err, "usage: args <word>...\n");
            const lots = ["prog", ...Array.from({ length: 600 }, (_, i) => "argument" + i)];
            const big = await runWith(argsModule, lots);
            assert.equal(big.status, 0);
            assert.equal(big.out, lots.map((a, i) => `${i}: ${a}\n`).join(""), "the allocator grows the memory for many arguments");

            const numbers = await buildLocal("numbers", [
                'package "wasi" as wasi;',
                'package "fmt" as fmt;',
                "use wasi::{Fd, heap};",
                "func line(arena: heap::*wasi::Arena, buffer: heap::*[u8], value: i32) {",
                "    Fd::Stdout.write(arena, fmt::signed::<heap>(buffer, value));",
                '    Fd::Stdout.write(arena, " ");',
                "    Fd::Stdout.write(arena, fmt::hex::<heap>(buffer, transmute(value)));",
                '    Fd::Stdout.write(arena, "\\n");',
                "}",
                "func main() {",
                "    local arena = wasi::arena();",
                "    local buffer = arena.allocate_slice_uninit::<u8>(fmt::SIGNED_LEN);",
                "    line(arena, buffer, 0); line(arena, buffer, 7); line(arena, buffer, -1);",
                "    line(arena, buffer, 255); line(arena, buffer, -2147483648);",
                "    line(arena, buffer, 2147483647);",
                "}",
                'export { main as "_start", heap as "memory" }',
            ].join("\n"));
            const result = await runWith(numbers, []);
            assert.equal(result.status, 0);
            assert.equal(result.out, [0, 7, -1, 255, -2147483648, 2147483647]
                .map(n => `${n} ${(n >>> 0).toString(16)}\n`).join(""));
        }
        console.log(`PASS wasi_cat, wasi_wc: ${inputs.length} inputs (up to 300000 bytes) match; a failed write exits with its errno`);
    }

    const negative = join(temporary, "wrong_memory");
    await mkdir(negative);
    await writeFile(join(negative, "wx.json"), JSON.stringify({ type: "bin", entry: "main.wx" }));
    const source = await readFile(resolve(root, "examples/two_memories/main.wx"), "utf8");
    const wrong = await readFile(resolve(root, "examples/two_memories/wrong_memory.wx.fail"), "utf8");
    await writeFile(join(negative, "main.wx"), `${source}\n${wrong}`);
    const rejected = command(["check", negative, "--message-format", "json"]);
    assert.equal(rejected.status, 1, rejected.stdout + rejected.stderr);
    const diagnostics = rejected.stderr.split("\n").filter(line => line.startsWith("{")).map(line => JSON.parse(line));
    assert.equal(diagnostics.length, 1, rejected.stderr);
    assert.equal(diagnostics[0].code, "E2001");
    assert.match(diagnostics[0].labels.map(label => label.message).join("\n"), /expected .*io::&\[u8\].*found .*policy::&\[u8\]/);
    console.log("PASS wrong_memory: policy-memory slice rejected by host io parameter");
} finally {
    await rm(temporary, { recursive: true, force: true });
}
