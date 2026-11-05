// Build and test the thesis's introductory memory examples.
// Usage: cargo build -p wx-cli
//        node examples/test_memory_examples.mjs
// WX may name another compiler binary. Outputs stay in a temporary directory.
import assert from "node:assert/strict";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
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
    const reports = [];
    const two = await build("two_memories", {
        host: {
            io,
            report: (offset, length) => {
                reports.push(Array.from(new Uint8Array(io.buffer, offset, length)));
            },
        },
    });
    assert.deepEqual(WebAssembly.Module.imports(two.module).sort((a, b) => a.name.localeCompare(b.name)), [
        { module: "host", name: "io", kind: "memory" },
        { module: "host", name: "report", kind: "function" },
    ]);
    assert.equal(sectionIds(two.bytes).includes(5), true, "Internal memory is defined");
    assert.deepEqual(WebAssembly.Module.exports(two.module).map(item => item.name).sort(), [
        "report_input", "sum_input", "sum_internal",
    ]);
    assert.equal(two.exports.sum_input.length, 2);
    assert.equal(two.exports.sum_internal(), 175);
    const ioBytes = new Uint8Array(io.buffer);
    ioBytes.set([1, 2, 3], 0);
    assert.equal(two.exports.sum_input(0, 3), 6);
    two.exports.report_input(0, 3);
    assert.deepEqual(reports, [[1, 2, 3]]);
    ioBytes.fill(0xff);
    assert.equal(two.exports.sum_input(0, 3), 765);
    assert.equal(two.exports.sum_internal(), 175);
    console.log("PASS two_memories: generic sum in both memories; internal bytes not in host io");

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
    assert.match(diagnostics[0].labels.map(label => label.message).join("\n"), /expected .*io::&\[u8\].*found .*internal::&\[u8\]/);
    console.log("PASS wrong_memory: internal-memory slice rejected by host io parameter");
} finally {
    await rm(temporary, { recursive: true, force: true });
}
