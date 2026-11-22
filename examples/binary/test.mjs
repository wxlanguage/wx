// node examples/binary/test.mjs; WX may select a compiler executable.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtemp, mkdir, writeFile, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../../", import.meta.url));
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-binary-"));
const formats = [
    ["u8", 1, false],
    ["u16_le", 2, true], ["u16_be", 2, false],
    ["u32_le", 4, true], ["u32_be", 4, false],
    ["u64_le", 8, true], ["u64_be", 8, false],
];

async function build(bits) {
    const dir = join(temporary, `memory${bits}`);
    await mkdir(dir);
    await writeFile(join(dir, "wx.json"), JSON.stringify({
        entry: "main.wx",
        dependencies: { binary: { type: "local", path: relative(dir, join(root, "examples/binary")) } },
    }));
    const size = `u${bits}`;
    const functions = formats.map(([name, width]) => {
        const type = `u${width * 8}`;
        const resultType = width === 8 ? "u64" : "u32";
        const value = width === 8 ? "read.value" : `transmute::<${type}, u32>(read.value)`;
        return `
func read_${name}(bytes: source::&[u8]) -> (u32, ${size}, ${size}, ${resultType}) {
    local read = Reader::new(bytes).read_${name}();
    (read.status.value, read.next.position(), read.next.remaining(), ${value})
}
func write_${name}(bytes: target::*[u8], value: ${type}) -> (u32, ${size}, ${size}) {
    local write = Writer::new(bytes).write_${name}(value);
    (write.status.value, write.next.position(), write.next.remaining())
}`;
    }).join("\n");
    const names = formats.flatMap(([name]) => [`read_${name}`, `write_${name}`]);
    await writeFile(join(dir, "main.wx"), `
package "binary" as binary;
use binary::{Reader, Writer};
#[memory_limits{ min_pages: 1 }]
memory source: ${size};
#[memory_limits{ min_pages: 1 }]
memory target: ${size};
${functions}
func take(bytes: source::&[u8], length: ${size}) -> (u32, ${size}, ${size}, ${size}, ${size}) {
    local read = Reader::new(bytes).take(length);
    (read.status.value, read.next.position(), read.next.remaining(), address(read.value), read.value.len())
}
func copy(src: source::&[u8], dst: target::*[u8]) -> (u32, ${size}, ${size}) {
    local write = Writer::new(dst).write_bytes(src);
    (write.status.value, write.next.position(), write.next.remaining())
}
func overlap(src: target::&[u8], dst: target::*[u8]) -> u32 {
    Writer::new(dst).write_bytes(src).status.value
}
// A failed operation must be retryable; a cursor is not sticky or consumed.
func retry_read(bytes: source::&[u8]) -> (u32, u32, ${size}, u32, ${size}) {
    local reader = Reader::new(bytes);
    local failed = reader.read_u64_be();
    local retried = failed.next.read_u8();
    (failed.status.value, retried.status.value, retried.next.position(),
        transmute::<u8, u32>(retried.value), reader.position())
}
func retry_write(bytes: target::*[u8]) -> (u32, u32, ${size}, ${size}) {
    local writer = Writer::new(bytes);
    local failed = writer.write_u64_be(0xffffffffffffffff);
    local retried = failed.next.write_u8(42);
    (failed.status.value, retried.status.value, retried.next.position(), writer.position())
}
func sequence_read(bytes: source::&[u8]) -> (u32, u32, ${size}, ${size}, u32) {
    local first = Reader::new(bytes).read_u8();
    local second = first.next.read_u32_be();
    local retry = second.next.read_u8();
    (first.status.value, second.status.value, second.next.position(),
        retry.next.position(), transmute::<u8, u32>(retry.value))
}
func sequence_write(bytes: target::*[u8]) -> (u32, u32, ${size}, ${size}) {
    local first = Writer::new(bytes).write_u8(17);
    local second = first.next.write_u32_be(0xffffffff);
    local retry = second.next.write_u8(31);
    (first.status.value, second.status.value, second.next.position(), retry.next.position())
}
func write_record(bytes: target::*[u8], value: u64) -> (u32, ${size}, ${size}) {
    local a = Writer::new(bytes).write_u8(0x57);
    local b = a.next.write_u16_be(0x1234);
    local c = b.next.write_u32_le(0x89abcdef);
    local d = c.next.write_u64_be(value);
    (d.status.value, d.next.position(), d.next.remaining())
}
func read_record(bytes: source::&[u8]) -> (u32, u32, u32, u32, u64, ${size}, ${size}) {
    local a = Reader::new(bytes).read_u8();
    local b = a.next.read_u16_be();
    local c = b.next.read_u32_le();
    local d = c.next.read_u64_be();
    (d.status.value, transmute::<u8, u32>(a.value),
        transmute::<u16, u32>(b.value), c.value, d.value,
        d.next.position(), d.next.remaining())
}
func take_to_end(bytes: source::&[u8]) -> (u32, ${size}, ${size}) {
    local all = Reader::new(bytes).take(bytes.len());
    local empty = all.next.take(0);
    (empty.status.value, address(empty.value), empty.next.remaining())
}
export { source, target, take, copy, overlap, retry_read, retry_write,
    sequence_read, sequence_write, write_record, read_record, take_to_end, ${names.join(", ")} }
`);
    const output = join(dir, "test.wasm");
    for (const command of ["check", "build"]) {
        const args = [command, dir, ...(command === "build" ? ["-o", output] : [])];
        const result = spawnSync(process.env.WX || "wx", args, { encoding: "utf8", timeout: 20000 });
        if (result.error) throw result.error;
        assert.equal(result.status, 0, result.stdout + result.stderr);
    }
    return (await WebAssembly.instantiate(await readFile(output))).instance.exports;
}

try {
    for (const bits of [32, 64]) {
        const wx = await build(bits);
        const index = value => bits === 64 ? BigInt(value) : value;
        const result = values => values.map(value => typeof value === "bigint" ? Number(value) : value >>> 0);
        const source = new Uint8Array(wx.source.buffer);
        const target = new Uint8Array(wx.target.buffer);
        const at = 37; // Deliberately unaligned.
        let seed = 0x12345678;
        const random = () => {
            seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5;
            return seed >>> 0;
        };
        for (const [name, width, little] of formats) {
            const mask = (1n << BigInt(width * 8)) - 1n;
            const values = [0n, 1n, mask, 1n << BigInt(width * 8 - 1), 0x0123456789abcdefn & mask];
            for (let i = 0; i < 40; i++) values.push((BigInt(random()) << 32n | BigInt(random())) & mask);
            for (const value of values) {
                const bytes = Uint8Array.from({ length: width }, (_, i) =>
                    Number(value >> BigInt((little ? i : width - i - 1) * 8) & 255n));
                source.set(bytes, at);
                const read = wx[`read_${name}`](index(at), index(width));
                assert.deepEqual(result(read.slice(0, 3)), [0, width, 0]);
                assert.equal(width === 8 ? BigInt.asUintN(64, read[3]) : BigInt(read[3] >>> 0), value);
                target.fill(0xcc);
                assert.deepEqual(result(wx[`write_${name}`](index(at), index(width), width === 8 ? value : Number(value))),
                    [0, width, 0]);
                assert.deepEqual(target.slice(at, at + width), bytes);
                assert(target.subarray(0, at).every(b => b === 0xcc));
                assert(target.subarray(at + width).every(b => b === 0xcc));
            }
            for (let length = 0; length < width; length++) {
                assert.deepEqual(result(wx[`read_${name}`](index(at), index(length))), [1, 0, length, 0]);
                target.fill(0xcc);
                assert.deepEqual(result(wx[`write_${name}`](index(at), index(length), width === 8 ? mask : Number(mask))),
                    [1, 0, length]);
                assert(target.every(b => b === 0xcc), "failed writes must be atomic");
            }
            // The same checks apply at Wasm memory's physical boundary.
            source.set(new Uint8Array(width).fill(255), source.length - width);
            assert.equal(wx[`read_${name}`](index(source.length - width), index(width))[0], 0);
            assert.throws(() => wx[`read_${name}`](index(source.length), index(width)), WebAssembly.RuntimeError);
            assert.throws(() => wx[`write_${name}`](index(target.length), index(width), width === 8 ? 0n : 0), WebAssembly.RuntimeError);
        }
        for (const [length, count, expected] of [
            [0, 0, [0, 0, 0, at, 0]],
            [4, 0, [0, 0, 4, at, 0]],
            [4, 4, [0, 4, 0, at, 4]],
            [4, 5, [1, 0, 4, at, 0]],
        ]) {
            assert.deepEqual(result(wx.take(index(at), index(length), index(count))), expected);
        }
        // Oversized counts cannot wrap the cursor or touch memory.
        const max = bits === 64 ? 0xffffffffffffffffn : 0xffffffff;
        assert.deepEqual(result(wx.take(index(at), index(4), max)), [1, 0, 4, at, 0]);
        assert.deepEqual(result(wx.take(index(source.length), index(0), index(0))),
            [0, 0, 0, source.length, 0]);
        assert.deepEqual(result(wx.take_to_end(index(at), index(4))), [0, at + 4, 0]);
        const wideValue = 0xfedcba9876543210n;
        target.fill(0xcc);
        assert.deepEqual(result(wx.write_record(index(at), index(17), wideValue)), [0, 15, 2]);
        const record = Uint8Array.of(0x57, 0x12, 0x34, 0xef, 0xcd, 0xab, 0x89,
            0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10);
        assert.deepEqual(target.slice(at, at + 15), record);
        assert(target.subarray(0, at).every(b => b === 0xcc));
        assert(target.subarray(at + 15).every(b => b === 0xcc));
        source.set(record, at);
        const readRecord = wx.read_record(index(at), index(17));
        assert.deepEqual(result(readRecord.slice(0, 4)), [0, 0x57, 0x1234, 0x89abcdef]);
        assert.equal(BigInt.asUintN(64, readRecord[4]), wideValue);
        assert.deepEqual(result(readRecord.slice(5)), [15, 2]);
        source.set([7, 8, 9, 10], at);
        target.fill(0xcc);
        assert.deepEqual(result(wx.copy(index(at), index(4), index(at + 1), index(4))), [0, 4, 0]);
        assert.deepEqual([...target.slice(at, at + 6)], [0xcc, 7, 8, 9, 10, 0xcc]);
        target.fill(0xcc);
        assert.deepEqual(result(wx.copy(index(at), index(4), index(at), index(3))), [1, 0, 3]);
        assert(target.every(b => b === 0xcc));
        assert.deepEqual(result(wx.copy(index(source.length), index(0), index(target.length), index(0))), [0, 0, 0]);
        for (const [from, to] of [[at, at + 1], [at + 1, at]]) {
            target.set([1, 2, 3, 4, 5], at);
            const expected = target.slice();
            expected.copyWithin(to, from, from + 4);
            assert.equal(wx.overlap(index(from), index(4), index(to), index(4)), 0);
            assert.deepEqual(target, expected);
        }
        source.set([7, 8], at);
        assert.deepEqual(result(wx.retry_read(index(at), index(1))), [1, 0, 1, 7, 0]);
        assert.deepEqual(result(wx.retry_write(index(at), index(1))), [1, 0, 1, 0]);
        assert.equal(target[at], 42);
        assert.deepEqual(result(wx.sequence_read(index(at), index(2))), [0, 1, 1, 2, 8]);
        target.fill(0xcc);
        assert.deepEqual(result(wx.sequence_write(index(at), index(2))), [0, 1, 1, 2]);
        assert.deepEqual([...target.slice(at - 1, at + 3)], [0xcc, 17, 31, 0xcc]);
        console.log(`PASS binary memory${bits}: all integer widths/endians, boundaries, atomic failures, retries, cursor chaining, zero-copy takes, cross-memory copy and overlap`);
    }
} finally {
    await rm(temporary, { recursive: true, force: true });
}
