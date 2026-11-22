// Tests for the WX UTF-8 package.
//
//   node examples/utf8/test.mjs
//
// A package has no exports by itself, so the test builds a tiny wrapper
// package in a temporary directory. The wrapper imports `utf8`, exports the
// operations a host can call, and is the same shape any application uses.

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { cp, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../../", import.meta.url));
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-utf8-"));
const library = join(temporary, "utf8");
const app = join(temporary, "app");
const wasmPath = join(temporary, "utf8.wasm");

const DATA = 65536;
const OUT = 65536;

const wrapper = `package "utf8" as utf8;

import "host" as host {
    memory data: u32;
}

#[memory_limits{ min_pages: 1 }]
memory wide: u64;

func valid(bytes: host::data::&[u8]) -> Bool {
    utf8::valid(bytes)
}

func validate(bytes: host::data::&[u8]) -> (Bool, u32) {
    local verdict = utf8::validate(bytes);
    (verdict.valid, verdict.invalid_at)
}

func count(bytes: host::data::&[u8]) -> u32 {
    utf8::count(bytes)
}

func decode(bytes: host::data::&[u8], at: u32) -> (u32, u32) {
    utf8::decode_at(bytes, at)
}

func previous(bytes: host::data::&[u8], at: u32) -> u32 {
    utf8::previous_start(bytes, at)
}

func encoded_len(value: u32) -> u32 {
    utf8::encoded_len(value)
}

func encode(value: u32, dst: host::data::*[u8]) -> (Bool, u32) {
    local (ok, length) = utf8::encode(value, dst);
    (ok, length)
}

func string_info(bytes: host::data::&[u8]) -> (Bool, u32, u32) {
    local (ok, text) = utf8::Str::from_bytes(bytes);
    (ok, text.byte_len(), text.char_count())
}

func nth(bytes: host::data::&[u8], index: u32) -> (Bool, u32) {
    local (ok, text) = utf8::Str::from_bytes(bytes);
    if (!ok) { return (False, 0) };
    text.nth(index)
}

func slice_info(bytes: host::data::&[u8], start: u32, end: u32) -> (Bool, u32, u32) {
    local (ok, text) = utf8::Str::from_bytes(bytes);
    if (!ok) { return (False, 0, 0) };
    local (sliced_ok, part) = text.slice(start, end);
    (sliced_ok, part.byte_len(), part.char_count())
}

func eq_str(a: host::data::&[u8], b: host::data::&[u8]) -> Bool {
    local (ok_a, left) = utf8::Str::from_bytes(a);
    local (ok_b, right) = utf8::Str::from_bytes(b);
    if (!ok_a || !ok_b) { return False };
    left.eq(right)
}

func alias_check(bytes: host::data::&[u8]) -> u32 {
    local (ok, text) = utf8::string(bytes);
    if (!ok) { return 0 };
    text.char_count()
}

func valid_wide(bytes: wide::&[u8]) -> Bool {
    utf8::valid(bytes)
}

func count_wide(bytes: wide::&[u8]) -> u64 {
    utf8::count(bytes)
}

func info_wide(bytes: wide::&[u8]) -> (Bool, u64, u64) {
    local (ok, text) = utf8::Str::from_bytes(bytes);
    (ok, text.byte_len(), text.char_count())
}

func encode_wide(value: u32, dst: wide::*[u8]) -> (Bool, u64) {
    utf8::encode(value, dst)
}

export {
    valid,
    validate,
    count,
    decode,
    previous,
    encoded_len,
    encode,
    string_info,
    nth,
    slice_info,
    eq_str,
    alias_check,
    valid_wide,
    count_wide,
    info_wide,
    encode_wide,
    wide as "wide_memory",
}
`;

try {
    await cp(join(root, "examples/utf8"), library, { recursive: true });
    await cp(join(root, "examples/utf8/wx.json"), join(library, "wx.json"));
    await mkdir(app, { recursive: true });
    await writeFile(join(app, "main.wx"), wrapper);
    await writeFile(
        join(app, "wx.json"),
        JSON.stringify({
            entry: "main.wx",
            dependencies: { utf8: { type: "local", path: "../utf8" } },
        }),
    );

    const built = spawnSync(process.env.WX || "wx", [
        "build",
        app,
        "-o",
        wasmPath,
    ], { cwd: root, encoding: "utf8", timeout: 60000 });
    if (built.error) throw built.error;
    assert.equal(built.status, 0, built.stdout + built.stderr);

    const module = await WebAssembly.compile(await readFile(wasmPath));
    const memory = new WebAssembly.Memory({ initial: 2 });
    const { exports: wx } = await WebAssembly.instantiate(module, {
        host: { data: memory },
    });

    const bytes = () => new Uint8Array(memory.buffer);
    const encoder = new TextEncoder();

    function write(bytesLike, at = 0) {
        bytes().set(bytesLike, at);
    }

    function read(at, length) {
        return Uint8Array.from(new Uint8Array(memory.buffer, at, length));
    }

    function runString(op, text, ...rest) {
        const input = typeof text === "string" ? encoder.encode(text) : text;
        write(input, 0);
        return wx[op](0, input.length, ...rest);
    }

    function runTwoStrings(op, a, b) {
        const left = encoder.encode(a);
        const right = encoder.encode(b);
        write(left, 0);
        write(right, 100);
        return wx[op](0, left.length, 100, right.length);
    }

    // ── validation ──────────────────────────────────────────────────────────
    for (const text of ["", "abc", "λ", "€", "🦀", "aλ€🦀", "\u{10FFFF}"]) {
        assert.equal(runString("valid", text), 1, `valid ${JSON.stringify(text)}`);
        const [ok, at] = runString("validate", text);
        assert.equal(ok, 1);
        assert.equal(at, encoder.encode(text).length);
        assert.equal(runString("count", text), [...text].length);
    }

    for (const [name, invalid] of [
        ["overlong NUL", [0xc0, 0x80]],
        ["overlong slash", [0xe0, 0x80, 0xaf]],
        ["surrogate", [0xed, 0xa0, 0x80]],
        ["above U+10FFFF", [0xf4, 0x90, 0x80, 0x80]],
        ["truncated 2-byte", [0xc2]],
        ["truncated 3-byte", [0xe2, 0x82]],
        ["truncated 4-byte", [0xf0, 0x9f, 0x98]],
        ["stray continuation", [0x80]],
        ["bad continuation", [0xe2, 0x28, 0xa1]],
        ["five-byte form", [0xf8, 0x88, 0x80, 0x80, 0x80]],
        ["C1 control lead", [0xc1, 0xbf]],
    ]) {
        assert.equal(runString("valid", invalid), 0, name);
        assert.equal(runString("count", invalid) >= 0, true, name);
        const [ok, at] = runString("validate", invalid);
        assert.equal(ok, 0, name);
        assert.ok(at < invalid.length, `${name} reports an offset`);
    }

    // ── decoding and boundaries ─────────────────────────────────────────────
    for (const [text, expected] of [
        ["A", [[0x41, 1]]],
        ["é", [[0xe9, 2]]],
        ["€", [[0x20ac, 3]]],
        ["🦀", [[0x1f980, 4]]],
        ["aλ€🦀", [[0x61, 1], [0x3bb, 2], [0x20ac, 3], [0x1f980, 4]]],
    ]) {
        const encoded = encoder.encode(text);
        write(encoded, 0);
        let at = 0;
        for (const [value, width] of expected) {
            assert.deepEqual(wx.decode(0, encoded.length, at), [value, width]);
            at += width;
        }
        assert.deepEqual(wx.previous(0, encoded.length, encoded.length), at - expected.at(-1)[1]);

        // previous_start at every boundary, and only at boundaries.
        let boundary = 0;
        for (const [, width] of expected) {
            assert.equal(wx.previous(0, encoded.length, boundary + width), boundary);
            boundary += width;
        }
        for (let i = 1; i < encoded.length; i++) {
            if ((encoded[i] & 0xc0) === 0x80) {
                // An interior offset is not a boundary; `previous_start`
                // still finds the start of the containing scalar.
                const start = wx.previous(0, encoded.length, i);
                assert.equal((encoded[start] & 0xc0) === 0x80, false);
            }
        }
    }

    // ── encoding ────────────────────────────────────────────────────────────
    for (const [value, expected] of [
        [0, [0x00]],
        [0x41, [0x41]],
        [0x7f, [0x7f]],
        [0x80, [0xc2, 0x80]],
        [0xe9, [0xc3, 0xa9]],
        [0x7ff, [0xdf, 0xbf]],
        [0x800, [0xe0, 0xa0, 0x80]],
        [0x20ac, [0xe2, 0x82, 0xac]],
        [0xffff, [0xef, 0xbf, 0xbf]],
        [0x10000, [0xf0, 0x90, 0x80, 0x80]],
        [0x1f980, [0xf0, 0x9f, 0xa6, 0x80]],
        [0x10ffff, [0xf4, 0x8f, 0xbf, 0xbf]],
    ]) {
        assert.equal(wx.encoded_len(value), expected.length);
        bytes().fill(0x5a, OUT, OUT + 8);
        const [ok, length] = wx.encode(value, OUT, 8);
        assert.equal(ok, 1);
        assert.equal(length, expected.length);
        assert.deepEqual([...read(OUT, length)], expected);
        assert.equal(bytes()[OUT + length], 0x5a, "no write past the value");
        assert.equal(runString("valid", read(OUT, length)), 1);
    }

    for (const value of [0xd800, 0xdfff, 0x110000, 0xffffffff]) {
        assert.equal(wx.encoded_len(value), 0);
        const [ok, length] = wx.encode(value, OUT, 8);
        assert.equal(ok, 0);
        assert.equal(length, 0);
    }
    // Too small: write nothing, report no length.
    for (const capacity of [0, 1, 2, 3]) {
        bytes().fill(0x5a, OUT, OUT + 8);
        const [ok, length] = wx.encode(0x1f980, OUT, capacity);
        assert.equal(ok, 0);
        assert.equal(length, 0);
        assert.deepEqual([...read(OUT, 8)], Array(8).fill(0x5a));
    }

    // ── Str: the borrowed UTF-8 string ──────────────────────────────────────
    assert.deepEqual(runString("string_info", "aλ€🦀"), [1, 10, 4]);
    assert.deepEqual(runString("string_info", [0xff]), [0, 0, 0]);
    assert.equal(runString("alias_check", "hé🦀"), 3);

    for (const [text, expected] of [
        ["aλ€🦀", [0x61, 0x3bb, 0x20ac, 0x1f980]],
    ]) {
        for (let i = 0; i < expected.length; i++) {
            assert.deepEqual(runString("nth", text, i), [1, expected[i]]);
        }
        assert.deepEqual(runString("nth", text, expected.length), [0, 0]);
    }

    const sliced = "hé🦀";
    assert.deepEqual(runString("slice_info", sliced, 0, 3), [1, 3, 2]);
    assert.deepEqual(runString("slice_info", sliced, 3, 7), [1, 4, 1]);
    assert.deepEqual(runString("slice_info", sliced, 0, 0), [1, 0, 0]);
    assert.deepEqual(runString("slice_info", sliced, 7, 7), [1, 0, 0]);
    assert.deepEqual(runString("slice_info", sliced, 1, 3), [1, 2, 1]);
    // Offsets inside a scalar, reversed ranges, and out-of-range ends fail.
    for (const [start, end] of [[1, 2], [2, 3], [3, 6], [2, 1], [0, 8], [8, 8]]) {
        assert.deepEqual(runString("slice_info", sliced, start, end), [0, 0, 0]);
    }

    assert.equal(runTwoStrings("eq_str", "hello", "hello"), 1);
    assert.equal(runTwoStrings("eq_str", "hello", "hellO"), 0);
    assert.equal(runTwoStrings("eq_str", "", ""), 1);

    // ── a 64-bit-address memory ────────────────────────────────────────────
    {
        const text = "aλ€🦀";
        const encoded = encoder.encode(text);
        new Uint8Array(wx.wide_memory.buffer, 0, encoded.length).set(encoded);
        assert.equal(wx.valid_wide(0n, BigInt(encoded.length)), 1);
        assert.equal(wx.count_wide(0n, BigInt(encoded.length)), BigInt([...text].length));
        assert.deepEqual(
            wx.info_wide(0n, BigInt(encoded.length)),
            [1, BigInt(encoded.length), BigInt([...text].length)],
        );
        const [ok, written] = wx.encode_wide(0x1f980, 100n, 8n);
        assert.equal(ok, 1);
        assert.equal(written, 4n);
        assert.deepEqual(
            [...new Uint8Array(wx.wide_memory.buffer, 100, 4)],
            [0xf0, 0x9f, 0xa6, 0x80],
        );
    }

    console.log("utf8: all tests passed");
} finally {
    await rm(temporary, { recursive: true, force: true });
}
