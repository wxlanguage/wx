// node examples/qoi/test.mjs (WX may select a different compiler executable)
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { demoPixels, encodeQoi } from "./encode.mjs";

const root = fileURLToPath(new URL("../../", import.meta.url));
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-qoi-"));
try {
    const output = join(temporary, "qoi.wasm");
    const built = spawnSync(process.env.WX || "wx",
        ["build", join(root, "examples/qoi"), "-o", output],
        { cwd: root, encoding: "utf8", timeout: 20000 });
    if (built.error) throw built.error;
    assert.equal(built.status, 0, built.stdout + built.stderr);
    const module = await WebAssembly.compile(await readFile(output));
    const encoded = new WebAssembly.Memory({ initial: 16 });
    const pixels = new WebAssembly.Memory({ initial: 16 });
    const { exports: wx } = await WebAssembly.instantiate(module, { host: { encoded, pixels } });
    assert.deepEqual(WebAssembly.Module.exports(module), [{ name: "decode", kind: "function" }]);
    assert.deepEqual(WebAssembly.Module.imports(module), [
        { module: "host", name: "encoded", kind: "memory" },
        { module: "host", name: "pixels", kind: "memory" },
    ]);
    const source = new Uint8Array(encoded.buffer);
    const destination = new Uint8Array(pixels.buffer);
    const start = 64;
    const operations = new Set();
    let cases = 0;
    function roundtrip(width, height, input, channels = 4, colorspace = 0) {
        const packed = encodeQoi(width, height, input, channels, colorspace);
        for (const op of packed.operations) operations.add(op);
        source.fill(0xcc);
        source.set(packed.bytes, start);
        destination.fill(0xcc);
        assert.deepEqual(wx.decode(start, packed.bytes.length, start, width * height),
            [0, width, height, width * height]);
        assert.deepEqual(destination.slice(start, start + input.length), input);
        assert(destination.subarray(0, start).every(b => b === 0xcc));
        assert(destination.subarray(start + input.length).every(b => b === 0xcc));
        assert.deepEqual(source.slice(start, start + packed.bytes.length), packed.bytes);
        cases++;
        return packed.bytes;
    }
    // Known opcode sequences as well as encoder-produced files: avoid having
    // the encoder and decoder accidentally agree on the same wrong convention.
    const header = [113, 111, 105, 102, 0, 0, 0, 1, 0, 0, 0, 1, 4, 0];
    const marker = [0, 0, 0, 0, 0, 0, 0, 1];
    for (const [ops, expected] of [
        [[0xc0], [0, 0, 0, 255]],
        [[0x00], [0, 0, 0, 0]], // initial index table is transparent black
        [[0x40], [254, 254, 254, 255]], // DIFF wraps each channel
        [[0x80, 0x00], [216, 224, 216, 255]], // minimum LUMA deltas
        [[0xfe, 1, 2, 3], [1, 2, 3, 255]],
        [[0xff, 1, 2, 3, 4], [1, 2, 3, 4]],
    ]) {
        const data = Uint8Array.from([...header, ...ops, ...marker]);
        source.set(data, start);
        assert.deepEqual(wx.decode(start, data.length, start, 1), [0, 1, 1, 1]);
        assert.deepEqual([...destination.slice(start, start + 4)], expected);
    }
    // Exercise every opcode against the tuple/or-pattern dispatch, especially
    // RGB/RGBA taking precedence over the RUN tag they share.
    for (let op = 0; op < 256; op++) {
        const count = op >= 0xc0 && op < 0xfe ? (op & 63) + 1 : 1;
        const h = [...header]; h[7] = count;
        const extra = op === 0xfe ? [17, 31, 63]
            : op === 0xff ? [17, 31, 63, 127] : op >> 6 === 2 ? [0x97] : [];
        const data = Uint8Array.from([...h, op, ...extra, ...marker]);
        const expected = op === 0xfe ? [17, 31, 63, 255]
            : op === 0xff ? [17, 31, 63, 127]
            : op < 0x40 ? [0, 0, 0, 0]
            : op < 0x80 ? [((op >> 4 & 3) - 2) & 255, ((op >> 2 & 3) - 2) & 255, ((op & 3) - 2) & 255, 255]
            : op < 0xc0 ? [((op & 63) - 31) & 255, ((op & 63) - 32) & 255, ((op & 63) - 33) & 255, 255]
            : [0, 0, 0, 255];
        source.set(data, start);
        assert.deepEqual(wx.decode(start, data.length, start, count), [0, count, 1, count], `opcode ${op}`);
        for (let i = 0; i < count; i++) {
            assert.deepEqual([...destination.slice(start + i * 4, start + i * 4 + 4)], expected, `opcode ${op}, pixel ${i}`);
        }
    }
    // Exhaust the byte-sized header fields: nested or-patterns must accept
    // exactly channels 3/4 and colorspace 0/1, not just their boundary cases.
    const black = Uint8Array.from([...header, 0xc0, ...marker]);
    source.set(black, start);
    for (let channels = 0; channels < 256; channels++) {
        for (let colorspace = 0; colorspace < 256; colorspace++) {
            source[start + 12] = channels;
            source[start + 13] = colorspace;
            const valid = (channels === 3 || channels === 4) && colorspace <= 1;
            assert.deepEqual(wx.decode(start, black.length, start, 1),
                valid ? [0, 1, 1, 1] : [1, 0, 0, 0], `header ${channels}/${colorspace}`);
        }
    }
    roundtrip(1, 1, Uint8Array.of(0, 0, 0, 255), 3, 1);
    roundtrip(130, 1, Uint8Array.from({ length: 520 }, (_, i) => i % 4 === 3 ? 255 : 0));
    roundtrip(7, 1, Uint8Array.from([
        100, 50, 20, 255, 101, 50, 19, 255, 110, 60, 30, 255,
        100, 50, 20, 255, 100, 50, 20, 0, 100, 50, 20, 0, 0, 0, 0, 0,
    ]));
    roundtrip(384, 256, demoPixels());
    let seed = 0x12345678;
    const random = () => {
        seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5;
        return seed >>> 0;
    };
    for (let test = 0; test < 200; test++) {
        const width = 1 + random() % 80, height = 1 + random() % 40;
        const input = new Uint8Array(width * height * 4);
        for (let i = 0; i < input.length; i += 4) {
            if (i && random() % 3 === 0) input.set(input.subarray(i - 4, i), i);
            else for (let c = 0; c < 4; c++) input[i + c] = random() & 255;
        }
        roundtrip(width, height, input);
    }
    assert.deepEqual([...operations].sort(), ["DIFF", "INDEX", "LUMA", "RGB", "RGBA", "RUN"]);

    function reject(data, capacity, expected) {
        source.set(data, start);
        destination.fill(0xcc);
        // Wasm i32 results cross the JS boundary as signed Numbers, even when
        // the WX source type is u32.
        const result = wx.decode(start, data.length, start, capacity).map(n => n >>> 0);
        assert.deepEqual(result, expected);
        assert(destination.subarray(0, start).every(b => b === 0xcc));
        assert(destination.subarray(start + result[3] * 4).every(b => b === 0xcc));
    }
    const valid = Uint8Array.from([...header, 0xff, 1, 2, 3, 4, ...marker]);
    for (let length = 0; length < valid.length; length++) {
        reject(valid.slice(0, length), 1, [1, 0, 0, 0].map((v, i) =>
            length >= 22 && (i === 1 || i === 2) ? 1 : v));
    }
    for (const [offset, value] of [[0, 0], [12, 2], [13, 2], [7, 0], [11, 0]]) {
        const bad = valid.slice(); bad[offset] = value;
        reject(bad, 1, [1, 0, 0, 0]);
    }
    reject(valid, 0, [2, 1, 1, 0]);
    const huge = valid.slice(); huge.fill(255, 4, 12);
    reject(huge, 1, [2, 0xffffffff, 0xffffffff, 0]);
    const badMarker = valid.slice(); badMarker[badMarker.length - 1] = 0;
    reject(badMarker, 1, [1, 1, 1, 0]);
    for (let i = 0; i < 8; i++) {
        const bad = valid.slice(); bad[bad.length - 8 + i] ^= 1;
        reject(bad, 1, [1, 1, 1, 0]);
    }
    for (const op of [[], [0xc1], [0xfe, 1, 2], [0xff, 1, 2, 3], [0x80]]) {
        reject(Uint8Array.from([...header, ...op, ...marker]), 1, [1, 1, 1, 0]);
    }
    reject(Uint8Array.from([...header, 0xc0, 0xc0, ...marker]), 1, [1, 1, 1, 1]);
    const two = [...header]; two[7] = 2;
    reject(Uint8Array.from([...two, 0xc0, 0xff, ...marker]), 2, [1, 2, 1, 1]);

    // Decode again after failures: no index-table state may leak between calls.
    roundtrip(1, 1, Uint8Array.of(0, 0, 0, 0));
    assert.throws(() => wx.decode(source.length, 22, start, 1), WebAssembly.RuntimeError);
    source.set(valid, start);
    assert.throws(() => wx.decode(start, valid.length, destination.length, 1), WebAssembly.RuntimeError);

    // Smoke-test browser glue with the real Wasm and a minimal DOM/canvas shim.
    // This checks memory growth, ImageData bytes, file loading and UI errors,
    // but is not a visual browser rendering test.
    const saved = { document: globalThis.document, fetch: globalThis.fetch, ImageData: globalThis.ImageData };
    const elements = Object.fromEntries(["canvas", "#message", "input", "button"].map(selector =>
        [selector, { disabled: true, listeners: {}, addEventListener(name, callback) { this.listeners[name] = callback; } }]));
    let displayed;
    elements.canvas.getContext = () => ({ putImageData(image) { displayed = image; } });
    try {
        globalThis.document = { querySelector: selector => elements[selector] };
        globalThis.fetch = async () => ({ ok: true, arrayBuffer: async () => readFile(output) });
        globalThis.ImageData = class {
            constructor(bytes, width, height) {
                this.data = bytes.slice(); this.width = width; this.height = height;
            }
        };
        await import("./viewer.mjs");
        assert.equal(elements.button.disabled, false);
        assert.equal(elements.input.disabled, false);
        assert.equal(displayed.width, 384);
        assert.equal(displayed.height, 256);
        assert.deepEqual(new Uint8Array(displayed.data), demoPixels());
        const upload = async bytes => {
            elements.input.files = [{ name: "test.qoi", size: bytes.length, arrayBuffer: async () => bytes.buffer }];
            await elements.input.listeners.change();
        };
        await upload(valid);
        assert.deepEqual([...displayed.data], [1, 2, 3, 4]);
        await upload(badMarker);
        assert.match(elements["#message"].textContent, /Invalid QOI/);
        await upload(huge);
        assert.match(elements["#message"].textContent, /4 megapixels/);
        elements.button.listeners.click();
        assert.match(elements["#message"].textContent, /Generated plasma/);
    } finally {
        for (const [name, value] of Object.entries(saved)) {
            if (value === undefined) delete globalThis[name];
            else globalThis[name] = value;
        }
    }
    console.log(`PASS QOI: ${cases} round trips, all 6 opcodes, known vectors, malformed files, bounds and repeat calls`);
    console.log("PASS patterns: all 256 opcode bytes and 65,536 channels/colorspace combinations");
    console.log("PASS viewer: generated image, memory growth, file upload and error reporting (DOM shim)");
    console.log(`Decoder: ${(await readFile(output)).length} Wasm bytes; no allocator, no host function imports`);
} finally {
    await rm(temporary, { recursive: true, force: true });
}
