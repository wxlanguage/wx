import { demoPixels, encodeQoi } from "./encode.mjs";

const canvas = document.querySelector("canvas");
const message = document.querySelector("#message");
const file = document.querySelector("input");
const sample = document.querySelector("button");
const limit = 4 * 1024 * 1024; // Pixels, not bytes: cap allocations from untrusted headers.
const encoded = new WebAssembly.Memory({ initial: 1 });
const pixels = new WebAssembly.Memory({ initial: 1 });

function grow(memory, bytes) {
    const pages = Math.ceil((bytes - memory.buffer.byteLength) / 65536);
    if (pages > 0) memory.grow(pages);
}

async function start() {
    const response = await fetch("./main.wasm");
    if (!response.ok) throw new Error("Build first: wx build examples/qoi -o examples/qoi/main.wasm");
    const { instance } = await WebAssembly.instantiate(await response.arrayBuffer(),
        { host: { encoded, pixels } });

    function show(bytes, name) {
        if (bytes.length < 14) throw new Error("File is too short for a QOI header");
        const header = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
        const width = header.getUint32(4), height = header.getUint32(8);
        if (!width || !height || width > limit / height) {
            throw new Error("Viewer limit: 4 megapixels");
        }
        // WX independently checks the entire format, header, and capacity.
        grow(encoded, bytes.length);
        grow(pixels, width * height * 4);
        new Uint8Array(encoded.buffer).set(bytes);
        const before = performance.now();
        const [status, w, h, written] = instance.exports.decode(0, bytes.length, 0, width * height);
        const elapsed = performance.now() - before;
        if (status !== 0) throw new Error(`Invalid QOI (status ${status}, ${written} pixels decoded)`);
        canvas.width = w;
        canvas.height = h;
        canvas.getContext("2d").putImageData(
            new ImageData(new Uint8ClampedArray(pixels.buffer, 0, written * 4), w, h), 0, 0);
        message.textContent = `${name} · ${w} × ${h} · ${bytes.length.toLocaleString()} bytes QOI → ${(written * 4).toLocaleString()} bytes RGBA · WX decode ${elapsed.toFixed(2)} ms`;
    }
    const report = error => { message.textContent = error.message; };
    const demo = () => {
        try { show(encodeQoi(384, 256, demoPixels()).bytes, "Generated plasma"); }
        catch (error) { report(error); }
    };
    sample.addEventListener("click", demo);
    file.addEventListener("change", async () => {
        try {
            const selected = file.files[0];
            if (!selected) return;
            if (selected.size > 32 * 1024 * 1024) throw new Error("Viewer limit: 32 MiB input");
            show(new Uint8Array(await selected.arrayBuffer()), selected.name);
        } catch (error) { report(error); }
    });
    sample.disabled = false;
    file.disabled = false;
    demo();
}

await start().catch(error => { message.textContent = error.message; });
