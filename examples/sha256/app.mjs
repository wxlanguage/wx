// Host glue for the SHA-256 browser page. Kept free of DOM references so the
// same code can be exercised from Node in ../test.mjs.
//
// The package exports a fixed `heap` memory and one-shot `(pointer, length)`
// adapters. This file owns the two buffers the facade needs: input bytes and a
// key, and grows the memory as the input grows. The SHA-256 package's own
// scratch memory stays private inside the module.
const INPUT = 65536;
const KEY = 32768;
const OUTPUT = 1024;
const MAX_BYTES = 64 * 1024 * 1024;

function hex(bytes) {
    let text = "";
    for (const byte of bytes) text += byte.toString(16).padStart(2, "0");
    return text;
}

export async function createHasher(wasmBytes) {
    const { instance } = await WebAssembly.instantiate(wasmBytes, {});
    const wx = instance.exports;
    const heap = wx.memory;
    const encoder = new TextEncoder();

    function ensure(end) {
        if (end > MAX_BYTES + INPUT) throw new Error("Input is larger than 64 MiB");
        const pages = Math.ceil(end / 65536);
        const have = heap.buffer.byteLength / 65536;
        if (pages > have) heap.grow(pages - have);
    }

    function write(bytes, at) {
        ensure(at + bytes.length);
        new Uint8Array(heap.buffer).set(bytes, at);
    }

    function result(at = OUTPUT) {
        return hex(new Uint8Array(heap.buffer, at, 32));
    }

    return {
        moduleBytes: wasmBytes.byteLength,

        hash(input) {
            write(input, INPUT);
            wx.hash(INPUT, input.length, OUTPUT);
            return result();
        },

        hmac(key, message) {
            if (key.length > 4096) throw new Error("Key is limited to 4096 bytes here");
            if (message.length > MAX_BYTES) throw new Error("Input is larger than 64 MiB");
            write(key, KEY);
            write(message, INPUT);
            wx.hmac(KEY, key.length, INPUT, message.length, OUTPUT);
            return result();
        },

        text(value) {
            return encoder.encode(value);
        },
    };
}
