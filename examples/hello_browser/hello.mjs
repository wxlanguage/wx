// Loads hello.wasm and calls its `main`. Used by index.html and by the tests.
export async function run(bytes, log) {
    const { instance } = await WebAssembly.instantiate(bytes, {
        env: {
            // A slice arrives as two numbers: an offset into the exported
            // memory and a length in bytes.
            print(offset, length) {
                const memory = new Uint8Array(instance.exports.memory.buffer);
                log(new TextDecoder().decode(memory.subarray(offset, offset + length)));
            },
        },
    });
    instance.exports.main();
}
