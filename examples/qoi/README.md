# QOI → RGBA, in WX

A complete [QOI](https://qoiformat.org/) image decoder: RGB, RGBA, INDEX,
DIFF, LUMA, and RUN chunks. A useful primitive for asset loaders, image tools,
and browser applications, without an allocator or a runtime.

```sh
wx check examples/qoi
wx build examples/qoi -o examples/qoi/main.wasm
node examples/qoi/test.mjs
python3 -m http.server 8000 --directory examples/qoi
```

Open **http://localhost:8000** in a browser with Wasm multi-memory support.
The viewer starts with a generated plasma image and accepts local `.qoi` files.
Its JavaScript encoder is independent of the WX decoder.

## Wasm boundary

Instantiate with two distinct `WebAssembly.Memory` objects:

```js
{ host: { encoded, pixels } }
```

Call `decode(inputByteOffset, inputByteLength, outputByteOffset, outputPixelCapacity)`.
The output slice contains `u32` pixels, not bytes. Pixels are packed RGBA in
little-endian memory, directly usable as browser `ImageData`.

The four results are `[status, width, height, writtenPixels]`:

| Status | Meaning |
| --- | --- |
| 0 | Success |
| 1 | Invalid or truncated QOI |
| 2 | Output capacity too small |

Header errors return zero dimensions. Later errors retain the dimensions.
Output is not transactional: an error can leave `writtenPixels` decoded pixels.
Bytes outside that prefix are untouched. A zero-length output can be used to
obtain dimensions from a valid header (status 2); this does **not** validate the
remaining file. As usual, Wasm `i32` results are signed JavaScript Numbers;
use `>>> 0` when interpreting large unsigned fields.

The caller owns buffer sizing and lifetime. Slices must designate real
in-bounds memory regions; forged pointers can trap. Bad file contents within
valid buffers return a status. The decoder checks dimensions before multiplying,
chunk lengths, run overflow, the end marker, and trailing data. It preserves
encoded channel values; it does not apply color-space conversion.

## Why this shape?

- Memory-qualified pointers separate compressed input from writable output.
  WX's types prevent mixing their addresses. Hosts must supply **distinct**
  memories; a host that aliases the imports breaks this contract.
- Slice indexing provides bounds checks; parsing adds format checks.
- A stack struct returns four Wasm values without allocating a result header.
- Immutable loop parameters carry the current `Pixel`, input position, and
  output count. Named `continue` arguments make each state transition explicit.
- Tuple and or-patterns validate headers and dispatch opcodes. Each iteration
  checks chunk size and run length, computes one next pixel, writes the run,
  then advances. Match arms contain no error exits or cursor updates.
- Malformed chunks break with a status and pixel count; the loop's result is
  assembled once. The private index table is cleared with Wasm `memory.fill`.
- Named constructors label result fields and RGBA channels; named method calls
  distinguish color deltas. Simple byte reads and unpacking stay positional.
- A `u32`-backed status enum preserves the numeric host ABI without magic
  status integers in the decoder.
- The 64-entry color cache is private, reset on every call, and never exported.
  It uses 256 bytes of a fixed one-page Wasm memory (64 KiB minimum).
- `binary::Reader` handles endian reads and bounded chunk views; the end marker
  is excluded from the chunk reader so truncated chunks cannot consume it.
- No mutable globals, growing heap, or host function imports.
  Each instance processes calls synchronously; there are no reentrant callbacks.

`test.mjs` builds a temporary Wasm module using installed `wx` (`WX` overrides
the executable), then runs known opcode vectors and deterministic differential
round trips, checks every opcode byte and all 65,536 combinations of the two
header metadata bytes, malformed inputs, output canaries, repeated calls, and
forged-buffer traps. No generated binaries are checked in.
