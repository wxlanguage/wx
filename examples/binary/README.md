# Binary readers and writers

Allocation-free binary I/O over caller-owned byte slices, generic over any WX
memory. The package defines no memories, globals, imports or runtime policy.

Add a local dependency pointing at this directory:

```json
{
  "entry": "main.wx",
  "dependencies": {
    "binary": { "type": "local", "path": "../binary" }
  }
}
```

## API

`Reader::new(bytes)` accepts `M::&[u8]`; `Writer::new(bytes)` accepts
`M::*[u8]`. Both are stack values with `position()` and `remaining()`,
measured in bytes using `M::Size` (`u32` or `u64`).

| Reader | Writer |
| --- | --- |
| `read_u8()` | `write_u8(value)` |
| `read_u16_le()`, `read_u16_be()` | `write_u16_le(value)`, `write_u16_be(value)` |
| `read_u32_le()`, `read_u32_be()` | `write_u32_le(value)`, `write_u32_be(value)` |
| `read_u64_le()`, `read_u64_be()` | `write_u64_le(value)`, `write_u64_be(value)` |
| `take(length)` — zero-copy byte view | `write_bytes(bytes)` — whole-slice copy |

Reads return `Read<M, T>{ status, next, value }`; writes return
`Write<M>{ status, next }`. Match the status, then keep `next` to advance:

```wx
package "binary" as binary;

func first_word<M: Memory>(bytes: M::&[u8]) -> (binary::Status, u32) {
    local read = binary::Reader::new(bytes).read_u32_be();
    match (read.status) {
        binary::Status::Ok => (read.status, read.value),
        binary::Status::Insufficient => (read.status, 0),
    }
}

func write_word<M: Memory>(bytes: M::*[u8], value: u32) -> binary::Write<M> {
    binary::Writer::new(bytes).write_u32_be(value)
}
```

Success advances by the field width or byte count. `Insufficient` means a
truncated read or insufficient output capacity: the returned cursor is
unchanged, and failed writes touch no bytes. Failed integer reads return zero;
failed `take` returns an empty view. Check the status, not the value.
There is no sticky error: a smaller operation can succeed after a failed one.

Zero-length operations succeed, including at the end of a buffer. Integer
accesses allow unaligned addresses and specify endianness explicitly.
`write_bytes` supports different source and destination memories when their
address sizes match; overlapping copies within one memory have `memmove`
semantics via Wasm `memory.copy`.

Atomicity is **per operation**, not per sequence. If writing a record's second
field fails, the first field remains written. Preflight the total size if the
whole record must be atomic.

## Ownership and validity

Cursors borrow existing memory; they neither allocate nor extend its lifetime.
Keeping an old reader allows backtracking. Keeping an old writer allows
overwriting its old position; cursors are not unique ownership tokens and
there is no rollback of writes.

Slices must describe actual in-bounds memory regions. Forged pointers can trap;
`Insufficient` checks the slice length, not whether a host-provided slice is
real. Raw-pointer arithmetic is confined to constructing checked subviews and
copy destinations. Cursor fields are private.

The first version intentionally covers unsigned fixed-width integers and raw
bytes, not varints, floating-point numbers, text encodings, file I/O, or a
general-purpose `Result` type.

Integer reads assemble bytes directly rather than running a width-dependent
loop. Methods are marked inline, but the current compiler can retain some
cursor/result bookkeeping; allocation-free does not yet mean identical code
size to handwritten offset-based parsing.

## Validation

```sh
wx check examples/binary
node examples/binary/test.mjs
node examples/qoi/test.mjs
```

`test.mjs` generates small consumers in a temporary directory and checks/builds
them with installed `wx` (`WX` overrides the executable). It executes both
memory32 and memory64 versions against independent JavaScript byte encodings.
Tests cover all widths and endiannesses, unsigned extremes and deterministic
random values, unaligned addresses, every truncated field length, output
canaries, mixed-field records, retry/backtracking behavior, empty takes at EOF,
oversized counts, cross-memory copies, overlapping copies, and physical bounds.

QOI uses the package for its big-endian header, end marker, and bounded chunk
reader. Its output remains packed `u32` pixels rather than serializing each
RGBA byte through a writer.
