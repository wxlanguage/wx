# SHA-256 toolkit

SHA-256, HMAC-SHA-256, PBKDF2-HMAC-SHA-256 and constant-time comparison,
written in WX without an allocator. Every primitive reads a slice of any
memory and writes its result into a slice of any memory, including a 64-bit
one.

The package itself is a library. The exported `hash`, `hmac`, `pbkdf2` and
`bytes_eq` functions are a fixed `heap` facade for hosts that cannot name
generic functions; WX callers should use the generic API directly.

```wx
package "sha256" as sha256;

// One shot: hash a view of any memory into a view of any other.
local digest = arena.allocate_slice_uninit::<u8>(32);
sha256::sha256(data, digest);

// Streaming: the caller owns the 64-byte partial-block buffer.
local mut state = sha256::Sha256::<heap>::new(block);
loop (chunk = next_chunk()) {
    state = state.update(chunk);
};
state.finish(digest);

// HMAC and PBKDF2 compose the same pieces.
sha256::hmac_sha256(key, message, tag);
sha256::pbkdf2_sha256(password, salt, 100_000, key);
```

## Design

- **No allocator.** The one-shot entry points reserve their working area after
  the static round constants at `scratch::DATA_END` in a private memory. A
  streaming `Sha256<Buf>` instead takes a `Buf::*[u8; 64]` from its caller, so
  separate streams have separate state and the policy for where that state
  lives stays with the application.
- **Memory-generic.** `SizeExt` bridges a memory's `u32` or `u64` address type
  to the widths the algorithm counts in. The same code hashes a heap slice, a
  64-bit-memory slice, or a source and destination in different memories. The
  test suite exercises both address sizes.
- **HMAC without copies.** `hmac_parts` absorbs a key and two message parts in
  order, which is what PBKDF2 needs for `salt || INT(i)` and what a caller
  needs to authenticate a header and a body that live in different buffers.
- **Explicit failure.** The one-shot entry points assume the destination holds
  the required 32 bytes; PBKDF2 uses the destination's actual length. A zero
  iteration count traps rather than silently returning a weak key.

This is an educational example, not an audited cryptography library. It
computes the standard algorithms correctly against published vectors, but a
production deployment should also consider side channels, zeroization, and
the host's use of the results.

## Tests

```sh
node examples/sha256/test.mjs
node examples/wasi_sha256/test.mjs
```

`test.mjs` builds the package and compares it with Node's `node:crypto`:

- NIST SHA-256 vectors, every length from 0 to 260, 1 MB messages, and random
  inputs;
- RFC 4231 HMAC vectors, keys longer than the block size, and every key size
  from 0 to 140 in steps;
- RFC 7914 PBKDF2 vectors plus differential cases over iteration counts and
  output lengths;
- constant-time comparison at every byte position and with mismatched lengths;
- the same inputs hashed over a `u64`-address memory and from that memory into
  the 32-bit heap.

The command-line test builds `wx-sha256` (below), runs it under Node's WASI
runtime, and checks stdin, multiple files, paths with spaces, missing files,
and the exact `sha256sum` output format.

## Browser demo

```sh
wx build examples/sha256 -o examples/sha256/sha.wasm
python3 -m http.server -d examples/sha256
```

Open the printed address. The page hashes the message as you type, computes an
optional HMAC, and hashes a selected file. All hashing is done by the WX module.

## The command

`examples/wasi_sha256` is a `sha256sum`-shaped program built on this package.
It streams input in 64 KiB chunks, so its memory use is constant:

```sh
wx build examples/wasi_sha256 -o examples/wasi_sha256/main.wasm
printf 'abc' | node examples/wasi_sha256/run.mjs
node examples/wasi_sha256/run.mjs examples/sha256/main.wx
```
