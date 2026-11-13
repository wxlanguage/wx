# Introductory memory examples

These small programs introduce the memory model before the larger applications.
They are not a memory-safety proof or a performance benchmark.

```sh
cargo build -p wx-cli
node examples/test_memory_examples.mjs
```

The runner builds into a temporary directory, executes the modules under Node,
checks their interfaces, and checks a deliberately invalid call. Use a Node
version with multi-memory support (tested with Node 24). Set `WX` to use a
different compiler binary. No generated Wasm is written into the examples.

## 1. Values without linear memory

[`memory_values/main.wx`](memory_values/main.wx) returns a `Reading` struct.
The host receives `[raw, calibrated]`: two Wasm results, not an address to an
allocated record. The runner verifies there are no imports or defined memories.
This does not mean execution needs no physical machine stack or engine storage.

## 2. Pointers and slices into host-managed bytes

[`memory_slices/main.wx`](memory_slices/main.wx) imports `host.buffer`. The
host creates a `WebAssembly.Memory`, chooses a range, writes its bytes, and calls
`sum(offset, length)` or `uppercase(offset, length)`. The imported memory is the
same object the host reads afterwards; no copy or allocator is required.

- `host::buffer::*u8` is one address, passed as an `i32`.
- `host::buffer::&[u8]` and `host::buffer::*[u8]` carry an address and element
  count, passed as two `i32` values. The memory identity is in the WX type, not
  another runtime argument.
- `dst.* = value` writes a byte; `bytes[i]` checks the slice length.
- Wasm also checks accesses against the whole memory. Neither check establishes
  who owns a range, whether its contents have a valid type, or how long it lives.

The module has no static data or initialization writes. In a larger program,
the host and guest must agree where literals, allocator metadata, and exchange
buffers live; an arbitrary offset is not automatically free space. Growing a
memory is also distinct from reserving an object inside it.

## 3. Two memories, one generic algorithm

[`two_memories/main.wx`](two_memories/main.wx) imports an exchange memory and
defines an unexported internal memory. A memory-generic `sum` reads both host
input and an internal string literal. Overwriting the entire host memory does
not change the internal string's sum. The host's `report` function accepts only
exchange-memory slices, whose raw ABI is still just `(offset, length)`.

Import blocks have their own scope. Inside this block, `io::&[u8]` names its
sibling memory. An enclosing type can be named as `super::Packet`, or brought
into scope with `use super::Packet;` (including aliases, groups and globs).
These `use` items are private by default. `pub use` re-exports accessible public
items through `host`, using the same rules as a module; a private item cannot be
made public this way. Neither form adds Wasm imports or exports. Nothing imports
the enclosing scope automatically. Outside the block the memory is named `host::io`.

The existing cycle checks still apply. Combining `use super::*` inside the
block with `use host::*` in its parent creates a rejected private glob cycle.
Use named imports in at least one direction instead.

[`two_memories/wrong_memory.wx.fail`](two_memories/wrong_memory.wx.fail) is
appended to the working source in a temporary package. The checker must reject
passing an internal-memory slice to `report`.

This prevents accidental mixing in ordinary typed calls. WX does not yet enforce
borrowing or pointer provenance, and explicit reinterpretation is an escape
hatch. The guest can deliberately copy internal bytes into exchange memory;
unexported memory is not a cryptographic confidentiality guarantee. The host
must interpret offsets against the memory agreed by the interface.
