# utf8 — UTF-8 primitives and a borrowed string type

A standalone WX package for UTF-8 validation, decoding, encoding and safe
borrowed strings. It is generic over `M: Memory`, like `binary` and `sha256`,
so the same code reads a 32-bit or 64-bit memory.

Two layers:

- **Free functions** for byte-oriented work: `valid`, `validate`, `count`,
  `decode_at`, `previous_start`, `next_start`, `encoded_len`, `encode`.
- **`Str<M>`** for code that has already crossed the validation boundary. It is
  the `&str` analogue: a borrowed, validated UTF-8 view that owns nothing and
  is just an address and a length at runtime. `String<M>` is a type alias for
  readers who prefer that name; `utf8::string(bytes)` constructs it with the
  memory inferred.

There is deliberately no owned/growable string. That needs an allocator policy,
which the WX baseline leaves to libraries.

## Use

```wx
package "utf8" as utf8;

func describe(bytes: host::data::&[u8]) -> (Bool, u32) {
    local (valid, text) = utf8::Str::from_bytes(bytes);
    if (!valid) { return (False, 0) };
    (True, text.char_count())
}
```

`Str::from_bytes` is the validating constructor. Its methods may then assume
well-formed UTF-8:

```wx
text.as_bytes()       // the underlying M::&[u8]
text.byte_len()       // bytes, like Rust's str::len
text.char_count()     // scalar values
text.is_empty()
text.nth(index)       // (Bool, u32)
text.is_char_boundary(offset)
text.slice(start, end) // (Bool, Str<M>), byte offsets on boundaries
text.eq(other)
```

`Str::from_utf8_unchecked` is the escape hatch for literals and already-valid
data. It mirrors `str::from_utf8_unchecked` without `unsafe`; name it at the
call site only when the invariant is already established.

## Validation

`validate` stops at the first ill-formed sequence and reports its byte offset.
It rejects overlong forms, surrogates, values above U+10FFFF, bad continuation
bytes and truncated sequences. `valid` is the convenience predicate.

`count` counts non-continuation bytes. That is exact for valid UTF-8; validate
first if validity is not known.

## Encoding

```wx
local (ok, written) = utf8::encode(0x1F980, output);
```

`encode` writes one scalar value and returns `(ok, bytes written)`. It rejects
surrogates and values above U+10FFFF, and writes nothing when the destination
is too small. `encoded_len` returns 1–4, or 0 for an invalid scalar value.

## Limits

- `Str` is a borrow: the bytes must outlive it. WX does not yet enforce
  lifetimes, so the caller owns that discipline.
- `slice` takes byte offsets, not character indices.
- No grapheme clusters, normalization, case mapping or collation. Those are
  higher-level libraries, not UTF-8.

## Test

```sh
node examples/utf8/test.mjs
```

The test builds a temporary wrapper package and covers every valid width,
malformed sequences, encode/decode round trips, boundary slicing, `Str`
operations, and the same code over a 64-bit-address memory.
