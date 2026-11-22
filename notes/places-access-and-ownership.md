# Places, access, and ownership

How a use of a place affects the names it is written through, and where
write permission comes from today and under a future ownership model. The
first part describes the compiler's behavior; the second is a design
direction, not yet implemented.

## Two kinds of storage

- **A name's own storage.** A local, a parameter, or a field of a value
  lives in Wasm locals (one or more, once flattened). Writing it is a
  `local.set`.
- **Memory reached through a pointer.** Bytes in a linear memory, at an
  address that a pointer value holds. Writing them is a store
  (`i32.store` …) into that memory; no local changes.

## What each step of a place does

A place such as `s.pointer.value` is a sequence of steps from a name:

| Step | Wasm | Where it leads |
|---|---|---|
| field `.inner` | a sub-range of the same locals, or a constant offset in the same memory | stays in the same storage |
| element `[i]` of an array place | an offset in the same storage | stays in the same storage |
| pointer step: `p.*`, or implicitly `p.field`, `s[i]` on a pointer | `local.get` of the pointer, then the address it holds, in its memory | leaves the name's storage; the pointer is only read |
| enum repr `e.repr` | the enum's value is copied, the repr taken from the copy | leaves the enum's storage; it is only read |

## The access rule

The use (read, write, read-modify-write, address) acts on the location the
place ends at. A name in the place is accessed that way only if that
location is still inside its storage: no step between the name and the end
leaves it. A name the place leaves is only read: its value was used to go
further, and it did not change.

```wx
s.inner.value = n;    // s, inner, value: Write   (local.set on s's locals)
p.inner.value = n;    // p: Read                  (local.get $p; i32.store offset=…)
                      // inner, value: Write      (that memory changed)
s.pointer.value += n; // s, pointer: Read; value: ReadWrite
p.data[i][j] = 1;     // p, data: Read            (data[i] is a pointer read from memory)
e.repr = x;           // rejected; e, repr: Read
```

Of this rule, one consequence is used today: whether a local's own storage
changes, which is what it needs `mut` for. A local changes exactly
when an assignment to a value (`=`, `op=`) has a target whose field chain
starts at it; a write through a pointer is a `Store` into memory and only
reads the local. `p.x = 1` needs no `local mut p`. The checker requires `mut`
by that rule (`check_assignable`), and the `unnecessary_mutability` and
`unused_variable` lints read it from the checked body (`wx-lint`).

The name resolution table records what each name means, not how it is
used. The language server marks a local declared `mut` wherever it is
named, as rust-analyzer does, rather than each write.

## Permission is separate

Whether a write is allowed is not the access rule's question. Today a place
reached through a pointer is writable when that pointer is exclusive
(`Place::mutable`, `check_place_writable`), whatever the pointer was read
from:

```wx
struct Outer(inner: heap::*Inner);               // * exclusive
func f(p: heap::&Outer) { p.inner.value = 1; }   // & shared: accepted today
```

That is consistent while nothing enforces that an exclusive pointer is
unique: "exclusive" is a permission tag, not a guarantee.

## Direction: exclusive pointers that are unique

Ownership and linear types need an exclusive pointer to be the only way to
reach its memory. Then, as in Rust, everything reached through a shared
pointer is read-only, including what an exclusive pointer stored behind it
points at. This follows from uniqueness: if a shared, copyable path could
write through an exclusive pointer, every copy of that path could.

Three rules, which only work together:

1. **Writing.** A pointer step gives a writable place only if the pointer is
   exclusive and the place it is read from is writable.
2. **Loading.** Reading an exclusive pointer out of a read-only place gives
   at most a shared pointer (or is an error). Otherwise `local q = p.inner;`
   copies it into a local and writes through it, bypassing rule 1.
3. **Copying.** Exclusive pointers are not freely copied: affine (used at
   most once) or linear (exactly once), with reborrowing for temporary use.
   Otherwise two copies of one exclusive pointer exist and rules 1–2 protect
   nothing.

Rust has all three: `&mut` is not `Copy`, a `&mut` read through `&` gives a
`&`, and writing needs a unique path. Rust's ownership is affine; linear
types are stricter about consuming values, but the borrowing side is the
same.

The three are introduced together, as the start of ownership work, not rule
1 alone: on its own it is bypassed by 2 and 3, and it rejects code accepted
today (the example above), so examples are revisited then.

A borrow checker classifies uses (shared, exclusive, move) from the checked
body: deref places and their `mutable`, stores, loads, moves. It does not
read the resolution table: an exclusive use of `s.pointer` is not a write of
`s`, and recording it as one would mislead `unnecessary_mutability`.

## Interior mutability: globals

A `global mut` is already written through a shared handle: its name is a
handle value (`g.set(value)` through `GlobalMut`, never `g = …`), and anyone
who can name it can write it. That is interior mutability, and it is
compatible with uniqueness for the reason Rust's `Cell` is: no pointer can
reach its storage. A Wasm global is not in linear memory and has no address;
`global.get` and `global.set` move whole values, and there is no `g.&`. So a
write through the handle cannot invalidate anyone's pointer.

An interior-mutable type for memory would follow the same principle: values
in and out, never a pointer into it.

## Open questions

- What loading an exclusive pointer from a read-only place gives: a shared
  copy (Rust's reborrow) or an error.
- A global holding a non-copyable value (an exclusive pointer under rule 3):
  `get` would duplicate it. Restrict globals to copyable types, or make
  reading take the value and replace it (`Cell::take`/`Cell::replace`).
- Shared globals under the threads proposal need atomics, as Rust's
  thread-shared statics need `Atomic*` or a lock.
- Reinterpreting memory across memories stays possible behind the planned
  unsafe effect, outside these rules.
