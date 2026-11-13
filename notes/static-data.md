# Static data, indexing and slice built-ins (lowering checkpoint)

Status: planned 2026-11-04, branch `tir-translation`. Follows the memory
checkpoint in `notes/tir-to-mir-transition-spec.md`; the type-level design
(literals are arrays, placement, `StackValue`) is
`notes/slices-and-untyped-constants.md`.

## Goal

String and array literals, constants and globals holding addresses,
`Memory::DATA_END`, indexing (`s[i]`) and the bodiless `Slice`/`Array`
methods lower to Wasm that runs. Everything that is static data is a
constant expression, checked by `wx check`, evaluated once by the
constant evaluator, and emitted as bytes in a data segment.

## What exists

| Piece | Where | State |
| --- | --- | --- |
| Literal → allocation | `eval.rs` `place_data`, `eval_static`, `place_static` | Works; relocations, per-memory placement |
| `Allocation { memory, align, bytes, relocations }` | `eval.rs`, in `Solver::allocations` | Relocations hold the target's in-allocation offset in place |
| Placed literals of a body | `Body::statics`, inner before outer | Recorded, nothing reads them |
| `StaticEntry`, `ExprKind::StaticPointer` | `mir/mod.rs`, `mir/body.rs` | No relocations |
| Segment layout | `codegen::Builder::build` | Live entries from function bodies only, align-sorted, one segment per memory at offset 0 |
| End of static data | MIR `ExprKind::MemoryOffset { memory }` → `DataSectionEnd` | Wired in opt and codegen, never produced |

Problems found by probing the CLI (2026-11-04):

- `func f(x: u8) -> heap::&[u8] { [x, 1] }` passes `wx check`: elements are
  built by the ordinary checker, which sees the function's locals, and no
  pass evaluates a function's literals.
- `heap::DATA_END` in a function panics the CLI (lowering fails without a
  diagnostic): a memory's synthetic `Memory` impl has no member for it.
- `global mut bump: heap::*u8 = heap::DATA_END` panics ("a checked global
  without errors has a value"): the evaluator has no value for it.
- `global s: heap::&[u8; 2] = "hi"` is "a global holding an address".
- `"hi"`, `[1, 2]`, `[0; 4]` in a function are "this expression".
- `Memory::INDEX` is named only in `lower.rs`'s header comment; std does not
  declare it. MIR's `MemoryIndex` node serves the intrinsics. Dropped.

## Design

### Static data is a constant context

A literal's elements (and a repeat's count) see what a constant's body
sees: items, constants and the function's type parameters, nothing of its
runtime. It is a mode of the same `BodyContext`, not a separate builder:
an element's type is decided by the literal's context after it is built
(`coerce_static`, possibly after a call infers its arguments), elements may
name the function's generics (`[T::SIZE]`), and the evaluator reads the
literal from the body it is in. Rust's precedent: a local named in a
constant context is a name-resolution error (E0435).

Two layers, each the single owner of its question:

1. **Names.** A literal's elements (and a repeat's value) are built in a
   scope of their own, `ScopeKind::Static`. The scope stays connected: a
   name still finds a local around it, so a local shadows an item as
   anywhere, and `lookup_local` says it lies past the static scope, which
   `build_path` reports (E2140 `LocalInStaticData`, "a local variable cannot
   be used in static data"). Disconnecting the scope was rejected: the name
   would silently fall through to an item of the same name. A repeat's count
   is a length, held to a literal or a constant by `repeat_length` (E2044).
   `return`, `break` and `continue` get no rule of their own: the evaluator
   reports them as not constant.
2. **Forms.** The evaluator decides what is a constant expression, as it
   does for constants. Each piece of a function's static data (a literal,
   or a constant holding data, placed) is a memoized solver query per
   function instance, `TypeContext::static_value` (`StaticInstance`, in
   `Solver::static_values`), whose failure its first reader reports; a
   nested literal goes through the same query, so it is evaluated and
   reported once. `check_function_body` asks for every piece of a function
   with no parameters, so `wx check` reports them; lowering asks for each
   instance's before it takes the body (the evaluator reads the body).
   A generic function's static data is evaluated only per instance, so a
   non-constant form in it is reported by `wx build`, not `wx check` (see
   Open).

No runtime arrays: wx has no stack allocation to hold them.

### Data flow

```
literal / constant / global initializer
   │ eval.rs: place_data → Allocation (Solver::allocations), Val::MemoryOffset
   ▼
lowering: AllocIdx → StaticEntry (memoized, transitive over relocations,
          deduplicated by content per memory)
   ▼
MIR: StaticEntry { bytes, align, memory, relocations }
     ExprKind::StaticPointer { entry, offset }, ConstInit::Static, DataEnd
   ▼
codegen: live entries (function bodies + global initializers, closed over
         relocations) → per-memory layout → relocations patched → segments
```

- **One representation per stage.** The evaluator owns allocations; MIR
  owns entries; codegen owns addresses. No stage stores another's numbers.
- **Relocation:** `(offset_in_entry, target_entry)`. The bytes at the
  offset hold the offset into the target (the allocation's convention),
  and codegen adds the target's address. Its width is the pointer's
  memory's (the target's `MemoryKind`), which may differ from the memory
  holding it.
- **Layout stays in codegen**, after inlining has dropped functions: dead
  data takes no space and `DATA_END` is tight.
- **Deduplication:** identical entries (memory, align, bytes, relocations
  after mapping) share one. Data is reached through shared pointers.
- **Addresses start at 0** in each memory, as today. Reserving low memory
  (for null or niches) is a later decision.
- **`DATA_END`** is late-bound: `ResolvedConstant::DataEnd(memory)` from a
  memory's synthetic impl (as `Array::LEN` is answered from the type),
  `Val::DataEnd { memory }` in evaluation, `ExprKind::DataEnd` (renamed
  from `MemoryOffset`) in MIR, `ConstInit::DataEnd` for globals; codegen
  emits the segment end rounded up to 16.

### Indexing

`PlaceKind::Element { object, index }`: the pointer is evaluated once, then
`if index >= len { unreachable }` (one unsigned compare, always on: no
build profiles yet), and the address is `base + index * stride`; later
field steps stay constant offsets. `len` is the array's length (a constant)
or the slice's metadata. Element layout from TIR; arrays of arrays wait
for `Sized`.

### Built-in methods

`ResolvedFunction::Builtin` expands, never a call:

| Method | Array `M::&[T; N]` | Slice `M::&[T]` |
| --- | --- | --- |
| `len` | `N` | the count |
| `as_ref` | the address | the address |
| `as_slice` / `as_slice_mut` | `(address, N)` | — |

Only `len` and `as_ref` are supplied; `as_slice`, `as_slice_mut`, `first`
and `last` have bodies in std and lower as generic functions.

## Plan

Each slice ends with execution tests (inlining off and on) and a CLI run.

- **A. Allocations to MIR.** Done (2026-11-04): `lower/statics.rs`
  (`StaticData`, content-interned with a `HashTable` over ids, memoized per
  allocation), `StaticEntryId`, `Relocation`, `StaticPointer { entry,
  offset }`, `ConstInit::Static`, `lay_out_static_data` in codegen
  (deterministic order). A pointer with metadata lowers as a MIR aggregate
  of the address (`ValueType::Pointer`) and its metadata. Tests in
  `tir/lower.rs` (constant slice, global, slice of slices in 32- and 64-bit
  memories, deduplication). Planned was: `StaticEntry.relocations`; the `AllocIdx` →
  entry map in lowering; `Val::MemoryOffset` materialized as
  `StaticPointer`; `ConstInit::Static`; codegen liveness from globals and
  relocations, patching. Tests: `const S: heap::&[u8] = "hi"`, a global
  string, a slice of slices, data in a 64-bit memory.
- **B. Literals in function bodies.** Done (2026-11-04), as described under
  "Static data is a constant context". Tests: `typecheck.rs`
  (`a_local_cannot_be_used_in_static_data`,
  `static_data_is_evaluated_when_its_function_is_checked`), `lower.rs`
  (literals, repeats, placed constants, nested data, a generic memory, a
  generic instance's failure). Planned was: the constant context in the checker;
  `check_bodies` evaluates statics; `Evaluated::Function` owner with the
  instance's arguments; lowering of `String`/`Array`/`ArrayRepeat` and
  placed constants, memoized per (instance, literal). Tests: the
  diagnostics, generic memory, generic element constant.
- **C. `DATA_END`.** Done (2026-11-04). `IntrinsicDefs::memory_data_end`
  recognized with `Memory`; `resolve_constant` answers it for a declared
  memory's synthetic impl as `ResolvedConstant::DataEnd`; the evaluator's
  `Val::DataEnd { memory }` is late-bound, and an address written in data
  points at an `AddressTarget` (an allocation, or a memory's data end), in
  the evaluator and in MIR (`mir::AddressTarget`, `ConstInit::DataEnd`,
  `ExprKind::DataEnd`, renamed from `MemoryOffset`; opt's
  `DataNodeKind::DataEnd`, Wasm's `Instruction::DataEnd`). Codegen's
  `StaticLayout` owns the segments, the entry addresses and
  `data_end` (the segment's size rounded up to 16, also the minimum pages),
  and resolves both kinds of target. Both CLI panics are gone. Tests:
  `eval.rs` `data_end_is_a_late_bound_address`, `lower.rs`
  `data_end_is_the_address_after_the_static_data` (32 and 64 bits, in a
  function, a global, written in data, a memory with no data).
- **D. Indexing.** Done (2026-11-04). `places.rs` `lower_element`: the
  pointer, then the index, each into a temporary; `if index >= len {
  unreachable }` (unsigned; `len` the slice's metadata or the array's
  type's); the address `base + transmute(index * stride)`, the stride the
  element's TIR layout size; later fields stay constant offsets, so load,
  store, compound store and `.&` need nothing more. Found on the way: the
  encoder wrote a `memarg` for a memory other than 0 in the wrong order and
  without the multi-memory flag (`codegen::encode_memarg`), so every
  access to a second memory was invalid. Tests in `lower.rs`:
  `an_element_is_read_within_its_length` (slice, array, a field after it,
  `.&`, traps), `an_element_is_written_through_an_exclusive_pointer`
  (evaluation order, compound store, a slice made from parts),
  `an_element_of_a_wide_memory_is_indexed_in_64_bits`,
  `a_slice_parameter_is_indexed_against_its_length` (replaces the
  "unsupported" test).
- **E. Built-in methods.** Done (2026-11-04). `IntrinsicDefs::slice_len`
  and `slice_as_ref`, and `IntrinsicDefs::supplies`, which
  `resolve_function` asks: a structural trait's member the compiler
  supplies is `Builtin` (those two, and `Call` of a function reference);
  any other is its default, `Instance { function, [Self, own...] }`, as for
  an impl that inherits it, so `first`, `last`, `as_slice` and
  `as_slice_mut` lower as generic functions. Lowering's `resolve_call`
  answers `Builtin` with `Dispatch::Supplied`, and `lower_supplied`
  (`places.rs`) expands it: the receiver once into a temporary, then
  `sequence_length` or `sequence_base`, the helpers indexing reads too.
  Found on the way: `resolve_call` and `lower_constant` substituted their
  type arguments without normalizing, so an operator on `M::Size` in a
  generic instance (`first`'s `self.len() == 0`) met an unreduced
  projection and resolved as abstract. Tests in `lower.rs`:
  `slice_and_array_methods_lower` (both forms of `len`/`as_ref`, by path,
  `first`/`last` with their traps, `as_slice` indexed, `as_slice_mut`
  written), `a_wide_slice_has_a_64_bit_length`.

## Open

- Checking a generic function's static data in `wx check`: an evaluation
  mode that treats an abstract constant as an opaque value and reports
  only forms that are never constant.

- Whether `Memory::INDEX` should exist at all (not planned).
- Low-memory reservation (null, niches).
- Arrays inside aggregates and arrays of arrays: done (2026-11-04) for a
  sized array. `layout.rs` `Piece::Array` (bytes, no values; `memory_values`
  of an array repeats its element's); the checker indexes a place of array
  type in place (`h.data[i]`, as `p.field`; `build_index`), and
  `lower_element` starts from that place's address and offset; the
  evaluator pushes an unplaced literal's element values (a string's bytes,
  a repeat's element per count) and reads a data constant used as an
  element from its body, so nested data is written inline. Tests:
  `layout.rs` `an_array_field_takes_its_elements_bytes`, `typecheck.rs`
  `an_array_place_is_indexed_in_place`, `lower.rs`
  `an_array_field_is_indexed_in_place`,
  `nested_arrays_are_static_data_written_inline`,
  `nested_loads_through_pointers_match_their_explicit_form`.
- A slice as a struct's last field (an unsized tail): reported by lowering
  (E2114), waits for `Sized`.
- Static data holding a struct with an array (`Header(2, "abcd")` placed):
  a construction is checked as a `StackValue`; deferred.
