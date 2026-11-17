# Variants, WIT, and components

Status: research and proposal, 2026-11-17 to 2026-11-18. Nothing here is
implemented. It records a design discussion that started with variant items
and their relation to WIT's variants and grew into how the component model
works and how wx could express components itself.

Sources: the Canonical ABI rules were read from `design/mvp/CanonicalABI.md`
and the binary format from `design/mvp/Binary.md`, both on the
component-model repository's `main` branch on 2026-11-17. The core-module
naming conventions and the shim mechanics were read from the `wit-parser` and
`wit-component` 0.258.3 sources (`resolve/mod.rs`'s `wasm_import_name` and
`wasm_export_name`; `encoding.rs`, `linking.rs`). Worked examples were derived
by hand and have not been checked against `wasm-tools` output. Syntax in this
note is a sketch; the semantics are what was agreed.

## Direction in short

- WIT is an ABI wx follows closely at component boundaries, not wx's internal
  representation. wx keeps its own optimizable layouts; the canonical form is
  a separate, visible type.
- WIT files are the only source of interface definitions. wx never restates a
  WIT signature.
- Composition (which core modules exist, how they are instantiated and wired,
  where lifting and lowering happen) is wx syntax, checked by the type system,
  not a policy hidden in the compiler or in `wit-component`. This follows from
  wx's aim of making Wasm's resources visible: instances and canonical options
  are such resources.
- A default composition can exist for simple packages, but only as sugar for
  the explicit form, printable with something like `wx build --emit
  composition`.

## How the component model works

### A component is an instantiation script

A component is not a core module plus metadata. It is a declarative program
for the runtime: which core modules to instantiate, with which imports, and
which core functions to wrap with `canon lift` or `canon lower`. Core modules
are embedded byte for byte. The component level has no code section: the only
code is in core modules; everything else is types, instantiation, aliasing and
`canon` definitions. Definitions only refer backwards (each index points to an
earlier definition), so the graph is acyclic and can be validated once and
instantiated in one top-down pass.

A small world, `import log: func(msg: string); export run: func();`, packaged
the way `wit-component` does it:

```wat
(component
  (import "log" (func $log (param "msg" string)))

  (core module $Main                                  ;; the developer's code, unchanged
    (import "$root" "log" (func $log (param i32 i32)))
    (memory (export "memory") 1)
    (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) …)
    (func (export "run") … call $log …))

  (core module $Shim                                  ;; see "The instantiation cycle"
    (table (export "$imports") 1 funcref)
    (func (export "log") (param i32 i32)
      local.get 0  local.get 1  i32.const 0  call_indirect (param i32 i32)))
  (core module $Fixup
    (import "" "$imports" (table 1 funcref))
    (import "" "log" (func (param i32 i32)))
    (elem (i32.const 0) func 0))

  (core instance $shim (instantiate $Shim))
  (core instance $main (instantiate $Main
    (with "$root" (instance (export "log" (func $shim "log"))))))
  (core func $log_low (canon lower (func $log) (memory $main "memory")))
  (core instance (instantiate $Fixup
    (with "" (instance (export "$imports" (table $shim "$imports"))
                       (export "log" (func $log_low))))))

  (func (export "run") (canon lift (core func $main "run")))
)
```

The core module never knows it is in a component: it sees ordinary core
imports and exports. `canon lower` produces a core function; `canon lift`
produces a component function; their options point back into a core
instance's exports (`(memory $main "memory")`).

### Who lifts and lowers

The runtime does, never the core module. Lowering is the opposite of lifting.

- `canon lift` wraps a core export. On a call the runtime lowers the
  arguments into the module's memory (calling its `realloc` for strings and
  lists), calls the core function, lifts the results out of core values or
  memory, then calls `post-return` so the module can free result buffers.
- `canon lower` wraps a component function into a core function the module
  imports. On a call the runtime lifts the arguments out of the module's
  memory, calls the callee, and lowers the results back in, through `realloc`
  or a return pointer the caller passes.

What the runtime (Wasmtime) does with a component:

- **Load:** parse, validate each core module, type-check the component graph
  (imports, exports, `instantiate` arguments). All type checking is here.
- **Compile:** each core module as usual; each `canon lower` into a native
  trampoline specialized to its WIT signature; component-to-component links
  into fused adapters that read one memory and write the other directly.
- **Instantiate:** run the script in order; create a handle table per
  component instance for resources.
- **Call:** run generated code, nothing interpreted. Only value checks happen
  per call: tag in range, `char` valid, string encoding valid (and
  transcoding), pointers aligned and in bounds.

### Runtime and core module, side by side

| Runtime, from the component binary | Core module, what wx must produce |
|---|---|
| type-checks the whole graph once | core functions with flattened signatures (at most 16 flat parameters, 1 flat result, otherwise memory and return pointers) |
| generates lift/lower code per signature | canonical layout behind every pointer it hands out or receives |
| copies strings and lists between memories, transcodes strings | `cabi_realloc(old_ptr, old_size, align, new_size) -> ptr` |
| checks tags, chars, UTF-8, bounds; traps on bad values | a return area for exports with more than one flat result |
| calls `realloc` and `post-return` at the right moments | `cabi_post_<name>` to free what an export returned |
| owns resource handle tables; calls a resource's destructor when its last handle drops | the representation behind its own resources; calls `[resource-new]` to get a handle |
| keeps components isolated: memories are never shared between components | everything inside: its types, layouts, allocator |

### One call in each direction

wx exports `f: func(s: string) -> list<u8>`:

```
caller ──s──▶ runtime: lift s from the caller's memory
              runtime: ptr = wx.cabi_realloc(0, 0, 1, len)   wx allocates
              runtime: copy the bytes into wx's memory
              runtime: rp = wx.f(ptr, len)
              wx:      writes (list_ptr, list_len) into a return area, returns rp
              runtime: lift the list from wx's memory, lower it into the caller's
              runtime: wx.cabi_post_f(rp)                    wx frees the result
caller ◀──list──
```

wx imports `g: func(s: string) -> list<u8>`:

```
wx: g(ptr, len, retptr)            more than one flat result: the caller passes a return pointer
    runtime: lift s from wx's memory (read only; the buffer stays wx's)
    runtime: call the callee
    runtime: p = wx.cabi_realloc(0, 0, 1, n); write the list there
    runtime: store (p, n) at retptr
wx: reads (p, n); wx owns that buffer and must free it
```

Everything entering wx's memory comes through wx's `realloc` and is owned by
wx. Everything wx sends out stays wx's; for exports it is released in
`post-return`. The runtime never frees anything in a module's memory.

## The instantiation cycle and shims

### The cycle

Two rules collide:

1. **Core Wasm:** a module receives all its imports when it is instantiated.
   There is no late binding; import references never change afterwards.
2. **Component model:** `canon lower` names its memory and `realloc` when it
   is defined. The lowered function is specialized to that memory; without a
   concrete memory it cannot exist. A memory is only an export of a core
   instance, so it exists only once that instance does.

When the memory is the module's own:

```
lowered log    needs     Main's memory         (rule 2)
Main's memory  exists    after Main is instantiated
Main           needs     lowered log           (rule 1)
```

Backward-only references make this unwritable.

### How `wit-component` breaks it

The only mutable function reference in MVP core Wasm is a `funcref` table,
written after instantiation: the same trick as a PLT/GOT in dynamic linking.

1. `Shim` has no imports, so it is instantiated first. It owns an empty table
   and exports a stand-in `log` that `call_indirect`s through slot 0.
2. `Main` is instantiated with the stand-in. Its memory and `cabi_realloc`
   now exist.
3. `canon lower log (memory $main "memory")` is now possible.
4. `Fixup` has no code, only an active `elem` segment writing an imported
   function into an imported table. Instantiating it is the write. It exists
   because the component format has no instruction for writing a table.

Cost: two tiny modules at load time; per call, the stand-in call, a
`call_indirect` (bounds and signature check), then the trampoline.

### When no shim is needed

`wit-component` lowers an import directly when its options are empty
(`options.is_empty()` in `encoding.rs`), or when the memory is available
before the main module (`memory_available`, the adapter case).

| import | needs from Main | lowering |
|---|---|---|
| `get-random-u64: func() -> u64` | nothing | direct |
| `log: func(msg: string)` | `memory` | indirect |
| `read: func() -> list<u8>` | `memory` and `realloc` | indirect |
| more than one flat result | `memory` for the return pointer | indirect |

A world of scalars only is a single core module.

`wit-component`'s shared-everything linking (`linking.rs`) uses the same
idea at a larger scale: a synthesized `env` module "hosts the component's
single memory and function table", and an `init` module fills the table and
applies relocations (modules built to the Wasm dynamic-linking convention).

## Variants and the canonical layout

### Why not make the ABI wx's representation

The first idea was to make the Canonical ABI the representation of a wx
variant in memory and on the stack, so a variant crossing a boundary needs no
conversion. Rejected: it is too restrictive inside a module. It has no niches
(`Option<Bool>`, `Option<Char>` or an option of a non-null pointer always
carry a tag), fixes the tag at offset 0 with a width chosen by the case count,
merges every case's payload into shared stack slots (`f32` in an `i64` slot
costs a reinterpret and an extend on every construction and match), and
numbers cases 0..n-1 with no written values.

### wx's own layout is the compiler's choice

A variant's default layout is decided by the compiler, deterministically. It
may use niches, put the tag in the payload's padding or after it, and give
each case its own stack slots. Its starting point is the canonical layout
(tag first, cases in declaration order, tag width by case count), departing
only where an optimization applies, so most variants convert for free. Memory
layout stays open to optimization; the stack slot policy should be fixed
early, since `StackValue::Repr` and `transmute` depend on it.

### The canonical layout is its own type, `Wit<T>`

One type cannot have two layouts chosen by context. If `Option<T>` were
compact in the program's data but canonical in a boundary list, a
`M::&Option<T>` would mean different bytes depending on where it points,
`size_of` would depend on context, `memory.copy` would silently convert,
`transmute` across memories would break, and generic code over `M::&[T]`
would be compiled per layout invisibly. Choosing the layout per memory fails
too when one memory holds both kinds of data.

So the canonical form is a separate type, `Wit<T>`, derived by the compiler
from `T`'s structure: `Wit<Option<u32>>` is a `u8` tag at 0 and the payload
at 4; `Wit<(A, B)>` keeps declaration order; `Wit<Char>` is a `u32`. A WIT
`list<option<T>>` is `M::&[Wit<Option<T>>]`. Access:

- by projection: `M::&Wit<Option<T>>` to `Option<M::&Wit<T>>`, no copy;
- by value: `get() -> Option<T>`, `set(Option<T>)`, O(1), no allocation;
- by reinterpretation when layouts agree: if `Option<u32>`'s own layout
  equals the canonical one, `M::&[Option<u32>]` views as
  `M::&[Wit<Option<u32>>]` for free, through an equality on an associated
  memory-representation type, as `transmute` requires equal
  `StackValue::Repr`;
- by copying a whole list, an ordinary loop with an allocator, never implicit.

Precedent: rkyv's `Archived<T>`, FlatBuffers, Cap'n Proto.

### Values convert on the stack; data in memory must be `Wit<T>`

On the stack (a parameter or flat result) a layout mismatch costs a few
instructions and allocates nothing. Behind a pointer it costs a copy of the
whole buffer into a new allocation, which the compiler must not do on its own
since allocation is left to libraries. Hence:

> Stack values convert through a trait. Data behind a pointer in a boundary
> signature must be written as `Wit<T>`.

```wx
pub trait Canonical {
    type Wit;
    func lower(self) -> Self::Wit;
    func lift(wit: Self::Wit) -> Self;
}
```

Derived by the compiler from a type's structure, writable by a user, called
by the boundary glue, inlined to a few instructions.

Plain core imports (`import "wasi_snapshot_preview1" as wasi { … }`) are a
different thing and stay as they are: core Wasm signatures, wx types mapped
through `StackValue::Repr`, no conversion.

## Composition in wx

### An interface has two views

WIT types have no memory: at the component level a `string` is an abstract
value. It becomes a pointer only when bound to a memory. So one WIT interface
appears in wx two ways:

| view | written | `string` is | used where |
|---|---|---|---|
| abstract | `wasi:cli/stdout` | an abstract value | component imports and exports |
| bound | `wasi:cli/stdout<M>` | `M::&str` sent, `M`-owned received | a package that calls or implements it |

Lowering is the conversion from the abstract view to a bound one; lifting is
the reverse. Neither needs its own syntax, and neither is spelled `canon`.

A signature needs only `M`. `realloc` and `post-return` decide how a call is
carried out, not its signature:

- **The allocator is a separate parameter from the memory.** The 2026-08-11
  devlog rejected one allocator per memory. The bound view takes `A` only when
  some function in the interface receives buffers, read off the WIT:
  `wasi:cli/stdout<M>`, but `wasi:filesystem/types<M, A>`.
- **`post-return` is derived, not supplied.** It frees what an export
  returned, so it needs the allocator that allocated it. This forces the
  devlog's open allocator-identity question at least for boundary buffers.
  Natural rule: everything crossing a binding belongs to that binding's `A`;
  incoming buffers came from `A`'s `realloc`, outgoing ones are freed through
  `A`.

### Packages, core modules and instances

A package's parameters are of two kinds:

- **Compile-time** (types and constants that change code or layout):
  monomorphized; each argument is a different core module.
- **Link-time** (memories, globals, tables, functions with a fixed core type):
  exactly what core Wasm can import. They are the core module's imports: one
  module, instantiated any number of times with different arguments.

So a package compiles to a core module once its compile-time parameters are
fixed, and its link-time parameters are its imports. Today's
`import "x" as y { … }` blocks and link-time parameters are the same concept.
A memory parameter must fix what is part of the memory import type (`Size`,
shared or not); being generic over `Size` makes it compile-time.

Memories are nominal types, so instances are namespaces for types: if `bump`
is instantiated twice, `a.Heap` and `b.Heap` are different types
(path-dependent typing, as with ML functors).

Instances are not modules. One module can have many instances:

```
packages (source)   core modules (compiled)   instances (in the component)
  bump      ──▶       bump.wasm       ──▶       alloc
  logic     ──▶       logic.wasm      ──▶       logic   (or logic_a, logic_b)
  app       ──▶       no code: only wiring, it becomes the component
```

A package can relate to another in two ways:

| relationship | meaning | in Wasm |
|---|---|---|
| library dependency | code compiled into the user's module, inlined | nothing; part of the module |
| instance link | link-time parameters filled with another instance's exports | core imports and exports |

The same package can play both roles (see "share state, not code" below).

### Composition syntax

The core package binds interfaces to its memory and implements its exports;
the component package names a world, which is its signature, and only wires:

```wx
// logic/ — link-time parameters: one core module, any number of instances
package<M: Memory<Size = u32>, A: Allocator<M>>;

use wasi:cli/stdout<M>;                 // a core import; signature from WIT

export wasi:cli/run<M, A> {             // checked against WIT, like an impl
    func run() -> Result<(), ()> { … }
}
```

```wx
// app/ — wx.json: { "world": "wasi:cli/command" }
instance alloc = bump;
instance logic = logic<alloc.Heap, alloc.Bump> {
    wasi:cli/stdout,                    // abstract → stdout<alloc.Heap>: lowering
};
export wasi:cli/run = logic;            // bound → abstract: lifting
```

Semantics:

- **Lowering is a coercion at an argument.** Passing the abstract interface
  where a bound one is expected lowers it, with memory and allocator taken from
  the parameter's type. `--emit` can show the resulting `canon` entries.
- **Lifting is the same rule at an export**, `post-return` derived from `A`.
- **Instance values refer backwards; types may refer to any instance in the
  composition.** Types are static (an instance's memory declaration is known
  at compile time), so a forward type reference creates no cycle. A forward
  value reference (`logic<logic.Heap, …>` naming a memory that does not exist
  yet) is "used before definition". The cycle becomes an ordinary error.
- **The memory option enters the type.** Lowering against `alloc.Heap` gives a
  function taking `alloc.Heap::&[u8]`; a pointer into another memory is a type
  error.
- **Instantiation is checked like a struct literal**: missing imports, wrong
  signatures, a memory with the wrong `Size`.
- **The world checks the component's imports and exports**, so not even the
  import list is written twice.
- Every construct maps to one kind of component section: core module, core
  instance, `canon`, import, export. Shims and fixups are not syntax; they are
  ordinary packages a user (or the default composition) writes.

### Strategy A: shims, written in wx

The developer's package owns its memory and binds its import to it:

```wx
// logic/main.wx
memory C: u32;                          // static data, heap and boundary buffers

use example:app/log<C>;                 // bound to the package's own memory

export example:app/run<C, Bump> {
    func run() { log("hello\n") }       // the literal is already in C
}

export { C }                            // the lowering below needs this memory
```

The shim is a slot holding the real function. With typed function references
a mutable global replaces the MVP's table and `call_indirect`; a trapping
placeholder replaces null:

```wx
// shim/main.wx
package<M: Memory>;                     // M appears only in types

func unset(msg: M::&str) { trap() }

pub global mut log_impl: func(M::&str) = unset;

pub func log(msg: M::&str) { log_impl.get()(msg) }   // global.get + call_ref

export { log, log_impl }
```

The fixup writes the slot from a start function. Running code at instantiation
is the only way to act on a value right after it exists, so a module
instantiated later must import it; a component-level start function would
remove the need, but it is gated in the spec.

```wx
// fixup/main.wx
package<M: Memory>;

import "shim" as shim { global mut log_impl: func(M::&str); }
import "lowered" as lowered { func log(msg: M::&str); }

#[start]
func install() { shim::log_impl.set(lowered::log) }
```

```wx
// app/ — wx.json: { "world": "example:app/app" }
instance shim  = shim<logic.C>;         // forward type reference
instance logic = logic { example:app/log: shim.log };
instance fixup = fixup<logic.C> {
    shim: shim,
    lowered: { log: example:app/log },  // the lowering happens here
};
export example:app/run = logic;
```

Forward type references keep the shim fully typed: the stand-in is
`func(logic.C::&str)`, exactly what `logic` expects. Without them the shim
would use raw `func(u32, u32)` and the composition would need an unchecked
cast. What types cannot check is that `fixup` runs before the first call;
otherwise `unset` traps.

### Strategy B: a separate allocator instance

Define the memory in its own instance, instantiated before the code:

```
1. alloc   defines the memory; exports memory, allocator state, cabi_realloc
2. lowerings name alloc's memory and realloc   (alloc exists)
3. logic   instantiated with alloc's exports and the lowered imports, all direct
4. lifts   name alloc's memory and realloc; post-return from logic
```

No shim, table, fixup or indirect call. That `canon` options may name a
memory from a different core instance than the function is believed valid
(`wit-component`'s adapters do it) but should be confirmed with
`wasm-tools validate` on a prototype.

**Share state, not code.** If allocation were a call into `alloc`, every
allocation in `logic` would cross instances and could not be inlined. Instead
`alloc` exports the allocator's state as globals and the memory; the
allocator's code is compiled into `logic` too and inlined, working on the
imported state. Only the runtime calls `alloc`'s copy, through
`cabi_realloc`. `bump` is then both an instance (`alloc`) and a library of
`logic`. Requirements: allocator state must be globals and memory; the
optimizer must not cache a shared global in a local across a lowered import
call, since the runtime may call `realloc` during it (an effect: "a lowered
import may allocate in `C`").

Core-level shape:

```wat
(module $bump                                   ;; instance alloc
  (memory (export "heap") 1)
  (global (export "top") (mut i32) …)
  (func (export "cabi_realloc") …))

(module $logic                                  ;; instance logic
  (import "M" "heap" (memory 1))
  (import "A" "top"  (global (mut i32)))
  (import "wasi:cli/stdout@0.2.0" "[method]output-stream.blocking-write-and-flush"
          (func (param i32 i32 i32 i32)))
  (func (export "wasi:cli/run@0.2.0#run") …)
  (func (export "cabi_post_wasi:cli/run@0.2.0#run") …))
```

**Static data in a shared memory.** If `logic`'s data segments go into
`alloc`'s memory, the modules must agree on regions. Options considered:

1. *Whole-component compilation*: the component package sees every package
   it instantiates and assigns static regions; the heap starts after the last.
   A module's layout then depends on the component it is built for.
2. *Relocatable modules*: data segments at `global.get $base + offset` with
   `$base` imported; every static address costs a `global.get` and an `add`;
   pointers stored inside static data (`hello_wasi`'s iovec) are patched by
   relocations in a start function; the module publishes its size and
   alignment in a custom section. A component cannot create a core global, so
   the bases come from a generated module exporting constant globals (or the
   module allocates its region at start and fills it from passive segments
   with `memory.init`). This is Wasm's dynamic-linking convention
   (`__memory_base`, `__table_base`, `dylink.0`). It pays off only for
   precompiled modules reused across compositions, or several instances of
   one module sharing a memory. `DATA_END` would stop being a constant.

**Resolution: separate memories.** The problem is two modules placing static
data in one memory. Let the shared memory hold no static data:

```
alloc's memory C     heap only, no data segments; the allocator owns its layout;
                     the world's memory, where every boundary buffer lives
logic's memory heap  static data and private state, fixed at compile time as today;
                     the runtime never sees it
```

No layout module, no relocations. Copies, which the pointer types make
visible:

| data | lives in | copy |
|---|---|---|
| built at runtime and sent | allocated in `C` directly, `C::*[u8]` | none |
| received from imports | `C`, written by the runtime | none |
| generic code (`encode<M: Memory>`) | instantiated for `C` | none |
| literals and constant tables sent | `heap`, since `C` has no static data | yes |
| private data later sent | `heap` | yes, by choice |

Literals cost either a `memory.copy` from `heap` to `C` per use, or one
`memory.init` from a passive segment into an allocated region of `C` at
startup. Proposed: a literal used as `C::&str` in a memory without static data
is placed at initialization, stated as a rule (the alternative is a type
error and an explicit copy). This needs the allocator usable during
initialization, and multi-memory inside a component's core module.

**Several instances on one allocator.** One `alloc` can serve any number of
`logic` instances, each with its own private memory, globals and static data
from the same compiled module:

```wx
instance alloc = bump;
instance a = logic<alloc.C, alloc.Bump> { wasi:cli/stdout };
instance b = logic<alloc.C, alloc.Bump> { wasi:cli/stdout };
```

- Instances can call each other with plain core calls: a `C::&[u8]` passes as
  two `i32`s, no lifting, lowering or copy; typed as
  `func(alloc.C::&[u8])`, so pointers into private memories are rejected.
- One allocator: a buffer `a` allocates may be freed by `b`.
- No isolation in `C`; the component, not the core instance, is the isolation
  boundary. Private memories are isolated since they are not exported.
- Shared allocator state is consistent single-threaded, including when the
  runtime calls `cabi_realloc` mid-call; shared-memory threads would need an
  atomic allocator.
- Uses: per-tenant or per-plugin state with one codebase, fresh instance per
  request, splitting a large program while sharing boundary buffers.

This gives two levels of composition, both written in wx and chosen per
relationship:

| | instances in one component | separate components |
|---|---|---|
| shared memory | `C` | none |
| calls | direct core calls, pointers as-is | lift, runtime adapter, lower, copies |
| isolation | none in `C` | full |
| interface | wx types over `alloc.C` | WIT |
| analogy | libraries in one address space | separate processes |

### Comparing the strategies

| | A: shims | B: separate `alloc` and private memories |
|---|---|---|
| memories | one, `logic.C` | `C` (boundary only) and one private per instance |
| literals sent | used directly | copied into `C`, at startup or per use |
| boundary call needing memory | stand-in, `call_ref`, trampoline | direct |
| extra modules | `shim` and `fixup` | `alloc` |
| several `logic` instances | each needs its own shim, fixup, memory; no shared buffers | share `C` and the allocator, call each other without copies |
| failure mode | calling before `fixup` runs traps | none |

Neither wins everywhere, which is the argument for making composition
explicit.

## Developer experience

- **WIT is a compiler input.** The manifest names WIT packages and a world;
  the compiler parses them (`wit-parser`) and synthesizes wx items:
  interfaces as modules or traits, records as structs, variants and enums as
  wx's, resources as handle types. No generated source; the language server
  shares the compiler, so completion, hover and go-to-definition into `.wit`
  work, and `wx check` reports mismatches.
- **Exporting is implementing.** A bound interface export is checked like a
  trait impl; a missing or wrong function is an ordinary error naming the WIT
  function.
- **Signatures state cost.**

  | WIT | sent (import parameter) | received (import result) |
  |---|---|---|
  | `string`, `list<u8>` | `M::&[u8]`, borrowed, no copy | `M`-owned, in `A`'s `realloc`'d memory |
  | `list<option<T>>` | `M::&[Wit<Option<T>>]` | `M`-owned `[Wit<Option<T>>]` |
  | `option<T>`, records, `result` | wx's own types, through `Canonical` | the same |
  | `own<R>`, `borrow<R>` | `R`, `&R` | `R` |

- **Allocation is named only when needed.** A world that never receives
  strings or lists needs no allocator; otherwise the error says which function
  receives what.
- **The glue is inspectable.** Hover shows an import's core signature and the
  cost per parameter; `--emit composition` prints the (default) composition
  in wx syntax; `--emit boundary` prints the generated wrappers.
- **Names.** WIT's kebab-case maps to wx names (`get-bytes` to `get_bytes`,
  `incoming-request` to `IncomingRequest`), the WIT name shown on hover.

## Variant items in wx

Independent of the boundary:

- A `variant` item beside `enum`. `enum` stays a repr integer with named
  constants and written values; `variant` is the tagged union, matching WIT's
  names.
- A case has at most one payload type, as in WIT; `Some(A, B)` could be sugar
  for a tuple payload. Named-field cases have no WIT counterpart.
- Core declares `Option<T> { None, Some(T) }` and `Result<T, E> { Ok(T),
  Err(E) }` in that order, so declaration order is the canonical numbering.
  Internally a niche or written tag may encode a case any way; the boundary
  maps it to index *i*.
- `match` lowers to `br_table` on the tag with `unreachable` as default, as
  closed enums do. Values entering through the runtime are already validated.
- Compiler shape: `Type::Variant { variant_index, type_args }`, a variant
  aggregate in `tir/layout.rs` (size, alignment, tag, payload placement, slot
  types, a row per case), its stack shape in `tir/lower/shapes.rs`. Matching
  through a reference reads the tag and the case's payload in place; loading a
  whole variant onto the stack may need a branch on the tag when cases load
  differently, as the ABI's `load_variant` does.

## Implementation layers

1. **WIT front end:** `wit-parser` into wx items (abstract and bound views).
2. **Boundary contract:** per WIT function, a data record computed from the
   WIT signature and the ABI alone, consumed by everything after it:

   ```
   BoundarySig {
       direction:   Import | Export
       core_name:   (module, field) or export name
       params:      [CoreSlot]   // Value(i32/i64/f32/f64) | BufPtr(b) | BufLen(b) | RetPtr
       results:     Flat(CoreType) | ViaRetPtr(layout) | None
       buffers:     [Buffer { wit_type, layout, owner, freed_by: PostReturn | Caller }]
       post_return: bool
   }
   ```

   `wit-parser`'s `Resolve::wasm_signature` implements the ABI's
   signature flattening and can be the test oracle.
3. **Glue:** wrappers calling `Canonical::lower`/`lift` on stack values,
   passing buffers as (ptr, len), return areas, `cabi_post_*`,
   `cabi_realloc` forwarding to the bound allocator.
4. **Packaging:** with composition as syntax, wx writes the component
   sections itself (`wasm-encoder`); the script is a handful of sections and
   wx controls all of it. `wit-component`'s `ComponentEncoder` (one main
   module plus adapters, legacy names, `component-type` section) is a
   possible stepping stone for the default single-package case.

Testing: Wasmtime's component API, host imports in Rust, exports called with
typed or dynamic values, matching `AGENTS.md`'s execution-test boundary.

## Open questions

Variants and layout:

1. Matching on views: should `Some(x)` / `None` match `M::&Wit<Option<T>>`
   directly, binding `x: M::&Wit<T>`, or is a method returning
   `Option<M::&Wit<T>>` explicit enough?
2. `Wit<T>` as a compiler-known constructor, or `<T as Canonical>::Wit` with
   only its layout computed by the compiler?
3. Stack slot policy for variants: per-case slots or the ABI's joined slots?
   Decide before `StackValue::Repr` for variants is fixed.
4. Record field order: `#[fixed_order]` then matters only outside WIT; wx
   tuples are always sorted today (`tir/layout.rs`), which `Wit<(A, B)>`
   sidesteps.
5. Pointer payloads at a boundary: reject until resources and handles exist?

Composition:

6. Binding: lowering as a coercion at an argument (proposed), or explicit
   `iface.bind<M>()`?
7. Allocator shape: a type `A: Allocator<M>` (code inlined, state in
   link-time globals; proposed) or a function value (a cross-instance call per
   allocation)? Either way `post-return` needs allocator identity for
   boundary buffers.
8. Should package syntax mark compile-time and link-time parameters
   differently, or infer the kind from the bound?
9. Bind per interface (`stdout<M>`) or per function?
10. Packages only as core modules, or also a lighter nested unit inside a
    package?
11. May a component package contain code (an implicit `self` instance), or
    is it composition only (proposed)?
12. Static data: separate memories (proposed) vs whole-component compilation
    vs relocatable modules. With separate memories: literals placed in `C` at
    initialization (proposed) or a type error with an explicit copy?
13. Multi-memory inside a component's core module: not verified.
14. `canon` options naming a memory from another core instance than the
    function: believed valid, not verified.
15. New language features implied: `#[start]`, forward type references in
    compositions, typed function references in globals (not checked whether
    wx supports them today), tables if wanted.
16. Composing external components (`instance x = component "other.wasm"`),
    making wx a WAC replacement for its own projects: after the core-level
    version.
17. Async (Preview 3): `stream`, `future`, `async`/`callback` options; after
    the synchronous path.

## Appendix A: the Canonical ABI's rules for variants

`despecialize` turns `enum` into a variant whose cases have no payload,
`option<T>` into `{ none, some(T) }`, `result<T, E>` into
`{ ok(T), error(E) }`, and `tuple` into a record with fields `"0"`, `"1"`, …
`flags` and `string` keep their own representations.

**Tag.** The case's index in declaration order, of type
`discriminant_type(cases)`: `u8` up to 256 cases, `u16` up to 65536, else
`u32`.

**Memory.**

```python
def max_case_alignment(cx, cases):
  a = 1
  for c in cases:
    if c.t is not None:
      a = max(a, alignment(cx, c.t))
  return a

def alignment_variant(cx, cases):
  return max(alignment(cx, discriminant_type(cases)), max_case_alignment(cx, cases))

def elem_size_variant(cx, cases):
  s = elem_size(cx, discriminant_type(cases))
  s = align_to(s, max_case_alignment(cx, cases))
  cs = 0
  for c in cases:
    if c.t is not None:
      cs = max(cs, elem_size(cx, c.t))
  s += cs
  return align_to(s, alignment_variant(cx, cases))
```

The tag is at 0, little-endian. The payload is at
`align_to(tag_size, max_case_alignment)`, the same for every case. Padding is
never written nor read. A load traps if the tag is not below the case count.

**Stack.** A variant flattens to the tag's `i32` followed by its cases' flat
types joined position by position:

```python
def join(a, b):
  if a == b: return a
  if (a == 'i32' and b == 'f32') or (a == 'f32' and b == 'i32'): return 'i32'
  return 'i64'
```

Lowering converts a case's values into the joined slots and fills unused
slots with `0`; lifting converts back and ignores unused slots:

| case value to slot | lower | lift |
|---|---|---|
| `f32` to `i32` | `i32.reinterpret_f32` | `f32.reinterpret_i32` |
| `i32` to `i64` | `i64.extend_i32_u` | `i32.wrap_i64` |
| `f32` to `i64` | reinterpret, then `extend_u` | wrap, then reinterpret |
| `f64` to `i64` | `i64.reinterpret_f64` | `f64.reinterpret_i64` |

`MAX_FLAT_PARAMS` is 16, `MAX_FLAT_RESULTS` is 1 (`MAX_FLAT_ASYNC_PARAMS` 4).
Over the limit, parameters go through memory (`realloc` on the callee's side)
and results through a return area: the callee returns a pointer to it when
lifted; the caller passes one when lowered.

**Related types.**

- `flags`: 1, 2 or 4 bytes for up to 8, 16 or 32 labels, label *k* is bit
  *k*; one `i32`.
- `bool`: 1 byte; `i32`; any nonzero value lifts to true.
- `char`: 4 bytes, alignment 4; lifting traps at 0x110000 and above and on
  surrogates.
- `list<T>`, `string`: `(ptr, len)`, two `i32`s with a 32-bit memory; a
  fixed-length list flattens to its element's flat types repeated.

**Worked examples.**

| type | memory | stack |
|---|---|---|
| `option<u32>` | tag 0, payload 4, size 8, align 4 | `[i32, i32]` |
| `option<u8>` | tag 0, payload 1, size 2, align 1 | `[i32, i32]` |
| `result<u64, f32>` | tag 0, payload 8, size 16, align 8 | `[i32, i64]` |
| `variant { a(u8), b(f32), c(tuple<u16, u64>) }` | tag 0, payload 8, size 24, align 8 | `[i32, i32, i64]` |

## Appendix B: binary format and naming conventions

**Preamble.**

```
core module:  00 61 73 6D  01 00 00 00     magic, version 1
component:    00 61 73 6D  0D 00 01 00     magic, version 0x0d, layer 1
```

The core version's 4 bytes are read as a 2-byte version and a 2-byte layer;
layer 0 is a core module, 1 a component, so both use `.wasm`. The component
version is pre-standard and bumped until the format is final.

**Sections.**

| id | section |
|---|---|
| 0 | custom |
| 1 | core module (a complete core module binary) |
| 2 | core instance: `instantiate m (with "name" instance)…` or inline exports |
| 3 | core type |
| 4 | nested component |
| 5 | instance |
| 6 | alias: `(alias core export i "name" (sort))` and others |
| 7 | type (WIT-level types) |
| 8 | canon |
| 9 | start (gated) |
| 10, 11 | import, export |
| 12 | value (gated) |

**`canon`.**

```
lift:  0x00 0x00 core-func opts type  → component func
lower: 0x01 0x00 func opts            → core func
resource.new 0x02, resource.drop 0x03, resource.rep 0x04 (and async built-ins)
opts:  0x00 utf8 | 0x01 utf16 | 0x02 latin1+utf16 | 0x03 (memory m)
     | 0x04 (realloc f) | 0x05 (post-return f) | 0x06 async | 0x07 (callback f)
```

String encoding defaults to UTF-8.

**Core-module naming (legacy scheme, what tooling expects today).**

| purpose | core name |
|---|---|
| imported interface function | module `wasi:cli/stdout@0.2.0`, field `get-stdout` |
| imported world-level function | module `$root`, field `log` |
| method, constructor, static | `[method]output-stream.write`, `[constructor]x`, `[static]x.f` |
| drop an imported resource | field `[resource-drop]output-stream` |
| exported resource intrinsics | module `[export]my:pkg/iface`, fields `[resource-new]x`, `[resource-rep]x`, `[resource-drop]x` |
| exported function | `my:pkg/iface#f`, or `f` at world level |
| its post-return | `cabi_post_my:pkg/iface#f` |
| exported resource destructor | `my:pkg/iface#[dtor]x` |
| memory, allocator, init | `memory`, `cabi_realloc`, `_initialize` |
| the world | custom section `component-type…` |

`wit-parser` also has a newer standard mangling meant to become the stable
convention: `cm32p2|iface|f`, `cm32p2|iface|f_post`, `cm32p2|iface|x_dtor`,
`cm32p2_memory`, `cm32p2_realloc`, `cm32p2_initialize`.
