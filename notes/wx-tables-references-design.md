# Tables, tags, host types and function references — design note

**Status: design only.** Nothing in this note is implemented, and no part of
it exists in the lexer, parser, TIR or stdlib today (the one exception is the
current implicit funcref table, §3). Do not describe any of it as a language
feature. Written 2026-10-09 on `tir-refactor`, from the chapter 3 design
discussion; the thesis chapter will be a narrative version of this, this note
is the implementation-facing record.

Related: `effect-system.md` (§7 "Tables would follow the same shape"),
`post.md` (Tags, Exception), `typeset.md`, `intrinsics.md`.

---

## 1. Goals

1. Give every Wasm item kind an **identity** the source can name, and a
   **shape** the compiler can check. Today that holds for functions, globals
   and memories. It does not hold for tables or tags.
2. Keep the model that already works for memories (`Type::Memory`, synthetic
   `Memory` impl, pointers that carry their memory) and extend it, not invent
   a second one.
3. Make imports the same kind of item as definitions; only the origin differs.
4. Expose reference types (`funcref`, `externref`) without making raw table
   indices forgeable and without putting references into linear memory.

Non-goals here: GC types, the `any`/`exn` reference families, the effect
system, ownership/borrow rules, element-segment initialisers (see §8).

---

## 2. Wasm facts this relies on

**Items.** Each item kind has its own index space; identity is `(kind, index)`.
Imports take the first indices of their kind, so a final index is a late
layout decision, not something source code can know. Each kind also has a
shape:

| Kind | Shape |
| --- | --- |
| function | signature |
| table | reference type, limits, index type (table64) |
| memory | limits, shared flag, index type (memory64) |
| global | value type, mutability |
| tag | signature (parameters; results are empty for exceptions) |

**Reference types are values, not bytes.** `funcref`/`externref` are value
types like `i32`, but opaque: no byte representation, so they cannot live in
linear memory. They can live in locals, parameters, globals, tables and (with
GC) struct/array fields. This is what makes tables the home of references the
way memory is the home of bytes.

**Two ways to point at a function.**

| | handle | reference |
| --- | --- | --- |
| what | integer index into a table | the value `ref.func` produces |
| storable in linear memory | yes | no |
| call | `call_indirect` (bounds, null, signature checks) | `call_ref` (statically typed) |
| needs a table | yes | no |
| Wasm version | MVP | typed function references, Wasm 3.0 |

The reference form exists for cross-module/host exchange without slot
management, calls without runtime checks, and filling tables from code
(`ref.func` + `table.set`). The handle form exists because C-style function
pointers must be integers stored in memory.

**Reference hierarchies** (heap types): `any`, `func`, `extern`, `exn`. They
are disjoint. Type Imports (Phase 1, not standard) adds
`(import "m" "T" (type $T (sub <heaptype>)))`: an abstract type with a bound,
validation-time only, same runtime behaviour as the top type.

Sources are listed in §10.

---

## 3. Current compiler state (verified against the tree)

- **TIR types.** `Type::Memory { memory_index }` and `Type::Global
  { global_index }` are per-declaration nominal type constructors
  (`tir/types.rs`). `Type::FunctionItem { func_index, type_args }` is the
  unique type of a named function; `Type::Function { params, result }` is the
  structural `fn(...) -> ...` type. `Type::Pointer { to, memory, ownership }`
  carries its memory.
- **Definitions.** `DefKind` has `Memory`, `Global`, `Function`, `Import`,
  `TypeSet`, `Trait`, etc. (`tir/defs.rs`); there is no `Table` or `Tag`.
  `MemoryDef` holds `trait_impl_index` and `size_assoc_type_index`.
  `GlobalDef` holds `trait_impl_index`, `value_assoc_type_index` and
  `mut_trait_impl_index: Option<_>`.
- **Synthetic impls.** `synthesize_memory_impl` / `synthesize_global_impl`
  (`tir/defs.rs`) create the item's trait impl and associated type at
  pre-scan; `resolve_memory_signature` / `resolve_global_signature`
  (`tir/signatures.rs`) fill them in. These are **shared between declared and
  imported items** (`AstNodeRef::Memory`/`ImportedMemory`,
  `Global`/`ImportedGlobal`); the imports principle in §1 is already how the
  code is structured.
- **Mutability picks the trait.** A `global mut` gets an extra `GlobalMut`
  impl through `mut_trait_impl_index`. This is the precedent for §4.3.
- **AST.** `ast::Item::Memory { id, attributes, name, size }` and an
  `ImportDeclaration::Memory` exist; `Global` and `Function` imports likewise.
  There is no `Table`, `Tag` or imported-type declaration.
- **Lang items.** `IntrinsicDefs` (`tir/defs.rs`) holds the compiler-known
  traits and primitives. `Memory`, `Global`, `GlobalMut` are defined in
  `std/main.wx`.
- **Name clash.** The attribute `#[tag = "..."]` marks lang-item traits. It is
  unrelated to the Wasm `tag` item proposed below; keep the two apart in
  diagnostics and docs.
- **Function pointers today.** Codegen builds one implicit `funcref` table
  (`builder.table` in `codegen/mod.rs`); a `fn(..)` value is an index into it,
  and calls lower to `CallIndirectSym`. The implicit table has no identity in
  source. (MIR/opt/codegen are disabled on this branch, see
  `tir-refactor-state` in memory.)
- **Coercion.** In the pre-rewrite checker (`tir/builder/types.rs`, which
  still uses the old `Type::FunctionItem { id, .. }` shape) a `FunctionItem`
  coerces implicitly to its `Function` type. The rewrite (`tir/types.rs`,
  `signatures.rs`) has the types but not the body-checking phase yet, so
  re-check where this rule lands before removing it (§5.7).

---

## 4. Design

### 4.1 Principle: identity becomes a type, shape becomes what it implements

Each item declaration creates a unique nominal type (identity). Its shape is
carried by the traits the compiler implements for it. Shape pieces are
sorted by how code uses them:

| Piece of shape | Mechanism | Examples |
| --- | --- | --- |
| a type code computes with | associated type | `Memory::Size`, `Global::Value`, `Tag::Result` |
| what operations exist | declaration modifier that selects a trait | `global mut` → `GlobalMut`; `table[func]` → `FuncTable` |
| plain numbers | attribute | `#[memory_limits(..)]`, `#[table_limits(..)]` |

Closed membership lists use `typeset` (a list of types, optional trait
supertraits). Typesets cannot contain traits, so there are no sealed marker
traits for reference families.

### 4.2 Tags

```wx
trait Tag { type Result; }
trait Exception: Tag where { Result = ! } {
    fn throw(self) -> ! { throw(self) }
}

tag ApplicationError(status: ErrorStatus) -> !;
impl Exception for ApplicationError;
```

- A `tag` is a struct (fields, constructed like one) plus a result type;
  `-> T` derives `Tag::Result = T`. This follows the derive-from-type rule
  used by `memory heap: u32;`.
- A tag item is therefore **not zero-sized**: it carries its payload. The
  zero-sized claim for items applies to the identity type, not to every item
  value.
- `Exception` is an explicit opt-in, since a tag is more general than
  "throwable".
- Exception tags and `exnref` are a separate extension (exception handling);
  see the opt-in rule in memory (`wasm-extensions-incremental`).

### 4.3 Tables

```wx
table[func]   handlers: u32;     // any function reference
table[extern] nodes:    u32;     // any host object
```

- The type after the colon is the index width `Size`, as for memory (`u64`
  needs table64, extension-gated).
- The bracket is the **kind** (`func`, `extern`; `any`, `exn` later). It is
  compiler-internal state of the table, shown in hover as part of the
  declaration. It is not an associated type and not a type the user can
  name; it selects the trait.
- Traits, implemented by the compiler for every table:
  `Table { type Size: PointerSize; ... }` plus exactly one of `FuncTable` or
  `ExternTable`. A table never implements both by construction.
- Limits go in an attribute, by analogy with `#[memory_limits]`.
  Name and field names are placeholders.
- A table is reusable for any funcref or any externref. It has no element
  signature; the slot type carries the use-site type, the same way a pointer
  type carries what a memory access reads.

Operations (`size`, `grow`, `fill`, `copy`, `get`, `set`, ...) are trait
methods over bodiless `#[intrinsic]` functions, as `Global::get` is.

### 4.4 Host (imported opaque) types

```wx
import "dom" {
    type Node: extern;
    fn create() -> Node;
    fn append(parent: Node, child: Node);
}
```

- `type Node: extern;` declares an opaque, nominal type supplied by the
  importer. It is the same kind of declaration as an imported memory or
  global; only the origin differs.
- The **kind bound is required.** It picks the Wasm reference type even
  without the Type Imports extension (`extern` → `externref`, `any` →
  `anyref`, `func` → `funcref`), so it cannot be a default.
- Baseline lowering: every opaque type of a kind lowers to that kind's
  top reference type; distinctness (`File` vs `Dir`) is enforced only by the
  wx checker. With the Type Imports extension enabled the same source emits
  `(type $T (sub extern))` and typed references. Source does not change.
- Principle: an imported-type declaration exists only for kinds that have no
  structural type of their own. `extern` and `any` have none. `func` already
  has `fn(A) -> R`.
- **No signature-bearing nominal func types.** Wasm cannot express them
  (Type Imports bounds are abstract heap types only) and wx already gets
  nominal wrappers from `struct Handler(T::fn() -> i32);`.
  `type X: func;` (opaque, uncallable) is kept for completeness and for
  future compatibility.
- Spelling `type[extern] Node;` (matching `table[extern]`) is an undecided
  alternative; the colon form mirrors Wasm's `sub`.

### 4.5 Handles and references

The same two layers as memory:

| | memory | table |
| --- | --- | --- |
| location, an integer carrying its container | `M::*u32` | `T::fn(i32) -> i32`, `T::Node` |
| value | `u32` | `fn(i32) -> i32`, `Node` (reference) |
| read | load | `table.get` |
| write | store | `table.set` |

- **Handle (`T::…`)**: an integer of the table's `Size`, with the table in its
  type. Storable anywhere an integer is, including linear memory
  (`M::*[nodes::Node]` is an array of `u32`). Always written with the `T::`
  qualifier when it sits in memory. Calling a handle lowers to
  `call_indirect`.
- **Reference (bare `fn(..)`, bare `Node`)**: a Wasm reference value. Allowed
  in locals, parameters, results and globals. **Not allowed** as the pointee
  of `M::*`, in an array/slice in memory, or in a struct that has a memory
  layout. Calling a function reference lowers to `call_ref`.
- `h.*` reads a slot (`table.get`), `h.* = r` writes it (`table.set`). A
  handle is the location; a deref reads a location.
- `Node` bare in a memory position is a hard error with a fix-it
  ("no memory representation; use `T::Node`"), not a silent change of
  meaning. No `extern` prefix at use sites: the declaration already carries
  the kind and a second marker could disagree with it.
- Imports pass and return references directly; no table glue. A table is
  needed only to keep a reference in memory-like storage (the wasm-bindgen
  pattern). Allocating slots (`insert`) is library code over `grow`/`set`
  plus a free list, not a primitive.
- A shared `func` table holds any function. A slot's static type is
  guaranteed by how slots are made: there are no raw indexes, and a
  `T::fn(i32) -> i32` can only come from a function item with that signature
  or another slot of that type. Null slots, out-of-range indexes and
  host-modified tables can still trap; `call_indirect`'s runtime check
  remains the backstop. State the claim at exactly that strength.

### 4.6 Function references: `as_ref()`

`ref.func` is **explicit**, never an implicit coercion and never a `Deref`
overload on items (deref reads a location; `ref.func` reads nothing, and the
effect profiles differ: `ref.func` is pure and cannot trap, `table.get` can).

```wx
trait Function {              // compiler-implemented for every function item
    type Ref;                 // the matching fn(A) -> R
    fn as_ref(self) -> Self::Ref { ref_func(self) }
}
#[intrinsic] fn ref_func<F: Function>(f: F) -> F::Ref;

local f = on_click.as_ref();  // ref.func
f(1);                         // call_ref
```

Same pattern as `Global::get`. The existing implicit `FunctionItem` →
`Function` coercion is removed. (`as_ref` is the chosen name; it differs from
Rust's `AsRef`.)

### 4.7 Lowering summary

| wx | Wasm |
| --- | --- |
| `on_click.as_ref()` | `ref.func` |
| call on a reference | `call_ref $sig` (typed function references) |
| call on a handle | `call_indirect $sig T` |
| `h.*` / `h.* = r` | `table.get T` / `table.set T` |
| `T.size/grow/fill/copy()` | `table.*` |
| `throw(tag_value)` | `throw $tag` |
| `type Node: extern` | `externref` (baseline) or `(sub extern)` import |

---

## 5. Implementation sketch

Following the existing shape of memory/global; names are placeholders.

1. **AST/parser.** `table[kind] name: size;` item and import form; `tag`
   item with struct-like fields and `-> T`; `type Name: kind;` inside import
   blocks; export of tables. Formatter and LSP follow.
2. **TIR defs.** `DefKind::Table`, `DefKind::Tag`, an imported-opaque-type
   def carrying its kind. `TableDef` mirrors `MemoryDef`: `trait_impl_index`,
   `size_assoc_type_index`, plus a second impl index for `FuncTable` /
   `ExternTable`, chosen at pre-scan the way `mut_trait_impl_index` is chosen
   for `global mut`. A `synthesize_table_impl` beside `synthesize_memory_impl`.
3. **TIR types.** `Type::Table { table_index }`, `Type::Tag { tag_index }`,
   a type for the imported opaque types, and a slot/handle type mirroring
   `Pointer { to, memory }` (e.g. `Slot { of, table }`).
4. **Signatures.** `resolve_table_signature` shared between declared and
   imported tables, as `resolve_memory_signature` already is.
5. **Memory-representability.** A compiler-internal predicate: numbers,
   pointers and handles qualify; references do not; structs/tuples qualify
   iff all fields do. Checked wherever a pointee, array element or slice
   element is validated, and in struct layout. The only user-visible place
   it surfaces is generic code over a pointee; an implicit bound with an
   opt-out (cf. Rust's `Sized`/`?Sized`) is the candidate.
6. **Lang items.** `IntrinsicDefs` gains `table`, `func_table`,
   `extern_table`, `tag`, `exception`, `function`; stdlib gains the traits
   and bodiless intrinsics (`table_get`, `table_set`, `table_grow`, ...,
   `ref_func`, `throw`).
7. **Coercions.** Drop `FunctionItem` → `Function`; add explicit
   `Function::as_ref`.
8. **MIR/opt/codegen** (when re-enabled). Reference types as new scalar
   kinds in `wasm::ScalarType`, locals/globals/params of those kinds,
   aggregate flattening that tolerates them, the table and element sections
   from declared tables, `call_ref`/`ref.func`, tag section. The implicit
   funcref table becomes an ordinary table (std-declared, compiler-populated)
   or goes away.
9. **Extension gating.** `call_ref`/typed references (Wasm 3.0), exception
   handling, table64 and Type Imports each follow the opt-in allowlist rule;
   without typed function references a bare `fn` value cannot lower and must
   be an error, or fall back to a table (open, §6).

---

## 6. Open questions

| Question | Candidate default |
| --- | --- |
| Nullability. Wasm has `ref null` and `ref`. | Non-null everywhere; `table.get` traps on null (shows as an effect). |
| Generic pointee bound for memory-representable types. | Implicit bound with an opt-out. |
| Gating of bare `fn` without typed function references. | Error; require the extension. |
| Fate of the implicit hidden funcref table. | Becomes an ordinary table item. |
| Marker for host handles in type position (`T::Node` reads like a path to an associated item). | Undecided. |
| Spelling of imported kind bound: `type Node: extern;` vs `type[extern] Node;`. | Colon form (mirrors `sub`). |
| `Memory::INDEX` doc comment says "the index in the generated module"; items carry a per-kind intermediate index, final index fixed at codegen after imports are counted. | Reword the doc comment. |
| Tags are not zero-sized; confirm the exact scope of the zero-sized claim in the docs. | Scope it to the identity type. |
| Reference-typed globals: initialiser rules for non-null references. | Follow Wasm's constant-expression rules. |

---

## 7. Decisions already taken (do not re-litigate without new information)

- `table[func]` / `table[extern]`: kind is a declaration modifier, not an
  associated type; the colon type is the index width.
- Tables hold a kind, slots carry the type. No element signature on the table.
- Always qualify handles with `T::` where they sit in memory.
- Typesets, not sealed traits, for closed lists; traits cannot be typeset
  members.
- Imported opaque types carry a required kind bound; no signature-bearing
  nominal func types; wrappers via structs.
- `ref.func` is explicit through `as_ref()`; no `Deref` for items.
- `.*` on a handle is `table.get` / `table.set`.

---

## 8. Later / out of scope

- `any` and `exn` reference kinds (add as accepted bracket words; `any` has no
  wx-created members until wx has GC types; `exn` may be needed for catching
  with the payload).
- Element-segment initialisers as item lists
  (`table[func] ops: u32 = [add, sub];`), which would give statically known
  slot indices. Speculative.
- Effect annotations on table operations (`table_get`, `trap` on bad
  index/null); see `effect-system.md` §7.
- Ownership and lifetime rules for host handles (Component Model `own` /
  `borrow` is the nearest prior art).
- Read-only vs mutable table split; Wasm tables are always mutable.

---

## 9. Evidence this design answers (thesis)

The chapter 2 study found language constructs for functions and globals but
mostly nothing for memories, tables and tags, and an imposed single-table
model for indirect calls. This design is the response to design questions
"Declared entities", "Several memories", "No imposed model" and "Declared host
boundary" (see `thesis/plan.md`). Claims in the thesis must stay at design
level for tables, tags and references until codegen is re-enabled.

---

## 10. Sources

- Type Imports and Exports, Overview:
  <https://raw.githubusercontent.com/WebAssembly/proposal-type-imports/master/proposals/type-imports/Overview.md>
  (Phase 1)
- Typed function references, Overview:
  <https://raw.githubusercontent.com/WebAssembly/function-references/main/proposals/function-references/Overview.md>
- Reference types, Overview:
  <https://raw.githubusercontent.com/WebAssembly/reference-types/master/proposals/reference-types/Overview.md>
- Component Model explainer (resource handles as table indices):
  <https://raw.githubusercontent.com/WebAssembly/component-model/main/design/mvp/Explainer.md>
- Haas et al., "Bringing the Web up to Speed with WebAssembly" (PLDI 2017),
  for the call_indirect CFI argument. Recalled from memory; check the exact
  wording before citing.
- The heap-type hierarchy and the "declared function references" rule for
  `ref.func` are from memory of the Wasm 3.0 spec, not read from it this
  session; verify against the spec before quoting.
