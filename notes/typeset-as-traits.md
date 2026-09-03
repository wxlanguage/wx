Good question to settle now, because the name sets the mental model. This concept — a constraint that admits a closed, compile-time-known set of types — exists in several languages, under two different framings.

## Prior art

| Language           | Construct                             | Syntax                                                                                    | Framing                                                                                                                                                                                   |
| ------------------ | ------------------------------------- | ----------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Go** (1.18+)     | **type set**                          | `type Integer interface { ~int8 \| ~int16 \| int32 \| ... }`                              | The set of types satisfying an interface *is* called its "type set" in the spec. A constraint interface can be nothing but a union of type terms. This is your `typeset`, almost exactly. |
| **Java** (17+)     | **sealed**                            | `sealed interface Shape permits Circle, Square {}`                                        | Closed set of *implementors*, named explicitly or restricted to the same module.                                                                                                          |
| **Kotlin / Scala** | **sealed**                            | `sealed interface Expr` (permitted subtypes = same file/package)                          | Same — "sealed" is the mainstream word for "closed implementor set." Both allow methods, so the set can carry behavior.                                                                   |
| **Nim**            | **type class** (union)                | `type SomeInteger = SomeSignedInt or SomeUnsignedInt`                                     | Built-in `SomeInteger`/`SomeFloat`/`SomeNumber` are literally defined as `or`-unions of concrete types. Called "type classes" but they're anonymous unions, not nominal traits.           |
| **C++20**          | **concept** (as disjunction)          | `template<class T> concept Integer = same_as<T,int8_t> \|\| same_as<T,int16_t> \|\| ...;` | A concept is a compile-time predicate; a finite disjunction of `same_as` is exactly a typeset. No sealing notion — concepts are structural.                                               |
| **Julia**          | **`Union{}`** + abstract-type tree    | `Union{Int8,Int16,Int32,Int64}`, or `x::Integer` over a sealed-by-convention hierarchy    | Closed set via `Union`; the `Number`/`Integer`/`Signed` tree is closed in practice.                                                                                                       |
| **Rust**           | **sealed trait** (pattern, no syntax) | `pub trait T: private::Sealed {}` + un-exported `Sealed`                                  | No first-class support at all — it's a known workaround.                                                                                                                                  |
| **TypeScript**     | union type                            | `type Id = number \| string`                                                              | Structural union, used as a constraint or a value type.                                                                                                                                   |

Two clusters: **"type set"** (Go, Nim, C++, Julia — *defined by enumerating member types*, integer-ish use cases dominate) and **"sealed"** (Java/Kotlin/Scala — *closed set of nominal implementors, usually carrying behavior*).

Your feature sits squarely in the first cluster. You enumerate primitive members; you don't (yet) attach behavior.

## What that implies for wx

**Keep `typeset`.** Reasons:

- It's an established term for precisely this — Go coined "type set" for "the set of types a constraint admits," and your construct is a Go type-set interface with the union spelled as a brace list.
- It's accurate about what the reader writes: `typeset Integer { u8, i8, ... }` is a set of types. The `{ ... }` body is unambiguous *because* it doesn't say `trait` — no one reads `{ u8, i8 }` as a method list.
- At the use site, `T: Integer` should make the reader think "closed set of types," even though the compiler now lowers it to a sealed trait. The name keeping that framing is a feature, not a leak.
- It's already in the codebase, the stdlib, and the tests.

A nice thesis framing falls out of the prior art: Rust forces the sealed-trait hack, Go bolts type sets onto interfaces; wx makes the common case (a closed set of primitives usable as a bound) a two-token declaration that desugars to ordinary trait machinery.

## The main alternative worth considering

Union-alias syntax, no new keyword:

```
trait Integer = u8 | i8 | u16 | i16 | u32 | i32 | u64 | i64
```

`|` is the Go/Nim/TS/Julia signal for "one of these," and `trait X = ...` reads as "X is defined by enumeration." Upside: visibly a definition-by-cases, and it hints that `trait` and this thing are the same kind of entity (which, post-desugar, they are). Downside: `trait` everywhere else in wx implies behavior, and `trait Integer = ...` with no body invites "where are the methods?" `typeset` sidesteps that by being its own word.

I'd only take the union-alias route if you also foresee general union types in the language; for an integer-set-only feature it's more syntax surface than `typeset`.

## Internal naming

Don't name the compiler-side concept `typeset` — name it **sealing**, with `typeset` as one *mode*:

```rust
enum Sealing {
    Typeset(Box<[TypeIndex]>),   // sealed by enumerating member types (today)
    // Permits(Box<[DefId]>),    // future: sealed by an explicit implementor list, Java-style
}
// Trait { ..., sealed: Option<Sealing> }
```

`typeset` is "sealed by type enumeration"; a future `sealed trait Foo permits Bar, Baz` for struct types would be "sealed by implementor list." Both share the coherence gate ("no external impls") and the closed-member list that operators / exhaustiveness / range-intersection consult. Leaving that seam now costs nothing and keeps `typeset` from becoming the name of a mechanism it's only one instance of.