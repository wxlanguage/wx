# wx Effect Tracking

A lightweight, local, opt-in effect system for wx. Not an algebraic effect
system — no handlers, no purity mandate. Every function is impure by default;
purity and bounded effects are opt-in annotations that the compiler checks and
the optimizer can trust.

---

## 1. Motivation

Modern software isn't pure, and forcing it to be (Haskell-style, effects-in,
purity-by-default) is unrealistic for a systems language. But *knowing* a
function is pure — or knows exactly which effects it may perform — is valuable
to both developers (contracts, reasoning) and the compiler (referential
transparency enables CSE, LICM, dead-call elimination, reordering, memoization).

wx inverts the usual default: **impure by default, pure by annotation.**
Unannotated code just works and carries no obligations. You annotate only the
boundaries where you want a guarantee. The system is *incremental* — adoptable
one function at a time — and *local* — checking a function never requires
inferring effects through the bodies of the functions it calls.

---

## 2. Core model: effects are sets

An effect annotation is an **upper bound on the set of effects a function may
perform**. There is exactly one concept — the *effect set* — and everything
else is a point on its lattice:

| Written      | Meaning              | Lattice position        |
|--------------|----------------------|-------------------------|
| `!()`        | empty set — **pure** | bottom                  |
| `!(trap)`    | the set `{trap}`     | an atom                 |
| `!(read, trap)` | `{read, trap}`    | a union                 |
| `!*`         | all effects          | top                     |
| *(absent)*   | top — identical to `!*` (§4)         | top                     |

Ordering is subset. `A ⊆ B` means a function with effect set `A` may be used
wherever `B` is permitted — so a pure function (`!()`) is usable anywhere, and
nothing is usable where `!()` is required unless it is itself pure. This
subtyping is the soundness backbone: it lets the optimizer key off the declared
bound.

**Top is open-world.** `!*` means *every* effect that could ever exist —
including host imports and markers not yet declared — never "the union of effects
known so far." So `X ⊆ !*` is unconditionally true for any `X`, and the checker
never expands `!*` into members. (If `!*` meant "all currently-known effects,"
adding a host import later would silently break every `!*` written before it.)

"pure" is not a separate keyword or concept. **Pure is just the empty set.**
Top is just the full set. A single root effect is just an atom. This is why
there is no `strict` keyword and no separate effect declarations — see §5.

---

## 3. Syntax

The effect set is part of the *arrow type*, so it sits after the return type as
a trailing `!(...)` clause:

```wx
fn add(a: i32, b: i32) -> i32 !()            // pure
fn log(msg: str) !(io)                        // may perform io
fn frobnicate() -> T !(io, alloc)             // may perform io and/or alloc
fn whatever()                                 // no annotation — impure (top)
```

This maps 1:1 onto the permission model the feature grew out of:

```
allow(*)        ==  (absent)  or  !*
allow(x, y, z)  ==  !(x, y, z)
allow()         ==  !()
```

The clause has exactly **two shapes** — there is no middle ground:

```
effect-clause  :=  "!*"             // top — all effects
                |  "!(" set ")"     // an explicit set: !() pure, !(a, b, …) bounded
```

`*` is a *distinct form*, never a list member — `!(io, *)` is ungrammatical, so
"these effects plus everything" (a meaningless state) cannot even be written. A
single-effect set still takes parens (`!(io)`, not `!io`): mandatory parens keep
one uniform "the parens hold the set" reading, and make growing a set a pure
insertion (`!(io)` → `!(io, trap)`) rather than a reshaping.

**Formatting.** One space before the clause (`-> i32 !(read)`, and `) !(read)`
when there is no return type). The sigil binds tight to its delimiter (`!(`,
`!*` — never `! (`), which is also what keeps it unambiguous with `!` as logical
negation. Inside the parens, format as an ordinary comma-list (`!(a, b)`).

> The `strict fn` spelling from early exploration is dropped: `strict` collides
> with strict-vs-lazy evaluation, and a leading keyword doesn't scale to the
> bounded case (`effect(io, alloc) fn` puts a growing list in front of the
> name). Trailing `!(...)` keeps the effect where it belongs type-theoretically
> and handles all three tiers with one mechanism.

---

## 4. Where effects come from

A function's annotation means one of two things, decided only by whether it has a
body:

```
no annotation         ⇒  top (!*)        — uniform: say nothing ⇒ assume anything
annotated, bodied     ⇒  checked bound    — callees' declared ⊆ declared (one hop)
annotated, bodyless   ⇒  declared bound   — ground truth; effects originate here
```

There is **one default, and it is top.** Omitting the clause always means `!*` —
for a stdlib intrinsic, a host import, or an ordinary body alike. "I haven't said
what this does" resolves to "assume it may do anything," everywhere. There is no
special leaf default to remember; leaf vs bodied only decides whether an
annotation, once written, is *checked* or *declared*.

### Bodied: the annotation is *checked*

A bodied function's annotation is verified — the union of its callees' *declared*
effect sets must be `⊆` its own declared set. One hop: it reads callees'
signatures, never their bodies.

```wx
fn clear(p: heap::*mut i32) !(write<heap>, trap) {
    store_i32(p, 0)          // store_i32 declares !(write<heap>, trap) ⊆ same ✓
}

fn helper() { /* ... */ }    // no annotation ⇒ top

fn caller() !() {
    helper()                 // ERROR: helper is top, !() forbids all effects
}
```

**Purity does not flow for free.** Effects propagate only through *annotated*
functions; an unannotated helper is top and makes its callers top. You opt into
propagation by annotating — the optimizer wins where people annotate, and nowhere
else. An acceptable cost for locality and simplicity.

### Bodyless: the annotation is *declared* — and this is where effects originate

A bodyless function — a stdlib intrinsic (`= intrinsic`, emits an instruction) or
a host import — has no body to check against, so its annotation is taken as
ground truth. This is the **only** place a real effect enters the system: every
bodied function can only inherit from what it calls, so all chains bottom out
here.

A bodyless annotation does one of two things:

**Mint a new effect — name itself.** A bodyless function whose annotation names
*itself* is a new primitive effect; the atom *is* the function identity.

```wx
fn trap() -> never !(trap);            // trap is a fresh atom — the effect IS this function
fn read<Mem: Memory>() !(read<Mem>);   // read<Mem> is a fresh atom, parameterized by Mem
```

**Reuse existing effects — name others.** A bodyless function whose annotation
names *other* effects produces exactly those, and mints no identity of its own.

```wx
fn store_i32<Mem: Memory>(p: Mem::*mut i32, v: i32) !(write<Mem>, trap);  // exactly {write<Mem>, trap}
fn div_s(a: i32, b: i32) -> i32 !(trap);                                 // exactly {trap}
```

`store_i32` is `{write<Mem>, trap}`, **not** `{write<Mem>, trap, store_i32}` —
the annotation is the *complete* set. It reuses `write`/`trap` (minted elsewhere)
rather than carrying a useless identity atom no caller would name.

**Mnemonic: self-annotate to mint, annotate-with-others to reuse.**

### Why this stays non-circular

`trap`'s annotation `!(trap)` names `trap` — that looks circular, but isn't,
because of the resolution rule for effect terms:

> **A bodyless function named in an effect term denotes *itself, as an atom*. A
> bodied function named in an effect term denotes its *declared bound*.**

So resolving `!(trap)` is one step: `trap` is bodyless → the atom `trap`, done.
You never expand a leaf's annotation to re-derive the leaf; the self-reference is
reflexive by construction, not a recurrence. This is the one line to state
explicitly in the spec — without it, someone later makes leaf-resolution expand
the annotation and reintroduces a fixpoint that never needed to exist. (It sits
comfortably in a demand-driven resolver: a bodyless callee is a terminal, not a
descent.)

### Failure mode, honestly

Because bare now means top *even for leaves*, forgetting to annotate a new
intrinsic yields top, not a tight guess — and top propagates. But it fails
**loud**: any `!()` function reaching the un-annotated leaf gets a compile error
(top ⊄ `{}`), so the mistake surfaces at the first purity boundary rather than
miscompiling. And leaves are few, stdlib-internal, and authored deliberately, so
the risk is concentrated and testable. In exchange the model has **one** default
instead of three, and the conservative direction (unknown ⇒ top) is the safe one
for everything uncharacterized — including foreign host imports, where "assume
anything" is exactly right.

---

## 5. No separate effect items — effects are just functions

There is no dedicated `effect` declaration. An effect is just a **bodyless
function that self-annotates** (`fn trap() -> never !(trap)`), which mints a fresh
atom whose identity *is* that function (§4). This keeps the "every effect is a
function" invariant with zero new syntax.

An **effect term** inside `!(...)` may be:

- a **root name** — a bodyless function, resolves to `{itself}` (`trap`, `fd_write`);
- a **function path** — resolves to that function's *declared* bound (one hop);
- a **trait path** — resolves to the join of the trait's method bounds;
- an **alias** — a library-defined name bundling a set (e.g. `io`).

Functions and traits **never introduce new atoms** — they only bundle existing
ones. This is what keeps the vocabulary from sprawling: writing `!(g)` doesn't
invent an effect, it points at the effects `g` already declares.

> **Function-refs inherit the *declared* bound, never the inferred one.**
> `!(g)` reads `g`'s signature and stops. If it followed `g`'s body, your
> contract would silently widen whenever someone edited `g` — an abstraction
> leak. So a function may appear in an allow-list only if it has an explicit
> annotation. Prefer named effects (`!(io, write)`, self-documenting) over
> function-refs (`!(read_file)`, opaque) for common cases.

### Two layers

Everything in this layer is a **bodyless intrinsic**. They differ along two
independent axes:

- **Lowering** — what code the call emits. `read`/`write`/`grow` lower to
  *nothing* (there is no "abstract write" instruction; writes only ever occur as
  concrete stores/fills/copies). `store_i32` lowers to its store instruction.
  `trap` lowers to `unreachable`.
- **Effect origin** — where the effect comes from. `trap`/`read`/`write`/`grow`
  are *their own* effect (bodyless, **self-annotated** — `fn trap() -> never
  !(trap)`). `store_i32` *reuses* others (bodyless, annotated with
  `!(write<Mem>, trap)`).

Two useful roles fall out of this:

- **Marker functions** — effect *identities*: bodyless, lower to nothing, are
  their own effect. Their job is to be *named* in `!(...)`. `read`, `write`,
  `grow`.
- **Operational intrinsics** — bodyless functions that lower to a real
  instruction and *declare* a set of markers. `load_i32`, `store_i32`,
  `memory_grow`.

`trap` sits in **both** at once: it is its own effect identity *and* it lowers to
a real instruction (`unreachable`). That's what makes it the one special case —
there is a distinguished 1:1 "trap now" instruction for the effect to attach to,
whereas `write` has no operational home and stays identity-only.

```wx
fn trap() -> never !(trap);                            // identity + lowers to `unreachable`
fn read<Mem: Memory>() !(read<Mem>);                   // identity only, self-annotated
fn write<Mem: Memory>() !(write<Mem>);                 // identity only, self-annotated

fn store_i32<Mem: Memory>(ptr: Mem::*mut i32, v: i32) !(write<Mem>, trap);  // operational
```

These self-annotations are **load-bearing**, not decoration: a *bare* marker
would be top (§4), so calling it — or naming it — would widen the caller to top
instead of contributing a precise atom. Self-annotating pins each marker to
exactly its own effect, which is what makes both the named-in-`!(...)` use and
the called-as-a-fence use (below) resolve to a single clean atom.

### Markers are callable — they are typed fences

Markers *may* be called; it is not a misuse. `read`/`write`/`grow` are
`() -> ()`, so calling one is a **runtime no-op that is still an effect-system
event**: it emits no code but contributes its effect to the enclosing function's
inferred set, exactly as reaching a real store would. (`trap : () -> never` is
the exception — calling it genuinely diverges, since it lowers to `unreachable`,
and the compiler treats everything after the call as dead.) Soundness is
unaffected: call `write()` inside a `!()` function and the `⊆` check fails with
an ordinary error, because the checker doesn't distinguish an effect that came
from a marker call from one that came from an instruction.

The direction matters: **calling a marker only ever *widens* the effect set — it
makes the optimizer more conservative, never more aggressive.** You cannot call a
marker to unlock an optimization (that is done by *narrowing*, i.e. annotating a
smaller set); you call one to *assert an effect the compiler can't otherwise
see*. That makes a marker call a **typed compiler fence**:

- **Volatile / memory-mapped reads** — a read whose value changes outside the
  program must not be CSE'd or hoisted; asserting `read<M>` forces each to
  observe fresh state.
- **Opaque effects** — memory touched through a path the type system doesn't
  track (some FFI channel); `write<M>()` asserts "a write happened here" so
  scheduling stays correct.
- **Ordering barriers** — a `write<heap>()` between two operations prevents the
  optimizer from reordering heap accesses across that point.

Because the marker is *typed and memory-parameterized*, `write<heap>()` fences
only heap-conflicting operations — pure code and `write<other_mem>` code still
move freely across it. It is a **fine-grained fence**, not a wall; a strict
improvement over a C-style blanket `asm volatile("" ::: "memory")` clobber.

---

## 6. Traits and effects

**Effects live on trait *methods*, not on the trait.** A trait is neither pure
nor effectful; each method carries its own bound. This dissolves the "what if a
trait mixes pure and effectful methods" question — there is no conflict.

```wx
trait Container {
    fn len(&self) -> i32 !()              // pure
    fn push(&mut self, x: T) !(write)     // may write
}
```

### An unannotated method is top — grouping requires bounded methods

A trait method signature is a **hole**, not a leaf: it's a contract some future
impl will fill, with no body or instruction behind it. So it takes the ordinary
default (§4) — **unannotated ⇒ top**, i.e. "the impl may do anything." This is
*not* the leaf mint: a leaf is a fully-known origin, a method is an unknown
contract, and the unknown case correctly defaults loose.

The consequence for grouping: a trait is a useful named effect group **only to
the extent its methods are annotated.** An all-unannotated trait is a group of
tops (i.e. top). You get precision out only where you put precision in — the same
"purity doesn't flow for free" principle, applied to contracts.

```wx
trait Io {
    fn fd_write(fd: i32, ptr: heap::*u8, len: i32) -> i32 !(fd_write);
    fn fd_read(fd: i32, ptr: heap::*mut u8, len: i32) -> i32 !(fd_read);
}
```

Now `!(Io)` = `{fd_write, fd_read}` — a real bundle — and every `impl` is checked
`⊆` its method's bound, so an impl can't secretly exceed it. **The trait is your
grouping mechanism; you need no separate effect-grouping primitive.** (Where do
`fd_write`/`fd_read` the effects come from? The host imports the impl actually
calls — the method bound is a *contract* that the impl's real import stays within
it.) This is why `io` is just a trait — or a plain `alias io = !(fd_write,
fd_read, …)` if your host boundary is free functions rather than methods. Either
reuses an existing language feature; neither is effect-system-specific.

### Import modules group effects too

An imported module is a named collection of bounded functions, so it groups
effects exactly as a trait does — **a module named in an effect term denotes the
join of its members' declared bounds.** No new mechanism; the grouping unit is
just an import block instead of a trait.

```wx
import "console" as console {
    fn log(message: heap::&[u8]) !(read<heap>, log);
}

fn print(message: heap::&[u8]) !(console) {   // !(console) = {read<heap>, log}
    console::log(message);
}
```

The grouping is **transparent**: `!(console)` expands to `{read<heap>, log}`, and
those atoms flow onward — a caller of `print` sees `read<heap>` and `log`, not an
opaque `console`. (This is the join reading, not a capability. `console` is
shorthand for its effects, not an opaque grant that hides them; keeping it
transparent means `⊆` needs no special module rules — it decomposes to atoms like
everything else.)

Same trade-off as any group: `!(console)` is a bound over the **whole
interface**, so adding an effectful import to `console` later silently widens
every `!(console)` annotation. When you want the contract pinned to what you
actually call, drop to the member projection `!(console::log)`, or name the atoms
directly (`!(read<heap>, log)`). Reach for `!(console)` when you genuinely mean
"as effectful as the whole console surface."

### A trait in an effect term = its method bounds, with `Self` supplied

Naming a trait in an effect term denotes the **join of its method bounds**. But
those bounds may mention `Self`, so the term needs a `Self` to project against —
two cases:

- **Self-independent bounds** (like `Io` — no `Self::` in any method effect): the
  projection is already ground, so **bare `!(Io)` works anywhere**, whoever `Self`
  is. The plain grouping case.
- **Self-dependent bounds** (like `Deref`, effect `read<Self::Mem>`): bare
  `!(Deref)` has a *free* `Self` and is **ill-formed alone** — the same error as a
  bare `Self::Target` out of scope. You must supply `Self`.

### Associated-type effects are substitution, not effect-variable polymorphism

A trait with an associated memory carries it into the effect:

```wx
trait Deref {
    type Mem: Memory;
    type Target;
    fn deref(&self) -> &Self::Target !(read<Self::Mem>);
}
```

`read<Self::Mem>` mentions the *same* `Self::Mem` projection the return type
already mentions, so it needs no new machinery: once `Self` is bound, `Self::Mem`
substitutes in lockstep with every other associated-type projection in the
signature. This is **type-argument substitution — the cheap kind** — *not* the
effect-variable polymorphism of `!E` callbacks (§11), where the effect
*constructor* is unknown. Here the constructor is fixed (`read`); only its
argument varies.

The governing rule: **an effect term may mention type parameters and
associated-type projections that are *in scope*; a *free* one is an error.**
`read<T::Mem>` inside `fn f<T: Deref>()` is fine (`T` is bound); `read<Self::Mem>`
with no `Self` is not.

Where `Self` comes from, and the spellings:

```wx
// enclosing trait Self — bare form works, Self is in scope
trait Smart: Deref {
    fn peek(&self) !(Deref);        // = !(Self: Deref) = read<Self::Mem>
}

// a generic param bound by the trait
fn first<T: Deref>(x: T) -> &T::Target !(T: Deref) { x.deref() }   // = read<T::Mem>
fn first<T: Deref>(x: T) -> &T::Target !(Deref)    { x.deref() }   // sugar: unique Self inferred
fn cnt<T: Deref>(x: T) !(T)                                         // terse: join over ALL of T's bounds

// concrete type — Self bound, effect ground
fn conc(p: FilePtr) !(<FilePtr as Deref>) { … }   // = read<FilePtr::Mem>

// single method — tighter than the whole trait
fn only<T: Deref>(x: T) !(T::deref)               // just deref's bound
```

- `!(T: Deref)` / `!(<T as Deref>)` — the `Deref` facet of `T`, explicit.
- `!(Deref)` — sugar, valid only when exactly one `Self` is in scope (enclosing
  trait, or a single generic param bound by `Deref`); ambiguous or absent ⇒
  error, name it.
- `!(T)` — the join over *all* of `T`'s trait bounds ("as effectful as `T`
  permits"); the terse common case, with `!(T: Deref)` as the narrowing.
- `!(T::deref)` — one method's bound, tighter than the whole trait.

### Checking generic bodies

Checking `first`: the body's `x.deref()` has effect `read<T::Mem>`, and the
declared bound `!(T: Deref)` *is* `read<T::Mem>`. The check
`read<T::Mem> ⊆ read<T::Mem>` holds **syntactically**, without knowing what
`T::Mem` concretely is — the payoff of writing body and bound against the same
projection. The rule the checker needs is one line: **compare effect terms up to
the type-equality you already use for associated types.** `read<A> ⊆ read<B>` iff
`A ≡ B` as types; `read<T::Mem> ⊆ read<heap>` stays unprovable generically
(correct) and resolves at monomorphization.

### The grouping trade-off, and the existential trap

`!(T: Deref)` grabs *all* of `Deref`'s methods' effects even if you only call
`deref` — the price of grouping over enumeration (sound, conservative). Drop to
`!(T::deref)` when you want it tight.

Do **not** give bare `!(Deref)` a silent existential meaning ("`read<M>` for some
unknown `M`", i.e. `read<_>`). `read<_>` can't be reordered against *any*
memory's writes, collapsing per-memory precision. It's occasionally what you
want, but it must be **spelled explicitly** (`read<_>`), never the accidental
meaning of an unbound trait name. Make the unbound case an *error* pointing at
either `!(T: Deref)` (bound) or `read<_>` (deliberately existential), so the two
intents never conflate.

> **Operator traits are load-bearing.** `a + b` → `Add::add`, `arr[i]` →
> `Index::index`, `*p` → `Deref::deref`, `*p = x` → `DerefMut::deref_mut`. If
> these aren't annotated in the stdlib, *no function containing arithmetic or
> indexing can ever be pure*, and the feature dies at desugaring. The stdlib's
> core traits must be meticulous: arithmetic `!()` (or `!(trap)` for
> overflow-trapping variants), `Index` `!(read<Self::Mem>, trap)`,
> `DerefMut` `!(write<Self::Mem>)`. User code needs no annotations unless it
> wants the guarantee to propagate.

---

## 7. The wasm effect vocabulary

The primitive effects (roots) mirror the effectful subset of wasm instructions.
Pure instructions (`add`, `mul`, shifts, comparisons, `wrap`, sign-extends,
`_sat` conversions) are `!()` and inline to instructions; only the effectful
ones are roots.

Marker names are **semantic** (`read`/`write`), not instruction names
(`load`/`store`) — consistent with `trap`/`host`, honest about the many-to-one
mapping (`write` also covers `memory.fill`/`copy`/`init`), and aligned with the
optimizer's own `readnone`/`readonly`/`readwrite` vocabulary.

| Effect     | Type        | Produced by (roots)                                                                 |
|------------|-------------|-------------------------------------------------------------------------------------|
| `trap`     | `() -> never` | `unreachable`; `div`/`rem` by 0 and signed overflow; non-saturating float→int `trunc`; **all loads & stores (OOB)**; `call_indirect`; table & bulk `memory.*`/`table.*` ops |
| `read<M>`  | `() -> ()`  | `*.load*`, `memory.size`, atomic loads                                              |
| `write<M>` | `() -> ()`  | `*.store*`, `memory.fill`/`copy`/`init`, atomic stores & RMW                         |
| `grow<M>`  | `() -> ()`  | `memory.grow` (mutates *validity*; distinct from `write` for bounds-check analysis) |
| `global_get<G>` / `global_set<G>` | leaf | `global.get`/`set` on a *mutable* global `G`; each intrinsic is its own effect (experimental — see §7) |
| host imports | (each own) | every imported call — the real I/O boundary                                       |

### Trap facts (settled)

- **`memory.size` cannot trap** — no operands, always succeeds ⇒ `!(read)`.
- **`memory.grow` cannot trap** — returns `-1` on failure (a value you check),
  otherwise the previous size ⇒ `!(read, grow)`, **no `trap`**.
- **Loads and stores trap** on out-of-bounds ⇒ they carry `trap`.
- **Pattern:** address-taking ops (loads/stores) can trap; size ops
  (`size`/`grow`) never do. `trap` distinguishes accessing memory *contents* at
  an address from querying/changing the memory's *size*.
- **One shared `trap` — no finer grain.** There is a single `trap` effect, not
  `trap.oob` / `trap.divzero` / etc. Knowing a function *may* trap is the effect
  system's job; knowing *why* is a question for the function's logic, not the
  effect annotation. The optimizer only needs "trap: yes/no" anyway, so the
  finer split buys nothing worth its cost at this stage.

### Host effects — the natural asymmetry

Instruction-effects need *shared* markers because many instructions collapse
onto one effect. **Host imports don't collapse** — each is distinct — so each
import can simply **be its own effect**, self-annotated with itself:

```wx
fn fd_write(fd: i32, ptr: heap::*u8, len: i32) -> i32 !(fd_write);
fn fd_read(fd: i32, ptr: heap::*mut u8, len: i32) -> i32 !(fd_read);
```

Left *bare*, a host import is **top** (§4) — the safe default for a foreign
function you've said nothing about. Self-annotate it to promote it into a
distinct, nameable effect that callers can allow specifically. Bundle several
under a trait or a convenience `alias io = !(fd_write, fd_read, …)` when listing
gets tedious — a library-defined set, not a compiler concept (§6). This is the
single recipe for any new effect — trap, a memory marker, or disk I/O: **a
bodyless function whose annotation names the effect.** There is no separate
machinery for module-external effects; the OS is just on the other side of a host
import.

### Globals and tables — `.get()`/`.set()` over singleton globals

> **Experimental — idea stage.** This is a candidate design, not settled. The
> rest of the doc doesn't depend on it; globals could equally stay as bare
> read/write atoms. Recorded here to capture the direction.

A wasm global is a single named mutable cell; `global.get` reads it,
`global.set` writes it. By the observability test (§9) `get` observes mutable
state and `set` mutates it — `read`/`write` over a *different kind of location*.
The design reuses machinery already in the doc rather than inventing markers:

**The intrinsics are their own effects — no separate `gread`/`gwrite` marker.**
`global_get`/`global_set` are bodyless, so by §4 a bodyless function named in an
effect term denotes *itself as an atom*. So the effect of a global read *is*
`global_get`, self-annotated like `trap`:

```wx
fn global_get<G: GlobalMut>()          -> G::Value !(global_get<G>);
fn global_set<G: GlobalMut>(v: G::Value)          !(global_set<G>);
fn global_get_const<G: Global>()       -> G::Value !();          // immutable ⇒ pure
```

Memory needs *shared* `read`/`write` markers because many instructions collapse
onto them; globals don't collapse (only `global.get` reads a global), so there's
no many-to-one and no marker is justified — the intrinsic names itself.

**Access goes through `.get()`/`.set()`, and the two mutability traits are
disjoint** — deliberately *not* a base/refinement hierarchy:

```wx
trait Global {                      // immutable — no relation to GlobalMut
    type Value;
    fn get(self) -> Self::Value !() {
        global_get_const(self)
    }
}

trait GlobalMut {                   // mutable — disjoint from Global
    type Value;
    fn get(self) -> Self::Value !(global_get<Self>) {
        global_get(self)
    }
    fn set(self, v: Self::Value) !(global_set<Self>) {
        global_set(self, v)
    }
}

global x: Global<i32> = 0;          // singleton: mints a type AND a value
global y: GlobalMut<i32> = 0;

fn test() {
    x.get();    // !()               — immutable, pure
    y.get();    // !(global_get<y>)  — mutable read
    y.set(1);   // !(global_set<y>)
}
```

Three things make this work, each already in the doc:

- **Method effects project through `Self`** (`!(global_get<Self>)`, not a free
  `G`) — the same associated-type projection as `read<Self::Mem>` (§6); it
  resolves to `global_get<y>` at the `y` impl.
- **Each `global` decl is a singleton** — it mints both a type (for
  `global_get<y>`) and a canonical value (to pass as `self`), like a `memory`
  decl. `global_get<x>` ≠ `global_get<y>` because `x`/`y` are distinct singleton
  types — per-global non-aliasing straight from the type system. (The index is a
  static identity, so the `<_>` existential never arises.)
- **The traits are disjoint on purpose.** A shared base `Global::get !()` that
  `GlobalMut` also satisfied would be *unsound*: generic-over-`Global` code would
  read a mutable, changing global as if pure. Keeping them unrelated closes that
  hole — at the cost that you can't be generic over "any global regardless of
  mutability."

**Why the `.get()`/`.set()` tax is worth it.** It makes global access
*syntactically visible*: a mutable global read is a method call, not a bare
identifier that looks exactly like a pure local. The effect then has a legible
source at the use site, and locals (pure, plain) read differently from globals
(effectful, method call). To keep ergonomics, let `+=` on a `GlobalMut` desugar
to `.get()`/`.set()` — the effect still flows (the desugaring calls the effectful
methods) while the surface stays `y += 1`, exactly as `Index`/`Deref` desugar to
effectful trait methods (§6).

**If disjointness ever bites** — you genuinely want "readable, whatever its
mutability" — the sound escape is a third trait `GlobalRead` that both implement,
whose `get` returns the *conservative* effect `!(global_get<Self>)` (never `!()`).
Reading an immutable global *through* `GlobalRead` then loses purity, which is the
safe direction; it doesn't reopen the hole because the shared bound is the *loose*
one, not the pure one. Not needed now.

**Tables** would follow the same shape parameterized by table identity: reads via
a `table.get` intrinsic (self-annotated `!(table_get<T>)`), writes via
`set`/`grow`/`fill`/`copy`, and `call_indirect` reading the table plus `trap`
(bad index / null / signature mismatch). Table accesses also trap on
out-of-bounds. Same experimental caveat applies.

---

## 8. Memory-parameterized effects

Effects that touch memory are indexed by a **memory identity**:
`read<M>`, `write<M>`, `grow<M>`. This is a *type-level* index resolved and
erased at compile time — **not a runtime call**; markers never execute.

The memory identity rides on the **pointer type** (`Mem::*i32`,
`Mem::*mut i32`), and the effect reads it off there:

```wx
fn load_i32<Mem: Memory>(ptr: Mem::*i32)      -> i32 !(read<Mem>, trap);
fn store_i32<Mem: Memory>(ptr: Mem::*mut i32, v: i32) !(write<Mem>, trap);
```

> **Pointer mutability and the `write` effect are complementary, not
> alternatives.** `*mut T` is a *capability* — "this pointer **may** be mutated
> through." The `write` effect is an *occurrence* — "this function **does**
> mutate." They are different axes, and both are load-bearing in permission-based
> code. A function can take, hold, and pass along a `*mut T` without ever storing
> through it, and then it needs **no** `write` effect — the capability flows but
> the effect doesn't appear until an actual store (via `store_i32` /
> `DerefMut::deref_mut`) is reached. So the type system carries the whole
> permission model *jointly*: pointer mutability says what a function is *allowed*
> to touch, effects say what it *actually* does with that permission. Neither
> subsumes the other.

**Payoff:** `write<A>` and `read<B>` don't alias by memory identity, so a
scheduler can reorder them — precision flat markers can't express. This is what
makes multi-memory first-class in the effect system.

**Cost:** it couples effects to the region/memory-parameter system — effects
become polymorphic over memory identities. That's the same *explicit generic*
mechanism as effect-generic callbacks (§11): a function generic over which memory
it touches carries a memory parameter, just as an effect-generic function carries
an `effect` parameter — both written by the author, neither inferred. If you're
building that anyway, it's nearly free; if you'd rather not, keep markers flat for
now. **Flat markers are a sound approximation** of per-memory markers (they treat
all memories as one), so starting flat invalidates nothing — you refine to `<M>`
when aliasing precision starts paying off in the optimizer.

Parameterizing effects by the memory type is **substitution, not effect-variable
polymorphism** (§6): the memory is an ordinary type argument the signature
already threads. When the memory genuinely isn't known statically — a dynamically
chosen memory — the wildcard `read<_>` / `write<_>` denotes "some memory,"
deliberately imprecise (it conflicts with *every* memory, so it can't reorder
against any memory access) and therefore always spelled explicitly, never
inferred and never the silent meaning of an unbound term.

### Memory as a trait (not a struct)

Memory is generic over pointer width (`u32`/`u64`), so it needs a type
parameter. Use a **trait**, not a generic struct:

```wx
typeset PointerSize { u32, u64 }

trait Memory {
    type Size: PointerSize;
}

memory heap: Memory where { Size = u32 };   // mints a fresh singleton type
```

A `struct Memory<Size>` **collapses every memory of the same width into one
type**, so `read<Memory<u32>>` couldn't tell two `u32` memories apart — defeating
the entire point of parameterizing the effect. A trait mints a **fresh singleton
type** per `memory` declaration, so `read<Heap>` and `read<Stack>` stay distinct
even at equal width. The trait also gives the nicer API (one associated `Size`,
not two threaded generics).

> A `memory` declaration mints both a **type** (for `read<heap>`, type position)
> and a canonical **value** (to pass as `mem` / `self`, value position). The
> compiler must treat it as both.

Intrinsics (corrected effect sets):

```wx
fn memory_size<Mem: Memory>(mem: Mem) -> Mem::Size !(read<Mem>);
fn memory_grow<Mem: Memory>(mem: Mem, delta: Mem::Size) -> Mem::Size !(read<Mem>, grow<Mem>);
```

---

## 9. Optimizer semantics

The declared bound is what the optimizer trusts. Key thresholds:

- **`!()` — pure / referentially transparent** → CSE, LICM, dead-call
  elimination, free reordering, memoization.
- **`!(trap)` vs `!()` — the totality line.** A pure-but-may-trap function is
  referentially transparent yet *pinned before a side exit* — reorderable only
  where a trap can't reorder observably. `!()` is freely movable.
- **`read` vs `write` — `readonly` vs `readwrite`.** A read-only function is
  reorderable against other reads and its result is stable within an unwritten
  window (enables CSE/hoisting); a writer isn't.
- **`grow` split from `write`.** A store changes *contents* at valid addresses;
  a grow changes which addresses are *valid*. Only `grow` invalidates an
  in-bounds proof — so keeping it separate lets ordinary stores not clobber
  bounds-check facts. Pairs directly with **bounds-check elimination**: proving
  an index in range lets you *downgrade* an `Index::index` call from
  `!(read, trap)` toward `!(read)` (the trap is discharged).

---

## 10. Soundness, errors, and escape hatches

A violated effect annotation is a **type error**, not a warning: the signature
is a claim the optimizer is about to act on, so the pipeline can't proceed with
it violated. (A linter-only mode is fine for style, but the moment codegen
relies on the bound, mismatch must be an error.)

For gradual adoption and FFI, provide an explicit, greppable **escape hatch** —
an `unsafe`-style cast that *asserts* a bound the compiler can't verify. The
default is "error"; the escape hatch is a marked way to say "trust me."

Default (§4): a **bodyless function with no annotation is top**, uniform with
bodied functions — say nothing, assume anything. This fails *loud* (any `!()`
caller reaching it errors at the purity boundary) and *conservative* (unknown ⇒
top is the safe direction, exactly right for foreign host imports). A new effect
is created deliberately, by a bodyless function that self-annotates (§4); the
compiler never invents one from omission.

---

## 11. Out of scope (for now)

- **Effect polymorphism over callbacks — explicit effect generics.** A
  higher-order function can be made *generic over its callback's effects* with an
  explicit **effect generic parameter**, kept separate from type generics in the
  generic list. Provisional syntax:

  ```wx
  fn map<type T, type U, effect E>(f: fn(T) -> U !E, xs: [T]) -> [U] !E
  ```

  The callback's effect set `E` is bound as a generic and flows to the result, so
  `map` is exactly as effectful as the `f` it is handed. **This is always the
  developer's explicit decision — never inferred or auto-derived.** ("What does
  `!E` mean here" is not a question the compiler can answer for you; it's a choice
  you make.) Being effect-generic is genuinely *different behaviour* from a fixed
  annotation, so it must be opted into deliberately.

  Effect generics are needed *only* when you want to be generic over the callback.
  Otherwise you annotate the callback's `fn`-type directly, with the same options
  as any effect set: leave it **unannotated** (the callback may perform any
  effects — top), or give an **explicit whitelist** (`f: fn(T) -> U !(io)`) so the
  passed function can't use anything outside that set. All three — generic,
  unconstrained, whitelist — are explicit choices the author makes; none is
  inferred. (Syntax provisional; the essential idea is that `effect` is its own
  kind in the generic list, alongside `type`.)
- **Effect abstraction / handling (algebraic effects).** A function that
  *absorbs* an inner effect and exposes a different, abstract one at a boundary
  (e.g. a `log` that does `write` internally but presents `!(logging)`). This is
  the algebraic-effects machinery deliberately kept out. The current model is
  **transparent propagation only** — effects surface unchanged all the way up,
  `!()` at the top means "traces to no impure leaf." The transparent model needs
  zero new machinery; the absorbing model is a real feature with real weight,
  deferred until a concrete need appears.

---

## 12. Open questions

- **Bounds-check interaction.** Does the elimination pass actually exploit
  `grow`-invalidates-proofs, or does it re-validate after any write anyway? If
  the latter, fold `grow` into `write`.
