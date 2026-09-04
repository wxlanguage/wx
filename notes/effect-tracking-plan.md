# Effect tracking — implementation plan (v3)

Supersedes the previous version of this file (see `git log -- notes/effect-tracking-plan.md`).
That one was written against [`effect-system.md`](./effect-system.md) (2026-08-18):
`does(...)` syntax, and a deliberately *local* model where a bodied function's
effects are only ever checked one hop against its direct callees, never inferred.
[`post.md`](./post.md) (2026-09-02) describes a different system — bracket syntax,
and full *inference* through the call graph — and that is what this plan builds.

v3 (2026-09-04) keeps v2's syntax, representation and origination rule intact
and changes three things, all in the direction of making the *unsettled* parts
unsettleable without a rewrite: §0c stages the work against a solver interface,
§3's unit of inference becomes an effect scope rather than a function, and §4
opens with a naive worklist instead of committing to Tarjan. §0c records why.

## 0. Syntax — settled

**The clause is square brackets: `[trap]`, `[*]`, `[]`.** Decided
2026-09-03, superseding the `does(...)` spelling in
[`effect-system.md`](./effect-system.md) §3; that document has deliberately
not been rewritten, so read its `does(x)` as `[x]` throughout.

Two reasons the earlier decision moves. First, the clause is already
unambiguous without a keyword to announce it: after a parameter list the only
legal continuations in wx are `->`, `{`, `;` and `where`, and `[` cannot begin
a type here — every slice and array carries an ownership sigil (`&[T]`,
`*[T; N]`), so there is no bare `[]T` to collide with, and the one other
construct opening with `[` (an array literal) is an expression, which cannot
appear in that position. One token of lookahead, no reserved word, no grammar
risk. Second, `effect-system.md`'s objection to going keyword-free was
specifically about *angle* brackets stacking against generics
(`read<Mem: Memory>()<read<Mem>>`) — an argument that never applied to square
brackets, which additionally carry the conventional reading of a *set*, which
is exactly what the clause is.

What that costs, recorded honestly: bare `[]` announces "deliberately pure"
less loudly than `does()` did. That was the keyword's real argument and it is
the one thing given up.

## 0b. The remaining open decision — inference or local checking

`effect-system.md` §4: absent annotation ⇒ `Top`, always; a bodied function is
only ever *checked* against its direct callees' declared sets. `post.md`:
absent annotation on a *bodied* function ⇒ infer from the body, transitively.

**Decided: inference.** Local checking only pays off once the world is
annotated, and the optimizer payoff (dead-call elimination, CSE, LICM across
calls) needs an answer for functions nobody annotated.

Two follow-on questions were settled 2026-09-04.

**A bodyless function with no effect clause is a hard error.** There is no
`Top` default. An earlier draft of this section claimed inference "gives a
real answer for `std/main.wx` on day one without touching a line of it" —
that was false: `std/main.wx` has 104 bodyless functions and none is
annotated, so under a `Top` default every one of them is `[*]` and nothing
infers anything useful. Making the clause mandatory forces that work up front
instead of leaving it as a footgun, and "an operation whose effects nobody
stated" is exactly what this system exists to rule out. See §2.

**A declaration is authoritative wherever it exists.** One rule, no boundary
case:

```
contract(f) = declared(f)                              if annotated
            = body closure over contract(callees)      otherwise
```

An intermediate revision of this plan (also 2026-09-04) tried the opposite —
in-package callers read the inferred set, the declared bound applying only
across a package boundary, per the working draft's line 744. That was
reversed, and the reason is worth recording because it is not a matter of
taste: it makes the package boundary an exception in the *summary-selection
rule*, and nothing about crossing a package makes a body less knowable in
principle. It is just where we chose to stop looking.

Under the rule above the boundary stops being an exception and converts into
a separate rule you want anyway, which the draft already states: **public
items must carry an explicit effect bound**. Then there are two simple rules
instead of one rule with a carve-out:

```
selection:   declared if present, else inferred
annotation:  public items must declare
```

and the cross-package behaviour falls out rather than being carved in.

The cost is precision: an unannotated caller of a deliberately-broad
annotated function inherits the breadth.

```wx
fn broad() [trap] { }     // annotated, actually pure
fn caller() { broad(); }  // contract = [trap], not []
```

That cost is confined to the *type system*, which is the part that exists for
the developer's benefit. The optimizer does not pay it — see "two closures"
in §1. So annotations behave predictably for people, and codegen still gets
the real facts.

Two consequences that follow directly:

- **Annotations cut the graph for propagation.** `contract(f)` is constant for
  an annotated `f`, so nothing depends on its body. Its *own* body closure is
  still computed, because that is what the `⊆ declared` check compares.
- **`catch` exhaustiveness reads contracts**, so a `catch` over a
  broadly-annotated callee must handle what the contract admits rather than
  what the body currently does. Same discipline as checked exceptions.


## 0c. Staging — what is settled, and what the settled part must not assume

The rest of this plan is ordered by *confidence*, not by dependency. Three
layers, and the boundary between them is chosen so that everything still
under exploration sits strictly above a fixed interface.

```
  L1  atoms + interned sets                    settled — build now
  L2  origination + storage on `Function`      settled — build now
  L3  scope collection (the effect forest)     settled in *shape* — build now
  ───────────────────────────────────────────  ← the interface that matters
  L4  the solver                               open — build the naive one
  L5  what effects mean elsewhere              open — build nothing
```

**L1–L3 are safe to build because none of them knows how the fixpoint is
computed.** Phase 3 ends by handing the solver a set of equations; the solver
hands back one resolved `EffectSetId` per scope. Every option we have looked
at — naive worklist to fixpoint, Tarjan condensation with a per-SCC worklist,
per-effect backwards reachability with handler-cut edges, symbolic SCC
solving — consumes exactly that input and produces exactly that output. So
the solver is one function behind one signature:

```rust
fn solve(
    scopes: &EffectScopeForest,       // L3's output
    effects: &mut EffectInterner,
    types: &mut TypeInterner,         // §3: reducing an edge substitutes
) -> Box<[EffectSetId]>;              // indexed by EffectScopeIndex
```

Swapping algorithms is deleting a file and writing another. That is the whole
scalability argument, and it is why the solver question does not have to be
answered before work starts.

**L5 is where the genuinely unresolved language design lives** — `fx` effect-set
parameters, effects in function types, `catch`/`tag`, dyn dispatch, MIR/opt
consumption. None of it is load-bearing for L1–L3 *provided* L1–L3 avoid the
three assumptions below, each of which is cheap to avoid now and expensive to
retract later.

### The three assumptions L1–L3 must not make

**(a) "A function's effect set is one flat accumulator."** *(See also §3b:
the scope structure this argues for is additive, but its evaluation timing is
not — an open defect.)* It is not, once
`catch` exists, because `catch` subtracts over an arbitrary sub-expression
while the handler arms sit *outside* that subtraction. The unit of inference
is therefore an **effect scope**, not a function; a function is just its root
scope. With no `catch` in the language today every function has exactly one
scope, so adopting the scoped shape now costs a `Vec` with one element in it
and removes the only rewrite this plan currently admits to (old §7). See §3.

**(b) "Every function in an SCC has the same effect set."** True under union
alone, false under subtraction, so it is false the moment `catch` lands:

```wx
fn b() [B];
fn f() { b(); g(); }
fn g() { { f(); } catch B; }
```

`effects(f) = {B} ∪ effects(g)` and `effects(g) = effects(f) − {B}`, whose
least solution is `f = {B}`, `g = {}` — two members of one SCC that differ.
Collapsing the SCC to a single union would give `g = {B}` and quietly discard
the entire point of the `catch`. So Tarjan may be used to get an *evaluation
order* (the condensation is still a DAG), but the per-component step has to be
an iteration to fixpoint rather than a single union. See §4.

**(c) "One stored set is enough."** Two are: what the source wrote
(`declared`) and what the body closes over (`inferred`). What callers see is
`declared ?? inferred`, derived rather than stored. A third *closure*
(`precise`, annotations ignored, for the optimizer) is a real field but only
once something reads it. See §1's "two closures".

### What monotonicity we are relying on

Subtraction is by a filter that is **constant** — fixed by the `catch` pattern
list at parse time, never itself a solver output. A `_` arm handling any
exception is not an exception to this: it is the pattern set `[throw<_>]`
(§1d), so a filter is always just an `EffectSetId`. An earlier revision had a
dedicated `HandlerFilter::AllExceptions` variant here; wildcards made it
unnecessary. So every equation is
monotone in the solver's variables, the system has a least fixed point, and
iterating upward from `∅` finds it. This is the single property that makes
*all* of the L4 candidates valid, and it is worth protecting deliberately: a
future feature that lets the handled set depend on inference (an effect
alias resolved from a bound, say) would break every one of them at once.

---

---

## 1. Representation

Optimised for the actual shape of the data: a program has on the order of tens
of distinct effects total, and a function has 0–3.

```rust
// crates/wx-compiler/src/tir/effects.rs — new file

/// One effect instance: the interned `Type::FunctionItem` that is its
/// origin plus type arguments. A newtype rather than a bare `TypeIndex` so
/// the two can't be confused at a call site, and so the representation can
/// change later without moving any of them. See §1b.
pub struct EffectAtom(TypeIndex);

/// Dense index into `EffectInterner::sets`. `EMPTY`/`TOP` are pre-interned,
/// same convention as the pre-interned `TypeIndex` slots.
pub struct EffectSetId(u32);
impl EffectSetId {
    pub const EMPTY: Self = Self(0);   // pure
    pub const TOP:   Self = Self(1);   // `[*]` — sentinel, never a member list
}

pub struct EffectInterner {
    /// `sets[0] = []`; `sets[1]` is the unused `TOP` slot.
    /// Every other entry is **sorted ascending and deduped**.
    /// Atoms need no pool of their own — `TypeInterner` is already it.
    sets: Vec<Box<[EffectAtom]>>,
    set_lookup: HashMap<Box<[EffectAtom]>, EffectSetId>,
}
```

Why this and not the obvious alternatives:

- **The atom is the interned type index itself, under a newtype.**
  Comparison, hashing and set membership collapse to `u32` work, and
  `substitute_type` handles monomorphisation of parameterized effects with no
  new code, because the atom *is* a type index. §1b is the full argument.
- **Sorted `Box<[EffectAtom]>`, not `BTreeSet`, not a hash set.** At n ≤ 3 a
  tree or a hash is pure overhead. Sorted (unlike the previous plan, which
  deliberately left sets unsorted) is what makes union and subset a single
  linear merge, and — the real reason — it makes sets *structurally
  comparable*, which is the precondition for interning them.
- **Interning the set too.** This is the piece that makes everything else
  cheap. An entry in `EffectAnalysis::inferred` is 4 bytes. "Is this call pure?" is
  `id == EffectSetId::EMPTY`. "Do these two functions have the same effects?"
  is a `u32` compare. Most functions in a real program share one of two sets
  (`[]` and `[trap]`), so the pool stays tiny and the solver below mostly
  hits `set_lookup` rather than allocating.
- **No `SmallVec`.** Nothing here needs it: the interned slices are heap-owned
  exactly once, and the only hot short-lived buffer is the per-body
  accumulator below, which is one `Vec` reused across the whole body.

The escape hatch if effect sets ever get big: `EffectSetId` can later resolve
to a `u64` bitmask (`union` = `|`, `⊆` = `a & !b == 0`) with a `Box<[u64]>`
fallback. That needs atoms numbered densely, which `TypeIndex` is not — it is
sparse across the whole type pool, so a mask keyed by it would be as wide as
the program's type count rather than its effect count. Densifying is part of
*doing* that optimisation, not a prerequisite to be paid now: assign dense ids
inside `EffectInterner` at that point. Nothing blocks it as long as atoms stay
opaque and set construction stays behind the interner, which is the actual
invariant to hold.

Optional, add only if profiling asks for it: memoise
`HashMap<(EffectSetId, EffectSetId), EffectSetId>` for union.

### Storage on `Function`

`tir::Function` (`tir/mod.rs:1914`) gets **one** field, next to `result`:

```rust
/// What the source wrote. `None` only for a *bodied* function: on a bodyless
/// one the clause is mandatory (§2), so `None` there is a reported error.
/// Kept so wx-fmt and the LSP round-trip the annotation rather than the
/// resolved set.
pub declared_effects: Option<Spanned<EffectSetId>>,
```

That is the only *signature* data among the four values effects need — it is
resolved in Phase 2 from the AST clause exactly like `params` and `result`,
and wx-fmt and the LSP read it without running any analysis at all.

Everything else is analysis output and lives with the analysis, in one field
on `TIR`:

```rust
pub struct EffectAnalysis {
    interner: EffectInterner,

    /// **The constraint**, by `FunctionIndex`. Extracted by one walk of the
    /// body (§3), then immutable: it holds *unreduced* callee references,
    /// which is what makes it a term rather than a set. Stable across every
    /// solver iteration — only the solution changes.
    terms: Box<[EffectTerm]>,
    /// **The solution**, by `FunctionIndex`. Each body's closure over its
    /// callees' contracts, from solving `terms`. Kept even when the function
    /// is annotated — that is what the `⊆ declared` check and the "never
    /// performed" lint compare against.
    inferred: Box<[EffectSetId]>,
}
```

Two reasons this is not merely tidier:

- **`Function` stays one phase's data.** Nothing about Phase 3.6 has a value
  to put on a `Function` at the moment one is constructed, so fields there
  would be placeholders waiting to be overwritten. (`body: Option<FunctionBody>`
  is already this shape and is already a wart; not adding three more is how
  that does not get worse.)
- **It makes the solver's borrows disjoint.** With the values on `Function`,
  the fixpoint would read `functions[g]` while writing `functions[f]` — a
  mutable borrow of the slice it is reading, needing `split_at_mut` or index
  gymnastics on the hot path. Split, the reads are
  `&items.functions[g].declared_effects` and the writes are
  `&mut analysis.inferred[f]`.

`contract` moves with the analysis — `analysis.contract(func_index, &items)`
rather than a method on `Function`. Marginally less convenient, and more
honest: a contract is an analysis concept, not a property of a declaration.

`contract` — what callers, coercion, `catch` exhaustiveness and diagnostics
see — is **derived, not stored**:

```rust
impl EffectAnalysis {
    pub fn contract(&self, f: FunctionIndex, items: &ItemRegistry) -> EffectSetId {
        items.functions[usize::from(f)]
            .declared_effects
            .map_or(self.inferred[usize::from(f)], |d| d.inner)
    }
}
```

An earlier revision stored it as a third `contract_effects` field. That was
redundant in the annotated case (it duplicated `declared`) and actively
harmful: writing the resolved contract over an annotated function's body
closure destroyed the one value the check and the lint need. A stored branch
result, saving a single `Option` test, at the cost of the information the
diagnostics run on.

`precise` is a genuinely separate propagation and gets its own array on
`EffectAnalysis` when it lands — it cannot be derived from these. See "two
closures" below.

### Why the term is stored

A fixpoint *iterates*. If a function's equation were "walk the body", every
worklist visit would re-walk the whole body. The term is the extracted
constraint: small, syntactic, and **stable across iterations** — only the
solution array changes. That separation is the reason constraint extraction
exists at all, and it is what the ideas note was reaching for by splitting
"effect expression" from "solver".

It buys a second thing, which §3b needs: evaluating a generic function at a
particular substitution is *substitute into the term, then solve* — a handful
of atoms — rather than re-walking its body per instantiation.

`EffectTerm` is representationally just an `EffectSetId` in the MVP, since
with no `catch` there is no subtraction and the term is a flat set of atoms,
some of them unreduced calls (§3, "one list, not two"). It grows the
subtraction structure when `catch` lands:

```rust
type EffectTerm = EffectSetId;                  // today

struct EffectTerm {                             // once catch exists
    atoms: EffectSetId,
    children: Vec<(EffectTerm, EffectSetId)>,   // (subterm, handled)
}
```

which is exactly the `EffectScope` type in §3. That type was never wrong;
what was wrong was assembling it by hooks during Phase 3, and implying the
MVP needed its subtraction half. It is the term, produced by one walk after
Phase 3.

### Two closures

The split is the point of §0b's decision, so it is worth stating exactly.
There are two propagations over the same graph, differing only in what a call
edge contributes:

```
inferred(f) = ⋃ contract(callee) over f's body       stored
contract(f) = declared(f) ?? inferred(f)             derived

precise(f)  = ⋃ precise(callee)  over f's body       stored, later (§7)
```

`inferred` and `precise` are the same walk over the same graph; they differ
only in which summary a call edge contributes — a callee's contract, or a
callee's precise set with every annotation ignored. Both are computed for
every bodied function; `contract` is one `Option` test on top.

The check compares the stored body closure against the declaration, so it
propagates **contracts**:

```
inferred(f)  ⊆  declared(f)
```

Checking against contracts rather than against `precise` is what makes the
check modular. If `f` were validated using what `g` *happens* to do today,
`g` legally widening within its own declared bound would break `f` — which is
exactly what a contract exists to prevent.

`precise` is not user-visible in any way: no diagnostic, no type, no coercion
consults it. That is what makes it safe to add later without changing a single
observable behaviour, and it is why the type system can afford to be
imprecise in §0b's `broad()` example while codegen is not.

Note there is no per-edge boundary logic anywhere. A previous revision
selected the summary per call site depending on package and body availability;
§0b's rule removed that, and reducing an atom is now one unconditional lookup.

Neither stored field is redundant. `declared_effects` is what the source said
and what wx-fmt must round-trip; `inferred` is what the body does
under its callees' contracts, which is what both diagnostics compare. The
lint that answers "this declares `[trap]` but never traps" wants
`precise` once it exists, since `inferred` is inflated by any broad
annotation below it — which is why that lint is worth having even though it is
demoted from a default warning.

The interner itself lives on `TIR` next to `types`, since MIR, the LSP and
wx-fmt all need to resolve an `EffectSetId` back to names after `TIR::build`
returns.

---

## 1b. Effects and the type system

Two separate questions get conflated easily, and they have opposite answers.

> **Can an effect *atom* reuse `TypeIndex`?** Yes — and it should.
> **Should `FunctionItem` carry effects?** No — and it must not.

### The atom is an interned `Type::FunctionItem`

An effect atom and a function item are the same data: a `DefId` plus a list of
type arguments. `throw<ApplicationError>` and the item type of `throw`
instantiated at `ApplicationError` are not merely similar shapes, they denote
the same thing — post.md's whole premise is that an effect *is* a function.

The payoff is not saving a struct. It is `substitute_type`
(`generics.rs:934`), which already walks `FunctionItem { id, type_args }`,
substitutes each argument, and re-interns. That is exactly the operation
monomorphisation needs to turn a schema `[read<Mem>]` into `[read<heap>]`
(§7), and it is subtle enough — nested projections, `AssocTypeProjection`,
change-tracking to avoid re-interning — that a parallel `substitute_effect`
would be a duplicate of tested code that then has to be kept in sync. Reusing
the variant makes the §7 substitution story *literally the same code path*
rather than "the same shape of code".

Nothing else in the compiler mistakes such an entry for a value type:
`WasmScalar::try_from` already returns `Err(())` for `FunctionItem`
(`tir/mod.rs:1821`), and `Layout` never sees one. **Do not add a
`Type::Effect` variant** — `Type` is matched exhaustively in many places, and
a new variant costs an arm in every one of them for no gain.

So the atom is the type index, under a newtype that keeps the two from being
passed for one another:

```rust
pub struct EffectAtom(TypeIndex);
```

There is deliberately **no second pool and no re-interning**. `TypeInterner`
is already the atom pool: atom identity is `(origin, args)`, which is exactly
what interning a `Type::FunctionItem` establishes, so two distinct atoms
cannot collide and an atom cannot be interned twice. Substituting one is
`substitute_type` and nothing else — a side table would add a
lookup-or-insert round trip on the one operation §7 leans on hardest.

Sets do get their own interner, for a reason that does not apply to atoms:
a set is not a type, and interning one requires a sorted canonical form that
`TypeInterner` has no reason to know about.

The one real consequence of sharing the entry: `TypeFormatter`
(`tir/mod.rs:2256`) prints a `FunctionItem` as `fn name<...>`, which is wrong
for an effect — `[trap]`, not `[fn trap]`. Effect sets need their own small
formatter. Cheap, but it has to exist before the first diagnostic ships.

### `FunctionItem` must not carry effects

It already stores no parameters and no result. It stores `id` and `type_args`
because those *determine* the signature, which is recovered on demand by
`substitute_type(functions[id].signature_index, type_args)`. Effects are the
same kind of derived property, recovered via `contract()` (§1). Adding a declared-effects field would be storing a copy of something
the `DefId` already names.

The argument that settles it is soundness, not tidiness. `FunctionItem` is
interned, so its fields *are* its identity. A function's effects are not known
until the solver runs in Phase 3.6, but its item type is interned all over
Phase 3 — every `foo` reference, every unification, every coercion result.
If effects were part of `FunctionItem`, either

- they are the *declared* set, and an unannotated function has no answer in
  Phase 3; or
- they are the *inferred* set, and the item type of every unannotated
  function changes identity at Phase 3.6, invalidating every type interned
  from it during Phase 3.

Nominal reference, structural type: `FunctionItem` is nominal and therefore
timing-independent, `Type::Function` is structural and therefore carries the
set. That split is what makes inference-after-Phase-3 possible at all.

### `tir::FunctionSignature` carries the set; MIR erases it

```rust
pub struct FunctionSignature {
    items: Box<[TypeIndex]>,
    params_count: u32,
    /// Upper bound. Part of type identity: `fn() [] -> ()` and
    /// `fn() [trap] -> ()` are different types related by coercion.
    effects: EffectSetId,
}
```

A fn pointer has no `DefId` to look anything up from, so this is the one place
the set has to be stored. `substitute_type`'s `Type::Function` arm
(`generics.rs:884`) has to substitute the effect set too, not just `items` —
easy to miss, and silently wrong in exactly the generic cases §7 cares about.

**MIR's `FunctionSignature` must *not* gain the field.** Effects are erased at
`lower_type_index`/`intern_tir_function_type` (`mir/mod.rs:1410`). This is a
codegen correctness requirement, not a size optimisation: `call_indirect`
demands an exact WASM functype match, so `fn() [] -> i32` and
`fn() [trap] -> i32` must collapse to one entry in the type section. Keeping
effects out of MIR's signature makes that automatic.

### Coercion is where this has to be designed up front

Today the only function-type coercion arm is `FunctionItem → Function`
(`types.rs:64`) and it is a *whole-index equality*:

```rust
self.substitute_type(generic_sig, &type_args.clone()) == b
```

That breaks the moment `effects` joins `FunctionSignature`, because the
substituted signature is now index-unequal to the target whenever the sets
differ — which is the entire point. Both arms have to split structural
equality from the effect relation:

```
params/result   equal            (as today — invariant, sound, less permissive)
effects         subset (⊆)       (new — the coercion axis)
```

and a `(Function, Function)` arm has to be *added*, because none exists at
all right now. Without it `fn() [] -> i32` would not be assignable to
`fn() [trap] -> i32` even though that is post.md's headline coercion.

Three further sites, each needing the relation rather than equality:

- **`unify`** (`types.rs:75`) — `if c { f } else { g }`. The join of two
  function types is structural equality plus the *union* of their effect sets.
- **`TypeComparison`** (`type_compare.rs:749`) — trait impl signature
  matching. Here the relation is impl ⊆ trait bound, per post.md's "Traits".
  Equality would reject a pure implementation of a `[throw<E>]` method, which
  is the case the design most wants to accept.
- **Polarity.** Effects are covariant in return position and contravariant in
  parameter position: `fn(fn() [trap] -> i32) -> i32` accepts a callback
  *bound* argument. Params are compared by equality today so it does not bite
  yet, but `recurse!` should thread a polarity flag from the start — retrofitting
  variance into a recursive comparator afterwards is the expensive version.

### The ordering problem, and why obligations solve it

This is a phase circularity, and effects are the only thing in wx that causes
one. Parameters and results are fixed in Phase 2, so Phase 3 normally has
complete information when it checks a coercion. Effects are inferred from the
body, making them an output of Phase 3 that Phase 3 also consumes:

```
Phase 2    signatures           declared effects known
Phase 3    bodies + coercions   needs effect sets ---+
Phase 3.6  solver               produces them <------+
```

It bites wherever a function value meets a function *type* — an annotated
local, a parameter of `fn` type, a return position, a struct field — which is
exactly the case inference exists for, since an annotated callee would already
have been decidable in Phase 2.

Three fixes that look reasonable and are not:

- **Check inline.** The set is not there yet: Phase 3 runs in parse order, so
  `fn main() { local f: fn() [] -> () = helper; }` is routinely walked before
  `helper`.
- **Walk callees first.** No such order exists in general — the dependency can
  be cyclic (`fn a() { b(); local f: fn() [] -> () = b; }` with
  `fn b() { a(); }`). Same reason the solver is a fixpoint pass and not a
  traversal.
- **Check against the partially accumulated set.** The dangerous one: sets only
  grow, so a check against a partial set can pass and later become false —

  ```wx
  fn main() { local f: fn() [] -> () = risky; }  // risky empty so far -> accepted
  fn risky() { trap(); }                          // now [trap]; check already passed
  ```

  A silent false accept, in the common case, with no diagnostic.

Deferring by patching the type afterwards is not available either: types are
interned, so their fields *are* their identity, and mutating an `EffectSetId`
inside an interned `Type::Function` would change its hash and break the
interner.

§0b's rule shrinks this problem considerably: for an **annotated** source
`contract` is `declared`, known at the end of Phase 2, so the coercion is
decidable inline. Only an *unannotated* source needs deferral — and since
`pub` items must be annotated (§5), most coercion targets that cross an API
are decidable immediately.

For the rest, typing and validation come apart. In every one of those sites
the target type is written down, so the expression's type is known regardless
of the answer — only legality is pending. So Phase 3 records what it cannot
yet decide:

```rust
struct EffectObligation {
    /// An atom, not a set — a generic coercion has to keep its type
    /// arguments, same reason `calls` does (§3).
    source: EffectAtom,        // FunctionItem { id, type_args }
    bound: EffectSetId,        // from the annotation: already known
    span: SourceSpan,
}
```

Discharge is `subst(contract(source.id), source.args) ⊆ bound`, run in Phase
3.6 beside the `inferred ⊆ declared` check (§4) — same pass, same diagnostic
shape, no extra traversal, and full precision because every set is final by
then. This is the familiar trait-obligation pattern.

Trait conformance needs none of this: `check_trait_conformance`
(`traits.rs:88`, Phase 3.5) compares impl signatures *after* the solver has
run, so impl ⊆ trait bound can be checked directly. Ordering solves that case
for free — one more reason 3.6 goes before 3.5 rather than after.

The residual case is `unify` with no expected type — `if c { f } else { g }`
where neither function is annotated. There the *type itself* depends on
effects, so it cannot be deferred. Use `TOP` for the joined set: sound,
because an upper bound is always safe to widen, and imprecise only for an
unannotated if/else over two function references with no expected type, which
the `expected_type` propagation already in `body.rs` (`scope.expected_type`,
`body.rs:404`) keeps rare. Tightening it later means introducing a deferred
set variable, and it is confined to `unify` — which is the same mechanism
`fx` parameters need anyway (§7), so it is a down payment rather than a
detour.

Worth recording that this entire mechanism is a cost of choosing inference
(§0b). Under the local-checking model, where an absent annotation means `Top`,
every function's effects are known at Phase 2 and none of it exists.

---

## 1d. Wildcard arguments — `throw<_>`

Decided 2026-09-04. Designed now, shipped with exceptions; **not in the MVP**,
which has no parameterized atoms for a wildcard to range over.

An atom argument may be a wildcard, so `throw<_>` denotes *any* throw. This
is not a `catch`-specific device: it is available anywhere an effect set is
written, including declared bounds and `fx` bounds.

```wx
fn f() [throw<_>];                  // may throw anything
fn apply<fx E: [throw<_>]>(..);     // E may contain only throws
handler() catch { _ -> .. }         // filter is [throw<_>]
```

Adopting it *removes* a special case rather than adding one. A previous
revision hardcoded `HandlerFilter::{ Explicit, AllExceptions }` into the
handler machinery to cover the `_` arm; with wildcards a filter is an ordinary
`EffectSetId` again.

### What it does to the lattice

An atom becomes a pattern — `(origin, args)` where each arg is a concrete type
or a wildcard — and the three operations grow subsumption:

```
⊆    {throw<AppError>} ⊆ {throw<_>}                  pattern match, not equality
∪    {throw<_>} ∪ {throw<AppError>} = {throw<_>}     a wildcard absorbs instances
−    {throw<AppError>, log} − {throw<_>} = {log}     the wildcard catch
```

Still cheap: sort by origin, and within an origin group a fully-wildcarded
pattern covers the group, so subset stays a near-linear merge. Monotonicity
and termination survive — union only draws patterns from its operands and
normalisation only removes subsumed ones, so the reachable lattice stays
bounded by the patterns written in the program.

**This is also the clean fix for §3b's rule.** That section says an
`AllExceptions` filter is safe to apply before substitution while an explicit
set is not. The general statement is: *a filter may be applied before
substitution iff it is stable under substitution*, and a fully-wildcarded
pattern always is, since `throw<_>` subsumes `throw<T0>` whatever `T0`
becomes.

**And it gives §3b a termination escape hatch.** If substitution starts
minting `throw<T1>, throw<T2>, …` without converging (polymorphic recursion),
collapsing them to `throw<_>` is a sound *widening* that terminates the
fixpoint, rather than hitting a hard cap and erroring. That option only exists
because wildcards are in the lattice.

### Representation

`EffectAtom(TypeIndex)` is invariantly a `Type::FunctionItem`, so a wildcard
argument needs a `TypeIndex` denoting it. **Add a pre-interned
`Type::Wildcard` at index 18** — appended at the end, per CLAUDE.md's rule
about never reordering the pre-interned slots.

Do *not* reuse `TypeIndex::INFER`, tempting as it looks given CLAUDE.md says
INFER "will be the type of user-written `_` in type annotations". The meanings
differ where it matters: INFER means *to be determined*, a wildcard means
*all*. Substitution must resolve the first and must never touch the second,
and every existing `matches!(ty, Type::Infer)` check becomes ambiguous. The
cost of the dedicated type is a handful of match arms; reusing INFER buys
only their absence and moves a "must never survive" invariant into a place
where it now legitimately survives.

### Syntax

`_` in an argument position, `*` reserved for the set level. They sit at
different levels — `[*]` is "every effect", `throw<_>` is "any argument here"
— so distinct spellings help, and `_`-as-wildcard in an argument position has
the Rust precedent (`_` is inference in a type, a wildcard in a pattern; an
effect clause is a bound, which reads as a pattern).

### Interaction with §0b

Under §0b a declaration is authoritative, so `fn f() [throw<_>]` means callers
see "any throw" — a real loss of granularity, and a deliberate one, the same
tradeoff as any widened contract. It has a tidy consequence: a `catch` over
such a callee cannot enumerate its arms, so it must carry a `_` arm.
Exhaustiveness falls out rather than needing a rule.

### What to pin now

Only this: the set operations must live behind `EffectInterner` methods that
can grow subsumption, rather than open-coded sorted merges at call sites. The
interner design (§1) already implies it.

---

## 2. Where effects come from

An effect exists because a bodyless function named itself in its own clause:

```wx
#[intrinsic]
pub fn trap() [trap] -> never;
```

**A bodyless function must declare an effect clause** (decided 2026-09-04,
§0b). Omitting one is a hard error, not a `Top` default — there is no `Top`
default any more. `Top` now arises only from an explicit `[*]`, from an
indirect call through a function pointer, and from abstract trait dispatch
(both MVP conservatisms, §5).

One carve-out to confirm before implementing: the working draft says
"Omitting the annotation from a trait method means that the trait places no
restriction on its effects, which is equivalent to `[*]`". A trait method
*declaration* is bodyless but is a bound over implementations rather than an
operation, so the draft's rule and the hard error are not in conflict — they
are about different things. This plan assumes the hard error applies to
operations (free functions, imports, intrinsics) and the draft's rule to trait
method declarations. Worth noting that in practice the two agree for concrete
code anyway: `a + b` resolves to `impl Add for i32`'s method, which has a
body, so an unannotated `Add::add` declaration only costs precision under
abstract dispatch, which the MVP already treats as `Top`.

Resolution rule, in `ensure_signature` (Phase 2, `tir/builder/signature.rs`):
resolve each element of the clause as an ordinary path. If it resolves to the
function currently being resolved *and* that function has no body, mint a new
`Effect { origin: self, args: [] }`. Otherwise it must resolve to a function
that already originates an atom, and we take that function's `effects` (which
forces `ensure_signature` on it — already re-entrancy-safe via `sig_state`, and
a cycle here is exactly the existing cyclic-dependency diagnostic).

Two things that are *not* calls also originate effects, and both must be
handled or the system is trivially bypassable:

- **`unreachable`** (`ExprKind::Unreachable`, `tir/mod.rs:741`) — the bare
  keyword already lowers end-to-end to WASM `unreachable`/`0x00`. If it
  doesn't count as `trap`, `[]` is silently violable by writing `unreachable`
  instead of `trap()`. It counts. (This was the previous plan's open question;
  answering it "yes" is what makes the accumulator have to look at more than
  call nodes — which is a good thing to design for now, because memory effects
  in §7 originate at `Load`/`Store` nodes the same way.)
- Later: `Load`/`Store` (`ExprKind::Load { place }` / `Store`) originate
  `read<Mem>`/`write<Mem>`, with `Mem` read straight off the pointer type's
  `Type::Pointer { memory }`. Deferred, but it's the reason an atom is an
  interned `Type::FunctionItem` with type arguments from day one (§1b).

**Finding `trap`'s `DefId` without a name lookup:** use the existing lang-item
mechanism — `#[tag = "trap"]` plus `items.tagged_items`, exactly how
`OperatorTraits` finds `Add`/`Div`/... (`tir/builder/operators.rs:124`).
Resolve it once after Phase 2, same place `resolve_operator_traits()` is
called (`tir/builder/mod.rs:666`).

---

## 3. Phase 3 — building the effect scope forest

The output of Phase 3 is the solver's input, and per §0c(a) its unit is an
**effect scope**, not a function. A scope is a region over which one
subtraction applies uniformly:

```rust
// crates/wx-compiler/src/tir/effects.rs

/// Deliberately *not* `ScopeIndex` — that name is taken (`tir/mod.rs:1059`)
/// and means a lexical block scope. See "block scopes vs effect scopes".
pub struct EffectScopeIndex(u32);

pub struct EffectScope {
    /// Every effect term reachable in this scope, reduced or not — a call, an
    /// `unreachable`, later a `Load`/`Store`. One list, not a direct/calls
    /// split: see "one list, not two". An interned set, not a `Vec`: see
    /// "accumulating, then interning". `TOP` is one of its possible values.
    pub atoms: EffectSetId,
    /// Nested scopes, each with the set it subtracts on the way out.
    /// Empty for every scope in the MVP.
    pub children: Vec<(EffectScopeIndex, EffectSetId)>,
}

pub struct EffectScopeForest {
    scopes: Vec<EffectScope>,
    /// Root scope of each function, indexed by `FunctionIndex` — the answer
    /// for its signature. `None` for a bodyless function: no body to walk,
    /// so it never enters the forest and its declared clause — mandatory,
    /// §2 — is its summary outright.
    roots: Box<[Option<EffectScopeIndex>]>,
}
```

The root index lives here rather than on `tir::Function` because the forest is
scaffolding: built in Phase 3, consumed by the solver in Phase 3.6, dropped.
`Function` outlives `TIR::build` and travels into MIR, so a scope index there
would dangle into an arena that no longer exists. The apparent precedent cuts
the other way — `signature_index` and `body` are on `Function` because they
stay true for the life of the TIR, which is also why `declared_effects` and
`declared_effects` belongs there and analysis output does not — the same
principle that puts terms and solutions on `EffectAnalysis` rather than on
`Function` (§1). (`Function` is also `serde::Serialize` under `cfg(test)`, so
a field there would put analysis ordering into every TIR snapshot.)

### What structure is needed, and when

The `EffectScope`/`EffectScopeForest` types below are **not built in the
MVP**, and possibly never: the expression tree carries the same structure
(§3b). Staged:

One walk of each body extracts an `EffectTerm` (§1); the solver then runs over
terms, never over bodies. What the term has to *hold* grows by stage:

| stage | `EffectTerm` is | solver |
|---|---|---|
| MVP — no `catch`, no parameterized atoms | an `EffectSetId` of atoms, some unreduced | reduce atoms to a fixpoint |
| `+ catch`, atoms still ground | gains `children: Vec<(EffectTerm, EffectSetId)>` — the type below | subtract on the way out of each child |
| `+ parameterized effects` | unchanged | `solve(term, σ)`, memoised on `(DefId, type_args)` (§3b) |

So the `Union | Subtract` shape from the ideas note is real, and it is the
`EffectTerm` type — `Union` needs no node (§3, "one list, not two"), leaving
`children` as the only structural part. What is *not* built is a global forest
with its own index space assembled by hooks during Phase 3: the term is
per-function, produced by one walk after Phase 3, and referenced from
`EffectAnalysis::terms`.

§0c(a)'s warning — do not hardcode a flat per-function accumulator — is met by
the term having room for `children` from the start, even though the MVP never
populates them.

### Block scopes vs effect scopes

These are different index spaces and must not share a name.

|  | block scope (`ScopeIndex`) | effect scope (`EffectScopeIndex`) |
|---|---|---|
| created by | every `{ }` | only a subtraction boundary — `catch` |
| holds | locals, labels, `expected_type` | `atoms`, `children` |
| lives in | the body's `StackFrame` | `EffectScopeForest`, spanning all bodies |
| count today | one per block | exactly one per function |

They are not in 1:1 correspondence and never will be: a function with twenty
nested blocks has one effect scope, and `catch` can wrap an arbitrary
expression rather than only a block. Both being `u32` newtypes in one crate,
reusing the name would make `ExprContext` carry two same-typed fields meaning
unrelated things, with nothing to catch a mix-up.

with the equation, for the solver:

```
effects(s) = ⋃ subst(contract(a.id), a.args)   for a in atoms(s)
           ∪ ⋃ (effects(c) − handled)          for (c, handled) in children(s)
```

**Today `children` is always empty and `roots.len() == functions.len()`, so
this is exactly the flat per-function formulation with one extra indirection.**
That indirection is the whole point: it is what `catch` needs, it costs one
`Vec` push per function to build, and it is what makes the diagnostics in the
next paragraph possible at all.

Why the scope has to survive into the solver rather than being flattened away
during the walk: `catch` exhaustiveness checking (post.md, "Handling effects")
needs the resolved set of the *guarded expression*, pre-subtraction, to say
"this arm handles `ConnectionError`, which cannot occur here". That is
`effects(c)` for the child scope — a solver output. Flattening filters down
into a per-call `handled` mask, as the ideas note sketches, computes the same
function effects but destroys precisely that intermediate. So: keep the
forest, solve over scopes, read child scopes back afterwards.

### Accumulating, then interning

A scope's atom list *is* an effect set — just not yet closed under reduction,
which is a legitimate state for one to be in (post.md's
`[<V as Validator>::validate]` is exactly such a member). So the stored field
is an `EffectSetId`, and solving has a clean signature:

```
solve: EffectSetId (syntactic) → EffectSetId (closed)
```

That also removes any need for a separate top flag: `EffectSetId::TOP` is a
value the field can already hold, and TOP absorbs everything, so a scope that
reaches it has irrelevant atoms. Stickiness is a build-time concern, not
stored state.

But atoms arrive one at a time during the body walk, and interning needs a
complete canonical sequence. Interning on every push would hash the whole
slice per call site — quadratic per scope — and fill the pool with prefix
garbage (`{a}`, `{a,b}`, `{a,b,c}`) that nothing ever refers to again.

So accumulation uses **one scratch `Vec<EffectAtom>` on the builder for the
entire walk**, not one per scope, with a mark/truncate discipline: the open
scope's atoms are always the suffix `buf[mark..]`.
`record_effect_call` binary-search-inserts into that suffix, so it stays
sorted and deduped at all times and closing a scope is a straight intern with
no sort. The scope-local dedup invariant below falls out for free.

```wx
fn g() {
    p();
    { q(); } catch A;
    r();
}
```

```
enter g       s0, mark=0            buf = []
  p()                               buf = [P]
  enter catch s1, mark=1            buf = [P]        s1 region = buf[1..]
    q()                             buf = [P, Q]
  exit catch  intern([Q]) -> s1.atoms
              truncate(1)           buf = [P]
              s0.children += (s1, {A})
  handler arms build here -> land in s0's region, not s1's
  r()                               buf = [P, R]
close g       intern([P, R]) -> s0.atoms
```

Interning therefore happens at exactly two moments: when a `catch` scope
closes, and when a function body ends. Never mid-walk.

The same rule binds the solver, for the same reason: it must union into a
scratch buffer and intern **once per scope visit**, not inside the union loop.
Comparing the resulting `EffectSetId` against the stored one then makes the
fixpoint's "did it change?" test a `u32` compare, and adds nothing to the pool
when it did not.

### Why dependencies are atoms, not function indices

An edge labelled with only a `FunctionIndex` loses the instantiation:

```wx
fn read_mem<M: Memory>(m: M) [read<M>];        // bodyless, declared
fn helper<M: Memory>(m: M) { read_mem(m); }    // bodied → schema [read<M0>]
fn main() { helper(heap); }                    // must infer [read<heap>]
```

`helper`'s inferred set is a **schema**: `read<M0>`, where `M0` is
`TypeParam { owner: Function(helper), index: 0 }`. Unioning that into `main`
under a bare `FunctionIndex` edge leaves `main` holding a type parameter
belonging to a function it is not inside — a dangling schema variable, with
the instantiation already discarded. The edge must be `helper<heap>`.

That is `(DefId, type_args)`, which is a `Type::FunctionItem`, which is an
`EffectAtom` (§1b) — and the call sites already have exactly this:
`GenericCall { id, type_args, .. }` (`tir/mod.rs:812`) and
`GenericMethodCall` (`:818`) carry it verbatim, while a non-generic `Call`
supplies empty `type_args`. Reducing a dependency is then
`substitute_type(contract(f.id), f.args)` — the same call §1b already
relies on, now doing double duty.

**Atoms and dependencies are the same data.** They differ only in whether the
solver can reduce them — and even that is not a category it has to recognise:
`trap` reduces to `{trap}`, a fixpoint, while
`helper<heap>` reduces to `helper`'s set substituted at `heap`. That is
post.md's "an effect is a function" showing through in the representation
rather than a coincidence, and it is what makes post.md's unresolved
`[<V as Validator>::validate]` need no new mechanism later: it is simply a
term the solver *cannot* reduce, so it stays unexpanded in the set and is
resolved at monomorphisation. Nothing has to notice it is special.

### One list, not two

An earlier draft split this into `direct` (already-known effects) and `calls`
(pending dependencies). That split is not necessary, and dropping it removes
the fiddliest part of the whole pass.

Irreducibility is not a category the solver has to recognise. `trap` is an
origin because `contract(trap) = {trap}`, so expanding the atom `trap` yields
`{trap}` and stops — a fixpoint, not a special case. Once that is true there
is nothing for a classification to decide, and every hook becomes uniform:
intern `FunctionItem { id, type_args }` and push it. `unreachable` pushes the
`trap` atom exactly as if it were a call; `Load`/`Store` will push
`read<M>`/`write<M>` the same way. No branch on bodyless / annotated /
unannotated anywhere.

What `direct` actually was: the constant term of the scope equation, eagerly
expanded at the call site — a classic dataflow gen-set, so a fixpoint loop
only re-touches what can still change. That is a real optimisation, and it is
available later without disturbing anything else, because it is a solver
concern and not a change to what a scope *means*. It therefore follows the
same rule as Tarjan in §4: build the plain version, split it when a benchmark
asks.

Two consequences to design in now rather than discover later:

- **The solver needs `&mut TypeInterner`, not just `&mut EffectInterner`**,
  since reducing an edge interns substituted atoms. Widen the §0c signature
  accordingly; it does not otherwise disturb the interface.
- **Polymorphic recursion is a termination hazard.** `fn f<T>() { f::<Wrapper<T>>(); }`
  generates a fresh atom per round and the fixpoint never closes — the finite
  lattice argument in §0c assumes a *fixed* atom set, which substitution
  breaks. Whatever bound monomorphisation already imposes, the solver needs
  the same one, and should report rather than hang.

### Where the hooks go

Nothing walks the tree a second time — every hook sits on a line that already
runs, at the moment the callee's `DefId` is already in hand:

| Site | Node |
|---|---|
| `calls.rs:222` | `GenericCall` |
| `calls.rs:236` | `Call` (direct — callee is `ExprKind::Function`) |
| `calls.rs:236` | `Call` (indirect, through a `fn(T) -> U` value) → `Top` for now, see §7 |
| `calls.rs:948` | `MethodCall` |
| `calls.rs:1041` | `GenericMethodCall` |
| `operators.rs:303,326,571,588` | operator dispatch → `Generic/MethodCall` |
| `operators.rs:1617,1678,1801` | `CompoundAssign` (`method_id`) |
| `body.rs:642` | `ExprKind::Unreachable` |

Best factored as one `Builder::record_effect_call(ctx, callee_id)` that every
site calls — the direct precedent is `mir::Builder::record_call_edge`
(`mir/mod.rs:1430`), which is exactly this pattern one layer down and is
already consumed by a call-graph pass (`mir/inlining.rs:608`).

`ExprContext` (`tir/builder/mod.rs:53`) carries the cursor:

```rust
/// The effect scope currently being accumulated into. `record_effect_call`
/// and the `unreachable` hook write here and nowhere else. The sibling field
/// `scope_index: ScopeIndex` is the *block* scope — a different index space.
current_effect_scope: EffectScopeIndex,
```

`record_effect_call` classifies the callee once, at the call site, and never
revisits it:

`record_effect_call` does the same thing at every site, with no classification
at all: intern `FunctionItem { id, type_args }` and binary-search-insert the
atom into the open scope's region of the scratch buffer. The one exception is
a callee with no body and no annotation, whose effects are `[*]` — that sets
the build-time sticky flag, so the scope closes as `EffectSetId::TOP`.

When `catch` lands, its only structural requirement is already satisfied: push
a child scope, run `enter_block`-style save/restore of `current_effect_scope` over the
guarded expression, restore *before* building the handler arms so their effects
land in the parent. `ExprContext::enter_block` (`tir/builder/mod.rs:88`) is the
existing precedent for exactly that save/restore shape.

Deduplication invariant, worth stating because it is what keeps `calls` short:
**within one scope a dependency matters only once; a `catch` starts a new
scope.** `foo(); foo(); foo();` is one edge. `foo(); { foo(); } catch A;` is
two, in different scopes, and must not be merged.

### Three details that are easy to get wrong

- **Gate on `ctx.mode`.** `EvalMode::Comptime` trees (`const` initialisers,
  enum discriminants) are interpreted and discarded, never lowered — they have
  no runtime effects. Skip accumulation there. The field already exists
  (`tir/builder/operators.rs:27`).
- **Abstract trait-method calls must be `Top` in the MVP.** When `Self` isn't
  concrete, `MethodCall`/`GenericMethodCall` carry the *trait's own* abstract
  declaration id — bodyless, no annotation ⇒ `Top`. Getting this wrong reports
  generic code as pure. There is already a hook that fires exactly once per
  such site: `record_abstract_dispatch_access` (`calls.rs:1626`). Concrete
  dispatch is unaffected — `i32 / i32` resolves to `impl Div for i32`'s method,
  which has a body.
- **Global initialisers are out of scope.** They do have runtime bodies
  (`body.rs:114`) and can therefore perform effects, so a complete system owes
  them an answer. Globals are slated for a rework, so this plan deliberately
  does not design one — no initialiser terms, no module-level
  "instantiation effects" set. Noted so it is not mistaken for an oversight;
  revisit once globals settle.

For the diagnostic in §4, first-introduction spans have to be recorded by the
**solver**, not here. The walker only ever sees *syntactic* atoms, so a map
built during the walk cannot answer the question the diagnostic asks:

```wx
fn g()    { trap(); }
fn f() [] { g(); }        // error: f performs `trap`
```

`f`'s scope contains the atom `g`; the offending resolved atom is `trap`, and
no `(f_scope, trap)` entry exists. So the map is populated during reduction —
when a scope's set gains atom `X` by reducing term `T`, record
`(scope, X) -> span(T)` if absent. One insert per newly discovered fact, and
it names the call that introduced it rather than the whole body. Interning
sets cannot carry provenance, so it has to live beside them.

---

## 3b. Subtraction must not be evaluated before substitution

Raised and resolved 2026-09-04. Not reachable in the MVP, but it fixes the
shape of a function's effect summary, so it is settled here rather than later.

`solve` currently evaluates every scope eagerly and stores a resolved
`EffectSetId`, discarding the forest. That is only valid when every atom
involved is ground, because **union commutes with substitution and difference
does not**:

```
subst(A u B, s)  =  subst(A, s) u subst(B, s)      always
subst(A - B, s)  ⊋  subst(A, s) - subst(B, s)      when s makes distinct atoms equal
```

Counterexample:

```wx
fn throw<E: Exception>(e: E) [throw<E>] -> never;

fn run<E: Exception>(e: E) {
    { throw(e); } catch { AppError(_) -> {} }
}
```

```
inner scope atoms = {throw<E0>}            E0 = run's own type param
handled           = {throw<AppError>}

evaluated at TIR (what the plan does):
  {throw<E0>} - {throw<AppError>} = {throw<E0>}    no syntactic match, nothing removed
  instantiate run<AppError> -> subst -> {throw<AppError>}

evaluated after substitution (the truth at E = AppError):
  {throw<AppError>} - {throw<AppError>} = {}
```

`run<AppError>` is reported as throwing an exception it demonstrably catches.
Sound as an upper bound, but it makes `catch` invisible inside generic code,
and it turns `[]` on such a function into a spurious hard error.

Structurally: a generic function's effect answer is not a set, it is a
**term** — unions of atoms with differences evaluable only once ground. The
forest *is* that term and solving is its evaluation, so
"forest -> solve -> set, discard forest" is valid exactly when everything is
ground. The missing rule is: **evaluate a difference only after substitution
is complete.**

Two cases, one of them fine:

- **Non-generic function** — substitution is the identity, eager evaluation is
  exact, discard the forest. Unchanged from §3/§4.
- **Generic function with a subtraction over non-ground operands** — the
  subtraction must not be evaluated until the caller's substitution has been
  applied. See the resolution below: the walk carries the substitution, so
  nothing needs to survive.

This does not reach the MVP, which has neither `catch` nor parameterized
effects; it is precisely their intersection. But it does falsify part of
§0c(a): the scope *structure* is additive, the *evaluation timing* is not.

### Resolution (decided 2026-09-04): thread the substitution through the walk

**Substitute into the term, then solve.** `EffectAnalysis::terms` (§1) is
retained precisely for this: it keeps the subtraction structure unevaluated,
so a caller's substitution can be pushed inside before any difference is
taken.

```
solve(term, σ):
  atom a          →  reduce(subst(a, σ))
  child (t, h)    →  solve(t, σ) − subst(h, σ)          substitution first
  union           →  ⋃ of the above
```

The difference always sees substituted operands, which is exactly the rule
above. `inferred` stays an `EffectSetId`: it is `solve(term, identity)`
— for a generic function, the schema, and a soundly over-approximate one
wherever a subtraction cannot fire at identity. Precise per-instantiation
answers come from `solve(term, σ)`, memoised on `(DefId, type_args)`.

Substituting a term is cheap — a handful of atoms — which is why this is
affordable per instantiation and re-walking the body would not be.

That memo key is `MonoRegistry`'s shape (`mir/mod.rs:856`) and is exactly
where polymorphic recursion diverges — see §1d, whose wildcard widening
(`throw<T1>, throw<T2>, … → throw<_>`) terminates it soundly rather than
hitting a cap.

### The layer question: TIR is sufficient

**The analysis stays entirely in TIR.** MIR exists to lower and monomorphise
for codegen; effect analysis is user-facing semantics and belongs where the
diagnostics are. Moving evaluation there was considered and rejected.

What makes TIR sufficient is that **monomorphisation is not needed to know an
instantiation**. A TIR call site already carries its type arguments —
`GenericCall { id, type_args }` (`tir/mod.rs:812`), `GenericMethodCall`
(`:818`) — so reducing the dependency `run<AppError>` has `[AppError]` in hand
at the call site. "Needs the instantiation" and "needs a monomorphic function"
are different requirements, and only the first one holds here.

So:

- Reducing a dependency walks the callee's body under the composed
  substitution, so a difference is never taken before substitution.
- Nothing has to be stored to make that work: the expression tree is the term,
  and it is retained anyway.

In the MVP there is no `catch`, hence no subtraction, so the term degenerates
to a flat set and none of this is visible. It becomes load-bearing only once
`catch` and parameterized effects coexist.

Consequence to design for: substitution inside reduction means polymorphic
recursion (`fn f<T>() { f::<Wrapper<T>>(); }`) can mint atoms forever, and
there is **no bound in `MonoRegistry` to inherit** — verified, `get_or_insert`
(`mir/mod.rs:873`) has no depth or count limit, so this is a latent hang in
MIR today. The cap and its diagnostic belong at TIR, which is the layer that
has a diagnostics channel at all.

---

## 4. Phase 3.6 — the solver, and why its choice is deferrable

New pass in `tir/builder/mod.rs`'s driver, between Phase 3 (line 670) and
Phase 3.5 (line 674). It is the *only* thing behind the §0c interface:

```rust
fn solve(
    scopes: &EffectScopeForest,
    effects: &mut EffectInterner,
    types: &mut TypeInterner,   // reducing an edge interns substituted atoms
) -> Box<[EffectSetId]>;
```

### What the forest does and does not encode

`EffectScope` is **purely syntactic**: which terms appeared, and where the
subtraction boundaries are. Nothing in it marks an atom as reducible, records
what it reduces to, or identifies origins. Reduction is not data — it is what
`solve` does to the forest, which is why a scope is only two fields.

| reduction | encoded where | performed as |
|---|---|---|
| term → its effects | *not* in the scope — via the atom's `DefId` | `subst(contract(a.id), a.args)` |
| handled effects removed | the `children` edge | `effects(child) − handled` |

Only subtraction is structural. That is the entire reason `children` exists
and `atoms` is flat.

`contract()` is the piece that closes the loop, and per §0b it has exactly
two cases — no package test, no availability test:

```
annotated (or bodyless, where the clause is mandatory)  → declared    constant
unannotated bodied                                      → effects[roots[f]]
```

Only the second reads mutable solver state, so **an annotation cuts the graph
for propagation**: nothing depends on an annotated function's body, no matter
how deep it goes. Its own body closure is still computed — that is what the
`⊆ declared` check compares — but it is a leaf as far as every caller is
concerned.

When `precise` lands (§7) it is the same walk with the first case
deleted: `precise()` always reads solver state where a body exists. Two runs
of one fixpoint, differing in one branch.

**An origin needs no marking.** `fn trap() [trap]` means
`contract(trap) = {trap}`, so reducing the atom `trap` yields `{trap}` — a
fixpoint. The solver never asks whether something is an origin.

#### Worked trace

```wx
fn throw<E: Exception>(e: E) [throw<E>] -> never;   // bodyless, origin
fn log(n: i32) [log];                               // bodyless, origin

fn risky()   { throw(AppError{}); }
fn recover() { log(2); }
fn main() {
    log(1);
    { risky(); } catch { AppError -> recover() };
}
```

`log` and `throw` are bodyless, so they get no scopes:

```
s0 = root(main)     atoms = {log, recover}   children = [(s1, {throw<AppError>})]
s1                  atoms = {risky}
s2 = root(risky)    atoms = {throw<AppError>}
s3 = root(recover)  atoms = {log}
```

`recover` sits in `s0`, not `s1` — the handler body is not under the
subtraction. Solving, every scope starting at the empty set:

```
s2:  reduce throw<AppError> = subst({throw<E0>}, [AppError]) = {throw<AppError>}
     s2 = {throw<AppError>}                    so contract(risky) = that

s3:  reduce log = {log}
     s3 = {log}                                so contract(recover) = {log}

s1:  reduce risky = contract(risky) = {throw<AppError>}
     s1 = {throw<AppError>}

s0:  reduce log     = {log}
     reduce recover = {log}
     child          = s1 - {throw<AppError>} = {}
     s0 = {log}                                so main is [log]
```

The `throw<AppError>` raised in `risky` reaches `s1`, is subtracted at the
edge, and never appears in `main` — while `log`, arriving both directly and
through the handler, survives.

### Build the naive solver first

A worklist over scopes, seeded with everything, iterating to fixpoint:

```
while let Some(s) = worklist.pop() {
    let new = ⋃ subst(contract(a.id), a.args) for a in atoms(s)
            ∪ ⋃ (effects(c) − handled)        for (c, handled) in children(s);

    if new != effects[s] {
        effects[s] = new;
        worklist.extend(reverse_deps[s]);   // callers, and parent scope
    }
}
```

Roughly forty lines, obviously correct, terminates by §0c's monotonicity
argument (every `(scope, effect)` pair is discovered at most once, and the
lattice is finite). It handles recursion with no special case at all — the
`new != effects[s]` check is what breaks cycles — and it handles `catch`
correctly on the day `catch` exists, including the §0c(b) counterexample,
because it does not assume anything about SCCs.

**Do not open with Tarjan.** It is an optimisation of the *evaluation order*
of this exact loop, not a different algorithm, and committing to it early is
what produced assumption (b). Write the naive version, write the tests against
it, and treat everything below as a later swap behind an unchanged signature.

### The candidates, and what each is actually worth

- **Tarjan condensation + per-SCC worklist.** Process SCCs in reverse
  topological order; everything outside the current component is already final,
  so the worklist only ever churns within one component. This is the real
  version of old §4 — the correction is that the per-component step is an
  iteration, not a single union (§0c(b)). Strictly better than naive, same
  output, ~150 lines. The obvious first swap, once there is a benchmark
  showing it matters.
- **Per-effect backwards reachability.** Propagate one newly-discovered
  `(scope, effect)` fact backwards through callers, stopping where a scope
  boundary handles that effect or the fact is already present. Elegant, and it
  makes `catch` a literal graph cut. Cost: a traversal per distinct effect,
  which gets worse exactly when parameterized effects arrive and
  `throw<A>`/`read<heap>`/`write<heap>`/… multiply the atom count. Reassess
  after §7's parameterized effects, not before.
- **Symbolic SCC solving.** Substitute equations algebraically. Interesting on
  paper; explodes on larger components, and would mean writing a constraint
  solver to avoid a small loop. Only becomes attractive if effect *variables*
  (`fx E`) arrive, at which point it stops being an optimisation and starts
  being the mechanism — which is the real reason to keep it on the list.

Note what is *not* in the dependency graph: calls to bodyless functions, calls
across a package boundary, and abstract dispatch — all three resolve to a
constant `declared` set at the call site (§1). Every other edge is real. Under
the pre-2026-09-04 rule this section claimed annotated functions were also cut
out; §0b reverses that, so the graph is close to the full in-package call
graph.

### Checking, which happens here and cannot happen earlier

The inferred set isn't known until the solver completes. For every function
with `declared_effects = Some(d)`:

- body closure ⊄ `d` → error, where the body closure propagates callees'
  **contracts**, not their precise sets (§1). Label the declaration, and use
  the solver-populated provenance map from §3 to point a secondary label at
  the call site that introduced the offending effect.
- `d ⊄ body closure` → **lint, not a default warning**: "declared effect is
  never performed". Demoted deliberately — the working draft endorses
  deliberate breadth ("The implementation may currently be pure and later
  change to one that can trap without changing the public API"), and under
  §0b's rule that breadth already costs its callers precision, so firing by
  default would fight the design. Compare against `precise` once it
  exists (§1), since that is the set that actually answers "never performs".
  **Exempt bodyless functions**, whose body closure is empty by definition —
  without this it fires on every intrinsic and import, `fn trap() [trap] -> never;`
  included, which is the origin the whole system is built on. Also exempt
  trait methods once §7 lands — there the annotation is a bound over all
  implementations, not a claim about one body.

Iterate in `FunctionIndex` order when reporting, not solver order, so
diagnostic output stays deterministic regardless of which solver is installed.
That determinism requirement is itself part of the interface: a swap must not
churn snapshots.

---

## 5. MVP scope

**In:**
- `[a, b]` / `[*]` / `[]` clause — lexer (nothing new), parser, AST, wx-fmt.
- Unparameterized atoms only — every atom interns as a `Type::FunctionItem`
  with empty `type_args`. Wildcard arguments (§1d) are therefore out too:
  there is nothing for them to range over. The parser accepts `name<Args>` and rejects it with
  a clear "not yet supported" so the grammar doesn't have to change later.
- Exactly one real atom: `trap`, minted by `#[intrinsic] #[tag = "trap"] fn trap() [trap] -> never;`
  and declared on `i32_div`/`i32_rem`/`u32_div`/`u32_rem`/… plus the bare
  `unreachable` keyword. Every *other* bodyless function in `std/main.wx`
  gets an explicit `[]` in the same commit — mandatory now (§2), and ~90 of
  them.
- Inference + closure + checking, as above.
- LSP hover showing the resolved set.

The end-to-end demo this buys, which is worth building toward deliberately
because it exercises every part of the mechanism through real stdlib code:
`a / b` → `Div::div` → `impl Div for i32` → `i32_div` `[trap]`, so a user
function containing a division infers `[trap]`, and annotating it `[]` is an
error. Inference through a trait impl, an operator, and an intrinsic, with one
atom.

**Out, deliberately:**
- `mir`/`opt` consumption of any kind. Effects stop at TIR.
- Parameterized effects, memory effects, `catch`, trait bounds, effect
  polymorphism, dyn dispatch — §7.
- Requiring annotations on `pub` items (the draft's "Effects at public
  boundaries"). Still out of the MVP — a single package has no boundary to
  cross — but note §0b now *leans* on it: it is what makes the cross-package
  behaviour fall out of "declared if present, else inferred" instead of
  needing a carve-out. So it is no longer optional polish, it is the second
  half of the rule, and it should land before wx has multi-package builds.
  Cheap: a check over `export_block` plus `pub` items, not a mechanism.
- Effects on function *pointer* types. Indirect calls are `Top`.

---

## 6. Order

Each step ends somewhere the tree compiles and the suite is green.

1. **Syntax.** AST `effects: Option<Spanned<EffectClause>>` on
   `ast::FunctionSignature` (`ast/mod.rs:1581`); parse between `params` and
   `result` in `parse_function_signature` (`ast/mod.rs:2596`). **wx-fmt lands
   in this step, not later** — a formatter that doesn't know about the clause
   silently deletes it. AST snapshot tests only; no semantics.
2. **Representation + Phase 2.** `tir/effects.rs` (L1); the two fields on
   `Function` (§1); clause resolution and atom minting in `ensure_signature`;
   the missing-clause error (§2). **The whole `std/main.wx` annotation pass
   lands here**, not at the end: `trap` plus `[trap]` on the arithmetic
   intrinsics plus `[]` on the other ~90 bodyless declarations. It has to
   precede step 4's demo, which is meaningless while everything is `[*]`.
3. **Phase 3 scope collection.** `EffectScopeForest`, `current_effect_scope` on
   `ExprContext`, `record_effect_call` and the hook table in §3. One root scope
   per function, `children` always empty. Nothing consumes the output yet — end
   this step by asserting the collected forest in a test, so the shape is
   pinned before a solver depends on it.
4. **The naive solver + diagnostics.** The forty-line worklist, `contract()`
   wiring, the two checks, three new `DiagnosticCode` entries — `E1082`
   (inferred ⊄ declared), `E1083` (missing effect clause on a bodyless
   function, raised in step 2), `W1011` (declared but never performed);
   next free codes verified at `diagnostics.rs:196`. **This is the first
   step that produces a user-visible answer**, and the end-to-end demo in §5
   should be a test here.
5. **LSP hover** showing the resolved set.
6. *(removed — the stdlib annotation pass moved into step 2, where it is a
   precondition rather than a follow-up.)*

Steps 1 and 3–5 touch no `.wx` file, so they validate against inline
`TestCase` fixtures in `tir/tests.rs` with zero snapshot churn.

Explicitly *not* in this list, and that is the point: choosing a solver.
Step 4 installs one; §0c's interface is what lets the choice be revisited
with a benchmark instead of a rewrite.

---

## 7. What this buys later (and why the architecture holds)

Each of these is additive against the structure above, not a rewrite:

- **Parameterized effects** (`throw<E>`, `read<Mem>`, `global_get<G>`) —
  free, representationally: an atom is already an interned
  `Type::FunctionItem` (§1b), so `throw<ApplicationError>` is just that item
  interned at that argument, and `substitute_type` already does the
  monomorphisation walk. Origination is unchanged. The open question
  is not representation but *timing*: TIR is pre-monomorphisation, so inside a
  generic function `read<Mem>` has a `Type::TypeParam` argument and the
  function's effect set is a **schema**, not a ground set. Substitution then
  happens at mono, using the same `find_trait_impl` machinery MIR already runs
  for `GenericMethodCall` — and `inferred ⊆ declared` checking on a generic
  function has to compare schemas param-relatively. Worth knowing before the
  first atom is interned with a non-empty argument list; not a blocker for the
  MVP, which has none.
- **Memory effects** — originate at `Load`/`Store`, memory read off
  `Type::Pointer { memory }`. The accumulator already handles non-call
  origination because of `unreachable`.
- **`catch`** — a child scope with a `handled` set, per §3. The forest, the
  save/restore, and the solver all already accommodate it; what is left is
  genuinely just the syntax, `tag` declarations, and the exhaustiveness check
  that reads a child scope's resolved set back. *This is the item that old §7
  listed as "the one place where the MVP's shape would actually change" —
  §0c(a) and §3 are what removed it.*
- **Trait bounds and abstract effects** (`[<V as Validator>::validate]`) — a
  third `Effect` shape, resolved at mono time. The MVP's blanket `Top` for
  abstract dispatch is the conservative version of exactly this, so tightening
  it is a local change at `record_abstract_dispatch_access`.
- **Effects on function types** — `tir::FunctionSignature` (`tir/mod.rs:96`)
  gains an `EffectSetId` field. It already derives `Hash`/`Eq` for interning,
  so this is one field plus the places that build a signature; it does change
  type identity, which is why it's worth doing as its own step.
- **`fx` effect-set parameters** — the one item that is *not* purely additive,
  and the one to think hardest about before committing. It introduces effect
  *variables*, so an `EffectSetId` stops always denoting a ground set and the
  solver stops being a monotone fixpoint over a finite lattice — it becomes
  constraint solving with `E ⊆ bound` obligations. The interface in §0c
  survives (`solve` still maps the forest to sets), but its implementation
  would be a real rewrite, which is exactly why the symbolic candidate stays on
  §4's list. **L1 changes too** — an earlier draft of this bullet claimed it
  did not, and that was wrong. `EffectAtom(TypeIndex)` invariantly denotes a
  `Type::FunctionItem`, i.e. one function-shaped atom; it cannot represent a
  variable standing for an entire set, as `[log, E]` requires. That needs a
  richer set *member* (distinct from `EffectTerm`, §1, which is a whole
  constraint):

  ```rust
  enum EffectMember { Atom(EffectAtom), SetVariable(EffectParamId) }
  ```

  or an equivalent symbolic form. Not worth introducing the enum now for a
  single variant, but the honest statement is that `fx` changes the atom
  representation, not that it slots in beside it.
- **The `precise` closure** — the second propagation defined in §1, computed
  with annotations ignored. Purely additive by construction: nothing
  user-visible reads it, so adding it cannot change a diagnostic or a type.
  It is what keeps §0b's decision from costing codegen anything, and it is the
  reason the type system can afford to be imprecise where a declaration is
  broad. Same fixpoint, one branch deleted (§4).
- **Optimizer payoff** — the point of all of it. `precise == EMPTY` on a call
  is what lets `opt` CSE it, hoist it out of a loop, or delete it when its
  result is unused; `write<M>` is what lets a load from a *different* memory
  survive across an opaque imported call. Note that `opt` should read
  `precise`, never `contract()` (§1): the type system is
  deliberately imprecise where a declaration is broad, and the optimizer is
  the one consumer that should not pay for that.

---

## 8. Snapshot discipline

Per CLAUDE.md: any edit to `std/main.wx` shifts byte offsets and fails every
snapshot in the suite. **One** `std/main.wx` edit is now planned, not two —
the annotation pass moved into step 2 (§6), so `trap`, the `[trap]`s and the
~90 `[]`s land together in one isolated commit followed by one
`INSTA_UPDATE=always` + `cargo insta accept`.

A second regen is unavoidable in the same step for a different reason:
`tir::Function` is `#[cfg_attr(test, derive(serde::Serialize))]`
(`tir/mod.rs:1913`), so even the single `declared_effects` field changes every
TIR snapshot though no `.wx` file moved. Keeping analysis output on
`EffectAnalysis` (§1) is what holds this to one field rather than four, and
lets the analysis itself be `serde(skip)`ped or snapshotted separately from
the item registry. §6's claim that steps 1
and 3–5 have zero churn holds; step 2 has two causes of it. Either accept both
in one commit, or gate the new fields with `#[cfg_attr(test, serde(skip))]`
until step 4 and regen once — the codebase already uses that escape hatch in a
dozen places.

Nothing else in this plan touches a `.wx` file.
