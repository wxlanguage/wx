# Generic traits and clause blocks

Status as of 2026-11-22: **design**, nothing implemented. Core's `Not` and
`PointerSize` are written in the clause-block form (uncommitted) and do not
parse yet. Companions: `inherent-associated-types.md` (one name per head),
`single-trait-impl-per-constructor-plan.md` (the rule this generalizes),
`tir-assumption-env-plan.md` (clauses about any subject).

Two parts, separable: **clause blocks** (`where { .. }` after an item header)
are useful on their own and come first; **generic traits** (`trait From<Source>`)
build on them and wait for a concrete need.

## The model

A trait is a relation over its **inputs**: `Self` (input 0) and its type
parameters. `Self` is special only in syntax (receivers, `x.m()`), never in
selection.

```wx
trait From<Source> { func from(value: Source) -> Self; }
impl From<u8> for i32 { .. }     // the row  From for <i32, u8>
```

- An impl is one row, keyed by the **head** of every input:
  `(From, head(i32), head(u8))`. A head is what `ImplTarget::from_type`
  returns; type arguments under a head never take part.
- Every input of an impl has a head. A bare parameter is not allowed in any
  input position, `Self` included. No blanket impls.
- Coherence is key uniqueness: no overlap analysis, no specialization.
- Today's traits are the one-input case: the key is `(Trait, head(Self))`,
  E2044 becomes "one impl per key", and every existing program keeps its
  meaning.

**Invariant:** substituting a parameter never changes a complete key. A head
belongs to a nominal type and substitution rewrites only beneath it
(`Wrap<T>` → `Wrap<u8>`, head `Wrap`). So selection in generic code and in
every monomorphized instance agree. A bare parameter in an impl would leave a
hole in its key that substitution fills differently, and overlap checking
would come back; the "every input has a head" rule is exactly what keeps key
uniqueness sufficient.

### Inputs and outputs

| Slot | In the key | Decided by | Projection |
| --- | --- | --- | --- |
| input (`Self`, a trait parameter) | yes | the use | trivial: the use wrote it |
| output (associated type or constant) | no | the impl | meaningful |

A slot is an input if and only if it is part of the key. Making a trait
parameter an associated type allows one impl per `Self`, which is today's
rule with different syntax. `<Foo as From>::Source` is not a function (`Foo`
has many sources) and is not resolved through a unique assumption either:
adding an unrelated clause would make it ambiguous.

## Clauses

A clause is a trait applied to all of its inputs, plus output bindings:
`(trait, [inputs], bindings)`. `T: Tr` is the short form for a clause whose
input 0 is a parameter. Internally `TraitClause::subject` is already any
`TypeIndex`; generic traits turn it into an input list with
`subject = inputs[0]`.

### Syntax: `where` after an item header

```wx
func convert<T>(x: T) -> Foo where { Foo: From<T> } {
    Foo::from(x)
}

func widen<T>(a: Wide, b: T) -> Wide where {
    Wide: Add<T> where { Output = Wide },
} {
    a.add(b)
}

impl<T> Set<T> where { Wrap<T>: Hash } { .. }
struct Sorted<T> where { Wrap<T>: Ord } { .. }

pub trait Pointer where {
    Self: StackValue where {
        Repr = <(Self::Memory::Size, Self::Metadata) as StackValue>::Repr,
    },
} { .. }

pub typeset PointerSize where {
    Self:
        + Add
        + Sub
        + PartialEq
        + StackValue
} { u32, u64 }
```

- An entry is `Type: Bounds`. Bounds are today's grammar: `+`-separated, an
  optional leading `+`, each bound with an optional binding block. One entry
  with several bounds is several clauses on one subject.
- A **binding block** after a bound constrains that bound's outputs
  (`Name = Type`, `Name: Bounds`, `const N: Type`). It is shorthand for
  clauses on projections (`Output = Wide` is `<Wide as Add<T>>::Output =
  Wide`), which is how the checker already lowers it.
- A `where` after a bound always belongs to the bound. A `where` after an
  item header (a function signature, an impl, struct, trait or typeset
  header) is the item's clause block. The token before `where` decides;
  no lookahead or name resolution.
- **Supertraits are `Self:` clauses** in the trait's block. The short form
  `trait X: Super` is dropped: a header ending in a bound followed by a
  clause block (`trait X: Iterator where { Item: Hash } {`) cannot tell a
  binding on `Item` from a clause about a type named `Item`.
- `<T: Tr where { .. }>` stays as the short form for a clause on a parameter.
- A trait function's clauses on `Self` go in its block, replacing the
  first-parameter `Self` trick:
  `func as_slice<Mem: Memory>(self: Mem::&Self) -> Mem::&[Self::Value]
  where { Self: Array where { const LEN: Mem::Size, Value: StackValue } }`.

### Two blocks, two kinds of keys

Both blocks read "such that"; their keys differ. A binding block's keys are
the bound trait's member names, as a struct literal's are field names; a
clause block's keys are types resolved in the item's scope.

```
BindingBlock := 'where' '{' (Binding (',' Binding)* ','?)? '}'
Binding      := Name '=' Type            // output equality:     Item = u8
              | Name ':' Bounds          // bound on an output:  Item: Hash
              | 'const' Name ':' Type    // representability:    const LEN: Mem::Size
              | 'const' Name '=' Expr    // constant equality (parsed, reported)

ClauseBlock  := 'where' '{' (Clause (',' Clause)* ','?)? '}'
Clause       := Type ':' Bounds
```

A clause block has one entry form. Equalities and constant facts hang under
the trait clause that gives the projection meaning
(`T::IntoIter: Iterator where { Item = u8 }`); a projection needs that clause
anyway, so a clause block needs no `=` or `const` entries. Inside a trait, a
bare `Item` in its clause block is a type path, not its associated type:
write `Self::Item`. Only binding blocks resolve bare member names.

A key is any type that mentions a parameter in scope or `Self`, in the key or
in the trait's inputs:

| Key | Example | Notes |
| --- | --- | --- |
| a parameter | `T: Hash` | long form of `<T: Hash>` |
| `Self` | `Self: StackValue` | supertraits; a trait function's facts about `Self` |
| a projection | `Self::Memory: Memory`, `<T as Tr>::Out: Eq` | a nested binding written from outside |
| a nominal type over a parameter | `Wrap<T>: Hash` | complete key, checked against the impl (rule 2) |
| a concrete type, a parameter among the inputs | `Foo: From<T>` | generic traits; a plain assumption |
| a structural type | `Mem::&T: StackValue`, `(T, U): StackValue` | compiler-answered traits; no heads, no user impls |

Rejected keys: `u32: Add` (no parameter, rule 1), `_: Tr` (no inference in
written clauses), `!: Tr`.

Per item:

| Item | Parameters in scope | The block |
| --- | --- | --- |
| free function | its own | assumed in the body, proved by every caller |
| trait function | its own, the trait's `Self` and inputs | the same; facts about outer parameters stay local to the function |
| impl | its own; `Self` is the target | assumed in its members, proved where the impl is selected |
| trait | `Self`, its inputs | the guarantee (rule 3) |
| typeset | `Self` | the guarantee, checked against each member (rule 5) |
| struct, enum | its own | open: see below |
| associated type | none | no block; `type A: B where { .. }` keeps its bounds |

Overlapping spellings lower to the same clauses and are accepted:
`<T: Iterator where { Item: Hash }>` is `where { T: Iterator, T::Item: Hash }`,
and `type IntoIter: Iterator where { Item = Self::Item };` is the trait-block
entry `Self::IntoIter: Iterator where { Item = Self::Item }`. The short forms
keep common cases short; the block can state anything.

### Rules

1. **A clause mentions a parameter** of the item, or `Self`, in some input.
   One that mentions none (`u32: Add`) is always true or always false and is
   an error.
2. **Clauses with a complete key are checked against the impl** at the
   declaration. `Wrap<T>: Hash` reduces to that impl's bounds on `T`; an
   equality contradicting the impl (`<Wrap<T> as Tr>::Out = u8` beside
   `impl<U> Tr for Wrap<U> { type Out = u16; }`) is an error there. Trusting
   both would let a body prove `u8 = u16`. Only clauses whose key has a
   parameter head (`Foo: From<T>`) become plain assumptions.
3. **A trait's block is its guarantee:** every impl proves it, and holding
   `X: Trait` assumes it. Implied are clauses whose subject is `Self`, a
   projection of `Self`, or another input of the trait; the rest are proved at
   each use. Implying a clause like `Wrap<Self>: A` would grow without bound
   (`Wrap<Wrap<T>>: A`, ...). Cycles between traits are handled by the
   visited walk `trait_implies` already does.
4. **Shorthand projections** `X::Name` resolve through the clauses about `X`
   in scope when exactly one trait provides `Name`, as for parameters today;
   otherwise E2043 asking for `<X as Tr>::Name`.
5. **A typeset's block is checked against its members** at the declaration;
   the set is closed.

## Using a generic trait

```wx
func convert<T>(x: T) -> Foo where { Foo: From<T> } { Foo::from(x) }
func outer<U>(y: U) -> Foo where { Foo: From<U> } { convert(y) }
func main() -> Foo { outer(5u32) }
```

- **Checking.** Inside `convert`, `T` has no head, no key matches, and the
  requirement `Foo: From<T>` is met only by the assumption. Without the clause
  the call is an error.
- **Selection.** At monomorphization the key `(From, Foo, u32)` is complete.
  The impl exists: the first caller without parameters proved `Foo:
  From<u32>` by the same lookup. It is unique: one impl per key. By induction
  over call chains, every instance finds exactly one impl.

A requirement, by its inputs:

| Inputs | Result |
| --- | --- |
| every head known | lookup: one impl or none |
| some input is a parameter | an assumption only |
| some input is an inference variable | wait (bodies) or error (written types) |
| some input is a projection | normalize, then as above |

When an assumption and an impl both match, checking uses the assumption;
monomorphization cannot disagree because the key has one impl.

**Paths stay open.** `Foo::from` names the family `From<Foo, ?>`. Member path
resolution through a type returns "this trait function, key incomplete", and
call checking completes the key from the arguments.

**No `Into`.** Rust needs it for bounds whose subject is the parameter (clause
blocks remove that) and for `x.into()` (method syntax stays about `Self`;
write `Foo::from(x)`). One trait per relation, no mirror trait, no generated
impls.

## Accepted costs

- No `impl<T> From<T> for Wrap<T>` (bare input): write a constructor.
- `impl From<Wrap<u8>> for Foo` and `impl From<Wrap<u16>> for Foo` collide,
  as type arguments under `Self` do today.
- Trait arguments need heads, so no tuples or pointers as inputs until they
  get heads, and then in both positions at once.
- Concrete subjects with generic traits often need qualified projections
  (`<Wide as Add<T>>::Output`) where `Wide` has its own `Add` impl.
- Dropping `trait X: Super` and the `Self` trick rewrites 28 trait headers,
  the `Integer` and `PointerSize` typesets and `Array::as_slice{,_mut}`.

## Typestate

Type arguments never select an impl, for inherent members (one name per
head) or trait impls (one impl per key). This is the intended rule, kept
deliberately; same-named inherent functions in impls with disjoint argument
heads are not allowed.

Checked against `HEAD` (2026-11-22):

| Pattern | Result |
| --- | --- |
| state-only methods, distinct names (`impl Conn<Closed> { func open }`, `impl Conn<Open> { func send }`) | accepted |
| a method in the wrong state (`Conn<Closed>.send()`) | E2034 |
| a subset of states (`impl<S: CanSend> Conn<S> { func send }`) | accepted; other states rejected |
| one name in two states (`describe` in `impl Conn<Open>` and `impl Conn<Closed>`) | E2000 |
| a trait impl per state (`impl Show for Conn<Open>`, `impl Show for Conn<Closed>`) | E2044 |

Per-state behaviour lives on the state types, which have their own heads:

```wx
trait State { type Next; const CODE: i32; }
impl State for Open   { type Next = Closed; const CODE: i32 = 1; }
impl State for Closed { type Next = Open;   const CODE: i32 = 0; }

impl<S: State> Conn<S> {
    func describe(self: Self) -> i32 { S::CODE }
    func toggle(self: Self) -> Conn<S::Next> { Conn{ fd: self.fd } }
}
```

The transition table is a set of impls: same-named transitions and
per-state signatures are associated types, per-state trait behaviour is one
generic impl delegating to `S`. Making the state a generic-trait input
(`impl Show<Open> for Conn<Open>`) repeats it on both sides and cannot be
filled from method syntax; the state trait is the idiom.

## Where it pays off

- **Clause blocks:** one place for an item's facts; clauses on impls and
  structs; no hidden `Self` parameter for the turbofish and conformance to
  skip.
- **Resource-indexed traits:** memories have heads (`ImplTarget::Memory`), so
  `Allocator<M>` keyed `(Allocator, Bump, heap)` lets one allocator type serve
  several memories, where `type Mem` ties it to one. Load/store or host
  boundary traits over a memory follow the same shape.
- **Not conversions in general:** core's `to_f32`, `to_i64`, `promote`,
  `demote`, `to_bits` name distinct Wasm instructions (truncating or
  saturating, signed or unsigned). A generic `From` would hide which runs;
  it fits lossless widening only.
- **Not pointer arithmetic yet:** pointers have no head, so no trait has an
  impl for them.

## Termination

Normalization is a rewriting system with head lookup and recursion through
projections; that is very likely Turing complete already, with or without
this design (not proven for wx):

```wx
impl<T> Grow for Wrap<T> { type Out = <Wrap<Wrap<T>> as Grow>::Out; }
```

Clause blocks add no computation: bounds are obligations, never filters, so
selection never searches. Generic traits make encodings shorter, not more
powerful. The solver's recursion limit (128, `solver.rs`) turns
non-termination into a diagnostic, and each step is a deterministic lookup,
so cost is linear in rewriting steps. What must not grow without a limit:
implied clauses (rule 3) and monomorphized instances (polymorphic recursion;
type flattening is capped by `SLOT_LIMIT`, instance count is unverified).

## Rejected alternatives

- **Trait arguments outside the key** (one impl per `Self` head): associated
  types with other syntax.
- **Rust's model** (unification-based selection, overlap checking, blanket
  impls): the problems both one-impl rules exist to avoid.
- **A `;` section in the generic list** (`<T; Foo: From<T>>`): mixes declaring
  parameters with stating facts.
- **A `requires` keyword:** `where` after a header is unambiguous once
  supertraits move into the block.
- **Marking the parameter's role** (`T: From<Self = Foo>`): cannot express a
  clause where no input is a bare parameter (`Foo: Add<Wrap<T>>`), and hides a
  relation about `Foo` under `T`.
- **Outputs in the trait's arguments** (`Add<T, Output = Wide>`): mixes named
  outputs into a positional list; a workaround for Rust's lack of a binding
  block.
- **Bare braces for bindings** (`Add<T> { Output = Wide }`): unambiguous only
  while no bound precedes an item body, and reads like a struct literal.
- **Flat-only clause blocks** (dropping binding blocks for `<X as Tr>::Out =
  Y` entries): verbose for concrete subjects; binding blocks already lower to
  the flat clauses.

## Open

- `=` before a function body (`func add(a: i32, b: i32) -> i32 = { a + b }`),
  making a definition read like `const` and `type`. Unambiguous after a
  signature. To decide: a block only or any expression (`= a + b;`), the `;`
  rule, and one canonical spelling for the formatter.
- Where a struct's or enum's clauses are proved: at every mention of the type
  with arguments (Rust's well-formedness, noisy), or only at construction and
  in impl headers, assumed inside its impls. Nothing in core needs struct
  clauses yet.
- Constants as trait inputs (a length) need their own notion of a head.
- Whether monomorphization needs its own instance limit.

## Stages

1. Clause blocks: parser, formatter, lowering into the assumption env;
   rules 1, 2, 4 and 5; diagnostics naming the clause a caller failed to prove.
2. Supertraits as `Self:` clauses and the guarantee rule (3); drop
   `trait X: Super` and the first-parameter `Self` trick; migrate core and the
   examples.
3. LSP: hover, definition and completion inside clause blocks.
4. Generic traits: inputs in `TraitClause` and the impl key, open member paths,
   pending requirements in bodies; checking tests, a Wasmtime execution test
   for a generic caller, and `Allocator<M>` as the first user.
