# Typeset Refactor — Research & Plan

Reframes `typeset` from a bespoke bound mechanism into **a compiler-generated
closed trait**, widens members beyond integers, fixes literal coercion (integer
*and* float), and deletes the parallel machinery that shadows the trait system
today.

Related notes:
- [typeset.md](./typeset.md) — the original feature spec (closed set, no methods, erased before codegen).
- [typeset-as-traits.md](./typeset-as-traits.md) — naming, prior art (Go type sets, Java/Kotlin `sealed`), and the `Trait { sealed: Option<Sealing> }` internal shape this plan adopts.
- [bound-checking-unification.md](./bound-checking-unification.md) — the bound-resolution path this touches.
- [single-trait-impl-per-constructor-plan.md](./single-trait-impl-per-constructor-plan.md) — the coherence rule the synthetic impls inherit.

---

## 1. Motivation

Three problems with typesets as they exist:

1. **Integer-only.** `signature.rs` rejects any non-integer member
   (`TypesetMemberNotInteger`, E1046). No `typeset Float { f32, f64 }`, no sets
   over structs/enums.
2. **A parallel type system.** `type_in_typeset` / `concrete_type_in_typeset`
   hand-mirror `type_implements_trait`; `Bounds` carries a bespoke
   `typeset: Option<TypesetBound>` slot alongside `traits`; `resolve_bounds`
   special-cases "at most one typeset" (`MultipleTypesetBounds`, E1048);
   operator dispatch has `is_typeset_bounded_assoc_type` as a dedicated trust
   path. Every one of these exists only because a typeset is not a trait.
3. **Implied operations are magic.** `resolve_bounded_operator_method` trusts a
   typeset bound for *any* operator trait, justified only by "all members are
   integer primitives with `#[inline]` impls." It does not compose, and it does
   not survive non-numeric members.

The fix: a `typeset` declaration generates an ordinary (empty) trait plus one
synthetic impl per member. `T: Integer` becomes `T: __Integer`. Operations come
from real bounds written on the typeset (`typeset Integer: Add + Sub { ... }`)
and reach the body through the ordinary supertrait chain. Membership, coherence,
conformance, projection — all handled by existing trait code with no
typeset-specific branch.

---

## 2. Current state (grounded)

### Parsing / AST
- `Item::TypeSet { id, pub_span, attributes, name, members: Box<[Separated<Spanned<TypeExpression>>]> }`
  — `ast/mod.rs:1803`. `parse_typeset_item` (`ast/mod.rs:5482`) parses only
  `typeset Name { T, T, ... }`. **No bound clause, no `where` clause.**
  `attributes`/`pub_span` are backfilled by the item wrapper (`set_attributes`),
  which is how `#[tag = "pointer_size"] pub typeset` works.
- `Expression::Int { value: u64 }` — raw non-negative magnitude; `-1` is a
  separate `Unary { InvertSign, .. }`. `Expression::Float { value: f64 }` —
  **parsed to `f64` at parse time (`ast/mod.rs:3940`), original decimal text
  discarded.** Malformed → diagnostic + `0`/`0.0`.
- The TIR builder can recover the original literal slice:
  `self.files.get(file_id)?.source` (`vfs/mod.rs:206`) sliced by `expr.span`;
  builder holds `files` at `builder/mod.rs:159`.

### TIR data model
- `TypeSet { id, file_id, namespace, name, pub_span, members: Box<[TypeIndex]>, intersection_range: IntegerRange, accesses, attributes }` — `tir/mod.rs:595`.
- `Bounds { traits: Box<[TraitBound]>, typeset: Option<TypesetBound> }` —
  `tir/mod.rs:2000`. **Single** typeset slot; `BoundSources::typeset()` returns
  the first found.
- `IntegerRange { min: u64, max: u64 }` with `for_integer_type`, `intersect`,
  `contains` — `tir/mod.rs:502`.
- `Trait { id, .., self_type_param: TypeParamInfo, members: HashMap<SymbolU32, MemberIndex>, .. }`
  — `tir/mod.rs:408`. Supertraits live in `self_type_param.bounds.traits`
  alongside a reflexive `Self: ThisTrait` entry (`Trait::supertraits` filters it
  out by index).
- `TraitImpl { id, trait_index, type_params, target, members, member_decls, span, file_id, namespace, self_accesses }`
  — `tir/mod.rs:464`.
- `ImplTarget` — `tir/mod.rs:1878`: `U8..I64, F32, F64, Bool, Char, Slice, Array, Struct(StructIndex), Enum(EnumIndex), Memory(DefId)`.
  `ImplTarget::from_type` returns `Err` for `Error/Infer/Never/Integer/Float/TypeParam/Unit/Tuple/Pointer/AssocTypeProjection/Namespace/FunctionItem`.

### Resolution
- **Signature** (`signature.rs:344`): resolves members; `!ty.is_integer()` →
  E1046; folds `intersection_range` via `IntegerRange::for_integer_type`.
- **`resolve_bounds`** (`generics.rs:195`): `BoundList` merges; a second typeset
  → `MultipleTypesetBounds` (E1048); a `where` clause on a typeset → ad-hoc
  "typesets cannot have associated type bindings" (no code).
- **`ensure_typeset_members`** (`generics.rs:73`): forces the typeset's
  signature when a bound names it, so declaration order can't observe an empty
  member list. Cycle-safe via `ensure_signature`.
- **Supertrait** (`traits.rs:969`): `trait Foo: Integer` already fills
  `self_param.bounds.typeset`.
- **Assoc type** (`std/main.wx:1418`): `type Size: PointerSize + UnsignedInt` —
  a typeset bound and a trait bound already coexist on one associated type.

### Membership & operators
- `concrete_type_in_typeset` = `members.contains(&ty)` (`tir/mod.rs:3879`);
  `type_in_typeset` (`:3974`) adds the abstract case.
- `type_implements_trait` (`:3903`) **already has closed-trait semantics**: a
  typeset bound proves trait `X` iff *every member* implements `X`.
- The magic: `is_typeset_bounded_assoc_type` (`generics.rs:642`) +
  `resolve_bounded_operator_method` (`operators.rs:237`) trust a typeset bound
  for any operator trait unconditionally. Call sites: `operators.rs:309, 536, 1094`.

### Literal coercion (`literal.rs`)
- `coerce_untyped_int_expr` (`:458`): int → `f32`/`f64` target → hard error
  `report_integer_literal_for_float_type` (E1006, "add a decimal point"). int →
  typeset-bounded `TypeParam` → `intersection_range.contains`. Generic pointer →
  looks up the `pointer_size`-tagged typeset, checks its `intersection_range`
  (`:530`).
- `coerce_untyped_float_expr` (`:593`): **f32/f64 accepted unconditionally —
  two `// TODO: add a diagnostic if the literal is out of range`.** Non-float
  target → E1005.
- ~30 call sites of `coerce_untyped_expr` across operators / control /
  aggregates / body / calls.

### Downstream
- **MIR has no typeset concept.** `instantiate_type` (`mir/types.rs:237`)
  asserts `Integer`/`Float`/`Infer` never reach MIR. This refactor is entirely
  AST + TIR; **MIR, codegen, opt, and the mono worklist are untouched.**
- `std/main.wx`: `pub typeset Integer { u8,i8,u16,i16,u32,i32,u64,i64 }`
  (`:1347`); `#[tag="pointer_size"] pub typeset PointerSize { u32, u64 }`
  (`:1415`).
- Diagnostic codes: E1004 `IntegerLiteralOutOfRange`, E1005 `UnableToCoerce`,
  E1006 `LiteralTypeMismatch`, E1046 `TypesetMemberNotInteger`, E1047
  `TypesetBoundViolation`, E1048 `MultipleTypesetBounds`.
- `register_trait_impl` (`traits.rs:21`) gates every impl on
  `ImplTarget::from_type(...).is_ok()` (`InvalidImplTarget`) **and rejects a
  second impl of the same trait for the same `ImplTarget` constructor**
  (`DuplicateTraitImpl`, `traits.rs:52`).
- **Precedent for synthetic trait machinery**: memory impls
  (`memory.rs:183`) `push_trait_impl` a `TraitImpl` with a synthetic `DefId`,
  `member_decls: HashMap::new()`, members built in full — "nothing for a lookup
  to force."

---

## 3. Target model — typeset as a compiler-generated closed trait

### 3.1 Shape

`typeset Integer: Add + Sub where { Output = Self } { i32, i64 }` lowers to:

1. **A synthetic `Trait`** (`__Integer`): `id` from `id_generator`, **no
   namespace symbol** (unnameable), `members` empty. `self_type_param.bounds.traits`
   = `[reflexive Self: __Integer, Add, Sub]` — built exactly the way
   `signature_trait` builds a hand-written trait's supertraits (`traits.rs:969`).
   The `where { Output = Self }` becomes bindings on the `Add`/`Sub` bounds, so
   `a + b : T` rather than `T::Output`.
2. **A synthetic `TraitImpl` of `__Integer` for each member** — synthetic
   `DefId`, `type_params: []`, `members: {}`, `member_decls: {}`. Registered via
   `register_trait_impl`, exactly like the memory-impl precedent.
3. **`TypeSet` gains `trait_index: TraitIndex`** (forward link to its generated
   trait).
4. **`Trait` gains `sealed: Option<Sealing>`** where
   `Sealing::Typeset(TypesetIndex)` (per [typeset-as-traits.md](./typeset-as-traits.md)'s
   internal-naming section — leaves room for a future `Sealing::Permits` for
   Java-style sealed struct hierarchies). This is the "this trait is closed, and
   here is the enumerable impl set" back-link.
5. **`Bounds.typeset` is deleted.** `resolve_identifier_as_bound` maps
   `SymbolKind::TypeSet { typeset_index }` → `BoundKind::Trait(TraitBound { trait_index: typesets[i].trait_index })`.

### 3.2 Why this shape

Everything downstream — `find_trait_impl`, `trait_implies` / `reachable_traits`,
`check_trait_conformance`, projection resolution, `type_implements_trait` — then
operates on `__Integer` with **no typeset-specific code path**. The generated
trait is plumbing; the `TypeSet` item stays the surface (name, `pub_span`,
`accesses`, `#[tag]`, hover, goto-def).

The only genuinely new mechanism is "a `Trait` with no AST node that is never
nameable." The memory impl already establishes both halves (synthetic `DefId`,
no `member_decls`, built outside the AST sweep).

### 3.3 Where it plugs into operator dispatch

`fn f<T: Integer>() { a + b }` — `T` is a `TypeParam` bounded by
`TraitBound(__Integer)`. `resolve_bounded_operator_method` (`operators.rs:237`)
currently does a **direct** match:
`bounds.traits.iter().any(|tb| tb.trait_index == add_trait)`. Change it to
`trait_implies(tb.trait_index, add_trait)` so a supertrait chain
(`__Integer: Add`) counts.

That single change **deletes** `is_typeset_bounded_assoc_type` and the
"trust any typeset for any operator" special case (`operators.rs:309, 536,
1094`, `generics.rs:642`). `+` on `T: Integer` then works for the same reason
`+` on `T: Add` works — and *only* if the typeset actually declares `: Add`.

### 3.4 Where the literal check finds members

`local x: T = 200` where `T: Integer`: `effective_bounds(T)` →
`TraitBound(__Integer)` → `traits[__Integer].sealed` →
`Sealing::Typeset(i)` → `typesets[i].members` → fold `literal_fits` over them.
The `Trait → Option<Sealing>` link is load-bearing here; it replaces today's
`bounds.typeset()` lookup.

---

## 4. Locked decisions

| # | Decision |
|---|---|
| a | **Nominal only.** No inline `i32 \| i64` union syntax in v1 (later sugar over an anonymous generated trait). |
| b | **Keep the `typeset` keyword and `typeset X { ... }` syntax.** Only addition: an optional bound clause, `typeset X: A + B { ... }`, putting a requirement on every member. |
| c | **`typeset` implies nothing.** Bounds written on it (`: Add + Sub`) are treated as supertraits of the generated trait; each member is statically checked against them (§6). A body over `T: Integer` may use `+` only because `Integer` declares `: Add`. |
| d | **`Bounds.typeset` disappears.** Typeset is represented by a generated trait; `Trait.sealed: Option<Sealing>` links back to the member list. |
| e | **Multiple typesets = ordinary multiple trait bounds.** `T: A + B` is two `TraitBound`s; the satisfying set is `members(A) ∩ members(B)` with no intersection code. An empty intersection is **not** diagnosed as an error (consistent with how `T: Add + Display` with no such type is not diagnosed) — at most a warning. `MultipleTypesetBounds` (E1048) is deleted. |
| f | **Literal coercion**: the only site that matters is a literal whose target type is an abstract `T` bounded by typeset(s). No defaulting anywhere — a bare literal with no concrete context stays an error. Replace `intersection_range.contains(v)` with `members.iter().all(|m| literal_fits(lit, m))`. |
| g | **Drop `TypeSet::intersection_range`.** Check each member separately (needed anyway for floats and for `A + B` intersection). `IntegerRange::for_integer_type` + `contains` stays as the per-member integer check. |
| h | **int literal → float member works**, in both the standalone (`local x: f32 = 0`) and typeset-member cases — one consistent rule (§5). The current hard error `report_integer_literal_for_float_type` (E1006) is **removed**. |
| i | **float literal → float type**: implement the two range TODOs — overflow-to-∞ → error, nonzero-literal-to-zero → error, subnormal → optional warning (§5). |
| j | **Correctly round f32 literals** by re-parsing the source slice, not casting the stored `f64` (§5.3). |
| k | **A member must be a distinct concrete impl target** — `ImplTarget::from_type(resolve(ty)).is_ok()` **and** a 1:1 `ImplTarget ↔ TypeIndex` mapping. v1: the 12 numeric primitives, `bool`, `char`, non-generic `struct`/`enum`. Excludes `Self`, abstract types, generics, slices, arrays, pointers, tuples (§6). `TypesetMemberNotInteger` (E1046) → `TypesetMemberNotConcrete`. |
| l | **`Self`** in member position → error ("a typeset lists concrete types, not `Self`"). `Self` in the bound clause → allowed, means "each member". |
| m | **Keep the `#[tag = "pointer_size"]` mechanism.** Tag stays on the `typeset` item; only the downstream check changes (per-member fold). |
| n | Typeset-name-as-a-type is already impossible (a bound is not a type), so `typeset A { A }` is not a case. `typeset A: B {}` / `typeset B: A {}` becomes a generated-trait supertrait cycle, caught by `signature_trait`'s existing cycle stack. |

---

## 5. Literal coercion — precise model

A literal's context type is always either **a concrete type** (ordinary fit
check) or **an abstract `T`** whose bounds include one or more typesets. In the
abstract case the literal must be valid for **every** member of **every**
typeset bounding `T` (monomorphization can substitute any of them). No context
type → error (wx has no literal defaulting).

Central helper: `fn literal_fits(&self, lit: LiteralValue, ty: TypeIndex) -> bool`,
covering all four cells below, called by both the all-members fold and the
existing concrete-target paths so behavior cannot drift.

| literal | integer member `M` | float member `M` |
|---|---|---|
| integer `n` (no `.`/exponent) | `n` in `IntegerRange::for_integer_type(M)` | `n` exactly representable in `M` — mantissa-span check |
| float `x` (`.` or exponent) | **never** (no implicit float→int truncation) | `parse(x, M)` finite, and nonzero if `x` is |

### 5.1 Integer → float member: mantissa-span check

```
n == 0 || (64 - n.leading_zeros() - n.trailing_zeros()) <= mantissa_bits
// mantissa_bits: 24 for f32, 53 for f64
```

A `u64` literal can never overflow or underflow either float type
(`u64::MAX ≈ 1.8e19` ≪ `f32::MAX ≈ 3.4e38`), so the span check is the *whole*
check — no range guard. Pass → the float holds `n` exactly, no approximation.
Fail → error, never a silent round.

This replaces the blanket `report_integer_literal_for_float_type` rejection: the
common `= 0` / `= 1` / small-constant cases now work; `= 16777217` for `f32` is
an error instead of silently `16777216`. Matches Zig
(`comptime_int` → float requires exact) and Rust's `From<Int> for Float`
policy (impls exist only for the provably-lossless pairs).

### 5.2 Float → float type: range checks

`str::parse::<fN>()` returns `Ok(±inf)` on overflow and `Ok(±0.0)` on
underflow (it only `Err`s on malformed syntax). So:

```
parsed = <target fN>::from_str(literal_text)          // see 5.3
if parsed.is_infinite() && literal not syntactically inf  → E FloatLiteralOutOfRange
if parsed == 0.0        && literal syntactically nonzero  → E FloatLiteralUnderflow
if parsed.is_subnormal()                                  → W (optional) LossyLiteral
```

"syntactically nonzero" = the mantissa digits are not all `0`. **No exactness
check** — that would reject `0.1` and contradict wx already accepting
`local x: f32 = 0.1`. The stored value is *the nearest representable value*;
relative error ≤ ½ ULP in the normal range (~6e-8 f32, ~1.1e-16 f64), worse in
subnormals — hence the optional subnormal warning.

New codes: `FloatLiteralOutOfRange`, `FloatLiteralUnderflow`. Rust
(`overflowing_literals`, deny) and Zig both hard-error the overflow case;
matching "overflow = error, underflow-to-zero = error, subnormal = warn" is
slightly stricter than both and defensible for a teaching language.

### 5.3 Double rounding — re-parse for f32

`Expression::Float` stores only the `f64` from parse time. `"x".parse::<f64>() as f32`
can differ from `"x".parse::<f32>()` for decimals sitting just past an f32
round-to-even boundary — the classic "double rounding" bug. Industry consensus
is to avoid it:

- **Rust** `f32::from_str` parses directly to f32, correctly rounded.
- **Go** `strconv.ParseFloat(s, 32)` is correctly rounded to float32; untyped
  constants use `big.Float` and round once at the destination.
- **C/C++** `strtof` is required correctly-rounded to `float` (C99+).
- **Java** `Float.parseFloat` had double-rounding bugs, since fixed.

wx already has this latent — it's just masked by `coerce_untyped_float_expr`
doing no checks. **Fix:** when the concrete target is `f32`, re-parse the
original source slice (`files.get(file_id).source[expr.span]`) with
`.parse::<f32>()`. Keep the stored `f64` for `f64` targets and for
`eval_const_expr` folding. Guard the re-parse behind "the AST did not already
flag this literal malformed" so nothing double-reports. Cost: one extra parse
per `f32` literal, only when an `f32` target is known.

Thesis line: *float literals are correctly rounded to their destination type
rather than rounded twice via `f64`.*

---

## 6. Member obligations & validity

### 6.1 Each member checked against the typeset's bounds (decision c)

Falls out of §3 for free. Register the synthetic `impl __Integer for i32` etc.,
then `check_trait_conformance` (`traits.rs:88`, Phase 3.5) iterates **all**
trait impls including synthetic ones and verifies the trait's supertraits are
implemented by the target — so `impl __Integer for i32` triggers "`i32: Add`?
`i32: Sub`?" via `find_trait_impl`.

`typeset Bad: Display { i32 }` where `i32: Display` doesn't exist → error there.
Two things to wire:

- **Anchor.** Conformance diagnostics anchor on `TraitImpl::span` (a real
  header). A synthetic impl has none — set `span` to the **member's type
  expression** in the `typeset` body, so the error underlines `i32` in
  `typeset Bad: Display { i32 }`.
- **Message.** Bespoke wording over the generic conformance one:
  `"member `i32` of typeset `Bad` does not satisfy the bound `Display`"`. Reuse
  `TypesetBoundViolation` (E1047) or a new code.

### 6.2 Member validity (decision k)

`ImplTarget::from_type(resolve(ty)).is_ok()` is the base predicate — it already
excludes `Self` (→ `TypeParam`), abstract types, `()`, tuples, function types,
bare pointers.

**Sharper constraint found in the impl machinery.** `register_trait_impl`
(`traits.rs:51`) buckets by `ImplTarget` constructor and rejects a second impl
of the same trait for the same constructor (`DuplicateTraitImpl`).
`ImplTarget::Struct(StructIndex)` and `ImplTarget::Array` are constructor-level,
not instantiation-level — so `typeset X { Box<i32>, Box<bool> }` generates two
`impl __X for …` that collide on `ImplTarget::Struct(box_idx)`. And
`find_trait_impl` (`mod.rs:4227`) does `.find(|(ti,_)| *ti == trait_index)` —
first match by trait index, then unify — so even if registration allowed it,
membership lookup could not disambiguate.

**v1 restriction:** members must have a **1:1 `ImplTarget` ↔ `TypeIndex`**
mapping — the 12 numeric primitives, `bool`, `char`, and non-generic
`struct`/`enum`. Reject generics, slices, arrays, pointers, tuples with an
explicit "typeset member must be a distinct concrete type" check (better message
than the downstream `DuplicateTraitImpl`).

**Fix path (later):** make `find_trait_impl` collect *all* trait matches in the
bucket and unify each candidate — the inherent-impl side already does this per
its doc comment (`mod.rs:2703`). Once that lands, generic-instantiation members
become safe.

### 6.3 Cycles (decision n)

`typeset A: B {}` / `typeset B: A {}` → `__A: __B` / `__B: __A`, caught by
`signature_trait`'s supertrait cycle stack (`traits.rs:986`) — **provided
generated-trait supertrait resolution goes through that same stack.** Ensure it
does. `typeset A: A {}` collapses into the reflexive `Self: __A` entry, same as
`trait A: A`.

---

## 7. Sequencing

Additive-first; the workspace compiles and the suite is green after every stage.

| Stage | Scope | Notes |
|---|---|---|
| **1. Representation** ✅ | Add optional `: Bounds` + `where { }` to the typeset AST + `parse_typeset_item` + `wx-fmt`. Thread an (unused) bound clause onto `TypeSet`. Members stay integer-only; `intersection_range`, `Bounds.typeset` stay. **No behavior change.** | Done. `Item::TypeSet` gained `bounds: Option<Spanned<BoundExpression>>`; parser mirrors `parse_trait_item`'s `: parse_bounds_expression()`; `wx-fmt` renders `: A + B`. `where { .. }` on a single bound comes free via `parse_bound` → `WithBindings`. prescan/signature untouched (`..`). No AST snapshot contained a typeset. |
| **2. Closed-trait membership** | Generate `__Typeset` + synthetic member impls; add `Trait.sealed` + `TypeSet.trait_index`; route `SymbolKind::TypeSet` bounds to `TraitBound`; route `type_in_typeset` through `type_implements_trait`; change `resolve_bounded_operator_method` to `trait_implies`; **delete `is_typeset_bounded_assoc_type`** and the operator special case. Add `: Add + Sub + … where { Output = Self }` to `std`'s `Integer`, and whatever ops `PointerSize` / `Mem::Size` actually need. | **The one `std/main.wx` edit** — do all snapshot re-accepts here. Audit `std` + `examples` for every operator applied to a typeset-bounded type or `Mem::Size` first. Synthetic `DefId`s allocated at a fixed point (end of Phase 2, registry order) for determinism. |
| &nbsp;&nbsp;↳ 2a ✅ | Data model: no `Sealing` enum (per review) — `Trait.typeset_index: Option<TypesetIndex>`, `TypeSet.trait_index: TraitIndex`. Backing-trait **shell** created in prescan next to the `TypeSet` (synthetic `DefId`, reuses the typeset's name symbol/span, no namespace symbol). | Done. Interleaved into the trait registry at the typeset's file position, so downstream `TraitIndex` values shift — snapshots accepted. |
| &nbsp;&nbsp;↳ 2b ✅ | `signature_typeset_backing_trait` (in `traits.rs`): resolves the `: A + B` clause into the backing trait's `self_type_param.bounds` (reflexive `Self: __X` first, mirroring `resolve_supertrait_clause`); generates + `register_trait_impl`s one empty `impl __X for <member>` per member; member-validity check relaxed from `is_integer()` → `ImplTarget::from_type(..).is_ok()`, `TypesetMemberNotInteger` (E1046) → `TypesetMemberNotConcrete`. `check_trait_conformance` now verifies each member against the clause (`bool` in `typeset T: Add` → `UnsatisfiedTraitBound`). | Done. `Bounds.typeset` still populated and still the thing consumers read — no behavior change yet. 3 new tests. |
| &nbsp;&nbsp;↳ 2c ✅ | The semantics flip. `SymbolKind::TypeSet` now resolves to a `TraitBound` on the generated trait; `BoundKind` enum, `Bounds.typeset`, `TypesetBound`, `type_in_typeset`/`concrete_type_in_typeset`, `intersection_range`, `MultipleTypesetBounds` (E1048), `check_written_bounds`/`report_redundant_typeset_binding` all **deleted**. Operator dispatch: `resolve_bounded_operator_method` → `abstract_operand_defers_operator` (uses `type_implements_trait` + `trait_implies`); `is_typeset_bounded_assoc_type` survives only for the not-yet-overloadable comparison path. Literal coercion: `ItemRegistry::int_literal_vs_typeset_bounds` + `TypesetLiteralFit` enum — walks the supertrait chain, checks the literal per-member, points the diagnostic at the offending member's span. `TypeSet.members` is now `Box<[Spanned<TypeIndex>]>`. New `CannotImplementTypeset` (E1083). `std`'s `Integer` / `PointerSize` given explicit operator bound clauses (`PointerSize` also `+ UnsignedInt`, was implied by the old magic). ~6 tests reworked; snapshots accepted; `wx-lsp` bound-display fixed. Workspace green, clippy clean. | Examples not checked (most pre-broken). |
| **3. Literal coercion** | Float parse moved AST→TIR; int→float exact check (§5.1); typeset-member fold for both literal kinds (§5); remove `report_integer_literal_for_float_type`. No `literal_fits` unification (per review — int/float paths kept separate, only `int_fits_float` shared). | `local x: f32 = 0` starts compiling; `local x: f32 = 16777217` starts erroring — flip the affected tests. |
| &nbsp;&nbsp;↳ 3i ✅ | Float parse relocated out of the parser. `ast::Expression::Float` is now payload-free (like `Char`/`String`); `parse_float_expression` keeps only a syntax gate (`f64::from_str().is_err()` → `InvalidNumericLiteral`, unchanged code). `body.rs` builds `ExprKind::Float { value: 0.0 }` (sentinel — an uncoerced float literal is already "type annotation required"). `coerce_untyped_float_expr` is the sole parse site: parses the source slice at the target's width (`f32` target → `parse::<f32>()` directly, correctly rounded, no f64 double-round; stored widened to f64), then `is_infinite()` → `FloatLiteralOverflow` (E1084), non-zero literal → `0.0` → `FloatLiteralUnderflow` (E1085). std's `f32` consts now snapshot as their exact values (fix landing). 3 AST tests reworked (`value` assertions dropped — moved to TIR), 5 new TIR tests. Workspace green, clippy clean. | |
| &nbsp;&nbsp;↳ 3ii ✅ | Int→float exact check (§5.1). The `report_integer_literal_for_float_type` hard error ("add a decimal point") is gone; `coerce_untyped_int_expr`'s float-target branch now does the significand-span check via `integer_exact_in_float(value, mantissa_bits)` (24/53) and on success **rewrites the node to `ExprKind::Float { value: value as f64 }`** (exact widening) so MIR/codegen never see an int-typed float. Fail → `IntegerLiteralNotRepresentable` (E1006, renamed from `LiteralTypeMismatch` — it was that code's only user). `fn f() -> f32 { 1 }` now compiles; `{ 16777217 }` errors. 1 test flipped, 2 TIR + 1 wasmtime codegen test added. | |
| &nbsp;&nbsp;↳ 3iii ✅ | Typeset-member fold for both literal kinds. `TypesetLiteralFit` enum and the `*_typeset_fit` / `typeset_fit` `ItemRegistry` methods **deleted**; replaced by pure queries `typeset_bounds_of` (no longer needed — inlined) and `first_unfit_member`, plus one `Builder` method `coerce_literal_to_typeset_bound(rc, span, target, member_fits)` that walks `effective_bounds` → `reachable_traits` → typeset members with an early `break`, remembers `(bool, Option<(TypesetIndex, Spanned<TypeIndex>)>)` on the stack, and reports its own diagnostics (`report_typeset_misfit` slices the literal from its span, resolves names from `self`). Predicates: int member → `IntegerRange`, float member → `integer_exact_in_float` (int literal) / parse-at-width finite-and-not-underflowed (float literal), other → never. An **all-float** typeset makes `typeset Float { f32, f64 }` usable; a **mixed** `{ i32, f32 }` accepts an int literal fitting every member (the `Int` node rides to mono and MIR turns it into a `Float` const for a float instantiation — `mir/mod.rs` two sites) and rejects float literals on the int member. The dead `#[tag="pointer_size"]` branch in `coerce_untyped_int_expr` (slice indexing coerces to `M::Size`, an assoc projection the typeset branch already handles) **removed** — and with it the `#[tag = "pointer_size"]` attribute on `std`'s `PointerSize` (nothing reads that tag any more; dropping the interned string shifts symbol ids → snapshots re-accepted). Typeset member resolution now runs the `contains_infer` check inline (`report_infer_in_signature`, E1051, `pub(super)`) so `typeset X { Box<_> }` is rejected the same way `impl T for Box<_>` is, and the member is dropped so no `impl __X for Box<_>` is registered. 4 TIR + 1 wasmtime test. | |
| **4. Multi-typeset** ✅ | Folded into 2c — `Bounds.typeset` deleted, `MultipleTypesetBounds` (E1048) retired, no `EmptyTypesetIntersection`. | |
| **5. Widen members** ✅ (mostly) | Folded into 2b — non-integer concrete members allowed via `ImplTarget::from_type(..).is_ok()`, `TypesetMemberNotInteger` → `TypesetMemberNotConcrete`. `Self`/abstract already rejected. `typeset Float { f32, f64 }` usable as of 3iii. **Remaining:** the 1:1-`ImplTarget` gate (a generic-struct / slice / array member collides in `trait_impl_dispatch` and only gets the downstream `DuplicateTraitImpl`, not a typeset-specific message). | |

`IntegerRange` stays useful for the per-member integer check throughout — just
not stored on `TypeSet`.

---

## 8. Implementation notes

No user code exists yet, so breaking changes are free — these are just the
things that need doing, not hazards.

- **`std` bounds must be spelled out (Stage 2).** Today `T: Integer` and
  `T: PointerSize` get `+` / indexing arithmetic for free via the blanket
  trust. After the change the typeset must declare `: Add + …` for the body to
  use it. Grep `std` + `examples` for every operator applied to a
  typeset-bounded type or `Mem::Size` and add the matching bounds to `Integer`
  / `PointerSize`.
- `report_integer_literal_out_of_typeset_range` hard-codes "safe range is
  `a..=b`" — reword for the per-member / float world
  (`"literal `N` is not representable as member `f32` of typeset `X`"`).
- `type Size: PointerSize + UnsignedInt` is a `BoundList` today; confirm it
  still resolves once `PointerSize` is trait-like (same path as `A + B`).
- **Comptime never sees a typeset bound** (const exprs aren't generic), so
  const-context literal coercion stays concrete-target. Add a test asserting it.
- `wx-lsp` hover / goto-def / find-refs on a typeset name and its members must
  still resolve. Keyword kept → minimal, but there are snapshots.
- Any `std/main.wx` edit shifts every offset-based snapshot — keep the std edit
  to Stage 2 and do one `cargo test -p wx-compiler` + `cargo insta accept`
  sweep.
