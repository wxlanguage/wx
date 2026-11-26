# Member selection and equalities

Status: both decided 2026-11-26 (decision 2: option C, with its design
points), not implemented.

Signature construction records types as written: a constant in a type stays
a reference, a projection keeps its written receiver, and every check is an
obligation run once all signatures exist. Name resolution is the exception:
selecting `Name` in `X::Name` reads what the scope says about `X`, and today
that includes the equalities written in bounds. Both decisions below are
about how far equalities take part in that, and in proving bounds.

Measured on 2026-11-26: neither use below occurs in core or in any example;
only compiler tests rely on them.

## 1. A member is selected off the receiver as written (decided)

```wx
func f<T: Tr where { A = W }>(x: T::A::Inner) {}
```

Today `select_associated_type` and `select_inherent_member` normalize the
receiver with `RewriteFlags::EQUALITIES` first, so `T::A` is read as `W` and
`Inner` is found on `W`. Writing `T::A` there is redundant: in this scope it
is `W`, which can be named directly.

Decided: a member is found from what is declared about the receiver as
written, or from its head constructor when it has one, never from what the
receiver is equal to. The projection itself can always be written.

| What the scope says about `T::A` | `T::A::Inner` |
|---|---|
| a bound supplies `Inner` (`type A: Tr2`, or `A: Tr2` in the `where`) | resolves, to `<<T as Tr>::A as Tr2>::Inner`; checking normalizes it |
| nothing | error: no associated type `Inner` on `<T as Tr>::A` |
| `A = W`, no bound | the same error, with help: "`<T as Tr>::A` is `W` here; write `W::Inner`" |
| `A = U` for a parameter `U`, no bound | the same, "write `U::Inner`" |

With both an equality and a bound, selection reads only the bound:

```wx
func f<T: Tr where { A = W, A: Tr2 }>(x: T::A::Inner) {}
```

`T::A::Inner` is `<<T as Tr>::A as Tr2>::Inner`. Checking normalizes it to
`<W as Tr2>::Inner` and then to `W`'s value, and the clause `A: Tr2` becomes
`W: Tr2`, proved where it is written (`env-normalization.md`). A trait only
`W` has is not reachable through `T::A`. Every way to reach `Inner` names
where it comes from:

| Written | `Inner` is found by |
|---|---|
| `T::A::Inner` | a bound declared for `A` |
| `<T::A as Tr2>::Inner` | the written trait; checking proves `T::A: Tr2`, by `W`'s impl |
| `W::Inner` | `W` directly |

- A concrete head (`Need<T::Item>::Output`) selects by its constructor,
  whatever its arguments.
- The help reads the written equality for exactly that projection
  (`Solver::projection_equality`), on the error path only: no normalization,
  nothing stored. Left out when the equality is `Pending` or ambiguous.
- `T::A::new` behaves the same: an abstract receiver has no inherent
  functions, so the trait lookup fails and the help applies.

Why: construction then normalizes nothing, so it cannot reach impl values,
compiler-answered values, field walks, or constant evaluation over
signatures not built yet; it holds by construction rather than by the
convention "construction normalizes with `EQUALITIES` only". Resolution no
longer depends on the solver's readiness, which is what the "pending
unqualified selection" diagnostics exist for.

The rule is about paths, wherever they are written. Bodies resolve type
paths with the same resolver (`resolve_type_member_path`), so `T::A::new()`
or `local y: T::A::Inner` in a body gets the same error, though every
signature exists by then and the rewrite would be safe: one rule, not a path
valid in a body and invalid in a signature. Nothing else about `T::A`
changes: `local x: T::A = w` checks, since checking normalizes `T::A` to
`W`, and `x.method()` or `x.field` look up members by the value's
normalized type.

Rejected: deferring selection. Recording `T::A::Inner` as an unresolved
member (`Type::Member { receiver, name }`) and picking the trait in the
solver would allow the path, but adds a type kind every consumer handles
(flags, substitution, impl matching, normalization, formatting, lowering),
moves "no such member" and ambiguity into normalization failures reported
where the type is first normalized rather than where it is written, and
makes the language server need the solver to answer go-to-definition. The
path it allows is redundant.

Consequences:

- `select_associated_type` and `select_inherent_member` drop their
  normalization.
- An inherent impl for specific arguments (`impl Need<i32>`) is not matched
  through an equality (`Need<T::Item>::new` with `Item = i32`). Nothing
  relies on it; if something does later, argument matching can move to
  checking.
- Selection asks `check_assumed_trait` for an abstract receiver, and its
  third source compares by equalities too (decision 2). Under this decision
  selection takes only the first two: stated on the receiver's path, or of
  the receiver as written.

Not decided here: requiring the trait to be named for a projection off a
concrete type (`<S as Tr>::A`), so adding another trait with an `A` later
cannot make the path ambiguous.

## 2. Evidence carried along equalities (decided: C)

`check_assumed_trait` answers whether the facts in scope prove `ty: Trait`
for an abstract `ty`, from three sources:

1. a declaration on `ty`'s path (`type Item: Marker`);
2. a clause stated of `ty` as written;
3. a clause stated of another subject that means the same as `ty` under the
   scope's equalities: both are normalized with `EQUALITIES` and compared.

```wx
// `U: Marker` is stated; `T::Item` is `U`, so `T::Item: Marker`.
func f<T: Container where { Item = U }, U: Marker>(x: Need<T::Item>) {}
// `T::Item: Marker` is stated; asked of `U` once `T::Item` normalizes to it.
func g<T: Container where { Item = U } + Container where { Item: Marker }, U>(
    x: <Wrap<T::Item> as Result>::Output) {}
```

The second shape is the one normalization needs: it rewrites `T::Item` to
`U`, and a fact stated about `T::Item` must still be found for `U`, or
normalizing loses it. `env-normalization.md` relies on this ("wx resolves
equalities where lookup reads them", instead of normalizing clause
subjects as rustc's `param_env` does).

Only equalities are read, never definitions or values: it runs inside trait
selection for abstract types and while an impl's requirements are proved,
where reading definitions could select the impl being proved, and during
construction, where it would reach signatures not built yet. Only abstract
meanings count; a concrete type takes its traits from impls.

This is the last use of `RewriteFlags::EQUALITIES` alone once decision 1 is
in. The flag set allows eight combinations and three are used, each a
superset of the last (`EQUALITIES`, `EQUALITIES | DEFINITIONS`, `ALL`).

Options:

- **A. Keep carrying evidence, as its own operation.** "The meaning of an
  abstract type under the scope's equalities", following
  `projection_equality`, replaces normalizing with a flag. No change in
  behavior. Normalization keeps two forms, with and without constant values.
- **B. Stop carrying evidence.** A fact holds of the subject it is written
  about. The first shape still works when the asking site normalizes first
  (`Need<T::Item>` is `Need<U>`, and `U: Marker` is stated). The second
  breaks unless clause subjects are normalized when the env is made
  (rustc's approach), which revisits `env-normalization.md`.
- **C. Rewrite clause subjects when the env is completed (rustc's
  approach).** An item whose clauses mention a projection an equality in
  scope rewrites gets a completed env, as a trait impl function's `Self`
  entry does (`complete_frame`), with `T::Item: Marker` and `Item = U`
  becoming `U: Marker`. Lookup then compares subjects by identity (sources 1
  and 2), the per-query scan over assumed subjects goes, and `RewriteFlags`
  collapses to normalization with and without values. Open points: the
  env's own equalities must rewrite its other clauses, which
  `env-normalization.md` ruled out only for `Self` entries (they reduce
  through definitions); more completed envs, one obligation each; and
  whether a declared bound reaches through an equality (`type Item: Marker`
  with `Item = U` giving `U: Marker`), which today it does not.

### Option C in detail

What it changes for code:

- Both shapes above prove what they prove today: the question and the fact
  meet in normal form (`Need<T::Item>` asks `U: Marker`; `Item: Marker` is
  now `U: Marker`).
- A shorthand path cannot use a fact that only exists rewritten: with
  `Item = U` and only `Item: Project` written, `U::Output` is not found,
  since construction reads the signature env. Write `<U as Project>::Output`
  (checking proves `U: Project` from the completed env) or bound `U` itself.
  This is the rule `env-normalization.md` already sets for `Self` entries,
  and rustc's; `equivalent_subjects_support_unqualified_and_qualified_members`
  changes.
- A clause whose subject rewrites to a concrete type (`Item: Marker` with
  `Item = U::Item` and `U::Item = i32`, giving `i32: Marker`) is proved
  where it is written: dropped if it holds, reported at the bound if not.
  Today it is never checked and does nothing.
- A clause whose subject rewrites to a type with a parameter that is not
  abstract (`Item = Wrap<U>` with `Item: Marker`) is E2085, unsupported,
  until such clauses are replaced by the requirements of the one impl that
  matches (`env-normalization.md`). Today it does nothing, and a use needing
  `Wrap<U>: Marker` fails far from the cause.
- Diagnostics name the normalized clause (`U: Marker`); pointing back at
  the written bound is `env-normalization.md`'s open question 6d-3.

What it changes inside: `check_assumed_trait` loses its third source and
its scan over assumed subjects; `NormalizeSelfEntry` generalizes to
completing any frame whose clauses rewrite, first in the frame's checks;
requirements stay as written; the solver is asked about normal forms only
(`find_trait_impl_query` already asks about the normalized receiver too).

#### Completing an env inside itself

```wx
func f<T: Container where { Item = U, Item: Marker }, U>() {}
```

The env holds two clauses:

```
(1)  T::Item = U        an equality: a rewriting rule
(2)  T::Item: Marker    a fact about a type
```

Completing it rewrites (2) to `U: Marker`, by (1), which is in the same
env: the env rewrites its own clauses. A `Self` entry is different: its
`<Wrap<T> as Container>::Item: Show` reduces through the impl's
`type Item = T`, a definition outside the entry, so `env-normalization.md`
could normalize it in the parent env with the entry's clauses not affecting
each other. C changes that sentence.

The rules must not be rewritten. Rewriting (1) by itself gives `U = U`
(E2100 today), and nothing knows `T::Item` is `U` any more, as a dictionary
of substitutions applied to itself turns every entry into "x means x". So:

- equalities keep their projection as written: they are the rules;
- trait clause subjects and equality values are rewritten by them.

Rules chain, in either order of declaration:

```wx
func g<T: Container where { Item = U::Item, Item: Marker },
       U: Container where { Item = i32 }>() {}
```

`T::Item: Marker` becomes `U::Item: Marker`, then `i32: Marker`, which is
concrete and proved at the bound.

Rules can loop:

```wx
func h<T: Container where { Item = U::Item },
       U: Container where { Item = T::Item }>() {}
```

`T::Item` to `U::Item` to `T::Item` never reaches a normal form;
normalization treats a loop through equalities as a tautology and keeps the
type as written, so a clause about `T::Item` stays as written too.

#### Envs are made, never changed

Completion makes a new env and points the frame at it (`complete_frame`);
no env changes once made. Caches key by env (`Normalization`, finiteness's
instances, verdicts), and a child's answers read its parents' clauses
through the chain under the child's own key, so changing an env in place
would leave answers computed with fewer facts standing under a key that
now means more. With a new env, an index means one set of facts for its
whole life, and a reader before completion gets a smaller, consistent
view.

A frame keeps its signature env when nothing would change: its own
clauses rewrite to themselves, its rules rewrite nothing it inherits, and
its parent's env was kept. Only a frame where something can rewrite (an
equality in scope, or clauses about a type that reduces through
definitions) gets a completion obligation at all. Interning envs by
content is not worth it: clause subjects name the item's own parameters,
so two items' envs are almost never equal, and the one case that pays,
"completed equals written", is the keep rule.

#### General where clauses

Planned: every item gets a `where` stating facts about any type in scope,
its parents' parameters included, replacing the `Self` entry:

```wx
impl<T: Container> Show for Wrap<T> {
    func show() where { Self: Debug, T::Item = U, T::Item: Marker, Wrap<T>: Eq } { ... }
}
```

What it changes for C:

- **The `Self` entry is no longer special.** `NormalizeSelfEntry` becomes
  the general completion of an item's clauses; clauses about the impl's
  target are clauses about a type that reduces through definitions.
- **A child's rules rewrite its parent's facts.**

  ```wx
  impl<T: Container where { Item: Marker }> S<T> {
      func m<U>() where { T::Item = U } { /* U: Marker here */ }
  }
  ```

  `T::Item: Marker` is the impl's fact, `T::Item = U` the method's rule;
  in `m` the fact reads `U: Marker`, which the impl's env, shared by every
  member, cannot hold. So a completed env needs the inherited facts its
  rules rewrite, not only its own clauses.
- **Subjects that are not abstract become ordinary.** `Wrap<T>: Eq`, or
  `Self: Debug` with `Self` as `Wrap<T>`, has a parameter but is not
  abstract: E2085 in `env-normalization.md`, now something written on
  purpose.
- **A child's equality on a parent's projection** (`T::Item = U` in a
  method of an impl whose `T` says `Item = V`) can conflict with the
  parent's.
- **Conformance** compares an impl member's clauses with the trait
  member's contract (E2095); with arbitrary clauses that comparison must
  be between completed clauses.

Decision 1 is unchanged (a shorthand path resolves from bounds written in
scope, a child's `where` included), as are replacing a rewritten clause
and whether declared bounds reach through an equality.

#### Decided (2026-11-26)

1. **Env shape: flat per item.** A completed env holds every clause in
   scope, its parents' included, rewritten by every rule in scope, as
   rustc's `param_env`; lookup reads one run, with no chain walk. Inherited
   facts are copied only into items where something rewrites; the others
   keep their signature env.
2. **Equalities: the projection without the env's own rules.** An
   equality's projection is normalized with definitions and its parents'
   rules only; its value and every other clause's subject with every rule
   in scope. `Item = U` stays `T::Item = U`, and
   `<Wrap<T> as Container>::Item = X` reduces through `type Item = T`.
3. **A subject that is not abstract is replaced by the requirements of the
   one impl that matches.** `Wrap<T>: Eq` with `impl<X: Eq> Eq for Wrap<X>`
   becomes `T: Eq`; with no matching impl it is an error at the clause. A
   concrete constructor takes its traits from its one impl, so the clause
   means exactly that impl's requirements. This replaces E2085 for these
   clauses.
4. **A child's equality on a projection its parent fixes is a conflict**,
   reported at the child's clause. A refinement adds facts; it does not
   override them.
5. **A rewritten clause replaces the written one.** The solver is asked
   about normal forms only, enforced by a debug assertion.
6. **Declared bounds are lent through an equality.** `type Item: Marker`
   with `Item = U` gives `U: Marker` in the completed env. Sound: impl
   conformance proves every declared bound, so whatever `U` stands for at
   a use is `Marker`. This reverses `check_assumed_trait`'s "not lent".
7. **Duplicate and conflict checks run again on completed clauses.** An
   exact duplicate is dropped; two equalities that disagree once rewritten
   are a conflict at the later bound.
8. **Constant clauses are rewritten like trait clauses.**
9. **Conformance compares completed clauses** on both sides: the impl
   member's, and the trait member's contract instantiated for the target.
   Follows from 5: a clause exists only in normal form.

Why lookup carries evidence today: it was added in September
(`tir-assumption-context-plan.md`, checkpoint 3), before any env was
normalized; envs were made in construction, which does not normalize, and
the checkpoint avoided new state, obligations, or passes. When
`env-normalization.md` added the completed env on 2026-10-31, it kept that
choice for this case in one line rather than deciding it again. Nothing in
the current design requires it.

Decided 2026-11-26: option C. A and B are not pursued.
