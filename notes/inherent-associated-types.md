# Inherent associated types

Status as of 2026-11-18: **planned**, nothing implemented. `impl S { type X
= i32; }` parses, but checking panics at the `unimplemented!` for
`ImplItem::AssocType` in `decls.rs`; `E2035 AssociatedTypeInInherentImpl`
is defined and never reported.

Motivation: a name for a type that depends on an impl's parameters,
written once beside the methods that use it. `examples/arena` repeats
`Mem::&u8` in every signature where `type Ptr = Mem::&u8;` would do.

## Why Rust has not stabilized them

`inherent_associated_types` (tracking issue #8995, open since 2013) is an
incomplete feature. From memory, not rechecked against current rustc:

- **Selection while lowering written types.** rustc resolves `Foo::X`
  before type checking, with no inference context. Rust lets disjoint
  impls share a name (`impl Foo<i32> { type X = u8; }` beside
  `impl Foo<u32> { type X = u16; }`), so choosing needs unification and
  where-clause evaluation; the prototype builds a temporary inference
  context in lowering, which breaks on `Foo<_>::X` and in generic code.
- **A new alias kind** (`ty::Inherent`), normalized lazily, meeting the old
  solver's eager normalization; a steady source of ICEs.
- **Regions:** higher-ranked types (`for<'a> fn(S<'a>::X)`), implied
  bounds and well-formedness, with regions unknown at selection.
- **Query cycles:** an impl's where-clauses, a struct's fields or bounds
  naming the alias; selecting needs the impl's predicates, which mention it.
- **Bounds:** free type aliases do not enforce theirs (`lazy_type_alias`);
  an inherent one must.
- **Precedence** against a trait's associated type of the same name.
- Low priority: module aliases and helper traits work around it.

## What wx already has

- **One candidate per head and name.** `register_inherent` (`impls.rs`)
  reports a name defined in two inherent impls of the same head even when
  their targets are disjoint (`Wrap<u32>` and `Wrap<i32>`). Rust's
  selection problem does not arise: choosing is a lookup and a one-sided
  match.
- **Bounds are obligations, never filters.** `select_inherent_member`
  (`members.rs`) matches the target with `match_impl_target` and records
  the impl's bounds with `record_bounds_check`. Inherent constants in types
  (`Self::SIZE`) already take this path.
- **`Infer` matches nothing** (`match_pattern`), so `Wrap<_>::X` cannot
  pick an impl by accident.
- **A type-tier inherent member exists:** a function is bound in both tiers,
  and `resolve_type_member_path` tries `select_inherent_function` before
  the trait members.
- **No regions**, demand-driven signature queries with cycle detection,
  and monomorphization after checking.

Together these make resolution commute with substitution:
`resolve(subst(Wrap<T>::X)) == subst(resolve(Wrap<T>::X))`. Generic code
and its monomorphized instance agree on what `Wrap<T>::X` is, and a lookup
that fails in generic code is a final error, never deferred to lowering.

**Language commitment:** inherent member names stay unique per head. Lifting
that rule (disjoint impls sharing a name) brings back Rust's selection
problem. Type-level functions over instances belong in traits.

## Decisions

1. **An impl-owned type alias, expanded where written.** The member is a
   type alias whose generic frame is its impl's; resolving `Foo<A>::X`
   matches the impl target, substitutes the impl arguments into the value,
   and returns the result. No `Type` variant: MIR and codegen never see it.
   A lazy variant would only help if the receiver could be unknown when the
   path is resolved, which unique names rule out.
   Storage: the type alias declaration (`TypeAliasIdx`) with an impl owner
   and a `MemberKind` for it, not `AssocTypeIdx`: `AssocTypeSignature`'s
   `declared_bounds` and `clauses` have no meaning here, and an
   `AssocTypeIdx` inside a `TypeProjection` must name a trait declaration.
2. **Inherent first**, as for values and in Rust. In
   `impl Iterator for S { type Item = i32; }` beside `impl S { type Item =
   u8; }`, `Self::Item` is `u8`; `<Self as Iterator>::Item` names the
   trait's. A conformance error caused by this shadowing gets a note
   pointing at the qualified form.
3. **No parameters** (`type Ptr<M> = ...`), as GATs are deferred
   (`generic-associated-types.md`); reported, likely as E2035.
4. **No bounds on the member.** The impl syntax has none; the impl's own
   bounds are checked at every use.

## Stages

1. **Declarations** (`decls.rs`, `ImplItem::AssocType` in an inherent
   impl): register the alias under `BindingKey::ty`, keeping its `pub`.
   The duplicate checks in the impl's `bindings` and in `register_inherent`
   then cover clashes with a function of the same name. A trait impl's
   associated type still rejects `pub`; update the doc comment on
   `ast::ImplItem::AssocType`.
2. **Signature query:** the value resolved in the impl's frame, `Self` its
   target. Preserve the query-stack unwind on every path after pushing a
   frame.
3. **Selection:** generalize `select_inherent_function` into a type-tier
   inherent lookup returning a function type or the substituted alias;
   update the `unreachable!`s that assume a type-tier inherent member is a
   function. Check visibility (`member_accessible`) on the type path and
   record the resolution for hover and go-to-definition.
4. **Value paths and patterns:** `Self::X::new()`, `S::X::Y`, and
   constructors or patterns through the alias, as free type aliases
   behave.
5. **Rejections:** an alias as an impl target (`impl S::X`,
   `impl Tr for S::X`: `ImplDispatch` is built before signatures, and only
   intrinsic aliases are targets today); arguments on the member
   (`S::X<i32>`); the member in value position.
6. **LSP:** completion of inherent aliases after `Foo::` in type position.
   The formatter already round-trips the syntax.
7. **Examples:** use it in `examples/arena`; check and build the touched
   examples.

## Edge cases

| Case | Expected |
| --- | --- |
| `Wrap<T>::X` in generic code, `impl<U> Wrap<U> { type X = U; }` | `T`; an execution test runs the monomorphized instance |
| `Wrap<T>::X` with only `impl Wrap<i32>` defining it | error when checking, not deferred |
| `Wrap<_>::X` | error asking for the argument |
| `impl<T: Copy> Wrap<T>`, used with a `U` without `Copy` | the bounds obligation fails at the use |
| `type A = Self::B; type B = Self::A;`, or `type A = Self::A;` | one cycle diagnostic |
| The impl's bounds name its own alias | cycle diagnostic; splitting the header query into target and bounds could lift it later |
| `struct Node(next: Node::Ptr)` with `type Ptr = heap::&Node` | accepted: the impl header must not depend on the struct's field types |
| `type Inner = Node` as a field of `Node` | infinite size, from layout |
| A struct's bounds name its own alias | cycle diagnostic |
| A projection as the value: `impl<I: Iterator> P<I> { type Item = I::Item; }` | substituted, then normalized by the solver |
| A projection as the receiver: `T::Out::X` with `T: Tr<Out = Wrap<i32>>` | selected through the assumed equality |
| `<i32 as Tr>::Out::X` | to verify: `select_inherent_member` normalizes with `RewriteFlags::EQUALITIES` only |
| `func X()` and `type X` in one impl, or in two impls of one head | E2000 |
| A private alias in a public signature | accepted: expansion leaves only the underlying type |
| `pub type` in a trait impl | still an error |
| An inherent `Item` where a trait requires `Item` | does not satisfy the trait |
| `<S as Tr>::X` beside an inherent `X` | the trait's: the qualified path skips inherent lookup |

## Validation

Checking tests for types and diagnostics, a Wasmtime execution test for
the generic and monomorphized case through `backend::emit`, LSP tests for
hover and completion, and the touched example packages built explicitly.
