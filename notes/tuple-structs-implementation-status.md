# Tuple structs — implementation status (as of 2026-09-12)

## Status

In progress, does not compile. This note exists to resume work without
re-deriving the design decisions below — several of them reverse an earlier,
already-approved plan (`/Users/melkam/.claude/plans/hazy-growing-stream.md`,
now stale — see "Superseded plan" at the bottom).

## What this feature is

`struct Point(i32, i32);` — a positional/tuple-shaped struct, constructed as
`Point(5, 2)` and destructured as `local Point(x, y) = p;`. First, smaller
step toward a future `variant` item (Rust-style discriminated union, compiler
managed tag). Scope is compiler pipeline only (parser → TIR → MIR → codegen);
wx-fmt and wx-lsp just need to not panic on the new syntax.

## Part 1 — already landed and compiling on its own (before the big pivot)

These are done, correct, and independent of the construction-syntax pivot
described in Part 2. If the crate is made to compile again, none of this
needs revisiting.

### `StructInit` evaluation-order fix

**The bug** (pre-existing, not tuple-struct-specific): `Point::{ y: fetch_y(), x: fetch_x() }`
on `struct Point { x: i32, y: i32 }` used to evaluate `fetch_x()` before
`fetch_y()` at runtime, even though the user wrote `fetch_y()` first. Cause:
`aggregates.rs`'s struct-literal builder stored each field's built
`Expression` into a `field_slots[declared_index]` array (indexed by
declaration position, not source-writing order), and MIR's lowering later
walked that array in stored order — so evaluation order silently became
declaration order instead of source order.

**The fix**:
- `tir::ExprKind::StructInit.fields` changed from `Box<[Expression]>` to
  `Box<[(FieldIndex, Expression)]>`, populated in **source-written order**
  (a plain `Vec` pushed to during the field-processing loop, not a
  slot array indexed by declared position).
- `aggregates.rs::build_struct_init_expression`: `ordered_fields: Vec<(FieldIndex, Expression)>`
  replaces the old `field_slots: Vec<Option<Expression>>`; the final
  "has_field_errors → return early with empty fields" branch was **removed
  entirely** — since errors are already diagnosed, there's nothing unsafe
  about handing back whatever fields did build (`ordered_fields.len() < field_count`
  is allowed; the caller decided this was fine and simpler than forcing an
  empty box).
- `mir/mod.rs`'s `StructInit` lowering: evaluates `fields` in array order
  (now = source order, so side effects run correctly), then permutes the
  **already-lowered** `Expression` values into physical layout slots using
  each entry's own carried `FieldIndex` (`aggregate.physical(usize::from(decl))`)
  — same permutation step as before, just fed a per-entry index instead of
  assuming array position == declaration index.
- `TupleInit` (plain tuples) was checked and does **not** have this bug —
  tuple elements have no name-based reordering possible, so source order
  already equals declaration order there. No change needed.

### `.field` access simplified to carry `FieldIndex`, not a name

While reviewing the ordering fix, realized `ExprKind::FieldAccess.field` and
`PlaceKind::Field.member` (both `Spanned<SymbolU32>`) only ever get resolved
by name **once**, at construction (`paths.rs::build_object_access_expression`,
via `resolve_struct_field`, which already returns a `FieldIndex`) — nothing
downstream ever re-looks-up the name. Changed both to `Spanned<FieldIndex>`,
resolved once at construction time. This let three MIR consumers
(`mir/mod.rs`'s `FieldAccess` lowering, `mir/builder/places.rs`'s two sites)
drop their `self.tir.items.structs[..].lookup[&name]` hashmap lookup
entirely — they now just do `aggregate.physical(usize::from(member.inner))`
directly. No `StructKind` matching needed there at all, since a `FieldIndex`
already unambiguously identifies the field regardless of struct shape (and
`.field` syntax can in fact never target a tuple struct in the first place —
tuple structs have no field names — so this was always vacuously Record-only).

### Dead-field-write lint (`tir/builder/mod.rs`) generalized to both `StructKind`s

Was Record-only, reading `struct_.fields.iter()` flatly. Rust's own
`dead_code` lint fires on unused tuple-struct fields too, so this now
matches on `StructKind::Record`/`StructKind::Tuple` and reports for both —
"field `x` is never read" for named fields, "field 1 is never read"
(positional) for tuple fields. `TupleFieldInfo` gained an `accesses: Vec<FieldAccess>`
field to make this possible (previously had none, since nothing populated
it) — **note: nothing populates it yet** for tuple structs, since
construction/destructuring for tuple structs weren't wired up until the work
described below. The lint code is ready; the push sites (construction,
destructuring) need to remember to push into it once they're finalized (see
"Remaining work" below — `bind_tuple_struct_pattern_element` in `control.rs`
**does** already push `FieldAccessKind::Read` there for destructuring; the
still-unwritten construction path needs to push `FieldAccessKind::Init`
too).

### `field_visibility` generalized to both `StructKind`s

Was Record-only (`modules.rs`). Since it only ever reads a `pub_span` (a
field both `StructField` and `TupleFieldInfo` have), generalizing it to
match on `StructKind` and read `pub_span` from either shape was free — no
duplicated logic, just two match arms doing the identical thing.

`report_private_field` (the `.field`-access privacy diagnostic, same file)
was **deliberately left Record-only** — confirmed against Rust's own
behavior (`error[E0616]: field \`1\` of struct \`Foo\` is private` only ever
fires for `x.1`-style field access, which wx doesn't have for tuple structs
at all — no `.0`/`.1` syntax). A **separate** per-position privacy
diagnostic for tuple-struct pattern destructuring was added instead — see
below.

### Pattern destructuring rewrite (`tir/builder/control.rs`) — done, compiles

This was a full rewrite, already complete and compiling on its own:

- `collect_pattern_bindings` (the public entry point, `pattern: &Spanned<ast::Pattern>`)
  is now a thin wrapper calling a new private `collect_pattern_bindings_at`
  that takes `(pattern: &ast::Pattern, span: TextSpan, ...)` separately —
  needed because `ast::TupleStructPatternItem::Element` holds a bare
  `ast::Pattern` (no `Spanned` wrapper of its own; the surrounding
  `Separated<Spanned<_>>` already carries the span), so there was no
  `&Spanned<Pattern>` to hand the old signature for a tuple-struct pattern
  element specifically.
- `collect_struct_pattern_bindings` (the `Path::{ ... }` arm): updated for
  the new `ast::Pattern::Struct { path, items }` shape (was `{ path, fields,
  rest }` — `items` is the **raw parsed sequence**, since an earlier session
  decided the parser must not assume how many `..` markers are legal or
  where; TIR decides). Now: splits `items` into `fields: Vec<&PatternField>`
  and `rest_spans: Vec<TextSpan>` by hand; reports a new
  `DuplicateRestPattern` (E1087) diagnostic for every `..` beyond the first;
  rejects the pattern with a new `TupleStructBracePattern` (E1088)
  diagnostic if the resolved struct is actually `StructKind::Tuple` (you
  can't destructure a tuple struct with `Point::{ ... }`).
- New `collect_tuple_struct_pattern_bindings` (the `Path(...)` arm, for
  `ast::Pattern::TupleStruct { path, elements }`): implements **Rust-style
  "rest anywhere"** semantics — elements before the (at most one) `..` bind
  the struct's first fields by position, elements after it bind the last
  fields (`back_start = field_count - after.len()`); with no `..`, element
  count must match exactly. Rejects the pattern with a new
  `RecordStructPositionalPattern` (E1089) diagnostic if the resolved struct
  is actually `StructKind::Record`. Arity mismatch reuses the existing
  generic `TypeMistmatch` code (same convention plain tuple patterns
  already use for their own arity mismatches — no new code needed there).
- New `bind_tuple_struct_pattern_element` (per-position binding helper):
  looks up the field's type via `StructKind::Tuple`, substitutes if generic;
  **skips the privacy check entirely for a bare `_`** (discarding a field is
  not reading it — `local Point(x, _) = p;` on `struct Point(pub i32, i32);`
  from outside the declaring namespace succeeds); otherwise checks
  `field_visibility` + `is_accessible_from` and reports a new
  `PrivateTupleField` (E1090) diagnostic (`"field {position} of struct
  \`{name}\` is private"`, with a "declared without `pub` here" secondary
  label at the field's own type span, since there's no name span to point
  at) if the caller can't see it. Pushes a `FieldAccessKind::Read` access
  onto the field's `accesses` list (feeds the dead-field-write lint) unless
  it was `_`.
- `bind_struct_pattern_field`'s signature simplified from
  `field: &Spanned<ast::PatternField>` to `field: &ast::PatternField` (the
  `Spanned` wrapper's `.span` was never actually read inside the function —
  only `.inner.pattern`/`.inner.name` — so dropping it was a pure
  simplification, not a behavior change).
- Four new free `report_*` functions added at the bottom of `control.rs`
  (`report_duplicate_rest_pattern`, `report_tuple_struct_brace_pattern`,
  `report_record_struct_positional_pattern`, `report_private_tuple_field_pattern`),
  matching this file's existing "each slice owns its own diagnostics"
  convention.

**This file compiles cleanly on its own** (confirmed via `cargo check`
before the pivot below started).

### New diagnostic codes (`diagnostics.rs`)

```
TupleStructBraceLiteral      => "E1086"   // Point::{ .. } where Point is a tuple struct (construction)
DuplicateRestPattern         => "E1087"   // more than one `..` in one pattern
TupleStructBracePattern      => "E1088"   // Point::{ .. } where Point is a tuple struct (pattern)
RecordStructPositionalPattern => "E1089"  // Point(..) where Point is a record struct (pattern)
PrivateTupleField            => "E1090"   // private tuple field named (not `_`) in a destructuring pattern
```

`report_tuple_struct_brace_literal` (E1086, used by `aggregates.rs::build_struct_init_expression`
to reject `Point::{ ... }` on a tuple struct) is also already written and
working.

## Part 2 — the big pivot: how does `Point(1, 2)` actually get built?

### Where this started

The original plan (see "Superseded plan" below) had tuple structs synthesize
a **real TIR `Function`** as their constructor — a fresh `DefId`, a hand-built
`Body`/`StackFrame`/`Local`s, bound into the Value namespace as
`SymbolKind::Function`, so `Point` would be a genuine first-class callable
value (`arr.map(Point)` was an explicit, earlier-confirmed requirement).

### Why that got abandoned

1. While implementing it, hit a real design question: the ctor's
   `FunctionParam`s have no names (tuple fields are unnamed) — what goes in
   `FunctionParam.name: Spanned<SymbolU32>` (not `Option`)? A digit-string
   placeholder (`"0"`, `"1"`) was the obvious hack, and was explicitly
   rejected earlier in this same session for a different reason (struct
   field storage) — reusing it here would be the same mistake.
2. Prompted a read of `notes/wx-named-invocation-and-struct-constructors.md`
   (a **future**, not-yet-implemented design doc for general named-call
   syntax) — its `Parameter { name: Optional<Symbol>, .. }` model confirmed
   "unnamed parameter" should be a first-class state, not a hack, and
   directly settled the digit-string question. **But**: that doc's own
   model has `Point : fn(i32, i32) -> Point` — i.e. it *also* assumes the
   tuple-struct constructor is a real function value! So the abandonment
   below is a genuine departure from that doc's model for tuple structs
   specifically, not something it anticipated. Worth reconciling later if
   that doc's design is ever actually implemented.
3. I wrote a full first draft of the ctor-synthesis method anyway (fresh
   `DefId`, remapped `TypeParamInfo`s under a fresh `TypeParamOwner::Function(ctor_id)`,
   `intern_function` for the signature, hand-built `Body`/`StackFrame`/`BlockScope`/`Local`s
   mirroring `build_function_body`'s exact shape, `ExprKind::StructInit`
   referencing each param by index as the body). User rejected it: too much
   boilerplate for something that's *always* going to be force-inlined away
   anyway, and objected to reusing `ExprKind::StructInit` for something
   that "isn't really user-representable code" (I pushed back that
   `StructInit` is exactly what a hand-written trivial forwarding
   constructor already compiles to, and is confirmed name-agnostic/positional
   at the IR level — this point turned out to still matter later, see below).
4. This led to the actual pivot: **drop "usable as a bare value" entirely.**
   `arr.map(Point)` no longer works. `Point` only ever means anything as
   `Point(...)`, immediately applied. User explicitly confirmed dropping
   this requirement.

### The collision-safety question, and its answer

Once `Point` is no longer a real value, does it still need to occupy the
Value namespace at all? **Yes** — purely for collision safety, not for
being usable as a value. If a module already has `fn Point(a: i32, b: i32)`
and *also* declares `struct Point(i32, i32);`, what should `Point(1, 2)`
mean? Reserving the Value-namespace slot for the struct (even though
nothing real backs it) means a colliding `fn Point` becomes an ordinary
**duplicate-definition error (E2005)** at declaration time — not a silent,
lookup-order-dependent ambiguity discovered later at a call site.

**Decision**: `prescan.rs` keeps its existing dual-namespace claim for
`TupleStruct` (already implemented, unchanged — claims both
`(Type, name)` and `(Value, name)` with the struct's own placeholder `id`,
mirroring `Memory`'s existing dual claim). At Phase 2 (`signature.rs`), the
Value-namespace slot should be resolved to the **same** `SymbolKind::Struct { struct_index }`
already used for the Type-namespace slot — no new `SymbolKind` variant.
`global_symbol_to_expression`'s existing catch-all (`paths.rs:142-150ish`,
groups `Enum | Module | Struct | Trait | TypeSet | TypeAlias` and reports
`report_namespace_used_as_value`) already does exactly the right thing for
any *ordinary* bare-value reference to `Point` once it's reachable via the
Value namespace — **no change needed there**, since we're not routing
`Point(...)` construction through that function at all (see next section).

### How `Point(1, 2)` gets recognized (the current, agreed design)

**Ruled out**: giving `SymbolKind::Struct`-in-Value-namespace a new `Type::StructConstructor`
variant so it flows through the type system like a real (if restricted)
value, checked via `match self.types.resolve(callee.ty)` in
`build_call_expression` (mirroring how `Type::Function`/`Type::FunctionItem`
are already dispatched there). This was explored in real depth — including
whether it's "overengineered" (first take: yes, ~5 exhaustive `Type`
matches across the compiler would need a new arm each; reconsidered: most
of those would just be one-line `unreachable!()`s since the type is
provably transient/immediately-consumed, so the real cost is small and
`TypeFormatter` display support is a legitimate, not-overengineered need —
see "why `TypeIndex::ERROR` doesn't work" below). **Then superseded** by a
simpler idea before being implemented — see next paragraph. (The exhaustive-match
survey that was done for this ruled-out approach is preserved below in case
a *future* feature — e.g. a real record-struct constructor per the named-invocation
doc — ends up needing a similar type-level marker; the survey work doesn't
need to be redone from scratch.)

**Agreed, current design**: no new `Type` variant, no new `ExprKind`
variant at all. `build_call_expression` (`calls.rs`) gets a pre-check
**before** it builds the callee as an ordinary value expression: if the
callee AST node is a `Path`, try to resolve that path to `(SymbolKind, type_args)`
directly (without building a value `Expression` and without triggering any
"used as value" diagnostic). If that resolves to `SymbolKind::Struct { struct_index }`
where the struct is `StructKind::Tuple`, branch into building
`ExprKind::StructInit` positionally right there (arity check, per-argument
type inference, per-field privacy check, coercion — see "still to write"
below). **Otherwise — including if resolution fails, finds a local, finds a
record struct, or finds an ordinary function — fall through to the existing,
completely unchanged code path**, which re-resolves the same callee
normally. This fallback re-resolution is intentionally a little redundant
(one extra scope-chain walk in the common case) but safe: signature forcing
is idempotent, and every existing diagnostic for every other case
(undeclared identifier, wrong arity, private function, etc.) is completely
untouched.

This sidesteps the entire "how do we reject bare `arr.map(Point)` usage"
problem for free: since `Point` alone is never converted through this new
path at all (only `build_call_expression`'s callee slot goes through it),
a bare reference to `Point` anywhere else still goes through the ordinary,
unchanged `global_symbol_to_expression` catch-all and gets
`report_namespace_used_as_value` exactly as it does today for any other
struct/enum/module/trait name used as a value.

**Why `TypeIndex::ERROR` specifically doesn't work as a stopgap type**: it
was raised whether the "used as value" case could just get `ty:
TypeIndex::ERROR` (matching the existing convention) without inventing
anything. Problem, raised by the user: `ERROR` deliberately suppresses
downstream diagnostics (that's the whole point of it — avoid cascading
noise). But we *want* a clear message for something like `Point + 5`
naming the constructor's shape (`cannot apply \`+\` to \`Point(i32, i32) -> Point\`
and \`{integer}\`\``) rather than a generic/absent error. This is now moot
under the "no bare-value path at all" design (bare `Point` just hits the
ordinary struct-used-as-value diagnostic, which doesn't need to show a
function-like signature), but the reasoning is worth keeping in case a
future feature needs to represent something similar.

### The general path-resolution helper — in progress, not committed

The pre-check above needs a way to resolve **any** shape of callee path —
plain (`Point(1,2)`), turbofish (`Pair::<i32>(1, 2)`), and qualified
(`module::Point(1, 2)`) — to `(SymbolKind, type_args)`, without going
through the diagnostic-emitting value-conversion step. `paths.rs`'s existing
`build_path_expression` handles exactly these three shapes today, but as
three separate, hardcoded branches (each already converts straight to an
`Expression`, and the turbofish/multi-segment branches are hardcoded to
only recognize `SymbolKind::Function`):

1. **Single segment, no type args** (`paths.rs:304-336`) → `resolve_symbol_forcing`
   → `Option<ResolvedSymbol>` (`Local` or `Global(SymbolKind)`) →
   `resolved_symbol_to_expression`.
2. **Single segment, with turbofish** (`paths.rs:339-445`) → its own
   `lookup_global_symbol_reporting` + hardcoded `Some(SymbolKind::Function { .. }) => .., _ => report_undeclared_identifier`
   — does not use `resolve_symbol_forcing`/`ResolvedSymbol` at all.
3. **Multi-segment** (`paths.rs:447-517`) → walks `path[0..n-1]` as a
   namespace chain via `resolve_type_identifier` (first segment) +
   `resolve_namespace_type_member` (remaining segments) to a `namespace_ty: TypeIndex`,
   applying turbofish on the first segment if present (only meaningful if
   it resolves to `Type::Struct`); then hands the **last** segment to
   `build_namespace_member_expression` → `resolve_namespace_member`
   (`paths.rs:942-1117`), whose `Type::Namespace { namespace_idx }` arm
   (`paths.rs:1053-1096`) calls `resolve_pending_namespace_symbol` and is
   itself hardcoded to only handle `SymbolKind::Function | Global | Const`
   (falls to `report_undeclared_identifier` for anything else, including
   `Struct`).

**User's explicit direction** (after I initially proposed a
struct-specific, single-segment-only helper, which was rejected twice for
being too narrow / "a separate kind of thing"): extract a **general**
`resolve_symbol_and_type_args(ctx, path) -> Result<Option<(SymbolKind, Box<[TypeIndex]>)>, ()>`
helper that mirrors all three of the branches above up to the point of
having a resolved symbol + type args, stopping *before* the
`Expression`-building step — reusable later for other symbol kinds too
(explicitly named: a future `variant`/tag item, not just structs). This
should live in `modules.rs` next to `resolve_symbol_forcing` (`modules.rs:969-1000`),
which it partially reuses for the bare/turbofish-single-segment case.

**Semantics that matter and must be preserved** (per `resolve_symbol_forcing`'s
own doc comment, an existing invariant in this codebase): the helper's
return value must distinguish three outcomes, not two:
- `Ok(Some((kind, args)))` — resolved to something; caller decides what to
  do (build tuple-struct call, or ignore and fall through).
- `Ok(None)` — doesn't resolve this way at all (a local, or nothing found)
  — safe for the caller to fall through to ordinary resolution, which will
  redo the work and report its own diagnostics normally.
- `Err(())` — a cycle, or a broken qualifier in a multi-segment walk, was
  **already reported** by a step inside this helper (e.g.
  `resolve_type_identifier`/`resolve_namespace_type_member` failing on an
  unknown module). The caller **must not** fall through and re-resolve in
  this case — that would report the same error a second time. `build_call_expression`'s
  pre-check needs to handle this by building an error-typed callee/call
  expression directly rather than falling through.

**Last draft attempted** (not reviewed/accepted — the session ended before
feedback): a `resolve_symbol_and_type_args` method roughly of this shape,
in `modules.rs`:

```rust
pub(super) fn resolve_symbol_and_type_args(
    &mut self,
    ctx: &mut ExprContext,
    path: &[ast::PathSegment],
) -> Result<Option<(SymbolKind, Box<[TypeIndex]>)>, ()> {
    let (last, qualifier) = path.split_last().expect("path is non-empty");

    let namespace_idx = if qualifier.is_empty() {
        // Bare identifier — may be a local (not a symbol, from this
        // function's point of view) or a global.
        let Some(ResolvedSymbol::Global(kind)) =
            self.resolve_symbol_forcing(ctx, last.ident)?
        else {
            return Ok(None);
        };
        let type_args = last.type_args.iter()
            .map(|arg| self.resolve_type(ctx.resolve_context, ctx.scope, arg))
            .collect();
        return Ok(Some((kind, type_args)));
    } else {
        // Qualified path: walk every segment before the last as a
        // namespace chain, mirroring build_path_expression's own
        // multi-segment tail (paths.rs:447-489) exactly, including
        // growing namespace_span the same way for diagnostic accuracy.
        let first = &qualifier[0];
        let mut namespace_ty = self.resolve_type_identifier(
            ctx.resolve_context, ctx.scope, first.ident, TypeArgArity::AllowInfer,
        )?;
        if !first.type_args.is_empty() {
            let struct_index = match self.types.resolve(namespace_ty) {
                Type::Struct { struct_index, .. } => *struct_index,
                _ => return Ok(None),
            };
            let resolved_args: Box<[TypeIndex]> = first.type_args.iter()
                .map(|arg| self.resolve_type(ctx.resolve_context, ctx.scope, arg))
                .collect();
            namespace_ty = self.types.intern(Type::Struct { struct_index, args: resolved_args });
        }
        let mut namespace_span = first.ident.span;
        for segment in &qualifier[1..] {
            namespace_ty = self.resolve_namespace_type_member(
                ctx.resolve_context, ctx.scope,
                Spanned { inner: namespace_ty, span: namespace_span },
                segment, TypeArgArity::AllowInfer,
            )?;
            namespace_span = TextSpan::new(namespace_span.start, segment.ident.span.end);
        }
        match self.types.resolve(namespace_ty) {
            Type::Namespace { namespace_idx } => *namespace_idx,
            _ => return Ok(None),
        }
    };

    let Some(kind) = self.resolve_pending_namespace_symbol(
        ctx.resolve_context.namespace, namespace_idx,
        (SymbolNamespace::Value, last.ident.inner),
        SourceSpan::new(ctx.resolve_context.file_id, last.ident.span),
    )? else {
        return Ok(None);
    };
    let type_args = last.type_args.iter()
        .map(|arg| self.resolve_type(ctx.resolve_context, ctx.scope, arg))
        .collect();
    Ok(Some((kind, type_args)))
}
```

Open questions on this draft, not yet resolved:
- Whether reusing `resolve_pending_namespace_symbol` (rather than the fuller
  `resolve_namespace_member`) for the final-segment lookup in the qualified
  case is right — `resolve_namespace_member`'s existing `Function` arm does
  a little more (builds `INFER`-padded `type_args` sized to the function's
  *own* type-param count automatically); this draft instead applies
  whatever turbofish is on `last.type_args` uniformly for any `SymbolKind`,
  un-padded — the caller would need to pad to the right length itself,
  which is fine for the struct case (caller already knows the struct's
  `type_params.len()`) but means this helper alone isn't a complete
  drop-in replacement for what `resolve_namespace_member` does today.
- `Err(())` handling in `build_call_expression`'s pre-check wasn't written
  yet — needs to build an error-typed callee/call rather than falling
  through, per the invariant above. A minimal version (skip building
  arguments, just return an `ExprKind::Error`-kinded call) was considered
  acceptable given how narrow the trigger is (cyclic/broken qualifier *and*
  happens to be tuple-struct-call syntax).
- Not yet updated: `calls.rs`'s pre-check currently calls a since-abandoned
  name (`self.resolve_tuple_struct_call_target(ctx, path)`, struct-specific,
  single-segment-only — the very first draft, since superseded). This needs
  to be rewritten to call the new general `resolve_symbol_and_type_args`,
  then interpret a `SymbolKind::Struct { struct_index }` result itself
  (check `StructKind::Tuple`, pad `type_args` to the struct's own
  `type_params.len()`).

### `build_tuple_struct_call_expression` — designed, not yet written to any file

The actual positional-construction builder (analogous to `aggregates.rs::build_struct_init_expression`,
but positional). Belongs in `aggregates.rs`. Design (arrived at before the
resolver detour, still valid):

- Signature roughly: `(&mut self, ctx: &mut ExprContext, struct_index: StructIndex, type_args: Box<[TypeIndex]>, arguments: &[Separated<Spanned<ast::Expression>>], expected_result: TypeIndex, call_span: TextSpan) -> Result<Expression, ()>`.
  `type_args` arrives already `INFER`-padded to the struct's own type-param
  count (from turbofish, or all-`INFER`) — the caller's job, not this
  function's.
- Arity check against `StructKind::Tuple`'s field count; reuse
  `report_tuple_struct_arity_mismatch` (**not yet written** — new free fn,
  same `TypeMistmatch` code convention as the plain-tuple-pattern arity
  check already uses).
- Optional cheap seed: if any `type_args` slot is still `INFER`, check
  whether `expected_result` is already `Type::Struct { struct_index: same, args }`
  of matching length and copy those args directly — same simple
  "already-concretely-embedded" tier `build_struct_init_expression` itself
  uses for its own expected-type inference, not full unification.
- Per positional argument (`i` in `0..field_count`): compute `expected_ty`
  via `substitute_expected_type(raw_field_ty, &type_args)`; check
  `field_visibility`/`is_accessible_from` and report a **new**
  `report_private_tuple_field_construction` (**not yet written** — reuses
  the `PrivateTupleField`/E1090 code, construction-context wording, no
  `_`-skip here since every argument is always supplied); build the
  argument expression; refine `type_args` via `self.types.infer_type_args(&mut type_args, raw_field_ty, built.ty)`
  (same mechanism `build_generic_call_arguments` already uses for ordinary
  generic function calls — `mod.rs`/`calls.rs:355-357`); coerce/type-check
  same as `build_struct_init_expression` (comptime-number coercion, else
  `coercible_to` + `report_type_mistmatch`).
- Extra arguments past the struct's arity: still build (and discard) them,
  with `expected_type: TypeIndex::ERROR`, so mistakes inside them are still
  reported — same convention `build_call_expression`'s own existing
  broken-callee fallback uses.
- After the loop: any `type_args` slot still `INFER` → report (reusing the
  existing generic `TypeAnnotationRequired` code, same as
  `build_generic_call_arguments`'s own "cannot infer type for type
  parameter" diagnostic — needs the struct's own `type_params[i].name` to
  name the parameter) and poison it to `TypeIndex::ERROR`.
- Result: `ExprKind::StructInit { struct_index, fields: <built (FieldIndex, Expression) pairs> }`,
  `ty: Type::Struct { struct_index, args: type_args }`.
- Also push a `FieldAccessKind::Init` access per field onto `TupleFieldInfo.accesses`
  (feeds the dead-field-write lint from Part 1 — not yet done, need to add
  this when writing the real function) and push a construction access onto
  the struct's own `Struct.accesses` (feeds the dead-struct lint — probably
  once, not per-field, at the top of the function).

## `signature.rs` — still has the dangling old call, not yet fixed

`AstNodeRef::TupleStruct`'s arm (`signature.rs:151-224`) still ends with a
call to `self.synthesize_tuple_struct_constructor(resolve_context, *id, struct_index, name, *pub_span);` —
**this method was never written** (every attempt to write it was
superseded before being committed), so this is a real, current compile
error. Per the final design (Part 2), this whole call should be **deleted**
and replaced with just registering the Value-namespace symbol using the
same `SymbolKind::Struct { struct_index }` already used for the
Type-namespace symbol two lines above it in the same arm:

```rust
let value_key = (SymbolNamespace::Value, name.inner);
if self.still_pending(resolve_context.namespace, value_key, *id) {
    self.insert_symbol(
        resolve_context.namespace,
        value_key,
        SymbolKind::Struct { struct_index },
        *pub_span,
    );
}
```

This is small, well-understood, and not blocked on anything else — safe to
do first when resuming.

## Current compile state (as of stopping)

Does not compile. Known errors:
- `signature.rs`: dangling `synthesize_tuple_struct_constructor` call (see
  directly above — fix is known and small).
- `calls.rs`: the pre-check block added to `build_call_expression` calls
  `self.resolve_tuple_struct_call_target(ctx, path)` and
  `self.build_tuple_struct_call_expression(...)` — **neither function
  exists yet** (the first name is an abandoned draft; the second was
  designed but never written to a file). Needs `resolve_symbol_and_type_args`
  (in `modules.rs`, in progress, draft above) plus a small adapter in
  `calls.rs` itself to interpret its `SymbolKind::Struct` result, plus
  `build_tuple_struct_call_expression` written into `aggregates.rs` per the
  design above.

Everything in Part 1 (StructInit ordering, `.field`-access simplification,
dead-field lint, `field_visibility`, and all of `control.rs`'s pattern
rewrite) compiles cleanly in isolation and does not need to change.

## Remaining work, roughly in order

1. Fix `signature.rs`'s dangling call (small, known, above).
2. Finish `resolve_symbol_and_type_args` in `modules.rs` (draft above needs
   review — especially the `Err(())`-propagation discipline and whether
   reusing `resolve_pending_namespace_symbol` vs. more of
   `resolve_namespace_member` is right for the qualified-path case).
3. Update `calls.rs`'s pre-check in `build_call_expression` to call the
   renamed/generalized resolver, interpret a `SymbolKind::Struct` result
   (check `StructKind::Tuple`, pad `type_args`), and handle the `Err(())`
   case without double-reporting.
4. Write `build_tuple_struct_call_expression` in `aggregates.rs` per the
   design above, plus its two new report functions
   (`report_tuple_struct_arity_mismatch`, `report_private_tuple_field_construction`).
5. `cargo check -p wx-compiler` until clean, then `cargo test -p wx-compiler`
   and `cargo clippy --workspace --no-deps -- -D warnings`.
6. wx-fmt: `Item::TupleStruct => todo!()`, `Pattern::TupleStruct => todo!()`
   (rename existing arms to `Item::RecordStruct`/named `Pattern::Struct`
   first if not already done — check current state, this predates the
   session that produced this note).
7. wx-lsp: safe, non-panicking fallbacks for the new AST/TIR shapes
   (`Item::TupleStruct`, `Pattern::TupleStruct`, `StructKind::Tuple`) —
   check current compile state, likely still broken here too since wx-lsp
   wasn't touched this session.
8. TIR tests (none written yet): non-generic tuple struct
   construction/destructuring/diagnostics; generic tuple struct
   (`struct Pair<T>(T, T);`) construction with inferred and explicit
   (turbofish) type args; `Point::{ .. }`/`Point(..)` grammar-mismatch
   diagnostics both ways; arity mismatches both ways; per-field visibility
   (construction rejects if any field private; destructuring rejects only
   on the specific private field named, not on `_`).
9. Manually verify via `wx build`/`wx check` on the commented-out example
   already sketched in `examples/fibonacci/main.wx` (per the original
   plan), confirm real WASM output round-trips through `wasm2wat`.
10. Update or retire the stale plan at `/Users/melkam/.claude/plans/hazy-growing-stream.md`
    (still describes the abandoned function-synthesis approach) — this note
    is the current source of truth in the meantime.

## Superseded plan

`/Users/melkam/.claude/plans/hazy-growing-stream.md` — the original,
user-approved plan for this feature. Still correct on: AST split
(`Item::RecordStruct`/`Item::TupleStruct`, `Pattern::Struct`/`Pattern::TupleStruct`),
TIR `StructKind` enum shape, per-field `pub` support, and the overall
"why one TIR `Struct` type, not two" research. **No longer correct** on: the
constructor being a real synthesized `Function`/first-class value (Part 2
above describes why and what replaced it), and the specific per-field
"aggregate visibility onto one synthesized function's `pub_span`" mechanism
for construction privacy (construction privacy is now a direct per-field
check inside `build_tuple_struct_call_expression`, not implicit through a
function's own `pub_span`).

## Other context worth keeping

- `notes/wx-named-invocation-and-struct-constructors.md` — a **future**,
  not-yet-implemented design doc (general named-call syntax `f({ x: 1 })`,
  record structs eventually getting their own `NamedOnly` synthesized
  constructor, `InvocationPolicy` enum). Explicitly out of scope to
  implement now — was read only to inform the tuple-struct design (settled
  the "unnamed parameters are legitimate" question) and to sanity-check
  that nothing being built now would block it later. The one real tension:
  that doc assumes tuple-struct constructors *are* real function values
  (`Point : fn(i32, i32) -> Point`) — the current session's Part 2 pivot
  means they aren't. Worth reconciling if that doc's design is ever picked
  up — likely resolution: that doc's model may need updating to reflect
  that tuple-struct "calls" are call-site syntax sugar, not real functions,
  while record structs (if they ever get a `NamedOnly` constructor per that
  doc) might still warrant being real functions since named-call resolution
  is a much bigger, more general mechanism than positional construction.
- The `Type`-exhaustive-match survey and full `Body`/`StackFrame`/`Local`
  struct-shape research done during this session (via two background
  research agents) are **not needed** for the current design (no new
  `Type` variant, no synthesized `Function`/`Body` at all), but were
  thorough and correct as of this session — worth pulling from the
  session transcript instead of re-researching if a future feature (e.g.
  a real record-struct constructor) ends up needing either.
