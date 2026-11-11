# Semantics ownership: what was built and why

Status: implemented (2026-11-11). This note was a 900-line plan; it is now a
record of the result. The plan's detailed alternatives and the abandoned
`SignatureState`/owned-AST-locator design are in git history (this file before
the commit that condensed it). Companion: [native LSP plan](lsp-refactor-plan.md).

## The problem

`TypeContext` fused two things: the semantic state a language server keeps
(declarations, dispatch, types, signatures, bodies, values, resolutions,
diagnostics, the solver) and the construction machinery that lives only while
checking (the prescan's AST entries, query state and stack, per-query
obligations, and the code that turns syntax into types). The `'ast` lifetime
belonged wholly to the second, so the whole thing could not be stored next to
the `CompilationUnit` and interner without self-reference.

Measured before splitting: after phase 1 of the build no signature is ever
computed and no cycle is hit (a probe panicking on either passed every test and
example). The solver, evaluation, obligation checking, deciding bodies, lowering
and formatting cannot reach a signature query; only ~45 methods that turn
written syntax into types, and body building, can.

## The result

```rust
pub fn check(compilation: &CompilationUnit, strings: &mut StringInterner) -> Semantics;
pub fn lower(sema: &mut Semantics, strings: &StringInterner) -> Result<MIR, ()>;
impl Semantics { pub fn diagnostics(&self) -> &[Diagnostic<FileId>]; }
```

- **`Semantics`** (was `TypeContext`) has no lifetime and owns `decls`,
  `ImplDispatch`, the solver, the diagnostics, the name resolutions, signature
  tables and bodies. It stays live and mutable after checking (queries may
  re-enter body deciding). It holds no syntax.
- **`SemanticsBuilder<'ast>`** (was `Construction`) is a *sibling*, not a
  wrapper: it holds the borrowed AST entries, files, the interner (`&mut`),
  query state/stack and declaration obligations, and lives only for
  `build(sema)`. Its operations take `sema` as a parameter, which is what lets a
  body builder hold both as disjoint `&mut`s. Nothing after the build reads it.
- **`BodyContext` / `BodyBuilder`**: deciding is its own entity (a body in its
  scope and what is valid on it, no syntax); building uses it through
  `self.context()`. Deciding lives in `typecheck/decide.rs`. The solver's
  re-entry (`decide_obligations`) makes only a `BodyContext`.
- **Lowering reads no AST.** `FunctionImplementation::Intrinsic` became
  `Parameter`; lowering fulfils std's package functions by name
  (`std_intrinsics`); an import is recognized by its namespace.
- **Strings are passed explicitly.** One interner outlives many compilations, so
  `Semantics` does not own it: methods that read a name take `strings` first;
  short-lived structs over `sema` hold it as a field. Cost: clippy's
  `too_many_arguments` rose to 18.
- **Renames:** `DefinitionRegistry` is `Declarations` (`DeclId`, `DeclKey`, ...).

Borrows that owning broke were fixed by collecting candidates first (a pure read)
and then querying, not by `Rc`/`unsafe`/a frozen registry (all rejected).

## Settled decisions

1. State that owns types, signatures, bodies: the broad `Semantics`, with query
   metadata on the builder.
2. Owned AST locator: none. The AST borrow lives in the builder.
3. Body-builder and lowering dependency signatures: as above.
4. Repeated check: call `tir::check` again. A snapshot is
   `{ compilation, strings, sema }`; no incremental invalidation, no reuse of
   caches against changed inputs.

## Tests that pin it

`lower.rs`: `semantics_answers_queries_after_checking_and_after_lowering` and
`an_erroneous_program_keeps_its_declarations_references_and_bodies`; a
regression keeps two compilation units alive with one interner. Every suite's
`TestCase` owns its files, interner and `Semantics`.

Validation at completion: 1450 compiler tests (2 ignored), 75 formatter tests,
every example checks.

## Still relevant when changing this

- A failed check keeps partial semantic data (declarations, references, bodies);
  the LSP depends on it.
- A construct that needs syntax after the build needs a new `SemanticsBuilder`
  over the same AST; an arena AST or item tree is worth it only once checking
  stops re-running whole-program per edit.
