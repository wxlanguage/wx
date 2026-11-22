# Compiler guidance

## Architecture and consumers

Read [the compiler architecture](README.md) for the stage map, ownership model,
and design rationale. Keep each stage usable at its own boundary: `ast` records
syntax, `vfs` assembles parsed packages, TIR checks their meaning, lowering builds
concrete MIR, `opt` rewrites it, and `codegen` emits Wasm.

`wx-fmt` consumes syntax, comments and source text without type checking.
`wx-lsp` consumes parsed inputs and semantic state without lowering or codegen.
Keep language decisions in the compiler and tool-specific queries and protocol
handling in the consumers. Preserve these boundaries when changing APIs.

## Semantic ownership and diagnostics

`tir::check` returns the owned, live `Semantics`; `tir::lower` reads it to produce
MIR. `SemanticsBuilder` handles syntax-dependent construction and signature
queries. Keep those responsibilities separate, with a caller-owned string
interner passed explicitly. Preserve partial semantic data after errors: the LSP
uses declarations, references, and bodies from unsuccessful checks.

Use `CompilationUnit::collect_diagnostics` and the `Diagnostics` extension trait
to gather and classify errors consistently, including bug severity. In tests,
use the existing `DiagnosticView` assertion vocabulary. Unsupported lowering
must report a diagnostic rather than silently discard a checked construct.

## Invariants when editing

- Keep pre-interned types in `tir/types.rs` aligned with their `TypeIndex`
  constants. Append new entries and update the constants together.
- In `ensure_signature`, handle cycle status and preserve the query-stack
  unwind on every path after pushing a frame.
- A parser function returning `Err` must already have reported the error.
  Preserve recoverable syntax for incomplete editor input such as `x.` and
  `a::`; avoid duplicate lookup diagnostics for missing names.
- Preserve package and module lookup boundaries. Use the existing resolution
  machinery for visibility and imports.
- Keep MIR item IDs stable through inlining and optimization; reachability
  determines which items codegen emits. Use `backend::emit` to exercise the
  shared build sequence in execution tests.
- Some IR derives exist only under `debug_assertions` or `test`. Ensure new
  assertions and formatting compile in release builds too.

For ownership rationale, consult
[the Semantics ownership note](../../notes/type-context-ownership-refactor.md).
For backend changes, consult [the MIR pipeline](../../notes/mir-pipeline.md)
and [optimizer design](../../notes/opt-design.md), checking historical sections
against the implementation.
