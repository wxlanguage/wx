# Agent guidance for WX

## Language direction

WX is a language built around WebAssembly, with a compiler implemented in Rust.
It has a long-term direction beyond the bachelor's thesis, which documents one
milestone of its design and implementation.

Make WebAssembly's resources visible and usable through the type system:
memories, globals, functions, host boundaries, and instructions. Favor safe,
zero-cost abstractions with a predictable mapping to Wasm. Keep the baseline
minimal; leave allocation and runtime policies to libraries and applications,
and let programs adopt platform extensions incrementally. Reuse uniform
mechanisms such as traits, item types, and typed calls as the language grows.

Discuss exceptions to these principles and changes to the safety/control
tradeoff with the user before implementing them. Rust-inspired syntax does not
imply that WX should inherit Rust's semantics. Breaking changes are acceptable
when they improve the design; update affected code, examples, and tests together.

## Approach to design and problem solving

Start with the data the problem needs: its shape, ownership, lifetime,
relationships, and access patterns. Build the solution around that model.
Favor compact, contiguous, cache-friendly storage, arenas, and typed indices,
with explicit owners and borrowing between stages.

Discuss introducing `Rc`, `Arc`, `RefCell`, `Cell`, or similar shared-ownership
or interior-mutability mechanisms with the user before implementing them.
Explain the requirement and why explicit ownership and arena-based storage
would not adequately solve it.

Invest time in a coherent architecture and maintainable code. Address the
underlying data model and responsibility boundaries when fixing a problem.
Avoid boolean flags that patch over unclear states, change an operation's
meaning by caller, or bypass an invariant. Prefer explicit states, distinct
operations, or a better model when they express the problem more clearly.
Ordinary boolean facts are fine; evaluate what a flag represents before adding
it. Favor a focused design that solves the actual problem and makes correctness
clear over either a quick workaround or speculative abstraction.

## Finding your way

- `crates/wx-compiler/`: parsing (`src/ast`), package loading (`src/vfs`), checking
  and monomorphizing lowering (`src/tir`), MIR and inlining (`src/mir`),
  optimization (`src/opt`), and Wasm emission (`src/codegen`, `src/wasm`).
  `src/backend.rs` coordinates inlining, optimization, and code generation.
- `crates/wx-compiler/core/`: embedded WX core library, including primitives,
  traits, and typed instruction declarations.
- `crates/wx-cli/`: the `wx` binary: `build`, `check`, `format`, and `lsp`.
- `crates/wx-fmt/` and `crates/wx-lsp/`: shared formatter and language server.
- `crates/wx-lint/`: lints over a checked package, configured by `wx.json`'s `lint`
  section; the CLI and language server run them after checking.
- `crates/wx-mcp/`: the `wx mcp` Model Context Protocol server, inspection-only
  tools for agents over a checked package; it shares the compiler's queries and
  rendering with the language server, not its protocol code.
- `examples/`: WX packages and runnable applications; some are experiments.
- `crates/*-wasm/`, `web/`, `web-next/`: browser wrappers and playgrounds.
- `editors/`: separate Git submodules; changes there belong to their own repos.

For compiler work, read [its scoped guidance](crates/wx-compiler/AGENTS.md);
for language-server work, read [its scoped guidance](crates/wx-lsp/AGENTS.md).
Read the relevant code and nearby tests before editing. `notes/` and `devlog/`
contain rationale, proposals, and historical plans; verify their implementation
claims against the code. `thesis/`, when present, is a separate, gitignored
checkout. Its `chapters/en/01-introduction.typ` explains the motivation and goals,
but working in this repository must not depend on that checkout being available.

## Build and validate

Run commands from the repository root:

```sh
cargo build -p wx-cli
cargo test -p wx-compiler -- <test_name>
cargo test -p wx-fmt -p wx-lsp
cargo fmt --check
```

To exercise the current sources, use `cargo run -p wx-cli -- check examples/factorial`
or `cargo run -p wx-cli -- build examples/factorial -o /tmp/wx-factorial.wasm`.
`build`, `check`, and `format` take a package directory containing `wx.json`.
A minimal manifest is `{ "entry": "main.wx" }`; ordinary packages omit `type`.

CI runs `cargo check --workspace`, `cargo test --workspace`, and
`cargo clippy --workspace --no-deps -- -D warnings`. The browser compiler wrapper
`wx-compiler-wasm` currently uses removed compiler APIs. If it blocks workspace
validation, report the failure and validate native crates with
`cargo test --workspace --exclude wx-compiler-wasm`. Keep unrelated migration work
out of the task. `wx-lsp-wasm` is excluded from the native workspace and requires
a separate wasm32 build.

Add a regression test at the boundary affected by the change. Checking tests
establish types and diagnostics; generated-code changes also need execution
tests through the shared backend, typically using Wasmtime. Prefer assertions
that state the intended behavior. Regenerate changed snapshots with the test
suite and review them with `cargo insta`; do not hand-edit `.snap` files.

CI does not exercise WX examples. When changing syntax, core, or language
behavior, check and build affected example packages explicitly. Run a release
build when changing conditional compilation or debug-only derives. Report what
you tested and any failures that limit validation.

## Maintaining guidance

Keep this file focused on durable instructions for agents. Put implementation
invariants beside the code or in narrowly scoped guidance; keep feature catalogs,
test counts, and session progress out of it. Preserve shared compiler behavior
across the CLI, formatter, and language server.

For release tasks, read [.claude/skills/release-wx/SKILL.md](.claude/skills/release-wx/SKILL.md).
