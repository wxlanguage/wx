# Findings: getting wasmtime + LLDB/CodeLLDB debugging working against wx's DWARF

## Summary

Getting `wasmtime run -D debug-info=y` (and, by extension, LLDB/CodeLLDB in
VS Code) working against wx's embedded DWARF5 debug info surfaced four
separate issues, two ours and two wasmtime's:

1. **Ours (fixed).** Our DWARF encoder omitted `DW_OP_stack_value` after
   `DW_OP_WASM_location`, so wasmtime read every scalar local as an address
   needing a memory dereference — and hard-crashed on any module with no
   declared memory. This was the actual root cause of the original crash.
2. **wasmtime's, still open.** Even granting that a consumer might read our
   (pre-fix) output as address-yielding, wasmtime's response to that is
   disproportionate (kills the whole `wasmtime run`, not just debug-info
   generation) and illegible (a generic gimli error with no indication of
   what or why).
3. **wasmtime's, still open, newly found.** Independent of bug 1: any
   multi-field struct local (anything using `DW_OP_piece`) still crashes
   the same way, but only at `-O opt-level=0` — a `need_deref` tracking bug
   in wasmtime's expression parser that our encoding can't work around.
4. **wasmtime's, acknowledged by a maintainer, not really "fixable" by us
   or practically by them right now.** Gutter/file-line breakpoints against
   wasmtime's JIT-registered debug info never bind in lldb on macOS, even
   after the module is loaded. A wasmtime core maintainer has stated native
   debugger attachment is "best-effort... more or less unmaintained" and
   they're building a replacement rather than continuing to harden this
   path. Workaround found: **symbol/function-name breakpoints work fully**
   (correct source location, working `frame variable`) — see the setup
   guide at the bottom.

## Bug 1 (ours, fixed): missing `DW_OP_stack_value`

`crates/wx-compiler/src/dwarf/mod.rs`, `build_location_expr`, used to emit:

```
DW_OP_WASM_location 0x00 <index>
```

for a scalar local, or a chain of

```
DW_OP_WASM_location 0x00 <index>  DW_OP_piece <size>
```

per flattened field for an aggregate. Neither includes `DW_OP_stack_value`.

Real producers (LLVM's wasm backend) always terminate one of these
expressions with `DW_OP_stack_value` to mark "the thing I just computed
*is* the value" — and wasmtime's consumer code assumes this. From
`crates/cranelift/src/debug/transform/expression.rs` (wasmtime v46.0.1):

```rust
while !pc.is_empty() {
    ...
    need_deref = true;          // <- reset to true before every operation
    let op = Operation::parse(&mut pc, encoding)?;
    match op {
        ...
        Operation::StackValue => {
            need_deref = false; // <- only operation that ever clears it
            ...
        }
        Operation::WasmLocal { index } => {
            // no effect on need_deref
            ...
        }
```

So a bare `DW_OP_WASM_location` operation leaves `need_deref == true`, and
later, when building the actual location list/exprloc bytes, that flag
triggers a call to `append_memory_deref`, which needs to know how to compute
the module's linear-memory base pointer from `vmctx`. If the module has no
memory, that's `ModuleMemoryOffset::None`, and:

```rust
// crates/cranelift/src/debug/transform/expression.rs
ModuleMemoryOffset::None => return Err(write::Error::InvalidAttributeValue),
```

— which is the exact error text we saw, propagated up through
`wasmtime_environ::error::Error`'s `Caused by:` chain.

**Fix applied**: `build_location_expr` now appends `DW_OP_stack_value`
(`0x9f`) after every `DW_OP_WASM_location` — once for a scalar, and once per
piece for an aggregate (right before that piece's `DW_OP_piece`).
Regression test: `dwarf::tests::wasmtime_accepts_our_debug_info_for_a_module_with_no_memory`
(deliberately declares no `memory` block, to pin the real fix rather than
the memory-declaration workaround). Verified end-to-end against the real
`wx` CLI + `wasmtime` binary too — `dwarf-playground/program.wx` (which
declares no memory) runs clean under
`wasmtime run -D debug-info=y --invoke compute program.wasm 5`.

## Bug 2 (wasmtime's, still open): disproportionate, illegible failure — not "rejecting is wrong"

To be precise about what's actually wrong here, since "reject bad input" is
a perfectly legitimate design choice and arguably *better* than silently
limping along on it: the problem isn't that wasmtime rejects our (pre-fix)
input. It's two separable things, both independent of whether rejecting is
the right call in the abstract:

1. **Blast radius.** `-D debug-info=y` / `Config::debug_info(true)` is
   opt-in tooling layered on top of running the module — it's not required
   for correctness of execution. When wasmtime can't honor it for some
   input, the current behavior kills the *entire* `wasmtime run`
   invocation: the module doesn't run at all, not even without debug info.
   That's disproportionate to what failed. A narrower failure — refuse to
   attach debug info (for the one variable, the one function, or worst
   case the whole module) but still execute the wasm — would still be
   "rejecting the bad input," just scoped to the thing that's actually
   broken.
2. **Diagnostic quality.** Even a hard, whole-module rejection would be
   defensible if it told you *why*. What you actually get is a generic
   gimli string —
   `Caused by: The attribute value is an invalid for writing.` — with no
   DIE offset, no attribute name, no mention of "no memory declared,"
   nothing pointing at the actual cause.

For context on how wasmtime handles similar situations elsewhere: the same
file (`crates/cranelift/src/debug/transform/attr.rs`) has a fallback path
for other malformed attributes that logs and skips rather than aborting:

```rust
// No other attributes contain addresses or address offsets.
_ => match convert_unit.convert_attribute_value(unit, attr, &|_| None) {
    Ok(value) => value,
    Err(e) => {
        // Invalid `FileIndex` was seen in #8884 and #8904. In general it's
        // better to ignore invalid or unknown DWARF rather then failing outright.
        dbi_log!(...);
        continue;
    }
},
```

That's one legitimate way to fix the blast-radius problem (scope the
failure to the one attribute), but it's not the only one — a louder,
scoped rejection (skip debug info for the module, print a real diagnostic,
still run the wasm) would address both problems above just as well without
taking a position on "should invalid DWARF be silently dropped," which is
a separate, more debatable question.

## Bug 3 (wasmtime's, still open, newly found): `DW_OP_piece` doesn't reset `need_deref`

Even with bug 1 fixed, a **struct-typed local still crashes wasmtime the
same way**, but only under `-O opt-level=0`. Reproduced via
`dwarf-playground/program.wx` (has a `Vec2` struct param/local):

```
wasmtime run -D debug-info=y --invoke compute program.wasm 5        # works
wasmtime run -D debug-info=y -O opt-level=0 --invoke compute program.wasm 5   # crashes,
                                                                       # same "attribute value is invalid for writing"
```

A scalar-only program (no structs) works fine at `-O opt-level=0`, so this
is specifically about `DW_OP_piece`-composite locations.

Root cause (same file, `expression.rs`): `need_deref` is a single flag for
the *whole* expression, computed from whichever operation was parsed last:

```rust
while !pc.is_empty() {
    ...
    need_deref = true;   // reset unconditionally, every iteration
    let op = Operation::parse(&mut pc, encoding)?;
    match op {
        ...
        Operation::StackValue => { need_deref = false; ... }
        ...
        Operation::Piece { .. } => (),   // <- grouped with inert arithmetic
                                          //    ops; doesn't touch need_deref
```

and later, unconditionally at the end of building the expression:

```rust
if self.need_deref {
    ranges_builder.process_label(vmctx_label);
    ...
    deref!();   // -> append_memory_deref -> same ModuleMemoryOffset::None crash
}
```

Our struct-local expression is `[WasmLocal, StackValue, Piece, WasmLocal,
StackValue, Piece]`. The *last* operation processed is `Piece`, which
doesn't reset `need_deref` — so despite every individual piece correctly
being marked with `DW_OP_stack_value`, the expression-wide flag comes out
`true` and wasmtime tries to memory-dereference the whole thing anyway.

This isn't something we can encode around: `DW_OP_piece` is a structural
marker (not a value-computing op), and any spec-legal multi-piece location
description built from register/stack values (not just ours) will end on a
`Piece`, not a `StackValue`. The real fix has to be on wasmtime's side —
either treat `Operation::Piece` as resetting/tracking `need_deref`
per-piece (mirroring how it already tracks per-`Local` `trailing` state),
or stop taking the whole-expression flag from "whatever the last op
happened to be."

**Workaround for now**: don't pass `-O opt-level=0` when the module may
have struct locals (i.e. always, unless you know the program is
scalar-only). Default opt level works cleanly; the tradeoff is coarser
local-variable visibility (values are more likely to show "optimized out"
near a function's start).

## Bug 4 (wasmtime's, acknowledged by a maintainer): gutter breakpoints never bind on macOS lldb

Confirmed directly, with the fix from bug 1 applied and without `-O
opt-level=0` (bugs 2/3 out of the way):

- `wasmtime run -D debug-info=y --invoke compute program.wasm 5` runs
  clean.
- The GDB/LLDB JIT interface *is* working: `target modules lookup -f
  program.wx -l 7` and `target modules lookup -n compute`, run interactively
  in lldb once the JIT module is loaded, both resolve correctly to real
  addresses inside the JIT-registered module.
- But `breakpoint set --file program.wx --line 7` — the exact mechanism VS
  Code's gutter/line breakpoints compile down to — stays "no locations
  (pending)" forever, **even when set after the module is already loaded**
  (confirmed by setting it only after stopping at a breakpoint on
  `__jit_debug_register_code`, at which point the module was already
  visible in `image list`).
- `breakpoint set --name compute` (symbol/function-name based), by
  contrast, **does** bind and stop correctly — reports the right file
  (`program.wx`) and line, shows source context, and `frame variable`
  returns real values for locals (arguments right at function entry can
  show "optimized out," which is normal debugger behavior, not specific to
  this).

This matches an existing, unrelated wasmtime issue
([#11830](https://github.com/bytecodealliance/wasmtime/issues/11830),
"Couldn't materialize any expression on macOS with LLDB"), where a
different symptom on the same subsystem got this reply from wasmtime core
maintainer `cfallin`:

> "our native-debugger support has been quite best-effort, and is more or
> less unmaintained at the moment. The DWARF translation has had known
> bugs, and we know that various aspects of our lowering can cause values
> to become unavailable... I wouldn't recommend relying on debugging by
> attaching a native debugger to wasmtime at the moment."

They also mention actively working on "guest debugging" as a *replacement*
for native-debugger attach, not a fix to the current path. A different
contributor also noted they could **not** reproduce a related crash on
Linux with `lldb-20`, suggesting the macOS lldb + wasmtime JIT interface
combination specifically is the weaker one — consistent with what we found.

**Practical takeaway**: this one probably isn't worth chasing upstream
right now — it's a known, maintainer-acknowledged gap on a path they're
already planning to replace, not a bug nobody's aware of. The workaround
(function-name breakpoints) is fully usable in the meantime.

## Existing mentions upstream, for bugs 1-3

Searched `bytecodealliance/wasmtime` issues and PRs (via `gh search
issues`/`gh search prs`) for: `ModuleMemoryOffset`, `InvalidAttributeValue`,
`"attribute value is an invalid for writing"`, `"no memory" debug`, `vmctx
debug panic`. No existing issue matches bugs 1-3 (the crash cases) exactly.

Related, but not the same:

- **[#894](https://github.com/bytecodealliance/wasmtime/issues/894) /
  [#896](https://github.com/bytecodealliance/wasmtime/issues/896)** — the
  original author of this code flagged that `ModuleMemoryOffset::Imported`
  handling was "temporarily stubbed" and incomplete. Same subsystem, same
  file, but about *imported* memories specifically, not the *zero-memories*
  case, and doesn't mention a crash.
- **[#5537](https://github.com/bytecodealliance/wasmtime/issues/5537)** —
  "Reimplement Wasmtime's DWARF transform and debugging support", the
  general tracking issue acknowledging this whole subsystem is
  known-incomplete. Bugs 1-3 would be data points for that issue, not
  duplicates of it.
- **[#887](https://github.com/bytecodealliance/wasmtime/issues/887)** —
  "Assertion failure generating debuginfo on a module with no functions" —
  same *flavor* of problem (an edge-case module shape crashing debug-info
  generation), different trigger, already fixed.
- **[#11830](https://github.com/bytecodealliance/wasmtime/issues/11830)** —
  the macOS-lldb issue quoted above for bug 4.

## Could we help fix bugs 1-3? How hard would it be?

Yes, these look like reasonable upstream contributions:

- **Root-causing them** (what took most of the effort here): genuinely
  hard without local reproduction — the error message is generic and
  raised one level removed from the actual cause (inside gimli's `write`
  module). Confirming it required building a small local repro against the
  `wasmtime` crate directly (with `RUST_LOG=debug-info-transform=trace` on
  a debug build) to watch exactly which DIE/attribute/operation it died on,
  for both bug 1 and bug 3 separately.
- **The fixes themselves, once found: easy — for bug 1/2.** A single,
  localized change in `attr.rs`, following an idiom already in the same
  file (catch the error, degrade instead of hard-propagating).
- **Bug 3 is a bit more involved**: it needs `Operation::Piece` to actually
  participate in `need_deref` tracking (or the whole-expression flag
  approach reworked to be piece-aware), which touches the core parsing
  loop rather than just an error-handling call site — still localized to
  one function, but requires understanding the per-piece semantics rather
  than just adding a `continue`.
- **Testing: easy for all three.** Minimal repros are small `.wat`/2-line
  wx programs; we already have equivalent `wx-compiler` unit tests using
  the `wasmtime` crate directly that could be adapted.

If you want, I can draft the actual wasmtime patches + minimal `.wat`
regression tests and open the issues/PRs, but that's a call for you to
make given it involves posting to a repo we don't control.

## Practical setup that works today: wasmtime + CodeLLDB in VS Code

`.vscode/launch.json` (already added to this repo):

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "wasmtime: debug dwarf-playground/program.wasm",
      "type": "lldb",
      "request": "launch",
      "program": "/opt/homebrew/bin/wasmtime",
      "args": ["run", "-D", "debug-info=y", "--invoke", "compute", "program.wasm", "5"],
      "cwd": "${workspaceFolder}/dwarf-playground",
      "stopOnEntry": false,
      "initCommands": ["settings set plugin.jit-loader.gdb.enable on"]
    }
  ]
}
```

To actually hit a breakpoint (given bug 4 above):

1. Open the **Run and Debug** panel, open the **Breakpoints** section, click
   the **+** ("Add Function Breakpoint") button — *not* a gutter click in
   `program.wx`.
2. Type a function name, e.g. `compute` or `add`.
3. Press F5 (or select this launch config and start debugging).
4. It should stop inside the named function, with correct source location
   and working variable inspection (`frame variable` / hover / Watch).

Gutter/line breakpoints in `program.wx` will show as set but will never
actually bind or stop execution (bug 4) — this is expected given the
current state of wasmtime's native-debugger support, not something to
debug further on our end.
