pub mod ast;
pub mod codegen;
pub mod dwarf;
pub mod mir;
pub mod opt;
#[cfg(test)]
pub mod testing;
pub mod tir;
pub mod vfs;
pub mod wasm;

/// Selects which per-function lowering pipeline `codegen::Builder::build`
/// uses, and (via each caller's own MIR-cleanup step) whether `#[inline]`
/// substitution runs.
///
/// `Release` — the sea-of-nodes `opt::builder`/`opt::scheduler` pipeline:
/// `#[inline]` substitution, CSE, spill decisions. Today's only behavior.
///
/// `Debug` — `mir::scheduler`, lowering the MIR expression tree directly:
/// no inlining, no CSE, no scheduling decisions — every declared local gets
/// its own fixed WASM slot and instructions come out in exactly the order
/// the source implies.
#[derive(Clone, Copy, PartialEq)]
pub enum CompilationMode {
	Release,
	Debug,
}
