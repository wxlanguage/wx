pub mod ast;
pub mod codegen;
pub mod diagnostics;
mod index;
pub mod mir;
pub mod opt;
#[cfg(test)]
pub mod testing;
pub mod tir;
pub mod vfs;
pub mod wasm;
