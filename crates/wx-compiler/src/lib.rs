pub mod ast;
#[cfg(test)]
mod backend_tests;
pub mod codegen;
pub mod diagnostics;
mod index;
pub mod mir;
pub mod opt;
mod small_vec;
#[cfg(test)]
pub mod testing;
pub mod tir;
pub mod vfs;
pub mod wasm;
