mod actor;
mod backend;
mod convert;
mod diagnostics;
mod documents;
mod hover;
mod projects;
mod rename;
mod requests;
mod semantic_tokens;
mod snapshot;
mod state;
pub mod task;
mod trace;

#[cfg(test)]
mod tests;

#[cfg(not(target_arch = "wasm32"))]
pub use backend::run_stdio;
pub use backend::{Backend, build_service};
