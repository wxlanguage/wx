//! A Model Context Protocol server that lets an agent inspect WX packages:
//! their diagnostics, their items and what the names in their code mean,
//! and the WebAssembly they build to. It never edits files or runs code.
//!
//! Every tool call loads the package from disk afresh, since an agent edits
//! the files directly, and answers from the compiler's own semantic data.
//! Items are named by their paths as written from the root package: its
//! own items unprefixed, a dependency's through the package instance
//! naming it, core's unprefixed, as the prelude makes them.

mod analysis;
mod server;
mod tools;

pub use server::serve_stdio;
