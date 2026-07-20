<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="banner.svg">
    <source media="(prefers-color-scheme: light)" srcset="banner-light.svg">
    <img src="banner.svg" alt="WX banner" width="540">
  </picture>
</p>

<h1 align="center">
WX - Web Assembly Expressive Language
</h1>

WX is a Rust-inspired language that compiles directly to WebAssembly. It stays close to the WASM spec instead of hiding it, so the code you write maps predictably onto the module you get — no hidden runtime, no GC, no surprises.

This project is part of my bachelor's thesis exploring what it takes to build a full WASM compiler from scratch. It's still early — expect rough edges.

## Features

- Rust-inspired syntax: structs, traits, generics, `impl` blocks, pattern-free control flow
- Compiles straight to WASM bytecode, with a low-abstraction, spec-aligned type system
- Generics with monomorphization, `#[inline]`, dead-code elimination, and sea-of-nodes optimization passes
- Multi-file modules, WASM imports/exports, and `#[intrinsic]` bindings for memory ops
- Tooling: an LSP with diagnostics/completions/formatting, and a VS Code extension

## Getting Started

Try it instantly in the browser playground: [wx-lang.deno.dev](https://wx-lang.deno.dev/)

**Install the CLI from npm**

```bash
npm install -g @wx-lang/cli

wx compile ./main.wx
```

**Or build the native CLI from source**

```bash
cargo build --release -p wx-cli
./target/release/wx compile ./main.wx
```

**Editor support**

Search for "WX" in the VS Code Extensions view for syntax highlighting, diagnostics, completions, and formatting. Other editors aren't supported yet.

## Examples

Sample programs live in the [`examples`](examples) directory.

## Architecture

![Architecture diagram](./web/public/pipeline.webp)

## Credits

Here are some of the resources I used to learn about compilers and wasm while working on this project:

- [Youtube channel of Julian Hartl](https://www.youtube.com/channel/UCFRB-SI9q_p5Erjsj-EpOGw)
- [Youtube channel of Jon Gjengset](https://www.youtube.com/@jonhoo)
- [Youtube channel of Tyler Laceby](https://www.youtube.com/@tylerlaceby)
- [Simple but Powerful Pratt Parsing by Alex Kladov](https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html)
- [WASM IO conference talks](https://www.youtube.com/@wasmio)
- Youtube channels with recordings of rust conferences like [Rust NL](https://www.youtube.com/@rustnederlandrustnl) and [EuroRust](https://www.youtube.com/@eurorust)
- [Conference talks of Andrew Kelley](https://andrewkelley.me/)
- [rats159](https://www.youtube.com/@awesome.rats159)
- [Allocation Strategies by gingerBill](https://www.youtube.com/watch?v=BxLEymP1f6o)