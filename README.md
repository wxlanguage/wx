<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="banner.svg">
    <source media="(prefers-color-scheme: light)" srcset="banner-light.svg">
    <img src="banner.svg" alt="WX banner" width="540">
  </picture>
</p>

<h1 align="center">
WX Language Repository
</h1>

WX is an experimental programming language that compiles to WebAssembly.
Memories, globals, imports, exports, and selected instructions are expressed in
source code and checked through the type system.

The project explores a language organized around WebAssembly's resources, with
allocation and runtime policies left to libraries and applications. It uses
Rust-inspired syntax, type inference, traits, and generics to work with those
resources. Its focus is code that needs direct control over a module's memories
and host interface.

## Design

- **Memory identity in types.** A pointer names the memory it addresses:
  `a::&u8` and `b::&u8` point into different memories. Functions can be generic
  over memories, including their address types. The checker rejects a pointer
  into one memory where a pointer into another is required.
- **Explicit host boundaries.** Source declarations specify imported and
  exported functions, memories, and globals. A program can use host-provided
  memory or define its own.
- **A minimal baseline.** Programs do not require a built-in allocator or garbage
  collector. Selected Wasm instructions are available as typed functions, and
  libraries build abstractions on top.

## Current state

WX is under active development. The native compiler, formatter, and language
server work, with example programs for browsers and WASI Preview 1. Some
constructs accepted by the checker cannot yet be compiled to Wasm. Full memory
safety checking, effect tracking, Wasm GC, and stack switching remain future
work; syntax and APIs can change.

The project forms the basis of a bachelor's thesis, with development intended
to continue beyond it.

## Getting started

Install the CLI with npm or another npm-compatible package manager:

```sh
npm install -g @wx-lang/cli
```

You can also download a binary for your platform from
[GitHub Releases](https://github.com/wxlanguage/wx/releases).
Extract the archive and put `wx` (`wx.exe` on Windows) on your `PATH`.

To build from source instead, clone the repository and install with Rust and Cargo:

```sh
git clone https://github.com/wxlanguage/wx.git
cd wx
cargo install --path crates/wx-cli
```

In a new directory, create `wx.json`:

```json
{ "entry": "main.wx" }
```

Then create `main.wx`:

```wx
func add(a: i32, b: i32) -> i32 {
    a + b
}

export { add }
```

Run these commands in that directory:

```sh
wx check .
wx build . -o hello.wasm
wx format .
```

`hello.wasm` exports `add`; load it from a WebAssembly host. For example, in
Node.js, save this as `run.mjs` and run `node run.mjs`:

```js
import { readFileSync } from "node:fs";

const { instance } = await WebAssembly.instantiate(readFileSync("hello.wasm"));
console.log(instance.exports.add(20, 22)); // 42
```

The [VS Code extension](https://marketplace.visualstudio.com/items?itemName=mellkam.wx-vscode)
uses `wx lsp`; set `wx.path` if the CLI is not on your `PATH`.

## Examples

See [two memories](examples/two_memories) for typed memory separation,
[hello browser](examples/hello_browser) for host imports, and
[WASI word count](examples/wasi_wc) for a command-line application.
More packages live in [examples/](examples).

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
