# WX for VS Code

[![Visual Studio Marketplace Version](https://img.shields.io/visual-studio-marketplace/v/mellkam.wx-vscode)](https://marketplace.visualstudio.com/items?itemName=mellkam.wx-vscode)

Language support for [WX](https://github.com/wxlanguage/wx), a Rust-inspired language that compiles directly to WebAssembly. Try WX in the browser first at [wx-lang.deno.dev](https://wx-lang.deno.dev/) if you just want to poke around without installing anything.

## Features

- Diagnostics as you type
- Hover, go to definition, find references, rename
- Completions and signature help
- Semantic highlighting
- Format on save

## Requirements

This extension talks to the `wx` CLI's language server — it doesn't bundle a binary. Install `wx` and make sure it's on your `PATH`:

```bash
npm install -g @wx-lang/cli
```

or build it from source (see the [main README](https://github.com/wxlanguage/wx#readme)). If `wx` isn't on your `PATH`, point the extension at it directly with the `wx.path` setting.

## Getting Started

1. Install this extension from the [Marketplace](https://marketplace.visualstudio.com/items?itemName=mellkam.wx-vscode).
2. Install the `wx` CLI (above).
3. Open a `.wx` file — the language server starts automatically.

## Settings

| Setting | Description |
| --- | --- |
| `wx.path` | Path to the `wx` executable. Leave empty to resolve it from `PATH`. |
| `wx.formatter.indentSize` | Spaces per indent level (default `2`). |
| `wx.formatter.maxWidth` | Max line width for formatting (default `80`). |

## Commands

- **WX: Restart Language Server** — restart the server without reloading the window.

## Feedback

Found a bug or missing feature? [Open an issue](https://github.com/wxlanguage/wx/issues).
