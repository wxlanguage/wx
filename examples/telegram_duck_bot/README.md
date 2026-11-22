# WX duck bot

The smallest useful bot on the [`telegram`](../telegram) framework. It exists
to show reuse: a new bot is an action enum, a command table and a handler. It
also proves the framework has no hidden commands — `/ping` and `/id` are
unknown here because this bot did not register them.

## Commands

```
/start, /help
/quack
/shout <text>
/repeat <n> <text>
/about
/stats
```

## Build and run

```sh
cargo build -p wx-cli
wx build examples/telegram_duck_bot -o examples/telegram_duck_bot/main.wasm
node examples/telegram_duck_bot/run.mjs --demo
```

Live mode uses the same host adapter:

```sh
TELEGRAM_BOT_TOKEN=... node examples/telegram_duck_bot/run.mjs
```

## Test

```sh
node examples/telegram_duck_bot/test.mjs
```

The test checks generated help, the absence of framework built-ins, random
quacks, uppercase, bounded repetition, stats and short-buffer truncation.
