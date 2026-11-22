# WX quiz bot

A stateful Telegram bot built on the [`telegram`](../telegram) framework and
the [`utf8`](../utf8) package. It demonstrates that the framework has no
built-in commands: this bot's `/ping`, `/help`, `/id`, `/stats` and everything
else are rows in its own declarative table.

## Commands

```
/start, /help
/ping
/echo <text>          /upper <text>       /lower <text>
/reverse <text>       /len <text>         /codepoints <text>
/roll [NdM]           /choose a | b | c   /8ball <question>
/id                   /stats
/quiz                 /answer <1|2|3>     /skip
/score                /reset              /quit
```

`/reverse`, `/len` and `/codepoints` use `utf8::Str`, so they work with
multi-byte scalar values rather than bytes. `/reverse héllo 🦀` returns
`🦀 olléh`, and invalid UTF-8 is reported without trapping.

The quiz keeps a fixed table of 32 chat slots in a private memory. Each slot
has `chat_id`, active flag, current question, score and answered count. Slot 0
is empty and Wasm zero-initialises the memory, so there is no bootstrap pass.
Two chats have independent quizzes and scores.

## Build and run

```sh
cargo build -p wx-cli

wx build examples/telegram_bot -o examples/telegram_bot/main.wasm
node examples/telegram_bot/run.mjs --demo
```

The demo needs no token and no network. It runs a scripted conversation,
including two chats to show state isolation.

For a real bot:

1. Create a bot with [@BotFather](https://t.me/BotFather) and copy the token.
2. Start the long poll:

```sh
TELEGRAM_BOT_TOKEN=123:abc node examples/telegram_bot/run.mjs
```

`run.mjs` uses the shared [`host.mjs`](../telegram/host.mjs): it polls
`getUpdates`, calls the WX module, and posts replies with `sendMessage`.
Long replies are split on scalar-value boundaries. The process keeps state in
Wasm memory; restarting it clears quizzes and scores.

For local play without a token:

```sh
node examples/telegram_bot/run.mjs --repl
```

## Test

```sh
node examples/telegram_bot/test.mjs
```

The test builds the package, instantiates it with a host-owned `io` memory, and
checks routing, generated help, UTF-8 edge cases, the quiz state machine,
per-chat isolation, the 32-slot bound, short output buffers, invalid UTF-8,
and a 60 KB echo. It never touches the network.

## Why the split?

- [`telegram`](../telegram) owns the host ABI, `Response`, command parser,
  declarative routing and generated help. It knows no command names.
- [`utf8`](../utf8) owns strict UTF-8 validation and the borrowed `Str<M>`
  type. It knows nothing about Telegram.
- This package owns the quiz, the text tools and the command table.

[`telegram_duck_bot`](../telegram_duck_bot) is a second, much smaller bot on the
same framework.
