# telegram — a small Telegram bot framework for WX

A reusable framework, not a bot. It owns the host boundary, command parsing,
reply formatting and routing; applications provide a command table and a
handler. There are **no built-in commands** in the framework: `/ping`, `/help`,
`/id` and `/stats` are ordinary rows in an application's table.

Telegram's Bot API is HTTPS + JSON, and WASI Preview 1 has no sockets. The WX
module therefore starts at the boundary a host can actually provide:

```
host::io       host-owned memory: request text in, reply bytes out
random_u32     a seed for the framework's xorshift generator
```

The Node adapter in [`host.mjs`](host.mjs) polls `getUpdates`, extracts
`message.chat.id` and `message.text`, calls the module, and sends the reply.
`telegram::serve` takes typed slices; `telegram::serve_raw` is the same entry
point with plain `u32` addresses for hosts that prefer that shape.

## API

- **`Response`** — a by-value reply builder over the host's output buffer.
  `res.text("...")`, `res.input(args)`, `res.decimal(n)`, `res.signed64(id)`,
  `res.hex_width(value, digits)`, `res.newline()`, `res.space()`.
  A short output buffer truncates; it never traps.
- **`Context`** — per-update data; currently `ctx.chat_id()`.
- **`Command<A>`** — one declarative route: `name`, `description`, `action`.
  The framework uses the table for lookup and generated help.
- **`Bot`** — the application trait: associated `Action`, plus `command`,
  `message` and an overridable `unknown`.
- **`telegram::help`** — renders the table, so help cannot drift from routing.
- **`telegram::stats`** — the framework's counters; applications append theirs.

The static table is the WX equivalent of grammY's
`bot.command("name", handler)`: no closures, no heap, and the compiler checks
the action type. A command can have aliases by adding rows with the same action.

## A minimal bot

```wx
package "telegram" as telegram;

use telegram::{Input, Response};

struct App(version: u8);

enum Action(value: u32) {
    Start = 0,
    Help,
    Echo,
}

const COMMANDS: telegram::text::&[telegram::Command<Action>] = [
    telegram::Command("start", "meet the bot", Action::Start),
    telegram::Command("help", "show this help", Action::Help),
    telegram::Command("echo", "<text> repeat text", Action::Echo),
];

impl telegram::Bot for App {
    type Action = Action;

    func command(self: Self, res: Response, ctx: telegram::Context, action: Action, args: Input) -> Response {
        _ = ctx;
        match (action) {
            Action::Start => telegram::help(res.text("Hello!\n\n"), COMMANDS),
            Action::Help => telegram::help(res, COMMANDS),
            Action::Echo => res.input(telegram::trim(args)),
        }
    }

    func message(self: Self, res: Response, ctx: telegram::Context, text: Input) -> Response {
        _ = ctx; _ = text;
        res.text("Send /help.")
    }
}

func handle(chat_id: i64, input: telegram::Input, output: telegram::Output) -> u32 {
    telegram::serve(App(1), COMMANDS, chat_id, input, output)
}

export { handle }
```

`App` is passed by value; make it zero-sized or small. Application state lives
in a memory the application declares (or in globals), not in the router.

## Host adapter

Build the bot package, then:

```sh
node run.mjs                # demo if no token, live if TELEGRAM_BOT_TOKEN is set
node run.mjs --demo         # scripted conversation
node run.mjs --repl         # local REPL, chat id 1
TELEGRAM_BOT_TOKEN=... node run.mjs
```

The adapter splits long replies on scalar values, retries rate limits, reports
409 conflicts, and copies replies out of the shared memory before the next
call. It assumes text-only messages; media, callbacks and inline keyboards are
not modelled yet. `host.mjs` can also be imported directly:

```js
import { instantiateBot } from "../telegram/host.mjs";
const bot = await instantiateBot(new URL("./main.wasm", import.meta.url), { seed: 1 });
const reply = bot.handle(123, "/help");
```

## Limits

- Replies are plain text; `parse_mode` and escaping are host concerns.
- State is in Wasm memory and is lost when the process exits.
- One process should poll one token (the host reports Telegram's 409).
- No middleware chain, sessions, inline keyboards or media yet. The declarative
  table is the extension point for commands.
- UTF-8 is a separate package: [`../utf8`](../utf8). Applications that need
  validated input use `utf8::Str::from_bytes`.

## Check

```sh
wx check examples/telegram
```

The framework is exercised end-to-end by
[`../telegram_bot/test.mjs`](../telegram_bot/test.mjs) and
[`../telegram_duck_bot/test.mjs`](../telegram_duck_bot/test.mjs).
