// Local host for the duck bot. Build first:
//
//   wx build examples/telegram_duck_bot -o examples/telegram_duck_bot/main.wasm
//   node examples/telegram_duck_bot/run.mjs

import { run } from "../telegram/host.mjs";

await run({
    name: "WX duck bot",
    wasm: new URL("./main.wasm", import.meta.url),
    build: "wx build examples/telegram_duck_bot -o examples/telegram_duck_bot/main.wasm",
    demo: [
        { text: "/start" },
        { text: "/quack" },
        { text: "/shout wasm" },
        { text: "/repeat 3 quack" },
        { text: "/about" },
        { text: "hello" },
        { text: "/stats" },
    ],
});
