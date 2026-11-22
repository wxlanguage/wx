// Local host for the quiz bot. Build first:
//
//   wx build examples/telegram_bot -o examples/telegram_bot/main.wasm
//   node examples/telegram_bot/run.mjs           # demo without a token
//   TELEGRAM_BOT_TOKEN=... node examples/telegram_bot/run.mjs
//   node examples/telegram_bot/run.mjs --repl

import { run } from "../telegram/host.mjs";

await run({
    name: "WX quiz bot",
    wasm: new URL("./main.wasm", import.meta.url),
    build: "wx build examples/telegram_bot -o examples/telegram_bot/main.wasm",
    demo: [
        { text: "/start" },
        { text: "/ping" },
        { text: "/reverse héllo 🦀" },
        { text: "/len héllo 🦀" },
        { text: "/codepoints Hé🦀" },
        { text: "/roll 2d6" },
        { text: "/choose compile | test | ship" },
        { text: "/quiz" },
        { text: "/skip" },
        { text: "/score" },
        { chat: 2, text: "/quiz" },
        { chat: 2, text: "/score" },
        { text: "/quit" },
        { text: "/stats" },
    ],
});
