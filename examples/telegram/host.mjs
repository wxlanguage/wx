// Node host adapter for a WX Telegram bot.
//
// The WX module owns the bot; this file owns HTTP, JSON and process lifetime:
//
//   node run.mjs            # demo if no token, live if TELEGRAM_BOT_TOKEN is set
//   node run.mjs --demo     # scripted conversation, no network
//   node run.mjs --repl     # type messages locally, no network
//
// `run` is generic. A bot package's run.mjs only supplies its Wasm file, a
// build hint and (optionally) a demo script.

import { readFile, access } from "node:fs/promises";
import { randomBytes } from "node:crypto";
import { createInterface } from "node:readline/promises";
import { fileURLToPath } from "node:url";

export const INPUT_CAP = 65536;
export const OUTPUT_OFFSET = 65536;
export const OUTPUT_CAP = 65536;

const encoder = new TextEncoder();
const decoder = new TextDecoder();

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

/// Instantiates a bot module with the host imports the WX framework declares.
/// The returned `handle` takes text or raw bytes and copies the reply out of
/// the shared `io` memory before the next call can overwrite it.
export async function instantiateBot(wasm, options = {}) {
    const bytes = await readFile(wasm);
    const module = await WebAssembly.compile(bytes);
    const io = new WebAssembly.Memory({ initial: 2 });

    let seed = options.seed;
    const nextSeed = () => {
        if (seed === undefined) return randomBytes(4).readUInt32LE(0);
        seed = (Math.imul(seed >>> 0, 1664525) + 1013904223) >>> 0;
        return seed;
    };

    const instance = await WebAssembly.instantiate(module, {
        host: {
            io,
            random_u32: nextSeed,
        },
    });
    const exports = instance.exports;

    function handle(chatId, textOrBytes, capacity = OUTPUT_CAP) {
        const input = typeof textOrBytes === "string"
            ? encoder.encode(textOrBytes)
            : textOrBytes;
        if (input.length > INPUT_CAP) {
            throw new RangeError(`input is ${input.length} bytes; limit is ${INPUT_CAP}`);
        }
        if (capacity > OUTPUT_CAP) {
            throw new RangeError(`output capacity is ${capacity}; limit is ${OUTPUT_CAP}`);
        }
        new Uint8Array(io.buffer, 0, input.length).set(input);
        const length = exports.handle(
            BigInt(chatId),
            0,
            input.length,
            OUTPUT_OFFSET,
            capacity,
        );
        const reply = Uint8Array.from(
            new Uint8Array(io.buffer, OUTPUT_OFFSET, length),
        );
        return { length, bytes: reply, text: decoder.decode(reply) };
    }

    return { module, instance, exports, io, handle };
}

/// Splits a reply into Telegram-sized chunks without cutting a scalar value.
export function chunkText(text, limit = 3900) {
    const chunks = [];
    let current = "";
    let units = 0;
    for (const scalar of text) {
        if (units + scalar.length > limit && current.length > 0) {
            chunks.push(current);
            current = "";
            units = 0;
        }
        current += scalar;
        units += scalar.length;
    }
    if (current.length > 0 || chunks.length === 0) chunks.push(current);
    return chunks;
}

async function telegram(method, token, payload) {
    for (let attempt = 0; attempt < 3; attempt++) {
        const response = await fetch(
            `https://api.telegram.org/bot${token}/${method}`,
            {
                method: "POST",
                headers: { "content-type": "application/json" },
                body: JSON.stringify(payload),
                signal: AbortSignal.timeout(30_000),
            },
        );
        const result = await response.json();
        if (result.ok) return result;
        if (result.error_code === 429) {
            const wait = (result.parameters?.retry_after ?? 3) + 1;
            console.error(`rate limited; retrying in ${wait}s`);
            await sleep(wait * 1000);
            continue;
        }
        throw new Error(`${method}: ${result.description ?? response.statusText}`);
    }
    throw new Error(`${method}: rate limited repeatedly`);
}

async function sendText(token, chatId, text) {
    for (const chunk of chunkText(text)) {
        if (chunk.length === 0) continue;
        await telegram("sendMessage", token, {
            chat_id: chatId,
            text: chunk,
            disable_web_page_preview: true,
        });
    }
}

async function poll(token, bot) {
    let offset = 0;
    let stopping = false;
    process.on("SIGINT", () => {
        stopping = true;
        console.log("\nstopping after the current poll...");
    });

    while (!stopping) {
        let result;
        try {
            const url = new URL(`https://api.telegram.org/bot${token}/getUpdates`);
            url.searchParams.set("timeout", "30");
            url.searchParams.set("offset", String(offset));
            url.searchParams.set("allowed_updates", JSON.stringify(["message"]));
            const response = await fetch(url, {
                signal: AbortSignal.timeout(40_000),
            });
            result = await response.json();
        } catch (error) {
            if (error.name === "AbortError" || error.name === "TimeoutError") {
                continue;
            }
            console.error(`poll failed: ${error.message}`);
            await sleep(3000);
            continue;
        }

        if (!result.ok) {
            if (result.error_code === 401 || result.error_code === 404) {
                throw new Error(`Telegram rejected the token: ${result.description}`);
            }
            if (result.error_code === 409) {
                throw new Error(
                    "another process is polling this bot; stop it or use a different token",
                );
            }
            console.error(`getUpdates: ${result.description ?? "unknown error"}`);
            await sleep(3000);
            continue;
        }

        for (const update of result.result) {
            offset = Math.max(offset, update.update_id + 1);
            const message = update.message;
            if (!message || typeof message.text !== "string") continue;

            const chatId = message.chat.id;
            const reply = bot.handle(chatId, message.text);
            const shown = reply.text.length > 200
                ? `${reply.text.slice(0, 200)}...`
                : reply.text;
            console.log(`[${chatId}] ${message.text} -> ${shown}`);
            if (reply.length > 0) {
                await sendText(token, chatId, reply.text);
            }
        }
    }
}

async function demo(bot, script) {
    for (const step of script) {
        const chat = step.chat ?? 1;
        const reply = bot.handle(chat, step.text);
        console.log(`\n[chat ${chat}] ${step.text}`);
        console.log(reply.text.split("\n").map((line) => `  ${line}`).join("\n"));
    }
}

async function repl(bot) {
    console.log("Local bot REPL. Type messages; `exit` or Ctrl+D to quit.");
    const lines = createInterface({
        input: process.stdin,
        output: process.stdout,
        terminal: process.stdin.isTTY,
    });
    lines.setPrompt("> ");
    lines.prompt();
    try {
        for await (const line of lines) {
            if (line === "exit" || line === ".exit" || line === "quit") break;
            const reply = bot.handle(1, line);
            console.log(reply.text);
            lines.prompt();
        }
    } finally {
        lines.close();
    }
}

/// Runs a bot package. `wasm` is a path or URL; `build` is the command to
/// print when it is missing; `demo` is a list of `{ chat?, text }` steps.
export async function run({ name = "WX bot", wasm, build, demo: script = [] }) {
    const flags = new Set(process.argv.slice(2));
    const token = process.env.TELEGRAM_BOT_TOKEN || process.env.BOT_TOKEN;

    try {
        await access(wasm);
    } catch {
        throw new Error(
            `missing ${wasm instanceof URL ? fileURLToPath(wasm) : wasm}` +
                (build ? `\nbuild it first:\n  ${build}` : ""),
        );
    }

    const useDemo = flags.has("--demo") || (!token && !flags.has("--repl"));
    const bot = await instantiateBot(wasm, useDemo ? { seed: 1 } : {});

    if (flags.has("--repl")) {
        await repl(bot);
        return;
    }
    if (useDemo) {
        console.log(`${name}: demo mode (no network). Set TELEGRAM_BOT_TOKEN for live mode.`);
        await demo(bot, script);
        return;
    }

    console.log(`${name}: polling Telegram`);
    await poll(token, bot);
}
