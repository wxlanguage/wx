// Tests for the WX Telegram bot core.
//
//   node examples/telegram_bot/test.mjs
//
// The test builds the package with the `wx` on PATH (`WX` overrides it), then
// drives `handle` through the same host ABI a real adapter uses: a host-owned
// `io` memory, a request slice, and an output slice. No network is involved.

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../../", import.meta.url));
const packageDir = join(root, "examples/telegram_bot");
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-telegram-"));
const wasmPath = join(temporary, "telegram_bot.wasm");

const INPUT_CAP = 65536;
const OUTPUT_OFFSET = 65536;
const OUTPUT_CAP = 65536;

try {
    const built = spawnSync(process.env.WX || "wx", [
        "build",
        packageDir,
        "-o",
        wasmPath,
    ], { cwd: root, encoding: "utf8", timeout: 60000 });
    if (built.error) throw built.error;
    assert.equal(built.status, 0, built.stdout + built.stderr);

    const module = await WebAssembly.compile(await readFile(wasmPath));
    assert.deepEqual(
        WebAssembly.Module.imports(module),
        [
            { module: "host", name: "io", kind: "memory" },
            { module: "host", name: "random_u32", kind: "function" },
        ],
    );
    // The private `state` memory is deliberately not exported: the host can
    // call the bot, but cannot read or edit the chat table.
    assert.deepEqual(
        WebAssembly.Module.exports(module).map(({ name, kind }) => `${name}:${kind}`),
        ["handle:function"],
    );

    const encoder = new TextEncoder();
    const decoder = new TextDecoder();

    /// A fresh instance has a fresh state memory, so these groups are isolated.
    function makeBot(seed = 0x12345678) {
        const io = new WebAssembly.Memory({ initial: 2 });
        const host = {
            io,
            random_u32() {
                // A tiny deterministic generator for the test's own sequencing;
                // the module has its own xorshift once seeded.
                seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
                return seed;
            },
        };
        return WebAssembly.instantiate(module, { host }).then(({ exports }) => {
            function sendBytes(chatId, bytes, capacity = OUTPUT_CAP) {
                assert.ok(bytes.length <= INPUT_CAP, "test input fits one page");
                new Uint8Array(io.buffer, 0, INPUT_CAP).fill(0);
                new Uint8Array(io.buffer, 0, bytes.length).set(bytes);
                const length = exports.handle(
                    BigInt(chatId),
                    0,
                    bytes.length,
                    OUTPUT_OFFSET,
                    capacity,
                );
                return {
                    length,
                    bytes: new Uint8Array(io.buffer, OUTPUT_OFFSET, length),
                    text: decoder.decode(new Uint8Array(io.buffer, OUTPUT_OFFSET, length)),
                };
            }

            return {
                send(chatId, text, capacity) {
                    return sendBytes(chatId, encoder.encode(text), capacity);
                },
                sendBytes,
            };
        });
    }

    const answers = new Map([
        ["What does Wasm call its linear address space?", 2],
        ["Which WX type names a pointer into a specific memory?", 2],
        ["How many memories can one Wasm module use?", 3],
        ["What runs WX code after it is compiled?", 1],
        ["Which WASI Preview 1 call reads a file descriptor?", 1],
        ["What does a WX `funcref` refer to?", 2],
        ["What is WX's baseline runtime policy?", 3],
        ["What is one WX memory page worth?", 2],
    ]);

    function questionOf(text) {
        const match = text.match(/Question: (.*?)\n1\) /s);
        assert.ok(match, `question in reply: ${JSON.stringify(text)}`);
        assert.ok(answers.has(match[1]), `known question: ${match[1]}`);
        return match[1];
    }

    // ── stateless commands ───────────────────────────────────────────────────
    {
        const bot = await makeBot();
        assert.equal(bot.send(1n, "/ping").text, "pong");
        assert.equal(bot.send(1n, "/ping@WXBot").text, "pong");
        assert.equal(bot.send(1n, "   /ping   ").text, "pong");
        assert.match(bot.send(1n, "/help").text, /\/codepoints <text>/);
        assert.match(bot.send(1n, "/start").text, /^Hi! I run entirely in a WebAssembly module\./);

        assert.equal(bot.send(1n, "/echo  hello  world ").text, "hello  world");
        assert.equal(bot.send(1n, "/echo héllo 🦀").text, "héllo 🦀");
        assert.equal(bot.send(1n, "/upper hello λ").text, "HELLO λ");
        assert.equal(bot.send(1n, "/lower HELLO Λ").text, "hello Λ");
        assert.equal(bot.send(1n, "/reverse héllo 🦀").text, "🦀 olléh");
        assert.equal(bot.send(1n, "/reverse a").text, "a");
        assert.equal(bot.send(1n, "/reverse ").text, "Usage: /reverse <text>");

        assert.equal(
            bot.send(1n, "/len héllo 🦀").text,
            "bytes: 11\nscalar values: 7\nutf-8: valid",
        );
        assert.equal(
            bot.send(1n, "/codepoints Hé🦀").text,
            "U+0048 U+00e9 U+1f980",
        );
        assert.match(bot.send(1n, "/codepoints " + "a".repeat(40)).text, /\.\.\.$/);

        assert.equal(bot.send(1n, "/id").text, "chat id: 1");
        assert.equal(bot.send(1n, "/id").text, "chat id: 1");
        assert.equal(bot.send(-100123n, "/id").text, "chat id: -100123");
        assert.equal(bot.send(1n, "/nope").text, "Unknown command. Send /help.");
        assert.equal(bot.send(1n, "/").text, "Unknown command. Send /help.");
        assert.equal(bot.send(1n, "   ").text, "Send /help to see what I can do.");
    }

    // ── dice, choices, oracle ────────────────────────────────────────────────
    {
        const bot = await makeBot();
        assert.match(bot.send(1n, "/roll").text, /^1d6: [1-6]$/);
        assert.match(bot.send(1n, "/roll 6").text, /^1d6: [1-6]$/);

        const three = bot.send(1n, "/roll 3d4").text;
        const threeMatch = three.match(/^3d4: ([1-4]) \+ ([1-4]) \+ ([1-4]) = (\d+)$/);
        assert.ok(threeMatch, three);
        assert.equal(
            Number(threeMatch[1]) + Number(threeMatch[2]) + Number(threeMatch[3]),
            Number(threeMatch[4]),
        );

        for (const bad of ["/roll 0d6", "/roll 1d1", "/roll 101d6", "/roll 1d1000001", "/roll x", "/roll 2x6"]) {
            assert.match(bot.send(1n, bad).text, /^Usage: \/roll/);
        }

        assert.match(bot.send(1n, "/choose a | b | c").text, /^I choose: [abc]$/);
        assert.match(bot.send(1n, "/choose  one | two ").text, /^I choose: (one|two)$/);
        assert.match(bot.send(1n, "/choose a |").text, /^Usage: \/choose/);
        assert.match(bot.send(1n, "/choose a").text, /^Usage: \/choose/);

        const oracle = bot.send(1n, "/8ball will it compile?").text;
        assert.match(oracle, /^🎱 /);
        assert.match(bot.send(1n, "/8ball").text, /^Ask a question:/);
    }

    // ── invalid UTF-8 never traps ────────────────────────────────────────────
    {
        const bot = await makeBot();
        const invalid = [
            [0xc0, 0x80],                   // overlong NUL
            [0xed, 0xa0, 0x80],             // surrogate
            [0xf4, 0x90, 0x80, 0x80],       // above U+10FFFF
            [0xe2, 0x82],                   // truncated
            [0x80],                         // stray continuation
        ];
        for (const bytes of invalid) {
            const input = new Uint8Array([...encoder.encode("/len "), ...bytes]);
            const result = bot.sendBytes(1n, input);
            assert.match(result.text, /^bytes: \d+\nscalar values: \?\nutf-8: invalid$/);
        }
        const reverse = bot.sendBytes(
            1n,
            new Uint8Array([...encoder.encode("/reverse "), 0xff, 0x41]),
        );
        assert.equal(reverse.text, "That is not valid UTF-8.");
        const points = bot.sendBytes(
            1n,
            new Uint8Array([...encoder.encode("/codepoints "), 0xff, 0x41]),
        );
        assert.equal(points.text, "That is not valid UTF-8.");
    }

    // ── quiz state, per chat ─────────────────────────────────────────────────
    {
        const bot = await makeBot();
        assert.equal(bot.send(1n, "/score").text, "No quiz yet. Send /quiz to start one.");

        const first = bot.send(1n, "/quiz").text;
        assert.match(first, /^New quiz! Question: /);
        const firstQuestion = questionOf(first);
        const firstAnswer = answers.get(firstQuestion);

        const correct = bot.send(1n, String(firstAnswer)).text;
        assert.match(correct, /^Correct! Score: 1\/1\.\n\nQuestion: /);
        const secondQuestion = questionOf(correct);
        assert.notEqual(secondQuestion, firstQuestion, "no immediate repeat");

        assert.equal(
            bot.send(1n, "/score").text,
            "Score: 1 correct out of 1 answered. Quiz running.",
        );
        // Another chat has its own slot and score.
        assert.equal(bot.send(2n, "/score").text, "No quiz yet. Send /quiz to start one.");

        const secondAnswer = answers.get(secondQuestion);
        const wrongChoice = (secondAnswer % 3) + 1;
        const wrong = bot.send(1n, String(wrongChoice)).text;
        assert.match(wrong, /^Nope\. The answer was \d\. Score: 1\/2\./);

        assert.match(bot.send(1n, "/answer 2").text, /^(Correct!|Nope\.)/);
        assert.match(bot.send(1n, "/answer 9").text, /^Reply with 1, 2 or 3\.$/);
        assert.match(bot.send(1n, "/answer x").text, /^Reply with 1, 2 or 3\.$/);

        assert.match(bot.send(1n, "/skip").text, /^Skipped\. The answer was \d\./);
        assert.match(bot.send(1n, "/quit").text, /^Quiz stopped\. Final score: \d+\/\d+\.$/);
        assert.match(bot.send(1n, "/score").text, / No quiz is running\.$/);
        assert.equal(bot.send(1n, "/quit").text, "No quiz is running.");
        assert.equal(bot.send(1n, "/skip").text, "No quiz is running. Send /quiz to start one.");
        assert.equal(bot.send(1n, "/reset").text, "Score cleared.");
        assert.match(bot.send(1n, "/score").text, /^Score: 0 correct out of 0 answered\./);

        // The same slot can start again.
        assert.match(bot.send(1n, "/quiz").text, /^New quiz! Question: /);
        assert.match(bot.send(1n, "/quiz").text, /^A quiz is running\./);
    }

    // ── 32-chat table is bounded, not a trap ─────────────────────────────────
    {
        const bot = await makeBot();
        for (let chat = 1; chat <= 32; chat++) {
            assert.match(bot.send(chat, "/quiz").text, /^New quiz! /);
        }
        assert.equal(
            bot.send(33, "/quiz").text,
            "State table is full; I am tracking too many chats.",
        );
        assert.match(bot.send(1, "/stats").text, /chat slots used: 32\/32/);
    }

    // ── host buffer is caller-owned: short output truncates, never traps ─────
    {
        const bot = await makeBot();
        const short = bot.send(1n, "/help", 20);
        assert.equal(short.length, 20);
        assert.equal(short.text, "Commands:\n/start gre");

        const zero = bot.send(1n, "/help", 0);
        assert.equal(zero.length, 0);

        // A max-size input fits the input page and a max-size reply fits the
        // output page. Neither side allocates.
        const payload = "a".repeat(60000);
        const big = bot.send(1n, "/echo " + payload);
        assert.equal(big.length, 60000);
        assert.equal(big.text, payload);

        // `handle` is safe to call thousands of times; no per-call state leaks.
        for (let i = 0; i < 1000; i++) bot.send(1n, "/ping");
        assert.match(bot.send(1n, "/stats").text, /updates handled: 1004/);
    }

    console.log("telegram_bot: all tests passed");
} finally {
    await rm(temporary, { recursive: true, force: true });
}
