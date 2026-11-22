// Tests for the second bot, including proof that the framework has no
// built-in commands: this bot does not register `/ping`, so `/ping` is unknown.

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { instantiateBot } from "../telegram/host.mjs";

const root = fileURLToPath(new URL("../../", import.meta.url));
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-duck-"));
const wasm = join(temporary, "duck.wasm");

try {
    const built = spawnSync(process.env.WX || "wx", [
        "build",
        join(root, "examples/telegram_duck_bot"),
        "-o",
        wasm,
    ], { cwd: root, encoding: "utf8", timeout: 60000 });
    if (built.error) throw built.error;
    assert.equal(built.status, 0, built.stdout + built.stderr);

    const bot = await instantiateBot(wasm, { seed: 1 });
    const send = (text) => bot.handle(1, text).text;

    assert.match(send("/start"), /^Quack\. I am a second bot/);
    assert.match(send("/help"), /^Commands:\n\/start /);
    assert.match(send("/help"), /\/repeat <n> <text>/);
    assert.doesNotMatch(send("/help"), /\/ping/);

    // No commands are built into the framework.
    assert.equal(send("/ping"), "No such command. Try /help.");
    assert.equal(send("/id"), "No such command. Try /help.");
    assert.equal(send("/nope"), "No such command. Try /help.");

    assert.ok(["Quack.", "Quack quack!", "Quaaack."].includes(send("/quack")));
    assert.equal(send("/shout hello λ"), "HELLO λ!!!");
    assert.equal(send("/shout"), "Usage: /shout <text>");
    assert.equal(send("/repeat 3 hi"), "hi\nhi\nhi");
    assert.equal(send("/repeat 1 a b c"), "a b c");
    assert.match(send("/repeat 0 hi"), /^Usage: \/repeat/);
    assert.match(send("/repeat 21 hi"), /^Usage: \/repeat/);
    assert.match(send("/repeat x hi"), /^Usage: \/repeat/);

    assert.match(send("hello"), /^Quack\. Try \/help\.$/);
    assert.match(send("/stats"), /messages seen: 1/);
    assert.match(send("/stats"), /updates handled: \d+/);

    // A short output buffer truncates rather than trapping.
    const short = bot.handle(1, "/help", 10);
    assert.equal(short.length, 10);

    console.log("telegram_duck_bot: all tests passed");
} finally {
    await rm(temporary, { recursive: true, force: true });
}
