// Differential tests for the WX SHA-256 / HMAC / PBKDF2 package.
//
//   node examples/sha256/test.mjs
//
// Every expected value comes from Node's independent implementation, so the
// tests do not compare WX against itself. Set WX to choose the compiler.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash, createHmac, pbkdf2Sync, randomBytes } from "node:crypto";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../../", import.meta.url));
const temporary = await mkdtemp(join(process.env.TMPDIR || tmpdir(), "wx-sha256-"));
try {
    const output = join(temporary, "sha256.wasm");
    const built = spawnSync(process.env.WX || "wx",
        ["build", join(root, "examples/sha256"), "-o", output],
        { cwd: root, encoding: "utf8", timeout: 60000 });
    if (built.error) throw built.error;
    assert.equal(built.status, 0, built.stdout + built.stderr);

    const module = await WebAssembly.compile(await readFile(output));
    assert.deepEqual(WebAssembly.Module.imports(module), []);
    assert.deepEqual(
        WebAssembly.Module.exports(module).map(({ name, kind }) => `${name}:${kind}`).sort(),
        [
            "bytes_eq:function",
            "hash:function",
            "hash_cross:function",
            "hash_wide:function",
            "hmac:function",
            "memory:memory",
            "pbkdf2:function",
            "wide_memory:memory",
        ],
    );

    const { exports: wx } = await WebAssembly.instantiate(module, {});

    // The host facade pins every memory to `heap`; the test keeps its buffers
    // in known regions and grows the memory only as far as a case needs.
    const OUT = 1024;
    const KEY = 2048;
    const SALT = 8192;
    const INPUT = 65536;
    const bytes = () => new Uint8Array(wx.memory.buffer);

    function ensure(end) {
        const pages = Math.ceil(end / 65536);
        const have = wx.memory.buffer.byteLength / 65536;
        if (pages > have) wx.memory.grow(pages - have);
    }

    function write(buffer, at) {
        ensure(at + buffer.length);
        bytes().set(buffer, at);
    }

    function read(at, length) {
        return Buffer.from(new Uint8Array(wx.memory.buffer, at, length));
    }

    let shaCases = 0;
    function sha256(input) {
        write(input, INPUT);
        // Sentinels on both sides of the output catch a write past 32 bytes.
        bytes().fill(0x5a, OUT, OUT + 48);
        ensure(INPUT + input.length);
        wx.hash(INPUT, input.length, OUT);
        assert.equal(bytes()[OUT + 32], 0x5a);
        assert.equal(bytes()[OUT + 47], 0x5a);
        shaCases++;
        return read(OUT, 32).toString("hex");
    }

    // Published NIST FIPS 180-4 vectors and block-boundary sizes.
    for (const [input, expected] of [
        ["", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"],
        ["abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"],
        [
            "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ],
        [
            "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
            "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
        ],
    ]) {
        assert.equal(sha256(Buffer.from(input)), expected, `NIST vector ${input.length}`);
    }
    const million = Buffer.alloc(1_000_000, "a");
    assert.equal(sha256(million),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");

    for (let length = 0; length <= 260; length++) {
        const input = Buffer.alloc(length);
        for (let i = 0; i < length; i++) input[i] = (i * 37 + length) & 255;
        assert.equal(sha256(input), createHash("sha256").update(input).digest("hex"), `length ${length}`);
    }
    for (const length of [511, 512, 513, 1000, 4096, 65535, 65536, 65537, 200_000]) {
        const input = randomBytes(length);
        assert.equal(sha256(input), createHash("sha256").update(input).digest("hex"), `length ${length}`);
    }
    // The input must stay untouched.
    const probe = randomBytes(300);
    write(probe, INPUT);
    const before = read(INPUT, probe.length);
    wx.hash(INPUT, probe.length, OUT);
    assert.deepEqual(read(INPUT, probe.length), before);

    // The same generic hasher over a 64-bit-address memory, and from that
    // memory into the 32-bit one. Node's WebAssembly runtime supports
    // multi-memory and memory64, so this is a real end-to-end check.
    function grow(memory, end, wide = false) {
        const pages = Math.ceil(end / 65536);
        const have = memory.buffer.byteLength / 65536;
        if (pages > have) {
            const delta = pages - have;
            memory.grow(wide ? BigInt(delta) : delta);
        }
    }
    function hashWide(input) {
        grow(wx.wide_memory, 4096 + input.length, true);
        new Uint8Array(wx.wide_memory.buffer).set(input, 4096);
        wx.hash_wide(4096n, BigInt(input.length), 64n);
        return Buffer.from(new Uint8Array(wx.wide_memory.buffer, 64, 32)).toString("hex");
    }
    function hashCross(input) {
        grow(wx.wide_memory, 4096 + input.length, true);
        new Uint8Array(wx.wide_memory.buffer).set(input, 4096);
        bytes().fill(0x5a, OUT, OUT + 40);
        wx.hash_cross(4096n, BigInt(input.length), OUT);
        assert.equal(bytes()[OUT + 32], 0x5a);
        return read(OUT, 32).toString("hex");
    }
    for (const length of [0, 1, 3, 55, 56, 63, 64, 65, 1000, 65536, 1_000_000]) {
        const input = randomBytes(length);
        const expected = createHash("sha256").update(input).digest("hex");
        assert.equal(hashWide(input), expected, `wide memory, ${length} bytes`);
        assert.equal(hashCross(input), expected, `wide to heap, ${length} bytes`);
    }

    function hmac(key, message) {
        write(key, KEY);
        write(message, INPUT);
        ensure(OUT + 64);
        bytes().fill(0x5a, OUT, OUT + 48);
        wx.hmac(KEY, key.length, INPUT, message.length, OUT);
        assert.equal(bytes()[OUT + 32], 0x5a);
        return read(OUT, 32).toString("hex");
    }

    // RFC 4231 test cases, including keys longer than the 64-byte block.
    const rfc4231 = [
        [Buffer.alloc(20, 0x0b), Buffer.from("Hi There")],
        [Buffer.from("Jefe"), Buffer.from("what do ya want for nothing?")],
        [Buffer.alloc(20, 0xaa), Buffer.alloc(50, 0xdd)],
        [Buffer.from("key"), Buffer.from("The quick brown fox jumps over the lazy dog")],
        [Buffer.alloc(131, 0xaa), Buffer.from("Test Using Larger Than Block-Size Key - Hash Key First")],
        [Buffer.alloc(131, 0xaa), Buffer.from("This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.")],
    ];
    for (const [key, message] of rfc4231) {
        assert.equal(hmac(key, message),
            createHmac("sha256", key).update(message).digest("hex"));
    }
    for (let keyLength = 0; keyLength <= 140; keyLength += 7) {
        for (const messageLength of [0, 1, 55, 56, 63, 64, 65, 127, 128, 1000]) {
            const key = randomBytes(keyLength);
            const message = randomBytes(messageLength);
            assert.equal(hmac(key, message),
                createHmac("sha256", key).update(message).digest("hex"),
                `hmac key ${keyLength}, message ${messageLength}`);
        }
    }

    function pbkdf2(password, salt, iterations, length) {
        write(password, KEY);
        write(salt, SALT);
        ensure(OUT + length + 8);
        bytes().fill(0x5a, OUT + length, OUT + length + 8);
        wx.pbkdf2(KEY, password.length, SALT, salt.length, iterations, OUT, length);
        assert.equal(bytes()[OUT + length], 0x5a);
        return read(OUT, length).toString("hex");
    }

    // RFC 7914's PBKDF2-HMAC-SHA-256 vectors, then differential coverage.
    assert.equal(
        pbkdf2(Buffer.from("passwd"), Buffer.from("salt"), 1, 64),
        "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc" +
        "49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783",
    );
    assert.equal(
        pbkdf2(Buffer.from("Password"), Buffer.from("NaCl"), 80000, 64),
        "4ddcd8f60b98be21830cee5ef22701f9641a4418d04c0414aeff08876b34ab56" +
        "a1d425a1225833549adb841b51c9b3176a272bdebba1d078478f62b397f33c8d",
    );
    for (const iterations of [1, 2, 3, 10, 100, 1000]) {
        for (const length of [1, 16, 31, 32, 33, 64, 100]) {
            const password = randomBytes(1 + (iterations % 37));
            const salt = randomBytes(1 + (length % 29));
            assert.equal(pbkdf2(password, salt, iterations, length),
                pbkdf2Sync(password, salt, iterations, length, "sha256").toString("hex"),
                `pbkdf2 ${iterations} iterations, ${length} bytes`);
        }
    }

    function equal(a, b) {
        write(a, KEY);
        write(b, SALT);
        return wx.bytes_eq(KEY, a.length, SALT, b.length);
    }
    assert.equal(equal(Buffer.alloc(0), Buffer.alloc(0)), 1);
    assert.equal(equal(Buffer.from("same"), Buffer.from("same")), 1);
    assert.equal(equal(Buffer.from("same"), Buffer.from("samf")), 0);
    assert.equal(equal(Buffer.from("same"), Buffer.from("same!")), 0);
    for (let i = 0; i < 64; i++) {
        const a = randomBytes(64);
        const b = Buffer.from(a);
        assert.equal(equal(a, b), 1, `equal at ${i}`);
        b[i] ^= 0x80;
        assert.equal(equal(a, b), 0, `differs at ${i}`);
    }

    // The browser page's glue code is DOM-free, so exercise it here too:
    // memory growth, the pinned facade and text encoding.
    const { createHasher } = await import("./app.mjs");
    const app = await createHasher(await readFile(output));
    assert.equal(app.text("abc").length, 3);
    assert.equal(app.hash(app.text("abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    assert.equal(app.hmac(app.text("key"), app.text("The quick brown fox jumps over the lazy dog")),
        "f7bc83f430538424b13298e6aa6fb143ef4d59a14946175997479dbc2d1a3cd8");
    const large = randomBytes(300_000);
    assert.equal(app.hash(large), createHash("sha256").update(large).digest("hex"));

    console.log(`PASS SHA-256: ${shaCases} cases, NIST vectors, block boundaries, 1 MB message, 200k random bytes`);
    console.log("PASS 64-bit memory: 11 sizes over a u64-address memory and a cross-memory source");
    console.log("PASS HMAC-SHA-256: RFC 4231 vectors, long keys, 140 key sizes, block-boundary messages");
    console.log("PASS PBKDF2-HMAC-SHA-256: RFC 7914 vectors and 42 differential cases");
    console.log("PASS constant-time equality: every byte position and mismatched lengths");
    console.log("PASS browser glue: text encoding, digest, HMAC and memory growth");
    console.log(`Module: ${(await readFile(output)).length} Wasm bytes; scratch memory is private, no imports`);
} finally {
    await rm(temporary, { recursive: true, force: true });
}
