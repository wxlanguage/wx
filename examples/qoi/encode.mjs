// Independent JavaScript encoder used by the demo and differential tests.
// The decoder is entirely WX; this file never decodes pixels.
export function encodeQoi(width, height, pixels, channels = 4, colorspace = 0) {
    if (!width || !height || pixels.length !== width * height * 4) {
        throw new Error("Expected width × height RGBA pixels");
    }
    const bytes = [0x71, 0x6f, 0x69, 0x66];
    for (const value of [width, height]) {
        bytes.push(value >>> 24, (value >>> 16) & 255, (value >>> 8) & 255, value & 255);
    }
    bytes.push(channels, colorspace);
    const table = new Uint32Array(64);
    const operations = new Set();
    const emit = (name, ...data) => { operations.add(name); bytes.push(...data); };
    const delta = (a, b) => ((a - b + 128) & 255) - 128;
    let pr = 0, pg = 0, pb = 0, pa = 255, run = 0;
    for (let i = 0; i < pixels.length; i += 4) {
        const [r, g, b, a] = pixels.subarray(i, i + 4);
        if (r === pr && g === pg && b === pb && a === pa) {
            if (++run === 62 || i + 4 === pixels.length) {
                emit("RUN", 0xc0 | (run - 1));
                run = 0;
            }
            continue;
        }
        if (run) { emit("RUN", 0xc0 | (run - 1)); run = 0; }
        const pixel = (r | g << 8 | b << 16 | a << 24) >>> 0;
        const hash = (r * 3 + g * 5 + b * 7 + a * 11) & 63;
        if (table[hash] === pixel) {
            emit("INDEX", hash);
        } else {
            table[hash] = pixel;
            const dr = delta(r, pr), dg = delta(g, pg), db = delta(b, pb);
            const drg = dr - dg, dbg = db - dg;
            if (a !== pa) {
                emit("RGBA", 0xff, r, g, b, a);
            } else if ([dr, dg, db].every(d => d >= -2 && d <= 1)) {
                emit("DIFF", 0x40 | (dr + 2) << 4 | (dg + 2) << 2 | (db + 2));
            } else if (dg >= -32 && dg <= 31 && drg >= -8 && drg <= 7 && dbg >= -8 && dbg <= 7) {
                emit("LUMA", 0x80 | (dg + 32), (drg + 8) << 4 | (dbg + 8));
            } else {
                emit("RGB", 0xfe, r, g, b);
            }
        }
        [pr, pg, pb, pa] = [r, g, b, a];
    }
    bytes.push(0, 0, 0, 0, 0, 0, 0, 1);
    return { bytes: Uint8Array.from(bytes), operations };
}

export function demoPixels(width = 384, height = 256) {
    const pixels = new Uint8Array(width * height * 4);
    for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
            const i = (y * width + x) * 4;
            const wave = Math.sin(x / 22 + Math.sin(y / 31) * 3);
            const ring = Math.sin(Math.hypot(x - width / 2, y - height / 2) / 9);
            pixels.set([
                Math.round(127 + 127 * wave),
                Math.round(127 + 127 * ring),
                Math.round(127 + 127 * Math.sin(y / 24 + wave * 2)),
                255,
            ], i);
        }
    }
    return pixels;
}
