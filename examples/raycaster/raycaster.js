const SCREEN_W = 160;
const SCREEN_H = 120;

// Shown until the player uploads their own map.
const DEFAULT_MAP = [
  "################",
  "#..............#",
  "#..............#",
  "#..............#",
  "#..............#",
  "#.....####.....#",
  "#.....#..#.....#",
  "#.....#..#.....#",
  "#.....####.....#",
  "#..............#",
  "#..............#",
  "#..............#",
  "#..............#",
  "#..............#",
  "#..............#",
  "################",
].join("\n");

const canvas = document.getElementById("screen");
const ctx = canvas.getContext("2d");
const statusEl = document.getElementById("status");
const fileInput = document.getElementById("mapfile");

const keys = new Set();
window.addEventListener("keydown", (e) => keys.add(e.keyCode));
window.addEventListener("keyup", (e) => keys.delete(e.keyCode));

const importObject = {
  host: {
    key_down: (code) => (keys.has(code) ? 1 : 0),
  },
};

const { instance } = await WebAssembly.instantiate(
  await (await fetch("main.wasm")).arrayBuffer(),
  importObject,
);
const { init, load_map, frame, framebuffer_ptr, map_ptr, memory } =
  instance.exports;

init();

function loadMapText(text) {
  const rows = text.split("\n").map((r) => r.replace(/\r$/, "")).filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  if (h === 0 || w === 0) {
    statusEl.textContent = "empty map, ignored";
    return;
  }
  if (w > 64 || h > 64) {
    statusEl.textContent = `map too large (${w}x${h}), max is 64x64`;
    return;
  }
  const buf = new Uint8Array(memory.buffer, map_ptr(), w * h);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const ch = rows[y][x];
      // Missing cells (short rows) and anything but '.' count as wall, so a
      // ragged upload can't accidentally open a hole in the boundary.
      buf[y * w + x] = ch === "." ? 0 : 1;
    }
  }
  load_map(w, h);
  statusEl.textContent = `loaded ${w}x${h} map`;
}

fileInput.addEventListener("change", async () => {
  const file = fileInput.files[0];
  if (!file) return;
  loadMapText(await file.text());
});

loadMapText(DEFAULT_MAP);

const fbPtr = framebuffer_ptr();
const imageData = ctx.createImageData(SCREEN_W, SCREEN_H);

let lastTime = performance.now();
function tick(now) {
  const dt = Math.min(now - lastTime, 100); // clamp to avoid huge jumps on tab-switch
  lastTime = now;

  frame(BigInt(Math.round(dt)));

  const view = new Uint8ClampedArray(
    memory.buffer,
    fbPtr,
    SCREEN_W * SCREEN_H * 4,
  );
  imageData.data.set(view);
  ctx.putImageData(imageData, 0, 0);

  requestAnimationFrame(tick);
}
requestAnimationFrame(tick);
