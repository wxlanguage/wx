// Run against a wasm-bindgen --target nodejs package, including release builds:
// node crates/wx-compiler-wasm/tests/compile.mjs /tmp/wx-compiler-node
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { resolve } from 'node:path';
import { readFileSync, readdirSync } from 'node:fs';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { test } from 'node:test';

const require = createRequire(import.meta.url);
const packagePath = resolve(process.argv[2]);
const bindingsPath = resolve(packagePath, 'wx_compiler_wasm.js');
const bindings = process.argv[3] === '--web'
    ? await import(pathToFileURL(bindingsPath))
    : require(bindingsPath);
if (process.argv[3] === '--web') {
    await bindings.default({
        module_or_path: readFileSync(resolve(packagePath, 'wx_compiler_wasm_bg.wasm')),
    });
}
const { compile, compile_package } = bindings;

function run(result, name, ...args) {
    assert.ok(result.bytecode instanceof Uint8Array, JSON.stringify(result.diagnostics));
    const module = new WebAssembly.Module(result.bytecode);
    return new WebAssembly.Instance(module).exports[name](...args);
}

function errors(result) {
    assert.equal(result.bytecode, null);
    assert.ok(result.diagnostics.some(d => d.severity === 'Error' || d.severity === 'Bug'));
    for (const d of result.diagnostics) {
        assert.ok(Array.isArray(d.labels));
        for (const label of d.labels) {
            assert.equal(typeof label.file_id, 'number');
            assert.equal(typeof label.range.start, 'number');
            assert.equal(typeof label.range.end, 'number');
        }
    }
}

test('entry compilation runs core operators, generics, modules, and inlining', () => {
    const result = compile('src/./main.wx', {
        '/src/main.wx': `
            mod math;
            #[inline] func identity<T: core::StackValue>(x: T) -> T { x }
            func answer() -> i32 { identity(math::double(21)) }
            export { answer }
        `,
        'src/math.wx': 'pub func double(x: i32) -> i32 { x + x }',
    });
    assert.equal(run(result, 'answer'), 42);
});

test('warnings survive successful compilation', () => {
    const result = compile('main.wx', {
        'main.wx': '#[unknown]\nfunc answer() -> i32 { 42 } export { answer }',
    });
    assert.equal(run(result, 'answer', 0), 42);
    assert.ok(result.diagnostics.some(d => d.code === 'W2011'));
});

test('parse, module-loading, and type errors return diagnostics and null bytes', () => {
    errors(compile('main.wx', { 'main.wx': 'func broken(' }));
    errors(compile('main.wx', { 'main.wx': 'mod missing;' }));
    errors(compile('main.wx', {
        'main.wx': 'func answer() -> i32 { true } export { answer }',
    }));
});

test('invalid input throws, without trapping the compiler instance', () => {
    assert.throws(() => compile('missing.wx', {}));
    assert.throws(() => compile('main.wx', { 'main.wx': 12 }));
    assert.throws(() => compile('main.wx', { 'main.wx': '', '/main.wx': '' }));
    assert.throws(() => compile_package('/', {}));
    assert.throws(() => compile_package('/', { 'wx.json': '{' }));
    assert.equal(run(compile('/main.wx', {
        'main.wx': 'func answer() -> i32 { 42 } export { answer }',
    }), 'answer'), 42);
});

test('package compilation resolves manifests and local dependencies', () => {
    const result = compile_package('app', {
        'app/wx.json': JSON.stringify({
            entry: 'main.wx',
            dependencies: { math: { type: 'local', path: '../math' } },
        }),
        'app/main.wx': `
            package "math" as math;
            func answer() -> i32 { math::double(21) }
            export { answer }
        `,
        'math/wx.json': '{ "entry": "main.wx" }',
        'math/main.wx': 'pub func double(x: i32) -> i32 { x + x }',
    });
    assert.equal(run(result, 'answer'), 42);
});


test('repository examples compile through the Wasm package API', () => {
    const root = fileURLToPath(new URL('../../../examples/', import.meta.url));
    const files = {};
    function collect(dir) {
        for (const entry of readdirSync(resolve(root, dir), { withFileTypes: true })) {
            const path = `${dir}/${entry.name}`;
            if (entry.isDirectory()) collect(path);
            else if (entry.name.endsWith('.wx') || entry.name === 'wx.json') {
                files[path] = readFileSync(resolve(root, path), 'utf8');
            }
        }
    }
    // Collect dependencies as well as roots, exactly as a browser VFS would.
    for (const dir of ['factorial', 'wasi_hello_world', 'alloc']) collect(dir);
    assert.equal(run(compile_package('factorial', files), 'factorial', 5), 120);
    const wasi = compile_package('wasi_hello_world', files);
    assert.ok(wasi.bytecode instanceof Uint8Array, JSON.stringify(wasi.diagnostics));
    assert.ok(WebAssembly.validate(wasi.bytecode));
});
