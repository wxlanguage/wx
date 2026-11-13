async function test(bytecode) {
	const module = await WebAssembly.compile(bytecode);
	let memory;
	const instance = await WebAssembly.instantiate(module, {
		console: {
			log: (ptr, len) =>
				console.log(new TextDecoder().decode(new Uint8Array(memory.buffer, ptr, len))),
		},
	});
	memory = instance.exports.memory;
	const { fibonacci_iterative } = instance.exports;

	return fibonacci_iterative(24);
}

return test;
