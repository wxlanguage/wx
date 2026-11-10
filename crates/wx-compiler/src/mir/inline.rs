//! Inlining over the arena MIR. Design: `notes/mir-inlining.md`.
//!
//! Build the call graph and per-function columns, order callees first through
//! strongly connected components, then splice accepted calls. MIR item IDs stay
//! stable; the optimizer's reachability worklist decides output retention later.
//! All temporary columns expire at the end of this pass.

use super::body::{self, ExprId, ExprKind, LabelId, shift_expr};
use super::{
	Code, FunctionFlags, FunctionId, Item, LocalIndex, MIR, ValueType,
};

/// Which calls the pass inlines beyond those it must.
#[derive(Clone, Copy)]
pub struct Policy {
	/// Whether the compiler chooses calls of its own: a callee no bigger than
	/// the call to it (with `slack`), and a callee with one call site that
	/// nothing outside the call graph refers to. Without it, only
	/// `#[inline]` callees are inlined.
	pub automatic: bool,
	/// How much bigger than a call a callee may be and still count as small,
	/// in [`ExprKind::cost`] units.
	pub slack: u32,
}

impl Policy {
	pub const DEFAULT: Self = Self {
		automatic: true,
		slack: 4,
	};
	/// `#[inline]` callees only.
	pub const ATTRIBUTE_ONLY: Self = Self {
		automatic: false,
		slack: 0,
	};
}

/// What calling a function costs at a call site: `call` and its index.
const CALL_COST: u32 = 2;

/// Inline what `policy` accepts, preserving every item and its MIR ID.
pub fn run(mir: &mut MIR, policy: Policy) {
	let graph = CallGraph::build(mir);
	let order = Components::of(&graph);
	let mut columns = Columns::build(mir, &graph);

	for &caller in &order.order {
		let Some(code) = mir.functions[usize::from(caller)].code() else {
			continue;
		};
		// Only the caller's own nodes: what a splice appends is a callee
		// already processed, so every call left in it is one the policy
		// refused, and the decision depends on the callee alone.
		let end = code.body.len() as u32;
		for id in 0..end {
			let call = ExprId::new(id);
			let code = mir.code(caller);
			let ExprKind::Call {
				function: callee, ..
			} = code.body.kind(call)
			else {
				continue;
			};
			if !columns.should_inline(mir, &order, policy, caller, callee) {
				continue;
			}
			let (caller_code, callee_code) =
				caller_and_callee(&mut mir.functions, caller, callee);
			splice(caller_code, call, callee_code, &mir.signatures);
		}
		let code = mir.code(caller);
		if cfg!(debug_assertions)
			&& let Err(error) = body::verify(
				&code.body,
				code.root,
				&code.locals,
				code.label_count,
			) {
			panic!("inlining broke the MIR arena's invariants: {error:?}");
		}
		columns.cost[usize::from(caller)] = code.body.cost();
	}
}

/// The functions each function calls, once per call node, in node order:
/// `callees[starts[f]..starts[f + 1]]` (a compressed sparse row).
struct CallGraph {
	starts: Vec<u32>,
	callees: Vec<FunctionId>,
}

impl CallGraph {
	fn build(mir: &MIR) -> Self {
		let mut starts = Vec::with_capacity(mir.functions.len() + 1);
		let mut callees = Vec::new();
		for function in &mir.functions {
			starts.push(callees.len() as u32);
			if let Some(code) = function.code() {
				callees.extend(code.callees());
			}
		}
		starts.push(callees.len() as u32);
		Self { starts, callees }
	}

	fn len(&self) -> usize {
		self.starts.len() - 1
	}

	fn callees(&self, function: usize) -> &[FunctionId] {
		&self.callees
			[self.starts[function] as usize..self.starts[function + 1] as usize]
	}
}

/// What the policy reads about each function, indexed by `FunctionId`.
struct Columns {
	/// The weighted size of the function's code: as lowered until the
	/// function is processed, after its own inlining from then on.
	cost: Vec<u32>,
	/// Call nodes naming the function across the program, as lowered. A
	/// call is decided before any copy of it exists (callees first), so the
	/// count is never stale where it is read.
	call_sites: Vec<u32>,
	/// Whether something outside the call graph refers to the function: an
	/// export or the start function.
	rooted: Vec<bool>,
}

impl Columns {
	fn build(mir: &MIR, graph: &CallGraph) -> Self {
		let cost = (mir.functions.iter())
			.map(|function| {
				function.code().map_or(CALL_COST, |code| code.body.cost())
			})
			.collect();
		let mut call_sites = vec![0; graph.len()];
		for &callee in &graph.callees {
			call_sites[usize::from(callee)] += 1;
		}
		Self {
			cost,
			call_sites,
			rooted: roots(mir),
		}
	}

	fn should_inline(
		&self,
		mir: &MIR,
		order: &Components,
		policy: Policy,
		caller: FunctionId,
		callee: FunctionId,
	) -> bool {
		let index = usize::from(callee);
		if mir.function(callee).code().is_none() {
			return false;
		}
		let component = order.component[index];
		if component == order.component[usize::from(caller)]
			&& order.recursive[component as usize]
		{
			return false;
		}
		if mir.flags(callee).contains(FunctionFlags::INLINE) {
			return true;
		}
		policy.automatic
			&& (self.cost[index] <= CALL_COST + policy.slack
				|| (self.call_sites[index] == 1 && !self.rooted[index]))
	}
}

/// The functions something outside the call graph refers to.
fn roots(mir: &MIR) -> Vec<bool> {
	let mut rooted = vec![false; mir.functions.len()];
	for export in &mir.exports {
		if let Item::Function(id) = export.item {
			rooted[usize::from(id)] = true;
		}
	}
	if let Some(start) = mir.start_function {
		rooted[usize::from(start)] = true;
	}
	rooted
}

/// The call graph's strongly connected components, by Tarjan's algorithm.
struct Components {
	/// Every function, callees first: a component comes after every
	/// component it calls into. Depends only on the program.
	order: Vec<FunctionId>,
	/// Each function's component.
	component: Vec<u32>,
	/// Per component: whether it is a cycle, several functions or one that
	/// calls itself.
	recursive: Vec<bool>,
}

impl Components {
	fn of(graph: &CallGraph) -> Self {
		let count = graph.len();
		let mut walk = Walk {
			index: vec![UNVISITED; count],
			low: vec![0; count],
			on_stack: vec![false; count],
			stack: Vec::new(),
			frames: Vec::new(),
			next_index: 0,
		};
		let mut this = Self {
			order: Vec::with_capacity(count),
			component: vec![0; count],
			recursive: Vec::new(),
		};
		for root in 0..count {
			if walk.index[root] != UNVISITED {
				continue;
			}
			walk.enter(root);
			while let Some(&mut (function, ref mut next)) =
				walk.frames.last_mut()
			{
				if let Some(&callee) = graph.callees(function).get(*next) {
					*next += 1;
					let callee = usize::from(callee);
					if walk.index[callee] == UNVISITED {
						walk.enter(callee);
					} else if walk.on_stack[callee] {
						walk.low[function] =
							walk.low[function].min(walk.index[callee]);
					}
					continue;
				}
				walk.frames.pop();
				if let Some(&(parent, _)) = walk.frames.last() {
					walk.low[parent] = walk.low[parent].min(walk.low[function]);
				}
				if walk.low[function] != walk.index[function] {
					continue;
				}
				// `function` is its component's root: the component is it and
				// everything above it on the stack.
				let component = this.recursive.len() as u32;
				let first = this.order.len();
				loop {
					let member = walk.stack.pop().unwrap();
					walk.on_stack[member] = false;
					this.component[member] = component;
					this.order.push(FunctionId::new(member as u32));
					if member == function {
						break;
					}
				}
				let recursive = this.order.len() - first > 1
					|| graph
						.callees(function)
						.contains(&FunctionId::new(function as u32));
				this.recursive.push(recursive);
			}
		}
		this
	}
}

const UNVISITED: u32 = u32::MAX;

/// Tarjan's walk. `frames` is the depth-first walk's own stack, so a deep
/// chain of calls cannot overflow the compiler's: a function and how many of
/// its callees it has entered.
struct Walk {
	index: Vec<u32>,
	low: Vec<u32>,
	on_stack: Vec<bool>,
	stack: Vec<usize>,
	frames: Vec<(usize, usize)>,
	next_index: u32,
}

impl Walk {
	fn enter(&mut self, function: usize) {
		self.index[function] = self.next_index;
		self.low[function] = self.next_index;
		self.next_index += 1;
		self.stack.push(function);
		self.on_stack[function] = true;
		self.frames.push((function, 0));
	}
}

/// The caller's code mutably and the callee's shared; they are different
/// functions, since a function calling itself is recursive.
fn caller_and_callee(
	functions: &mut [super::Function],
	caller: FunctionId,
	callee: FunctionId,
) -> (&mut Code, &Code) {
	let (caller, callee) = (usize::from(caller), usize::from(callee));
	debug_assert_ne!(caller, callee, "a recursive call is never inlined");
	let (caller, callee) = if caller < callee {
		let (left, right) = functions.split_at_mut(callee);
		(&mut left[caller], &right[0])
	} else {
		let (left, right) = functions.split_at_mut(caller);
		(&mut right[0], &left[callee])
	};
	(
		caller.code_mut().expect("a caller has code"),
		callee.code().expect("only a defined function is inlined"),
	)
}

/// Replace the call node `call` in `caller` with `callee`'s body.
///
/// The callee's locals and labels are appended to the caller's, its nodes
/// after the caller's with every index shifted, and each `Return` becomes a
/// `Break` to a fresh wrapper label. The call node becomes the wrapper
/// `Block`, keeping its type (the callee's result): first each argument
/// stored in the parameter locals it fills, one per scalar (a `LocalSet`,
/// a `SetLocals`, or the zero-sized argument alone), then the callee's root.
fn splice(
	caller: &mut Code,
	call: ExprId,
	callee: &Code,
	signatures: &super::Signatures,
) {
	let ExprKind::Call { args, .. } = caller.body.kind(call) else {
		unreachable!("only a call is spliced")
	};
	let locals = caller.locals.len() as u32;
	let labels = caller.label_count;
	let wrapper = LabelId::new(labels + callee.label_count);
	caller.locals.extend_from_slice(&callee.locals);
	caller.label_count += callee.label_count + 1;
	let offset = caller.body.append(&callee.body, locals, labels, |kind| {
		if let ExprKind::Return { value } = *kind {
			*kind = ExprKind::Break {
				label: wrapper,
				value,
			};
		}
	});
	let args = caller.body.list(args).to_vec();
	let mut statements = Vec::with_capacity(args.len() + 1);
	// Parameters are the callee's first locals, one per scalar of each
	// argument in turn.
	let mut param = locals;
	for value in args {
		let count = signatures.scalars(&caller.body.ty(value)).len() as u32;
		let statement = match count {
			0 => value,
			1 => caller.body.push(
				ExprKind::LocalSet {
					local: LocalIndex::new(param),
					value,
				},
				ValueType::Unit,
			),
			_ => {
				let targets = caller.body.push_targets(
					(param..param + count)
						.map(|local| Some(LocalIndex::new(local))),
				);
				caller.body.push(
					ExprKind::SetLocals { targets, value },
					ValueType::Unit,
				)
			}
		};
		statements.push(statement);
		param += count;
	}
	statements.push(shift_expr(callee.root, offset));
	let statements = caller.body.push_list(statements);
	caller.body.set_kind(
		call,
		ExprKind::Block {
			label: wrapper,
			statements,
		},
	);
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::symbols::{Keyword, StringInterner};
	use crate::testing::DiagnosticView;
	use crate::vfs;

	fn source_graph(
		source: &str,
		strings: &mut StringInterner,
	) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new(strings);
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)]),
				),
			)
			.unwrap();
		let graph = builder.build(root_id);
		DiagnosticView::new(
			"parse",
			&graph.collect_diagnostics(),
			&graph.files,
		)
		.assert_no_errors();
		graph
	}

	/// `source` checked, lowered and inlined under `policy`.
	fn inlined(source: &str, policy: Policy) -> (StringInterner, MIR) {
		let mut strings = Keyword::create_interner();
		let graph = source_graph(source, &mut strings);
		let (diagnostics, mir) = crate::tir::build(&graph, &mut strings);
		let Some(mut mir) = mir else {
			panic!(
				"the source must lower: {:?}",
				diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
			)
		};
		let function_count = mir.functions.len();
		let flags = mir.function_flags.clone();
		let imports: Vec<_> = mir.imports.iter().map(|i| i.item).collect();
		let exports: Vec<_> = mir.exports.iter().map(|e| e.item).collect();
		let start = mir.start_function;
		run(&mut mir, policy);
		assert_eq!(mir.functions.len(), function_count);
		assert!(mir.function_flags == flags);
		assert_eq!(
			mir.imports.iter().map(|i| i.item).collect::<Vec<_>>(),
			imports
		);
		assert_eq!(
			mir.exports.iter().map(|e| e.item).collect::<Vec<_>>(),
			exports
		);
		assert_eq!(mir.start_function, start);
		assert_dense(&mir);
		(strings, mir)
	}

	fn call_count(mir: &MIR) -> usize {
		(mir.functions.iter())
			.filter_map(|function| function.code())
			.map(|code| code.callees().count())
			.sum()
	}

	/// The export `name` of `mir`, encoded and run on `arg`.
	fn call<A, R>(strings: &StringInterner, mir: &MIR, name: &str, arg: A) -> R
	where
		A: wasmtime::WasmParams,
		R: wasmtime::WasmResults,
	{
		let bytes = crate::codegen::Builder::build_linearized(mir, strings)
			.expect("inlined MIR must encode")
			.encode();
		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, &bytes)
			.expect("inlined MIR must be valid Wasm");
		let mut store = wasmtime::Store::new(&engine, ());
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
		instance
			.get_typed_func::<A, R>(&mut store, name)
			.unwrap()
			.call(&mut store, arg)
			.unwrap()
	}

	/// Every id the program names is in range and every function's flags
	/// are beside it: a `FunctionId` is still its index.
	fn assert_dense(mir: &MIR) {
		assert_eq!(mir.function_flags.len(), mir.functions.len());
		for function in &mir.functions {
			if let Some(code) = function.code() {
				assert!(
					code.callees()
						.all(|id| usize::from(id) < mir.functions.len())
				);
			}
		}
		for export in &mir.exports {
			if let Item::Function(id) = export.item {
				assert!(usize::from(id) < mir.functions.len());
			}
		}
		mir.verify_imports().unwrap();
	}

	#[test]
	fn an_inline_callee_is_spliced_into_every_caller_with_stable_ids() {
		let source = r#"
			#[inline] func double(x: i32) -> i32 { x + x }
			func run(a: i32) -> i32 { double(a) + double(3) }
			export { run as "run" }
		"#;
		let (strings, mir) = inlined(source, Policy::ATTRIBUTE_ONLY);
		assert_eq!(mir.functions.len(), 2, "both MIR entries keep their IDs");
		assert_eq!(call_count(&mir), 0);
		assert_dense(&mir);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", 5), 16);
	}

	#[test]
	fn without_the_attribute_nothing_is_inlined_under_attribute_only() {
		let source = r#"
			func small(x: i32) -> i32 { x + 1 }
			func run(a: i32) -> i32 { small(a) + small(2) }
			export { run as "run" }
		"#;
		let (strings, mir) = inlined(source, Policy::ATTRIBUTE_ONLY);
		assert_eq!(mir.functions.len(), 2);
		assert_eq!(call_count(&mir), 2);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", 5), 9);
	}

	#[test]
	fn a_small_callee_is_inlined_and_a_large_one_with_two_callers_is_not() {
		let source = r#"
			func small(x: i32) -> i32 { x + 1 }
			func large(x: i32) -> i32 {
				(x * 3 + 7) * (x - 2) + (x * x - 5) * (x + 9) + (x - 1) * (x - 4)
			}
			func run(a: i32) -> i32 { small(a) + small(a + 1) + large(a) + large(2) }
			export { run as "run" }
		"#;
		let (strings, mir) = inlined(source, Policy::DEFAULT);
		assert_eq!(
			mir.functions.len(),
			3,
			"`run`, `large` and inlined `small`"
		);
		assert_eq!(call_count(&mir), 2, "both calls of `large`");
		assert_dense(&mir);
		let large = |x: i32| {
			(x * 3 + 7) * (x - 2) + (x * x - 5) * (x + 9) + (x - 1) * (x - 4)
		};
		assert_eq!(
			call::<i32, i32>(&strings, &mir, "run", 5),
			6 + 7 + large(5) + large(2)
		);
	}

	#[test]
	fn a_callee_with_one_call_site_is_inlined_unless_exported() {
		let large = r#"
			func large(x: i32) -> i32 {
				(x * 3 + 7) * (x - 2) + (x * x - 5) * (x + 9) + (x - 1) * (x - 4)
			}
		"#;
		let (strings, mir) = inlined(
			&format!(
				r#"{large} func run(a: i32) -> i32 {{ large(a) }} export {{ run as "run" }}"#
			),
			Policy::DEFAULT,
		);
		assert_eq!(mir.functions.len(), 2);
		assert_eq!(call_count(&mir), 0);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", 1), -10 + (-4) * 10);

		let (_, mir) = inlined(
			&format!(
				r#"{large} func run(a: i32) -> i32 {{ large(a) + 1 }}
				export {{ run as "run", large as "large" }}"#
			),
			Policy::DEFAULT,
		);
		assert_eq!(mir.functions.len(), 2, "an export is kept");
		assert_eq!(call_count(&mir), 1, "and it is not inlined for one caller");
	}

	#[test]
	fn a_recursive_function_stays_a_call_of_itself() {
		let source = r#"
			#[inline] func count(n: u32) -> u32 { if n == 0 { 0 } else { count(n - 1) + 1 } }
			func run(n: u32) -> u32 { count(n) }
			export { run as "run" }
		"#;
		let (strings, mir) = inlined(source, Policy::DEFAULT);
		// One level of `count` goes into `run`; its own call stays.
		assert_eq!(mir.functions.len(), 2);
		assert_eq!(call_count(&mir), 2);
		assert_dense(&mir);
		assert_eq!(call::<u32, u32>(&strings, &mir, "run", 5), 5);
	}

	#[test]
	fn mutually_recursive_functions_are_never_spliced_into_each_other() {
		let source = r#"
			func even(n: u32) -> u32 { if n == 0 { 1 } else { odd(n - 1) } }
			func odd(n: u32) -> u32 { if n == 0 { 0 } else { even(n - 1) } }
			export { even as "even" }
		"#;
		let (strings, mir) = inlined(source, Policy::DEFAULT);
		assert_eq!(mir.functions.len(), 2);
		assert_eq!(call_count(&mir), 2);
		assert_eq!(call::<u32, u32>(&strings, &mir, "even", 6), 1);
		assert_eq!(call::<u32, u32>(&strings, &mir, "even", 7), 0);
	}

	#[test]
	fn an_inlined_early_return_leaves_the_callers_wrapper() {
		let source = r#"
			#[inline] func clamp(x: i32) -> i32 { if x < 0 { return 0; } x }
			func run(a: i32) -> i32 { clamp(a) + clamp(a - 10) }
			export { run as "run" }
		"#;
		let (strings, mir) = inlined(source, Policy::ATTRIBUTE_ONLY);
		assert_eq!(mir.functions.len(), 2);
		assert!(
			!(mir.code(FunctionId::new(0)).body.kinds().iter())
				.any(|kind| matches!(kind, ExprKind::Return { .. })),
			"a callee's `return` leaves its wrapper, not the caller"
		);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", 5), 5);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", 20), 30);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", -3), 0);
	}

	#[test]
	fn two_copies_of_a_loop_get_their_own_labels_and_locals() {
		let source = r#"
			#[inline] func sum_to(n: i32) -> i32 {
				local mut i: i32 = 0;
				local mut acc: i32 = 0;
				loop {
					if i == n { break acc; }
					i = i + 1;
					acc = acc + i;
				}
			}
			func run(a: i32) -> i32 { sum_to(a) + sum_to(3) }
			export { run as "run" }
		"#;
		let (strings, mir) = inlined(source, Policy::ATTRIBUTE_ONLY);
		assert_eq!(mir.functions.len(), 2);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", 4), 16);
	}

	#[test]
	fn inlining_preserves_calls_and_import_ids() {
		let source = r#"
			import "host" as host { func log(value: i32); }
			func helper(x: i32) { host::log(x); host::log(x + 1); }
			func run(a: i32) { helper(a) }
			export { run as "run" }
		"#;
		let (_, mir) = inlined(source, Policy::DEFAULT);
		// `run` 0, `helper` 1, `log` 2 stay at their original IDs.
		assert_eq!(mir.functions.len(), 3);
		assert_dense(&mir);
		let [import] = mir.imports.as_slice() else {
			panic!("one import entry")
		};
		let Item::Function(log) = import.item else {
			panic!("a function import")
		};
		assert_eq!(log, FunctionId::new(2));
		assert!(mir.code(FunctionId::new(0)).callees().all(|id| id == log));
		assert_eq!(mir.code(FunctionId::new(0)).callees().count(), 2);
		assert_eq!(call_count(&mir), 4, "original helper remains in MIR");
	}

	#[test]
	fn the_same_program_is_inlined_the_same_way_every_time() {
		let source = r#"
			#[inline] func a(x: u32) -> u32 { b(x) + c(x) }
			func b(x: u32) -> u32 { c(x) * 2 }
			func c(x: u32) -> u32 { x + 1 }
			func d(x: u32) -> u32 { if x == 0 { 0 } else { e(x - 1) } }
			func e(x: u32) -> u32 { if x == 0 { 1 } else { d(x - 1) } }
			func run(x: u32) -> u32 { a(x) + d(x) + a(x + 1) }
			export { run as "run", d as "d" }
		"#;
		let render = |mir: &MIR| {
			(mir.functions.iter())
				.map(|function| match function.code() {
					Some(code) => {
						format!("{:?} {:?}", code.root, code.body.kinds())
					}
					None => "import".to_string(),
				})
				.collect::<Vec<_>>()
		};
		let first = render(&inlined(source, Policy::DEFAULT).1);
		for _ in 0..8 {
			assert_eq!(render(&inlined(source, Policy::DEFAULT).1), first);
		}
	}

	/// `mir`'s function exported as `name`.
	fn exported(strings: &StringInterner, mir: &MIR, name: &str) -> FunctionId {
		mir.exports
			.iter()
			.find_map(|export| match export.item {
				Item::Function(id)
					if strings.resolve(export.name) == Some(name) =>
				{
					Some(id)
				}
				_ => None,
			})
			.expect("an exported function")
	}

	#[test]
	fn an_inline_chain_grows_by_each_callee_after_its_own_inlining() {
		// Exported, so every level is kept and can be measured; an export is
		// still inlined into its callers.
		let source = r#"
			#[inline] func a(x: i32) -> i32 { b(x) * b(x + 1) }
			#[inline] func b(x: i32) -> i32 { c(x) * c(x + 2) }
			#[inline] func c(x: i32) -> i32 { x * 3 }
			export { a as "a", b as "b", c as "c" }
		"#;
		let mut strings = Keyword::create_interner();
		let graph = source_graph(source, &mut strings);
		let lowered = crate::tir::build(&graph, &mut strings)
			.1
			.expect("the source lowers");
		let (strings, mir) = inlined(source, Policy::ATTRIBUTE_ONLY);
		assert_eq!(call_count(&mir), 0);
		let len = |mir: &MIR, name| {
			mir.code(exported(&strings, mir, name)).body.len()
		};
		// A splice appends the callee's nodes and one `LocalSet` per
		// argument, and reuses the call node as the wrapper.
		let c = len(&mir, "c");
		assert_eq!(c, len(&lowered, "c"));
		let b = len(&mir, "b");
		assert_eq!(b, len(&lowered, "b") + 2 * (c + 1));
		assert_eq!(len(&mir, "a"), len(&lowered, "a") + 2 * (b + 1));
		let c = |x: i32| x * 3;
		let b = |x: i32| c(x) * c(x + 2);
		assert_eq!(call::<i32, i32>(&strings, &mir, "a", 2), b(2) * b(3));
	}

	#[test]
	fn an_unattributed_chain_stops_growing_once_a_level_is_no_longer_small() {
		let source = r#"
			func a(x: i32) -> i32 { b(x) * b(x + 1) }
			func b(x: i32) -> i32 { c(x) * c(x + 2) }
			func c(x: i32) -> i32 { x * 3 }
			func run(x: i32) -> i32 { a(x) + a(x + 5) }
			export { run as "run" }
		"#;
		let (strings, mir) = inlined(source, Policy::DEFAULT);
		// `c` is small and goes into `b`; `b`, with two copies of it, is no
		// longer small, and neither is `a`, so both stay calls.
		assert_eq!(mir.functions.len(), 4, "`run`, `a`, `b` and inlined `c`");
		assert_eq!(call_count(&mir), 4);
		assert_dense(&mir);
		let c = |x: i32| x * 3;
		let b = |x: i32| c(x) * c(x + 2);
		let a = |x: i32| b(x) * b(x + 1);
		assert_eq!(call::<i32, i32>(&strings, &mir, "run", 1), a(1) + a(6));
	}
}
