use std::collections::{HashMap, HashSet, VecDeque};

use crate::ast;
use crate::mir::*;
use crate::tir;

/// Holds the two fixed parameters of a scope-rebase pass so the recursive
/// walk doesn't need to thread them through every call.
struct Rebaser {
	scope_offset: ScopeIndex,
	wrapper_scope: ScopeIndex,
}

impl Rebaser {
	/// Offsets every scope index in `expr` by `scope_offset` in place, and
	/// rewrites `Return { value }` into `Break { scope_index: wrapper_scope,
	/// value }`. Never reallocates — only the handful of fields that
	/// actually change are touched.
	fn rebase(&self, expr: &mut Expression) {
		match &mut expr.kind {
			// Scope-indexed leaves — just offset the index.
			ExprKind::LocalGet { scope_index, .. }
			| ExprKind::AggregateGet { scope_index, .. }
			| ExprKind::Continue { scope_index } => {
				*scope_index += self.scope_offset;
			}
			// Scope-indexed variants with a child to recurse into.
			ExprKind::LocalSet {
				scope_index, value, ..
			}
			| ExprKind::AggregateSet {
				scope_index, value, ..
			}
			| ExprKind::Loop {
				scope_index,
				block: value,
			} => {
				*scope_index += self.scope_offset;
				self.rebase(value);
			}
			ExprKind::Block {
				scope_index,
				expressions,
			} => {
				*scope_index += self.scope_offset;
				for e in expressions.iter_mut() {
					self.rebase(e);
				}
			}
			ExprKind::Break { scope_index, value } => {
				*scope_index += self.scope_offset;
				if let Some(v) = value {
					self.rebase(v);
				}
			}
			ExprKind::Return { value } => {
				if let Some(v) = value {
					self.rebase(v);
				}
				// Convert in place: re-tagging the variant needs its own
				// fresh `&mut expr.kind` borrow via `mem::replace`, which is
				// why this happens after `value`'s last use above rather
				// than as part of the match's own destructuring.
				let value =
					match std::mem::replace(&mut expr.kind, ExprKind::Noop) {
						ExprKind::Return { value } => value,
						_ => unreachable!(),
					};
				expr.kind = ExprKind::Break {
					scope_index: self.wrapper_scope,
					value,
				};
			}
			// Non-scope variants with a single child — recurse only.
			ExprKind::Drop { value }
			| ExprKind::GlobalSet { value, .. }
			| ExprKind::Neg { value }
			| ExprKind::Sqrt { value }
			| ExprKind::Abs { value }
			| ExprKind::Floor { value }
			| ExprKind::Ceil { value }
			| ExprKind::BitNot { value }
			| ExprKind::Eqz { value }
			| ExprKind::I64ExtendI32S { value }
			| ExprKind::I64ExtendI32U { value }
			| ExprKind::I32WrapI64 { value }
			| ExprKind::F32ConvertI32 { value }
			| ExprKind::F32ConvertU32 { value }
			| ExprKind::F32ConvertI64 { value }
			| ExprKind::F32ConvertU64 { value }
			| ExprKind::F64ConvertI32 { value }
			| ExprKind::F64ConvertU32 { value }
			| ExprKind::F64ConvertI64 { value }
			| ExprKind::F64ConvertU64 { value }
			| ExprKind::I32TruncF32 { value }
			| ExprKind::U32TruncF32 { value }
			| ExprKind::I32TruncF64 { value }
			| ExprKind::U32TruncF64 { value }
			| ExprKind::I64TruncF32 { value }
			| ExprKind::U64TruncF32 { value }
			| ExprKind::I64TruncF64 { value }
			| ExprKind::U64TruncF64 { value }
			| ExprKind::F64PromoteF32 { value }
			| ExprKind::F32DemoteF64 { value }
			| ExprKind::PointerLoad { pointer: value, .. }
			| ExprKind::MemoryGrow { delta: value, .. } => self.rebase(value),
			// Non-scope variants with two children.
			ExprKind::Add { left, right }
			| ExprKind::Sub { left, right }
			| ExprKind::Mul { left, right }
			| ExprKind::Div { left, right }
			| ExprKind::Rem { left, right }
			| ExprKind::And { left, right }
			| ExprKind::Or { left, right }
			| ExprKind::Eq { left, right }
			| ExprKind::NotEq { left, right }
			| ExprKind::Less { left, right }
			| ExprKind::LessEq { left, right }
			| ExprKind::Greater { left, right }
			| ExprKind::GreaterEq { left, right }
			| ExprKind::BitAnd { left, right }
			| ExprKind::BitOr { left, right }
			| ExprKind::BitXor { left, right }
			| ExprKind::LeftShift { left, right }
			| ExprKind::RightShift { left, right }
			| ExprKind::PointerStore {
				pointer: left,
				value: right,
				..
			} => {
				self.rebase(left);
				self.rebase(right);
			}
			ExprKind::MemoryFill { dst, val, len, .. } => {
				self.rebase(dst);
				self.rebase(val);
				self.rebase(len);
			}
			ExprKind::MemoryCopy { dst, src, len, .. } => {
				self.rebase(dst);
				self.rebase(src);
				self.rebase(len);
			}
			ExprKind::Aggregate { values } => {
				for e in values.iter_mut() {
					self.rebase(e);
				}
			}
			ExprKind::Call { callee, arguments } => {
				self.rebase(callee);
				for a in arguments.iter_mut() {
					self.rebase(a);
				}
			}
			ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				self.rebase(condition);
				self.rebase(then_block);
				if let Some(e) = else_block {
					self.rebase(e);
				}
			}
			ExprKind::Switch {
				selector,
				cases,
				default,
			} => {
				self.rebase(selector);
				for (_, body) in cases.iter_mut() {
					self.rebase(body);
				}
				if let Some(d) = default {
					self.rebase(d);
				}
			}
			// Leaf variants — nothing to rebase.
			ExprKind::Noop
			| ExprKind::Bool { .. }
			| ExprKind::Function { .. }
			| ExprKind::Int { .. }
			| ExprKind::Float { .. }
			| ExprKind::Global { .. }
			| ExprKind::Unreachable
			| ExprKind::MemoryOffset { .. }
			| ExprKind::MemoryIndex { .. }
			| ExprKind::MemorySize { .. }
			| ExprKind::StaticPointer { .. } => {}
		}
	}
}

/// Offsets every scope index in `expr` by `scope_offset` (in place), and
/// rewrites `Return { value }` into `Break { scope_index: wrapper_scope,
/// value }`.
pub(super) fn rebase_scope(
	expr: &mut Expression,
	scope_offset: ScopeIndex,
	wrapper_scope: ScopeIndex,
) {
	Rebaser {
		scope_offset,
		wrapper_scope,
	}
	.rebase(expr);
}

/// Substitutes a direct call at the call site with the callee's body inlined
/// into the caller. Appends the required scopes to `caller_scopes`.
fn inline_call(
	callee: &Function,
	arguments: Box<[Expression]>,
	caller_scopes: &mut Vec<BlockScope>,
	call_site_scope: ScopeIndex,
) -> Expression {
	let result_ty = callee.block.ty;

	// The wrapper scope is the break-target for all rewritten `Return` nodes.
	let wrapper_scope = caller_scopes.len() as ScopeIndex;
	caller_scopes.push(BlockScope {
		kind: tir::BlockKind::Block,
		parent: Some(call_site_scope),
		locals: vec![],
		result: result_ty,
	});

	// Callee's scopes follow the wrapper.  Offset their parent pointers.
	let body_scope_offset = caller_scopes.len() as ScopeIndex;
	for scope in callee.scopes.iter().cloned() {
		caller_scopes.push(BlockScope {
			parent: scope
				.parent
				.map(|p| p + body_scope_offset)
				.or(Some(wrapper_scope)),
			..scope
		});
	}

	// Store each argument into the corresponding param local in the callee's
	// root scope (now living at body_scope_offset).
	let mut exprs: Vec<Expression> = arguments
		.into_vec()
		.into_iter()
		.enumerate()
		.map(|(i, arg)| Expression {
			ty: Type::Unit,
			kind: ExprKind::LocalSet {
				scope_index: body_scope_offset,
				local_index: i as LocalIndex,
				value: Box::new(arg),
			},
		})
		.collect();

	let mut body = callee.block.clone();
	rebase_scope(&mut body, body_scope_offset, wrapper_scope);
	exprs.push(body);

	Expression {
		ty: result_ty,
		kind: ExprKind::Block {
			scope_index: wrapper_scope,
			expressions: exprs.into_boxed_slice(),
		},
	}
}

/// Walks `expr` in-place (post-order) and replaces every direct call to
/// `inline_id` with `inline_body` inlined at the call site.
fn inline_expr(
	expr: &mut Expression,
	caller_scopes: &mut Vec<BlockScope>,
	inline_id: ast::DefId,
	inline_body: &Function,
	current_scope: ScopeIndex,
) {
	// Recurse into all children first.
	match &mut expr.kind {
		ExprKind::LocalSet { value, .. }
		| ExprKind::GlobalSet { value, .. }
		| ExprKind::Drop { value }
		| ExprKind::AggregateSet { value, .. }
		| ExprKind::Neg { value }
		| ExprKind::Sqrt { value }
		| ExprKind::Abs { value }
		| ExprKind::Floor { value }
		| ExprKind::Ceil { value }
		| ExprKind::BitNot { value }
		| ExprKind::Eqz { value }
		| ExprKind::I64ExtendI32S { value }
		| ExprKind::I64ExtendI32U { value }
		| ExprKind::I32WrapI64 { value }
		| ExprKind::F32ConvertI32 { value }
		| ExprKind::F32ConvertU32 { value }
		| ExprKind::F32ConvertI64 { value }
		| ExprKind::F32ConvertU64 { value }
		| ExprKind::F64ConvertI32 { value }
		| ExprKind::F64ConvertU32 { value }
		| ExprKind::F64ConvertI64 { value }
		| ExprKind::F64ConvertU64 { value }
		| ExprKind::I32TruncF32 { value }
		| ExprKind::U32TruncF32 { value }
		| ExprKind::I32TruncF64 { value }
		| ExprKind::U32TruncF64 { value }
		| ExprKind::I64TruncF32 { value }
		| ExprKind::U64TruncF32 { value }
		| ExprKind::I64TruncF64 { value }
		| ExprKind::U64TruncF64 { value }
		| ExprKind::F64PromoteF32 { value }
		| ExprKind::F32DemoteF64 { value } => inline_expr(
			value,
			caller_scopes,
			inline_id,
			inline_body,
			current_scope,
		),

		ExprKind::Aggregate { values: fields } => {
			for e in fields.iter_mut() {
				inline_expr(
					e,
					caller_scopes,
					inline_id,
					inline_body,
					current_scope,
				);
			}
		}
		ExprKind::Block {
			scope_index,
			expressions,
			..
		} => {
			let block_scope = *scope_index;
			for e in expressions.iter_mut() {
				inline_expr(
					e,
					caller_scopes,
					inline_id,
					inline_body,
					block_scope,
				);
			}
		}
		ExprKind::Loop { block, .. } => inline_expr(
			block,
			caller_scopes,
			inline_id,
			inline_body,
			current_scope,
		),

		ExprKind::Break { value, .. } | ExprKind::Return { value } => {
			if let Some(v) = value {
				inline_expr(
					v,
					caller_scopes,
					inline_id,
					inline_body,
					current_scope,
				);
			}
		}
		ExprKind::IfElse {
			condition,
			then_block,
			else_block,
		} => {
			inline_expr(
				condition,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			inline_expr(
				then_block,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			if let Some(e) = else_block {
				inline_expr(
					e,
					caller_scopes,
					inline_id,
					inline_body,
					current_scope,
				);
			}
		}
		ExprKind::Switch {
			selector,
			cases,
			default,
		} => {
			inline_expr(
				selector,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			for (_, body) in cases.iter_mut() {
				inline_expr(
					body,
					caller_scopes,
					inline_id,
					inline_body,
					current_scope,
				);
			}
			if let Some(e) = default {
				inline_expr(
					e,
					caller_scopes,
					inline_id,
					inline_body,
					current_scope,
				);
			}
		}
		ExprKind::Call { callee, arguments } => {
			inline_expr(
				callee,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			for a in arguments.iter_mut() {
				inline_expr(
					a,
					caller_scopes,
					inline_id,
					inline_body,
					current_scope,
				);
			}
		}
		ExprKind::Add { left, right }
		| ExprKind::Sub { left, right }
		| ExprKind::Mul { left, right }
		| ExprKind::Div { left, right }
		| ExprKind::Rem { left, right }
		| ExprKind::And { left, right }
		| ExprKind::Or { left, right }
		| ExprKind::Eq { left, right }
		| ExprKind::NotEq { left, right }
		| ExprKind::Less { left, right }
		| ExprKind::LessEq { left, right }
		| ExprKind::Greater { left, right }
		| ExprKind::GreaterEq { left, right }
		| ExprKind::BitAnd { left, right }
		| ExprKind::BitOr { left, right }
		| ExprKind::BitXor { left, right }
		| ExprKind::LeftShift { left, right }
		| ExprKind::RightShift { left, right } => {
			inline_expr(
				left,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			inline_expr(
				right,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
		}
		ExprKind::MemoryGrow { delta, .. } => inline_expr(
			delta,
			caller_scopes,
			inline_id,
			inline_body,
			current_scope,
		),
		ExprKind::MemoryFill { dst, val, len, .. } => {
			inline_expr(
				dst,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			inline_expr(
				val,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			inline_expr(
				len,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
		}
		ExprKind::MemoryCopy { dst, src, len, .. } => {
			inline_expr(
				dst,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			inline_expr(
				src,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			inline_expr(
				len,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
		}
		ExprKind::PointerLoad { pointer, .. } => inline_expr(
			pointer,
			caller_scopes,
			inline_id,
			inline_body,
			current_scope,
		),
		ExprKind::PointerStore { pointer, value, .. } => {
			inline_expr(
				pointer,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
			inline_expr(
				value,
				caller_scopes,
				inline_id,
				inline_body,
				current_scope,
			);
		}
		// Leaf variants — nothing to recurse into.
		ExprKind::Noop
		| ExprKind::Bool { .. }
		| ExprKind::Function { .. }
		| ExprKind::Int { .. }
		| ExprKind::Float { .. }
		| ExprKind::Global { .. }
		| ExprKind::Unreachable
		| ExprKind::LocalGet { .. }
		| ExprKind::AggregateGet { .. }
		| ExprKind::Continue { .. }
		| ExprKind::MemoryOffset { .. }
		| ExprKind::MemoryIndex { .. }
		| ExprKind::MemorySize { .. }
		| ExprKind::StaticPointer { .. } => {}
	}

	// After children are processed, check if this node is a call to inline_id.
	let id = match &expr.kind {
		ExprKind::Call { callee, .. } => match &callee.kind {
			ExprKind::Function { id } => *id,
			_ => return,
		},
		_ => return,
	};
	if id != inline_id {
		return;
	}

	let arguments = match std::mem::replace(&mut expr.kind, ExprKind::Noop) {
		ExprKind::Call { arguments, .. } => arguments,
		_ => unreachable!(),
	};
	*expr = inline_call(inline_body, arguments, caller_scopes, current_scope);
}

/// Directed call graph over MIR function `DefId`s.
struct CallGraph {
	/// `callees[A]` = functions that A calls.
	callees: HashMap<ast::DefId, HashSet<ast::DefId>>,
	/// `callers[A]` = functions that call A.
	callers: HashMap<ast::DefId, HashSet<ast::DefId>>,
}

impl CallGraph {
	fn build(
		functions: &[Function],
		call_edges: &[(ast::DefId, ast::DefId)],
	) -> Self {
		let mut callees: HashMap<ast::DefId, HashSet<ast::DefId>> =
			HashMap::with_capacity(functions.len());
		let mut callers: HashMap<ast::DefId, HashSet<ast::DefId>> =
			HashMap::with_capacity(functions.len());
		for f in functions {
			callees.insert(f.id, HashSet::new());
			callers.insert(f.id, HashSet::new());
		}

		for &(caller_id, callee_id) in call_edges {
			if let Some(caller_callees) = callees.get_mut(&caller_id) {
				caller_callees.insert(callee_id);
			}
			if let Some(callee_callers) = callers.get_mut(&callee_id) {
				callee_callers.insert(caller_id);
			}
		}

		CallGraph { callees, callers }
	}
}

/// Inlines all `#[inline]` functions in topological order, then removes
/// unreachable functions — and unreachable imported functions — via dead
/// code elimination from export roots.
pub fn run_inlining_pass(mir: &mut MIR) {
	let mut graph = CallGraph::build(&mir.functions, &mir.call_edges);

	// DefId → index in mir.functions for O(1) mutation during inlining.
	let func_idx: HashMap<ast::DefId, usize> = mir
		.functions
		.iter()
		.enumerate()
		.map(|(i, f)| (f.id, i))
		.collect();

	// Kahn's algorithm on the inline subgraph:
	// in-degree = number of inline callees not yet processed.
	let mut inline_callee_count: HashMap<ast::DefId, usize> = mir
		.inline_functions
		.iter()
		.map(|&id| {
			let count = graph.callees[&id]
				.iter()
				.filter(|c| mir.inline_functions.contains(c))
				.count();
			(id, count)
		})
		.collect();

	let mut queue: VecDeque<ast::DefId> = inline_callee_count
		.iter()
		.filter(|(_, n)| **n == 0)
		.map(|(&id, _)| id)
		.collect();

	// Outer loop: run Kahn's, then break one mutual-recursion cycle at a time.
	// When all inline callees have been processed the inner while loop drains
	// to empty and there are no stalled nodes left, so we break out.
	loop {
		while let Some(f_id) = queue.pop_front() {
			// f's body is clean: all of its inline callees were processed first.
			// Clone once here; inline_call will clone scopes+block again per call site.
			let f_body = mir.functions[func_idx[&f_id]].clone();

			let caller_ids: Vec<ast::DefId> =
				graph.callers[&f_id].iter().copied().collect();
			// f's own callee set doesn't change while its callers are being
			// processed below (only caller/f edges are touched), so collect
			// it once here instead of re-cloning it on every caller.
			let f_callees: Vec<ast::DefId> =
				graph.callees[&f_id].iter().copied().collect();
			for caller_id in caller_ids {
				let ci = func_idx[&caller_id];
				let caller_func = &mut mir.functions[ci];
				inline_expr(
					&mut caller_func.block,
					&mut caller_func.scopes,
					f_id,
					&f_body,
					0,
				);
				caller_func
					.static_data
					.extend_from_slice(&f_body.static_data);

				// Update graph: remove caller → f, propagate f's callees to caller.
				graph.callees.get_mut(&caller_id).unwrap().remove(&f_id);
				graph.callers.get_mut(&f_id).unwrap().remove(&caller_id);
				for callee_id in f_callees.iter().copied() {
					graph
						.callees
						.get_mut(&caller_id)
						.unwrap()
						.insert(callee_id);
					graph
						.callers
						.get_mut(&callee_id)
						.unwrap()
						.insert(caller_id);
				}

				// If caller is also inline, one of its pending inline callees is done.
				if let Some(count) = inline_callee_count.get_mut(&caller_id) {
					*count -= 1;
					if *count == 0 {
						queue.push_back(caller_id);
					}
				}
			}
			// graph.callers[f_id] is now empty — f is dead.
		}

		// Cycle-breaker: any inline function still with count > 0 is part of a
		// mutual-recursion cycle.  Inlining it fully would require infinite
		// expansion, so we evict one "anchor" per iteration — it stays as an
		// ordinary call target — then decrement its inline callers so they may
		// become unblocked and get inlined on the next inner-loop pass.
		let anchor = inline_callee_count
			.iter()
			.find(|(_, n)| **n > 0)
			.map(|(&id, _)| id);
		let Some(anchor) = anchor else { break };
		inline_callee_count.remove(&anchor);
		for caller_id in
			graph.callers[&anchor].iter().copied().collect::<Vec<_>>()
		{
			if let Some(count) = inline_callee_count.get_mut(&caller_id) {
				*count -= 1;
				if *count == 0 {
					queue.push_back(caller_id);
				}
			}
		}
	}

	// Dead code elimination: BFS from exported functions and the start function.
	let mut live: HashSet<ast::DefId> = mir
		.exports
		.iter()
		.filter_map(|e| match e {
			ExportItem::Function { id, .. } => Some(*id),
			_ => None,
		})
		.collect();
	if let Some(start_id) = mir.start_function {
		live.insert(start_id);
	}
	let mut dce_queue: VecDeque<ast::DefId> = live.iter().copied().collect();
	while let Some(id) = dce_queue.pop_front() {
		for &callee_id in graph.callees.get(&id).into_iter().flatten() {
			if live.insert(callee_id) {
				dce_queue.push_back(callee_id);
			}
		}
	}
	mir.functions.retain(|f| live.contains(&f.id));

	// Imported functions share the same DefId space and flow through the
	// same call_edges as regular calls (see `record_call_edge`), so `live`
	// already tells us which imported functions are actually reachable.
	// Imported globals/memories aren't tracked here yet — they're not part
	// of `call_edges` — so leave those import kinds untouched for now.
	for module in &mut mir.imports {
		module.items.retain(|item| match item {
			ImportModuleItem::Function { id, .. } => live.contains(id),
			ImportModuleItem::Global { .. }
			| ImportModuleItem::Memory { .. } => true,
		});
	}
	mir.imports.retain(|module| !module.items.is_empty());
}
