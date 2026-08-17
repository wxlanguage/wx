use std::collections::{HashMap, HashSet, VecDeque};

use crate::ast;
use crate::mir::*;
use crate::tir;

/// Offsets every scope index in `expr` by `scope_offset` (in place), and
/// rewrites `Return { value }` into `Break { scope_index: wrapper_scope,
/// value }`. Used for combining multiple globals' own scope trees into one
/// synthesized start function (`mir::MIR::build_start_function`) — a plain
/// uniform shift, no root-scope redirect needed, since each global's own
/// root scope becomes a genuinely new, disjoint scope of its own rather
/// than dissolving into an existing one. Implemented as the no-redirect
/// case of `Rebaser` (`root_scope: scope_offset, root_bias: 0` — redirecting
/// scope `0` to exactly where a plain `+= scope_offset` shift would already
/// send it) rather than a second, separately-maintained walk.
pub(super) fn rebase_scope(
	expr: &mut Expression,
	scope_offset: ScopeIndex,
	wrapper_scope: ScopeIndex,
) {
	Rebaser {
		scope_offset,
		wrapper_scope,
		root_scope: scope_offset,
		root_bias: 0,
	}
	.rebase(expr);
}

/// Rewrites scope/local references while splicing one scope tree into
/// another. Every scope index shifts by `scope_offset`, *except* index `0`
/// (a tree's own root, in its own numbering), which redirects to
/// `root_scope` instead, with `local_index` shifted by `root_bias` — the
/// callee's-parameters-become-more-locals-on-an-existing-scope case
/// `mir::inlining::inline_call` needs. `rebase_scope` (above) is the
/// special case of this where root scope `0` redirects to exactly
/// `scope_offset`, i.e. nowhere special — a plain uniform shift, which is
/// all `MIR::build_start_function`'s use (combining separate globals' own
/// scope trees, each becoming a genuinely new disjoint scope) ever needs.
struct Rebaser {
	scope_offset: ScopeIndex,
	wrapper_scope: ScopeIndex,
	root_scope: ScopeIndex,
	root_bias: LocalIndex,
}

impl Rebaser {
	/// For a reference that carries only a scope index (`Block`, `Loop`,
	/// `Break`, `Continue` — no local of their own to shift).
	#[inline]
	fn rebase_scope(&self, scope_index: &mut ScopeIndex) {
		if *scope_index == 0 {
			*scope_index = self.root_scope;
		} else {
			*scope_index += self.scope_offset;
		}
	}

	/// For a reference that carries both a scope index and a local index
	/// within it (`LocalGet`/`LocalSet`/`AggregateGet`/`AggregateSet`).
	#[inline]
	fn rebase_scope_and_local(
		&self,
		scope_index: &mut ScopeIndex,
		local_index: &mut LocalIndex,
	) {
		if *scope_index == 0 {
			*scope_index = self.root_scope;
			*local_index += self.root_bias;
		} else {
			*scope_index += self.scope_offset;
		}
	}

	fn rebase(&self, expr: &mut Expression) {
		match &mut expr.kind {
			ExprKind::LocalGet {
				scope_index,
				local_index,
			} => self.rebase_scope_and_local(scope_index, local_index),
			ExprKind::AggregateGet {
				scope_index,
				local_index,
				..
			} => self.rebase_scope_and_local(scope_index, local_index),
			ExprKind::Continue { scope_index } => {
				self.rebase_scope(scope_index)
			}
			ExprKind::LocalSet {
				scope_index,
				local_index,
				value,
			} => {
				self.rebase_scope_and_local(scope_index, local_index);
				self.rebase(value);
			}
			ExprKind::AggregateSet {
				scope_index,
				local_index,
				value,
				..
			} => {
				self.rebase_scope_and_local(scope_index, local_index);
				self.rebase(value);
			}
			ExprKind::Loop {
				scope_index,
				block: value,
			} => {
				self.rebase_scope(scope_index);
				self.rebase(value);
			}
			ExprKind::Block {
				scope_index,
				expressions,
			} => {
				self.rebase_scope(scope_index);
				for e in expressions.iter_mut() {
					self.rebase(e);
				}
			}
			ExprKind::Break { scope_index, value } => {
				self.rebase_scope(scope_index);
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
			ExprKind::Drop { value }
			| ExprKind::GlobalSet { value, .. }
			| ExprKind::Neg { value }
			| ExprKind::Sqrt { value }
			| ExprKind::Abs { value }
			| ExprKind::Floor { value }
			| ExprKind::Ceil { value }
			| ExprKind::Trunc { value }
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

/// Substitutes a direct call at the call site with the callee's body inlined
/// into the caller. Appends any scopes the callee needs beyond its root to
/// `caller_scopes`.
///
/// The callee's own root-scope locals — its parameters, and any `local` it
/// declares directly in its own body — become more locals on
/// `caller_scopes[call_site_scope]` itself, not a new sibling scope. A
/// second inlined call at the same site (another argument of the same
/// expression, or a later, separate inlining sweep substituting a sibling)
/// simply finds more locals already there and gets index ranges past them —
/// the same way a second ordinary `local` declaration would. Nothing needs
/// protecting: `Vec::push` can't collide with itself.
///
/// (This is what `compute_locals_offsets` in `opt/builder.rs` used to get
/// wrong: it gives every scope the same flat local-offset as its
/// `parent`-siblings, assuming — correctly for `if`/`else`/`match` arms,
/// the only shape ordinary lowering produces — that same-parent scopes are
/// mutually exclusive at runtime. Inlining used to create a *new* sibling
/// scope per call for exactly this data, which made that assumption false.
/// Not creating that scope removes the false assumption instead of working
/// around it.)
///
/// The wrapper scope below still exists, unconditionally, as the `break`
/// target for the callee's own `Return`s — but it never holds any locals
/// itself, so it's always safe to parent directly at the call site.
fn inline_call(
	callee: &Function,
	arguments: Box<[Expression]>,
	caller_scopes: &mut Vec<BlockScope>,
	call_site_scope: ScopeIndex,
) -> Expression {
	let result_ty = callee.block.ty;
	let callee_root = &callee.scopes[0];

	let root_bias =
		caller_scopes[call_site_scope as usize].locals.len() as LocalIndex;
	caller_scopes[call_site_scope as usize]
		.locals
		.extend(callee_root.locals.iter().cloned());

	let mut exprs: Vec<Expression> = arguments
		.into_vec()
		.into_iter()
		.enumerate()
		.map(|(i, arg)| Expression {
			ty: Type::Unit,
			kind: ExprKind::LocalSet {
				scope_index: call_site_scope,
				local_index: root_bias + i as LocalIndex,
				value: Box::new(arg),
			},
		})
		.collect();

	let wrapper_scope = caller_scopes.len() as ScopeIndex;
	caller_scopes.push(BlockScope {
		kind: tir::BlockKind::Block,
		parent: Some(call_site_scope),
		locals: vec![],
		result: result_ty,
	});

	// Any scopes the callee's own body nests beyond its root (its own
	// if/else, loops, ...) still need their own entries, following the
	// wrapper — the callee's root itself is never copied; it was just
	// dissolved into `call_site_scope` above. Scope `k` (k >= 1) in the
	// callee's own numbering lands at `k + wrapper_scope`; a parent of `0`
	// (the callee's own root) becomes `wrapper_scope` by that same formula.
	for scope in callee.scopes[1..].iter().cloned() {
		caller_scopes.push(BlockScope {
			parent: scope.parent.map(|p| p + wrapper_scope),
			..scope
		});
	}

	let mut body = callee.block.clone();
	Rebaser {
		scope_offset: wrapper_scope,
		wrapper_scope,
		root_scope: call_site_scope,
		root_bias,
	}
	.rebase(&mut body);
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
		| ExprKind::Trunc { value }
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
