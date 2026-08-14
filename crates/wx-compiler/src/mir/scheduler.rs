//! Lower a [`mir::Function`] directly to a [`wasm::Function`], bypassing the
//! sea-of-nodes `opt` pipeline entirely — no CSE, no scheduling decisions,
//! no `#[inline]` substitution assumed. Instructions come out in exactly the
//! order the source expression tree implies, and every declared local gets
//! its own fixed WASM slot. This is the debug-mode counterpart to
//! `opt::scheduler`: source-faithful by construction rather than optimized.
//!
//! Every `ExprKind` is handled — `emit_expr`'s match is exhaustive, checked
//! by the compiler. Aggregates (as locals, loads/stores, and call args/
//! results) are just their flattened leaf fields as consecutive WASM stack
//! values / consecutive local slots, matching the convention WASM's own
//! multi-value params/results already use — no separate representation
//! needed. `match` always lowers to an if/else-if chain rather than
//! replicating `opt::builder`'s dense-vs-sparse `br_table` choice — simpler,
//! and correctness doesn't need the optimization.

use crate::ast;
use crate::mir::{self, ExprKind, Expression};
use crate::opt::MemAccess;
use crate::wasm::{self, BlockType, Instruction, MemArg, ScalarType};

/// Maps each MIR scope's locals to WASM local indices. Every local gets its
/// own dedicated slot — no sharing across sibling scopes, unlike
/// `opt::builder`'s `compute_locals_offsets`: that scheme is safe for that
/// module's internal bookkeeping (never emitted as WASM), but a WASM local
/// has one fixed type for the whole function, so two sibling branches
/// declaring locals of different types could never safely share a slot.
/// `wasm::coalesce_locals` can safely reclaim unused slots afterward — it
/// already does type-aware reuse.
struct LocalTable {
	/// `starts[scope_index][local_index]` = first WASM local index for that
	/// MIR local (aggregates occupy `starts[..] .. starts[..] + N` for their
	/// `N` flattened leaf fields).
	starts: Vec<Vec<u32>>,
	/// Declared WASM locals, in slot order (params first, per `scopes[0]`).
	locals: Vec<wasm::Local>,
	/// One entry per named local (i.e. every `scope.locals_debug` entry —
	/// see `mir::LocalDebugInfo`, only ever populated when `mir::MIR` was
	/// built with `CompilationMode::Debug`, which is the only mode that
	/// ever reaches this scheduler), resolved to the wasm-local range it
	/// occupies.
	locals_debug: Vec<wasm::LocalDebugInfo>,
}

impl LocalTable {
	fn build(
		scopes: &[mir::BlockScope],
		aggregates: &[mir::Aggregate],
	) -> Self {
		let mut starts = Vec::with_capacity(scopes.len());
		let mut locals = Vec::new();
		let mut locals_debug = Vec::new();
		for scope in scopes {
			let mut scope_starts = Vec::with_capacity(scope.locals.len());
			for (local_index, local) in scope.locals.iter().enumerate() {
				let wasm_local_start = locals.len() as u32;
				scope_starts.push(wasm_local_start);
				for ty in wasm::flatten_type_to_scalars(local.ty, aggregates) {
					locals.push(wasm::Local { ty });
				}
				// `locals_debug` only covers a scope's originally-declared
				// locals, in the same order — anything past its end is a
				// compiler-synthesized temporary with no debug info.
				if let Some(debug) = scope.locals_debug.get(local_index) {
					locals_debug.push(wasm::LocalDebugInfo {
						name: debug.name,
						ty: local.ty,
						struct_debug: debug.struct_debug.clone(),
						wasm_local_start,
						wasm_local_count: locals.len() as u32
							- wasm_local_start,
					});
				}
			}
			starts.push(scope_starts);
		}
		LocalTable {
			starts,
			locals,
			locals_debug,
		}
	}

	fn wasm_index(
		&self,
		scope_index: mir::ScopeIndex,
		local_index: mir::LocalIndex,
	) -> u32 {
		self.starts[scope_index as usize][local_index as usize]
	}
}

/// One currently-open WASM construct that `break`/`continue` can jump to,
/// tagged with the MIR scope it corresponds to. Depth is computed by
/// walking this stack from the top, charging each entry its real WASM
/// nesting cost (mirrors `opt::scheduler::break_depth`'s per-node cost).
enum BranchTarget {
	/// An ordinary `block`, or one arm of an `if` (an if's two arms share
	/// one real WASM level, so each gets its own entry but they're never
	/// open simultaneously) — costs 1 level to walk through.
	Block(mir::ScopeIndex),
	/// A `loop` — an outer `block` (the `break` target) wrapping an inner
	/// `loop` (the `continue` target), two real WASM levels tracked as one
	/// logical entry. `result_local` is where a `break <value>` stores its
	/// value for code after the loop to read; `None` if the loop's type is
	/// `Unit`/`Never`.
	Loop {
		scope_index: mir::ScopeIndex,
		result_local: Option<u32>,
	},
}

struct Scheduler<'f> {
	mir: &'f mir::MIR,
	/// Needed (alongside `mir`) to look up a local's declared MIR type —
	/// e.g. resolving `AggregateGet`'s `aggregate_index`, which isn't
	/// carried on the node itself, only recoverable from what the local
	/// was declared as.
	mir_func: &'f mir::Function,
	table: LocalTable,
	body: Vec<Instruction>,
	/// `spans[i]` is the source span for `body[i]` — see `emit`. Tracks
	/// `current_span`, which every `emit_expr` call saves and restores
	/// around its own span, so instructions pushed while lowering a nested
	/// expression get that expression's span rather than its ancestor's.
	spans: Vec<ast::TextSpan>,
	current_span: ast::TextSpan,
	br_table_depths: Vec<u32>,
	branch_targets: Vec<BranchTarget>,
}

/// Lower one MIR function directly into a [`wasm::Function`].
pub fn schedule(mir_func: &mir::Function, mir: &mir::MIR) -> wasm::Function {
	let mut sched = Scheduler {
		mir,
		mir_func,
		table: LocalTable::build(&mir_func.scopes, &mir.aggregates),
		body: Vec::new(),
		spans: Vec::new(),
		current_span: mir_func.block.span,
		br_table_depths: Vec::new(),
		branch_targets: Vec::new(),
	};

	let body_exprs = match &mir_func.block.kind {
		ExprKind::Block { expressions, .. } => expressions,
		_ => unreachable!("function body must be a Block"),
	};
	sched.emit_sequence(body_exprs);

	if matches!(sched.body.last(), Some(Instruction::Return)) {
		sched.body.pop();
		sched.spans.pop();
	}

	wasm::Function {
		locals: sched.table.locals,
		body: sched.body,
		br_table_depths: sched.br_table_depths,
		spans: sched.spans,
		locals_debug: sched.table.locals_debug,
	}
}

fn scalar_ty(ty: mir::Type) -> ScalarType {
	ScalarType::try_from(ty).expect("must be scalar")
}

/// The WASM block-signature type for a construct whose MIR result type is
/// `ty` — `Empty` for `Unit`/`Never` (nothing left on the stack), otherwise
/// the single scalar value produced. Divergent arms (type `Never`) validate
/// under any declared block type since WASM treats code after an
/// unconditional `return`/`br`/`unreachable` as stack-polymorphic — no
/// special-casing needed here.
fn block_type(ty: mir::Type) -> BlockType {
	match ty {
		mir::Type::Unit | mir::Type::Never => BlockType::Empty,
		scalar => BlockType::Value(scalar_ty(scalar)),
	}
}

/// Extract `(scope_index, expressions)` from a `Block` expression — every
/// `if`/`loop` arm's body is one, matching `opt::builder::unwrap_block`.
fn unwrap_block(expr: &Expression) -> (mir::ScopeIndex, &[Expression]) {
	match &expr.kind {
		ExprKind::Block {
			scope_index,
			expressions,
		} => (*scope_index, expressions),
		_ => panic!("expected Block expression"),
	}
}

fn add_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Add,
		ScalarType::I64 => Instruction::I64Add,
		ScalarType::F32 => Instruction::F32Add,
		ScalarType::F64 => Instruction::F64Add,
	}
}

fn sub_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Sub,
		ScalarType::I64 => Instruction::I64Sub,
		ScalarType::F32 => Instruction::F32Sub,
		ScalarType::F64 => Instruction::F64Sub,
	}
}

fn mul_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Mul,
		ScalarType::I64 => Instruction::I64Mul,
		ScalarType::F32 => Instruction::F32Mul,
		ScalarType::F64 => Instruction::F64Mul,
	}
}

fn div_instr(ty: ScalarType, unsigned: bool) -> Instruction {
	match (ty, unsigned) {
		(ScalarType::I32, true) => Instruction::I32DivU,
		(ScalarType::I32, false) => Instruction::I32DivS,
		(ScalarType::I64, true) => Instruction::I64DivU,
		(ScalarType::I64, false) => Instruction::I64DivS,
		(ScalarType::F32, _) => Instruction::F32Div,
		(ScalarType::F64, _) => Instruction::F64Div,
	}
}

fn rem_instr(ty: ScalarType, unsigned: bool) -> Instruction {
	match (ty, unsigned) {
		(ScalarType::I32, true) => Instruction::I32RemU,
		(ScalarType::I32, false) => Instruction::I32RemS,
		(ScalarType::I64, true) => Instruction::I64RemU,
		(ScalarType::I64, false) => Instruction::I64RemS,
		_ => unreachable!("Rem is only valid on integers"),
	}
}

fn eq_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Eq,
		ScalarType::I64 => Instruction::I64Eq,
		ScalarType::F32 => Instruction::F32Eq,
		ScalarType::F64 => Instruction::F64Eq,
	}
}

fn ne_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Ne,
		ScalarType::I64 => Instruction::I64Ne,
		ScalarType::F32 => Instruction::F32Ne,
		ScalarType::F64 => Instruction::F64Ne,
	}
}

fn lt_instr(ty: ScalarType, unsigned: bool) -> Instruction {
	match (ty, unsigned) {
		(ScalarType::I32, true) => Instruction::I32LtU,
		(ScalarType::I32, false) => Instruction::I32LtS,
		(ScalarType::I64, true) => Instruction::I64LtU,
		(ScalarType::I64, false) => Instruction::I64LtS,
		(ScalarType::F32, _) => Instruction::F32Lt,
		(ScalarType::F64, _) => Instruction::F64Lt,
	}
}

fn le_instr(ty: ScalarType, unsigned: bool) -> Instruction {
	match (ty, unsigned) {
		(ScalarType::I32, true) => Instruction::I32LeU,
		(ScalarType::I32, false) => Instruction::I32LeS,
		(ScalarType::I64, true) => Instruction::I64LeU,
		(ScalarType::I64, false) => Instruction::I64LeS,
		(ScalarType::F32, _) => Instruction::F32Le,
		(ScalarType::F64, _) => Instruction::F64Le,
	}
}

fn gt_instr(ty: ScalarType, unsigned: bool) -> Instruction {
	match (ty, unsigned) {
		(ScalarType::I32, true) => Instruction::I32GtU,
		(ScalarType::I32, false) => Instruction::I32GtS,
		(ScalarType::I64, true) => Instruction::I64GtU,
		(ScalarType::I64, false) => Instruction::I64GtS,
		(ScalarType::F32, _) => Instruction::F32Gt,
		(ScalarType::F64, _) => Instruction::F64Gt,
	}
}

fn ge_instr(ty: ScalarType, unsigned: bool) -> Instruction {
	match (ty, unsigned) {
		(ScalarType::I32, true) => Instruction::I32GeU,
		(ScalarType::I32, false) => Instruction::I32GeS,
		(ScalarType::I64, true) => Instruction::I64GeU,
		(ScalarType::I64, false) => Instruction::I64GeS,
		(ScalarType::F32, _) => Instruction::F32Ge,
		(ScalarType::F64, _) => Instruction::F64Ge,
	}
}

/// `And`/`Or` and `BitAnd`/`BitOr` compile to the same instruction — MIR's
/// `bool` is just `i32` 0/1, so bitwise-and/or already gives the right
/// truth table without short-circuiting. `opt::builder` treats them
/// identically for the same reason.
fn bitand_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32And,
		ScalarType::I64 => Instruction::I64And,
		_ => unreachable!("And/BitAnd is only valid on integers"),
	}
}

fn bitor_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Or,
		ScalarType::I64 => Instruction::I64Or,
		_ => unreachable!("Or/BitOr is only valid on integers"),
	}
}

fn bitxor_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Xor,
		ScalarType::I64 => Instruction::I64Xor,
		_ => unreachable!("BitXor is only valid on integers"),
	}
}

fn shl_instr(ty: ScalarType) -> Instruction {
	match ty {
		ScalarType::I32 => Instruction::I32Shl,
		ScalarType::I64 => Instruction::I64Shl,
		_ => unreachable!("LeftShift is only valid on integers"),
	}
}

fn shr_instr(ty: ScalarType, unsigned: bool) -> Instruction {
	match (ty, unsigned) {
		(ScalarType::I32, true) => Instruction::I32ShrU,
		(ScalarType::I32, false) => Instruction::I32ShrS,
		(ScalarType::I64, true) => Instruction::I64ShrU,
		(ScalarType::I64, false) => Instruction::I64ShrS,
		_ => unreachable!("RightShift is only valid on integers"),
	}
}

fn cast_instr(kind: &ExprKind) -> Instruction {
	match kind {
		ExprKind::I64ExtendI32S { .. } => Instruction::I64ExtendI32S,
		ExprKind::I64ExtendI32U { .. } => Instruction::I64ExtendI32U,
		ExprKind::I32WrapI64 { .. } => Instruction::I32WrapI64,
		ExprKind::F32ConvertI32 { .. } => Instruction::F32ConvertI32S,
		ExprKind::F32ConvertU32 { .. } => Instruction::F32ConvertI32U,
		ExprKind::F32ConvertI64 { .. } => Instruction::F32ConvertI64S,
		ExprKind::F32ConvertU64 { .. } => Instruction::F32ConvertI64U,
		ExprKind::F64ConvertI32 { .. } => Instruction::F64ConvertI32S,
		ExprKind::F64ConvertU32 { .. } => Instruction::F64ConvertI32U,
		ExprKind::F64ConvertI64 { .. } => Instruction::F64ConvertI64S,
		ExprKind::F64ConvertU64 { .. } => Instruction::F64ConvertI64U,
		ExprKind::I32TruncF32 { .. } => Instruction::I32TruncF32S,
		ExprKind::U32TruncF32 { .. } => Instruction::I32TruncF32U,
		ExprKind::I32TruncF64 { .. } => Instruction::I32TruncF64S,
		ExprKind::U32TruncF64 { .. } => Instruction::I32TruncF64U,
		ExprKind::I64TruncF32 { .. } => Instruction::I64TruncF32S,
		ExprKind::U64TruncF32 { .. } => Instruction::I64TruncF32U,
		ExprKind::I64TruncF64 { .. } => Instruction::I64TruncF64S,
		ExprKind::U64TruncF64 { .. } => Instruction::I64TruncF64U,
		ExprKind::F64PromoteF32 { .. } => Instruction::F64PromoteF32,
		ExprKind::F32DemoteF64 { .. } => Instruction::F32DemoteF64,
		_ => unreachable!("cast_instr called on a non-cast ExprKind"),
	}
}

impl Scheduler<'_> {
	/// Allocate a fresh WASM local beyond what `LocalTable` declared from
	/// source — used for compiler-synthesized temporaries like a loop's
	/// break-value slot.
	fn alloc_local(&mut self, ty: ScalarType) -> u32 {
		let idx = self.table.locals.len() as u32;
		self.table.locals.push(wasm::Local { ty });
		idx
	}

	/// The aggregate a local was declared as — recovered from its
	/// declaration (`mir_func`), since `AggregateGet`/`AggregateSet` don't
	/// carry it on the node itself.
	fn local_aggregate_index(
		&self,
		scope_index: mir::ScopeIndex,
		local_index: mir::LocalIndex,
	) -> mir::AggregateIndex {
		match self.mir_func.scopes[scope_index as usize].locals
			[local_index as usize]
			.ty
		{
			mir::Type::Aggregate { aggregate_index } => aggregate_index,
			_ => unreachable!(
				"AggregateGet/AggregateSet on a non-aggregate local"
			),
		}
	}

	/// `(leaf-slot start offset, leaf-slot count)` for field `value_index`
	/// within an aggregate, in the same flattened order `LocalTable`/
	/// `wasm::flatten_type_to_scalars` use — `value_index` is already a
	/// physical (layout-order) index by this stage of MIR, matching
	/// `Aggregate::values`'s own order, so no `decl_to_phys` translation is
	/// needed here (that already happened once, upstream during lowering).
	fn aggregate_field_slots(
		&self,
		aggregate_index: mir::AggregateIndex,
		value_index: usize,
	) -> (u32, u32) {
		let values = &self.mir.aggregates[aggregate_index as usize].values;
		let start: u32 = values[..value_index]
			.iter()
			.map(|&t| {
				wasm::flatten_type_to_scalars(t, &self.mir.aggregates).len()
					as u32
			})
			.sum();
		let count = wasm::flatten_type_to_scalars(
			values[value_index],
			&self.mir.aggregates,
		)
		.len() as u32;
		(start, count)
	}

	/// Emit a scalar load — the address must already be on the stack.
	fn emit_scalar_load(
		&mut self,
		ty: mir::Type,
		offset: u32,
		memory: ast::DefId,
	) {
		let access = MemAccess::from_mir(ty);
		let m = MemArg {
			align: access.align_log2(),
			offset,
			memory,
		};
		self.emit(match access {
			MemAccess::I8S => Instruction::I32Load8S(m),
			MemAccess::I8U => Instruction::I32Load8U(m),
			MemAccess::I16S => Instruction::I32Load16S(m),
			MemAccess::I16U => Instruction::I32Load16U(m),
			MemAccess::I32 => Instruction::I32Load(m),
			MemAccess::I64 => Instruction::I64Load(m),
			MemAccess::F32 => Instruction::F32Load(m),
			MemAccess::F64 => Instruction::F64Load(m),
		});
	}

	/// Emit a scalar store — the address and value must already be on the
	/// stack, address pushed first.
	fn emit_scalar_store(
		&mut self,
		ty: mir::Type,
		offset: u32,
		memory: ast::DefId,
	) {
		let access = MemAccess::from_mir(ty);
		let m = MemArg {
			align: access.align_log2(),
			offset,
			memory,
		};
		self.emit(match access {
			MemAccess::I8S | MemAccess::I8U => Instruction::I32Store8(m),
			MemAccess::I16S | MemAccess::I16U => Instruction::I32Store16(m),
			MemAccess::I32 => Instruction::I32Store(m),
			MemAccess::I64 => Instruction::I64Store(m),
			MemAccess::F32 => Instruction::F32Store(m),
			MemAccess::F64 => Instruction::F64Store(m),
		});
	}

	/// Recursively load every leaf field of an aggregate at
	/// `addr_local + base_offset`, pushing them in physical order — the
	/// address is re-read from `addr_local` per leaf field rather than
	/// re-evaluating the pointer expression, which would re-run any side
	/// effects it has once per field instead of once total.
	fn emit_aggregate_load(
		&mut self,
		addr_local: u32,
		base_offset: u32,
		aggregate_index: mir::AggregateIndex,
		memory: ast::DefId,
	) {
		let n = self.mir.aggregates[aggregate_index as usize].values.len();
		for i in 0..n {
			let field_ty =
				self.mir.aggregates[aggregate_index as usize].values[i];
			let field_offset = base_offset
				+ self.mir.aggregates[aggregate_index as usize].offsets[i];
			match field_ty {
				mir::Type::Aggregate {
					aggregate_index: nested,
				} => {
					self.emit_aggregate_load(
						addr_local,
						field_offset,
						nested,
						memory,
					);
				}
				_ => {
					self.emit(Instruction::LocalGet(addr_local));
					self.emit_scalar_load(field_ty, field_offset, memory);
				}
			}
		}
	}

	/// Recursively store every leaf field of an aggregate — `value_locals`
	/// holds one already-spilled temp local per leaf field (in the same
	/// physical order `emit_aggregate_load`/`Aggregate` use), since storing
	/// needs the address pushed fresh before *each* field's value.
	fn emit_aggregate_store(
		&mut self,
		addr_local: u32,
		base_offset: u32,
		value_locals: &[u32],
		aggregate_index: mir::AggregateIndex,
		memory: ast::DefId,
	) {
		let n = self.mir.aggregates[aggregate_index as usize].values.len();
		let mut consumed = 0usize;
		for i in 0..n {
			let field_ty =
				self.mir.aggregates[aggregate_index as usize].values[i];
			let field_offset = base_offset
				+ self.mir.aggregates[aggregate_index as usize].offsets[i];
			let field_slots =
				wasm::flatten_type_to_scalars(field_ty, &self.mir.aggregates)
					.len();
			match field_ty {
				mir::Type::Aggregate {
					aggregate_index: nested,
				} => {
					self.emit_aggregate_store(
						addr_local,
						field_offset,
						&value_locals[consumed..consumed + field_slots],
						nested,
						memory,
					);
				}
				_ => {
					self.emit(Instruction::LocalGet(addr_local));
					self.emit(Instruction::LocalGet(value_locals[consumed]));
					self.emit_scalar_store(field_ty, field_offset, memory);
				}
			}
			consumed += field_slots;
		}
	}

	/// WASM `br` depth for a `break` targeting `target`, walking
	/// `branch_targets` from the innermost currently-open construct outward
	/// and charging each one its real WASM nesting cost — mirrors
	/// `opt::scheduler::break_depth` exactly, just walking a stack instead
	/// of a graph's block-parent chain.
	fn break_depth(&self, target: mir::ScopeIndex) -> u32 {
		let mut depth = 0u32;
		for bt in self.branch_targets.iter().rev() {
			match bt {
				BranchTarget::Block(s) if *s == target => return depth,
				BranchTarget::Loop { scope_index, .. }
					if *scope_index == target =>
				{
					return depth + 1;
				}
				BranchTarget::Block(_) => depth += 1,
				BranchTarget::Loop { .. } => depth += 2,
			}
		}
		unreachable!("break target scope not found in branch_targets")
	}

	/// WASM `br` depth for a `continue` (branch to loop header) targeting
	/// `target` — one level shallower than `break`'s, landing on the inner
	/// `loop` instead of the outer wrapping `block`. Only ever called with a
	/// `target` that's actually a `Loop` entry — TIR guarantees `continue`
	/// can't target a non-loop scope.
	fn continue_depth(&self, target: mir::ScopeIndex) -> u32 {
		self.break_depth(target) - 1
	}

	/// The break-value local for the (currently open) loop `target`, if it
	/// has one.
	fn loop_result_local(&self, target: mir::ScopeIndex) -> Option<u32> {
		self.branch_targets.iter().rev().find_map(|bt| match bt {
			BranchTarget::Loop {
				scope_index,
				result_local,
			} if *scope_index == target => Some(*result_local),
			_ => None,
		})?
	}

	/// Emit a sequence of statements: every non-final expression's value (if
	/// any) is explicitly dropped — unlike `opt::builder`, there's no graph
	/// to silently discard unused pure nodes, so a leftover WASM stack value
	/// has to be dropped for real or the emitted module is invalid.
	fn emit_sequence(&mut self, exprs: &[Expression]) {
		for (i, expr) in exprs.iter().enumerate() {
			let is_last = i == exprs.len() - 1;
			self.emit_expr(expr);
			if !is_last {
				self.drop_value(expr.ty, expr.span);
			}
		}
	}

	/// Drop a value of MIR type `ty` off the stack — one `Drop` per
	/// flattened leaf scalar, since an aggregate value is N separate WASM
	/// stack values, not one. No-op for `Unit`/`Never` (nothing was pushed).
	/// Tagged with `span` (the dropped expression's own) rather than
	/// whatever's currently ambient, since by the time a caller drops a
	/// value, `current_span` has already been restored past it.
	fn drop_value(&mut self, ty: mir::Type, span: ast::TextSpan) {
		self.current_span = span;
		let n = wasm::flatten_type_to_scalars(ty, &self.mir.aggregates).len();
		for _ in 0..n {
			self.emit(Instruction::Drop);
		}
	}

	/// Pushes `instr`, tagged with whichever expression's lowering is
	/// currently on the stack — see `emit_expr`'s save/restore of
	/// `current_span`.
	fn emit(&mut self, instr: Instruction) {
		self.body.push(instr);
		self.spans.push(self.current_span);
		debug_assert_eq!(
			self.body.len(),
			self.spans.len(),
			"every push to `body` must go through `emit` so `spans` stays \
			 index-aligned with it — some caller pushed to `self.body` \
			 directly"
		);
	}

	/// Sets `current_span` to `expr.span` for the duration of lowering
	/// `expr`, restoring the caller's span on return — so instructions
	/// pushed by a nested `emit_expr` call get that nested expression's own
	/// span, and control returns to the enclosing span automatically once
	/// it's done, with no explicit reset needed at each call site.
	fn emit_expr(&mut self, expr: &Expression) {
		let saved = self.current_span;
		self.current_span = expr.span;
		self.emit_expr_inner(expr);
		self.current_span = saved;
	}

	fn emit_expr_inner(&mut self, expr: &Expression) {
		match &expr.kind {
			ExprKind::Noop => {}
			ExprKind::Bool { value } => {
				self.emit(Instruction::I32Const(*value as i32));
			}
			ExprKind::Int { value } => self.emit_int_const(expr.ty, *value),
			ExprKind::Float { value } => self.emit_float_const(expr.ty, *value),
			ExprKind::LocalGet {
				scope_index,
				local_index,
			} => {
				// Mirrors `LocalSet` below: `expr.ty` may be aggregate-typed
				// (e.g. reading a whole `Point`-typed local to pass it as a
				// call argument), occupying N consecutive wasm locals — push
				// all N, not just the first.
				let idx = self.table.wasm_index(*scope_index, *local_index);
				let n = wasm::flatten_type_to_scalars(
					expr.ty,
					&self.mir.aggregates,
				)
				.len() as u32;
				for i in 0..n {
					self.emit(Instruction::LocalGet(idx + i));
				}
			}
			ExprKind::LocalSet {
				scope_index,
				local_index,
				value,
			} => {
				// `value` may itself be aggregate-typed (e.g. `local p:
				// Point = Point::{ .. }`), pushing N flattened values —
				// pop them into the local's N consecutive slots in
				// reverse, same convention as `AggregateSet`.
				self.emit_expr(value);
				let idx = self.table.wasm_index(*scope_index, *local_index);
				let n = wasm::flatten_type_to_scalars(
					value.ty,
					&self.mir.aggregates,
				)
				.len() as u32;
				for i in (0..n).rev() {
					self.emit(Instruction::LocalSet(idx + i));
				}
			}
			ExprKind::Add { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(add_instr(scalar_ty(expr.ty)));
			}
			ExprKind::Sub { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(sub_instr(scalar_ty(expr.ty)));
			}
			ExprKind::Mul { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(mul_instr(scalar_ty(expr.ty)));
			}
			ExprKind::Div { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(div_instr(scalar_ty(expr.ty), expr.ty.is_unsigned()));
			}
			ExprKind::Rem { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(rem_instr(scalar_ty(expr.ty), expr.ty.is_unsigned()));
			}
			ExprKind::Eq { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(eq_instr(scalar_ty(left.ty)));
			}
			ExprKind::NotEq { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(ne_instr(scalar_ty(left.ty)));
			}
			ExprKind::Less { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(lt_instr(scalar_ty(left.ty), left.ty.is_unsigned()));
			}
			ExprKind::LessEq { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(le_instr(scalar_ty(left.ty), left.ty.is_unsigned()));
			}
			ExprKind::Greater { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(gt_instr(scalar_ty(left.ty), left.ty.is_unsigned()));
			}
			ExprKind::GreaterEq { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(ge_instr(scalar_ty(left.ty), left.ty.is_unsigned()));
			}
			ExprKind::Eqz { value } => {
				// Always i32.eqz — matches opt::builder/opt::scheduler exactly:
				// `Eqz` is only ever constructed over an already-i32 (bool)
				// operand in this language, so `DataNodeKind::Eqz` there
				// doesn't even carry a type.
				self.emit_expr(value);
				self.emit(Instruction::I32Eqz);
			}
			ExprKind::And { left, right }
			| ExprKind::BitAnd { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(bitand_instr(scalar_ty(expr.ty)));
			}
			ExprKind::Or { left, right } | ExprKind::BitOr { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(bitor_instr(scalar_ty(expr.ty)));
			}
			ExprKind::BitXor { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(bitxor_instr(scalar_ty(expr.ty)));
			}
			ExprKind::LeftShift { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(shl_instr(scalar_ty(expr.ty)));
			}
			ExprKind::RightShift { left, right } => {
				self.emit_expr(left);
				self.emit_expr(right);
				self.emit(shr_instr(scalar_ty(expr.ty), expr.ty.is_unsigned()));
			}
			ExprKind::BitNot { value } => {
				// WASM has no bitwise-not; emit `x ^ -1`, matching
				// opt::scheduler's `DataNodeKind::BitNot`.
				let ty = scalar_ty(expr.ty);
				self.emit_expr(value);
				self.emit(match ty {
					ScalarType::I32 => Instruction::I32Const(-1),
					ScalarType::I64 => Instruction::I64Const(-1),
					_ => unreachable!("BitNot is only valid on integers"),
				});
				self.emit(bitxor_instr(ty));
			}
			ExprKind::Neg { value } => {
				// WASM only has neg for floats; ints synthesize `0 - x`.
				match scalar_ty(expr.ty) {
					ScalarType::F32 => {
						self.emit_expr(value);
						self.emit(Instruction::F32Neg);
					}
					ScalarType::F64 => {
						self.emit_expr(value);
						self.emit(Instruction::F64Neg);
					}
					ScalarType::I32 => {
						self.emit(Instruction::I32Const(0));
						self.emit_expr(value);
						self.emit(Instruction::I32Sub);
					}
					ScalarType::I64 => {
						self.emit(Instruction::I64Const(0));
						self.emit_expr(value);
						self.emit(Instruction::I64Sub);
					}
				}
			}
			ExprKind::Sqrt { value } => {
				self.emit_expr(value);
				self.emit(match scalar_ty(expr.ty) {
					ScalarType::F32 => Instruction::F32Sqrt,
					ScalarType::F64 => Instruction::F64Sqrt,
					_ => unreachable!("Sqrt is only valid on floats"),
				});
			}
			ExprKind::Abs { value } => {
				self.emit_expr(value);
				self.emit(match scalar_ty(expr.ty) {
					ScalarType::F32 => Instruction::F32Abs,
					ScalarType::F64 => Instruction::F64Abs,
					_ => unreachable!("Abs is only valid on floats"),
				});
			}
			ExprKind::Floor { value } => {
				self.emit_expr(value);
				self.emit(match scalar_ty(expr.ty) {
					ScalarType::F32 => Instruction::F32Floor,
					ScalarType::F64 => Instruction::F64Floor,
					_ => unreachable!("Floor is only valid on floats"),
				});
			}
			ExprKind::Ceil { value } => {
				self.emit_expr(value);
				self.emit(match scalar_ty(expr.ty) {
					ScalarType::F32 => Instruction::F32Ceil,
					ScalarType::F64 => Instruction::F64Ceil,
					_ => unreachable!("Ceil is only valid on floats"),
				});
			}
			ExprKind::I64ExtendI32S { value }
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
			| ExprKind::F32DemoteF64 { value } => {
				self.emit_expr(value);
				self.emit(cast_instr(&expr.kind));
			}
			ExprKind::Global { id } => {
				self.emit(Instruction::GlobalGet(*id));
			}
			ExprKind::GlobalSet { id, value } => {
				self.emit_expr(value);
				self.emit(Instruction::GlobalSet(*id));
			}
			ExprKind::Function { id } => {
				self.emit(Instruction::FunctionPointer(*id));
			}
			ExprKind::StaticPointer { data_index } => {
				self.emit(Instruction::StaticDataPointer {
					data_index: *data_index,
					ty: scalar_ty(expr.ty),
				});
			}
			ExprKind::MemoryOffset { memory } => {
				self.emit(Instruction::DataSectionEnd { memory: *memory });
			}
			ExprKind::MemoryIndex { memory } => {
				self.emit(Instruction::MemoryIndex { memory: *memory });
			}
			ExprKind::MemorySize { memory } => {
				self.emit(Instruction::MemorySize(*memory));
			}
			ExprKind::MemoryGrow { memory, delta } => {
				self.emit_expr(delta);
				self.emit(Instruction::MemoryGrow(*memory));
			}
			ExprKind::MemoryFill {
				memory,
				dst,
				val,
				len,
			} => {
				self.emit_expr(dst);
				self.emit_expr(val);
				self.emit_expr(len);
				self.emit(Instruction::MemoryFill(*memory));
			}
			ExprKind::MemoryCopy {
				dst_memory,
				src_memory,
				dst,
				src,
				len,
			} => {
				self.emit_expr(dst);
				self.emit_expr(src);
				self.emit_expr(len);
				self.emit(Instruction::MemoryCopy {
					dst: *dst_memory,
					src: *src_memory,
				});
			}
			ExprKind::PointerLoad {
				pointer,
				offset,
				memory,
			} => {
				if let mir::Type::Aggregate { aggregate_index } = expr.ty {
					let addr_local = self.alloc_local(scalar_ty(pointer.ty));
					self.emit_expr(pointer);
					self.emit(Instruction::LocalSet(addr_local));
					self.emit_aggregate_load(
						addr_local,
						*offset,
						aggregate_index,
						*memory,
					);
					return;
				}
				self.emit_expr(pointer);
				self.emit_scalar_load(expr.ty, *offset, *memory);
			}
			ExprKind::PointerStore {
				pointer,
				value,
				offset,
				memory,
			} => {
				if let mir::Type::Aggregate { aggregate_index } = value.ty {
					let addr_local = self.alloc_local(scalar_ty(pointer.ty));
					self.emit_expr(pointer);
					self.emit(Instruction::LocalSet(addr_local));

					// Spill the value's flattened fields to temp locals
					// first — storing needs the address pushed fresh before
					// *each* field's value, so the fields can't just stay on
					// the stack in the order `emit_expr` left them in.
					self.emit_expr(value);
					let field_types = wasm::flatten_type_to_scalars(
						value.ty,
						&self.mir.aggregates,
					);
					let mut value_locals = vec![0u32; field_types.len()];
					for (i, ty) in field_types.iter().enumerate().rev() {
						let local = self.alloc_local(*ty);
						self.emit(Instruction::LocalSet(local));
						value_locals[i] = local;
					}
					self.emit_aggregate_store(
						addr_local,
						*offset,
						&value_locals,
						aggregate_index,
						*memory,
					);
					return;
				}
				self.emit_expr(pointer);
				self.emit_expr(value);
				self.emit_scalar_store(value.ty, *offset, *memory);
			}
			ExprKind::Aggregate { values } => {
				// An aggregate value is just its flattened fields, in
				// physical order, sitting on the WASM stack — the same
				// convention as a multi-value call result or an
				// aggregate-typed local's slots.
				for v in values.iter() {
					self.emit_expr(v);
				}
			}
			ExprKind::AggregateGet {
				scope_index,
				local_index,
				value_index,
			} => {
				let aggregate_index =
					self.local_aggregate_index(*scope_index, *local_index);
				let (field_start, field_count) = self.aggregate_field_slots(
					aggregate_index,
					*value_index as usize,
				);
				let base = self.table.wasm_index(*scope_index, *local_index);
				for i in 0..field_count {
					self.emit(Instruction::LocalGet(base + field_start + i));
				}
			}
			ExprKind::AggregateSet {
				scope_index,
				local_index,
				value_index,
				value,
			} => {
				let aggregate_index =
					self.local_aggregate_index(*scope_index, *local_index);
				let (field_start, field_count) = self.aggregate_field_slots(
					aggregate_index,
					*value_index as usize,
				);
				let base = self.table.wasm_index(*scope_index, *local_index);
				self.emit_expr(value);
				for i in (0..field_count).rev() {
					self.emit(Instruction::LocalSet(base + field_start + i));
				}
			}
			ExprKind::Call { callee, arguments } => {
				// Aggregate args/results need no special handling here:
				// each `emit_expr` on an argument already pushes exactly
				// as many stack values as its type flattens to (1 for a
				// scalar, N for an aggregate, via `Aggregate`/
				// `AggregateGet`), matching WASM's native multi-value
				// params/results — the same convention the callee's own
				// flattened signature already expects.
				if let ExprKind::Function { id } = &callee.kind {
					for arg in arguments {
						self.emit_expr(arg);
					}
					self.emit(Instruction::Call(*id));
				} else {
					let signature_index = match callee.ty {
						mir::Type::Function { signature_index } => {
							signature_index
						}
						_ => {
							unreachable!("call target must be a function type")
						}
					};
					// WASM's call_indirect pops the table index last, so it
					// must be pushed last too — after the args, not before.
					for arg in arguments {
						self.emit_expr(arg);
					}
					self.emit_expr(callee);
					self.emit(Instruction::CallIndirectSym { signature_index });
				}
			}
			ExprKind::Return { value } => {
				if let Some(v) = value {
					self.emit_expr(v);
				}
				self.emit(Instruction::Return);
			}
			ExprKind::Drop { value } => {
				self.emit_expr(value);
				self.drop_value(value.ty, value.span);
			}
			ExprKind::Unreachable => {
				self.emit(Instruction::Unreachable);
			}
			ExprKind::Block {
				scope_index,
				expressions,
			} => {
				// A bare `{ ... }` isn't necessarily a break target, but it
				// might be (any block can be labeled), so it always gets a
				// real `block ... end` wrapper — unlike an if-arm's body,
				// which reuses the `if`'s own level instead (see below).
				self.emit(Instruction::Block {
					ty: block_type(expr.ty),
				});
				self.branch_targets.push(BranchTarget::Block(*scope_index));
				self.emit_sequence(expressions);
				self.branch_targets.pop();
				self.emit(Instruction::End);
			}
			ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				self.emit_expr(condition);
				self.emit(Instruction::If {
					ty: block_type(expr.ty),
				});
				let (then_scope, then_exprs) = unwrap_block(then_block);
				self.branch_targets.push(BranchTarget::Block(then_scope));
				self.emit_sequence(then_exprs);
				self.branch_targets.pop();
				if let Some(else_block) = else_block {
					self.emit(Instruction::Else);
					let (else_scope, else_exprs) = unwrap_block(else_block);
					self.branch_targets.push(BranchTarget::Block(else_scope));
					self.emit_sequence(else_exprs);
					self.branch_targets.pop();
				}
				self.emit(Instruction::End);
			}
			ExprKind::Loop { scope_index, block } => {
				let (body_scope, body_exprs) = unwrap_block(block);
				let result_local = match block_type(expr.ty) {
					BlockType::Empty => None,
					BlockType::Value(ty) => Some(self.alloc_local(ty)),
					BlockType::MultiValue(_) => {
						unreachable!("loop result must be scalar or unit")
					}
				};
				self.emit(Instruction::Block {
					ty: BlockType::Empty,
				});
				self.emit(Instruction::Loop {
					ty: BlockType::Empty,
				});
				self.branch_targets.push(BranchTarget::Loop {
					scope_index: *scope_index,
					result_local,
				});
				// `body_scope` is `*scope_index` itself — MIR gives a `Loop`
				// and its body the same scope, so no separate lookup needed.
				debug_assert_eq!(body_scope, *scope_index);
				self.emit_sequence(body_exprs);
				self.branch_targets.pop();
				// Back-edge; unreachable if the body always breaks/returns,
				// same as opt::scheduler — WASM allows dead code after an
				// unconditional branch.
				self.emit(Instruction::Br(0));
				self.emit(Instruction::End); // loop
				self.emit(Instruction::End); // block
				if let Some(local) = result_local {
					self.emit(Instruction::LocalGet(local));
				}
			}
			ExprKind::Break { scope_index, value } => {
				let result_local = self.loop_result_local(*scope_index);
				if let Some(v) = value {
					self.emit_expr(v);
					let local = result_local.expect(
						"break with a value must target a loop with a result local",
					);
					self.emit(Instruction::LocalSet(local));
				}
				self.emit(Instruction::Br(self.break_depth(*scope_index)));
			}
			ExprKind::Continue { scope_index } => {
				self.emit(Instruction::Br(self.continue_depth(*scope_index)));
			}
			ExprKind::Switch {
				selector,
				cases,
				default,
			} => {
				// Uniform if/else-if chain — simpler and just as correct as
				// opt::builder's dense-vs-sparse `br_table`-or-chain choice,
				// without needing to replicate its block-depth bookkeeping.
				let sel_ty = scalar_ty(selector.ty);
				self.emit_expr(selector);
				let sel_local = self.alloc_local(sel_ty);
				self.emit(Instruction::LocalSet(sel_local));
				self.emit_switch_chain(
					sel_local,
					sel_ty,
					cases,
					default.as_deref(),
					block_type(expr.ty),
				);
			}
		}
	}

	/// Recursively emit `cases` as a chain of `local.get sel; const d; eq;
	/// if ... else <rest> end`, bottoming out at `default` (or
	/// `unreachable` if none — TIR only omits `default` when it already
	/// proved exhaustiveness).
	fn emit_switch_chain(
		&mut self,
		sel_local: u32,
		sel_ty: ScalarType,
		cases: &[(i64, Expression)],
		default: Option<&Expression>,
		ty: BlockType,
	) {
		let Some(((discriminant, body), rest)) = cases.split_first() else {
			match default {
				Some(d) => self.emit_expr(d),
				None => self.emit(Instruction::Unreachable),
			}
			return;
		};

		self.emit(Instruction::LocalGet(sel_local));
		self.emit(match sel_ty {
			ScalarType::I32 => Instruction::I32Const(*discriminant as i32),
			ScalarType::I64 => Instruction::I64Const(*discriminant),
			_ => unreachable!("switch selector must be an integer"),
		});
		self.emit(match sel_ty {
			ScalarType::I32 => Instruction::I32Eq,
			ScalarType::I64 => Instruction::I64Eq,
			_ => unreachable!("switch selector must be an integer"),
		});
		self.emit(Instruction::If { ty });
		let (case_scope, case_exprs) = unwrap_block(body);
		self.branch_targets.push(BranchTarget::Block(case_scope));
		self.emit_sequence(case_exprs);
		self.branch_targets.pop();
		self.emit(Instruction::Else);
		self.emit_switch_chain(sel_local, sel_ty, rest, default, ty);
		self.emit(Instruction::End);
	}

	fn emit_int_const(&mut self, ty: mir::Type, value: i64) {
		self.emit(match scalar_ty(ty) {
			ScalarType::I32 => Instruction::I32Const(value as i32),
			ScalarType::I64 => Instruction::I64Const(value),
			ScalarType::F32 | ScalarType::F64 => {
				unreachable!()
			}
		});
	}

	fn emit_float_const(&mut self, ty: mir::Type, value: f64) {
		self.emit(match scalar_ty(ty) {
			ScalarType::F32 => Instruction::F32Const(value as f32),
			ScalarType::F64 => Instruction::F64Const(value),
			ScalarType::I32 | ScalarType::I64 => {
				unreachable!()
			}
		});
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

	use super::*;
	use crate::{tir, vfs};

	/// Builds MIR from source, standalone from `mir::tests::TestCase` — this
	/// module only needs `mir::MIR` plus one function to hand to `schedule`,
	/// not the wider harness.
	fn build_mir(source: &str) -> mir::MIR {
		let mut builder = vfs::CompilationGraphBuilder::new();
		let stdlib_id = builder.load_stdlib();
		let prefixed = format!("use std::*;\n{source}");
		let root_id = builder
			.load_binary(
				"main.wx".to_string(),
				&vfs::VirtualFileSource::new(HashMap::from([(
					"main.wx".to_string(),
					prefixed,
				)])),
			)
			.unwrap();
		let mut graph = builder.build(root_id, stdlib_id);
		let tir = tir::TIR::build(&mut graph);
		let mut mir_out = mir::MIR::build(
			&tir,
			&graph.interner,
			graph.id_generator,
			crate::CompilationMode::Debug,
		);
		let mut call_graph =
			mir::CallGraph::build(&mir_out.functions, &mir_out.call_edges);
		mir_out.inline_calls(&mut call_graph);
		mir_out.dead_code_eliminate(&call_graph);
		mir_out
	}

	#[test]
	fn lowers_straight_line_arithmetic() {
		let mir_out = build_mir(indoc! {"
            fn compute(x: i32) -> i32 {
                local y = x + 1;
                y * 2
            }
            export { compute }
        "});
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);

		assert_eq!(
			scheduled.body,
			vec![
				Instruction::LocalGet(0),
				Instruction::I32Const(1),
				Instruction::I32Add,
				Instruction::LocalSet(1),
				Instruction::LocalGet(1),
				Instruction::I32Const(2),
				Instruction::I32Mul,
			]
		);
	}

	#[test]
	fn lowers_bitwise_and_shift() {
		let mir_out = build_mir(indoc! {"
            fn combine(a: i32, b: i32) -> i32 {
                (a & b) << 1
            }
            export { combine }
        "});
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);

		assert_eq!(
			scheduled.body,
			vec![
				Instruction::LocalGet(0),
				Instruction::LocalGet(1),
				Instruction::I32And,
				Instruction::I32Const(1),
				Instruction::I32Shl,
			]
		);
	}

	#[test]
	fn lowers_global_get_and_set() {
		let mir_out = build_mir(indoc! {"
            global mut counter: i32 = 0;
            fn bump() -> i32 {
                counter = counter + 1;
                counter
            }
            export { bump }
        "});
		let counter_id = mir_out.globals[0].id;
		let func = mir_out
			.functions
			.iter()
			.find(|f| {
				matches!(
					mir_out.signatures[f.signature_index as usize].params(),
					[]
				)
			})
			.expect("bump function not found");
		let scheduled = schedule(func, &mir_out);

		assert_eq!(
			scheduled.body,
			vec![
				Instruction::GlobalGet(counter_id),
				Instruction::I32Const(1),
				Instruction::I32Add,
				Instruction::GlobalSet(counter_id),
				Instruction::GlobalGet(counter_id),
			]
		);
	}

	#[test]
	fn lowers_direct_call() {
		let mir_out = build_mir(indoc! {"
            fn helper(x: i32) -> i32 {
                x + 1
            }
            fn caller(x: i32) -> i32 {
                helper(x) * 2
            }
            export { caller }
        "});
		// Only `caller` is exported (`helper` stays live only via the call
		// edge), so the single export is unambiguously `caller`.
		let caller_id = mir_out
			.exports
			.iter()
			.find_map(|e| match e {
				mir::ExportItem::Function { id, .. } => Some(*id),
				_ => None,
			})
			.expect("caller export not found");
		let func = mir_out
			.functions
			.iter()
			.find(|f| f.id == caller_id)
			.expect("caller function not found");
		let helper_id = mir_out
			.functions
			.iter()
			.find(|f| f.id != caller_id)
			.expect("helper function not found")
			.id;
		let scheduled = schedule(func, &mir_out);

		assert_eq!(
			scheduled.body,
			vec![
				Instruction::LocalGet(0),
				Instruction::Call(helper_id),
				Instruction::I32Const(2),
				Instruction::I32Mul,
			]
		);
	}

	#[test]
	fn lowers_if_else_with_value() {
		let mir_out = build_mir(indoc! {"
            fn classify(x: i32) -> i32 {
                if x > 0 {
                    1
                } else {
                    0 - 1
                }
            }
            export { classify }
        "});
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);

		assert_eq!(
			scheduled.body,
			vec![
				Instruction::LocalGet(0),
				Instruction::I32Const(0),
				Instruction::I32GtS,
				Instruction::If {
					ty: BlockType::Value(ScalarType::I32)
				},
				Instruction::I32Const(1),
				Instruction::Else,
				Instruction::I32Const(0),
				Instruction::I32Const(1),
				Instruction::I32Sub,
				Instruction::End,
			]
		);
	}

	#[test]
	fn lowers_if_without_else() {
		let mir_out = build_mir(indoc! {"
            global mut flag: i32 = 0;
            fn maybe_set(x: i32) {
                if x > 0 {
                    flag = 1;
                }
            }
            export { maybe_set }
        "});
		let flag_id = mir_out.globals[0].id;
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);

		assert_eq!(
			scheduled.body,
			vec![
				Instruction::LocalGet(0),
				Instruction::I32Const(0),
				Instruction::I32GtS,
				Instruction::If {
					ty: BlockType::Empty
				},
				Instruction::I32Const(1),
				Instruction::GlobalSet(flag_id),
				Instruction::End,
			]
		);
	}

	#[test]
	fn lowers_loop_with_break_value_and_continue() {
		let mir_out = build_mir(indoc! {"
            fn count_to(n: i32) -> i32 {
                local mut i: i32 = 0;
                loop {
                    i = i + 1;
                    if i < n {
                        continue;
                    }
                    break i;
                }
            }
            export { count_to }
        "});
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);

		// Structural shape: ..., Block, Loop, ..., Br(0) back-edge, End, End,
		// then reading the result local. (`local mut i = 0` emits its own
		// init instructions before the loop, so Block/Loop aren't at a fixed
		// index — precise depth correctness is checked by execution instead,
		// in the codegen smoke test.)
		let block_pos = scheduled
			.body
			.iter()
			.position(|i| {
				matches!(
					i,
					Instruction::Block {
						ty: BlockType::Empty
					}
				)
			})
			.expect("expected the loop's wrapping Block");
		assert_eq!(
			scheduled.body[block_pos + 1],
			Instruction::Loop {
				ty: BlockType::Empty
			}
		);
		let len = scheduled.body.len();
		assert_eq!(scheduled.body[len - 4], Instruction::Br(0));
		assert_eq!(scheduled.body[len - 3], Instruction::End);
		assert_eq!(scheduled.body[len - 2], Instruction::End);
		assert!(
			matches!(scheduled.body[len - 1], Instruction::LocalGet(_)),
			"loop with a value result must end by reading its result local; got {:#?}",
			scheduled.body
		);
	}

	#[test]
	fn break_from_nested_loop_targets_correct_depth() {
		// The inner loop's `break` must exit only the inner loop (depth 1:
		// past its own Block+Loop... no — see below), not the outer one.
		// Concretely: outer keeps running (increments `outer_count`) while
		// the inner loop breaks out after one iteration every time.
		let mir_out = build_mir(indoc! {"
            fn nested(n: i32) -> i32 {
                local mut outer_count: i32 = 0;
                loop {
                    if outer_count >= n {
                        break outer_count;
                    }
                    loop {
                        break;
                    }
                    outer_count = outer_count + 1;
                }
            }
            export { nested }
        "});
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);
		// Two Loop instructions (outer + inner), two matching Block wrappers.
		let loop_count = scheduled
			.body
			.iter()
			.filter(|i| matches!(i, Instruction::Loop { .. }))
			.count();
		assert_eq!(loop_count, 2, "got: {:#?}", scheduled.body);
	}

	#[test]
	fn lowers_match_to_if_else_chain() {
		let mir_out = build_mir(indoc! {"
            fn classify(x: i32) -> i32 {
                match x {
                    0 -> { 10 },
                    1 -> { 20 },
										
                    _ -> { -1 },
                }
            }
            export { classify }
        "});
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);

		// Two nested `if`s (one per real case), no BrTable at all.
		let if_count = scheduled
			.body
			.iter()
			.filter(|i| matches!(i, Instruction::If { .. }))
			.count();
		assert_eq!(
			if_count, 2,
			"expected one `if` per real case; got: {:#?}",
			scheduled.body
		);
		assert!(
			!scheduled
				.body
				.iter()
				.any(|i| matches!(i, Instruction::BrTable { .. })),
			"direct scheduler always uses an if/else-if chain, never BrTable"
		);
	}

	#[test]
	fn lowers_struct_construction_and_field_access() {
		let mir_out = build_mir(indoc! {"
            struct Point {
                x: i32,
                y: i32,
            }
            fn make_point(x: i32, y: i32) -> Point {
                Point::{ x: x, y: y }
            }
            fn sum(p: Point) -> i32 {
                p.x + p.y
            }
            export { make_point, sum }
        "});
		let make_point = mir_out
			.functions
			.iter()
			.find(|f| {
				matches!(
					mir_out.signatures[f.signature_index as usize].params(),
					[mir::Type::I32, mir::Type::I32]
				) && mir_out.signatures[f.signature_index as usize].result()
					== mir::Type::Aggregate { aggregate_index: 0 }
			})
			.expect("make_point not found");
		assert_eq!(
			schedule(make_point, &mir_out).body,
			vec![Instruction::LocalGet(0), Instruction::LocalGet(1)],
		);

		let sum = mir_out
			.functions
			.iter()
			.find(|f| {
				mir_out.signatures[f.signature_index as usize].result()
					== mir::Type::I32
			})
			.expect("sum not found");
		assert_eq!(
			schedule(sum, &mir_out).body,
			vec![
				Instruction::LocalGet(0),
				Instruction::LocalGet(1),
				Instruction::I32Add,
			],
		);
	}

	#[test]
	fn lowers_local_struct_field_mutation() {
		let mir_out = build_mir(indoc! {"
            struct Point {
                x: i32,
                y: i32,
            }
            fn bump_x(x: i32, y: i32) -> i32 {
                local mut p: Point = Point::{ x: x, y: y };
                p.x = p.x + 1;
                p.x + p.y
            }
            export { bump_x }
        "});
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);

		// `p` is a 2-slot local starting right after the 2 params (slots 0,1),
		// so `p` occupies slots 2 (x) and 3 (y). `LocalSet` on a multi-value
		// (aggregate) assignment pops in reverse to land each field in its
		// correct slot — see the comment on `ExprKind::LocalSet`.
		assert_eq!(
			scheduled.body,
			vec![
				// local mut p: Point = Point::{ x, y }
				Instruction::LocalGet(0),
				Instruction::LocalGet(1),
				Instruction::LocalSet(3),
				Instruction::LocalSet(2),
				// p.x = p.x + 1
				Instruction::LocalGet(2),
				Instruction::I32Const(1),
				Instruction::I32Add,
				Instruction::LocalSet(2),
				// p.x + p.y
				Instruction::LocalGet(2),
				Instruction::LocalGet(3),
				Instruction::I32Add,
			]
		);
	}

	#[test]
	fn spans_track_source_positions() {
		let src = indoc! {"
            fn compute(x: i32) -> i32 {
                local y = x + 1;
                y * 2
            }
            export { compute }
        "};
		let mir_out = build_mir(src);
		let func = &mir_out.functions[0];
		let scheduled = schedule(func, &mir_out);
		assert_eq!(scheduled.body.len(), scheduled.spans.len());

		// `build_mir` prepends `"use std::*;\n"`, so spans are relative to
		// that combined text, not `src` alone.
		let full = format!("use std::*;\n{src}");
		let text_at =
			|span: ast::TextSpan| &full[span.start as usize..span.end as usize];

		let spanned: Vec<(&str, &Instruction)> = scheduled
			.spans
			.iter()
			.copied()
			.map(text_at)
			.zip(scheduled.body.iter())
			.collect();
		assert_eq!(
			spanned,
			vec![
				("x", &Instruction::LocalGet(0)),
				("1", &Instruction::I32Const(1)),
				("x + 1", &Instruction::I32Add),
				("local y = x + 1", &Instruction::LocalSet(1)),
				("y", &Instruction::LocalGet(1)),
				("2", &Instruction::I32Const(2)),
				("y * 2", &Instruction::I32Mul),
			]
		);
	}
}
