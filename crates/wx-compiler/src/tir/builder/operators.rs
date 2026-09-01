//! Operator overloading, end to end: resolving the stdlib `Add`/`Sub`/...
//! traits an operator dispatches through, and building every expression that
//! dispatches through one — binary and unary arithmetic, bitwise, comparison,
//! logical, assignment and compound assignment.

use super::*;

/// Whether the expression tree currently being built will actually be
/// lowered to MIR and executed (`Runtime`), or is purely interpreted at
/// compile time by `eval_const_expr` and then discarded — only the
/// resulting literal value survives, inlined at every reference site
/// (`const` declarations, enum discriminants: both resolved in
/// `ensure_signature`/Phase 2, since other signatures can depend on the
/// value). `Runtime` covers regular function bodies *and* `global`
/// initializers — both resolved in `ensure_body`/Phase 3, since globals are
/// genuine mutable state initialized by a real synthesized `start` function
/// (`mir::MIR::build_start_function`), not folded away.
///
/// This is what operator dispatch (`Builder::build_operator_dispatch`) gates
/// on: dispatching `+` to a real `Add::add` call is only worth doing for
/// trees that will actually run — a `Comptime` tree never reaches MIR, so
/// `build_arithmetic_expr` builds a plain `Binary` node for it instead,
/// exactly as before operator overloading existed, keeping it directly
/// foldable by `eval_const_expr`'s existing arithmetic arm.
pub(super) enum EvalMode {
	Runtime(OperatorTraits),
	Comptime,
}

/// `Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg` — the fixed set of operator-overload
/// traits binary/unary arithmetic expressions dispatch through. Resolved
/// once, right after Phase 2 (every item's signature, including
/// `std/main.wx`'s `#[tag = "add"]`-style attributes, is available by then —
/// a missing tag is a stdlib/compiler bug, not a per-expression condition),
/// so checking a `+`/`-`/... never touches the interner or `tagged_items` on
/// the hot path. Lives on `Builder`, not `TIR`: nothing outside `TIR::build`
/// needs this mapping — every operator is already resolved to a concrete
/// `ExprKind::MethodCall` by the time `TIR::build` returns.
///
/// Covers arithmetic (`Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg`) and bitwise
/// (`BitAnd`/`BitOr`/`BitXor`/`Shl`/`Shr`/`BitNot`) operators alike — every
/// binary family dispatches through `for_op`/`build_operator_dispatch`, and
/// both unary members (`Neg`, `BitNot`) through `for_unary_op`/
/// `build_unary_operator_dispatch`.
#[derive(Clone)]
pub(super) struct OperatorTraits {
	add: (TraitIndex, SymbolU32),
	sub: (TraitIndex, SymbolU32),
	mul: (TraitIndex, SymbolU32),
	div: (TraitIndex, SymbolU32),
	rem: (TraitIndex, SymbolU32),
	neg: (TraitIndex, SymbolU32),
	bitand: (TraitIndex, SymbolU32),
	bitor: (TraitIndex, SymbolU32),
	bitxor: (TraitIndex, SymbolU32),
	shl: (TraitIndex, SymbolU32),
	shr: (TraitIndex, SymbolU32),
	bitnot: (TraitIndex, SymbolU32),
}

impl OperatorTraits {
	/// Maps an arithmetic or bitwise `BinaryOp` to its `(TraitIndex,
	/// SymbolU32)` entry — the lookup every such operator-dispatch path
	/// needs, factored out so it's defined once. `None` for an operator with
	/// no overload trait (comparisons, logical, assignment).
	pub(super) fn for_op(
		&self,
		op: BinaryOp,
	) -> Option<(TraitIndex, SymbolU32)> {
		Some(match op {
			BinaryOp::Add => self.add,
			BinaryOp::Sub => self.sub,
			BinaryOp::Mul => self.mul,
			BinaryOp::Div => self.div,
			BinaryOp::Rem => self.rem,
			BinaryOp::BitAnd => self.bitand,
			BinaryOp::BitOr => self.bitor,
			BinaryOp::BitXor => self.bitxor,
			BinaryOp::LeftShift => self.shl,
			BinaryOp::RightShift => self.shr,
			_ => return None,
		})
	}

	/// Unary counterpart of `for_op`, for `-x` (`Neg`) and `^x` (`BitNot`).
	/// `None` for an operator with no overload trait (`!x`, bool-only).
	pub(super) fn for_unary_op(
		&self,
		op: ast::UnaryOp,
	) -> Option<(TraitIndex, SymbolU32)> {
		Some(match op {
			ast::UnaryOp::InvertSign => self.neg,
			ast::UnaryOp::BitNot => self.bitnot,
			ast::UnaryOp::Not => return None,
		})
	}
}

/// What `Builder::resolve_compound_operator` resolved `x op= y` to for a
/// given target. Mirrors the split between `MethodCall` and
/// `GenericMethodCall`: `Concrete` when `find_trait_impl` already resolved a
/// real impl for the target's (already concrete) type, `Generic` when the
/// target's type is still abstract (a bare `TypeParam` or a typeset-bounded
/// `AssocTypeProjection`) and resolution has to wait for monomorphization,
/// exactly like `GenericMethodCall`'s abstract-method branch.
enum CompoundOperatorDispatch {
	Concrete(ast::DefId),
	Generic { abstract_method_id: ast::DefId },
}

impl<'ast> Builder<'ast, '_> {
	/// Resolves one `#[tag = "..."]`-marked stdlib trait to its `TraitIndex`
	/// plus its single method's name symbol. Panics on failure — by the time
	/// this runs (right after Phase 2), `std/main.wx` is fully signature-checked,
	/// so a missing tag is a stdlib/compiler bug, not a recoverable condition.
	fn resolve_operator_trait(&self, tag: &str) -> (TraitIndex, SymbolU32) {
		let symbol = self
			.interner
			.get(tag)
			.unwrap_or_else(|| panic!("stdlib missing `{tag}` symbol"));
		let def_id =
			*self.items.tagged_items.get(&symbol).unwrap_or_else(|| {
				panic!("stdlib missing #[tag = \"{tag}\"] item")
			});
		(self.items.expect_trait_index(def_id), symbol)
	}

	pub(super) fn resolve_operator_traits(&self) -> OperatorTraits {
		OperatorTraits {
			add: self.resolve_operator_trait("add"),
			sub: self.resolve_operator_trait("sub"),
			mul: self.resolve_operator_trait("mul"),
			div: self.resolve_operator_trait("div"),
			rem: self.resolve_operator_trait("rem"),
			neg: self.resolve_operator_trait("neg"),
			bitand: self.resolve_operator_trait("bitand"),
			bitor: self.resolve_operator_trait("bitor"),
			bitxor: self.resolve_operator_trait("bitxor"),
			shl: self.resolve_operator_trait("shl"),
			shr: self.resolve_operator_trait("shr"),
			bitnot: self.resolve_operator_trait("bitnot"),
		}
	}

	/// Pure lookup: resolves `ty`'s method for the trait tagged `trait_index`
	/// under member name `method_symbol`. No side effects, no `EvalMode`
	/// awareness — callers only call this once they already know evaluation
	/// mode is `Runtime` (see `build_operator_dispatch`), and decide for
	/// themselves what a `None` means (a struct with no `Add` impl is a real
	/// error; a typeset-bounded associated type, which `find_trait_impl` can
	/// never match since it has no concrete `ImplTarget`, is not — see
	/// `is_typeset_bounded_assoc_type`). Shared by binary
	/// (`build_operator_dispatch`), unary (`Neg`), and the
	/// `Type::TypeParam` compound-assignment dispatch.
	pub(super) fn resolve_trait_method(
		&self,
		trait_index: TraitIndex,
		method_symbol: SymbolU32,
		ty: TypeIndex,
	) -> Option<FunctionIndex> {
		let (impl_idx, _type_args) =
			self.items.find_trait_impl(&self.types, ty, trait_index)?;
		match self.items.trait_impls[usize::from(impl_idx)]
			.members
			.get(&method_symbol)?
		{
			ImplEntry::Method(func_idx) => Some(*func_idx),
			_ => None,
		}
	}

	/// The operator trait's own declared method for `method_symbol` — every
	/// operator trait declares exactly one, so this never legitimately
	/// misses. Shared by every "trust it, don't check the concrete type"
	/// path: a typeset-bounded type param or associated type (`T: Size`,
	/// `Mem::Size`) both resolve to this the same way, since neither is a
	/// concrete `ImplTarget` `resolve_trait_method` could look up.
	fn operator_trait_method(
		&self,
		trait_index: TraitIndex,
		method_symbol: SymbolU32,
	) -> FunctionIndex {
		match self.items.traits[usize::from(trait_index)]
			.entries
			.get(&method_symbol)
		{
			Some(ImplEntry::Method(idx)) => *idx,
			_ => unreachable!("operator trait must declare its own method"),
		}
	}

	/// The `Type::TypeParam` counterpart of `resolve_trait_method` — which
	/// only ever resolves a concrete `ImplTarget`, so it fails outright for
	/// a type param (`ImplTarget::from_type` doesn't handle `TypeParam`).
	/// Checks the type param's own declared bounds instead: `None` means
	/// neither bound applies — a genuinely unbounded `T` — and the caller
	/// should fall through to the ordinary concrete-resolution path, which
	/// reports the same "operator cannot be applied" diagnostic either way.
	///
	/// Two independent ways a type param can be "bounded enough" for this:
	/// - A real trait bound matching this operator's own trait (`T: Add`
	///   for `+`) — could concretize to any type implementing that trait,
	///   not just a primitive, so resolution stays deferred.
	/// - A typeset bound (`T: Size`) — every typeset today consists
	///   entirely of integer primitives (enforced at typeset-declaration
	///   time, `DiagnosticCode::TypesetMemberNotInteger`), which all carry
	///   `#[inline]` impls of every operator trait, so it's trusted
	///   unconditionally for *any* operator trait here, exactly like
	///   `Type::AssocTypeProjection`'s equivalent trust (see
	///   `is_typeset_bounded_assoc_type`) — no need to check which trait
	///   `T` was bounded by.
	///
	/// `Some` returns the trait's *abstract* method (no body — resolved for
	/// real once monomorphization substitutes a concrete `Self`, exactly
	/// like `GenericMethodCall`'s existing abstract-method fallback).
	fn resolve_bounded_operator_method(
		&self,
		owner: TypeParamOwner,
		param_index: u32,
		trait_index: TraitIndex,
		method_symbol: SymbolU32,
	) -> Option<FunctionIndex> {
		let bounds = &self
			.items
			.type_param_info(owner, param_index as usize)
			.bounds;
		let bounded = bounds.typeset.is_some()
			|| bounds.traits.iter().any(|tb| tb.trait_index == trait_index);
		if !bounded {
			return None;
		}
		Some(self.operator_trait_method(trait_index, method_symbol))
	}

	/// Resolves `operator` for `ty` in `ctx`'s evaluation mode and builds the
	/// resulting expression:
	/// - `Comptime` never attempts dispatch at all (see `EvalMode`'s doc
	///   comment) — builds a plain `Binary` node, exactly as before operator
	///   overloading existed, still directly foldable by `eval_const_expr`.
	/// - `Runtime`, `ty` isn't concrete yet (`Type::TypeParam` or
	///   `Type::AssocTypeProjection`) but is trusted anyway — a real trait
	///   bound, or a typeset bound on either shape (see
	///   `resolve_bounded_operator_method`/`is_typeset_bounded_assoc_type`)
	///   — builds a `GenericMethodCall`, deferred to real resolution once
	///   monomorphization substitutes a concrete `Self`.
	/// - `Runtime`, dispatch succeeds against a concrete type — records
	///   `operator`'s own span as a go-to-definition access against the
	///   resolved method (the same `accesses`-list mechanism ordinary
	///   method calls use) and builds a `MethodCall`.
	/// - `Runtime`, dispatch fails — reports "operator cannot be applied".
	fn build_operator_dispatch(
		&mut self,
		ctx: &ExprContext,
		operator: Spanned<ast::BinaryOp>,
		left: Expression,
		right: Expression,
		ty: TypeIndex,
		span: ast::TextSpan,
	) -> Expression {
		let binary_op = Spanned {
			inner: BinaryOp::from(operator.inner),
			span: operator.span,
		};
		let EvalMode::Runtime(traits) = &ctx.mode else {
			return Expression {
				kind: ExprKind::Binary {
					operator: binary_op,
					left: Box::new(left),
					right: Box::new(right),
				},
				ty,
				span,
			};
		};

		if let Some((trait_index, method_symbol)) =
			traits.for_op(binary_op.inner)
		{
			let deferred = match self.types.resolve(ty) {
				Type::TypeParam { owner, param_index } => self
					.resolve_bounded_operator_method(
						*owner,
						*param_index,
						trait_index,
						method_symbol,
					),
				Type::AssocTypeProjection { .. }
					if self.is_typeset_bounded_assoc_type(ty) =>
				{
					Some(self.operator_trait_method(trait_index, method_symbol))
				}
				_ => None,
			};
			if let Some(func_idx) = deferred {
				self.items.functions[usize::from(func_idx)].accesses.push(
					SourceSpan::new(ctx.resolve_context.file_id, operator.span),
				);
				let abstract_method_id =
					self.items.functions[usize::from(func_idx)].id;
				return Expression {
					kind: ExprKind::GenericMethodCall {
						id: abstract_method_id,
						type_args: Box::new([ty]),
						arguments: Box::new([left, right]),
					},
					ty,
					span,
				};
			}
		}

		let method = traits.for_op(binary_op.inner).and_then(
			|(trait_index, method_symbol)| {
				self.resolve_trait_method(trait_index, method_symbol, ty)
			},
		);
		match method {
			Some(func_idx) => {
				self.items.functions[usize::from(func_idx)].accesses.push(
					SourceSpan::new(ctx.resolve_context.file_id, operator.span),
				);
				let method_id = self.items.functions[usize::from(func_idx)].id;
				Expression {
					kind: ExprKind::MethodCall {
						arguments: Box::new([left, right]),
						id: method_id,
					},
					ty,
					span,
				}
			}
			None => {
				self.diagnostics.push(
					report_binary_operator_cannot_be_applied(
						self.formatter(ctx.resolve_context.namespace),
						BinaryOperatorCannotBeAppliedDiagnostic {
							file_id: ctx.resolve_context.file_id,
							operator,
							operand: Spanned { inner: ty, span },
						},
					),
				);
				Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::ERROR,
					span,
				}
			}
		}
	}

	/// Shared by `build_bitwise_binary_expr`'s same-type arm once `ty` is a
	/// fully concrete type both operands agree on. Concrete integers/`bool`
	/// stay on the plain `Binary` path unconditionally — that's the
	/// pre-existing native codegen for bitwise ops on primitives, and it's
	/// deliberately left untouched (no snapshot churn, no new intrinsics
	/// needed for the concrete-primitive case). Everything else (a struct,
	/// a typeset-bounded `Type::TypeParam`/`Type::AssocTypeProjection`, or a
	/// bare `Type::TypeParam` bounded by one of the bitwise traits) goes
	/// through real dispatch via `build_operator_dispatch`, which already
	/// reports "operator cannot be applied" on its own if nothing
	/// implements it.
	fn build_bitwise_result(
		&mut self,
		ctx: &ExprContext,
		operator: Spanned<ast::BinaryOp>,
		left: Expression,
		right: Expression,
		ty: TypeIndex,
		span: ast::TextSpan,
	) -> Expression {
		if ty.is_integer() || ty == TypeIndex::BOOL {
			Expression {
				kind: ExprKind::Binary {
					operator: Spanned {
						inner: BinaryOp::from(operator.inner),
						span: operator.span,
					},
					left: Box::new(left),
					right: Box::new(right),
				},
				ty,
				span,
			}
		} else {
			self.build_operator_dispatch(ctx, operator, left, right, ty, span)
		}
	}

	/// Resolves what a compound-assignment operator (`+=` and friends)
	/// dispatches to for `ty`, for building `CompoundAssign`/`CompoundStore`
	/// (`Concrete`) or `GenericCompoundAssign`/`GenericCompoundStore`
	/// (`Generic`) — the compound-assignment analogue of
	/// `build_operator_dispatch`, except it never builds an `Expression`
	/// itself, since compound assignment needs `target` built exactly once
	/// (see the four compound-assignment nodes' doc comments in `tir/mod.rs`),
	/// not duplicated the way a `MethodCall`'s `arguments[0]` would require.
	///
	/// `operator` is the plain form (`Add`, not `AddAssign`) — same
	/// convention as `ExprKind::CompoundAssign`'s doc comment: the `*Assign`
	/// form is only needed for `BinaryExpressionMistmatchDiagnostic`'s own
	/// dedicated wording, kept separately by callers.
	///
	/// `Err(())` means a real, already-diagnosed failure — `ty` is concrete
	/// and genuinely has no matching impl. There is no benign `None` case
	/// left to worry about: typeset-bounded and generic-not-yet-concrete
	/// both fall into `Generic` now (see the design doc's "same category"
	/// insight), and `EvalMode::Comptime` never reaches this function at all
	/// (compound assignment is always inside a function body or `global`
	/// initializer).
	fn resolve_compound_operator(
		&mut self,
		ctx: &ExprContext,
		operator: Spanned<ast::BinaryOp>,
		ty: TypeIndex,
		operand_span: ast::TextSpan,
	) -> Result<CompoundOperatorDispatch, ()> {
		let EvalMode::Runtime(traits) = &ctx.mode else {
			unreachable!(
				"compound assignment is always inside a function body or \
				 global initializer, never a const/enum-discriminant context"
			);
		};
		let (trait_index, method_symbol) = traits
			.for_op(BinaryOp::from(operator.inner))
			.unwrap_or_else(|| {
				unreachable!(
					"resolve_compound_operator only takes the plain form"
				)
			});

		// Typeset-bounded associated types (`Mem::Size`) always defer — their
		// members are all primitives today (see `is_typeset_bounded_assoc_type`),
		// so there's no separate trait bound to check. A bare `Type::TypeParam`
		// is different: it could concretize to any type, so it only defers
		// when actually bounded by this operator's trait — an unbounded `T`
		// falls through to the failure path below instead of building a
		// `GenericCompoundAssign`/`GenericCompoundStore` that would only fail
		// later, as a raw panic once monomorphization substitutes some
		// concrete, non-implementing type.
		let abstract_func_idx = match self.types.resolve(ty) {
			Type::AssocTypeProjection { .. } => {
				Some(self.operator_trait_method(trait_index, method_symbol))
			}
			Type::TypeParam { owner, param_index } => self
				.resolve_bounded_operator_method(
					*owner,
					*param_index,
					trait_index,
					method_symbol,
				),
			_ => None,
		};
		if let Some(abstract_func_idx) = abstract_func_idx {
			self.items.functions[usize::from(abstract_func_idx)]
				.accesses
				.push(SourceSpan::new(
					ctx.resolve_context.file_id,
					operator.span,
				));
			return Ok(CompoundOperatorDispatch::Generic {
				abstract_method_id: self.items.functions
					[usize::from(abstract_func_idx)]
				.id,
			});
		}

		match self.resolve_trait_method(trait_index, method_symbol, ty) {
			Some(func_idx) => {
				self.items.functions[usize::from(func_idx)].accesses.push(
					SourceSpan::new(ctx.resolve_context.file_id, operator.span),
				);
				Ok(CompoundOperatorDispatch::Concrete(
					self.items.functions[usize::from(func_idx)].id,
				))
			}
			None => {
				self.diagnostics.push(
					report_binary_operator_cannot_be_applied(
						self.formatter(ctx.resolve_context.namespace),
						BinaryOperatorCannotBeAppliedDiagnostic {
							file_id: ctx.resolve_context.file_id,
							operator,
							operand: Spanned {
								inner: ty,
								span: operand_span,
							},
						},
					),
				);
				Err(())
			}
		}
	}

	/// Unary counterpart of `build_operator_dispatch`, for `-x` (`Neg`) and
	/// `^x` (`BitNot`) — `EvalMode` gating, go-to-definition access
	/// recording, and diagnostic-on-failure all mirror the binary case
	/// exactly, just with one operand instead of two. Callers only ever
	/// pass an `operator` `for_unary_op` recognizes (`InvertSign`/
	/// `BitNot`) — `!x` (`Not`) is bool-only and never reaches here.
	///
	/// TODO: revisit whether this and `build_operator_dispatch` can share
	/// more than `resolve_trait_method` — the binary/unary duplication here
	/// is mostly `Box::new([left, right])` vs. `Box::new([operand])` and
	/// `ExprKind::Binary` vs. `ExprKind::Unary`, which might collapse with a
	/// small enum over "1 or 2 operands" if a third unary/binary trait op is
	/// ever added.
	fn build_unary_operator_dispatch(
		&mut self,
		ctx: &ExprContext,
		operator: Spanned<ast::UnaryOp>,
		operand: Expression,
		ty: TypeIndex,
		span: ast::TextSpan,
	) -> Expression {
		let EvalMode::Runtime(traits) = &ctx.mode else {
			return Expression {
				kind: ExprKind::Unary {
					operator,
					operand: Box::new(operand),
				},
				ty,
				span,
			};
		};
		let Some((trait_index, method_symbol)) =
			traits.for_unary_op(operator.inner)
		else {
			unreachable!(
				"build_unary_operator_dispatch called with an operator \
				 that has no overload trait"
			)
		};

		// Same reasoning as `build_operator_dispatch`'s equivalent branch: a
		// bare `Type::TypeParam` or `Type::AssocTypeProjection` isn't
		// concrete, so `resolve_trait_method` below can never resolve it —
		// deferred dispatch, resolved at MIR-lowering time once
		// monomorphization substitutes a concrete `Self`. An unbounded `T`
		// falls through to the same failure path below as a concrete type
		// with no matching impl.
		let deferred = match self.types.resolve(ty) {
			Type::TypeParam { owner, param_index } => self
				.resolve_bounded_operator_method(
					*owner,
					*param_index,
					trait_index,
					method_symbol,
				),
			Type::AssocTypeProjection { .. }
				if self.is_typeset_bounded_assoc_type(ty) =>
			{
				Some(self.operator_trait_method(trait_index, method_symbol))
			}
			_ => None,
		};
		if let Some(func_idx) = deferred {
			self.items.functions[usize::from(func_idx)].accesses.push(
				SourceSpan::new(ctx.resolve_context.file_id, operator.span),
			);
			let abstract_method_id =
				self.items.functions[usize::from(func_idx)].id;
			return Expression {
				kind: ExprKind::GenericMethodCall {
					id: abstract_method_id,
					type_args: Box::new([ty]),
					arguments: Box::new([operand]),
				},
				ty,
				span,
			};
		}

		match self.resolve_trait_method(trait_index, method_symbol, ty) {
			Some(func_idx) => {
				self.items.functions[usize::from(func_idx)].accesses.push(
					SourceSpan::new(ctx.resolve_context.file_id, operator.span),
				);
				let method_id = self.items.functions[usize::from(func_idx)].id;
				Expression {
					kind: ExprKind::MethodCall {
						arguments: Box::new([operand]),
						id: method_id,
					},
					ty,
					span,
				}
			}
			None => {
				self.diagnostics
					.push(report_unary_operator_cannot_be_applied(
						self.formatter(ctx.resolve_context.namespace),
						UnaryOperatorCannotBeAppliedDiagnostic {
							file_id: ctx.resolve_context.file_id,
							operator,
							operand: Spanned { inner: ty, span },
						},
					));
				Expression {
					kind: ExprKind::Unary {
						operator,
						operand: Box::new(operand),
					},
					ty: TypeIndex::ERROR,
					span,
				}
			}
		}
	}

	pub(super) fn build_binary_expression(
		&mut self,
		func_ctx: &mut ExprContext,
		access_ctx: AccessContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let operator = match &expr.inner {
			ast::Expression::Binary { operator, .. } => operator.inner,
			_ => unreachable!(),
		};

		match operator {
			ast::BinaryOp::Add
			| ast::BinaryOp::Sub
			| ast::BinaryOp::Mul
			| ast::BinaryOp::Div
			| ast::BinaryOp::Rem => {
				self.build_arithmetic_expr(func_ctx, expr, access_ctx)
			}
			ast::BinaryOp::Assign => self.build_assignment_expr(func_ctx, expr),
			ast::BinaryOp::AddAssign
			| ast::BinaryOp::SubAssign
			| ast::BinaryOp::MulAssign
			| ast::BinaryOp::DivAssign
			| ast::BinaryOp::RemAssign
			| ast::BinaryOp::BitAndAssign
			| ast::BinaryOp::BitOrAssign
			| ast::BinaryOp::BitXorAssign
			| ast::BinaryOp::LeftShiftAssign
			| ast::BinaryOp::RightShiftAssign => {
				self.build_compound_assignment_expr(func_ctx, expr)
			}
			ast::BinaryOp::Eq
			| ast::BinaryOp::NotEq
			| ast::BinaryOp::Less
			| ast::BinaryOp::LessEq
			| ast::BinaryOp::Greater
			| ast::BinaryOp::GreaterEq => {
				self.build_comparison_binary_expr(func_ctx, expr)
			}
			ast::BinaryOp::And | ast::BinaryOp::Or => {
				self.build_logical_binary_expr(func_ctx, expr)
			}
			ast::BinaryOp::BitAnd
			| ast::BinaryOp::BitOr
			| ast::BinaryOp::BitXor
			| ast::BinaryOp::LeftShift
			| ast::BinaryOp::RightShift => {
				self.build_bitwise_binary_expr(func_ctx, expr, access_ctx)
			}
		}
	}

	pub(super) fn build_unary_expression(
		&mut self,
		ctx: &mut ExprContext,
		access_ctx: AccessContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (operator, ast_operand) = match &expr.inner {
			ast::Expression::Unary { operator, operand } => {
				(*operator, operand)
			}
			_ => unreachable!(),
		};
		let mut operand = self.build_expression(
			ctx,
			AccessContext {
				expected_type: access_ctx.expected_type,
				access_kind: AccessKind::Read,
			},
			ast_operand,
		)?;

		match operator.inner {
			// `-x` — dispatches through `Neg`. A comptime-number operand
			// (e.g. `-1`) has no concrete type yet to dispatch against, so
			// this stays deferred exactly like binary arithmetic's arm 1
			// (`build_arithmetic_expr`) — `coerce_untyped_unary_expr`
			// resolves it later, once a concrete type is known.
			ast::UnaryOp::InvertSign if operand.ty.is_comptime_number() => {
				let ty = operand.ty;
				Ok(Expression {
					kind: ExprKind::Unary {
						operator,
						operand: Box::new(operand),
					},
					ty,
					span: expr.span,
				})
			}
			ast::UnaryOp::InvertSign => {
				let ty = operand.ty;
				Ok(self.build_unary_operator_dispatch(
					ctx, operator, operand, ty, expr.span,
				))
			}
			ast::UnaryOp::BitNot => {
				if operand.ty.is_primitive() || operand.ty.is_comptime_number()
				{
					// Native fast path — unchanged from before `BitNot`
					// had an overload trait at all: primitives and
					// deferred comptime numbers stay a plain `Unary`
					// node (no snapshot churn, no new intrinsics needed
					// for this case).
					let ty = operand.ty;
					Ok(Expression {
						kind: ExprKind::Unary {
							operator,
							operand: Box::new(operand),
						},
						ty,
						span: expr.span,
					})
				} else {
					// Anything else (a struct, or a typeset-bounded
					// `Type::TypeParam`/`Type::AssocTypeProjection`) goes
					// through real `BitNot` dispatch, which reports
					// "operator cannot be applied" on its own if nothing
					// implements it — same shape as `InvertSign`'s
					// always-dispatch arm above, just gated to the
					// non-primitive case to match the binary bitwise
					// operators' native-path split (`build_bitwise_result`).
					let ty = operand.ty;
					Ok(self.build_unary_operator_dispatch(
						ctx, operator, operand, ty, expr.span,
					))
				}
			}
			ast::UnaryOp::Not => {
				if operand.ty == TypeIndex::BOOL {
					Ok(Expression {
						kind: ExprKind::Unary {
							operator,
							operand: Box::new(operand),
						},
						ty: TypeIndex::BOOL,
						span: expr.span,
					})
				} else if operand.ty.is_comptime_number() {
					_ = self.coerce_untyped_expr(
						ctx,
						&mut operand,
						TypeIndex::BOOL,
					);
					Ok(Expression {
						kind: ExprKind::Unary {
							operator,
							operand: Box::new(operand),
						},
						ty: TypeIndex::BOOL,
						span: expr.span,
					})
				} else {
					let formatter =
						self.formatter(ctx.resolve_context.namespace);
					let diagnostic = Diagnostic::error()
						.with_code(
							DiagnosticCode::UnaryOperatorCannotBeApplied.code(),
						)
						.with_message(format!(
							"operator `{}` cannot be applied to type `{}`",
							operator.inner,
							formatter.display_type(operand.ty).unwrap()
						))
						.with_label(Label::primary(
							ctx.resolve_context.file_id,
							operand.span,
						))
						.with_label(Label::secondary(
							ctx.resolve_context.file_id,
							operator.span,
						));

					self.diagnostics.push(diagnostic);
					Ok(Expression {
						kind: ExprKind::Unary {
							operator,
							operand: Box::new(operand),
						},
						ty: TypeIndex::BOOL,
						span: expr.span,
					})
				}
			}
		}
	}

	fn build_logical_binary_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (left, right, operator) = match &expr.inner {
			ast::Expression::Binary {
				left,
				right,
				operator,
				..
			} => (left, right, *operator),
			_ => unreachable!(),
		};

		let left = self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::BOOL,
				access_kind: AccessKind::Read,
			},
			left,
		)?;
		if left.ty == TypeIndex::ERROR {
			// Error already reported
		} else if left.ty.is_comptime_number() {
			self.diagnostics.push(report_type_annotation_required(
				SourceSpan::new(ctx.resolve_context.file_id, left.span),
			));
		} else if left.ty != TypeIndex::BOOL {
			self.diagnostics.push(report_type_mistmatch(
				self.formatter(ctx.resolve_context.namespace),
				TypeMistmatchDiagnostic {
					expected_type: TypeIndex::BOOL,
					actual_type: left.ty,
					span: SourceSpan::new(
						ctx.resolve_context.file_id,
						left.span,
					),
				},
			));
		}
		let right = self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::BOOL,
				access_kind: AccessKind::Read,
			},
			right,
		)?;
		if right.ty == TypeIndex::ERROR {
			// Error already reported
		} else if right.ty.is_comptime_number() {
			self.diagnostics.push(report_type_annotation_required(
				SourceSpan::new(ctx.resolve_context.file_id, right.span),
			));
		} else if right.ty != TypeIndex::BOOL {
			self.diagnostics.push(report_type_mistmatch(
				self.formatter(ctx.resolve_context.namespace),
				TypeMistmatchDiagnostic {
					expected_type: TypeIndex::BOOL,
					actual_type: right.ty,
					span: SourceSpan::new(
						ctx.resolve_context.file_id,
						right.span,
					),
				},
			));
		}

		Ok(Expression {
			kind: ExprKind::Binary {
				operator: Spanned {
					inner: BinaryOp::from(operator.inner),
					span: operator.span,
				},
				left: Box::new(left),
				right: Box::new(right),
			},
			ty: TypeIndex::BOOL,
			span: expr.span,
		})
	}

	fn build_bitwise_binary_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
		access_ctx: AccessContext,
	) -> Result<Expression, ()> {
		let (left, right, operator) = match &expr.inner {
			ast::Expression::Binary {
				left,
				right,
				operator,
			} => (left, right, *operator),
			_ => unreachable!(),
		};
		let binary_op = Spanned {
			inner: BinaryOp::from(operator.inner),
			span: operator.span,
		};

		let mut left = self.build_expression(ctx, access_ctx, left)?;
		let mut right = self.build_expression(
			ctx,
			AccessContext {
				expected_type: match self.types.resolve(left.ty) {
					Type::Integer
					| Type::Float
					| Type::Error
					| Type::Never
					| Type::Unit => access_ctx.expected_type,
					_ => left.ty,
				},
				access_kind: access_ctx.access_kind,
			},
			right,
		)?;

		match (left.ty, right.ty) {
			// Allow operations with Error type (error already reported elsewhere)
			(l, r) if l == TypeIndex::ERROR || r == TypeIndex::ERROR => {
				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: access_ctx.expected_type.infer_or(TypeIndex::ERROR),
					span: expr.span,
				})
			}
			(l, r) if l.is_comptime_number() && r.is_comptime_number() => {
				if access_ctx.expected_type != TypeIndex::INFER {
					let expected_type = access_ctx.expected_type;
					self.coerce_untyped_expr(ctx, &mut left, expected_type)?;
					self.coerce_untyped_expr(ctx, &mut right, expected_type)?;

					if !expected_type.is_integer()
						&& expected_type != TypeIndex::BOOL
					{
						self.diagnostics.push(
							report_binary_operator_cannot_be_applied(
								self.formatter(ctx.resolve_context.namespace),
								BinaryOperatorCannotBeAppliedDiagnostic {
									file_id: ctx.resolve_context.file_id,
									operator,
									operand: Spanned {
										inner: expected_type,
										span: left.span,
									},
								},
							),
						);
					}

					Ok(Expression {
						kind: ExprKind::Binary {
							operator: binary_op,
							left: Box::new(left),
							right: Box::new(right),
						},
						ty: expected_type,
						span: expr.span,
					})
				} else {
					self.diagnostics.push(report_type_annotation_required(
						SourceSpan::new(ctx.resolve_context.file_id, expr.span),
					));
					Err(())
				}
			}
			(l, right_type) if l.is_comptime_number() => {
				if !right_type.is_integer() && right_type != TypeIndex::BOOL {
					self.diagnostics.push(
						report_binary_operator_cannot_be_applied(
							self.formatter(ctx.resolve_context.namespace),
							BinaryOperatorCannotBeAppliedDiagnostic {
								file_id: ctx.resolve_context.file_id,
								operator,
								operand: Spanned {
									inner: right_type,
									span: right.span,
								},
							},
						),
					);
				}
				self.coerce_untyped_expr(ctx, &mut left, right_type)?;

				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: right_type,
					span: expr.span,
				})
			}
			(left_type, r) if r.is_comptime_number() => {
				if !left_type.is_integer() && left_type != TypeIndex::BOOL {
					self.diagnostics.push(
						report_binary_operator_cannot_be_applied(
							self.formatter(ctx.resolve_context.namespace),
							BinaryOperatorCannotBeAppliedDiagnostic {
								file_id: ctx.resolve_context.file_id,
								operator,
								operand: Spanned {
									inner: left_type,
									span: left.span,
								},
							},
						),
					);
				}
				self.coerce_untyped_expr(ctx, &mut right, left_type)?;

				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: left_type,
					span: expr.span,
				})
			}
			(left_type, right_type) if left_type == right_type => Ok(self
				.build_bitwise_result(
					ctx, operator, left, right, left_type, expr.span,
				)),
			(left_type, right_type) => {
				self.diagnostics.push(report_binary_expression_mistmatch(
					self.formatter(ctx.resolve_context.namespace),
					BinaryExpressionMistmatchDiagnostic {
						file_id: ctx.resolve_context.file_id,
						left_type: Spanned {
							inner: left_type,
							span: left.span,
						},
						operator,
						right_type: Spanned {
							inner: right_type,
							span: right.span,
						},
					},
				));

				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: access_ctx.expected_type.infer_or(TypeIndex::ERROR),
					span: expr.span,
				})
			}
		}
	}

	fn build_comparison_binary_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (left, right, operator) = match &expr.inner {
			ast::Expression::Binary {
				left,
				right,
				operator,
				..
			} => (left, right, *operator),
			_ => unreachable!(),
		};
		let binary_op = Spanned {
			inner: BinaryOp::from(operator.inner),
			span: operator.span,
		};

		let mut left = self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Read,
			},
			left,
		)?;
		let mut right = self.build_expression(
			ctx,
			AccessContext {
				expected_type: left.ty,
				access_kind: AccessKind::Read,
			},
			right,
		)?;

		match (left.ty, right.ty) {
			// Allow operations with Error type (error already reported elsewhere)
			(l, r) if l == TypeIndex::ERROR || r == TypeIndex::ERROR => {
				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(l, r) if l.is_comptime_number() && r.is_comptime_number() => {
				self.diagnostics.push(
					report_comparison_type_annotation_required(
						SourceSpan::new(ctx.resolve_context.file_id, left.span),
						SourceSpan::new(
							ctx.resolve_context.file_id,
							right.span,
						),
					),
				);

				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(l, ty) if l.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut left, ty)?;

				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(ty, r) if r.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut right, ty)?;

				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(l, r) if l == TypeIndex::BOOL && r == TypeIndex::BOOL => {
				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(left_type, right_type)
				if left_type == right_type
					&& (left_type.is_primitive()
						|| self.is_typeset_bounded_assoc_type(left_type)) =>
			{
				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(left_type, right_type)
				if left_type == right_type
					&& matches!(
						self.types.resolve(left_type),
						Type::Enum { .. }
					) =>
			{
				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(left_type, right_type)
				if matches!(
					operator.inner,
					ast::BinaryOp::Eq | ast::BinaryOp::NotEq
				) && matches!(
					(
						self.types.resolve(left_type),
						self.types.resolve(right_type),
					),
					(
						Type::Pointer { to: lt, memory: lm, .. },
						Type::Pointer { to: rt, memory: rm, .. },
					) if lt == rt && lm == rm
				) =>
			{
				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			(left_type, right_type) => {
				self.diagnostics.push(report_binary_expression_mistmatch(
					self.formatter(ctx.resolve_context.namespace),
					BinaryExpressionMistmatchDiagnostic {
						file_id: ctx.resolve_context.file_id,
						left_type: Spanned {
							inner: left_type,
							span: left.span,
						},
						operator,
						right_type: Spanned {
							inner: right_type,
							span: right.span,
						},
					},
				));

				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
		}
	}

	fn build_assignment_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (left, right, operator) = match &expr.inner {
			ast::Expression::Binary {
				left,
				right,
				operator,
			} => (left, right, *operator),
			_ => unreachable!(),
		};

		let left = self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::Write,
			},
			left,
		)?;
		match left.kind {
			ExprKind::Local {
				scope_index,
				local_index,
			} => {
				let local_type =
					ctx.stack.get_local(scope_index, local_index).ty;
				let mut right = self.build_expression(
					ctx,
					AccessContext {
						expected_type: local_type,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right, local_type)?;
				} else if !self.coercible_to(right.ty, local_type) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: local_type,
								span: left.span,
							},
							operator,
							right_type: Spanned {
								inner: right.ty,
								span: right.span,
							},
						},
					));
				}

				Ok(Expression {
					kind: ExprKind::Assign {
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::Global { id } => {
				let global_index = self.items.expect_global_index(id);
				let global = &self.items.globals[usize::from(global_index)];
				let global_type = global.ty.inner;
				let mut right = self.build_expression(
					ctx,
					AccessContext {
						expected_type: global_type,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right, global_type)?;
				} else if !self.coercible_to(right.ty, global_type) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: global_type,
								span: left.span,
							},
							operator,
							right_type: Spanned {
								inner: right.ty,
								span: right.span,
							},
						},
					));
				}

				Ok(Expression {
					kind: ExprKind::Assign {
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::Placeholder => {
				let right = self.build_expression(
					ctx,
					AccessContext {
						expected_type: TypeIndex::INFER,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right.ty.is_comptime_number() {
					self.diagnostics.push(report_type_annotation_required(
						SourceSpan::new(
							ctx.resolve_context.file_id,
							right.span,
						),
					));
					return Err(());
				}
				let right_type = right.ty;

				Ok(Expression {
					kind: ExprKind::Assign {
						left: Box::new(Expression {
							kind: ExprKind::Placeholder,
							ty: right_type,
							span: left.span,
						}),
						right: Box::new(right),
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::Load { place } => {
				let inner_ty = place.ty;
				let left_span = left.span;
				let mut right_expr = self.build_expression(
					ctx,
					AccessContext {
						expected_type: inner_ty,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right_expr.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right_expr, inner_ty)?;
				} else if !self.coercible_to(right_expr.ty, inner_ty) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: inner_ty,
								span: left_span,
							},
							operator,
							right_type: Spanned {
								inner: right_expr.ty,
								span: right_expr.span,
							},
						},
					));
				}
				Ok(Expression {
					kind: ExprKind::Store {
						target: place,
						value: Box::new(right_expr),
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::FieldAccess { ref object, .. } => {
				if !matches!(
					object.kind,
					ExprKind::Local { .. } | ExprKind::Global { .. }
				) {
					self.diagnostics.push(report_invalid_assignment_target(
						SourceSpan::new(ctx.resolve_context.file_id, left.span),
					));
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::UNIT,
						span: expr.span,
					});
				}
				let field_ty = left.ty;
				let left_span = left.span;
				let mut right_expr = self.build_expression(
					ctx,
					AccessContext {
						expected_type: field_ty,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right_expr.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right_expr, field_ty)?;
				} else if !self.coercible_to(right_expr.ty, field_ty) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: field_ty,
								span: left_span,
							},
							operator,
							right_type: Spanned {
								inner: right_expr.ty,
								span: right_expr.span,
							},
						},
					));
				}
				Ok(Expression {
					kind: ExprKind::Assign {
						left: Box::new(left),
						right: Box::new(right_expr),
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::Error => {
				let right_expr = self
					.build_expression(
						ctx,
						AccessContext {
							expected_type: TypeIndex::ERROR,
							access_kind: AccessKind::Read,
						},
						right,
					)
					.unwrap_or(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::ERROR,
						span: right.span,
					});
				Ok(Expression {
					kind: ExprKind::Assign {
						left: Box::new(left),
						right: Box::new(right_expr),
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			_ => {
				self.diagnostics.push(report_invalid_assignment_target(
					SourceSpan::new(ctx.resolve_context.file_id, left.span),
				));

				Ok(Expression {
					kind: ExprKind::Error,
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
		}
	}

	fn build_compound_assignment_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
	) -> Result<Expression, ()> {
		let (left, right, operator) = match &expr.inner {
			ast::Expression::Binary {
				left,
				right,
				operator,
			} => (left, right, *operator),
			_ => unreachable!(),
		};

		// `ExprKind::CompoundAssign` and `resolve_compound_assignment_method`
		// only ever deal in the plain form — see `CompoundAssign`'s doc
		// comment. `operator` (the `*Assign` form) is kept around only for
		// `BinaryExpressionMistmatchDiagnostic`, which has its own
		// dedicated "cannot add-assign" wording.
		let plain_op = Spanned {
			inner: match operator.inner {
				ast::BinaryOp::AddAssign => ast::BinaryOp::Add,
				ast::BinaryOp::SubAssign => ast::BinaryOp::Sub,
				ast::BinaryOp::MulAssign => ast::BinaryOp::Mul,
				ast::BinaryOp::DivAssign => ast::BinaryOp::Div,
				ast::BinaryOp::RemAssign => ast::BinaryOp::Rem,
				ast::BinaryOp::BitAndAssign => ast::BinaryOp::BitAnd,
				ast::BinaryOp::BitOrAssign => ast::BinaryOp::BitOr,
				ast::BinaryOp::BitXorAssign => ast::BinaryOp::BitXor,
				ast::BinaryOp::LeftShiftAssign => ast::BinaryOp::LeftShift,
				ast::BinaryOp::RightShiftAssign => ast::BinaryOp::RightShift,
				_ => unreachable!(),
			},
			span: operator.span,
		};

		let left = self.build_expression(
			ctx,
			AccessContext {
				expected_type: TypeIndex::INFER,
				access_kind: AccessKind::ReadWrite,
			},
			left,
		)?;
		match left.kind {
			ExprKind::Local {
				scope_index,
				local_index,
			} => {
				let local_type =
					ctx.stack.get_local(scope_index, local_index).ty;
				let mut right = self.build_expression(
					ctx,
					AccessContext {
						expected_type: local_type,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right, local_type)?;
				} else if !self.coercible_to(right.ty, local_type) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: local_type,
								span: left.span,
							},
							operator,
							right_type: Spanned {
								inner: right.ty,
								span: right.span,
							},
						},
					));
				}

				let dispatch = self.resolve_compound_operator(
					ctx, plain_op, local_type, left.span,
				)?;
				Ok(Expression {
					kind: match dispatch {
						CompoundOperatorDispatch::Concrete(method_id) => {
							ExprKind::CompoundAssign {
								target: Box::new(left),
								rhs: Box::new(right),
								method_id,
							}
						}
						CompoundOperatorDispatch::Generic {
							abstract_method_id,
						} => ExprKind::GenericCompoundAssign {
							target: Box::new(left),
							rhs: Box::new(right),
							abstract_method_id,
							self_type: local_type,
						},
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::Global { id } => {
				let global_index = self.items.expect_global_index(id);
				let global =
					self.items.globals.get(usize::from(global_index)).unwrap();
				let global_type = global.ty.inner;
				let mut right = self.build_expression(
					ctx,
					AccessContext {
						expected_type: global_type,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right, global_type)?;
				} else if !self.coercible_to(right.ty, global_type) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: global_type,
								span: left.span,
							},
							operator,
							right_type: Spanned {
								inner: right.ty,
								span: right.span,
							},
						},
					));
				}

				let dispatch = self.resolve_compound_operator(
					ctx,
					plain_op,
					global_type,
					left.span,
				)?;
				Ok(Expression {
					kind: match dispatch {
						CompoundOperatorDispatch::Concrete(method_id) => {
							ExprKind::CompoundAssign {
								target: Box::new(left),
								rhs: Box::new(right),
								method_id,
							}
						}
						CompoundOperatorDispatch::Generic {
							abstract_method_id,
						} => ExprKind::GenericCompoundAssign {
							target: Box::new(left),
							rhs: Box::new(right),
							abstract_method_id,
							self_type: global_type,
						},
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::Load { place } => {
				let inner_ty = place.ty;
				let left_span = left.span;
				let mut right_expr = self.build_expression(
					ctx,
					AccessContext {
						expected_type: inner_ty,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right_expr.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right_expr, inner_ty)?;
				} else if !self.coercible_to(right_expr.ty, inner_ty) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: inner_ty,
								span: left_span,
							},
							operator,
							right_type: Spanned {
								inner: right_expr.ty,
								span: right_expr.span,
							},
						},
					));
				}
				let dispatch = self.resolve_compound_operator(
					ctx, plain_op, inner_ty, left_span,
				)?;
				Ok(Expression {
					kind: match dispatch {
						CompoundOperatorDispatch::Concrete(method_id) => {
							ExprKind::CompoundStore {
								target: place,
								rhs: Box::new(right_expr),
								method_id,
							}
						}
						CompoundOperatorDispatch::Generic {
							abstract_method_id,
						} => ExprKind::GenericCompoundStore {
							target: place,
							rhs: Box::new(right_expr),
							abstract_method_id,
							self_type: inner_ty,
						},
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			ExprKind::FieldAccess { ref object, .. } => {
				if !matches!(
					object.kind,
					ExprKind::Local { .. } | ExprKind::Global { .. }
				) {
					self.diagnostics.push(report_invalid_assignment_target(
						SourceSpan::new(ctx.resolve_context.file_id, left.span),
					));
					return Ok(Expression {
						kind: ExprKind::Error,
						ty: TypeIndex::UNIT,
						span: expr.span,
					});
				}
				let field_ty = left.ty;
				let left_span = left.span;
				let mut right_expr = self.build_expression(
					ctx,
					AccessContext {
						expected_type: field_ty,
						access_kind: AccessKind::Read,
					},
					right,
				)?;
				if right_expr.ty.is_comptime_number() {
					self.coerce_untyped_expr(ctx, &mut right_expr, field_ty)?;
				} else if !self.coercible_to(right_expr.ty, field_ty) {
					self.diagnostics.push(report_binary_expression_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						BinaryExpressionMistmatchDiagnostic {
							file_id: ctx.resolve_context.file_id,
							left_type: Spanned {
								inner: field_ty,
								span: left_span,
							},
							operator,
							right_type: Spanned {
								inner: right_expr.ty,
								span: right_expr.span,
							},
						},
					));
				}
				let dispatch = self.resolve_compound_operator(
					ctx, plain_op, field_ty, left_span,
				)?;
				Ok(Expression {
					kind: match dispatch {
						CompoundOperatorDispatch::Concrete(method_id) => {
							ExprKind::CompoundAssign {
								target: Box::new(left),
								rhs: Box::new(right_expr),
								method_id,
							}
						}
						CompoundOperatorDispatch::Generic {
							abstract_method_id,
						} => ExprKind::GenericCompoundAssign {
							target: Box::new(left),
							rhs: Box::new(right_expr),
							abstract_method_id,
							self_type: field_ty,
						},
					},
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			// The target is already in error, so there is no operator impl to
			// resolve and no `method_id` to build a `CompoundStore` around.
			// Check the right-hand side anyway so its own mistakes still get
			// reported, then absorb — the right-hand side of
			// `build_assignment_expr`'s `ExprKind::Error` arm gets the same
			// treatment.
			ExprKind::Error => {
				self.build_expression(
					ctx,
					AccessContext {
						expected_type: TypeIndex::ERROR,
						access_kind: AccessKind::Read,
					},
					right,
				)
				.ok();

				Ok(Expression {
					kind: ExprKind::Error,
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
			_ => {
				self.diagnostics.push(report_invalid_assignment_target(
					SourceSpan::new(ctx.resolve_context.file_id, left.span),
				));

				Ok(Expression {
					kind: ExprKind::Error,
					ty: TypeIndex::UNIT,
					span: expr.span,
				})
			}
		}
	}

	fn build_arithmetic_expr(
		&mut self,
		ctx: &mut ExprContext,
		expr: &Spanned<ast::Expression>,
		access_ctx: AccessContext,
	) -> Result<Expression, ()> {
		let (left, right, operator) = match &expr.inner {
			ast::Expression::Binary {
				left,
				right,
				operator,
			} => (left, right, *operator),
			_ => unreachable!(),
		};
		let binary_op = Spanned {
			inner: BinaryOp::from(operator.inner),
			span: operator.span,
		};

		let mut left = self.build_expression(
			ctx,
			AccessContext {
				expected_type: access_ctx.expected_type,
				access_kind: AccessKind::Read,
			},
			left,
		)?;
		let mut right = self.build_expression(
			ctx,
			AccessContext {
				expected_type: match self.types.resolve(left.ty) {
					Type::Integer
					| Type::Float
					| Type::Error
					| Type::Never
					| Type::Unit => access_ctx.expected_type,
					_ => left.ty,
				},
				access_kind: AccessKind::Read,
			},
			right,
		)?;

		match (left.ty, right.ty) {
			(l, r) if l.is_comptime_number() && r.is_comptime_number() => {
				if l != r {
					self.diagnostics.push(report_type_mistmatch(
						self.formatter(ctx.resolve_context.namespace),
						TypeMistmatchDiagnostic {
							expected_type: l,
							actual_type: r,
							span: SourceSpan::new(
								ctx.resolve_context.file_id,
								right.span,
							),
						},
					));
					return Ok(Expression {
						kind: ExprKind::Binary {
							operator: binary_op,
							left: Box::new(left),
							right: Box::new(right),
						},
						ty: TypeIndex::ERROR,
						span: expr.span,
					});
				}
				Ok(Expression {
					kind: ExprKind::Binary {
						operator: binary_op,
						left: Box::new(left),
						right: Box::new(right),
					},
					ty: l,
					span: expr.span,
				})
			}
			(l, ty) if l.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut left, ty)?;
				Ok(self.build_operator_dispatch(
					ctx, operator, left, right, ty, expr.span,
				))
			}
			(ty, r) if r.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut right, ty)?;
				Ok(self.build_operator_dispatch(
					ctx, operator, left, right, ty, expr.span,
				))
			}
			(l, _) if l == TypeIndex::NEVER => {
				self.diagnostics.push(report_unreachable_code(
					SourceSpan::new(ctx.resolve_context.file_id, right.span),
				));

				Ok(left)
			}
			(_, r) if r == TypeIndex::NEVER => {
				self.diagnostics.push(report_unreachable_code(
					SourceSpan::new(ctx.resolve_context.file_id, operator.span),
				));

				Ok(right)
			}
			(left_type, right_type) if left_type == right_type => Ok(self
				.build_operator_dispatch(
					ctx, operator, left, right, left_type, expr.span,
				)),
			(left_type, right_type) => {
				self.diagnostics.push(report_binary_expression_mistmatch(
					self.formatter(ctx.resolve_context.namespace),
					BinaryExpressionMistmatchDiagnostic {
						file_id: ctx.resolve_context.file_id,
						left_type: Spanned {
							inner: left_type,
							span: left.span,
						},
						operator,
						right_type: Spanned {
							inner: right_type,
							span: right.span,
						},
					},
				));

				if access_ctx.expected_type != TypeIndex::INFER {
					Ok(Expression {
						kind: ExprKind::Binary {
							operator: binary_op,
							left: Box::new(left),
							right: Box::new(right),
						},
						ty: access_ctx.expected_type,
						span: expr.span,
					})
				} else {
					Err(())
				}
			}
		}
	}
}

struct BinaryOperatorCannotBeAppliedDiagnostic {
	file_id: FileId,
	operator: Spanned<ast::BinaryOp>,
	operand: Spanned<TypeIndex>,
}

fn report_binary_operator_cannot_be_applied(
	fmt: TypeFormatter,
	diagnostic: BinaryOperatorCannotBeAppliedDiagnostic,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::BinaryOperatorCannotBeApplied.code())
		.with_message(format!(
			"operator `{}` cannot be applied to type `{}`",
			diagnostic.operator.inner,
			fmt.display_type(diagnostic.operand.inner).unwrap()
		))
		.with_label(Label::primary(diagnostic.file_id, diagnostic.operand.span))
		.with_label(Label::secondary(
			diagnostic.file_id,
			diagnostic.operator.span,
		))
}

struct UnaryOperatorCannotBeAppliedDiagnostic {
	file_id: FileId,
	operator: Spanned<ast::UnaryOp>,
	operand: Spanned<TypeIndex>,
}

fn report_unary_operator_cannot_be_applied(
	fmt: TypeFormatter,
	diagnostic: UnaryOperatorCannotBeAppliedDiagnostic,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnaryOperatorCannotBeApplied.code())
		.with_message(format!(
			"operator `{}` cannot be applied to type `{}`",
			diagnostic.operator.inner,
			fmt.display_type(diagnostic.operand.inner).unwrap()
		))
		.with_label(Label::primary(diagnostic.file_id, diagnostic.operand.span))
		.with_label(Label::secondary(
			diagnostic.file_id,
			diagnostic.operator.span,
		))
}

struct BinaryExpressionMistmatchDiagnostic {
	file_id: FileId,
	left_type: Spanned<TypeIndex>,
	operator: Spanned<ast::BinaryOp>,
	right_type: Spanned<TypeIndex>,
}

fn report_binary_expression_mistmatch(
	fmt: TypeFormatter,
	diagnostic: BinaryExpressionMistmatchDiagnostic,
) -> Diagnostic<FileId> {
	let left_type_name = fmt.display_type(diagnostic.left_type.inner).unwrap();
	let right_type_name =
		fmt.display_type(diagnostic.right_type.inner).unwrap();

	let message = match diagnostic.operator.inner {
		ast::BinaryOp::Add => {
			format!("cannot add `{}` to `{}`", left_type_name, right_type_name)
		}
		ast::BinaryOp::Sub => format!(
			"cannot subtract `{}` from `{}`",
			left_type_name, right_type_name
		),
		ast::BinaryOp::Assign => format!(
			"cannot assign `{}` to `{}`",
			right_type_name, left_type_name
		),
		ast::BinaryOp::Mul => format!(
			"cannot multiply `{}` by `{}`",
			left_type_name, right_type_name
		),
		ast::BinaryOp::Div => format!(
			"cannot divide `{}` by `{}`",
			left_type_name, right_type_name
		),
		ast::BinaryOp::Rem => format!(
			"cannot calculate the remainder of `{}` by `{}`",
			left_type_name, right_type_name
		),
		ast::BinaryOp::Eq
		| ast::BinaryOp::NotEq
		| ast::BinaryOp::Less
		| ast::BinaryOp::LessEq
		| ast::BinaryOp::Greater
		| ast::BinaryOp::GreaterEq => {
			format!(
				"cannot compare `{}` to `{}`",
				left_type_name, right_type_name
			)
		}
		ast::BinaryOp::MulAssign => {
			format!(
				"cannot multiply-assign `{}` to `{}`",
				right_type_name, left_type_name
			)
		}
		ast::BinaryOp::DivAssign => {
			format!(
				"cannot divide-assign `{}` by `{}`",
				right_type_name, left_type_name
			)
		}
		ast::BinaryOp::RemAssign => format!(
			"cannot remainder-assign `{}` by `{}`",
			right_type_name, left_type_name
		),
		ast::BinaryOp::AddAssign => {
			format!(
				"cannot add-assign `{}` to `{}`",
				right_type_name, left_type_name
			)
		}
		ast::BinaryOp::SubAssign => format!(
			"cannot subtract-assign `{}` from `{}`",
			right_type_name, left_type_name
		),
		_ => format!(
			"cannot perform operation on `{}` and `{}`",
			left_type_name, right_type_name
		),
	};

	Diagnostic::error()
		.with_code(DiagnosticCode::TypeMistmatch)
		.with_message(message)
		.with_label(
			Label::secondary(diagnostic.file_id, diagnostic.left_type.span)
				.with_message(format!("`{}`", left_type_name)),
		)
		.with_label(
			Label::primary(diagnostic.file_id, diagnostic.right_type.span)
				.with_message(format!("`{}`", right_type_name)),
		)
}

fn report_invalid_assignment_target(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidAssignmentTarget.code())
		.with_message("invalid assignment target")
		.with_label(
			span.primary_label()
				.with_message("cannot assign to this expression"),
		)
		.with_note("assignment only allowed to a variable or `_`")
}

fn report_comparison_type_annotation_required(
	left: SourceSpan,
	right: SourceSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ComparisonTypeAnnotationRequired.code())
		.with_message("type annotation required")
		.with_label(left.primary_label())
		.with_label(right.primary_label())
		.with_note("at least one side of the comparison must have a known type")
}
