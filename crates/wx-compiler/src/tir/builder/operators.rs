//! Operator overloading, end to end: resolving the stdlib `Add`/`Sub`/...
//! traits an operator dispatches through, and building every expression that
//! dispatches through one — binary and unary arithmetic, bitwise, comparison,
//! logical, assignment and compound assignment.

use crate::diagnostics::DiagnosticCode;

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
	not: (TraitIndex, SymbolU32),
	eq: (TraitIndex, SymbolU32),
	ne: (TraitIndex, SymbolU32),
	lt: (TraitIndex, SymbolU32),
	le: (TraitIndex, SymbolU32),
	gt: (TraitIndex, SymbolU32),
	ge: (TraitIndex, SymbolU32),
}

impl OperatorTraits {
	/// Maps a `BinaryOp` to its `(TraitIndex, SymbolU32)` entry — the lookup
	/// every operator-dispatch path needs, factored out so it's defined once.
	/// Covers arithmetic, bitwise, equality (`==`/`!=` → `PartialEq::eq`/`ne`)
	/// and ordering (`<`/`<=`/`>`/`>=` → `PartialOrd::lt`/`le`/`gt`/`ge`).
	/// `None` for an operator with no overload trait (logical, assignment).
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
			BinaryOp::Eq => self.eq,
			BinaryOp::NotEq => self.ne,
			BinaryOp::Less => self.lt,
			BinaryOp::LessEq => self.le,
			BinaryOp::Greater => self.gt,
			BinaryOp::GreaterEq => self.ge,
			_ => return None,
		})
	}

	/// Unary counterpart of `for_op`, for `-x` (`Neg`), `^x` (`BitNot`) and
	/// `!x` (`Not`). Every unary operator has an overload trait, so — unlike
	/// `for_op`, which returns `None` for the non-overloadable binary
	/// operators — this is total.
	pub(super) fn for_unary_op(
		&self,
		op: ast::UnaryOp,
	) -> (TraitIndex, SymbolU32) {
		match op {
			ast::UnaryOp::InvertSign => self.neg,
			ast::UnaryOp::BitNot => self.bitnot,
			ast::UnaryOp::Not => self.not,
		}
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

/// What `Builder::resolve_trait_method` found for an operator's method on a
/// concrete type. `Impl` — an impl block provides it directly, so the callee
/// is fully concrete and dispatch builds a plain `MethodCall`. `Default` —
/// only the trait's own bodied default supplies it (`PartialEq::ne` when the
/// impl overrides just `eq`), so `Self` is still abstract inside that body and
/// dispatch must build a `GenericMethodCall` with the operand type as the
/// `Self` type arg, exactly like an abstract operand.
pub(super) enum OperatorMethod {
	Impl(FunctionIndex),
	Default(FunctionIndex),
}

impl OperatorMethod {
	/// The resolved method's index, regardless of which kind it is — for the
	/// call sites that only want to record a go-to-definition access against
	/// it and don't care whether it came from an impl or a trait default.
	pub(super) fn function_index(&self) -> FunctionIndex {
		match self {
			OperatorMethod::Impl(idx) | OperatorMethod::Default(idx) => *idx,
		}
	}
}

/// What a concrete, non-default `impl` match (`OperatorMethod::Impl`)
/// becomes in `Builder::build_operator_dispatch`. `MethodCall` is the
/// ordinary shape; `Native` is `Builder::dispatch_binary_op`'s opt-in for a
/// primitive operand where MIR's inliner would otherwise process a call
/// only to dissolve it back to the same instruction — skips straight to the
/// plain `Binary` node that inlining would have produced anyway. Every
/// other resolution outcome (`Comptime`, deferred-generic, `Default`, no
/// impl) is unaffected by this choice.
enum ImplNode {
	MethodCall,
	Native,
}

impl<'ast> Builder<'ast, '_> {
	pub(super) fn resolve_operator_traits(&self) -> OperatorTraits {
		let resolve_operator_method = |trait_name: &str, method_name: &str| {
			let symbol = self.interner.get(trait_name).unwrap();
			let method_symbol = self.interner.get(method_name).unwrap();
			let def_id = *self.items.tagged_items.get(&symbol).unwrap();
			(self.items.expect_trait_index(def_id), method_symbol)
		};

		OperatorTraits {
			add: resolve_operator_method("Add", "add"),
			sub: resolve_operator_method("Sub", "sub"),
			mul: resolve_operator_method("Mul", "mul"),
			div: resolve_operator_method("Div", "div"),
			rem: resolve_operator_method("Rem", "rem"),
			neg: resolve_operator_method("Neg", "neg"),
			bitand: resolve_operator_method("BitAnd", "bitand"),
			bitor: resolve_operator_method("BitOr", "bitor"),
			bitxor: resolve_operator_method("BitXor", "bitxor"),
			shl: resolve_operator_method("Shl", "shl"),
			shr: resolve_operator_method("Shr", "shr"),
			bitnot: resolve_operator_method("BitNot", "bitnot"),
			not: resolve_operator_method("Not", "not"),
			eq: resolve_operator_method("PartialEq", "eq"),
			ne: resolve_operator_method("PartialEq", "ne"),
			lt: resolve_operator_method("PartialOrd", "lt"),
			le: resolve_operator_method("PartialOrd", "le"),
			gt: resolve_operator_method("PartialOrd", "gt"),
			ge: resolve_operator_method("PartialOrd", "ge"),
		}
	}

	/// Pure lookup: resolves `ty`'s method for the trait tagged `trait_index`
	/// under member name `method_symbol`. No side effects, no `EvalMode`
	/// awareness — callers only call this once they already know evaluation
	/// mode is `Runtime` (see `build_operator_dispatch`), and decide for
	/// themselves what a `None` means (a struct with no `Add` impl is a real
	/// error; an abstract operand whose bounds still imply the operator —
	/// handled up front by `abstract_operand_defers_operator` — is not, since
	/// `find_trait_impl` has no concrete `ImplTarget` to match). Shared by
	/// binary (`build_operator_dispatch`), unary (`Neg`), and the
	/// `Type::TypeParam` compound-assignment dispatch.
	///
	/// Distinguishes an impl-provided method (`Impl` — call it as a plain
	/// `MethodCall`, the callee is fully concrete) from one only the trait's
	/// own default body supplies (`Default`, e.g. `PartialEq::ne` when the
	/// impl overrides only `eq` — this still has an abstract `Self`, so the
	/// caller must build a `GenericMethodCall` with `ty` as the `Self` type
	/// arg, the same as an abstract operand). The trait's own member
	/// signatures are resolved in Phase 2, well before any operator dispatch
	/// runs, so the default-body check here stays a pure read.
	pub(super) fn resolve_trait_method(
		&self,
		trait_index: TraitIndex,
		method_symbol: SymbolU32,
		ty: TypeIndex,
	) -> Option<OperatorMethod> {
		let (impl_idx, _type_args) =
			self.items.find_trait_impl(&self.types, ty, trait_index)?;
		if let Some(entry) = self.items.trait_impls[usize::from(impl_idx)]
			.members
			.get(&method_symbol)
		{
			return match entry {
				ImplEntry::Method(func_idx) => {
					Some(OperatorMethod::Impl(*func_idx))
				}
				_ => None,
			};
		}
		// The impl exists but doesn't override this method — fall back to the
		// trait's own bodied default (`PartialEq::ne`'s `!self.eq(other)`).
		match self.items.traits[usize::from(trait_index)]
			.members
			.get(&method_symbol)?
		{
			MemberIndex::Function(func_idx)
				if self.entry_has_body(ImplEntry::Method(*func_idx)) =>
			{
				Some(OperatorMethod::Default(*func_idx))
			}
			_ => None,
		}
	}

	/// Records `op_span` (an operator token's own span) as a go-to-definition /
	/// hover access against the operator method `func_idx` resolves to, and
	/// returns that method's `DefId` for building the call node. Every operator
	/// dispatch path — binary and unary arithmetic/bitwise, compound
	/// assignment, concrete and generic — funnels its access recording through
	/// here, so hover / goto-def on an operator lands on the same method the
	/// call resolves to, and coverage can't drift between operator families.
	fn record_operator_method_access(
		&mut self,
		ctx: &ExprContext,
		func_idx: FunctionIndex,
		op_span: ast::TextSpan,
	) -> ast::DefId {
		let func = &mut self.items.functions[usize::from(func_idx)];
		func.accesses
			.push(SourceSpan::new(ctx.resolve_context.file_id, op_span));
		func.id
	}

	/// Whether an abstract operand `ty` (a `Type::TypeParam` or
	/// `Type::AssocTypeProjection`) is bound tightly enough to defer this
	/// operator to monomorphization: its declared bounds must *imply* the
	/// operator's own trait — directly (`T: Add`) or transitively (`T: Integer`
	/// where the generated `Integer` trait has `Add` as a supertrait). An
	/// unbounded `T` fails here and falls through to the concrete-resolution
	/// path, which reports "operator cannot be applied".
	fn abstract_operand_defers_operator(
		&self,
		ty: TypeIndex,
		trait_index: TraitIndex,
		method_symbol: SymbolU32,
	) -> Option<FunctionIndex> {
		if !matches!(
			self.types.resolve(ty),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			return None;
		}
		if !self
			.items
			.type_implements_trait(&self.types, ty, trait_index)
		{
			return None;
		}

		match self.items.traits[usize::from(trait_index)]
			.members
			.get(&method_symbol)
		{
			Some(MemberIndex::Function(idx)) => Some(*idx),
			_ => unreachable!("operator trait must declare its own method"),
		}
	}

	/// Resolves `operator` for `operand_ty` in `ctx`'s evaluation mode and
	/// builds the resulting expression, whose type is `result_ty`:
	/// - `Comptime` never attempts dispatch at all (see `EvalMode`'s doc
	///   comment) — builds a plain `Binary` node, exactly as before operator
	///   overloading existed, still directly foldable by `eval_const_expr`.
	/// - `Runtime`, `operand_ty` isn't concrete yet (`Type::TypeParam` or
	///   `Type::AssocTypeProjection`) but its declared bounds imply the
	///   operator's trait (see `abstract_operand_defers_operator`) — builds a
	///   `GenericMethodCall`, deferred to real resolution once monomorphization
	///   substitutes a concrete `Self`.
	/// - `Runtime`, dispatch succeeds against a concrete type — records
	///   `operator`'s own span as a go-to-definition access against the
	///   resolved method (the same `accesses`-list mechanism ordinary
	///   method calls use) and builds a `MethodCall` or a native `Binary`
	///   (per `impl_node`), or a `GenericMethodCall` when only the trait's
	///   own default body supplies the method (`OperatorMethod::Default`,
	///   e.g. `!=` → `PartialEq::ne` — always `MethodCall`-shaped regardless
	///   of `impl_node`, since there's no single concrete impl to treat as
	///   native).
	/// - `Runtime`, dispatch fails — reports "operator cannot be applied".
	///
	/// `operand_ty` and `result_ty` are the same for arithmetic and bitwise
	/// operators (an operator on `T` yields a `T`); they differ for `==`/`!=`,
	/// where the operands are some `T` but the result is always `bool`.
	#[allow(clippy::too_many_arguments)]
	fn build_operator_dispatch(
		&mut self,
		ctx: &ExprContext,
		operator: Spanned<ast::BinaryOp>,
		left: Expression,
		right: Expression,
		operand_ty: TypeIndex,
		result_ty: TypeIndex,
		span: ast::TextSpan,
		impl_node: ImplNode,
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
				ty: result_ty,
				span,
			};
		};

		if let Some((trait_index, method_symbol)) =
			traits.for_op(binary_op.inner)
		{
			let deferred = self.abstract_operand_defers_operator(
				operand_ty,
				trait_index,
				method_symbol,
			);
			if let Some(func_idx) = deferred {
				let abstract_method_id = self.record_operator_method_access(
					ctx,
					func_idx,
					operator.span,
				);
				return Expression {
					kind: ExprKind::GenericMethodCall {
						id: abstract_method_id,
						type_args: Box::new([operand_ty]),
						arguments: Box::new([left, right]),
					},
					ty: result_ty,
					span,
				};
			}
		}

		let method = traits.for_op(binary_op.inner).and_then(
			|(trait_index, method_symbol)| {
				self.resolve_trait_method(
					trait_index,
					method_symbol,
					operand_ty,
				)
			},
		);
		match method {
			Some(OperatorMethod::Impl(func_idx)) => {
				let method_id = self.record_operator_method_access(
					ctx,
					func_idx,
					operator.span,
				);
				match impl_node {
					ImplNode::MethodCall => Expression {
						kind: ExprKind::MethodCall {
							arguments: Box::new([left, right]),
							id: method_id,
						},
						ty: result_ty,
						span,
					},
					ImplNode::Native => Expression {
						kind: ExprKind::Binary {
							operator: binary_op,
							left: Box::new(left),
							right: Box::new(right),
						},
						ty: result_ty,
						span,
					},
				}
			}
			Some(OperatorMethod::Default(func_idx)) => {
				let method_id = self.record_operator_method_access(
					ctx,
					func_idx,
					operator.span,
				);
				Expression {
					kind: ExprKind::GenericMethodCall {
						id: method_id,
						type_args: Box::new([operand_ty]),
						arguments: Box::new([left, right]),
					},
					ty: result_ty,
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
							operand: Spanned {
								inner: operand_ty,
								span,
							},
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

		// An abstract operand (`Mem::Size`, or a bounded `T`) defers to
		// monomorphization when its bounds imply this operator's trait — an
		// unbounded `T` falls through to the failure path below instead of
		// building a `GenericCompoundAssign`/`GenericCompoundStore` that would
		// only panic later once monomorphization substitutes a concrete,
		// non-implementing type.
		let abstract_func_idx = self.abstract_operand_defers_operator(
			ty,
			trait_index,
			method_symbol,
		);
		if let Some(abstract_func_idx) = abstract_func_idx {
			let abstract_method_id = self.record_operator_method_access(
				ctx,
				abstract_func_idx,
				operator.span,
			);
			return Ok(CompoundOperatorDispatch::Generic {
				abstract_method_id,
			});
		}

		match self.resolve_trait_method(trait_index, method_symbol, ty) {
			Some(OperatorMethod::Impl(func_idx)) => {
				Ok(CompoundOperatorDispatch::Concrete(
					self.record_operator_method_access(
						ctx,
						func_idx,
						operator.span,
					),
				))
			}
			// No compound-assignment operator's trait (`Add`..`Shr`) has a
			// bodied default method, so this is unreachable today — but if one
			// ever gains one, a default resolves exactly like an abstract
			// operand: dispatch waits for monomorphization.
			Some(OperatorMethod::Default(func_idx)) => {
				Ok(CompoundOperatorDispatch::Generic {
					abstract_method_id: self.record_operator_method_access(
						ctx,
						func_idx,
						operator.span,
					),
				})
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

	/// Unary counterpart of `build_operator_dispatch`, for `-x` (`Neg`),
	/// `^x` (`BitNot`) and `!x` (`Not`) — `EvalMode` gating, go-to-definition
	/// access recording, and diagnostic-on-failure all mirror the binary case
	/// exactly, just with one operand instead of two. Every `ast::UnaryOp`
	/// now has an overload trait, so `for_unary_op` always resolves.
	///
	/// TODO: revisit whether this and `build_operator_dispatch` can share
	/// more than `resolve_trait_method` — the binary/unary duplication here
	/// is mostly `Box::new([left, right])` vs. `Box::new([operand])` and
	/// `ExprKind::Binary` vs. `ExprKind::Unary`, which might collapse with a
	/// small enum over "1 or 2 operands".
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
		let (trait_index, method_symbol) = traits.for_unary_op(operator.inner);

		// Same reasoning as `build_operator_dispatch`'s equivalent branch: a
		// bare `Type::TypeParam` or `Type::AssocTypeProjection` isn't
		// concrete, so `resolve_trait_method` below can never resolve it —
		// deferred dispatch, resolved at MIR-lowering time once
		// monomorphization substitutes a concrete `Self`. An unbounded `T`
		// falls through to the same failure path below as a concrete type
		// with no matching impl.
		let deferred = self.abstract_operand_defers_operator(
			ty,
			trait_index,
			method_symbol,
		);
		if let Some(func_idx) = deferred {
			let abstract_method_id = self.record_operator_method_access(
				ctx,
				func_idx,
				operator.span,
			);
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
			Some(OperatorMethod::Impl(func_idx)) => {
				let method_id = self.record_operator_method_access(
					ctx,
					func_idx,
					operator.span,
				);
				Expression {
					kind: ExprKind::MethodCall {
						arguments: Box::new([operand]),
						id: method_id,
					},
					ty,
					span,
				}
			}
			Some(OperatorMethod::Default(func_idx)) => {
				let method_id = self.record_operator_method_access(
					ctx,
					func_idx,
					operator.span,
				);
				Expression {
					kind: ExprKind::GenericMethodCall {
						id: method_id,
						type_args: Box::new([ty]),
						arguments: Box::new([operand]),
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
		let operand = self.build_expression(
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
			// `^x` — dispatches through `BitNot`, mirroring `InvertSign` above:
			// a comptime-number operand has no concrete type to dispatch
			// against yet, so it stays a deferred `Unary` node
			// (`coerce_untyped_unary_expr` resolves it once a type is known);
			// everything else — primitive, struct, or typeset-bounded type
			// param / associated type — goes through real dispatch and lowers
			// to a `MethodCall`/`GenericMethodCall`, exactly like the binary
			// bitwise operators.
			ast::UnaryOp::BitNot if operand.ty.is_comptime_number() => {
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
			ast::UnaryOp::BitNot => {
				let ty = operand.ty;
				Ok(self.build_unary_operator_dispatch(
					ctx, operator, operand, ty, expr.span,
				))
			}
			// `!x` — dispatches through `Not`, exactly like `^x`/`-x`. Unlike
			// those two there is no comptime-number form: `!` is bool-only and
			// there is no `int -> bool` coercion, so a comptime-number operand
			// is a hard error (recovered as `bool`). Everything else — `bool`
			// resolving to the stdlib's `#[inline]` impl, a struct with its own
			// `impl Not`, or a typeset-bounded type param — goes through real
			// dispatch. `Comptime` mode leaves a plain `Unary` node behind for
			// `eval_const_expr` to fold, same as `Neg`/`BitNot`.
			ast::UnaryOp::Not if operand.ty.is_comptime_number() => {
				self.diagnostics
					.push(report_unary_operator_cannot_be_applied(
						self.formatter(ctx.resolve_context.namespace),
						UnaryOperatorCannotBeAppliedDiagnostic {
							file_id: ctx.resolve_context.file_id,
							operator,
							operand: Spanned {
								inner: operand.ty,
								span: expr.span,
							},
						},
					));
				Ok(Expression {
					kind: ExprKind::Unary {
						operator,
						operand: Box::new(operand),
					},
					ty: TypeIndex::BOOL,
					span: expr.span,
				})
			}
			ast::UnaryOp::Not => {
				let ty = operand.ty;
				Ok(self.build_unary_operator_dispatch(
					ctx, operator, operand, ty, expr.span,
				))
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
				// Both operands untyped: no concrete type yet to decide
				// native-vs-dispatch with. Coerce to the expected type when
				// one is known and hand off to the shared decision point
				// (`dispatch_binary_op`), or require an annotation when
				// nothing pins the type down.
				if access_ctx.expected_type != TypeIndex::INFER {
					let expected_type = access_ctx.expected_type;
					self.coerce_untyped_expr(ctx, &mut left, expected_type)?;
					self.coerce_untyped_expr(ctx, &mut right, expected_type)?;
					Ok(self.dispatch_binary_op(
						ctx,
						operator,
						left,
						right,
						expected_type,
						expr.span,
					))
				} else {
					self.diagnostics.push(report_type_annotation_required(
						SourceSpan::new(ctx.resolve_context.file_id, expr.span),
					));
					Err(())
				}
			}
			(l, right_type) if l.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut left, right_type)?;
				Ok(self.dispatch_binary_op(
					ctx, operator, left, right, right_type, expr.span,
				))
			}
			(left_type, r) if r.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut right, left_type)?;
				Ok(self.dispatch_binary_op(
					ctx, operator, left, right, left_type, expr.span,
				))
			}
			(left_type, right_type) if left_type == right_type => Ok(self
				.dispatch_binary_op(
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

	/// The result node for a comparison that lowers natively — a plain `Binary`
	/// with a `bool` result, as every primitive / `bool` / enum / pointer
	/// comparison does (no `MethodCall`; MIR emits `i32.eq`/`i32.lt_s` etc.
	/// directly). In `Runtime` mode it still records the operator's own span as
	/// an access against the `PartialEq` / `PartialOrd` method the operator
	/// conceptually resolves to for `operand_ty`, so hover / go-to-definition /
	/// find-references on `==` / `<` / … behave the same as on `+`. An
	/// `operand_ty` with no matching impl (an enum, a pointer, an abstract
	/// `Mem::Size`) records nothing.
	fn native_comparison(
		&mut self,
		ctx: &ExprContext,
		operator: Spanned<ast::BinaryOp>,
		left: Expression,
		right: Expression,
		operand_ty: TypeIndex,
		span: ast::TextSpan,
	) -> Expression {
		let method = match &ctx.mode {
			EvalMode::Runtime(traits) => traits
				.for_op(BinaryOp::from(operator.inner))
				.and_then(|(trait_index, method_symbol)| {
					self.resolve_trait_method(
						trait_index,
						method_symbol,
						operand_ty,
					)
				}),
			EvalMode::Comptime => None,
		};
		if let Some(method) = method {
			self.record_operator_method_access(
				ctx,
				method.function_index(),
				operator.span,
			);
		}
		Expression {
			kind: ExprKind::Binary {
				operator: Spanned {
					inner: BinaryOp::from(operator.inner),
					span: operator.span,
				},
				left: Box::new(left),
				right: Box::new(right),
			},
			ty: TypeIndex::BOOL,
			span,
		}
	}

	/// The single decision point `build_arithmetic_expr` and
	/// `build_bitwise_binary_expr` route every one of their "operands are
	/// now concretely typed `ty`" arms through — including the
	/// untyped-literal arms, once `coerce_untyped_expr` has pinned the
	/// literal down, so `1 + x` gets the native `Binary` path (see
	/// `ImplNode`) exactly like `y + x` does.
	///
	/// Eligibility (inlined below rather than its own predicate, having only
	/// this one call site) is the single source of truth for arithmetic's
	/// `is_numeric()` and bitwise's integer-or-`bool` (`&`/`|`/`^`) /
	/// integer-only (`<<`/`>>`) split: every numeric primitive implements
	/// the five arithmetic traits directly, every integer primitive (plus
	/// `bool`, whose `impl BitAnd`/`BitOr`/`BitXor` exist so `&`/`|`/`^`
	/// work as `&&`/`||`'s eager, non-short-circuit siblings) implements the
	/// bitwise ones, and none implement shifting except integers. `false`
	/// for any other operator or type (structs, `char`, float bitwise, ...)
	/// falls through to `ImplNode::MethodCall`.
	fn dispatch_binary_op(
		&mut self,
		ctx: &ExprContext,
		operator: Spanned<ast::BinaryOp>,
		left: Expression,
		right: Expression,
		ty: TypeIndex,
		span: ast::TextSpan,
	) -> Expression {
		let eligible = match operator.inner {
			ast::BinaryOp::Add
			| ast::BinaryOp::Sub
			| ast::BinaryOp::Mul
			| ast::BinaryOp::Div
			| ast::BinaryOp::Rem => ty.is_numeric(),
			ast::BinaryOp::BitAnd
			| ast::BinaryOp::BitOr
			| ast::BinaryOp::BitXor => ty.is_integer() || ty == TypeIndex::BOOL,
			ast::BinaryOp::LeftShift | ast::BinaryOp::RightShift => {
				ty.is_integer()
			}
			_ => false,
		};
		let impl_node = if eligible {
			ImplNode::Native
		} else {
			ImplNode::MethodCall
		};
		self.build_operator_dispatch(
			ctx, operator, left, right, ty, ty, span, impl_node,
		)
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
				Ok(self.native_comparison(
					ctx, operator, left, right, l, expr.span,
				))
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
				Ok(self.native_comparison(
					ctx, operator, left, right, l, expr.span,
				))
			}
			(l, ty) if l.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut left, ty)?;
				Ok(self.native_comparison(
					ctx, operator, left, right, ty, expr.span,
				))
			}
			(ty, r) if r.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut right, ty)?;
				Ok(self.native_comparison(
					ctx, operator, left, right, ty, expr.span,
				))
			}
			(l, r) if l == TypeIndex::BOOL && r == TypeIndex::BOOL => Ok(self
				.native_comparison(
					ctx,
					operator,
					left,
					right,
					TypeIndex::BOOL,
					expr.span,
				)),
			(left_type, right_type)
				if left_type == right_type
					&& (left_type.is_primitive()
						|| self.is_typeset_bounded_assoc_type(left_type)) =>
			{
				Ok(self.native_comparison(
					ctx, operator, left, right, left_type, expr.span,
				))
			}
			// Enums compare natively for equality only — every enum has an
			// integer repr, so `==`/`!=` are always meaningful. Ordering is
			// not: `<`/`>`/`<=`/`>=` on an enum fall through to
			// `build_operator_dispatch`, which requires an explicit
			// `impl PartialOrd for MyEnum` (matching Rust, where enums get
			// nothing without `#[derive]`).
			(left_type, right_type)
				if left_type == right_type
					&& matches!(
						operator.inner,
						ast::BinaryOp::Eq | ast::BinaryOp::NotEq
					) && matches!(
					self.types.resolve(left_type),
					Type::Enum { .. }
				) =>
			{
				Ok(self.native_comparison(
					ctx, operator, left, right, left_type, expr.span,
				))
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
				Ok(self.native_comparison(
					ctx, operator, left, right, left_type, expr.span,
				))
			}
			// Same type, but none of the built-in comparison arms above matched
			// (not a primitive / bool / enum / pointer pair) — a struct, slice,
			// tuple, etc. `==`/`!=` dispatch through `PartialEq` and
			// `<`/`<=`/`>`/`>=` through `PartialOrd` (`build_operator_dispatch`,
			// result type `bool`); a type with no such impl gets "operator
			// cannot be applied to type `T`".
			(left_type, right_type) if left_type == right_type => Ok(self
				.build_operator_dispatch(
					ctx,
					operator,
					left,
					right,
					left_type,
					TypeIndex::BOOL,
					expr.span,
					ImplNode::MethodCall,
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
				Ok(self.dispatch_binary_op(
					ctx, operator, left, right, ty, expr.span,
				))
			}
			(ty, r) if r.is_comptime_number() => {
				self.coerce_untyped_expr(ctx, &mut right, ty)?;
				Ok(self.dispatch_binary_op(
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
				.dispatch_binary_op(
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
