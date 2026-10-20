//! Blocks, statements, locals and control flow: `{ .. }`, `local`, `if`,
//! `loop`, labels, `break`, `continue` and `return`.
//!
//! Every block is a scope (`body::Scope`), entered before anything inside it
//! is checked. A value given to a scope (a block's result, a `break`, a
//! `return`) is held to the scope's type: the context's expectation when there
//! is one, else the type the first value settled on (`ScopeType`).

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::{BodyContext, ScopeType};
use crate::ast::{self, Separated, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{
	self, Body, ExprIdx, ExprKind, LabelIdx, LocalIdx, Scope, ScopeIdx,
	ScopeKind,
};
use crate::tir::defs::{FunctionIdx, Tier};
use crate::tir::resolutions::Referent;
use crate::tir::signatures::InferPolicy;
use crate::tir::types::TypeIndex;

impl BodyContext<'_, '_, '_, '_> {
	/// Checks a function's block as its body. Its parameters are the root
	/// scope's first locals, and the block's statements are written directly
	/// in the root scope, which `return` leaves.
	pub(in crate::tir) fn check_function(
		mut self,
		function_index: FunctionIdx,
		signature: &ast::FunctionSignature,
		block: &Spanned<ast::Expression>,
	) -> Body {
		let env = self.scope.env;
		let function = &self.cx.functions[usize::from(function_index)];
		let (params, return_type) =
			(function.params().to_vec(), function.return_type());
		// A type with a reported part in it expects nothing more.
		let return_type = self.normalized(return_type, env);
		let return_type = self.cx.types.collapse_error(return_type);
		self.enter_root(block.span, return_type);
		for (param, ty) in signature.params.iter().zip(params) {
			let param = &param.inner.inner;
			let ty = self.normalized(ty, env);
			let ty = self.cx.types.collapse_error(ty);
			self.declare_local(param.name, ty, param.mut_span);
		}
		let root = self.build_block_in(
			ScopeIdx::ROOT,
			block.inner.as_block_statements(),
			block.span,
		);
		self.body.finish(root)
	}

	/// Enters a new scope inside the current one; `leave_scope` returns to
	/// its parent.
	fn enter_scope(
		&mut self,
		kind: ScopeKind,
		label: Option<LabelIdx>,
		span: TextSpan,
		expected: TypeIndex,
	) -> ScopeIdx {
		let scope = self.body.push_scope(Scope {
			kind,
			parent: Some(self.current),
			label,
			span,
		});
		self.scope_types.push(ScopeType {
			expected,
			ty: TypeIndex::INFER,
		});
		self.current = scope;
		scope
	}

	fn leave_scope(&mut self, scope: ScopeIdx) {
		self.current = self.body.scope(scope).parent.unwrap();
	}

	/// Declares a local in the current scope. It is visible from here on, and
	/// hides any local of the same name declared before it.
	fn declare_local(
		&mut self,
		name: Spanned<SymbolU32>,
		ty: TypeIndex,
		mut_span: Option<TextSpan>,
	) -> LocalIdx {
		let local = self.body.push_local(body::Local { name, ty, mut_span });
		self.lookup.insert((self.current, name.inner), local);
		local
	}

	/// `{ .. }` in a scope of its own, held to `expected`.
	pub(super) fn build_block(
		&mut self,
		statements: &[Separated<Spanned<ast::Statement>>],
		expected: TypeIndex,
		label: Option<LabelIdx>,
		span: TextSpan,
	) -> ExprIdx {
		let scope = self.enter_scope(ScopeKind::Block, label, span, expected);
		let block = self.build_block_in(scope, statements, span);
		self.leave_scope(scope);
		block
	}

	/// The statements of a block, in `scope`, which is the current one. A
	/// last expression without a `;` is the block's result.
	fn build_block_in(
		&mut self,
		scope: ScopeIdx,
		statements: &[Separated<Spanned<ast::Statement>>],
		span: TextSpan,
	) -> ExprIdx {
		let (statements, result) = match statements.split_last() {
			Some((last, rest)) if last.separator.is_none() => {
				match &last.inner.inner {
					ast::Statement::Expression(result) => {
						(rest, Some(&**result))
					}
					ast::Statement::LocalDefinition { .. } => {
						(statements, None)
					}
				}
			}
			_ => (statements, None),
		};
		let (built, diverges) = self.build_statements(statements, result);
		let result = result.map(|result| {
			let hint = self.scope_hint(scope);
			let value = self.build(result, hint);
			self.give(scope, value, true);
			value
		});
		if result.is_none() && !diverges {
			self.give_unit(scope, span);
		}
		let ty = self.scope_type(scope);
		let statements = self.body.push_args(built);
		self.body.push(
			ExprKind::Block {
				scope,
				statements,
				result,
			},
			ty,
			span,
		)
	}

	/// Builds `statements`, and whether one of them diverges (is `!`). What
	/// follows the first that does, `result` included, is reported
	/// unreachable once, and still checked.
	fn build_statements(
		&mut self,
		statements: &[Separated<Spanned<ast::Statement>>],
		result: Option<&Spanned<ast::Expression>>,
	) -> (Vec<ExprIdx>, bool) {
		let mut built = Vec::with_capacity(statements.len());
		let mut diverges_at = None;
		for (at, statement) in statements.iter().enumerate() {
			let statement = self.build_statement(&statement.inner);
			if diverges_at.is_none()
				&& self.body.ty(statement) == TypeIndex::NEVER
			{
				diverges_at = Some(at);
			}
			built.push(statement);
		}
		let Some(at) = diverges_at else {
			return (built, false);
		};
		let start = statements
			.get(at + 1)
			.map(|statement| statement.inner.span.start)
			.or(result.map(|result| result.span.start));
		let end = result
			.map(|result| result.span.end)
			.or(statements.last().map(|statement| statement.inner.span.end));
		if let (Some(start), Some(end)) = (start, end) {
			self.cx.diagnostics.push(
				Diagnostic::warning()
					.with_code(DiagnosticCode::UnreachableCode.code())
					.with_message("unreachable code")
					.with_label(
						Label::primary(
							self.scope.file_id,
							TextSpan::new(start, end),
						)
						.with_message("this code will never be executed"),
					),
			);
		}
		(built, true)
	}

	fn build_statement(
		&mut self,
		statement: &Spanned<ast::Statement>,
	) -> ExprIdx {
		match &statement.inner {
			ast::Statement::Expression(expr) => {
				let value = self.build(expr, TypeIndex::INFER);
				let ty = self.body.ty(value);
				if self.cx.types.has_untyped(ty) {
					self.report_annotation_required(value);
				} else if ty != TypeIndex::UNIT
					&& ty != TypeIndex::NEVER
					&& ty != TypeIndex::ERROR
				{
					self.cx.diagnostics.push(
						Diagnostic::error()
							.with_code(DiagnosticCode::UnusedValue.code())
							.with_message("value must be used")
							.with_label(
								self.source_span(value)
									.primary_label()
									.with_message("value never used"),
							)
							.with_note(
								"if you don't need the value, drop it with \
								 an assignment to `_`",
							),
					);
				}
				value
			}
			ast::Statement::LocalDefinition { pattern, ty, value } => {
				self.build_local(pattern, ty.as_deref(), value, statement.span)
			}
		}
	}

	/// `local pattern [: ty] = value`. Without a written type the local
	/// takes the value's, which must be known: an untyped literal needs an
	/// annotation.
	fn build_local(
		&mut self,
		pattern: &Spanned<ast::BindPattern>,
		ty: Option<&Spanned<ast::TypeExpression>>,
		value: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> ExprIdx {
		let declared = ty.map(|ty| {
			let mut obligations = Vec::new();
			let ty = self.cx.resolve_type(
				&mut obligations,
				self.scope,
				ty,
				InferPolicy::Allow,
			);
			self.cx.check_now(&obligations);
			self.normalized(ty, self.scope.env)
		});
		let value = match declared {
			Some(declared) => self.check(value, declared),
			None => self.build(value, TypeIndex::INFER),
		};
		let value_ty = self.body.ty(value);
		// A written `_` in the type is learned from the value.
		let mut local_ty = match declared {
			Some(declared) => {
				self.cx.types.meet(declared, value_ty).unwrap_or(declared)
			}
			None => value_ty,
		};
		if self.cx.types.has_untyped(local_ty)
			|| self.cx.types.has_infer(local_ty)
		{
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeAnnotationRequired.code())
					.with_message("type annotation required")
					.with_label(
						Label::primary(self.scope.file_id, pattern.span)
							.with_message(
								"cannot infer the type of this local",
							),
					),
			);
			local_ty = TypeIndex::ERROR;
		}
		let ty = if value_ty == TypeIndex::NEVER {
			TypeIndex::NEVER
		} else {
			TypeIndex::UNIT
		};
		match &pattern.inner {
			ast::BindPattern::Binding { mut_span, name } => {
				let local = self.declare_local(*name, local_ty, *mut_span);
				self.body.push(
					ExprKind::LocalDeclaration { local, value },
					ty,
					span,
				)
			}
			// TODO: patterns, `_` among them, need their own representation.
			ast::BindPattern::Wildcard
			| ast::BindPattern::Destructure(_)
			| ast::BindPattern::Marked(_) => {
				self.report_unsupported(pattern.span, "a pattern");
				self.body.push(ExprKind::Error, ty, span)
			}
		}
	}

	/// `if condition { .. } else { .. }`. Without `else` the `if` is `()`, so
	/// its block must be too; when it is not, the `if` is an error, which its
	/// context does not report again. With one, the branches share a type: an untyped
	/// branch takes the other's, and `!` gives way to the other.
	pub(super) fn build_if_else(
		&mut self,
		condition: &Spanned<ast::Expression>,
		then_block: &Spanned<ast::Expression>,
		else_block: Option<&Spanned<ast::Expression>>,
		expected: TypeIndex,
		label: Option<LabelIdx>,
		span: TextSpan,
	) -> ExprIdx {
		let condition = self.check(condition, TypeIndex::BOOL);
		let Some(else_block) = else_block else {
			let then_block =
				self.build_branch(then_block, TypeIndex::INFER, label);
			let then_ty = self.body.ty(then_block);
			let mut ty = TypeIndex::UNIT;
			if then_ty != TypeIndex::UNIT
				&& then_ty != TypeIndex::NEVER
				&& then_ty != TypeIndex::ERROR
			{
				ty = TypeIndex::ERROR;
				let found = self.cx.type_formatter().display_type(then_ty);
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::MissingElseBlock.code())
						.with_message("`if` may be missing an `else` clause")
						.with_label(
							self.source_span(then_block)
								.primary_label()
								.with_message(format!(
									"expected `()`, found `{found}`"
								)),
						)
						.with_note("`if` without `else` evaluates to `()`"),
				);
			}
			return self.body.push(
				ExprKind::IfElse {
					condition,
					then_block,
					else_block: None,
				},
				ty,
				span,
			);
		};
		let then_block = self.build_branch(then_block, expected, label);
		let else_block = self.build_branch(else_block, expected, label);
		let ty = self.join_branches(then_block, else_block);
		self.body.push(
			ExprKind::IfElse {
				condition,
				then_block,
				else_block: Some(else_block),
			},
			ty,
			span,
		)
	}

	/// An `if`'s branch: a block, which takes the `if`'s label, or the `if` of
	/// an `else if`.
	fn build_branch(
		&mut self,
		branch: &Spanned<ast::Expression>,
		expected: TypeIndex,
		label: Option<LabelIdx>,
	) -> ExprIdx {
		match &branch.inner {
			ast::Expression::Block { statements } => {
				self.build_block(statements, expected, label, branch.span)
			}
			_ => self.build(branch, expected),
		}
	}

	/// The type two branches share, coercing an untyped one to the other's.
	fn join_branches(&mut self, first: ExprIdx, second: ExprIdx) -> TypeIndex {
		let (first_ty, second_ty) = (self.body.ty(first), self.body.ty(second));
		if first_ty == TypeIndex::NEVER {
			return second_ty;
		}
		if second_ty == TypeIndex::NEVER || first_ty == second_ty {
			return first_ty;
		}
		if first_ty == TypeIndex::ERROR || second_ty == TypeIndex::ERROR {
			return TypeIndex::ERROR;
		}
		match (
			self.cx.types.has_untyped(first_ty),
			self.cx.types.has_untyped(second_ty),
		) {
			(true, false) => {
				self.coerce(first, second_ty);
				second_ty
			}
			(false, true) => {
				self.coerce(second, first_ty);
				first_ty
			}
			// Two numeric literals are a float if either is.
			(true, true)
				if first_ty.is_comptime_number()
					&& second_ty.is_comptime_number() =>
			{
				TypeIndex::FLOAT
			}
			_ => {
				let diagnostic =
					self.report_type_mismatch(first_ty, second_ty, second);
				self.cx.diagnostics.push(diagnostic);
				TypeIndex::ERROR
			}
		}
	}

	/// `loop { .. }`: its statements are checked as statements, a last one
	/// without `;` included. Its type is what its `break`s give it.
	pub(super) fn build_loop(
		&mut self,
		block: &Spanned<ast::Expression>,
		expected: TypeIndex,
		label: Option<LabelIdx>,
		span: TextSpan,
	) -> ExprIdx {
		let scope = self.enter_scope(ScopeKind::Loop, label, span, expected);
		let (built, _) =
			self.build_statements(block.inner.as_block_statements(), None);
		self.leave_scope(scope);
		let ty = self.scope_type(scope);
		let statements = self.body.push_args(built);
		self.body
			.push(ExprKind::Loop { scope, statements }, ty, span)
	}

	/// `label: block { .. }`, `label: loop { .. }` or `label: if ..`.
	pub(super) fn build_labelled(
		&mut self,
		name: Spanned<SymbolU32>,
		labelled: &Spanned<ast::Expression>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let label = self.body.push_label(body::Label { name });
		match &labelled.inner {
			ast::Expression::Block { statements } => {
				self.build_block(statements, expected, Some(label), span)
			}
			ast::Expression::Loop { block } => {
				self.build_loop(block, expected, Some(label), span)
			}
			ast::Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => self.build_if_else(
				condition,
				then_block,
				else_block.as_deref(),
				expected,
				Some(label),
				span,
			),
			// The parser reports a label on anything else.
			_ => self.build(labelled, expected),
		}
	}

	/// `break`, leaving the nearest loop, or the scope `label` names, with
	/// `value` (`()` without one).
	pub(super) fn build_break(
		&mut self,
		label: Option<Spanned<SymbolU32>>,
		value: Option<&Spanned<ast::Expression>>,
		span: TextSpan,
	) -> ExprIdx {
		let Some(scope) = self.jump_target(label, span, Jump::Break) else {
			return self.body.push(ExprKind::Error, TypeIndex::NEVER, span);
		};
		let value = value.map(|value| {
			let hint = self.scope_hint(scope);
			let value = self.build(value, hint);
			self.give(scope, value, false);
			value
		});
		if value.is_none() {
			self.give_unit(scope, span);
		}
		self.body
			.push(ExprKind::Break { scope, value }, TypeIndex::NEVER, span)
	}

	/// `continue`, restarting the nearest loop, or the loop `label` names.
	pub(super) fn build_continue(
		&mut self,
		label: Option<Spanned<SymbolU32>>,
		span: TextSpan,
	) -> ExprIdx {
		let Some(scope) = self.jump_target(label, span, Jump::Continue) else {
			return self.body.push(ExprKind::Error, TypeIndex::NEVER, span);
		};
		self.body
			.push(ExprKind::Continue { scope }, TypeIndex::NEVER, span)
	}

	/// `return`, leaving the body with `value` (`()` without one).
	pub(super) fn build_return(
		&mut self,
		value: Option<&Spanned<ast::Expression>>,
		span: TextSpan,
	) -> ExprIdx {
		let value = value.map(|value| {
			let hint = self.scope_hint(ScopeIdx::ROOT);
			let value = self.build(value, hint);
			self.give(ScopeIdx::ROOT, value, false);
			value
		});
		if value.is_none() {
			self.give_unit(ScopeIdx::ROOT, span);
		}
		self.body
			.push(ExprKind::Return { value }, TypeIndex::NEVER, span)
	}

	/// The scope a `break` or `continue` leaves: the one whose label it names,
	/// else the nearest loop. Reports and gives `None` when there is none.
	fn jump_target(
		&mut self,
		label: Option<Spanned<SymbolU32>>,
		span: TextSpan,
		jump: Jump,
	) -> Option<ScopeIdx> {
		let mut at = Some(self.current);
		while let Some(scope) = at {
			let Scope {
				kind,
				parent,
				label: scope_label,
				..
			} = *self.body.scope(scope);
			let found = match (label, scope_label) {
				(Some(name), Some(scope_label)) => {
					self.body.label(scope_label).name.inner == name.inner
				}
				(Some(_), None) => false,
				(None, _) => kind == ScopeKind::Loop,
			};
			if found {
				if let (Some(name), Some(scope_label)) = (label, scope_label) {
					self.cx.resolutions.by_site.insert(
						(
							SourceSpan::new(self.scope.file_id, name.span),
							Tier::Value,
						),
						Referent::Label {
							owner: self.owner,
							label: scope_label,
						},
					);
				}
				if jump == Jump::Continue && kind != ScopeKind::Loop {
					self.cx.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::ContinueOutsideOfLoop.code(),
							)
							.with_message("`continue` can only restart a loop")
							.with_label(Label::primary(
								self.scope.file_id,
								span,
							)),
					);
					return None;
				}
				return Some(scope);
			}
			at = parent;
		}
		let diagnostic = match (label, jump) {
			(Some(name), _) => {
				let name_text = self.cx.strings.resolve(name.inner).unwrap();
				Diagnostic::error()
					.with_code(DiagnosticCode::UndeclaredLabel.code())
					.with_message(format!(
						"use of undeclared label `{name_text}`"
					))
					.with_label(
						Label::primary(self.scope.file_id, name.span)
							.with_message("undeclared label"),
					)
			}
			(None, Jump::Break) => Diagnostic::error()
				.with_code(DiagnosticCode::BreakOutsideOfLoop.code())
				.with_message("`break` outside of a loop or labelled block")
				.with_label(Label::primary(self.scope.file_id, span)),
			(None, Jump::Continue) => Diagnostic::error()
				.with_code(DiagnosticCode::ContinueOutsideOfLoop.code())
				.with_message("`continue` outside of a loop")
				.with_label(Label::primary(self.scope.file_id, span)),
		};
		self.cx.diagnostics.push(diagnostic);
		None
	}

	/// What a value given to `scope` is expected to be: the type an earlier
	/// value settled on, else the context's expectation.
	fn scope_hint(&self, scope: ScopeIdx) -> TypeIndex {
		let ScopeType { expected, ty } = self.scope_types[usize::from(scope)];
		if ty != TypeIndex::INFER { ty } else { expected }
	}

	/// The scope's type once its block is checked: `!` when nothing gave it
	/// a value.
	fn scope_type(&self, scope: ScopeIdx) -> TypeIndex {
		match self.scope_types[usize::from(scope)].ty {
			TypeIndex::INFER => TypeIndex::NEVER,
			ty => ty,
		}
	}

	/// Holds `value`, given to `scope`, to its type, or settles the scope's
	/// type on it when nothing is known yet. A `!` value settles nothing. An
	/// untyped value settles it only for a block's result
	/// (`allow_untyped`), which the context coerces later; a `break` or
	/// `return` needs a type.
	fn give(&mut self, scope: ScopeIdx, value: ExprIdx, allow_untyped: bool) {
		let ty = self.body.ty(value);
		if ty == TypeIndex::NEVER {
			return;
		}
		let hint = self.scope_hint(scope);
		let slot = &mut self.scope_types[usize::from(scope)];
		if hint != TypeIndex::INFER {
			if slot.ty == TypeIndex::INFER {
				slot.ty = hint;
			}
			self.expect(value, hint);
			return;
		}
		if self.cx.types.has_untyped(ty) && !allow_untyped {
			self.report_annotation_required(value);
			self.scope_types[usize::from(scope)].ty = TypeIndex::ERROR;
			return;
		}
		self.scope_types[usize::from(scope)].ty = ty;
	}

	/// `give` for a `()` with no node of its own: a block without a result,
	/// a bare `break` or `return`, reported at `span`.
	fn give_unit(&mut self, scope: ScopeIdx, span: TextSpan) {
		let hint = self.scope_hint(scope);
		let slot = &mut self.scope_types[usize::from(scope)];
		if hint == TypeIndex::INFER || hint == TypeIndex::UNIT {
			slot.ty = TypeIndex::UNIT;
			return;
		}
		slot.ty = TypeIndex::ERROR;
		if hint == TypeIndex::ERROR {
			return;
		}
		let diagnostic = self.mismatch_at(hint, TypeIndex::UNIT, span);
		self.cx.diagnostics.push(diagnostic);
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Jump {
	Break,
	Continue,
}
