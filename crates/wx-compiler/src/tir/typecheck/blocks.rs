//! Blocks, statements, locals and control flow: `{ .. }`, `local`, `if`,
//! `loop`, labels, `break`, `continue` and `return`.
//!
//! Every block is a scope (`body::Scope`), entered before anything inside it
//! is checked. A value given to a scope (a block's result, a `break`, a
//! `return`) is held to the scope's type: the context's expectation when there
//! is one, else the type the first value settled on (`ScopeType`).

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::calls::{NamedMatch, NamedOwner};
use super::patterns::PatternContext;
use super::{BodyBuilder, ScopeType};
use crate::ast::{self, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextOffset, TextSpan};
use crate::symbols::Keyword;
use crate::tir::body::{
	self, Body, ExprIdx, ExprKind, ExprObligation, LabelIdx, LocalIdx,
	Obligations, ParamIdx, Scope, ScopeIdx, ScopeKind,
};
use crate::tir::decls::{FunctionIdx, report_duplicate_parameter};
use crate::tir::resolutions::{AccessKind, Reference, Site};
use crate::tir::signatures::InferPolicy;
use crate::tir::types::{Type, TypeIndex};

impl BodyBuilder<'_, '_> {
	/// Checks a function's block as its body. Its named parameters are the
	/// root scope's first locals (`Body::params` says which parameter each
	/// is), and the block's statements are written directly in the root
	/// scope, which `return` leaves.
	pub(in crate::tir) fn check_function(
		mut self,
		function_index: FunctionIdx,
		signature: &ast::FunctionSignature,
		block: ast::BlockId,
	) -> (Body, Obligations) {
		let function = &self.sema.functions[usize::from(function_index)];
		let (param_types, return_type) =
			(function.param_types, function.return_type);
		// A type with a reported part in it expects nothing more.
		let return_type = self.context().normalized(return_type);
		let return_type = self.sema.types.collapse_error(return_type);
		let span = self.ast().block_span(block);
		self.enter_root(span, return_type);
		for (at, param) in self.ast().list(signature.params).iter().enumerate()
		{
			let ty = self.sema.types.list(param_types)[at];
			let ty = self.context().normalized(ty);
			let ty = self.sema.types.collapse_error(ty);
			// A parameter whose name is missing (reported by the parser)
			// binds nothing.
			let binding = param.binding;
			let local = (!binding.is_missing()).then(|| {
				let mut_span =
					binding.mut_at.map(|at| Keyword::Mut.span_at(at));
				self.declare_local(binding.name, ty, mut_span)
			});
			self.body.push_param(local);
		}
		self.build_block_in(ScopeIdx::ROOT, block, span);
		(self.body, self.obligations)
	}

	/// Enters a new scope inside the current one; `leave_scope` returns to
	/// its parent.
	pub(super) fn enter_scope(
		&mut self,
		kind: ScopeKind,
		label: Option<LabelIdx>,
		span: TextSpan,
		expected: TypeIndex,
	) -> ScopeIdx {
		let scope = self.body.push_scope(kind, Some(self.current), label, span);
		self.scope_types.push(ScopeType {
			expected,
			ty: TypeIndex::INFER,
		});
		self.current = scope;
		scope
	}

	pub(super) fn leave_scope(&mut self, scope: ScopeIdx) {
		self.current = self.body.scope(scope).parent.unwrap();
	}

	/// Declares a local in the current scope. It is visible from here on, and
	/// hides any local of the same name declared before it.
	pub(super) fn declare_local(
		&mut self,
		name: Spanned<SymbolU32>,
		ty: TypeIndex,
		mut_span: Option<TextSpan>,
	) -> LocalIdx {
		let local = self
			.body
			.push_local(self.current, body::Local { name, ty, mut_span });
		self.lookup.insert((self.current, name.inner), local);
		local
	}

	/// `{ .. }` in a scope of its own, of `kind`, held to `expected`: a
	/// written `block` (`ScopeKind::Block`), or braces a construct owns
	/// (`ScopeKind::Body`), which take no label.
	pub(super) fn build_block(
		&mut self,
		kind: ScopeKind,
		block: ast::BlockId,
		expected: TypeIndex,
		label: Option<LabelIdx>,
		span: TextSpan,
	) -> ExprIdx {
		let scope = self.enter_scope(kind, label, span, expected);
		let block = self.build_block_in(scope, block, span);
		self.leave_scope(scope);
		block
	}

	/// The statements of a block, in `scope`, which is the current one. Its
	/// tail, the last expression written without a `;`, is its result.
	fn build_block_in(
		&mut self,
		scope: ScopeIdx,
		block: ast::BlockId,
		span: TextSpan,
	) -> ExprIdx {
		let ast = self.ast();
		let ast::Block { statements, tail } = ast.block(block);
		let (statements, result) = (ast.list(statements), tail);
		let (built, flow) = self.build_statements(statements, result, span.end);
		let result = result.map(|result| {
			let hint = self.scope_hint(scope);
			let value = match self.loop_of_body(scope) {
				Some(target) => self.build_state(target, result, hint),
				None => self.build(result, hint),
			};
			self.give(scope, value, true)
		});
		if result.is_none() {
			match flow {
				StatementFlow::Convergent => self.give_unit(scope, span),
				StatementFlow::Divergent => {}
				// Whether it reaches its end is not known, so neither is
				// what it gives there.
				StatementFlow::Unknown => {
					let slot = &mut self.scope_types[usize::from(scope)];
					if slot.ty == TypeIndex::INFER {
						slot.ty = TypeIndex::ERROR;
					}
				}
			}
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

	/// Builds `statements`, and how control flows through them
	/// (`StatementFlow`). What follows the first divergent one (of type `!`),
	/// `result` included, is reported unreachable once, and still checked. Each `local` among them
	/// opens the rest of the block, up to `end`, as a scope of its own; the
	/// block's own scope closes them all when it is left.
	fn build_statements(
		&mut self,
		statements: &[ast::StmtId],
		result: Option<ast::ExprId>,
		block_end: TextOffset,
	) -> (Vec<ExprIdx>, StatementFlow) {
		let ast = self.ast();
		let mut built = Vec::with_capacity(statements.len());
		let mut divergent_at = None;
		let mut unknown = false;
		for (at, &statement) in statements.iter().enumerate() {
			let statement = self.build_statement(statement, block_end);
			match self.body.ty(statement) {
				TypeIndex::NEVER if divergent_at.is_none() => {
					divergent_at = Some(at);
				}
				TypeIndex::ERROR => unknown = true,
				_ => {}
			}
			built.push(statement);
		}
		let Some(at) = divergent_at else {
			let flow = if unknown {
				StatementFlow::Unknown
			} else {
				StatementFlow::Convergent
			};
			return (built, flow);
		};
		let start = statements
			.get(at + 1)
			.map(|&statement| ast.statement_span(statement).start)
			.or(result.map(|result| ast.expr_span(result).start));
		let end = result.map(|result| ast.expr_span(result).end).or(statements
			.last()
			.map(|&statement| ast.statement_span(statement).end));
		if let (Some(start), Some(end)) = (start, end) {
			self.sema.diagnostics.push(
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
		(built, StatementFlow::Divergent)
	}

	fn build_statement(
		&mut self,
		statement: ast::StmtId,
		block_end: TextOffset,
	) -> ExprIdx {
		let ast = self.ast();
		match ast.statement(statement) {
			ast::Statement::Expression(expr) => {
				self.build_expression_statement(expr)
			}
			ast::Statement::LocalDefinition { pattern, ty, value } => self
				.build_local(
					pattern,
					ty,
					value,
					ast.statement_span(statement),
					block_end,
				),
		}
	}

	/// An expression as a statement: its value, if it has one, must be used.
	fn build_expression_statement(&mut self, expr: ast::ExprId) -> ExprIdx {
		let value = self.build(expr, TypeIndex::INFER);
		let ty = self.body.ty(value);
		if self.sema.types.needs_context(ty) {
			self.report_annotation_required(value);
		} else if ty != TypeIndex::UNIT
			&& ty != TypeIndex::NEVER
			&& ty != TypeIndex::ERROR
		{
			let at = self.context().source_span(value);
			self.sema.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::UnusedValue.code())
					.with_message("value must be used")
					.with_label(
						at.primary_label().with_message("value never used"),
					)
					.with_note(
						"if you don't need the value, drop it with \
						 an assignment to `_`",
					),
			);
		}
		value
	}

	/// `(value: ty)`: the value checked as a local of that type would be. The
	/// ascription leaves no node of its own.
	pub(super) fn build_ascription(
		&mut self,
		value: ast::ExprId,
		ty: ast::TypeId,
	) -> ExprIdx {
		let ty = self.builder.resolve_value_type(
			self.sema,
			&mut self.obligations.types,
			self.scope,
			ty,
			InferPolicy::Allow,
		);
		let ty = self.context().normalized(ty);
		self.check(value, ty)
	}

	/// `local pattern [: ty] = value`. Without a written type the local
	/// takes the value's, which must be known: an untyped literal needs an
	/// annotation. What the pattern binds is declared in the rest of the
	/// block, up to `block_end`, a scope opened after the value is built
	/// (`ScopeKind::Remainder`).
	fn build_local(
		&mut self,
		pattern: ast::PatId,
		ty: Option<ast::TypeId>,
		value: ast::ExprId,
		span: TextSpan,
		block_end: TextOffset,
	) -> ExprIdx {
		let declared = self.declared_type(ty);
		let value = self.build(value, declared);
		let (value, mut local_ty) = self.complete(value, declared);
		if !self.is_known(local_ty, declared) {
			let span = self.ast().pattern_span(pattern);
			self.report_uninferred(span, "local");
			local_ty = TypeIndex::ERROR;
		}
		let ty = if self.body.ty(value) == TypeIndex::NEVER {
			TypeIndex::NEVER
		} else {
			TypeIndex::UNIT
		};
		self.enter_scope(
			ScopeKind::Remainder,
			None,
			TextSpan::new(span.end, block_end),
			TypeIndex::INFER,
		);
		let pattern =
			self.check_pattern(pattern, local_ty, &mut PatternContext::local());
		self.body
			.push(ExprKind::LocalDeclaration { pattern, value }, ty, span)
	}

	/// The type a binding is declared with: as written, its `_` parts
	/// `INFER`, or all of it `INFER` when none is written.
	fn declared_type(&mut self, ty: Option<ast::TypeId>) -> TypeIndex {
		let Some(ty) = ty else {
			return TypeIndex::INFER;
		};
		let ty = self.builder.resolve_value_type(
			self.sema,
			&mut self.obligations.types,
			self.scope,
			ty,
			InferPolicy::Allow,
		);
		self.context().normalized(ty)
	}

	/// Holds `value`, built with `declared` as its hint, to `declared`, and
	/// completes `declared` with its type: what the bindings it is given to
	/// are, as far as `is_known` says.
	fn complete(
		&mut self,
		value: ExprIdx,
		declared: TypeIndex,
	) -> (ExprIdx, TypeIndex) {
		let value = self.expect(value, declared);
		let actual = self.body.ty(value);
		let ty = self.sema.types.meet(declared, actual).unwrap_or(declared);
		(value, ty)
	}

	/// Whether `ty`, `declared` completed by a value, is known enough for a
	/// binding: no part left unknown or untyped (a literal), and no data in
	/// no memory that the value brought. A written slice or array is
	/// reported where it is written, as held by value.
	fn is_known(&self, ty: TypeIndex, declared: TypeIndex) -> bool {
		let types = &self.sema.types;
		!types.has_infer(ty)
			&& !types.has_const_kind(ty)
			&& (!types.has_unplaced(ty) || types.has_unplaced(declared))
	}

	/// E2002 at `span`, a binding (`what`) whose type is not known.
	fn report_uninferred(&mut self, span: TextSpan, what: &str) {
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypeAnnotationRequired.code())
				.with_message("type annotation required")
				.with_label(
					Label::primary(self.scope.file_id, span).with_message(
						format!("cannot infer the type of this {what}"),
					),
				),
		);
	}

	/// `match scrutinee { pattern => expr | { .. }, .. }`. Each arm's bindings
	/// are declared in a scope of its own, around its body. The arms share a
	/// type as an `if`'s branches do. The arms must cover every value, and each
	/// must match one the arms before it do not (`exhaustiveness`).
	pub(super) fn build_match(
		&mut self,
		scrutinee: ast::ExprId,
		arms: &[ast::MatchArm],
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let scrutinee = self.build(scrutinee, TypeIndex::INFER);
		let mut scrutinee_ty = self.body.ty(scrutinee);
		if self.sema.types.needs_context(scrutinee_ty) {
			self.report_annotation_required(scrutinee);
			scrutinee_ty = TypeIndex::ERROR;
		}
		let mut built = Vec::with_capacity(arms.len());
		let ast = self.ast();
		for &ast::MatchArm { pattern, body } in arms {
			// Its bindings are in scope after its pattern.
			let scope = self.enter_scope(
				ScopeKind::Body,
				None,
				TextSpan::new(
					ast.pattern_span(pattern).end,
					ast.branch_span(body).end,
				),
				TypeIndex::INFER,
			);
			let pattern = self.check_pattern(
				pattern,
				scrutinee_ty,
				&mut PatternContext::arm(),
			);
			let body = self.build_branch(body, expected);
			self.leave_scope(scope);
			built.push(body::Arm {
				scope,
				pattern,
				body,
			});
		}
		let bodies: Vec<ExprIdx> = built.iter().map(|arm| arm.body).collect();
		let ty = self.join_arms(&bodies);
		let arms = self.body.push_arms(built);
		let expr =
			self.body
				.push(ExprKind::Match { scrutinee, arms }, ty, span);
		// An arm may compare with a constant, whose value is not known yet.
		self.obligations.exprs.push(ExprObligation::Match(expr));
		expr
	}

	/// The type a match's arms share: the first typed one's, which every
	/// untyped arm takes; `!` gives way to the others, and with no arm the
	/// match is `!`. While the arms are untyped they join among themselves
	/// (`const_int` with `{float}` is `{float}`) and the match waits for its
	/// context, which coerces each of them.
	fn join_arms(&mut self, arms: &[ExprIdx]) -> TypeIndex {
		let Some(&first) = arms
			.iter()
			.find(|&&arm| self.body.ty(arm) != TypeIndex::NEVER)
		else {
			return TypeIndex::NEVER;
		};
		let mut joined = first;
		let mut ty = self.body.ty(first);
		for &arm in arms {
			if arm == first || self.body.ty(arm) == TypeIndex::NEVER {
				continue;
			}
			ty = self.join_branches(joined, arm);
			if ty == TypeIndex::ERROR {
				return ty;
			}
			// An untyped arm that gave way keeps the typed one as the one the
			// rest join.
			if !self.sema.types.needs_context(self.body.ty(arm)) {
				joined = arm;
			}
		}
		// `join_branches` coerced only the arm a typed one met (`joined`);
		// the untyped arms joined before it still wait for a type
		// (`0, 1, g()` with `g() -> u8`). The match is typed now, so its
		// context will not coerce them.
		if ty != TypeIndex::ERROR && !self.sema.types.needs_context(ty) {
			for &arm in arms {
				if self.sema.types.needs_context(self.body.ty(arm)) {
					self.coerce(arm, ty);
				}
			}
		}
		ty
	}

	/// `if condition { .. } else { .. }`. Without `else` the `if` is `()`, so
	/// its block must be too; when it is not, the `if` is an error, which its
	/// context does not report again. With one, the branches share a type: an untyped
	/// branch takes the other's, and `!` gives way to the other.
	pub(super) fn build_if_else(
		&mut self,
		condition: ast::ExprId,
		then_block: ast::BlockId,
		else_block: Option<ast::Branch>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let condition = self.check(condition, TypeIndex::BOOL);
		let then_span = self.ast().block_span(then_block);
		let Some(else_block) = else_block else {
			let then_block = self.build_block(
				ScopeKind::Body,
				then_block,
				TypeIndex::INFER,
				None,
				then_span,
			);
			let then_ty = self.body.ty(then_block);
			let mut ty = TypeIndex::UNIT;
			if then_ty != TypeIndex::UNIT
				&& then_ty != TypeIndex::NEVER
				&& then_ty != TypeIndex::ERROR
			{
				ty = TypeIndex::ERROR;
				let found = self
					.sema
					.type_formatter(self.builder.strings)
					.display_type(then_ty);
				let at = self.context().source_span(then_block);
				self.sema.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::MissingElseBlock.code())
						.with_message("`if` may be missing an `else` clause")
						.with_label(at.primary_label().with_message(format!(
							"expected `()`, found `{found}`"
						)))
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
		let then_block = self.build_block(
			ScopeKind::Body,
			then_block,
			expected,
			None,
			then_span,
		);
		let else_block = self.build_branch(else_block, expected);
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

	/// An `else` branch or a match arm's body: the construct's own block,
	/// the `if` of an `else if`, or an arm's expression. Each is held to
	/// `expected` as a block's result is (`give`), before the `if` or `match`
	/// holding it exists, so `A => p` and `A => { p }` are checked alike.
	fn build_branch(
		&mut self,
		branch: ast::Branch,
		expected: TypeIndex,
	) -> ExprIdx {
		match branch {
			ast::Branch::Block(block) => {
				let span = self.ast().block_span(block);
				self.build_block(ScopeKind::Body, block, expected, None, span)
			}
			ast::Branch::Expression(expr) => self.check(expr, expected),
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
			self.sema.types.needs_context(first_ty),
			self.sema.types.needs_context(second_ty),
		) {
			(true, false) => {
				self.coerce(first, second_ty);
				second_ty
			}
			(false, true) => {
				self.coerce(second, first_ty);
				first_ty
			}
			// A character literal with an integer one is a character, and two
			// numeric literals are a float if either is.
			(true, true)
				if first_ty == TypeIndex::CONST_CHAR
					&& second_ty == TypeIndex::CONST_INT
					|| first_ty == TypeIndex::CONST_INT
						&& second_ty == TypeIndex::CONST_CHAR =>
			{
				TypeIndex::CONST_CHAR
			}
			(true, true)
				if first_ty.is_numeric_const_kind()
					&& second_ty.is_numeric_const_kind() =>
			{
				TypeIndex::CONST_FLOAT
			}
			_ => {
				let diagnostic = self
					.context()
					.report_type_mismatch(first_ty, second_ty, second);
				self.sema.diagnostics.push(diagnostic);
				TypeIndex::ERROR
			}
		}
	}

	/// `loop :l (a: A, b) = first { body }`, or `loop { body }` with the
	/// state `()`. The slots are the loop scope's locals, in order, declared
	/// before `first` is built outside the loop (it sees neither them nor the
	/// loop's label) and typed by it: a slot without a written type takes its
	/// part of `first`'s. The body is a block of its own, whose result is the
	/// next state. The loop's type is what its `break`s give it.
	pub(super) fn build_loop(
		&mut self,
		header: Option<ast::LoopHeaderId>,
		block: ast::BlockId,
		expected: TypeIndex,
		label: Option<LabelIdx>,
		span: TextSpan,
	) -> ExprIdx {
		let ast = self.ast();
		let header = header.map(|header| ast.loop_header(header));
		// The slots are in scope after the first state, up to the loop's end.
		let start = header
			.map_or(span.start, |header| ast.expr_span(header.initializer).end);
		let outer = self.current;
		let scope = self.enter_scope(
			ScopeKind::Loop,
			label,
			TextSpan::new(start, span.end),
			expected,
		);
		let first = header.map(|header| {
			self.declare_slots(ast.list(header.state));
			self.current = outer;
			let first = self.build_first_state(scope, header.initializer);
			self.current = scope;
			first
		});
		let state = self.state_type(scope);
		let block_span = ast.block_span(block);
		let body =
			self.build_block(ScopeKind::Body, block, state, None, block_span);
		self.leave_scope(scope);
		// A first state that never arrives never starts the loop.
		let ty = match first {
			Some(first) if self.body.ty(first) == TypeIndex::NEVER => {
				TypeIndex::NEVER
			}
			_ => self.scope_type(scope),
		};
		self.body
			.push(ExprKind::Loop { scope, first, body }, ty, span)
	}

	/// Declares a loop's slots in the current scope, the loop's, each of its
	/// written type or `INFER` until the first state gives it one. A slot
	/// whose name the parser reported missing keeps its position, an `ERROR`
	/// that no name finds, so the state is one too. A repeated name is
	/// reported, and finds the first.
	fn declare_slots(&mut self, slots: &[ast::FunctionParam]) {
		for slot in slots {
			let ty = self.declared_type(slot.ty);
			let binding = slot.binding;
			if binding.is_missing() {
				let local = body::Local {
					name: binding.name,
					ty: TypeIndex::ERROR,
					mut_span: None,
				};
				self.body.push_local(self.current, local);
				continue;
			}
			let mut_span = binding.mut_at.map(|at| Keyword::Mut.span_at(at));
			let first = (self.body.scope_locals(self.current))
				.map(|slot| self.body.local(slot).name)
				.find(|first| first.inner == binding.name.inner);
			let Some(first) = first else {
				self.declare_local(binding.name, ty, mut_span);
				continue;
			};
			self.sema.diagnostics.push(report_duplicate_parameter(
				self.builder.strings,
				self.scope.file_id,
				binding.name,
				first,
			));
			let local = body::Local {
				name: binding.name,
				ty,
				mut_span,
			};
			self.body.push_local(self.current, local);
		}
	}

	/// The first state, completing the slots' types as a `local`'s value
	/// does its type: a slot whose part is still not known is reported, and
	/// is `ERROR`. One that never arrives completes nothing, silently.
	fn build_first_state(
		&mut self,
		scope: ScopeIdx,
		initializer: ast::ExprId,
	) -> ExprIdx {
		let declared = self.state_type(scope);
		let value = self.build_state(scope, initializer, declared);
		let (value, state) = self.complete(value, declared);
		let arrives = self.body.ty(value) != TypeIndex::NEVER;
		let slots: Vec<LocalIdx> = self.body.scope_locals(scope).collect();
		let parts = match (slots.len(), *self.sema.types.resolve(state)) {
			(1, _) => vec![state],
			(count, Type::Tuple { elements }) if elements.len() == count => {
				self.sema.types.list(elements).to_vec()
			}
			_ => vec![TypeIndex::ERROR; slots.len()],
		};
		for (slot, mut ty) in slots.into_iter().zip(parts) {
			let local = *self.body.local(slot);
			if !arrives || !self.is_known(ty, local.ty) {
				if arrives {
					self.report_uninferred(local.name.span, "slot");
				}
				ty = TypeIndex::ERROR;
			}
			self.body.set_local_ty(slot, ty);
		}
		value
	}

	/// The type of a loop's state, from its slots: `()` for none, a slot's
	/// type for one, else the tuple of them. `ERROR` once a part is.
	fn state_type(&mut self, scope: ScopeIdx) -> TypeIndex {
		let types: Vec<TypeIndex> = (self.body.scope_locals(scope))
			.map(|slot| self.body.local(slot).ty)
			.collect();
		let ty = match *types {
			[ty] => ty,
			_ => self.sema.types.intern_tuple(&types),
		};
		self.sema.types.collapse_error(ty)
	}

	/// The loop whose next state `scope`'s result is: its body's.
	fn loop_of_body(&self, scope: ScopeIdx) -> Option<ScopeIdx> {
		let Scope { kind, parent, .. } = *self.body.scope(scope);
		let parent = parent.filter(|_| kind == ScopeKind::Body)?;
		(self.body.scope(parent).kind == ScopeKind::Loop).then_some(parent)
	}

	/// A state given to the loop `target`: its first, its body's result or a
	/// `continue`'s value, positionally (`expected` hints it) or by name. The
	/// caller holds it to the state.
	fn build_state(
		&mut self,
		target: ScopeIdx,
		value: ast::ExprId,
		expected: TypeIndex,
	) -> ExprIdx {
		let ast = self.ast();
		match ast.expr(value) {
			ast::Expression::NamedList { arguments, .. } => self
				.build_named_state(
					target,
					ast.list(arguments),
					ast.expr_span(value),
				),
			_ => self.build(value, expected),
		}
	}

	/// `({ b: 2, a })` as the state of the loop `target`: each value gives the
	/// parameter of its name (`match_names`), held to its type.
	fn build_named_state(
		&mut self,
		target: ScopeIdx,
		arguments: &[ast::NamedArgument],
		span: TextSpan,
	) -> ExprIdx {
		let slots: Vec<LocalIdx> = self.body.scope_locals(target).collect();
		let names: Vec<Option<SymbolU32>> = (slots.iter())
			.map(|&slot| self.body.local(slot).name.inner)
			.map(|name| (name != Keyword::Error.symbol()).then_some(name))
			.collect();
		let owner = NamedOwner::Loop(target);
		let matches = self.match_names(&names, arguments, owner, span);
		let mut types = vec![TypeIndex::ERROR; slots.len()];
		let mut values = Vec::with_capacity(matches.len());
		for &NamedMatch { argument, param } in &matches {
			let argument = &arguments[argument as usize];
			let slot = slots[param as usize];
			self.sema.resolutions.record(
				Site::Label(SourceSpan::new(
					self.scope.file_id,
					argument.name.span,
				)),
				Reference::Local {
					owner: self.owner,
					local: slot,
					access: AccessKind::Write,
				},
			);
			let ty = self.body.local(slot).ty;
			let value = self.build_named_argument(argument, ty);
			let value = self.expect(value, ty);
			types[param as usize] = self.body.ty(value);
			values.push(value);
		}
		if matches.len() != arguments.len() || matches.len() != slots.len() {
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		}
		// One parameter's state is its value.
		if let [value] = *values {
			return value;
		}
		let ty = self.sema.types.intern_tuple(&types);
		let ty = self.sema.types.collapse_error(ty);
		let order = self.body.push_permutation(
			matches.iter().map(|given| ParamIdx::new(given.param)),
		);
		self.pack(values, order, ty, span)
	}

	/// The values of a named list whose names mean nothing here, each built
	/// against nothing, standing in an error node for the list.
	pub(super) fn build_named_values(
		&mut self,
		arguments: &[ast::NamedArgument],
		span: TextSpan,
	) -> ExprIdx {
		for argument in arguments {
			self.build_named_argument(argument, TypeIndex::ERROR);
		}
		self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
	}

	/// `break`, leaving the nearest loop, or the scope `label` names, with
	/// `value` (`()` without one).
	pub(super) fn build_break(
		&mut self,
		label: Option<Spanned<SymbolU32>>,
		value: Option<ast::ExprId>,
		span: TextSpan,
	) -> ExprIdx {
		let Some(scope) = self.jump_target(label, span, Jump::Break) else {
			// Its value is still checked, against nothing.
			if let Some(value) = value {
				self.build(value, TypeIndex::ERROR);
			}
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		let value = value.map(|value| {
			let hint = self.scope_hint(scope);
			let value = self.build(value, hint);
			self.give(scope, value, false)
		});
		if value.is_none() {
			self.give_unit(scope, span);
		}
		self.body
			.push(ExprKind::Break { scope, value }, TypeIndex::NEVER, span)
	}

	/// `continue`, restarting the nearest loop, or the loop `label` names,
	/// with `value` as its next state (`()` without one).
	pub(super) fn build_continue(
		&mut self,
		label: Option<Spanned<SymbolU32>>,
		value: Option<ast::ExprId>,
		span: TextSpan,
	) -> ExprIdx {
		let Some(scope) = self.jump_target(label, span, Jump::Continue) else {
			// Its value is still checked, against nothing.
			if let Some(value) = value {
				let ast = self.ast();
				match ast.expr(value) {
					ast::Expression::NamedList { arguments, .. } => self
						.build_named_values(
							ast.list(arguments),
							ast.expr_span(value),
						),
					_ => self.build(value, TypeIndex::ERROR),
				};
			}
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		let state = self.state_type(scope);
		let value = value.map(|value| {
			let value = self.build_state(scope, value, state);
			self.expect(value, state)
		});
		if value.is_none()
			&& state != TypeIndex::UNIT
			&& state != TypeIndex::ERROR
		{
			let diagnostic =
				self.context().mismatch_at(state, TypeIndex::UNIT, span);
			self.sema.diagnostics.push(diagnostic);
		}
		self.body.push(
			ExprKind::Continue { scope, value },
			TypeIndex::NEVER,
			span,
		)
	}

	/// `return`, leaving the body with `value` (`()` without one).
	pub(super) fn build_return(
		&mut self,
		value: Option<ast::ExprId>,
		span: TextSpan,
	) -> ExprIdx {
		let value = value.map(|value| {
			let hint = self.scope_hint(ScopeIdx::ROOT);
			let value = self.build(value, hint);
			self.give(ScopeIdx::ROOT, value, false)
		});
		if value.is_none() {
			self.give_unit(ScopeIdx::ROOT, span);
		}
		self.body
			.push(ExprKind::Return { value }, TypeIndex::NEVER, span)
	}

	/// The scope a `break` or `continue` leaves: the one whose label it names,
	/// else the nearest loop. Reports and gives `None` when there is none,
	/// and gives `None` silently for a label not written yet (`break :`),
	/// which the parser reported.
	fn jump_target(
		&mut self,
		label: Option<Spanned<SymbolU32>>,
		span: TextSpan,
		jump: Jump,
	) -> Option<ScopeIdx> {
		if label.is_some_and(|name| name.inner == Keyword::Error.symbol()) {
			return None;
		}
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
				// A `break` leaves the nearest written `block` or loop, a
				// `continue` the nearest loop.
				(None, _) => match jump {
					Jump::Break => {
						matches!(kind, ScopeKind::Block | ScopeKind::Loop)
					}
					Jump::Continue => kind == ScopeKind::Loop,
				},
			};
			if found {
				if let (Some(name), Some(scope_label)) = (label, scope_label) {
					self.sema.resolutions.record(
						Site::Label(SourceSpan::new(
							self.scope.file_id,
							name.span,
						)),
						Reference::Label {
							owner: self.owner,
							label: scope_label,
						},
					);
				}
				if jump == Jump::Continue && kind != ScopeKind::Loop {
					self.sema.diagnostics.push(
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
				let name_text =
					self.builder.strings.resolve(name.inner).unwrap();
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
				.with_message("`break` outside of a loop or `block`")
				.with_label(Label::primary(self.scope.file_id, span)),
			(None, Jump::Continue) => Diagnostic::error()
				.with_code(DiagnosticCode::ContinueOutsideOfLoop.code())
				.with_message("`continue` outside of a loop")
				.with_label(Label::primary(self.scope.file_id, span)),
		};
		self.sema.diagnostics.push(diagnostic);
		None
	}

	/// What a value given to `scope` is expected to be: the type an earlier
	/// value settled on, else the context's expectation.
	fn scope_hint(&self, scope: ScopeIdx) -> TypeIndex {
		let ScopeType { expected, ty, .. } =
			self.scope_types[usize::from(scope)];
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
	/// type on it when nothing is known yet, and returns the node the scope
	/// is given (`expect`'s). A `!` value settles nothing. An untyped value
	/// settles it only for a block's result (`allow_untyped`), which the
	/// context coerces later; a `break` or `return` needs a type.
	#[must_use]
	fn give(
		&mut self,
		scope: ScopeIdx,
		value: ExprIdx,
		allow_untyped: bool,
	) -> ExprIdx {
		let ty = self.body.ty(value);
		if ty == TypeIndex::NEVER {
			return value;
		}
		let hint = self.scope_hint(scope);
		let slot = &mut self.scope_types[usize::from(scope)];
		if hint != TypeIndex::INFER {
			if slot.ty == TypeIndex::INFER {
				slot.ty = hint;
			}
			return self.expect(value, hint);
		}
		if self.sema.types.needs_context(ty) && !allow_untyped {
			self.report_annotation_required(value);
			self.scope_types[usize::from(scope)].ty = TypeIndex::ERROR;
			return value;
		}
		self.scope_types[usize::from(scope)].ty = ty;
		value
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
		let diagnostic =
			self.context().mismatch_at(hint, TypeIndex::UNIT, span);
		self.sema.diagnostics.push(diagnostic);
	}
}

/// How control flows through a block's statements.
#[derive(Clone, Copy)]
enum StatementFlow {
	/// It reaches past the last one, where the block's result or `()` is.
	Convergent,
	/// It never gets past one of type `!`.
	Divergent,
	/// Not known: one is an error, which might have been either (a jump
	/// with no target, a misspelled call of a `-> !` function).
	Unknown,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Jump {
	Break,
	Continue,
}
