//! Expression checking: lowers written expressions into a `Body`, with every
//! node typed. One checker for every expression, whatever owns it; constant
//! initializers are the first owner, function bodies follow.
//!
//! Operators are checked through their trait (`OperatorTraits`): the trait
//! decides whether the operator applies to a type. The node built for it is a
//! builtin `Binary`/`Unary` on a primitive scalar, and a method call otherwise.
//!
//! Untyped literals keep the pseudo-types `Integer`/`Float` until context
//! gives them one (`coerce`), which rewrites the subtree in place.

use codespan_reporting::diagnostic::Diagnostic;

use super::body::{Body, BodyBuilder, ExprIdx, ExprKind};
use super::defs::{
	BindingNamespace, DefKind, MemberKind, NamespaceIdx, TypesetIdx,
};
use super::literals::{CharLiteralError, parse_char_literal};
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::operators::{
	Scalar, is_builtin_binary, is_builtin_unary, is_comparison,
};
use super::paths::PathResolver;
use super::signatures::TypeContext;
use super::types::{TypeEnvIdx, TypeIndex};
use crate::ast::{self, BinaryOp, Spanned, UnaryOp};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::vfs::FileId;

/// Checks the expressions of one definition into a `Body`.
pub(super) struct BodyContext<'a, 'ast, 'ctx, 'dispatch> {
	cx: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
	body: BodyBuilder,
	file_id: FileId,
	namespace: NamespaceIdx,
	/// The type scope the expressions are written in: the root for a free
	/// constant, the impl's or trait's `Self` scope for an associated one.
	scope: TypeEnvIdx,
}

impl<'a, 'ast, 'ctx, 'dispatch> BodyContext<'a, 'ast, 'ctx, 'dispatch> {
	pub(super) fn new(
		cx: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
		file_id: FileId,
		namespace: NamespaceIdx,
		scope: TypeEnvIdx,
	) -> Self {
		Self {
			cx,
			body: BodyBuilder::default(),
			file_id,
			namespace,
			scope,
		}
	}

	/// Checks `expr` as the whole body, against `expected`.
	pub(super) fn check_body(
		mut self,
		expr: &Spanned<ast::Expression>,
		expected: TypeIndex,
	) -> Body {
		let expected = self.normalized(expected, self.scope);
		let root = self.check(expr, expected);
		self.body.finish(root)
	}

	/// Builds `expr` and holds it to `expected`: an untyped literal takes that
	/// type, any other type must equal it. `INFER` and `ERROR` expect nothing.
	fn check(
		&mut self,
		expr: &Spanned<ast::Expression>,
		expected: TypeIndex,
	) -> ExprIdx {
		let built = self.build(expr);
		self.expect(built, expected)
	}

	fn expect(&mut self, expr: ExprIdx, expected: TypeIndex) -> ExprIdx {
		if expected == TypeIndex::INFER || expected == TypeIndex::ERROR {
			return expr;
		}
		let actual = self.body.ty(expr);
		if is_untyped(actual) {
			self.coerce(expr, expected);
		} else if actual != TypeIndex::ERROR && actual != expected {
			let diagnostic = self.report_type_mismatch(expected, actual, expr);
			self.cx.diagnostics.push(diagnostic);
		}
		expr
	}

	/// Lowers `expr` without an expectation: an untyped literal stays untyped.
	fn build(&mut self, expr: &Spanned<ast::Expression>) -> ExprIdx {
		let span = expr.span;
		match &expr.inner {
			ast::Expression::Int { value } => {
				self.body
					.push(ExprKind::Int(*value), TypeIndex::INTEGER, span)
			}
			// The value is read from the source once the width is known.
			ast::Expression::Float => {
				self.body.push(ExprKind::Float(0.0), TypeIndex::FLOAT, span)
			}
			ast::Expression::True => {
				self.body.push(ExprKind::Bool(true), TypeIndex::BOOL, span)
			}
			ast::Expression::False => {
				self.body.push(ExprKind::Bool(false), TypeIndex::BOOL, span)
			}
			ast::Expression::Char => self.build_char(span),
			ast::Expression::Grouping { value } => self.build(value),
			ast::Expression::Unary { operator, operand } => {
				self.build_unary(*operator, operand, span)
			}
			ast::Expression::Binary {
				left,
				operator,
				right,
			} => self.build_binary(*operator, left, right, span),
			ast::Expression::Path(segments) => self.build_path(segments, span),
			ast::Expression::Error => {
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
			_ => self
				.body
				.push(ExprKind::Unsupported, TypeIndex::ERROR, span),
		}
	}

	fn build_char(&mut self, span: TextSpan) -> ExprIdx {
		let source = &self.cx.files.get(self.file_id).unwrap().source;
		match parse_char_literal(span.extract_str(source)) {
			Ok(value) => {
				self.body.push(ExprKind::Char(value), TypeIndex::CHAR, span)
			}
			Err(error) => {
				let message = match error {
					CharLiteralError::Empty => "empty character literal",
					CharLiteralError::TooLong => {
						"character literal may only contain one codepoint"
					}
				};
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidCharacterLiteral.code(),
						)
						.with_message(message)
						.with_label(self.source_span(span).primary_label()),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
		}
	}

	/// A value path. Only constants are modelled yet; a path the checker does
	/// not cover, including an associated item reached through a type, is
	/// `Unsupported` rather than an error.
	fn build_path(
		&mut self,
		segments: &[ast::PathSegment],
		span: TextSpan,
	) -> ExprIdx {
		let walk = PathResolver::new(self.cx.defs).walk_path(
			self.cx.diagnostics,
			self.cx.strings,
			self.file_id,
			self.namespace,
			segments,
			BindingNamespace::Value,
		);
		let Some(key) = walk.target.def_key() else {
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		if !walk.is_complete(segments) {
			return self.body.push(
				ExprKind::Unsupported,
				TypeIndex::ERROR,
				span,
			);
		}
		match key.symbol_kind(self.cx.defs) {
			DefKind::Const(const_index) => {
				let (ty, scope) = self.cx.constant_type(const_index);
				let ty = self.normalized(ty, scope);
				self.body.push(ExprKind::Const(const_index), ty, span)
			}
			_ => self
				.body
				.push(ExprKind::Unsupported, TypeIndex::ERROR, span),
		}
	}

	fn build_unary(
		&mut self,
		op: Spanned<UnaryOp>,
		operand: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> ExprIdx {
		let operand = self.build(operand);
		let ty = self.body.ty(operand);
		// Every unary operator answers its operand's type, so an untyped
		// operand leaves the node untyped until context coerces both.
		if is_untyped(ty) {
			return self.body.push(
				ExprKind::Unary {
					op: op.inner,
					operand,
				},
				ty,
				span,
			);
		}
		let (kind, ty) = self.select_unary(op, operand);
		self.body.push(kind, ty, span)
	}

	fn build_binary(
		&mut self,
		op: Spanned<BinaryOp>,
		left: &Spanned<ast::Expression>,
		right: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> ExprIdx {
		match op.inner {
			BinaryOp::And | BinaryOp::Or => {
				let lhs = self.check(left, TypeIndex::BOOL);
				let rhs = self.check(right, TypeIndex::BOOL);
				return self.body.push(
					ExprKind::Binary {
						op: op.inner,
						lhs,
						rhs,
					},
					TypeIndex::BOOL,
					span,
				);
			}
			BinaryOp::Assign
			| BinaryOp::AddAssign
			| BinaryOp::SubAssign
			| BinaryOp::MulAssign
			| BinaryOp::DivAssign
			| BinaryOp::RemAssign
			| BinaryOp::BitAndAssign
			| BinaryOp::BitOrAssign
			| BinaryOp::BitXorAssign
			| BinaryOp::LeftShiftAssign
			| BinaryOp::RightShiftAssign => {
				return self.body.push(
					ExprKind::Unsupported,
					TypeIndex::ERROR,
					span,
				);
			}
			_ => {}
		}
		let lhs = self.build(left);
		let rhs = self.build(right);
		let (left_ty, right_ty) = (self.body.ty(lhs), self.body.ty(rhs));
		// Both operands share one type (every operator trait takes
		// `rhs: Self`); a typed side gives it to an untyped one.
		let operand_ty = match (is_untyped(left_ty), is_untyped(right_ty)) {
			(true, true) => {
				if is_comparison(op.inner) {
					self.cx.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::ComparisonTypeAnnotationRequired
									.code(),
							)
							.with_message(
								"type annotation required to compare untyped literals",
							)
							.with_label(self.source_span(span).primary_label()),
					);
					return self.body.push(
						ExprKind::Error,
						TypeIndex::ERROR,
						span,
					);
				}
				let ty = if left_ty == TypeIndex::FLOAT
					|| right_ty == TypeIndex::FLOAT
				{
					TypeIndex::FLOAT
				} else {
					TypeIndex::INTEGER
				};
				return self.body.push(
					ExprKind::Binary {
						op: op.inner,
						lhs,
						rhs,
					},
					ty,
					span,
				);
			}
			(true, false) => {
				self.coerce(lhs, right_ty);
				right_ty
			}
			(false, true) => {
				self.coerce(rhs, left_ty);
				left_ty
			}
			(false, false) => {
				if left_ty != right_ty
					&& left_ty != TypeIndex::ERROR
					&& right_ty != TypeIndex::ERROR
				{
					let diagnostic =
						self.report_type_mismatch(left_ty, right_ty, rhs);
					self.cx.diagnostics.push(diagnostic);
					return self.body.push(
						ExprKind::Error,
						TypeIndex::ERROR,
						span,
					);
				}
				left_ty
			}
		};
		let (kind, ty) = self.select_binary(op, lhs, rhs, operand_ty);
		self.body.push(kind, ty, span)
	}

	/// The node for a unary operator on an operand of concrete type, and its
	/// type. Pushes nothing but call arguments, so a caller can rewrite a node
	/// in place with it.
	fn select_unary(
		&mut self,
		op: Spanned<UnaryOp>,
		operand: ExprIdx,
	) -> (ExprKind, TypeIndex) {
		let ty = self.body.ty(operand);
		let Some(lookup) = self.operator_impl(
			ty,
			self.cx.operators.unary(op.inner),
			operand,
			op.span,
			op.inner.as_str(),
			DiagnosticCode::UnaryOperatorCannotBeApplied,
		) else {
			return (ExprKind::Error, TypeIndex::ERROR);
		};
		if Scalar::from_type(ty)
			.is_some_and(|scalar| is_builtin_unary(op.inner, scalar))
		{
			let kind = ExprKind::Unary {
				op: op.inner,
				operand,
			};
			return (kind, ty);
		}
		(self.method_call(lookup, [operand]), ty)
	}

	/// The node for a binary operator on operands of concrete type `ty`, and
	/// its type. See `select_unary`.
	fn select_binary(
		&mut self,
		op: Spanned<BinaryOp>,
		lhs: ExprIdx,
		rhs: ExprIdx,
		ty: TypeIndex,
	) -> (ExprKind, TypeIndex) {
		let Some(lookup) = self.operator_impl(
			ty,
			self.cx.operators.binary(op.inner),
			lhs,
			op.span,
			op.inner.as_str(),
			DiagnosticCode::BinaryOperatorCannotBeApplied,
		) else {
			return (ExprKind::Error, TypeIndex::ERROR);
		};
		let result = if is_comparison(op.inner) {
			TypeIndex::BOOL
		} else {
			ty
		};
		if Scalar::from_type(ty)
			.is_some_and(|scalar| is_builtin_binary(op.inner, scalar))
		{
			let kind = ExprKind::Binary {
				op: op.inner,
				lhs,
				rhs,
			};
			return (kind, result);
		}
		(self.method_call(lookup, [lhs, rhs]), result)
	}

	/// Whether `ty` implements the operator's trait, and through what. `None`
	/// when it does not (reported here) or `ty` is already an error.
	fn operator_impl(
		&mut self,
		ty: TypeIndex,
		method: Option<super::operators::OperatorMethod>,
		operand: ExprIdx,
		op_span: TextSpan,
		op_text: &str,
		code: DiagnosticCode,
	) -> Option<(super::operators::OperatorMethod, TraitImplLookup)> {
		if ty == TypeIndex::ERROR {
			return None;
		}
		let found = match method {
			Some(method) => {
				match self.cx.find_trait_impl_query(
					self.scope,
					ty,
					method.trait_index,
				) {
					Ok(found) => found.map(|lookup| (method, lookup)),
					Err(error) => {
						let site = self.source_span(op_span);
						let _ = self.cx.report_unsolved::<()>(Err(error), site);
						return None;
					}
				}
			}
			None => None,
		};
		if found.is_none() {
			let message = format!(
				"operator `{op_text}` cannot be applied to type `{}`",
				self.cx.type_formatter().display_type(ty)
			);
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(code.code())
					.with_message(message)
					.with_label(
						self.source_span(self.body.span(operand))
							.primary_label(),
					)
					.with_label(self.source_span(op_span).secondary_label()),
			);
		}
		found
	}

	/// A call to the operator's method: the selected impl's own, or the trait's
	/// declaration when the receiver is abstract or the impl inherits a default.
	fn method_call<const N: usize>(
		&mut self,
		(method, lookup): (super::operators::OperatorMethod, TraitImplLookup),
		args: [ExprIdx; N],
	) -> ExprKind {
		let args = self.body.push_args(args);
		let TraitImplLookup::Concrete { impl_index, .. } = lookup else {
			return ExprKind::GenericMethodCall {
				method: method.method,
				args,
			};
		};
		match self
			.cx
			.defs
			.select_trait_member(impl_index, MemberKind::Method(method.method))
		{
			TraitMemberSelection::Impl(
				MemberKind::Method(selected) | MemberKind::Function(selected),
			) => ExprKind::MethodCall {
				method: selected,
				args,
			},
			TraitMemberSelection::Impl(_)
			| TraitMemberSelection::TraitDeclaration(_) => ExprKind::GenericMethodCall {
				method: method.method,
				args,
			},
		}
	}

	/// What a type means in `scope`: comparisons and literal coercion work on
	/// normalized types. A projection that does not normalize stays as written;
	/// whoever wrote it has reported why.
	fn normalized(&mut self, ty: TypeIndex, scope: TypeEnvIdx) -> TypeIndex {
		match self.cx.normalize_type_query(scope, ty) {
			Ok(normalized) => normalized,
			Err(_) => ty,
		}
	}

	/// The scalars a literal given type `target` must fit: `target` itself, or
	/// every member of every typeset bounding an abstract `target`, since any
	/// of them can be substituted for it. Each comes with the typeset member it
	/// stands for, if any. `None` when no literal can have type `target`.
	fn literal_targets(
		&mut self,
		target: TypeIndex,
	) -> Option<Vec<LiteralTarget>> {
		if let Some(scalar) = Scalar::from_type(target) {
			return Some(vec![LiteralTarget {
				scalar: Some(scalar),
				member: None,
			}]);
		}
		let mut targets = Vec::new();
		for index in 0..self.cx.defs.typesets.len() {
			let typeset = TypesetIdx::new(index as u32);
			let trait_index = self.cx.defs.typesets[index].trait_index;
			if !matches!(
				self.cx
					.find_trait_impl_query(self.scope, target, trait_index),
				Ok(Some(_))
			) {
				continue;
			}
			for member in self.cx.typeset_members(typeset).to_vec() {
				targets.push(LiteralTarget {
					scalar: Scalar::from_type(member.inner),
					member: Some((typeset, member)),
				});
			}
		}
		(!targets.is_empty()).then_some(targets)
	}

	/// Gives an untyped subtree the type `target`, checking each literal fits.
	/// Reports and leaves the offending node at `ERROR` when one does not.
	fn coerce(&mut self, expr: ExprIdx, target: TypeIndex) {
		if target == TypeIndex::ERROR {
			self.body.set_ty(expr, TypeIndex::ERROR);
			return;
		}
		let Some(targets) = self.literal_targets(target) else {
			return self.report_unable_to_coerce(expr, target);
		};
		match self.body.kind(expr) {
			ExprKind::Int(value) => {
				for fit in &targets {
					let fits = fit.scalar.is_some_and(|scalar| {
						if scalar.is_integer() {
							value <= max_magnitude(scalar, false)
						} else if scalar.is_float() {
							exact_in_float(value, mantissa_bits(scalar))
						} else {
							false
						}
					});
					if !fits {
						return self.report_int_misfit(
							expr, value, false, target, fit,
						);
					}
				}
				// An integer literal of float type is a float.
				if targets
					.iter()
					.all(|fit| fit.scalar.is_some_and(Scalar::is_float))
				{
					self.body.set_kind(expr, ExprKind::Float(value as f64));
				}
				self.body.set_ty(expr, target);
			}
			ExprKind::Float(_) => self.coerce_float(expr, target, &targets),
			ExprKind::Unary { op, operand } => {
				for fit in &targets {
					let fits = fit.scalar.is_some_and(|scalar| match op {
						UnaryOp::InvertSign => {
							scalar.is_signed() || scalar.is_float()
						}
						UnaryOp::BitNot => scalar.is_integer(),
						UnaryOp::Not => false,
					});
					if !fits {
						return self.report_misfit(expr, target, fit);
					}
				}
				// `-128` is in range for `i8` though `128` is not: a negated
				// literal is checked against the negative bound.
				match (op, self.body.kind(operand)) {
					(UnaryOp::InvertSign, ExprKind::Int(value)) => {
						for fit in &targets {
							let scalar = fit.scalar.unwrap();
							let fits = if scalar.is_integer() {
								value <= max_magnitude(scalar, true)
							} else {
								exact_in_float(value, mantissa_bits(scalar))
							};
							if !fits {
								return self.report_int_misfit(
									expr, value, true, target, fit,
								);
							}
						}
						if targets
							.iter()
							.all(|fit| fit.scalar.is_some_and(Scalar::is_float))
						{
							self.body.set_kind(
								operand,
								ExprKind::Float(value as f64),
							);
						}
						self.body.set_ty(operand, target);
					}
					_ => self.coerce(operand, target),
				}
				self.body.set_ty(expr, target);
			}
			ExprKind::Binary { op, lhs, rhs } => {
				debug_assert!(
					!is_comparison(op),
					"a comparison is never untyped"
				);
				self.coerce(lhs, target);
				self.coerce(rhs, target);
				// The operator could not be checked while its operands had no
				// type; it is now, and the node is rewritten in place.
				let op = Spanned {
					inner: op,
					span: self.body.span(expr),
				};
				let (kind, ty) = self.select_binary(op, lhs, rhs, target);
				self.body.set_kind(expr, kind);
				self.body.set_ty(expr, ty);
			}
			kind => unreachable!(
				"only literals and operators over them are untyped: {kind:?}"
			),
		}
	}

	/// Reads a float literal's value from its text at each target's width.
	fn coerce_float(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		targets: &[LiteralTarget],
	) {
		let source = &self.cx.files.get(self.file_id).unwrap().source;
		let text = self.body.span(expr).extract_str(source).to_owned();
		let nonzero = text.bytes().any(|b| b.is_ascii_digit() && b != b'0');
		let mut value = None;
		for fit in targets {
			let Some(scalar) = fit.scalar.filter(|scalar| scalar.is_float())
			else {
				return self.report_misfit(expr, target, fit);
			};
			let parsed = match scalar {
				Scalar::F32 => text.parse::<f32>().map(f64::from).ok(),
				_ => text.parse::<f64>().ok(),
			};
			// Malformed syntax was reported by the parser.
			let Some(parsed) = parsed else {
				return self.body.set_ty(expr, TypeIndex::ERROR);
			};
			let name = self.cx.type_formatter().display_type(scalar.ty());
			if parsed.is_infinite() {
				return self.push_error(
					DiagnosticCode::FloatLiteralOverflow,
					format!("float literal is too large for `{name}`"),
					expr,
				);
			}
			if parsed == 0.0 && nonzero {
				return self.push_error(
					DiagnosticCode::FloatLiteralUnderflow,
					format!(
						"float literal is too small to represent in `{name}`"
					),
					expr,
				);
			}
			value.get_or_insert(parsed);
		}
		self.body.set_kind(expr, ExprKind::Float(value.unwrap()));
		self.body.set_ty(expr, target);
	}

	/// An integer literal that does not fit `fit`: out of range for a plain
	/// integer target, not representable for a float one.
	fn report_int_misfit(
		&mut self,
		expr: ExprIdx,
		value: u64,
		negated: bool,
		target: TypeIndex,
		fit: &LiteralTarget,
	) {
		match fit.scalar {
			Some(scalar) if fit.member.is_none() && scalar.is_integer() => {
				let value = if negated {
					-(value as i128)
				} else {
					value as i128
				};
				self.report_out_of_range(expr, value, target);
			}
			Some(scalar) if fit.member.is_none() && scalar.is_float() => {
				let message = format!(
					"integer literal cannot be represented exactly by `{}`",
					self.cx.type_formatter().display_type(target)
				);
				self.push_error(
					DiagnosticCode::IntegerLiteralNotRepresentable,
					message,
					expr,
				);
			}
			_ => self.report_misfit(expr, target, fit),
		}
	}

	/// A literal `fit` cannot hold: unable to coerce to a scalar target, or a
	/// typeset member it does not fit for an abstract one.
	fn report_misfit(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		fit: &LiteralTarget,
	) {
		let Some((typeset, member)) = fit.member else {
			return self.report_unable_to_coerce(expr, target);
		};
		let def = &self.cx.defs.typesets[usize::from(typeset)];
		let typeset_name = self
			.cx
			.strings
			.resolve(
				self.cx.defs.traits[usize::from(def.trait_index)].name.inner,
			)
			.unwrap();
		let member_name = self.cx.type_formatter().display_type(member.inner);
		let label = self.source_span(self.body.span(expr)).primary_label();
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypesetBoundViolation.code())
				.with_message(format!(
					"literal is not representable by every member of typeset `{typeset_name}`"
				))
				.with_label(label.with_message(format!(
					"cannot be represented by `{member_name}`"
				)))
				.with_label(
					SourceSpan::new(def.file_id, member.span)
						.secondary_label()
						.with_message(format!(
							"`{member_name}` is a member here"
						)),
				),
		);
		self.body.set_ty(expr, TypeIndex::ERROR);
	}

	fn report_out_of_range(
		&mut self,
		expr: ExprIdx,
		value: i128,
		ty: TypeIndex,
	) {
		let message = format!(
			"literal `{value}` out of range for `{}`",
			self.cx.type_formatter().display_type(ty)
		);
		self.push_error(
			DiagnosticCode::IntegerLiteralOutOfRange,
			message,
			expr,
		);
	}

	fn report_unable_to_coerce(&mut self, expr: ExprIdx, target: TypeIndex) {
		let message = format!(
			"unable to coerce to type `{}`",
			self.cx.type_formatter().display_type(target)
		);
		self.push_error(DiagnosticCode::UnableToCoerce, message, expr);
	}

	/// Reports at `expr` and leaves it at `ERROR`, so nothing reports it again.
	fn push_error(
		&mut self,
		code: DiagnosticCode,
		message: String,
		expr: ExprIdx,
	) {
		let label = self.source_span(self.body.span(expr)).primary_label();
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(code.code())
				.with_message(message)
				.with_label(label),
		);
		self.body.set_ty(expr, TypeIndex::ERROR);
	}

	fn report_type_mismatch(
		&self,
		expected: TypeIndex,
		actual: TypeIndex,
		expr: ExprIdx,
	) -> Diagnostic<FileId> {
		let formatter = self.cx.type_formatter();
		Diagnostic::error()
			.with_code(DiagnosticCode::TypeMistmatch.code())
			.with_message("type mismatch")
			.with_label(
				self.source_span(self.body.span(expr))
					.primary_label()
					.with_message(format!(
						"expected `{}`, found `{}`",
						formatter.display_type(expected),
						formatter.display_type(actual)
					)),
			)
	}

	fn source_span(&self, span: TextSpan) -> SourceSpan {
		SourceSpan::new(self.file_id, span)
	}
}

/// One scalar a literal must fit; see `BodyContext::literal_targets`.
struct LiteralTarget {
	/// `None` for a typeset member that is not a primitive scalar, which no
	/// literal fits.
	scalar: Option<Scalar>,
	member: Option<(TypesetIdx, Spanned<TypeIndex>)>,
}

fn mantissa_bits(scalar: Scalar) -> u32 {
	if scalar == Scalar::F32 { 24 } else { 53 }
}

fn is_untyped(ty: TypeIndex) -> bool {
	ty == TypeIndex::INTEGER || ty == TypeIndex::FLOAT
}

/// The largest literal magnitude `scalar` holds, written plainly or negated.
fn max_magnitude(scalar: Scalar, negated: bool) -> u64 {
	let bits = scalar.bits();
	if !scalar.is_signed() {
		return if negated { 0 } else { u64::MAX >> (64 - bits) };
	}
	let positive = (1u64 << (bits - 1)) - 1;
	if negated { positive + 1 } else { positive }
}

/// Whether `value` survives the trip through a float with `mantissa` bits.
fn exact_in_float(value: u64, mantissa: u32) -> bool {
	value == 0
		|| 64 - value.leading_zeros() - value.trailing_zeros() <= mantissa
}
