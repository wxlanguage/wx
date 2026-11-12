//! Deciding what building a body left open: what reads values (constants'
//! lengths, representability, equalities between constants left as written)
//! and a match's usefulness. A constant's body is built before any value
//! exists, so its obligations are decided after every constant body is built;
//! a function's or global's are decided right after it is built.

use codespan_reporting::diagnostic::Diagnostic;

use super::{BodyContext, StaticTarget, TypeEquality};
use crate::diagnostics::DiagnosticCode;
use crate::tir::body::{ExprIdx, ExprKind, ExprObligation, Obligations};
use crate::tir::decls::ConstIdx;
use crate::tir::literals::{CharMiss, ConcreteType, IntegerMiss, UntypedValue};
use crate::tir::solver::{NormalizationDepth, RewriteFlags};
use crate::tir::types::{Type, TypeIndex};

impl BodyContext<'_> {
	/// Decides what building the body left open, once every constant body is
	/// built and every declaration is checked, reading values, and reports
	/// what fails.
	pub(in crate::tir) fn decide(&mut self, obligations: Obligations) {
		for obligation in &obligations.types {
			self.sema
				.check_obligation(self.strings, obligation)
				.expect("every signature and every constant body exists");
		}
		for check in obligations.exprs {
			match check {
				ExprObligation::Equal { expr, expected } => {
					self.decide_equal(expr, expected);
				}
				ExprObligation::StaticLength {
					expr,
					target,
					length,
				} => self.decide_static_length(expr, target, length),
				ExprObligation::Match(expr) => {
					self.check_match_usefulness(expr)
				}
				ExprObligation::Representable { expr, target } => {
					self.decide_representable(expr, target)
				}
			}
		}
	}

	/// Decides a recorded `Equal`, now that constants have values.
	fn decide_equal(&mut self, expr: ExprIdx, expected: TypeIndex) {
		let actual = self.body.ty(expr);
		let span = self.body.span(expr);
		match self.equality(expected, actual, RewriteFlags::ALL, span) {
			Ok(TypeEquality::Equal) => {}
			Ok(_) => self.report_mismatch(expr, expected),
			Err(()) => self.body.set_ty(expr, TypeIndex::ERROR),
		}
	}

	/// Decides a recorded `Representable`: the untyped constant `expr` names
	/// has a value of its kind representable as `target`, as a literal of that
	/// value would. A constant without a value reports itself.
	fn decide_representable(&mut self, expr: ExprIdx, target: TypeIndex) {
		// Without a value, a representability clause in scope said it is.
		let Some((constant, Some(value))) = self.untyped_value(expr, target)
		else {
			return;
		};
		let kind = self.sema.constants[usize::from(constant)].ty;
		let name = self.sema.decls.name(constant).inner;
		let name = self.strings.resolve(name).unwrap().to_owned();
		let at = self.source_span(expr);
		for concrete in
			self.sema.concrete_types(self.scope.assumption_env, target)
		{
			let held = if kind == TypeIndex::CHAR_LITERAL {
				u32::try_from(value)
					.map_err(|_| CharMiss::OutOfRange)
					.and_then(|code_point| concrete.holds_char(code_point))
					.map_err(|miss| match miss {
						CharMiss::OutOfRange => IntegerMiss::OutOfRange,
						CharMiss::WrongKind => IntegerMiss::WrongKind,
					})
			} else {
				concrete.holds_integer(value)
			};
			let Err(miss) = held else {
				continue;
			};
			let ty =
				self.sema.type_formatter(self.strings).display_type(target);
			let diagnostic = match (concrete, miss) {
				(ConcreteType::Member(typeset, member), _) => {
					self.sema.report_typeset_member(
						self.strings,
						format_args!("constant `{name}`"),
						typeset,
						member,
						at,
					)
				}
				(ConcreteType::Target(_), IntegerMiss::OutOfRange) => {
					Diagnostic::error()
						.with_code(
							DiagnosticCode::IntegerLiteralOutOfRange.code(),
						)
						.with_message(format!(
							"constant `{name}` cannot be represented as `{ty}`"
						))
						.with_label(at.primary_label().with_message(format!(
							"its value `{value}` is out of range for `{ty}`"
						)))
				}
				(ConcreteType::Target(_), IntegerMiss::Inexact) => {
					Diagnostic::error()
						.with_code(
							DiagnosticCode::IntegerLiteralNotRepresentable
								.code(),
						)
						.with_message(format!(
							"constant `{name}` cannot be represented exactly \
							 as `{ty}`"
						))
						.with_label(
							at.primary_label().with_message(format!(
								"its value is `{value}`"
							)),
						)
				}
				(ConcreteType::Target(_), IntegerMiss::WrongKind) => {
					self.report_unable_to_coerce(expr, target)
				}
			};
			return self.reject(expr, diagnostic);
		}
	}

	/// The constant an untyped `expr` names, and its value. `None` when it has
	/// none here: it failed (reported where it is), or it is a trait's constant
	/// over a type not known here and no representability clause in scope says
	/// it is representable as `target` (reported); `Some` with no value when
	/// one does.
	fn untyped_value(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
	) -> Option<(ConstIdx, Option<i128>)> {
		let (constant, args) = match self.body.kind(expr) {
			ExprKind::Const { constant, .. } => (constant, Vec::new()),
			ExprKind::AbstractConst {
				constant,
				type_args,
			} => (constant, self.sema.generic_args.types(type_args).to_vec()),
			_ => unreachable!("only a constant's representability is decided"),
		};
		let env = self.scope.assumption_env;
		match self
			.sema
			.untyped_value(self.strings, env, constant, &args)
			.ok()?
		{
			UntypedValue::Known(value) => Some((constant, Some(value))),
			UntypedValue::Failed => None,
			UntypedValue::Abstract => {
				let subject = self.normalized(args[0]);
				if self
					.sema
					.assumed_representable(
						self.strings,
						env,
						subject,
						constant,
						target,
					)
					.ok()?
				{
					return Some((constant, None));
				}
				let diagnostic = self.sema.report_unrepresentable_constant(
					self.strings,
					self.source_span(expr),
					(subject, constant),
					target,
					None,
					None,
				);
				self.sema.diagnostics.push(diagnostic);
				None
			}
		}
	}

	/// Decides a literal's length against its array's, reading values.
	pub(super) fn decide_static_length(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		length: TypeIndex,
	) {
		let Some(StaticTarget {
			length: Some(target_length),
			..
		}) = self.static_target(target)
		else {
			unreachable!("a literal with a length becomes an array")
		};
		let scope = self.scope.assumption_env;
		let target_now = self.sema.normalize(
			self.strings,
			scope,
			target_length,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		);
		let length_now = self.sema.normalize(
			self.strings,
			scope,
			length,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		);
		let (expected, actual) = match (target_now, length_now) {
			(Ok(expected), Ok(actual)) => (expected, actual),
			// Reported where the constant is.
			_ => return,
		};
		let (Type::Value { bits }, Type::Value { bits: length }) = (
			*self.sema.types.resolve(expected),
			*self.sema.types.resolve(actual),
		) else {
			return;
		};
		if bits == length {
			return;
		}
		let target =
			self.sema.type_formatter(self.strings).display_type(target);
		let literal = match self.body.kind(expr) {
			ExprKind::String(_) => {
				format!("this string literal is {length} bytes long")
			}
			ExprKind::Const { .. } => {
				format!("this constant holds {length} elements")
			}
			_ => format!("this array literal has {length} elements"),
		};
		self.push_error(
			DiagnosticCode::ArraySizeMismatch,
			format!("{literal}, but `{target}` holds {bits}"),
			expr,
		);
	}
}
