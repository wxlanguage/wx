//! `value as T`.
//!
//! A cast converts between primitive scalars (every number to every number;
//! `bool` and `char` to and from integers), between an enum and an integer
//! (its discriminant), between
//! pointers into the same memory, and between a pointer and its memory's
//! `Size`. A pointer cast may give up exclusivity (`*T as &T`) but never gain
//! it (`&T as *T`), so a shared pointer stays read-only. `as _` casts to the
//! expected type.

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::BodyContext;
use crate::ast::{self, Ownership, Spanned};
use crate::diagnostics::{DiagnosticCode, TextSpan};
use crate::tir::body::{ExprIdx, ExprKind};
use crate::tir::defs::{BindingKey, MemberKind};
use crate::tir::operators::Scalar;
use crate::tir::signatures::InferPolicy;
use crate::tir::types::{Type, TypeIndex};

impl BodyContext<'_, '_, '_, '_> {
	pub(super) fn build_cast(
		&mut self,
		value: &Spanned<ast::Expression>,
		ty: &Spanned<ast::TypeExpression>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let mut obligations = Vec::new();
		let target = self.cx.resolve_type(
			&mut obligations,
			self.scope,
			ty,
			InferPolicy::Allow,
		);
		self.cx.check_now(&obligations);
		let mut target = self.normalized(target, self.scope.env);
		if target == TypeIndex::INFER {
			target = expected;
		}
		// The target guides what the value is built as (a literal, a generic
		// construction), but the value keeps its own type.
		let value = self.build(value, target);
		let source = self.body.ty(value);
		if target == TypeIndex::INFER || self.cx.types.has_infer(target) {
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeAnnotationRequired.code())
					.with_message("cannot infer the type to cast to")
					.with_label(
						Label::primary(self.scope.file_id, ty.span)
							.with_message("type annotation required"),
					),
			);
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		}
		if source == TypeIndex::ERROR || target == TypeIndex::ERROR {
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		}
		// A literal is given the type it is cast to, or for a pointer, the
		// memory's `Size`.
		if self.cx.types.has_untyped(source) {
			let literal_target = match *self.cx.types.resolve(target) {
				Type::Pointer { memory, .. } => self.memory_size(memory),
				_ if Scalar::from_type(target).is_some() => target,
				_ => TypeIndex::ERROR,
			};
			if literal_target == TypeIndex::ERROR {
				return self.report_invalid_cast(value, source, target, span);
			}
			self.coerce(value, literal_target);
		} else if !self.is_valid_cast(source, target) {
			return self.report_invalid_cast(value, source, target, span);
		}
		self.body.push(ExprKind::Cast { value }, target, span)
	}

	fn is_valid_cast(&mut self, source: TypeIndex, target: TypeIndex) -> bool {
		if source == target {
			return true;
		}
		if let (Some(from), Some(to)) =
			(Scalar::from_type(source), Scalar::from_type(target))
		{
			let numeric =
				|scalar: Scalar| scalar.is_integer() || scalar.is_float();
			return (numeric(from) && numeric(to))
				|| (from.is_integer()
					&& matches!(to, Scalar::Bool | Scalar::Char))
				|| (matches!(from, Scalar::Bool | Scalar::Char)
					&& to.is_integer());
		}
		match (
			*self.cx.types.resolve(source),
			*self.cx.types.resolve(target),
		) {
			(Type::Enum { .. }, _) => {
				Scalar::from_type(target).is_some_and(Scalar::is_integer)
			}
			(_, Type::Enum { .. }) => {
				Scalar::from_type(source).is_some_and(Scalar::is_integer)
			}
			(
				Type::Pointer {
					memory: from_memory,
					ownership: from_ownership,
					..
				},
				Type::Pointer {
					memory: to_memory,
					ownership: to_ownership,
					..
				},
			) => {
				from_memory == to_memory
					&& !(from_ownership == Ownership::Shared
						&& to_ownership == Ownership::Exclusive)
			}
			(Type::Pointer { memory, .. }, _) => {
				self.memory_size(memory) == target
			}
			(_, Type::Pointer { memory, .. }) => {
				self.memory_size(memory) == source
			}
			_ => false,
		}
	}

	/// `memory`'s `Size` (`<memory as Memory>::Size`), normalized; `ERROR`
	/// when the stdlib declares no `Memory`.
	fn memory_size(&mut self, memory: TypeIndex) -> TypeIndex {
		let Some(memory_trait) = self.cx.defs.intrinsics.memory else {
			return TypeIndex::ERROR;
		};
		let Some(size) = self.cx.strings.get("Size") else {
			return TypeIndex::ERROR;
		};
		let Some(MemberKind::AssociatedType(assoc_type_index)) = self
			.cx
			.defs
			.declared_trait_member(memory_trait, BindingKey::ty(size))
		else {
			return TypeIndex::ERROR;
		};
		let projection = self.cx.types.intern(Type::AssocTypeProjection {
			trait_index: memory_trait,
			assoc_type_index,
			base: memory,
		});
		self.normalized(projection, self.scope.env)
	}

	fn report_invalid_cast(
		&mut self,
		value: ExprIdx,
		source: TypeIndex,
		target: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let formatter = self.cx.type_formatter();
		let (source, target) = (
			formatter.display_type(source),
			formatter.display_type(target),
		);
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::InvalidCast.code())
			.with_message(format!("cannot cast `{source}` as `{target}`"))
			.with_label(
				Label::primary(self.scope.file_id, span)
					.with_message("invalid cast"),
			);
		if self.cx.types.has_untyped(self.body.ty(value)) {
			diagnostic = diagnostic
				.with_note("a literal is cast only to a number or a pointer");
		}
		self.cx.diagnostics.push(diagnostic);
		self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
	}
}
