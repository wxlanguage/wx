//! `value as T`.
//!
//! A cast reinterprets a value on the Wasm stack without changing it, so it
//! is valid only between types held in the same Wasm value: integers of one
//! width class (`u8`, `i32`, `bool`, `char`, an enum with such a repr are all
//! `i32`), two pointers into the same memory, and a pointer and an integer of
//! its memory's `Size` width. Converting a value (`i32` to `i64`, an integer
//! to a float, `f32` to its bits) is an instruction's job, not a cast's. A
//! pointer cast may give up exclusivity (`*T as &T`) but never gain it
//! (`&T as *T`), so a shared pointer stays read-only. A literal is untyped,
//! so casting one gives it the target as its type: a number takes a scalar or
//! a pointer's `Size`, a string a shared byte slice or byte array of its
//! length, an array literal a shared slice or array of its length. `as _`
//! casts to the expected type.

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::{ARRAY_TARGETS_NOTE, BodyContext, STRING_TARGETS_NOTE};
use crate::ast::{self, Ownership, Spanned};
use crate::diagnostics::{DiagnosticCode, TextSpan};
use crate::tir::body::{ExprIdx, ExprKind};
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
		self.check_now(&obligations);
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
		// A string or array literal is cast to the shared array or slice it
		// could be coerced to; coercing it checks its elements and length.
		if source == TypeIndex::STRING || source == TypeIndex::ARRAY_LITERAL {
			let fits = self.static_target(target).is_some_and(|(of, ..)| {
				source == TypeIndex::ARRAY_LITERAL || of == TypeIndex::U8
			});
			if !fits {
				return self.report_invalid_cast(value, source, target, span);
			}
			self.coerce(value, target);
			if self.body.ty(value) == TypeIndex::ERROR {
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
		// A numeric literal is given the type it is cast to, or for a
		// pointer, the memory's `Size`.
		} else if self.cx.types.has_untyped(source) {
			let literal_target = match *self.cx.types.resolve(target) {
				Type::Pointer { memory, .. } => self.memory_size(memory),
				_ if target.is_numeric() => target,
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

	/// A cast reinterprets the value on the Wasm stack and never changes it,
	/// so source and target must be the same Wasm value. Changing the value
	/// (`i32` to `i64`, an integer to a float) is an instruction's job. A
	/// pointer is its memory's `Size`; between two pointers, the memory must
	/// match and a shared one never becomes exclusive.
	fn is_valid_cast(&mut self, source: TypeIndex, target: TypeIndex) -> bool {
		if source == target {
			return true;
		}
		match (
			*self.cx.types.resolve(source),
			*self.cx.types.resolve(target),
		) {
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
				self.is_pointer_integer(memory, target)
			}
			(_, Type::Pointer { memory, .. }) => {
				self.is_pointer_integer(memory, source)
			}
			_ => matches!(
				(self.wasm_value(source), self.wasm_value(target)),
				(Some(from), Some(to)) if from == to
			),
		}
	}

	/// Whether `other` is an integer a pointer into `memory` can be
	/// reinterpreted as: its memory's `Size`, or one held in the same Wasm
	/// value.
	fn is_pointer_integer(
		&mut self,
		memory: TypeIndex,
		other: TypeIndex,
	) -> bool {
		let size = self.memory_size(memory);
		if size == other {
			return true;
		}
		other.is_integer() && self.wasm_value(other) == self.wasm_value(size)
	}

	/// The Wasm value a scalar or an enum is held in on the stack; `None`
	/// for anything else.
	fn wasm_value(&self, ty: TypeIndex) -> Option<WasmValue> {
		if let Type::Enum { enum_index } = *self.cx.types.resolve(ty) {
			return WasmValue::of(self.cx.enum_repr(enum_index));
		}
		WasmValue::of(ty)
	}

	/// `memory`'s `Size` (`<memory as Memory>::Size`), normalized; `ERROR`
	/// when the stdlib declares no `Memory`.
	pub(super) fn memory_size(&mut self, memory: TypeIndex) -> TypeIndex {
		let Some(projection) = self.cx.memory_size(memory) else {
			return TypeIndex::ERROR;
		};
		self.normalized(projection, self.scope.env)
	}

	fn report_invalid_cast(
		&mut self,
		value: ExprIdx,
		source: TypeIndex,
		target: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let target_ty = target;
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
		let value_ty = self.body.ty(value);
		if self.wasm_value(value_ty).is_some()
			&& self.wasm_value(target_ty).is_some()
		{
			diagnostic = diagnostic.with_note(
				"a cast reinterprets a value without changing it, and these \
				 are held in different Wasm values; converting one into the \
				 other needs an instruction",
			);
		} else if value_ty == TypeIndex::STRING {
			diagnostic = diagnostic.with_note(STRING_TARGETS_NOTE);
		} else if value_ty == TypeIndex::ARRAY_LITERAL {
			diagnostic = diagnostic.with_note(ARRAY_TARGETS_NOTE);
		} else if self.cx.types.has_untyped(value_ty) {
			diagnostic = diagnostic
				.with_note("a literal is cast only to a number or a pointer");
		}
		self.cx.diagnostics.push(diagnostic);
		self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
	}
}

/// A Wasm value type: what a scalar is held in on the stack.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WasmValue {
	I32,
	I64,
	F32,
	F64,
}

impl WasmValue {
	/// The Wasm value a primitive scalar is held in; `None` for any other
	/// type.
	fn of(ty: TypeIndex) -> Option<Self> {
		Some(match ty {
			TypeIndex::U8
			| TypeIndex::I8
			| TypeIndex::U16
			| TypeIndex::I16
			| TypeIndex::U32
			| TypeIndex::I32
			| TypeIndex::BOOL
			| TypeIndex::CHAR => Self::I32,
			TypeIndex::U64 | TypeIndex::I64 => Self::I64,
			TypeIndex::F32 => Self::F32,
			TypeIndex::F64 => Self::F64,
			_ => return None,
		})
	}
}
