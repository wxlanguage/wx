//! Places and assignment: `p.*`, `value.field`, `place.&`, and `=`/`op=`.
//!
//! A place is a location in linear memory, reached through a pointer: `p.*`,
//! and a field of a place. Everything else is a value, even when it names a
//! location (a local, or a field of one), and is assigned through `Assign`; a
//! place is written through `Store`. A global's name is a handle, written
//! through `GlobalMut::set`, so it is never the target of `=`. Reading a place
//! is a `Load`, pushed only where its value is used, so `.&` and the left of
//! `=` take the place itself.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::{BodyContext, SelectedMethod};
use crate::ast::{self, BinaryOp, Ownership, Spanned};
use crate::diagnostics::{DiagnosticCode, TextSpan};
use crate::tir::body::{ExprIdx, ExprKind, Place, PlaceIdx, PlaceKind};
use crate::tir::defs::Visibility;
use crate::tir::operators::is_primitive_binary;
use crate::tir::types::{Substitution, Type, TypeIndex};

/// What the left of `=`, the operand of `.&` or the object of `.field` is.
#[derive(Clone, Copy)]
enum Operand {
	Place(PlaceIdx),
	Value(ExprIdx),
}

/// What defines an `op=`.
enum CompoundMethod {
	/// The primitive scalar's operator.
	Primitive,
	/// The operator's method: the selected impl's, or the trait's declaration.
	Method(SelectedMethod),
}

impl BodyContext<'_, '_, '_, '_> {
	/// `p.*` or `value.field` where its value is used.
	pub(super) fn build_read(
		&mut self,
		expr: &Spanned<ast::Expression>,
	) -> ExprIdx {
		match self.build_operand(expr) {
			Operand::Place(place) => {
				let ty = self.body.place(place).ty;
				self.body.push(ExprKind::Load(place), ty, expr.span)
			}
			Operand::Value(value) => value,
		}
	}

	/// `expr` as a place when it is one, else as a value.
	fn build_operand(&mut self, expr: &Spanned<ast::Expression>) -> Operand {
		match &expr.inner {
			ast::Expression::Grouping { value } => self.build_operand(value),
			ast::Expression::Deref { pointer } => {
				self.build_deref(pointer, expr.span)
			}
			ast::Expression::ObjectAccess { object, member } => {
				self.build_field(object, *member, expr.span)
			}
			_ => Operand::Value(self.build(expr, TypeIndex::INFER)),
		}
	}

	/// `pointer.*`: the place the pointer points at, in its memory, writable
	/// when the pointer is exclusive.
	fn build_deref(
		&mut self,
		pointer: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> Operand {
		let pointer = self.build(pointer, TypeIndex::INFER);
		let pointer_ty = self.body.ty(pointer);
		match *self.cx.types.resolve(pointer_ty) {
			Type::Pointer {
				to,
				memory,
				ownership,
			} => Operand::Place(self.body.push_place(Place {
				kind: PlaceKind::Deref { pointer },
				ty: to,
				memory,
				mutable: ownership == Ownership::Exclusive,
				span,
			})),
			Type::Error => Operand::Value(self.body.push(
				ExprKind::Error,
				TypeIndex::ERROR,
				span,
			)),
			_ => {
				let found = self.cx.type_formatter().display_type(pointer_ty);
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::CannotDerefNonPointer.code())
						.with_message(format!(
							"type `{found}` cannot be dereferenced"
						))
						.with_label(
							self.source_span(pointer)
								.primary_label()
								.with_message("not a pointer"),
						),
				);
				Operand::Value(self.body.push(
					ExprKind::Error,
					TypeIndex::ERROR,
					span,
				))
			}
		}
	}

	/// `object.member`, a struct's field: a place when the object is one,
	/// else a value.
	fn build_field(
		&mut self,
		object: &Spanned<ast::Expression>,
		member: Spanned<SymbolU32>,
		span: TextSpan,
	) -> Operand {
		let object = self.build_operand(object);
		let object_ty = match object {
			Operand::Place(place) => self.body.place(place).ty,
			Operand::Value(value) => self.body.ty(value),
		};
		let Some((field, ty)) = self.select_field(object_ty, member) else {
			return Operand::Value(self.body.push(
				ExprKind::Error,
				TypeIndex::ERROR,
				span,
			));
		};
		match object {
			Operand::Place(object) => {
				let Place {
					memory, mutable, ..
				} = *self.body.place(object);
				Operand::Place(self.body.push_place(Place {
					kind: PlaceKind::Field { object, field },
					ty,
					memory,
					mutable,
					span,
				}))
			}
			Operand::Value(object) => Operand::Value(self.body.push(
				ExprKind::FieldAccess { object, field },
				ty,
				span,
			)),
		}
	}

	/// The field `member` of a value of type `object_ty`, and its type with
	/// the struct's type arguments. Reports and gives `None` when there is no
	/// such field; a private field is reported and still selected.
	fn select_field(
		&mut self,
		object_ty: TypeIndex,
		member: Spanned<SymbolU32>,
	) -> Option<(crate::tir::defs::FieldIdx, TypeIndex)> {
		if object_ty == TypeIndex::ERROR {
			return None;
		}
		let name = self.cx.strings.resolve(member.inner).unwrap();
		let Type::Struct {
			struct_index,
			type_args,
		} = *self.cx.types.resolve(object_ty)
		else {
			let found = self.cx.type_formatter().display_type(object_ty);
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::UnknownStructField.code())
					.with_message(format!(
						"no field `{name}` on type `{found}`"
					))
					.with_label(Label::primary(
						self.scope.file_id,
						member.span,
					)),
			);
			return None;
		};
		let def = &self.cx.defs.structs[usize::from(struct_index)];
		let struct_name = self.cx.strings.resolve(def.name.inner).unwrap();
		let Some(&field) = def.lookup.get(&member.inner) else {
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::UnknownStructField.code())
					.with_message(format!(
						"no such field `{name}` in struct `{struct_name}`"
					))
					.with_label(Label::primary(
						self.scope.file_id,
						member.span,
					)),
			);
			return None;
		};
		let visibility =
			Visibility::from(def.fields[usize::from(field)].pub_span);
		if !self.cx.defs.namespaces.is_accessible_from(
			self.scope.namespace,
			def.namespace.into(),
			visibility,
		) {
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::PrivateStructField.code())
					.with_message(format!(
						"field `{name}` of struct `{struct_name}` is private"
					))
					.with_label(
						Label::primary(self.scope.file_id, member.span)
							.with_message("private field"),
					),
			);
		}
		let declared = self
			.cx
			.types
			.list(self.cx.structs[usize::from(struct_index)].field_types)
			[usize::from(field)];
		let args = self.cx.types.list(type_args).to_vec();
		let ty = self.cx.types.substitute(
			declared,
			Substitution {
				envs: &self.cx.type_envs,
				env: self.cx.structs[usize::from(struct_index)].type_params,
				args: &args,
			},
		);
		Some((field, self.normalized(ty, self.scope.env)))
	}

	/// `place.&`: a shared pointer to a place, in its memory. Only a place
	/// has an address; a local or a call's result does not.
	pub(super) fn build_address_of(
		&mut self,
		value: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> ExprIdx {
		match self.build_operand(value) {
			Operand::Place(place) => {
				let Place { ty: to, memory, .. } = *self.body.place(place);
				let ty = self.cx.types.intern(Type::Pointer {
					to,
					memory,
					ownership: Ownership::Shared,
				});
				self.body.push(ExprKind::AddressOf(place), ty, span)
			}
			Operand::Value(value)
				if self.body.ty(value) == TypeIndex::ERROR =>
			{
				value
			}
			Operand::Value(value) => {
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidAssignmentTarget.code(),
						)
						.with_message("cannot take the address of a value")
						.with_label(
							self.source_span(value)
								.primary_label()
								.with_message(
									"this is a value, not a location in memory",
								),
						)
						.with_note(
							"`.&` takes the address of a place reached \
							 through a pointer, as `p.*` or `p.*.field`",
						),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
		}
	}

	/// `target = value`.
	pub(super) fn build_assign(
		&mut self,
		target: &Spanned<ast::Expression>,
		value: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> ExprIdx {
		if let ast::Expression::Placeholder = target.inner {
			let value = self.build(value, TypeIndex::INFER);
			let ty = self.body.ty(value);
			if self.cx.types.has_untyped(ty) {
				self.report_annotation_required(value);
			}
			return self.body.push(
				ExprKind::Drop { value },
				TypeIndex::UNIT,
				span,
			);
		}
		match self.build_operand(target) {
			Operand::Place(place) => {
				self.check_place_writable(place);
				let ty = self.body.place(place).ty;
				let value = self.check(value, ty);
				self.body.push(
					ExprKind::Store { place, value },
					TypeIndex::UNIT,
					span,
				)
			}
			Operand::Value(target) => {
				if !self.check_assignable(target) {
					self.build(value, TypeIndex::ERROR);
					return self.body.push(
						ExprKind::Error,
						TypeIndex::UNIT,
						span,
					);
				}
				let ty = self.body.ty(target);
				let value = self.check(value, ty);
				self.body.push(
					ExprKind::Assign { target, value },
					TypeIndex::UNIT,
					span,
				)
			}
		}
	}

	/// `target op= value`: `target = target op value` with `target` evaluated
	/// once. Both sides have the target's type, as the operator's trait takes
	/// `rhs: Self`.
	pub(super) fn build_compound_assign(
		&mut self,
		op: Spanned<BinaryOp>,
		target: &Spanned<ast::Expression>,
		value: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> ExprIdx {
		let plain = plain_operator(op.inner);
		match self.build_operand(target) {
			Operand::Place(place) => {
				self.check_place_writable(place);
				let Place {
					ty,
					span: target_span,
					..
				} = *self.body.place(place);
				let value = self.check(value, ty);
				let Some(method) =
					self.compound_method(op, plain, ty, target_span)
				else {
					return self.body.push(
						ExprKind::Error,
						TypeIndex::UNIT,
						span,
					);
				};
				let kind = match method {
					CompoundMethod::Primitive => {
						ExprKind::PrimitiveCompoundStore {
							op: plain,
							place,
							value,
						}
					}
					CompoundMethod::Method(SelectedMethod::Concrete {
						function,
						type_args,
					}) => ExprKind::ConcreteCompoundStore {
						method: function,
						type_args,
						place,
						value,
					},
					CompoundMethod::Method(SelectedMethod::Abstract {
						method,
						type_args,
					}) => ExprKind::AbstractCompoundStore {
						method,
						type_args,
						place,
						value,
					},
				};
				self.body.push(kind, TypeIndex::UNIT, span)
			}
			Operand::Value(target) => {
				if !self.check_assignable(target) {
					self.build(value, TypeIndex::ERROR);
					return self.body.push(
						ExprKind::Error,
						TypeIndex::UNIT,
						span,
					);
				}
				let ty = self.body.ty(target);
				let value = self.check(value, ty);
				let target_span = self.body.span(target);
				let Some(method) =
					self.compound_method(op, plain, ty, target_span)
				else {
					return self.body.push(
						ExprKind::Error,
						TypeIndex::UNIT,
						span,
					);
				};
				let kind = match method {
					CompoundMethod::Primitive => {
						ExprKind::PrimitiveCompoundAssign {
							op: plain,
							target,
							value,
						}
					}
					CompoundMethod::Method(SelectedMethod::Concrete {
						function,
						type_args,
					}) => ExprKind::ConcreteCompoundAssign {
						method: function,
						type_args,
						target,
						value,
					},
					CompoundMethod::Method(SelectedMethod::Abstract {
						method,
						type_args,
					}) => ExprKind::AbstractCompoundAssign {
						method,
						type_args,
						target,
						value,
					},
				};
				self.body.push(kind, TypeIndex::UNIT, span)
			}
		}
	}

	/// What `op=` on a target of type `ty` calls, through `plain`'s trait.
	/// `None` when the type has no impl (reported) or is already an error.
	fn compound_method(
		&mut self,
		op: Spanned<BinaryOp>,
		plain: BinaryOp,
		ty: TypeIndex,
		target_span: TextSpan,
	) -> Option<CompoundMethod> {
		let selected = self.operator_impl(
			ty,
			self.cx.operators.binary(plain),
			target_span,
			op.span,
			op.inner.as_str(),
			DiagnosticCode::BinaryOperatorCannotBeApplied,
		)?;
		if is_primitive_binary(plain, ty) {
			return Some(CompoundMethod::Primitive);
		}
		Some(CompoundMethod::Method(
			self.select_operator_method(selected, ty),
		))
	}

	/// Reports a write through a shared pointer.
	fn check_place_writable(&mut self, place: PlaceIdx) {
		let place = *self.body.place(place);
		if place.mutable || place.ty == TypeIndex::ERROR {
			return;
		}
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::CannotMutateImmutable.code())
				.with_message("cannot write through a shared pointer")
				.with_label(Label::primary(self.scope.file_id, place.span))
				.with_note(
					"a place reached through `&T` is read-only; `*T` may be written",
				),
		);
	}

	/// Whether `target`, a value, is something `=` can write: a local or a
	/// field of a local. A target that is not is reported and gives
	/// `false`; one that is but is not `mut` is reported and gives `true`,
	/// since its type still holds the value to it.
	fn check_assignable(&mut self, target: ExprIdx) -> bool {
		let mut root = target;
		while let ExprKind::FieldAccess { object, .. } = self.body.kind(root) {
			root = object;
		}
		let span = self.body.span(target);
		match self.body.kind(root) {
			ExprKind::Error => true,
			ExprKind::Local(local) => {
				let local = *self.body.local(local);
				if local.mut_span.is_none() {
					let name =
						self.cx.strings.resolve(local.name.inner).unwrap();
					self.cx.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::CannotMutateImmutable.code(),
							)
							.with_message(format!(
								"cannot assign to immutable local `{name}`"
							))
							.with_label(Label::primary(
								self.scope.file_id,
								span,
							))
							.with_label(
								Label::secondary(
									self.scope.file_id,
									local.name.span,
								)
								.with_message(format!(
									"declare it `local mut {name}` to assign to it"
								)),
							),
					);
				}
				true
			}
			// A global is a handle, not a location: it is written through
			// `GlobalMut::set`, never with `=`.
			ExprKind::Global(global) => {
				let name = self.cx.defs.globals[usize::from(global)].name.inner;
				let name = self.cx.strings.resolve(name).unwrap();
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidAssignmentTarget.code(),
						)
						.with_message(format!(
							"cannot assign to global `{name}`"
						))
						.with_label(
							Label::primary(self.scope.file_id, span)
								.with_message("a global's name is its handle"),
						)
						.with_note(format!(
							"a `global mut` is written with `{name}.set(value)`"
						)),
				);
				false
			}
			_ => {
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidAssignmentTarget.code(),
						)
						.with_message("invalid left-hand side of assignment")
						.with_label(
							Label::primary(self.scope.file_id, span)
								.with_message(
									"cannot assign to this expression",
								),
						),
				);
				false
			}
		}
	}
}

/// The operator `op=` applies: `Add` for `+=`.
fn plain_operator(op: BinaryOp) -> BinaryOp {
	match op {
		BinaryOp::AddAssign => BinaryOp::Add,
		BinaryOp::SubAssign => BinaryOp::Sub,
		BinaryOp::MulAssign => BinaryOp::Mul,
		BinaryOp::DivAssign => BinaryOp::Div,
		BinaryOp::RemAssign => BinaryOp::Rem,
		BinaryOp::BitAndAssign => BinaryOp::BitAnd,
		BinaryOp::BitOrAssign => BinaryOp::BitOr,
		BinaryOp::BitXorAssign => BinaryOp::BitXor,
		BinaryOp::LeftShiftAssign => BinaryOp::LeftShift,
		BinaryOp::RightShiftAssign => BinaryOp::RightShift,
		_ => unreachable!("not a compound assignment"),
	}
}
