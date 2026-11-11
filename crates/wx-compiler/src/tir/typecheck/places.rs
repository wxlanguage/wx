//! Places and assignment: `p.*`, `value.field`, `x[i]`, `place.&`, and
//! `=`/`op=`.
//!
//! A place is a location in linear memory, reached through a pointer: `p.*`,
//! a field of a place, and an element, `x[i]`. Each step of a place goes
//! through at most one pointer: `p.field` is `p.*.field` for a pointer `p`,
//! and `s[i]` is `s.*[i]` for a pointer `s` to a slice or an array.
//! Everything else is a value, even when it names a location (a local, or a
//! field of one), and is assigned through `Assign`; a place is written through
//! `Store`. A global's name is a handle, written through `GlobalMut::set`, so
//! it is never the target of `=`. Reading a place is a `Load`, pushed only
//! where its value is used, so `.&` and the left of `=` take the place
//! itself.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::{BodyBuilder, SelectedMethod};
use crate::ast::{self, BinaryOp, Ownership, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{ExprIdx, ExprKind, Place, PlaceIdx, PlaceKind};
use crate::tir::decls::{TraitIdx, Visibility};
use crate::tir::operators::is_primitive_binary;
use crate::tir::resolutions::{AccessKind, Reference, Site};
use crate::tir::solver::SolverError;
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

impl BodyBuilder<'_, '_> {
	/// `p.*` or `value.field` where its value is used.
	pub(super) fn build_read(
		&mut self,
		expr: &Spanned<ast::Expression>,
	) -> ExprIdx {
		match self.build_operand(expr, AccessKind::Read, &mut None) {
			Operand::Place(place) => self.load(place),
			Operand::Value(value) => value,
		}
	}

	fn load(&mut self, place: PlaceIdx) -> ExprIdx {
		let Place { ty, span, .. } = *self.body.place(place);
		let ty = self.require_stack_value(ty, span);
		self.body.push(ExprKind::Load(place), ty, span)
	}

	/// `expr` as a place when it is one, else as a value. `access` is how the
	/// use treats it. Only the named node the use ends at (`value` in
	/// `s.inner.value = n`) carries it; the names it is reached through are
	/// projections and read. An index passes it on to its object, since the
	/// element has no name of its own: `data` in `p.data[i] = n` is written,
	/// unless it turns out to be a pointer, which `[i]` only reads.
	///
	/// `site` is set to the name that was recorded with `access`, if one was,
	/// so that an index which finds its object a pointer can make it a read.
	fn build_operand(
		&mut self,
		expr: &Spanned<ast::Expression>,
		access: AccessKind,
		site: &mut Option<Site>,
	) -> Operand {
		match &expr.inner {
			// `(p.*).x`: parentheses are a tuple of one, kept a place
			// rather than loaded as a value.
			ast::Expression::Tuple { elements } if elements.len() == 1 => {
				self.build_operand(&elements[0].inner, access, site)
			}
			ast::Expression::Deref { pointer } => {
				self.build_deref(pointer, expr.span)
			}
			ast::Expression::ObjectAccess { object, member } => {
				self.build_field(object, member, expr.span, access, site)
			}
			ast::Expression::Index { object, index } => {
				self.build_index(object, index, expr.span, access, site)
			}
			ast::Expression::Path(segments) => {
				let value = self.build_path(
					segments,
					TypeIndex::INFER,
					expr.span,
					access,
				);
				if let ExprKind::Local(_) = self.body.kind(value) {
					*site = Some(Site::Value(SourceSpan::new(
						self.scope.file_id,
						expr.span,
					)));
				}
				Operand::Value(value)
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
		match *self.sema.types.resolve(pointer_ty) {
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
				let found = self
					.sema
					.type_formatter(self.builder.strings)
					.display_type(pointer_ty);
				let at = self.context().source_span(pointer);
				self.sema.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::CannotDerefNonPointer.code())
						.with_message(format!(
							"type `{found}` cannot be dereferenced"
						))
						.with_label(
							at.primary_label().with_message("not a pointer"),
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
	/// else a value. An object that is a pointer is gone through once:
	/// `p.field` is `p.*.field`, and a pointer to a pointer has no fields.
	fn build_field(
		&mut self,
		object: &Spanned<ast::Expression>,
		segment: &ast::PathSegment,
		span: TextSpan,
		access: AccessKind,
		site: &mut Option<Site>,
	) -> Operand {
		let member = segment.ident;
		if let (Some(first), Some(last)) =
			(segment.type_args.first(), segment.type_args.last())
		{
			self.sema.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeArgumentsNotAllowed.code())
					.with_message("type arguments are not allowed here")
					.with_label(
						Label::primary(
							self.scope.file_id,
							TextSpan::new(first.span().start, last.span().end),
						)
						.with_message("a field takes no type arguments"),
					),
			);
		}
		let mut object =
			self.build_operand(object, AccessKind::Read, &mut None);
		let mut object_ty = match object {
			Operand::Place(place) => self.body.place(place).ty,
			Operand::Value(value) => self.body.ty(value),
		};
		if let Type::Pointer {
			to,
			memory,
			ownership,
		} = *self.sema.types.resolve(object_ty)
		{
			let pointer = match object {
				Operand::Place(place) => self.load(place),
				Operand::Value(value) => value,
			};
			object = Operand::Place(self.body.push_place(Place {
				kind: PlaceKind::Deref { pointer },
				ty: to,
				memory,
				mutable: ownership == Ownership::Exclusive,
				span: self.body.span(pointer),
			}));
			object_ty = to;
		}
		let Some((field, ty)) =
			self.select_field(object_ty, member, access, site)
		else {
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

	/// `object[index]`: an element of a slice or an array, as `object.field`
	/// is a field of a struct. A place of a slice or an array is indexed where
	/// it is (`h.data[i]`); an object that is a pointer to one is gone
	/// through once (`s[i]` is `s.*[i]`), and a pointer to that pointer is
	/// not. The element is in its sequence's memory, writable when the
	/// sequence is, and the index is that memory's `Size`.
	fn build_index(
		&mut self,
		object: &Spanned<ast::Expression>,
		index: &Spanned<ast::Expression>,
		span: TextSpan,
		access: AccessKind,
		site: &mut Option<Site>,
	) -> Operand {
		let object_span = object.span;
		let object = match self.build_operand(object, access, site) {
			Operand::Place(place) => {
				let ty = self.body.place(place).ty;
				let ty = self.context().normalized(ty);
				match *self.sema.types.resolve(ty) {
					Type::Pointer { .. } => Some(self.load(place)),
					_ => match self.sequence_element(ty, object_span) {
						Ok(Some(element)) => {
							return self
								.build_element(place, element, index, span);
						}
						Ok(None) => {
							self.report_cannot_index(ty, object_span, None);
							None
						}
						Err(()) => None,
					},
				}
			}
			Operand::Value(value) => Some(value),
		};
		// Past a sequence place (returned above), the object is a pointer
		// value, or invalid: the index only reads it, whatever the use does
		// to the element.
		if let Some(site) = *site {
			self.sema.resolutions.downgrade_to_read(site);
		}
		let Some((pointer, (to, element, memory, ownership))) = object
			.and_then(|pointer| Some((pointer, self.indexed_slice(pointer)?)))
		else {
			self.build(index, TypeIndex::ERROR);
			return Operand::Value(self.body.push(
				ExprKind::Error,
				TypeIndex::ERROR,
				span,
			));
		};
		let sequence = self.body.push_place(Place {
			kind: PlaceKind::Deref { pointer },
			ty: to,
			memory,
			mutable: ownership == Ownership::Exclusive,
			span: self.body.span(pointer),
		});
		self.build_element(sequence, element, index, span)
	}

	/// `sequence[index]`, `element` the sequence's element type.
	fn build_element(
		&mut self,
		sequence: PlaceIdx,
		element: TypeIndex,
		index: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> Operand {
		let Place {
			memory, mutable, ..
		} = *self.body.place(sequence);
		let size = self.memory_size(memory);
		let index = self.check(index, size);
		Operand::Place(self.body.push_place(Place {
			kind: PlaceKind::Element {
				object: sequence,
				index,
			},
			ty: element,
			memory,
			mutable,
			span,
		}))
	}

	/// The slice or array `pointer` points at, its element type, and the
	/// pointer's memory and ownership. `None` when it is no pointer to one
	/// (reported) or is already an error.
	fn indexed_slice(
		&mut self,
		pointer: ExprIdx,
	) -> Option<(TypeIndex, TypeIndex, TypeIndex, Ownership)> {
		let ty = self.body.ty(pointer);
		if ty == TypeIndex::ERROR {
			return None;
		}
		if self.sema.types.needs_context(ty) {
			self.report_annotation_required(pointer);
			return None;
		}
		let ty = self.context().normalized(ty);
		let span = self.body.span(pointer);
		let Type::Pointer {
			to,
			memory,
			ownership,
		} = *self.sema.types.resolve(ty)
		else {
			self.report_cannot_index(ty, span, None);
			return None;
		};
		match self.sequence_element(to, span) {
			Ok(Some(element)) => Some((to, element, memory, ownership)),
			Ok(None) => {
				self.report_cannot_index(ty, span, Some(to));
				None
			}
			Err(()) => None,
		}
	}

	/// The element type of `ty` (normalized) when it is a slice, an array,
	/// or a type assumed `Slice`; `Ok(None)` when it is none of them, and
	/// `Err` when it is an error or the solver could not say (reported).
	fn sequence_element(
		&mut self,
		ty: TypeIndex,
		span: TextSpan,
	) -> Result<Option<TypeIndex>, ()> {
		match *self.sema.types.resolve(ty) {
			Type::Slice { of } | Type::Array { of, .. } => Ok(Some(of)),
			Type::Error => Err(()),
			Type::TypeParam { .. } | Type::TypeProjection { .. } => {
				let intrinsics = &self.sema.decls.intrinsics;
				let slice = intrinsics.slice.expect("std declares `Slice`");
				let value =
					intrinsics.slice_value.expect("`Slice` declares `Value`");
				if !self.implements(ty, slice, span).ok_or(())? {
					return Ok(None);
				}
				let element = self.sema.types.intern(Type::TypeProjection {
					trait_index: slice,
					assoc_type_index: value,
					base: ty,
				});
				Ok(Some(self.context().normalized(element)))
			}
			_ => Ok(None),
		}
	}

	/// E2125 for an object of type `ty` at `span`; `pointee` is what a
	/// pointer object points at, to say when it is one pointer too many.
	fn report_cannot_index(
		&mut self,
		ty: TypeIndex,
		span: TextSpan,
		pointee: Option<TypeIndex>,
	) {
		let found_ty = self
			.sema
			.type_formatter(self.builder.strings)
			.display_type(ty);
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::CannotIndex.code())
			.with_message(format!("type `{found_ty}` cannot be indexed"))
			.with_label(
				Label::primary(self.scope.file_id, span).with_message(
					"not a slice or an array, or a pointer to one",
				),
			);
		// A pointer to a pointer to a slice: one step too far.
		if let Some(to) = pointee
			&& let Type::Pointer { to, .. } = *self.sema.types.resolve(to)
			&& matches!(
				self.sema.types.resolve(to),
				Type::Slice { .. } | Type::Array { .. }
			) {
			diagnostic = diagnostic.with_note(
				"an element is reached through one pointer, not two: \
				 dereference the outer one first, as `x.*[i]`",
			);
		}
		self.sema.diagnostics.push(diagnostic);
	}

	/// Whether `ty` has `trait_index` here. `None` when the solver cannot
	/// say (an overflow or a cycle is reported at `span`).
	fn implements(
		&mut self,
		ty: TypeIndex,
		trait_index: TraitIdx,
		span: TextSpan,
	) -> Option<bool> {
		match self.sema.find_trait_impl_query(
			self.builder.strings,
			self.scope.assumption_env,
			ty,
			trait_index,
		) {
			Ok(found) => Some(found.is_some()),
			Err(error) => {
				let site = SourceSpan::new(self.scope.file_id, span);
				match error {
					SolverError::Overflow => {
						self.sema
							.diagnostics
							.push(self.sema.overflow_diagnostic(site));
					}
					SolverError::Cycle(cycle) => {
						let diagnostic = self.sema.cycle_diagnostic(
							self.builder.strings,
							&cycle,
							site,
						);
						self.sema.diagnostics.push(diagnostic);
					}
					// Its owner reported it.
					SolverError::Poisoned => {}
					SolverError::Pending => unreachable!(
						"every signature is final when bodies are checked"
					),
				}
				None
			}
		}
	}

	/// `ty`, made at `span` as a value: itself when it is a `StackValue`, else
	/// `ERROR`, reported.
	pub(super) fn require_stack_value(
		&mut self,
		ty: TypeIndex,
		span: TextSpan,
	) -> TypeIndex {
		if ty == TypeIndex::ERROR {
			return ty;
		}
		let site = SourceSpan::new(self.scope.file_id, span);
		match self.sema.check_value_type(
			self.builder.strings,
			self.scope.assumption_env,
			ty,
			site,
		) {
			Ok(()) => return ty,
			Err(SolverError::Overflow) => {
				self.sema
					.diagnostics
					.push(self.sema.overflow_diagnostic(site));
			}
			Err(SolverError::Cycle(cycle)) => {
				let diagnostic = self.sema.cycle_diagnostic(
					self.builder.strings,
					&cycle,
					site,
				);
				self.sema.diagnostics.push(diagnostic);
			}
			// Its owner reported it.
			Err(SolverError::Poisoned) => {}
			Err(SolverError::Pending) => {
				unreachable!("every signature is final when bodies are checked")
			}
		}
		TypeIndex::ERROR
	}

	/// The field `member` of a value of type `object_ty`, and its type with
	/// the struct's type arguments. Reports and gives `None` when there is no
	/// such field; a private field is reported and still selected.
	fn select_field(
		&mut self,
		object_ty: TypeIndex,
		member: Spanned<SymbolU32>,
		access: AccessKind,
		site: &mut Option<Site>,
	) -> Option<(crate::tir::decls::FieldIdx, TypeIndex)> {
		if object_ty == TypeIndex::ERROR {
			return None;
		}
		let name = self.builder.strings.resolve(member.inner).unwrap();
		let Type::Struct {
			struct_index,
			type_args,
		} = *self.sema.types.resolve(object_ty)
		else {
			let found = self
				.sema
				.type_formatter(self.builder.strings)
				.display_type(object_ty);
			let mut diagnostic = Diagnostic::error()
				.with_code(DiagnosticCode::UnknownStructField.code())
				.with_message(format!("no field `{name}` on type `{found}`"))
				.with_label(Label::primary(self.scope.file_id, member.span));
			// The object was a pointer to it, gone through once already.
			if matches!(
				self.sema.types.resolve(object_ty),
				Type::Pointer { .. }
			) {
				diagnostic = diagnostic.with_note(
					"a field is reached through one pointer, not two: \
					 dereference the outer one first, as `p.*.field`",
				);
			}
			self.sema.diagnostics.push(diagnostic);
			return None;
		};
		let decl = &self.sema.decls.structs[usize::from(struct_index)];
		let struct_name =
			self.builder.strings.resolve(decl.name.inner).unwrap();
		let Some(&field) = decl.lookup.get(&member.inner) else {
			self.sema.diagnostics.push(
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
		let recorded =
			Site::Value(SourceSpan::new(self.scope.file_id, member.span));
		self.sema.resolutions.record(
			recorded,
			Reference::Field {
				access,
				owner: struct_index,
				field,
			},
		);
		*site = Some(recorded);
		let visibility =
			Visibility::from(decl.field_pub_spans[usize::from(field)]);
		if !self.sema.decls.namespaces.is_accessible_from(
			self.scope.namespace,
			decl.namespace.into(),
			visibility,
		) {
			self.sema.diagnostics.push(
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
			.sema
			.types
			.list(self.sema.structs[usize::from(struct_index)].field_types)
			[usize::from(field)];
		let args = self.sema.types.list(type_args).to_vec();
		let ty = self.sema.types.substitute(
			declared,
			Substitution {
				envs: &self.sema.generic_envs,
				env: self.sema.structs[usize::from(struct_index)].type_params,
				args: &args,
			},
		);
		Some((field, self.context().normalized(ty)))
	}

	/// `place.&`: a shared pointer to a place, in its memory. Only a place
	/// has an address; a local or a call's result does not.
	pub(super) fn build_address_of(
		&mut self,
		value: &Spanned<ast::Expression>,
		span: TextSpan,
	) -> ExprIdx {
		match self.build_operand(value, AccessKind::Read, &mut None) {
			Operand::Place(place) => {
				let Place { ty: to, memory, .. } = *self.body.place(place);
				let ty = self.sema.types.intern(Type::Pointer {
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
				let at = self.context().source_span(value);
				self.sema.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidAssignmentTarget.code(),
						)
						.with_message("cannot take the address of a value")
						.with_label(at.primary_label().with_message(
							"this is a value, not a location in memory",
						))
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
			if self.sema.types.needs_context(ty) {
				self.report_annotation_required(value);
			}
			return self.body.push(
				ExprKind::Drop { value },
				TypeIndex::UNIT,
				span,
			);
		}
		let access = AccessKind::Write;
		let operand = self.build_operand(target, access, &mut None);
		match operand {
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
				if !self.check_assignable(target, access) {
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
		let access = AccessKind::ReadWrite;
		let operand = self.build_operand(target, access, &mut None);
		match operand {
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
				if !self.check_assignable(target, access) {
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
			self.sema.operators.binary(plain),
			target_span,
			op.span,
			op.inner.as_str(),
		)?;
		if is_primitive_binary(plain, ty) {
			return Some(CompoundMethod::Primitive);
		}
		Some(CompoundMethod::Method(self.select_operator_method(
			selected,
			ty,
			target_span,
		)))
	}

	/// Reports a write through a shared pointer.
	fn check_place_writable(&mut self, place: PlaceIdx) {
		let place = *self.body.place(place);
		if place.mutable || place.ty == TypeIndex::ERROR {
			return;
		}
		self.sema.diagnostics.push(
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
	/// since its type still holds the value to it. The root local is the one
	/// that needs `mut`, so it is recorded as written however deep the field
	/// chain is: a chain that went through a pointer is a place, not a value,
	/// and never gets here.
	fn check_assignable(
		&mut self,
		target: ExprIdx,
		access: AccessKind,
	) -> bool {
		let mut root = target;
		while let ExprKind::FieldAccess { object, .. } = self.body.kind(root) {
			root = object;
		}
		let span = self.body.span(target);
		match self.body.kind(root) {
			ExprKind::Error => true,
			ExprKind::Local(local) => {
				self.sema.resolutions.set_local_access(
					Site::Value(SourceSpan::new(
						self.scope.file_id,
						self.body.span(root),
					)),
					access,
				);
				let local = *self.body.local(local);
				if local.mut_span.is_none() {
					let name =
						self.builder.strings.resolve(local.name.inner).unwrap();
					self.sema.diagnostics.push(
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
				let name =
					self.sema.decls.globals[usize::from(global)].name.inner;
				let name = self.builder.strings.resolve(name).unwrap();
				self.sema.diagnostics.push(
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
				self.sema.diagnostics.push(
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
