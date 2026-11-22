//! `mut` on a struct field never written in place
//! (`unnecessary_mutability`).
//!
//! A write changes every field on its way up to the pointer it goes
//! through, as the checker requires `mut` of them: `o.inner.value = 1` writes
//! `inner` and `value`, `o.ptr.value = 1` writes only `value`. Replacing a
//! whole value writes none of its fields. Only private fields are reported:
//! nothing outside the package can name them, so every write is in its
//! bodies.

use codespan_reporting::diagnostic::{Diagnostic, Severity};
use wx_compiler::diagnostics::SourceSpan;
use wx_compiler::symbols::StringInterner;
use wx_compiler::tir::{
	Body, BodyOwner, ConstIdx, Declared as _, ExprIdx, ExprKind, FieldIdx,
	FunctionIdx, GlobalIdx, PlaceIdx, PlaceKind, Semantics, Type, TypeIndex,
	Visibility,
};
use wx_compiler::vfs::{FileId, PackageId};

use crate::Lint;

/// Reports each private `mut` field of a struct declared in `package` that
/// none of the package's bodies writes in place.
pub(crate) fn report_unnecessary_field_mut(
	diagnostics: &mut Vec<Diagnostic<FileId>>,
	severity: Severity,
	sema: &Semantics,
	strings: &StringInterner,
	package: PackageId,
) {
	let decls = &sema.decls;
	let mut written = Written::new(sema);
	let owners = (0..decls.functions.len() as u32)
		.map(|index| BodyOwner::Function(FunctionIdx::new(index)))
		.chain(
			(0..decls.constants.len() as u32)
				.map(|index| BodyOwner::Const(ConstIdx::new(index))),
		)
		.chain(
			(0..decls.globals.len() as u32)
				.map(|index| BodyOwner::Global(GlobalIdx::new(index))),
		);
	for owner in owners {
		if decls.package_id(owner.loc(decls)) != package {
			continue;
		}
		if let Some(body) = sema.owner_body(owner) {
			written.collect(body);
		}
	}

	for (decl, &start) in decls.structs.iter().zip(&written.starts) {
		if decls.package_id(decl.loc) != package {
			continue;
		}
		let file = decls.file_id(decl.loc);
		let fields = decl.fields;
		for at in 0..fields.len() {
			let field = FieldIdx::new(at as u32);
			let Some(mut_span) = decls.fields.mut_span(fields, field) else {
				continue;
			};
			if decls.fields.visibility(fields)[at] != Visibility::Private
				|| written.fields[start as usize + at]
			{
				continue;
			}
			let Some(name) = decls.fields.name(fields, field) else {
				continue;
			};
			let name = strings.resolve(name).expect("interned");
			diagnostics.push(
				Diagnostic::new(severity)
					.with_code(Lint::UnnecessaryMutability.code())
					.with_message(format!(
						"field `{name}` does not need to be mutable"
					))
					.with_label(SourceSpan::new(file, mut_span).primary_label())
					.with_note("no write changes it in place"),
			);
		}
	}
}

/// Which struct fields some write changes in place, in one flat column: a
/// struct's fields are a run of `fields` starting at its entry in `starts`.
struct Written<'a> {
	sema: &'a Semantics,
	/// By struct arena.
	starts: Vec<u32>,
	fields: Vec<bool>,
}

impl<'a> Written<'a> {
	fn new(sema: &'a Semantics) -> Self {
		let mut total = 0;
		let starts = sema
			.decls
			.structs
			.iter()
			.map(|decl| {
				let start = total;
				total += decl.fields.len() as u32;
				start
			})
			.collect();
		Self {
			sema,
			starts,
			fields: vec![false; total as usize],
		}
	}

	fn collect(&mut self, body: &Body) {
		for &kind in body.kinds() {
			match kind {
				ExprKind::Assign { target, .. }
				| ExprKind::PrimitiveCompoundAssign { target, .. }
				| ExprKind::ConcreteCompoundAssign { target, .. }
				| ExprKind::AbstractCompoundAssign { target, .. } => {
					self.value_target(body, target);
				}
				ExprKind::Store { place, .. }
				| ExprKind::PrimitiveCompoundStore { place, .. }
				| ExprKind::ConcreteCompoundStore { place, .. }
				| ExprKind::AbstractCompoundStore { place, .. } => {
					self.place_target(body, place);
				}
				_ => {}
			}
		}
	}

	/// Every field of the chain `target` is, down to its root.
	fn value_target(&mut self, body: &Body, mut target: ExprIdx) {
		while let ExprKind::FieldAccess { object, field, .. } =
			body.kind(target)
		{
			self.mark(body.ty(object), field);
			target = object;
		}
	}

	/// Every field of `place` up to the pointer it is reached through.
	fn place_target(&mut self, body: &Body, mut place: PlaceIdx) {
		loop {
			match body.place(place).kind {
				PlaceKind::Field { object, field, .. } => {
					self.mark(body.place(object).ty, field);
					place = object;
				}
				PlaceKind::Element { object, .. } => place = object,
				PlaceKind::Deref { .. } => return,
			}
		}
	}

	fn mark(&mut self, object_ty: TypeIndex, field: FieldIdx) {
		if let Type::Struct { struct_index, .. } =
			*self.sema.types.resolve(object_ty)
		{
			let start = self.starts[usize::from(struct_index)];
			self.fields[start as usize + usize::from(field)] = true;
		}
	}
}
