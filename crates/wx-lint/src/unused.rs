//! What a body declares and never uses: a local never read
//! (`unused_variable`), `mut` on a local never assigned
//! (`unnecessary_mutability`), and a label no jump names (`unused_label`).
//! A local's uses are read from its body ([`local_uses`]); a label's from the
//! compiler's name resolutions, read once to mark each label a jump names.
//!
//! Only a read uses a local; one only assigned or compound-assigned is
//! still reported, as rustc does. `_ = x;` reads `x`, and is how to keep a
//! local that is not otherwise read.

use codespan_reporting::diagnostic::Diagnostic;
use wx_compiler::diagnostics::SourceSpan;
use wx_compiler::symbols::{Keyword, StringInterner};
use wx_compiler::tir::{
	Body, BodyOwner, ConstIdx, Declared as _, ExprKind, FunctionIdx, GlobalIdx,
	Reference, Semantics,
};
use wx_compiler::vfs::{FileId, PackageId};

use crate::{Lint, LintConfig};

/// Reports the unused locals and labels of every body declared in
/// `package`.
pub(crate) fn report_unused(
	diagnostics: &mut Vec<Diagnostic<FileId>>,
	config: LintConfig,
	sema: &Semantics,
	strings: &StringInterner,
	package: PackageId,
) {
	let uses = Uses::collect(sema, package);
	for (owner, columns) in uses.owners() {
		let body = sema.owner_body(owner).expect("a selected owner has a body");
		let file = sema.decls.file_id(owner.loc(&sema.decls));
		for (local, used) in body.locals().iter().zip(local_uses(body)) {
			let name = strings.resolve(local.name.inner).expect("interned");
			if let Some(severity) = config.severity(Lint::UnusedVariable)
				&& !used.is_read()
				&& local.name.inner != Keyword::SelfLower.symbol()
			{
				let message = if used.is_assigned() {
					format!("`{name}` is assigned but never read")
				} else {
					format!("unused variable `{name}`")
				};
				diagnostics.push(
					Diagnostic::new(severity)
						.with_code(Lint::UnusedVariable.code())
						.with_message(message)
						.with_label(
							SourceSpan::new(file, local.name.span)
								.primary_label(),
						)
						.with_note(format!(
							"if it is unused on purpose, drop it with `_ = {name};`"
						)),
				);
			}
			if let Some(severity) = config.severity(Lint::UnnecessaryMutability)
				&& let Some(mut_span) = local.mut_span
				&& !used.is_assigned()
			{
				diagnostics.push(
					Diagnostic::new(severity)
						.with_code(Lint::UnnecessaryMutability.code())
						.with_message(format!(
							"`{name}` does not need to be mutable"
						))
						.with_label(
							SourceSpan::new(file, mut_span).primary_label(),
						),
				);
			}
		}
		for (at, target) in body.targets().iter().enumerate() {
			if let Some(severity) = config.severity(Lint::UnusedLabel)
				&& let Some(label) = target.label
				&& !uses.labels[columns.labels as usize + at]
			{
				let name = strings.resolve(label.inner).expect("interned");
				diagnostics.push(
					Diagnostic::new(severity)
						.with_code(Lint::UnusedLabel.code())
						.with_message(format!("unused label `{name}`"))
						.with_label(
							SourceSpan::new(file, label.span).primary_label(),
						),
				);
			}
		}
	}
}

#[derive(Clone, Copy, Default)]
struct LocalUse {
	/// Every expression that names it, an assignment's target included.
	named: u32,
	/// Every assignment to its own storage (`=`, `op=`): one whose target's
	/// field chain starts at it. A write through a pointer it holds changes
	/// memory, not the local, and only names it.
	assigned: u32,
}

/// How `body` uses each of its locals, index-aligned with `Body::locals`.
fn local_uses(body: &Body) -> Vec<LocalUse> {
	let mut locals = vec![LocalUse::default(); body.locals().len()];
	for &kind in body.kinds() {
		let target = match kind {
			ExprKind::Local(local) => {
				locals[usize::from(local)].named += 1;
				continue;
			}
			ExprKind::Assign { target, .. }
			| ExprKind::PrimitiveCompoundAssign { target, .. }
			| ExprKind::ConcreteCompoundAssign { target, .. }
			| ExprKind::AbstractCompoundAssign { target, .. } => target,
			_ => continue,
		};
		let mut root = target;
		while let ExprKind::FieldAccess { object, .. } = body.kind(root) {
			root = object;
		}
		if let ExprKind::Local(local) = body.kind(root) {
			locals[usize::from(local)].assigned += 1;
		}
	}
	locals
}

impl LocalUse {
	/// Whether something reads its value: it is named other than as the
	/// root of an assignment's target, so `x += 1` alone does not read `x`.
	fn is_read(self) -> bool {
		self.named > self.assigned
	}

	/// Whether an assignment changes it, which is what it needs `mut` for.
	fn is_assigned(self) -> bool {
		self.assigned > 0
	}
}

/// Which labels of each selected body a jump names, in one flat column: an
/// owner's labels are a run of `labels` starting at its `Columns::labels`,
/// in `TargetIdx` order.
struct Uses {
	/// By owner arena; `None` for an owner not reported on, or without a
	/// body.
	functions: Vec<Option<Columns>>,
	constants: Vec<Option<Columns>>,
	globals: Vec<Option<Columns>>,
	labels: Vec<bool>,
}

#[derive(Clone, Copy)]
struct Columns {
	labels: u32,
}

impl Uses {
	fn collect(sema: &Semantics, package: PackageId) -> Self {
		let mut labels = 0;
		let mut columns = |owner: BodyOwner| {
			if sema.decls.package_id(owner.loc(&sema.decls)) != package {
				return None;
			}
			let body = sema.owner_body(owner)?;
			let at = Columns { labels };
			labels += body.targets().len() as u32;
			Some(at)
		};
		let functions = (0..sema.decls.functions.len() as u32)
			.map(|index| columns(BodyOwner::Function(FunctionIdx::new(index))))
			.collect();
		let constants = (0..sema.decls.constants.len() as u32)
			.map(|index| columns(BodyOwner::Const(ConstIdx::new(index))))
			.collect();
		let globals = (0..sema.decls.globals.len() as u32)
			.map(|index| columns(BodyOwner::Global(GlobalIdx::new(index))))
			.collect();
		let mut uses = Self {
			functions,
			constants,
			globals,
			labels: vec![false; labels as usize],
		};
		for (_, reference) in sema.resolutions.iter() {
			if let Reference::Label { owner, target } = reference
				&& let Some(columns) = uses.columns(owner)
			{
				uses.labels[columns.labels as usize + usize::from(target)] =
					true;
			}
		}
		uses
	}

	fn columns(&self, owner: BodyOwner) -> Option<Columns> {
		match owner {
			BodyOwner::Function(index) => self.functions[usize::from(index)],
			BodyOwner::Const(index) => self.constants[usize::from(index)],
			BodyOwner::Global(index) => self.globals[usize::from(index)],
		}
	}

	/// Every selected owner with its columns, in arena order.
	fn owners(&self) -> impl Iterator<Item = (BodyOwner, Columns)> + '_ {
		fn selected(
			column: &[Option<Columns>],
			owner: fn(u32) -> BodyOwner,
		) -> impl Iterator<Item = (BodyOwner, Columns)> + '_ {
			column
				.iter()
				.enumerate()
				.filter_map(move |(index, columns)| {
					Some((owner(index as u32), (*columns)?))
				})
		}
		selected(&self.functions, |index| {
			BodyOwner::Function(FunctionIdx::new(index))
		})
		.chain(selected(&self.constants, |index| {
			BodyOwner::Const(ConstIdx::new(index))
		}))
		.chain(selected(&self.globals, |index| {
			BodyOwner::Global(GlobalIdx::new(index))
		}))
	}
}
