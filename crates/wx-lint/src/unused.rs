//! What a body declares and never uses: a local never read
//! (`unused_variable`), `mut` on a local never assigned
//! (`unnecessary_mutability`), and a label no jump names (`unused_label`).
//! Each is the inverse of the compiler's name resolutions: the pass reads
//! every recorded reference once, marks the local or label it names, and
//! reports what is left unmarked.
//!
//! Only a `Read` uses a local; one only assigned or compound-assigned is
//! still reported, as rustc does. `_ = x;` reads `x`, and is how to keep a
//! local that is not otherwise read.

use codespan_reporting::diagnostic::Diagnostic;
use wx_compiler::diagnostics::SourceSpan;
use wx_compiler::symbols::{Keyword, StringInterner};
use wx_compiler::tir::{
	AccessKind, BodyOwner, ConstIdx, Declared as _, FunctionIdx, GlobalIdx,
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
		for (at, local) in body.locals().iter().enumerate() {
			let used = uses.locals[columns.locals as usize + at];
			let name = strings.resolve(local.name.inner).expect("interned");
			if let Some(severity) = config.severity(Lint::UnusedVariable)
				&& !used.read
				&& local.name.inner != Keyword::SelfLower.symbol()
			{
				let message = if used.written {
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
				&& !used.written
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

/// What the references say of each selected body's locals and labels, in
/// flat columns: an owner's locals are a run of `locals` starting at its
/// `Columns::locals`, in `LocalIdx` order, and its labels likewise by
/// `TargetIdx`.
struct Uses {
	/// By owner arena; `None` for an owner not reported on, or without a
	/// body.
	functions: Vec<Option<Columns>>,
	constants: Vec<Option<Columns>>,
	globals: Vec<Option<Columns>>,
	locals: Vec<LocalUse>,
	labels: Vec<bool>,
}

#[derive(Clone, Copy)]
struct Columns {
	locals: u32,
	labels: u32,
}

#[derive(Clone, Copy, Default)]
struct LocalUse {
	read: bool,
	/// Assigned or compound-assigned, which needs `mut`.
	written: bool,
}

impl Uses {
	fn collect(sema: &Semantics, package: PackageId) -> Self {
		let mut locals = 0;
		let mut labels = 0;
		let mut columns = |owner: BodyOwner| {
			if sema.decls.package_id(owner.loc(&sema.decls)) != package {
				return None;
			}
			let body = sema.owner_body(owner)?;
			let at = Columns { locals, labels };
			locals += body.locals().len() as u32;
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
			locals: vec![LocalUse::default(); locals as usize],
			labels: vec![false; labels as usize],
		};
		for reference in sema.resolutions.by_site.values() {
			match *reference {
				Reference::Local {
					owner,
					local,
					access,
				} => {
					let Some(columns) = uses.columns(owner) else {
						continue;
					};
					let used = &mut uses.locals
						[columns.locals as usize + usize::from(local)];
					match access {
						AccessKind::Read => used.read = true,
						AccessKind::Write | AccessKind::ReadWrite => {
							used.written = true
						}
						AccessKind::Initialize => {
							unreachable!("only a field is initialized")
						}
					}
				}
				Reference::Label { owner, target } => {
					if let Some(columns) = uses.columns(owner) {
						uses.labels
							[columns.labels as usize + usize::from(target)] = true;
					}
				}
				_ => {}
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
