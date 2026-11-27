//! Hover text that depends on where the cursor is: which construct is under
//! it, what a name holds, and the documentation written above a declaration.
//!
//! How a definition reads as `wx` source is the compiler's
//! (`Semantics::definition_formatter`); this module only finds what to render.

use wx_compiler::ast::{ExprId, Expression, Keyword};
use wx_compiler::diagnostics::{SourceSpan, TextOffset};
use wx_compiler::tir::{
	DeclKind, Definition, MemberKind, Semantics, TypeIndex,
};
use wx_compiler::vfs::{CompilationUnit, FileId};

use crate::snapshot::Snapshot;

/// The signature of the `if` or `match` whose keyword is written at
/// `offset`: the value it branches on and the value its branches give,
/// with the keyword's span.
pub(crate) fn branch(
	snapshot: &Snapshot,
	file: FileId,
	offset: TextOffset,
) -> Option<(SourceSpan, String)> {
	let ast = snapshot.compilation.ast(file);
	let (expr, keyword, on) = (0..ast.exprs.kinds.len())
		.map(|index| ExprId(index as u32))
		.filter_map(|expr| match ast.expr(expr) {
			Expression::IfElse { condition, .. } => {
				Some((expr, Keyword::If, condition))
			}
			Expression::Match { scrutinee, .. } => {
				Some((expr, Keyword::Match, scrutinee))
			}
			_ => None,
		})
		.find(|&(expr, keyword, _)| {
			let span = keyword.span_at(ast.expr_span(expr).start);
			span.start <= offset && offset <= span.end
		})?;
	let owner = snapshot.expression_owner(file, expr)?;
	let body = snapshot.sema.owner_body(owner)?;
	let ty = |expr| Some(body.operand_ty(body.operand_of(ast, expr)?));
	let span = keyword.span_at(ast.expr_span(expr).start);
	let signature = (snapshot.sema.definition_formatter(&snapshot.strings))
		.branch(keyword, ty(on)?, ty(expr)?);
	Some((SourceSpan::new(file, span), signature))
}

/// The type of the value a name of `definition` holds, as its signature
/// states it: a local's or a constant's. `None` for anything else: a
/// global's name is a handle of its own type (`DefinitionFormatter::summary`), and a
/// field's type depends on the value it is read from
/// (`Semantics::field_type`).
pub(crate) fn value_type(
	sema: &Semantics,
	definition: Definition,
) -> Option<TypeIndex> {
	match definition {
		Definition::Local { owner, local } => {
			Some(sema.owner_body(owner)?.local(local).ty)
		}
		Definition::Member(MemberKind::Constant(index)) => {
			Some(sema.constants[usize::from(index)].ty)
		}
		Definition::Item(loc) => match sema.declaration_kind(loc) {
			DeclKind::Const(index) => {
				Some(sema.constants[usize::from(index)].ty)
			}
			_ => None,
		},
		_ => None,
	}
}

/// Documentation attached to a definition, read from its own source file.
/// Parameters, fields and type parameters share their owner's line, where
/// the owner's comment must not be mistaken for their own documentation.
pub(crate) fn documentation(
	sema: &Semantics,
	compilation: &CompilationUnit,
	definition: Definition,
) -> Option<String> {
	if !matches!(definition, Definition::Item(_) | Definition::Member(_)) {
		return None;
	}
	let span = sema.definition_span(definition)?;
	let file = compilation.files.get(span.file_id).ok()?;
	// A package is declared at the start of its entry file, which is what
	// describes it.
	if let Definition::Item(key) = definition
		&& let DeclKind::Package(_) = sema.declaration_kind(key)
	{
		return Some(format!("`{}`", file.name));
	}
	(compilation.comments(span.file_id))
		.documentation(&file.source, span.span.start)
}
