//! The callable selected at the cursor, with the parameter being written.
//! Syntax identifies the innermost argument list; the checker supplies the
//! selected signature. Everything is computed from the current snapshot.

use tower_lsp_server::ls_types::{
	Documentation, MarkupContent, MarkupKind, ParameterInformation,
	ParameterLabel, SignatureHelp, SignatureHelpParams, SignatureInformation,
};
use wx_compiler::ast::{ExprId, Expression};
use wx_compiler::tir::{DeclKind, Definition, Type};

use crate::call;
use crate::convert::position_to_offset;
use crate::hover;
use crate::state::ServerState;

pub(crate) fn signature_help(
	state: &mut ServerState,
	params: &SignatureHelpParams,
) -> Option<SignatureHelp> {
	let offsets = state.client.signature_label_offsets;
	let position = &params.text_document_position_params;
	let (snapshot, file) =
		state.resolve_uri_mut(&position.text_document.uri)?;
	let offset = position_to_offset(
		&snapshot.compilation.files,
		file,
		position.position,
	)?;
	let source = &snapshot.compilation.files.get(file).ok()?.source;
	let ast = snapshot.compilation.ast(file);
	let comments = &snapshot.compilation.comments(file).0;
	if comments.iter().any(|comment| {
		comment.span.start < offset && offset <= comment.span.end
	}) {
		return None;
	}
	// A child is stored before its parent. Choosing the narrowest argument
	// list finds the innermost call, even when the surrounding file is broken.
	let call = (0..ast.exprs.kinds.len())
		.map(|index| ExprId(index as u32))
		.filter(|&expr| {
			let (close, last) = match ast.expr(expr) {
				Expression::Call { arguments, .. } => (
					')',
					ast.list(arguments)
						.last()
						.map(|&arg| ast.expr_span(arg).end),
				),
				Expression::NamedCall { arguments, .. } => (
					'}',
					ast.list(arguments).last().map(|arg| {
						arg.value.map_or(arg.name.span.end, |value| {
							ast.expr_span(value).end
						})
					}),
				),
				_ => return false,
			};
			let span = ast.arguments_span(expr);
			let closed = source[..span.end as usize].ends_with(close)
				&& last.is_none_or(|last| last < span.end)
				&& !comments.iter().any(|comment| {
					comment.span.start < span.end
						&& span.end <= comment.span.end
				});
			span.start < offset
				&& (offset < span.end || (!closed && offset == span.end))
		})
		.min_by_key(|&expr| {
			let span = ast.arguments_span(expr);
			span.end - span.start
		})?;
	let owner = snapshot.expression_owner(file, call)?;
	let signature = call::signature(
		&mut snapshot.sema,
		&snapshot.strings,
		owner,
		ast,
		call,
	)?;
	let callee = match ast.expr(call) {
		Expression::Call { callee, .. }
		| Expression::NamedCall { callee, .. } => callee,
		_ => unreachable!(),
	};
	let name = match ast.expr(callee) {
		Expression::Path(segments)
		| Expression::QualifiedPath { segments, .. } => {
			let name = ast.list(segments).last()?.ident.inner;
			snapshot.strings.resolve(name)?.to_owned()
		}
		Expression::ObjectAccess { member, .. } => snapshot
			.strings
			.resolve(ast.segment(member).ident.inner)?
			.to_owned(),
		_ => ast.expr_span(callee).extract_str(source).trim().to_owned(),
	};
	let active = match ast.expr(call) {
		Expression::NamedCall { arguments, .. } => ast
			.list(arguments)
			.iter()
			.find(|arg| {
				arg.name.span.start <= offset
					&& offset
						<= arg.value.map_or(arg.name.span.end, |value| {
							ast.expr_span(value).end
						})
			})
			.and_then(|arg| {
				signature
					.parameters
					.iter()
					.position(|(name, _)| *name == Some(arg.name.inner))
			}),
		Expression::Call { arguments, .. } => {
			let arguments = ast.list(arguments);
			if signature.parameters.len() > 1 && signature.whole_argument {
				None
			} else if signature.parameters.len() == 1
				&& matches!(
					*snapshot.sema.types.resolve(signature.parameters[0].1),
					Type::Tuple { .. }
				) {
				Some(0)
			} else {
				let at = arguments
					.partition_point(|&arg| ast.expr_span(arg).end < offset);
				let at = if at > 0
					&& (at == arguments.len()
						|| offset < ast.expr_span(arguments[at]).start)
				{
					let end = ast.expr_span(arguments[at - 1]).end;
					let comma = source[end as usize..offset as usize]
						.char_indices()
						.any(|(rel, c)| {
							let at = end + rel as u32;
							c == ','
								&& !comments.iter().any(|comment| {
									comment.span.start <= at
										&& at < comment.span.end
								})
						});
					if comma { at } else { at - 1 }
				} else {
					at
				};
				(at < signature.parameters.len()).then_some(at)
			}
		}
		_ => unreachable!(),
	};
	let formatter = snapshot.sema.type_formatter(&snapshot.strings);
	let prefix = match signature.definition {
		Some(Definition::Item(loc))
			if matches!(
				snapshot.sema.declaration_kind(loc),
				DeclKind::Struct(_)
			) =>
		{
			""
		}
		_ => "func ",
	};
	let mut label = format!("{prefix}{name}(");
	let mut parameters = Vec::new();
	for (index, &(name, ty)) in signature.parameters.iter().enumerate() {
		if index > 0 {
			label.push_str(", ");
		}
		let start = label.encode_utf16().count() as u32;
		let text = match name.and_then(|name| snapshot.strings.resolve(name)) {
			Some(name) => format!("{name}: {}", formatter.display_type(ty)),
			None => formatter.display_type(ty),
		};
		label.push_str(&text);
		parameters.push(ParameterInformation {
			label: if offsets {
				ParameterLabel::LabelOffsets([
					start,
					label.encode_utf16().count() as u32,
				])
			} else {
				ParameterLabel::Simple(text)
			},
			documentation: None,
		});
	}
	label.push_str(&format!(
		") -> {}",
		formatter.display_type(signature.result)
	));
	let documentation = signature
		.definition
		.and_then(|definition| {
			hover::documentation(
				&snapshot.sema,
				&snapshot.compilation.files,
				definition,
			)
		})
		.map(|value| {
			Documentation::MarkupContent(MarkupContent {
				kind: MarkupKind::Markdown,
				value,
			})
		});
	Some(SignatureHelp {
		signatures: vec![SignatureInformation {
			label,
			documentation,
			parameters: Some(parameters),
			active_parameter: active.map(|index| index as u32),
		}],
		active_signature: Some(0),
		active_parameter: active.map(|index| index as u32),
	})
}
