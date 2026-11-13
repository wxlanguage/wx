//! Call-site signatures shared by signature help and named-argument
//! completion. The server assembles this data on demand from checked calls;
//! no extra information is recorded while checking.

use string_interner::symbol::SymbolU32;
use wx_compiler::ast::{AST, ExprId, Expression, StringInterner};
use wx_compiler::tir::{
	BodyOwner, Call, Definition, Operand, Semantics, Type, TypeIndex,
};

/// Call-site types and the definition used to present a signature. Receiver
/// omission and fallback to declared generic names are server presentation
/// choices; the compiler supplies the checked call and type operations.
pub(crate) struct CallSignature {
	pub(crate) parameters: Vec<(Option<SymbolU32>, TypeIndex)>,
	pub(crate) result: TypeIndex,
	pub(crate) definition: Option<Definition>,
	/// A single written tuple supplies the complete parameter list.
	pub(crate) whole_argument: bool,
}

pub(crate) fn signature(
	sema: &mut Semantics,
	strings: &StringInterner,
	owner: BodyOwner,
	ast: &AST,
	call: ExprId,
) -> Option<CallSignature> {
	let callee = match ast.expr(call) {
		Expression::Call { callee, .. }
		| Expression::NamedCall { callee, .. } => callee,
		_ => return None,
	};
	let body = sema.owner_body(owner)?;
	let Operand::Value(value) = body.operand_of(ast, call)? else {
		return None;
	};
	let checked = sema.call_of(owner, value)?;
	let packed = match &checked {
		Call::Function { arguments, .. }
		| Call::Reference { arguments, .. } => *arguments,
		Call::Constructor { fields, .. } => *fields,
	};
	let whole_argument = match ast.expr(call) {
		Expression::Call { arguments, .. } => match ast.list(arguments) {
			&[arg] => {
				body.operand_of(ast, arg) == Some(packed)
					&& matches!(
						*sema.types.resolve(body.operand_ty(packed)),
						Type::Tuple { .. }
					)
			}
			_ => false,
		},
		_ => false,
	};
	let (definition, env, names, params, args, skipped, result) = match checked
	{
		Call::Function {
			function,
			type_args,
			receiver,
			..
		} => {
			// Calling a function item uses its declared parameter list. The
			// checked node reaches it through `Call::call`, whose packed Args
			// describe implementation rather than how this call is written.
			let item = body
				.operand_of(ast, callee)
				.map(|operand| body.operand_ty(operand))
				.and_then(|ty| match *sema.types.resolve(ty) {
					Type::Function {
						func_index,
						type_args,
					} => Some((func_index, type_args)),
					_ => None,
				});
			let (function, args, skipped) = match item {
				Some((function, args)) if receiver.is_some() => {
					(function, sema.types.list(args).to_vec(), 0)
				}
				_ => (
					function,
					sema.generic_args.types(type_args).to_vec(),
					usize::from(receiver.is_some()),
				),
			};
			let decl = &sema.decls.functions[usize::from(function)];
			let signature = &sema.functions[usize::from(function)];
			let names = sema
				.function_parameter_names(function)
				.iter()
				.map(|name| name.map(|name| name.inner))
				.collect::<Vec<_>>();
			(
				Some(Definition::Item(decl.loc)),
				signature.type_params,
				names,
				sema.types.list(signature.param_types).to_vec(),
				args,
				skipped,
				signature.return_type,
			)
		}
		Call::Constructor { structure, .. } => {
			let decl = &sema.decls.structs[usize::from(structure)];
			let signature = &sema.structs[usize::from(structure)];
			let ty = body.operand_ty(Operand::Value(value));
			let args = match *sema.types.resolve(ty) {
				Type::Struct { type_args, .. } => {
					sema.types.list(type_args).to_vec()
				}
				_ => sema
					.generic_envs
					.identity_args(signature.type_params)
					.to_vec(),
			};
			let names = decl
				.field_names
				.iter()
				.map(|name| name.map(|name| name.inner))
				.collect::<Vec<_>>();
			let params = sema.types.list(signature.field_types).to_vec();
			let definition = Definition::Item(decl.loc);
			let env = signature.type_params;
			let result = sema.types.intern_struct(structure, &args);
			(Some(definition), env, names, params, args, 0, result)
		}
		Call::Reference { callee, .. } => {
			let Type::TypedFuncref { param, result } =
				*sema.types.resolve(body.operand_ty(callee))
			else {
				return None;
			};
			let parameters = match *sema.types.resolve(param) {
				Type::Tuple { elements } => sema
					.types
					.list(elements)
					.iter()
					.map(|&ty| (None, ty))
					.collect(),
				_ => vec![(None, param)],
			};
			return Some(CallSignature {
				parameters,
				result,
				definition: None,
				whole_argument,
			});
		}
	};
	let identity = sema.generic_envs.identity_args(env);
	let args: Vec<_> = args
		.iter()
		.enumerate()
		.map(|(at, &arg)| {
			if sema.types.has_error(arg) || arg == TypeIndex::INFER {
				identity[at]
			} else {
				arg
			}
		})
		.collect();
	let mut types = Vec::new();
	for ty in params
		.into_iter()
		.skip(skipped)
		.chain(std::iter::once(result))
	{
		let ty = sema.substitute_type(ty, env, &args);
		types.push(sema.normalize_in_body(strings, owner, ty).unwrap_or(ty));
	}
	let result = types.pop()?;
	Some(CallSignature {
		parameters: names.into_iter().skip(skipped).zip(types).collect(),
		result,
		definition,
		whole_argument,
	})
}
