//! Functions as values and direct calls: `f`, `f::<T>`, `f(a, b)`.
//!
//! A call's type arguments are learned within the call, as a struct
//! construction's are: from what is written on the name, the expected result
//! type, and then each argument in order (`TypeInterner::learn`). What none of
//! them gives needs an annotation. Arguments are then held to their
//! parameter's final type, and the parameters' bounds are checked at the call.

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::BodyContext;
use crate::ast::{self, Separated, Spanned};
use crate::diagnostics::{DiagnosticCode, TextSpan};
use crate::tir::body::{ExprIdx, ExprKind};
use crate::tir::defs::FunctionIdx;
use crate::tir::types::{Substitution, TypeEnvIdx, TypeEnvOwner, TypeIndex};

impl BodyContext<'_, '_, '_, '_> {
	/// A function named without a call. It needs every type argument
	/// written, since nothing else gives them.
	pub(super) fn build_function_value(
		&mut self,
		function_index: FunctionIdx,
		segment: &ast::PathSegment,
		span: TextSpan,
	) -> ExprIdx {
		let env = self.cx.functions[usize::from(function_index)].type_params;
		let owner = TypeEnvOwner::Function(function_index);
		let mut type_args = self.written_type_args(segment, env, owner);
		self.report_uninferred(env, segment.ident.span, false, &mut type_args);
		self.check_param_bounds(env, owner, segment, &[], &type_args, &[]);
		let ty = self.cx.types.intern_function(function_index, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		self.body.push(ExprKind::Function(function_index), ty, span)
	}

	/// `f(a, b)`: a call of the function `callee` names, by position.
	pub(super) fn build_function_call(
		&mut self,
		function_index: FunctionIdx,
		segment: &ast::PathSegment,
		arguments: &[Separated<Spanned<ast::Expression>>],
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let function = &self.cx.functions[usize::from(function_index)];
		let (env, params, return_type) = (
			function.type_params,
			function.params().to_vec(),
			function.return_type(),
		);
		let owner = TypeEnvOwner::Function(function_index);
		let mut type_args = self.written_type_args(segment, env, owner);
		// The result is learned from first: a disagreement teaches nothing,
		// and the call's own type is held to the expected one by the caller.
		if expected != TypeIndex::INFER && expected != TypeIndex::ERROR {
			let expected = self.normalized(expected, self.scope.env);
			self.cx.types.learn(
				&self.cx.type_envs,
				env,
				&mut type_args,
				return_type,
				expected,
			);
		}
		if arguments.len() != params.len() {
			self.report_argument_count(params.len(), arguments.len(), span);
		}
		let mut given = Vec::with_capacity(params.len());
		for (at, argument) in arguments.iter().enumerate() {
			// An argument past the last parameter is checked and dropped.
			let Some(&param) = params.get(at) else {
				self.build(&argument.inner, TypeIndex::INFER);
				continue;
			};
			let hint = self.instantiate(param, env, &type_args);
			let value = self.build(&argument.inner, hint);
			let actual = self.body.ty(value);
			self.cx.types.learn(
				&self.cx.type_envs,
				env,
				&mut type_args,
				param,
				actual,
			);
			given.push((at, value));
		}
		let poisoned = expected == TypeIndex::ERROR
			|| given.iter().any(|&(_, value)| {
				self.cx.types.has_error(self.body.ty(value))
			});
		self.report_uninferred(
			env,
			segment.ident.span,
			poisoned,
			&mut type_args,
		);
		// Every type argument is known now, so each argument is held to its
		// parameter's final type: an untyped literal takes it only here.
		for &(at, value) in &given {
			let param = self.instantiate(params[at], env, &type_args);
			self.expect(value, param);
		}
		self.check_param_bounds(
			env, owner, segment, &params, &type_args, &given,
		);
		let args = self.body.push_args(given.iter().map(|&(_, value)| value));
		let ty = self.instantiate(return_type, env, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		let type_args = self.cx.types.push_list(&type_args);
		self.body.push(
			ExprKind::Call {
				function: function_index,
				type_args,
				args,
			},
			ty,
			span,
		)
	}

	/// `ty`, written with the parameters of `env`, with `args` for them. A
	/// type argument not known yet leaves its parts `INFER`, which expect
	/// nothing; one that failed makes the whole type `ERROR`.
	fn instantiate(
		&mut self,
		ty: TypeIndex,
		env: TypeEnvIdx,
		args: &[TypeIndex],
	) -> TypeIndex {
		let ty = self.cx.types.substitute(
			ty,
			Substitution {
				envs: &self.cx.type_envs,
				env,
				args,
			},
		);
		let ty = self.normalized(ty, self.scope.env);
		self.cx.types.collapse_error(ty)
	}

	fn report_argument_count(
		&mut self,
		expected: usize,
		found: usize,
		span: TextSpan,
	) {
		let plural = |n: usize| if n == 1 { "" } else { "s" };
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::ArgumentCountMismatch.code())
				.with_message(format!(
					"this function takes {expected} argument{} but {found} {} \
					 supplied",
					plural(expected),
					if found == 1 { "was" } else { "were" }
				))
				.with_label(
					Label::primary(self.scope.file_id, span).with_message(
						format!(
							"expected {expected} argument{}, found {found}",
							plural(expected)
						),
					),
				),
		);
	}
}
