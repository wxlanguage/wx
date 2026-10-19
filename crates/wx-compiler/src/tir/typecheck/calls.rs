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

/// The function a call or a path selects, with what the call knows of it
/// before its arguments are checked.
pub(super) struct Callee {
	pub(super) function: FunctionIdx,
	/// The arguments of the frames around the function's own: an impl's, or
	/// `Self` for a trait's declaration; empty for a free function.
	pub(super) leading: Box<[TypeIndex]>,
	pub(super) dispatch: Dispatch,
}

/// How a callee is reached.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Dispatch {
	/// The function itself is called (`Call`).
	Direct,
	/// The function is a trait's declaration, whose impl is selected once
	/// `Self` is known (`AbstractCall`).
	Abstract,
}

impl Callee {
	pub(super) fn free(function: FunctionIdx) -> Self {
		Self {
			function,
			leading: Box::new([]),
			dispatch: Dispatch::Direct,
		}
	}
}

impl BodyContext<'_, '_, '_, '_> {
	/// A function named without a call. It needs every type argument of its
	/// own written, since nothing else gives them.
	pub(super) fn build_function_value(
		&mut self,
		callee: Callee,
		segment: &ast::PathSegment,
		span: TextSpan,
	) -> ExprIdx {
		let function = callee.function;
		let (env, own) = self.function_frames(function);
		let mut type_args = self.callee_type_args(&callee, own, segment);
		self.report_uninferred(env, segment.ident.span, false, &mut type_args);
		self.check_param_bounds(
			own,
			TypeEnvOwner::Function(function),
			segment,
			&[],
			&type_args,
			&[],
		);
		let ty = self.cx.types.intern_function(function, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		self.body.push(ExprKind::Function(function), ty, span)
	}

	/// `f(a, b)`, `Type::f(a, b)` or `receiver.f(a, b)`: a call of `callee`,
	/// by position. A method call's `receiver` is checked already and gives
	/// the first parameter.
	pub(super) fn build_function_call(
		&mut self,
		callee: Callee,
		segment: &ast::PathSegment,
		receiver: Option<ExprIdx>,
		arguments: &[Separated<Spanned<ast::Expression>>],
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let function = &self.cx.functions[usize::from(callee.function)];
		let (params, return_type) =
			(function.params().to_vec(), function.return_type());
		let (env, own) = self.function_frames(callee.function);
		let mut type_args = self.callee_type_args(&callee, own, segment);
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
		let skipped = usize::from(receiver.is_some());
		let mut given = Vec::with_capacity(params.len());
		if let Some(receiver) = receiver {
			let actual = self.body.ty(receiver);
			self.cx.types.learn(
				&self.cx.type_envs,
				env,
				&mut type_args,
				params[0],
				actual,
			);
			given.push((0, receiver));
		}
		if arguments.len() + skipped != params.len() {
			self.report_argument_count(
				params.len() - skipped,
				arguments.len(),
				span,
			);
		}
		for (at, argument) in arguments.iter().enumerate() {
			let at = at + skipped;
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
			own,
			TypeEnvOwner::Function(callee.function),
			segment,
			&params,
			&type_args,
			&given,
		);
		let args = self.body.push_args(given.iter().map(|&(_, value)| value));
		let ty = self.instantiate(return_type, env, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		let type_args = self.cx.types.push_list(&type_args);
		let kind = match callee.dispatch {
			Dispatch::Direct => ExprKind::Call {
				function: callee.function,
				type_args,
				args,
			},
			Dispatch::Abstract => ExprKind::AbstractCall {
				method: callee.function,
				type_args,
				args,
			},
		};
		self.body.push(kind, ty, span)
	}

	/// A function's parameter frames: its whole chain, which its type
	/// arguments instantiate, and its own frame (`ROOT` when it declares no
	/// parameters, which then stores its parent's frame).
	fn function_frames(
		&self,
		function: FunctionIdx,
	) -> (TypeEnvIdx, TypeEnvIdx) {
		let env = self.cx.functions[usize::from(function)].type_params;
		let own = if env != TypeEnvIdx::ROOT
			&& self.cx.type_envs.owner(env) == TypeEnvOwner::Function(function)
		{
			env
		} else {
			TypeEnvIdx::ROOT
		};
		(env, own)
	}

	/// A callee's flat type arguments before its call is checked: the leading
	/// ones it was selected with, then those written for its own parameters.
	fn callee_type_args(
		&mut self,
		callee: &Callee,
		own: TypeEnvIdx,
		segment: &ast::PathSegment,
	) -> Box<[TypeIndex]> {
		let written = self.written_type_args(
			segment,
			own,
			TypeEnvOwner::Function(callee.function),
		);
		callee.leading.iter().chain(&written).copied().collect()
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
