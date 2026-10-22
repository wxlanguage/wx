//! Functions as values and direct calls: `f`, `f::<T>`, `f(a, b)`,
//! `f({ b, a: 1 })`.
//!
//! A call's type arguments are learned within the call, as a struct
//! construction's are: from what is written on the name, the expected result
//! type, and then each argument in order (`TypeInterner::learn`). What none of
//! them gives needs an annotation. Arguments are then held to their
//! parameter's final type, and the parameters' bounds are checked at the call.
//! A call by name binds each argument to the parameter of its name; the
//! arguments stay in written order, which is the order they are evaluated in.
//!
//! A struct construction is a call of the struct's constructor, whose
//! parameters are its fields: both are checked against a `CallTarget` by the
//! same code, with the same diagnostics. Each argument keeps the type it was
//! built with (`GivenArgument`), which is final unless it had an unknown part.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::{Arguments, BodyContext};
use crate::ast::{self, Separated, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{ArgOrder, ExprIdx, ExprKind, ParamIdx};
use crate::tir::defs::{
	BindingKey, FunctionIdx, FunctionOwner, InherentImplIdx, MemberKind,
	StructIdx,
};
use crate::tir::obligations::BoundRequirements;
use crate::tir::signatures::TypeContext;
use crate::tir::types::{
	Substitution, TypeEnvIdx, TypeEnvOwner, TypeIndex, TypeList,
};
use crate::vfs::FileId;

/// The function a call or a path selects, with what the call knows of it
/// before its arguments are checked.
pub(super) struct Callee {
	pub(super) function: FunctionIdx,
	/// The arguments of the frames around the function's own: an impl's, or
	/// `Self` for a trait's declaration; empty for a free function.
	pub(super) leading: Box<[TypeIndex]>,
	pub(super) dispatch: Dispatch,
	/// The inherent impl the callee was selected from before the impl's
	/// arguments were known, whose bounds the call proves once it has learned
	/// them (`Layout::of::<T>()`).
	pub(super) impl_bounds: Option<InherentImplIdx>,
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
			impl_bounds: None,
		}
	}
}

/// An argument a call gives, as checked: the parameter it is for, its value,
/// and the type it was built with, which it is held to at the end unless an
/// unknown part of it needs instantiating again.
#[derive(Clone, Copy)]
pub(super) struct GivenArgument {
	pub(super) param: ParamIdx,
	pub(super) value: ExprIdx,
	pub(super) expected: TypeIndex,
}

/// What a call calls: a function, or a struct's constructor, whose
/// parameters are the struct's fields. A call's arguments are checked against
/// either the same way, by position or by name.
#[derive(Clone, Copy)]
pub(super) enum CallTarget {
	Function(FunctionIdx),
	StructConstructor(StructIdx),
}

impl CallTarget {
	/// The frames the parameter types are written with: the whole chain the
	/// call's flat type arguments instantiate.
	fn type_params(self, cx: &TypeContext<'_, '_, '_>) -> TypeEnvIdx {
		match self {
			Self::Function(function) => {
				cx.functions[usize::from(function)].type_params
			}
			Self::StructConstructor(struct_index) => {
				cx.structs[usize::from(struct_index)].type_params
			}
		}
	}

	pub(super) fn owner(self) -> TypeEnvOwner {
		match self {
			Self::Function(function) => TypeEnvOwner::Function(function),
			Self::StructConstructor(struct_index) => {
				TypeEnvOwner::Struct(struct_index)
			}
		}
	}

	fn param_count(self, cx: &TypeContext<'_, '_, '_>) -> usize {
		match self {
			Self::Function(function) => {
				cx.functions[usize::from(function)].param_types.len()
			}
			Self::StructConstructor(struct_index) => {
				cx.structs[usize::from(struct_index)].field_types.len()
			}
		}
	}

	/// The parameter's type as declared, `self` included.
	pub(super) fn param_type(
		self,
		cx: &TypeContext<'_, '_, '_>,
		param: ParamIdx,
	) -> TypeIndex {
		match self {
			Self::Function(function) => {
				let params = cx.functions[usize::from(function)].param_types;
				cx.types.list(params)[usize::from(param)]
			}
			Self::StructConstructor(struct_index) => cx
				.types
				.list(cx.structs[usize::from(struct_index)].field_types)
				[usize::from(param)],
		}
	}

	/// The parameter's name as a call by name spells it, `None` when it is
	/// unnamed. A function's are its naming declaration's.
	fn param_name(
		self,
		cx: &TypeContext<'_, '_, '_>,
		param: ParamIdx,
	) -> Option<SymbolU32> {
		let name = match self {
			Self::Function(function) => {
				cx.defs.functions[usize::from(naming_declaration(cx, function))]
					.params[usize::from(param)]
			}
			Self::StructConstructor(struct_index) => {
				cx.defs.structs[usize::from(struct_index)].fields
					[usize::from(param)]
				.name
			}
		};
		name.map(|name| name.inner)
	}

	/// The first parameter from `from` on named `name`: a later one of the
	/// same name was reported on the declaration.
	fn find_param(
		self,
		cx: &TypeContext<'_, '_, '_>,
		name: SymbolU32,
		from: usize,
	) -> Option<ParamIdx> {
		match self {
			Self::Function(function) => cx.defs.functions
				[usize::from(naming_declaration(cx, function))]
			.params
			.iter()
			.enumerate()
			.skip(from)
			.find(|(_, param)| param.is_some_and(|param| param.inner == name))
			.map(|(at, _)| ParamIdx::new(at as u32)),
			Self::StructConstructor(struct_index) => cx.defs.structs
				[usize::from(struct_index)]
			.lookup
			.get(&name)
			.map(|&field| ParamIdx::new(usize::from(field) as u32))
			.filter(|&param| usize::from(param) >= from),
		}
	}

	/// What kind of target a diagnostic names: "function" or "struct
	/// constructor".
	fn kind(self) -> &'static str {
		match self {
			Self::Function(_) => "function",
			Self::StructConstructor(_) => "struct constructor",
		}
	}

	/// The target's name as written: the function's, or the struct's.
	fn name<'c>(self, cx: &'c TypeContext<'_, '_, '_>) -> &'c str {
		let name = match self {
			Self::Function(function) => {
				cx.defs.functions[usize::from(function)].name
			}
			Self::StructConstructor(struct_index) => {
				cx.defs.structs[usize::from(struct_index)].name
			}
		};
		cx.strings.resolve(name.inner).unwrap()
	}

	/// A label at the declaration's name, where a diagnostic points for the
	/// target's parameters.
	fn declared_here(self, cx: &TypeContext<'_, '_, '_>) -> Label<FileId> {
		let declaration = match self {
			Self::Function(function) => {
				let def = &cx.defs.functions[usize::from(function)];
				SourceSpan::new(def.file_id, def.name.span)
			}
			Self::StructConstructor(struct_index) => {
				let def = &cx.defs.structs[usize::from(struct_index)];
				SourceSpan::new(def.file_id, def.name.span)
			}
		};
		declaration.secondary_label().with_message("declared here")
	}
}

/// The declaration whose parameter names a call of `function` by name uses:
/// for a trait impl's function, its trait's declaration, so a call is named
/// the same whichever impl it reaches; otherwise the function itself. An impl
/// function its trait does not declare names its own.
fn naming_declaration(
	cx: &TypeContext<'_, '_, '_>,
	function: FunctionIdx,
) -> FunctionIdx {
	let def = &cx.defs.functions[usize::from(function)];
	let FunctionOwner::TraitImpl(impl_index) = def.owner else {
		return function;
	};
	let Some(trait_index) = cx.impl_dispatch.trait_header(impl_index).trait_def
	else {
		return function;
	};
	match cx.defs.declared_trait_member(
		trait_index.inner,
		BindingKey::value(def.name.inner),
	) {
		Some(
			MemberKind::Function(declaration) | MemberKind::Method(declaration),
		) => declaration,
		_ => function,
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
		let type_list = self.cx.types.push_list(&type_args);
		self.check_impl_bounds(&callee, segment, type_list);
		self.check_param_bounds(
			CallTarget::Function(function),
			own,
			segment,
			type_list,
			&[],
		);
		let ty = self.cx.types.intern_function(function, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		self.body.push(ExprKind::Function(function), ty, span)
	}

	/// `f(a, b)`, `Type::f(a, b)` or `receiver.f(a, b)`: a call of `callee`,
	/// by position or by name (`f({ b: 2, a })`). A method call's `receiver`
	/// is checked already and gives the first parameter.
	pub(super) fn build_function_call(
		&mut self,
		callee: Callee,
		segment: &ast::PathSegment,
		receiver: Option<ExprIdx>,
		arguments: Arguments<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let target = CallTarget::Function(callee.function);
		let return_type =
			self.cx.functions[usize::from(callee.function)].return_type;
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
		let mut given = Vec::new();
		if let Some(receiver) = receiver {
			let receiver_param = ParamIdx::new(0);
			self.learn_argument(
				target,
				&mut type_args,
				receiver_param,
				receiver,
			);
			// Checked before its parameter's type was instantiated, so it is
			// held to that type at the end.
			given.push(GivenArgument {
				param: receiver_param,
				value: receiver,
				expected: TypeIndex::INFER,
			});
		}
		let reported = self.build_arguments(
			target,
			&mut type_args,
			arguments,
			&mut given,
			span,
		);
		// A reported argument list may be why a type argument stays unknown.
		let poisoned = expected == TypeIndex::ERROR
			|| reported
			|| given.iter().any(|argument| {
				self.cx.types.has_error(self.body.ty(argument.value))
			});
		self.report_uninferred(
			env,
			segment.ident.span,
			poisoned,
			&mut type_args,
		);
		self.expect_arguments(target, &type_args, &given);
		// One stored list for the bound checks and the node.
		let type_list = self.cx.types.push_list(&type_args);
		self.check_impl_bounds(&callee, segment, type_list);
		self.check_param_bounds(target, own, segment, type_list, &given);
		let order = match arguments {
			Arguments::Positional(_) => ArgOrder::InOrder,
			Arguments::Named(_) => self
				.body
				.push_permutation(given.iter().map(|argument| argument.param)),
		};
		let args = self
			.body
			.push_args(given.iter().map(|argument| argument.value));
		let ty = self.instantiate(return_type, env, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		let kind = match callee.dispatch {
			Dispatch::Direct => ExprKind::Call {
				function: callee.function,
				type_args: type_list,
				args,
				order,
			},
			Dispatch::Abstract => ExprKind::AbstractCall {
				method: callee.function,
				type_args: type_list,
				args,
				order,
			},
		};
		self.body.push(kind, ty, span)
	}

	/// The arguments of a call of `target`, appended to `given` after the
	/// parameters it holds already (a method's receiver, which cannot be
	/// named), each built with its parameter's type as known so far and
	/// learned from. Returns whether the arguments were reported, which may be
	/// why a type argument stays unknown.
	pub(super) fn build_arguments(
		&mut self,
		target: CallTarget,
		type_args: &mut [TypeIndex],
		arguments: Arguments<'_>,
		given: &mut Vec<GivenArgument>,
		span: TextSpan,
	) -> bool {
		match arguments {
			Arguments::Positional(arguments) => self.positional_arguments(
				target, type_args, arguments, given, span,
			),
			Arguments::Named(arguments) => {
				self.named_arguments(target, type_args, arguments, given, span)
			}
		}
	}

	/// Holds each argument to its parameter's final type, once every type
	/// argument is known: an untyped literal takes its type only here. The
	/// type an argument was built with is final already unless it had an
	/// unknown part, since a known type argument never changes; only those
	/// are instantiated again.
	pub(super) fn expect_arguments(
		&mut self,
		target: CallTarget,
		type_args: &[TypeIndex],
		given: &[GivenArgument],
	) {
		let env = target.type_params(self.cx);
		for argument in given {
			let ty = if self.cx.types.has_infer(argument.expected) {
				let declared = target.param_type(self.cx, argument.param);
				self.instantiate(declared, env, type_args)
			} else {
				argument.expected
			};
			self.expect(argument.value, ty);
		}
	}

	/// What `value`, given for `param`, teaches the call's type arguments.
	fn learn_argument(
		&mut self,
		target: CallTarget,
		type_args: &mut [TypeIndex],
		param: ParamIdx,
		value: ExprIdx,
	) {
		let declared = target.param_type(self.cx, param);
		let env = target.type_params(self.cx);
		let actual = self.body.ty(value);
		self.cx.types.learn(
			&self.cx.type_envs,
			env,
			type_args,
			declared,
			actual,
		);
	}

	/// `f(a, b)`: the n-th argument gives the n-th parameter after those
	/// `given` holds. An argument past the last parameter is built and
	/// dropped.
	fn positional_arguments(
		&mut self,
		target: CallTarget,
		type_args: &mut [TypeIndex],
		arguments: &[Separated<Spanned<ast::Expression>>],
		given: &mut Vec<GivenArgument>,
		span: TextSpan,
	) -> bool {
		let skipped = given.len();
		let env = target.type_params(self.cx);
		let open = target.param_count(self.cx) - skipped;
		let reported = arguments.len() != open;
		if reported {
			self.report_argument_count(target, open, arguments.len(), span);
		}
		given.reserve_exact(arguments.len().min(open));
		for (at, argument) in arguments.iter().enumerate() {
			if at >= open {
				self.build(&argument.inner, TypeIndex::INFER);
				continue;
			}
			let param = ParamIdx::new((skipped + at) as u32);
			let declared = target.param_type(self.cx, param);
			let hint = self.instantiate(declared, env, type_args);
			let value = self.build(&argument.inner, hint);
			self.learn_argument(target, type_args, param, value);
			given.push(GivenArgument {
				param,
				value,
				expected: hint,
			});
		}
		reported
	}

	/// `f({ b: 2, a })`: each argument gives the parameter of its name, in
	/// written order. A target with an unnamed parameter is called by
	/// position only. An argument naming no parameter, or one already given,
	/// is built and dropped.
	fn named_arguments(
		&mut self,
		target: CallTarget,
		type_args: &mut [TypeIndex],
		arguments: &[Separated<Spanned<ast::NamedArgument>>],
		given: &mut Vec<GivenArgument>,
		span: TextSpan,
	) -> bool {
		let skipped = given.len();
		let env = target.type_params(self.cx);
		let count = target.param_count(self.cx);
		let positional_only = (skipped..count).any(|at| {
			target
				.param_name(self.cx, ParamIdx::new(at as u32))
				.is_none()
		});
		if positional_only {
			let (kind, target_name) = (target.kind(), target.name(self.cx));
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::PositionalOnlyCall.code())
					.with_message(format!(
						"{kind} `{target_name}` has an unnamed parameter, so \
						 it is called by position"
					))
					.with_label(Label::primary(self.scope.file_id, span))
					.with_label(target.declared_here(self.cx)),
			);
			for argument in arguments {
				self.build_named_argument(
					&argument.inner.inner,
					TypeIndex::INFER,
				);
			}
			return true;
		}
		given.reserve_exact(arguments.len().min(count - skipped));
		let mut reported = false;
		// Each parameter given by name, with its name as written.
		let mut named: Vec<(ParamIdx, TextSpan)> =
			Vec::with_capacity(arguments.len());
		for argument in arguments {
			let argument = &argument.inner.inner;
			let name = argument.name;
			let param = target.find_param(self.cx, name.inner, skipped);
			let hint = match param {
				Some(param) => {
					let declared = target.param_type(self.cx, param);
					self.instantiate(declared, env, type_args)
				}
				None => TypeIndex::INFER,
			};
			let value = self.build_named_argument(argument, hint);
			let param_name = self.cx.strings.resolve(name.inner).unwrap();
			let Some(param) = param else {
				let (kind, target_name) = (target.kind(), target.name(self.cx));
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::UnknownParameterName.code())
						.with_message(format!(
							"{kind} `{target_name}` has no parameter named \
							 `{param_name}`"
						))
						.with_label(Label::primary(
							self.scope.file_id,
							name.span,
						))
						.with_label(target.declared_here(self.cx)),
				);
				reported = true;
				continue;
			};
			if let Some(&(_, first)) =
				named.iter().find(|&&(named, _)| named == param)
			{
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::DuplicateNamedArgument.code(),
						)
						.with_message(format!(
							"argument `{param_name}` given more than once"
						))
						.with_label(Label::primary(
							self.scope.file_id,
							name.span,
						))
						.with_label(
							Label::secondary(self.scope.file_id, first)
								.with_message("first given here"),
						),
				);
				reported = true;
				continue;
			}
			self.learn_argument(target, type_args, param, value);
			named.push((param, name.span));
			given.push(GivenArgument {
				param,
				value,
				expected: hint,
			});
		}
		// A later parameter of a name declared twice is one no argument can
		// name; the duplicate was reported on the declaration.
		let missing: Vec<String> = (skipped..count)
			.map(|at| ParamIdx::new(at as u32))
			.filter(|&param| !named.iter().any(|&(named, _)| named == param))
			.filter_map(|param| {
				let name = target.param_name(self.cx, param)?;
				(target.find_param(self.cx, name, skipped) == Some(param)).then(
					|| format!("`{}`", self.cx.strings.resolve(name).unwrap()),
				)
			})
			.collect();
		if !missing.is_empty() {
			reported = true;
			let (kind, target_name) = (target.kind(), target.name(self.cx));
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::MissingArguments.code())
					.with_message(format!(
						"missing argument{} {} in call to {kind} \
						 `{target_name}`",
						if missing.len() == 1 { "" } else { "s" },
						missing.join(", ")
					))
					.with_label(Label::primary(self.scope.file_id, span))
					.with_label(target.declared_here(self.cx)),
			);
		}
		reported
	}

	/// A named argument's value: written, or for `{ x }` the value `x` names.
	fn build_named_argument(
		&mut self,
		argument: &ast::NamedArgument,
		hint: TypeIndex,
	) -> ExprIdx {
		match &argument.value {
			Some(value) => self.build(value, hint),
			None => {
				let path = [ast::PathSegment {
					ident: argument.name,
					type_args: Box::new([]),
				}];
				self.build_path(&path, argument.name.span)
			}
		}
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

	/// Records and checks the bounds of the impl `callee` was selected from
	/// with arguments still unknown, now that the stored flat list
	/// `type_args` holds them; they lead it, so the impl's arguments are its
	/// prefix. Reported at the callee's name.
	fn check_impl_bounds(
		&mut self,
		callee: &Callee,
		segment: &ast::PathSegment,
		type_args: TypeList,
	) {
		let Some(impl_index) = callee.impl_bounds else {
			return;
		};
		let env = self.cx.inherent_impls[usize::from(impl_index)]
			.as_ref()
			.expect("a selected impl has a header")
			.type_params;
		let arguments = type_args.prefix(self.cx.type_envs.generic_count(env));
		let reference = SourceSpan::new(self.scope.file_id, segment.ident.span);
		let mut obligations = Vec::new();
		for index in 0..arguments.len() {
			let argument = self.cx.types.list(arguments)[index];
			self.cx.record_bounds_check(
				&mut obligations,
				self.scope.env,
				BoundRequirements::Parameter {
					env,
					index,
					arguments,
				},
				Spanned {
					inner: argument,
					span: segment.ident.span,
				},
				reference,
				TypeEnvOwner::InherentImpl(impl_index),
			);
		}
		self.cx.check_now(&obligations);
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
		target: CallTarget,
		expected: usize,
		found: usize,
		span: TextSpan,
	) {
		let plural = |n: usize| if n == 1 { "" } else { "s" };
		let (kind, target_name) = (target.kind(), target.name(self.cx));
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::ArgumentCountMismatch.code())
				.with_message(format!(
					"{kind} `{target_name}` takes {expected} argument{} but \
					 {found} {} supplied",
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
				)
				.with_label(target.declared_here(self.cx)),
		);
	}
}
