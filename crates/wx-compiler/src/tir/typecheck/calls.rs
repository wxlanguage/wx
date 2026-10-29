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
//! parameters are its fields: both are checked against a `CallTarget`,
//! read once per call, by the same code, with the same diagnostics. Each
//! argument keeps the type it was built with (`GivenArgument`), which is
//! final unless it had an unknown part.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::{Arguments, BodyContext};
use crate::ast::{self, Separated, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{ElementOrder, ExprIdx, ExprKind, ParamIdx};
use crate::tir::defs::{
	AssocTypeIdx, BindingKey, FunctionIdx, MemberKind, MemberOwner, StructIdx,
};
use crate::tir::members::{TraitImplLookup, TraitMemberSelection};
use crate::tir::signatures::TypeContext;
use crate::tir::solver::SolverError;
use crate::tir::types::{
	Substitution, Type, TypeEnvIdx, TypeEnvOwner, TypeIndex, TypeList,
};
use crate::vfs::FileId;

/// A function a path or a value selects, with its flat type arguments,
/// every frame on its chain outer first: what the selection knows, `INFER`
/// where it knows nothing. The bounds of the first `proven` arguments were
/// proven where it was selected; the call proves the frames after them once
/// it has learned them.
pub(super) struct Callee {
	pub(super) function: FunctionIdx,
	pub(super) type_args: Box<[TypeIndex]>,
	pub(super) proven: usize,
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
	/// `function` with `leading` for the frames around its own (an impl's,
	/// or `Self` for a trait's declaration), the first `proven` of them
	/// proven, its own arguments left to the call.
	pub(super) fn new(
		cx: &TypeContext<'_, '_, '_>,
		function: FunctionIdx,
		leading: &[TypeIndex],
		proven: usize,
	) -> Self {
		let env = cx.functions[usize::from(function)].type_params;
		let mut type_args =
			vec![TypeIndex::INFER; cx.type_envs.generic_count(env)]
				.into_boxed_slice();
		type_args[..leading.len()].copy_from_slice(leading);
		Self {
			function,
			type_args,
			proven,
		}
	}
}

impl Dispatch {
	/// How a function or a constant `owner` declares is reached: a trait's
	/// declaration through the impl its `Self` selects, any other itself.
	pub(super) fn of(owner: MemberOwner) -> Self {
		match owner {
			MemberOwner::Trait(_) => Self::Abstract,
			_ => Self::Direct,
		}
	}
}

/// An argument a call gives, as checked: the parameter it is for, or `None`
/// for one value written for every parameter left (`f(p)`); the type that is
/// declared for it, written with the target's parameters; its value; and the
/// type it was built with, which it is held to at the end unless an unknown
/// part of it needs instantiating again.
#[derive(Clone, Copy)]
pub(super) struct GivenArgument {
	pub(super) param: Option<ParamIdx>,
	pub(super) declared: TypeIndex,
	pub(super) value: ExprIdx,
	pub(super) expected: TypeIndex,
}

/// What a call calls, read once per call: a function, or a struct's
/// constructor, whose parameters are the struct's fields. A call's arguments
/// are checked against either the same way, by position or by name.
pub(super) struct CallTarget<'ctx> {
	pub(super) kind: CallTargetKind,
	/// The frames the parameter types are written with: the whole chain the
	/// call's flat type arguments instantiate.
	pub(super) type_env: TypeEnvIdx,
	/// Each parameter's type as declared, `self` included.
	pub(super) param_types: TypeList,
	/// Each parameter's name as a call by name spells it, `None` when it is
	/// unnamed. A function's are its naming declaration's.
	pub(super) param_names: &'ctx [Option<Spanned<SymbolU32>>],
}

impl<'ctx> CallTarget<'ctx> {
	pub(super) fn function(
		cx: &TypeContext<'_, 'ctx, '_>,
		function: FunctionIdx,
	) -> Self {
		let signature = &cx.functions[usize::from(function)];
		Self {
			kind: CallTargetKind::Function(function),
			type_env: signature.type_params,
			param_types: signature.param_types,
			param_names: &cx.defs.functions
				[usize::from(naming_declaration(cx, function))]
			.params,
		}
	}

	pub(super) fn struct_constructor(
		cx: &TypeContext<'_, 'ctx, '_>,
		struct_index: StructIdx,
	) -> Self {
		let signature = &cx.structs[usize::from(struct_index)];
		Self {
			kind: CallTargetKind::StructConstructor(struct_index),
			type_env: signature.type_params,
			param_types: signature.field_types,
			param_names: &cx.defs.structs[usize::from(struct_index)]
				.field_names,
		}
	}

	/// The first parameter from `from` on named `name`: a later one of the
	/// same name was reported on the declaration.
	fn find_param(&self, name: SymbolU32, from: usize) -> Option<ParamIdx> {
		self.param_names
			.iter()
			.enumerate()
			.skip(from)
			.find(|(_, param)| param.is_some_and(|param| param.inner == name))
			.map(|(at, _)| ParamIdx::new(at as u32))
	}
}

/// Which declaration a `CallTarget` is, for what the checking itself does not
/// need: what a diagnostic names, and who owns a bound.
#[derive(Clone, Copy)]
pub(super) enum CallTargetKind {
	Function(FunctionIdx),
	StructConstructor(StructIdx),
}

impl CallTargetKind {
	pub(super) fn owner(self) -> TypeEnvOwner {
		match self {
			Self::Function(function) => TypeEnvOwner::Function(function),
			Self::StructConstructor(struct_index) => {
				TypeEnvOwner::Struct(struct_index)
			}
		}
	}

	/// What a diagnostic calls the target: "function" or "struct
	/// constructor".
	fn describe(self) -> &'static str {
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
	let MemberOwner::TraitImpl(impl_index) = def.owner else {
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
	/// A function named without a call. Its type arguments are written, or
	/// given by an expected item type of the same function (`local g: id<u8>
	/// = id;`); there are no arguments to learn from.
	pub(super) fn build_function_value(
		&mut self,
		callee: Callee,
		segment: &ast::PathSegment,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let Callee {
			function,
			mut type_args,
			proven,
		} = callee;
		let (env, own) = self.function_frames(function);
		self.write_type_args(
			segment,
			own,
			TypeEnvOwner::Function(function),
			&mut type_args,
		);
		let mut mismatched = false;
		if expected != TypeIndex::INFER && expected != TypeIndex::ERROR {
			let expected = self.normalized(expected, self.scope.env);
			let declared = self.cx.types.intern_function(
				function,
				self.cx.type_envs.identity_args(env),
			);
			self.cx.types.learn(
				&self.cx.type_envs,
				env,
				&mut type_args,
				declared,
				expected,
			);
			// No item of another type can teach its arguments: what is wrong
			// is the type, not a missing annotation.
			let same_item = matches!(
				*self.cx.types.resolve(expected),
				Type::Function { func_index, .. } if func_index == function
			);
			if !same_item
				&& !self.cx.types.has_infer(expected)
				&& type_args.iter().any(|&arg| self.cx.types.has_infer(arg))
			{
				let diagnostic = self.mismatch_at(expected, declared, span);
				self.cx.diagnostics.push(diagnostic);
				mismatched = true;
			}
		}
		self.settle_uninferred(
			env,
			segment.ident.span,
			mismatched,
			&mut type_args,
		);
		let type_list = self.cx.types.push_list(&type_args);
		let target = CallTarget::function(self.cx, function);
		self.check_callee_bounds(&target, proven, segment, type_list, &[]);
		let ty = self.cx.types.intern_function(function, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		let kind = ExprKind::Function {
			function,
			type_args: type_list,
		};
		self.body.push(kind, ty, span)
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
		let Callee {
			function,
			mut type_args,
			proven,
		} = callee;
		let target = CallTarget::function(self.cx, function);
		let return_type = self.cx.functions[usize::from(function)].return_type;
		let (env, own) = self.function_frames(function);
		self.write_type_args(
			segment,
			own,
			TypeEnvOwner::Function(function),
			&mut type_args,
		);
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
			let declared = self.cx.types.list(target.param_types)[0];
			self.learn_argument(&target, &mut type_args, declared, receiver);
			// Checked before its parameter's type was instantiated, so it is
			// held to that type at the end.
			given.push(GivenArgument {
				param: Some(ParamIdx::new(0)),
				declared,
				value: receiver,
				expected: TypeIndex::INFER,
			});
		}
		let reported = self.build_arguments(
			&target,
			&mut type_args,
			arguments,
			&mut given,
			span,
		);
		// A reported argument list may be why a type argument stays unknown.
		let already_reported = expected == TypeIndex::ERROR
			|| reported
			|| given.iter().any(|argument| {
				self.cx.types.has_error(self.body.ty(argument.value))
			});
		self.settle_uninferred(
			env,
			segment.ident.span,
			already_reported,
			&mut type_args,
		);
		self.expect_arguments(&target, &type_args, &given);
		// One stored list for the bound checks and the node.
		let type_list = self.cx.types.push_list(&type_args);
		self.check_callee_bounds(&target, proven, segment, type_list, &given);
		let skipped = usize::from(receiver.is_some());
		let args = self.arguments_value(
			&target, &type_args, &given, skipped, reported, span,
		);
		let ty = self.instantiate(return_type, env, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		let kind = self.call_node(function, type_list, receiver, args);
		self.body.push(kind, ty, span)
	}

	/// The node of a call of `function`: a trait's declaration is reached
	/// through the impl its `Self` selects (`Abstract*`), any other directly;
	/// a receiver makes it a method call.
	fn call_node(
		&self,
		function: FunctionIdx,
		type_args: TypeList,
		receiver: Option<ExprIdx>,
		args: ExprIdx,
	) -> ExprKind {
		let owner = self.cx.defs.functions[usize::from(function)].owner;
		match (Dispatch::of(owner), receiver) {
			(Dispatch::Direct, None) => ExprKind::Call {
				function,
				type_args,
				args,
			},
			(Dispatch::Abstract, None) => ExprKind::AbstractCall {
				method: function,
				type_args,
				args,
			},
			(Dispatch::Direct, Some(receiver)) => ExprKind::MethodCall {
				function,
				type_args,
				receiver,
				args,
			},
			(Dispatch::Abstract, Some(receiver)) => {
				ExprKind::AbstractMethodCall {
					method: function,
					type_args,
					receiver,
					args,
				}
			}
		}
	}

	/// The value of the parameters of `target` after the first `skipped` (a
	/// method's receiver, which `given` holds first), as a call node holds
	/// it, once every type argument is final: the one value written for them
	/// all, the argument of a lone one, or a tuple of the arguments in
	/// written order with the position each gives (`()` for none). A tuple of
	/// a reported list is `ERROR`.
	pub(super) fn arguments_value(
		&mut self,
		target: &CallTarget<'_>,
		type_args: &[TypeIndex],
		given: &[GivenArgument],
		skipped: usize,
		reported: bool,
		span: TextSpan,
	) -> ExprIdx {
		let given = &given[skipped..];
		let open = target.param_types.len() - skipped;
		if let [argument] = given
			&& (argument.param.is_none() || open == 1)
		{
			return argument.value;
		}
		let in_order = given.iter().enumerate().all(|(at, argument)| {
			argument.param == Some(ParamIdx::new((skipped + at) as u32))
		});
		let order = if in_order {
			ElementOrder::InOrder
		} else {
			self.body.push_permutation(given.iter().map(|argument| {
				let param = argument.param.expect("a whole value is alone");
				ParamIdx::new((usize::from(param) - skipped) as u32)
			}))
		};
		let ty = if reported {
			TypeIndex::ERROR
		} else {
			let declared = self.declared_after(target, skipped);
			self.instantiate(declared, target.type_env, type_args)
		};
		self.pack(given.iter().map(|argument| argument.value), order, ty, span)
	}

	/// The declared type of `target`'s parameters after the first `skipped`,
	/// as one value: their tuple, or a lone one's own type.
	fn declared_after(
		&mut self,
		target: &CallTarget<'_>,
		skipped: usize,
	) -> TypeIndex {
		self.cx.types.intern(Type::Tuple {
			elements: target.param_types.suffix(skipped),
		})
	}

	/// The arguments of a call of `target`, appended to `given` after the
	/// parameters it holds already (a method's receiver, which cannot be
	/// named), each built with its parameter's type as known so far and
	/// learned from. Returns whether the arguments were reported, which may be
	/// why a type argument stays unknown.
	pub(super) fn build_arguments(
		&mut self,
		target: &CallTarget<'_>,
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
		target: &CallTarget<'_>,
		type_args: &[TypeIndex],
		given: &[GivenArgument],
	) {
		for argument in given {
			let ty = if self.cx.types.has_infer(argument.expected) {
				self.instantiate(argument.declared, target.type_env, type_args)
			} else {
				argument.expected
			};
			self.expect(argument.value, ty);
		}
	}

	/// What `value`, given for a parameter declared `declared`, teaches the
	/// call's type arguments.
	fn learn_argument(
		&mut self,
		target: &CallTarget<'_>,
		type_args: &mut [TypeIndex],
		declared: TypeIndex,
		value: ExprIdx,
	) {
		let actual = self.body.ty(value);
		self.cx.types.learn(
			&self.cx.type_envs,
			target.type_env,
			type_args,
			declared,
			actual,
		);
	}

	/// `f(a, b)`: the n-th argument gives the n-th parameter after those
	/// `given` holds. An argument past the last parameter is built and
	/// dropped. The list is one value of the parameters left: when one is
	/// left, the parentheses only mark the call, and the whole list is its
	/// value (`g(a, b)` is `g((a, b))`); one argument for any other number
	/// is their value as a tuple (`f(p)`).
	fn positional_arguments(
		&mut self,
		target: &CallTarget<'_>,
		type_args: &mut [TypeIndex],
		arguments: &[Separated<Spanned<ast::Expression>>],
		given: &mut Vec<GivenArgument>,
		span: TextSpan,
	) -> bool {
		let skipped = given.len();
		let open = target.param_types.len() - skipped;
		if open == 1 && arguments.len() != 1 {
			return self.whole_argument_list(
				target, type_args, arguments, given, span,
			);
		}
		if open != 1
			&& let [argument] = arguments
		{
			return self
				.one_value_for_all(target, type_args, argument, given, span);
		}
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
			let declared =
				self.cx.types.list(target.param_types)[usize::from(param)];
			let hint = self.instantiate(declared, target.type_env, type_args);
			let value = self.build(&argument.inner, hint);
			self.learn_argument(target, type_args, declared, value);
			given.push(GivenArgument {
				param: Some(param),
				declared,
				value,
				expected: hint,
			});
		}
		reported
	}

	/// `f(p)` for a target with any number of parameters left but one: `p`
	/// is their value as one, a tuple of their types, and is held to it
	/// whole. One that is no tuple is a wrong count, which is what it most
	/// likely is (`f(a)` missing `b`).
	fn one_value_for_all(
		&mut self,
		target: &CallTarget<'_>,
		type_args: &mut [TypeIndex],
		argument: &Separated<Spanned<ast::Expression>>,
		given: &mut Vec<GivenArgument>,
		span: TextSpan,
	) -> bool {
		let skipped = given.len();
		let open = target.param_types.len() - skipped;
		let declared = self.declared_after(target, skipped);
		let hint = self.instantiate(declared, target.type_env, type_args);
		let value = self.build(&argument.inner, hint);
		let actual = self.body.ty(value);
		let is_tuple =
			matches!(self.cx.types.resolve(actual), Type::Tuple { .. });
		if !is_tuple {
			if !self.cx.types.has_error(actual) {
				self.report_argument_count(target, open, 1, span);
			}
			return true;
		}
		self.learn_argument(target, type_args, declared, value);
		given.push(GivenArgument {
			param: None,
			declared,
			value,
			expected: hint,
		});
		false
	}

	/// The written list as the value of the one parameter left, when it is
	/// not one argument. The parameter's type must be able to be that tuple:
	/// one not known yet learns it (`id(1, 2)`), any other is a wrong count.
	fn whole_argument_list(
		&mut self,
		target: &CallTarget<'_>,
		type_args: &mut [TypeIndex],
		arguments: &[Separated<Spanned<ast::Expression>>],
		given: &mut Vec<GivenArgument>,
		span: TextSpan,
	) -> bool {
		let param = ParamIdx::new(given.len() as u32);
		let declared =
			self.cx.types.list(target.param_types)[usize::from(param)];
		let hint = self.instantiate(declared, target.type_env, type_args);
		let fits = match *self.cx.types.resolve(hint) {
			Type::Tuple { elements } => elements.len() == arguments.len(),
			_ => self.cx.types.has_infer(hint),
		};
		if !fits {
			if hint != TypeIndex::ERROR {
				self.report_argument_count(target, 1, arguments.len(), span);
			}
			for argument in arguments {
				self.build(&argument.inner, TypeIndex::INFER);
			}
			return true;
		}
		let span = match (arguments.first(), arguments.last()) {
			(Some(first), Some(last)) => {
				TextSpan::new(first.inner.span.start, last.inner.span.end)
			}
			_ => span,
		};
		let value = self.build_tuple(arguments, hint, span);
		self.learn_argument(target, type_args, declared, value);
		given.push(GivenArgument {
			param: Some(param),
			declared,
			value,
			expected: hint,
		});
		false
	}

	/// `f({ b: 2, a })`: each argument gives the parameter of its name, in
	/// written order. A target with an unnamed parameter is called by
	/// position only. An argument naming no parameter, or one already given,
	/// is built and dropped.
	fn named_arguments(
		&mut self,
		target: &CallTarget<'_>,
		type_args: &mut [TypeIndex],
		arguments: &[Separated<Spanned<ast::NamedArgument>>],
		given: &mut Vec<GivenArgument>,
		span: TextSpan,
	) -> bool {
		let skipped = given.len();
		let count = target.param_names.len();
		let positional_only =
			target.param_names[skipped..].iter().any(Option::is_none);
		if positional_only {
			let (kind, target_name) =
				(target.kind.describe(), target.kind.name(self.cx));
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::PositionalOnlyCall.code())
					.with_message(format!(
						"{kind} `{target_name}` has an unnamed parameter, so \
						 it is called by position"
					))
					.with_label(Label::primary(self.scope.file_id, span))
					.with_label(target.kind.declared_here(self.cx)),
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
			let param = target.find_param(name.inner, skipped);
			let hint = match param {
				Some(param) => {
					let declared = self.cx.types.list(target.param_types)
						[usize::from(param)];
					self.instantiate(declared, target.type_env, type_args)
				}
				None => TypeIndex::INFER,
			};
			let value = self.build_named_argument(argument, hint);
			let param_name = self.cx.strings.resolve(name.inner).unwrap();
			let Some(param) = param else {
				let (kind, target_name) =
					(target.kind.describe(), target.kind.name(self.cx));
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
						.with_label(target.kind.declared_here(self.cx)),
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
			let declared =
				self.cx.types.list(target.param_types)[usize::from(param)];
			self.learn_argument(target, type_args, declared, value);
			named.push((param, name.span));
			given.push(GivenArgument {
				param: Some(param),
				declared,
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
				let name = target.param_names[usize::from(param)]?.inner;
				(target.find_param(name, skipped) == Some(param)).then(|| {
					format!("`{}`", self.cx.strings.resolve(name).unwrap())
				})
			})
			.collect();
		if !missing.is_empty() {
			reported = true;
			let (kind, target_name) =
				(target.kind.describe(), target.kind.name(self.cx));
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
					.with_label(target.kind.declared_here(self.cx)),
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
				self.build_path(&path, hint, argument.name.span)
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

	/// Proves, for the final flat `type_args`, the bounds of each frame on
	/// `target`'s chain after the first `proven` arguments: the selection
	/// proved those.
	fn check_callee_bounds(
		&mut self,
		target: &CallTarget<'_>,
		proven: usize,
		segment: &ast::PathSegment,
		type_args: TypeList,
		given: &[GivenArgument],
	) {
		let mut frame = target.type_env;
		while frame != TypeEnvIdx::ROOT {
			if self.cx.type_envs.parent_count(frame) >= proven {
				self.check_frame_bounds(
					target, frame, segment, type_args, given,
				);
			}
			frame = self.cx.type_envs.parent(frame).unwrap();
		}
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
		target: &CallTarget<'_>,
		expected: usize,
		found: usize,
		span: TextSpan,
	) {
		let plural = |n: usize| if n == 1 { "" } else { "s" };
		let (kind, target_name) =
			(target.kind.describe(), target.kind.name(self.cx));
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
				.with_label(target.kind.declared_here(self.cx)),
		);
	}
}

/// What a value is called through.
enum ValueCallee {
	/// `Call::call` of the value's type: its impl's, or the trait's
	/// declaration over `[V]` for an abstract `V: Call` or a function item.
	Call(Callee),
	/// A function reference, `func(A) -> R`, which is callable by a compiler
	/// rule.
	Reference { param: TypeIndex, result: TypeIndex },
}

impl BodyContext<'_, '_, '_, '_> {
	/// `v(a, b)` where `v` is a value, checked already: a local, a constant,
	/// or a computed callee. Its type says how it is called: through its
	/// `Call` impl, with the value as `self` and the arguments forming its
	/// `Args`, or as a function reference. A function item's arguments are
	/// its function's, by position or by name; any other type's form `Args`
	/// as a parameter list forms a function's type: none give `()`, one
	/// gives it whole, several give the elements of a tuple.
	pub(super) fn build_value_call(
		&mut self,
		value: ExprIdx,
		arguments: Arguments<'_>,
		span: TextSpan,
	) -> ExprIdx {
		let ty = self.normalized(self.body.ty(value), self.scope.env);
		let callee = self.value_callee(value, ty);
		let item = match *self.cx.types.resolve(ty) {
			Type::Function {
				func_index,
				type_args,
			} => Some((func_index, type_args)),
			_ => None,
		};
		let callee = match (callee, arguments, item) {
			(None, ..) => {
				self.build_unchecked_arguments(arguments);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
			(Some(_), Arguments::Named(_), None) => {
				self.report_named_value_call(ty, span);
				self.build_unchecked_arguments(arguments);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
			(
				Some(ValueCallee::Reference { param, result }),
				Arguments::Positional(arguments),
				_,
			) => {
				let args =
					self.build_packed_arguments(ty, param, arguments, span);
				let kind = ExprKind::CallRef {
					callee: value,
					args,
				};
				return self.body.push(kind, result, span);
			}
			(Some(ValueCallee::Call(callee)), ..) => callee,
			(Some(ValueCallee::Reference { .. }), Arguments::Named(_), _) => {
				unreachable!("a function reference is not an item")
			}
		};
		let (packed, result) = match (item, arguments) {
			(Some((function, type_args)), _) => {
				self.build_item_arguments(function, type_args, arguments, span)
			}
			// Read from the trait, not the impl's `call`, whose shape nothing
			// has checked yet.
			(None, Arguments::Positional(arguments)) => {
				let intrinsics = &self.cx.defs.intrinsics;
				let (args, result) =
					(intrinsics.call_args, intrinsics.call_result);
				let args_type = self.call_projection(ty, args);
				let packed =
					self.build_packed_arguments(ty, args_type, arguments, span);
				(packed, self.call_projection(ty, result))
			}
			(None, Arguments::Named(_)) => unreachable!("reported above"),
		};
		let type_args = self.cx.types.push_list(&callee.type_args);
		let kind =
			self.call_node(callee.function, type_args, Some(value), packed);
		self.body.push(kind, result, span)
	}

	/// The `Args` of a call of the item of `function`, applied to
	/// `type_args`, and its `Result`: the arguments are checked as a call of
	/// the function checks them, by position or by name, and placed where its
	/// parameter list puts them. Both types are read from the function, whose
	/// bounds were proven where the item was named.
	fn build_item_arguments(
		&mut self,
		function: FunctionIdx,
		type_args: TypeList,
		arguments: Arguments<'_>,
		span: TextSpan,
	) -> (ExprIdx, TypeIndex) {
		let target = CallTarget::function(self.cx, function);
		let mut type_args: Box<[TypeIndex]> =
			self.cx.types.list(type_args).into();
		let mut given = Vec::new();
		let reported = self.build_arguments(
			&target,
			&mut type_args,
			arguments,
			&mut given,
			span,
		);
		self.expect_arguments(&target, &type_args, &given);
		let return_type = self.cx.functions[usize::from(function)].return_type;
		let result = self.instantiate(return_type, target.type_env, &type_args);
		let args = self
			.arguments_value(&target, &type_args, &given, 0, reported, span);
		(args, result)
	}

	/// `<ty as Call>::{assoc}`, normalized; `ERROR` when std declares no such
	/// member.
	fn call_projection(
		&mut self,
		ty: TypeIndex,
		assoc: Option<AssocTypeIdx>,
	) -> TypeIndex {
		let (Some(trait_index), Some(assoc_type_index)) =
			(self.cx.defs.intrinsics.call, assoc)
		else {
			return TypeIndex::ERROR;
		};
		let projection = self.cx.types.intern(Type::AssocTypeProjection {
			trait_index,
			assoc_type_index,
			base: ty,
		});
		let projection = self.normalized(projection, self.scope.env);
		self.cx.types.collapse_error(projection)
	}

	/// A call's arguments as a tuple of `values`, spanning them (the call's
	/// `span` for none).
	pub(super) fn pack(
		&mut self,
		values: impl IntoIterator<Item = ExprIdx>,
		order: ElementOrder,
		ty: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let elements = self.body.push_args(values);
		let span = match self.body.args(elements) {
			[first, .., last] => TextSpan::new(
				self.body.span(*first).start,
				self.body.span(*last).end,
			),
			&[only] => self.body.span(only),
			[] => span,
		};
		self.body
			.push(ExprKind::Tuple { elements, order }, ty, span)
	}

	/// How a value of type `ty` is called, or `None` when it cannot be
	/// (reported, unless `ty` is an error).
	fn value_callee(
		&mut self,
		value: ExprIdx,
		ty: TypeIndex,
	) -> Option<ValueCallee> {
		if self.cx.types.has_error(ty) {
			return None;
		}
		let call = self.cx.defs.intrinsics.call.and_then(|call_trait| {
			let members = &self.cx.defs.traits[usize::from(call_trait)].members;
			members.iter().find_map(|member| match member.kind {
				MemberKind::Method(function) => Some((call_trait, function)),
				_ => None,
			})
		});
		let Some((call_trait, declaration)) = call else {
			self.report_not_callable(value, ty);
			return None;
		};
		// A trait's declaration is selected over `[Self]`.
		let over_self = |cx| Callee::new(cx, declaration, &[ty], 1);
		// A function item's impl is its own, which requires its function's
		// bounds, proven where the item was named.
		if let Type::Function { .. } = self.cx.types.resolve(ty) {
			return Some(ValueCallee::Call(over_self(self.cx)));
		}
		let found = if self.cx.types.has_literal(ty) {
			Ok(None)
		} else {
			self.cx
				.find_trait_impl_query(self.scope.env, ty, call_trait)
		};
		let callee = match found {
			Ok(Some(TraitImplLookup::Concrete { impl_index, args })) => {
				match self.cx.defs.select_trait_member(
					impl_index,
					MemberKind::Method(declaration),
				) {
					TraitMemberSelection::Impl(
						MemberKind::Method(function)
						| MemberKind::Function(function),
					) => Callee::new(self.cx, function, &args, args.len()),
					_ => over_self(self.cx),
				}
			}
			Ok(Some(TraitImplLookup::Abstract)) => over_self(self.cx),
			Ok(Some(TraitImplLookup::Builtin)) => {
				let Type::FunctionRef { param, result } =
					*self.cx.types.resolve(ty)
				else {
					unreachable!(
						"only a function reference is called by a rule"
					)
				};
				return Some(ValueCallee::Reference { param, result });
			}
			Ok(None) => {
				self.report_not_callable(value, ty);
				return None;
			}
			Err(error) => {
				let reference =
					SourceSpan::new(self.scope.file_id, self.body.span(value));
				match error {
					SolverError::Overflow => {
						self.cx
							.diagnostics
							.push(self.cx.overflow_diagnostic(reference));
					}
					SolverError::Cycle(cycle) => {
						self.cx
							.diagnostics
							.push(self.cx.cycle_diagnostic(&cycle, reference));
					}
					_ => {}
				}
				return None;
			}
		};
		Some(ValueCallee::Call(callee))
	}

	/// The value of `args_type`, the one parameter type a called value takes,
	/// from its written arguments: one argument is it whole, any other number
	/// are the elements of a tuple, which is `ERROR` when they cannot form it
	/// (reported).
	fn build_packed_arguments(
		&mut self,
		callee_type: TypeIndex,
		args_type: TypeIndex,
		arguments: &[Separated<Spanned<ast::Expression>>],
		span: TextSpan,
	) -> ExprIdx {
		if let [argument] = arguments {
			let value = self.build(&argument.inner, args_type);
			return self.expect(value, args_type);
		}
		let element_types = match *self.cx.types.resolve(args_type) {
			Type::Tuple { elements } if elements.len() == arguments.len() => {
				Some(elements)
			}
			_ => None,
		};
		if element_types.is_none() && args_type != TypeIndex::ERROR {
			self.report_value_argument_count(
				callee_type,
				args_type,
				arguments.len(),
				span,
			);
		}
		// Built before they are packed: building each borrows the body.
		let values: Vec<ExprIdx> = arguments
			.iter()
			.enumerate()
			.map(|(at, argument)| {
				let hint = element_types.map_or(TypeIndex::ERROR, |types| {
					self.cx.types.list(types)[at]
				});
				let value = self.build(&argument.inner, hint);
				self.expect(value, hint)
			})
			.collect();
		let ty = match element_types {
			Some(_) => args_type,
			None => TypeIndex::ERROR,
		};
		self.pack(values, ElementOrder::InOrder, ty, span)
	}

	/// Checks the arguments of a call that has no target, for their own
	/// diagnostics.
	fn build_unchecked_arguments(&mut self, arguments: Arguments<'_>) {
		match arguments {
			Arguments::Positional(arguments) => {
				for argument in arguments {
					self.build(&argument.inner, TypeIndex::ERROR);
				}
			}
			Arguments::Named(arguments) => {
				for argument in arguments {
					self.build_named_argument(
						&argument.inner.inner,
						TypeIndex::ERROR,
					);
				}
			}
		}
	}

	fn report_not_callable(&mut self, value: ExprIdx, ty: TypeIndex) {
		let ty = self.cx.type_formatter().display_type(ty);
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TraitBoundViolation.code())
				.with_message(format!(
					"the trait bound `{ty}: Call` is not satisfied"
				))
				.with_label(
					Label::primary(self.scope.file_id, self.body.span(value))
						.with_message(format!(
							"the trait `Call` is not implemented for `{ty}`"
						)),
				),
		);
	}

	fn report_named_value_call(&mut self, ty: TypeIndex, span: TextSpan) {
		let ty = self.cx.type_formatter().display_type(ty);
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::PositionalOnlyCall.code())
				.with_message(format!(
					"a value of type `{ty}` is called through `Call`, so it is \
					 called by position"
				))
				.with_label(Label::primary(self.scope.file_id, span)),
		);
	}

	fn report_value_argument_count(
		&mut self,
		callee_type: TypeIndex,
		args_type: TypeIndex,
		found: usize,
		span: TextSpan,
	) {
		let expected = match *self.cx.types.resolve(args_type) {
			Type::Tuple { elements } if elements.is_empty() => {
				"no arguments".to_string()
			}
			Type::Tuple { elements } => {
				format!("1 or {} arguments", elements.len())
			}
			_ => "1 argument".to_string(),
		};
		let formatter = self.cx.type_formatter();
		let (callee_type, args_type) = (
			formatter.display_type(callee_type),
			formatter.display_type(args_type),
		);
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::ArgumentCountMismatch.code())
				.with_message(format!(
					"a value of type `{callee_type}` is called with \
					 `{args_type}`, but {found} arguments were supplied"
				))
				.with_label(
					Label::primary(self.scope.file_id, span)
						.with_message(format!("expected {expected}")),
				),
		);
	}
}
