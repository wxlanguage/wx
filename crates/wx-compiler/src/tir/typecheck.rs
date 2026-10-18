//! Expression checking: lowers written expressions into a `Body`, with every
//! node typed. One checker for every expression, whatever owns it; constant
//! initializers are the first owner, function bodies follow.
//!
//! Operators are checked through their trait (`OperatorTraits`): the trait
//! decides whether the operator applies to a type. The node built for it is a
//! builtin `Binary`/`Unary` on a primitive scalar, and a method call otherwise.
//!
//! Untyped literals keep the pseudo-types `Integer`/`Float` until context
//! gives them one (`coerce`), which rewrites the subtree in place.
//!
//! A struct's name is a value only to be called: calling it constructs the
//! struct (`StructConstructor`). It is not a function, and naming it without a call is
//! an error. A generic struct's type arguments are learned within the call,
//! from what is written on its name, the expected type and the fields' values
//! (`TypeInterner::meet`/`learn`); what none of them gives needs an
//! annotation.

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::body::{
	ArgOrder, Body, BodyBuilder, ExprIdx, ExprKind, ExprRange, ParamIdx,
};
use super::defs::{
	BindingTarget, ConstIdx, DefKey, DefKind, FieldIdx, MemberKind, StructIdx,
	Tier, TypesetIdx,
};
use super::imports::report_private_identifier;
use super::literals::{CharLiteralError, parse_char_literal};
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::obligations::BoundRequirements;
use super::operators::{
	Scalar, is_builtin_binary, is_builtin_unary, is_comparison,
};
use super::paths::PathResolver;
use super::signatures::{InferPolicy, LexicalScope, TypeContext};
use super::types::{Substitution, Type, TypeEnvIdx, TypeEnvOwner, TypeIndex};
use crate::ast::{self, BinaryOp, Spanned, UnaryOp};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::operators::OperatorMethod;
use crate::vfs::FileId;

/// Checks the expressions of one definition into a `Body`.
pub(super) struct BodyContext<'a, 'ast, 'ctx, 'dispatch> {
	cx: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
	body: BodyBuilder,
	/// Where the expressions are written. Its type scope is the root for a
	/// free constant, the impl's or trait's `Self` scope for an associated one.
	scope: LexicalScope,
}

impl<'a, 'ast, 'ctx, 'dispatch> BodyContext<'a, 'ast, 'ctx, 'dispatch> {
	pub(super) fn new(
		cx: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
		scope: LexicalScope,
	) -> Self {
		Self {
			cx,
			body: BodyBuilder::default(),
			scope,
		}
	}

	/// Checks `expr` as the whole body, against `expected`.
	pub(super) fn check_body(
		mut self,
		expr: &Spanned<ast::Expression>,
		expected: TypeIndex,
	) -> Body {
		let expected = self.normalized(expected, self.scope.env);
		let root = self.check(expr, expected);
		self.body.finish(root)
	}

	/// Checks an enum variant's value as a value of the enum's `repr`. A
	/// variant written without one counts on from `previous`, the variant
	/// before it; the first variant has nothing to count from.
	pub(super) fn check_variant_value(
		mut self,
		variant: &ast::EnumVariant,
		previous: Option<ConstIdx>,
		repr: TypeIndex,
	) -> Body {
		let span = variant.name.span;
		// A missing or non-integer repr was reported on the enum; checking each
		// value against it would only repeat that.
		if repr == TypeIndex::ERROR {
			let root = self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			return self.body.finish(root);
		}
		let root = match (variant.value.as_deref(), previous) {
			(Some(value), _) => self.check(value, repr),
			(None, Some(previous)) => {
				self.body
					.push(ExprKind::NextDiscriminant(previous), repr, span)
			}
			(None, None) => {
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::EnumVariantRequiresExplicitValue
								.code(),
						)
						.with_message("enum variant requires an explicit value")
						.with_label(
							Label::primary(self.scope.file_id, span)
								.with_message("add `= <value>` here"),
						)
						.with_note(
							"or add a value to an earlier variant to anchor \
							 auto-increment",
						),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
		};
		self.body.finish(root)
	}

	/// Builds `expr` and holds it to `expected`: an untyped literal takes that
	/// type, any other type must equal it. `INFER` and `ERROR` expect nothing.
	fn check(
		&mut self,
		expr: &Spanned<ast::Expression>,
		expected: TypeIndex,
	) -> ExprIdx {
		let built = self.build(expr, expected);
		self.expect(built, expected)
	}

	fn expect(&mut self, expr: ExprIdx, expected: TypeIndex) -> ExprIdx {
		if expected == TypeIndex::INFER || expected == TypeIndex::ERROR {
			return expr;
		}
		let actual = self.body.ty(expr);
		if self.cx.types.has_untyped(actual) {
			self.coerce(expr, expected);
		} else if actual != TypeIndex::ERROR && actual != expected {
			let diagnostic = self.report_type_mismatch(expected, actual, expr);
			self.cx.diagnostics.push(diagnostic);
			// Reported: nothing reads a value from it, or reports it again.
			self.body.set_ty(expr, TypeIndex::ERROR);
		}
		expr
	}

	/// Lowers `expr`. `expected` is the type the context hints at this site:
	/// `INFER` is no constraint, and a type with `INFER` positions in it
	/// (`Wrapper<_>`) constrains only the others. A construct whose meaning
	/// depends on its type reads it; the node's type may still differ, which
	/// is `expect`'s to report. An untyped literal stays untyped.
	fn build(
		&mut self,
		expr: &Spanned<ast::Expression>,
		expected: TypeIndex,
	) -> ExprIdx {
		let span = expr.span;
		match &expr.inner {
			ast::Expression::Int { value } => {
				self.body
					.push(ExprKind::Int(*value), TypeIndex::INTEGER, span)
			}
			// The value is read from the source once the width is known.
			ast::Expression::Float => {
				self.body.push(ExprKind::Float(0.0), TypeIndex::FLOAT, span)
			}
			ast::Expression::True => {
				self.body.push(ExprKind::Bool(true), TypeIndex::BOOL, span)
			}
			ast::Expression::False => {
				self.body.push(ExprKind::Bool(false), TypeIndex::BOOL, span)
			}
			ast::Expression::Char => self.build_char(span),
			ast::Expression::Grouping { value } => self.build(value, expected),
			ast::Expression::Unary { operator, operand } => {
				self.build_unary(*operator, operand, expected, span)
			}
			ast::Expression::Binary {
				left,
				operator,
				right,
			} => self.build_binary(*operator, left, right, expected, span),
			ast::Expression::Path(segments) => self.build_path(segments, span),
			ast::Expression::Call { callee, arguments } => self.build_call(
				callee,
				Arguments::Positional(arguments),
				expected,
				span,
			),
			ast::Expression::NamedCall { callee, arguments } => self
				.build_call(
					callee,
					Arguments::Named(arguments),
					expected,
					span,
				),
			ast::Expression::Tuple { elements } => {
				self.build_tuple(elements, expected, span)
			}
			ast::Expression::Error => {
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
			_ => todo!("checking this expression form"),
		}
	}

	/// A tuple, each element built with the expected type's element at its
	/// position when the expected type is a tuple as long. Its type is its
	/// elements': one with an untyped literal in it is untyped, and takes its
	/// type from context later, as a literal does (`coerce`).
	fn build_tuple(
		&mut self,
		elements: &[Spanned<ast::Expression>],
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let hints = match *self.cx.types.resolve(expected) {
			Type::Tuple { elements: hints }
				if hints.len() == elements.len() =>
			{
				Some(hints)
			}
			_ => None,
		};
		let mut values = Vec::with_capacity(elements.len());
		let mut types = Vec::with_capacity(elements.len());
		for (at, element) in elements.iter().enumerate() {
			let hint = match hints {
				Some(hints) => self.cx.types.list(hints)[at],
				None => TypeIndex::INFER,
			};
			let value = self.build(element, hint);
			values.push(value);
			types.push(self.body.ty(value));
		}
		let ty = self.cx.types.intern_tuple(&types);
		let ty = self.cx.types.collapse_error(ty);
		let elements = self.body.push_args(values);
		self.body.push(ExprKind::Tuple { elements }, ty, span)
	}

	fn build_char(&mut self, span: TextSpan) -> ExprIdx {
		let source = &self.cx.files.get(self.scope.file_id).unwrap().source;
		match parse_char_literal(span.extract_str(source)) {
			Ok(value) => {
				self.body.push(ExprKind::Char(value), TypeIndex::CHAR, span)
			}
			Err(error) => {
				let message = match error {
					CharLiteralError::Empty => "empty character literal",
					CharLiteralError::TooLong => {
						"character literal may only contain one codepoint"
					}
				};
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidCharacterLiteral.code(),
						)
						.with_message(message)
						.with_label(Label::primary(self.scope.file_id, span)),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
		}
	}

	/// A value path. Only constants, enum variants and struct names are
	/// checked yet.
	fn build_path(
		&mut self,
		segments: &[ast::PathSegment],
		span: TextSpan,
	) -> ExprIdx {
		let walk = PathResolver::new(
			self.cx.diagnostics,
			self.cx.resolutions,
			self.cx.strings,
			self.cx.defs,
		)
		.walk_path(
			self.scope.file_id,
			self.scope.namespace,
			segments,
			Tier::Value,
		);
		let Some(key) = walk.target.def_key() else {
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		let kind = key.symbol_kind(self.cx.defs);
		// A bare struct name is an error of its own, whoever may construct it.
		if let BindingTarget::Inaccessible(_) = walk.target
			&& !matches!(kind, DefKind::Struct(_))
		{
			let segment = &segments[walk.stopped_at as usize];
			self.cx.diagnostics.push(report_private_identifier(
				&self.cx.defs.namespaces,
				self.cx.strings,
				segment.ident.inner,
				SourceSpan::new(self.scope.file_id, segment.ident.span),
				Some(key),
			));
		}
		if !walk.is_complete(segments) {
			todo!("checking a value path through a type");
		}
		match kind {
			DefKind::Const(const_index) | DefKind::EnumVariant(const_index) => {
				let (ty, scope) = self.cx.constant_type(const_index);
				let ty = self.normalized(ty, scope);
				self.body.push(ExprKind::Const(const_index), ty, span)
			}
			DefKind::Struct(struct_index) => {
				let name = self.cx.defs.structs[usize::from(struct_index)].name;
				let name = self.cx.strings.resolve(name.inner).unwrap();
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::StructUsedAsValue.code())
						.with_message(format!(
							"expected a value, found struct `{name}`"
						))
						.with_label(Label::primary(self.scope.file_id, span))
						.with_note(format!(
							"a struct's name is only a value when it is called: \
							 `{name}(...)`"
						)),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
			_ => todo!("checking a path to a `{}`", kind.noun()),
		}
	}

	/// A call. Only the construction of a struct is checked yet.
	fn build_call(
		&mut self,
		callee: &Spanned<ast::Expression>,
		arguments: Arguments<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let ast::Expression::Path(segments) = &callee.inner else {
			todo!("checking a call of a computed callee");
		};
		let walk = PathResolver::new(
			self.cx.diagnostics,
			self.cx.resolutions,
			self.cx.strings,
			self.cx.defs,
		)
		.walk_path(
			self.scope.file_id,
			self.scope.namespace,
			segments,
			Tier::Value,
		);
		let Some(key) = walk.target.def_key() else {
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		let kind = key.symbol_kind(self.cx.defs);
		let (DefKind::Struct(struct_index), true) =
			(kind, walk.is_complete(segments))
		else {
			if let BindingTarget::Inaccessible(_) = walk.target {
				let segment = &segments[walk.stopped_at as usize];
				self.cx.diagnostics.push(report_private_identifier(
					&self.cx.defs.namespaces,
					self.cx.strings,
					segment.ident.inner,
					SourceSpan::new(self.scope.file_id, segment.ident.span),
					Some(key),
				));
			}
			todo!("checking a call of a `{}`", kind.noun());
		};
		let segment = segments.last().unwrap();
		if let BindingTarget::Inaccessible(key) = walk.target {
			let diagnostic =
				self.report_private_constructor(struct_index, key, segment);
			self.cx.diagnostics.push(diagnostic);
		}
		// The struct's type arguments are learned within this call: from what
		// is written on its name, the expected type, and then the fields.
		let mut type_args =
			self.struct_type_args(struct_index, segment, expected);
		let given = match arguments {
			Arguments::Positional(arguments) => self.positional_fields(
				struct_index,
				&mut type_args,
				arguments,
				span,
			),
			Arguments::Named(arguments) => {
				self.named_fields(struct_index, &mut type_args, arguments, span)
			}
		};
		self.report_uninferred(struct_index, segment, expected, &mut type_args);
		// Every argument is known now, so each value is held to its field's
		// final type: an untyped literal takes it only here.
		for &(field, value) in &given {
			let field_ty = self.field_type(struct_index, &type_args, field);
			self.expect(value, field_ty);
		}
		self.check_struct_bounds(struct_index, segment, &type_args, &given);
		let order = match arguments {
			Arguments::Positional(_) => ArgOrder::InOrder,
			Arguments::Named(_) => self.body.push_permutation(
				given.iter().map(|&(field, _)| ParamIdx::new(field as u32)),
			),
		};
		let args = self.body.push_args(given.iter().map(|&(_, value)| value));
		let ty = self.cx.types.intern_struct(struct_index, &type_args);
		let ty = self.cx.types.collapse_error(ty);
		self.body.push(
			ExprKind::StructConstructor {
				struct_index,
				args,
				order,
			},
			ty,
			span,
		)
	}

	/// What a constructed struct's type arguments are known to be before its
	/// fields are: the ones written on its name (`Wrapper<u32>(..)`, a `_`
	/// anywhere in one unknown), met with the expected type's when that is this
	/// struct. `INFER` per parameter when none are written; `ERROR` per
	/// parameter when the written count is wrong.
	fn struct_type_args(
		&mut self,
		struct_index: StructIdx,
		segment: &ast::PathSegment,
		expected: TypeIndex,
	) -> Box<[TypeIndex]> {
		let params_env = self.cx.structs[usize::from(struct_index)].type_params;
		let count = self.cx.type_envs.param_names(params_env).len();
		let mut type_args = if segment.type_args.is_empty() {
			vec![TypeIndex::INFER; count].into_boxed_slice()
		} else {
			let mut obligations = Vec::new();
			let mut written = Vec::with_capacity(segment.type_args.len());
			for arg in &segment.type_args {
				written.push(self.cx.resolve_type(
					&mut obligations,
					self.scope,
					arg,
					InferPolicy::Allow,
				));
			}
			self.cx.check_now(&obligations);
			if !self.cx.check_type_arg_count(
				self.scope,
				segment,
				params_env,
				TypeEnvOwner::Struct(struct_index),
			) {
				return vec![TypeIndex::ERROR; count].into_boxed_slice();
			}
			written.into_boxed_slice()
		};
		if expected == TypeIndex::INFER {
			return type_args;
		}
		// A disagreement teaches nothing: the construction's own type is held
		// to the expected one where the call is checked.
		let expected = self.normalized(expected, self.scope.env);
		if let Type::Struct {
			struct_index: hinted,
			type_args: hints,
		} = *self.cx.types.resolve(expected)
			&& hinted == struct_index
		{
			for at in 0..count {
				let hint = self.cx.types.list(hints)[at];
				if let Some(met) = self.cx.types.meet(type_args[at], hint) {
					type_args[at] = met;
				}
			}
		}
		type_args
	}

	/// Records and checks the bounds of the struct's parameters for its final
	/// type arguments, at the call, wherever they were learned from. Each is
	/// reported at its written argument, else at the value of a field whose
	/// declared type is that parameter, else at the struct's name.
	fn check_struct_bounds(
		&mut self,
		struct_index: StructIdx,
		segment: &ast::PathSegment,
		type_args: &[TypeIndex],
		given: &[(usize, ExprIdx)],
	) {
		if type_args.is_empty() {
			return;
		}
		let params_env = self.cx.structs[usize::from(struct_index)].type_params;
		let arguments = self.cx.types.push_list(type_args);
		let mut obligations = Vec::new();
		for (index, &argument) in type_args.iter().enumerate() {
			let span = match segment.type_args.get(index) {
				Some(written) => written.span,
				None => {
					let param =
						self.cx.type_envs.param_types(params_env)[index];
					let mut span = segment.ident.span;
					for &(field, value) in given {
						if self.cx.struct_field_types(struct_index)[field]
							== param
						{
							span = self.body.span(value);
							break;
						}
					}
					span
				}
			};
			self.cx.record_bounds_check(
				&mut obligations,
				self.scope.env,
				BoundRequirements::Parameter {
					env: params_env,
					index,
					arguments,
				},
				Spanned {
					inner: argument,
					span,
				},
				SourceSpan::new(self.scope.file_id, span),
				TypeEnvOwner::Struct(struct_index),
			);
		}
		self.cx.check_now(&obligations);
	}

	/// Reports each parameter whose argument is still not fully known (an
	/// `INFER` anywhere in it), and makes it `ERROR`.
	/// Nothing is reported against an `ERROR` expectation: whoever made it
	/// has said why.
	fn report_uninferred(
		&mut self,
		struct_index: StructIdx,
		segment: &ast::PathSegment,
		expected: TypeIndex,
		args: &mut [TypeIndex],
	) {
		let params_env = self.cx.structs[usize::from(struct_index)].type_params;
		for at in 0..args.len() {
			if !self.cx.types.has_infer(args[at]) {
				continue;
			}
			args[at] = TypeIndex::ERROR;
			if expected == TypeIndex::ERROR {
				continue;
			}
			let name = self.cx.type_envs.param_names(params_env)[at].inner;
			let name = self.cx.strings.resolve(name).unwrap();
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeAnnotationRequired.code())
					.with_message(format!(
						"cannot infer type for type parameter `{name}`"
					))
					.with_label(
						Label::primary(self.scope.file_id, segment.ident.span)
							.with_message("type annotation required"),
					),
			);
		}
	}

	/// What `value`, given for `field`, teaches the struct's type arguments:
	/// the parts of its type standing where the field's declared type names a
	/// parameter.
	fn learn_field(
		&mut self,
		struct_index: StructIdx,
		type_args: &mut [TypeIndex],
		field: usize,
		value: ExprIdx,
	) {
		let declared = self.cx.struct_field_types(struct_index)[field];
		let env = self.cx.structs[usize::from(struct_index)].type_params;
		let actual = self.body.ty(value);
		self.cx.types.learn(
			&self.cx.type_envs,
			env,
			type_args,
			declared,
			actual,
		);
	}

	/// A field's type, as expected of the value given for it: as declared,
	/// with the struct's type arguments `args` for its parameters. An argument
	/// not known yet leaves its parts `INFER`, which expect nothing.
	fn field_type(
		&mut self,
		struct_index: StructIdx,
		args: &[TypeIndex],
		field: usize,
	) -> TypeIndex {
		let ty = self.cx.struct_field_types(struct_index)[field];
		let ty = self.cx.types.substitute(
			ty,
			Substitution {
				envs: &self.cx.type_envs,
				env: self.cx.structs[usize::from(struct_index)].type_params,
				args,
			},
		);
		self.normalized(ty, self.scope.env)
	}

	/// The fields of `Point(1, 2)`: the n-th argument gives the n-th field.
	/// Each value is built with its field's type as known so far, and teaches
	/// `type_args` what it can; it is held to the field's final type by the
	/// caller. An argument past the last field is built and dropped.
	fn positional_fields(
		&mut self,
		struct_index: StructIdx,
		type_args: &mut [TypeIndex],
		arguments: &[ast::Separated<Spanned<ast::Expression>>],
		span: TextSpan,
	) -> Vec<(usize, ExprIdx)> {
		let count = self.cx.struct_field_types(struct_index).len();
		if arguments.len() != count {
			let plural = |n: usize| if n == 1 { "" } else { "s" };
			let label =
				Label::primary(self.scope.file_id, span).with_message(format!(
					"expected {count} field{}, found {}",
					plural(count),
					arguments.len()
				));
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::ArgumentCountMismatch.code())
					.with_message(format!(
						"this struct takes {count} field{} but {} {} supplied",
						plural(count),
						arguments.len(),
						if arguments.len() == 1 { "was" } else { "were" }
					))
					.with_label(label),
			);
		}
		let mut given = Vec::with_capacity(count);
		for (at, argument) in arguments.iter().enumerate() {
			if at >= count {
				self.build(&argument.inner, TypeIndex::INFER);
				continue;
			}
			let hint = self.field_type(struct_index, type_args, at);
			let value = self.build(&argument.inner, hint);
			self.learn_field(struct_index, type_args, at, value);
			given.push((at, value));
		}
		given
	}

	/// The fields of `Point({ y: 2, x })`, in written order, each with the
	/// field it gives, built and learned from as `positional_fields` does. Only
	/// a struct whose every field is named is built this way. An argument
	/// naming no field, or a field already given, is built and dropped.
	fn named_fields(
		&mut self,
		struct_index: StructIdx,
		type_args: &mut [TypeIndex],
		arguments: &[ast::Separated<Spanned<ast::NamedArgument>>],
		span: TextSpan,
	) -> Vec<(usize, ExprIdx)> {
		let def = &self.cx.defs.structs[usize::from(struct_index)];
		let struct_name = self.cx.strings.resolve(def.name.inner).unwrap();
		let count = def.fields.len();
		if !def.is_fully_named() {
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TupleStructBraceLiteral.code())
					.with_message(format!(
						"struct `{struct_name}` has unnamed fields, so it is \
						 constructed with `{struct_name}(...)`"
					))
					.with_label(Label::primary(self.scope.file_id, span)),
			);
			return Vec::new();
		}
		// Each field given, with its name as written and its value.
		let mut given: Vec<(FieldIdx, TextSpan, ExprIdx)> =
			Vec::with_capacity(arguments.len());
		for argument in arguments {
			let argument = &argument.inner.inner;
			let name = argument.name;
			let field = self.cx.defs.structs[usize::from(struct_index)]
				.lookup
				.get(&name.inner)
				.copied();
			let hint = match field {
				Some(field) => {
					self.field_type(struct_index, type_args, usize::from(field))
				}
				None => TypeIndex::INFER,
			};
			let value = match &argument.value {
				Some(value) => self.build(value, hint),
				// `{ x }` is `{ x: x }`.
				None => {
					let path = [ast::PathSegment {
						ident: name,
						type_args: Box::new([]),
					}];
					self.build_path(&path, name.span)
				}
			};
			let def = &self.cx.defs.structs[usize::from(struct_index)];
			let struct_name = self.cx.strings.resolve(def.name.inner).unwrap();
			let field_name = self.cx.strings.resolve(name.inner).unwrap();
			let Some(field) = field else {
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::UnknownStructField.code())
						.with_message(format!(
							"no such field `{field_name}` in struct \
							 `{struct_name}`"
						))
						.with_label(
							SourceSpan::new(self.scope.file_id, name.span)
								.primary_label(),
						),
				);
				continue;
			};
			if let Some(&(_, first, _)) =
				given.iter().find(|&&(given, ..)| given == field)
			{
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::DuplicateStructFieldInit.code(),
						)
						.with_message(format!(
							"field `{field_name}` specified more than once"
						))
						.with_label(Label::primary(
							self.scope.file_id,
							name.span,
						))
						.with_label(
							Label::secondary(self.scope.file_id, first)
								.with_message("first use of this field"),
						),
				);
				continue;
			}
			self.learn_field(
				struct_index,
				type_args,
				usize::from(field),
				value,
			);
			given.push((field, name.span, value));
		}
		// A later field of a name declared twice is one no argument can name;
		// the duplicate was reported on the struct.
		let def = &self.cx.defs.structs[usize::from(struct_index)];
		let missing: Vec<String> = (0..count)
			.map(|at| FieldIdx::new(at as u32))
			.filter(|&field| {
				let name = def.fields[usize::from(field)].name.unwrap().inner;
				!given.iter().any(|&(given, ..)| given == field)
					&& def.lookup.get(&name) == Some(&field)
			})
			.map(|field| {
				let name = def.fields[usize::from(field)].name.unwrap().inner;
				format!("`{}`", self.cx.strings.resolve(name).unwrap())
			})
			.collect();
		if !missing.is_empty() {
			let struct_name = self.cx.strings.resolve(def.name.inner).unwrap();
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::MissingStructFields.code())
					.with_message(format!(
						"missing field{} {} in construction of `{struct_name}`",
						if missing.len() == 1 { "" } else { "s" },
						missing.join(", ")
					))
					.with_label(Label::primary(self.scope.file_id, span)),
			);
		}
		given
			.into_iter()
			.map(|(field, _, value)| (usize::from(field), value))
			.collect()
	}

	/// A struct's constructor is as visible as the struct and every one of
	/// its fields. When the struct is visible, the private fields are why its
	/// constructor is not, and the report says so.
	fn report_private_constructor(
		&self,
		struct_index: StructIdx,
		key: DefKey,
		segment: &ast::PathSegment,
	) -> Diagnostic<FileId> {
		let def = &self.cx.defs.structs[usize::from(struct_index)];
		let strings = self.cx.strings;
		let name = strings.resolve(def.name.inner).unwrap();
		let private: Vec<String> = def
			.fields
			.iter()
			.enumerate()
			.filter(|(_, field)| field.pub_span.is_none())
			.map(|(at, field)| match field.name {
				Some(name) => {
					format!("`{}`", strings.resolve(name.inner).unwrap())
				}
				None => format!("field {at}"),
			})
			.collect();
		let site = SourceSpan::new(self.scope.file_id, segment.ident.span);
		if private.is_empty() {
			return report_private_identifier(
				&self.cx.defs.namespaces,
				strings,
				segment.ident.inner,
				site,
				Some(key),
			);
		}
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::PrivateItem.code())
			.with_message(format!(
				"the constructor of struct `{name}` is private"
			))
			.with_label(
				site.primary_label().with_message("private constructor"),
			);
		for field in def.fields.iter().filter(|field| field.pub_span.is_none())
		{
			if let Some(field_name) = field.name {
				diagnostic = diagnostic.with_label(
					SourceSpan::new(def.file_id, field_name.span)
						.secondary_label()
						.with_message("private field"),
				);
			}
		}
		let fields = private.join(", ");
		diagnostic
			.with_note(format!(
				"a constructor is private if any field is: {fields} of `{name}` \
				 {} private",
				if private.len() == 1 { "is" } else { "are" }
			))
			.with_note(format!(
				"make every field of `{name}` `pub`, or expose a `pub func` that \
				 constructs it"
			))
	}

	fn build_unary(
		&mut self,
		op: Spanned<UnaryOp>,
		operand: &Spanned<ast::Expression>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		// Every unary operator's method returns `Self`: the operand is expected
		// to have the result's type, and an untyped operand leaves the node
		// untyped until context coerces both.
		let operand = self.build(operand, expected);
		let ty = self.body.ty(operand);
		if ty.is_untyped() {
			return self.body.push(
				ExprKind::Unary {
					op: op.inner,
					operand,
				},
				ty,
				span,
			);
		}
		let (kind, ty) = self.select_unary(op, operand);
		self.body.push(kind, ty, span)
	}

	fn build_binary(
		&mut self,
		op: Spanned<BinaryOp>,
		left: &Spanned<ast::Expression>,
		right: &Spanned<ast::Expression>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		match op.inner {
			BinaryOp::And | BinaryOp::Or => {
				let lhs = self.check(left, TypeIndex::BOOL);
				let rhs = self.check(right, TypeIndex::BOOL);
				return self.body.push(
					ExprKind::Binary {
						op: op.inner,
						lhs,
						rhs,
					},
					TypeIndex::BOOL,
					span,
				);
			}
			BinaryOp::Assign
			| BinaryOp::AddAssign
			| BinaryOp::SubAssign
			| BinaryOp::MulAssign
			| BinaryOp::DivAssign
			| BinaryOp::RemAssign
			| BinaryOp::BitAndAssign
			| BinaryOp::BitOrAssign
			| BinaryOp::BitXorAssign
			| BinaryOp::LeftShiftAssign
			| BinaryOp::RightShiftAssign => {
				todo!("checking an assignment");
			}
			_ => {}
		}
		// An arithmetic or bitwise method returns `Self`, so its operands are
		// expected to have the result's type; a comparison returns `bool`
		// whatever they are.
		let expected = if is_comparison(op.inner) {
			TypeIndex::INFER
		} else {
			expected
		};
		// Both operands share one type (every operator trait takes
		// `rhs: Self`): a typed left side is what the right one is expected to
		// be, and below, a typed side gives its type to an untyped one.
		let lhs = self.build(left, expected);
		let left_ty = self.body.ty(lhs);
		let rhs = if self.cx.types.has_untyped(left_ty) {
			self.build(right, expected)
		} else {
			self.build(right, left_ty)
		};
		let right_ty = self.body.ty(rhs);
		let operand_ty = match (
			self.cx.types.has_untyped(left_ty),
			self.cx.types.has_untyped(right_ty),
		) {
			(true, true) => {
				if is_comparison(op.inner) {
					self.cx.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::ComparisonTypeAnnotationRequired
									.code(),
							)
							.with_message(
								"type annotation required to compare untyped literals",
							)
							.with_label(Label::primary(self.scope.file_id, span)),
					);
					return self.body.push(
						ExprKind::Error,
						TypeIndex::ERROR,
						span,
					);
				}
				// Two literals are a float if either is; anything else untyped
				// (a tuple of literals) keeps the left side's shape.
				let ty = if !left_ty.is_untyped() || !right_ty.is_untyped() {
					left_ty
				} else if left_ty == TypeIndex::FLOAT
					|| right_ty == TypeIndex::FLOAT
				{
					TypeIndex::FLOAT
				} else {
					TypeIndex::INTEGER
				};
				return self.body.push(
					ExprKind::Binary {
						op: op.inner,
						lhs,
						rhs,
					},
					ty,
					span,
				);
			}
			(true, false) => {
				self.coerce(lhs, right_ty);
				right_ty
			}
			(false, true) => {
				self.coerce(rhs, left_ty);
				left_ty
			}
			(false, false) => {
				if left_ty != right_ty
					&& left_ty != TypeIndex::ERROR
					&& right_ty != TypeIndex::ERROR
				{
					let diagnostic =
						self.report_type_mismatch(left_ty, right_ty, rhs);
					self.cx.diagnostics.push(diagnostic);
					return self.body.push(
						ExprKind::Error,
						TypeIndex::ERROR,
						span,
					);
				}
				left_ty
			}
		};
		let (kind, ty) = self.select_binary(op, lhs, rhs, operand_ty);
		self.body.push(kind, ty, span)
	}

	/// The node for a unary operator on an operand of concrete type, and its
	/// type. Pushes nothing but call arguments, so a caller can rewrite a node
	/// in place with it.
	fn select_unary(
		&mut self,
		op: Spanned<UnaryOp>,
		operand: ExprIdx,
	) -> (ExprKind, TypeIndex) {
		let ty = self.body.ty(operand);
		let Some(lookup) = self.operator_impl(
			ty,
			self.cx.operators.unary(op.inner),
			operand,
			op.span,
			op.inner.as_str(),
			DiagnosticCode::UnaryOperatorCannotBeApplied,
		) else {
			return (ExprKind::Error, TypeIndex::ERROR);
		};
		if Scalar::from_type(ty)
			.is_some_and(|scalar| is_builtin_unary(op.inner, scalar))
		{
			let kind = ExprKind::Unary {
				op: op.inner,
				operand,
			};
			return (kind, ty);
		}
		(self.method_call(lookup, [operand]), ty)
	}

	/// The node for a binary operator on operands of concrete type `ty`, and
	/// its type. See `select_unary`.
	fn select_binary(
		&mut self,
		op: Spanned<BinaryOp>,
		lhs: ExprIdx,
		rhs: ExprIdx,
		ty: TypeIndex,
	) -> (ExprKind, TypeIndex) {
		let Some(lookup) = self.operator_impl(
			ty,
			self.cx.operators.binary(op.inner),
			lhs,
			op.span,
			op.inner.as_str(),
			DiagnosticCode::BinaryOperatorCannotBeApplied,
		) else {
			return (ExprKind::Error, TypeIndex::ERROR);
		};
		let result = if is_comparison(op.inner) {
			TypeIndex::BOOL
		} else {
			ty
		};
		if Scalar::from_type(ty)
			.is_some_and(|scalar| is_builtin_binary(op.inner, scalar))
		{
			let kind = ExprKind::Binary {
				op: op.inner,
				lhs,
				rhs,
			};
			return (kind, result);
		}
		(self.method_call(lookup, [lhs, rhs]), result)
	}

	/// Whether `ty` implements the operator's trait, and through what. `None`
	/// when it does not (reported here) or `ty` is already an error.
	fn operator_impl(
		&mut self,
		ty: TypeIndex,
		method: Option<OperatorMethod>,
		operand: ExprIdx,
		op_span: TextSpan,
		op_text: &str,
		code: DiagnosticCode,
	) -> Option<(OperatorMethod, TraitImplLookup)> {
		if ty == TypeIndex::ERROR {
			return None;
		}
		let found = match method {
			Some(method) => {
				match self.cx.find_trait_impl_query(
					self.scope.env,
					ty,
					method.trait_index,
				) {
					Ok(found) => found.map(|lookup| (method, lookup)),
					Err(error) => {
						let _ = self.cx.report_solver_error::<()>(
							Err(error),
							SourceSpan::new(self.scope.file_id, op_span),
						);
						return None;
					}
				}
			}
			None => None,
		};
		if found.is_none() {
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(code.code())
					.with_message(format!(
						"operator `{op_text}` cannot be applied to type `{}`",
						self.cx.type_formatter().display_type(ty)
					))
					.with_label(self.source_span(operand).primary_label())
					.with_label(Label::secondary(self.scope.file_id, op_span)),
			);
		}
		found
	}

	/// A call to the operator's method: the selected impl's own, or the trait's
	/// declaration when the receiver is abstract or the impl inherits a default.
	fn method_call<const N: usize>(
		&mut self,
		(method, lookup): (super::operators::OperatorMethod, TraitImplLookup),
		args: [ExprIdx; N],
	) -> ExprKind {
		let args = self.body.push_args(args);
		let TraitImplLookup::Concrete { impl_index, .. } = lookup else {
			return ExprKind::GenericMethodCall {
				method: method.method,
				args,
			};
		};
		match self
			.cx
			.defs
			.select_trait_member(impl_index, MemberKind::Method(method.method))
		{
			TraitMemberSelection::Impl(
				MemberKind::Method(selected) | MemberKind::Function(selected),
			) => ExprKind::MethodCall {
				method: selected,
				args,
			},
			TraitMemberSelection::Impl(_)
			| TraitMemberSelection::TraitDeclaration(_) => ExprKind::GenericMethodCall {
				method: method.method,
				args,
			},
		}
	}

	/// What a type means in `scope`: comparisons and literal coercion work on
	/// normalized types. A projection that does not normalize stays as written;
	/// whoever wrote it has reported why.
	fn normalized(&mut self, ty: TypeIndex, scope: TypeEnvIdx) -> TypeIndex {
		match self.cx.normalize_type_query(scope, ty) {
			Ok(normalized) => normalized,
			Err(_) => ty,
		}
	}

	/// Every member of every typeset an abstract `target` assumes, any of
	/// which can be substituted for it. Empty when no literal can have type
	/// `target`.
	fn typeset_targets(&self, target: TypeIndex) -> Vec<LiteralTarget> {
		// An abstract target is constrained by its own bounds alone, so read
		// the typesets those name rather than probing every typeset.
		let mut targets = Vec::new();
		for trait_index in self.cx.clause_tables().declared_traits(
			&self.cx.types,
			target,
			self.cx.solver.state.recursion_budget,
		) {
			let Some(typeset) =
				self.cx.defs.traits[usize::from(trait_index)].typeset
			else {
				continue;
			};
			for member in self.cx.typeset_members(typeset).iter().copied() {
				targets.push(LiteralTarget::TypesetMember(typeset, member));
			}
		}
		targets
	}

	/// Gives an untyped subtree the type `target`, checking each literal fits.
	/// Reports and leaves the offending node at `ERROR` when one does not.
	fn coerce(&mut self, expr: ExprIdx, target: TypeIndex) {
		if target == TypeIndex::ERROR {
			self.body.set_ty(expr, TypeIndex::ERROR);
			return;
		}
		if let ExprKind::Tuple { elements } = self.body.kind(expr) {
			return self.coerce_tuple(expr, elements, target);
		}
		// The common case: one concrete number, held on the stack.
		if Integer::from_type(target).is_some()
			|| Float::from_type(target).is_some()
		{
			let single = [LiteralTarget::Target(target)];
			return self.coerce_against(expr, target, &single);
		}
		let targets = self.typeset_targets(target);
		if targets.is_empty() {
			self.cx
				.diagnostics
				.push(self.report_unable_to_coerce(expr, target));
			return self.body.set_ty(expr, TypeIndex::ERROR);
		}
		self.coerce_against(expr, target, &targets);
	}

	/// `coerce` against the scalars a literal must fit: `target`'s own, or
	/// every member of every typeset it assumes.
	fn coerce_against(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		targets: &[LiteralTarget],
	) {
		match self.body.kind(expr) {
			ExprKind::Int(value) => {
				self.coerce_int(expr, expr, target, targets, value, false);
			}
			ExprKind::Float(_) => self.coerce_float(expr, target, targets),
			ExprKind::Unary { op, operand } => {
				for fit in targets {
					if !fit.fits_unary(op) {
						return self.report_misfit(expr, target, fit);
					}
				}
				let coerced = match (op, self.body.kind(operand)) {
					// `-128` is in range for `i8` though `128` is not: a
					// negated literal is checked against the negative bound.
					(UnaryOp::InvertSign, ExprKind::Int(value)) => self
						.coerce_int(
							expr, operand, target, targets, value, true,
						),
					_ => {
						self.coerce(operand, target);
						true
					}
				};
				if coerced {
					self.body.set_ty(expr, target);
				}
			}
			ExprKind::Binary { op, lhs, rhs } => {
				debug_assert!(
					!is_comparison(op),
					"a comparison is never untyped"
				);
				self.coerce(lhs, target);
				self.coerce(rhs, target);
				// The operator could not be checked while its operands had no
				// type; it is now, and the node is rewritten in place.
				let op = Spanned {
					inner: op,
					span: self.body.span(expr),
				};
				let (kind, ty) = self.select_binary(op, lhs, rhs, target);
				self.body.set_kind(expr, kind);
				self.body.set_ty(expr, ty);
			}
			kind => unreachable!(
				"only literals and operators over them are untyped: {kind:?}"
			),
		}
	}

	/// Checks an integer literal (`value`, optionally negated) against every
	/// candidate, then gives `literal` the type `target` and returns `true`.
	/// On a misfit it draws the report, leaves the node at `ERROR`, and
	/// returns `false`. `report` is the node a diagnostic points at — the
	/// unary itself, for a negated literal.
	fn coerce_int(
		&mut self,
		report: ExprIdx,
		literal: ExprIdx,
		target: TypeIndex,
		targets: &[LiteralTarget],
		value: u64,
		negated: bool,
	) -> bool {
		let mut all_float = true;
		for fit in targets {
			if !fit.fits_int(value, negated) {
				self.report_int_misfit(report, value, negated, target, fit);
				return false;
			}
			all_float &= fit.is_float();
		}
		// An integer literal of float type is a float.
		if all_float {
			self.body.set_kind(literal, ExprKind::Float(value as f64));
		}
		self.body.set_ty(literal, target);
		true
	}

	/// Gives an untyped tuple the type `target`: each element is held to the
	/// target's element at its position, which coerces the untyped ones. A
	/// target that is not a tuple as long is a mismatch.
	fn coerce_tuple(
		&mut self,
		expr: ExprIdx,
		elements: ExprRange,
		target: TypeIndex,
	) {
		let targets = match *self.cx.types.resolve(target) {
			Type::Tuple { elements: targets }
				if targets.len() == elements.len() =>
			{
				targets
			}
			_ => {
				let actual = self.body.ty(expr);
				let diagnostic =
					self.report_type_mismatch(target, actual, expr);
				self.cx.diagnostics.push(diagnostic);
				return self.body.set_ty(expr, TypeIndex::ERROR);
			}
		};
		let mut types = Vec::with_capacity(elements.len());
		for at in 0..elements.len() {
			let element = self.body.args(elements)[at];
			let element_target = self.cx.types.list(targets)[at];
			let element = self.expect(element, element_target);
			types.push(self.body.ty(element));
		}
		let ty = self.cx.types.intern_tuple(&types);
		let ty = self.cx.types.collapse_error(ty);
		self.body.set_ty(expr, ty);
	}

	/// Reads a float literal's value from its text at each target's width.
	fn coerce_float(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		targets: &[LiteralTarget],
	) {
		let source = &self.cx.files.get(self.scope.file_id).unwrap().source;
		let text = self.body.span(expr).extract_str(source).to_owned();
		let mut value = None;
		for fit in targets {
			match fit.fits_float(&text) {
				FloatFit::Fits(parsed) => {
					value.get_or_insert(parsed);
				}
				// Malformed syntax was reported by the parser.
				FloatFit::Invalid => {
					return self.body.set_ty(expr, TypeIndex::ERROR);
				}
				FloatFit::Overflow => {
					return self.report_float(expr, fit, true);
				}
				FloatFit::Underflow => {
					return self.report_float(expr, fit, false);
				}
				FloatFit::NotFloat => {
					return self.report_misfit(expr, target, fit);
				}
			}
		}
		self.body.set_kind(expr, ExprKind::Float(value.unwrap()));
		self.body.set_ty(expr, target);
	}

	/// A float literal `fit` cannot hold: too large or too small for its width.
	fn report_float(
		&mut self,
		expr: ExprIdx,
		fit: &LiteralTarget,
		overflow: bool,
	) {
		let name = self.cx.type_formatter().display_type(fit.ty());
		let (code, message) = if overflow {
			(
				DiagnosticCode::FloatLiteralOverflow,
				format!("float literal is too large for `{name}`"),
			)
		} else {
			(
				DiagnosticCode::FloatLiteralUnderflow,
				format!("float literal is too small to represent in `{name}`"),
			)
		};
		self.push_error(code, message, expr);
	}

	/// An integer literal that does not fit `fit`: out of range for a plain
	/// integer target, not representable for a float one.
	fn report_int_misfit(
		&mut self,
		expr: ExprIdx,
		value: u64,
		negated: bool,
		target: TypeIndex,
		fit: &LiteralTarget,
	) {
		let LiteralTarget::Target(ty) = fit else {
			return self.report_misfit(expr, target, fit);
		};
		if Integer::from_type(*ty).is_some() {
			let value = if negated {
				-(value as i128)
			} else {
				value as i128
			};
			self.report_out_of_range(expr, value, target);
		} else if Float::from_type(*ty).is_some() {
			let message = format!(
				"integer literal cannot be represented exactly by `{}`",
				self.cx.type_formatter().display_type(target)
			);
			self.push_error(
				DiagnosticCode::IntegerLiteralNotRepresentable,
				message,
				expr,
			);
		} else {
			// A concrete type that is neither integer nor float (bool, char)
			// has no integer proof, just as a typeset member has none.
			self.report_misfit(expr, target, fit);
		}
	}

	/// A literal `fit` cannot hold: unable to coerce to a scalar target, or a
	/// typeset member it does not fit for an abstract one.
	fn report_misfit(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		fit: &LiteralTarget,
	) {
		let LiteralTarget::TypesetMember(typeset, member) = fit else {
			self.cx
				.diagnostics
				.push(self.report_unable_to_coerce(expr, target));
			return self.body.set_ty(expr, TypeIndex::ERROR);
		};
		let def = &self.cx.defs.typesets[usize::from(*typeset)];
		let typeset_name = self
			.cx
			.strings
			.resolve(
				self.cx.defs.traits[usize::from(def.trait_index)].name.inner,
			)
			.unwrap();
		let member_name = self.cx.type_formatter().display_type(member.inner);
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypesetBoundViolation.code())
				.with_message(format!(
					"literal is not representable by every member of typeset `{typeset_name}`"
				))
				.with_label(
					Label::primary(self.scope.file_id, self.body.span(expr))
						.with_message(format!(
							"cannot be represented by `{member_name}`"
						)),
				)
				.with_label(
					SourceSpan::new(def.file_id, member.span)
						.secondary_label()
						.with_message(format!(
							"`{member_name}` is a member here"
						)),
				),
		);
		self.body.set_ty(expr, TypeIndex::ERROR);
	}

	fn report_out_of_range(
		&mut self,
		expr: ExprIdx,
		value: i128,
		ty: TypeIndex,
	) {
		let message = format!(
			"literal `{value}` out of range for `{}`",
			self.cx.type_formatter().display_type(ty)
		);
		self.push_error(
			DiagnosticCode::IntegerLiteralOutOfRange,
			message,
			expr,
		);
	}

	fn report_unable_to_coerce(
		&self,
		expr: ExprIdx,
		target: TypeIndex,
	) -> Diagnostic<FileId> {
		Diagnostic::error()
			.with_code(DiagnosticCode::UnableToCoerce.code())
			.with_message(format!(
				"unable to coerce to type `{}`",
				self.cx.type_formatter().display_type(target)
			))
			.with_label(self.source_span(expr).primary_label())
	}

	/// Reports at `expr` and leaves it at `ERROR`, so nothing reports it again.
	fn push_error(
		&mut self,
		code: DiagnosticCode,
		message: String,
		expr: ExprIdx,
	) {
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(code.code())
				.with_message(message)
				.with_label(self.source_span(expr).primary_label()),
		);
		self.body.set_ty(expr, TypeIndex::ERROR);
	}

	fn report_type_mismatch(
		&self,
		expected: TypeIndex,
		actual: TypeIndex,
		expr: ExprIdx,
	) -> Diagnostic<FileId> {
		let formatter = self.cx.type_formatter();
		Diagnostic::error()
			.with_code(DiagnosticCode::TypeMistmatch.code())
			.with_message("type mismatch")
			.with_label(self.source_span(expr).primary_label().with_message(
				format!(
					"expected `{}`, found `{}`",
					formatter.display_type(expected),
					formatter.display_type(actual)
				),
			))
	}

	fn source_span(&self, expr: ExprIdx) -> SourceSpan {
		SourceSpan::new(self.scope.file_id, self.body.span(expr))
	}
}

/// A call's arguments, by position or by name.
enum Arguments<'e> {
	Positional(&'e [ast::Separated<Spanned<ast::Expression>>]),
	Named(&'e [ast::Separated<Spanned<ast::NamedArgument>>]),
}

/// A type a literal must fit, and where the requirement comes from.
enum LiteralTarget {
	/// The target type itself.
	Target(TypeIndex),
	/// A member of a typeset an abstract target assumes: the typeset, to name
	/// it, and the member's written type, for its place in a diagnostic.
	TypesetMember(TypesetIdx, Spanned<TypeIndex>),
}

impl LiteralTarget {
	/// The candidate type. `Integer::from_type` or `Float::from_type` narrows
	/// it when the check wants one; a typeset member need be neither.
	fn ty(&self) -> TypeIndex {
		match self {
			LiteralTarget::Target(ty) => *ty,
			LiteralTarget::TypesetMember(_, member) => member.inner,
		}
	}

	/// Whether an integer literal (`value`, optionally negated) fits.
	fn fits_int(&self, value: u64, negated: bool) -> bool {
		let ty = self.ty();
		if let Some(integer) = Integer::from_type(ty) {
			integer.in_range(value, negated)
		} else if let Some(float) = Float::from_type(ty) {
			float.exact_precision_int(value)
		} else {
			false
		}
	}

	/// Whether a float literal written `text` fits, and its value when it does.
	fn fits_float(&self, text: &str) -> FloatFit {
		let Some(float) = Float::from_type(self.ty()) else {
			return FloatFit::NotFloat;
		};
		let result = match float {
			Float::F32 => text
				.parse::<f32>()
				// f64::from is a lossless conversion
				.map(f64::from),
			Float::F64 => text.parse::<f64>(),
		};
		match result {
			Ok(parsed) if parsed.is_infinite() => FloatFit::Overflow,
			Ok(parsed)
				if parsed == 0.0
					&& text
						.bytes()
						.any(|b| b.is_ascii_digit() && b != b'0') =>
			{
				FloatFit::Underflow
			}
			Ok(parsed) => FloatFit::Fits(parsed),
			Err(_) => FloatFit::Invalid,
		}
	}

	/// Whether `op` means anything over a literal of this candidate's type.
	fn fits_unary(&self, op: UnaryOp) -> bool {
		let ty = self.ty();
		match op {
			UnaryOp::InvertSign => {
				Integer::from_type(ty).is_some_and(Integer::is_signed)
					|| Float::from_type(ty).is_some()
			}
			UnaryOp::BitNot => Integer::from_type(ty).is_some(),
			UnaryOp::Not => false,
		}
	}

	/// Whether a literal of this candidate's type is a float.
	fn is_float(&self) -> bool {
		Float::from_type(self.ty()).is_some()
	}
}

/// How a float literal fares against one candidate.
enum FloatFit {
	/// It parses and is representable at the candidate's width, at this value.
	Fits(f64),
	/// The text is not a float; the parser has already reported it.
	Invalid,
	/// It parses to infinity at the candidate's width.
	Overflow,
	/// It is nonzero in text but rounds to zero at the candidate's width.
	Underflow,
	/// The candidate is not a float type.
	NotFloat,
}

#[derive(Clone, Copy)]
enum Float {
	F32,
	F64,
}

impl Float {
	fn from_type(ty: TypeIndex) -> Option<Self> {
		Some(match ty {
			TypeIndex::F32 => Self::F32,
			TypeIndex::F64 => Self::F64,
			_ => return None,
		})
	}

	fn mantissa_bits(self) -> u32 {
		match self {
			Self::F32 => 24,
			Self::F64 => 53,
		}
	}

	fn exact_precision_int(self, value: u64) -> bool {
		value == 0
			|| 64 - value.leading_zeros() - value.trailing_zeros()
				<= self.mantissa_bits()
	}
}

#[derive(Clone, Copy)]
enum Integer {
	I8,
	U8,
	I16,
	U16,
	I32,
	U32,
	I64,
	U64,
}

impl Integer {
	fn from_type(ty: TypeIndex) -> Option<Self> {
		Some(match ty {
			TypeIndex::U8 => Self::U8,
			TypeIndex::I8 => Self::I8,
			TypeIndex::U16 => Self::U16,
			TypeIndex::I16 => Self::I16,
			TypeIndex::U32 => Self::U32,
			TypeIndex::I32 => Self::I32,
			TypeIndex::U64 => Self::U64,
			TypeIndex::I64 => Self::I64,
			_ => return None,
		})
	}

	/// Whether an integer literal `value`, optionally negated, is in range.
	fn in_range(self, value: u64, negated: bool) -> bool {
		// A negated literal reaches one past the maximum: `-min`, e.g. `-128`
		// is in range for `i8` although `128` is not.
		let limit = if negated {
			self.min().unsigned_abs()
		} else {
			self.max()
		};
		value <= limit
	}

	fn is_signed(self) -> bool {
		match self {
			Self::I8 | Self::I16 | Self::I32 | Self::I64 => true,
			Self::U8 | Self::U16 | Self::U32 | Self::U64 => false,
		}
	}

	fn max(self) -> u64 {
		match self {
			Self::I8 => i8::MAX as u64,
			Self::U8 => u8::MAX as u64,
			Self::I16 => i16::MAX as u64,
			Self::U16 => u16::MAX as u64,
			Self::I32 => i32::MAX as u64,
			Self::U32 => u32::MAX as u64,
			Self::I64 => i64::MAX as u64,
			Self::U64 => u64::MAX,
		}
	}

	fn min(self) -> i64 {
		match self {
			Self::I8 => i8::MIN as i64,
			Self::U8 => 0,
			Self::I16 => i16::MIN as i64,
			Self::U16 => 0,
			Self::I32 => i32::MIN as i64,
			Self::U32 => 0,
			Self::I64 => i64::MIN,
			Self::U64 => 0,
		}
	}
}
