//! Expression checking: lowers written expressions into a `Body`, with every
//! node typed. One checker for every expression, whatever owns it: a
//! constant's or global's initializer, or a function's block.
//!
//! Blocks, locals and control flow are in `blocks`, patterns in `patterns`,
//! places and assignment in `places`, function calls in `calls`, casts in
//! `casts`. A form the checker does not cover yet
//! is reported once (`UnsupportedExpression`) and checked as an error node.
//!
//! Operators are checked through their trait (`OperatorTraits`): the trait
//! decides whether the operator applies to a type. The node built for it is a
//! `PrimitiveBinary`/`PrimitiveUnary` on a primitive scalar, and a call of the
//! impl's method (`Call`) or the trait's declaration (`AbstractCall`) otherwise.
//!
//! Untyped literals keep the pseudo-types `Integer`/`Float`/`String` until
//! context gives them one (`coerce`), which rewrites the subtree in place. A
//! string literal becomes a shared byte slice or a shared byte array of its
//! length, in the memory its context names.
//!
//! A struct's name is a value only to be called: calling it constructs the
//! struct (`StructConstructor`). It is not a function, and naming it without a call is
//! an error. A generic struct's type arguments are learned within the call,
//! from what is written on its name, the expected type and the fields' values
//! (`TypeInterner::meet`/`learn`); what none of them gives needs an
//! annotation.

mod blocks;
mod calls;
mod casts;
mod members;
mod patterns;
mod places;

use calls::Callee;
use members::MemberPath;

use std::collections::HashMap;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::body::{
	ArgOrder, Body, BodyBuilder, BodyOwner, ExprIdx, ExprKind, ExprRange,
	LocalIdx, ParamIdx, Scope, ScopeIdx, ScopeKind,
};
use super::defs::{
	BindingTarget, ConstIdx, DefKey, DefKind, FieldIdx, FunctionIdx,
	MemberKind, StructIdx, Tier, TypesetIdx, Visibility,
};
use super::imports::report_private_identifier;
use super::literals::{
	CharLiteralError, parse_char_literal, unescape_string_literal,
};
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::obligations::BoundRequirements;
use super::operators::{
	OperatorMethod, is_comparison, is_primitive_binary, is_primitive_unary,
};
use super::paths::{PathResolver, PathWalk};
use super::resolutions::Referent;
use super::signatures::{InferPolicy, LexicalScope, TypeContext};
use super::types::{
	ImplKind, Substitution, Type, TypeEnvIdx, TypeEnvOwner, TypeIndex, TypeList,
};
use crate::ast::{self, BinaryOp, Keyword, Ownership, Spanned, UnaryOp};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::vfs::FileId;

/// Checks the expressions of one definition into a `Body`.
pub(super) struct BodyContext<'a, 'ast, 'ctx, 'dispatch> {
	cx: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
	body: BodyBuilder,
	/// Where the expressions are written. Its type scope is the root for a
	/// free constant, the impl's or trait's `Self` scope for an associated one,
	/// the function's own for a function's block.
	scope: LexicalScope,
	owner: BodyOwner,
	/// The block scope being checked.
	current: ScopeIdx,
	/// The locals each scope declares, by name. A name is looked up in the
	/// current scope, then in each enclosing one; a later declaration of the
	/// same name in one scope replaces the entry, which shadows the earlier.
	lookup: HashMap<(ScopeIdx, SymbolU32), LocalIdx>,
	/// What each scope's value is checked against, index-aligned with the
	/// body's scopes.
	scope_types: Vec<ScopeType>,
}

/// The type a scope's value is held to while its block is checked.
#[derive(Clone, Copy)]
struct ScopeType {
	/// What the context expects of the scope's value; `INFER` for nothing.
	expected: TypeIndex,
	/// The type the first value given to the scope settled on (its result,
	/// a `break`, a `return`); `INFER` until one does.
	ty: TypeIndex,
}

impl<'a, 'ast, 'ctx, 'dispatch> BodyContext<'a, 'ast, 'ctx, 'dispatch> {
	pub(super) fn new(
		cx: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
		scope: LexicalScope,
		owner: BodyOwner,
	) -> Self {
		Self {
			cx,
			body: BodyBuilder::default(),
			scope,
			owner,
			current: ScopeIdx::ROOT,
			lookup: HashMap::new(),
			scope_types: Vec::new(),
		}
	}

	/// Checks `expr` as the whole body, against `expected`.
	pub(super) fn check_body(
		mut self,
		expr: &Spanned<ast::Expression>,
		expected: TypeIndex,
	) -> Body {
		let expected = self.normalized(expected, self.scope.env);
		self.enter_root(expr.span, expected);
		let root = self.check(expr, expected);
		self.body.finish(root)
	}

	/// Pushes the root scope, which every body has.
	fn enter_root(&mut self, span: TextSpan, expected: TypeIndex) {
		let root = self.body.push_scope(Scope {
			kind: ScopeKind::Block,
			parent: None,
			label: None,
			span,
		});
		debug_assert_eq!(root, ScopeIdx::ROOT);
		self.scope_types.push(ScopeType {
			expected,
			ty: TypeIndex::INFER,
		});
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
		self.enter_root(span, repr);
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
	/// type, any other type must equal it, and `!` fits any type, since no
	/// value ever arrives. `INFER` and `ERROR` expect nothing.
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
		} else if actual != TypeIndex::ERROR
			&& actual != TypeIndex::NEVER
			&& actual != expected
		{
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
			ast::Expression::Block { statements } => {
				self.build_block(statements, expected, None, span)
			}
			ast::Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => self.build_if_else(
				condition,
				then_block,
				else_block.as_deref(),
				expected,
				None,
				span,
			),
			ast::Expression::Loop { block } => {
				self.build_loop(block, expected, None, span)
			}
			ast::Expression::Label { label, block } => {
				self.build_labelled(*label, block, expected, span)
			}
			ast::Expression::Break { label, value } => {
				self.build_break(*label, value.as_deref(), span)
			}
			ast::Expression::Continue { label } => {
				self.build_continue(*label, span)
			}
			ast::Expression::Return { value } => {
				self.build_return(value.as_deref(), span)
			}
			ast::Expression::Deref { .. }
			| ast::Expression::ObjectAccess { .. } => self.build_read(expr),
			ast::Expression::AddressOf { value } => {
				self.build_address_of(value, span)
			}
			ast::Expression::Placeholder => {
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::InvalidAssignmentTarget.code(),
						)
						.with_message(
							"`_` can only be used on the left of an assignment",
						)
						.with_label(Label::primary(self.scope.file_id, span)),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
			ast::Expression::Error => {
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
			ast::Expression::Cast { value, ty } => {
				self.build_cast(value, ty, expected, span)
			}
			ast::Expression::MethodCall(call) => {
				self.build_method_call(call, expected, span)
			}
			ast::Expression::NamedMethodCall(_) => {
				self.unsupported(span, "a method call by name")
			}
			ast::Expression::TypeApplication { .. } => {
				self.unsupported(span, "a type application")
			}
			ast::Expression::Match { scrutinee, arms } => {
				self.build_match(scrutinee, arms, expected, span)
			}
			ast::Expression::String => self.build_string(span),
			ast::Expression::QualifiedPath { .. }
			| ast::Expression::Grouped { .. } => match self.resolve_rooted_path(expr) {
				Ok(path) => self.build_member_value(path, span),
				Err(error) => error,
			},
			ast::Expression::ArrayList { .. }
			| ast::Expression::ArrayRepeat { .. } => {
				self.unsupported(span, "an array literal")
			}
			ast::Expression::Index { .. }
			| ast::Expression::SliceRange { .. } => self.unsupported(span, "indexing"),
		}
	}

	/// Reports a form the checker does not cover yet and stands in an error
	/// node for it, so nothing around it reports again. Nothing inside it is
	/// checked.
	fn unsupported(&mut self, span: TextSpan, what: &str) -> ExprIdx {
		self.report_unsupported(span, what);
		self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
	}

	/// Reports that `value`, untyped, needs a type from its context, and
	/// leaves it at `ERROR`.
	fn report_annotation_required(&mut self, value: ExprIdx) {
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypeAnnotationRequired.code())
				.with_message("type annotation required")
				.with_label(
					self.source_span(value)
						.primary_label()
						.with_message("the type of this value is not known"),
				),
		);
		self.body.set_ty(value, TypeIndex::ERROR);
	}

	fn report_unsupported(&mut self, span: TextSpan, what: &str) {
		self.cx.diagnostics.push(
			Diagnostic::bug()
				.with_code(DiagnosticCode::UnsupportedExpression.code())
				.with_message(format!("checking {what} is not supported yet"))
				.with_label(Label::primary(self.scope.file_id, span)),
		);
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

	/// A string literal stays untyped (`Type::String`) until its context
	/// gives it a byte slice or a byte array (`coerce`).
	fn build_string(&mut self, span: TextSpan) -> ExprIdx {
		let source = &self.cx.files.get(self.scope.file_id).unwrap().source;
		match unescape_string_literal(span.extract_str(source)) {
			Ok(contents) => {
				let symbol = self.cx.strings.get_or_intern(contents);
				self.body.push(
					ExprKind::String(symbol),
					TypeIndex::STRING,
					span,
				)
			}
			Err(error) => {
				self.cx.diagnostics.push(
					error.diagnostic(SourceSpan::new(self.scope.file_id, span)),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
		}
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

	/// A value path: a local, or an item in scope. Locals come first, so a
	/// local shadows an item of the same name.
	fn build_path(
		&mut self,
		segments: &[ast::PathSegment],
		span: TextSpan,
	) -> ExprIdx {
		if let [segment] = segments
			&& segment.type_args.is_empty()
			&& let Some(local) = self.lookup_local(segment.ident.inner)
		{
			self.record_local(local, segment.ident.span);
			let ty = self.body.local(local).ty;
			return self.body.push(ExprKind::Local(local), ty, span);
		}
		if let [segment] = segments
			&& segment.ident.inner == Keyword::SelfPascal.symbol()
		{
			if self.impl_self_struct(segment).is_some() {
				self.report_struct_used_as_value(
					Keyword::SelfPascal.symbol(),
					span,
				);
			}
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		}
		let walk = match self.resolve_value_path(segments, span) {
			Ok(ValuePath::Item(walk)) => walk,
			Ok(ValuePath::Member(path)) => {
				return self.build_member_value(path, span);
			}
			Err(error) => return error,
		};
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
		match kind {
			DefKind::Const(const_index) | DefKind::EnumVariant(const_index) => {
				let (ty, scope) = self.cx.constant_type(const_index);
				let ty = self.normalized(ty, scope);
				let kind = ExprKind::Const {
					constant: const_index,
					type_args: TypeList::EMPTY,
				};
				self.body.push(kind, ty, span)
			}
			DefKind::Struct(struct_index) => {
				let name = self.cx.defs.structs[usize::from(struct_index)].name;
				self.report_struct_used_as_value(name.inner, span);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
			DefKind::Function(function_index) => self.build_function_value(
				Callee::free(function_index),
				segments.last().unwrap(),
				span,
			),
			// A global's name is its handle, of its own nominal type: its value
			// is read with `Global::get` and written with `GlobalMut::set`.
			DefKind::Global(global_index) => {
				let ty = self.cx.types.intern(Type::Global { global_index });
				self.body.push(ExprKind::Global(global_index), ty, span)
			}
			_ => {
				self.unsupported(span, &format!("a path to a {}", kind.noun()))
			}
		}
	}

	/// Resolves a value path: an item the namespace walk reaches, or a member
	/// of the type the segments before the last name (`Ordering::of`,
	/// `Self::f`, `T::f`, `W::<u8>::new`). A path starting at a type parameter
	/// or `Self` names a type from its first segment; any other walks the
	/// namespace graph, and continues past a type where the walk stops at one.
	fn resolve_value_path<'s>(
		&mut self,
		segments: &'s [ast::PathSegment],
		span: TextSpan,
	) -> Result<ValuePath<'s>, ExprIdx> {
		let (member, prefix) = segments.split_last().unwrap();
		let first = segments[0].ident.inner;
		if !prefix.is_empty()
			&& (first == Keyword::SelfPascal.symbol()
				|| self.cx.type_envs.resolve(self.scope.env, first).is_some())
		{
			let mut obligations = Vec::new();
			let receiver = self.cx.resolve_type_path(
				&mut obligations,
				self.scope,
				prefix,
				InferPolicy::Allow,
			);
			self.cx.check_now(&obligations);
			return Ok(ValuePath::Member(MemberPath::new(receiver, member)));
		}
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
			return Ok(ValuePath::Item(walk));
		};
		if walk.is_complete(segments) {
			return Ok(ValuePath::Item(walk));
		}
		let stop = walk.stopped_at as usize;
		let stopped = &segments[stop];
		// A generic struct named without its arguments leaves them to the
		// call to learn, as its construction does (`Layout::of::<T>()`).
		if stopped.type_args.is_empty()
			&& let DefKind::Struct(struct_index) = key.symbol_kind(self.cx.defs)
		{
			let params = self.cx.structs[usize::from(struct_index)].type_params;
			let count = self.cx.type_envs.param_names(params).len();
			if count > 0 {
				if stop + 1 != prefix.len() {
					return Err(self.unsupported(
						span,
						"a path past a generic type without its type arguments",
					));
				}
				let receiver = self.cx.types.intern_struct(
					struct_index,
					&vec![TypeIndex::INFER; count],
				);
				return Ok(ValuePath::Member(MemberPath::new(
					receiver, member,
				)));
			}
		}
		let mut obligations = Vec::new();
		let head = self.cx.resolve_named_type(
			&mut obligations,
			self.scope,
			key,
			stopped,
			InferPolicy::Allow,
		);
		let receiver = self.cx.resolve_type_member_path(
			&mut obligations,
			self.scope,
			head,
			&prefix[stop + 1..],
			InferPolicy::Allow,
		);
		self.cx.check_now(&obligations);
		Ok(ValuePath::Member(MemberPath::new(receiver, member)))
	}

	/// The local `name` refers to from the current scope: declared in it or in
	/// a scope around it.
	fn lookup_local(&self, name: SymbolU32) -> Option<LocalIdx> {
		let mut scope = Some(self.current);
		while let Some(at) = scope {
			if let Some(&local) = self.lookup.get(&(at, name)) {
				return Some(local);
			}
			scope = self.body.scope(at).parent;
		}
		None
	}

	fn record_local(&mut self, local: LocalIdx, span: TextSpan) {
		self.cx.resolutions.by_site.insert(
			(SourceSpan::new(self.scope.file_id, span), Tier::Value),
			Referent::Local {
				owner: self.owner,
				local,
			},
		);
	}

	/// A call: of a function named by a path, or the construction of a
	/// struct.
	fn build_call(
		&mut self,
		callee: &Spanned<ast::Expression>,
		arguments: Arguments<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let segments = match &callee.inner {
			ast::Expression::Path(segments) => segments,
			ast::Expression::QualifiedPath { .. }
			| ast::Expression::Grouped { .. } => {
				return match self.resolve_rooted_path(callee) {
					Ok(path) => {
						self.build_member_call(path, arguments, expected, span)
					}
					Err(error) => error,
				};
			}
			_ => {
				return self.unsupported(span, "a call of a computed callee");
			}
		};
		if let [segment] = &**segments
			&& self.lookup_local(segment.ident.inner).is_some()
		{
			return self.unsupported(span, "a call of a local");
		}
		// `Self(..)` constructs the struct the impl around it is for, with
		// that target's arguments.
		if let [segment] = &**segments
			&& segment.ident.inner == Keyword::SelfPascal.symbol()
		{
			let Some((struct_index, type_args)) =
				self.impl_self_struct(segment)
			else {
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			};
			if !self.constructor_accessible(struct_index) {
				let diagnostic = self.report_private_constructor(
					struct_index,
					None,
					segment,
				);
				self.cx.diagnostics.push(diagnostic);
			}
			return self.build_construction(
				struct_index,
				type_args,
				segment,
				arguments,
				expected,
				span,
			);
		}
		let walk = match self.resolve_value_path(segments, span) {
			Ok(ValuePath::Item(walk)) => walk,
			Ok(ValuePath::Member(path)) => {
				return self.build_member_call(path, arguments, expected, span);
			}
			Err(error) => return error,
		};
		let Some(key) = walk.target.def_key() else {
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		let kind = key.symbol_kind(self.cx.defs);
		let DefKind::Struct(struct_index) = kind else {
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
			return match (kind, arguments) {
				(
					DefKind::Function(function_index),
					Arguments::Positional(arguments),
				) => self.build_function_call(
					Callee::free(function_index),
					segments.last().unwrap(),
					None,
					arguments,
					expected,
					span,
				),
				(DefKind::Function(_), Arguments::Named(_)) => {
					self.unsupported(span, "a function call by name")
				}
				_ => self
					.unsupported(span, &format!("a call of a {}", kind.noun())),
			};
		};
		let segment = segments.last().unwrap();
		if let BindingTarget::Inaccessible(key) = walk.target {
			let diagnostic = self.report_private_constructor(
				struct_index,
				Some(key),
				segment,
			);
			self.cx.diagnostics.push(diagnostic);
		}
		// The struct's type arguments are learned within this call: from what
		// is written on its name, the expected type, and then the fields.
		let type_args = self.struct_type_args(struct_index, segment, expected);
		self.build_construction(
			struct_index,
			type_args,
			segment,
			arguments,
			expected,
			span,
		)
	}

	/// The construction of `struct_index` from `arguments`, its type
	/// arguments as known before the fields are (`INFER` where unknown).
	fn build_construction(
		&mut self,
		struct_index: StructIdx,
		mut type_args: Box<[TypeIndex]>,
		segment: &ast::PathSegment,
		arguments: Arguments<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
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
		let params_env = self.cx.structs[usize::from(struct_index)].type_params;
		let poisoned = expected == TypeIndex::ERROR
			|| given.iter().any(|&(_, value)| {
				self.cx.types.has_error(self.body.ty(value))
			});
		self.report_uninferred(
			params_env,
			segment.ident.span,
			poisoned,
			&mut type_args,
		);
		// Every argument is known now, so each value is held to its field's
		// final type: an untyped literal takes it only here.
		for &(field, value) in &given {
			let field_ty = self.field_type(struct_index, &type_args, field);
			self.expect(value, field_ty);
		}
		let declared = self.cx.struct_field_types(struct_index).to_vec();
		self.check_param_bounds(
			params_env,
			TypeEnvOwner::Struct(struct_index),
			segment,
			&declared,
			&type_args,
			&given,
		);
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
		let mut type_args = self.written_type_args(
			segment,
			params_env,
			TypeEnvOwner::Struct(struct_index),
		);
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

	/// The type arguments written on `segment` for the parameters of
	/// `params_env` (`_` anywhere in one is unknown); `INFER` per parameter
	/// when none are written, `ERROR` per parameter when the count is wrong.
	fn written_type_args(
		&mut self,
		segment: &ast::PathSegment,
		params_env: TypeEnvIdx,
		owner: TypeEnvOwner,
	) -> Box<[TypeIndex]> {
		let count = self.cx.type_envs.param_names(params_env).len();
		if segment.type_args.is_empty() {
			return vec![TypeIndex::INFER; count].into_boxed_slice();
		}
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
		if !self
			.cx
			.check_type_arg_count(self.scope, segment, params_env, owner)
		{
			return vec![TypeIndex::ERROR; count].into_boxed_slice();
		}
		written.into_boxed_slice()
	}

	/// Records and checks the bounds of the parameters of `params_env` (a
	/// struct's or a function's own frame) for their final type arguments, at
	/// the call, wherever they were learned from. `type_args` are flat: the
	/// frames around `params_env` first, whose bounds the selection of the
	/// callee proved. Each is reported at its written argument, else at the
	/// value given for a field or parameter whose declared type (`declared`)
	/// is that parameter, else at the name.
	fn check_param_bounds(
		&mut self,
		params_env: TypeEnvIdx,
		owner: TypeEnvOwner,
		segment: &ast::PathSegment,
		declared: &[TypeIndex],
		type_args: &[TypeIndex],
		given: &[(usize, ExprIdx)],
	) {
		let own = self.cx.type_envs.param_names(params_env).len();
		if own == 0 {
			return;
		}
		let arguments = self.cx.types.push_list(type_args);
		let mut obligations = Vec::new();
		let leading = type_args.len() - own;
		for (index, &argument) in type_args[leading..].iter().enumerate() {
			let span = match segment.type_args.get(index) {
				Some(written) => written.span,
				None => {
					let param =
						self.cx.type_envs.param_types(params_env)[index];
					let mut span = segment.ident.span;
					for &(field, value) in given {
						if declared[field] == param {
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
				owner,
			);
		}
		self.cx.check_now(&obligations);
	}

	/// Reports each parameter on `params_env`'s chain whose argument in the
	/// flat `args` is still not fully known (an `INFER` anywhere in it), and
	/// makes it `ERROR`. Nothing is reported in a `poisoned` call (an `ERROR`
	/// expectation, an argument that failed): whatever failed has said why,
	/// and may be why nothing was learned.
	fn report_uninferred(
		&mut self,
		params_env: TypeEnvIdx,
		span: TextSpan,
		poisoned: bool,
		args: &mut [TypeIndex],
	) {
		for at in 0..args.len() {
			if !self.cx.types.has_infer(args[at]) {
				continue;
			}
			args[at] = TypeIndex::ERROR;
			if poisoned {
				continue;
			}
			let frame = self
				.cx
				.type_envs
				.chain(params_env)
				.find(|&frame| self.cx.type_envs.parent_count(frame) <= at)
				.unwrap();
			let index = at - self.cx.type_envs.parent_count(frame);
			let name = self.cx.type_envs.param_names(frame)[index].inner;
			let name = self.cx.strings.resolve(name).unwrap();
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeAnnotationRequired.code())
					.with_message(format!(
						"cannot infer type for type parameter `{name}`"
					))
					.with_label(
						Label::primary(self.scope.file_id, span)
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
		let ty = self.normalized(ty, self.scope.env);
		self.cx.types.collapse_error(ty)
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
	/// The struct `Self` names here, the target of the impl around this
	/// body, with that target's arguments; recorded as what `Self` refers to.
	/// `None` when `Self` names no struct here (reported).
	fn impl_self_struct(
		&mut self,
		segment: &ast::PathSegment,
	) -> Option<(StructIdx, Box<[TypeIndex]>)> {
		let site = SourceSpan::new(self.scope.file_id, segment.ident.span);
		let Some((impl_kind, target)) =
			self.cx.resolve_impl_self(self.scope.env)
		else {
			// A trait's `Self` is the type implementing it, which is not
			// known to be a struct; elsewhere `Self` names nothing.
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::CannotCallExpression.code())
					.with_message("`Self` names no struct here")
					.with_label(site.primary_label())
					.with_note(
						"`Self` is constructed only inside an impl for a struct",
					),
			);
			return None;
		};
		self.cx.resolutions.by_site.insert(
			(site, Tier::Value),
			match impl_kind {
				ImplKind::Inherent(index) => Referent::InherentImplSelf(index),
				ImplKind::Trait(index) => Referent::TraitImplSelf(index),
			},
		);
		if !segment.type_args.is_empty() {
			let diagnostic = self.cx.report_type_args_on_impl_self(
				self.scope.file_id,
				segment,
				impl_kind,
			);
			self.cx.diagnostics.push(diagnostic);
		}
		let Type::Struct {
			struct_index,
			type_args,
		} = *self.cx.types.resolve(target)
		else {
			if target != TypeIndex::ERROR {
				let target = self.cx.type_formatter().display_type(target);
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::CannotCallExpression.code())
						.with_message(format!(
							"`Self` is `{target}`, which is not a struct"
						))
						.with_label(site.primary_label())
						.with_note(
							"only a struct is constructed through `Self`",
						),
				);
			}
			return None;
		};
		Some((struct_index, self.cx.types.list(type_args).into()))
	}

	/// Whether every field of `struct_index` is visible here, which is where
	/// its constructor is.
	fn constructor_accessible(&self, struct_index: StructIdx) -> bool {
		let def = &self.cx.defs.structs[usize::from(struct_index)];
		def.fields.iter().all(|field| {
			self.cx.defs.namespaces.is_accessible_from(
				self.scope.namespace,
				def.namespace.into(),
				Visibility::from(field.pub_span),
			)
		})
	}

	fn report_struct_used_as_value(&mut self, name: SymbolU32, span: TextSpan) {
		let name = self.cx.strings.resolve(name).unwrap();
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
	}

	fn report_private_constructor(
		&self,
		struct_index: StructIdx,
		key: Option<DefKey>,
		segment: &ast::PathSegment,
	) -> Diagnostic<FileId> {
		let def = &self.cx.defs.structs[usize::from(struct_index)];
		let strings = &*self.cx.strings;
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
				key,
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
		if ty == TypeIndex::STRING {
			return self.report_operator_on_string(
				DiagnosticCode::UnaryOperatorCannotBeApplied,
				op.inner.as_str(),
				operand,
				span,
			);
		}
		if ty.is_untyped() {
			return self.body.push(
				ExprKind::PrimitiveUnary {
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
					ExprKind::PrimitiveBinary {
						op: op.inner,
						lhs,
						rhs,
					},
					TypeIndex::BOOL,
					span,
				);
			}
			BinaryOp::Assign => {
				return self.build_assign(left, right, span);
			}
			BinaryOp::AddAssign
			| BinaryOp::SubAssign
			| BinaryOp::MulAssign
			| BinaryOp::DivAssign
			| BinaryOp::RemAssign
			| BinaryOp::BitAndAssign
			| BinaryOp::BitOrAssign
			| BinaryOp::BitXorAssign
			| BinaryOp::LeftShiftAssign
			| BinaryOp::RightShiftAssign => {
				return self.build_compound_assign(op, left, right, span);
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
				// A string literal has no operators of its own; typed, it
				// has its slice's or array's.
				for (ty, operand) in [(left_ty, lhs), (right_ty, rhs)] {
					if ty == TypeIndex::STRING {
						return self.report_operator_on_string(
							DiagnosticCode::BinaryOperatorCannotBeApplied,
							op.inner.as_str(),
							operand,
							span,
						);
					}
				}
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
					ExprKind::PrimitiveBinary {
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
			self.body.span(operand),
			op.span,
			op.inner.as_str(),
			DiagnosticCode::UnaryOperatorCannotBeApplied,
		) else {
			return (ExprKind::Error, TypeIndex::ERROR);
		};
		if is_primitive_unary(op.inner, ty) {
			let kind = ExprKind::PrimitiveUnary {
				op: op.inner,
				operand,
			};
			return (kind, ty);
		}
		(self.method_call(lookup, ty, [operand]), ty)
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
		// Enums and pointers compare natively, by discriminant and address.
		if is_comparison(op.inner)
			&& matches!(
				self.cx.types.resolve(ty),
				Type::Enum { .. } | Type::Pointer { .. }
			) {
			let kind = ExprKind::PrimitiveBinary {
				op: op.inner,
				lhs,
				rhs,
			};
			return (kind, TypeIndex::BOOL);
		}
		let Some(lookup) = self.operator_impl(
			ty,
			self.cx.operators.binary(op.inner),
			self.body.span(lhs),
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
		if is_primitive_binary(op.inner, ty) {
			let kind = ExprKind::PrimitiveBinary {
				op: op.inner,
				lhs,
				rhs,
			};
			return (kind, result);
		}
		(self.method_call(lookup, ty, [lhs, rhs]), result)
	}

	/// Whether `ty` implements the operator's trait, and through what. `None`
	/// when it does not (reported here) or `ty` is already an error.
	fn operator_impl(
		&mut self,
		ty: TypeIndex,
		method: Option<OperatorMethod>,
		operand_span: TextSpan,
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
					.with_label(Label::primary(
						self.scope.file_id,
						operand_span,
					))
					.with_label(Label::secondary(self.scope.file_id, op_span)),
			);
		}
		found
	}

	/// A call of the operator's method on operands of type `ty`: the selected
	/// impl's own, or the trait's declaration when the receiver is abstract
	/// or the impl inherits a default.
	fn method_call<const N: usize>(
		&mut self,
		selected: (OperatorMethod, TraitImplLookup),
		ty: TypeIndex,
		args: [ExprIdx; N],
	) -> ExprKind {
		let args = self.body.push_args(args);
		match self.select_operator_method(selected, ty) {
			SelectedMethod::Concrete {
				function,
				type_args,
			} => ExprKind::Call {
				function,
				type_args,
				args,
			},
			SelectedMethod::Abstract { method, type_args } => {
				ExprKind::AbstractCall {
					method,
					type_args,
					args,
				}
			}
		}
	}

	/// Which method an operator on operands of type `ty` calls, with its type
	/// arguments: the selected impl's own, with the impl's arguments, or the
	/// trait's declaration, with `ty` as `Self`, when the receiver is
	/// abstract or the impl inherits a default.
	fn select_operator_method(
		&mut self,
		(method, lookup): (OperatorMethod, TraitImplLookup),
		ty: TypeIndex,
	) -> SelectedMethod {
		if let TraitImplLookup::Concrete { impl_index, args } = lookup
			&& let TraitMemberSelection::Impl(
				MemberKind::Method(function) | MemberKind::Function(function),
			) = self.cx.defs.select_trait_member(
				impl_index,
				MemberKind::Method(method.method),
			) {
			return SelectedMethod::Concrete {
				function,
				type_args: self.cx.types.push_list(&args),
			};
		}
		SelectedMethod::Abstract {
			method: method.method,
			type_args: self.cx.types.push_list(&[ty]),
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
		match self.body.kind(expr) {
			ExprKind::String(contents) => {
				return self.coerce_string(expr, contents, target);
			}
			ExprKind::Tuple { elements } => {
				return self.coerce_tuple(expr, elements, target);
			}
			// A block is untyped through its result, an `if` through its
			// branches: each untyped one takes the type.
			ExprKind::Block {
				result: Some(result),
				..
			} => {
				self.coerce(result, target);
				return self.body.set_ty(expr, target);
			}
			ExprKind::IfElse {
				then_block,
				else_block: Some(else_block),
				..
			} => {
				for branch in [then_block, else_block] {
					if self.cx.types.has_untyped(self.body.ty(branch)) {
						self.coerce(branch, target);
					}
				}
				return self.body.set_ty(expr, target);
			}
			ExprKind::Match { arms, .. } => {
				let bodies: Vec<ExprIdx> =
					self.body.arms(arms).iter().map(|arm| arm.body).collect();
				for arm in bodies {
					if self.cx.types.has_untyped(self.body.ty(arm)) {
						self.coerce(arm, target);
					}
				}
				return self.body.set_ty(expr, target);
			}
			_ => {}
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
			ExprKind::PrimitiveUnary { op, operand } => {
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
			ExprKind::PrimitiveBinary { op, lhs, rhs } => {
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

	/// A string literal becomes a shared byte slice, `M::&[u8]`, or a shared
	/// byte array of its length, `M::&[u8; N]`, in whatever memory `target`
	/// names. Its data is static and read-only, so an exclusive pointer is
	/// not one it can become.
	fn coerce_string(
		&mut self,
		expr: ExprIdx,
		contents: SymbolU32,
		target: TypeIndex,
	) {
		if self.cx.types.has_infer(target) {
			self.report_annotation_required(expr);
			return self.body.set_ty(expr, TypeIndex::ERROR);
		}
		let fits = match *self.cx.types.resolve(target) {
			Type::Slice {
				of: TypeIndex::U8,
				ownership: Ownership::Shared,
				..
			} => true,
			Type::Array {
				of: TypeIndex::U8,
				ownership: Ownership::Shared,
				size,
				..
			} => {
				let length = self.cx.strings.resolve(contents).unwrap().len();
				if usize::try_from(size).is_ok_and(|size| size == length) {
					true
				} else {
					let target = self.cx.type_formatter().display_type(target);
					return self.push_error(
						DiagnosticCode::ArraySizeMismatch,
						format!(
							"this string literal is {length} bytes long, but \
							 `{target}` holds {size}"
						),
						expr,
					);
				}
			}
			_ => false,
		};
		if fits {
			return self.body.set_ty(expr, target);
		}
		let diagnostic = self
			.report_unable_to_coerce(expr, target)
			.with_note(STRING_TARGETS_NOTE);
		self.cx.diagnostics.push(diagnostic);
		self.body.set_ty(expr, TypeIndex::ERROR);
	}

	/// An operator applied to an untyped string literal.
	fn report_operator_on_string(
		&mut self,
		code: DiagnosticCode,
		op: &str,
		operand: ExprIdx,
		span: TextSpan,
	) -> ExprIdx {
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(code.code())
				.with_message(format!(
					"cannot apply `{op}` to a string literal"
				))
				.with_label(self.source_span(operand).primary_label())
				.with_note(STRING_TARGETS_NOTE),
		);
		self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
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
		self.mismatch_at(expected, actual, self.body.span(expr))
	}

	fn mismatch_at(
		&self,
		expected: TypeIndex,
		actual: TypeIndex,
		span: TextSpan,
	) -> Diagnostic<FileId> {
		let formatter = self.cx.type_formatter();
		Diagnostic::error()
			.with_code(DiagnosticCode::TypeMistmatch.code())
			.with_message("type mismatch")
			.with_label(Label::primary(self.scope.file_id, span).with_message(
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

/// What a string literal can become, for the notes that reject one.
pub(super) const STRING_TARGETS_NOTE: &str = "a string literal is a shared \
	byte slice or byte array in a memory: `heap::&[u8]` or `heap::&[u8; N]`";

/// The method an operator dispatches to, with its type arguments.
#[derive(Clone, Copy)]
enum SelectedMethod {
	/// The selected impl's own method, called directly.
	Concrete {
		function: FunctionIdx,
		type_args: TypeList,
	},
	/// The trait's declaration, whose impl is selected once the receiver is
	/// known.
	Abstract {
		method: FunctionIdx,
		type_args: TypeList,
	},
}

/// What a value path names.
enum ValuePath<'s> {
	/// What the namespace walk reached, all of the path or where it failed.
	Item(PathWalk),
	/// A member of the type the segments before the last name.
	Member(MemberPath<'s>),
}

/// A call's arguments, by position or by name.
#[derive(Clone, Copy)]
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

#[cfg(test)]
mod tests {
	use codespan_reporting::diagnostic::Diagnostic;
	use indoc::indoc;

	use super::super::body::{Body, ExprIdx, ExprKind, PlaceIdx, PlaceKind};
	use super::super::defs::{
		AstEntry, DefKind, DefinitionRegistry, FunctionOwner, Scope, Tier,
	};
	use super::super::eval::{ConstScalar, ConstValueState};
	use super::super::impls::ImplDispatch;
	use super::super::paths::PathResolver;
	use super::super::resolutions::{NameResolutions, Referent};
	use super::super::signatures::TypeContext;
	use super::super::types::{Type, TypeIndex};
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::{DiagnosticCode, TextSpan};
	use crate::testing::DiagnosticView;
	use crate::vfs::{self, FileId, Files};

	const STDLIB: &str = include_str!("../../std/main.wx");

	/// `test_case!(case = "source")` declares the graph, the inputs and the
	/// swept `TestCase` borrowing them as three locals of the calling test.
	/// The test's items are appended to the real stdlib, so operators,
	/// memories and globals are checked against its actual traits.
	macro_rules! test_case {
		($case:ident = $source:expr $(,)?) => {
			let mut graph = source_graph($source);
			let mut inputs = TestInputs::new(&mut graph);
			let $case = TestCase::new(&mut inputs);
		};
	}

	fn source_graph(source: &str) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						format!("{STDLIB}\n{source}"),
					)]),
				),
			)
			.unwrap();
		builder.set_stdlib(root_id);
		builder.build(root_id)
	}

	/// Everything a `TypeContext` borrows, kept on the test's stack.
	struct TestInputs<'g> {
		files: &'g Files,
		strings: &'g mut StringInterner,
		defs: DefinitionRegistry,
		ast_nodes: Vec<AstEntry<'g>>,
		impl_dispatch: ImplDispatch,
		diagnostics: Vec<Diagnostic<FileId>>,
		resolutions: NameResolutions,
	}

	impl<'g> TestInputs<'g> {
		fn new(graph: &'g mut vfs::CompilationUnit) -> Self {
			let vfs::CompilationUnit {
				files,
				packages,
				strings,
				stdlib_package,
				root_package,
			} = graph;
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				packages,
				files,
				strings,
				&mut diagnostics,
				&mut resolutions,
				*stdlib_package,
				*root_package,
			);
			let impl_dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				strings,
				&defs,
				&ast_nodes,
			);
			Self {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			}
		}
	}

	struct TestCase<'a> {
		defs: &'a DefinitionRegistry,
		context: TypeContext<'a, 'a, 'a>,
	}

	impl<'a> TestCase<'a> {
		fn new(inputs: &'a mut TestInputs<'_>) -> Self {
			let TestInputs {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			} = inputs;
			let mut context = TypeContext::new(
				diagnostics,
				resolutions,
				strings,
				files,
				defs,
				ast_nodes,
				impl_dispatch,
			);
			context.sweep();
			// The stdlib's own bodies use forms the checker does not cover
			// yet; those reports are not what this suite is about.
			let stdlib_end = STDLIB.len() as u32;
			context.diagnostics.retain(|diagnostic| {
				let in_stdlib =
					diagnostic.labels.first().is_some_and(|label| {
						(label.range.start as u32) < stdlib_end
					});
				!(in_stdlib
					&& diagnostic.code.as_deref()
						== Some(DiagnosticCode::UnsupportedExpression.code()))
			});
			Self { defs, context }
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"typecheck",
				self.context.diagnostics,
				&self.context.files,
			)
		}

		fn resolve(&self, name: &str) -> DefKind {
			let root = Scope::Package(self.defs.root_package);
			let file_id = self.defs.namespaces.file_id(root.into());
			let segments: Box<[ast::PathSegment]> = name
				.split("::")
				.map(|segment| ast::PathSegment {
					ident: Spanned {
						inner: self.context.strings.get(segment).unwrap(),
						span: TextSpan::new(0, 0),
					},
					type_args: Box::new([]),
				})
				.collect();
			let mut scratch = Vec::new();
			let mut resolutions = NameResolutions::default();
			PathResolver::new(
				&mut scratch,
				&mut resolutions,
				self.context.strings,
				self.defs,
			)
			.resolve_path(file_id, root, &segments, Tier::Value)
			.def_key()
			.unwrap_or_else(|| panic!("expected `{name}` to resolve"))
			.symbol_kind(self.defs)
		}

		/// The checked block of the function `name`.
		fn body(&self, name: &str) -> &Body {
			let DefKind::Function(index) = self.resolve(name) else {
				panic!("expected `{name}` to be a function");
			};
			self.context.function_bodies[usize::from(index)]
				.as_ref()
				.expect("a function with a block has a body")
		}

		/// The rendered block of the member `name`, which only one impl or
		/// trait in the test defines with a block.
		fn member_shape(&self, name: &str) -> String {
			let symbol = self.context.strings.get(name).unwrap();
			let mut found = self.defs.functions.iter().enumerate().filter(
				|&(index, function)| {
					function.name.inner == symbol
						&& !matches!(function.owner, FunctionOwner::Free)
						&& self.context.function_bodies[index].is_some()
				},
			);
			let (index, _) = found.next().unwrap();
			assert!(found.next().is_none(), "`{name}` is declared twice");
			let body = self.context.function_bodies[index].as_ref().unwrap();
			self.render(body, body.root())
		}

		fn display(&self, ty: TypeIndex) -> String {
			self.context.type_formatter().display_type(ty).to_string()
		}

		/// The type of `name`'s whole block.
		fn body_type(&self, name: &str) -> String {
			let body = self.body(name);
			self.display(body.ty(body.root()))
		}

		/// The function `name`'s block as an S-expression; see `render`.
		fn shape(&self, name: &str) -> String {
			let body = self.body(name);
			self.render(body, body.root())
		}

		/// Renders a node without types: `(block (local x 1) => (+ x 2))`.
		/// A local is its name and declaration index (`x#1`), so shadowing
		/// shows; a jump names the label it leaves, or `loop`/`block`.
		fn render(&self, body: &Body, expr: ExprIdx) -> String {
			let list = |text: &str, items: &[ExprIdx]| {
				let mut text = format!("({text}");
				for &item in items {
					text.push(' ');
					text.push_str(&self.render(body, item));
				}
				text + ")"
			};
			let name = |symbol| self.context.strings.resolve(symbol).unwrap();
			match body.kind(expr) {
				ExprKind::Error => "error".to_string(),
				ExprKind::Int(value) => value.to_string(),
				ExprKind::Float(value) => format!("{value:?}"),
				ExprKind::Bool(value) => value.to_string(),
				ExprKind::Char(value) => format!("{value:?}"),
				ExprKind::String(contents) => {
					format!(
						"{:?}",
						self.context.strings.resolve(contents).unwrap()
					)
				}
				ExprKind::Const {
					constant,
					type_args,
				} => self.constant_name(constant, type_args),
				ExprKind::AbstractConst {
					constant,
					type_args,
				} => format!(
					"(abstract {})",
					self.constant_name(constant, type_args)
				),
				ExprKind::NextDiscriminant(index) => {
					name(self.defs.constants[usize::from(index)].name.inner)
						.to_string()
				}
				ExprKind::Local(local) => self.local_name(body, local),
				ExprKind::Global(index) => {
					name(self.defs.globals[usize::from(index)].name.inner)
						.to_string()
				}
				ExprKind::Function(index) => {
					name(self.defs.functions[usize::from(index)].name.inner)
						.to_string()
				}
				ExprKind::PrimitiveUnary { op, operand } => {
					list(op.as_str(), &[operand])
				}
				ExprKind::PrimitiveBinary { op, lhs, rhs } => {
					list(op.as_str(), &[lhs, rhs])
				}
				ExprKind::Call {
					function,
					type_args,
					args,
				} => {
					let callee = self.callee(function, type_args);
					list(&format!("call {callee}"), body.args(args))
				}
				ExprKind::AbstractCall {
					method,
					type_args,
					args,
				} => {
					let callee = self.callee(method, type_args);
					list(&format!("abstract {callee}"), body.args(args))
				}
				ExprKind::Tuple { elements } => {
					list("tuple", body.args(elements))
				}
				ExprKind::StructConstructor {
					struct_index, args, ..
				} => list(
					name(
						self.defs.structs[usize::from(struct_index)].name.inner,
					),
					body.args(args),
				),
				ExprKind::Cast { value } => {
					let ty = self.display(body.ty(expr));
					format!("(as {} {ty})", self.render(body, value))
				}
				ExprKind::FieldAccess { object, field } => format!(
					"(. {} {})",
					self.render(body, object),
					self.field_name(body.ty(object), field)
				),
				ExprKind::Load(place) => {
					format!("(load {})", self.render_place(body, place))
				}
				ExprKind::AddressOf(place) => {
					format!("(.& {})", self.render_place(body, place))
				}
				ExprKind::Block {
					statements, result, ..
				} => {
					let mut text = list("block", body.args(statements));
					if let Some(result) = result {
						text.pop();
						text.push_str(" => ");
						text.push_str(&self.render(body, result));
						text.push(')');
					}
					text
				}
				ExprKind::LocalDeclaration { pattern, value } => format!(
					"(local {} {})",
					self.render_pattern(body, pattern),
					self.render(body, value)
				),
				ExprKind::Match { scrutinee, arms } => {
					let mut text =
						format!("(match {}", self.render(body, scrutinee));
					for arm in body.arms(arms) {
						text.push_str(&format!(
							" ({} => {})",
							self.render_pattern(body, arm.pattern),
							self.render(body, arm.body)
						));
					}
					text + ")"
				}
				ExprKind::IfElse {
					condition,
					then_block,
					else_block,
				} => {
					let mut items = vec![condition, then_block];
					items.extend(else_block);
					list("if", &items)
				}
				ExprKind::Loop { statements, .. } => {
					list("loop", body.args(statements))
				}
				ExprKind::Break { scope, value } => {
					let target = self.scope_name(body, scope);
					list(&format!("break {target}"), value.as_slice())
				}
				ExprKind::Continue { scope } => {
					format!("(continue {})", self.scope_name(body, scope))
				}
				ExprKind::Return { value } => list("return", value.as_slice()),
				ExprKind::Drop { value } => list("drop", &[value]),
				ExprKind::Assign { target, value } => {
					list("=", &[target, value])
				}
				ExprKind::Store { place, value } => format!(
					"(store {} {})",
					self.render_place(body, place),
					self.render(body, value)
				),
				ExprKind::PrimitiveCompoundAssign { op, target, value } => {
					list(&format!("{}=", op.as_str()), &[target, value])
				}
				ExprKind::ConcreteCompoundAssign {
					method,
					type_args,
					target,
					value,
				} => list(
					&format!("assign call {}", self.callee(method, type_args)),
					&[target, value],
				),
				ExprKind::AbstractCompoundAssign {
					method,
					type_args,
					target,
					value,
				} => list(
					&format!(
						"assign abstract {}",
						self.callee(method, type_args)
					),
					&[target, value],
				),
				ExprKind::PrimitiveCompoundStore { op, place, value } => {
					format!(
						"(store {}= {} {})",
						op.as_str(),
						self.render_place(body, place),
						self.render(body, value)
					)
				}
				ExprKind::ConcreteCompoundStore {
					method,
					type_args,
					place,
					value,
				} => format!(
					"(store call {} {} {})",
					self.callee(method, type_args),
					self.render_place(body, place),
					self.render(body, value)
				),
				ExprKind::AbstractCompoundStore {
					method,
					type_args,
					place,
					value,
				} => format!(
					"(store abstract {} {} {})",
					self.callee(method, type_args),
					self.render_place(body, place),
					self.render(body, value)
				),
			}
		}

		/// Renders a pattern: a binding is its local (`x#1`), a destructuring
		/// lists one child per element or field (`(tuple a#0 _)`,
		/// `(Point a#0 _)`), an integer reads as its type's value.
		fn render_pattern(
			&self,
			body: &Body,
			pattern: super::super::body::PatIdx,
		) -> String {
			use super::super::body::PatKind;
			let list = |head: &str, children: &[super::super::body::PatIdx]| {
				let mut text = format!("({head}");
				for &child in children {
					text.push(' ');
					text.push_str(&self.render_pattern(body, child));
				}
				text + ")"
			};
			match body.pattern(pattern) {
				PatKind::Wildcard => "_".to_string(),
				PatKind::Bind(local) => self.local_name(body, local),
				PatKind::Tuple(elements) => {
					list("tuple", body.patterns(elements))
				}
				PatKind::Struct {
					struct_index,
					fields,
				} => {
					let name =
						self.defs.structs[usize::from(struct_index)].name.inner;
					let name = self.context.strings.resolve(name).unwrap();
					list(name, body.patterns(fields))
				}
				PatKind::Int(bits) => {
					let integer =
						super::Integer::from_type(body.pattern_ty(pattern))
							.unwrap();
					if integer.is_signed() {
						let width = integer.mask().count_ones();
						let shift = 64 - width;
						(((bits << shift) as i64) >> shift).to_string()
					} else {
						bits.to_string()
					}
				}
				PatKind::Bool(value) => value.to_string(),
				PatKind::Char(value) => format!("{value:?}"),
				PatKind::Constant {
					constant,
					type_args,
				} => self.constant_name(constant, type_args),
				PatKind::AbstractConstant {
					constant,
					type_args,
				} => format!(
					"(abstract {})",
					self.constant_name(constant, type_args)
				),
				PatKind::Or(alternatives) => {
					list("|", body.patterns(alternatives))
				}
				PatKind::Error => "error".to_string(),
			}
		}

		fn render_place(&self, body: &Body, place: PlaceIdx) -> String {
			match body.place(place).kind {
				PlaceKind::Deref { pointer } => {
					format!("(* {})", self.render(body, pointer))
				}
				PlaceKind::Field { object, field } => format!(
					"(. {} {})",
					self.render_place(body, object),
					self.field_name(body.place(object).ty, field)
				),
			}
		}

		fn function_name(&self, index: super::FunctionIdx) -> &str {
			let name = self.defs.functions[usize::from(index)].name.inner;
			self.context.strings.resolve(name).unwrap()
		}

		/// A constant's name, with its type arguments when it has any.
		fn constant_name(
			&self,
			index: super::ConstIdx,
			type_args: super::TypeList,
		) -> String {
			let name = self.defs.constants[usize::from(index)].name.inner;
			self.with_type_args(
				self.context.strings.resolve(name).unwrap(),
				type_args,
			)
		}

		/// A called function's name, with its type arguments when it has
		/// any: `add`, `id<u8>`.
		fn callee(
			&self,
			index: super::FunctionIdx,
			type_args: super::TypeList,
		) -> String {
			self.with_type_args(self.function_name(index), type_args)
		}

		fn with_type_args(
			&self,
			name: &str,
			type_args: super::TypeList,
		) -> String {
			let type_args = self.context.types.list(type_args);
			if type_args.is_empty() {
				return name.to_string();
			}
			let type_args: Vec<String> =
				type_args.iter().map(|&ty| self.display(ty)).collect();
			format!("{name}<{}>", type_args.join(", "))
		}

		fn local_name(&self, body: &Body, local: super::LocalIdx) -> String {
			let name = body.local(local).name.inner;
			format!(
				"{}#{}",
				self.context.strings.resolve(name).unwrap(),
				u32::from(local)
			)
		}

		fn field_name(
			&self,
			object: TypeIndex,
			field: super::FieldIdx,
		) -> &str {
			let Type::Struct { struct_index, .. } =
				*self.context.types.resolve(object)
			else {
				panic!("a field of a non-struct");
			};
			let field = self.defs.structs[usize::from(struct_index)].fields
				[usize::from(field)]
			.name
			.unwrap();
			self.context.strings.resolve(field.inner).unwrap()
		}

		/// A jump's target: its label, else the kind of scope it leaves.
		fn scope_name(&self, body: &Body, scope: super::ScopeIdx) -> String {
			let scope = body.scope(scope);
			match scope.label {
				Some(label) => self
					.context
					.strings
					.resolve(body.label(label).name.inner)
					.unwrap()
					.to_string(),
				None => format!("{:?}", scope.kind).to_lowercase(),
			}
		}

		/// The `(name, type)` of every local of `function`, in declaration
		/// order.
		fn locals(&self, function: &str) -> Vec<(String, String)> {
			self.body(function)
				.locals()
				.iter()
				.map(|local| {
					let name =
						self.context.strings.resolve(local.name.inner).unwrap();
					(name.to_string(), self.display(local.ty))
				})
				.collect()
		}
	}

	#[test]
	fn the_embedded_stdlib_reports_nothing_but_unsupported_forms() {
		test_case!(case = "");
		case.diagnostics().assert_none();
	}

	#[test]
	fn parameters_are_locals_of_the_root_scope() {
		const SOURCE: &str = "func f(a: u32, mut b: u32) -> u32 { a + b }";
		test_case!(case = SOURCE);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("f"), "(block => (+ a#0 b#1))");
		assert_eq!(
			case.locals("f"),
			[("a".into(), "u32".into()), ("b".into(), "u32".into())]
		);
		let body = case.body("f");
		assert!(body.scope(super::ScopeIdx::ROOT).parent.is_none());
		// Each use of a parameter is recorded as a reference to it.
		let file_id = case
			.defs
			.namespaces
			.file_id(Scope::Package(case.defs.root_package).into());
		let start = (STDLIB.len() + 1 + SOURCE.find("a + b").unwrap()) as u32;
		let site = (
			crate::diagnostics::SourceSpan::new(
				file_id,
				TextSpan::new(start, start + 1),
			),
			Tier::Value,
		);
		assert!(matches!(
			case.context.resolutions.by_site.get(&site),
			Some(Referent::Local { local, .. }) if u32::from(*local) == 0
		));
	}

	#[test]
	fn a_block_result_takes_the_return_type() {
		test_case!(
			case = indoc! {"
				func literal() -> u8 { 200 + 50 }
				func nothing() {}
				func diverges() -> u32 { loop {} }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.body_type("literal"), "u8");
		assert_eq!(case.body_type("nothing"), "()");
		assert_eq!(case.body_type("diverges"), "!");
	}

	#[test]
	fn a_block_without_a_result_does_not_give_a_value() {
		test_case!(case = "func f() -> u32 { local x: u32 = 1; }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
	}

	#[test]
	fn a_local_takes_its_written_type_or_its_values() {
		test_case!(
			case = indoc! {"
				func f(a: u64) {
					local x: u8 = 1;
					local y = a;
					local z = (x, y);
				}
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.locals("f"),
			[
				("a".into(), "u64".into()),
				("x".into(), "u8".into()),
				("y".into(), "u64".into()),
				("z".into(), "(u8, u64)".into()),
			]
		);
	}

	#[test]
	fn a_local_of_an_untyped_literal_needs_a_type() {
		test_case!(case = "func f() { local x = 1; }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeAnnotationRequired]);
		assert_eq!(case.locals("f"), [("x".into(), "{unknown}".into())]);
	}

	#[test]
	fn a_later_local_shadows_an_earlier_one_from_its_declaration_on() {
		test_case!(
			case = "func f() -> u32 { local x: u32 = 1; local x = x + 1; x }"
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block (local x#0 1) (local x#1 (+ x#0 1)) => x#1)"
		);
	}

	#[test]
	fn a_local_is_visible_only_in_its_block() {
		test_case!(
			case = indoc! {"
				func f() -> u32 {
					block { local inner: u32 = 1; };
					inner
				}
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
	}

	#[test]
	fn a_local_shadows_an_item_of_the_same_name() {
		test_case!(
			case = "const x: u8 = 1; func f() -> u16 { local x: u16 = 2; x }"
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("f"), "(block (local x#0 2) => x#0)");
	}

	#[test]
	fn a_statement_value_must_be_used_or_dropped() {
		test_case!(
			case = indoc! {"
				func one() -> u32 { 1 }
				func f() {
					one();
					_ = one();
				}
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnusedValue]);
		assert_eq!(case.shape("f"), "(block (call one) (drop (call one)))");
	}

	#[test]
	fn code_after_a_diverging_statement_is_unreachable() {
		test_case!(case = "func f() -> u32 { return 1; local x: u32 = 2; x }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnreachableCode]);
		case.diagnostics()
			.assert_warning(DiagnosticCode::UnreachableCode);
		assert_eq!(case.body_type("f"), "u32");
	}

	#[test]
	fn if_branches_share_a_type() {
		test_case!(
			case = indoc! {"
				func pick(c: bool, a: u8) -> u8 { if c { a } else { 1 } }
				func nested(c: bool) -> u16 { if c { 1 } else { if !c { 2 } else { 3 } } }
				func diverging(c: bool, a: u8) -> u8 { if c { return a; } else { a } }
				func statement(c: bool) { if c { pick(c, 1); } }
				func untyped(c: bool) { local x: i64 = if c { 1 } else { 2 }; }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnusedValue]);
		assert_eq!(
			case.shape("pick"),
			"(block => (if c#0 (block => a#1) (block => 1)))"
		);
		assert_eq!(case.body_type("diverging"), "u8");
		assert_eq!(case.body_type("nested"), "u16");
		// Context reaches literals through both branches.
		let body = case.body("untyped");
		let ExprKind::Block { statements, .. } = body.kind(body.root()) else {
			unreachable!()
		};
		let ExprKind::LocalDeclaration { value, .. } =
			body.kind(body.args(statements)[0])
		else {
			unreachable!()
		};
		assert_eq!(case.display(body.ty(value)), "i64");
		let ExprKind::IfElse { then_block, .. } = body.kind(value) else {
			unreachable!()
		};
		let ExprKind::Block {
			result: Some(result),
			..
		} = body.kind(then_block)
		else {
			unreachable!()
		};
		assert_eq!(case.display(body.ty(result)), "i64");
	}

	#[test]
	fn an_untyped_branch_takes_the_other_branchs_type() {
		test_case!(
			case =
				"func f(c: bool, a: u8) { local x = if c { 1 } else { a }; }"
		);
		case.diagnostics().assert_none();
		assert_eq!(case.locals("f")[2], ("x".into(), "u8".into()));
	}

	#[test]
	fn if_errors_are_reported_where_they_are_written() {
		test_case!(
			case = indoc! {"
				func condition(a: u8) { if a { } }
				func mismatch(c: bool, a: u8, b: u16) { local x = if c { a } else { b }; }
				func missing_else(c: bool, a: u8) -> u8 { if c { a } }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::MissingElseBlock,
		]);
	}

	#[test]
	fn a_loop_is_typed_by_its_breaks() {
		test_case!(
			case = indoc! {"
				func first(n: u32) -> u32 {
					local mut i: u32 = 0;
					loop {
						if i == n { break i; }
						i += 1;
					}
				}
				func endless() -> u8 { loop {} }
				func unit() { loop { break; } }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("first"),
			"(block (local i#1 0) => (loop (if (== i#1 n#0) (block (break loop i#1))) \
			 (+= i#1 1)))"
		);
		assert_eq!(case.body_type("endless"), "!");
		let body = case.body("unit");
		let ExprKind::Block {
			result: Some(lp), ..
		} = body.kind(body.root())
		else {
			unreachable!()
		};
		assert_eq!(case.display(body.ty(lp)), "()");
	}

	#[test]
	fn break_values_must_agree() {
		test_case!(
			case = indoc! {"
				func f(c: bool, a: u8, b: u16) {
					local x = loop { if c { break a; } break b; };
				}
				func untyped() { local x = loop { break 1; }; }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeAnnotationRequired,
		]);
	}

	#[test]
	fn a_label_names_the_scope_a_jump_leaves() {
		test_case!(
			case = indoc! {"
				func f(c: bool) -> u32 {
					outer: loop {
						loop {
							if c { break :outer 1; }
							continue :outer;
						}
					}
				}
				func labelled_block(c: bool) -> u8 {
					found: block {
						if c { break :found 1; }
						2
					}
				}
				func labelled_if(c: bool) -> u8 {
					l: if c { break :l 1; } else { 2 }
				}
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block => (loop (loop (if c#0 (block (break outer 1))) \
			 (continue outer))))"
		);
		assert_eq!(case.body_type("f"), "u32");
		assert_eq!(
			case.shape("labelled_block"),
			"(block => (block (if c#0 (block (break found 1))) => 2))"
		);
		// Both branches of a labelled `if` share its label.
		let body = case.body("labelled_if");
		let ExprKind::Block {
			result: Some(branching),
			..
		} = body.kind(body.root())
		else {
			unreachable!()
		};
		let ExprKind::IfElse {
			then_block,
			else_block: Some(else_block),
			..
		} = body.kind(branching)
		else {
			unreachable!()
		};
		let scope_of = |block| match body.kind(block) {
			ExprKind::Block { scope, .. } => body.scope(scope).label,
			_ => unreachable!(),
		};
		assert!(scope_of(then_block).is_some());
		assert_eq!(scope_of(then_block), scope_of(else_block));
	}

	#[test]
	fn jumps_need_a_target() {
		test_case!(
			case = indoc! {"
				func outside() { break; }
				func outside_continue() { continue; }
				func unknown() { loop { break :nowhere; } }
				func not_a_loop() { l: block { continue :l; } }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::BreakOutsideOfLoop,
			DiagnosticCode::ContinueOutsideOfLoop,
			DiagnosticCode::UndeclaredLabel,
			DiagnosticCode::ContinueOutsideOfLoop,
		]);
	}

	#[test]
	fn a_labelled_jump_is_recorded_as_a_reference_to_its_label() {
		const SOURCE: &str = "func f() { outer: loop { break :outer; } }";
		test_case!(case = SOURCE);
		case.diagnostics().assert_none();
		let file_id = case
			.defs
			.namespaces
			.file_id(Scope::Package(case.defs.root_package).into());
		let start =
			(STDLIB.len() + 1 + SOURCE.find(":outer").unwrap() + 1) as u32;
		let site = (
			crate::diagnostics::SourceSpan::new(
				file_id,
				TextSpan::new(start, start + "outer".len() as u32),
			),
			Tier::Value,
		);
		assert!(matches!(
			case.context.resolutions.by_site.get(&site),
			Some(Referent::Label { label, .. }) if u32::from(*label) == 0
		));
	}

	#[test]
	fn return_gives_the_function_its_value() {
		test_case!(
			case = indoc! {"
				func early(c: bool) -> u8 { if c { return 1; } 2 }
				func bare() { return; }
				func wrong() -> u8 { return; }
				func mismatch(a: u16) -> u8 { return a; }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
		]);
		assert_eq!(
			case.shape("early"),
			"(block (if c#0 (block (return 1))) => 2)"
		);
	}

	#[test]
	fn assignment_writes_a_mutable_local() {
		test_case!(
			case = indoc! {"
				func f() {
					local mut x: u8 = 1;
					x = 2;
				}
				func errors() {
					local x: u8 = 1;
					x = 2;
					errors() = ();
					_ = 1;
				}
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::CannotMutateImmutable,
			DiagnosticCode::InvalidAssignmentTarget,
			DiagnosticCode::TypeAnnotationRequired,
		]);
		assert_eq!(case.shape("f"), "(block (local x#0 1) (= x#0 2))");
	}

	#[test]
	fn a_global_is_a_handle_and_is_not_assigned() {
		test_case!(
			case = indoc! {"
				global mut counter: u32 = 0;
				func f() {
					counter = 3;
					counter += 1;
				}
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::InvalidAssignmentTarget,
			DiagnosticCode::InvalidAssignmentTarget,
		]);
		case.diagnostics().assert_error_saying(
			"a `global mut` is written with `counter.set(value)`",
		);
	}

	#[test]
	fn an_operator_call_carries_its_type_arguments() {
		test_case!(
			case = indoc! {"
				struct W<T>(x: T);
				impl<T> Add for W<T> { func add(self, rhs: Self) -> Self { rhs } }
				func concrete(w: W<u8>) -> W<u8> { w + w }
				func generic<T: Add>(t: T) -> T { t + t }
				func assigned(w: W<u8>) { local mut v = w; v += w; }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("concrete"), "(block => (call add<u8> w#0 w#0))");
		assert_eq!(
			case.shape("generic"),
			"(block => (abstract add<T> t#0 t#0))"
		);
		assert_eq!(
			case.shape("assigned"),
			"(block (local v#1 w#0) (assign call add<u8> v#1 w#0))"
		);
	}

	#[test]
	fn compound_assignment_dispatches_like_its_operator() {
		test_case!(
			case = indoc! {"
				struct V(x: u32);
				impl Add for V { func add(self, rhs: Self) -> Self { rhs } }
				func scalar() { local mut a: u32 = 1; a += 2; a <<= 1; }
				func overloaded(v: V) { local mut w = v; w += v; }
				func generic<T: Add>(t: T) { local mut u = t; u += t; }
				func missing(c: bool) { local mut d = c; d -= c; }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::BinaryOperatorCannotBeApplied]);
		assert_eq!(
			case.shape("scalar"),
			"(block (local a#0 1) (+= a#0 2) (<<= a#0 1))"
		);
		assert_eq!(
			case.shape("overloaded"),
			"(block (local w#1 v#0) (assign call add w#1 v#0))"
		);
		assert_eq!(
			case.shape("generic"),
			"(block (local u#1 t#0) (assign abstract add<T> u#1 t#0))"
		);
	}

	#[test]
	fn a_field_of_a_value_is_read_and_written_through_its_root() {
		test_case!(
			case = indoc! {"
				struct Inner(v: u8);
				struct Outer(inner: Inner, n: u32);
				struct Wrap<T>(value: T);
				func read(o: Outer) -> u8 { o.inner.v }
				func generic(w: Wrap<u16>) -> u16 { w.value }
				func write(o: Outer) { local mut p = o; p.inner.v = 1; p.n += 1; }
				func immutable(o: Outer) { o.n = 1; }
				func temporary(o: Outer) { read(o).v = 1; }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::CannotMutateImmutable,
			DiagnosticCode::UnknownStructField,
		]);
		assert_eq!(case.shape("read"), "(block => (. (. o#0 inner) v))");
		assert_eq!(case.body_type("generic"), "u16");
		assert_eq!(
			case.shape("write"),
			"(block (local p#1 o#0) (= (. (. p#1 inner) v) 1) (+= (. p#1 n) 1))"
		);
	}

	#[test]
	fn field_access_checks_the_field() {
		test_case!(
			case = indoc! {"
				mod m { pub struct S(pub open: u8, closed: u8); }
				func f(s: m::S) -> u8 { s.open + s.closed }
				func g(s: m::S) -> u8 { s.missing }
				func h(x: u8) -> u8 { x.field }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::PrivateStructField,
			DiagnosticCode::UnknownStructField,
			DiagnosticCode::UnknownStructField,
		]);
	}

	#[test]
	fn a_place_in_memory_is_read_written_and_addressed() {
		test_case!(
			case = indoc! {"
				memory heap: u32;
				struct Node(value: u32, next: heap::*Node);
				func read(p: heap::&Node) -> u32 { p.*.value }
				func write(p: heap::*Node) { p.* = Node(1, p); p.*.value += 2; }
				func address(p: heap::*Node) -> heap::&u32 { p.*.value.& }
				func next(p: heap::*Node) -> u32 { p.*.next.*.value }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("read"), "(block => (load (. (* p#0) value)))");
		assert_eq!(
			case.shape("write"),
			"(block (store (* p#0) (Node 1 p#0)) (store += (. (* p#0) value) 2))"
		);
		assert_eq!(case.shape("address"), "(block => (.& (. (* p#0) value)))");
		assert_eq!(
			case.shape("next"),
			"(block => (load (. (* (load (. (* p#0) next))) value)))"
		);
	}

	#[test]
	fn a_place_is_written_only_through_an_exclusive_pointer() {
		test_case!(
			case = indoc! {"
				memory heap: u32;
				func shared(p: heap::&u32) { p.* = 1; }
				func not_a_pointer(x: u32) -> u32 { x.* }
				func local_address(x: u32) -> heap::&u32 { x.& }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::CannotMutateImmutable,
			DiagnosticCode::CannotDerefNonPointer,
			DiagnosticCode::InvalidAssignmentTarget,
		]);
	}

	#[test]
	fn a_call_checks_its_arguments_against_the_parameters() {
		test_case!(
			case = indoc! {"
				func add(a: u32, b: u32) -> u32 { a + b }
				func f() -> u32 { add(1, 2) }
				func count() -> u32 { add(1) }
				func mismatch(c: bool) -> u32 { add(c, 2) }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::TypeMistmatch,
		]);
		assert_eq!(case.shape("f"), "(block => (call add 1 2))");
	}

	#[test]
	fn a_generic_call_learns_its_type_arguments() {
		test_case!(
			case = indoc! {"
				trait Number {}
				impl Number for u32 {}
				impl Number for i64 {}
				func id<T>(x: T) -> T { x }
				func zero<T: Number>() -> T { loop {} }
				func from_argument(a: u16) -> u16 { id(a) }
				func from_expected() -> u8 { id(1) }
				func from_turbofish() { local x = zero::<i64>(); }
				func from_result() -> u32 { zero() }
				func nothing() { _ = zero(); }
				func unsatisfied() { local x = zero::<bool>(); }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TraitBoundViolation,
		]);
		assert_eq!(case.body_type("from_argument"), "u16");
		assert_eq!(case.body_type("from_expected"), "u8");
		assert_eq!(case.locals("from_turbofish"), [("x".into(), "i64".into())]);
		assert_eq!(case.shape("from_expected"), "(block => (call id<u8> 1))");
	}

	#[test]
	fn a_function_is_a_value_of_its_own_type() {
		test_case!(
			case = indoc! {"
				func id<T>(x: T) -> T { x }
				func f() { local g = id::<u8>; local h = id; }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeAnnotationRequired]);
		assert_eq!(case.locals("f")[0], ("g".into(), "id<u8>".into()));
	}

	#[test]
	fn a_cast_reinterprets_a_value_of_the_same_wasm_type() {
		test_case!(
			case = indoc! {"
				memory heap: u32;
				func widen(a: u8) -> i32 { a as i32 }
				func sign(a: i64) -> u64 { a as u64 }
				func truth(b: bool) -> u8 { b as u8 }
				func code(c: char) -> u32 { c as u32 }
				func enum_value(o: Ordering) -> i8 { o as i8 }
				func inferred(a: u16) -> u32 { a as _ }
				func literal() -> u8 { 300 as u8 }
				func give_up(p: heap::*u8) -> heap::&u8 { p as heap::&u8 }
				func address(p: heap::&u8) -> u32 { p as u32 }
				func signed_address(p: heap::&u8) -> i32 { p as i32 }
				func from_int(a: u32) -> heap::*u8 { a as heap::*u8 }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
		assert_eq!(case.shape("widen"), "(block => (as a#0 i32))");
		assert_eq!(case.shape("inferred"), "(block => (as a#0 u32))");
	}

	#[test]
	fn a_cast_never_changes_the_value() {
		test_case!(
			case = indoc! {"
				memory heap: u32;
				func wider(a: i32) -> i64 { a as i64 }
				func narrower(a: u64) -> u32 { a as u32 }
				func to_float(a: u8) -> f64 { a as f64 }
				func to_int(f: f32) -> i32 { f as i32 }
				func bits(f: f32) -> u32 { f as u32 }
				func float_to_bool(f: f32) -> bool { f as bool }
				func gain(p: heap::&u8) -> heap::*u8 { p as heap::*u8 }
				func wide_address(p: heap::&u8) -> u64 { p as u64 }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
		]);
		case.diagnostics().assert_error_saying(
			"a cast reinterprets a value without changing it",
		);
	}

	#[test]
	fn a_string_literal_takes_a_byte_slice_or_array_from_its_context() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				func slice() -> heap::&[u8] { "hello" }
				func array() -> heap::&[u8; 5] { "hello" }
				func escaped() -> heap::&[u8; 2] { "a\n" }
				func annotated() { local s: heap::&[u8; 3] = "abc"; }
				func branches(c: bool) -> heap::&[u8] { if c { "yes" } else { "no" } }
				func tuple() -> (heap::&[u8], u8) { ("a", 1) }
				func any_memory<Mem: Memory>() -> Mem::&[u8] { "abstract" }
			"#}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("slice"), r#"(block => "hello")"#);
		assert_eq!(case.body_type("slice"), "heap::&[u8]");
		assert_eq!(case.body_type("array"), "heap::&[u8; 5]");
		assert_eq!(case.shape("escaped"), r#"(block => "a\n")"#);
		assert_eq!(
			case.locals("annotated"),
			[("s".into(), "heap::&[u8; 3]".into())]
		);
		assert_eq!(case.body_type("branches"), "heap::&[u8]");
		assert_eq!(case.body_type("tuple"), "(heap::&[u8], u8)");
		assert_eq!(case.body_type("any_memory"), "Mem::&[u8]");
	}

	#[test]
	fn a_string_literal_waits_for_a_generic_call_to_learn_its_memory() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				func take<Mem: Memory>(s: Mem::&[u8], p: Mem::&u8) {}
				func call(p: heap::&u8) { take("abc", p); }
			"#}
		);
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_string_literal_is_a_shared_byte_type_of_its_length() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				func length() -> heap::&[u8; 4] { "abc" }
				func exclusive() -> heap::*[u8] { "abc" }
				func number() -> u32 { "abc" }
				func untyped() { local s = "abc"; }
				func operator() -> heap::&[u8] { "a" + "b" }
				func negate() -> heap::&[u8] { -"a" }
				func expected(c: bool) -> heap::&[u8] { if c { "a" } else { 1 } }
				func joined(c: bool) { local x = if c { "a" } else { 1 }; }
				func escape() -> heap::&[u8] { "\q" }
			"#}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArraySizeMismatch,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::BinaryOperatorCannotBeApplied,
			DiagnosticCode::UnaryOperatorCannotBeApplied,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::UnknownCharacterEscape,
		]);
		case.diagnostics().assert_error_saying(
			"this string literal is 3 bytes long, but `heap::&[u8; 4]` holds 4",
		);
	}

	#[test]
	fn a_string_literal_is_cast_to_what_it_can_become() {
		test_case!(
			case = indoc! {r#"
				memory heap: u32;
				func array() -> heap::&[u8; 3] { "abc" as heap::&[u8; 3] }
				func slice() -> heap::&[u8] { "abc" as heap::&[u8] }
				func number() -> u32 { "abc" as u32 }
				func exclusive() -> heap::*[u8] { "abc" as heap::*[u8] }
				func length() -> heap::&[u8; 2] { "abc" as heap::&[u8; 2] }
			"#}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::InvalidCast,
			DiagnosticCode::InvalidCast,
			DiagnosticCode::ArraySizeMismatch,
		]);
		assert_eq!(
			case.shape("array"),
			r#"(block => (as "abc" heap::&[u8; 3]))"#
		);
	}

	#[test]
	fn enums_and_pointers_compare_natively() {
		test_case!(
			case = indoc! {"
				memory heap: u32;
				func less(o: Ordering) -> bool { o == Ordering::Less }
				func same(a: heap::&u8, b: heap::&u8) -> bool { a != b }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("less"), "(block => (== o#0 Less))");
	}

	#[test]
	fn a_constant_comparing_variants_is_evaluated() {
		test_case!(
			case = "const SAME: bool = Ordering::Less == Ordering::Greater;"
		);
		case.diagnostics().assert_none();
		let DefKind::Const(index) = case.resolve("SAME") else {
			panic!("expected a constant");
		};
		assert_eq!(
			case.context.const_values[usize::from(index)],
			ConstValueState::Evaluated(Box::new([ConstScalar::bool(false)]))
		);
	}

	#[test]
	fn a_global_initializer_is_checked_against_its_type() {
		test_case!(case = "global small: u8 = 300;");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
	}

	#[test]
	fn a_path_through_a_type_calls_its_member_directly() {
		test_case!(
			case = indoc! {"
				enum E: u8 { A = 0 }
				impl E { pub func pick<T>(t: T) -> E { E::A } }
				struct W<T>(x: T);
				impl<T> W<T> {
					pub func new(x: T) -> W<T> { W(x) }
					pub func get(self) -> T { loop {} }
					func again(x: T) -> W<T> { Self::new(x) }
				}
				trait Make { func make() -> Self; }
				struct P();
				impl Make for P { func make() -> Self { P() } }
				func inherent() -> E { E::pick(true) }
				func generic_impl(w: W<u8>) -> u8 { W::<u8>::get(w) }
				func constructed() -> W<u16> { W::<u16>::new(1) }
				func trait_impl() -> P { P::make() }
				func value() { local f = W::<u8>::new; }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("inherent"), "(block => (call pick<bool> true))");
		assert_eq!(case.shape("generic_impl"), "(block => (call get<u8> w#0))");
		assert_eq!(case.shape("constructed"), "(block => (call new<u16> 1))");
		assert_eq!(case.member_shape("again"), "(block => (call new<T> x#0))");
		assert_eq!(case.shape("trait_impl"), "(block => (call make))");
		assert_eq!(case.locals("value"), [("f".into(), "new<u8>".into())]);
	}

	#[test]
	fn a_trait_declaration_is_called_with_its_receiver_as_self() {
		test_case!(
			case = indoc! {"
				trait Make {
					func make() -> Self;
					func zero() -> u32 { 0 }
				}
				struct P();
				impl Make for P { func make() -> Self { P() } }
				func abstract_receiver<T: Make>() -> T { T::make() }
				func inherited_default() -> u32 { P::zero() }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("abstract_receiver"),
			"(block => (abstract make<T>))"
		);
		assert_eq!(
			case.shape("inherited_default"),
			"(block => (abstract zero<P>))"
		);
	}

	#[test]
	fn a_bracketed_root_names_the_receiver_and_maybe_its_trait() {
		test_case!(
			case = indoc! {"
				trait Make { func make() -> Self; }
				trait Other { func make() -> Self; }
				struct P();
				impl Make for P { func make() -> Self { P() } }
				impl Other for P { func make() -> Self { P() } }
				struct W<T>(x: T);
				impl<T> W<T> { pub func new(x: T) -> W<T> { W(x) } }
				func qualified() -> P { <P as Make>::make() }
				func abstract_qualified<T: Make>() -> T { <T as Make>::make() }
				func grouped() -> W<u8> { <W<u8>>::new(1) }
				func ambiguous() -> P { P::make() }
				func not_implemented() -> bool { <bool as Make>::make() }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::AmbiguousTraitMember,
			DiagnosticCode::TraitBoundViolation,
		]);
		assert_eq!(case.shape("qualified"), "(block => (call make))");
		assert_eq!(
			case.shape("abstract_qualified"),
			"(block => (abstract make<T>))"
		);
		assert_eq!(case.shape("grouped"), "(block => (call new<u8> 1))");
	}

	#[test]
	fn a_member_must_exist_and_be_visible() {
		test_case!(
			case = indoc! {"
				mod inner {
					pub struct S();
					impl S { func hidden() {} pub func shown() {} }
					trait Secret { func secret(); }
					impl Secret for S { func secret() {} }
				}
				func missing() { inner::S::nothing(); }
				func private() { inner::S::hidden(); inner::S::shown(); }
				func private_trait() { inner::S::secret(); }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::MethodNotFound,
			DiagnosticCode::PrivateItem,
			DiagnosticCode::PrivateItem,
		]);
		case.diagnostics()
			.assert_error_saying("associated function `hidden` is private");
	}

	#[test]
	fn a_type_named_without_its_arguments_leaves_them_to_the_call() {
		test_case!(
			case = indoc! {"
				struct W<T>(x: T);
				impl<T> W<T> {
					pub func new(x: T) -> W<T> { W(x) }
					pub func empty() -> W<T> { loop {} }
					pub func of<U>() -> W<T> { loop {} }
				}
				struct M<T>(x: T);
				impl M<u8> { pub func one() -> M<u8> { loop {} } }
				impl M<u32> { pub func only() -> M<u32> { loop {} } }
				func from_argument(a: u8) -> W<u8> { W::new(a) }
				func from_expected() -> W<u16> { W::empty() }
				func with_own(a: u8) -> W<bool> { W::of::<u8>() }
				func picked() -> M<u32> { M::only() }
				func uninferred() { W::empty(); }
				func other_impl() -> M<u8> { M::only() }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TypeMistmatch,
		]);
		case.diagnostics()
			.assert_error_saying("cannot infer type for type parameter `T`");
		assert_eq!(
			case.shape("from_argument"),
			"(block => (call new<u8> a#0))"
		);
		assert_eq!(case.shape("from_expected"), "(block => (call empty<u16>))");
		assert_eq!(case.shape("with_own"), "(block => (call of<bool, u8>))");
		assert_eq!(case.shape("picked"), "(block => (call only))");
	}

	#[test]
	fn an_impl_selected_before_its_arguments_proves_its_bounds_at_the_call() {
		test_case!(
			case = indoc! {"
				trait Small {}
				impl Small for u8 {}
				struct B<T>(x: T);
				impl<T: Small> B<T> { pub func new(x: T) -> B<T> { B(x) } }
				func holds(a: u8) { local b = B::new(a); }
				func violated() { local b = B::new(true); }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
	}

	#[test]
	fn self_constructs_the_struct_its_impl_is_for() {
		test_case!(
			case = indoc! {"
				struct W<T>(x: T);
				impl<T> W<T> {
					func positional(x: T) -> W<T> { Self(x) }
					func named(x: T) -> Self { Self({ x }) }
				}
				struct P();
				trait Make { func make() -> Self; }
				impl Make for P { func make() -> Self { Self() } }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.member_shape("positional"), "(block => (W x#0))");
		assert_eq!(case.member_shape("named"), "(block => (W x#0))");
		assert_eq!(case.member_shape("make"), "(block => (P))");
	}

	#[test]
	fn self_is_constructed_only_where_it_names_an_accessible_struct() {
		test_case!(
			case = indoc! {"
				mod inner { pub struct P(x: u32); }
				impl inner::P { func outside() -> inner::P { Self(1) } }
				struct W(x: u32);
				impl W {
					func bare() { local w = Self; }
					func written() -> W { Self::<u8>(1) }
				}
				enum E: u8 { A = 0 }
				impl E { func variant() -> E { Self(0) } }
				trait Tr { func make() -> Self { Self() } }
				func free() { Self(); }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::PrivateItem,
			DiagnosticCode::StructUsedAsValue,
			DiagnosticCode::TypeArgumentsNotAllowed,
			DiagnosticCode::CannotCallExpression,
			DiagnosticCode::CannotCallExpression,
			DiagnosticCode::CannotCallExpression,
		]);
		case.diagnostics()
			.assert_error_saying("the constructor of struct `P` is private");
		case.diagnostics()
			.assert_error_saying("`Self` is `E`, which is not a struct");
		case.diagnostics()
			.assert_error_saying("`Self` names no struct here");
	}

	#[test]
	fn an_associated_constant_is_read_like_its_function_would_be_called() {
		test_case!(
			case = indoc! {"
				trait Sized {
					const SIZE: u32;
					const ALIGN: u32 = 4;
				}
				struct P();
				impl Sized for P { const SIZE: u32 = 8; }
				impl P { const ORIGIN: u8 = 0; }
				struct W<T>(x: T);
				impl<T> W<T> { const ID: u32 = 1; }
				func inherent() -> u8 { P::ORIGIN }
				func generic_inherent() -> u32 { W::<u8>::ID }
				func trait_impl() -> u32 { P::SIZE }
				func inherited() -> u32 { P::ALIGN }
				func abstract_receiver<T: Sized>() -> u32 { T::SIZE }
				func qualified() -> u32 { <P as Sized>::SIZE }
				const EVALUATED: u8 = P::ORIGIN;
				func written() -> u8 { P::ORIGIN::<u8> }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
		assert_eq!(case.shape("inherent"), "(block => ORIGIN)");
		assert_eq!(case.shape("generic_inherent"), "(block => ID<u8>)");
		assert_eq!(case.shape("trait_impl"), "(block => SIZE)");
		assert_eq!(case.shape("inherited"), "(block => (abstract ALIGN<P>))");
		assert_eq!(
			case.shape("abstract_receiver"),
			"(block => (abstract SIZE<T>))"
		);
		assert_eq!(case.shape("qualified"), "(block => SIZE)");
		let DefKind::Const(index) = case.resolve("EVALUATED") else {
			panic!("expected a constant");
		};
		assert!(matches!(
			case.context.const_values[usize::from(index)],
			ConstValueState::Evaluated(_)
		));
	}

	#[test]
	fn a_method_call_passes_its_receiver_first() {
		test_case!(
			case = indoc! {"
				memory heap: u32;
				struct W<T>(x: T);
				impl<T> W<T> {
					pub func get(self) -> T { loop {} }
					pub func map<U>(self, u: U) -> W<U> { W(u) }
					pub func by_pointer(self: heap::*Self) -> T { loop {} }
				}
				trait Twice { func twice(self) -> Self; }
				impl Twice for u8 { func twice(self) -> Self { self } }
				func inherent(w: W<u8>) -> u8 { w.get() }
				func own_args(w: W<u8>) -> W<bool> { w.map(true) }
				func turbofish(w: W<u8>) -> W<u16> { w.map::<u16>(1) }
				func trait_impl(a: u8) -> u8 { a.twice() }
				func abstract_receiver<T: Twice>(t: T) -> T { t.twice() }
				func pointer(p: heap::*W<u8>) -> u8 { p.by_pointer() }
				func reverse(o: Ordering) -> Ordering { o.reverse() }
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("inherent"), "(block => (call get<u8> w#0))");
		assert_eq!(
			case.shape("own_args"),
			"(block => (call map<u8, bool> w#0 true))"
		);
		assert_eq!(
			case.shape("turbofish"),
			"(block => (call map<u8, u16> w#0 1))"
		);
		assert_eq!(case.shape("trait_impl"), "(block => (call twice a#0))");
		assert_eq!(
			case.shape("abstract_receiver"),
			"(block => (abstract twice<T> t#0))"
		);
		assert_eq!(
			case.shape("pointer"),
			"(block => (call by_pointer<u8> p#0))"
		);
		assert_eq!(case.shape("reverse"), "(block => (call reverse o#0))");
	}

	/// `Global::get` and `GlobalMut::set` are declarations a global's impls
	/// inherit, so they are called with the global as `Self`.
	#[test]
	fn a_global_is_read_and_written_through_its_handle() {
		test_case!(
			case = indoc! {"
				global mut counter: u32 = 0;
				global limit: u32 = 10;
				func bump() -> u32 {
					counter.set(counter.get() + 1);
					counter.get()
				}
				func fixed() { limit.set(1); }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::MethodNotFound]);
		assert_eq!(
			case.shape("bump"),
			"(block (abstract set<counter> counter (+ (abstract get<counter> \
			 counter) 1)) => (abstract get<counter> counter))"
		);
	}

	#[test]
	fn a_method_call_needs_a_method_of_the_receiver() {
		test_case!(
			case = indoc! {"
				memory heap: u32;
				struct S();
				impl S {
					pub func by_value(self) {}
					pub func associated() {}
				}
				func missing(s: S) { s.nothing(); }
				func not_a_method(s: S) { s.associated(); }
				func through_pointer(p: heap::*S) { p.by_value(); }
				func loaded(p: heap::*S) { p.*.by_value(); }
				func untyped() { (1).add(2); }
				func arguments(s: S) { s.by_value(1); }
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::MethodNotFound,
			DiagnosticCode::NotAMethod,
			DiagnosticCode::MethodNotFound,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::ArgumentCountMismatch,
		]);
		case.diagnostics().assert_error_saying(
			"this function takes 0 arguments but 1 was supplied",
		);
	}

	#[test]
	fn an_unsupported_form_is_reported_once_as_a_bug() {
		test_case!(
			case = indoc! {"
				func f(o: Ordering) -> Ordering {
					o[0]
				}
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnsupportedExpression]);
		assert_eq!(case.shape("f"), "(block => error)");
	}

	#[test]
	fn a_local_pattern_takes_its_value_apart() {
		test_case!(
			case = indoc! {"
				struct Point(x: u32, y: i64);
				struct W<T>(a: T, b: bool);
				func f(p: Point, t: (u8, (u16, u32)), w: W<u8>) {
					local Point(x, y) = p;
					local Point({ y: py, .. }) = p;
					local (a, (_, c)) = t;
					local (.., (d, ..)) = t;
					local W(e, mut g) = w;
				}
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block \
			 (local (Point x#3 y#4) p#0) \
			 (local (Point _ py#5) p#0) \
			 (local (tuple a#6 (tuple _ c#7)) t#1) \
			 (local (tuple _ (tuple d#8 _)) t#1) \
			 (local (W e#9 g#10) w#2))"
		);
		let types: Vec<String> = case.locals("f")[3..]
			.iter()
			.map(|(_, ty)| ty.clone())
			.collect();
		assert_eq!(
			types,
			["u32", "i64", "i64", "u8", "u32", "u16", "u8", "bool"]
		);
	}

	#[test]
	fn a_local_pattern_must_fit_its_value() {
		test_case!(
			case = indoc! {"
				struct Point(x: u32, y: u32);
				struct Pair(u32, u32);
				func f(p: Point, t: (u32, u32), q: Pair) {
					local (a, b, c) = t;
					local Point(x, .., ..) = p;
					local Point({ x }) = p;
					local Point({ z, .. }) = p;
					local (n, n) = t;
					local Pair({ .. }) = q;
					local (m, k) = p;
					local Pair(r, s) = p;
				}
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::DuplicateRestPattern,
			DiagnosticCode::MissingStructFields,
			DiagnosticCode::UnknownStructField,
			DiagnosticCode::DuplicatePatternBinding,
			DiagnosticCode::TupleStructBracePattern,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
		]);
		case.diagnostics().assert_error_saying(
			"this pattern has 3 elements but the tuple has 2",
		);
		case.diagnostics()
			.assert_error_saying("pattern does not mention field `y`");
	}

	#[test]
	fn a_local_pattern_cannot_test_a_value() {
		test_case!(
			case = indoc! {"
				func f(t: (u32, u32)) -> u32 {
					local (a, case 0) = t;
					a
				}
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::RefutablePatternInLocal]);
		assert_eq!(
			case.shape("f"),
			"(block (local (tuple a#1 error) t#0) => a#1)"
		);
	}

	#[test]
	fn a_match_checks_each_arm_against_the_scrutinee() {
		test_case!(
			case = indoc! {"
				func sign(x: i32) -> i32 {
					match x {
						case 0 -> { 0 },
						case -1 | -128 -> { 1 },
						n -> { n },
					}
				}
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("sign"),
			"(block => (match x#0 \
			 (0 => (block => 0)) \
			 ((| -1 -128) => (block => 1)) \
			 (n#1 => (block => n#1))))"
		);
		assert_eq!(case.body_type("sign"), "i32");
	}

	#[test]
	fn a_match_compares_with_constants_and_destructures() {
		test_case!(
			case = indoc! {"
				enum Dir: u8 { North = 0, South = 1 }
				const LIMIT: u8 = 10;
				struct P(x: u8, d: Dir);
				trait Lim { const MAX: u8; }
				struct S();
				impl S { const ZERO: u8 = 0; }
				func f<T: Lim>(p: P) -> u8 {
					match p {
						case P(0, Dir::North) -> { 1 },
						case P(LIMIT, local d) -> { 2 },
						P(x, case Dir::South) -> { x },
						case P(S::ZERO | T::MAX, _) -> { 3 },
						_ -> { 4 },
					}
				}
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block => (match p#0 \
			 ((P 0 North) => (block => 1)) \
			 ((P LIMIT d#1) => (block => 2)) \
			 ((P x#2 South) => (block => x#2)) \
			 ((P (| ZERO (abstract MAX<T>)) _) => (block => 3)) \
			 (_ => (block => 4))))"
		);
	}

	#[test]
	fn a_value_in_a_pattern_is_a_constant_of_the_matched_type() {
		test_case!(
			case = indoc! {"
				const C: u8 = 1;
				func g() {}
				func f(x: u8, b: bool) {
					local y: u8 = 1;
					match x { case y -> {}, _ -> {} }
					match x { case g -> {}, _ -> {} }
					match x { case 300 -> {}, case -1 -> {}, _ -> {} }
					match x { case true -> {}, _ -> {} }
					match b { case C -> {}, _ -> {} }
					match x { case 1 | local z -> {}, _ -> {} }
				}
			"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UndeclaredIdentifier,
			DiagnosticCode::InvalidMatchPattern,
			DiagnosticCode::IntegerLiteralOutOfRange,
			DiagnosticCode::IntegerLiteralOutOfRange,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::InvalidMatchPattern,
		]);
		case.diagnostics().assert_error_saying(
			"`y` is a local; a pattern compares with constants, and `local y` \
			 would bind a new one",
		);
	}

	#[test]
	fn match_arms_share_a_type() {
		test_case!(
			case = indoc! {"
				func f(x: u8) -> u64 { match x { case 0 -> { 1 }, _ -> { 2 } } }
				func g(x: u8) -> u8 {
					match x { case 0 -> { return 0 }, _ -> { x } }
				}
				func h(x: u8) { local v = match x { case 0 -> { 1 }, _ -> { true } }; }
			"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnableToCoerce]);
		assert_eq!(case.body_type("f"), "u64");
		assert_eq!(case.body_type("g"), "u8");
	}

	#[test]
	fn self_destructures_the_struct_its_impl_is_for() {
		test_case!(
			case = indoc! {"
				struct W(x: u32, y: u32);
				impl W {
					func first(self) -> u32 { local Self(x, ..) = self; x }
				}
			"}
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.member_shape("first"),
			"(block (local (W x#1 _) self#0) => x#1)"
		);
	}
}
