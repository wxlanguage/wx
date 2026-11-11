//! Expression checking: lowers written expressions into a `Body`, with every
//! node typed. One checker for every expression, whatever owns it: a
//! constant's or global's initializer, or a function's block.
//!
//! Blocks, locals and control flow are in `blocks`, patterns in `patterns`,
//! places and assignment in `places`, function calls in `calls`. A form the
//! checker does not cover yet is reported once (`UnsupportedExpression`) and
//! checked as an error node.
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
mod decide;
mod exhaustiveness;
mod members;
mod patterns;
mod places;

use calls::{CallTarget, Callee, GivenArgument};
use members::{MemberPath, RootedPath};

use rustc_hash::FxHashMap;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::body::{
	Body, BodyOwner, ElementOrder, ExprIdx, ExprKind, ExprObligation,
	ExprRange, LocalIdx, Obligations, Scope, ScopeIdx, ScopeKind,
};
use super::bounds::AssumptionEnvIdx;
use super::decls::{
	BindingTarget, ConstIdx, DeclKey, DeclKind, FunctionIdx, MemberKind,
	StructIdx, Tier, Visibility,
};
use super::imports::report_private_identifier;
use super::literals::{
	CharLiteralError, CharMiss, ConcreteType, FloatMiss, Integer, IntegerMiss,
	parse_char_literal, unescape_string_literal,
};
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::obligations::BoundRequirements;
use super::operators::{
	OperatorMethod, is_comparison, is_primitive_binary, is_primitive_unary,
};
use super::paths::{PathResolver, PathWalk};
use super::resolutions::Referent;
use super::signatures::{
	InferPolicy, LexicalScope, Semantics, SemanticsBuilder,
};
use super::solver::{NormalizationDepth, RewriteFlags, SolverError};
use super::types::{
	GenericArgs, GenericEnvIdx, GenericEnvOwner, ImplKind, Substitution, Type,
	TypeIndex,
};
use crate::ast::{
	self, BinaryOp, Keyword, Ownership, Separated, Spanned, StringInterner,
	UnaryOp,
};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::vfs::FileId;
use members::Expected;

/// A body in the scope it is written in: what is valid on it whatever wrote
/// it. It normalizes, compares, reports, checks usefulness and decides what
/// building left open, and knows nothing about syntax.
pub(super) struct BodyContext<'a> {
	sema: &'a mut Semantics,
	strings: &'a StringInterner,
	body: &'a mut Body,
	/// Where the expressions are written. Its type scope is the root for a
	/// free constant, the impl's or trait's `Self` scope for an associated one,
	/// the function's own for a function's block.
	scope: LexicalScope,
}

/// Builds the expressions of one definition into a `Body` from its written
/// syntax. What is valid on the body whatever wrote it is its `BodyContext`'s.
pub(super) struct BodyBuilder<'a, 'ast> {
	sema: &'a mut Semantics,
	/// What lowers the written types and paths the body names.
	builder: &'a mut SemanticsBuilder<'ast>,
	body: Body,
	/// What lowering the body's types and expressions left to decide.
	obligations: Obligations,
	/// Where the expressions are written (`BodyContext::scope`).
	scope: LexicalScope,
	owner: BodyOwner,
	/// The block scope being checked.
	current: ScopeIdx,
	/// The locals each scope declares, by name. A name is looked up in the
	/// current scope, then in each enclosing one; a later declaration of the
	/// same name in one scope replaces the entry, which shadows the earlier.
	lookup: FxHashMap<(ScopeIdx, SymbolU32), LocalIdx>,
	/// What each scope's value is checked against, index-aligned with the
	/// body's scopes.
	scope_types: Vec<ScopeType>,
}

/// Whether a local a name finds can be used where the name is written.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LocalReach {
	Visible,
	/// Declared outside the static data the name is written in.
	BehindStatic,
}

/// Whether two types are equal once some facts have rewritten them.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TypeEquality {
	Equal,
	Diff,
	/// A constant left as written decides it.
	NeedsValues,
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

impl<'a> BodyContext<'a> {
	pub(super) fn new(
		sema: &'a mut Semantics,
		strings: &'a StringInterner,
		body: &'a mut Body,
		scope: LexicalScope,
	) -> Self {
		Self {
			sema,
			strings,
			body,
			scope,
		}
	}

	/// What a type means in this body's scope: comparisons and literal coercion
	/// work on normalized types.
	fn normalized(&mut self, ty: TypeIndex) -> TypeIndex {
		self.normalized_in(ty, self.scope.assumption_env)
	}

	/// What a type means in `scope`. A projection that does not normalize stays
	/// as written; whoever wrote it has reported why.
	fn normalized_in(
		&mut self,
		ty: TypeIndex,
		scope: AssumptionEnvIdx,
	) -> TypeIndex {
		match self.sema.normalize(
			&self.strings,
			scope,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::EQUALITIES | RewriteFlags::DEFINITIONS,
		) {
			Ok(normalized) => normalized,
			Err(_) => ty,
		}
	}

	/// `ty` in this body's scope, rewritten by `facts`. A normalization that
	/// diverges is reported here, at `site`, once; `Err` means the failure is
	/// explained (here, or by its owner) and the caller only recovers.
	fn normalize_at(
		&mut self,
		ty: TypeIndex,
		facts: RewriteFlags,
		site: TextSpan,
	) -> Result<TypeIndex, ()> {
		let site = SourceSpan::new(self.scope.file_id, site);
		match self.sema.normalize(
			&self.strings,
			self.scope.assumption_env,
			ty,
			NormalizationDepth::Deep,
			facts,
		) {
			Ok(ty) => Ok(ty),
			// Its owner reported it.
			Err(SolverError::Poisoned) => Err(()),
			Err(SolverError::Overflow) => {
				self.sema
					.diagnostics
					.push(self.sema.overflow_diagnostic(site));
				Err(())
			}
			Err(SolverError::Cycle(cycle)) => {
				let diagnostic =
					self.sema.cycle_diagnostic(&self.strings, &cycle, site);
				self.sema.diagnostics.push(diagnostic);
				Err(())
			}
			Err(SolverError::Pending) => {
				unreachable!("every signature is final when bodies are checked")
			}
		}
	}

	/// Whether two types are equal once `facts` have rewritten both. `Err`
	/// means one does not normalize and that is explained: by its owner, or
	/// here, at `site`.
	fn equality(
		&mut self,
		expected: TypeIndex,
		actual: TypeIndex,
		facts: RewriteFlags,
		site: TextSpan,
	) -> Result<TypeEquality, ()> {
		if expected == actual {
			return Ok(TypeEquality::Equal);
		}
		if !self.sema.types.has_projection(expected)
			&& !self.sema.types.has_projection(actual)
		{
			return Ok(TypeEquality::Diff);
		}
		let expected = self.normalize_at(expected, facts, site)?;
		let actual = self.normalize_at(actual, facts, site)?;
		Ok(if expected == actual {
			TypeEquality::Equal
		} else if !facts.contains(RewriteFlags::VALUES)
			&& (self.sema.types.has_const(expected)
				|| self.sema.types.has_const(actual))
		{
			TypeEquality::NeedsValues
		} else {
			TypeEquality::Diff
		})
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
		let ty = self
			.sema
			.types
			.list(self.sema.structs[usize::from(struct_index)].field_types)[field];
		let ty = self.sema.types.substitute(
			ty,
			Substitution {
				envs: &self.sema.generic_envs,
				env: self.sema.structs[usize::from(struct_index)].type_params,
				args,
			},
		);
		let ty = self.normalized(ty);
		self.sema.types.collapse_error(ty)
	}

	/// What a string or array literal can become, read off `target`: a
	/// shared pointer to an array or a slice, or an array in no memory (a
	/// constant's type).
	fn static_target(&self, target: TypeIndex) -> Option<StaticTarget> {
		let (to, memory) = match *self.sema.types.resolve(target) {
			Type::Pointer {
				to,
				memory,
				ownership: Ownership::Shared,
			} => (to, Some(memory)),
			_ => (target, None),
		};
		match *self.sema.types.resolve(to) {
			Type::Array { of, length } => Some(StaticTarget {
				of,
				memory,
				length: Some(length),
			}),
			Type::Slice { of } if memory.is_some() => Some(StaticTarget {
				of,
				memory,
				length: None,
			}),
			_ => None,
		}
	}

	fn source_span(&self, expr: ExprIdx) -> SourceSpan {
		SourceSpan::new(self.scope.file_id, self.body.span(expr))
	}

	/// Reports at `expr` and leaves it at `ERROR`, so nothing reports it again.
	fn push_error(
		&mut self,
		code: DiagnosticCode,
		message: String,
		expr: ExprIdx,
	) {
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(code.code())
				.with_message(message)
				.with_label(self.source_span(expr).primary_label()),
		);
		self.body.set_ty(expr, TypeIndex::ERROR);
	}

	/// Reports `diagnostic` about `expr` and leaves `expr` at `ERROR`, so
	/// nothing reports it again.
	fn reject(&mut self, expr: ExprIdx, diagnostic: Diagnostic<FileId>) {
		self.sema.diagnostics.push(diagnostic);
		self.body.set_ty(expr, TypeIndex::ERROR);
	}

	fn report_mismatch(&mut self, expr: ExprIdx, expected: TypeIndex) {
		let actual = self.body.ty(expr);
		let diagnostic = self.report_type_mismatch(expected, actual, expr);
		self.sema.diagnostics.push(diagnostic);
		// Reported: nothing reads a value from it, or reports it again.
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

	fn report_unable_to_coerce(
		&self,
		expr: ExprIdx,
		target: TypeIndex,
	) -> Diagnostic<FileId> {
		Diagnostic::error()
			.with_code(DiagnosticCode::UnableToCoerce.code())
			.with_message(format!(
				"unable to coerce to type `{}`",
				self.sema.type_formatter(&self.strings).display_type(target)
			))
			.with_label(self.source_span(expr).primary_label())
	}

	fn mismatch_at(
		&self,
		expected: TypeIndex,
		actual: TypeIndex,
		span: TextSpan,
	) -> Diagnostic<FileId> {
		let formatter = self.sema.type_formatter(&self.strings);
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
}

impl<'a, 'ast> BodyBuilder<'a, 'ast> {
	pub(super) fn new(
		sema: &'a mut Semantics,
		builder: &'a mut SemanticsBuilder<'ast>,
		scope: LexicalScope,
		owner: BodyOwner,
	) -> Self {
		Self {
			sema,
			builder,
			body: Body::default(),
			obligations: Obligations::default(),
			scope,
			owner,
			current: ScopeIdx::ROOT,
			lookup: FxHashMap::default(),
			scope_types: Vec::new(),
		}
	}

	/// Builds the parts of a literal (its elements, a repeat's value) in a
	/// scope of their own, which keeps the locals around it out
	/// of reach.
	fn static_scope<R>(
		&mut self,
		span: TextSpan,
		build: impl FnOnce(&mut Self) -> R,
	) -> R {
		let scope =
			self.enter_scope(ScopeKind::Static, None, span, TypeIndex::INFER);
		let built = build(self);
		self.leave_scope(scope);
		built
	}

	/// The body built so far, in its scope.
	fn context(&mut self) -> BodyContext<'_> {
		BodyContext::new(
			self.sema,
			self.builder.strings,
			&mut self.body,
			self.scope,
		)
	}

	/// Checks `expr` as the whole body, against `expected`.
	pub(super) fn check_body(
		mut self,
		expr: &Spanned<ast::Expression>,
		expected: TypeIndex,
	) -> (Body, Obligations) {
		let expected = self.context().normalized(expected);
		self.enter_root(expr.span, expected);
		self.check(expr, expected);
		(self.body, self.obligations)
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
	) -> (Body, Obligations) {
		let span = variant.name.span;
		self.enter_root(span, repr);
		// A missing or non-integer repr was reported on the enum; checking each
		// value against it would only repeat that.
		if repr == TypeIndex::ERROR {
			self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			return (self.body, self.obligations);
		}
		match (variant.value.as_deref(), previous) {
			(Some(value), _) => self.check(value, repr),
			(None, Some(previous)) => {
				self.body
					.push(ExprKind::NextDiscriminant(previous), repr, span)
			}
			(None, None) => {
				self.sema.diagnostics.push(
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
		(self.body, self.obligations)
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
		if self.sema.types.needs_context(actual) {
			self.coerce(expr, expected);
		} else if actual != TypeIndex::ERROR
			&& actual != TypeIndex::NEVER
			&& actual != expected
		{
			let span = self.body.span(expr);
			match self.context().equality(
				expected,
				actual,
				RewriteFlags::EQUALITIES | RewriteFlags::DEFINITIONS,
				span,
			) {
				Ok(TypeEquality::Equal) => return expr,
				// A constant left as written is compared once it has a
				// value.
				Ok(TypeEquality::NeedsValues) => {
					self.obligations
						.exprs
						.push(ExprObligation::Equal { expr, expected });
					return expr;
				}
				Ok(TypeEquality::Diff) => {
					self.context().report_mismatch(expr, expected)
				}
				// Explained: nothing reads a value from it, and no mismatch
				// on top.
				Err(()) => self.body.set_ty(expr, TypeIndex::ERROR),
			}
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
			ast::Expression::Int { value } => self.body.push(
				ExprKind::Int(*value),
				TypeIndex::INTEGER_LITERAL,
				span,
			),
			// The value is read from the source once the width is known.
			ast::Expression::Float => self.body.push(
				ExprKind::Float(0.0),
				TypeIndex::FLOAT_LITERAL,
				span,
			),
			ast::Expression::Char => self.build_char(span),
			ast::Expression::Unary { operator, operand } => {
				self.build_unary(*operator, operand, expected, span)
			}
			ast::Expression::Binary {
				left,
				operator,
				right,
			} => self.build_binary(*operator, left, right, expected, span),
			ast::Expression::Path(segments) => {
				self.build_path(segments, expected, span)
			}
			ast::Expression::Call { callee, arguments } => self.build_call(
				callee,
				Arguments::Positional(arguments),
				Expected::Type(expected),
				span,
			),
			ast::Expression::NamedCall { callee, arguments } => self
				.build_call(
					callee,
					Arguments::Named(arguments),
					Expected::Type(expected),
					span,
				),
			ast::Expression::Tuple { elements } => {
				self.build_tuple(elements, expected, span)
			}
			ast::Expression::Block { label, statements } => {
				let label = label.map(|name| {
					self.body.push_label(super::body::Label { name })
				});
				self.build_block(statements, expected, label, span)
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
				span,
			),
			ast::Expression::Loop { label, block } => {
				let label = label.map(|name| {
					self.body.push_label(super::body::Label { name })
				});
				self.build_loop(block, expected, label, span)
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
			| ast::Expression::ObjectAccess { .. }
			| ast::Expression::Index { .. } => self.build_read(expr),
			ast::Expression::AddressOf { value } => {
				self.build_address_of(value, span)
			}
			ast::Expression::Placeholder => {
				self.sema.diagnostics.push(
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
			ast::Expression::Ascription { value, ty } => {
				self.build_ascription(value, ty)
			}
			ast::Expression::MethodCall(call) => self.build_method_call(
				&call.object,
				&call.method,
				Arguments::Positional(&call.arguments),
				Expected::Type(expected),
				span,
			),
			ast::Expression::NamedMethodCall(call) => self.build_method_call(
				&call.object,
				&call.method,
				Arguments::Named(&call.arguments),
				Expected::Type(expected),
				span,
			),
			ast::Expression::Match { scrutinee, arms } => {
				self.build_match(scrutinee, arms, expected, span)
			}
			ast::Expression::String => self.build_string(span),
			ast::Expression::QualifiedPath { .. }
			| ast::Expression::Grouped { .. } => {
				let rooted = RootedPath::of_expression(&expr.inner).unwrap();
				match self.resolve_rooted_path(rooted, span) {
					Ok(path) => self.build_member_value(path, expected, span),
					Err(error) => error,
				}
			}
			ast::Expression::ArrayList { elements } => {
				self.build_array(elements, expected, span)
			}
			ast::Expression::ArrayRepeat { value, count } => {
				self.build_array_repeat(value, count, expected, span)
			}
			ast::Expression::SliceRange { .. } => {
				self.unsupported(span, "a slice range")
			}
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
		let at = self.context().source_span(value);
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypeAnnotationRequired.code())
				.with_message("type annotation required")
				.with_label(
					at.primary_label()
						.with_message("the type of this value is not known"),
				),
		);
		self.body.set_ty(value, TypeIndex::ERROR);
	}

	fn report_unsupported(&mut self, span: TextSpan, what: &str) {
		self.sema.diagnostics.push(
			Diagnostic::bug()
				.with_code(DiagnosticCode::UnsupportedExpression.code())
				.with_message(format!("checking {what} is not supported yet"))
				.with_label(Label::primary(self.scope.file_id, span)),
		);
	}

	/// A tuple, each element built with the expected type's element at its
	/// position when the expected type is a tuple as long. Its type is its
	/// elements': one with an untyped literal in it is untyped, and takes its
	/// type from context later, as a literal does (`coerce`). A tuple of one
	/// is its element: `(x,)` is `(x)`.
	fn build_tuple(
		&mut self,
		elements: &[Separated<Spanned<ast::Expression>>],
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		if let [element] = elements {
			return self.build(&element.inner, expected);
		}
		let hints = match *self.sema.types.resolve(expected) {
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
				Some(hints) => self.sema.types.list(hints)[at],
				None => TypeIndex::INFER,
			};
			let value = self.build(&element.inner, hint);
			values.push(value);
			types.push(self.body.ty(value));
		}
		let ty = self.sema.types.intern_tuple(&types);
		let ty = self.sema.types.collapse_error(ty);
		let elements = self.body.push_args(values);
		let kind = ExprKind::Tuple {
			elements,
			order: ElementOrder::InOrder,
		};
		self.body.push(kind, ty, span)
	}

	/// An array literal is an array, data in no memory until its context
	/// places it (`coerce_static`). Its elements are built with the expected
	/// element type as their hint; its element type is the first typed
	/// element's, or the first one's (`[{integer}; 3]`), which placing checks
	/// each element against.
	fn build_array(
		&mut self,
		elements: &[Spanned<ast::Expression>],
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let hint = self.array_element_hint(expected);
		let values: Vec<ExprIdx> = self.static_scope(span, |this| {
			(elements.iter())
				.map(|element| this.build(element, hint))
				.collect()
		});
		let of = values
			.iter()
			.map(|&value| self.body.ty(value))
			.find(|&ty| !self.sema.types.has_literal(ty))
			.or_else(|| values.first().map(|&value| self.body.ty(value)))
			.unwrap_or(hint);
		let bits = u64::try_from(values.len()).unwrap();
		let length = self.sema.types.intern(Type::Value { bits });
		let ty = self.sema.types.intern(Type::Array { of, length });
		let elements = self.body.push_args(values);
		let expr = self.body.push(ExprKind::Array { elements }, ty, span);
		self.body.push_static(expr);
		expr
	}

	/// A repeat is an array as an array literal is, its length the count:
	/// an integer literal, a constant, or `_` for the length of the array its
	/// context gives. Placed in a memory, the count is checked against the
	/// memory's `Size`.
	fn build_array_repeat(
		&mut self,
		value: &Spanned<ast::Expression>,
		count: &Spanned<ast::ConstArgument>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let hint = self.array_element_hint(expected);
		let value = self.static_scope(span, |this| this.build(value, hint));
		// The count is a length, which `repeat_length` holds to a literal or
		// a constant.
		let count = self.build_repeat_count(count);
		let of = self.body.ty(value);
		let length = match count {
			None => TypeIndex::INFER,
			Some(count) => self.repeat_length(count),
		};
		let ty = if length == TypeIndex::ERROR {
			TypeIndex::ERROR
		} else {
			self.sema.types.intern(Type::Array { of, length })
		};
		let expr =
			self.body
				.push(ExprKind::ArrayRepeat { value, count }, ty, span);
		self.body.push_static(expr);
		expr
	}

	/// A repeat's count as written: an integer literal or a constant's path,
	/// `None` for `_`.
	fn build_repeat_count(
		&mut self,
		count: &Spanned<ast::ConstArgument>,
	) -> Option<ExprIdx> {
		match &count.inner {
			ast::ConstArgument::Infer => None,
			ast::ConstArgument::Literal(ast::Literal::Int(value)) => {
				Some(self.body.push(
					ExprKind::Int(*value),
					TypeIndex::INTEGER_LITERAL,
					count.span,
				))
			}
			ast::ConstArgument::Literal(_) => {
				self.sema.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::TypeMistmatch.code())
						.with_message("an array's length is an integer")
						.with_label(
							Label::primary(self.scope.file_id, count.span)
								.with_message("not an integer"),
						),
				);
				Some(self.body.push(
					ExprKind::Error,
					TypeIndex::ERROR,
					count.span,
				))
			}
			ast::ConstArgument::Path(segments) => {
				Some(self.build_path(segments, TypeIndex::INFER, count.span))
			}
			ast::ConstArgument::QualifiedPath { .. }
			| ast::ConstArgument::Grouped { .. } => {
				let rooted = RootedPath::of_constant(&count.inner).unwrap();
				Some(match self.resolve_rooted_path(rooted, count.span) {
					Ok(path) => self.build_member_value(
						path,
						TypeIndex::INFER,
						count.span,
					),
					Err(error) => error,
				})
			}
		}
	}

	/// A repeat's `count` as a length: a `Value`, or the `Const` it names.
	/// `ERROR` when it is neither (reported).
	fn repeat_length(&mut self, count: ExprIdx) -> TypeIndex {
		match self.body.kind(count) {
			_ if self.body.ty(count) == TypeIndex::ERROR => TypeIndex::ERROR,
			ExprKind::Int(bits) => self.sema.types.intern(Type::Value { bits }),
			ExprKind::Const {
				constant,
				type_args,
			} if type_args.is_empty() => self.sema.types.intern_const(constant, &[]),
			// An impl's constant may depend on the impl's arguments, which
			// evaluation does not substitute (yet).
			ExprKind::Const { .. } | ExprKind::AbstractConst { .. } => {
				let span = self.body.span(count);
				self.report_unsupported(
					span,
					"a repeat count of a generic constant",
				);
				TypeIndex::ERROR
			}
			_ => {
				self.context().push_error(
					DiagnosticCode::ArrayRepeatCountNotConst,
					"an array's length is a literal or a constant".to_string(),
					count,
				);
				TypeIndex::ERROR
			}
		}
	}

	/// The element type an expected array or slice, or a pointer to one,
	/// gives its literal's elements; no constraint otherwise.
	fn array_element_hint(&self, expected: TypeIndex) -> TypeIndex {
		let expected = match *self.sema.types.resolve(expected) {
			Type::Pointer { to, .. } => to,
			_ => expected,
		};
		match *self.sema.types.resolve(expected) {
			Type::Array { of, .. } | Type::Slice { of } => of,
			_ => TypeIndex::INFER,
		}
	}

	/// A string literal is the byte array of its length (`[u8; 5]`), data in
	/// no memory until its context places it (`coerce_static`).
	fn build_string(&mut self, span: TextSpan) -> ExprIdx {
		let source =
			&self.builder.files.get(self.scope.file_id).unwrap().source;
		match unescape_string_literal(span.extract_str(source)) {
			Ok(contents) => {
				let bits = u64::try_from(contents.len()).unwrap();
				let symbol = self.builder.strings.get_or_intern(contents);
				let length = self.sema.types.intern(Type::Value { bits });
				let ty = self.sema.types.intern(Type::Array {
					of: TypeIndex::U8,
					length,
				});
				let expr = self.body.push(ExprKind::String(symbol), ty, span);
				self.body.push_static(expr);
				expr
			}
			Err(error) => {
				self.sema.diagnostics.push(
					error.diagnostic(SourceSpan::new(self.scope.file_id, span)),
				);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
		}
	}

	fn build_char(&mut self, span: TextSpan) -> ExprIdx {
		let source =
			&self.builder.files.get(self.scope.file_id).unwrap().source;
		match parse_char_literal(span.extract_str(source)) {
			Ok(value) => self.body.push(
				ExprKind::Char(value),
				TypeIndex::CHAR_LITERAL,
				span,
			),
			Err(error) => {
				let message = match error {
					CharLiteralError::Empty => "empty character literal",
					CharLiteralError::TooLong => {
						"character literal may only contain one codepoint"
					}
				};
				self.sema.diagnostics.push(
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
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		if let [segment] = segments
			&& segment.type_args.is_empty()
			&& let Some((local, reach)) = self.lookup_local(segment.ident.inner)
		{
			self.record_local(local, segment.ident.span);
			if reach == LocalReach::BehindStatic {
				self.report_local_in_static_data(span);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
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
				return self.build_member_value(path, expected, span);
			}
			Err(error) => return error,
		};
		let Some(key) = walk.target.decl_key() else {
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		let kind = key.symbol_kind(&self.sema.decls);
		// A bare struct name is an error of its own, whoever may construct it.
		if let BindingTarget::Inaccessible(_) = walk.target
			&& !matches!(kind, DeclKind::Struct(_))
		{
			let segment = &segments[walk.stopped_at as usize];
			self.sema.diagnostics.push(report_private_identifier(
				&self.sema.decls.namespaces,
				self.builder.strings,
				segment.ident.inner,
				SourceSpan::new(self.scope.file_id, segment.ident.span),
				Some(key),
			));
		}
		match kind {
			DeclKind::Const(const_index)
			| DeclKind::EnumVariant(const_index) => {
				let signature = &self.sema.constants[usize::from(const_index)];
				let ty = signature.ty;
				let env = self.sema.assumption_envs.of_frame(signature.env);
				let ty = self.context().normalized_in(ty, env);
				let kind = ExprKind::Const {
					constant: const_index,
					type_args: GenericArgs::EMPTY,
				};
				self.body.push(kind, ty, span)
			}
			DeclKind::Struct(struct_index) => {
				let name =
					self.sema.decls.structs[usize::from(struct_index)].name;
				self.report_struct_used_as_value(name.inner, span);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
			DeclKind::Function(function_index) => self.build_function_value(
				Callee::new(self.sema, function_index, &[], 0),
				segments.last().unwrap(),
				expected,
				span,
			),
			// A global's name is its handle, of its own nominal type: its value
			// is read with `Global::get` and written with `GlobalMut::set`.
			DeclKind::Global(global_index) => {
				let ty = self.sema.types.intern(Type::Global { global_index });
				self.body.push(ExprKind::Global(global_index), ty, span)
			}
			// A memory's name is its handle, as a global's is.
			DeclKind::Memory(memory_index) => {
				let ty = self.sema.types.intern(Type::Memory { memory_index });
				self.body.push(ExprKind::Memory(memory_index), ty, span)
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
				|| self
					.sema
					.generic_envs
					.resolve(self.scope.generic_env, first)
					.is_some())
		{
			let receiver = self.builder.resolve_type_path(
				self.sema,
				&mut self.obligations.types,
				self.scope,
				prefix,
				InferPolicy::Allow,
			);
			return Ok(ValuePath::Member(MemberPath::new(receiver, member)));
		}
		let walk = PathResolver::new(
			&mut self.sema.diagnostics,
			&mut self.sema.resolutions,
			self.builder.strings,
			&self.sema.decls,
		)
		.walk_path(
			self.scope.file_id,
			self.scope.namespace,
			segments,
			Tier::Value,
		);
		let Some(key) = walk.target.decl_key() else {
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
			&& let DeclKind::Struct(struct_index) =
				key.symbol_kind(&self.sema.decls)
		{
			let params =
				self.sema.structs[usize::from(struct_index)].type_params;
			let count = self.sema.generic_envs.param_names(params).len();
			if count > 0 {
				if stop + 1 != prefix.len() {
					return Err(self.unsupported(
						span,
						"a path past a generic type without its type arguments",
					));
				}
				let receiver = self.sema.types.intern_struct(
					struct_index,
					&vec![TypeIndex::INFER; count],
				);
				return Ok(ValuePath::Member(MemberPath::new(
					receiver, member,
				)));
			}
		}
		let head = self.builder.resolve_named_type(
			self.sema,
			&mut self.obligations.types,
			self.scope,
			key,
			stopped,
			InferPolicy::Allow,
		);
		let receiver = self.builder.resolve_type_member_path(
			self.sema,
			&mut self.obligations.types,
			self.scope,
			head,
			&prefix[stop + 1..],
			InferPolicy::Allow,
		);
		Ok(ValuePath::Member(MemberPath::new(receiver, member)))
	}

	/// The local `name` refers to from the current scope: declared in it or in
	/// a scope around it, and whether it lies past static data the name is
	/// written in.
	fn lookup_local(&self, name: SymbolU32) -> Option<(LocalIdx, LocalReach)> {
		let mut reach = LocalReach::Visible;
		let mut scope = Some(self.current);
		while let Some(at) = scope {
			if let Some(&local) = self.lookup.get(&(at, name)) {
				return Some((local, reach));
			}
			let scope_data = self.body.scope(at);
			if scope_data.kind == ScopeKind::Static {
				reach = LocalReach::BehindStatic;
			}
			scope = scope_data.parent;
		}
		None
	}

	fn record_local(&mut self, local: LocalIdx, span: TextSpan) {
		self.sema.resolutions.record(
			(SourceSpan::new(self.scope.file_id, span), Tier::Value),
			Referent::Local {
				owner: self.owner,
				local,
			},
		);
	}

	/// A call: of a function named by a path, the construction of a struct,
	/// or of any other value whose type is callable (`build_value_call`).
	/// As a method call's receiver, a function's call reads its expected
	/// type from the method.
	fn build_call(
		&mut self,
		callee: &Spanned<ast::Expression>,
		arguments: Arguments<'_>,
		expected: Expected,
		span: TextSpan,
	) -> ExprIdx {
		let segments = match &callee.inner {
			ast::Expression::Path(segments) => segments,
			ast::Expression::QualifiedPath { .. }
			| ast::Expression::Grouped { .. } => {
				let rooted = RootedPath::of_expression(&callee.inner).unwrap();
				return match self.resolve_rooted_path(rooted, callee.span) {
					Ok(path) => self.build_member_call(
						path,
						callee.span,
						arguments,
						expected,
						span,
					),
					Err(error) => {
						self.build_unchecked_arguments(arguments);
						error
					}
				};
			}
			_ => {
				let callee = self.build(callee, TypeIndex::INFER);
				return self.build_value_call(callee, arguments, span);
			}
		};
		if let [segment] = &**segments
			&& segment.type_args.is_empty()
			&& self.lookup_local(segment.ident.inner).is_some()
		{
			let callee =
				self.build_path(segments, TypeIndex::INFER, callee.span);
			return self.build_value_call(callee, arguments, span);
		}
		// `Self(..)` constructs the struct the impl around it is for, with
		// that target's arguments.
		if let [segment] = &**segments
			&& segment.ident.inner == Keyword::SelfPascal.symbol()
		{
			let Some((struct_index, type_args)) =
				self.impl_self_struct(segment)
			else {
				self.build_unchecked_arguments(arguments);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			};
			if !self.constructor_accessible(struct_index) {
				let diagnostic = self.report_private_constructor(
					struct_index,
					None,
					segment,
				);
				self.sema.diagnostics.push(diagnostic);
			}
			return self.build_construction(
				struct_index,
				type_args,
				segment,
				arguments,
				expected.ty(),
				span,
			);
		}
		let walk = match self.resolve_value_path(segments, span) {
			Ok(ValuePath::Item(walk)) => walk,
			Ok(ValuePath::Member(path)) => {
				return self.build_member_call(
					path,
					callee.span,
					arguments,
					expected,
					span,
				);
			}
			Err(error) => {
				self.build_unchecked_arguments(arguments);
				return error;
			}
		};
		let Some(key) = walk.target.decl_key() else {
			self.build_unchecked_arguments(arguments);
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		};
		let kind = key.symbol_kind(&self.sema.decls);
		// Any other item is called as the value it names.
		if !matches!(kind, DeclKind::Struct(_) | DeclKind::Function(_)) {
			let callee =
				self.build_path(segments, TypeIndex::INFER, callee.span);
			return self.build_value_call(callee, arguments, span);
		}
		let DeclKind::Struct(struct_index) = kind else {
			if let BindingTarget::Inaccessible(_) = walk.target {
				let segment = &segments[walk.stopped_at as usize];
				self.sema.diagnostics.push(report_private_identifier(
					&self.sema.decls.namespaces,
					self.builder.strings,
					segment.ident.inner,
					SourceSpan::new(self.scope.file_id, segment.ident.span),
					Some(key),
				));
			}
			let DeclKind::Function(function_index) = kind else {
				unreachable!("any other item is called as a value")
			};
			return self.build_function_call(
				Callee::new(self.sema, function_index, &[], 0),
				segments.last().unwrap(),
				None,
				arguments,
				expected,
				span,
			);
		};
		let segment = segments.last().unwrap();
		if let BindingTarget::Inaccessible(key) = walk.target {
			let diagnostic = self.report_private_constructor(
				struct_index,
				Some(key),
				segment,
			);
			self.sema.diagnostics.push(diagnostic);
		}
		// The struct's type arguments are learned within this call: from what
		// is written on its name, the expected type, and then the fields.
		let type_args =
			self.struct_type_args(struct_index, segment, expected.ty());
		self.build_construction(
			struct_index,
			type_args,
			segment,
			arguments,
			expected.ty(),
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
		let target = CallTarget::struct_constructor(self.sema, struct_index);
		let mut given = Vec::new();
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
				self.sema.types.has_error(self.body.ty(argument.value))
			});
		self.settle_uninferred(
			target.generic_env,
			segment.ident.span,
			already_reported,
			&mut type_args,
		);
		self.expect_arguments(&target, &type_args, &given);
		let args = self.use_args(&target, segment, &type_args, &given);
		self.check_use_bounds(&target, 0, segment, args);
		let fields = self
			.arguments_value(&target, &type_args, &given, 0, reported, span);
		let ty = self.sema.types.intern_struct(struct_index, &type_args);
		let ty = self.sema.types.collapse_error(ty);
		// Fields need nothing; the value made of them does.
		let ty = self.require_stack_value(ty, span);
		self.body.push(
			ExprKind::StructConstructor {
				struct_index,
				fields,
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
		let params_env =
			self.sema.structs[usize::from(struct_index)].type_params;
		let count = self.sema.generic_envs.param_names(params_env).len();
		let mut type_args = vec![TypeIndex::INFER; count].into_boxed_slice();
		self.write_type_args(
			segment,
			params_env,
			GenericEnvOwner::Struct(struct_index),
			&mut type_args,
		);
		if expected == TypeIndex::INFER {
			return type_args;
		}
		// A disagreement teaches nothing: the construction's own type is held
		// to the expected one where the call is checked.
		let expected = self.context().normalized(expected);
		if let Type::Struct {
			struct_index: hinted,
			type_args: hints,
		} = *self.sema.types.resolve(expected)
			&& hinted == struct_index
		{
			for at in 0..count {
				let hint = self.sema.types.list(hints)[at];
				if let Some(met) = self.sema.types.meet(type_args[at], hint) {
					type_args[at] = met;
				}
			}
		}
		type_args
	}

	/// Writes the type arguments written on `segment` for the parameters of
	/// `params_env` into their slots of `type_args`, the flat list of its
	/// chain. A `_` written as a whole argument leaves its slot as it is (`_`
	/// inside one, `W<_>`, is written); a wrong count makes every slot of the
	/// frame `ERROR`.
	fn write_type_args(
		&mut self,
		segment: &ast::PathSegment,
		params_env: GenericEnvIdx,
		owner: GenericEnvOwner,
		type_args: &mut [TypeIndex],
	) {
		if segment.type_args.is_empty() {
			return;
		}
		let start = self.sema.generic_envs.parent_count(params_env);
		let len = self.sema.generic_envs.param_names(params_env).len();
		let slots = &mut type_args[start..start + len];
		// Every written argument is resolved, extra ones too, for their own
		// diagnostics.
		for (at, arg) in segment.type_args.iter().enumerate() {
			let ty = self.builder.resolve_type_argument(
				self.sema,
				&mut self.obligations.types,
				self.scope,
				arg,
				InferPolicy::Allow,
			);
			if let Some(slot) = slots.get_mut(at)
				&& ty != TypeIndex::INFER
			{
				*slot = ty;
			}
		}
		if !self.sema.check_type_arg_count(
			self.builder.strings,
			self.scope,
			segment,
			params_env,
			owner,
		) {
			slots.fill(TypeIndex::ERROR);
		}
	}

	/// The flat `type_args` of a use of `target` through `segment`, each
	/// with where it is given: the argument written on `segment`, else the
	/// value given for a parameter declared as that type parameter (a
	/// receiver for `Self`), else the name.
	fn use_args(
		&mut self,
		target: &CallTarget,
		segment: &ast::PathSegment,
		type_args: &[TypeIndex],
		given: &[GivenArgument],
	) -> GenericArgs {
		let env = target.generic_env;
		let written_from = (env != GenericEnvIdx::ROOT
			&& self.sema.generic_envs.owner(env) == target.kind.owner())
		.then(|| self.sema.generic_envs.parent_count(env));
		let identity = self.sema.generic_envs.identity_args(env);
		let body = &self.body;
		let span_of = |slot: usize| {
			if let Some(written) = written_from
				.and_then(|start| slot.checked_sub(start))
				.and_then(|at| segment.type_args.get(at))
			{
				return written.span();
			}
			given
				.iter()
				.find(|argument| argument.declared == identity[slot])
				.map_or(segment.ident.span, |argument| {
					body.span(argument.value)
				})
		};
		self.sema.generic_args.push(
			type_args
				.iter()
				.enumerate()
				.map(|(slot, &ty)| (ty, span_of(slot))),
		)
	}

	/// Proves, for a use's final `args`, the bounds of each frame on
	/// `target`'s chain after the first `proven` arguments: the selection
	/// proved those.
	fn check_use_bounds(
		&mut self,
		target: &CallTarget,
		proven: usize,
		segment: &ast::PathSegment,
		args: GenericArgs,
	) {
		let mut frame = target.generic_env;
		while frame != GenericEnvIdx::ROOT {
			let start = self.sema.generic_envs.parent_count(frame);
			if start >= proven {
				let own = self.sema.generic_envs.param_names(frame).len();
				self.sema.record_bounds_check(
					&mut self.obligations.types,
					self.scope.generic_env,
					BoundRequirements::Frame {
						env: frame,
						args: args.prefix(start + own),
					},
					SourceSpan::new(self.scope.file_id, segment.ident.span),
					self.sema.generic_envs.owner(frame),
				);
			}
			frame = self.sema.generic_envs.parent(frame).unwrap();
		}
	}

	/// Makes `ERROR` each argument in the flat `args` for `params_env`'s
	/// chain that is still not fully known (an `INFER` anywhere in it), and
	/// reports its parameter. Nothing is reported when `already_reported`
	/// (an `ERROR` expectation, an argument that failed, a mismatched item):
	/// whatever failed has said why, and may be why nothing was learned.
	fn settle_uninferred(
		&mut self,
		params_env: GenericEnvIdx,
		span: TextSpan,
		already_reported: bool,
		args: &mut [TypeIndex],
	) {
		for at in 0..args.len() {
			if !self.sema.types.has_infer(args[at]) {
				continue;
			}
			args[at] = TypeIndex::ERROR;
			if already_reported {
				continue;
			}
			let frame = self
				.sema
				.generic_envs
				.chain(params_env)
				.find(|&frame| self.sema.generic_envs.parent_count(frame) <= at)
				.unwrap();
			let index = at - self.sema.generic_envs.parent_count(frame);
			let name = self.sema.generic_envs.param_names(frame)[index].inner;
			let name = self.builder.strings.resolve(name).unwrap();
			self.sema.diagnostics.push(
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
			self.sema.resolve_impl_self(self.scope.generic_env)
		else {
			// A trait's `Self` is the type implementing it, which is not
			// known to be a struct; elsewhere `Self` names nothing.
			self.sema.diagnostics.push(
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
		self.sema.resolutions.record(
			(site, Tier::Value),
			match impl_kind {
				ImplKind::Inherent(index) => Referent::InherentImplSelf(index),
				ImplKind::Trait(index) => Referent::TraitImplSelf(index),
			},
		);
		if !segment.type_args.is_empty() {
			let diagnostic = self.sema.report_type_args_on_impl_self(
				self.builder.strings,
				self.scope.file_id,
				segment,
				impl_kind,
			);
			self.sema.diagnostics.push(diagnostic);
		}
		let Type::Struct {
			struct_index,
			type_args,
		} = *self.sema.types.resolve(target)
		else {
			if target != TypeIndex::ERROR {
				let target = self
					.sema
					.type_formatter(self.builder.strings)
					.display_type(target);
				self.sema.diagnostics.push(
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
		Some((struct_index, self.sema.types.list(type_args).into()))
	}

	/// Whether every field of `struct_index` is visible here, which is where
	/// its constructor is.
	fn constructor_accessible(&self, struct_index: StructIdx) -> bool {
		let decl = &self.sema.decls.structs[usize::from(struct_index)];
		decl.field_pub_spans.iter().all(|&pub_span| {
			self.sema.decls.namespaces.is_accessible_from(
				self.scope.namespace,
				decl.namespace.into(),
				Visibility::from(pub_span),
			)
		})
	}

	fn report_local_in_static_data(&mut self, span: TextSpan) {
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::LocalInStaticData.code())
				.with_message("a local variable cannot be used in static data")
				.with_label(
					Label::primary(self.scope.file_id, span)
						.with_message("a runtime value"),
				)
				.with_note(
					"a string or array literal is placed as data before the \
					 program runs, so its elements are constant expressions",
				),
		);
	}

	fn report_struct_used_as_value(&mut self, name: SymbolU32, span: TextSpan) {
		let name = self.builder.strings.resolve(name).unwrap();
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::StructUsedAsValue.code())
				.with_message(format!(
					"expected a value, found struct `{name}`"
				))
				.with_label(Label::primary(self.scope.file_id, span))
				.with_note(format!(
					"a struct's name is only a value when it is called: \
					 `{name}(...)`; to pass a constructor, pass a function \
					 that calls it"
				)),
		);
	}

	fn report_private_constructor(
		&self,
		struct_index: StructIdx,
		key: Option<DeclKey>,
		segment: &ast::PathSegment,
	) -> Diagnostic<FileId> {
		let decl = &self.sema.decls.structs[usize::from(struct_index)];
		let strings = &*self.builder.strings;
		let name = strings.resolve(decl.name.inner).unwrap();
		let private: Vec<String> = decl
			.field_names
			.iter()
			.zip(&decl.field_pub_spans)
			.enumerate()
			.filter(|(_, (_, pub_span))| pub_span.is_none())
			.map(|(at, (name, _))| match name {
				Some(name) => {
					format!("`{}`", strings.resolve(name.inner).unwrap())
				}
				None => format!("field {at}"),
			})
			.collect();
		let site = SourceSpan::new(self.scope.file_id, segment.ident.span);
		if private.is_empty() {
			return report_private_identifier(
				&self.sema.decls.namespaces,
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
		for (name, pub_span) in
			decl.field_names.iter().zip(&decl.field_pub_spans)
		{
			if pub_span.is_none()
				&& let Some(field_name) = name
			{
				diagnostic = diagnostic.with_label(
					SourceSpan::new(decl.file_id, field_name.span)
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
		if ty == TypeIndex::NEVER {
			// The operand never produces a value, so no operator is applied
			// and the unary expression itself diverges.
			return self.body.push(
				ExprKind::PrimitiveUnary {
					op: op.inner,
					operand,
				},
				TypeIndex::NEVER,
				span,
			);
		}
		if self.sema.types.is_unplaced(ty) {
			return self.report_operator_on_literal(
				op.inner.as_str(),
				operand,
				span,
			);
		}
		if ty.is_literal() {
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
		// expected to have the result's type; a comparison returns `Bool`
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
		// A diverging left operand has no type to lend the right one, so it
		// must not become the right side's expectation.
		let rhs = if self.sema.types.needs_context(left_ty)
			|| left_ty == TypeIndex::NEVER
		{
			self.build(right, expected)
		} else {
			self.build(right, left_ty)
		};
		let right_ty = self.body.ty(rhs);
		if left_ty == TypeIndex::NEVER || right_ty == TypeIndex::NEVER {
			return self
				.build_diverging_binary(op, lhs, rhs, left_ty, right_ty, span);
		}
		// Data not placed in a memory has no operators of its own.
		for (ty, operand) in [(left_ty, lhs), (right_ty, rhs)] {
			if self.sema.types.is_unplaced(ty) {
				return self.report_operator_on_literal(
					op.inner.as_str(),
					operand,
					span,
				);
			}
		}
		let operand_ty = match (
			self.sema.types.has_literal(left_ty),
			self.sema.types.has_literal(right_ty),
		) {
			(true, true) => {
				if is_comparison(op.inner) {
					return self.report_untyped_comparison(span);
				}
				// Two literals are a character if either is, else a float if
				// either is; anything else untyped (a tuple of literals) keeps
				// the left side's shape.
				let ty = if !left_ty.is_literal() || !right_ty.is_literal() {
					left_ty
				} else if left_ty == TypeIndex::CHAR_LITERAL
					|| right_ty == TypeIndex::CHAR_LITERAL
				{
					TypeIndex::CHAR_LITERAL
				} else if left_ty == TypeIndex::FLOAT_LITERAL
					|| right_ty == TypeIndex::FLOAT_LITERAL
				{
					TypeIndex::FLOAT_LITERAL
				} else {
					TypeIndex::INTEGER_LITERAL
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
					let diagnostic = self
						.context()
						.report_type_mismatch(left_ty, right_ty, rhs);
					self.sema.diagnostics.push(diagnostic);
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

	/// A binary with at least one `Never` operand. Since `!` fits every type,
	/// a lone diverging side lets the other side choose the operator; when
	/// that side is an untyped literal the node stays untyped for its context,
	/// exactly as two literals do. Two diverging operands apply no operator
	/// at all and are themselves `Never`.
	fn build_diverging_binary(
		&mut self,
		op: Spanned<BinaryOp>,
		lhs: ExprIdx,
		rhs: ExprIdx,
		left_ty: TypeIndex,
		right_ty: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		if left_ty == TypeIndex::NEVER && right_ty == TypeIndex::NEVER {
			return self.body.push(
				ExprKind::PrimitiveBinary {
					op: op.inner,
					lhs,
					rhs,
				},
				TypeIndex::NEVER,
				span,
			);
		}
		let live_ty = if left_ty == TypeIndex::NEVER {
			right_ty
		} else {
			left_ty
		};
		// Data not placed in a memory has no operators of its own.
		if self.sema.types.is_unplaced(live_ty) {
			let live = if left_ty == TypeIndex::NEVER {
				rhs
			} else {
				lhs
			};
			return self.report_operator_on_literal(
				op.inner.as_str(),
				live,
				span,
			);
		}
		if self.sema.types.has_literal(live_ty) {
			if is_comparison(op.inner) {
				return self.report_untyped_comparison(span);
			}
			return self.body.push(
				ExprKind::PrimitiveBinary {
					op: op.inner,
					lhs,
					rhs,
				},
				live_ty,
				span,
			);
		}
		let (kind, ty) = self.select_binary(op, lhs, rhs, live_ty);
		self.body.push(kind, ty, span)
	}

	/// A comparison between untyped literals — or between one and a
	/// diverging operand — has no concrete type from which to choose its
	/// instruction.
	fn report_untyped_comparison(&mut self, span: TextSpan) -> ExprIdx {
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(
					DiagnosticCode::ComparisonTypeAnnotationRequired.code(),
				)
				.with_message(
					"type annotation required to compare untyped literals",
				)
				.with_label(Label::primary(self.scope.file_id, span)),
		);
		self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
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
			self.sema.operators.unary(op.inner),
			self.body.span(operand),
			op.span,
			op.inner.as_str(),
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
		(self.method_call(lookup, ty, operand, None), ty)
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
				self.sema.types.resolve(ty),
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
			self.sema.operators.binary(op.inner),
			self.body.span(lhs),
			op.span,
			op.inner.as_str(),
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
		(self.method_call(lookup, ty, lhs, Some(rhs)), result)
	}

	/// Whether `ty` implements the operator's trait, and through what. `None`
	/// when it does not (reported here) or `ty` is already an error.
	fn operator_impl(
		&mut self,
		ty: TypeIndex,
		method: Option<OperatorMethod>,
		operand_span: TextSpan,
		op_span: TextSpan,
		op: &str,
	) -> Option<(OperatorMethod, TraitImplLookup)> {
		if ty == TypeIndex::ERROR {
			return None;
		}
		let found = match method {
			Some(method) => {
				match self.sema.find_trait_impl_query(
					self.builder.strings,
					self.scope.assumption_env,
					ty,
					method.trait_index,
				) {
					Ok(found) => found.map(|lookup| (method, lookup)),
					Err(error) => {
						let site = SourceSpan::new(self.scope.file_id, op_span);
						match error {
							SolverError::Overflow => {
								self.sema
									.diagnostics
									.push(self.sema.overflow_diagnostic(site));
							}
							SolverError::Cycle(cycle) => {
								let diagnostic = self.sema.cycle_diagnostic(
									self.builder.strings,
									&cycle,
									site,
								);
								self.sema.diagnostics.push(diagnostic);
							}
							_ => {}
						}
						return None;
					}
				}
			}
			None => None,
		};
		if found.is_none() {
			let ty = self
				.sema
				.type_formatter(self.builder.strings)
				.display_type(ty)
				.to_string();
			let label = Label::primary(self.scope.file_id, operand_span);
			let (message, label) = match method {
				Some(method) => {
					let name = self.sema.decls.traits
						[usize::from(method.trait_index)]
					.name
					.inner;
					let name = self.builder.strings.resolve(name).unwrap();
					(
						format!(
							"the trait bound `{ty}: {name}` is not satisfied"
						),
						label.with_message(format!(
							"the trait `{name}` is not implemented for `{ty}`"
						)),
					)
				}
				None => (format!("cannot apply `{op}` to `{ty}`"), label),
			};
			self.sema.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TraitBoundViolation.code())
					.with_message(message)
					.with_label(label)
					.with_label(
						Label::secondary(self.scope.file_id, op_span)
							.with_message(format!("required by `{op}`")),
					),
			);
		}
		found
	}

	/// A call of the operator's method on operands of type `ty`, with the
	/// first as the receiver and the other, if any, as its argument: the
	/// selected impl's own, or the trait's declaration when the receiver is
	/// abstract or the impl inherits a default.
	fn method_call(
		&mut self,
		selected: (OperatorMethod, TraitImplLookup),
		ty: TypeIndex,
		receiver: ExprIdx,
		operand: Option<ExprIdx>,
	) -> ExprKind {
		let args = operand.unwrap_or_else(|| {
			let span = self.body.span(receiver);
			self.pack([], ElementOrder::InOrder, TypeIndex::UNIT, span)
		});
		let span = self.body.span(receiver);
		match self.select_operator_method(selected, ty, span) {
			SelectedMethod::Concrete {
				function,
				type_args,
			} => ExprKind::MethodCall {
				function,
				type_args,
				receiver,
				args,
			},
			SelectedMethod::Abstract { method, type_args } => {
				ExprKind::AbstractMethodCall {
					method,
					type_args,
					receiver,
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
		span: TextSpan,
	) -> SelectedMethod {
		if let TraitImplLookup::Concrete { impl_index, args } = lookup
			&& let TraitMemberSelection::Impl(
				MemberKind::Method(function) | MemberKind::Function(function),
			) = self.sema.decls.select_trait_member(
				impl_index,
				MemberKind::Method(method.method),
			) {
			return SelectedMethod::Concrete {
				function,
				type_args: self
					.sema
					.generic_args
					.push(args.iter().map(|&arg| (arg, span))),
			};
		}
		SelectedMethod::Abstract {
			method: method.method,
			type_args: self.sema.generic_args.push([(ty, span)]),
		}
	}

	/// `memory`'s `Size` (`<memory as Memory>::Size`), normalized; `ERROR`
	/// when the stdlib declares no `Memory`.
	fn memory_size(&mut self, memory: TypeIndex) -> TypeIndex {
		let Some(projection) = self.sema.memory_size(memory) else {
			return TypeIndex::ERROR;
		};
		self.context().normalized(projection)
	}

	/// Gives an untyped subtree the type `target`, checking each literal is
	/// representable as it. Reports and leaves the offending node at `ERROR`
	/// when one does not.
	fn coerce(&mut self, expr: ExprIdx, target: TypeIndex) {
		// `!` fits every type and never produces a value, so there is nothing
		// to convert. Treating it as an untyped literal here would try to
		// select an operator for it or fail the literal-only coercion path.
		if self.body.ty(expr) == TypeIndex::NEVER {
			return;
		}
		if target == TypeIndex::ERROR {
			self.body.set_ty(expr, TypeIndex::ERROR);
			return;
		}
		// An untyped constant's body is of its kind already, and stays
		// untyped.
		if target.is_literal() {
			let actual = self.body.ty(expr);
			if actual != target {
				let diagnostic =
					self.context().report_type_mismatch(target, actual, expr);
				self.sema.diagnostics.push(diagnostic);
				self.body.set_ty(expr, TypeIndex::ERROR);
			}
			return;
		}
		match self.body.kind(expr) {
			ExprKind::Const { .. }
				if self.sema.types.is_unplaced(self.body.ty(expr)) =>
			{
				return self.place_constant(expr, target);
			}
			ExprKind::Const { .. } | ExprKind::AbstractConst { .. } => {
				return self.coerce_constant(expr, target);
			}
			ExprKind::String(_)
			| ExprKind::Array { .. }
			| ExprKind::ArrayRepeat { .. } => {
				return self.coerce_static(expr, target);
			}
			ExprKind::Tuple { elements, order } => {
				return self.coerce_tuple(expr, elements, order, target);
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
					if self.sema.types.needs_context(self.body.ty(branch)) {
						self.coerce(branch, target);
					}
				}
				return self.body.set_ty(expr, target);
			}
			ExprKind::Match { arms, .. } => {
				let bodies: Vec<ExprIdx> =
					self.body.arms(arms).iter().map(|arm| arm.body).collect();
				for arm in bodies {
					if self.sema.types.needs_context(self.body.ty(arm)) {
						self.coerce(arm, target);
					}
				}
				return self.body.set_ty(expr, target);
			}
			_ => {}
		}
		let concrete_types =
			self.sema.concrete_types(self.scope.assumption_env, target);
		if concrete_types.is_empty() {
			let diagnostic =
				self.context().report_unable_to_coerce(expr, target);
			self.sema.diagnostics.push(diagnostic);
			return self.body.set_ty(expr, TypeIndex::ERROR);
		}
		self.coerce_against(expr, target, &concrete_types);
	}

	/// Gives an untyped constant the type `target`. Whether its value is
	/// representable is decided once values exist (`decide_representable`), as
	/// a constant's body reads none.
	fn coerce_constant(&mut self, expr: ExprIdx, target: TypeIndex) {
		if self
			.sema
			.concrete_types(self.scope.assumption_env, target)
			.is_empty()
		{
			let diagnostic =
				self.context().report_unable_to_coerce(expr, target);
			self.sema.diagnostics.push(diagnostic);
			return self.body.set_ty(expr, TypeIndex::ERROR);
		}
		self.body.set_ty(expr, target);
		self.obligations
			.exprs
			.push(ExprObligation::Representable { expr, target });
	}

	/// `coerce` against the scalars a literal must be representable as:
	/// `target`'s own, or every member of every typeset it assumes.
	fn coerce_against(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		concrete_types: &[ConcreteType],
	) {
		match self.body.kind(expr) {
			ExprKind::Int(value) => {
				self.coerce_int(
					expr,
					expr,
					target,
					concrete_types,
					value,
					false,
				);
			}
			ExprKind::Float(_) => {
				self.coerce_float(expr, target, concrete_types)
			}
			ExprKind::Char(value) => {
				self.coerce_char(expr, target, concrete_types, value)
			}
			ExprKind::PrimitiveUnary { op, operand } => {
				for &concrete in concrete_types {
					if concrete.allows_unary(op) {
						continue;
					}
					let diagnostic = match concrete {
						ConcreteType::Member(typeset, member) => {
							let at = self.context().source_span(expr);
							self.sema.report_typeset_member(
								self.builder.strings,
								"literal",
								typeset,
								member,
								at,
							)
						}
						ConcreteType::Target(_) => {
							self.context().report_unable_to_coerce(expr, target)
						}
					};
					return self.context().reject(expr, diagnostic);
				}
				let coerced = match (op, self.body.kind(operand)) {
					// `-128` is in range for `i8` though `128` is not: a
					// negated literal is checked as the negative value.
					(UnaryOp::InvertSign, ExprKind::Int(value)) => self
						.coerce_int(
							expr,
							operand,
							target,
							concrete_types,
							value,
							true,
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
			_ => unreachable!(
				"only literals and operators over them are untyped"
			),
		}
	}

	/// Checks an integer literal (`value`, optionally negated) against every
	/// concrete type of `target`, then gives `literal` the type `target` and
	/// returns `true`. When one cannot represent it, it draws the report,
	/// leaves the node at `ERROR`, and returns `false`. `report` is the node a
	/// diagnostic points at — the unary itself, for a negated literal.
	fn coerce_int(
		&mut self,
		report: ExprIdx,
		literal: ExprIdx,
		target: TypeIndex,
		concrete_types: &[ConcreteType],
		magnitude: u64,
		negated: bool,
	) -> bool {
		let value = if negated {
			-i128::from(magnitude)
		} else {
			i128::from(magnitude)
		};
		let at = self.context().source_span(report);
		let mut all_float = true;
		for &concrete in concrete_types {
			let Err(miss) = concrete.holds_integer(value) else {
				all_float &= concrete.is_float();
				continue;
			};
			let diagnostic = match (concrete, miss) {
				(ConcreteType::Member(typeset, member), _) => {
					self.sema.report_typeset_member(
						self.builder.strings,
						format_args!("literal `{value}`"),
						typeset,
						member,
						at,
					)
				}
				(ConcreteType::Target(_), IntegerMiss::OutOfRange) => {
					self.sema.report_out_of_range(
						self.builder.strings,
						format_args!("literal `{value}`"),
						target,
						at,
					)
				}
				(ConcreteType::Target(_), IntegerMiss::Inexact) => {
					Diagnostic::error()
						.with_code(
							DiagnosticCode::IntegerLiteralNotRepresentable
								.code(),
						)
						.with_message(format!(
							"literal `{value}` cannot be represented exactly \
							 as `{}`",
							self.sema
								.type_formatter(self.builder.strings)
								.display_type(target)
						))
						.with_label(at.primary_label())
				}
				(ConcreteType::Target(_), IntegerMiss::WrongKind) => {
					self.context().report_unable_to_coerce(report, target)
				}
			};
			self.context().reject(report, diagnostic);
			return false;
		}
		// An integer literal of float type is a float.
		if all_float {
			self.body
				.set_kind(literal, ExprKind::Float(magnitude as f64));
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
		order: ElementOrder,
		target: TypeIndex,
	) {
		let targets = match *self.sema.types.resolve(target) {
			Type::Tuple { elements: targets }
				if targets.len() == elements.len() =>
			{
				targets
			}
			_ => {
				let actual = self.body.ty(expr);
				let diagnostic =
					self.context().report_type_mismatch(target, actual, expr);
				self.sema.diagnostics.push(diagnostic);
				return self.body.set_ty(expr, TypeIndex::ERROR);
			}
		};
		let mut types = vec![TypeIndex::ERROR; elements.len()];
		for at in 0..elements.len() {
			let element = self.body.args(elements)[at];
			let position = usize::from(self.body.declared_index(order, at));
			let element_target = self.sema.types.list(targets)[position];
			let element = self.expect(element, element_target);
			types[position] = self.body.ty(element);
		}
		let ty = self.sema.types.intern_tuple(&types);
		let ty = self.sema.types.collapse_error(ty);
		self.body.set_ty(expr, ty);
	}

	/// Reads a float literal's value from its text at each concrete type's
	/// width.
	fn coerce_float(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		concrete_types: &[ConcreteType],
	) {
		let source =
			&self.builder.files.get(self.scope.file_id).unwrap().source;
		let text = self.body.span(expr).extract_str(source);
		let mut value = None;
		for &concrete in concrete_types {
			match concrete.read_float(text) {
				Ok(Some(read)) => {
					value.get_or_insert(read);
				}
				// Malformed syntax was reported by the parser.
				Ok(None) => return self.body.set_ty(expr, TypeIndex::ERROR),
				Err(miss) => {
					let at = self.context().source_span(expr);
					let ty = self
						.sema
						.type_formatter(self.builder.strings)
						.display_type(concrete.ty());
					let diagnostic = match (concrete, miss) {
						(_, FloatMiss::TooLarge) => Diagnostic::error()
							.with_code(
								DiagnosticCode::FloatLiteralOverflow.code(),
							)
							.with_message(format!(
								"float literal is too large for `{ty}`"
							))
							.with_label(at.primary_label()),
						(_, FloatMiss::TooSmall) => Diagnostic::error()
							.with_code(
								DiagnosticCode::FloatLiteralUnderflow.code(),
							)
							.with_message(format!(
								"float literal is too small to represent in \
								 `{ty}`"
							))
							.with_label(at.primary_label()),
						(
							ConcreteType::Member(typeset, member),
							FloatMiss::WrongKind,
						) => self.sema.report_typeset_member(
							self.builder.strings,
							"float literal",
							typeset,
							member,
							at,
						),
						(ConcreteType::Target(_), FloatMiss::WrongKind) => {
							self.context().report_unable_to_coerce(expr, target)
						}
					};
					return self.context().reject(expr, diagnostic);
				}
			}
		}
		self.body.set_kind(expr, ExprKind::Float(value.unwrap()));
		self.body.set_ty(expr, target);
	}

	/// A character literal is a `Char`, or an integer that can represent its
	/// code point, which it then is.
	fn coerce_char(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		concrete_types: &[ConcreteType],
		value: char,
	) {
		let at = self.context().source_span(expr);
		for &concrete in concrete_types {
			let Err(miss) = concrete.holds_char(u32::from(value)) else {
				continue;
			};
			let diagnostic = match (concrete, miss) {
				(ConcreteType::Member(typeset, member), _) => {
					self.sema.report_typeset_member(
						self.builder.strings,
						format_args!("literal {value:?}"),
						typeset,
						member,
						at,
					)
				}
				(ConcreteType::Target(_), CharMiss::OutOfRange) => {
					self.sema.report_out_of_range(
						self.builder.strings,
						format_args!("literal {value:?}"),
						target,
						at,
					)
				}
				(ConcreteType::Target(_), CharMiss::WrongKind) => {
					self.context().report_unable_to_coerce(expr, target)
				}
			};
			return self.context().reject(expr, diagnostic);
		}
		if target != TypeIndex::CHAR {
			self.body.set_kind(expr, ExprKind::Int(u64::from(value)));
		}
		self.body.set_ty(expr, target);
	}

	/// Places a string or array literal, data in no memory: it becomes a
	/// shared pointer to an array of its length or to a slice, in whatever
	/// memory `target` names, abstract ones included. The data is read-only,
	/// so an exclusive pointer is not one it can become. In a constant's
	/// type it stays in no memory, as the array `target` is. A string's
	/// elements are bytes; an array literal's are checked against the
	/// target's element type. Placed, a repeat's count is a length in the
	/// memory, of its `Size`.
	fn coerce_static(&mut self, expr: ExprIdx, target: TypeIndex) {
		let Type::Array { length, .. } =
			*self.sema.types.resolve(self.body.ty(expr))
		else {
			unreachable!("a literal is an array")
		};
		// Only an array's length can be left to the literal.
		let parts = self.context().static_target(target);
		let known = parts.is_some_and(|parts| {
			!self.sema.types.has_infer(parts.of)
				&& parts
					.memory
					.is_none_or(|memory| !self.sema.types.has_infer(memory))
		});
		if self.sema.types.has_infer(target) && !known {
			self.report_annotation_required(expr);
			return self.body.set_ty(expr, TypeIndex::ERROR);
		}
		let kind = self.body.kind(expr);
		let fits = parts.filter(|parts| {
			!matches!(kind, ExprKind::String(_)) || parts.of == TypeIndex::U8
		});
		let Some(parts) = fits else {
			let note = match kind {
				ExprKind::String(_) => STRING_TARGETS_NOTE,
				_ => ARRAY_TARGETS_NOTE,
			};
			let diagnostic = self
				.context()
				.report_unable_to_coerce(expr, target)
				.with_note(note);
			self.sema.diagnostics.push(diagnostic);
			return self.body.set_ty(expr, TypeIndex::ERROR);
		};
		match kind {
			ExprKind::String(_) => {}
			ExprKind::Array { elements } => {
				for at in 0..elements.len() {
					let element = self.body.args(elements)[at];
					self.expect(element, parts.of);
				}
			}
			ExprKind::ArrayRepeat { value, count } => {
				self.expect(value, parts.of);
				if let (Some(count), Some(memory)) = (count, parts.memory) {
					let length_type = self.memory_size(memory);
					self.expect(count, length_type);
				}
				// `[value; _]` is as long as the array it becomes.
				if count.is_none() {
					return match parts.length {
						Some(length) if length != TypeIndex::INFER => {
							self.body.set_ty(expr, target)
						}
						_ => {
							self.report_annotation_required(expr);
							self.body.set_ty(expr, TypeIndex::ERROR)
						}
					};
				}
			}
			_ => unreachable!("only static data is coerced as static data"),
		}
		self.set_static_type(expr, target, parts, length);
	}

	/// Places the constant `expr` names, which holds data in no memory (an
	/// array): each use is its own copy, in the memory `target` names, as a
	/// literal is. Its element type is the target's. An array `target` (a
	/// constant's type) keeps it in no memory.
	fn place_constant(&mut self, expr: ExprIdx, target: TypeIndex) {
		let Type::Array { of: actual, length } =
			*self.sema.types.resolve(self.body.ty(expr))
		else {
			let diagnostic =
				self.context().report_unable_to_coerce(expr, target);
			self.sema.diagnostics.push(diagnostic);
			return self.body.set_ty(expr, TypeIndex::ERROR);
		};
		let Some(parts) = self.context().static_target(target) else {
			let diagnostic = self
				.context()
				.report_unable_to_coerce(expr, target)
				.with_note(ARRAY_TARGETS_NOTE);
			self.sema.diagnostics.push(diagnostic);
			return self.body.set_ty(expr, TypeIndex::ERROR);
		};
		let span = self.body.span(expr);
		match self.context().equality(
			parts.of,
			actual,
			RewriteFlags::EQUALITIES | RewriteFlags::DEFINITIONS,
			span,
		) {
			Ok(TypeEquality::Equal | TypeEquality::NeedsValues) => {}
			Ok(TypeEquality::Diff) => {
				return self.context().report_mismatch(expr, target);
			}
			Err(()) => return self.body.set_ty(expr, TypeIndex::ERROR),
		}
		self.set_static_type(expr, target, parts, length);
		if parts.memory.is_some() {
			self.body.push_static(expr);
		}
	}

	/// Gives static data `expr` of length `length` the type `target`, whose
	/// `parts` are as `static_target` reads them: a written `_` takes the
	/// data's length, and any other length must be the data's.
	fn set_static_type(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		parts: StaticTarget,
		length: TypeIndex,
	) {
		let Some(target_length) = parts.length else {
			return self.body.set_ty(expr, target);
		};
		if target_length == TypeIndex::INFER {
			let of = parts.of;
			let mut ty = self.sema.types.intern(Type::Array { of, length });
			if let Some(memory) = parts.memory {
				ty = self.sema.types.intern(Type::Pointer {
					to: ty,
					memory,
					ownership: Ownership::Shared,
				});
			}
			return self.body.set_ty(expr, ty);
		}
		self.body.set_ty(expr, target);
		self.check_static_length(expr, target, length);
	}

	/// Checks that a string or array literal `expr` of length `length` is as
	/// long as `target`, the array it becomes. In a constant's body, a length
	/// that names a constant is compared once it has a value.
	fn check_static_length(
		&mut self,
		expr: ExprIdx,
		target: TypeIndex,
		length: TypeIndex,
	) {
		let Some(StaticTarget {
			length: Some(target_length),
			..
		}) = self.context().static_target(target)
		else {
			unreachable!("a literal with a length becomes an array")
		};
		if target_length == length {
			return;
		}
		if self.sema.types.has_const(target_length)
			|| self.sema.types.has_const(length)
		{
			return self.obligations.exprs.push(ExprObligation::StaticLength {
				expr,
				target,
				length,
			});
		}
		self.context().decide_static_length(expr, target, length);
	}

	/// An operator applied to an untyped string or array literal, which has
	/// no operators of its own; placed, a pointer to it has its slice's or
	/// array's methods.
	fn report_operator_on_literal(
		&mut self,
		op: &str,
		operand: ExprIdx,
		span: TextSpan,
	) -> ExprIdx {
		let (noun, note) = match self.body.kind(operand) {
			ExprKind::String(_) => ("a string literal", STRING_TARGETS_NOTE),
			ExprKind::Array { .. } | ExprKind::ArrayRepeat { .. } => {
				("an array literal", ARRAY_TARGETS_NOTE)
			}
			_ => ("data in no memory", ARRAY_TARGETS_NOTE),
		};
		let at = self.context().source_span(operand);
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TraitBoundViolation.code())
				.with_message(format!("cannot apply `{op}` to {noun}"))
				.with_label(at.primary_label())
				.with_note(note),
		);
		self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
	}
}

/// What a string or array literal can become (`static_target`).
#[derive(Clone, Copy)]
struct StaticTarget {
	/// The element type.
	of: TypeIndex,
	/// The memory it is placed in; `None` for an array in no memory.
	memory: Option<TypeIndex>,
	/// The length; `None` for a slice.
	length: Option<TypeIndex>,
}

/// What a string literal can become, for the notes that reject one.
pub(super) const STRING_TARGETS_NOTE: &str = "a string literal is placed in \
	a memory as a shared byte slice or byte array: `heap::&[u8]` or \
	`heap::&[u8; N]`";

pub(super) const ARRAY_TARGETS_NOTE: &str = "an array literal is placed in a \
	memory as a shared array or slice: `heap::&[T; N]` or `heap::&[T]`";

/// The method an operator dispatches to, with its type arguments.
#[derive(Clone, Copy)]
enum SelectedMethod {
	/// The selected impl's own method, called directly.
	Concrete {
		function: FunctionIdx,
		type_args: GenericArgs,
	},
	/// The trait's declaration, whose impl is selected once the receiver is
	/// known.
	Abstract {
		method: FunctionIdx,
		type_args: GenericArgs,
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

#[cfg(test)]
mod tests {
	use indoc::indoc;

	use super::super::body::{
		Body, ElementOrder, ExprIdx, ExprKind, ExprRange, PlaceIdx, PlaceKind,
	};
	use super::super::decls::{
		DeclKind, FunctionIdx, MemberOwner, Scope, Tier,
	};
	use super::super::eval::{ConstScalar, ConstValueState};
	use super::super::paths::PathResolver;
	use super::super::resolutions::{NameResolutions, Referent, Resolution};
	use super::super::signatures::Semantics;
	use super::super::solver::{NormalizationDepth, RewriteFlags};
	use super::super::types::{GenericEnvIdx, Type, TypeIndex};
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::{DiagnosticCode, TextSpan};
	use crate::testing::DiagnosticView;
	use crate::vfs::{self, Files};

	fn source_graph(
		source: &str,
		strings: &mut StringInterner,
	) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new(strings);
		builder.load_stdlib();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)]),
				),
			)
			.unwrap();
		let graph = builder.build(root_id);
		DiagnosticView::new(
			"parse",
			&graph.collect_parser_diagnostics(),
			&graph.files,
		)
		.assert_no_errors();
		graph
	}

	/// The source is a binary over the real stdlib, so operators, memories
	/// and globals are checked against its actual traits.
	struct TestCase {
		files: Files,
		strings: StringInterner,
		sema: Semantics,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut strings = ast::Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
			let mut sema = crate::tir::check(&graph, &mut strings);
			// The stdlib's own bodies use forms the checker does not cover
			// yet; those reports are not what this suite is about.
			let root_file = sema
				.decls
				.namespaces
				.file_id(Scope::Package(sema.decls.root_package).into());
			sema.diagnostics.retain(|diagnostic| {
				let in_stdlib = diagnostic
					.labels
					.first()
					.is_some_and(|label| label.file_id != root_file);
				!(in_stdlib
					&& diagnostic.code.as_deref()
						== Some(DiagnosticCode::UnsupportedExpression.code()))
			});
			Self {
				files: graph.files,
				strings,
				sema,
			}
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"typecheck",
				&self.sema.diagnostics,
				&self.files,
			)
		}

		fn resolve(&self, name: &str) -> DeclKind {
			let root = Scope::Package(self.sema.decls.root_package);
			let file_id = self.sema.decls.namespaces.file_id(root.into());
			let segments: Box<[ast::PathSegment]> = name
				.split("::")
				.map(|segment| ast::PathSegment {
					ident: Spanned {
						inner: self.strings.get(segment).unwrap(),
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
				&self.strings,
				&self.sema.decls,
			)
			.resolve_path(file_id, root, &segments, Tier::Value)
			.decl_key()
			.unwrap_or_else(|| panic!("expected `{name}` to resolve"))
			.symbol_kind(&self.sema.decls)
		}

		/// The checked block of the function `name`.
		fn body(&self, name: &str) -> &Body {
			let DeclKind::Function(index) = self.resolve(name) else {
				panic!("expected `{name}` to be a function");
			};
			self.sema.body(
				self.sema.function_implementations[usize::from(index)]
					.body()
					.expect("a function with a block has a body"),
			)
		}

		/// The rendered block of the member `name`, which only one impl or
		/// trait in the test defines with a block.
		fn member_shape(&self, name: &str) -> String {
			let symbol = self.strings.get(name).unwrap();
			let mut found =
				self.sema.decls.functions.iter().enumerate().filter(
					|&(index, function)| {
						function.name.inner == symbol
							&& !matches!(function.owner, MemberOwner::Free)
							&& self.sema.function_implementations[index]
								.body()
								.is_some()
					},
				);
			let (index, _) = found.next().unwrap();
			assert!(found.next().is_none(), "`{name}` is declared twice");
			let body = self.sema.body(
				self.sema.function_implementations[index].body().unwrap(),
			);
			self.render(body, body.root())
		}

		fn display(&self, ty: TypeIndex) -> String {
			self.sema
				.type_formatter(&self.strings)
				.display_type(ty)
				.to_string()
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

		/// A call's arguments in written order; when they are permuted, each
		/// is prefixed with the parameter it gives: `(call f 1=2 0=1)`.
		fn render_call(
			&self,
			body: &Body,
			head: &str,
			args: ExprRange,
			order: ElementOrder,
		) -> String {
			let mut text = format!("({head}");
			for (at, &arg) in body.args(args).iter().enumerate() {
				text.push(' ');
				if let ElementOrder::Permuted { .. } = order {
					let param = body.declared_index(order, at);
					text.push_str(&format!("{}=", usize::from(param)));
				}
				text.push_str(&self.render(body, arg));
			}
			text + ")"
		}

		/// A call's `head` and then its `args`, the value of `count`
		/// parameters: a tuple of several is written as its elements, as the
		/// call is; any other value, a lone parameter's, as itself.
		fn render_arguments(
			&self,
			body: &Body,
			head: &str,
			count: usize,
			args: ExprIdx,
		) -> String {
			match body.kind(args) {
				ExprKind::Tuple { elements, order } if count != 1 => {
					self.render_call(body, head, elements, order)
				}
				_ => format!("({head} {})", self.render(body, args)),
			}
		}

		fn param_count(&self, function: FunctionIdx) -> usize {
			self.sema.functions[usize::from(function)].param_types.len()
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
			let name = |symbol| self.strings.resolve(symbol).unwrap();
			match body.kind(expr) {
				ExprKind::Error => "error".to_string(),
				ExprKind::Int(value) => value.to_string(),
				ExprKind::Float(value) => format!("{value:?}"),
				ExprKind::Char(value) => format!("{value:?}"),
				ExprKind::String(contents) => {
					format!("{:?}", self.strings.resolve(contents).unwrap())
				}
				ExprKind::Array { elements } => {
					list("array", body.args(elements))
				}
				ExprKind::ArrayRepeat { value, count } => match count {
					Some(count) => list("repeat", &[value, count]),
					None => list("repeat _", &[value]),
				},
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
				ExprKind::NextDiscriminant(index) => name(
					self.sema.decls.constants[usize::from(index)].name.inner,
				)
				.to_string(),
				ExprKind::Local(local) => self.local_name(body, local),
				ExprKind::Global(index) => {
					name(self.sema.decls.globals[usize::from(index)].name.inner)
						.to_string()
				}
				ExprKind::Memory(index) => name(
					self.sema.decls.memories[usize::from(index)].name.inner,
				)
				.to_string(),
				ExprKind::Function {
					function,
					type_args,
				} => self.callee(function, type_args),
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
					self.render_arguments(
						body,
						&format!("call {callee}"),
						self.param_count(function),
						args,
					)
				}
				ExprKind::AbstractCall {
					method,
					type_args,
					args,
				} => {
					let callee = self.callee(method, type_args);
					self.render_arguments(
						body,
						&format!("abstract {callee}"),
						self.param_count(method),
						args,
					)
				}
				ExprKind::MethodCall {
					function,
					type_args,
					receiver,
					args,
				} => {
					let callee = self.callee(function, type_args);
					let head = format!(
						"call {callee} {}",
						self.render(body, receiver)
					);
					self.render_arguments(
						body,
						&head,
						self.param_count(function) - 1,
						args,
					)
				}
				ExprKind::AbstractMethodCall {
					method,
					type_args,
					receiver,
					args,
				} => {
					let callee = self.callee(method, type_args);
					let head = format!(
						"abstract {callee} {}",
						self.render(body, receiver)
					);
					self.render_arguments(
						body,
						&head,
						self.param_count(method) - 1,
						args,
					)
				}
				ExprKind::CallRef { callee, args } => {
					let head =
						format!("call_ref {}", self.render(body, callee));
					self.render_arguments(body, &head, 0, args)
				}
				ExprKind::Tuple { elements, order } => {
					self.render_call(body, "tuple", elements, order)
				}
				ExprKind::StructConstructor {
					struct_index,
					fields,
				} => {
					let name = name(
						self.sema.decls.structs[usize::from(struct_index)]
							.name
							.inner,
					);
					let count = self.sema.structs[usize::from(struct_index)]
						.field_types
						.len();
					self.render_arguments(body, name, count, fields)
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
			use super::super::body::PatternKind;
			let list = |head: &str, children: &[super::super::body::PatIdx]| {
				let mut text = format!("({head}");
				for &child in children {
					text.push(' ');
					text.push_str(&self.render_pattern(body, child));
				}
				text + ")"
			};
			match body.pattern(pattern) {
				PatternKind::Wildcard => "_".to_string(),
				PatternKind::Bind(local) => self.local_name(body, local),
				PatternKind::Tuple(elements) => {
					list("tuple", body.patterns(elements))
				}
				PatternKind::Struct {
					struct_index,
					fields,
				} => {
					let name = self.sema.decls.structs
						[usize::from(struct_index)]
					.name
					.inner;
					let name = self.strings.resolve(name).unwrap();
					let count = self.sema.structs[usize::from(struct_index)]
						.field_types
						.len();
					match body.pattern(fields) {
						PatternKind::Tuple(children) if count != 1 => {
							list(name, body.patterns(children))
						}
						_ => list(name, &[fields]),
					}
				}
				PatternKind::Int(bits) => {
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
				PatternKind::Char(value) => format!("{value:?}"),
				PatternKind::Constant {
					constant,
					type_args,
				} => self.constant_name(constant, type_args),
				PatternKind::AbstractConstant {
					constant,
					type_args,
				} => format!(
					"(abstract {})",
					self.constant_name(constant, type_args)
				),
				PatternKind::Or(alternatives) => {
					list("|", body.patterns(alternatives))
				}
				PatternKind::Error => "error".to_string(),
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
				PlaceKind::Element { object, index } => format!(
					"([] {} {})",
					self.render_place(body, object),
					self.render(body, index)
				),
			}
		}

		fn function_name(&self, index: super::FunctionIdx) -> &str {
			let name = self.sema.decls.functions[usize::from(index)].name.inner;
			self.strings.resolve(name).unwrap()
		}

		/// A constant's name, with its type arguments when it has any.
		fn constant_name(
			&self,
			index: super::ConstIdx,
			type_args: super::GenericArgs,
		) -> String {
			let name = self.sema.decls.constants[usize::from(index)].name.inner;
			self.with_type_args(self.strings.resolve(name).unwrap(), type_args)
		}

		/// A called function's name, with its type arguments when it has
		/// any: `add`, `id<u8>`.
		fn callee(
			&self,
			index: super::FunctionIdx,
			type_args: super::GenericArgs,
		) -> String {
			self.with_type_args(self.function_name(index), type_args)
		}

		fn with_type_args(
			&self,
			name: &str,
			type_args: super::GenericArgs,
		) -> String {
			let type_args = self.sema.generic_args.types(type_args);
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
				self.strings.resolve(name).unwrap(),
				u32::from(local)
			)
		}

		fn field_name(
			&self,
			object: TypeIndex,
			field: crate::tir::decls::FieldIdx,
		) -> &str {
			let Type::Struct { struct_index, .. } =
				*self.sema.types.resolve(object)
			else {
				panic!("a field of a non-struct");
			};
			let field = self.sema.decls.structs[usize::from(struct_index)]
				.field_names[usize::from(field)]
			.unwrap();
			self.strings.resolve(field.inner).unwrap()
		}

		/// A jump's target: its label, else the kind of scope it leaves.
		fn scope_name(&self, body: &Body, scope: super::ScopeIdx) -> String {
			let scope = body.scope(scope);
			match scope.label {
				Some(label) => self
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
					let name = self.strings.resolve(local.name.inner).unwrap();
					(name.to_string(), self.display(local.ty))
				})
				.collect()
		}
	}

	#[test]
	fn the_embedded_stdlib_reports_nothing_but_unsupported_forms() {
		let case = TestCase::new("");
		case.diagnostics().assert_none();
	}

	#[test]
	fn parameters_are_locals_of_the_root_scope() {
		const SOURCE: &str = "func f(a: u32, mut b: u32) -> u32 { a + b }";
		let case = TestCase::new(SOURCE);
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
			.sema
			.decls
			.namespaces
			.file_id(Scope::Package(case.sema.decls.root_package).into());
		let start = SOURCE.find("a + b").unwrap() as u32;
		let site = (
			crate::diagnostics::SourceSpan::new(
				file_id,
				TextSpan::new(start, start + 1),
			),
			Tier::Value,
		);
		assert!(matches!(
			case.sema.resolutions.by_site.get(&site),
			Some(Resolution::Reference(Referent::Local { local, .. })) if u32::from(*local) == 0
		));
	}

	/// An unnamed parameter is passed like any other, but binds no local.
	#[test]
	fn an_unnamed_parameter_binds_no_local() {
		let case = TestCase::new("func f(u32, _: u8, c: u32) -> u32 { c }");
		case.diagnostics().assert_none();
		assert_eq!(case.locals("f"), [("c".into(), "u32".into())]);
		let params: Vec<_> = case
			.body("f")
			.params()
			.iter()
			.map(|local| local.map(u32::from))
			.collect();
		assert_eq!(params, [None, None, Some(0)]);
	}

	#[test]
	fn a_block_result_takes_the_return_type() {
		let case = TestCase::new(indoc! {"
				func literal() -> u8 { 200 + 50 }
				func nothing() {}
				func diverges() -> u32 { loop {} }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.body_type("literal"), "u8");
		assert_eq!(case.body_type("nothing"), "()");
		assert_eq!(case.body_type("diverges"), "!");
	}

	#[test]
	fn a_block_without_a_result_does_not_give_a_value() {
		let case = TestCase::new("func f() -> u32 { local x: u32 = 1; }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
	}

	#[test]
	fn a_local_takes_its_written_type_or_its_values() {
		let case = TestCase::new(indoc! {"
				func f(a: u64) {
					local x: u8 = 1;
					local y = a;
					local z = (x, y);
				}
			"});
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
		let case = TestCase::new("func f() { local x = 1; }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeAnnotationRequired]);
		assert_eq!(case.locals("f"), [("x".into(), "{unknown}".into())]);
	}

	#[test]
	fn a_character_literal_is_a_char_or_an_integer_that_represents_it() {
		let case = TestCase::new(indoc! {"
				func c() -> Char { 'a' }
				func b() -> u8 { 'a' }
				func w() -> u16 { '€' }
				func digit(d: u8) -> u8 { d + '0' }
				func next() -> u8 { 'a' + 1 }
				func any<T: Integer>() -> T { 'a' }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("c"), "(block => 'a')");
		assert_eq!(case.shape("b"), "(block => 97)");
		assert_eq!(case.shape("w"), "(block => 8364)");
		assert_eq!(case.shape("next"), "(block => (+ 97 1))");
	}

	#[test]
	fn a_character_literal_must_be_representable_as_its_integer() {
		let case = TestCase::new("func f() -> u8 { '€' }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
		case.diagnostics()
			.assert_error_saying("literal '€' cannot be represented as `u8`");
		let case = TestCase::new("func f<T: Integer>() -> T { '€' }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypesetBoundViolation]);
	}

	#[test]
	fn a_character_literal_is_no_float_and_has_no_default() {
		let case = TestCase::new("func f() -> f32 { 'a' }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnableToCoerce]);
		let case = TestCase::new("func f() { local c = 'a'; }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeAnnotationRequired]);
		let case = TestCase::new("func f() -> Char { 'a' + 1 }");
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::TraitBoundViolation,
		]);
	}

	#[test]
	fn a_character_pattern_compares_an_integer_by_code_point() {
		let case = TestCase::new(indoc! {"
				func f(b: u8) -> u32 { match b { 'a' => { 1 }, _ => { 0 } } }
				func g(c: Char) -> u32 { match c { 'a' => { 1 }, _ => { 0 } } }
			"});
		case.diagnostics().assert_none();
		let case = TestCase::new(
			"func f(b: u8) -> u32 { match b { '€' => { 1 }, _ => { 0 } } }",
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
		case.diagnostics()
			.assert_error_saying("literal '€' cannot be represented as `u8`");
	}

	#[test]
	fn a_later_local_shadows_an_earlier_one_from_its_declaration_on() {
		let case = TestCase::new(
			"func f() -> u32 { local x: u32 = 1; local x = x + 1; x }",
		);
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block (local x#0 1) (local x#1 (+ x#0 1)) => x#1)"
		);
	}

	#[test]
	fn a_local_is_visible_only_in_its_block() {
		let case = TestCase::new(indoc! {"
				func f() -> u32 {
					block { local inner: u32 = 1; };
					inner
				}
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
	}

	#[test]
	fn a_local_shadows_an_item_of_the_same_name() {
		let case = TestCase::new(
			"const x: u8 = 1; func f() -> u16 { local x: u16 = 2; x }",
		);
		case.diagnostics().assert_none();
		assert_eq!(case.shape("f"), "(block (local x#0 2) => x#0)");
	}

	#[test]
	fn a_statement_value_must_be_used_or_dropped() {
		let case = TestCase::new(indoc! {"
				func one() -> u32 { 1 }
				func f() {
					one();
					_ = one();
				}
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnusedValue]);
		assert_eq!(case.shape("f"), "(block (call one) (drop (call one)))");
	}

	#[test]
	fn code_after_a_diverging_statement_is_unreachable() {
		let case =
			TestCase::new("func f() -> u32 { return 1; local x: u32 = 2; x }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnreachableCode]);
		case.diagnostics()
			.assert_warning(DiagnosticCode::UnreachableCode);
		assert_eq!(case.body_type("f"), "u32");
	}

	#[test]
	fn unreachable_statements_and_tail_are_still_typechecked() {
		let case = TestCase::new(
			"func f() -> u32 { return 1; local x: u32 = True; missing }",
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::UnreachableCode,
			DiagnosticCode::UndeclaredIdentifier,
		]);
		case.diagnostics()
			.assert_warning(DiagnosticCode::UnreachableCode);
	}

	#[test]
	fn an_uncalled_function_body_is_still_typechecked() {
		let case = TestCase::new("func unused() -> u32 { missing }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
	}

	#[test]
	fn if_branches_share_a_type() {
		let case = TestCase::new(indoc! {"
				func pick(c: Bool, a: u8) -> u8 { if c { a } else { 1 } }
				func nested(c: Bool) -> u16 { if c { 1 } else { if !c { 2 } else { 3 } } }
				func diverging(c: Bool, a: u8) -> u8 { if c { return a; } else { a } }
				func statement(c: Bool) { if c { pick(c, 1); } }
				func untyped(c: Bool) { local x: i64 = if c { 1 } else { 2 }; }
			"});
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
		let case = TestCase::new(
			"func f(c: Bool, a: u8) { local x = if c { 1 } else { a }; }",
		);
		case.diagnostics().assert_none();
		assert_eq!(case.locals("f")[2], ("x".into(), "u8".into()));
	}

	#[test]
	fn if_errors_are_reported_where_they_are_written() {
		let case = TestCase::new(indoc! {"
				func condition(a: u8) { if a { } }
				func mismatch(c: Bool, a: u8, b: u16) { local x = if c { a } else { b }; }
				func missing_else(c: Bool, a: u8) -> u8 { if c { a } }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::MissingElseBlock,
		]);
	}

	#[test]
	fn a_loop_is_typed_by_its_breaks() {
		let case = TestCase::new(indoc! {"
				func first(n: u32) -> u32 {
					local mut i: u32 = 0;
					loop {
						if i == n { break i; }
						i += 1;
					}
				}
				func endless() -> u8 { loop {} }
				func unit() { loop { break; } }
			"});
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
		let case = TestCase::new(indoc! {"
				func f(c: Bool, a: u8, b: u16) {
					local x = loop { if c { break a; } break b; };
				}
				func untyped() { local x = loop { break 1; }; }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeAnnotationRequired,
		]);
	}

	#[test]
	fn a_label_names_the_scope_a_jump_leaves() {
		let case = TestCase::new(indoc! {"
				func f(c: Bool) -> u32 {
					loop :outer {
						loop {
							if c { break :outer 1; }
							continue :outer;
						}
					}
				}
				func labelled_block(c: Bool) -> u8 {
					block :found {
						if c { break :found 1; }
						2
					}
				}
			"});
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
	}

	#[test]
	fn an_ascription_checks_its_value_against_its_type() {
		let case = TestCase::new(indoc! {"
				func id<T: StackValue>(t: T) -> T { t }
				func literal() -> u8 { (5: u8) }
				func inferred() { local x = id(5: u16); }
				func elements() { local t = (1: u8, 2: u16); }
			"});
		case.diagnostics().assert_none();
		// It leaves no node of its own.
		assert_eq!(case.shape("literal"), "(block => 5)");
		assert_eq!(case.body_type("literal"), "u8");
		assert_eq!(case.locals("inferred"), [("x".into(), "u16".into())]);
		assert_eq!(case.locals("elements"), [("t".into(), "(u8, u16)".into())]);
	}

	#[test]
	fn an_ascription_converts_nothing() {
		let case = TestCase::new(indoc! {"
				func takes(x: u16) {}
				func widened(a: u8) -> u16 { (a: u16) }
				func argument() { takes(1: u8); }
				func out_of_range() { local x = (300: u8); }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::IntegerLiteralOutOfRange,
		]);
	}

	#[test]
	fn jumps_need_a_target() {
		let case = TestCase::new(indoc! {"
				func outside() { break; }
				func outside_continue() { continue; }
				func unknown() { loop { break :nowhere; } }
				func not_a_loop() { block :l { continue :l; } }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::BreakOutsideOfLoop,
			DiagnosticCode::ContinueOutsideOfLoop,
			DiagnosticCode::UndeclaredLabel,
			DiagnosticCode::ContinueOutsideOfLoop,
		]);
	}

	#[test]
	fn a_labelled_jump_is_recorded_as_a_reference_to_its_label() {
		const SOURCE: &str = "func f() { loop :outer { break :outer; } }";
		let case = TestCase::new(SOURCE);
		case.diagnostics().assert_none();
		let file_id = case
			.sema
			.decls
			.namespaces
			.file_id(Scope::Package(case.sema.decls.root_package).into());
		let start = (SOURCE.rfind(":outer").unwrap() + 1) as u32;
		let site = (
			crate::diagnostics::SourceSpan::new(
				file_id,
				TextSpan::new(start, start + "outer".len() as u32),
			),
			Tier::Value,
		);
		assert!(matches!(
			case.sema.resolutions.by_site.get(&site),
			Some(Resolution::Reference(Referent::Label { label, .. })) if u32::from(*label) == 0
		));
	}

	#[test]
	fn return_gives_the_function_its_value() {
		let case = TestCase::new(indoc! {"
				func early(c: Bool) -> u8 { if c { return 1; } 2 }
				func bare() { return; }
				func wrong() -> u8 { return; }
				func mismatch(a: u16) -> u8 { return a; }
			"});
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
		let case = TestCase::new(indoc! {"
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
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::CannotMutateImmutable,
			DiagnosticCode::InvalidAssignmentTarget,
			DiagnosticCode::TypeAnnotationRequired,
		]);
		assert_eq!(case.shape("f"), "(block (local x#0 1) (= x#0 2))");
	}

	#[test]
	fn a_global_is_a_handle_and_is_not_assigned() {
		let case = TestCase::new(indoc! {"
				global mut counter: u32 = 0;
				func f() {
					counter = 3;
					counter += 1;
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::InvalidAssignmentTarget,
			DiagnosticCode::InvalidAssignmentTarget,
		]);
		case.diagnostics().assert_error_saying(
			"a `global mut` is written with `counter.set(value)`",
		);
	}

	#[test]
	fn a_diverging_operand_takes_the_other_operands_type() {
		let case = TestCase::new(indoc! {"
				func stop() -> ! { loop {} }
				func left(x: i32) -> i32 { stop() + x }
				func right(x: i32) -> i32 { x + stop() }
				func compare(x: i32) -> Bool { x == stop() }
				func typed(x: u8) -> u8 { stop() + x }
				func literal() -> i32 { stop() + 1 }
				func nested() -> i32 { (stop() + 1) * 2 }
				func both() -> i32 { stop() + stop() }
				func takes(x: u8) -> u8 { x }
				func argument() -> u8 { takes(stop() + 1) }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.body_type("left"), "i32");
		assert_eq!(case.body_type("right"), "i32");
		assert_eq!(case.body_type("compare"), "Bool");
		assert_eq!(case.body_type("typed"), "u8");
		assert_eq!(case.body_type("literal"), "i32");
		assert_eq!(case.body_type("nested"), "i32");
		assert_eq!(case.body_type("argument"), "u8");
	}

	#[test]
	fn an_untyped_comparison_against_a_diverging_operand_needs_an_annotation() {
		let case = TestCase::new(indoc! {"
				func stop() -> ! { loop {} }
				func left() -> Bool { stop() == 1 }
				func right() -> Bool { 1 == stop() }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ComparisonTypeAnnotationRequired,
			DiagnosticCode::ComparisonTypeAnnotationRequired,
		]);
	}

	#[test]
	fn a_diverging_operand_does_not_skip_literal_coercion() {
		let case = TestCase::new(
			"func stop() -> ! { loop {} } func f() -> u8 { stop() + 256 }",
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
	}

	#[test]
	fn a_diverging_operand_does_not_make_a_literal_operable() {
		let case = TestCase::new(
			r#"func stop() -> ! { loop {} } func f() -> Bool { stop() == "x" }"#,
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics()
			.assert_error_saying("cannot apply `==` to a string literal");
	}

	#[test]
	fn a_diverging_operand_makes_a_unary_expression_diverge() {
		let case = TestCase::new(indoc! {"
				func stop() -> ! { loop {} }
				func negate() -> i32 { -stop() }
				func logical() -> Bool { !stop() }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.body_type("negate"), "!");
		assert_eq!(case.body_type("logical"), "!");
	}

	#[test]
	fn an_operator_call_carries_its_type_arguments() {
		let case = TestCase::new(indoc! {"
				struct W<T>(x: T);
				impl<T: StackValue> Add for W<T> { func add(self: Self, rhs: Self) -> Self { rhs } }
				func concrete(w: W<u8>) -> W<u8> { w + w }
				func generic<T: Add>(t: T) -> T { t + t }
				func assigned(w: W<u8>) { local mut v = w; v += w; }
			"});
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
		let case = TestCase::new(indoc! {"
				struct V(x: u32);
				impl Add for V { func add(self: Self, rhs: Self) -> Self { rhs } }
				func scalar() { local mut a: u32 = 1; a += 2; a <<= 1; }
				func overloaded(v: V) { local mut w = v; w += v; }
				func generic<T: Add>(t: T) { local mut u = t; u += t; }
				func missing(c: Bool) { local mut d = c; d -= c; }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
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
		let case = TestCase::new(indoc! {"
				struct Inner(v: u8);
				struct Outer(inner: Inner, n: u32);
				struct Wrap<T>(value: T);
				func read(o: Outer) -> u8 { o.inner.v }
				func generic(w: Wrap<u16>) -> u16 { w.value }
				func write(o: Outer) { local mut p = o; p.inner.v = 1; p.n += 1; }
				func immutable(o: Outer) { o.n = 1; }
				func temporary(o: Outer) { read(o).v = 1; }
			"});
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
		let case = TestCase::new(indoc! {"
				mod m { pub struct S(pub open: u8, closed: u8); }
				func f(s: m::S) -> u8 { s.open + s.closed }
				func g(s: m::S) -> u8 { s.missing }
				func h(x: u8) -> u8 { x.field }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::PrivateStructField,
			DiagnosticCode::UnknownStructField,
			DiagnosticCode::UnknownStructField,
		]);
	}

	#[test]
	fn a_field_takes_no_type_arguments() {
		let case = TestCase::new(indoc! {"
				struct P(x: u8);
				func f(p: P) -> u8 { p.x::<u8> }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeArgumentsNotAllowed]);
	}

	#[test]
	fn a_place_in_memory_is_read_written_and_addressed() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct Node(value: u32, next: heap::*Node);
				func read(p: heap::&Node) -> u32 { p.*.value }
				func write(p: heap::*Node) { p.* = Node(1, p); p.*.value += 2; }
				func value_address(p: heap::*Node) -> heap::&u32 { p.*.value.& }
				func next(p: heap::*Node) -> u32 { p.*.next.*.value }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("read"), "(block => (load (. (* p#0) value)))");
		assert_eq!(
			case.shape("write"),
			"(block (store (* p#0) (Node 1 p#0)) (store += (. (* p#0) value) 2))"
		);
		assert_eq!(
			case.shape("value_address"),
			"(block => (.& (. (* p#0) value)))"
		);
		assert_eq!(
			case.shape("next"),
			"(block => (load (. (* (load (. (* p#0) next))) value)))"
		);
	}

	#[test]
	fn a_place_is_written_only_through_an_exclusive_pointer() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func shared(p: heap::&u32) { p.* = 1; }
				func not_a_pointer(x: u32) -> u32 { x.* }
				func local_address(x: u32) -> heap::&u32 { x.& }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::CannotMutateImmutable,
			DiagnosticCode::CannotDerefNonPointer,
			DiagnosticCode::InvalidAssignmentTarget,
		]);
	}

	#[test]
	fn a_call_checks_its_arguments_against_the_parameters() {
		let case = TestCase::new(indoc! {"
				func add(a: u32, b: u32) -> u32 { a + b }
				func f() -> u32 { add(1, 2) }
				func count() -> u32 { add(1) }
				func mismatch(c: Bool) -> u32 { add(c, 2) }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::TypeMistmatch,
		]);
		assert_eq!(case.shape("f"), "(block => (call add 1 2))");
	}

	#[test]
	fn a_generic_call_learns_its_type_arguments() {
		let case = TestCase::new(indoc! {"
				trait Number {}
				impl Number for u32 {}
				impl Number for i64 {}
				func id<T: StackValue>(x: T) -> T { x }
				func zero<T: StackValue + Number>() -> T { loop {} }
				func from_argument(a: u16) -> u16 { id(a) }
				func from_expected() -> u8 { id(1) }
				func from_turbofish() { local x = zero::<i64>(); }
				func from_result() -> u32 { zero() }
				func nothing() { _ = zero(); }
				func unsatisfied() { local x = zero::<Bool>(); }
			"});
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
		let case = TestCase::new(indoc! {"
				func id<T: StackValue>(x: T) -> T { x }
				func f() { local g = id::<u8>; local h = id; }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeAnnotationRequired]);
		assert_eq!(case.locals("f")[0], ("g".into(), "id<u8>".into()));
	}

	#[test]
	fn a_function_item_held_in_a_value_is_called_through_call() {
		let case = TestCase::new(indoc! {"
				func id<T: StackValue>(x: T) -> T { x }
				func pair(a: u8, b: u16) {}
				func positional() -> u8 { local g = id::<u8>; g(1) }
				func named() { local g = pair; g({ b: 2, a: 1 }); }
				func shadowed(id: pair) { id(1, 2); }
				func counted() { local g = pair; g(1); }
				struct V(x: u32);
				impl V { func area(self: Self, k: u32) -> u32 { k } }
				func method(v: V) -> u32 { local m = V::area; m({ k: 1, self: v }) }
				trait Make: StackValue { func make(n: u32) -> Self; }
				func declared<T: StackValue + Make>() -> T { local g = T::make; g(1) }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ArgumentCountMismatch]);
		assert_eq!(
			case.shape("positional"),
			"(block (local g#0 id<u8>) => (abstract call<id<u8>> g#0 1))"
		);
		assert_eq!(
			case.shape("named"),
			"(block (local g#0 pair) (abstract call<pair> g#0 (tuple 1=2 0=1)))"
		);
		assert_eq!(
			case.shape("shadowed"),
			"(block (abstract call<pair> id#0 (tuple 1 2)))"
		);
		assert_eq!(
			case.shape("counted"),
			"(block (local g#0 pair) (abstract call<pair> g#0 (tuple)))"
		);
		assert_eq!(
			case.shape("method"),
			"(block (local m#1 area) => (abstract call<area> m#1 (tuple 1=1 \
			 0=v#0)))"
		);
		assert_eq!(case.body_type("declared"), "T");
		assert_eq!(
			case.shape("declared"),
			"(block (local g#0 make<T>) => (abstract call<<T as \
			 Make>::make> g#0 1))"
		);
	}

	#[test]
	fn a_tuple_of_one_is_its_element() {
		let case = TestCase::new(indoc! {"
				func f(x: (u8,)) -> u8 { local (y,) = x; local (z) = y; (z,) }
				func g(p: (u8, u16)) { local (..) = p; }
				func h(mut a: u8) { (a,) = 1; }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.locals("f"),
			[
				("x".into(), "u8".into()),
				("y".into(), "u8".into()),
				("z".into(), "u8".into())
			]
		);
		assert_eq!(
			case.shape("f"),
			"(block (local y#1 x#0) (local z#2 y#1) => z#2)"
		);
		assert_eq!(case.shape("g"), "(block (local (tuple _ _) p#0))");
	}

	#[test]
	fn a_value_is_called_through_its_call_impl() {
		let case = TestCase::new(indoc! {"
				struct Adder(n: u32);
				impl Call for Adder {
					type Args = (u32, u32);
					type Result = u32;
					func call(self: Self, args: (u32, u32)) -> u32 { 0 }
				}
				func spread(a: Adder) -> u32 { a(1, 2) }
				func whole(a: Adder, p: (u32, u32)) -> u32 { a(p) }
				func apply<F: Call>(f: F, x: F::Args) -> F::Result { f(x) }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("spread"),
			"(block => (call call a#0 (tuple 1 2)))"
		);
		assert_eq!(case.shape("whole"), "(block => (call call a#0 p#1))");
		assert_eq!(
			case.shape("apply"),
			"(block => (abstract call<F> f#0 x#1))"
		);
	}

	#[test]
	fn a_value_without_a_call_impl_cannot_be_called() {
		let case = TestCase::new(indoc! {"
				struct Adder(n: u32);
				impl Call for Adder {
					type Args = (u32, u32);
					type Result = u32;
					func call(self: Self, args: (u32, u32)) -> u32 { 0 }
				}
				func number(x: u32) { x(1); }
				func named(a: Adder) { a({ args: (1, 2) }); }
				func too_many(a: Adder) { _ = a(1, 2, 3); }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::PositionalOnlyCall,
			DiagnosticCode::ArgumentCountMismatch,
		]);
	}

	/// The parentheses of a call only mark it: when the arguments fill one
	/// parameter, the whole list is its value.
	#[test]
	fn the_argument_list_is_the_value_of_a_lone_parameter() {
		let case = TestCase::new(indoc! {"
				func g(p: (u8, u16)) {}
				func id<T: StackValue>(x: T) -> T { x }
				func unit(x: ()) {}
				struct W(x: (u8, u16));
				struct V();
				impl V { func m(self: Self, p: (u8, u16)) {} }
				func spread(a: u8, b: u16) { g(a, b); }
				func whole(a: u8, b: u16) { g((a, b)); }
				func named(a: u8, b: u16) { g({ p: (a, b) }); }
				func learned() -> (u8, u16) { id(1, 2) }
				func empty() { unit(); }
				func construct(a: u8, b: u16) -> W { W(a, b) }
				func method(v: V, a: u8, b: u16) { v.m(a, b); }
				func qualified(v: V, a: u8, b: u16) { V::m(v, (a, b)); }
				func item(a: u8, b: u16) { local k = g; k(a, b); }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("spread"), "(block (call g (tuple a#0 b#1)))");
		assert_eq!(case.shape("whole"), "(block (call g (tuple a#0 b#1)))");
		assert_eq!(
			case.shape("learned"),
			"(block => (call id<(u8, u16)> (tuple 1 2)))"
		);
		assert_eq!(case.shape("empty"), "(block (call unit (tuple)))");
		assert_eq!(
			case.shape("method"),
			"(block (call m v#0 (tuple a#1 b#2)))"
		);
	}

	/// Nothing is regrouped: a list of another length, one value that is no
	/// tuple for several parameters, or several for a lone parameter of a
	/// known type that is no such tuple, is a wrong count.
	#[test]
	fn the_argument_list_fills_several_parameters_one_each() {
		let case = TestCase::new(indoc! {"
				func f(a: u8, b: u16) {}
				func h(x: u32) {}
				struct V();
				impl V { func m(self: Self, p: (u8, u16)) {} }
				func missing(a: u8) { f(a); }
				func none() { h(); }
				func several() { h(1, 2); }
				func qualified(v: V, a: u8, b: u16) { V::m(v, a, b); }
			"});
		// The arguments that do fall on a parameter are still held to it.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::TypeMistmatch,
		]);
	}

	/// One value written for several parameters is their value as one, as
	/// the list they form would be: the call holds it whole.
	#[test]
	fn one_value_is_the_arguments_of_several_parameters() {
		let case = TestCase::new(indoc! {"
				func f(a: u8, b: u16) -> u16 { b }
				func none() {}
				struct Point(x: u8, y: u16);
				struct V();
				impl V { func m(self: Self, a: u8, b: u16) {} }
				func call(p: (u8, u16)) -> u16 { f(p) }
				func literal() -> u16 { f((1, 2)) }
				func unit() { none(()); }
				func construct(p: (u8, u16)) -> Point { Point(p) }
				func method(v: V, p: (u8, u16)) { v.m(p); }
				func qualified(t: (V, u8, u16)) { V::m(t); }
				func grouped(v: V, p: (u8, u16)) { V::m(v, p); }
			"});
		// `V::m(v, p)` is no regrouping: `p` falls on `a`.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::TypeMistmatch,
		]);
		assert_eq!(case.shape("call"), "(block => (call f p#0))");
		// The same call as `f(1, 2)`.
		assert_eq!(case.shape("literal"), "(block => (call f 1 2))");
		assert_eq!(case.shape("unit"), "(block (call none))");
		assert_eq!(case.shape("construct"), "(block => (Point p#0))");
		assert_eq!(case.shape("method"), "(block (call m v#0 p#1))");
		assert_eq!(case.shape("qualified"), "(block (call m t#0))");
	}

	/// A `call` of the wrong shape breaks the trait's contract, and still does
	/// not decide what the call takes: `Args` and `Result` are read from the
	/// impl.
	#[test]
	fn a_value_call_reads_args_and_result_from_its_call_impl() {
		let case = TestCase::new(indoc! {"
				struct X(n: u32);
				impl Call for X {
					type Args = u32;
					type Result = u32;
					func call(self: Self) -> u8 { 0 }
				}
				func f(x: X) -> u32 { x(1) }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		assert_eq!(case.body_type("f"), "u32");
	}

	#[test]
	fn a_function_item_is_not_a_function_reference() {
		let case = TestCase::new(indoc! {"
				func id<T: StackValue>(x: T) -> T { x }
				func f() { local g: func(u8) -> u8 = id; }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
	}

	#[test]
	fn a_function_reference_is_callable_by_a_compiler_rule() {
		let case = TestCase::new(indoc! {"
				func twice(f: func(u32) -> u32, x: u32) -> u32 { f(f(x)) }
				func spread(f: func(u32, u8) -> u8) -> u8 { f(1, 2) }
				func whole(f: func(u32, u8) -> u8, p: (u32, u8)) -> u8 { f(p) }
				func nothing(f: func()) { f(); }
				func apply<F: Call>(f: F, x: F::Args) -> F::Result { f(x) }
				func through(f: func(u32) -> u8) -> u8 { apply(f, 1) }
				func projected(x: <func(u32) -> u8 as Call>::Result) -> u8 { x }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("twice"),
			"(block => (call_ref f#0 (call_ref f#0 x#1)))"
		);
		assert_eq!(case.shape("spread"), "(block => (call_ref f#0 1 2))");
		assert_eq!(case.shape("whole"), "(block => (call_ref f#0 p#1))");
		assert_eq!(case.shape("nothing"), "(block (call_ref f#0))");
		assert_eq!(case.body_type("through"), "u8");
		assert_eq!(
			case.shape("through"),
			"(block => (call apply<func(u32) -> u8> f#0 1))"
		);
	}

	#[test]
	fn a_function_reference_has_call_as_a_method() {
		let case = TestCase::new(indoc! {"
				func one(f: func(u32) -> u8) -> u8 { f.call(1) }
				func two(f: func(u32, u8) -> u8) -> u8 { f.call(1, 2) }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("one"),
			"(block => (abstract call<func(u32) -> u8> f#0 1))"
		);
		assert_eq!(
			case.shape("two"),
			"(block => (abstract call<func(u32, u8) -> u8> f#0 (tuple 1 2)))"
		);
	}

	#[test]
	fn a_function_reference_is_called_by_position_with_its_parameter() {
		let case = TestCase::new(indoc! {"
				func named(f: func(u32) -> u32) { _ = f({ x: 1 }); }
				func too_many(f: func(u32, u8) -> u8) { _ = f(1, 2, 3); }
				func wrong(f: func(u32) -> u32) { _ = f(True); }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::PositionalOnlyCall,
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::TypeMistmatch,
		]);
	}

	#[test]
	fn a_computed_function_item_is_evaluated_as_the_receiver() {
		let case = TestCase::new(indoc! {"
				func pair(a: u8, b: u16) {}
				func make() -> pair { pair }
				func f() { make()({ b: 2, a: 1 }); }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block (abstract call<pair> (call make) (tuple 1=2 0=1)))"
		);
	}

	#[test]
	fn an_expected_item_type_gives_a_function_value_its_arguments() {
		let case = TestCase::new(indoc! {"
				func id<T: StackValue>(x: T) -> T { x }
				func take(g: id<u8>) {}
				func annotated() { local g: id<u8> = id; }
				func argument() { take(id); }
				func returned() -> id<u16> { id }
				func generic<T: StackValue>() { local g: id<T> = id; }
				func other() { local g: id<u8> = take; }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
		assert_eq!(case.locals("annotated"), [("g".into(), "id<u8>".into())]);
		assert_eq!(case.shape("argument"), "(block (call take id<u8>))");
		assert_eq!(case.shape("returned"), "(block => id<u16>)");
		assert_eq!(case.locals("generic"), [("g".into(), "id<T>".into())]);
	}

	#[test]
	fn a_string_literal_takes_a_byte_slice_or_array_from_its_context() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func slice() -> heap::&[u8] { "hello" }
				func array() -> heap::&[u8; 5] { "hello" }
				func escaped() -> heap::&[u8; 2] { "a\n" }
				func annotated() { local s: heap::&[u8; 3] = "abc"; }
				func branches(c: Bool) -> heap::&[u8] { if c { "yes" } else { "no" } }
				func tuple() -> (heap::&[u8], u8) { ("a", 1) }
				func any_memory<Mem: Memory>() -> Mem::&[u8] { "abstract" }
			"#});
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
	fn an_array_literal_takes_a_shared_array_or_slice_from_its_context() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				memory wide: u64;
				const SIZE: u32 = 3;
				func slice() -> heap::&[u32] { [1, 2, 3] }
				func array() -> heap::&[u8; 2] { [1, 2] }
				func empty() -> heap::&[u8] { [] }
				func annotated() { local a: heap::&[u8; 1] = [9]; }
				func nested() -> heap::&[heap::&[u8]] { [[1], [2, 3]] }
				func repeat() -> heap::&[u16; 4] { [0; 4] }
				func repeat_constant() -> heap::&[u16; 3] { [7; SIZE] }
				func repeat_wide() -> wide::&[u8; 5] { [1; 5] }
				func any_memory<Mem: Memory>() -> Mem::&[u8; 2] { [1; 2] }
			"#});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("slice"), "(block => (array 1 2 3))");
		assert_eq!(case.body_type("slice"), "heap::&[u32]");
		assert_eq!(case.body_type("array"), "heap::&[u8; 2]");
		assert_eq!(case.body_type("empty"), "heap::&[u8]");
		assert_eq!(
			case.locals("annotated"),
			[("a".into(), "heap::&[u8; 1]".into())]
		);
		assert_eq!(case.body_type("nested"), "heap::&[heap::&[u8]]");
		assert_eq!(case.shape("repeat"), "(block => (repeat 0 4))");
		assert_eq!(case.body_type("repeat_constant"), "heap::&[u16; 3]");
		assert_eq!(case.body_type("repeat_wide"), "wide::&[u8; 5]");
		assert_eq!(case.body_type("any_memory"), "Mem::&[u8; 2]");
		// A repeat's count is a length in its memory, of its `Size`.
		let body = case.body("repeat_wide");
		let ExprKind::ArrayRepeat {
			count: Some(count), ..
		} = body.kind(body.statics()[0])
		else {
			panic!("expected a repeat");
		};
		assert_eq!(body.ty(count), TypeIndex::U64);
		// Every literal is static data, an inner one before its outer one.
		let body = case.body("nested");
		let lengths: Vec<usize> = body
			.statics()
			.iter()
			.map(|&expr| match body.kind(expr) {
				ExprKind::Array { elements } => elements.len(),
				_ => panic!("expected an array literal"),
			})
			.collect();
		assert_eq!(lengths, [1, 2, 2]);
	}

	#[test]
	fn an_array_literal_is_only_what_its_context_allows() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const LONG: u64 = 2;
				func exclusive() -> heap::*[u8] { [1] }
				func number() -> u32 { [1] }
				func too_long() -> heap::&[u8; 2] { [1, 2, 3] }
				func repeat_too_long() -> heap::&[u8; 2] { [0; 3] }
				func element() -> heap::&[u8] { [True] }
				func count_type() -> heap::&[u8; 2] { [0; LONG] }
				func computed(n: u32) -> heap::&[u8; 2] { [0; n] }
				func computed_slice(n: u32) -> heap::&[u8] { [0; n] }
				func untyped() { local a = [1]; }
				func operator() -> heap::&[u8] { [1] + [2] }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::ArraySizeMismatch,
			DiagnosticCode::ArraySizeMismatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::ArrayRepeatCountNotConst,
			DiagnosticCode::ArrayRepeatCountNotConst,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TraitBoundViolation,
		]);
	}

	/// A literal's elements are constant expressions: a local of the function
	/// is found (it still shadows an item) and reported, and a local declared
	/// inside the literal is the evaluator's to reject, with the block holding
	/// it.
	#[test]
	fn a_local_cannot_be_used_in_static_data() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const x: u8 = 5;
				func param(x: u8) -> heap::&[u8] { [x, 1] }
				func declared() -> heap::&[u8] { local y: u8 = 1; [y] }
				func inner() -> heap::&[u8] { [block { local z: u8 = 1; z }] }
				func outside(x: u8) -> heap::&[u8; 2] { [0; 2] }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::LocalInStaticData,
			DiagnosticCode::LocalInStaticData,
			DiagnosticCode::NotConstEvaluatable,
		]);
	}

	/// A function's static data is evaluated when the function is checked, so
	/// what fails in it is reported by `wx check`; a generic function's is
	/// evaluated per instance, where it is lowered.
	#[test]
	fn static_data_is_evaluated_when_its_function_is_checked() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func one() -> u8 { 1 }
				func call() -> heap::&[u8] { [one(), 1] }
				func overflow() -> heap::&[u8] { [200 + 100] }
				func nested() -> heap::&[heap::&[u8]] { [[one()]] }
				func generic<T>() -> heap::&[u8] { [one()] }
				func fine() -> heap::&[u16] { [1, 2 + 3, 4] }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NotConstEvaluatable,
			DiagnosticCode::ConstEvaluationFailed,
			DiagnosticCode::NotConstEvaluatable,
		]);
	}

	#[test]
	fn a_body_records_its_string_literals_as_static_data() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func branches(c: Bool) -> heap::&[u8] { if c { "yes" } else { "no" } }
				func none() -> u32 { 1 }
			"#});
		case.diagnostics().assert_none();
		let body = case.body("branches");
		let contents: Vec<&str> = body
			.statics()
			.iter()
			.map(|&expr| {
				let ExprKind::String(symbol) = body.kind(expr) else {
					panic!("expected a string literal");
				};
				case.strings.resolve(symbol).unwrap()
			})
			.collect();
		assert_eq!(contents, ["yes", "no"]);
		assert!(case.body("none").statics().is_empty());
	}

	#[test]
	fn a_string_literal_waits_for_a_generic_call_to_learn_its_memory() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func take<Mem: Memory>(s: Mem::&[u8], p: Mem::&u8) {}
				func call(p: heap::&u8) { take("abc", p); }
			"#});
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_string_literal_is_a_shared_byte_type_of_its_length() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func length() -> heap::&[u8; 4] { "abc" }
				func exclusive() -> heap::*[u8] { "abc" }
				func number() -> u32 { "abc" }
				func untyped() { local s = "abc"; }
				func operator() -> heap::&[u8] { "a" + "b" }
				func negate() -> heap::&[u8] { -"a" }
				func expected(c: Bool) -> heap::&[u8] { if c { "a" } else { 1 } }
				func joined(c: Bool) { local x = if c { "a" } else { 1 }; }
				func escape() -> heap::&[u8] { "\q" }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArraySizeMismatch,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::UnknownCharacterEscape,
		]);
		case.diagnostics().assert_error_saying(
			"this string literal is 3 bytes long, but `heap::&[u8; 4]` holds 4",
		);
	}

	#[test]
	fn a_string_literal_is_ascribed_what_it_can_become() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func array() -> heap::&[u8; 3] { ("abc": heap::&[u8; 3]) }
				func slice() -> heap::&[u8] { ("abc": heap::&[u8]) }
				func number() -> u32 { ("abc": u32) }
				func exclusive() -> heap::*[u8] { ("abc": heap::*[u8]) }
				func length() -> heap::&[u8; 2] { ("abc": heap::&[u8; 2]) }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::ArraySizeMismatch,
		]);
		assert_eq!(case.shape("array"), r#"(block => "abc")"#);
	}

	#[test]
	fn an_array_literal_is_ascribed_what_it_can_become() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func array() -> heap::&[u8; 2] { ([1, 2]: heap::&[u8; 2]) }
				func slice() -> heap::&[u32] { ([1, 2]: heap::&[u32]) }
				func repeat() -> heap::&[u8; 3] { ([0; 3]: heap::&[u8; 3]) }
				func inferred() { local a = ([1]: heap::&[u16]); }
				func number() -> u32 { ([1]: u32) }
				func pointer() -> heap::*u32 { ([1]: heap::*u32) }
				func exclusive() -> heap::*[u8] { ([1]: heap::*[u8]) }
				func length() -> heap::&[u8; 2] { ([1]: heap::&[u8; 2]) }
				func element() -> heap::&[u8] { ([True]: heap::&[u8]) }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::ArraySizeMismatch,
			DiagnosticCode::TypeMistmatch,
		]);
		assert_eq!(case.shape("array"), "(block => (array 1 2))");
		assert_eq!(
			case.locals("inferred"),
			[("a".into(), "heap::&[u16]".into())]
		);
	}

	#[test]
	fn constant_parameters_and_arguments_are_not_checked_yet() {
		let case = TestCase::new(indoc! {r#"
				struct Buffer<const N: u32>(u8);
				func f(b: Buffer<4>) {}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnsupportedExpression,
			DiagnosticCode::UnsupportedExpression,
		]);
	}

	#[test]
	fn a_constant_value_in_a_bound_is_not_checked_yet() {
		// Representability (`const LEN: u8`) is a clause; a value (`const LEN =
		// 4`) is not supported yet.
		let case = TestCase::new(indoc! {r#"
				func g<A: Array where { const LEN: u8 }, B: Array where { const LEN = 4 }>() {}
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnsupportedExpression]);
	}

	#[test]
	fn an_abstract_constant_is_representable_as_what_a_bound_says() {
		// `u8` gives `u16`, not `i8`.
		let case = TestCase::new(indoc! {r#"
				func f<A: Array where { const LEN: u8 }>() -> u8 { A::LEN }
				func wider<A: Array where { const LEN: u8 }>() -> u16 { A::LEN }
				func signed<A: Array where { const LEN: u8 }>() -> i8 { A::LEN }
				func none<A: Array>() -> u8 { A::LEN }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnrepresentableConstant,
			DiagnosticCode::UnrepresentableConstant,
		]);
		case.diagnostics().assert_error_saying(
			"constant `<A as Array>::LEN` cannot be represented as `i8`",
		);
		case.diagnostics().assert_error_saying(
			"constant `<A as Array>::LEN` cannot be represented as `u8`",
		);
	}

	#[test]
	fn representability_is_proved_at_a_call() {
		let case = TestCase::new(indoc! {r#"
				func f<A: Array where { const LEN: u8 }>() {}
				func representable() { f::<[u16; 255]>() }
				func overflows() { f::<[u16; 256]>() }
				func implied<B: Array where { const LEN: u8 }>() { f::<B>() }
				func wider<B: Array where { const LEN: u16 }>() { f::<B>() }
				func unstated<B: Array>() { f::<B>() }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnrepresentableConstant,
			DiagnosticCode::UnrepresentableConstant,
			DiagnosticCode::UnrepresentableConstant,
		]);
		case.diagnostics().assert_error_saying(
			"constant `<[u16; 256] as Array>::LEN` cannot be represented as `u8`",
		);
	}

	#[test]
	fn representability_as_a_memory_size_is_read_through_its_typesets() {
		// `M::Size` is `u32` or `u64`: it gives `u32`, not `u16`, and `u8`
		// gives it.
		let case = TestCase::new(indoc! {r#"
				func f<M: Memory, A: Array where { const LEN: M::Size }>() -> M::Size { A::LEN }
				func narrow<M: Memory, A: Array where { const LEN: M::Size }>() -> u32 { A::LEN }
				func narrower<M: Memory, A: Array where { const LEN: M::Size }>() -> u16 { A::LEN }
				func small<M: Memory, A: Array where { const LEN: u8 }>() -> M::Size { A::LEN }
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnrepresentableConstant]);
		case.diagnostics().assert_error_saying(
			"constant `<A as Array>::LEN` cannot be represented as `u16`",
		);
	}

	#[test]
	fn representability_is_inherited_from_a_supertraits_bound() {
		let case = TestCase::new(indoc! {r#"
				trait Small: Array where { const LEN: u8 } {}
				func f<A: Small>() -> u8 { A::LEN }
				func g<A: Small>() -> i8 { A::LEN }
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnrepresentableConstant]);
	}

	#[test]
	fn a_bound_states_representability_of_an_untyped_constant_only() {
		let case = TestCase::new(indoc! {r#"
				trait Sized { const SIZE: u32; type Item; const FIRST: Self::Item; }
				func typed<T: Sized where { const SIZE: u8 }>() {}
				func projected<T: Sized where { const FIRST: u8 }>() {}
				func untyped<A: Array where { const LEN: u8 }>() {}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypedConstantBound,
			DiagnosticCode::TypedConstantBound,
		]);
		case.diagnostics().assert_error_saying(
			"constant `SIZE` has a type, so a bound cannot state what it is \
			 representable as",
		);
	}

	#[test]
	fn a_trait_function_bounding_self_assumes_it_in_its_body() {
		// `Self` written first is no parameter: `f` takes one argument.
		let case = TestCase::new(indoc! {r#"
				trait Show: StackValue { func show(self: Self); }
				trait Tr: StackValue {
					func f<Self: Show, T: StackValue>(self: Self, t: T) { self.show() }
					func g<Self: Show>(self: Self) { self.show() }
				}
				func call<X: StackValue + Tr + Show>(x: X) { x.f::<u8>(1); x.g() }
			"#});
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_call_proves_what_a_trait_function_requires_of_self() {
		let case = TestCase::new(indoc! {r#"
				trait Show: StackValue { func show(self: Self); }
				trait Tr: StackValue {
					func f<Self: Show>(self: Self) { self.show() }
				}
				struct A();
				impl Tr for A {}
				struct B();
				impl Show for B { func show(self: Self) {} }
				impl Tr for B {}
				func concrete(a: A, b: B) { a.f(); b.f() }
				func generic<X: StackValue + Tr>(x: X) { x.f() }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
		]);
		case.diagnostics()
			.assert_error_saying("the trait bound `A: Show` is not satisfied");
		case.diagnostics()
			.assert_error_saying("the trait bound `X: Show` is not satisfied");
	}

	#[test]
	fn a_bound_is_reported_where_its_argument_is_given() {
		let source = indoc! {r#"
			trait Show { func show(self: Self); }
			trait Tr { func f<Self: Show>(self: Self) {} }
			struct A();
			impl Tr for A {}
			func g<T: Show, U: Show>(t: T, u: U) {}
			func h<T: Show>() {}
			func calls(first: A, second: A, third: A) {
				g(first, second);
				h::<A>();
				third.f()
			}
		"#};
		let case = TestCase::new(source);
		case.diagnostics().print();
		let at: Vec<&str> = case
			.sema
			.diagnostics
			.iter()
			.filter(|diagnostic| {
				diagnostic.code.as_deref()
					== Some(DiagnosticCode::TraitBoundViolation.code())
			})
			.map(|diagnostic| &source[diagnostic.labels[0].range.clone()])
			.collect();
		assert_eq!(at, ["first", "second", "A", "third"]);
	}

	#[test]
	fn self_is_bounded_only_first_in_a_trait_function() {
		let case = TestCase::new(indoc! {r#"
				trait Show {}
				trait Tr: StackValue {
					func late<T: StackValue, Self: Show>(t: T);
					func f(self: Self);
				}
				struct S<Self>(u8);
				func free<Self: Show>() {}
				impl S { func inherent<Self: Show>() {} }
				impl Tr for S {
					func late<T: StackValue>(t: T) {}
					func f(self: Self) {}
				}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::MisplacedSelfBound,
			DiagnosticCode::MisplacedSelfBound,
			DiagnosticCode::MisplacedSelfBound,
			DiagnosticCode::MisplacedSelfBound,
		]);
	}

	/// What the trait impls below share: `Container::show_all` requires its
	/// items to be shown, `Wrap<T>`'s items are `T`.
	const SHOWN_ITEMS: &str = indoc! {r#"
		trait Show: StackValue { func show(self: Self); }
		trait Container: StackValue {
			type Item;
			func show_all<Self: Container where { Item: Show }>(self: Self);
		}
		struct Wrap<T>(inner: T);
	"#};

	#[test]
	fn a_trait_impl_function_assumes_what_its_self_entry_means() {
		// `<Wrap<T> as Container>::Item: Show` means `T: Show` in the impl.
		let case = TestCase::new(&format!(
			"{SHOWN_ITEMS}{}",
			indoc! {r#"
					impl<T: StackValue> Container for Wrap<T> {
						type Item = T;
						func show_all<Self: Container where { Item: Show }>(
							self: Self,
						) {
							self.inner.show()
						}
					}
				"#}
		));
		case.diagnostics().assert_none();
	}

	#[test]
	fn without_its_self_entry_a_trait_impl_function_assumes_nothing() {
		let case = TestCase::new(&format!(
			"{SHOWN_ITEMS}{}",
			indoc! {r#"
					impl<T: StackValue> Container for Wrap<T> {
						type Item = T;
						func show_all(self: Self) { self.inner.show() }
					}
				"#}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::MethodNotFound]);
	}

	#[test]
	fn a_self_entry_reads_in_its_function_signature_checks() {
		// `Shown<Self::Item>` needs `Item: Show`, which only the entry gives.
		let case = TestCase::new(indoc! {r#"
				trait Show: StackValue { func show(self: Self); }
				struct Shown<X: Show>(x: X);
				trait Container {
					type Item;
					func shown<Self: Container where { Item: Show }>(
						item: Shown<Self::Item>,
					);
				}
				struct Wrap<T>(inner: T);
				impl<T> Container for Wrap<T> {
					type Item = T;
					func shown<Self: Container where { Item: Show }>(
						item: Shown<Self::Item>,
					) {}
				}
			"#});
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_self_entry_about_a_concrete_item_is_proved_where_it_is_written() {
		let case = TestCase::new(&format!(
			"{SHOWN_ITEMS}{}",
			indoc! {r#"
					struct Bytes();
					struct Text();
					impl Show for Text { func show(self: Self) {} }
					struct Bag();
					impl Container for Bag {
						type Item = Bytes;
						func show_all<Self: Container where { Item: Show }>(
							self: Self,
						) {}
					}
					struct Page();
					impl Container for Page {
						type Item = Text;
						func show_all<Self: Container where { Item: Show }>(
							self: Self,
						) {}
					}
				"#}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `<Bag as Container>::Item: Show` is not satisfied",
		);
	}

	#[test]
	fn a_call_of_a_trait_impl_function_proves_its_self_entry() {
		let case = TestCase::new(&format!(
			"{SHOWN_ITEMS}{}",
			indoc! {r#"
					impl<T: StackValue> Container for Wrap<T> {
						type Item = T;
						func show_all<Self: Container where { Item: Show }>(
							self: Self,
						) {
							self.inner.show()
						}
					}
					struct No();
					struct Yes();
					impl Show for Yes { func show(self: Self) {} }
					func calls(no: Wrap<No>, yes: Wrap<Yes>) {
						no.show_all();
						yes.show_all()
					}
				"#}
		));
		// Reported at the method for now; at the receiver, which gives
		// `Self`, is 6d-3.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `<Wrap<No> as Container>::Item: Show` is not \
			 satisfied",
		);
	}

	#[test]
	fn a_self_entry_assumes_only_about_an_abstract_type() {
		// `Wrap2<T>: Show` would hold only if `T: Show`, which nothing reads
		// from an assumption about `Wrap2<T>`; `Always<T>: Show` holds anyway.
		let case = TestCase::new(&format!(
			"{SHOWN_ITEMS}{}",
			indoc! {r#"
					struct Wrap2<T>(x: T);
					impl<T: StackValue + Show> Show for Wrap2<T> { func show(self: Self) {} }
					struct Always<T>(x: T);
					impl<T: StackValue> Show for Always<T> { func show(self: Self) {} }
					struct Nest<T>(inner: T);
					impl<T: StackValue> Container for Nest<T> {
						type Item = Wrap2<T>;
						func show_all<Self: Container where { Item: Show }>(
							self: Self,
						) {}
					}
					struct Keep<T>(inner: T);
					impl<T: StackValue> Container for Keep<T> {
						type Item = Always<T>;
						func show_all<Self: Container where { Item: Show }>(
							self: Self,
						) {}
					}
				"#}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnsupportedExpression]);
		case.diagnostics().assert_error_saying(
			"assuming `Wrap2<T>: Show` is not supported yet",
		);
	}

	#[test]
	fn a_self_entry_is_compared_with_its_declarations_meaning() {
		// The declaration's entry, read with `Self` as `Wrap<T>`, means
		// `T: Show`, which the impl's own entry asks no more than; asking
		// for `Item: Eq` beside it is more than the trait does.
		let case = TestCase::new(indoc! {r#"
				trait Show: StackValue { func show(self: Self); }
				trait Eq: StackValue { func eq(self: Self, other: Self); }
				trait Container: StackValue {
					type Item;
					func pair<Self: Container where { Item: Show }, U: StackValue>(
						self: Self,
						u: U,
					);
					func single<Self: Container where { Item: Show }>(
						self: Self,
					);
				}
				struct Wrap<T>(inner: T);
				impl<T: StackValue> Container for Wrap<T> {
					type Item = T;
					func pair<Self: Container where { Item: Show }, U: StackValue>(
						self: Self,
						u: U,
					) {
						self.inner.show()
					}
					func single<
						Self: Container where { Item: Show + Eq },
					>(self: Self) {}
				}
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
	}

	#[test]
	fn a_self_entry_equality_is_assumed_or_proved() {
		let source = indoc! {r#"
				trait Container: StackValue {
					type Item;
					func of_bytes<Self: Container where { Item = u8 }>(
						self: Self,
					);
				}
				struct Bytes();
				impl Container for Bytes {
					type Item = u8;
					func of_bytes<Self: Container where { Item = u8 }>(
						self: Self,
					) {}
				}
				struct Words();
				impl Container for Words {
					type Item = u16;
					func of_bytes<Self: Container where { Item = u8 }>(
						self: Self,
					) {}
				}
				struct Any<T>(x: T);
				impl<T: StackValue> Container for Any<T> {
					type Item = T;
					func of_bytes<Self: Container where { Item = u8 }>(
						self: Self,
					) {}
				}
			"#};
		let case = TestCase::new(source);
		// `u8 == u8` holds, `u16 == u8` never does, and `T == u8` would be
		// an assumption about a parameter's value. Each is reported at the
		// equality itself.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::AssocTypeEqualityMismatch,
			DiagnosticCode::UnassumableEquality,
		]);
		case.diagnostics().assert_error_saying(
			"`<Any<T> as Container>::Item` is `T`, which a bound cannot \
			 require to be `u8`",
		);
		let at: Vec<&str> = case
			.sema
			.diagnostics
			.iter()
			.map(|diagnostic| &source[diagnostic.labels[0].range.clone()])
			.collect();
		assert_eq!(at, ["Item = u8", "Item = u8"]);
	}

	#[test]
	fn an_array_type_length_is_an_integer_literal_or_a_constant() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				memory wide: u64;
				const N: u32 = 2;
				func literal(a: heap::&[u8; 2]) {}
				func constant(a: heap::&[u8; N]) {}
				func not_integer(a: heap::&[u8; True]) {}
				func too_long(a: heap::&[u8; 5000000000]) {}
				func long(a: wide::&[u8; 5000000000]) {}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::IntegerLiteralOutOfRange,
		]);
	}

	#[test]
	fn a_constant_length_means_its_value() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				struct Buffer(data: heap::&[u8; TWO]);
				const TWO: u32 = 1 + 1;
				func same(a: heap::&[u8; TWO]) -> heap::&[u8; 2] { a }
				func text() { local s: heap::&[u8; TWO] = "ab"; }
				func repeat() { local z: heap::&[u8; TWO] = [0; _]; }
				func long() { local s: heap::&[u8; TWO] = "abc"; }
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ArraySizeMismatch]);
	}

	#[test]
	fn a_constant_length_has_its_memorys_size_type() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const SHORT: u16 = 2;
				const N: u32 = 2;
				func narrow(a: heap::&[u8; SHORT]) {}
				func abstract<M: Memory>(a: M::&[u8; N]) {}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
		]);
	}

	#[test]
	fn a_length_path_names_a_free_constant() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				trait Sized { const SIZE: u32; }
				func f() {}
				func function(a: heap::&[u8; f]) {}
				func missing(a: heap::&[u8; NOPE]) {}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArrayRepeatCountNotConst,
			DiagnosticCode::UndeclaredIdentifier,
		]);
	}

	#[test]
	fn a_length_names_a_constant_of_a_type() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				trait Sized { const SIZE: u32; }
				struct P();
				impl Sized for P { const SIZE: u32 = 3; }
				impl P { const OWN: u32 = 2; }
				type A = [u8; 4];
				func of_param<T: Sized>(a: heap::&[u8; T::SIZE]) {
					local b: heap::&[u8; T::SIZE] = a;
				}
				func of_impl(a: heap::&[u8; P::SIZE]) { local b: heap::&[u8; 3] = a; }
				func inherent(a: heap::&[u8; P::OWN]) { local b: heap::&[u8; 2] = a; }
				func of_array(a: heap::&[u8; A::LEN]) { local b: heap::&[u8; 4] = a; }
				func caller(a: heap::&[u8; 3]) { of_param::<P>(a); }
				func of_array_len<T: Array>(a: heap::&[u8; T::LEN]) {}
				func call(x: heap::&[u8; 3]) { of_array_len::<[u16; 3]>(x); }
				func abstract<M: Memory, T: Array>(a: M::&[u8; T::LEN]) {}
				trait Takes: StackValue { const K: u32; func f(self: Self, a: heap::&[u8; Self::K]); }
				impl Takes for P { const K: u32 = 1; func f(self: Self, a: heap::&[u8; 1]) {} }
				func qualified<T: Sized>(a: heap::&[u8; <T as Sized>::SIZE]) {}
				func of_written(a: heap::&[u8; <[u8; 4]>::LEN]) {
					local b: heap::&[u8; 4] = a;
				}
				func counted() {
					local a: heap::&[u8; 3] = [0; <P as Sized>::SIZE];
				}
				const C: heap::&[u8; <P as Sized>::SIZE] = [7; _];
			"#});
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_length_through_a_type_is_checked_as_any_constant() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				trait Sized { const SIZE: u32; }
				trait Wide { const N: u64; }
				struct P();
				impl Sized for P { const SIZE: u32 = 3; }
				func of_param<T: Sized>(a: heap::&[u8; T::SIZE]) {}
				func unbound<T>(a: heap::&[u8; T::SIZE]) {}
				func no_such(a: heap::&[u8; P::NOPE]) {}
				func wide<T: Wide>(a: heap::&[u8; T::N]) {}
				func wrong(a: heap::&[u8; 2]) { of_param::<P>(a); }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NotATraitMember,
			DiagnosticCode::NotATraitMember,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
		]);
		case.diagnostics().assert_error_saying(
			"no associated constant named `SIZE` found for this type",
		);
		case.diagnostics().assert_error_saying(
			"an array's length is a `u32`, but `N` is a `u64`",
		);
	}

	#[test]
	fn a_constant_named_in_a_type_inside_its_own_value_is_a_cycle() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const C: u32 = block {
					local a: heap::&[u8; C] = [0; _];
					1
				};
			"#});
		// The local's type is compared once `C` has a value, and `C` has none
		// until its body is checked: rustc's `typeck(C)` to `eval(C)` and back.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicConstant]);
	}

	#[test]
	fn a_constant_whose_value_needs_its_own_type_is_a_cycle() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const A: heap::&[u8; A] = [0; _];
			"#});
		// `[0; _]` is as long as `A`'s type says, which is `A`'s value. The
		// constant owns the loop; the checks that met it are silent.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicConstant]);
	}

	#[test]
	fn a_constant_body_may_name_a_later_constant_in_a_type() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				struct Buf(data: heap::&[u8; N]);
				const N: u32 = M * 2;
				const TEXT: heap::&[u8; N] = "abcdefgh";
				const COPY: heap::&[u8; 8] = TEXT;
				const ZEROS: heap::&[u8; 8] = [0; N];
				const M: u32 = 4;
			"#});
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_length_named_by_a_later_constant_is_checked_once_it_is_known() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const TEXT: heap::&[u8; N] = "abc";
				const COPY: heap::&[u8; 2] = TEXT;
				const ZEROS: heap::&[u8; 2] = [0; N];
				const N: u32 = 4;
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArraySizeMismatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::ArraySizeMismatch,
		]);
	}

	#[test]
	fn a_length_check_is_decided_after_the_body_is_built() {
		// Building a body never reads a value, so the length of `"ab"` is
		// compared with `N` after what the body could decide itself, in a
		// constant's and in a function's alike; the constant waits for the
		// other constants, the function does not.
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const N: u32 = 4;
				const IN_CONSTANT: (heap::&[u8; N], u8) = ("ab", True);
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::ArraySizeMismatch,
		]);
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const N: u32 = 4;
				func in_function() {
					local t: (heap::&[u8; N], u8) = ("ab", True);
				}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::ArraySizeMismatch,
		]);
	}

	/// The scope and type of the first parameter of the function `name`.
	fn first_param(case: &TestCase, name: &str) -> (GenericEnvIdx, TypeIndex) {
		let DeclKind::Function(index) = case.resolve(name) else {
			panic!("expected `{name}` to be a function");
		};
		let signature = &case.sema.functions[usize::from(index)];
		(
			signature.type_params,
			case.sema.types.list(signature.param_types)[0],
		)
	}

	#[test]
	fn a_named_length_is_kept_unless_values_are_read() {
		let mut case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const N: u32 = 4;
				func named(a: heap::&[u8; N]) {}
				func written(a: heap::&[u8; 4]) {}
			"#});
		case.diagnostics().assert_none();
		let (scope, named) = first_param(&case, "named");
		let (_, written) = first_param(&case, "written");
		let without_values = RewriteFlags::ALL.without(RewriteFlags::VALUES);
		let mut normalize = |ty, facts| {
			case.sema
				.normalize(
					&case.strings,
					case.sema.assumption_envs.of_frame(scope),
					ty,
					NormalizationDepth::Deep,
					facts,
				)
				.unwrap()
		};
		// The two requests differ only in the facts, and neither is answered
		// from the other's cache entry, whichever is asked first.
		for _ in 0..2 {
			assert_eq!(normalize(named, without_values), named);
			assert_eq!(normalize(named, RewriteFlags::ALL), written);
		}
		// A type that cannot reach a constant means the same either way.
		assert_eq!(normalize(written, without_values), written);
		assert_eq!(normalize(written, RewriteFlags::ALL), written);
		assert!(case.sema.types.has_const(named));
		assert!(!case.sema.types.has_const(written));
	}

	#[test]
	fn a_match_in_a_constant_reads_later_constants() {
		let case = TestCase::new(indoc! {r#"
				const PICK: u8 = match ON {
					const YES => { 1 },
					const NO => { 0 },
				};
				const ON: Bool = True;
				const YES: Bool = True;
				const NO: Bool = False;
				const SIDE: u8 = match Side::Left {
					Side::Left => { 1 },
					Side::Right => { 2 },
				};
				enum Side(u8) { Left = 0, Right = 1 }
			"#});
		// Both matches are exhaustive once the constants they read are known;
		// a match is not evaluated (yet), which is all that is reported.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NotConstEvaluatable,
			DiagnosticCode::NotConstEvaluatable,
		]);
	}

	#[test]
	fn an_array_length_in_an_abstract_memory_is_representable_as_every_size() {
		let case = TestCase::new(indoc! {r#"
				func short<M: Memory>(a: M::&[u8; 5]) {}
				func long<M: Memory>(a: M::&[u8; 5000000000]) {}
				func local<M: Memory>() {
					local a: M::&[u8; 5000000000] = [0; _];
				}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypesetBoundViolation,
			DiagnosticCode::TypesetBoundViolation,
		]);
	}

	#[test]
	fn an_inferred_length_is_the_literals() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func f() {
					local s: heap::&[u8; _] = "abc";
					local t: heap::&[u8; 3] = s;
					local a: heap::&[u16; _] = [1, 2];
					local b: heap::&[u16; 2] = a;
					local z: heap::&[u8; 4] = [0; _];
				}
				func mismatch() {
					local s: heap::&[u8; _] = "abc";
					local t: heap::&[u8; 4] = s;
				}
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
	}

	#[test]
	fn an_inferred_length_needs_an_array_to_learn_from() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				func signature(a: heap::&[u8; _]) {}
				func slice() { local z: heap::&[u8] = [0; _]; }
				func neither() { local z: heap::&[u8; _] = [0; _]; }
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::InferInSignature,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TypeAnnotationRequired,
		]);
	}

	#[test]
	fn enums_and_pointers_compare_natively() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func less(o: Ordering) -> Bool { o == Ordering::Less }
				func same(a: heap::&u8, b: heap::&u8) -> Bool { a != b }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("less"), "(block => (== o#0 Less))");
	}

	#[test]
	fn a_constant_comparing_variants_is_evaluated() {
		let case = TestCase::new(
			"const SAME: Bool = Ordering::Less == Ordering::Greater;",
		);
		case.diagnostics().assert_none();
		let DeclKind::Const(index) = case.resolve("SAME") else {
			panic!("expected a constant");
		};
		assert_eq!(
			case.sema.solver.const_values[usize::from(index)],
			ConstValueState::Evaluated(Box::new([ConstScalar::bool(false)]))
		);
	}

	#[test]
	fn a_constant_whose_body_failed_its_checks_is_not_evaluated() {
		// `BAD` evaluates to a value of the wrong length; its check is what
		// says so, and that has not happened by the time anything could read
		// the value, so nothing does: `BAD` is poisoned, and `READ`, which
		// names it, is silent.
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const N: u32 = 4;
				const BAD: heap::&[u8; N] = "ab";
				const READ: heap::&[u8; N] = BAD;
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ArraySizeMismatch]);
		for name in ["BAD", "READ"] {
			let DeclKind::Const(index) = case.resolve(name) else {
				panic!("expected a constant");
			};
			assert_eq!(
				case.sema.solver.const_values[usize::from(index)],
				ConstValueState::Poisoned,
				"{name}"
			);
		}
	}

	#[test]
	fn a_constant_is_checked_before_a_later_constant_reads_it() {
		// `B` reads `A`'s value in its own check, before `A`'s turn: `A` is
		// checked on demand, and a mismatch in it is reported once.
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const B: heap::&[u8; A] = [0; _];
				const A: u32 = True;
			"#});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
	}

	#[test]
	fn a_function_item_is_a_zero_sized_constant() {
		let case = TestCase::new(indoc! {"
				func id<T: StackValue>(x: T) -> T { x }
				const ID: id<u8> = id;
				const AGAIN: id<u8> = ID;
				func f() -> u8 { ID(1) }
			"});
		case.diagnostics().assert_none();
		for name in ["ID", "AGAIN"] {
			let DeclKind::Const(index) = case.resolve(name) else {
				panic!("expected a constant");
			};
			assert_eq!(
				case.sema.solver.const_values[usize::from(index)],
				ConstValueState::Evaluated(Box::new([]))
			);
		}
		assert_eq!(case.shape("f"), "(block => (abstract call<id<u8>> ID 1))");
	}

	/// `Value` is `Global`'s, bound through its subtrait `GlobalMut`.
	#[test]
	fn a_bound_on_a_supertraits_value_holds_for_each_global() {
		let case = TestCase::new(indoc! {"
				global mut hits: u32 = 0;
				global mut flag: Bool = False;
				func bump<G: GlobalMut where { Value = u32 }>(g: G) {
					g.set(g.get() + 1);
				}
				func f() { bump(hits); bump(flag); }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
		case.diagnostics().assert_error_saying(
			"type mismatch resolving `<flag as Global>::Value == u32`",
		);
	}

	#[test]
	fn a_global_handle_is_a_zero_sized_constant() {
		let case = TestCase::new(indoc! {"
				global mut counter: u32 = 0;
				const COUNTER: counter = counter;
				func read() -> u32 { COUNTER.get() }
			"});
		case.diagnostics().assert_none();
		let DeclKind::Const(index) = case.resolve("COUNTER") else {
			panic!("expected a constant");
		};
		assert_eq!(
			case.sema.solver.const_values[usize::from(index)],
			ConstValueState::Evaluated(Box::new([]))
		);
		assert_eq!(
			case.shape("read"),
			"(block => (abstract get<counter> COUNTER))"
		);
	}

	#[test]
	fn a_global_initializer_is_checked_against_its_type() {
		let case = TestCase::new("global small: u8 = 300;");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
	}

	#[test]
	fn a_path_through_a_type_calls_its_member_directly() {
		let case = TestCase::new(indoc! {"
				enum E(u8) { A = 0 }
				impl E { pub func pick<T: StackValue>(t: T) -> E { E::A } }
				struct W<T>(x: T);
				impl<T: StackValue> W<T> {
					pub func new(x: T) -> W<T> { W(x) }
					pub func get(self: Self) -> T { loop {} }
					func again(x: T) -> W<T> { Self::new(x) }
				}
				trait Make: StackValue { func make() -> Self; }
				struct P();
				impl Make for P { func make() -> Self { P() } }
				func inherent() -> E { E::pick(True) }
				func generic_impl(w: W<u8>) -> u8 { W::<u8>::get(w) }
				func constructed() -> W<u16> { W::<u16>::new(1) }
				func trait_impl() -> P { P::make() }
				func value() { local f = W::<u8>::new; }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("inherent"), "(block => (call pick<Bool> True))");
		assert_eq!(case.shape("generic_impl"), "(block => (call get<u8> w#0))");
		assert_eq!(case.shape("constructed"), "(block => (call new<u16> 1))");
		assert_eq!(case.member_shape("again"), "(block => (call new<T> x#0))");
		assert_eq!(case.shape("trait_impl"), "(block => (call make))");
		assert_eq!(case.locals("value"), [("f".into(), "new<u8>".into())]);
	}

	#[test]
	fn a_trait_declaration_is_called_with_its_receiver_as_self() {
		let case = TestCase::new(indoc! {"
				trait Make: StackValue {
					func make() -> Self;
					func zero() -> u32 { 0 }
				}
				struct P();
				impl Make for P { func make() -> Self { P() } }
				func abstract_receiver<T: StackValue + Make>() -> T { T::make() }
				func inherited_default() -> u32 { P::zero() }
			"});
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
		let case = TestCase::new(indoc! {"
				trait Make: StackValue { func make() -> Self; }
				trait Other: StackValue { func make() -> Self; }
				struct P();
				impl Make for P { func make() -> Self { P() } }
				impl Other for P { func make() -> Self { P() } }
				struct W<T>(x: T);
				impl<T: StackValue> W<T> { pub func new(x: T) -> W<T> { W(x) } }
				func qualified() -> P { <P as Make>::make() }
				func abstract_qualified<T: StackValue + Make>() -> T { <T as Make>::make() }
				func grouped() -> W<u8> { <W<u8>>::new(1) }
				func ambiguous() -> P { P::make() }
				func not_implemented() -> Bool { <Bool as Make>::make() }
			"});
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
		let case = TestCase::new(indoc! {"
				mod inner {
					pub struct S();
					impl S { func hidden() {} pub func shown() {} }
					trait Secret { func secret(); }
					impl Secret for S { func secret() {} }
				}
				func missing() { inner::S::nothing(); }
				func private() { inner::S::hidden(); inner::S::shown(); }
				func private_trait() { inner::S::secret(); }
			"});
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
		let case = TestCase::new(indoc! {"
				struct W<T>(x: T);
				impl<T: StackValue> W<T> {
					pub func new(x: T) -> W<T> { W(x) }
					pub func empty() -> W<T> { loop {} }
					pub func of<U>() -> W<T> { loop {} }
				}
				struct M<T>(x: T);
				impl M<u8> { pub func one() -> M<u8> { loop {} } }
				impl M<u32> { pub func only() -> M<u32> { loop {} } }
				func from_argument(a: u8) -> W<u8> { W::new(a) }
				func from_expected() -> W<u16> { W::empty() }
				func with_own(a: u8) -> W<Bool> { W::of::<u8>() }
				func picked() -> M<u32> { M::only() }
				func uninferred() { W::empty(); }
				func other_impl() -> M<u8> { M::only() }
			"});
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
		assert_eq!(case.shape("with_own"), "(block => (call of<Bool, u8>))");
		assert_eq!(case.shape("picked"), "(block => (call only))");
	}

	#[test]
	fn a_receiver_call_learns_its_type_arguments_from_the_method() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct P<M: Memory, T>(addr: M::Size);
				impl<M: Memory, T: StackValue> P<M, T> {
					pub func at(addr: M::Size) -> Self { Self({ addr }) }
					pub func get(self: Self) -> M::*T { transmute(self.addr) }
					pub func peek(self: heap::&Self) -> M::&T { loop {} }
				}
				func by_value(n: u32) -> heap::*u8 { P::at(n).get() }
				func make<M: Memory, T: StackValue>(a: u32) -> M::*P<M, T> {
					loop {}
				}
				func by_pointer(n: u32) -> heap::&u8 { make(n).peek() }
				func nothing_expected(n: u32) { P::at(n).get(); }
				func written_wins(n: u32) -> heap::*u8 {
					P::<heap, u16>::at(n).get()
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TypeMistmatch,
		]);
		assert_eq!(
			case.shape("by_value"),
			"(block => (call get<heap, u8> (call at<heap, u8> n#0)))"
		);
		assert_eq!(
			case.shape("by_pointer"),
			"(block => (call peek<heap, u8> (.& (* (call make<heap, u8> n#0)))))"
		);
	}

	#[test]
	fn an_impl_selected_before_its_arguments_proves_its_bounds_at_the_call() {
		let case = TestCase::new(indoc! {"
				trait Small {}
				impl Small for u8 {}
				struct B<T>(x: T);
				impl<T: StackValue + Small> B<T> { pub func new(x: T) -> B<T> { B(x) } }
				func holds(a: u8) { local b = B::new(a); }
				func violated() { local b = B::new(True); }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
	}

	#[test]
	fn a_wrong_type_argument_count_makes_that_frame_an_error() {
		let case = TestCase::new(indoc! {"
				func id<T: StackValue>(x: T) -> T { x }
				func pair<A: StackValue, B: StackValue>(a: A, b: B) {}
				func plain() {}
				struct W<T>(x: T);
				impl<T: StackValue> W<T> { func get(self: Self) -> T { local W(x) = self; x } }
				func too_many() { _ = id::<u8, u16>(1); }
				func too_few() { pair::<u8>(1, 2); }
				func own_none() { plain::<u8>(); }
				func method(w: W<u8>) -> u8 { w.get::<u8>() }
				func construction() { _ = W::<u8, u16>(1); }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentCountMismatch,
			DiagnosticCode::TypeArgumentCountMismatch,
		]);
		assert_eq!(
			case.shape("too_many"),
			"(block (drop (call id<{unknown}> 1)))"
		);
		assert_eq!(
			case.shape("too_few"),
			"(block (call pair<{unknown}, {unknown}> 1 2))"
		);
		assert_eq!(case.shape("own_none"), "(block (call plain))");
		// The impl's argument, known from the receiver, is kept.
		assert_eq!(case.shape("method"), "(block => (call get<u8> w#0))");
	}

	#[test]
	fn a_function_value_proves_its_bounds_once_where_it_is_named() {
		let case = TestCase::new(indoc! {"
				trait Small {}
				impl Small for u8 {}
				func take<T: StackValue + Small>(x: T) {}
				func holds(a: u8) { local g = take::<u8>; g(a); }
				func violated() { local g = take::<Bool>; g(True); }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
	}

	#[test]
	fn self_constructs_the_struct_its_impl_is_for() {
		let case = TestCase::new(indoc! {"
				struct W<T>(x: T);
				impl<T: StackValue> W<T> {
					func positional(x: T) -> W<T> { Self(x) }
					func named(x: T) -> Self { Self({ x }) }
				}
				struct P();
				trait Make: StackValue { func make() -> Self; }
				impl Make for P { func make() -> Self { Self() } }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.member_shape("positional"), "(block => (W x#0))");
		assert_eq!(case.member_shape("named"), "(block => (W x#0))");
		assert_eq!(case.member_shape("make"), "(block => (P))");
	}

	#[test]
	fn self_is_constructed_only_where_it_names_an_accessible_struct() {
		let case = TestCase::new(indoc! {"
				mod inner { pub struct P(x: u32); }
				impl inner::P { func outside() -> inner::P { Self(1) } }
				struct W(x: u32);
				impl W {
					func bare() { local w = Self; }
					func written() -> W { Self::<u8>(1) }
				}
				enum E(u8) { A = 0 }
				impl E { func variant() -> E { Self(0) } }
				trait Tr: StackValue { func make() -> Self { Self() } }
				func free() { Self(); }
			"});
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
		let case = TestCase::new(indoc! {"
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
			"});
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
		let DeclKind::Const(index) = case.resolve("EVALUATED") else {
			panic!("expected a constant");
		};
		assert!(matches!(
			case.sema.solver.const_values[usize::from(index)],
			ConstValueState::Evaluated(_)
		));
	}

	#[test]
	fn a_method_call_passes_its_receiver_first() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct W<T>(x: T);
				impl<T: StackValue> W<T> {
					pub func get(self: Self) -> T { loop {} }
					pub func map<U: StackValue>(self: Self, u: U) -> W<U> { W(u) }
					pub func by_pointer(self: heap::*Self) -> T { loop {} }
				}
				trait Twice: StackValue { func twice(self: Self) -> Self; }
				impl Twice for u8 { func twice(self: Self) -> Self { self } }
				func inherent(w: W<u8>) -> u8 { w.get() }
				func own_args(w: W<u8>) -> W<Bool> { w.map(True) }
				func turbofish(w: W<u8>) -> W<u16> { w.map::<u16>(1) }
				func trait_impl(a: u8) -> u8 { a.twice() }
				func abstract_receiver<T: StackValue + Twice>(t: T) -> T { t.twice() }
				func pointer(p: heap::*W<u8>) -> u8 { p.by_pointer() }
				func reverse(o: Ordering) -> Ordering { o.reverse() }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("inherent"), "(block => (call get<u8> w#0))");
		assert_eq!(
			case.shape("own_args"),
			"(block => (call map<u8, Bool> w#0 True))"
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
		let case = TestCase::new(indoc! {"
				global mut counter: u32 = 0;
				global limit: u32 = 10;
				func bump() -> u32 {
					counter.set(counter.get() + 1);
					counter.get()
				}
				func fixed() { limit.set(1); }
			"});
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
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct S();
				impl S {
					pub func by_value(self: Self) {}
					pub func associated() {}
				}
				func missing(s: S) { s.nothing(); }
				func not_a_method(s: S) { s.associated(); }
				func through_pointer(p: heap::*S) { p.by_value(); }
				func loaded(p: heap::*S) { p.*.by_value(); }
				func untyped() { (1).add(2); }
				func arguments(s: S) { s.by_value(1); }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::MethodNotFound,
			DiagnosticCode::NotAMethod,
			DiagnosticCode::MethodNotFound,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::ArgumentCountMismatch,
		]);
		case.diagnostics().assert_error_saying(
			"function `by_value` takes 0 arguments but 1 was supplied",
		);
	}

	#[test]
	fn a_call_by_name_binds_each_argument_to_its_parameter() {
		let case = TestCase::new(indoc! {"
				func f(a: u32, b: i64) -> u32 { a }
				func id<T: StackValue>(value: T, flag: Bool) -> T { value }
				func by_name() -> u32 {
					local a: u32 = 1;
					f({ b: 2, a })
				}
				func in_order() -> u32 { f({ a: 1, b: 2 }) }
				func positional() -> u32 { f(1, 2) }
				func generic(x: u8) -> u8 { id({ flag: True, value: x }) }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("by_name"),
			"(block (local a#0 1) => (call f 1=2 0=a#0))"
		);
		assert_eq!(case.shape("in_order"), "(block => (call f 1 2))");
		assert_eq!(case.shape("positional"), "(block => (call f 1 2))");
		assert_eq!(
			case.shape("generic"),
			"(block => (call id<u8> 1=True 0=x#0))"
		);
	}

	#[test]
	fn a_method_is_called_by_name_with_its_receiver_named_self() {
		let case = TestCase::new(indoc! {"
				struct S(n: u32);
				impl S {
					pub func pick(self: Self, n: u32, m: u32) -> u32 { n }
				}
				func method(s: S) -> u32 { s.pick({ m: 1, n: 2 }) }
				func path(s: S) -> u32 { S::pick({ n: 2, self: s, m: 1 }) }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.shape("method"), "(block => (call pick s#0 1=1 0=2))");
		assert_eq!(case.shape("path"), "(block => (call pick 1=2 0=s#0 2=1))");
	}

	/// A member of another kind does not provide the declaration of its name:
	/// a call selects the trait's declaration, as for a member the impl
	/// leaves out, and conformance reports the member.
	#[test]
	fn a_call_skips_an_impl_member_of_another_kind() {
		let case = TestCase::new(indoc! {"
				trait Size: StackValue { func size(self: Self) -> u32 { 0 } }
				struct S();
				impl Size for S { const size: u32 = 1; }
				func f(s: S) -> u32 { s.size() }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplItemKindMismatch]);
		assert_eq!(case.shape("f"), "(block => (abstract size<S> s#0))");
	}

	#[test]
	fn a_trait_impl_function_is_called_by_its_traits_names() {
		let case = TestCase::new(indoc! {"
				struct P(v: u32);
				impl Add for P {
					func add(self: Self, other: Self) -> Self { other }
				}
				func concrete(p: P, q: P) -> P { p.add({ rhs: q }) }
				func path(p: P, q: P) -> P { P::add({ rhs: q, self: p }) }
				func generic<T: Add>(a: T, b: T) -> T { a.add({ rhs: b }) }
				func impl_name(p: P, q: P) -> P { p.add({ other: q }) }
			"});
		// The impl's own name breaks the trait's contract, and calls still use
		// the trait's.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::UnknownParameterName,
			DiagnosticCode::MissingArguments,
		]);
		case.diagnostics().assert_error_saying(
			"function `add` has no parameter named `other`",
		);
		assert_eq!(case.shape("concrete"), "(block => (call add p#0 q#1))");
		assert_eq!(case.shape("path"), "(block => (call add 1=q#1 0=p#0))");
		assert_eq!(
			case.shape("generic"),
			"(block => (abstract add<T> a#0 b#1))"
		);
	}

	#[test]
	fn every_path_to_a_known_function_can_be_called_by_name() {
		let case = TestCase::new(indoc! {"
				trait Make: StackValue {
					func make(value: u32, scale: u32) -> Self;
				}
				struct S(n: u32);
				impl Make for S {
					func make(value: u32, _: u32) -> Self { S(value) }
				}
				impl S {
					pub func twice(self: Self, by: u32) -> u32 { by }
					pub func again(self: Self) -> u32 {
						Self::twice({ by: 2, self })
					}
				}
				struct W<T>(x: T);
				impl<T: StackValue> W<T> {
					pub func new(x: T, flag: Bool) -> W<T> { W(x) }
				}
				func qualified() -> S {
					<S as Make>::make({ scale: 1, value: 2 })
				}
				func generic<T: StackValue + Make>() -> T { T::make({ scale: 1, value: 2 }) }
				func learned(a: u8) -> W<u8> { W::new({ flag: True, x: a }) }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.member_shape("again"),
			"(block => (call twice 1=2 0=self#0))"
		);
		assert_eq!(case.shape("qualified"), "(block => (call make 1=1 0=2))");
		assert_eq!(
			case.shape("generic"),
			"(block => (abstract make<T> 1=1 0=2))"
		);
		assert_eq!(
			case.shape("learned"),
			"(block => (call new<u8> 1=True 0=a#0))"
		);
	}

	#[test]
	fn a_call_by_name_follows_the_traits_names_even_where_it_leaves_one_out() {
		let case = TestCase::new(indoc! {"
				trait Scale: StackValue {
					func scale(self: Self, u32) -> Self;
				}
				struct S(n: u32);
				impl Scale for S {
					func scale(self: Self, by: u32) -> Self { self }
				}
				func named(s: S) -> S { s.scale({ by: 2 }) }
				func positional(s: S) -> S { s.scale(2) }
			"});
		// Naming the parameter breaks the trait's contract, and the call still
		// follows the trait's declaration, which has no name to call it by.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::PositionalOnlyCall,
		]);
		case.diagnostics().assert_error_saying(
			"function `scale` has an unnamed parameter, so it is called by \
			 position",
		);
		assert_eq!(case.shape("positional"), "(block => (call scale s#0 2))");
	}

	#[test]
	fn a_call_by_name_reaches_the_first_parameter_of_a_name_declared_twice() {
		let case = TestCase::new(indoc! {"
				func d(a: u32, a: u32) {}
				func once() { d({ a: 1 }) }
				func twice() { d({ a: 1, a: 2 }) }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::DuplicateFunctionParameter,
			DiagnosticCode::DuplicateNamedArgument,
		]);
		assert_eq!(case.shape("once"), "(block => (call d 1))");
	}

	#[test]
	fn an_empty_call_by_name_gives_no_argument() {
		let case = TestCase::new(indoc! {"
				func none() {}
				func some(a: u32) {}
				func empty() { none({}) }
				func missing() { some({}) }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::MissingArguments]);
		assert_eq!(case.shape("empty"), "(block => (call none))");
	}

	#[test]
	fn a_call_by_name_reports_what_does_not_match_its_parameters() {
		let case = TestCase::new(indoc! {"
				struct S();
				impl S {
					pub func m(self: Self, n: u32) {}
				}
				func f(a: u32, b: i64) {}
				func g(u32, b: u32) {}
				func unknown() { f({ a: 1, b: 2, c: 3 }) }
				func twice() { f({ a: 1, a: 2, b: 3 }) }
				func missing() { f({ b: 2 }) }
				func unnamed() { g({ b: 1 }) }
				func receiver(s: S) { s.m({ self: s, n: 1 }) }
				func mismatch(x: i64) { f({ a: x, b: x }) }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnknownParameterName,
			DiagnosticCode::DuplicateNamedArgument,
			DiagnosticCode::MissingArguments,
			DiagnosticCode::PositionalOnlyCall,
			DiagnosticCode::UnknownParameterName,
			DiagnosticCode::TypeMistmatch,
		]);
		case.diagnostics()
			.assert_error_saying("function `f` has no parameter named `c`");
		case.diagnostics()
			.assert_error_saying("argument `a` given more than once");
		case.diagnostics().assert_error_saying(
			"missing argument `a` in call to function `f`",
		);
		case.diagnostics().assert_error_saying(
			"function `g` has an unnamed parameter, so it is called by \
			 position",
		);
		case.diagnostics()
			.assert_error_saying("function `m` has no parameter named `self`");
		assert_eq!(case.shape("missing"), "(block => (call f 1=2))");
	}

	#[test]
	fn a_reported_argument_list_does_not_also_report_an_uninferred_type() {
		let case = TestCase::new(indoc! {"
				func pair<T: StackValue>(a: T, b: T) -> T { a }
				func none<T: StackValue>(flag: Bool) -> T { loop {} }
				func g<T: StackValue>(T, b: u32) -> T { loop {} }
				struct W<T>(x: T, y: T);
				func missing() { pair(1); }
				func missing_by_name() { pair({ a: 1 }); }
				func extra() { none(True, 1); }
				func unknown_name() { none({ flag: True, other: 1 }); }
				func positional_only() { g({ b: 1 }); }
				func construction() { W(1); }
				func construction_by_name() { W({ x: 1 }); }
				func uninferred() { none(True); }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::MissingArguments,
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::UnknownParameterName,
			DiagnosticCode::PositionalOnlyCall,
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::MissingArguments,
			DiagnosticCode::TypeAnnotationRequired,
		]);
		case.diagnostics().assert_error_saying(
			"struct constructor `W` takes 2 arguments but 1 was supplied",
		);
		case.diagnostics().assert_error_saying(
			"missing argument `y` in call to struct constructor `W`",
		);
	}

	#[test]
	fn an_argument_built_with_a_known_type_is_held_to_it() {
		let case = TestCase::new(indoc! {"
				func three<T: StackValue>(a: T, b: T, c: T) -> T { a }
				func f(x: u8, y: u16) { three(x, y, nothing); }
			"});
		// `T` is `u8` from `x` before `y` is built, so `y` is held to `u8`
		// although the failed third argument leaves `T` an error.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UndeclaredIdentifier,
			DiagnosticCode::TypeMistmatch,
		]);
	}

	#[test]
	fn an_unsupported_form_is_reported_once_as_a_bug() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func f(s: heap::&[u8]) -> heap::&[u8] {
					s[1..]
				}
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnsupportedExpression]);
		assert_eq!(case.shape("f"), "(block => error)");
	}

	#[test]
	fn a_local_pattern_takes_its_value_apart() {
		let case = TestCase::new(indoc! {"
				struct Point(x: u32, y: i64);
				struct W<T>(a: T, b: Bool);
				func f(p: Point, t: (u8, (u16, u32)), w: W<u8>) {
					local Point(x, y) = p;
					local Point({ y: py, .. }) = p;
					local (a, (_, c)) = t;
					local (.., (d, ..)) = t;
					local W(e, mut g) = w;
				}
			"});
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
			["u32", "i64", "i64", "u8", "u32", "u16", "u8", "Bool"]
		);
	}

	#[test]
	fn a_local_pattern_must_fit_its_value() {
		let case = TestCase::new(indoc! {"
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
			"});
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
		let case = TestCase::new(indoc! {"
				func f(t: (u32, u32)) -> u32 {
					local (a, 0) = t;
					a
				}
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::RefutablePatternInLocal]);
		assert_eq!(
			case.shape("f"),
			"(block (local (tuple a#1 error) t#0) => a#1)"
		);
	}

	#[test]
	fn a_match_checks_each_arm_against_the_scrutinee() {
		let case = TestCase::new(indoc! {"
				func sign(x: i32) -> i32 {
					match x {
						0 => { 0 },
						-1 | -128 => { 1 },
						n => { n },
					}
				}
			"});
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
		let case = TestCase::new(indoc! {"
				enum Dir(u8) { North = 0, South = 1 }
				const LIMIT: u8 = 10;
				struct P(x: u8, d: Dir);
				trait Lim { const MAX: u8; }
				struct S();
				impl S { const ZERO: u8 = 0; }
				func f<T: Lim>(p: P) -> u8 {
					match p {
						P(0, Dir::North) => { 1 },
						P(const LIMIT, d) => { 2 },
						P(x, Dir::South) => { x },
						P(S::ZERO | T::MAX, _) => { 3 },
						_ => { 4 },
					}
				}
			"});
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

	/// A struct pattern's list is one value of its fields, as a construction
	/// gives them: one pattern for several fields matches them all as a
	/// tuple, several for a lone tuple field match that tuple.
	#[test]
	fn a_struct_pattern_matches_its_fields_as_one_value() {
		let case = TestCase::new(indoc! {"
				struct P(x: u8, y: u16);
				struct W(x: (u8, u16));
				struct Unit();
				func whole(p: P) -> (u8, u16) { local P(t) = p; t }
				func grouped(p: P) -> u8 { local P((a, b)) = p; a }
				func any(p: P) { local P(_) = p; }
				func spread(w: W) -> u8 { local W(a, b) = w; a }
				func lone_rest(w: W) -> u16 { local W(.., b) = w; b }
				func field(w: W) -> (u8, u16) { local W(t) = w; t }
				func unit(u: Unit) { local Unit(e) = u; }
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.locals("whole")[1], ("t".into(), "(u8, u16)".into()));
		assert_eq!(
			case.locals("grouped")[1..],
			[("a".into(), "u8".into()), ("b".into(), "u16".into())]
		);
		assert_eq!(
			case.locals("spread")[1..],
			[("a".into(), "u8".into()), ("b".into(), "u16".into())]
		);
		assert_eq!(case.locals("lone_rest")[1], ("b".into(), "u16".into()));
		assert_eq!(case.locals("field")[1], ("t".into(), "(u8, u16)".into()));
		assert_eq!(case.locals("unit")[1], ("e".into(), "()".into()));
	}

	#[test]
	fn an_open_enum_is_exhaustive_only_with_a_wildcard() {
		let case = TestCase::new(indoc! {"
				enum Closed(u8) { A = 0, B = 1, C = 2 }
				enum Open(u8) { A = 0, B = 1, .. }
				func closed(c: Closed) -> u8 {
					match c { Closed::A => { 1 }, Closed::B => { 2 }, Closed::C => { 3 } }
				}
				func named(o: Open) -> u8 {
					match o { Open::A => { 1 }, Open::B => { 2 } }
				}
				func rest(o: Open) -> u8 {
					match o { Open::A => { 1 }, Open::B => { 2 }, _ => { 3 } }
				}
				func binding(o: Open) -> u8 {
					match o { Open::A => { 1 }, other => { 2 } }
				}
				func destructure(o: Open) { local x = o; local _ = o; }
				func same(a: Open, b: Open) -> Bool { a == b }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::NonExhaustiveMatch]);
	}

	#[test]
	fn an_open_enum_is_its_variants_and_the_rest() {
		// What is not covered is named by variant first, then `_` for the rest.
		let case = TestCase::new(indoc! {"
				enum Open(u8) { A = 0, B = 1, C = 2, .. }
				func f(o: Open) -> u8 { match o { Open::A => { 1 } } }
			"});
		case.diagnostics()
			.assert_error_saying("patterns `Open::B`, `Open::C` and `_`");

		// Inside a tuple, and with a signed repr.
		let case = TestCase::new(indoc! {"
				enum Sign(i8) { Minus = -1, Zero = 0, .. }
				func f(a: Sign, b: Bool) -> u8 {
					match (a, b) {
						(Sign::Minus, _) => { 1 },
						(Sign::Zero, _) => { 2 },
						(_, _) => { 3 },
					}
				}
			"});
		case.diagnostics().assert_none();
	}

	#[test]
	fn an_open_enum_that_names_every_value_has_no_rest() {
		// `..` admits nothing here (and is warned about), so the enum is closed
		// in effect: listing every variant is exhaustive, and a wildcard after
		// them is unreachable.
		let all: Vec<String> =
			(0..256).map(|n| format!("V{n} = {n}")).collect();
		let arms: Vec<String> =
			(0..256).map(|n| format!("E::V{n} => {{ 1 }}")).collect();
		let source = format!(
			"enum E(u8) {{ {}, .. }}\nfunc f(e: E) -> u8 {{ match e {{ {} }} }}",
			all.join(", "),
			arms.join(", ")
		);
		let case = TestCase::new(source.as_str());
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::RedundantOpenMarker]);

		let source = format!(
			"enum E(u8) {{ {}, .. }}\nfunc f(e: E) -> u8 {{ match e {{ {}, _ => {{ 2 }} }} }}",
			all.join(", "),
			arms.join(", ")
		);
		let case = TestCase::new(source.as_str());
		case.diagnostics().assert_codes(&[
			DiagnosticCode::RedundantOpenMarker,
			DiagnosticCode::UnreachableMatchArm,
		]);
	}

	#[test]
	fn the_dots_of_an_enum_are_judged_when_its_signature_is_built() {
		// Fine: one `..`, last.
		let case = TestCase::new("enum E(u8) { A = 0, .. }");
		case.diagnostics().assert_none();

		// Any `..` opens the enum, so a misplaced one only draws a warning.
		let case = TestCase::new("enum E(u8) { A = 0, .., B = 1 }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::MisplacedOpenMarker]);

		// A second adds nothing.
		let case = TestCase::new("enum E(u8) { A = 0, .., .. }");
		case.diagnostics().assert_codes(&[
			DiagnosticCode::MisplacedOpenMarker,
			DiagnosticCode::RedundantOpenMarker,
		]);

		// Nothing is left for it to admit once the variants name every value.
		let all: Vec<String> =
			(0..256).map(|n| format!("V{n} = {n}")).collect();
		let source = format!("enum E(u8) {{ {}, .. }}", all.join(", "));
		let case = TestCase::new(source.as_str());
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::RedundantOpenMarker]);

		// One value short, it is not.
		let source = format!("enum E(u8) {{ {}, .. }}", all[1..].join(", "));
		let case = TestCase::new(source.as_str());
		case.diagnostics().assert_none();
	}

	#[test]
	fn an_open_enum_missing_arm_is_a_wildcard() {
		let case = TestCase::new(indoc! {"
				enum Open(u8) { A = 0, .. }
				func named(o: Open) -> u8 {
					match o { Open::A => { 1 } }
				}
			"});
		case.diagnostics().assert_error_saying("pattern `_`");
	}

	#[test]
	fn a_struct_pattern_of_its_fields_as_one_value_counts_for_exhaustiveness() {
		let case = TestCase::new(indoc! {"
				struct P(x: u8, y: u16);
				struct W(x: (u8, u16));
				func covered(p: P) -> u8 {
					match p { P(0, _) => { 1 }, P(t) => { 2 } }
				}
				func missing(p: P) -> u8 {
					match p { P((0, _) | (1, _)) => { 1 } }
				}
				func unreachable(w: W) -> u8 {
					match w { W(0, _) => { 1 }, W(_) => { 2 }, W(a, b) => { 3 } }
				}
				func count(p: P) { local P(a, b, c) = p; }
				func lone(w: W) { local W(a, b, c) = w; }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NonExhaustiveMatch,
			DiagnosticCode::UnreachableMatchArm,
			DiagnosticCode::ArgumentCountMismatch,
			DiagnosticCode::ArgumentCountMismatch,
		]);
	}

	#[test]
	fn a_constant_has_its_value_wherever_a_pattern_may_name_it() {
		// A constant's value is known wherever a pattern may name it: in a
		// function's block, in a global's initializer, in a constant's own.
		let case = TestCase::new(indoc! {"
				enum Dir(u8) { North = 0, East = 1, South = 2 }
				const N: Dir = Dir::North;
				global g: Dir = match (N) {
					const N => { Dir::North },
					Dir::North => { Dir::South },
					_ => { Dir::East },
				};
				// The variants are known here too, so listing them all is
				// enough: no `_` is needed.
				global h: Dir = match (N) {
					Dir::North => { Dir::North },
					Dir::East => { Dir::East },
					Dir::South => { Dir::South },
				};
				func f(d: Dir) {
					match d {
						const N => {},
						Dir::North => {},
						_ => {},
					}
				}
			"});
		// In both, the second arm is covered by the first. Each global's
		// `match` is a constant in principle, but the evaluator folds no
		// control flow yet, so its initializer is not evaluated (E2015).
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnreachableMatchArm,
			DiagnosticCode::NonConstantGlobalInitializer,
			DiagnosticCode::NonConstantGlobalInitializer,
			DiagnosticCode::UnreachableMatchArm,
		]);
	}

	#[test]
	fn constants_whose_initializers_name_each_other_are_one_cycle() {
		// Each initializer's pattern compares with the other's value, so
		// checking one asks for the other's value, which needs the other
		// checked, which asks for the first one's value again. Only a checked
		// body is evaluated, so that is a loop, reported once.
		let case = TestCase::new(indoc! {"
				const A: Bool = match (True) { const B => { True }, _ => { False } };
				const B: Bool = match (True) { const A => { True }, _ => { False } };
				func f() -> Bool {
					match (True) {
						const A => { match (True) { const B => { True }, _ => { False } } },
						_ => { False },
					}
				}
			"});
		// The constants are poisoned, so the function that names them is silent.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CyclicConstant]);
	}

	#[test]
	fn a_float_literal_needs_eq_and_a_string_cannot_be_matched() {
		// The parser reads them; a float has only partial equality, and a
		// string has no equality at all.
		let case = TestCase::new(indoc! {r#"
				func f(x: f32, s: u8) {
					match x { 1.5 => {}, _ => {} }
					match s { "hi" => {}, _ => {} }
				}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::UnmatchableLiteral,
		]);
		case.diagnostics()
			.assert_error_saying("the trait bound `f32: Eq` is not satisfied");
		case.diagnostics()
			.assert_error_saying("a string cannot be matched");
	}

	#[test]
	fn a_match_constant_needs_eq() {
		let case = TestCase::new(indoc! {"
				struct P(x: u8);
				const F: f32 = 1.0;
				const ORIGIN: P = P(0);
				func floats(x: f32) {
					match x { const F => {}, _ => {} }
				}
				func points(p: P) {
					match p { const ORIGIN => {}, _ => {} }
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
		]);
		case.diagnostics()
			.assert_error_saying("the trait bound `f32: Eq` is not satisfied");
		case.diagnostics()
			.assert_error_saying("the trait bound `P: Eq` is not satisfied");
	}

	#[test]
	fn an_enum_satisfies_eq_and_partial_eq_structurally() {
		let case = TestCase::new(indoc! {"
				enum Color(u8) { Red = 0, Green }
				func needs_eq<T: Eq>(value: T) {}
				func needs_partial<T: PartialEq>(value: T) {}
				func f(color: Color) {
					needs_eq(color);
					needs_partial(color);
				}
			"});
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_float_or_an_aggregate_can_still_be_bound() {
		let case = TestCase::new(indoc! {"
				struct P(x: u8);
				func floats(x: f32) -> f32 {
					match x { whole => { whole + 1.0 } }
				}
				func points(p: P) -> P {
					match p { whole => { whole }, }
				}
			"});
		case.diagnostics().assert_none();
	}

	#[test]
	fn every_test_in_a_local_pattern_poisons_the_pattern() {
		// A `local` always matches: every test in it is a mistake, and each
		// one poisons its own pattern, so the pattern takes the value apart
		// and binds without testing. Only the first test is reported.
		let case = TestCase::new(indoc! {"
				const C: u8 = 1;
				func f(x: (u8, u8)) {
					local (a, 5) = x;
					local (b, const C) = x;
					local (c, 5) | (0, 10) = x;
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::RefutablePatternInLocal,
			DiagnosticCode::RefutablePatternInLocal,
			DiagnosticCode::RefutablePatternInLocal,
			DiagnosticCode::NotBoundInAllAlternatives,
		]);
		assert_eq!(
			case.shape("f"),
			"(block (local (tuple a#1 error) x#0) (local (tuple b#2 error) x#0) \
			 (local (| (tuple c#3 error) (tuple error error)) x#0))"
		);
	}

	#[test]
	fn a_name_bound_twice_in_one_alternative_is_still_one_local() {
		// The name is bound twice in the second alternative, which is a
		// mistake, but it is still the one local the alternatives share: the
		// two bindings are of different types, and that is said too.
		let case = TestCase::new(indoc! {"
				func f(x: (i32, i32, i64)) {
					match x { (a, 5, 6) | (a, b, a) => { local _ = a; }, _ => {} }
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::DuplicatePatternBinding,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::NotBoundInAllAlternatives,
			DiagnosticCode::UnreachableMatchArm,
		]);
		assert_eq!(
			case.shape("f"),
			"(block => (match x#0 ((| (tuple a#1 5 6) (tuple a#1 b#2 a#1)) => \
			 (block (local _ a#1))) (_ => (block))))"
		);
	}

	#[test]
	fn the_same_name_in_two_alternatives_is_one_local() {
		// The same name in two alternatives is one local, which the arm's
		// body reads.
		let case = TestCase::new(indoc! {"
				func f(x: (i32, i64)) {
					match x { (a, 5) | (a, 10) => { local _ = a; }, _ => {} }
				}
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block => (match x#0 ((| (tuple a#1 5) (tuple a#1 10)) => (block \
			 (local _ a#1))) (_ => (block))))"
		);
	}

	#[test]
	fn a_binding_bound_differently_in_two_alternatives_is_an_error() {
		let case = TestCase::new(indoc! {"
				func f(x: (i32, i64)) {
					match x { (mut a, 5) | (a, 10) => {}, _ => {} }
				}
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::InconsistentPatternBinding]);
		case.diagnostics().assert_error_saying(
			"variable `a` is bound inconsistently across alternatives separated \
			 by `|`",
		);
	}

	#[test]
	fn a_binding_must_have_the_same_type_in_all_alternatives() {
		// The two alternatives bind `a` and `b` at different types, so
		// neither can be one local of one type.
		let case = TestCase::new(indoc! {"
				func f(x: (i32, i64)) {
					match x { (a, b) | (b, a) => {} }
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
		]);
		case.diagnostics().assert_error_saying(
			"in the same arm, a binding must have the same type in all \
			 alternatives",
		);
	}

	#[test]
	fn nested_alternatives_bind_the_same_names() {
		// Each `|` is checked on its own: the inner one binds `a` in one
		// alternative and `b` in the other, and the outer one sees both.
		let case = TestCase::new(indoc! {"
				func f(x: ((i32, i32), i32)) {
					match x { ((a, 1) | (a, 2), 3) => {}, _ => {} }
					match x { ((a, 1) | (b, 2), 3) => {}, _ => {} }
					match x { ((a, 1) | (b, 2), 3) | ((a, 1), 3) => {}, _ => {} }
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NotBoundInAllAlternatives,
			DiagnosticCode::NotBoundInAllAlternatives,
			DiagnosticCode::NotBoundInAllAlternatives,
			DiagnosticCode::NotBoundInAllAlternatives,
			DiagnosticCode::NotBoundInAllAlternatives,
		]);
	}

	#[test]
	fn a_name_bound_twice_in_one_pattern_is_an_error() {
		// A name bound in the same product is bound twice: the alternatives
		// of a `|` share a name, but two groups in one pattern do not.
		let case = TestCase::new(indoc! {"
				func f(x: ((i32, i32), (i32, i32))) {
					match x { ((a, 1) | (a, 2), (a, 3) | (a, 4)) => {}, _ => {} }
				}
				func g(x: ((i32, i32), i32)) {
					match x { ((a, 1) | (a, 2), a) => {}, _ => {} }
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::DuplicatePatternBinding,
			DiagnosticCode::DuplicatePatternBinding,
			DiagnosticCode::DuplicatePatternBinding,
		]);
	}

	#[test]
	fn a_local_pattern_binds_the_same_names_in_its_alternatives() {
		let case = TestCase::new(indoc! {"
				func f(x: (i32, i64)) {
					local (a, b) | (a, b) = x;
				}
				func g(x: (i32, i64)) {
					local (a, 5) | (0, 10) = x;
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::RefutablePatternInLocal,
			DiagnosticCode::NotBoundInAllAlternatives,
		]);
		assert_eq!(
			case.shape("f"),
			"(block (local (| (tuple a#1 b#2) (tuple a#1 b#2)) x#0))"
		);
	}

	#[test]
	fn a_value_in_a_pattern_is_a_constant_of_the_matched_type() {
		let case = TestCase::new(indoc! {"
				const C: u8 = 1;
				func g() {}
				func f(x: u8, b: Bool) {
					local y: u8 = 1;
					match x { const y => {}, _ => {} }
					match x { const g => {}, _ => {} }
					match x { 300 => {}, -1 => {}, _ => {} }
					match x { const True => {}, _ => {} }
					match b { const C => {}, _ => {} }
					match x { 1 | z => {}, _ => {} }
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UndeclaredIdentifier,
			DiagnosticCode::InvalidMatchPattern,
			DiagnosticCode::IntegerLiteralOutOfRange,
			DiagnosticCode::IntegerLiteralOutOfRange,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::NotBoundInAllAlternatives,
			DiagnosticCode::UnreachableMatchArm,
		]);
		case.diagnostics().assert_error_saying(
			"`y` is a local; a pattern compares with constants, and `y` would \
			 bind a new one",
		);
	}

	/// std implements no `Rem` for a float (an `fmod` is the math
	/// library's), so float `%` is refused wherever it is written, a constant
	/// included: constant evaluation relies on never meeting one.
	#[test]
	fn a_float_has_no_remainder() {
		let case = TestCase::new(indoc! {"
				func a(x: f64, y: f64) -> f64 { x % y }
				func b(x: f32, y: f32) -> f32 { x.rem(y) }
				const C: f64 = 5.0 % 2.0;
			"});
		// Constant bodies are checked before function bodies.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::MethodNotFound,
		]);
		case.diagnostics()
			.assert_error_saying("the trait bound `f64: Rem` is not satisfied");
	}

	#[test]
	fn match_arms_share_a_type() {
		let case = TestCase::new(indoc! {"
				func f(x: u8) -> u64 { match x { 0 => { 1 }, _ => { 2 } } }
				func g(x: u8) -> u8 {
					match x { 0 => { return 0 }, _ => { x } }
				}
				func h(x: u8) { local v = match x { 0 => { 1 }, _ => { True } }; }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnableToCoerce]);
		assert_eq!(case.body_type("f"), "u64");
		assert_eq!(case.body_type("g"), "u8");
	}

	#[test]
	fn every_untyped_arm_takes_a_later_typed_arms_type() {
		// The typed arm meets the first untyped one; the ones between are
		// coerced too, so `300` is held to `u8` like the others.
		let case = TestCase::new(indoc! {"
				func g() -> u8 { 5 }
				func f(x: u32) -> u8 { match x { 0 => 1, 1 => 2, _ => g() } }
				func h(x: u32) -> u8 { local v = match x { 0 => 1, 1 => 300, _ => g() }; v }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
		case.diagnostics()
			.assert_error_saying("literal `300` cannot be represented as `u8`");
		assert_eq!(case.body_type("f"), "u8");
	}

	#[test]
	fn match_arm_bodies_may_be_expressions() {
		let case = TestCase::new(indoc! {"
				func f(x: u8) -> u8 {
					match x {
						0 => 1,
						n => n + 1,
					}
				}
			"});
		case.diagnostics().assert_none();
		assert_eq!(case.body_type("f"), "u8");
	}

	#[test]
	fn self_destructures_the_struct_its_impl_is_for() {
		let case = TestCase::new(indoc! {"
				struct W(x: u32, y: u32);
				impl W {
					func head(self: Self) -> u32 { local Self(x, ..) = self; x }
				}
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.member_shape("head"),
			"(block (local (W x#1 _) self#0) => x#1)"
		);
	}

	#[test]
	fn a_match_must_cover_every_value() {
		let case = TestCase::new(indoc! {"
				enum Dir(u8) { North = 0, East, South, West }
				struct P(x: Bool, y: Bool);
				func a(d: Dir) -> u8 {
					match d { Dir::North => { 0 }, Dir::East => { 1 } }
				}
				func b(d: Dir) -> u8 {
					match d {
						Dir::North | Dir::East => { 0 },
						Dir::South | Dir::West => { 1 },
					}
				}
				func c(x: Bool, d: Dir) {
					match (x, d) { (const True, _) => {}, (_, Dir::North) => {} }
				}
				func i(x: u8) -> u8 { match x { 0 => { 0 }, 1 => { 1 } } }
				func s(p: P) {
					match p { P(const True, _) => {}, P(const False, const True) => {} }
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NonExhaustiveMatch,
			DiagnosticCode::NonExhaustiveMatch,
			DiagnosticCode::NonExhaustiveMatch,
			DiagnosticCode::NonExhaustiveMatch,
		]);
		case.diagnostics().assert_error_saying(
			"non-exhaustive match: patterns `Dir::South` and `Dir::West` not \
			 covered",
		);
		case.diagnostics().assert_error_saying(
			"non-exhaustive match: patterns `(Bool::False, Dir::East)`, \
			 `(Bool::False, Dir::South)` and `(Bool::False, Dir::West)` not \
			 covered",
		);
		case.diagnostics().assert_error_saying(
			"non-exhaustive match: pattern `2` not covered",
		);
		case.diagnostics().assert_error_saying(
			"non-exhaustive match: pattern `P(Bool::False, Bool::False)` not \
			 covered",
		);
	}

	#[test]
	fn an_arm_the_arms_before_it_cover_is_unreachable() {
		let case = TestCase::new(indoc! {"
				const ZERO: u8 = 0;
				func u(x: u8) { match x { _ => {}, 0 => {} } }
				func v(b: Bool) {
					match b { const True => {}, const False => {}, _ => {} }
				}
				func w(x: u8) { match x { 0 | 1 => {}, 1 => {}, _ => {} } }
				func z(x: u8) { match x { const ZERO => {}, 0 => {}, _ => {} } }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UnreachableMatchArm,
			DiagnosticCode::UnreachableMatchArm,
			DiagnosticCode::UnreachableMatchArm,
			DiagnosticCode::UnreachableMatchArm,
		]);
		case.diagnostics()
			.assert_warning(DiagnosticCode::UnreachableMatchArm);
	}

	#[test]
	fn a_constant_counts_by_its_value_unless_it_is_abstract() {
		let case = TestCase::new(indoc! {"
				enum Dir(u8) { North = 0, East, South }
				const N: Dir = Dir::North;
				trait Lim { const MAX: u8; }
				func k(d: Dir) {
					match d { const N => {}, Dir::East | Dir::South => {} }
				}
				func l<T: Lim>(x: u8) { match x { T::MAX => {} } }
				func m<T: Lim>(x: u8) { match x { T::MAX => {}, _ => {} } }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::NonExhaustiveMatch]);
		case.diagnostics().assert_error_saying(
			"non-exhaustive match: pattern `_` not covered",
		);
	}

	#[test]
	fn a_match_with_a_failed_pattern_is_not_checked_for_coverage() {
		let case =
			TestCase::new("func f(x: u8) { match x { const nope => {} } }");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
	}

	#[test]
	fn a_type_that_fails_to_normalize_is_not_reported_as_a_mismatch() {
		// The constant, the loop and the member each own their report; what
		// they poison is not compared with anything.
		let cases = [
			(
				"memory heap: u32;
				const BAD: u32 = 1 / 0;
				func f(a: heap::&[u8; BAD]) { local b: heap::&[u8; 4] = a; }",
				DiagnosticCode::ConstEvaluationFailed,
			),
			(
				"memory heap: u32;
				const A: u32 = B;
				const B: u32 = A;
				func f(a: heap::&[u8; A]) { local b: heap::&[u8; 4] = a; }",
				DiagnosticCode::CyclicConstant,
			),
			(
				"trait Tr { type Item; }
				struct P();
				impl Tr for P { type Item = <P as Tr>::Item; }
				func f(a: <P as Tr>::Item) { local b: u8 = a; }",
				DiagnosticCode::CyclicAssociatedType,
			),
		];
		for (source, owner) in cases {
			let case = TestCase::new(source);
			case.diagnostics().assert_codes(&[owner]);
		}
	}

	#[test]
	fn slices_and_arrays_have_the_slice_traits() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func f(s: heap::&[u8], a: heap::*[u16; 4]) {
					local n: u32 = s.len();
					local k: u32 = <[u16; 4] as Array>::LEN;
					local t: heap::*[u16] = a.as_slice_mut();
					local v: <[u8] as Slice>::Value = 5;
					local w: heap::&u8 = s.last();
					local u: heap::&[u16] = a.as_slice();
				}
				func g<M: Memory, T>(s: M::&[T]) -> M::Size { s.len() - 1 }
				func h<M: Memory, S: Slice>(s: M::&S) -> M::&S::Value { s.first() }
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block \
			 (local n#2 (abstract len<[u8], heap> s#0)) \
			 (local k#3 (abstract LEN<[u16; 4]>)) \
			 (local t#4 (abstract as_slice_mut<[u16; 4], heap> a#1)) \
			 (local v#5 5) \
			 (local w#6 (abstract last<[u8], heap> s#0)) \
			 (local u#7 (abstract as_slice<[u16; 4], heap> (.& (* a#1)))))"
		);
	}

	#[test]
	fn pointers_have_the_pointer_trait() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct Is<
					P: Pointer where { Memory = M, Pointee = T },
					M: Memory,
					T,
				>();
				struct Needs<P: Pointer>();
				func concrete(a: Is<heap::&u8, heap, u8>, b: Is<heap::*(u8, u64), heap, (u8, u64)>) {}
				func generic<M: Memory, T>(p: Is<M::*T, M, T>) {}
				func pointee<M: Memory, T: StackValue>(x: <M::&T as Pointer>::Pointee) -> T { x }
				func size<P: Pointer>(n: <P::Memory as Memory>::Size) {}
				func element<M: Memory, S: Slice>(p: M::&<M::*S as Pointer>::Pointee) -> M::&S::Value { p[0].& }
				func not_pointers(a: Needs<u32>, b: Needs<(heap::&u8, u8)>) {}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
		]);
	}

	#[test]
	fn pointer_metadata_keeps_recursive_slice_equalities_rigid() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				trait Tr { type Item; }
				func direct<T: Tr where { Item = [T::Item] }>(
					p: heap::&T::Item,
				) -> <heap::&T::Item as Pointer>::Metadata {
					metadata(p)
				}
				func mutual<
					T: Tr where { Item = [U::Item] },
					U: Tr where { Item = [T::Item] },
				>(p: heap::*T::Item) -> heap::&T::Item { transmute(p) }
				func nested<T: Tr where { Item = [[T::Item]] }>(
					p: heap::&[T::Item],
				) -> <heap::&[T::Item] as Pointer>::Metadata {
					metadata(p)
				}
				func not_thin<T: Tr where { Item = [T::Item] }>(
					p: heap::&T::Item,
				) -> u32 { transmute(p) }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
	}

	#[test]
	fn a_pointer_carries_its_pointee_counts_as_metadata() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct Is<P: Pointer where { Metadata = X }, X: StackValue>();
				func concrete(
					a: Is<heap::&u8, ()>,
					b: Is<heap::&[u8], u32>,
					c: Is<heap::*[u8; 4], ()>,
					d: Is<heap::&[[u16]], (u32, u32)>,
					e: Is<heap::&heap::&[u8], ()>,
				) {}
				func memory<M: Memory>(a: Is<M::&[u8], M::Size>, b: Is<M::*u8, ()>) {}
				func thin<M: Memory, T: StackValue, A: Array>(
					a: Is<M::&T, ()>,
					b: Is<M::*A, ()>,
				) {}
				func unknown<M: Memory, T>(x: <M::&T as Pointer>::Metadata) -> () { x }
				func rigid<M: Memory, S: Slice>(
					x: <M::*S as Pointer>::Metadata,
				) -> <M::&S as Pointer>::Metadata {
					x
				}
				func not_thin<M: Memory, S: Slice>(x: <M::&S as Pointer>::Metadata) -> () { x }
			"});
		// Neither an unbounded `T` nor a `Slice` that may not be an array is
		// known to be thin.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::TypeMistmatch,
		]);
	}

	#[test]
	fn a_pointer_is_held_as_its_address_and_metadata() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct Needs<V: StackValue>();
				func nested(p: heap::&[[u8]]) -> (u32, u32, u32) { transmute(p) }
				func shared<M: Memory, S: Slice>(p: M::*S) -> M::&S { transmute(p) }
				func held<M: Memory, S: Slice>(a: Needs<M::&S>, b: Needs<(M::*S, u8)>) {}
				func not_thin<M: Memory, S: Slice>(p: M::&S) -> M::Size { transmute(p) }
			"});
		case.diagnostics().print();
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
	}

	#[test]
	fn a_pointer_is_built_from_and_taken_apart_into_its_parts() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func slice(address: u32, len: u32) -> heap::&[u8] {
					from_raw_parts(address, len)
				}
				func value(address: u32) -> heap::*u64 { from_raw_parts(address, ()) }
				func len(s: heap::&[u8]) -> u32 { metadata(s) }
				func start(s: heap::&[u8]) -> u32 { address(s) }
				func generic_address<M: Memory, T>(p: M::*T) -> M::Size { address(p) }
				func thin(p: heap::*[u8; 4]) -> () { metadata(p) }
				func generic_len<M: Memory, T: StackValue>(s: M::&[T]) -> M::Size {
					metadata(s)
				}
				func rebuild<P: Pointer>(p: P, at: <P::Memory as Memory>::Size) -> P {
					from_raw_parts::<P>(at, metadata(p))
				}
				func round_trip<P: Pointer>(p: P) -> P { from_raw_parts(address(p), metadata(p)) }
				func passed<P: Pointer>(p: P) -> P { transmute(p) }
				func no_length(address: u32) -> heap::&[u8] { from_raw_parts(address, ()) }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
	}

	/// The message states the equality with the use's arguments; the label
	/// says what its sides reduce to.
	#[test]
	fn an_equality_mismatch_states_the_equality_and_shows_the_values() {
		let case = TestCase::new(indoc! {"
				trait Container { type Item; }
				struct Bytes(); impl Container for Bytes { type Item = u8; }
				struct Words(); impl Container for Words { type Item = u16; }
				func same<A: Container, B: Container where { Item = A::Item }>() {}
				func pair() { same::<Bytes, Words>(); }
				func widen(x: u32) -> u64 { transmute(x) }
			"});
		let diagnostics = case.diagnostics();
		diagnostics.assert_codes(&[
			DiagnosticCode::AssocTypeEqualityMismatch,
			DiagnosticCode::AssocTypeEqualityMismatch,
		]);
		diagnostics.assert_error_saying(
			"type mismatch resolving \
			 `<Words as Container>::Item == <Bytes as Container>::Item`",
		);
		diagnostics.assert_error_saying(
			"type mismatch resolving \
			 `<u64 as StackValue>::Repr == <u32 as StackValue>::Repr`",
		);
		let rendered = diagnostics.render();
		assert!(
			rendered.contains("expected `u8`, found `u16`"),
			"{rendered}"
		);
		assert!(
			rendered.contains("expected `i32`, found `i64`"),
			"{rendered}"
		);
	}

	/// std is the last place a name is looked up, so the program's own items
	/// shadow its: `address(5)` calls the program's `address`, not std's.
	#[test]
	fn a_program_item_shadows_the_std_prelude() {
		let case = TestCase::new(indoc! {"
				struct Layout();
				func trap() {}
				func address(x: u32) -> u32 { x }
				func f() -> u32 { address(5) }
			"});
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_value_is_a_stack_value() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				type R = [u8];
				struct S(x: [u8; 4]);
				func f(x: [u8]) {}
				func g() -> R { trap() }
				func h(t: ([u8], u8), c: func([u16; 2]) -> u8) {}
				func k<M: Memory, T: Slice>(t: T, ok: M::&T) {}
				func l(p: heap::&[u8]) { local v: [u8; 2] = trap(); }
				func m<M: Memory, T>(t: T, p: M::&[T], q: M::*[T; 3], r: ([u8])) {}
				func n() -> S { trap() }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
		]);
		case.diagnostics().assert_error_saying(
			"`[u8]` is a slice, which only a pointer holds, as `M::&[u8]`",
		);
		case.diagnostics().assert_error_saying(
			"`T` is not known to be a `StackValue`: require `T: StackValue`",
		);
		case.diagnostics().assert_error_saying(
			"`S` cannot be held by value, since it holds `[u8; 4]`",
		);
	}

	/// A field, a tuple's element and a type argument need nothing: what holds
	/// them by value states what it needs.
	#[test]
	fn a_type_argument_may_be_a_slice() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct Box<T>(p: heap::*T);
				struct Header(len: u32, data: [u8; 16]);
				func id<M: Memory, T>(p: M::&T) -> M::&T { p }
				func len<M: Memory, S: Slice>(p: M::&S) -> M::Size { p.len() }
				func of_array<A: Array>() {}
				func value<T: StackValue>() {}
				func f(s: heap::&[u8], b: Box<[u8]>, h: heap::&Header) {
					local p = id(s);
					local n = len(s);
					local b: Box<[u8]> = Box(b.p);
					of_array::<[u8; 2]>();
					of_array::<[u8]>();
					value::<[u8]>();
					local z = size_of::<[u8], heap>();
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitBoundViolation,
			DiagnosticCode::TraitBoundViolation,
		]);
	}

	#[test]
	fn a_load_reads_a_stack_value() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func f<M: Memory, T>(p: M::&T) { local x = p.*; }
				func g<M: Memory, T: StackValue>(p: M::&T) -> T { p.* }
				func h(p: heap::&[u8; 2]) { local x = p.*; }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NotStackValue,
			DiagnosticCode::NotStackValue,
		]);
	}

	/// An abstract pointee is thin when it is a `StackValue`, which holds no
	/// slice; otherwise its pointer's metadata is unknown.
	#[test]
	fn a_pointer_to_an_unbounded_parameter_may_be_fat() {
		let case = TestCase::new(indoc! {"
				func thin<M: Memory, T: StackValue>(p: M::&T) -> M::Size {
					transmute(p)
				}
				func fat<M: Memory, T>(p: M::&T) -> M::Size { transmute(p) }
				func any<M: Memory, T>(p: M::&T) -> M::&T { p }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
	}

	#[test]
	fn a_literal_is_data_its_context_places() {
		let case = TestCase::new(indoc! {r#"
				memory heap: u32;
				const GREETING: [u8; 5] = "hello";
				const SHORT: heap::&[u8; 4] = GREETING;
				const WORDS: heap::&[u16] = GREETING;
				const MUTABLE: heap::*[u8] = GREETING;
				func f() {
					local s: heap::&[u8] = GREETING;
					local t: heap::&[u8; _] = "abc";
					local u = "abc";
					local v = GREETING;
					local w = "a" + "b";
				}
			"#});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::ArraySizeMismatch,
			DiagnosticCode::TypeMistmatch,
			DiagnosticCode::UnableToCoerce,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TypeAnnotationRequired,
			DiagnosticCode::TraitBoundViolation,
		]);
		case.diagnostics().assert_error_saying(
			"this constant holds 5 elements, but `heap::&[u8; 4]` holds 4",
		);
		case.diagnostics()
			.assert_error_saying("cannot apply `+` to a string literal");
		assert_eq!(
			case.shape("f"),
			"(block \
			 (local s#0 GREETING) \
			 (local t#1 \"abc\") \
			 (local u#2 \"abc\") \
			 (local v#3 GREETING) \
			 (local w#4 error))"
		);
	}

	#[test]
	fn a_method_of_a_slice_takes_its_ownership_from_the_receiver() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func f(a: heap::&[u8; 2]) { a.as_slice_mut(); }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TypeMistmatch]);
	}

	#[test]
	fn an_element_is_a_place_in_the_slice() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func f(s: heap::&[u8], a: heap::*[u16; 4], m: heap::&[heap::&[u8]]) {
					local e: u8 = s[0];
					a[1] = 5;
					a[2] += 1;
					local r: heap::&u8 = m[0][1].&;
				}
				func g<M: Memory, S: Slice where { Value: StackValue }>(
					s: M::&S,
					i: M::Size,
				) -> S::Value {
					s[i]
				}
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block \
			 (local e#3 (load ([] (* s#0) 0))) \
			 (store ([] (* a#1) 1) 5) \
			 (store += ([] (* a#1) 2) 1) \
			 (local r#4 (.& ([] (* (load ([] (* m#2) 0))) 1))))"
		);
		assert_eq!(case.shape("g"), "(block => (load ([] (* s#0) i#1)))");
	}

	/// An array place is indexed where it is, as a struct place's field is
	/// read: `h.data[i]` through the pointer `h`, writable when `h` is
	/// exclusive. `s.*[i]` is the same element as `s[i]`.
	#[test]
	fn an_array_place_is_indexed_in_place() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct Header(len: u32, data: [u8; 4]);
				func f(h: heap::*Header, s: heap::&[u8], m: heap::&[[u8; 2]]) {
					h.data[1] = 5;
					local a: u8 = s.*[0];
					local b: u8 = m[1][0];
				}
				func g(h: heap::&Header) { h.data[0] = 1; }
				func k(h: heap::&Header) { local x = h.len[0]; }
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::CannotMutateImmutable,
			DiagnosticCode::CannotIndex,
		]);
		assert_eq!(
			case.shape("f"),
			"(block \
			 (store ([] (. (* h#0) data) 1) 5) \
			 (local a#3 (load ([] (* s#1) 0))) \
			 (local b#4 (load ([] ([] (* m#2) 1) 0))))"
		);
	}

	#[test]
	fn an_element_of_a_shared_slice_is_read_only() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func f(s: heap::&[u8]) { s[0] = 1; }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CannotMutateImmutable]);
	}

	#[test]
	fn only_a_slice_or_an_array_is_indexed() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				func f(ps: heap::&heap::&[u8], o: Ordering) {
					local a: u8 = ps[0];
					local b: u8 = o[0];
					local c: u8 = 7[0];
				}
			"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::CannotIndex,
			DiagnosticCode::CannotIndex,
			DiagnosticCode::TypeAnnotationRequired,
		]);
		case.diagnostics().assert_error_saying(
			"dereference the outer one first, as `x.*[i]`",
		);
	}

	#[test]
	fn a_field_is_reached_through_one_pointer() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct P(x: u32, next: heap::&P);
				func f(p: heap::*P) {
					local x: u32 = p.x;
					p.x = 3;
					local y: u32 = p.next.x;
					local z: u32 = p.*.x;
				}
				func g(pp: heap::&heap::&P) -> u32 { pp.x }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnknownStructField]);
		case.diagnostics().assert_error_saying("as `p.*.field`");
		assert_eq!(
			case.shape("f"),
			"(block \
			 (local x#1 (load (. (* p#0) x))) \
			 (store (. (* p#0) x) 3) \
			 (local y#2 (load (. (* (load (. (* p#0) next))) x))) \
			 (local z#3 (load (. (* p#0) x))))"
		);
	}

	#[test]
	fn a_field_through_a_pointer_is_a_place() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct P(x: u32, next: heap::&P);
				func f(p: heap::*P, s: heap::&[heap::&P], v: heap::&[P]) {
					p.x += 1;
					local r: heap::&u32 = p.x.&;
					local a: u32 = (p.*).x;
					local b: u32 = s[0].x;
					local c: u32 = v[0].x;
				}
			"});
		case.diagnostics().assert_none();
		assert_eq!(
			case.shape("f"),
			"(block \
			 (store += (. (* p#0) x) 1) \
			 (local r#3 (.& (. (* p#0) x))) \
			 (local a#4 (load (. (* p#0) x))) \
			 (local b#5 (load (. (* (load ([] (* s#1) 0))) x))) \
			 (local c#6 (load (. ([] (* v#2) 0) x))))"
		);
	}

	#[test]
	fn a_field_through_a_shared_pointer_is_read_only() {
		let case = TestCase::new(indoc! {"
				memory heap: u32;
				struct P(x: u32);
				func f(p: heap::&P) { p.x = 1; }
			"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::CannotMutateImmutable]);
	}
}
