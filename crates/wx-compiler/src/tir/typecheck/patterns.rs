//! Patterns: what a `local` or a match arm takes apart, binds and tests.
//!
//! A pattern is checked against the type it is given (a `local`'s value's, a
//! match's scrutinee's), from the outside in, into the body's pattern arena.
//! What each term is was decided while parsing: a name binds, a literal
//! tests, a qualified path compares with a constant. Destructuring has one
//! child per element or field of its type, in declaration order, whatever was
//! written: what `..` covers, and a field a named pattern leaves out, is a
//! `Wildcard`.
//!
//! A value path never sees locals: `const y` names a constant `y`, and a
//! local of that name only earns a note on the "cannot find" report.
//!
//! The alternatives of a `|` bind the same names. The same name in two
//! alternatives is one local, bound the same way and of the same type in
//! both, so the body of the arm reads one value.
//!
//! A pattern test compares the matched value with a constant, so its type
//! must satisfy `Eq`. Enums answer it structurally because their repr is an
//! `Integer` typeset member. Floats and aggregate values without an `Eq` impl
//! are reported; an aggregate that has one still needs aggregate matching,
//! which is a later checkpoint. Such values can always be bound instead.

use std::ops::Range;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::{BodyBuilder, Integer, ValuePath};
use crate::ast::{self, Keyword, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{ExprKind, LocalIdx, PatIdx, PatternKind};
use crate::tir::decls::{BindingTarget, DeclKind, StructIdx, TraitIdx};
use crate::tir::imports::report_private_identifier;
use crate::tir::literals::{CharLiteralError, parse_char_literal};
use crate::tir::resolutions::{AccessKind, Reference, Site};
use crate::tir::solver::SolverError;
use crate::tir::types::{GenericArgs, GenericEnvOwner, Type, TypeIndex};
use crate::vfs::FileId;

/// The state of checking one pattern: where it is written, and the names it
/// has bound.
pub(super) struct PatternContext {
	/// Whether the pattern may test a value. A match arm may; a `local`
	/// always matches, so a test in one is a mistake.
	refutable: bool,
	/// Whether a test in a `local` has already been reported: one mistake is
	/// one report, however many tests the pattern holds.
	reported_refutable: bool,
	/// Every name the pattern binds, in the order it binds them. A name
	/// bound in two alternatives of one `|` is one local, listed once per
	/// alternative that binds it.
	bindings: Vec<LocalIdx>,
	/// The frames of the pattern being checked, outermost first: the
	/// pattern's own product, then the alternatives of a `|`, then the
	/// alternative being checked.
	frames: Vec<Frame>,
}

/// One level of the pattern at which names are bound.
struct Frame {
	kind: FrameKind,
	/// Where in the context's `bindings` this frame's names begin.
	start: u32,
}

/// What the names bound in a frame name.
enum FrameKind {
	/// A product: one value taken apart. The names bound in it name
	/// different values, so the same name twice is a mistake.
	Product,
	/// The alternatives of a `|`: one value matched several ways. The
	/// names bound in it name the same value, so the same name in two
	/// alternatives is one local.
	Alternatives,
}

/// One alternative of a `|`: the pattern it checked to, and the names it
/// bound.
struct Alternative {
	/// The pattern it checked to, in the arena.
	pattern: PatIdx,
	/// The names it bound: the range of the context's `bindings` it
	/// covered.
	bound: Range<usize>,
}

impl Alternative {
	/// The names it bound: the bindings it covers.
	fn bindings<'a>(&self, context: &'a PatternContext) -> &'a [LocalIdx] {
		&context.bindings[self.bound.clone()]
	}
}

impl PatternContext {
	/// A `local` statement's pattern, which always matches: it holds no
	/// tests.
	pub(super) fn local() -> Self {
		Self {
			refutable: false,
			reported_refutable: false,
			bindings: Vec::new(),
			frames: vec![Frame {
				kind: FrameKind::Product,
				start: 0,
			}],
		}
	}

	/// A match arm's pattern.
	pub(super) fn arm() -> Self {
		Self {
			refutable: true,
			reported_refutable: false,
			bindings: Vec::new(),
			frames: vec![Frame {
				kind: FrameKind::Product,
				start: 0,
			}],
		}
	}

	/// Opens a frame: a product for the pattern or one alternative, the
	/// alternatives of a `|`.
	fn open(&mut self, kind: FrameKind) {
		let start = u32::try_from(self.bindings.len()).unwrap();
		self.frames.push(Frame { kind, start });
	}

	/// Closes the innermost frame, returning the range of `bindings` its
	/// names are in. The range, not a slice: the caller holds it while
	/// more names are bound, and the bindings may move.
	fn close(&mut self) -> Range<usize> {
		let frame = self.frames.pop().unwrap();
		usize::try_from(frame.start).unwrap()..self.bindings.len()
	}

	/// Records a binding in the frame being filled.
	fn record(&mut self, local: LocalIdx) {
		self.bindings.push(local);
	}

	/// The bindings of the frame at `at`. A frame covers what was bound in
	/// it, and in the frames that closed inside it; the frame above it,
	/// still open, is not yet its own.
	fn frame_bindings(&self, at: usize) -> &[LocalIdx] {
		let start = usize::try_from(self.frames[at].start).unwrap();
		let end = self
			.frames
			.get(at + 1)
			.map_or(self.bindings.len(), |above| {
				usize::try_from(above.start).unwrap()
			});
		&self.bindings[start..end]
	}
}

impl BodyBuilder<'_, '_> {
	/// Checks `pattern` against `expected`, declaring its bindings in the
	/// current scope.
	pub(super) fn check_pattern(
		&mut self,
		pattern: ast::PatId,
		expected: TypeIndex,
		context: &mut PatternContext,
	) -> PatIdx {
		let ast = self.ast();
		let span = ast.pattern_span(pattern);
		match ast.pattern(pattern) {
			ast::Pattern::Wildcard => {
				self.body
					.push_pattern(PatternKind::Wildcard, expected, span)
			}
			ast::Pattern::Binding { name, .. } => {
				let mut_span = ast.pattern_mut_span(pattern);
				self.bind(name, mut_span, expected, span, context)
			}
			ast::Pattern::Constant { path } => {
				let expected = self.check_refutable(context, span, expected);
				self.check_value_path(ast.list(path), span, expected)
			}
			ast::Pattern::Literal(literal) => {
				let expected = self.check_refutable(context, span, expected);
				self.check_literal(&literal, span, expected)
			}
			ast::Pattern::Or(alternatives) => {
				// The alternatives of a `|` bind the same names: the same
				// name in two of them is one local, which they share.
				context.open(FrameKind::Alternatives);
				let mut checked = Vec::with_capacity(alternatives.len());
				for &alternative in ast.list(alternatives) {
					context.open(FrameKind::Product);
					let pattern =
						self.check_pattern(alternative, expected, context);
					let bound = context.close();
					checked.push(Alternative { pattern, bound });
				}
				context.close();
				self.check_alternatives(context, &checked);
				let alternatives = self.body.push_patterns(
					checked.iter().map(|checked| checked.pattern),
				);
				self.body.push_pattern(
					PatternKind::Or(alternatives),
					expected,
					span,
				)
			}
			ast::Pattern::Destructure(destructure) => {
				self.check_destructure(destructure, span, expected, context)
			}
			ast::Pattern::Error => self.error_pattern(span),
		}
	}

	/// A `local` always matches, so a test in one is a mistake. The rest of
	/// the pattern is still checked, so the bindings it makes resolve; every
	/// test is checked against `ERROR`, so it says nothing more, and only
	/// the first one is reported.
	fn check_refutable(
		&mut self,
		context: &mut PatternContext,
		span: TextSpan,
		expected: TypeIndex,
	) -> TypeIndex {
		if context.refutable {
			return self.check_pattern_equality(expected, span);
		}
		if !context.reported_refutable {
			context.reported_refutable = true;
			self.sema.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::RefutablePatternInLocal.code())
					.with_message("a `local` pattern cannot test a value")
					.with_label(
						Label::primary(self.scope.file_id, span)
							.with_message("this tests a value"),
					)
					.with_note(
						"a `local` always matches; test values with `match`",
					),
			);
		}
		TypeIndex::ERROR
	}

	/// A constant or literal pattern compares the matched value with a known
	/// value, so the matched type must implement `Eq`. The solver answers for
	/// enums structurally: their repr is an `Integer` typeset member, so every
	/// enum has `Eq` without an explicit impl. Floats only have partial
	/// equality, and an aggregate needs its own `Eq` impl; bind those values
	/// with `_` or a name instead.
	fn check_pattern_equality(
		&mut self,
		ty: TypeIndex,
		span: TextSpan,
	) -> TypeIndex {
		if ty == TypeIndex::ERROR {
			return ty;
		}
		let normalized = self.context().normalized(ty);
		match *self.sema.types.resolve(normalized) {
			// A literal or inference placeholder has its own diagnostic.
			Type::Error
			| Type::Infer
			| Type::ConstInt
			| Type::ConstFloat
			| Type::ConstChar => return ty,
			// Unplaced data has its own diagnostic too.
			Type::Slice { .. } | Type::Array { .. } => return ty,
			_ => {}
		}
		let trait_index = self
			.sema
			.decls
			.intrinsics
			.eq
			.expect("the core must declare the `Eq` trait");
		match self.sema.find_trait_impl_query(
			self.builder.strings,
			self.scope.assumption_env,
			normalized,
			trait_index,
		) {
			Ok(Some(_)) => ty,
			Ok(None) => {
				self.report_pattern_eq_violation(ty, trait_index, span);
				TypeIndex::ERROR
			}
			Err(SolverError::Overflow) => {
				let site = SourceSpan::new(self.scope.file_id, span);
				self.sema
					.diagnostics
					.push(self.sema.overflow_diagnostic(site));
				TypeIndex::ERROR
			}
			Err(SolverError::Cycle(cycle)) => {
				let site = SourceSpan::new(self.scope.file_id, span);
				let diagnostic = self.sema.cycle_diagnostic(
					self.builder.strings,
					&cycle,
					site,
				);
				self.sema.diagnostics.push(diagnostic);
				TypeIndex::ERROR
			}
			// Another construct owns the error or the answer is not final.
			Err(SolverError::Pending | SolverError::Poisoned) => ty,
		}
	}

	/// Reports that a pattern test's type does not implement `Eq`.
	fn report_pattern_eq_violation(
		&mut self,
		ty: TypeIndex,
		trait_index: TraitIdx,
		span: TextSpan,
	) {
		let name = self
			.sema
			.type_formatter(self.builder.strings)
			.display_type(ty)
			.to_string();
		let trait_name = self
			.builder
			.strings
			.resolve(self.sema.decls.name(trait_index).inner)
			.unwrap()
			.to_string();
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TraitBoundViolation.code())
				.with_message(format!(
					"the trait bound `{name}: {trait_name}` is not satisfied"
				))
				.with_label(
					Label::primary(self.scope.file_id, span).with_message(
						format!(
							"the trait `{trait_name}` is not implemented for `{name}`"
						),
					),
				)
				.with_note(
					"a `match` value pattern requires type to implement `Eq`",
				),
		);
	}

	/// A binding: a local of the matched part's type.
	fn bind(
		&mut self,
		name: Spanned<SymbolU32>,
		mut_span: Option<TextSpan>,
		expected: TypeIndex,
		span: TextSpan,
		context: &mut PatternContext,
	) -> PatIdx {
		// A name bound in a product names a different value each time: the
		// same name twice is a mistake. A name bound in the alternatives of
		// a `|` names the same value, seen two ways: it is one local, bound
		// the same way and of the same type in both.
		let mut product = None;
		let mut alternatives = None;
		for (at, frame) in context.frames.iter().enumerate() {
			match frame.kind {
				FrameKind::Product => {
					if product.is_none() {
						product = self.frame_binding(context, at, name.inner);
					}
				}
				FrameKind::Alternatives => {
					if alternatives.is_none() {
						alternatives =
							self.frame_binding(context, at, name.inner);
					}
				}
			}
		}
		if let Some(first) = product {
			let text = self.builder.strings.resolve(name.inner).unwrap();
			let first_span = self.body.local(first).name.span;
			self.sema.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::DuplicatePatternBinding.code())
					.with_message(format!(
						"`{text}` is bound more than once in the same pattern"
					))
					.with_label(Label::primary(self.scope.file_id, name.span))
					.with_label(
						Label::secondary(self.scope.file_id, first_span)
							.with_message("first bound here"),
					),
			);
		}
		let local = match alternatives {
			Some(local) => {
				// One local, bound in two alternatives: it must be bound the
				// same way, and have the same type, in both.
				let bound = *self.body.local(local);
				if bound.mut_span.is_some() != mut_span.is_some() {
					let text =
						self.builder.strings.resolve(name.inner).unwrap();
					self.sema.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::InconsistentPatternBinding
									.code(),
							)
							.with_message(format!(
								"variable `{text}` is bound inconsistently across \
								 alternatives separated by `|`"
							))
							.with_label(
								Label::primary(self.scope.file_id, span)
									.with_message("bound differently here"),
							)
							.with_label(
								Label::secondary(
									self.scope.file_id,
									bound.name.span,
								)
								.with_message("first bound here"),
							),
					);
				}
				if self.sema.types.meet(bound.ty, expected).is_none() {
					let diagnostic = self.binding_mismatch(
						bound.ty,
						expected,
						span,
						bound.name.span,
					);
					self.sema.diagnostics.push(diagnostic);
				}
				local
			}
			None => self.declare_local(name, expected, mut_span),
		};
		context.record(local);
		self.body
			.push_pattern(PatternKind::Bind(local), expected, span)
	}

	/// The local a frame binds for a name, if it binds one.
	fn frame_binding(
		&self,
		context: &PatternContext,
		at: usize,
		name: SymbolU32,
	) -> Option<LocalIdx> {
		context
			.frame_bindings(at)
			.iter()
			.copied()
			.find(|&local| self.body.local(local).name.inner == name)
	}

	/// The local an alternative binds for a name, if it binds one.
	fn alternative_binding(
		&self,
		context: &PatternContext,
		alternative: &Alternative,
		name: SymbolU32,
	) -> Option<LocalIdx> {
		alternative
			.bindings(context)
			.iter()
			.copied()
			.find(|&local| self.body.local(local).name.inner == name)
	}

	/// Every alternative of a `|` must bind the same names: a name one of
	/// them binds and another does not is bound only sometimes.
	fn check_alternatives(
		&mut self,
		context: &PatternContext,
		alternatives: &[Alternative],
	) {
		// The names the alternatives bind, and the local each is bound to:
		// the first binding of a name is the one that counts.
		let mut names: Vec<(SymbolU32, LocalIdx)> = Vec::new();
		for alternative in alternatives {
			for local in alternative.bindings(context).iter().copied() {
				let name = self.body.local(local).name.inner;
				if !names.iter().copied().any(|(bound, _)| bound == name) {
					names.push((name, local));
				}
			}
		}
		for (name, local) in names {
			// An alternative that does not bind it: the name is bound only
			// sometimes.
			let mut missing = false;
			for alternative in alternatives {
				if self
					.alternative_binding(context, alternative, name)
					.is_none()
				{
					missing = true;
					break;
				}
			}
			if !missing {
				continue;
			}
			let text = self.builder.strings.resolve(name).unwrap();
			let bound_span = self.body.local(local).name.span;
			let mut diagnostic = Diagnostic::error()
				.with_code(DiagnosticCode::NotBoundInAllAlternatives.code())
				.with_message(format!(
					"variable `{text}` is not bound in all patterns"
				))
				.with_label(
					Label::primary(self.scope.file_id, bound_span)
						.with_message("not bound in all patterns"),
				);
			for alternative in alternatives {
				if self
					.alternative_binding(context, alternative, name)
					.is_none()
				{
					let span = self.body.pattern_span(alternative.pattern);
					diagnostic = diagnostic.with_label(
						Label::secondary(self.scope.file_id, span)
							.with_message(format!(
								"pattern doesn't bind `{text}`"
							)),
					);
				}
			}
			self.sema.diagnostics.push(diagnostic);
		}
	}

	/// A binding of one type in an alternative and another in the next.
	fn binding_mismatch(
		&self,
		expected: TypeIndex,
		found: TypeIndex,
		span: TextSpan,
		first: TextSpan,
	) -> Diagnostic<FileId> {
		let formatter = self.sema.type_formatter(self.builder.strings);
		Diagnostic::error()
			.with_code(DiagnosticCode::TypeMistmatch.code())
			.with_message("type mismatch")
			.with_label(Label::primary(self.scope.file_id, span).with_message(
				format!(
					"expected `{}`, found `{}`",
					formatter.display_type(expected),
					formatter.display_type(found)
				),
			))
			.with_label(
				Label::secondary(self.scope.file_id, first).with_message(
					format!(
						"first introduced with type `{}` here",
						formatter.display_type(expected)
					),
				),
			)
			.with_note(
				"in the same arm, a binding must have the same type in all \
				 alternatives",
			)
	}

	/// A tuple or struct pattern, with one child per element or field.
	fn check_destructure(
		&mut self,
		destructure: ast::Destructure,
		span: TextSpan,
		expected: TypeIndex,
		context: &mut PatternContext,
	) -> PatIdx {
		let ast = self.ast();
		match destructure {
			// A tuple of one is its element: `(p,)` and `(p)` are `p`.
			ast::Destructure::Tuple { elements }
				if let [ast::PatternElement::Pattern(pattern)] =
					*ast.list(elements) =>
			{
				self.check_pattern(pattern, expected, context)
			}
			ast::Destructure::Tuple { elements } => {
				self.check_tuple(elements, span, expected, context)
			}
			ast::Destructure::Struct { path, elements } => {
				let Some((struct_index, ty, types)) =
					self.pattern_struct(ast.list(path), span, expected)
				else {
					return self.check_poisoned(elements, span, context);
				};
				let Some(fields) = self.check_field_list(
					elements,
					struct_index,
					&types,
					span,
					context,
				) else {
					return self.error_pattern(span);
				};
				self.body.push_pattern(
					PatternKind::Struct {
						struct_index,
						fields,
					},
					ty,
					span,
				)
			}
			ast::Destructure::NamedStruct { path, fields } => {
				let Some((struct_index, ty, types)) =
					self.pattern_struct(ast.list(path), span, expected)
				else {
					for item in ast.list(fields) {
						if let ast::PatternFieldItem::Field(field) = item {
							self.check_field(field, TypeIndex::ERROR, context);
						}
					}
					return self.error_pattern(span);
				};
				let Some(children) = self.check_fields(
					fields,
					struct_index,
					&types,
					span,
					context,
				) else {
					return self.error_pattern(span);
				};
				let fields = self.fields_value(children, &types, span);
				self.body.push_pattern(
					PatternKind::Struct {
						struct_index,
						fields,
					},
					ty,
					span,
				)
			}
		}
	}

	/// `(a, b)` against `expected`, with one child per element.
	fn check_tuple(
		&mut self,
		elements: ast::List<ast::PatternElement>,
		span: TextSpan,
		expected: TypeIndex,
		context: &mut PatternContext,
	) -> PatIdx {
		let types = match *self.sema.types.resolve(expected) {
			Type::Tuple { elements } => self.sema.types.list(elements).to_vec(),
			_ => {
				if expected != TypeIndex::ERROR {
					self.report_pattern_mismatch(expected, "a tuple", span);
				}
				return self.check_poisoned(elements, span, context);
			}
		};
		let Some(children) =
			self.check_elements(elements, &types, span, context, None)
		else {
			return self.error_pattern(span);
		};
		let children = self.body.push_patterns(children);
		self.body
			.push_pattern(PatternKind::Tuple(children), expected, span)
	}

	/// `Name(...)`: the written list as one value of the struct's fields, as
	/// a construction gives them. One pattern for several fields (or none)
	/// matches them all as a tuple (`P(p)`); several for a lone field whose
	/// type is a tuple match that tuple (`W(a, b)`); otherwise each gives
	/// one field. `None` when the counts cannot fit (reported).
	fn check_field_list(
		&mut self,
		elements: ast::List<ast::PatternElement>,
		struct_index: StructIdx,
		types: &[TypeIndex],
		span: TextSpan,
		context: &mut PatternContext,
	) -> Option<PatIdx> {
		match (types, self.ast().list(elements)) {
			(_, &[ast::PatternElement::Pattern(pattern)]) => {
				let ty = self.sema.types.intern_tuple(types);
				Some(self.check_pattern(pattern, ty, context))
			}
			(&[field], _)
				if let Type::Tuple { .. } = self.sema.types.resolve(field) =>
			{
				Some(self.check_tuple(elements, span, field, context))
			}
			_ => {
				let children = self.check_elements(
					elements,
					types,
					span,
					context,
					Some(struct_index),
				)?;
				Some(self.fields_value(children, types, span))
			}
		}
	}

	/// One child per field as the value of them all: the child itself for a
	/// lone field, else a tuple of them.
	fn fields_value(
		&mut self,
		children: Vec<PatIdx>,
		types: &[TypeIndex],
		span: TextSpan,
	) -> PatIdx {
		if let [child] = *children {
			return child;
		}
		let ty = self.sema.types.intern_tuple(types);
		let children = self.body.push_patterns(children);
		self.body
			.push_pattern(PatternKind::Tuple(children), ty, span)
	}

	/// The children of a positional list against `types`, a tuple's elements
	/// or a struct's fields: the written ones before the first `..` take the
	/// first types, those after it the last, and `..` covers what is between.
	/// `None` when the counts cannot fit (reported, every child still checked).
	fn check_elements(
		&mut self,
		elements: ast::List<ast::PatternElement>,
		types: &[TypeIndex],
		span: TextSpan,
		context: &mut PatternContext,
		struct_index: Option<StructIdx>,
	) -> Option<Vec<PatIdx>> {
		let mut rest: Option<(usize, TextSpan)> = None;
		let mut written: Vec<ast::PatId> = Vec::new();
		for &item in self.ast().list(elements) {
			match item {
				ast::PatternElement::Pattern(pattern) => written.push(pattern),
				ast::PatternElement::Rest(at) => match rest {
					Some((_, first)) => self.report_duplicate_rest(at, first),
					None => rest = Some((written.len(), at)),
				},
			}
		}
		let count = types.len();
		let fits = match rest {
			Some(_) => written.len() <= count,
			None => written.len() == count,
		};
		if !fits {
			self.report_element_count(
				count,
				written.len(),
				rest.is_some(),
				span,
				struct_index,
			);
			for pattern in written {
				self.check_pattern(pattern, TypeIndex::ERROR, context);
			}
			return None;
		}
		let before = rest.map_or(written.len(), |(at, _)| at);
		let after = written.len() - before;
		let mut children = Vec::with_capacity(count);
		for (at, &pattern) in written[..before].iter().enumerate() {
			children.push(self.check_pattern(pattern, types[at], context));
		}
		if let Some((_, rest_span)) = rest {
			for &ty in &types[before..count - after] {
				children.push(self.body.push_pattern(
					PatternKind::Wildcard,
					ty,
					rest_span,
				));
			}
		}
		for (at, &pattern) in written[before..].iter().enumerate() {
			let ty = types[count - after + at];
			children.push(self.check_pattern(pattern, ty, context));
		}
		Some(children)
	}

	/// The children of `Name({ x, y: pat, .. })`, one per field in
	/// declaration order. A field not named is covered by `..`; without one
	/// it is reported and matched as `_`.
	fn check_fields(
		&mut self,
		fields: ast::List<ast::PatternFieldItem>,
		struct_index: StructIdx,
		types: &[TypeIndex],
		span: TextSpan,
		context: &mut PatternContext,
	) -> Option<Vec<PatIdx>> {
		let decl = &self.sema.decls.structs[usize::from(struct_index)];
		if !decl.is_fully_named() {
			let name = self
				.builder
				.strings
				.resolve(self.sema.decls.item(decl.loc).name.inner)
				.unwrap();
			self.sema.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TupleStructBracePattern.code())
					.with_message(format!(
						"struct `{name}` has unnamed fields, so it is matched \
						 with `{name}(...)`"
					))
					.with_label(Label::primary(self.scope.file_id, span)),
			);
			for item in self.ast().list(fields) {
				if let ast::PatternFieldItem::Field(field) = item {
					self.check_field(field, TypeIndex::ERROR, context);
				}
			}
			return None;
		}
		let mut rest: Option<TextSpan> = None;
		let mut given: Vec<Option<(PatIdx, TextSpan)>> =
			vec![None; types.len()];
		for item in self.ast().list(fields) {
			let field = match item {
				ast::PatternFieldItem::Rest(at) => {
					match rest {
						Some(first) => self.report_duplicate_rest(*at, first),
						None => rest = Some(*at),
					}
					continue;
				}
				ast::PatternFieldItem::Field(field) => field,
			};
			let name = field.name;
			let decl = &self.sema.decls.structs[usize::from(struct_index)];
			let Some(index) = decl.lookup.get(&name.inner).copied() else {
				let struct_name = self
					.builder
					.strings
					.resolve(self.sema.decls.item(decl.loc).name.inner)
					.unwrap();
				let field_name =
					self.builder.strings.resolve(name.inner).unwrap();
				self.sema.diagnostics.push(
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
				self.check_field(field, TypeIndex::ERROR, context);
				continue;
			};
			self.sema.resolutions.record(
				Site::Value(SourceSpan::new(self.scope.file_id, name.span)),
				Reference::Field {
					access: AccessKind::Read,
					owner: struct_index,
					field: index,
				},
			);
			let at = usize::from(index);
			if let Some((_, first)) = given[at] {
				let field_name =
					self.builder.strings.resolve(name.inner).unwrap();
				self.sema.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::DuplicateStructFieldInit.code(),
						)
						.with_message(format!(
							"field `{field_name}` matched more than once"
						))
						.with_label(Label::primary(
							self.scope.file_id,
							name.span,
						))
						.with_label(
							Label::secondary(self.scope.file_id, first)
								.with_message("first matched here"),
						),
				);
				self.check_field(field, TypeIndex::ERROR, context);
				continue;
			}
			let child = self.check_field(field, types[at], context);
			given[at] = Some((child, name.span));
		}
		if rest.is_none() {
			let decl = &self.sema.decls.structs[usize::from(struct_index)];
			let missing: Vec<String> = given
				.iter()
				.enumerate()
				.filter(|(_, given)| given.is_none())
				.map(|(at, _)| {
					let name = decl.field_names[at].unwrap().inner;
					format!("`{}`", self.builder.strings.resolve(name).unwrap())
				})
				.collect();
			if !missing.is_empty() {
				let struct_name = self
					.builder
					.strings
					.resolve(self.sema.decls.item(decl.loc).name.inner)
					.unwrap();
				self.sema.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::MissingStructFields.code())
						.with_message(format!(
							"pattern does not mention field{} {}",
							if missing.len() == 1 { "" } else { "s" },
							missing.join(", ")
						))
						.with_label(Label::primary(self.scope.file_id, span))
						.with_note(format!(
							"write `..` to match the rest of `{struct_name}`"
						)),
				);
			}
		}
		let rest_span = rest.unwrap_or(span);
		let children = given
			.into_iter()
			.zip(types)
			.map(|(given, &ty)| match given {
				Some((child, _)) => child,
				None => {
					self.body.push_pattern(PatternKind::Wildcard, ty, rest_span)
				}
			})
			.collect();
		Some(children)
	}

	/// `x` or `x: pat` in a named struct pattern, against the field's type.
	fn check_field(
		&mut self,
		field: &ast::PatternField,
		expected: TypeIndex,
		context: &mut PatternContext,
	) -> PatIdx {
		match field.pattern {
			Some(pattern) => self.check_pattern(pattern, expected, context),
			// `{ x }` — the field binds a local of its own name.
			None => {
				self.bind(field.name, None, expected, field.name.span, context)
			}
		}
	}

	/// The struct a struct pattern names, its type as matched (the expected
	/// type, which must be that struct), and its fields' types. `None` when
	/// the path names no struct, or the expected type is not it (reported).
	fn pattern_struct(
		&mut self,
		path: &[ast::PathSegment],
		span: TextSpan,
		expected: TypeIndex,
	) -> Option<(StructIdx, TypeIndex, Vec<TypeIndex>)> {
		let segment = path.last().unwrap();
		let (struct_index, written) = if let [segment] = path
			&& segment.ident.inner == Keyword::SelfPascal.symbol()
		{
			let (struct_index, type_args) = self.impl_self_struct(segment)?;
			if !self.constructor_accessible(struct_index) {
				let diagnostic = self.report_private_constructor(
					struct_index,
					None,
					segment,
				);
				self.sema.diagnostics.push(diagnostic);
			}
			(struct_index, type_args)
		} else {
			let walk = match self.resolve_value_path(path, span) {
				Ok(ValuePath::Item(walk)) => walk,
				Ok(ValuePath::Member(_)) => {
					self.report_not_a_struct("an associated item", span);
					return None;
				}
				Err(_) => return None,
			};
			let key = walk.target.loc()?;
			let kind = key.symbol_kind(&self.sema.decls);
			let DeclKind::Struct(struct_index) = kind else {
				self.report_not_a_struct(&format!("a {}", kind.noun()), span);
				return None;
			};
			if let BindingTarget::Inaccessible(key) = walk.target {
				let diagnostic = self.report_private_constructor(
					struct_index,
					Some(key),
					segment,
				);
				self.sema.diagnostics.push(diagnostic);
			}
			let params =
				self.sema.structs[usize::from(struct_index)].type_params;
			let count = self.sema.generic_envs.param_names(params).len();
			let mut written = vec![TypeIndex::INFER; count].into_boxed_slice();
			self.write_type_args(
				segment,
				params,
				GenericEnvOwner::Struct(struct_index),
				&mut written,
			);
			(struct_index, written)
		};
		let named = self.sema.types.intern_struct(struct_index, &written);
		let ty = if expected == TypeIndex::ERROR {
			TypeIndex::ERROR
		} else {
			match self.sema.types.meet(expected, named) {
				Some(ty) => ty,
				None => {
					let diagnostic =
						self.context().mismatch_at(expected, named, span);
					self.sema.diagnostics.push(diagnostic);
					return None;
				}
			}
		};
		let type_args: Vec<TypeIndex> = match *self.sema.types.resolve(ty) {
			Type::Struct { type_args, .. } => {
				self.sema.types.list(type_args).to_vec()
			}
			_ => vec![TypeIndex::ERROR; written.len()],
		};
		let count = self.sema.structs[usize::from(struct_index)]
			.field_types
			.len();
		let types = (0..count)
			.map(|field| {
				self.context().field_type(struct_index, &type_args, field)
			})
			.collect();
		Some((struct_index, ty, types))
	}

	/// A literal, against the type it is compared with. An integer is stored
	/// as its bits in that type.
	fn check_literal(
		&mut self,
		literal: &ast::Literal,
		span: TextSpan,
		expected: TypeIndex,
	) -> PatIdx {
		if expected == TypeIndex::ERROR {
			return self.error_pattern(span);
		}
		match *literal {
			ast::Literal::Int(value) => {
				self.check_int(value, false, span, expected)
			}
			ast::Literal::NegInt(value) => {
				self.check_int(value, true, span, expected)
			}
			ast::Literal::Char => {
				let integer = Integer::from_type(expected);
				if expected != TypeIndex::CHAR && integer.is_none() {
					self.report_pattern_mismatch(expected, "a character", span);
					return self.error_pattern(span);
				}
				let source =
					&self.builder.files.get(self.scope.file_id).unwrap().source;
				match parse_char_literal(span.extract_str(source)) {
					Ok(value) => match integer {
						None => self.body.push_pattern(
							PatternKind::Char(value),
							expected,
							span,
						),
						Some(integer)
							if integer
								.contains(i128::from(u32::from(value))) =>
						{
							self.body.push_pattern(
								PatternKind::Int(u64::from(value)),
								expected,
								span,
							)
						}
						Some(_) => {
							let diagnostic = self.sema.report_out_of_range(
								self.builder.strings,
								format_args!("literal {value:?}"),
								expected,
								SourceSpan::new(self.scope.file_id, span),
							);
							self.sema.diagnostics.push(diagnostic);
							self.error_pattern(span)
						}
					},
					Err(error) => {
						let message = match error {
							CharLiteralError::Empty => {
								"empty character literal"
							}
							CharLiteralError::TooLong => {
								"character literal may only contain one \
								 codepoint"
							}
						};
						self.sema.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::InvalidCharacterLiteral
										.code(),
								)
								.with_message(message)
								.with_label(Label::primary(
									self.scope.file_id,
									span,
								)),
						);
						self.error_pattern(span)
					}
				}
			}
			ast::Literal::Float => {
				self.report_unmatchable_literal(
					span,
					"a float",
					"float equality is partial: `0.1 + 0.2` is not `0.3`, so \
					 a float has no single value to compare with",
				);
				self.error_pattern(span)
			}
			ast::Literal::String => {
				self.report_unmatchable_literal(
					span,
					"a string",
					"a string has no equality to compare with",
				);
				self.error_pattern(span)
			}
		}
	}

	/// An integer literal, against the type it is compared with. `negated` is
	/// the sign: a negative literal reaches one past the maximum, so `-128`
	/// is in range for an `i8` although `128` is not. The value is stored as
	/// its bits in that type.
	fn check_int(
		&mut self,
		magnitude: u64,
		negated: bool,
		span: TextSpan,
		expected: TypeIndex,
	) -> PatIdx {
		let Some(integer) = Integer::from_type(expected) else {
			self.report_pattern_mismatch(expected, "an integer", span);
			return self.error_pattern(span);
		};
		let value = if negated {
			-i128::from(magnitude)
		} else {
			i128::from(magnitude)
		};
		if !integer.contains(value) {
			let diagnostic = self.sema.report_out_of_range(
				self.builder.strings,
				format_args!("literal `{value}`"),
				expected,
				SourceSpan::new(self.scope.file_id, span),
			);
			self.sema.diagnostics.push(diagnostic);
			return self.error_pattern(span);
		}
		let bits = if negated {
			magnitude.wrapping_neg()
		} else {
			magnitude
		};
		self.body.push_pattern(
			PatternKind::Int(bits & integer.mask()),
			expected,
			span,
		)
	}

	/// A value path, which names a constant: a variant, a free constant, or
	/// an associated one. Locals are never looked at.
	fn check_value_path(
		&mut self,
		segments: &[ast::PathSegment],
		span: TextSpan,
		expected: TypeIndex,
	) -> PatIdx {
		let found = match self.resolve_value_path(segments, span) {
			Ok(ValuePath::Item(walk)) => {
				let Some(key) = walk.target.loc() else {
					self.note_local_not_constant(segments);
					return self.error_pattern(span);
				};
				let kind = key.symbol_kind(&self.sema.decls);
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
				match kind {
					DeclKind::Const(constant)
					| DeclKind::EnumVariant(constant) => {
						let signature =
							&self.sema.constants[usize::from(constant)];
						let ty = signature.ty;
						let env =
							self.sema.assumption_envs.of_frame(signature.env);
						let ty = self.context().normalized_in(ty, env);
						let kind = PatternKind::Constant {
							constant,
							type_args: GenericArgs::EMPTY,
						};
						Some((kind, ty))
					}
					_ => {
						self.sema.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::InvalidMatchPattern.code(),
								)
								.with_message(format!(
									"expected a constant, found {} `{}`",
									kind.noun(),
									self.builder
										.strings
										.resolve(
											segments
												.last()
												.unwrap()
												.ident
												.inner
										)
										.unwrap()
								))
								.with_label(Label::primary(
									self.scope.file_id,
									span,
								))
								.with_note("a pattern compares with constants"),
						);
						None
					}
				}
			}
			Ok(ValuePath::Member(path)) => match self.select_constant(path) {
				Some((
					ExprKind::Const {
						constant,
						type_args,
					},
					ty,
				)) => Some((
					PatternKind::Constant {
						constant,
						type_args,
					},
					ty,
				)),
				Some((
					ExprKind::AbstractConst {
						constant,
						type_args,
					},
					ty,
				)) => Some((
					PatternKind::AbstractConstant {
						constant,
						type_args,
					},
					ty,
				)),
				_ => None,
			},
			Err(_) => None,
		};
		let Some((kind, ty)) = found else {
			return self.error_pattern(span);
		};
		if expected == TypeIndex::ERROR {
			// The test is a mistake already reported; the pattern says
			// nothing more.
			return self.error_pattern(span);
		}
		if ty != TypeIndex::ERROR && ty != expected {
			let diagnostic = self.context().mismatch_at(expected, ty, span);
			self.sema.diagnostics.push(diagnostic);
			return self.error_pattern(span);
		}
		self.body.push_pattern(kind, expected, span)
	}

	/// After a value path of one name found nothing: when a local of that
	/// name is in scope, a note on the report says why it was not used.
	fn note_local_not_constant(&mut self, segments: &[ast::PathSegment]) {
		let [segment] = segments else { return };
		if self.lookup_local(segment.ident.inner).is_none() {
			return;
		}
		let name = self.builder.strings.resolve(segment.ident.inner).unwrap();
		let note = format!(
			"`{name}` is a local; a pattern compares with constants, and \
			 `{name}` would bind a new one"
		);
		let site = std::ops::Range::from(segment.ident.span);
		if let Some(report) = self.sema.diagnostics.last_mut()
			&& report.labels.iter().any(|label| {
				label.file_id == self.scope.file_id && label.range == site
			}) {
			report.notes.push(note);
		}
	}

	/// The children of a pattern that matched nothing it could take apart,
	/// checked against `ERROR` so their bindings are still declared.
	fn check_poisoned(
		&mut self,
		elements: ast::List<ast::PatternElement>,
		span: TextSpan,
		context: &mut PatternContext,
	) -> PatIdx {
		for item in self.ast().list(elements) {
			if let ast::PatternElement::Pattern(pattern) = *item {
				self.check_pattern(pattern, TypeIndex::ERROR, context);
			}
		}
		self.error_pattern(span)
	}

	fn error_pattern(&mut self, span: TextSpan) -> PatIdx {
		self.body
			.push_pattern(PatternKind::Error, TypeIndex::ERROR, span)
	}

	/// A float has no single value to compare with, and a string has no
	/// equality at all, so neither can be matched.
	fn report_unmatchable_literal(
		&mut self,
		span: TextSpan,
		kind: &str,
		note: &str,
	) {
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::UnmatchableLiteral.code())
				.with_message(format!("{kind} cannot be matched"))
				.with_label(Label::primary(self.scope.file_id, span))
				.with_note(note),
		);
	}

	fn report_pattern_mismatch(
		&mut self,
		expected: TypeIndex,
		found: &str,
		span: TextSpan,
	) {
		let expected = self
			.sema
			.type_formatter(self.builder.strings)
			.display_type(expected);
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypeMistmatch.code())
				.with_message("type mismatch")
				.with_label(
					Label::primary(self.scope.file_id, span).with_message(
						format!("expected `{expected}`, found {found}"),
					),
				),
		);
	}

	fn report_not_a_struct(&mut self, found: &str, span: TextSpan) {
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::InvalidMatchPattern.code())
				.with_message(format!("expected a struct, found {found}"))
				.with_label(Label::primary(self.scope.file_id, span)),
		);
	}

	fn report_duplicate_rest(&mut self, span: TextSpan, first: TextSpan) {
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::DuplicateRestPattern.code())
				.with_message("`..` can only be used once per pattern")
				.with_label(Label::primary(self.scope.file_id, span))
				.with_label(
					Label::secondary(self.scope.file_id, first)
						.with_message("previously used here"),
				),
		);
	}

	fn report_element_count(
		&mut self,
		count: usize,
		written: usize,
		rest: bool,
		span: TextSpan,
		struct_index: Option<StructIdx>,
	) {
		let plural = |n: usize| if n == 1 { "" } else { "s" };
		let (noun, owner) = match struct_index {
			Some(struct_index) => {
				let name = self.sema.decls.name(struct_index);
				let name = self.builder.strings.resolve(name.inner).unwrap();
				("field", format!("struct `{name}`"))
			}
			None => ("element", "the tuple".to_string()),
		};
		let at_least = if rest { "at least " } else { "" };
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::ArgumentCountMismatch.code())
				.with_message(format!(
					"this pattern has {at_least}{written} {noun}{} but \
					 {owner} has {count}",
					plural(written)
				))
				.with_label(
					Label::primary(self.scope.file_id, span).with_message(
						format!("expected {count} {noun}{}", plural(count)),
					),
				),
		);
	}
}

impl Integer {
	/// The bits a value of this type occupies, as a mask over a `u64`.
	pub(super) fn mask(self) -> u64 {
		if self.is_signed() {
			(self.max() << 1) | 1
		} else {
			self.max()
		}
	}
}
