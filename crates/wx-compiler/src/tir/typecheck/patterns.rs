//! Patterns: what a `local` or a match arm takes apart, binds and tests.
//!
//! A pattern is checked against the type it is given (a `local`'s value's, a
//! match's scrutinee's), from the outside in, into the body's pattern arena.
//! The mode it was written in is gone by then: the parser decided what every
//! name is, so a marker is looked through. Destructuring has one child per
//! element or field of its type, in declaration order, whatever was written:
//! what `..` covers, and a field a named pattern leaves out, is a `Wildcard`.
//!
//! A value path never sees locals: `case y` names a constant `y`, and a local
//! of that name only earns a note on the "cannot find" report.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::{BodyContext, Integer, ValuePath};
use crate::ast::{self, Keyword, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{ExprKind, PatIdx, PatKind};
use crate::tir::defs::{BindingTarget, DefKind, StructIdx};
use crate::tir::imports::report_private_identifier;
use crate::tir::literals::{CharLiteralError, parse_char_literal};
use crate::tir::types::{Type, TypeEnvOwner, TypeIndex, TypeList};

/// Where a pattern is written, and the names it has bound so far.
pub(super) struct PatternSite {
	refutable: bool,
	/// Every name the pattern binds, to report one bound twice.
	bindings: Vec<Spanned<SymbolU32>>,
}

impl PatternSite {
	/// A `local` statement's pattern, which always matches: it holds no
	/// tests.
	pub(super) fn local() -> Self {
		Self {
			refutable: false,
			bindings: Vec::new(),
		}
	}

	/// A match arm's pattern.
	pub(super) fn arm() -> Self {
		Self {
			refutable: true,
			bindings: Vec::new(),
		}
	}
}

/// The syntax of one mode, so destructuring, which reads the same in both, is
/// checked once.
trait PatternSyntax {
	fn check(
		cx: &mut BodyContext<'_, '_, '_, '_>,
		pattern: &Self,
		span: TextSpan,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx;

	/// `{ x }` in a named struct pattern: `{ x: x }` in this mode.
	fn check_shorthand(
		cx: &mut BodyContext<'_, '_, '_, '_>,
		name: Spanned<SymbolU32>,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx;
}

impl PatternSyntax for ast::BindPattern {
	fn check(
		cx: &mut BodyContext<'_, '_, '_, '_>,
		pattern: &Self,
		span: TextSpan,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		cx.check_bind_pattern(pattern, span, expected, site)
	}

	fn check_shorthand(
		cx: &mut BodyContext<'_, '_, '_, '_>,
		name: Spanned<SymbolU32>,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		cx.bind(name, None, expected, name.span, site)
	}
}

impl PatternSyntax for ast::ValuePattern {
	fn check(
		cx: &mut BodyContext<'_, '_, '_, '_>,
		pattern: &Self,
		span: TextSpan,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		cx.check_value_pattern(pattern, span, expected, site)
	}

	fn check_shorthand(
		cx: &mut BodyContext<'_, '_, '_, '_>,
		name: Spanned<SymbolU32>,
		expected: TypeIndex,
		_site: &mut PatternSite,
	) -> PatIdx {
		let path = [ast::PathSegment {
			ident: name,
			type_args: Box::new([]),
		}];
		cx.check_value_path(&path, name.span, expected)
	}
}

impl BodyContext<'_, '_, '_, '_> {
	/// Checks `pattern` against `expected`, declaring its bindings in the
	/// current scope.
	pub(super) fn check_pattern(
		&mut self,
		pattern: &Spanned<ast::BindPattern>,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		self.check_bind_pattern(&pattern.inner, pattern.span, expected, site)
	}

	fn check_bind_pattern(
		&mut self,
		pattern: &ast::BindPattern,
		span: TextSpan,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		match pattern {
			ast::BindPattern::Wildcard => {
				self.body.push_pattern(PatKind::Wildcard, expected, span)
			}
			ast::BindPattern::Binding { mut_span, name } => {
				self.bind(*name, *mut_span, expected, span, site)
			}
			ast::BindPattern::Destructure(destructure) => {
				self.check_destructure(destructure, span, expected, site)
			}
			ast::BindPattern::Marked(ast::Marked::Local {
				pattern, ..
			}) => self.check_bind_pattern(
				&pattern.inner,
				pattern.span,
				expected,
				site,
			),
			ast::BindPattern::Marked(ast::Marked::Case {
				case_span,
				pattern,
			}) => {
				if site.refutable {
					return self.check_value_pattern(
						&pattern.inner,
						pattern.span,
						expected,
						site,
					);
				}
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::RefutablePatternInLocal.code(),
						)
						.with_message("a `local` pattern cannot test a value")
						.with_label(
							Label::primary(self.scope.file_id, *case_span)
								.with_message("this tests a value"),
						)
						.with_note(
							"a `local` always matches; test values with \
							 `match`",
						),
				);
				// Its bindings are still declared, so their uses resolve.
				self.check_value_pattern(
					&pattern.inner,
					pattern.span,
					TypeIndex::ERROR,
					site,
				);
				self.body
					.push_pattern(PatKind::Error, TypeIndex::ERROR, span)
			}
		}
	}

	fn check_value_pattern(
		&mut self,
		pattern: &ast::ValuePattern,
		span: TextSpan,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		match pattern {
			ast::ValuePattern::Wildcard => {
				self.body.push_pattern(PatKind::Wildcard, expected, span)
			}
			ast::ValuePattern::Literal(literal) => {
				self.check_literal(literal, span, expected)
			}
			ast::ValuePattern::Path(path) => {
				self.check_value_path(path, span, expected)
			}
			ast::ValuePattern::Or(alternatives) => {
				let mut checked = Vec::with_capacity(alternatives.len());
				let mut binds = false;
				for alternative in alternatives {
					let alternative = &alternative.inner;
					let bound = site.bindings.len();
					checked.push(self.check_value_pattern(
						&alternative.inner,
						alternative.span,
						expected,
						site,
					));
					if let Some(name) = site.bindings.get(bound) {
						binds = true;
						self.cx.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::InvalidMatchPattern.code(),
								)
								.with_message(
									"an alternative of `|` cannot bind a name",
								)
								.with_label(Label::primary(
									self.scope.file_id,
									name.span,
								)),
						);
					}
				}
				if binds {
					return self.error_pattern(span);
				}
				let alternatives = self.body.push_patterns(checked);
				self.body.push_pattern(
					PatKind::Or(alternatives),
					expected,
					span,
				)
			}
			ast::ValuePattern::Destructure(destructure) => {
				self.check_destructure(destructure, span, expected, site)
			}
			ast::ValuePattern::Marked(ast::Marked::Case {
				pattern, ..
			}) => self.check_value_pattern(
				&pattern.inner,
				pattern.span,
				expected,
				site,
			),
			ast::ValuePattern::Marked(ast::Marked::Local {
				pattern, ..
			}) => self.check_bind_pattern(
				&pattern.inner,
				pattern.span,
				expected,
				site,
			),
		}
	}

	/// A binding: a local of the matched part's type.
	fn bind(
		&mut self,
		name: Spanned<SymbolU32>,
		mut_span: Option<TextSpan>,
		expected: TypeIndex,
		span: TextSpan,
		site: &mut PatternSite,
	) -> PatIdx {
		if let Some(first) =
			site.bindings.iter().find(|bound| bound.inner == name.inner)
		{
			let text = self.cx.strings.resolve(name.inner).unwrap();
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::DuplicatePatternBinding.code())
					.with_message(format!(
						"`{text}` is bound more than once in the same pattern"
					))
					.with_label(Label::primary(self.scope.file_id, name.span))
					.with_label(
						Label::secondary(self.scope.file_id, first.span)
							.with_message("first bound here"),
					),
			);
		}
		site.bindings.push(name);
		let local = self.declare_local(name, expected, mut_span);
		self.body.push_pattern(PatKind::Bind(local), expected, span)
	}

	/// A tuple or struct pattern, with one child per element or field.
	fn check_destructure<P: PatternSyntax>(
		&mut self,
		destructure: &ast::Destructure<P>,
		span: TextSpan,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		match destructure {
			ast::Destructure::Tuple { elements } => {
				let types = match *self.cx.types.resolve(expected) {
					Type::Tuple { elements } => {
						Some(self.cx.types.list(elements).to_vec())
					}
					_ => None,
				};
				let Some(types) = types else {
					if expected != TypeIndex::ERROR {
						self.report_pattern_mismatch(expected, "a tuple", span);
					}
					return self.check_poisoned(elements, span, site);
				};
				let Some(children) =
					self.check_elements(elements, &types, span, site, None)
				else {
					return self.error_pattern(span);
				};
				let children = self.body.push_patterns(children);
				self.body
					.push_pattern(PatKind::Tuple(children), expected, span)
			}
			ast::Destructure::Struct { path, elements } => {
				let Some((struct_index, ty, types)) =
					self.pattern_struct(path, span, expected)
				else {
					return self.check_poisoned(elements, span, site);
				};
				let Some(children) = self.check_elements(
					elements,
					&types,
					span,
					site,
					Some(struct_index),
				) else {
					return self.error_pattern(span);
				};
				let fields = self.body.push_patterns(children);
				self.body.push_pattern(
					PatKind::Struct {
						struct_index,
						fields,
					},
					ty,
					span,
				)
			}
			ast::Destructure::NamedStruct { path, fields } => {
				let Some((struct_index, ty, types)) =
					self.pattern_struct(path, span, expected)
				else {
					for item in fields {
						if let ast::PatternFieldItem::Field(field) =
							&item.inner.inner
						{
							self.check_field(field, TypeIndex::ERROR, site);
						}
					}
					return self.error_pattern(span);
				};
				let Some(children) =
					self.check_fields(fields, struct_index, &types, span, site)
				else {
					return self.error_pattern(span);
				};
				let fields = self.body.push_patterns(children);
				self.body.push_pattern(
					PatKind::Struct {
						struct_index,
						fields,
					},
					ty,
					span,
				)
			}
		}
	}

	/// The children of a positional list against `types`, a tuple's elements
	/// or a struct's fields: the written ones before the first `..` take the
	/// first types, those after it the last, and `..` covers what is between.
	/// `None` when the counts cannot fit (reported, every child still checked).
	fn check_elements<P: PatternSyntax>(
		&mut self,
		elements: &ast::PatternElements<P>,
		types: &[TypeIndex],
		span: TextSpan,
		site: &mut PatternSite,
		struct_index: Option<StructIdx>,
	) -> Option<Vec<PatIdx>> {
		let mut rest: Option<(usize, TextSpan)> = None;
		let mut written: Vec<(&P, TextSpan)> = Vec::new();
		for item in elements {
			match &item.inner.inner {
				ast::PatternElement::Pattern(pattern) => {
					written.push((pattern, item.inner.span));
				}
				ast::PatternElement::Rest => match rest {
					Some((_, first)) => {
						self.report_duplicate_rest(item.inner.span, first);
					}
					None => rest = Some((written.len(), item.inner.span)),
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
			for (pattern, span) in written {
				P::check(self, pattern, span, TypeIndex::ERROR, site);
			}
			return None;
		}
		let before = rest.map_or(written.len(), |(at, _)| at);
		let after = written.len() - before;
		let mut children = Vec::with_capacity(count);
		for (at, &(pattern, span)) in written[..before].iter().enumerate() {
			children.push(P::check(self, pattern, span, types[at], site));
		}
		if let Some((_, rest_span)) = rest {
			for &ty in &types[before..count - after] {
				children.push(self.body.push_pattern(
					PatKind::Wildcard,
					ty,
					rest_span,
				));
			}
		}
		for (at, &(pattern, span)) in written[before..].iter().enumerate() {
			let ty = types[count - after + at];
			children.push(P::check(self, pattern, span, ty, site));
		}
		Some(children)
	}

	/// The children of `Name({ x, y: pat, .. })`, one per field in
	/// declaration order. A field not named is covered by `..`; without one
	/// it is reported and matched as `_`.
	fn check_fields<P: PatternSyntax>(
		&mut self,
		fields: &ast::PatternFields<P>,
		struct_index: StructIdx,
		types: &[TypeIndex],
		span: TextSpan,
		site: &mut PatternSite,
	) -> Option<Vec<PatIdx>> {
		let def = &self.cx.defs.structs[usize::from(struct_index)];
		if !def.is_fully_named() {
			let name = self.cx.strings.resolve(def.name.inner).unwrap();
			self.cx.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TupleStructBracePattern.code())
					.with_message(format!(
						"struct `{name}` has unnamed fields, so it is matched \
						 with `{name}(...)`"
					))
					.with_label(Label::primary(self.scope.file_id, span)),
			);
			for item in fields {
				if let ast::PatternFieldItem::Field(field) = &item.inner.inner {
					self.check_field(field, TypeIndex::ERROR, site);
				}
			}
			return None;
		}
		let mut rest: Option<TextSpan> = None;
		let mut given: Vec<Option<(PatIdx, TextSpan)>> =
			vec![None; types.len()];
		for item in fields {
			let field = match &item.inner.inner {
				ast::PatternFieldItem::Rest => {
					match rest {
						Some(first) => {
							self.report_duplicate_rest(item.inner.span, first)
						}
						None => rest = Some(item.inner.span),
					}
					continue;
				}
				ast::PatternFieldItem::Field(field) => field,
			};
			let name = field.name;
			let def = &self.cx.defs.structs[usize::from(struct_index)];
			let Some(index) = def.lookup.get(&name.inner).copied() else {
				let struct_name =
					self.cx.strings.resolve(def.name.inner).unwrap();
				let field_name = self.cx.strings.resolve(name.inner).unwrap();
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
				self.check_field(field, TypeIndex::ERROR, site);
				continue;
			};
			let at = usize::from(index);
			if let Some((_, first)) = given[at] {
				let field_name = self.cx.strings.resolve(name.inner).unwrap();
				self.cx.diagnostics.push(
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
				self.check_field(field, TypeIndex::ERROR, site);
				continue;
			}
			let child = self.check_field(field, types[at], site);
			given[at] = Some((child, name.span));
		}
		if rest.is_none() {
			let def = &self.cx.defs.structs[usize::from(struct_index)];
			let missing: Vec<String> = given
				.iter()
				.enumerate()
				.filter(|(_, given)| given.is_none())
				.map(|(at, _)| {
					let name = def.fields[at].name.unwrap().inner;
					format!("`{}`", self.cx.strings.resolve(name).unwrap())
				})
				.collect();
			if !missing.is_empty() {
				let struct_name =
					self.cx.strings.resolve(def.name.inner).unwrap();
				self.cx.diagnostics.push(
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
					self.body.push_pattern(PatKind::Wildcard, ty, rest_span)
				}
			})
			.collect();
		Some(children)
	}

	/// `x` or `x: pat` in a named struct pattern, against the field's type.
	fn check_field<P: PatternSyntax>(
		&mut self,
		field: &ast::PatternField<P>,
		expected: TypeIndex,
		site: &mut PatternSite,
	) -> PatIdx {
		match &field.pattern {
			Some(pattern) => {
				P::check(self, &pattern.inner, pattern.span, expected, site)
			}
			None => P::check_shorthand(self, field.name, expected, site),
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
				self.cx.diagnostics.push(diagnostic);
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
			let key = walk.target.def_key()?;
			let kind = key.symbol_kind(self.cx.defs);
			let DefKind::Struct(struct_index) = kind else {
				self.report_not_a_struct(&format!("a {}", kind.noun()), span);
				return None;
			};
			if let BindingTarget::Inaccessible(key) = walk.target {
				let diagnostic = self.report_private_constructor(
					struct_index,
					Some(key),
					segment,
				);
				self.cx.diagnostics.push(diagnostic);
			}
			let params = self.cx.structs[usize::from(struct_index)].type_params;
			let written = self.written_type_args(
				segment,
				params,
				TypeEnvOwner::Struct(struct_index),
			);
			(struct_index, written)
		};
		let named = self.cx.types.intern_struct(struct_index, &written);
		let ty = if expected == TypeIndex::ERROR {
			TypeIndex::ERROR
		} else {
			match self.cx.types.meet(expected, named) {
				Some(ty) => ty,
				None => {
					let diagnostic = self.mismatch_at(expected, named, span);
					self.cx.diagnostics.push(diagnostic);
					return None;
				}
			}
		};
		let type_args: Vec<TypeIndex> = match *self.cx.types.resolve(ty) {
			Type::Struct { type_args, .. } => {
				self.cx.types.list(type_args).to_vec()
			}
			_ => vec![TypeIndex::ERROR; written.len()],
		};
		let count = self.cx.struct_field_types(struct_index).len();
		let types = (0..count)
			.map(|field| self.field_type(struct_index, &type_args, field))
			.collect();
		Some((struct_index, ty, types))
	}

	/// A literal, against the type it is compared with. An integer is stored
	/// as its bits in that type.
	fn check_literal(
		&mut self,
		literal: &ast::PatternLiteral,
		span: TextSpan,
		expected: TypeIndex,
	) -> PatIdx {
		if expected == TypeIndex::ERROR {
			return self.error_pattern(span);
		}
		let kind = match *literal {
			ast::PatternLiteral::Int { minus_span, value } => {
				let negated = minus_span.is_some();
				let Some(integer) = Integer::from_type(expected) else {
					self.report_pattern_mismatch(expected, "an integer", span);
					return self.error_pattern(span);
				};
				if !integer.in_range(value, negated) {
					let shown = if negated {
						format!("-{value}")
					} else {
						value.to_string()
					};
					let ty = self.cx.type_formatter().display_type(expected);
					self.cx.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::IntegerLiteralOutOfRange.code(),
							)
							.with_message(format!(
								"literal `{shown}` out of range for `{ty}`"
							))
							.with_label(Label::primary(
								self.scope.file_id,
								span,
							)),
					);
					return self.error_pattern(span);
				}
				let bits = if negated { value.wrapping_neg() } else { value };
				PatKind::Int(bits & integer.mask())
			}
			ast::PatternLiteral::Bool(value) => {
				if expected != TypeIndex::BOOL {
					self.report_pattern_mismatch(expected, "`bool`", span);
					return self.error_pattern(span);
				}
				PatKind::Bool(value)
			}
			ast::PatternLiteral::Char => {
				if expected != TypeIndex::CHAR {
					self.report_pattern_mismatch(expected, "`char`", span);
					return self.error_pattern(span);
				}
				let source =
					&self.cx.files.get(self.scope.file_id).unwrap().source;
				match parse_char_literal(span.extract_str(source)) {
					Ok(value) => PatKind::Char(value),
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
						self.cx.diagnostics.push(
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
						return self.error_pattern(span);
					}
				}
			}
		};
		self.body.push_pattern(kind, expected, span)
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
				let Some(key) = walk.target.def_key() else {
					self.note_local_not_constant(segments);
					return self.error_pattern(span);
				};
				let kind = key.symbol_kind(self.cx.defs);
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
				match kind {
					DefKind::Const(constant)
					| DefKind::EnumVariant(constant) => {
						let (ty, scope) = self.cx.constant_type(constant);
						let ty = self.normalized(ty, scope);
						let kind = PatKind::Constant {
							constant,
							type_args: TypeList::EMPTY,
						};
						Some((kind, ty))
					}
					_ => {
						self.cx.diagnostics.push(
							Diagnostic::error()
								.with_code(
									DiagnosticCode::InvalidMatchPattern.code(),
								)
								.with_message(format!(
									"expected a constant, found {} `{}`",
									kind.noun(),
									self.cx
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
					PatKind::Constant {
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
					PatKind::AbstractConstant {
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
		if expected != TypeIndex::ERROR
			&& ty != TypeIndex::ERROR
			&& ty != expected
		{
			let diagnostic = self.mismatch_at(expected, ty, span);
			self.cx.diagnostics.push(diagnostic);
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
		let name = self.cx.strings.resolve(segment.ident.inner).unwrap();
		let note = format!(
			"`{name}` is a local; a pattern compares with constants, and \
			 `local {name}` would bind a new one"
		);
		let site = std::ops::Range::from(segment.ident.span);
		if let Some(report) = self.cx.diagnostics.last_mut()
			&& report.labels.iter().any(|label| {
				label.file_id == self.scope.file_id && label.range == site
			}) {
			report.notes.push(note);
		}
	}

	/// The children of a pattern that matched nothing it could take apart,
	/// checked against `ERROR` so their bindings are still declared.
	fn check_poisoned<P: PatternSyntax>(
		&mut self,
		elements: &ast::PatternElements<P>,
		span: TextSpan,
		site: &mut PatternSite,
	) -> PatIdx {
		for item in elements {
			if let ast::PatternElement::Pattern(pattern) = &item.inner.inner {
				P::check(
					self,
					pattern,
					item.inner.span,
					TypeIndex::ERROR,
					site,
				);
			}
		}
		self.error_pattern(span)
	}

	fn error_pattern(&mut self, span: TextSpan) -> PatIdx {
		self.body
			.push_pattern(PatKind::Error, TypeIndex::ERROR, span)
	}

	fn report_pattern_mismatch(
		&mut self,
		expected: TypeIndex,
		found: &str,
		span: TextSpan,
	) {
		let expected = self.cx.type_formatter().display_type(expected);
		self.cx.diagnostics.push(
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
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::InvalidMatchPattern.code())
				.with_message(format!("expected a struct, found {found}"))
				.with_label(Label::primary(self.scope.file_id, span)),
		);
	}

	fn report_duplicate_rest(&mut self, span: TextSpan, first: TextSpan) {
		self.cx.diagnostics.push(
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
				let name = self.cx.defs.structs[usize::from(struct_index)].name;
				let name = self.cx.strings.resolve(name.inner).unwrap();
				("field", format!("struct `{name}`"))
			}
			None => ("element", "the tuple".to_string()),
		};
		let at_least = if rest { "at least " } else { "" };
		self.cx.diagnostics.push(
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
