//! The parser: tokens to the AST, by recursive descent with a Pratt loop
//! for expressions. Every parse function that fails has reported why.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::SymbolU32;

use super::lexer::{Lexer, Token};
use super::*;
use crate::{
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	vfs::{self, FileId},
};

fn report_mixed_call_arguments(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MixedCallArguments.code())
		.with_message(
			"named arguments cannot be combined with positional arguments",
		)
		.with_label(Label::primary(file_id, span))
		.with_note(
			"pass every argument by position, `f(a, b)`, or every one by name, `f({ x: a, y: b })`",
		)
}

fn report_unexpected_token(
	file_id: FileId,
	received: Spanned<Token>,
	expected: Token,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnexpectedToken.code())
		.with_message(format!(
			"expected `{}`, found `{}`",
			expected, received.inner
		))
		.with_label(
			Label::primary(file_id, received.span)
				.with_message(format!("expected `{}`", expected)),
		)
}

/// A `.` with no member after it. A keyword is named by its text, since it
/// is lexed as an identifier: `x.` on a line of its own is followed by the
/// next statement's `local`.
fn report_missing_member(
	file_id: FileId,
	received: Spanned<Token>,
	source: &str,
) -> Diagnostic<FileId> {
	let found = match received.inner {
		Token::Identifier => received.span.extract_str(source).to_string(),
		token => token.to_string(),
	};
	Diagnostic::error()
		.with_code(DiagnosticCode::UnexpectedToken.code())
		.with_message(format!(
			"expected a member name after `.`, found `{found}`"
		))
		.with_label(
			Label::primary(file_id, received.span)
				.with_message("expected a field or method name"),
		)
}

/// `report_unexpected_token` only ever names one expected token; right
/// after a path's `::`, the actual expected set is "another path segment,
/// or a pointer/slice/array sigil starting a memory tag" — reusing the same
/// code (this is still the same class of diagnostic, just with more than
/// one token that would have been accepted) rather than naming just `*`
/// and leaving out `&` and plain continuation.
fn report_expected_path_segment_or_memory_tag(
	file_id: FileId,
	received: Spanned<Token>,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnexpectedToken.code())
		.with_message(format!(
			"expected a path segment or a pointer type after `::`, found `{}`",
			received.inner
		))
		.with_label(
			Label::primary(file_id, received.span)
				.with_message("expected an identifier, `*`, or `&` here"),
		)
}

fn report_missing_separator(
	file_id: FileId,
	span: TextSpan,
	separator: Token,
) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::MissingSeparator.code())
		.with_message("missing separator")
		.with_label(
			Label::primary(file_id, span)
				.with_message(format!("consider adding `{}` here", separator)),
		)
}

pub struct UnclosedDelimiterDiagnostic {
	pub file_id: FileId,
	pub open_span: TextSpan,
	pub close_token: Token,
	pub expected_close_span: TextSpan,
}

fn report_unclosed_delimiter(
	details: UnclosedDelimiterDiagnostic,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnclosedDelimiter.code())
		.with_message("unclosed delimiter")
		.with_label(
			Label::primary(details.file_id, details.expected_close_span)
				.with_message(format!(
					"consider adding `{}` here",
					details.close_token
				)),
		)
		.with_label(
			Label::secondary(details.file_id, details.open_span)
				.with_message("unclosed delimiter"),
		)
}

fn report_invalid_integer_literal(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidNumericLiteral.code())
		.with_message("invalid integer literal")
		.with_label(Label::primary(file_id, span))
}

fn report_invalid_float_literal(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidNumericLiteral.code())
		.with_message("invalid float literal")
		.with_label(Label::primary(file_id, span))
}

fn report_incomplete_binary_expression(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::IncompleteExpression.code())
		.with_message("incomplete binary expression")
		.with_label(Label::primary(file_id, span))
		.with_label(
			Label::secondary(file_id, span)
				.with_message("consider adding a right-hand side operand"),
		)
}

fn report_incomplete_unary_expression(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::IncompleteExpression.code())
		.with_message("incomplete unary expression")
		.with_label(Label::primary(file_id, span))
		.with_label(
			Label::secondary(file_id, span)
				.with_message("consider adding an operand"),
		)
}

/// A block-like expression (`if`, `match`, `loop`, `block`) met as an
/// operand: `operator` is the token that would take it, or `None` when it
/// is itself the operand an operator before it parsed.
fn report_block_like_operand(
	file_id: FileId,
	expression: &Spanned<Expression>,
	operator: Option<TextSpan>,
) -> Diagnostic<FileId> {
	let keyword = match expression.inner {
		Expression::IfElse { .. } => "if",
		Expression::Match { .. } => "match",
		Expression::Loop { .. } => "loop",
		_ => "block",
	};
	let diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::BlockLikeOperand.code())
		.with_message(format!("`{keyword}` cannot be an operand"));
	let diagnostic = match operator {
		Some(operator) => diagnostic
			.with_label(Label::primary(file_id, operator).with_message(
				format!("this operator would take the `{keyword}`"),
			))
			.with_label(
				Label::secondary(file_id, expression.span)
					.with_message(format!("the `{keyword}` ends here")),
			),
		None => diagnostic.with_label(
			Label::primary(file_id, expression.span)
				.with_message(format!("this `{keyword}` is an operand")),
		),
	};
	diagnostic
		.with_note(format!(
			"a block-like expression ends at its closing `}}`; wrap it in parentheses: `({keyword} ..)`"
		))
}

fn report_chained_comparisons(
	file_id: FileId,
	first_operator_span: TextSpan,
	second_operator_span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
        .with_code(DiagnosticCode::ChainedComparison.code())
        .with_message("comparison operators cannot be chained")
        .with_label(Label::primary(file_id, first_operator_span))
        .with_label(Label::primary(file_id, second_operator_span))
        .with_note("consider using logical operator like `&&` or `||` to split the comparisons or use parentheses to group them")
}

fn report_chained_assignments(
	file_id: FileId,
	first_operator_span: TextSpan,
	second_operator_span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ChainedAssignment.code())
		.with_message("assignments cannot be chained")
		.with_label(Label::primary(file_id, first_operator_span))
		.with_label(Label::primary(file_id, second_operator_span))
		.with_note(
			"an assignment's value is `()`; write each assignment as its own statement",
		)
}

/// A `const` before a path that is a constant already: it changes nothing,
/// and the path is what the pattern means.
fn report_redundant_const(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::RedundantConstMarker.code())
		.with_message("redundant `const`")
		.with_label(
			Label::primary(file_id, span)
				.with_message("this path is a constant already"),
		)
		.with_note("drop the `const`")
}

/// `const` where nothing else could be written: before a literal or `_`
/// argument, or an array's length.
fn report_redundant_const_marker(
	file_id: FileId,
	span: TextSpan,
	why: &str,
) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::RedundantConstMarker.code())
		.with_message("redundant `const`")
		.with_label(Label::primary(file_id, span).with_message(why))
		.with_note("drop the `const`")
}

/// `local` in a pattern: a name binds by default, so the marker says
/// nothing.
fn report_redundant_local(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidBindingPattern.code())
		.with_message("`local` is not needed in a pattern")
		.with_label(Label::primary(file_id, span))
		.with_note("a name binds by default")
}

fn report_mut_without_name(
	file_id: FileId,
	mut_span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidMutBinding.code())
		.with_message("`mut` needs a name")
		.with_label(
			Label::primary(file_id, mut_span)
				.with_message("nothing without a name can be mutated"),
		)
		.with_note("write `mut name: Type`, or leave out `mut`")
}

fn report_binding_without_type(
	file_id: FileId,
	name_span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingTypeAnnotation.code())
		.with_message("expected a type annotation")
		.with_label(
			Label::primary(file_id, name_span)
				.with_message("expected `: Type` after this name"),
		)
		.with_note("write `name: Type`")
}

fn report_reserved_identifier(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::ReservedIdentifier.code())
		.with_message("cannot use keyword as identifier")
		.with_label(Label::primary(file_id, span))
}

fn report_invalid_namespace(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidNamespace.code())
		.with_message("invalid namespace")
		.with_label(
			Label::primary(file_id, span)
				.with_message("namespace must be a valid identifier"),
		)
}

fn report_type_args_not_allowed(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeArgumentsNotAllowed.code())
		.with_message("type arguments are not allowed here")
		.with_label(
			Label::primary(file_id, span).with_message(
				"only a path or a method name takes type arguments",
			),
		)
}

fn report_unknown_token(file_id: FileId, span: TextSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnknownToken.code())
		.with_message("unknown token")
		.with_label(
			Label::primary(file_id, span)
				.with_message("not valid in wx source"),
		)
}

fn report_invalid_item(file_id: FileId, span: TextSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidItem.code())
		.with_message("invalid item")
		.with_label(Label::primary(file_id, span))
}

fn report_expected_expression(
	file_id: FileId,
	token: Spanned<Token>,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UnexpectedToken.code())
		.with_message(format!(
			"expected an expression, found `{}`",
			token.inner
		))
		.with_label(
			Label::primary(file_id, token.span)
				.with_message("expected an expression"),
		)
}

fn report_missing_local_initializer(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingInitializer.code())
		.with_message("missing initial value for local variable")
		.with_note("example syntax: local x: i32 = 0")
		.with_label(Label::primary(file_id, span))
}

fn report_missing_global_initializer(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::MissingInitializer.code())
		.with_message("missing initial value for global variable")
		.with_note("example syntax: global x: i32 = 0")
		.with_label(Label::primary(file_id, span))
}

fn report_invalid_attribute(
	file_id: FileId,
	span: TextSpan,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::InvalidAttribute.code())
		.with_message("invalid attribute")
		.with_label(
			Label::primary(file_id, span)
				.with_message("expected attribute name here"),
		)
}

impl TryFrom<Token> for BinaryOp {
	type Error = ();

	fn try_from(token: Token) -> Result<Self, Self::Error> {
		match token {
			// Arithmetic
			Token::Plus => Ok(BinaryOp::Add),
			Token::Minus => Ok(BinaryOp::Sub),
			Token::Star => Ok(BinaryOp::Mul),
			Token::Slash => Ok(BinaryOp::Div),
			Token::Percent => Ok(BinaryOp::Rem),
			// Relational
			Token::EqEq => Ok(BinaryOp::Eq),
			Token::BangEq => Ok(BinaryOp::NotEq),
			Token::LeftArrow => Ok(BinaryOp::Less),
			Token::LeftArrowEq => Ok(BinaryOp::LessEq),
			Token::RightArrow => Ok(BinaryOp::Greater),
			Token::RightArrowEq => Ok(BinaryOp::GreaterEq),
			// Logical
			Token::DoubleAmper => Ok(BinaryOp::And),
			Token::DoubleVbar => Ok(BinaryOp::Or),
			// Assignment
			Token::Eq => Ok(BinaryOp::Assign),
			Token::PlusEq => Ok(BinaryOp::AddAssign),
			Token::MinusEq => Ok(BinaryOp::SubAssign),
			Token::StarEq => Ok(BinaryOp::MulAssign),
			Token::SlashEq => Ok(BinaryOp::DivAssign),
			Token::PercentEq => Ok(BinaryOp::RemAssign),
			Token::AmperEq => Ok(BinaryOp::BitAndAssign),
			Token::VbarEq => Ok(BinaryOp::BitOrAssign),
			Token::CaretEq => Ok(BinaryOp::BitXorAssign),
			Token::DoubleLeftArrowEq => Ok(BinaryOp::LeftShiftAssign),
			Token::DoubleRightArrowEq => Ok(BinaryOp::RightShiftAssign),
			// Bitwise
			Token::Amper => Ok(BinaryOp::BitAnd),
			Token::Vbar => Ok(BinaryOp::BitOr),
			Token::Caret => Ok(BinaryOp::BitXor),
			Token::DoubleLeftArrow => Ok(BinaryOp::LeftShift),
			Token::DoubleRightArrow => Ok(BinaryOp::RightShift),
			_ => Err(()),
		}
	}
}

impl TryFrom<Token> for UnaryOp {
	type Error = ();

	fn try_from(kind: Token) -> Result<Self, Self::Error> {
		match kind {
			Token::Minus => Ok(UnaryOp::InvertSign),
			Token::Bang => Ok(UnaryOp::Not),
			Token::Caret => Ok(UnaryOp::BitNot),
			_ => Err(()),
		}
	}
}

/// A parsed `<Type as Trait>::` or `<Type>::`, before what follows it.
enum BracketedRoot {
	Qualified(QualifiedPathRoot),
	Grouped(Box<Spanned<TypeExpression>>),
}

/// A trait or typeset bound expression.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub(super) enum BindingPower {
	Default,
	Assignment,
	LogicalOr,
	LogicalAnd,
	BitwiseOr,
	BitwiseXor,
	BitwiseAnd,
	Comparison,
	BitwiseShift,
	Additive,
	Multiplicative,
	Unary,
	Postfix,
	Member,
	Primary,
}

impl From<BinaryOp> for BindingPower {
	fn from(operator: BinaryOp) -> Self {
		match operator {
			BinaryOp::Assign => BindingPower::Assignment,
			BinaryOp::AddAssign => BindingPower::Assignment,
			BinaryOp::SubAssign => BindingPower::Assignment,
			BinaryOp::MulAssign => BindingPower::Assignment,
			BinaryOp::DivAssign => BindingPower::Assignment,
			BinaryOp::RemAssign => BindingPower::Assignment,
			BinaryOp::BitAndAssign => BindingPower::Assignment,
			BinaryOp::BitOrAssign => BindingPower::Assignment,
			BinaryOp::BitXorAssign => BindingPower::Assignment,
			BinaryOp::LeftShiftAssign => BindingPower::Assignment,
			BinaryOp::RightShiftAssign => BindingPower::Assignment,

			BinaryOp::Or => BindingPower::LogicalOr,
			BinaryOp::And => BindingPower::LogicalAnd,

			BinaryOp::BitOr => BindingPower::BitwiseOr,
			BinaryOp::BitXor => BindingPower::BitwiseXor,
			BinaryOp::BitAnd => BindingPower::BitwiseAnd,

			BinaryOp::Eq => BindingPower::Comparison,
			BinaryOp::NotEq => BindingPower::Comparison,
			BinaryOp::Less => BindingPower::Comparison,
			BinaryOp::LessEq => BindingPower::Comparison,
			BinaryOp::Greater => BindingPower::Comparison,
			BinaryOp::GreaterEq => BindingPower::Comparison,

			BinaryOp::LeftShift => BindingPower::BitwiseShift,
			BinaryOp::RightShift => BindingPower::BitwiseShift,

			BinaryOp::Add => BindingPower::Additive,
			BinaryOp::Sub => BindingPower::Additive,

			BinaryOp::Mul => BindingPower::Multiplicative,
			BinaryOp::Div => BindingPower::Multiplicative,
			BinaryOp::Rem => BindingPower::Multiplicative,
		}
	}
}

/// What a path turned out to be: a path, or the old `Path::{ .. }` form,
/// which is reported and read as an error.
enum PathTerm {
	Path(Box<[PathSegment]>),
	Old(Spanned<Pattern>),
}

pub struct Parser<'input> {
	source: &'input str,
	lexer: Lexer<'input>,
	strings: &'input mut StringInterner,
	ast: AST,
}

struct SeparatedGroup<T> {
	item_handler: fn(parser: &mut Parser) -> Result<Spanned<T>, ()>,
	open_token: Token,
	close_token: Token,
	separator_token: Token,
	/// Optional callback to determine if a missing separator should emit a
	/// diagnostic. If None, always emits a diagnostic. If Some, calls the
	/// function with the item.
	should_warn_missing_separator: Option<fn(&T) -> bool>,
}

impl<T> SeparatedGroup<T> {
	fn parse(
		self,
		parser: &mut Parser,
	) -> Result<Spanned<Box<[Separated<Spanned<T>>]>>, ()> {
		let open_span = parser.next_expect(self.open_token)?.span;
		self.parse_after_open(parser, open_span)
	}

	/// `parse`, for a caller that consumed the opening token itself to look
	/// past it.
	fn parse_after_open(
		self,
		parser: &mut Parser,
		open_span: TextSpan,
	) -> Result<Spanned<Box<[Separated<Spanned<T>>]>>, ()> {
		let mut items: Vec<Separated<Spanned<T>>> = Vec::new();

		let close_span = loop {
			let token = parser.lexer.peek();
			if token.inner == self.close_token {
				break parser.lexer.next().span;
			}

			if token.inner == Token::Eof {
				let expected_close_span = match items.last() {
					Some(last) => {
						TextSpan::new(last.inner.span.end, last.inner.span.end)
					}
					None => TextSpan::new(open_span.end, open_span.end),
				};
				parser.ast.diagnostics.push(report_unclosed_delimiter(
					UnclosedDelimiterDiagnostic {
						file_id: parser.ast.file_id,
						close_token: self.close_token,
						open_span,
						expected_close_span,
					},
				));
				break expected_close_span;
			}

			let item = match self.parse_with_recovery(parser) {
				Some(item) => item,
				None => continue,
			};

			let next_token = parser.lexer.peek();
			if next_token.inner == self.separator_token {
				let separator_span = parser.lexer.next().span;
				items.push(Separated {
					inner: item,
					separator: Some(separator_span),
				});
				continue;
			}
			if next_token.inner == self.close_token {
				items.push(Separated {
					inner: item,
					separator: None,
				});
				break parser.lexer.next().span;
			}

			if next_token.inner == Token::Eof {
				let eof_span = TextSpan::new(item.span.end, item.span.end);
				parser.ast.diagnostics.push(report_unclosed_delimiter(
					UnclosedDelimiterDiagnostic {
						file_id: parser.ast.file_id,
						close_token: self.close_token,
						open_span,
						expected_close_span: eof_span,
					},
				));
				items.push(Separated {
					inner: item,
					separator: None,
				});
				break eof_span;
			}

			let should_warn = self
				.should_warn_missing_separator
				.map(|f| f(&item.inner))
				.unwrap_or(true);

			if should_warn {
				parser.ast.diagnostics.push(report_missing_separator(
					parser.ast.file_id,
					TextSpan::new(item.span.end, item.span.end),
					self.separator_token,
				));
			}
			items.push(Separated {
				inner: item,
				separator: None,
			});
		};

		Ok(Spanned {
			inner: items.into_boxed_slice(),
			span: TextSpan::new(open_span.start, close_span.end),
		})
	}

	fn parse_with_recovery(&self, parser: &mut Parser) -> Option<Spanned<T>> {
		match (self.item_handler)(parser) {
			Ok(item) => Some(item),
			Err(_) => loop {
				let token = parser.lexer.peek();
				match token.inner {
					t if t == self.separator_token => {
						parser.lexer.next();
						return None;
					}
					t if t == self.close_token || t == Token::Eof => {
						return None;
					}
					_ => {
						parser.lexer.next();
					}
				}
			},
		}
	}
}

impl<'ctx> Parser<'ctx> {
	pub fn parse(
		file_id: FileId,
		files: &'ctx vfs::Files,
		strings: &'ctx mut StringInterner,
	) -> AST {
		let source = &files.get(file_id).unwrap().source;
		let mut parser = Self {
			source,
			lexer: Lexer::new(source),
			strings,
			ast: AST {
				file_id,
				diagnostics: Vec::new(),
				items: Vec::new(),
				comments: CommentMap::empty(),
			},
		};

		loop {
			let item_attrs = match Parser::parse_attributes(&mut parser) {
				Ok(attrs) => attrs,
				Err(_) => continue,
			};

			let start_token = parser.lexer.peek();
			if start_token.inner == Token::Eof {
				break;
			}
			if start_token.inner == Token::SemiColon {
				// TODO: report unnecessary semicolon
				parser.lexer.next();
				continue;
			}

			let item_handler = match parser.get_item_handler(start_token) {
				Ok(handler) => handler,
				Err(_) => match parser.recover_from_invalid_item(start_token) {
					Some(handler) => handler,
					None => break,
				},
			};

			match item_handler(&mut parser) {
				Ok(mut item) => {
					item.inner.set_attributes(item_attrs);
					let separator_span = if !item.inner.is_block_like() {
						let token = parser.lexer.peek();
						match token.inner {
							Token::SemiColon => Some(parser.lexer.next().span),
							_ => {
								// TODO: report missing semicolon
								None
							}
						}
					} else {
						None
					};

					parser.ast.items.push(Separated {
						inner: item,
						separator: separator_span,
					});
				}
				Err(_) => continue,
			}
		}

		if parser.lexer.has_crlf {
			parser.ast.diagnostics.push(Diagnostic::warning()
				.with_code(DiagnosticCode::CrlfLineEndings.code())
				.with_message("file contains carriage returns (`\\r\\n`)")
				.with_label(
					Label::primary(file_id, TextSpan::new(0, 0)).with_message(
						"carriage returns can shift text spans; consider using LF (`\\n`) line endings instead",
				))
			);
		}

		let Parser { mut ast, lexer, .. } = parser;
		// Appended, in whatever position they land: nothing downstream reads
		// diagnostics positionally, each one carries its own span, and the
		// CRLF warning above is already out of source order. `extend` over an
		// exact-size iterator reserves once and moves each `Diagnostic` — not
		// a cheap thing to shuffle, holding an owned message and two `Vec`s —
		// exactly once.
		ast.diagnostics.extend(
			lexer
				.unknown_spans
				.iter()
				.map(|span| report_unknown_token(file_id, *span)),
		);
		ast.comments = CommentMap(lexer.comments.into_boxed_slice());
		ast
	}

	fn recover_from_invalid_item(
		&mut self,
		start_token: Spanned<Token>,
	) -> Option<fn(parser: &mut Parser) -> Result<Spanned<Item>, ()>> {
		let mut end_token = None;
		let handler = loop {
			let token = self.lexer.peek();
			if token.inner == Token::Eof {
				break None;
			}

			match self.get_item_handler(token) {
				Ok(handler) => break Some(handler),
				Err(_) => {
					end_token = Some(self.lexer.next());
				}
			}
		};

		self.ast.diagnostics.push(report_invalid_item(
			self.ast.file_id,
			match end_token {
				Some(end_token) => {
					TextSpan::new(start_token.span.start, end_token.span.end)
				}
				None => start_token.span,
			},
		));

		handler
	}

	fn get_item_handler(
		&mut self,
		token: Spanned<Token>,
	) -> Result<fn(parser: &mut Parser) -> Result<Spanned<Item>, ()>, ()> {
		let keyword = match token.inner {
			Token::Identifier => {
				Keyword::try_from(token.span.extract_str(self.source)).ok()
			}
			_ => None,
		};

		match keyword {
			Some(Keyword::Func) => Ok(Parser::parse_function_definition_item),
			Some(Keyword::Global) => Ok(Parser::parse_global_definition_item),
			Some(Keyword::Export) => Ok(Parser::parse_export_item),
			Some(Keyword::Import) => Ok(Parser::parse_import_block),
			Some(Keyword::Enum) => Ok(Parser::parse_enum_item),
			Some(Keyword::Impl) => Ok(Parser::parse_impl_item),
			Some(Keyword::Struct) => Ok(Parser::parse_struct_item),
			Some(Keyword::Memory) => Ok(Parser::parse_memory_item),
			Some(Keyword::Const) => Ok(Parser::parse_const_item),
			Some(Keyword::Mod) => Ok(Parser::parse_module_item),
			Some(Keyword::Use) => Ok(Parser::parse_use_item),
			Some(Keyword::Package) => Ok(Parser::parse_crate_item),
			Some(Keyword::Pub) => Ok(Parser::parse_pub_item),
			Some(Keyword::Trait) => Ok(Parser::parse_trait_item),
			Some(Keyword::Typeset) => Ok(Parser::parse_typeset_item),
			Some(Keyword::Type) => Ok(Parser::parse_type_alias_item),
			_ => Err(()),
		}
	}

	#[inline]
	fn next_expect(
		&mut self,
		expected_token: Token,
	) -> Result<Spanned<Token>, ()> {
		let token = self.lexer.next();
		if token.inner == expected_token {
			Ok(token)
		} else {
			self.ast.diagnostics.push(report_unexpected_token(
				self.ast.file_id,
				token,
				expected_token,
			));
			Err(())
		}
	}

	#[inline]
	fn peek_keyword(&mut self) -> Option<Keyword> {
		let token = self.lexer.peek();
		match token.inner {
			Token::Identifier => {
				Keyword::try_from(token.span.extract_str(self.source)).ok()
			}
			_ => None,
		}
	}

	/// Whether the identifier token at `span` spells a keyword.
	fn is_keyword(&self, span: TextSpan) -> bool {
		Keyword::try_from(span.extract_str(self.source)).is_ok()
	}

	/// Whether the identifier token at `span` may follow a `::`: any name,
	/// and `super` (`super::super::x`). Another keyword is the next
	/// statement's, after a path the user has not finished (`a::` on a line
	/// of its own, then `local ..`).
	fn is_later_segment(&self, span: TextSpan) -> bool {
		matches!(
			Keyword::try_from(span.extract_str(self.source)),
			Err(_) | Ok(Keyword::Super)
		)
	}

	fn intern_identifier(&mut self, span: TextSpan) -> SymbolU32 {
		if self.is_keyword(span) {
			self.ast
				.diagnostics
				.push(report_reserved_identifier(self.ast.file_id, span));
		}
		self.strings.get_or_intern(span.extract_str(self.source))
	}

	fn parse_attributes(parser: &mut Parser) -> Result<Box<[Attribute]>, ()> {
		let mut attrs = Vec::new();
		loop {
			if parser.lexer.peek().inner != Token::Hash {
				break;
			}
			parser.lexer.next();
			let open_bracket = parser.next_expect(Token::OpenBracket)?;
			let name_token = parser.lexer.peek();
			if name_token.inner != Token::Identifier {
				parser.ast.diagnostics.push(report_invalid_attribute(
					parser.ast.file_id,
					name_token.span,
				));
				return Err(());
			}
			let name_span = parser.lexer.next().span;
			let name_symbol = parser
				.strings
				.get_or_intern(name_span.extract_str(parser.source));

			let value = if parser.lexer.peek().inner == Token::OpenParen {
				AttributeValue::Named(Parser::parse_attribute_arguments(
					parser,
				)?)
			} else {
				AttributeValue::Word
			};

			let close_token = parser.lexer.peek();
			if close_token.inner != Token::CloseBracket {
				parser.ast.diagnostics.push(report_unclosed_delimiter(
					UnclosedDelimiterDiagnostic {
						file_id: parser.ast.file_id,
						open_span: open_bracket.span,
						close_token: Token::CloseBracket,
						expected_close_span: close_token.span,
					},
				));
				return Err(());
			}
			parser.lexer.next();
			attrs.push(Attribute {
				name: Spanned {
					inner: name_symbol,
					span: name_span,
				},
				value,
			});
		}
		Ok(attrs.into_boxed_slice())
	}

	/// `({ name: value, .. })`, as a call by name writes its arguments. The
	/// old `(name = value, ..)` is reported and read as the named list it
	/// stands for.
	fn parse_attribute_arguments(
		parser: &mut Parser,
	) -> Result<Box<[Separated<Spanned<NamedArgument>>]>, ()> {
		let open = parser.next_expect(Token::OpenParen)?.span;
		match parser.lexer.peek().inner {
			Token::OpenBrace => {
				Ok(Parser::parse_named_call_arguments(parser)?.0.inner)
			}
			Token::CloseParen => {
				parser.lexer.next();
				Ok(Box::default())
			}
			_ => {
				let mut arguments = Vec::new();
				loop {
					let name_span = parser.next_expect(Token::Identifier)?.span;
					let name = Spanned {
						inner: parser.intern_identifier(name_span),
						span: name_span,
					};
					parser.next_expect(Token::Eq)?;
					let value =
						parser.parse_expression(BindingPower::Default)?;
					let span = TextSpan::new(name_span.start, value.span.end);
					let separator = parser
						.lexer
						.next_if(Token::Comma)
						.map(|comma| comma.span);
					arguments.push(Separated {
						inner: Spanned {
							inner: NamedArgument {
								name,
								value: Some(Box::new(value)),
							},
							span,
						},
						separator,
					});
					if separator.is_none()
						|| parser.lexer.peek().inner == Token::CloseParen
					{
						break;
					}
				}
				let close = parser.next_expect(Token::CloseParen)?.span;
				parser.ast.diagnostics.push(
					Diagnostic::error()
						.with_code(
							DiagnosticCode::AttributeArgumentsAreNamed.code(),
						)
						.with_message(
							"an attribute's arguments are named as a call's",
						)
						.with_label(Label::primary(
							parser.ast.file_id,
							TextSpan::new(open.start, close.end),
						))
						.with_note("write `#[name({ argument: value, .. })]`"),
				);
				Ok(arguments.into_boxed_slice())
			}
		}
	}

	fn parse_function_param_item(
		parser: &mut Parser,
	) -> Result<Spanned<FunctionParam>, ()> {
		let start = parser.lexer.peek().span.start;
		let (binding, ty) = Parser::parse_binding_and_type(parser)?;
		Ok(Spanned {
			span: TextSpan::new(start, ty.span.end),
			inner: FunctionParam {
				binding,
				ty: Box::new(ty),
			},
		})
	}

	/// What a parameter or a struct field is written as: `binding: Type`, or
	/// `Type` alone, which binds nothing. A binding is `_`, `name` or
	/// `mut name`, and is always followed by `:`, so anything else is a type
	/// (`x` alone is the type `x`). `self` is a name like any other, and is
	/// written with its type; where it may stand is checked by the item it
	/// is in.
	fn parse_binding_and_type(
		parser: &mut Parser,
	) -> Result<(Option<Binding>, Spanned<TypeExpression>), ()> {
		let mut_span = matches!(parser.peek_keyword(), Some(Keyword::Mut))
			.then(|| parser.lexer.next().span);

		let token = parser.lexer.peek();
		let keyword = Keyword::try_from(token.span.extract_str(parser.source));
		let named = token.inner == Token::Identifier
			&& matches!(
				keyword,
				Err(_) | Ok(Keyword::Underscore | Keyword::SelfLower)
			);
		if !named {
			if let Some(mut_span) = mut_span {
				parser.ast.diagnostics.push(report_mut_without_name(
					parser.ast.file_id,
					mut_span,
				));
			}
			return Ok((None, parser.parse_type_expression()?));
		}

		let name_span = parser.lexer.next().span;
		let underscore = matches!(keyword, Ok(Keyword::Underscore));
		// `self` is never a type, so it is always a name.
		let receiver = matches!(keyword, Ok(Keyword::SelfLower));
		let name = Spanned {
			inner: parser
				.strings
				.get_or_intern(name_span.extract_str(parser.source)),
			span: name_span,
		};
		if let Some(colon) = parser.lexer.next_if(Token::Colon) {
			let binding = if underscore {
				if let Some(mut_span) = mut_span {
					parser.ast.diagnostics.push(report_mut_without_name(
						parser.ast.file_id,
						mut_span,
					));
				}
				Binding::Wildcard(name_span)
			} else {
				Binding::Name { mut_span, name }
			};
			let ty = match parser.parse_type_expression() {
				Ok(ty) => ty,
				// A type not written yet, where the entry ends (`y: )`,
				// `y: ,`), has been reported; it is kept as an error node
				// spanning the gap up to that token, so the binding is still
				// declared. Anything else there is a type written wrong, which
				// the list's recovery skips.
				Err(()) => {
					let token = parser.lexer.peek();
					if !matches!(token.inner, Token::Comma | Token::CloseParen)
					{
						return Err(());
					}
					Spanned {
						inner: TypeExpression::Error,
						span: TextSpan::new(colon.span.end, token.span.start),
					}
				}
			};
			return Ok((Some(binding), ty));
		}
		// Not followed by `:`: a type, unless it can only be a name, which is
		// then given an error type.
		let missing = Spanned {
			inner: TypeExpression::Error,
			span: TextSpan::new(name_span.end, name_span.end),
		};
		match mut_span {
			// `mut _`: the type `_`, without the `mut`.
			Some(mut_span) if underscore => {
				parser.ast.diagnostics.push(report_mut_without_name(
					parser.ast.file_id,
					mut_span,
				));
				Ok((
					None,
					Spanned {
						inner: TypeExpression::Infer,
						span: name_span,
					},
				))
			}
			// `mut heap::*u8`: `mut` before a type that goes on past its
			// first name.
			Some(mut_span)
				if !receiver
					&& !matches!(
						parser.lexer.peek().inner,
						Token::Comma | Token::CloseParen
					) =>
			{
				parser.ast.diagnostics.push(report_mut_without_name(
					parser.ast.file_id,
					mut_span,
				));
				Ok((None, parser.parse_type_path_from(name)?))
			}
			// `_` is the type `_`.
			None if underscore => Ok((
				None,
				Spanned {
					inner: TypeExpression::Infer,
					span: name_span,
				},
			)),
			None if !receiver => Ok((None, parser.parse_type_path_from(name)?)),
			// `mut x`, `self` or `mut self`: a name, but no type.
			_ => {
				parser.ast.diagnostics.push(report_binding_without_type(
					parser.ast.file_id,
					name_span,
				));
				Ok((Some(Binding::Name { mut_span, name }), missing))
			}
		}
	}

	fn parse_function_signature(
		&mut self,
	) -> Result<Spanned<FunctionSignature>, ()> {
		let fn_span = self.lexer.next();
		let name_token = self.lexer.peek();
		let name_span = match name_token.inner {
			Token::Identifier => self.lexer.next().span,
			_ => {
				return {
					self.ast.diagnostics.push(report_unexpected_token(
						self.ast.file_id,
						name_token,
						Token::Identifier,
					));
					Err(())
				};
			}
		};
		let name_symbol = self
			.strings
			.get_or_intern(name_span.extract_str(self.source));
		let name = Spanned {
			inner: name_symbol,
			span: name_span,
		};

		let type_params = if self.lexer.peek().inner == Token::LeftArrow {
			self.parse_type_params()?
		} else {
			Box::new([])
		};

		let params = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			item_handler: Parser::parse_function_param_item,
			should_warn_missing_separator: None,
		}
		.parse(self)?;

		let result = self.parse_function_result()?;

		let span = TextSpan::new(
			fn_span.span.start,
			match &result {
				Some(result) => result.span.end,
				None => params.span.end,
			},
		);

		Ok(Spanned {
			inner: FunctionSignature {
				name,
				type_params,
				params: params.inner,
				result,
			},
			span,
		})
	}

	/// Whether the next token starts a literal: a number, a char, a string,
	/// or `-` before a number.
	fn at_literal(&mut self) -> bool {
		matches!(
			self.lexer.peek().inner,
			Token::Int
				| Token::Char
				| Token::Float
				| Token::String
				| Token::Minus
		)
	}

	/// A literal, as a pattern compares with it or a constant argument gives
	/// it; the caller has checked `at_literal`.
	fn parse_literal(&mut self) -> Result<Spanned<Literal>, ()> {
		let token = self.lexer.next();
		let literal = match token.inner {
			Token::Int => Literal::Int(self.integer_literal(token.span)),
			Token::Char => Literal::Char,
			// A float has no single value to compare with and a string has
			// no equality at all, so a pattern can match neither — but that
			// is the checker's judgement, not the parser's: the literal is
			// read, and the rest of the file still parses.
			Token::Float => Literal::Float,
			Token::String => Literal::String,
			Token::Minus => {
				let number = self.lexer.next();
				let literal = match number.inner {
					Token::Int => {
						Literal::NegInt(self.integer_literal(number.span))
					}
					Token::Float => Literal::Float,
					// `-` must be followed by the number it negates.
					_ => {
						self.ast.diagnostics.push(report_unexpected_token(
							self.ast.file_id,
							number,
							Token::Int,
						));
						return Err(());
					}
				};
				return Ok(Spanned {
					inner: literal,
					span: TextSpan::new(token.span.start, number.span.end),
				});
			}
			_ => unreachable!("the caller checked `at_literal`"),
		};
		Ok(Spanned {
			inner: literal,
			span: token.span,
		})
	}

	/// Parse `<T, U: Bound1 + Bound2, const N: u32>` — generic parameter
	/// declarations.
	fn parse_type_params(&mut self) -> Result<Box<[Spanned<TypeParam>]>, ()> {
		let open_span = self.next_expect(Token::LeftArrow)?.span;
		let mut params: Vec<Spanned<TypeParam>> = Vec::new();

		loop {
			let peeked = self.lexer.peek();
			if peeked.inner == Token::RightArrow {
				self.lexer.next();
				break;
			}
			if peeked.inner == Token::Eof {
				self.ast.diagnostics.push(report_unclosed_delimiter(
					UnclosedDelimiterDiagnostic {
						file_id: self.ast.file_id,
						open_span,
						close_token: Token::RightArrow,
						expected_close_span: peeked.span,
					},
				));
				break;
			}

			let start = self.lexer.peek().span.start;
			let const_span = match self.peek_keyword() {
				Some(Keyword::Const) => Some(self.lexer.next().span),
				_ => None,
			};
			// `Self` is a name here, as `self` is among a function's
			// parameters; where it may stand is the signature's to check.
			let self_type =
				matches!(self.peek_keyword(), Some(Keyword::SelfPascal));
			let name_span = self.next_expect(Token::Identifier)?.span;
			let name_symbol = if self_type {
				self.strings
					.get_or_intern(name_span.extract_str(self.source))
			} else {
				self.intern_identifier(name_span)
			};
			let name = Spanned {
				inner: name_symbol,
				span: name_span,
			};

			let (param, end) = match const_span {
				// A constant's type is always written: nothing else says
				// what its values are.
				Some(const_span) => {
					self.next_expect(Token::Colon)?;
					let ty = self.parse_type_expression()?;
					let end = ty.span.end;
					(
						TypeParam::Const {
							const_span,
							name,
							ty: Box::new(ty),
						},
						end,
					)
				}
				None => {
					let bounds = match self.lexer.next_if(Token::Colon) {
						Some(colon) => {
							Some(self.parse_bounds_expression(colon.span.end)?)
						}
						None => None,
					};
					let end = bounds
						.as_ref()
						.map_or(name.span.end, |bounds| bounds.span.end);
					(TypeParam::Type { name, bounds }, end)
				}
			};
			params.push(Spanned {
				inner: param,
				span: TextSpan::new(start, end),
			});

			if self.lexer.peek().inner == Token::Comma {
				self.lexer.next();
			}
		}

		Ok(params.into_boxed_slice())
	}

	/// Consumes a single closing `>` for an angle-bracket construct opened at
	/// `open_span`, splitting a `>>` token when the construct closes at the
	/// same position as an outer one (e.g. nested generics). Reports an
	/// unclosed-delimiter diagnostic and returns the current token's span
	/// without consuming it if EOF is hit first.
	fn expect_close_angle(&mut self, open_span: TextSpan) -> TextSpan {
		let peeked = self.lexer.peek();
		if peeked.inner == Token::RightArrow {
			return self.lexer.next().span;
		}
		if peeked.inner == Token::DoubleRightArrow {
			return self.lexer.split_double_right_arrow();
		}
		self.ast.diagnostics.push(report_unclosed_delimiter(
			UnclosedDelimiterDiagnostic {
				file_id: self.ast.file_id,
				open_span,
				close_token: Token::RightArrow,
				expected_close_span: peeked.span,
			},
		));
		peeked.span
	}

	/// Parse `<Type1, 5, const SIZE>` arguments, after a type's name or a
	/// turbofish's `::`. Returns the args and the closing `>` span.
	fn parse_type_args(
		&mut self,
	) -> Result<(Box<[TypeArgument]>, TextSpan), ()> {
		let open_span = self.next_expect(Token::LeftArrow)?.span;
		let mut args: Vec<TypeArgument> = Vec::new();

		let close_span = loop {
			let peeked = self.lexer.peek();
			if peeked.inner == Token::RightArrow {
				break self.lexer.next().span;
			}
			// `>>` appears when a nested generic arg list closes at the same
			// position as an outer one (e.g. `Memory where { Size = Size }>`).
			if peeked.inner == Token::DoubleRightArrow {
				break self.lexer.split_double_right_arrow();
			}
			if peeked.inner == Token::Eof {
				self.ast.diagnostics.push(report_unclosed_delimiter(
					UnclosedDelimiterDiagnostic {
						file_id: self.ast.file_id,
						open_span,
						close_token: Token::RightArrow,
						expected_close_span: peeked.span,
					},
				));
				break peeked.span;
			}

			args.push(self.parse_type_argument()?);

			if self.lexer.peek().inner == Token::Comma {
				self.lexer.next();
			}
		};

		Ok((args.into_boxed_slice(), close_span))
	}

	/// One type argument: a literal is a constant; `const` marks a path as
	/// one; anything else is a type. `const` before a literal or `_` says
	/// nothing (`_` is inferred as whatever its parameter is), so it is
	/// reported as redundant and dropped.
	fn parse_type_argument(&mut self) -> Result<TypeArgument, ()> {
		let const_span = match self.peek_keyword() {
			Some(Keyword::Const) => Some(self.lexer.next().span),
			_ => None,
		};
		let at_underscore =
			matches!(self.peek_keyword(), Some(Keyword::Underscore));
		if let Some(span) = const_span
			&& (self.at_literal() || at_underscore)
		{
			self.ast.diagnostics.push(report_redundant_const_marker(
				self.ast.file_id,
				span,
				"this argument is a constant already",
			));
		}
		if self.at_literal() || (const_span.is_some() && !at_underscore) {
			return Ok(TypeArgument::Const(self.parse_const_argument()?));
		}
		Ok(TypeArgument::Type(self.parse_type_expression()?))
	}

	/// A constant: a literal, `_`, or a path naming one, written with a
	/// bracketed root (`<T as Array>::LEN`, `<[u8; 4]>::LEN`) or
	/// without.
	fn parse_const_argument(&mut self) -> Result<Spanned<ConstArgument>, ()> {
		if let Some(Keyword::Underscore) = self.peek_keyword() {
			return Ok(Spanned {
				inner: ConstArgument::Infer,
				span: self.lexer.next().span,
			});
		}
		if let Token::LeftArrow | Token::DoubleLeftArrow =
			self.lexer.peek().inner
		{
			let open_span = match self.lexer.peek().inner {
				Token::LeftArrow => self.lexer.next().span,
				_ => self.lexer.split_double_left_arrow(),
			};
			let root = self.parse_bracketed_root(open_span)?;
			let segments = self.parse_value_path()?;
			let span = TextSpan::new(open_span.start, segments.span().end);
			let segments = segments.segments;
			return Ok(Spanned {
				inner: match root {
					BracketedRoot::Qualified(root) => {
						ConstArgument::QualifiedPath { root, segments }
					}
					BracketedRoot::Grouped(inner) => {
						ConstArgument::Grouped { inner, segments }
					}
				},
				span,
			});
		}
		if self.at_literal() {
			let literal = self.parse_literal()?;
			return Ok(Spanned {
				inner: ConstArgument::Literal(literal.inner),
				span: literal.span,
			});
		}
		let path = match Parser::parse_path(self)? {
			PathTerm::Path(path) => path,
			PathTerm::Old(_) => return Err(()),
		};
		let span = TextSpan::new(
			path[0].ident.span.start,
			path.last().unwrap().ident.span.end,
		);
		Ok(Spanned {
			inner: ConstArgument::Path(path),
			span,
		})
	}

	/// An array's length, in a type or a repeat: only a constant can be
	/// written there, so `const` says nothing.
	fn parse_length(&mut self) -> Result<Spanned<ConstArgument>, ()> {
		if let Some(Keyword::Const) = self.peek_keyword() {
			let span = self.lexer.next().span;
			self.ast.diagnostics.push(report_redundant_const_marker(
				self.ast.file_id,
				span,
				"a length is a constant already",
			));
		}
		self.parse_const_argument()
	}

	/// Parse `where { Name = Type, Name: Bound, const N: Type, const N = 4 }`,
	/// the bindings block
	/// following a type. Returns a `Spanned` whose span covers from `{`
	/// through `}`. The `where` keyword must already be confirmed as the next
	/// token by the caller.
	fn parse_where_bindings(
		&mut self,
	) -> Result<Spanned<Box<[Spanned<AssocBinding>]>>, ()> {
		self.lexer.next(); // consume `where`
		let open_span = self.next_expect(Token::OpenBrace)?.span;
		let mut bindings: Vec<Spanned<AssocBinding>> = Vec::new();

		let close_span = loop {
			let peeked = self.lexer.peek();
			if peeked.inner == Token::CloseBrace {
				break self.lexer.next().span;
			}
			if peeked.inner == Token::Eof {
				self.ast.diagnostics.push(report_unclosed_delimiter(
					UnclosedDelimiterDiagnostic {
						file_id: self.ast.file_id,
						open_span,
						close_token: Token::CloseBrace,
						expected_close_span: peeked.span,
					},
				));
				break peeked.span;
			}

			let const_span = match self.peek_keyword() {
				Some(Keyword::Const) => Some(self.lexer.next().span),
				_ => None,
			};
			let name_span = self.next_expect(Token::Identifier)?.span;
			let name = Spanned {
				inner: self.intern_identifier(name_span),
				span: name_span,
			};
			let colon = self.lexer.next_if(Token::Colon);
			if colon.is_none() {
				self.next_expect(Token::Eq)?;
			}
			let (kind, end) = match (const_span, colon) {
				(None, Some(colon)) => {
					let bound = self.parse_bounds_expression(colon.span.end)?;
					let end = bound.span.end;
					(AssocBindingKind::Bound(bound), end)
				}
				(None, None) => {
					let ty = self.parse_type_expression()?;
					let end = ty.span.end;
					(AssocBindingKind::Equals(ty), end)
				}
				(Some(const_span), Some(_)) => {
					let ty = self.parse_type_expression()?;
					let end = ty.span.end;
					(
						AssocBindingKind::ConstRepresentable { const_span, ty },
						end,
					)
				}
				(Some(const_span), None) => {
					let value = self.parse_const_argument()?;
					let end = value.span.end;
					(AssocBindingKind::ConstEquals { const_span, value }, end)
				}
			};
			self.lexer.next_if(Token::Comma);
			bindings.push(Spanned {
				inner: AssocBinding { name, kind },
				span: TextSpan::new(
					const_span.map_or(name.span.start, |span| span.start),
					end,
				),
			});
		};

		Ok(Spanned {
			inner: bindings.into_boxed_slice(),
			span: TextSpan::new(open_span.start, close_span.end),
		})
	}

	/// Keep a result annotation whose type is not written yet, spanning the
	/// gap after `->`. Leave the body or declaration delimiter for the caller.
	fn parse_function_result(
		&mut self,
	) -> Result<Option<Box<Spanned<TypeExpression>>>, ()> {
		let Some(arrow) = self.lexer.next_if(Token::MinusRightArrow) else {
			return Ok(None);
		};
		let token = self.lexer.peek();
		let ty = if matches!(
			token.inner,
			Token::OpenBrace
				| Token::SemiColon
				| Token::CloseBrace
				| Token::Eof
		) {
			self.ast.diagnostics.push(report_unexpected_token(
				self.ast.file_id,
				token,
				Token::Identifier,
			));
			Spanned {
				inner: TypeExpression::Error,
				span: TextSpan::new(arrow.span.end, token.span.start),
			}
		} else {
			self.parse_type_expression()?
		};
		Ok(Some(Box::new(ty)))
	}

	fn parse_function_definition_item(
		parser: &mut Parser,
	) -> Result<Spanned<Item>, ()> {
		let signature = Parser::parse_function_signature(parser)?;
		let block = if parser.lexer.peek().inner == Token::OpenBrace {
			Some(Box::new(Parser::parse_block_expression(parser)?))
		} else {
			None
		};
		let span = TextSpan::new(
			signature.span.start,
			match &block {
				Some(block) => block.span.end,
				None => signature.span.end,
			},
		);
		Ok(Spanned {
			inner: match block {
				Some(block) => Item::Function {
					pub_span: None,
					attributes: Box::new([]),
					signature: signature.inner,
					block,
				},
				None => Item::FunctionDeclaration {
					pub_span: None,
					attributes: Box::new([]),
					signature: signature.inner,
				},
			},
			span,
		})
	}

	/// Parse a path in expression/value position: a call-site path
	/// (`math::add`), a constructor path, a qualified-path-expression
	/// segment list. Generic arguments are only ever spelled as turbofish
	/// (`::<T>`) — a bare `<` here would be ambiguous with the `<`/`>`
	/// comparison operators, so it's left untouched for the expression
	/// parser to consume. See `parse_type_path` for the type-directed twin,
	/// which is the reverse: bare `<...>` only, no turbofish, since type
	/// position has no such ambiguity to avoid.
	fn parse_value_path(&mut self) -> Result<Path, ()> {
		let first_ident = self.parse_path_ident()?;
		let mut segments: Vec<PathSegment> = vec![PathSegment {
			ident: first_ident,
			type_args: Box::new([]),
		}];

		while self.lexer.peek().inner == Token::ColonColon {
			self.lexer.next(); // consume `::`
			match self.lexer.peek().inner {
				Token::LeftArrow => {
					let (type_args, _) = self.parse_type_args()?;
					segments.last_mut().unwrap().type_args = type_args;
				}
				Token::Identifier => {
					let ident = self.parse_path_ident()?;
					segments.push(PathSegment {
						ident,
						type_args: Box::new([]),
					});
				}
				_ => {
					// `::` consumed but no valid continuation — stop and let the caller handle it
					break;
				}
			}
		}

		Ok(Path {
			segments: segments.into_boxed_slice(),
		})
	}

	/// Parse a path in a type-directed position: an ordinary type
	/// expression's name, a bound, a trait name, an impl target, or a
	/// typeset member. Every segment — including the first — may carry
	/// bare `<...>` generic arguments; turbofish is never accepted here
	/// (see `parse_value_path` for why the two positions differ). `::`
	/// continues to another segment regardless of whether the one just
	/// parsed carried args — `Vec<T>::Item` is a plain path here, same as
	/// `Vec::Item`.
	fn parse_type_path(&mut self) -> Result<Path, ()> {
		let mut ident = self.parse_path_ident()?;
		let mut segments: Vec<PathSegment> = Vec::new();
		loop {
			let mut type_args: Box<[TypeArgument]> = Box::new([]);
			if self.lexer.peek().inner == Token::LeftArrow {
				let (args, _) = self.parse_type_args()?;
				type_args = args;
			}
			segments.push(PathSegment { ident, type_args });
			if self.lexer.peek().inner != Token::ColonColon {
				break;
			}
			self.lexer.next(); // consume `::`
			ident = self.parse_path_ident()?;
		}

		Ok(Path {
			segments: segments.into_boxed_slice(),
		})
	}

	/// Parse a single bound: a path optionally followed by `where { ... }` bindings.
	fn parse_bound(&mut self) -> Result<Spanned<BoundExpression>, ()> {
		let path = self.parse_type_path()?;
		let path_span = path.span();

		let peeked = self.lexer.peek();
		if peeked.inner == Token::Identifier
			&& matches!(
				Keyword::try_from(peeked.span.extract_str(self.source)),
				Ok(Keyword::Where)
			) {
			let bindings = self.parse_where_bindings()?;
			let span = TextSpan::new(path_span.start, bindings.span.end);
			return Ok(Spanned {
				inner: BoundExpression::WithBindings {
					path: Box::new(BoundExpression::Path(path.segments)),
					bindings: bindings.inner,
				},
				span,
			});
		}

		Ok(Spanned {
			inner: BoundExpression::Path(path.segments),
			span: path_span,
		})
	}

	/// Parse one or more `+`-separated bounds: `Bound1 + Bound2 + ...`,
	/// optionally led by a `+` (`+ Bound1 + Bound2`), so a long list can put
	/// each bound on its own line, `+` first. The leading `+` is layout, not
	/// meaning, and is not recorded: the formatter writes it when it breaks
	/// the list. Returns a single `BoundExpression` when only one bound is
	/// present, or `BoundExpression::BoundList` for two or more.
	/// `after` is where the `:` before the bounds ends. A bound not written
	/// yet, where what holds it ends (`trait X: {`, `<T: >`, `{ Size: }`),
	/// is reported and kept as an error node spanning the gap from there up
	/// to that token, as a missing type is, so what holds it is kept too.
	/// Anything else there is a bound written wrong, which the caller's
	/// recovery skips.
	fn parse_bounds_expression(
		&mut self,
		after: u32,
	) -> Result<Spanned<BoundExpression>, ()> {
		let _ = self.lexer.next_if(Token::Plus);
		let token = self.lexer.peek();
		if matches!(
			token.inner,
			Token::OpenBrace
				| Token::CloseBrace
				| Token::RightArrow
				| Token::Comma
				| Token::SemiColon
				| Token::Eq
		) {
			self.ast.diagnostics.push(report_unexpected_token(
				self.ast.file_id,
				token,
				Token::Identifier,
			));
			return Ok(Spanned {
				inner: BoundExpression::Error,
				span: TextSpan::new(after, token.span.start),
			});
		}
		let first = self.parse_bound()?;
		if self.lexer.peek().inner != Token::Plus {
			return Ok(first);
		}
		let mut bounds: Vec<Spanned<BoundExpression>> = vec![first];
		while self.lexer.next_if(Token::Plus).is_some() {
			bounds.push(self.parse_bound()?);
		}
		let span = TextSpan::new(
			bounds.first().unwrap().span.start,
			bounds.last().unwrap().span.end,
		);
		Ok(Spanned {
			inner: BoundExpression::BoundList(bounds.into_boxed_slice()),
			span,
		})
	}

	fn parse_type_expression(&mut self) -> Result<Spanned<TypeExpression>, ()> {
		let token = self.lexer.peek();
		match token.inner {
			Token::Star | Token::Amper => {
				self.parse_pointer_type_expression(None)
			}
			Token::Bang => {
				let span = self.lexer.next().span;
				Ok(Spanned {
					inner: TypeExpression::Never,
					span,
				})
			}
			Token::Identifier => {
				let (first_tok, first_sym) = match Keyword::try_from(
					token.span.extract_str(self.source),
				) {
					Ok(Keyword::Underscore) => {
						let span = self.lexer.next().span;
						return Ok(Spanned {
							inner: TypeExpression::Infer,
							span,
						});
					}
					Ok(Keyword::Func) => {
						return Parser::parse_function_type_expression(self);
					}
					// `Self` is valid in type paths for `Self::AssocType`, etc.;
					// `crate`/`super` are path roots the resolver
					// pre-populates every namespace with (see
					// `intern_path_segment`) — none of the three are ever
					// reserved here, so they intern like ordinary text.
					Ok(Keyword::SelfPascal)
					| Ok(Keyword::Package)
					| Ok(Keyword::Super) => {
						let tok = self.lexer.next();
						let sym = self
							.strings
							.get_or_intern(tok.span.extract_str(self.source));
						(tok, sym)
					}
					_ => {
						let tok = self.lexer.next();
						let sym = self.intern_identifier(tok.span);
						(tok, sym)
					}
				};
				self.parse_type_path_from(Spanned {
					inner: first_sym,
					span: first_tok.span,
				})
			}
			Token::OpenParen => self.parse_tuple_or_paren_type_expression(),
			Token::OpenBracket => self.parse_slice_type_expression(),
			Token::LeftArrow => {
				let open_span = self.lexer.next().span; // consume `<`
				self.parse_qualified_path_type_expression(open_span)
			}
			// `<<A as B>::C as D>::E`: the lexer sees one `<<`, but here it is
			// two openings, so split it and parse the outer one first.
			Token::DoubleLeftArrow => {
				let open_span = self.lexer.split_double_left_arrow();
				self.parse_qualified_path_type_expression(open_span)
			}
			// No type starts here: reported, and the token is left for
			// whatever it closes or starts.
			_ => {
				self.ast.diagnostics.push(report_unexpected_token(
					self.ast.file_id,
					token,
					Token::Identifier,
				));
				Err(())
			}
		}
	}

	/// The rest of a type that starts with a path, its first identifier already
	/// consumed: a plain path, or a memory-tagged pointer type (`heap::*T`).
	/// Every segment, including the first, may carry bare `<...>` generic
	/// arguments (`Type<T>`, `module::Wrapper<T>`); `::` continues to another
	/// segment regardless of whether the one just parsed had arguments
	/// (`Vec<T>::Item` is a plain path, no bracket needed).
	fn parse_type_path_from(
		&mut self,
		first: Spanned<SymbolU32>,
	) -> Result<Spanned<TypeExpression>, ()> {
		let mut ident = first;
		let mut segments: Vec<PathSegment> = Vec::new();
		let path_end = loop {
			let mut type_args: Box<[TypeArgument]> = Box::new([]);
			let mut end = ident.span.end;
			if self.lexer.peek().inner == Token::LeftArrow {
				let (args, close_span) = self.parse_type_args()?;
				type_args = args;
				end = close_span.end;
			}
			segments.push(PathSegment { ident, type_args });
			if self.lexer.peek().inner != Token::ColonColon {
				break end;
			}
			let colons = self.lexer.next(); // consume `::`
			let next = self.lexer.peek();
			match next.inner {
				Token::Identifier if self.is_later_segment(next.span) => {
					ident = self.parse_path_ident()?;
				}
				Token::Star | Token::Amper => {
					// `::` consumed, followed by a pointer/slice/array sigil —
					// a memory-tagged type (`heap::*u8`), tagged with the path
					// built up so far.
					return self.parse_pointer_type_expression(Some(
						segments.into_boxed_slice(),
					));
				}
				// A missing segment: reported, and kept, as in an
				// expression's path. The token after `::` is left for
				// whatever it closes or starts.
				_ => {
					let token = self.lexer.peek();
					self.ast.diagnostics.push(
						report_expected_path_segment_or_memory_tag(
							self.ast.file_id,
							token,
						),
					);
					segments.push(PathSegment::missing(colons.span.end));
					break colons.span.end;
				}
			}
		};

		Ok(Spanned {
			inner: TypeExpression::Path(segments.into_boxed_slice()),
			span: TextSpan::new(first.span.start, path_end),
		})
	}

	/// Parse `<Type as Trait>::Item` (a trait-qualified path) or `<Type>::Item`
	/// (a bare bracketed self-type, no trait) — the opening `<` (whose span is
	/// `open_span`) has already been consumed.
	fn parse_qualified_path_type_expression(
		&mut self,
		open_span: TextSpan,
	) -> Result<Spanned<TypeExpression>, ()> {
		let root = self.parse_bracketed_root(open_span)?;
		let segments = self.parse_type_path()?;
		let span = TextSpan::new(open_span.start, segments.span().end);
		let segments = segments.segments;
		Ok(Spanned {
			inner: match root {
				BracketedRoot::Qualified(root) => {
					TypeExpression::QualifiedPath { root, segments }
				}
				BracketedRoot::Grouped(inner) => {
					TypeExpression::Grouped { inner, segments }
				}
			},
			span,
		})
	}

	/// `<Type as Trait>::` or `<Type>::`, after its opening `<`
	/// (`open_span`), up to and including the `::`. Which one it is hinges
	/// entirely on whether `as` follows the type.
	fn parse_bracketed_root(
		&mut self,
		open_span: TextSpan,
	) -> Result<BracketedRoot, ()> {
		let self_type = Box::new(self.parse_type_expression()?);
		let root = if matches!(self.peek_keyword(), Some(Keyword::As)) {
			self.lexer.next(); // consume `as`
			let trait_path = self.parse_type_path()?;
			let close_span = self.expect_close_angle(open_span);
			BracketedRoot::Qualified(QualifiedPathRoot {
				self_type,
				trait_path: trait_path.segments,
				span: TextSpan::new(open_span.start, close_span.end),
			})
		} else {
			self.expect_close_angle(open_span);
			BracketedRoot::Grouped(self_type)
		};
		self.next_expect(Token::ColonColon)?;
		Ok(root)
	}

	/// Parses a leading `*`/`&` sigil (not yet consumed — the caller only
	/// peeks to route here) and the type it points at, a slice included
	/// (`*[T]`, `&[T; N]`). `memory` is the path already parsed before an
	/// explicit `heap::` tag, if any — its first segment's start becomes the
	/// whole expression's span start instead of the sigil's own, since the
	/// tag is written before it.
	fn parse_pointer_type_expression(
		&mut self,
		memory: Option<Box<[PathSegment]>>,
	) -> Result<Spanned<TypeExpression>, ()> {
		let sigil = self.lexer.next();
		let ownership = if sigil.inner == Token::Star {
			Ownership::Exclusive
		} else {
			Ownership::Shared
		};
		let start = memory
			.as_ref()
			.and_then(|segments| segments.first())
			.map_or(sigil.span.start, |segment| segment.ident.span.start);

		let inner = self.parse_type_expression()?;
		let span = TextSpan::new(start, inner.span.end);
		Ok(Spanned {
			inner: TypeExpression::Pointer {
				ownership,
				memory,
				inner: Box::new(inner),
			},
			span,
		})
	}

	/// Parses a slice or an array, `[T]` or `[T; N]`, from its `[` (not yet
	/// consumed).
	fn parse_slice_type_expression(
		&mut self,
	) -> Result<Spanned<TypeExpression>, ()> {
		let open = self.lexer.next().span; // consume `[`
		let inner = Box::new(self.parse_type_expression()?);
		let next = self.lexer.next();
		match next.inner {
			Token::CloseBracket => Ok(Spanned {
				inner: TypeExpression::Slice { inner },
				span: TextSpan::new(open.start, next.span.end),
			}),
			Token::SemiColon => {
				let length = self.parse_length()?;
				let close_span = self.next_expect(Token::CloseBracket)?.span;
				Ok(Spanned {
					inner: TypeExpression::Array { inner, length },
					span: TextSpan::new(open.start, close_span.end),
				})
			}
			_ => {
				self.ast.diagnostics.push(report_unexpected_token(
					self.ast.file_id,
					next,
					Token::CloseBracket,
				));
				Err(())
			}
		}
	}

	fn parse_tuple_or_paren_type_expression(
		&mut self,
	) -> Result<Spanned<TypeExpression>, ()> {
		let grouped = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			item_handler: |parser| parser.parse_type_expression(),
			should_warn_missing_separator: None,
		}
		.parse(self)?;

		Ok(Spanned {
			inner: TypeExpression::Tuple {
				elements: grouped.inner,
			},
			span: grouped.span,
		})
	}

	fn parse_function_type_param(
		parser: &mut Parser,
	) -> Result<Spanned<FunctionTypeParam>, ()> {
		let ty = parser.parse_type_expression()?;
		// A single-segment path followed by `:` is a named parameter (`self: T`).
		let single_ident = match &ty.inner {
			TypeExpression::Path(segs)
				if segs.len() == 1 && segs[0].type_args.is_empty() =>
			{
				Some(segs[0].ident)
			}
			_ => None,
		};
		let (name, ty) = if let Some(name_ident) = single_ident {
			if parser.lexer.next_if(Token::Colon).is_some() {
				let new_ty = parser.parse_type_expression()?;
				(Some(name_ident), Box::new(new_ty))
			} else {
				(None, Box::new(ty))
			}
		} else {
			(None, Box::new(ty))
		};

		let span = TextSpan::new(
			name.map(|n| n.span).unwrap_or(ty.span).start,
			ty.span.end,
		);
		Ok(Spanned {
			inner: FunctionTypeParam { name, ty },
			span,
		})
	}

	fn parse_function_type_expression(
		&mut self,
	) -> Result<Spanned<TypeExpression>, ()> {
		let func_keyword = self.lexer.next();
		let params = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			item_handler: Parser::parse_function_type_param,
			should_warn_missing_separator: None,
		}
		.parse(self)?;

		if self.lexer.next_if(Token::MinusRightArrow).is_some() {
			let result = Box::new(Parser::parse_type_expression(self)?);
			let span = TextSpan::new(func_keyword.span.start, result.span.end);
			Ok(Spanned {
				inner: TypeExpression::Function {
					params: params.inner,
					result: Some(result),
				},
				span,
			})
		} else {
			let span = TextSpan::new(func_keyword.span.start, params.span.end);
			Ok(Spanned {
				inner: TypeExpression::Function {
					params: params.inner,
					result: None,
				},
				span,
			})
		}
	}

	fn nud_lookup(
		&mut self,
		token: Spanned<Token>,
	) -> Option<(
		fn(parser: &mut Parser) -> Result<Spanned<Expression>, ()>,
		BindingPower,
	)> {
		match token.inner {
			Token::Identifier => {
				match Keyword::try_from(token.span.extract_str(self.source)) {
					Ok(Keyword::Return) => Some((
						Parser::parse_return_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::If) => Some((
						Parser::parse_if_else_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::Loop) => Some((
						Parser::parse_loop_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::Match) => Some((
						Parser::parse_match_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::Break) => Some((
						Parser::parse_break_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::Continue) => Some((
						Parser::parse_continue_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::Underscore) => Some((
						Parser::parse_placeholder_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::Block) => Some((
						Parser::parse_keyword_block_expression,
						BindingPower::Primary,
					)),
					_ => Some((
						Parser::parse_path_expression,
						BindingPower::Primary,
					)),
				}
			}
			Token::Int => {
				Some((Parser::parse_int_expression, BindingPower::Primary))
			}
			Token::Float => {
				Some((Parser::parse_float_expression, BindingPower::Primary))
			}
			Token::OpenBrace => Some((
				Parser::parse_bare_block_expression,
				BindingPower::Primary,
			)),
			Token::OpenParen => {
				Some((Parser::parse_tuple_expression, BindingPower::Default))
			}
			Token::Minus | Token::Bang | Token::Caret => {
				Some((Parser::parse_unary_expression, BindingPower::Unary))
			}
			Token::String => {
				Some((Parser::parse_string_expression, BindingPower::Primary))
			}
			Token::Char => {
				Some((Parser::parse_char_expression, BindingPower::Primary))
			}
			Token::OpenBracket => {
				Some((Parser::parse_array_expression, BindingPower::Primary))
			}
			Token::LeftArrow => Some((
				Parser::parse_qualified_path_expression,
				BindingPower::Primary,
			)),
			_ => None,
		}
	}

	fn led_lookup(
		&mut self,
		token: Spanned<Token>,
	) -> Option<(
		fn(
			parser: &mut Parser,
			left: Spanned<Expression>,
			bp: BindingPower,
		) -> Result<Spanned<Expression>, ()>,
		BindingPower,
	)> {
		match token.inner {
			Token::Plus | Token::Minus => {
				Some((Parser::parse_binary_expression, BindingPower::Additive))
			}
			Token::Star | Token::Slash | Token::Percent => Some((
				Parser::parse_binary_expression,
				BindingPower::Multiplicative,
			)),
			Token::Eq
			| Token::PlusEq
			| Token::MinusEq
			| Token::StarEq
			| Token::SlashEq
			| Token::PercentEq
			| Token::AmperEq
			| Token::VbarEq
			| Token::CaretEq
			| Token::DoubleLeftArrowEq
			| Token::DoubleRightArrowEq => Some((
				Parser::parse_binary_expression,
				BindingPower::Assignment,
			)),
			Token::DoubleVbar => {
				Some((Parser::parse_binary_expression, BindingPower::LogicalOr))
			}
			Token::DoubleAmper => Some((
				Parser::parse_binary_expression,
				BindingPower::LogicalAnd,
			)),
			Token::Vbar => {
				Some((Parser::parse_binary_expression, BindingPower::BitwiseOr))
			}
			Token::Caret => Some((
				Parser::parse_binary_expression,
				BindingPower::BitwiseXor,
			)),
			Token::Amper => Some((
				Parser::parse_binary_expression,
				BindingPower::BitwiseAnd,
			)),
			Token::EqEq
			| Token::BangEq
			| Token::LeftArrowEq
			| Token::LeftArrow
			| Token::RightArrow
			| Token::RightArrowEq => Some((
				Parser::parse_binary_expression,
				BindingPower::Comparison,
			)),
			Token::DoubleLeftArrow | Token::DoubleRightArrow => Some((
				Parser::parse_binary_expression,
				BindingPower::BitwiseShift,
			)),
			Token::OpenParen => {
				Some((Parser::parse_call_expression, BindingPower::Postfix))
			}
			Token::ColonColon => Some((
				Parser::parse_type_application_expression,
				BindingPower::Member,
			)),
			Token::Dot => Some((
				Parser::parse_object_access_expression,
				BindingPower::Member,
			)),
			Token::OpenBracket => {
				Some((Parser::parse_index_expression, BindingPower::Postfix))
			}
			_ => None,
		}
	}

	/// An expression. Like every parse function, it has reported whatever
	/// made it fail.
	fn parse_expression(
		&mut self,
		limit_bp: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		let token = self.lexer.peek();
		let nud_handler = match self.nud_lookup(token) {
			Some((nud_handler, _)) => nud_handler,
			None => {
				self.ast
					.diagnostics
					.push(report_expected_expression(self.ast.file_id, token));
				return Err(());
			}
		};
		let mut left = nud_handler(self)?;

		// A block-like expression is never an operand: it fills an
		// expression position whole and ends at its closing `}`, so no
		// operator continues it and none takes it without parentheses
		// (`(if c { f } else { g })(x)`). An assignment's value is a whole
		// position too, as a `local`'s initializer is (`x = if c { 1 } else
		// { 2 }`): only an operator binding tighter takes an operand. In a
		// statement list, what follows is the next statement: `if c { .. }
		// (a, b)` is two. Once that is reported, the operators are read as
		// before, so the caller sees one diagnostic and a whole expression.
		if left.inner.is_block_like() {
			let token = self.lexer.peek();
			if limit_bp > BindingPower::Assignment {
				self.ast.diagnostics.push(report_block_like_operand(
					self.ast.file_id,
					&left,
					None,
				));
			} else if self
				.led_lookup(token)
				.is_some_and(|(_, bp)| bp > limit_bp)
				&& self.nud_lookup(token).is_none()
			{
				// A token that can only continue this expression; one that
				// can also start one (`(`, `[`, `-`) starts whatever comes
				// next, and one that binds no tighter than `limit_bp`
				// continues an enclosing expression instead.
				self.ast.diagnostics.push(report_block_like_operand(
					self.ast.file_id,
					&left,
					Some(token.span),
				));
			} else {
				return Ok(left);
			}
		}

		loop {
			let token = self.lexer.peek();

			let (led_handler, operator_bp) = match self.led_lookup(token) {
				Some((_, bp)) if bp <= limit_bp => break,
				Some((handler, bp)) => (handler, bp),
				None => break,
			};

			left = led_handler(self, left, operator_bp)?;
		}
		Ok(left)
	}

	/// Parse `<Type as Trait>::item` (a trait-qualified path) or
	/// `<Type>::item` (a bare bracketed self-type, no trait) in expression
	/// position — the expression-side twin of
	/// `parse_qualified_path_type_expression`; see its doc comment for how
	/// the two forms are told apart. The opening `<` is not yet consumed.
	/// Ordinary postfix parsing (`Call`, `ObjectAccess`, `Index`) applies on
	/// top of the returned expression via the normal Pratt loop, so `<Type
	/// as Trait>::method(x)` needs no extra handling here.
	fn parse_qualified_path_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let open_span = parser.lexer.next().span; // consume `<`
		let root = parser.parse_bracketed_root(open_span)?;
		let segments = parser.parse_value_path()?;
		let span = TextSpan::new(open_span.start, segments.span().end);
		let segments = segments.segments;
		Ok(Spanned {
			inner: match root {
				BracketedRoot::Qualified(root) => {
					Expression::QualifiedPath { root, segments }
				}
				BracketedRoot::Grouped(inner) => {
					Expression::Grouped { inner, segments }
				}
			},
			span,
		})
	}

	fn parse_path_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let token = parser.lexer.next();
		let text = token.span.extract_str(parser.source);

		match Keyword::try_from(text) {
			Ok(Keyword::SelfLower)
			| Ok(Keyword::SelfPascal)
			| Ok(Keyword::Underscore)
			| Ok(Keyword::Package)
			| Ok(Keyword::Super)
			| Err(_) => {}
			Ok(_) => {
				parser.ast.diagnostics.push(report_reserved_identifier(
					parser.ast.file_id,
					token.span,
				));
			}
		}

		let symbol = parser.strings.get_or_intern(text);
		let start = token.span;

		// Start the path with the first segment (no type args yet).
		let mut segments: Vec<PathSegment> = vec![PathSegment {
			ident: Spanned {
				inner: symbol,
				span: token.span,
			},
			type_args: Box::new([]),
		}];

		loop {
			if parser.lexer.peek().inner != Token::ColonColon {
				break;
			}
			let colons = parser.lexer.next(); // consume `::`
			let next = parser.lexer.peek();
			match next.inner {
				// `::<T, U>` — turbofish type args for the last segment
				Token::LeftArrow => {
					let (type_args, _close) = parser.parse_type_args()?;
					segments.last_mut().unwrap().type_args = type_args;
					// Loop continues: next `::` starts a new segment.
				}
				// `::{ ... }` — the old struct literal
				Token::OpenBrace => {
					return Parser::parse_struct_literal_as_call(
						parser,
						segments.into(),
					);
				}
				// `::ident` — next path segment
				Token::Identifier if parser.is_later_segment(next.span) => {
					let seg_token = parser.lexer.next();
					let seg_text = seg_token.span.extract_str(parser.source);
					let seg_symbol = parser.strings.get_or_intern(seg_text);
					segments.push(PathSegment {
						ident: Spanned {
							inner: seg_symbol,
							span: seg_token.span,
						},
						type_args: Box::new([]),
					});
				}
				// Anything else after `::` is a missing segment: reported,
				// and kept, so the path up to it is still resolved.
				_ => {
					let bad = parser.lexer.peek();
					parser.ast.diagnostics.push(report_invalid_namespace(
						parser.ast.file_id,
						bad.span,
					));
					segments.push(PathSegment::missing(colons.span.end));
					break;
				}
			}
		}

		let end = segments.last().unwrap().ident.span;
		let span = TextSpan::new(start.start, end.end);
		Ok(Spanned {
			inner: Expression::Path(segments.into()),
			span,
		})
	}

	/// A named list and the `)` after it, the `(` consumed. The list is the
	/// call's only argument: anything else before `)` is reported, and read
	/// for recovery. Returns the arguments and where the call ends.
	fn parse_named_call_arguments(
		parser: &mut Parser,
	) -> Result<(Spanned<Box<[Separated<Spanned<NamedArgument>>]>>, u32), ()> {
		let named = Parser::parse_named_arguments(parser)?;
		if parser.lexer.peek().inner != Token::CloseParen {
			let at = parser.lexer.peek().span;
			parser
				.ast
				.diagnostics
				.push(report_mixed_call_arguments(parser.ast.file_id, at));
			while parser.lexer.next_if(Token::Comma).is_some()
				&& parser.lexer.peek().inner != Token::CloseParen
			{
				parser.parse_expression(BindingPower::Default)?;
			}
		}
		let close_span = parser.next_expect(Token::CloseParen)?.span;
		Ok((named, close_span.end))
	}

	/// One positional argument. A named list here follows other arguments,
	/// which is a mix: reported, and read so the call still parses.
	fn parse_positional_argument(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		if parser.lexer.peek().inner != Token::OpenBrace {
			return Parser::parse_element(parser);
		}
		let named = Parser::parse_named_arguments(parser)?;
		parser
			.ast
			.diagnostics
			.push(report_mixed_call_arguments(parser.ast.file_id, named.span));
		Ok(Spanned {
			inner: Expression::Error,
			span: named.span,
		})
	}

	/// `{ name: expr, name, .. }`, braces included.
	fn parse_named_arguments(
		parser: &mut Parser,
	) -> Result<Spanned<Box<[Separated<Spanned<NamedArgument>>]>>, ()> {
		SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			item_handler: Parser::parse_named_argument,
			should_warn_missing_separator: None,
		}
		.parse(parser)
	}

	/// `name: expr`, or the shorthand `name` for `name: name`. `self` is a
	/// name here, a method's receiver (`T::m({ self: x })`). A value not
	/// written yet after the `:` is reported and kept as an error node
	/// spanning the gap up to the next token, as a `local`'s is, so the name
	/// is still read.
	fn parse_named_argument(
		parser: &mut Parser,
	) -> Result<Spanned<NamedArgument>, ()> {
		let name_token = parser.next_expect(Token::Identifier)?;
		let text = name_token.span.extract_str(parser.source);
		let name = Spanned {
			inner: match Keyword::try_from(text) {
				Ok(Keyword::SelfLower) => parser.strings.get_or_intern(text),
				_ => parser.intern_identifier(name_token.span),
			},
			span: name_token.span,
		};
		let (value, span) = match parser.lexer.next_if(Token::Colon) {
			Some(colon) => {
				let token = parser.lexer.peek();
				let value = if parser.nud_lookup(token).is_some() {
					parser.parse_expression(BindingPower::Default)?
				} else {
					parser.ast.diagnostics.push(report_expected_expression(
						parser.ast.file_id,
						token,
					));
					Spanned {
						inner: Expression::Error,
						span: TextSpan::new(colon.span.end, token.span.start),
					}
				};
				let span = TextSpan::new(name_token.span.start, value.span.end);
				(Some(Box::new(value)), span)
			}
			None => (None, name_token.span),
		};
		Ok(Spanned {
			inner: NamedArgument { name, value },
			span,
		})
	}

	/// `Path::{ ... }`, the old struct literal, with `::` consumed and `{`
	/// next. A struct is constructed by a call now: reported, and read as the
	/// named call `Path({ ... })` it stands for.
	fn parse_struct_literal_as_call(
		parser: &mut Parser,
		path: Box<[PathSegment]>,
	) -> Result<Spanned<Expression>, ()> {
		let path_span = TextSpan::new(
			path.first().unwrap().ident.span.start,
			path.last().unwrap().ident.span.end,
		);
		let named = Parser::parse_named_arguments(parser)?;
		parser.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::StructLiteralIsACall.code())
				.with_message("a struct is constructed by a call")
				.with_label(Label::primary(
					parser.ast.file_id,
					TextSpan::new(path_span.start, named.span.end),
				))
				.with_note("write `Name({ field: value, ... })`"),
		);
		Ok(Spanned {
			span: TextSpan::new(path_span.start, named.span.end),
			inner: Expression::NamedCall {
				callee: Box::new(Spanned {
					inner: Expression::Path(path),
					span: path_span,
				}),
				arguments: named,
			},
		})
	}

	fn parse_object_access_expression(
		parser: &mut Parser,
		object: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		let dot = parser.lexer.next(); // consume the dot
		let token = parser.lexer.peek();
		let span = TextSpan::new(object.span.start, token.span.end);
		match token.inner {
			Token::Star => {
				parser.lexer.next();
				Ok(Spanned {
					inner: Expression::Deref {
						pointer: Box::new(object),
					},
					span,
				})
			}
			Token::Amper => {
				parser.lexer.next();
				Ok(Spanned {
					inner: Expression::AddressOf {
						value: Box::new(object),
					},
					span,
				})
			}
			// A keyword is never a member: `x.` on a line of its own is
			// followed by the next statement's `local`, `return`, ...
			Token::Identifier if !parser.is_keyword(token.span) => {
				parser.lexer.next();
				Ok(Spanned {
					inner: Expression::ObjectAccess {
						object: Box::new(object),
						member: PathSegment {
							ident: Spanned {
								inner: parser.strings.get_or_intern(
									token.span.extract_str(parser.source),
								),
								span: token.span,
							},
							type_args: Box::new([]),
						},
					},
					span,
				})
			}
			// `x.` with no member: reported, and kept as an access of a
			// missing one, so the object is still checked, and the token
			// after the dot is left to close or start whatever it does.
			_ => {
				parser.ast.diagnostics.push(report_missing_member(
					parser.ast.file_id,
					token,
					parser.source,
				));
				let span = TextSpan::new(object.span.start, dot.span.end);
				Ok(Spanned {
					inner: Expression::ObjectAccess {
						object: Box::new(object),
						member: PathSegment::missing(dot.span.end),
					},
					span,
				})
			}
		}
	}

	fn parse_binary_expression(
		parser: &mut Parser,
		left: Spanned<Expression>,
		bp: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		let operator_token = parser.lexer.next();
		let operator = match BinaryOp::try_from(operator_token.inner) {
			Ok(operator) => operator,
			Err(_) => unreachable!(),
		};

		let token = parser.lexer.peek();
		if parser.nud_lookup(token).is_none() {
			parser
				.ast
				.diagnostics
				.push(report_incomplete_binary_expression(
					parser.ast.file_id,
					operator_token.span,
				));
			return Err(());
		}
		let right = parser.parse_expression(bp)?;

		// Comparisons and assignments do not associate: neither grouping of
		// `a < b < c` or `a = b = c` means anything (a comparison is a `Bool`,
		// an assignment `()`), so a chain is an error rather than a grouping.
		// Operators parse left-grouped, so a chain is always in `left`;
		// written parentheses make a tuple, which is no chain.
		if let Expression::Binary {
			operator: left_operator,
			..
		} = &left.inner
			&& BindingPower::from(left_operator.inner) == bp
		{
			match bp {
				BindingPower::Comparison => {
					parser.ast.diagnostics.push(report_chained_comparisons(
						parser.ast.file_id,
						left_operator.span,
						operator_token.span,
					));
				}
				BindingPower::Assignment => {
					parser.ast.diagnostics.push(report_chained_assignments(
						parser.ast.file_id,
						left_operator.span,
						operator_token.span,
					));
				}
				_ => {}
			}
		}

		let span = TextSpan::new(left.span.start, right.span.end);
		Ok(Spanned {
			inner: Expression::Binary {
				left: Box::new(left),
				right: Box::new(right),
				operator: Spanned {
					inner: operator,
					span: operator_token.span,
				},
			},
			span,
		})
	}

	fn parse_string_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let token = parser.lexer.next();
		Ok(Spanned {
			inner: Expression::String,
			span: token.span,
		})
	}

	/// The value of the integer literal at `span`, reported and read as `0`
	/// when it does not fit a `u64`.
	fn integer_literal(&mut self, span: TextSpan) -> u64 {
		let text = span.extract_str(self.source).replace('_', "");
		let value = if let Some(rest) =
			text.strip_prefix("0b").or_else(|| text.strip_prefix("0B"))
		{
			u64::from_str_radix(rest, 2).ok()
		} else if let Some(rest) =
			text.strip_prefix("0x").or_else(|| text.strip_prefix("0X"))
		{
			u64::from_str_radix(rest, 16).ok()
		} else {
			text.parse::<u64>().ok()
		};
		value.unwrap_or_else(|| {
			self.ast
				.diagnostics
				.push(report_invalid_integer_literal(self.ast.file_id, span));
			0
		})
	}

	fn parse_char_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let token = parser.lexer.next();
		Ok(Spanned {
			inner: Expression::Char,
			span: token.span,
		})
	}

	fn parse_int_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let token = parser.lexer.next();
		debug_assert!(matches!(token.inner, Token::Int));
		let value = parser.integer_literal(token.span);

		Ok(Spanned {
			inner: Expression::Int { value },
			span: token.span,
		})
	}

	fn parse_float_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let token = parser.lexer.next();
		debug_assert!(matches!(token.inner, Token::Float));

		// Syntactic validity only — `f64::from_str` and `f32::from_str` accept
		// the identical grammar, so this rejects a malformed token (`1e`,
		// `1e+`) without committing to a value. The literal's actual value is
		// preserved exactly in TIR. `coerce_float` checks representability;
		// evaluation and lowering convert at the concrete target width.
		if token
			.span
			.extract_str(parser.source)
			.parse::<f64>()
			.is_err()
		{
			parser.ast.diagnostics.push(report_invalid_float_literal(
				parser.ast.file_id,
				token.span,
			));
		}

		Ok(Spanned {
			inner: Expression::Float,
			span: token.span,
		})
	}

	fn parse_return_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let return_span = parser.lexer.next().span;
		let token = parser.lexer.peek();
		if parser.nud_lookup(token).is_none() {
			return Ok(Spanned {
				inner: Expression::Return { value: None },
				span: return_span,
			});
		}
		let expr = parser.parse_expression(BindingPower::Default)?;
		let span = TextSpan::new(return_span.start, expr.span.end);
		Ok(Spanned {
			inner: Expression::Return {
				value: Some(Box::new(expr)),
			},
			span,
		})
	}

	fn parse_break_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let break_keyword = parser.lexer.next();
		let label = parser.parse_label();
		let token = parser.lexer.peek();
		let value = if parser.nud_lookup(token).is_some() {
			Some(parser.parse_expression(BindingPower::Default)?)
		} else {
			None
		};

		let span = match (label, &value) {
			(_, Some(value)) => {
				TextSpan::new(break_keyword.span.start, value.span.end)
			}
			(Some(label), None) => {
				TextSpan::new(break_keyword.span.start, label.span.end)
			}
			(None, None) => break_keyword.span,
		};
		Ok(Spanned {
			inner: Expression::Break {
				label,
				value: value.map(Box::new),
			},
			span,
		})
	}

	fn parse_continue_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let continue_keyword = parser.lexer.next();
		let label = parser.parse_label();

		let span = match label {
			Some(label) => {
				TextSpan::new(continue_keyword.span.start, label.span.end)
			}
			None => continue_keyword.span,
		};
		Ok(Spanned {
			inner: Expression::Continue { label },
			span,
		})
	}

	fn parse_tuple_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let grouped = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			item_handler: Parser::parse_element,
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		Ok(Spanned {
			inner: Expression::Tuple {
				elements: grouped.inner,
			},
			span: grouped.span,
		})
	}

	/// An element of a parenthesized list: an expression, or `value: Type`.
	fn parse_element(parser: &mut Parser) -> Result<Spanned<Expression>, ()> {
		let value = parser.parse_expression(BindingPower::Default)?;
		if parser.lexer.next_if(Token::Colon).is_none() {
			return Ok(value);
		}
		let ty = parser.parse_type_expression()?;
		Ok(Spanned {
			span: TextSpan::new(value.span.start, ty.span.end),
			inner: Expression::Ascription {
				value: Box::new(value),
				ty: Box::new(ty),
			},
		})
	}

	fn parse_unary_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let operator_token = parser.lexer.next();
		let operator = match UnaryOp::try_from(operator_token.inner) {
			Ok(operator) => operator,
			Err(_) => unreachable!(),
		};

		let token = parser.lexer.peek();
		if parser.nud_lookup(token).is_none() {
			parser
				.ast
				.diagnostics
				.push(report_incomplete_unary_expression(
					parser.ast.file_id,
					operator_token.span,
				));
			return Err(());
		}
		let operand = parser.parse_expression(BindingPower::Unary)?;

		let span = TextSpan::new(operator_token.span.start, operand.span.end);
		Ok(Spanned {
			inner: Expression::Unary {
				operator: Spanned {
					inner: operator,
					span: operator_token.span,
				},
				operand: Box::new(operand),
			},
			span,
		})
	}

	/// `block :label { ... }`: a plain block in expression position. Blocks
	/// that belong to a construct (`if`, `loop`, a match arm, a function body)
	/// are parsed by it directly and need no keyword.
	fn parse_keyword_block_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let keyword_span = parser.lexer.next().span;
		let label = parser.parse_label();
		let block = Parser::parse_block_expression(parser)?;
		let Expression::Block { statements, .. } = block.inner else {
			unreachable!("a block parses as a block")
		};
		Ok(Spanned {
			span: TextSpan::new(keyword_span.start, block.span.end),
			inner: Expression::Block { label, statements },
		})
	}

	/// `:label` after `block`, a loop's keyword, `break` or `continue`. A `:`
	/// with no name after it is reported and keeps the error symbol at the
	/// empty span right after it, as a missing member does
	/// (`PathSegment::missing`); the token after it, a keyword included, is
	/// left for whatever it starts.
	fn parse_label(&mut self) -> Option<Spanned<SymbolU32>> {
		let colon = self.lexer.next_if(Token::Colon)?;
		let token = self.lexer.peek();
		if token.inner != Token::Identifier || self.is_keyword(token.span) {
			self.ast.diagnostics.push(report_unexpected_token(
				self.ast.file_id,
				token,
				Token::Identifier,
			));
			return Some(Spanned {
				inner: Keyword::Error.symbol(),
				span: TextSpan::new(colon.span.end, colon.span.end),
			});
		}
		let span = self.lexer.next().span;
		Some(Spanned {
			inner: self.strings.get_or_intern(span.extract_str(self.source)),
			span,
		})
	}

	/// `{ ... }` where an expression starts: the plain block without its
	/// keyword. `{` is reserved for named arguments in a call, so this is
	/// reported, and read as the block it was meant to be.
	fn parse_bare_block_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let brace_span = parser.lexer.peek().span;
		parser.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::BlockNeedsKeyword.code())
				.with_message("a block expression is written `block { ... }`")
				.with_label(
					Label::primary(parser.ast.file_id, brace_span)
						.with_message("expected `block` before `{`"),
				),
		);
		Parser::parse_block_expression(parser)
	}

	fn parse_block_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let statements = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::SemiColon,
			item_handler: |parser| {
				let token = parser.lexer.peek();
				let keyword = match token.inner {
					Token::Identifier => {
						Keyword::try_from(token.span.extract_str(parser.source))
							.ok()
					}
					_ => None,
				};
				match keyword {
					Some(Keyword::Local) => {
						Parser::parse_local_definition_statement(parser)
					}
					_ => {
						let expr =
							parser.parse_expression(BindingPower::Default)?;
						let span = expr.span;
						Ok(Spanned {
							inner: Statement::Expression(Box::new(expr)),
							span,
						})
					}
				}
			},
			should_warn_missing_separator: Some(|stmt| {
				!Statement::is_block_like(stmt)
			}),
		}
		.parse(parser)?;

		Ok(Spanned {
			span: statements.span,
			inner: Expression::Block {
				label: None,
				statements,
			},
		})
	}

	fn parse_loop_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let loop_keyword = parser.lexer.next();
		let label = parser.parse_label();
		let block = Parser::parse_block_expression(parser)?;

		let span = TextSpan::new(loop_keyword.span.start, block.span.end);
		Ok(Spanned {
			inner: Expression::Loop {
				label,
				block: Box::new(block),
			},
			span,
		})
	}

	fn parse_if_else_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let if_keyword = parser.lexer.next();
		let label = parser.parse_label();
		let condition = parser.parse_expression(BindingPower::Default)?;
		let then_block = Parser::parse_block_expression(parser)?;
		let else_block = match parser.peek_keyword() {
			Some(Keyword::Else) => {
				let _ = parser.lexer.next();
				// `else if` nests an `if` in the else position; `else { .. }`
				// stays a plain block. TIR's `IfElse` branch and the checker's
				// `build_branch` already describe both shapes.
				if matches!(parser.peek_keyword(), Some(Keyword::If)) {
					Some(Box::new(Parser::parse_if_else_expression(parser)?))
				} else {
					Some(Box::new(Parser::parse_block_expression(parser)?))
				}
			}
			_ => None,
		};
		let end = else_block.as_ref().map_or(then_block.span, |b| b.span).end;
		let if_else = Spanned {
			inner: Expression::IfElse {
				condition: Box::new(condition),
				then_block: Box::new(then_block),
				else_block,
			},
			span: TextSpan::new(if_keyword.span.start, end),
		};
		let Some(label) = label else {
			return Ok(if_else);
		};
		// Read as the block it would be written in, so a `break` to the label
		// still finds it.
		parser.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::LabelOnIf.code())
				.with_message("an `if` cannot be labelled")
				.with_label(
					Label::primary(parser.ast.file_id, label.span)
						.with_message("a label names a `block` or a `loop`"),
				)
				.with_note(
					"write it on a block around the `if`: `block :label { if .. }`",
				),
		);
		let span = if_else.span;
		Ok(Spanned {
			inner: Expression::Block {
				label: Some(label),
				// No braces are written: the block is the `if` alone.
				statements: Spanned {
					inner: Box::new([Separated {
						inner: Spanned {
							inner: Statement::Expression(Box::new(if_else)),
							span,
						},
						separator: None,
					}]),
					span,
				},
			},
			span,
		})
	}

	fn parse_match_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let match_keyword = parser.lexer.next();
		let scrutinee = parser.parse_expression(BindingPower::Default)?;

		let arms = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			item_handler:
				|parser: &mut Parser| -> Result<Spanned<MatchArm>, ()> {
					let pattern = Parser::parse_pattern(parser)?;
					parser.next_expect(Token::FatArrow)?;
					// A braced body is a block; a bare expression must be
					// separated by a comma like a statement.
					let body = if parser.lexer.peek().inner == Token::OpenBrace
					{
						Parser::parse_block_expression(parser)?
					} else {
						parser.parse_expression(BindingPower::Default)?
					};
					let span = TextSpan::new(pattern.span.start, body.span.end);
					Ok(Spanned {
						inner: MatchArm {
							pattern,
							body: Box::new(body),
						},
						span,
					})
				},
			// A block body is self-delimiting, so its trailing comma stays
			// optional, exactly as a block-like statement's separator does.
			// Any other body needs a comma before the next arm.
			should_warn_missing_separator: Some(|arm| {
				!arm.body.inner.is_block_like()
			}),
		}
		.parse(parser)?;

		let span = TextSpan::new(match_keyword.span.start, arms.span.end);
		Ok(Spanned {
			inner: Expression::Match {
				scrutinee: Box::new(scrutinee),
				arms: arms.inner,
			},
			span,
		})
	}

	/// Handles `expr::<T, U>` when `expr` is not a path (paths take their
	/// type arguments in `parse_identifier_expression`). Only a member
	/// (`obj.method::<T>`) accepts them; they join its segment.
	fn parse_type_application_expression(
		parser: &mut Parser,
		left: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		let colons = parser.lexer.next(); // consume `::`

		if parser.lexer.peek().inner == Token::LeftArrow {
			let (args, close_span) = parser.parse_type_args()?;
			let span = TextSpan::new(left.span.start, close_span.end);
			return match left.inner {
				Expression::ObjectAccess { object, mut member }
					if member.type_args.is_empty() =>
				{
					member.type_args = args;
					Ok(Spanned {
						inner: Expression::ObjectAccess { object, member },
						span,
					})
				}
				_ => {
					parser.ast.diagnostics.push(report_type_args_not_allowed(
						parser.ast.file_id,
						TextSpan::new(colons.span.start, close_span.end),
					));
					Err(())
				}
			};
		}

		let bad = parser.lexer.peek();
		parser
			.ast
			.diagnostics
			.push(report_invalid_namespace(parser.ast.file_id, bad.span));
		Err(())
	}

	/// `callee(a, b)` or `callee({ x: a, y })`, decided on the token after
	/// `(`: `{` opens a named list (a plain block is spelled `block { }`, so
	/// nothing else starts with `{` here), anything else a positional one.
	/// A callee that names a method on an object makes it a method call.
	fn parse_call_expression(
		parser: &mut Parser,
		callee: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		let start = callee.span.start;
		let open_span = parser.next_expect(Token::OpenParen)?.span;
		if parser.lexer.peek().inner == Token::OpenBrace {
			let (arguments, end) = Parser::parse_named_call_arguments(parser)?;
			let inner = match Parser::method_callee(callee) {
				Ok((object, method)) => {
					Expression::NamedMethodCall(Box::new(MethodCallExpr {
						object,
						method,
						arguments,
					}))
				}
				Err(callee) => Expression::NamedCall {
					callee: Box::new(callee),
					arguments,
				},
			};
			return Ok(Spanned {
				inner,
				span: TextSpan::new(start, end),
			});
		}
		let arguments = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			item_handler: Parser::parse_positional_argument,
			should_warn_missing_separator: None,
		}
		.parse_after_open(parser, open_span)?;
		let span = TextSpan::new(start, arguments.span.end);
		let inner = match Parser::method_callee(callee) {
			Ok((object, method)) => {
				Expression::MethodCall(Box::new(MethodCallExpr {
					object,
					method,
					arguments,
				}))
			}
			Err(callee) => Expression::Call {
				callee: Box::new(callee),
				arguments,
			},
		};
		Ok(Spanned { inner, span })
	}

	/// The object, method and type arguments of a callee that names a method
	/// (`object.method`, `object.method::<T>`); any other callee back as is.
	#[allow(clippy::type_complexity)]
	fn method_callee(
		callee: Spanned<Expression>,
	) -> Result<(Box<Spanned<Expression>>, PathSegment), Spanned<Expression>> {
		match callee.inner {
			Expression::ObjectAccess { object, member } => Ok((object, member)),
			inner => Err(Spanned {
				inner,
				span: callee.span,
			}),
		}
	}

	fn parse_array_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let open_span = parser.next_expect(Token::OpenBracket)?.span;

		if let Some(close) = parser.lexer.next_if(Token::CloseBracket) {
			let span = TextSpan::new(open_span.start, close.span.end);
			return Ok(Spanned {
				inner: Expression::ArrayList {
					elements: Box::new([]),
				},
				span,
			});
		}

		let first = parser.parse_expression(BindingPower::Default)?;

		if parser.lexer.next_if(Token::SemiColon).is_some() {
			let count = parser.parse_length()?;
			let close_span = parser.next_expect(Token::CloseBracket)?.span;
			let span = TextSpan::new(open_span.start, close_span.end);
			return Ok(Spanned {
				inner: Expression::ArrayRepeat {
					value: Box::new(first),
					count,
				},
				span,
			});
		}

		let mut elements = Vec::new();
		let mut element = first;
		loop {
			let separator =
				parser.lexer.next_if(Token::Comma).map(|comma| comma.span);
			let last = separator.is_none()
				|| parser.lexer.peek().inner == Token::CloseBracket;
			elements.push(Separated {
				inner: element,
				separator,
			});
			if last {
				break;
			}
			element = parser.parse_expression(BindingPower::Default)?;
		}

		let close_span = parser.next_expect(Token::CloseBracket)?.span;
		let span = TextSpan::new(open_span.start, close_span.end);
		Ok(Spanned {
			inner: Expression::ArrayList {
				elements: elements.into_boxed_slice(),
			},
			span,
		})
	}

	fn parse_index_expression(
		parser: &mut Parser,
		object: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		_ = parser.lexer.next(); // consume `[`
		let index = Box::new(parser.parse_expression(BindingPower::Default)?);

		let close_span = parser.next_expect(Token::CloseBracket)?.span;
		let span = TextSpan::new(object.span.start, close_span.end);
		Ok(Spanned {
			inner: Expression::Index {
				object: Box::new(object),
				index,
			},
			span,
		})
	}

	/// `..`, or one element in the list.
	fn parse_pattern_element(
		parser: &mut Parser,
	) -> Result<Spanned<PatternElement>, ()> {
		if let Some(dot_dot) = parser.lexer.next_if(Token::DotDot) {
			return Ok(Spanned {
				inner: PatternElement::Rest,
				span: dot_dot.span,
			});
		}
		let pattern = Parser::parse_pattern(parser)?;
		Ok(Spanned {
			inner: PatternElement::Pattern(pattern.inner),
			span: pattern.span,
		})
	}

	/// `..`, `name` or `name: pat`.
	fn parse_pattern_field_item(
		parser: &mut Parser,
	) -> Result<Spanned<PatternFieldItem>, ()> {
		if let Some(dot_dot) = parser.lexer.next_if(Token::DotDot) {
			return Ok(Spanned {
				inner: PatternFieldItem::Rest,
				span: dot_dot.span,
			});
		}
		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name = Spanned {
			inner: parser.intern_identifier(name_span),
			span: name_span,
		};
		let pattern = if parser.lexer.next_if(Token::Colon).is_some() {
			Some(Parser::parse_pattern(parser)?)
		} else {
			None
		};
		let span = match &pattern {
			Some(p) => TextSpan::new(name_span.start, p.span.end),
			None => name_span,
		};
		Ok(Spanned {
			inner: PatternFieldItem::Field(PatternField { name, pattern }),
			span,
		})
	}

	/// `{ field, other: pat, .. }`, braces included, as written.
	fn parse_pattern_fields(
		parser: &mut Parser,
	) -> Result<Spanned<PatternFields>, ()> {
		SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			should_warn_missing_separator: None,
			item_handler: Parser::parse_pattern_field_item,
		}
		.parse(parser)
	}

	/// `(pat, .., pat)`.
	fn parse_tuple_pattern(
		parser: &mut Parser,
	) -> Result<Spanned<Pattern>, ()> {
		let elements = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			should_warn_missing_separator: None,
			item_handler: Parser::parse_pattern_element,
		}
		.parse(parser)?;
		Ok(Spanned {
			inner: Pattern::Destructure(Destructure::Tuple {
				elements: elements.inner,
			}),
			span: elements.span,
		})
	}

	/// `Path(pat, ..)` or `Path({ field, .. })`, with `path` consumed and `(`
	/// next — decided on the token after `(`, exactly as a call's arguments.
	fn parse_struct_pattern(
		parser: &mut Parser,
		path: Box<[PathSegment]>,
	) -> Result<Spanned<Pattern>, ()> {
		let path_start = path.first().unwrap().ident.span.start;
		let open_span = parser.next_expect(Token::OpenParen)?.span;
		if parser.lexer.peek().inner == Token::OpenBrace {
			let fields = Parser::parse_pattern_fields(parser)?;
			let close_span = parser.next_expect(Token::CloseParen)?.span;
			return Ok(Spanned {
				inner: Pattern::Destructure(Destructure::NamedStruct {
					path,
					fields: fields.inner,
				}),
				span: TextSpan::new(path_start, close_span.end),
			});
		}
		let elements = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			should_warn_missing_separator: None,
			item_handler: Parser::parse_pattern_element,
		}
		.parse_after_open(parser, open_span)?;
		Ok(Spanned {
			inner: Pattern::Destructure(Destructure::Struct {
				path,
				elements: elements.inner,
			}),
			span: TextSpan::new(path_start, elements.span.end),
		})
	}

	/// `Path::{ ... }`, the old named pattern: gone. The fields are read and
	/// dropped, so the rest of the file still parses, and the pattern itself
	/// is an error.
	fn parse_old_struct_pattern(
		parser: &mut Parser,
		path: &[PathSegment],
	) -> Result<PathTerm, ()> {
		let path_start = path.first().unwrap().ident.span.start;
		let named = Parser::parse_pattern_fields(parser)?;
		let span = TextSpan::new(path_start, named.span.end);
		parser.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::StructLiteralIsACall.code())
				.with_message(
					"a struct pattern is written like its construction",
				)
				.with_label(Label::primary(parser.ast.file_id, span))
				.with_note("write `Name({ field, .. })` or `Name(a, b)`"),
		);
		Ok(PathTerm::Old(Spanned {
			inner: Pattern::Error,
			span,
		}))
	}

	/// A path: one or more segments, `A::B`. As in an expression, it may
	/// start at `Self`, `crate` or `super`.
	fn parse_path(parser: &mut Parser) -> Result<PathTerm, ()> {
		let name_span = parser.next_expect(Token::Identifier)?.span;
		let text = name_span.extract_str(parser.source);
		let first = match Keyword::try_from(text) {
			Ok(Keyword::SelfPascal | Keyword::Package | Keyword::Super) => {
				parser.strings.get_or_intern(text)
			}
			_ => parser.intern_identifier(name_span),
		};
		let mut segments = vec![PathSegment {
			ident: Spanned {
				inner: first,
				span: name_span,
			},
			type_args: Box::new([]),
		}];

		while parser.lexer.peek().inner == Token::ColonColon {
			let colons = parser.lexer.next(); // consume `::`
			let next = parser.lexer.peek();
			match next.inner {
				// `::<T, U>` — turbofish for the last segment
				Token::LeftArrow => {
					let (type_args, _close) = parser.parse_type_args()?;
					segments.last_mut().unwrap().type_args = type_args;
				}
				// `::{ ... }` — the old named pattern, gone
				Token::OpenBrace => {
					return Parser::parse_old_struct_pattern(parser, &segments);
				}
				// `::ident` — another path segment
				Token::Identifier if parser.is_later_segment(next.span) => {
					// A later segment is a name, `super` included, as in an
					// expression.
					let seg_span = parser.next_expect(Token::Identifier)?.span;
					let seg_text = seg_span.extract_str(parser.source);
					segments.push(PathSegment {
						ident: Spanned {
							inner: parser.strings.get_or_intern(seg_text),
							span: seg_span,
						},
						type_args: Box::new([]),
					});
				}
				// A missing segment: reported, and kept, as in an
				// expression's path.
				_ => {
					let bad = parser.lexer.peek();
					parser.ast.diagnostics.push(report_invalid_namespace(
						parser.ast.file_id,
						bad.span,
					));
					segments.push(PathSegment::missing(colons.span.end));
					break;
				}
			}
		}

		Ok(PathTerm::Path(segments.into()))
	}

	/// A term that starts with a path: a struct pattern (`Path(..)`), a
	/// qualified path (a constant), or a single-segment name (a binding).
	fn parse_path_pattern(parser: &mut Parser) -> Result<Spanned<Pattern>, ()> {
		let segments = match Parser::parse_path(parser)? {
			PathTerm::Path(segments) => segments,
			PathTerm::Old(pattern) => return Ok(pattern),
		};

		if parser.lexer.peek().inner == Token::OpenParen {
			return Parser::parse_struct_pattern(parser, segments);
		}

		// A single segment with no type arguments is a name, and a name
		// binds; anything longer is a path, and a path is a constant.
		let span = TextSpan::new(
			segments[0].ident.span.start,
			segments.last().unwrap().ident.span.end,
		);
		match &*segments {
			[segment] if segment.type_args.is_empty() => Ok(Spanned {
				inner: Pattern::Binding {
					mut_span: None,
					name: segment.ident,
				},
				span,
			}),
			_ => Ok(Spanned {
				inner: Pattern::Constant { path: segments },
				span,
			}),
		}
	}

	/// `const P`: a name marked `const` compares with the constant of that
	/// name instead of binding it. Only a path can be marked: a literal is
	/// a comparison already, and a destructure has no name to mark.
	fn parse_const_pattern(
		parser: &mut Parser,
		const_span: TextSpan,
	) -> Result<Spanned<Pattern>, ()> {
		let path = match Parser::parse_path(parser)? {
			PathTerm::Path(path) => path,
			PathTerm::Old(_) => return Err(()),
		};
		// A path of one segment is a name, which is ambiguous: the marker
		// is what says it is a constant. A longer path is a constant
		// already, and the marker says nothing.
		let ambiguous = matches!(
			&*path,
			[segment] if segment.type_args.is_empty()
		);
		if !ambiguous {
			parser
				.ast
				.diagnostics
				.push(report_redundant_const(parser.ast.file_id, const_span));
		}
		let span = TextSpan::new(
			const_span.start,
			path.last().unwrap().ident.span.end,
		);
		Ok(Spanned {
			inner: Pattern::Constant { path },
			span,
		})
	}

	/// A pattern, alternatives included: `|` joins them.
	fn parse_pattern(parser: &mut Parser) -> Result<Spanned<Pattern>, ()> {
		let first = Parser::parse_primary(parser)?;
		if parser.lexer.peek().inner != Token::Vbar {
			return Ok(first);
		}
		let start = first.span.start;
		let mut alternatives = Vec::new();
		let mut current = first;
		while let Some(bar) = parser.lexer.next_if(Token::Vbar) {
			alternatives.push(Separated {
				inner: current,
				separator: Some(bar.span),
			});
			current = Parser::parse_primary(parser)?;
		}
		let end = current.span.end;
		alternatives.push(Separated {
			inner: current,
			separator: None,
		});
		Ok(Spanned {
			inner: Pattern::Or(alternatives.into()),
			span: TextSpan::new(start, end),
		})
	}

	/// One term of a pattern. What it is follows from its own shape: a
	/// literal compares with that value, a qualified path with that
	/// constant, and a name binds — unless `const` says it is a constant.
	fn parse_primary(parser: &mut Parser) -> Result<Spanned<Pattern>, ()> {
		let token = parser.lexer.peek();
		match token.inner {
			Token::OpenParen => Parser::parse_tuple_pattern(parser),
			Token::Int
			| Token::Char
			| Token::Float
			| Token::String
			| Token::Minus => {
				let literal = parser.parse_literal()?;
				Ok(Spanned {
					inner: Pattern::Literal(literal.inner),
					span: literal.span,
				})
			}
			Token::Identifier => {
				let text = token.span.extract_str(parser.source);
				match Keyword::try_from(text) {
					Ok(Keyword::Underscore) => {
						let span = parser.lexer.next().span;
						Ok(Spanned {
							inner: Pattern::Wildcard,
							span,
						})
					}
					Ok(Keyword::Mut) => {
						let mut_span = parser.lexer.next().span;
						let name_span =
							parser.next_expect(Token::Identifier)?.span;
						let name = Spanned {
							inner: parser.intern_identifier(name_span),
							span: name_span,
						};
						Ok(Spanned {
							inner: Pattern::Binding {
								mut_span: Some(mut_span),
								name,
							},
							span: TextSpan::new(mut_span.start, name_span.end),
						})
					}
					Ok(Keyword::Const) => {
						let const_span = parser.lexer.next().span;
						Parser::parse_const_pattern(parser, const_span)
					}
					Ok(Keyword::Local) => {
						let span = parser.lexer.next().span;
						parser.ast.diagnostics.push(report_redundant_local(
							parser.ast.file_id,
							span,
						));
						Err(())
					}
					_ => Parser::parse_path_pattern(parser),
				}
			}
			_ => {
				let token = parser.lexer.next();
				parser.ast.diagnostics.push(report_unexpected_token(
					parser.ast.file_id,
					token,
					Token::Identifier,
				));
				Err(())
			}
		}
	}

	fn parse_local_definition_statement(
		parser: &mut Parser,
	) -> Result<Spanned<Statement>, ()> {
		let local_keyword = parser.lexer.next();

		let pattern = Parser::parse_pattern(parser)?;
		let mut end = pattern.span.end;

		// A part not written yet (`local x: `, `local x: T`, `local x = `) is
		// reported and kept as an error node, as a parameter's missing type
		// is: the statement and what is written of it stay, and the token
		// that follows is left for whatever it closes or starts. The node
		// spans the gap where the part belongs, up to that token, so a
		// position there is in it (what completion reads).
		let ty = match parser.lexer.next_if(Token::Colon) {
			Some(colon) => {
				let ty = parser.parse_type_expression().unwrap_or_else(|()| {
					Spanned {
						inner: TypeExpression::Error,
						span: TextSpan::new(
							colon.span.end,
							parser.lexer.peek().span.start,
						),
					}
				});
				end = ty.span.end;
				Some(Box::new(ty))
			}
			None => None,
		};

		let assigned = parser.lexer.next_if(Token::Eq);
		if let Some(eq) = assigned {
			end = eq.span.end;
		}
		let token = parser.lexer.peek();
		let value = if assigned.is_some() && parser.nud_lookup(token).is_some()
		{
			parser.parse_expression(BindingPower::Default)?
		} else {
			parser
				.ast
				.diagnostics
				.push(report_missing_local_initializer(
					parser.ast.file_id,
					token.span,
				));
			Spanned {
				inner: Expression::Error,
				span: TextSpan::new(end, token.span.start),
			}
		};

		let span = TextSpan::new(local_keyword.span.start, value.span.end);
		Ok(Spanned {
			inner: Statement::LocalDefinition {
				pattern,
				ty,
				value: Box::new(value),
			},
			span,
		})
	}

	fn parse_global_definition_item(
		parser: &mut Parser,
	) -> Result<Spanned<Item>, ()> {
		let global_keyword = parser.lexer.next();
		let token = parser.lexer.peek();
		let mut_span =
			match Keyword::try_from(token.span.extract_str(parser.source)) {
				Ok(Keyword::Mut) => {
					let mut_token = parser.lexer.next();
					Some(mut_token.span)
				}
				_ => None,
			};

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name = Spanned {
			inner: parser.intern_identifier(name_span),
			span: name_span,
		};

		let ty = match parser.lexer.next_if(Token::Colon) {
			Some(_) => Some(Box::new(parser.parse_type_expression()?)),
			None => None,
		};

		let assigned = parser.lexer.next_if(Token::Eq).is_some();
		let token = parser.lexer.peek();
		if !assigned || parser.nud_lookup(token).is_none() {
			parser
				.ast
				.diagnostics
				.push(report_missing_global_initializer(
					parser.ast.file_id,
					token.span,
				));
			return Err(());
		}
		let value = parser.parse_expression(BindingPower::Default)?;

		let span = TextSpan::new(global_keyword.span.start, value.span.end);
		Ok(Spanned {
			inner: Item::Global {
				pub_span: None,
				mut_span,
				name,
				ty,
				value: Box::new(value),
				attributes: Box::new([]),
			},
			span,
		})
	}

	fn parse_const_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let const_span = parser.lexer.next().span;
		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name_symbol = parser.intern_identifier(name_span);

		let ty = if parser.lexer.next_if(Token::Colon).is_some() {
			Some(Box::new(parser.parse_type_expression()?))
		} else {
			None
		};

		let _ = parser.next_expect(Token::Eq)?;
		let value = parser.parse_expression(BindingPower::Default)?;

		let span = TextSpan::new(const_span.start, value.span.end);
		Ok(Spanned {
			inner: Item::Const {
				pub_span: None,
				name: Spanned {
					inner: name_symbol,
					span: name_span,
				},
				ty,
				value: Box::new(value),
				attributes: Box::new([]),
			},
			span,
		})
	}

	fn parse_placeholder_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let underscore = parser.lexer.next();
		Ok(Spanned {
			inner: Expression::Placeholder,
			span: underscore.span,
		})
	}

	fn parse_export_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let export_keyword = parser.lexer.next();

		if parser.lexer.peek().inner != Token::OpenBrace {
			let entry = Parser::parse_export_entry(parser)?;
			let span = TextSpan::new(export_keyword.span.start, entry.span.end);
			return Ok(Spanned {
				inner: Item::Export { entry },
				span,
			});
		}

		let entries = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			item_handler: Parser::parse_export_entry,
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		let span = TextSpan::new(export_keyword.span.start, entries.span.end);

		Ok(Spanned {
			inner: Item::ExportBlock {
				keyword_span: export_keyword.span,
				entries: entries.inner,
			},
			span,
		})
	}

	fn parse_export_entry(
		parser: &mut Parser,
	) -> Result<Spanned<ExportEntry>, ()> {
		let name_token = parser.next_expect(Token::Identifier)?;
		let name_symbol = parser.intern_identifier(name_token.span);

		let alias = if matches!(parser.peek_keyword(), Some(Keyword::As)) {
			parser.lexer.next();
			Some(parser.next_expect(Token::String)?.span)
		} else {
			None
		};

		let span = match alias {
			Some(alias) => TextSpan::new(name_token.span.start, alias.end),
			None => name_token.span,
		};

		Ok(Spanned {
			inner: ExportEntry {
				name: Spanned {
					inner: name_symbol,
					span: name_token.span,
				},
				alias,
			},
			span,
		})
	}

	fn parse_enum_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let enum_span = parser.lexer.next().span;

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name_symbol = parser.intern_identifier(name_span);

		// The repr is written like a struct's fields, `enum Ordering(i8)`.
		// The old `enum Ordering: i8` is reported and read as the new form.
		let repr = if let Some(colon) = parser.lexer.next_if(Token::Colon) {
			parser.ast.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::EnumReprNeedsParentheses.code())
					.with_message("an enum's repr is written in parentheses")
					.with_label(
						Label::primary(parser.ast.file_id, colon.span)
							.with_message("expected `(`"),
					)
					.with_note("write `enum Name(Type) { ... }`"),
			);
			Some(Box::new(parser.parse_type_expression()?))
		} else if parser.lexer.next_if(Token::OpenParen).is_some() {
			let repr = parser.parse_type_expression()?;
			parser.next_expect(Token::CloseParen)?;
			Some(Box::new(repr))
		} else {
			None
		};

		// A `..` is an entry of the body like a variant. Where it stands and
		// how many there are is judged when the enum's signature is built.
		let entries = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			item_handler:
				|parser: &mut Parser| -> Result<Spanned<EnumEntry>, ()> {
					if let Some(dots) = parser.lexer.next_if(Token::DotDot) {
						return Ok(Spanned {
							inner: EnumEntry::Rest,
							span: dots.span,
						});
					}
					let name_token = parser.next_expect(Token::Identifier)?;
					let name_symbol = parser.intern_identifier(name_token.span);

					let (value, span) =
						if parser.lexer.next_if(Token::Eq).is_some() {
							let expr = parser
								.parse_expression(BindingPower::Default)?;
							let span = TextSpan::new(
								name_token.span.start,
								expr.span.end,
							);
							(Some(Box::new(expr)), span)
						} else {
							(None, name_token.span)
						};

					Ok(Spanned {
						inner: EnumEntry::Variant(EnumVariant {
							name: Spanned {
								inner: name_symbol,
								span: name_token.span,
							},
							value,
						}),
						span,
					})
				},
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		let span = TextSpan::new(enum_span.start, entries.span.end);

		Ok(Spanned {
			inner: Item::Enum {
				pub_span: None,
				repr,
				name: Spanned {
					inner: name_symbol,
					span: name_span,
				},
				entries: entries.inner,
				attributes: Box::new([]),
			},
			span,
		})
	}

	fn parse_impl_member(parser: &mut Parser) -> Result<Spanned<ImplItem>, ()> {
		let attrs = Parser::parse_attributes(parser)?;
		let pub_span = match parser.peek_keyword() {
			Some(Keyword::Pub) => Some(parser.lexer.next().span),
			_ => None,
		};

		match parser.peek_keyword() {
			Some(Keyword::Type) => {
				let type_span = parser.lexer.next().span;
				let name_span = parser.next_expect(Token::Identifier)?.span;
				let name_symbol = parser.intern_identifier(name_span);
				parser.next_expect(Token::Eq)?;
				let ty = parser.parse_type_expression()?;
				let span = TextSpan::new(type_span.start, ty.span.end);
				Ok(Spanned {
					inner: ImplItem::AssocType {
						pub_span,
						name: Spanned {
							inner: name_symbol,
							span: name_span,
						},
						ty: Box::new(Spanned {
							inner: ty.inner,
							span: ty.span,
						}),
						attributes: Box::new([]),
					},
					span,
				})
			}
			Some(Keyword::Const) => {
				let const_span = parser.lexer.next().span;
				let name_span = parser.next_expect(Token::Identifier)?.span;
				let name_symbol = parser.intern_identifier(name_span);

				let ty = if parser.lexer.next_if(Token::Colon).is_some() {
					Some(Box::new(parser.parse_type_expression()?))
				} else {
					None
				};

				_ = parser.next_expect(Token::Eq)?;
				let value = parser.parse_expression(BindingPower::Default)?;
				let span = TextSpan::new(const_span.start, value.span.end);
				Ok(Spanned {
					inner: ImplItem::Constant {
						pub_span,
						name: Spanned {
							inner: name_symbol,
							span: name_span,
						},
						ty,
						value: Box::new(value),
						attributes: Box::new([]),
					},
					span,
				})
			}
			Some(Keyword::Func) => {
				let fn_span = parser.lexer.next().span;
				let name_span = parser.next_expect(Token::Identifier)?.span;
				let name_symbol = parser.intern_identifier(name_span);
				let type_params =
					if parser.lexer.peek().inner == Token::LeftArrow {
						parser.parse_type_params()?
					} else {
						Box::new([])
					};
				let params = SeparatedGroup {
					open_token: Token::OpenParen,
					close_token: Token::CloseParen,
					separator_token: Token::Comma,
					item_handler: Parser::parse_function_param_item,
					should_warn_missing_separator: None,
				}
				.parse(parser)?;

				let result = parser.parse_function_result()?;
				let block = Parser::parse_block_expression(parser)?;
				let method_span = TextSpan::new(fn_span.start, block.span.end);
				Ok(Spanned {
					inner: ImplItem::Function {
						pub_span,
						attributes: attrs,
						signature: FunctionSignature {
							name: Spanned {
								inner: name_symbol,
								span: name_span,
							},
							type_params,
							params: params.inner,
							result,
						},
						block: Box::new(block),
					},
					span: method_span,
				})
			}
			_ => {
				let token = parser.lexer.next();
				parser.ast.diagnostics.push(report_unexpected_token(
					parser.ast.file_id,
					token,
					Token::Identifier,
				));
				Err(())
			}
		}
	}

	fn parse_impl_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let impl_span = parser.lexer.next().span;

		let type_params = if parser.lexer.peek().inner == Token::LeftArrow {
			parser.parse_type_params()?
		} else {
			Box::new([])
		};

		let first_path = parser.parse_type_path()?;
		if let Some(Keyword::For) = parser.peek_keyword() {
			parser.lexer.next(); // consume `for`
			let target = parser.parse_type_path()?;

			let items = SeparatedGroup {
				open_token: Token::OpenBrace,
				close_token: Token::CloseBrace,
				separator_token: Token::SemiColon,
				item_handler: Parser::parse_impl_member,
				should_warn_missing_separator: Some(|item: &ImplItem| {
					!item.is_block_like()
				}),
			}
			.parse(parser)?;

			// A trait impl's members are reachable exactly where the trait
			// is, so `pub` on one decides nothing. `parse_impl_member` still
			// accepts it — it is shared with inherent impls, whose members do
			// carry visibility, and it has no way to tell which it is parsing
			// — so the qualifier is judged here, where that is known, rather
			// than by the member parser itself.
			for item in items.inner.iter() {
				let (ImplItem::Function { pub_span, .. }
				| ImplItem::Constant { pub_span, .. }
				| ImplItem::AssocType { pub_span, .. }) = &item.inner.inner;
				let Some(pub_span) = *pub_span else {
					continue;
				};
				parser.ast.diagnostics.push(
					Diagnostic::warning()
						.with_code(
							DiagnosticCode::VisibilityNotPermitted.code(),
						)
						.with_message(
							"visibility qualifiers are not permitted here",
						)
						.with_label(
							Label::primary(parser.ast.file_id, pub_span)
								.with_message("remove the qualifier"),
						)
						.with_note(
							"trait impl items always share the visibility of \
							 the trait they implement",
						),
				);
			}

			let span = TextSpan::new(impl_span.start, items.span.end);
			return Ok(Spanned {
				inner: Item::TraitImpl {
					type_params,
					items: items.inner,
					target,
					trait_name: first_path,
				},
				span,
			});
		};

		let items = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::SemiColon,
			item_handler: Parser::parse_impl_member,
			should_warn_missing_separator: Some(|item: &ImplItem| {
				!item.is_block_like()
			}),
		}
		.parse(parser)?;

		let span = TextSpan::new(impl_span.start, items.span.end);
		Ok(Spanned {
			inner: Item::InherentImpl {
				type_params,
				items: items.inner,
				target: first_path,
			},
			span,
		})
	}

	fn parse_trait_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let trait_span = parser.lexer.next().span;

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name = Spanned {
			inner: parser.intern_identifier(name_span),
			span: name_span,
		};

		let supertraits: Option<Spanned<BoundExpression>> =
			match parser.lexer.next_if(Token::Colon) {
				Some(colon) => {
					Some(parser.parse_bounds_expression(colon.span.end)?)
				}
				None => None,
			};

		let items = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::SemiColon,
			item_handler:
				|parser: &mut Parser| -> Result<Spanned<TraitItem>, ()> {
					let attributes = Parser::parse_attributes(parser)?;

					if let Some(Keyword::Pub) = parser.peek_keyword() {
						let pub_span = parser.lexer.next().span;
						parser.ast.diagnostics.push(
							Diagnostic::warning()
								.with_code(
									DiagnosticCode::VisibilityNotPermitted
										.code(),
								)
								.with_message(
									"visibility qualifiers are not permitted here",
								)
								.with_label(
									Label::primary(
										parser.ast.file_id,
										pub_span,
									)
									.with_message("remove the qualifier"),
								)
								.with_note(
									"trait items always share the visibility of their trait",
								),
						);
					}

					match parser.peek_keyword() {
						Some(Keyword::Type) => {
							let type_span = parser.lexer.next().span;
							let name_span =
								parser.next_expect(Token::Identifier)?.span;
							let name_symbol =
								parser.intern_identifier(name_span);

							let bounds: Option<Spanned<BoundExpression>> =
								match parser.lexer.next_if(Token::Colon) {
									Some(colon) => {
										Some(parser.parse_bounds_expression(
											colon.span.end,
										)?)
									}
									None => None,
								};
							let value =
								if parser.lexer.next_if(Token::Eq).is_some() {
									Some(Box::new(
										parser.parse_type_expression()?,
									))
								} else {
									None
								};
							let span = TextSpan::new(
								type_span.start,
								value
									.as_ref()
									.map(|v| v.span)
									.or_else(|| bounds.as_ref().map(|b| b.span))
									.unwrap_or(name_span)
									.end,
							);
							Ok(Spanned {
								inner: TraitItem::AssociatedType {
									name: Spanned {
										inner: name_symbol,
										span: name_span,
									},
									bounds,
									value,
									attributes,
								},
								span,
							})
						}
						Some(Keyword::Const) => {
							let const_span = parser.lexer.next().span;
							let name_span =
								parser.next_expect(Token::Identifier)?.span;
							let name_symbol =
								parser.intern_identifier(name_span);
							parser.next_expect(Token::Colon)?;
							let ty = parser.parse_type_expression()?;
							let value =
								if parser.lexer.next_if(Token::Eq).is_some() {
									Some(Box::new(parser.parse_expression(
										BindingPower::Default,
									)?))
								} else {
									None
								};
							let span = TextSpan::new(
								const_span.start,
								match &value {
									Some(value) => value.span.end,
									None => ty.span.end,
								},
							);
							Ok(Spanned {
								inner: TraitItem::Const {
									name: Spanned {
										inner: name_symbol,
										span: name_span,
									},
									ty: Box::new(ty),
									value,
									attributes,
								},
								span,
							})
						}
						Some(Keyword::Func) => {
							let signature =
								parser.parse_function_signature()?;
							let body = if parser.lexer.peek().inner
								== Token::OpenBrace
							{
								Some(Box::new(Parser::parse_block_expression(
									parser,
								)?))
							} else {
								None
							};
							let span = TextSpan::new(
								signature.span.start,
								match &body {
									Some(body) => body.span.end,
									None => signature.span.end,
								},
							);

							Ok(Spanned {
								inner: TraitItem::Function {
									attributes,
									signature: signature.inner,
									body,
								},
								span,
							})
						}
						_ => {
							let token = parser.lexer.next();
							parser.ast.diagnostics.push(
								report_unexpected_token(
									parser.ast.file_id,
									token,
									Token::Identifier,
								),
							);
							Err(())
						}
					}
				},
			should_warn_missing_separator: Some(|item: &TraitItem| {
				!item.is_block_like()
			}),
		}
		.parse(parser)?;

		let span = TextSpan::new(trait_span.start, items.span.end);
		Ok(Spanned {
			inner: Item::Trait {
				pub_span: None,
				attributes: Box::new([]),
				name,
				supertraits,
				items: items.inner,
			},
			span,
		})
	}

	fn parse_typeset_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let typeset_span = parser.lexer.next().span; // consume `typeset`

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name = Spanned {
			inner: parser.intern_identifier(name_span),
			span: name_span,
		};

		// Optional bound clause: `typeset Name: A + B { .. }` — mirrors a
		// trait's supertrait list. The `where { .. }` bindings a single bound
		// may carry are handled by `parse_bounds_expression`; the members
		// brace that follows is unambiguous because that never continues past
		// a `+`.
		let bounds: Option<Spanned<BoundExpression>> =
			match parser.lexer.next_if(Token::Colon) {
				Some(colon) => {
					Some(parser.parse_bounds_expression(colon.span.end)?)
				}
				None => None,
			};

		let members = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			item_handler: |parser: &mut Parser| {
				let path = parser.parse_type_path()?;
				let span = path.span();
				Ok(Spanned { inner: path, span })
			},
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		let span = TextSpan::new(typeset_span.start, members.span.end);
		Ok(Spanned {
			inner: Item::TypeSet {
				pub_span: None,
				attributes: Box::new([]),
				name,
				bounds,
				members: members.inner,
			},
			span,
		})
	}

	fn parse_struct_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let struct_span = parser.lexer.next().span;

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name_symbol = parser.intern_identifier(name_span);

		let type_params = if parser.lexer.peek().inner == Token::LeftArrow {
			parser.parse_type_params()?
		} else {
			Box::new([])
		};

		let name = Spanned {
			inner: name_symbol,
			span: name_span,
		};

		// Fields are written in parentheses. A braced list is the old record
		// form: reported, and read the same way so the rest still parses.
		let open_token = if parser.lexer.peek().inner == Token::OpenBrace {
			let brace = parser.lexer.peek();
			parser.ast.diagnostics.push(
				Diagnostic::error()
					.with_code(
						DiagnosticCode::StructFieldsNeedParentheses.code(),
					)
					.with_message("struct fields are written in parentheses")
					.with_label(
						Label::primary(parser.ast.file_id, brace.span)
							.with_message("expected `(`"),
					)
					.with_note("write `struct Name(field: Type, ...);`"),
			);
			Token::OpenBrace
		} else {
			Token::OpenParen
		};
		let close_token = if open_token == Token::OpenBrace {
			Token::CloseBrace
		} else {
			Token::CloseParen
		};
		let fields = SeparatedGroup {
			open_token,
			close_token,
			separator_token: Token::Comma,
			item_handler: Parser::parse_struct_field,
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		let span = TextSpan::new(struct_span.start, fields.span.end);
		Ok(Spanned {
			inner: Item::Struct {
				pub_span: None,
				attributes: Box::new([]),
				name,
				type_params,
				fields: fields.inner,
			},
			span,
		})
	}

	/// `[pub] [name:] Type`, decided on one token: a type that starts with a
	/// keyword (`func`, `_`, `Self`, ...) is never a name, and a plain identifier
	/// is a name exactly when `:` follows it; otherwise it was the first
	/// segment of the field's type, which is parsed on from there.
	fn parse_struct_field(
		parser: &mut Parser,
	) -> Result<Spanned<StructField>, ()> {
		let start = parser.lexer.peek().span.start;
		let pub_span = matches!(parser.peek_keyword(), Some(Keyword::Pub))
			.then(|| parser.lexer.next().span);
		let (binding, ty) = Parser::parse_binding_and_type(parser)?;
		Ok(Spanned {
			span: TextSpan::new(start, ty.span.end),
			inner: StructField {
				pub_span,
				binding,
				ty: Box::new(ty),
			},
		})
	}

	/// Parse `type Name = TypeExpr;` or `type Name<T> = TypeExpr;`.
	fn parse_type_alias_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let type_span = parser.lexer.next().span;

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name_symbol = parser.intern_identifier(name_span);

		let type_params = if parser.lexer.peek().inner == Token::LeftArrow {
			parser.parse_type_params()?
		} else {
			Box::new([])
		};

		// No `= TypeExpr` body — a bodiless `type Name;` declaration, only
		// legal when tagged `#[intrinsic]` (checked in TIR). Used for
		// primitives, which have no expressible type-expression right-hand
		// side of their own and are never generic, so falling back to
		// `name_span` (rather than tracking `type_params`' own end, which
		// nothing else in this parser needs either) is exact for every real
		// use of this branch.
		let body = if parser.lexer.peek().inner == Token::Eq {
			parser.lexer.next();
			Some(Box::new(parser.parse_type_expression()?))
		} else {
			None
		};

		let end = match &body {
			Some(body) => body.span.end,
			None => name_span.end,
		};
		let span = TextSpan::new(type_span.start, end);
		Ok(Spanned {
			inner: Item::TypeAlias {
				pub_span: None,
				name: Spanned {
					inner: name_symbol,
					span: name_span,
				},
				type_params,
				body,
				attributes: Box::new([]),
			},
			span,
		})
	}

	fn parse_pub_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let pub_span = parser.lexer.next().span; // consume `pub`
		let token = parser.lexer.peek();
		let handler = match parser.get_item_handler(token) {
			Ok(handler) => handler,
			Err(_) => {
				parser
					.ast
					.diagnostics
					.push(report_invalid_item(parser.ast.file_id, token.span));
				return Err(());
			}
		};

		let mut item = handler(parser)?;
		match &mut item.inner {
			Item::Function { pub_span: span, .. }
			| Item::FunctionDeclaration { pub_span: span, .. }
			| Item::PackageFunction { pub_span: span, .. }
			| Item::PackageConst { pub_span: span, .. }
			| Item::PackageType { pub_span: span, .. }
			| Item::Global { pub_span: span, .. }
			| Item::Enum { pub_span: span, .. }
			| Item::Struct { pub_span: span, .. }
			| Item::Const { pub_span: span, .. }
			| Item::Module { pub_span: span, .. }
			| Item::ModuleDeclaration { pub_span: span, .. }
			| Item::Trait { pub_span: span, .. }
			| Item::TypeSet { pub_span: span, .. }
			| Item::Memory { pub_span: span, .. }
			| Item::TypeAlias { pub_span: span, .. }
			| Item::PackageInstance { pub_span: span, .. }
			| Item::Use { pub_span: span, .. } => *span = Some(pub_span),
			Item::Export { .. }
			| Item::ExportBlock { .. }
			| Item::Import { .. }
			| Item::InherentImpl { .. }
			| Item::TraitImpl { .. } => {
				parser.ast.diagnostics.push(
					Diagnostic::warning()
						.with_code(
							DiagnosticCode::VisibilityNotPermitted.code(),
						)
						.with_message(
							"visibility qualifiers are not permitted here",
						)
						.with_label(
							Label::primary(parser.ast.file_id, pub_span)
								.with_message("remove the qualifier"),
						),
				);
			}
		}

		Ok(item)
	}

	fn parse_memory_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let memory_span = parser.lexer.next().span;

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name = Spanned {
			inner: parser.intern_identifier(name_span),
			span: name_span,
		};

		parser.next_expect(Token::Colon)?;
		let size = Box::new(parser.parse_type_expression()?);

		let span = TextSpan::new(memory_span.start, size.span.end);
		Ok(Spanned {
			inner: Item::Memory {
				pub_span: None,
				attributes: Box::new([]),
				name,
				size,
			},
			span,
		})
	}

	fn parse_global_import_declaration(
		&mut self,
	) -> Result<Spanned<ImportDeclaration>, ()> {
		let keyword_span = self.lexer.next().span;
		let token = self.lexer.peek();
		let mut_span =
			match Keyword::try_from(token.span.extract_str(self.source)) {
				Ok(Keyword::Mut) => Some(self.lexer.next().span),
				_ => None,
			};

		let name_span = self.next_expect(Token::Identifier)?.span;
		let name_symbol = self.intern_identifier(name_span);
		let name = Spanned {
			inner: name_symbol,
			span: name_span,
		};

		let _ = self.next_expect(Token::Colon)?;
		let type_expr = self.parse_type_expression()?;
		let span = TextSpan::new(keyword_span.start, type_expr.span.end);

		Ok(Spanned {
			inner: ImportDeclaration::Global {
				mut_span,
				name,
				ty: Box::new(type_expr),
			},
			span,
		})
	}

	fn parse_memory_import_declaration(
		&mut self,
	) -> Result<Spanned<ImportDeclaration>, ()> {
		let keyword_span = self.lexer.next().span;
		let name_span = self.next_expect(Token::Identifier)?.span;
		let name = Spanned {
			inner: self.intern_identifier(name_span),
			span: name_span,
		};
		let _ = self.next_expect(Token::Colon)?;
		let size = Box::new(self.parse_type_expression()?);
		let span = TextSpan::new(keyword_span.start, size.span.end);
		Ok(Spanned {
			inner: ImportDeclaration::Memory { name, size },
			span,
		})
	}

	fn parse_import_entry(
		parser: &mut Parser,
	) -> Result<Spanned<ImportEntry>, ()> {
		let pub_span = matches!(parser.peek_keyword(), Some(Keyword::Pub))
			.then(|| parser.lexer.next().span);
		let external_name = match parser.lexer.next_if(Token::String) {
			Some(string) => {
				parser.next_expect(Token::Colon)?;
				Some(string.span)
			}
			None => None,
		};
		let token = parser.lexer.peek();
		let keyword = match token.inner {
			Token::Identifier => {
				Keyword::try_from(token.span.extract_str(parser.source)).ok()
			}
			_ => None,
		};
		if let Some(span) = pub_span
			&& !matches!(keyword, Some(Keyword::Use))
		{
			parser.ast.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::VisibilityNotPermitted.code())
					.with_message(
						"visibility qualifiers are not permitted on host import declarations",
					)
					.with_label(
						SourceSpan::new(parser.ast.file_id, span)
							.primary_label()
							.with_message("remove `pub`"),
					)
					.with_note(
						"inside an import block, `pub` is supported on `use` items only",
					),
			);
		}
		// An entry with a field name starts at it.
		let entry_span = |span: TextSpan| match external_name {
			Some(name) => TextSpan::new(name.start, span.end),
			None => span,
		};
		match keyword {
			Some(Keyword::Use) => {
				// A `use` imports nothing from the host, so no field names it.
				if let Some(name) = external_name {
					parser.ast.diagnostics.push(
						report_invalid_item(parser.ast.file_id, name)
							.with_message(
								"a `use` item has no host field name",
							),
					);
				}
				let use_span = parser.lexer.next().span;
				let start = pub_span.unwrap_or(use_span).start;
				let tree = Self::parse_use_tree(parser)?;
				Ok(Spanned {
					span: TextSpan::new(start, tree.span.end),
					inner: ImportEntry::Use { pub_span, tree },
				})
			}
			Some(Keyword::Func) => {
				parser.parse_function_signature().map(|signature| Spanned {
					inner: ImportEntry::Declaration {
						external_name,
						declaration: ImportDeclaration::Function {
							signature: signature.inner,
						},
					},
					span: entry_span(signature.span),
				})
			}
			Some(Keyword::Global) => parser
				.parse_global_import_declaration()
				.map(|decl| Spanned {
					inner: ImportEntry::Declaration {
						external_name,
						declaration: decl.inner,
					},
					span: entry_span(decl.span),
				}),
			Some(Keyword::Memory) => parser
				.parse_memory_import_declaration()
				.map(|decl| Spanned {
					inner: ImportEntry::Declaration {
						external_name,
						declaration: decl.inner,
					},
					span: entry_span(decl.span),
				}),
			_ => {
				parser
					.ast
					.diagnostics
					.push(report_invalid_item(parser.ast.file_id, token.span));
				Err(())
			}
		}
	}

	fn parse_module_body_item(
		parser: &mut Parser,
	) -> Result<Spanned<Item>, ()> {
		let item_attrs = Parser::parse_attributes(parser).unwrap_or_default();
		let token = parser.lexer.peek();
		match parser.get_item_handler(token) {
			Ok(handler) => {
				let mut item = handler(parser)?;
				item.inner.set_attributes(item_attrs);
				Ok(item)
			}
			Err(()) => {
				parser
					.ast
					.diagnostics
					.push(report_invalid_item(parser.ast.file_id, token.span));
				Err(())
			}
		}
	}

	fn parse_module_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let module_span = parser.lexer.next().span; // consume `mod`

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name_symbol = parser.intern_identifier(name_span);

		if parser.lexer.peek().inner == Token::OpenBrace {
			let items = SeparatedGroup {
				open_token: Token::OpenBrace,
				close_token: Token::CloseBrace,
				separator_token: Token::SemiColon,
				item_handler: Parser::parse_module_body_item,
				should_warn_missing_separator: Some(|item: &Item| {
					!item.is_block_like()
				}),
			}
			.parse(parser)?;

			let span = TextSpan::new(module_span.start, items.span.end);
			Ok(Spanned {
				inner: Item::Module {
					pub_span: None,
					name: Spanned {
						inner: name_symbol,
						span: name_span,
					},
					items,
				},
				span,
			})
		} else {
			Ok(Spanned {
				inner: Item::ModuleDeclaration {
					pub_span: None,
					name: Spanned {
						inner: name_symbol,
						span: name_span,
					},
				},
				span: TextSpan::new(module_span.start, name_span.end),
			})
		}
	}

	fn parse_use_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let use_span = parser.lexer.next().span; // consume `use`

		// The trailing `;` is deliberately left for the caller: top-level
		// items are separated by `SemiColon` at the group level (see
		// `parse_module_item`).
		let tree = Self::parse_use_tree(parser)?;

		Ok(Spanned {
			span: TextSpan::new(use_span.start, tree.span.end),
			inner: Item::Use {
				pub_span: None,
				tree,
			},
		})
	}

	fn parse_path_ident(&mut self) -> Result<Spanned<SymbolU32>, ()> {
		let token = self.next_expect(Token::Identifier)?;
		let text = token.span.extract_str(self.source);
		let symbol = match Keyword::try_from(text) {
			Ok(Keyword::Package | Keyword::Super | Keyword::SelfLower)
			| Err(_) => self.strings.get_or_intern(text),
			Ok(kwd) => {
				self.ast.diagnostics.push(report_reserved_identifier(
					self.ast.file_id,
					token.span,
				));
				kwd.symbol()
			}
		};
		Ok(Spanned {
			inner: symbol,
			span: token.span,
		})
	}

	/// One node of a `use` tree, recursing on `::` and `{ .. }`.
	///
	/// `a::b` is left-nested as `Path{a, Path{b, ..}}` rather than collected
	/// into a flat prefix + leaf, because a `Group` can appear at any depth
	/// (`a::{b::{c, d}, e}`) — there is no single prefix to collect.
	fn parse_use_tree(parser: &mut Parser) -> Result<Spanned<UseTree>, ()> {
		let segment = parser.parse_path_ident()?;
		let token = parser.lexer.peek();
		if token.inner == Token::ColonColon {
			_ = parser.lexer.next();
			let token = parser.lexer.peek();
			match token.inner {
				Token::Star => {
					let span = TextSpan::new(
						segment.span.start,
						parser.lexer.next().span.end,
					);
					return Ok(Spanned {
						inner: UseTree::Glob { segment },
						span,
					});
				}
				Token::OpenBrace => {
					let branches = SeparatedGroup {
						open_token: Token::OpenBrace,
						close_token: Token::CloseBrace,
						separator_token: Token::Comma,
						item_handler: Self::parse_use_tree,
						should_warn_missing_separator: None,
					}
					.parse(parser)?;
					let span =
						TextSpan::new(segment.span.start, branches.span.end);
					return Ok(Spanned {
						inner: UseTree::Group { segment, branches },
						span,
					});
				}
				Token::Identifier => {
					let rest = Parser::parse_use_tree(parser)?;
					let span = TextSpan::new(segment.span.start, rest.span.end);
					return Ok(Spanned {
						inner: UseTree::Path {
							segment,
							rest: Box::new(rest),
						},
						span,
					});
				}
				_ => unreachable!(),
			}
		}

		let alias = if token.inner == Token::Identifier
			&& let Ok(Keyword::As) =
				Keyword::try_from(token.span.extract_str(parser.source))
		{
			_ = parser.lexer.next(); // consume "as"
			let alias = parser.next_expect(Token::Identifier)?;
			let alias_symbol = parser.intern_identifier(alias.span);

			Some(Spanned {
				inner: alias_symbol,
				span: alias.span,
			})
		} else {
			None
		};
		let span = TextSpan::new(
			segment.span.start,
			match alias {
				Some(alias) => alias.span.end,
				None => segment.span.end,
			},
		);
		Ok(Spanned {
			inner: UseTree::Name { segment, alias },
			span,
		})
	}

	/// `package func`, `package const`, `package type`, or a package instance.
	fn parse_crate_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let crate_span = parser.lexer.next().span;
		if parser.lexer.peek().inner == Token::String {
			return Parser::parse_package_instance(parser, crate_span);
		}
		let (item, end) = match parser.peek_keyword() {
			Some(Keyword::Func) => {
				let signature = parser.parse_function_signature()?;
				let end = if parser.lexer.peek().inner == Token::OpenBrace {
					let body = Parser::parse_block_expression(parser)?;
					parser.report_crate_member_body(body.span);
					body.span.end
				} else {
					signature.span.end
				};
				(
					Item::PackageFunction {
						pub_span: None,
						crate_span,
						attributes: Box::new([]),
						signature: signature.inner,
					},
					end,
				)
			}
			Some(Keyword::Const) => {
				parser.lexer.next();
				let name_span = parser.next_expect(Token::Identifier)?.span;
				let name = Spanned {
					inner: parser.intern_identifier(name_span),
					span: name_span,
				};
				parser.next_expect(Token::Colon)?;
				let ty = parser.parse_type_expression()?;
				let end = if parser.lexer.next_if(Token::Eq).is_some() {
					let value =
						parser.parse_expression(BindingPower::Default)?;
					parser.report_crate_member_body(value.span);
					value.span.end
				} else {
					ty.span.end
				};
				(
					Item::PackageConst {
						pub_span: None,
						crate_span,
						attributes: Box::new([]),
						name,
						ty: Box::new(ty),
					},
					end,
				)
			}
			Some(Keyword::Type) => {
				parser.lexer.next();
				let name_span = parser.next_expect(Token::Identifier)?.span;
				let name = Spanned {
					inner: parser.intern_identifier(name_span),
					span: name_span,
				};
				let type_params =
					if parser.lexer.peek().inner == Token::LeftArrow {
						parser.parse_type_params()?
					} else {
						Box::new([])
					};
				let end = if parser.lexer.next_if(Token::Eq).is_some() {
					let body = parser.parse_type_expression()?;
					parser.report_crate_member_body(body.span);
					body.span.end
				} else {
					name_span.end
				};
				(
					Item::PackageType {
						pub_span: None,
						crate_span,
						attributes: Box::new([]),
						name,
						type_params,
					},
					end,
				)
			}
			_ => {
				let token = parser.lexer.peek();
				parser
					.ast
					.diagnostics
					.push(report_invalid_item(parser.ast.file_id, token.span));
				return Err(());
			}
		};
		Ok(Spanned {
			inner: item,
			span: TextSpan::new(crate_span.start, end),
		})
	}

	fn report_crate_member_body(&mut self, span: TextSpan) {
		self.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::PackageMemberHasBody.code())
				.with_message("a package member cannot have a body")
				.with_label(
					Label::primary(self.ast.file_id, span)
						.with_message("remove this body"),
				),
		);
	}

	/// `package "name" as alias;`. The trailing `;` is left for the caller, like
	/// every other item's.
	fn parse_package_instance(
		parser: &mut Parser,
		crate_span: TextSpan,
	) -> Result<Spanned<Item>, ()> {
		let package = parser.next_expect(Token::String)?.span;

		let token = parser.lexer.peek();
		let alias = if matches!(parser.peek_keyword(), Some(Keyword::As)) {
			_ = parser.lexer.next(); // consume "as"
			let alias_span = parser.next_expect(Token::Identifier)?.span;
			Spanned {
				inner: parser.intern_identifier(alias_span),
				span: alias_span,
			}
		} else {
			parser.ast.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::MissingPackageAlias.code())
					.with_message("a package instance requires an `as` alias")
					.with_label(
						SourceSpan::new(parser.ast.file_id, token.span)
							.primary_label()
							.with_message("expected `as <name>` here"),
					),
			);
			Spanned {
				inner: Keyword::Error.symbol(),
				span: TextSpan::new(token.span.start, token.span.start),
			}
		};

		Ok(Spanned {
			span: TextSpan::new(
				crate_span.start,
				package.end.max(alias.span.end),
			),
			inner: Item::PackageInstance {
				pub_span: None,
				package,
				alias,
			},
		})
	}

	fn parse_import_block(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let import_keyword = parser.lexer.next();
		let external_span = parser.next_expect(Token::String)?.span;
		let external_name = external_span;

		let token = parser.lexer.peek();
		let internal_name = match token.inner {
			Token::Identifier
				if matches!(
					Keyword::try_from(token.span.extract_str(parser.source)),
					Ok(Keyword::As)
				) =>
			{
				_ = parser.lexer.next(); // consume "as"

				let alias_token = parser.next_expect(Token::Identifier)?;
				let alias_symbol = parser.intern_identifier(alias_token.span);

				Spanned {
					inner: alias_symbol,
					span: alias_token.span,
				}
			}
			_ => {
				parser.ast.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::MissingImportAlias.code())
						.with_message("import requires an `as` alias")
						.with_label(
							SourceSpan::new(parser.ast.file_id, token.span)
								.primary_label()
								.with_message("expected `as <name>` here"),
						),
				);

				let recovery_point = token.span.start;
				Spanned {
					inner: Keyword::Error.symbol(),
					span: TextSpan::new(recovery_point, recovery_point),
				}
			}
		};

		let items = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::SemiColon,
			item_handler: Parser::parse_import_entry,
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		let span = TextSpan::new(import_keyword.span.start, items.span.end);

		Ok(Spanned {
			inner: Item::Import {
				external_name,
				internal_name,
				items,
			},
			span,
		})
	}
}
