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
	expression: Expression,
	span: TextSpan,
	operator: Option<TextSpan>,
) -> Diagnostic<FileId> {
	let keyword = match expression {
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
				Label::secondary(file_id, span)
					.with_message(format!("the `{keyword}` ends here")),
			),
		None => diagnostic.with_label(
			Label::primary(file_id, span)
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
	Grouped(TypeId),
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
	Old(PatId),
}

pub struct Parser<'input> {
	source: &'input str,
	lexer: Lexer<'input>,
	strings: &'input mut StringInterner,
	ast: AST,
}

/// The tokens that open, separate and close a delimited list.
#[derive(Clone, Copy)]
struct Delimiters {
	open: Token,
	close: Token,
	separator: Token,
}

/// `( a, b )`
const PARENS: Delimiters = Delimiters {
	open: Token::OpenParen,
	close: Token::CloseParen,
	separator: Token::Comma,
};

/// `{ a, b }`
const BRACES: Delimiters = Delimiters {
	open: Token::OpenBrace,
	close: Token::CloseBrace,
	separator: Token::Comma,
};

/// `{ a; b }`
const BLOCK: Delimiters = Delimiters {
	open: Token::OpenBrace,
	close: Token::CloseBrace,
	separator: Token::SemiColon,
};

/// A delimited list as parsed: its items, its span, delimiters included,
/// and whether a separator follows the last item.
struct Delimited<T> {
	items: Vec<Spanned<T>>,
	span: TextSpan,
	trailing: bool,
}

/// What reads one item of a delimited list. Its `Err` means it has
/// reported, and the list skips to the next separator.
type ItemParser<T> = fn(&mut Parser) -> Result<Spanned<T>, ()>;

/// An item of a delimited list.
trait ListItem {
	/// Whether the item ends at a block-like expression's `}`, so the next
	/// one needs no separator before it, as a block-like expression is never
	/// an operand.
	fn ends_in_block(&self, _ast: &AST) -> bool {
		false
	}
}

impl ListItem for Statement {
	/// A `local` needs its `;` even when its value is block-like.
	fn ends_in_block(&self, ast: &AST) -> bool {
		match *self {
			Statement::Expression(expr) => ast.expr(expr).is_block_like(),
			Statement::LocalDefinition { .. } => false,
		}
	}
}

impl ListItem for MatchArm {
	fn ends_in_block(&self, ast: &AST) -> bool {
		ast.expr(self.body).is_block_like()
	}
}

impl ListItem for ExprId {}
impl ListItem for TypeId {}
impl ListItem for FunctionTypeParam {}
impl ListItem for NamedArgument {}
impl ListItem for PatternElement {}
impl ListItem for PatternFieldItem {}

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
			ast: AST::new(file_id),
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
			Token::Keyword(keyword) => Some(keyword),
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
	/// A delimited list: the opening token, the items, each followed by the
	/// separator (the last one optionally), and the closing token.
	fn separated<T: ListItem>(
		&mut self,
		delimiters: Delimiters,
		item: ItemParser<T>,
	) -> Result<Delimited<T>, ()> {
		let open = self.next_expect(delimiters.open)?.span;
		Ok(self.separated_after(delimiters, open, item))
	}

	/// [`Parser::separated`], with the opening token at `open` consumed
	/// already. A missing separator is reported, unless the item before it
	/// ends in a block ([`ListItem::ends_in_block`]), and the list goes on;
	/// an item that fails is skipped to the next separator.
	fn separated_after<T: ListItem>(
		&mut self,
		delimiters: Delimiters,
		open: TextSpan,
		item: ItemParser<T>,
	) -> Delimited<T> {
		let mut items: Vec<Spanned<T>> = Vec::new();
		let mut trailing = false;
		let close = loop {
			let token = self.lexer.peek();
			if token.inner == delimiters.close {
				break self.lexer.next().span;
			}
			if token.inner == Token::Eof {
				let at = items.last().map_or(open.end, |last| last.span.end);
				break self.report_unclosed(delimiters, open, at);
			}
			let parsed = match item(self) {
				Ok(parsed) => parsed,
				Err(()) => {
					self.skip_to_separator(delimiters);
					continue;
				}
			};
			let end = parsed.span.end;
			let next = self.lexer.peek().inner;
			let needs = !parsed.inner.ends_in_block(&self.ast);
			items.push(parsed);
			trailing = false;
			if next == delimiters.separator {
				self.lexer.next();
				trailing = true;
			} else if next == delimiters.close {
				break self.lexer.next().span;
			} else if next == Token::Eof {
				break self.report_unclosed(delimiters, open, end);
			} else if needs {
				self.ast.diagnostics.push(report_missing_separator(
					self.ast.file_id,
					TextSpan::new(end, end),
					delimiters.separator,
				));
			}
		};
		Delimited {
			items,
			span: TextSpan::new(open.start, close.end),
			trailing,
		}
	}

	/// After an item that failed (and reported): skips to the next
	/// separator, consumed, or to the list's end, left for the list.
	fn skip_to_separator(&mut self, delimiters: Delimiters) {
		loop {
			let token = self.lexer.peek().inner;
			if token == delimiters.separator {
				self.lexer.next();
				return;
			}
			if token == delimiters.close || token == Token::Eof {
				return;
			}
			self.lexer.next();
		}
	}

	/// A list the file ends inside: reported, and closed at `at`.
	fn report_unclosed(
		&mut self,
		delimiters: Delimiters,
		open: TextSpan,
		at: u32,
	) -> TextSpan {
		let expected_close_span = TextSpan::new(at, at);
		self.ast.diagnostics.push(report_unclosed_delimiter(
			UnclosedDelimiterDiagnostic {
				file_id: self.ast.file_id,
				close_token: delimiters.close,
				open_span: open,
				expected_close_span,
			},
		));
		expected_close_span
	}

	/// A delimited list's items, written whole into the tree, spanned by
	/// its delimiters.
	fn push_delimited<T: Listed>(
		&mut self,
		list: Delimited<T>,
	) -> Spanned<List<T>> {
		Spanned {
			inner: self
				.ast
				.push_list(list.items.into_iter().map(|item| item.inner)),
			span: list.span,
		}
	}

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
		match self.lexer.peek().inner {
			Token::Keyword(keyword) => Some(keyword),
			_ => None,
		}
	}

	/// Whether `token` may follow a `::`: any name, and `super`
	/// (`super::super::x`). Another keyword is the next statement's, after a
	/// path the user has not finished (`a::` on a line of its own, then
	/// `local ..`).
	fn is_later_segment(token: Token) -> bool {
		matches!(token, Token::Identifier | Token::Keyword(Keyword::Super))
	}

	/// A name: an identifier, or one of the keywords in `allowed`, which name
	/// something where this one is read (`self`, `Self`, `super`, `package`,
	/// `_`). Any other keyword is reported as reserved and read as the name it
	/// spells, so what follows it is still parsed.
	fn expect_name(
		&mut self,
		allowed: &[Keyword],
	) -> Result<Spanned<SymbolU32>, ()> {
		let token = self.lexer.next();
		let inner = match token.inner {
			Token::Identifier => self
				.strings
				.get_or_intern(token.span.extract_str(self.source)),
			Token::Keyword(keyword) => {
				if !allowed.contains(&keyword) {
					self.ast.diagnostics.push(report_reserved_identifier(
						self.ast.file_id,
						token.span,
					));
				}
				keyword.symbol()
			}
			_ => {
				self.ast.diagnostics.push(report_unexpected_token(
					self.ast.file_id,
					token,
					Token::Identifier,
				));
				return Err(());
			}
		};
		Ok(Spanned {
			inner,
			span: token.span,
		})
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
			if !matches!(
				name_token.inner,
				Token::Identifier | Token::Keyword(_)
			) {
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
	) -> Result<List<NamedArgument>, ()> {
		let open = parser.next_expect(Token::OpenParen)?.span;
		match parser.lexer.peek().inner {
			Token::OpenBrace => {
				Ok(parser.parse_named_call_arguments()?.0.inner)
			}
			Token::CloseParen => {
				parser.lexer.next();
				Ok(List::EMPTY)
			}
			_ => {
				let mut arguments = Vec::new();
				loop {
					let name = parser.expect_name(&[])?;
					parser.next_expect(Token::Eq)?;
					let value =
						parser.parse_expression(BindingPower::Default)?;
					arguments.push(NamedArgument {
						name,
						value: Some(value),
					});
					if parser.lexer.next_if(Token::Comma).is_none()
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
				Ok(parser.ast.push_list(arguments))
			}
		}
	}

	fn parse_function_param_item(
		parser: &mut Parser,
	) -> Result<Spanned<FunctionParam>, ()> {
		let start = parser.lexer.peek().span.start;
		let (binding, ty) = Parser::parse_binding_and_type(parser)?;
		Ok(Spanned {
			span: TextSpan::new(start, parser.ast.type_span(ty).end),
			inner: FunctionParam { binding, ty },
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
	) -> Result<(Option<Binding>, TypeId), ()> {
		let mut_span = matches!(parser.peek_keyword(), Some(Keyword::Mut))
			.then(|| parser.lexer.next().span);

		let token = parser.lexer.peek().inner;
		let named = matches!(
			token,
			Token::Identifier
				| Token::Keyword(Keyword::Underscore | Keyword::SelfLower)
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
		let underscore = token == Token::Keyword(Keyword::Underscore);
		// `self` is never a type, so it is always a name.
		let receiver = token == Token::Keyword(Keyword::SelfLower);
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
					parser.ast.push_type(
						TypeExpression::Error,
						TextSpan::new(colon.span.end, token.span.start),
					)
				}
			};
			return Ok((Some(binding), ty));
		}
		// Not followed by `:`: a type, unless it can only be a name, which is
		// then given an error type.
		match mut_span {
			// `mut _`: the type `_`, without the `mut`.
			Some(mut_span) if underscore => {
				parser.ast.diagnostics.push(report_mut_without_name(
					parser.ast.file_id,
					mut_span,
				));
				Ok((
					None,
					parser.ast.push_type(TypeExpression::Infer, name_span),
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
				parser.ast.push_type(TypeExpression::Infer, name_span),
			)),
			None if !receiver => Ok((None, parser.parse_type_path_from(name)?)),
			// `mut x`, `self` or `mut self`: a name, but no type.
			_ => {
				parser.ast.diagnostics.push(report_binding_without_type(
					parser.ast.file_id,
					name_span,
				));
				let missing = parser.ast.push_type(
					TypeExpression::Error,
					TextSpan::new(name_span.end, name_span.end),
				);
				Ok((Some(Binding::Name { mut_span, name }), missing))
			}
		}
	}

	fn parse_function_signature(
		&mut self,
	) -> Result<Spanned<FunctionSignature>, ()> {
		let fn_span = self.lexer.next();
		let name = self.expect_name(&[])?;

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
			match result {
				Some(result) => self.ast.type_span(result).end,
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
			let name = self.expect_name(&[Keyword::SelfPascal])?;

			let (param, end) = match const_span {
				// A constant's type is always written: nothing else says
				// what its values are.
				Some(const_span) => {
					self.next_expect(Token::Colon)?;
					let ty = self.parse_type_expression()?;
					let end = self.ast.type_span(ty).end;
					(
						TypeParam::Const {
							const_span,
							name,
							ty,
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
					let end = bounds.map_or(name.span.end, |bounds| {
						self.ast.bound_span(bounds).end
					});
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
	/// Parse `<Type1, 5, const SIZE>` arguments: the list, the span from the
	/// first argument to the last, and the closing `>`'s span.
	fn parse_type_args(
		&mut self,
	) -> Result<(List<TypeArgument>, TextSpan, TextSpan), ()> {
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

		let args_span = match (args.first(), args.last()) {
			(Some(&first), Some(&last)) => TextSpan::new(
				self.ast.type_argument_span(first).start,
				self.ast.type_argument_span(last).end,
			),
			_ => TextSpan::new(open_span.end, open_span.end),
		};
		Ok((self.ast.push_list(args), args_span, close_span))
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
	fn parse_const_argument(&mut self) -> Result<ConstId, ()> {
		if let Some(Keyword::Underscore) = self.peek_keyword() {
			let span = self.lexer.next().span;
			return Ok(self.ast.push_const(ConstArgument::Infer, span));
		}
		if let Token::LeftArrow | Token::DoubleLeftArrow =
			self.lexer.peek().inner
		{
			let open_span = match self.lexer.peek().inner {
				Token::LeftArrow => self.lexer.next().span,
				_ => self.lexer.split_double_left_arrow(),
			};
			let root = self.parse_bracketed_root(open_span)?;
			let path = self.parse_value_path()?;
			let span = TextSpan::new(open_span.start, path.span().end);
			let segments = self.ast.push_list(path.segments);
			let kind = match root {
				BracketedRoot::Qualified(root) => {
					ConstArgument::QualifiedPath {
						root: self.ast.push_qualified_root(root),
						segments,
					}
				}
				BracketedRoot::Grouped(inner) => {
					ConstArgument::Grouped { inner, segments }
				}
			};
			return Ok(self.ast.push_const(kind, span));
		}
		if self.at_literal() {
			let literal = self.parse_literal()?;
			return Ok(self.ast.push_const(
				ConstArgument::Literal(literal.inner),
				literal.span,
			));
		}
		let path = match Parser::parse_path(self)? {
			PathTerm::Path(path) => path,
			PathTerm::Old(_) => return Err(()),
		};
		let span = AST::path_span(&path);
		let segments = self.ast.push_list(path);
		Ok(self.ast.push_const(ConstArgument::Path(segments), span))
	}

	/// An array's length, in a type or a repeat: only a constant can be
	/// written there, so `const` says nothing.
	fn parse_length(&mut self) -> Result<ConstId, ()> {
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
	) -> Result<Spanned<List<AssocBinding>>, ()> {
		self.lexer.next(); // consume `where`
		let open_span = self.next_expect(Token::OpenBrace)?.span;
		let mut bindings: Vec<AssocBinding> = Vec::new();

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
			let name = self.expect_name(&[])?;
			let colon = self.lexer.next_if(Token::Colon);
			if colon.is_none() {
				self.next_expect(Token::Eq)?;
			}
			let (kind, end) = match (const_span, colon) {
				(None, Some(colon)) => {
					let bound = self.parse_bounds_expression(colon.span.end)?;
					let end = self.ast.bound_span(bound).end;
					(AssocBindingKind::Bound(bound), end)
				}
				(None, None) => {
					let ty = self.parse_type_expression()?;
					let end = self.ast.type_span(ty).end;
					(AssocBindingKind::Equals(ty), end)
				}
				(Some(const_span), Some(_)) => {
					let ty = self.parse_type_expression()?;
					let end = self.ast.type_span(ty).end;
					(
						AssocBindingKind::ConstRepresentable { const_span, ty },
						end,
					)
				}
				(Some(const_span), None) => {
					let value = self.parse_const_argument()?;
					let end = self.ast.const_span(value).end;
					(AssocBindingKind::ConstEquals { const_span, value }, end)
				}
			};
			self.lexer.next_if(Token::Comma);
			bindings.push(AssocBinding {
				name,
				kind,
				span: TextSpan::new(
					const_span.map_or(name.span.start, |span| span.start),
					end,
				),
			});
		};

		Ok(Spanned {
			inner: self.ast.push_list(bindings),
			span: TextSpan::new(open_span.start, close_span.end),
		})
	}

	/// Keep a result annotation whose type is not written yet, spanning the
	/// gap after `->`. Leave the body or declaration delimiter for the caller.
	fn parse_function_result(&mut self) -> Result<Option<TypeId>, ()> {
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
			self.ast.push_type(
				TypeExpression::Error,
				TextSpan::new(arrow.span.end, token.span.start),
			)
		} else {
			self.parse_type_expression()?
		};
		Ok(Some(ty))
	}

	fn parse_function_definition_item(
		parser: &mut Parser,
	) -> Result<Spanned<Item>, ()> {
		let signature = Parser::parse_function_signature(parser)?;
		let block = if parser.lexer.peek().inner == Token::OpenBrace {
			Some(parser.parse_block()?)
		} else {
			None
		};
		let span = TextSpan::new(
			signature.span.start,
			match block {
				Some(block) => parser.ast.block_span(block).end,
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
		let mut segments: Vec<PathSegment> =
			vec![PathSegment::new(first_ident)];

		while self.lexer.peek().inner == Token::ColonColon {
			self.lexer.next(); // consume `::`
			match self.lexer.peek().inner {
				Token::LeftArrow => {
					let (type_args, args_span, _) = self.parse_type_args()?;
					let last = segments.last_mut().unwrap();
					last.type_args = type_args;
					last.args_span = args_span;
				}
				Token::Identifier | Token::Keyword(_) => {
					let ident = self.parse_path_ident()?;
					segments.push(PathSegment::new(ident));
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
			let mut segment = PathSegment::new(ident);
			if self.lexer.peek().inner == Token::LeftArrow {
				let (args, args_span, _) = self.parse_type_args()?;
				segment.type_args = args;
				segment.args_span = args_span;
			}
			segments.push(segment);
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
	fn parse_bound(&mut self) -> Result<BoundId, ()> {
		let path = self.parse_type_path()?;
		let path_span = path.span();
		let segments = self.ast.push_list(path.segments);

		if self.peek_keyword() == Some(Keyword::Where) {
			let bindings = self.parse_where_bindings()?;
			let span = TextSpan::new(path_span.start, bindings.span.end);
			return Ok(self.ast.push_bound(
				BoundExpression::WithBindings {
					path: segments,
					bindings: bindings.inner,
				},
				span,
			));
		}

		Ok(self
			.ast
			.push_bound(BoundExpression::Path(segments), path_span))
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
	fn parse_bounds_expression(&mut self, after: u32) -> Result<BoundId, ()> {
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
			return Ok(self.ast.push_bound(
				BoundExpression::Error,
				TextSpan::new(after, token.span.start),
			));
		}
		let first = self.parse_bound()?;
		if self.lexer.peek().inner != Token::Plus {
			return Ok(first);
		}
		let mut bounds: Vec<BoundId> = vec![first];
		while self.lexer.next_if(Token::Plus).is_some() {
			bounds.push(self.parse_bound()?);
		}
		let span = TextSpan::new(
			self.ast.bound_span(bounds[0]).start,
			self.ast.bound_span(*bounds.last().unwrap()).end,
		);
		let bounds = self.ast.push_list(bounds);
		Ok(self
			.ast
			.push_bound(BoundExpression::BoundList(bounds), span))
	}

	fn parse_type_expression(&mut self) -> Result<TypeId, ()> {
		let token = self.lexer.peek();
		match token.inner {
			Token::Star | Token::Amper => {
				self.parse_pointer_type_expression(None)
			}
			Token::Bang => {
				let span = self.lexer.next().span;
				Ok(self.ast.push_type(TypeExpression::Never, span))
			}
			Token::Keyword(Keyword::Underscore) => {
				let span = self.lexer.next().span;
				Ok(self.ast.push_type(TypeExpression::Infer, span))
			}
			Token::Keyword(Keyword::Func) => {
				Parser::parse_function_type_expression(self)
			}
			// `Self` is valid in type paths for `Self::AssocType`, etc.;
			// `package`/`super` are path roots every namespace binds. Any
			// other keyword is reported as reserved and read as a name.
			Token::Identifier | Token::Keyword(_) => {
				let first = self.expect_name(&[
					Keyword::SelfPascal,
					Keyword::Package,
					Keyword::Super,
				])?;
				self.parse_type_path_from(first)
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
	) -> Result<TypeId, ()> {
		let mut ident = first;
		let mut segments: Vec<PathSegment> = Vec::new();
		let path_end = loop {
			let mut segment = PathSegment::new(ident);
			let mut end = ident.span.end;
			if self.lexer.peek().inner == Token::LeftArrow {
				let (args, args_span, close_span) = self.parse_type_args()?;
				segment.type_args = args;
				segment.args_span = args_span;
				end = close_span.end;
			}
			segments.push(segment);
			if self.lexer.peek().inner != Token::ColonColon {
				break end;
			}
			let colons = self.lexer.next(); // consume `::`
			let next = self.lexer.peek();
			match next.inner {
				token if Self::is_later_segment(token) => {
					ident = self.parse_path_ident()?;
				}
				Token::Star | Token::Amper => {
					// `::` consumed, followed by a pointer/slice/array sigil —
					// a memory-tagged type (`heap::*u8`), tagged with the path
					// built up so far.
					return self.parse_pointer_type_expression(Some(segments));
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

		let segments = self.ast.push_list(segments);
		Ok(self.ast.push_type(
			TypeExpression::Path(segments),
			TextSpan::new(first.span.start, path_end),
		))
	}

	/// Parse `<Type as Trait>::Item` (a trait-qualified path) or `<Type>::Item`
	/// (a bare bracketed self-type, no trait) — the opening `<` (whose span is
	/// `open_span`) has already been consumed.
	fn parse_qualified_path_type_expression(
		&mut self,
		open_span: TextSpan,
	) -> Result<TypeId, ()> {
		let root = self.parse_bracketed_root(open_span)?;
		let path = self.parse_type_path()?;
		let span = TextSpan::new(open_span.start, path.span().end);
		let segments = self.ast.push_list(path.segments);
		let kind = match root {
			BracketedRoot::Qualified(root) => TypeExpression::QualifiedPath {
				root: self.ast.push_qualified_root(root),
				segments,
			},
			BracketedRoot::Grouped(inner) => {
				TypeExpression::Grouped { inner, segments }
			}
		};
		Ok(self.ast.push_type(kind, span))
	}

	/// `<Type as Trait>::` or `<Type>::`, after its opening `<`
	/// (`open_span`), up to and including the `::`. Which one it is hinges
	/// entirely on whether `as` follows the type.
	fn parse_bracketed_root(
		&mut self,
		open_span: TextSpan,
	) -> Result<BracketedRoot, ()> {
		let self_type = self.parse_type_expression()?;
		let root = if matches!(self.peek_keyword(), Some(Keyword::As)) {
			self.lexer.next(); // consume `as`
			let trait_path = self.parse_type_path()?;
			let close_span = self.expect_close_angle(open_span);
			BracketedRoot::Qualified(QualifiedPathRoot {
				self_type,
				trait_path: self.ast.push_list(trait_path.segments),
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
		memory: Option<Vec<PathSegment>>,
	) -> Result<TypeId, ()> {
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
		let memory = memory.map(|segments| self.ast.push_list(segments));

		let inner = self.parse_type_expression()?;
		let span = TextSpan::new(start, self.ast.type_span(inner).end);
		Ok(self.ast.push_type(
			TypeExpression::Pointer {
				ownership,
				memory,
				inner,
			},
			span,
		))
	}

	/// Parses a slice or an array, `[T]` or `[T; N]`, from its `[` (not yet
	/// consumed).
	fn parse_slice_type_expression(&mut self) -> Result<TypeId, ()> {
		let open = self.lexer.next().span; // consume `[`
		let inner = self.parse_type_expression()?;
		let next = self.lexer.next();
		match next.inner {
			Token::CloseBracket => Ok(self.ast.push_type(
				TypeExpression::Slice { inner },
				TextSpan::new(open.start, next.span.end),
			)),
			Token::SemiColon => {
				let length = self.parse_length()?;
				let close_span = self.next_expect(Token::CloseBracket)?.span;
				Ok(self.ast.push_type(
					TypeExpression::Array { inner, length },
					TextSpan::new(open.start, close_span.end),
				))
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

	/// A type as a list item: its id, spanned as the type is.
	fn parse_type_item(parser: &mut Parser) -> Result<Spanned<TypeId>, ()> {
		let ty = parser.parse_type_expression()?;
		Ok(Spanned {
			inner: ty,
			span: parser.ast.type_span(ty),
		})
	}

	fn parse_tuple_or_paren_type_expression(&mut self) -> Result<TypeId, ()> {
		let elements = self.separated(PARENS, Parser::parse_type_item)?;
		let elements = self.push_delimited(elements);
		Ok(self.ast.push_type(
			TypeExpression::Tuple {
				elements: elements.inner,
			},
			elements.span,
		))
	}

	fn parse_function_type_param(
		parser: &mut Parser,
	) -> Result<Spanned<FunctionTypeParam>, ()> {
		let ty = parser.parse_type_expression()?;
		// A single-segment path followed by `:` is a named parameter (`self: T`).
		let single_ident = match parser.ast.ty(ty) {
			TypeExpression::Path(segments) => match parser.ast.list(segments) {
				[segment] if segment.type_args.is_empty() => {
					Some(segment.ident)
				}
				_ => None,
			},
			_ => None,
		};
		let (name, ty) = match single_ident {
			Some(name) if parser.lexer.next_if(Token::Colon).is_some() => {
				(Some(name), parser.parse_type_expression()?)
			}
			_ => (None, ty),
		};

		let ty_span = parser.ast.type_span(ty);
		let span =
			TextSpan::new(name.map_or(ty_span, |n| n.span).start, ty_span.end);
		Ok(Spanned {
			inner: FunctionTypeParam { name, ty, span },
			span,
		})
	}

	fn parse_function_type_expression(&mut self) -> Result<TypeId, ()> {
		let func_keyword = self.lexer.next();
		let params =
			self.separated(PARENS, Parser::parse_function_type_param)?;
		let params = self.push_delimited(params);
		let list = params.inner;

		let result = match self.lexer.next_if(Token::MinusRightArrow) {
			Some(_) => Some(Parser::parse_type_expression(self)?),
			None => None,
		};
		let end = result
			.map_or(params.span.end, |result| self.ast.type_span(result).end);
		Ok(self.ast.push_type(
			TypeExpression::Function {
				params: list,
				result,
			},
			TextSpan::new(func_keyword.span.start, end),
		))
	}

	/// Whether `token` starts an expression: what [`Parser::parse_prefix`]
	/// reads. Any word does, a keyword included (`local` read where an
	/// expression should be is reported as a reserved name, as a path).
	fn starts_expression(token: Token) -> bool {
		matches!(
			token,
			Token::Identifier
				| Token::Keyword(_)
				| Token::Int | Token::Float
				| Token::String
				| Token::Char
				| Token::OpenBrace
				| Token::OpenParen
				| Token::OpenBracket
				| Token::LeftArrow
				| Token::Minus
				| Token::Bang
				| Token::Caret
		)
	}

	/// The expression an operand starts with, before any operator: a
	/// literal, a path, a prefix operator, a bracketed list or a block-like
	/// expression. The caller has checked [`Parser::starts_expression`].
	fn parse_prefix(&mut self) -> Result<ExprId, ()> {
		match self.lexer.peek().inner {
			Token::Keyword(Keyword::Return) => self.parse_return_expression(),
			Token::Keyword(Keyword::If) => self.parse_if_else_expression(),
			Token::Keyword(Keyword::Loop) => self.parse_loop_expression(),
			Token::Keyword(Keyword::Match) => self.parse_match_expression(),
			Token::Keyword(Keyword::Break) => self.parse_break_expression(),
			Token::Keyword(Keyword::Continue) => {
				self.parse_continue_expression()
			}
			Token::Keyword(Keyword::Underscore) => {
				self.parse_placeholder_expression()
			}
			Token::Keyword(Keyword::Block) => {
				self.parse_keyword_block_expression()
			}
			Token::Identifier | Token::Keyword(_) => {
				self.parse_path_expression()
			}
			Token::Int => self.parse_int_expression(),
			Token::Float => self.parse_float_expression(),
			Token::String => {
				let span = self.lexer.next().span;
				Ok(self.ast.push_expr(Expression::String, span))
			}
			Token::Char => {
				let span = self.lexer.next().span;
				Ok(self.ast.push_expr(Expression::Char, span))
			}
			Token::OpenBrace => self.parse_bare_block_expression(),
			Token::OpenParen => self.parse_tuple_expression(),
			Token::OpenBracket => self.parse_array_expression(),
			Token::LeftArrow => self.parse_qualified_path_expression(),
			Token::Minus | Token::Bang | Token::Caret => {
				self.parse_unary_expression()
			}
			_ => unreachable!("the caller checked `starts_expression`"),
		}
	}

	/// How tightly `token` binds the operand before it, if it continues an
	/// expression: a binary operator, or a postfix call, index, `.` or `::`.
	fn infix_power(token: Token) -> Option<BindingPower> {
		Some(match token {
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
			| Token::DoubleRightArrowEq => BindingPower::Assignment,
			Token::DoubleVbar => BindingPower::LogicalOr,
			Token::DoubleAmper => BindingPower::LogicalAnd,
			Token::Vbar => BindingPower::BitwiseOr,
			Token::Caret => BindingPower::BitwiseXor,
			Token::Amper => BindingPower::BitwiseAnd,
			Token::EqEq
			| Token::BangEq
			| Token::LeftArrow
			| Token::LeftArrowEq
			| Token::RightArrow
			| Token::RightArrowEq => BindingPower::Comparison,
			Token::DoubleLeftArrow | Token::DoubleRightArrow => {
				BindingPower::BitwiseShift
			}
			Token::Plus | Token::Minus => BindingPower::Additive,
			Token::Star | Token::Slash | Token::Percent => {
				BindingPower::Multiplicative
			}
			Token::OpenParen | Token::OpenBracket => BindingPower::Postfix,
			Token::Dot | Token::ColonColon => BindingPower::Member,
			_ => return None,
		})
	}

	/// An expression. Like every parse function, it has reported whatever
	/// made it fail.
	fn parse_expression(
		&mut self,
		limit_bp: BindingPower,
	) -> Result<ExprId, ()> {
		let token = self.lexer.peek();
		if !Self::starts_expression(token.inner) {
			self.ast
				.diagnostics
				.push(report_expected_expression(self.ast.file_id, token));
			return Err(());
		}
		let mut left = self.parse_prefix()?;

		// A block-like expression is never an operand: it fills an
		// expression position whole and ends at its closing `}`, so no
		// operator continues it and none takes it without parentheses
		// (`(if c { f } else { g })(x)`). An assignment's value is a whole
		// position too, as a `local`'s initializer is (`x = if c { 1 } else
		// { 2 }`): only an operator binding tighter takes an operand. In a
		// statement list, what follows is the next statement: `if c { .. }
		// (a, b)` is two. Once that is reported, the operators are read as
		// before, so the caller sees one diagnostic and a whole expression.
		let kind = self.ast.expr(left);
		if kind.is_block_like() {
			let token = self.lexer.peek();
			let span = self.ast.expr_span(left);
			if limit_bp > BindingPower::Assignment {
				self.ast.diagnostics.push(report_block_like_operand(
					self.ast.file_id,
					kind,
					span,
					None,
				));
			} else if Self::infix_power(token.inner)
				.is_some_and(|bp| bp > limit_bp)
				&& !Self::starts_expression(token.inner)
			{
				// A token that can only continue this expression; one that
				// can also start one (`(`, `[`, `-`) starts whatever comes
				// next, and one that binds no tighter than `limit_bp`
				// continues an enclosing expression instead.
				self.ast.diagnostics.push(report_block_like_operand(
					self.ast.file_id,
					kind,
					span,
					Some(token.span),
				));
			} else {
				return Ok(left);
			}
		}

		loop {
			let token = self.lexer.peek().inner;
			let power = match Self::infix_power(token) {
				Some(power) if power > limit_bp => power,
				_ => break,
			};
			left = match token {
				Token::OpenParen => self.parse_call_expression(left)?,
				Token::OpenBracket => self.parse_index_expression(left)?,
				Token::Dot => self.parse_object_access_expression(left)?,
				Token::ColonColon => {
					self.parse_type_application_expression(left)?
				}
				_ => self.parse_binary_expression(left, power)?,
			};
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
	fn parse_qualified_path_expression(&mut self) -> Result<ExprId, ()> {
		let open_span = self.lexer.next().span; // consume `<`
		let root = self.parse_bracketed_root(open_span)?;
		let path = self.parse_value_path()?;
		let span = TextSpan::new(open_span.start, path.span().end);
		let segments = self.ast.push_list(path.segments);
		let kind = match root {
			BracketedRoot::Qualified(root) => Expression::QualifiedPath {
				root: self.ast.push_qualified_root(root),
				segments,
			},
			BracketedRoot::Grouped(inner) => {
				Expression::Grouped { inner, segments }
			}
		};
		Ok(self.ast.push_expr(kind, span))
	}

	fn parse_path_expression(&mut self) -> Result<ExprId, ()> {
		let first = self.expect_name(&[
			Keyword::SelfLower,
			Keyword::SelfPascal,
			Keyword::Underscore,
			Keyword::Package,
			Keyword::Super,
		])?;

		// Start the path with the first segment (no type args yet).
		let mut segments: Vec<PathSegment> = vec![PathSegment::new(first)];

		while self.lexer.peek().inner == Token::ColonColon {
			let colons = self.lexer.next(); // consume `::`
			let next = self.lexer.peek();
			match next.inner {
				// `::<T, U>` — turbofish type args for the last segment
				Token::LeftArrow => {
					let (type_args, args_span, _) = self.parse_type_args()?;
					let last = segments.last_mut().unwrap();
					last.type_args = type_args;
					last.args_span = args_span;
					// Loop continues: next `::` starts a new segment.
				}
				// `::{ ... }` — the old struct literal
				Token::OpenBrace => {
					return self.parse_struct_literal_as_call(&segments);
				}
				// `::ident` — next path segment
				token if Self::is_later_segment(token) => {
					segments.push(PathSegment::new(
						self.expect_name(&[Keyword::Super])?,
					));
				}
				// Anything else after `::` is a missing segment: reported,
				// and kept, so the path up to it is still resolved.
				_ => {
					let bad = self.lexer.peek();
					self.ast.diagnostics.push(report_invalid_namespace(
						self.ast.file_id,
						bad.span,
					));
					segments.push(PathSegment::missing(colons.span.end));
					break;
				}
			}
		}

		let span = AST::path_span(&segments);
		let path = self.ast.push_list(segments);
		Ok(self.ast.push_expr(Expression::Path(path), span))
	}

	/// A named list and the `)` after it, the `(` consumed. The list is the
	/// call's only argument: anything else before `)` is reported, and read
	/// for recovery. Returns the arguments and where the call ends.
	fn parse_named_call_arguments(
		&mut self,
	) -> Result<(Spanned<List<NamedArgument>>, u32), ()> {
		let named = self.parse_named_arguments()?;
		if self.lexer.peek().inner != Token::CloseParen {
			let at = self.lexer.peek().span;
			self.ast
				.diagnostics
				.push(report_mixed_call_arguments(self.ast.file_id, at));
			while self.lexer.next_if(Token::Comma).is_some()
				&& self.lexer.peek().inner != Token::CloseParen
			{
				self.parse_expression(BindingPower::Default)?;
			}
		}
		let close_span = self.next_expect(Token::CloseParen)?.span;
		Ok((named, close_span.end))
	}

	/// One positional argument. A named list here follows other arguments,
	/// which is a mix: reported, and read so the call still parses.
	fn parse_positional_argument(
		parser: &mut Parser,
	) -> Result<Spanned<ExprId>, ()> {
		if parser.lexer.peek().inner != Token::OpenBrace {
			return Parser::parse_element(parser);
		}
		let named = parser.parse_named_arguments()?;
		parser
			.ast
			.diagnostics
			.push(report_mixed_call_arguments(parser.ast.file_id, named.span));
		Ok(Spanned {
			inner: parser.ast.push_expr(Expression::Error, named.span),
			span: named.span,
		})
	}

	/// `{ name: expr, name, .. }`, braces included.
	fn parse_named_arguments(
		&mut self,
	) -> Result<Spanned<List<NamedArgument>>, ()> {
		let named = self.separated(BRACES, Parser::parse_named_argument)?;
		Ok(self.push_delimited(named))
	}

	/// `name: expr`, or the shorthand `name` for `name: name`. `self` is a
	/// name here, a method's receiver (`T::m({ self: x })`). A value not
	/// written yet after the `:` is reported and kept as an error node
	/// spanning the gap up to the next token, as a `local`'s is, so the name
	/// is still read.
	fn parse_named_argument(
		parser: &mut Parser,
	) -> Result<Spanned<NamedArgument>, ()> {
		let name = parser.expect_name(&[Keyword::SelfLower])?;
		let Some(colon) = parser.lexer.next_if(Token::Colon) else {
			return Ok(Spanned {
				inner: NamedArgument { name, value: None },
				span: name.span,
			});
		};
		let token = parser.lexer.peek();
		let value = if Self::starts_expression(token.inner) {
			parser.parse_expression(BindingPower::Default)?
		} else {
			parser
				.ast
				.diagnostics
				.push(report_expected_expression(parser.ast.file_id, token));
			parser.ast.push_expr(
				Expression::Error,
				TextSpan::new(colon.span.end, token.span.start),
			)
		};
		Ok(Spanned {
			inner: NamedArgument {
				name,
				value: Some(value),
			},
			span: TextSpan::new(
				name.span.start,
				parser.ast.expr_span(value).end,
			),
		})
	}

	/// `Path::{ ... }`, the old struct literal, with `::` consumed and `{`
	/// next. A struct is constructed by a call now: reported, and read as the
	/// named call `Path({ ... })` it stands for.
	fn parse_struct_literal_as_call(
		&mut self,
		path: &[PathSegment],
	) -> Result<ExprId, ()> {
		let path_span = AST::path_span(path);
		let path = self.ast.push_list(path.iter().copied());
		let callee = self.ast.push_expr(Expression::Path(path), path_span);
		let named = self.parse_named_arguments()?;
		let span = TextSpan::new(path_span.start, named.span.end);
		self.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::StructLiteralIsACall.code())
				.with_message("a struct is constructed by a call")
				.with_label(Label::primary(self.ast.file_id, span))
				.with_note("write `Name({ field: value, ... })`"),
		);
		Ok(self.ast.push_expr(
			Expression::NamedCall {
				callee,
				arguments: named.inner,
				braces: named.span,
			},
			span,
		))
	}

	fn parse_object_access_expression(
		&mut self,
		object: ExprId,
	) -> Result<ExprId, ()> {
		let start = self.ast.expr_span(object).start;
		let dot = self.lexer.next(); // consume the dot
		let token = self.lexer.peek();
		let span = TextSpan::new(start, token.span.end);
		let (kind, span) = match token.inner {
			Token::Star => {
				self.lexer.next();
				(Expression::Deref { pointer: object }, span)
			}
			Token::Amper => {
				self.lexer.next();
				(Expression::AddressOf { value: object }, span)
			}
			// A keyword is never a member: `x.` on a line of its own is
			// followed by the next statement's `local`, `return`, ...
			Token::Identifier => {
				self.lexer.next();
				let member = self.ast.push_segment(PathSegment::new(Spanned {
					inner: self
						.strings
						.get_or_intern(token.span.extract_str(self.source)),
					span: token.span,
				}));
				(Expression::ObjectAccess { object, member }, span)
			}
			// `x.` with no member: reported, and kept as an access of a
			// missing one, so the object is still checked, and the token
			// after the dot is left to close or start whatever it does.
			_ => {
				self.ast.diagnostics.push(report_missing_member(
					self.ast.file_id,
					token,
					self.source,
				));
				let member =
					self.ast.push_segment(PathSegment::missing(dot.span.end));
				(
					Expression::ObjectAccess { object, member },
					TextSpan::new(start, dot.span.end),
				)
			}
		};
		Ok(self.ast.push_expr(kind, span))
	}

	fn parse_binary_expression(
		&mut self,
		left: ExprId,
		bp: BindingPower,
	) -> Result<ExprId, ()> {
		let operator_token = self.lexer.next();
		let operator = match BinaryOp::try_from(operator_token.inner) {
			Ok(operator) => operator,
			Err(_) => unreachable!(),
		};

		let token = self.lexer.peek();
		if !Self::starts_expression(token.inner) {
			self.ast
				.diagnostics
				.push(report_incomplete_binary_expression(
					self.ast.file_id,
					operator_token.span,
				));
			return Err(());
		}
		let right = self.parse_expression(bp)?;

		// Comparisons and assignments do not associate: neither grouping of
		// `a < b < c` or `a = b = c` means anything (a comparison is a `Bool`,
		// an assignment `()`), so a chain is an error rather than a grouping.
		// Operators parse left-grouped, so a chain is always in `left`;
		// written parentheses make a tuple, which is no chain.
		if let Expression::Binary {
			operator: left_operator,
			..
		} = self.ast.expr(left)
			&& BindingPower::from(left_operator) == bp
		{
			let left_operator = self.ast.operator_span(left);
			match bp {
				BindingPower::Comparison => {
					self.ast.diagnostics.push(report_chained_comparisons(
						self.ast.file_id,
						left_operator,
						operator_token.span,
					));
				}
				BindingPower::Assignment => {
					self.ast.diagnostics.push(report_chained_assignments(
						self.ast.file_id,
						left_operator,
						operator_token.span,
					));
				}
				_ => {}
			}
		}

		let span = TextSpan::new(
			self.ast.expr_span(left).start,
			self.ast.expr_span(right).end,
		);
		Ok(self.ast.push_expr(
			Expression::Binary {
				operator,
				operator_start: operator_token.span.start,
				left,
				right,
			},
			span,
		))
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

	fn parse_int_expression(&mut self) -> Result<ExprId, ()> {
		let token = self.lexer.next();
		debug_assert!(matches!(token.inner, Token::Int));
		let value = self.integer_literal(token.span);
		Ok(self.ast.push_expr(Expression::Int { value }, token.span))
	}

	fn parse_float_expression(&mut self) -> Result<ExprId, ()> {
		let token = self.lexer.next();
		debug_assert!(matches!(token.inner, Token::Float));

		// Syntactic validity only — `f64::from_str` and `f32::from_str` accept
		// the identical grammar, so this rejects a malformed token (`1e`,
		// `1e+`) without committing to a value. The literal's actual value is
		// preserved exactly in TIR. `coerce_float` checks representability;
		// evaluation and lowering convert at the concrete target width.
		if token.span.extract_str(self.source).parse::<f64>().is_err() {
			self.ast.diagnostics.push(report_invalid_float_literal(
				self.ast.file_id,
				token.span,
			));
		}
		Ok(self.ast.push_expr(Expression::Float, token.span))
	}

	fn parse_return_expression(&mut self) -> Result<ExprId, ()> {
		let return_span = self.lexer.next().span;
		let token = self.lexer.peek();
		if !Self::starts_expression(token.inner) {
			return Ok(self
				.ast
				.push_expr(Expression::Return { value: None }, return_span));
		}
		let value = self.parse_expression(BindingPower::Default)?;
		let span =
			TextSpan::new(return_span.start, self.ast.expr_span(value).end);
		Ok(self
			.ast
			.push_expr(Expression::Return { value: Some(value) }, span))
	}

	fn parse_break_expression(&mut self) -> Result<ExprId, ()> {
		let break_keyword = self.lexer.next();
		let label = self.parse_label();
		let token = self.lexer.peek();
		let value = if Self::starts_expression(token.inner) {
			Some(self.parse_expression(BindingPower::Default)?)
		} else {
			None
		};
		let end = match (label, value) {
			(_, Some(value)) => self.ast.expr_span(value).end,
			(Some(label), None) => label.span.end,
			(None, None) => break_keyword.span.end,
		};
		Ok(self.ast.push_expr(
			Expression::Break { label, value },
			TextSpan::new(break_keyword.span.start, end),
		))
	}

	fn parse_continue_expression(&mut self) -> Result<ExprId, ()> {
		let continue_keyword = self.lexer.next();
		let label = self.parse_label();
		let end =
			label.map_or(continue_keyword.span.end, |label| label.span.end);
		Ok(self.ast.push_expr(
			Expression::Continue { label },
			TextSpan::new(continue_keyword.span.start, end),
		))
	}

	fn parse_tuple_expression(&mut self) -> Result<ExprId, ()> {
		let elements = self.separated(PARENS, Parser::parse_element)?;
		let elements = self.push_delimited(elements);
		Ok(self.ast.push_expr(
			Expression::Tuple {
				elements: elements.inner,
			},
			elements.span,
		))
	}

	/// An element of a parenthesized list: an expression, or `value: Type`.
	fn parse_element(parser: &mut Parser) -> Result<Spanned<ExprId>, ()> {
		let value = parser.parse_expression(BindingPower::Default)?;
		let start = parser.ast.expr_span(value).start;
		let (id, end) = if parser.lexer.next_if(Token::Colon).is_none() {
			(value, parser.ast.expr_span(value).end)
		} else {
			let ty = parser.parse_type_expression()?;
			let span = TextSpan::new(start, parser.ast.type_span(ty).end);
			let id = parser
				.ast
				.push_expr(Expression::Ascription { value, ty }, span);
			(id, span.end)
		};
		Ok(Spanned {
			inner: id,
			span: TextSpan::new(start, end),
		})
	}

	fn parse_unary_expression(&mut self) -> Result<ExprId, ()> {
		let operator_token = self.lexer.next();
		let operator = match UnaryOp::try_from(operator_token.inner) {
			Ok(operator) => operator,
			Err(_) => unreachable!(),
		};

		let token = self.lexer.peek();
		if !Self::starts_expression(token.inner) {
			self.ast
				.diagnostics
				.push(report_incomplete_unary_expression(
					self.ast.file_id,
					operator_token.span,
				));
			return Err(());
		}
		let operand = self.parse_expression(BindingPower::Unary)?;
		let span = TextSpan::new(
			operator_token.span.start,
			self.ast.expr_span(operand).end,
		);
		Ok(self
			.ast
			.push_expr(Expression::Unary { operator, operand }, span))
	}

	/// `block :label { ... }`: a plain block in expression position. Blocks
	/// that belong to a construct (`if`, `loop`, a match arm, a function body)
	/// are parsed by it directly and need no keyword.
	fn parse_keyword_block_expression(&mut self) -> Result<ExprId, ()> {
		let keyword_span = self.lexer.next().span;
		let label = self.parse_label();
		let block = self.parse_block()?;
		let span =
			TextSpan::new(keyword_span.start, self.ast.block_span(block).end);
		Ok(self.ast.push_expr(Expression::Block { label, block }, span))
	}

	/// `:label` after `block`, a loop's keyword, `break` or `continue`. A `:`
	/// with no name after it is reported and keeps the error symbol at the
	/// empty span right after it, as a missing member does
	/// (`PathSegment::missing`); the token after it, a keyword included, is
	/// left for whatever it starts.
	fn parse_label(&mut self) -> Option<Spanned<SymbolU32>> {
		let colon = self.lexer.next_if(Token::Colon)?;
		let token = self.lexer.peek();
		if token.inner != Token::Identifier {
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
	fn parse_bare_block_expression(&mut self) -> Result<ExprId, ()> {
		let brace_span = self.lexer.peek().span;
		self.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::BlockNeedsKeyword.code())
				.with_message("a block expression is written `block { ... }`")
				.with_label(
					Label::primary(self.ast.file_id, brace_span)
						.with_message("expected `block` before `{`"),
				),
		);
		self.parse_block_expression()
	}

	/// A block where an expression is expected (an `else` branch, a match
	/// arm's body), with no keyword and no label.
	fn parse_block_expression(&mut self) -> Result<ExprId, ()> {
		let block = self.parse_block()?;
		let span = self.ast.block_span(block);
		Ok(self
			.ast
			.push_expr(Expression::Block { label: None, block }, span))
	}

	/// `{ statement; ... tail }`: the statements, and the expression written
	/// last without a `;`, which is the block's value. A block-like
	/// statement needs no `;` before the next one.
	fn parse_block(&mut self) -> Result<BlockId, ()> {
		let open = self.next_expect(Token::OpenBrace)?.span;
		let mut list =
			self.separated_after(BLOCK, open, Parser::parse_statement);
		let tail = match list.items.last() {
			Some(&Spanned {
				inner: Statement::Expression(expr),
				..
			}) if !list.trailing => {
				list.items.pop();
				Some(expr)
			}
			_ => None,
		};
		let statements: Vec<StmtId> = list
			.items
			.into_iter()
			.map(|statement| {
				self.ast.push_statement(statement.inner, statement.span)
			})
			.collect();
		let statements = self.ast.push_list(statements);
		Ok(self.ast.push_block(Block { statements, tail }, list.span))
	}

	/// One statement in a block: a `local`, or an expression.
	fn parse_statement(parser: &mut Parser) -> Result<Spanned<Statement>, ()> {
		if let Some(Keyword::Local) = parser.peek_keyword() {
			return Parser::parse_local_definition_statement(parser);
		}
		let expr = parser.parse_expression(BindingPower::Default)?;
		Ok(Spanned {
			inner: Statement::Expression(expr),
			span: parser.ast.expr_span(expr),
		})
	}

	fn parse_loop_expression(&mut self) -> Result<ExprId, ()> {
		let loop_keyword = self.lexer.next();
		let label = self.parse_label();
		let block = self.parse_block()?;
		let span = TextSpan::new(
			loop_keyword.span.start,
			self.ast.block_span(block).end,
		);
		Ok(self.ast.push_expr(Expression::Loop { label, block }, span))
	}

	fn parse_if_else_expression(&mut self) -> Result<ExprId, ()> {
		let if_keyword = self.lexer.next();
		let label = self.parse_label();
		let condition = self.parse_expression(BindingPower::Default)?;
		let then_block = self.parse_block()?;
		let else_block = match self.peek_keyword() {
			Some(Keyword::Else) => {
				let _ = self.lexer.next();
				// `else if` nests an `if` in the else position; `else { .. }`
				// stays a plain block. TIR's `IfElse` branch and the checker's
				// `build_branch` already describe both shapes.
				if matches!(self.peek_keyword(), Some(Keyword::If)) {
					Some(self.parse_if_else_expression()?)
				} else {
					Some(self.parse_block_expression()?)
				}
			}
			_ => None,
		};
		let end = match else_block {
			Some(else_block) => self.ast.expr_span(else_block).end,
			None => self.ast.block_span(then_block).end,
		};
		let span = TextSpan::new(if_keyword.span.start, end);
		let if_else = self.ast.push_expr(
			Expression::IfElse {
				condition,
				then_block,
				else_block,
			},
			span,
		);
		let Some(label) = label else {
			return Ok(if_else);
		};
		// Read as the block it would be written in, so a `break` to the label
		// still finds it.
		self.ast.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::LabelOnIf.code())
				.with_message("an `if` cannot be labelled")
				.with_label(
					Label::primary(self.ast.file_id, label.span)
						.with_message("a label names a `block` or a `loop`"),
				)
				.with_note(
					"write it on a block around the `if`: `block :label { if .. }`",
				),
		);
		// No braces are written: the block is the `if` alone.
		let block = self.ast.push_block(
			Block {
				statements: List::EMPTY,
				tail: Some(if_else),
			},
			span,
		);
		Ok(self.ast.push_expr(
			Expression::Block {
				label: Some(label),
				block,
			},
			span,
		))
	}

	fn parse_match_expression(&mut self) -> Result<ExprId, ()> {
		let match_keyword = self.lexer.next();
		let scrutinee = self.parse_expression(BindingPower::Default)?;
		let open = self.next_expect(Token::OpenBrace)?.span;
		// A block body is self-delimiting, so its trailing comma stays
		// optional, exactly as a block-like statement's separator does. Any
		// other body needs a comma before the next arm.
		let arms = self.separated_after(BRACES, open, Parser::parse_match_arm);
		let arms = self.push_delimited(arms);
		let span = TextSpan::new(match_keyword.span.start, arms.span.end);
		Ok(self.ast.push_expr(
			Expression::Match {
				scrutinee,
				arms: arms.inner,
			},
			span,
		))
	}

	/// `pattern => { .. }` or `pattern => expr`.
	fn parse_match_arm(parser: &mut Parser) -> Result<Spanned<MatchArm>, ()> {
		let pattern = Parser::parse_pattern(parser)?;
		parser.next_expect(Token::FatArrow)?;
		// A braced body is a block; a bare expression must be separated by a
		// comma like a statement.
		let body = if parser.lexer.peek().inner == Token::OpenBrace {
			parser.parse_block_expression()?
		} else {
			parser.parse_expression(BindingPower::Default)?
		};
		Ok(Spanned {
			inner: MatchArm { pattern, body },
			span: TextSpan::new(
				parser.ast.pattern_span(pattern).start,
				parser.ast.expr_span(body).end,
			),
		})
	}

	/// Handles `expr::<T, U>` when `expr` is not a path (paths take their
	/// type arguments in `parse_path_expression`). Only a member
	/// (`obj.method::<T>`) accepts them; they join its segment, and the
	/// access, still the operand being read, ends after them.
	fn parse_type_application_expression(
		&mut self,
		left: ExprId,
	) -> Result<ExprId, ()> {
		let colons = self.lexer.next(); // consume `::`

		if self.lexer.peek().inner == Token::LeftArrow {
			let (args, args_span, close_span) = self.parse_type_args()?;
			return match self.ast.expr(left) {
				Expression::ObjectAccess { member, .. }
					if self.ast.segment(member).type_args.is_empty() =>
				{
					let segment = &mut self.ast.segments[usize::from(member)];
					segment.type_args = args;
					segment.args_span = args_span;
					self.ast.exprs.spans[usize::from(left)].end =
						close_span.end;
					Ok(left)
				}
				_ => {
					self.ast.diagnostics.push(report_type_args_not_allowed(
						self.ast.file_id,
						TextSpan::new(colons.span.start, close_span.end),
					));
					Err(())
				}
			};
		}

		let bad = self.lexer.peek();
		self.ast
			.diagnostics
			.push(report_invalid_namespace(self.ast.file_id, bad.span));
		Err(())
	}

	/// `callee(a, b)` or `callee({ x: a, y })`, decided on the token after
	/// `(`: `{` opens a named list (a plain block is spelled `block { }`, so
	/// nothing else starts with `{` here), anything else a positional one.
	/// A callee that names a method on an object makes it a method call.
	fn parse_call_expression(&mut self, callee: ExprId) -> Result<ExprId, ()> {
		let start = self.ast.expr_span(callee).start;
		let open = self.next_expect(Token::OpenParen)?.span;
		if self.lexer.peek().inner == Token::OpenBrace {
			let (arguments, end) = self.parse_named_call_arguments()?;
			return Ok(self.ast.push_expr(
				Expression::NamedCall {
					callee,
					arguments: arguments.inner,
					braces: arguments.span,
				},
				TextSpan::new(start, end),
			));
		}
		let arguments = self.separated_after(
			PARENS,
			open,
			Parser::parse_positional_argument,
		);
		let arguments = self.push_delimited(arguments);
		Ok(self.ast.push_expr(
			Expression::Call {
				callee,
				arguments: arguments.inner,
				open: open.start,
			},
			TextSpan::new(start, arguments.span.end),
		))
	}

	fn parse_array_expression(&mut self) -> Result<ExprId, ()> {
		let open_span = self.next_expect(Token::OpenBracket)?.span;

		if let Some(close) = self.lexer.next_if(Token::CloseBracket) {
			let span = TextSpan::new(open_span.start, close.span.end);
			return Ok(self.ast.push_expr(
				Expression::ArrayList {
					elements: List::EMPTY,
				},
				span,
			));
		}

		let first = self.parse_expression(BindingPower::Default)?;

		if self.lexer.next_if(Token::SemiColon).is_some() {
			let count = self.parse_length()?;
			let close_span = self.next_expect(Token::CloseBracket)?.span;
			let span = TextSpan::new(open_span.start, close_span.end);
			return Ok(self.ast.push_expr(
				Expression::ArrayRepeat {
					value: first,
					count,
				},
				span,
			));
		}

		let mut elements = vec![first];
		while self.lexer.next_if(Token::Comma).is_some()
			&& self.lexer.peek().inner != Token::CloseBracket
		{
			elements.push(self.parse_expression(BindingPower::Default)?);
		}

		let close_span = self.next_expect(Token::CloseBracket)?.span;
		let span = TextSpan::new(open_span.start, close_span.end);
		let elements = self.ast.push_list(elements);
		Ok(self.ast.push_expr(Expression::ArrayList { elements }, span))
	}

	fn parse_index_expression(&mut self, object: ExprId) -> Result<ExprId, ()> {
		_ = self.lexer.next(); // consume `[`
		let index = self.parse_expression(BindingPower::Default)?;
		let close_span = self.next_expect(Token::CloseBracket)?.span;
		let span =
			TextSpan::new(self.ast.expr_span(object).start, close_span.end);
		Ok(self
			.ast
			.push_expr(Expression::Index { object, index }, span))
	}

	/// `..`, or one element in the list.
	fn parse_pattern_element(
		parser: &mut Parser,
	) -> Result<Spanned<PatternElement>, ()> {
		if let Some(dot_dot) = parser.lexer.next_if(Token::DotDot) {
			return Ok(Spanned {
				inner: PatternElement::Rest(dot_dot.span),
				span: dot_dot.span,
			});
		}
		let pattern = Parser::parse_pattern(parser)?;
		Ok(Spanned {
			inner: PatternElement::Pattern(pattern),
			span: parser.ast.pattern_span(pattern),
		})
	}

	/// `..`, `name` or `name: pat`.
	fn parse_pattern_field_item(
		parser: &mut Parser,
	) -> Result<Spanned<PatternFieldItem>, ()> {
		if let Some(dot_dot) = parser.lexer.next_if(Token::DotDot) {
			return Ok(Spanned {
				inner: PatternFieldItem::Rest(dot_dot.span),
				span: dot_dot.span,
			});
		}
		let name = parser.expect_name(&[])?;
		let pattern = if parser.lexer.next_if(Token::Colon).is_some() {
			Some(Parser::parse_pattern(parser)?)
		} else {
			None
		};
		let end = pattern.map_or(name.span.end, |pattern| {
			parser.ast.pattern_span(pattern).end
		});
		Ok(Spanned {
			inner: PatternFieldItem::Field(PatternField { name, pattern }),
			span: TextSpan::new(name.span.start, end),
		})
	}

	/// `{ field, other: pat, .. }`, braces included, as written.
	fn parse_pattern_fields(
		parser: &mut Parser,
	) -> Result<Spanned<List<PatternFieldItem>>, ()> {
		let fields =
			parser.separated(BRACES, Parser::parse_pattern_field_item)?;
		Ok(parser.push_delimited(fields))
	}

	/// The elements of a positional list, `(pat, .., pat)`, with the `(`
	/// at `open_span` consumed.
	fn parse_pattern_elements(
		parser: &mut Parser,
		open_span: TextSpan,
	) -> Result<Spanned<List<PatternElement>>, ()> {
		let elements = parser.separated_after(
			PARENS,
			open_span,
			Parser::parse_pattern_element,
		);
		Ok(parser.push_delimited(elements))
	}

	/// `(pat, .., pat)`.
	fn parse_tuple_pattern(parser: &mut Parser) -> Result<PatId, ()> {
		let open_span = parser.next_expect(Token::OpenParen)?.span;
		let elements = Parser::parse_pattern_elements(parser, open_span)?;
		Ok(parser.ast.push_pattern(
			Pattern::Destructure(Destructure::Tuple {
				elements: elements.inner,
			}),
			elements.span,
		))
	}

	/// `Path(pat, ..)` or `Path({ field, .. })`, with `path` consumed and `(`
	/// next — decided on the token after `(`, exactly as a call's arguments.
	fn parse_struct_pattern(
		parser: &mut Parser,
		path: Box<[PathSegment]>,
	) -> Result<PatId, ()> {
		let path_start = path.first().unwrap().ident.span.start;
		let open_span = parser.next_expect(Token::OpenParen)?.span;
		if parser.lexer.peek().inner == Token::OpenBrace {
			let fields = Parser::parse_pattern_fields(parser)?;
			let close_span = parser.next_expect(Token::CloseParen)?.span;
			let path = parser.ast.push_list(path);
			return Ok(parser.ast.push_pattern(
				Pattern::Destructure(Destructure::NamedStruct {
					path,
					fields: fields.inner,
				}),
				TextSpan::new(path_start, close_span.end),
			));
		}
		let elements = Parser::parse_pattern_elements(parser, open_span)?;
		let path = parser.ast.push_list(path);
		Ok(parser.ast.push_pattern(
			Pattern::Destructure(Destructure::Struct {
				path,
				elements: elements.inner,
			}),
			TextSpan::new(path_start, elements.span.end),
		))
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
		Ok(PathTerm::Old(parser.ast.push_pattern(Pattern::Error, span)))
	}

	/// A path: one or more segments, `A::B`. As in an expression, it may
	/// start at `Self`, `crate` or `super`.
	fn parse_path(parser: &mut Parser) -> Result<PathTerm, ()> {
		let first = parser.expect_name(&[
			Keyword::SelfPascal,
			Keyword::Package,
			Keyword::Super,
		])?;
		let mut segments = vec![PathSegment::new(first)];

		while parser.lexer.peek().inner == Token::ColonColon {
			let colons = parser.lexer.next(); // consume `::`
			let next = parser.lexer.peek();
			match next.inner {
				// `::<T, U>` — turbofish for the last segment
				Token::LeftArrow => {
					let (type_args, args_span, _) = parser.parse_type_args()?;
					let last = segments.last_mut().unwrap();
					last.type_args = type_args;
					last.args_span = args_span;
				}
				// `::{ ... }` — the old named pattern, gone
				Token::OpenBrace => {
					return Parser::parse_old_struct_pattern(parser, &segments);
				}
				// `::ident` — another path segment
				token if Self::is_later_segment(token) => {
					// A later segment is a name, `super` included, as in an
					// expression.
					segments.push(PathSegment::new(
						parser.expect_name(&[Keyword::Super])?,
					));
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
	fn parse_path_pattern(parser: &mut Parser) -> Result<PatId, ()> {
		let segments = match Parser::parse_path(parser)? {
			PathTerm::Path(segments) => segments,
			PathTerm::Old(pattern) => return Ok(pattern),
		};

		if parser.lexer.peek().inner == Token::OpenParen {
			return Parser::parse_struct_pattern(parser, segments);
		}

		// A single segment with no type arguments is a name, and a name
		// binds; anything longer is a path, and a path is a constant.
		let span = AST::path_span(&segments);
		let kind = match &*segments {
			[segment] if segment.type_args.is_empty() => Pattern::Binding {
				mutable: false,
				name: segment.ident,
			},
			_ => Pattern::Constant {
				path: parser.ast.push_list(segments),
			},
		};
		Ok(parser.ast.push_pattern(kind, span))
	}

	/// `const P`: a name marked `const` compares with the constant of that
	/// name instead of binding it. Only a path can be marked: a literal is
	/// a comparison already, and a destructure has no name to mark.
	fn parse_const_pattern(
		parser: &mut Parser,
		const_span: TextSpan,
	) -> Result<PatId, ()> {
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
		let path = parser.ast.push_list(path);
		Ok(parser.ast.push_pattern(Pattern::Constant { path }, span))
	}

	/// A pattern, alternatives included: `|` joins them.
	fn parse_pattern(parser: &mut Parser) -> Result<PatId, ()> {
		let first = Parser::parse_primary(parser)?;
		if parser.lexer.peek().inner != Token::Vbar {
			return Ok(first);
		}
		let mut alternatives = vec![first];
		while parser.lexer.next_if(Token::Vbar).is_some() {
			alternatives.push(Parser::parse_primary(parser)?);
		}
		let span = TextSpan::new(
			parser.ast.pattern_span(first).start,
			parser.ast.pattern_span(*alternatives.last().unwrap()).end,
		);
		let alternatives = parser.ast.push_list(alternatives);
		Ok(parser.ast.push_pattern(Pattern::Or(alternatives), span))
	}

	/// One term of a pattern. What it is follows from its own shape: a
	/// literal compares with that value, a qualified path with that
	/// constant, and a name binds — unless `const` says it is a constant.
	fn parse_primary(parser: &mut Parser) -> Result<PatId, ()> {
		let token = parser.lexer.peek();
		match token.inner {
			Token::OpenParen => Parser::parse_tuple_pattern(parser),
			Token::Int
			| Token::Char
			| Token::Float
			| Token::String
			| Token::Minus => {
				let literal = parser.parse_literal()?;
				Ok(parser.ast.push_pattern(
					Pattern::Literal(literal.inner),
					literal.span,
				))
			}
			Token::Keyword(Keyword::Underscore) => {
				let span = parser.lexer.next().span;
				Ok(parser.ast.push_pattern(Pattern::Wildcard, span))
			}
			Token::Keyword(Keyword::Mut) => {
				let mut_span = parser.lexer.next().span;
				let name = parser.expect_name(&[])?;
				Ok(parser.ast.push_pattern(
					Pattern::Binding {
						mutable: true,
						name,
					},
					TextSpan::new(mut_span.start, name.span.end),
				))
			}
			Token::Keyword(Keyword::Const) => {
				let const_span = parser.lexer.next().span;
				Parser::parse_const_pattern(parser, const_span)
			}
			Token::Keyword(Keyword::Local) => {
				let span = parser.lexer.next().span;
				parser
					.ast
					.diagnostics
					.push(report_redundant_local(parser.ast.file_id, span));
				Err(())
			}
			Token::Identifier | Token::Keyword(_) => {
				Parser::parse_path_pattern(parser)
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
		let mut end = parser.ast.pattern_span(pattern).end;

		// A part not written yet (`local x: `, `local x: T`, `local x = `) is
		// reported and kept as an error node, as a parameter's missing type
		// is: the statement and what is written of it stay, and the token
		// that follows is left for whatever it closes or starts. The node
		// spans the gap where the part belongs, up to that token, so a
		// position there is in it (what completion reads).
		let ty = match parser.lexer.next_if(Token::Colon) {
			Some(colon) => {
				let ty = match parser.parse_type_expression() {
					Ok(ty) => ty,
					Err(()) => {
						let gap = TextSpan::new(
							colon.span.end,
							parser.lexer.peek().span.start,
						);
						parser.ast.push_type(TypeExpression::Error, gap)
					}
				};
				end = parser.ast.type_span(ty).end;
				Some(ty)
			}
			None => None,
		};

		let assigned = parser.lexer.next_if(Token::Eq);
		if let Some(eq) = assigned {
			end = eq.span.end;
		}
		let token = parser.lexer.peek();
		let value =
			if assigned.is_some() && Self::starts_expression(token.inner) {
				parser.parse_expression(BindingPower::Default)?
			} else {
				parser
					.ast
					.diagnostics
					.push(report_missing_local_initializer(
						parser.ast.file_id,
						token.span,
					));
				parser.ast.push_expr(
					Expression::Error,
					TextSpan::new(end, token.span.start),
				)
			};

		let span = TextSpan::new(
			local_keyword.span.start,
			parser.ast.expr_span(value).end,
		);
		Ok(Spanned {
			inner: Statement::LocalDefinition { pattern, ty, value },
			span,
		})
	}

	fn parse_global_definition_item(
		parser: &mut Parser,
	) -> Result<Spanned<Item>, ()> {
		let global_keyword = parser.lexer.next();
		let mut_span = match parser.peek_keyword() {
			Some(Keyword::Mut) => {
				let mut_token = parser.lexer.next();
				Some(mut_token.span)
			}
			_ => None,
		};

		let name = parser.expect_name(&[])?;

		let ty = match parser.lexer.next_if(Token::Colon) {
			Some(_) => Some(parser.parse_type_expression()?),
			None => None,
		};

		let assigned = parser.lexer.next_if(Token::Eq).is_some();
		let token = parser.lexer.peek();
		if !assigned || !Self::starts_expression(token.inner) {
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

		let span = TextSpan::new(
			global_keyword.span.start,
			parser.ast.expr_span(value).end,
		);
		Ok(Spanned {
			inner: Item::Global {
				pub_span: None,
				mut_span,
				name,
				ty,
				value,
				attributes: Box::new([]),
			},
			span,
		})
	}

	fn parse_const_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let const_span = parser.lexer.next().span;
		let Spanned {
			inner: name_symbol,
			span: name_span,
		} = parser.expect_name(&[])?;

		let ty = if parser.lexer.next_if(Token::Colon).is_some() {
			Some(parser.parse_type_expression()?)
		} else {
			None
		};

		let _ = parser.next_expect(Token::Eq)?;
		let value = parser.parse_expression(BindingPower::Default)?;

		let span =
			TextSpan::new(const_span.start, parser.ast.expr_span(value).end);
		Ok(Spanned {
			inner: Item::Const {
				pub_span: None,
				name: Spanned {
					inner: name_symbol,
					span: name_span,
				},
				ty,
				value,
				attributes: Box::new([]),
			},
			span,
		})
	}

	fn parse_placeholder_expression(&mut self) -> Result<ExprId, ()> {
		let span = self.lexer.next().span;
		Ok(self.ast.push_expr(Expression::Placeholder, span))
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
		let name = parser.expect_name(&[])?;

		let alias = if matches!(parser.peek_keyword(), Some(Keyword::As)) {
			parser.lexer.next();
			Some(parser.next_expect(Token::String)?.span)
		} else {
			None
		};

		let span = match alias {
			Some(alias) => TextSpan::new(name.span.start, alias.end),
			None => name.span,
		};

		Ok(Spanned {
			inner: ExportEntry { name, alias },
			span,
		})
	}

	fn parse_enum_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let enum_span = parser.lexer.next().span;

		let Spanned {
			inner: name_symbol,
			span: name_span,
		} = parser.expect_name(&[])?;

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
			Some(parser.parse_type_expression()?)
		} else if parser.lexer.next_if(Token::OpenParen).is_some() {
			let repr = parser.parse_type_expression()?;
			parser.next_expect(Token::CloseParen)?;
			Some(repr)
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
					let Spanned {
						inner: name_symbol,
						span: name_token_span,
					} = parser.expect_name(&[])?;

					let (value, span) =
						if parser.lexer.next_if(Token::Eq).is_some() {
							let expr = parser
								.parse_expression(BindingPower::Default)?;
							let span = TextSpan::new(
								name_token_span.start,
								parser.ast.expr_span(expr).end,
							);
							(Some(expr), span)
						} else {
							(None, name_token_span)
						};

					Ok(Spanned {
						inner: EnumEntry::Variant(EnumVariant {
							name: Spanned {
								inner: name_symbol,
								span: name_token_span,
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
				let Spanned {
					inner: name_symbol,
					span: name_span,
				} = parser.expect_name(&[])?;
				parser.next_expect(Token::Eq)?;
				let ty = parser.parse_type_expression()?;
				let span = TextSpan::new(
					type_span.start,
					parser.ast.type_span(ty).end,
				);
				Ok(Spanned {
					inner: ImplItem::AssocType {
						pub_span,
						name: Spanned {
							inner: name_symbol,
							span: name_span,
						},
						ty,
						attributes: Box::new([]),
					},
					span,
				})
			}
			Some(Keyword::Const) => {
				let const_span = parser.lexer.next().span;
				let Spanned {
					inner: name_symbol,
					span: name_span,
				} = parser.expect_name(&[])?;

				let ty = if parser.lexer.next_if(Token::Colon).is_some() {
					Some(parser.parse_type_expression()?)
				} else {
					None
				};

				_ = parser.next_expect(Token::Eq)?;
				let value = parser.parse_expression(BindingPower::Default)?;
				let span = TextSpan::new(
					const_span.start,
					parser.ast.expr_span(value).end,
				);
				Ok(Spanned {
					inner: ImplItem::Constant {
						pub_span,
						name: Spanned {
							inner: name_symbol,
							span: name_span,
						},
						ty,
						value,
						attributes: Box::new([]),
					},
					span,
				})
			}
			Some(Keyword::Func) => {
				let fn_span = parser.lexer.next().span;
				let Spanned {
					inner: name_symbol,
					span: name_span,
				} = parser.expect_name(&[])?;
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
				let block = parser.parse_block()?;
				let method_span = TextSpan::new(
					fn_span.start,
					parser.ast.block_span(block).end,
				);
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
						block,
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

		let name = parser.expect_name(&[])?;

		let supertraits: Option<BoundId> =
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
							let Spanned {
								inner: name_symbol,
								span: name_span,
							} = parser.expect_name(&[])?;

							let bounds: Option<BoundId> =
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
									Some(parser.parse_type_expression()?)
								} else {
									None
								};
							let span = TextSpan::new(
								type_span.start,
								value
									.map(|value| parser.ast.type_span(value))
									.or_else(|| {
										bounds.map(|bounds| {
											parser.ast.bound_span(bounds)
										})
									})
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
							let Spanned {
								inner: name_symbol,
								span: name_span,
							} = parser.expect_name(&[])?;
							parser.next_expect(Token::Colon)?;
							let ty = parser.parse_type_expression()?;
							let value =
								if parser.lexer.next_if(Token::Eq).is_some() {
									Some(parser.parse_expression(
										BindingPower::Default,
									)?)
								} else {
									None
								};
							let span = TextSpan::new(
								const_span.start,
								match value {
									Some(value) => {
										parser.ast.expr_span(value).end
									}
									None => parser.ast.type_span(ty).end,
								},
							);
							Ok(Spanned {
								inner: TraitItem::Const {
									name: Spanned {
										inner: name_symbol,
										span: name_span,
									},
									ty,
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
								Some(parser.parse_block()?)
							} else {
								None
							};
							let span = TextSpan::new(
								signature.span.start,
								match body {
									Some(body) => {
										parser.ast.block_span(body).end
									}
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

		let name = parser.expect_name(&[])?;

		// Optional bound clause: `typeset Name: A + B { .. }` — mirrors a
		// trait's supertrait list. The `where { .. }` bindings a single bound
		// may carry are handled by `parse_bounds_expression`; the members
		// brace that follows is unambiguous because that never continues past
		// a `+`.
		let bounds: Option<BoundId> = match parser.lexer.next_if(Token::Colon) {
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

		let Spanned {
			inner: name_symbol,
			span: name_span,
		} = parser.expect_name(&[])?;

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
			span: TextSpan::new(start, parser.ast.type_span(ty).end),
			inner: StructField {
				pub_span,
				binding,
				ty,
			},
		})
	}

	/// Parse `type Name = TypeExpr;` or `type Name<T> = TypeExpr;`.
	fn parse_type_alias_item(parser: &mut Parser) -> Result<Spanned<Item>, ()> {
		let type_span = parser.lexer.next().span;

		let Spanned {
			inner: name_symbol,
			span: name_span,
		} = parser.expect_name(&[])?;

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
			Some(parser.parse_type_expression()?)
		} else {
			None
		};

		let end = match body {
			Some(body) => parser.ast.type_span(body).end,
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

		let name = parser.expect_name(&[])?;

		parser.next_expect(Token::Colon)?;
		let size = parser.parse_type_expression()?;

		let span =
			TextSpan::new(memory_span.start, parser.ast.type_span(size).end);
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
		let mut_span = match self.peek_keyword() {
			Some(Keyword::Mut) => Some(self.lexer.next().span),
			_ => None,
		};

		let Spanned {
			inner: name_symbol,
			span: name_span,
		} = self.expect_name(&[])?;
		let name = Spanned {
			inner: name_symbol,
			span: name_span,
		};

		let _ = self.next_expect(Token::Colon)?;
		let type_expr = self.parse_type_expression()?;
		let span = TextSpan::new(
			keyword_span.start,
			self.ast.type_span(type_expr).end,
		);

		Ok(Spanned {
			inner: ImportDeclaration::Global {
				mut_span,
				name,
				ty: type_expr,
			},
			span,
		})
	}

	fn parse_memory_import_declaration(
		&mut self,
	) -> Result<Spanned<ImportDeclaration>, ()> {
		let keyword_span = self.lexer.next().span;
		let name = self.expect_name(&[])?;
		let _ = self.next_expect(Token::Colon)?;
		let size = self.parse_type_expression()?;
		let span =
			TextSpan::new(keyword_span.start, self.ast.type_span(size).end);
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
		let keyword = parser.peek_keyword();
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

		let Spanned {
			inner: name_symbol,
			span: name_span,
		} = parser.expect_name(&[])?;

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
		self.expect_name(&[
			Keyword::Package,
			Keyword::Super,
			Keyword::SelfLower,
		])
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

		let alias = if token.inner == Token::Keyword(Keyword::As) {
			_ = parser.lexer.next(); // consume "as"
			Some(parser.expect_name(&[])?)
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
					let body = parser.parse_block()?;
					let span = parser.ast.block_span(body);
					parser.report_crate_member_body(span);
					span.end
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
				let name = parser.expect_name(&[])?;
				parser.next_expect(Token::Colon)?;
				let ty = parser.parse_type_expression()?;
				let end = if parser.lexer.next_if(Token::Eq).is_some() {
					let value =
						parser.parse_expression(BindingPower::Default)?;
					let span = parser.ast.expr_span(value);
					parser.report_crate_member_body(span);
					span.end
				} else {
					parser.ast.type_span(ty).end
				};
				(
					Item::PackageConst {
						pub_span: None,
						crate_span,
						attributes: Box::new([]),
						name,
						ty,
					},
					end,
				)
			}
			Some(Keyword::Type) => {
				parser.lexer.next();
				let name = parser.expect_name(&[])?;
				let name_span = name.span;
				let type_params =
					if parser.lexer.peek().inner == Token::LeftArrow {
						parser.parse_type_params()?
					} else {
						Box::new([])
					};
				let end = if parser.lexer.next_if(Token::Eq).is_some() {
					let body = parser.parse_type_expression()?;
					parser.report_crate_member_body(parser.ast.type_span(body));
					parser.ast.type_span(body).end
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
			parser.expect_name(&[])?
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
			Token::Keyword(Keyword::As) => {
				_ = parser.lexer.next(); // consume "as"
				parser.expect_name(&[])?
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
