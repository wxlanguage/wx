use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::{Symbol, SymbolU32};

use crate::{
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	vfs::{self, FileId},
};

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
	Line,
	Doc,
}

#[derive(Clone, Copy)]
pub struct Comment {
	pub span: TextSpan,
	pub kind: CommentKind,
}

pub struct CommentMap(pub Box<[Comment]>);

impl CommentMap {
	pub fn empty() -> Self {
		Self(Box::new([]))
	}

	/// Returns all comments whose spans fall entirely within `[start, end)`.
	pub fn between(&self, start: u32, end: u32) -> &[Comment] {
		let lo = self.0.partition_point(|c| c.span.end <= start);
		let hi = self.0.partition_point(|c| c.span.start < end);
		&self.0[lo..hi]
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum Token {
	// Literals
	Int,
	Float,
	Char,
	String,
	Identifier,
	// Delimiters
	Colon,
	ColonColon,
	SemiColon,
	Comma,
	Dot,
	DotDot,
	// Grouping
	OpenParen,
	CloseParen,
	OpenBrace,
	CloseBrace,
	OpenBracket,
	CloseBracket,
	// Operators
	Eq,
	EqEq,
	Bang,
	BangEq,
	LeftArrow,
	LeftArrowEq,
	DoubleLeftArrow,
	DoubleLeftArrowEq,
	RightArrow,
	RightArrowEq,
	DoubleRightArrow,
	DoubleRightArrowEq,
	Plus,
	PlusEq,
	Minus,
	MinusEq,
	Star,
	StarEq,
	Slash,
	SlashEq,
	Percent,
	PercentEq,
	Amper,
	DoubleAmper,
	AmperEq,
	Vbar,
	DoubleVbar,
	VbarEq,
	Caret,
	CaretEq,
	Hash,
	MinusRightArrow,
	// Special
	Comment,
	DocComment,
	Unknown,
	Eof,
}

impl std::fmt::Display for Token {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use Token::*;
		let text = match self {
			Int => "integer",
			Float => "float",
			Char => "char",
			String => "string",
			Identifier => "identifier",
			Colon => ":",
			ColonColon => "::",
			SemiColon => ";",
			Comma => ",",
			Dot => ".",
			DotDot => "..",
			OpenParen => "(",
			CloseParen => ")",
			OpenBrace => "{",
			CloseBrace => "}",
			OpenBracket => "[",
			CloseBracket => "]",
			Eq => "=",
			Bang => "!",
			EqEq => "==",
			BangEq => "!=",
			LeftArrow => "<",
			LeftArrowEq => "<=",
			DoubleLeftArrow => "<<",
			DoubleLeftArrowEq => "<<=",
			RightArrow => ">",
			RightArrowEq => ">=",
			DoubleRightArrow => ">>",
			DoubleRightArrowEq => ">>=",
			Plus => "+",
			PlusEq => "+=",
			Minus => "-",
			MinusEq => "-=",
			Star => "*",
			StarEq => "*=",
			Slash => "/",
			SlashEq => "/=",
			Percent => "%",
			PercentEq => "%=",
			Amper => "&",
			DoubleAmper => "&&",
			AmperEq => "&=",
			Vbar => "|",
			DoubleVbar => "||",
			VbarEq => "|=",
			Caret => "^",
			CaretEq => "^=",
			Hash => "#",
			MinusRightArrow => "->",
			Comment => "comment",
			DocComment => "doc comment",
			Unknown => "unknown token",
			Eof => "end of file",
		};
		write!(f, "{}", text)
	}
}

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

/// Benchmark hook (see `benches/lexer.rs`): lex `src` to EOF and return the
/// token count. Gated behind the `bench` feature — not part of the public API.
#[cfg(feature = "bench")]
#[doc(hidden)]
pub fn bench_lex_to_eof(src: &str) -> usize {
	let mut lexer = Lexer::new(src);
	let mut count = 0usize;
	loop {
		count += 1;
		if lexer.next().inner == Token::Eof {
			return count;
		}
	}
}

struct Lexer<'src> {
	chars: std::str::Chars<'src>,
	src_len: usize,
	peeked: Option<Spanned<Token>>,
	comments: Vec<Comment>,
	has_crlf: bool,
	unknown_spans: Vec<TextSpan>,
}

const EOF: char = '\0';

impl<'src> Lexer<'src> {
	fn new(input: &'src str) -> Lexer<'src> {
		Lexer {
			chars: input.chars(),
			src_len: input.len(),
			peeked: None,
			comments: Vec::new(),
			has_crlf: false,
			unknown_spans: Vec::new(),
		}
	}

	/// Current byte offset into the source.
	fn offset(&self) -> usize {
		self.src_len - self.chars.as_str().len()
	}

	fn peek(&mut self) -> Spanned<Token> {
		match &self.peeked {
			Some(token) => *token,
			None => {
				let token = self.next();
				self.peeked = Some(token);
				token
			}
		}
	}

	fn next_if(&mut self, expected: Token) -> Option<Spanned<Token>> {
		let peeked = match &self.peeked {
			Some(token) => *token,
			None => {
				let token = self.next();
				self.peeked = Some(token);
				token
			}
		};
		if peeked.inner == expected {
			self.peeked = None;
			Some(peeked)
		} else {
			None
		}
	}

	fn next(&mut self) -> Spanned<Token> {
		if let Some(token) = self.peeked.take() {
			return token;
		}

		let mut unknown_span: Option<TextSpan> = None;
		loop {
			let token = self.advance();
			match token.inner {
				Token::Comment => {
					self.comments.push(Comment {
						span: token.span,
						kind: CommentKind::Line,
					});
					continue;
				}
				Token::DocComment => {
					self.comments.push(Comment {
						span: token.span,
						kind: CommentKind::Doc,
					});
					continue;
				}
				Token::Unknown => {
					unknown_span = match unknown_span {
						Some(span) => {
							Some(TextSpan::new(span.start, token.span.end))
						}
						None => Some(token.span),
					};
					continue;
				}
				_ => {
					// A run of unknown characters is recorded and skipped,
					// exactly like a comment. The parser has no handler for
					// `Token::Unknown`, so surfacing one only ever added a
					// second, misleading diagnostic on top of this one —
					// pointing at whatever token happened to follow.
					//
					// Recorded here, where the run ends, so it is counted once
					// however often the surrounding tokens are peeked: `next`
					// returns a peeked token before reaching this point.
					if let Some(span) = unknown_span {
						self.unknown_spans.push(span);
					}
					return token;
				}
			}
		}
	}

	fn advance(&mut self) -> Spanned<Token> {
		// Whitespace never becomes a token — skip it here instead of
		// round-tripping it through the dispatch below only for `next` to
		// discard the result and loop. Scan on a local cursor (see
		// `eat_while`) so the skip costs one `self.chars` store, not one
		// per whitespace char.
		let mut cursor = self.chars.clone();
		loop {
			let mut probe = cursor.clone();
			match probe.next() {
				Some(' ' | '\t' | '\n') => cursor = probe,
				Some('\r') => {
					self.has_crlf = true;
					cursor = probe;
				}
				_ => break,
			}
		}
		self.chars = cursor;

		let start = self.offset() as u32;
		let token = match self.chars.next().unwrap_or(EOF) {
			// Patterns are ordered by frequency of occurrence in typical source code
			// Most Frequent
			'A'..='Z' | 'a'..='z' | '_' => self.consume_identifier(),
			'0'..='9' => self.consume_number(),

			// Common Punctuation & Operators
			'(' => Token::OpenParen,
			')' => Token::CloseParen,
			';' => Token::SemiColon,
			',' => Token::Comma,
			'=' => self.consume_and_check('=', Token::EqEq, Token::Eq),
			'{' => Token::OpenBrace,
			'}' => Token::CloseBrace,
			'#' => Token::Hash,
			'[' => Token::OpenBracket,
			']' => Token::CloseBracket,
			'.' => self.consume_and_check('.', Token::DotDot, Token::Dot),
			':' => self.consume_and_check(':', Token::ColonColon, Token::Colon),
			'/' => self.consume_slash(),

			// Moderately Frequent
			'+' => self.consume_and_check('=', Token::PlusEq, Token::Plus),
			'-' => self.consume_dash(),
			'*' => self.consume_and_check('=', Token::StarEq, Token::Star),
			'<' => self.consume_open_angle(),
			'>' => self.consume_close_angle(),
			'!' => self.consume_and_check('=', Token::BangEq, Token::Bang),
			'&' => self.consume_amper(),
			'|' => self.consume_vbar(),
			'"' => self.consume_string(),

			// Less Frequent
			'\'' => self.consume_char(),
			'%' => {
				self.consume_and_check('=', Token::PercentEq, Token::Percent)
			}
			'^' => self.consume_and_check('=', Token::CaretEq, Token::Caret),
			'\0' => Token::Eof,
			_ => Token::Unknown,
		};
		let span = TextSpan::new(start, self.offset() as u32);

		Spanned { inner: token, span }
	}

	#[inline]
	fn consume_and_check(
		&mut self,
		expect: char,
		token: Token,
		fallback: Token,
	) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			ch if ch == expect => {
				_ = self.chars.next();
				token
			}
			_ => fallback,
		}
	}

	#[inline]
	fn consume_amper(&mut self) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			'&' => {
				_ = self.chars.next();
				Token::DoubleAmper
			}
			'=' => {
				_ = self.chars.next();
				Token::AmperEq
			}
			_ => Token::Amper,
		}
	}

	#[inline]
	fn consume_vbar(&mut self) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			'|' => {
				_ = self.chars.next();
				Token::DoubleVbar
			}
			'=' => {
				_ = self.chars.next();
				Token::VbarEq
			}
			_ => Token::Vbar,
		}
	}

	#[inline]
	fn consume_dash(&mut self) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			'=' => {
				_ = self.chars.next();
				Token::MinusEq
			}
			'>' => {
				_ = self.chars.next();
				Token::MinusRightArrow
			}
			_ => Token::Minus,
		}
	}

	#[inline]
	fn consume_open_angle(&mut self) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			'=' => {
				_ = self.chars.next();
				Token::LeftArrowEq
			}
			'<' => {
				_ = self.chars.next();
				match self.chars.clone().next().unwrap_or(EOF) {
					'=' => {
						_ = self.chars.next();
						Token::DoubleLeftArrowEq
					}
					_ => Token::DoubleLeftArrow,
				}
			}
			_ => Token::LeftArrow,
		}
	}

	#[inline]
	fn consume_close_angle(&mut self) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			'=' => {
				_ = self.chars.next();
				Token::RightArrowEq
			}
			'>' => {
				_ = self.chars.next();
				match self.chars.clone().next().unwrap_or(EOF) {
					'=' => {
						_ = self.chars.next();
						Token::DoubleRightArrowEq
					}
					_ => Token::DoubleRightArrow,
				}
			}
			_ => Token::RightArrow,
		}
	}

	/// Consume a `>>` token and split it: return the span of the first `>` and
	/// push the second `>` into `peeked`. Used when a nested generic arg list
	/// closes at the same position as the outer one (e.g. `Foo<Bar<T>>`).
	fn split_double_right_arrow(&mut self) -> TextSpan {
		let tok = self.next();
		debug_assert!(tok.inner == Token::DoubleRightArrow);
		let first = TextSpan::new(tok.span.start, tok.span.start + 1);
		self.peeked = Some(Spanned {
			inner: Token::RightArrow,
			span: TextSpan::new(tok.span.start + 1, tok.span.end),
		});
		first
	}

	/// Consume a `<<` token and split it: return the span of the first `<` and
	/// push the second `<` into `peeked`. Used when a qualified type opens
	/// another one immediately (`<<A as B>::C as D>::E`), the mirror of
	/// `split_double_right_arrow`.
	fn split_double_left_arrow(&mut self) -> TextSpan {
		let tok = self.next();
		debug_assert!(tok.inner == Token::DoubleLeftArrow);
		let first = TextSpan::new(tok.span.start, tok.span.start + 1);
		self.peeked = Some(Spanned {
			inner: Token::LeftArrow,
			span: TextSpan::new(tok.span.start + 1, tok.span.end),
		});
		first
	}

	/// Advance past each following char for which `pred` holds, leaving
	/// `self.chars` on the first char that doesn't (or at end of input).
	#[inline]
	fn eat_while(&mut self, pred: impl Fn(char) -> bool) {
		// Scan on a local cursor and write `self.chars` back once, rather
		// than restoring it through `&mut self` after every char — the
		// latter forces a store to the `Lexer` struct per iteration.
		let mut cursor = self.chars.clone();
		loop {
			let mut probe = cursor.clone();
			match probe.next() {
				Some(ch) if pred(ch) => cursor = probe,
				_ => break,
			}
		}
		self.chars = cursor;
	}

	#[inline]
	fn consume_identifier(&mut self) -> Token {
		self.eat_while(
			|ch| matches!(ch, 'A'..='Z' | 'a'..='z' | '0'..='9' | '_'),
		);
		Token::Identifier
	}

	fn consume_number(&mut self) -> Token {
		match self.chars.clone().next() {
			Some('b' | 'B') => {
				_ = self.chars.next();
				self.eat_while(|ch| matches!(ch, '0' | '1' | '_'));
				return Token::Int;
			}
			Some('x' | 'X') => {
				_ = self.chars.next();
				self.eat_while(|ch| ch.is_ascii_hexdigit() || ch == '_');
				return Token::Int;
			}
			_ => {}
		}

		// See `eat_while`: scan locally, store `self.chars` back once.
		let mut seen_dot = false;
		let mut cursor = self.chars.clone();
		loop {
			let mut probe = cursor.clone();
			match probe.next() {
				Some('0'..='9' | '_') => cursor = probe,
				Some('.') if !seen_dot => {
					// `probe` is now past the `.`; don't consume it if the
					// next char is also `.` (the `..` range operator).
					if probe.clone().next() == Some('.') {
						break;
					}
					seen_dot = true;
					cursor = probe;
				}
				_ => break,
			}
		}
		self.chars = cursor;

		// Scientific notation: `e`/`E` right after a numeric literal is
		// always an exponent — there's no valid grammar where an
		// identifier can immediately follow a number with no operator
		// between them — so commit unconditionally rather than
		// backtracking. An empty/sign-only exponent (`1e`, `1e+`) still
		// lexes as a single malformed Float token, which falls straight
		// into the same `report_invalid_float_literal` diagnostic
		// `parse_float_expression` already raises for any span
		// `str::parse::<f64>` rejects — no separate error handling needed
		// here.
		if let Some('e' | 'E') = self.chars.clone().next() {
			_ = self.chars.next();
			if let Some('+' | '-') = self.chars.clone().next() {
				_ = self.chars.next();
			}
			self.eat_while(|ch| ch.is_ascii_digit() || ch == '_');
			return Token::Float;
		}

		match seen_dot {
			true => Token::Float,
			false => Token::Int,
		}
	}

	fn consume_string(&mut self) -> Token {
		loop {
			match self.chars.next().unwrap_or(EOF) {
				'\\' => {
					_ = self.chars.next();
				}
				'"' | EOF => return Token::String,
				_ => (),
			}
		}
	}

	fn consume_char(&mut self) -> Token {
		loop {
			match self.chars.next().unwrap_or(EOF) {
				'\\' => {
					_ = self.chars.next();
				}
				'\'' | EOF => return Token::Char,
				_ => (),
			}
		}
	}

	fn consume_slash(&mut self) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			'/' => {
				_ = self.chars.next(); // consume second /
				let is_doc = self.chars.clone().next().unwrap_or(EOF) == '/';
				self.eat_while(|ch| !matches!(ch, '\n' | EOF));
				if is_doc {
					Token::DocComment
				} else {
					Token::Comment
				}
			}
			'=' => {
				_ = self.chars.next();
				Token::SlashEq
			}
			_ => Token::Slash,
		}
	}
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum BinaryOp {
	// Arithmetic
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	// Comparison
	Eq,
	NotEq,
	Less,
	LessEq,
	Greater,
	GreaterEq,
	// Logical
	And,
	Or,
	// Assignment
	Assign,
	AddAssign,
	SubAssign,
	MulAssign,
	DivAssign,
	RemAssign,
	BitAndAssign,
	BitOrAssign,
	BitXorAssign,
	LeftShiftAssign,
	RightShiftAssign,
	// Bitwise
	BitAnd,
	BitOr,
	BitXor,
	LeftShift,
	RightShift,
}

impl BinaryOp {
	pub const fn as_str(&self) -> &'static str {
		match self {
			BinaryOp::Add => "+",
			BinaryOp::Sub => "-",
			BinaryOp::Mul => "*",
			BinaryOp::Div => "/",
			BinaryOp::Rem => "%",
			BinaryOp::Eq => "==",
			BinaryOp::NotEq => "!=",
			BinaryOp::Less => "<",
			BinaryOp::LessEq => "<=",
			BinaryOp::Greater => ">",
			BinaryOp::GreaterEq => ">=",
			BinaryOp::And => "&&",
			BinaryOp::Or => "||",
			BinaryOp::Assign => "=",
			BinaryOp::AddAssign => "+=",
			BinaryOp::SubAssign => "-=",
			BinaryOp::MulAssign => "*=",
			BinaryOp::DivAssign => "/=",
			BinaryOp::RemAssign => "%=",
			BinaryOp::BitAndAssign => "&=",
			BinaryOp::BitOrAssign => "|=",
			BinaryOp::BitXorAssign => "^=",
			BinaryOp::LeftShiftAssign => "<<=",
			BinaryOp::RightShiftAssign => ">>=",
			BinaryOp::BitAnd => "&",
			BinaryOp::BitOr => "|",
			BinaryOp::BitXor => "^",
			BinaryOp::LeftShift => "<<",
			BinaryOp::RightShift => ">>",
		}
	}
}

impl std::fmt::Display for BinaryOp {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.as_str())
	}
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

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum UnaryOp {
	InvertSign,
	Not,
	BitNot,
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

impl UnaryOp {
	pub fn as_str(&self) -> &'static str {
		match self {
			UnaryOp::InvertSign => "-",
			UnaryOp::Not => "!",
			UnaryOp::BitNot => "^",
		}
	}
}

impl std::fmt::Display for UnaryOp {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.as_str())
	}
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
pub struct Spanned<T> {
	pub inner: T,
	pub span: TextSpan,
}

impl<T: Copy> Copy for Spanned<T> {}

/// Represents an item in a separated list, storing both the item and its
/// trailing separator.
///
/// Used for comma-separated lists like function parameters `(a, b, c)` or
/// statement sequences. The `separator` field holds the token that follows this
/// item (e.g., `,` or `;`), if present.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct Separated<T> {
	pub inner: T,
	pub separator: Option<TextSpan>,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum Expression {
	Error,
	/// `1`. Always the raw, non-negative magnitude as written — `-1` is a
	/// separate `Unary { InvertSign, .. }` node wrapping this, never folded
	/// in here. Stored as `u64` (not `i64`) so the full range a literal can
	/// validly denote — up to `u64::MAX` directly, or up to `i64::MIN`'s
	/// magnitude when negated — is representable before a concrete target
	/// type decides the final signed/unsigned interpretation.
	Int {
		value: u64,
	},
	/// `1.0` / `3.4e2`. Carries no payload — the text is recovered from the
	/// span and parsed against the *resolved target type* in TIR
	/// (`coerce_untyped_float_expr`), because the correct rounding (f32 vs f64)
	/// isn't known until then. Same span-only treatment as `Char` / `String`.
	Float,
	/// `({expr})` — transparent grouping, same type as inner
	Grouping {
		value: Box<Spanned<Expression>>,
	},
	/// `5 as i32`
	Cast {
		value: Box<Spanned<Expression>>,
		ty: Box<Spanned<TypeExpression>>,
	},
	/// `-{expr}`
	Unary {
		operator: Spanned<UnaryOp>,
		operand: Box<Spanned<Expression>>,
	},
	/// `{expr} + {expr}`
	Binary {
		left: Box<Spanned<Expression>>,
		operator: Spanned<BinaryOp>,
		right: Box<Spanned<Expression>>,
	},
	/// `{expr}::<...>(a, b)`: a function call, or the construction of a
	/// struct, by position.
	Call {
		callee: Box<Spanned<Expression>>,
		arguments: Box<[Separated<Spanned<Expression>>]>,
	},
	/// `{expr}::<...>({ x: a, y })`: the same, naming each parameter (or
	/// field). The named list is the call's only argument.
	NamedCall {
		callee: Box<Spanned<Expression>>,
		arguments: Box<[Separated<Spanned<NamedArgument>>]>,
	},
	/// `{expr}.{method}::<...>(a, b)`
	MethodCall(Box<MethodCallExpr>),
	/// `{expr}.{method}::<...>({ x: a, y })`
	NamedMethodCall(Box<MethodCallExpr<NamedArgument>>),
	/// `{expr}::<Type1, Type2>` — turbofish type application on a non-path
	/// expression. Method turbofish calls are represented as `MethodCall`.
	TypeApplication {
		callee: Box<Spanned<Expression>>,
		args: Box<[Spanned<TypeExpression>]>,
	},
	/// `{expr}.{expr}`
	ObjectAccess {
		object: Box<Spanned<Expression>>,
		member: Spanned<SymbolU32>,
	},
	/// `{expr}.*`
	Deref {
		pointer: Box<Spanned<Expression>>,
	},
	/// `{expr}.&` — always produces a shared reference.
	AddressOf {
		value: Box<Spanned<Expression>>,
	},
	/// `return {expr}`
	Return {
		value: Option<Box<Spanned<Expression>>>,
	},
	/// `{ ... }`
	Block {
		statements: Box<[Separated<Spanned<Statement>>]>,
	},
	/// `{identifier}: { ... }`
	Label {
		label: Spanned<SymbolU32>,
		block: Box<Spanned<Expression>>,
	},
	/// `break (:{label})? {expr}?`
	Break {
		label: Option<Spanned<SymbolU32>>,
		value: Option<Box<Spanned<Expression>>>,
	},
	/// `if {expr} { ... }`
	IfElse {
		condition: Box<Spanned<Expression>>,
		then_block: Box<Spanned<Expression>>,
		else_block: Option<Box<Spanned<Expression>>>,
	},
	/// `match {expr} { {pattern} -> { ... }, ... }`
	Match {
		scrutinee: Box<Spanned<Expression>>,
		arms: Box<[Separated<Spanned<MatchArm>>]>,
	},
	/// `continue (:{label})?`
	Continue {
		label: Option<Spanned<SymbolU32>>,
	},
	/// `loop { ... }`
	Loop {
		block: Box<Spanned<Expression>>,
	},
	/// `unreachable`
	Unreachable,
	/// `true`
	True,
	/// `false`
	False,
	/// `_` — discard in value position (e.g. `_ = expr;`)
	Placeholder,
	/// Raw quoted string text is recovered from the expression span.
	String,
	/// 'a' — raw source text (including quotes) is recovered from span
	Char,
	/// A `::` separated path: `foo`, `module::Point`, `module::Point::<i32>`.
	/// Replaces bare `Identifier`, `NamespaceAccess`, and path-typed
	/// `TypeApplication` as the canonical representation for named references.
	Path(Box<[PathSegment]>),
	/// `<Type as Trait>::item` — a qualified path pinning down exactly
	/// which trait's item is meant. Composes with the usual postfix grammar
	/// (`Call`, `ObjectAccess`, `Index`) like any other primary expression,
	/// e.g. `<Type as Trait>::method(x)`.
	QualifiedPath {
		root: QualifiedPathRoot,
		segments: Box<[PathSegment]>,
	},
	/// `<Type>::item` — a bare bracketed type used as a path root, with no
	/// trait qualification. Distinct from `QualifiedPath`: this doesn't
	/// disambiguate anything (it resolves exactly like the unbracketed
	/// `Type::item` would), it's purely for self-types that can't be
	/// written as a plain path segment (e.g. `<[T]>::method()`).
	Grouped {
		inner: Box<Spanned<TypeExpression>>,
		segments: Box<[PathSegment]>,
	},
	/// `(a, b, c)` or `()`
	Tuple {
		elements: Box<[Spanned<Expression>]>,
	},
	/// `[a, b, c]`
	ArrayList {
		elements: Box<[Spanned<Expression>]>,
	},
	/// `[value; count]`
	ArrayRepeat {
		value: Box<Spanned<Expression>>,
		count: Box<Spanned<Expression>>,
	},
	/// `expr[index]`
	Index {
		object: Box<Spanned<Expression>>,
		index: Box<Spanned<Expression>>,
	},
	/// `expr[start..end]` — exclusive slice range; either bound may be absent.
	/// `expr[..]` = `start:None, end:None`
	/// `expr[i..]` = `start:Some(i), end:None`
	/// `expr[..n]` = `start:None, end:Some(n)`
	/// `expr[i..n]` = `start:Some(i), end:Some(n)`
	SliceRange {
		object: Box<Spanned<Expression>>,
		start: Option<Box<Spanned<Expression>>>,
		end: Option<Box<Spanned<Expression>>>,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
/// A method call; `Argument` is `Expression` for one by position and
/// `NamedArgument` for one by name.
pub struct MethodCallExpr<Argument = Expression> {
	pub object: Box<Spanned<Expression>>,
	pub method: Spanned<SymbolU32>,
	pub type_args: Box<[Spanned<TypeExpression>]>,
	pub arguments: Box<[Separated<Spanned<Argument>>]>,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct NamedArgument {
	pub name: Spanned<SymbolU32>,
	/// `None` means shorthand: `{ name }` is equivalent to `{ name: name }`
	pub value: Option<Box<Spanned<Expression>>>,
}

/// One arm of a `match` expression: `{pattern} -> { ... }`.
///
/// `pattern` is parsed as an ordinary `Expression` (a literal, `_`, or an
/// `Enum::Variant` path) — legality is validated in TIR rather than by a
/// separate pattern grammar, mirroring how `EnumVariant.value` reuses
/// `Expression` for its discriminant.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct MatchArm {
	pub pattern: Box<Spanned<Expression>>,
	pub body: Box<Spanned<Expression>>,
}

/// One segment of a `::` path, with optional turbofish type args.
/// `Point` → `PathSegment { ident: "Point", type_args: [] }`
/// `Point<i32>` → `PathSegment { ident: "Point", type_args: [i32] }`. The
/// spelling of `type_args` depends on which parser produced the segment —
/// bare `<...>` from `parse_type_path`, turbofish `::<...>` from
/// `parse_value_path` — never both; empty when no type args are provided.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct PathSegment {
	pub ident: Spanned<SymbolU32>,
	pub type_args: Box<[Spanned<TypeExpression>]>,
}

/// A parsed, non-empty `::`-separated path — `i32`, `module::Type`,
/// `Point<i32>`. Its own type rather than a bare `Box<[PathSegment]>`
/// specifically so its span can be a real method: Rust doesn't allow an
/// inherent impl on `[PathSegment]` itself, only on a named local type, and
/// a stored `Spanned` wrapper around the box would just duplicate what
/// `span()` recomputes on demand from the segments themselves.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct Path {
	pub segments: Box<[PathSegment]>,
}

impl Path {
	/// The span of the whole path, from its first segment's identifier to
	/// its last — not including any trailing generic arguments.
	pub fn span(&self) -> TextSpan {
		TextSpan::new(
			self.segments.first().unwrap().ident.span.start,
			self.segments.last().unwrap().ident.span.end,
		)
	}
}

/// The `<Type as Trait>` clause of a qualified path (`<Type as
/// Trait>::item`) — its own struct so the whole bracketed clause, the site
/// of a "trait not implemented" error, carries one precise span (exactly
/// `<self_type as trait_path>`, not including the trailing `::item`) rather
/// than that span having to be reconstructed from separately-threaded
/// pieces at every diagnostic call site.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct QualifiedPathRoot {
	pub self_type: Box<Spanned<TypeExpression>>,
	pub trait_path: Box<[PathSegment]>,
	pub span: TextSpan,
}

/// A trait or typeset bound expression.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum BoundExpression {
	/// `Trait` or `module::Trait`
	Path(Box<[PathSegment]>),
	/// `Memory where { Size = u32, Size: UnsignedInt }` — trait bound with
	/// associated-type bindings.
	WithBindings {
		path: Box<BoundExpression>,
		bindings: Box<[AssocTypeBinding]>,
	},
	/// `Bound1 + Bound2 + Bound3` — multiple bounds joined by `+`.
	BoundList(Box<[Spanned<BoundExpression>]>),
}

impl Expression {
	pub fn is_block_like(&self) -> bool {
		match self {
			Expression::Block { .. }
			| Expression::IfElse { .. }
			| Expression::Loop { .. }
			| Expression::Label { .. }
			| Expression::Match { .. } => true,
			_ => false,
		}
	}

	#[inline]
	pub fn as_block_statements(&self) -> &[Separated<Spanned<Statement>>] {
		match self {
			Expression::Block { statements } => statements,
			_ => unreachable!("expected a block expression"),
		}
	}
}

/// A generic type parameter declaration: `T` or `T: Bound1 + Bound2`.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct TypeParam {
	pub name: Spanned<SymbolU32>,
	/// Trait bounds. `None` = unconstrained.
	pub bounds: Option<Spanned<BoundExpression>>,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct FunctionTypeParam {
	pub name: Option<Spanned<SymbolU32>>,
	pub ty: Box<Spanned<TypeExpression>>,
}

/// `Size = u32` (equality) or `Size: UnsignedInt` (bound) inside a `where {
/// }` block — constrains an associated type.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct AssocTypeBinding {
	pub name: Spanned<SymbolU32>,
	pub kind: AssocTypeBindingKind,
}

/// The right-hand side of an [`AssocTypeBinding`].
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum AssocTypeBindingKind {
	/// `Size = u32` — the associated type must equal exactly this type.
	Equals(Spanned<TypeExpression>),
	/// `Size: UnsignedInt` — the associated type must satisfy this bound.
	Bound(Spanned<BoundExpression>),
}

/// `*T` = exclusive pointer/slice/array, `&T` = shared, always read-only.
/// No enforcement of "only one exclusive value at a time" — this is a naming
/// convention carried through the type system, not a move-checker.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum Ownership {
	Exclusive,
	Shared,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum TypeExpression {
	/// `_` — explicit inference placeholder; type-resolution context decides
	/// whether it stays `INFER` or is rejected as `ERROR`.
	Infer,
	/// `i32`, `module::Type`, `Point<i32>`, `module::Wrapper<T>` — a flat path
	/// of segments; any segment (including the first) may carry bare
	/// `<...>` generic arguments. Turbofish is never accepted in type
	/// position, only in expression position (see `parse_value_path`).
	Path(Box<[PathSegment]>),
	/// `(T, U, V)` or `()`
	Tuple {
		elements: Box<[Spanned<TypeExpression>]>,
	},
	/// `fn(i32, i32) -> i32`
	Function {
		params: Box<[Separated<Spanned<FunctionTypeParam>>]>,
		result: Option<Box<Spanned<TypeExpression>>>,
	},
	/// `*u8` or `&u8`; `heap::*u8` tags the memory explicitly instead of
	/// leaving it to ambient resolution — carried on the pointer itself
	/// (rather than as a separate wrapper node) so only a pointer/slice/
	/// array can ever be tagged, a constraint the parser otherwise has to
	/// enforce by hand against an arbitrary inner type expression.
	Pointer {
		ownership: Ownership,
		memory: Option<Box<[PathSegment]>>,
		inner: Box<Spanned<TypeExpression>>,
	},
	/// `*[u8]` or `&[u8]`; see `Pointer` for the optional `heap::` tag.
	Slice {
		ownership: Ownership,
		memory: Option<Box<[PathSegment]>>,
		inner: Box<Spanned<TypeExpression>>,
	},
	/// `*[u8; 5]` or `&[u8; 5]`; see `Pointer` for the optional `heap::` tag.
	Array {
		ownership: Ownership,
		memory: Option<Box<[PathSegment]>>,
		inner: Box<Spanned<TypeExpression>>,
		size: Spanned<usize>,
	},
	/// `<Type as Trait>::Item` — a qualified path that pins down exactly
	/// which trait's item is meant, disambiguating a name that would
	/// otherwise be ambiguous (or first-match) across multiple bounds/impls
	/// on `self_type`.
	QualifiedPath {
		root: QualifiedPathRoot,
		segments: Box<[PathSegment]>,
	},
	/// `<Type>::Item` — a bare bracketed type used as a path root, with no
	/// trait qualification. See `Expression::Grouped` for why this is kept
	/// distinct from `QualifiedPath` rather than making its `trait_path`
	/// optional.
	Grouped {
		inner: Box<Spanned<TypeExpression>>,
		segments: Box<[PathSegment]>,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct PatternField {
	pub name: Spanned<SymbolU32>,
	/// `None` = shorthand `{ x }`, same as `{ x: x }`
	pub pattern: Option<Spanned<Pattern>>,
}

/// One entry of a named struct pattern `Path({ ... })`, exactly as written.
/// `SeparatedGroup`'s `item_handler` is a plain `fn` pointer that yields
/// exactly one item, so the `..` rest marker has to come back through the
/// same channel as a field — that's the only reason this sum type exists.
/// The parser does *not* collapse the sequence (e.g. assume there's at most
/// one `Rest`, or that its position is meaningless): it hands the raw
/// sequence to TIR exactly as parsed, and TIR is the one that decides what a
/// duplicate or misplaced `..` means.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum NamedPatternItem {
	Field(PatternField),
	Rest,
}

/// One entry of a positional struct pattern `Path(...)` — the positional
/// analogue of [`NamedPatternItem`], same "raw sequence, no parser-side
/// assumptions" rationale.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum PositionalPatternItem {
	Element(Pattern),
	Rest,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum Pattern {
	/// `_`
	Wildcard,
	/// `[mut] name`
	Binding {
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
	},
	/// `(pat, pat, ...)`
	Tuple {
		elements: Box<[Separated<Spanned<Pattern>>]>,
	},
	/// `Name(pat, pat, ..)` or `module::Name(pat, ..)` — destructures a
	/// struct by position, written exactly as its construction is
	/// (`Name(1, 2)`), so a pattern and a value read the same way. The items
	/// are the raw parsed sequence: how many `Rest` entries there are and
	/// where is a semantic question TIR answers, not a parse-time assumption.
	Struct {
		path: Box<[PathSegment]>,
		elements: Box<[Separated<Spanned<PositionalPatternItem>>]>,
	},
	/// `Name({ field, other: pat, .. })` — destructures a struct by field
	/// name, as `Name({ x: 1, y: 2 })` constructs it. Same raw sequence as
	/// `Struct`.
	NamedStruct {
		path: Box<[PathSegment]>,
		fields: Box<[Separated<Spanned<NamedPatternItem>>]>,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum Statement {
	/// `{expr}`
	Expression(Box<Spanned<Expression>>),
	/// `local <pattern> [: type] = {expr}`
	LocalDefinition {
		pattern: Spanned<Pattern>,
		ty: Option<Box<Spanned<TypeExpression>>>,
		value: Box<Spanned<Expression>>,
	},
}

impl Statement {
	pub fn is_block_like(&self) -> bool {
		match self {
			Statement::Expression(expr) => expr.inner.is_block_like(),
			Statement::LocalDefinition { .. } => false,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct FunctionParam {
	pub mut_span: Option<TextSpan>,
	pub name: Spanned<SymbolU32>,
	pub ty: Option<Box<Spanned<TypeExpression>>>,
}

/// The payload of an attribute, following the meta item grammar.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum AttributeValue {
	/// `#[inline]` — name only, no payload.
	Word,
	/// `#[tag = "memory"]` — the span of the raw quoted string.
	NameValue(TextSpan),
	/// `#[memory_limits(min_pages = 1, max_pages = 10)]` — name plus a
	/// parenthesized, comma-separated list of `name = value` arguments.
	Args(Box<[Separated<Spanned<AttributeArg>>]>),
}

/// A single attribute on an item, e.g. `#[inline]`, `#[tag = "memory"]`, or
/// `#[memory_limits(min_pages = 1)]`.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct Attribute {
	pub name: Spanned<SymbolU32>,
	pub value: AttributeValue,
}

/// One `name = value` argument inside a parenthesized attribute, e.g.
/// `min_pages = 1` in `#[memory_limits(min_pages = 1)]`.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct AttributeArg {
	pub name: Spanned<SymbolU32>,
	pub value: AttributeArgValue,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum AttributeArgValue {
	/// Range/sign validity for a given attribute is a semantic question,
	/// checked where the attribute is resolved (TIR), not here.
	Int(Spanned<i64>),
	/// The span of the raw quoted string.
	String(TextSpan),
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum ImplItem {
	/// A method or associated function — TIR distinguishes the two after
	/// parsing, by checking whether the first param is named `self`.
	Function {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
		block: Box<Spanned<Expression>>,
	},
	Constant {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<Box<Spanned<TypeExpression>>>,
		value: Box<Spanned<Expression>>,
		attributes: Box<[Attribute]>,
	},
	AssocType {
		/// Always an error to have set — an associated type is only legal in
		/// a trait impl, where visibility comes from the trait. Recorded
		/// anyway so the qualifier can be reported and round-tripped:
		/// dropping it here made the formatter delete `pub` from the source.
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Box<Spanned<TypeExpression>>,
		attributes: Box<[Attribute]>,
	},
}

impl ImplItem {
	pub fn is_block_like(&self) -> bool {
		match self {
			ImplItem::Function { .. } => true,
			ImplItem::Constant { .. } | ImplItem::AssocType { .. } => false,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum TraitItem {
	/// A method with an optional default body.
	Function {
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
		/// `None` = abstract (must be provided by impl); `Some` = default
		/// implementation.
		body: Option<Box<Spanned<Expression>>>,
	},
	/// An associated constant declaration, with an optional default value.
	/// `None` = abstract (must be provided by every impl); `Some` = a
	/// default value impls may omit and inherit as-is.
	Const {
		name: Spanned<SymbolU32>,
		attributes: Box<[Attribute]>,
		ty: Box<Spanned<TypeExpression>>,
		value: Option<Box<Spanned<Expression>>>,
	},
	/// An associated type declaration, optionally with a default value.
	AssociatedType {
		name: Spanned<SymbolU32>,
		attributes: Box<[Attribute]>,
		/// Trait bounds the concrete type must satisfy. `None` = unconstrained.
		bounds: Option<Spanned<BoundExpression>>,
		/// Used when an impl does not provide this associated type.
		value: Option<Box<Spanned<TypeExpression>>>,
	},
}

impl TraitItem {
	pub fn is_block_like(&self) -> bool {
		match self {
			TraitItem::Function { body, .. } => body.is_some(),
			TraitItem::Const { .. } | TraitItem::AssociatedType { .. } => false,
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct FunctionSignature {
	pub name: Spanned<SymbolU32>,
	/// Generic type parameters `<T, U: Bound>`. Empty = monomorphic.
	pub type_params: Box<[TypeParam]>,
	pub params: Box<[Separated<Spanned<FunctionParam>>]>,
	pub result: Option<Box<Spanned<TypeExpression>>>,
}

/// One node of a `use` tree. `use a::b::*` is
/// `Path{a, Path{b, Glob}}`; `use a::{b, c::*}` is `Path{a, Group[Name{b},
/// Path{c, Glob}]}`.
///
/// The two leaf kinds resolve at different times, which is why they stay
/// distinct all the way into TIR rather than collapsing into one "import"
/// node: a `Glob` has to be registered during prescan (`lookup_global_symbol`
/// consults `wildcard_imports` throughout Phase 2, so one registered later
/// would be invisible to earlier lookups), while a `Name` *cannot* be
/// resolved that early — files are prescanned in order, so `use math::add;`
/// in `main.wx` runs before `math.wx`'s items exist.
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum UseTree {
	/// `*` — every visible name in the namespace walked to so far.
	Glob { segment: Spanned<SymbolU32> },
	/// A single imported name, optionally renamed: `add`, `add as plus`.
	Name {
		segment: Spanned<SymbolU32>,
		alias: Option<Spanned<SymbolU32>>,
	},
	/// One `::`-separated segment and whatever follows it.
	Path {
		segment: Spanned<SymbolU32>,
		rest: Box<Spanned<UseTree>>,
	},
	/// `{ .. }` — several subtrees sharing the prefix walked to so far.
	/// `Separated<Spanned<_>>` is what `SeparatedGroup::parse` returns, and
	/// matches `ExportEntry`'s shape. Nothing reads the separator spans: a
	/// `use` group is formatted on one line, so it never emits a trailing
	/// comma the way a broken `export` block does.
	Group {
		segment: Spanned<SymbolU32>,
		branches: Spanned<Box<[Separated<Spanned<UseTree>>]>>,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct ExportEntry {
	pub name: Spanned<SymbolU32>,
	/// The span of the raw quoted external name.
	pub alias: Option<TextSpan>,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum ImportDeclaration {
	Function {
		signature: FunctionSignature,
	},
	Global {
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Box<Spanned<TypeExpression>>,
	},
	Memory {
		name: Spanned<SymbolU32>,
		size: Box<Spanned<TypeExpression>>,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct ImportEntry {
	pub external_name: Option<Spanned<SymbolU32>>,
	pub declaration: ImportDeclaration,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct EnumVariant {
	pub name: Spanned<SymbolU32>,
	pub value: Option<Box<Spanned<Expression>>>,
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub enum Item {
	Function {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
		block: Box<Spanned<Expression>>,
	},
	FunctionDeclaration {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
	},
	Global {
		pub_span: Option<TextSpan>,
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<Box<Spanned<TypeExpression>>>,
		value: Box<Spanned<Expression>>,
		attributes: Box<[Attribute]>,
	},
	Export {
		entry: Spanned<ExportEntry>,
	},
	ExportBlock {
		/// Span of the `export` keyword.
		keyword_span: TextSpan,
		entries: Box<[Separated<Spanned<ExportEntry>>]>,
	},
	Import {
		external_name: TextSpan,
		internal_name: Spanned<SymbolU32>,
		items: Spanned<Box<[Separated<Spanned<ImportEntry>>]>>,
	},
	Enum {
		pub_span: Option<TextSpan>,
		repr: Option<Box<Spanned<TypeExpression>>>,
		name: Spanned<SymbolU32>,
		variants: Box<[Separated<Spanned<EnumVariant>>]>,
		attributes: Box<[Attribute]>,
	},
	/// `impl Type { ... }`
	InherentImpl {
		type_params: Box<[TypeParam]>,
		target: Path,
		items: Box<[Separated<Spanned<ImplItem>>]>,
	},
	/// `impl Trait for Type { ... }` / `impl<T> Trait for Type<T> { ... }`
	TraitImpl {
		type_params: Box<[TypeParam]>,
		/// Plain path to the trait, e.g. `module::Trait`.
		trait_name: Path,
		target: Path,
		items: Box<[Separated<Spanned<ImplItem>>]>,
	},
	/// `struct Point(x: i32, y: i32);`, `struct Pair(i32, i32);` — one form
	/// for every struct. A field's name is optional, field by field, like its
	/// `pub`; a struct is constructed by a call, by position always and by
	/// name when every field has one.
	Struct {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		type_params: Box<[TypeParam]>,
		fields: Box<[Separated<Spanned<StructField>>]>,
	},
	Memory {
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		size: Box<Spanned<TypeExpression>>,
	},
	Const {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<Box<Spanned<TypeExpression>>>,
		value: Box<Spanned<Expression>>,
		attributes: Box<[Attribute]>,
	},
	Module {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		items: Spanned<Box<[Separated<Spanned<Item>>]>>,
	},
	ModuleDeclaration {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
	},
	Trait {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		/// Supertrait bounds: `trait X: Y + Z { ... }`.  `None` = no bounds.
		supertraits: Option<Spanned<BoundExpression>>,
		items: Box<[Separated<Spanned<TraitItem>>]>,
	},
	/// `typeset Name: A + B { T1, T2, ... }` — a closed compile-time set of
	/// concrete types. The optional bound clause after `:` applies to every
	/// member: each member must satisfy `A + B`, and a body generic over the
	/// typeset may rely on those bounds. `None` = no bounds required.
	TypeSet {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		bounds: Option<Spanned<BoundExpression>>,
		/// `SeparatedGroup` always wraps each item in `Spanned<T>`; `Path`'s
		/// own `span()` makes that wrapper redundant here, but there's no
		/// avoiding it without changing `SeparatedGroup` itself.
		members: Box<[Separated<Spanned<Path>>]>,
	},
	/// `use math::add;`, `use math::*;`, `use math::{trig::sin, ops::*};` —
	/// brings names from another namespace into this one.
	Use {
		pub_span: Option<TextSpan>,
		tree: Spanned<UseTree>,
	},
	/// `type Name = TypeExpr;` or `type Name<T> = TypeExpr;` — a transparent
	/// alias. `body` is `None` only for a bodiless `#[intrinsic] type Name;`
	/// declaration (primitives).
	TypeAlias {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		type_params: Box<[TypeParam]>,
		body: Option<Box<Spanned<TypeExpression>>>,
		attributes: Box<[Attribute]>,
	},
}

#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct StructField {
	pub pub_span: Option<TextSpan>,
	/// `None` for a positional field: `struct Pair(i32, i32);`.
	pub name: Option<Spanned<SymbolU32>>,
	pub ty: Box<Spanned<TypeExpression>>,
}

impl Item {
	pub fn is_block_like(&self) -> bool {
		match self {
			Item::Function { .. }
			| Item::ExportBlock { .. }
			| Item::Import { .. }
			| Item::Enum { .. }
			| Item::InherentImpl { .. }
			| Item::TraitImpl { .. }
			| Item::Module { .. }
			| Item::Trait { .. }
			| Item::TypeSet { .. } => true,
			Item::Global { .. }
			| Item::Export { .. }
			| Item::Const { .. }
			| Item::Memory { .. }
			| Item::FunctionDeclaration { .. }
			| Item::ModuleDeclaration { .. }
			| Item::TypeAlias { .. }
			| Item::Struct { .. }
			| Item::Use { .. } => false,
		}
	}

	/// Backfills the attributes parsed ahead of an item onto whichever item
	/// kinds carry an `attributes` field. No-op for kinds that don't.
	pub fn set_attributes(&mut self, attrs: Box<[Attribute]>) {
		match self {
			Item::Function { attributes, .. }
			| Item::FunctionDeclaration { attributes, .. }
			| Item::Trait { attributes, .. }
			| Item::TypeSet { attributes, .. }
			| Item::Const { attributes, .. }
			| Item::Global { attributes, .. }
			| Item::Enum { attributes, .. }
			| Item::TypeAlias { attributes, .. }
			| Item::Memory { attributes, .. }
			| Item::Struct { attributes, .. } => {
				*attributes = attrs;
			}
			Item::Export { .. }
			| Item::ExportBlock { .. }
			| Item::Import { .. }
			| Item::InherentImpl { .. }
			| Item::TraitImpl { .. }
			| Item::Module { .. }
			| Item::ModuleDeclaration { .. }
			| Item::Use { .. } => {}
		}
	}
}

#[cfg_attr(test, derive(serde::Serialize))]
pub struct AST {
	pub file_id: FileId,
	pub diagnostics: Vec<Diagnostic<FileId>>,
	pub items: Vec<Separated<Spanned<Item>>>,
	#[cfg_attr(test, serde(skip))]
	pub comments: CommentMap,
}

#[derive(Clone, Copy, PartialEq, PartialOrd)]
enum BindingPower {
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
	Cast,
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

macro_rules! define_keywords {
	(
		$(
			$(#[$meta:meta])*
			$variant:ident => $text:literal
		),+ $(,)?
	) => {
		#[derive(Clone, Copy)]
		pub enum Keyword {
			$(
				$(#[$meta])*
				$variant,
			)+
		}

		impl TryFrom<&str> for Keyword {
			type Error = ();

			fn try_from(text: &str) -> Result<Self, <Keyword as TryFrom<&str>>::Error> {
				match text {
					$( $text => Ok(Keyword::$variant), )+
					_ => Err(()),
				}
			}
		}

		impl Keyword {
			/// A fresh interner with every keyword string pre-interned, in
			/// declaration order, so each keyword's raw index lines up with
			/// what [`Keyword::symbol`] fabricates directly from the enum
			/// discriminant. Any interner backing a compilation must be
			/// built from this rather than `StringInterner::new()` — one
			/// that skips this seeding step will hand out those same raw
			/// indices to the first ordinary identifiers it interns instead.
			pub(crate) fn create_interner() -> StringInterner {
				const KEYWORDS: &[&str] = &[$($text),+];
				let mut strings = StringInterner::with_capacity(KEYWORDS.len());
				for keyword in KEYWORDS {
					strings.get_or_intern(keyword);
				}
				strings
			}
		}
	};
}

pub type StringInterner = string_interner::StringInterner<
	string_interner::backend::StringBackend<SymbolU32>,
>;

define_keywords! {
	Error => "<error>",
	Export => "export",
	Import => "import",
	Local => "local",
	Global => "global",
	Mut => "mut",
	Enum => "enum",
	Fn => "fn",
	Loop => "loop",
	Break => "break",
	Continue => "continue",
	Return => "return",
	If => "if",
	Else => "else",
	As => "as",
	Unreachable => "unreachable",
	True => "true",
	False => "false",
	Impl => "impl",
	SelfLower => "self",
	SelfPascal => "Self",
	Struct => "struct",
	Pub => "pub",
	Memory => "memory",
	Const => "const",
	Mod => "mod",
	Trait => "trait",
	For => "for",
	Type => "type",
	Typeset => "typeset",
	Match => "match",
	Underscore => "_",
	Use => "use",
	Where => "where",
	Crate => "crate",
	Super => "super",
	Block => "block",
}

impl Keyword {
	#[inline]
	pub fn symbol(self) -> SymbolU32 {
		SymbolU32::try_from_usize(self as usize)
			.expect("keyword index always fits in a SymbolU32")
	}
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
			Some(Keyword::Fn) => Ok(Parser::parse_function_definition_item),
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
	fn peek_expect(
		&mut self,
		expected_token: Token,
	) -> Result<Spanned<Token>, ()> {
		let token = self.lexer.peek();
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

	fn intern_identifier(&mut self, span: TextSpan) -> SymbolU32 {
		let text = span.extract_str(self.source);
		if Keyword::try_from(text).is_ok() {
			self.ast
				.diagnostics
				.push(report_reserved_identifier(self.ast.file_id, span));
		}

		self.strings.get_or_intern(text)
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

			let value = if parser.lexer.next_if(Token::Eq).is_some() {
				let str_token = parser.next_expect(Token::String)?;
				AttributeValue::NameValue(str_token.span)
			} else if parser.lexer.peek().inner == Token::OpenParen {
				let args = SeparatedGroup {
					open_token: Token::OpenParen,
					close_token: Token::CloseParen,
					separator_token: Token::Comma,
					should_warn_missing_separator: None,
					item_handler: Parser::parse_attribute_arg,
				}
				.parse(parser)?;
				AttributeValue::Args(args.inner)
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

	fn parse_attribute_arg(
		parser: &mut Parser,
	) -> Result<Spanned<AttributeArg>, ()> {
		let name_span = parser.next_expect(Token::Identifier)?.span;
		let name = Spanned {
			inner: parser.intern_identifier(name_span),
			span: name_span,
		};
		parser.next_expect(Token::Eq)?;
		let value_token = parser.lexer.next();
		let value = match value_token.inner {
			Token::Int => {
				let raw = value_token
					.span
					.extract_str(parser.source)
					.parse::<i64>()
					.unwrap_or(0);
				AttributeArgValue::Int(Spanned {
					inner: raw,
					span: value_token.span,
				})
			}
			Token::String => AttributeArgValue::String(value_token.span),
			_ => {
				parser.ast.diagnostics.push(report_unexpected_token(
					parser.ast.file_id,
					value_token,
					Token::Int,
				));
				return Err(());
			}
		};
		let value_span = match &value {
			AttributeArgValue::Int(v) => v.span,
			AttributeArgValue::String(v) => *v,
		};
		let span = TextSpan::new(name_span.start, value_span.end);
		Ok(Spanned {
			inner: AttributeArg { name, value },
			span,
		})
	}

	fn parse_function_param_item(
		parser: &mut Parser,
	) -> Result<Spanned<FunctionParam>, ()> {
		let token = parser.peek_expect(Token::Identifier)?;
		let mut_span =
			match Keyword::try_from(token.span.extract_str(parser.source)) {
				Ok(Keyword::Mut) => Some(parser.lexer.next().span),
				_ => None,
			};

		let name_span = parser.next_expect(Token::Identifier)?.span;
		let text = name_span.extract_str(parser.source);
		match Keyword::try_from(text) {
			Ok(Keyword::SelfLower) | Err(_) => {}
			Ok(_) => {
				parser.ast.diagnostics.push(report_reserved_identifier(
					parser.ast.file_id,
					name_span,
				));
			}
		}

		let name = Spanned {
			inner: parser.strings.get_or_intern(text),
			span: name_span,
		};

		let colon = parser.lexer.next_if(Token::Colon);
		let (ty, span) = match colon {
			Some(_) => {
				let ty = parser.parse_type_expression()?;
				let span = TextSpan::new(name_span.start, ty.span.end);
				(Some(Box::new(ty)), span)
			}
			None => (None, name_span),
		};

		Ok(Spanned {
			inner: FunctionParam { mut_span, name, ty },
			span,
		})
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

		let result = self
			.lexer
			.next_if(Token::MinusRightArrow)
			.ok_or(())
			.and_then(|_| {
				Ok(Some(Box::new(Parser::parse_type_expression(self)?)))
			})
			.unwrap_or(None);

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

	/// Parse `<T, U: Bound1 + Bound2>` — generic type parameter declarations.
	fn parse_type_params(&mut self) -> Result<Box<[TypeParam]>, ()> {
		let open_span = self.next_expect(Token::LeftArrow)?.span;
		let mut params: Vec<TypeParam> = Vec::new();

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

			let name_span = self.next_expect(Token::Identifier)?.span;
			let name_symbol = self.intern_identifier(name_span);
			let name = Spanned {
				inner: name_symbol,
				span: name_span,
			};

			let bounds: Option<Spanned<BoundExpression>> =
				if self.lexer.next_if(Token::Colon).is_some() {
					Some(self.parse_bounds_expression()?)
				} else {
					None
				};

			params.push(TypeParam { name, bounds });

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

	/// Parse `::<Type1, Type2>` turbofish arguments (the `<...>` part after
	/// `::` is already consumed by the caller). Returns the args and the
	/// closing `>` span.
	fn parse_type_args(
		&mut self,
	) -> Result<(Box<[Spanned<TypeExpression>]>, TextSpan), ()> {
		let open_span = self.next_expect(Token::LeftArrow)?.span;
		let mut args: Vec<Spanned<TypeExpression>> = Vec::new();

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

			args.push(self.parse_type_expression()?);

			if self.lexer.peek().inner == Token::Comma {
				self.lexer.next();
			}
		};

		Ok((args.into_boxed_slice(), close_span))
	}

	/// Parse `where { Name = Type, Name: Bound, ... }` — the bindings block
	/// following a type. Returns a `Spanned` whose span covers from `{`
	/// through `}`. The `where` keyword must already be confirmed as the next
	/// token by the caller.
	fn parse_where_bindings(
		&mut self,
	) -> Result<Spanned<Box<[AssocTypeBinding]>>, ()> {
		self.lexer.next(); // consume `where`
		let open_span = self.next_expect(Token::OpenBrace)?.span;
		let mut bindings: Vec<AssocTypeBinding> = Vec::new();

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

			let name_span = self.next_expect(Token::Identifier)?.span;
			let name = Spanned {
				inner: self.intern_identifier(name_span),
				span: name_span,
			};
			let kind = if self.lexer.next_if(Token::Colon).is_some() {
				AssocTypeBindingKind::Bound(self.parse_bounds_expression()?)
			} else {
				self.next_expect(Token::Eq)?;
				AssocTypeBindingKind::Equals(self.parse_type_expression()?)
			};
			self.lexer.next_if(Token::Comma);
			bindings.push(AssocTypeBinding { name, kind });
		};

		Ok(Spanned {
			inner: bindings.into_boxed_slice(),
			span: TextSpan::new(open_span.start, close_span.end),
		})
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
			let mut type_args: Box<[Spanned<TypeExpression>]> = Box::new([]);
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

	/// Parse one or more `+`-separated bounds: `Bound1 + Bound2 + ...`.
	/// Returns a single `BoundExpression` when only one bound is present,
	/// or `BoundExpression::BoundList` for two or more.
	fn parse_bounds_expression(
		&mut self,
	) -> Result<Spanned<BoundExpression>, ()> {
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
					Ok(Keyword::Fn) => {
						return Parser::parse_function_type_expression(self);
					}
					// `Self` is valid in type paths for `Self::AssocType`, etc.;
					// `crate`/`super` are path roots the resolver
					// pre-populates every namespace with (see
					// `intern_path_segment`) — none of the three are ever
					// reserved here, so they intern like ordinary text.
					Ok(Keyword::SelfPascal)
					| Ok(Keyword::Crate)
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
			_ => {
				let token = self.lexer.next();
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
			let mut type_args: Box<[Spanned<TypeExpression>]> = Box::new([]);
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
			self.lexer.next(); // consume `::`
			match self.lexer.peek().inner {
				Token::Identifier => {
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
				_ => {
					let token = self.lexer.next();
					self.ast.diagnostics.push(
						report_expected_path_segment_or_memory_tag(
							self.ast.file_id,
							token,
						),
					);
					return Err(());
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
	/// `open_span`) has already been consumed. Which one this becomes hinges
	/// entirely on whether `as` follows `self_type`.
	fn parse_qualified_path_type_expression(
		&mut self,
		open_span: TextSpan,
	) -> Result<Spanned<TypeExpression>, ()> {
		let self_type = self.parse_type_expression()?;
		if matches!(self.peek_keyword(), Some(Keyword::As)) {
			self.lexer.next(); // consume `as`
			let trait_path = self.parse_type_path()?;
			let close_span = self.expect_close_angle(open_span);
			self.next_expect(Token::ColonColon)?;
			let segments = self.parse_type_path()?;
			let span = TextSpan::new(open_span.start, segments.span().end);
			Ok(Spanned {
				inner: TypeExpression::QualifiedPath {
					root: QualifiedPathRoot {
						self_type: Box::new(self_type),
						trait_path: trait_path.segments,
						span: TextSpan::new(open_span.start, close_span.end),
					},
					segments: segments.segments,
				},
				span,
			})
		} else {
			self.expect_close_angle(open_span);
			self.next_expect(Token::ColonColon)?;
			let segments = self.parse_type_path()?;
			let span = TextSpan::new(open_span.start, segments.span().end);
			Ok(Spanned {
				inner: TypeExpression::Grouped {
					inner: Box::new(self_type),
					segments: segments.segments,
				},
				span,
			})
		}
	}

	/// Parses a leading `*`/`&` sigil (not yet consumed — the caller only
	/// peeks to route here) and everything after it: a bare type (`*T`,
	/// `&T` → `Pointer`), or a bracketed one (`*[T]`/`&[T]` → `Slice`,
	/// `*[T; N]`/`&[T; N]` → `Array`). `memory` is the path already parsed
	/// before an explicit `heap::` tag, if any — its first segment's start
	/// becomes the whole expression's span start instead of the sigil's
	/// own, since the tag is written before it.
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

		if self.lexer.peek().inner != Token::OpenBracket {
			let inner = self.parse_type_expression()?;
			let span = TextSpan::new(start, inner.span.end);
			return Ok(Spanned {
				inner: TypeExpression::Pointer {
					ownership,
					memory,
					inner: Box::new(inner),
				},
				span,
			});
		}

		self.lexer.next(); // consume `[`
		let inner = self.parse_type_expression()?;
		let next = self.lexer.next();
		match next.inner {
			Token::CloseBracket => {
				let span = TextSpan::new(start, next.span.end);
				Ok(Spanned {
					inner: TypeExpression::Slice {
						ownership,
						memory,
						inner: Box::new(inner),
					},
					span,
				})
			}
			Token::SemiColon => {
				let size_token = self.lexer.next();
				let size_value = size_token
					.span
					.extract_str(self.source)
					.parse::<usize>()
					.map_err(|_| {
						self.ast.diagnostics.push(
							report_invalid_integer_literal(
								self.ast.file_id,
								size_token.span,
							),
						);
					})?;
				let size = Spanned {
					inner: size_value,
					span: size_token.span,
				};
				let close_span = self.next_expect(Token::CloseBracket)?.span;
				let span = TextSpan::new(start, close_span.end);
				Ok(Spanned {
					inner: TypeExpression::Array {
						ownership,
						memory,
						inner: Box::new(inner),
						size,
					},
					span,
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

		let span = grouped.span;
		let mut elements = Vec::from(grouped.inner);

		if elements.len() == 1 && elements[0].separator.is_none() {
			let single = elements.remove(0);
			return Ok(Spanned {
				inner: single.inner.inner,
				span,
			});
		}

		let types: Box<[Spanned<TypeExpression>]> =
			elements.into_iter().map(|s| s.inner).collect();
		Ok(Spanned {
			inner: TypeExpression::Tuple { elements: types },
			span,
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
					Ok(Keyword::Unreachable) => Some((
						Parser::parse_unreachable_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::True) => Some((
						Parser::parse_true_expression,
						BindingPower::Primary,
					)),
					Ok(Keyword::False) => Some((
						Parser::parse_false_expression,
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
			Token::Identifier => {
				match Keyword::try_from(token.span.extract_str(self.source)) {
					Ok(Keyword::As) => Some((
						Parser::parse_cast_expression,
						BindingPower::Cast,
					)),
					_ => None,
				}
			}
			Token::Colon => {
				Some((Parser::parse_labelled_expression, BindingPower::Primary))
			}
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

	fn parse_expression(
		&mut self,
		limit_bp: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		let token = self.lexer.peek();
		let nud_handler = match self.nud_lookup(token) {
			Some((nud_handler, _)) => nud_handler,
			None => return Err(()),
		};
		let mut left = nud_handler(self)?;

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
		let self_type = parser.parse_type_expression()?;
		if matches!(parser.peek_keyword(), Some(Keyword::As)) {
			parser.lexer.next(); // consume `as`
			let trait_path = parser.parse_type_path()?;
			let close_span = parser.expect_close_angle(open_span);
			parser.next_expect(Token::ColonColon)?;
			let segments = parser.parse_value_path()?;
			let span = TextSpan::new(open_span.start, segments.span().end);
			Ok(Spanned {
				inner: Expression::QualifiedPath {
					root: QualifiedPathRoot {
						self_type: Box::new(self_type),
						trait_path: trait_path.segments,
						span: TextSpan::new(open_span.start, close_span.end),
					},
					segments: segments.segments,
				},
				span,
			})
		} else {
			parser.expect_close_angle(open_span);
			parser.next_expect(Token::ColonColon)?;
			let segments = parser.parse_value_path()?;
			let span = TextSpan::new(open_span.start, segments.span().end);
			Ok(Spanned {
				inner: Expression::Grouped {
					inner: Box::new(self_type),
					segments: segments.segments,
				},
				span,
			})
		}
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
			| Ok(Keyword::Crate)
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
			parser.lexer.next(); // consume `::`

			match parser.lexer.peek().inner {
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
				Token::Identifier => {
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
				// Anything else after `::` is malformed
				_ => {
					let bad = parser.lexer.peek();
					parser.ast.diagnostics.push(report_invalid_namespace(
						parser.ast.file_id,
						bad.span,
					));
					return Err(());
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
	) -> Result<(Box<[Separated<Spanned<NamedArgument>>]>, u32), ()> {
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
		Ok((named.inner, close_span.end))
	}

	/// One positional argument. A named list here follows other arguments,
	/// which is a mix: reported, and read so the call still parses.
	fn parse_positional_argument(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		if parser.lexer.peek().inner != Token::OpenBrace {
			return parser.parse_expression(BindingPower::Default);
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

	/// `name: expr`, or the shorthand `name` for `name: name`.
	fn parse_named_argument(
		parser: &mut Parser,
	) -> Result<Spanned<NamedArgument>, ()> {
		let name_token = parser.next_expect(Token::Identifier)?;
		let name = Spanned {
			inner: parser.intern_identifier(name_token.span),
			span: name_token.span,
		};
		let (value, span) = if parser.lexer.next_if(Token::Colon).is_some() {
			let value = parser.parse_expression(BindingPower::Default)?;
			let span = TextSpan::new(name_token.span.start, value.span.end);
			(Some(Box::new(value)), span)
		} else {
			(None, name_token.span)
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
				arguments: named.inner,
			},
		})
	}

	fn parse_object_access_expression(
		parser: &mut Parser,
		object: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		_ = parser.lexer.next(); // consume the dot
		let token = parser.lexer.next();
		let span = TextSpan::new(object.span.start, token.span.end);
		match token.inner {
			Token::Star => Ok(Spanned {
				inner: Expression::Deref {
					pointer: Box::new(object),
				},
				span,
			}),
			Token::Amper => Ok(Spanned {
				inner: Expression::AddressOf {
					value: Box::new(object),
				},
				span,
			}),
			Token::Identifier => {
				let member_symbol = parser.intern_identifier(token.span);
				Ok(Spanned {
					inner: Expression::ObjectAccess {
						object: Box::new(object),
						member: Spanned {
							inner: member_symbol,
							span: token.span,
						},
					},
					span,
				})
			}
			_ => {
				parser.ast.diagnostics.push(report_unexpected_token(
					parser.ast.file_id,
					token,
					Token::Identifier,
				));
				Err(())
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

		let right = match parser.parse_expression(bp) {
			Ok(expr) => expr,
			Err(_) => {
				parser.ast.diagnostics.push(
					report_incomplete_binary_expression(
						parser.ast.file_id,
						operator_token.span,
					),
				);
				return Err(());
			}
		};

		if bp == BindingPower::Comparison {
			match &left.inner {
				Expression::Binary {
					operator: left_operator,
					..
				} if BindingPower::from(left_operator.inner)
					== BindingPower::Comparison =>
				{
					parser.ast.diagnostics.push(report_chained_comparisons(
						parser.ast.file_id,
						left_operator.span,
						operator_token.span,
					));
				}
				_ => {}
			}
			match &right.inner {
				Expression::Binary {
					operator: right_operator,
					..
				} if BindingPower::from(right_operator.inner)
					== BindingPower::Comparison =>
				{
					parser.ast.diagnostics.push(report_chained_comparisons(
						parser.ast.file_id,
						operator_token.span,
						right_operator.span,
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
		fn parse_integer_literal(s: &str) -> Option<u64> {
			let s = s.replace('_', "");
			if let Some(rest) =
				s.strip_prefix("0b").or_else(|| s.strip_prefix("0B"))
			{
				u64::from_str_radix(rest, 2).ok()
			} else if let Some(rest) =
				s.strip_prefix("0x").or_else(|| s.strip_prefix("0X"))
			{
				u64::from_str_radix(rest, 16).ok()
			} else {
				s.parse::<u64>().ok()
			}
		}
		let token = parser.lexer.next();
		let value = match token.inner {
			Token::Int => {
				parse_integer_literal(token.span.extract_str(parser.source))
			}
			_ => unreachable!(),
		};

		let value = match value {
			Some(value) => value,
			None => {
				parser.ast.diagnostics.push(report_invalid_integer_literal(
					parser.ast.file_id,
					token.span,
				));

				0
			}
		};

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
		// parsed against its resolved target type in TIR
		// (`coerce_untyped_float_expr`), where f32-vs-f64 rounding is finally
		// known.
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
		match parser.parse_expression(BindingPower::Default) {
			Ok(expr) => {
				let span = TextSpan::new(return_span.start, expr.span.end);
				Ok(Spanned {
					inner: Expression::Return {
						value: Some(Box::new(expr)),
					},
					span,
				})
			}
			Err(_) => Ok(Spanned {
				inner: Expression::Return { value: None },
				span: return_span,
			}),
		}
	}

	fn parse_break_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let break_keyword = parser.lexer.next();
		let label = match parser.lexer.next_if(Token::Colon) {
			Some(_) => {
				let label_span = parser.next_expect(Token::Identifier)?.span;
				let label_symbol = parser.intern_identifier(label_span);

				Some(Spanned {
					inner: label_symbol,
					span: label_span,
				})
			}
			None => None,
		};
		let value = parser.parse_expression(BindingPower::Default).ok();

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
		let label = match parser.lexer.next_if(Token::Colon) {
			Some(_) => {
				let label_span = parser.next_expect(Token::Identifier)?.span;
				let label_symbol = parser.intern_identifier(label_span);

				Some(Spanned {
					inner: label_symbol,
					span: label_span,
				})
			}
			None => None,
		};

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
			item_handler: |parser| {
				parser.parse_expression(BindingPower::Default)
			},
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		let span = grouped.span;
		let mut elements = Vec::from(grouped.inner);

		// (expr) with no trailing comma — grouping, not a tuple
		if elements.len() == 1 && elements[0].separator.is_none() {
			let single = elements.remove(0);
			return Ok(Spanned {
				inner: Expression::Grouping {
					value: Box::new(single.inner),
				},
				span,
			});
		}

		// () or (expr,) or (a, b, ...) — tuple
		let exprs: Box<[Spanned<Expression>]> =
			elements.into_iter().map(|s| s.inner).collect();
		Ok(Spanned {
			inner: Expression::Tuple { elements: exprs },
			span,
		})
	}

	fn parse_cast_expression(
		parser: &mut Parser,
		value: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		_ = parser.lexer.next();
		let ty = parser.parse_type_expression()?;

		let span = TextSpan::new(value.span.start, ty.span.end);
		Ok(Spanned {
			inner: Expression::Cast {
				value: Box::new(value),
				ty: Box::new(ty),
			},
			span,
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

		let operand = match parser.parse_expression(BindingPower::Unary) {
			Ok(operand) => operand,
			Err(_) => {
				parser.ast.diagnostics.push(
					report_incomplete_unary_expression(
						parser.ast.file_id,
						operator_token.span,
					),
				);
				return Err(());
			}
		};

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

	fn parse_labelled_expression(
		parser: &mut Parser,
		label_expr: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		let label = match label_expr.inner {
			Expression::Path(segs)
				if segs.len() == 1 && segs[0].type_args.is_empty() =>
			{
				segs[0].ident
			}
			_ => {
				parser.ast.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::InvalidLabel.code())
						.with_message("invalid label")
						.with_label(
							Label::primary(parser.ast.file_id, label_expr.span)
								.with_message(
									"a label must be a single identifier, not a path",
								),
						),
				);
				return Err(());
			}
		};
		let colon_token = parser.next_expect(Token::Colon)?;

		let block = parser.parse_expression(BindingPower::Default)?;
		match block.inner {
			Expression::Block { .. }
			| Expression::IfElse { .. }
			| Expression::Loop { .. } => {}
			_ => {
				let mut diag = Diagnostic::error()
					.with_code(DiagnosticCode::IncompleteExpression.code())
					.with_message(
						"expected a block-like expression after a label",
					)
					.with_label(Label::primary(parser.ast.file_id, block.span));
				match &block.inner {
					Expression::Path(_)
					| Expression::Call { .. }
					| Expression::MethodCall(_) => {
						diag = diag.with_label(
							Label::secondary(
								parser.ast.file_id,
								colon_token.span,
							)
							.with_message("use `::` here for namespace access"),
						);
					}
					_ => {}
				}

				parser.ast.diagnostics.push(diag);
				return Err(());
			}
		}

		let span = TextSpan::new(label.span.start, block.span.end);
		Ok(Spanned {
			inner: Expression::Label {
				label,
				block: Box::new(block),
			},
			span,
		})
	}

	/// `block { ... }`: a plain block in expression position. Blocks that
	/// belong to a construct (`if`, `loop`, a match arm, a function body) are
	/// parsed by it directly and need no keyword.
	fn parse_keyword_block_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let keyword_span = parser.lexer.next().span;
		let block = Parser::parse_block_expression(parser)?;
		Ok(Spanned {
			span: TextSpan::new(keyword_span.start, block.span.end),
			inner: block.inner,
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
			inner: Expression::Block {
				statements: statements.inner,
			},
			span: statements.span,
		})
	}

	fn parse_loop_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let loop_keyword = parser.lexer.next();
		let block = Parser::parse_block_expression(parser)?;

		let span = TextSpan::new(loop_keyword.span.start, block.span.end);
		Ok(Spanned {
			inner: Expression::Loop {
				block: Box::new(block),
			},
			span,
		})
	}

	fn parse_if_else_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let if_keyword = parser.lexer.next();
		let condition = parser.parse_expression(BindingPower::Default)?;
		let then_block = Parser::parse_block_expression(parser)?;
		let else_keyword = Keyword::try_from(
			parser.lexer.peek().span.extract_str(parser.source),
		);

		match else_keyword {
			Ok(Keyword::Else) => {
				let _ = parser.lexer.next();
				let else_block = Parser::parse_block_expression(parser)?;
				let span =
					TextSpan::new(if_keyword.span.start, else_block.span.end);
				Ok(Spanned {
					inner: Expression::IfElse {
						condition: Box::new(condition),
						then_block: Box::new(then_block),
						else_block: Some(Box::new(else_block)),
					},
					span,
				})
			}
			_ => {
				let span =
					TextSpan::new(if_keyword.span.start, then_block.span.end);
				Ok(Spanned {
					inner: Expression::IfElse {
						condition: Box::new(condition),
						then_block: Box::new(then_block),
						else_block: None,
					},
					span,
				})
			}
		}
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
					let pattern =
						parser.parse_expression(BindingPower::Default)?;
					parser.next_expect(Token::MinusRightArrow)?;
					let body = Parser::parse_block_expression(parser)?;
					let span = TextSpan::new(pattern.span.start, body.span.end);
					Ok(Spanned {
						inner: MatchArm {
							pattern: Box::new(pattern),
							body: Box::new(body),
						},
						span,
					})
				},
			// Arm bodies are always `{ }` blocks, so — like `parse_enum_item`
			// — a missing trailing comma before the next arm is never
			// ambiguous with statement continuation; no warning needed.
			should_warn_missing_separator: None,
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

	/// Handles `expr::<T, U>` turbofish when `expr` is NOT a bare identifier
	/// (e.g. `obj.method::<T>()`).  Bare-identifier paths are already fully
	/// consumed by `parse_identifier_expression`, so this led only fires on
	/// non-path left-hand sides.
	fn parse_type_application_expression(
		parser: &mut Parser,
		left: Spanned<Expression>,
		_: BindingPower,
	) -> Result<Spanned<Expression>, ()> {
		_ = parser.lexer.next(); // consume `::`

		if parser.lexer.peek().inner == Token::LeftArrow {
			let (args, close_span) = parser.parse_type_args()?;
			let span = TextSpan::new(left.span.start, close_span.end);
			return Ok(Spanned {
				inner: Expression::TypeApplication {
					callee: Box::new(left),
					args,
				},
				span,
			});
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
				Ok((object, method, type_args)) => {
					Expression::NamedMethodCall(Box::new(MethodCallExpr {
						object,
						method,
						type_args,
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
		let inner = match Parser::method_callee(callee) {
			Ok((object, method, type_args)) => {
				Expression::MethodCall(Box::new(MethodCallExpr {
					object,
					method,
					type_args,
					arguments: arguments.inner,
				}))
			}
			Err(callee) => Expression::Call {
				callee: Box::new(callee),
				arguments: arguments.inner,
			},
		};
		Ok(Spanned {
			inner,
			span: TextSpan::new(start, arguments.span.end),
		})
	}

	/// The object, method and type arguments of a callee that names a method
	/// (`object.method`, `object.method::<T>`); any other callee back as is.
	#[allow(clippy::type_complexity)]
	fn method_callee(
		callee: Spanned<Expression>,
	) -> Result<
		(
			Box<Spanned<Expression>>,
			Spanned<SymbolU32>,
			Box<[Spanned<TypeExpression>]>,
		),
		Spanned<Expression>,
	> {
		match callee.inner {
			Expression::ObjectAccess { object, member } => {
				Ok((object, member, Box::new([])))
			}
			Expression::TypeApplication {
				callee: inner,
				args,
			} if matches!(inner.inner, Expression::ObjectAccess { .. }) => {
				let Expression::ObjectAccess { object, member } = inner.inner
				else {
					unreachable!()
				};
				Ok((object, member, args))
			}
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
			let count = parser.parse_expression(BindingPower::Default)?;
			let close_span = parser.next_expect(Token::CloseBracket)?.span;
			let span = TextSpan::new(open_span.start, close_span.end);
			return Ok(Spanned {
				inner: Expression::ArrayRepeat {
					value: Box::new(first),
					count: Box::new(count),
				},
				span,
			});
		}

		let mut elements = vec![first];
		while parser.lexer.next_if(Token::Comma).is_some() {
			if parser.lexer.peek().inner == Token::CloseBracket {
				break;
			}
			elements.push(parser.parse_expression(BindingPower::Default)?);
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

		// Detect slice-range form: `[..]`, `[i..]`, `[..n]`, `[i..n]`
		let start = if parser.lexer.peek().inner == Token::DotDot {
			None
		} else {
			Some(Box::new(parser.parse_expression(BindingPower::Default)?))
		};

		if parser.lexer.next_if(Token::DotDot).is_some() {
			let end = if parser.lexer.peek().inner == Token::CloseBracket {
				None
			} else {
				Some(Box::new(parser.parse_expression(BindingPower::Default)?))
			};
			let close_span = parser.next_expect(Token::CloseBracket)?.span;
			let span = TextSpan::new(object.span.start, close_span.end);
			return Ok(Spanned {
				inner: Expression::SliceRange {
					object: Box::new(object),
					start,
					end,
				},
				span,
			});
		}

		// Plain index: `[expr]`
		let index = start.expect("no DotDot consumed so start must be Some");
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

	fn parse_pattern_field(
		parser: &mut Parser,
	) -> Result<Spanned<PatternField>, ()> {
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
			inner: PatternField { name, pattern },
			span,
		})
	}

	fn parse_named_pattern_item(
		parser: &mut Parser,
	) -> Result<Spanned<NamedPatternItem>, ()> {
		if let Some(dot_dot) = parser.lexer.next_if(Token::DotDot) {
			return Ok(Spanned {
				inner: NamedPatternItem::Rest,
				span: dot_dot.span,
			});
		}
		let field = Parser::parse_pattern_field(parser)?;
		Ok(Spanned {
			inner: NamedPatternItem::Field(field.inner),
			span: field.span,
		})
	}

	fn parse_positional_pattern_item(
		parser: &mut Parser,
	) -> Result<Spanned<PositionalPatternItem>, ()> {
		if let Some(dot_dot) = parser.lexer.next_if(Token::DotDot) {
			return Ok(Spanned {
				inner: PositionalPatternItem::Rest,
				span: dot_dot.span,
			});
		}
		let pattern = Parser::parse_pattern(parser)?;
		Ok(Spanned {
			inner: PositionalPatternItem::Element(pattern.inner),
			span: pattern.span,
		})
	}

	/// `{ field, other: pat, .. }`, braces included. The items are handed to
	/// TIR as parsed; see [`NamedPatternItem`].
	fn parse_named_pattern_items(
		parser: &mut Parser,
	) -> Result<Spanned<Box<[Separated<Spanned<NamedPatternItem>>]>>, ()> {
		SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			should_warn_missing_separator: None,
			item_handler: Parser::parse_named_pattern_item,
		}
		.parse(parser)
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
			let fields = Parser::parse_named_pattern_items(parser)?;
			let close_span = parser.next_expect(Token::CloseParen)?.span;
			return Ok(Spanned {
				inner: Pattern::NamedStruct {
					path,
					fields: fields.inner,
				},
				span: TextSpan::new(path_start, close_span.end),
			});
		}
		let elements = SeparatedGroup {
			open_token: Token::OpenParen,
			close_token: Token::CloseParen,
			separator_token: Token::Comma,
			should_warn_missing_separator: None,
			item_handler: Parser::parse_positional_pattern_item,
		}
		.parse_after_open(parser, open_span)?;
		Ok(Spanned {
			inner: Pattern::Struct {
				path,
				elements: elements.inner,
			},
			span: TextSpan::new(path_start, elements.span.end),
		})
	}

	/// `Path::{ ... }`, the old named pattern, with `::` consumed and `{`
	/// next: reported, and read as `Path({ ... })`.
	fn parse_old_struct_pattern(
		parser: &mut Parser,
		path: Box<[PathSegment]>,
	) -> Result<Spanned<Pattern>, ()> {
		let path_start = path.first().unwrap().ident.span.start;
		let named = Parser::parse_named_pattern_items(parser)?;
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
		Ok(Spanned {
			inner: Pattern::NamedStruct {
				path,
				fields: named.inner,
			},
			span,
		})
	}

	fn parse_pattern(parser: &mut Parser) -> Result<Spanned<Pattern>, ()> {
		let token = parser.lexer.peek();
		match token.inner {
			Token::OpenParen => {
				let elements = SeparatedGroup {
					open_token: Token::OpenParen,
					close_token: Token::CloseParen,
					separator_token: Token::Comma,
					should_warn_missing_separator: None,
					item_handler: Parser::parse_pattern,
				}
				.parse(parser)?;
				Ok(Spanned {
					inner: Pattern::Tuple {
						elements: elements.inner,
					},
					span: elements.span,
				})
			}
			Token::Identifier => {
				let text = token.span.extract_str(parser.source);
				if matches!(Keyword::try_from(text), Ok(Keyword::Underscore)) {
					let span = parser.lexer.next().span;
					return Ok(Spanned {
						inner: Pattern::Wildcard,
						span,
					});
				}
				if let Ok(Keyword::Mut) = Keyword::try_from(text) {
					let mut_token = parser.lexer.next();
					let name_span = parser.next_expect(Token::Identifier)?.span;
					let name = Spanned {
						inner: parser.intern_identifier(name_span),
						span: name_span,
					};
					let span =
						TextSpan::new(mut_token.span.start, name_span.end);
					return Ok(Spanned {
						inner: Pattern::Binding {
							mut_span: Some(mut_token.span),
							name,
						},
						span,
					});
				}
				// A bare identifier is a binding, but it may also open a path
				// leading to a struct pattern `Path(...)`.
				let name_token = parser.lexer.next();
				let name = Spanned {
					inner: parser.intern_identifier(name_token.span),
					span: name_token.span,
				};
				let mut segments = vec![PathSegment {
					ident: name,
					type_args: Box::new([]),
				}];

				while parser.lexer.peek().inner == Token::ColonColon {
					parser.lexer.next(); // consume `::`
					match parser.lexer.peek().inner {
						// `::<T, U>` — turbofish for the last segment
						Token::LeftArrow => {
							let (type_args, _close) =
								parser.parse_type_args()?;
							segments.last_mut().unwrap().type_args = type_args;
						}
						// `::{ ... }` — the old named pattern
						Token::OpenBrace => {
							return Parser::parse_old_struct_pattern(
								parser,
								segments.into(),
							);
						}
						// `::ident` — another path segment
						Token::Identifier => {
							let seg_span =
								parser.next_expect(Token::Identifier)?.span;
							segments.push(PathSegment {
								ident: Spanned {
									inner: parser.intern_identifier(seg_span),
									span: seg_span,
								},
								type_args: Box::new([]),
							});
						}
						_ => {
							let bad = parser.lexer.peek();
							parser.ast.diagnostics.push(
								report_invalid_namespace(
									parser.ast.file_id,
									bad.span,
								),
							);
							return Err(());
						}
					}
				}

				// `Path(...)` — a struct pattern. Checked before the "must be a
				// plain binding" fallback below, since a multi-segment path is
				// legal here too (`module::Point(x, y)`).
				if parser.lexer.peek().inner == Token::OpenParen {
					return Parser::parse_struct_pattern(
						parser,
						segments.into(),
					);
				}

				// The path never reached `::{` or `(`, so it can only be a
				// binding — and a binding is a single plain name.
				if segments.len() > 1 || !segments[0].type_args.is_empty() {
					let span = TextSpan::new(
						name_token.span.start,
						segments.last().unwrap().ident.span.end,
					);
					parser.ast.diagnostics.push(
						Diagnostic::error()
							.with_code(
								DiagnosticCode::InvalidBindingPattern.code(),
							)
							.with_message("invalid pattern")
							.with_note(
								"a path may only appear in a pattern as a struct pattern, `Path(...)`",
							)
							.with_label(
								Label::primary(parser.ast.file_id, span)
									.with_message("expected a plain name"),
							),
					);
					return Err(());
				}

				Ok(Spanned {
					inner: Pattern::Binding {
						mut_span: None,
						name,
					},
					span: name_token.span,
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

	fn parse_local_definition_statement(
		parser: &mut Parser,
	) -> Result<Spanned<Statement>, ()> {
		let local_keyword = parser.lexer.next();

		let pattern = Parser::parse_pattern(parser)?;

		let ty = match parser.lexer.next_if(Token::Colon) {
			Some(_) => Some(Box::new(parser.parse_type_expression()?)),
			None => None,
		};

		let value = parser
			.lexer
			.next_if(Token::Eq)
			.ok_or(())
			.and_then(|_| parser.parse_expression(BindingPower::Default))
			.map_err(|_| {
				let token = parser.lexer.peek();
				parser
					.ast
					.diagnostics
					.push(report_missing_local_initializer(
						parser.ast.file_id,
						token.span,
					));
			})?;

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

		let value = parser
			.lexer
			.next_if(Token::Eq)
			.ok_or(())
			.and_then(|_| parser.parse_expression(BindingPower::Default))
			.map_err(|_| {
				let token = parser.lexer.peek();
				parser
					.ast
					.diagnostics
					.push(report_missing_global_initializer(
						parser.ast.file_id,
						token.span,
					));
			})?;

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

	fn parse_unreachable_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let unreachable_keyword = parser.lexer.next();
		Ok(Spanned {
			inner: Expression::Unreachable,
			span: unreachable_keyword.span,
		})
	}

	fn parse_true_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let true_keyword = parser.lexer.next();
		Ok(Spanned {
			inner: Expression::True,
			span: true_keyword.span,
		})
	}

	fn parse_false_expression(
		parser: &mut Parser,
	) -> Result<Spanned<Expression>, ()> {
		let false_keyword = parser.lexer.next();
		Ok(Spanned {
			inner: Expression::False,
			span: false_keyword.span,
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

		let repr = if parser.lexer.next_if(Token::Colon).is_some() {
			Some(Box::new(parser.parse_type_expression()?))
		} else {
			None
		};

		let variants = SeparatedGroup {
			open_token: Token::OpenBrace,
			close_token: Token::CloseBrace,
			separator_token: Token::Comma,
			item_handler:
				|parser: &mut Parser| -> Result<Spanned<EnumVariant>, ()> {
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
						inner: EnumVariant {
							name: Spanned {
								inner: name_symbol,
								span: name_token.span,
							},
							value,
						},
						span,
					})
				},
			should_warn_missing_separator: None,
		}
		.parse(parser)?;

		let span = TextSpan::new(enum_span.start, variants.span.end);

		Ok(Spanned {
			inner: Item::Enum {
				pub_span: None,
				repr,
				name: Spanned {
					inner: name_symbol,
					span: name_span,
				},
				variants: variants.inner,
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
			Some(Keyword::Fn) => {
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

				let result = parser
					.lexer
					.next_if(Token::MinusRightArrow)
					.ok_or(())
					.and_then(|_| {
						Ok(Some(Box::new(Parser::parse_type_expression(
							parser,
						)?)))
					})
					.unwrap_or(None);
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
			if parser.lexer.next_if(Token::Colon).is_some() {
				Some(parser.parse_bounds_expression()?)
			} else {
				None
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
								if parser.lexer.next_if(Token::Colon).is_some()
								{
									Some(parser.parse_bounds_expression()?)
								} else {
									None
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
						Some(Keyword::Fn) => {
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
			if parser.lexer.next_if(Token::Colon).is_some() {
				Some(parser.parse_bounds_expression()?)
			} else {
				None
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

	fn parse_struct_field_pub_span(parser: &mut Parser) -> Option<TextSpan> {
		let peek = parser.lexer.peek();
		match Keyword::try_from(peek.span.extract_str(parser.source)) {
			Ok(Keyword::Pub) => Some(parser.lexer.next().span),
			_ => None,
		}
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
	/// keyword (`fn`, `_`, `Self`, ...) is never a name, and a plain identifier
	/// is a name exactly when `:` follows it; otherwise it was the first
	/// segment of the field's type, which is parsed on from there.
	fn parse_struct_field(
		parser: &mut Parser,
	) -> Result<Spanned<StructField>, ()> {
		let pub_span = Parser::parse_struct_field_pub_span(parser);
		let peek = parser.lexer.peek();
		let plain_identifier = peek.inner == Token::Identifier
			&& Keyword::try_from(peek.span.extract_str(parser.source)).is_err();
		let (name, ty) = if plain_identifier {
			let token = parser.lexer.next();
			let ident = Spanned {
				inner: parser.intern_identifier(token.span),
				span: token.span,
			};
			if parser.lexer.next_if(Token::Colon).is_some() {
				(Some(ident), parser.parse_type_expression()?)
			} else {
				(None, parser.parse_type_path_from(ident)?)
			}
		} else {
			(None, parser.parse_type_expression()?)
		};
		let start = pub_span
			.or(name.map(|name| name.span))
			.unwrap_or(ty.span)
			.start;
		Ok(Spanned {
			span: TextSpan::new(start, ty.span.end),
			inner: StructField {
				pub_span,
				name,
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
			| Item::Global { pub_span: span, .. }
			| Item::Enum { pub_span: span, .. }
			| Item::Struct { pub_span: span, .. }
			| Item::Const { pub_span: span, .. }
			| Item::Module { pub_span: span, .. }
			| Item::ModuleDeclaration { pub_span: span, .. }
			| Item::Trait { pub_span: span, .. }
			| Item::TypeSet { pub_span: span, .. }
			| Item::TypeAlias { pub_span: span, .. }
			| Item::Use { pub_span: span, .. } => *span = Some(pub_span),
			Item::Export { .. }
			| Item::ExportBlock { .. }
			| Item::Import { .. }
			| Item::InherentImpl { .. }
			| Item::TraitImpl { .. }
			| Item::Memory { .. } => {
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
		let token = parser.lexer.peek();
		let keyword = match token.inner {
			Token::Identifier => {
				Keyword::try_from(token.span.extract_str(parser.source)).ok()
			}
			_ => None,
		};
		match keyword {
			Some(Keyword::Fn) => {
				parser.parse_function_signature().map(|signature| Spanned {
					inner: ImportEntry {
						external_name: None,
						declaration: ImportDeclaration::Function {
							signature: signature.inner,
						},
					},
					span: signature.span,
				})
			}
			Some(Keyword::Global) => parser
				.parse_global_import_declaration()
				.map(|decl| Spanned {
					inner: ImportEntry {
						external_name: None,
						declaration: decl.inner,
					},
					span: decl.span,
				}),
			Some(Keyword::Memory) => parser
				.parse_memory_import_declaration()
				.map(|decl| Spanned {
					inner: ImportEntry {
						external_name: None,
						declaration: decl.inner,
					},
					span: decl.span,
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
			Ok(Keyword::Crate | Keyword::Super | Keyword::SelfLower)
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
