//! The lexer: source text to tokens, on demand. Comments and unknown
//! characters are recorded on the side and never reach the parser.

use super::{Comment, CommentKind, Spanned};
use crate::diagnostics::TextSpan;

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
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
	FatArrow,
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
			FatArrow => "=>",
			Comment => "comment",
			DocComment => "doc comment",
			Unknown => "unknown token",
			Eof => "end of file",
		};
		write!(f, "{}", text)
	}
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

pub(super) struct Lexer<'src> {
	pub(super) chars: std::str::Chars<'src>,
	pub(super) src_len: usize,
	pub(super) peeked: Option<Spanned<Token>>,
	pub(super) comments: Vec<Comment>,
	pub(super) has_crlf: bool,
	pub(super) unknown_spans: Vec<TextSpan>,
}

const EOF: char = '\0';

impl<'src> Lexer<'src> {
	pub(super) fn new(input: &'src str) -> Lexer<'src> {
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
	pub(super) fn offset(&self) -> usize {
		self.src_len - self.chars.as_str().len()
	}

	pub(super) fn peek(&mut self) -> Spanned<Token> {
		match &self.peeked {
			Some(token) => *token,
			None => {
				let token = self.next();
				self.peeked = Some(token);
				token
			}
		}
	}

	pub(super) fn next_if(
		&mut self,
		expected: Token,
	) -> Option<Spanned<Token>> {
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

	pub(super) fn next(&mut self) -> Spanned<Token> {
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

	pub(super) fn advance(&mut self) -> Spanned<Token> {
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
			'=' => self.consume_equals(),
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

	/// `=`, `==`, or `=>`.
	#[inline]
	pub(super) fn consume_equals(&mut self) -> Token {
		match self.chars.clone().next().unwrap_or(EOF) {
			'=' => {
				_ = self.chars.next();
				Token::EqEq
			}
			'>' => {
				_ = self.chars.next();
				Token::FatArrow
			}
			_ => Token::Eq,
		}
	}

	#[inline]
	pub(super) fn consume_and_check(
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
	pub(super) fn consume_amper(&mut self) -> Token {
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
	pub(super) fn consume_vbar(&mut self) -> Token {
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
	pub(super) fn consume_dash(&mut self) -> Token {
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
	pub(super) fn consume_open_angle(&mut self) -> Token {
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
	pub(super) fn consume_close_angle(&mut self) -> Token {
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
	pub(super) fn split_double_right_arrow(&mut self) -> TextSpan {
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
	pub(super) fn split_double_left_arrow(&mut self) -> TextSpan {
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
	pub(super) fn eat_while(&mut self, pred: impl Fn(char) -> bool) {
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
	pub(super) fn consume_identifier(&mut self) -> Token {
		self.eat_while(
			|ch| matches!(ch, 'A'..='Z' | 'a'..='z' | '0'..='9' | '_'),
		);
		Token::Identifier
	}

	pub(super) fn consume_number(&mut self) -> Token {
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
					// next char is also `.` (the `..` token).
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

	pub(super) fn consume_string(&mut self) -> Token {
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

	pub(super) fn consume_char(&mut self) -> Token {
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

	pub(super) fn consume_slash(&mut self) -> Token {
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
