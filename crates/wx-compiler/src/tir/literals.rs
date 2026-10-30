use std::borrow::Cow;

use codespan_reporting::diagnostic::Diagnostic;

use super::types::TypeIndex;
use crate::{
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	vfs::FileId,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StringLiteralErrorKind {
	UnknownEscape(char),
	Unterminated,
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub(super) struct StringLiteralError {
	pub kind: StringLiteralErrorKind,
	/// Byte range relative to the opening quote, including UTF-8 characters.
	pub span: TextSpan,
}

impl StringLiteralError {
	pub(super) fn diagnostic(self, literal: SourceSpan) -> Diagnostic<FileId> {
		let reference = SourceSpan::new(
			literal.file_id,
			TextSpan::new(
				literal.span.start + self.span.start,
				literal.span.start + self.span.end,
			),
		);
		let (code, message, label) = match self.kind {
			StringLiteralErrorKind::UnknownEscape(ch) => (
				DiagnosticCode::UnknownCharacterEscape,
				format!("unknown character escape: `{ch}`"),
				"unknown character escape",
			),
			StringLiteralErrorKind::Unterminated => (
				DiagnosticCode::UnterminatedStringLiteral,
				"unterminated string literal".to_string(),
				"missing closing quote",
			),
		};
		Diagnostic::error()
			.with_code(code.code())
			.with_message(message)
			.with_label(reference.primary_label().with_message(label))
	}
}

/// Decodes a quoted string token. Plain strings borrow their contents;
/// an owned buffer is allocated only when an escape needs decoding.
/// Unknown escapes are errors, rather than silently becoming literal backslashes.
pub(super) fn unescape_string_literal(
	source: &str,
) -> Result<Cow<'_, str>, StringLiteralError> {
	let unterminated = || StringLiteralError {
		kind: StringLiteralErrorKind::Unterminated,
		span: TextSpan::new(0, source.len() as u32),
	};
	let mut chars = source.char_indices();
	if chars.next() != Some((0, '"')) {
		return Err(unterminated());
	}
	let mut decoded: Option<String> = None;
	while let Some((offset, ch)) = chars.next() {
		match ch {
			'"' if offset + 1 == source.len() => {
				return Ok(match decoded {
					Some(value) => Cow::Owned(value),
					None => Cow::Borrowed(&source[1..offset]),
				});
			}
			'"' => return Err(unterminated()),
			'\\' => {
				let Some((escape_offset, escape)) = chars.next() else {
					return Err(unterminated());
				};
				let value = match escape {
					'n' => '\n',
					'r' => '\r',
					't' => '\t',
					'\\' => '\\',
					'"' => '"',
					'0' => '\0',
					ch => {
						return Err(StringLiteralError {
							kind: StringLiteralErrorKind::UnknownEscape(ch),
							span: TextSpan::new(
								escape_offset as u32,
								(escape_offset + ch.len_utf8()) as u32,
							),
						});
					}
				};
				let output = decoded.get_or_insert_with(|| {
					let mut value =
						String::with_capacity(source.len().saturating_sub(2));
					value.push_str(&source[1..offset]);
					value
				});
				output.push(value);
			}
			ch => {
				if let Some(output) = &mut decoded {
					output.push(ch);
				}
			}
		}
	}
	Err(unterminated())
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn decodes_supported_escapes_and_borrows_plain_strings() {
		for (source, expected) in [
			(r#""plain λ""#, "plain λ"),
			(r#""""#, ""),
			(r#""\n\r\t\\\"\0""#, "\n\r\t\\\"\0"),
			(r#""slash\\n""#, "slash\\n"),
		] {
			assert_eq!(unescape_string_literal(source).unwrap(), expected);
		}
		assert!(matches!(
			unescape_string_literal(r#""plain""#).unwrap(),
			Cow::Borrowed("plain")
		));
	}

	#[test]
	fn unknown_escapes_have_utf8_byte_ranges() {
		for (source, ch, start, end) in [
			(r#""\o""#, 'o', 2, 3),
			(r#""λ\💥""#, '💥', 4, 8),
			(r#""\x41""#, 'x', 2, 3),
		] {
			let error = unescape_string_literal(source).unwrap_err();
			assert_eq!(error.kind, StringLiteralErrorKind::UnknownEscape(ch));
			assert_eq!(error.span, TextSpan::new(start, end));
		}
	}

	#[test]
	fn escaped_quotes_and_dangling_backslashes_do_not_terminate_strings() {
		for source in ["\"", "\"text", "\"text\\", r#""text\""#, "not quoted"] {
			let error = unescape_string_literal(source).unwrap_err();
			assert_eq!(error.kind, StringLiteralErrorKind::Unterminated);
			assert_eq!(error.span, TextSpan::new(0, source.len() as u32));
		}
	}
}

#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum CharLiteralError {
	Empty,
	TooLong,
}

pub fn parse_char_literal(s: &str) -> Result<char, CharLiteralError> {
	let content = if s.starts_with('\'') && s.ends_with('\'') && s.len() >= 2 {
		&s[1..s.len() - 1]
	} else {
		s
	};

	let mut chars = content.chars();
	let value = match chars.next() {
		None => return Err(CharLiteralError::Empty),
		Some('\\') => match chars.next() {
			None => return Err(CharLiteralError::Empty),
			Some('n') => '\n',
			Some('r') => '\r',
			Some('t') => '\t',
			Some('\\') => '\\',
			Some('\'') => '\'',
			Some('0') => '\0',
			Some('x') => {
				let hi = chars.next().and_then(|c| c.to_digit(16));
				let lo = chars.next().and_then(|c| c.to_digit(16));
				match (hi, lo) {
					(Some(h), Some(l)) => {
						let codepoint = h * 16 + l;
						char::from_u32(codepoint).unwrap()
					}
					_ => return Err(CharLiteralError::TooLong),
				}
			}
			Some(c) => c,
		},
		Some(c) => c,
	};

	if chars.next().is_some() {
		return Err(CharLiteralError::TooLong);
	}

	Ok(value)
}

/// An integer type, for the range of a literal or a constant of it.
#[derive(Clone, Copy)]
pub(super) enum Integer {
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
	pub(super) fn from_type(ty: TypeIndex) -> Option<Self> {
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
	pub(super) fn in_range(self, value: u64, negated: bool) -> bool {
		// A negated literal reaches one past the maximum: `-min`, e.g. `-128`
		// is in range for `i8` although `128` is not.
		let limit = if negated {
			self.min().unsigned_abs()
		} else {
			self.max()
		};
		value <= limit
	}

	pub(super) fn is_signed(self) -> bool {
		match self {
			Self::I8 | Self::I16 | Self::I32 | Self::I64 => true,
			Self::U8 | Self::U16 | Self::U32 | Self::U64 => false,
		}
	}

	pub(super) fn max(self) -> u64 {
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
