pub fn unescape_string_literal(s: &str) -> String {
	// Remove surrounding quotes
	let s = if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
		&s[1..s.len() - 1]
	} else {
		s
	};

	let mut result = String::with_capacity(s.len());
	let mut chars = s.chars();

	while let Some(ch) = chars.next() {
		if ch == '\\' {
			match chars.next() {
				Some('n') => result.push('\n'),
				Some('r') => result.push('\r'),
				Some('t') => result.push('\t'),
				Some('\\') => result.push('\\'),
				Some('"') => result.push('"'),
				Some('0') => result.push('\0'),
				// If we encounter an unknown escape, keep the backslash and the character
				Some(c) => {
					result.push('\\');
					result.push(c);
				}
				None => result.push('\\'),
			}
		} else {
			result.push(ch);
		}
	}

	result
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
