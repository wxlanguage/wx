//! Interned identifier spellings and the reserved keyword symbols.
//!
//! Interners used for parsing/checking must be created with
//! [`Keyword::create_interner`] so keywords occupy their fixed symbol indices.

use string_interner::symbol::{Symbol, SymbolU32};

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
			pub fn create_interner() -> StringInterner {
				const KEYWORDS: &[&str] = &[$($text),+];
				let mut strings = StringInterner::with_capacity(KEYWORDS.len());
				for keyword in KEYWORDS {
					strings.get_or_intern(keyword);
				}
				strings
			}
		}

		#[cfg(test)]
		mod tests {
			use super::*;

			#[test]
			fn seeded_keywords_keep_their_reserved_symbols() {
				let mut strings = Keyword::create_interner();
				$(
					let symbol = Keyword::$variant.symbol();
					assert_eq!(strings.get($text), Some(symbol));
					assert_eq!(strings.resolve(symbol), Some($text));
					assert_eq!(Keyword::try_from($text).unwrap().symbol(), symbol);
				)+
				let ordinary = strings.get_or_intern("ordinary_identifier");
				assert_eq!(ordinary.to_usize(), [$($text),+].len());
				$(assert_eq!(strings.get_or_intern($text), Keyword::$variant.symbol());)+
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
	Func => "func",
	Loop => "loop",
	Break => "break",
	Continue => "continue",
	Return => "return",
	If => "if",
	Else => "else",
	As => "as",
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
	Package => "package",
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
