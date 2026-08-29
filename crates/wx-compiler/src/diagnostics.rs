//! Diagnostic-code plumbing shared by every reporting stage.
//!
//! Each stage owns its own `DiagnosticCode` enum with its own number range —
//! `ast` (E0xxx), `tir` (E1xxx), `vfs` (E2xxx) — but the enums are otherwise
//! identical in shape, and until this module existed so was the macro that
//! generated them: three byte-for-byte copies, one per stage.
//!
//! [`Code`] is what makes the set addressable generically. Anything that works
//! with diagnostics from more than one stage (the test assertions in
//! `crate::testing`, for one) would otherwise have to take a bare `&str` and
//! give up the compiler's help in spelling a code correctly.

/// A stage's diagnostic code.
///
/// Implemented for every enum produced by [`define_diagnostic_codes`], which
/// is the only way these enums are declared. Named `Code` rather than
/// `DiagnosticCode` so it does not collide with the three enums of that name
/// when both are in scope.
pub trait Code {
	fn as_code(&self) -> &'static str;
}

macro_rules! define_diagnostic_codes {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $variant:ident => $code:literal,
            )*
        }
    ) => {
        $(#[$meta])*
        $vis enum $name {
            $($variant,)*
        }

        impl $name {
            pub const fn code(&self) -> &'static str {
                match self {
                    $(Self::$variant => $code,)*
                }
            }
        }

        impl $crate::diagnostics::Code for $name {
            fn as_code(&self) -> &'static str {
                self.code()
            }
        }

        impl std::str::FromStr for $name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($code => Ok(Self::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str(self.code())
            }
        }
    };
}

pub(crate) use define_diagnostic_codes;
