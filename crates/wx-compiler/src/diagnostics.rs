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

use codespan_reporting::diagnostic::{Diagnostic, Severity};

use crate::vfs::FileId;

/// A stage's diagnostic code.
///
/// Implemented for every enum produced by [`define_diagnostic_codes`], which
/// is the only way these enums are declared. Named `Code` rather than
/// `DiagnosticCode` so it does not collide with the three enums of that name
/// when both are in scope.
pub trait Code {
	fn as_code(&self) -> &'static str;
}

/// Severity queries over a run of diagnostics.
///
/// An extension trait because both `Vec` and `Diagnostic` are foreign types,
/// so there is nowhere to hang an inherent `impl`. Implemented on the slice,
/// which covers `Vec<Diagnostic<FileId>>` through deref.
///
/// Its whole job is to define "counts as an error" once. That predicate —
/// `Severity::Error | Severity::Bug` — was written out at five separate
/// points in `wx-cli` alone, and a sixth in the test assertions; `Bug` being
/// dropped from any one of them is a silent hole, since a bug diagnostic is
/// strictly worse than an error and would sail through a check that only
/// looked for `Error`.
pub trait Diagnostics {
	fn errors(&self) -> impl Iterator<Item = &Diagnostic<FileId>>;

	fn error_count(&self) -> usize {
		self.errors().count()
	}

	fn has_errors(&self) -> bool {
		self.errors().next().is_some()
	}
}

impl Diagnostics for [Diagnostic<FileId>] {
	fn errors(&self) -> impl Iterator<Item = &Diagnostic<FileId>> {
		self.iter()
			.filter(|d| matches!(d.severity, Severity::Error | Severity::Bug))
	}
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
