//! Diagnostic-code plumbing shared by every reporting stage.
//!
//! Diagnostic codes share one [`DiagnosticCode`] enum while retaining a
//! stage-specific number range, ordered by which stage runs first: `vfs`
//! uses E0xxx, `ast` uses E1xxx, and `tir` uses E2xxx.
//!
use codespan_reporting::diagnostic::{Diagnostic, Label, Severity};

use crate::vfs::FileId;

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

        impl std::str::FromStr for $name {
            type Err = ();

			#[deny(unreachable_patterns)]
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

define_diagnostic_codes! {
	/// A diagnostic emitted by any compiler stage.
	pub enum DiagnosticCode {
		// VFS diagnostics (E0xxx).
		ModuleFileNotFound => "E0000",
		AmbiguousModuleFile => "E0001",
		DuplicatePackageName => "E0002",
		CircularDependency => "E0003",
		StdPackageAsDependency => "E0004",
		PackageDeclaredTwice => "E0005",
		NestedModuleDeclaration => "E0006",

		// AST diagnostics (E1xxx/W1xxx).
		UnknownToken => "E1001",
		UnexpectedToken => "E1002",
		MissingSeparator => "E1003",
		UnclosedDelimiter => "E1004",
		InvalidNumericLiteral => "E1005",
		IncompleteExpression => "E1006",
		ChainedComparison => "E1007",
		ReservedIdentifier => "E1008",
		InvalidItem => "E1009",
		MissingInitializer => "E1010",
		InvalidAttribute => "E1012",
		InvalidNamespace => "E1013",
		InvalidLabel => "E1014",
		InvalidBindingPattern => "E1015",
		MissingImportAlias => "E1016",
		CrlfLineEndings => "W1001",
		VisibilityNotPermitted => "W1002",

		// TIR diagnostics (E2xxx/W2xxx).
		DuplicateDefinition => "E2000",
		TypeMistmatch => "E2001",
		TypeAnnotationRequired => "E2002",
		UnusedValue => "E2003",
		IntegerLiteralOutOfRange => "E2004",
		UnableToCoerce => "E2005",
		IntegerLiteralNotRepresentable => "E2006",
		UndeclaredIdentifier => "E2007",
		BinaryOperatorCannotBeApplied => "E2008",
		CannotCallExpression => "E2009",
		UnaryOperatorCannotBeApplied => "E2010",
		UndeclaredLabel => "E2011",
		BreakOutsideOfLoop => "E2012",
		InvalidAssignmentTarget => "E2013",
		ComparisonTypeAnnotationRequired => "E2014",
		NonConstantGlobalInitializer => "E2015",
		ArgumentCountMismatch => "E2016",
		InvalidCharacterLiteral => "E2017",
		DuplicateExport => "E2018",
		CannotExportItem => "E2019",
		CannotUseAsNamespace => "E2020",
		UndeclaredType => "E2021",
		DuplicateStructField => "E2022",
		UnknownStructField => "E2025",
		DuplicateStructFieldInit => "E2026",
		MissingStructFields => "E2027",
		CannotMutateImmutable => "W2000",
		UnusedVariable => "W2001",
		UnnecessaryMutability => "W2002",
		UnreachableCode => "W2003",
		UnusedItem => "W2004",
		MissingImportParamName => "W2005",
		UnusedTypeParam => "W2006",
		UnusedStructField => "W2007",
		UnusedLabel => "W2008",
		MissingFunctionBody => "E2028",
		InvalidMemoryKind => "E2029",
		NamespaceUsedAsValue => "E2030",
		ExpectedTraitBound => "E2031",
		RecursiveTypeWithoutIndirection => "E2032",
		IncompleteTraitImpl => "E2033",
		UnsatisfiedTraitBound => "E2034",
		AssociatedTypeInInherentImpl => "E2035",
		MissingEnumRepr => "E2036",
		CannotDerefNonPointer => "E2037",
		NoMemoryForPointer => "E2038",
		AmbiguousPointerMemory => "E2039",
		TypeArgCountMismatch => "E2040",
		InvalidCast => "E2041",
		IndexOnNonIndexable => "E2042",
		ArraySizeMismatch => "E2043",
		ArrayRepeatCountNotConst => "E2044",
		ArrayElementNotConst => "E2045",
		TypesetMemberNotConcrete => "E2046",
		TypesetBoundViolation => "E2047",
		MethodNotFound => "E2049",
		NotAMethod => "E2050",
		InferInSignature => "E2051",
		MissingElseBlock => "E2052",
		InvalidSelfType => "E2053",
		ContinueOutsideOfLoop => "E2054",
		EnumReprNotInteger => "E2055",
		EnumDuplicateValue => "E2056",
		NotConstEvaluatable => "E2057",
		UnusedEnumVariant => "W2009",
		AmbiguousTraitMember => "E2059",
		NotAField => "E2060",
		DuplicateTraitImpl => "E2061",
		InvalidImplTarget => "E2062",
		TraitBoundViolation => "E2063",
		DuplicateAssocTypeBinding => "E2064",
		PrivateItem => "E2065",
		NonExhaustiveMatch => "E2066",
		InvalidMatchScrutineeType => "E2067",
		InvalidMatchPattern => "E2068",
		InvalidMemoryLimitsAttribute => "E2069",
		UnreachableMatchArm => "W2010",
		MissingTypeAliasBody => "E2070",
		EnumVariantRequiresExplicitValue => "E2071",
		DuplicateExportBlock => "E2072",
		ExportBlockNotAtRoot => "E2073",
		LibraryCannotExport => "E2074",
		AmbiguousIdentifier => "E2075",
		PrivateStructField => "E2076",
		ForeignImplTarget => "E2077",
		NotATraitMember => "E2078",
		TraitImplItemKindMismatch => "E2079",
		TraitImplSignatureMismatch => "E2080",
		TraitImplConstTypeMismatch => "E2081",
		CyclicSupertrait => "E2082",
		CannotImplementTypeset => "E2083",
		FloatLiteralOverflow => "E2084",
		FloatLiteralUnderflow => "E2085",
		TupleStructBraceLiteral => "E2086",
		DuplicateRestPattern => "E2087",
		TupleStructBracePattern => "E2088",
		RecordStructPositionalPattern => "E2089",
		PrivateTupleField => "E2090",
		NamespaceUsedAsType => "E2091",
		DuplicateGenericParam => "E2092",
		UnresolvedImport => "E2093",
		CyclicImport => "E2094",
		PrivateReexport => "E2095",
		CyclicTypeAlias => "E2096",
	}
}

#[derive(Copy, Clone, PartialEq)]
#[cfg_attr(test, derive(serde::Serialize))]
#[cfg_attr(debug_assertions, derive(Debug))]
pub struct TextSpan {
	pub start: u32,
	pub end: u32,
}

impl TextSpan {
	pub fn new(start: u32, end: u32) -> TextSpan {
		debug_assert!(end >= start);
		TextSpan { start, end }
	}

	#[inline]
	pub fn extract_str<'a>(&self, source: &'a str) -> &'a str {
		&source[self.start as usize..self.end as usize]
	}
}

impl From<TextSpan> for core::ops::Range<usize> {
	fn from(val: TextSpan) -> Self {
		val.start as usize..val.end as usize
	}
}

#[cfg_attr(debug_assertions, derive(Debug))]
#[cfg_attr(test, derive(serde::Serialize))]
#[derive(Clone, Copy, PartialEq)]
pub struct SourceSpan {
	pub file_id: FileId,
	pub span: TextSpan,
}

impl SourceSpan {
	pub fn new(file_id: FileId, span: TextSpan) -> Self {
		Self { file_id, span }
	}

	pub fn primary_label(self) -> Label<FileId> {
		Label::primary(self.file_id, self.span)
	}

	pub fn secondary_label(self) -> Label<FileId> {
		Label::secondary(self.file_id, self.span)
	}
}
