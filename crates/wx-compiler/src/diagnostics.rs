//! Diagnostic-code plumbing shared by every reporting stage.
//!
//! Diagnostic codes share one [`DiagnosticCode`] enum while retaining a
//! stage-specific number range, ordered by which stage runs first: `vfs`
//! uses E0xxx, `ast` uses E1xxx, and `tir` uses E2xxx. L3xxx belongs to
//! `wx-lint`, which defines its own codes.
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
		// Package loading (E0xxx).
		ModuleFileNotFound => "E0000",
		AmbiguousModuleFile => "E0001",
		DuplicatePackageName => "E0002",
		CircularDependency => "E0003",
		CorePackageAsDependency => "E0004",
		NestedModuleDeclaration => "E0005",

		// Parsing (E1xxx, W1xxx).
		UnknownToken => "E1000",
		UnexpectedToken => "E1001",
		MissingComma => "E1002",
		UnclosedDelimiter => "E1003",
		InvalidNumericLiteral => "E1004",
		IncompleteExpression => "E1005",
		ChainedComparison => "E1006",
		ReservedIdentifier => "E1007",
		InvalidItem => "E1008",
		MissingInitializer => "E1009",
		InvalidAttribute => "E1010",
		InvalidNamespace => "E1011",
		InvalidBindingPattern => "E1012",
		MissingImportAlias => "E1013",
		StructFieldsNeedParentheses => "E1014",
		MissingPackageAlias => "E1015",
		LabelOnIf => "E1016",
		PackageMemberHasBody => "E1017",
		BlockLikeOperand => "E1018",
		ChainedAssignment => "E1019",
		RestInEnumBody => "E1020",
		VisibilityNotPermitted => "E1021",
		MissingSemicolon => "W1022",

		// Checking (E2xxx, W2xxx).
		DuplicateDefinition => "E2000",
		CannotMutateImmutable => "E2001",
		TypeMistmatch => "E2002",
		TypeAnnotationRequired => "E2003",
		UnusedValue => "E2004",
		IntegerLiteralOutOfRange => "E2005",
		UnableToCoerce => "E2006",
		IntegerLiteralNotRepresentable => "E2007",
		UndeclaredIdentifier => "E2008",
		CannotCallExpression => "E2009",
		UndeclaredLabel => "E2010",
		BreakOutsideOfLoop => "E2011",
		InvalidAssignmentTarget => "E2012",
		ComparisonTypeAnnotationRequired => "E2013",
		NonConstantGlobalInitializer => "E2014",
		ArgumentCountMismatch => "E2015",
		InvalidCharacterLiteral => "E2016",
		DuplicateExport => "E2017",
		CannotExportItem => "E2018",
		CannotUseAsNamespace => "E2019",
		DuplicateStructField => "E2020",
		UnknownStructField => "E2021",
		DuplicateStructFieldInit => "E2022",
		MissingStructFields => "E2023",
		NotATraitBound => "E2024",
		RecursiveTypeWithoutIndirection => "E2025",
		IncompleteTraitImpl => "E2026",
		MissingEnumRepr => "E2027",
		CannotDerefNonPointer => "E2028",
		PointerWithoutMemory => "E2029",
		TypeArgumentCountMismatch => "E2030",
		ArraySizeMismatch => "E2031",
		ArrayRepeatCountNotConst => "E2032",
		TypesetBoundViolation => "E2033",
		MethodNotFound => "E2034",
		NotAMethod => "E2035",
		InferInSignature => "E2036",
		MissingElseBlock => "E2037",
		InvalidSelfType => "E2038",
		ContinueOutsideOfLoop => "E2039",
		EnumReprNotInteger => "E2040",
		EnumDuplicateValue => "E2041",
		NotConstEvaluatable => "E2042",
		AmbiguousTraitMember => "E2043",
		DuplicateTraitImpl => "E2044",
		InvalidImplTarget => "E2045",
		TraitBoundViolation => "E2046",
		DuplicateAssocTypeBinding => "E2047",
		PrivateItem => "E2048",
		NonExhaustiveMatch => "E2049",
		InvalidMatchPattern => "E2050",
		MissingTypeAliasBody => "E2051",
		EnumVariantRequiresExplicitValue => "E2052",
		AmbiguousIdentifier => "E2053",
		PrivateStructField => "E2054",
		ForeignImplTarget => "E2055",
		NotATraitMember => "E2056",
		TraitImplItemKindMismatch => "E2057",
		TraitImplSignatureMismatch => "E2058",
		TraitImplConstTypeMismatch => "E2059",
		CyclicTraitBounds => "E2060",
		FloatLiteralOverflow => "E2061",
		FloatLiteralUnderflow => "E2062",
		DuplicateRestPattern => "E2063",
		NotAType => "E2064",
		DuplicateGenericParam => "E2065",
		UnresolvedImport => "E2066",
		CyclicImport => "E2067",
		PrivateReexport => "E2068",
		CyclicTypeAlias => "E2069",
		DuplicateParameter => "E2070",
		SelfParamPosition => "E2071",
		MissingGlobalType => "E2072",
		CyclicAssociatedType => "E2073",
		TypeNormalizationOverflow => "E2074",
		TypeMemberNeedsQualification => "E2075",
		MissingConstantType => "E2076",
		UnknownCharacterEscape => "E2077",
		UnterminatedStringLiteral => "E2078",
		ConstEvaluationFailed => "E2079",
		CyclicConstant => "E2080",
		StructUsedAsValue => "E2081",
		TypeArgumentsNotAllowed => "E2082",
		AssocTypeEqualityMismatch => "E2083",
		UnknownPackage => "E2084",
		UnsupportedExpression => "E2085",
		RefutablePatternInLocal => "E2086",
		DuplicatePatternBinding => "E2087",
		UnmatchableLiteral => "E2088",
		NotBoundInAllAlternatives => "E2089",
		InconsistentPatternBinding => "E2090",
		UnknownParameterName => "E2091",
		DuplicateNamedArgument => "E2092",
		MissingArguments => "E2093",
		PositionalOnlyCall => "E2094",
		ImplStricterThanTrait => "E2095",
		CannotIndex => "E2096",
		MisplacedLiteralKind => "E2097",
		NotStackValue => "E2098",
		MisplacedSelfBound => "E2099",
		UnassumableEquality => "E2100",
		UnrepresentableConstant => "E2101",
		TypedConstantBound => "E2102",
		RecursionLimit => "E2103",
		SlotLimit => "E2104",
		MisplacedAttribute => "E2105",
		MalformedAttribute => "E2106",
		InvalidMemoryLimits => "E2107",
		LocalInStaticData => "E2108",
		MutableEnumRepr => "E2109",
		EnumConstructedFromRepr => "E2110",
		TestInEnumRepr => "E2111",
		NamedListWithoutNames => "E2112",
		UnreachableCode => "W2113",
		UnreachableMatchArm => "W2114",
		UnknownAttribute => "W2115",
		DuplicateAttribute => "W2116",
	}
}

/// A byte position in a file's text. A length is a plain `u32`: an offset
/// plus a length is an offset, and an offset minus an offset is a length.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(
	any(debug_assertions, test),
	derive(Debug, serde::Serialize),
	serde(transparent)
)]
pub struct TextOffset(u32);

impl TextOffset {
	pub const ZERO: TextOffset = TextOffset(0);
}

impl From<u32> for TextOffset {
	fn from(offset: u32) -> Self {
		TextOffset(offset)
	}
}

impl From<TextOffset> for u32 {
	fn from(offset: TextOffset) -> Self {
		offset.0
	}
}

impl core::fmt::Display for TextOffset {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		self.0.fmt(f)
	}
}

impl From<TextOffset> for usize {
	fn from(offset: TextOffset) -> Self {
		offset.0 as usize
	}
}

impl core::ops::Add<u32> for TextOffset {
	type Output = TextOffset;

	fn add(self, len: u32) -> TextOffset {
		TextOffset(self.0 + len)
	}
}

impl core::ops::AddAssign<u32> for TextOffset {
	fn add_assign(&mut self, len: u32) {
		self.0 += len;
	}
}

impl core::ops::Sub<u32> for TextOffset {
	type Output = TextOffset;

	fn sub(self, len: u32) -> TextOffset {
		TextOffset(self.0 - len)
	}
}

/// The length between two offsets.
impl core::ops::Sub for TextOffset {
	type Output = u32;

	fn sub(self, start: TextOffset) -> u32 {
		self.0 - start.0
	}
}

/// A run of a file's text, from `start` up to, not including, `end`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct TextSpan {
	pub start: TextOffset,
	pub end: TextOffset,
}

impl TextSpan {
	pub fn new(start: TextOffset, end: TextOffset) -> TextSpan {
		debug_assert!(end >= start);
		TextSpan { start, end }
	}

	/// The empty span at `at`: where something not written would go.
	pub fn empty_at(at: TextOffset) -> TextSpan {
		TextSpan { start: at, end: at }
	}

	pub fn len(self) -> u32 {
		self.end - self.start
	}

	pub fn is_empty(self) -> bool {
		self.start == self.end
	}

	pub fn contains(self, offset: TextOffset) -> bool {
		self.start <= offset && offset < self.end
	}

	#[inline]
	pub fn extract_str<'a>(&self, source: &'a str) -> &'a str {
		&source[usize::from(self.start)..usize::from(self.end)]
	}
}

/// A span written as numbers, `TextSpan::from(3..5)`: a test's, or a
/// position computed from text found in a source.
impl From<core::ops::Range<u32>> for TextSpan {
	fn from(range: core::ops::Range<u32>) -> Self {
		TextSpan::new(range.start.into(), range.end.into())
	}
}

impl From<TextSpan> for core::ops::Range<usize> {
	fn from(val: TextSpan) -> Self {
		usize::from(val.start)..usize::from(val.end)
	}
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
