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
		CorePackageAsDependency => "E0004",

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
		InvalidBindingPattern => "E1015",
		MissingImportAlias => "E1016",
		StructFieldsNeedParentheses => "E1019",
		MissingPackageAlias => "E1021",
		LabelOnIf => "E1025",
		PackageMemberHasBody => "E1026",
		BlockLikeOperand => "E1028",
		ChainedAssignment => "E1029",
		RestInEnumBody => "E1030",
		CrlfLineEndings => "W1001",
		VisibilityNotPermitted => "W1002",
		RedundantConstMarker => "W1003",

		// TIR diagnostics (E2xxx/W2xxx).
		DuplicateDefinition => "E2000",
		TypeMistmatch => "E2001",
		TypeAnnotationRequired => "E2002",
		UnusedValue => "E2003",
		IntegerLiteralOutOfRange => "E2004",
		UnableToCoerce => "E2005",
		IntegerLiteralNotRepresentable => "E2006",
		UndeclaredIdentifier => "E2007",
		CannotCallExpression => "E2009",
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
		NotATraitBound => "E2031",
		RecursiveTypeWithoutIndirection => "E2032",
		IncompleteTraitImpl => "E2033",
		UnsatisfiedTraitBound => "E2034",
		AssociatedTypeInInherentImpl => "E2035",
		MissingEnumRepr => "E2036",
		CannotDerefNonPointer => "E2037",
		PointerWithoutMemory => "E2038",
		TypeArgumentCountMismatch => "E2040",
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
		UnknownAttribute => "W2011",
		DuplicateAttribute => "W2012",
		MissingTypeAliasBody => "E2070",
		EnumVariantRequiresExplicitValue => "E2071",
		DuplicateExportBlock => "E2072",
		LibraryCannotExport => "E2074",
		AmbiguousIdentifier => "E2075",
		PrivateStructField => "E2076",
		ForeignImplTarget => "E2077",
		NotATraitMember => "E2078",
		TraitImplItemKindMismatch => "E2079",
		TraitImplSignatureMismatch => "E2080",
		TraitImplConstTypeMismatch => "E2081",
		CyclicTraitBounds => "E2082",
		CannotImplementTypeset => "E2083",
		FloatLiteralOverflow => "E2084",
		FloatLiteralUnderflow => "E2085",
		DuplicateRestPattern => "E2087",
		RecordStructPositionalPattern => "E2089",
		PrivateTupleField => "E2090",
		NotAType => "E2091",
		DuplicateGenericParam => "E2092",
		UnresolvedImport => "E2093",
		CyclicImport => "E2094",
		PrivateReexport => "E2095",
		CyclicTypeAlias => "E2096",
		DuplicateParameter => "E2097",
		SelfParamPosition => "E2098",
		MissingGlobalType => "E2100",
		CyclicAssociatedType => "E2102",
		TypeNormalizationOverflow => "E2103",
		TypeMemberNeedsQualification => "E2104",
		MissingConstantType => "E2105",
		UnknownCharacterEscape => "E2106",
		UnterminatedStringLiteral => "E2107",
		ConstEvaluationFailed => "E2108",
		CyclicConstant => "E2109",
		StructUsedAsValue => "E2110",
		TypeArgumentsNotAllowed => "E2111",
		AssocTypeEqualityMismatch => "E2112",
		UnknownPackage => "E2113",
		UnsupportedExpression => "E2114",
		RefutablePatternInLocal => "E2115",
		DuplicatePatternBinding => "E2116",
		UnmatchableLiteral => "E2117",
		NotBoundInAllAlternatives => "E2118",
		InconsistentPatternBinding => "E2119",
		UnknownParameterName => "E2120",
		DuplicateNamedArgument => "E2121",
		MissingArguments => "E2122",
		PositionalOnlyCall => "E2123",
		ImplStricterThanTrait => "E2124",
		CannotIndex => "E2125",
		MisplacedLiteralKind => "E2128",
		NotStackValue => "E2129",
		MisplacedSelfBound => "E2131",
		UnassumableEquality => "E2132",
		UnrepresentableConstant => "E2133",
		TypedConstantBound => "E2134",
		RecursionLimit => "E2135",
		SlotLimit => "E2136",
		MisplacedAttribute => "E2137",
		MalformedAttribute => "E2138",
		InvalidMemoryLimits => "E2139",
		LocalInStaticData => "E2140",
		MutableEnumRepr => "E2141",
		EnumConstructedFromRepr => "E2142",
		TestInEnumRepr => "E2143",
		NamedListWithoutNames => "E2144",
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
