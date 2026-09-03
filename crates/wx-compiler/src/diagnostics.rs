//! Diagnostic-code plumbing shared by every reporting stage.
//!
//! Diagnostic codes share one [`DiagnosticCode`] enum while retaining a
//! stage-specific number range: `ast` uses E0xxx, `tir` uses E1xxx, and `vfs`
//! uses E2xxx.
//!
use codespan_reporting::diagnostic::{Diagnostic, Severity};

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
		// AST diagnostics (E0xxx/W0xxx).
		UnknownToken => "E0001",
		UnexpectedToken => "E0002",
		MissingSeparator => "E0003",
		UnclosedDelimiter => "E0004",
		InvalidNumericLiteral => "E0005",
		IncompleteExpression => "E0006",
		ChainedComparison => "E0007",
		ReservedIdentifier => "E0008",
		InvalidItem => "E0009",
		MissingInitializer => "E0010",
		InvalidAttribute => "E0012",
		InvalidNamespace => "E0013",
		InvalidLabel => "E0014",
		InvalidBindingPattern => "E0015",
		CrlfLineEndings => "W0001",
		VisibilityNotPermitted => "W0002",

		// TIR diagnostics (E1xxx/W1xxx).
		DuplicateDefinition => "E1000",
		TypeMistmatch => "E1001",
		TypeAnnotationRequired => "E1002",
		UnusedValue => "E1003",
		IntegerLiteralOutOfRange => "E1004",
		UnableToCoerce => "E1005",
		LiteralTypeMismatch => "E1006",
		UndeclaredIdentifier => "E1007",
		BinaryOperatorCannotBeApplied => "E1008",
		CannotCallExpression => "E1009",
		UnaryOperatorCannotBeApplied => "E1010",
		UndeclaredLabel => "E1011",
		BreakOutsideOfLoop => "E1012",
		InvalidAssignmentTarget => "E1013",
		ComparisonTypeAnnotationRequired => "E1014",
		NonConstantGlobalInitializer => "E1015",
		ArgumentCountMismatch => "E1016",
		InvalidCharacterLiteral => "E1017",
		DuplicateExport => "E1018",
		CannotExportItem => "E1019",
		NotANamespace => "E1020",
		UndeclaredType => "E1021",
		DuplicateStructField => "E1022",
		UnknownStructField => "E1025",
		DuplicateStructFieldInit => "E1026",
		MissingStructFields => "E1027",
		CannotMutateImmutable => "W1000",
		UnusedVariable => "W1001",
		UnnecessaryMutability => "W1002",
		UnreachableCode => "W1003",
		UnusedItem => "W1004",
		MissingImportParamName => "W1005",
		UnusedTypeParam => "W1006",
		UnusedStructField => "W1007",
		UnusedLabel => "W1008",
		MissingFunctionBody => "E1028",
		InvalidMemoryKind => "E1029",
		NamespaceUsedAsValue => "E1030",
		ExpectedBound => "E1031",
		CyclicTypeDependency => "E1032",
		IncompleteTraitImpl => "E1033",
		UnsatisfiedTraitBound => "E1034",
		AssociatedTypeInInherentImpl => "E1035",
		MissingEnumRepr => "E1036",
		CannotDerefNonPointer => "E1037",
		NoMemoryForPointer => "E1038",
		AmbiguousPointerMemory => "E1039",
		TypeArgCountMismatch => "E1040",
		InvalidCast => "E1041",
		IndexOnNonIndexable => "E1042",
		ArraySizeMismatch => "E1043",
		ArrayRepeatCountNotConst => "E1044",
		ArrayElementNotConst => "E1045",
		TypesetMemberNotInteger => "E1046",
		TypesetBoundViolation => "E1047",
		MultipleTypesetBounds => "E1048",
		MethodNotFound => "E1049",
		NotAMethod => "E1050",
		InferInSignature => "E1051",
		MissingElseBlock => "E1052",
		InvalidSelfType => "E1053",
		ContinueOutsideOfLoop => "E1054",
		EnumReprNotInteger => "E1055",
		EnumDuplicateValue => "E1056",
		NotConstEvaluatable => "E1057",
		UnusedEnumVariant => "W1009",
		MissingImportAlias => "E1058",
		AmbiguousTraitMember => "E1059",
		NotAField => "E1060",
		DuplicateTraitImpl => "E1061",
		InvalidImplTarget => "E1062",
		TraitBoundViolation => "E1063",
		DuplicateAssocTypeBinding => "E1064",
		PrivateItem => "E1065",
		NonExhaustiveMatch => "E1066",
		InvalidMatchScrutineeType => "E1067",
		InvalidMatchPattern => "E1068",
		InvalidMemoryLimitsAttribute => "E1069",
		UnreachableMatchArm => "W1010",
		MissingTypeAliasBody => "E1070",
		EnumVariantRequiresExplicitValue => "E1071",
		DuplicateExportBlock => "E1072",
		ExportBlockNotAtRoot => "E1073",
		LibraryCannotExport => "E1074",
		AmbiguousWildcardImport => "E1075",
		PrivateStructField => "E1076",
		ForeignImplTarget => "E1077",
		NotATraitMember => "E1078",
		TraitImplItemKindMismatch => "E1079",
		TraitImplSignatureMismatch => "E1080",
		TraitImplConstTypeMismatch => "E1081",

		// VFS diagnostics (E2xxx).
		ModuleFileNotFound => "E2000",
		AmbiguousModuleFile => "E2001",
		DuplicatePackageName => "E2002",
		CircularDependency => "E2003",
		StdPackageAsDependency => "E2004",
		PackageDeclaredTwice => "E2005",
		NestedModuleDeclaration => "E2006",
	}
}
