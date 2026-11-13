mod body;
mod bounds;
mod conformance;
mod decls;
mod eval;
mod format;
mod impls;
mod imports;
mod intrinsics;
mod layout;
mod literals;
mod lower;
mod members;
mod numbers;
mod obligations;
mod operators;
mod paths;
mod resolutions;
mod satisfaction;
mod signatures;
mod solver;
mod typecheck;
mod types;
mod usefulness;

use crate::diagnostics::Diagnostics;
use crate::mir::MIR;
use crate::symbols::StringInterner;
use crate::vfs::CompilationUnit;

pub use self::body::{
	Body, BodyOwner, Label, LabelIdx, LabelKind, Local, LocalIdx, ParamIdx,
};
use self::decls::Declarations;
pub use self::decls::{
	AssocTypeIdx, ConstIdx, DeclKind, EnumIdx, FieldIdx, FunctionIdx,
	GlobalIdx, InherentImplIdx, ItemLoc, MemberKind, MemberOwner, MemoryIdx,
	NameUse, StructIdx, Tier, TraitIdx, TraitImplIdx, TypeAliasIdx, TypeRole,
	TypesetIdx, UseItemIndex,
};
pub use self::eval::{AllocIdx, ConstScalar, Val};
pub use self::format::{BoundFormatter, TypeFormatter};
use self::impls::ImplDispatch;
pub use self::literals::{
	StringLiteralError, StringLiteralErrorKind, unescape_string_literal,
};
use self::resolutions::NameResolutions;
pub use self::resolutions::{AccessKind, Definition, Reference, Route};
pub use self::signatures::Semantics;
use self::signatures::SemanticsBuilder;
pub use self::types::{GenericEnvIdx, Primitive, Type, TypeIndex};

/// Checks declarations and bodies into a live [`Semantics`], which holds
/// their diagnostics. Parser and package diagnostics remain available on
/// `compilation`. `strings` must be the interner used to load the
/// compilation.
pub fn check(
	compilation: &CompilationUnit,
	strings: &mut StringInterner,
) -> Semantics {
	let CompilationUnit {
		files,
		packages,
		core_package,
		root_package,
		asts,
	} = compilation;
	let mut diagnostics = Vec::new();
	let mut resolutions = NameResolutions::default();
	let (decls, ast_nodes) = Declarations::build(
		packages,
		asts,
		files,
		strings,
		&mut diagnostics,
		&mut resolutions,
		*core_package,
		*root_package,
	);
	let impl_dispatch = ImplDispatch::build(
		&mut diagnostics,
		&mut resolutions,
		strings,
		&decls,
		&ast_nodes,
		asts,
	);
	let mut sema =
		Semantics::new(decls, impl_dispatch, diagnostics, resolutions, strings);
	SemanticsBuilder::new(files, asts, strings, &ast_nodes).build(&mut sema);
	sema
}

/// Lowers a checked program into [`MIR`]. A program whose checking reported
/// an error or a bug is not lowered; a lowering failure is reported on
/// `sema`. `strings` must be the interner `sema` was checked with.
pub fn lower(
	sema: &mut Semantics,
	strings: &StringInterner,
) -> Result<MIR, ()> {
	if sema.diagnostics.has_errors() {
		return Err(());
	}
	lower::build(sema, strings)
}
