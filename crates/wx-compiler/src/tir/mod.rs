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

use self::decls::Declarations;
use self::impls::ImplDispatch;
use self::resolutions::NameResolutions;
pub use self::signatures::Semantics;
use self::signatures::SemanticsBuilder;

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
		stdlib_package,
		root_package,
	} = compilation;
	let mut diagnostics = Vec::new();
	let mut resolutions = NameResolutions::default();
	let (decls, ast_nodes) = Declarations::build(
		packages,
		files,
		strings,
		&mut diagnostics,
		&mut resolutions,
		*stdlib_package,
		*root_package,
	);
	let impl_dispatch = ImplDispatch::build(
		&mut diagnostics,
		&mut resolutions,
		strings,
		&decls,
		&ast_nodes,
	);
	let mut sema =
		Semantics::new(decls, impl_dispatch, diagnostics, resolutions, strings);
	SemanticsBuilder::new(files, strings, &ast_nodes).build(&mut sema);
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
