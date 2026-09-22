//! Namespace-graph path resolution: walks a `::`-separated sequence of name
//! segments to the `DefKey` the last one names.
//!
//! Matches rustc: an unqualified name is looked up only in the namespace it
//! was written in (its own direct declarations, its own `use`/glob
//! imports), then the std prelude tier — **never** by climbing to an
//! enclosing module. A struct declared at the package root is not visible,
//! unqualified, from inside a child `mod inner { }` any more than it would
//! be in Rust; reaching it needs `super::Outer`, exactly as it would there.
//! (The pre-rewrite builder's `lookup_scope_chain`, in
//! `tir/builder/modules.rs`, did climb ancestors — that turned out to be a
//! real divergence from Rust, not something to carry forward, confirmed by
//! literally compiling the equivalent Rust and getting E0425.)
//!
//! Every segment after the first is looked up in exactly the one namespace
//! the previous segment named — no prelude fallback there either, since a
//! qualified path's later segments are never "unqualified."
//!
//! Deliberately stops at the namespace graph's edge. Once a segment
//! resolves to a `DefKind` that doesn't own a namespace of its own
//! (`DefKind::as_namespace` returns `None`) — a struct, an enum variant, a
//! trait, ... — there's nowhere left to look up the next segment using this
//! module's own machinery: namespace bindings are the only kind it knows
//! about. Resolving `Type::member` needs the
//! inherent/trait impl dispatch tables instead (not built yet); that case
//! surfaces as `PathResolution::stopped_with` being `Found` while
//! `stopped_at` is still short of the last segment, for
//! `resolve_path` to route onward however it can once that machinery
//! exists, or diagnose, if there's nowhere onward to route it to yet.
//!
//! Doesn't diagnose anything itself. Rustc splits privacy-checking off
//! into a wholly separate later pass over already-resolved paths — I
//! compiled a private-module test case (`mod a { mod b { pub struct C; } }
//! fn f() -> a::b::C`) and rustc reports the error against `b` — "module
//! `b` is private" — even though the terminal `C` is `pub`, which only
//! makes sense if resolution finds every segment's identity regardless of
//! visibility and something else decides afterward which hop was illegal.
//! `try_resolve_path` doesn't need a *separate* pass to get the same result,
//! though: it already fetches each hop's `Visibility` from
//! `NamespaceLookup::lookup` regardless, so checking accessibility right
//! there costs nothing extra — `PathResolution::first_inaccessible` just
//! reads off what the one walk already computed, still with no diagnostics
//! pushed and no decision made about whether/how to report it, only
//! whether-and-where. (I also confirmed the same private item referenced
//! from two call sites gets two independent privacy diagnostics, and that
//! a privacy violation doesn't stop type-checking from also reporting its
//! own unrelated errors on the same expression — both only make sense if
//! privacy-checking is genuinely
//! decoupled from, and doesn't gate, resolution or anything downstream of
//! it.)

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::{
	ast::{PathSegment, StringInterner},
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	vfs::FileId,
};

use super::defs::{
	BindingKey, BindingLookup, BindingNamespace, BindingTarget, DefKey,
	DefKind, Namespace, NamespaceIndex, NamespaceLookup, UseItemDef,
};
use super::imports::{
	report_ambiguous_identifier, report_cannot_use_as_namespace,
	report_private_identifier,
};

/// The result of walking a whole path. `stopped_with` is the answer for
/// `segments[stopped_at]`:
/// - `Found` with `stopped_at == segments.len() - 1` — the path fully
///   resolved; `stopped_with`'s `BindingTarget` is the answer.
/// - `Found` with segments still remaining — `stopped_at`'s def isn't a
///   namespace, so there's nowhere to look up the rest with this module's
///   own machinery ("not a module", though there's no dedicated variant
///   for it: it falls out of `stopped_at`/`stopped_with` together, same as
///   rustc's `PartialRes` never needs a distinct case for it either).
/// - `NotFound` / `Ambiguous` — resolution stopped at `stopped_at` for that
///   reason.
///
/// `Found(BindingTarget::Error, _)` is an already-diagnosed error-recovery
/// placeholder; no separate "errored" case is needed since `BindingTarget`
/// already says so.
///
/// Both fields are private. [`PathResolver::resolve_path`] is the
/// intended way to consume a resolution — it turns this raw shape into a
/// plain `BindingTarget`, reporting whatever went wrong, so a caller never
/// needs to know this struct's shape at all. `try_resolve_path` itself still
/// stays diagnostics-free internally (same reasoning as
/// `NamespaceLookup::try_insert_binding`); it's just that nothing outside
/// this file gets to see its raw result anymore.
///
/// `stopped_at` is `u32`, not `usize` — a path realistically never has more
/// than a handful of segments, so matching every other arena/segment index
/// in this codebase (`index_newtype!`'s `u32` backing) halves its footprint.
#[cfg_attr(test, derive(Debug))]
struct PathResolution {
	stopped_at: u32,
	stopped_with: BindingLookup,
	/// `(segment index, its DefKey)` for the earliest segment whose binding
	/// wasn't visible to `accessor` — `None` together, never one without
	/// the other. Always a real `DefKey` when `Some`: an already-errored
	/// placeholder (`BindingTarget::Error`) is never checked for
	/// accessibility at all (see `try_resolve_path`), since there's nothing
	/// real there to flag privacy on top of an already-reported problem —
	/// which is what makes "a hop, but no DefKey" unrepresentable here
	/// rather than a case this type has to account for.
	first_inaccessible: Option<(u32, DefKey)>,
}

/// Namespace-graph path resolution, holding just the read-only inputs
/// every call needs — see the module docs for what this does and doesn't
/// cover.
pub(super) struct PathResolver<'r> {
	namespaces: &'r [Namespace],
	use_items: &'r [UseItemDef],
	stdlib_root: NamespaceIndex,
}

impl<'r> PathResolver<'r> {
	pub(super) fn new(
		namespaces: &'r [Namespace],
		use_items: &'r [UseItemDef],
		stdlib_root: NamespaceIndex,
	) -> Self {
		Self {
			namespaces,
			use_items,
			stdlib_root,
		}
	}

	/// Resolves `segments`, starting from `accessor` — both the namespace
	/// the path is written in and the identity privacy is checked against,
	/// since those are always the same thing. `tier` applies to the *last*
	/// segment only: every earlier one is always looked up in the `Type`
	/// tier, since a module — the only thing a non-final segment can ever
	/// name — always lives there.
	///
	/// Private: [`Self::resolve_path`] is the surface other modules
	/// use — see [`PathResolution`]'s own doc comment for why.
	fn try_resolve_path(
		&self,
		accessor: NamespaceIndex,
		segments: &[PathSegment],
		tier: BindingNamespace,
	) -> PathResolution {
		debug_assert!(
			!segments.is_empty(),
			"a path always has at least one segment"
		);

		let mut base = accessor;
		let mut first_inaccessible = None;
		for (index, segment) in segments.iter().enumerate() {
			let is_last = index + 1 == segments.len();
			let seg_tier = if is_last {
				tier
			} else {
				BindingNamespace::Type
			};
			let key = BindingKey::new(seg_tier, segment.ident.inner);

			// The std-prelude fallback only ever applies to the first
			// segment, and only once nothing binds it directly.
			let mut outcome =
				self.namespaces.lookup(self.use_items, accessor, base, key);
			if index == 0 && matches!(outcome, BindingLookup::NotFound) {
				base = self.stdlib_root;
				outcome =
					self.namespaces.lookup(self.use_items, accessor, base, key);
			}

			match &outcome {
				BindingLookup::Found(target, visibility) => {
					// `target.def_key()` computed once and reused below —
					// also what makes an already-errored placeholder
					// (`None` here) never get checked for accessibility at
					// all, so `first_inaccessible` can never end up with a
					// hop that has no real `DefKey` behind it.
					let def_key = target.def_key();
					if first_inaccessible.is_none()
						&& let Some(def_key) = def_key
						&& !self.namespaces.is_accessible_from(
							accessor,
							base,
							*visibility,
						) {
						first_inaccessible = Some((index as u32, def_key));
					}
					if is_last {
						return PathResolution {
							stopped_at: index as u32,
							stopped_with: outcome,
							first_inaccessible,
						};
					}
					let Some(def_key) = def_key else {
						// `BindingTarget::Error` mid-path — nothing left to
						// continue into.
						return PathResolution {
							stopped_at: index as u32,
							stopped_with: outcome,
							first_inaccessible,
						};
					};
					match self.def_kind(def_key).as_namespace() {
						Some(next) => base = next,
						None => {
							return PathResolution {
								stopped_at: index as u32,
								stopped_with: outcome,
								first_inaccessible,
							};
						}
					}
				}
				BindingLookup::NotFound | BindingLookup::Ambiguous(_) => {
					return PathResolution {
						stopped_at: index as u32,
						stopped_with: outcome,
						first_inaccessible,
					};
				}
			}
		}
		unreachable!(
			"the loop above returns for every segment, including the last"
		)
	}

	/// Resolves `segments` and turns the result into a single
	/// `BindingTarget`, reporting a diagnostic for everything that can go
	/// wrong along the way:
	/// - `NotFound` / `Ambiguous` / reaching a non-module mid-path — nothing
	///   real to hand back, so this reports and returns `BindingTarget::Error`.
	/// - A hop that resolved to something real but isn't visible to
	///   `accessor` — reported too, but *not* turned into `Error`: matching
	///   rustc (verified empirically — a privacy violation doesn't stop
	///   type-checking from also reporting its own, unrelated errors on the
	///   same resolved item), the real target is still returned, so a
	///   caller building on top of it doesn't get a spurious cascade on top
	///   of the privacy diagnostic.
	///
	/// This is the intended entry point for every other module — see
	/// [`PathResolution`]'s doc comment for why its raw shape isn't exposed
	/// directly.
	///
	/// The exact diagnostic codes/wording below are still open — see the
	/// `report_*` stubs.
	pub(super) fn resolve_path(
		&self,
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		file_id: FileId,
		accessor: NamespaceIndex,
		segments: &[PathSegment],
		tier: BindingNamespace,
	) -> BindingTarget {
		let resolution = self.try_resolve_path(accessor, segments, tier);
		let stopped_at = resolution.stopped_at as usize;
		let is_last = stopped_at + 1 == segments.len();
		// Every segment but the last is always looked up in the `Type`
		// tier (see `try_resolve_path`) — `tier` only applies once we've
		// actually reached the last one.
		let seg_tier = if is_last {
			tier
		} else {
			BindingNamespace::Type
		};
		let span = segments[stopped_at].ident.span;

		match &resolution.stopped_with {
			BindingLookup::Found(target, _) if is_last => {
				let target = *target;
				if let Some((bad, def_key)) = resolution.first_inaccessible {
					diagnostics.push(report_private_identifier(
						self.namespaces,
						strings,
						segments[bad as usize].ident.inner,
						SourceSpan::new(
							file_id,
							segments[bad as usize].ident.span,
						),
						Some(def_key),
					));
				}
				target
			}
			BindingLookup::Found(target, _) => {
				// `None` here means an already-errored placeholder
				// (`BindingTarget::Error`) mid-path — already diagnosed
				// by whoever caused that, nothing new to report.
				if let Some(def_key) = target.def_key() {
					diagnostics.push(report_cannot_use_as_namespace(
						self.namespaces,
						strings,
						segments[stopped_at].ident.inner,
						SourceSpan::new(file_id, span),
						def_key,
					));
				}
				BindingTarget::Error
			}
			BindingLookup::NotFound => {
				diagnostics.push(report_not_found(
					strings,
					file_id,
					span,
					seg_tier,
					segments[stopped_at].ident.inner,
				));
				BindingTarget::Error
			}
			BindingLookup::Ambiguous(candidates) => {
				diagnostics.push(report_ambiguous_identifier(
					self.namespaces,
					strings,
					segments[stopped_at].ident.inner,
					SourceSpan::new(file_id, span),
					candidates,
				));
				BindingTarget::Error
			}
		}
	}

	fn def_kind(&self, def_key: DefKey) -> DefKind {
		self.namespaces[usize::from(def_key.namespace_idx)].items
			[usize::from(def_key.def_idx)]
		.kind
	}
}

// The four cases `resolve_path` can report. Bodies are stubs — the
// exact diagnostic codes/wording are still an open decision (see the
// conversation that led here); everything *around* these calls is final.
// Kept as named, `report_*`-shaped functions (rather than inline `todo!()`s
// in `resolve_path` itself) both to match this codebase's convention
// of each module owning its own `report_*` diagnostics, and so this list is
// a literal checklist of what's left.

/// One code regardless of tier — matches rustc, which reports both
/// "cannot find type `X`" and "cannot find value `X`" as the same E0425,
/// only the noun in the message differing. `UndeclaredType` (E2021) stays
/// unused rather than being pressed into service for the same concept a
/// second time.
fn report_not_found(
	strings: &StringInterner,
	file_id: FileId,
	span: TextSpan,
	tier: BindingNamespace,
	name: SymbolU32,
) -> Diagnostic<FileId> {
	let name = strings.resolve(name).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredIdentifier.code())
		.with_message(format!(
			"cannot find {} `{name}` in this scope",
			tier.noun()
		))
		.with_label(SourceSpan::new(file_id, span).primary_label())
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

	use super::*;
	use crate::tir::defs::DefinitionRegistry;
	use crate::vfs;

	/// Small, path-resolution-only duplicate of `defs::tests::TestCase` —
	/// kept separate rather than shared across files so each test module
	/// stays self-contained, same as `imports.rs`'s own copy.
	struct TestCase {
		graph: vfs::CompilationUnit,
		defs: DefinitionRegistry,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			builder.load_stdlib();
			let root_id = builder
				.load_binary(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)])),
				)
				.unwrap();
			let mut graph = builder.build(root_id);

			let mut diagnostics = Vec::new();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				graph.stdlib_package,
			);
			// Only path resolution over the finished namespace graph is
			// under test here — `ast_nodes` is Phase 2's input, and
			// `diagnostics` is prescan/import-resolution's own concern
			// (already exercised by `defs.rs`/`imports.rs`'s own tests).
			drop(ast_nodes);
			drop(diagnostics);

			TestCase { graph, defs }
		}

		fn new_workspace(
			entry_path: vfs::AbsolutePath,
			workspace: HashMap<vfs::AbsolutePath, String>,
		) -> Self {
			let mut builder = vfs::CompilationUnitBuilder::new();
			builder.load_stdlib();
			let root_id = builder
				.load_binary(
					entry_path,
					&vfs::VirtualFileSource::new(workspace),
				)
				.unwrap();
			let mut graph = builder.build(root_id);

			let mut diagnostics = Vec::new();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				graph.stdlib_package,
			);
			drop(ast_nodes);
			drop(diagnostics);

			TestCase { graph, defs }
		}

		fn root_namespace(&self) -> NamespaceIndex {
			self.defs.package_namespaces[self.graph.root_package.as_usize()]
		}

		fn root_file(&self) -> FileId {
			self.defs.namespaces[usize::from(self.root_namespace())].file_id
		}

		fn stdlib_root(&self) -> NamespaceIndex {
			self.defs.package_namespaces[self.graph.stdlib_package.as_usize()]
		}

		fn resolver(&self) -> PathResolver<'_> {
			PathResolver::new(
				&self.defs.namespaces,
				&self.defs.use_items,
				self.stdlib_root(),
			)
		}

		fn segments(&mut self, path: &str) -> Vec<PathSegment> {
			path.split("::")
				.map(|name| PathSegment {
					ident: crate::ast::Spanned {
						inner: self.graph.strings.get_or_intern(name),
						span: crate::diagnostics::TextSpan::new(0, 0),
					},
					type_args: Box::new([]),
				})
				.collect()
		}

		fn resolve_type(
			&mut self,
			from: NamespaceIndex,
			path: &str,
		) -> PathResolution {
			let segments = self.segments(path);
			self.resolver().try_resolve_path(
				from,
				&segments,
				BindingNamespace::Type,
			)
		}

		fn resolve_value(
			&mut self,
			from: NamespaceIndex,
			path: &str,
		) -> PathResolution {
			let segments = self.segments(path);
			self.resolver().try_resolve_path(
				from,
				&segments,
				BindingNamespace::Value,
			)
		}
	}

	fn assert_resolved(resolution: PathResolution) -> DefKey {
		let BindingLookup::Found(target, _) = resolution.stopped_with else {
			panic!("expected Found, got {:?}", resolution.stopped_with);
		};
		match target {
			BindingTarget::Accessible(key)
			| BindingTarget::Inaccessible(key) => key,
			BindingTarget::Error => panic!("expected a real DefKey, got Error"),
		}
	}

	#[test]
	fn resolves_a_direct_declaration_in_the_same_namespace() {
		let mut case = TestCase::new(indoc! {"
			struct Point { x: i32, y: i32 }
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "Point");
		let key = assert_resolved(resolution);
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Struct(_)));
	}

	#[test]
	fn resolves_through_a_child_module() {
		let mut case = TestCase::new(indoc! {"
			mod inner {
				pub struct Widget { a: i32 }
			}
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "inner::Widget");
		let key = assert_resolved(resolution);
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Struct(_)));
	}

	#[test]
	fn resolves_through_a_glob_import() {
		let mut case = TestCase::new(indoc! {"
			mod inner {
				pub struct Widget { a: i32 }
			}
			use inner::*;
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "Widget");
		let key = assert_resolved(resolution);
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Struct(_)));
	}

	/// Matches rustc (verified against a literal Rust equivalent, which
	/// fails with E0425 "cannot find type `Outer` in this scope"): a child
	/// module does not implicitly see its parent's declarations. Reaching
	/// `Outer` from `inner` needs `super::Outer` instead.
	#[test]
	fn a_child_module_does_not_see_its_parents_declarations() {
		let mut case = TestCase::new(indoc! {"
			struct Outer { a: i32 }
			mod inner {
				fn use_it() -> i32 { 1 }
			}
		"});
		let root = case.root_namespace();
		let inner_key = assert_resolved(case.resolve_type(root, "inner"));
		let DefKind::Module(inner) = inner_key.symbol_kind(&case.defs) else {
			panic!("expected a module");
		};

		let resolution = case.resolve_type(inner, "Outer");
		assert_eq!(resolution.stopped_at, 0);
		assert!(matches!(resolution.stopped_with, BindingLookup::NotFound));
	}

	#[test]
	fn later_segments_do_not_climb_either() {
		let mut case = TestCase::new(indoc! {"
			struct Outer { a: i32 }
			mod inner {
				mod deeper { }
			}
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "inner::deeper::Outer");
		assert_eq!(resolution.stopped_at, 2);
		assert!(matches!(resolution.stopped_with, BindingLookup::NotFound));
	}

	#[test]
	fn falls_back_to_the_std_prelude_for_the_first_segment_only() {
		let mut case = TestCase::new(indoc! {"
			fn main() -> i32 { 0 }
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "i32");
		let key = assert_resolved(resolution);
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::TypeAlias(_)));
	}

	#[test]
	fn not_a_module_when_a_non_final_segment_names_a_non_namespace_item() {
		let mut case = TestCase::new(indoc! {"
			struct Point { x: i32 }
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "Point::x");
		assert_eq!(resolution.stopped_at, 0);
		assert!(matches!(resolution.stopped_with, BindingLookup::Found(..)));
	}

	#[test]
	fn not_found_when_nothing_binds_the_name() {
		let mut case = TestCase::new("");
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "DoesNotExist");
		assert_eq!(resolution.stopped_at, 0);
		assert!(matches!(resolution.stopped_with, BindingLookup::NotFound));
	}

	#[test]
	fn ambiguous_when_two_globs_disagree() {
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub struct Widget { x: i32 }
			}
			mod b {
				pub struct Widget { y: i32 }
			}
			use a::*;
			use b::*;
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "Widget");
		assert_eq!(resolution.stopped_at, 0);
		assert!(matches!(
			resolution.stopped_with,
			BindingLookup::Ambiguous(_)
		));
	}

	#[test]
	fn resolves_across_a_file_boundary() {
		let mut case = TestCase::new_workspace(
			vfs::AbsolutePath::new("/main.wx"),
			HashMap::from([
				(vfs::AbsolutePath::new("/main.wx"), "mod math;".to_string()),
				(
					vfs::AbsolutePath::new("/math.wx"),
					"pub fn add() -> i32 { 1 }".to_string(),
				),
			]),
		);
		let root = case.root_namespace();
		let resolution = case.resolve_value(root, "math::add");
		let key = assert_resolved(resolution);
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Function(_)));
	}

	#[test]
	fn value_tier_is_only_applied_to_the_last_segment() {
		let mut case = TestCase::new(indoc! {"
			mod inner {
				pub fn helper() -> i32 { 1 }
			}
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_value(root, "inner::helper");
		let key = assert_resolved(resolution);
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Function(_)));
	}

	/// Mirrors a real rustc case I compiled: `mod a { mod b { pub struct C;
	/// } }`, referenced as `a::b::C` from the crate root, reports the
	/// private-module hop (`b`) — not the terminal `C`, which is `pub`.
	#[test]
	fn first_inaccessible_blames_the_private_intermediate_module() {
		let mut case = TestCase::new(indoc! {"
			mod a {
				mod b {
					pub struct C { x: i32 }
				}
			}
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "a::b::C");
		assert!(matches!(resolution.stopped_with, BindingLookup::Found(..)));
		let (index, _def_key) = resolution
			.first_inaccessible
			.expect("expected an inaccessible hop");
		assert_eq!(
			index, 1,
			"expected the `b` hop (index 1) to be the first inaccessible one"
		);
	}

	#[test]
	fn first_inaccessible_is_none_when_everything_along_the_way_is_public() {
		let mut case = TestCase::new(indoc! {"
			pub mod a {
				pub mod b {
					pub struct C { x: i32 }
				}
			}
		"});
		let root = case.root_namespace();
		let resolution = case.resolve_type(root, "a::b::C");
		assert_eq!(resolution.first_inaccessible, None);
	}

	/// Only the success path is covered here — every failure branch of
	/// `resolve_path` calls a `report_*` stub that's still a `todo!()`
	/// pending the diagnostic-code decision, so exercising them would panic.
	#[test]
	fn resolve_path_returns_the_target_when_fully_resolved() {
		let mut case = TestCase::new(indoc! {"
			struct Point { x: i32, y: i32 }
		"});
		let root = case.root_namespace();
		let file_id = case.root_file();
		let segments = case.segments("Point");
		let mut diagnostics = Vec::new();

		let target = case.resolver().resolve_path(
			&mut diagnostics,
			&case.graph.strings,
			file_id,
			root,
			&segments,
			BindingNamespace::Type,
		);

		assert!(diagnostics.is_empty(), "{diagnostics:?}");
		let BindingTarget::Accessible(key) = target else {
			panic!("expected Accessible, got {target:?}");
		};
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Struct(_)));
	}

	#[test]
	fn resolve_path_reports_not_found_with_the_right_tier_and_name() {
		let mut case = TestCase::new("");
		let root = case.root_namespace();
		let file_id = case.root_file();
		let segments = case.segments("DoesNotExist");
		let mut diagnostics = Vec::new();

		let target = case.resolver().resolve_path(
			&mut diagnostics,
			&case.graph.strings,
			file_id,
			root,
			&segments,
			BindingNamespace::Value,
		);

		assert!(matches!(target, BindingTarget::Error));
		assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
		assert_eq!(
			diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::UndeclaredIdentifier.code())
		);
		assert_eq!(
			diagnostics[0].message,
			"cannot find value `DoesNotExist` in this scope"
		);
	}

	#[test]
	fn resolve_path_reports_ambiguous_via_the_shared_imports_diagnostic() {
		let mut case = TestCase::new(indoc! {"
			mod a {
				pub struct Widget { x: i32 }
			}
			mod b {
				pub struct Widget { y: i32 }
			}
			use a::*;
			use b::*;
		"});
		let root = case.root_namespace();
		let file_id = case.root_file();
		let segments = case.segments("Widget");
		let mut diagnostics = Vec::new();

		let target = case.resolver().resolve_path(
			&mut diagnostics,
			&case.graph.strings,
			file_id,
			root,
			&segments,
			BindingNamespace::Type,
		);

		assert!(matches!(target, BindingTarget::Error));
		assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
		assert_eq!(
			diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::AmbiguousIdentifier.code())
		);
		assert_eq!(diagnostics[0].message, "`Widget` is ambiguous");
	}

	/// Same source shape as `try_resolve_path`'s own
	/// `first_inaccessible_blames_the_private_intermediate_module` — but
	/// exercised through the diagnosing wrapper this time, confirming it
	/// reports the private hop *and* still hands back the real, fully
	/// resolved target rather than `Error`.
	#[test]
	fn resolve_path_reports_private_but_still_returns_the_real_target() {
		let mut case = TestCase::new(indoc! {"
			mod a {
				mod b {
					pub struct C { x: i32 }
				}
			}
		"});
		let root = case.root_namespace();
		let file_id = case.root_file();
		let segments = case.segments("a::b::C");
		let mut diagnostics = Vec::new();

		let target = case.resolver().resolve_path(
			&mut diagnostics,
			&case.graph.strings,
			file_id,
			root,
			&segments,
			BindingNamespace::Type,
		);

		let BindingTarget::Accessible(key) = target else {
			panic!("expected Accessible, got {target:?}");
		};
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Struct(_)));

		assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
		assert_eq!(
			diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::PrivateItem.code())
		);
		assert_eq!(diagnostics[0].message, "module `b` is private");
	}

	#[test]
	fn resolve_path_reports_not_a_namespace() {
		let mut case = TestCase::new(indoc! {"
			struct Point { x: i32 }
		"});
		let root = case.root_namespace();
		let file_id = case.root_file();
		let segments = case.segments("Point::x");
		let mut diagnostics = Vec::new();

		let target = case.resolver().resolve_path(
			&mut diagnostics,
			&case.graph.strings,
			file_id,
			root,
			&segments,
			BindingNamespace::Type,
		);

		assert!(matches!(target, BindingTarget::Error));
		assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
		assert_eq!(
			diagnostics[0].code.as_deref(),
			Some(DiagnosticCode::CannotUseAsNamespace.code())
		);
		assert_eq!(
			diagnostics[0].message,
			"cannot use struct `Point` as a namespace"
		);
	}
}
