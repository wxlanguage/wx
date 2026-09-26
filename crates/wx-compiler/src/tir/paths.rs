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
//! about. Resolving `Type::member` needs the inherent/trait impl dispatch
//! tables or a bound instead (`members.rs`'s job). [`Self::walk_path`] is
//! the raw primitive: it never decides whether stopping early is fine,
//! just hands back whichever segment it actually reached and where.
//! [`Self::resolve_path`] is built on top of it for the common case — a
//! caller that never continues (a bound's own trait path, a `use` path, ...)
//! and wants stopping early to be `CannotUseAsNamespace`; a caller that
//! *can* continue past this module's own edge calls `walk_path` directly
//! and decides for itself.
//!
//! The raw resolver does not emit diagnostics. Rustc splits privacy-checking off
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
	tir::defs::{EnumDef, ImportDef, ModuleDef},
	vfs::FileId,
};

use super::defs::{
	BindingKey, BindingLookup, BindingNamespace, BindingTarget, DefKey,
	DefKind, DefinitionRegistry, Namespace, NamespaceIdx, NamespaceLookup,
	UseItemDef,
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
/// Both fields are private — [`PathResolver::walk_path`] is the intended
/// way to consume a resolution, turning this raw shape into the smaller,
/// already-diagnosed [`PathWalk`]. `try_resolve_path` itself still stays
/// diagnostics-free internally (same reasoning as
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

/// [`PathResolver::walk_path`]'s result: the target reached, and which
/// segment it was reached at. Whether the whole path was consumed is a
/// plain comparison ([`Self::is_complete`]) rather than its own variant
/// (`Full`/`Partial`) — every caller needs `stopped_at` regardless, either
/// to know where to continue from, or (a caller that never continues) to
/// point its own diagnostic at the right segment.
pub(super) struct PathWalk {
	pub(super) target: BindingTarget,
	pub(super) stopped_at: u32,
}

impl PathWalk {
	pub(super) fn is_complete(&self, segments: &[PathSegment]) -> bool {
		self.stopped_at as usize + 1 == segments.len()
	}
}

/// Namespace-graph path resolution, holding just the read-only inputs
/// every call needs — see the module docs for what this does and doesn't
/// cover.
pub(super) struct PathResolver<'r> {
	namespaces: &'r [Namespace],
	enums: &'r [EnumDef],
	imports: &'r [ImportDef],
	modules: &'r [ModuleDef],
	use_items: &'r [UseItemDef],
	stdlib_root: NamespaceIdx,
}

impl<'r> PathResolver<'r> {
	pub(super) fn new(defs: &'r DefinitionRegistry) -> Self {
		Self {
			namespaces: &defs.namespaces,
			use_items: &defs.use_items,
			enums: &defs.enums,
			imports: &defs.imports,
			modules: &defs.modules,
			stdlib_root: defs.stdlib_package.root_namespace(),
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
		accessor: NamespaceIdx,
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
					base = match self.def_kind(def_key) {
						DefKind::Package(package) => package.root_namespace(),
						DefKind::Enum(enum_idx) => {
							self.enums[usize::from(enum_idx)].own_namespace
						}
						DefKind::Module(module_idx) => {
							self.modules[usize::from(module_idx)].own_namespace
						}
						DefKind::Import(import_idx) => {
							self.imports[usize::from(import_idx)].own_namespace
						}
						_ => {
							return PathResolution {
								stopped_at: index as u32,
								stopped_with: outcome,
								first_inaccessible,
							};
						}
					};
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

	/// Walks `segments`, diagnosing only what's *always* an error
	/// regardless of caller:
	/// - `NotFound` / `Ambiguous` — nothing real to hand back.
	/// - A hop that resolved to something real but isn't visible to
	///   `accessor` — reported, but *not* turned into `Error`: matching
	///   rustc (verified empirically — a privacy violation doesn't stop
	///   type-checking from also reporting its own, unrelated errors on the
	///   same resolved item), the real target is still returned, so a
	///   caller building on top of it doesn't get a spurious cascade on top
	///   of the privacy diagnostic.
	///
	/// Stopping before the last segment is deliberately left undiagnosed —
	/// whether that's fine depends entirely on what the caller does next,
	/// which this method has no way to know. [`Self::resolve_path`] is the
	/// convenience for a caller that doesn't; a caller that can continue
	/// past this module's own edge (`members.rs`'s territory) calls this
	/// directly and decides for itself, using [`PathWalk::stopped_at`] to
	/// know where to pick up from.
	pub(super) fn walk_path(
		&self,
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		file_id: FileId,
		accessor: NamespaceIdx,
		segments: &[PathSegment],
		tier: BindingNamespace,
	) -> PathWalk {
		let resolution = self.try_resolve_path(accessor, segments, tier);
		let stopped_at = resolution.stopped_at;
		let is_last = stopped_at as usize + 1 == segments.len();
		// Every segment but the last is always looked up in the `Type`
		// tier (see `try_resolve_path`) — `tier` only applies once we've
		// actually reached the last one.
		let seg_tier = if is_last {
			tier
		} else {
			BindingNamespace::Type
		};
		let span = segments[stopped_at as usize].ident.span;

		let target = match &resolution.stopped_with {
			BindingLookup::Found(target, _) => {
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
			BindingLookup::NotFound => {
				diagnostics.push(report_not_found(
					strings,
					file_id,
					span,
					seg_tier,
					segments[stopped_at as usize].ident.inner,
				));
				BindingTarget::Error
			}
			BindingLookup::Ambiguous(candidates) => {
				diagnostics.push(report_ambiguous_identifier(
					self.namespaces,
					strings,
					segments[stopped_at as usize].ident.inner,
					SourceSpan::new(file_id, span),
					candidates,
				));
				BindingTarget::Error
			}
		};

		PathWalk { target, stopped_at }
	}

	/// The surface most callers want: resolves `segments` and requires the
	/// whole path to have been consumed, reporting `CannotUseAsNamespace`
	/// if [`Self::walk_path`] stopped early — built entirely out of that
	/// plus the one thing every non-continuing caller does with its second
	/// outcome, not a special path through it.
	pub(super) fn resolve_path(
		&self,
		diagnostics: &mut Vec<Diagnostic<FileId>>,
		strings: &StringInterner,
		file_id: FileId,
		accessor: NamespaceIdx,
		segments: &[PathSegment],
		tier: BindingNamespace,
	) -> BindingTarget {
		let walk = self.walk_path(
			diagnostics,
			strings,
			file_id,
			accessor,
			segments,
			tier,
		);
		if walk.is_complete(segments) {
			return walk.target;
		}
		// `None` here means an already-errored placeholder
		// (`BindingTarget::Error`) mid-path — already diagnosed by
		// whoever caused that, nothing new to report.
		if let Some(def_key) = walk.target.def_key() {
			diagnostics.push(report_cannot_use_as_namespace(
				self.namespaces,
				strings,
				segments[walk.stopped_at as usize].ident.inner,
				SourceSpan::new(
					file_id,
					segments[walk.stopped_at as usize].ident.span,
				),
				def_key,
			));
		}
		BindingTarget::Error
	}

	fn def_kind(&self, def_key: DefKey) -> DefKind {
		self.namespaces[usize::from(def_key.namespace_idx)].items
			[usize::from(def_key.def_idx)]
		.kind
	}
}

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
	use crate::testing::DiagnosticView;
	use crate::tir::defs::DefinitionRegistry;
	use crate::vfs;

	/// Small, path-resolution-only duplicate of `defs::tests::TestCase` —
	/// kept separate rather than shared across files so each test module
	/// stays self-contained, same as `imports.rs`'s own copy.
	struct TestCase {
		graph: vfs::CompilationUnit,
		defs: DefinitionRegistry,
		diagnostics: Vec<Diagnostic<FileId>>,
	}

	#[must_use]
	struct ResolutionResult<'a> {
		case: &'a TestCase,
		target: BindingTarget,
		diagnostics: Vec<Diagnostic<FileId>>,
	}

	impl ResolutionResult<'_> {
		fn target(&self) -> BindingTarget {
			self.target
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"resolution",
				&self.diagnostics,
				&self.case.graph.files,
			)
		}

		#[track_caller]
		fn expect_success(&self) -> DefKey {
			self.diagnostics().assert_none();
			let BindingTarget::Accessible(key) = self.target else {
				panic!(
					"expected an accessible definition, got {:?}",
					self.target
				);
			};
			key
		}
	}

	impl TestCase {
		fn from_graph(mut graph: vfs::CompilationUnit) -> Self {
			let parser_diagnostics = graph.collect_parser_diagnostics();
			DiagnosticView::new("parse", &parser_diagnostics, &graph.files)
				.assert_no_errors();
			let linker_diagnostics = graph.collect_linker_diagnostics();
			DiagnosticView::new("link", &linker_diagnostics, &graph.files)
				.assert_no_errors();

			let mut diagnostics = Vec::new();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				&graph.packages,
				&graph.files,
				&mut graph.strings,
				&mut diagnostics,
				graph.stdlib_package,
				graph.root_package,
			);
			drop(ast_nodes);

			Self {
				graph,
				defs,
				diagnostics,
			}
		}

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
			Self::from_graph(builder.build(root_id))
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
			Self::from_graph(builder.build(root_id))
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new("prescan", &self.diagnostics, &self.graph.files)
		}

		fn root_namespace(&self) -> NamespaceIdx {
			self.defs.root_package.root_namespace()
		}

		fn resolver(&self) -> PathResolver<'_> {
			PathResolver::new(&self.defs)
		}

		/// Supply a source offset for diagnostic tests; synthetic queries use empty spans.
		fn segments(
			&mut self,
			path: &str,
			mut offset: Option<usize>,
		) -> Vec<PathSegment> {
			path.split("::")
				.map(|name| {
					let span = if let Some(start) = offset {
						offset = Some(start + name.len() + 2);
						TextSpan::new(start as u32, (start + name.len()) as u32)
					} else {
						TextSpan::new(0, 0)
					};
					PathSegment {
						ident: crate::ast::Spanned {
							inner: self.graph.strings.get_or_intern(name),
							span,
						},
						type_args: Box::new([]),
					}
				})
				.collect()
		}

		/// Inspects the raw outcome, including partial paths and inaccessible hops.
		fn try_resolve(
			&mut self,
			from: NamespaceIdx,
			tier: BindingNamespace,
			path: &str,
		) -> PathResolution {
			let segments = self.segments(path, None);
			self.resolver().try_resolve_path(from, &segments, tier)
		}

		/// Uses the complete-path API: stopping early produces an error target.
		fn resolve(
			&mut self,
			from: NamespaceIdx,
			tier: BindingNamespace,
			path: &str,
		) -> ResolutionResult<'_> {
			let file_id = self.defs.namespaces[usize::from(from)].file_id;
			let segments = self.segments(path, None);
			self.resolve_segments(file_id, from, tier, &segments)
		}

		fn resolve_segments(
			&self,
			file_id: FileId,
			from: NamespaceIdx,
			tier: BindingNamespace,
			segments: &[PathSegment],
		) -> ResolutionResult<'_> {
			let mut diagnostics = Vec::new();
			let target = self.resolver().resolve_path(
				&mut diagnostics,
				&self.graph.strings,
				file_id,
				from,
				segments,
				tier,
			);
			ResolutionResult {
				case: self,
				target,
				diagnostics,
			}
		}
	}

	#[test]
	fn resolves_through_a_child_module() {
		let mut case = TestCase::new(indoc! {"
			mod inner {
				pub struct Widget { a: i32 }
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let key = case
			.resolve(root, BindingNamespace::Type, "inner::Widget")
			.expect_success();
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
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let key = case
			.resolve(root, BindingNamespace::Type, "Widget")
			.expect_success();
		let original = case
			.resolve(root, BindingNamespace::Type, "inner::Widget")
			.expect_success();
		assert_eq!(key, original);
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
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let inner_key = case
			.resolve(root, BindingNamespace::Type, "inner")
			.expect_success();
		let DefKind::Module(inner) = inner_key.symbol_kind(&case.defs) else {
			panic!("expected a module");
		};
		let inner_namespace =
			case.defs.modules[usize::from(inner)].own_namespace;

		let resolution =
			case.try_resolve(inner_namespace, BindingNamespace::Type, "Outer");
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
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let resolution = case.try_resolve(
			root,
			BindingNamespace::Type,
			"inner::deeper::Outer",
		);
		assert_eq!(resolution.stopped_at, 2);
		assert!(matches!(resolution.stopped_with, BindingLookup::NotFound));
	}

	#[test]
	fn falls_back_to_the_std_prelude_for_the_first_segment_only() {
		let mut case = TestCase::new(indoc! {"
			mod inner {}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let key = case
			.resolve(root, BindingNamespace::Type, "i32")
			.expect_success();
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::TypeAlias(_)));

		let resolution =
			case.try_resolve(root, BindingNamespace::Type, "inner::i32");
		assert_eq!(resolution.stopped_at, 1);
		assert!(matches!(resolution.stopped_with, BindingLookup::NotFound));
	}

	#[test]
	fn local_definition_takes_precedence_over_the_std_prelude() {
		let mut case = TestCase::new("struct i32 {}");
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let key = case
			.resolve(root, BindingNamespace::Type, "i32")
			.expect_success();
		assert_eq!(key.namespace_idx, root);
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Struct(_)));
	}

	#[test]
	fn walk_path_returns_a_partial_target_while_resolve_path_requires_completion()
	 {
		let source = indoc! {"
			mod inner { pub struct Point {} }
			type Alias = inner::Point::member;
		"};
		let mut case = TestCase::new(source);
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let original = case
			.resolve(root, BindingNamespace::Type, "inner::Point")
			.expect_success();
		let file_id = case.defs.namespaces[usize::from(root)].file_id;
		let path = "inner::Point::member";
		let segments = case.segments(path, Some(source.find(path).unwrap()));
		let mut diagnostics = Vec::new();
		let walk = case.resolver().walk_path(
			&mut diagnostics,
			&case.graph.strings,
			file_id,
			root,
			&segments,
			BindingNamespace::Type,
		);

		DiagnosticView::new("walk", &diagnostics, &case.graph.files)
			.assert_none();
		assert_eq!(walk.stopped_at, 1);
		let BindingTarget::Accessible(key) = walk.target else {
			panic!("expected Point, got {:?}", walk.target);
		};
		assert_eq!(key, original);

		let result = case.resolve_segments(
			file_id,
			root,
			BindingNamespace::Type,
			&segments,
		);
		assert!(matches!(result.target(), BindingTarget::Error));
		result
			.diagnostics()
			.assert_codes(&[DiagnosticCode::CannotUseAsNamespace]);
	}

	#[test]
	fn errored_imports_do_not_cascade_at_terminal_or_intermediate_segments() {
		// The alias also collides with the prelude: an error placeholder must
		// suppress fallback as well as additional diagnostics.
		let mut case = TestCase::new("use missing as i32;");
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::UnresolvedImport]);

		let root = case.root_namespace();
		for path in ["i32", "i32::member"] {
			let result = case.resolve(root, BindingNamespace::Type, path);
			assert!(matches!(result.target(), BindingTarget::Error), "{path}");
			result.diagnostics().assert_none();
		}
	}

	#[test]
	fn not_found_when_nothing_binds_the_name() {
		let mut case = TestCase::new("");
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let resolution =
			case.try_resolve(root, BindingNamespace::Type, "DoesNotExist");
		assert_eq!(resolution.stopped_at, 0);
		assert!(matches!(resolution.stopped_with, BindingLookup::NotFound));
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
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let key = case
			.resolve(root, BindingNamespace::Value, "math::add")
			.expect_success();
		assert!(matches!(key.symbol_kind(&case.defs), DefKind::Function(_)));
	}

	#[test]
	fn value_tier_is_only_applied_to_the_last_segment() {
		let mut case = TestCase::new(indoc! {"
			mod inner {
				pub fn helper() -> i32 { 1 }
			}
		"});
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let key = case
			.resolve(root, BindingNamespace::Value, "inner::helper")
			.expect_success();
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
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let resolution =
			case.try_resolve(root, BindingNamespace::Type, "a::b::C");
		assert_eq!(resolution.stopped_at, 2);
		let BindingLookup::Found(BindingTarget::Accessible(target), _) =
			resolution.stopped_with
		else {
			panic!(
				"expected the terminal definition, got {:?}",
				resolution.stopped_with
			);
		};
		let (index, private_key) = resolution
			.first_inaccessible
			.expect("expected an inaccessible hop");
		assert_eq!(index, 1);
		let DefKind::Module(module) = private_key.symbol_kind(&case.defs)
		else {
			panic!("expected the private module");
		};
		let module = &case.defs.modules[usize::from(module)];
		assert_eq!(case.graph.strings.resolve(module.name.inner), Some("b"));
		let namespace = module.own_namespace;
		let original = case
			.resolve(namespace, BindingNamespace::Type, "C")
			.expect_success();
		assert_eq!(target, original);
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
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let resolution =
			case.try_resolve(root, BindingNamespace::Type, "a::b::C");
		assert_eq!(resolution.first_inaccessible, None);
		assert_eq!(resolution.stopped_at, 2);
		let BindingLookup::Found(BindingTarget::Accessible(key), _) =
			resolution.stopped_with
		else {
			panic!(
				"expected the terminal definition, got {:?}",
				resolution.stopped_with
			);
		};
		let DefKind::Struct(index) = key.symbol_kind(&case.defs) else {
			panic!("expected struct C");
		};
		assert_eq!(
			case.graph
				.strings
				.resolve(case.defs.structs[usize::from(index)].name.inner),
			Some("C")
		);
	}

	#[test]
	fn resolve_path_reports_not_found_with_the_right_tier_and_name() {
		let source = "fn main() { DoesNotExist; }";
		let mut case = TestCase::new(source);
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let file_id = case.defs.namespaces[usize::from(root)].file_id;
		let path_start = source.rfind("DoesNotExist").unwrap();
		let segments = case.segments("DoesNotExist", Some(path_start));
		let result = case.resolve_segments(
			file_id,
			root,
			BindingNamespace::Value,
			&segments,
		);
		let target = result.target();
		let diagnostics = result.diagnostics();

		assert!(matches!(target, BindingTarget::Error));
		diagnostics.assert_codes(&[DiagnosticCode::UndeclaredIdentifier]);
		diagnostics.assert_error_with(
			DiagnosticCode::UndeclaredIdentifier,
			|diagnostic| {
				assert_eq!(diagnostic.labels[0].file_id, file_id);
				assert_eq!(
					diagnostic.labels[0].range,
					path_start..path_start + 12
				);
				assert_eq!(
					diagnostic.message,
					"cannot find value `DoesNotExist` in this scope"
				);
			},
		);
	}

	#[test]
	fn resolve_path_reports_ambiguity_without_falling_back_to_the_prelude() {
		// A prelude definition must not hide ambiguity in the local scope.
		let source = indoc! {"
			mod a {
				pub struct i32 {}
			}
			mod b {
				pub struct i32 {}
			}
			use a::*;
			use b::*;
			type Alias = i32;
		"};
		let mut case = TestCase::new(source);
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let file_id = case.defs.namespaces[usize::from(root)].file_id;
		let path_start = source.rfind("i32").unwrap();
		let segments = case.segments("i32", Some(path_start));
		let result = case.resolve_segments(
			file_id,
			root,
			BindingNamespace::Type,
			&segments,
		);
		let target = result.target();
		let diagnostics = result.diagnostics();

		assert!(matches!(target, BindingTarget::Error));
		diagnostics.assert_codes(&[DiagnosticCode::AmbiguousIdentifier]);
		diagnostics.assert_error_with(
			DiagnosticCode::AmbiguousIdentifier,
			|diagnostic| {
				assert_eq!(diagnostic.labels[0].file_id, file_id);
				assert_eq!(
					diagnostic.labels[0].range,
					path_start..path_start + 3
				);
				assert_eq!(diagnostic.message, "`i32` is ambiguous");
			},
		);
	}

	/// Same source shape as `try_resolve_path`'s own
	/// `first_inaccessible_blames_the_private_intermediate_module` — but
	/// exercised through the diagnosing wrapper this time, confirming it
	/// reports the private hop *and* still hands back the real, fully
	/// resolved target rather than `Error`.
	#[test]
	fn resolve_path_reports_private_but_still_returns_the_real_target() {
		let source = indoc! {"
			mod a {
				mod b {
					pub struct C { x: i32 }
				}
			}
			type Alias = a::b::C;
		"};
		let mut case = TestCase::new(source);
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let file_id = case.defs.namespaces[usize::from(root)].file_id;
		let path_start = source.rfind("a::b::C").unwrap();
		let segments = case.segments("a::b::C", Some(path_start));
		let result = case.resolve_segments(
			file_id,
			root,
			BindingNamespace::Type,
			&segments,
		);
		let target = result.target();
		let diagnostics = result.diagnostics();

		let BindingTarget::Accessible(key) = target else {
			panic!("expected Accessible, got {target:?}");
		};

		diagnostics.assert_codes(&[DiagnosticCode::PrivateItem]);
		diagnostics.assert_error_with(
			DiagnosticCode::PrivateItem,
			|diagnostic| {
				assert_eq!(diagnostic.labels[0].file_id, file_id);
				assert_eq!(
					diagnostic.labels[0].range,
					path_start + 3..path_start + 4
				);
				assert_eq!(diagnostic.message, "module `b` is private");
			},
		);
		let DefKind::Struct(index) = key.symbol_kind(&case.defs) else {
			panic!("expected struct C");
		};
		assert_eq!(
			case.graph
				.strings
				.resolve(case.defs.structs[usize::from(index)].name.inner),
			Some("C")
		);
	}

	#[test]
	fn resolve_path_reports_not_a_namespace() {
		let source = indoc! {"
			struct Point { x: i32 }
			type Alias = Point::x;
		"};
		let mut case = TestCase::new(source);
		case.diagnostics().assert_none();

		let root = case.root_namespace();
		let file_id = case.defs.namespaces[usize::from(root)].file_id;
		let path_start = source.rfind("Point::x").unwrap();
		let segments = case.segments("Point::x", Some(path_start));
		let result = case.resolve_segments(
			file_id,
			root,
			BindingNamespace::Type,
			&segments,
		);
		let target = result.target();
		let diagnostics = result.diagnostics();

		assert!(matches!(target, BindingTarget::Error));
		diagnostics.assert_codes(&[DiagnosticCode::CannotUseAsNamespace]);
		diagnostics.assert_error_with(
			DiagnosticCode::CannotUseAsNamespace,
			|diagnostic| {
				assert_eq!(diagnostic.labels[0].file_id, file_id);
				assert_eq!(
					diagnostic.labels[0].range,
					path_start..path_start + 5
				);
				assert_eq!(
					diagnostic.message,
					"cannot use struct `Point` as a namespace"
				);
			},
		);
	}
}
